(* fuzz_preset, image B' (asan-ubsan d663f82d, the #102 pin), slice RD-GROW: SEGMENT of grow's walk - ARM 7 (an object: the kids and the keys
   moved), from the facts the walk holds at grow's `ret` to the kit's post body for that arm. Re-uses no run: the walk's
   run 12 (`sd a0, 0(s1)`, `sd s6, 0(s0)`, the epilogue) gives the final memory mF through its frame (only grow's
   windows written) and the three field reads; the two fuzz_realloc calls give their posts in the SHAPE-FREE form
   below (WalkS5a3's COM / COM2 forms, lib/A/Prog/PwGrow.v grow_from_J), which both the cap <> 0 walk (realloc's
   success arm) and the cap = 0 walk (fuzz_malloc's post through realloc's p = 0 arm) supply. The proof follows
   WalkS5a3's arm-7 proof for image A (PwGrow.v :2533-2664 at walk-S5A 860f777e75d5) over image B's facts.
   The live-request permutation and the position transfer are premises the walk composes from the two calls' posts.
   lia is scoped throughout (clear - ..): the walk's contexts are large (BGrow3R's measured runaway, PwGrowBCapnz.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI00 YI04 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK06 YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC80xf YC1fPx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PwGrowG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRoom PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PwGrowB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- list facts (image-free; WalkS5a3's PwGrow.v perm_swap2 / grow_lsum_* / grow_held_*, the same statements) ---- *)
Lemma growB_perm_swap2 {T} : forall (A X Y D1 D2 : list T) (N1 : T),
  Permutation A (D1 ++ X) -> Permutation (N1 :: X) (D2 ++ Y) -> ~ In N1 D2 ->
  exists Z0, Permutation A ((D1 ++ D2) ++ Z0) /\ Permutation Y (N1 :: Z0).
Proof.
intros A X Y D1 D2 N1 HA HX Hn.
assert (HinY : In N1 Y).
{ pose proof (Permutation_in N1 HX (or_introl eq_refl)) as Hi. apply in_app_or in Hi as [Hi | Hi];
    [contradiction | exact Hi]. }
destruct (in_split _ _ HinY) as (y1 & y2 & Ey). exists (y1 ++ y2). split.
- eapply perm_trans; [exact HA|]. rewrite <- app_assoc. apply Permutation_app_head.
  apply (Permutation_cons_inv (a := N1)). eapply perm_trans; [exact HX|]. rewrite Ey, !app_assoc.
  apply Permutation_sym. apply Permutation_middle.
- rewrite Ey. apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma growB_lsum_app : forall l1 l2, Ledger.lsum (l1 ++ l2) = Ledger.lsum l1 + Ledger.lsum l2.
Proof. induction l1 as [|[a k] l1 IH]; intros l2; cbn [app Ledger.lsum]; [lia | rewrite IH; lia]. Qed.
Lemma growB_lsum_perm : forall l l', Permutation l l' -> Ledger.lsum l = Ledger.lsum l'.
Proof.
intros l l' H. induction H as [|[a k] l l' H IH|[a k] [a' k'] l|l l' l'' H1 IH1 H2 IH2]; cbn [Ledger.lsum]; lia.
Qed.
Lemma growB_lsum_keys : forall ty keys cap, 0 <= cap -> ty = 6 -> Ledger.lsum (keys_blkR ty keys cap) = 8 * cap.
Proof.
intros ty keys cap H H6. unfold keys_blkR. rewrite (proj2 (Z.eqb_eq ty 6) H6).
destruct (Z.eqb_spec cap 0); cbn [orb negb Ledger.lsum]; lia.
Qed.
Lemma growB_lsum_kids : forall kids cap, 0 <= cap -> Ledger.lsum (kids_blkR kids cap) = 56 * cap.
Proof. intros kids cap H. unfold kids_blkR. destruct (Z.eqb_spec cap 0); cbn [Ledger.lsum]; lia. Qed.

Section held. Context {cp : CfParams}.
Lemma growB_held_nat : forall (o : bool) (c : nat),
  PjGrammar.held (snd (fst (PjGrammar.grow o c c []))) +
    cf_head * Z.of_nat (PjGrammar.calls (snd (fst (PjGrammar.grow o c c [])))) =
  Z.of_nat (56 * (if Nat.eqb c 0 then 8 else 2 * c))%nat - Z.of_nat (56 * c)%nat + cf_head +
  (if o then Z.of_nat (8 * (if Nat.eqb c 0 then 8 else 2 * c))%nat - Z.of_nat (8 * c)%nat + cf_head else 0).
Proof.
intros o c. unfold PjGrammar.grow. rewrite Nat.ltb_irrefl. cbv zeta.
generalize (if Nat.eqb c 0 then 8%nat else (2 * c)%nat) as c'. intros c'.
destruct o; cbn [PjGrammar.jbind PjGrammar.jrealloc PjGrammar.take PjGrammar.jret fst snd app
  PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]; lia.
Qed.
Lemma growB_held_eq : forall (o : bool) cap, 0 <= cap ->
  PRH_Charge.prh_held (PRH_Charge.prhPg_gtrace o cap cap) =
  56 * (cap2R cap - cap) + cf_head + (if o then 8 * (cap2R cap - cap) + cf_head else 0).
Proof.
intros o cap Hc. unfold PRH_Charge.prh_held, PRH_Charge.prhPg_gtrace. rewrite growB_held_nat. unfold cap2R.
destruct (Z.eqb_spec cap 0) as [H0 | H0].
- subst cap. change (Z.to_nat 0) with 0%nat. cbn [Nat.eqb]. destruct o; lia.
- rewrite (proj2 (Nat.eqb_neq (Z.to_nat cap) 0)) by lia. destruct o; lia.
Qed.
End held.
Lemma growB_held_nat2 : forall (o : bool) (c : nat),
  PjGrammar.held (snd (fst (PjGrammar.grow o c c []))) =
  Z.of_nat (56 * (if Nat.eqb c 0 then 8 else 2 * c))%nat - Z.of_nat (56 * c)%nat +
  (if o then Z.of_nat (8 * (if Nat.eqb c 0 then 8 else 2 * c))%nat - Z.of_nat (8 * c)%nat else 0).
Proof.
intros o c. unfold PjGrammar.grow. rewrite Nat.ltb_irrefl. cbv zeta.
generalize (if Nat.eqb c 0 then 8%nat else (2 * c)%nat) as c'. intros c'.
destruct o; cbn [PjGrammar.jbind PjGrammar.jrealloc PjGrammar.take PjGrammar.jret fst snd app
  PjGrammar.held PjGrammar.held_ev]; lia.
Qed.
Lemma growB_held_only : forall (o : bool) cap, 0 <= cap ->
  PjGrammar.held (PRH_Charge.prhPg_gtrace o cap cap) =
  56 * (cap2R cap - cap) + (if o then 8 * (cap2R cap - cap) else 0).
Proof.
intros o cap Hc. unfold PRH_Charge.prhPg_gtrace. rewrite growB_held_nat2. unfold cap2R.
destruct (Z.eqb_spec cap 0) as [H0 | H0].
- subst cap. change (Z.to_nat 0) with 0%nat. cbn [Nat.eqb]. destruct o; lia.
- rewrite (proj2 (Nat.eqb_neq (Z.to_nat cap) 0)) by lia. destruct o; lia.
Qed.

(* a new block's shadow facts survive a change that leaves the shadow band alone (WalkS5a3's vis_keep) *)
Lemma growB_vis_keep : forall (rd rd' : reader) a n,
  (forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 - 64 ->
  range_addressable rd SHADOW_OFF a n -> (0 < n -> shadow_hull_vis rd a n) ->
  range_addressable rd' SHADOW_OFF a n /\ (0 < n -> shadow_hull_vis rd' a n).
Proof.
intros rd rd' a n Hag Ha0 Han HRA HV. split.
- intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite Hag; [exact Hs|]. unfold SHADOW_OFF in *. Z.div_mod_to_equations. lia.
- intros Hn s Hs. rewrite Hag; [exact (HV Hn s Hs)|]. unfold shadow_addr, SHADOW_OFF in *.
  Z.div_mod_to_equations. lia.
Qed.

Section a7. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {PG : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PG).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Existing Instance prh_img_B.
Hypothesis HPST : forall a, Exists (in_zr a) PST -> in_img SEGS a.

(* a byte array outside grow's windows survives its stores *)
Lemma growB_bytes_keep : forall (W : world SEGS) mem m' sp v p l,
  bytes_at W mem p l ->
  (forall x : word, ~ grow_wr GROW_FR_B sp v (bv_unsigned x) -> mrestrict (w_H W) m' x = mrestrict (w_H W) mem x) ->
  0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ grow_wr GROW_FR_B sp v a) ->
  bytes_at W m' p l.
Proof.
intros W mem m' sp v p l HB HF Hp0 Hp64 Hnw. unfold bytes_at in *. apply (garr8R_frame SEGS _ _ _ _ HB).
intros a Ha. unfold mbyte. rewrite HF; [reflexivity|]. rewrite unsigned_lit_small by lia. exact (Hnw a Ha).
Qed.

(* THE SEGMENT. Entry values (tgrow_specX's binders); the kids call in the shape-free form (res the new kids block,
   Lr the harness list without the old kids block, blr / hlr the allocator blocks / hidden heads without it); the keys
   call likewise (res2, Lr2, blr2, hlr2); the walk's final memory mF after run 12. Conclusion: tgrow_specX's
   live-room bound and its arm-7 disjunct body without the arm's position conjunct (PRH_FnReader a1763aa44943 :663
   and :748-759; the walk adds the position, :760-762). *)
Lemma growB_seg_arm7 : forall (ly : alayout) (S : astate) (Hp : list Z)
    (regs : bvmap 5 word) (e v ty num str kids keys n cap : Z) (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) (most own : Z)
    (res : Z) (Lr blr : list (Z * Z)) (hlr : list Z) (ly2 : alayout) (S2 : astate) (Hp2 : list Z) (W2 : world SEGS)
    (mem2 : word -> option byte) (pk2 ct2 fl2 rn2 : Z)
    (res2 : Z) (Lr2 blr2 : list (Z * Z)) (hlr2 : list Z) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS)
    (mem3 : word -> option byte) (md3 : Model)
    (regsF : bvmap 5 word) (mF : word -> option byte),
  n = cap -> 0 <= cap -> cap2R cap <= 2 ^ 54 -> cnt <> fail -> ty = 6 -> cnt + 1 <> fail ->
  (0 < cap -> prh_lin Lam kids (56 * cap) /\ (ty = 6 -> prh_lin Lam keys (8 * cap))) ->
  (* the kids call *)
  Permutation (ablocks B ly S) (prhReader_ab (kids_blkR kids cap) ++ blr) ->
  Permutation (ablocks B ly2 S2) ((res - cf_head, 56 * cap2R cap + cf_head) :: blr) ->
  Permutation Hp (prhReader_hd (kids_blkR kids cap) ++ hlr) -> Hp2 = (res - cf_head) :: hlr ->
  Permutation Lam (kids_blkR kids cap ++ Lr) ->
  4096 + cf_head <= res -> res mod 16 = 0 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 ((res, 56 * cap2R cap) :: Lr) pk2 ct2 fl2 rn2 most own ->
  blocks_bytes S2 <= blocks_bytes S + 56 * (cap2R cap - cap) + cf_head ->
  (* the keys call *)
  Permutation ((res, 56 * cap2R cap) :: Lr) (keys_blkR ty keys cap ++ Lr2) ->
  Permutation (ablocks B ly2 S2) (prhReader_ab (keys_blkR ty keys cap) ++ blr2) ->
  Permutation (ablocks B ly3 S3) ((res2 - cf_head, 8 * cap2R cap + cf_head) :: blr2) ->
  Permutation Hp2 (prhReader_hd (keys_blkR ty keys cap) ++ hlr2) -> Hp3 = (res2 - cf_head) :: hlr2 ->
  ARx ly3 S3 Hp3 W3 mem3 md3 ->
  prh_ledger B ly3 S3 Hp3 W3 mem3 ((res2, 8 * cap2R cap) :: Lr2)
    (Z.max (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr))) (Ledger.lsum ((res2, 8 * cap2R cap) :: Lr2)))
    (cnt + 2) fail ran most own ->
  prhReader_at B ly3 S3 ((res2, 8 * cap2R cap) :: Lr2) regs e v 56 ->
  bytes_at W3 mem3 res kb -> Z.of_nat (length kb) <= 56 * cap2R cap ->
  (forall a, res <= a < res + Z.of_nat (length kb) -> ~ grow_wr GROW_FR_B (spZ regs) v a) ->
  bytes_at W3 mem3 res2 yb -> Z.of_nat (length yb) <= 8 * cap2R cap ->
  (forall a, res2 <= a < res2 + Z.of_nat (length yb) -> ~ grow_wr GROW_FR_B (spZ regs) v a) ->
  prhReader_vis W3 mem3 res2 (8 * cap2R cap) ->
  4096 + cf_head <= res2 -> res2 mod 16 = 0 ->
  blocks_bytes S3 <= blocks_bytes S2 + 8 * (cap2R cap - cap) + cf_head ->
  (* run 12 *)
  (forall x : word, ~ grow_wr GROW_FR_B (spZ regs) v (bv_unsigned x) -> mrestrict (w_H W3) mF x = mrestrict (w_H W3) mem3 x) ->
  mem_grows (mrestrict (w_H W3) mem3) (mrestrict (w_H W3) mF) ->
  getr regsF 10 = w64 0 ->
  pj_hdrR SEGS (mrestrict (w_H W3) mem3) v ty num str res keys n cap ->
  rd_u64 SEGS (mrestrict (w_H W3) mF) (v + 24) res ->
  rd_u64 SEGS (mrestrict (w_H W3) mF) (v + 32) res2 ->
  rd_u64 SEGS (mrestrict (w_H W3) mF) (v + 48) (cap2R cap) ->
  (v + 56 <= spZ regs - GROW_FR_B \/ spZ regs <= v) -> 4096 <= v -> v + 56 <= 2 ^ 47 ->
  YM05.alloc_ceiling + 128 <= spZ regs ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a) ->
  (forall a, v <= a < v + 56 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  (* the live requests and the position at the post state (the walk composes them from the two calls' posts) *)
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S3))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [true; true])) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
     PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [true; true]) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length (prhPg_evs (ty =? 6)%Z n cap [true; true]))%nat H0 hist' S3) ->
  blocks_bytes S3 <= blocks_bytes S + PRH_Charge.prh_held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap) /\
  (n = cap /\ cnt <> fail /\ ty = 6 /\ cnt + 1 <> fail /\ getr regsF 10 = w64 0 /\
   exists k' y' Lam', 4096 + cf_head <= k' /\ k' mod 16 = 0 /\ 4096 + cf_head <= y' /\ y' mod 16 = 0 /\
     prhReader_swap B ly S Hp Lam ly3 S3 Hp3 Lam' (kids_blkR kids cap ++ keys_blkR ty keys cap)
       [(y', 8 * cap2R cap); (k', 56 * cap2R cap)] /\
     prh_ledger B ly3 S3 Hp3 W3 mF Lam'
       (Z.max peak (Z.max (Ledger.lsum Lam + 56 * (cap2R cap - cap)) (Ledger.lsum Lam')))
       (cnt + 2) fail ran most own /\
     Ledger.lsum Lam' = Ledger.lsum Lam + PjGrammar.held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap) /\
     bytes_at W3 mF k' kb /\ prhReader_vis W3 mF k' (56 * cap2R cap) /\
     bytes_at W3 mF y' yb /\ prhReader_vis W3 mF y' (8 * cap2R cap) /\
     pj_hdrR SEGS (mrestrict (w_H W3) mF) v ty num str k' y' n (cap2R cap) /\
     pj_slots_atR (prh_lin Lam') ty k' y' n (cap2R cap) /\
     Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S3))
       (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (prhPg_evs (ty =? 6) n cap [true; true])) /\
     (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
        (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
        PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [true; true]) ->
        exists hist', PresetRoomPos.iface_room_pos sm x os
          (i + length (prhPg_evs (ty =? 6)%Z n cap [true; true]))%nat H0 hist' S3)).
Proof.
intros ly S Hp regs e v ty num str kids keys n cap kb yb Lam peak cnt fail ran most own
  res Lr blr hlr ly2 S2 Hp2 W2 mem2 pk2 ct2 fl2 rn2 res2 Lr2 blr2 hlr2 ly3 S3 Hp3 W3 mem3 md3 regsF mF
  Heq Hc0 Hc54 Hcf Hty6 Hcf2 Hslots
  PAB1 PAB2 PHP EHp2 PLam Hr16 Hrm HL2 HBB2
  PLam2 PAB3 PAB4 PHP2 EHp3 HAR3 HL3 HAT3 HB3 Hkbl HKBnw HB3y Hybl HYBnw HVIS3y Hr16' Hrm' HBB3
  F9 G9 R10F HDR3 RkF RyF RcF Hvstk Hv4096 Hv47 Hsp128 Hoff Happ HLVF HPOSF.
pose proof cf_head_nonneg as Hh0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hc2 : 0 < cap2R cap /\ cap <= cap2R cap)
  by (unfold cap2R; destruct (Z.eqb_spec cap 0) as [Hz | Hz]; clear - Hc0 Hz; lia).
(* the shadow band is outside grow's windows: the frame is above alloc_ceiling, the node off the band *)
assert (HSHK9 : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 ->
  aview SEGS (w_H W3) mF s = aview SEGS (w_H W3) mem3 s).
{ intros s Hs. apply aview_eq_of. apply F9. rewrite unsigned_lit_small by (clear - Hs; unfold SHADOW_OFF in Hs; lia).
  unfold grow_wr, GROW_FR_B. intros [Hw | [Hw | Hw]].
  - clear - Hw Hs Hsp128 C1 C2 C3 C4 C5. unfold SHADOW_OFF in *. lia.
  - exact (Happ s ltac:(clear - Hw; lia) Hs).
  - exact (Happ s ltac:(clear - Hw; lia) Hs). }
(* the two new blocks at the post state, below alloc_ceiling *)
assert (Hnew3y : In (res2 - cf_head, 8 * cap2R cap + cf_head) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym PAB4)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR3 Hnew3y) as (_ & _ & Hncy & _).
assert (Hrqy : 8 * cap2R cap + cf_head <= req_size (8 * cap2R cap + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (8 * cap2R cap + cf_head) 0) as [Hq | Hq]; clear - Hh0 Hc2 Hq; lia).
(* the harness list's sums and the kids entry in it *)
assert (Hlsum2 : 56 * cap2R cap + Ledger.lsum Lr = 8 * cap + Ledger.lsum Lr2).
{ pose proof (growB_lsum_perm _ _ PLam2) as Hq. rewrite growB_lsum_app, (growB_lsum_keys ty keys cap) in Hq
    by (first [exact Hc0 | exact Hty6]).
  cbn [Ledger.lsum] in Hq. clear - Hq. lia. }
assert (Hink3 : In (res, 56 * cap2R cap) ((res2, 8 * cap2R cap) :: Lr2)).
{ right. pose proof (Permutation_in _ PLam2
    (or_introl eq_refl : In (res, 56 * cap2R cap) ((res, 56 * cap2R cap) :: Lr))) as Hq.
  apply in_app_or in Hq as [Hq | Hq]; [|exact Hq].
  exfalso. revert Hq. unfold keys_blkR. destruct ((cap =? 0) || negb (ty =? 6)); [intros []|].
  intros [Hq | []]. injection Hq as _ Hq. clear - Hq Hc2 Hc0. lia. }
pose proof HL3 as (_ & _ & HFl3 & _).
pose proof (proj1 (Forall_forall _ _) HFl3 _ Hink3) as (_ & Hb3' & Hh3 & _). cbn [fst snd] in Hb3', Hh3.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR3 Hb3') as (_ & _ & Hnck & _).
assert (Hrqk : 56 * cap2R cap + cf_head <= req_size (56 * cap2R cap + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (56 * cap2R cap + cf_head) 0) as [Hq | Hq]; clear - Hh0 Hc2 Hq; lia).
assert (HVISk : prhReader_vis W3 mF res (56 * cap2R cap)).
{ destruct (grow_vis_law B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 res (56 * cap2R cap) HAR3 Hb3' Hh3
    ltac:(clear - Hc2; lia)) as (HRAn & HVn).
  exact (growB_vis_keep _ _ res (56 * cap2R cap) HSHK9 ltac:(clear - Hr16 Hh0; lia)
           ltac:(clear - Hnck Hrqk Hh0 C1 C2 C3 C4 C5; lia) HRAn HVn). }
split.
{ (* the live-room bound: the two calls' bounds, against the grammar's charge *)
  rewrite Heq, growB_held_eq by exact Hc0. rewrite (proj2 (Z.eqb_eq ty 6) Hty6). clear - HBB2 HBB3. lia. }
split; [exact Heq|]. split; [exact Hcf|]. split; [exact Hty6|]. split; [exact Hcf2|].
split; [exact R10F|].
exists res, res2, ((res2, 8 * cap2R cap) :: Lr2).
split; [exact Hr16|]. split; [exact Hrm|]. split; [exact Hr16'|]. split; [exact Hrm'|].
split.
{ (* the two swaps composed *)
  split.
  - assert (Hnk1 : ~ In (res - cf_head, 56 * cap2R cap + cf_head) (prhReader_ab (keys_blkR ty keys cap))).
    { unfold keys_blkR, prhReader_ab. destruct ((cap =? 0) || negb (ty =? 6)); cbn [map In fst snd];
        [tauto | intros [Hq | []]; injection Hq as _ Hq; clear - Hq Hc2 Hc0; lia]. }
    destruct (growB_perm_swap2 (ablocks B ly S) blr blr2 (prhReader_ab (kids_blkR kids cap))
      (prhReader_ab (keys_blkR ty keys cap)) (res - cf_head, 56 * cap2R cap + cf_head) PAB1
      (perm_trans (Permutation_sym PAB2) PAB3) Hnk1) as (Z0 & PZ1 & PZ2).
    exists Z0. unfold prhReader_ab in PZ1 |- *. rewrite map_app. split; [exact PZ1|].
    eapply perm_trans; [exact PAB4|]. cbn [map app fst snd]. apply perm_skip. exact PZ2.
  - split.
    + assert (Hnk2 : ~ In (res - cf_head) (prhReader_hd (keys_blkR ty keys cap))).
      { unfold keys_blkR, prhReader_hd. destruct (Z.eqb_spec cap 0) as [Hz | Hz]; [cbn; tauto|].
        rewrite (proj2 (Z.eqb_eq ty 6) Hty6). cbn [orb negb map In fst]. intros [Hq | []].
        assert (Hcp : 0 < cap) by (clear - Hz Hc0; lia).
        destruct (Hslots Hcp) as (_ & Hky). specialize (Hky Hty6). unfold prh_lin in Hky.
        assert (Hky2 : In (keys, 8 * cap) Lr).
        { apply (Permutation_in _ PLam) in Hky. unfold kids_blkR in Hky.
          rewrite (proj2 (Z.eqb_neq cap 0) Hz) in Hky.
          destruct Hky as [Hq' | Hky]; [injection Hq' as Ek Ekk; clear - Ekk Hcp; lia | exact Hky]. }
        pose proof HL2 as (_ & HND2 & _). apply NoDup_ListNoDup in HND2. cbn [map fst] in HND2.
        apply NoDup_cons_iff in HND2 as (Hnr & _). apply Hnr. replace res with keys by (clear - Hq; lia).
        apply in_map_iff. exists (keys, 8 * cap). split; [reflexivity | exact Hky2]. }
      assert (PHP2' : Permutation ((res - cf_head) :: hlr) (prhReader_hd (keys_blkR ty keys cap) ++ hlr2))
        by (rewrite <- EHp2; exact PHP2).
      destruct (growB_perm_swap2 Hp hlr hlr2 (prhReader_hd (kids_blkR kids cap))
        (prhReader_hd (keys_blkR ty keys cap)) (res - cf_head) PHP PHP2' Hnk2) as (Z0 & PZ1 & PZ2).
      exists Z0. unfold prhReader_hd in PZ1 |- *. rewrite map_app. split; [exact PZ1|].
      rewrite EHp3. cbn [map app fst snd]. apply perm_skip. exact PZ2.
    + assert (Hnk3 : ~ In (res, 56 * cap2R cap) (keys_blkR ty keys cap)).
      { unfold keys_blkR. destruct ((cap =? 0) || negb (ty =? 6)); cbn [In];
          [tauto | intros [Hq | []]; injection Hq as _ Hq; clear - Hq Hc2 Hc0; lia]. }
      destruct (growB_perm_swap2 Lam Lr Lr2 (kids_blkR kids cap) (keys_blkR ty keys cap) (res, 56 * cap2R cap)
        PLam PLam2 Hnk3) as (Z0 & PZ1 & PZ2).
      exists Z0. split; [exact PZ1|]. cbn [app]. apply perm_skip. exact PZ2. }
split.
{ (* the ledger at the final memory: its cells are apart from grow's writes *)
  replace (Z.max peak (Z.max (Ledger.lsum Lam + 56 * (cap2R cap - cap))
              (Ledger.lsum ((res2, 8 * cap2R cap) :: Lr2))))
    with (Z.max (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr)))
              (Ledger.lsum ((res2, 8 * cap2R cap) :: Lr2))).
  2: { pose proof (growB_lsum_perm _ _ PLam) as Hq. rewrite growB_lsum_app, (growB_lsum_kids kids cap Hc0) in Hq.
       cbn [Ledger.lsum]. clear - Hq. lia. }
  eapply prh_ledger_keep; [exact HL3|]. intros a Hca.
  destruct (grow_cell_apart B ARx LAWS HPST GROW_FR_B ly3 S3 Hp3 W3 mem3 md3 _ _ _ _ _ _ _ regs e v a
    ltac:(unfold GROW_FR_B; lia) HAR3 HL3 HAT3 Hsp128 Hoff Hca) as (Ha64 & Hnw).
  apply F9. rewrite unsigned_lit_small by exact Ha64. exact Hnw. }
split.
{ (* the net user bytes: the grammar's granted trace *)
  rewrite Heq, growB_held_only by exact Hc0. rewrite (proj2 (Z.eqb_eq ty 6) Hty6).
  pose proof (growB_lsum_perm _ _ PLam) as Hq. rewrite growB_lsum_app, (growB_lsum_kids kids cap Hc0) in Hq.
  cbn [Ledger.lsum]. clear - Hq Hlsum2. lia. }
split.
{ apply (growB_bytes_keep W3 mem3 mF (spZ regs) v res kb HB3 F9); [clear - Hr16 Hh0; lia | | exact HKBnw].
  clear - Hnck Hrqk Hkbl Hh0 C1 C2 C3 C4 C5. lia. }
split; [exact HVISk|].
split.
{ apply (growB_bytes_keep W3 mem3 mF (spZ regs) v res2 yb HB3y F9); [clear - Hr16' Hh0; lia | | exact HYBnw].
  clear - Hncy Hrqy Hybl Hh0 C1 C2 C3 C4 C5. lia. }
split.
{ destruct HVIS3y as (HRAn & HVn).
  exact (growB_vis_keep _ _ res2 (8 * cap2R cap) HSHK9 ltac:(clear - Hr16' Hh0; lia)
           ltac:(clear - Hncy Hrqy Hh0 C1 C2 C3 C4 C5; lia) HRAn HVn). }
split.
{ exact (grow_hdr_keep GROW_FR_B (w_H W3) mem3 mF (spZ regs) v ty num str res keys n cap res res2 (cap2R cap)
           HDR3 F9 G9 Hvstk ltac:(clear - Hv4096; lia) ltac:(clear - Hv47; lia) RkF RyF RcF). }
split; [|split; [exact HLVF | exact HPOSF]].
unfold pj_slots_atR, prh_lin.
split; [right; exact Hty6|]. split; [clear - Heq Hc2 Hc54 Hc0; lia|]. split; [intros Hz; clear - Hz Hc2; lia|].
intros _. split; [exact Hink3 | intros _; left; reflexivity].
Qed.
End a7.
