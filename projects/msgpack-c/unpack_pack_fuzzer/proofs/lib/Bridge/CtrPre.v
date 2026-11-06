(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto AMalloc_iface AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aaligned_iseg APrimFacts.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallU CallV C24.
Import CtrFX.

Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require KnownA.
Unset Nia Cache. Unset Nra Cache.

Lemma shad_img_band : forall a', 0 <= a' < AIMG_HI -> 0x7fff8000 <= shad a' < 0x800bde00.
Proof. intros a' H. unfold shad, ASHOFF, AIMG_HI in *. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. Qed.

Section Pre.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.

Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).

Lemma zlist_eqb_eq : forall a b, zlist_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. apply IH. exact H2.
Qed.
Lemma univ_ok_in : forall PCz r, univ_ok UNIV PCz r = true -> In [PCz; to_Z r] UNIV /\ In [PCz] UNIV.
Proof.
  intros PCz r H. unfold univ_ok in H. apply andb_prop in H as [H1 H2].
  apply existsb_exists in H1 as (l1 & I1 & E1). apply existsb_exists in H2 as (l2 & I2 & E2).
  apply zlist_eqb_eq in E1. apply zlist_eqb_eq in E2. subst l1 l2. split; assumption.
Qed.

Lemma aunw_stop : forall (L : alayout) RNG (m : amem) lo PCz (sp s0 : word) r,
  incl UNIV (al_U L) -> univ_ok UNIV PCz r = true ->
  bv_unsigned s0 <= bv_unsigned sp -> bv_unsigned sp < 2^47 -> 0 <= to_Z r < 2^62 ->
  ATOP + 4096 <= lo ->
  rng RNG (ATOP + 4096) (al_top L - (ATOP + 4096)) ->
  aunw m L RNG lo PCz sp s0 (Z_to_bv 64 (to_Z r)) [].
Proof.
  intros L RNG m lo PCz sp s0 r HU UO S0 SP47 RR LO RSTK.
  destruct (univ_ok_in PCz r UO) as [I2 I1]. unfold aunw.
  destruct (Z_lt_le_dec (bv_unsigned sp + 16) (al_top L)) as [LT|GE].
  - left. split; [exact LT|]. split; [apply uc_stop; intros (X & _); lia|]. split; [cbn; lia|]. split.
    + apply HU. rewrite Z_to_bv_small by (unfold bv_modulus; lia). exact I2.
    + destruct (Z_le_gt_dec lo (al_top L)) as [LE|GT].
      * eapply rng_sub'; [exact RSTK|]. lia.
      *   destruct RSTK as (A & B & H). split; [lia|]. split; [lia|]. intros b j Hb Hj. lia.
  - right. split; [exact GE|]. split; [exact SP47|]. apply HU. exact I1.
Qed.

Lemma unw_ok_inv : forall PCz r st hargs nn md A nw rest, unw_ok UNIV PCz r st hargs = true ->
  heap_nwin hargs = Some nn -> hargs = VL md :: A :: VL nw :: rest ->
  exists wl, CtrA.nonstack_windows nn rest = Some wl /\ In [PCz] UNIV /\ s0_far st wl = true
  /\ exists cands, unw_walk 32%nat st hargs wl PCz (getr st X2) (getr st X8) 28%nat = Some cands
       /\ forall tr, In tr cands -> (length tr <= 28)%nat /\ In (PCz :: to_Z r :: tr) UNIV.
Proof.
  intros PCz r st hargs nn md A nw rest H Hn Eh. unfold unw_ok in H. rewrite Hn in H. rewrite Eh in H. rewrite <- Eh in H.
  destruct (CtrA.nonstack_windows nn rest) as [wl|]; [|discriminate H]. exists wl. split; [reflexivity|].
  apply andb_prop in H as [H W]. apply andb_prop in H as [U1 SF].
  apply existsb_exists in U1 as (l1 & I1 & E1). apply zlist_eqb_eq in E1. subst l1.
  split; [exact I1|]. split; [exact SF|].
  destruct (unw_walk 32%nat st hargs wl PCz (getr st X2) (getr st X8) 28%nat) as [cands|]; [|discriminate W].
  exists cands. split; [reflexivity|]. intros tr Htr. pose proof (proj1 (forallb_forall _ _) W tr Htr) as X.
  apply andb_prop in X as [X1 X2]. apply Nat.leb_le in X1. apply existsb_exists in X2 as (l2 & I2 & E2). apply zlist_eqb_eq in E2. subst l2. auto.
Qed.

Lemma below_stack_w_sound : forall E st ms mo nn rest wl LB W aw k off,
  st_ok asegs OPS E st ms mo -> CtrA.nonstack_windows nn rest = Some wl ->
  windows_wf (wins_of E nn rest) LB (ATOP + 4096) -> aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W ->
  below_stack_w (s_facts st) wl k off = true -> bv_unsigned (den E (VP k off)) <= ATOP.
Proof.
  intros E st ms mo nn rest wl LB W aw k off HS NW WF [HWW _] H. unfold below_stack_w in H.
  destruct (CtrA.win_lookup wl k) as [[len kd]|] eqn:WL; [|discriminate H].
  apply andb_prop in H as [WT LT]. apply negb_true_iff in WT.

  assert (L : w2Z off < bv_unsigned (den E len) \/ (0 < w2Z off /\ w2Z off <= bv_unsigned (den E len))).
  { destruct (KnownT.KnownT.known_ltu_t (s_facts st) (VL off) len) eqn:K1.
    - left. pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) K1) as L. cbn [den] in L. rewrite wbv_unsigned in L. exact L.
    - right. destruct (weqb off wzero) eqn:WZ; [discriminate LT|]. cbn [negb] in LT.
      pose proof (KnownA.KnownA.known_leu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) LT) as L. cbn [den] in L. rewrite wbv_unsigned in L.
      assert (NZ : w2Z off <> 0).
      { intros Z0. assert (off = wzero) by (apply w2Z_inj; rewrite Z0, wzero_ok; reflexivity). subst off. rewrite weqb_refl in WZ. discriminate WZ. }
      pose proof (w2Z_range off). lia. }
  destruct (HeapCtrB.nonstack_windows_In E nn rest wl k len kd NW (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & KDS). cbn [w_lo w_len w_kind] in W1, W2, W3, KDS.
  pose proof (w2Z_range off) as RO. unfold two64 in *.
  assert (EW : w2Zs off = w2Z off) by (rewrite ValP.w2Zs_eq, WT; lia).

  set (a := bv_unsigned (ev E k) + w2Z off - (if Z_lt_dec (w2Z off) (bv_unsigned (den E len)) then 0 else 1)).
  assert (AR1 : bv_unsigned (ev E k) + w2Z off <= a + 1) by (unfold a; destruct (Z_lt_dec _ _); lia).
  assert (IU : in_user LB a).
  { assert (AIN : bv_unsigned (ev E k) <= a < bv_unsigned (ev E k) + bv_unsigned (den E len)) by (unfold a; destruct (Z_lt_dec _ _); lia).
    destruct KDS as [[K0 _]|[[KB B]|[KS (b & Hb & SUB)]]]; unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
    - exfalso. unfold K_STACK in K0. lia.
    - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
    - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }
  pose proof atop_range as AR.
  assert (ALT : a < ATOP) by (destruct (LB_band AI ACCT UNIV AI_fake W aw LB (ms_mem ms) mo a HWW IU) as [X|[X|X]]; unfold AIMG_HI, KLS in *; lia).
  assert (ED : bv_unsigned (den E (VP k off)) = bv_unsigned (ev E k) + w2Z off).
  { rewrite ValP.den_VP, EW. apply Z.mod_small. unfold two64. lia. }
  rewrite ED. lia.
Qed.

Lemma alias_d_fact : forall (ea ek : word) (oa ob : w64),
  bv_add ea (wbv oa) = bv_add ek (wbv ob) -> bv_add ea (wbv (wsub oa ob)) = ek.
Proof.
  intros ea ek oa ob H. rewrite ValP.wbv_wsub. apply bv_eq. apply (f_equal bv_unsigned) in H.
  rewrite !bv_add_unsigned, ?bv_sub_unsigned in *.
  pose proof (bv_unsigned_in_range _ ea). pose proof (bv_unsigned_in_range _ ek). pose proof (bv_unsigned_in_range _ (wbv oa)). pose proof (bv_unsigned_in_range _ (wbv ob)).
  unfold bv_wrap, bv_modulus in *. set (M := 2 ^ Z.of_N 64) in *.
  assert (HM : 0 < M) by (subst M; apply Z.pow_pos_nonneg; lia).
  rewrite Zplus_mod_idemp_r.
  replace (bv_unsigned ea + (bv_unsigned (wbv oa) - bv_unsigned (wbv ob))) with ((bv_unsigned ea + bv_unsigned (wbv oa)) - bv_unsigned (wbv ob)) by lia.
  rewrite <- Zminus_mod_idemp_l, H, Zminus_mod_idemp_l.
  replace (bv_unsigned ek + bv_unsigned (wbv ob) - bv_unsigned (wbv ob)) with (bv_unsigned ek) by lia. apply Z.mod_small. lia.
Qed.
Lemma alias_d_den : forall (ek' ek : word) (d off : w64),
  bv_add ek' (wbv d) = ek -> bv_add ek' (wbv (wadd off d)) = bv_add ek (wbv off).
Proof.
  intros ek' ek d off <-. rewrite ValP.wbv_wadd. apply bv_eq. rewrite !bv_add_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma anchor_aliases_sound : forall E fs k k' d, facts_hold E fs -> In (k', d) (anchor_aliases fs k) -> bv_add (ev E k') (wbv d) = ev E k.
Proof.
  intros E fs k k' d HF. induction fs as [|f fs IH]; [intros []|].
  apply Forall_cons_iff in HF as [Hf HF]. specialize (IH HF). cbn [anchor_aliases].
  destruct f as [| | | |a b| | |]; try exact IH.
  destruct a as [|k1 o1| | | | | | | | |]; try exact IH. destruct b as [|k2 o2| | | | | | | | |]; try exact IH.
  cbn [fact_holds den] in Hf.
  destruct (PrimInt63.eqb k2 k) eqn:E2.
  - apply Uint63.eqb_correct in E2. subst k2. intros [EQ|IN]; [| exact (IH IN)].
    injection EQ as <- <-. exact (alias_d_fact _ _ _ _ Hf).
  - destruct (PrimInt63.eqb k1 k) eqn:E1; [|exact IH]. apply Uint63.eqb_correct in E1. subst k1.
    intros [EQ|IN]; [| exact (IH IN)]. injection EQ as <- <-. exact (alias_d_fact _ _ _ _ (eq_sym Hf)).
Qed.
Lemma below_stack_sound : forall E st ms mo nn rest wl LB W aw v,
  st_ok asegs OPS E st ms mo -> CtrA.nonstack_windows nn rest = Some wl ->
  windows_wf (wins_of E nn rest) LB (ATOP + 4096) -> aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W ->
  below_stack (s_facts st) wl v = true -> bv_unsigned (den E v) <= ATOP.
Proof.
  intros E st ms mo nn rest wl LB W aw v HS NW WF ARW H. unfold below_stack in H.
  destruct v as [|k off| | | | | | | | |]; try discriminate H.
  destruct (below_stack_w (s_facts st) wl k off) eqn:BW.
  { exact (below_stack_w_sound E st ms mo nn rest wl LB W aw k off HS NW WF ARW BW). }
  apply existsb_exists in H as ([k' d] & IN & BW'). cbn [fst snd] in BW'.
  pose proof (anchor_aliases_sound E _ _ _ _ (so_facts _ _ _ _ _ _ HS) IN) as EV.
  pose proof (below_stack_w_sound E st ms mo nn rest wl LB W aw k' (wadd off d) HS NW WF ARW BW') as X.
  cbn [den] in X |- *. rewrite (alias_d_den _ _ d off EV) in X. exact X.
Qed.

Lemma aunw_chain : forall E st ms mo hargs nn md A nw rest ks offs rss W (L : alayout) RNG sta LBa PCz r lo,
  st_ok asegs OPS E st ms mo ->
  heap_nwin hargs = Some nn -> hargs = VL md :: A :: VL nw :: rest ->
  sp_region st = Some (ks, offs, rss) -> sp_floor_ok st hargs = true ->
  bv_unsigned (ev E ks) + loZ rss <= bv_unsigned (AP.getr (ms_regs ms) 2) ->
  ties W (wins_of E nn rest) -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  forall LB aw, windows_wf (wins_of E nn rest) LB (ATOP + 4096) -> aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W ->
  unw_ok UNIV PCz r st hargs = true -> incl UNIV (al_U L) ->
  bv_unsigned (AP.getr (ms_regs ms) 2) < 2 ^ 47 -> 0 <= to_Z r < 2 ^ 62 -> ATOP + 4096 <= lo ->
  rng RNG (ATOP + 4096) (al_top L - (ATOP + 4096)) ->
  (exists tr, aunw (ms_mem ms) L RNG lo PCz (AP.getr (ms_regs ms) 2) (AP.getr (ms_regs ms) 8) (Z_to_bv 64 (to_Z r)) tr)
  /\ bv_unsigned (AP.getr (ms_regs ms) 8) <> bv_unsigned (AP.getr (ms_regs ms) 2) + 8.
Proof.
  intros E st ms mo hargs nn md A nw rest ks offs rss W L RNG sta LBa PCz r lo HS Hn Eh SPR SFO LOSP TI AH LB aw WF ARW UO HU SP47 RR LO RSTK.
  destruct (unw_ok_inv PCz r st hargs nn md A nw rest UO Hn Eh) as (wl & NWL & I1 & SF & cands & WK & CA).
  pose proof (fun v => below_stack_sound E st ms mo nn rest wl LB W aw v HS NWL WF ARW) as BS0.
  assert (BS : forall v, below_stack (s_facts st) wl v = true -> bv_unsigned (den E v) < ATOP + 1) by (intros v Hv; pose proof (BS0 v Hv); lia).
  pose proof (GlueA.getr_RA asegs OPS E st ms mo HS) as GR.
  assert (SP2 : bv_unsigned (den E (getr st X2)) = bv_unsigned (AP.getr (ms_regs ms) 2%bv)) by (rewrite <- HeapCtr.reg_of_X2, (GR X2); reflexivity).
  assert (S02 : bv_unsigned (den E (getr st X8)) = bv_unsigned (AP.getr (ms_regs ms) 8%bv)) by (rewrite <- CallA.reg_of_X8, (GR X8); reflexivity).
  destruct (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _).
  assert (TOPB : forall wlo x, stack_window_key nn rest = Some wlo -> x - bv_unsigned (den E (VP STACK_ID wlo)) <= SPALT -> x <= al_top L).
  { intros wlo x SK D. destruct (CallA.stack_window_key_In E nn rest wlo SK) as (len & INw).
    pose proof (CallA.sp_floor_key asegs OPS E st ms mo hargs nn md A nw rest ks offs rss wlo HS SFO Hn Eh SPR SK) as FL.
    apply (stk0_sp_bound AI W (wins_of E nn rest) _ L RNG sta LBa (ms_mem ms) x TI INw); [reflexivity| | exact AH| exact D].
    cbn [w_lo]. unfold ZC_BASE. lia. }
  pose proof atop_range as ATR0.
  assert (LOWP : ATOP + 1 <= bv_unsigned (den E (getr st X2))).
  { rewrite SP2. destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & KZ & _).
    pose proof (so_reg _ _ _ _ _ _ HS _ _ Hrs) as RO. destruct (ro_range _ _ _ _ _ _ RO KZ) as [RLO _].
    assert (FLw : exists wlo, stack_window_key nn rest = Some wlo).
    { unfold sp_floor_ok in SFO. rewrite Hn, Eh, SPR in SFO. destruct (stack_window_key nn rest) as [wlo|]; [eexists; reflexivity| discriminate SFO]. }
    destruct FLw as [wlo SK]. destruct (CallA.stack_window_key_In E nn rest wlo SK) as (len & INw).
    pose proof (CallA.sp_floor_key asegs OPS E st ms mo hargs nn md A nw rest ks offs rss wlo HS SFO Hn Eh SPR SK) as FL.
    pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
    destruct KDs as [[_ C]|[[K _]|[K _]]]; [lia| unfold K_BLOCK, K_STACK in K; lia| unfold K_SUB, K_STACK in K; lia]. }
  destruct (CallU.unw_walk_sound OPS E st ms mo hargs nn md A nw rest wl (al_top L) (ATOP + 1) PCz HS Hn Eh TOPB TOP47 BS _ _ _ _ _ LOWP WK) as (tr & Htr & UC).
  rewrite SP2, S02 in UC. destruct (CA tr Htr) as [LEN INU].
  split.
  - exists tr. unfold aunw.
    destruct (Z_lt_le_dec (bv_unsigned (AP.getr (ms_regs ms) 2%bv) + 16) (al_top L)) as [LT|GE].
    + left. split; [exact LT|]. split; [exact UC|]. split; [exact LEN|]. split.
      * apply HU. rewrite Z_to_bv_small by (unfold bv_modulus; lia). exact INU.
      * destruct (Z_le_gt_dec lo (al_top L)) as [LE|GT].
        -- eapply rng_sub'; [exact RSTK|]. lia.
        -- destruct RSTK as (X & Y & H). split; [lia|]. split; [lia|]. intros b j Hb Hj. lia.
    + right. split; [exact GE|]. split; [exact SP47|]. apply HU. exact I1.
  - destruct (CallU.s0_far_sound asegs OPS E st ms mo wl (ATOP + 1) HS SF BS LOWP ltac:(rewrite SP2; exact SP47)) as [X|X]; rewrite SP2, S02 in X; lia.
Qed.

Lemma amalloc_apply_inv : forall st sts, amalloc_apply UNIV AMALLOC_PC st = Some sts ->
  exists r tp hargs cred st1,
    call_pre st = Some r /\ getr st X4 = VL tp /\ find_op HEAP_ID (s_ops st) = Some hargs /\ heap_A hargs = Some cred
    /\ weqb tp (wlit ATPi) = true /\ stack_room_g st AMALLOC_ROOM = true /\ sp_floor_ok st hargs = true
    /\ unw_ok UNIV AMALLOC_PC r st hargs = true /\ sp_top_ok st = true /\ ret_ok AMALLOC_PC r = true
    /\ KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (getr st X10) = true /\ KnownT.KnownT.known_leu_t (s_facts st) (getr st X10) (VL AREQMAXw) = true
    /\ cred_pre (s_facts st) (getr st X10) cred = true
    /\ (if sec_decided (s_facts st) (getr st X10) then true else prist_absent (s_facts st) hargs) = true
    /\ twins_intact st hargs = true
    /\ forget_stack_below_sp_g st = Some st1
    /\ exists stN tl, sts = stN :: tl /\ null_post hargs cred (clobber st1) r = Some stN.
Proof.
  intros st sts H. unfold amalloc_apply in H.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |] eqn:TP; try discriminate.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:FO; [|discriminate].
  destruct (heap_A hargs) as [cred|] eqn:HA; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  do 11 (apply andb_prop in CK as [CK ?]).
  destruct (forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate].
  destruct (null_post hargs cred (clobber st1) r) as [stN|] eqn:NP; [|discriminate].
  destruct (fresh (clobber st1)) as [k st3] eqn:F1. destruct (fresh st3) as [sh st4] eqn:F2.
  destruct (heap_set_A hargs (cred_post (s_facts st) (getr st X10) cred)) as [h1|]; [|discriminate].
  destruct (heap_add_window h1 (VP k wzero) (getr st X10) (VL CtrLib.K_BLOCK)) as [h2|]; [|discriminate].
  destruct (heap_add_window h2 (VP sh wzero) (twin_len (getr st X10)) (VL K_TWIN)) as [h3|]; [|discriminate].
  destruct (fresh st4) as [s2 st4b] eqn:F3.
  injection H as <-.
  exists r, tp, hargs, cred, st1. repeat (split; [first [assumption | reflexivity]|]).
  repeat match goal with |- exists _ _, (if ?c then _ else _) = _ /\ _ => destruct c end; do 2 eexists; (split; [reflexivity| exact NP]).
Qed.

Lemma aheap_call_facts : forall E st ms mo hargs wnl,
  st_ok asegs OPS E st ms mo -> aheap_windows st = Some (hargs, wnl) ->
  exists r1 n md A nw rest LB,
    IMap.find STACK_ID (s_regs st) = Some r1 /\ find_op HEAP_ID (s_ops st) = Some hargs /\ CtrA.count_op HEAP_ID (s_ops st) = 1%nat
    /\ heap_nwin hargs = Some n /\ hargs = VL md :: A :: VL nw :: rest
    /\ wt nw = false /\ n = Z.to_nat (to_Z (wl nw)) /\ (3 * n <= length rest)%nat /\ (n <= 255)%nat
    /\ stack_window_ok_g n rest (rg_lo r1) = true /\ CtrA.nonstack_windows n rest = Some wnl
    /\ CtrA.windows_anchored (s_regs st) wnl = true /\ aregions_justified st wnl = true
    /\ aw_holds_asan AI ACCT UNIV (den E A) LB (ms_mem ms) mo
    /\ windows_wf (wins_of E n rest) LB (ATOP + 4096)
    /\ cw_holds Cw (w2Z md) (map (den E) (skipn (3 * n) rest)) LB (wins_of E n rest) (ms_mem ms)
    /\ exists W, aw_realW AI ACCT UNIV (den E A) LB (ms_mem ms) mo W /\ ties W (wins_of E n rest).
Proof.
  intros E st ms mo hargs wnl HS HW.
  destruct (CallA.aheap_windows_inv st hargs wnl HW) as (Hf & Hc & r1 & n & md & A & nw & rest & Hr1 & Hn & Eh & T & N & L & N255 & SW & NW & AN & JU & TS).
  pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (so_ops _ _ _ _ _ _ HS) Hf) as HH.
  rewrite OPS_holds1 in HH. destruct HH as (md' & aw & ws & ca & LB & W & D & HWw & WF & HC & TI).
  rewrite Eh, (decode_hargs E md A nw rest n T N L) in D. injection D as <- <- <- <-.
  exists r1, n, md, A, nw, rest, LB.
  split; [exact Hr1|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hn|]. split; [exact Eh|]. split; [exact T|]. split; [exact N|].
  split; [exact L|]. split; [exact N255|]. split; [exact SW|]. split; [exact NW|]. split; [exact AN|]. split; [exact JU|].
  split; [exists W; exact HWw|]. split; [exact WF|]. split; [exact HC|].
  exists (set_ms W (ms_mem ms)). split; [| apply ties_set_ms; exact TI].
  apply (aw_holds_real_w AI ACCT UNIV AI_fake W (den E A) LB (ms_mem ms) mo HWw).
  intros b HbT NPRIM g G0 G1. set (A0 := ab_addr b) in *. set (n0 := ab_size b) in *. pose proof atop_range as AR.

  pose proof (proj1 TI b HbT) as WIN. fold A0 n0 in WIN.
  destruct (HeapCtrB.wins_cover E n rest wnl _ NW WIN) as [KS|(sh & len & kd & Iw & EW)]; [cbn in KS; unfold K_TWINz, K_STACK in KS; lia|].
  injection EW as E1 E2 E3.
  assert (KD : weqb kd K_TWIN = true) by (apply weqb_w2Z; rewrite <- E3; reflexivity).
  destruct (CallA.twins_scan_sound _ _ _ _ sh len kd TS Iw KD) as [OLD|EVA].
  2:{
      exfalso. pose proof (CallA.twin_small_sound E _ _ (so_facts _ _ _ _ _ _ HS) EVA) as LW.
      destruct (twin_T_facts AI ACCT UNIV W _ _ _ _ b HWw HbT) as (_ & _ & _ & _ & _ & NR & _). fold n0 in NR.
      unfold shlen in E2. rewrite Z.shiftr_div_pow2 in E2 by lia. change (2 ^ 3) with 8 in E2.
      rewrite (is_primary_le n0) in NPRIM; [discriminate|]. clear - E2 LW NR. Z.div_mod_to_equations. lia. }
  destruct (CallA.twin_arm_old_inv _ _ _ _ _ OLD) as (k & r & nsv & BT & FR & WL & LEN & ALT).
  pose proof (HeapCtrB.win_lookup_In _ _ _ _ WL) as Ik.
  destruct (HeapCtrB.nonstack_windows_In E n rest wnl k nsv CtrLib.K_BLOCK NW Ik) as (_ & _ & _ & INk).
  destruct (HeapCtrB.nonstack_windows_In E n rest wnl sh len kd NW Iw) as (SH0 & _).

  pose proof (proj1 (Forall_forall _ _) WF _ INk) as (W1 & W2 & W3 & KDs). cbn [w_kind w_lo w_len w_iv] in KDs, W1, W2, W3.
  assert (HB : In (bv_unsigned (ev E k), bv_unsigned (den E nsv)) LB).
  { replace (w2Z CtrLib.K_BLOCK) with 1 in KDs by (vm_compute; reflexivity).
    destruct KDs as [[K _]|[[_ B]|[K _]]]; [unfold K_STACK in K; lia| exact B| unfold K_SUB in K; lia]. }
  pose proof (CallA.block_of_twin_sound E _ sh k (so_facts _ _ _ _ _ _ HS) BT) as LK.
  assert (SHEQ : shad (bv_unsigned (ev E k)) = shad A0).
  { rewrite E1. rewrite LK. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. change (bv_modulus 64) with (2 ^ 64) in RK.
    rewrite Z.mod_small; [lia|]. clear - RK. Z.div_mod_to_equations. lia. }
  destruct (twin_owner_w AI ACCT UNIV AI_fake W _ _ _ _ b _ _ HWw HbT HB SHEQ) as (EA & EN & NR). fold A0 n0 in EA, EN, NR.

  assert (SHNZ : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact SH0).
  destruct ALT as [PD|[[TR SS]|[TM [s2 TSC]]]].
  { exfalso. pose proof (CallA.prim_decided_sound E _ nsv (so_facts _ _ _ _ _ _ HS) PD) as LE64. rewrite EN in LE64.
    rewrite (is_primary_le n0 ltac:(lia)) in NPRIM. discriminate. }
  2:{
      pose proof (CallA.twin_pair_sound asegs (s_priv st) E (ms_mem ms) (s_facts st) (s_regs st) sh r nsv s2 (so_facts _ _ _ _ _ _ HS)
                    (so_reg _ _ _ _ _ _ HS) FR SHNZ TM TSC) as PATP.
      rewrite EN in PATP. rewrite <- E1 in PATP. apply PATP; [clear - NR; lia| | exact G0| exact G1].
      pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. change (bv_modulus 64) with (2 ^ 64) in RK. rewrite EA in RK.
      unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold AREQMAX in NR. clear - RK NR. Z.div_mod_to_equations. lia. }

  pose proof (so_reg _ _ _ _ _ _ HS sh r FR) as RO.
  pose proof (CallA.size_shape_sound E _ nsv (so_facts _ _ _ _ _ _ HS) SS) as SHAPE.
  pose proof (CallA.is_twin_region_sound asegs (s_priv st) E (ms_mem ms) sh r nsv RO SHNZ TR) as PATR.
  rewrite EN in PATR. rewrite <- E1 in PATR.
  apply PATR; [unfold AREQMAX in NR; lia| | exact G0| exact G1].
  destruct nsv; try exact I; rewrite <- EN; exact SHAPE.
Qed.

Definition find_sliver (st : sstate) (ks : int) : option int :=
  match List.find (fun kr : int * region => negb (PrimInt63.eqb (fst kr) 0%uint63) && negb (PrimInt63.eqb (fst kr) ks)
                      && sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) (fst kr) (snd kr)) (IMap.elements (s_regs st)) with
  | Some kr => Some (fst kr)
  | None => None
  end.
Definition sp_lo (E : env) (st : sstate) : Z :=
  match sp_region st with
  | Some (k, _, rs) => match find_sliver st k with Some b => bv_unsigned (ev E b) | None => bv_unsigned (ev E k) + loZ rs end
  | None => 0
  end.

Lemma find_sliver_spec : forall st ks b, IMap.bst (s_regs st) -> find_sliver st ks = Some b ->
  exists r, IMap.find b (s_regs st) = Some r /\ b <> 0%uint63 /\ b <> ks
    /\ sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) b r = true.
Proof.
  intros st ks b BST H. unfold find_sliver in H.
  match type of H with match ?f with _ => _ end = _ => destruct f as [[b0 r0]|] eqn:F; [|discriminate H] end. injection H as <-. cbn [fst].
  apply List.find_some in F as [IN CK]. cbn [fst snd] in CK. apply andb_prop in CK as [CK SJ]. apply andb_prop in CK as [N0 NK].
  apply negb_true_iff in N0, NK. apply Uint63.eqb_false_spec in N0, NK.
  exists r0. split; [apply (IMap.elements_spec _ _ _ BST); exact IN|]. auto.
Qed.

Lemma stack_wlo_ceiling : forall E st hargs n md A nw rest LB wlo,
  find_op HEAP_ID (s_ops st) = Some hargs -> heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest ->
  windows_wf (wins_of E n rest) LB (ATOP + 4096) -> stack_wlo st = Some wlo ->
  ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo)).
Proof.
  intros E st hargs n md A nw rest LB wlo Hf Hn Eh WF SW. unfold stack_wlo in SW. rewrite Hf, Hn, Eh in SW.
  destruct (stack_window_key n rest) as [w|] eqn:SK; [|discriminate SW]. destruct (nowrap_kb (s_facts st) STACK_ID w); [|discriminate SW]. injection SW as ->.
  destruct (CallA.stack_window_key_In E n rest wlo SK) as (len & INw).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  destruct KDs as [[_ C]|[[K _]|[K _]]]; [exact C| unfold K_BLOCK, K_STACK in K; lia| unfold K_SUB, K_STACK in K; lia].
Qed.

Lemma sp_lo_spec : forall E st ms mo ks offs rss hargs n md A nw rest LB,
  st_ok asegs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) ->
  find_op HEAP_ID (s_ops st) = Some hargs -> heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest ->
  windows_wf (wins_of E n rest) LB (ATOP + 4096) ->
  ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss -> bv_unsigned (ev E ks) + loZ rss <= 2 ^ 64 ->
  (ATOP + 4096 <= sp_lo E st <= bv_unsigned (ev E ks) + loZ rss)
  /\ stk asegs (ms_mem ms) (sp_lo E st) (bv_unsigned (ev E ks) + loZ rss).
Proof.
  intros E st ms mo ks offs rss hargs n md A nw rest LB HS SPR Hf Hn Eh WF FLOOR TOP. pose proof atop_range as ATR.
  unfold sp_lo. rewrite SPR. destruct (find_sliver st ks) as [b|] eqn:FS.
  - destruct (find_sliver_spec st ks b (so_bst _ _ _ _ _ _ HS) FS) as (r & Fb & B0 & BK & SJ).
    destruct (CallA.sliver_just_sound asegs OPS E st ms mo ks offs rss b r HS SPR Fb B0 SJ) as (RC & RB & RW & L0 & wlo & SW & EK & EH).
    pose proof (stack_wlo_ceiling E st hargs n md A nw rest LB wlo Hf Hn Eh WF SW) as CE.
    pose proof (bv_unsigned_in_range 64 (den E (rg_hi r))) as RH. unfold bv_modulus in RH. fold (hiZ E r) in RH.
    split; [rewrite EK; lia|].
    assert (BZ : PrimInt63.eqb b 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact B0).
    pose proof (so_reg _ _ _ _ _ _ HS b r Fb) as RO.
    unfold stk. split; [lia|]. split; [exact TOP|]. intros a Ha.
    destruct (ro_valid _ _ _ _ _ _ RO BZ a ltac:(rewrite L0; lia)) as (V1 & V2 & _).
    split; [apply (GlueA.wb_wviewA asegs); apply V2; exact RW|]. rewrite (GlueA.rb_mrdA asegs) in V1.
    destruct (ALib.Mem.mrd asegs (ms_mem ms) (ALib.Mem.wa a)); [eexists; reflexivity| congruence].
  - split; [lia|]. apply stk_empty. lia.
Qed.

Lemma stk_sp_region : forall E st (m' : amem) ks offs rss sp, sp_region st = Some (ks, offs, rss) ->
  sp_lo E st <= bv_unsigned (ev E ks) + loZ rss <= sp ->
  stk asegs m' (sp_lo E st) sp -> stk asegs m' (bv_unsigned (ev E ks) + loZ rss) sp.
Proof. intros E st m' ks offs rss sp SPR LE ST. exact (proj2 (stk_split asegs m' _ _ _ ST LE)). Qed.

Lemma sp_lo_of_sliver : forall E st ms mo ks offs rss k0 rg,
  st_ok asegs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) ->
  IMap.find k0 (s_regs st) = Some rg -> k0 <> 0%uint63 -> k0 <> ks ->
  sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k0 rg = true ->
  sp_lo E st = bv_unsigned (ev E k0) /\ loZ rg = 0 /\ bv_unsigned (ev E k0) + hiZ E rg = bv_unsigned (ev E ks) + loZ rss
  /\ rg_cells rg = IMap.Leaf /\ rg_bg rg = BGNone
  /\ exists wlo, stack_wlo st = Some wlo /\ bv_unsigned (ev E k0) = bv_unsigned (den E (VP STACK_ID wlo)).
Proof.
  intros E st ms mo ks offs rss k0 rg HS SPR Fk K0 KS SJ.
  destruct (CallA.sliver_just_sound asegs OPS E st ms mo ks offs rss k0 rg HS SPR Fk K0 SJ) as (RC & RB & RW & L0 & wlo & SW & EK & EH).
  split; [| split; [exact L0| split; [exact EH| split; [exact RC| split; [exact RB| exists wlo; split; [exact SW| exact EK]]]]]].
  unfold sp_lo. rewrite SPR. destruct (find_sliver st ks) as [b|] eqn:FS.
  - destruct (find_sliver_spec st ks b (so_bst _ _ _ _ _ _ HS) FS) as (r & Fb & B0 & BK & SJb).
    destruct (CallA.sliver_just_sound asegs OPS E st ms mo ks offs rss b r HS SPR Fb B0 SJb) as (_ & _ & _ & _ & wlo' & SW' & EK' & _).
    rewrite SW in SW'. injection SW' as <-. rewrite EK, EK'. reflexivity.
  - exfalso. unfold find_sliver in FS.
    match type of FS with match ?f with _ => _ end = _ => destruct f as [kr|] eqn:F; [discriminate FS|] end.
    pose proof (List.find_none _ _ F (k0, rg) (proj2 (IMap.elements_spec _ _ _ (so_bst _ _ _ _ _ _ HS)) Fk)) as X. cbn [fst snd] in X.
    rewrite SJ in X. apply Uint63.eqb_false_spec in K0, KS. rewrite K0, KS in X. discriminate X.
Qed.

Lemma sp_lo_le : forall E st ms mo ks offs rss, st_ok asegs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) ->
  sp_lo E st <= bv_unsigned (ev E ks) + loZ rss.
Proof.
  intros E st ms mo ks offs rss HS SPR. unfold sp_lo. rewrite SPR. destruct (find_sliver st ks) as [b|] eqn:FS; [| lia].
  destruct (find_sliver_spec st ks b (so_bst _ _ _ _ _ _ HS) FS) as (r & Fb & B0 & BK & SJb).
  destruct (CallA.sliver_just_sound asegs OPS E st ms mo ks offs rss b r HS SPR Fb B0 SJb) as (_ & _ & _ & _ & wlo & _ & _ & EH).
  pose proof (bv_unsigned_in_range 64 (den E (rg_hi r))) as RH. fold (hiZ E r) in RH. lia.
Qed.

Lemma sliver_low : forall E st ms mo ks offs rss k r hargs n md A nw rest LB a,
  st_ok asegs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) -> IMap.find k (s_regs st) = Some r -> k <> 0%uint63 -> k <> ks ->
  sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k r = true ->
  find_op HEAP_ID (s_ops st) = Some hargs -> hargs = VL md :: A :: VL nw :: rest -> wt nw = false -> n = Z.to_nat (to_Z (wl nw)) ->
  (3 * n <= length rest)%nat -> windows_wf (wins_of E n rest) LB (ATOP + 4096) ->
  bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r ->
  ATOP + 4096 <= a < bv_unsigned (ev E ks) + loZ rss.
Proof.
  intros E st ms mo ks offs rss k r hargs n md A nw rest LB a HS SPR Fk K0 KS SL Hf Eh Tnw Nn Ln WF Ha.
  destruct (sp_lo_of_sliver E st ms mo ks offs rss k r HS SPR Fk K0 KS SL) as (_ & L0 & EH & _ & _ & wlo & SW & EKW).
  pose proof (CallV.wlo_floor E st hargs n md A nw rest LB (ATOP + 4096) wlo Hf Eh Tnw Nn Ln WF SW) as CE. rewrite L0 in Ha. lia.
Qed.

Lemma sliver_region_ok : forall E E' st ms mo (m' : amem) ks offs rss k0 rg sp,
  st_ok asegs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) ->
  IMap.find k0 (s_regs st) = Some rg -> k0 <> 0%uint63 -> k0 <> ks ->
  sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k0 rg = true ->
  ev E' k0 = ev E k0 -> hiZ E' rg = hiZ E rg ->
  bv_unsigned (ev E ks) + loZ rss <= sp -> stk asegs m' (sp_lo E st) sp ->
  region_ok asegs (s_priv st) E' m' k0 rg.
Proof.
  intros E E' st ms mo m' ks offs rss k0 rg sp HS SPR Fk K0 KS SJ EK' EH' LE ST.
  destruct (sp_lo_of_sliver E st ms mo ks offs rss k0 rg HS SPR Fk K0 KS SJ) as (ELO & L0 & EH & RC & RB & _).
  pose proof (so_reg _ _ _ _ _ _ HS k0 rg Fk) as RO.
  assert (KZ : PrimInt63.eqb k0 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  destruct ST as (_ & _ & ST).
  constructor.
  - exact (ro_bst _ _ _ _ _ _ RO).
  - intros _. rewrite EK', EH'. exact (ro_range _ _ _ _ _ _ RO KZ).
  - intros _ a Ha. rewrite EK', EH' in Ha.
    destruct (ro_valid _ _ _ _ _ _ RO KZ a Ha) as (_ & _ & SEG).
    destruct (ST a ltac:(rewrite ELO; rewrite L0 in Ha; lia)) as [WV (bb & MR)].
    split; [rewrite (GlueA.rb_mrdA asegs), MR; discriminate|]. split; [intros _; apply (GlueA.wb_wviewA asegs); exact WV| exact SEG].
  - intros g gr Fg. rewrite RC in Fg. discriminate Fg.
  - intros g gr c i Fg. rewrite RC in Fg. discriminate Fg.
  - intros o _ _ _. unfold bg_byte. rewrite RB. exact I.
Qed.

Lemma ATPi_eq : to_Z ATPi = ATP. Proof. reflexivity. Qed.

Definition acall_facts (XN : r5) (E : env) (st : sstate) (ms : machine_state) (mo : Model)
    (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (n : Z) : Prop :=
  exists (LB : blocks) (r : int) (hargs : list sv) (st1 : sstate) (ks : int) (offs : w64) (rss : region) (ksp : int)
         (wnl : list (int * sv * w64)) (nn : nat) (md : w64) (A : sv) (nw : w64) (rest : list sv),
    call_pre st = Some r /\ forget_stack_below_sp_g st = Some st1
    /\ sp_region st = Some (ks, offs, rss) /\ okey offs = Some ksp
    /\ bv_unsigned (AP.getr (ms_regs ms) 2%bv) = bv_unsigned (ev E ks) + keyZ ksp
    /\ keyZ ksp mod 16 = 0 /\ loZ rss <= keyZ ksp /\ ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss
    /\ find_op HEAP_ID (s_ops st) = Some hargs /\ CtrA.count_op HEAP_ID (s_ops st) = 1%nat
    /\ hargs = VL md :: A :: VL nw :: rest /\ wt nw = false /\ nn = Z.to_nat (to_Z (wl nw)) /\ (3 * nn <= length rest)%nat /\ (nn <= 255)%nat
    /\ CtrA.nonstack_windows nn rest = Some wnl /\ aregions_justified st wnl = true
    /\ windows_wf (wins_of E nn rest) LB (ATOP + 4096)
    /\ cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) (ms_mem ms)
    /\ aw = den E A
    /\ (exists W, wit_of W L RNG sta LBa /\ aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W /\ ties W (wins_of E nn rest))
    /\ bv_unsigned (den E (getr st XN)) = n /\ (XN = X11 -> exists w, getr st XN = VL w).

Definition prist_in (E : env) (st : sstate) : Prop :=
  exists hargs md A nw rest, find_op HEAP_ID (s_ops st) = Some hargs /\ hargs = VL md :: A :: VL nw :: rest
    /\ In prist_win (wins_of E (Z.to_nat (to_Z (wl nw))) rest).
Lemma prist_absent_not_in : forall E st hargs, facts_hold E (s_facts st) -> find_op HEAP_ID (s_ops st) = Some hargs ->
  prist_absent (s_facts st) hargs = true -> ~ prist_in E st.
Proof.
  intros E st hargs HF FO PA (h2 & md & A & nw & rest & FO2 & Eh & IP). rewrite FO in FO2. injection FO2 as <-.
  unfold prist_absent in PA. destruct (heap_nwin hargs) as [n|] eqn:HN; [|discriminate].
  destruct (heap_nwin_shape hargs n HN) as (md' & A' & nw' & rest' & Eh' & T & N & Ln). rewrite Eh in Eh'. injection Eh' as <- <- <- <-.
  rewrite Eh in PA. subst n. exact (CallA.wins_not_prist_sound E _ HF _ _ PA IP).
Qed.

Lemma prist_in_aprist : forall XN E st ms mo L RNG sta LBa aw n, acall_facts XN E st ms mo L RNG sta LBa aw n -> prist_in E st -> aprist sta.
Proof.
  intros XN E st ms mo L RNG sta LBa aw n CF (h2 & md2 & A2 & nw2 & rest2 & FO2 & Eh2 & IP).
  destruct CF as (LB & r & hargs & st1 & ks & offs & rss & ksp & wnl & nn & md & A & nw & rest
                  & CP & FS & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255 & NW & AJ & WF & HC & AWden & (W & WOF & AR & TI) & NDEN & SHAPE).
  rewrite Hf in FO2. injection FO2 as <-. rewrite Eh in Eh2. injection Eh2 as <- <- <- <-. rewrite <- Nn in IP.
  destruct WOF as (_ & _ & <- & _). exact (ties_prist W _ TI IP).
Qed.

Lemma amalloc_pre_facts : forall st sts E ms mo,
  st_ok asegs OPS E st ms mo -> to_Z (s_pc st) = AMALLOC_SYM -> amalloc_apply UNIV AMALLOC_PC st = Some sts ->
  let R := ms_regs ms in
  let lo := sp_lo E st in
  exists (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (n : Z),
    ms = MS R (ms_fregs ms) (Z_to_bv 64 AMALLOC_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom asegs)
    /\ AHEAP AI L RNG sta LBa (ms_mem ms) /\ ACCT aw L RNG sta LBa mo /\ incl UNIV (al_U L)
    /\ ALib.Mem.mem_inv asegs (ms_mem ms)
    /\ stk asegs (ms_mem ms) lo (bv_unsigned (AP.getr R 2)) /\ ATOP + 4096 <= lo /\ lo <= bv_unsigned (AP.getr R 2) - 4608
    /\ AP.getr R 4 = Z_to_bv 64 ATP /\ AP.getr R 10 = Z_to_bv 64 n /\ 1 <= n <= AREQMAX
    /\ (1048576 <= bv_unsigned aw /\ (prim_decided (s_facts st) (getr st X10) = true \/ n <= bv_unsigned aw))
    /\ (exists tr, aunw (ms_mem ms) L RNG lo AMALLOC_PC (AP.getr R 2) (AP.getr R 8) (AP.getr R 1) tr)
    /\ bv_unsigned (AP.getr R 8) <> bv_unsigned (AP.getr R 2) + 8 /\ 4096 <= bv_unsigned (AP.getr R 1)
    /\ bv_unsigned (AP.getr R 1) <> AMALLOC_PC
    /\ bv_unsigned (AP.getr R 2) mod 16 = 0 /\ rng RNG lo (bv_unsigned (AP.getr R 2) - lo)
    /\ acall_facts X10 E st ms mo L RNG sta LBa aw n
    /\ (64512 < n \/ ~ prist_in E st).
Proof.
  intros st sts E ms mo HS HPC Happ R lo.
  destruct (amalloc_apply_inv st sts Happ) as (r & tp & hargs & cred & st1 & CP & TP & FO & HAc & TPE & SR & SFO & UO & SPT & RO & N0 & N1 & NC & PRA & TI & FS & _).
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.

  unfold twins_intact in TI. destruct (aheap_windows st) as [[h wnl]|] eqn:HW; [|discriminate]. clear TI.
  destruct (aheap_call_facts E st ms mo h wnl HS HW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (aw_realW_AHEAP AI ACCT UNIV _ _ _ _ _ ARW) as (AH & AC & HU).
  set (L := w_L W) in *. set (RNG := w_RNG W) in *. set (sta := w_st W) in *. set (LBa := w_LBa W) in *.
  rewrite FO in Hf. injection Hf as <-. rewrite Eh, heap_A_eq in HAc. injection HAc as <-.

  destruct (CallA.stack_sound_g asegs OPS E st ms mo AMALLOC_ROOM HS ltac:(vm_compute; reflexivity) SR)
    as (k & off & rs & ksp & HX2 & Hr & K0 & Hksp & K16 & A16 & Esp & LO0 & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.sp_floor_sound asegs OPS E st ms mo hargs n md A nw rest k off rs HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K _]|[K _]]]; [exact C| unfold K_BLOCK, K_STACK in K; lia| unfold K_SUB, K_STACK in K; lia]. }

  destruct (CallA.amalloc_regs asegs OPS E st ms mo r tp A HS CP TP TPE N0 N1 NC) as (RV & RA & RR & TP4 & N10 & NCR).
  fold R in RA, TP4, N10, NCR.
  pose proof (GlueA.getr_RA asegs OPS E st ms mo HS) as GR.
  assert (SP2 : bv_unsigned (AP.getr R 2) = bv_unsigned (ev E k) + keyZ ksp).
  { unfold R. rewrite <- HeapCtr.reg_of_X2, (GR X2). exact Esp. }
  assert (SP47 : bv_unsigned (AP.getr R 2) < 2 ^ 47).
  { unfold sp_top_ok in SPT. pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF SPT) as X. unfold R. rewrite <- HeapCtr.reg_of_X2, (GR X2).
    replace (bv_unsigned (den E (VL SP_TOPw))) with (2 ^ 47) in X by (vm_compute; reflexivity). exact X. }
  assert (RA1 : bv_unsigned (AP.getr R 1) = to_Z r) by (rewrite RA; apply Z_to_bv_small; unfold bv_modulus; lia).
  unfold ret_ok in RO. apply andb_prop in RO as [R4096 RNE]. apply Uint63.leb_spec in R4096. change (to_Z 4096%uint63) with 4096 in R4096.
  apply negb_true_iff in RNE. apply Z.eqb_neq in RNE.
  pose proof (ACCT_rng _ _ _ _ _ _ AC) as RSTK. pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _). pose proof atop_range as AR.
  set (sp := bv_unsigned (AP.getr R 2)) in *.
  destruct (sp_lo_spec E st ms mo k off rs hargs n md A nw rest LB HS SPR FO Hn Eh WF ltac:(lia) ltac:(pose proof (Uint63.to_Z_bounded AMALLOC_ROOM); lia)) as [[LOB LOLE] STKlo]. fold lo in LOB, LOLE, STKlo.
  assert (ASTK : to_Z AMALLOC_ROOM = 12288) by reflexivity.
  exists L, RNG, sta, LBa, (den E A), (bv_unsigned (AP.getr R 10)).
  split. { rewrite <- HPC. exact (GlueA.ms_formA asegs OPS E st ms mo HS RV). }
  split; [exact AH|]. split; [exact AC|]. split; [exact HU|].
  split. { intros a b Hm. unfold ALib.Mem.ro_addr. destruct (find_segment asegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
           rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity. }
  split. { rewrite SP2. apply (stk_merge asegs _ lo (bv_unsigned (ev E k) + loZ rs)); [exact STKlo| exact STK| lia]. }
  split; [exact LOB|]. split; [lia|].
  split; [rewrite TP4, ATPi_eq; reflexivity|].
  split; [symmetry; apply Z_to_bv_bv_unsigned|].
  split; [unfold AREQMAX; lia|]. split; [exact NCR|].
  destruct (aunw_chain E st ms mo hargs n md A nw rest k off rs W L RNG sta LBa AMALLOC_PC r lo HS Hn Eh SPR SFO
              ltac:(fold R; fold sp; rewrite SP2; lia) TI AH LB (den E A) WF ARW UO HU SP47 RR LOB ltac:(eapply rng_sub'; [exact RSTK|]; lia)) as [AUNW S0NE].
  split. { rewrite RA. exact AUNW. }
  split; [exact S0NE|]. split; [lia|]. split; [rewrite RA1; exact RNE|].
  split. { fold sp. rewrite SP2. rewrite Z.add_mod, A16, K16 by lia. reflexivity. }
  split; [eapply rng_sub'; [exact RSTK|]; lia|].
  split.
  2: { destruct (sec_decided (s_facts st) (getr st X10)) eqn:SD.
       - left. pose proof (CallA.sec_decided_sound E _ _ HF SD) as Q. unfold R. rewrite <- HeapCtr.reg_of_X10, (GR X10). exact Q.
       - right. exact (prist_absent_not_in E st _ HF FO PRA). }
  exists LB, r, hargs, st1, k, off, rs, ksp, wnl, n, md, A, nw, rest.
  split; [exact CP|]. split; [exact FS|]. split; [exact SPR|]. split; [exact Hksp|]. split; [exact SP2|]. split; [exact K16|].
  split; [lia|]. split; [lia|]. split; [exact FO|]. split; [exact Hc|]. split; [exact Eh|]. split; [exact T|]. split; [exact N|].
  split; [exact Ln|]. split; [exact N255|]. split; [exact NW|]. split; [exact JU|]. split; [exact WF|]. split; [exact HC|].
  split; [reflexivity|]. split; [exists W; split; [apply wit_of_refl| split; [exact ARW| exact TI]]|].
  split; [| intros X; discriminate X]. unfold R. rewrite <- HeapCtr.reg_of_X10, (GR X10). reflexivity.
Qed.

Lemma aaligned_apply_inv : forall st sts, aaligned_apply UNIV F_aaligned_iseg.AALIGNED_PC st = Some sts ->
  exists r tp hargs cred st1 al,
    call_pre st = Some r /\ getr st X4 = VL tp /\ find_op HEAP_ID (s_ops st) = Some hargs /\ heap_A hargs = Some cred
    /\ getr st X10 = VL al /\ weqb al (wlit 16%uint63) = true /\ aligned_size_ok (getr st X11) = true
    /\ weqb tp (wlit ATPi) = true /\ stack_room_g st AMALLOC_ROOM = true /\ sp_floor_ok st hargs = true
    /\ unw_ok UNIV F_aaligned_iseg.AALIGNED_PC r st hargs = true /\ sp_top_ok st = true /\ ret_ok F_aaligned_iseg.AALIGNED_PC r = true
    /\ cred_pre (s_facts st) (getr st X11) cred = true
    /\ prist_absent (s_facts st) hargs = true
    /\ twins_intact st hargs = true
    /\ forget_stack_below_sp_g st = Some st1
    /\ exists stN stB, sts = [stN; stB] /\ null_post hargs cred (clobber st1) r = Some stN.
Proof.
  intros st sts H. unfold aaligned_apply in H.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |] eqn:TP; try discriminate.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:FO; [|discriminate].
  destruct (getr st X10) as [al| | | | | | | | | |] eqn:X10E; try discriminate.
  destruct (heap_A hargs) as [cred|] eqn:HA; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  do 11 (apply andb_prop in CK as [CK ?]).
  destruct (forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate].
  destruct (null_post hargs cred (clobber st1) r) as [stN|] eqn:NP; [|discriminate].
  destruct (fresh (clobber st1)) as [k st3] eqn:F1. destruct (fresh st3) as [sh st4] eqn:F2.
  destruct (heap_set_A hargs (cred_post (s_facts st) (getr st X11) cred)) as [h1|]; [|discriminate].
  destruct (heap_add_window h1 (VP k wzero) (getr st X11) (VL CtrLib.K_BLOCK)) as [h2|]; [|discriminate].
  destruct (heap_add_window h2 (VP sh wzero) (twin_len (getr st X11)) (VL K_TWIN)) as [h3|]; [|discriminate].
  injection H as <-.
  exists r, tp, hargs, cred, st1, al. repeat (split; [first [assumption | reflexivity]|]).
  do 2 eexists. split; [reflexivity| exact NP].
Qed.

Lemma aaligned_pre_facts : forall st sts E ms mo,
  st_ok asegs OPS E st ms mo -> to_Z (s_pc st) = F_aaligned_iseg.AALIGNED_SYM -> aaligned_apply UNIV F_aaligned_iseg.AALIGNED_PC st = Some sts ->
  let R := ms_regs ms in
  let lo := sp_lo E st in
  exists (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (n : Z),
    ms = MS R (ms_fregs ms) (Z_to_bv 64 F_aaligned_iseg.AALIGNED_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom asegs)
    /\ AHEAP AI L RNG sta LBa (ms_mem ms) /\ ACCT aw L RNG sta LBa mo /\ incl UNIV (al_U L)
    /\ ALib.Mem.mem_inv asegs (ms_mem ms)
    /\ stk asegs (ms_mem ms) lo (bv_unsigned (AP.getr R 2)) /\ ATOP + 4096 <= lo /\ lo <= bv_unsigned (AP.getr R 2) - 4608
    /\ AP.getr R 4 = Z_to_bv 64 ATP /\ AP.getr R 10 = Z_to_bv 64 16 /\ AP.getr R 11 = Z_to_bv 64 n
    /\ F_aalloc1.F_aalloc1_16.is_primary16 n = true /\ n mod 16 = 0 /\ 16 <= n <= 4096
    /\ (1048576 <= bv_unsigned aw /\ (prim_decided (s_facts st) (getr st X11) = true \/ n <= bv_unsigned aw))
    /\ (exists tr, aunw (ms_mem ms) L RNG lo F_aaligned_iseg.AALIGNED_PC (AP.getr R 2) (AP.getr R 8) (AP.getr R 1) tr)
    /\ bv_unsigned (AP.getr R 8) <> bv_unsigned (AP.getr R 2) + 8 /\ 4096 <= bv_unsigned (AP.getr R 1)
    /\ bv_unsigned (AP.getr R 1) <> F_aaligned_iseg.AALIGNED_PC
    /\ bv_unsigned (AP.getr R 2) mod 16 = 0 /\ rng RNG lo (bv_unsigned (AP.getr R 2) - lo)
    /\ acall_facts X11 E st ms mo L RNG sta LBa aw n
    /\ ~ prist_in E st.
Proof.
  intros st sts E ms mo HS HPC Happ R lo.
  destruct (aaligned_apply_inv st sts Happ) as (r & tp & hargs & cred & st1 & al & CP & TP & FO & HAc & X10E & AL16 & ASZ & TPE & SR & SFO & UO & SPT & RO & NC & PRA & TI & FS & _).
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.

  unfold twins_intact in TI. destruct (aheap_windows st) as [[h wnl]|] eqn:HW; [|discriminate]. clear TI.
  destruct (aheap_call_facts E st ms mo h wnl HS HW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (aw_realW_AHEAP AI ACCT UNIV _ _ _ _ _ ARW) as (AH & AC & HU).
  set (L := w_L W) in *. set (RNG := w_RNG W) in *. set (sta := w_st W) in *. set (LBa := w_LBa W) in *.
  rewrite FO in Hf. injection Hf as <-. rewrite Eh, heap_A_eq in HAc. injection HAc as <-.

  destruct (CallA.stack_sound_g asegs OPS E st ms mo AMALLOC_ROOM HS ltac:(vm_compute; reflexivity) SR)
    as (k & off & rs & ksp & HX2 & Hr & K0 & Hksp & K16 & A16 & Esp & LO0 & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.sp_floor_sound asegs OPS E st ms mo hargs n md A nw rest k off rs HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K _]|[K _]]]; [exact C| unfold K_BLOCK, K_STACK in K; lia| unfold K_SUB, K_STACK in K; lia]. }

  destruct (CallA.acall_regs asegs OPS E st ms mo r tp HS CP TP TPE) as (RV & RA & RR & TP4). fold R in RA, TP4.

  unfold aligned_size_ok in ASZ. destruct (getr st X11) as [nw0| | | | | | | | | |] eqn:X11E; try discriminate ASZ.
  apply andb_prop in ASZ as [ASZ M16]. apply andb_prop in ASZ as [ASZ NHI]. apply andb_prop in ASZ as [NWT NLO]. apply negb_true_iff in NWT.
  apply Uint63.leb_spec in NLO. apply Uint63.leb_spec in NHI. change (to_Z 16%uint63) with 16 in NLO. change (to_Z ALIGNED_NMAX) with 4096 in NHI.
  apply Uint63.eqb_correct in M16.
  assert (M16Z : to_Z (wl nw0) mod 16 = 0).
  { pose proof (ValP.land_mk (wl nw0) 4%uint63 ltac:(change (to_Z 4%uint63) with 4; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 4) 1)%uint63 with 15%uint63 in LM. rewrite M16 in LM. change (to_Z 0%uint63) with 0 in LM. change (2 ^ to_Z 4%uint63) with 16 in LM. lia. }
  assert (DNW : bv_unsigned (den E (VL nw0)) = to_Z (wl nw0)) by (cbn [den]; rewrite wbv_unsigned; exact (w2Z_nowt nw0 NWT)).
  assert (NCR : 1048576 <= bv_unsigned (den E A) /\ (prim_decided (s_facts st) (VL nw0) = true \/ to_Z (wl nw0) <= bv_unsigned (den E A))).
  { unfold cred_pre in NC. apply andb_prop in NC as [NCX NC].
    pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF NCX) as LX. replace (bv_unsigned (den E (VL C_EXHw))) with 1048576 in LX by (vm_compute; reflexivity).
    split; [exact LX|]. apply orb_prop in NC as [NC|NC]; [left; exact NC| right]. pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF NC) as Y. rewrite DNW in Y. exact Y. }
  pose proof (GlueA.getr_RA asegs OPS E st ms mo HS) as GR.
  assert (SP2 : bv_unsigned (AP.getr R 2) = bv_unsigned (ev E k) + keyZ ksp).
  { unfold R. rewrite <- HeapCtr.reg_of_X2, (GR X2). exact Esp. }
  assert (SP47 : bv_unsigned (AP.getr R 2) < 2 ^ 47).
  { unfold sp_top_ok in SPT. pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF SPT) as X. unfold R. rewrite <- HeapCtr.reg_of_X2, (GR X2).
    replace (bv_unsigned (den E (VL SP_TOPw))) with (2 ^ 47) in X by (vm_compute; reflexivity). exact X. }
  assert (RA1 : bv_unsigned (AP.getr R 1) = to_Z r) by (rewrite RA; apply Z_to_bv_small; unfold bv_modulus; lia).
  unfold ret_ok in RO. apply andb_prop in RO as [R4096 RNE]. apply Uint63.leb_spec in R4096. change (to_Z 4096%uint63) with 4096 in R4096.
  apply negb_true_iff in RNE. apply Z.eqb_neq in RNE.
  pose proof (ACCT_rng _ _ _ _ _ _ AC) as RSTK. pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _). pose proof atop_range as AR.
  set (sp := bv_unsigned (AP.getr R 2)) in *.
  destruct (sp_lo_spec E st ms mo k off rs hargs n md A nw rest LB HS SPR FO Hn Eh WF ltac:(lia) ltac:(pose proof (Uint63.to_Z_bounded AMALLOC_ROOM); lia)) as [[LOB LOLE] STKlo]. fold lo in LOB, LOLE, STKlo.
  assert (ASTK : to_Z AMALLOC_ROOM = 12288) by reflexivity.
  exists L, RNG, sta, LBa, (den E A), (to_Z (wl nw0)).
  split. { rewrite <- HPC. exact (GlueA.ms_formA asegs OPS E st ms mo HS RV). }
  split; [exact AH|]. split; [exact AC|]. split; [exact HU|].
  split. { intros a b Hm. unfold ALib.Mem.ro_addr. destruct (find_segment asegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
           rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity. }
  split. { rewrite SP2. apply (stk_merge asegs _ lo (bv_unsigned (ev E k) + loZ rs)); [exact STKlo| exact STK| lia]. }
  split; [exact LOB|]. split; [lia|].
  split; [rewrite TP4, ATPi_eq; reflexivity|].
  split. { unfold R. rewrite <- HeapCtr.reg_of_X10, (GR X10), X10E. apply (proj1 (weqb_ok _ _)) in AL16. subst al. rewrite HeapCtr.den_wlit. reflexivity. }
  split. { unfold R. rewrite <- HeapCtr.reg_of_X11, (GR X11), X11E. rewrite <- (Z_to_bv_bv_unsigned (den E (VL nw0))), DNW. reflexivity. }
  split. { unfold F_aalloc1.F_aalloc1_16.is_primary16, F_aalloc1.F_aalloc1_16.needed16, F_aalloc1.F_aalloc1_16.rounded_size16, rup, K_MAX_SIZE. apply Z.leb_le.
           pose proof (APrimFacts.rz_size_range (to_Z (wl nw0))) as [[RZ1 RZ2] _]. rewrite Z.max_l by lia. Z.div_mod_to_equations. lia. }
  split; [exact M16Z|].
  split; [lia|]. split; [exact NCR|].
  destruct (aunw_chain E st ms mo hargs n md A nw rest k off rs W L RNG sta LBa F_aaligned_iseg.AALIGNED_PC r lo HS Hn Eh SPR SFO
              ltac:(fold R; fold sp; rewrite SP2; lia) TI AH LB (den E A) WF ARW UO HU SP47 RR LOB ltac:(eapply rng_sub'; [exact RSTK|]; lia)) as [AUNW S0NE].
  split. { rewrite RA. exact AUNW. }
  split; [exact S0NE|]. split; [lia|]. split; [rewrite RA1; exact RNE|].
  split. { fold sp. rewrite SP2. rewrite Z.add_mod, A16, K16 by lia. reflexivity. }
  split; [eapply rng_sub'; [exact RSTK|]; lia|].
  split; [| exact (prist_absent_not_in E st _ HF FO PRA)].
  exists LB, r, hargs, st1, k, off, rs, ksp, wnl, n, md, A, nw, rest.
  split; [exact CP|]. split; [exact FS|]. split; [exact SPR|]. split; [exact Hksp|]. split; [exact SP2|]. split; [exact K16|].
  split; [lia|]. split; [lia|]. split; [exact FO|]. split; [exact Hc|]. split; [exact Eh|]. split; [exact T|]. split; [exact N|].
  split; [exact Ln|]. split; [exact N255|]. split; [exact NW|]. split; [exact JU|]. split; [exact WF|]. split; [exact HC|].
  split; [reflexivity|]. split; [exists W; split; [apply wit_of_refl| split; [exact ARW| exact TI]]|].
  split; [rewrite X11E; exact DNW| intros _; exists nw0; exact X11E].
Qed.

Lemma acall_pre_inv : forall room unw st r hargs wnl st1, acall_pre room unw st = Some (r, hargs, wnl, st1) ->
  exists tp, call_pre st = Some r /\ getr st X4 = VL tp /\ aheap_windows st = Some (hargs, wnl)
    /\ weqb tp (wlit ATPi) = true /\ stack_room_g st room = true /\ sp_floor_ok st hargs = true /\ sp_top_ok st = true
    /\ match unw with Some (U, PCz) => unw_ok U PCz r st hargs = true /\ ret_ok PCz r = true | None => True end
    /\ forget_stack_below_sp_g st = Some st1.
Proof.
  intros room unw st r hargs wnl st1 H. unfold acall_pre in H.
  destruct (call_pre st) as [r0|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |] eqn:TP; try discriminate.
  destruct (aheap_windows st) as [[h w]|] eqn:HW; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  destruct (forget_stack_below_sp_g st) as [s1|] eqn:FS; [|discriminate]. injection H as -> -> -> ->.
  do 4 (apply andb_prop in CK as [CK ?]).
  exists tp. repeat (split; [reflexivity || assumption|]). split; [| reflexivity].
  destruct unw as [[U PCz]|]; [| exact I]. match goal with X : (if _ then _ else false) = true |- _ => apply andb_prop in X as [? ?] end. auto.
Qed.

Lemma acall_pre_nt_inv : forall room unw st r hargs wnl st1, acall_pre_nt room unw st = Some (r, hargs, wnl, st1) ->
  exists tp, call_pre st = Some r /\ getr st X4 = VL tp /\ aheap_windows_nt st = Some (hargs, wnl)
    /\ weqb tp (wlit ATPi) = true /\ stack_room_g st room = true /\ sp_floor_ok st hargs = true /\ sp_top_ok st = true
    /\ match unw with Some (U, PCz) => unw_ok U PCz r st hargs = true /\ ret_ok PCz r = true | None => True end
    /\ forget_stack_below_sp_g st = Some st1.
Proof.
  intros room unw st r hargs wnl st1 H. unfold acall_pre_nt in H.
  destruct (call_pre st) as [r0|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |] eqn:TP; try discriminate.
  destruct (aheap_windows_nt st) as [[h w]|] eqn:HW; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  destruct (forget_stack_below_sp_g st) as [s1|] eqn:FS; [|discriminate]. injection H as -> -> -> ->.
  do 4 (apply andb_prop in CK as [CK ?]).
  exists tp. repeat (split; [reflexivity || assumption|]). split; [| reflexivity].
  destruct unw as [[U PCz]|]; [| exact I]. match goal with X : (if _ then _ else false) = true |- _ => apply andb_prop in X as [? ?] end. auto.
Qed.
Lemma aheap_windows_nt_of : forall st x, aheap_windows st = Some x -> aheap_windows_nt st = Some x.
Proof.
  intros st x H. unfold aheap_windows in H. unfold aheap_windows_nt.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|]; [|discriminate].
  destruct (CtrA.count_op HEAP_ID (s_ops st)) as [|[|c]]; try discriminate.
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|]; [|discriminate].
  destruct (heap_nwin hargs) as [n|]; [|discriminate].
  destruct hargs as [|h0 [|h1 [|h2 rest]]]; try discriminate.
  destruct (Nat.leb n 255 && stack_window_ok_g n rest (rg_lo r1)); [|discriminate].
  destruct (CtrA.nonstack_windows n rest) as [wl|]; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Q; [|discriminate] end.
  apply andb_prop in Q as [Q AJ]. apply andb_prop in Q as [WA TS]. rewrite WA, AJ. exact H.
Qed.
Lemma acall_pre_nt_of : forall room unw st x, acall_pre room unw st = Some x -> acall_pre_nt room unw st = Some x.
Proof.
  intros room unw st x H. unfold acall_pre in H. unfold acall_pre_nt.
  destruct (call_pre st) as [r0|]; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |]; try discriminate.
  destruct (aheap_windows st) as [[h w]|] eqn:HW; [|discriminate].
  rewrite (aheap_windows_nt_of st _ HW). exact H.
Qed.

Definition acallG (E : env) (st : sstate) (ms : machine_state) (mo : Model) (r : int) (hargs : list sv) (wnl : list (int * sv * w64))
    (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) : Prop :=
  exists (LB : blocks) (ks : int) (offs : w64) (rss : region) (ksp : int) (nn : nat) (md : w64) (A : sv) (nw : w64) (rest : list sv),
    sp_region st = Some (ks, offs, rss) /\ okey offs = Some ksp
    /\ bv_unsigned (AP.getr (ms_regs ms) 2%bv) = bv_unsigned (ev E ks) + keyZ ksp
    /\ keyZ ksp mod 16 = 0 /\ loZ rss <= keyZ ksp /\ ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss
    /\ find_op HEAP_ID (s_ops st) = Some hargs /\ CtrA.count_op HEAP_ID (s_ops st) = 1%nat
    /\ hargs = VL md :: A :: VL nw :: rest /\ wt nw = false /\ nn = Z.to_nat (to_Z (wl nw)) /\ (3 * nn <= length rest)%nat /\ (nn <= 255)%nat
    /\ CtrA.nonstack_windows nn rest = Some wnl /\ CtrA.windows_anchored (s_regs st) wnl = true /\ aregions_justified st wnl = true
    /\ twins_scan (s_facts st) (s_regs st) wnl wnl = true
    /\ windows_wf (wins_of E nn rest) LB (ATOP + 4096)
    /\ cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) (ms_mem ms)
    /\ aw = den E A
    /\ exists W, wit_of W L RNG sta LBa /\ aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W /\ ties W (wins_of E nn rest).

Lemma acall_pre_facts0 : forall room unw st r hargs wnl st1 E ms mo,
  st_ok asegs OPS E st ms mo -> 4096 <= to_Z room < 2 ^ 32 ->
  acall_pre room unw st = Some (r, hargs, wnl, st1) ->
  let R := ms_regs ms in
  let lo := sp_lo E st in
  exists (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
    ms = MS R (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None (ms_mem ms) (seg_rom asegs)
    /\ AHEAP AI L RNG sta LBa (ms_mem ms) /\ ACCT aw L RNG sta LBa mo /\ incl UNIV (al_U L)
    /\ ALib.Mem.mem_inv asegs (ms_mem ms)
    /\ stk asegs (ms_mem ms) lo (bv_unsigned (AP.getr R 2)) /\ ATOP + 4096 <= lo /\ lo <= bv_unsigned (AP.getr R 2) - 4096
    /\ lo <= bv_unsigned (AP.getr R 2) - to_Z room
    /\ AP.getr R 4 = Z_to_bv 64 ATP
    /\ AP.getr R 1 = Z_to_bv 64 (to_Z r) /\ 0 <= to_Z r < 2 ^ 62
    /\ bv_unsigned (AP.getr R 2) < 2 ^ 47
    /\ bv_unsigned (AP.getr R 2) mod 16 = 0 /\ rng RNG lo (bv_unsigned (AP.getr R 2) - lo)
    /\ call_pre st = Some r /\ forget_stack_below_sp_g st = Some st1
    /\ acallG E st ms mo r hargs wnl L RNG sta LBa aw.
Proof.
  intros room unw st r hargs wnl st1 E ms mo HS ROOM Hpre R lo.
  destruct (acall_pre_inv room _ st r hargs wnl st1 Hpre) as (tp & CP & TP & HW & TPE & SR & SFO & SPT & _ & FS).
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (aheap_call_facts E st ms mo hargs wnl HS HW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (aw_realW_AHEAP AI ACCT UNIV _ _ _ _ _ ARW) as (AH & AC & HU).
  set (L := w_L W) in *. set (RNG := w_RNG W) in *. set (sta := w_st W) in *. set (LBa := w_LBa W) in *.
  destruct (CallA.stack_sound_g asegs OPS E st ms mo room HS ltac:(lia) SR)
    as (k & off & rs & ksp & HX2 & Hr & K0 & Hksp & K16 & A16 & Esp & LO0 & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.sp_floor_sound asegs OPS E st ms mo hargs n md A nw rest k off rs HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K _]|[K _]]]; [exact C| unfold K_BLOCK, K_STACK in K; lia| unfold K_SUB, K_STACK in K; lia]. }
  destruct (CallA.acall_regs asegs OPS E st ms mo r tp HS CP TP TPE) as (RV & RA & RR & TP4). fold R in RA, TP4.
  pose proof (GlueA.getr_RA asegs OPS E st ms mo HS) as GR.
  assert (SP2 : bv_unsigned (AP.getr R 2) = bv_unsigned (ev E k) + keyZ ksp).
  { unfold R. rewrite <- HeapCtr.reg_of_X2, (GR X2). exact Esp. }
  assert (SP47 : bv_unsigned (AP.getr R 2) < 2 ^ 47).
  { unfold sp_top_ok in SPT. pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF SPT) as X. unfold R. rewrite <- HeapCtr.reg_of_X2, (GR X2).
    replace (bv_unsigned (den E (VL SP_TOPw))) with (2 ^ 47) in X by (vm_compute; reflexivity). exact X. }
  pose proof (ACCT_rng _ _ _ _ _ _ AC) as RSTK. pose proof atop_range as ATR.
  set (sp := bv_unsigned (AP.getr R 2)) in *.
  destruct (sp_lo_spec E st ms mo k off rs hargs n md A nw rest LB HS SPR Hf Hn Eh WF ltac:(lia) ltac:(lia)) as [[LOB LOLE] STKlo]. fold lo in LOB, LOLE, STKlo.
  exists L, RNG, sta, LBa, (den E A).
  split. { exact (GlueA.ms_formA asegs OPS E st ms mo HS RV). }
  split; [exact AH|]. split; [exact AC|]. split; [exact HU|].
  split. { intros a b Hm. unfold ALib.Mem.ro_addr. destruct (find_segment asegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
           rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity. }
  split. { rewrite SP2. apply (stk_merge asegs _ lo (bv_unsigned (ev E k) + loZ rs)); [exact STKlo| exact STK| lia]. }
  split; [exact LOB|]. split; [lia|]. split; [lia|].
  split; [rewrite TP4, ATPi_eq; reflexivity|].
  split; [exact RA|]. split; [exact RR|]. split; [exact SP47|].
  split. { fold sp. rewrite SP2. rewrite Z.add_mod, A16, K16 by lia. reflexivity. }
  split; [eapply rng_sub'; [exact RSTK|]; lia|].
  split; [exact CP|]. split; [exact FS|].
  exists LB, k, off, rs, ksp, n, md, A, nw, rest.
  split; [exact SPR|]. split; [exact Hksp|]. split; [exact SP2|]. split; [exact K16|]. split; [lia|]. split; [lia|].
  split; [exact Hf|]. split; [exact Hc|]. split; [exact Eh|]. split; [exact T|]. split; [exact N|]. split; [exact Ln|]. split; [exact N255|].
  split; [exact NW|]. split; [exact AN|]. split; [exact JU|].
  split. { destruct (CallA.aheap_windows_inv st hargs wnl HW) as (_ & _ & r1' & n' & md2 & A2 & nw2 & rest2 & _ & _ & Eh2 & _ & N2 & _ & _ & _ & NW2 & _ & _ & TS).
           exact TS. }
  split; [exact WF|]. split; [exact HC|]. split; [reflexivity|].
  exists W. split; [apply wit_of_refl| split; [exact ARW| exact TI]].
Qed.

Lemma acall_sp_altop : forall E st ms mo r hargs wnl L RNG sta LBa aw,
  st_ok asegs OPS E st ms mo -> acallG E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> bv_unsigned (AP.getr (ms_regs ms) 2%bv) < 2 ^ 47 ->
  sp_floor_ok st hargs = true -> sp_altop_ok st hargs = true ->
  bv_unsigned (AP.getr (ms_regs ms) 2%bv) <= al_top L.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw HS G AH SP47 SFO SAO.
  destruct G as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                 & NW & AN & AJ & TS & WF & CW & EA & W & WOF & ARW & TI).
  assert (Hn : heap_nwin hargs = Some nn).
  { rewrite Eh. unfold heap_nwin. rewrite Tnw, <- Nn. destruct (Nat.leb_spec (3 * nn) (length rest)); [reflexivity| lia]. }
  destruct (CallA.sp_altop_sound asegs OPS E st ms mo hargs nn md A nw rest HS SAO Hn Eh) as (wlo & len & SK & INw & D).
  pose proof (CallA.sp_floor_key asegs OPS E st ms mo hargs nn md A nw rest ks offs rss wlo HS SFO Hn Eh SPR SK) as FL.
  assert (SP2 : bv_unsigned (den E (getr st X2)) = bv_unsigned (AP.getr (ms_regs ms) 2%bv)).
  { rewrite <- HeapCtr.reg_of_X2, (GlueA.getr_RA asegs OPS E st ms mo HS X2). reflexivity. }
  rewrite SP2 in D.
  apply (stk0_sp_bound AI W (wins_of E nn rest) _ L RNG sta LBa (ms_mem ms) _ TI INw); [reflexivity| | exact AH| exact D].
  cbn [w_lo]. unfold ZC_BASE. lia.
Qed.

Lemma acall_pre_room : forall room unw st r hargs wnl st1 E ms mo,
  st_ok asegs OPS E st ms mo -> 4096 <= to_Z room < 2 ^ 32 ->
  acall_pre room unw st = Some (r, hargs, wnl, st1) ->
  sp_lo E st <= bv_unsigned (AP.getr (ms_regs ms) 2) - to_Z room.
Proof.
  intros room unw st r hargs wnl st1 E ms mo HS ROOM Hpre.
  destruct (acall_pre_facts0 room unw st r hargs wnl st1 E ms mo HS ROOM Hpre) as (L & RNG & sta & LBa & aw & _ & _ & _ & _ & _ & _ & _ & _ & LOR & _).
  exact LOR.
Qed.

Lemma acall_pre_facts : forall room PCz st r hargs wnl st1 E ms mo,
  st_ok asegs OPS E st ms mo -> 4096 <= to_Z room < 2 ^ 32 ->
  acall_pre room (Some (UNIV, PCz)) st = Some (r, hargs, wnl, st1) ->
  let R := ms_regs ms in
  let lo := sp_lo E st in
  exists (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
    ms = MS R (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None (ms_mem ms) (seg_rom asegs)
    /\ AHEAP AI L RNG sta LBa (ms_mem ms) /\ ACCT aw L RNG sta LBa mo
    /\ ALib.Mem.mem_inv asegs (ms_mem ms)
    /\ stk asegs (ms_mem ms) lo (bv_unsigned (AP.getr R 2)) /\ ATOP + 4096 <= lo /\ lo <= bv_unsigned (AP.getr R 2) - 4096
    /\ AP.getr R 4 = Z_to_bv 64 ATP
    /\ (exists tr, aunw (ms_mem ms) L RNG lo PCz (AP.getr R 2) (AP.getr R 8) (AP.getr R 1) tr)
    /\ bv_unsigned (AP.getr R 8) <> bv_unsigned (AP.getr R 2) + 8 /\ 4096 <= bv_unsigned (AP.getr R 1)
    /\ bv_unsigned (AP.getr R 1) <> PCz
    /\ bv_unsigned (AP.getr R 2) mod 16 = 0 /\ rng RNG lo (bv_unsigned (AP.getr R 2) - lo)
    /\ call_pre st = Some r /\ forget_stack_below_sp_g st = Some st1
    /\ acallG E st ms mo r hargs wnl L RNG sta LBa aw.
Proof.
  intros room PCz st r hargs wnl st1 E ms mo HS ROOM Hpre R lo.
  destruct (acall_pre_inv room _ st r hargs wnl st1 Hpre) as (tp & _ & _ & _ & _ & _ & SFO & _ & (UO & RO) & _).
  destruct (acall_pre_facts0 room _ st r hargs wnl st1 E ms mo HS ROOM Hpre)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & HU & MI & ST & BOT & LO & _ & TP & RA & RR & SP47 & SP16 & RSTKlo & CP & FS & CF).
  fold R in Ems, ST, LO, TP, RA, SP47, SP16, RSTKlo. fold lo in ST, BOT, LO, RSTKlo.
  assert (RA1 : bv_unsigned (AP.getr R 1) = to_Z r) by (rewrite RA; apply Z_to_bv_small; unfold bv_modulus; lia).
  unfold ret_ok in RO. apply andb_prop in RO as [R4096 RNE]. apply Uint63.leb_spec in R4096. change (to_Z 4096%uint63) with 4096 in R4096.
  apply negb_true_iff in RNE. apply Z.eqb_neq in RNE.
  pose proof (ACCT_rng _ _ _ _ _ _ AC) as RSTK. pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _).
  exists L, RNG, sta, LBa, aw.
  split; [exact Ems|]. split; [exact AH|]. split; [exact AC|]. split; [exact MI|]. split; [exact ST|]. split; [exact BOT|]. split; [exact LO|].
  split; [exact TP|].
  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & CW & EA & W & WOF & ARW & TI).
  assert (Hn : heap_nwin hargs = Some nn).
  { rewrite Eh. unfold heap_nwin. rewrite Tnw, <- Nn. destruct (Nat.leb_spec (3 * nn) (length rest)); [reflexivity| lia]. }
  destruct (aunw_chain E st ms mo hargs nn md A nw rest ks offs rss W L RNG sta LBa PCz r lo HS Hn Eh SPR SFO
              ltac:(unfold R in *; rewrite SPE; lia) TI AH LB aw WF ltac:(rewrite EA in *; exact ARW) UO HU SP47 RR BOT ltac:(eapply rng_sub'; [exact RSTK|]; lia)) as [AUNW S0NE].
  split. { rewrite RA. exact AUNW. }
  split; [exact S0NE|]. split; [lia|]. split; [rewrite RA1; exact RNE|].
  split; [exact SP16|]. split; [exact RSTKlo|]. split; [exact CP|]. split; [exact FS| exact CF].
Qed.

Lemma wins_of_length : forall E n ws, (length (wins_of E n ws) <= n)%nat.
Proof. intros E n. induction n as [|n IH]; intros ws; [cbn; lia|]. destruct ws as [|lo [|len [|kd ws]]]; cbn; try lia. specialize (IH ws). lia. Qed.

Lemma c24_of_ties : forall E W L RNG sta LBa aw LB m mo nn rest,
  wit_of W L RNG sta LBa -> aw_realW AI ACCT UNIV aw LB m mo W -> ties W (wins_of E nn rest) -> (nn <= 255)%nat -> C24.c24count LBa <= 255.
Proof.
  intros E W L RNG sta LBa aw LB m mo nn rest (_ & _ & _ & <-) [HW _] TI N.
  pose proof (C24.c24count_le_windows AI ACCT UNIV W aw LB m mo _ HW TI). pose proof (wins_of_length E nn rest). lia.
Qed.

Lemma acall_facts_c24 : forall XN E st ms mo L RNG sta LBa aw n, acall_facts XN E st ms mo L RNG sta LBa aw n ->
  C24.c24count LBa <= 255 /\ bv_unsigned (den E (getr st XN)) = n.
Proof.
  intros XN E st ms mo L RNG sta LBa aw n (LB & r & hargs & st1 & ks & offs & rss & ksp & wnl & nn & md & A & nw & rest
    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N255 & _ & _ & _ & _ & _ & (W & WOF & AR & TI) & NDEN & _).
  split; [exact (c24_of_ties E W L RNG sta LBa aw LB _ mo nn rest WOF AR TI N255)| exact NDEN].
Qed.

Lemma acallG_c24 : forall E st ms mo r hargs wnl L RNG sta LBa aw, acallG E st ms mo r hargs wnl L RNG sta LBa aw -> C24.c24count LBa <= 255.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw (LB & ks & offs & rss & ksp & nn & md & A & nw & rest
    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N255 & _ & _ & _ & _ & _ & _ & _ & (W & WOF & AR & TI)).
  exact (c24_of_ties E W L RNG sta LBa aw LB _ mo nn rest WOF AR TI N255).
Qed.

End Pre.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import CtrFX.

Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Unset Nia Cache. Unset Nra Cache.

Lemma shad_img_band : forall a', 0 <= a' < AIMG_HI -> 0x7fff8000 <= shad a' < 0x800be200.
Proof. intros a' H. unfold shad, ASHOFF, AIMG_HI in *. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. Qed.

Section Pre.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.

Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).

Lemma zlist_eqb_eq : forall a b, zlist_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. apply IH. exact H2.
Qed.
Lemma univ_ok_in : forall PCz r, univ_ok UNIV PCz r = true -> In [PCz; to_Z r] UNIV /\ In [PCz] UNIV.
Proof.
  intros PCz r H. unfold univ_ok in H. apply andb_prop in H as [H1 H2].
  apply existsb_exists in H1 as (l1 & I1 & E1). apply existsb_exists in H2 as (l2 & I2 & E2).
  apply zlist_eqb_eq in E1. apply zlist_eqb_eq in E2. subst l1 l2. split; assumption.
Qed.

Lemma aunw_stop : forall (L : alayout) RNG (m : amem) lo PCz (sp s0 : word) r,
  incl UNIV (al_U L) -> univ_ok UNIV PCz r = true ->
  bv_unsigned s0 <= bv_unsigned sp -> bv_unsigned sp < 2^47 -> 0 <= to_Z r < 2^62 ->
  ATOP + 4096 <= lo ->
  rng RNG (ATOP + 4096) (al_top L - (ATOP + 4096)) ->
  aunw m L RNG lo PCz sp s0 (Z_to_bv 64 (to_Z r)) [].
Proof.
  intros L RNG m lo PCz sp s0 r HU UO S0 SP47 RR LO RSTK.
  destruct (univ_ok_in PCz r UO) as [I2 I1]. unfold aunw.
  destruct (Z_lt_le_dec (bv_unsigned sp + 16) (al_top L)) as [LT|GE].
  - left. split; [exact LT|]. split; [apply uc_stop; intros (X & _); lia|]. split; [cbn; lia|]. split.
    + apply HU. rewrite Z_to_bv_small by (unfold bv_modulus; lia). exact I2.
    + destruct (Z_le_gt_dec lo (al_top L)) as [LE|GT].
      * eapply rng_sub'; [exact RSTK|]. lia.
      *   destruct RSTK as (A & B & H). split; [lia|]. split; [lia|]. intros b j Hb Hj. lia.
  - right. split; [exact GE|]. split; [exact SP47|]. apply HU. exact I1.
Qed.

Lemma unw_ok_inv : forall PCz r st hargs nn md A nw rest, unw_ok UNIV PCz r st hargs = true ->
  heap_nwin hargs = Some nn -> hargs = VL md :: A :: VL nw :: rest ->
  exists wl, CtrA.nonstack_windows nn rest = Some wl /\ In [PCz] UNIV /\ s0_far st wl = true
  /\ exists cands, unw_walk 32%nat st hargs wl PCz (getr st X2) (getr st X8) 28%nat = Some cands
       /\ forall tr, In tr cands -> (length tr <= 28)%nat /\ In (PCz :: to_Z r :: tr) UNIV.
Proof.
  intros PCz r st hargs nn md A nw rest H Hn Eh. unfold unw_ok in H. rewrite Hn in H. rewrite Eh in H. rewrite <- Eh in H.
  destruct (CtrA.nonstack_windows nn rest) as [wl|]; [|discriminate H]. exists wl. split; [reflexivity|].
  apply andb_prop in H as [H W]. apply andb_prop in H as [U1 SF].
  apply existsb_exists in U1 as (l1 & I1 & E1). apply zlist_eqb_eq in E1. subst l1.
  split; [exact I1|]. split; [exact SF|].
  destruct (unw_walk 32%nat st hargs wl PCz (getr st X2) (getr st X8) 28%nat) as [cands|]; [|discriminate W].
  exists cands. split; [reflexivity|]. intros tr Htr. pose proof (proj1 (forallb_forall _ _) W tr Htr) as X.
  apply andb_prop in X as [X1 X2]. apply Nat.leb_le in X1. apply existsb_exists in X2 as (l2 & I2 & E2). apply zlist_eqb_eq in E2. subst l2. auto.
Qed.

Lemma below_stack_w_sound : forall E st ms mo nn rest wl LB W aw k off,
  st_ok bsegs OPS E st ms mo -> CtrA.nonstack_windows nn rest = Some wl ->
  windows_wf (wins_of E nn rest) LB (ATOP + 4096) -> aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W ->
  below_stack_w (s_facts st) wl k off = true -> bv_unsigned (den E (VP k off)) <= ATOP.
Proof.
  intros E st ms mo nn rest wl LB W aw k off HS NW WF [HWW _] H. unfold below_stack_w in H.
  destruct (CtrA.win_lookup wl k) as [[len kd]|] eqn:WL; [|discriminate H].
  apply andb_prop in H as [WT LT]. apply negb_true_iff in WT.

  assert (L : w2Z off < bv_unsigned (den E len) \/ (0 < w2Z off /\ w2Z off <= bv_unsigned (den E len))).
  { destruct (KnownT.KnownT.known_ltu_t (s_facts st) (VL off) len) eqn:K1.
    - left. pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) K1) as L. cbn [den] in L. rewrite wbv_unsigned in L. exact L.
    - right. destruct (weqb off wzero) eqn:WZ; [discriminate LT|]. cbn [negb] in LT.
      pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) LT) as L. cbn [den] in L. rewrite wbv_unsigned in L.
      assert (NZ : w2Z off <> 0).
      { intros Z0. assert (off = wzero) by (apply w2Z_inj; rewrite Z0, wzero_ok; reflexivity). subst off. rewrite weqb_refl in WZ. discriminate WZ. }
      pose proof (w2Z_range off). lia. }
  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wl k len kd NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & KDS). cbn [w_lo w_len w_kind] in W1, W2, W3, KDS.
  pose proof (w2Z_range off) as RO. unfold two64 in *.
  assert (EW : w2Zs off = w2Z off) by (rewrite ValP.w2Zs_eq, WT; lia).

  set (a := bv_unsigned (ev E k) + w2Z off - (if Z_lt_dec (w2Z off) (bv_unsigned (den E len)) then 0 else 1)).
  assert (AR1 : bv_unsigned (ev E k) + w2Z off <= a + 1) by (unfold a; destruct (Z_lt_dec _ _); lia).
  assert (IU : in_user LB a).
  { assert (AIN : bv_unsigned (ev E k) <= a < bv_unsigned (ev E k) + bv_unsigned (den E len)) by (unfold a; destruct (Z_lt_dec _ _); lia).
    destruct KDS as [[K0 _]|[[KB B]|[KS (b & Hb & SUB)]]]; unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
    - exfalso. unfold K_STACK in K0. lia.
    - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
    - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }
  pose proof atop_range as AR.
  assert (ALT : a < ATOP) by (destruct (LB_band AI ACCT UNIV AI_fake W aw LB (ms_mem ms) mo a HWW IU) as [X|[X|X]]; unfold AIMG_HI, KLS in *; lia).
  assert (ED : bv_unsigned (den E (VP k off)) = bv_unsigned (ev E k) + w2Z off).
  { rewrite ValP.den_VP, EW. apply Z.mod_small. unfold two64. lia. }
  rewrite ED. lia.
Qed.

Lemma alias_d_fact : forall (ea ek : word) (oa ob : w64),
  bv_add ea (wbv oa) = bv_add ek (wbv ob) -> bv_add ea (wbv (wsub oa ob)) = ek.
Proof.
  intros ea ek oa ob H. rewrite ValP.wbv_wsub. apply bv_eq. apply (f_equal bv_unsigned) in H.
  rewrite !bv_add_unsigned, ?bv_sub_unsigned in *.
  pose proof (bv_unsigned_in_range _ ea). pose proof (bv_unsigned_in_range _ ek). pose proof (bv_unsigned_in_range _ (wbv oa)). pose proof (bv_unsigned_in_range _ (wbv ob)).
  unfold bv_wrap, bv_modulus in *. set (M := 2 ^ Z.of_N 64) in *.
  assert (HM : 0 < M) by (subst M; apply Z.pow_pos_nonneg; lia).
  rewrite Zplus_mod_idemp_r.
  replace (bv_unsigned ea + (bv_unsigned (wbv oa) - bv_unsigned (wbv ob))) with ((bv_unsigned ea + bv_unsigned (wbv oa)) - bv_unsigned (wbv ob)) by lia.
  rewrite <- Zminus_mod_idemp_l, H, Zminus_mod_idemp_l.
  replace (bv_unsigned ek + bv_unsigned (wbv ob) - bv_unsigned (wbv ob)) with (bv_unsigned ek) by lia. apply Z.mod_small. lia.
Qed.
Lemma alias_d_den : forall (ek' ek : word) (d off : w64),
  bv_add ek' (wbv d) = ek -> bv_add ek' (wbv (wadd off d)) = bv_add ek (wbv off).
Proof.
  intros ek' ek d off <-. rewrite ValP.wbv_wadd. apply bv_eq. rewrite !bv_add_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma anchor_aliases_sound : forall E fs k k' d, facts_hold E fs -> In (k', d) (anchor_aliases fs k) -> bv_add (ev E k') (wbv d) = ev E k.
Proof.
  intros E fs k k' d HF. induction fs as [|f fs IH]; [intros []|].
  apply Forall_cons_iff in HF as [Hf HF]. specialize (IH HF). cbn [anchor_aliases].
  destruct f as [| | | |a b| | |]; try exact IH.
  destruct a as [|k1 o1| | | | | | | | |]; try exact IH. destruct b as [|k2 o2| | | | | | | | |]; try exact IH.
  cbn [fact_holds den] in Hf.
  destruct (PrimInt63.eqb k2 k) eqn:E2.
  - apply Uint63.eqb_correct in E2. subst k2. intros [EQ|IN]; [| exact (IH IN)].
    injection EQ as <- <-. exact (alias_d_fact _ _ _ _ Hf).
  - destruct (PrimInt63.eqb k1 k) eqn:E1; [|exact IH]. apply Uint63.eqb_correct in E1. subst k1.
    intros [EQ|IN]; [| exact (IH IN)]. injection EQ as <- <-. exact (alias_d_fact _ _ _ _ (eq_sym Hf)).
Qed.
Lemma below_stack_sound : forall E st ms mo nn rest wl LB W aw v,
  st_ok bsegs OPS E st ms mo -> CtrA.nonstack_windows nn rest = Some wl ->
  windows_wf (wins_of E nn rest) LB (ATOP + 4096) -> aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W ->
  below_stack (s_facts st) wl v = true -> bv_unsigned (den E v) <= ATOP.
Proof.
  intros E st ms mo nn rest wl LB W aw v HS NW WF ARW H. unfold below_stack in H.
  destruct v as [|k off| | | | | | | | |]; try discriminate H.
  destruct (below_stack_w (s_facts st) wl k off) eqn:BW.
  { exact (below_stack_w_sound E st ms mo nn rest wl LB W aw k off HS NW WF ARW BW). }
  apply existsb_exists in H as ([k' d] & IN & BW'). cbn [fst snd] in BW'.
  pose proof (anchor_aliases_sound E _ _ _ _ (so_facts _ _ _ _ _ _ HS) IN) as EV.
  pose proof (below_stack_w_sound E st ms mo nn rest wl LB W aw k' (wadd off d) HS NW WF ARW BW') as X.
  cbn [den] in X |- *. rewrite (alias_d_den _ _ d off EV) in X. exact X.
Qed.

Lemma aunw_chain : forall E st ms mo hargs nn md A nw rest ks offs rss W (L : alayout) RNG sta LBa PCz r lo,
  st_ok bsegs OPS E st ms mo ->
  heap_nwin hargs = Some nn -> hargs = VL md :: A :: VL nw :: rest ->
  sp_region st = Some (ks, offs, rss) -> sp_floor_ok st hargs = true ->
  bv_unsigned (ev E ks) + loZ rss <= bv_unsigned (AP.getr (ms_regs ms) 2) ->
  ties W (wins_of E nn rest) -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  forall LB aw, windows_wf (wins_of E nn rest) LB (ATOP + 4096) -> aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W ->
  unw_ok UNIV PCz r st hargs = true -> incl UNIV (al_U L) ->
  bv_unsigned (AP.getr (ms_regs ms) 2) < 2 ^ 47 -> 0 <= to_Z r < 2 ^ 62 -> ATOP + 4096 <= lo ->
  rng RNG (ATOP + 4096) (al_top L - (ATOP + 4096)) ->
  (exists tr, aunw (ms_mem ms) L RNG lo PCz (AP.getr (ms_regs ms) 2) (AP.getr (ms_regs ms) 8) (Z_to_bv 64 (to_Z r)) tr)
  /\ bv_unsigned (AP.getr (ms_regs ms) 8) <> bv_unsigned (AP.getr (ms_regs ms) 2) + 8.
Proof.
  intros E st ms mo hargs nn md A nw rest ks offs rss W L RNG sta LBa PCz r lo HS Hn Eh SPR SFO LOSP TI AH LB aw WF ARW UO HU SP47 RR LO RSTK.
  destruct (unw_ok_inv PCz r st hargs nn md A nw rest UO Hn Eh) as (wl & NWL & I1 & SF & cands & WK & CA).
  pose proof (fun v => below_stack_sound E st ms mo nn rest wl LB W aw v HS NWL WF ARW) as BS0.
  assert (BS : forall v, below_stack (s_facts st) wl v = true -> bv_unsigned (den E v) < ATOP + 1) by (intros v Hv; pose proof (BS0 v Hv); lia).
  pose proof (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS) as GR.
  assert (SP2 : bv_unsigned (den E (getr st X2)) = bv_unsigned (AP.getr (ms_regs ms) 2%bv)) by (rewrite <- HeapCtr.TwinB.reg_of_X2, (GR X2); reflexivity).
  assert (S02 : bv_unsigned (den E (getr st X8)) = bv_unsigned (AP.getr (ms_regs ms) 8%bv)) by (rewrite <- CallA.TwinB.reg_of_X8, (GR X8); reflexivity).
  destruct (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _).
  assert (TOPB : forall wlo x, stack_window_key nn rest = Some wlo -> x - bv_unsigned (den E (VP STACK_ID wlo)) <= SPALT -> x <= al_top L).
  { intros wlo x SK D. destruct (CallA.TwinB.stack_window_key_In E nn rest wlo SK) as (len & INw).
    pose proof (CallA.TwinB.sp_floor_key bsegs OPS E st ms mo hargs nn md A nw rest ks offs rss wlo HS SFO Hn Eh SPR SK) as FL.
    apply (stk0_sp_bound AI W (wins_of E nn rest) _ L RNG sta LBa (ms_mem ms) x TI INw); [reflexivity| | exact AH| exact D].
    cbn [w_lo]. unfold ZC_BASE. lia. }
  pose proof atop_range as ATR0.
  assert (LOWP : ATOP + 1 <= bv_unsigned (den E (getr st X2))).
  { rewrite SP2. destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & KZ & _).
    pose proof (so_reg _ _ _ _ _ _ HS _ _ Hrs) as RO. destruct (ro_range _ _ _ _ _ _ RO KZ) as [RLO _].
    assert (FLw : exists wlo, stack_window_key nn rest = Some wlo).
    { unfold sp_floor_ok in SFO. rewrite Hn, Eh, SPR in SFO. destruct (stack_window_key nn rest) as [wlo|]; [eexists; reflexivity| discriminate SFO]. }
    destruct FLw as [wlo SK]. destruct (CallA.TwinB.stack_window_key_In E nn rest wlo SK) as (len & INw).
    pose proof (CallA.TwinB.sp_floor_key bsegs OPS E st ms mo hargs nn md A nw rest ks offs rss wlo HS SFO Hn Eh SPR SK) as FL.
    pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
    destruct KDs as [[_ C]|[[K _]|[K _]]]; [lia| unfold K_BLOCK, K_STACK in K; lia| unfold K_SUB, K_STACK in K; lia]. }
  destruct (CallU.TwinB.unw_walk_sound OPS E st ms mo hargs nn md A nw rest wl (al_top L) (ATOP + 1) PCz HS Hn Eh TOPB TOP47 BS _ _ _ _ _ LOWP WK) as (tr & Htr & UC).
  rewrite SP2, S02 in UC. destruct (CA tr Htr) as [LEN INU].
  split.
  - exists tr. unfold aunw.
    destruct (Z_lt_le_dec (bv_unsigned (AP.getr (ms_regs ms) 2%bv) + 16) (al_top L)) as [LT|GE].
    + left. split; [exact LT|]. split; [exact UC|]. split; [exact LEN|]. split.
      * apply HU. rewrite Z_to_bv_small by (unfold bv_modulus; lia). exact INU.
      * destruct (Z_le_gt_dec lo (al_top L)) as [LE|GT].
        -- eapply rng_sub'; [exact RSTK|]. lia.
        -- destruct RSTK as (X & Y & H). split; [lia|]. split; [lia|]. intros b j Hb Hj. lia.
    + right. split; [exact GE|]. split; [exact SP47|]. apply HU. exact I1.
  - destruct (CallU.TwinB.s0_far_sound bsegs OPS E st ms mo wl (ATOP + 1) HS SF BS LOWP ltac:(rewrite SP2; exact SP47)) as [X|X]; rewrite SP2, S02 in X; lia.
Qed.

Lemma amalloc_apply_inv : forall st sts, amalloc_apply UNIV AMALLOC_PC st = Some sts ->
  exists r tp hargs cred st1,
    call_pre st = Some r /\ getr st X4 = VL tp /\ find_op HEAP_ID (s_ops st) = Some hargs /\ heap_A hargs = Some cred
    /\ weqb tp (wlit ATPi) = true /\ stack_room_g st AMALLOC_ROOM = true /\ sp_floor_ok st hargs = true
    /\ unw_ok UNIV AMALLOC_PC r st hargs = true /\ sp_top_ok st = true /\ ret_ok AMALLOC_PC r = true
    /\ KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (getr st X10) = true /\ KnownT.KnownT.known_leu_t (s_facts st) (getr st X10) (VL AREQMAXw) = true
    /\ cred_pre (s_facts st) (getr st X10) cred = true
    /\ (if sec_decided (s_facts st) (getr st X10) then true else prist_absent (s_facts st) hargs) = true
    /\ twins_intact st hargs = true
    /\ forget_stack_below_sp_g st = Some st1
    /\ exists stN tl, sts = stN :: tl /\ null_post hargs cred (clobber st1) r = Some stN.
Proof.
  intros st sts H. unfold amalloc_apply in H.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |] eqn:TP; try discriminate.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:FO; [|discriminate].
  destruct (heap_A hargs) as [cred|] eqn:HA; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  do 11 (apply andb_prop in CK as [CK ?]).
  destruct (forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate].
  destruct (null_post hargs cred (clobber st1) r) as [stN|] eqn:NP; [|discriminate].
  destruct (fresh (clobber st1)) as [k st3] eqn:F1. destruct (fresh st3) as [sh st4] eqn:F2.
  destruct (heap_set_A hargs (cred_post (s_facts st) (getr st X10) cred)) as [h1|]; [|discriminate].
  destruct (heap_add_window h1 (VP k wzero) (getr st X10) (VL CtrLib.K_BLOCK)) as [h2|]; [|discriminate].
  destruct (heap_add_window h2 (VP sh wzero) (twin_len (getr st X10)) (VL K_TWIN)) as [h3|]; [|discriminate].
  destruct (fresh st4) as [s2 st4b] eqn:F3.
  injection H as <-.
  exists r, tp, hargs, cred, st1. repeat (split; [first [assumption | reflexivity]|]).
  repeat match goal with |- exists _ _, (if ?c then _ else _) = _ /\ _ => destruct c end; do 2 eexists; (split; [reflexivity| exact NP]).
Qed.

Lemma aheap_call_facts : forall E st ms mo hargs wnl,
  st_ok bsegs OPS E st ms mo -> aheap_windows st = Some (hargs, wnl) ->
  exists r1 n md A nw rest LB,
    IMap.find STACK_ID (s_regs st) = Some r1 /\ find_op HEAP_ID (s_ops st) = Some hargs /\ CtrA.count_op HEAP_ID (s_ops st) = 1%nat
    /\ heap_nwin hargs = Some n /\ hargs = VL md :: A :: VL nw :: rest
    /\ wt nw = false /\ n = Z.to_nat (to_Z (wl nw)) /\ (3 * n <= length rest)%nat /\ (n <= 255)%nat
    /\ stack_window_ok_g n rest (rg_lo r1) = true /\ CtrA.nonstack_windows n rest = Some wnl
    /\ CtrA.windows_anchored (s_regs st) wnl = true /\ aregions_justified st wnl = true
    /\ aw_holds_asan AI ACCT UNIV (den E A) LB (ms_mem ms) mo
    /\ windows_wf (wins_of E n rest) LB (ATOP + 4096)
    /\ cw_holds Cw (w2Z md) (map (den E) (skipn (3 * n) rest)) LB (wins_of E n rest) (ms_mem ms)
    /\ exists W, aw_realW AI ACCT UNIV (den E A) LB (ms_mem ms) mo W /\ ties W (wins_of E n rest).
Proof.
  intros E st ms mo hargs wnl HS HW.
  destruct (CallA.TwinB.aheap_windows_inv st hargs wnl HW) as (Hf & Hc & r1 & n & md & A & nw & rest & Hr1 & Hn & Eh & T & N & L & N255 & SW & NW & AN & JU & TS).
  pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (so_ops _ _ _ _ _ _ HS) Hf) as HH.
  rewrite OPS_holds1 in HH. destruct HH as (md' & aw & ws & ca & LB & W & D & HWw & WF & HC & TI).
  rewrite Eh, (decode_hargs E md A nw rest n T N L) in D. injection D as <- <- <- <-.
  exists r1, n, md, A, nw, rest, LB.
  split; [exact Hr1|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hn|]. split; [exact Eh|]. split; [exact T|]. split; [exact N|].
  split; [exact L|]. split; [exact N255|]. split; [exact SW|]. split; [exact NW|]. split; [exact AN|]. split; [exact JU|].
  split; [exists W; exact HWw|]. split; [exact WF|]. split; [exact HC|].
  exists (set_ms W (ms_mem ms)). split; [| apply ties_set_ms; exact TI].
  apply (aw_holds_real_w AI ACCT UNIV AI_fake W (den E A) LB (ms_mem ms) mo HWw).
  intros b HbT NPRIM g G0 G1. set (A0 := ab_addr b) in *. set (n0 := ab_size b) in *. pose proof atop_range as AR.

  pose proof (proj1 TI b HbT) as WIN. fold A0 n0 in WIN.
  destruct (HeapCtrB.TwinB.wins_cover E n rest wnl _ NW WIN) as [KS|(sh & len & kd & Iw & EW)]; [cbn in KS; unfold K_TWINz, K_STACK in KS; lia|].
  injection EW as E1 E2 E3.
  assert (KD : weqb kd K_TWIN = true) by (apply weqb_w2Z; rewrite <- E3; reflexivity).
  destruct (CallA.TwinB.twins_scan_sound _ _ _ _ sh len kd TS Iw KD) as [OLD|EVA].
  2:{
      exfalso. pose proof (CallA.TwinB.twin_small_sound E _ _ (so_facts _ _ _ _ _ _ HS) EVA) as LW.
      destruct (twin_T_facts AI ACCT UNIV W _ _ _ _ b HWw HbT) as (_ & _ & _ & _ & _ & NR & _). fold n0 in NR.
      unfold shlen in E2. rewrite Z.shiftr_div_pow2 in E2 by lia. change (2 ^ 3) with 8 in E2.
      rewrite (is_primary_le n0) in NPRIM; [discriminate|]. clear - E2 LW NR. Z.div_mod_to_equations. lia. }
  destruct (CallA.TwinB.twin_arm_old_inv _ _ _ _ _ OLD) as (k & r & nsv & BT & FR & WL & LEN & ALT).
  pose proof (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL) as Ik.
  destruct (HeapCtrB.TwinB.nonstack_windows_In E n rest wnl k nsv CtrLib.K_BLOCK NW Ik) as (_ & _ & _ & INk).
  destruct (HeapCtrB.TwinB.nonstack_windows_In E n rest wnl sh len kd NW Iw) as (SH0 & _).

  pose proof (proj1 (Forall_forall _ _) WF _ INk) as (W1 & W2 & W3 & KDs). cbn [w_kind w_lo w_len w_iv] in KDs, W1, W2, W3.
  assert (HB : In (bv_unsigned (ev E k), bv_unsigned (den E nsv)) LB).
  { replace (w2Z CtrLib.K_BLOCK) with 1 in KDs by (vm_compute; reflexivity).
    destruct KDs as [[K _]|[[_ B]|[K _]]]; [unfold K_STACK in K; lia| exact B| unfold K_SUB in K; lia]. }
  pose proof (CallA.TwinB.block_of_twin_sound E _ sh k (so_facts _ _ _ _ _ _ HS) BT) as LK.
  assert (SHEQ : shad (bv_unsigned (ev E k)) = shad A0).
  { rewrite E1. rewrite LK. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. change (bv_modulus 64) with (2 ^ 64) in RK.
    rewrite Z.mod_small; [lia|]. clear - RK. Z.div_mod_to_equations. lia. }
  destruct (twin_owner_w AI ACCT UNIV AI_fake W _ _ _ _ b _ _ HWw HbT HB SHEQ) as (EA & EN & NR). fold A0 n0 in EA, EN, NR.

  assert (SHNZ : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact SH0).
  destruct ALT as [PD|[[TR SS]|[TM [s2 TSC]]]].
  { exfalso. pose proof (CallA.TwinB.prim_decided_sound E _ nsv (so_facts _ _ _ _ _ _ HS) PD) as LE64. rewrite EN in LE64.
    rewrite (is_primary_le n0 ltac:(lia)) in NPRIM. discriminate. }
  2:{
      pose proof (CallA.TwinB.twin_pair_sound bsegs (s_priv st) E (ms_mem ms) (s_facts st) (s_regs st) sh r nsv s2 (so_facts _ _ _ _ _ _ HS)
                    (so_reg _ _ _ _ _ _ HS) FR SHNZ TM TSC) as PATP.
      rewrite EN in PATP. rewrite <- E1 in PATP. apply PATP; [clear - NR; lia| | exact G0| exact G1].
      pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. change (bv_modulus 64) with (2 ^ 64) in RK. rewrite EA in RK.
      unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold AREQMAX in NR. clear - RK NR. Z.div_mod_to_equations. lia. }

  pose proof (so_reg _ _ _ _ _ _ HS sh r FR) as RO.
  pose proof (CallA.TwinB.size_shape_sound E _ nsv (so_facts _ _ _ _ _ _ HS) SS) as SHAPE.
  pose proof (CallA.TwinB.is_twin_region_sound bsegs (s_priv st) E (ms_mem ms) sh r nsv RO SHNZ TR) as PATR.
  rewrite EN in PATR. rewrite <- E1 in PATR.
  apply PATR; [unfold AREQMAX in NR; lia| | exact G0| exact G1].
  destruct nsv; try exact I; rewrite <- EN; exact SHAPE.
Qed.

Definition find_sliver (st : sstate) (ks : int) : option int :=
  match List.find (fun kr : int * region => negb (PrimInt63.eqb (fst kr) 0%uint63) && negb (PrimInt63.eqb (fst kr) ks)
                      && sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) (fst kr) (snd kr)) (IMap.elements (s_regs st)) with
  | Some kr => Some (fst kr)
  | None => None
  end.
Definition sp_lo (E : env) (st : sstate) : Z :=
  match sp_region st with
  | Some (k, _, rs) => match find_sliver st k with Some b => bv_unsigned (ev E b) | None => bv_unsigned (ev E k) + loZ rs end
  | None => 0
  end.

Lemma find_sliver_spec : forall st ks b, IMap.bst (s_regs st) -> find_sliver st ks = Some b ->
  exists r, IMap.find b (s_regs st) = Some r /\ b <> 0%uint63 /\ b <> ks
    /\ sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) b r = true.
Proof.
  intros st ks b BST H. unfold find_sliver in H.
  match type of H with match ?f with _ => _ end = _ => destruct f as [[b0 r0]|] eqn:F; [|discriminate H] end. injection H as <-. cbn [fst].
  apply List.find_some in F as [IN CK]. cbn [fst snd] in CK. apply andb_prop in CK as [CK SJ]. apply andb_prop in CK as [N0 NK].
  apply negb_true_iff in N0, NK. apply Uint63.eqb_false_spec in N0, NK.
  exists r0. split; [apply (IMap.elements_spec _ _ _ BST); exact IN|]. auto.
Qed.

Lemma stack_wlo_ceiling : forall E st hargs n md A nw rest LB wlo,
  find_op HEAP_ID (s_ops st) = Some hargs -> heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest ->
  windows_wf (wins_of E n rest) LB (ATOP + 4096) -> stack_wlo st = Some wlo ->
  ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo)).
Proof.
  intros E st hargs n md A nw rest LB wlo Hf Hn Eh WF SW. unfold stack_wlo in SW. rewrite Hf, Hn, Eh in SW.
  destruct (stack_window_key n rest) as [w|] eqn:SK; [|discriminate SW]. destruct (nowrap_kb (s_facts st) STACK_ID w); [|discriminate SW]. injection SW as ->.
  destruct (CallA.TwinB.stack_window_key_In E n rest wlo SK) as (len & INw).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  destruct KDs as [[_ C]|[[K _]|[K _]]]; [exact C| unfold K_BLOCK, K_STACK in K; lia| unfold K_SUB, K_STACK in K; lia].
Qed.

Lemma sp_lo_spec : forall E st ms mo ks offs rss hargs n md A nw rest LB,
  st_ok bsegs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) ->
  find_op HEAP_ID (s_ops st) = Some hargs -> heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest ->
  windows_wf (wins_of E n rest) LB (ATOP + 4096) ->
  ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss -> bv_unsigned (ev E ks) + loZ rss <= 2 ^ 64 ->
  (ATOP + 4096 <= sp_lo E st <= bv_unsigned (ev E ks) + loZ rss)
  /\ stk bsegs (ms_mem ms) (sp_lo E st) (bv_unsigned (ev E ks) + loZ rss).
Proof.
  intros E st ms mo ks offs rss hargs n md A nw rest LB HS SPR Hf Hn Eh WF FLOOR TOP. pose proof atop_range as ATR.
  unfold sp_lo. rewrite SPR. destruct (find_sliver st ks) as [b|] eqn:FS.
  - destruct (find_sliver_spec st ks b (so_bst _ _ _ _ _ _ HS) FS) as (r & Fb & B0 & BK & SJ).
    destruct (CallA.TwinB.sliver_just_sound bsegs OPS E st ms mo ks offs rss b r HS SPR Fb B0 SJ) as (RC & RB & RW & L0 & wlo & SW & EK & EH).
    pose proof (stack_wlo_ceiling E st hargs n md A nw rest LB wlo Hf Hn Eh WF SW) as CE.
    pose proof (bv_unsigned_in_range 64 (den E (rg_hi r))) as RH. unfold bv_modulus in RH. fold (hiZ E r) in RH.
    split; [rewrite EK; lia|].
    assert (BZ : PrimInt63.eqb b 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact B0).
    pose proof (so_reg _ _ _ _ _ _ HS b r Fb) as RO.
    unfold stk. split; [lia|]. split; [exact TOP|]. intros a Ha.
    destruct (ro_valid _ _ _ _ _ _ RO BZ a ltac:(rewrite L0; lia)) as (V1 & V2 & _).
    split; [apply (GlueA.TwinB.wb_wviewA bsegs); apply V2; exact RW|]. rewrite (GlueA.TwinB.rb_mrdA bsegs) in V1.
    destruct (ALib.Mem.mrd bsegs (ms_mem ms) (ALib.Mem.wa a)); [eexists; reflexivity| congruence].
  - split; [lia|]. apply stk_empty. lia.
Qed.

Lemma stk_sp_region : forall E st (m' : amem) ks offs rss sp, sp_region st = Some (ks, offs, rss) ->
  sp_lo E st <= bv_unsigned (ev E ks) + loZ rss <= sp ->
  stk bsegs m' (sp_lo E st) sp -> stk bsegs m' (bv_unsigned (ev E ks) + loZ rss) sp.
Proof. intros E st m' ks offs rss sp SPR LE ST. exact (proj2 (stk_split bsegs m' _ _ _ ST LE)). Qed.

Lemma sp_lo_of_sliver : forall E st ms mo ks offs rss k0 rg,
  st_ok bsegs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) ->
  IMap.find k0 (s_regs st) = Some rg -> k0 <> 0%uint63 -> k0 <> ks ->
  sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k0 rg = true ->
  sp_lo E st = bv_unsigned (ev E k0) /\ loZ rg = 0 /\ bv_unsigned (ev E k0) + hiZ E rg = bv_unsigned (ev E ks) + loZ rss
  /\ rg_cells rg = IMap.Leaf /\ rg_bg rg = BGNone
  /\ exists wlo, stack_wlo st = Some wlo /\ bv_unsigned (ev E k0) = bv_unsigned (den E (VP STACK_ID wlo)).
Proof.
  intros E st ms mo ks offs rss k0 rg HS SPR Fk K0 KS SJ.
  destruct (CallA.TwinB.sliver_just_sound bsegs OPS E st ms mo ks offs rss k0 rg HS SPR Fk K0 SJ) as (RC & RB & RW & L0 & wlo & SW & EK & EH).
  split; [| split; [exact L0| split; [exact EH| split; [exact RC| split; [exact RB| exists wlo; split; [exact SW| exact EK]]]]]].
  unfold sp_lo. rewrite SPR. destruct (find_sliver st ks) as [b|] eqn:FS.
  - destruct (find_sliver_spec st ks b (so_bst _ _ _ _ _ _ HS) FS) as (r & Fb & B0 & BK & SJb).
    destruct (CallA.TwinB.sliver_just_sound bsegs OPS E st ms mo ks offs rss b r HS SPR Fb B0 SJb) as (_ & _ & _ & _ & wlo' & SW' & EK' & _).
    rewrite SW in SW'. injection SW' as <-. rewrite EK, EK'. reflexivity.
  - exfalso. unfold find_sliver in FS.
    match type of FS with match ?f with _ => _ end = _ => destruct f as [kr|] eqn:F; [discriminate FS|] end.
    pose proof (List.find_none _ _ F (k0, rg) (proj2 (IMap.elements_spec _ _ _ (so_bst _ _ _ _ _ _ HS)) Fk)) as X. cbn [fst snd] in X.
    rewrite SJ in X. apply Uint63.eqb_false_spec in K0, KS. rewrite K0, KS in X. discriminate X.
Qed.

Lemma sp_lo_le : forall E st ms mo ks offs rss, st_ok bsegs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) ->
  sp_lo E st <= bv_unsigned (ev E ks) + loZ rss.
Proof.
  intros E st ms mo ks offs rss HS SPR. unfold sp_lo. rewrite SPR. destruct (find_sliver st ks) as [b|] eqn:FS; [| lia].
  destruct (find_sliver_spec st ks b (so_bst _ _ _ _ _ _ HS) FS) as (r & Fb & B0 & BK & SJb).
  destruct (CallA.TwinB.sliver_just_sound bsegs OPS E st ms mo ks offs rss b r HS SPR Fb B0 SJb) as (_ & _ & _ & _ & wlo & _ & _ & EH).
  pose proof (bv_unsigned_in_range 64 (den E (rg_hi r))) as RH. fold (hiZ E r) in RH. lia.
Qed.

Lemma sliver_low : forall E st ms mo ks offs rss k r hargs n md A nw rest LB a,
  st_ok bsegs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) -> IMap.find k (s_regs st) = Some r -> k <> 0%uint63 -> k <> ks ->
  sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k r = true ->
  find_op HEAP_ID (s_ops st) = Some hargs -> hargs = VL md :: A :: VL nw :: rest -> wt nw = false -> n = Z.to_nat (to_Z (wl nw)) ->
  (3 * n <= length rest)%nat -> windows_wf (wins_of E n rest) LB (ATOP + 4096) ->
  bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r ->
  ATOP + 4096 <= a < bv_unsigned (ev E ks) + loZ rss.
Proof.
  intros E st ms mo ks offs rss k r hargs n md A nw rest LB a HS SPR Fk K0 KS SL Hf Eh Tnw Nn Ln WF Ha.
  destruct (sp_lo_of_sliver E st ms mo ks offs rss k r HS SPR Fk K0 KS SL) as (_ & L0 & EH & _ & _ & wlo & SW & EKW).
  pose proof (CallV.TwinB.wlo_floor E st hargs n md A nw rest LB (ATOP + 4096) wlo Hf Eh Tnw Nn Ln WF SW) as CE. rewrite L0 in Ha. lia.
Qed.

Lemma sliver_region_ok : forall E E' st ms mo (m' : amem) ks offs rss k0 rg sp,
  st_ok bsegs OPS E st ms mo -> sp_region st = Some (ks, offs, rss) ->
  IMap.find k0 (s_regs st) = Some rg -> k0 <> 0%uint63 -> k0 <> ks ->
  sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k0 rg = true ->
  ev E' k0 = ev E k0 -> hiZ E' rg = hiZ E rg ->
  bv_unsigned (ev E ks) + loZ rss <= sp -> stk bsegs m' (sp_lo E st) sp ->
  region_ok bsegs (s_priv st) E' m' k0 rg.
Proof.
  intros E E' st ms mo m' ks offs rss k0 rg sp HS SPR Fk K0 KS SJ EK' EH' LE ST.
  destruct (sp_lo_of_sliver E st ms mo ks offs rss k0 rg HS SPR Fk K0 KS SJ) as (ELO & L0 & EH & RC & RB & _).
  pose proof (so_reg _ _ _ _ _ _ HS k0 rg Fk) as RO.
  assert (KZ : PrimInt63.eqb k0 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  destruct ST as (_ & _ & ST).
  constructor.
  - exact (ro_bst _ _ _ _ _ _ RO).
  - intros _. rewrite EK', EH'. exact (ro_range _ _ _ _ _ _ RO KZ).
  - intros _ a Ha. rewrite EK', EH' in Ha.
    destruct (ro_valid _ _ _ _ _ _ RO KZ a Ha) as (_ & _ & SEG).
    destruct (ST a ltac:(rewrite ELO; rewrite L0 in Ha; lia)) as [WV (bb & MR)].
    split; [rewrite (GlueA.TwinB.rb_mrdA bsegs), MR; discriminate|]. split; [intros _; apply (GlueA.TwinB.wb_wviewA bsegs); exact WV| exact SEG].
  - intros g gr Fg. rewrite RC in Fg. discriminate Fg.
  - intros g gr c i Fg. rewrite RC in Fg. discriminate Fg.
  - intros o _ _ _. unfold bg_byte. rewrite RB. exact I.
Qed.

Lemma ATPi_eq : to_Z ATPi = ATP. Proof. reflexivity. Qed.

Definition acall_facts (XN : r5) (E : env) (st : sstate) (ms : machine_state) (mo : Model)
    (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (n : Z) : Prop :=
  exists (LB : blocks) (r : int) (hargs : list sv) (st1 : sstate) (ks : int) (offs : w64) (rss : region) (ksp : int)
         (wnl : list (int * sv * w64)) (nn : nat) (md : w64) (A : sv) (nw : w64) (rest : list sv),
    call_pre st = Some r /\ forget_stack_below_sp_g st = Some st1
    /\ sp_region st = Some (ks, offs, rss) /\ okey offs = Some ksp
    /\ bv_unsigned (AP.getr (ms_regs ms) 2%bv) = bv_unsigned (ev E ks) + keyZ ksp
    /\ keyZ ksp mod 16 = 0 /\ loZ rss <= keyZ ksp /\ ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss
    /\ find_op HEAP_ID (s_ops st) = Some hargs /\ CtrA.count_op HEAP_ID (s_ops st) = 1%nat
    /\ hargs = VL md :: A :: VL nw :: rest /\ wt nw = false /\ nn = Z.to_nat (to_Z (wl nw)) /\ (3 * nn <= length rest)%nat /\ (nn <= 255)%nat
    /\ CtrA.nonstack_windows nn rest = Some wnl /\ aregions_justified st wnl = true
    /\ windows_wf (wins_of E nn rest) LB (ATOP + 4096)
    /\ cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) (ms_mem ms)
    /\ aw = den E A
    /\ (exists W, wit_of W L RNG sta LBa /\ aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W /\ ties W (wins_of E nn rest))
    /\ bv_unsigned (den E (getr st XN)) = n /\ (XN = X11 -> exists w, getr st XN = VL w).

Definition prist_in (E : env) (st : sstate) : Prop :=
  exists hargs md A nw rest, find_op HEAP_ID (s_ops st) = Some hargs /\ hargs = VL md :: A :: VL nw :: rest
    /\ In prist_win (wins_of E (Z.to_nat (to_Z (wl nw))) rest).
Lemma prist_absent_not_in : forall E st hargs, facts_hold E (s_facts st) -> find_op HEAP_ID (s_ops st) = Some hargs ->
  prist_absent (s_facts st) hargs = true -> ~ prist_in E st.
Proof.
  intros E st hargs HF FO PA (h2 & md & A & nw & rest & FO2 & Eh & IP). rewrite FO in FO2. injection FO2 as <-.
  unfold prist_absent in PA. destruct (heap_nwin hargs) as [n|] eqn:HN; [|discriminate].
  destruct (heap_nwin_shape hargs n HN) as (md' & A' & nw' & rest' & Eh' & T & N & Ln). rewrite Eh in Eh'. injection Eh' as <- <- <- <-.
  rewrite Eh in PA. subst n. exact (CallA.TwinB.wins_not_prist_sound E _ HF _ _ PA IP).
Qed.

Lemma prist_in_aprist : forall XN E st ms mo L RNG sta LBa aw n, acall_facts XN E st ms mo L RNG sta LBa aw n -> prist_in E st -> aprist sta.
Proof.
  intros XN E st ms mo L RNG sta LBa aw n CF (h2 & md2 & A2 & nw2 & rest2 & FO2 & Eh2 & IP).
  destruct CF as (LB & r & hargs & st1 & ks & offs & rss & ksp & wnl & nn & md & A & nw & rest
                  & CP & FS & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255 & NW & AJ & WF & HC & AWden & (W & WOF & AR & TI) & NDEN & SHAPE).
  rewrite Hf in FO2. injection FO2 as <-. rewrite Eh in Eh2. injection Eh2 as <- <- <- <-. rewrite <- Nn in IP.
  destruct WOF as (_ & _ & <- & _). exact (ties_prist W _ TI IP).
Qed.

Lemma amalloc_pre_facts : forall st sts E ms mo,
  st_ok bsegs OPS E st ms mo -> to_Z (s_pc st) = AMALLOC_SYM -> amalloc_apply UNIV AMALLOC_PC st = Some sts ->
  let R := ms_regs ms in
  let lo := sp_lo E st in
  exists (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (n : Z),
    ms = MS R (ms_fregs ms) (Z_to_bv 64 AMALLOC_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom bsegs)
    /\ AHEAP AI L RNG sta LBa (ms_mem ms) /\ ACCT aw L RNG sta LBa mo /\ incl UNIV (al_U L)
    /\ ALib.Mem.mem_inv bsegs (ms_mem ms)
    /\ stk bsegs (ms_mem ms) lo (bv_unsigned (AP.getr R 2)) /\ ATOP + 4096 <= lo /\ lo <= bv_unsigned (AP.getr R 2) - 4608
    /\ AP.getr R 4 = Z_to_bv 64 ATP /\ AP.getr R 10 = Z_to_bv 64 n /\ 1 <= n <= AREQMAX
    /\ (1048576 <= bv_unsigned aw /\ (prim_decided (s_facts st) (getr st X10) = true \/ n <= bv_unsigned aw))
    /\ (exists tr, aunw (ms_mem ms) L RNG lo AMALLOC_PC (AP.getr R 2) (AP.getr R 8) (AP.getr R 1) tr)
    /\ bv_unsigned (AP.getr R 8) <> bv_unsigned (AP.getr R 2) + 8 /\ 4096 <= bv_unsigned (AP.getr R 1)
    /\ bv_unsigned (AP.getr R 1) <> AMALLOC_PC
    /\ bv_unsigned (AP.getr R 2) mod 16 = 0 /\ rng RNG lo (bv_unsigned (AP.getr R 2) - lo)
    /\ acall_facts X10 E st ms mo L RNG sta LBa aw n
    /\ (64512 < n \/ ~ prist_in E st).
Proof.
  intros st sts E ms mo HS HPC Happ R lo.
  destruct (amalloc_apply_inv st sts Happ) as (r & tp & hargs & cred & st1 & CP & TP & FO & HAc & TPE & SR & SFO & UO & SPT & RO & N0 & N1 & NC & PRA & TI & FS & _).
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.

  unfold twins_intact in TI. destruct (aheap_windows st) as [[h wnl]|] eqn:HW; [|discriminate]. clear TI.
  destruct (aheap_call_facts E st ms mo h wnl HS HW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (aw_realW_AHEAP AI ACCT UNIV _ _ _ _ _ ARW) as (AH & AC & HU).
  set (L := w_L W) in *. set (RNG := w_RNG W) in *. set (sta := w_st W) in *. set (LBa := w_LBa W) in *.
  rewrite FO in Hf. injection Hf as <-. rewrite Eh, heap_A_eq in HAc. injection HAc as <-.

  destruct (CallA.TwinB.stack_sound_g bsegs OPS E st ms mo AMALLOC_ROOM HS ltac:(vm_compute; reflexivity) SR)
    as (k & off & rs & ksp & HX2 & Hr & K0 & Hksp & K16 & A16 & Esp & LO0 & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.TwinB.sp_floor_sound bsegs OPS E st ms mo hargs n md A nw rest k off rs HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K _]|[K _]]]; [exact C| unfold K_BLOCK, K_STACK in K; lia| unfold K_SUB, K_STACK in K; lia]. }

  destruct (CallA.TwinB.amalloc_regs bsegs OPS E st ms mo r tp A HS CP TP TPE N0 N1 NC) as (RV & RA & RR & TP4 & N10 & NCR).
  fold R in RA, TP4, N10, NCR.
  pose proof (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS) as GR.
  assert (SP2 : bv_unsigned (AP.getr R 2) = bv_unsigned (ev E k) + keyZ ksp).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X2, (GR X2). exact Esp. }
  assert (SP47 : bv_unsigned (AP.getr R 2) < 2 ^ 47).
  { unfold sp_top_ok in SPT. pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF SPT) as X. unfold R. rewrite <- HeapCtr.TwinB.reg_of_X2, (GR X2).
    replace (bv_unsigned (den E (VL SP_TOPw))) with (2 ^ 47) in X by (vm_compute; reflexivity). exact X. }
  assert (RA1 : bv_unsigned (AP.getr R 1) = to_Z r) by (rewrite RA; apply Z_to_bv_small; unfold bv_modulus; lia).
  unfold ret_ok in RO. apply andb_prop in RO as [R4096 RNE]. apply Uint63.leb_spec in R4096. change (to_Z 4096%uint63) with 4096 in R4096.
  apply negb_true_iff in RNE. apply Z.eqb_neq in RNE.
  pose proof (ACCT_rng _ _ _ _ _ _ AC) as RSTK. pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _). pose proof atop_range as AR.
  set (sp := bv_unsigned (AP.getr R 2)) in *.
  destruct (sp_lo_spec E st ms mo k off rs hargs n md A nw rest LB HS SPR FO Hn Eh WF ltac:(lia) ltac:(pose proof (Uint63.to_Z_bounded AMALLOC_ROOM); lia)) as [[LOB LOLE] STKlo]. fold lo in LOB, LOLE, STKlo.
  assert (ASTK : to_Z AMALLOC_ROOM = 12288) by reflexivity.
  exists L, RNG, sta, LBa, (den E A), (bv_unsigned (AP.getr R 10)).
  split. { rewrite <- HPC. exact (GlueA.TwinB.ms_formA bsegs OPS E st ms mo HS RV). }
  split; [exact AH|]. split; [exact AC|]. split; [exact HU|].
  split. { intros a b Hm. unfold ALib.Mem.ro_addr. destruct (find_segment bsegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
           rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity. }
  split. { rewrite SP2. apply (stk_merge bsegs _ lo (bv_unsigned (ev E k) + loZ rs)); [exact STKlo| exact STK| lia]. }
  split; [exact LOB|]. split; [lia|].
  split; [rewrite TP4, ATPi_eq; reflexivity|].
  split; [symmetry; apply Z_to_bv_bv_unsigned|].
  split; [unfold AREQMAX; lia|]. split; [exact NCR|].
  destruct (aunw_chain E st ms mo hargs n md A nw rest k off rs W L RNG sta LBa AMALLOC_PC r lo HS Hn Eh SPR SFO
              ltac:(fold R; fold sp; rewrite SP2; lia) TI AH LB (den E A) WF ARW UO HU SP47 RR LOB ltac:(eapply rng_sub'; [exact RSTK|]; lia)) as [AUNW S0NE].
  split. { rewrite RA. exact AUNW. }
  split; [exact S0NE|]. split; [lia|]. split; [rewrite RA1; exact RNE|].
  split. { fold sp. rewrite SP2. rewrite Z.add_mod, A16, K16 by lia. reflexivity. }
  split; [eapply rng_sub'; [exact RSTK|]; lia|].
  split.
  2: { destruct (sec_decided (s_facts st) (getr st X10)) eqn:SD.
       - left. pose proof (CallA.TwinB.sec_decided_sound E _ _ HF SD) as Q. unfold R. rewrite <- HeapCtr.TwinB.reg_of_X10, (GR X10). exact Q.
       - right. exact (prist_absent_not_in E st _ HF FO PRA). }
  exists LB, r, hargs, st1, k, off, rs, ksp, wnl, n, md, A, nw, rest.
  split; [exact CP|]. split; [exact FS|]. split; [exact SPR|]. split; [exact Hksp|]. split; [exact SP2|]. split; [exact K16|].
  split; [lia|]. split; [lia|]. split; [exact FO|]. split; [exact Hc|]. split; [exact Eh|]. split; [exact T|]. split; [exact N|].
  split; [exact Ln|]. split; [exact N255|]. split; [exact NW|]. split; [exact JU|]. split; [exact WF|]. split; [exact HC|].
  split; [reflexivity|]. split; [exists W; split; [apply wit_of_refl| split; [exact ARW| exact TI]]|].
  split; [| intros X; discriminate X]. unfold R. rewrite <- HeapCtr.TwinB.reg_of_X10, (GR X10). reflexivity.
Qed.

Lemma aaligned_apply_inv : forall st sts, aaligned_apply UNIV F_aaligned_iseg.TwinB.AALIGNED_PC st = Some sts ->
  exists r tp hargs cred st1 al,
    call_pre st = Some r /\ getr st X4 = VL tp /\ find_op HEAP_ID (s_ops st) = Some hargs /\ heap_A hargs = Some cred
    /\ getr st X10 = VL al /\ weqb al (wlit 16%uint63) = true /\ aligned_size_ok (getr st X11) = true
    /\ weqb tp (wlit ATPi) = true /\ stack_room_g st AMALLOC_ROOM = true /\ sp_floor_ok st hargs = true
    /\ unw_ok UNIV F_aaligned_iseg.TwinB.AALIGNED_PC r st hargs = true /\ sp_top_ok st = true /\ ret_ok F_aaligned_iseg.TwinB.AALIGNED_PC r = true
    /\ cred_pre (s_facts st) (getr st X11) cred = true
    /\ prist_absent (s_facts st) hargs = true
    /\ twins_intact st hargs = true
    /\ forget_stack_below_sp_g st = Some st1
    /\ exists stN stB, sts = [stN; stB] /\ null_post hargs cred (clobber st1) r = Some stN.
Proof.
  intros st sts H. unfold aaligned_apply in H.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |] eqn:TP; try discriminate.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:FO; [|discriminate].
  destruct (getr st X10) as [al| | | | | | | | | |] eqn:X10E; try discriminate.
  destruct (heap_A hargs) as [cred|] eqn:HA; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  do 11 (apply andb_prop in CK as [CK ?]).
  destruct (forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate].
  destruct (null_post hargs cred (clobber st1) r) as [stN|] eqn:NP; [|discriminate].
  destruct (fresh (clobber st1)) as [k st3] eqn:F1. destruct (fresh st3) as [sh st4] eqn:F2.
  destruct (heap_set_A hargs (cred_post (s_facts st) (getr st X11) cred)) as [h1|]; [|discriminate].
  destruct (heap_add_window h1 (VP k wzero) (getr st X11) (VL CtrLib.K_BLOCK)) as [h2|]; [|discriminate].
  destruct (heap_add_window h2 (VP sh wzero) (twin_len (getr st X11)) (VL K_TWIN)) as [h3|]; [|discriminate].
  injection H as <-.
  exists r, tp, hargs, cred, st1, al. repeat (split; [first [assumption | reflexivity]|]).
  do 2 eexists. split; [reflexivity| exact NP].
Qed.

Lemma aaligned_pre_facts : forall st sts E ms mo,
  st_ok bsegs OPS E st ms mo -> to_Z (s_pc st) = F_aaligned_iseg.TwinB.AALIGNED_SYM -> aaligned_apply UNIV F_aaligned_iseg.TwinB.AALIGNED_PC st = Some sts ->
  let R := ms_regs ms in
  let lo := sp_lo E st in
  exists (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (n : Z),
    ms = MS R (ms_fregs ms) (Z_to_bv 64 F_aaligned_iseg.TwinB.AALIGNED_SYM) (ms_fcsr ms) None (ms_mem ms) (seg_rom bsegs)
    /\ AHEAP AI L RNG sta LBa (ms_mem ms) /\ ACCT aw L RNG sta LBa mo /\ incl UNIV (al_U L)
    /\ ALib.Mem.mem_inv bsegs (ms_mem ms)
    /\ stk bsegs (ms_mem ms) lo (bv_unsigned (AP.getr R 2)) /\ ATOP + 4096 <= lo /\ lo <= bv_unsigned (AP.getr R 2) - 4608
    /\ AP.getr R 4 = Z_to_bv 64 ATP /\ AP.getr R 10 = Z_to_bv 64 16 /\ AP.getr R 11 = Z_to_bv 64 n
    /\ F_aalloc1.TwinB.F_aalloc1_16.is_primary16 n = true /\ n mod 16 = 0 /\ 16 <= n <= 4096
    /\ (1048576 <= bv_unsigned aw /\ (prim_decided (s_facts st) (getr st X11) = true \/ n <= bv_unsigned aw))
    /\ (exists tr, aunw (ms_mem ms) L RNG lo F_aaligned_iseg.TwinB.AALIGNED_PC (AP.getr R 2) (AP.getr R 8) (AP.getr R 1) tr)
    /\ bv_unsigned (AP.getr R 8) <> bv_unsigned (AP.getr R 2) + 8 /\ 4096 <= bv_unsigned (AP.getr R 1)
    /\ bv_unsigned (AP.getr R 1) <> F_aaligned_iseg.TwinB.AALIGNED_PC
    /\ bv_unsigned (AP.getr R 2) mod 16 = 0 /\ rng RNG lo (bv_unsigned (AP.getr R 2) - lo)
    /\ acall_facts X11 E st ms mo L RNG sta LBa aw n
    /\ ~ prist_in E st.
Proof.
  intros st sts E ms mo HS HPC Happ R lo.
  destruct (aaligned_apply_inv st sts Happ) as (r & tp & hargs & cred & st1 & al & CP & TP & FO & HAc & X10E & AL16 & ASZ & TPE & SR & SFO & UO & SPT & RO & NC & PRA & TI & FS & _).
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.

  unfold twins_intact in TI. destruct (aheap_windows st) as [[h wnl]|] eqn:HW; [|discriminate]. clear TI.
  destruct (aheap_call_facts E st ms mo h wnl HS HW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (aw_realW_AHEAP AI ACCT UNIV _ _ _ _ _ ARW) as (AH & AC & HU).
  set (L := w_L W) in *. set (RNG := w_RNG W) in *. set (sta := w_st W) in *. set (LBa := w_LBa W) in *.
  rewrite FO in Hf. injection Hf as <-. rewrite Eh, heap_A_eq in HAc. injection HAc as <-.

  destruct (CallA.TwinB.stack_sound_g bsegs OPS E st ms mo AMALLOC_ROOM HS ltac:(vm_compute; reflexivity) SR)
    as (k & off & rs & ksp & HX2 & Hr & K0 & Hksp & K16 & A16 & Esp & LO0 & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.TwinB.sp_floor_sound bsegs OPS E st ms mo hargs n md A nw rest k off rs HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K _]|[K _]]]; [exact C| unfold K_BLOCK, K_STACK in K; lia| unfold K_SUB, K_STACK in K; lia]. }

  destruct (CallA.TwinB.acall_regs bsegs OPS E st ms mo r tp HS CP TP TPE) as (RV & RA & RR & TP4). fold R in RA, TP4.

  unfold aligned_size_ok in ASZ. destruct (getr st X11) as [nw0| | | | | | | | | |] eqn:X11E; try discriminate ASZ.
  apply andb_prop in ASZ as [ASZ M16]. apply andb_prop in ASZ as [ASZ NHI]. apply andb_prop in ASZ as [NWT NLO]. apply negb_true_iff in NWT.
  apply Uint63.leb_spec in NLO. apply Uint63.leb_spec in NHI. change (to_Z 16%uint63) with 16 in NLO. change (to_Z ALIGNED_NMAX) with 4096 in NHI.
  apply Uint63.eqb_correct in M16.
  assert (M16Z : to_Z (wl nw0) mod 16 = 0).
  { pose proof (ValP.land_mk (wl nw0) 4%uint63 ltac:(change (to_Z 4%uint63) with 4; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 4) 1)%uint63 with 15%uint63 in LM. rewrite M16 in LM. change (to_Z 0%uint63) with 0 in LM. change (2 ^ to_Z 4%uint63) with 16 in LM. lia. }
  assert (DNW : bv_unsigned (den E (VL nw0)) = to_Z (wl nw0)) by (cbn [den]; rewrite wbv_unsigned; exact (w2Z_nowt nw0 NWT)).
  assert (NCR : 1048576 <= bv_unsigned (den E A) /\ (prim_decided (s_facts st) (VL nw0) = true \/ to_Z (wl nw0) <= bv_unsigned (den E A))).
  { unfold cred_pre in NC. apply andb_prop in NC as [NCX NC].
    pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF NCX) as LX. replace (bv_unsigned (den E (VL C_EXHw))) with 1048576 in LX by (vm_compute; reflexivity).
    split; [exact LX|]. apply orb_prop in NC as [NC|NC]; [left; exact NC| right]. pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF NC) as Y. rewrite DNW in Y. exact Y. }
  pose proof (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS) as GR.
  assert (SP2 : bv_unsigned (AP.getr R 2) = bv_unsigned (ev E k) + keyZ ksp).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X2, (GR X2). exact Esp. }
  assert (SP47 : bv_unsigned (AP.getr R 2) < 2 ^ 47).
  { unfold sp_top_ok in SPT. pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF SPT) as X. unfold R. rewrite <- HeapCtr.TwinB.reg_of_X2, (GR X2).
    replace (bv_unsigned (den E (VL SP_TOPw))) with (2 ^ 47) in X by (vm_compute; reflexivity). exact X. }
  assert (RA1 : bv_unsigned (AP.getr R 1) = to_Z r) by (rewrite RA; apply Z_to_bv_small; unfold bv_modulus; lia).
  unfold ret_ok in RO. apply andb_prop in RO as [R4096 RNE]. apply Uint63.leb_spec in R4096. change (to_Z 4096%uint63) with 4096 in R4096.
  apply negb_true_iff in RNE. apply Z.eqb_neq in RNE.
  pose proof (ACCT_rng _ _ _ _ _ _ AC) as RSTK. pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _). pose proof atop_range as AR.
  set (sp := bv_unsigned (AP.getr R 2)) in *.
  destruct (sp_lo_spec E st ms mo k off rs hargs n md A nw rest LB HS SPR FO Hn Eh WF ltac:(lia) ltac:(pose proof (Uint63.to_Z_bounded AMALLOC_ROOM); lia)) as [[LOB LOLE] STKlo]. fold lo in LOB, LOLE, STKlo.
  assert (ASTK : to_Z AMALLOC_ROOM = 12288) by reflexivity.
  exists L, RNG, sta, LBa, (den E A), (to_Z (wl nw0)).
  split. { rewrite <- HPC. exact (GlueA.TwinB.ms_formA bsegs OPS E st ms mo HS RV). }
  split; [exact AH|]. split; [exact AC|]. split; [exact HU|].
  split. { intros a b Hm. unfold ALib.Mem.ro_addr. destruct (find_segment bsegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
           rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity. }
  split. { rewrite SP2. apply (stk_merge bsegs _ lo (bv_unsigned (ev E k) + loZ rs)); [exact STKlo| exact STK| lia]. }
  split; [exact LOB|]. split; [lia|].
  split; [rewrite TP4, ATPi_eq; reflexivity|].
  split. { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X10, (GR X10), X10E. apply (proj1 (weqb_ok _ _)) in AL16. subst al. rewrite HeapCtr.TwinB.den_wlit. reflexivity. }
  split. { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X11, (GR X11), X11E. rewrite <- (Z_to_bv_bv_unsigned (den E (VL nw0))), DNW. reflexivity. }
  split. { unfold F_aalloc1.TwinB.F_aalloc1_16.is_primary16, F_aalloc1.TwinB.F_aalloc1_16.needed16, F_aalloc1.TwinB.F_aalloc1_16.rounded_size16, rup, K_MAX_SIZE. apply Z.leb_le.
           pose proof (APrimFacts.TwinB.rz_size_range (to_Z (wl nw0))) as [[RZ1 RZ2] _]. rewrite Z.max_l by lia. Z.div_mod_to_equations. lia. }
  split; [exact M16Z|].
  split; [lia|]. split; [exact NCR|].
  destruct (aunw_chain E st ms mo hargs n md A nw rest k off rs W L RNG sta LBa F_aaligned_iseg.TwinB.AALIGNED_PC r lo HS Hn Eh SPR SFO
              ltac:(fold R; fold sp; rewrite SP2; lia) TI AH LB (den E A) WF ARW UO HU SP47 RR LOB ltac:(eapply rng_sub'; [exact RSTK|]; lia)) as [AUNW S0NE].
  split. { rewrite RA. exact AUNW. }
  split; [exact S0NE|]. split; [lia|]. split; [rewrite RA1; exact RNE|].
  split. { fold sp. rewrite SP2. rewrite Z.add_mod, A16, K16 by lia. reflexivity. }
  split; [eapply rng_sub'; [exact RSTK|]; lia|].
  split; [| exact (prist_absent_not_in E st _ HF FO PRA)].
  exists LB, r, hargs, st1, k, off, rs, ksp, wnl, n, md, A, nw, rest.
  split; [exact CP|]. split; [exact FS|]. split; [exact SPR|]. split; [exact Hksp|]. split; [exact SP2|]. split; [exact K16|].
  split; [lia|]. split; [lia|]. split; [exact FO|]. split; [exact Hc|]. split; [exact Eh|]. split; [exact T|]. split; [exact N|].
  split; [exact Ln|]. split; [exact N255|]. split; [exact NW|]. split; [exact JU|]. split; [exact WF|]. split; [exact HC|].
  split; [reflexivity|]. split; [exists W; split; [apply wit_of_refl| split; [exact ARW| exact TI]]|].
  split; [rewrite X11E; exact DNW| intros _; exists nw0; exact X11E].
Qed.

Lemma acall_pre_inv : forall room unw st r hargs wnl st1, acall_pre room unw st = Some (r, hargs, wnl, st1) ->
  exists tp, call_pre st = Some r /\ getr st X4 = VL tp /\ aheap_windows st = Some (hargs, wnl)
    /\ weqb tp (wlit ATPi) = true /\ stack_room_g st room = true /\ sp_floor_ok st hargs = true /\ sp_top_ok st = true
    /\ match unw with Some (U, PCz) => unw_ok U PCz r st hargs = true /\ ret_ok PCz r = true | None => True end
    /\ forget_stack_below_sp_g st = Some st1.
Proof.
  intros room unw st r hargs wnl st1 H. unfold acall_pre in H.
  destruct (call_pre st) as [r0|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |] eqn:TP; try discriminate.
  destruct (aheap_windows st) as [[h w]|] eqn:HW; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  destruct (forget_stack_below_sp_g st) as [s1|] eqn:FS; [|discriminate]. injection H as -> -> -> ->.
  do 4 (apply andb_prop in CK as [CK ?]).
  exists tp. repeat (split; [reflexivity || assumption|]). split; [| reflexivity].
  destruct unw as [[U PCz]|]; [| exact I]. match goal with X : (if _ then _ else false) = true |- _ => apply andb_prop in X as [? ?] end. auto.
Qed.

Lemma acall_pre_nt_inv : forall room unw st r hargs wnl st1, acall_pre_nt room unw st = Some (r, hargs, wnl, st1) ->
  exists tp, call_pre st = Some r /\ getr st X4 = VL tp /\ aheap_windows_nt st = Some (hargs, wnl)
    /\ weqb tp (wlit ATPi) = true /\ stack_room_g st room = true /\ sp_floor_ok st hargs = true /\ sp_top_ok st = true
    /\ match unw with Some (U, PCz) => unw_ok U PCz r st hargs = true /\ ret_ok PCz r = true | None => True end
    /\ forget_stack_below_sp_g st = Some st1.
Proof.
  intros room unw st r hargs wnl st1 H. unfold acall_pre_nt in H.
  destruct (call_pre st) as [r0|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |] eqn:TP; try discriminate.
  destruct (aheap_windows_nt st) as [[h w]|] eqn:HW; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  destruct (forget_stack_below_sp_g st) as [s1|] eqn:FS; [|discriminate]. injection H as -> -> -> ->.
  do 4 (apply andb_prop in CK as [CK ?]).
  exists tp. repeat (split; [reflexivity || assumption|]). split; [| reflexivity].
  destruct unw as [[U PCz]|]; [| exact I]. match goal with X : (if _ then _ else false) = true |- _ => apply andb_prop in X as [? ?] end. auto.
Qed.
Lemma aheap_windows_nt_of : forall st x, aheap_windows st = Some x -> aheap_windows_nt st = Some x.
Proof.
  intros st x H. unfold aheap_windows in H. unfold aheap_windows_nt.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|]; [|discriminate].
  destruct (CtrA.count_op HEAP_ID (s_ops st)) as [|[|c]]; try discriminate.
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|]; [|discriminate].
  destruct (heap_nwin hargs) as [n|]; [|discriminate].
  destruct hargs as [|h0 [|h1 [|h2 rest]]]; try discriminate.
  destruct (Nat.leb n 255 && stack_window_ok_g n rest (rg_lo r1)); [|discriminate].
  destruct (CtrA.nonstack_windows n rest) as [wl|]; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Q; [|discriminate] end.
  apply andb_prop in Q as [Q AJ]. apply andb_prop in Q as [WA TS]. rewrite WA, AJ. exact H.
Qed.
Lemma acall_pre_nt_of : forall room unw st x, acall_pre room unw st = Some x -> acall_pre_nt room unw st = Some x.
Proof.
  intros room unw st x H. unfold acall_pre in H. unfold acall_pre_nt.
  destruct (call_pre st) as [r0|]; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |]; try discriminate.
  destruct (aheap_windows st) as [[h w]|] eqn:HW; [|discriminate].
  rewrite (aheap_windows_nt_of st _ HW). exact H.
Qed.

Definition acallG (E : env) (st : sstate) (ms : machine_state) (mo : Model) (r : int) (hargs : list sv) (wnl : list (int * sv * w64))
    (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) : Prop :=
  exists (LB : blocks) (ks : int) (offs : w64) (rss : region) (ksp : int) (nn : nat) (md : w64) (A : sv) (nw : w64) (rest : list sv),
    sp_region st = Some (ks, offs, rss) /\ okey offs = Some ksp
    /\ bv_unsigned (AP.getr (ms_regs ms) 2%bv) = bv_unsigned (ev E ks) + keyZ ksp
    /\ keyZ ksp mod 16 = 0 /\ loZ rss <= keyZ ksp /\ ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss
    /\ find_op HEAP_ID (s_ops st) = Some hargs /\ CtrA.count_op HEAP_ID (s_ops st) = 1%nat
    /\ hargs = VL md :: A :: VL nw :: rest /\ wt nw = false /\ nn = Z.to_nat (to_Z (wl nw)) /\ (3 * nn <= length rest)%nat /\ (nn <= 255)%nat
    /\ CtrA.nonstack_windows nn rest = Some wnl /\ CtrA.windows_anchored (s_regs st) wnl = true /\ aregions_justified st wnl = true
    /\ twins_scan (s_facts st) (s_regs st) wnl wnl = true
    /\ windows_wf (wins_of E nn rest) LB (ATOP + 4096)
    /\ cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) (ms_mem ms)
    /\ aw = den E A
    /\ exists W, wit_of W L RNG sta LBa /\ aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W /\ ties W (wins_of E nn rest).

Lemma acall_pre_facts0 : forall room unw st r hargs wnl st1 E ms mo,
  st_ok bsegs OPS E st ms mo -> 4096 <= to_Z room < 2 ^ 32 ->
  acall_pre room unw st = Some (r, hargs, wnl, st1) ->
  let R := ms_regs ms in
  let lo := sp_lo E st in
  exists (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
    ms = MS R (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None (ms_mem ms) (seg_rom bsegs)
    /\ AHEAP AI L RNG sta LBa (ms_mem ms) /\ ACCT aw L RNG sta LBa mo /\ incl UNIV (al_U L)
    /\ ALib.Mem.mem_inv bsegs (ms_mem ms)
    /\ stk bsegs (ms_mem ms) lo (bv_unsigned (AP.getr R 2)) /\ ATOP + 4096 <= lo /\ lo <= bv_unsigned (AP.getr R 2) - 4096
    /\ lo <= bv_unsigned (AP.getr R 2) - to_Z room
    /\ AP.getr R 4 = Z_to_bv 64 ATP
    /\ AP.getr R 1 = Z_to_bv 64 (to_Z r) /\ 0 <= to_Z r < 2 ^ 62
    /\ bv_unsigned (AP.getr R 2) < 2 ^ 47
    /\ bv_unsigned (AP.getr R 2) mod 16 = 0 /\ rng RNG lo (bv_unsigned (AP.getr R 2) - lo)
    /\ call_pre st = Some r /\ forget_stack_below_sp_g st = Some st1
    /\ acallG E st ms mo r hargs wnl L RNG sta LBa aw.
Proof.
  intros room unw st r hargs wnl st1 E ms mo HS ROOM Hpre R lo.
  destruct (acall_pre_inv room _ st r hargs wnl st1 Hpre) as (tp & CP & TP & HW & TPE & SR & SFO & SPT & _ & FS).
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (aheap_call_facts E st ms mo hargs wnl HS HW)
    as (r1 & n & md & A & nw & rest & LB & Hr1 & Hf & Hc & Hn & Eh & T & N & Ln & N255 & SW & NW & AN & JU & HA & WF & HC & W & ARW & TI).
  destruct (aw_realW_AHEAP AI ACCT UNIV _ _ _ _ _ ARW) as (AH & AC & HU).
  set (L := w_L W) in *. set (RNG := w_RNG W) in *. set (sta := w_st W) in *. set (LBa := w_LBa W) in *.
  destruct (CallA.TwinB.stack_sound_g bsegs OPS E st ms mo room HS ltac:(lia) SR)
    as (k & off & rs & ksp & HX2 & Hr & K0 & Hksp & K16 & A16 & Esp & LO0 & HI64 & STK & SPR & LOR & LOZ0).
  destruct (CallA.TwinB.sp_floor_sound bsegs OPS E st ms mo hargs n md A nw rest k off rs HS SFO Hn Eh SPR LOZ0) as (wlo & len & INw & FLOOR).
  pose proof (proj1 (Forall_forall _ _) WF _ INw) as (_ & _ & _ & KDs). cbn [w_kind w_lo] in KDs.
  assert (CE : ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo))).
  { destruct KDs as [[_ C]|[[K _]|[K _]]]; [exact C| unfold K_BLOCK, K_STACK in K; lia| unfold K_SUB, K_STACK in K; lia]. }
  destruct (CallA.TwinB.acall_regs bsegs OPS E st ms mo r tp HS CP TP TPE) as (RV & RA & RR & TP4). fold R in RA, TP4.
  pose proof (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS) as GR.
  assert (SP2 : bv_unsigned (AP.getr R 2) = bv_unsigned (ev E k) + keyZ ksp).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X2, (GR X2). exact Esp. }
  assert (SP47 : bv_unsigned (AP.getr R 2) < 2 ^ 47).
  { unfold sp_top_ok in SPT. pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF SPT) as X. unfold R. rewrite <- HeapCtr.TwinB.reg_of_X2, (GR X2).
    replace (bv_unsigned (den E (VL SP_TOPw))) with (2 ^ 47) in X by (vm_compute; reflexivity). exact X. }
  pose proof (ACCT_rng _ _ _ _ _ _ AC) as RSTK. pose proof atop_range as ATR.
  set (sp := bv_unsigned (AP.getr R 2)) in *.
  destruct (sp_lo_spec E st ms mo k off rs hargs n md A nw rest LB HS SPR Hf Hn Eh WF ltac:(lia) ltac:(lia)) as [[LOB LOLE] STKlo]. fold lo in LOB, LOLE, STKlo.
  exists L, RNG, sta, LBa, (den E A).
  split. { exact (GlueA.TwinB.ms_formA bsegs OPS E st ms mo HS RV). }
  split; [exact AH|]. split; [exact AC|]. split; [exact HU|].
  split. { intros a b Hm. unfold ALib.Mem.ro_addr. destruct (find_segment bsegs (bv_unsigned a) 1) as [seg|] eqn:Fs; [|reflexivity].
           rewrite (so_minv _ _ _ _ _ _ HS a b Hm seg Fs). reflexivity. }
  split. { rewrite SP2. apply (stk_merge bsegs _ lo (bv_unsigned (ev E k) + loZ rs)); [exact STKlo| exact STK| lia]. }
  split; [exact LOB|]. split; [lia|]. split; [lia|].
  split; [rewrite TP4, ATPi_eq; reflexivity|].
  split; [exact RA|]. split; [exact RR|]. split; [exact SP47|].
  split. { fold sp. rewrite SP2. rewrite Z.add_mod, A16, K16 by lia. reflexivity. }
  split; [eapply rng_sub'; [exact RSTK|]; lia|].
  split; [exact CP|]. split; [exact FS|].
  exists LB, k, off, rs, ksp, n, md, A, nw, rest.
  split; [exact SPR|]. split; [exact Hksp|]. split; [exact SP2|]. split; [exact K16|]. split; [lia|]. split; [lia|].
  split; [exact Hf|]. split; [exact Hc|]. split; [exact Eh|]. split; [exact T|]. split; [exact N|]. split; [exact Ln|]. split; [exact N255|].
  split; [exact NW|]. split; [exact AN|]. split; [exact JU|].
  split. { destruct (CallA.TwinB.aheap_windows_inv st hargs wnl HW) as (_ & _ & r1' & n' & md2 & A2 & nw2 & rest2 & _ & _ & Eh2 & _ & N2 & _ & _ & _ & NW2 & _ & _ & TS).
           exact TS. }
  split; [exact WF|]. split; [exact HC|]. split; [reflexivity|].
  exists W. split; [apply wit_of_refl| split; [exact ARW| exact TI]].
Qed.

Lemma acall_sp_altop : forall E st ms mo r hargs wnl L RNG sta LBa aw,
  st_ok bsegs OPS E st ms mo -> acallG E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> bv_unsigned (AP.getr (ms_regs ms) 2%bv) < 2 ^ 47 ->
  sp_floor_ok st hargs = true -> sp_altop_ok st hargs = true ->
  bv_unsigned (AP.getr (ms_regs ms) 2%bv) <= al_top L.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw HS G AH SP47 SFO SAO.
  destruct G as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                 & NW & AN & AJ & TS & WF & CW & EA & W & WOF & ARW & TI).
  assert (Hn : heap_nwin hargs = Some nn).
  { rewrite Eh. unfold heap_nwin. rewrite Tnw, <- Nn. destruct (Nat.leb_spec (3 * nn) (length rest)); [reflexivity| lia]. }
  destruct (CallA.TwinB.sp_altop_sound bsegs OPS E st ms mo hargs nn md A nw rest HS SAO Hn Eh) as (wlo & len & SK & INw & D).
  pose proof (CallA.TwinB.sp_floor_key bsegs OPS E st ms mo hargs nn md A nw rest ks offs rss wlo HS SFO Hn Eh SPR SK) as FL.
  assert (SP2 : bv_unsigned (den E (getr st X2)) = bv_unsigned (AP.getr (ms_regs ms) 2%bv)).
  { rewrite <- HeapCtr.TwinB.reg_of_X2, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X2). reflexivity. }
  rewrite SP2 in D.
  apply (stk0_sp_bound AI W (wins_of E nn rest) _ L RNG sta LBa (ms_mem ms) _ TI INw); [reflexivity| | exact AH| exact D].
  cbn [w_lo]. unfold ZC_BASE. lia.
Qed.

Lemma acall_pre_room : forall room unw st r hargs wnl st1 E ms mo,
  st_ok bsegs OPS E st ms mo -> 4096 <= to_Z room < 2 ^ 32 ->
  acall_pre room unw st = Some (r, hargs, wnl, st1) ->
  sp_lo E st <= bv_unsigned (AP.getr (ms_regs ms) 2) - to_Z room.
Proof.
  intros room unw st r hargs wnl st1 E ms mo HS ROOM Hpre.
  destruct (acall_pre_facts0 room unw st r hargs wnl st1 E ms mo HS ROOM Hpre) as (L & RNG & sta & LBa & aw & _ & _ & _ & _ & _ & _ & _ & _ & LOR & _).
  exact LOR.
Qed.

Lemma acall_pre_facts : forall room PCz st r hargs wnl st1 E ms mo,
  st_ok bsegs OPS E st ms mo -> 4096 <= to_Z room < 2 ^ 32 ->
  acall_pre room (Some (UNIV, PCz)) st = Some (r, hargs, wnl, st1) ->
  let R := ms_regs ms in
  let lo := sp_lo E st in
  exists (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word),
    ms = MS R (ms_fregs ms) (Z_to_bv 64 (to_Z (s_pc st))) (ms_fcsr ms) None (ms_mem ms) (seg_rom bsegs)
    /\ AHEAP AI L RNG sta LBa (ms_mem ms) /\ ACCT aw L RNG sta LBa mo
    /\ ALib.Mem.mem_inv bsegs (ms_mem ms)
    /\ stk bsegs (ms_mem ms) lo (bv_unsigned (AP.getr R 2)) /\ ATOP + 4096 <= lo /\ lo <= bv_unsigned (AP.getr R 2) - 4096
    /\ AP.getr R 4 = Z_to_bv 64 ATP
    /\ (exists tr, aunw (ms_mem ms) L RNG lo PCz (AP.getr R 2) (AP.getr R 8) (AP.getr R 1) tr)
    /\ bv_unsigned (AP.getr R 8) <> bv_unsigned (AP.getr R 2) + 8 /\ 4096 <= bv_unsigned (AP.getr R 1)
    /\ bv_unsigned (AP.getr R 1) <> PCz
    /\ bv_unsigned (AP.getr R 2) mod 16 = 0 /\ rng RNG lo (bv_unsigned (AP.getr R 2) - lo)
    /\ call_pre st = Some r /\ forget_stack_below_sp_g st = Some st1
    /\ acallG E st ms mo r hargs wnl L RNG sta LBa aw.
Proof.
  intros room PCz st r hargs wnl st1 E ms mo HS ROOM Hpre R lo.
  destruct (acall_pre_inv room _ st r hargs wnl st1 Hpre) as (tp & _ & _ & _ & _ & _ & SFO & _ & (UO & RO) & _).
  destruct (acall_pre_facts0 room _ st r hargs wnl st1 E ms mo HS ROOM Hpre)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & HU & MI & ST & BOT & LO & _ & TP & RA & RR & SP47 & SP16 & RSTKlo & CP & FS & CF).
  fold R in Ems, ST, LO, TP, RA, SP47, SP16, RSTKlo. fold lo in ST, BOT, LO, RSTKlo.
  assert (RA1 : bv_unsigned (AP.getr R 1) = to_Z r) by (rewrite RA; apply Z_to_bv_small; unfold bv_modulus; lia).
  unfold ret_ok in RO. apply andb_prop in RO as [R4096 RNE]. apply Uint63.leb_spec in R4096. change (to_Z 4096%uint63) with 4096 in R4096.
  apply negb_true_iff in RNE. apply Z.eqb_neq in RNE.
  pose proof (ACCT_rng _ _ _ _ _ _ AC) as RSTK. pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _).
  exists L, RNG, sta, LBa, aw.
  split; [exact Ems|]. split; [exact AH|]. split; [exact AC|]. split; [exact MI|]. split; [exact ST|]. split; [exact BOT|]. split; [exact LO|].
  split; [exact TP|].
  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & CW & EA & W & WOF & ARW & TI).
  assert (Hn : heap_nwin hargs = Some nn).
  { rewrite Eh. unfold heap_nwin. rewrite Tnw, <- Nn. destruct (Nat.leb_spec (3 * nn) (length rest)); [reflexivity| lia]. }
  destruct (aunw_chain E st ms mo hargs nn md A nw rest ks offs rss W L RNG sta LBa PCz r lo HS Hn Eh SPR SFO
              ltac:(unfold R in *; rewrite SPE; lia) TI AH LB aw WF ltac:(rewrite EA in *; exact ARW) UO HU SP47 RR BOT ltac:(eapply rng_sub'; [exact RSTK|]; lia)) as [AUNW S0NE].
  split. { rewrite RA. exact AUNW. }
  split; [exact S0NE|]. split; [lia|]. split; [rewrite RA1; exact RNE|].
  split; [exact SP16|]. split; [exact RSTKlo|]. split; [exact CP|]. split; [exact FS| exact CF].
Qed.

Lemma wins_of_length : forall E n ws, (length (wins_of E n ws) <= n)%nat.
Proof. intros E n. induction n as [|n IH]; intros ws; [cbn; lia|]. destruct ws as [|lo [|len [|kd ws]]]; cbn; try lia. specialize (IH ws). lia. Qed.

Lemma c24_of_ties : forall E W L RNG sta LBa aw LB m mo nn rest,
  wit_of W L RNG sta LBa -> aw_realW AI ACCT UNIV aw LB m mo W -> ties W (wins_of E nn rest) -> (nn <= 255)%nat -> C24.TwinB.c24count LBa <= 255.
Proof.
  intros E W L RNG sta LBa aw LB m mo nn rest (_ & _ & _ & <-) [HW _] TI N.
  pose proof (C24.TwinB.c24count_le_windows AI ACCT UNIV W aw LB m mo _ HW TI). pose proof (wins_of_length E nn rest). lia.
Qed.

Lemma acall_facts_c24 : forall XN E st ms mo L RNG sta LBa aw n, acall_facts XN E st ms mo L RNG sta LBa aw n ->
  C24.TwinB.c24count LBa <= 255 /\ bv_unsigned (den E (getr st XN)) = n.
Proof.
  intros XN E st ms mo L RNG sta LBa aw n (LB & r & hargs & st1 & ks & offs & rss & ksp & wnl & nn & md & A & nw & rest
    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N255 & _ & _ & _ & _ & _ & (W & WOF & AR & TI) & NDEN & _).
  split; [exact (c24_of_ties E W L RNG sta LBa aw LB _ mo nn rest WOF AR TI N255)| exact NDEN].
Qed.

Lemma acallG_c24 : forall E st ms mo r hargs wnl L RNG sta LBa aw, acallG E st ms mo r hargs wnl L RNG sta LBa aw -> C24.TwinB.c24count LBa <= 255.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw (LB & ks & offs & rss & ksp & nn & md & A & nw & rest
    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N255 & _ & _ & _ & _ & _ & _ & _ & (W & WOF & AR & TI)).
  exact (c24_of_ties E W L RNG sta LBa aw LB _ mo nn rest WOF AR TI N255).
Qed.

End Pre.
End TwinB.
