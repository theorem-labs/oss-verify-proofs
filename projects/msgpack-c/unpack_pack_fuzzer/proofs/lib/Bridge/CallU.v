(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.PropExec ALib.MState ALib.Frame ALib.Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Instr Mem State Step Plan ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import GlueA Actr CallA.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP CtrLib CtrFX ActrA.
Open Scope Z_scope.
Unset Lia Cache.

Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require KnownA.
Unset Nia Cache. Unset Nra Cache.
Module AMem := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Section CallU.
Variable segs : list Segment.
Variable OPS : optable.

Lemma altop_v_sound : forall E st ms mo hargs n md A nw rest v slack,
  st_ok segs OPS E st ms mo -> altop_ok_v st hargs v slack = true ->
  heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest ->
  exists wlo len, stack_window_key n rest = Some wlo
    /\ In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len HeapOp.K_STACK) (wins_of E n rest)
    /\ bv_unsigned (den E v) + slack - bv_unsigned (den E (VP STACK_ID wlo)) <= SPALT.
Proof.
  intros E st ms mo hargs n md A nw rest v slack HS H Hn Eh. unfold altop_ok_v in H. rewrite Hn, Eh in H.
  destruct v as [|k off| | | | | | | | |]; try discriminate.
  destruct (stack_window_key n rest) as [wlo|] eqn:SK; [|discriminate].
  apply andb_prop in H as [H ARM]. apply andb_prop in H as [NW1 NW2].
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (nowrap_kb_sound E _ HF STACK_ID wlo NW1) as [R1 D1]. destruct (nowrap_kb_sound E _ HF k off NW2) as [R2 D2].
  destruct (stack_window_key_In E n rest wlo SK) as (len & IN). exists wlo, len. split; [reflexivity|]. split; [exact IN|]. rewrite D1, D2.
  destruct (PrimInt63.eqb k STACK_ID) eqn:K1.
  - apply Uint63.eqb_correct in K1. subst k. apply Z.leb_le in ARM. lia.
  - destruct (GTwinSub.GTwinSub.find_ub (s_facts st) k) as [[kb o1]|] eqn:UB; [|discriminate].
    apply andb_prop in ARM as [ARM LE]. apply andb_prop in ARM as [KB NW3]. apply Uint63.eqb_correct in KB. subst kb. apply Z.leb_le in LE.
    destruct (nowrap_kb_sound E _ HF STACK_ID o1 NW3) as [R3 D3].
    pose proof (GTwinSub.GTwinSub.find_ub_holds E _ k STACK_ID o1 HF UB) as U. rewrite D3, HeapCtr.den_VPz in U. lia.
Qed.

Lemma land7_mod8 : forall i : int, (PrimInt63.eqb (PrimInt63.land i 7%uint63) 0%uint63 = true <-> to_Z i mod 8 = 0).
Proof.
  intros i. pose proof (land_mk i 3%uint63 ltac:(change (to_Z 3%uint63) with 3; lia)) as LM.
  change (PrimInt63.sub (PrimInt63.lsl 1 3) 1)%uint63 with 7%uint63 in LM. change (2 ^ to_Z 3%uint63) with 8 in LM.
  split; intros H.
  - apply Uint63.eqb_correct in H. rewrite H in LM. change (to_Z 0%uint63) with 0 in LM. lia.
  - apply Uint63.eqb_spec. apply Uint63.to_Z_inj. rewrite LM, H. reflexivity.
Qed.

Lemma w2Z_mod8 : forall a : w64, w2Z a mod 8 = to_Z (wl a) mod 8.
Proof.
  intros [t l]. unfold w2Z. cbn [wt wl]. destruct t; [| reflexivity].
  replace (two63 + to_Z l) with (to_Z l + 1152921504606846976 * 8) by (unfold two63; lia). apply Z.mod_add. lia.
Qed.
Lemma w2Zs_mod8 : forall a : w64, w2Zs a mod 8 = to_Z (wl a) mod 8.
Proof.
  intros a. unfold w2Zs. destruct (wt a); [| apply w2Z_mod8].
  replace (w2Z a - two64) with (w2Z a + (-2305843009213693952) * 8) by (unfold two64; lia). rewrite Z.mod_add by lia. apply w2Z_mod8.
Qed.

Lemma frame_al8_sound : forall E fs v b, facts_hold E fs -> frame_al8 fs v = Some b ->
  (b = true <-> bv_unsigned (den E v) mod 8 = 0).
Proof.
  intros E fs v b HF H. unfold frame_al8 in H. destruct v as [a|k off| | | | | | | | |]; try discriminate.
  - injection H as <-. rewrite (land7_mod8 (wl a)). cbn [den]. rewrite wbv_unsigned, w2Z_mod8. reflexivity.
  - destruct (PrimInt63.leb 3%uint63 (find_align fs k)) eqn:AL; [|discriminate]. injection H as <-.
    pose proof (find_align_le E fs HF k 3%uint63 AL) as X. change (2 ^ to_Z 3%uint63) with 8 in X.
    rewrite (land7_mod8 (wl off)). rewrite den_VP.
    assert (M64 : forall z, (z mod two64) mod 8 = z mod 8).
    { intros z. unfold two64. rewrite <- Znumtheory.Zmod_div_mod; [reflexivity| lia| lia|]. exists 2305843009213693952. reflexivity. }
    rewrite M64. rewrite Z.add_mod, X, w2Zs_mod8 by lia. rewrite Z.add_0_l, Z.mod_mod by lia. reflexivity.
Qed.

Lemma cell8_sound : forall priv E m k r key v,
  region_ok segs priv E m k r -> cell8 r key = Some v ->
  0 <= bv_unsigned (ev E k) + keyZ key -> bv_unsigned (ev E k) + keyZ key + 8 <= 2 ^ 64 ->
  AMem.bytes_at segs m (bv_unsigned (ev E k) + keyZ key) (AMem.le8 (den E v)).
Proof.
  intros priv E m k r key v RO H LO HI. unfold cell8 in H.
  destruct (PrimInt63.eqb (gidx key) 0%uint63) eqn:GI; [|discriminate]. apply Uint63.eqb_correct in GI.
  destruct (IMap.find (granule key) (rg_cells r)) as [[d [|[ci cw cv] [|? ?]]]|] eqn:FG; try discriminate.
  destruct (PrimInt63.eqb ci 0%uint63 && PrimInt63.eqb cw 8%uint63)%bool eqn:CK; [|discriminate]. injection H as ->.
  apply andb_prop in CK as [CI CW]. apply Uint63.eqb_correct in CI. apply Uint63.eqb_correct in CW. subst ci cw.
  pose proof (keyZ_range key) as KR.
  destruct (granule_gidx key ltac:(unfold two63; lia)) as [EK _]. rewrite GI in EK. change (to_Z 0%uint63) with 0 in EK.
  destruct (ro_cells _ _ _ _ _ _ RO (granule key) _ FG) as [_ FC]. cbn [g_cells] in FC.
  apply Forall_inv in FC. destruct FC as (_ & _ & _ & CB). cbn [c_idx c_w c_v] in CB. change (to_Z 0%uint63) with 0 in CB. change (to_Z 8%uint63) with 8 in CB.
  split; [exact LO|]. split; [rewrite AMem.length_le8; lia|].
  intros i Hi. rewrite AMem.length_le8 in Hi.
  change (AMem.mrd segs m (AMem.wa (bv_unsigned (ev E k) + keyZ key + Z.of_nat i))) with (rb segs m (bv_unsigned (ev E k) + keyZ key + Z.of_nat i)).
  replace (bv_unsigned (ev E k) + keyZ key + Z.of_nat i) with (bv_unsigned (ev E k) + 8 * keyZ (granule key) + 0 + Z.of_nat i) by lia.
  rewrite (CB (Z.of_nat i) ltac:(lia)).
  unfold AMem.le8, word_to_le_bytes, byte_of. symmetry. apply HeapCtrB.nth_error_Z_to_le_bytes. exact Hi.
Qed.

Lemma frame_rec_sound : forall E st ms mo kf off fp ra,
  st_ok segs OPS E st ms mo -> frame_rec st (VP kf off) = Some (fp, ra) ->
  let F := bv_unsigned (den E (VP kf off)) in
  16 <= F
  /\ AMem.bytes_at segs (ms_mem ms) (F - 16) (AMem.le8 (den E fp))
  /\ AMem.bytes_at segs (ms_mem ms) (F - 8) (AMem.le8 (den E ra)).
Proof.
  intros E st ms mo kf off fp ra HS H F. unfold frame_rec in H.
  destruct (IMap.find kf (s_regs st)) as [rf|] eqn:FR; [|discriminate].
  destruct (okey (wsub off (wlit 16%uint63))) as [o16|] eqn:K16; [|discriminate].
  destruct (okey off) as [o0|] eqn:K0; [|discriminate].
  destruct (PrimInt63.eqb kf 0%uint63) eqn:KZ; [discriminate|].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  apply andb_prop in CK as [CK HIK]. apply andb_prop in CK as [LOK LT].
  destruct (rg_hi rf) as [h| | | | | | | | | |] eqn:Hhi; try discriminate HIK.
  destruct (okey h) as [hk|] eqn:KH; [|discriminate HIK].
  destruct (cell8 rf o16) as [fp'|] eqn:C16; [|discriminate]. destruct (cell8 rf (PrimInt63.add o16 8%uint63)) as [ra'|] eqn:C8; [|discriminate].
  injection H as -> ->.
  rewrite kleb_keyZ in LOK, HIK. rewrite kltb_keyZ in LT. apply Z.leb_le in LOK. apply Z.leb_le in HIK. apply Z.ltb_lt in LT.
  destruct (okey_sound _ _ K16) as [E16 R16]. destruct (okey_sound _ _ K0) as [E0 R0]. destruct (okey_sound _ _ KH) as [EH RH].
  rewrite !half63 in *.
  assert (W16 : w2Zs (wlit 16%uint63) = 16) by (rewrite w2Zs_eq, wlit_ok; cbn [wt wlit]; reflexivity).
  assert (E16' : keyZ o16 = keyZ o0 - 16).
  { destruct (Z_lt_le_dec (w2Zs off - 16) (- two63)) as [L|L].
    - exfalso. rewrite <- E0 in L. unfold two63 in L, R0. lia.
    - rewrite E16, E0. rewrite GlueA.w2Zs_wsub_small; rewrite W16; [reflexivity|]. rewrite <- E0. unfold two63 in *. lia. }
  pose proof (so_reg _ _ _ _ _ _ HS _ _ FR) as RO.
  destruct (ro_range _ _ _ _ _ _ RO KZ) as [RLO RHI]. unfold two64 in RHI.
  assert (Ehi : keyZ hk <= hiZ E rf).
  { unfold hiZ. rewrite Hhi, unsigned_VL, EH, w2Zs_eq. unfold two64. destruct (wt h); lia. }
  assert (EF : F = bv_unsigned (ev E kf) + keyZ o0).
  { unfold F. rewrite den_VP, <- E0. unfold loZ in *. apply Z.mod_small. unfold two64. lia. }
  assert (K8 : keyZ (PrimInt63.add o16 8%uint63) = keyZ o16 + 8).
  { apply keyZ_add_small; [rewrite half63; lia| change (to_Z 8%uint63) with 8; lia]. }
  unfold loZ in *.
  split; [lia|]. split.
  - replace (F - 16) with (bv_unsigned (ev E kf) + keyZ o16) by lia.
    apply (cell8_sound (s_priv st) E (ms_mem ms) kf rf o16 fp RO C16); lia.
  - replace (F - 8) with (bv_unsigned (ev E kf) + keyZ (PrimInt63.add o16 8%uint63)) by lia.
    apply (cell8_sound (s_priv st) E (ms_mem ms) kf rf _ ra RO C8); lia.
Qed.

End CallU.

Lemma s0_far_sound : forall (segs : list Segment) (OPS : optable) E st ms mo wl (LOWV : Z), st_ok segs OPS E st ms mo -> s0_far st wl = true ->
  (forall v, below_stack (s_facts st) wl v = true -> bv_unsigned (den E v) < LOWV) -> LOWV <= bv_unsigned (den E (getr st X2)) ->
  bv_unsigned (den E (getr st X2)) < 2 ^ 47 ->
  bv_unsigned (den E (getr st X8)) <= bv_unsigned (den E (getr st X2)) \/ bv_unsigned (den E (getr st X2)) + 16 <= bv_unsigned (den E (getr st X8)).
Proof.
  intros segs OPS E st ms mo wl LOWV HS H BS LOWP SP47. pose proof (so_facts _ _ _ _ _ _ HS) as HF. unfold s0_far in H.
  destruct (below_stack (s_facts st) wl (getr st X8)) eqn:B0; [left; pose proof (BS _ B0); lia|].
  destruct (KnownT.KnownT.known_leu_t (s_facts st) (getr st X8) (getr st X2)) eqn:K1; [left; exact (KnownA.KnownA.known_leu_sound E _ _ _ HF K1)|].
  right. pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF H) as X. rewrite den_sv_alu in X. cbn [alu64 alu den] in X.
  rewrite bv_add_unsigned, wbv_unsigned, wlit_ok in X. change (to_Z 16%uint63) with 16 in X. unfold bv_wrap in X. rewrite bv_modulus_64 in X.
  pose proof (bv_unsigned_in_range 64 (den E (getr st X2))) as R2. rewrite Z.mod_small in X by (unfold two64; lia). exact X.
Qed.

Section Walk.
Context {rc : RunConst.runConstT}.
Variable OPS : optable.

Lemma unw_classify_sound : forall E st ms mo hargs n md A nw rest wl (top LOWV : Z) prev frame,
  st_ok asegs OPS E st ms mo -> heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest ->
  (forall wlo x, stack_window_key n rest = Some wlo -> x - bv_unsigned (den E (VP STACK_ID wlo)) <= SPALT -> x <= top) ->
  top <= 2 ^ 47 ->
  (forall v, below_stack (s_facts st) wl v = true -> bv_unsigned (den E v) < LOWV) -> LOWV <= bv_unsigned (den E prev) ->
  let P := bv_unsigned (den E prev) in let F := bv_unsigned (den E frame) in
  match unw_classify st hargs wl prev frame with
  | UCStop => ~ (P < F /\ F < top - 16 /\ F mod 8 = 0)
  | UCIn => P < F /\ F < top - 16 /\ F mod 8 = 0
  | UCMaybe => P < F /\ F mod 8 = 0
  | UCUnk => True
  end.
Proof.
  intros E st ms mo hargs n md A nw rest wl top LOWV prev frame HS Hn Eh TOPB T47 BS LOWP. cbv zeta.
  remember (bv_unsigned (den E prev)) as P eqn:EP. remember (bv_unsigned (den E frame)) as F eqn:EF0. unfold unw_classify.
  destruct (below_stack (s_facts st) wl frame) eqn:BSF.
  { pose proof (BS _ BSF) as X. rewrite <- EF0 in X. intros (Y & _). lia. }
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (KnownT.KnownT.decide_ltu_tt (s_facts st) prev frame) as [[|]|] eqn:D; [| | exact I].
  2:{ pose proof (proj1 (ltu_iff _ _ false) (KnownT.KnownT.decide_ltu_tt_sound E _ HF prev frame false D)) as X. rewrite <- EP, <- EF0 in X. intros (Y & _). lia. }
  pose proof (proj1 (ltu_iff _ _ true) (KnownT.KnownT.decide_ltu_tt_sound E _ HF prev frame true D)) as LT. rewrite <- EP, <- EF0 in LT.
  destruct (frame_al8 (s_facts st) frame) as [[|]|] eqn:AL; [| | exact I].
  2:{ pose proof (frame_al8_sound E _ frame false HF AL) as X. rewrite <- EF0 in X. intros (_ & _ & Y). apply X in Y. discriminate Y. }
  pose proof (proj1 (frame_al8_sound E _ frame true HF AL) eq_refl) as M8. rewrite <- EF0 in M8.
  destruct frame as [a|kf off| | | | | | | | |];
    try (destruct (altop_ok_v st hargs _ 17) eqn:AT; [| split; assumption];
         unfold altop_ok_v in AT; rewrite Hn, Eh in AT; discriminate AT).
  - destruct (Z.leb TOP47m16 (w2Z a)) eqn:TL; [| exact I]. apply Z.leb_le in TL. unfold TOP47m16 in TL.
    intros (_ & Y & _). rewrite EF0 in Y. cbn [den] in Y. rewrite wbv_unsigned in Y. lia.
  - destruct (altop_ok_v st hargs (VP kf off) 17) eqn:AT; [| split; assumption].
    destruct (altop_v_sound asegs OPS E st ms mo hargs n md A nw rest _ 17 HS AT Hn Eh) as (wlo & len & SK & _ & LE).
    pose proof (TOPB wlo (F + 17) SK ltac:(rewrite EF0; lia)) as X. split; [exact LT|]. split; [lia| exact M8].
Qed.

Lemma unw_walk_sound : forall E st ms mo hargs n md A nw rest wl (top LOWV : Z) PCz,
  st_ok asegs OPS E st ms mo -> heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest ->
  (forall wlo x, stack_window_key n rest = Some wlo -> x - bv_unsigned (den E (VP STACK_ID wlo)) <= SPALT -> x <= top) ->
  top <= 2 ^ 47 ->
  (forall v, below_stack (s_facts st) wl v = true -> bv_unsigned (den E v) < LOWV) ->
  forall fuel prev frame k cands, LOWV <= bv_unsigned (den E prev) ->
  unw_walk fuel st hargs wl PCz prev frame k = Some cands ->
  exists tr, In tr cands /\ uchain (ms_mem ms) top PCz (bv_unsigned (den E prev)) (bv_unsigned (den E frame)) k tr.
Proof.
  intros E st ms mo hargs n md A nw rest wl top LOWV PCz HS Hn Eh TOPB T47 BS.
  induction fuel as [|f IH]; intros prev frame k cands LOWP H; cbn [unw_walk] in H; [discriminate|].
  destruct k as [|k1].
  { injection H as <-. exists []. split; [left; reflexivity|]. apply uc_stop. intros (_ & _ & _ & X). lia. }
  pose proof (unw_classify_sound E st ms mo hargs n md A nw rest wl top LOWV prev frame HS Hn Eh TOPB T47 BS LOWP) as CL. cbv zeta in CL.
  set (P := bv_unsigned (den E prev)) in *. set (F := bv_unsigned (den E frame)) in *.
  destruct (unw_classify st hargs wl prev frame) eqn:UC.
  - injection H as <-. exists []. split; [left; reflexivity|]. apply uc_stop. intros (X1 & X2 & X3 & _). apply CL. auto.
  -
    destruct CL as (LT & TP & M8).
    destruct (frame_rec st frame) as [[fp [raw| | | | | | | | | |]]|] eqn:FRc; try discriminate.
    destruct frame as [|kf off| | | | | | | | |]; try (cbn in FRc; discriminate FRc).
    destruct (frame_rec_sound asegs OPS E st ms mo kf off fp (VL raw) HS FRc) as (F16 & B16 & B8). fold F in F16, B16, B8.
    assert (ERA : den E (VL raw) = Z_to_bv 64 (w2Z raw)) by reflexivity. rewrite ERA in B8.
    pose proof (w2Z_range raw) as RR. unfold two64 in RR.
    assert (EFP : den E fp = Z_to_bv 64 (bv_unsigned (den E fp))) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite EFP in B16.
    pose proof (bv_unsigned_in_range 64 (den E fp)) as RF. unfold bv_modulus in RF.
    destruct (Z.ltb (w2Z raw) 4096) eqn:LOW.
    + injection H as <-. apply Z.ltb_lt in LOW. exists []. split; [left; reflexivity|].
      eapply uc_lowpc; eauto; lia.
    + apply Z.ltb_ge in LOW.
      destruct (unw_walk f st hargs wl PCz (VP kf off) fp (if w2Z raw =? PCz then S k1 else k1)) as [cands'|] eqn:W; [|discriminate].
      injection H as <-. destruct (IH (VP kf off) fp _ _ ltac:(subst P F; lia) W) as (tr' & IN' & UC').
      exists ((if w2Z raw =? PCz then [] else [w2Z raw]) ++ tr'). split; [apply in_map; exact IN'|].
      eapply uc_step; eauto; try lia.
  -
    destruct CL as (LT & M8).
    destruct (frame_rec st frame) as [[fp [raw| | | | | | | | | |]]|] eqn:FRc; try discriminate.
    destruct frame as [|kf off| | | | | | | | |]; try (cbn in FRc; discriminate FRc).
    destruct (frame_rec_sound asegs OPS E st ms mo kf off fp (VL raw) HS FRc) as (F16 & B16 & B8). fold F in F16, B16, B8.
    assert (ERA : den E (VL raw) = Z_to_bv 64 (w2Z raw)) by reflexivity. rewrite ERA in B8.
    pose proof (w2Z_range raw) as RR. unfold two64 in RR.
    assert (EFP : den E fp = Z_to_bv 64 (bv_unsigned (den E fp))) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite EFP in B16.
    pose proof (bv_unsigned_in_range 64 (den E fp)) as RF. unfold bv_modulus in RF.
    destruct (Z.ltb (w2Z raw) 4096) eqn:LOW.
    + injection H as <-. apply Z.ltb_lt in LOW. exists []. split; [left; reflexivity|].
      destruct (Z_lt_le_dec F (top - 16)) as [TP|TP]; [eapply uc_lowpc; eauto; lia| apply uc_stop; intros (_ & X & _); lia].
    + apply Z.ltb_ge in LOW.
      destruct (unw_walk f st hargs wl PCz (VP kf off) fp (if w2Z raw =? PCz then S k1 else k1)) as [cands'|] eqn:W; [|discriminate].
      injection H as <-. destruct (IH (VP kf off) fp _ _ ltac:(subst P F; lia) W) as (tr' & IN' & UC').
      destruct (Z_lt_le_dec F (top - 16)) as [TP|TP].
      * exists ((if w2Z raw =? PCz then [] else [w2Z raw]) ++ tr'). split; [right; apply in_map; exact IN'|].
        eapply uc_step; eauto; try lia.
      * exists []. split; [left; reflexivity|]. apply uc_stop. intros (_ & X & _). lia.
  - discriminate H.
Qed.
End Walk.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.
Import ABase.TwinB.
Import GlueA.TwinB Actr.TwinB CallA.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP CtrLib CtrFX ActrA.
Open Scope Z_scope.
Unset Lia Cache.

Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.

Unset Nia Cache. Unset Nra Cache.
Module AMem := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.

Section CallU.
Variable segs : list Segment.
Variable OPS : optable.

Lemma altop_v_sound : forall E st ms mo hargs n md A nw rest v slack,
  st_ok segs OPS E st ms mo -> altop_ok_v st hargs v slack = true ->
  heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest ->
  exists wlo len, stack_window_key n rest = Some wlo
    /\ In (HeapOp.Win (bv_unsigned (den E (VP STACK_ID wlo))) len HeapOp.K_STACK) (wins_of E n rest)
    /\ bv_unsigned (den E v) + slack - bv_unsigned (den E (VP STACK_ID wlo)) <= SPALT.
Proof.
  intros E st ms mo hargs n md A nw rest v slack HS H Hn Eh. unfold altop_ok_v in H. rewrite Hn, Eh in H.
  destruct v as [|k off| | | | | | | | |]; try discriminate.
  destruct (stack_window_key n rest) as [wlo|] eqn:SK; [|discriminate].
  apply andb_prop in H as [H ARM]. apply andb_prop in H as [NW1 NW2].
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (nowrap_kb_sound E _ HF STACK_ID wlo NW1) as [R1 D1]. destruct (nowrap_kb_sound E _ HF k off NW2) as [R2 D2].
  destruct (stack_window_key_In E n rest wlo SK) as (len & IN). exists wlo, len. split; [reflexivity|]. split; [exact IN|]. rewrite D1, D2.
  destruct (PrimInt63.eqb k STACK_ID) eqn:K1.
  - apply Uint63.eqb_correct in K1. subst k. apply Z.leb_le in ARM. lia.
  - destruct (GTwinSub.GTwinSub.find_ub (s_facts st) k) as [[kb o1]|] eqn:UB; [|discriminate].
    apply andb_prop in ARM as [ARM LE]. apply andb_prop in ARM as [KB NW3]. apply Uint63.eqb_correct in KB. subst kb. apply Z.leb_le in LE.
    destruct (nowrap_kb_sound E _ HF STACK_ID o1 NW3) as [R3 D3].
    pose proof (GTwinSub.GTwinSub.find_ub_holds E _ k STACK_ID o1 HF UB) as U. rewrite D3, HeapCtr.TwinB.den_VPz in U. lia.
Qed.

Lemma land7_mod8 : forall i : int, (PrimInt63.eqb (PrimInt63.land i 7%uint63) 0%uint63 = true <-> to_Z i mod 8 = 0).
Proof.
  intros i. pose proof (land_mk i 3%uint63 ltac:(change (to_Z 3%uint63) with 3; lia)) as LM.
  change (PrimInt63.sub (PrimInt63.lsl 1 3) 1)%uint63 with 7%uint63 in LM. change (2 ^ to_Z 3%uint63) with 8 in LM.
  split; intros H.
  - apply Uint63.eqb_correct in H. rewrite H in LM. change (to_Z 0%uint63) with 0 in LM. lia.
  - apply Uint63.eqb_spec. apply Uint63.to_Z_inj. rewrite LM, H. reflexivity.
Qed.

Lemma w2Z_mod8 : forall a : w64, w2Z a mod 8 = to_Z (wl a) mod 8.
Proof.
  intros [t l]. unfold w2Z. cbn [wt wl]. destruct t; [| reflexivity].
  replace (two63 + to_Z l) with (to_Z l + 1152921504606846976 * 8) by (unfold two63; lia). apply Z.mod_add. lia.
Qed.
Lemma w2Zs_mod8 : forall a : w64, w2Zs a mod 8 = to_Z (wl a) mod 8.
Proof.
  intros a. unfold w2Zs. destruct (wt a); [| apply w2Z_mod8].
  replace (w2Z a - two64) with (w2Z a + (-2305843009213693952) * 8) by (unfold two64; lia). rewrite Z.mod_add by lia. apply w2Z_mod8.
Qed.

Lemma frame_al8_sound : forall E fs v b, facts_hold E fs -> frame_al8 fs v = Some b ->
  (b = true <-> bv_unsigned (den E v) mod 8 = 0).
Proof.
  intros E fs v b HF H. unfold frame_al8 in H. destruct v as [a|k off| | | | | | | | |]; try discriminate.
  - injection H as <-. rewrite (land7_mod8 (wl a)). cbn [den]. rewrite wbv_unsigned, w2Z_mod8. reflexivity.
  - destruct (PrimInt63.leb 3%uint63 (find_align fs k)) eqn:AL; [|discriminate]. injection H as <-.
    pose proof (find_align_le E fs HF k 3%uint63 AL) as X. change (2 ^ to_Z 3%uint63) with 8 in X.
    rewrite (land7_mod8 (wl off)). rewrite den_VP.
    assert (M64 : forall z, (z mod two64) mod 8 = z mod 8).
    { intros z. unfold two64. rewrite <- Znumtheory.Zmod_div_mod; [reflexivity| lia| lia|]. exists 2305843009213693952. reflexivity. }
    rewrite M64. rewrite Z.add_mod, X, w2Zs_mod8 by lia. rewrite Z.add_0_l, Z.mod_mod by lia. reflexivity.
Qed.

Lemma cell8_sound : forall priv E m k r key v,
  region_ok segs priv E m k r -> cell8 r key = Some v ->
  0 <= bv_unsigned (ev E k) + keyZ key -> bv_unsigned (ev E k) + keyZ key + 8 <= 2 ^ 64 ->
  AMem.bytes_at segs m (bv_unsigned (ev E k) + keyZ key) (AMem.le8 (den E v)).
Proof.
  intros priv E m k r key v RO H LO HI. unfold cell8 in H.
  destruct (PrimInt63.eqb (gidx key) 0%uint63) eqn:GI; [|discriminate]. apply Uint63.eqb_correct in GI.
  destruct (IMap.find (granule key) (rg_cells r)) as [[d [|[ci cw cv] [|? ?]]]|] eqn:FG; try discriminate.
  destruct (PrimInt63.eqb ci 0%uint63 && PrimInt63.eqb cw 8%uint63)%bool eqn:CK; [|discriminate]. injection H as ->.
  apply andb_prop in CK as [CI CW]. apply Uint63.eqb_correct in CI. apply Uint63.eqb_correct in CW. subst ci cw.
  pose proof (keyZ_range key) as KR.
  destruct (granule_gidx key ltac:(unfold two63; lia)) as [EK _]. rewrite GI in EK. change (to_Z 0%uint63) with 0 in EK.
  destruct (ro_cells _ _ _ _ _ _ RO (granule key) _ FG) as [_ FC]. cbn [g_cells] in FC.
  apply Forall_inv in FC. destruct FC as (_ & _ & _ & CB). cbn [c_idx c_w c_v] in CB. change (to_Z 0%uint63) with 0 in CB. change (to_Z 8%uint63) with 8 in CB.
  split; [exact LO|]. split; [rewrite AMem.length_le8; lia|].
  intros i Hi. rewrite AMem.length_le8 in Hi.
  change (AMem.mrd segs m (AMem.wa (bv_unsigned (ev E k) + keyZ key + Z.of_nat i))) with (rb segs m (bv_unsigned (ev E k) + keyZ key + Z.of_nat i)).
  replace (bv_unsigned (ev E k) + keyZ key + Z.of_nat i) with (bv_unsigned (ev E k) + 8 * keyZ (granule key) + 0 + Z.of_nat i) by lia.
  rewrite (CB (Z.of_nat i) ltac:(lia)).
  unfold AMem.le8, word_to_le_bytes, byte_of. symmetry. apply HeapCtrB.TwinB.nth_error_Z_to_le_bytes. exact Hi.
Qed.

Lemma frame_rec_sound : forall E st ms mo kf off fp ra,
  st_ok segs OPS E st ms mo -> frame_rec st (VP kf off) = Some (fp, ra) ->
  let F := bv_unsigned (den E (VP kf off)) in
  16 <= F
  /\ AMem.bytes_at segs (ms_mem ms) (F - 16) (AMem.le8 (den E fp))
  /\ AMem.bytes_at segs (ms_mem ms) (F - 8) (AMem.le8 (den E ra)).
Proof.
  intros E st ms mo kf off fp ra HS H F. unfold frame_rec in H.
  destruct (IMap.find kf (s_regs st)) as [rf|] eqn:FR; [|discriminate].
  destruct (okey (wsub off (wlit 16%uint63))) as [o16|] eqn:K16; [|discriminate].
  destruct (okey off) as [o0|] eqn:K0; [|discriminate].
  destruct (PrimInt63.eqb kf 0%uint63) eqn:KZ; [discriminate|].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  apply andb_prop in CK as [CK HIK]. apply andb_prop in CK as [LOK LT].
  destruct (rg_hi rf) as [h| | | | | | | | | |] eqn:Hhi; try discriminate HIK.
  destruct (okey h) as [hk|] eqn:KH; [|discriminate HIK].
  destruct (cell8 rf o16) as [fp'|] eqn:C16; [|discriminate]. destruct (cell8 rf (PrimInt63.add o16 8%uint63)) as [ra'|] eqn:C8; [|discriminate].
  injection H as -> ->.
  rewrite kleb_keyZ in LOK, HIK. rewrite kltb_keyZ in LT. apply Z.leb_le in LOK. apply Z.leb_le in HIK. apply Z.ltb_lt in LT.
  destruct (okey_sound _ _ K16) as [E16 R16]. destruct (okey_sound _ _ K0) as [E0 R0]. destruct (okey_sound _ _ KH) as [EH RH].
  rewrite !half63 in *.
  assert (W16 : w2Zs (wlit 16%uint63) = 16) by (rewrite w2Zs_eq, wlit_ok; cbn [wt wlit]; reflexivity).
  assert (E16' : keyZ o16 = keyZ o0 - 16).
  { destruct (Z_lt_le_dec (w2Zs off - 16) (- two63)) as [L|L].
    - exfalso. rewrite <- E0 in L. unfold two63 in L, R0. lia.
    - rewrite E16, E0. rewrite GlueA.TwinB.w2Zs_wsub_small; rewrite W16; [reflexivity|]. rewrite <- E0. unfold two63 in *. lia. }
  pose proof (so_reg _ _ _ _ _ _ HS _ _ FR) as RO.
  destruct (ro_range _ _ _ _ _ _ RO KZ) as [RLO RHI]. unfold two64 in RHI.
  assert (Ehi : keyZ hk <= hiZ E rf).
  { unfold hiZ. rewrite Hhi, unsigned_VL, EH, w2Zs_eq. unfold two64. destruct (wt h); lia. }
  assert (EF : F = bv_unsigned (ev E kf) + keyZ o0).
  { unfold F. rewrite den_VP, <- E0. unfold loZ in *. apply Z.mod_small. unfold two64. lia. }
  assert (K8 : keyZ (PrimInt63.add o16 8%uint63) = keyZ o16 + 8).
  { apply keyZ_add_small; [rewrite half63; lia| change (to_Z 8%uint63) with 8; lia]. }
  unfold loZ in *.
  split; [lia|]. split.
  - replace (F - 16) with (bv_unsigned (ev E kf) + keyZ o16) by lia.
    apply (cell8_sound (s_priv st) E (ms_mem ms) kf rf o16 fp RO C16); lia.
  - replace (F - 8) with (bv_unsigned (ev E kf) + keyZ (PrimInt63.add o16 8%uint63)) by lia.
    apply (cell8_sound (s_priv st) E (ms_mem ms) kf rf _ ra RO C8); lia.
Qed.

End CallU.

Lemma s0_far_sound : forall (segs : list Segment) (OPS : optable) E st ms mo wl (LOWV : Z), st_ok segs OPS E st ms mo -> s0_far st wl = true ->
  (forall v, below_stack (s_facts st) wl v = true -> bv_unsigned (den E v) < LOWV) -> LOWV <= bv_unsigned (den E (getr st X2)) ->
  bv_unsigned (den E (getr st X2)) < 2 ^ 47 ->
  bv_unsigned (den E (getr st X8)) <= bv_unsigned (den E (getr st X2)) \/ bv_unsigned (den E (getr st X2)) + 16 <= bv_unsigned (den E (getr st X8)).
Proof.
  intros segs OPS E st ms mo wl LOWV HS H BS LOWP SP47. pose proof (so_facts _ _ _ _ _ _ HS) as HF. unfold s0_far in H.
  destruct (below_stack (s_facts st) wl (getr st X8)) eqn:B0; [left; pose proof (BS _ B0); lia|].
  destruct (KnownT.KnownT.known_leu_t (s_facts st) (getr st X8) (getr st X2)) eqn:K1; [left; exact (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF K1)|].
  right. pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF H) as X. rewrite den_sv_alu in X. cbn [alu64 alu den] in X.
  rewrite bv_add_unsigned, wbv_unsigned, wlit_ok in X. change (to_Z 16%uint63) with 16 in X. unfold bv_wrap in X. rewrite bv_modulus_64 in X.
  pose proof (bv_unsigned_in_range 64 (den E (getr st X2))) as R2. rewrite Z.mod_small in X by (unfold two64; lia). exact X.
Qed.

Section Walk.
Context {rc : RunConst.runConstT}.
Variable OPS : optable.

Lemma unw_classify_sound : forall E st ms mo hargs n md A nw rest wl (top LOWV : Z) prev frame,
  st_ok bsegs OPS E st ms mo -> heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest ->
  (forall wlo x, stack_window_key n rest = Some wlo -> x - bv_unsigned (den E (VP STACK_ID wlo)) <= SPALT -> x <= top) ->
  top <= 2 ^ 47 ->
  (forall v, below_stack (s_facts st) wl v = true -> bv_unsigned (den E v) < LOWV) -> LOWV <= bv_unsigned (den E prev) ->
  let P := bv_unsigned (den E prev) in let F := bv_unsigned (den E frame) in
  match unw_classify st hargs wl prev frame with
  | UCStop => ~ (P < F /\ F < top - 16 /\ F mod 8 = 0)
  | UCIn => P < F /\ F < top - 16 /\ F mod 8 = 0
  | UCMaybe => P < F /\ F mod 8 = 0
  | UCUnk => True
  end.
Proof.
  intros E st ms mo hargs n md A nw rest wl top LOWV prev frame HS Hn Eh TOPB T47 BS LOWP. cbv zeta.
  remember (bv_unsigned (den E prev)) as P eqn:EP. remember (bv_unsigned (den E frame)) as F eqn:EF0. unfold unw_classify.
  destruct (below_stack (s_facts st) wl frame) eqn:BSF.
  { pose proof (BS _ BSF) as X. rewrite <- EF0 in X. intros (Y & _). lia. }
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  destruct (KnownT.KnownT.decide_ltu_tt (s_facts st) prev frame) as [[|]|] eqn:D; [| | exact I].
  2:{ pose proof (proj1 (ltu_iff _ _ false) (KnownT.KnownT.decide_ltu_tt_sound E _ HF prev frame false D)) as X. rewrite <- EP, <- EF0 in X. intros (Y & _). lia. }
  pose proof (proj1 (ltu_iff _ _ true) (KnownT.KnownT.decide_ltu_tt_sound E _ HF prev frame true D)) as LT. rewrite <- EP, <- EF0 in LT.
  destruct (frame_al8 (s_facts st) frame) as [[|]|] eqn:AL; [| | exact I].
  2:{ pose proof (frame_al8_sound E _ frame false HF AL) as X. rewrite <- EF0 in X. intros (_ & _ & Y). apply X in Y. discriminate Y. }
  pose proof (proj1 (frame_al8_sound E _ frame true HF AL) eq_refl) as M8. rewrite <- EF0 in M8.
  destruct frame as [a|kf off| | | | | | | | |];
    try (destruct (altop_ok_v st hargs _ 17) eqn:AT; [| split; assumption];
         unfold altop_ok_v in AT; rewrite Hn, Eh in AT; discriminate AT).
  - destruct (Z.leb TOP47m16 (w2Z a)) eqn:TL; [| exact I]. apply Z.leb_le in TL. unfold TOP47m16 in TL.
    intros (_ & Y & _). rewrite EF0 in Y. cbn [den] in Y. rewrite wbv_unsigned in Y. lia.
  - destruct (altop_ok_v st hargs (VP kf off) 17) eqn:AT; [| split; assumption].
    destruct (altop_v_sound bsegs OPS E st ms mo hargs n md A nw rest _ 17 HS AT Hn Eh) as (wlo & len & SK & _ & LE).
    pose proof (TOPB wlo (F + 17) SK ltac:(rewrite EF0; lia)) as X. split; [exact LT|]. split; [lia| exact M8].
Qed.

Lemma unw_walk_sound : forall E st ms mo hargs n md A nw rest wl (top LOWV : Z) PCz,
  st_ok bsegs OPS E st ms mo -> heap_nwin hargs = Some n -> hargs = VL md :: A :: VL nw :: rest ->
  (forall wlo x, stack_window_key n rest = Some wlo -> x - bv_unsigned (den E (VP STACK_ID wlo)) <= SPALT -> x <= top) ->
  top <= 2 ^ 47 ->
  (forall v, below_stack (s_facts st) wl v = true -> bv_unsigned (den E v) < LOWV) ->
  forall fuel prev frame k cands, LOWV <= bv_unsigned (den E prev) ->
  unw_walk fuel st hargs wl PCz prev frame k = Some cands ->
  exists tr, In tr cands /\ uchain (ms_mem ms) top PCz (bv_unsigned (den E prev)) (bv_unsigned (den E frame)) k tr.
Proof.
  intros E st ms mo hargs n md A nw rest wl top LOWV PCz HS Hn Eh TOPB T47 BS.
  induction fuel as [|f IH]; intros prev frame k cands LOWP H; cbn [unw_walk] in H; [discriminate|].
  destruct k as [|k1].
  { injection H as <-. exists []. split; [left; reflexivity|]. apply uc_stop. intros (_ & _ & _ & X). lia. }
  pose proof (unw_classify_sound E st ms mo hargs n md A nw rest wl top LOWV prev frame HS Hn Eh TOPB T47 BS LOWP) as CL. cbv zeta in CL.
  set (P := bv_unsigned (den E prev)) in *. set (F := bv_unsigned (den E frame)) in *.
  destruct (unw_classify st hargs wl prev frame) eqn:UC.
  - injection H as <-. exists []. split; [left; reflexivity|]. apply uc_stop. intros (X1 & X2 & X3 & _). apply CL. auto.
  -
    destruct CL as (LT & TP & M8).
    destruct (frame_rec st frame) as [[fp [raw| | | | | | | | | |]]|] eqn:FRc; try discriminate.
    destruct frame as [|kf off| | | | | | | | |]; try (cbn in FRc; discriminate FRc).
    destruct (frame_rec_sound bsegs OPS E st ms mo kf off fp (VL raw) HS FRc) as (F16 & B16 & B8). fold F in F16, B16, B8.
    assert (ERA : den E (VL raw) = Z_to_bv 64 (w2Z raw)) by reflexivity. rewrite ERA in B8.
    pose proof (w2Z_range raw) as RR. unfold two64 in RR.
    assert (EFP : den E fp = Z_to_bv 64 (bv_unsigned (den E fp))) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite EFP in B16.
    pose proof (bv_unsigned_in_range 64 (den E fp)) as RF. unfold bv_modulus in RF.
    destruct (Z.ltb (w2Z raw) 4096) eqn:LOW.
    + injection H as <-. apply Z.ltb_lt in LOW. exists []. split; [left; reflexivity|].
      eapply uc_lowpc; eauto; lia.
    + apply Z.ltb_ge in LOW.
      destruct (unw_walk f st hargs wl PCz (VP kf off) fp (if w2Z raw =? PCz then S k1 else k1)) as [cands'|] eqn:W; [|discriminate].
      injection H as <-. destruct (IH (VP kf off) fp _ _ ltac:(subst P F; lia) W) as (tr' & IN' & UC').
      exists ((if w2Z raw =? PCz then [] else [w2Z raw]) ++ tr'). split; [apply in_map; exact IN'|].
      eapply uc_step; eauto; try lia.
  -
    destruct CL as (LT & M8).
    destruct (frame_rec st frame) as [[fp [raw| | | | | | | | | |]]|] eqn:FRc; try discriminate.
    destruct frame as [|kf off| | | | | | | | |]; try (cbn in FRc; discriminate FRc).
    destruct (frame_rec_sound bsegs OPS E st ms mo kf off fp (VL raw) HS FRc) as (F16 & B16 & B8). fold F in F16, B16, B8.
    assert (ERA : den E (VL raw) = Z_to_bv 64 (w2Z raw)) by reflexivity. rewrite ERA in B8.
    pose proof (w2Z_range raw) as RR. unfold two64 in RR.
    assert (EFP : den E fp = Z_to_bv 64 (bv_unsigned (den E fp))) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite EFP in B16.
    pose proof (bv_unsigned_in_range 64 (den E fp)) as RF. unfold bv_modulus in RF.
    destruct (Z.ltb (w2Z raw) 4096) eqn:LOW.
    + injection H as <-. apply Z.ltb_lt in LOW. exists []. split; [left; reflexivity|].
      destruct (Z_lt_le_dec F (top - 16)) as [TP|TP]; [eapply uc_lowpc; eauto; lia| apply uc_stop; intros (_ & X & _); lia].
    + apply Z.ltb_ge in LOW.
      destruct (unw_walk f st hargs wl PCz (VP kf off) fp (if w2Z raw =? PCz then S k1 else k1)) as [cands'|] eqn:W; [|discriminate].
      injection H as <-. destruct (IH (VP kf off) fp _ _ ltac:(subst P F; lia) W) as (tr' & IN' & UC').
      destruct (Z_lt_le_dec F (top - 16)) as [TP|TP].
      * exists ((if w2Z raw =? PCz then [] else [w2Z raw]) ++ tr'). split; [right; apply in_map; exact IN'|].
        eapply uc_step; eauto; try lia.
      * exists []. split; [left; reflexivity|]. apply uc_stop. intros (_ & X & _). lia.
  - discriminate H.
Qed.
End Walk.
End TwinB.
