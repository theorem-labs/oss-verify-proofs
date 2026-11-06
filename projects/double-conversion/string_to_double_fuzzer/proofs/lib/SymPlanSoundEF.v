(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg Nodes
  MmapSim AllocSim FileSim AgentLib ShapeLaws Spec LibWritev RefNodes RefExitBase LibCas LibCas2 Hoare Frame
  RefMemcpyLib RefMemcpyBase RefMemcpy SymExec
  MallocDefs RefEnframeBase RefEnframeArith RefEnframe RefGetMeta RefFreePro.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan SymSlots SymPlanSoundA SymPlanSound SymPlanSoundH.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S. Import SP. Import SSL. Import SPSA. Import SPS.

#[local] Abbreviation RSEGS := ImgP.M.loaded_segments.
Section NX0.
Variable nx0 : nat.
Context {fx : PropExec.FPState}.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
#[using="Type"] Lemma memF_out : forall (m : word -> option byte) idx n stride start off (x : word),
  0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= start -> start + stride < 2 ^ 64 ->
  ~ (start - 3 <= bv_unsigned x < start + 16 * off) ->
  ~ (start + 16 * off + n <= bv_unsigned x < start + stride - 4) ->
  memF m idx n stride start off x = m x.
Proof.
  intros m idx n stride start off x Hoff Hn Hstr Hst Hnw Hx1 Hx2.
  pose proof (u64_range x) as Hxr.
  Ltac miss1 := rewrite wbytes_miss;
    [ | rewrite ?length_wle2, ?length_wle4; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?u64_lit by lia; lia
      | rewrite ?length_wle2, ?length_wle4; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?u64_lit by lia; lia ].
  unfold memF, mF. miss1.
  unfold mE. cbv zeta.
  assert (D : mD start off m x = m x).
  { unfold mD. destruct (off =? 0) eqn:Eo; [reflexivity|]. apply Z.eqb_neq in Eo. miss1. miss1. miss1. reflexivity. }
  assert (E1 : mE1 idx stride start off (mD start off m) x = m x).
  { unfold mE1. miss1. miss1. exact D. }
  destruct (stride - 4 - n - 16 * off =? 0) eqn:Er; [exact E1|]. apply Z.eqb_neq in Er.
  destruct (stride - 4 - n - 16 * off <? 5) eqn:Er5.
  - apply Z.ltb_lt in Er5. miss1. exact E1.
  - apply Z.ltb_ge in Er5. miss1. miss1. miss1. exact E1.
Qed.

#[using="Type"] Lemma memF_grows : forall (m : word -> option byte) idx n stride start off,
  mem_grows m (memF m idx n stride start off).
Proof.
  intros. unfold memF. eapply mem_grows_trans; [| apply grows_mF].
  eapply mem_grows_trans; [apply grows_mD | apply grows_mE].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma env_agree_refl' : forall b E, env_agree b E E.
Proof. intros. split; [intros; reflexivity | reflexivity]. Qed.

#[using="Type"] Lemma env_agree_trans' : forall b E1 E2 E3, env_agree b E1 E2 -> env_agree b E2 E3 -> env_agree b E1 E3.
Proof. intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [intros n Hn; rewrite (A1 n Hn); apply A2; exact Hn | congruence]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cs_ok_bump1 : forall E cs R M model a,
  cs_ok E cs R M model -> fresh_ok nx0 cs = true ->
  cs_ok (ext1 E (s_next (c_ss cs)) a) (bump_next cs 1) R M model.
Proof.
  intros E cs R M model a HC Hf. unfold fresh_ok in Hf.
  apply andb_prop in Hf as [Hf Hnx]. apply andb_prop in Hf as [Hf Hslv]. apply andb_prop in Hf as [Hf Hmv].
  apply andb_prop in Hf as [Hsv Hkv].
  pose proof (ext1_agree E (s_next (c_ss cs)) a) as Hag.
  destruct HC as [HR HK HL Hh Hlz Hmt Hfd HV HSL HLIB].
  constructor; cbn [bump_next c_ss s_regs s_know s_log c_maps c_nmaps c_live c_slots].
  - eapply regs_ok_ext; [exact Hag | exact Hsv | exact HR].
  - eapply know_ok_ext; [exact Hag | exact Hkv | exact HK].
  - reflexivity.
  - exact Hh.
  - exact Hlz.
  - exact Hmt.
  - exact Hfd.
  - eapply vm_ok_ext; [exact Hag | exact Hmv | | exact HV].
    (* [comment removed for export] *) match goal with H : Nat.leb (Nat.max 1 nx0) _ = true |- _ => apply Nat.leb_le in H; exact (max1_le_0 _ _ H) | H : (Nat.max 1 nx0 <= _)%nat |- _ => exact (max1_le_0 _ _ H) end.
  - eapply slots_ok_ext; [exact Hag | exact Hslv | exact HSL].
  - exact HLIB.
Qed.

#[using="Type"] Lemma expr_vars_lt_mono : forall b b' e, (b <= b')%nat -> SP.expr_vars_lt b e = true -> SP.expr_vars_lt b' e = true.
Proof.
  intros b b' e Hle. induction e; cbn [SP.expr_vars_lt]; intros He; try reflexivity.
  - apply Nat.ltb_lt in He. apply Nat.ltb_lt. lia.
  - apply andb_prop in He as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply andb_prop in He as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply andb_prop in He as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply andb_prop in He as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - exact (IHe He).
Qed.

#[using="Type"] Lemma slots_vars_lt_mono : forall b b' ss, (b <= b')%nat -> slots_vars_lt b ss = true -> slots_vars_lt b' ss = true.
Proof.
  intros b b' ss Hle H. unfold slots_vars_lt in *. apply forallb_forall. intros x Hx.
  pose proof (proj1 (forallb_forall _ _) H x Hx) as Hs. unfold slot_vars_lt in *.
  repeat match goal with G : (_ && _)%bool = true |- _ => apply andb_prop in G; destruct G end.
  rewrite !(expr_vars_lt_mono b b') by assumption. reflexivity.
Qed.

#[using="Type"] Lemma rdn1_byte : forall (M : word -> option byte) (a : word) b, M a = Some b -> rdn RSEGS M a 1 = Some [b].
Proof. intros M a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_lit_words_ok : forall E (M : word -> option byte) sb sk idx stride n st,
  enframe_post M idx n stride st 0 ->
  bv_unsigned (edenot E sb) + sk = st -> 4 <= st -> st + stride < 2 ^ 64 -> 0 <= n -> n + 4 <= stride ->
  know_ok RSEGS E M (slot_lit_words sb sk idx stride n).
Proof.
  intros E M sb sk idx stride n st P Hsb Hst Hnw Hn0 Hn4.
  destruct P as [pp pe pr pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Pr]. cbn zeta in *. subst pp pe pr pq.
  replace (st + 16 * 0) with st in * by lia. replace (stride - 4 - n - 16 * 0) with (stride - 4 - n) in * by lia.
  replace (stride * idx / 16 + 0) with (stride * idx / 16) in * by lia.
  assert (AD : forall k, adenot E (SA sb k) = Z_to_bv 64 (st + (k - sk))).
  { intros k. rewrite adenot_Z. f_equal. lia. }
  assert (FL : forall k w, 0 <= st + (k - sk) -> st + (k - sk) + w <= 2 ^ 64 -> 0 < w -> flat E (SA sb k) w).
  { intros k w H1 H2 H3. unfold flat, estart. cbn [a_base a_off]. lia. }
  unfold slot_lit_words. cbv zeta.
  apply Forall_cons.
  { cbn [kentry_ok edenot]. split; [lia|]. split; [apply FL; lia|]. rewrite AD, w2lb1.
    replace (st + (sk - 3 - sk)) with (st - 3) by lia. apply rdn1_byte. exact Pm3. }
  apply Forall_cons.
  { cbn [kentry_ok edenot]. split; [lia|]. split; [apply FL; lia|]. rewrite AD.
    replace (st + (sk - 2 - sk)) with (st - 2) by lia. exact Pm2. }
  apply Forall_app. split.
  - destruct (0 <? stride - 4 - n) eqn:Er; [|constructor]. apply Z.ltb_lt in Er.
    apply Forall_one. cbn [kentry_ok edenot]. split; [lia|]. split; [apply FL; lia|]. rewrite AD, w2lb1.
    replace (st + (sk + n - sk)) with (st + n) by lia. apply rdn1_byte. apply Pzr. exact Er.
  - destruct (5 <=? stride - 4 - n) eqn:Er; [|constructor]. apply Z.leb_le in Er.
    apply Forall_cons.
    { cbn [kentry_ok edenot]. split; [lia|]. split; [apply FL; lia|]. rewrite AD, w2lb1.
      replace (st + (sk + stride - 4 - 5 - sk)) with (st + stride - 4 - 5) by lia. apply rdn1_byte. apply Pe5. exact Er. }
    apply Forall_one. cbn [kentry_ok edenot]. split; [lia|]. split; [apply FL; lia|]. rewrite AD.
    replace (st + (sk + stride - 4 - 4 - sk)) with (st + stride - 4 - 4) by lia. apply Pe4. exact Er.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma enframe_core : forall cs cs1 csa E E1 R R' M model T (ret : Z) (v nx1 : nat)
    (p sb pnb len1 len2 sde : expr) (sk pnk : Z) (k0 kl : list kentry) (s : sslot)
    (idx stride st n off : Z),
  let MF := memF M idx n stride st off in
  let ss := s :: slots_keep (kn cs) sb (sk - 4) sde (c_slots cs) in
  (forall E' R'' M', env_agree nx0 E E' -> cs_ok E' (set_slots csa ss) R'' M' model ->
      realizes RSEGS (cfg_of R'' (pc (set_slots csa ss)) M' model) T) ->
  after_call nx0 cs1 ret (Some p) (kl ++ kn_havoc (kn_havoc k0 sb (sk - 3) len1) pnb pnk len2) = Some csa ->
  cs_ok E1 cs1 R M model -> know_ok RSEGS E1 M (kn cs) -> slots_ok E1 M (c_slots cs) ->
  fresh_ok nx0 cs = true -> v = s_next (c_ss cs) -> s_next (c_ss cs1) = nx1 -> (v <= nx1)%nat ->
  env_agree v E E1 ->
  know_ok RSEGS E1 M k0 ->
  bv_unsigned (edenot E1 sb) + sk = st ->
  bv_unsigned (edenot E1 pnb) + pnk = st + 16 * off + n ->
  elenZ E1 len1 = 16 * off + 3 -> elenZ E1 len2 = stride - 4 - n - 16 * off -> elenZ E1 sde = stride ->
  edenot E1 p = Z_to_bv 64 (st + 16 * off) ->
  know_ok RSEGS E1 MF kl -> slot_ok E1 MF s -> slot_vars_lt nx1 s = true ->
  keeps_cs R R' -> getr R' 10%bv = Z_to_bv 64 (st + 16 * off) ->
  0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= st -> st + stride < 2 ^ 64 ->
  (st - 4 + stride <= 0x10000 \/ 0xe6000 <= st - 4) ->
  realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 ret) MF (seg_rom RSEGS)) model) T.
Proof.
  intros cs cs1 csa E E1 R R' M model T ret v nx1 p sb pnb len1 len2 sde sk pnk k0 kl s idx stride st n off MF ss
         HK Hac HC1 HK1 HSL1 Hfresh Hv Hnx1 Hvle Hag1 K0 SB PNB Elen1 Elen2 Esde Ep1 KL SLOT Hvsl Hkeeps HA0
         Hoff Hn0 Hfit Hst4 Hnw Himgh.
  (* [comment removed for export] *)
  set (M1 := fun x : word => if ((st - 3 <=? bv_unsigned x) && (bv_unsigned x <? st + 16 * off))%bool then MF x else M x).
  pose proof (memF_grows M idx n stride st off) as HgF. fold MF in HgF.
  assert (OUT : forall x : word, ~ (st - 3 <= bv_unsigned x < st + 16 * off) ->
                               ~ (st + 16 * off + n <= bv_unsigned x < st + stride - 4) -> MF x = M x).
  { intros x Hx1 Hx2. subst MF. apply memF_out; lia. }
  assert (K1 : know_ok RSEGS E1 M1 (kn_havoc k0 sb (sk - 3) len1)).
  { apply (know_ok_havoc E1 M M1 k0 sb (sk - 3) len1 K0).
    - intros x Hx. unfold estart in Hx. cbn [a_base a_off] in Hx. rewrite Elen1 in Hx. subst M1. cbv beta.
      destruct (Z.leb_spec (st - 3) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (st + 16 * off)); cbn [andb]; try reflexivity. lia.
    - intros x Hx. subst M1. cbv beta. destruct (_ && _)%bool; [apply HgF; exact Hx | exact Hx]. }
  assert (K2 : know_ok RSEGS E1 MF (kn_havoc (kn_havoc k0 sb (sk - 3) len1) pnb pnk len2)).
  { apply (know_ok_havoc E1 M1 MF _ pnb pnk len2 K1).
    - intros x Hx. unfold estart in Hx. cbn [a_base a_off] in Hx. rewrite PNB, Elen2 in Hx. subst M1. cbv beta.
      destruct (Z.leb_spec (st - 3) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (st + 16 * off)); cbn [andb]; try reflexivity;
        apply OUT; lia.
    - intros x Hx. subst M1. cbv beta in Hx. destruct (_ && _)%bool; [exact Hx | apply HgF; exact Hx]. }
  (* [comment removed for export] *)
  destruct (after_call_sound nx0 cs1 ret (Some p) _ csa E1 R R' M MF model ss Hac HC1) as [HC' Hpc'].
  - (* [comment removed for export] *)
    intros r Hr0 Hnin. apply (keeps_cs_getr R R' r Hkeeps).
    apply kept_of_not_caller_saved; [| exact Hr0 | exact Hnin].
    intros k Hk. cbn [In] in Hk. unfold callee_saved.
    repeat (destruct Hk as [<-|Hk]; [cbn [In Z.of_nat Pos.of_succ_nat Pos.succ];
      repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] end; fail | ]).
    all: try (destruct Hk).
  - (* [comment removed for export] *)
    rewrite Ep1. exact HA0.
  - (* [comment removed for export] *)
    apply Forall_app. split; [exact KL | exact K2].
  - (* [comment removed for export] *)
    apply Forall_cons; [exact SLOT|].
    eapply slots_keep_sound; [exact HK1 | exact HSL1 |].
    unfold estart. cbn [a_base a_off]. rewrite Esde. intros x Hx. apply OUT; lia.
  - (* [comment removed for export] *)
    rewrite Hnx1. subst ss. unfold slots_vars_lt. cbn [forallb]. fold (slots_vars_lt nx1 (slots_keep (kn cs) sb (sk - 4) sde (c_slots cs))).
    rewrite Hvsl. cbn [andb]. apply slots_vars_lt_keep. apply (slots_vars_lt_mono v nx1); [exact Hvle|].
    subst v. apply (fresh_ok_slots nx0). exact Hfresh.
  - (* [comment removed for export] *)
    eapply lib_ok_frame; [|exact (co_lib _ _ _ _ _ HC1)]. intros a Ha. unfold HULL_LO, HULL_HI in Ha; cbn in Ha.
    apply OUT; rewrite u64_lit by lia; lia.
  - (* [comment removed for export] *)
    rewrite <- Hpc'.
    apply (HK (ext_call E1 (s_next (c_ss cs1)) R') R' MF); [|exact HC'].
    apply (env_agree_trans' nx0 E E1).
    + eapply env_agree_le; [exact Hag1 | subst v; exact (fresh_ok_nx0 nx0 cs Hfresh)].
    + eapply env_agree_le; [apply ext_call_agree |]. rewrite Hnx1.
      pose proof (fresh_ok_nx0 nx0 cs Hfresh). subst v. lia.
Qed.

#[using="Type"] Theorem call_enframe_ok_fx : forall cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_enframe P0 -> call_enframe RSEGS P0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
   intros cs cs' E R M model T HC Hpc Hn HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_slots _ _ _ _ _ HC) as HSL.
  unfold call_enframe in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [idx|] eqn:H11; [|discriminate].
  cbv zeta in Hn.
  destruct (split_lit (reg cs 10)) as [gb gk] eqn:Hsg.
  destruct (kread8e RSEGS (kn cs) gb (gk + 16)) as [Me|] eqn:HMe; [|discriminate].
  destruct (kreadZ RSEGS (kn cs) gb (gk + 32) 8) as [W|] eqn:HW; [|discriminate].
  set (stride := slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W)) in Hn.
  set (start := mkAlu ALU_ADD Me (ELit (16 + stride * idx))) in Hn.
  destruct (split_lit start) as [sb sk] eqn:Hss.
  destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (ehi (kn cs) Me) as [mh|] eqn:Hmh; [|discriminate].
  set (shs := (stride - 4 - nlo) / 16) in Hn.
  set (symb := negb (shs =? 0)) in Hn.
  set (v := s_next (c_ss cs)) in Hn.
  set (offe := if symb then EVar v else ELit 0) in Hn.
  set (p := mkAlu ALU_ADD start (times16 offe)) in Hn.
  destruct (split_lit p) as [pb pk] eqn:Hsp.
  set (ne := reg cs 12) in *.
  set (pn := mkAlu ALU_ADD p ne) in Hn.
  destruct (split_lit pn) as [pnb pnk] eqn:Hspn.
  set (kf := if symb then [KRange (EVar v) 0 (Z.min 255 shs); KRange (mkAlu ALU_ADD (times16 (EVar v)) ne) nlo (stride - 4)] else []) in Hn.
  set (s := SL start (ELit stride) ne offe (ELit W) idx p) in Hn.
  set (nx1 := if symb then S v else v) in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  set (cs1 := if symb then bump_next cs 1 else cs) in Hn.
  set (len1 := mkAlu ALU_ADD (times16 offe) (ELit 3)) in Hn.
  set (len2 := mkAlu ALU_SUB (ELit (stride - 4)) (mkAlu ALU_ADD ne (times16 offe))) in Hn.
  set (k1 := kn_havoc (kf ++ kn cs) sb (sk - 3) len1) in Hn.
  set (k2 := kn_havoc k1 pnb pnk len2) in Hn.
  set (kl := if symb then [] else match ne with ELit n0 => slot_lit_words sb sk idx stride (n0 mod two64) | _ => [] end) in Hn.
  destruct (after_call nx0 cs1 ret (Some p) (kl ++ k2)) as [csa|] eqn:Hac; [|discriminate].
  lazymatch type of Hn with Some ?x = Some _ => assert (Ecs : cs' = x) by congruence end. clear Hn.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hvsl].
  apply andb_prop in Hcond as [Hcond Hvn]. apply andb_prop in Hcond as [Hcond Hvs].
  apply andb_prop in Hcond as [Hcond Hflpn]. apply andb_prop in Hcond as [Hcond Hflp].
  apply andb_prop in Hcond as [Hcond Himg]. apply andb_prop in Hcond as [Hcond Hrw].
  apply andb_prop in Hcond as [Hcond Hr4]. apply andb_prop in Hcond as [Hcond Hap].
  apply andb_prop in Hcond as [Hcond Hflg]. apply andb_prop in Hcond as [Hcond Hmhb].
  apply andb_prop in Hcond as [Hcond Hnhi4]. apply andb_prop in Hcond as [Hcond Hnlo0].
  apply andb_prop in Hcond as [Hcond Hal]. apply andb_prop in Hcond as [Hcond Hq].
  apply andb_prop in Hcond as [Hcond Hidx32]. apply andb_prop in Hcond as [Hcond Hidx0].
  apply andb_prop in Hcond as [Hcond Hm16]. apply andb_prop in Hcond as [Hcond H31].
  apply andb_prop in Hcond as [Hsc H16].
  apply Z.leb_le in H16. apply Z.ltb_lt in H31. apply Z.eqb_eq in Hm16. apply Z.leb_le in Hidx0. apply Z.ltb_lt in Hidx32.
  apply Z.leb_le in Hq. apply Z.leb_le in Hal. apply Z.leb_le in Hnlo0. apply Z.leb_le in Hnhi4. apply Z.leb_le in Hmhb.
  unfold two64 in Hmhb.
  assert (Hscp : (w_maplen W = 0 \/ w_lastidx W <> 0) -> w_sizeclass W < 48).
  { intros Hd. destruct (w_sizeclass W <? 48) eqn:E48; [apply Z.ltb_lt in E48; exact E48|].
    exfalso. destruct Hd as [Hd|Hd].
    - rewrite (proj2 (Z.eqb_eq _ _) Hd) in Hsc. cbn in Hsc. discriminate.
    - destruct (w_lastidx W =? 0) eqn:El; [apply Z.eqb_eq in El; lia|]. destruct (w_maplen W =? 0); cbn in Hsc; discriminate. }
  clear Hsc.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R M model ret HC Hret) as (R1 & Hrok & Hretr).
  destruct (reg_lit_sound E cs R M model 11 idx HC ltac:(lia) H11) as [R11 _].
  pose proof (reg_sound E cs R M model 10 HC ltac:(lia)) as R10.
  pose proof (reg_sound E cs R M model 12 HC ltac:(lia)) as R12. fold ne in R12.
  set (c := getr R (Z_to_bv 5 13)).
  set (nw := edenot E ne) in *. set (n := bv_unsigned nw). pose proof (u64_range nw) as Hnwr. fold n in Hnwr.
  pose proof (xlo_sound RSEGS E M (kn cs) ne nlo HKN Hnlo) as Hnlo'. fold nw n in Hnlo'.
  pose proof (xhi_sound RSEGS E M (kn cs) ne nhi HKN Hnhi) as Hnhi'. fold nw n in Hnhi'.
  (* [comment removed for export] *)
  pose proof (flat_b_sound E M (kn cs) gb gk 40 HKN Hflg) as Fg.
  set (g := bv_unsigned (edenot E gb) + gk) in *.
  assert (Hg40 : 0 <= g /\ g + 40 <= 2 ^ 64) by (unfold flat, estart in Fg; cbn [a_base a_off] in Fg; lia).
  assert (R10' : getr R (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 g) by (rewrite R10; exact (split_lit_denot E _ _ _ Hsg)).
  pose proof (kread8e_rdn E M (kn cs) gb (gk + 16) Me HKN HMe ltac:(eapply flat_sub; [exact Fg | lia | lia | lia])) as RM.
  rewrite adenot_Z in RM. replace (bv_unsigned (edenot E gb) + (gk + 16)) with (g + 16) in RM by lia.
  set (M0 := bv_unsigned (edenot E Me)). pose proof (u64_range (edenot E Me)) as HM0r. fold M0 in HM0r.
  destruct (kreadZ_rdn E M (kn cs) gb (gk + 32) 8 W HKN HW ltac:(lia) ltac:(eapply flat_sub; [exact Fg | lia | cbn; lia | cbn; lia])) as [RW HWr].
  rewrite adenot_Z in RW. replace (bv_unsigned (edenot E gb) + (gk + 32)) with (g + 32) in RW by lia. unfold two64 in HWr.
  pose proof (ehi_sound E M (kn cs) Me mh HKN Hmh) as Hmh'. fold M0 in Hmh'.
  (* [comment removed for export] *)
  set (st := M0 + 16 + stride * idx).
  assert (Hsidx : 0 <= stride * idx) by nia.
  assert (Est : edenot E start = Z_to_bv 64 st).
  { subst start. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. subst st M0. f_equal. lia. }
  assert (Ust : bv_unsigned (edenot E start) = st) by (rewrite Est; apply u64_lit; lia).
  (* [comment removed for export] *)
  destruct (rw_okb_sound E M (kn cs) sb (sk - 4) stride HKN Hrw ltac:(lia)) as (OKh & DEFh & IMGh & H0h & Hnwh).
  pose proof (split_lit_denot E start sb sk Hss) as Esb. rewrite Est in Esb.
  assert (SB : bv_unsigned (edenot E sb) + sk = st).
  { apply (f_equal bv_unsigned) in Esb. rewrite !u64_lit in Esb by lia. lia. }
  replace (bv_unsigned (edenot E sb) + (sk - 4)) with (st - 4) in OKh, DEFh, IMGh, H0h, Hnwh by lia.
  replace (Z_to_bv 64 (bv_unsigned (edenot E sb) + (sk - 4))) with (Z_to_bv 64 (st - 4) : word) in OKh by (f_equal; lia).
  (* [comment removed for export] *)
  destruct (kreadZ RSEGS (kn cs) sb (sk - 4) 1) as [z4|] eqn:Hz4; [|discriminate]. destruct z4; try discriminate. clear Hr4.
  destruct (kreadZ_rdn E M (kn cs) sb (sk - 4) 1 0 HKN Hz4 ltac:(lia) ltac:(unfold flat, estart; cbn [a_base a_off]; lia)) as [R4r _].
  rewrite adenot_Z, w2lb1 in R4r. replace (bv_unsigned (edenot E sb) + (sk - 4)) with (st - 4) in R4r by lia.
  assert (R4 : M (Z_to_bv 64 (st - 4)) = Some (Z_to_bv 8 0)).
  { pose proof (DEFh 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0. cbn [rdn] in R4r.
    destruct (M (Z_to_bv 64 (st - 4))) as [b4|]; [|exfalso; apply D0; reflexivity].
    cbn in R4r. congruence. }
  clear R4r.
  (* [comment removed for export] *)
  destruct (M (Z_to_bv 64 (st - 3))) as [b3|] eqn:HM3.
  2:{ exfalso. apply (DEFh 1 ltac:(lia)). replace (st - 4 + 1) with (st - 3) by lia. exact HM3. }
  pose proof (u8_range b3) as Hb3.
  destruct (rdn_defined M (st - 2) 2 ltac:(lia) ltac:(cbn; lia)
              ltac:(intros i Hi; replace (st - 2 + i) with (st - 4 + (2 + i)) by lia; apply DEFh; cbn in Hi; lia)) as (bs2 & Hbs2 & Hlen2).
  set (o16 := bytes_le_to_Z bs2).
  pose proof (bytes_le_to_Z_bound bs2) as Ho16. rewrite Hlen2 in Ho16. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul] in Ho16. fold o16 in Ho16.
  (* [comment removed for export] *)
  assert (OK3 : store_ok RSEGS M (Z_to_bv 64 (st - 3)) (Z.to_nat (stride - 1)) = true).
  { eapply (store_ok_sub RSEGS M (Z_to_bv 64 (st - 4)) _ (Z.to_nat stride)); rewrite ?u64_lit by lia; rewrite ?Z2Nat.id by lia; try lia. exact OKh. }
  (* [comment removed for export] *)
  assert (TBL : sc_tbl_clear M).
  { rewrite DSC_eq in Himg. unfold kimg_covers in Himg. apply existsb_exists in Himg as (K & HinK & HKb).
    destruct K as [| | |ilo ihi| | | |]; try discriminate. apply andb_prop in HKb as [Hil Hih].
    apply Z.leb_le in Hil. apply Z.leb_le in Hih.
    pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKi. cbn [kentry_ok] in HKi. destruct HKi as (_ & _ & Hnone).
    intros j Hj. apply Hnone. unfold SCT. lia. }
  (* [comment removed for export] *)
  pose proof (ranges_apart_sound RSEGS E M (kn cs) gb (gk + 16) 8 sb (sk - 3) (stride - 1) HKN Hap) as Hdisj.
  unfold estart in Hdisj. cbn [a_base a_off] in Hdisj.
  (* [comment removed for export] *)
  destruct (ealign_sound RSEGS E M (kn cs) start HKN) as [Heal Hdiv]. rewrite Ust in Hdiv.
  assert (Hst16 : st mod 16 = 0).
  { apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdiv].
    exists (2 ^ (ealign (kn cs) start - 4)). change 16 with (2 ^ 4). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  (* [comment removed for export] *)
  set (off := enframe_off (slack_of stride n) ((if bv_unsigned b3 =? 0 then bv_unsigned c else o16 + 1) mod 256)).
  assert (EF : efH M c g M0 W idx n (bv_unsigned b3) o16 stride st off).
  { constructor.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact Hg40.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hscp.
    - exact H31.
    - exact Hq.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite RM. subst M0. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exact RW.
    - exact R4.
    - rewrite Z_to_bv_bv_unsigned. exact HM3.
    - intros _. rewrite Hbs2. subst o16. rewrite word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
    - exact OK3.
    - exact TBL. }
  pose proof (off_facts M c g M0 W idx n (bv_unsigned b3) o16 stride st off EF) as (Ooff & O255 & O16 & Oslack).
  assert (R12' : getr R (Z_to_bv 5 (Z.of_nat 12)) = Z_to_bv 64 n) by (rewrite R12; symmetry; apply Z_to_bv_bv_unsigned).
  destruct (enframe_run M c g M0 W idx n (bv_unsigned b3) o16 stride st off EF R (seg_rom RSEGS) (Z_to_bv 64 ret)
              R1 Hrok R10' R11 R12' eq_refl) as (R' & Hms & Hkeeps & HA0).
  pose proof (post_memF M c g M0 W idx n (bv_unsigned b3) o16 stride st off EF) as POST.
  set (MF := memF M idx n stride st off) in *.
  (* [comment removed for export] *)
  unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_enframe P0)) with (0x998fc%bv : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |]. clear Hms.
  (* [comment removed for export] *)
  assert (Hslack : slack_of stride n <= shs).
  { subst shs. unfold slack_of, IB, UNIT. apply Z.div_le_mono; lia. }
  set (offw := (Z_to_bv 64 off : word)).
  set (E1 := if symb then ext1 E v offw else E).
  assert (Hag1 : env_agree v E E1) by (subst E1; destruct symb; [apply ext1_agree | apply env_agree_refl']).
  assert (HC1 : cs_ok E1 cs1 R M model).
  { subst E1 cs1. destruct symb; [apply cs_ok_bump1; [exact HC | exact Hfresh] | exact HC]. }
  assert (Hnx1 : s_next (c_ss cs1) = nx1).
  { subst cs1 nx1. destruct symb; [cbn [bump_next c_ss s_next]; subst v; apply Nat.add_1_r | reflexivity]. }
  assert (Eoffe : edenot E1 offe = offw).
  { subst E1 offe offw. destruct symb eqn:Hsy.
    - apply ext1_at.
    - cbn [edenot]. f_equal. subst symb. apply negb_false_iff in Hsy. apply Z.eqb_eq in Hsy. lia. }
  assert (Estart1 : edenot E1 start = Z_to_bv 64 st).
  { rewrite <- (edenot_agree v E E1 start Hag1) by (rewrite <- expr_vars_lt_eq; exact Hvs). exact Est. }
  assert (Ene1 : edenot E1 ne = nw).
  { rewrite <- (edenot_agree v E E1 ne Hag1) by (rewrite <- expr_vars_lt_eq; exact Hvn). reflexivity. }
  assert (Esb1 : edenot E1 sb = edenot E sb).
  { symmetry. apply (edenot_agree v E E1 sb Hag1). rewrite <- expr_vars_lt_eq. eapply split_lit_vars; [exact Hss | exact Hvs]. }
  assert (Hoffw : bv_unsigned offw = off) by (subst offw; apply u64_lit; lia).
  assert (Etimes : edenot E1 (times16 offe) = Z_to_bv 64 (16 * off)) by (rewrite times16_denot, Eoffe, Hoffw; reflexivity).
  assert (Ep1 : edenot E1 p = Z_to_bv 64 (st + 16 * off)).
  { subst p. rewrite mkAlu_denot, alu_add, Estart1, Etimes. unfold v_add. rewrite !u64_lit by lia. reflexivity. }
  assert (Epn1 : edenot E1 pn = Z_to_bv 64 (st + 16 * off + n)).
  { subst pn. rewrite mkAlu_denot, alu_add, Ep1, Ene1. unfold v_add. rewrite u64_lit by lia. reflexivity. }
  assert (Elen1 : elenZ E1 len1 = 16 * off + 3).
  { unfold elenZ. subst len1. rewrite mkAlu_denot, alu_add, Etimes. cbn [edenot]. unfold v_add.
    rewrite (u64_lit (16 * off)), (u64_lit 3) by lia. apply u64_lit. lia. }
  assert (Elen2 : elenZ E1 len2 = stride - 4 - n - 16 * off).
  { unfold elenZ. subst len2. rewrite mkAlu_denot, alu_sub. cbn [edenot]. rewrite mkAlu_denot, alu_add, Ene1, Etimes.
    unfold v_sub, v_add. fold n. rewrite (u64_lit (16 * off)), (u64_lit (stride - 4)) by lia.
    rewrite (u64_lit (n + 16 * off)) by lia. rewrite u64_lit by lia. lia. }
  assert (Hn_eq : bv_unsigned nw = n) by reflexivity.
  (* [comment removed for export] *)
  assert (HK1 : know_ok RSEGS E1 M (kn cs)).
  { pose proof (co_know _ _ _ _ _ HC1) as X. subst cs1. destruct symb; exact X. }
  assert (HSL1 : slots_ok E1 M (c_slots cs)).
  { pose proof (co_slots _ _ _ _ _ HC1) as X. subst cs1. destruct symb; exact X. }
  assert (Hkf : know_ok RSEGS E1 M kf).
  { pose proof Eoffe as Eo. subst kf offe. destruct symb; [|constructor].
    apply Forall_cons; [|apply Forall_one]; cbn [kentry_ok].
    - rewrite Eo, Hoffw. lia.
    - rewrite mkAlu_denot, alu_add, times16_denot, Eo, Hoffw, Ene1. unfold v_add.
      rewrite (u64_lit (16 * off)) by lia. rewrite Hn_eq. rewrite u64_lit by lia. lia. }
  assert (K0 : know_ok RSEGS E1 M (kf ++ kn cs)) by (apply Forall_app; split; [exact Hkf | exact HK1]).
  (* [comment removed for export] *)
  assert (PB : bv_unsigned (edenot E1 pb) + pk = st + 16 * off).
  { pose proof (flat_b_sound E1 M (kf ++ kn cs) pb pk 1 K0 Hflp) as F. unfold flat, estart in F. cbn [a_base a_off] in F.
    pose proof (split_lit_denot E1 p pb pk Hsp) as X. rewrite Ep1 in X. apply (f_equal bv_unsigned) in X.
    rewrite !u64_lit in X by lia. lia. }
  assert (PNB : bv_unsigned (edenot E1 pnb) + pnk = st + 16 * off + n).
  { pose proof (flat_b_sound E1 M (kf ++ kn cs) pnb pnk 1 K0 Hflpn) as F. unfold flat, estart in F. cbn [a_base a_off] in F.
    pose proof (split_lit_denot E1 pn pnb pnk Hspn) as X. rewrite Epn1 in X. apply (f_equal bv_unsigned) in X.
    rewrite !u64_lit in X by lia. lia. }
  assert (KL : know_ok RSEGS E1 MF kl).
  { subst kl. destruct symb eqn:Hsy; [constructor|].
    assert (Hoff0 : off = 0).
    { subst symb. apply negb_false_iff in Hsy. apply Z.eqb_eq in Hsy. lia. }
    destruct ne as [n0| | | | | | |] eqn:Hne; try (apply Forall_nil).
    assert (Hn0 : n = n0 mod two64).
    { rewrite <- Hn_eq. subst nw. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. }
    rewrite <- Hn0. apply (slot_lit_words_ok E1 MF sb sk idx stride n st); try lia.
    - rewrite <- Hoff0. exact POST.
    - rewrite Esb1. exact SB. }
  assert (SLOT : slot_ok E1 MF s).
  { unfold slot_ok. subst s. cbn [sl_start sl_stride sl_n sl_off sl_W sl_idx sl_p]. rewrite Hss, Hsp.
    unfold uE. rewrite Estart1, Ene1, Eoffe, Ep1, Hn_eq, Hoffw. cbn [edenot].
    rewrite (u64_lit st), (u64_lit stride), (u64_lit W), (u64_lit (st + 16 * off)) by lia.
    rewrite Esb1.
    split; [exact POST|]. split; [reflexivity|]. split; [exact SB|]. split; [exact PB|].
    split; [reflexivity|]. split; [exact Hscp|]. repeat split; lia. }
  subst cs' k1 k2.
  apply (enframe_core cs cs1 csa E E1 R R' M model T ret v nx1 p sb pnb len1 len2 (ELit stride) sk pnk (kf ++ kn cs) kl s
           idx stride st n off HK Hac HC1 HK1 HSL1 Hfresh eq_refl Hnx1); try assumption; try lia.
  - subst nx1. destruct symb; lia.
  - rewrite Esb1. exact SB.
  - unfold elenZ. cbn [edenot]. apply u64_lit. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[using="Type"] Lemma W_fields : forall S c, 1 <= S -> 0 <= c < 4096 -> c mod 32 = 0 ->
  w_maplen (4096 * S + c) = S /\ w_lastidx (4096 * S + c) = 0
  /\ slot_stride (w_maplen (4096 * S + c)) (w_lastidx (4096 * S + c)) (w_sizeclass (4096 * S + c)) = 4096 * S - 16.
Proof.
  intros S c HS Hc Hc32. unfold w_maplen, w_lastidx.
  assert (A : (4096 * S + c) / 4096 = S) by lia.
  assert (B : (4096 * S + c) mod 32 = 0) by lia.
  rewrite A, B. split; [reflexivity|]. split; [reflexivity|].
  unfold slot_stride, UNIT. destruct (S =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|]. cbn [negb andb Z.eqb]. lia.
Qed.

#[using="Type"] Lemma stride_mod16 : forall S, (4096 * S - 16) mod 16 = 0.
Proof. intros. lia. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[using="Type"] Lemma decode_W_sound : forall E We Se c,
  decode_W We = Some (Se, c) -> 4096 * bv_unsigned (edenot E Se) + 4096 <= 2 ^ 64 ->
  bv_unsigned (edenot E We) = 4096 * bv_unsigned (edenot E Se) + c /\ 0 <= c < 4096.
Proof.
  intros E We Se c H Hb. unfold decode_W in H.
  destruct We as [w|i|op a b|opw aw bw|op a b|opmw am bm|sx lo nn ee|sx kk ii nn]; try discriminate.
  - injection H as <- <-. cbn [edenot]. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64.
    pose proof (Z.mod_pos_bound w (2 ^ 64) ltac:(lia)) as Hw.
    rewrite (Z.mod_small (w mod 2 ^ 64 / 4096)).
    2:{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    pose proof (Z.div_mod (w mod 2 ^ 64) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (w mod 2 ^ 64) 4096 ltac:(lia)). lia.
  - destruct op; try discriminate. destruct a as [| | | |op2 a1 a2| | |]; try discriminate.
    destruct op2; try discriminate. destruct a1 as [z| | | | | | |]; try discriminate.
    destruct z; try discriminate. repeat (destruct p; try discriminate).
    destruct b as [c'| | | | | | |]; try discriminate.
    destruct (Z.leb 0 c' && Z.ltb c' 4096)%bool eqn:Hc; [|discriminate]. injection H as <- <-.
    apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    cbn [edenot]. rewrite alu_add. unfold v_add. rewrite u_mul64. rewrite (u64_lit 4096) by lia.
    rewrite (Z.mod_small (4096 * _)) by (pose proof (u64_range (edenot E a2)); lia).
    rewrite (u64_lit c') by lia. rewrite u64_lit by (pose proof (u64_range (edenot E a2)); lia). lia.
  - destruct op; try discriminate. destruct a as [z| | | | | | |]; try discriminate.
    destruct z; try discriminate. repeat (destruct p; try discriminate). injection H as <- <-.
    cbn [edenot]. rewrite u_mul64. rewrite (u64_lit 4096) by lia.
    rewrite Z.mod_small by (pose proof (u64_range (edenot E b)); lia). lia.
Qed.

#[using="Type"] Lemma stride_e_denot : forall E Se, 1 <= bv_unsigned (edenot E Se) -> 4096 * bv_unsigned (edenot E Se) <= 2 ^ 64 ->
  edenot E (mkAlu ALU_ADD (mkMd M_MUL (ELit 4096) Se) (ELit (-16))) = Z_to_bv 64 (4096 * bv_unsigned (edenot E Se) - 16).
Proof.
  intros E Se H1 H2. rewrite mkAlu_denot, alu_add, mkMd_denot. unfold v_add. rewrite u_mul64. cbn [edenot].
  rewrite (u64_lit 4096) by lia. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  destruct (Z.eq_dec (4096 * bv_unsigned (edenot E Se)) (2 ^ 64)) as [E64|N64].
  - rewrite E64. rewrite Z_mod_same_full. change ((-16) mod 2 ^ 64) with (2 ^ 64 - 16). reflexivity.
  - rewrite (Z.mod_small (4096 * _)) by lia. change ((-16) mod 2 ^ 64) with (2 ^ 64 - 16).
    replace (4096 * bv_unsigned (edenot E Se) + (2 ^ 64 - 16)) with ((4096 * bv_unsigned (edenot E Se) - 16) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rw_okb_x_sound : forall E M k b off ne,
  know_ok RSEGS E M k -> rw_okb_x P0 k b off ne = true ->
  let a := bv_unsigned (edenot E b) + off in
  let N := elenZ E ne in
  (forall m, Z.of_nat m <= N -> store_ok RSEGS M (Z_to_bv 64 a) m = true)
  /\ (forall i, 0 <= i < N -> M (Z_to_bv 64 (a + i)) <> None)
  /\ (a + N <= 0x10000 \/ 0xe6000 <= a)
  /\ 0 <= a /\ a + N <= 2 ^ 64.
Proof.
  intros E M k b off ne HK H. rewrite rw_okb_x_eq in H. apply andb_prop in H as [Hw Hoff]. cbv zeta.
  destruct (kwritable_x_sound E M k k b off ne HK HK Hw) as (Hst & F1 & F2).
  rewrite off_image_x_eq, ISPAN_eq in Hoff. pose proof (ranges_apart_x_sound RSEGS E M k _ _ _ _ _ _ HK Hoff) as Himg.
  unfold estart in Himg. cbn [a_base a_off edenot] in Himg. rewrite elenZ_lit in Himg. rewrite u64_lit in Himg by lia.
  2:{ lia. }
  change (57344 mod 2 ^ 64) with 57344 in Himg.
  pose proof (u64_range (edenot E ne)) as Hnr. unfold elenZ in *.
  split; [exact Hst|]. split; [|lia].
  intros i Hi.
  pose proof (Hst (Z.to_nat (bv_unsigned (edenot E ne))) ltac:(rewrite Z2Nat.id by lia; lia)) as Hst'.
  pose proof (store_ok_all RSEGS M (Z.to_nat (bv_unsigned (edenot E ne))) (Z_to_bv 64 (bv_unsigned (edenot E b) + off))
                ltac:(rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia) Hst'
                (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) ltac:(rewrite !u64_lit by lia; rewrite Z2Nat.id by lia; lia)) as Wv.
  intros HM. apply Wv. apply wview_off_image; [|exact HM]. rewrite u64_lit by lia. lia.
Qed.

#[using="Type"] Theorem call_enframe_x_ok_fx : forall cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_enframe P0 -> call_enframe_x RSEGS P0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
   intros cs cs' E R M model T HC Hpc Hn HK.
  pose proof (co_know _ _ _ _ _ HC) as HKN. pose proof (co_slots _ _ _ _ _ HC) as HSL.
  unfold call_enframe_x in Hn.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [idx|] eqn:H11; [|discriminate].
  destruct idx; try discriminate.
  cbv zeta in Hn.
  destruct (split_lit (reg cs 10)) as [gb gk] eqn:Hsg.
  destruct (kread8e RSEGS (kn cs) gb (gk + 16)) as [Me|] eqn:HMe; [|discriminate].
  destruct (kread8e RSEGS (kn cs) gb (gk + 32)) as [We|] eqn:HWe; [|discriminate].
  destruct (decode_W We) as [[Se c]|] eqn:HdW; [|discriminate].
  cbv zeta in Hn.
  set (strideE := mkAlu ALU_ADD (mkMd M_MUL (ELit 4096) Se) (ELit (-16))) in Hn.
  set (start := mkAlu ALU_ADD Me (ELit 16)) in Hn.
  destruct (split_lit start) as [sb sk] eqn:Hss.
  set (ne := reg cs 12) in *.
  destruct (xlo (kn cs) ne) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) ne) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (ehi (kn cs) Me) as [mh|] eqn:Hmh; [|discriminate].
  destruct (xlo (kn cs) Se) as [Slo|] eqn:HSlo; [|discriminate].
  destruct (xhi (kn cs) Se) as [Shi|] eqn:HShi; [|discriminate].
  cbv zeta in Hn.
  set (shi := 4096 * Shi - 16) in Hn.
  set (shs := (shi - 4 - nlo) / 16) in Hn.
  set (v := s_next (c_ss cs)) in Hn.
  set (offe := EVar v) in Hn.
  set (p := mkAlu ALU_ADD start (times16 offe)) in Hn.
  destruct (split_lit p) as [pb pk] eqn:Hsp.
  set (pn := mkAlu ALU_ADD p ne) in Hn.
  destruct (split_lit pn) as [pnb pnk] eqn:Hspn.
  set (rexp := mkAlu ALU_SUB strideE (mkAlu ALU_ADD ne (times16 offe))) in Hn.
  set (kf := [KRange offe 0 (Z.min 255 shs); KRange rexp 4 (shi - nlo)]) in Hn.
  set (s := SL start strideE ne offe We 0 p) in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  set (cs1 := bump_next cs 1) in Hn.
  set (len1 := mkAlu ALU_ADD (times16 offe) (ELit 3)) in Hn.
  set (len2 := mkAlu ALU_ADD rexp (ELit (-4))) in Hn.
  set (k1 := kn_havoc (kf ++ kn cs) sb (sk - 3) len1) in Hn.
  set (k2 := kn_havoc k1 pnb pnk len2) in Hn.
  destruct (after_call nx0 cs1 ret (Some p) k2) as [csa|] eqn:Hac; [|discriminate].
  lazymatch type of Hn with Some ?x = Some _ => assert (Ecs : cs' = x) by congruence end. clear Hn.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hvsl].
  apply andb_prop in Hcond as [Hcond HvW]. apply andb_prop in Hcond as [Hcond Hvstr].
  apply andb_prop in Hcond as [Hcond Hvn]. apply andb_prop in Hcond as [Hcond Hvs].
  apply andb_prop in Hcond as [Hcond Hflpn]. apply andb_prop in Hcond as [Hcond Hflp].
  apply andb_prop in Hcond as [Hcond Himg]. apply andb_prop in Hcond as [Hcond Hrw].
  apply andb_prop in Hcond as [Hcond Hr4]. apply andb_prop in Hcond as [Hcond Hap].
  apply andb_prop in Hcond as [Hcond Hflg]. apply andb_prop in Hcond as [Hcond Hmhb].
  apply andb_prop in Hcond as [Hcond Hge]. apply andb_prop in Hcond as [Hcond Hnlo0].
  apply andb_prop in Hcond as [Hcond Hal]. apply andb_prop in Hcond as [Hcond HShi19].
  apply andb_prop in Hcond as [Hc32 HSlo1].
  apply Z.eqb_eq in Hc32. apply Z.leb_le in HSlo1. apply Z.leb_le in HShi19. apply Z.leb_le in Hal.
  apply Z.leb_le in Hnlo0. apply Z.leb_le in Hmhb. unfold two64 in Hmhb.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R M model ret HC Hret) as (R1 & Hrok & Hretr).
  destruct (reg_lit_sound E cs R M model 11 0 HC ltac:(lia) H11) as [R11 _].
  pose proof (reg_sound E cs R M model 10 HC ltac:(lia)) as R10.
  pose proof (reg_sound E cs R M model 12 HC ltac:(lia)) as R12. fold ne in R12.
  set (c13 := getr R (Z_to_bv 5 13)).
  set (nw := edenot E ne) in *. set (n := bv_unsigned nw). pose proof (u64_range nw) as Hnwr. fold n in Hnwr.
  pose proof (xlo_sound RSEGS E M (kn cs) ne nlo HKN Hnlo) as Hnlo'. fold nw n in Hnlo'.
  pose proof (xhi_sound RSEGS E M (kn cs) ne nhi HKN Hnhi) as Hnhi'. fold nw n in Hnhi'.
  (* [comment removed for export] *)
  set (Sv := bv_unsigned (edenot E Se)).
  pose proof (xlo_sound RSEGS E M (kn cs) Se Slo HKN HSlo) as HSlo'. fold Sv in HSlo'.
  pose proof (xhi_sound RSEGS E M (kn cs) Se Shi HKN HShi) as HShi'. fold Sv in HShi'.
  set (stride := 4096 * Sv - 16).
  assert (Estr : edenot E strideE = Z_to_bv 64 stride) by (subst strideE stride Sv; apply stride_e_denot; lia).
  assert (Ustr : bv_unsigned (edenot E strideE) = stride) by (rewrite Estr; apply u64_lit; lia).
  (* [comment removed for export] *)
  pose proof (flat_b_sound E M (kn cs) gb gk 40 HKN Hflg) as Fg.
  set (g := bv_unsigned (edenot E gb) + gk) in *.
  assert (Hg40 : 0 <= g /\ g + 40 <= 2 ^ 64) by (unfold flat, estart in Fg; cbn [a_base a_off] in Fg; lia).
  assert (R10' : getr R (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 g) by (rewrite R10; exact (split_lit_denot E _ _ _ Hsg)).
  pose proof (kread8e_rdn E M (kn cs) gb (gk + 16) Me HKN HMe ltac:(eapply flat_sub; [exact Fg | lia | lia | lia])) as RM.
  rewrite adenot_Z in RM. replace (bv_unsigned (edenot E gb) + (gk + 16)) with (g + 16) in RM by lia.
  set (M0 := bv_unsigned (edenot E Me)). pose proof (u64_range (edenot E Me)) as HM0r. fold M0 in HM0r.
  pose proof (kread8e_rdn E M (kn cs) gb (gk + 32) We HKN HWe ltac:(eapply flat_sub; [exact Fg | lia | lia | lia])) as RW.
  rewrite adenot_Z in RW. replace (bv_unsigned (edenot E gb) + (gk + 32)) with (g + 32) in RW by lia.
  set (W := bv_unsigned (edenot E We)). pose proof (u64_range (edenot E We)) as HWr. fold W in HWr.
  destruct (decode_W_sound E We Se c HdW ltac:(fold Sv; lia)) as [HWdec Hc]. fold W Sv in HWdec.
  destruct (W_fields Sv c ltac:(lia) Hc Hc32) as (Hml & Hli & Hss_stride). rewrite <- HWdec in Hml, Hli, Hss_stride.
  pose proof (ehi_sound E M (kn cs) Me mh HKN Hmh) as Hmh'. fold M0 in Hmh'.
  (* [comment removed for export] *)
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HKN Hge) as Hge'. cbn [xt_den] in Hge'. rewrite Ustr in Hge'.
  fold nw in Hge'. fold n in Hge'.
  (* [comment removed for export] *)
  set (st := M0 + 16).
  assert (Est : edenot E start = Z_to_bv 64 st).
  { subst start. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. subst st M0. reflexivity. }
  assert (Ust : bv_unsigned (edenot E start) = st) by (rewrite Est; apply u64_lit; lia).
  (* [comment removed for export] *)
  destruct (rw_okb_x_sound E M (kn cs) sb (sk - 4) strideE HKN Hrw) as (OKh & DEFh & IMGh & H0h & Hnwh).
  unfold elenZ in OKh, DEFh, IMGh, Hnwh. rewrite Ustr in OKh, DEFh, IMGh, Hnwh.
  pose proof (split_lit_denot E start sb sk Hss) as Esb. rewrite Est in Esb.
  assert (SB : bv_unsigned (edenot E sb) + sk = st).
  { apply (f_equal bv_unsigned) in Esb. rewrite !u64_lit in Esb by lia. lia. }
  replace (bv_unsigned (edenot E sb) + (sk - 4)) with (st - 4) in OKh, DEFh, IMGh, H0h, Hnwh by lia.
  (* [comment removed for export] *)
  destruct (kreadZ RSEGS (kn cs) sb (sk - 4) 1) as [z4|] eqn:Hz4; [|discriminate]. destruct z4; try discriminate. clear Hr4.
  destruct (kreadZ_rdn E M (kn cs) sb (sk - 4) 1 0 HKN Hz4 ltac:(lia) ltac:(unfold flat, estart; cbn [a_base a_off]; lia)) as [R4r _].
  rewrite adenot_Z, w2lb1 in R4r. replace (bv_unsigned (edenot E sb) + (sk - 4)) with (st - 4) in R4r by lia.
  assert (R4 : M (Z_to_bv 64 (st - 4)) = Some (Z_to_bv 8 0)).
  { pose proof (DEFh 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0. cbn [rdn] in R4r.
    destruct (M (Z_to_bv 64 (st - 4))) as [b4|]; [|exfalso; apply D0; reflexivity].
    cbn in R4r. congruence. }
  clear R4r.
  (* [comment removed for export] *)
  destruct (M (Z_to_bv 64 (st - 3))) as [b3|] eqn:HM3.
  2:{ exfalso. apply (DEFh 1 ltac:(lia)). replace (st - 4 + 1) with (st - 3) by lia. exact HM3. }
  pose proof (u8_range b3) as Hb3.
  destruct (rdn_defined M (st - 2) 2 ltac:(lia) ltac:(cbn; lia)
              ltac:(intros i Hi; replace (st - 2 + i) with (st - 4 + (2 + i)) by lia; apply DEFh; cbn in Hi; lia)) as (bs2 & Hbs2 & Hlen2).
  set (o16 := bytes_le_to_Z bs2).
  pose proof (bytes_le_to_Z_bound bs2) as Ho16. rewrite Hlen2 in Ho16. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul] in Ho16. fold o16 in Ho16.
  assert (OK3 : store_ok RSEGS M (Z_to_bv 64 (st - 3)) (Z.to_nat (stride - 1)) = true).
  { eapply (store_ok_sub RSEGS M (Z_to_bv 64 (st - 4)) _ (Z.to_nat stride)); rewrite ?u64_lit by lia; rewrite ?Z2Nat.id by lia; try lia.
    apply OKh. rewrite Z2Nat.id by lia. lia. }
  assert (TBL : sc_tbl_clear M).
  { rewrite DSC_eq in Himg. unfold kimg_covers in Himg. apply existsb_exists in Himg as (K & HinK & HKb).
    destruct K as [| | |ilo ihi| | | |]; try discriminate. apply andb_prop in HKb as [Hil Hih].
    apply Z.leb_le in Hil. apply Z.leb_le in Hih.
    pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKi. cbn [kentry_ok] in HKi. destruct HKi as (_ & _ & Hnone).
    intros j Hj. apply Hnone. unfold SCT. lia. }
  pose proof (ranges_apart_x_sound RSEGS E M (kn cs) gb (gk + 16) (ELit 8) sb (sk - 3) (mkAlu ALU_ADD strideE (ELit (-1))) HKN Hap) as Hdisj.
  unfold estart in Hdisj. cbn [a_base a_off] in Hdisj. rewrite elenZ_lit in Hdisj. change (8 mod 2 ^ 64) with 8 in Hdisj.
  assert (Elm1 : elenZ E (mkAlu ALU_ADD strideE (ELit (-1))) = stride - 1).
  { unfold elenZ. rewrite mkAlu_denot, alu_add, Estr. cbn [edenot]. unfold v_add. rewrite (u64_lit stride) by lia.
    rewrite (Z_to_bv_unsigned 64 (-1)), bv_wrap64_mod. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
    replace (stride + (2 ^ 64 - 1)) with ((stride - 1) + 1 * 2 ^ 64) by lia.
    rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z_mod_plus_full. apply Z.mod_small. lia. }
  rewrite Elm1 in Hdisj.
  destruct (ealign_sound RSEGS E M (kn cs) start HKN) as [Heal Hdiv]. rewrite Ust in Hdiv.
  assert (Hst16 : st mod 16 = 0).
  { apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hdiv].
    exists (2 ^ (ealign (kn cs) start - 4)). change 16 with (2 ^ 4). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  (* [comment removed for export] *)
  set (off := enframe_off (slack_of stride n) ((if bv_unsigned b3 =? 0 then bv_unsigned c13 else o16 + 1) mod 256)).
  assert (EF : efH M c13 g M0 W 0 n (bv_unsigned b3) o16 stride st off).
  { constructor.
    - symmetry. exact Hss_stride.
    - unfold slot_start, UNIT. lia.
    - reflexivity.
    - exact Hg40.
    - lia.
    - lia.
    - lia.
    - lia.
    - intros Hd. exfalso. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite RM. subst M0. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - rewrite RW. subst W. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exact R4.
    - rewrite Z_to_bv_bv_unsigned. exact HM3.
    - intros _. rewrite Hbs2. subst o16. rewrite word_to_le_bytes_of_lez by (assumption || lia). reflexivity.
    - exact OK3.
    - exact TBL. }
  pose proof (off_facts M c13 g M0 W 0 n (bv_unsigned b3) o16 stride st off EF) as (Ooff & O255 & O16 & Oslack).
  assert (R12' : getr R (Z_to_bv 5 (Z.of_nat 12)) = Z_to_bv 64 n) by (rewrite R12; symmetry; apply Z_to_bv_bv_unsigned).
  destruct (enframe_run M c13 g M0 W 0 n (bv_unsigned b3) o16 stride st off EF R (seg_rom RSEGS) (Z_to_bv 64 ret)
              R1 Hrok R10' R11 R12' eq_refl) as (R' & Hms & Hkeeps & HA0).
  pose proof (post_memF M c13 g M0 W 0 n (bv_unsigned b3) o16 stride st off EF) as POST.
  set (MF := memF M 0 n stride st off) in *.
  (* [comment removed for export] *)
  unfold cfg_of. rewrite Hpc. replace (Z_to_bv 64 (t_enframe P0)) with (0x998fc%bv : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (co_halt _ _ _ _ _ HC) | exact (co_lazy _ _ _ _ _ HC) | exact Hms |]. clear Hms.
  (* [comment removed for export] *)
  assert (Hslack : slack_of stride n <= shs).
  { subst shs shi. unfold slack_of, IB, UNIT. apply Z.div_le_mono; lia. }
  set (offw := (Z_to_bv 64 off : word)).
  set (E1 := ext1 E v offw).
  assert (Hag1 : env_agree v E E1) by (subst E1; apply ext1_agree).
  assert (HC1 : cs_ok E1 cs1 R M model) by (subst E1 cs1 v; apply cs_ok_bump1; [exact HC | exact Hfresh]).
  assert (Hnx1 : s_next (c_ss cs1) = S v) by (subst cs1; cbn [bump_next c_ss s_next]; subst v; apply Nat.add_1_r).
  assert (Eoffe : edenot E1 offe = offw) by (subst E1 offe; apply ext1_at).
  assert (Estart1 : edenot E1 start = Z_to_bv 64 st).
  { rewrite <- (edenot_agree v E E1 start Hag1) by (rewrite <- expr_vars_lt_eq; exact Hvs). exact Est. }
  assert (Ene1 : edenot E1 ne = nw).
  { rewrite <- (edenot_agree v E E1 ne Hag1) by (rewrite <- expr_vars_lt_eq; exact Hvn). reflexivity. }
  assert (Estr1 : edenot E1 strideE = Z_to_bv 64 stride).
  { rewrite <- (edenot_agree v E E1 strideE Hag1) by (rewrite <- expr_vars_lt_eq; exact Hvstr). exact Estr. }
  assert (EWe1 : edenot E1 We = edenot E We).
  { symmetry. apply (edenot_agree v E E1 We Hag1). rewrite <- expr_vars_lt_eq. exact HvW. }
  assert (Esb1 : edenot E1 sb = edenot E sb).
  { symmetry. apply (edenot_agree v E E1 sb Hag1). rewrite <- expr_vars_lt_eq. eapply split_lit_vars; [exact Hss | exact Hvs]. }
  assert (Hoffw : bv_unsigned offw = off) by (subst offw; apply u64_lit; lia).
  assert (Etimes : edenot E1 (times16 offe) = Z_to_bv 64 (16 * off)) by (rewrite times16_denot, Eoffe, Hoffw; reflexivity).
  assert (Ep1 : edenot E1 p = Z_to_bv 64 (st + 16 * off)).
  { subst p. rewrite mkAlu_denot, alu_add, Estart1, Etimes. unfold v_add. rewrite !u64_lit by lia. reflexivity. }
  assert (Epn1 : edenot E1 pn = Z_to_bv 64 (st + 16 * off + n)).
  { subst pn. rewrite mkAlu_denot, alu_add, Ep1, Ene1. unfold v_add. rewrite u64_lit by lia. reflexivity. }
  assert (Elen1 : elenZ E1 len1 = 16 * off + 3).
  { unfold elenZ. subst len1. rewrite mkAlu_denot, alu_add, Etimes. cbn [edenot]. unfold v_add.
    rewrite (u64_lit (16 * off)), (u64_lit 3) by lia. apply u64_lit. lia. }
  assert (Hn_eq : bv_unsigned nw = n) by reflexivity.
  assert (Erexp : edenot E1 rexp = Z_to_bv 64 (stride - n - 16 * off)).
  { subst rexp. rewrite mkAlu_denot, alu_sub, Estr1. rewrite mkAlu_denot, alu_add, Ene1, Etimes.
    unfold v_sub, v_add. rewrite (u64_lit (16 * off)), (u64_lit stride), Hn_eq by lia.
    rewrite (u64_lit (n + 16 * off)) by lia. f_equal. lia. }
  assert (Elen2 : elenZ E1 len2 = stride - 4 - n - 16 * off).
  { unfold elenZ. subst len2. rewrite mkAlu_denot, alu_add, Erexp. cbn [edenot]. unfold v_add.
    rewrite (u64_lit (stride - n - 16 * off)) by lia. rewrite (Z_to_bv_unsigned 64 (-4)), bv_wrap64_mod. change ((-4) mod 2 ^ 64) with (2 ^ 64 - 4).
    replace (stride - n - 16 * off + (2 ^ 64 - 4)) with ((stride - 4 - n - 16 * off) + 1 * 2 ^ 64) by lia.
    rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z_mod_plus_full. apply Z.mod_small. lia. }
  (* [comment removed for export] *)
  assert (HK1 : know_ok RSEGS E1 M (kn cs)) by exact (co_know _ _ _ _ _ HC1).
  assert (HSL1 : slots_ok E1 M (c_slots cs)) by exact (co_slots _ _ _ _ _ HC1).
  assert (Hkf : know_ok RSEGS E1 M kf).
  { subst kf. apply Forall_cons; [|apply Forall_one]; cbn [kentry_ok].
    - rewrite Eoffe, Hoffw. lia.
    - rewrite Erexp. rewrite u64_lit by lia. lia. }
  assert (K0 : know_ok RSEGS E1 M (kf ++ kn cs)) by (apply Forall_app; split; [exact Hkf | exact HK1]).
  assert (PB : bv_unsigned (edenot E1 pb) + pk = st + 16 * off).
  { pose proof (flat_b_sound E1 M (kf ++ kn cs) pb pk 1 K0 Hflp) as F. unfold flat, estart in F. cbn [a_base a_off] in F.
    pose proof (split_lit_denot E1 p pb pk Hsp) as X. rewrite Ep1 in X. apply (f_equal bv_unsigned) in X.
    rewrite !u64_lit in X by lia. lia. }
  assert (PNB : bv_unsigned (edenot E1 pnb) + pnk = st + 16 * off + n).
  { pose proof (flat_b_sound E1 M (kf ++ kn cs) pnb pnk 1 K0 Hflpn) as F. unfold flat, estart in F. cbn [a_base a_off] in F.
    pose proof (split_lit_denot E1 pn pnb pnk Hspn) as X. rewrite Epn1 in X. apply (f_equal bv_unsigned) in X.
    rewrite !u64_lit in X by lia. lia. }
  (* [comment removed for export] *)
  assert (SLOT : slot_ok E1 MF s).
  { unfold slot_ok. subst s. cbn [sl_start sl_stride sl_n sl_off sl_W sl_idx sl_p]. rewrite Hss, Hsp.
    unfold uE. rewrite Estart1, Ene1, Eoffe, Ep1, Hn_eq, Hoffw, Estr1, EWe1. fold W.
    rewrite (u64_lit st), (u64_lit stride), (u64_lit (st + 16 * off)) by lia.
    rewrite Esb1.
    split; [exact POST|]. split; [reflexivity|]. split; [exact SB|]. split; [exact PB|].
    split; [symmetry; exact Hss_stride|]. split; [intros Hd; exfalso; lia|].
    pose proof (stride_mod16 Sv). fold stride in H. repeat split; lia. }
  subst cs' k1 k2.
  apply (enframe_core cs cs1 csa E E1 R R' M model T ret v (S v) p sb pnb len1 len2 strideE sk pnk (kf ++ kn cs) [] s
           0 stride st n off HK Hac HC1 HK1 HSL1 Hfresh eq_refl Hnx1); try assumption; try lia.
  4:{ split; [lia|]. cbv. reflexivity. }
  - rewrite Esb1. exact SB.
  - unfold elenZ. rewrite Estr1. apply u64_lit. lia.
  - constructor.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
#[using="Type"] Theorem call_enframe2_ok_fx : forall cs cs' E R M model T,
  cs_ok E cs R M model -> pc cs = t_enframe P0 -> call_enframe2 RSEGS P0 nx0 cs = Some cs' ->
  (forall E' R' M', env_agree nx0 E E' -> cs_ok E' cs' R' M' model ->
      realizes RSEGS (cfg_of R' (pc cs') M' model) T) ->
  realizes RSEGS (cfg_of R (pc cs) M model) T.
Proof.
   intros cs cs' E R M model T HC Hpc Hn HK.
  unfold call_enframe2 in Hn.
  destruct (call_enframe RSEGS P0 nx0 cs) as [cs1|] eqn:H1.
  - injection Hn as <-. exact (call_enframe_ok_fx cs cs1 E R M model T HC Hpc H1 HK).
  - exact (call_enframe_x_ok_fx cs cs' E R M model T HC Hpc Hn HK).
Qed.

End NX0.

(* [comment removed for export] *)
Theorem call_enframe_ok : forall nx0, enframe_sound_stmt nx0.
Proof. intros nx0  fx. exact (call_enframe_ok_fx nx0 ). Qed.
Theorem call_enframe_x_ok : forall nx0, enframe_x_sound_stmt nx0.
Proof. intros nx0  fx. exact (call_enframe_x_ok_fx nx0 ). Qed.
Theorem call_enframe2_ok : forall nx0, enframe2_sound_stmt nx0.
Proof. intros nx0  fx. exact (call_enframe2_ok_fx nx0 ). Qed.
