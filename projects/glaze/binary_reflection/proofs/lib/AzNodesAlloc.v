(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma callee_saved_of_not_caller : forall n, (n < 32)%nat -> n <> 0%nat -> ~ In n caller_saved ->
  In (Z.of_nat n) callee_saved_regs.
Proof.
  intros n Hn.
  do 32 (destruct n as [|n];
    [intros A B; first [exfalso; apply A; reflexivity | exfalso; apply B; cbn; tauto | cbn; tauto] |]).
  lia.
Qed.

Lemma kept_ok_of_callee_saved : forall R R',
  (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) -> kept_ok R R'.
Proof.
  intros R R' H r Hr0 Hnin.
  pose proof (ridx_range r) as Hrr.
  assert (Hnz : ridx r <> 0%nat).
  { intros X. apply Hr0. apply bv_eq. unfold ridx in X. 
    replace (bv_unsigned (0%bv : bv 5)) with 0 by reflexivity. pose proof (bv_unsigned_in_range _ r). lia. }
  rewrite (reg_of_ridx r (ridx r) eq_refl). apply H. apply callee_saved_of_not_caller; assumption.
Qed.

Lemma kn_vars_lt_forallb : forall b k, AP.kn_vars_lt b k = forallb (kentry_vars_lt b) k.
Proof. intros b k. induction k as [|K r IH]; [reflexivity|]. cbn [AP.kn_vars_lt forallb]. rewrite IH. reflexivity. Qed.



Lemma store_ok_bytes : forall SEGS M (a : word) n (x : word),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 -> store_ok SEGS M a n = true ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> store_ok SEGS M x 1 = true.
Proof.
  intros SEGS M a n x Hnw Hs Hx. apply store_ok_of_all; [change (Z.of_nat 1) with 1; lia|].
  intros y Hy. eapply store_ok_all; [exact Hnw | exact Hs | change (Z.of_nat 1) with 1 in Hy; lia].
Qed.

(* [comment removed for export] *)
Lemma store_ok_mrestrict_full : forall SEGS H M (a : word),
  store_ok SEGS (mrestrict H M) a 1 = true -> store_ok SEGS M a 1 = true.
Proof.
  intros SEGS H M a Hs. cbn [store_ok] in Hs |- *. unfold wview in Hs |- *. unfold mrestrict in Hs.
  destruct (H a); destruct (M a); first [exact Hs | reflexivity | idtac].
  all: try exact Hs.
Qed.

Lemma cost_hi_sound : forall SEGS E M k live ch,
  know_ok SEGS E M k -> cost_hi k live = Some ch -> GPS.bcost E live <= ch /\ 0 <= GPS.bcost E live.
Proof.
  intros SEGS E M k live. induction live as [|[b n] r IH]; intros ch HK H; cbn [cost_hi GPS.bcost] in H |- *.
  - injection H as <-. lia.
  - cbn [snd]. destruct (xhi k n) as [h|] eqn:Hh; [|discriminate]. destruct (cost_hi k r) as [c|] eqn:Hc; [|discriminate].
    injection H as <-. destruct (IH c HK eq_refl) as [IH1 IH2].
    pose proof (xhi_sound SEGS E M k n h HK Hh). pose proof (u64_range (edenot E n)). unfold GPS.uE, GPS.MBLK, AzIface.MBLK in *. lia.
Qed.

Lemma bcost_app : forall E l1 l2, GPS.bcost E (l1 ++ l2) = GPS.bcost E l1 + GPS.bcost E l2.
Proof. intros E l1 l2. induction l1 as [|p r IH]; [reflexivity|]. cbn [app GPS.bcost]. rewrite IH. lia. Qed.
Lemma bcost_nonneg : forall E l, 0 <= GPS.bcost E l.
Proof. intros E l. induction l as [|p r IH]; cbn [GPS.bcost]; [lia|]. pose proof (u64_range (edenot E (snd p))). unfold GPS.uE, GPS.MBLK. lia. Qed.
Lemma bcount_app : forall l1 l2 : list (expr * expr), GPS.bcount (l1 ++ l2) = GPS.bcount l1 + GPS.bcount l2.
Proof. intros. unfold GPS.bcount. rewrite length_app. lia. Qed.

Lemma align16_of_ealign : forall a (z : Z), 4 <= a <= 64 -> (2 ^ a | z) -> z mod 16 = 0.
Proof.
  intros a z Ha [q ->]. replace a with (a - 4 + 4) by lia. rewrite Z.pow_add_r by lia.
  change (2 ^ 4) with 16. rewrite Z.mul_assoc. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable SHC : list (Z * Z).
Variable VSH : list (Z * Z).
Variable AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable KCAP : Z.
Variable FTOPc : Z.   (* [comment removed for export] *)
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.
Variable G : gtable.
Variable bcap ccap : Z.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ).
#[local] Notation MRof := (GPS.Mr SHC VSH).

Lemma some_inj : forall {A} (a b : A), Some a = Some b -> a = b.
Proof. intros A a b H. injection H as H. exact H. Qed.

(* [comment removed for export] *)
Lemma call_ok_stk_sound : forall stk entry cs ret E fx R M model,
  0 < stk < 2 ^ 40 ->
  cs_ok E cs fx R M model -> call_ok_stk nx0 G stk entry cs = Some ret ->
  let k := kn cs in let sp := reg cs 2 in let '(spb, spk) := split_lit sp in
  pc cs = entry
  /\ fresh_ok nx0 cs = true /\ length (s_regs (a_ss cs)) = 32%nat
  /\ getr R (Z_to_bv 5 1) = Z_to_bv 64 ret /\ 0 <= ret < 2 ^ 64 /\ ret mod 2 = 0
  /\ getr R (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G)
  /\ getr R (Z_to_bv 5 2) = edenot E sp
  /\ uE E sp = uE E spb + spk /\ uE E sp mod 16 = 0 /\ SFLOOR + stk <= uE E sp /\ uE E sp <= SPTOPc /\ uE E sp + 16 <= two47
  /\ (forall a : word, uE E sp - stk <= bv_unsigned a < uE E sp -> store_ok SEGS M a 1 = true)
  /\ forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (a_vis cs ++ a_fake cs ++ a_ghost cs) = true.
Proof.
  intros stk entry cs ret E fx R M model Hstk HC H.
  unfold call_ok_stk in H.
  destruct (negb (Z.eqb (pc cs) entry)) eqn:Hpc; [discriminate|]. apply negb_false_iff in Hpc. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret'|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 4) as [tp|] eqn:Htp; [|discriminate].
  cbv zeta in H.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as ->.
  apply andb_prop in Hc as [Hc Hflat]. apply andb_prop in Hc as [Hc Hxhi]. apply andb_prop in Hc as [Hc Hfl]. apply andb_prop in Hc as [Hc Hkw].
  apply andb_prop in Hc as [Hc Hal]. apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Htpe Hfresh].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hxh; [|discriminate]. apply Z.leb_le in Hxhi.
  apply Z.eqb_eq in Htpe. subst tp. apply Nat.eqb_eq in Hlen. apply Z.leb_le in Hal.
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  set (MR := MRof E cs model M) in HK.
  destruct (ret_lit_sound E cs R ret HR Hret) as (R1 & _ & Rr & Re).
  destruct (reg_lit_sound E cs R 4 (g_tp G) HR ltac:(lia) Htp) as [R4 _].
  pose proof (reg_sound E cs R 2 HR ltac:(lia)) as R2.
  destruct (kwritable_x_sound SEGS E MR (kn cs) (kn cs) spb (spk - stk) (ELit stk) HK HK Hkw) as (W1 & W2 & W3).
  rewrite elenZ_lit in W1, W3 by lia. rewrite estart_SA in W1, W2, W3.
  pose proof (split_lit_denot E (reg cs 2) spb spk Hsp) as Hspd.
  destruct (ealign_sound SEGS E MR (kn cs) (reg cs 2) HK) as [A1 A2].
  pose proof (u64_range (edenot E spb)) as Rspb. pose proof ceil_rng as CR.
  (* [comment removed for export] *)
  assert (FL : forall z, bv_unsigned (edenot E spb) + (spk - stk) <= z < bv_unsigned (edenot E spb) + (spk - stk) + stk ->
               SFLOOR <= z < SPTOPc /\ SPTOPc < 2 ^ 64).
  { intros z Hz. rewrite <- (co_top HC).
    assert (Hz64 : 0 <= z < 2 ^ 64) by lia.
    pose proof (GPS.in_floor_sound SEGS E MR (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - stk) (ELit stk) (Z_to_bv 64 z)
                  HK Hfl (co_floor HC)) as X.
    rewrite estart_SA, elenZ_lit, u64_lit in X by lia. apply X. lia. }
  assert (Hspv : uE E (reg cs 2) = uE E spb + spk).
  { unfold uE. rewrite Hspd. apply u64_lit. pose proof (FL (bv_unsigned (edenot E spb) + spk - 1) ltac:(lia)). lia. }
  cbv zeta. rewrite Hsp.
  split; [exact Hpc|]. split; [exact Hfresh|]. split; [exact Hlen|]. split; [exact R1|]. split; [unfold two64 in Rr; lia|].
  split; [exact Re|]. split; [exact R4|]. split; [exact R2|]. split; [exact Hspv|].
  split; [eapply align16_of_ealign; [| exact A2]; lia|].
  split; [pose proof (FL (bv_unsigned (edenot E spb) + spk - stk) ltac:(lia)); unfold uE in *; lia|].
  split; [pose proof (FL (bv_unsigned (edenot E spb) + spk - 1) ltac:(lia)); unfold uE in *; lia|].
  split; [pose proof (xhi_sound SEGS E MR (kn cs) (reg cs 2) sphi HK Hxh); unfold uE in *; lia|].
  split; [|exact Hflat].
  intros a Ha. apply (store_ok_mrestrict_full SEGS (GPS.hid SHC VSH E cs model) M).
  eapply (store_ok_bytes SEGS MR (Z_to_bv 64 (bv_unsigned (edenot E spb) + (spk - stk))) (Z.to_nat stk));
    [rewrite u64_lit by lia; lia | apply W1; lia | rewrite u64_lit by lia; unfold uE in *; lia].
Qed.


(* [comment removed for export] *)
Lemma disj_facts_ok : forall E M M0 k p n live (pw : word),
  know_ok SEGS E M0 k ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) live = true ->
  edenot E p = pw ->
  (forall b m, In (b, m) (blocks_den E live) -> bv_unsigned pw + uE E n <= b \/ b + m <= bv_unsigned pw) ->
  know_ok SEGS E M (disj_facts p n live).
Proof.
  intros E M M0 k p n live pw HK Hflat Hp Hd. unfold disj_facts, know_ok. apply Forall_forall. intros K HKin.
  apply in_map_iff in HKin as [[b0 ln] [HKe Hin]]. cbn [fst snd] in HKe.
  destruct (split_lit b0) as [lb lk] eqn:Hs. subst K. cbn [kentry_ok].
  rewrite !estart_SA. cbn [edenot]. rewrite Hp. unfold elenZ.
  pose proof (split_lit_denot E b0 lb lk Hs) as Hd0.
  pose proof (proj1 (forallb_forall _ _) Hflat _ Hin) as Hfl. cbn [fst snd] in Hfl. rewrite Hs in Hfl.
  pose proof (bflat_x_sound SEGS E _ k lb lk ln HK Hfl) as (F1 & F2 & F3). rewrite !estart_SA in F1, F2, F3.
  specialize (Hd (uE E b0) (uE E ln)).
  assert (Hin' : In (uE E b0, uE E ln) (blocks_den E live)).
  { unfold blocks_den. apply in_map_iff. exists (b0, ln). split; [reflexivity | exact Hin]. }
  specialize (Hd Hin'). unfold uE in Hd. rewrite Hd0 in Hd. rewrite u64_lit in Hd by lia.
  pose proof (u64_range pw). lia.
Qed.

(* [comment removed for export] *)

Lemma remove_block_split : forall p live m live',
  remove_block p live = Some (m, live') ->
  exists L1 L2, live = L1 ++ (p, m) :: L2 /\ live' = L1 ++ L2.
Proof.
  intros p live. induction live as [|[b n] r IH]; intros m live' H; cbn [remove_block] in H; [discriminate|].
  destruct (expr_eqb b p) eqn:Heq.
  - injection H as <- <-. apply expr_eqb_eq in Heq. subst b. exists [], r. split; reflexivity.
  - destruct (remove_block p r) as [[m' r']|] eqn:Hr; [|discriminate]. injection H as <- <-.
    destruct (IH m' r' eq_refl) as (L1 & L2 & -> & ->). exists ((b, n) :: L1), L2. split; reflexivity.
Qed.

Lemma blocks_den_app : forall E l1 l2, blocks_den E (l1 ++ l2) = blocks_den E l1 ++ blocks_den E l2.
Proof. intros. unfold blocks_den. apply map_app. Qed.

End Sound.
