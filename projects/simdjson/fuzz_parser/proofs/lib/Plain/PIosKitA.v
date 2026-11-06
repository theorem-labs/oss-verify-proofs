(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymStepR.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore LogDedupe.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosFxStep PIosFxSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import AX2. Import AX2B. Import AX2S.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mk_itab_ranges_acc_ok : forall segs rs t, itab_sound segs t -> itab_sound segs (APC.mk_itab_ranges_acc segs rs t).
Proof.
  intros segs. induction rs as [|[lo n] rs IH]; intros t Ht; cbn [APC.mk_itab_ranges_acc]; [exact Ht|].
  apply IH. apply mk_itab_fuel_sound. exact Ht.
Qed.
Lemma mk_itab_ranges_ok : forall segs rs, itab_sound segs (APC.mk_itab_ranges segs rs).
Proof.
  intros segs rs. unfold APC.mk_itab_ranges. apply mk_itab_ranges_acc_ok.
  intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Run.
Context {fx : FPState}.     (* [comment removed for export] *)
Variable segs : list Segment.

Definition closed_ok (ss : sym_state) : bool :=
  sr_vars_lt (s_next ss) (s_regs ss) && kn_vars_lt (s_next ss) (s_know ss).

Definition srun (IT : itab) (fuel : nat) (stops : list Z) (ss : sym_state) : option (sym_state * list sentry) :=
  if closed_ok ss then
    let bc := mkbc (facts_of (s_know ss)) in
    let kx := mk_kix (s_know ss) in
    let ss' := sym_execTXBI segs bc kx IT 0 fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    let lg := APC.log_dd (s_log ss') in
    match carryK bc lg (s_know ss') [] with
    | (kn', [], _) => Some (SS (s_pc ss') (s_regs ss') [] kn' (s_next ss'), lg)
    | _ => None
    end
  else None.

Theorem srun_sound : forall IT fuel stops ss ss' lg,
  itab_sound segs IT -> srun IT fuel stops ss = Some (ss', lg) ->
  forall E base rom R, regs_ok E (s_regs ss) R -> know_ok segs E base (s_know ss) ->
  exists E' R', env_agree (s_next ss) E E' /\ (s_next ss <= s_next ss')%nat
    /\ regs_ok E' (s_regs ss') R' /\ log_flat E' lg
    /\ know_ok segs E' (mem_denot E' base lg) (s_know ss')
    /\ msteps segs (mkst R (Z_to_bv 64 (s_pc ss)) base rom) (mkst R' (Z_to_bv 64 (s_pc ss')) (mem_denot E' base lg) rom).
Proof.
  intros IT fuel stops ss ss' lg HIT Hrun E base rom R HR HK. unfold srun in Hrun.
  destruct (closed_ok ss) eqn:Hc; [|discriminate]. unfold closed_ok in Hc. apply andb_prop in Hc as [Fsr Fkn].
  cbv zeta in Hrun.
  rewrite (sym_execTXBI_eq segs (s_know ss)) in Hrun by reflexivity.
  set (sx := sym_execTX segs IT 0 fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss))) in *.
  assert (Hkn : s_know sx = s_know ss) by (unfold sx; rewrite sym_execTX_know; reflexivity).
  rewrite <- Hkn in Hrun at 1. rewrite carryK_eq in Hrun.
  destruct (carry (APC.log_dd (s_log sx)) (s_know sx) []) as [[kn' scs] hs] eqn:Hcar.
  destruct scs; [|discriminate]. injection Hrun as <- <-.
  pose proof (AX2F.runTX_sound segs IT 0 fuel stops (s_pc ss) (s_regs ss) (s_know ss) (s_next ss) E base rom R HIT HR HK Fsr Fkn) as HX.
  cbv zeta in HX. fold sx in HX. destruct HX as (E' & R' & Hag & Hle & HR' & Hlf & HK' & Hms & _).
  exists E', R'. cbn [s_pc s_regs s_know s_next].
  split; [exact Hag|]. split; [exact Hle|]. split; [exact HR'|]. split; [apply log_flat_dd; exact Hlf|].
  rewrite (mem_denot_dd E' base (s_log sx) Hlf). split; [|exact Hms].
  rewrite <- (mem_denot_dd E' base (s_log sx) Hlf).
  eapply (carry_sound segs E' base); [exact Hcar | exact (log_flat_dd _ _ Hlf) | exact HK' | constructor].
Qed.

End Run.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fpwin : Type := (expr * Z * Z)%type.
Definition se_in_fp (W : list fpwin) (s : sentry) : bool :=
  match s with
  | SE (SA b off) w _ => existsb (fun x => match x with (b', lo, hi) => expr_eqb b b' && Z.leb lo off && Z.leb (off + Z.of_nat w) hi end) W
  end.
Definition fp_closed (nx : nat) (W : list fpwin) : bool := forallb (fun x => match x with (b, _, _) => expr_vars_lt nx b end) W.

Definition fpwin_den (E : env) (x : fpwin) : Z * Z :=
  match x with (b, lo, hi) => (bv_unsigned (edenot E b) + lo, bv_unsigned (edenot E b) + hi)%Z end.

Fixpoint outsideZ (W : list (Z * Z)) (x : Z) : Prop :=
  match W with [] => True | (lo, hi) :: W' => ~ (lo <= x < hi)%Z /\ outsideZ W' x end.

Lemma outsideZ_in : forall W lo hi x, outsideZ W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof.
  induction W as [|[l h] W IH]; intros lo hi x Ho Hin; [destruct Hin|].
  cbn in Ho. destruct Ho as [H1 H2]. destruct Hin as [Heq|Hin]; [injection Heq as -> ->; exact H1 | eapply IH; eauto].
Qed.

Lemma length_word_to_le_bytes : forall w v, length (word_to_le_bytes w v) = w.
Proof. intros w v. unfold word_to_le_bytes. generalize (bv_unsigned v). induction w as [|w IH]; intros z; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma mem_denot_outside : forall E W base lg (x : word),
  log_flat E lg -> forallb (se_in_fp W) lg = true ->
  outsideZ (map (fpwin_den E) W) (bv_unsigned x) ->
  mem_denot E base lg x = base x.
Proof.
  intros E W base lg x. induction lg as [|[a w v] rest IH]; intros Hlf Hfp Hout; [reflexivity|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfl & Hlf). cbn [forallb] in Hfp. apply andb_prop in Hfp as [Hs Hfp].
  cbn [mem_denot]. rewrite <- (IH Hlf Hfp Hout).
  pose proof (flat_u E a _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  assert (Hx : (bv_unsigned x < estart E a \/ estart E a + Z.of_nat w <= bv_unsigned x)%Z).
  { destruct a as [b off]. unfold estart in *. cbn [a_base a_off] in *. cbn [se_in_fp] in Hs.
    apply existsb_exists in Hs. destruct Hs as ([[b' lo] hi] & Hin & Hb).
    apply andb_prop in Hb as [Hb Hb2]. apply andb_prop in Hb as [Hbe Hb1].
    apply expr_eqb_eq in Hbe. subst b'. apply Z.leb_le in Hb1, Hb2.
    pose proof (outsideZ_in _ _ _ _ Hout (in_map (fpwin_den E) W _ Hin)) as Ho. cbn [fpwin_den] in Ho. lia. }
  destruct Hx as [Hlt|Hge].
  - apply wbytes_below; rewrite ?length_word_to_le_bytes, Hu; lia.
  - apply wbytes_above. rewrite length_word_to_le_bytes, Hu. lia.
Qed.

Lemma fpwin_den_agree : forall nx E E' W, env_agree nx E E' -> fp_closed nx W = true -> map (fpwin_den E') W = map (fpwin_den E) W.
Proof.
  intros nx E E' W Hag. induction W as [|[[b lo] hi] W IH]; intros Hc; [reflexivity|].
  cbn [fp_closed forallb] in Hc. apply andb_prop in Hc as [Hb Hc]. cbn [map fpwin_den].
  rewrite (edenot_agree nx E E' b Hag Hb), (IH Hc). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Export.
Variable segs : list Segment.

Definition kw_byte (k : kentry) (a : Z) : option byte :=
  match k with
  | KWord (SA (ELit Z0) off) w (ELit v) =>
      if (Z.leb off a && Z.ltb a (off + Z.of_nat w))%bool then nth_error (word_to_le_bytes w (Z_to_bv 64 v)) (Z.to_nat (a - off)) else None
  | KImg lo hi => if (Z.leb lo a && Z.ltb a hi)%bool then seg_rom segs (Z_to_bv 64 a) else None
  | _ => None
  end.
Fixpoint kbyte (kn : list kentry) (a : Z) : option byte :=
  match kn with
  | [] => None
  | k :: r => match kw_byte k a with Some b => Some b | None => kbyte r a end
  end.

Definition rd1 (m : word -> option byte) (a : word) : option byte :=
  match m a with Some b => Some b | None => seg_rom segs a end.

Lemma rdn_nth : forall m n (k : Z) bs, (0 <= k)%Z -> (k + Z.of_nat n <= 2^64)%Z ->
  rdn segs m (Z_to_bv 64 k) n = Some bs ->
  forall i, (i < n)%nat -> rd1 m (Z_to_bv 64 (k + Z.of_nat i)) = nth_error bs i.
Proof.
  intros m. induction n as [|n IH]; intros k bs Hk Hn Hr i Hi; [lia|].
  cbn [rdn] in Hr. fold (rd1 m (Z_to_bv 64 k)) in Hr.
  destruct (rd1 m (Z_to_bv 64 k)) as [b|] eqn:Eb; [|discriminate].
  assert (Hnext : (Z_to_bv 64 k + 1 : word) = Z_to_bv 64 (k + 1)).
  { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1 : word)) with 1%Z.
    unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. }
  rewrite Hnext in Hr.
  destruct (rdn segs m (Z_to_bv 64 (k + 1)) n) as [rest|] eqn:Er; [|discriminate]. injection Hr as <-.
  destruct i as [|i].
  - cbn [nth_error]. rewrite Z.add_0_r. exact Eb.
  - cbn [nth_error]. replace (k + Z.of_nat (S i))%Z with ((k + 1) + Z.of_nat i)%Z by lia.
    apply (IH (k + 1)%Z rest); [lia | lia | exact Er | lia].
Qed.

Lemma kw_byte_sound : forall E m k a b,
  kentry_ok segs E m k -> kw_byte k a = Some b -> rd1 m (Z_to_bv 64 a) = Some b.
Proof.
  intros E m k a b Hk Hb. destruct k as [[bb off] w v| | |lo hi| | | | | | ]; try discriminate Hb.
  - cbn [kw_byte] in Hb. destruct bb as [z| | | | | | | ]; try discriminate Hb. destruct z; try discriminate Hb.
    destruct v as [vz| | | | | | | ]; try discriminate Hb.
    destruct (Z.leb off a && Z.ltb a (off + Z.of_nat w))%bool eqn:Hin; [|discriminate].
    apply andb_prop in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    cbn [kentry_ok] in Hk. destruct Hk as (Hw8 & Hfl & Hrd).
    pose proof Hfl as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4. cbn [a_base a_off] in F1, F2, F4.
    rewrite edenot_lit in F1, F2, F4. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in F1, F2, F4.
    assert (Had : adenot E (SA (ELit 0) off) = Z_to_bv 64 off).
    { unfold adenot. cbn [a_base a_off]. rewrite edenot_lit. unfold v_addi. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. reflexivity. }
    rewrite Had, edenot_lit in Hrd.
    pose proof (rdn_nth m w off _ ltac:(lia) ltac:(lia) Hrd (Z.to_nat (a - off)) ltac:(lia)) as Hn.
    rewrite Z2Nat.id in Hn by lia. replace (off + (a - off))%Z with a in Hn by lia. rewrite Hn. exact Hb.
  - cbn [kw_byte] in Hb. destruct (Z.leb lo a && Z.ltb a hi)%bool eqn:Hin; [|discriminate].
    apply andb_prop in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    cbn [kentry_ok] in Hk. destruct Hk as (K1 & K2 & K3). unfold rd1. rewrite (K3 a ltac:(lia)). exact Hb.
Qed.

Lemma kbyte_sound : forall E m kn a b,
  know_ok segs E m kn -> kbyte kn a = Some b -> rd1 m (Z_to_bv 64 a) = Some b.
Proof.
  intros E m kn a b. induction kn as [|k r IH]; intros HK Hb; [discriminate|].
  apply Forall_cons_iff in HK as [Hk Hr]. cbn [kbyte] in Hb.
  destruct (kw_byte k a) as [b'|] eqn:Ek.
  - injection Hb as ->. eapply kw_byte_sound; eauto.
  - exact (IH Hr Hb).
Qed.

(* [comment removed for export] *)
Fixpoint chunk_ok (kn : list kentry) (a : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' => match kbyte kn a with Some b' => bv_eqb b b' && chunk_ok kn (a + 1) bs' | None => false end
  end.

Lemma chunk_ok_sound : forall E m kn bs a,
  know_ok segs E m kn -> chunk_ok kn a bs = true ->
  forall i b, nth_error bs i = Some b -> rd1 m (Z_to_bv 64 (a + Z.of_nat i)) = Some b.
Proof.
  intros E m kn. induction bs as [|b0 bs IH]; intros a HK Hc i b Hn; [destruct i; discriminate|].
  cbn [chunk_ok] in Hc. destruct (kbyte kn a) as [b'|] eqn:Eb; [|discriminate].
  apply andb_prop in Hc as [He Hc]. unfold bv_eqb in He. apply Z.eqb_eq in He. apply bv_eq in He. subst b'.
  destruct i as [|i].
  - cbn in Hn. injection Hn as <-. rewrite Z.add_0_r. eapply kbyte_sound; eauto.
  - cbn in Hn. replace (a + Z.of_nat (S i))%Z with ((a + 1) + Z.of_nat i)%Z by lia. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Fixpoint kword_has (kn : list kentry) (a : saddr) (w : nat) (v : expr) : bool :=
  match kn with
  | [] => false
  | KWord a' w' v' :: r => (saddr_eqb a a' && Nat.eqb w w' && expr_eqb v v')%bool || kword_has r a w v
  | _ :: r => kword_has r a w v
  end.

Lemma kword_has_sound : forall E m kn a w v,
  know_ok segs E m kn -> kword_has kn a w v = true ->
  flat E a (Z.of_nat w) /\ rdn segs m (adenot E a) w = Some (word_to_le_bytes w (edenot E v)).
Proof.
  intros E m kn a w v. induction kn as [|k r IH]; intros HK H; [discriminate|].
  apply Forall_cons_iff in HK as [Hk Hr].
  destruct k as [a' w' v'| | | | | | | | | ]; cbn [kword_has] in H; try exact (IH Hr H).
  apply orb_prop in H as [H|H]; [|exact (IH Hr H)].
  apply andb_prop in H as [H Hv]. apply andb_prop in H as [Ha Hw].
  apply saddr_eqb_eq in Ha. apply Nat.eqb_eq in Hw. apply expr_eqb_eq in Hv. subst a' w' v'.
  cbn [kentry_ok] in Hk. destruct Hk as (_ & Hf & Hrd). split; assumption.
Qed.

End Export.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Keep.
Variable segs : list Segment.

Definition win_has (KEEP : list fpwin) (b : expr) (lo hi : Z) : bool :=
  existsb (fun x => match x with (b', l, h) => expr_eqb b b' && Z.leb l lo && Z.leb hi h end) KEEP.

Definition k_keep (KEEP : list fpwin) (k : kentry) : bool :=
  match k with
  | KWord (SA b off) w _ => win_has KEEP b off (off + Z.of_nat w)
  | KImg lo hi => win_has KEEP (ELit 0) lo hi
  | KWr (SA b off) (ELit n) => (Z.leb 0 n && Z.ltb n (2^64) && win_has KEEP b off (off + n))%bool
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true
  | _ => false
  end.
Definition kn_keep (KEEP : list fpwin) (kn : list kentry) : list kentry := List.filter (k_keep KEEP) kn.

Definition in_wins (Wd : list (Z * Z)) (x : Z) : Prop := exists lo hi, In (lo, hi) Wd /\ (lo <= x < hi)%Z.
Definition magree_win (E : env) (KEEP : list fpwin) (m m' : word -> option byte) : Prop :=
  forall x : word, in_wins (map (fpwin_den E) KEEP) (bv_unsigned x) ->
    m' x = m x /\ (wview segs m x <> None -> wview segs m' x <> None).

Lemma win_has_in : forall E KEEP b lo hi x, win_has KEEP b lo hi = true ->
  (bv_unsigned (edenot E b) + lo <= x < bv_unsigned (edenot E b) + hi)%Z -> in_wins (map (fpwin_den E) KEEP) x.
Proof.
  intros E KEEP b lo hi x H Hx. unfold win_has in H. apply existsb_exists in H. destruct H as ([[b' l] h] & Hin & Hb).
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [Hbe H1]. apply expr_eqb_eq in Hbe. subst b'.
  apply Z.leb_le in H1, H2. exists (bv_unsigned (edenot E b) + l)%Z, (bv_unsigned (edenot E b) + h)%Z.
  split; [exact (in_map (fpwin_den E) KEEP _ Hin) | lia].
Qed.

Lemma rdn_agree : forall (m m' : word -> option byte) n (k : Z), (0 <= k)%Z -> (k + Z.of_nat n <= 2^64)%Z ->
  (forall i, (k <= i < k + Z.of_nat n)%Z -> m' (Z_to_bv 64 i) = m (Z_to_bv 64 i)) ->
  rdn segs m' (Z_to_bv 64 k) n = rdn segs m (Z_to_bv 64 k) n.
Proof.
  intros m m'. induction n as [|n IH]; intros k Hk Hn H; [reflexivity|]. cbn [rdn].
  rewrite (H k ltac:(lia)).
  assert (Hnext : (Z_to_bv 64 k + 1 : word) = Z_to_bv 64 (k + 1)).
  { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1 : word)) with 1%Z.
    unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. }
  rewrite Hnext, (IH (k + 1)%Z) by (try lia; intros i Hi; apply H; lia). reflexivity.
Qed.

Lemma u64 : forall i, (0 <= i < 2^64)%Z -> bv_unsigned (Z_to_bv 64 i) = i.
Proof. intros i Hi. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | unfold bv_modulus; lia]. Qed.

Lemma kentry_keep_ok : forall E KEEP m m' k,
  magree_win E KEEP m m' -> kentry_ok segs E m k -> k_keep KEEP k = true -> kentry_ok segs E m' k.
Proof.
  intros E KEEP m m' k HA Hk Hkeep.
  destruct k as [[b off] w v| | |lo hi|e al|e lo hi|[b off] n|a1 n1 a2 n2| | ]; cbn [k_keep] in Hkeep; try discriminate Hkeep; try exact Hk.
  - (* [comment removed for export] *)
    cbn [kentry_ok] in Hk |- *. destruct Hk as (Hw8 & Hfl & Hrd). split; [exact Hw8|]. split; [exact Hfl|].
    rewrite <- Hrd. pose proof Hfl as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4. cbn [a_base a_off] in F1, F2, F4.
    unfold adenot, v_addi. cbn [a_base a_off].
    apply rdn_agree; [exact F1 | exact F4 |].
    intros i Hi. apply HA. rewrite u64 by lia. eapply win_has_in; [exact Hkeep | lia].
  - (* [comment removed for export] *)
    cbn [kentry_ok] in Hk |- *. destruct Hk as (K1 & K2 & K3). split; [exact K1|]. split; [exact K2|].
    intros i Hi. rewrite <- (K3 i Hi). apply HA. rewrite u64 by lia.
    eapply (win_has_in E KEEP (ELit 0)); [exact Hkeep|]. rewrite edenot_lit. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
  - (* [comment removed for export] *)
    destruct n as [nz| | | | | | | ]; try discriminate Hkeep.
    apply andb_prop in Hkeep as [Hkeep Hwin]. apply andb_prop in Hkeep as [Hn0 Hn1]. apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1.
    cbn [kentry_ok] in Hk |- *. destruct Hk as (Hfl & Hso). split; [exact Hfl|].
    assert (HnE : elenZ E (ELit nz) = nz) by (unfold elenZ; rewrite edenot_lit; apply u64; lia).
    rewrite HnE in *. pose proof Hfl as (F1 & F2 & F3 & F4). unfold estart in *. cbn [a_base a_off] in *.
    intros d mm Hd Hdm. destruct mm as [|mm]; [reflexivity|].
    specialize (Hso d (S mm) Hd Hdm).
    assert (Hu : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E b) + off + d)) = (bv_unsigned (edenot E b) + off + d)%Z) by (apply u64; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. apply (proj2 (HA x ltac:(eapply win_has_in; [exact Hwin | lia]))).
    eapply (store_ok_all segs m (S mm)); [| exact Hso |]; rewrite Hu; lia.
Qed.

Lemma know_ok_keep : forall E KEEP m m' kn,
  magree_win E KEEP m m' -> know_ok segs E m kn -> know_ok segs E m' (kn_keep KEEP kn).
Proof.
  intros E KEEP m m' kn HA HK. unfold kn_keep, know_ok in *. apply Forall_forall. intros k Hin.
  apply filter_In in Hin as [Hin Hkeep]. eapply kentry_keep_ok; [exact HA | exact (proj1 (Forall_forall _ _) HK k Hin) | exact Hkeep].
Qed.

(* [comment removed for export] *)
Lemma kentry_eqb_eq : forall x y, APC.kentry_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y; cbn [APC.kentry_eqb] in H; try discriminate;
  repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    end;
  repeat match goal with
    | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
    | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    end; subst; reflexivity.
Qed.
Definition kn_sub (a b : list kentry) : bool := forallb (fun k => existsb (APC.kentry_eqb k) b) a.
Lemma kn_sub_ok : forall E m a b, kn_sub a b = true -> know_ok segs E m b -> know_ok segs E m a.
Proof.
  intros E m a b H HK. unfold know_ok in *. apply Forall_forall. intros k Hk.
  pose proof (proj1 (forallb_forall _ _) H k Hk) as He. apply existsb_exists in He. destruct He as (k' & Hin & Heq).
  apply kentry_eqb_eq in Heq. subst k'. exact (proj1 (Forall_forall _ _) HK k Hin).
Qed.

End Keep.
