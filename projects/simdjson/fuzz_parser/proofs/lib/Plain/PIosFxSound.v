(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import SymStepR AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require AxSymExec3Sound AxSymRun3.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require MemSplit.
From Stdlib Require Import Zify.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosFxStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Module AX2F.
Import AX2.
Import AxSymExec3Sound.AX2S.
Import AxSymRun3.

Section FX.
Context {fx : FPState}.

Section StepSound.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition st_ok (E : env) (base rom : word -> option byte)
                 (ss : sym_state) (ms : machine_state) : Prop :=
  exists regs, ms = mkst regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
            /\ regs_ok E (s_regs ss) regs
            /\ log_flat E (s_log ss)
            /\ know_ok segs E base (s_know ss).

(* [comment removed for export] *)
Definition resv_denot (E : env) (r : option saddr) : option word :=
  match r with Some a => Some (adenot E a) | None => None end.

(* [comment removed for export] *)
Definition st_okR (E : env) (base rom : word -> option byte)
                  (ss : sym_state) (ms : machine_state) : Prop :=
  exists regs, ms = mkstR regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
                              (resv_denot E (s_resv ss))
            /\ regs_ok E (s_regs ss) regs
            /\ log_flat E (s_log ss)
            /\ know_ok segs E base (s_know ss).

Lemma st_ok_R : forall E base rom ss ms,
  st_ok E base rom ss ms -> st_okR E base rom (clr ss) ms.
Proof.
  intros E base rom ss ms (regs & -> & HR & HL & HK). exists regs.
  split; [reflexivity|]. split; [exact HR|]. split; [exact HL|exact HK].
Qed.

Lemma st_okR_ok : forall E base rom ss ms,
  st_okR E base rom ss ms -> s_resv ss = None -> st_ok E base rom ss ms.
Proof.
  intros E base rom ss ms (regs & -> & HR & HL & HK) Hr. exists regs. rewrite Hr.
  split; [reflexivity|]. split; [exact HR|]. split; [exact HL|exact HK].
Qed.

Lemma s_clean_None : forall ss, s_clean ss = true <-> s_resv ss = None.
Proof. intros ss. unfold s_clean. destruct (s_resv ss); split; intros H; congruence. Qed.

Lemma s_resv_clr : forall ss, s_resv (clr ss) = None.
Proof. reflexivity. Qed.

Lemma msize_bytes_range : forall sz, (1 <= msize_bytes sz)%nat /\ (msize_bytes sz <= 8)%nat.
Proof. destruct sz; cbn; lia. Qed.

Lemma msize_bytes_R : forall sz, SymStepR.msize_bytes sz = msize_bytes sz.
Proof. destruct sz; reflexivity. Qed.

Lemma amo_nbytes_sz : forall wd, amo_nbytes wd = msize_bytes (amo_sz wd).
Proof. destruct wd; reflexivity. Qed.

Lemma amo_msize_sz : forall wd, amo_msize wd = amo_sz wd.
Proof. destruct wd; reflexivity. Qed.

Lemma v_addi_0 : forall x : word, v_addi x 0 = x.
Proof. intros x. unfold v_addi. apply Z_to_bv_u_plus0. Qed.

Lemma wrap_swrap : forall n z, bv_wrap n (bv_swrap n z) = bv_wrap n z.
Proof. intros n z. unfold bv_swrap, bv_wrap. rewrite Zminus_mod_idemp_l. f_equal. lia. Qed.

Lemma low32_sext64_32 : forall v : bv 32, low32 (sext 64 v) = v.
Proof.
  intros v. apply bv_eq. rewrite low32_unsigned, sext32_unsigned.
  rewrite bv_wrap_bv_wrap by lia. rewrite wrap_swrap. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma sym_read_sound : forall E base ss scr a n sx' v scs scr' nx',
  sym_read segs ss (facts_of (s_know ss)) scr a n sx' = Some (v, scs, scr', nx') ->
  scs_denot segs base E scs ->
  log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  (1 <= n)%nat -> (n <= 8)%nat ->
  flat E a (Z.of_nat n) /\
  exists bs, rdn segs (mem_denot E base (s_log ss)) (adenot E a) n = Some bs
             /\ length bs = n
             /\ Z_to_bv 64 (extz sx' n (bytes_le_to_Z bs)) = edenot E v.
Proof.
  intros E base ss scr a n sx' v scs scr' nx' Hs Hsc Hlf Hkn Hn1 Hn8.
  set (mem := mem_denot E base (s_log ss)) in *.
  pose proof (facts_of_ok segs E base _ Hkn) as Hfk. set (fk := facts_of (s_know ss)) in *.
  unfold sym_read in Hs.
  pose proof (log_lookup_sound segs E base fk (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] Hfk Hlf Hn1 Hn8) as HL.
  destruct (log_lookup fk (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []) as [v0 lscs lh|lscs lh|] eqn:Hll;
    [ | | discriminate].
  - (* [comment removed for export] *)
    injection Hs as <- <- <- <-.
    apply (flat_sc_sound segs E base fk _ _ _ Hfk Hn1 Hn8) in Hsc as [Hfl Hsc].
    split; [exact Hfl|].
    destruct (HL Hsc ltac:(destruct a; exact Hfl)) as (bs & Hrd & Hlen & Hval).
    exists bs. split; [destruct a; exact Hrd|]. split; [exact Hlen|].
    rewrite (extK_denot segs E base fk v0 Hfk). exact Hval.
  - (* [comment removed for export] *)
    pose proof (know_lookupA_sound segs E base fk base (s_know ss) (a_base a) (a_off a) n sx' lh lscs Hfk Hkn Hn1 Hn8) as HK.
    pose proof (know_lookupA_acc fk segs (s_know ss) (a_base a) (a_off a) n sx' lh lscs) as HKacc.
    destruct (know_lookupA fk segs (s_know ss) (a_base a) (a_off a) n sx' lh lscs) as [v0 kscs kh|kscs kh|] eqn:Hkl;
      [ | | discriminate].
    + (* [comment removed for export] *)
      injection Hs as <- <- <- <-.
      apply (flat_sc_sound segs E base fk _ _ _ Hfk Hn1 Hn8) in Hsc as [Hfl Hsc].
      split; [exact Hfl|].
      destruct HKacc as [pre ->].
      assert (Hlscs : scs_denot segs base E lscs) by (apply scs_denot_app in Hsc as [_ H]; exact H).
      destruct (HK Hsc ltac:(destruct a; exact Hfl)) as (bs & Hrd & Hlen & Hval).
      exists bs. split.
      * destruct a; cbn [a_base a_off] in *. unfold mem. rewrite (HL Hlscs Hfl). exact Hrd.
      * split; [exact Hlen|]. rewrite (extK_denot segs E base fk v0 Hfk). exact Hval.
    + (* [comment removed for export] *)
      injection Hs as <- <- <- <-.
      apply (flat_sc_sound segs E base fk _ _ _ Hfk Hn1 Hn8) in Hsc as [Hfl Hsc].
      split; [exact Hfl|].
      apply scs_denot_cons in Hsc as [Hrb Hsc]. cbn [sc_denot] in Hrb.
      destruct Hrb as (bs & Hrd & Hval).
      destruct HKacc as [pre ->].
      assert (Hlscs : scs_denot segs base E lscs) by (apply scs_denot_app in Hsc as [_ H]; exact H).
      assert (Hrd' : rdn segs mem (adenot E a) n = Some bs).
      { destruct a; cbn [a_base a_off] in *. unfold mem. rewrite (HL Hlscs Hfl). exact Hrd. }
      exists bs. split; [exact Hrd'|]. split; [exact (rdn_length _ _ _ _ _ Hrd')|]. exact Hval.
Qed.

(* [comment removed for export] *)
Lemma storeok_sc_sound : forall E base fk a n,
  know_ok segs E base fk -> flat E a (Z.of_nat n) -> (1 <= n)%nat -> (n <= 8)%nat ->
  scs_denot segs base E (storeok_sc fk a n) ->
  RiscvSemantics.store_ok segs base (adenot E a) n = true.
Proof.
  intros E base fk a n Hfk Hfl Hn1 Hn8 Hsc.
  unfold storeok_sc in Hsc.
  destruct (wr_covered fk fk a n) eqn:Hw.
  - clear Hsc. revert Hw. pose proof Hfk as Hall. generalize Hfk. generalize fk at 1 3 as kn. intros kn Hkn0 Hw.
    induction kn as [|K rest IH]; cbn [wr_covered] in Hw; [discriminate|].
    apply Forall_cons_iff in Hkn0 as [HK Hrest].
    destruct K as [| | | | | |[kb kk] len| | |]; try (apply IH; assumption).
    cbn [kentry_ok] in HK. destruct HK as [Hflk Hs0]. unfold elenZ in Hflk, Hs0.
    match type of Hw with (if ?c then _ else _) = _ => destruct c eqn:Hc end.
    { destruct (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool eqn:H12; [|discriminate].
      apply andb_prop in H12 as [H1 H2].
      apply expr_eqb_eq in H1. apply Z.leb_le in H2.
      destruct (xlo fk len) as [l|] eqn:Hxl; [|discriminate]. apply Z.leb_le in Hc. rename Hc into H3.
      pose proof (xlo_sound segs E base fk len l Hall Hxl) as Hl.
      replace (adenot E a) with (Z_to_bv 64 (estart E (SA kb kk) + (a_off a - kk))).
      + apply Hs0; lia.
      + apply bv_eq. rewrite (flat_u E _ _ Hfl). unfold estart. cbn [a_base a_off]. rewrite <- H1.
        destruct Hfl as (?&?&?&?). unfold estart in *. rewrite u_small by lia. lia. }
    match type of Hw with (if ?c then _ else _) = _ => destruct c eqn:Hxi; [|apply IH; assumption] end.
    destruct (xinside_sound segs E base fk _ _ _ _ _ _ Hall Hxi) as [I1 I2].
    replace (SA (a_base a) (a_off a)) with a in I1, I2 by (destruct a; reflexivity).
    unfold elenZ in I2. cbn [edenot] in I2. rewrite u_lit64 in I2. unfold two64 in I2. rewrite Z.mod_small in I2 by lia.
    replace (adenot E a) with (Z_to_bv 64 (estart E (SA kb kk) + (estart E a - estart E (SA kb kk)))).
    + apply Hs0; lia.
    + apply bv_eq. rewrite (flat_u E _ _ Hfl).
      destruct Hfl as (?&?&?&?). rewrite u_small by lia. lia.
  - apply scs_denot_cons in Hsc as [Hok _]. cbn [sc_denot] in Hok. exact Hok.
Qed.

(* [comment removed for export] *)
Lemma resv_inval_sound : forall E r a r',
  resv_inval r a = Some r' ->
  resv_inval_w (resv_denot E r) (adenot E a) = resv_denot E r'.
Proof.
  intros E r a r' H. unfold resv_inval in H. destruct r as [ra|].
  - destruct (saddr_eqb ra a) eqn:Heq.
    + injection H as <-. apply saddr_eqb_eq in Heq. subst ra. cbn. rewrite Z.eqb_refl. reflexivity.
    + destruct (expr_eqb (a_base ra) (a_base a) && negb (Z.eqb ((a_off ra - a_off a) mod two64) 0))%bool eqn:Hc;
        [|discriminate].
      injection H as <-. apply andb_prop in Hc as [Hb Hne]. apply expr_eqb_eq in Hb.
      apply negb_true_iff in Hne. apply Z.eqb_neq in Hne.
      cbn [resv_denot resv_inval_w].
      destruct (Z.eqb (bv_unsigned (adenot E ra)) (bv_unsigned (adenot E a))) eqn:Hz; [|reflexivity].
      exfalso. apply Z.eqb_eq in Hz. apply Hne.
      unfold adenot, v_addi in Hz. rewrite Hb in Hz. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in Hz.
      unfold two64.
      set (u := bv_unsigned (edenot E (a_base a))) in *.
      replace (a_off ra - a_off a)%Z with ((u + a_off ra) - (u + a_off a))%Z by lia.
      rewrite Zminus_mod, Hz, Z.sub_diag. reflexivity.
  - injection H as <-. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma amo_alignedb_sound : forall E M kn e wd,
  know_ok segs E M kn -> amo_alignedb kn e wd = true ->
  (bv_unsigned (edenot E e) mod amo_bytes wd = 0)%Z.
Proof.
  intros E M kn e wd Hkn H. unfold amo_alignedb in H.
  set (k := match wd with AW => 2%Z | AD => 3%Z end) in H.
  destruct (lin_lowbits_kn kn e k) as [r|] eqn:Hl; [|discriminate].
  apply Z.eqb_eq in H. subst r.
  assert (Hk : (0 <= k <= 64)%Z) by (subst k; destruct wd; lia).
  destruct (lin_lowbits_kn_sound segs E M kn e k 0 Hkn Hk Hl) as [Hm _].
  replace (amo_bytes wd) with (2 ^ k)%Z by (subst k; destruct wd; reflexivity).
  exact Hm.
Qed.

(* [comment removed for export] *)
Lemma amo_val_alu32 : forall op o (a b : bv 32),
  amo_aluop op = Some (Some o) -> amo_val op a b = alu32 o a b.
Proof. intros op o a b H; destruct op; cbn in H; try discriminate; injection H as <-; reflexivity. Qed.

Lemma amo_val_alu64 : forall op o (a b : word),
  amo_aluop op = Some (Some o) -> amo_val op a b = alu64 o a b.
Proof. intros op o a b H; destruct op; cbn in H; try discriminate; injection H as <-; reflexivity. Qed.

Lemma amo_val_swap : forall op n (a b : bv n),
  amo_aluop op = Some None -> amo_val op a b = b.
Proof. intros op n a b H; destruct op; cbn in H; try discriminate; reflexivity. Qed.

(* [comment removed for export] *)
Lemma amo_store_bytes_newval : forall E M fk op aop wd bs vold src,
  know_ok segs E M fk ->
  amo_aluop op = Some aop ->
  length bs = msize_bytes (amo_sz wd) ->
  edenot E vold = load_result (amo_sz wd) true bs ->
  amo_store_bytes op wd bs (edenot E src)
  = word_to_le_bytes (msize_bytes (amo_sz wd)) (edenot E (amo_newval fk wd aop vold src)).
Proof.
  intros E M fk op aop wd bs vold src Hfk Hop Hlen Hold.
  unfold amo_store_bytes, amo_newval.
  destruct wd; cbn [amo_sz msize_bytes] in *.
  - (* [comment removed for export] *)
    destruct aop as [o|].
    + rewrite (mkAluwK_denot segs E M fk o vold src Hfk). cbn [edenot]. rewrite Hold.
      unfold load_result. rewrite low32_sext64_32.
      rewrite (amo_val_alu32 op o _ _ Hop).
      rewrite <- store_bytes_low32, low32_sext64_32. reflexivity.
    + rewrite (amo_val_swap op 32 _ _ Hop). apply store_bytes_low32.
  - (* [comment removed for export] *)
    destruct aop as [o|].
    + rewrite (mkAluK_denot segs E M fk o vold src Hfk). cbn [edenot]. rewrite Hold.
      unfold load_result. rewrite (amo_val_alu64 op o _ _ Hop). reflexivity.
    + rewrite (amo_val_swap op 64 _ _ Hop). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sym_step_sound_load : forall E base rom ss regs sz sx rd rs imm ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Load sz sx rd rs imm, 4%Z) ->
  sym_step segs (Load sz sx rd rs imm) ss scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  regs_ok E (s_regs ss) regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  exists ms', RiscvSemantics.step segs (mkstR regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
                                              (resv_denot E (s_resv ss))) = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof.
  intros E base rom ss regs sz sx rd rs imm ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
  set (mem := mem_denot E base (s_log ss)) in *.
  cbn [sym_step] in Hs.
  pose proof (facts_of_ok segs E base _ Hkn) as Hfk. set (fk := facts_of (s_know ss)) in *.
  set (n := msize_bytes sz) in Hs.
  set (sx' := match sz with SZ8 => false | _ => sx end) in Hs.
  set (a := to_saddrK fk (sr_get (s_regs ss) rs) (bv_signed imm)) in Hs.
  pose proof (msize_bytes_range sz) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
  assert (Hadr : adenot E a = v_addi (getr regs rs) (bv_signed imm)).
  { subst a. rewrite (to_saddrK_denot segs E base fk _ _ Hfk), Hregs. reflexivity. }
  assert (Hsx : sx' = eff_sx sz sx) by (subst sx'; destruct sz; reflexivity).
  destruct (sym_read segs ss fk scr a n sx') as [[[[v rscs] rscr] nx']|] eqn:Hr; [|discriminate].
  injection Hs as <- <- <-.
  destruct (sym_read_sound E base ss scr a n sx' v rscs rscr nx' Hr Hsc Hlf Hkn Hn1 Hn8)
    as [Hfl (bs & Hrd & Hlen & Hval)].
  rewrite Hadr in Hrd.
  eexists; split.
  - apply (stepR_load segs regs _ mem rom _ w sz sx rd rs imm bs Hf He Hd). rewrite msize_bytes_R. exact Hrd.
  - exists (if bv_eqb rd 0 then regs else regupd regs rd (load_result sz sx bs)).
    split; [cbn [s_pc s_log s_resv]; rewrite v_addi_lit; reflexivity|].
    cbn [s_regs s_log s_know]. split; [|split; [exact Hlf | exact Hkn]].
    apply regs_ok_upd; [exact Hregs|].
    rewrite load_result_val by exact Hlen. rewrite <- Hsx. fold n. symmetry. exact Hval.
Qed.

Lemma sym_step_sound_store : forall E base rom ss regs sz rs1 rs2 imm ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Store sz rs1 rs2 imm, 4%Z) ->
  sym_step segs (Store sz rs1 rs2 imm) ss scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  regs_ok E (s_regs ss) regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  exists ms', RiscvSemantics.step segs (mkstR regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
                                              (resv_denot E (s_resv ss))) = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof.
  intros E base rom ss regs sz rs1 rs2 imm ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
  set (mem := mem_denot E base (s_log ss)) in *.
  cbn [sym_step] in Hs.
  pose proof (facts_of_ok segs E base _ Hkn) as Hfk. set (fk := facts_of (s_know ss)) in *.
  set (n := msize_bytes sz) in *.
  set (a := to_saddrK fk (sr_get (s_regs ss) rs1) (bv_signed imm)) in *.
  destruct (resv_inval (s_resv ss) a) as [r'|] eqn:Hri; [|discriminate].
  injection Hs as <- <- <-.
  pose proof (msize_bytes_range sz) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
  assert (Hadr : adenot E a = v_addi (getr regs rs1) (bv_signed imm)).
  { subst a. rewrite (to_saddrK_denot segs E base fk _ _ Hfk), Hregs. reflexivity. }
  apply (flat_sc_sound segs E base fk _ _ _ Hfk Hn1 Hn8) in Hsc as [Hfl Hsc].
  pose proof (storeok_sc_sound E base fk a n Hfk Hfl Hn1 Hn8 Hsc) as Hok.
  assert (Hok' : RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) n = true).
  { rewrite <- Hadr. unfold mem. eapply store_ok_mono; [apply mem_denot_grows | exact Hok]. }
  eexists; split.
  - apply (stepR_store segs regs _ mem rom _ w sz rs1 rs2 imm Hf He Hd). rewrite msize_bytes_R. exact Hok'.
  - exists regs. split.
    + cbn [s_pc s_log s_resv]. rewrite (mem_denot_push E base _ _ _ _ Hlf Hfl). cbn [mem_denot]. rewrite v_addi_lit, msize_bytes_R. fold n.
      rewrite Hadr, (Hregs rs2), <- (resv_inval_sound E _ _ _ Hri), Hadr. reflexivity.
    + cbn [s_regs s_log s_know]. split; [exact Hregs|]. split; [|exact Hkn].
      apply log_flat_push; [exact Hn8 | exact Hfl | exact Hlf].
Qed.

Lemma sym_step_sound_lr : forall E base rom ss regs wd aq rl rd rs ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Lr wd aq rl rd rs, 4%Z) ->
  sym_step segs (Lr wd aq rl rd rs) ss scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  regs_ok E (s_regs ss) regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  exists ms', RiscvSemantics.step segs (mkstR regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
                                              (resv_denot E (s_resv ss))) = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof.
  intros E base rom ss regs wd aq rl rd rs ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
  set (mem := mem_denot E base (s_log ss)) in *.
  cbn [sym_step] in Hs.
  pose proof (facts_of_ok segs E base _ Hkn) as Hfk. set (fk := facts_of (s_know ss)) in *.
  set (n := msize_bytes (amo_sz wd)) in Hs.
  destruct (amo_alignedb fk (sr_get (s_regs ss) rs) wd) eqn:Hal; [|discriminate].
  set (a := to_saddrK fk (sr_get (s_regs ss) rs) 0) in Hs.
  pose proof (msize_bytes_range (amo_sz wd)) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
  assert (Hadr : adenot E a = getr regs rs).
  { subst a. rewrite (to_saddrK_denot segs E base fk _ _ Hfk), Hregs. apply v_addi_0. }
  destruct (sym_read segs ss fk scr a n (amo_sx wd)) as [[[[v rscs] rscr] nx']|] eqn:Hr; [|discriminate].
  injection Hs as <- <- <-.
  destruct (sym_read_sound E base ss scr a n (amo_sx wd) v rscs rscr nx' Hr Hsc Hlf Hkn Hn1 Hn8)
    as [Hfl (bs & Hrd & Hlen & Hval)].
  rewrite Hadr in Hrd.
  pose proof (amo_alignedb_sound E base fk _ wd Hfk Hal) as HA. rewrite <- (Hregs rs) in HA.
  eexists; split.
  - apply (stepR_lr segs regs _ mem rom _ w wd aq rl rd rs bs Hf He Hd HA). rewrite amo_nbytes_sz. exact Hrd.
  - exists (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs)).
    split; [cbn [s_pc s_log s_resv resv_denot]; rewrite v_addi_lit, Hadr; reflexivity|].
    cbn [s_regs s_log s_know]. split; [|split; [exact Hlf | exact Hkn]].
    apply regs_ok_upd; [exact Hregs|].
    rewrite amo_msize_sz. rewrite load_result_val by exact Hlen.
    replace (eff_sx (amo_sz wd) true) with (amo_sx wd) by (destruct wd; reflexivity).
    fold n. symmetry. exact Hval.
Qed.

Lemma sym_step_sound_sc : forall E base rom ss regs wd aq rl rd rs1 rs2 ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
  sym_step segs (Sc wd aq rl rd rs1 rs2) ss scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  regs_ok E (s_regs ss) regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  exists ms', RiscvSemantics.step segs (mkstR regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
                                              (resv_denot E (s_resv ss))) = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof.
  intros E base rom ss regs wd aq rl rd rs1 rs2 ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
  set (mem := mem_denot E base (s_log ss)) in *.
  cbn [sym_step] in Hs.
  pose proof (facts_of_ok segs E base _ Hkn) as Hfk. set (fk := facts_of (s_know ss)) in *.
  set (n := msize_bytes (amo_sz wd)) in *.
  destruct (amo_alignedb fk (sr_get (s_regs ss) rs1) wd) eqn:Hal; [|discriminate].
  set (a := to_saddrK fk (sr_get (s_regs ss) rs1) 0) in *.
  destruct (s_resv ss) as [r|] eqn:Hrv; [|discriminate].
  destruct (saddr_eqb r a) eqn:Heq; [|discriminate].
  apply saddr_eqb_eq in Heq. subst r.
  injection Hs as <- <- <-.
  pose proof (msize_bytes_range (amo_sz wd)) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
  assert (Hadr : adenot E a = getr regs rs1).
  { subst a. rewrite (to_saddrK_denot segs E base fk _ _ Hfk), Hregs. apply v_addi_0. }
  apply (flat_sc_sound segs E base fk _ _ _ Hfk Hn1 Hn8) in Hsc as [Hfl Hsc].
  pose proof (storeok_sc_sound E base fk a n Hfk Hfl Hn1 Hn8 Hsc) as Hok.
  assert (Hok' : RiscvSemantics.store_ok segs mem (getr regs rs1) n = true).
  { rewrite <- Hadr. unfold mem. eapply store_ok_mono; [apply mem_denot_grows | exact Hok]. }
  pose proof (amo_alignedb_sound E base fk _ wd Hfk Hal) as HA. rewrite <- (Hregs rs1) in HA.
  eexists; split.
  - cbn [resv_denot]. apply (stepR_sc_ok segs regs _ mem rom w wd aq rl rd rs1 rs2 _ Hf He Hd HA Hadr).
    rewrite amo_nbytes_sz. exact Hok'.
  - exists (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)). split.
    + cbn [s_pc s_log s_resv resv_denot]. rewrite (mem_denot_push E base _ _ _ _ Hlf Hfl). cbn [mem_denot]. rewrite v_addi_lit, amo_nbytes_sz. fold n.
      rewrite Hadr, (Hregs rs2). reflexivity.
    + cbn [s_regs s_log s_know]. split; [apply regs_ok_upd; [exact Hregs|reflexivity]|]. split; [|exact Hkn].
      apply log_flat_push; [exact Hn8 | exact Hfl | exact Hlf].
Qed.

Lemma sym_step_sound_amo : forall E base rom ss regs op wd aq rl rd rs1 rs2 ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Amo op wd aq rl rd rs1 rs2, 4%Z) ->
  sym_step segs (Amo op wd aq rl rd rs1 rs2) ss scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  regs_ok E (s_regs ss) regs -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  exists ms', RiscvSemantics.step segs (mkstR regs (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom
                                              (resv_denot E (s_resv ss))) = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof.
  intros E base rom ss regs op wd aq rl rd rs1 rs2 ss' scs scr scr' w Hf He Hd Hs Hsc Hregs Hlf Hkn.
  set (mem := mem_denot E base (s_log ss)) in *.
  cbn [sym_step] in Hs.
  pose proof (facts_of_ok segs E base _ Hkn) as Hfk. set (fk := facts_of (s_know ss)) in *.
  destruct (amo_aluop op) as [aop|] eqn:Hop; [|discriminate].
  set (n := msize_bytes (amo_sz wd)) in *.
  destruct (amo_alignedb fk (sr_get (s_regs ss) rs1) wd) eqn:Hal; [|discriminate].
  set (a := to_saddrK fk (sr_get (s_regs ss) rs1) 0) in *.
  destruct (resv_inval (s_resv ss) a) as [r'|] eqn:Hri; [|discriminate].
  destruct (sym_read segs ss fk scr a n (amo_sx wd)) as [[[[vold rscs] rscr] nx']|] eqn:Hr; [|discriminate].
  injection Hs as <- <- <-.
  pose proof (msize_bytes_range (amo_sz wd)) as Hnr. fold n in Hnr. destruct Hnr as [Hn1 Hn8].
  assert (Hadr : adenot E a = getr regs rs1).
  { subst a. rewrite (to_saddrK_denot segs E base fk _ _ Hfk), Hregs. apply v_addi_0. }
  apply scs_denot_app in Hsc as [Hsc Hsok].
  destruct (sym_read_sound E base ss scr a n (amo_sx wd) vold rscs rscr nx' Hr Hsc Hlf Hkn Hn1 Hn8)
    as [Hfl (bs & Hrd & Hlen & Hval)].
  pose proof (storeok_sc_sound E base fk a n Hfk Hfl Hn1 Hn8 Hsok) as Hok.
  assert (Hok' : RiscvSemantics.store_ok segs mem (getr regs rs1) n = true).
  { rewrite <- Hadr. unfold mem. eapply store_ok_mono; [apply mem_denot_grows | exact Hok]. }
  rewrite Hadr in Hrd.
  pose proof (amo_alignedb_sound E base fk _ wd Hfk Hal) as HA. rewrite <- (Hregs rs1) in HA.
  assert (Hold : edenot E vold = load_result (amo_sz wd) true bs).
  { rewrite load_result_val by exact Hlen.
    replace (eff_sx (amo_sz wd) true) with (amo_sx wd) by (destruct wd; reflexivity).
    fold n. symmetry. exact Hval. }
  eexists; split.
  - apply (stepR_amo segs regs _ mem rom _ w op wd aq rl rd rs1 rs2 bs Hf He Hd HA);
      rewrite amo_nbytes_sz; [exact Hrd | exact Hok'].
  - exists (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs)). split.
    + cbn [s_pc s_log s_resv]. rewrite (mem_denot_push E base _ _ _ _ Hlf Hfl). cbn [mem_denot]. rewrite v_addi_lit. fold n.
      rewrite Hadr, <- (resv_inval_sound E _ _ _ Hri), Hadr.
      rewrite (Hregs rs2), (amo_store_bytes_newval E base fk op aop wd bs vold _ Hfk Hop Hlen Hold).
      reflexivity.
    + cbn [s_regs s_log s_know]. split.
      * apply regs_ok_upd; [exact Hregs|]. rewrite amo_msize_sz. exact Hold.
      * split; [|exact Hkn]. apply log_flat_push; [exact Hn8 | exact Hfl | exact Hlf].
Qed.

(* [comment removed for export] *)
Ltac alu_case STEP DEN :=
  match goal with
  | Hs : SOk _ _ _ = SOk _ _ _ |- _ =>
      injection Hs as <- <- <-;
      eexists; split; [ STEP |];
      eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |];
      cbn [s_regs s_log s_know sset];
      match goal with
      | Hregs : regs_ok _ _ _, Hlf : log_flat _ _, Hkn : know_ok _ _ _ _ |- _ =>
          split; [ apply regs_ok_upd; [exact Hregs|]; DEN | split; [exact Hlf | exact Hkn] ]
      end
  end.

Lemma sym_step_soundR : forall E base rom ss ms i ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, 4%Z) ->
  sym_step segs i ss scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  st_okR E base rom ss ms ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof.
  intros E base rom ss ms i ss' scs scr scr' w Hf He Hd Hs Hsc (regs & -> & Hregs & Hlf & Hkn).
  destruct i;
    try (eapply sym_step_sound_load; eassumption);
    try (eapply sym_step_sound_store; eassumption);
    try (eapply sym_step_sound_lr; eassumption);
    try (eapply sym_step_sound_sc; eassumption);
    try (eapply sym_step_sound_amo; eassumption);
    set (mem := mem_denot E base (s_log ss)) in *;
    set (rv := resv_denot E (s_resv ss)) in *;
    cbn [sym_step] in Hs; try discriminate;
    pose proof (facts_of_ok segs E base _ Hkn) as Hfk; set (fk := facts_of (s_know ss)) in *.
  - (* [comment removed for export] *)
    alu_case ltac:(exact (stepR_lui segs regs _ mem rom rv w rd imm Hf He Hd))
             ltac:(cbn [edenot]; unfold v_lui; apply Z_to_bv64_u).
  - (* [comment removed for export] *)
    alu_case ltac:(exact (stepR_auipc segs regs _ mem rom rv w rd imm Hf He Hd))
             ltac:(cbn [edenot]; rewrite Z_to_bv64_u; symmetry; apply v_auipc_lit).
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (stepR_jal_link segs regs _ mem rom rv w rd imm Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; rewrite btgt_lit; symmetry; apply Z_to_bv64_u |].
    cbn [s_regs s_log s_know sset]. split; [| split; [exact Hlf | exact Hkn]].
    apply regs_ok_upd; [exact Hregs|]. cbn [edenot]. symmetry. apply v_addi_lit.
  - (* [comment removed for export] *)
    pose proof (conc_expr_sound segs E base fk (sr_get (s_regs ss) rs1) Hfk) as Hce.
    destruct (conc_expr fk (sr_get (s_regs ss) rs1)) as [z| | | | | | |] eqn:Hg; try discriminate.
    injection Hs as <- <- <-.
    eexists; split; [ exact (stepR_jalr segs regs _ mem rom rv w rd rs1 imm Hf He Hd) |].
    eexists; split.
    + f_equal. cbn [s_pc sset]. unfold v_jalr.
      specialize (Hregs rs1) as Hg1. rewrite <- Hce in Hg1. cbn [edenot] in Hg1.
      rewrite Hg1. rewrite Z_to_bv64_mod. exact (jalr_tgt_lit z (bv_signed imm)).
    + cbn [s_regs s_log s_know sset]. split; [| split; [exact Hlf | exact Hkn]].
      apply regs_ok_upd; [exact Hregs|]. cbn [edenot]. symmetry. apply v_addi_lit.
  - (* [comment removed for export] *)
    set (tk := bv_unsigned (Z_to_bv 64 (s_pc ss + bv_signed imm))) in Hs.
    assert (Hcond : forall t, branch_taken c (getr regs rs1) (getr regs rs2) = t ->
              exists ms', RiscvSemantics.step segs (mkstR regs (Z_to_bv 64 (s_pc ss)) mem rom rv) = MachineOk ms'
                /\ st_okR E base rom (sjump ss (if t then tk else (s_pc ss + 4)%Z)) ms').
    { intros t Ht. destruct t.
      - eexists; split; [exact (stepR_branch_tk_gen segs regs _ mem rom rv w c rs1 rs2 imm Hf He Hd Ht)|].
        eexists; split; [| split; [exact Hregs | split; [exact Hlf | exact Hkn]]].
        f_equal. cbn [s_pc sjump]. rewrite btgt_lit. subst tk. symmetry. apply Z_to_bv64_u.
      - eexists; split; [exact (stepR_branch_ft_gen segs regs _ mem rom rv w c rs1 rs2 imm Hf He Hd Ht)|].
        eexists; split; [| split; [exact Hregs | split; [exact Hlf | exact Hkn]]].
        f_equal. cbn [s_pc sjump]. apply v_addi_lit. }
    destruct (decide_branch fk c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)) as [t|] eqn:Hdb.
    + (* [comment removed for export] *)
      injection Hs as <- <- <-. apply Hcond. rewrite (Hregs rs1), (Hregs rs2).
      eapply decide_branch_sound; [exact Hfk | exact Hdb].
    + destruct (decide_branch fk c (conc_expr fk (sr_get (s_regs ss) rs1))
                                            (conc_expr fk (sr_get (s_regs ss) rs2))) as [t|] eqn:Hdb2.
      * (* [comment removed for export] *)
        injection Hs as <- <- <-. apply Hcond. rewrite (Hregs rs1), (Hregs rs2).
        rewrite <- (conc_expr_sound segs E base fk (sr_get (s_regs ss) rs1) Hfk).
        rewrite <- (conc_expr_sound segs E base fk (sr_get (s_regs ss) rs2) Hfk).
        eapply decide_branch_sound; [exact Hfk | exact Hdb2].
      * destruct (enum_branch fk c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)) as [t|] eqn:Hdb3.
        { (* [comment removed for export] *)
          injection Hs as <- <- <-. apply Hcond. rewrite (Hregs rs1), (Hregs rs2).
          eapply enum_branch_sound; [exact Hfk | exact Hdb3]. }
        (* [comment removed for export] *)
        destruct (sc_dirs scr) as [|t dirs'] eqn:Hdirs; [discriminate|].
        injection Hs as <- <- <-. apply Hcond.
        apply scs_denot_cons in Hsc as [Hbr _]. cbn [sc_denot] in Hbr.
        rewrite (Hregs rs1), (Hregs rs2). exact Hbr.
  - (* [comment removed for export] *)
    alu_case ltac:(exact (stepR_opimm_gen segs regs _ mem rom rv w op rd rs1 imm Hf He Hd))
             ltac:(rewrite (mkAluK_denot segs E base _ _ _ _ Hfk); cbn [edenot]; rewrite <- Hregs, sext64_lit; reflexivity).
  - (* [comment removed for export] *)
    alu_case ltac:(exact (stepR_shiftimm_gen segs regs _ mem rom rv w op rd rs1 shamt Hf He Hd))
             ltac:(rewrite (mkAluK_denot segs E base _ _ _ _ Hfk); cbn [edenot]; rewrite <- Hregs, zext64_lit; reflexivity).
  - (* [comment removed for export] *)
    alu_case ltac:(exact (stepR_op_gen segs regs _ mem rom rv w op rd rs1 rs2 Hf He Hd))
             ltac:(rewrite (mkAluK_denot segs E base _ _ _ _ Hfk); rewrite <- !Hregs; reflexivity).
  - (* [comment removed for export] *)
    alu_case ltac:(exact (stepR_opimm32_gen segs regs _ mem rom rv w rd rs1 imm Hf He Hd))
             ltac:(lazymatch goal with |- _ = ?r => change (edenot E (mkAluwK fk ALU_ADD (sr_get (s_regs ss) rs1) (ELit (bv_signed imm))) = r) end;
                   rewrite (mkAluwK_denot segs E base _ _ _ _ Hfk); cbn [edenot]; rewrite <- Hregs, sext32_low32; reflexivity).
  - (* [comment removed for export] *)
    alu_case ltac:(exact (stepR_shiftimm32_gen segs regs _ mem rom rv w op rd rs1 shamt Hf He Hd))
             ltac:(rewrite mkAluw_denot; cbn [edenot]; rewrite <- Hregs, zext32_low32; reflexivity).
  - (* [comment removed for export] *)
    alu_case ltac:(exact (stepR_op32_gen segs regs _ mem rom rv w op rd rs1 rs2 Hf He Hd))
             ltac:(lazymatch goal with |- _ = ?r => change (edenot E (mkAluwK fk op (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)) = r) end;
                   rewrite (mkAluwK_denot segs E base _ _ _ _ Hfk); rewrite <- !Hregs; reflexivity).
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (stepR_fence segs regs _ mem rom rv w _ _ _ _ _ Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sjump]; apply v_addi_lit |].
    cbn [s_regs s_log s_know sjump]. split; [exact Hregs | split; [exact Hlf | exact Hkn]].
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (stepR_fencei segs regs _ mem rom rv w _ _ _ Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sjump]; apply v_addi_lit |].
    cbn [s_regs s_log s_know sjump]. split; [exact Hregs | split; [exact Hlf | exact Hkn]].
  - (* [comment removed for export] *)
    alu_case ltac:(exact (stepR_mul_gen segs regs _ mem rom rv w op rd rs1 rs2 Hf He Hd))
             ltac:(rewrite (mkMdK_denot segs E base _ _ _ _ Hfk); rewrite <- !Hregs; reflexivity).
  - (* [comment removed for export] *)
    alu_case ltac:(exact (stepR_mul32_gen segs regs _ mem rom rv w op rd rs1 rs2 Hf He Hd))
             ltac:(rewrite mkMdw_denot; rewrite <- !Hregs; reflexivity).
Qed.

(* [comment removed for export] *)
Lemma sym_step_sound : forall E base rom ss ms i ss' scs scr scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, 4%Z) ->
  sym_step segs i (clr ss) scr = SOk ss' scs scr' ->
  scs_denot segs base E scs ->
  st_ok E base rom ss ms ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms'
              /\ st_okR E base rom ss' ms'.
Proof.
  intros E base rom ss ms i ss' scs scr scr' w Hf He Hd Hs Hsc Hst.
  exact (sym_step_soundR E base rom (clr ss) ms i ss' scs scr scr' w Hf He Hd Hs Hsc (st_ok_R E base rom ss ms Hst)).
Qed.

End StepSound.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sidecond_eqb_eq : forall x y, sidecond_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y; cbn [sidecond_eqb] in H; try discriminate;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    repeat match goal with
      | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
      | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      end; subst; reflexivity.
Qed.

Lemma sc_mem_In : forall x l, sc_mem x l = true -> In x l.
Proof.
  induction l as [|y t IH]; cbn [sc_mem]; intros H; [discriminate|].
  apply orb_prop in H as [H|H].
  - left. symmetry. apply sidecond_eqb_eq. exact H.
  - right. apply IH. exact H.
Qed.

Lemma sc_add_denot : forall segs base E news acc,
  scs_denot segs base E (sc_add news acc) ->
  scs_denot segs base E news /\ scs_denot segs base E acc.
Proof.
  intros segs base E news. induction news as [|x t IH]; intros acc H; cbn [sc_add] in H.
  - split; [constructor | exact H].
  - destruct (sc_mem x acc) eqn:Hm.
    + destruct (IH acc H) as [Ht Hacc]. split; [|exact Hacc].
      constructor; [|exact Ht].
      apply sc_mem_In in Hm. unfold scs_denot in Hacc. rewrite Forall_forall in Hacc. apply Hacc. exact Hm.
    + destruct (IH (x :: acc) H) as [Ht Hxa]. apply scs_denot_cons in Hxa as [Hx Hacc].
      split; [constructor; assumption | exact Hacc].
Qed.

Section ExecSound.
Variable segs : list Segment.

(* [comment removed for export] *)
Local Ltac fetch_cases Hstop :=
  lazymatch goal with
  | |- context [fetch_word segs (Z_to_bv 64 (s_pc ?ss))] =>
      destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|exact Hstop];
      destruct (is_ecall w) eqn:He; [exact Hstop|];
      destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact Hstop];
      destruct (Z.eqb sz 4) eqn:Hsz; cbn [negb]; [|exact Hstop];
      apply Z.eqb_eq in Hsz; subst sz
  end.

(* [comment removed for export] *)
Lemma sym_exec_go_sound : forall fuel first stops scr ss acc ck E base rom,
  sym_exec_go segs fuel first stops scr ss acc ck = ck \/
  (let '(r, accr, _) := sym_exec_go segs fuel first stops scr ss acc ck in
   s_resv r = None /\
   (scs_denot segs base E accr -> scs_denot segs base E acc) /\
   (forall ms, scs_denot segs base E accr -> st_okR segs E base rom ss ms ->
      exists mr, msteps segs ms mr /\ st_okR segs E base rom r mr)).
Proof.
  induction fuel as [|f IH]; intros first stops scr ss acc ck E base rom.
  - cbn [sym_exec_go]. destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
    split; [apply s_clean_None; exact Hc|]. split; [intros H; exact H|].
    intros ms _ Hst. exists ms. split; [apply mst_refl|exact Hst].
  - assert (Hstop : (if s_clean ss then (ss, acc, scr) else ck) = ck \/
            (let '(r, accr, _) := (if s_clean ss then (ss, acc, scr) else ck) in
             s_resv r = None /\
             (scs_denot segs base E accr -> scs_denot segs base E acc) /\
             (forall ms, scs_denot segs base E accr -> st_okR segs E base rom ss ms ->
                exists mr, msteps segs ms mr /\ st_okR segs E base rom r mr))).
    { destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
      split; [apply s_clean_None; exact Hc|]. split; [intros H; exact H|].
      intros ms _ Hst. exists ms. split; [apply mst_refl|exact Hst]. }
    cbn [sym_exec_go].
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact Hstop|].
    fetch_cases Hstop.
    destruct (sym_step segs i ss scr) as [ss2 scs2 scr2|] eqn:Hstep; [|exact Hstop].
    cbv zeta.
    set (ck' := if s_clean ss2 then (ss2, sc_add scs2 acc, scr2) else ck).
    specialize (IH false stops scr2 ss2 (sc_add scs2 acc) ck' E base rom).
    destruct (sym_exec_go segs f false stops scr2 ss2 (sc_add scs2 acc) ck') as [[r accr] scrr] eqn:Hgo.
    destruct IH as [Hck|(Hr & Hacc & Hrun)].
    + (* [comment removed for export] *)
      subst ck'. destruct (s_clean ss2) eqn:Hc2.
      * right. injection Hck as -> -> ->.
        split; [apply s_clean_None; exact Hc2|].
        split; [intros H; apply sc_add_denot in H as [_ H]; exact H|].
        intros ms Hsc Hst. apply sc_add_denot in Hsc as [Hsc2 _].
        destruct (sym_step_soundR segs E base rom ss ms i ss2 scs2 scr scr2 w Hf He Hd Hstep Hsc2 Hst)
          as (msA & HstepA & HstA).
        exists msA. split; [|exact HstA].
        eapply mst_step; [destruct Hst as (rr & -> & _); reflexivity | exact HstepA | apply mst_refl].
      * left. exact Hck.
    + right. split; [exact Hr|].
      split; [intros H; apply Hacc in H; apply sc_add_denot in H as [_ H]; exact H|].
      intros ms Hsc Hst.
      pose proof (Hacc Hsc) as Hacc'. apply sc_add_denot in Hacc' as [Hsc2 _].
      destruct (sym_step_soundR segs E base rom ss ms i ss2 scs2 scr scr2 w Hf He Hd Hstep Hsc2 Hst)
        as (msA & HstepA & HstA).
      destruct (Hrun msA Hsc HstA) as (mr & Hmr & Hstr).
      exists mr. split; [|exact Hstr].
      eapply mst_step; [destruct Hst as (rr & -> & _); reflexivity | exact HstepA | exact Hmr].
Qed.

Lemma sym_exec_acc : forall fuel first stops scr ss acc E base,
  match sym_exec segs fuel first stops scr ss acc with
  | (ss', scs, scr') => scs_denot segs base E scs -> scs_denot segs base E acc
  end.
Proof.
  intros fuel first stops scr ss acc E base. unfold sym_exec.
  destruct (sym_exec_go_sound fuel first stops scr (clr ss) acc (clr ss, acc, scr) E base (fun _ => None))
    as [Hck|H].
  - rewrite Hck. intros HH; exact HH.
  - destruct (sym_exec_go segs fuel first stops scr (clr ss) acc (clr ss, acc, scr)) as [[r accr] scrr].
    destruct H as (_ & Hacc & _). exact Hacc.
Qed.

(* [comment removed for export] *)
Theorem sym_exec_soundR : forall fuel first stops scr ss acc ss' scs scr' E base rom ms,
  sym_exec segs fuel first stops scr ss acc = (ss', scs, scr') ->
  scs_denot segs base E scs ->
  st_ok segs E base rom ss ms ->
  s_resv ss' = None /\ exists ms', msteps segs ms ms' /\ st_okR segs E base rom ss' ms'.
Proof.
  intros fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst. unfold sym_exec in Hex.
  destruct (sym_exec_go_sound fuel first stops scr (clr ss) acc (clr ss, acc, scr) E base rom) as [Hck|H].
  - rewrite Hex in Hck. injection Hck as -> -> ->. split; [reflexivity|].
    exists ms. split; [apply mst_refl | apply st_ok_R; exact Hst].
  - rewrite Hex in H. destruct H as (Hr & _ & Hrun). split; [exact Hr|].
    apply (Hrun ms Hsc). apply st_ok_R. exact Hst.
Qed.

Theorem sym_exec_sound : forall fuel first stops scr ss acc ss' scs scr' E base rom ms,
  sym_exec segs fuel first stops scr ss acc = (ss', scs, scr') ->
  scs_denot segs base E scs ->
  st_ok segs E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok segs E base rom ss' ms'.
Proof.
  intros fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst.
  destruct (sym_exec_soundR fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst)
    as (Hr & ms' & Hms & Hst').
  exists ms'. split; [exact Hms | apply st_okR_ok; assumption].
Qed.

(* [comment removed for export] *)
Theorem sym_exec_ex : forall fuel first stops scr ss acc ss' scs scr' E base rom ms,
  sym_exec segs fuel first stops scr ss acc = (ss', scs, scr') ->
  scs_denot segs base E scs ->
  st_ok segs E base rom ss ms ->
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
  intros fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst.
  destruct (sym_exec_sound fuel first stops scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst)
    as (ms' & Hms & (R & Heq & Hregs & Hlf & _)).
  exists R. split; [exact Hregs|]. split; [exact Hlf|]. rewrite <- Heq. exact Hms.
Qed.

Theorem sym_exec_resv : forall fuel first stops scr ss acc,
  s_resv (fst (fst (sym_exec segs fuel first stops scr ss acc))) = None.
Proof.
  intros fuel first stops scr ss acc. unfold sym_exec.
  destruct (sym_exec_go_sound fuel first stops scr (clr ss) acc (clr ss, acc, scr)
              (Env (fun _ => Z_to_bv 64 0) (fun _ => [])) (fun _ => None) (fun _ => None)) as [Hck|H].
  - rewrite Hck. reflexivity.
  - destruct (sym_exec_go segs fuel first stops scr (clr ss) acc (clr ss, acc, scr)) as [[r accr] scrr].
    destruct H as (Hr & _). exact Hr.
Qed.

(* [comment removed for export] *)
Lemma sym_execS_go_sound : forall fuel first stops ss ck E base rom,
  sym_execS_go segs fuel first stops ss ck = ck \/
  (let r := sym_execS_go segs fuel first stops ss ck in
   s_resv r = None /\
   (forall ms, st_okR segs E base rom ss ms -> exists mr, msteps segs ms mr /\ st_okR segs E base rom r mr)).
Proof.
  induction fuel as [|f IH]; intros first stops ss ck E base rom.
  - cbn [sym_execS_go]. destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
    split; [apply s_clean_None; exact Hc|].
    intros ms Hst. exists ms. split; [apply mst_refl|exact Hst].
  - assert (Hstop : (if s_clean ss then ss else ck) = ck \/
            (let r := (if s_clean ss then ss else ck) in
             s_resv r = None /\
             (forall ms, st_okR segs E base rom ss ms -> exists mr, msteps segs ms mr /\ st_okR segs E base rom r mr))).
    { destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
      split; [apply s_clean_None; exact Hc|].
      intros ms Hst. exists ms. split; [apply mst_refl|exact Hst]. }
    cbn [sym_execS_go].
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact Hstop|].
    fetch_cases Hstop.
    destruct (sym_step segs i ss scr_nil) as [ss2 scs2 scr2|] eqn:Hstep; [|exact Hstop].
    destruct scs2 as [|x l]; [|exact Hstop].
    set (ck' := if s_clean ss2 then ss2 else ck).
    specialize (IH false stops ss2 ck' E base rom).
    destruct IH as [Hck|(Hr & Hrun)].
    + subst ck'. destruct (s_clean ss2) eqn:Hc2.
      * right. rewrite Hck. split; [apply s_clean_None; exact Hc2|].
        intros ms Hst.
        destruct (sym_step_soundR segs E base rom ss ms i ss2 [] scr_nil scr2 w Hf He Hd Hstep ltac:(constructor) Hst)
          as (msA & HstepA & HstA).
        exists msA. split; [|exact HstA].
        eapply mst_step; [destruct Hst as (rr & -> & _); reflexivity | exact HstepA | apply mst_refl].
      * left. exact Hck.
    + right. split; [exact Hr|].
      intros ms Hst.
      destruct (sym_step_soundR segs E base rom ss ms i ss2 [] scr_nil scr2 w Hf He Hd Hstep ltac:(constructor) Hst)
        as (msA & HstepA & HstA).
      destruct (Hrun msA HstA) as (mr & Hmr & Hstr).
      exists mr. split; [|exact Hstr].
      eapply mst_step; [destruct Hst as (rr & -> & _); reflexivity | exact HstepA | exact Hmr].
Qed.

Theorem sym_execS_soundR : forall fuel first stops ss E base rom ms,
  st_ok segs E base rom ss ms ->
  s_resv (sym_execS segs fuel first stops ss) = None /\
  exists ms', msteps segs ms ms' /\ st_okR segs E base rom (sym_execS segs fuel first stops ss) ms'.
Proof.
  intros fuel first stops ss E base rom ms Hst. unfold sym_execS.
  destruct (sym_execS_go_sound fuel first stops (clr ss) (clr ss) E base rom) as [Hck|(Hr & Hrun)].
  - rewrite Hck. split; [reflexivity|]. exists ms. split; [apply mst_refl | apply st_ok_R; exact Hst].
  - split; [exact Hr|]. apply Hrun. apply st_ok_R. exact Hst.
Qed.

Theorem sym_execS_sound : forall fuel first stops ss E base rom ms,
  st_ok segs E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok segs E base rom (sym_execS segs fuel first stops ss) ms'.
Proof.
  intros fuel first stops ss E base rom ms Hst.
  destruct (sym_execS_soundR fuel first stops ss E base rom ms Hst) as (Hr & ms' & Hms & Hst').
  exists ms'. split; [exact Hms | apply st_okR_ok; assumption].
Qed.

(* [comment removed for export] *)
Theorem sym_execS_ex : forall fuel first stops ss E base rom ms,
  st_ok segs E base rom ss ms ->
  let ss' := sym_execS segs fuel first stops ss in
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ know_ok segs E base (s_know ss')
         /\ msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
  intros fuel first stops ss E base rom ms Hst.
  destruct (sym_execS_sound fuel first stops ss E base rom ms Hst) as (ms' & Hms & (R & Heq & Hregs & Hlf & Hkn)).
  exists R. split; [exact Hregs|]. split; [exact Hlf|]. split; [exact Hkn|]. rewrite <- Heq. exact Hms.
Qed.

Theorem sym_execS_resv : forall fuel first stops ss,
  s_resv (sym_execS segs fuel first stops ss) = None.
Proof.
  intros fuel first stops ss. unfold sym_execS.
  destruct (sym_execS_go_sound fuel first stops (clr ss) (clr ss)
              (Env (fun _ => Z_to_bv 64 0) (fun _ => [])) (fun _ => None) (fun _ => None)) as [Hck|(Hr & _)].
  - rewrite Hck. reflexivity.
  - exact Hr.
Qed.

(* [comment removed for export] *)
Lemma sym_execT_go_sound : forall t fuel first stops ss ck E base rom,
  itab_sound segs t ->
  sym_execT_go segs t fuel first stops ss ck = ck \/
  (let r := sym_execT_go segs t fuel first stops ss ck in
   s_resv r = None /\
   (forall ms, st_okR segs E base rom ss ms -> exists mr, msteps segs ms mr /\ st_okR segs E base rom r mr)).
Proof.
  intros t fuel. induction fuel as [|f IH]; intros first stops ss ck E base rom Ht.
  - cbn [sym_execT_go]. destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
    split; [apply s_clean_None; exact Hc|].
    intros ms Hst. exists ms. split; [apply mst_refl|exact Hst].
  - assert (Hstop : (if s_clean ss then ss else ck) = ck \/
            (let r := (if s_clean ss then ss else ck) in
             s_resv r = None /\
             (forall ms, st_okR segs E base rom ss ms -> exists mr, msteps segs ms mr /\ st_okR segs E base rom r mr))).
    { destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
      split; [apply s_clean_None; exact Hc|].
      intros ms Hst. exists ms. split; [apply mst_refl|exact Hst]. }
    cbn [sym_execT_go].
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact Hstop|].
    destruct (itab_lookup t (s_pc ss)) as [i|] eqn:Hl; [|exact Hstop].
    pose proof (Ht _ _ Hl) as Hen. unfold itab_entry in Hen.
    destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|discriminate].
    destruct (is_ecall w) eqn:Hec; [discriminate|].
    destruct (decode_any w) as [[i' sz]|] eqn:Hd; [|discriminate].
    destruct (Z.eqb sz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst sz.
    injection Hen as ->.
    destruct (sym_step segs i ss scr_nil) as [ss2 scs2 scr2|] eqn:Hstep; [|exact Hstop].
    destruct scs2 as [|x l]; [|exact Hstop].
    set (ck' := if s_clean ss2 then ss2 else ck).
    specialize (IH false stops ss2 ck' E base rom Ht).
    destruct IH as [Hck|(Hr & Hrun)].
    + subst ck'. destruct (s_clean ss2) eqn:Hc2.
      * right. rewrite Hck. split; [apply s_clean_None; exact Hc2|].
        intros ms Hst.
        destruct (sym_step_soundR segs E base rom ss ms i ss2 [] scr_nil scr2 w Hf Hec Hd Hstep ltac:(constructor) Hst)
          as (msA & HstepA & HstA).
        exists msA. split; [|exact HstA].
        eapply mst_step; [destruct Hst as (rr & -> & _); reflexivity | exact HstepA | apply mst_refl].
      * left. exact Hck.
    + right. split; [exact Hr|].
      intros ms Hst.
      destruct (sym_step_soundR segs E base rom ss ms i ss2 [] scr_nil scr2 w Hf Hec Hd Hstep ltac:(constructor) Hst)
        as (msA & HstepA & HstA).
      destruct (Hrun msA HstA) as (mr & Hmr & Hstr).
      exists mr. split; [|exact Hstr].
      eapply mst_step; [destruct Hst as (rr & -> & _); reflexivity | exact HstepA | exact Hmr].
Qed.

Theorem sym_execT_soundR : forall t fuel first stops ss E base rom ms,
  itab_sound segs t ->
  st_ok segs E base rom ss ms ->
  s_resv (sym_execT segs t fuel first stops ss) = None /\
  exists ms', msteps segs ms ms' /\ st_okR segs E base rom (sym_execT segs t fuel first stops ss) ms'.
Proof.
  intros t fuel first stops ss E base rom ms Ht Hst. unfold sym_execT.
  destruct (sym_execT_go_sound t fuel first stops (clr ss) (clr ss) E base rom Ht) as [Hck|(Hr & Hrun)].
  - rewrite Hck. split; [reflexivity|]. exists ms. split; [apply mst_refl | apply st_ok_R; exact Hst].
  - split; [exact Hr|]. apply Hrun. apply st_ok_R. exact Hst.
Qed.

Theorem sym_execT_sound : forall t fuel first stops ss E base rom ms,
  itab_sound segs t ->
  st_ok segs E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok segs E base rom (sym_execT segs t fuel first stops ss) ms'.
Proof.
  intros t fuel first stops ss E base rom ms Ht Hst.
  destruct (sym_execT_soundR t fuel first stops ss E base rom ms Ht Hst) as (Hr & ms' & Hms & Hst').
  exists ms'. split; [exact Hms | apply st_okR_ok; assumption].
Qed.

Theorem sym_execT_ex : forall t fuel first stops ss E base rom ms,
  itab_sound segs t ->
  st_ok segs E base rom ss ms ->
  let ss' := sym_execT segs t fuel first stops ss in
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ know_ok segs E base (s_know ss')
         /\ msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
  intros t fuel first stops ss E base rom ms Ht Hst.
  destruct (sym_execT_sound t fuel first stops ss E base rom ms Ht Hst) as (ms' & Hms & (R & Heq & Hregs & Hlf & Hkn)).
  exists R. split; [exact Hregs|]. split; [exact Hlf|]. split; [exact Hkn|]. rewrite <- Heq. exact Hms.
Qed.

Theorem sym_execT_resv : forall t fuel first stops ss,
  itab_sound segs t ->
  s_resv (sym_execT segs t fuel first stops ss) = None.
Proof.
  intros t fuel first stops ss Ht. unfold sym_execT.
  destruct (sym_execT_go_sound t fuel first stops (clr ss) (clr ss)
              (Env (fun _ => Z_to_bv 64 0) (fun _ => [])) (fun _ => None) (fun _ => None) Ht) as [Hck|(Hr & _)].
  - rewrite Hck. reflexivity.
  - exact Hr.
Qed.

End ExecSound.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section XSound.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition eagree (b : nat) (E E' : env) : Prop :=
  (forall n, (n < b)%nat -> ev E n = ev E' n) /\ eb E = eb E'.

Definition eupd (E : env) (i : nat) (v : word) : env :=
  Env (fun n => if Nat.eqb n i then v else ev E n) (eb E).

Lemma eagree_refl : forall b E, eagree b E E.
Proof. intros b E. split; [intros; reflexivity | reflexivity]. Qed.

Lemma eagree_sym : forall b E E', eagree b E E' -> eagree b E' E.
Proof. intros b E E' [H1 H2]. split; [intros n Hn; symmetry; apply H1; exact Hn | symmetry; exact H2]. Qed.

Lemma eagree_trans : forall b E1 E2 E3, eagree b E1 E2 -> eagree b E2 E3 -> eagree b E1 E3.
Proof.
  intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [|congruence].
  intros n Hn. rewrite (A1 n Hn). apply A2. exact Hn.
Qed.

Lemma eagree_le : forall b b' E E', eagree b' E E' -> (b <= b')%nat -> eagree b E E'.
Proof. intros b b' E E' [A B] Hle. split; [|exact B]. intros n Hn. apply A. lia. Qed.

Lemma eagree_upd : forall E i v, eagree i E (eupd E i v).
Proof.
  intros E i v. split; [|reflexivity]. intros n Hn. cbn [ev eupd].
  destruct (Nat.eqb n i) eqn:Hni; [apply Nat.eqb_eq in Hni; lia | reflexivity].
Qed.

Lemma eupd_at : forall E i v, ev (eupd E i v) i = v.
Proof. intros E i v. cbn [ev eupd]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma edenot_evars_lt : forall b E E' e,
  eagree b E E' -> evars_lt b e = true -> edenot E e = edenot E' e.
Proof.
  intros b E E' e [HA HB]. induction e; cbn [evars_lt edenot]; intros H.
  - reflexivity.
  - apply HA. apply Nat.ltb_lt. exact H.
  - apply andb_prop in H as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - rewrite (IHe H). reflexivity.
  - rewrite HB. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition st_okX (E : env) (base rom : word -> option byte) (ss : sym_state) (ms : machine_state) : Prop :=
  forall E', eagree (s_next ss) E E' -> st_okR segs E' base rom ss ms.

Lemma st_okX_R : forall E base rom ss ms, st_okX E base rom ss ms -> st_okR segs E base rom ss ms.
Proof. intros E base rom ss ms H. apply H. apply eagree_refl. Qed.

Lemma st_okX_agree : forall E E' base rom ss ms,
  st_okX E base rom ss ms -> eagree (s_next ss) E E' -> st_okX E' base rom ss ms.
Proof.
  intros E E' base rom ss ms H Ha E'' Ha''. apply H. eapply eagree_trans; [exact Ha | exact Ha''].
Qed.

Lemma st_okX_clr : forall E base rom ss ms,
  (forall E', eagree (s_next ss) E E' -> st_ok segs E' base rom ss ms) -> st_okX E base rom (clr ss) ms.
Proof. intros E base rom ss ms H E' Ha. apply st_ok_R. apply H. exact Ha. Qed.

(* [comment removed for export] *)
Lemma st_okR_parts : forall E base rom ss ms,
  st_okR segs E base rom ss ms ->
  regs_ok E (s_regs ss) (ms_regs ms) /\ ms_mem ms = mem_denot E base (s_log ss)
  /\ log_flat E (s_log ss) /\ know_ok segs E base (s_know ss)
  /\ ms = mkstR (ms_regs ms) (Z_to_bv 64 (s_pc ss)) (mem_denot E base (s_log ss)) rom (resv_denot E (s_resv ss)).
Proof.
  intros E base rom ss ms (regs & -> & HR & HL & HK). cbn [ms_regs ms_mem]. repeat split; assumption.
Qed.

(* [comment removed for export] *)

Definition rd1 (mem : word -> option byte) (x : word) : option byte :=
  match mem x with Some b => Some b | None => seg_rom segs x end.

Lemma rdn_defined : forall mem n (a : word),
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall j, (j < n)%nat -> rd1 mem (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None) ->
  exists bs, rdn segs mem a n = Some bs /\ length bs = n.
Proof.
  intros mem n. induction n as [|n IH]; intros a Hnw Hall.
  - exists []. split; reflexivity.
  - cbn [rdn].
    pose proof (Hall 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0.
    unfold rd1 in H0.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Hb; [|exfalso; exact (H0 eq_refl)].
    destruct n as [|n'].
    + exists [b]. split; reflexivity.
    + assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
      destruct (IH (a + 1)) as (bs & Hbs & Hlen); [rewrite Hu1; lia | | ].
      { intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
        apply Hall. lia. }
      rewrite Hbs. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

Lemma rdn_rd1 : forall mem n (a : word) bs j,
  rdn segs mem a n = Some bs -> (j < n)%nat ->
  rd1 mem (a + nat_to_word j) <> None.
Proof.
  intros mem n a bs j H Hj.
  pose proof (rdn_nth segs mem n a bs j H Hj) as H1.
  unfold rd1. cbn [rdn] in H1.
  destruct (match mem (a + nat_to_word j) with Some b => Some b | None => seg_rom segs (a + nat_to_word j) end); [discriminate|discriminate].
Qed.

(* [comment removed for export] *)
Lemma zf_covers_sound : forall E M0 allkn rb rk n kb kk len,
  know_ok segs E M0 allkn -> (n <= 8)%nat ->
  zf_covers allkn rb rk n kb kk len = true ->
  (estart E (SA kb kk) <= estart E (SA rb rk))%Z
  /\ (estart E (SA rb rk) + Z.of_nat n <= estart E (SA kb kk) + elenZ E len)%Z.
Proof.
  intros E M0 allkn rb rk n kb kk len Hall Hn8 H. unfold zf_covers in H.
  apply orb_prop in H as [H|H].
  - destruct len as [l0| | | | | | |]; try discriminate.
    destruct (rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)) as [d| | |] eqn:Hrel; try discriminate.
    destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (Heqb & Hd & Hkk & Hrn & Hst).
    rewrite elenZ_lit. unfold estart in *; cbn [a_base a_off] in *. subst. lia.
  - pose proof (xinside_sound segs E M0 allkn _ _ _ _ _ _ Hall H) as [A B].
    rewrite elenZ_elen in B by exact Hn8. lia.
Qed.

Lemma kentry_overlay_sound : forall E M0 allkn base rb rk n K,
  know_ok segs E M0 allkn -> kentry_ok segs E base K -> (1 <= n)%nat -> (n <= 8)%nat ->
  kentry_overlay allkn rb rk n K = true ->
  flat E (SA rb rk) (Z.of_nat n)
  /\ forall j, (j < n)%nat -> base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None.
Proof.
  intros E M0 allkn base rb rk n K Hall HK Hn1 Hn8 H.
  assert (GEN : forall kb kk len (P : option byte -> Prop),
    (forall x, P x -> x <> None) ->
    flat E (SA kb kk) (elenZ E len) ->
    (forall i, (0 <= i < elenZ E len)%Z -> P (base (Z_to_bv 64 (estart E (SA kb kk) + i)))) ->
    zf_covers allkn rb rk n kb kk len = true ->
    flat E (SA rb rk) (Z.of_nat n) /\ forall j, (j < n)%nat -> base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None).
  { intros kb kk len P HP Hfl Hz Hc.
    destruct (zf_covers_sound E M0 allkn rb rk n kb kk len Hall Hn8 Hc) as [A B].
    split; [unfold flat, estart in *; cbn [a_base a_off] in *; lia|].
    intros j Hj.
    replace (estart E (SA rb rk) + Z.of_nat j)%Z with (estart E (SA kb kk) + (estart E (SA rb rk) - estart E (SA kb kk) + Z.of_nat j))%Z by lia.
    apply HP. apply Hz. lia. }
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len k|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2|[kb kk] len fc|[kb kk] len];
    cbn [kentry_overlay] in H; try discriminate; cbn [kentry_ok] in HK.
  - destruct HK as [Hfl Hz]. apply (GEN kb kk len (fun x => x = Some (Z_to_bv 8 0))); [intros x ->; discriminate | exact Hfl | exact Hz | exact H].
  - destruct HK as (Hfl & Hlen & Hz). apply (GEN kb kk len (fun x => exists b, x = Some b)); [intros x [b ->]; discriminate | exact Hfl | | exact H].
    intros i Hi. eexists. apply Hz. exact Hi.
  - destruct HK as [Hfl Hz]. apply (GEN kb kk len (fun x => x = Some (Z_to_bv 8 fc))); [intros x ->; discriminate | exact Hfl | exact Hz | exact H].
  - destruct HK as [Hfl Hz]. apply (GEN kb kk len (fun x => x <> None)); [intros x Hx; exact Hx | exact Hfl | exact Hz | exact H].
Qed.

Lemma kentry_readable_sound : forall E M0 allkn base rb rk n K,
  know_ok segs E M0 allkn -> kentry_ok segs E base K -> (1 <= n)%nat -> (n <= 8)%nat ->
  kentry_readable allkn rb rk n K = true ->
  flat E (SA rb rk) (Z.of_nat n)
  /\ forall j, (j < n)%nat -> rd1 base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None.
Proof.
  intros E M0 allkn base rb rk n K Hall HK Hn1 Hn8 H.
  assert (OV : kentry_overlay allkn rb rk n K = true ->
    flat E (SA rb rk) (Z.of_nat n) /\ forall j, (j < n)%nat -> rd1 base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None).
  { intros Hov. destruct (kentry_overlay_sound E M0 allkn base rb rk n K Hall HK Hn1 Hn8 Hov) as [A B].
    split; [exact A|]. intros j Hj. unfold rd1. specialize (B j Hj).
    destruct (base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j))); [discriminate | exfalso; exact (B eq_refl)]. }
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len k|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2|[kb kk] len fc|[kb kk] len];
    try exact (OV H).
  (* [comment removed for export] *)
  cbn [kentry_readable] in H. cbn [kentry_ok] in HK. destruct HK as (Hw8 & Hfk & Hrd).
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)) as [d| | |] eqn:Hrel; try discriminate.
  destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (<- & Hd & Hkk & Hrn & Hst).
  assert (Hfr : flat E (SA rb rk) (Z.of_nat n)) by (unfold flat, estart in *; cbn [a_base a_off] in *; destruct Hfk as (?&?&?&?); lia).
  split; [exact Hfr|]. intros j Hj.
  pose proof (rdn_rd1 base w (adenot E (SA rb kk)) _ (Z.to_nat d + j) Hrd ltac:(lia)) as X.
  rewrite w_add_nat in X. rewrite (flat_u E _ _ Hfk) in X.
  replace (estart E (SA rb kk) + Z.of_nat (Z.to_nat d + j))%Z with (estart E (SA rb rk) + Z.of_nat j)%Z in X by lia.
  exact X.
Qed.

Lemma know_byte_cov_sound : forall img E base kn rb rk,
  know_ok segs E base kn -> know_byte_cov segs img kn rb rk = true ->
  flat E (SA rb rk) 1
  /\ (if img then rd1 base (Z_to_bv 64 (estart E (SA rb rk))) <> None
      else base (Z_to_bv 64 (estart E (SA rb rk))) <> None).
Proof.
  intros img E base kn rb rk Hkn. induction kn as [|K rest IH]; intros H; [discriminate|].
  apply Forall_cons_iff in Hkn as [HK Hrest].
  cbn [know_byte_cov] in H. apply orb_prop in H as [H|H]; [|exact (IH Hrest H)]. clear IH.
  assert (LIT : forall kb kk (l : Z) (P : option byte -> Prop),
    (forall x, P x -> x <> None) ->
    flat E (SA kb kk) l ->
    (forall i, (0 <= i < l)%Z -> P (base (Z_to_bv 64 (estart E (SA kb kk) + i)))) ->
    match rel_lit rb rk 1 kb kk l with RInside _ => true | _ => false end = true ->
    flat E (SA rb rk) 1 /\ (if img then rd1 base (Z_to_bv 64 (estart E (SA rb rk))) <> None
                            else base (Z_to_bv 64 (estart E (SA rb rk))) <> None)).
  { intros kb kk l P HP Hfl Hz Hm.
    destruct (rel_lit rb rk 1 kb kk l) as [d| | |] eqn:Hrel; try discriminate.
    destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (Heqb & Hd & Hkk & Hrn & Hst).
    split; [unfold flat, estart in *; cbn [a_base a_off] in *; subst; lia|].
    assert (B : base (Z_to_bv 64 (estart E (SA rb rk))) <> None).
    { rewrite Hst. apply HP. apply Hz. lia. }
    destruct img; [|exact B]. unfold rd1. destruct (base (Z_to_bv 64 (estart E (SA rb rk)))); [discriminate | exfalso; exact (B eq_refl)]. }
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len k|lo hi|ae am|re rlo rhi|wa0 wn0|da1 dn1 da2 dn2|[kb kk] len fc|[kb kk] len];
    cbn [kentry_ok] in HK; try discriminate.
  - (* [comment removed for export] *)
    destruct img; [|discriminate]. cbn [andb] in H.
    destruct HK as (Hw8 & Hfk & Hrd).
    destruct (rel_lit rb rk 1 kb kk (Z.of_nat w)) as [d| | |] eqn:Hrel; try discriminate.
    destruct (rel_lit_inside E _ _ _ _ _ _ _ Hrel) as (<- & Hd & Hkk & Hrn & Hst).
    split; [unfold flat, estart in *; cbn [a_base a_off] in *; destruct Hfk as (?&?&?&?); lia|].
    pose proof (rdn_rd1 base w (adenot E (SA rb kk)) _ (Z.to_nat d) Hrd ltac:(lia)) as X.
    rewrite w_add_nat, (flat_u E _ _ Hfk) in X.
    replace (estart E (SA rb kk) + Z.of_nat (Z.to_nat d))%Z with (estart E (SA rb rk)) in X by lia. exact X.
  - destruct len as [l0| | | | | | |]; try discriminate. destruct HK as [Hfl Hz]. rewrite elenZ_lit in Hfl, Hz.
    apply (LIT kb kk (l0 mod 2 ^ 64)%Z (fun x => x = Some (Z_to_bv 8 0))); [intros x ->; discriminate | exact Hfl | exact Hz | exact H].
  - destruct len as [l0| | | | | | |]; try discriminate. destruct HK as (Hfl & Hlen & Hz). rewrite elenZ_lit in Hfl, Hz, Hlen.
    apply (LIT kb kk (l0 mod 2 ^ 64)%Z (fun x => exists b, x = Some b)); [intros x [b ->]; discriminate | exact Hfl | | exact H].
    intros i Hi. eexists. apply Hz. exact Hi.
  - (* [comment removed for export] *)
    destruct img; [|discriminate]. cbn [andb] in H.
    destruct rb as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
    destruct HK as (Hlo & Hhi & Hnone).
    apply andb_prop in H as [H Hrom]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    rewrite estart_lit0. split; [unfold flat; rewrite estart_lit0; lia|].
    unfold rd1. rewrite (Hnone rk) by lia. destruct (seg_rom segs (Z_to_bv 64 rk)); [discriminate|discriminate].
  - destruct len as [l0| | | | | | |]; try discriminate. destruct HK as [Hfl Hz]. rewrite elenZ_lit in Hfl, Hz.
    apply (LIT kb kk (l0 mod 2 ^ 64)%Z (fun x => x = Some (Z_to_bv 8 fc))); [intros x ->; discriminate | exact Hfl | exact Hz | exact H].
  - destruct len as [l0| | | | | | |]; try discriminate. destruct HK as [Hfl Hz]. rewrite elenZ_lit in Hfl, Hz.
    apply (LIT kb kk (l0 mod 2 ^ 64)%Z (fun x => x <> None)); [intros x Hx; exact Hx | exact Hfl | exact Hz | exact H].
Qed.

Lemma know_bytes_cov_sound : forall img E base kn rb n rk,
  know_ok segs E base kn -> know_bytes_cov segs img kn rb rk n = true -> (1 <= n)%nat ->
  flat E (SA rb rk) (Z.of_nat n)
  /\ forall j, (j < n)%nat ->
       if img then rd1 base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None
       else base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None.
Proof.
  intros img E base kn rb n. induction n as [|n IH]; intros rk Hkn H Hn1; [lia|].
  cbn [know_bytes_cov] in H. apply andb_prop in H as [H1 H2].
  destruct (know_byte_cov_sound img E base kn rb rk Hkn H1) as [F1 B1].
  destruct n as [|n'].
  - split; [exact F1|]. intros j Hj. replace j with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r. exact B1.
  - destruct (IH (rk + 1)%Z Hkn H2 ltac:(lia)) as [F2 B2].
    split; [unfold flat, estart in *; cbn [a_base a_off] in *; lia|].
    intros j Hj. destruct j as [|j'].
    + cbn [Z.of_nat]. rewrite Z.add_0_r. exact B1.
    + specialize (B2 j' ltac:(lia)). unfold estart in *; cbn [a_base a_off] in *.
      replace (bv_unsigned (edenot E rb) + rk + Z.of_nat (S j'))%Z with (bv_unsigned (edenot E rb) + (rk + 1) + Z.of_nat j')%Z by lia.
      exact B2.
Qed.

Lemma kn_readable_sound : forall E M0 allkn base kn rb rk n,
  know_ok segs E M0 allkn -> know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
  kn_readable segs allkn kn rb rk n = true ->
  flat E (SA rb rk) (Z.of_nat n) /\ exists bs, rdn segs base (adenot E (SA rb rk)) n = Some bs /\ length bs = n.
Proof.
  intros E M0 allkn base kn rb rk n Hall Hkn Hn1 Hn8 H. unfold kn_readable in H.
  assert (PT : flat E (SA rb rk) (Z.of_nat n)
               /\ forall j, (j < n)%nat -> rd1 base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None).
  { apply orb_prop in H as [H|H].
    - apply existsb_exists in H as (K & Hin & HK).
      eapply kentry_readable_sound; [exact Hall | exact (proj1 (Forall_forall _ _) Hkn K Hin) | exact Hn1 | exact Hn8 | exact HK].
    - exact (know_bytes_cov_sound true E base kn rb n rk Hkn H Hn1). }
  destruct PT as [Hfl Hpt]. split; [exact Hfl|].
  apply rdn_defined; rewrite (flat_u E _ _ Hfl); [destruct Hfl as (?&?&?&?); lia | exact Hpt].
Qed.

Lemma kn_overlay_sound : forall E M0 allkn base kn rb rk n,
  know_ok segs E M0 allkn -> know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
  kn_overlay segs allkn kn rb rk n = true ->
  flat E (SA rb rk) (Z.of_nat n) /\ RiscvSemantics.store_ok segs base (adenot E (SA rb rk)) n = true.
Proof.
  intros E M0 allkn base kn rb rk n Hall Hkn Hn1 Hn8 H. unfold kn_overlay in H.
  assert (PT : flat E (SA rb rk) (Z.of_nat n)
               /\ forall j, (j < n)%nat -> base (Z_to_bv 64 (estart E (SA rb rk) + Z.of_nat j)) <> None).
  { apply orb_prop in H as [H|H].
    - apply existsb_exists in H as (K & Hin & HK).
      eapply kentry_overlay_sound; [exact Hall | exact (proj1 (Forall_forall _ _) Hkn K Hin) | exact Hn1 | exact Hn8 | exact HK].
    - exact (know_bytes_cov_sound false E base kn rb n rk Hkn H Hn1). }
  destruct PT as [Hfl Hpt]. split; [exact Hfl|].
  apply store_ok_of_all; rewrite (flat_u E _ _ Hfl); [destruct Hfl as (?&?&?&?); lia|].
  intros x Hx. unfold wview.
  specialize (Hpt (Z.to_nat (bv_unsigned x - estart E (SA rb rk))) ltac:(lia)).
  replace (estart E (SA rb rk) + Z.of_nat (Z.to_nat (bv_unsigned x - estart E (SA rb rk))))%Z with (bv_unsigned x) in Hpt by lia.
  rewrite Z_to_bv_bv_unsigned in Hpt. destruct (base x); [discriminate | exfalso; exact (Hpt eq_refl)].
Qed.


(* [comment removed for export] *)

Lemma find_readbase_In : forall i scs a n sx,
  find_readbase i scs = Some (a, n, sx) -> In (SCReadBase a n sx (EVar i)) scs.
Proof.
  intros i scs a n sx. induction scs as [|sc rest IH]; cbn [find_readbase]; intros H; [discriminate|].
  destruct sc as [| | | | |ra rn rsx rv|]; try (right; exact (IH H)).
  destruct rv as [|j| | | | | |]; try (right; exact (IH H)).
  destruct (Nat.eqb j i) eqn:Hj; [|right; exact (IH H)].
  apply Nat.eqb_eq in Hj. subst j. injection H as <- <- <-. left. reflexivity.
Qed.

Lemma x_filter_nil : forall ss ss' scs sc,
  x_filter segs ss ss' scs = [] -> In sc scs ->
  x_dischargeable segs ss ss' (find_readbase (s_next ss) scs) sc = true.
Proof.
  intros ss ss' scs sc H Hin. unfold x_filter in H.
  destruct scs as [|sc0 rest] eqn:Hscs; [destruct Hin|]. rewrite <- Hscs in H, Hin |- *. clear Hscs.
  assert (Hf : forall l f (x : sidecond), List.filter f l = [] -> In x l -> f x = false).
  { intros l f x. induction l as [|y l IH]; cbn; intros Hn Hx; [destruct Hx|].
    destruct (f y) eqn:Hy; [discriminate|]. destruct Hx as [<-|Hx]; [exact Hy | exact (IH Hn Hx)]. }
  pose proof (Hf _ _ sc H Hin) as X. cbv beta in X. destruct (x_dischargeable segs ss ss' _ sc); [reflexivity | discriminate].
Qed.

Lemma x_discharge_sound : forall E0 E base ss ss' rb sc,
  know_ok segs E base (s_know ss) ->
  eagree (s_next ss) E0 E ->
  x_dischargeable segs ss ss' rb sc = true ->
  (forall a n sx, rb = Some (a, n, sx) ->
      exists bs, rdn segs base (adenot E0 a) n = Some bs
                 /\ ev E (s_next ss) = Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))) ->
  sc_denot segs base E sc.
Proof.
  intros E0 E base ss ss' rb sc Hkn Hag Hd Hrb.
  pose proof (facts_of_ok segs E base _ Hkn) as Hfk.
  unfold x_dischargeable in Hd.
  destruct sc as [| fa fn | | | oa on | ra rn rsx rv |]; try discriminate.
  - (* [comment removed for export] *)
    destruct fa as [fb fk]. destruct fn as [z| | | | | | |]; try discriminate.
    apply andb_prop in Hd as [Hd Hcov]. apply andb_prop in Hd as [Hz1 Hz8]. apply Z.leb_le in Hz1. apply Z.leb_le in Hz8.
    cbn [sc_denot a_base a_off] in Hcov |- *. rewrite elenZ_lit.
    destruct (kn_readable_sound E _ _ base _ fb fk (Z.to_nat z) Hfk Hkn ltac:(lia) ltac:(lia) Hcov) as [Hfl _].
    rewrite Z2Nat.id in Hfl by lia. rewrite Z.mod_small by lia. exact Hfl.
  - (* [comment removed for export] *)
    destruct oa as [ob ok]. apply andb_prop in Hd as [Hd Hcov]. apply andb_prop in Hd as [Hn1 Hn8].
    apply Nat.leb_le in Hn1. apply Nat.leb_le in Hn8.
    cbn [sc_denot a_base a_off] in Hcov |- *.
    destruct (kn_overlay_sound E _ _ base _ ob ok on Hfk Hkn Hn1 Hn8 Hcov) as [_ Hso]. exact Hso.
  - (* [comment removed for export] *)
    destruct rv as [|j| | | | | |]; try discriminate.
    destruct rb as [[[a' n'] sx']|]; [|discriminate].
    apply andb_prop in Hd as [Hd Hcov]. apply andb_prop in Hd as [Hd Hn8]. apply andb_prop in Hd as [Hd Hn1].
    apply andb_prop in Hd as [Hd Hvars]. apply andb_prop in Hd as [Hd Hlt]. apply andb_prop in Hd as [Hd Hj].
    apply andb_prop in Hd as [Hd Hsx]. apply andb_prop in Hd as [Ha Hn].
    apply saddr_eqb_eq in Ha. apply Nat.eqb_eq in Hn. apply Bool.eqb_prop in Hsx. subst a' n' sx'.
    apply Nat.eqb_eq in Hj. subst j. apply Nat.leb_le in Hn1. apply Nat.leb_le in Hn8.
    destruct (Hrb ra rn rsx eq_refl) as (bs & Hbs & Hv).
    cbn [sc_denot edenot]. exists bs. split; [|symmetry; exact Hv].
    replace (adenot E ra) with (adenot E0 ra); [exact Hbs|].
    unfold adenot. rewrite (edenot_evars_lt (s_next ss) E0 E (a_base ra) Hag Hvars). reflexivity.
Qed.

(* [comment removed for export] *)

Lemma cap_rd_sound : forall K i E1 base rom ss' ms',
  (forall E'', eagree (s_next ss') E1 E'' -> st_okR segs E'' base rom ss' ms') ->
  exists E', eagree (s_next ss') E1 E'
    /\ (s_next ss' <= s_next (cap_rd K i ss'))%nat
    /\ st_okX E' base rom (cap_rd K i ss') ms'.
Proof.
  intros K i E1 base rom ss' ms' ALL.
  assert (SAME : exists E', eagree (s_next ss') E1 E' /\ (s_next ss' <= s_next ss')%nat /\ st_okX E' base rom ss' ms').
  { exists E1. split; [apply eagree_refl|]. split; [lia|]. intros E'' Ha. exact (ALL E'' Ha). }
  unfold cap_rd. destruct K as [|K']; [exact SAME|].
  destruct (rd_of i) as [rd|]; [|exact SAME].
  destruct (bv_eqb rd 0) eqn:Hrd0; [exact SAME|].
  destruct (esize_le (sr_get (s_regs ss') rd) (S K')); [exact SAME|].
  set (e := sr_get (s_regs ss') rd).
  exists (eupd E1 (s_next ss') (edenot E1 e)).
  split; [apply eagree_upd|]. split; [cbn [s_next]; lia|].
  intros E'' Ha''. cbn [s_next] in Ha''.
  assert (Ha1 : eagree (s_next ss') E1 E'').
  { eapply eagree_trans; [apply eagree_upd | eapply eagree_le; [exact Ha'' | lia]]. }
  destruct (st_okR_parts E'' base rom ss' ms' (ALL E'' Ha1)) as (Hregs & Hmem & Hlf & Hkn & Heq).
  destruct (st_okR_parts E1 base rom ss' ms' (ALL E1 (eagree_refl _ _))) as (Hregs1 & _).
  exists (ms_regs ms'). cbn [s_pc s_regs s_log s_know s_resv].
  split; [exact Heq|]. split; [|split; [exact Hlf | exact Hkn]].
  apply regs_ok_pin; [exact Hregs|].
  cbn [edenot]. destruct Ha'' as [Hv _]. rewrite <- (Hv (s_next ss')) by lia. rewrite eupd_at.
  exact (Hregs1 rd).
Qed.

(* [comment removed for export] *)

Lemma sym_stepX_sound : forall K E base rom ss ms i ssx scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, 4%Z) ->
  sym_stepX segs K i ss scr_nil = SOk ssx [] scr' ->
  st_okX E base rom ss ms ->
  exists E' ms', eagree (s_next ss) E E'
    /\ (s_next ss <= s_next ssx)%nat
    /\ RiscvSemantics.step segs ms = MachineOk ms'
    /\ st_okX E' base rom ssx ms'.
Proof.
  intros K E base rom ss ms i ssx scr' w Hf He Hd H HX. unfold sym_stepX in H.
  destruct (sym_step segs i ss scr_nil) as [ss' scs scr2|] eqn:Hst; [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss')) eqn:Hle; [|discriminate]. apply Nat.leb_le in Hle.
  injection H as Hss Hfil Hscr. subst ssx scr'.
  set (i0 := s_next ss) in *.
  pose proof (st_okX_R _ _ _ _ _ HX) as HR0.
  destruct (st_okR_parts E base rom ss ms HR0) as (Hregs0 & Hmem0 & Hlf0 & Hkn0 & _).
  (* [comment removed for export] *)
  assert (HV : exists E1, eagree i0 E E1 /\
               (forall E'', eagree (s_next ss') E1 E'' -> scs_denot segs base E'' scs)).
  { destruct (find_readbase i0 scs) as [[[a n] sx]|] eqn:Hrb.
    - pose proof (x_filter_nil ss ss' scs _ Hfil (find_readbase_In _ _ _ _ _ Hrb)) as Hdis.
      fold i0 in Hdis. rewrite Hrb in Hdis. unfold x_dischargeable in Hdis.
      apply andb_prop in Hdis as [Hdis Hcov]. apply andb_prop in Hdis as [Hdis Hn8]. apply andb_prop in Hdis as [Hdis Hn1].
      apply andb_prop in Hdis as [Hdis Hvars]. apply andb_prop in Hdis as [Hdis Hlt]. clear Hdis.
      apply Nat.leb_le in Hn1. apply Nat.leb_le in Hn8. apply Nat.ltb_lt in Hlt.
      destruct a as [ab ak]. cbn [a_base a_off] in Hcov, Hvars.
      destruct (kn_readable_sound E _ _ base _ ab ak n (facts_of_ok segs E base _ Hkn0) Hkn0 Hn1 Hn8 Hcov) as (Hfl & bs & Hbs & Hlen).
      exists (eupd E i0 (Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)))).
      split; [apply eagree_upd|].
      intros E'' Ha''.
      assert (HaE : eagree i0 E E'').
      { eapply eagree_trans; [apply eagree_upd | eapply eagree_le; [exact Ha'' | exact Hle]]. }
      destruct (st_okR_parts E'' base rom ss ms (HX E'' HaE)) as (_ & _ & _ & Hkn'' & _).
      unfold scs_denot. apply Forall_forall. intros sc Hin.
      eapply (x_discharge_sound E E''); [exact Hkn'' | exact HaE | exact (x_filter_nil ss ss' scs sc Hfil Hin) |].
      intros a' n' sx' Hrb'. fold i0 in Hrb'. rewrite Hrb in Hrb'. injection Hrb' as <- <- <-.
      exists bs. split; [exact Hbs|].
      destruct Ha'' as [Hv _]. subst i0. rewrite <- (Hv (s_next ss) Hlt). apply eupd_at.
    - exists E. split; [apply eagree_refl|].
      intros E'' Ha''.
      assert (HaE : eagree i0 E E'') by (eapply eagree_le; [exact Ha'' | exact Hle]).
      destruct (st_okR_parts E'' base rom ss ms (HX E'' HaE)) as (_ & _ & _ & Hkn'' & _).
      unfold scs_denot. apply Forall_forall. intros sc Hin.
      eapply (x_discharge_sound E E''); [exact Hkn'' | exact HaE | exact (x_filter_nil ss ss' scs sc Hfil Hin) |].
      intros a' n' sx' Hrb'. fold i0 in Hrb'. rewrite Hrb in Hrb'. discriminate. }
  destruct HV as (E1 & Ha1 & Hscs).
  (* [comment removed for export] *)
  destruct (sym_step_soundR segs E1 base rom ss ms i ss' scs scr_nil scr2 w Hf He Hd Hst
              (Hscs E1 (eagree_refl _ _)) (HX E1 Ha1)) as (ms' & Hstep & HR1).
  assert (ALL : forall E'', eagree (s_next ss') E1 E'' -> st_okR segs E'' base rom ss' ms').
  { intros E'' Ha''.
    assert (HaE : eagree i0 E E'') by (eapply eagree_trans; [exact Ha1 | eapply eagree_le; [exact Ha'' | exact Hle]]).
    destruct (sym_step_soundR segs E'' base rom ss ms i ss' scs scr_nil scr2 w Hf He Hd Hst (Hscs E'' Ha'') (HX E'' HaE))
      as (ms'' & Hstep'' & HR''). rewrite Hstep in Hstep''. injection Hstep'' as <-. exact HR''. }
  destruct (cap_rd_sound K i E1 base rom ss' ms' ALL) as (E' & Ha' & Hle' & HX').
  exists E', ms'. split; [|split; [lia | split; [exact Hstep | exact HX']]].
  eapply eagree_trans; [exact Ha1 | eapply eagree_le; [exact Ha' | exact Hle]].
Qed.

(* [comment removed for export] *)

Lemma sym_execTX_go_sound : forall t K fuel first stops ss ck base rom,
  itab_sound segs t ->
  sym_execTX_go segs t K fuel first stops ss ck = ck \/
  (let r := sym_execTX_go segs t K fuel first stops ss ck in
   s_resv r = None /\ (s_next ss <= s_next r)%nat /\
   (forall E ms, st_okX E base rom ss ms ->
      exists E' mr, eagree (s_next ss) E E' /\ msteps segs ms mr /\ st_okX E' base rom r mr)).
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck base rom Ht.
  - cbn [sym_execTX_go]. destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
    split; [apply s_clean_None; exact Hc|]. split; [lia|].
    intros E ms Hst. exists E, ms. split; [apply eagree_refl|]. split; [apply mst_refl|exact Hst].
  - assert (Hstop : (if s_clean ss then ss else ck) = ck \/
            (let r := (if s_clean ss then ss else ck) in
             s_resv r = None /\ (s_next ss <= s_next r)%nat /\
             (forall E ms, st_okX E base rom ss ms ->
                exists E' mr, eagree (s_next ss) E E' /\ msteps segs ms mr /\ st_okX E' base rom r mr))).
    { destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
      split; [apply s_clean_None; exact Hc|]. split; [lia|].
      intros E ms Hst. exists E, ms. split; [apply eagree_refl|]. split; [apply mst_refl|exact Hst]. }
    cbn [sym_execTX_go].
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact Hstop|].
    destruct (itab_lookup t (s_pc ss)) as [i|] eqn:Hl; [|exact Hstop].
    pose proof (Ht _ _ Hl) as Hen. unfold itab_entry in Hen.
    destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|discriminate].
    destruct (is_ecall w) eqn:Hec; [discriminate|].
    destruct (decode_any w) as [[i' sz]|] eqn:Hd; [|discriminate].
    destruct (Z.eqb sz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst sz.
    injection Hen as ->.
    destruct (sym_stepX segs K i ss scr_nil) as [ss2 scs2 scr2|] eqn:Hstep; [|exact Hstop].
    destruct scs2 as [|x l]; [|exact Hstop].
    set (ck' := if s_clean ss2 then ss2 else ck).
    specialize (IH false stops ss2 ck' base rom Ht).
    assert (ONE : forall E ms, st_okX E base rom ss ms ->
              exists E' msA, eagree (s_next ss) E E' /\ (s_next ss <= s_next ss2)%nat /\
                             msteps segs ms msA /\ st_okX E' base rom ss2 msA).
    { intros E ms Hst.
      destruct (sym_stepX_sound K E base rom ss ms i ss2 scr2 w Hf Hec Hd Hstep Hst) as (E' & msA & Ha & Hle & HstepA & HstA).
      exists E', msA. split; [exact Ha|]. split; [exact Hle|]. split; [|exact HstA].
      eapply mst_step; [destruct (st_okX_R _ _ _ _ _ Hst) as (rr & -> & _); reflexivity | exact HstepA | apply mst_refl]. }
    destruct IH as [Hck|(Hr & Hle2 & Hrun)].
    + subst ck'. destruct (s_clean ss2) eqn:Hc2.
      * right. rewrite Hck. split; [apply s_clean_None; exact Hc2|].
        split.
        { (* [comment removed for export] *)
          unfold sym_stepX in Hstep. destruct (sym_step segs i ss scr_nil) as [ss3 scs3 scr3|]; [|discriminate].
          destruct (Nat.leb (s_next ss) (s_next ss3)) eqn:Hle3; [|discriminate]. apply Nat.leb_le in Hle3.
          injection Hstep as <- _ _. unfold cap_rd. destruct K; [exact Hle3|].
          destruct (rd_of i); [|exact Hle3]. destruct (bv_eqb _ _); [exact Hle3|]. destruct (esize_le _ _); [exact Hle3|].
          cbn [s_next]. lia. }
        intros E ms Hst. destruct (ONE E ms Hst) as (E' & msA & Ha & _ & Hms & HstA).
        exists E', msA. split; [exact Ha|]. split; [exact Hms | exact HstA].
      * left. exact Hck.
    + right. split; [exact Hr|]. split.
      { unfold sym_stepX in Hstep. destruct (sym_step segs i ss scr_nil) as [ss3 scs3 scr3|]; [|discriminate].
        destruct (Nat.leb (s_next ss) (s_next ss3)) eqn:Hle3; [|discriminate]. apply Nat.leb_le in Hle3.
        assert (s_next ss <= s_next ss2)%nat; [|lia].
        injection Hstep as <- _ _. unfold cap_rd. destruct K; [exact Hle3|].
        destruct (rd_of i); [|exact Hle3]. destruct (bv_eqb _ _); [exact Hle3|]. destruct (esize_le _ _); [exact Hle3|].
        cbn [s_next]. lia. }
      intros E ms Hst.
      destruct (ONE E ms Hst) as (E' & msA & Ha & Hle & HmsA & HstA).
      destruct (Hrun E' msA HstA) as (E2 & mr & Ha2 & Hmr & Hstr).
      exists E2, mr. split; [|split; [eapply msteps_trans; [exact HmsA | exact Hmr] | exact Hstr]].
      eapply eagree_trans; [exact Ha | eapply eagree_le; [exact Ha2 | exact Hle]].
Qed.

(* [comment removed for export] *)
Theorem sym_execTX_sound : forall t K fuel first stops ss E base rom ms,
  itab_sound segs t ->
  (forall E', eagree (s_next ss) E E' -> st_ok segs E' base rom ss ms) ->
  let ss' := sym_execTX segs t K fuel first stops ss in
  exists E' ms', eagree (s_next ss) E E'
    /\ (s_next ss <= s_next ss')%nat
    /\ msteps segs ms ms'
    /\ (forall E'', eagree (s_next ss') E' E'' -> st_ok segs E'' base rom ss' ms').
Proof.
  intros t K fuel first stops ss E base rom ms Ht Hst. unfold sym_execTX.
  assert (HX : st_okX E base rom (clr ss) ms) by (apply st_okX_clr; exact Hst).
  destruct (sym_execTX_go_sound t K fuel first stops (clr ss) (clr ss) base rom Ht) as [Hck|(Hr & Hle & Hrun)].
  - rewrite Hck. exists E, ms. split; [apply eagree_refl|]. split; [cbn [s_next clr]; lia|].
    split; [apply mst_refl|]. intros E'' Ha. apply st_okR_ok; [apply HX; exact Ha | reflexivity].
  - destruct (Hrun E ms HX) as (E' & mr & Ha & Hmr & HX').
    exists E', mr. split; [exact Ha|]. split; [exact Hle|]. split; [exact Hmr|].
    intros E'' Ha''. apply st_okR_ok; [apply HX'; exact Ha'' | exact Hr].
Qed.

(* [comment removed for export] *)
Theorem sym_execTX_ex : forall t K fuel first stops ss E base rom ms,
  itab_sound segs t ->
  (forall E', eagree (s_next ss) E E' -> st_ok segs E' base rom ss ms) ->
  let ss' := sym_execTX segs t K fuel first stops ss in
  exists E' R, eagree (s_next ss) E E'
    /\ (s_next ss <= s_next ss')%nat
    /\ regs_ok E' (s_regs ss') R
    /\ log_flat E' (s_log ss')
    /\ know_ok segs E' base (s_know ss')
    /\ msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)
    /\ (forall E'', eagree (s_next ss') E' E'' -> st_ok segs E'' base rom ss' (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)).
Proof.
  intros t K fuel first stops ss E base rom ms Ht Hst.
  destruct (sym_execTX_sound t K fuel first stops ss E base rom ms Ht Hst) as (E' & ms' & Ha & Hle & Hms & HALL).
  destruct (HALL E' (eagree_refl _ _)) as (R & Heq & Hregs & Hlf & Hkn).
  exists E', R. split; [exact Ha|]. split; [exact Hle|]. split; [exact Hregs|]. split; [exact Hlf|]. split; [exact Hkn|].
  rewrite <- Heq. split; [exact Hms | exact HALL].
Qed.

Theorem sym_execTX_resv : forall t K fuel first stops ss,
  itab_sound segs t -> s_resv (sym_execTX segs t K fuel first stops ss) = None.
Proof.
  intros t K fuel first stops ss Ht. unfold sym_execTX.
  destruct (sym_execTX_go_sound t K fuel first stops (clr ss) (clr ss) (fun _ => None) (fun _ => None) Ht) as [Hck|(Hr & _)].
  - rewrite Hck. reflexivity.
  - exact Hr.
Qed.


Lemma sym_execSX_go_sound : forall K fuel first stops ss ck base rom,
  sym_execSX_go segs K fuel first stops ss ck = ck \/
  (let r := sym_execSX_go segs K fuel first stops ss ck in
   s_resv r = None /\ (s_next ss <= s_next r)%nat /\
   (forall E ms, st_okX E base rom ss ms ->
      exists E' mr, eagree (s_next ss) E E' /\ msteps segs ms mr /\ st_okX E' base rom r mr)).
Proof.
  intros K fuel. induction fuel as [|f IH]; intros first stops ss ck base rom.
  - cbn [sym_execSX_go]. destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
    split; [apply s_clean_None; exact Hc|]. split; [lia|].
    intros E ms Hst. exists E, ms. split; [apply eagree_refl|]. split; [apply mst_refl|exact Hst].
  - assert (Hstop : (if s_clean ss then ss else ck) = ck \/
            (let r := (if s_clean ss then ss else ck) in
             s_resv r = None /\ (s_next ss <= s_next r)%nat /\
             (forall E ms, st_okX E base rom ss ms ->
                exists E' mr, eagree (s_next ss) E E' /\ msteps segs ms mr /\ st_okX E' base rom r mr))).
    { destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
      split; [apply s_clean_None; exact Hc|]. split; [lia|].
      intros E ms Hst. exists E, ms. split; [apply eagree_refl|]. split; [apply mst_refl|exact Hst]. }
    cbn [sym_execSX_go].
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact Hstop|].
    destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|exact Hstop].
    destruct (is_ecall w) eqn:Hec; [exact Hstop|].
    destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact Hstop].
    destruct (negb (Z.eqb sz 4)) eqn:Hsz; [exact Hstop|].
    assert (sz = 4%Z) as -> by (destruct (Z.eqb_spec sz 4); [assumption|discriminate]).
    destruct (sym_stepX segs K i ss scr_nil) as [ss2 scs2 scr2|] eqn:Hstep; [|exact Hstop].
    destruct scs2 as [|x l]; [|exact Hstop].
    set (ck' := if s_clean ss2 then ss2 else ck).
    specialize (IH false stops ss2 ck' base rom).
    assert (LE1 : (s_next ss <= s_next ss2)%nat).
    { unfold sym_stepX in Hstep. destruct (sym_step segs i ss scr_nil) as [ss3 scs3 scr3|]; [|discriminate].
      destruct (Nat.leb (s_next ss) (s_next ss3)) eqn:Hle3; [|discriminate]. apply Nat.leb_le in Hle3.
      injection Hstep as <- _ _. unfold cap_rd. destruct K; [exact Hle3|].
      destruct (rd_of i); [|exact Hle3]. destruct (bv_eqb _ _); [exact Hle3|]. destruct (esize_le _ _); [exact Hle3|].
      cbn [s_next]. lia. }
    assert (ONE : forall E ms, st_okX E base rom ss ms ->
              exists E' msA, eagree (s_next ss) E E' /\ msteps segs ms msA /\ st_okX E' base rom ss2 msA).
    { intros E ms Hst.
      destruct (sym_stepX_sound K E base rom ss ms i ss2 scr2 w Hf Hec Hd Hstep Hst) as (E' & msA & Ha & Hle & HstepA & HstA).
      exists E', msA. split; [exact Ha|]. split; [|exact HstA].
      eapply mst_step; [destruct (st_okX_R _ _ _ _ _ Hst) as (rr & -> & _); reflexivity | exact HstepA | apply mst_refl]. }
    destruct IH as [Hck|(Hr & Hle2 & Hrun)].
    + subst ck'. destruct (s_clean ss2) eqn:Hc2.
      * right. rewrite Hck. split; [apply s_clean_None; exact Hc2|]. split; [exact LE1|].
        intros E ms Hst. destruct (ONE E ms Hst) as (E' & msA & Ha & Hms & HstA).
        exists E', msA. split; [exact Ha|]. split; [exact Hms | exact HstA].
      * left. exact Hck.
    + right. split; [exact Hr|]. split; [lia|].
      intros E ms Hst.
      destruct (ONE E ms Hst) as (E' & msA & Ha & HmsA & HstA).
      destruct (Hrun E' msA HstA) as (E2 & mr & Ha2 & Hmr & Hstr).
      exists E2, mr. split; [|split; [eapply msteps_trans; [exact HmsA | exact Hmr] | exact Hstr]].
      eapply eagree_trans; [exact Ha | eapply eagree_le; [exact Ha2 | exact LE1]].
Qed.

Theorem sym_execSX_sound : forall K fuel first stops ss E base rom ms,
  (forall E', eagree (s_next ss) E E' -> st_ok segs E' base rom ss ms) ->
  let ss' := sym_execSX segs K fuel first stops ss in
  exists E' ms', eagree (s_next ss) E E'
    /\ (s_next ss <= s_next ss')%nat
    /\ msteps segs ms ms'
    /\ (forall E'', eagree (s_next ss') E' E'' -> st_ok segs E'' base rom ss' ms').
Proof.
  intros K fuel first stops ss E base rom ms Hst. unfold sym_execSX.
  assert (HX : st_okX E base rom (clr ss) ms) by (apply st_okX_clr; exact Hst).
  destruct (sym_execSX_go_sound K fuel first stops (clr ss) (clr ss) base rom) as [Hck|(Hr & Hle & Hrun)].
  - rewrite Hck. exists E, ms. split; [apply eagree_refl|]. split; [cbn [s_next clr]; lia|].
    split; [apply mst_refl|]. intros E'' Ha. apply st_okR_ok; [apply HX; exact Ha | reflexivity].
  - destruct (Hrun E ms HX) as (E' & mr & Ha & Hmr & HX').
    exists E', mr. split; [exact Ha|]. split; [exact Hle|]. split; [exact Hmr|].
    intros E'' Ha''. apply st_okR_ok; [apply HX'; exact Ha'' | exact Hr].
Qed.

Theorem sym_execSX_resv : forall K fuel first stops ss,
  s_resv (sym_execSX segs K fuel first stops ss) = None.
Proof.
  intros K fuel first stops ss. unfold sym_execSX.
  destruct (sym_execSX_go_sound K fuel first stops (clr ss) (clr ss) (fun _ => None) (fun _ => None)) as [Hck|(Hr & _)].
  - rewrite Hck. reflexivity.
  - exact Hr.
Qed.

End XSound.

(* [comment removed for export] *)
Section Run.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma st_ok_entry : forall E base rom pc sr kn nx regs,
  regs_ok E sr regs -> know_ok segs E base kn ->
  st_ok segs E base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom).
Proof.
  intros E base rom pc sr kn nx regs HR HK. exists regs. cbn [s_pc s_log s_regs s_know mem_denot].
  split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK].
Qed.

Theorem run_sound : forall fuel stops scr pc sr kn nx ss' scs scr' E base rom regs,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  regs_ok E sr regs -> know_ok segs E base kn ->
  scs_denot segs base E scs ->
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
                        (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' E base rom regs Hex HR HK Hsc.
  eapply sym_exec_ex; [exact Hex | exact Hsc | apply st_ok_entry; assumption].
Qed.

(* [comment removed for export] *)
Lemma eagree_env_agree : forall b E E', eagree b E E' <-> env_agree b E E'.
Proof. intros b E E'. unfold eagree, env_agree. tauto. Qed.

(* [comment removed for export] *)
Lemma st_okX_entry : forall E base rom pc sr kn nx regs,
  regs_ok E sr regs -> know_ok segs E base kn ->
  sr_vars_lt nx sr = true -> kn_vars_lt nx kn = true ->
  forall E', eagree nx E E' -> st_ok segs E' base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom).
Proof.
  intros E base rom pc sr kn nx regs HR HK Hsr Hkn E' Ha. apply eagree_env_agree in Ha.
  apply st_ok_entry.
  - eapply regs_ok_agree; [exact Ha | exact Hsr | exact HR].
  - eapply know_ok_agree; [exact Ha | exact Hkn | exact HK].
Qed.

(* [comment removed for export] *)
Theorem runTX_sound : forall t K fuel stops pc sr kn nx E base rom regs,
  itab_sound segs t ->
  regs_ok E sr regs -> know_ok segs E base kn ->
  sr_vars_lt nx sr = true -> kn_vars_lt nx kn = true ->
  let ss' := sym_execTX segs t K fuel true stops (SS pc sr [] kn nx) in
  exists E' R, env_agree nx E E'
    /\ (nx <= s_next ss')%nat
    /\ regs_ok E' (s_regs ss') R
    /\ log_flat E' (s_log ss')
    /\ know_ok segs E' base (s_know ss')
    /\ msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
                   (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)
    /\ (forall E'', env_agree (s_next ss') E' E'' ->
          st_ok segs E'' base rom ss' (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)).
Proof.
  intros t K fuel stops pc sr kn nx E base rom regs Ht HR HK Hsr Hkn.
  destruct (sym_execTX_ex segs t K fuel true stops (SS pc sr [] kn nx) E base rom _ Ht
              (st_okX_entry E base rom pc sr kn nx regs HR HK Hsr Hkn)) as (E' & R & Ha & Hle & HR' & Hlf & HK' & Hms & HALL).
  exists E', R. split; [apply eagree_env_agree; exact Ha|]. split; [exact Hle|].
  split; [exact HR'|]. split; [exact Hlf|]. split; [exact HK'|]. split; [exact Hms|].
  intros E'' Ha''. apply HALL. apply eagree_env_agree. exact Ha''.
Qed.

(* [comment removed for export] *)
Theorem carry_after : forall E base log kn hints kn' scs hs',
  carry log kn hints = (kn', scs, hs') ->
  log_flat E log -> know_ok segs E base kn -> scs_denot segs base E scs ->
  know_ok segs E (mem_denot E base log) kn'.
Proof. intros. eapply carry_sound; eauto. Qed.

(* [comment removed for export] *)
Lemma reg_val : forall E sr R (r : reg), regs_ok E sr R -> getr R r = edenot E (sr_get sr r).
Proof. intros E sr R r HR. apply HR. Qed.

(* [comment removed for export] *)
Lemma regs_ok_set : forall E sr R (rd : reg) v e,
  regs_ok E sr R -> rd <> 0%bv -> edenot E e = v ->
  regs_ok E (sr_upd sr (ridx rd) e) (regupd R rd v).
Proof.
  intros E sr R rd v e HR Hrd He.
  pose proof (regs_ok_upd E sr R rd v e HR He) as H.
  assert (Hb : bv_eqb rd 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. intros Hc. apply Hrd. apply bv_eq. exact Hc. }
  rewrite Hb in H. exact H.
Qed.

End Run.

End FX.
End AX2F.
