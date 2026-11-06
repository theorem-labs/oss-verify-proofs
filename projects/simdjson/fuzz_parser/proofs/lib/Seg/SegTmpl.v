(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymStepR.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosFxStep PIosFxSound PIosKitA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require PIosRegs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegSR SegLearn SegFPSteps SegFP SegDisch SegExplore SegLin SegSrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import AX2. Import AX2S. Import AX2F.

Module ST.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint esub (sg : list expr) (e : expr) : expr :=
  match e with
  | ELit z => ELit z
  | EVar n => nth n sg (ELit 0)
  | EAlu op a b => EAlu op (esub sg a) (esub sg b)
  | EAluw op a b => EAluw op (esub sg a) (esub sg b)
  | EMd op a b => EMd op (esub sg a) (esub sg b)
  | EMdw op a b => EMdw op (esub sg a) (esub sg b)
  | EExt sx lo n a => EExt sx lo n (esub sg a)
  | EBlob sx k i n => EBlob sx k i n
  end.

Definition asub (sg : list expr) (a : saddr) : saddr := SA (esub sg (a_base a)) (a_off a).

Definition ksub (sg : list expr) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (asub sg a) w (esub sg v)
  | KZero a n => KZero (asub sg a) (esub sg n)
  | KBlob a n k => KBlob (asub sg a) (esub sg n) k
  | KImg lo hi => KImg lo hi
  | KAlign e m => KAlign (esub sg e) m
  | KRange e lo hi => KRange (esub sg e) lo hi
  | KWr a n => KWr (asub sg a) (esub sg n)
  | KDisj a1 n1 a2 n2 => KDisj (asub sg a1) (esub sg n1) (asub sg a2) (esub sg n2)
  | KFill a n c => KFill (asub sg a) (esub sg n) c
  | KUnk a n => KUnk (asub sg a) (esub sg n)
  end.

(* [comment removed for export] *)
Definition senv (E : env) (sg : list expr) : env := Env (vals_ev (map (edenot E) sg)) (eb E).

Lemma esub_den : forall E sg e, edenot (senv E sg) e = edenot E (esub sg e).
Proof.
  intros E sg e. induction e; cbn [esub edenot]; try reflexivity;
    try (rewrite IHe1, IHe2; reflexivity); try (rewrite IHe; reflexivity).
  - (* [comment removed for export] *) cbn [senv ev]. unfold vals_ev.
    change (Z_to_bv 64 0) with (edenot E (ELit 0)). apply map_nth.
Qed.

Lemma asub_estart : forall E sg a, estart (senv E sg) a = estart E (asub sg a).
Proof. intros E sg [b k]. unfold estart, asub. cbn [a_base a_off]. rewrite esub_den. reflexivity. Qed.
Lemma asub_adenot : forall E sg a, adenot (senv E sg) a = adenot E (asub sg a).
Proof. intros E sg [b k]. unfold adenot, asub. cbn [a_base a_off]. rewrite esub_den. reflexivity. Qed.
Lemma asub_elenZ : forall E sg n, elenZ (senv E sg) n = elenZ E (esub sg n).
Proof. intros E sg n. unfold elenZ. rewrite esub_den. reflexivity. Qed.
Lemma asub_flat : forall E sg a n, flat (senv E sg) a n <-> flat E (asub sg a) n.
Proof. intros E sg a n. unfold flat. rewrite asub_estart. tauto. Qed.

Lemma ksub_ok : forall segs E M sg K, kentry_ok segs E M (ksub sg K) -> kentry_ok segs (senv E sg) M K.
Proof.
  intros segs E M sg K H.
  destruct K as [a w v|a n|a n k|lo hi|e m|e lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [ksub kentry_ok] in H |- *;
    rewrite ?asub_estart, ?asub_adenot, ?asub_elenZ, ?esub_den, ?asub_flat; try exact H.
Qed.

Lemma know_ok_ksub : forall segs E M sg kn, know_ok segs E M (map (ksub sg) kn) -> know_ok segs (senv E sg) M kn.
Proof.
  intros segs E M sg kn H. unfold know_ok in *. apply Forall_forall. intros K HK.
  apply ksub_ok. exact (proj1 (Forall_forall _ _) H _ (in_map _ _ _ HK)).
Qed.

(* [comment removed for export] *)
Record gatom : Type := GA { g_id : nat; g_args : list expr }.
Definition gsub (sg : list expr) (g : gatom) : gatom := GA (g_id g) (map (esub sg) (g_args g)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record tmpl : Type := TMG {
  t_pc : Z;
  t_regs : list expr;      (* [comment removed for export] *)
  t_know : list kentry;
  t_ns : nat;              (* [comment removed for export] *)
  t_meas : expr;
  t_rank : nat;
  t_ghost : list gatom     (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition TM (pc : Z) (regs : list expr) (kn : list kentry) (ns : nat) (meas : expr) (rank : nat) : tmpl := TMG pc regs kn ns meas rank [].

Definition tstate (T : tmpl) : sym_state := SS (t_pc T) (t_regs T) [] (t_know T) (t_ns T).

Definition gvars_lt (n : nat) (l : list gatom) : bool :=
  forallb (fun g => forallb (expr_vars_lt n) (g_args g)) l.

Definition tm_closed (T : tmpl) : bool :=
  (sr_vars_lt (t_ns T) (t_regs T) && kn_vars_lt (t_ns T) (t_know T) && expr_vars_lt (t_ns T) (t_meas T)
   && Nat.eqb (length (t_regs T)) 32 && match t_regs T with ELit 0 :: _ => true | _ => false end
   && gvars_lt (t_ns T) (t_ghost T))%bool.

Section Sem.
Context {fx : FPState}.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition tm_ok (T : tmpl) (E : env) (M rom : word -> option byte) (ms : machine_state) : Prop :=
  st_ok segs E M rom (tstate T) ms.

Lemma tm_okX : forall T E M rom ms, tm_closed T = true -> tm_ok T E M rom ms -> st_okX segs E M rom (tstate T) ms.
Proof.
  intros T E M rom ms Hc (regs & Hms & HR & _ & HK). unfold tm_closed in Hc.
  apply andb_prop in Hc as [Hc _].
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _].
  apply andb_prop in Hc as [Hsr Hkn].
  intros E' Ha. exists regs. cbn [tstate s_pc s_log s_regs s_know s_resv] in *. subst ms.
  split; [reflexivity|]. apply eagree_env_agree in Ha.
  split; [eapply regs_ok_agree; [exact Ha | exact Hsr | exact HR]|]. split; [exact I|].
  eapply know_ok_agree; [exact Ha | exact Hkn | exact HK].
Qed.

End Sem.

(* [comment removed for export] *)
Definition tm_okF (segs : list Segment) (T : tmpl) (E : env) (M rom : word -> option byte) (ms : machine_state) : Prop :=
  frm_zero (ms_fcsr ms) /\ PIosRegs.rfull (ms_regs ms) /\ @tm_ok (SFP.fx_of ms) segs T E M rom ms.

Lemma tm_okXF : forall segs T E M rom ms, tm_closed T = true -> tm_okF segs T E M rom ms -> SFP.st_okXF segs E M rom (tstate T) ms.
Proof. intros segs T E M rom ms Hc (Hz & _ & HT). split; [exact Hz | exact (tm_okX segs T E M rom ms Hc HT)]. Qed.

(* [comment removed for export] *)
Lemma tm_ok_F : forall (fx : FPState) segs T E M rom ms, frm_zero (@fp_csr fx) -> PIosRegs.rfull (ms_regs ms) ->
  @tm_ok fx segs T E M rom ms -> tm_okF segs T E M rom ms.
Proof.
  intros fx segs T E M rom ms Hz Hf HT. destruct HT as (regs & Hms & HR & HL & HK).
  assert (Hfx : SFP.fx_of ms = fx) by (rewrite Hms; apply SFP.fx_of_mkst).
  split; [rewrite Hms; destruct fx; exact Hz|]. split; [exact Hf|]. rewrite Hfx. exists regs. split; [exact Hms|]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition log_unk (lg : list sentry) : list kentry := map (fun s => KUnk (e_addr s) (elen (e_width s))) lg.

(* [comment removed for export] *)
Definition is_unkb (K : kentry) : bool := match K with KUnk _ _ => true | _ => false end.

(* [comment removed for export] *)
Definition kreg (K : kentry) : option (saddr * expr) :=
  match K with
  | KZero a n | KFill a n _ | KBlob a n _ => Some (a, n)
  | KWord a w _ => if Nat.leb w 8 then Some (a, elen w) else None
  | _ => None
  end.
Definition st_apart (fk : list kentry) (s : sentry) (a : saddr) (n : expr) : bool :=
  let b1 := a_base (e_addr s) in let k1 := a_off (e_addr s) in let n1 := elen (e_width s) in
  if ranges_apart_x fk b1 k1 n1 (a_base a) (a_off a) n then true
  else if SDI.kdisj_apart fk b1 k1 n1 (a_base a) (a_off a) n then true
  else SLin.apart2 fk b1 k1 n1 (a_base a) (a_off a) n.
Definition recover (fk : list kentry) (lg : list sentry) (kn0 kn1 : list kentry) : list kentry :=
  List.filter (fun K => match kreg K with
                        | Some (a, n) => if SLin.kin K kn1 then false else SLin.lall (fun s => st_apart fk s a n) lg
                        | None => false
                        end) kn0.

Definition exit_kn (ss : sym_state) : option (list kentry) :=
  match carry (s_log ss) (List.filter (fun K => negb (is_unkb K)) (s_know ss)) [] with
  | (kn', [], _) => Some (log_unk (s_log ss) ++ List.filter is_unkb (s_know ss) ++ kn'
                          ++ recover (facts_of (s_know ss)) (s_log ss) (s_know ss) kn')
  | _ => None
  end.

Section ExitSound.
Variable segs : list Segment.

Lemma elenZ_elen' : forall E w, (w <= 8)%nat -> elenZ E (elen w) = Z.of_nat w.
Proof.
  intros E w Hw. unfold elenZ, elen. rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
  unfold bv_modulus. cbn. lia.
Qed.

Lemma log_unk_ok : forall E base lg, log_flat E lg -> know_ok segs E (mem_denot E base lg) (log_unk lg).
Proof.
  intros E base lg. induction lg as [|[a w v] rest IH]; intros Hlf; [constructor|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlf').
  cbn [log_unk map]. constructor.
  - cbn [kentry_ok e_addr e_width]. rewrite elenZ_elen' by exact Hw8. split; [exact Hfa|].
    intros i Hi. cbn [mem_denot]. pose proof (flat_u E _ _ Hfa) as Hu.
    replace (estart E a + i)%Z with (bv_unsigned (adenot E a) + Z.of_nat (Z.to_nat i))%Z by lia.
    rewrite wbytes_nth; [discriminate | | ].
    + rewrite length_N_to_le_bytes, Hu. destruct Hfa as (?&?&?&?). lia.
    + rewrite length_N_to_le_bytes. lia.
  - pose proof (IH Hlf') as H. unfold know_ok in *. apply Forall_forall. intros K HK.
    pose proof (proj1 (Forall_forall _ _) H K HK) as HK'.
    apply in_map_iff in HK as ([a' w' v'] & <- & Hin). cbn [kentry_ok e_addr e_width] in HK' |- *.
    destruct HK' as [Hf Hd]. split; [exact Hf|]. intros i Hi. cbn [mem_denot].
    apply (wbytes_grows _ (mem_denot E base rest) (adenot E a)). exact (Hd i Hi).
Qed.

Lemma st_apart_ok : forall E base fk s a n, know_ok segs E base fk -> st_apart fk s a n = true ->
  (estart E (e_addr s) + elenZ E (elen (e_width s)) <= estart E a \/ estart E a + elenZ E n <= estart E (e_addr s))%Z.
Proof.
  intros E base fk [[b1 k1] w v] [b2 k2] n HK H. unfold st_apart in H. cbn [e_addr e_width a_base a_off] in *.
  destruct (ranges_apart_x fk b1 k1 (elen w) b2 k2 n) eqn:H1; [exact (ranges_apart_x_sound segs E base fk _ _ _ _ _ _ HK H1)|].
  destruct (SDI.kdisj_apart fk b1 k1 (elen w) b2 k2 n) eqn:H2; [exact (SDI.kdisj_apart_sound segs E base fk _ _ _ _ _ _ HK H2)|].
  exact (SLin.apart2_sound segs E base fk _ _ _ _ _ _ HK H).
Qed.

Lemma recover1_ok : forall E base fk lg K a n, know_ok segs E base fk -> log_flat E lg -> kentry_ok segs E base K ->
  kreg K = Some (a, n) -> SLin.lall (fun s => st_apart fk s a n) lg = true -> kentry_ok segs E (mem_denot E base lg) K.
Proof.
  intros E base fk lg K a n HF. induction lg as [|[sa w v] rest IH]; intros Hlf HK Hr Ha; [exact HK|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlf'). cbn [SLin.lall] in Ha.
  destruct (st_apart fk (SE sa w v) a n) eqn:H1; [|discriminate].
  pose proof (IH Hlf' HK Hr Ha) as HK'. cbn [mem_denot].
  pose proof (st_apart_ok E base fk (SE sa w v) a n HF H1) as D. cbn [e_addr e_width] in D.
  rewrite elenZ_elen' in D by exact Hw8.
  apply (kentry_ok_frame_bytes segs E _ sa _ K a n).
  - rewrite length_N_to_le_bytes. exact Hfa.
  - exact HK'.
  - destruct K as [a0 w0 v0|a0 n0|a0 n0 k0| | | | | |a0 n0 c0|]; cbn [kreg] in Hr; try discriminate.
    + destruct (Nat.leb w0 8) eqn:Hw; [|discriminate]. injection Hr as <- <-. apply Nat.leb_le in Hw. auto.
    + injection Hr as <- <-. auto.
    + injection Hr as <- <-. auto.
    + injection Hr as <- <-. auto.
  - rewrite length_N_to_le_bytes. exact D.
Qed.

Lemma recover_ok : forall E base fk lg kn0 kn1, know_ok segs E base fk -> log_flat E lg -> know_ok segs E base kn0 ->
  know_ok segs E (mem_denot E base lg) (recover fk lg kn0 kn1).
Proof.
  intros E base fk lg kn0 kn1 HF Hlf HK. unfold recover. apply Forall_forall. intros K HKin. apply filter_In in HKin as [HKin Hc].
  destruct (kreg K) as [[a n]|] eqn:Hr; [|discriminate]. destruct (SLin.kin K kn1); [discriminate|].
  exact (recover1_ok E base fk lg K a n HF Hlf (proj1 (Forall_forall _ _) HK K HKin) Hr Hc).
Qed.

Lemma exit_kn_ok : forall E base ss kn',
  exit_kn ss = Some kn' -> log_flat E (s_log ss) -> know_ok segs E base (s_know ss) ->
  know_ok segs E (mem_denot E base (s_log ss)) kn'.
Proof.
  intros E base ss kn' H Hlf HK. unfold exit_kn in H.
  destruct (carry (s_log ss) (List.filter (fun K => negb (is_unkb K)) (s_know ss)) []) as [[kn1 scs] hs] eqn:Hc.
  destruct scs; [|discriminate]. injection H as <-.
  apply Forall_app. split; [exact (log_unk_ok E base _ Hlf)|].
  rewrite app_assoc. apply Forall_app. split;
    [|exact (recover_ok E base _ _ _ _ (facts_of_ok segs E base _ HK) Hlf HK)].
  apply Forall_app. split.
  - unfold know_ok in *. apply Forall_forall. intros K HKin. apply filter_In in HKin as [HKin Hu].
    destruct K; try discriminate Hu.
    apply (kentry_ok_unk_grows segs E base _ _ _ (mem_denot_grows E base (s_log ss))).
    exact (proj1 (Forall_forall _ _) HK _ HKin).
  - eapply (carry_sound segs E base base); [exact Hc | exact Hlf | | constructor].
    unfold know_ok in *. apply Forall_forall. intros K HKin. apply filter_In in HKin as [HKin _].
    exact (proj1 (Forall_forall _ _) HK _ HKin).
Qed.

End ExitSound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kin (K : kentry) (kn : list kentry) : bool := SLin.lex (APC.kentry_eqb K) kn.

(* [comment removed for export] *)
Definition addr_key (a : saddr) : expr := mkAlu ALU_ADD (a_base a) (ELit (a_off a)).

Lemma addr_key_den : forall E a, adenot E a = edenot E (addr_key a).
Proof.
  intros E [b k]. unfold addr_key, adenot, v_addi. cbn [a_base a_off]. rewrite mkAlu_denot. cbn [edenot]. rewrite alu_add. unfold v_add.
  apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
Definition unk_cover1 (kn : list kentry) (b : expr) (k : Z) (n : expr) (K : kentry) : bool :=
  match K with
  | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      (SLin.xinside2 kn b k n kb kk len && SLin.xinside2 kn b k (ELit 1) kb kk len)%bool
  | _ => false
  end.

(* [comment removed for export] *)
Definition zero_cover1 (kn : list kentry) (b : expr) (k : Z) (n : expr) (K : kentry) : bool :=
  match K with
  | KZero (SA kb kk) len => (SLin.xinside2 kn b k n kb kk len && SLin.xinside2 kn b k (ELit 1) kb kk len)%bool
  | KFill (SA kb kk) len c => if Z.eqb c 0 then (SLin.xinside2 kn b k n kb kk len && SLin.xinside2 kn b k (ELit 1) kb kk len)%bool else false
  | _ => false
  end.

(* [comment removed for export] *)
Definition fill_cover1 (kn : list kentry) (b : expr) (k : Z) (n : expr) (c : Z) (K : kentry) : bool :=
  match K with
  | KZero (SA kb kk) len => if Z.eqb c 0 then (SLin.xinside2 kn b k n kb kk len && SLin.xinside2 kn b k (ELit 1) kb kk len)%bool else false
  | KFill (SA kb kk) len c' => if Z.eqb c c' then (SLin.xinside2 kn b k n kb kk len && SLin.xinside2 kn b k (ELit 1) kb kk len)%bool else false
  | _ => false
  end.

Definition wr_cover1 (kn : list kentry) (b : expr) (k : Z) (n : expr) (K : kentry) : bool :=
  match K with
  | KWr (SA kb kk) len => (SLin.xinside2 kn b k n kb kk len && SLin.xinside2 kn b k (ELit 1) kb kk len)%bool
  | _ => false
  end.

(* [comment removed for export] *)
Definition unk_cover1q (kn : list kentry) (b : expr) (k : Z) (n : expr) (K : kentry) : bool :=
  match K with
  | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      (xinside kn b k n kb kk len && xinside kn b k (ELit 1) kb kk len)%bool
  | _ => false
  end.

(* [comment removed for export] *)
Definition zero_cover1q (kn : list kentry) (b : expr) (k : Z) (n : expr) (K : kentry) : bool :=
  match K with
  | KZero (SA kb kk) len => (xinside kn b k n kb kk len && xinside kn b k (ELit 1) kb kk len)%bool
  | KFill (SA kb kk) len c => if Z.eqb c 0 then (xinside kn b k n kb kk len && xinside kn b k (ELit 1) kb kk len)%bool else false
  | _ => false
  end.

(* [comment removed for export] *)
Definition fill_cover1q (kn : list kentry) (b : expr) (k : Z) (n : expr) (c : Z) (K : kentry) : bool :=
  match K with
  | KZero (SA kb kk) len => if Z.eqb c 0 then (xinside kn b k n kb kk len && xinside kn b k (ELit 1) kb kk len)%bool else false
  | KFill (SA kb kk) len c' => if Z.eqb c c' then (xinside kn b k n kb kk len && xinside kn b k (ELit 1) kb kk len)%bool else false
  | _ => false
  end.

Definition wr_cover1q (kn : list kentry) (b : expr) (k : Z) (n : expr) (K : kentry) : bool :=
  match K with
  | KWr (SA kb kk) len => (xinside kn b k n kb kk len && xinside kn b k (ELit 1) kb kk len)%bool
  | _ => false
  end.

(* [comment removed for export] *)
Definition zlen (kn : list kentry) (b : expr) (k : Z) (n : expr) : bool :=
  match erange kn n with
  | Some (_, h) => if Z.eqb h 0 then SDI.flat_ok kn b k n else false
  | None => false
  end.

(* [comment removed for export] *)
Fixpoint fillpat (c : Z) (w : nat) : Z := match w with O => 0 | S w' => c + 256 * fillpat c w' end.

Definition kwf1 (kn : list kentry) (b : expr) (k : Z) (w : nat) (v : expr) (K : kentry) : bool :=
  match K with
  | KZero _ _ => if fill_cover1 kn b k (ELit (Z.of_nat w)) 0 K then SL.dtrue (decide_branch kn BC_EQ v (ELit 0)) else false
  | KFill _ _ c =>
      if (Z.leb 0 c && Z.ltb c 256)%bool then
        if fill_cover1 kn b k (ELit (Z.of_nat w)) c K then SL.dtrue (decide_branch kn BC_EQ v (ELit (fillpat c w))) else false
      else false
  | _ => false
  end.
Definition kwf1q (kn : list kentry) (b : expr) (k : Z) (w : nat) (v : expr) (K : kentry) : bool :=
  match K with
  | KZero _ _ => if fill_cover1q kn b k (ELit (Z.of_nat w)) 0 K then SL.dtrue (decide_branch kn BC_EQ v (ELit 0)) else false
  | KFill _ _ c =>
      if (Z.leb 0 c && Z.ltb c 256)%bool then
        if fill_cover1q kn b k (ELit (Z.of_nat w)) c K then SL.dtrue (decide_branch kn BC_EQ v (ELit (fillpat c w))) else false
      else false
  | _ => false
  end.
Definition kword_fill (kn : list kentry) (a : saddr) (w : nat) (v : expr) : bool :=
  match a with
  | SA b k => if (Nat.leb 1 w && Nat.leb w 8)%bool then SLin.ex2 (kwf1q kn b k w v) (kwf1 kn b k w v) kn else false
  end.

(* [comment removed for export] *)
Definition scale_k (l l' : lin) : option Z :=
  match snd l, snd l' with
  | (c, a) :: _, (c', a') :: _ =>
      if expr_eqb a a' then
        if Z.eqb c' 0 then None else
        if Z.eqb (c mod c') 0 then (if Z.leb 2 (c / c') then Some (c / c') else None) else None
      else None
  | _, _ => None
  end.
Definition lin_eqb (x y : lin) : bool := if Z.eqb (fst x) (fst y) then SSR.terms_eqb (snd x) (snd y) else false.
Definition scaled_fact (kn : list kentry) (e' : expr) (lo' hi' : Z) (K : kentry) : bool :=
  match K with
  | KRange e lo hi =>
      if Z.leb 0 lo then if Z.ltb hi (2 ^ 63) then
        match scale_k (lin_of e) (lin_of e') with
        | Some k =>
            if lin_eqb (lin_of e) (lscale k (lin_of e')) then
              match SSR.srange kn e' with
              | Some (a, b) =>
                  if Z.leb (- 2 ^ 63) (k * a) then if Z.ltb (k * b) (2 ^ 63) then
                    let lo2 := (lo + k - 1) / k in
                    if Z.leb 0 lo2 then (if Z.leb lo' lo2 then Z.leb (hi / k) hi' else false) else false
                  else false else false
              | None => false
              end
            else false
        | None => false
        end
      else false else false
  | _ => false
  end.
Definition scaled_imp (kn : list kentry) (e : expr) (lo hi : Z) : bool := SLin.lex (scaled_fact kn e lo hi) kn.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition biased_imp (kn : list kentry) (e : expr) (lo hi : Z) : bool :=
  let l := lin_of e in
  let d := ((fst l) mod 2 ^ 64 - 2 ^ 63)%Z in
  if (if Z.leb (- 2 ^ 32) d then Z.leb d (2 ^ 32) else false) then
    match SSR.srange kn (unlin (d, snd l)) with
    | Some (a, b) => if Z.leb lo (a + 2 ^ 63) then Z.leb (b + 2 ^ 63) hi else false
    | None => false
    end
  else false.
Definition srange_imp (kn : list kentry) (e : expr) (lo hi : Z) : bool :=
  match SSR.srange kn e with
  | Some (l, h) => if Z.leb 0 l then (if Z.leb lo l then Z.leb h hi else false) else false
  | None => false
  end.

(* [comment removed for export] *)
Fixpoint bytes_lit_all (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) (c : Z) : bool :=
  match n with
  | O => true
  | S n' => match know_byte_lit segs kn rb rk with
            | Some v => if Z.eqb v c then bytes_lit_all segs kn rb (rk + 1) n' c else false
            | None => false
            end
  end.
Definition fill_bytes (segs : list Segment) (kn : list kentry) (b : expr) (k : Z) (z : Z) (c : Z) : bool :=
  if (Z.leb 1 z && Z.leb z 512)%bool then
    if SDI.flat_ok kn b k (ELit z) then
      let a := to_saddr b k in
      if know_bytes_cov segs false kn (a_base a) (a_off a) (Z.to_nat z) then bytes_lit_all segs kn (a_base a) (a_off a) (Z.to_nat z) (c mod 256)
      else false
    else false
  else false.

Definition kimplied (segs : list Segment) (kn : list kentry) (K : kentry) : bool :=
  (* [comment removed for export] *)
  if kin K kn then true else
  match K with
  | KRange e lo hi => if (match erange kn e with Some (l, h) => (Z.leb lo l && Z.leb h hi)%bool | None => false end) then true
                      else if (SL.dtrue (decide_branch kn BC_GEU e (ELit lo)) && SL.dtrue (decide_branch kn BC_GEU (ELit hi) e)
                               && Z.leb 0 lo && Z.leb lo hi && Z.ltb hi (2^64))%bool then true
                      else if SLin.krange_auto kn e lo hi then true
                      else (* [comment removed for export] *)
                        if srange_imp kn e lo hi then true
                      else if scaled_imp kn e lo hi then true
                      else biased_imp kn e lo hi
  | KAlign e m => (Z.ltb 0 m && Z.eqb (Z.modulo (2 ^ ealign kn e) m) 0)%bool
  | KDisj (SA b1 k1) n1 (SA b2 k2) n2 =>
      SLin.apart2 kn b1 k1 n1 b2 k2 n2
  | KUnk (SA b k) n =>
      if SLin.ex2 (unk_cover1q kn b k n) (unk_cover1 kn b k n) kn then true else
      if zlen kn b k n then true else
      match n with
      | ELit z => if (Z.leb 1 z && Z.leb z 4096)%bool then know_bytes_cov segs false kn b k (Z.to_nat z) else false
      | _ => false
      end
  | KWr (SA b k) n => if SLin.ex2 (wr_cover1q kn b k n) (wr_cover1 kn b k n) kn then true else zlen kn b k n
  | KZero (SA b k) n => if SLin.ex2 (zero_cover1q kn b k n) (zero_cover1 kn b k n) kn then true else
                        if zlen kn b k n then true else match n with ELit z => fill_bytes segs kn b k z 0 | _ => false end
  | KFill (SA b k) n c => if SLin.ex2 (fill_cover1q kn b k n c) (fill_cover1 kn b k n c) kn then true else
                          if zlen kn b k n then true else match n with ELit z => fill_bytes segs kn b k z c | _ => false end
  | KWord a w v =>       (* [comment removed for export] *)
      if SLin.lex (fun K' => match K' with
                         | KWord a' w' v' => if saddr_eqb a a' then if Nat.eqb w w' then SL.dtrue (decide_branch kn BC_EQ v v') else false
                                             else if expr_eqb (addr_key a) (addr_key a') then
                                               if Nat.eqb w w' then
                                                 if SDI.flat_ok kn (a_base a) (a_off a) (elen w) then SL.dtrue (decide_branch kn BC_EQ v v')
                                                 else false
                                               else false
                                             else false
                         | _ => false end) kn
      then true else kword_fill kn a w v
  | _ => false
  end.

(* [comment removed for export] *)
Definition kimplied_h (segs : list Segment) (kn : list kentry) (h : option (list SLin.fterm * list SLin.fterm)) (K : kentry) : bool :=
  kimplied segs kn K ||
  match K, h with
  | KRange e lo hi, Some (hl, hu) => SLin.krange_farkas kn e lo hi hl hu
  | _, _ => false
  end.

(* [comment removed for export] *)
Ltac q1_tac K := let H := fresh "H" in let H1 := fresh "H" in let H2 := fresh "H" in intros H; destruct K; try discriminate; repeat match goal with s : saddr |- _ => destruct s end;
  cbv beta iota in *;
  repeat match goal with H : context [if Z.eqb ?a ?b then _ else _] |- _ => destruct (Z.eqb a b); [|discriminate] end;
  apply andb_prop in H as [H1 H2]; rewrite (SLin.xinside_2 _ _ _ _ _ _ _ H1), (SLin.xinside_2 _ _ _ _ _ _ _ H2); reflexivity.
Lemma unk_cover1q_1 : forall kn b k n K, unk_cover1q kn b k n K = true -> unk_cover1 kn b k n K = true.
Proof. intros kn b k n K. unfold unk_cover1q, unk_cover1. q1_tac K. Qed.
Lemma zero_cover1q_1 : forall kn b k n K, zero_cover1q kn b k n K = true -> zero_cover1 kn b k n K = true.
Proof. intros kn b k n K. unfold zero_cover1q, zero_cover1. q1_tac K. Qed.
Lemma fill_cover1q_1 : forall kn b k n c K, fill_cover1q kn b k n c K = true -> fill_cover1 kn b k n c K = true.
Proof. intros kn b k n c K. unfold fill_cover1q, fill_cover1. q1_tac K. Qed.
Lemma wr_cover1q_1 : forall kn b k n K, wr_cover1q kn b k n K = true -> wr_cover1 kn b k n K = true.
Proof. intros kn b k n K. unfold wr_cover1q, wr_cover1. q1_tac K. Qed.

Section ImplSound.
Variable segs : list Segment.

Lemma kin_ok : forall E M kn K, know_ok segs E M kn -> kin K kn = true -> kentry_ok segs E M K.
Proof.
  intros E M kn K HK H. apply SLin.lex_exists in H as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'.
  exact (proj1 (Forall_forall _ _) HK K Hin).
Qed.

Lemma flat_inside : forall E a1 n1 a2 n2,
  flat E a2 n2 -> (estart E a2 <= estart E a1)%Z -> (estart E a1 + n1 <= estart E a2 + n2)%Z -> (0 <= n1)%Z ->
  (estart E a1 + 1 <= estart E a2 + n2)%Z -> flat E a1 n1.
Proof. intros E a1 n1 a2 n2 (F1 & F2 & F3 & F4) H1 H2 H3 H4. unfold flat. lia. Qed.

Lemma elenZ_one : forall E, elenZ E (ELit 1) = 1%Z.
Proof. intros E. unfold elenZ. rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small; [reflexivity | unfold bv_modulus; cbn; lia]. Qed.

Lemma elenZ_nonneg : forall E n, (0 <= elenZ E n)%Z.
Proof. intros E n. unfold elenZ. pose proof (bv_unsigned_in_range 64 (edenot E n)). lia. Qed.

Lemma unk_cover1_ok : forall E M kn b k n K,
  know_ok segs E M kn -> kentry_ok segs E M K -> unk_cover1 kn b k n K = true -> kentry_ok segs E M (KUnk (SA b k) n).
Proof.
  intros E M kn b k n K HK HKK H.
  assert (GEN : forall kb kk len, (SLin.xinside2 kn b k n kb kk len && SLin.xinside2 kn b k (ELit 1) kb kk len)%bool = true -> flat E (SA kb kk) (elenZ E len) ->
                  (forall i, (0 <= i < elenZ E len)%Z -> M (Z_to_bv 64 (estart E (SA kb kk) + i)) <> None) ->
                  kentry_ok segs E M (KUnk (SA b k) n)).
  { intros kb kk len Hx2 Hfl Hd. apply andb_prop in Hx2 as [Hx Hx1].
    destruct (SLin.xinside2_sound segs E M kn b k n kb kk len HK Hx) as [A B].
    destruct (SLin.xinside2_sound segs E M kn b k (ELit 1) kb kk len HK Hx1) as [_ B1]. rewrite elenZ_one in B1.
    cbn [kentry_ok]. split; [eapply flat_inside; [exact Hfl | exact A | exact B | apply elenZ_nonneg | exact B1]|].
    intros i Hi. replace (estart E (SA b k) + i)%Z with (estart E (SA kb kk) + (estart E (SA b k) - estart E (SA kb kk) + i))%Z by lia.
    apply Hd. pose proof (elenZ_nonneg E n). lia. }
  destruct K as [|[kb kk] len|[kb kk] len kk'| | | | | |[kb kk] len c|[kb kk] len]; cbn [unk_cover1] in H; try discriminate;
    cbn [kentry_ok] in HKK.
  - destruct HKK as [Hfl Hz]. apply (GEN kb kk len H Hfl). intros i Hi. rewrite (Hz i Hi). discriminate.
  - destruct HKK as (Hfl & _ & Hz). apply (GEN kb kk len H Hfl). intros i Hi. rewrite (Hz i Hi). discriminate.
  - destruct HKK as [Hfl Hz]. apply (GEN kb kk len H Hfl). intros i Hi. rewrite (Hz i Hi). discriminate.
  - destruct HKK as [Hfl Hz]. exact (GEN kb kk len H Hfl Hz).
Qed.

Lemma zero_cover1_ok : forall E M kn b k n K,
  know_ok segs E M kn -> kentry_ok segs E M K -> zero_cover1 kn b k n K = true -> kentry_ok segs E M (KZero (SA b k) n).
Proof.
  intros E M kn b k n K HK HKK H.
  assert (GEN : forall kb kk len, (SLin.xinside2 kn b k n kb kk len && SLin.xinside2 kn b k (ELit 1) kb kk len)%bool = true -> flat E (SA kb kk) (elenZ E len) ->
                  (forall i, (0 <= i < elenZ E len)%Z -> M (Z_to_bv 64 (estart E (SA kb kk) + i)) = Some (Z_to_bv 8 0)) ->
                  kentry_ok segs E M (KZero (SA b k) n)).
  { intros kb kk len Hx2 Hfl Hd. apply andb_prop in Hx2 as [Hx Hx1].
    destruct (SLin.xinside2_sound segs E M kn b k n kb kk len HK Hx) as [A B].
    destruct (SLin.xinside2_sound segs E M kn b k (ELit 1) kb kk len HK Hx1) as [_ B1]. rewrite elenZ_one in B1.
    cbn [kentry_ok]. split; [eapply flat_inside; [exact Hfl | exact A | exact B | apply elenZ_nonneg | exact B1]|].
    intros i Hi. replace (estart E (SA b k) + i)%Z with (estart E (SA kb kk) + (estart E (SA b k) - estart E (SA kb kk) + i))%Z by lia.
    apply Hd. pose proof (elenZ_nonneg E n). lia. }
  destruct K as [|[kb kk] len| | | | | | |[kb kk] len c|]; cbn [zero_cover1] in H; try discriminate; cbn [kentry_ok] in HKK.
  - destruct HKK as [Hfl Hz]. exact (GEN kb kk len H Hfl Hz).
  - destruct (Z.eqb c 0) eqn:Hc; [|discriminate]. apply Z.eqb_eq in Hc. subst c.
    destruct HKK as [Hfl Hz]. exact (GEN kb kk len H Hfl Hz).
Qed.

Lemma fill_cover1_ok : forall E M kn b k n c K,
  know_ok segs E M kn -> kentry_ok segs E M K -> fill_cover1 kn b k n c K = true -> kentry_ok segs E M (KFill (SA b k) n c).
Proof.
  intros E M kn b k n c K HK HKK H.
  assert (GEN : forall kb kk len, (SLin.xinside2 kn b k n kb kk len && SLin.xinside2 kn b k (ELit 1) kb kk len)%bool = true -> flat E (SA kb kk) (elenZ E len) ->
                  (forall i, (0 <= i < elenZ E len)%Z -> M (Z_to_bv 64 (estart E (SA kb kk) + i)) = Some (Z_to_bv 8 c)) ->
                  kentry_ok segs E M (KFill (SA b k) n c)).
  { intros kb kk len Hx2 Hfl Hd. apply andb_prop in Hx2 as [Hx Hx1].
    destruct (SLin.xinside2_sound segs E M kn b k n kb kk len HK Hx) as [A B].
    destruct (SLin.xinside2_sound segs E M kn b k (ELit 1) kb kk len HK Hx1) as [_ B1]. rewrite elenZ_one in B1.
    cbn [kentry_ok]. split; [eapply flat_inside; [exact Hfl | exact A | exact B | apply elenZ_nonneg | exact B1]|].
    intros i Hi. replace (estart E (SA b k) + i)%Z with (estart E (SA kb kk) + (estart E (SA b k) - estart E (SA kb kk) + i))%Z by lia.
    apply Hd. pose proof (elenZ_nonneg E n). lia. }
  destruct K as [|[kb kk] len| | | | | | |[kb kk] len c'|]; cbn [fill_cover1] in H; try discriminate; cbn [kentry_ok] in HKK.
  - destruct (Z.eqb c 0) eqn:Hc; [|discriminate]. apply Z.eqb_eq in Hc. subst c.
    destruct HKK as [Hfl Hz]. exact (GEN kb kk len H Hfl Hz).
  - destruct (Z.eqb c c') eqn:Hc; [|discriminate]. apply Z.eqb_eq in Hc. subst c'.
    destruct HKK as [Hfl Hz]. exact (GEN kb kk len H Hfl Hz).
Qed.

Lemma wr_cover1_ok : forall E M kn b k n K,
  know_ok segs E M kn -> kentry_ok segs E M K -> wr_cover1 kn b k n K = true -> kentry_ok segs E M (KWr (SA b k) n).
Proof.
  intros E M kn b k n K HK HKK H.
  destruct K as [| | | | | |[kb kk] len| | |]; cbn [wr_cover1] in H; try discriminate.
  cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hso]. apply andb_prop in H as [Hx Hx1].
  destruct (SLin.xinside2_sound segs E M kn b k n kb kk len HK Hx) as [A B].
  destruct (SLin.xinside2_sound segs E M kn b k (ELit 1) kb kk len HK Hx1) as [_ B1]. rewrite elenZ_one in B1.
  split; [eapply flat_inside; [exact Hfl | exact A | exact B | apply elenZ_nonneg | exact B1]|].
  intros d m Hd Hdm.
  replace (estart E (SA b k) + d)%Z with (estart E (SA kb kk) + (estart E (SA b k) - estart E (SA kb kk) + d))%Z by lia.
  apply Hso; lia.
Qed.

Lemma zlen_ok : forall E M kn b k n, know_ok segs E M kn -> zlen kn b k n = true -> elenZ E n = 0%Z /\ flat E (SA b k) 0.
Proof.
  intros E M kn b k n HK H. unfold zlen in H. destruct (erange kn n) as [[l h]|] eqn:Er; [|discriminate].
  destruct (Z.eqb h 0) eqn:Hh; [|discriminate]. apply Z.eqb_eq in Hh. subst h.
  pose proof (erange_sound segs E M kn n l 0 HK Er) as R.
  pose proof (SDI.flat_ok_sound segs E M kn b k n HK H) as F.
  assert (Hz : elenZ E n = 0%Z) by (unfold elenZ; pose proof (bv_unsigned_in_range _ (edenot E n)); lia).
  rewrite Hz in F. split; [exact Hz | exact F].
Qed.

Lemma fillpat0 : forall w, fillpat 0 w = 0%Z.
Proof. induction w as [|w IH]; [reflexivity|]. cbn [fillpat]. rewrite IH. reflexivity. Qed.

Lemma fillpat_range : forall c w, 0 <= c < 256 -> 0 <= fillpat c w < 256 ^ Z.of_nat w.
Proof.
  intros c w Hc. induction w as [|w IH]; [cbn; lia|].
  cbn [fillpat]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma fillpat_bytes : forall c w, 0 <= c < 256 -> Z_to_le_bytes w (fillpat c w) = repeat (Z_to_bv 8 c) w.
Proof.
  intros c w Hc. induction w as [|w IH]; [reflexivity|].
  pose proof (fillpat_range c w Hc) as Hr.
  cbn [fillpat Z_to_le_bytes repeat]. f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
    rewrite (Z.mul_comm 256 (fillpat c w)), Z_mod_plus_full. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8)%Z with 256%Z.
    rewrite (Z.mul_comm 256 (fillpat c w)), Z.div_add by lia. rewrite (Z.div_small c 256) by lia. rewrite Z.add_0_l. exact IH.
Qed.

Lemma kwf1_ok : forall E M kn b k w v K, know_ok segs E M kn -> kentry_ok segs E M K -> (1 <= w <= 8)%nat ->
  kwf1 kn b k w v K = true -> kentry_ok segs E M (KWord (SA b k) w v).
Proof.
  intros E M kn b k w v K HK HKK Hw H.
  assert (GEN : forall c, 0 <= c < 256 -> fill_cover1 kn b k (ELit (Z.of_nat w)) c K = true ->
                 SL.dtrue (decide_branch kn BC_EQ v (ELit (fillpat c w))) = true -> kentry_ok segs E M (KWord (SA b k) w v)).
  { intros c Hc Hcov Hv.
    pose proof (fill_cover1_ok E M kn b k (ELit (Z.of_nat w)) c K HK HKK Hcov) as F. cbn [kentry_ok] in F.
    assert (Hel : elenZ E (ELit (Z.of_nat w)) = Z.of_nat w).
    { unfold elenZ. rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. unfold bv_modulus. cbn. lia. }
    rewrite Hel in F. destruct F as [Hfl Hbytes].
    pose proof (SL.dtrue_sound segs E M kn _ _ _ HK Hv) as B. cbn [branch_taken] in B. unfold bv_eqb in B. apply Z.eqb_eq in B.
    pose proof (fillpat_range c w Hc) as Hr.
    assert (H256 : (256 ^ Z.of_nat w <= 2 ^ 64)%Z).
    { replace (256 ^ Z.of_nat w)%Z with (2 ^ (8 * Z.of_nat w))%Z by (rewrite Z.pow_mul_r by lia; reflexivity).
      apply Z.pow_le_mono_r; lia. }
    rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small in B by (unfold bv_modulus; cbn; lia).
    cbn [kentry_ok]. split; [lia|]. split; [exact Hfl|].
    unfold word_to_le_bytes. rewrite B, (fillpat_bytes c w Hc).
    apply rdn_pointwise; [apply repeat_length | rewrite (flat_u E _ _ Hfl); destruct Hfl as (?&?&?&?); lia |].
    intros j Hj. rewrite (flat_u E _ _ Hfl).
    rewrite (nth_indep _ (Z_to_bv 8 0) (Z_to_bv 8 c)) by (rewrite repeat_length; exact Hj).
    rewrite nth_repeat. apply Hbytes. lia. }
  unfold kwf1 in H. destruct K as [| a0 n0 | | | | | | | a0 n0 c |]; try discriminate.
  - destruct (fill_cover1 kn b k (ELit (Z.of_nat w)) 0 (KZero a0 n0)) eqn:Hc; [|discriminate].
    apply (GEN 0%Z ltac:(lia) Hc). rewrite fillpat0. exact H.
  - destruct (Z.leb 0 c && Z.ltb c 256)%bool eqn:Hcr; [|discriminate]. apply andb_prop in Hcr as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    destruct (fill_cover1 kn b k (ELit (Z.of_nat w)) c (KFill a0 n0 c)) eqn:Hc; [|discriminate].
    exact (GEN c ltac:(lia) Hc H).
Qed.

Lemma kwf1q_1 : forall kn b k w v K, kwf1q kn b k w v K = true -> kwf1 kn b k w v K = true.
Proof.
  intros kn b k w v K H. unfold kwf1q, kwf1 in *. destruct K; try discriminate.
  - destruct (fill_cover1q kn b k (ELit (Z.of_nat w)) 0 _) eqn:Hq; [|discriminate]. rewrite (fill_cover1q_1 _ _ _ _ _ _ Hq). exact H.
  - destruct (Z.leb 0 c && Z.ltb c 256)%bool; [|discriminate].
    destruct (fill_cover1q kn b k (ELit (Z.of_nat w)) c _) eqn:Hq; [|discriminate]. rewrite (fill_cover1q_1 _ _ _ _ _ _ Hq). exact H.
Qed.

Lemma kword_fill_ok : forall E M kn a w v, know_ok segs E M kn -> kword_fill kn a w v = true -> kentry_ok segs E M (KWord a w v).
Proof.
  intros E M kn [b k] w v HK H. unfold kword_fill in H.
  destruct (Nat.leb 1 w && Nat.leb w 8)%bool eqn:Hw; [|discriminate]. apply andb_prop in Hw as [H1 H2].
  apply Nat.leb_le in H1, H2.
  rewrite SLin.ex2_eq in H by (intros K0; apply kwf1q_1).
  apply existsb_exists in H as (K & Hin & HK1).
  exact (kwf1_ok E M kn b k w v K HK (proj1 (Forall_forall _ _) HK K Hin) ltac:(lia) HK1).
Qed.

Lemma lin_eqb_eq : forall x y, lin_eqb x y = true -> x = y.
Proof.
  intros [c ts] [c' ts'] H. unfold lin_eqb in H. cbn [fst snd] in H.
  destruct (Z.eqb c c') eqn:Hc; [|discriminate]. apply Z.eqb_eq in Hc. subst c'. apply SSR.terms_eqb_eq in H. subst ts'. reflexivity.
Qed.

Lemma scale_k_ge2 : forall l l' k, scale_k l l' = Some k -> 2 <= k.
Proof.
  intros l l' k H. unfold scale_k in H.
  destruct (snd l) as [|[c a] ?]; [discriminate|]. destruct (snd l') as [|[c' a'] ?]; [discriminate|].
  destruct (expr_eqb a a'); [|discriminate]. destruct (Z.eqb c' 0); [discriminate|].
  destruct (Z.eqb (c mod c') 0); [|discriminate]. destruct (Z.leb 2 (c / c')) eqn:C; [|discriminate].
  injection H as <-. apply Z.leb_le in C. exact C.
Qed.

Lemma scaled_fact_ok : forall E M kn e' lo' hi' K, know_ok segs E M kn -> kentry_ok segs E M K ->
  scaled_fact kn e' lo' hi' K = true -> lo' <= bv_unsigned (edenot E e') <= hi'.
Proof.
  intros E M kn e' lo' hi' K HK HK1 H.
  destruct K as [| | | | |e lo hi| | | | ]; try discriminate. cbn [kentry_ok] in HK1. unfold scaled_fact in H.
  destruct (Z.leb 0 lo) eqn:C1; [|discriminate]. destruct (Z.ltb hi (2 ^ 63)) eqn:C2; [|discriminate].
  destruct (scale_k (lin_of e) (lin_of e')) as [k|] eqn:Hk; [|discriminate].
  pose proof (scale_k_ge2 _ _ _ Hk) as K2.
  destruct (lin_eqb (lin_of e) (lscale k (lin_of e'))) eqn:Hl; [|discriminate].
  destruct (SSR.srange kn e') as [[a b]|] eqn:Hs; [|discriminate].
  destruct (Z.leb (- 2 ^ 63) (k * a)) eqn:C3; [|discriminate]. destruct (Z.ltb (k * b) (2 ^ 63)) eqn:C4; [|discriminate].
  destruct (Z.leb 0 ((lo + k - 1) / k)) eqn:C5; [|discriminate].
  destruct (Z.leb lo' ((lo + k - 1) / k)) eqn:C6; [|discriminate].
  apply Z.leb_le in C1, C3, C5, C6, H. apply Z.ltb_lt in C2, C4.
  pose proof (SSR.srange_sound segs E M kn e' a b HK Hs) as Sr.
  apply lin_eqb_eq in Hl.
  (* [comment removed for export] *)
  assert (EQ : eqm (bv_unsigned (edenot E e)) (k * bv_signed (edenot E e'))).
  { pose proof (lin_of_sound E e) as L1. rewrite Hl in L1. pose proof (lscale_sound E k (lin_of e')) as L2.
    pose proof (lin_of_sound E e') as L3. unfold uE in *.
    apply eqm_sym in L1. eapply eqm_trans; [exact L1|]. eapply eqm_trans; [exact L2|].
    destruct L3 as [q3 H3]. destruct (SSR.s_eqm (edenot E e')) as [qs Hs']. exists (k * q3 - k * qs)%Z. nia. }
  set (s' := bv_signed (edenot E e')) in *. set (u0 := bv_unsigned (edenot E e)) in *.
  assert (Hks : (k * s' = u0)%Z).
  { destruct EQ as [q Hq]. assert (q = 0)%Z by nia. subst q. lia. }
  assert (Hlo : ((lo + k - 1) / k <= s')%Z).
  { assert (((lo + k - 1) / k < s' + 1)%Z) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (Hhi : (s' <= hi / k)%Z) by (apply Z.div_le_lower_bound; lia).
  assert (Hu : (bv_unsigned (edenot E e') = s')%Z) by (apply SSR.s_u_nonneg; lia).
  rewrite Hu. lia.
Qed.

Lemma scaled_imp_ok : forall E M kn e lo hi, know_ok segs E M kn -> scaled_imp kn e lo hi = true -> lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M kn e lo hi HK H. unfold scaled_imp in H. apply SLin.lex_exists in H as (K & Hin & HK1).
  exact (scaled_fact_ok E M kn e lo hi K HK (proj1 (Forall_forall _ _) HK K Hin) HK1).
Qed.

Lemma biased_imp_ok : forall E M kn e lo hi, know_ok segs E M kn -> biased_imp kn e lo hi = true -> lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros E M kn e lo hi HK H. unfold biased_imp in H.
  destruct (lin_of e) as [c ts] eqn:Hl. cbn [fst snd] in H.
  set (d := (c mod 2 ^ 64 - 2 ^ 63)%Z) in H.
  destruct (if Z.leb (- 2 ^ 32) d then Z.leb d (2 ^ 32) else false) eqn:Hc; [|discriminate].
  destruct (SSR.srange kn (unlin (d, ts))) as [[a b]|] eqn:Hs; [|discriminate].
  destruct (Z.leb lo (a + 2 ^ 63)) eqn:C1; [|discriminate]. apply Z.leb_le in C1, H.
  pose proof (SSR.srange_sound segs E M kn _ a b HK Hs) as Sr.
  set (s0 := bv_signed (edenot E (unlin (d, ts)))) in *.
  pose proof (lin_of_sound E e) as L1. rewrite Hl in L1. unfold lden in L1. cbn [fst snd] in L1.
  pose proof (unlin_sound E (d, ts)) as L2. unfold lden in L2. cbn [fst snd] in L2.
  destruct (SSR.s_eqm (edenot E (unlin (d, ts)))) as [q0 H0]. fold s0 in H0.
  destruct L1 as [q1 H1]. destruct L2 as [q2 H2]. unfold uE in H1, H2.
  pose proof (Z.div_mod c (2 ^ 64) ltac:(lia)) as Dc.
  assert (Hd : (c mod 2 ^ 64 = d + 2 ^ 63)%Z) by (unfold d; lia). rewrite Hd in Dc.
  pose proof (bv_unsigned_in_range _ (edenot E e)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  pose proof (SSR.s_range (edenot E (unlin (d, ts)))) as Rs. fold s0 in Rs.
  (* [comment removed for export] *)
  assert (Hk : exists k : Z, (bv_unsigned (edenot E e) = 2 ^ 63 + s0 + k * 2 ^ 64)%Z).
  { exists (c / 2 ^ 64 - q2 - q0 - q1)%Z. lia. }
  destruct Hk as [k Hk]. assert (k = 0)%Z by nia. subst k. lia.
Qed.

Lemma bytes_lit_all_ok : forall E M kn rb n rk c, know_ok segs E M kn -> bytes_lit_all segs kn rb rk n c = true ->
  flat E (SA rb rk) (Z.of_nat n) ->
  forall j, (j < n)%nat -> rdn segs M (adenot E (SA rb (rk + Z.of_nat j))) 1 = Some [Z_to_bv 8 c].
Proof.
  intros E M kn rb n. induction n as [|n IH]; intros rk c HK H Hfl j Hj; [lia|].
  cbn [bytes_lit_all] in H. destruct (know_byte_lit segs kn rb rk) as [v|] eqn:Hb; [|discriminate].
  destruct (Z.eqb v c) eqn:Hvc; [|discriminate]. apply Z.eqb_eq in Hvc. subst v.
  destruct j as [|j].
  - rewrite Z.add_0_r. apply (know_byte_lit_sound segs E M kn rb rk c HK Hb).
    unfold flat, estart in *. cbn [a_base a_off] in *. lia.
  - replace (rk + Z.of_nat (S j))%Z with ((rk + 1) + Z.of_nat j)%Z by lia.
    apply (IH (rk + 1)%Z c HK H); [unfold flat, estart in *; cbn [a_base a_off] in *; lia | lia].
Qed.

Lemma fill_bytes_ok : forall E M kn b k z c, know_ok segs E M kn -> fill_bytes segs kn b k z c = true ->
  flat E (SA b k) z /\ forall i, (0 <= i < z)%Z -> M (Z_to_bv 64 (estart E (SA b k) + i)) = Some (Z_to_bv 8 c).
Proof.
  intros E M kn b k z c HK H. unfold fill_bytes in H.
  destruct (Z.leb 1 z && Z.leb z 512)%bool eqn:Hz; [|discriminate]. apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1, Hz2.
  destruct (SDI.flat_ok kn b k (ELit z)) eqn:Hf; [|discriminate].
  pose proof (SDI.flat_ok_sound segs E M kn b k (ELit z) HK Hf) as Hfl.
  assert (Ez : elenZ E (ELit z) = z) by (unfold elenZ; rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia); reflexivity).
  rewrite Ez in Hfl.
  set (a := to_saddr b k) in *.
  destruct (know_bytes_cov segs false kn (a_base a) (a_off a) (Z.to_nat z)) eqn:Hc; [|discriminate].
  destruct (know_bytes_cov_sound segs false E M kn (a_base a) (Z.to_nat z) (a_off a) HK Hc ltac:(lia)) as [Hfa Hd].
  pose proof (bytes_lit_all_ok E M kn (a_base a) (Z.to_nat z) (a_off a) (c mod 256) HK H Hfa) as Hv.
  assert (Hadr : forall i, (0 <= i < z)%Z -> Z_to_bv 64 (estart E (SA b k) + i) = Z_to_bv 64 (estart E (SA (a_base a) (a_off a)) + i)).
  { intros i Hi. pose proof (to_saddr_denot E b k) as D. fold a in D. destruct a as [ab ak]. cbn [a_base a_off] in *.
    unfold adenot, v_addi in D. cbn [a_base a_off] in D. apply (f_equal bv_unsigned) in D.
    rewrite !Z_to_bv_unsigned in D. unfold bv_wrap, bv_modulus in D. change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in D.
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold estart. cbn [a_base a_off]. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z.
    rewrite <- (Zplus_mod_idemp_l (bv_unsigned (edenot E b) + k) i), <- (Zplus_mod_idemp_l (bv_unsigned (edenot E ab) + ak) i), D.
    reflexivity. }
  split; [exact Hfl|]. intros i Hi.
  specialize (Hd (Z.to_nat i) ltac:(lia)). specialize (Hv (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hd by lia.
  rewrite Hadr by exact Hi.
  assert (HA : adenot E (SA (a_base a) (a_off a + Z.of_nat (Z.to_nat i))) = Z_to_bv 64 (estart E (SA (a_base a) (a_off a)) + i)).
  { unfold adenot, v_addi, estart. cbn [a_base a_off]. rewrite Z2Nat.id by lia. f_equal. lia. }
  rewrite HA in Hv. cbn [rdn] in Hv.
  destruct (M (Z_to_bv 64 (estart E (SA (a_base a) (a_off a)) + i))) as [bt|] eqn:Hm; [|exfalso; exact (Hd eq_refl)].
  cbn in Hv. injection Hv as Hv. rewrite Hv.
  f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z.
  rewrite Zmod_mod. reflexivity.
Qed.

Lemma kimplied_ok : forall E M kn K, know_ok segs E M kn -> kimplied segs kn K = true -> kentry_ok segs E M K.
Proof.
  intros E M kn K HK H. unfold kimplied in H. destruct (kin K kn) eqn:Hkin; [exact (kin_ok E M kn K HK Hkin)|].
  destruct K as [a w v|[zb zk] zn|a n k|lo hi|e m|e lo hi|[b k] n|[b1 k1] n1 [b2 k2] n2|[fb fk] fn fc|[b k] n]; try discriminate.
  - (* [comment removed for export] *)
    match type of H with (if ?X then true else kword_fill kn a w v) = true => destruct X eqn:Hex end.
    2: { exact (kword_fill_ok E M kn a w v HK H). }
    clear H. rename Hex into H.
    apply SLin.lex_exists in H as (K' & Hin & H1). destruct K' as [a' w' v'| | | | | | | | |]; try discriminate.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HK1.
    destruct (saddr_eqb a a') eqn:Ha.
    + destruct (Nat.eqb w w') eqn:Hw; [|discriminate]. rename H1 into Hv.
      apply saddr_eqb_eq in Ha. apply Nat.eqb_eq in Hw. subst a' w'.
      pose proof (SL.dtrue_sound segs E M kn _ _ _ HK Hv) as B. cbn [branch_taken] in B. unfold bv_eqb in B. apply Z.eqb_eq in B.
      assert (Ev : edenot E v = edenot E v') by (apply bv_eq; exact B).
      cbn [kentry_ok] in HK1 |- *. rewrite Ev. exact HK1.
    + destruct (expr_eqb (addr_key a) (addr_key a')) eqn:Hk; [|discriminate].
      destruct (Nat.eqb w w') eqn:Hw; [|discriminate]. apply Nat.eqb_eq in Hw. subst w'.
      destruct (SDI.flat_ok kn (a_base a) (a_off a) (elen w)) eqn:Hfl; [|discriminate]. rename H1 into Hv.
      apply expr_eqb_eq in Hk.
      pose proof (SL.dtrue_sound segs E M kn _ _ _ HK Hv) as B. cbn [branch_taken] in B. unfold bv_eqb in B. apply Z.eqb_eq in B.
      assert (Ev : edenot E v = edenot E v') by (apply bv_eq; exact B).
      cbn [kentry_ok] in HK1 |- *. destruct HK1 as (Hw8 & _ & Hrd).
      split; [exact Hw8|]. split.
      * pose proof (SDI.flat_ok_sound segs E M kn (a_base a) (a_off a) (elen w) HK Hfl) as F.
        rewrite elenZ_elen' in F by exact Hw8. destruct a as [ab ak]. exact F.
      * rewrite (addr_key_den E a), Hk, <- (addr_key_den E a'), Ev. exact Hrd.
  - (* [comment removed for export] *)
    rewrite SLin.ex2_eq in H by (intros K0; apply zero_cover1q_1).
    destruct (existsb (zero_cover1 kn zb zk zn) kn) eqn:Hx.
    2: { destruct (zlen kn zb zk zn) eqn:Hzl.
         { destruct (zlen_ok E M kn zb zk zn HK Hzl) as [Hz Hfl]. cbn [kentry_ok]. rewrite Hz. split; [exact Hfl | intros i Hi; lia]. }
         destruct zn as [z| | | | | | |]; try discriminate.
         destruct (fill_bytes_ok E M kn zb zk z 0 HK H) as [Hfl Hb].
         assert (Ez : elenZ E (ELit z) = z).
         { unfold fill_bytes in H. destruct (Z.leb 1 z && Z.leb z 512)%bool eqn:Hz; [|discriminate].
           apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1, Hz2.
           unfold elenZ; rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia); reflexivity. }
         cbn [kentry_ok]. rewrite Ez. split; [exact Hfl | exact Hb]. }
    clear H. rename Hx into H.
    apply existsb_exists in H as (K & Hin & HK1). exact (zero_cover1_ok E M kn zb zk zn K HK (proj1 (Forall_forall _ _) HK K Hin) HK1).
  - (* [comment removed for export] *)
    apply andb_prop in H as [H0 Hm]. apply Z.ltb_lt in H0. apply Z.eqb_eq in Hm.
    destruct (ealign_sound segs E M kn e HK) as [Hr Hdiv].
    cbn [kentry_ok]. split; [exact H0|]. apply Z.mod_divide; [lia|].
    apply Z.mod_divide in Hm; [|lia]. eapply Z.divide_trans; [exact Hm | exact Hdiv].
  - (* [comment removed for export] *)
    destruct (match erange kn e with Some (l, h) => (Z.leb lo l && Z.leb h hi)%bool | None => false end) eqn:H0.
    { destruct (erange kn e) as [[l h]|] eqn:Er; [|discriminate]. apply andb_prop in H0 as [H1 H2]. apply Z.leb_le in H1, H2.
      pose proof (erange_sound segs E M kn e l h HK Er) as R. cbn [kentry_ok]. lia. }
    destruct (SL.dtrue (decide_branch kn BC_GEU e (ELit lo)) && SL.dtrue (decide_branch kn BC_GEU (ELit hi) e)
              && Z.leb 0 lo && Z.leb lo hi && Z.ltb hi (2^64))%bool eqn:H0'.
    2: { cbn [kentry_ok]. destruct (SLin.krange_auto kn e lo hi) eqn:Ha; [exact (SLin.krange_auto_sound segs E M kn e lo hi HK Ha)|].
         destruct (srange_imp kn e lo hi) eqn:Hsi.
         2: { destruct (scaled_imp kn e lo hi) eqn:Hsc; [exact (scaled_imp_ok E M kn e lo hi HK Hsc)|].
              exact (biased_imp_ok E M kn e lo hi HK H). }
         clear H. rename Hsi into H.
         unfold srange_imp in H.
         destruct (SSR.srange kn e) as [[l h]|] eqn:Es; [|discriminate].
         destruct (Z.leb 0 l) eqn:H0l; [|discriminate]. destruct (Z.leb lo l) eqn:H1l; [|discriminate].
         apply Z.leb_le in H0l, H1l, H. pose proof (SSR.srange_sound_u segs E M kn e l h HK Es H0l). lia. }
    + clear H. rename H0' into H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
      apply Z.leb_le in H3, H5. apply Z.ltb_lt in H4.
      pose proof (SL.geu_true _ _ (SL.dtrue_sound segs E M kn _ _ _ HK H1)) as B1.
      pose proof (SL.geu_true _ _ (SL.dtrue_sound segs E M kn _ _ _ HK H2)) as B2.
      rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small in B1, B2 by (unfold bv_modulus; cbn; lia).
      cbn [kentry_ok]. lia.
  - (* [comment removed for export] *)
    rewrite SLin.ex2_eq in H by (intros K0; apply wr_cover1q_1).
    destruct (existsb (wr_cover1 kn b k n) kn) eqn:Hx.
    2: { destruct (zlen_ok E M kn b k n HK H) as [Hz Hfl]. cbn [kentry_ok]. rewrite Hz. split; [exact Hfl|].
         intros d m Hd Hdm. assert (m = 0%nat) by lia. subst m. reflexivity. }
    clear H. rename Hx into H.
    apply existsb_exists in H as (K & Hin & HK1). exact (wr_cover1_ok E M kn b k n K HK (proj1 (Forall_forall _ _) HK K Hin) HK1).
  - (* [comment removed for export] *)
    pose proof (SLin.apart2_sound segs E M kn b1 k1 n1 b2 k2 n2 HK H) as R. cbn [kentry_ok]. exact R.
  - (* [comment removed for export] *)
    rewrite SLin.ex2_eq in H by (intros K0; apply fill_cover1q_1).
    destruct (existsb (fill_cover1 kn fb fk fn fc) kn) eqn:Hx.
    2: { destruct (zlen kn fb fk fn) eqn:Hzl.
         { destruct (zlen_ok E M kn fb fk fn HK Hzl) as [Hz Hfl]. cbn [kentry_ok]. rewrite Hz. split; [exact Hfl | intros i Hi; lia]. }
         destruct fn as [z| | | | | | |]; try discriminate.
         destruct (fill_bytes_ok E M kn fb fk z fc HK H) as [Hfl Hb].
         assert (Ez : elenZ E (ELit z) = z).
         { unfold fill_bytes in H. destruct (Z.leb 1 z && Z.leb z 512)%bool eqn:Hz; [|discriminate].
           apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1, Hz2.
           unfold elenZ; rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia); reflexivity. }
         cbn [kentry_ok]. rewrite Ez. split; [exact Hfl | exact Hb]. }
    clear H. rename Hx into H.
    apply existsb_exists in H as (K & Hin & HK1). exact (fill_cover1_ok E M kn fb fk fn fc K HK (proj1 (Forall_forall _ _) HK K Hin) HK1).
  - (* [comment removed for export] *)
    rewrite SLin.ex2_eq in H by (intros K0; apply unk_cover1q_1).
    destruct (existsb (unk_cover1 kn b k n) kn) eqn:Hx.
    + apply existsb_exists in Hx as (K & Hin & HK1). exact (unk_cover1_ok E M kn b k n K HK (proj1 (Forall_forall _ _) HK K Hin) HK1).
    + destruct (zlen kn b k n) eqn:Hzl.
      { destruct (zlen_ok E M kn b k n HK Hzl) as [Hz Hfl]. cbn [kentry_ok]. rewrite Hz. split; [exact Hfl | intros i Hi; lia]. }
      destruct n as [z| | | | | | |]; try discriminate. destruct (Z.leb 1 z && Z.leb z 4096)%bool eqn:Hz; [|discriminate].
      rename H into Hc. apply andb_prop in Hz as [H1 H2].
      apply Z.leb_le in H1, H2.
      destruct (know_bytes_cov_sound segs false E M kn b (Z.to_nat z) k HK Hc ltac:(lia)) as [Hfl Hd].
      cbn [kentry_ok]. unfold elenZ. rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia).
      rewrite Z2Nat.id in Hfl by lia. split; [exact Hfl|].
      intros i Hi. specialize (Hd (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hd by lia. exact Hd.
Qed.

Lemma kimplied_h_ok : forall E M kn h K, know_ok segs E M kn -> kimplied_h segs kn h K = true -> kentry_ok segs E M K.
Proof.
  intros E M kn h K HK H. unfold kimplied_h in H. apply orb_prop in H as [H|H]; [exact (kimplied_ok E M kn K HK H)|].
  destruct K as [| | | | |e lo hi| | | |]; try discriminate. destruct h as [[hl hu]|]; [|discriminate].
  cbn [kentry_ok]. exact (SLin.krange_farkas_sound segs E M kn e lo hi hl hu HK H).
Qed.

Lemma kimplied_all_ok : forall E M kn l, know_ok segs E M kn -> forallb (kimplied segs kn) l = true -> know_ok segs E M l.
Proof.
  intros E M kn l HK H. unfold know_ok. apply Forall_forall. intros K HKin.
  exact (kimplied_ok E M kn K HK (proj1 (forallb_forall _ _) H K HKin)).
Qed.

End ImplSound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint set_nth {A} (l : list A) (n : nat) (x : A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: t, O => x :: t
  | y :: t, S n' => y :: set_nth t n' x
  end.

(* [comment removed for export] *)
Definition fin_sg (sg : list (option expr)) : list expr :=
  map (fun p => match fst p with Some e => e | None => EVar (snd p) end) (combine sg (seq 0 (length sg))).

Definition unbound (G j : nat) (sg : list (option expr)) : bool :=
  (Nat.leb G j && match nth j sg None with None => true | Some _ => false end)%bool.

(* [comment removed for export] *)
Fixpoint bind_regs (G : nat) (tregs regs : list expr) (sg : list (option expr)) : list (option expr) :=
  match tregs, regs with
  | EVar j :: tr, e :: r =>
      let sg' := if unbound G j sg then set_nth sg j (Some e) else sg in
      bind_regs G tr r sg'
  | EAlu ALU_ADD (EVar g) (EVar j) :: tr, e :: r =>
      let sg' := if unbound G j sg then
                   match nth g sg None with Some eg => set_nth sg j (Some (mkAlu ALU_SUB e eg)) | None => sg end
                 else sg in
      bind_regs G tr r sg'
  | EAlu ALU_ADD (EAlu ALU_ADD b (EVar j)) (ELit c) :: tr, e :: r =>    (* [comment removed for export] *)
      let sg' := if (unbound G j sg && AxSymRun3.expr_vars_lt G b)%bool then set_nth sg j (Some (mkAlu ALU_SUB (mkAlu ALU_SUB e b) (ELit c)))
                 else sg in
      bind_regs G tr r sg'
  | EAlu ALU_ADD b (EAlu ALU_SUB (EVar j) (ELit c)) :: tr, e :: r =>    (* [comment removed for export] *)
      let sg' := if (unbound G j sg && AxSymRun3.expr_vars_lt G b)%bool then set_nth sg j (Some (mkAlu ALU_ADD (mkAlu ALU_SUB e b) (ELit c)))
                 else sg in
      bind_regs G tr r sg'
  | EAlu ALU_ADD b (EAlu ALU_ADD (EVar j) (ELit c)) :: tr, e :: r =>    (* [comment removed for export] *)
      let sg' := if (unbound G j sg && AxSymRun3.expr_vars_lt G b)%bool then set_nth sg j (Some (mkAlu ALU_SUB (mkAlu ALU_SUB e b) (ELit c)))
                 else sg in
      bind_regs G tr r sg'
  | EAlu ALU_ADD b (EVar j) :: tr, e :: r =>        (* [comment removed for export] *)
      let sg' := if (unbound G j sg && AxSymRun3.expr_vars_lt G b)%bool then set_nth sg j (Some (mkAlu ALU_SUB e b)) else sg in
      bind_regs G tr r sg'
  | _ :: tr, _ :: r => bind_regs G tr r sg
  | _, _ => sg
  end.

Fixpoint find_kword (kn : list kentry) (a : saddr) (w : nat) : option expr :=
  match kn with
  | [] => None
  | KWord a' w' v :: r => if Nat.eqb w w' then (if saddr_eqb a a' then Some v else if expr_eqb (addr_key a) (addr_key a') then Some v
                                                   else find_kword r a w) else find_kword r a w
  | _ :: r => find_kword r a w
  end.

(* [comment removed for export] *)
Fixpoint bind_kw (G : nat) (tkn kn : list kentry) (sg : list (option expr)) : list (option expr) :=
  match tkn with
  | [] => sg
  | KWord a w (EVar j) :: r =>
      let sg' := if unbound G j sg then
                   match find_kword kn (asub (fin_sg sg) a) w with Some v => set_nth sg j (Some v) | None => sg end
                 else sg in
      bind_kw G r kn sg'
  | KWord a w (EAlu ALU_ADD (EVar g) (EVar j)) :: r =>      (* [comment removed for export] *)
      let sg' := if unbound G j sg then
                   match nth g sg None with
                   | Some eg => match find_kword kn (asub (fin_sg sg) a) w with Some v => set_nth sg j (Some (mkAlu ALU_SUB v eg)) | None => sg end
                   | None => sg
                   end
                 else sg in
      bind_kw G r kn sg'
  | KWord a w (EAlu ALU_ADD b (EVar j)) :: r =>             (* [comment removed for export] *)
      let sg' := if (unbound G j sg && AxSymRun3.expr_vars_lt G b)%bool then
                   match find_kword kn (asub (fin_sg sg) a) w with Some v => set_nth sg j (Some (mkAlu ALU_SUB v b)) | None => sg end
                 else sg in
      bind_kw G r kn sg'
  | _ :: r => bind_kw G r kn sg
  end.

Fixpoint bind_hints (hs : list (nat * expr)) (sg : list (option expr)) : list (option expr) :=
  match hs with
  | [] => sg
  | (j, e) :: r => bind_hints r (set_nth sg j (Some e))
  end.

(* [comment removed for export] *)
Fixpoint grp_sum (eq : expr -> expr -> bool) (a : expr) (ts : list (Z * expr)) : Z * list (Z * expr) :=
  match ts with
  | [] => (0%Z, [])
  | (k, b) :: r => let '(s, rest) := grp_sum eq a r in if eq a b then ((k + s)%Z, rest) else (s, (k, b) :: rest)
  end.
Fixpoint grp_ok (eq : expr -> expr -> bool) (fuel : nat) (ts : list (Z * expr)) : bool :=
  match fuel with
  | O => match ts with [] => true | _ => false end
  | S f => match ts with
           | [] => true
           | (k, a) :: r => let '(s, rest) := grp_sum eq a r in
                            if Z.eqb ((k + s) mod 2 ^ 64) 0 then grp_ok eq f rest else false
           end
  end.
Definition lin_eq_mod (eq : expr -> expr -> bool) (x y : lin) : bool :=
  let D := SLin.zsub x y in
  if Z.eqb (fst D mod 2 ^ 64) 0 then grp_ok eq (length (snd D)) (snd D) else false.
Fixpoint eqf (n : nat) (x y : expr) : bool :=
  if expr_eqb x y then true else
  match n with
  | O => false
  | S n' =>
      if lin_eq_mod (eqf n') (lin_of x) (lin_of y) then true else
      match x, y with
      | EAlu o a b, EAlu o' a' b' => if aluop_eqb o o' then (if eqf n' a a' then eqf n' b b' else false) else false
      | EAluw o a b, EAluw o' a' b' => if aluop_eqb o o' then (if eqf n' a a' then eqf n' b b' else false) else false
      | EMd o a b, EMd o' a' b' => if mulop_eqb o o' then (if eqf n' a a' then eqf n' b b' else false) else false
      | EMdw o a b, EMdw o' a' b' => if mulop_eqb o o' then (if eqf n' a a' then eqf n' b b' else false) else false
      | EExt sx lo m a, EExt sx' lo' m' a' =>
          if Bool.eqb sx sx' then if Nat.eqb lo lo' then if Nat.eqb m m' then eqf n' a a' else false else false else false
      | _, _ => false
      end
  end.

(* [comment removed for export] *)
Fixpoint grp_norm (eq : expr -> expr -> bool) (fuel : nat) (ts : list (Z * expr)) : list (Z * expr) :=
  match fuel with
  | O => ts
  | S f => match ts with
           | [] => []
           | (k, a) :: r => let '(s, rest) := grp_sum eq a r in
                            if Z.eqb ((k + s) mod 2 ^ 64) 0 then grp_norm eq f rest else ((k + s)%Z, a) :: grp_norm eq f rest
           end
  end.
Definition ldiff (x y : expr) : expr :=
  let d := mkAlu ALU_SUB x y in
  let L := lin_of d in
  let ts := grp_norm (eqf 3) (length (snd L)) (snd L) in
  if Nat.ltb (length ts) (length (snd L)) then unlin (fst L, ts) else d.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint vars_bound (G : nat) (sg : list (option expr)) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar k => if Nat.ltb k G then true else match nth k sg None with Some _ => true | None => false end
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if vars_bound G sg a then vars_bound G sg b else false
  | EExt _ _ _ a => vars_bound G sg a
  | EBlob _ _ _ _ => false
  end.
Definition lin_sub (G : nat) (sg : list (option expr)) (t : Z * expr) : option (Z * expr) :=
  match snd t with
  | EVar k => if Nat.ltb k G then Some t else match nth k sg None with Some e => Some (fst t, e) | None => None end
  | a => if AxSymRun3.expr_vars_lt G a then Some t
         (* [comment removed for export] *)
         else if vars_bound G sg a then Some (fst t, esub (fin_sg sg) a) else None
  end.
Fixpoint lin_split (G : nat) (sg : list (option expr)) (ts : list (Z * expr)) (acc : list (Z * expr)) (hit : option (Z * nat))
  : option (list (Z * expr) * option (Z * nat)) :=
  match ts with
  | [] => Some (acc, hit)
  | t :: r =>
      match lin_sub G sg t with
      | Some t' => lin_split G sg r (t' :: acc) hit
      | None => match snd t, hit with
                | EVar j, None => if (Z.eqb (fst t) 1 || Z.eqb (fst t) (-1))%bool then lin_split G sg r acc (Some (fst t, j)) else None
                | _, _ => None
                end
      end
  end.
Definition bind_lin1 (G : nat) (t e : expr) (sg : list (option expr)) : list (option expr) :=
  let L := lin_of t in
  match lin_split G sg (snd L) [] None with
  | Some (rest, Some (c, j)) =>
      if unbound G j sg then
        let r := unlin (fst L, rest) in
        set_nth sg j (Some (if Z.eqb c 1 then ldiff e r else ldiff r e))
      else sg
  | _ => sg
  end.
Fixpoint bind_lin (G : nat) (tregs regs : list expr) (sg : list (option expr)) : list (option expr) :=
  match tregs, regs with
  | t :: tr, e :: r => bind_lin G tr r (bind_lin1 G t e sg)
  | _, _ => sg
  end.

Definition mk_sg (G : nat) (T : tmpl) (regs : list expr) (kn : list kentry) (hs : list (nat * expr)) : list expr :=
  let sg0 := map (fun j => if Nat.ltb j G then Some (EVar j) else None) (seq 0 (t_ns T)) in
  let sg1 := bind_hints hs sg0 in
  let sg2 := bind_regs G (t_regs T) regs (bind_regs G (t_regs T) regs sg1) in   (* [comment removed for export] *)
  fin_sg (bind_lin G (t_regs T) regs (bind_kw G (t_know T) kn sg2)).

Fixpoint sr_eqb (a b : list expr) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => expr_eqb x y && sr_eqb a' b'
  | _, _ => false
  end.
Lemma sr_eqb_eq : forall a b, sr_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn in H. apply andb_prop in H as [H1 H2]. rewrite (expr_eqb_eq _ _ H1), (IH _ H2). reflexivity.
Qed.

(* [comment removed for export] *)
Definition lin_eqz (x y : lin) : bool :=
  let D := SLin.zsub x y in if Z.eqb (fst D mod 2 ^ 64) 0 then match snd D with [] => true | _ => false end else false.
Fixpoint eq_lin (x y : expr) : bool :=
  if expr_eqb x y then true else
  if lin_eqz (lin_of x) (lin_of y) then true else
  match x, y with
  | EAlu o a b, EAlu o' a' b' => if aluop_eqb o o' then (if eq_lin a a' then eq_lin b b' else false) else false
  | EAluw o a b, EAluw o' a' b' => if aluop_eqb o o' then (if eq_lin a a' then eq_lin b b' else false) else false
  | EMd o a b, EMd o' a' b' => if mulop_eqb o o' then (if eq_lin a a' then eq_lin b b' else false) else false
  | EMdw o a b, EMdw o' a' b' => if mulop_eqb o o' then (if eq_lin a a' then eq_lin b b' else false) else false
  | EExt sx lo n a, EExt sx' lo' n' a' =>
      if Bool.eqb sx sx' then if Nat.eqb lo lo' then if Nat.eqb n n' then eq_lin a a' else false else false else false
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition reg_eq (kn : list kentry) (x y : expr) : bool :=
  if expr_eqb x y then true else if eq_lin x y then true else if eqf 3 x y then true
  else if SL.dtrue (decide_branch kn BC_EQ x y) then true
  else let x' := SSRL.srl_norm kn x in let y' := SSRL.srl_norm kn y in
       if eq_lin x' y' then true else eqf 3 x' y'.
Fixpoint regs_match (kn : list kentry) (a b : list expr) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => if reg_eq kn x y then regs_match kn a' b' else false
  | _, _ => false
  end.

(* [comment removed for export] *)
Record xhint : Type := XH {
  xh_sg : list (nat * expr);
  xh_fk : list (nat * (list SLin.fterm * list SLin.fterm));
  xh_dec : list (list SLin.fterm)
}.
Definition xh0 : xhint := XH [] [] [].

Fixpoint hfind (i : nat) (l : list (nat * (list SLin.fterm * list SLin.fterm))) : option (list SLin.fterm * list SLin.fterm) :=
  match l with [] => None | (j, h) :: r => if Nat.eqb i j then Some h else hfind i r end.

Fixpoint kchk_all (segs : list Segment) (kn : list kentry) (fh : list (nat * (list SLin.fterm * list SLin.fterm))) (i : nat) (l : list kentry) : bool :=
  match l with
  | [] => true
  | K :: r => (kimplied_h segs kn (hfind i fh) K && kchk_all segs kn fh (S i) r)%bool
  end.

Definition entails (segs : list Segment) (T : tmpl) (pc : Z) (regs : list expr) (kn : list kentry) (sg : list expr)
    (fh : list (nat * (list SLin.fterm * list SLin.fterm))) : bool :=
  (Z.eqb pc (t_pc T) && regs_match kn regs (map (esub sg) (t_regs T))
   && kchk_all segs kn fh 0 (map (ksub sg) (t_know T)))%bool.

Lemma sr_get_map : forall sg tr (r : reg), sr_get (map (esub sg) tr) r = esub sg (sr_get tr r).
Proof.
  intros sg tr r. unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
  change (ELit 0) with (esub sg (ELit 0)) at 1. apply map_nth.
Qed.

Section EntailSound.
Context {fx : FPState}.
Variable segs : list Segment.

Lemma lin_eqz_ok : forall E x y, lin_eqz (lin_of x) (lin_of y) = true -> edenot E x = edenot E y.
Proof.
  intros E x y H. unfold lin_eqz in H.
  destruct (Z.eqb (fst (SLin.zsub (lin_of x) (lin_of y)) mod 2 ^ 64) 0) eqn:H1; [|discriminate].
  destruct (snd (SLin.zsub (lin_of x) (lin_of y))) eqn:H2; [|discriminate]. apply Z.eqb_eq in H1.
  pose proof (SLin.zsub_den E (lin_of x) (lin_of y)) as D. unfold SLin.zden in D. rewrite H2 in D. cbn [tden] in D.
  pose proof (lin_of_sound E x) as [qx Hx]. pose proof (lin_of_sound E y) as [qy Hy]. unfold lden, uE in Hx, Hy.
  unfold SLin.zden in D.
  pose proof (u64_range (edenot E x)) as Rx. pose proof (u64_range (edenot E y)) as Ry.
  apply Z.mod_divide in H1; [|lia]. destruct H1 as [k Hk].
  apply bv_eq. nia.
Qed.

Lemma eq_lin_ok : forall E x y, eq_lin x y = true -> edenot E x = edenot E y.
Proof.
  intros E x. induction x as [z|v|o a IHa b IHb|o a IHa b IHb|o a IHa b IHb|o a IHa b IHb|sx lo n a IHa|sx k i n];
    intros y H; cbn [eq_lin] in H;
    (destruct (expr_eqb _ y) eqn:H0; [rewrite (expr_eqb_eq _ _ H0); reflexivity|]);
    (destruct (lin_eqz _ (lin_of y)) eqn:H1; [exact (lin_eqz_ok E _ y H1)|]);
    destruct y as [z'|v'|o' a' b'|o' a' b'|o' a' b'|o' a' b'|sx' lo' n' a'|sx' k' i' n']; try discriminate.
  - destruct (aluop_eqb o o') eqn:Ho; [|discriminate]. apply aluop_eqb_eq in Ho. subst o'.
    destruct (eq_lin a a') eqn:Ha; [|discriminate]. cbn [edenot]. rewrite (IHa a' Ha), (IHb b' H). reflexivity.
  - destruct (aluop_eqb o o') eqn:Ho; [|discriminate]. apply aluop_eqb_eq in Ho. subst o'.
    destruct (eq_lin a a') eqn:Ha; [|discriminate]. cbn [edenot]. rewrite (IHa a' Ha), (IHb b' H). reflexivity.
  - destruct (mulop_eqb o o') eqn:Ho; [|discriminate]. apply mulop_eqb_eq in Ho. subst o'.
    destruct (eq_lin a a') eqn:Ha; [|discriminate]. cbn [edenot]. rewrite (IHa a' Ha), (IHb b' H). reflexivity.
  - destruct (mulop_eqb o o') eqn:Ho; [|discriminate]. apply mulop_eqb_eq in Ho. subst o'.
    destruct (eq_lin a a') eqn:Ha; [|discriminate]. cbn [edenot]. rewrite (IHa a' Ha), (IHb b' H). reflexivity.
  - destruct (Bool.eqb sx sx') eqn:Hs; [|discriminate]. apply Bool.eqb_prop in Hs. subst sx'.
    destruct (Nat.eqb lo lo') eqn:Hl; [|discriminate]. apply Nat.eqb_eq in Hl. subst lo'.
    destruct (Nat.eqb n n') eqn:Hn; [|discriminate]. apply Nat.eqb_eq in Hn. subst n'.
    cbn [edenot]. rewrite (IHa a' H). reflexivity.
Qed.

Lemma grp_sum_ok : forall E (eq : expr -> expr -> bool) a ts s rest,
  (forall b, eq a b = true -> bv_unsigned (edenot E a) = bv_unsigned (edenot E b)) ->
  grp_sum eq a ts = (s, rest) -> tden E ts = (s * bv_unsigned (edenot E a) + tden E rest)%Z.
Proof.
  intros E eq a ts. induction ts as [|[k b] r IH]; intros s rest Heq H; cbn [grp_sum] in H.
  - injection H as <- <-. cbn [tden]. lia.
  - destruct (grp_sum eq a r) as [s0 rest0] eqn:Hr. pose proof (IH s0 rest0 Heq eq_refl) as HI.
    destruct (eq a b) eqn:Hab.
    + injection H as <- <-. cbn [tden]. unfold uE. rewrite <- (Heq b Hab). rewrite HI. lia.
    + injection H as <- <-. cbn [tden]. rewrite HI. lia.
Qed.

Lemma grp_ok_ok : forall E (eq : expr -> expr -> bool), (forall a b, eq a b = true -> edenot E a = edenot E b) ->
  forall fuel ts, grp_ok eq fuel ts = true -> (tden E ts mod 2 ^ 64 = 0)%Z.
Proof.
  intros E eq Heq fuel. induction fuel as [|f IH]; intros ts H.
  - destruct ts; [reflexivity | discriminate].
  - destruct ts as [|[k a] r]; [reflexivity|]. cbn [grp_ok] in H.
    destruct (grp_sum eq a r) as [s rest] eqn:Hg.
    destruct (Z.eqb ((k + s) mod 2 ^ 64) 0) eqn:Hz; [|discriminate]. apply Z.eqb_eq in Hz.
    pose proof (IH rest H) as HR.
    assert (He : forall b, eq a b = true -> bv_unsigned (edenot E a) = bv_unsigned (edenot E b)) by (intros b Hb; rewrite (Heq a b Hb); reflexivity).
    pose proof (grp_sum_ok E eq a r s rest He Hg) as HS.
    cbn [tden]. unfold uE. rewrite HS.
    replace (k * bv_unsigned (edenot E a) + (s * bv_unsigned (edenot E a) + tden E rest))%Z
      with ((k + s) * bv_unsigned (edenot E a) + tden E rest)%Z by lia.
    rewrite Z.add_mod, Z.mul_mod, Hz, HR by lia. reflexivity.
Qed.

Lemma lin_eq_mod_ok : forall E eq x y, (forall a b, eq a b = true -> edenot E a = edenot E b) ->
  lin_eq_mod eq (lin_of x) (lin_of y) = true -> edenot E x = edenot E y.
Proof.
  intros E eq x y Heq H. unfold lin_eq_mod in H.
  destruct (Z.eqb (fst (SLin.zsub (lin_of x) (lin_of y)) mod 2 ^ 64) 0) eqn:H1; [|discriminate]. apply Z.eqb_eq in H1.
  pose proof (grp_ok_ok E eq Heq _ _ H) as H2.
  pose proof (SLin.zsub_den E (lin_of x) (lin_of y)) as D. unfold SLin.zden in D.
  pose proof (lin_of_sound E x) as [qx Hx]. pose proof (lin_of_sound E y) as [qy Hy]. unfold lden, uE in Hx, Hy.
  pose proof (u64_range (edenot E x)) as Rx. pose proof (u64_range (edenot E y)) as Ry.
  apply bv_eq.
  assert (Hm : ((fst (SLin.zsub (lin_of x) (lin_of y)) + tden E (snd (SLin.zsub (lin_of x) (lin_of y)))) mod 2 ^ 64 = 0)%Z).
  { rewrite Z.add_mod, H1, H2 by lia. reflexivity. }
  rewrite D in Hm. apply Z.mod_divide in Hm; [|lia]. destruct Hm as [m Hm]. nia.
Qed.

Lemma eqf_ok : forall E n x y, eqf n x y = true -> edenot E x = edenot E y.
Proof.
  intros E n. induction n as [|n IH]; intros x y H; cbn [eqf] in H;
    (destruct (expr_eqb x y) eqn:H0; [rewrite (expr_eqb_eq _ _ H0); reflexivity|]); [discriminate|].
  destruct (lin_eq_mod (eqf n) (lin_of x) (lin_of y)) eqn:H1; [exact (lin_eq_mod_ok E (eqf n) x y (fun a b Hab => IH a b Hab) H1)|].
  destruct x as [z|v|o a b|o a b|o a b|o a b|sx lo m a|sx k i m];
    destruct y as [z'|v'|o' a' b'|o' a' b'|o' a' b'|o' a' b'|sx' lo' m' a'|sx' k' i' m']; try discriminate.
  - destruct (aluop_eqb o o') eqn:Ho; [|discriminate]. apply aluop_eqb_eq in Ho. subst o'.
    destruct (eqf n a a') eqn:Ha; [|discriminate]. cbn [edenot]. rewrite (IH a a' Ha), (IH b b' H). reflexivity.
  - destruct (aluop_eqb o o') eqn:Ho; [|discriminate]. apply aluop_eqb_eq in Ho. subst o'.
    destruct (eqf n a a') eqn:Ha; [|discriminate]. cbn [edenot]. rewrite (IH a a' Ha), (IH b b' H). reflexivity.
  - destruct (mulop_eqb o o') eqn:Ho; [|discriminate]. apply mulop_eqb_eq in Ho. subst o'.
    destruct (eqf n a a') eqn:Ha; [|discriminate]. cbn [edenot]. rewrite (IH a a' Ha), (IH b b' H). reflexivity.
  - destruct (mulop_eqb o o') eqn:Ho; [|discriminate]. apply mulop_eqb_eq in Ho. subst o'.
    destruct (eqf n a a') eqn:Ha; [|discriminate]. cbn [edenot]. rewrite (IH a a' Ha), (IH b b' H). reflexivity.
  - destruct (Bool.eqb sx sx') eqn:Hs; [|discriminate]. apply Bool.eqb_prop in Hs. subst sx'.
    destruct (Nat.eqb lo lo') eqn:Hl; [|discriminate]. apply Nat.eqb_eq in Hl. subst lo'.
    destruct (Nat.eqb m m') eqn:Hn; [|discriminate]. apply Nat.eqb_eq in Hn. subst m'.
    cbn [edenot]. rewrite (IH a a' H). reflexivity.
Qed.

Lemma regs_match_ok : forall E M kn a b, know_ok segs E M kn -> regs_match kn a b = true ->
  forall r : reg, edenot E (sr_get a r) = edenot E (sr_get b r).
Proof.
  intros E M kn a b HK H r. unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
  revert b H. generalize (ridx r). induction a as [|x a IH]; intros n [|y b] H; try discriminate.
  - destruct n; reflexivity.
  - cbn [regs_match] in H.
    destruct (reg_eq kn x y) eqn:H1; [|discriminate]. rename H into H2.
    destruct n as [|n]; cbn [nth]; [|exact (IH n b H2)].
    unfold reg_eq in H1.
    destruct (expr_eqb x y) eqn:H0; [rewrite (expr_eqb_eq _ _ H0); reflexivity|].
    destruct (eq_lin x y) eqn:H3; [exact (eq_lin_ok E x y H3)|].
    destruct (eqf 3 x y) eqn:H4; [exact (eqf_ok E 3 x y H4)|].
    destruct (SL.dtrue (decide_branch kn BC_EQ x y)) eqn:H5.
    + pose proof (SL.dtrue_sound segs E M kn _ _ _ HK H5) as B. cbn [branch_taken] in B. unfold bv_eqb in B.
      apply Z.eqb_eq in B. apply bv_eq. exact B.
    + rewrite <- (SSRL.srl_norm_ok segs E M kn x HK), <- (SSRL.srl_norm_ok segs E M kn y HK).
      destruct (eq_lin (SSRL.srl_norm kn x) (SSRL.srl_norm kn y)) eqn:H6; [exact (eq_lin_ok E _ _ H6)|].
      exact (eqf_ok E 3 _ _ H1).
Qed.

Lemma kchk_all_ok : forall E M kn fh l i, know_ok segs E M kn -> kchk_all segs kn fh i l = true -> know_ok segs E M l.
Proof.
  intros E M kn fh l. induction l as [|K r IH]; intros i HK H; [constructor|].
  cbn [kchk_all] in H. apply andb_prop in H as [H1 H2]. constructor; [exact (kimplied_h_ok segs E M kn _ K HK H1) | exact (IH (S i) HK H2)].
Qed.

Theorem entails_sound : forall T pc regs kn sg fh E M rom R,
  entails segs T pc regs kn sg fh = true -> know_ok segs E M kn -> regs_ok E regs R ->
  tm_ok segs T (senv E sg) M rom (mkst R (Z_to_bv 64 pc) M rom).
Proof.
  intros T pc regs kn sg fh E M rom R H HK HR. unfold entails in H.
  apply andb_prop in H as [H Hk]. apply andb_prop in H as [Hpc Hsr]. apply Z.eqb_eq in Hpc.
  pose proof (regs_match_ok E M kn _ _ HK Hsr) as RM.
  exists R. cbn [tstate s_pc s_regs s_log s_know mem_denot]. rewrite Hpc.
  split; [reflexivity|]. split.
  { intros r. rewrite (HR r), (RM r), sr_get_map. symmetry. apply esub_den. }
  split; [exact I|].
  apply know_ok_ksub. exact (kchk_all_ok E M kn fh _ 0 HK Hk).
Qed.

End EntailSound.
End ST.
