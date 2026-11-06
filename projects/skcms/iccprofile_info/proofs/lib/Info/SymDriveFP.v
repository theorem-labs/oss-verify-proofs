(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame RefMemcpyLib PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

(* [comment removed for export] *)
Definition blobs_ev (bl : list (list byte)) : nat -> list byte := fun n => nth n bl [].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Drive.
Variable segs : list Segment.

Definition runs_to (st : machine_state) (Q : machine_state -> Prop) : Prop :=
  exists st', msteps segs st st' /\ Q st'.

Lemma runs_to_here : forall st (Q : machine_state -> Prop), Q st -> runs_to st Q.
Proof. intros st Q H. exists st. split; [apply mst_refl | exact H]. Qed.

Lemma runs_to_fwd : forall st st1 Q, msteps segs st st1 -> runs_to st1 Q -> runs_to st Q.
Proof.
  intros st st1 Q Hms (st' & Hms' & HQ). exists st'. split; [| exact HQ].
  eapply msteps_trans; eassumption.
Qed.

Lemma runs_to_mono : forall st (Q Q' : machine_state -> Prop),
  (forall s, Q s -> Q' s) -> runs_to st Q -> runs_to st Q'.
Proof. intros st Q Q' H (st' & A & B). exists st'. split; [exact A | apply H; exact B]. Qed.

(* [comment removed for export] *)
Lemma rt_step : forall st st1 Q,
  ms_svc_pending st = None ->
  RiscvSemantics.step segs st = MachineOk st1 ->
  runs_to st1 Q -> runs_to st Q.
Proof.
  intros st st1 Q Hp Hs HQ. eapply runs_to_fwd; [| exact HQ].
  eapply mst_step; [exact Hp | exact Hs | apply mst_refl].
Qed.

(* [comment removed for export] *)
Lemma rt_ret : forall (FPI : FPState) R (pc : word) M rom w Q,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr 0 1 (Z_to_bv 12 0), 4%Z) ->
  ret_ok (getr R 1) ->
  Q (mkst (FP:=FPI) R (getr R 1) M rom) ->
  runs_to (mkst (FP:=FPI) R pc M rom) Q.
Proof.
  intros FPI R pc M rom w Q Hf He Hd Hret HQ.
  eapply rt_step; [reflexivity | |].
  - exact (step_jalr_gen segs R pc M rom w 0 1 (Z_to_bv 12 0) Hf He Hd).
  - rewrite bv_eqb_refl.
    unfold ret_ok, v_jalr in Hret. change (bv_signed (Z_to_bv 12 0)) with 0%Z.
    unfold jalr_tgt. rewrite Hret.
    apply runs_to_here. exact HQ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rt_run : forall fuel stops scr (chints : list bool) pc sr sfr kn nx ss' scs scr' kn' scs2 hs2
                        E M rom R (FPI : FPState) Q,
  sym_exec segs fuel true stops scr (SS pc sr sfr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn chints = (kn', scs2, hs2) ->
  regs_ok E sr R -> fregs_ok E sfr fp_regs -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  (forall R' (FPI' : FPState) M',
     regs_ok E (s_regs ss') R' -> fregs_ok E (s_fregs ss') (fp_regs (FPState:=FPI')) ->
     know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     log_flat E (s_log ss') ->
     runs_to (mkst (FP:=FPI') R' (Z_to_bv 64 (s_pc ss')) M' rom) Q) ->
  runs_to (mkst (FP:=FPI) R (Z_to_bv 64 pc) M rom) Q.
Proof.
  intros fuel stops scr chints pc sr sfr kn nx ss' scs scr' kn' scs2 hs2 E M rom R FPI Q
         Hex Hc HR HF HK Hsc Hsc2 Hcont.
  destruct (run_sound segs fuel stops scr pc sr sfr kn nx ss' scs scr' E M rom R FPI Hex HR HF HK Hsc)
    as (R' & FPI' & HR' & HF' & Hlf & Hms).
  eapply runs_to_fwd; [exact Hms|].
  apply (Hcont R' FPI' _ HR' HF'); [|reflexivity|exact Hlf].
  eapply carry_after; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition junk_vals (R : bvmap 5 word) : list word :=
  [getr R 0; getr R 1; getr R 2; getr R 3; getr R 4; getr R 5; getr R 6; getr R 7;
   getr R 8; getr R 9; getr R 10; getr R 11; getr R 12; getr R 13; getr R 14; getr R 15;
   getr R 16; getr R 17; getr R 18; getr R 19; getr R 20; getr R 21; getr R 22; getr R 23;
   getr R 24; getr R 25; getr R 26; getr R 27; getr R 28; getr R 29; getr R 30; getr R 31]%bv.
Definition fjunk_vals (FR : bvmap 5 word) : list word :=
  [reg_get FR 0; reg_get FR 1; reg_get FR 2; reg_get FR 3; reg_get FR 4; reg_get FR 5; reg_get FR 6; reg_get FR 7;
   reg_get FR 8; reg_get FR 9; reg_get FR 10; reg_get FR 11; reg_get FR 12; reg_get FR 13; reg_get FR 14; reg_get FR 15;
   reg_get FR 16; reg_get FR 17; reg_get FR 18; reg_get FR 19; reg_get FR 20; reg_get FR 21; reg_get FR 22; reg_get FR 23;
   reg_get FR 24; reg_get FR 25; reg_get FR 26; reg_get FR 27; reg_get FR 28; reg_get FR 29; reg_get FR 30; reg_get FR 31]%bv.

Lemma junk_vals_nth : forall R (r : reg), nth (ridx r) (junk_vals R) (Z_to_bv 64 0) = getr R r.
Proof.
  intros R r. pose proof (ridx_range r) as Hlt. rewrite <- (ridx_roundtrip r) at 2.
  set (n := ridx r) in *. clearbody n.
  do 32 (destruct n as [|n]; [reflexivity|]). exfalso. lia.
Qed.
Lemma fjunk_vals_nth : forall FR (r : reg), nth (ridx r) (fjunk_vals FR) (Z_to_bv 64 0) = reg_get FR r.
Proof.
  intros FR r. pose proof (ridx_range r) as Hlt. rewrite <- (ridx_roundtrip r) at 2.
  set (n := ridx r) in *. clearbody n.
  do 32 (destruct n as [|n]; [reflexivity|]). exfalso. lia.
Qed.

Lemma junk_vals_length : forall R, length (junk_vals R) = 32%nat.
Proof. reflexivity. Qed.
Lemma fjunk_vals_length : forall R, length (fjunk_vals R) = 32%nat.
Proof. reflexivity. Qed.

Lemma nth_map_seq_gen : forall {A} (f : nat -> A) len s n d, (n < len)%nat ->
  nth n (map f (seq s len)) d = f (s + n)%nat.
Proof.
  intros A f len. induction len as [|len IH]; intros s n d H; [lia|].
  cbn [seq map]. destruct n as [|n].
  - cbn [nth]. rewrite Nat.add_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma nth_map_seq : forall {A} (f : nat -> A) n len d, (n < len)%nat ->
  nth n (map f (seq 0 len)) d = f n.
Proof. intros. rewrite nth_map_seq_gen by assumption. reflexivity. Qed.

Lemma vals_ev_app_l : forall vals extra n, (n < length vals)%nat ->
  vals_ev (vals ++ extra) n = vals_ev vals n.
Proof. intros. unfold vals_ev. rewrite app_nth1 by assumption. reflexivity. Qed.

Lemma vals_ev_app_r : forall vals extra n,
  vals_ev (vals ++ extra) (length vals + n) = vals_ev extra n.
Proof. intros. unfold vals_ev. rewrite app_nth2_plus. reflexivity. Qed.

(* [comment removed for export] *)
Definition sr_vars (b : nat) : list expr :=
  ELit 0 :: map (fun i => EVar (b + i)) (seq 1 31).

(* [comment removed for export] *)
Lemma regs_ok_vars : forall vals R rest ebs,
  regs_ok (Env (vals_ev (vals ++ junk_vals R ++ rest)) ebs) (sr_vars (length vals)) R.
Proof.
  intros vals R rest ebs r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
  - pose proof (ridx_range r) as Hlt.
    assert (Hnz : ridx r <> 0%nat).
    { intros Hc. assert (r = 0%bv) by (apply ridx_inj; rewrite Hc; reflexivity). subst r.
      rewrite bv_eqb_refl in Hr0. discriminate. }
    unfold sr_vars. destruct (ridx r) as [|n] eqn:Hn; [lia|].
    cbn [nth]. rewrite nth_map_seq_gen by lia. cbn [edenot ev].
    unfold vals_ev. rewrite app_nth2 by lia.
    replace (length vals + (1 + n) - length vals)%nat with (S n) by lia.
    rewrite app_nth1 by (rewrite junk_vals_length; lia).
    rewrite <- Hn, junk_vals_nth. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fregs_ok_vars : forall vals FR rest ebs,
  fregs_ok (Env (vals_ev (vals ++ fjunk_vals FR ++ rest)) ebs) (sfr_vars (length vals)) FR.
Proof.
  intros vals FR rest ebs r. unfold sfr_get, sfr_vars. pose proof (ridx_range r) as Hlt.
  rewrite nth_map_seq by exact Hlt. cbn [edenot ev]. unfold vals_ev.
  rewrite app_nth2 by lia. rewrite app_nth1 by (rewrite fjunk_vals_length; lia).
  replace (length vals + ridx r - length vals)%nat with (ridx r) by lia.
  rewrite fjunk_vals_nth. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma env_app_regs : forall vals extra ebs sr R,
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R -> regs_ok (Env (vals_ev (vals ++ extra)) ebs) sr R.
Proof. intros. eapply regs_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

Lemma env_app_fregs : forall vals extra ebs sfr FR,
  sr_vars_lt (length vals) sfr = true ->
  fregs_ok (Env (vals_ev vals) ebs) sfr FR -> fregs_ok (Env (vals_ev (vals ++ extra)) ebs) sfr FR.
Proof. intros. eapply fregs_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

Lemma env_app_know : forall vals extra ebs M kn,
  kn_vars_lt (length vals) kn = true ->
  know_ok segs (Env (vals_ev vals) ebs) M kn -> know_ok segs (Env (vals_ev (vals ++ extra)) ebs) M kn.
Proof. intros. eapply know_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.

Lemma env_app_edenot : forall vals extra ebs e,
  expr_vars_lt (length vals) e = true ->
  edenot (Env (vals_ev (vals ++ extra)) ebs) e = edenot (Env (vals_ev vals) ebs) e.
Proof. intros. symmetry. eapply edenot_agree; [apply vals_app_agree | assumption]. Qed.

(* [comment removed for export] *)
Definition sr_after_call_j (sr : list expr) (kept : list nat) (jbase : nat) : list expr :=
  map (fun i => if existsb (Nat.eqb i) kept then nth i sr (ELit 0) else EVar (jbase + i))
      (seq 0 32).

Lemma sr_vars_lt_nth : forall b sr n, sr_vars_lt b sr = true -> expr_vars_lt b (nth n sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|e t IH]; intros n H; [destruct n; reflexivity|].
  cbn [sr_vars_lt] in H. apply andb_prop in H as [He Ht]. destruct n; [exact He | apply IH; exact Ht].
Qed.

Lemma regs_after_keeps : forall vals ebs sr R R' (kept : list reg),
  sr_vars_lt (length vals) sr = true ->
  regs_ok (Env (vals_ev vals) ebs) sr R ->
  (forall r : reg, In r kept -> getr R' r = getr R r) ->
  regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs)
          (sr_after_call_j sr (map ridx kept) (length vals)) R'.
Proof.
  intros vals ebs sr R R' kept Hlt HR Hk r.
  pose proof (ridx_range r) as Hr.
  unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
  - unfold sr_after_call_j. rewrite nth_map_seq by exact Hr.
    destruct (existsb (Nat.eqb (ridx r)) (map ridx kept)) eqn:Hex.
    + apply existsb_exists in Hex as (i & Hin & Heqi). apply Nat.eqb_eq in Heqi. subst i.
      apply in_map_iff in Hin as (r0 & Hr0' & Hin). apply ridx_inj in Hr0'. subst r0.
      rewrite (Hk _ Hin).
      pose proof (HR r) as Hv. unfold sr_get in Hv. rewrite Hr0 in Hv. rewrite Hv.
      eapply edenot_agree; [apply vals_app_agree|]. apply sr_vars_lt_nth. exact Hlt.
    + cbn [edenot ev]. unfold vals_ev. rewrite app_nth2 by lia.
      replace (length vals + ridx r - length vals)%nat with (ridx r) by lia.
      rewrite junk_vals_nth. reflexivity.
Qed.

(* [comment removed for export] *)
Definition sfr_after_call_j (sfr : list expr) (kept : list nat) (jbase : nat) : list expr :=
  map (fun i => if existsb (Nat.eqb i) kept then nth i sfr (ELit 0) else EVar (jbase + i))
      (seq 0 32).

Lemma fregs_after_keeps : forall vals ebs sfr FR FR' (kept : list reg),
  sr_vars_lt (length vals) sfr = true ->
  fregs_ok (Env (vals_ev vals) ebs) sfr FR ->
  (forall r : reg, In r kept -> reg_get FR' r = reg_get FR r) ->
  fregs_ok (Env (vals_ev (vals ++ fjunk_vals FR')) ebs)
           (sfr_after_call_j sfr (map ridx kept) (length vals)) FR'.
Proof.
  intros vals ebs sfr FR FR' kept Hlt HF Hk r.
  pose proof (ridx_range r) as Hr.
  unfold sfr_get, sfr_after_call_j. rewrite nth_map_seq by exact Hr.
  destruct (existsb (Nat.eqb (ridx r)) (map ridx kept)) eqn:Hex.
  - apply existsb_exists in Hex as (i & Hin & Heqi). apply Nat.eqb_eq in Heqi. subst i.
    apply in_map_iff in Hin as (r0 & Hr0' & Hin). apply ridx_inj in Hr0'. subst r0.
    rewrite (Hk _ Hin). pose proof (HF r) as Hv. unfold sfr_get in Hv. rewrite Hv.
    eapply edenot_agree; [apply vals_app_agree|]. apply sr_vars_lt_nth. exact Hlt.
  - cbn [edenot ev]. unfold vals_ev. rewrite app_nth2 by lia.
    replace (length vals + ridx r - length vals)%nat with (ridx r) by lia.
    rewrite fjunk_vals_nth. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rt_call : forall st (P : FPState -> bvmap 5 word -> (word -> option byte) -> Prop)
                       (ret : word) rom Q,
  (exists (FPI' : FPState) regs' mem',
      msteps segs st (mkst (FP:=FPI') regs' ret mem' rom) /\ P FPI' regs' mem') ->
  (forall (FPI' : FPState) regs' mem', P FPI' regs' mem' ->
      runs_to (mkst (FP:=FPI') regs' ret mem' rom) Q) ->
  runs_to st Q.
Proof.
  intros st P ret rom Q (FPI' & regs' & mem' & Hms & HP) Hk.
  eapply runs_to_fwd; [exact Hms | apply Hk; exact HP].
Qed.

(* [comment removed for export] *)
Lemma runs_to_contract : forall st (ret : word) rom
    (P : FPState -> bvmap 5 word -> (word -> option byte) -> Prop),
  runs_to st (fun st' => exists (FPI' : FPState) regs' mem',
                 st' = mkst (FP:=FPI') regs' ret mem' rom /\ P FPI' regs' mem') ->
  exists (FPI' : FPState) regs' mem',
    msteps segs st (mkst (FP:=FPI') regs' ret mem' rom) /\ P FPI' regs' mem'.
Proof.
  intros st ret rom P (st' & Hms & (FPI' & regs' & mem' & -> & HP)).
  exists FPI', regs', mem'. split; [exact Hms | exact HP].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Fixpoint find_read (i : nat) (scs : list sidecond) : option (saddr * nat * bool) :=
  match scs with
  | [] => None
  | SCReadBase a n sx (EVar j) :: rest => if Nat.eqb i j then Some (a, n, sx) else find_read i rest
  | _ :: rest => find_read i rest
  end.

Fixpoint fresh_reads (i cnt : nat) (scs : list sidecond) : list (saddr * nat * bool) :=
  match cnt with
  | O => []
  | S c => match find_read i scs with
           | Some r => r :: fresh_reads (S i) c scs
           | None => []
           end
  end.

Lemma sc_readbase_named : forall M ebs vals pre (v : word) post a n sx bs i,
  length (vals ++ pre) = i ->
  saddr_vars_lt i a = true ->
  rdn segs M (adenot (Env (vals_ev (vals ++ pre)) ebs) a) n = Some bs ->
  v = Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) ->
  sc_denot segs M (Env (vals_ev (vals ++ (pre ++ v :: post))) ebs) (SCReadBase a n sx (EVar i)).
Proof.
  intros M ebs vals pre v post a n sx bs i Hi Ha Hrd Hv. cbn [sc_denot]. exists bs.
  assert (Hag : env_agree i (Env (vals_ev (vals ++ pre)) ebs) (Env (vals_ev (vals ++ (pre ++ v :: post))) ebs)).
  { rewrite <- Hi, app_assoc. apply vals_app_agree. }
  subst v.
  split.
  - rewrite <- (adenot_agree i _ _ a Hag Ha). exact Hrd.
  - cbn [edenot ev]. unfold vals_ev. rewrite app_assoc, app_nth2 by lia. rewrite <- Hi, Nat.sub_diag. reflexivity.
Qed.

(* [comment removed for export] *)
Definition readable (M : word -> option byte) (lo hi : Z) : Prop :=
  forall (a : Z) (m : nat), (lo <= a)%Z -> (a + Z.of_nat m <= hi)%Z ->
  exists bs, rdn segs M (Z_to_bv 64 a) m = Some bs.

Lemma rdn_grows : forall M M' n (a : word),
  mem_grows M M' -> (exists bs, rdn segs M a n = Some bs) -> exists bs', rdn segs M' a n = Some bs'.
Proof.
  intros M M' n. induction n as [|n IH]; intros a Hg [bs Hbs]; [exists []; reflexivity|].
  cbn [rdn] in Hbs |- *.
  assert (Hb : exists b', match M' a with Some b => Some b | None => seg_rom segs a end = Some b').
  { destruct (M a) as [b|] eqn:HMa.
    - destruct (M' a) as [b'|] eqn:HM'a; [exists b'; reflexivity|].
      exfalso. apply (Hg a); [rewrite HMa; discriminate | exact HM'a].
    - destruct (M' a) as [b'|]; [exists b'; reflexivity|].
      destruct (seg_rom segs a) as [b|]; [exists b; reflexivity | discriminate]. }
  destruct Hb as [b' ->].
  destruct (match M a with Some b => Some b | None => seg_rom segs a end) as [b|]; [|discriminate].
  destruct (rdn segs M (a + 1) n) as [rest|] eqn:Hr; [|discriminate].
  destruct (IH (a + 1) Hg (ex_intro _ rest Hr)) as [rest' ->]. exists (b' :: rest'). reflexivity.
Qed.

Lemma readable_grows : forall M M' lo hi,
  mem_grows M M' -> readable M lo hi -> readable M' lo hi.
Proof. intros M M' lo hi Hg Hr a m H1 H2. eapply rdn_grows; [exact Hg | apply Hr; assumption]. Qed.

Lemma readable_mem_denot : forall E M log lo hi,
  readable M lo hi -> readable (mem_denot E M log) lo hi.
Proof. intros. eapply readable_grows; [apply mem_denot_grows | assumption]. Qed.

(* [comment removed for export] *)
Lemma readable_intro : forall M lo hi,
  (forall (a : Z) (m : nat), (lo <= a)%Z -> (a + Z.of_nat m <= hi)%Z -> exists bs, rdn segs M (Z_to_bv 64 a) m = Some bs) ->
  readable M lo hi.
Proof. intros M lo hi H. exact H. Qed.

Lemma readable_sub : forall M lo hi lo' hi',
  readable M lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> readable M lo' hi'.
Proof. intros M lo hi lo' hi' H H1 H2 a m Ha Hm. apply H; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_bv_lit : forall z (w : word), bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof. intros z w <-. apply Z_to_bv_bv_unsigned. Qed.

Lemma flat_intro : forall E b k n,
  (0 <= bv_unsigned (edenot E b) + k)%Z -> (0 <= n)%Z ->
  (bv_unsigned (edenot E b) + k < 2 ^ 64)%Z ->
  (bv_unsigned (edenot E b) + k + n <= 2 ^ 64)%Z ->
  flat E (SA b k) n.
Proof. intros. unfold flat, estart. cbn [a_base a_off]. lia. Qed.

Lemma adenot_lit0 : forall E a, adenot E (SA (ELit 0) a) = Z_to_bv 64 a.
Proof. intros. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_lit0. reflexivity. Qed.

(* [comment removed for export] *)
Lemma branch_taken_Z : forall c (x y : word),
  branch_taken c x y =
  match c with
  | BC_EQ => Z.eqb (bv_unsigned x) (bv_unsigned y)
  | BC_NE => negb (Z.eqb (bv_unsigned x) (bv_unsigned y))
  | BC_LT => Z.ltb (bv_signed x) (bv_signed y)
  | BC_GE => negb (Z.ltb (bv_signed x) (bv_signed y))
  | BC_LTU => Z.ltb (bv_unsigned x) (bv_unsigned y)
  | BC_GEU => negb (Z.ltb (bv_unsigned x) (bv_unsigned y))
  end.
Proof. intros c x y. destruct c; reflexivity. Qed.

(* [comment removed for export] *)
Lemma u_bool_word : forall b, bv_unsigned (bool_word b) = Z.b2z b.
Proof. intros [|]; reflexivity. Qed.
Lemma b2z_eqb0 : forall b, (Z.b2z b =? 0)%Z = negb b.
Proof. intros [|]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma u_lin_mod : forall E e,
  bv_unsigned (edenot E e) = ((fst (lin_of e) + tden E (snd (lin_of e))) mod 2 ^ 64)%Z.
Proof.
  intros E e. pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
  pose proof (u64_range (edenot E e)) as Hr.
  rewrite Hq. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma edenot_lin : forall E e,
  edenot E e = Z_to_bv 64 (fst (lin_of e) + tden E (snd (lin_of e)))%Z.
Proof.
  intros E e. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E e)). apply eqm_Z_to_bv.
  apply eqm_sym. pose proof (lin_of_sound E e) as H. unfold lden, uE in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma regs_same_on : forall E sr sr' R R' (l : list reg),
  regs_ok E sr R -> regs_ok E sr' R' ->
  forallb (fun r => expr_eqb (sr_get sr' r) (sr_get sr r)) l = true ->
  forall r, In r l -> getr R' r = getr R r.
Proof.
  intros E sr sr' R R' l HR HR' Hl r Hin.
  rewrite (HR r), (HR' r).
  apply forallb_forall with (x := r) in Hl; [| exact Hin].
  apply expr_eqb_eq in Hl. rewrite Hl. reflexivity.
Qed.

Lemma fregs_same_on : forall E sfr sfr' FR FR' (l : list reg),
  fregs_ok E sfr FR -> fregs_ok E sfr' FR' ->
  forallb (fun r => expr_eqb (sfr_get sfr' r) (sfr_get sfr r)) l = true ->
  forall r, In r l -> reg_get FR' r = reg_get FR r.
Proof.
  intros E sfr sfr' FR FR' l HF HF' Hl r Hin.
  rewrite (HF r), (HF' r).
  apply forallb_forall with (x := r) in Hl; [| exact Hin].
  apply expr_eqb_eq in Hl. rewrite Hl. reflexivity.
Qed.

End Drive.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac split_foralls :=
  repeat lazymatch goal with
  | |- scs_denot _ _ _ [] => constructor
  | |- scs_denot _ _ _ (_ :: _) => constructor; [| ]
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [| ]
  end.

(* [comment removed for export] *)
Ltac env_parts E k :=
  lazymatch E with
  | Env (vals_ev ?V) ?B => k V B
  | _ => let Ev := eval unfold E in E in
         lazymatch Ev with Env (vals_ev ?V) ?B => k V B end
  end.

(* [comment removed for export] *)
Ltac pose_u64_ranges :=
  repeat match goal with
  | |- context [bv_unsigned ?x] =>
      lazymatch goal with
      | H : (0 <= bv_unsigned x < _)%Z |- _ => fail
      | _ => pose proof (u64_range x)
      end
  end.

(* [comment removed for export] *)
Ltac ev_simpl E :=
  try unfold E; cbn [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals].
Ltac ev_simpl_in E H :=
  try unfold E in H; cbn [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.

(* [comment removed for export] *)
Ltac is_lin_candidate e :=
  lazymatch e with
  | EAlu ALU_ADD _ _ => idtac
  | EAlu ALU_SUB _ _ => idtac
  | EAlu ALU_SLL _ (ELit _) => idtac
  | EMd M_MUL (ELit _) _ => idtac
  | EMd M_MUL _ (ELit _) => idtac
  | _ => fail
  end.

Ltac linearize_with HK :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
      repeat match goal with
      | |- context [bv_unsigned (edenot E ?e)] =>
          is_lin_candidate e;
          let l := eval vm_compute in (lin_of e) in
          first
            [ rewrite (lin_nowrap_sound segs E M kn e HK ltac:(vm_compute; reflexivity))
            | rewrite (u_lin_mod E e) ];
          change (lin_of e) with l; cbn [fst snd tden]; unfold uE
      end
  end.

(* [comment removed for export] *)
Ltac mod_small_all :=
  repeat match goal with
  | |- context [ (?a mod ?b)%Z ] => rewrite (Z.mod_small a b) by (pose_u64_ranges; lia)
  end.

Ltac linearize :=
  match goal with
  | HK : know_ok _ ?E _ _ |- context [edenot ?E _] => linearize_with HK
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac rewrite_getr :=
  repeat match goal with
  | H : getr ?R ?r = _ |- context [getr ?R ?r] => rewrite H
  end.

(* [comment removed for export] *)
Ltac term_has_var t := match t with context [?x] => is_var x end.
Ltac ground_mod_fp :=
  repeat match goal with
  | |- context [ (?a mod ?b)%Z ] =>
      tryif term_has_var a then fail else
      tryif term_has_var b then fail else
      let v := eval vm_compute in (a mod b)%Z in change ((a mod b)%Z) with v
  end.

(* [comment removed for export] *)
Ltac sc_simpl :=
  unfold sc_denot, flat, estart, elenZ, adenot; cbn [a_base a_off];
  rewrite ?branch_taken_Z; cbv beta iota;
  linearize;
  cbn [edenot fop1_denot fop2_denot fop3_denot];
  match goal with
  | HK : know_ok _ ?E _ _ |- _ => ev_simpl E
  | _ => cbn [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals]
  end;
  unfold fcmp_res; rewrite ?u_bool_word;
  rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; ground_mod_fp; rewrite ?b2z_eqb0, ?negb_involutive;
  rewrite_getr; mod_small_all.

(* [comment removed for export] *)
Ltac br_simpl_in E H :=
  rewrite ?branch_taken_Z in H; cbv beta iota in H;
  cbn [edenot fop1_denot fop2_denot fop3_denot] in H; unfold fcmp_res in H; ev_simpl_in E H;
  rewrite ?u_bool_word, ?Z_to_bv_unsigned, ?bv_wrap64_mod in H;
  rewrite ?b2z_eqb0, ?negb_involutive in H;
  try (apply (f_equal negb) in H; rewrite negb_involutive in H; cbn [negb] in H).

Ltac sc_auto_fp extra :=
  first
    [ assumption
    | sc_simpl; first
        [ assumption
        | extra
        | lia
        | sc_store
        | match goal with |- _ /\ _ => repeat split; first [assumption | extra | lia | sc_store] end
        | pose_u64_ranges; first [lia | idtac] ] ].

(* [comment removed for export] *)
Ltac readable_fwd :=
  match goal with
  | HK : know_ok ?segs ?E ?M' _ |- _ =>
      repeat match goal with
      | H : readable segs ?M0 ?lo ?hi |- _ =>
          lazymatch M' with
          | M0 => fail
          | mem_denot E M0 ?log => apply (readable_mem_denot segs E M0 log lo hi) in H
          end
      end
  end.

(* [comment removed for export] *)
Ltac run_fp_with_h HR HF HK fuel stops scr chints keep extra :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
   lazymatch type of HF with
   | fregs_ok _ ?sfr (@fp_regs ?FPI) =>
     lazymatch type of HK with
     | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- runs_to _ (@mkst FPI R (Z_to_bv 64 ?pc) M ?rom) ?Q =>
        env_parts E ltac:(fun VALS EBS =>
        let NX := eval cbn in (length VALS) in
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr sfr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn chints) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (rt_run segs fuel stops scr chints pc sr sfr kn NX ss' scs scr' kn' scs2 hs2 E M rom R FPI Q);
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HF | exact HK
            | split_foralls; sc_auto_fp extra
            | split_foralls; sc_auto_fp extra
            | clear HR HF HK;
              let R' := fresh "R" in let FPI' := fresh "FPI" in
              let M' := fresh "M" in let EQM := fresh "EQM" in let HLF := fresh "HLF" in
              intros R' FPI' M' HR HF HK EQM HLF; cbn [s_pc s_regs s_fregs s_log] in HR, HF, EQM, HLF |- *;
              try change (mem_denot E M []) with M in EQM;
              lazymatch keep with
              | true => idtac
              | false => clear HLF; subst M'; readable_fwd;
                         try clear R; try clear FPI;
                         try rename R' into R; try rename FPI' into FPI
              end ]
          end
        end)
      end
     end
   end
  end.

Ltac run_fp_with HR HF HK fuel stops scr keep extra :=
  run_fp_with_h HR HF HK fuel stops scr (@nil bool) keep extra.

(* [comment removed for export] *)
Definition keep_all : list bool := repeat true 512.

(* [comment removed for export] *)
Ltac with_state_hyps k :=
  lazymatch goal with
  | |- runs_to _ (@mkst ?FPI ?R _ ?M _) _ =>
      match goal with
      | HR : regs_ok _ _ R, HF : fregs_ok _ _ (@fp_regs FPI), HK : know_ok _ _ M _ |- _ => k HR HF HK
      end
  end.

Tactic Notation "run_fp" constr(fuel) constr(stops) constr(scr) constr(keep) :=
  with_state_hyps ltac:(fun HR HF HK => run_fp_with HR HF HK fuel stops scr keep fail).

Tactic Notation "run_fp" constr(fuel) constr(stops) constr(scr) constr(keep) "by" tactic3(extra) :=
  with_state_hyps ltac:(fun HR HF HK => run_fp_with HR HF HK fuel stops scr keep extra).

Tactic Notation "run_fp" constr(fuel) constr(stops) constr(scr) constr(keep) "hints" constr(chints) :=
  with_state_hyps ltac:(fun HR HF HK => run_fp_with_h HR HF HK fuel stops scr chints keep fail).

Tactic Notation "run_fp" constr(fuel) constr(stops) constr(scr) constr(keep) "hints" constr(chints) "by" tactic3(extra) :=
  with_state_hyps ltac:(fun HR HF HK => run_fp_with_h HR HF HK fuel stops scr chints keep extra).

(* [comment removed for export] *)
Definition noscr : scripts := SCR [] [] [].
Definition dirs (l : list bool) : scripts := SCR l [] [].

(* [comment removed for export] *)
Ltac branch_case_with HR HF HK Hc :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
   lazymatch type of HF with
   | fregs_ok _ ?sfr _ =>
     lazymatch type of HK with
     | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- runs_to _ (@mkst _ R (Z_to_bv 64 ?pc) M ?rom) ?Q =>
        env_parts E ltac:(fun VALS EBS =>
        let NX := eval cbn in (length VALS) in
        let r := eval vm_compute in (sym_exec segs 1%nat true (@nil Z) (dirs [true]) (SS pc sr sfr [] kn NX) []) in
        lazymatch r with
        | (_, [SCBr true ?c ?a ?b], _) =>
            destruct (branch_taken c (edenot E a) (edenot E b)) eqn:Hc;
            [ run_fp_with HR HF HK 1%nat (@nil Z) (dirs [true]) false fail
            | run_fp_with HR HF HK 1%nat (@nil Z) (dirs [false]) false fail ]
        | _ => fail "branch_case: no undecided branch at this pc"
        end)
      end
     end
   end
  end.

Tactic Notation "branch_case" "as" ident(Hc) :=
  with_state_hyps ltac:(fun HR HF HK => branch_case_with HR HF HK Hc).

(* [comment removed for export] *)
Ltac regv HR r :=
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
    let e := eval vm_compute in (sr_get sr r) in
    rewrite (reg_val E sr R r HR); change (sr_get sr r) with e; cbn [edenot fop1_denot fop2_denot fop3_denot];
    ev_simpl E
  end.
(* [comment removed for export] *)
Ltac regv_lin HR r :=
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
    let e := eval vm_compute in (sr_get sr r) in
    let l := eval vm_compute in (lin_of e) in
    rewrite (reg_val E sr R r HR); change (sr_get sr r) with e;
    rewrite (edenot_lin E e); change (lin_of e) with l; cbn [fst snd tden]; unfold uE;
    cbn [edenot fop1_denot fop2_denot fop3_denot]; ev_simpl E
  end.

Ltac fregv HF r :=
  lazymatch type of HF with fregs_ok ?E ?sfr ?FR =>
    let e := eval vm_compute in (sfr_get sfr r) in
    rewrite (HF r); change (sfr_get sfr r) with e; cbn [edenot fop1_denot fop2_denot fop3_denot];
    ev_simpl E
  end.

(* [comment removed for export] *)
Ltac show_reg HR r :=
  lazymatch type of HR with regs_ok ?E ?sr ?R =>
    let e := eval vm_compute in (sr_get sr r) in idtac r ":=" e end.
Ltac show_freg HF r :=
  lazymatch type of HF with fregs_ok ?E ?sfr ?FR =>
    let e := eval vm_compute in (sfr_get sfr r) in idtac r ":=" e end.

(* [comment removed for export] *)
Ltac probe_run_with HR HF HK fuel stops scr :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
   lazymatch type of HF with
   | fregs_ok _ ?sfr _ =>
     lazymatch type of HK with
     | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- runs_to _ (@mkst _ R (Z_to_bv 64 ?pc) M ?rom) ?Q =>
        env_parts E ltac:(fun VALS EBS =>
        let NX := eval cbn in (length VALS) in
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr sfr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
            let p := eval vm_compute in (s_pc ss') in
            idtac "stops at pc" p "sideconds:" scs "scripts left:" scr' "next var:";
            let n := eval vm_compute in (s_next ss') in idtac n
        end)
      end
     end
   end
  end.

Tactic Notation "probe_run" constr(fuel) constr(stops) constr(scr) :=
  with_state_hyps ltac:(fun HR HF HK => probe_run_with HR HF HK fuel stops scr).

(* [comment removed for export] *)
Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
Ltac vm_decide :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_compute; reflexivity
  end.

(* [comment removed for export] *)
Ltac fin_ret_with HR :=
  lazymatch goal with
  | |- runs_to ?segs (@mkst ?FPI ?R (Z_to_bv 64 ?pc) ?M ?rom) ?Q =>
      let f := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch f with
      | Some ?w =>
          eapply (rt_ret segs FPI R (Z_to_bv 64 pc) M rom w Q);
          [ vm_refl
          | vm_decide
          | vm_decide
          | try (regv HR (1%bv : reg); rewrite_getr; solve [assumption | auto])
          | ]
      end
  end.

Tactic Notation "fin_ret" :=
  with_state_hyps ltac:(fun HR HF HK => fin_ret_with HR).

(* [comment removed for export] *)
Ltac fin_here :=
  lazymatch goal with
  | |- runs_to _ (@mkst ?I ?R ?pc ?M ?rom) _ =>
      apply runs_to_here;
      first [ exists I, R, M; split; [first [reflexivity | f_equal] |] | idtac ]
  end.
