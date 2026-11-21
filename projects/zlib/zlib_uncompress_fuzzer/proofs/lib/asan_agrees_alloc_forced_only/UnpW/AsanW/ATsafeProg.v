(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad MSafe MPaths STree Stdio Harness Adapter Driver TargetSafe StepB EquivShared EquivProg RSim MI_Inv LB_Inv LB_Sum SizeHist RSimProg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import Keeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AProto ATsafeCore.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import CMonad.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require HarnessC AdapterC DriverC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import CLogicA.   (* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation M := Monad.M.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Section CANSEC1. Context {rc : runConstT}.
Section Prog.
Context {St : Type}.
Variable NMAX : nat.
Local Notation TSM := (TSM NMAX (St:=St)).
Local Notation preT := (preT (St:=St)).
Local Notation postM := (postM (St:=St)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma TSM_bind' {X Y} (P : preT) (m : M St X) (f : X -> M St Y) (Q1 : postM X) (Q : postM Y) :
  TSM P m Q1 -> (forall x, TSM (Q1 x) (f x) Q) -> TSM P (mbind m f) Q.
Proof. intros Hm Hf. eapply TSM_bind; [exact Hm|]. intros x. eapply TSM_pre; [apply Hf|]. intros RNG A s mo [_ H]; exact H. Qed.

Lemma TSM_seq {X Y} (P P1 : preT) (m : M St X) (f : X -> M St Y) (Q : postM Y) :
  TSM P m (fun _ => P1) -> (forall x, TSM P1 (f x) Q) -> TSM P (mbind m f) Q.
Proof. intros Hm Hf. eapply TSM_bind'; [exact Hm| exact Hf]. Qed.

Lemma TSM_ret' {X} (x : X) (P : preT) :
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) -> TSM P (mret x) (fun _ => P).
Proof. intros HA. apply TSM_ret. intros RNG A s mo Hp. split; [apply (HA _ _ _ _ Hp)| exact Hp]. Qed.

Lemma TSM_false {X} (m : M St X) (Q : postM X) : TSM (fun _ _ _ _ => False) m Q.
Proof. intros RNG A s mo []. Qed.

(* [comment removed for export] *)
Lemma TSM_pointwise {X} (P : preT) (m : M St X) (Q : postM X) :
  (forall RNG0 A0 s0 mo0, P RNG0 A0 s0 mo0 -> TSM (fun RNG A s mo => RNG = RNG0 /\ A = A0 /\ s = s0 /\ mo = mo0) m Q) -> TSM P m Q.
Proof. intros H RNG A s mo Hp. apply (H _ _ _ _ Hp). repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma TSM_pure' {X} (phi : Prop) (Pr : preT) (m : M St X) (Q : postM X) :
  (phi -> TSM Pr m Q) -> TSM (fun RNG A s mo => phi /\ Pr RNG A s mo) m Q.
Proof. intros H RNG A s mo [Hphi Hp]. apply (H Hphi). exact Hp. Qed.

(* [comment removed for export] *)
Lemma TSM_pure_r0 {X} (phi : Prop) (Pr : preT) (m : M St X) (Q : postM X) :
  TSM Pr m Q -> TSM (fun RNG A s mo => Pr RNG A s mo /\ phi) m Q.
Proof. intros H RNG A s mo [Hp _]. apply H. exact Hp. Qed.
Lemma TSM_pure_r {X} (phi : Prop) (Pr : preT) (m : M St X) (Q : postM X) :
  (phi -> TSM Pr m Q) -> TSM (fun RNG A s mo => Pr RNG A s mo /\ phi) m Q.
Proof. intros H RNG A s mo [Hp Hphi]. apply (H Hphi). exact Hp. Qed.

Lemma TSM_if' {X} (b : bool) (Pr : preT) (m1 m2 : M St X) (Q : postM X) :
  (b = true -> TSM Pr m1 Q) -> (b = false -> TSM Pr m2 Q) -> TSM Pr (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; [apply H1| apply H2]; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Context {P : Type}.
(* [comment removed for export] *)
Variable JX : list (P * Z) -> Z -> preT.
Hypothesis JX_acct : forall Y v RNG A s mo, JX Y v RNG A s mo -> acct_ok NMAX RNG A mo.
Hypothesis JX_perm : forall Y Y' v RNG A s mo, Permutation Y Y' -> JX Y v RNG A s mo -> JX Y' v RNG A s mo.
Hypothesis JX_credit : forall Y v v' RNG A s mo, 0 <= v' <= v -> JX Y v RNG A s mo -> JX Y v' RNG A s mo.
Hypothesis JX_nonneg : forall Y v RNG A s mo, JX Y v RNG A s mo -> 0 <= v.
Hypothesis JX_io : forall n Y v RNG A s mo rsp mo' evs, io_node n -> nstep n mo rsp mo' evs -> JX Y v RNG A s mo -> JX Y v RNG A s mo'.
(* [comment removed for export] *)
Variable QOV : Z.
Hypothesis HQOV : 0 <= QOV.
(* [comment removed for export] *)
Variables (NREQ : nat) (RMAX : Z).

Local Notation sizes := (map (@snd P Z)).
Local Notation names := (map (@fst P Z)).

(* [comment removed for export] *)
Definition TSJ {X} (Y : list (P * Z)) (v : Z) (m : M St X) : Prop := TSM (JX Y v) m (fun _ => JX Y v).

Lemma TSJ_ret {X} Y v (x : X) : TSJ Y v (mret x).
Proof. apply TSM_ret'. apply JX_acct. Qed.

Lemma TSJ_munr {X} Y v : TSJ Y v (munr (A:=X)).
Proof. unfold TSJ. apply TSM_munr. apply JX_acct. Qed.

Lemma TSJ_bind {X Y0} Y v (m : M St X) (f : X -> M St Y0) : TSJ Y v m -> (forall x, TSJ Y v (f x)) -> TSJ Y v (mbind m f).
Proof. intros Hm Hf. unfold TSJ. eapply TSM_seq; [exact Hm| exact Hf]. Qed.

Lemma TSJ_if {X} (b : bool) Y v (m1 m2 : M St X) : TSJ Y v m1 -> TSJ Y v m2 -> TSJ Y v (if b then m1 else m2).
Proof. intros H1 H2. destruct b; assumption. Qed.

(* [comment removed for export] *)
Lemma TSJ_msys_io {X} Y v n (dec : resp -> option X) : io_node n -> TSJ Y v (msys n dec).
Proof.
  intros Hio. unfold TSJ. apply TSM_msys_io; [exact Hio| apply JX_acct|].
  intros RNG A s mo rsp mo' evs x HJ Hst _. eapply JX_io; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stdio.
Variables (get : St -> stdout_st) (set : stdout_st -> St -> St).
Hypothesis JX_so : forall Y v RNG A s mo w, JX Y v RNG A s mo -> JX Y v RNG A (set w s) mo.

Lemma rd_so_ok : forall Y v, TSJ Y v (rd_so get).
Proof.
  intros Y v. unfold rd_so, TSJ. eapply TSM_bind'; [apply TSM_get; apply JX_acct|]. intros so.
  apply TSM_ret. intros RNG A s mo [_ H]. split; [eapply JX_acct; exact H| exact H].
Qed.

Lemma upd_so_ok : forall Y v f, TSJ Y v (upd_so get set f).
Proof.
  intros Y v f. unfold upd_so, TSJ. eapply TSM_post; [apply TSM_upd; apply JX_acct|].
  cbv beta. intros [] RNG A s mo _ (s0 & -> & H). apply JX_so. exact H.
Qed.

Lemma stdio_write_loop_ok : forall Y v fuel fd iov, TSJ Y v (stdio_write_loop fuel fd iov).
Proof.
  intros Y v fuel. induction fuel as [|fuel IH]; intros fd iov; cbn [stdio_write_loop].
  - apply TSJ_munr.
  - eapply TSJ_bind; [apply TSJ_msys_io; exact I|]. intros cnt. apply TSJ_if; [apply TSJ_ret| apply IH].
Qed.

Lemma stdio_write_ok : forall Y v fd buf s, TSJ Y v (stdio_write fd buf s).
Proof. intros. unfold stdio_write. apply TSJ_if; [apply TSJ_munr| apply stdio_write_loop_ok]. Qed.

Lemma stdout_stdio_write_ok : forall Y v s, TSJ Y v (stdout_stdio_write get set s).
Proof.
  intros. unfold stdout_stdio_write. eapply TSJ_bind; [apply rd_so_ok|]. intros so.
  eapply TSJ_bind; [apply stdio_write_ok|]. intros _. apply upd_so_ok.
Qed.

Lemma stdout_writefn_ok : forall Y v s, TSJ Y v (stdout_writefn get set s).
Proof.
  intros. unfold stdout_writefn. eapply TSJ_bind; [apply rd_so_ok|]. intros so.
  eapply TSJ_bind; [| intros _; apply stdout_stdio_write_ok].
  apply TSJ_if; [| apply TSJ_ret].
  eapply TSJ_bind; [apply upd_so_ok|]. intros _.
  eapply TSJ_bind; [apply TSJ_msys_io; exact I|]. intros [e|w]; [apply upd_so_ok| apply TSJ_munr].
Qed.

Lemma stdout_towrite_ok : forall Y v, TSJ Y v (stdout_towrite get set).
Proof. intros. unfold stdout_towrite. apply upd_so_ok. Qed.

Lemma stdout_fwritex_ok : forall Y v s, TSJ Y v (stdout_fwritex get set s).
Proof.
  intros. unfold stdout_fwritex. eapply TSJ_bind; [apply stdout_towrite_ok|]. intros _.
  eapply TSJ_bind; [apply rd_so_ok|]. intros so.
  apply TSJ_if; [apply stdout_writefn_ok|]. apply TSJ_if; [| apply upd_so_ok].
  eapply TSJ_bind; [apply TSJ_if; [apply stdout_writefn_ok| apply TSJ_ret]|]. intros _. apply upd_so_ok.
Qed.

Lemma out_pieces_ok : forall Y v ps, TSJ Y v (out_pieces get set ps).
Proof.
  intros Y v ps. induction ps as [|p ps IH]; cbn [out_pieces]; [apply TSJ_ret|].
  eapply TSJ_bind; [apply stdout_fwritex_ok|]. intros _. exact IH.
Qed.

Lemma stdout_vprintf_ok : forall Y v ps, TSJ Y v (stdout_vprintf get set ps).
Proof. intros. unfold stdout_vprintf. eapply TSJ_bind; [apply stdout_towrite_ok|]. intros _. apply out_pieces_ok. Qed.

Lemma stdout_exit_flush_ok : forall Y v, TSJ Y v (stdout_exit_flush get set).
Proof.
  intros. unfold stdout_exit_flush. eapply TSJ_bind; [apply rd_so_ok|]. intros so.
  apply TSJ_if; [apply stdout_writefn_ok| apply TSJ_ret].
Qed.

Lemma stderr_pieces_ok : forall Y v ps buf, TSJ Y v (stderr_pieces (St:=St) buf ps).
Proof.
  intros Y v ps. induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [apply TSJ_ret|].
  apply TSJ_if; [| apply IH]. eapply TSJ_bind; [apply stdio_write_ok|]. intros _. apply IH.
Qed.

Lemma stderr_fprintf_ok : forall Y v ps, TSJ Y v (stderr_fprintf (St:=St) ps).
Proof. intros. unfold stderr_fprintf. eapply TSJ_bind; [apply stderr_pieces_ok|]. intros buf. apply stdio_write_ok. Qed.

Lemma stderr_fwrite_ok : forall Y v s, TSJ Y v (stderr_fwrite (St:=St) s).
Proof. intros. unfold stderr_fwrite. apply TSJ_if; [apply stdio_write_ok| apply TSJ_ret]. Qed.

(* [comment removed for export] *)
Lemma s_diag_ok : forall Y v d, TSJ Y v (s_diag d).
Proof. intros Y v d. destruct d; cbn [s_diag]; first [apply stderr_fprintf_ok | apply stderr_fwrite_ok]. Qed.

Lemma s_emit_ok : forall Y v z, TSJ Y v (s_emit get set z).
Proof. intros. unfold s_emit. apply stdout_vprintf_ok. Qed.
End Stdio.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma open_ok : forall Y v path, TSJ Y v (msys (NOpen path) dec_open).
Proof. intros. apply TSJ_msys_io. exact I. Qed.

Lemma close_ok : forall Y v fd, TSJ Y v (msys (NClose fd) dec_close).
Proof. intros. apply TSJ_msys_io. exact I. Qed.

Lemma read_ok : forall Y v fd buf cnt, 0 <= cnt < 2^64 ->
  TSM (JX Y v) (msys (NRead fd buf cnt) (dec_read buf cnt))
      (fun a RNG A s mo => JX Y v RNG A s mo /\ match a with RdData bs => zlength bs <= cnt | RdErr _ => True end).
Proof.
  intros Y v fd buf cnt Hcnt. apply TSM_msys_io; [exact I| apply JX_acct|].
  intros RNG A s mo rsp mo' evs x HJ Hst Hdec. split; [eapply (JX_io (NRead fd buf cnt)); eauto; exact I|].
  destruct (dec_read_Some buf cnt rsp x ltac:(lia) Hdec) as [ci Hx]. destruct x as [e|bs]; [exact I|].
  unfold zlength. lia.
Qed.

Lemma exit_node_ok : forall Y v c (Q : postM Empty_set), TSM (JX Y v) (msys (NExit c) dec_exit) Q.
Proof.
  intros Y v c Q RNG A s mo HJ. unfold msys, enode.
  apply TS_io; [exact I| eapply JX_acct; exact HJ|].
  intros rsp mo' evs Hst _. cbn [nstep] in Hst. destruct Hst.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma TS_tall : forall {X} (t : itree node (exc X)) RNG A mo (Q : postT X) (Pl : X -> Prop),
  TS NMAX RNG A t mo (EQ Q) -> tall Pl t -> TS NMAX RNG A t mo (EQ (fun x RNG A mo => Q x RNG A mo /\ Pl x)).
Proof.
  intros X t. induction t as [[|x]|n k IH]; intros RNG A mo Q Pl HT HP; cbn in HT, HP |- *.
  - exact HT.
  - destruct HT as [HA HQ]. split; [exact HA|]. split; [exact HQ| exact HP].
  - destruct HT as (HA & HS & HK). split; [exact HA|]. split; [exact HS|].
    intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (RNG' & A' & HF & HL & HT').
    exists RNG', A'. split; [exact HF|]. split; [exact HL|]. apply IH; [exact HT'| apply HP].
Qed.

Lemma TSM_tall {X} (Pr : preT) (m : M St X) (Q : postM X) (Pl : X * St -> Prop) :
  TSM Pr m Q -> (forall s, tall Pl (m s)) -> TSM Pr m (fun x RNG A s mo => Q x RNG A s mo /\ Pl (x, s)).
Proof.
  intros H HP RNG A s mo Hp. unfold MQ.
  eapply TS_mono; [eapply TS_tall; [apply (H _ _ _ _ Hp)| apply HP]|].
  intros [|[x s']] RNG' A' mo' _ HQ; cbn in HQ |- *; [exact I| exact HQ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Target.
Variables (malloc : Z -> M St (option P)) (free : P -> M St unit) (emit : Z -> M St unit).

(* [comment removed for export] *)
Hypothesis Um : forall Y v n, 0 <= n <= REQMAX -> HISTOK (n :: sizes Y) ->
  TSM (fun RNG A s mo => JX Y v RNG A s mo /\ n + QOV <= v) (malloc n)
      (fun r RNG A s mo => exists q, r = Some q /\ JX ((q, n) :: Y) (v - n - QOV) RNG A s mo /\ n < 2^63).
Hypothesis Uf : forall Y v p n, TSM (JX ((p, n) :: Y) v) (free p) (fun _ => JX Y v).
Hypothesis Uemit : forall Y v z, TSJ Y v (emit z).

(* [comment removed for export] *)
Lemma malloc_seq {X} Y v n (k : option P -> M St X) (Q : postM X) :
  0 <= n <= REQMAX -> HISTOK (n :: sizes Y) ->
  (forall q, n < 2^63 -> TSM (JX ((q, n) :: Y) (v - n - QOV)) (k (Some q)) Q) ->
  TSM (fun RNG A s mo => JX Y v RNG A s mo /\ n + QOV <= v) (mbind (malloc n) k) Q.
Proof.
  intros Hn HH Hk. eapply TSM_bind'; [apply Um; [exact Hn| exact HH]|].
  intros [q|]; cbv beta.
  - apply (TSM_pure _ _ (n < 2^63)); [intros RNG A s mo (q' & _ & _ & Hlt); exact Hlt|]. intros Hlt.
    eapply TSM_pre; [apply Hk; exact Hlt|]. intros RNG A s mo (q' & E & HJ & _). injection E as ->. exact HJ.
  - eapply TSM_pre; [apply TSM_false|]. intros RNG A s mo (q' & E & _). discriminate E.
Qed.

(* [comment removed for export] *)
Lemma free_seq {X} Y v p n (k : unit -> M St X) (Q : postM X) :
  TSM (JX Y v) (k tt) Q -> TSM (JX ((p, n) :: Y) v) (mbind (free p) k) Q.
Proof. intros Hk. eapply TSM_seq; [apply Uf|]. intros []. exact Hk. Qed.

Definition olist (sb : option (P * Z)) : list (P * Z) := match sb with Some b => [b] | None => [] end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable script : list Z -> list Z.
Hypothesis Hscript : forall data, (length (script data) <= NREQ)%nat /\ Forall (fun n => 0 <= n <= RMAX) (script data).
Hypothesis HNREQ : (NREQ <= 2)%nat.
Hypothesis HRMAX : 0 <= RMAX <= REQMAX.
Local Notation fuzz1 := (Harness.fuzz_one malloc free script).

(* [comment removed for export] *)
Definition FUZZ_COST : Z := Z.of_nat NREQ * (RMAX + QOV).
Lemma FUZZ_COST_nonneg : 0 <= FUZZ_COST. Proof. unfold FUZZ_COST. clear - HQOV HRMAX. nia. Qed.

Lemma alloc_all_ok : forall ns T X v,
  Forall (fun n => 0 <= n <= RMAX) ns -> (length T + length X + length ns <= 4)%nat ->
  Z.of_nat (length ns) * (RMAX + QOV) <= v ->
  TSM (JX (T ++ X) v) (alloc_all malloc ns (names T))
      (fun ps RNG A s mo => exists T', ps = names T' /\ (length T' <= length T + length ns)%nat
                                      /\ JX (T' ++ X) (v - Z.of_nat (length ns) * (RMAX + QOV)) RNG A s mo).
Proof.
  induction ns as [|n ns IH]; intros T X v Hns HL Hv; cbn [alloc_all].
  - apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. exists T. split; [reflexivity|]. split; [lia|].
    eapply JX_credit; [| exact HJ]. pose proof (JX_nonneg _ _ _ _ _ _ HJ). cbn [length]. lia.
  - inversion Hns as [|n' ns' Hn Hns' E]; subst. cbn [length] in HL, Hv |- *.
    assert (HK : 0 <= Z.of_nat (length ns) * (RMAX + QOV)) by nia.
    eapply TSM_pre; [apply (malloc_seq (T ++ X) v n)|].
    + lia.
    + apply HISTOK_amb0. rewrite length_map, length_app. lia.
    + intros q _. cbv beta iota.
      eapply TSM_post; [apply (IH ((q, n) :: T) X (v - n - QOV) Hns'); [cbn [length]; lia| nia]|].
      cbv beta. intros ps RNG A s mo _ (T' & -> & HLT & HJ). exists T'. split; [reflexivity|]. split; [cbn [length] in HLT |- *; lia|].
      eapply JX_credit; [| exact HJ]. pose proof (JX_nonneg _ _ _ _ _ _ HJ). nia.
    + intros RNG A s mo HJ. split; [exact HJ| nia].
Qed.

Lemma free_all_ok : forall T X v, TSM (JX (T ++ X) v) (free_all free (names T)) (fun _ => JX X v).
Proof.
  induction T as [|[p n] T IH]; intros X v; cbn [free_all map fst app].
  - apply TSM_ret'. apply JX_acct.
  - apply free_seq. apply IH.
Qed.

Lemma fuzz_one_ok : forall X v data, (length X <= 2)%nat -> FUZZ_COST <= v ->
  TSM (JX X v) (fuzz1 data) (fun _ => JX X (v - FUZZ_COST)).
Proof.
  intros X v data HLX Hv. unfold Harness.fuzz_one. destruct (Hscript data) as [SL SS].
  assert (HK : Z.of_nat (length (script data)) * (RMAX + QOV) <= FUZZ_COST) by (unfold FUZZ_COST; nia).
  eapply TSM_bind'; [apply (alloc_all_ok (script data) [] X v SS); [cbn [length]; lia| lia]|].
  intros ps. apply TSM_exI. intros T'. apply TSM_pure'. intros ->. apply TSM_pure'. intros _.
  eapply TSM_seq; [apply free_all_ok|]. intros _.
  apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|].
  eapply JX_credit; [| exact HJ]. pose proof (JX_nonneg _ _ _ _ _ _ HJ). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_calls_ok : forall n X payload rcd v, (length X <= 2)%nat -> Z.of_nat n * FUZZ_COST <= v ->
  TSM (JX X v) (run_calls fuzz1 emit n payload rcd) (fun _ => JX X (v - Z.of_nat n * FUZZ_COST)).
Proof.
  pose proof FUZZ_COST_nonneg as F0.
  induction n as [|n IH]; intros X payload rcd v HLX Hv; cbn [run_calls].
  - apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. eapply JX_credit; [| exact HJ].
    pose proof (JX_nonneg _ _ _ _ _ _ HJ). lia.
  - eapply TSM_bind'; [apply fuzz_one_ok; [exact HLX| nia]|]. intros rcd'.
    eapply TSM_seq; [apply Uemit|]. intros _.
    eapply TSM_post; [apply IH; [exact HLX| nia]|].
    cbv beta. intros x RNG A s mo _ HJ. eapply JX_credit; [| exact HJ]. pose proof (JX_nonneg _ _ _ _ _ _ HJ). nia.
Qed.

(* [comment removed for export] *)
Definition RUN_COST : Z := MAX_INPUT + QOV + 4 * FUZZ_COST.
Lemma RUN_COST_nonneg : 0 <= RUN_COST.
Proof. pose proof FUZZ_COST_nonneg as F0. unfold RUN_COST, MAX_INPUT. clear - F0 HQOV. lia. Qed.

Theorem target_run_ok : forall X cfg payload v, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> RUN_COST <= v ->
  TSM (JX X v) (target_run malloc free fuzz1 emit cfg payload) (fun _ => JX X (v - RUN_COST)).
Proof.
  intros X cfg payload v HLX Hp Hv. unfold target_run.
  assert (Hpl : 0 <= zlength payload) by (unfold zlength; lia).
  pose proof FUZZ_COST_nonneg as F0.
  assert (HN : 0 <= Z.of_nat (Z.to_nat (1 + Z.land cfg 3)) <= 4).
  { assert (HL3 : Z.land cfg 3 = cfg mod 4) by (apply (Z.land_ones cfg 2); lia).
    pose proof (Z.mod_pos_bound cfg 4 ltac:(lia)). lia. }
  set (NC := Z.to_nat (1 + Z.land cfg 3)) in *.
  eapply TSM_bind' with (Q1 := fun a RNG A s mo => exists ob w, a = Some (option_map fst ob) /\ v - (MAX_INPUT + QOV) <= w
                                                /\ JX (olist ob ++ X) w RNG A s mo).
  { apply TSM_if'; intros C.
    - apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. exists None, v. cbn. split; [reflexivity|]. split; [unfold RUN_COST, MAX_INPUT; lia| exact HJ].
    - apply Z.eqb_neq in C. eapply TSM_pre; [apply (malloc_seq X v (zlength payload))|].
      + unfold REQMAX, MAX_INPUT in *; lia.
      + apply HISTOK_amb0. rewrite length_map. lia.
      + intros p _. apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. exists (Some (p, zlength payload)), (v - zlength payload - QOV). cbn.
        split; [reflexivity|]. split; [lia| exact HJ].
      + intros RNG A s mo HJ. split; [exact HJ| unfold RUN_COST in Hv; lia]. }
  intros a. apply TSM_exI. intros ob. apply TSM_exI. intros w. apply TSM_pure'. intros ->. apply TSM_pure'. intros Hw.
  cbn [option_map].
  eapply TSM_bind'; [apply (run_calls_ok NC (olist ob ++ X)); [destruct ob as [[p n]|]; cbn [olist app length]; lia| unfold RUN_COST in Hv; nia]|]. intros rcd.
  eapply TSM_seq with (P1 := JX X (w - Z.of_nat NC * FUZZ_COST)).
  { destruct ob as [[p n]|]; cbn [olist app option_map fst]; [apply Uf| apply TSM_ret'; apply JX_acct]. }
  intros _. apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. eapply JX_credit; [| exact HJ].
  pose proof (JX_nonneg _ _ _ _ _ _ HJ). unfold RUN_COST, MAX_INPUT in *. nia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Notation cTSM := (cTSM NMAX (St:=St)).
Variables pre opt : list Z.
Hypothesis Hclient : (length (pre ++ opt) <= NREQ)%nat /\ Forall (fun n => 0 <= n <= RMAX) (pre ++ opt).
Local Notation fuzz1c := (HarnessC.fuzz_one malloc free pre opt).

Lemma fuzz_without_ok : forall T X v, TSM (JX (T ++ X) v) (HarnessC.fuzz_without free (names T)) (fun _ => JX X v).
Proof. intros T X v. unfold HarnessC.fuzz_without. eapply TSM_seq; [apply free_all_ok|]. intros _. apply TSM_ret'. apply JX_acct. Qed.

Lemma fuzz_with_ok : forall ns T X v, Forall (fun n => 0 <= n <= RMAX) ns -> (length T + length X + length ns <= 4)%nat ->
  Z.of_nat (length ns) * (RMAX + QOV) <= v ->
  TSM (JX (T ++ X) v) (HarnessC.fuzz_with malloc free ns (names T)) (fun _ => JX X (v - Z.of_nat (length ns) * (RMAX + QOV))).
Proof.
  intros ns T X v Hns HL Hv. unfold HarnessC.fuzz_with.
  eapply TSM_bind'; [apply (alloc_all_ok ns T X v Hns HL Hv)|].
  intros ps. apply TSM_exI. intros T'. apply TSM_pure'. intros ->. apply TSM_pure'. intros _.
  eapply TSM_seq; [apply free_all_ok|]. intros _. apply TSM_ret'. apply JX_acct.
Qed.

Lemma fuzz_oneC_ok : forall X v data, (length X <= 2)%nat -> FUZZ_COST <= v ->
  cTSM (JX X v) (fuzz1c data) (fun _ => JX X (v - FUZZ_COST)).
Proof.
  intros X v data HLX Hv. unfold HarnessC.fuzz_one. destruct Hclient as [CL CS]. rewrite length_app in CL.
  apply Forall_app in CS. destruct CS as [CSp CSo].
  assert (K0 : 0 <= RMAX + QOV) by (clear - HQOV HRMAX; lia).
  assert (K1 : Z.of_nat (length pre) * (RMAX + QOV) + Z.of_nat (length opt) * (RMAX + QOV) <= FUZZ_COST) by (unfold FUZZ_COST; clear - CL K0; nia).
  assert (K2 : 0 <= Z.of_nat (length opt) * (RMAX + QOV)) by (clear - K0; nia).
  assert (K3 : 0 <= Z.of_nat (length pre) * (RMAX + QOV)) by (clear - K0; nia).
  eapply cTSM_bind'; [apply cTSM_lift; apply (alloc_all_ok pre [] X v CSp); [cbn [length]; lia| lia]|].
  intros ps. apply cTSM_exI. intros T'. apply cTSM_pure'. intros ->. apply cTSM_pure'. intros HT'. cbn [length] in HT'.
  assert (DONE : forall w, v - FUZZ_COST <= w -> TSM (JX (T' ++ X) w) (HarnessC.fuzz_without free (names T')) (fun _ => JX X (v - FUZZ_COST))).
  { intros w Hw. eapply TSM_post; [apply fuzz_without_ok|]. cbv beta. intros x RNG A s mo _ HJ.
    eapply JX_credit; [| exact HJ]. pose proof (JX_nonneg _ _ _ _ _ _ HJ). pose proof FUZZ_COST_nonneg. lia. }
  apply cTSM_if'; intros _.
  - apply cTSM_lift. apply DONE. lia.
  - apply cTSM_choice.
    + apply cTSM_lift. eapply TSM_post; [apply (fuzz_with_ok opt T' X _ CSo); [lia| lia]|].
      cbv beta. intros x RNG A s mo _ HJ. eapply JX_credit; [| exact HJ]. pose proof (JX_nonneg _ _ _ _ _ _ HJ). lia.
    + apply cTSM_lift. apply DONE. lia.
Qed.

Lemma run_callsC_ok : forall n X payload rcd v, (length X <= 2)%nat -> Z.of_nat n * FUZZ_COST <= v ->
  cTSM (JX X v) (AdapterC.run_calls fuzz1c emit n payload rcd) (fun _ => JX X (v - Z.of_nat n * FUZZ_COST)).
Proof.
  pose proof FUZZ_COST_nonneg as F0.
  induction n as [|n IH]; intros X payload rcd v HLX Hv; cbn [AdapterC.run_calls].
  - apply cTSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. eapply JX_credit; [| exact HJ].
    pose proof (JX_nonneg _ _ _ _ _ _ HJ). lia.
  - eapply cTSM_bind'; [apply fuzz_oneC_ok; [exact HLX| nia]|]. intros rcd'.
    eapply cTSM_seq; [apply cTSM_lift; apply Uemit|]. intros _.
    eapply cTSM_post; [apply IH; [exact HLX| nia]|].
    cbv beta. intros x RNG A s mo _ HJ. eapply JX_credit; [| exact HJ]. pose proof (JX_nonneg _ _ _ _ _ _ HJ). nia.
Qed.

Theorem target_runC_ok : forall X cfg payload v, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> RUN_COST <= v ->
  cTSM (JX X v) (AdapterC.target_run malloc free fuzz1c emit cfg payload) (fun _ => JX X (v - RUN_COST)).
Proof.
  intros X cfg payload v HLX Hp Hv. unfold AdapterC.target_run.
  assert (Hpl : 0 <= zlength payload) by (unfold zlength; lia).
  pose proof FUZZ_COST_nonneg as F0.
  assert (HN : 0 <= Z.of_nat (Z.to_nat (1 + Z.land cfg 3)) <= 4).
  { assert (HL3 : Z.land cfg 3 = cfg mod 4) by (apply (Z.land_ones cfg 2); lia).
    pose proof (Z.mod_pos_bound cfg 4 ltac:(lia)). lia. }
  set (NC := Z.to_nat (1 + Z.land cfg 3)) in *.
  eapply cTSM_bind' with (Q1 := fun a RNG A s mo => exists ob w, a = Some (option_map fst ob) /\ v - (MAX_INPUT + QOV) <= w
                                                 /\ JX (olist ob ++ X) w RNG A s mo).
  { apply cTSM_lift. unfold AdapterC.payload_copy. apply TSM_if'; intros C.
    - apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. exists None, v. cbn. split; [reflexivity|]. split; [unfold MAX_INPUT; lia| exact HJ].
    - apply Z.eqb_neq in C. eapply TSM_pre; [apply (malloc_seq X v (zlength payload))|].
      + unfold REQMAX, MAX_INPUT in *; lia.
      + apply HISTOK_amb0. rewrite length_map. lia.
      + intros p _. apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. exists (Some (p, zlength payload)), (v - zlength payload - QOV). cbn.
        split; [reflexivity|]. split; [lia| exact HJ].
      + intros RNG A s mo HJ. split; [exact HJ| unfold RUN_COST in Hv; lia]. }
  intros a. apply cTSM_exI. intros ob. apply cTSM_exI. intros w. apply cTSM_pure'. intros ->. apply cTSM_pure'. intros Hw.
  cbn [option_map].
  eapply cTSM_bind'; [apply (run_callsC_ok NC (olist ob ++ X)); [destruct ob as [[p n]|]; cbn [olist app length]; lia| unfold RUN_COST in Hv; nia]|]. intros rcd.
  eapply cTSM_seq with (P1 := JX X (w - Z.of_nat NC * FUZZ_COST)).
  { apply cTSM_lift. destruct ob as [[p n]|]; cbn [olist app option_map fst]; [apply Uf| apply TSM_ret'; apply JX_acct]. }
  intros _. apply cTSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. eapply JX_credit; [| exact HJ].
  pose proof (JX_nonneg _ _ _ _ _ _ HJ). unfold RUN_COST, MAX_INPUT in *. nia.
Qed.
End Target.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Driver.
Variable io_ : IOStyle St.
Variables (malloc : Z -> M St (option P)) (free : P -> M St unit) (read_stage : Z).   (* [comment removed for export] *)
Variables (alloc_init : Z -> M St unit) (run : Z -> list Z -> M St Z) (alloc_count : M St Z).

Hypothesis Um : forall Y v n, 0 <= n <= REQMAX -> HISTOK (n :: sizes Y) ->
  TSM (fun RNG A s mo => JX Y v RNG A s mo /\ n + QOV <= v) (malloc n)
      (fun r RNG A s mo => exists q, r = Some q /\ JX ((q, n) :: Y) (v - n - QOV) RNG A s mo /\ n < 2^63).
Hypothesis Uf : forall Y v p n, TSM (JX ((p, n) :: Y) v) (free p) (fun _ => JX Y v).
Hypothesis Udiag : forall Y v d, TSJ Y v (io_diag io_ d).
Hypothesis Uinit : forall Y v bm, TSJ Y v (alloc_init bm).
Hypothesis Ucount : forall Y v, TSJ Y v alloc_count.
Hypothesis Urun : forall X cfg payload v, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> RUN_COST <= v ->
  TSM (JX X v) (run cfg payload) (fun _ => JX X (v - RUN_COST)).
Hypothesis Uioexit : forall Y v, TSJ Y v (io_exit io_).
(* [comment removed for export] *)
Hypothesis HRMAX : 0 <= RMAX <= REQMAX.

(* [comment removed for export] *)
Definition rd_pot (cap : Z) : Z := 2^27 - 2 * cap.
Definition READ_COST : Z := 2^27 + QOV * 11.          (* [comment removed for export] *)
Definition MAIN_COST : Z := READ_COST + RUN_COST.

(* [comment removed for export] *)
Definition rd_rel (vb : Z) (st : @rd_st P) : preT := fun RNG A s mo =>
  exists v, JX [(rd_buf st, rd_cap st)] v RNG A s mo /\ zlength (rd_content st) <= rd_cap st
            /\ (exists k, (k <= 10)%nat /\ rd_cap st = 65536 * 2 ^ Z.of_nat k /\ vb + rd_pot (rd_cap st) + QOV * (10 - Z.of_nat k) <= v).

Definition QR (vb : Z) (r : @rd_result P) : preT :=
  match r with
  | RdExit => fun RNG A s mo => exists X' v', JX X' v' RNG A s mo
  | RdDone b c => fun RNG A s mo => (exists cap, JX [(b, cap)] vb RNG A s mo) /\ zlength c <= MAX_INPUT
  end.

Lemma read_loop_body_ok : forall fd path vb st, 0 <= vb ->
  TSM (rd_rel vb st) (read_loop_body io_ malloc free read_stage fd path st)
      (fun r => match r with inl st' => rd_rel vb st' | inr res => QR vb res end).
Proof.
  intros fd path vb st Hvb. unfold read_loop_body.
  apply TSM_exI. intros v. apply TSM_pointwise. intros RNG0 A0 s0 mo0 (Ho0 & Hlen & (k & Hk & Hcap & Hpot)).
  pose proof (pow2_le_1024' k Hk) as Hp2. unfold rd_pot in Hpot.
  eapply TSM_bind' with
    (Q1 := fun g => match g with
                    | None => fun RNG A s mo => exists X' v', JX X' v' RNG A s mo
                    | Some st1 => fun RNG A s mo => rd_rel vb st1 RNG A s mo /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1
                    end).
  { destruct (Z.eqb_spec (zlength (rd_content st)) (rd_cap st)) as [Heq|Hne].
    - destruct (Z.leb_spec MAX_INPUT (rd_cap st)) as [Hbig|Hsmall].
      + eapply TSM_seq; [eapply TSM_pre; [apply (Udiag [(rd_buf st, rd_cap st)] v)| intros ? ? ? ? (-> & -> & -> & ->); exact Ho0]|].
        intros _. apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. exists [(rd_buf st, rd_cap st)], v. exact HJ.
      + assert (Hk9 : (k <= 9)%nat).
        { destruct (Nat.le_gt_cases k 9) as [|Hgt]; [assumption|]. exfalso. assert (k = 10%nat) as -> by lia. unfold MAX_INPUT in Hsmall. cbn in Hcap. lia. }
        assert (Hp9 : 2 ^ Z.of_nat k <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia).
        eapply TSM_pre; [apply (malloc_seq malloc Um [(rd_buf st, rd_cap st)] v (rd_cap st * 2))|].
        { unfold REQMAX, MAX_INPUT in *; lia. }
        { apply HISTOK_amb0. cbn; lia. }
        2:{ intros ? ? ? ? (-> & -> & -> & ->). split; [exact Ho0| nia]. }
        intros nb _. cbn beta iota.
        eapply TSM_seq.
        { eapply TSM_pre; [apply (Uf [(nb, rd_cap st * 2)] (v - rd_cap st * 2 - QOV) (rd_buf st) (rd_cap st))|]. intros ? ? ? ? Ho. eapply JX_perm; [apply perm_swap| exact Ho]. }
        intros _. apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. cbn. unfold rd_rel. cbn.
        split; [| split; [reflexivity| lia]].
        exists (v - rd_cap st * 2 - QOV). splits; auto; try lia.
        exists (S k). split; [lia|]. split; [rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia|]. unfold rd_pot. rewrite Nat2Z.inj_succ. lia.
    - apply TSM_ret. intros ? ? ? ? (-> & -> & -> & ->). split; [eapply JX_acct; exact Ho0|]. unfold rd_rel. splits; auto; try lia.
      exists v. splits; auto; try (unfold rd_pot; lia). exists k. unfold rd_pot. auto. }
  intros [st1|]; cbn beta iota.
  2:{ apply TSM_ret. intros RNG A s mo H. split; [destruct H as (X' & v' & HJ); eapply JX_acct; exact HJ| exact H]. }
  apply TSM_pure_r. intros [Hct Hlt]. rewrite Hct.
  apply TSM_pointwise. intros RNG1 A1 s1' mo1 (w & Ho & Hlen' & (k' & Hk' & Hcap' & Hpot')).
  pose proof (pow2_le_1024' k' Hk') as Hp2'.
  set (want0 := rd_cap st1 - zlength (rd_content st)).
  set (want := if 65536 <? want0 then 65536 else want0).
  assert (Hwant : 0 <= want <= want0 /\ want < 2^64). { subst want want0. destruct (Z.ltb_spec 65536 (rd_cap st1 - zlength (rd_content st))); lia. }
  eapply TSM_bind'.
  { eapply TSM_pre; [apply (read_ok [(rd_buf st1, rd_cap st1)] w fd _ want); lia|].
    intros ? ? ? ? (-> & -> & -> & ->). exact Ho. }
  intros [e|bs]; cbn beta iota.
  - apply TSM_pure_r0. eapply TSM_seq; [apply Udiag|]. intros _. apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. exists [(rd_buf st1, rd_cap st1)], w. exact HJ.
  - destruct (length bs =? 0)%nat eqn:C.
    + apply TSM_ret. intros RNG A s mo [Ho' _]. split; [eapply JX_acct; exact Ho'|]. cbn. split; [exists (rd_cap st1); eapply JX_credit; [| exact Ho']; unfold rd_pot in Hpot'; nia|].
      unfold MAX_INPUT in *. lia.
    + apply TSM_ret. intros RNG A s mo [Ho' Hbs]. split; [eapply JX_acct; exact Ho'|]. unfold rd_rel. cbn. exists w. rewrite zlength_app', zlength_u8s', ?Hct. splits; auto; [lia| exists k'; auto].
Qed.

Lemma read_all_ok : forall path v, READ_COST <= v ->
  TSM (JX [] v) (read_all io_ malloc free read_stage path) (QR (v - READ_COST)).
Proof.
  intros path v Hv. unfold read_all.
  assert (Hvb : 0 <= v - READ_COST).
  { (* [comment removed for export] *) unfold READ_COST in *. lia. }
  eapply TSM_bind'; [apply open_ok|]. intros [e|fd]; cbn beta iota.
  - eapply TSM_seq; [apply Udiag|]. intros _. apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. exists [], v. exact HJ.
  - eapply TSM_pre; [apply (malloc_seq malloc Um [] v 65536)|].
    { unfold REQMAX; lia. } { apply HISTOK_amb0; cbn; lia. }
    2:{ intros RNG A s mo HJ. split; [exact HJ| unfold READ_COST in Hv; lia]. }
    intros buf _. cbn beta iota.
    eapply TSM_bind'.
    + eapply TSM_pre.
      * apply (TSM_loop _ (rd_rel (v - READ_COST)) (QR (v - READ_COST))).
        -- intros st. eapply TSM_post; [apply read_loop_body_ok; exact Hvb|]. intros [st'|r] RNG A s mo _ H; exact H.
        -- intros st RNG A s mo (w & HJ & _). eapply JX_acct; exact HJ.
      * intros RNG A s mo HJ. unfold rd_rel. cbn. exists (v - 65536 - QOV). split; [exact HJ|]. split; [unfold zlength; cbn; lia|].
        exists 0%nat. split; [lia|]. split; [reflexivity|]. unfold rd_pot, READ_COST. cbn. lia.
    + intros [|buf' c]; cbn beta iota.
      * apply TSM_ret. intros RNG A s mo H. split; [destruct H as (X' & v' & HJ); eapply JX_acct; exact HJ| exact H].
      * apply TSM_pure_r. intros Hlen. apply TSM_exI. intros cap.
        eapply TSM_seq; [apply close_ok|]. intros _. apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. cbn. split; [exists cap; exact HJ| exact Hlen].
Qed.

Lemma main_model_ok : forall argv v, MAIN_COST <= v ->
  TSM (JX [] v) (main_model io_ malloc free read_stage alloc_init run alloc_count argv)
      (fun _ RNG A s mo => exists X' v', JX X' v' RNG A s mo).
Proof.
  intros argv v Hv. unfold main_model.
  assert (DONE : forall Y w (z : Z), TSM (JX Y w) (mret z) (fun _ RNG A s mo => exists X' v', JX X' v' RNG A s mo)).
  { intros Y w z. apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. exists Y, w. exact HJ. }
  apply TSM_if'; intros C.
  { eapply TSM_seq; [apply Udiag|]. intros _. apply DONE. }
  eapply TSM_bind'; [apply read_all_ok; pose proof (RUN_COST_nonneg HRMAX) as R0; unfold MAIN_COST in *; lia|]. intros [|buf c]; cbn beta iota.
  { apply TSM_ret. intros RNG A s mo H. split; [destruct H as (X' & v' & HJ); eapply JX_acct; exact HJ| exact H]. }
  apply TSM_pure_r. intros Hlen. apply TSM_exI. intros cap.
  apply TSM_if'; intros C1.
  { eapply TSM_seq; [apply Udiag|]. intros _. eapply TSM_seq; [apply Uf|]. intros _. apply DONE. }
  apply TSM_if'; intros C2.
  { eapply TSM_seq; [apply Udiag|]. intros _. eapply TSM_seq; [apply Uf|]. intros _. apply DONE. }
  eapply TSM_seq; [apply Uinit|]. intros _.
  eapply TSM_bind'; [apply (Urun [(buf, cap)]); [cbn; lia| | unfold MAIN_COST in Hv; lia]|].
  { etransitivity; [| exact Hlen]. unfold zlength. rewrite length_skipn. lia. }
  intros status.
  eapply TSM_bind' with (Q1 := fun _ => JX [(buf, cap)] (v - READ_COST - RUN_COST)).
  { destruct (Z.testbit _ 15).
    - eapply TSM_seq; [apply Ucount|]. intros n. apply TSM_ret'. apply JX_acct.
    - apply TSM_ret'. apply JX_acct. }
  intros status'. eapply TSM_seq; [apply Uf|]. intros _. apply DONE.
Qed.

Lemma exit_model_ok : forall code (Q : postM Empty_set),
  TSM (fun RNG A s mo => exists X v, JX X v RNG A s mo) (exit_model io_ code) Q.
Proof.
  intros code Q. unfold exit_model. apply TSM_exI. intros X. apply TSM_exI. intros v.
  eapply TSM_seq; [apply Uioexit|]. intros _. apply exit_node_ok.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Notation cTSM := (cTSM NMAX (St:=St)).
Variable runc : Z -> list Z -> MC St Z.
Hypothesis UrunC : forall X cfg payload v, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> RUN_COST <= v ->
  cTSM (JX X v) (runc cfg payload) (fun _ => JX X (v - RUN_COST)).

Lemma main_modelC_ok : forall argv v, MAIN_COST <= v ->
  cTSM (JX [] v) (DriverC.main_model io_ malloc free read_stage alloc_init runc alloc_count argv)
       (fun _ RNG A s mo => exists X' v', JX X' v' RNG A s mo).
Proof.
  intros argv v Hv. unfold DriverC.main_model.
  assert (DONE : forall Y w (z : Z), TSM (JX Y w) (mret z) (fun _ RNG A s mo => exists X' v', JX X' v' RNG A s mo)).
  { intros Y w z. apply TSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. exists Y, w. exact HJ. }
  apply cTSM_if'; intros C.
  { apply cTSM_lift. eapply TSM_seq; [apply Udiag|]. intros _. apply DONE. }
  eapply cTSM_bind'; [apply cTSM_lift; apply read_all_ok; pose proof (RUN_COST_nonneg HRMAX) as R0; unfold MAIN_COST in *; lia|]. intros [|buf c]; cbn beta iota.
  { apply cTSM_ret. intros RNG A s mo H. split; [destruct H as (X' & v' & HJ); eapply JX_acct; exact HJ| exact H]. }
  apply cTSM_pure_r. intros Hlen. apply cTSM_exI. intros cap.
  apply cTSM_if'; intros C1.
  { apply cTSM_lift. eapply TSM_seq; [apply Udiag|]. intros _. eapply TSM_seq; [apply Uf|]. intros _. apply DONE. }
  apply cTSM_if'; intros C2.
  { apply cTSM_lift. eapply TSM_seq; [apply Udiag|]. intros _. eapply TSM_seq; [apply Uf|]. intros _. apply DONE. }
  eapply cTSM_seq; [apply cTSM_lift; apply Uinit|]. intros _.
  eapply cTSM_bind'; [apply (UrunC [(buf, cap)]); [cbn; lia| | unfold MAIN_COST in Hv; lia]|].
  { etransitivity; [| exact Hlen]. unfold zlength. rewrite length_skipn. lia. }
  intros status.
  eapply cTSM_bind' with (Q1 := fun _ => JX [(buf, cap)] (v - READ_COST - RUN_COST)).
  { apply cTSM_lift. destruct (Z.testbit _ 15).
    - eapply TSM_seq; [apply Ucount|]. intros n. apply TSM_ret'. apply JX_acct.
    - apply TSM_ret'. apply JX_acct. }
  intros status'. eapply cTSM_seq; [apply cTSM_lift; apply Uf|]. intros _.
  apply cTSM_ret. intros RNG A s mo HJ. split; [eapply JX_acct; exact HJ|]. eexists _, _. exact HJ.
Qed.

Theorem main_exitC_ok : forall argv v (Q : postM Empty_set), MAIN_COST <= v ->
  cTSM (JX [] v) (cmbind (DriverC.main_model io_ malloc free read_stage alloc_init runc alloc_count argv) (fun code => DriverC.exit_model io_ code)) Q.
Proof.
  intros argv v Q Hv. eapply cTSM_bind'; [apply main_modelC_ok; exact Hv|]. intros c.
  unfold DriverC.exit_model. apply cTSM_lift. apply exit_model_ok.
Qed.

(* [comment removed for export] *)
Theorem main_exit_ok : forall argv v (Q : postM Empty_set), MAIN_COST <= v ->
  TSM (JX [] v) (code <- main_model io_ malloc free read_stage alloc_init run alloc_count argv ;; exit_model io_ code) Q.
Proof.
  intros argv v Q Hv. eapply TSM_bind'; [apply main_model_ok; exact Hv|]. intros c. apply exit_model_ok.
Qed.
End Driver.
End Prog.
End CANSEC1.
