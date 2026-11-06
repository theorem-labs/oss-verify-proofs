(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxZZ AxLin AxVal AxBytes AxMem AxState AxAcc AxMat AxAmo AxStep AxFetchFast AxDecFast AxDecInt AxFetchFast2.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition ic_key (pc : w64) : int := (wl pc >> 2)%uint63.

Section Fetch.
Variable segs : list Segment.
Variable M : Type.
Variable LIM : Z.

(* [comment removed for export] *)
Definition afetch (ic : itrie icent) (pc : w64) : option (icent * itrie icent) :=
  if negb (pc_ok pc) then None else
  match iget ic_depth ic (ic_key pc) with
  | Some e => Some (e, ic)
  | None =>
      match fetch_fast2 segs pc with   (* [comment removed for export] *)
      | None => None
      | Some w =>
          if is_ecall_fast w then Some (ICEcall w, iset ic_depth ic (ic_key pc) (ICEcall w))
          else match fdecode w with
               | Some (i, isz) => if isz =? 4 then Some (ICInstr w i (dec_fast i), iset ic_depth ic (ic_key pc) (ICInstr w i (dec_fast i))) else None   (* [comment removed for export] *)
               | None => None
               end
      end
  end.

Definition astep (ic : itrie icent) (A : astate M) : itrie icent * ares M :=
  match afetch ic (a_pc A) with
  | Some (ICEcall _, ic') => (ic', AEcall A)
  | Some (ICInstr _ _ d, ic') => (ic', match astep_d segs M LIM A d with AEcall _ => AStuck 99 A | r => r end)
  | None => (ic, AStuck 1 A)
  end.

(* [comment removed for export] *)
Definition nomem_at (ic : itrie icent) (A : astate M) : bool :=
  match afetch ic (a_pc A) with
  | Some (ICInstr _ _ d, _) => nomem d
  | _ => false
  end.

Lemma astep_nomem (ic ic' : itrie icent) (A A' : astate M) :
  nomem_at ic A = true -> astep ic A = (ic', ANext A') -> a_mem A' = a_mem A /\ a_model A' = a_model A.
Proof.
  unfold nomem_at, astep. destruct (afetch ic (a_pc A)) as [[[w|w i d] ic1]|]; try discriminate.
  intros Hn H. assert (E : (match astep_d segs M LIM A d with AEcall _ => AStuck 99 A | r => r end) = ANext A') by (injection H as _ H; exact H).
  destruct (astep_d segs M LIM A d) as [B| | | |] eqn:Ed; try discriminate E. injection E as <-.
  exact (astep_d_nomem segs M LIM A B d Hn Ed).
Qed.

Lemma astep_fork_mem (ic ic' : itrie icent) (A : astate M) (l : list (astate M)) :
  astep ic A = (ic', AFork l) -> forall C, In C l -> a_mem C = a_mem A /\ a_model C = a_model A.
Proof.
  unfold astep. destruct (afetch ic (a_pc A)) as [[[w|w i d] ic1]|]; try discriminate.
  intros H. assert (E : (match astep_d segs M LIM A d with AEcall _ => AStuck 99 A | r => r end) = AFork l) by (injection H as _ H; exact H).
  destruct (astep_d segs M LIM A d) as [B|l0| | |] eqn:Ed; try discriminate E. injection E as <-.
  exact (astep_d_fork_mem segs M LIM A d l0 Ed).
Qed.

End Fetch.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FetchSound.
Variable segs : list Segment.

Lemma ic_key_pc (pc : w64) : wZ pc mod 4 = 0 -> wZ pc < 2 ^ 26 -> 4 * to_Z (ic_key pc) = wZ pc /\ to_Z (ic_key pc) < 2 ^ 24.
Proof.
  intros H1 H2. unfold ic_key. rewrite lsr_spec. change (to_Z 2%uint63) with 2. change (2 ^ 2) with 4.
  destruct pc as [h l]. unfold wZ in *. cbn [wh wl] in *. pose proof (to_Z_bounded l). change wB with (2^63) in *.
  destruct h; [unfold two63 in *; lia|]. rewrite Z.add_0_l in *.
  pose proof (Z.div_mod (to_Z l) 4 ltac:(lia)). split; [lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma ICok_set (ic : itrie icent) (k0 : int) (e1 : icent) :
  ICok segs ic -> to_Z k0 < 2 ^ 24 -> icent_ok segs (4 * to_Z k0) e1 -> ICok segs (iset ic_depth ic k0 e1).
Proof.
  intros Hic Hk0 He1 k e2 Hkk Hg. rewrite iget_iset in Hg.
  pose proof (to_Z_bounded k) as Hkb2. pose proof (to_Z_bounded k0) as Hkb3.
  change (2 ^ Z.of_nat ic_depth) with 16777216 in Hkk, Hg. change (2 ^ 24) with 16777216 in Hk0.
  rewrite (Z.mod_small (to_Z k0)) in Hg by lia. rewrite (Z.mod_small (to_Z k)) in Hg by lia.
  destruct (Z.eqb_spec (to_Z k0) (to_Z k)) as [E|E].
  - injection Hg as <-. rewrite <- E. exact He1.
  - apply (Hic k e2); [change (2 ^ Z.of_nat ic_depth) with 16777216; exact Hkk | exact Hg].
Qed.

Lemma ICok_empty : ICok segs IEmpty.
Proof. intros k e _ H. rewrite iget_empty in H. discriminate. Qed.

Lemma some_pair_inj {X Y : Type} (a a' : X) (b b' : Y) : Some (a, b) = Some (a', b') -> a = a' /\ b = b'.
Proof. intros H. injection H. auto. Qed.

Lemma pair_inj {X Y : Type} (a a' : X) (b b' : Y) : (a, b) = (a', b') -> a = a' /\ b = b'.
Proof. intros H. injection H. auto. Qed.

Lemma afetch_nok (ic : itrie icent) (pc : w64) : pc_ok pc = false -> afetch segs ic pc = None.
Proof. intros Hp. unfold afetch. rewrite fetch_fast2_eq, Hp. reflexivity. Qed.

Lemma afetch_hit (ic : itrie icent) (pc : w64) (e0 : icent) :
  pc_ok pc = true -> iget ic_depth ic (ic_key pc) = Some e0 -> afetch segs ic pc = Some (e0, ic).
Proof. intros Hp Eg. unfold afetch. rewrite fetch_fast2_eq, Hp. cbn [negb]. rewrite Eg. reflexivity. Qed.

Lemma afetch_miss_ecall (ic : itrie icent) (pc : w64) (w : bv 32) :
  pc_ok pc = true -> iget ic_depth ic (ic_key pc) = None -> fetch_word segs (wbv pc) = Some w -> is_ecall w = true ->
  afetch segs ic pc = Some (ICEcall w, iset ic_depth ic (ic_key pc) (ICEcall w)).
Proof. intros Hp Eg Ef He. unfold afetch. rewrite fetch_fast2_eq, Hp. cbn [negb]. rewrite Eg, Ef, is_ecall_fast_eq, He. reflexivity. Qed.

Lemma afetch_miss_instr (ic : itrie icent) (pc : w64) (w : bv 32) (i : instr) :
  pc_ok pc = true -> iget ic_depth ic (ic_key pc) = None -> fetch_word segs (wbv pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (i, 4) ->
  afetch segs ic pc = Some (ICInstr w i (dec i), iset ic_depth ic (ic_key pc) (ICInstr w i (dec i))).
Proof. intros Hp Eg Ef He Ed. rewrite <- (dec_fast_eq i). unfold afetch. rewrite fetch_fast2_eq, Hp. cbn [negb]. rewrite Eg, Ef, is_ecall_fast_eq, He, fdecode_eq, Ed. reflexivity. Qed.

Lemma afetch_none_fetch (ic : itrie icent) (pc : w64) :
  pc_ok pc = true -> iget ic_depth ic (ic_key pc) = None -> fetch_word segs (wbv pc) = None -> afetch segs ic pc = None.
Proof. intros Hp Eg Ef. unfold afetch. rewrite fetch_fast2_eq, Hp. cbn [negb]. rewrite Eg, Ef. reflexivity. Qed.

Lemma afetch_none_dec (ic : itrie icent) (pc : w64) (w : bv 32) :
  pc_ok pc = true -> iget ic_depth ic (ic_key pc) = None -> fetch_word segs (wbv pc) = Some w -> is_ecall w = false ->
  decode_any w = None -> afetch segs ic pc = None.
Proof. intros Hp Eg Ef He Ed. unfold afetch. rewrite fetch_fast2_eq, Hp. cbn [negb]. rewrite Eg, Ef, is_ecall_fast_eq, He, fdecode_eq, Ed. reflexivity. Qed.

Lemma afetch_none_isz (ic : itrie icent) (pc : w64) (w : bv 32) (i : instr) (isz : Z) :
  pc_ok pc = true -> iget ic_depth ic (ic_key pc) = None -> fetch_word segs (wbv pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (i, isz) -> isz <> 4 -> afetch segs ic pc = None.
Proof. intros Hp Eg Ef He Ed Hi. unfold afetch. rewrite fetch_fast2_eq, Hp. cbn [negb]. rewrite Eg, Ef, is_ecall_fast_eq, He, fdecode_eq, Ed. destruct (Z.eqb_spec isz 4); [lia | reflexivity]. Qed.

Lemma afetch_cases (ic : itrie icent) (pc : w64) (e : icent) (ic' : itrie icent) :
  afetch segs ic pc = Some (e, ic') ->
  pc_ok pc = true /\
  ((iget ic_depth ic (ic_key pc) = Some e /\ ic' = ic)
  \/ (exists w, fetch_word segs (wbv pc) = Some w
      /\ ((is_ecall w = true /\ e = ICEcall w) \/ (exists i, is_ecall w = false /\ decode_any w = Some (i, 4) /\ e = ICInstr w i (dec i)))
      /\ ic' = iset ic_depth ic (ic_key pc) e)).
Proof.
  intros H. destruct (pc_ok pc) eqn:Hp; [|rewrite (afetch_nok ic pc Hp) in H; discriminate].
  split; [reflexivity|].
  destruct (iget ic_depth ic (ic_key pc)) as [e0|] eqn:Eg.
  - rewrite (afetch_hit ic pc e0 Hp Eg) in H. destruct (some_pair_inj _ _ _ _ H) as [<- <-]. left. split; reflexivity.
  - right. destruct (fetch_word segs (wbv pc)) as [w|] eqn:Ef.
    + exists w. split; [reflexivity|].
      destruct (is_ecall w) eqn:He.
      * rewrite (afetch_miss_ecall ic pc w Hp Eg Ef He) in H. destruct (some_pair_inj _ _ _ _ H) as [<- <-]. split; [left; split; reflexivity | reflexivity].
      * destruct (decode_any w) as [[i isz]|] eqn:Ed.
        -- destruct (Z.eqb_spec isz 4) as [->|Hne].
           ++ rewrite (afetch_miss_instr ic pc w i Hp Eg Ef He Ed) in H. destruct (some_pair_inj _ _ _ _ H) as [<- <-].
              split; [right; exists i; split; [reflexivity | split; reflexivity] | reflexivity].
           ++ rewrite (afetch_none_isz ic pc w i isz Hp Eg Ef He Ed Hne) in H. discriminate.
        -- rewrite (afetch_none_dec ic pc w Hp Eg Ef He Ed) in H. discriminate.
    + rewrite (afetch_none_fetch ic pc Hp Eg Ef) in H. discriminate.
Qed.

Lemma afetch_sound (ic ic' : itrie icent) (pc : w64) (e : icent) :
  ICok segs ic -> afetch segs ic pc = Some (e, ic') ->
  ICok segs ic' /\ icent_ok segs (wZ pc) e.
Proof.
  intros Hic H. destruct (afetch_cases ic pc e ic' H) as [Hp Hc].
  destruct (pc_ok_spec pc Hp) as [H1 H2].
  destruct (ic_key_pc pc H1 H2) as [Hk Hkb].
  destruct Hc as [[Eg ->]|[w [Ef [Hc ->]]]].
  - split; [exact Hic|]. rewrite <- Hk. exact (Hic _ _ Hkb Eg).
  - assert (Hok : icent_ok segs (wZ pc) e).
    { destruct Hc as [[He ->]|[i [He [Ed ->]]]].
      - split; [exact Ef | exact He].
      - split; [exact Ef | split; [exact He | split; [exact Ed | reflexivity]]]. }
    split; [|exact Hok]. apply ICok_set; [exact Hic | exact Hkb | rewrite Hk; exact Hok].
Qed.

End FetchSound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma node_instr_acc (ms ms' : machine_state) (model model' : Model) :
  m_halted model = None -> ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model').
Proof.
  intros Hh Hsvc Hst. split.
  - intros []. apply sstep_cfg_instr; assumption.
  - intros e st H. inversion H; subst;
      try (match goal with H1 : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H1; discriminate H1 end).
    + exists tt. match goal with H2 : mi_account_step _ _ _ = _ |- _ => rewrite Hst in H2; injection H2 as <- <- end.
      split; reflexivity.
    + match goal with H2 : mi_account_step _ _ _ = _ |- _ => rewrite Hst in H2; discriminate H2 end.
    + match goal with H2 : mi_account_step _ _ _ = _ |- _ => rewrite Hst in H2; discriminate H2 end.
Qed.

(* [comment removed for export] *)
Definition latched (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := Some (ms_reg ms 17);
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

Lemma acc_Ecall (ms : machine_state) (w : bv 32) :
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state (latched ms) []).
Proof.
  intros Hf He. unfold RiscvSemantics.step_accesses, ms_pc. rewrite Hf. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite He. reflexivity.
Qed.

Lemma node_ecall (ms : machine_state) (model : Model) (w : bv 32) :
  m_halted model = None -> ms_svc_pending ms = None ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true ->
  node_ok_cfg segs cfg (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg (latched ms) model).
Proof.
  intros Hh Hsvc Hf He. apply node_instr_acc; [exact Hh | exact Hsvc|].
  apply (account_none segs ms (latched ms) model). exact (acc_Ecall ms w Hf He).
Qed.

Variable M : Type.
Variable MR : valuation -> M -> Model -> Prop.
Variable LIM : Z.
Hypothesis MR_mat : forall ρ am m pages, MR ρ am m -> MR ρ am (with_vm_backing (m_vm_lazy m) pages m).
Hypothesis Hlow : segs_low segs.

Notation RR ρ := (R segs M (MR ρ) LIM ρ).

Lemma astep_cases (ic : itrie icent) (A : astate M) (ic' : itrie icent) (r : ares M) :
  astep segs M LIM ic A = (ic', r) ->
  (exists w i d, afetch segs ic (a_pc A) = Some (ICInstr w i d, ic')
     /\ r = match astep_d segs M LIM A d with AEcall _ => AStuck 99 A | r' => r' end)
  \/ (exists w, afetch segs ic (a_pc A) = Some (ICEcall w, ic') /\ r = AEcall A)
  \/ (afetch segs ic (a_pc A) = None /\ r = AStuck 1 A /\ ic' = ic).
Proof.
  intros H. unfold astep in H. destruct (afetch segs ic (a_pc A)) as [[[w|w i d] ic1]|] eqn:Ef.
  - right; left. destruct (pair_inj _ _ _ _ H) as [<- <-]. exists w. split; reflexivity.
  - left. destruct (pair_inj _ _ _ _ H) as [<- <-]. exists w, i, d. split; reflexivity.
  - right; right. destruct (pair_inj _ _ _ _ H) as [<- <-]. split; [reflexivity | split; reflexivity].
Qed.

Lemma astep_ic (ic : itrie icent) (A : astate M) : ICok segs ic -> ICok segs (fst (astep segs M LIM ic A)).
Proof.
  intros Hic. destruct (astep segs M LIM ic A) as [ic' r] eqn:E. cbn [fst].
  destruct (astep_cases ic A ic' r E) as [[w [i [d [Ef _]]]]|[[w [Ef _]]|[_ [_ ->]]]].
  - exact (proj1 (afetch_sound segs ic ic' _ _ Hic Ef)).
  - exact (proj1 (afetch_sound segs ic ic' _ _ Hic Ef)).
  - exact Hic.
Qed.

Lemma astep_instr_inv (ic ic' : itrie icent) (A : astate M) (w : bv 32) (i : instr) (d : dinstr) (ρ : valuation) (c : config) :
  ICok segs ic -> RR ρ A c -> afetch segs ic (a_pc A) = Some (ICInstr w i d, ic') ->
  fetch_word segs (ms_pc_val (cfg_ms c)) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4) /\ d = dec i.
Proof.
  intros Hic HR Ef. destruct (afetch_sound segs ic ic' _ _ Hic Ef) as [_ Hok].
  destruct Hok as [Hf [He [Hd ->]]]. rewrite (r_pc _ _ _ _ _ _ _ HR). split; [exact Hf | split; [exact He | split; [exact Hd | reflexivity]]].
Qed.

Theorem astep_next_node (ic ic' : itrie icent) (A A' : astate M) (ρ : valuation) (c : config) :
  ICok segs ic -> RR ρ A c -> astep segs M LIM ic A = (ic', ANext A') ->
  exists c', node_ok_cfg segs cfg c unit (fun _ => []) (fun _ => c') /\ RR ρ A' c'.
Proof.
  intros Hic HR H. destruct c as [ms model].
  destruct (astep_cases ic A ic' _ H) as [[w [i [d [Ef Er]]]]|[[w [Ef Er]]|[_ [Er _]]]]; [|discriminate|discriminate].
  destruct (astep_instr_inv ic ic' A w i d ρ _ Hic HR Ef) as [Hf [He [Hd ->]]].
  assert (Hn : astep_d segs M LIM A (dec i) = ANext A') by (destruct (astep_d segs M LIM A (dec i)); try discriminate; exact (eq_sym Er)).
  destruct (astep_d_next_sound segs M (MR ρ) LIM ρ (MR_mat ρ) Hlow A A' ms model w i HR Hf He Hd Hn) as [ms' [model' [Ea HR']]].
  exists (mkCfg ms' model'). split; [|exact HR'].
  apply node_instr_acc; [exact (r_halted _ _ _ _ _ _ _ HR) | exact (r_svc _ _ _ _ _ _ _ HR) | exact Ea].
Qed.

Theorem astep_fork_node (ic ic' : itrie icent) (A : astate M) (l : list (astate M)) (ρ : valuation) (c : config) :
  ICok segs ic -> RR ρ A c -> astep segs M LIM ic A = (ic', AFork l) ->
  exists c', node_ok_cfg segs cfg c unit (fun _ => []) (fun _ => c') /\ exists A', In A' l /\ RR ρ A' c'.
Proof.
  intros Hic HR H. destruct c as [ms model].
  destruct (astep_cases ic A ic' _ H) as [[w [i [d [Ef Er]]]]|[[w [Ef Er]]|[_ [Er _]]]]; [|discriminate|discriminate].
  destruct (astep_instr_inv ic ic' A w i d ρ _ Hic HR Ef) as [Hf [He [Hd ->]]].
  assert (Hn : astep_d segs M LIM A (dec i) = AFork l) by (destruct (astep_d segs M LIM A (dec i)); try discriminate; exact (eq_sym Er)).
  destruct (astep_d_fork_sound segs M (MR ρ) LIM ρ (MR_mat ρ) A l ms model w i HR Hf He Hd Hn) as [ms' [model' [Ea HR']]].
  exists (mkCfg ms' model'). split; [|exact HR'].
  apply node_instr_acc; [exact (r_halted _ _ _ _ _ _ _ HR) | exact (r_svc _ _ _ _ _ _ _ HR) | exact Ea].
Qed.

Theorem astep_ecall_inv (ic ic' : itrie icent) (A A' : astate M) (ρ : valuation) (c : config) :
  ICok segs ic -> RR ρ A c -> astep segs M LIM ic A = (ic', AEcall A') ->
  A' = A /\ exists w, fetch_word segs (ms_pc_val (cfg_ms c)) = Some w /\ is_ecall w = true.
Proof.
  intros Hic HR H.
  destruct (astep_cases ic A ic' _ H) as [[w [i [d [Ef Er]]]]|[[w [Ef Er]]|[_ [Er _]]]].
  - destruct (astep_d segs M LIM A d); discriminate.
  - injection Er as <-. split; [reflexivity|]. exists w.
    destruct (afetch_sound segs ic ic' _ _ Hic Ef) as [_ [Hf He]]. rewrite (r_pc _ _ _ _ _ _ _ HR). split; assumption.
  - discriminate.
Qed.

End Nodes.
