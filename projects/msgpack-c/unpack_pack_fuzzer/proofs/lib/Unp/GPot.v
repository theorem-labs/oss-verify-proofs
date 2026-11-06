(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Pot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Ops OpsTwin OpsKeep GLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem St Step Plan ValP PlanS HeapOp UO UG UOK.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GPot.

Definition POT_BASEw : w64 := wlit 6917529027641081856%uint63.
Definition POT_HIw : w64 := wlit 6917531226666434560%uint63.
Definition POT_TOPw : w64 := wlit 6917533425687592960%uint63.
Definition PRE_MAXw : w64 := wlit 6917530127153758208%uint63.
Definition FXMAXw : w64 := wlit 2199023255552%uint63.
Definition Q0w : w64 := wlit 134217728%uint63.
Definition D_ITEMw : w64 := wlit 40%uint63.
Definition D_RETw : w64 := wlit 48%uint63.
Definition D_PUSHw : w64 := wsub (wlit 88%uint63) POT_BASEw.
Definition D_BODYw : w64 := wsub (wlit 40%uint63) POT_BASEw.
Definition wtwo : w64 := wlit 2%uint63.
Definition CRED_MAXw : w64 := wlit 1099511627776%uint63.
Definition NEG_BASEw : w64 := wsub wzero POT_BASEw.

Lemma POT_BASEw_ok : w2Z POT_BASEw = POT_BASE. Proof. reflexivity. Qed.
Lemma POT_HIw_ok : w2Z POT_HIw = POT_BASE + 2 ^ 41 + 2 ^ 21. Proof. reflexivity. Qed.
Lemma POT_TOPw_ok : w2Z POT_TOPw = POT_BASE + POT_SPAN. Proof. reflexivity. Qed.
Lemma PRE_MAXw_ok : w2Z PRE_MAXw = POT_BASE + 2 ^ 40 + 2 ^ 20. Proof. reflexivity. Qed.
Lemma FXMAXw_ok : w2Z FXMAXw = 2 ^ 41. Proof. reflexivity. Qed.
Lemma Q0w_ok : w2Z Q0w = Pot.Pot.Q0. Proof. reflexivity. Qed.
Lemma D_PUSHw_ok : w2Z D_PUSHw = two64 - POT_BASE + 88. Proof. reflexivity. Qed.
Lemma D_BODYw_ok : w2Z D_BODYw = two64 - POT_BASE + 40. Proof. reflexivity. Qed.
Lemma CRED_MAXw_ok : w2Z CRED_MAXw = 2 ^ 40. Proof. reflexivity. Qed.
Lemma NEG_BASEw_ok : w2Z NEG_BASEw = two64 - POT_BASE. Proof. reflexivity. Qed.

Definition pwl (lo : sv) : sv * sv * sv := (lo, VL wzero, VL wzero).
Definition pw (z : int) : sv * sv * sv := pwl (VP z POT_BASEw).

Definition cred_route (fs : list fact) (aw lo : sv) : bool :=
  if wleu (snd (sv_bounds fs aw)) CRED_MAXw
  then match decide_ltu_t fs aw (sv_alu ALU_ADD lo (VL NEG_BASEw)) with Some false => true | _ => false end
  else false.

Definition lo_in (fs : list fact) (aw lo : sv) : bool :=
  let '(l, h) := sv_bounds fs lo in
  if wleu POT_BASEw l then (if wleu h POT_HIw then true else if cred_route fs aw lo then true
                            else match decide_ltu_t fs (VL POT_HIw) lo with Some false => true | _ => false end)
  else false.

Definition pot_q_c (fs : list fact) (aw : sv) (x : sv * sv * sv) : option sv :=
  match x with
  | (lo, VL len, VL kd) => if weqb len wzero then if weqb kd wzero then if lo_in fs aw lo then Some lo else None else None else None
  | _ => None
  end.

Definition not_pot (fs : list fact) (x : sv * sv * sv) : bool :=
  match x with
  | (lo, len, VL kd) =>
      if negb (weqb kd wzero) then true
      else if match len with VL l => negb (weqb l wzero) | _ => false end then true
      else let '(l, h) := sv_bounds fs lo in if wltu h POT_BASEw then true else wltu POT_TOPw l
  | _ => false
  end.

Fixpoint all_not_pot (fs : list fact) (ws : list (sv * sv * sv)) : bool :=
  match ws with [] => true | x :: ws' => if not_pot fs x then all_not_pot fs ws' else false end.
Fixpoint pot_scan_c (fs : list fact) (aw : sv) (ws : list (sv * sv * sv)) : option (option sv) :=
  match ws with
  | [] => Some None
  | x :: ws' => if not_pot fs x then pot_scan_c fs aw ws'
                else match pot_q_c fs aw x with
                     | Some lo => if all_not_pot fs ws' then Some (Some lo) else None
                     | None => None
                     end
  end.

Definition pot_set (sc : option sv) (lo' : sv) (ws : list (sv * sv * sv)) : list (sv * sv * sv) :=
  match sc with Some lo => map (fun x => if win3_eqb x (pwl lo) then pwl lo' else x) ws | None => ws end.

Definition lit_lo (sc : option sv) (d : w64) : sv := match sc with Some lo => sv_alu ALU_ADD lo (VL d) | None => VL wzero end.
Definition pot_lit (sc : option sv) (d : w64) (ws : list (sv * sv * sv)) : list (sv * sv * sv) := pot_set sc (lit_lo sc d) ws.

Definition pot_pre (fs : list fact) (aw : sv) (sc : option sv) : bool :=
  match sc with
  | Some lo => if wleu (snd (sv_bounds fs lo)) PRE_MAXw then true
               else match decide_ltu_t fs (VL PRE_MAXw) lo with Some false => true | _ => cred_route fs aw lo end
  | None => true
  end.
Definition pot_sym (sc : option sv) (z' : int) (ws : list (sv * sv * sv)) : list (sv * sv * sv) := pot_set sc (VP z' POT_BASEw) ws.
Definition pot_next (sc : option sv) (n : int) : int := match sc with Some _ => PrimInt63.add n 1%uint63 | None => n end.

Definition BIG_SZw : w64 := wlit 32761%uint63.
Definition BIG_PAYw : w64 := wlit 65524%uint63.
Definition big_sz (fs : list fact) (SZ : sv) : bool := match decide_ltu_t fs (VL BIG_SZw) SZ with Some true => true | _ => false end.
Definition pot_facts_push (fs : list fact) (sc : option sv) (z' : int) (SZ : sv) : list fact :=
  match sc with
  | Some lo => [FEq (VAlu ALU_ADD (VP z' wzero) (VAlu ALU_SLL SZ (VL wone))) (sv_alu ALU_ADD lo (VL D_PUSHw)); FRange z' wzero FXMAXw]
               ++ (if big_sz fs SZ then [FULe (VP z' BIG_PAYw) (sv_alu ALU_ADD lo (VL D_PUSHw))] else [])
  | None => []
  end.
Definition pot_facts_body (sc : option sv) (z' : int) (SZ : sv) : list fact :=
  match sc with
  | Some lo => [FEq (VP z' wzero) (VAlu ALU_ADD (sv_alu ALU_ADD lo (VL D_BODYw)) (VAlu ALU_SLL SZ (VL wtwo))); FRange z' wzero FXMAXw]
  | None => []
  end.

Definition pot_facts_init (z' : int) : list fact := [FEq (VP z' wzero) (VL Q0w); FRange z' wzero FXMAXw].

Definition pot_word (E : env) (sc : option sv) : Z := match sc with Some lo => bv_unsigned (den E lo) - POT_BASE | None => 0 end.

Section Sound.
Variable E : env.

Lemma pwl_den : forall lo, wden E (pwl lo) = Win (bv_unsigned (den E lo)) 0 K_STACK.
Proof. intros lo. unfold pwl, wden. rewrite !den_VL, wzero_ok. reflexivity. Qed.
Lemma pwl_kind : forall lo, w_kind (wden E (pwl lo)) = K_STACK.
Proof. intros lo. rewrite pwl_den. reflexivity. Qed.
Lemma pwl_len : forall lo, w_len (wden E (pwl lo)) = 0.
Proof. intros lo. rewrite pwl_den. reflexivity. Qed.

Lemma alu_add_u0 : forall a b : word, bv_unsigned (alu64 ALU_ADD a b) = (bv_unsigned a + bv_unsigned b) mod two64.
Proof. intros a b. cbn [alu64 alu]. rewrite bv_add_unsigned. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. Qed.
Lemma cred_route_sound : forall fs aw lo, facts_hold E fs -> cred_route fs aw lo = true -> POT_BASE <= bv_unsigned (den E lo) ->
  bv_unsigned (den E lo) <= POT_BASE + 2 ^ 40.
Proof.
  intros fs aw lo HF H LB. unfold cred_route in H. destruct (wleu (snd (sv_bounds fs aw)) CRED_MAXw) eqn:CM; [|discriminate].
  destruct (decide_ltu_t fs aw (sv_alu ALU_ADD lo (VL NEG_BASEw))) as [[|]|] eqn:D; try discriminate.
  pose proof (decide_ltu_t_sound E fs HF _ _ _ D) as LT. apply (proj1 (ltu_iff _ _ false)) in LT.
  rewrite den_sv_alu, alu_add_u0, den_VL, NEG_BASEw_ok in LT.
  pose proof (bv_unsigned_in_range _ (den E lo)) as R. rewrite bv_modulus_64 in R.
  replace (bv_unsigned (den E lo) + (two64 - POT_BASE)) with ((bv_unsigned (den E lo) - POT_BASE) + 1 * two64) in LT by lia.
  rewrite Z.mod_add in LT by (unfold two64; lia). rewrite Z.mod_small in LT by (unfold POT_BASE, two64 in *; lia).
  pose proof (sv_bounds_sound E fs HF aw) as B. destruct (sv_bounds fs aw) as [l h]. unfold inb in B. cbn [fst snd] in B, CM.
  rewrite wleu_w2Z in CM. apply Z.leb_le in CM. rewrite CRED_MAXw_ok in CM. lia.
Qed.
Lemma lo_in_sound : forall fs aw lo, facts_hold E fs -> lo_in fs aw lo = true -> POT_BASE <= bv_unsigned (den E lo) <= POT_BASE + 2 ^ 41 + 2 ^ 21.
Proof.
  intros fs aw lo HF H. unfold lo_in in H. pose proof (sv_bounds_sound E fs HF lo) as B. destruct (sv_bounds fs lo) as [l h] eqn:SB. unfold inb in B. cbn [fst snd] in B.
  destruct (wleu POT_BASEw l) eqn:H1; [|discriminate]. rewrite wleu_w2Z in H1. apply Z.leb_le in H1. rewrite POT_BASEw_ok in H1.
  destruct (wleu h POT_HIw) eqn:H2.
  - rewrite wleu_w2Z in H2. apply Z.leb_le in H2. rewrite POT_HIw_ok in H2. lia.
  - destruct (cred_route fs aw lo) eqn:CR.
    + pose proof (cred_route_sound fs aw lo HF CR ltac:(lia)) as C. lia.
    + destruct (decide_ltu_t fs (VL POT_HIw) lo) as [[|]|] eqn:D; try discriminate.
      pose proof (decide_ltu_t_sound E fs HF _ _ _ D) as LT. apply (proj1 (ltu_iff _ _ false)) in LT. rewrite den_VL, POT_HIw_ok in LT. lia.
Qed.
Lemma pot_q_c_sound : forall fs aw x lo, facts_hold E fs -> pot_q_c fs aw x = Some lo ->
  x = pwl lo /\ POT_BASE <= bv_unsigned (den E lo) <= POT_BASE + 2 ^ 41 + 2 ^ 21.
Proof.
  intros fs aw [[lo0 len] kd] lo HF H. unfold pot_q_c in H.
  destruct len as [l| | | | | | | | | |]; try discriminate. destruct kd as [k| | | | | | | | | |]; try discriminate.
  destruct (weqb l wzero) eqn:L0; [|discriminate]. destruct (weqb k wzero) eqn:K0; [|discriminate]. destruct (lo_in fs aw lo0) eqn:LI; [|discriminate].
  injection H as <-. apply (proj1 (weqb_ok _ _)) in L0. apply (proj1 (weqb_ok _ _)) in K0. subst l k.
  split; [reflexivity| exact (lo_in_sound fs aw lo0 HF LI)].
Qed.
Lemma not_pot_sound : forall fs x, facts_hold E fs -> not_pot fs x = true -> ~ pot_win (wden E x).
Proof.
  intros fs [[lo len] kd] HF H (K & L & B1 & B2). unfold not_pot in H. destruct kd as [k| | | | | | | | | |]; try discriminate.
  unfold wden in K, L, B1, B2. cbn [w_kind w_len w_lo] in K, L, B1, B2.
  destruct (negb (weqb k wzero)) eqn:NK.
  { apply negb_true_iff in NK. rewrite den_VL in K. unfold K_STACK in K. rewrite weqb_eqb in NK. rewrite K, wzero_ok in NK. discriminate. }
  destruct (match len with VL l => negb (weqb l wzero) | _ => false end) eqn:NL.
  { destruct len as [l| | | | | | | | | |]; try discriminate. apply negb_true_iff in NL. rewrite den_VL in L. rewrite weqb_eqb in NL. rewrite L, wzero_ok in NL. discriminate. }
  pose proof (sv_bounds_sound E fs HF lo) as B. destruct (sv_bounds fs lo) as [l h]. unfold inb in B. cbn [fst snd] in B.
  destruct (wltu h POT_BASEw) eqn:HB.
  - rewrite wltu_w2Z in HB. apply Z.ltb_lt in HB. rewrite POT_BASEw_ok in HB. lia.
  - rewrite wltu_w2Z in H. apply Z.ltb_lt in H. rewrite POT_TOPw_ok in H. lia.
Qed.

Lemma all_not_pot_In : forall fs ws, all_not_pot fs ws = true -> forall x, In x ws -> not_pot fs x = true.
Proof.
  induction ws as [|y ws IH]; intros H x Hx; [destruct Hx|]. cbn [all_not_pot] in H. destruct (not_pot fs y) eqn:N; [|discriminate].
  destruct Hx as [<-|Hx]; [exact N| exact (IH H x Hx)].
Qed.
Lemma pot_scan_c_none : forall fs aw ws, pot_scan_c fs aw ws = Some None -> forall x, In x ws -> not_pot fs x = true.
Proof.
  intros fs aw. induction ws as [|y ws IH]; intros H x Hx; [destruct Hx|]. cbn [pot_scan_c] in H.
  destruct (not_pot fs y) eqn:N.
  - destruct Hx as [<-|Hx]; [exact N| exact (IH H x Hx)].
  - destruct (pot_q_c fs aw y) as [lo|]; [destruct (all_not_pot fs ws); discriminate| discriminate].
Qed.
Lemma pot_scan_c_some : forall fs aw ws lo, pot_scan_c fs aw ws = Some (Some lo) ->
  exists y, In y ws /\ pot_q_c fs aw y = Some lo /\ forall x, In x ws -> x = y \/ not_pot fs x = true.
Proof.
  intros fs aw. induction ws as [|y ws IH]; intros lo H; [discriminate|]. cbn [pot_scan_c] in H.
  destruct (not_pot fs y) eqn:N.
  - destruct (IH lo H) as (z & Hz & PZ & REST). exists z. split; [right; exact Hz|]. split; [exact PZ|].
    intros x [<-|Hx]; [right; exact N| exact (REST x Hx)].
  - destruct (pot_q_c fs aw y) as [lo0|] eqn:PQ; [|discriminate]. destruct (all_not_pot fs ws) eqn:FA; [|discriminate]. injection H as <-.
    exists y. split; [left; reflexivity|]. split; [exact PQ|].
    intros x [<-|Hx]; [left; reflexivity| right; exact (all_not_pot_In fs ws FA x Hx)].
Qed.

Definition scan_ok (ws : list (sv * sv * sv)) (sc : option sv) : Prop :=
  match sc with
  | Some lo => In (pwl lo) ws /\ POT_BASE <= bv_unsigned (den E lo) <= POT_BASE + 2 ^ 41 + 2 ^ 21 /\ forall x, In x ws -> x = pwl lo \/ ~ pot_win (wden E x)
  | None => forall x, In x ws -> ~ pot_win (wden E x)
  end.
Lemma pot_scan_c_ok : forall fs aw ws sc, facts_hold E fs -> pot_scan_c fs aw ws = Some sc -> scan_ok ws sc.
Proof.
  intros fs aw ws [lo|] HF H; unfold scan_ok.
  - destruct (pot_scan_c_some fs aw ws lo H) as (y & Hy & PQ & REST). destruct (pot_q_c_sound fs aw y lo HF PQ) as [-> B].
    split; [exact Hy|]. split; [exact B|]. intros x Hx. destruct (REST x Hx) as [->|N]; [left; reflexivity| right; exact (not_pot_sound fs x HF N)].
  - intros x Hx. exact (not_pot_sound fs x HF (pot_scan_c_none fs aw ws H x Hx)).
Qed.
Lemma pwl_pot_win : forall lo, POT_BASE <= bv_unsigned (den E lo) <= POT_BASE + POT_SPAN -> pot_win (wden E (pwl lo)).
Proof. intros lo B. rewrite pwl_den. unfold pot_win. cbn [w_kind w_len w_lo]. split; [reflexivity|]. split; [reflexivity| exact B]. Qed.

Definition pot_scan (fs : list fact) (ws : list (sv * sv * sv)) : option (option sv) := pot_scan_c fs (VL wzero) ws.
Lemma pot_scan_ok : forall fs ws sc, facts_hold E fs -> pot_scan fs ws = Some sc -> scan_ok ws sc.
Proof. intros fs ws sc HF H. exact (pot_scan_c_ok fs (VL wzero) ws sc HF H). Qed.

Lemma scan_value : forall ws lo v, scan_ok ws (Some lo) -> pot_at (map (wden E) ws) v -> bv_unsigned (den E lo) = POT_BASE + v.
Proof.
  intros ws lo v (IN & B & _) PA. assert (PW : pot_win (wden E (pwl lo))) by (apply pwl_pot_win; unfold POT_SPAN; lia).
  pose proof (PA _ (in_map (wden E) _ _ IN) PW) as V. rewrite pwl_den in V. cbn [w_lo] in V. exact V.
Qed.
Lemma scan_word : forall ws sc v, scan_ok ws sc -> pot_at (map (wden E) ws) v -> match sc with Some _ => pot_word E sc = v | None => True end.
Proof. intros ws [lo|] v SC PA; [| exact I]. cbn [pot_word]. rewrite (scan_value ws lo v SC PA). lia. Qed.

Lemma pwl_pseudo : forall lo, POT_BASE <= bv_unsigned (den E lo) -> pseudo (wden E (pwl lo)).
Proof. intros lo B. rewrite pwl_den. unfold pseudo. cbn [w_kind w_lo]. split; [reflexivity|]. unfold AW_BAND, POT_BASE in *. lia. Qed.
Lemma pwl_wf : forall LB ceil lo, POT_BASE <= bv_unsigned (den E lo) -> ceil <= Mem.two62Z -> window_wf LB ceil (wden E (pwl lo)).
Proof.
  intros LB ceil lo B C. rewrite pwl_den. unfold window_wf. cbn [w_lo w_len w_kind].
  pose proof (bv_unsigned_in_range _ (den E lo)) as R. rewrite bv_modulus_64 in R. unfold POT_BASE, Mem.two62Z, two64 in *.
  split; [lia|]. split; [lia|]. split; [lia|]. left. split; [reflexivity| lia].
Qed.

End Sound.

Lemma pot_set_length : forall sc lo' ws, length (pot_set sc lo' ws) = length ws.
Proof. intros [lo|] lo' ws; cbn [pot_set]; [apply length_map| reflexivity]. Qed.
Lemma pot_lit_length : forall sc d ws, length (pot_lit sc d ws) = length ws.
Proof. intros sc d ws. apply pot_set_length. Qed.
Lemma pot_set_new : forall sc lo' ws x, In x (pot_set sc lo' ws) ->
  (In x ws /\ match sc with Some lo => x <> pwl lo | None => True end) \/ (exists lo, sc = Some lo /\ x = pwl lo').
Proof.
  intros [lo|] lo' ws x H; cbn [pot_set] in H; [| left; split; [exact H| exact I]].
  apply in_map_iff in H as (y & Hy & IN). destruct (win3_eqb y (pwl lo)) eqn:Q.
  - right. exists lo. split; [reflexivity| symmetry; exact Hy].
  - left. subst x. split; [exact IN|]. intros X. rewrite X, win3_eqb_refl in Q. discriminate.
Qed.
Lemma pot_set_old : forall sc lo' ws x, In x ws -> In x (pot_set sc lo' ws) \/ (exists lo, sc = Some lo /\ x = pwl lo).
Proof.
  intros [lo|] lo' ws x H; cbn [pot_set]; [| left; exact H].
  destruct (win3_eqb x (pwl lo)) eqn:Q; [right; exists lo; split; [reflexivity| exact (win3_eqb_eq _ _ Q)]| left].
  apply in_map_iff. exists x. rewrite Q. split; [reflexivity| exact H].
Qed.

Section Transparent.
Variable E : env.
Variables (sc : option sv) (lo' : sv) (ws : list (sv * sv * sv)).

Lemma pot_set_other : forall w, w_kind w <> K_STACK -> (In w (map (wden E) (pot_set sc lo' ws)) <-> In w (map (wden E) ws)).
Proof.
  intros w NK. split; intros H; apply in_map_iff in H as (x & <- & Hx).
  - destruct (pot_set_new sc lo' ws x Hx) as [[H0 _]|(lo & _ & ->)]; [apply in_map; exact H0| exfalso; exact (NK (pwl_kind E lo'))].
  - destruct (pot_set_old sc lo' ws x Hx) as [H0|(lo & _ & ->)]; [apply in_map; exact H0| exfalso; exact (NK (pwl_kind E lo))].
Qed.

Lemma in_ws_pot_set : forall a, in_ws (map (wden E) (pot_set sc lo' ws)) a <-> in_ws (map (wden E) ws) a.
Proof.
  intros a. rewrite !in_ws_map_iff. split.
  - intros (x & Hx & Ha). destruct (pot_set_new sc lo' ws x Hx) as [[H0 _]|(lo & _ & ->)]; [exists x; split; assumption|].
    exfalso. unfold in_iv, w_iv in Ha. cbn [fst snd] in Ha. rewrite pwl_len in Ha. lia.
  - intros (x & Hx & Ha). destruct (pot_set_old sc lo' ws x Hx) as [H0|(lo & _ & ->)]; [exists x; split; assumption|].
    exfalso. unfold in_iv, w_iv in Ha. cbn [fst snd] in Ha. rewrite pwl_len in Ha. lia.
Qed.

Lemma wins_ok_pot_set : forall md g, wins_ok md g (map (wden E) ws) -> wins_ok md g (map (wden E) (pot_set sc lo' ws)).
Proof.
  intros md g H. unfold wins_ok in *. apply Forall_forall. intros w Hw NK.
  exact (proj1 (Forall_forall _ _) H w (proj1 (pot_set_other w NK) Hw) NK).
Qed.
Lemma seal_ok_pot_set : forall cs, Seal.seal_ok (map (wden E) ws) cs -> Seal.seal_ok (map (wden E) (pot_set sc lo' ws)) cs.
Proof.
  intros cs H. apply (Seal.seal_ok_ws _ _ _ H). intros w Hw K. apply (proj1 (pot_set_other w ltac:(rewrite K; unfold Seal.K_TWIN, K_STACK; lia)) Hw).
Qed.

Hypothesis OLDB : match sc with Some lo => POT_BASE <= bv_unsigned (den E lo) | None => True end.
Hypothesis NEWB : match sc with Some _ => POT_BASE <= bv_unsigned (den E lo') | None => True end.

Lemma windows_wf_pot_set : forall LB ceil, ceil <= Mem.two62Z -> windows_wf (map (wden E) ws) LB ceil -> windows_wf (map (wden E) (pot_set sc lo' ws)) LB ceil.
Proof.
  intros LB ceil C H. unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
  destruct (pot_set_new sc lo' ws x Hx) as [[H0 _]|(lo & -> & ->)]; [exact (proj1 (Forall_forall _ _) H _ (in_map _ _ _ H0))|].
  exact (pwl_wf E LB ceil lo' NEWB C).
Qed.
Lemma wins_keep_pot_set : forall LB, wins_keep LB (map (wden E) ws) (map (wden E) (pot_set sc lo' ws)).
Proof.
  intros LB. apply wins_keep_intro.
  - intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
    destruct (pot_set_new sc lo' ws x Hx) as [[H0 _]|(lo & -> & ->)]; [left; apply in_map; exact H0| right].
    split; [exact (pseudo_untied _ (pwl_pseudo E lo' NEWB))|]. intros K. exfalso. rewrite pwl_kind in K. unfold K_STACK, K_BLOCK in K. lia.
  - intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
    destruct (pot_set_old sc lo' ws x Hx) as [H0|(lo & -> & ->)]; [left; apply in_map; exact H0| right].
    split; [exact (pseudo_untied _ (pwl_pseudo E lo OLDB))|].
    intros [K _]. exfalso. rewrite pwl_kind in K. unfold K_STACK, K_BLOCK in K. lia.
Qed.

End Transparent.

Lemma pot_at_set : forall E ws ws' sc lo' v',
  scan_ok E ws sc ->
  (forall x, In x ws' -> In x ws \/ w_kind (wden E x) <> K_STACK) ->
  (match sc with Some _ => bv_unsigned (den E lo') = POT_BASE + v' | None => True end) ->
  pot_at (map (wden E) (pot_set sc lo' ws')) v'.
Proof.
  intros E ws ws' sc lo' v' SC NEW VAL w Hw PW. apply in_map_iff in Hw as (x & <- & Hx).
  destruct (pot_set_new sc lo' ws' x Hx) as [[H0 NQ]|(lo & -> & ->)].
  - exfalso. destruct (NEW x H0) as [Hold|NK]; [| destruct PW as (K & _); exact (NK K)].
    destruct sc as [lo|]; unfold scan_ok in SC.
    + destruct SC as (_ & _ & REST). destruct (REST x Hold) as [->|N]; [exact (NQ eq_refl)| exact (N PW)].
    + exact (SC x Hold PW).
  - rewrite pwl_den. cbn [w_lo]. exact VAL.
Qed.

Lemma alu_add_u : forall a b : word, bv_unsigned (alu64 ALU_ADD a b) = (bv_unsigned a + bv_unsigned b) mod two64.
Proof. intros a b. cbn [alu64 alu]. rewrite bv_add_unsigned. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. Qed.
Lemma shamt_wone : to_Z (shamt6 wone) = 1. Proof. reflexivity. Qed.
Lemma shamt_wtwo : to_Z (shamt6 wtwo) = 2. Proof. reflexivity. Qed.
Lemma alu_sll1_u : forall E x, bv_unsigned (den E (VAlu ALU_SLL x (VL wone))) = (bv_unsigned (den E x) * 2) mod two64.
Proof.
  intros E x. cbn [den alu64 alu]. rewrite bv_shiftl_unsigned, shamt6_bv, shamt_wone. rewrite Z.shiftl_mul_pow2 by lia.
  unfold bv_wrap. rewrite bv_modulus_64. reflexivity.
Qed.
Lemma alu_sll2_u : forall E x, bv_unsigned (den E (VAlu ALU_SLL x (VL wtwo))) = (bv_unsigned (den E x) * 4) mod two64.
Proof.
  intros E x. cbn [den alu64 alu]. rewrite bv_shiftl_unsigned, shamt6_bv, shamt_wtwo. rewrite Z.shiftl_mul_pow2 by lia.
  unfold bv_wrap. rewrite bv_modulus_64. reflexivity.
Qed.

Lemma lit_den : forall E lo d, POT_BASE <= bv_unsigned (den E lo) <= POT_BASE + 2 ^ 41 + 2 ^ 21 -> 0 <= w2Z d <= 2 ^ 20 ->
  bv_unsigned (den E (sv_alu ALU_ADD lo (VL d))) = bv_unsigned (den E lo) + w2Z d.
Proof.
  intros E lo d B D. rewrite den_sv_alu, alu_add_u, den_VL. apply Z.mod_small. unfold POT_BASE, two64 in *. lia.
Qed.
Lemma scan_oldb : forall E ws sc, scan_ok E ws sc -> match sc with Some lo => POT_BASE <= bv_unsigned (den E lo) | None => True end.
Proof. intros E ws [lo|] SC; [| exact I]. destruct SC as (_ & B & _). lia. Qed.
Lemma lit_newb : forall E ws sc d, scan_ok E ws sc -> 0 <= w2Z d <= 2 ^ 20 ->
  match sc with Some _ => POT_BASE <= bv_unsigned (den E (lit_lo sc d)) | None => True end.
Proof. intros E ws [lo|] d SC D; [| exact I]. destruct SC as (_ & B & _). cbn [lit_lo]. rewrite (lit_den E lo d B D). lia. Qed.

Lemma lit_value : forall E ws sc d v, scan_ok E ws sc -> pot_at (map (wden E) ws) v -> 0 <= w2Z d <= 2 ^ 20 ->
  match sc with Some _ => bv_unsigned (den E (lit_lo sc d)) = POT_BASE + (v + w2Z d) | None => True end.
Proof.
  intros E ws [lo|] d v SC PA D; [| exact I]. pose proof (scan_value E ws lo v SC PA) as V. destruct SC as (_ & B & _).
  cbn [lit_lo]. rewrite (lit_den E lo d B D), V. lia.
Qed.

Lemma rebase_den : forall E lo dw c, POT_BASE <= bv_unsigned (den E lo) <= POT_BASE + 2 ^ 41 + 2 ^ 21 -> w2Z dw = two64 - POT_BASE + c -> 0 <= c <= 2 ^ 20 ->
  bv_unsigned (den E (sv_alu ALU_ADD lo (VL dw))) = bv_unsigned (den E lo) - POT_BASE + c.
Proof.
  intros E lo dw c B D C. rewrite den_sv_alu, alu_add_u, den_VL, D.
  replace (bv_unsigned (den E lo) + (two64 - POT_BASE + c)) with ((bv_unsigned (den E lo) - POT_BASE + c) + 1 * two64) by lia.
  rewrite Z.mod_add by (unfold two64; lia). apply Z.mod_small. unfold POT_BASE, two64 in *. lia.
Qed.

Lemma pw_den_lo : forall E z, bv_unsigned (ev E z) <= 2 ^ 41 -> bv_unsigned (den E (VP z POT_BASEw)) = POT_BASE + bv_unsigned (ev E z).
Proof.
  intros E z H. rewrite den_VPu, POT_BASEw_ok. pose proof (bv_unsigned_in_range _ (ev E z)) as R. rewrite bv_modulus_64 in R.
  rewrite Z.mod_small by (unfold POT_BASE, two64 in *; lia). lia.
Qed.

Lemma sym_newb : forall E (sc : option sv) z', bv_unsigned (ev E z') <= 2 ^ 41 ->
  match sc with Some _ => POT_BASE <= bv_unsigned (den E (VP z' POT_BASEw)) | None => True end.
Proof. intros E [lo|] z' H; [| exact I]. rewrite (pw_den_lo E z' H). pose proof (bv_unsigned_in_range _ (ev E z')). lia. Qed.

Lemma pot_pre_sound : forall E fs aw lo, facts_hold E fs -> pot_pre fs aw (Some lo) = true -> POT_BASE <= bv_unsigned (den E lo) ->
  bv_unsigned (den E lo) <= POT_BASE + 2 ^ 40 + 2 ^ 20.
Proof.
  intros E fs aw lo HF H LB. cbn [pot_pre] in H.
  destruct (wleu (snd (sv_bounds fs lo)) PRE_MAXw) eqn:BR.
  { pose proof (sv_bounds_sound E fs HF lo) as B. destruct (sv_bounds fs lo) as [l h]. unfold inb in B. cbn [fst snd] in B, BR.
    rewrite wleu_w2Z in BR. apply Z.leb_le in BR. rewrite PRE_MAXw_ok in BR. lia. }
  destruct (decide_ltu_t fs (VL PRE_MAXw) lo) as [[|]|] eqn:D.
  - pose proof (cred_route_sound E fs aw lo HF H LB). lia.
  - pose proof (decide_ltu_t_sound E fs HF _ _ _ D) as LT. apply (proj1 (ltu_iff _ _ false)) in LT. rewrite den_VL, PRE_MAXw_ok in LT. lia.
  - pose proof (cred_route_sound E fs aw lo HF H LB). lia.
Qed.

Lemma sym_word : forall E E0 fs aw ws lo nP v0 dlt,
  facts_hold E fs -> scan_ok E ws (Some lo) -> pot_pre fs aw (Some lo) = true -> pot_at (map (wden E) ws) v0 ->
  den E lo = den E0 lo -> ev E nP = Z_to_bv 64 (pot_word E0 (Some lo) + dlt) ->
  0 <= v0 + dlt -> dlt <= 2 ^ 20 ->
  bv_unsigned (ev E nP) = v0 + dlt /\ v0 + dlt <= 2 ^ 41 /\
  POT_BASE <= bv_unsigned (den E lo) <= POT_BASE + 2 ^ 41 + 2 ^ 21 /\ bv_unsigned (den E lo) = POT_BASE + v0.
Proof.
  intros E E0 fs aw ws lo nP v0 dlt HF SC PRE PA DL EV POS SMALL.
  pose proof (scan_value E ws lo v0 SC PA) as V. destruct SC as (_ & B & _). pose proof (pot_pre_sound E fs aw lo HF PRE ltac:(lia)) as PM.
  cbn [pot_word] in EV. rewrite <- DL, V in EV. replace (POT_BASE + v0 - POT_BASE + dlt) with (v0 + dlt) in EV by lia.
  assert (R : 0 <= v0 + dlt <= 2 ^ 41) by lia.
  split; [| split; [lia| split; [exact B| exact V]]].
  rewrite EV, Z_to_bv_unsigned. unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. unfold two64. lia.
Qed.

Lemma pot_facts_push_hold : forall E lo z' SZ v', POT_BASE <= bv_unsigned (den E lo) <= POT_BASE + 2 ^ 41 + 2 ^ 21 ->
  bv_unsigned (ev E z') = v' -> 0 <= v' <= 2 ^ 41 -> 0 <= bv_unsigned (den E SZ) <= 2 ^ 20 ->
  v' + 2 * bv_unsigned (den E SZ) = bv_unsigned (den E lo) - POT_BASE + 88 ->
  forall fs, facts_hold E fs -> Forall (fact_holds E) (pot_facts_push fs (Some lo) z' SZ).
Proof.
  intros E lo z' SZ v' B EV V S EQ fs HF. cbn [pot_facts_push]. apply Forall_app. split.
  2:{ destruct (big_sz fs SZ) eqn:BG; [| constructor]. constructor; [| constructor]. unfold big_sz in BG.
      destruct (decide_ltu_t fs (VL BIG_SZw) SZ) as [[|]|] eqn:D; try discriminate.
      pose proof (decide_ltu_t_sound E fs HF _ _ _ D) as LT. apply (proj1 (ltu_iff _ _ true)) in LT. rewrite den_VL in LT. change (w2Z BIG_SZw) with 32761 in LT.
      cbn [fact_holds]. rewrite (rebase_den E lo D_PUSHw 88 B D_PUSHw_ok ltac:(lia)), den_VPu. change (w2Z BIG_PAYw) with 65524.
      pose proof (bv_unsigned_in_range _ (ev E z')) as R. rewrite bv_modulus_64 in R.
      rewrite Z.mod_small by (unfold two64; lia). lia. }
  constructor; [| constructor; [| constructor]].
  - cbn [fact_holds]. apply bv_eq. rewrite (rebase_den E lo D_PUSHw 88 B D_PUSHw_ok ltac:(lia)).
    change (den E (VAlu ALU_ADD (VP z' wzero) (VAlu ALU_SLL SZ (VL wone)))) with (alu64 ALU_ADD (den E (VP z' wzero)) (den E (VAlu ALU_SLL SZ (VL wone)))).
    rewrite alu_add_u, alu_sll1_u, den_VPu, wzero_ok, Z.add_0_r.
    pose proof (bv_unsigned_in_range _ (ev E z')) as R. rewrite bv_modulus_64 in R.
    rewrite (Z.mod_small (bv_unsigned (ev E z'))) by lia. rewrite (Z.mod_small (bv_unsigned (den E SZ) * 2)) by (unfold two64; lia).
    rewrite Z.mod_small by (unfold two64; lia). lia.
  - cbn [fact_holds]. rewrite wzero_ok, FXMAXw_ok. lia.
Qed.
Lemma pot_facts_body_hold : forall E lo z' SZ v', POT_BASE <= bv_unsigned (den E lo) <= POT_BASE + 2 ^ 41 + 2 ^ 21 ->
  bv_unsigned (ev E z') = v' -> 0 <= v' <= 2 ^ 41 -> 0 <= bv_unsigned (den E SZ) <= 2 ^ 20 ->
  v' = bv_unsigned (den E lo) - POT_BASE + 40 + 4 * bv_unsigned (den E SZ) ->
  Forall (fact_holds E) (pot_facts_body (Some lo) z' SZ).
Proof.
  intros E lo z' SZ v' B EV V S EQ. cbn [pot_facts_body]. constructor; [| constructor; [| constructor]].
  - cbn [fact_holds]. apply bv_eq.
    change (den E (VAlu ALU_ADD (sv_alu ALU_ADD lo (VL D_BODYw)) (VAlu ALU_SLL SZ (VL wtwo))))
      with (alu64 ALU_ADD (den E (sv_alu ALU_ADD lo (VL D_BODYw))) (den E (VAlu ALU_SLL SZ (VL wtwo)))).
    rewrite alu_add_u, alu_sll2_u, (rebase_den E lo D_BODYw 40 B D_BODYw_ok ltac:(lia)), den_VPu, wzero_ok, Z.add_0_r.
    pose proof (bv_unsigned_in_range _ (ev E z')) as R. rewrite bv_modulus_64 in R.
    rewrite (Z.mod_small (bv_unsigned (ev E z'))) by lia. rewrite (Z.mod_small (bv_unsigned (den E SZ) * 4)) by (unfold two64; lia).
    rewrite Z.mod_small by (unfold POT_BASE, two64 in *; lia). lia.
  - cbn [fact_holds]. rewrite wzero_ok, FXMAXw_ok. lia.
Qed.

End GPot.
