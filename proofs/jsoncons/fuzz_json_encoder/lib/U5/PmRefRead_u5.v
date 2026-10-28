(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmEncSpecs_u5 PmLibSpecsW_u5 PmRef_u5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMRR.
Import PML. Import PMR.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma firstn_length_le : forall {A} n (l : list A), (length (firstn n l) <= n)%nat.
Proof. intros A n l. rewrite length_firstn. lia. Qed.
Lemma skipn_skipn : forall {A} n m (l : list A), skipn n (skipn m l) = skipn (n + m) l.
Proof. intros A n m l. revert n l. induction m as [|m IH]; intros n l; [rewrite Nat.add_0_r; reflexivity|].
  destruct l as [|x r]; [rewrite !skipn_nil; reflexivity|]. rewrite Nat.add_succ_r. cbn [skipn]. apply IH. Qed.
Lemma length_skipn_Z : forall {A} (l : list A) k, 0 <= k <= Z.of_nat (length l) -> Z.of_nat (length (skipn (Z.to_nat k) l)) = Z.of_nat (length l) - k.
Proof. intros A l k Hk. rewrite length_skipn. lia. Qed.
Lemma length_firstn_Z : forall {A} (l : list A) k, 0 <= k -> Z.of_nat (length (firstn (Z.to_nat k) l)) = Z.min k (Z.of_nat (length l)).
Proof. intros A l k Hk. rewrite length_firstn. lia. Qed.
Lemma Forall_skipn : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof. intros A P n l H. revert n. induction H; intros [|n]; cbn; auto. Qed.
Lemma Forall_firstn : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof. intros A P n l H. revert n. induction H; intros [|n]; cbn; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition chunkw (s : list Z) (bof : bool) : nat * Z * bool :=
  match s with
  | [] => (0%nat, 0, bof)
  | _ => if bof then match detect s with None => (0%nat, E_ILLEGAL_UNICODE, bof) | Some j => (j, 0, false) end else (0%nat, 0, false)
  end.
Lemma refill_full : forall rs b r, r_w rs = b :: r -> refill rs = (rs, 0).
Proof. intros [c w rest bof eof] b r H. cbn in H. subst w. reflexivity. Qed.
Lemma refill_eof : forall rs, r_eof rs = true -> refill rs = (rs, 0).
Proof. intros [c w rest bof eof] H. cbn in H. subst eof. unfold refill. cbn. destruct w; reflexivity. Qed.
Lemma refill_read : forall c rest bof,
  refill (RS c [] rest bof false) =
    let s := firstn (Z.to_nat CHUNK) rest in
    let '(j, cd, b') := chunkw s bof in
    (RS c (if cd =? 0 then skipn j s else []) (skipn (Z.to_nat CHUNK) rest) b' (length s <? Z.to_nat CHUNK)%nat, cd).
Proof.
  intros c rest bof. unfold refill. cbn [r_w r_eof r_rest r_c r_bof]. cbv zeta.
  destruct (firstn (Z.to_nat CHUNK) rest) as [|b r] eqn:Es; [reflexivity|].
  unfold chunkw. destruct bof; [|reflexivity]. destruct (detect (b :: r)) as [j|]; reflexivity.
Qed.
Lemma detect_le4 : forall s j, detect s = Some j -> (j <= 3 /\ j <= length s)%nat.
Proof.
  intros s j H. unfold detect in H.
  destruct (pfx [255; 254; 0; 0] s); [discriminate H|]. destruct (pfx [0; 0; 254; 255] s); [discriminate H|].
  destruct (pfx [255; 254] s); [discriminate H|]. destruct (pfx [254; 255] s); [discriminate H|].
  destruct (pfx [239; 187; 191] s) eqn:P3.
  - injection H as <-. unfold pfx in P3. apply andb_prop in P3 as [P3 _]. apply Nat.leb_le in P3. cbn [length] in P3. lia.
  - destruct (Nat.ltb_spec (length s) 4) as [L|L]; [injection H as <-; lia|].
    destruct s as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn [length] in L; try lia.
    repeat match goal with H : (if ?c then _ else _) = Some j |- _ => destruct c; [try discriminate H|] end; injection H as <-; lia.
Qed.
Lemma chunkw_skip_le : forall s bof j cd b', chunkw s bof = (j, cd, b') -> (j <= length s /\ j <= 3)%nat.
Proof.
  intros s bof j cd b' H. unfold chunkw in H. destruct s as [|b r]; [injection H as <- _ _; cbn; lia|].
  destruct bof; [|injection H as <- _ _; cbn; lia]. destruct (detect (b :: r)) as [k|] eqn:D; injection H as <- _ _; [|cbn; lia].
  pose proof (detect_le4 _ _ D). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rres : Type := (rstate * list evk * Z * Z)%type.
Definition t_rs (t : rres) : rstate := fst (fst (fst t)).
Definition t_evs (t : rres) : list evk := snd (fst (fst t)).
Definition t_al (t : rres) : Z := snd (fst t).
Definition t_code (t : rres) : Z := snd t.
(* [comment removed for export] *)
Definition rpre (evs : list evk) (al : Z) (t : rres) : rres := (t_rs t, evs ++ t_evs t, al + t_al t, t_code t).
Lemma rpre_nil : forall t, rpre [] 0 t = t.
Proof. intros [[[rs e] a] k]. reflexivity. Qed.
Lemma rpre_rpre : forall e1 a1 e2 a2 t, rpre e1 a1 (rpre e2 a2 t) = rpre (e1 ++ e2) (a1 + a2) t.
Proof. intros e1 a1 e2 a2 [[[rs e] a] k]. unfold rpre. cbn. rewrite app_assoc, Z.add_assoc. reflexivity. Qed.
Lemma t_rs_rpre : forall e a t, t_rs (rpre e a t) = t_rs t. Proof. intros e a [[[rs e'] a'] k]. reflexivity. Qed.
Lemma t_evs_rpre : forall e a t, t_evs (rpre e a t) = e ++ t_evs t. Proof. intros e a [[[rs e'] a'] k]. reflexivity. Qed.
Lemma t_al_rpre : forall e a t, t_al (rpre e a t) = a + t_al t. Proof. intros e a [[[rs e'] a'] k]. reflexivity. Qed.
Lemma t_code_rpre : forall e a t, t_code (rpre e a t) = t_code t. Proof. intros e a [[[rs e'] a'] k]. reflexivity. Qed.
Lemma t_eta : forall t : rres, t = (t_rs t, t_evs t, t_al t, t_code t). Proof. intros [[[rs e] a] k]. reflexivity. Qed.

(* [comment removed for export] *)
Definition rs_after (q : res) (rs1 : rstate) : rstate := RS (q_c q) (q_w q) (r_rest rs1) (r_bof rs1) (r_eof rs1).
Definition weof (rs1 : rstate) : bool := match r_w rs1 with [] => true | _ => false end.

Lemma rloop_unfold : forall F rs, rloop (S F) rs =
    if negb (c_more (r_c rs)) then (rs, [], 0, 0)
    else
      let p := refill rs in let rs1 := fst p in
      if negb (snd p =? 0) then (rs1, [], 0, snd p)
      else
        let eof := match r_w rs1 with [] => true | _ => false end in
        let q := parse_some (r_c rs1) (r_w rs1) in
        let rs2 := RS (q_c q) (q_w q) (r_rest rs1) (r_bof rs1) (r_eof rs1) in
        if negb (q_code q =? 0) then (rs2, q_evs q, q_al q, q_code q)
        else if eof && (c_st (q_c q) =? ST_START) then (rs2, q_evs q, q_al q, 0)
        else if eof && negb ((c_st (q_c q) =? ST_ACCEPT) || c_done (q_c q)) then (rs2, q_evs q, q_al q, E_EOF)
        else let t := rloop F rs2 in (fst (fst (fst t)), q_evs q ++ snd (fst (fst t)), q_al q + snd (fst t), snd t).
Proof. reflexivity. Qed.

Lemma rloop_stopped : forall F rs, c_more (r_c rs) = false -> rloop (S F) rs = (rs, [], 0, 0).
Proof. intros F rs H. rewrite rloop_unfold, H. reflexivity. Qed.
Lemma rloop_referr : forall F rs rs1 cd, c_more (r_c rs) = true -> refill rs = (rs1, cd) -> cd <> 0 -> rloop (S F) rs = (rs1, [], 0, cd).
Proof. intros F rs rs1 cd Hm Hr Hcd. rewrite rloop_unfold, Hm, Hr. cbn [negb fst snd]. destruct (Z.eqb_spec cd 0); [contradiction | reflexivity]. Qed.
(* [comment removed for export] *)
Lemma rloop_pserr : forall F rs rs1 q, c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> q_code q <> 0 ->
  rloop (S F) rs = (rs_after q rs1, q_evs q, q_al q, q_code q).
Proof.
  intros F rs rs1 q Hm Hr Hq Hc. rewrite rloop_unfold, Hm, Hr. cbn [negb fst snd Z.eqb]. rewrite Hq.
  destruct (Z.eqb_spec (q_code q) 0); [contradiction | reflexivity].
Qed.
(* [comment removed for export] *)
Lemma rloop_start : forall F rs rs1 q, c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> q_code q = 0 ->
  weof rs1 = true -> c_st (q_c q) = ST_START ->
  rloop (S F) rs = (rs_after q rs1, q_evs q, q_al q, 0).
Proof.
  intros F rs rs1 q Hm Hr Hq Hc He Hs. rewrite rloop_unfold, Hm, Hr. cbn [negb fst snd]. rewrite Hq, Hc. cbn [Z.eqb negb].
  unfold weof in He. rewrite He, Hs. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rloop_ueof : forall F rs rs1 q, c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> q_code q = 0 ->
  weof rs1 = true -> c_st (q_c q) <> ST_START -> c_st (q_c q) <> ST_ACCEPT -> c_done (q_c q) = false ->
  rloop (S F) rs = (rs_after q rs1, q_evs q, q_al q, E_EOF).
Proof.
  intros F rs rs1 q Hm Hr Hq Hc He Hs Ha Hd. rewrite rloop_unfold, Hm, Hr. cbn [negb fst snd]. rewrite Hq, Hc. cbn [Z.eqb negb].
  unfold weof in He. rewrite He, Hd. destruct (Z.eqb_spec (c_st (q_c q)) ST_START); [contradiction|]. destruct (Z.eqb_spec (c_st (q_c q)) ST_ACCEPT); [contradiction|]. reflexivity.
Qed.
(* [comment removed for export] *)
Definition rcont (rs1 : rstate) (q : res) : Prop :=
  weof rs1 = false \/ (c_st (q_c q) <> ST_START /\ (c_st (q_c q) = ST_ACCEPT \/ c_done (q_c q) = true)).
Lemma rloop_cont : forall F rs rs1 q, c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> q_code q = 0 ->
  rcont rs1 q ->
  rloop (S F) rs = rpre (q_evs q) (q_al q) (rloop F (rs_after q rs1)).
Proof.
  intros F rs rs1 q Hm Hr Hq Hc HC. rewrite rloop_unfold, Hm, Hr. cbn [negb fst snd]. rewrite Hq, Hc. cbn [Z.eqb negb].
  fold (weof rs1). fold (rs_after q rs1).
  assert (X : (weof rs1 && (c_st (q_c q) =? ST_START)) = false /\ (weof rs1 && negb ((c_st (q_c q) =? ST_ACCEPT) || c_done (q_c q))) = false).
  { destruct HC as [-> | (Hs & Ha)]; [split; reflexivity|]. destruct (weof rs1); [|split; reflexivity]. cbn [andb].
    destruct (Z.eqb_spec (c_st (q_c q)) ST_START); [contradiction|]. split; [reflexivity|].
    destruct Ha as [Ha | ->]; [| rewrite orb_true_r; reflexivity]. rewrite (proj2 (Z.eqb_eq _ _) Ha). reflexivity. }
  destruct X as [-> ->]. rewrite (t_eta (rloop F (rs_after q rs1))) at 1. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nchunks (rs : rstate) : Z := if r_eof rs then 0 else Z.of_nat (length (r_rest rs)) / CHUNK + 1.
Definition wwz (rs : rstate) : Z := match r_w rs with [] => 0 | _ => 1 end.
Definition rankz (c : ctrl) : Z := if (c_st c =? ST_NUMBER) || (c_st c =? ST_CR) then 1 else 0.
Definition RB (rs : rstate) : Z :=
  if negb (c_more (r_c rs)) then 1
  else if (wwz rs =? 0) && (nchunks rs =? 0) then 2 + rankz (r_c rs)
  else wwz rs + nchunks rs + 3.
Lemma nchunks_nonneg : forall rs, 0 <= nchunks rs.
Proof. intros rs. unfold nchunks. destruct (r_eof rs); [lia|]. pose proof (Z.div_pos (Z.of_nat (length (r_rest rs))) CHUNK). unfold CHUNK in *. lia. Qed.
Lemma RB_pos : forall rs, 1 <= RB rs.
Proof.
  intros rs. unfold RB, wwz, rankz. pose proof (nchunks_nonneg rs). destruct (c_more (r_c rs)); cbn [negb]; [|lia].
  destruct (r_w rs); cbn [Z.eqb andb]; [destruct (nchunks rs =? 0)|]; destruct ((c_st (r_c rs) =? ST_NUMBER) || (c_st (r_c rs) =? ST_CR)); lia.
Qed.
(* [comment removed for export] *)
Lemma RB_init : forall p, RB (RS ctrl0 [] p true false) = Z.of_nat (rfuel p).
Proof.
  intros p. unfold RB, rfuel, nchunks, wwz. cbn [r_c r_w r_eof r_rest c_more ctrl0 negb Z.eqb andb].
  pose proof (Z.div_pos (Z.of_nat (length p)) CHUNK ltac:(lia) ltac:(unfold CHUNK; lia)) as P.
  destruct (Z.eqb_spec (Z.of_nat (length p) / CHUNK + 1) 0); [lia|].
  rewrite Nat2Z.inj_add, Nat2Z.inj_div. change (Z.of_nat (Z.to_nat CHUNK)) with CHUNK. change (Z.of_nat 4) with 4. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rtail_unfold : forall F rs, rtail (S F) rs =
    if r_eof rs then (rs, 0)
    else let rs1 := sw rs in
         match r_w rs1 with
         | [] => let p := refill rs1 in if negb (snd p =? 0) then (fst p, snd p) else rtail F (fst p)
         | _ => (rs1, 0)
         end.
Proof. reflexivity. Qed.
Lemma rtail_eof : forall F rs, r_eof rs = true -> rtail (S F) rs = (rs, 0).
Proof. intros F rs H. rewrite rtail_unfold, H. reflexivity. Qed.
Lemma rtail_break : forall F rs b r, r_eof rs = false -> r_w (sw rs) = b :: r -> rtail (S F) rs = (sw rs, 0).
Proof. intros F rs b r He Hw. rewrite rtail_unfold, He. cbv zeta. rewrite Hw. reflexivity. Qed.
Lemma rtail_referr : forall F rs rs2 cd, r_eof rs = false -> r_w (sw rs) = [] -> refill (sw rs) = (rs2, cd) -> cd <> 0 -> rtail (S F) rs = (rs2, cd).
Proof. intros F rs rs2 cd He Hw Hr Hcd. rewrite rtail_unfold, He. cbv zeta. rewrite Hw, Hr. cbn [fst snd negb]. destruct (Z.eqb_spec cd 0); [contradiction | reflexivity]. Qed.
Lemma rtail_cont : forall F rs rs2, r_eof rs = false -> r_w (sw rs) = [] -> refill (sw rs) = (rs2, 0) -> rtail (S F) rs = rtail F rs2.
Proof. intros F rs rs2 He Hw Hr. rewrite rtail_unfold, He. cbv zeta. rewrite Hw, Hr. reflexivity. Qed.

Lemma rcheck_unfold : forall F rs, rcheck (S F) rs =
    let p := refill rs in let rs1 := fst p in
    if negb (snd p =? 0) then snd p
    else let q := match r_w rs1 with [] => ret (r_c rs1) [] | _ => pcheck_done (r_c rs1) (r_w rs1) end in
         if negb (q_code q =? 0) then q_code q
         else let rs2 := RS (q_c q) (q_w q) (r_rest rs1) (r_bof rs1) (r_eof rs1) in
              if r_eof rs2 then 0 else rcheck F rs2.
Proof. reflexivity. Qed.
Lemma rcheck_referr : forall F rs rs1 cd, refill rs = (rs1, cd) -> cd <> 0 -> rcheck (S F) rs = cd.
Proof. intros F rs rs1 cd Hr Hcd. rewrite rcheck_unfold, Hr. cbn [fst snd negb]. destruct (Z.eqb_spec cd 0); [contradiction | reflexivity]. Qed.
(* [comment removed for export] *)
Definition qcheck (rs1 : rstate) : res := match r_w rs1 with [] => ret (r_c rs1) [] | _ => pcheck_done (r_c rs1) (r_w rs1) end.
Lemma rcheck_round : forall F rs rs1 q, refill rs = (rs1, 0) -> qcheck rs1 = q ->
  (q_code q <> 0 -> rcheck (S F) rs = q_code q) /\
  (q_code q = 0 -> r_eof rs1 = true -> rcheck (S F) rs = 0) /\
  (q_code q = 0 -> r_eof rs1 = false -> rcheck (S F) rs = rcheck F (rs_after q rs1)).
Proof.
  intros F rs rs1 q Hr Hq. rewrite rcheck_unfold, Hr. cbn [fst snd negb Z.eqb]. fold (qcheck rs1). rewrite Hq.
  split; [|split].
  - intros Hc. destruct (Z.eqb_spec (q_code q) 0); [contradiction | reflexivity].
  - intros -> ->. reflexivity.
  - intros -> He. cbn [Z.eqb negb r_eof]. rewrite He. unfold rs_after. rewrite He. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rs0 (p : list Z) : rstate := RS ctrl0 [] p true false.
Lemma READ_of : forall p tA, rloop (rfuel p) (rs0 p) = tA ->
  (t_code tA <> 0 -> READ p = (t_evs tA, t_al tA, t_code tA)) /\
  (t_code tA = 0 -> forall tB, rtail (rfuel p) (sw (t_rs tA)) = tB ->
     (snd tB <> 0 -> READ p = (t_evs tA, t_al tA, snd tB)) /\
     (snd tB = 0 -> READ p = (t_evs tA, t_al tA, read_check_done (rfuel p) (fst tB)))).
Proof.
  intros p tA HA. unfold READ. fold (rs0 p). rewrite HA. destruct tA as [[[rsA evsA] alA] cdA]. cbn [fst snd t_rs t_evs t_al t_code].
  split.
  - intros Hc. destruct (Z.eqb_spec cdA 0); [contradiction | reflexivity].
  - intros Hc tB HB. rewrite Hc. cbn [Z.eqb negb]. rewrite HB. split.
    + intros Hb. destruct (Z.eqb_spec (snd tB) 0); [contradiction | reflexivity].
    + intros ->. reflexivity.
Qed.
Lemma K_of : forall p, K p = fst (fst (READ p)). Proof. reflexivity. Qed.
Lemma ALLOW_of : forall p, ALLOW p = snd (fst (READ p)). Proof. reflexivity. Qed.
Lemma CODE_of : forall p, CODE p = snd (READ p). Proof. reflexivity. Qed.

End PMRR.
