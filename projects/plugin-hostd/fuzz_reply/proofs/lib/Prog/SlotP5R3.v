From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import StatementKept SlotInv SlotSteps SlotRes
  SlotParse SlotCaps3 SlotRI3 RelayRunT RelayRunF RelayModel HarnessRep ListRep CheckRep ListTr HarnessTr SlotRun3.
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition arr_c (cap c : Z) : Z := if cap =? 0 then 0 else one_if c (band (16 * cap)).

Definition arr_dl (cap cap' c : Z) : Z := arr_c cap' c - arr_c cap c.

Definition gm_keys (s : shl) (ln : list Z) : list Z :=
  match gesture ln with
  | Some (GBegin, x) => if existsb (list_eqb x) (sh_keys s) then [] else [Z.of_nat (length x) + 1]
  | _ => []
  end.

Definition gm_frees (s : shl) (ln : list Z) : list Z :=
  match gesture ln with
  | Some (GEnd, x) =>
      match find_key x (sh_keys s) with Some i => [rec_len (nth i (sh_recs s) (Known pdefT, []))] | None => [] end
  | _ => []
  end.

Fixpoint cnl_keys (j : nat) (s : shl) (rs : list (tad * list Z)) : list Z :=
  match rs with
  | [] => []
  | r :: rs' =>
      gm_keys s (snd r) ++ cnl_keys (j + nret sptr (gesture_model_tr s (snd r))) (gesture_model_sh j s (snd r)) rs'
  end.

Fixpoint cnl_frees (j : nat) (s : shl) (rs : list (tad * list Z)) : list Z :=
  match rs with
  | [] => []
  | r :: rs' =>
      gm_frees s (snd r) ++ rec_len r ::
        cnl_frees (j + nret sptr (gesture_model_tr s (snd r))) (gesture_model_sh j s (snd r)) rs'
  end.

Definition cse_ds (nm : Z -> tad) (gone : Z) (P : list byte) (rs : list (Z * list byte)) (d : list byte)
    : list (tad * list Z) :=
  if gone =? 0 then
    match ends_run P rs d (want_of P rs) with Some (_, ds, _) => map (shr nm) ds | None => [] end
  else map (shr nm) (List.rev (base.filter (fun r => prefixb P (snd r)) rs)).

Definition check_shape_ends_room3_S : Prop :=
  forall (nm : Z -> tad) gone P rs d (b : pbound3) (qs : list sptr),
    length qs = nretF (check_shape_ends_tr nm gone P rs d) ->
    roomF pack3_form qs b (check_shape_ends_tr nm gone P rs d).

Definition check_shape_ends_ledger3_S : Prop :=
  forall NW pl k V L A (b : pbound3) al alb (nm : Z -> tad) gone P rs d (qs : list sptr) k' V' L' A',
    RI3_ledger NW pl k V L A b al alb ->
    nc_step NW pl k' V L A V' L' A' al alb (fun _ => 0) 0 ->
    mis_nc V' L' (p3_mis (runF pack3_form qs b (check_shape_ends_tr nm gone P rs d))) ->
    exists al' alb', RI3_ledger NW pl k' V' L' A' (runF pack3_form qs b (check_shape_ends_tr nm gone P rs d)) al' alb'.

Definition check_shape_ends_effect3_S : Prop :=
  forall (nm : Z -> tad) gone P rs d (qs : list sptr) (b : pbound3),
    length (p3_live b) = 49%nat ->
    let b' := runF pack3_form qs b (check_shape_ends_tr nm gone P rs d) in
    let fs := map rec_len (cse_ds nm gone P rs d) in
    p3_cap b' = p3_cap b /\ p3_mcap b' = p3_mcap b /\ length (p3_live b') = 49%nat /\
    (forall c, 0 <= c < 49 -> znth c (p3_live b') = znth c (p3_live b) - bcnt c fs) /\
    p3_bytes b' = p3_bytes b - zsum (fun n => n) fs /\
    (forall c, count_mis (p3_mis b') c <= count_mis (p3_mis b) c) /\ Forall (fun n => 0 <= n) fs.

Definition check_no_loss_effect3_S : Prop :=
  forall (s : shl) (rs : list (tad * list Z)) (qs : list sptr) (b : pbound3),
    length (p3_live b) = 49%nat ->
    let b' := runF pack3_form qs b (check_no_loss_tr 0 s rs) in
    let s' := check_no_loss_sh 0 s rs in
    let ks := cnl_keys 0 s rs in
    let fs := cnl_frees 0 s rs in
    p3_cap b' = p3_cap b /\ p3_mcap b' = p3_mcap b /\ length (p3_live b') = 49%nat /\
    (forall c, 0 <= c < 49 ->
       znth c (p3_live b') = znth c (p3_live b) + bcnt c ks - bcnt c fs + arr_dl (sh_cap s) (sh_cap s') c) /\
    p3_bytes b' = p3_bytes b + zsum (fun n => n) ks - zsum (fun n => n) fs + 16 * sh_cap s' - 16 * sh_cap s /\
    (forall c, count_mis (p3_mis b') c <= count_mis (p3_mis b) c) /\
    Forall (fun n => 0 <= n) ks /\ Forall (fun n => 0 <= n) fs.

Definition check_no_loss_room3_S : Prop :=
  forall NW pl k V L A (b : pbound3) al alb (H E : hlist),
    let s := sh_of (known_at L A) H in
    let rs := map (shr (known_at L A)) (hl_recs E) in
    RI3_ledger NW pl k V L A b al alb ->
    hl_n H + Z.of_nat (count_begin (texts E)) < 2 ^ 22 ->
    (forall c, 0 <= c < 49 -> bcnt c (ekeys_hl E) <= ek_c V c) ->
    zsum (fun n => n) (ekeys_hl E) <= ek_b V ->
    forall qs, length qs = nretF (check_no_loss_tr 0 s rs) -> roomF pack3_form qs b (check_no_loss_tr 0 s rs).

Definition check_no_loss_ledger3_S : Prop :=
  forall NW pl k V L A (b : pbound3) al alb (H E : hlist) (qs : list sptr) k' V' L' A',
    let s := sh_of (known_at L A) H in
    let rs := map (shr (known_at L A)) (hl_recs E) in
    let s' := check_no_loss_sh 0 s rs in
    RI3_ledger NW pl k V L A b al alb ->
    call_step NW pl k' V L A V' L' A' al alb (cnl_keys 0 s rs) (arr_dl (sh_cap s) (sh_cap s'))
      (16 * sh_cap s' - 16 * sh_cap s) ->
    mis_nc V' L' (p3_mis (runF pack3_form qs b (check_no_loss_tr 0 s rs))) ->
    exists al' alb', RI3_ledger NW pl k' V' L' A' (runF pack3_form qs b (check_no_loss_tr 0 s rs)) al' alb'.

Definition check_no_loss_credit3_S : Prop :=
  forall NW pl k V L A (b : pbound3) al alb (H E : hlist) k' V',
    let s := sh_of (known_at L A) H in
    let rs := map (shr (known_at L A)) (hl_recs E) in
    let ks := cnl_keys 0 s rs in
    RI3_ledger NW pl k V L A b al alb -> k <= k' -> rv_pend V' = rv_pend V ->
    (forall c, 0 <= c < 49 -> ek_c V' c + bcnt c (ekeys_hl E) = ek_c V c) ->
    ek_b V' + zsum (fun n => n) (ekeys_hl E) = ek_b V ->
    (forall c, 0 <= c < 49 -> znth c al + bcnt c ks + ek_c V' c + prom_c (rv_pend V') c <= cons_c pl k' c) /\
    alb + zsum (fun n => n) ks + ek_b V' + promb (rv_pend V') <= consb pl k'.

Ltac fa_ev := repeat (apply Forall_cons; [cbn [ev_ok ev_grow]; first [exact I | (try unfold rec_len); lia]|]);
  apply Forall_nil.

Lemma NMAX_v : NMAX = 536879104.
Proof. vm_compute. reflexivity. Qed.

Lemma BMAX_v : BMAX = 17592186044416.
Proof. vm_compute. reflexivity. Qed.

Lemma CONSB_MAX_v : CONSB_MAX = 143435264.
Proof. vm_compute. reflexivity. Qed.

Lemma P22_v : 2 ^ 22 = 4194304.
Proof. reflexivity. Qed.

Lemma bcnt_one c n : bcnt c [n] = one_if c (band n).
Proof. rewrite bcnt_cons. change (bcnt c []) with 0. lia. Qed.

Lemma zsum_id_one m : zsum (fun n => n) [m] = m.
Proof. unfold zsum. cbn [fold_right]. lia. Qed.

Lemma zsum_id_cons m ks : zsum (fun n => n) (m :: ks) = m + zsum (fun n => n) ks.
Proof. rewrite zsum_cons. reflexivity. Qed.

Lemma count_mis_del M p c : count_mis (mis_del M p) c <= count_mis M c.
Proof. apply count_mis_filter. Qed.

Lemma arr_c_b cap c : 0 <= arr_c cap c <= 1.
Proof. unfold arr_c. destruct (cap =? 0); [lia|apply one_if_b]. Qed.

Lemma arr_c_0 c : arr_c 0 c = 0.
Proof. reflexivity. Qed.

Lemma arr_c_8 c : arr_c 8 c = one_if c (band 128).
Proof. reflexivity. Qed.

Lemma arr_c_nz cap c : cap <> 0 -> arr_c cap c = one_if c (band (16 * cap)).
Proof. intros H. unfold arr_c. destruct (Z.eqb_spec cap 0); [contradiction|reflexivity]. Qed.

Lemma arr_c_2 cap c : cap <> 0 -> arr_c (2 * cap) c = one_if c (band (32 * cap)).
Proof.
  intros H. unfold arr_c. destruct (Z.eqb_spec (2 * cap) 0); [lia|].
  replace (16 * (2 * cap)) with (32 * cap) by lia. reflexivity.
Qed.

Lemma grow_cap_00 n cap : n = cap -> cap = 0 -> grow_cap n cap = 8.
Proof. intros -> ->. reflexivity. Qed.

Lemma grow_cap_2 n cap : n = cap -> cap <> 0 -> grow_cap n cap = 2 * cap.
Proof. intros -> H. unfold grow_cap. rewrite Z.eqb_refl. destruct (Z.eqb_spec cap 0); [contradiction|reflexivity]. Qed.

Lemma grow_cap_id n cap : n <> cap -> grow_cap n cap = cap.
Proof. intros H. unfold grow_cap. destruct (Z.eqb_spec n cap); [contradiction|reflexivity]. Qed.

Lemma sh_cap_push j s x : sh_cap (list_push_sh j s x) = grow_cap (sh_n s) (sh_cap s).
Proof. unfold list_push_sh, grow_cap. destruct (sh_n s =? sh_cap s); reflexivity. Qed.

Lemma sh_n_push j s x : sh_n (list_push_sh j s x) = sh_n s + 1.
Proof.
  unfold list_push_sh. destruct (sh_n s =? sh_cap s); unfold sh_n; cbn [sh_recs]; rewrite length_app; cbn [length];
    lia.
Qed.

Lemma sh_n_drop s i : sh_n (list_drop_sh s i) <= sh_n s.
Proof. unfold sh_n, list_drop_sh. cbn [sh_recs]. rewrite length_app, length_firstn, length_skipn. lia. Qed.

Lemma sh_n_of nm (H : hlist) : sh_n (sh_of nm H) = hl_n H.
Proof. unfold sh_n, sh_of, hl_n. cbn [sh_recs]. rewrite length_map. reflexivity. Qed.

Lemma map_snd_shr nm (E : hlist) : map snd (map (shr nm) (hl_recs E)) = texts E.
Proof. unfold texts. rewrite map_map. reflexivity. Qed.

Lemma rec_len_nonneg_map (l : list (tad * list Z)) : Forall (fun n => 0 <= n) (map rec_len l).
Proof. induction l as [|r l IH]; [constructor|]. cbn [map]. constructor; [unfold rec_len; lia|exact IH]. Qed.

Lemma gm_ok s ln : Forall ev_ok (gesture_model_tr s ln) /\ Forall ev_grow (gesture_model_tr s ln).
Proof.
  assert (Hn : 0 <= sh_n s) by (unfold sh_n; lia).
  unfold gesture_model_tr. destruct (gesture ln) as [[[|] x]|]; [| |split; constructor].
  - destruct (existsb (list_eqb x) (sh_keys s)); [split; constructor|].
    unfold list_push_tr, list_grow_tr. destruct (Z.eqb_spec (sh_n s) (sh_cap s)) as [En|En];
      [destruct (sh_cap s =? 0)|]; cbn [app]; split; fa_ev.
  - destruct (find_key x (sh_keys s)) as [i|]; [|split; constructor].
    unfold list_drop_tr, rec_drop_tr. split; fa_ev.
Qed.

Lemma gm_keys_nonneg s ln : Forall (fun n => 0 <= n) (gm_keys s ln).
Proof.
  unfold gm_keys. destruct (gesture ln) as [[[|] x]|]; [destruct (existsb (list_eqb x) (sh_keys s))| |];
    repeat constructor; lia.
Qed.

Lemma gm_frees_nonneg s ln : Forall (fun n => 0 <= n) (gm_frees s ln).
Proof.
  unfold gm_frees. destruct (gesture ln) as [[[|] x]|]; [|destruct (find_key x (sh_keys s))|];
    repeat constructor; unfold rec_len; lia.
Qed.

Lemma gm_keys_len s ln : zlen (gm_keys s ln) <= if is_begin ln then 1 else 0.
Proof.
  unfold gm_keys, is_begin. destruct (gesture ln) as [[[|] x]|];
    [destruct (existsb (list_eqb x) (sh_keys s))| |]; unfold zlen; cbn [length]; lia.
Qed.

Lemma gm_dl j s ln c : tr_dl (gesture_model_tr s ln) c =
  bcnt c (gm_keys s ln) - bcnt c (gm_frees s ln) + arr_dl (sh_cap s) (sh_cap (gesture_model_sh j s ln)) c.
Proof.
  unfold gesture_model_tr, gesture_model_sh, gm_keys, gm_frees. destruct (gesture ln) as [[[|] x]|].
  - destruct (existsb (list_eqb x) (sh_keys s)).
    + change (tr_dl [] c) with 0. change (bcnt c []) with 0. unfold arr_dl. lia.
    + rewrite sh_cap_push. unfold list_push_tr, list_grow_tr, arr_dl.
      rewrite tr_dl_app, bcnt_one. change (bcnt c []) with 0.
      destruct (Z.eqb_spec (sh_n s) (sh_cap s)) as [En|En]; [destruct (Z.eqb_spec (sh_cap s) 0) as [Ec|Ec]|].
      * rewrite (grow_cap_00 _ _ En Ec), Ec, arr_c_8, arr_c_0, !tr_dl_one. cbn [ev_dl]. lia.
      * rewrite (grow_cap_2 _ _ En Ec), (arr_c_2 _ c Ec), (arr_c_nz _ c Ec), !tr_dl_one. cbn [ev_dl]. lia.
      * rewrite (grow_cap_id _ _ En), tr_dl_one. change (tr_dl [] c) with 0. cbn [ev_dl]. lia.
  - destruct (find_key x (sh_keys s)) as [i|].
    + unfold list_drop_tr, rec_drop_tr, arr_dl. rewrite tr_dl_one, bcnt_one. change (bcnt c []) with 0.
      change (sh_cap (list_drop_sh s i)) with (sh_cap s). cbn [ev_dl]. lia.
    + change (tr_dl [] c) with 0. change (bcnt c []) with 0. unfold arr_dl. lia.
  - change (tr_dl [] c) with 0. change (bcnt c []) with 0. unfold arr_dl. lia.
Qed.

Lemma gm_db j s ln : tr_db (gesture_model_tr s ln) =
  zsum (fun n => n) (gm_keys s ln) - zsum (fun n => n) (gm_frees s ln) +
  16 * sh_cap (gesture_model_sh j s ln) - 16 * sh_cap s.
Proof.
  unfold gesture_model_tr, gesture_model_sh, gm_keys, gm_frees. destruct (gesture ln) as [[[|] x]|].
  - destruct (existsb (list_eqb x) (sh_keys s)).
    + change (tr_db []) with 0. change (zsum (fun n : Z => n) []) with 0. lia.
    + rewrite sh_cap_push. unfold list_push_tr, list_grow_tr.
      rewrite tr_db_app, zsum_id_one. change (zsum (fun n : Z => n) []) with 0.
      destruct (Z.eqb_spec (sh_n s) (sh_cap s)) as [En|En]; [destruct (Z.eqb_spec (sh_cap s) 0) as [Ec|Ec]|].
      * rewrite (grow_cap_00 _ _ En Ec), Ec, !tr_db_one. cbn [ev_db]. lia.
      * rewrite (grow_cap_2 _ _ En Ec), !tr_db_one. cbn [ev_db]. lia.
      * rewrite (grow_cap_id _ _ En), tr_db_one. change (tr_db []) with 0. cbn [ev_db]. lia.
  - destruct (find_key x (sh_keys s)) as [i|].
    + unfold list_drop_tr, rec_drop_tr. rewrite tr_db_one, zsum_id_one. change (zsum (fun n : Z => n) []) with 0.
      change (sh_cap (list_drop_sh s i)) with (sh_cap s). cbn [ev_db]. lia.
    + change (tr_db []) with 0. change (zsum (fun n : Z => n) []) with 0. lia.
  - change (tr_db []) with 0. change (zsum (fun n : Z => n) []) with 0. lia.
Qed.

Lemma cnl_ok j s rs : Forall ev_ok (check_no_loss_tr j s rs) /\ Forall ev_grow (check_no_loss_tr j s rs).
Proof.
  revert j s. induction rs as [|r rs IH]; intros j s; [split; constructor|]. cbn [check_no_loss_tr].
  destruct (gm_ok s (snd r)) as [G1 G2].
  destruct (IH (j + nret sptr (gesture_model_tr s (snd r)))%nat (gesture_model_sh j s (snd r))) as [I1 I2].
  unfold rec_drop_tr. split; (apply Forall_app; split; [assumption|]); cbn [app]; constructor; try assumption;
    cbn [ev_ok ev_grow]; first [exact I | unfold rec_len; lia].
Qed.

Lemma cnl_keys_nonneg j s rs : Forall (fun n => 0 <= n) (cnl_keys j s rs).
Proof.
  revert j s. induction rs as [|r rs IH]; intros j s; [constructor|]. cbn [cnl_keys].
  apply Forall_app. split; [apply gm_keys_nonneg|apply IH].
Qed.

Lemma cnl_frees_nonneg j s rs : Forall (fun n => 0 <= n) (cnl_frees j s rs).
Proof.
  revert j s. induction rs as [|r rs IH]; intros j s; [constructor|]. cbn [cnl_frees].
  apply Forall_app. split; [apply gm_frees_nonneg|]. constructor; [unfold rec_len; lia|apply IH].
Qed.

Lemma count_begin_cons_n x l : count_begin (x :: l) = (if is_begin x then S (count_begin l) else count_begin l).
Proof. unfold count_begin. cbn. destruct (is_begin x); reflexivity. Qed.

Lemma count_begin_cons x l : Z.of_nat (count_begin (x :: l)) = (if is_begin x then 1 else 0) + Z.of_nat (count_begin l).
Proof. rewrite count_begin_cons_n. destruct (is_begin x); lia. Qed.

Lemma cnl_keys_len j s rs : zlen (cnl_keys j s rs) <= Z.of_nat (count_begin (map snd rs)).
Proof.
  revert j s. induction rs as [|r rs IH]; intros j s; [cbn [cnl_keys]; unfold zlen; cbn [length]; lia|].
  cbn [cnl_keys map]. rewrite count_begin_cons.
  specialize (IH (j + nret sptr (gesture_model_tr s (snd r)))%nat (gesture_model_sh j s (snd r))).
  pose proof (gm_keys_len s (snd r)) as G. unfold zlen in *. rewrite length_app.
  destruct (is_begin (snd r)); lia.
Qed.

Lemma gm_keys_ek s ln : gm_keys s ln = [] \/ gm_keys s ln = ekey_of ln.
Proof.
  unfold gm_keys, ekey_of. destruct (gesture ln) as [[[|] x]|];
    [destruct (existsb (list_eqb x) (sh_keys s))| |]; first [left; reflexivity|right; reflexivity].
Qed.

Lemma ekeys_cons ln ls : ekeys (ln :: ls) = ekey_of ln ++ ekeys ls.
Proof. reflexivity. Qed.

Lemma cnl_keys_bcnt j s rs c : bcnt c (cnl_keys j s rs) <= bcnt c (ekeys (map snd rs)).
Proof.
  revert j s. induction rs as [|r rs IH]; intros j s; [cbn [cnl_keys map ekeys concat]; lia|].
  cbn [cnl_keys map]. rewrite ekeys_cons, !bcnt_app.
  match goal with |- context [cnl_keys ?j' ?s' rs] => pose proof (IH j' s') end.
  destruct (gm_keys_ek s (snd r)) as [X|X]; rewrite X;
    [pose proof (bcnt_nonneg c (ekey_of (snd r))); change (bcnt c []) with 0|]; lia.
Qed.

Lemma cnl_keys_zsum j s rs : zsum (fun n => n) (cnl_keys j s rs) <= zsum (fun n => n) (ekeys (map snd rs)).
Proof.
  revert j s. induction rs as [|r rs IH]; intros j s; [cbn [cnl_keys map ekeys concat]; lia|].
  cbn [cnl_keys map]. rewrite ekeys_cons, !zsum_app.
  match goal with |- context [cnl_keys ?j' ?s' rs] => pose proof (IH j' s') end.
  destruct (gm_keys_ek s (snd r)) as [X|X]; rewrite X;
    [pose proof (zsum_id_nonneg _ (ekey_of_nonneg (snd r))); rewrite zsum_nil|]; lia.
Qed.

Lemma cnl_keys_bcnt_hl nm j s E c : bcnt c (cnl_keys j s (map (shr nm) (hl_recs E))) <= bcnt c (ekeys_hl E).
Proof. pose proof (cnl_keys_bcnt j s (map (shr nm) (hl_recs E)) c) as X. rewrite map_snd_shr in X. exact X. Qed.

Lemma cnl_keys_zsum_hl nm j s E :
  zsum (fun n => n) (cnl_keys j s (map (shr nm) (hl_recs E))) <= zsum (fun n => n) (ekeys_hl E).
Proof. pose proof (cnl_keys_zsum j s (map (shr nm) (hl_recs E))) as X. rewrite map_snd_shr in X. exact X. Qed.

Lemma cnl_dl j s rs c : tr_dl (check_no_loss_tr j s rs) c =
  bcnt c (cnl_keys j s rs) - bcnt c (cnl_frees j s rs) + arr_dl (sh_cap s) (sh_cap (check_no_loss_sh j s rs)) c.
Proof.
  revert j s. induction rs as [|r rs IH]; intros j s.
  - cbn [check_no_loss_tr cnl_keys cnl_frees check_no_loss_sh]. change (tr_dl [] c) with 0.
    change (bcnt c []) with 0. unfold arr_dl. lia.
  - cbn [check_no_loss_tr cnl_keys cnl_frees check_no_loss_sh].
    rewrite !tr_dl_app, (gm_dl j s (snd r) c), IH, !bcnt_app, bcnt_cons.
    unfold rec_drop_tr. rewrite tr_dl_one. cbn [ev_dl]. unfold arr_dl. lia.
Qed.

Lemma cnl_db j s rs : tr_db (check_no_loss_tr j s rs) =
  zsum (fun n => n) (cnl_keys j s rs) - zsum (fun n => n) (cnl_frees j s rs) +
  16 * sh_cap (check_no_loss_sh j s rs) - 16 * sh_cap s.
Proof.
  revert j s. induction rs as [|r rs IH]; intros j s.
  - cbn [check_no_loss_tr cnl_keys cnl_frees check_no_loss_sh]. change (tr_db []) with 0.
    change (zsum (fun n : Z => n) []) with 0. lia.
  - cbn [check_no_loss_tr cnl_keys cnl_frees check_no_loss_sh].
    rewrite !tr_db_app, (gm_db j s (snd r)), IH, !zsum_app, zsum_id_cons.
    unfold rec_drop_tr. rewrite tr_db_one. cbn [ev_db]. lia.
Qed.

Lemma cse_tr nm gone P rs d : check_shape_ends_tr nm gone P rs d = recs_drop_tr (cse_ds nm gone P rs d).
Proof.
  unfold check_shape_ends_tr, cse_ds. destruct (gone =? 0); [|reflexivity].
  destruct (ends_run P rs d (want_of P rs)) as [[[? ?] ?]|]; reflexivity.
Qed.

Theorem check_shape_ends_room3 : check_shape_ends_room3_S.
Proof. intros nm gone P rs d b qs _. rewrite cse_tr. apply roomF_frees, recs_drop_free. Qed.

Theorem check_shape_ends_effect3 : check_shape_ends_effect3_S.
Proof.
  intros nm gone P rs d qs b Hl. cbv zeta. rewrite runF3, cse_tr.
  destruct (recs_drop_ok (cse_ds nm gone P rs d)) as [O1 O2].
  split; [apply run3_cap|]. split; [apply run3_mcap|]. split; [rewrite run3_len; exact Hl|].
  split; [intros c Hc; rewrite run3_live by assumption; rewrite recs_drop_dl; lia|].
  split; [rewrite run3_bytes, recs_drop_db; lia|].
  split; [intros c; apply run3_mis; assumption|]. apply rec_len_nonneg_map.
Qed.

Theorem check_shape_ends_ledger3 : check_shape_ends_ledger3_S.
Proof.
  intros NW pl k V L A b al alb nm gone P rs d qs k' V' L' A' HL HS HM.
  pose proof HL as (_ & _ & _ & HlL & _).
  pose proof (check_shape_ends_effect3 nm gone P rs d qs b HlL) as X. cbv zeta in X.
  destruct X as (E1 & E2 & E3 & E4 & E5 & _ & K).
  exists al, alb.
  apply (ledger3_nc NW pl k V L A b al alb k' V' L' A' _ (fun _ => 0) 0 HL HS E1 E2 E3); [| |exact HM].
  - intros c Hc. cbv beta. rewrite E4 by exact Hc.
    pose proof (bcnt_nonneg c (map rec_len (cse_ds nm gone P rs d))). lia.
  - rewrite E5. pose proof (zsum_id_nonneg _ K). lia.
Qed.

Theorem check_no_loss_effect3 : check_no_loss_effect3_S.
Proof.
  intros s rs qs b Hl. cbv zeta. rewrite runF3. destruct (cnl_ok 0 s rs) as [O1 O2].
  split; [apply run3_cap|]. split; [apply run3_mcap|]. split; [rewrite run3_len; exact Hl|].
  split; [intros c Hc; rewrite run3_live by assumption; rewrite cnl_dl; lia|].
  split; [rewrite run3_bytes, cnl_db; lia|].
  split; [intros c; apply run3_mis; assumption|].
  split; [apply cnl_keys_nonneg|apply cnl_frees_nonneg].
Qed.

Theorem check_no_loss_ledger3 : check_no_loss_ledger3_S.
Proof.
  intros NW pl k V L A b al alb H E qs k' V' L' A'. cbv zeta. intros HL HS HM.
  pose proof HL as (_ & _ & _ & HlL & _).
  pose proof (check_no_loss_effect3 (sh_of (known_at L A) H) (map (shr (known_at L A)) (hl_recs E)) qs b HlL) as X.
  cbv zeta in X. destruct X as (E1 & E2 & E3 & E4 & E5 & _ & K1 & K2).
  eexists. eexists.
  apply (ledger3_call NW pl k V L A b al alb k' V' L' A' _ _ _ _ HL K1 HS E1 E2 E3); [| |exact HM].
  - intros c Hc. rewrite E4 by exact Hc.
    pose proof (bcnt_nonneg c (cnl_frees 0 (sh_of (known_at L A) H) (map (shr (known_at L A)) (hl_recs E)))). lia.
  - rewrite E5. pose proof (zsum_id_nonneg _ K2). lia.
Qed.

Theorem check_no_loss_credit3 : check_no_loss_credit3_S.
Proof.
  intros NW pl k V L A b al alb H E k' V'. cbv zeta. intros HL Hk HP HEc HEb. rewrite HP. split.
  - intros c Hc. pose proof (cnl_keys_bcnt_hl (known_at L A) 0 (sh_of (known_at L A) H) E c).
    pose proof (HEc c Hc). pose proof (ledger3_credit _ _ _ _ _ _ _ _ _ c HL Hc). pose proof (cons_mono pl k k' c Hk).
    lia.
  - pose proof (cnl_keys_zsum_hl (known_at L A) 0 (sh_of (known_at L A) H) E).
    pose proof (ledger3_creditb _ _ _ _ _ _ _ _ _ HL). pose proof (consb_mono pl k k' Hk). lia.
Qed.

Definition arr_pot (cap : Z) : Z := 16 * Z.max 0 (8388608 - Z.max 0 cap).

Definition pinv (pl : list byte) (BB cap n : Z) (ks : list Z) (b : pbound3) : Prop :=
  p3_cap b = CS_reply pl /\ p3_mcap b = MC_reply /\ length (p3_live b) = 49%nat /\
  (forall c, 0 <= c < 49 -> count_mis (p3_mis b) c + 1 <= MC_ONE) /\
  (forall c, 0 <= c < 49 -> znth c (p3_live b) - arr_c cap c + bcnt c ks + 2 <= znth c (p3_cap b)) /\
  Forall (fun m => 0 <= m) ks /\ 0 <= n /\ n + zlen ks < 4194304 /\ zsum (fun m => m) ks <= NMAX /\
  p3_bytes b + zsum (fun m => m) ks + arr_pot cap <= BB /\ BB + 67108864 <= BMAX.

Lemma arr_pot_b cap : 0 <= arr_pot cap <= 134217728.
Proof. unfold arr_pot. lia. Qed.

Lemma pinv_free pl BB cap n n' ks b m p : pinv pl BB cap n ks b -> 0 <= m -> 0 <= n' <= n ->
  pinv pl BB cap n' ks (pb3_free b m p).
Proof.
  intros (HC & HM & Hl & HMis & HL & Hks & Hn & HN & HS & HB & HBB) Hm Hn'.
  pose proof (band_range m Hm) as Bm. unfold pinv, pb3_free. cbn [p3_cap p3_mcap p3_live p3_mis p3_bytes].
  split; [exact HC|]. split; [exact HM|]. split; [rewrite lv_add_length; exact Hl|].
  split; [intros c Hc; pose proof (count_mis_del (p3_mis b) p c); pose proof (HMis c Hc); lia|].
  split; [intros c Hc; rewrite znth_lv_add_d by (first [exact Hl|lia]); pose proof (HL c Hc);
          pose proof (one_if_b c (band m)); lia|].
  split; [exact Hks|]. split; [lia|]. split; [lia|]. split; [exact HS|]. split; [lia|exact HBB].
Qed.

Lemma pinv_copy pl BB cap n m ks b : pinv pl BB cap n (m :: ks) b ->
  room_pack3 b m /\ pinv pl BB cap (n + 1) ks (pb3_malloc b m).
Proof.
  intros (HC & HM & Hl & HMis & HL & Hks & Hn & HN & HS & HB & HBB).
  apply Forall_cons_iff in Hks as [Hm Hks]. pose proof (band_range m Hm) as Bm.
  pose proof (zsum_id_nonneg ks Hks) as Z0. rewrite zsum_id_cons in HS, HB. pose proof (arr_pot_b cap).
  unfold zlen in HN. cbn [length] in HN.
  split.
  - apply (room3_at pl); [exact HC|exact HM|lia|lia| |exact HMis].
    pose proof (HL (band m) Bm) as X. rewrite bcnt_cons in X. unfold one_if in X. rewrite Z.eqb_refl in X.
    pose proof (bcnt_nonneg (band m) ks). pose proof (arr_c_b cap (band m)). lia.
  - unfold pinv, pb3_malloc. cbn [p3_cap p3_mcap p3_live p3_mis p3_bytes].
    split; [exact HC|]. split; [exact HM|]. split; [rewrite lv_add_length; exact Hl|]. split; [exact HMis|].
    split; [intros c Hc; rewrite znth_lv_add_d by (first [exact Hl|lia]); pose proof (HL c Hc) as X;
            rewrite bcnt_cons in X; lia|].
    split; [exact Hks|]. split; [lia|]. split; [unfold zlen; lia|]. split; [lia|]. split; [lia|exact HBB].
Qed.

Lemma pinv_first pl BB n ks b : pinv pl BB 0 n ks b -> room_pack3 b 128 /\ pinv pl BB 8 n ks (pb3_malloc b 128).
Proof.
  intros (HC & HM & Hl & HMis & HL & Hks & Hn & HN & HS & HB & HBB).
  pose proof (band_range 128 ltac:(lia)) as B0. pose proof (zsum_id_nonneg ks Hks) as Z0.
  assert (P0 : arr_pot 0 = 134217728) by reflexivity. assert (P8 : arr_pot 8 = 134217600) by reflexivity.
  rewrite P0 in HB. pose proof NMAX_v as NV.
  split.
  - apply (room3_at pl); [exact HC|exact HM|lia|lia| |exact HMis].
    pose proof (HL (band 128) B0) as X. rewrite arr_c_0 in X. pose proof (bcnt_nonneg (band 128) ks). lia.
  - unfold pinv, pb3_malloc. cbn [p3_cap p3_mcap p3_live p3_mis p3_bytes].
    split; [exact HC|]. split; [exact HM|]. split; [rewrite lv_add_length; exact Hl|]. split; [exact HMis|].
    split; [intros c Hc; rewrite znth_lv_add_d by (first [exact Hl|lia]); pose proof (HL c Hc) as X;
            rewrite arr_c_0 in X; rewrite arr_c_8; lia|].
    split; [exact Hks|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [rewrite P8; lia|exact HBB].
Qed.

Lemma pinv_grow pl BB cap ks b p q : pinv pl BB cap cap ks b -> cap <> 0 ->
  room_pack3 b (32 * cap) /\ pinv pl BB (2 * cap) cap ks (pb3_realloc b (16 * cap) (32 * cap) p q).
Proof.
  intros (HC & HM & Hl & HMis & HL & Hks & Hn & HN & HS & HB & HBB) Hc0.
  pose proof (zsum_id_nonneg ks Hks) as Z0.
  assert (Hcap : 0 < cap < 4194304) by (unfold zlen in HN; lia).
  assert (P1 : arr_pot cap = 16 * (8388608 - cap)) by (unfold arr_pot; lia).
  assert (P2 : arr_pot (2 * cap) = 16 * (8388608 - 2 * cap)) by (unfold arr_pot; lia).
  pose proof (band_range (16 * cap) ltac:(lia)) as B1. pose proof (band_range (32 * cap) ltac:(lia)) as B2.
  rewrite P1 in HB. pose proof NMAX_v as NV.
  split.
  - apply (room3_at pl); [exact HC|exact HM|lia|lia| |exact HMis].
    pose proof (HL (band (32 * cap)) B2) as X. pose proof (bcnt_nonneg (band (32 * cap)) ks).
    pose proof (arr_c_b cap (band (32 * cap))). lia.
  - unfold pinv, pb3_realloc. cbn [p3_cap p3_mcap p3_live p3_mis p3_bytes].
    split; [exact HC|]. split; [exact HM|]. split; [rewrite !lv_add_length; exact Hl|].
    split; [intros c Hc; pose proof (count_mis_realloc (p3_mis b) (16 * cap) (32 * cap) p q c ltac:(lia));
            pose proof (HMis c Hc); lia|].
    split; [intros c Hc; rewrite znth_lv_add_d by (first [rewrite lv_add_length; exact Hl|lia]);
            rewrite znth_lv_add_d by (first [exact Hl|lia]); pose proof (HL c Hc) as X;
            rewrite (arr_c_nz cap c Hc0) in X; rewrite (arr_c_2 cap c Hc0); lia|].
    split; [exact Hks|]. split; [lia|]. split; [exact HN|]. split; [exact HS|]. split; [rewrite P2; lia|exact HBB].
Qed.

Lemma pinv_gm pl BB qs j s ln ks b : pinv pl BB (sh_cap s) (sh_n s) (gm_keys s ln ++ ks) b ->
  room3 qs b j (gesture_model_tr s ln) /\
  pinv pl BB (sh_cap (gesture_model_sh j s ln)) (sh_n (gesture_model_sh j s ln)) ks (run3 qs b j (gesture_model_tr s ln)).
Proof.
  unfold gesture_model_tr, gesture_model_sh, gm_keys. destruct (gesture ln) as [[[|] x]|].
  - destruct (existsb (list_eqb x) (sh_keys s)); cbn [app]; intros HP; [split; [exact I|exact HP]|].
    rewrite sh_cap_push, sh_n_push. unfold list_push_tr, list_grow_tr.
    destruct (Z.eqb_spec (sh_n s) (sh_cap s)) as [En|En]; [destruct (Z.eqb_spec (sh_cap s) 0) as [Ec|Ec]|];
      cbn [app room_from run_from].
    + rewrite (grow_cap_00 _ _ En Ec). rewrite Ec in HP.
      destruct (pinv_first pl BB _ _ b HP) as [R1 P1]. destruct (pinv_copy pl BB _ _ _ _ _ P1) as [R2 P2].
      split; [split; [exact R1|split; [exact R2|exact I]]|exact P2].
    + rewrite (grow_cap_2 _ _ En Ec). rewrite En in HP |- *.
      destruct (pinv_grow pl BB _ _ b (resolve sptr (SP 0 0) qs (sh_v s)) (nth j qs (SP 0 0)) HP Ec) as [R1 P1].
      destruct (pinv_copy pl BB _ _ _ _ _ P1) as [R2 P2].
      split; [split; [exact R1|split; [exact R2|exact I]]|exact P2].
    + rewrite (grow_cap_id _ _ En). destruct (pinv_copy pl BB _ _ _ _ _ HP) as [R2 P2].
      split; [split; [exact R2|exact I]|exact P2].
  - destruct (find_key x (sh_keys s)) as [i|]; cbn [app]; intros HP; [|split; [exact I|exact HP]].
    unfold list_drop_tr, rec_drop_tr. cbn [room_from run_from]. split; [exact I|].
    change (sh_cap (list_drop_sh s i)) with (sh_cap s).
    apply (pinv_free pl BB _ (sh_n s)); [exact HP|unfold rec_len; lia|].
    pose proof (sh_n_drop s i). split; [unfold sh_n; lia|lia].
  - cbn [app]. intros HP. split; [exact I|exact HP].
Qed.

Lemma pinv_cnl pl BB qs rs : forall j s b, pinv pl BB (sh_cap s) (sh_n s) (cnl_keys j s rs) b ->
  room3 qs b j (check_no_loss_tr j s rs).
Proof.
  induction rs as [|r rs IH]; intros j s b HP; [exact I|]. cbn [check_no_loss_tr cnl_keys] in *.
  destruct (pinv_gm pl BB qs j s (snd r) _ b HP) as [R1 P1].
  apply room_from_app. split; [exact R1|]. apply room_from_app.
  unfold rec_drop_tr. split; [cbn [room_from]; exact I|].
  change (nret sptr [RFree (rec_len r) (fst r)]) with 0%nat. rewrite Nat.add_0_r. cbn [run_from].
  apply IH. apply (pinv_free pl BB _ (sh_n (gesture_model_sh j s (snd r)))); [exact P1|unfold rec_len; lia|].
  split; [unfold sh_n; lia|lia].
Qed.

Lemma pinv_init NW pl k V L A b al alb s rs :
  RI3_ledger NW pl k V L A b al alb -> sh_n s + Z.of_nat (count_begin (map snd rs)) < 2 ^ 22 ->
  (forall c, 0 <= c < 49 -> znth c al + bcnt c (cnl_keys 0 s rs) + prom_c (rv_pend V) c <= cons_c pl k c) ->
  alb + zsum (fun n => n) (cnl_keys 0 s rs) + promb (rv_pend V) <= consb pl k ->
  pinv pl (p3_bytes b + zsum (fun n => n) (cnl_keys 0 s rs) + 134217728) (sh_cap s) (sh_n s) (cnl_keys 0 s rs) b.
Proof.
  intros HL HN HC HB. pose proof HL as (HCp & HM & _ & HlL & _ & Ha & _).
  pose proof (cnl_keys_nonneg 0 s rs) as Hks. pose proof (zsum_id_nonneg _ Hks) as Z0.
  pose proof (cnl_keys_len 0 s rs) as KL. pose proof (consb_le pl k). pose proof (promb_nonneg (rv_pend V)).
  pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL) as PB. rewrite PB3_MAX_val in PB.
  rewrite CONSB_MAX_v in *. rewrite P22_v in HN. pose proof NMAX_v as NV. pose proof BMAX_v as BV.
  pose proof (arr_pot_b (sh_cap s)).
  unfold pinv. split; [exact HCp|]. split; [exact HM|]. split; [exact HlL|].
  split; [intros c Hc; pose proof (ledger3_mis _ _ _ _ _ _ _ _ _ c HL Hc) as X; rewrite HM, MC_reply_at in X by exact Hc;
          exact X|].
  split; [intros c Hc; pose proof (ledger3_margin _ _ _ _ _ _ _ _ _ c _ HL Hc (HC c Hc));
          pose proof (arr_c_b (sh_cap s) c); lia|].
  split; [exact Hks|]. split; [unfold sh_n; lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

Theorem check_no_loss_room3 : check_no_loss_room3_S.
Proof.
  intros NW pl k V L A b al alb H E. cbv zeta. intros HL HN HKc HKb qs _. rewrite roomF3.
  apply (pinv_cnl pl (p3_bytes b + zsum (fun n => n) (cnl_keys 0 (sh_of (known_at L A) H)
    (map (shr (known_at L A)) (hl_recs E))) + 134217728)).
  apply (pinv_init NW pl k V L A b al alb); [exact HL| | |].
  - rewrite sh_n_of, map_snd_shr. exact HN.
  - intros c Hc. pose proof (cnl_keys_bcnt_hl (known_at L A) 0 (sh_of (known_at L A) H) E c).
    pose proof (HKc c Hc). pose proof (ledger3_credit _ _ _ _ _ _ _ _ _ c HL Hc). lia.
  - pose proof (cnl_keys_zsum_hl (known_at L A) 0 (sh_of (known_at L A) H) E).
    pose proof (ledger3_creditb _ _ _ _ _ _ _ _ _ HL). lia.
Qed.

