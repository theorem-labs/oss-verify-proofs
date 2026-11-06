From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT SlotKept SlotPack
  AllocPack AllocPackRoom AllocBound AllocPack3 AllocPack3Room.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotInv SlotParse SlotCaps3 SlotRI3 SlotRun3
  RelayRunT RelayRunF RelayRep HarnessRep send_line_b_c gesture_end_b_c gestures_end_b_c drain_b_c relay_remove_b_c
  relay_instance_gone_b_c RelayModel RelayKeys.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Definition ncb (n c : Z) : Z := if n =? 0 then 0 else one_if c (band n).

Definition slot3 (n : Z) (x : sptr) : list sptr := if n =? 0 then [] else [x].

Definition res3 (n : Z) : nat := if n =? 0 then 1%nat else 0%nat.

Definition misT (S : list sptr) (r : nat) (M : list (sptr * Z)) : Prop :=
  List.NoDup (map fst M) /\ incl (map fst M) S /\ (length S + r <= NC_MAX)%nat.

Definition pk3_ok (b : pbound3) : Prop :=
  length (p3_live b) = 49%nat /\
  CAPOK2 (GALL3 (p3_cap b) (p3_mcap b)) (GMAP3 (p3_cap b) (p3_mcap b)) BMAX NMAX /\
  (forall c, 0 <= c < 49 -> MC_ONE <= znth c (p3_mcap b)).

Definition cred (h : hsrc) (c : Z) : Z := zsum (rec_cred c) (map snd (hl_recs (hs_pending h))).

Definition credb (h : hsrc) : Z := zsum rec_credb (map snd (hl_recs (hs_pending h))).

Definition dchain (e : rentry) (h : hsrc) (s : dstate) (c : Z) : Z :=
  ncb (ds_cap s) c - ncb (re_cap e) c + (ncb (ds_ka s) c - ncb (ent_ka e) c) +
  (ncb (16 * ds_ecap s) c - ncb (16 * hl_cap (hs_expected h)) c).

Definition dchainb (e : rentry) (h : hsrc) (s : dstate) : Z :=
  ds_cap s - re_cap e + (ds_ka s - ent_ka e) + 16 * (ds_ecap s - hl_cap (hs_expected h)).

Definition dslots (qs : list sptr) (e : rentry) (h : hsrc) (a : dadr) : list sptr :=
  slot3 (re_cap e) (resolveF qs (da_buf a)) ++ slot3 (ent_ka e) (resolveF qs (da_hp a)) ++
  slot3 (hl_cap (hs_expected h)) (resolveF qs (da_ev a)).

Definition dres (e : rentry) (h : hsrc) : nat :=
  (res3 (re_cap e) + res3 (ent_ka e) + res3 (hl_cap (hs_expected h)))%nat.

Definition DRAIN_HR : Z := 32.

Definition DRAIN_B : Z := 2 ^ 40.

Definition drain3 (e : rentry) (h : hsrc) : Prop :=
  forall (lv : bool) (mx NO CAP : Z), 0 <= mx -> 0 <= CAP ->
    let s := drain_fin lv mx NO CAP e h in
    CAP <= ds_ocap s /\
    forall (qs : list sptr) (b : pbound3) (j : nat) (a : dadr) (S : list sptr) (r : nat),
      let td := drain_tr lv mx NO CAP e h j a in
      let b' := run3 qs b j td in
      pk3_ok b ->
      ds_ocap s <= NMAX ->
      (forall c, 0 <= c < 49 -> znth c (p3_live b) + cred h c + DRAIN_HR <= znth c (p3_cap b)) ->
      p3_bytes b - CAP + 2 * ds_ocap s + DRAIN_B <= BMAX ->
      misT (slot3 CAP (resolveF qs (da_out a)) ++ dslots qs e h a ++ S) (r + res3 CAP + dres e h) (p3_mis b) ->
      room3 qs b j td /\
      pk3_ok b' /\ p3_cap b' = p3_cap b /\ p3_mcap b' = p3_mcap b /\
      (exists dks : list Z, Forall (fun n => 0 <= n) dks /\
         (forall c, 0 <= c < 49 ->
            znth c (p3_live b') <= znth c (p3_live b) + (ncb (ds_ocap s) c - ncb CAP c) + dchain e h s c + bcnt c dks) /\
         p3_bytes b' <= p3_bytes b + (ds_ocap s - CAP) + dchainb e h s + zsum (fun n => n) dks /\
         (forall c, 0 <= c < 49 ->
            bcnt c dks + bcnt c (ekeys (lines (hs_state h) (bzs (pending_stream h)))) <= cred h c) /\
         zsum (fun n => n) dks + zsum (fun n => n) (ekeys (lines (hs_state h) (bzs (pending_stream h)))) <= credb h) /\
      p3_bytes b' <= p3_bytes b + (ds_ocap s - CAP) + DRAIN_B /\
      exists D, misT (slot3 (ds_ocap s) (resolveF qs (da_out (drain_adr lv mx NO CAP e h j a))) ++ D ++ S)
                     (r + res3 (ds_ocap s)) (p3_mis b').

Definition gslots (qs : list sptr) (nm : Z -> adrF) (p : rentry * (hsrc * nat)) : list sptr :=
  if re_eof (fst p) =? 0 then dslots qs (fst p) (fst (snd p)) (drain_start nm adr0 (fst p) (fst (snd p))) else [].

Definition gres (p : rentry * (hsrc * nat)) : nat := if re_eof (fst p) =? 0 then dres (fst p) (fst (snd p)) else 0%nat.

Definition gone_dem (ps : list (rentry * (hsrc * nat))) (c : Z) : Z :=
  zsum (fun p => if re_eof (fst p) =? 0 then 3 + cred (fst (snd p)) c else 0) ps.

Definition gone_cred (ps : list (rentry * (hsrc * nat))) (c : Z) : Z :=
  zsum (fun p => if re_eof (fst p) =? 0 then cred (fst (snd p)) c else 0) ps.

Definition gone_credb (ps : list (rentry * (hsrc * nat))) : Z :=
  zsum (fun p => if re_eof (fst p) =? 0 then credb (fst (snd p)) else 0) ps.

Fixpoint gone_dch (ps : list (rentry * (hsrc * nat))) (ss : list dstate) (c : Z) : Z :=
  match ps, ss with
  | p :: ps', s :: ss' => (if re_eof (fst p) =? 0 then dchain (fst p) (fst (snd p)) s c else 0) + gone_dch ps' ss' c
  | _, _ => 0
  end.

Fixpoint gone_dchb (ps : list (rentry * (hsrc * nat))) (ss : list dstate) : Z :=
  match ps, ss with
  | p :: ps', s :: ss' => (if re_eof (fst p) =? 0 then dchainb (fst p) (fst (snd p)) s else 0) + gone_dchb ps' ss'
  | _, _ => 0
  end.

Definition gone_capT (lv : bool) (mx NO CAP : Z) (pre : list Z) (es : list rentry) (hs : list (hsrc * nat))
    (nm : Z -> adrF) (j : nat) (o : adrF) : Z :=
  snd (fst (fst (gone_run lv mx NO CAP pre (combine es hs) nm j o))).

Definition gone_ssT (lv : bool) (mx NO CAP : Z) (pre : list Z) (es : list rentry) (hs : list (hsrc * nat))
    (nm : Z -> adrF) (j : nat) (o : adrF) : list dstate :=
  snd (fst (gone_run lv mx NO CAP pre (combine es hs) nm j o)).

Definition gone_dl (lv : bool) (mx NO CAP : Z) (pre : list Z) (es : list rentry) (hs : list (hsrc * nat))
    (nm : Z -> adrF) (j : nat) (o : adrF) (c : Z) : Z :=
  ncb (gone_capT lv mx NO CAP pre es hs nm j o) c - ncb CAP c +
  gone_dch (combine es hs) (gone_ssT lv mx NO CAP pre es hs nm j o) c.

Definition gone_db (lv : bool) (mx NO CAP : Z) (pre : list Z) (es : list rentry) (hs : list (hsrc * nat))
    (nm : Z -> adrF) (j : nat) (o : adrF) : Z :=
  gone_capT lv mx NO CAP pre es hs nm j o - CAP + gone_dchb (combine es hs) (gone_ssT lv mx NO CAP pre es hs nm j o).

Definition gone_ek (ps : list (rentry * (hsrc * nat))) : list Z :=
  concat (map (fun p => if re_eof (fst p) =? 0 then ekeys (lines (hs_state (fst (snd p))) (bzs (pending_stream (fst (snd p)))))
                        else []) ps).

Definition gone_da (es : list rentry) (hs : list (hsrc * nat)) (c : Z) : Z :=
  gone_cred (combine es hs) c - bcnt c (gone_ek (combine es hs)).

Definition gone_dab (es : list rentry) (hs : list (hsrc * nat)) : Z :=
  gone_credb (combine es hs) - zsum (fun n => n) (gone_ek (combine es hs)).

Definition call_step3 (NW : rview -> Z) (pl : list byte) (k' : Z) (V : rview) (L : layout) (A : astate) (V' : rview)
    (L' : layout) (A' : astate) (al : list Z) (alb : Z) (dl : Z -> Z) (db : Z) (da : Z -> Z) (dab : Z) : Prop :=
  (length (rv_nc V') <= NC_MAX)%nat /\
  (forall c, 0 <= c < 49 -> nc_cnt V L A c + dl c <= nc_cnt V' L' A' c) /\ ncs V L A + db <= ncs V' L' A' /\
  ncs V' L' A' <= NW V' /\ NW V' <= NC_FIX + NC_PER * (alsum al + zsumZ da (zseq 0 49)) + DATA_PER * cdat pl k' /\
  (forall c, 0 <= c < 49 -> znth c al + da c + ek_c V' c + prom_c (rv_pend V') c <= cons_c pl k' c) /\
  alb + dab + ek_b V' + promb (rv_pend V') <= consb pl k' /\ Forall (fun n => 0 <= n) (rv_ek V').

Definition keys3_stmt : Prop :=
  forall (xks : list (Z * adrF)) (lv : bool) (mx no cap : Z) (j : nat) (o : adrF) (qs : list sptr) (b : pbound3)
         (S : list sptr) (r : nat) (capF : Z),
    let k := keys_end_run lv mx no cap xks j o in
    let b' := run3 qs b j (fst k) in
    Forall (fun x => 0 <= fst x) xks -> 0 <= cap -> fst (snd k) <= capF -> capF <= NMAX ->
    pk3_ok b ->
    (forall c, 0 <= c < 49 -> znth c (p3_live b) - ncb cap c + 2 <= znth c (p3_cap b)) ->
    p3_bytes b - cap + 2 * capF <= BMAX ->
    misT (slot3 cap (resolveF qs o) ++ S) (r + res3 cap) (p3_mis b) ->
    room3 qs b j (fst k) /\ pk3_ok b' /\ p3_cap b' = p3_cap b /\ p3_mcap b' = p3_mcap b /\
    (forall c, 0 <= c < 49 -> znth c (p3_live b') <= znth c (p3_live b) + ncb (fst (snd k)) c - ncb cap c) /\
    p3_bytes b' <= p3_bytes b + fst (snd k) - cap /\
    misT (slot3 (fst (snd k)) (resolveF qs (snd (snd k))) ++ S) (r + res3 (fst (snd k))) (p3_mis b').

Definition gone_effect3_stmt : Prop :=
  forall (lv : bool) (mx NO CAP : Z) (pre : list Z) (es : list rentry) (hs : list (hsrc * nat)) (nm : Z -> adrF)
         (o : adrF) (qs : list sptr) (b : pbound3) (F : list sptr) (r : nat),
    let ps := combine es hs in
    let tr := relay_instance_gone_tr lv mx NO CAP pre es hs nm 0 o in
    let b' := runF pack3_form qs b tr in
    let capF := gone_capT lv mx NO CAP pre es hs nm 0 o in
    Forall (fun p => re_eof (fst p) = 0 -> drain3 (fst p) (fst (snd p))) ps ->
    0 <= mx -> 0 <= CAP -> capF <= NMAX ->
    pk3_ok b ->
    (forall c, 0 <= c < 49 -> znth c (p3_live b) + 1 + gone_dem ps c + DRAIN_HR <= znth c (p3_cap b)) ->
    p3_bytes b + 2 * capF + (Z.of_nat (length ps) + 1) * DRAIN_B <= BMAX ->
    misT (slot3 CAP (resolveF qs o) ++ concat (map (gslots qs nm) ps) ++ F) (r + res3 CAP + list_sum (map gres ps))
      (p3_mis b) ->
    roomF pack3_form qs b tr /\ pk3_ok b' /\ p3_cap b' = p3_cap b /\ p3_mcap b' = p3_mcap b /\
    (forall c, 0 <= c < 49 ->
       znth c (p3_live b') <= znth c (p3_live b) + gone_dl lv mx NO CAP pre es hs nm 0 o c + gone_da es hs c) /\
    p3_bytes b' <= p3_bytes b + gone_db lv mx NO CAP pre es hs nm 0 o + gone_dab es hs /\
    (forall c, 0 <= c < 49 -> 0 <= gone_da es hs c) /\ 0 <= gone_dab es hs /\
    exists F', misT (slot3 capF (resolveF qs (gone_out lv mx NO CAP pre es hs nm 0 o)) ++ F') (r + res3 capF) (p3_mis b').

Definition gone_room3_stmt : Prop :=
  forall (NW : rview -> Z) (pl : list byte) (k : Z) (L : layout) (A : astate) (b : pbound3) (al : list Z) (alb : Z)
         (G OUT : Z) (es : list rentry) (hs : list (hsrc * nat)) (lv : bool) (mx NO CAP : Z) (pre : list Z)
         (F : list sptr),
    let nm := known_at L A in
    let ps := combine es hs in
    let tr := relay_instance_gone_tr lv mx NO CAP pre es hs nm 0 (nm OUT) in
    RI3_ledger NW pl k (view_of G OUT es hs) L A b al alb ->
    Forall (fun p => re_eof (fst p) = 0 -> drain3 (fst p) (fst (snd p))) ps ->
    (length es <= 4)%nat -> 0 <= mx -> 0 <= CAP ->
    gone_capT lv mx NO CAP pre es hs nm 0 (nm OUT) <= NMAX ->
    misT (slot3 CAP (sptr_of L A OUT) ++ concat (map (gslots [] nm) ps) ++ F) (res3 CAP + list_sum (map gres ps))
      (p3_mis b) ->
    forall qs, length qs = nretF tr -> roomF pack3_form qs b tr.

Definition gone_ledger3_stmt : Prop :=
  forall (NW : rview -> Z) (pl : list byte) (k k' : Z) (L : layout) (A : astate) (L' : layout) (A' : astate)
         (V' : rview) (b : pbound3) (al : list Z) (alb : Z) (G OUT : Z) (es : list rentry) (hs : list (hsrc * nat))
         (lv : bool) (mx NO CAP : Z) (pre : list Z) (F : list sptr) (qs : list sptr),
    let nm := known_at L A in
    let ps := combine es hs in
    let V := view_of G OUT es hs in
    let tr := relay_instance_gone_tr lv mx NO CAP pre es hs nm 0 (nm OUT) in
    let b' := runF pack3_form qs b tr in
    RI3_ledger NW pl k V L A b al alb ->
    Forall (fun p => re_eof (fst p) = 0 -> drain3 (fst p) (fst (snd p))) ps ->
    (length es <= 4)%nat -> 0 <= mx -> 0 <= CAP ->
    gone_capT lv mx NO CAP pre es hs nm 0 (nm OUT) <= NMAX ->
    misT (slot3 CAP (sptr_of L A OUT) ++ concat (map (gslots [] nm) ps) ++ F) (res3 CAP + list_sum (map gres ps))
      (p3_mis b) ->
    call_step3 NW pl k' V L A V' L' A' al alb (gone_dl lv mx NO CAP pre es hs nm 0 (nm OUT))
      (gone_db lv mx NO CAP pre es hs nm 0 (nm OUT)) (gone_da es hs) (gone_dab es hs) ->
    mis_nc V' L' (p3_mis b') ->
    exists al' alb', RI3_ledger NW pl k' V' L' A' b' al' alb'.

Definition gone_ri3_stmt : Prop :=
  forall (E : sstart) (k k' : Z) (L : layout) (A : astate) (L' : layout) (A' : astate)
         (V' : rview) (b : pbound3) (al : list Z) (alb : Z) (G OUT : Z) (es : list rentry) (hs : list (hsrc * nat))
         (lv : bool) (mx NO CAP : Z) (pre : list Z) (F : list sptr) (qs : list sptr),
    let nm := known_at L A in
    let ps := combine es hs in
    let V := view_of G OUT es hs in
    let tr := relay_instance_gone_tr lv mx NO CAP pre es hs nm 0 (nm OUT) in
    let b' := runF pack3_form qs b tr in
    RI3_ledger rv_wt (ss_pl E) k V L A b al alb ->
    Forall (fun p => re_eof (fst p) = 0 -> drain3 (fst p) (fst (snd p))) ps ->
    (length es <= 4)%nat -> 0 <= mx -> 0 <= CAP ->
    gone_capT lv mx NO CAP pre es hs nm 0 (nm OUT) <= NMAX ->
    misT (slot3 CAP (sptr_of L A OUT) ++ concat (map (gslots [] nm) ps) ++ F) (res3 CAP + list_sum (map gres ps))
      (p3_mis b) ->
    res_ok_pack3 A' b' ->
    call_step3 rv_wt (ss_pl E) k' V L A V' L' A' al alb (gone_dl lv mx NO CAP pre es hs nm 0 (nm OUT))
      (gone_db lv mx NO CAP pre es hs nm 0 (nm OUT)) (gone_da es hs) (gone_dab es hs) ->
    mis_nc V' L' (p3_mis b') ->
    RI3_reply E k' V' L' A'.

Lemma run3_app qs b j t1 t2 : run3 qs b j (t1 ++ t2) = run3 qs (run3 qs b j t1) (j + nretF t1) t2.
Proof. apply run_from_app. Qed.

Lemma room3_app qs b j t1 t2 :
  room3 qs b j (t1 ++ t2) <-> room3 qs b j t1 /\ room3 qs (run3 qs b j t1) (j + nretF t1) t2.
Proof. apply room_from_app. Qed.

Lemma room3_m qs b j n t : room3 qs b j (RMalloc n :: t) = (room_pack3 b n /\ room3 qs (pb3_malloc b n) (S j) t).
Proof. reflexivity. Qed.

Lemma run3_m qs b j n t : run3 qs b j (RMalloc n :: t) = run3 qs (pb3_malloc b n) (S j) t.
Proof. reflexivity. Qed.

Lemma room3_r qs b j k n a t : room3 qs b j (RRealloc k n a :: t) =
  (room_pack3 b n /\ room3 qs (pb3_realloc b k n (resolveF qs a) (nth j qs (SP 0 0))) (S j) t).
Proof. reflexivity. Qed.

Lemma run3_r qs b j k n a t : run3 qs b j (RRealloc k n a :: t) =
  run3 qs (pb3_realloc b k n (resolveF qs a) (nth j qs (SP 0 0))) (S j) t.
Proof. reflexivity. Qed.

Lemma room3_f qs b j n a t : room3 qs b j (RFree n a :: t) = room3 qs (pb3_free b n (resolveF qs a)) j t.
Proof. reflexivity. Qed.

Lemma run3_f qs b j n a t : run3 qs b j (RFree n a :: t) = run3 qs (pb3_free b n (resolveF qs a)) j t.
Proof. reflexivity. Qed.

Lemma ncb_b n c : 0 <= ncb n c <= 1.
Proof. unfold ncb. destruct (n =? 0); [lia|apply one_if_b]. Qed.

Lemma ncb_nz n c : n <> 0 -> ncb n c = one_if c (band n).
Proof. intros H. unfold ncb. rewrite (proj2 (Z.eqb_neq n 0) H). reflexivity. Qed.

Lemma ncb_0 c : ncb 0 c = 0.
Proof. reflexivity. Qed.

Lemma slot3_nz n x : n <> 0 -> slot3 n x = [x].
Proof. intros H. unfold slot3. rewrite (proj2 (Z.eqb_neq n 0) H). reflexivity. Qed.

Lemma res3_nz n : n <> 0 -> res3 n = 0%nat.
Proof. intros H. unfold res3. rewrite (proj2 (Z.eqb_neq n 0) H). reflexivity. Qed.

Lemma misT_r S r r' M : r = r' -> misT S r M -> misT S r' M.
Proof. intros ->. exact (fun H => H). Qed.

Lemma misT_perm S S' r M : Permutation S S' -> misT S r M -> misT S' r M.
Proof.
  intros P (HN & HI & HL). split; [exact HN|]. split.
  - intros y Hy. eapply Permutation_in; [exact P|exact (HI y Hy)].
  - rewrite <- (Permutation_length P). exact HL.
Qed.

Lemma misT_count S r M c : misT S r M -> count_mis M c + 1 <= MC_ONE.
Proof.
  intros (HN & HI & HL). unfold count_mis.
  pose proof (filter_len_le (fun e : sptr * Z => snd e =? c) M) as F.
  pose proof (NoDup_incl_length HN HI) as G. rewrite length_map in G. unfold NC_MAX in HL. unfold MC_ONE. lia.
Qed.

Lemma misT_free S r M p : misT S r M -> misT S r (mis_del M p).
Proof.
  intros (HN & HI & HL). split; [unfold mis_del; apply nodup_map_filter; exact HN|]. split; [|exact HL].
  intros y Hy. apply HI. unfold mis_del in Hy. apply in_map_iff in Hy as (e & <- & He). apply filter_In in He as [He _].
  apply in_map. exact He.
Qed.

Lemma misT_start S r M q : misT S (r + 1) M -> misT (q :: S) r M.
Proof. intros (HN & HI & HL). split; [exact HN|]. split; [intros y Hy; right; exact (HI y Hy)|cbn [length]; lia]. Qed.

Lemma misT_realloc S r M k n x q : misT (x :: S) r M -> misT (q :: S) r (mis_realloc M k n x q).
Proof.
  intros (HN & HI & HL).
  assert (HD : List.NoDup (map fst (mis_del M x))) by (unfold mis_del; apply nodup_map_filter; exact HN).
  assert (HX : ~ In x (map fst (mis_del M x))).
  { intros Hin. apply in_map_iff in Hin as (e & Ee & He). unfold mis_del in He. apply filter_In in He as [_ Hne].
    rewrite Ee, sptr_eqb_refl in Hne. discriminate. }
  assert (HS : incl (map fst (mis_del M x)) S).
  { intros y Hy. pose proof Hy as Hy'. apply in_map_iff in Hy as (e & <- & He). unfold mis_del in He.
    apply filter_In in He as [He _]. destruct (HI (fst e) (in_map fst M e He)) as [E|Hin]; [|exact Hin].
    exfalso. apply HX. rewrite E at 1. exact Hy'. }
  cbn [length] in HL. unfold mis_realloc.
  match goal with |- misT _ _ (if ?c then _ else _) => destruct c eqn:B end.
  - apply andb_true_iff in B as [B _]. apply andb_true_iff in B as [B _]. apply sptr_eqb_eq in B. subst q.
    split; [cbn [map fst]; constructor; [exact HX|exact HD]|]. split; [|cbn [length]; exact HL].
    intros y [<-|Hy]; [left; reflexivity|right; exact (HS y Hy)].
  - split; [exact HD|]. split; [intros y Hy; right; exact (HS y Hy)|cbn [length]; exact HL].
Qed.

Lemma room1 b n S r : pk3_ok b -> 0 <= n <= NMAX -> p3_bytes b + n <= BMAX ->
  znth (band n) (p3_live b) + 1 <= znth (band n) (p3_cap b) -> misT S r (p3_mis b) -> room_pack3 b n.
Proof.
  intros (_ & HC & HM) Hn HB HL HS. apply (room_pack3_of b n BMAX NMAX HC Hn HB HL).
  intros Hb. pose proof (misT_count _ _ _ (band n + 1) HS). pose proof (band_range n ltac:(lia)).
  pose proof (HM (band n + 1) ltac:(lia)). lia.
Qed.

Lemma pk3_malloc b n : pk3_ok b -> pk3_ok (pb3_malloc b n).
Proof.
  intros (Hl & HC & HM). split; [unfold pb3_malloc; cbn [p3_live]; rewrite lv_add_length; exact Hl|].
  split; [exact HC|exact HM].
Qed.

Lemma pk3_free b n p : pk3_ok b -> pk3_ok (pb3_free b n p).
Proof.
  intros (Hl & HC & HM). split; [unfold pb3_free; cbn [p3_live]; rewrite lv_add_length; exact Hl|].
  split; [exact HC|exact HM].
Qed.

Lemma pk3_realloc b k n p q : pk3_ok b -> pk3_ok (pb3_realloc b k n p q).
Proof.
  intros (Hl & HC & HM). split; [unfold pb3_realloc; cbn [p3_live]; rewrite !lv_add_length; exact Hl|].
  split; [exact HC|exact HM].
Qed.

Definition gc3 (b0 : pbound3) (cap0 : Z) (E : Z -> Z) (EB EBB : Z) (S : list sptr) (r : nat) (cap : Z) (x : sptr)
    (b : pbound3) : Prop :=
  pk3_ok b /\ p3_cap b = p3_cap b0 /\ p3_mcap b = p3_mcap b0 /\
  (forall c, 0 <= c < 49 -> znth c (p3_live b) <= znth c (p3_live b0) + ncb cap c - ncb cap0 c + E c) /\
  p3_bytes b <= p3_bytes b0 + cap - cap0 + EB /\ p3_bytes b <= p3_bytes b0 + cap - cap0 + EBB /\
  misT (slot3 cap x ++ S) (r + res3 cap) (p3_mis b).

Definition rc3 (b0 : pbound3) (cap0 : Z) (E : Z -> Z) (EBB capF : Z) : Prop :=
  (forall c, 0 <= c < 49 -> znth c (p3_live b0) - ncb cap0 c + E c + 2 <= znth c (p3_cap b0)) /\
  p3_bytes b0 - cap0 + EBB + 2 * capF <= BMAX /\ capF <= NMAX.

Lemma gc3_mono b0 cap0 E E' EB EB' EBB EBB' S r cap x b :
  (forall c, 0 <= c < 49 -> E c <= E' c) -> EB <= EB' -> EBB <= EBB' ->
  gc3 b0 cap0 E EB EBB S r cap x b -> gc3 b0 cap0 E' EB' EBB' S r cap x b.
Proof.
  intros HE H1 H2 (P & C & M & L & B1 & B2 & HS). split; [exact P|]. split; [exact C|]. split; [exact M|].
  split; [intros c Hc; pose proof (L c Hc); pose proof (HE c Hc); lia|]. split; [lia|]. split; [lia|]. exact HS.
Qed.

Lemma gc3_perm b0 cap0 E EB EBB S S' r cap x b : Permutation S S' ->
  gc3 b0 cap0 E EB EBB S r cap x b -> gc3 b0 cap0 E EB EBB S' r cap x b.
Proof.
  intros P (H1 & H2 & H3 & H4 & H5 & H6 & H7). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  eapply misT_perm; [|exact H7]. apply Permutation_app_head. exact P.
Qed.

Lemma gc3_free b0 cap0 E EB EBB S r cap x b n p : gc3 b0 cap0 E EB EBB S r cap x b -> 0 <= n ->
  gc3 b0 cap0 E EB EBB S r cap x (pb3_free b n p).
Proof.
  intros (HP & HC & HM & HL & HB1 & HB2 & HS) Hn. pose proof HP as (Hl & _).
  split; [apply pk3_free; exact HP|]. split; [exact HC|]. split; [exact HM|].
  split.
  { intros c Hc. pose proof (live3_free b n p c Hl Hn Hc). pose proof (one_if_b c (band n)). pose proof (HL c Hc).
    lia. }
  unfold pb3_free. cbn [p3_bytes p3_mis]. split; [lia|]. split; [lia|]. apply misT_free. exact HS.
Qed.

Lemma gc3_malloc b0 cap0 E EB EBB S r c x q b capF : gc3 b0 cap0 E EB EBB S r 0 x b ->
  rc3 b0 cap0 E EBB capF -> 0 < c <= capF ->
  room_pack3 b c /\ gc3 b0 cap0 E EB EBB S r c q (pb3_malloc b c).
Proof.
  intros (HP & HC & HM & HL & HB1 & HB2 & HS) (R1 & R2 & R3) Hc. pose proof HP as (Hl & _).
  change (misT S (r + 1) (p3_mis b)) in HS. pose proof (band_range c ltac:(lia)) as Bc.
  split.
  - apply (room1 b c S (r + 1) HP); [lia|lia| |exact HS].
    pose proof (HL (band c) ltac:(lia)). pose proof (R1 (band c) ltac:(lia)). pose proof (ncb_b cap0 (band c)).
    rewrite ncb_0 in *. rewrite HC. lia.
  - split; [apply pk3_malloc; exact HP|]. split; [exact HC|]. split; [exact HM|].
    split.
    { intros d Hd. pose proof (live3_malloc b c d ltac:(lia) ltac:(lia)). pose proof (HL d Hd). rewrite ncb_0 in *.
      rewrite (ncb_nz c d) by lia. lia. }
    unfold pb3_malloc. cbn [p3_bytes p3_mis]. split; [lia|]. split; [lia|].
    rewrite (slot3_nz c q), (res3_nz c) by lia. rewrite Nat.add_0_r. apply misT_start. exact HS.
Qed.

Lemma gc3_realloc b0 cap0 E EB EBB S r cap c x q b capF : gc3 b0 cap0 E EB EBB S r cap x b ->
  rc3 b0 cap0 E EBB capF -> 0 < cap < c -> c <= capF ->
  room_pack3 b c /\ gc3 b0 cap0 E EB EBB S r c q (pb3_realloc b cap c x q).
Proof.
  intros (HP & HC & HM & HL & HB1 & HB2 & HS) (R1 & R2 & R3) Hc Hf. pose proof HP as (Hl & _).
  rewrite (slot3_nz cap x), (res3_nz cap) in HS by lia.
  pose proof (band_range c ltac:(lia)) as Bc.
  split.
  - apply (room1 b c ([x] ++ S) (r + 0) HP); [lia|lia| |exact HS].
    pose proof (HL (band c) ltac:(lia)). pose proof (R1 (band c) ltac:(lia)). pose proof (ncb_b cap (band c)).
    pose proof (ncb_b cap0 (band c)). rewrite HC. lia.
  - split; [apply pk3_realloc; exact HP|]. split; [exact HC|]. split; [exact HM|].
    split.
    { intros d Hd. pose proof (live3_realloc b cap c x q d Hl ltac:(lia) ltac:(lia) Hd). pose proof (HL d Hd).
      rewrite (ncb_nz c d), (ncb_nz cap d) in * by lia. lia. }
    unfold pb3_realloc. cbn [p3_bytes p3_mis]. split; [lia|]. split; [lia|].
    rewrite (slot3_nz c q), (res3_nz c) by lia. apply misT_realloc. exact HS.
Qed.

Lemma sl_capi f : forall mx no cap rem j o j' o',
  fst (snd (sl_run f mx no cap rem j o)) = fst (snd (sl_run f mx no cap rem j' o')).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o j' o'; cbn [sl_run]; [reflexivity|].
  destruct (rem <=? 0); [reflexivity|]. destruct (cap <? _); cbn [fst snd]; apply IH.
Qed.

Lemma sl_mono f : forall mx no cap rem j o, 0 <= cap -> cap <= fst (snd (sl_run f mx no cap rem j o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [sl_run]; [cbn [fst snd]; lia|].
  destruct (rem <=? 0); [cbn [fst snd]; lia|].
  destruct (cap <? _) eqn:Hlt; cbn [fst snd].
  - apply Z.ltb_lt in Hlt. etransitivity; [|apply IH; lia]. lia.
  - apply IH. exact Hc.
Qed.

Lemma sl3 f : forall mx no cap rem j o qs b b0 cap0 E EB EBB S r capF,
  0 <= cap -> fst (snd (sl_run f mx no cap rem j o)) <= capF -> rc3 b0 cap0 E EBB capF ->
  gc3 b0 cap0 E EB EBB S r cap (resolveF qs o) b ->
  room3 qs b j (fst (sl_run f mx no cap rem j o)) /\
  gc3 b0 cap0 E EB EBB S r (fst (snd (sl_run f mx no cap rem j o))) (resolveF qs (snd (snd (sl_run f mx no cap rem j o))))
    (run3 qs b j (fst (sl_run f mx no cap rem j o))).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o qs b b0 cap0 E EB EBB S r capF Hc Hf HR HG; cbn [sl_run] in *.
  - split; [exact I|exact HG].
  - destruct (rem <=? 0); [split; [exact I|exact HG]|].
    set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem) in *.
    destruct (cap <? no + n) eqn:Hlt; cbn [fst snd] in *.
    + apply Z.ltb_lt in Hlt.
      pose proof (sl_mono f mx (no + n) ((no + n) * 2) (rem - n) (Datatypes.S j) (Ret j) ltac:(lia)) as M.
      destruct (cap =? 0) eqn:Hz.
      * apply Z.eqb_eq in Hz. subst cap. rewrite room3_m, run3_m.
        destruct (gc3_malloc b0 cap0 E EB EBB S r ((no + n) * 2) (resolveF qs o) (nth j qs (SP 0 0)) b capF HG HR
                    ltac:(lia)) as [Rm Gm].
        destruct (IH mx (no + n) ((no + n) * 2) (rem - n) (Datatypes.S j) (Ret j) qs (pb3_malloc b ((no + n) * 2)) b0 cap0 E EB
                    EBB S r capF ltac:(lia) Hf HR Gm) as [R1 G1].
        split; [split; [exact Rm|exact R1]|exact G1].
      * apply Z.eqb_neq in Hz. rewrite room3_r, run3_r.
        destruct (gc3_realloc b0 cap0 E EB EBB S r cap ((no + n) * 2) (resolveF qs o) (nth j qs (SP 0 0)) b capF HG HR
                    ltac:(lia) ltac:(lia)) as [Rr Gr].
        destruct (IH mx (no + n) ((no + n) * 2) (rem - n) (Datatypes.S j) (Ret j) qs
                    (pb3_realloc b cap ((no + n) * 2) (resolveF qs o) (nth j qs (SP 0 0))) b0 cap0 E EB EBB S r capF
                    ltac:(lia) Hf HR Gr) as [R1 G1].
        split; [split; [exact Rr|exact R1]|exact G1].
    + exact (IH mx (no + n) cap (rem - n) j o qs b b0 cap0 E EB EBB S r capF Hc Hf HR HG).
Qed.

Lemma send_mono live mx NO cap LEN : 0 <= cap -> cap <= send_line_cap live mx NO cap LEN.
Proof. intros Hc. unfold send_line_cap. destruct live; [apply sl_mono; exact Hc|lia]. Qed.

Lemma send3 live mx NO cap LEN j o qs b b0 cap0 E EB EBB S r capF :
  0 <= cap -> send_line_cap live mx NO cap LEN <= capF -> rc3 b0 cap0 E EBB capF ->
  gc3 b0 cap0 E EB EBB S r cap (resolveF qs o) b ->
  room3 qs b j (send_line_tr live mx NO cap LEN j o) /\
  gc3 b0 cap0 E EB EBB S r (send_line_cap live mx NO cap LEN) (resolveF qs (send_line_out live mx NO cap LEN j o))
    (run3 qs b j (send_line_tr live mx NO cap LEN j o)).
Proof.
  intros Hc Hf HR HG. unfold send_line_tr, send_line_out, send_line_cap in *. destruct live.
  - rewrite (sl_capi _ _ _ _ _ 0 adr0 j o) in *. exact (sl3 _ mx NO cap LEN j o qs b b0 cap0 E EB EBB S r capF Hc Hf HR HG).
  - split; [exact I|exact HG].
Qed.

Lemma ge_mono live mx NO cap XL : 0 <= cap -> cap <= gesture_end_cap live mx NO cap XL.
Proof.
  intros Hc. unfold gesture_end_cap. pose proof (send_mono live mx NO cap XL Hc) as M.
  pose proof (send_mono live mx (NO + XL) (send_line_cap live mx NO cap XL) 5 ltac:(lia)). lia.
Qed.

Lemma ge3 live mx NO cap XL j o qs b b0 cap0 E EB EBB S r capF :
  0 <= cap -> gesture_end_cap live mx NO cap XL <= capF -> rc3 b0 cap0 E EBB capF ->
  gc3 b0 cap0 E EB EBB S r cap (resolveF qs o) b ->
  room3 qs b j (gesture_end_tr live mx NO cap XL j o) /\
  gc3 b0 cap0 E EB EBB S r (gesture_end_cap live mx NO cap XL) (resolveF qs (gesture_end_out live mx NO cap XL j o))
    (run3 qs b j (gesture_end_tr live mx NO cap XL j o)).
Proof.
  intros Hc Hf HR HG. unfold gesture_end_tr, gesture_end_cap, gesture_end_out in *.
  pose proof (send_mono live mx NO cap XL Hc) as M1.
  pose proof (send_mono live mx (NO + XL) (send_line_cap live mx NO cap XL) 5 ltac:(lia)) as M2.
  destruct (send3 live mx NO cap XL j o qs b b0 cap0 E EB EBB S r capF Hc ltac:(lia) HR HG) as [R1 G1].
  destruct (send3 live mx (NO + XL) (send_line_cap live mx NO cap XL) 5 (j + nretF (send_line_tr live mx NO cap XL j o))
              (send_line_out live mx NO cap XL j o) qs _ b0 cap0 E EB EBB S r capF ltac:(lia) Hf HR G1) as [R2 G2].
  rewrite room3_app, run3_app. split; [split; assumption|exact G2].
Qed.

Lemma ke_mono xks : forall live mx no cap j o, 0 <= cap -> cap <= fst (snd (keys_end_run live mx no cap xks j o)).
Proof.
  induction xks as [|[xl ka] xr IH]; intros live mx no cap j o Hc; cbn [keys_end_run fst snd]; [lia|].
  pose proof (ge_mono live mx no cap xl Hc) as M. etransitivity; [exact M|]. apply IH. lia.
Qed.

Lemma ke3 xks : forall live mx no cap j o qs b b0 cap0 E EB EBB S r capF,
  Forall (fun x => 0 <= fst x) xks -> 0 <= cap -> fst (snd (keys_end_run live mx no cap xks j o)) <= capF ->
  rc3 b0 cap0 E EBB capF -> gc3 b0 cap0 E EB EBB S r cap (resolveF qs o) b ->
  room3 qs b j (fst (keys_end_run live mx no cap xks j o)) /\
  gc3 b0 cap0 E EB EBB S r (fst (snd (keys_end_run live mx no cap xks j o)))
    (resolveF qs (snd (snd (keys_end_run live mx no cap xks j o)))) (run3 qs b j (fst (keys_end_run live mx no cap xks j o))).
Proof.
  induction xks as [|[xl ka] xr IH]; intros live mx no cap j o qs b b0 cap0 E EB EBB S r capF HX Hc Hf HR HG;
    cbn [keys_end_run fst snd] in *.
  - split; [exact I|exact HG].
  - apply Forall_cons_iff in HX as [Hx HX]. cbn [fst] in Hx.
    pose proof (ge_mono live mx no cap xl Hc) as M1.
    pose proof (ke_mono xr live mx (no + xl + 5) (gesture_end_cap live mx no cap xl)
                  (j + nretF (gesture_end_tr live mx no cap xl j o)) (gesture_end_out live mx no cap xl j o) ltac:(lia)) as M2.
    destruct (ge3 live mx no cap xl j o qs b b0 cap0 E EB EBB S r capF Hc ltac:(lia) HR HG) as [R1 G1].
    pose proof (gc3_free _ _ _ _ _ _ _ _ _ _ (xl + 1) (resolveF qs ka) G1 ltac:(lia)) as G2.
    destruct (IH live mx (no + xl + 5) (gesture_end_cap live mx no cap xl) (j + nretF (gesture_end_tr live mx no cap xl j o))%nat
                (gesture_end_out live mx no cap xl j o) qs _ b0 cap0 E EB EBB S r capF HX ltac:(lia) Hf HR G2) as [R3 G3].
    rewrite room3_app, run3_app, room3_f, run3_f. split; [split; assumption|exact G3].
Qed.

Theorem keys3 : keys3_stmt.
Proof.
  intros xks lv mx no cap j o qs b S r capF. cbv zeta. intros HX Hc Hf HN HP HL HB HS.
  assert (HR : rc3 b cap (fun _ => 0) 0 capF).
  { split; [intros c Hc'; pose proof (HL c Hc'); lia|]. split; [lia|exact HN]. }
  assert (G0 : gc3 b cap (fun _ => 0) 0 0 S r cap (resolveF qs o) b).
  { split; [exact HP|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros c _; lia|].
    split; [lia|]. split; [lia|exact HS]. }
  destruct (ke3 xks lv mx no cap j o qs b b cap (fun _ => 0) 0 0 S r capF HX Hc Hf HR G0)
    as [R (HP' & HC' & HM' & HL' & HB' & _ & HS')].
  split; [exact R|]. split; [exact HP'|]. split; [exact HC'|]. split; [exact HM'|].
  split; [intros c Hc'; pose proof (HL' c Hc'); lia|]. split; [lia|exact HS'].
Qed.

Lemma gone_run_cons lv mx no cap pre e hj r nm j o :
  exists s a0 td a xks k g,
    s = after_drain lv mx no cap e (fst hj) /\ a0 = drain_start nm o e (fst hj) /\
    td = (if re_eof e =? 0 then drain_tr lv mx no cap e (fst hj) j a0 else []) /\
    a = after_drain_adr lv mx no cap e (fst hj) j a0 /\
    xks = map (fun x => (Z.of_nat (length (fst x)), snd x)) (fst (geia pre (combine (ds_H s) (da_keys a)))) /\
    k = keys_end_run lv mx (ds_no s) (ds_ocap s) xks (j + nretF td) (da_out a) /\
    g = gone_run lv mx (ds_no s + fold_right (fun xl acc => xl + 5 + acc) 0 (map fst xks)) (fst (snd k)) pre r nm
          (j + nretF td + nretF (fst k)) (snd (snd k)) /\
    fst (fst (fst (gone_run lv mx no cap pre ((e, hj) :: r) nm j o))) = td ++ fst k ++ fst (fst (fst g)) /\
    snd (fst (fst (gone_run lv mx no cap pre ((e, hj) :: r) nm j o))) = snd (fst (fst g)) /\
    snd (fst (gone_run lv mx no cap pre ((e, hj) :: r) nm j o)) = s :: snd (fst g) /\
    fst (snd (gone_run lv mx no cap pre ((e, hj) :: r) nm j o)) = fst (snd g).
Proof.
  do 7 eexists. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  cbn [gone_run]. destruct (gone_run _ _ _ _ _ r _ _ _) as [[[t c] ss] [o' das]]. cbn [fst snd].
  repeat split; reflexivity.
Qed.

Lemma gone_mono ps : forall lv mx no cap pre nm j o,
  Forall (fun p => re_eof (fst p) = 0 -> drain3 (fst p) (fst (snd p))) ps -> 0 <= mx -> 0 <= cap ->
  cap <= snd (fst (fst (gone_run lv mx no cap pre ps nm j o))).
Proof.
  induction ps as [|[e hj] ps IH]; intros lv mx no cap pre nm j o HD Hm Hc; [cbn; lia|].
  apply Forall_cons_iff in HD as [Hd HD]. cbn [fst snd] in Hd.
  destruct (gone_run_cons lv mx no cap pre e hj ps nm j o)
    as (s & a0 & td & a & xks & k & g & Es & _ & _ & _ & _ & Ek & Eg & _ & T2 & _ & _).
  rewrite T2.
  assert (Ho : cap <= ds_ocap s).
  { rewrite Es. unfold after_drain. destruct (Z.eqb_spec (re_eof e) 0) as [E|E].
    - exact (proj1 (Hd E lv mx no cap Hm Hc)).
    - cbn. lia. }
  assert (Hk : ds_ocap s <= fst (snd k)) by (rewrite Ek; apply ke_mono; lia).
  assert (Hg : fst (snd k) <= snd (fst (fst g))) by (rewrite Eg; apply IH; [exact HD|exact Hm|lia]).
  lia.
Qed.

Lemma cred_nonneg h c : 0 <= cred h c.
Proof. unfold cred. apply zsum_nonneg. intros x _. pose proof (rec_cred_ge c x). lia. Qed.

Lemma credb_nonneg h : 0 <= credb h.
Proof. unfold credb. apply zsum_nonneg. intros x _. pose proof (rec_credb_ge x). unfold WILD_B, LLIM in *. lia. Qed.

Lemma dchain_le3 e h s c : dchain e h s c <= 3.
Proof.
  unfold dchain. pose proof (ncb_b (ds_cap s) c). pose proof (ncb_b (re_cap e) c). pose proof (ncb_b (ds_ka s) c).
  pose proof (ncb_b (ent_ka e) c). pose proof (ncb_b (16 * ds_ecap s) c).
  pose proof (ncb_b (16 * hl_cap (hs_expected h)) c). lia.
Qed.

Lemma gone_dem_nonneg ps c : 0 <= gone_dem ps c.
Proof.
  unfold gone_dem. apply zsum_nonneg. intros p _. destruct (re_eof (fst p) =? 0); [|lia].
  pose proof (cred_nonneg (fst (snd p)) c). lia.
Qed.

Lemma gone_cred_nonneg ps c : 0 <= gone_cred ps c.
Proof.
  unfold gone_cred. apply zsum_nonneg. intros p _. destruct (re_eof (fst p) =? 0); [apply cred_nonneg|lia].
Qed.

Lemma gone_credb_nonneg ps : 0 <= gone_credb ps.
Proof.
  unfold gone_credb. apply zsum_nonneg. intros p _. destruct (re_eof (fst p) =? 0); [apply credb_nonneg|lia].
Qed.

Lemma gone_dem_cons e hj ps c :
  gone_dem ((e, hj) :: ps) c = (if re_eof e =? 0 then 3 + cred (fst hj) c else 0) + gone_dem ps c.
Proof. unfold gone_dem. rewrite zsum_cons. reflexivity. Qed.

Lemma gone_cred_cons e hj ps c :
  gone_cred ((e, hj) :: ps) c = (if re_eof e =? 0 then cred (fst hj) c else 0) + gone_cred ps c.
Proof. unfold gone_cred. rewrite zsum_cons. reflexivity. Qed.

Lemma gone_credb_cons e hj ps :
  gone_credb ((e, hj) :: ps) = (if re_eof e =? 0 then credb (fst hj) else 0) + gone_credb ps.
Proof. unfold gone_credb. rewrite zsum_cons. reflexivity. Qed.

Lemma gone_dch_cons e hj ps s ss c :
  gone_dch ((e, hj) :: ps) (s :: ss) c = (if re_eof e =? 0 then dchain e (fst hj) s c else 0) + gone_dch ps ss c.
Proof. reflexivity. Qed.

Lemma gone_dchb_cons e hj ps s ss :
  gone_dchb ((e, hj) :: ps) (s :: ss) = (if re_eof e =? 0 then dchainb e (fst hj) s else 0) + gone_dchb ps ss.
Proof. reflexivity. Qed.

Lemma gslots_cons qs nm e hj ps : concat (map (gslots qs nm) ((e, hj) :: ps)) =
  (if re_eof e =? 0 then dslots qs e (fst hj) (drain_start nm adr0 e (fst hj)) else []) ++
  concat (map (gslots qs nm) ps).
Proof. reflexivity. Qed.

Lemma gres_cons e hj ps :
  list_sum (map gres ((e, hj) :: ps)) = Nat.add (if re_eof e =? 0 then dres e (fst hj) else 0%nat) (list_sum (map gres ps)).
Proof. reflexivity. Qed.

Lemma ekeys_nonneg ls : Forall (fun n => 0 <= n) (ekeys ls).
Proof.
  apply Forall_forall. intros x Hx. unfold ekeys in Hx. apply in_concat in Hx as (l0 & Hl0 & Hx).
  apply in_map_iff in Hl0 as (l & <- & _). unfold ekey_of in Hx.
  destruct (gesture l) as [[[|] y]|]; cbn in Hx; [|contradiction|contradiction].
  destruct Hx as [<-|[]]. lia.
Qed.

Lemma gone_ek_cons e hj ps : gone_ek ((e, hj) :: ps) =
  (if re_eof e =? 0 then ekeys (lines (hs_state (fst hj)) (bzs (pending_stream (fst hj)))) else []) ++ gone_ek ps.
Proof. reflexivity. Qed.

Lemma gone3 ps : forall lv mx no cap pre nm j o qs b b0 cap0 E EB EBB S r capF,
  Forall (fun p => re_eof (fst p) = 0 -> drain3 (fst p) (fst (snd p))) ps ->
  0 <= mx -> 0 <= cap -> 0 <= cap0 ->
  snd (fst (fst (gone_run lv mx no cap pre ps nm j o))) <= capF -> capF <= NMAX ->
  (forall c, 0 <= c < 49 -> znth c (p3_live b0) + E c + 1 + gone_dem ps c + DRAIN_HR <= znth c (p3_cap b0)) ->
  p3_bytes b0 + EBB + 2 * capF + (Z.of_nat (length ps) + 1) * DRAIN_B <= BMAX ->
  gc3 b0 cap0 E EB EBB (concat (map (gslots qs nm) ps) ++ S) (r + list_sum (map gres ps)) cap (resolveF qs o) b ->
  room3 qs b j (fst (fst (fst (gone_run lv mx no cap pre ps nm j o)))) /\
  exists S' ks, Forall (fun n => 0 <= n) ks /\
    (forall c, 0 <= c < 49 -> bcnt c ks + bcnt c (gone_ek ps) <= gone_cred ps c) /\
    zsum (fun n => n) ks + zsum (fun n => n) (gone_ek ps) <= gone_credb ps /\
    gc3 b0 cap0
      (fun c => E c + gone_dch ps (snd (fst (gone_run lv mx no cap pre ps nm j o))) c + bcnt c ks)
      (EB + gone_dchb ps (snd (fst (gone_run lv mx no cap pre ps nm j o))) + zsum (fun n => n) ks)
      (EBB + Z.of_nat (length ps) * DRAIN_B) S' r (snd (fst (fst (gone_run lv mx no cap pre ps nm j o))))
      (resolveF qs (fst (snd (gone_run lv mx no cap pre ps nm j o))))
      (run3 qs b j (fst (fst (fst (gone_run lv mx no cap pre ps nm j o))))).
Proof.
  induction ps as [|[e hj] ps IH];
    intros lv mx no cap pre nm j o qs b b0 cap0 E EB EBB S r capF HD Hm Hc Hc0 Hf HN R1 R2 HG.
  - cbn [gone_run fst snd] in *. split; [exact I|]. exists S, []. cbn [concat map app list_sum] in HG.
    rewrite Nat.add_0_r in HG. split; [constructor|]. split.
    { intros c _. unfold gone_ek, gone_cred, bcnt. cbn [map concat]. rewrite !zsum_nil. lia. }
    split.
    { unfold gone_ek, gone_credb. cbn [map concat]. rewrite !zsum_nil. lia. }
    eapply gc3_mono; [| | |exact HG].
    + intros c _. cbv beta. cbn [gone_dch]. unfold bcnt. rewrite zsum_nil. lia.
    + cbn [gone_dchb]. rewrite zsum_nil. lia.
    + cbn [length]. lia.
  - pose proof (gone_mono ((e, hj) :: ps) lv mx no cap pre nm j o HD Hm Hc) as Mc.
    apply Forall_cons_iff in HD as [Hd HD]. cbn [fst snd] in Hd.
    destruct (gone_run_cons lv mx no cap pre e hj ps nm j o)
      as (s & a0 & td & a & xks & k & g & Es & Ea0 & Etd & Ea & Ex & Ek & Eg & T1 & T2 & T3 & T4).
    subst a0. rewrite T2 in Hf, Mc. rewrite T1, T2, T3, T4.
    rewrite gslots_cons, gres_cons, <- app_assoc in HG.
    assert (E3 : DRAIN_B = 1099511627776) by reflexivity.
    assert (HX : Forall (fun x => 0 <= fst x) xks).
    { rewrite Ex. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (y & <- & _). cbn [fst]. lia. }
    cbn [length] in R2.
    destruct (Z.eqb_spec (re_eof e) 0) as [Ee|Ee].
    +
      assert (Ee' : (re_eof e =? 0) = true) by (apply Z.eqb_eq; exact Ee).
      try rewrite Ee' in Etd; try rewrite Ee' in HG. cbv iota in Etd, HG.
      assert (Es' : s = drain_fin lv mx no cap e (fst hj)) by (rewrite Es; unfold after_drain; rewrite Ee'; reflexivity).
      assert (Ea' : a = drain_adr lv mx no cap e (fst hj) j (drain_start nm o e (fst hj)))
        by (rewrite Ea; unfold after_drain_adr; rewrite Ee'; reflexivity).
      specialize (Hd Ee lv mx no cap Hm Hc). cbv zeta in Hd. destruct Hd as [Hmo Hd]. rewrite <- Es' in Hmo.
      destruct HG as (HP & HC & HM & HL & HB1 & HB2 & HS).
      assert (P2 : forall c, 0 <= c < 49 -> znth c (p3_live b) + cred (fst hj) c + DRAIN_HR <= znth c (p3_cap b)).
      { intros c Hc'. pose proof (HL c Hc') as L1. pose proof (R1 c Hc') as R. rewrite gone_dem_cons, Ee' in R.
        cbv iota in R. pose proof (gone_dem_nonneg ps c). pose proof (ncb_b cap c). pose proof (ncb_b cap0 c).
        rewrite HC. lia. }
      assert (H0k : ds_ocap s <= fst (snd k)) by (rewrite Ek; apply ke_mono; lia).
      assert (Hkg : fst (snd k) <= snd (fst (fst g))) by (rewrite Eg; apply gone_mono; [exact HD|exact Hm|lia]).
      assert (P5 : ds_ocap (drain_fin lv mx no cap e (fst hj)) <= NMAX) by (rewrite <- Es'; lia).
      assert (P3 : p3_bytes b - cap + 2 * ds_ocap (drain_fin lv mx no cap e (fst hj)) + DRAIN_B <= BMAX)
        by (rewrite <- Es'; rewrite E3 in *; lia).
      assert (P4 : misT (slot3 cap (resolveF qs (da_out (drain_start nm o e (fst hj)))) ++
                         dslots qs e (fst hj) (drain_start nm o e (fst hj)) ++ (concat (map (gslots qs nm) ps) ++ S))
                        ((r + list_sum (map gres ps)) + res3 cap + dres e (fst hj)) (p3_mis b)).
      { eapply misT_r; [|exact HS]. lia. }
      destruct (Hd qs b j (drain_start nm o e (fst hj)) (concat (map (gslots qs nm) ps) ++ S)
                  (r + list_sum (map gres ps))%nat HP P5 P2 P3 P4)
        as (Rd & Pd & Cd & Md & (dks & Hk0 & Ld & Bd1 & Hkc & Hkb) & Bd2 & D & SD).
      assert (Hkd : forall c, 0 <= c < 49 -> bcnt c dks <= cred (fst hj) c).
      { intros c Hc'. pose proof (Hkc c Hc').
        pose proof (bcnt_nonneg c (ekeys (lines (hs_state (fst hj)) (bzs (pending_stream (fst hj)))))). lia. }
      rewrite <- Es', <- Ea', <- Etd in *.
      assert (G1 : gc3 b0 cap0 (fun c => E c + dchain e (fst hj) s c + bcnt c dks)
                     (EB + dchainb e (fst hj) s + zsum (fun n => n) dks) (EBB + DRAIN_B)
                     (D ++ concat (map (gslots qs nm) ps) ++ S)
                     (r + list_sum (map gres ps)) (ds_ocap s) (resolveF qs (da_out a)) (run3 qs b j td)).
      { split; [exact Pd|]. split; [congruence|]. split; [congruence|].
        split; [intros c Hc'; cbv beta; pose proof (HL c Hc'); pose proof (Ld c Hc'); lia|].
        split; [lia|]. split; [lia|]. exact SD. }
      assert (RCk : rc3 b0 cap0 (fun c => E c + dchain e (fst hj) s c + bcnt c dks) (EBB + DRAIN_B) capF).
      { split; [|split; [rewrite E3 in *; lia|exact HN]].
        intros c Hc'. cbv beta. pose proof (R1 c Hc') as R. rewrite gone_dem_cons, Ee' in R. cbv iota in R.
        pose proof (gone_dem_nonneg ps c). pose proof (ncb_b cap0 c). pose proof (dchain_le3 e (fst hj) s c).
        pose proof (Hkd c Hc'). unfold DRAIN_HR in *. lia. }
      pose proof (ke3 xks lv mx (ds_no s) (ds_ocap s) (j + nretF td) (da_out a) qs (run3 qs b j td) b0 cap0 _ _ _
                    (D ++ concat (map (gslots qs nm) ps) ++ S) (r + list_sum (map gres ps))%nat capF HX
                    ltac:(lia) ltac:(rewrite <- Ek; lia) RCk G1) as KE.
      rewrite <- Ek in KE. destruct KE as [Rk Gk].
      pose proof (gc3_perm _ _ _ _ _ _ _ _ _ _ _ (Permutation_app_swap_app D (concat (map (gslots qs nm) ps)) S) Gk) as G2.
      rewrite Eg in Hf.
      assert (R1' : forall c, 0 <= c < 49 ->
                znth c (p3_live b0) + (E c + dchain e (fst hj) s c + bcnt c dks) + 1 + gone_dem ps c + DRAIN_HR <=
                znth c (p3_cap b0)).
      { intros c Hc'. pose proof (R1 c Hc') as R. rewrite gone_dem_cons, Ee' in R. cbv iota in R.
        pose proof (dchain_le3 e (fst hj) s c). pose proof (Hkd c Hc'). lia. }
      assert (R2' : p3_bytes b0 + (EBB + DRAIN_B) + 2 * capF + (Z.of_nat (length ps) + 1) * DRAIN_B <= BMAX)
        by (rewrite E3 in *; lia).
      destruct (IH lv mx _ (fst (snd k)) pre nm _ _ qs _ b0 cap0 _ _ _ (D ++ S) r capF HD Hm ltac:(lia) Hc0 Hf HN R1' R2' G2)
        as [Rg HS'].
      rewrite <- Eg in Rg, HS'. destruct HS' as (S' & ks & Hks & Hkc' & Hkb' & Gg).
      split.
      * rewrite room3_app. split; [exact Rd|]. rewrite room3_app. split; [exact Rk|exact Rg].
      * exists S', (dks ++ ks). split; [apply Forall_app; split; assumption|].
        split.
        { intros c Hc'. rewrite gone_ek_cons, Ee', gone_cred_cons, Ee'. cbv iota. rewrite !bcnt_app.
          pose proof (Hkc c Hc'). pose proof (Hkc' c Hc'). lia. }
        split.
        { rewrite gone_ek_cons, Ee', gone_credb_cons, Ee'. cbv iota. rewrite !zsum_app. lia. }
        rewrite !run3_app. eapply gc3_mono; [| | |exact Gg].
        -- intros c _. cbv beta. rewrite gone_dch_cons, Ee', bcnt_app. cbv iota. lia.
        -- rewrite gone_dchb_cons, Ee', zsum_app. cbv iota. lia.
        -- cbn [length]. rewrite E3. lia.
    +
      assert (Ee' : (re_eof e =? 0) = false) by (apply Z.eqb_neq; exact Ee).
      try rewrite Ee' in Etd; try rewrite Ee' in HG. cbv iota in Etd, HG.
      assert (Es' : s = drain_init no cap e (fst hj)) by (rewrite Es; unfold after_drain; rewrite Ee'; reflexivity).
      assert (Ea' : a = drain_start nm o e (fst hj)) by (rewrite Ea; unfold after_drain_adr; rewrite Ee'; reflexivity).
      clear Es Ea. subst s a td.
      assert (H0k : cap <= fst (snd k)) by (rewrite Ek; apply ke_mono; exact Hc).
      assert (Hkg : fst (snd k) <= snd (fst (fst g))) by (rewrite Eg; apply gone_mono; [exact HD|exact Hm|lia]).
      assert (RCk : rc3 b0 cap0 E EBB capF).
      { split; [|split; [rewrite E3 in *; lia|exact HN]].
        intros c Hc'. pose proof (R1 c Hc') as R. rewrite gone_dem_cons, Ee' in R. cbv iota in R.
        pose proof (gone_dem_nonneg ps c). pose proof (ncb_b cap0 c). unfold DRAIN_HR in *. lia. }
      pose proof (ke3 xks lv mx (ds_no (drain_init no cap e (fst hj))) (ds_ocap (drain_init no cap e (fst hj)))
                    (j + nretF []) (da_out (drain_start nm o e (fst hj))) qs (run3 qs b j []) b0 cap0 E EB EBB
                    (concat (map (gslots qs nm) ps) ++ S) (r + list_sum (map gres ps))%nat capF HX
                    Hc ltac:(rewrite <- Ek; lia) RCk HG) as KE.
      rewrite <- Ek in KE. destruct KE as [Rk Gk].
      rewrite Eg in Hf.
      assert (R1' : forall c, 0 <= c < 49 ->
                znth c (p3_live b0) + E c + 1 + gone_dem ps c + DRAIN_HR <= znth c (p3_cap b0)).
      { intros c Hc'. pose proof (R1 c Hc') as R. rewrite gone_dem_cons, Ee' in R. cbv iota in R. lia. }
      assert (R2' : p3_bytes b0 + EBB + 2 * capF + (Z.of_nat (length ps) + 1) * DRAIN_B <= BMAX)
        by (rewrite E3 in *; lia).
      destruct (IH lv mx _ (fst (snd k)) pre nm _ _ qs _ b0 cap0 E EB EBB S r capF HD Hm ltac:(lia) Hc0 Hf HN R1' R2' Gk)
        as [Rg HS'].
      rewrite <- Eg in Rg, HS'. destruct HS' as (S' & ks & Hks & Hkc' & Hkb' & Gg).
      split.
      * rewrite room3_app. split; [exact I|]. rewrite room3_app. split; [exact Rk|exact Rg].
      * exists S', ks. split; [exact Hks|].
        split.
        { intros c Hc'. rewrite gone_ek_cons, Ee', gone_cred_cons, Ee'. cbv iota. cbn [app].
          pose proof (Hkc' c Hc'). lia. }
        split.
        { rewrite gone_ek_cons, Ee', gone_credb_cons, Ee'. cbv iota. cbn [app]. lia. }
        rewrite !run3_app. eapply gc3_mono; [| | |exact Gg].
        -- intros c _. cbv beta. rewrite gone_dch_cons, Ee'. cbv iota. lia.
        -- rewrite gone_dchb_cons, Ee'. cbv iota. lia.
        -- cbn [length]. rewrite E3. lia.
Qed.

Theorem gone_effect3 : gone_effect3_stmt.
Proof.
  intros lv mx NO CAP pre es hs nm o qs b F r. cbv zeta. intros HD Hm Hc HN HP R1 R2 HS.
  assert (G0 : gc3 b CAP (fun _ => 0) 0 0 (concat (map (gslots qs nm) (combine es hs)) ++ F)
                 (r + list_sum (map gres (combine es hs))) CAP (resolveF qs o) b).
  { split; [exact HP|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros c _; lia|].
    split; [lia|]. split; [lia|]. eapply misT_r; [|exact HS]. lia. }
  destruct (gone3 (combine es hs) lv mx NO CAP pre nm 0 o qs b b CAP (fun _ => 0) 0 0 F r
              (gone_capT lv mx NO CAP pre es hs nm 0 o) HD Hm Hc Hc (Z.le_refl _) HN
              ltac:(intros c Hc'; cbv beta; pose proof (R1 c Hc'); lia) ltac:(lia) G0)
    as [Hr (S' & ks & Hks & Hkc & Hkb & HP' & HC' & HM' & HL' & HB' & _ & HS')].
  rewrite runF3, roomF3. unfold relay_instance_gone_tr.
  split; [exact Hr|]. split; [exact HP'|]. split; [exact HC'|]. split; [exact HM'|].
  pose proof (zsum_id_nonneg _ Hks) as Z0.
  split.
  { intros c Hc'. pose proof (HL' c Hc') as L1. cbv beta in L1. pose proof (Hkc c Hc').
    unfold gone_dl, gone_da, gone_capT, gone_ssT. lia. }
  split; [unfold gone_db, gone_dab, gone_capT, gone_ssT; lia|].
  split; [intros c Hc'; pose proof (Hkc c Hc'); pose proof (bcnt_nonneg c ks); unfold gone_da; lia|].
  split; [unfold gone_dab; lia|].
  exists S'. exact HS'.
Qed.

Lemma ledger3_pk3 NW pl k V L A b al alb : RI3_ledger NW pl k V L A b al alb -> pk3_ok b.
Proof.
  intros (HC & HM & _ & HlL & _). split; [exact HlL|]. rewrite HC, HM. split; [apply CS_reply_capok3|].
  intros c Hc. rewrite MC_reply_at by exact Hc. lia.
Qed.

Lemma ledger3_slack NW pl k V L A b al alb c : RI3_ledger NW pl k V L A b al alb -> 0 <= c < 49 ->
  znth c (p3_live b) + prom_c (rv_pend V) c + 103 <= znth c (p3_cap b).
Proof.
  intros (HC & _ & HN & _ & _ & _ & _ & _ & _ & _ & _ & _ & H) Hc. destruct (H c Hc) as (H1 & H2 & H3).
  pose proof (cons_le pl k c). pose proof (nc_cnt_bounds V L A c). pose proof (ek_c_nonneg V c).
  assert (Z.of_nat (length (rv_nc V)) <= 26) by (unfold NC_MAX in HN; lia).
  rewrite HC, CS_reply_at by exact Hc. unfold cs_band. destruct (Z.eqb_spec c 0) as [E|E]; cbv beta iota.
  - subst c. pose proof (x0_bound pl). unfold CAPS0, RI_BASE, BTEXT in *. lia.
  - unfold CBASE, RI_BASE in *. lia.
Qed.

Lemma gone_cred_le es hs c : gone_cred (combine es hs) c <= prom_c (pend_view hs) c.
Proof.
  unfold prom_c, pend_view. rewrite zsum_map. revert hs. induction es as [|e es IH]; intros hs; destruct hs as [|p hs];
    cbn [combine]; unfold gone_cred in *; rewrite ?zsum_nil.
  - lia.
  - apply zsum_nonneg. intros x _. exact (cred_nonneg (fst x) c).
  - lia.
  - rewrite !zsum_cons. cbn [fst snd]. pose proof (IH hs). pose proof (cred_nonneg (fst p) c).
    destruct (re_eof e =? 0); cbv iota; unfold cred in *; lia.
Qed.

Lemma gone_dem_le ps c : gone_dem ps c <= 3 * Z.of_nat (length ps) + gone_cred ps c.
Proof.
  induction ps as [|p ps IH]; [unfold gone_dem, gone_cred; rewrite !zsum_nil; cbn [length]; lia|].
  unfold gone_dem, gone_cred in *. rewrite !zsum_cons. cbn [length]. destruct (re_eof (fst p) =? 0); lia.
Qed.

Lemma combine_len_le {X Y : Type} (l : list X) (l' : list Y) : (length (combine l l') <= length l)%nat.
Proof. revert l'. induction l as [|x l IH]; intros [|y l']; cbn [combine length]; try lia. specialize (IH l'). lia. Qed.

Lemma gone_pre3 NW pl k L A b al alb G OUT es hs lv mx NO CAP pre F qs :
  RI3_ledger NW pl k (view_of G OUT es hs) L A b al alb -> (length es <= 4)%nat ->
  gone_capT lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT) <= NMAX ->
  misT (slot3 CAP (sptr_of L A OUT) ++ concat (map (gslots [] (known_at L A)) (combine es hs)) ++ F)
    (res3 CAP + list_sum (map gres (combine es hs))) (p3_mis b) ->
  pk3_ok b /\
  (forall c, 0 <= c < 49 -> znth c (p3_live b) + 1 + gone_dem (combine es hs) c + DRAIN_HR <= znth c (p3_cap b)) /\
  p3_bytes b + 2 * gone_capT lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT) +
    (Z.of_nat (length (combine es hs)) + 1) * DRAIN_B <= BMAX /\
  misT (slot3 CAP (resolveF qs (known_at L A OUT)) ++ concat (map (gslots qs (known_at L A)) (combine es hs)) ++ F)
    (0 + res3 CAP + list_sum (map gres (combine es hs))) (p3_mis b).
Proof.
  intros HL Hes HN HS. pose proof (combine_len_le es hs) as LP.
  split; [exact (ledger3_pk3 _ _ _ _ _ _ _ _ _ HL)|]. split.
  - intros c Hc. pose proof (ledger3_slack _ _ _ _ _ _ _ _ _ c HL Hc) as SL. cbn [view_of rv_pend] in SL.
    pose proof (gone_cred_le es hs c). pose proof (gone_dem_le (combine es hs) c). unfold DRAIN_HR. lia.
  - split.
    + pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL) as HB. rewrite PB3_MAX_val in HB.
      assert (E1 : BMAX = 17592186044416) by reflexivity. assert (E2 : NMAX = 536879104) by reflexivity.
      assert (E3 : DRAIN_B = 1099511627776) by reflexivity. rewrite E1, E3. rewrite E2 in HN. lia.
    + eapply misT_r; [|exact HS]. lia.
Qed.

Lemma ledger3_call3 NW pl k V L A b al alb k' V' L' A' b' dl db da dab :
  RI3_ledger NW pl k V L A b al alb -> call_step3 NW pl k' V L A V' L' A' al alb dl db da dab ->
  (forall c, 0 <= c < 49 -> 0 <= da c) -> 0 <= dab ->
  p3_cap b' = p3_cap b -> p3_mcap b' = p3_mcap b -> length (p3_live b') = 49%nat ->
  (forall c, 0 <= c < 49 -> znth c (p3_live b') <= znth c (p3_live b) + dl c + da c) ->
  p3_bytes b' <= p3_bytes b + db + dab -> mis_nc V' L' (p3_mis b') ->
  RI3_ledger NW pl k' V' L' A' b' (map (fun c => znth c al + da c) (zseq 0 49)) (alb + dab).
Proof.
  intros (HC & HM & HN & HlL & HL & Ha & HE & HB & HW1 & HW2 & HP & HMis & H)
    (HN' & HC' & HB' & HW1' & HW2' & HP' & HQ' & HE') Hda Hdab Hcap Hmc Hl Hlive Hby HMis'.
  assert (AL : forall c, 0 <= c < 49 -> znth c (map (fun c => znth c al + da c) (zseq 0 49)) = znth c al + da c).
  { intros c Hc. apply (znth_map_zseq (fun c => znth c al + da c)). exact Hc. }
  assert (AS : alsum (map (fun c => znth c al + da c) (zseq 0 49)) = alsum al + zsumZ da (zseq 0 49)).
  { unfold alsum. rewrite <- zsumZ_add. apply zsumZ_ext. intros c Hc. apply In_zseq in Hc. cbv beta. apply AL. lia. }
  split; [rewrite Hcap; exact HC|]. split; [rewrite Hmc; exact HM|]. split; [exact HN'|]. split; [exact Hl|].
  split; [unfold zseq; rewrite !length_map, length_seq; reflexivity|]. split; [lia|]. split; [exact HE'|].
  split; [lia|]. split; [exact HW1'|]. split; [rewrite AS; exact HW2'|]. split; [lia|]. split; [exact HMis'|].
  intros c Hc. rewrite (AL c Hc). destruct (H c Hc) as (H1 & H2 & H3). pose proof (Hlive c Hc). pose proof (HC' c Hc).
  pose proof (HP' c Hc). pose proof (Hda c Hc). lia.
Qed.

Lemma bcnt_sum ks : Forall (fun n => 0 <= n) ks -> zsumZ (fun c => bcnt c ks) (zseq 0 49) = zlen ks.
Proof.
  induction ks as [|n ks IH]; intros Hks; [reflexivity|]. apply Forall_cons_iff in Hks as [Hn Hks].
  rewrite (zsumZ_ext _ (fun c => one_if c (band n) + bcnt c ks)) by (intros c _; apply bcnt_cons).
  rewrite zsumZ_add, one_if_sum by (apply band_range; exact Hn). rewrite (IH Hks). unfold zlen. cbn [length]. lia.
Qed.

Lemma call_step_3 NW pl k' V L A V' L' A' al alb ks dl db : Forall (fun n => 0 <= n) ks ->
  call_step NW pl k' V L A V' L' A' al alb ks dl db ->
  call_step3 NW pl k' V L A V' L' A' al alb dl db (fun c => bcnt c ks) (zsum (fun n => n) ks).
Proof.
  intros Hks (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [exact H4|]. split; [rewrite (bcnt_sum ks Hks); exact H5|]. split; [exact H6|]. split; [exact H7|exact H8].
Qed.

Theorem gone_room3 : gone_room3_stmt.
Proof.
  intros NW pl k L A b al alb G OUT es hs lv mx NO CAP pre F. cbv zeta. intros HL HD Hes Hm Hc HN HS qs _.
  destruct (gone_pre3 NW pl k L A b al alb G OUT es hs lv mx NO CAP pre F qs HL Hes HN HS) as (P1 & P2 & P3 & P4).
  pose proof (gone_effect3 lv mx NO CAP pre es hs (known_at L A) (known_at L A OUT) qs b F 0%nat) as GE. cbv zeta in GE.
  exact (proj1 (GE HD Hm Hc HN P1 P2 P3 P4)).
Qed.

Theorem gone_ledger3 : gone_ledger3_stmt.
Proof.
  intros NW pl k k' L A L' A' V' b al alb G OUT es hs lv mx NO CAP pre F qs. cbv zeta.
  intros HL HD Hes Hm Hc HN HS Hstep Hmis.
  destruct (gone_pre3 NW pl k L A b al alb G OUT es hs lv mx NO CAP pre F qs HL Hes HN HS) as (P1 & P2 & P3 & P4).
  pose proof (gone_effect3 lv mx NO CAP pre es hs (known_at L A) (known_at L A OUT) qs b F 0%nat) as GE. cbv zeta in GE.
  destruct (GE HD Hm Hc HN P1 P2 P3 P4) as (_ & (Hl' & _) & HC' & HM' & HLv & HB & Hda & Hdab & _).
  exists (map (fun c => znth c al + gone_da es hs c) (zseq 0 49)), (alb + gone_dab es hs).
  apply (ledger3_call3 NW pl k _ L A b al alb k' V' L' A' _ _ _ _ _ HL Hstep).
  - exact Hda.
  - exact Hdab.
  - exact HC'.
  - exact HM'.
  - exact Hl'.
  - exact HLv.
  - exact HB.
  - exact Hmis.
Qed.

Theorem gone_ri3 : gone_ri3_stmt.
Proof.
  intros E k k' L A L' A' V' b al alb G OUT es hs lv mx NO CAP pre F qs. cbv zeta.
  intros HL HD Hes Hm Hc HN HS HA Hstep Hmis.
  destruct (gone_ledger3 rv_wt (ss_pl E) k k' L A L' A' V' b al alb G OUT es hs lv mx NO CAP pre F qs HL HD Hes Hm Hc HN HS
              Hstep Hmis) as (al' & alb' & HL').
  hnf. exists (runF pack3_form qs b (relay_instance_gone_tr lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT))).
  exists al', alb'. split; [exact HA|exact HL'].
Qed.

Lemma grow_cap_i cap used j b j' b' : fst (snd (grow_tr cap used j b)) = fst (snd (grow_tr cap used j' b')).
Proof. unfold grow_tr. destruct (cap - used <? 4096); reflexivity. Qed.

Lemma pushes_cap_i ls : forall n cap j v rs j' v' rs',
  snd (fst (pushes_run n cap ls j v rs)) = snd (fst (pushes_run n cap ls j' v' rs')).
Proof. induction ls as [|l ls IH]; intros n cap j v rs j' v' rs'; cbn [pushes_run fst snd]; [reflexivity|apply IH]. Qed.

Lemma seen_ka_i H ka l j ha ks j' ha' ks' : snd (fst (seen_tr H ka l j ha ks)) = snd (fst (seen_tr H ka l j' ha' ks')).
Proof.
  unfold seen_tr. destruct (gesture l) as [[[|] x]|]; [destruct (index_of x H)|destruct (index_of x H)|]; reflexivity.
Qed.

Lemma set_nth_len {X : Type} n (y : X) l : length (set_nth n y l) = length l.
Proof. revert n. induction l as [|x l IH]; intros [|n]; cbn [set_nth length]; [reflexivity|reflexivity|reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma swap_remove_len {X : Type} (d : X) n l : length (swap_remove d n l) = (length l - 1)%nat.
Proof. unfold swap_remove. rewrite length_firstn, set_nth_len. lia. Qed.

Lemma seen_len H ka l j ha ks : length ks = length H ->
  length (snd (snd (seen_tr H ka l j ha ks))) = length (seen_arr H l).
Proof.
  intros Hl. unfold seen_tr, seen_arr. destruct (gesture l) as [[[|] x]|];
    [destruct (index_of x H)|destruct (index_of x H)|]; cbn [snd fst]; rewrite ?length_app, ?swap_remove_len;
    cbn [length]; lia.
Qed.

Lemma lines_state_i ls : forall live mx no cap H ka j o ha ks j' o' ha' ks',
  snd (fst (lines_run live mx no cap H ka ls j o ha ks)) = snd (fst (lines_run live mx no cap H ka ls j' o' ha' ks')).
Proof.
  induction ls as [|l ls IH]; intros live mx no cap H ka j o ha ks j' o' ha' ks'; cbn [lines_run fst snd]; [reflexivity|].
  rewrite (seen_ka_i H ka l _ ha ks 0 adr0 []), (seen_ka_i H ka l _ ha' ks' 0 adr0 []). apply IH.
Qed.

Lemma lines_keys_len ls : forall live mx no cap H ka j o ha ks, length ks = length H ->
  length (snd (snd (lines_run live mx no cap H ka ls j o ha ks))) =
  length (snd (fst (snd (fst (lines_run live mx no cap H ka ls j o ha ks))))).
Proof.
  induction ls as [|l ls IH]; intros live mx no cap H ka j o ha ks Hl; cbn [lines_run fst snd]; [exact Hl|].
  apply IH. apply seen_len. exact Hl.
Qed.

Lemma drain_state_i f : forall live mx s j a j' a',
  fst (snd (drain_run f live mx s j a)) = fst (snd (drain_run f live mx s j' a')).
Proof.
  induction f as [|f IH]; intros live mx s j a j' a'; [reflexivity|]. cbn [drain_run].
  rewrite (grow_cap_i _ _ j (da_buf a) 0 adr0), (grow_cap_i _ _ j' (da_buf a') 0 adr0).
  destruct (ds_eintr s); [cbn [fst snd]; apply IH|].
  destruct (ds_pend s) as [|r0 rs]; [reflexivity|].
  match goal with |- context [if ?c <=? 0 then _ else _] => destruct (c <=? 0) end; [reflexivity|].
  rewrite (pushes_cap_i _ _ _ _ (da_ev a) (da_erecs a) 0 adr0 []), (pushes_cap_i _ _ _ _ (da_ev a') (da_erecs a') 0 adr0 []).
  match goal with |- context [chunk ?x ?y ?z] => destruct (chunk x y z) as [[u' sk'] rl] end.
  rewrite (lines_state_i _ _ _ _ _ _ _ _ (da_out a) (da_hp a) (da_keys a) 0 adr0 adr0 []),
    (lines_state_i _ _ _ _ _ _ _ _ (da_out a') (da_hp a') (da_keys a') 0 adr0 adr0 []).
  match goal with |- context [snd (fst (lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 0 adr0 adr0 []))] =>
    destruct (snd (fst (lines_run a1 a2 a3 a4 a5 a6 a7 0 adr0 adr0 []))) as [[oc' H'] ka'] end.
  match goal with |- context [snd (lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 (da_out a) ?a9 ?a10)] =>
    destruct (snd (lines_run a1 a2 a3 a4 a5 a6 a7 a8 (da_out a) a9 a10)) as [[o1 h1] k1] end.
  match goal with |- context [snd (lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 (da_out a') ?a9 ?a10)] =>
    destruct (snd (lines_run a1 a2 a3 a4 a5 a6 a7 a8 (da_out a') a9 a10)) as [[o2 h2] k2] end.
  cbn [fst snd]. apply IH.
Qed.

Lemma drain_keys_len f : forall live mx s j a, length (da_keys a) = length (ds_H s) ->
  length (da_keys (snd (snd (drain_run f live mx s j a)))) = length (ds_H (fst (snd (drain_run f live mx s j a)))).
Proof.
  induction f as [|f IH]; intros live mx s j a Hl; [exact Hl|]. cbn [drain_run].
  destruct (ds_eintr s); [cbn [fst snd]; apply IH; exact Hl|].
  destruct (ds_pend s) as [|r0 rs]; [exact Hl|].
  match goal with |- context [if ?c <=? 0 then _ else _] => destruct (c <=? 0) end; [exact Hl|].
  match goal with |- context [chunk ?x ?y ?z] => destruct (chunk x y z) as [[u' sk'] rl] end.
  match goal with |- context [lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11] =>
    pose proof (lines_keys_len a7 a1 a2 a3 a4 a5 a6 a8 a9 a10 a11 Hl) as LK; revert LK;
    destruct (lines_run a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) as [[t [[oc' H'] ka']] [[o' ha'] ks']] end.
  intros LK. cbn [fst snd] in *. apply IH. exact LK.
Qed.

Lemma after_keys_len lv mx no cap e h j nm o :
  length (da_keys (after_drain_adr lv mx no cap e h j (drain_start nm o e h))) = length (ds_H (after_drain lv mx no cap e h)).
Proof.
  unfold after_drain_adr, after_drain. destruct (re_eof e =? 0).
  - unfold drain_adr, drain_fin, drain_go.
    rewrite (drain_state_i _ lv mx (drain_init no cap e h) 0 dadr0 j (drain_start nm o e h)).
    apply drain_keys_len. cbn [drain_start da_keys drain_init ds_H]. unfold keys_texts. rewrite !length_map. reflexivity.
  - cbn [drain_start da_keys drain_init ds_H]. unfold keys_texts. rewrite !length_map. reflexivity.
Qed.

Lemma combine_fst {X Y : Type} (K : list X) (A : list Y) : length A = length K -> map fst (combine K A) = K.
Proof.
  revert A. induction K as [|x K IH]; intros [|y A] HL; cbn [combine map length fst] in *; try lia; [reflexivity|].
  f_equal. apply IH. lia.
Qed.

Lemma map_firstn' {X Y : Type} (f : X -> Y) k l : map f (firstn k l) = firstn k (map f l).
Proof. revert k. induction l as [|x l IH]; intros [|k]; cbn [firstn map]; [reflexivity|reflexivity|reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma map_set_nth {X Y : Type} (f : X -> Y) n y l : map f (set_nth n y l) = set_nth n (f y) (map f l).
Proof. revert n. induction l as [|x l IH]; intros [|n]; cbn [set_nth map]; [reflexivity|reflexivity|reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma map_last' {X Y : Type} (f : X -> Y) l d : f (last l d) = last (map f l) (f d).
Proof. induction l as [|x [|y l] IH]; [reflexivity|reflexivity|]. exact IH. Qed.

Lemma map_swap_remove {X Y : Type} (f : X -> Y) d n l : map f (swap_remove d n l) = swap_remove (f d) n (map f l).
Proof. unfold swap_remove. rewrite map_firstn', map_set_nth, length_map, <- map_last'. reflexivity. Qed.

Lemma geia_fst f : forall pre n (H1 H2 : list (list Z * adrF)), map fst H1 = map fst H2 ->
  map fst (fst (geia_loop f pre n H1)) = map fst (fst (geia_loop f pre n H2)).
Proof.
  induction f as [|f IH]; intros pre n H1 H2 HE; cbn [geia_loop]; [reflexivity|].
  assert (HL : length H1 = length H2) by (rewrite <- (length_map fst H1), <- (length_map fst H2), HE; reflexivity).
  assert (HN : fst (nth n H1 ([], adr0)) = fst (nth n H2 ([], adr0))).
  { rewrite <- !(map_nth fst). rewrite HE. reflexivity. }
  rewrite HL, HN. destruct (Nat.ltb n (length H2)); [|reflexivity].
  destruct (has_prefix pre (fst (nth n H2 ([], adr0)))); [|apply IH; exact HE].
  assert (HS : map fst (swap_remove ([], adr0) n H1) = map fst (swap_remove ([], adr0) n H2))
    by (rewrite !map_swap_remove, HE; reflexivity).
  pose proof (IH pre n _ _ HS) as R. revert R.
  destruct (geia_loop f pre n (swap_remove ([], adr0) n H1)) as [E1 K1].
  destruct (geia_loop f pre n (swap_remove ([], adr0) n H2)) as [E2 K2]. intros R. cbn [fst map] in *. rewrite HN, R.
  reflexivity.
Qed.

Lemma xks_fst lv mx no cap e h pre j1 nm1 o1 j2 nm2 o2 :
  map fst (map (fun x => (Z.of_nat (length (fst x)), snd x))
    (fst (geia pre (combine (ds_H (after_drain lv mx no cap e h))
                            (da_keys (after_drain_adr lv mx no cap e h j1 (drain_start nm1 o1 e h))))))) =
  map fst (map (fun x => (Z.of_nat (length (fst x)), snd x))
    (fst (geia pre (combine (ds_H (after_drain lv mx no cap e h))
                            (da_keys (after_drain_adr lv mx no cap e h j2 (drain_start nm2 o2 e h))))))).
Proof.
  set (K := ds_H (after_drain lv mx no cap e h)).
  set (A1 := da_keys (after_drain_adr lv mx no cap e h j1 (drain_start nm1 o1 e h))).
  set (A2 := da_keys (after_drain_adr lv mx no cap e h j2 (drain_start nm2 o2 e h))).
  assert (E1 : map fst (combine K A1) = K) by (apply combine_fst; apply after_keys_len).
  assert (E2 : map fst (combine K A2) = K) by (apply combine_fst; apply after_keys_len).
  assert (HL : length (combine K A1) = length (combine K A2))
    by (rewrite <- (length_map fst (combine K A1)), <- (length_map fst (combine K A2)), E1, E2; reflexivity).
  unfold geia. rewrite HL.
  pose proof (geia_fst (length (combine K A2)) pre 0 (combine K A1) (combine K A2) ltac:(rewrite E1, E2; reflexivity)) as G.
  apply (f_equal (map (fun k : list Z => Z.of_nat (length k)))) in G. rewrite !map_map in G |- *. exact G.
Qed.

Lemma ke_capi xks1 : forall xks2 live mx no cap j1 o1 j2 o2, map fst xks1 = map fst xks2 ->
  fst (snd (keys_end_run live mx no cap xks1 j1 o1)) = fst (snd (keys_end_run live mx no cap xks2 j2 o2)).
Proof.
  induction xks1 as [|[xl ka] r IH]; intros [|[xl2 ka2] r2] live mx no cap j1 o1 j2 o2 HE; cbn [map fst] in HE;
    try discriminate; cbn [keys_end_run fst snd]; [reflexivity|].
  injection HE as <- HE. apply IH. exact HE.
Qed.

Lemma gone_indep ps : forall lv mx no cap pre nm1 j1 o1 nm2 j2 o2,
  snd (fst (fst (gone_run lv mx no cap pre ps nm1 j1 o1))) = snd (fst (fst (gone_run lv mx no cap pre ps nm2 j2 o2))) /\
  snd (fst (gone_run lv mx no cap pre ps nm1 j1 o1)) = snd (fst (gone_run lv mx no cap pre ps nm2 j2 o2)).
Proof.
  induction ps as [|[e hj] ps IH]; intros lv mx no cap pre nm1 j1 o1 nm2 j2 o2; [split; reflexivity|].
  destruct (gone_run_cons lv mx no cap pre e hj ps nm1 j1 o1)
    as (s1 & a01 & td1 & a1 & x1 & k1 & g1 & Es1 & Ea01 & Etd1 & Ea1 & Ex1 & Ek1 & Eg1 & _ & T21 & T31 & _).
  destruct (gone_run_cons lv mx no cap pre e hj ps nm2 j2 o2)
    as (s2 & a02 & td2 & a2 & x2 & k2 & g2 & Es2 & Ea02 & Etd2 & Ea2 & Ex2 & Ek2 & Eg2 & _ & T22 & T32 & _).
  rewrite T21, T31, T22, T32.
  assert (XE : map fst x1 = map fst x2) by (subst; apply xks_fst).
  subst s1 s2.
  assert (KE : fst (snd k1) = fst (snd k2)) by (rewrite Ek1, Ek2; apply ke_capi; exact XE).
  rewrite Eg1, Eg2, XE, KE. split.
  - exact (proj1 (IH _ _ _ _ _ _ _ _ _ _ _)).
  - f_equal. exact (proj2 (IH _ _ _ _ _ _ _ _ _ _ _)).
Qed.

Theorem gone_capT_eq lv mx NO CAP pre es hs nm j o :
  gone_capT lv mx NO CAP pre es hs nm j o = gone_cap lv mx NO CAP pre es hs.
Proof. unfold gone_capT, gone_cap. exact (proj1 (gone_indep _ _ _ _ _ _ _ _ _ _ _ _)). Qed.

Theorem gone_ssT_eq lv mx NO CAP pre es hs nm j o :
  gone_ssT lv mx NO CAP pre es hs nm j o = gone_states lv mx NO CAP pre es hs.
Proof. unfold gone_ssT, gone_states. exact (proj2 (gone_indep _ _ _ _ _ _ _ _ _ _ _ _)). Qed.
