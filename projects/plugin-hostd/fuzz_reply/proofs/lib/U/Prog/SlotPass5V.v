From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack AllocBound AllocPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement StatementKept
  send_line_c gesture_end_c relay_event_c RelayFrame RelayRunT RelayRunF ListTr RelayModel RelayKeys send_line_b_c
  gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep HarnessRep ListRep CheckRep drain_b_c
  relay_remove_b_c SlotInv SlotReads printf_facts_c snprintf_c relay_instance_gone_b_c RelayCap
  check_shape_done_c check_no_loss_c check_shape_ends_c SlotPass2Check SlotPass4C SlotPass5Run relay_remove_b_aux
  SlotPass5Check relay_instance_gone_b_lem SlotCaps3 SlotSteps SlotRes SlotRI3 SlotRun3 SlotP5R3G SlotP5Res3
  TrModel SlotPass5M SlotNcMove3 SlotNcWt.
Import ListNotations.
Local Open Scope Z_scope.

Definition p5c_hj (es : list rentry) (hj : list (hsrc * nat)) (hs' : list hsrc) : list (hsrc * nat) :=
  map (fun i => (g5_src (nth i es no_entry) (fst (nth i hj no_hj)) (nth i hs' (fst no_hj)), snd (nth i hj no_hj)))
    (seq 0 (length es)).

Definition p5v_ctx {rc : RunCeil} (Bm : malloc_syms) (API : AllocAPI Bm) (L : layout) (A : astate)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (t k G : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (cl br dd : Z) (mx nout cap out : word) (pre : list Z)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (OUT' CAP' : Z)
    (es' : list rentry) (hs' : list hsrc) (kss : list (list (list Z))) (qs : list sptr) : Prop :=
  let lv := send_live cl br dd 1 in
  let ss := gone_states lv (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj in
  let das := gone_adrs lv (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj
               (known_at L A) 0 (known_at L A (bv_unsigned out)) in
  let segsz := map (fun i => gone_segment pre (entry_lines (nth i es no_entry) (nth i hj no_hj)) (nth i kss []))
                   (seq 0 (length es)) in
  let TOT := Z.of_nat (length (concat segsz)) in
  let live := send_live cl br dd TOT in
  aa_MR API L A mem md /\ List.NoDup (map fst (blocks L A)) /\
  output_at Bm L A mem nout cap out /\ In (G, SRC_TABLE) (blocks L A) /\
  Forall (RelayRep.entry_ok Bm L A mem) es /\ Forall2 (pair_ok Bm L A mem t) es hj /\
  NoDup (target_addrs G (bv_unsigned out) es hj) /\ length hj = length es /\ (length es <= 4)%nat /\
  slot_cost es hj <= k /\ k < INPUT_MAX /\ 0 <= t < OPS_MAX /\ bv_unsigned nout = 0 /\
  (cl = 3 \/ cl = -1) /\ (br = 0 \/ br = 1) /\ (dd = 0 \/ dd = 1) /\
  relay_post Bm API RELAY_INSTANCE_GONE_K
    (fun a => send_writes true (bv_unsigned out) (bv_unsigned cap) a \/ G_LOCK + 4 <= a < G_LOCK + 8 \/
              G <= a < G + SRC_TABLE \/ drained_area es hj a \/
              (exists q m, In q (concat (map entry_blocks es) ++ drained_blocks es hj) /\
                           In (q, m) (blocks L A) /\ q <= a < q + m))
    (fun q => (live = true /\ q = bv_unsigned out) \/ In q (concat (map entry_blocks es)) \/
              In q (drained_blocks es hj))
    L A regs mem md L' A' regs' mem' md' /\
  length qs = nretF (relay_instance_gone_tr lv (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj
                       (known_at L A) 0 (known_at L A (bv_unsigned out))) /\
  (live = true ->
     live_at L' A' (resolveF qs (gone_out lv (bv_unsigned mx) (bv_unsigned nout)
       (bv_unsigned cap) pre es hj (known_at L A) 0 (known_at L A (bv_unsigned out)))) OUT' CAP') /\
  (forall i, (i < length es)%nat ->
     entry_links L' A' qs (nth i das dadr0) (nth i es' no_entry) /\
     (re_eof (nth i es no_entry) = 0 ->
        src_links L' A' qs (known_at L A) (nth i das dadr0) (nth i hs' (fst (nth i hj no_hj))))) /\
  In (G, SRC_TABLE) (blocks L' A') /\ length es' = length es /\
  Forall (RelayRep.entry_ok Bm L' A' mem') es' /\ length kss = length es /\ length hs' = length es /\
  (forall i, (i < length es)%nat ->
     let e := nth i es no_entry in
     let e' := nth i es' no_entry in
     let ks := nth i kss [] in
     let hj0 := nth i hj no_hj in
     let Ls := entry_lines e hj0 in
     let s := nth i ss (drain_init (bv_unsigned nout) (bv_unsigned cap) e (fst hj0)) in
     re_fd e' = re_fd e /\
     re_eof e' = (if re_eof e =? 0 then (if hs_closed (fst hj0) =? 1 then 1 else 0) else 1) /\
     NoDup ks /\ same_set ks (upds (keys_texts (re_keys e)) Ls) /\
     keys_texts (re_keys e') = snd (gei pre ks) /\
     ks = ds_H s /\ re_cap e' = ds_cap s /\ bzs (re_U e') = ds_u s /\
     re_skip e' = (if ds_skip s then 1 else 0) /\ ent_ka e' = ds_ka s /\
     (re_eof e = 0 ->
        let h := fst hj0 in
        let h' := nth i hs' h in
        src_at Bm L' A' mem' (G_S + SRC_SIZE * Z.of_nat (snd hj0)) h' /\
        hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\
        hs_eintr h' = 0 /\ hl_recs (hs_pending h') = [] /\
        hl_cap (hs_pending h') = hl_cap (hs_pending h) /\ hl_v (hs_pending h') = hl_v (hs_pending h) /\
        hs_off h' = 0 /\
        hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
        map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) Ls /\
        firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
        hs_held h' = hs_held h /\
        re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
        hl_cap (hs_expected h') = ds_ecap s /\
        hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h')))) /\
     (re_eof e = 1 ->
        re_skip e' = re_skip e /\ re_U e' = re_U e /\ re_buf e' = re_buf e /\
        re_used e' = re_used e /\ re_cap e' = re_cap e)) /\
  NoDup (G :: OUT' :: concat (map entry_blocks es') ++
         concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) (combine es hs'))) /\
  (forall q m, In (q, m) (blocks L A) -> q <> bv_unsigned out -> ~ In q (concat (map entry_blocks es)) ->
     ~ In q (drained_blocks es hj) -> In (q, m) (blocks L' A')) /\
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> q <> bv_unsigned out ->
     ~ In q (concat (map entry_blocks es)) -> ~ In q (drained_blocks es hj) ->
     q <> OUT' /\ ~ In q (concat (map entry_blocks es')) /\
     ~ In q (concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) (combine es hs')))) /\
  (forall q m, In (q, m) (blocks L' A') ->
     (In (q, m) (blocks L A) /\ q <> bv_unsigned out /\ ~ In q (concat (map entry_blocks es)) /\
      ~ In q (drained_blocks es hj)) \/
     In q (concat (map entry_blocks es')) \/
     In q (concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) (combine es hs'))) \/
     q = OUT') /\
  (live = false -> OUT' = bv_unsigned out /\ CAP' = bv_unsigned cap /\
     (0 < bv_unsigned cap -> In (bv_unsigned out, bv_unsigned cap) (blocks L' A'))) /\
  (live = true ->
     bv_unsigned nout + TOT <= CAP' /\
     CAP' = gone_cap lv (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj /\
     In (OUT', CAP') (blocks L' A')) /\
  aa_MR API L' A' mem' md' /\ List.NoDup (map fst (blocks L' A')) /\
  (forall p, In p (p5c_hj es hj hs') -> exists HA, src_at Bm L' A' mem' HA (fst p)) /\
  NoDup (target_addrs G OUT' es' (p5c_hj es hj hs')) /\
  (forall i, (i < length es)%nat -> re_eof (nth i es no_entry) = 0 ->
     hs_partial (nth i hs' (fst (nth i hj no_hj))) = hs_partial (fst (nth i hj no_hj))).

Definition p5v_cnt_S : Prop :=
  forall (rc : RunCeil) (Bm : malloc_syms) (API : @AllocAPI rc Bm) (L : layout) (A : astate)
         (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (t k G : Z) (es : list rentry)
         (hj : list (hsrc * nat)) (cl br dd : Z) (mx nout cap out : word) (pre : list Z)
         (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
         (OUT' CAP' : Z) (es' : list rentry) (hs' : list hsrc) (kss : list (list (list Z))) (qs : list sptr),
    p5v_ctx Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP'
      es' hs' kss qs ->
    let lv := send_live cl br dd 1 in
    let V := view_of G (bv_unsigned out) es hj in
    let V' := view_of G OUT' es' (p5c_hj es hj hs') in
    let nm := known_at L A in
    forall c, 0 <= c < 49 ->
      nc_cnt V L A c + gone_dl lv (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj nm 0
        (nm (bv_unsigned out)) c <= nc_cnt V' L' A' c.

Definition p5v_ncs_S : Prop :=
  forall (rc : RunCeil) (Bm : malloc_syms) (API : @AllocAPI rc Bm) (L : layout) (A : astate)
         (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (t k G : Z) (es : list rentry)
         (hj : list (hsrc * nat)) (cl br dd : Z) (mx nout cap out : word) (pre : list Z)
         (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
         (OUT' CAP' : Z) (es' : list rentry) (hs' : list hsrc) (kss : list (list (list Z))) (qs : list sptr),
    p5v_ctx Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP'
      es' hs' kss qs ->
    let lv := send_live cl br dd 1 in
    let V := view_of G (bv_unsigned out) es hj in
    let V' := view_of G OUT' es' (p5c_hj es hj hs') in
    let nm := known_at L A in
    ncs V L A + gone_db lv (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj nm 0 (nm (bv_unsigned out)) <=
      ncs V' L' A'.

Definition p5v_wt_S : Prop :=
  forall (rc : RunCeil) (Bm : malloc_syms) (API : @AllocAPI rc Bm) (L : layout) (A : astate)
         (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (t k G : Z) (es : list rentry)
         (hj : list (hsrc * nat)) (cl br dd : Z) (mx nout cap out : word) (pre : list Z)
         (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
         (OUT' CAP' : Z) (es' : list rentry) (hs' : list hsrc) (kss : list (list (list Z))) (qs : list sptr),
    p5v_ctx Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP'
      es' hs' kss qs ->
    let lv := send_live cl br dd 1 in
    let V := view_of G (bv_unsigned out) es hj in
    let V' := view_of G OUT' es' (p5c_hj es hj hs') in
    let nm := known_at L A in
    rv_wt V' <= rv_wt V +
      gone_wd (combine es hj) (gone_states lv (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj).

Definition p5v_ekc_S : Prop :=
  forall (rc : RunCeil) (Bm : malloc_syms) (API : @AllocAPI rc Bm) (L : layout) (A : astate)
         (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (t k G : Z) (es : list rentry)
         (hj : list (hsrc * nat)) (cl br dd : Z) (mx nout cap out : word) (pre : list Z)
         (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
         (OUT' CAP' : Z) (es' : list rentry) (hs' : list hsrc) (kss : list (list (list Z))) (qs : list sptr),
    p5v_ctx Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP'
      es' hs' kss qs ->
    let lv := send_live cl br dd 1 in
    let V := view_of G (bv_unsigned out) es hj in
    let V' := view_of G OUT' es' (p5c_hj es hj hs') in
    let nm := known_at L A in
    forall c, 0 <= c < 49 -> ek_c V' c = ek_c V c + bcnt c (gone_ek (combine es hj)).

Definition p5v_ekb_S : Prop :=
  forall (rc : RunCeil) (Bm : malloc_syms) (API : @AllocAPI rc Bm) (L : layout) (A : astate)
         (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (t k G : Z) (es : list rentry)
         (hj : list (hsrc * nat)) (cl br dd : Z) (mx nout cap out : word) (pre : list Z)
         (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
         (OUT' CAP' : Z) (es' : list rentry) (hs' : list hsrc) (kss : list (list (list Z))) (qs : list sptr),
    p5v_ctx Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP'
      es' hs' kss qs ->
    let lv := send_live cl br dd 1 in
    let V := view_of G (bv_unsigned out) es hj in
    let V' := view_of G OUT' es' (p5c_hj es hj hs') in
    let nm := known_at L A in
    ek_b V' = ek_b V + zsum (fun n => n) (gone_ek (combine es hj)).

Definition p5v_old_S : Prop :=
  forall (rc : RunCeil) (Bm : malloc_syms) (API : @AllocAPI rc Bm) (L : layout) (A : astate)
         (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (t k G : Z) (es : list rentry)
         (hj : list (hsrc * nat)) (cl br dd : Z) (mx nout cap out : word) (pre : list Z)
         (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
         (OUT' CAP' : Z) (es' : list rentry) (hs' : list hsrc) (kss : list (list (list Z))) (qs : list sptr),
    p5v_ctx Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP'
      es' hs' kss qs ->
    let lv := send_live cl br dd 1 in
    let V := view_of G (bv_unsigned out) es hj in
    let V' := view_of G OUT' es' (p5c_hj es hj hs') in
    let nm := known_at L A in
    forall p n, In (p, n) (user_blocks A) -> In (ptr_addr L p) (rv_nc V) ->
      ~ In (ptr_addr L p) (gone_tch (bv_unsigned out) (bv_unsigned cap) es hj) -> In (ptr_addr L' p) (rv_nc V').

Definition p5v_out_S : Prop :=
  forall (rc : RunCeil) (Bm : malloc_syms) (API : @AllocAPI rc Bm) (L : layout) (A : astate)
         (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (t k G : Z) (es : list rentry)
         (hj : list (hsrc * nat)) (cl br dd : Z) (mx nout cap out : word) (pre : list Z)
         (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
         (OUT' CAP' : Z) (es' : list rentry) (hs' : list hsrc) (kss : list (list (list Z))) (qs : list sptr),
    p5v_ctx Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP'
      es' hs' kss qs ->
    let lv := send_live cl br dd 1 in
    let V := view_of G (bv_unsigned out) es hj in
    let V' := view_of G OUT' es' (p5c_hj es hj hs') in
    let nm := known_at L A in
    gone_cap lv (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj <> 0 ->
      In (ptr_addr L' (resolveF qs (gone_out lv (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj nm 0
        (nm (bv_unsigned out))))) (rv_nc V').

Definition p5v_chain_S : Prop :=
  forall (rc : RunCeil) (Bm : malloc_syms) (API : @AllocAPI rc Bm) (L : layout) (A : astate)
         (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (t k G : Z) (es : list rentry)
         (hj : list (hsrc * nat)) (cl br dd : Z) (mx nout cap out : word) (pre : list Z)
         (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
         (OUT' CAP' : Z) (es' : list rentry) (hs' : list hsrc) (kss : list (list (list Z))) (qs : list sptr),
    p5v_ctx Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP'
      es' hs' kss qs ->
    let lv := send_live cl br dd 1 in
    let V := view_of G (bv_unsigned out) es hj in
    let V' := view_of G OUT' es' (p5c_hj es hj hs') in
    let nm := known_at L A in
    forall i, (i < length es)%nat -> re_eof (nth i es no_entry) = 0 ->
      let s := nth i (gone_states lv (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj)
                 (drain_init (bv_unsigned nout) (bv_unsigned cap) (nth i es no_entry) (fst (nth i hj no_hj))) in
      let a := nth i (gone_adrs lv (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj nm 0
                 (nm (bv_unsigned out))) dadr0 in
      (ds_cap s <> 0 -> In (ptr_addr L' (resolveF qs (da_buf a))) (rv_nc V')) /\
      (ds_ka s <> 0 -> In (ptr_addr L' (resolveF qs (da_hp a))) (rv_nc V')) /\
      (ds_ecap s <> 0 -> In (ptr_addr L' (resolveF qs (da_ev a))) (rv_nc V')).

Definition p5v_pend_S : Prop :=
  forall (rc : RunCeil) (Bm : malloc_syms) (API : @AllocAPI rc Bm) (L : layout) (A : astate)
         (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (t k G : Z) (es : list rentry)
         (hj : list (hsrc * nat)) (cl br dd : Z) (mx nout cap out : word) (pre : list Z)
         (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
         (OUT' CAP' : Z) (es' : list rentry) (hs' : list hsrc) (kss : list (list (list Z))) (qs : list sptr),
    p5v_ctx Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP'
      es' hs' kss qs ->
    let lv := send_live cl br dd 1 in
    let V := view_of G (bv_unsigned out) es hj in
    let V' := view_of G OUT' es' (p5c_hj es hj hs') in
    let nm := known_at L A in
    rv_pend V' = gone_pend es hj.

Lemma p5v_nth_seq {X} (f : nat -> X) n i d : (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof.
  intros H. rewrite (nth_indep (map f (seq 0 n)) d (f 0%nat)) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Lemma p5v_hj_len es hj hs' : length (p5c_hj es hj hs') = length es.
Proof. unfold p5c_hj. rewrite length_map, length_seq. reflexivity. Qed.

Lemma p5v_hj_nth es hj hs' i d : (i < length es)%nat ->
  nth i (p5c_hj es hj hs') d =
  (g5_src (nth i es no_entry) (fst (nth i hj no_hj)) (nth i hs' (fst no_hj)), snd (nth i hj no_hj)).
Proof. intros H. unfold p5c_hj. rewrite p5v_nth_seq by exact H. reflexivity. Qed.

Lemma p5v_map_eq {B} (f : hsrc * nat -> B) (g : rentry * (hsrc * nat) -> B) es hj hs' :
  length hj = length es ->
  (forall i, (i < length es)%nat ->
     f (g5_src (nth i es no_entry) (fst (nth i hj no_hj)) (nth i hs' (fst no_hj)), snd (nth i hj no_hj)) =
     g (nth i es no_entry, nth i hj no_hj)) ->
  map f (p5c_hj es hj hs') = map g (combine es hj).
Proof.
  intros HL HF. apply (nth_ext _ _ (f no_hj) (g (no_entry, no_hj))).
  - rewrite !length_map, p5v_hj_len, length_combine, HL. lia.
  - intros i Hi. rewrite length_map, p5v_hj_len in Hi.
    rewrite map_nth, map_nth, combine_nth by (symmetry; exact HL). rewrite p5v_hj_nth by exact Hi.
    apply HF. exact Hi.
Qed.

Ltac p5v_open H :=
  unfold p5v_ctx in H; cbv zeta in H;
  destruct H as (MR & ND & OA & GB & EOK & POK & NDT & LHJ & LES & SC & KI & TR & NO0 & CL & BR & DD & RP & LQS &
                 LIVE & LNK & GB' & LES' & EOK' & LKS & LHS' & PER & ND' & KEEP & KPOS & ORIG & DEAD & LV & MR' & ND2 &
                 SRC & NDT' & PART).

Lemma p5v_el0 e hj0 : re_eof e = 0 -> entry_lines e hj0 = lines (hs_state (fst hj0)) (bzs (pending_stream (fst hj0))).
Proof. intros E. unfold entry_lines. rewrite E. reflexivity. Qed.

Lemma p5v_f2r {X Y} (R : X -> Y -> Prop) (P : Y -> Prop) l1 l2 :
  Forall2 R l1 l2 -> (forall x y, R x y -> P y) -> Forall P l2.
Proof. intros H HP. induction H as [|x y l1 l2 Hxy _ IH]; constructor; [exact (HP x y Hxy)|exact IH]. Qed.

Lemma p5v_ekv0 (hj : list (hsrc * nat)) : Forall (fun p => hl_recs (hs_expected (fst p)) = []) hj -> ek_view hj = [].
Proof.
  induction 1 as [|p hj Hp _ IH]; [reflexivity|]. unfold ek_view in *. cbn [map concat]. rewrite IH.
  unfold ekeys_hl. rewrite Hp. reflexivity.
Qed.

Lemma p5v_bzs_map Ls : Forall zrange Ls -> map bzs (map (map (Z_to_bv 8)) Ls) = Ls.
Proof. induction 1 as [|l Ls Hl _ IH]; [reflexivity|]. cbn [map]. rewrite bzs_lits by exact Hl. f_equal. exact IH. Qed.

Lemma p5v_ekv1 es hj hs' : length hj = length es ->
  (forall i, (i < length es)%nat -> hl_recs (hs_expected (fst (nth i hj no_hj))) = [] /\
     (re_eof (nth i es no_entry) = 0 ->
        map snd (hl_recs (hs_expected (nth i hs' (fst no_hj)))) =
        map snd (hl_recs (hs_expected (fst (nth i hj no_hj)))) ++
        map (map (Z_to_bv 8)) (lines (hs_state (fst (nth i hj no_hj))) (bzs (pending_stream (fst (nth i hj no_hj))))))) ->
  ek_view (p5c_hj es hj hs') = gone_ek (combine es hj).
Proof.
  intros HL HF. unfold ek_view, gone_ek. f_equal. apply p5v_map_eq; [exact HL|]. intros i Hi. cbn [fst snd].
  destruct (HF i Hi) as [HE HM].
  destruct (g5_exp (nth i es no_entry) (nth i hj no_hj) (nth i hs' (fst no_hj)) HE HM) as [X ZR].
  unfold ekeys_hl. rewrite <- (map_map snd bzs), X, (p5v_bzs_map _ ZR). unfold entry_lines.
  destruct (re_eof (nth i es no_entry) =? 0); reflexivity.
Qed.

Lemma p5v_ek_all {rc : RunCeil} {Bm : malloc_syms} {API : AllocAPI Bm} {L A regs mem md t k G es hj cl br dd mx nout
    cap out pre L' A' regs' mem' md' OUT' CAP' es' hs' kss qs} :
  p5v_ctx Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP' es' hs' kss qs ->
  ek_view hj = [] /\ ek_view (p5c_hj es hj hs') = gone_ek (combine es hj).
Proof.
  intros H. p5v_open H.
  assert (EX : Forall (fun p => hl_recs (hs_expected (fst p)) = []) hj).
  { apply (p5v_f2r _ _ _ _ POK). intros e p (_ & _ & _ & _ & _ & _ & X & _). exact X. }
  split; [exact (p5v_ekv0 hj EX)|]. apply (p5v_ekv1 es hj hs' LHJ). intros i Hi.
  split; [exact (proj1 (Forall_nth _ _) EX i no_hj ltac:(lia))|]. intros E0.
  destruct (PER i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P0 & _).
  destruct (P0 E0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _).
  rewrite (nth_indep hs' (fst no_hj) (fst (nth i hj no_hj))) by lia. rewrite X, (p5v_el0 _ _ E0). reflexivity.
Qed.

Lemma p5v_zsum_nth {X} (f : X -> Z) d l :
  AllocBound.zsum f l = AllocBound.zsum (fun i => f (nth i l d)) (seq 0 (length l)).
Proof.
  induction l as [|x l IH]; [reflexivity|]. cbn [length seq].
  rewrite !AllocBound.zsum_cons, <- seq_shift, AllocBound.zsum_map, IH. reflexivity.
Qed.

Lemma p5v_zsum_add {X} (f g : X -> Z) l :
  AllocBound.zsum (fun x => f x + g x) l = AllocBound.zsum f l + AllocBound.zsum g l.
Proof. induction l as [|x l IH]; [reflexivity|]. rewrite !AllocBound.zsum_cons, IH. lia. Qed.

Lemma p5v_zsum_le {X} (f g : X -> Z) l :
  (forall x, In x l -> f x <= g x) -> AllocBound.zsum f l <= AllocBound.zsum g l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. rewrite !AllocBound.zsum_cons.
  pose proof (H x (or_introl eq_refl)). pose proof (IH (fun y Hy => H y (or_intror Hy))). lia.
Qed.

Lemma p5v_wd_seq ps ss d : length ss = length ps ->
  gone_wd ps ss = AllocBound.zsum (fun i => let p := nth i ps (no_entry, no_hj) in
    if re_eof (fst p) =? 0 then drain_wt_src (nth i ss d) (fst (snd p)) - nw_ent (fst p) - nw_src (fst (snd p)) else 0)
    (seq 0 (length ps)).
Proof.
  revert ss. induction ps as [|p ps IH]; intros [|s ss] HL; cbn [length] in HL; try discriminate; [reflexivity|].
  cbn [gone_wd length seq]. rewrite AllocBound.zsum_cons, <- seq_shift, AllocBound.zsum_map, (IH ss) by lia.
  reflexivity.
Qed.

Lemma p5v_gei_len pre ks : NoDup ks -> (length (snd (gei pre ks)) <= length ks)%nat.
Proof.
  intros ND. apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in ND.
  pose proof (gei_ok pre ks ND) as G. destruct (gei pre ks) as [E H'].
  destruct G as (_ & _ & PM & _). apply Permutation_length in PM. rewrite length_app in PM. cbn [snd]. lia.
Qed.

Lemma p5v_kt_len pre ks e : NoDup ks -> keys_texts (re_keys e) = snd (gei pre ks) -> re_nheld e <= Z.of_nat (length ks).
Proof.
  intros ND KT. pose proof (p5v_gei_len pre ks ND) as GL.
  assert (E1 : length (keys_texts (re_keys e)) = length (re_keys e)) by (unfold keys_texts; apply length_map).
  unfold re_nheld. rewrite <- E1, KT. lia.
Qed.

Lemma p5v_wt0 (e' : rentry) (h h' : hsrc) (s : dstate) (pre : list Z) (ks : list (list Z)) :
  NoDup ks -> keys_texts (re_keys e') = snd (gei pre ks) -> ks = ds_H s -> re_cap e' = ds_cap s ->
  bzs (re_U e') = ds_u s -> ent_ka e' = ds_ka s -> Z.of_nat (length (re_U e')) = re_used e' ->
  hl_recs (hs_pending h') = [] -> hl_cap (hs_pending h') = hl_cap (hs_pending h) ->
  map snd (hl_recs (hs_expected h')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (lines (hs_state h) (bzs (pending_stream h))) ->
  hs_held h' = hs_held h -> hl_cap (hs_expected h') = ds_ecap s ->
  nw_ent e' + nw_src h' <= drain_wt_src s h.
Proof.
  intros ND KT KH RC RU KA LU HP HPC HX HH HEC.
  pose proof (p5v_kt_len pre ks e' ND KT) as LK. rewrite KH in LK.
  assert (LU2 : Z.of_nat (length (ds_u s)) = re_used e') by (rewrite <- RU; unfold bzs; rewrite length_map; exact LU).
  assert (LX : hl_n (hs_expected h') =
      hl_n (hs_expected h) + Z.of_nat (length (lines (hs_state h) (bzs (pending_stream h))))).
  { unfold hl_n. rewrite <- (length_map snd (hl_recs (hs_expected h'))), HX, length_app, !length_map. lia. }
  assert (PS : pending_stream h' = []) by (unfold pending_stream; rewrite HP; reflexivity).
  assert (PN : hl_n (hs_pending h') = 0) by (unfold hl_n; rewrite HP; reflexivity).
  unfold nw_ent, nw_src, drain_wt_src, nw_list. fold (ent_ka e').
  rewrite KA, RC, PS, PN, HPC, HH, HEC, LX, <- LU2. cbn [length Z.of_nat]. unfold DATA_PER, NC_PER. lia.
Qed.

Lemma p5v_wt1 (e e' : rentry) (pre : list Z) (ks : list (list Z)) :
  NoDup ks -> keys_texts (re_keys e') = snd (gei pre ks) -> ks = keys_texts (re_keys e) -> ent_ka e' = ent_ka e ->
  re_cap e' = re_cap e -> re_used e' = re_used e -> nw_ent e' <= nw_ent e.
Proof.
  intros ND KT KH KA RC RU. pose proof (p5v_kt_len pre ks e' ND KT) as LK.
  assert (E1 : length (keys_texts (re_keys e)) = length (re_keys e)) by (unfold keys_texts; apply length_map).
  rewrite KH, E1 in LK. unfold nw_ent. fold (ent_ka e'). fold (ent_ka e). rewrite KA, RC, RU.
  unfold re_nheld in *. lia.
Qed.

Lemma p5v_gs1 lv mx no cap pre es hj i d : length hj = length es -> (i < length es)%nat ->
  re_eof (nth i es no_entry) <> 0 ->
  ds_H (nth i (gone_states lv mx no cap pre es hj) d) = keys_texts (re_keys (nth i es no_entry)) /\
  ds_ka (nth i (gone_states lv mx no cap pre es hj) d) = ent_ka (nth i es no_entry) /\
  ds_cap (nth i (gone_states lv mx no cap pre es hj) d) = re_cap (nth i es no_entry).
Proof.
  intros HL Hi E1. unfold gone_states.
  destruct (g5m_gs_after lv mx pre (combine es hj) no cap (fun _ => adr0) 0 adr0 i d) as (no' & cap' & EQ).
  { rewrite length_combine, HL. lia. }
  rewrite EQ, combine_nth by (symmetry; exact HL). cbn [fst snd]. unfold after_drain.
  destruct (Z.eqb_spec (re_eof (nth i es no_entry)) 0) as [E|_]; [contradiction|]. cbv iota.
  split; [|split]; reflexivity.
Qed.

Lemma p5v_wt_gen (es es' : list rentry) (hj P : list (hsrc * nat)) (w : nat -> Z) :
  length es' = length es -> length hj = length es -> length P = length es ->
  (forall i, (i < length es)%nat ->
     nw_ent (nth i es' no_entry) + nw_src (fst (nth i P no_hj)) <=
     nw_ent (nth i es no_entry) + nw_src (fst (nth i hj no_hj)) + w i) ->
  nc_wt es' P <= nc_wt es hj + AllocBound.zsum w (seq 0 (length es)).
Proof.
  intros L1 L2 L3 HP. unfold nc_wt.
  rewrite (p5v_zsum_nth nw_ent no_entry es'), (p5v_zsum_nth nw_ent no_entry es),
    (p5v_zsum_nth (fun p => nw_src (fst p)) no_hj P), (p5v_zsum_nth (fun p => nw_src (fst p)) no_hj hj), L1, L2, L3.
  cbv beta.
  assert (X : AllocBound.zsum (fun i => nw_ent (nth i es' no_entry)) (seq 0 (length es)) +
              AllocBound.zsum (fun i => nw_src (fst (nth i P no_hj))) (seq 0 (length es)) <=
              AllocBound.zsum (fun i => nw_ent (nth i es no_entry)) (seq 0 (length es)) +
              AllocBound.zsum (fun i => nw_src (fst (nth i hj no_hj))) (seq 0 (length es)) +
              AllocBound.zsum w (seq 0 (length es))).
  { rewrite <- !p5v_zsum_add. apply p5v_zsum_le. intros i Hi. apply in_seq in Hi. cbv beta. apply HP. lia. }
  lia.
Qed.

Lemma p5v_sum_ge (fe : rentry -> Z) (fs : hsrc -> Z) (es es' : list rentry) (hj P : list (hsrc * nat)) (w : nat -> Z) :
  length es' = length es -> length hj = length es -> length P = length es ->
  (forall i, (i < length es)%nat ->
     fe (nth i es no_entry) + fs (fst (nth i hj no_hj)) + w i <= fe (nth i es' no_entry) + fs (fst (nth i P no_hj))) ->
  AllocBound.zsum fe es + AllocBound.zsum (fun p => fs (fst p)) hj + AllocBound.zsum w (seq 0 (length es)) <=
  AllocBound.zsum fe es' + AllocBound.zsum (fun p => fs (fst p)) P.
Proof.
  intros L1 L2 L3 HP.
  rewrite (p5v_zsum_nth fe no_entry es'), (p5v_zsum_nth fe no_entry es),
    (p5v_zsum_nth (fun p => fs (fst p)) no_hj P), (p5v_zsum_nth (fun p => fs (fst p)) no_hj hj), L1, L2, L3.
  cbv beta. rewrite <- !p5v_zsum_add. apply p5v_zsum_le. intros i Hi. apply in_seq in Hi. cbv beta. apply HP. lia.
Qed.

Lemma p5v_dch_seq ps ss d c : length ss = length ps ->
  gone_dch ps ss c = AllocBound.zsum (fun i => let p := nth i ps (no_entry, no_hj) in
    if re_eof (fst p) =? 0 then dchain (fst p) (fst (snd p)) (nth i ss d) c else 0) (seq 0 (length ps)).
Proof.
  revert ss. induction ps as [|p ps IH]; intros [|s ss] HL; cbn [length] in HL; try discriminate; [reflexivity|].
  cbn [gone_dch length seq]. rewrite AllocBound.zsum_cons, <- seq_shift, AllocBound.zsum_map, (IH ss) by lia.
  reflexivity.
Qed.

Lemma p5v_dchb_seq ps ss d : length ss = length ps ->
  gone_dchb ps ss = AllocBound.zsum (fun i => let p := nth i ps (no_entry, no_hj) in
    if re_eof (fst p) =? 0 then dchainb (fst p) (fst (snd p)) (nth i ss d) else 0) (seq 0 (length ps)).
Proof.
  revert ss. induction ps as [|p ps IH]; intros [|s ss] HL; cbn [length] in HL; try discriminate; [reflexivity|].
  cbn [gone_dchb length seq]. rewrite AllocBound.zsum_cons, <- seq_shift, AllocBound.zsum_map, (IH ss) by lia.
  reflexivity.
Qed.

Lemma p5v_capT lv mx no cap pre es hj nm j o :
  gone_capT lv mx no cap pre es hj nm j o = gone_cap lv mx no cap pre es hj.
Proof. unfold gone_capT, gone_cap. exact (proj1 (gone_indep _ _ _ _ _ _ _ _ _ _ _ _)). Qed.

Lemma p5v_ssT lv mx no cap pre es hj nm j o :
  gone_ssT lv mx no cap pre es hj nm j o = gone_states lv mx no cap pre es hj.
Proof. unfold gone_ssT, gone_states. exact (proj2 (gone_indep _ _ _ _ _ _ _ _ _ _ _ _)). Qed.

Definition p5v_apl (l : hlist) : list (Z * Z) := if hl_cap l =? 0 then [] else [(hl_v l, 16 * hl_cap l)].

Definition p5v_spl (h : hsrc) : list (Z * Z) :=
  p5v_apl (hs_pending h) ++ [(hs_partial h, 6000)] ++ p5v_apl (hs_expected h) ++ p5v_apl (hs_held h).

Definition p5v_epl (e : rentry) : list (Z * Z) :=
  (if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++ (if re_hp e =? 0 then [] else [(re_hp e, re_kh e)]).

Definition p5v_vpl (G OUT CAP : Z) (es : list rentry) (hj : list (hsrc * nat)) : list (Z * Z) :=
  (G, SRC_TABLE) :: (OUT, CAP) :: concat (map p5v_epl es) ++ concat (map (fun p => p5v_spl (fst p)) hj).

Definition p5v_ok (L : layout) (A : astate) (t : Z * Z) : Prop :=
  (snd t = 0 /\ forall m, ~ In (fst t, m) (blocks L A)) \/ (snd t <> 0 /\ In t (blocks L A)).

Definition p5v_ew (w : Z -> Z) (e : rentry) : Z := w (re_cap e) + w (ent_ka e).

Definition p5v_sw (w : Z -> Z) (h : hsrc) : Z :=
  w (16 * hl_cap (hs_pending h)) + w 6000 + w (16 * hl_cap (hs_expected h)) + w (16 * hl_cap (hs_held h)).

Lemma p5v_vpl_fst G OUT CAP es hj : map fst (p5v_vpl G OUT CAP es hj) = rv_nc (view_of G OUT es hj).
Proof.
  unfold p5v_vpl, view_of. cbn [map rv_nc fst]. do 2 f_equal.
  rewrite map_app, !concat_map, !map_map. f_equal; f_equal; apply map_ext; intros x.
  - unfold p5v_epl, entry_nc. rewrite map_app. destruct (re_cap x =? 0), (re_hp x =? 0); reflexivity.
  - unfold p5v_spl, src_nc, p5v_apl, arr_nc. rewrite !map_app.
    destruct (hl_cap (hs_pending (fst x)) =? 0), (hl_cap (hs_expected (fst x)) =? 0), (hl_cap (hs_held (fst x)) =? 0);
      reflexivity.
Qed.

Lemma p5v_one (w : Z -> Z) (b : bool) (x m : Z) : w 0 = 0 ->
  AllocBound.zsum (fun t : Z * Z => w (snd t)) (if b then [] else [(x, m)]) = w (if b then 0 else m).
Proof. intros W. destruct b; cbn [AllocBound.zsum fold_right snd]; [symmetry; exact W|lia]. Qed.

Lemma p5v_vpl_w (w : Z -> Z) G OUT CAP es hj : w 0 = 0 ->
  AllocBound.zsum (fun t => w (snd t)) (p5v_vpl G OUT CAP es hj) =
  w SRC_TABLE + w CAP + AllocBound.zsum (p5v_ew w) es + AllocBound.zsum (fun p => p5v_sw w (fst p)) hj.
Proof.
  intros W.
  assert (E1 : forall e, AllocBound.zsum (fun t => w (snd t)) (p5v_epl e) = p5v_ew w e).
  { intros e. unfold p5v_epl, p5v_ew, ent_ka. rewrite AllocBound.zsum_app, !p5v_one by exact W.
    destruct (Z.eqb_spec (re_cap e) 0) as [E|E]; [rewrite E|]; reflexivity. }
  assert (E2 : forall l, AllocBound.zsum (fun t => w (snd t)) (p5v_apl l) = w (16 * hl_cap l)).
  { intros l. unfold p5v_apl. rewrite p5v_one by exact W.
    destruct (Z.eqb_spec (hl_cap l) 0) as [E|E]; [rewrite E|]; reflexivity. }
  assert (E3 : forall h, AllocBound.zsum (fun t => w (snd t)) (p5v_spl h) = p5v_sw w h).
  { intros h. unfold p5v_spl, p5v_sw. rewrite !AllocBound.zsum_app, AllocBound.zsum_cons, AllocBound.zsum_nil, !E2.
    cbn [snd]. lia. }
  unfold p5v_vpl. rewrite !AllocBound.zsum_cons, AllocBound.zsum_app, !nw_zsum_concat. cbn [snd].
  rewrite (nm3_ext _ (p5v_ew w) es) by (intros e _; apply E1).
  rewrite (nm3_ext _ (fun p => p5v_sw w (fst p)) hj) by (intros p _; apply E3). lia.
Qed.

Lemma p5v_cnt_one L A c t : List.NoDup (map fst (blocks L A)) -> p5v_ok L A t ->
  (if nc_has L A c (fst t) then 1 else 0) = ncb (snd t) c.
Proof.
  intros HN [(E0 & HB)|(E0 & HB)]; destruct t as [q m]; cbn [fst snd] in *.
  - rewrite nm3_has_b, nm3_has_none.
    + unfold ncb. rewrite E0. reflexivity.
    + intros X. apply in_map_iff in X as ([q' m'] & Eq & X). cbn [fst] in Eq. subst q'. exact (HB m' X).
  - apply in_split in HB as (l1 & l2 & EB). rewrite nm3_has_b, EB. rewrite EB in HN.
    destruct (nm3_pt_at l1 l2 q m HN) as (_ & _ & X & _). rewrite X. unfold ncb.
    rewrite (proj2 (Z.eqb_neq m 0) E0). reflexivity.
Qed.

Lemma p5v_sz_one L A t : List.NoDup (map fst (blocks L A)) -> p5v_ok L A t -> nc_sz L A (fst t) = snd t.
Proof.
  intros HN [(E0 & HB)|(E0 & HB)]; destruct t as [q m]; cbn [fst snd] in *.
  - rewrite E0. exact (nw_sz_none L A q HB).
  - exact (nw_sz_at L A q m HN HB).
Qed.

Lemma p5v_cnt_view V L A c PL : List.NoDup (map fst (blocks L A)) -> map fst PL = rv_nc V ->
  Forall (p5v_ok L A) PL -> nc_cnt V L A c = AllocBound.zsum (fun t => ncb (snd t) c) PL.
Proof.
  intros HN HM HF. rewrite nm3_cnt, <- HM, AllocBound.zsum_map. apply nm3_ext. intros t Ht.
  apply p5v_cnt_one; [exact HN | exact (proj1 (Forall_forall _ _) HF t Ht)].
Qed.

Lemma p5v_ncs_view V L A PL : List.NoDup (map fst (blocks L A)) -> map fst PL = rv_nc V ->
  Forall (p5v_ok L A) PL -> ncs V L A = AllocBound.zsum (fun t => snd t) PL.
Proof.
  intros HN HM HF. unfold ncs. rewrite <- HM, AllocBound.zsum_map. apply nm3_ext. intros t Ht.
  apply p5v_sz_one; [exact HN | exact (proj1 (Forall_forall _ _) HF t Ht)].
Qed.

Lemma p5v_apl_ok L A (l : hlist) (X Y : Prop) :
  ((hl_cap l = 0 /\ X) \/ (0 < hl_cap l /\ In (hl_v l, 16 * hl_cap l) (blocks L A) /\ Y)) ->
  Forall (p5v_ok L A) (p5v_apl l).
Proof.
  intros Hc. unfold p5v_apl. destruct (Z.eqb_spec (hl_cap l) 0) as [E|E]; cbv iota; [constructor|].
  constructor; [|constructor]. unfold p5v_ok. right. cbn [fst snd].
  destruct Hc as [(C & _)|(C & IN & _)]; [lia|]. split; [lia|exact IN].
Qed.

Lemma p5v_spl_ok L A (h : hsrc) (X1 Y1 X2 Y2 X3 Y3 : Prop) :
  ((hl_cap (hs_pending h) = 0 /\ X1) \/
   (0 < hl_cap (hs_pending h) /\ In (hl_v (hs_pending h), 16 * hl_cap (hs_pending h)) (blocks L A) /\ Y1)) ->
  ((hl_cap (hs_expected h) = 0 /\ X2) \/
   (0 < hl_cap (hs_expected h) /\ In (hl_v (hs_expected h), 16 * hl_cap (hs_expected h)) (blocks L A) /\ Y2)) ->
  ((hl_cap (hs_held h) = 0 /\ X3) \/
   (0 < hl_cap (hs_held h) /\ In (hl_v (hs_held h), 16 * hl_cap (hs_held h)) (blocks L A) /\ Y3)) ->
  In (hs_partial h, 6000) (blocks L A) -> Forall (p5v_ok L A) (p5v_spl h).
Proof.
  intros Cp Ce Ch Hp. unfold p5v_spl. apply Forall_app. split; [exact (p5v_apl_ok L A _ _ _ Cp)|].
  apply Forall_app. split; [constructor; [|constructor]; unfold p5v_ok; right; cbn [fst snd]; split; [lia|exact Hp]|].
  apply Forall_app. split; [exact (p5v_apl_ok L A _ _ _ Ce)|exact (p5v_apl_ok L A _ _ _ Ch)].
Qed.

Lemma p5v_epl_ok L A (e : rentry) (X1 Y1 X2 Y2 Y3 Y4 : Prop) :
  ((re_cap e = 0 /\ X1) \/ (0 < re_cap e /\ In (re_buf e, re_cap e) (blocks L A) /\ Y1)) ->
  ((re_hp e = 0 /\ X2) \/ (In (re_hp e, re_kh e) (blocks L A) /\ Y2 /\ Y3 /\ 8 <= re_kh e /\ Y4)) ->
  Forall (p5v_ok L A) (p5v_epl e).
Proof.
  intros Hb Hh. unfold p5v_epl. apply Forall_app. split.
  - destruct (Z.eqb_spec (re_cap e) 0) as [E|E]; cbv iota; [constructor|].
    constructor; [|constructor]. unfold p5v_ok. right. cbn [fst snd].
    destruct Hb as [(C & _)|(C & IN & _)]; [lia|]. split; [lia|exact IN].
  - destruct (Z.eqb_spec (re_hp e) 0) as [E|E]; cbv iota; [constructor|].
    constructor; [|constructor]. unfold p5v_ok. right. cbn [fst snd].
    destruct Hh as [(C & _)|(IN & _ & _ & K8 & _)]; [lia|]. split; [lia|exact IN].
Qed.

Lemma p5v_fcm {X Y} (P : Y -> Prop) (f : X -> list Y) l :
  (forall x, In x l -> Forall P (f x)) -> Forall P (concat (map f l)).
Proof.
  induction l as [|x l IH]; intros H; [constructor|]. cbn [map concat]. apply Forall_app.
  split; [apply H; left; reflexivity|apply IH; intros y Hy; apply H; right; exact Hy].
Qed.

Ltac p5v_ent_ok EO :=
  let Hb := fresh "Hb" in let Hh := fresh "Hh" in
  destruct EO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _ & Hh & _);
  exact (p5v_epl_ok _ _ _ _ _ _ _ _ _ Hb Hh).

Ltac p5v_src_ok SA :=
  let Lp := fresh "Lp" in let Le := fresh "Le" in let Lh := fresh "Lh" in let Hp := fresh "Hp" in
  destruct SA as (_ & _ & _ & _ & _ & Lp & _ & _ & _ & _ & Hp & _ & _ & _ & _ & Le & Lh & _);
  exact (p5v_spl_ok _ _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 Lp))) (proj1 (proj2 (proj2 Le)))
           (proj1 (proj2 (proj2 Lh))) Hp).

Lemma p5v_live_tot cl br dd n : send_live cl br dd n = true -> n <> 0.
Proof.
  intros H E. subst n. unfold send_live, send_off in H. rewrite Z.eqb_refl, orb_true_r in H. cbn in H.
  discriminate H.
Qed.

Lemma p5v_live0 cl br dd n : send_live cl br dd 1 = true -> send_live cl br dd n = false -> n = 0.
Proof.
  intros H1 H2. destruct (Z.eqb_spec n 0) as [E|E]; [exact E|]. exfalso.
  unfold send_live, send_off in H1, H2. rewrite (proj2 (Z.eqb_neq n 0) E) in H2. cbn [Z.eqb] in H1.
  rewrite H1 in H2. discriminate H2.
Qed.

Lemma p5v_pl_pre {rc : RunCeil} {Bm : malloc_syms} {API : AllocAPI Bm} {L A regs mem md t k G es hj cl br dd mx nout
    cap out pre L' A' regs' mem' md' OUT' CAP' es' hs' kss qs} :
  p5v_ctx Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP' es' hs' kss qs ->
  Forall (p5v_ok L A) (p5v_vpl G (bv_unsigned out) (bv_unsigned cap) es hj).
Proof.
  intros H. p5v_open H. unfold p5v_vpl. constructor; [|constructor].
  - unfold p5v_ok. cbn [fst snd]. right. split; [unfold SRC_TABLE, SRC_ENTRY; lia|exact GB].
  - unfold p5v_ok. cbn [fst snd]. destruct OA as ((O & junk & [(C0 & O0 & _)|(CP & _ & IN & _)]) & _).
    + left. split; [exact C0|]. rewrite O0. exact (nw_no_zero Bm API L A mem md MR).
    + right. split; [lia|exact IN].
  - apply Forall_app. split; apply p5v_fcm; intros y Hy.
    + pose proof (proj1 (Forall_forall _ _) EOK y Hy) as EO. p5v_ent_ok EO.
    + destruct (nw_f2_r _ _ _ y POK Hy) as (e & _ & PO). destruct PO as (SA & _). cbv beta. p5v_src_ok SA.
Qed.

Lemma p5v_pl_post {rc : RunCeil} {Bm : malloc_syms} {API : AllocAPI Bm} {L A regs mem md t k G es hj cl br dd mx nout
    cap out pre L' A' regs' mem' md' OUT' CAP' es' hs' kss qs} :
  p5v_ctx Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP' es' hs' kss qs ->
  Forall (p5v_ok L' A') (p5v_vpl G OUT' CAP' es' (p5c_hj es hj hs')).
Proof.
  intros H. p5v_open H. unfold p5v_vpl. constructor; [|constructor].
  - unfold p5v_ok. cbn [fst snd]. right. split; [unfold SRC_TABLE, SRC_ENTRY; lia|exact GB'].
  - unfold p5v_ok. cbn [fst snd].
    match type of LIVE with ?lv = true -> _ => destruct lv eqn:LVE end.
    + destruct (LV eq_refl) as (C1 & _ & IN). pose proof (p5v_live_tot _ _ _ _ LVE) as T.
      right. split; [lia|exact IN].
    + destruct (DEAD eq_refl) as (O1 & C1 & IN). rewrite O1, C1.
      destruct OA as ((O & junk & [(C0 & O0 & _)|(CP & _ & _)]) & _).
      * left. split; [exact C0|]. rewrite O0. exact (nw_no_zero Bm API L' A' mem' md' MR').
      * right. split; [lia|exact (IN CP)].
  - apply Forall_app. split; apply p5v_fcm; intros y Hy.
    + pose proof (proj1 (Forall_forall _ _) EOK' y Hy) as EO. p5v_ent_ok EO.
    + destruct (SRC y Hy) as (HA & SA). cbv beta. p5v_src_ok SA.
Qed.

Lemma p5v_capF {rc : RunCeil} {Bm : malloc_syms} {API : AllocAPI Bm} {L A regs mem md t k G es hj cl br dd mx nout
    cap out pre L' A' regs' mem' md' OUT' CAP' es' hs' kss qs} :
  p5v_ctx Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP' es' hs' kss qs ->
  CAP' = gone_cap (send_live cl br dd 1) (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj.
Proof.
  intros H. p5v_open H.
  match type of LIVE with ?lv = true -> _ => destruct lv eqn:LVE end.
  - exact (proj1 (proj2 (LV eq_refl))).
  - destruct (DEAD eq_refl) as (_ & C1 & _). rewrite C1.
    destruct (send_live cl br dd 1) eqn:LV1; [|symmetry; apply gone_cap_dead].
    pose proof (p5v_live0 _ _ _ _ LV1 LVE) as T0.
    assert (HT : concat (map (fun i => gone_segment pre (entry_lines (nth i es no_entry) (nth i hj no_hj)) (nth i kss []))
                   (seq 0 (length es))) = []) by (apply length_zero_iff_nil; lia).
    assert (HK : forall i, (i < length es)%nat ->
       nth i kss [] = ds_H (nth i (gone_states true (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj)
                              (drain_init (bv_unsigned nout) (bv_unsigned cap) (nth i es no_entry) (fst (nth i hj no_hj))))).
    { intros i Hi. destruct (PER i Hi) as (_ & _ & _ & _ & _ & KH & _). exact KH. }
    destruct (gone_tot0_holds true (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj kss (fun _ => adr0)
      0%nat adr0 LHJ (g5m_tot0_drain Bm L A mem t es hj EOK POK) HK HT) as [GC _].
    symmetry. exact GC.
Qed.

Lemma p5v_pt0 (w : Z -> Z) (e e' : rentry) (h h' : hsrc) (s : dstate) :
  re_cap e' = ds_cap s -> ent_ka e' = ds_ka s -> hl_cap (hs_pending h') = hl_cap (hs_pending h) ->
  hl_cap (hs_expected h') = ds_ecap s -> hs_held h' = hs_held h ->
  p5v_ew w e' + p5v_sw w h' = p5v_ew w e + p5v_sw w h +
    (w (ds_cap s) - w (re_cap e) + (w (ds_ka s) - w (ent_ka e)) + (w (16 * ds_ecap s) - w (16 * hl_cap (hs_expected h)))).
Proof. intros RC KA HPC HEC HH. unfold p5v_ew, p5v_sw. rewrite RC, KA, HPC, HEC, HH. lia. Qed.

Theorem p5v_pend : p5v_pend_S.
Proof.
  intros rc Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP' es' hs'
    kss qs H. cbv zeta. p5v_open H.
  cbn [rv_pend view_of]. unfold pend_view, gone_pend.
  apply p5v_map_eq; [exact LHJ|]. intros i Hi. cbn [fst snd]. unfold g5_src.
  destruct (Z.eqb_spec (re_eof (nth i es no_entry)) 0) as [E0|E0]; cbv iota; [|reflexivity].
  destruct (PER i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P0 & _).
  destruct (P0 E0) as (_ & _ & _ & _ & HP & _).
  rewrite (nth_indep hs' (fst no_hj) (fst (nth i hj no_hj))) by lia. rewrite HP. reflexivity.
Qed.

Theorem p5v_ekc : p5v_ekc_S.
Proof.
  intros rc Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP' es' hs'
    kss qs H. cbv zeta. intros c _. destruct (p5v_ek_all H) as [E1 E2].
  unfold ek_c, bcnt. cbn [rv_ek view_of]. rewrite E1, E2, AllocBound.zsum_nil. lia.
Qed.

Theorem p5v_ekb : p5v_ekb_S.
Proof.
  intros rc Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP' es' hs'
    kss qs H. cbv zeta. destruct (p5v_ek_all H) as [E1 E2].
  unfold ek_b. cbn [rv_ek view_of]. rewrite E1, E2, AllocBound.zsum_nil. lia.
Qed.

Theorem p5v_wt : p5v_wt_S.
Proof.
  intros rc Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP' es' hs'
    kss qs H. cbv zeta. p5v_open H.
  set (ss := gone_states (send_live cl br dd 1) (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj) in *.
  assert (LSS : length ss = length es).
  { unfold ss, gone_states. rewrite gone_ss_len, length_combine, LHJ. lia. }
  cbn [rv_wt view_of].
  rewrite (p5v_wd_seq (combine es hj) ss (drain_init 0 0 no_entry (fst no_hj))) by (rewrite length_combine; lia).
  rewrite length_combine, LHJ, Nat.min_id.
  apply p5v_wt_gen; [exact LES' | exact LHJ | apply p5v_hj_len |].
  intros i Hi. cbv beta zeta. rewrite p5v_hj_nth by exact Hi. rewrite combine_nth by (symmetry; exact LHJ).
  cbn [fst snd]. unfold g5_src.
  destruct (PER i Hi) as (_ & _ & NDks & _ & KT & KH & RC & RU & _ & KA & P0 & P1).
  pose proof (proj1 (Forall_nth _ _) EOK' i no_entry ltac:(lia)) as (_ & _ & _ & _ & _ & _ & LU' & _).
  pose proof (proj1 (Forall_nth _ _) EOK i no_entry ltac:(lia)) as (EF & _).
  destruct (Z.eqb_spec (re_eof (nth i es no_entry)) 0) as [E0|E0]; cbv iota.
  - destruct (P0 E0) as (_ & _ & _ & _ & HP & HPC & _ & _ & _ & HX & _ & HH & _ & _ & HEC & _).
    rewrite (nth_indep hs' (fst no_hj) (fst (nth i hj no_hj))) by lia.
    rewrite (nth_indep ss (drain_init 0 0 no_entry (fst no_hj))
      (drain_init (bv_unsigned nout) (bv_unsigned cap) (nth i es no_entry) (fst (nth i hj no_hj)))) by lia.
    rewrite (p5v_el0 _ _ E0) in HX.
    pose proof (p5v_wt0 _ _ _ _ pre _ NDks KT KH RC RU KA LU' HP HPC HX HH HEC). lia.
  - assert (E1 : re_eof (nth i es no_entry) = 1) by lia.
    destruct (P1 E1) as (_ & _ & _ & RU1 & RC1).
    destruct (p5v_gs1 (send_live cl br dd 1) (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj i
      (drain_init (bv_unsigned nout) (bv_unsigned cap) (nth i es no_entry) (fst (nth i hj no_hj))) LHJ Hi E0)
      as (GH & GK & _).
    fold ss in GH, GK. rewrite GH in KH. rewrite GK in KA.
    pose proof (p5v_wt1 _ _ pre _ NDks KT KH KA RC1 RU1). lia.
Qed.

Theorem p5v_cnt : p5v_cnt_S.
Proof.
  intros rc Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP' es' hs'
    kss qs H. cbv zeta. intros c _.
  pose proof (p5v_capF H) as CF. pose proof (p5v_pl_pre H) as F1. pose proof (p5v_pl_post H) as F2.
  p5v_open H. unfold gone_dl. rewrite p5v_capT, p5v_ssT, <- CF.
  set (ss := gone_states (send_live cl br dd 1) (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj) in *.
  assert (LSS : length ss = length es).
  { unfold ss, gone_states. rewrite gone_ss_len, length_combine, LHJ. lia. }
  rewrite (p5v_cnt_view _ L A c _ ND (p5v_vpl_fst G (bv_unsigned out) (bv_unsigned cap) es hj) F1).
  rewrite (p5v_cnt_view _ L' A' c _ ND2 (p5v_vpl_fst G OUT' CAP' es' (p5c_hj es hj hs')) F2).
  pose proof (p5v_vpl_w (fun m => ncb m c) G (bv_unsigned out) (bv_unsigned cap) es hj eq_refl) as W1.
  pose proof (p5v_vpl_w (fun m => ncb m c) G OUT' CAP' es' (p5c_hj es hj hs') eq_refl) as W2.
  cbv beta in W1, W2. rewrite W1, W2.
  rewrite (p5v_dch_seq (combine es hj) ss (drain_init 0 0 no_entry (fst no_hj)) c) by (rewrite length_combine; lia).
  rewrite length_combine, LHJ, Nat.min_id.
  match goal with |- context [AllocBound.zsum ?w (seq 0 (length es))] =>
    enough (X : AllocBound.zsum (p5v_ew (fun m => ncb m c)) es +
                AllocBound.zsum (fun p => p5v_sw (fun m => ncb m c) (fst p)) hj + AllocBound.zsum w (seq 0 (length es)) <=
                AllocBound.zsum (p5v_ew (fun m => ncb m c)) es' +
                AllocBound.zsum (fun p => p5v_sw (fun m => ncb m c) (fst p)) (p5c_hj es hj hs')) by lia;
    apply p5v_sum_ge; [exact LES' | exact LHJ | apply p5v_hj_len |]
  end.
  intros i Hi. cbv beta zeta. rewrite p5v_hj_nth by exact Hi. rewrite combine_nth by (symmetry; exact LHJ).
  cbn [fst snd]. unfold g5_src.
  destruct (PER i Hi) as (_ & _ & _ & _ & _ & _ & RC & _ & _ & KA & P0 & P1).
  pose proof (proj1 (Forall_nth _ _) EOK i no_entry ltac:(lia)) as (EF & _).
  destruct (Z.eqb_spec (re_eof (nth i es no_entry)) 0) as [E0|E0]; cbv iota.
  - destruct (P0 E0) as (_ & _ & _ & _ & _ & HPC & _ & _ & _ & _ & _ & HH & _ & _ & HEC & _).
    rewrite (nth_indep hs' (fst no_hj) (fst (nth i hj no_hj))) by lia.
    rewrite (nth_indep ss (drain_init 0 0 no_entry (fst no_hj))
      (drain_init (bv_unsigned nout) (bv_unsigned cap) (nth i es no_entry) (fst (nth i hj no_hj)))) by lia.
    pose proof (p5v_pt0 (fun m => ncb m c) (nth i es no_entry) _ _ _ _ RC KA HPC HEC HH) as X. cbv beta in X.
    unfold dchain. lia.
  - assert (E1 : re_eof (nth i es no_entry) = 1) by lia.
    destruct (P1 E1) as (_ & _ & _ & _ & RC1).
    destruct (p5v_gs1 (send_live cl br dd 1) (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj i
      (drain_init (bv_unsigned nout) (bv_unsigned cap) (nth i es no_entry) (fst (nth i hj no_hj))) LHJ Hi E0)
      as (_ & GK & _).
    fold ss in GK. rewrite GK in KA. unfold p5v_ew. rewrite RC1, KA. lia.
Qed.

Theorem p5v_ncs : p5v_ncs_S.
Proof.
  intros rc Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP' es' hs'
    kss qs H. cbv zeta.
  pose proof (p5v_capF H) as CF. pose proof (p5v_pl_pre H) as F1. pose proof (p5v_pl_post H) as F2.
  p5v_open H. unfold gone_db. rewrite p5v_capT, p5v_ssT, <- CF.
  set (ss := gone_states (send_live cl br dd 1) (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj) in *.
  assert (LSS : length ss = length es).
  { unfold ss, gone_states. rewrite gone_ss_len, length_combine, LHJ. lia. }
  rewrite (p5v_ncs_view _ L A _ ND (p5v_vpl_fst G (bv_unsigned out) (bv_unsigned cap) es hj) F1).
  rewrite (p5v_ncs_view _ L' A' _ ND2 (p5v_vpl_fst G OUT' CAP' es' (p5c_hj es hj hs')) F2).
  pose proof (p5v_vpl_w (fun m => m) G (bv_unsigned out) (bv_unsigned cap) es hj eq_refl) as W1.
  pose proof (p5v_vpl_w (fun m => m) G OUT' CAP' es' (p5c_hj es hj hs') eq_refl) as W2.
  cbv beta in W1, W2. rewrite W1, W2.
  rewrite (p5v_dchb_seq (combine es hj) ss (drain_init 0 0 no_entry (fst no_hj))) by (rewrite length_combine; lia).
  rewrite length_combine, LHJ, Nat.min_id.
  match goal with |- context [AllocBound.zsum ?w (seq 0 (length es))] =>
    enough (X : AllocBound.zsum (p5v_ew (fun m => m)) es +
                AllocBound.zsum (fun p => p5v_sw (fun m => m) (fst p)) hj + AllocBound.zsum w (seq 0 (length es)) <=
                AllocBound.zsum (p5v_ew (fun m => m)) es' +
                AllocBound.zsum (fun p => p5v_sw (fun m => m) (fst p)) (p5c_hj es hj hs')) by lia;
    apply p5v_sum_ge; [exact LES' | exact LHJ | apply p5v_hj_len |]
  end.
  intros i Hi. cbv beta zeta. rewrite p5v_hj_nth by exact Hi. rewrite combine_nth by (symmetry; exact LHJ).
  cbn [fst snd]. unfold g5_src.
  destruct (PER i Hi) as (_ & _ & _ & _ & _ & _ & RC & _ & _ & KA & P0 & P1).
  pose proof (proj1 (Forall_nth _ _) EOK i no_entry ltac:(lia)) as (EF & _).
  destruct (Z.eqb_spec (re_eof (nth i es no_entry)) 0) as [E0|E0]; cbv iota.
  - destruct (P0 E0) as (_ & _ & _ & _ & _ & HPC & _ & _ & _ & _ & _ & HH & _ & _ & HEC & _).
    rewrite (nth_indep hs' (fst no_hj) (fst (nth i hj no_hj))) by lia.
    rewrite (nth_indep ss (drain_init 0 0 no_entry (fst no_hj))
      (drain_init (bv_unsigned nout) (bv_unsigned cap) (nth i es no_entry) (fst (nth i hj no_hj)))) by lia.
    pose proof (p5v_pt0 (fun m => m) (nth i es no_entry) _ _ _ _ RC KA HPC HEC HH) as X. cbv beta in X.
    unfold dchainb. lia.
  - assert (E1 : re_eof (nth i es no_entry) = 1) by lia.
    destruct (P1 E1) as (_ & _ & _ & _ & RC1).
    destruct (p5v_gs1 (send_live cl br dd 1) (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj i
      (drain_init (bv_unsigned nout) (bv_unsigned cap) (nth i es no_entry) (fst (nth i hj no_hj))) LHJ Hi E0)
      as (_ & GK & _).
    fold ss in GK. rewrite GK in KA. unfold p5v_ew. rewrite RC1, KA. lia.
Qed.

