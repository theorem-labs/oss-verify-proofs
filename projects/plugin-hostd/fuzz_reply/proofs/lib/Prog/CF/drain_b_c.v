From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayRunT RelayRunF RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition DRAIN : Z := 0x135d0.
Definition DRAIN_FRAME : Z := 128.
Definition DRAIN_K : Z := DRAIN_FRAME + SEND_LINE_K.

Definition keys_texts (ks : list (Z * list byte * list byte)) : list (list Z) := map (fun k => bzs (key_text k)) ks.

(* The size of a source's held array, 0 when s->held is NULL. *)
Definition ent_ka (e : rentry) : Z := if re_hp e =? 0 then 0 else re_kh e.

(* drain's buffer growth when fewer than 4096 bytes are free (relay.c:178-194): to cap ? cap * 2 : 8192 with realloc
   (realloc (NULL, ...) when cap = 0, else of the cap-byte block at b). The requests, the capacity and the buffer
   after. *)
Definition grow_tr (cap used : Z) (j : nat) (b : adrF) : trF * (Z * adrF) :=
  if cap - used <? 4096 then
    let c := if cap =? 0 then 8192 else cap * 2 in ([if cap =? 0 then RMalloc c else RRealloc cap c b], (c, Ret j))
  else ([], (cap, b)).

(* gesture_seen (s, line) (relay.c:89-121) with the held keys H in array order in an array of ka bytes (0: NULL) at
   ha, the keys at ks (in H's order): a begin not held grows the array to (nheld + 1) * 8 with realloc, then
   strndup's the key (|key| + 1 bytes), appended; an end held frees its key, the last key taking its place. The
   requests, the array's size after, and the array's and the keys' addresses after; RelayKeys.seen_arr is the keys
   after. *)
Definition seen_tr (H : list (list Z)) (ka : Z) (l : list Z) (j : nat) (ha : adrF) (ks : list adrF)
    : trF * Z * (adrF * list adrF) :=
  match gesture l with
  | Some (GBegin, x) =>
      match index_of x H with
      | Some _ => ([], ka, (ha, ks))
      | None =>
          let c := (Z.of_nat (length H) + 1) * 8 in
          ([if ka =? 0 then RMalloc c else RRealloc ka c ha; RMalloc (Z.of_nat (length x) + 1)], c,
           (Ret j, ks ++ [Ret (S j)]))
      end
  | Some (GEnd, x) =>
      match index_of x H with
      | Some n => ([RFree (Z.of_nat (length x) + 1) (nth n ks adr0)], ka, (ha, swap_remove adr0 n ks))
      | None => ([], ka, (ha, ks))
      end
  | None => ([], ka, (ha, ks))
  end.

(* The capacity of a harness list after list_push on n texts in an array of cap (fuzz_reply.c:132-142). *)
Definition push_cap (n cap : Z) : Z := if n =? cap then (if cap =? 0 then 8 else cap * 2) else cap.

(* The lines ls relayed in order (relay.c:207-213), each send_line (line, |line| + 1) then gesture_seen, from
   g_nout = no, g_capout = cap, g_out at o, held keys H at ks in an array of ka bytes at ha: the requests,
   (g_capout, keys, array size) after and (g_out, array, keys) addresses after. Every send_line of a drain is live
   exactly when the first is (gestures_end_b_c.keys_end_run). *)
Fixpoint lines_run (live : bool) (mx no cap : Z) (H : list (list Z)) (ka : Z) (ls : list (list Z))
    (j : nat) (o ha : adrF) (ks : list adrF) : trF * (Z * list (list Z) * Z) * (adrF * adrF * list adrF) :=
  match ls with
  | [] => ([], (cap, H, ka), (o, ha, ks))
  | l :: r =>
      let len := Z.of_nat (length l) + 1 in
      let t1 := send_line_tr live mx no cap len j o in
      let sn := seen_tr H ka l (j + nretF t1) ha ks in
      let p := lines_run live mx (no + len) (send_line_cap live mx no cap len) (seen_arr H l) (snd (fst sn)) r
                 (j + nretF t1 + nretF (fst (fst sn))) (send_line_out live mx no cap len j o) (fst (snd sn))
                 (snd (snd sn)) in
      (t1 ++ fst (fst sn) ++ fst (fst p), snd (fst p), snd p)
  end.

(* What a drain changes: the relay's source (s->cap, s->buf [0, s->used), s->skip, the held keys in array order and
   the array's size, 0 when NULL), the harness's source (eintr, the pending texts and pending_off, the reference
   splitter, the expected list's length and capacity), and g_nout, g_capout. *)
Record dstate := DS {
  ds_cap : Z; ds_u : list Z; ds_skip : bool; ds_H : list (list Z); ds_ka : Z;
  ds_eintr : bool; ds_pend : list (list Z); ds_off : Z; ds_ref : lstate; ds_en : Z; ds_ecap : Z;
  ds_no : Z; ds_ocap : Z }.

Definition drain_init (NO CAP : Z) (e : rentry) (h : hsrc) : dstate :=
  DS (re_cap e) (bzs (re_U e)) (re_skip e =? 1) (keys_texts (re_keys e)) (ent_ka e)
     (hs_eintr h =? 1) (map (fun r => bzs (snd r)) (hl_recs (hs_pending h))) (hs_off h) (hs_state h)
     (hl_n (hs_expected h)) (hl_cap (hs_expected h)) NO CAP.

(* The addresses of the blocks a drain touches: g_out, s->buf, s->held, the held keys (in ds_H's order), the pending
   texts' blocks (in ds_pend's order), the expected list's array and its texts' blocks (in the list's order). *)
Record dadr := DA {
  da_out : adrF; da_buf : adrF; da_hp : adrF; da_keys : list adrF;
  da_pend : list adrF; da_ev : adrF; da_erecs : list adrF }.

(* The addresses at a drain's start: g_out at o, the blocks of the sources e and h named by nm. *)
Definition drain_start (nm : Z -> adrF) (o : adrF) (e : rentry) (h : hsrc) : dadr :=
  DA o (nm (re_buf e)) (nm (re_hp e)) (map (fun k => nm (key_addr k)) (re_keys e))
     (map (fun r => nm (fst r)) (hl_recs (hs_pending h))) (nm (hl_v (hs_expected h)))
     (map (fun r => nm (fst r)) (hl_recs (hs_expected h))).

(* Placeholder addresses, for the model values, which do not depend on the addresses. *)
Definition dadr0 : dadr := DA adr0 adr0 adr0 [] [] adr0 [].

(* reference_feed's pushes of the lines ls onto the expected list of n texts in an array of cap at v, its texts at rs
   (fuzz_reply.c:226), each list_push's requests ListTr.list_push_tra (the grown array first when n = cap, push_cap,
   the text's block last): the requests, the capacity after, and the array's and the texts' addresses after. *)
Fixpoint pushes_run (n cap : Z) (ls : list (list Z)) (j : nat) (v : adrF) (rs : list adrF)
    : trF * Z * (adrF * list adrF) :=
  match ls with
  | [] => ([], cap, (v, rs))
  | l :: r =>
      let t := list_push_tra v n cap (Z.of_nat (length l)) in
      let j' := (j + nretF t)%nat in
      let p := pushes_run (n + 1) (push_cap n cap) r j' (if n =? cap then Ret j else v) (rs ++ [Ret (Nat.pred j')]) in
      (t ++ fst (fst p), snd (fst p), snd p)
  end.

(* drain's rounds (relay.c:173-223) from base j with the addresses a: the buffer's growth, then recv
   (fuzz_reply.c:240-276): an EINTR round requests nothing more; no pending text ends the drain (EAGAIN, or 0 for a
   closed source); else recv takes n = min (the head text's rest, cap - used) bytes d, whose lines the reference
   pushes onto the expected list, and drops the head text once it is all read (list_drop, ListTr.list_drop_tra);
   then the relay relays d's complete lines (RelayModel.chunk). The requests, the state and the addresses after.
   Each data round reads at least one byte, so |pending| + 2 rounds are enough. *)
Fixpoint drain_run (fuel : nat) (live : bool) (mx : Z) (s : dstate) (j : nat) (a : dadr) : trF * (dstate * dadr) :=
  match fuel with
  | O => ([], (s, a))
  | S f =>
      let used := Z.of_nat (length (ds_u s)) in
      let g := grow_tr (ds_cap s) used j (da_buf a) in
      let cap := fst (snd g) in
      let j1 := (j + nretF (fst g))%nat in
      let s1 := DS cap (ds_u s) (ds_skip s) (ds_H s) (ds_ka s) false (ds_pend s) (ds_off s) (ds_ref s)
                   (ds_en s) (ds_ecap s) (ds_no s) (ds_ocap s) in
      let a1 := DA (da_out a) (snd (snd g)) (da_hp a) (da_keys a) (da_pend a) (da_ev a) (da_erecs a) in
      if ds_eintr s then let p := drain_run f live mx s1 j1 a1 in (fst g ++ fst p, snd p) else
      match ds_pend s with
      | [] => (fst g, (s1, a1))
      | r0 :: rs =>
          let n := Z.min (Z.of_nat (length r0) - ds_off s) (cap - used) in
          if n <=? 0 then (fst g, (s1, a1)) else
          let d := firstn (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0) in
          let ls := lines (ds_ref s) d in
          let pu := pushes_run (ds_en s) (ds_ecap s) ls j1 (da_ev a) (da_erecs a) in
          let whole := ds_off s + n =? Z.of_nat (length r0) in
          let td := if whole then list_drop_tra (nth 0 (da_pend a) adr0) (Z.of_nat (length r0)) else [] in
          let j3 := (j1 + nretF (fst (fst pu)) + nretF td)%nat in
          let '(u', sk', rl) := chunk (ds_u s) (ds_skip s) d in
          let sl := lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 (da_out a) (da_hp a) (da_keys a) in
          let '(oc', H', ka') := snd (fst sl) in
          let '(o', ha', ks') := snd sl in
          let s2 := DS cap u' sk' H' ka' false (if whole then rs else ds_pend s) (if whole then 0 else ds_off s + n)
                       (feed (ds_ref s) d) (ds_en s + Z.of_nat (length ls)) (snd (fst pu))
                       (ds_no s + Z.of_nat (length (with_nul rl))) oc' in
          let a2 := DA o' (snd (snd g)) ha' ks' (if whole then skipn 1 (da_pend a) else da_pend a) (fst (snd pu))
                       (snd (snd pu)) in
          let p := drain_run f live mx s2 (j3 + nretF (fst (fst sl))) a2 in
          (fst g ++ fst (fst pu) ++ td ++ fst (fst sl) ++ fst p, snd p)
      end
  end.

(* drain (s) of the relay's source e reading the harness's source h, from g_nout = NO, g_capout = CAP, base j and
   addresses a: the requests, the state and the addresses it leaves. *)
Definition drain_go (live : bool) (mx NO CAP : Z) (e : rentry) (h : hsrc) (j : nat) (a : dadr) : trF * (dstate * dadr) :=
  drain_run (S (S (length (pending_stream h)))) live mx (drain_init NO CAP e h) j a.

Definition drain_tr (live : bool) (mx NO CAP : Z) (e : rentry) (h : hsrc) (j : nat) (a : dadr) : trF :=
  fst (drain_go live mx NO CAP e h j a).

(* The state drain (s) leaves. *)
Definition drain_fin (live : bool) (mx NO CAP : Z) (e : rentry) (h : hsrc) : dstate :=
  fst (snd (drain_go live mx NO CAP e h 0 dadr0)).

(* The addresses drain (s) leaves. *)
Definition drain_adr (live : bool) (mx NO CAP : Z) (e : rentry) (h : hsrc) (j : nat) (a : dadr) : dadr :=
  snd (snd (drain_go live mx NO CAP e h j a)).

(* A relay source e's blocks at the addresses fa resolved by qs: its buffer, held array and held keys (in order). *)
Definition entry_links (L : layout) (A : astate) (qs : list sptr) (fa : dadr) (e : rentry) : Prop :=
  (0 < re_cap e -> live_at L A (resolveF qs (da_buf fa)) (re_buf e) (re_cap e)) /\
  (re_hp e <> 0 -> live_at L A (resolveF qs (da_hp fa)) (re_hp e) (re_kh e)) /\
  Forall2 (fun k a => live_at L A (resolveF qs a) (key_addr k) (Z.of_nat (length (key_text k)) + 1))
    (re_keys e) (da_keys fa).

(* A harness source h's expected list at the addresses fa resolved by qs: its array and its texts' blocks. *)
Definition expected_links (L : layout) (A : astate) (qs : list sptr) (fa : dadr) (h : hsrc) : Prop :=
  (0 < hl_cap (hs_expected h) ->
     live_at L A (resolveF qs (da_ev fa)) (hl_v (hs_expected h)) (16 * hl_cap (hs_expected h))) /\
  Forall2 (fun r a => live_at L A (resolveF qs a) (fst r) (Z.of_nat (length (snd r)) + 1))
    (hl_recs (hs_expected h)) (da_erecs fa).

(* All of a harness source h's blocks (HarnessRep.hs_blocks) at their addresses resolved by qs: the pending list's
   array, the partial block and the held list's array and texts, untouched since the entry and named by nm there;
   the pending texts at da_pend fa; the expected list at the addresses fa (expected_links). *)
Definition src_links (L : layout) (A : astate) (qs : list sptr) (nm : Z -> adrF) (fa : dadr) (h : hsrc) : Prop :=
  (0 < hl_cap (hs_pending h) ->
     live_at L A (resolveF qs (nm (hl_v (hs_pending h)))) (hl_v (hs_pending h)) (16 * hl_cap (hs_pending h))) /\
  Forall2 (fun r a => live_at L A (resolveF qs a) (fst r) (Z.of_nat (length (snd r)) + 1))
    (hl_recs (hs_pending h)) (da_pend fa) /\
  live_at L A (resolveF qs (nm (hs_partial h))) (hs_partial h) 6000 /\
  expected_links L A qs fa h /\
  (0 < hl_cap (hs_held h) ->
     live_at L A (resolveF qs (nm (hl_v (hs_held h)))) (hl_v (hs_held h)) (16 * hl_cap (hs_held h))) /\
  Forall (fun r => live_at L A (resolveF qs (nm (fst r))) (fst r) (Z.of_nat (length (snd r)) + 1))
    (hl_recs (hs_held h)).

Section DB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition others_at (mem : word -> option byte) (j : nat) (fd : Z) (fs os : list Z) : Prop :=
  length fs = 4%nat /\ length os = 4%nat /\
  forall i, (i < 4)%nat -> i <> j ->
    rw_cells segs mem (G_S + SRC_SIZE * Z.of_nat i) [C4 (Z_to_bv 64 (nth i fs 0)); C4 (Z_to_bv 64 (nth i os 0))] /\
    (nth i os 0 = 0 \/ nth i fs 0 <> fd) /\ 0 <= nth i fs 0 < 2 ^ 31.

Definition drain_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (e : rentry) (h : hsrc) (j : nat) (fs os : list Z)
         (G : Z) (O junk : list byte) (cl br dd ei : Z) (mx nout cap out : word),
    let SA := bv_unsigned (getr regs 10) in
    let HA := G_S + SRC_SIZE * Z.of_nat j in
    let P := pending_stream h in
    let st := hs_state h in
    let Ls := lines st (bzs P) in
    let TOT := Z.of_nat (length (with_nul Ls)) in
    let PL := Z.of_nat (length P) in
    let ERR := errno_addr Bm in
    let NO := bv_unsigned nout in
    let CAP := bv_unsigned cap in
    let OUT := bv_unsigned out in
    let live := send_live cl br dd TOT in
    let a0 := drain_start (known_at L A) (known_at L A OUT) e h in
    let tr := drain_tr live (bv_unsigned mx) NO CAP e h 0 a0 in
    let fin := drain_fin live (bv_unsigned mx) NO CAP e h in
    let fa := drain_adr live (bv_unsigned mx) NO CAP e h 0 a0 in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR DRAIN_K L A regs mem md ->
    st_init_done A = true ->
    ms_tp Bm + ERRNO_OFF = ERR ->
    G_LOCK_HI <= ERR ->
    ro_agree segs mem ->
    (forall a, G_RELAY_LO <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a) ->
    (forall a, G_CLIENT <= a < G_CLIENT + 4 -> img_plain Bm a) ->
    (forall a, ERR <= a < ERR + 4 -> in_img Bm a) ->
    (j < 4)%nat ->
    In (G, SRC_TABLE) (blocks L A) /\ fresh_block Bm G SRC_TABLE /\ G <= SA /\ SA + SRC_ENTRY <= G + SRC_TABLE /\
      (SA - G) mod SRC_ENTRY = 0 ->
    rw_cells segs mem SA [CB 56%nat (entry_bytes e)] ->
    entry_ok Bm L A mem e ->
    src_at Bm L A mem HA h ->
    others_at mem j (re_fd e) fs os ->
    hs_fd h = re_fd e ->
    re_skip e = hs_overlong h ->
    (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
    NoDup (G :: OUT :: entry_blocks e ++ hs_blocks h) ->
    PL < 2 ^ 26 -> hl_cap (hs_expected h) < 2 ^ 26 -> re_nheld e + PL < 2 ^ 26 ->
    (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) -> (ei = 0 \/ ei = 1) ->
    rw_cells segs mem G_CLIENT [C4 (Z_to_bv 64 cl)] ->
    rw_cells segs mem G_BROKEN [C1 (Z_to_bv 8 br)] ->
    rw_cells segs mem G_DEAD [C1 (Z_to_bv 8 dd)] ->
    rw_cells segs mem G_EINTR [C1 (Z_to_bv 8 ei)] ->
    rw_cells segs mem G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] ->
    (exists ev, rw_cells segs mem ERR [C4 ev]) ->
    ((CAP = 0 /\ OUT = 0 /\ NO = 0 /\ O = []) \/
     (0 < CAP /\ NO <= CAP /\ In (OUT, CAP) (blocks L A) /\ fresh_block Bm OUT CAP /\
      bytes_at segs mem OUT (O ++ junk) /\ Z.of_nat (length O) = NO /\ Z.of_nat (length junk) = CAP - NO)) ->
    rt_ok F A bnd ->
    (forall qs, length qs = nretF tr -> roomF F qs bnd tr) ->
    let off := send_off cl br TOT in
    let br' := if off then br else dd in
    let ei' := if off then ei else 0 in
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 DRAIN) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (e' : rentry) (h' : hsrc) (OUT' CAP' : Z) (junk' LB : list byte),
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API DRAIN_K
           (fun a => send_writes live OUT CAP a \/ SA <= a < SA + SRC_ENTRY \/ HA + 12 <= a < HA + SRC_SIZE \/
                     (exists q m, In q (entry_blocks e ++ hs_blocks h) /\ In (q, m) (blocks L A) /\ q <= a < q + m))
           (fun q => (live = true /\ q = OUT) \/ In q (entry_blocks e ++ hs_blocks h))
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF tr /\ rt_ok F A' (runF F qs bnd tr) /\
            (live = true -> live_at L' A' (resolveF qs (da_out fa)) OUT' CAP') /\
            entry_links L' A' qs fa e' /\ src_links L' A' qs (known_at L A) fa h') /\
         ro_agree segs mem' /\
         rw_cells segs mem' SA [CB 56%nat (entry_bytes e')] /\
         entry_ok Bm L' A' mem' e' /\
         src_at Bm L' A' mem' HA h' /\
         others_at mem' j (re_fd e) fs os /\
         re_fd e' = re_fd e /\
         re_eof e' = (if hs_closed h =? 1 then 1 else re_eof e) /\
         0 < re_cap e' /\
         re_cap e' = ds_cap fin /\ bzs (re_U e') = ds_u fin /\ re_skip e' = (if ds_skip fin then 1 else 0) /\
         keys_texts (re_keys e') = ds_H fin /\ ent_ka e' = ds_ka fin /\ hl_cap (hs_expected h') = ds_ecap fin /\
         ((re_hp e' = re_hp e /\ re_kh e' = re_kh e) \/ re_kh e' <= 2 ^ 30) /\
         hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h'))) /\
         hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\ hs_eintr h' = 0 /\
         hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
         hl_v (hs_pending h') = hl_v (hs_pending h) /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
         hs_partial h' = hs_partial h /\
         hs_state h' = feed st (bzs P) /\
         map snd (hl_recs (hs_expected h')) =
           map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) Ls /\
         firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
         hs_held h' = hs_held h /\
         re_skip e' = hs_overlong h' /\
         (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
         NoDup (keys_texts (re_keys e')) /\
         same_set (keys_texts (re_keys e')) (upds (keys_texts (re_keys e)) Ls) /\
         NoDup (G :: OUT' :: entry_blocks e' ++ hs_blocks h') /\
         In (G, SRC_TABLE) (blocks L' A') /\
         (forall q m, In (q, m) (blocks L A) -> q <> OUT -> ~ In q (entry_blocks e ++ hs_blocks h) ->
            In (q, m) (blocks L' A')) /\
         (forall q m, In (q, m) (blocks L' A') ->
            (In (q, m) (blocks L A) /\ q <> OUT /\ ~ In q (entry_blocks e) /\ ~ In q (hs_blocks h)) \/
            In q (entry_blocks e' ++ hs_blocks h') \/ q = OUT') /\
         (forall q m, In (q, m) (blocks L A) -> 0 < m -> q <> OUT -> ~ In q (entry_blocks e ++ hs_blocks h) ->
            q <> OUT' /\ ~ In q (entry_blocks e') /\ ~ In q (hs_blocks h')) /\
         rw_cells segs mem' G_CLIENT [C4 (Z_to_bv 64 cl)] /\
         rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 br')] /\
         rw_cells segs mem' G_DEAD [C1 (Z_to_bv 8 dd)] /\
         rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 ei')] /\
         (exists ev', rw_cells segs mem' ERR [C4 ev']) /\
         bzs LB = with_nul Ls /\
         (live = false -> rw_cells segs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] /\
            (0 < CAP -> In (OUT, CAP) (blocks L' A') /\ bytes_at segs mem' OUT (O ++ junk)) /\ OUT' = OUT) /\
         (live = true ->
            NO + TOT <= CAP' /\ CAP' = ds_ocap fin /\ In (OUT', CAP') (blocks L' A') /\ fresh_block Bm OUT' CAP' /\
            bytes_at segs mem' OUT' (O ++ LB ++ junk') /\ Z.of_nat (length junk') = CAP' - NO - TOT /\
            rw_cells segs mem' G_OUTV
              [C8 mx; C8 (Z_to_bv 64 (NO + TOT)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')])).

End DB.
