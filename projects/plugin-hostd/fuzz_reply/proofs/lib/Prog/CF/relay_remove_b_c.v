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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition RELAY_REMOVE : Z := 0x13a58.
Definition RELAY_REMOVE_FRAME : Z := 48.
Definition RELAY_REMOVE_K : Z :=
  RELAY_REMOVE_FRAME + Z.max (Z.max DRAIN_K GESTURES_END_K) (Z.max ALLOC_STACK UNLOCK_STACK).

Definition remove_at {X : Type} (i : nat) (l : list X) : list X :=
  match List.rev l with
  | [] => []
  | last :: rrest =>
      let pre := List.rev rrest in
      if Nat.eqb i (length pre) then pre else firstn i pre ++ last :: skipn (S i) pre
  end.

Definition no_entry : rentry := RE 0 0 0 [] 0 0 0 0 0 [] [] [] [].

(* A relay's source e (and the harness's h it reads) after `if (!s->eof) drain (s)` (relay.c:446-447, 463-464):
   drain's state when s->eof = 0, else as it was. *)
Definition after_drain (lv : bool) (mx NO CAP : Z) (e : rentry) (h : hsrc) : dstate :=
  if re_eof e =? 0 then drain_fin lv mx NO CAP e h else drain_init NO CAP e h.

(* The addresses after `if (!s->eof) drain (s)`, from base j with the addresses a. *)
Definition after_drain_adr (lv : bool) (mx NO CAP : Z) (e : rentry) (h : hsrc) (j : nat) (a : dadr) : dadr :=
  if re_eof e =? 0 then drain_adr lv mx NO CAP e h j a else a.

(* relay_remove's run on its source e (relay.c:463-467) from base j with the addresses a: drain (s) when
   s->eof = 0, gestures_end (s) (its held array is NULL exactly when ds_ka = 0, the size gestures_end_tr frees),
   then free (s->buf) (NULL exactly when s->cap = 0). lv is the liveness of a send of at least one byte: a run with
   no send asks nothing of send_line. The requests and g_out after. *)
Definition remove_entry_run (lv : bool) (mx NO CAP : Z) (e : rentry) (h : hsrc) (j : nat) (a : dadr) : trF * adrF :=
  let s := after_drain lv mx NO CAP e h in
  let a1 := after_drain_adr lv mx NO CAP e h j a in
  let td := if re_eof e =? 0 then drain_tr lv mx NO CAP e h j a else [] in
  let j1 := (j + nretF td)%nat in
  let xks := combine (map (fun x => Z.of_nat (length x)) (ds_H s)) (da_keys a1) in
  (td ++ gestures_end_tr lv mx (ds_no s) (ds_ocap s) xks (ds_ka s) (ds_ka s) j1 (da_out a1) (da_hp a1) ++
   (if ds_cap s =? 0 then [] else [RFree (ds_cap s) (da_buf a1)]),
   gestures_end_out lv mx (ds_no s) (ds_ocap s) xks j1 (da_out a1)).

Definition remove_entry_tr (lv : bool) (mx NO CAP : Z) (e : rentry) (h : hsrc) (j : nat) (a : dadr) : trF :=
  fst (remove_entry_run lv mx NO CAP e h j a).

(* g_out after relay_remove's run on its source e. *)
Definition remove_entry_out (lv : bool) (mx NO CAP : Z) (e : rentry) (h : hsrc) (j : nat) (a : dadr) : adrF :=
  snd (remove_entry_run lv mx NO CAP e h j a).

(* g_capout after relay_remove's run on its source e. *)
Definition remove_entry_cap (lv : bool) (mx NO CAP : Z) (e : rentry) (h : hsrc) : Z :=
  let s := after_drain lv mx NO CAP e h in
  gestures_end_cap lv mx (ds_no s) (ds_ocap s) (map (fun x => Z.of_nat (length x)) (ds_H s)).

(* relay_remove (fd) (relay.c:453) from base j with g_out at o, nm naming the sources' blocks: nothing for fd < 0;
   the run on the first source of fd, if any. *)
Definition relay_remove_tr (lv : bool) (mx NO CAP FD : Z) (es : list rentry) (h : hsrc) (nm : Z -> adrF) (j : nat)
    (o : adrF) : trF :=
  if FD <? 0 then [] else
  match find (fun e => re_fd e =? FD) es with
  | Some e => remove_entry_tr lv mx NO CAP e h j (drain_start nm o e h)
  | None => []
  end.

Section RB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition relay_remove_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (es : list rentry) (G : Z) (tail : list byte)
         (h : hsrc) (j : nat) (fs os : list Z)
         (O junk : list byte) (cl br dd ei : Z) (mx nout cap out : word),
    let FD := bv_signed (getr regs 10) in
    let N := Z.of_nat (length es) in
    let ERR := errno_addr Bm in
    let NO := bv_unsigned nout in
    let CAP := bv_unsigned cap in
    let OUT := bv_unsigned out in
    let HA := G_S + SRC_SIZE * Z.of_nat j in
    let PL := Z.of_nat (length (pending_stream h)) in
    let lv := send_live cl br dd 1 in
    let nm := known_at L A in
    let tr := relay_remove_tr lv (bv_unsigned mx) NO CAP FD es h nm 0 (nm OUT) in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR RELAY_REMOVE_K L A regs mem md ->
    st_init_done A = true ->
    ms_tp Bm + ERRNO_OFF = ERR ->
    G_LOCK_HI <= ERR ->
    ro_agree segs mem ->
    (forall a, G_RELAY_LO <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a) ->
    (forall a, G_LISTEN <= a < G_WAKE1 + 4 -> img_plain Bm a) ->
    (forall a, ERR <= a < ERR + 4 -> in_img Bm a) ->
    (forall a, END5_ADDR <= a < END5_ADDR + 5 -> img_plain Bm a) ->
    - 2 ^ 31 <= FD < 2 ^ 31 ->
    rw_cells segs mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    bytes_at segs mem G_WAKE1 (le4 (Z_to_bv 64 (-1))) ->
    rw_cells segs mem G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)] ->
    rw_cells segs mem G_SRC [C8 (Z_to_bv 64 G)] ->
    N <= 4 ->
    In (G, SRC_TABLE) (blocks L A) -> fresh_block Bm G SRC_TABLE -> table_at Bm mem G es tail ->
    Forall (entry_ok Bm L A mem) es ->
    NoDup (map re_fd es) ->
    NoDup (G :: OUT :: concat (map entry_blocks es)) ->
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
    (forall e, In e es -> re_fd e = FD -> re_eof e = 0 ->
       src_at Bm L A mem HA h /\ others_at Bm mem j FD fs os /\ (j < 4)%nat /\ hs_fd h = FD /\
       re_skip e = hs_overlong h /\ (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) /\
       NoDup (G :: OUT :: concat (map entry_blocks es) ++ hs_blocks h) /\
       PL < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\ re_nheld e + PL < 2 ^ 26) ->
    (forall qs, length qs = nretF tr -> roomF F qs bnd tr) ->
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 RELAY_REMOVE) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (OUT' CAP' : Z) (junk' LB : list byte)
                        (e' : rentry) (h' : hsrc) (tail' : list byte),
         (* The lines relayed from the source e and the bytes sent for it. *)
         let Lsf (e : rentry) := if re_eof e =? 0 then lines (hs_state h) (bzs (pending_stream h)) else [] in
         let TOTf (e : rentry) := Z.of_nat (length (with_nul (Lsf e))) + keys_total (re_keys e') in
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API RELAY_REMOVE_K
           (fun a => send_writes true OUT CAP a \/ G_LOCK + 4 <= a < G_LOCK + 8 \/ G_NSRC <= a < G_NSRC + 4 \/
                     G <= a < G + SRC_TABLE \/
                     ((exists e, In e es /\ re_fd e = FD /\ re_eof e = 0) /\ HA + 12 <= a < HA + SRC_SIZE) \/
                     (exists e q m, In e es /\ re_fd e = FD /\ In (q, m) (blocks L A) /\ q <= a < q + m /\
                        (In q (entry_blocks e) \/ (re_eof e = 0 /\ In q (hs_blocks h)))))
           (fun q => ((exists e, In e es /\ re_fd e = FD /\ send_live cl br dd (TOTf e) = true) /\ q = OUT) \/
                     (exists e, In e es /\ re_fd e = FD /\ (In q (entry_blocks e) \/ (re_eof e = 0 /\ In q (hs_blocks h)))))
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF tr /\ rt_ok F A' (runF F qs bnd tr) /\
            (forall i, (i < length es)%nat -> re_fd (nth i es no_entry) = FD ->
               let e := nth i es no_entry in
               let a0 := drain_start nm (nm OUT) e h in
               (send_live cl br dd (TOTf e) = true ->
                  live_at L' A' (resolveF qs (remove_entry_out lv (bv_unsigned mx) NO CAP e h 0 a0)) OUT' CAP') /\
               (re_eof e = 0 -> src_links L' A' qs nm (after_drain_adr lv (bv_unsigned mx) NO CAP e h 0 a0) h'))) /\
         ro_agree segs mem' /\
         rw_cells segs mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
         bytes_at segs mem' G_WAKE1 (le4 (Z_to_bv 64 (-1))) /\
         rw_cells segs mem' G_SRC [C8 (Z_to_bv 64 G)] /\ In (G, SRC_TABLE) (blocks L' A') /\
         rw_cells segs mem' G_CLIENT [C4 (Z_to_bv 64 cl)] /\
         (exists ev', rw_cells segs mem' ERR [C4 ev']) /\
         ((forall e, In e es -> re_fd e <> FD) ->
            rw_cells segs mem' G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)] /\
            table_at Bm mem' G es tail /\ blocks L' A' = blocks L A /\
            rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 br)] /\
            rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 ei)] /\
            rw_cells segs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out]) /\
         (forall i, (i < length es)%nat -> re_fd (nth i es no_entry) = FD ->
            let e := nth i es no_entry in
            let Ls := Lsf e in
            let TOT := TOTf e in
            let live := send_live cl br dd TOT in
            let off := send_off cl br TOT in
            let fin := drain_fin lv (bv_unsigned mx) NO CAP e h in
            rw_cells segs mem' G_NSRC [C4 (Z_to_bv 64 (N - 1)); C4 (Z_to_bv 64 16)] /\
            table_at Bm mem' G (remove_at i es) tail' /\
            re_fd e' = re_fd e /\ re_eof e' = re_eof e /\
            (re_eof e = 0 ->
               src_at Bm L' A' mem' HA h' /\ others_at Bm mem' j FD fs os /\
               hs_eintr h' = 0 /\ hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
               hl_v (hs_pending h') = hl_v (hs_pending h) /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
               hs_partial h' = hs_partial h /\
               hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
               map snd (hl_recs (hs_expected h')) =
                 map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) Ls /\
               firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
               hs_held h' = hs_held h /\
               NoDup (keys_texts (re_keys e')) /\
               same_set (keys_texts (re_keys e')) (upds (keys_texts (re_keys e)) Ls) /\
               keys_texts (re_keys e') = ds_H fin /\ hl_cap (hs_expected h') = ds_ecap fin) /\
            (re_eof e = 1 -> re_keys e' = re_keys e) /\
            bzs LB = with_nul Ls /\
            rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 (if off then br else dd))] /\
            rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 (if off then ei else 0))] /\
            (forall q m, In (q, m) (blocks L A) -> q <> OUT -> ~ In q (entry_blocks e) ->
               (re_eof e = 0 -> ~ In q (hs_blocks h)) -> In (q, m) (blocks L' A')) /\
            (forall q m, In (q, m) (blocks L A) -> 0 < m -> q <> OUT -> ~ In q (entry_blocks e) ->
               (re_eof e = 0 -> ~ In q (hs_blocks h)) ->
               q <> OUT' /\ (re_eof e = 0 -> ~ In q (hs_blocks h'))) /\
            (re_eof e = 0 -> NoDup (OUT' :: hs_blocks h')) /\
            (forall q m, In (q, m) (blocks L' A') ->
               (In (q, m) (blocks L A) /\ q <> OUT /\ ~ In q (entry_blocks e) /\
                (re_eof e = 0 -> ~ In q (hs_blocks h))) \/
               (re_eof e = 0 /\ In q (hs_blocks h')) \/ q = OUT') /\
            (live = false -> rw_cells segs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] /\
               (0 < CAP -> In (OUT, CAP) (blocks L' A') /\ bytes_at segs mem' OUT (O ++ junk)) /\ OUT' = OUT) /\
            (live = true ->
               NO + TOT <= CAP' /\ CAP' = remove_entry_cap lv (bv_unsigned mx) NO CAP e h /\
               In (OUT', CAP') (blocks L' A') /\ fresh_block Bm OUT' CAP' /\
               bytes_at segs mem' OUT' (O ++ LB ++ keys_out (re_keys e') ++ junk') /\
               Z.of_nat (length junk') = CAP' - NO - TOT /\
               rw_cells segs mem' G_OUTV
                 [C8 mx; C8 (Z_to_bv 64 (NO + TOT)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')]))).

End RB.
