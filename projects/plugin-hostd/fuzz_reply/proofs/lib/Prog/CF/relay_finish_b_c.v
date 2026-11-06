From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition RELAY_FINISH : Z := 0x1300c.
Definition RELAY_FINISH_FRAME : Z := 64.
Definition RELAY_FINISH_K : Z := RELAY_FINISH_FRAME + Z.max (Z.max ALLOC_STACK GESTURES_END_K) UNLOCK_STACK.
Definition G_THREAD_UP : Z := 0x30fc0.
Definition G_LISTEN : Z := 0x20d38.

(* The table's sources closed in order (relay.c:351-356), each free (s->buf) of its re_cap-byte buffer (NULL exactly
   when re_cap = 0: entry_ok) then gestures_end (s), from g_nout = no, g_capout = cap, g_out at o, nm naming the
   sources' blocks (all live at the start): the requests, the final g_capout and g_out. Every gesture_end of the run
   is live exactly when the first is (gestures_end_b_c.keys_end_run). *)
Fixpoint entries_end_run (nm : Z -> adrF) (live : bool) (mx no cap : Z) (es : list rentry) (j : nat) (o : adrF)
    : trF * (Z * adrF) :=
  match es with
  | [] => ([], (cap, o))
  | e :: r =>
      let xks := key_runs nm (re_keys e) in
      let tf := if re_cap e =? 0 then [] else [RFree (re_cap e) (nm (re_buf e))] in
      let tg := gestures_end_tr live mx no cap xks (re_hp e) (re_kh e) (j + nretF tf) o (nm (re_hp e)) in
      let p := entries_end_run nm live mx (no + keys_total (re_keys e))
                 (gestures_end_cap live mx no cap (key_lens (re_keys e))) r (j + nretF tf + nretF tg)
                 (gestures_end_out live mx no cap xks (j + nretF tf) o) in
      (tf ++ tg ++ fst p, snd p)
  end.

(* relay_finish () with no relay thread up: the sources' requests. *)
Definition relay_finish_tr (nm : Z -> adrF) (live : bool) (mx NO CAP : Z) (es : list rentry) (j : nat) (o : adrF)
    : trF :=
  fst (entries_end_run nm live mx NO CAP es j o).

(* g_capout after relay_finish (); the capacity does not depend on the addresses. *)
Definition relay_finish_cap (live : bool) (mx NO CAP : Z) (es : list rentry) : Z :=
  fst (snd (entries_end_run (fun _ => adr0) live mx NO CAP es 0 adr0)).

(* g_out after relay_finish (). *)
Definition relay_finish_out (nm : Z -> adrF) (live : bool) (mx NO CAP : Z) (es : list rentry) (j : nat) (o : adrF)
    : adrF :=
  snd (snd (entries_end_run nm live mx NO CAP es j o)).

Section FB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition relay_finish_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (es : list rentry) (C G : Z) (tail O junk : list byte)
         (lst cl br dd ei : Z) (mx nout cap out : word),
    let N := Z.of_nat (length es) in
    let TOT := entries_total es in
    let ERR := errno_addr Bm in
    let NO := bv_unsigned nout in
    let CAP := bv_unsigned cap in
    let OUT := bv_unsigned out in
    let live := send_live cl br dd TOT in
    let nm := known_at L A in
    let tr := relay_finish_tr nm live (bv_unsigned mx) NO CAP es 0 (nm OUT) in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR RELAY_FINISH_K L A regs mem md ->
    st_init_done A = true ->
    ms_tp Bm + ERRNO_OFF = ERR ->
    G_LOCK_HI <= ERR ->
    ro_agree segs mem ->
    (forall a, G_RELAY_LO <= a < G_LOCK_HI -> img_plain Bm a) ->
    (forall a, G_LISTEN <= a < G_CLIENT + 4 -> img_plain Bm a) ->
    (forall a, ERR <= a < ERR + 4 -> in_img Bm a) ->
    (forall a, END5_ADDR <= a < END5_ADDR + 5 -> img_plain Bm a) ->
    rw_cells segs mem G_THREAD_UP [C1 (Z_to_bv 8 0)] ->
    rw_cells segs mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    rw_cells segs mem G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 C)] ->
    rw_cells segs mem G_SRC [C8 (Z_to_bv 64 G)] ->
    rw_cells segs mem G_LISTEN [C4 (Z_to_bv 64 lst); C4 (Z_to_bv 64 cl)] ->
    N <= 4 ->
    ((C = 0 /\ G = 0 /\ es = []) \/
     (C = 16 /\ In (G, SRC_TABLE) (blocks L A) /\ fresh_block Bm G SRC_TABLE /\ G <> OUT /\
      ~ In G (concat (map entry_blocks es)) /\ table_at Bm mem G es tail)) ->
    Forall (entry_ok Bm L A mem) es ->
    entries_disjoint OUT es ->
    (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) -> (ei = 0 \/ ei = 1) ->
    rw_cells segs mem G_BROKEN [C1 (Z_to_bv 8 br)] ->
    rw_cells segs mem G_DEAD [C1 (Z_to_bv 8 dd)] ->
    rw_cells segs mem G_EINTR [C1 (Z_to_bv 8 ei)] ->
    rw_cells segs mem G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] ->
    (exists ev, rw_cells segs mem ERR [C4 ev]) ->
    ((CAP = 0 /\ OUT = 0 /\ NO = 0 /\ O = []) \/
     (0 < CAP /\ NO <= CAP /\ In (OUT, CAP) (blocks L A) /\ fresh_block Bm OUT CAP /\
      bytes_at segs mem OUT (O ++ junk) /\ Z.of_nat (length O) = NO /\ Z.of_nat (length junk) = CAP - NO)) ->
    2 * (NO + TOT) < 2 ^ 63 ->
    rt_ok F A bnd ->
    (forall qs, length qs = nretF tr -> roomF F qs bnd tr) ->
    let off := send_off cl br TOT in
    let br' := if off then br else dd in
    let ei' := if off then ei else 0 in
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 RELAY_FINISH) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (OUT' CAP' : Z) (junk' : list byte),
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API RELAY_FINISH_K
           (fun a => send_writes live OUT CAP a \/ G_LOCK + 4 <= a < G_LOCK + 8 \/ G_NSRC <= a < G_NSRC + 4 \/
                     G_LISTEN <= a < G_CLIENT + 4 \/ (C = 16 /\ G <= a < G + SRC_TABLE))
           (fun q => (live = true /\ q = OUT) \/ In q (concat (map entry_blocks es)))
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF tr /\ rt_ok F A' (runF F qs bnd tr) /\
            (live = true ->
               live_at L' A' (resolveF qs (relay_finish_out nm live (bv_unsigned mx) NO CAP es 0 (nm OUT))) OUT' CAP')) /\
         ro_agree segs mem' /\
         rw_cells segs mem' G_THREAD_UP [C1 (Z_to_bv 8 0)] /\
         rw_cells segs mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
         rw_cells segs mem' G_NSRC [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 C)] /\
         rw_cells segs mem' G_SRC [C8 (Z_to_bv 64 G)] /\
         rw_cells segs mem' G_LISTEN [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
         (C = 16 -> table_at Bm mem' G (map entry_cleared es) tail /\ In (G, SRC_TABLE) (blocks L' A')) /\
         rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 br')] /\
         rw_cells segs mem' G_DEAD [C1 (Z_to_bv 8 dd)] /\
         rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 ei')] /\
         (exists ev', rw_cells segs mem' ERR [C4 ev']) /\
         (forall q m, In (q, m) (blocks L' A') <->
            ((In (q, m) (blocks L A) /\ q <> OUT /\ ~ In q (concat (map entry_blocks es))) \/
             (live = true /\ q = OUT' /\ m = CAP') \/
             (live = false /\ 0 < CAP /\ q = OUT /\ m = CAP))) /\
         (live = false ->
            rw_cells segs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out]) /\
         (live = true ->
            NO + TOT <= CAP' /\ CAP' = relay_finish_cap live (bv_unsigned mx) NO CAP es /\ fresh_block Bm OUT' CAP' /\
            (forall q m, In (q, m) (blocks L A) -> q <> OUT -> ~ In q (concat (map entry_blocks es)) -> 0 < m ->
               q <> OUT') /\
            bytes_at segs mem' OUT' (O ++ entries_out es ++ junk') /\ Z.of_nat (length junk') = CAP' - NO - TOT /\
            rw_cells segs mem' G_OUTV
              [C8 mx; C8 (Z_to_bv 64 (NO + TOT)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')])).

End FB.
