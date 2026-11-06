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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Section GP.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.

Definition relay_instance_gone_contract_p : Prop :=
  forall L A regs mem md (bnd : rt_R F) (es : list rentry) (G : Z) (tail : list byte)
         (hs : list (hsrc * nat)) (fs os : list Z)
         (O junk : list byte) (cl br dd ei : Z) (mx nout cap out : word),
    let ID := bv_signed (getr regs 10) in
    let pre := instance_prefix ID in
    let N := Z.of_nat (length es) in
    let ERR := errno_addr Bm in
    let NO := bv_unsigned nout in
    let CAP := bv_unsigned cap in
    let OUT := bv_unsigned out in
    let lv := send_live cl br dd 1 in
    let nm := known_at L A in
    let tr := relay_instance_gone_tr lv (bv_unsigned mx) NO CAP pre es hs nm 0 (nm OUT) in
    let ss := gone_states lv (bv_unsigned mx) NO CAP pre es hs in
    let das := gone_adrs lv (bv_unsigned mx) NO CAP pre es hs nm 0 (nm OUT) in
    ms_segs Bm = rsegs ->
    call_pre_t Bm API RELAY_INSTANCE_GONE_K L A regs mem md ->
    st_init_done A = true ->
    ms_tp Bm + ERRNO_OFF = ERR ->
    G_LOCK_HI <= ERR ->
    ro_agree segs mem ->
    frm_zero fp_csr ->
    ms_got_guard Bm = GOT_GUARD -> ms_guard Bm = GUARD ->
    (forall a, G_RELAY_LO <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a) ->
    (forall a, G_CLIENT <= a < G_CLIENT + 4 -> img_plain Bm a) ->
    (forall a, ERR <= a < ERR + 4 -> in_img Bm a) ->
    (forall a, END5_ADDR <= a < END5_ADDR + 5 -> img_plain Bm a) ->
    - 2 ^ 31 <= ID < 2 ^ 31 ->
    rw_cells segs mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    rw_cells segs mem G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)] ->
    rw_cells segs mem G_SRC [C8 (Z_to_bv 64 G)] ->
    N <= 4 ->
    In (G, SRC_TABLE) (blocks L A) -> fresh_block Bm G SRC_TABLE -> table_at Bm mem G es tail ->
    Forall (entry_ok Bm L A mem) es ->
    NoDup (map re_fd es) ->
    length hs = length es ->
    length fs = 4%nat -> length os = 4%nat ->
    (forall i, (i < 4)%nat ->
       rw_cells segs mem (G_S + SRC_SIZE * Z.of_nat i) [C4 (Z_to_bv 64 (nth i fs 0)); C4 (Z_to_bv 64 (nth i os 0))]) ->
    (forall i i', (i < 4)%nat -> (i' < 4)%nat -> i <> i' -> nth i os 0 = 1 -> nth i' os 0 = 1 -> nth i fs 0 <> nth i' fs 0) ->
    (forall i, (i < 4)%nat -> (nth i os 0 = 0 \/ nth i os 0 = 1) /\ 0 <= nth i fs 0 < 2 ^ 31) ->
    Forall (fun p => gone_src_ok Bm L A mem G OUT es (fst p) (snd p)) (combine es hs) ->
    NoDup (G :: OUT :: concat (map entry_blocks es) ++
           concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (fst (snd p)) else []) (combine es hs))) ->
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
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 RELAY_INSTANCE_GONE) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' (OUT' CAP' : Z) (junk' LB : list byte)
                        (es' : list rentry) (hs' : list hsrc) (kss : list (list (list Z))) (tail' : list byte),
         let segsz := map (fun i => gone_segment pre (entry_lines (nth i es no_entry) (nth i hs no_hj))
                                                   (nth i kss []))
                          (seq 0 (length es)) in
         let TOT := Z.of_nat (length (concat segsz)) in
         let live := send_live cl br dd TOT in
         let off := send_off cl br TOT in
         c' = mkCfg (@YK11.mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\ frm_zero (@fp_csr fx') /\
         relay_post Bm API RELAY_INSTANCE_GONE_K
           (fun a => send_writes true OUT CAP a \/ G_LOCK + 4 <= a < G_LOCK + 8 \/
                     G <= a < G + SRC_TABLE \/ drained_area es hs a \/
                     (exists q m, In q (concat (map entry_blocks es) ++ drained_blocks es hs) /\
                                  In (q, m) (blocks L A) /\ q <= a < q + m))
           (fun q => (live = true /\ q = OUT) \/ In q (concat (map entry_blocks es)) \/ In q (drained_blocks es hs))
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF tr /\ rt_ok F A' (runF F qs bnd tr) /\
            (live = true ->
               live_at L' A' (resolveF qs (gone_out lv (bv_unsigned mx) NO CAP pre es hs nm 0 (nm OUT)))
                 OUT' CAP') /\
            (forall i, (i < length es)%nat ->
               entry_links L' A' qs (nth i das dadr0) (nth i es' no_entry) /\
               (re_eof (nth i es no_entry) = 0 ->
                  src_links L' A' qs nm (nth i das dadr0) (nth i hs' (fst (nth i hs no_hj)))))) /\
         ro_agree segs mem' /\
         rw_cells segs mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
         rw_cells segs mem' G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)] /\
         rw_cells segs mem' G_SRC [C8 (Z_to_bv 64 G)] /\ In (G, SRC_TABLE) (blocks L' A') /\
         length es' = length es /\ table_at Bm mem' G es' tail' /\
         Forall (entry_ok Bm L' A' mem') es' /\
         length kss = length es /\ length hs' = length es /\
         (forall i, (i < length es)%nat ->
            let e := nth i es no_entry in
            let e' := nth i es' no_entry in
            let ks := nth i kss [] in
            let hj := nth i hs no_hj in
            let Ls := entry_lines e hj in
            let s := nth i ss (drain_init NO CAP e (fst hj)) in
            re_fd e' = re_fd e /\
            re_eof e' = (if re_eof e =? 0 then (if hs_closed (fst hj) =? 1 then 1 else 0) else 1) /\
            NoDup ks /\ same_set ks (upds (keys_texts (re_keys e)) Ls) /\
            keys_texts (re_keys e') = snd (gei pre ks) /\
            ks = ds_H s /\ re_cap e' = ds_cap s /\ bzs (re_U e') = ds_u s /\
            re_skip e' = (if ds_skip s then 1 else 0) /\ ent_ka e' = ds_ka s /\
            (re_eof e = 0 ->
               let h := fst hj in
               let h' := nth i hs' h in
               src_at Bm L' A' mem' (G_S + SRC_SIZE * Z.of_nat (snd hj)) h' /\
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
         (forall i, (i < length es)%nat -> re_eof (nth i es no_entry) = 0 ->
            hs_partial (nth i hs' (fst (nth i hs no_hj))) = hs_partial (fst (nth i hs no_hj))) /\
         bzs LB = concat segsz /\
         rw_cells segs mem' G_CLIENT [C4 (Z_to_bv 64 cl)] /\
         rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 (if off then br else dd))] /\
         rw_cells segs mem' G_DEAD [C1 (Z_to_bv 8 dd)] /\
         rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 (if off then ei else 0))] /\
         (exists ev', rw_cells segs mem' ERR [C4 ev']) /\
         (forall i, (i < 4)%nat ->
            rw_cells segs mem' (G_S + SRC_SIZE * Z.of_nat i) [C4 (Z_to_bv 64 (nth i fs 0)); C4 (Z_to_bv 64 (nth i os 0))]) /\
         NoDup (G :: OUT' :: concat (map entry_blocks es') ++
                concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) (combine es hs'))) /\
         (forall q m, In (q, m) (blocks L A) -> q <> OUT -> ~ In q (concat (map entry_blocks es)) ->
            ~ In q (drained_blocks es hs) -> In (q, m) (blocks L' A')) /\
         (forall q m, In (q, m) (blocks L A) -> 0 < m -> q <> OUT -> ~ In q (concat (map entry_blocks es)) ->
            ~ In q (drained_blocks es hs) ->
            q <> OUT' /\ ~ In q (concat (map entry_blocks es')) /\
            ~ In q (concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) (combine es hs')))) /\
         (forall q m, In (q, m) (blocks L' A') ->
            (In (q, m) (blocks L A) /\ q <> OUT /\ ~ In q (concat (map entry_blocks es)) /\
             ~ In q (drained_blocks es hs)) \/
            In q (concat (map entry_blocks es')) \/
            In q (concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) (combine es hs'))) \/
            q = OUT') /\
         (live = false -> rw_cells segs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] /\ OUT' = OUT /\ CAP' = CAP /\
            (0 < CAP -> In (OUT, CAP) (blocks L' A') /\ bytes_at segs mem' OUT (O ++ junk))) /\
         (live = true ->
            NO + TOT <= CAP' /\ CAP' = gone_cap lv (bv_unsigned mx) NO CAP pre es hs /\
            In (OUT', CAP') (blocks L' A') /\ fresh_block Bm OUT' CAP' /\
            bytes_at segs mem' OUT' (O ++ LB ++ junk') /\ Z.of_nat (length junk') = CAP' - NO - TOT /\
            rw_cells segs mem' G_OUTV
              [C8 mx; C8 (Z_to_bv 64 (NO + TOT)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')])).

End GP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocPackGSF AllocPack3Ag.

Definition gone_partial_S (rc : YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B) : Prop :=
  forall fx' : YK11.FPState, @relay_instance_gone_contract_p fx' rc B API pack3_ag_formT.

Lemma gone_partial_of_contract : forall (rc : YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  (forall fx' : YK11.FPState, @relay_instance_gone_contract fx' rc B API pack3_ag_formT) -> gone_partial_S rc B API.
Proof.
  intros rc B API H fx'.
  unfold relay_instance_gone_contract_p.
  intros L A regs mem md bnd es G tail hs fs os O junk cl br dd ei mx nout cap out.
  pose proof (H fx' L A regs mem md bnd es G tail hs fs os O junk cl br dd ei mx nout cap out) as HC.
  cbv zeta in HC |- *.
  intros.
  eapply SR_mono; [apply HC; assumption|].
  intros c' (fx'' & L' & A' & regs' & mem' & md' & OUT' & CAP' & junk' & LB & es' & hs' & kss & tail' &
    X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & REST).
  exists fx'', L', A', regs', mem', md', OUT', CAP', junk', LB, es', hs', kss, tail'.
  do 15 (split; [assumption|]).
  split; [|split; [|exact REST]].
  - intros i Hi.
    destruct (X16 i Hi) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
    do 10 (split; [assumption|]).
    split; [|exact Y12].
    intros E0.
    destruct (Y11 E0) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14).
    do 12 (split; [assumption|]).
    exact Z14.
  - intros i Hi E0.
    destruct (X16 i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Y11 & _).
    destruct (Y11 E0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Z13 & _).
    exact Z13.
Qed.
