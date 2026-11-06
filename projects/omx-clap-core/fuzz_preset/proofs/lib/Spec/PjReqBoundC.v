(* omx-clap-core/fuzz_preset: check_round_trip's largest single request, against the harness allocator's request
   bound. Nothing here is a function's proof (rule 24); kind: statement text.

   ASKED BY a Theorem Labs lane's LLVMFuzzerTestOneInput walk (a conjunct of ec_req_bound):
     forall x t, |x| <= 0x300000 -> ck_read x = Some t -> RQ_crt t + cf_head < cf_malloc_max
   with cf_head = 16 (the kit lib/A/CfParamsPreset.v; the CfParams field of lib/Reusable/YGcfNames.v) and cf_malloc_max =
   402,653,184 = 3 * 2 ^ 27 = 2 ^ 28 + 2 ^ 27, the preset owner's FINAL value (a Theorem Labs lane 2026-10-29 15:39Z, after
   a Theorem Labs lane's landing 1; it replaces 2 ^ 29 - 2 ^ 20). 0x300000 = MAXB (PresetReqAt.v:86; the harness's size gate
   fuzz_preset.c:806). rq_crt_abs states the parameter-free bound RQ_crt t + cf_head <= 352,321,446, so any later
   value of cf_malloc_max above it is one lia step.

   THE TERMS are the kit's (walkkit-next 99f596897b85, lib/A/PRH_FnCheck.v:178-220 and :377-406, PRH_FnPj.v:184-191,
   PRH_Charge.v:70, PRH_FnWriter.v:104, PRH_Reader.v:28 and :189, PRH_Base.v:178), copied below with their bodies;
   ck_strtod is the kit's prh_jr_strtod, and ReaderRes.jr_strtod is the same term (ck_strtod_res, by conversion).

   THE MEASUREMENT (X = |x| <= MAXB = 3,145,728). Proved bound, its value at MAXB, and the largest value a Python
   copy of the model (reader, writer, tvp, pj_set_model; agreeing with rq_rows below) reached on four adversarial
   inputs at X = MAXB (a 32-deep array of zeros; a flat array of 1,572,863 zeros; an object of 629,145 members "":0;
   a string of 1,572,863 "\b", each written \u0008):
     component                          proved bound      at MAXB        reached       lemma
     prhWriter_WMAX (in both RQ_rtt)    2 ^ 28            268,435,456    268,435,456   - (a constant)
     TX_req t false = 2 (wlen + 1)      6 X + 2            18,874,370     18,874,362   SlotSizes.wlen_false_read
     TX_req t true  = 2 (wlen + 1)      112 X - 106       352,321,430    210,763,712   SlotSizes.wlen_true_read
     RQ_pj_parse (wdoc t p), both p     2 ^ 27 - 16       134,217,712    117,440,512   rq_readback_2_27
     56 * cap2R (ck_members t)          56 X + 448        176,161,216     70,464,240   PjReqBoundW.set_grow_read
     |ck_STAMP| + 1                     21                         21             21   -
     RQ_pj_parse (wdoc (crt t) true)    2 ^ 27 - 16       134,217,712    117,440,512   rq_readback_2_27
   The binding proved bound is TX_req t true (rendered()'s last tx_put, pretty): 352,321,430 + 16 = 352,321,446, a
   margin of 50,331,738 below 402,653,184. ck_tx_len t p is wlen t p (ck_tx_len_wlen: TvSpec.tvp_concat). The
   read-back is NOT bounded through PjReqBoundW.rq_wdoc_read (168 X + 448 = 528,482,752, above 402,653,184) but
   through PjRoundTrip.G9_trace (the read-back of wdoc t p has the trace ttrace t) and SlotSizes.ez_ev / set_ez (every
   event of ttrace t and of ttrace (crt_tree t) has esize + 16 <= 2 ^ 27 when |x| <= 3 * 2 ^ 20).
   The values reached: the pretty text is at most about 33.5 X (a 32-deep array of zeros, 3,145,727 bytes: each "0,"
   of x is a 67-byte line, wlen t true = 105,381,855), so TX_req t true stays below 2 ^ 28 and RQ_crt t is 2 ^ 28
   (WMAX) at every input measured; the read-back's largest request is a container's grow, 56 * 2 ^ 21 = 117,440,512
   for an array of more than 2 ^ 20 items. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjWriteHyp SlotSizes check_round_trip_c
  TxModel TvSpec ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjReqBoundW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require FloatScan.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ The kit's terms, bodies copied *)

(* PRH_Base.v:178 *)
Definition zmaxl (l : list Z) : Z := fold_right Z.max 0 l.

(* PRH_Reader.v:28 prh_jr_strtod; ReaderRes.v:58 jr_strtod is the same term *)
Definition ck_strtod (txt : list Z) : Z * Z :=
  match FloatScan.scan_strtod (txt ++ [0]) with
  | Some (bits, c) => (c, bits)
  | None => (0, 0)
  end.

Lemma ck_strtod_res : ck_strtod = ReaderRes.jr_strtod.
Proof. reflexivity. Qed.

(* PRH_FnCheck.v:180 *)
Definition ck_read (x : list Z) : option jv := json_read ck_strtod x.

(* PRH_Charge.v:70 *)
Definition prh_maxreq (tr : list ev) : Z := fold_right Z.max 0 (map (fun e => Z.of_nat (esize e)) tr).

(* PRH_FnPj.v:184, :191 *)
Definition RQ_pj_parse (tl : list Z) : Z := prh_maxreq (snd (jr_run ck_strtod tl [])).

(* PRH_FnWriter.v:104 *)
Definition prhWriter_WMAX : Z := 2 ^ 28.

(* PRH_FnCheck.v:208-209, :378 *)
Definition ck_rtt_ns (t : jv) (p : bool) : list Z := [0] ++ TxModel.tv_calls t p 0 ++ (if p then [1] else []).
Definition ck_tx_len (t : jv) (p : bool) : Z := TxModel.zsum (ck_rtt_ns t p).
Definition TX_req (t : jv) (p : bool) : Z := 2 * (ck_tx_len t p + 1).

(* PRH_FnCheck.v:212-220 *)
Definition ck_MOD_AT : list Z := [109; 111; 100; 105; 102; 105; 101; 100; 65; 116].
Definition ck_STAMP : list Z := [50; 48; 50; 54; 45; 49; 48; 45; 50; 53; 84; 48; 48; 58; 48; 48; 58; 48; 48; 90].
Definition ck_crt_tree (t : jv) : jv :=
  match t with
  | JObj ms => JObj (pj_set_model ms ck_MOD_AT (JStr ck_STAMP))
  | _ => t
  end.
Definition ck_members (t : jv) : Z := match t with JObj ms => Z.of_nat (length ms) | _ => 0 end.

(* PRH_Reader.v:189 *)
Definition cap2R (cap : Z) : Z := if cap =? 0 then 8 else 2 * cap.

(* PRH_FnCheck.v:394-406 *)
Definition RQ_rtt (t : jv) (p : bool) : Z := zmaxl [prhWriter_WMAX; TX_req t p; RQ_pj_parse (wdoc t p)].
Definition RQ_crt (t : jv) : Z :=
  zmaxl [RQ_rtt t false; RQ_rtt t true; 56 * cap2R (ck_members t); Z.of_nat (length ck_STAMP) + 1;
         RQ_pj_parse (wdoc (ck_crt_tree t) true)].

(* CfParamsPreset.v: the preset instance's cf_head (the harness's HEAD) *)
Definition cf_head : Z := 16.
(* the preset owner's FINAL value (a Theorem Labs lane 2026-10-29 15:39Z, a Theorem Labs lane's landing 1): 3 * 2 ^ 27 *)
Definition cf_malloc_max : Z := 402653184.

(* ================================================================ the copies against the lemmas' terms *)

Lemma ck_crt_tree_eq : forall t, ck_crt_tree t = check_round_trip_c.crt_tree t.
Proof. intros t. rewrite PjReqBoundW.crt_tree_form. destruct t; reflexivity. Qed.

(* rendered()'s total is the text's length *)
Lemma ck_tx_len_wlen : forall t p, ck_tx_len t p = PjWriteHyp.wlen t p.
Proof.
  intros t p. unfold ck_tx_len, ck_rtt_ns, TxModel.tv_calls, PjWriteHyp.wlen, wdoc, wdpieces.
  rewrite !TxModel.zsum_app, TxModel.zsum_plen, TvSpec.tvp_concat, concat_app, length_app.
  destruct p; cbn [TxModel.zsum concat app length]; lia.
Qed.

(* ================================================================ the read-back (a Theorem Labs lane's F2 glue) *)

(* every request of the granted reading of wdoc t p, and of wdoc (crt_tree t) true, plus the harness head, is at
   most 2 ^ 27: G9_trace makes the trace ttrace t (ttrace (crt_tree t)), and SlotSizes bounds each event of it *)
Theorem rq_readback_2_27 : forall sm x t, json_read sm x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  forall e, (exists p, In e (snd (jr_run sm (wdoc t p) []))) \/
            In e (snd (jr_run sm (wdoc (check_round_trip_c.crt_tree t) true) [])) ->
  Z.of_nat (esize e) + 16 <= 2 ^ 27.
Proof.
  intros sm x t H HN e [[p He]|He].
  - rewrite (G9_trace sm t (wf_read sm x t H) p) in He.
    exact (SlotSizes.ez_ev t (SlotSizes.read_ez sm x t H HN) e He).
  - rewrite (G9_trace sm _ (PjReqBoundW.crt_wf_sm sm x t H) true) in He.
    pose proof (SlotSizes.s_read sm x t H) as Sz. pose proof (SlotSizes.szok_ez _ _ Sz HN) as Ez.
    rewrite PjReqBoundW.crt_tree_form in He.
    destruct t as [| | | | | | ms]; try exact (SlotSizes.ez_ev _ Ez e He).
    refine (SlotSizes.ez_ev _ (SlotSizes.set_ez ms check_round_trip_c.MOD_AT check_round_trip_c.STAMP
      (length x) Sz HN _ _) e He).
    + pose proof (SlotSizes.fme_le check_round_trip_c.MOD_AT) as F.
      unfold check_round_trip_c.MOD_AT in *. cbn [length] in F. lia.
    + pose proof (SlotSizes.fme_le check_round_trip_c.STAMP) as F.
      unfold check_round_trip_c.STAMP in *. cbn [length] in F. lia.
Qed.

Lemma rq_parse_readback : forall x t, ck_read x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  (forall p, RQ_pj_parse (wdoc t p) + 16 <= 2 ^ 27) /\ RQ_pj_parse (wdoc (ck_crt_tree t) true) + 16 <= 2 ^ 27.
Proof.
  intros x t H HN. unfold ck_read in H. split.
  - intros p. unfold RQ_pj_parse, prh_maxreq.
    enough (fold_right Z.max 0 (map (fun e => Z.of_nat (esize e)) (snd (jr_run ck_strtod (wdoc t p) [])))
      <= 2 ^ 27 - 16) by lia.
    apply PjReqBoundW.maxreq_le; [lia|]. intros e He.
    pose proof (rq_readback_2_27 ck_strtod x t H HN e (or_introl (ex_intro _ p He))). lia.
  - rewrite ck_crt_tree_eq. unfold RQ_pj_parse, prh_maxreq.
    enough (fold_right Z.max 0 (map (fun e => Z.of_nat (esize e))
      (snd (jr_run ck_strtod (wdoc (check_round_trip_c.crt_tree t) true) []))) <= 2 ^ 27 - 16) by lia.
    apply PjReqBoundW.maxreq_le; [lia|]. intros e He.
    pose proof (rq_readback_2_27 ck_strtod x t H HN e (or_intror He)). lia.
Qed.

(* ================================================================ the bound *)

(* the parameter-free bound: the largest proved component is TX_req t true <= 112 * 0x300000 - 106 *)
Theorem rq_crt_abs : forall x t, Z.of_nat (length x) <= 0x300000 -> ck_read x = Some t ->
  RQ_crt t + cf_head <= 352321446.
Proof.
  intros x t HN H.
  assert (HN' : Z.of_nat (length x) <= 3 * 2 ^ 20) by lia.
  destruct (rq_parse_readback x t H HN') as [Rp Rc].
  pose proof (Rp false) as Rf. pose proof (Rp true) as Rt.
  unfold ck_read in H.
  pose proof (SlotSizes.wlen_false_read ck_strtod x t H) as Wf.
  pose proof (SlotSizes.wlen_true_read ck_strtod x t H) as Wt.
  pose proof (PjReqBoundW.set_grow_read ck_strtod x t H) as G.
  unfold RQ_crt, RQ_rtt, TX_req, zmaxl, prhWriter_WMAX, cf_head.
  rewrite !ck_tx_len_wlen.
  change (56 * cap2R (ck_members t)) with (56 * PjReqBoundW.cap2 (PjReqBoundW.members t)).
  change (Z.of_nat (length ck_STAMP)) with 20.
  cbn [fold_right]. lia.
Qed.

Theorem rq_crt_cf_bound : forall x t, Z.of_nat (length x) <= 0x300000 -> ck_read x = Some t ->
  RQ_crt t + cf_head < cf_malloc_max.
Proof.
  intros x t HN H. pose proof (rq_crt_abs x t HN H). unfold cf_malloc_max. lia.
Qed.

(* ================================================================ the copies, pinned to the model *)

(* Row: |x|, TX_req t false, TX_req t true, RQ_pj_parse (wdoc t false), RQ_pj_parse (wdoc t true),
   56 * cap2R (ck_members t), RQ_pj_parse (wdoc (ck_crt_tree t) true), RQ_crt t, RQ_pj_parse x. The first input is
   {"":[[0,"\b"],{}],"":0,...} with 8 members (the rewrite's 9th grows the kids to 16: 896; "\b" is written \u0008),
   the second [[[0,0]]]. The same rows come from the Python copy of the model used for the measurement at MAXB. *)
Definition rq_row (x : list Z) : list Z :=
  match ck_read x with
  | Some t => [Z.of_nat (length x); TX_req t false; TX_req t true; RQ_pj_parse (wdoc t false);
               RQ_pj_parse (wdoc t true); 56 * cap2R (ck_members t); RQ_pj_parse (wdoc (ck_crt_tree t) true);
               RQ_crt t; RQ_pj_parse x]
  | None => []
  end.

Definition x_ex8 : list Z :=
  [123; 34; 34; 58; 91; 91; 48; 44; 34; 92; 98; 34; 93; 44; 123; 125; 93; 44; 34; 34; 58; 48; 44; 34; 34; 58; 48;
   44; 34; 34; 58; 48; 44; 34; 34; 58; 48; 44; 34; 34; 58; 48; 44; 34; 34; 58; 48; 44; 34; 34; 58; 48; 125].
Definition x_ex3 : list Z := [91; 91; 91; 48; 44; 48; 93; 93; 93].

Example rq_rows : map rq_row [x_ex8; x_ex3] =
  [[53; 116; 248; 448; 448; 896; 896; 268435456; 448]; [9; 20; 84; 448; 448; 448; 448; 268435456; 448]].
Proof. vm_compute. reflexivity. Qed.
