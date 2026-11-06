(* omx-clap-core/fuzz_preset: the per-call LIVE byte bounds of the #102 check texts. Nothing here is a function's
   proof (rule 24); kind: statement text.

   WHAT IS BOUNDED. The kit's check texts (walkkit-next 99f596897b85: lib/A/PRH_FnCheck.v:212-220 and :382-403,
   PRH_FnPj.v:184-214, PRH_FnWriter.v:179-180, PRH_FnTx.v:146, PRH_FnReader.v:357, PRH_Reader.v:53-57 and :189) take
   `blocks_bytes S + LIVE_<fn> .. <= LIVE_MAX` as a premise. The walk of LLVMFuzzerTestOneInput discharges it from
   `blocks_bytes S + LIVE_LIB <= LIVE_MAX`, LIVE_LIB = 3 * 2 ^ 32 (live_lib), so each LIVE_<fn> of the input x, or of
   the tree t read from x, must be at most live_lib whenever |x| <= MAXB = 3 * 2 ^ 20 (PresetReqAt.v:86, the
   harness's input cap). The terms below are the kit's with their bodies written out, hd for cf_head (the CfParams field;
   16 at the preset's parameters) and sm for prh_jr_strtod:
     PRH_Reader.hpeakR                      hpeak_r
     PRH_FnPj.prhPj_ptrace tl               ptrace prh_jr_strtod tl
     PRH_FnPj.LIVE_pj_parse tl              live_pj_parse cf_head prh_jr_strtod tl
     PRH_FnWriter.LIVE_pj_write t p         live_pj_write cf_head t p
     PRH_FnTx.LIVE_tx                       live_tx
     PRH_FnReader.cap2R / LIVE_grow         cap2r / live_grow cf_head
     PRH_FnPj.LIVE_pj_set / LIVE_pj_string  live_pj_set cf_head / live_pj_string cf_head
     PRH_FnCheck.ck_MOD_AT, ck_STAMP, ck_crt_tree, ck_members   ck_mod_at, ck_stamp, ck_crt_tree, ck_members
     PRH_FnCheck.LIVE_check_no_overread x               live_check_no_overread cf_head prh_jr_strtod x
     PRH_FnCheck.LIVE_check_reject_clean_starved x t    live_check_reject_clean_starved cf_head prh_jr_strtod x t
     PRH_FnCheck.LIVE_round_trip_text t p               live_round_trip_text cf_head prh_jr_strtod t p
     PRH_FnCheck.LIVE_check_round_trip t                live_check_round_trip cf_head prh_jr_strtod t
   each by delta / beta / iota only.

   WHY THEY HOLD, X = |x|, 0 <= hd <= 16, t read from x (json_read sm x = Some t):
   - the reading of x: hpeak_rd (M10), the peak of a trace is the held bytes of one of its prefixes (hpeak_prefix), at
     most 224 X + 16384 (PjGrammar.G10); calls <= 2 X + 2 (PjGrammar.G7_4). So live_pj_parse x <= 480 X + 32816.
   - the read-back of wdoc t p: its trace is ttrace t for both p (PjRoundTrip.G9_trace), whose events never shrink
     (PackTraceR.tt_trok), so its peak is all it holds, zl (rtsz t) (hpeak_tt, M10, by PackTraceR.tt_fr); that is at
     most 258 X + 16448 (PackTreeTight.tb_read, M4); its calls are tcalls t <= rtw t <= X (PjRoundTrip.tcalls_trace,
     PackTraceR.tcalls_rtw, PackReparse.rtw_read). So live_pj_parse (wdoc t p) <= 532 X + 32912.
   - the rewrite's read-back: the same for crt_tree t (PjReqBoundW.crt_wf_sm), zl (rtsz (crt_tree t)) <=
     zl (rtsz t) + 32 X + 544 (PackTreeTight.crt_zl_lin, M5), tcalls <= rtw t + 18 (PackTraceR.rtw_crt):
     596 X + 34288.
   - the writer: its last buffer rqw (PjReqBoundW.rqw_false_read / rqw_true_read / rqw_crt_read).
   - pj_set at cap = members: 64 cap2r (members) + 3 hd + 11, with 2 members + 2 <= X (SlotSizes.s_read).
   Values at X = MAXB = 3,145,728, hd = 16 (the *_maxb lemmas; live_lib = 12,884,901,888):
     live_pj_parse x                      1,509,982,256
     live_check_no_overread x             4,539,384,000
     live_check_reject_clean_starved x t  2,252,373,912
     live_round_trip_text t false         2,785,050,800
     live_round_trip_text t true          3,451,944,920
     live_check_round_trip t              9,017,853,504 *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue ReaderRes
  PackReparse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PackTraceR PackTreeTight SlotSizes
  check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PjReqBoundW.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ The kit's terms, bodies written out *)

(* the per-call allowance of the harness's callees *)
Definition live_lib : Z := 3 * 2 ^ 32.

(* the most user bytes a trace holds at once above its start *)
Fixpoint hpeak_r (tr : list ev) : Z :=
  match tr with
  | [] => 0
  | e :: r => Z.max 0 (held_ev e + hpeak_r r)
  end.

(* pj_parse: the granted reading's trace, its doubled peak and a head per call *)
Definition ptrace (sm : list Z -> Z * Z) (tl : list Z) : list ev := snd (PjGrammar.jr_run sm tl []).
Definition live_pj_parse (hd : Z) (sm : list Z -> Z * Z) (tl : list Z) : Z :=
  2 * hpeak_r (ptrace sm tl) + hd * (Z.of_nat (PjGrammar.calls (ptrace sm tl)) + 1).

(* pj_write: the old and the new last buffer, each with its head *)
Definition live_pj_write (hd : Z) (t : jv) (p : bool) : Z :=
  2 * (WriterSpec.newcap 0 (Z.of_nat (length (WriterValue.wdoc t p)) + 1) + hd).

(* every tx_put of a rendering *)
Definition live_tx : Z := 2 ^ 30.

Definition cap2r (cap : Z) : Z := if cap =? 0 then 8 else 2 * cap.
Definition live_grow (hd ty cap : Z) : Z := 56 * cap2r cap + hd + (if ty =? 6 then 8 * cap2r cap + hd else 0).
Definition live_pj_set (hd n cap klen : Z) : Z := (if n =? cap then live_grow hd 6 cap else 0) + klen + 1 + hd.
Definition live_pj_string (hd len : Z) : Z := len + 1 + hd.

Definition ck_mod_at : list Z := [109; 111; 100; 105; 102; 105; 101; 100; 65; 116].
Definition ck_stamp : list Z := [50; 48; 50; 54; 45; 49; 48; 45; 50; 53; 84; 48; 48; 58; 48; 48; 58; 48; 48; 90].
Definition ck_crt_tree (t : jv) : jv :=
  match t with
  | JObj ms => JObj (pj_set_model ms ck_mod_at (JStr ck_stamp))
  | _ => t
  end.
Definition ck_members (t : jv) : Z := match t with JObj ms => Z.of_nat (length ms) | _ => 0 end.

Definition live_check_no_overread (hd : Z) (sm : list Z -> Z * Z) (x : list Z) : Z :=
  3 * (Z.of_nat (length x) + 16) + 3 * live_pj_parse hd sm x.
Definition live_check_reject_clean_starved (hd : Z) (sm : list Z -> Z * Z) (x : list Z) (t : jv) : Z :=
  live_pj_parse hd sm x + live_pj_write hd t true + live_pj_write hd t false.
Definition live_round_trip_text (hd : Z) (sm : list Z -> Z * Z) (t : jv) (p : bool) : Z :=
  live_pj_write hd t p + live_tx + live_pj_parse hd sm (WriterValue.wdoc t p).
Definition live_check_round_trip (hd : Z) (sm : list Z -> Z * Z) (t : jv) : Z :=
  live_round_trip_text hd sm t false + live_round_trip_text hd sm t true +
  live_pj_string hd (Z.of_nat (length ck_stamp)) +
  live_pj_set hd (ck_members t) (ck_members t) (Z.of_nat (length ck_mod_at)) +
  live_pj_write hd (ck_crt_tree t) true + live_pj_parse hd sm (WriterValue.wdoc (ck_crt_tree t) true).

Lemma ck_crt_eq : forall t, ck_crt_tree t = check_round_trip_c.crt_tree t.
Proof. intros t. destruct t; reflexivity. Qed.

Lemma live_lib_val : live_lib = 12884901888.
Proof. reflexivity. Qed.

Lemma live_tx_val : live_tx = 1073741824.
Proof. reflexivity. Qed.

Lemma hd_mul : forall hd c, 0 <= hd <= 16 -> 0 <= c -> hd * c <= 16 * c.
Proof. intros hd c Hd Hc. apply Z.mul_le_mono_nonneg_r; lia. Qed.

(* ================================================================ M10: the peaks *)

Lemma hpeak_prefix : forall tr, exists p rest, tr = p ++ rest /\ hpeak_r tr = held p.
Proof.
  induction tr as [|e r IH].
  - exists [], []. split; reflexivity.
  - destruct IH as (p & rest & E & H). cbn [hpeak_r]. rewrite H.
    destruct (Z.max_spec 0 (held_ev e + held p)) as [[_ M]|[_ M]]; rewrite M.
    + exists (e :: p), rest. rewrite E. split; reflexivity.
    + exists [], (e :: r). split; reflexivity.
Qed.

(* M10 hpeak_rd: any reading of x, any grants *)
Theorem hpeak_rd : forall sm x ok, hpeak_r (snd (jr_run sm x ok)) <= 224 * Z.of_nat (length x) + 16384.
Proof.
  intros sm x ok. destruct (hpeak_prefix (snd (jr_run sm x ok))) as (p & rest & E & H).
  rewrite H. exact (PjGrammar.G10 sm x ok p rest E).
Qed.

Lemma held_fr : forall tr, held tr = PackTraceR.fr Z.of_nat tr.
Proof.
  induction tr as [|e r IH]; [reflexivity|]. cbn [held PackTraceR.fr]. rewrite IH.
  destruct e as [n|[|m] n|n|n]; cbn [held_ev PackTraceR.fw]; lia.
Qed.

Lemma hpeak_held : forall tr, Forall PackTraceR.trok tr -> hpeak_r tr = held tr /\ 0 <= held tr.
Proof.
  induction tr as [|e r IH]; intros H; [cbn; lia|].
  apply Forall_cons_iff in H as [He H]. destruct (IH H) as [E N].
  assert (Ne : 0 <= held_ev e)
    by (destruct e as [n|m n|n|n]; cbn [PackTraceR.trok] in He; cbn [held_ev]; try contradiction; lia).
  cbn [hpeak_r held]. rewrite E. lia.
Qed.

(* M10 hpeak_tt: the read-back's trace never shrinks, so its peak is all its blocks *)
Theorem hpeak_tt : forall u, hpeak_r (ttrace u) = zl (map Z.of_nat (rtsz u)).
Proof.
  intros u. rewrite (proj1 (hpeak_held _ (PackTraceR.tt_trok u))), held_fr. exact (PackTraceR.tt_fr Z.of_nat u).
Qed.

(* ================================================================ the pieces, linear in |x| *)

Theorem live_pj_parse_lin : forall hd sm x, 0 <= hd <= 16 ->
  live_pj_parse hd sm x <= 480 * Z.of_nat (length x) + 32816.
Proof.
  intros hd sm x Hd. unfold live_pj_parse, ptrace.
  pose proof (hpeak_rd sm x []) as P. pose proof (PjGrammar.G7_4 sm x []) as C.
  pose proof (hd_mul hd (Z.of_nat (calls (snd (jr_run sm x []))) + 1) Hd ltac:(lia)) as M. lia.
Qed.

Lemma live_pj_write_rqw : forall hd t p, live_pj_write hd t p = 2 * (PjReqBoundW.rqw t p + hd).
Proof. reflexivity. Qed.

Theorem live_pj_write_false : forall hd sm x t, 0 <= hd <= 16 -> json_read sm x = Some t ->
  live_pj_write hd t false <= 2 * Z.max 4096 (6 * Z.of_nat (length x)) + 32.
Proof.
  intros hd sm x t Hd H. rewrite live_pj_write_rqw. pose proof (PjReqBoundW.rqw_false_read sm x t H). lia.
Qed.

Theorem live_pj_write_true : forall hd sm x t, 0 <= hd <= 16 -> json_read sm x = Some t ->
  live_pj_write hd t true <= 2 * Z.max 4096 (112 * Z.of_nat (length x) - 108) + 32.
Proof.
  intros hd sm x t Hd H. rewrite live_pj_write_rqw. pose proof (PjReqBoundW.rqw_true_read sm x t H). lia.
Qed.

Theorem live_pj_parse_wdoc : forall hd sm x t p, 0 <= hd <= 16 -> json_read sm x = Some t ->
  live_pj_parse hd sm (wdoc t p) <= 532 * Z.of_nat (length x) + 32912.
Proof.
  intros hd sm x t p Hd H. unfold live_pj_parse, ptrace.
  rewrite (G9_trace sm t (wf_read sm x t H) p), hpeak_tt, tcalls_trace.
  pose proof (PackTreeTight.tb_read sm x t H) as Tb.
  pose proof (PackTraceR.tcalls_rtw t) as C1. pose proof (rtw_read sm x t H) as C2.
  pose proof (hd_mul hd (Z.of_nat (tcalls t) + 1) Hd ltac:(lia)) as M. lia.
Qed.

Theorem live_pj_parse_crt : forall hd sm x t, 0 <= hd <= 16 -> json_read sm x = Some t ->
  live_pj_parse hd sm (wdoc (ck_crt_tree t) true) <= 596 * Z.of_nat (length x) + 34288.
Proof.
  intros hd sm x t Hd H. rewrite ck_crt_eq. unfold live_pj_parse, ptrace.
  rewrite (G9_trace sm _ (PjReqBoundW.crt_wf_sm sm x t H) true), hpeak_tt, tcalls_trace.
  pose proof (PackTreeTight.tb_read sm x t H) as Tb. pose proof (PackTreeTight.crt_zl_lin sm x t H) as Z5.
  pose proof (PackTraceR.tcalls_rtw (check_round_trip_c.crt_tree t)) as C1.
  pose proof (PackTraceR.rtw_crt t) as C2. pose proof (rtw_read sm x t H) as C3.
  pose proof (hd_mul hd (Z.of_nat (tcalls (check_round_trip_c.crt_tree t)) + 1) Hd ltac:(lia)) as M. lia.
Qed.

Theorem live_pj_write_crt : forall hd sm x t, 0 <= hd <= 16 -> json_read sm x = Some t ->
  live_pj_write hd (ck_crt_tree t) true <= 2 * Z.max 4096 (112 * Z.of_nat (length x) - 28) + 32.
Proof.
  intros hd sm x t Hd H. rewrite live_pj_write_rqw, ck_crt_eq.
  pose proof (PjReqBoundW.rqw_crt_read sm x t H). lia.
Qed.

Theorem live_pj_set_read : forall hd sm x t, 0 <= hd <= 16 -> json_read sm x = Some t ->
  live_pj_set hd (ck_members t) (ck_members t) (Z.of_nat (length ck_mod_at)) <=
    64 * Z.max 8 (Z.of_nat (length x) - 2) + 59.
Proof.
  intros hd sm x t Hd H.
  assert (Hc : cap2r (ck_members t) <= Z.max 8 (Z.of_nat (length x) - 2)).
  { destruct t as [| | | txt bits | s | items | ms]; try (cbn -[Z.max]; lia).
    unfold cap2r, ck_members.
    pose proof (SlotSizes.s_read sm x (JObj ms) H) as S.
    destruct (SlotSizes.szok_obj_inv _ _ S) as (Hn & _ & _).
    destruct (Z.eqb_spec (Z.of_nat (length ms)) 0); cbv iota; lia. }
  unfold live_pj_set, live_grow. rewrite !Z.eqb_refl. cbv iota.
  change (Z.of_nat (length ck_mod_at)) with 10. lia.
Qed.

Lemma live_pj_string_stamp : forall hd, 0 <= hd <= 16 -> live_pj_string hd (Z.of_nat (length ck_stamp)) <= 37.
Proof. intros hd Hd. unfold live_pj_string. change (Z.of_nat (length ck_stamp)) with 20. lia. Qed.

Theorem live_round_trip_text_lin : forall hd sm x t p, 0 <= hd <= 16 -> json_read sm x = Some t ->
  live_round_trip_text hd sm t p <=
    2 * Z.max 4096 (if p then 112 * Z.of_nat (length x) - 108 else 6 * Z.of_nat (length x)) + 32 + live_tx +
    532 * Z.of_nat (length x) + 32912.
Proof.
  intros hd sm x t p Hd H. unfold live_round_trip_text.
  pose proof (live_pj_parse_wdoc hd sm x t p Hd H).
  destruct p; [pose proof (live_pj_write_true hd sm x t Hd H) | pose proof (live_pj_write_false hd sm x t Hd H)];
    cbv iota; lia.
Qed.

(* ================================================================ the values at MAXB *)

Theorem live_pj_parse_maxb : forall hd sm x, 0 <= hd <= 16 -> Z.of_nat (length x) <= PresetReqAt.MAXB ->
  live_pj_parse hd sm x <= 1509982256.
Proof.
  intros hd sm x Hd HX. unfold PresetReqAt.MAXB in HX. pose proof (live_pj_parse_lin hd sm x Hd). lia.
Qed.

Theorem live_check_no_overread_maxb : forall hd sm x, 0 <= hd <= 16 ->
  Z.of_nat (length x) <= PresetReqAt.MAXB -> live_check_no_overread hd sm x <= 4539384000.
Proof.
  intros hd sm x Hd HX. unfold live_check_no_overread. unfold PresetReqAt.MAXB in HX.
  pose proof (live_pj_parse_lin hd sm x Hd). lia.
Qed.

Theorem live_check_reject_clean_starved_maxb : forall hd sm x t, 0 <= hd <= 16 -> json_read sm x = Some t ->
  Z.of_nat (length x) <= PresetReqAt.MAXB -> live_check_reject_clean_starved hd sm x t <= 2252373912.
Proof.
  intros hd sm x t Hd H HX. unfold live_check_reject_clean_starved. unfold PresetReqAt.MAXB in HX.
  pose proof (live_pj_parse_lin hd sm x Hd). pose proof (live_pj_write_true hd sm x t Hd H).
  pose proof (live_pj_write_false hd sm x t Hd H). lia.
Qed.

Theorem live_round_trip_text_maxb : forall hd sm x t p, 0 <= hd <= 16 -> json_read sm x = Some t ->
  Z.of_nat (length x) <= PresetReqAt.MAXB ->
  live_round_trip_text hd sm t p <= if p then 3451944920 else 2785050800.
Proof.
  intros hd sm x t p Hd H HX. unfold PresetReqAt.MAXB in HX.
  pose proof (live_round_trip_text_lin hd sm x t p Hd H) as R. rewrite live_tx_val in R.
  destruct p; cbv iota in R |- *; lia.
Qed.

Theorem live_check_round_trip_maxb : forall hd sm x t, 0 <= hd <= 16 -> json_read sm x = Some t ->
  Z.of_nat (length x) <= PresetReqAt.MAXB -> live_check_round_trip hd sm t <= 9017853504.
Proof.
  intros hd sm x t Hd H HX.
  pose proof (live_round_trip_text_maxb hd sm x t false Hd H HX) as R0.
  pose proof (live_round_trip_text_maxb hd sm x t true Hd H HX) as R1. cbv iota in R0, R1.
  pose proof (live_pj_string_stamp hd Hd). pose proof (live_pj_set_read hd sm x t Hd H).
  pose proof (live_pj_write_crt hd sm x t Hd H). pose proof (live_pj_parse_crt hd sm x t Hd H).
  unfold live_check_round_trip. unfold PresetReqAt.MAXB in HX. lia.
Qed.

(* ================================================================ the bounds the walk takes *)

Theorem live_pj_parse_bound : forall hd sm x, 0 <= hd <= 16 -> Z.of_nat (length x) <= PresetReqAt.MAXB ->
  live_pj_parse hd sm x <= live_lib.
Proof. intros hd sm x Hd HX. pose proof (live_pj_parse_maxb hd sm x Hd HX). rewrite live_lib_val. lia. Qed.

Theorem live_check_no_overread_bound : forall hd sm x, 0 <= hd <= 16 -> Z.of_nat (length x) <= PresetReqAt.MAXB ->
  live_check_no_overread hd sm x <= live_lib.
Proof.
  intros hd sm x Hd HX. pose proof (live_check_no_overread_maxb hd sm x Hd HX). rewrite live_lib_val. lia.
Qed.

Theorem live_check_reject_clean_starved_bound : forall hd sm x t, 0 <= hd <= 16 -> json_read sm x = Some t ->
  Z.of_nat (length x) <= PresetReqAt.MAXB -> live_check_reject_clean_starved hd sm x t <= live_lib.
Proof.
  intros hd sm x t Hd H HX. pose proof (live_check_reject_clean_starved_maxb hd sm x t Hd H HX).
  rewrite live_lib_val. lia.
Qed.

Theorem live_round_trip_text_bound : forall hd sm x t p, 0 <= hd <= 16 -> json_read sm x = Some t ->
  Z.of_nat (length x) <= PresetReqAt.MAXB -> live_round_trip_text hd sm t p <= live_lib.
Proof.
  intros hd sm x t p Hd H HX. pose proof (live_round_trip_text_maxb hd sm x t p Hd H HX) as R.
  rewrite live_lib_val. destruct p; cbv iota in R; lia.
Qed.

Theorem live_check_round_trip_bound : forall hd sm x t, 0 <= hd <= 16 -> json_read sm x = Some t ->
  Z.of_nat (length x) <= PresetReqAt.MAXB -> live_check_round_trip hd sm t <= live_lib.
Proof.
  intros hd sm x t Hd H HX. pose proof (live_check_round_trip_maxb hd sm x t Hd H HX). rewrite live_lib_val. lia.
Qed.

(* ================================================================ the terms on a concrete input *)

(* {"k":[1,"ab"]}: an object (so the rewrite appends modifiedAt), an array, a number and a string; 14 bytes *)
Definition lb_x : list Z := [123; 34; 107; 34; 58; 91; 49; 44; 34; 97; 98; 34; 93; 125].

(* the reading of lb_x: blocks kids 448, keys 64, "k" 2, kids 448, 1 2, "ab" 3 (peak 967) in 6 calls, so
   2 * 967 + 16 * 7 = 2046, against 480 * 14 + 32816 = 39536 *)
Example live_pj_parse_ex :
  (live_pj_parse 16 jr_strtod lb_x, hpeak_r (ptrace jr_strtod lb_x), calls (ptrace jr_strtod lb_x),
   480 * Z.of_nat (length lb_x) + 32816) = (2046, 967, 6%nat, 39536).
Proof. vm_compute. reflexivity. Qed.

(* M10 on the tree read from lb_x: the read-back's peak is all its blocks *)
Example hpeak_tt_ex :
  match json_read jr_strtod lb_x with
  | Some t => (hpeak_r (ttrace t), zl (map Z.of_nat (rtsz t)))
  | None => (0, 0)
  end = (967, 967).
Proof. vm_compute. reflexivity. Qed.

(* 3 * (14 + 16) + 3 * 2046 *)
Example live_check_no_overread_ex : live_check_no_overread 16 jr_strtod lb_x = 6228.
Proof. vm_compute. reflexivity. Qed.

(* 2046 + 2 * (4096 + 16) + 2 * (4096 + 16): both texts fit the writer's first buffer *)
Example live_check_reject_clean_starved_ex :
  match json_read jr_strtod lb_x with
  | Some t => live_check_reject_clean_starved 16 jr_strtod lb_x t
  | None => 0
  end = 18494.
Proof. vm_compute. reflexivity. Qed.

(* 8224 + 2 ^ 30 + 2046 for both p: the read-back of either text has lb_x's trace *)
Example live_round_trip_text_ex :
  match json_read jr_strtod lb_x with
  | Some t => (live_round_trip_text 16 jr_strtod t false, live_round_trip_text 16 jr_strtod t true)
  | None => (0, 0)
  end = (1073752094, 1073752094).
Proof. vm_compute. reflexivity. Qed.

(* 2 * 1073752094 + pj_string 37 + pj_set 187 (1 member, cap 1: grow 56 * 2 + 8 * 2 and two heads, then the key
   10 + 1 + 16) + 8224 + the rewrite's read-back 2 * 999 + 16 * 9 = 2142 (modifiedAt 11 and the stamp 21 added) *)
Example live_check_round_trip_ex :
  match json_read jr_strtod lb_x with
  | Some t => live_check_round_trip 16 jr_strtod t
  | None => 0
  end = 2147514778.
Proof. vm_compute. reflexivity. Qed.
