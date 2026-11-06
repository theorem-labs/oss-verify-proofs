(* Modified by Theorem Labs, 2026-10: new file, the definitions, frame lemmas and closing tactics the proofs of operations 5 (wake) and 6 (close) share (a Theorem Labs lane). *)
(* fuzz_transport.c (FT):1193-1205 on top of WakeOk.v: op_begin (FT:388-394), the model's m_wake / m_close, the
   library's diginet_session_wake / _close (DS:119-158) with io_send and notice inline, the wake code check
   (FT:517-525) and settle(0) (FT:980-991, SettleOk.v). The operations' proofs: WakeOp5.v, WakeOp5T.v, WakeOp6.v;
   the statements the loop takes: WakeOps.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SendOk SimLib SettleOk WakeOk.
Import ListNotations.
Open Scope Z_scope.

(* the option monad of TOps.v *)
Local Notation "'let?' p ':=' e 'in' b" :=
  (match e with Some p => b | None => None end)
  (at level 200, p pattern, e at level 100, b at level 200, right associativity).

(* ---- the two operations after op_begin (TOps.v LLVMFuzzerTestOneInput_op_m, FT:1193-1205) ---- *)
Definition op5_body (I : timg) (B1 : list byte) (c1 : fuzz_in) (k : nat) : option (list byte * (fuzz_in * nat)) :=
  let? (B2, want) := m_wake_m B1 in
  let? (B3, rc) := diginet_session_wake_m I None B2 (g_now B2) in
  let? (B4, _) := check_state_wake_code_m B3 rc want in
  let? (B5, _) := settle_m B4 0 in
  Some (B5, (c1, k)).

Definition op6_body (I : timg) (B1 : list byte) (c1 : fuzz_in) (k : nat) : option (list byte * (fuzz_in * nat)) :=
  let? (B2, _) := m_close_m B1 in
  let? (B3, _) := diginet_session_close_m I None B2 (g_now B2) in
  let? (B4, _) := settle_m B3 0 in
  Some (B4, (c1, k)).

Lemma op5_unfold : forall I B A D c k, snd (fuzz_u8_m D c) mod 9 = 5 ->
  LLVMFuzzerTestOneInput_op_m I B A D c k = (let? (B1, _) := op_begin_m B in op5_body I B1 (fst (fuzz_u8_m D c)) k).
Proof.
  intros I B A D c k Hop. unfold LLVMFuzzerTestOneInput_op_m.
  destruct (fuzz_u8_m D c) as [c1 opb]. cbn [fst snd] in *. cbv beta iota zeta. rewrite Hop. kdec.
  unfold op5_body. exact eq_refl.
Qed.

Lemma op6_unfold : forall I B A D c k, snd (fuzz_u8_m D c) mod 9 = 6 ->
  LLVMFuzzerTestOneInput_op_m I B A D c k = (let? (B1, _) := op_begin_m B in op6_body I B1 (fst (fuzz_u8_m D c)) k).
Proof.
  intros I B A D c k Hop. unfold LLVMFuzzerTestOneInput_op_m.
  destruct (fuzz_u8_m D c) as [c1 opb]. cbn [fst snd] in *. cbv beta iota zeta. rewrite Hop. kdec.
  unfold op6_body. exact eq_refl.
Qed.

(* ---- op_begin (FT:388-394): OW and GOT zeroed, M.fail = g_fail_next ---- *)
Definition opz (W : list byte) : Prop :=
  OW_n W = 0 /\ GOT_n W = 0 /\ OW_e2 W = 0 /\ GOT_e2 W = 0 /\ OW_e3 W = 0 /\ GOT_e3 W = 0 /\
  OW_acks W = 0 /\ GOT_acks W = 0 /\ OW_desk W = 0 /\ GOT_desk W = 0 /\ OW_foreign W = 0 /\ GOT_foreign W = 0 /\
  OW_acked W = 0 /\ GOT_acked W = 0 /\ OW_ndata W = 0 /\ GOT_ndata W = 0 /\ M_fail W = g_fail_next W.

Lemma op_begin_facts : forall I ops B, agree I ops B ->
  exists W0, op_begin_m B = Some (W0, tt) /\ agree I ops W0 /\ opz W0.
Proof.
  intros I ops B HA. pose proof (ac_len _ _ _ (ag_core _ _ _ HA)) as HB.
  eexists. split; [unfold op_begin_m; cbv zeta; exact eq_refl|].
  split; [apply (agree_op_begin I ops B _ HA); unfold op_begin_m; cbv zeta; exact eq_refl|].
  unfold opz. repeat split; wsimp.
Qed.

Lemma opz_settle : forall W, opz W -> settle_eq W.
Proof.
  intros W (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & _).
  exact (settle_eq_zero W H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16).
Qed.

(* the OW / GOT fields and M.fail lie in these ranges *)
Definition foot_opz : list (Z * Z) := [(OFF_OW, SZ_OW); (OFF_GOT, SZ_GOT); (A_M_fail, 4); (OFF_g_fail_next, 1)].

Lemma opz_frame : forall W W' rs, opz W -> wsame W W' rs -> rdisj rs foot_opz = true -> opz W'.
Proof.
  intros W W' rs Hz Hw Hr. pose proof (rdisj_spec rs foot_opz Hr) as Hd.
  unfold opz in *. wsame_rw Hw Hd. exact Hz.
Qed.

Lemma truth0 : truth 0 = false.
Proof. reflexivity. Qed.

(* settle (0) on a world where agree holds and settle_eq does *)
Lemma settle0 : forall I ops W, agree I ops W -> settle_eq W -> settle_m W 0 = Some (W, tt).
Proof.
  intros I ops W [HC HK HR] HS.
  apply (settle_ok I ops W 0 HC HK HS). rewrite truth0. discriminate.
Qed.

(* ---- finer footprints than SimLib's foot_corem, for the sub-records a wake / close leaves alone ---- *)
Definition foot_cfg : list (Z * Z) := [(OFF_g_cfg, 60); (A_S_cfg_host_mac, 60); (OFF_g_raw, 4)].
Definition foot_io : list (Z * Z) := [(A_S_io_ctx, 32); (A_S_notify, 16)].

Lemma agree_cfg_ff : forall B B' rs, wsame B B' rs -> rdisj rs foot_cfg = true -> agree_cfg B -> agree_cfg B'.
Proof.
  intros B B' rs Hw Hr H. pose proof (rdisj_spec rs foot_cfg Hr) as Hd.
  destruct H. constructor; wsame_rw Hw Hd; wexact.
Qed.

Lemma agree_io_ff : forall I B B' rs, wsame B B' rs -> rdisj rs foot_io = true -> agree_io I B -> agree_io I B'.
Proof.
  intros I B B' rs Hw Hr H. pose proof (rdisj_spec rs foot_io Hr) as Hd.
  destruct H. constructor; wsame_rw Hw Hd; wexact.
Qed.

(* ---- the wake's and the close's refusals ---- *)
Lemma m_wake_unknown : forall B, M_desk_known B = 0 -> m_wake_m B = Some (B, SPEC_E_ARG).
Proof. intros B H. unfold m_wake_m. rewrite H. kdec. exact eq_refl. Qed.

Lemma m_wake_foreign : forall B, M_desk_known B <> 0 -> M_foreign B <> 0 -> m_wake_m B = Some (B, SPEC_E_REFUSED).
Proof.
  intros B Hk Hf. unfold m_wake_m, truth.
  destruct (Z.eqb_spec (M_desk_known B) 0) as [E|_]; [contradiction|].
  destruct (Z.eqb_spec (M_foreign B) 0) as [E|_]; [contradiction|]. kdec. exact eq_refl.
Qed.

Lemma lib_wake_unknown : forall I F B now, S_desk_known B = 0 ->
  diginet_session_wake_m I F B now = Some (B, DIGINET_E_ARG).
Proof. intros I F B now H. unfold diginet_session_wake_m. rewrite H. kdec. exact eq_refl. Qed.

Lemma lib_wake_foreign : forall I F B now, S_desk_known B <> 0 -> S_foreign B <> 0 ->
  diginet_session_wake_m I F B now =
    Some (set_S_stats_refused B (u64 (S_stats_refused B + 1)), DIGINET_E_REFUSED).
Proof.
  intros I F B now Hk Hf. unfold diginet_session_wake_m.
  destruct (Z.eqb_spec (S_desk_known B) 0) as [E|_]; [contradiction|].
  destruct (Z.eqb_spec (S_foreign B) 0) as [E|_]; [contradiction|]. kdec. exact eq_refl.
Qed.

(* ================================================================ op 5 *)





(* the fields agree_fly reads: the frame in flight on both sides, the states, the desk, the counter, g_cfg *)
Definition foot_fly : list (Z * Z) :=
  [(A_M_fly_on, 1552); (A_M_state, 4); (A_M_desk, 6); (A_S_inflight, 1548); (A_S_host_counter, 4); (OFF_g_cfg, 60)].

Lemma agree_fly_ff : forall B B' rs, wsame B B' rs -> rdisj rs foot_fly = true -> agree_fly B -> agree_fly B'.
Proof.
  intros B B' rs Hw Hr H. pose proof (rdisj_spec rs foot_fly Hr) as Hd.
  destruct H as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11].
  constructor; wsame_rw Hw Hd; try wexact.
  intros Hon. destruct (F11 Hon) as (body & ncmds & H1 & H2 & H3 & H4 & H5 & H6).
  assert (Hn : (Z.to_nat (M_fly_len B) <= 1514)%nat) by (rewrite H4; unfold frame_len; lia).
  assert (E1 : sub B' A_M_fly_frame (Z.to_nat (M_fly_len B)) = sub B A_M_fly_frame (Z.to_nat (M_fly_len B)))
    by (refine (wsame_cov_sub_le B B' rs foot_fly A_M_fly_frame _ 1514 Hw Hd _ Hn _);
        [wle | vm_compute; reflexivity]).
  assert (E2 : sub B' A_S_inflight_frame (Z.to_nat (M_fly_len B)) = sub B A_S_inflight_frame (Z.to_nat (M_fly_len B)))
    by (refine (wsame_cov_sub_le B B' rs foot_fly A_S_inflight_frame _ 1514 Hw Hd _ Hn _);
        [wle | vm_compute; reflexivity]).
  wrw E1. wrw E2. exists body, ncmds. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
Qed.

(* name the write layers of the goal once, innermost first (SimLib's wsimp_once reads through the names) *)
Ltac wname :=
  repeat match goal with
  | |- context [upd ?X ?k ?v] => wno_upd X; wno_upd v; let W := fresh "W" in set (W := upd X k v)
  end.

(* bv_swrap 32 x = x once the facts in the context bound x (the side condition is decided by lia alone:
   never cbn / vm_compute on a goal with reads) *)
Lemma swrap_id : forall x, - 2147483648 <= x < 2147483648 -> bv_swrap 32 x = x.
Proof. intros x Hx. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn. lia. Qed.

Ltac swrap_ctx :=
  repeat match goal with
  | |- context [bv_swrap 32 ?x] => rewrite (swrap_id x) by lia
  end.

(* before the closers: drop the facts about whole worlds (frames, chain equations, lengths); lia and the
   matchers then see only the field facts *)
Ltac oclean :=
  repeat match goal with
  | H : wsame _ _ _ |- _ => clear H
  | H : ?W = _ |- _ => lazymatch type of W with list byte => clear H end
  | H : length _ = Z.to_nat W_LEN |- _ => clear H
  | H : (_ <= length _)%nat |- _ => clear H
  end.

(* before lia: drop every hypothesis with propositional structure (a disjunction, an implication, a
   quantifier, bit01). lia puts its hypotheses in CNF, and n disjunctions there cost 2 ^ n: the destructed
   agree_core carries dozens (16 GB and more per call). *)
Ltac atomize :=
  repeat match goal with
  | H : ?A |- _ =>
      lazymatch type of A with
      | Prop =>
          lazymatch A with
          | _ \/ _ => clear H
          | _ <-> _ => clear H
          | ex _ => clear H
          | _ -> _ => clear H
          | forall _, _ => clear H
          | bit01 _ => clear H
          | c2_keepalive _ => clear H
          end
      end
  end.

Ltac kunfold :=
  unfold S_IDLE, S_WAKING, S_ONLINE, S_CLOSED, DIGINET_S_IDLE, DIGINET_S_WAKING, DIGINET_S_ONLINE, DIGINET_S_CLOSED,
    R_WAKE, R_CLOSED, DIGINET_R_WAKE, DIGINET_R_CLOSED, SPEC_CMD_E2, SPEC_CMD_DATA, DIGINET_CMD_WAKE,
    TRANS_MAX, INT_MAX, OPS_MAX in *;
  try change (2 ^ 31) with 2147483648 in *; try change (2 ^ 32) with 4294967296 in *;
  try change (2 ^ 8) with 256 in *; try change (2 ^ 16) with 65536 in *.

(* the end of a clause: syntactic closers on the whole context, then lia on its atomic facts only *)
Ltac oend :=
  first [ synrefl | wexact | (intros; synrefl) | (intros; wexact)
        | (atomize; swrap_ctx;
           first [ lia | (intros; lia) | (unfold bit01; lia) | (intros; unfold bit01; lia)
                 | (intros; exfalso; lia) | (intros; wrange; lia) ]) ].

(* one clause over the operation's final world: read it through the writes down to W0, then close it from
   agree at W0 (HC, HK), the opz facts (Hz) and the branch facts in the context *)
Ltac oclose HC HK Hz :=
  unfold c2_keepalive;
  wsimpq;
  let H := fresh "H" in pose proof HC as H; destruct H as [? ? [] [] [] [] [] [] []];
  let K := fresh "K" in pose proof HK as K;
  let Z' := fresh "Z" in pose proof Hz as Z'; unfold opz in Z';
  repeat match goal with Hx : _ /\ _ |- _ => destruct Hx end;
  unfold c2_keepalive in K; oclean; kunfold; oend.

(* the reads of the wake's library side from the model's world (m_wake_pre / m_wake_w writes only M fields and
   OW): what lib_wake_ok needs, from agree at W0 *)
Section WakeLib.
Variables (HL : links) (I : timg) (ops : Z) (W0 Wm : list byte).
Hypothesis HC : agree_core I ops W0.
Hypothesis Hz : opz W0.
Hypothesis Dk : M_desk_known W0 = 1.
Hypothesis Fo : M_foreign W0 = 0.
Hypothesis HWl : length Wm = Z.to_nat W_LEN.
(* Wm reads like W0 on every field the library's wake reads *)
Hypothesis R1 : S_desk_known Wm = S_desk_known W0.
Hypothesis R2 : S_foreign Wm = S_foreign W0.
Hypothesis R3 : S_desk_mac Wm = S_desk_mac W0.
Hypothesis R4 : S_cfg_host_mac Wm = S_cfg_host_mac W0.
Hypothesis R5 : S_host_counter Wm = S_host_counter W0.
Hypothesis R6 : S_cfg_sum_mode Wm = S_cfg_sum_mode W0.
Hypothesis R7 : S_io_send Wm = S_io_send W0.
Hypothesis R8 : S_notify Wm = S_notify W0.
Hypothesis R9 : M_desk_known Wm = M_desk_known W0.
Hypothesis R10 : M_desk Wm = M_desk W0.
Hypothesis R11 : Cfg_sum_mode Wm = Cfg_sum_mode W0.
Hypothesis R12 : M_foreign Wm = M_foreign W0.
Hypothesis R13 : M_host_counter Wm = M_host_counter W0.
Hypothesis R14 : GOT_e2 Wm = GOT_e2 W0.
Hypothesis R15 : GOT_n Wm = GOT_n W0.
Hypothesis R16 : g_fail_next Wm = g_fail_next W0.

Lemma wake_lib_at : forall now,
  diginet_session_wake_m I None Wm now =
    if g_fail_next W0 =? 0
    then Some (lw_done (lw_sent (lw_pre Wm now) (wake_frame (M_desk W0) (S_host_counter W0) (Cfg_sum_mode W0))
                 (S_host_counter W0)) (wake_frame (M_desk W0) (S_host_counter W0) (Cfg_sum_mode W0)) now, DIGINET_OK)
    else Some (io_e2_w (lw_pre Wm now) (wake_frame (M_desk W0) (S_host_counter W0) (Cfg_sum_mode W0))
                 (S_host_counter W0), - EIO).
Proof.
  intros now.
  pose proof (ac_cfg _ _ _ HC) as Hcf. pose proof (ac_st _ _ _ HC) as Hst. pose proof (ac_io _ _ _ HC) as Hio.
  pose proof (ac_misc _ _ _ HC) as Hmi. pose proof (ac_len _ _ _ HC) as HB.
  destruct Hz as (_ & Zgn & _ & Zge & _).
  rewrite <- R16.
  apply (lib_wake_ok HL I None Wm now (M_desk W0) (S_host_counter W0) (Cfg_sum_mode W0) HWl).
  - rewrite R1, (b2_desk_known _ Hst), Dk. discriminate.
  - rewrite R2, (b3_foreign _ Hst). exact Fo.
  - rewrite R3. exact (b2_desk_mac _ Hst Dk).
  - rewrite R4. exact (a2_host_mac _ Hcf).
  - exact R5.
  - rewrite R6. exact (a2_sum_mode _ Hcf).
  - unfold M_desk. apply length_sub; [wle|]. rewrite HB. wle.
  - exact (a1_sum_mode _ Hcf).
  - rewrite R7. exact (a3_io_send _ _ Hio).
  - rewrite R8. exact (a3_notify _ _ Hio).
  - rewrite R9. exact Dk.
  - exact R10.
  - exact R11.
  - rewrite R12. exact Fo.
  - rewrite R13. symmetry. exact (b7_host_counter _ Hst).
  - rewrite R14, Zge. unfold INT_MAX. lia.
  - rewrite R15, Zgn. unfold INT_MAX. lia.
  - rewrite R16. exact (e1_fail_next _ _ Hmi).
Qed.
End WakeLib.

(* the frame fact G Wm = G W0, Wm a chain of writes on W0 *)
Ltac wframe_eq := wsimpq; synrefl.



(* settle_eq's transition list after one transition on each side: the entries at index 0 agree *)
Lemma se_t_one_entry : forall W, OW_n W = 1 -> GOT_t_state W 0 = OW_t_state W 0 -> GOT_t_old W 0 = OW_t_old W 0 ->
  GOT_t_reason W 0 = OW_t_reason W 0 ->
  forall i, 0 <= i < OW_n W -> i < TRANS_MAX ->
    GOT_t_state W i = OW_t_state W i /\ GOT_t_old W i = OW_t_old W i /\ GOT_t_reason W i = OW_t_reason W i.
Proof.
  intros W Hn H1 H2 H3 i Hi _. assert (E : i = 0) by lia. subst i. exact (conj H1 (conj H2 H3)).
Qed.

(* the writes of a wake that sent its E2 or of a close, as ranges (none in foot_cfg, foot_io, foot_q), and the
   unwritten gaps between them: a read inside a gap reads the world before (wsame_rw) *)
Definition rs_wake : list (Z * Z) :=
  [(OFF_M + 12, 12); (OFF_M + 40, 8); (OFF_M + 88, SZ_M - 88); (OFF_OW, SZ_OW); (OFF_GOT, SZ_GOT);
   (OFF_g_s + 112, 4); (OFF_g_s + 140, 8); (OFF_g_s + 152, 8); (OFF_g_s + 212, 1548); (A_S_stats_rx_frames, 112);
   (OFF_g_fail_next, 1); (OFF_g_last_counter, 4)].
Definition fp_wake : list (Z * Z) :=
  [(0, 12); (24, 16); (48, 40); (1648, 112); (1764, 24); (1796, 4); (1808, 52); (3408, 16392); (19912, 45056);
   (64969, 7); (64980, 104); (65308, 4)].

Lemma fp_wake_disj : forall a, in_ranges fp_wake a -> ~ in_ranges rs_wake a.
Proof. apply rdisj_spec. vm_compute. reflexivity. Qed.

(* one clause over the final world W (Hw : wsame W0 W rs_wake, EW : W = its chain of writes on W0): the reads
   of unwritten fields go to W0 in one step (wsame_rw), the others through the chain; then close as oclose *)
Ltac oclose2 HC HK Hz Hw EW :=
  unfold c2_keepalive;
  wsame_rw Hw fp_wake_disj;
  try rewrite EW; wsimpq;
  let H := fresh "H" in pose proof HC as H; destruct H as [? ? [] [] [] [] [] [] []];
  let K := fresh "K" in pose proof HK as K;
  let Z' := fresh "Z" in pose proof Hz as Z'; unfold opz in Z';
  repeat match goal with Hx : _ /\ _ |- _ => destruct Hx end;
  unfold c2_keepalive in K; oclean; kunfold; oend.

(* b8_frames after the wake sent its E2: the frame in flight on both sides is the E2 (no body, ncmds 0) *)
Ltac frames_e2 Hw EW :=
  wsame_rw Hw fp_wake_disj; try rewrite EW; wsimpq;
  intros _; exists (@nil byte), 0;
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
  [ apply Nat.le_0_l
  | vm_compute; reflexivity
  | split; [apply Z.le_refl | vm_compute; reflexivity]
  | vm_compute; reflexivity
  | unfold wake_frame; synrefl
  | unfold wake_frame; synrefl ].





(* ================================================================ op 6 *)

(* the reads of the close's library side from the model's world (m_close writes only M fields and OW) *)
Section CloseLib.
Variables (HL : links) (I : timg) (ops : Z) (W0 Wm : list byte).
Hypothesis HC : agree_core I ops W0.
Hypothesis Hz : opz W0.
Hypothesis HWl : length Wm = Z.to_nat W_LEN.
Hypothesis R1 : S_desk_known Wm = S_desk_known W0.
Hypothesis R2 : S_foreign Wm = S_foreign W0.
Hypothesis R3 : S_desk_mac Wm = S_desk_mac W0.
Hypothesis R4 : S_cfg_host_mac Wm = S_cfg_host_mac W0.
Hypothesis R5 : S_host_counter Wm = S_host_counter W0.
Hypothesis R6 : S_cfg_sum_mode Wm = S_cfg_sum_mode W0.
Hypothesis R7 : S_io_send Wm = S_io_send W0.
Hypothesis R8 : S_notify Wm = S_notify W0.
Hypothesis R9 : M_desk_known Wm = M_desk_known W0.
Hypothesis R10 : M_desk Wm = M_desk W0.
Hypothesis R11 : Cfg_sum_mode Wm = Cfg_sum_mode W0.
Hypothesis R13 : M_host_counter Wm = M_host_counter W0.
Hypothesis R14 : GOT_e3 Wm = GOT_e3 W0.
Hypothesis R15 : GOT_n Wm = GOT_n W0.
Hypothesis R16 : g_fail_next Wm = g_fail_next W0.
Hypothesis R17 : S_state Wm = S_state W0.

Lemma close_lib_send : forall now, M_desk_known W0 = 1 -> M_foreign W0 = 0 -> M_state W0 <> S_CLOSED ->
  diginet_session_close_m I None Wm now =
    Some (set_state_w (set_S_inflight (lc_sent Wm) 0) DIGINET_S_CLOSED DIGINET_R_CLOSED,
          if g_fail_next Wm =? 0 then 0 else - EIO).
Proof.
  intros now Dk Fo Sc.
  pose proof (ac_cfg _ _ _ HC) as Hcf. pose proof (ac_st _ _ _ HC) as Hst. pose proof (ac_io _ _ _ HC) as Hio.
  pose proof (ac_misc _ _ _ HC) as Hmi. pose proof (ac_len _ _ _ HC) as HB.
  destruct Hz as (_ & Zgn & _ & _ & _ & Zg3 & _).
  apply (lib_close_send_ok HL I None Wm now (M_desk W0) (S_host_counter W0) (Cfg_sum_mode W0) HWl).
  - rewrite R1, (b2_desk_known _ Hst), Dk. discriminate.
  - rewrite R2, (b3_foreign _ Hst). exact Fo.
  - rewrite R17, (b1_state _ Hst). intro E. apply Sc. exact E.
  - rewrite R3. exact (b2_desk_mac _ Hst Dk).
  - rewrite R4. exact (a2_host_mac _ Hcf).
  - exact R5.
  - rewrite R6. exact (a2_sum_mode _ Hcf).
  - unfold M_desk. apply length_sub; [wle|]. rewrite HB. wle.
  - exact (a1_sum_mode _ Hcf).
  - rewrite R7. exact (a3_io_send _ _ Hio).
  - rewrite R8. exact (a3_notify _ _ Hio).
  - rewrite R9. exact Dk.
  - exact R10.
  - exact R11.
  - rewrite R13. symmetry. exact (b7_host_counter _ Hst).
  - rewrite R14, Zg3. unfold INT_MAX. lia.
  - rewrite R15, Zgn. unfold INT_MAX. lia.
  - rewrite R16. exact (e1_fail_next _ _ Hmi).
Qed.

Lemma close_lib_nosend : forall now, (M_desk_known W0 = 0 \/ M_foreign W0 <> 0 \/ M_state W0 = S_CLOSED) ->
  diginet_session_close_m I None Wm now =
    Some (set_state_w (set_S_inflight Wm 0) DIGINET_S_CLOSED DIGINET_R_CLOSED, 0).
Proof.
  intros now Hc. pose proof (ac_st _ _ _ HC) as Hst. pose proof (ac_io _ _ _ HC) as Hio.
  destruct Hz as (_ & Zgn & _).
  apply (lib_close_nosend_ok I None Wm now HWl).
  - rewrite R1, R2, R17, (b2_desk_known _ Hst), (b3_foreign _ Hst), (b1_state _ Hst). exact Hc.
  - rewrite R8. exact (a3_notify _ _ Hio).
  - rewrite R15, Zgn. unfold INT_MAX. lia.
Qed.
End CloseLib.

(* an implication whose premise reads false: refute the premise alone *)
Ltac ovac :=
  lazymatch goal with
  | |- ?P -> _ =>
      let Hn := fresh "Hn" in
      assert (Hn : P -> False) by (wsimpq; kunfold; oclean; atomize; intro; lia);
      let Hp := fresh "Hp" in intro Hp; exfalso; exact (Hn Hp)
  end.












