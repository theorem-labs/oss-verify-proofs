(* One reception (fuzz_transport.c receive, FT:995-1025): the harness runs its model m_rx on the heap frame
   first (FT:1020, or FT:1003 inside a poll), and only then the library's diginet_session_rx on the same bytes
   (FT:1021, or DS:521 through io_recv inside poll), whose callbacks (notice FT:937, io_send FT:823) check the
   library against the model's post-reception state. The relations:
   - rx_pre: the world right before m_rx: agree_core (Agree.v) plus the per-operation facts op_begin and
     receive set up (OW and GOT zero, M.fail = g_fail_next, g_rx_send = the frame's send counter).
   - rx_accepts: the frame passes both filters (FT:283-300 / DS:268-294) and the session is not closed; under
     rx_pre the model's and the library's filters agree (L1, A2, B2), so this is one condition.
   - learn_M / learn_S: the desk the first announce names (FT:296-297 / DS:290-291).
   - lib_start Bm W: W is the world the library's switch (DS:298) starts from, Bm the world m_rx's switch and
     tick left: they differ only in the fields the library's prologue writes (stats.rx_frames, last_rx_us, the
     learnt desk) and the poll's g_rx fields (FT:1012-1015, io_recv FT:916).
   - rx_post: what the switch leaves for the library's tick (DS:317): agree_core, every OW count equal to the
     GOT count (settle's checks, FT:680-771), and the g_rx fields untouched.
   The branch lemmas (RxAnn, RxAck, RxData, RxMisc) are each `rx_branch cond` for one cond. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SettleOk RxDefs.
Import ListNotations.
Open Scope Z_scope.

(* the n bytes of the heap frame the library reads (receive passes the frame and n, FT:1021; poll's io_recv
   copies the first got of them, FT:917-927) *)
Definition rxbuf (fr : tframe) (n : Z) : list byte := firstn (Z.to_nat n) (tf_bytes fr).

(* the OW and GOT counts settle compares (FT:680-771) *)
Record ow_zero (B : list byte) : Prop := {
  oz_n : OW_n B = 0; oz_e2 : OW_e2 B = 0; oz_e3 : OW_e3 B = 0; oz_acks : OW_acks B = 0;
  oz_desk : OW_desk B = 0; oz_foreign : OW_foreign B = 0; oz_acked : OW_acked B = 0; oz_ndata : OW_ndata B = 0;
  gz_n : GOT_n B = 0; gz_e2 : GOT_e2 B = 0; gz_e3 : GOT_e3 B = 0; gz_acks : GOT_acks B = 0;
  gz_desk : GOT_desk B = 0; gz_foreign : GOT_foreign B = 0; gz_acked : GOT_acked B = 0; gz_ndata : GOT_ndata B = 0;
}.

Record ow_got_eq (B : list byte) : Prop := {
  og_n : GOT_n B = OW_n B;
  og_n_range : 0 <= OW_n B <= 8;
  og_t : forall i, 0 <= i < OW_n B -> i < TRANS_MAX ->
    GOT_t_state B i = OW_t_state B i /\ GOT_t_old B i = OW_t_old B i /\ GOT_t_reason B i = OW_t_reason B i;
  og_e2 : GOT_e2 B = OW_e2 B; og_e2_range : 0 <= OW_e2 B <= 2;
  og_e3 : GOT_e3 B = OW_e3 B; og_e3_range : 0 <= OW_e3 B <= 2;
  og_acks : GOT_acks B = OW_acks B; og_acks_range : 0 <= OW_acks B <= 2;
  og_desk : GOT_desk B = OW_desk B; og_desk_range : 0 <= OW_desk B <= 2;
  og_foreign : GOT_foreign B = OW_foreign B; og_foreign_range : 0 <= OW_foreign B <= 2;
  og_acked : GOT_acked B = OW_acked B; og_acked_range : 0 <= OW_acked B <= 2;
  og_ndata : GOT_ndata B = OW_ndata B; og_ndata_range : 0 <= OW_ndata B <= 2;
}.

Record rx_pre (I : timg) (ops : Z) (B : list byte) (buf : list byte) : Prop := {
  rp_core : agree_core I ops B;
  rp_ka : c2_keepalive B;
  rp_zero : ow_zero B;
  rp_fail : M_fail B = g_fail_next B;
  rp_rx_send : fr_code buf = DIGINET_OK -> g_rx_send B = fr_send buf;
}.

(* the frame passes the filters of both sides and the session is not closed (FT:283-300, DS:268-294) *)
Record rx_accepts (B : list byte) (buf : list byte) : Prop := {
  ra_code : fr_code buf = DIGINET_OK;
  ra_src : beq_bytes (fr_src buf) HOST = false;
  ra_dst : beq_bytes (fr_dst buf) HOST = true \/ beq_bytes (fr_dst buf) SPEC_BCAST = true;
  ra_known : M_desk_known B = 1 -> fr_src buf = M_desk B;
  ra_unknown : M_desk_known B = 0 -> ann_cmd (fr_cmd buf) = true /\ oui_of (fr_src buf) = true;
  ra_open : M_state B <> S_CLOSED;
}.

Definition learn_M (B : list byte) (buf : list byte) : list byte :=
  if M_desk_known B =? 0 then set_M_desk_known (set_M_desk B (fr_src buf)) 1 else B.

Definition learn_S (B : list byte) (buf : list byte) : list byte :=
  if S_desk_known B =? 0 then set_S_desk_known (set_S_desk_mac B (fr_src buf)) 1 else B.

(* the fields the library's prologue and the poll write between m_rx's end and the library's switch *)
Definition R_start : list (Z * Z) :=
  [(A_S_desk_known, 4); (A_S_desk_mac, 6); (A_S_stats_rx_frames, 8); (A_S_last_rx_us, 8);
   (OFF_g_rx_fail, 4); (OFF_g_rx_times, 4); (OFF_g_rx, 8); (OFF_g_rx_len, 8)].

(* W is Bm outside R_start (TQueueFacts / SimLib wframe), with the prologue's values in it *)
Definition in_rs (rs : list (Z * Z)) (a : Z) : Prop := Exists (fun '(k, n) => k <= a < k + n) rs.

Definition lib_start (Bm W : list byte) (buf : list byte) : Prop :=
  (length W = length Bm /\ forall a : nat, ~ in_rs R_start (Z.of_nat a) -> nth_error W a = nth_error Bm a) /\
  S_desk_known W = 1 /\ S_desk_mac W = fr_src buf /\ S_last_rx_us W = g_now Bm.

(* what the switch leaves for the library's tick (DS:317) *)
Record rx_post (I : timg) (ops : Z) (W W' : list byte) : Prop := {
  rq_core : agree_core I ops W';
  rq_og : ow_got_eq W';
  rq_rx : g_rx W' = g_rx W;
  rq_rx_len : g_rx_len W' = g_rx_len W;
  rq_rx_times : g_rx_times W' = g_rx_times W;
  rq_rx_fail : g_rx_fail W' = g_rx_fail W;
  rq_now : g_now W' = g_now W;
}.

(* what the model's reception writes: M, and GOT through OW (m_rx FT:280-375 writes M and OW only) *)
Definition R_mod : list (Z * Z) := [(OFF_M, SZ_M); (OFF_GOT, OFF_OW + SZ_OW - OFF_GOT)].

(* one branch of the switch, model then library, from the world before m_rx (FT:301-372 then DS:298-316).
   The heap frame is one object of the address space (malloc's block, FT:997): 0 < address and its end
   representable; m_rx stores f.body = frame + 30 in 8-byte cells (FT:311, :359) and the checks read the frame
   through them (FT:544, :566). *)
Definition rx_branch (cond : list byte -> list byte -> Prop) : Prop :=
  forall I ops fr n B,
    let buf := rxbuf fr n in
    let now := g_now B in
    0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
    0 < tf_addr fr /\ tf_addr fr + Z.of_nat (length (tf_bytes fr)) < 2 ^ 64 ->
    rx_pre I ops B buf -> rx_accepts B buf -> cond B buf ->
    exists Bm, m_rx_sw I fr n (set_M_last_rx (learn_M B buf) now) = Some (Bm, tt) /\
      m_tick_m Bm = Some (Bm, tt) /\
      (length Bm = length B /\ forall a : nat, ~ in_rs R_mod (Z.of_nat a) -> nth_error Bm a = nth_error B a) /\
      forall W, lib_start Bm W buf ->
        exists W', rx_sw I (Some fr) W buf now = Some (W', tt) /\ rx_post I ops W W'.

(* the poll's writes between m_rx and the library's rx (FT:1012-1015, io_recv FT:916) *)
Definition R_poll : list (Z * Z) := [(OFF_g_rx_fail, 4); (OFF_g_rx_times, 4); (OFF_g_rx, 8); (OFF_g_rx_len, 8)].

(* what one whole reception leaves for settle (FT:1023, SettleOk.v settle_ok): t = what m_rx returned *)
Record rx_done (I : timg) (ops t : Z) (W W' : list byte) : Prop := {
  rd_core : agree_core I ops W';
  rd_ka : c2_keepalive W';
  rd_og : ow_got_eq W';
  rd_drain : t = 1 -> drain_fact W';
  rd_rx : g_rx W' = g_rx W;
  rd_rx_len : g_rx_len W' = g_rx_len W;
  rd_rx_times : g_rx_times W' = g_rx_times W;
  rd_rx_fail : g_rx_fail W' = g_rx_fail W;
  rd_now : g_now W' = g_now W;
}.

(* ---- a reception that is not the first of its operation ----
   receive (p, n, 1, flags) with flags bit 0 set (FT:1006, :1014) hands the frame over twice: io_recv runs m_rx
   on each hand-over (FT:923-924) and the library's rx follows (DS:521, then DS:525 in the drain loop), with the
   poll's tick (DS:522) between the two. The second m_rx starts from a world whose OW and GOT agree but are not
   zero, and whose M.fail may differ from g_fail_next (a send of that tick consumed g_fail_next, FT:829). The
   relations below generalise rx_pre / rx_post / rx_done to such a world; rx_pre is the case OW = GOT = 0. *)

(* OW and GOT agree, with room for one more reception: each count at most 1, at most 4 transitions *)
Record ow_room (B : list byte) : Prop := {
  wr_og : ow_got_eq B;
  wr_n : OW_n B <= 4;
  wr_e2 : OW_e2 B <= 1; wr_e3 : OW_e3 B <= 1; wr_acks : OW_acks B <= 1; wr_desk : OW_desk B <= 1;
  wr_foreign : OW_foreign B <= 1; wr_acked : OW_acked B <= 1; wr_ndata : OW_ndata B <= 1;
}.

(* what one reception adds to OW: each count at most 1, at most 2 transitions (m_lost then m_wake, FT:315-318) *)
Record ow_step (B W : list byte) : Prop := {
  ws_n : OW_n W <= OW_n B + 2;
  ws_e2 : OW_e2 W <= OW_e2 B + 1; ws_e3 : OW_e3 W <= OW_e3 B + 1; ws_acks : OW_acks W <= OW_acks B + 1;
  ws_desk : OW_desk W <= OW_desk B + 1; ws_foreign : OW_foreign W <= OW_foreign B + 1;
  ws_acked : OW_acked W <= OW_acked B + 1; ws_ndata : OW_ndata W <= OW_ndata B + 1;
}.

(* an e0 with a full body: the one frame whose reception can wake, and so read M.fail (FT:227) against
   g_fail_next (io_send FT:826) *)
Definition rx_wake_buf (buf : list byte) : Prop := fr_cmd buf = DIGINET_CMD_ANNOUNCE /\ 33 <= fr_body_len buf.

(* the world right before m_rx, any reception of the operation *)
Record rx_pre_g (I : timg) (ops : Z) (B : list byte) (buf : list byte) : Prop := {
  rg_core : agree_core I ops B;
  rg_ka : c2_keepalive B;
  rg_room : ow_room B;
  rg_fail : rx_accepts B buf -> rx_wake_buf buf -> M_fail B = g_fail_next B;
  rg_rx_send : fr_code buf = DIGINET_OK -> g_rx_send B = fr_send buf;
}.

(* rx_post, and what the next reception of the operation needs (B: the world before m_rx) *)
Record rx_post_g (I : timg) (ops : Z) (B : list byte) (buf : list byte) (W W' : list byte) : Prop := {
  rh_post : rx_post I ops W W';
  rh_step : ow_step B W';
  rh_rx_send : g_rx_send W' = g_rx_send W;
  rh_wake : rx_wake_buf buf -> M_fail W' = g_fail_next W' /\ M_state W' <> S_ONLINE;
}.

Definition rx_branch_g (cond : list byte -> list byte -> Prop) : Prop :=
  forall I ops fr n B,
    let buf := rxbuf fr n in
    let now := g_now B in
    0 <= n <= Z.of_nat (length (tf_bytes fr)) ->
    0 < tf_addr fr /\ tf_addr fr + Z.of_nat (length (tf_bytes fr)) < 2 ^ 64 ->
    rx_pre_g I ops B buf -> rx_accepts B buf -> cond B buf ->
    exists Bm, m_rx_sw I fr n (set_M_last_rx (learn_M B buf) now) = Some (Bm, tt) /\
      m_tick_m Bm = Some (Bm, tt) /\
      (length Bm = length B /\ forall a : nat, ~ in_rs R_mod (Z.of_nat a) -> nth_error Bm a = nth_error B a) /\
      forall W, lib_start Bm W buf ->
        exists W', rx_sw I (Some fr) W buf now = Some (W', tt) /\ rx_post_g I ops B buf W W'.

(* rx_done, and what the next reception of the operation needs (B: the world before m_rx) *)
Record rx_done_g (I : timg) (ops t : Z) (B : list byte) (buf : list byte) (W W' : list byte) : Prop := {
  rk_done : rx_done I ops t W W';
  rk_step : ow_step B W';
  rk_rx_send : g_rx_send W' = g_rx_send W;
  rk_drain : t = 0 -> drain_fact B -> drain_fact W';
  rk_wake : rx_accepts B buf -> rx_wake_buf buf -> M_fail W' = g_fail_next W' /\ M_state W' <> S_ONLINE;
  rk_acc : rx_accepts W' buf -> rx_accepts B buf;
}.
