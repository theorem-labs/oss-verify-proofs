(* L1-L7: the library facts the simulation needs, stated over the names the transport model uses for the library
   (TSess.v / TSess0.v) and for fuzz/spec.h (TCb.v):
     diginet_frame_parse (buf, len, f)   = DgnSpec fr_code / fr_<field> of the len bytes (TSess.v header);
     diginet_frame_build                 = TNeed diginet_frame_build_code (the code) and DgnLib lib_frame (bytes);
     diginet_body_check                  = DgnLib body_check;
     diginet_announce_parse              = DgnSpec ann_code / ann_unknown and TSess ann_field;
     diginet_personality_from_name       = TNeed diginet_personality_from_name;
     diginet_frame_is_keepalive, diginet_mac_is_digidesign = DgnSpec fr_keepalive, oui_of;
     spec_read_frame, spec_system_at, spec_sum, spec_strz_len = DgnSpec (over zs of the bytes), strz_len;
     spec_build_frame                    = TNeed spec_build_frame; desk_named = TCb desk_named_m.
   Each simulation proof takes them as one hypothesis (HL : links); LinksProof.v discharges them. No Axiom:
   these are Definitions of Props. (DgnLib.v already proves the cores of L1-L3: spec_read_frame_fr,
   diginet_body_check_body_check, body_check_spec, spec_system_at_system_at, frame_build_ok.) *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess.
Import ListNotations.
Open Scope Z_scope.

(* L1 parse agreement (m_rx FT:280-375 vs diginet_session_rx DS:263-318; check_ack_frame, check_state_data).
   For 0 <= len <= length b: the library's parse of the first len bytes is OK iff spec_read_frame of b over len
   is SPEC_OK, and then they read the same fields. *)
Definition L1_stmt : Prop :=
  forall (b : list byte) (len : Z), 0 <= len <= Z.of_nat (length b) ->
    let bb := firstn (Z.to_nat len) b in
    let f := spec_read_frame (zs b) len in
    (fr_code bb = DIGINET_OK <-> sf_code f = SPEC_OK) /\
    (fr_code bb = DIGINET_OK ->
       sf_dst f = 0 /\ sf_src f = SPEC_MAC /\ sf_cmd f = fr_cmd bb /\ sf_send f = fr_send bb /\
       sf_ack f = fr_ack bb /\ sf_retry f = fr_retry bb /\ sf_ncmds f = fr_ncmds bb /\
       sf_body f = SPEC_BODY_AT /\ sf_body_len f = fr_body_len bb /\ sf_sum f = fr_sum bb /\
       sf_pad_len f = fr_pad_len bb /\ sf_body_sum f = fr_body_sum bb).

(* L2 build then read (check_sent_frame, check_ack_frame, check_latest_frame, check_latest_control,
   check_inflight_retry; DS:97-109, :388-401). A body bd of n <= 1484 bytes that body_check accepts, a buffer
   of cap >= max(60, 30 + n) bytes, mode SUM_BODY or SUM_ZERO, header fields in range: the build answers
   out = max(60, 30 + n), writes out bytes, and spec_read_frame reads them back as built. The refusal side:
   a refused body gives E_REFUSED, a body over 1484 bytes E_LENGTH (-4). *)
Definition L2_stmt : Prop :=
  forall (dst src : list byte) (send ack retry cmd ncmds : Z) (bd : list byte) (cap mode : Z),
    length dst = 6%nat -> length src = 6%nat ->
    (mode = DIGINET_SUM_BODY \/ mode = DIGINET_SUM_ZERO) ->
    0 <= send < 2 ^ 32 -> 0 <= ack < 2 ^ 32 -> 0 <= retry < 2 ^ 16 -> 0 <= cmd < 2 ^ 8 -> 0 <= ncmds < 2 ^ 8 ->
    (Z.of_nat (length bd) <= DIGINET_MAX_BODY_LEN -> body_check bd = DIGINET_OK ->
     frame_len (length bd) <= cap ->
     let out := frame_len (length bd) in
     let bytes := lib_frame dst src send ack retry cmd ncmds bd mode in
     let f := spec_read_frame (zs bytes) out in
     diginet_frame_build_code bd cap mode = out /\ Z.of_nat (length bytes) = out /\
     sf_code f = SPEC_OK /\ sub bytes (sf_dst f) 6 = dst /\ sub bytes (sf_src f) 6 = src /\
     sf_cmd f = cmd /\ sf_send f = send /\ sf_ack f = ack /\ sf_retry f = retry /\ sf_ncmds f = ncmds /\
     sf_body_len f = Z.of_nat (length bd) /\ sub bytes SPEC_BODY_AT (length bd) = bd /\
     forallb (fun x => bz x =? 0) (skipn (Z.to_nat (SPEC_BODY_AT + Z.of_nat (length bd))) bytes) = true /\
     sf_sum f = (if mode =? DIGINET_SUM_ZERO then 0 else spec_sum_at (zs bd) 0 (Z.of_nat (length bd)))) /\
    (Z.of_nat (length bd) <= DIGINET_MAX_BODY_LEN -> body_check bd <> DIGINET_OK ->
     diginet_frame_build_code bd cap mode = DIGINET_E_REFUSED) /\
    (DIGINET_MAX_BODY_LEN < Z.of_nat (length bd) -> diginet_frame_build_code bd cap mode = -4).

(* L3 body check is the harness's system test (check_refusal_submit FT:656-665, check_sent_frame FT:405-406,
   take DS:363-366). For 0 <= n <= length b: diginet_body_check of the first n bytes is OK iff
   spec_system_at b n < 0, its only other value is E_REFUSED, and the prefix lemma. *)
Definition L3_stmt : Prop :=
  forall (b : list byte) (n : Z), 0 <= n <= Z.of_nat (length b) ->
    (body_check (firstn (Z.to_nat n) b) = DIGINET_OK <-> spec_system_at (zs b) n < 0) /\
    (body_check (firstn (Z.to_nat n) b) = DIGINET_OK \/
     body_check (firstn (Z.to_nat n) b) = DIGINET_E_REFUSED) /\
    (spec_system_at (zs b) n < 0 -> forall k, 0 <= k <= n -> spec_system_at (zs b) k < 0).

(* L4 announce (check_state_desk FT:527-557 vs on_announce DS:184-221). On a parsed frame bb with cmd E0 or E1:
   the announce parse is OK iff body_len >= SPEC_ANN_MIN (33); then unknown is the 15 bytes at the body, and
   for X = version (15) and name (24), with k = spec_strz_len at body + X, the field the library fills holds
   the k bytes there, then a NUL (k <= 9 < 10). *)
Definition L4_stmt : Prop :=
  forall (bb : list byte), fr_code bb = DIGINET_OK -> ann_cmd (fr_cmd bb) = true ->
    (ann_code (fr_cmd bb) (fr_body_len bb) = DIGINET_OK <-> SPEC_ANN_MIN <= fr_body_len bb) /\
    (ann_code (fr_cmd bb) (fr_body_len bb) = DIGINET_OK ->
       ann_unknown (fr_body bb) = firstn (Z.to_nat SPEC_ANN_UNKNOWN) (skipn (Z.to_nat SPEC_BODY_AT) bb) /\
       forall X, X = SPEC_ANN_VERSION \/ X = SPEC_ANN_NAME ->
         let at_x := skipn (Z.to_nat (SPEC_BODY_AT + X)) bb in
         let k := strz_len at_x in
         let fld := ann_field (skipn (Z.to_nat X) (fr_body bb)) in
         (k <= 9)%nat /\ firstn k fld = firstn k at_x /\ at8 fld k = 0).

(* L5 personality (check_state_desk FT:534-536 vs on_announce DS:191-197). rest = the bytes from the body on
   (33 of them at least): with name = the copy_strz of at most 9 bytes at rest + 24, the library's personality
   is entry i of personalities exactly when the harness's desk_named (FT:265-273) names a desk d (SPEC_C24 for
   i = 0, SPEC_PC for i = 1), with the same device and strips; NULL exactly when desk_named is NULL. *)
Definition L5_stmt : Prop :=
  forall (I : timg) (B : list byte) (rest : list byte), SPEC_ANN_MIN <= Z.of_nat (length rest) ->
    let name := skipn (Z.to_nat SPEC_ANN_NAME) rest in
    exists dp, desk_named_m I B rest = Some (B, dp) /\
    match diginet_personality_from_name (firstn (copy_len 10 9 name) name) with
    | Some i => exists p d, personality_at i = Some p /\
        ((i = 0 /\ dp = ti_spec_c24 I /\ d = c24) \/ (i = 1 /\ dp = ti_spec_pc I /\ d = pc)) /\
        dp_device p = d_dev d /\ dp_strips p = d_strips d
    | None => dp = 0
    end.

(* L6 keepalive / OUI (m_rx FT:344-365, io_send FT:854) *)
Definition L6_stmt : Prop :=
  (forall bb : list byte, fr_code bb = DIGINET_OK ->
     (fr_keepalive bb = true <->
      fr_cmd bb = DIGINET_CMD_DATA /\ fr_body_len bb = 1 /\ at8 (fr_body bb) 0 = 0)) /\
  (forall mac : list byte, (3 <= length mac)%nat ->
     (oui_of mac = true <-> beq_bytes (firstn 3 mac) SPEC_OUI = true)).

(* L7 spec_build_frame then read (op_frame / op_announce FT:1027-1066): for len <= SPEC_MAX_BODY the frame
   reads back OK with the fields given, n = max(60, 30 + len), zero_sum = 0 and the harness's sum. *)
Definition L7_stmt : Prop :=
  forall (dst src : list byte) (send ack retry cmd ncmds : Z) (body : list byte),
    length dst = 6%nat -> length src = 6%nat -> Z.of_nat (length body) <= SPEC_MAX_BODY ->
    0 <= send < 2 ^ 32 -> 0 <= ack < 2 ^ 32 -> 0 <= retry < 2 ^ 16 -> 0 <= cmd < 2 ^ 8 -> 0 <= ncmds < 2 ^ 8 ->
    let r := spec_build_frame dst src send ack retry cmd ncmds body 0 in
    let frame := fst r in
    let n := snd r in
    let f := spec_read_frame (zs frame) n in
    n = frame_len (length body) /\ Z.of_nat (length frame) = n /\
    sf_code f = SPEC_OK /\ sub frame (sf_dst f) 6 = dst /\ sub frame (sf_src f) 6 = src /\
    sf_cmd f = cmd /\ sf_send f = send /\ sf_ack f = ack /\ sf_retry f = retry /\ sf_ncmds f = ncmds /\
    sf_body_len f = Z.of_nat (length body) /\ sub frame SPEC_BODY_AT (length body) = body /\
    forallb (fun x => bz x =? 0) (skipn (Z.to_nat (SPEC_BODY_AT + Z.of_nat (length body))) frame) = true /\
    sf_sum f = spec_sum body.

Definition links : Prop := L1_stmt /\ L2_stmt /\ L3_stmt /\ L4_stmt /\ L5_stmt /\ L6_stmt /\ L7_stmt.
