From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPack3 SlotPack3 AllocBound.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require SlotParse.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocPackGSF.
Import ListNotations.
Local Open Scope Z_scope.

Definition LOOP_BODY : Z := 0x14144.
Definition LOOP_EXIT : Z := 0x14658.
Definition SLOT_FRAME : Z := 192.
Definition OPS_MAX : Z := 512.
Definition INPUT_MAX : Z := 2 ^ 26.
Definition WRITE_MAX : Z := 65535.
Definition DIV10 : Z := 0x199999999999999a.
Definition CLIENT_BASE : Z := 0x210e4.
Definition G_WAKE0 : Z := 0x21628.

Record sstart := SS {
  ss_L : layout; ss_A : astate; ss_regs : bvmap 5 word; ss_mem : word -> option byte; ss_md : Model;
  ss_p : Z; ss_n : Z; ss_pl : list byte; ss_b : pbound3; ss_T : list (Z * Z) }.

Definition in_byte (E : sstart) (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) (ss_pl E) (Z_to_bv 8 0)).
Definition op_at (E : sstart) (k : Z) : Z := in_byte E k mod 10.
Definition slot_sp (E : sstart) : Z := spZ (ss_regs E) - SLOT_FRAME.
Definition head_body (E : sstart) (t k : Z) : bool := (t <? OPS_MAX) && (k <? ss_n E).
Definition head_pc (E : sstart) (t k : Z) : Z := if head_body E t k then LOOP_BODY else LOOP_EXIT.

Definition saved_cells (regs : bvmap 5 word) : list cell :=
  [C8 (getr regs 27); C8 (getr regs 26); C8 (getr regs 25); C8 (getr regs 24); C8 (getr regs 23);
   C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
   C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)].

Definition head_regs (E : sstart) (t k : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = Z_to_bv 64 (slot_sp E) /\ getr regs 3 = getr (ss_regs E) 3 /\
  getr regs 4 = getr (ss_regs E) 4 /\ getr regs 20 = Z_to_bv 64 G_RELAY_LO /\
  (head_body E t k = true ->
     getr regs 9 = Z_to_bv 64 (ss_n E - k) /\ getr regs 18 = Z_to_bv 64 (ss_p E + k) /\
     getr regs 22 = Z_to_bv 64 t /\ getr regs 24 = Z_to_bv 64 1 /\
     getr regs 23 = Z_to_bv 64 (slot_sp E + 32) /\ getr regs 25 = Z_to_bv 64 DIV10 /\
     getr regs 21 = Z_to_bv 64 10 /\ getr regs 19 = Z_to_bv 64 4 /\
     getr regs 27 = Z_to_bv 64 (G_S + 4)).

Definition pair_cost (e : rentry) (p : hsrc * nat) : Z :=
  keys_total (re_keys e) + Z.of_nat (length (pending_stream (fst p))) + (if re_skip e =? 0 then re_used e else 0).

Definition slot_cost (es : list rentry) (hj : list (hsrc * nat)) : Z :=
  fold_right Z.add 0 (map (fun q => pair_cost (fst q) (snd q)) (combine es hj)).

Definition target_addrs (G OUT : Z) (es : list rentry) (hj : list (hsrc * nat)) : list Z :=
  G :: OUT :: concat (map entry_blocks es) ++ concat (map (fun p => hs_blocks (fst p)) hj).

Definition slot_open (hj : list (hsrc * nat)) (i : nat) : bool := existsb (Nat.eqb i) (map snd hj).

Fixpoint sp_pos (d : list Z) (f : nat) (k : Z) : Z :=
  match f with
  | O => k
  | S f' => if k <? SlotParse.zlen d then sp_pos d f' (fst (SlotParse.sp_pass d k)) else k
  end.

Definition walk_at (pl : list byte) (t k : Z) : Prop := 0 <= t /\ k = sp_pos (SlotParse.plz pl) (Z.to_nat t) 0.

Lemma walk_start pl : walk_at pl 0 0.
Proof. split; [lia|reflexivity]. Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at, wr_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros (((W1 & W2) & B1 & B2) & H0 & H1 & HW).
    rewrite (cells_bytes_length cs1 W1) in B2.
    split; (split; [split; assumption|]); (split; [lia|]); (split; [lia|]); intros i Hi.
    + apply HW. lia.
    + replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply HW. lia.
  - intros (((W1 & B1) & H0 & H1 & HW1) & ((W2 & B2) & H2 & H3 & HW2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2.
    split; [split; [split; assumption|split; assumption]|]. rewrite (cells_bytes_length cs1 W1) in B2.
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec0 i (Z.of_nat (cells_size cs1))); [apply HW1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply HW2. lia.
Qed.

Definition ecap_ok (c : Z) : Prop := c = 0 \/ exists k, 0 <= k <= 22 /\ c = 8 * 2 ^ k.

Lemma ecap_ok_lt c : ecap_ok c -> 0 <= c < 2 ^ 26.
Proof.
  intros [->|(k & Hk & ->)]; [lia|].
  pose proof (Z.pow_nonneg 2 k ltac:(lia)) as P0.
  assert (P1 : 2 ^ k <= 2 ^ 22) by (apply Z.pow_le_mono_r; lia).
  assert (E1 : 2 ^ 22 = 4194304) by reflexivity. assert (E2 : 2 ^ 26 = 67108864) by reflexivity. lia.
Qed.

Definition NC_PER : Z := 32.

Definition DATA_PER : Z := 2.

Definition nw_list (l : HarnessRep.hlist) : Z :=
  Z.max (16 * HarnessRep.hl_cap l) (NC_PER * HarnessRep.hl_n l + 128).

Definition nw_src (h : HarnessRep.hsrc) : Z :=
  nw_list (HarnessRep.hs_pending h) + DATA_PER * Z.of_nat (length (HarnessRep.pending_stream h)) +
  CF.op_add_c.PARTIAL_BYTES + nw_list (HarnessRep.hs_expected h) + nw_list (HarnessRep.hs_held h).

Definition nw_ent (e : CF.RelayRep.rentry) : Z :=
  Z.max (CF.RelayRep.re_cap e) (DATA_PER * CF.RelayRep.re_used e + 8192) +
  Z.max (if CF.RelayRep.re_hp e =? 0 then 0 else CF.RelayRep.re_kh e) (8 * CF.RelayRep.re_nheld e + 8).

Definition NW_SRC0 : Z := 3 * 128 + CF.op_add_c.PARTIAL_BYTES.

Definition NW_ENT0 : Z := 8192 + 8.

Definition nc_wt (es : list CF.RelayRep.rentry) (hj : list (HarnessRep.hsrc * nat)) : Z :=
  CF.relay_add_b_c.SRC_TABLE + TBBYTES + zsum nw_ent es + zsum (fun p => nw_src (fst p)) hj +
  (4 - Z.of_nat (length es)) * NW_ENT0 + (4 - Z.of_nat (length hj)) * NW_SRC0.

Definition NC_FIX : Z := CF.relay_add_b_c.SRC_TABLE + TBBYTES + 4 * NW_ENT0 + 4 * NW_SRC0.

Definition ekey_of (ln : list Z) : list Z :=
  match RelayModel.gesture ln with
  | Some (RelayModel.GBegin, x) => [Z.of_nat (length x) + 1]
  | _ => []
  end.

Definition ekeys (ls : list (list Z)) : list Z := concat (map ekey_of ls).

Definition ekeys_hl (l : HarnessRep.hlist) : list Z :=
  ekeys (map (fun r => HarnessRep.bzs (snd r)) (HarnessRep.hl_recs l)).

Definition ek_view (hj : list (HarnessRep.hsrc * nat)) : list Z :=
  concat (map (fun p => ekeys_hl (HarnessRep.hs_expected (fst p))) hj).

Lemma ek_view_nil : ek_view [] = [].
Proof. reflexivity. Qed.

Lemma ekey_of_nonneg ln : Forall (fun n => 0 <= n) (ekey_of ln).
Proof. unfold ekey_of. destruct (RelayModel.gesture ln) as [[[|] x]|]; repeat constructor; lia. Qed.

Lemma ek_view_nonneg hj : Forall (fun n => 0 <= n) (ek_view hj).
Proof.
  apply Forall_forall. intros n Hn. unfold ek_view in Hn.
  apply in_concat in Hn as (l1 & Hl1 & Hn). apply in_map_iff in Hl1 as (p & <- & _).
  unfold ekeys_hl, ekeys in Hn. apply in_concat in Hn as (l2 & Hl2 & Hn).
  apply in_map_iff in Hl2 as (ln & <- & _).
  exact (proj1 (Forall_forall _ _) (ekey_of_nonneg ln) n Hn).
Qed.

Section LI.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variable ra empty : Z.
Variable j : nat.
Variable E : sstart.
Variable CS : list byte -> list Z.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition slot_cfg : config :=
  mkCfg (YK11.mkst (ss_regs E) (Z_to_bv 64 ENTRY) (ss_mem E) (seg_rom segs)) (ss_md E).

Definition slot_pre : Prop :=
  lib_pre_w B API SLOT_STACK empty (ss_L E) (ss_A E) (ss_regs E) (ss_mem E) (ss_md E) ra
    (ss_p E) (ss_n E) (ss_pl E) /\
  (res_ok_pack3 (ss_A E) (ss_b E) /\ GSF (ss_A E)) /\
  pack3_entry CS frame_MCAP (ss_pl E) (ss_T E) (ss_b E) /\
  p3_mis (ss_b E) = [] /\
  GI_t j (ss_T E) (ss_mem E) /\
  tb_live (ss_L E) (ss_A E) (ss_T E) /\
  (0 < ss_n E -> ~ In (ss_p E, ss_n E) (ss_T E)) /\
  G_img_c B frame_RELRO (ss_mem E) /\
  ro_agree segs (ss_mem E) /\
  spZ (ss_regs E) <= TASK_SIZE /\
  frm_zero fp_csr.

Definition slot_post (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md' T',
    c' = mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    lib_post_cgp3 B API (CS (ss_pl E)) frame_MCAP G_reply SLOT_STACK (ss_L E) (ss_A E) (ss_regs E) (ss_mem E) (ss_md E)
      (ss_p E) (ss_n E) (ss_b E) (LL 0 (m_fs (ss_md E)) []) (ss_T E) T' L' A' regs' mem' md' /\
    GI_t (S j) T' mem'.

Definition driver_kept (TA : list Z) (L : layout) (A : astate) (mem : word -> option byte) : Prop :=
  (forall q m, In (q, m) (user_blocks (ss_A E)) -> ~ In (ptr_addr (ss_L E) q, m) (ss_T E) ->
     (0 < m -> ~ In (ptr_addr (ss_L E) q) TA) /\
     exists q', In (q', m) (user_blocks A) /\ ptr_addr L q' = ptr_addr (ss_L E) q) /\
  (forall q m i, In (q, m) (user_blocks (ss_A E)) -> ~ In (ptr_addr (ss_L E) q, m) (ss_T E) ->
     ptr_addr (ss_L E) q <> ss_p E -> 0 <= i < m ->
     mbyte segs mem (ptr_addr (ss_L E) q + i) = mbyte segs (ss_mem E) (ptr_addr (ss_L E) q + i)) /\
  (forall i, 0 <= i < ss_n E -> mbyte segs mem (ss_p E + i) = mbyte segs (ss_mem E) (ss_p E + i)) /\
  (forall q m, In (q, m) (blocks L A) ->
     (In (q, m) (blocks (ss_L E) (ss_A E)) /\ ~ In (q, m) (ss_T E)) \/ In q TA).

Definition image_kept (mem : word -> option byte) : Prop :=
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals G_reply a ->
     mbyte segs mem a = mbyte segs (ss_mem E) a /\ (writable_at segs (ss_mem E) a <-> writable_at segs mem a)) /\
  (forall a, in_globals G_reply a -> writable_at segs (ss_mem E) a <-> writable_at segs mem a) /\
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B SLOT_STACK (ss_regs E) a ->
     mbyte segs mem a = mbyte segs (ss_mem E) a /\ (writable_at segs (ss_mem E) a <-> writable_at segs mem a)) /\
  (forall a, lib_scratch B SLOT_STACK (ss_regs E) a -> writable_at segs mem a).

Definition stack_at (t k : Z) (mem : word -> option byte) : Prop :=
  rw_cells segs mem (slot_sp E + 88) (saved_cells (ss_regs E)) /\
  rw_cells segs mem (slot_sp E) [C8 (Z_to_bv 64 CLIENT_BASE)] /\
  (head_body E t k = true -> rw_cells segs mem (slot_sp E + 8) [C8 (Z_to_bv 64 G_S)]).

Definition globals_at (mem : word -> option byte) (cl br gn dd ei N G nfd : Z) (mx nout cap out : word) : Prop :=
  rw_cells segs mem G_LISTEN [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 cl)] /\
  rw_cells segs mem G_WAKE0 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
  rw_cells segs mem G_THREAD_UP [C1 (Z_to_bv 8 0)] /\
  rw_cells segs mem G_BROKEN [C1 (Z_to_bv 8 br)] /\
  rw_cells segs mem G_GONE [C1 (Z_to_bv 8 gn)] /\
  rw_cells segs mem G_DEAD [C1 (Z_to_bv 8 dd)] /\
  rw_cells segs mem G_EINTR [C1 (Z_to_bv 8 ei)] /\
  rw_cells segs mem G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)] /\
  rw_cells segs mem G_NFD [C4 (Z_to_bv 64 nfd)] /\
  rw_cells segs mem G_SRC [C8 (Z_to_bv 64 G)] /\
  rw_cells segs mem G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] /\
  rw_cells segs mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
  rw_cells segs mem (G_LOCK + 12) [CB 28 (nulbytes 28)] /\
  (exists ev, rw_cells segs mem (errno_addr B) [C4 ev]) /\
  (cl = 3 \/ cl = -1) /\ (br = 0 \/ br = 1) /\ (gn = 0 \/ gn = 1) /\ (dd = 0 \/ dd = 1) /\ (ei = 0 \/ ei = 1) /\
  ((gn = 0 -> cl = 3 /\ br = 0 /\ dd = 0) /\ (gn = 1 -> cl = -1 \/ br = 1 \/ dd = 1)) /\
  bv_unsigned mx <= 255.

Definition output_at (L : layout) (A : astate) (mem : word -> option byte) (nout cap out : word) : Prop :=
  let NO := bv_unsigned nout in
  let CAP := bv_unsigned cap in
  let OUT := bv_unsigned out in
  (exists O junk,
     (CAP = 0 /\ OUT = 0 /\ NO = 0 /\ O = []) \/
     (0 < CAP /\ NO <= CAP /\ In (OUT, CAP) (blocks L A) /\ fresh_block B OUT CAP /\
      bytes_at segs mem OUT (O ++ junk) /\ Z.of_nat (length O) = NO /\ Z.of_nat (length junk) = CAP - NO)) /\
  CAP <= TBBYTES.

Definition pair_ok (L : layout) (A : astate) (mem : word -> option byte) (t : Z) (e : rentry) (p : hsrc * nat)
    : Prop :=
  let h := fst p in
  src_at B L A mem (G_S + SRC_SIZE * Z.of_nat (snd p)) h /\ (snd p < 4)%nat /\
  hs_fd h = re_fd e /\
  (re_eof e = 0 -> re_skip e = hs_overlong h /\ (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h))) /\
  same_set (keys_texts (re_keys e)) (texts (hs_held h)) /\ NoDup (texts (hs_held h)) /\
  hl_recs (hs_expected h) = [] /\
  hl_n (hs_pending h) <= t /\ hl_cap (hs_pending h) <= Z.max 8 (2 * t) /\
  Z.of_nat (length (pending_stream h)) <= WRITE_MAX * t /\
  ecap_ok (hl_cap (hs_expected h)) /\ hl_cap (hs_held h) < 2 ^ 24.

Definition relay_at (L : layout) (A : astate) (mem : word -> option byte) (t nfd G OUT : Z)
    (es : list rentry) (hj : list (hsrc * nat)) : Prop :=
  (exists tail, table_at B mem G es tail) /\
  In (G, SRC_TABLE) (blocks L A) /\ fresh_block B G SRC_TABLE /\
  Forall (entry_ok B L A mem) es /\
  NoDup (map re_fd es) /\
  Forall (fun e => FIRST_FD <= re_fd e < FIRST_FD + nfd) es /\
  Forall2 (pair_ok L A mem t) es hj /\
  NoDup (map snd hj) /\
  (forall i, (i < 4)%nat -> slot_open hj i = false ->
     rw_cells segs mem (G_S + SRC_SIZE * Z.of_nat i) [CB 96%nat (nulbytes 96)]) /\
  NoDup (target_addrs G OUT es hj).

Definition pend_view (hj : list (hsrc * nat)) : list (list (list byte)) :=
  map (fun p => map snd (hl_recs (hs_pending (fst p)))) hj.

Definition arr_nc (l : hlist) : list Z := if hl_cap l =? 0 then [] else [hl_v l].

Definition src_nc (h : hsrc) : list Z :=
  arr_nc (hs_pending h) ++ [hs_partial h] ++ arr_nc (hs_expected h) ++ arr_nc (hs_held h).

Definition entry_nc (e : rentry) : list Z :=
  (if re_cap e =? 0 then [] else [re_buf e]) ++ (if re_hp e =? 0 then [] else [re_hp e]).

Record rview := RV { rv_pend : list (list (list byte)); rv_nc : list Z; rv_wt : Z; rv_ek : list Z }.

Definition view_of (G OUT : Z) (es : list rentry) (hj : list (hsrc * nat)) : rview :=
  RV (pend_view hj) (G :: OUT :: concat (map entry_nc es) ++ concat (map (fun p => src_nc (fst p)) hj))
     (nc_wt es hj) (ek_view hj).

Definition LI (RI : sstart -> Z -> rview -> layout -> astate -> Prop) (t k : Z) (c : config) : Prop :=
  exists (fx' : FPState) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
         (cl br gn dd ei G nfd : Z) (mx nout cap out : word) (es : list rentry) (hj : list (hsrc * nat)),
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 (head_pc E t k)) mem (seg_rom segs)) md /\
    frm_zero (@fp_csr fx') /\
    0 <= t <= OPS_MAX /\ 0 <= k <= ss_n E /\ walk_at (ss_pl E) t k /\ ss_n E < INPUT_MAX /\
    head_regs E t k regs /\
    MR L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
    (exists vm, md = with_vmmaps vm (ss_md E)) /\
    ro_agree segs mem /\
    image_kept mem /\
    stack_at t k mem /\
    driver_kept (target_addrs G (bv_unsigned out) es hj) L A mem /\
    globals_at mem cl br gn dd ei (Z.of_nat (length es)) G nfd mx nout cap out /\
    0 <= nfd <= t + 1 /\
    output_at L A mem nout cap out /\
    relay_at L A mem t nfd G (bv_unsigned out) es hj /\
    (length es <= 4)%nat /\
    slot_cost es hj <= k /\
    RI E k (view_of G (bv_unsigned out) es hj) L A.

End LI.

Lemma LI_walk : forall rc B API E RI t k c, LI (rc := rc) B API E RI t k c -> walk_at (ss_pl E) t k.
Proof.
  intros rc B API E RI t k c
    (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
     _ & _ & _ & _ & HW & _).
  exact HW.
Qed.
