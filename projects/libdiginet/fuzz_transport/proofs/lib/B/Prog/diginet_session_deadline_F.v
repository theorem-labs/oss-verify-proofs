From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_deadline_c diginet_session_deadline_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of diginet_session_deadline_contract_F (image B, entry 0x8a6c0, frame 16 bytes), with StepF's step: every
   access side goal is closed from the rng fact of the accessed range.

   The function reads only fields of g_s's payload [S, S + 18264) = [0x5df640, 0x5e3d98), the two runtime cells and
   the shadow bytes of that payload, and writes only its own 16-byte frame.

   WHY NO INSTRUMENTED CHECK FAILS. S is 8-aligned and 18264 is a multiple of 8, so the payload is a whole number of
   ASan granules. For any offset o in it, the byte at the end of o's granule is in the payload too, so the
   `addressable` premise gives that granule's shadow byte k with k = 0 or (7 < k <= 7): k = 0 (sd_shadow0). Every
   check therefore reads a zero shadow byte and its `bne` falls through, so none of the nine __asan_report_load4,
   seven __asan_report_load8 and one __asan_report_load1 calls, and none of the compare handlers before them, is
   reached.

   WHY THE TRAP WORD AT 0x8a9a8 IS NOT REACHED. Three UBSan branches go to it:
     0x8a6e0  bne (s & 7), zero: s = 0x5df640, so s & 7 = 0 and the branch falls through.
     0x8a8f4  beq t1, t3 with t1 = i + 1 and t3 = 513: the scan's invariant keeps i < 512 (LOOP below). The scan
              reaches turn i + 1 only when the model's deadline_display_only_m takes its recursive arm at i + 1, and
              that arm needs i + 1 < S_queue_N = 512; at i + 1 >= 512 the model is None, which the premise
              diginet_session_deadline_m Bw now = Some r rules out.
     0x8a8f8  bltu t2, a7 with t2 = ~(s + 1760) = 2^64 - 1 - 0x5dfd20 and a7 = 32 i <= 32 * 511: never taken.

   The walk, against the model (TSess0.diginet_session_deadline_m, cut below at the binary's join points):
     0x8a6c0-0x8a6c4  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk. It is the only store.
     0x8a6c8-0x8a6d4  a2 = s; a0 = now + 1000000 (d of :478).
     0x8a6d8          beq a2,zero: not taken (s = 0x5df640).
     0x8a6dc-0x8a6e0  the alignment check of s: not taken.
     0x8a6e4-0x8a6ec  a3 = [GOT_CELL_K] = CELL_K; a5 = [CELL_K] = 0x7fff8000, the shadow base.
     0x8a6f0-0x8a704  the check and the 4-byte load of s->state.
     0x8a708-0x8a71c  the state dispatch: 0 and 3 return d (:479-480); 1 is the waking arm, 2 the online arm; any
                      other state joins at 0x8a824 with a6 = 0 (not online).
     0x8a720-0x8a768  state 1: d = min64 (d, wake_sent_us + ms (cfg.wake_timeout_ms)) (:481-482); a6 = 0; -> 0x8a824.
     0x8a780-0x8a820  state 2: d = min64 (d, last_rx_us + ms (cfg.offline_ms)) (:484); a6 = 1; when inflight = 0 also
                      d = min64 (d, max (backoff_until_us, next_keepalive_us)) (:487-489); -> 0x8a824.
     0x8a824-0x8a83c  the join: the check and the load of s->inflight.
     0x8a840-0x8a880  inflight <> 0: a0 = min64 (d, inflight_sent_us + ms (cfg.ack_timeout_ms)) and return WITHOUT
                      the clamp (:491-492), as the model's dl_tail returns that value directly.
     0x8a884-0x8a88c  ld ra,8(sp); addi sp,sp,16; ret: the one return.
     0x8a890          inflight = 0 and not online: -> the clamp at 0x8a9a0 with d.
     0x8a894-0x8a8b4  the check and the load of s->queued; queued = 0 -> the clamp with d.
     0x8a8b8-0x8a8d4  the check and the load of s->backoff_until_us; a4 = t = max (now, backoff_until_us) (:494).
     0x8a8d8-0x8a8f0  the scan's setup: a7 = 0, t0 = a3 = &s->queue[0].display, t1 = 1, t2 = ~(s + 1760), t3 = 513.
     0x8a8f4-0x8a928  the scan of :495-497, one turn per deadline_display_only_m step: the two UBSan tests, the check
                      and the 1-byte load of s->queue[i].display, the test i + 1 < queued and the test display <> 0.
     0x8a93c-0x8a994  :498-499: when display_only and s->display_sent, t = max (t, last_display_us + cfg.display_gap_us).
     0x8a998-0x8a99c  a0 = min64 (d, t) (:500).
     0x8a9a0-0x8a9a4  the clamp a0 = max (now, a0) (:502), then the return.

   The world after the run: the run writes only its frame, which the off_stk premise puts outside the hull
   [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 payloads, so tw_at holds at the new memory with the same Bw
   (TMAP_B_kept).

   Template: image A's walk of this function (lib/A/Prog/diginet_session_deadline_F.v): the same model cuts, the same
   continuation structure, image B's addresses, registers and UBSan branches. *)

(* ============================================================================
   The model, cut at the binary's join points (image A's walk's definitions)
   ============================================================================ *)

Definition dl_clamp (now d : Z) : Z := if d <? now then now else d.

Definition dl_tdisp (B : list byte) (dsp t : Z) : Z :=
  if negb (dsp =? 0) && negb (TW.S_display_sent B =? 0) then
    let g := TS0.u64 (TW.S_last_display_us B + TW.S_cfg_display_gap_us B) in if g <? t then t else g
  else t.

Definition dl_t (B : list byte) (now dsp : Z) : Z :=
  dl_tdisp B dsp (if now <? TW.S_backoff_until_us B then TW.S_backoff_until_us B else now).

Definition dl_tail (B : list byte) (now d : Z) (online : bool) : option Z :=
  if negb (TW.S_inflight B =? 0) then
    Some (TS0.min64_m d (TS0.u64 (TW.S_inflight_sent_us B + TS0.ms_m (TW.S_cfg_ack_timeout_ms B))))
  else
  let dq := if online && negb (TW.S_queued B =? 0) then
      match TS0.deadline_display_only_m B 0 1 (Z.to_nat (TW.S_queued B)) with
      | None => None
      | Some dsp => Some (TS0.min64_m d (dl_t B now dsp))
      end
    else Some d in
  match dq with
  | None => None
  | Some d => Some (dl_clamp now d)
  end.

Definition dl_dO (B : list byte) (now : Z) : Z :=
  let d := if TW.S_state B =? 1
           then TS0.min64_m (TS0.u64 (now + 1000000))
                  (TS0.u64 (TW.S_wake_sent_us B + TS0.ms_m (TW.S_cfg_wake_timeout_ms B)))
           else TS0.u64 (now + 1000000) in
  if TW.S_state B =? 2 then
    let d := TS0.min64_m d (TS0.u64 (TW.S_last_rx_us B + TS0.ms_m (TW.S_cfg_offline_ms B))) in
    if TW.S_inflight B =? 0 then
      TS0.min64_m d (if TW.S_backoff_until_us B <? TW.S_next_keepalive_us B then TW.S_next_keepalive_us B
                     else TW.S_backoff_until_us B)
    else d
  else d.

Definition dl_dO2 (B : list byte) (dv : Z) : Z :=
  if TW.S_inflight B =? 0 then
    TS0.min64_m dv (if TW.S_backoff_until_us B <? TW.S_next_keepalive_us B then TW.S_next_keepalive_us B
                    else TW.S_backoff_until_us B)
  else dv.

Lemma dl_split : forall B now, TS0.diginet_session_deadline_m B now =
  if (TW.S_state B =? 3) || (TW.S_state B =? 0) then Some (TS0.u64 (now + 1000000))
  else dl_tail B now (dl_dO B now) (TW.S_state B =? 2).
Proof. intros B now. reflexivity. Qed.

(* the first turn of the scan (display_only = 1 at i = 0) when s->queued >= 1 *)
Lemma dd_first : forall B q, 1 <= q ->
  TS0.deadline_display_only_m B 0 1 (Z.to_nat q) =
  TS0.deadline_display_only_m B (0 + 1) (TW.S_queue_display B 0) (Z.to_nat (q - (0 + 1))).
Proof. intros B q Hq. replace (Z.to_nat q) with (S (Z.to_nat (q - (0 + 1)))) by lia. reflexivity. Qed.

(* ============================================================================
   Memory facts
   ============================================================================ *)

(* a load of c bytes at TB_g_s + k, in the form the kit's load step reads *)
Lemma sd_rd : forall (m : word -> option byte) Bw k (c : nat) (A : Z),
  tw_at TMAP_B (csw_view m) Bw -> 0 <= k -> k + Z.of_nat c <= TW.SZ_g_s -> TB_g_s + k = A ->
  ov_read_bytes rsegs m (wa A) c = Some (TW.sub Bw (TW.OFF_g_s + k) c).
Proof.
  intros m Bw k c A HW Hk Hkc <-.
  pose proof (tw_row TMAP_B TW.OFF_g_s TB_g_s TW.SZ_g_s TMAP_B_ok TMAP_B_g_s) as (Ho & Hn & HoW & Hb & Hb64).
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s k c TMAP_B_ok HW TMAP_B_g_s Hk Hkc) as BF.
  assert (LB : Z.of_nat (length Bw) = TW.W_LEN).
  { rewrite (tw_len TMAP_B _ Bw HW). apply Z2Nat.id. unfold TW.W_LEN. lia. }
  assert (L : length (TW.sub Bw (TW.OFF_g_s + k) c) = c) by (apply TWorldLemmas.length_sub; lia).
  replace (wa (TB_g_s + k)) with (wa (TB_g_s + k + 0)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_read rsegs m (TB_g_s + k) _ 0 c BF ltac:(lia)) by (rewrite L; lia).
  cbn [Z.to_nat skipn]. f_equal. apply firstn_all2. rewrite L. lia.
Qed.

(* the frame store keeps the world: the frame is outside the hull of the 18 payloads *)
Lemma sd_kept : forall (m m' : word -> option byte) lo hi Bw,
  tw_at TMAP_B (csw_view m) Bw -> munch [(lo, hi)] m m' ->
  (hi <= TG.G_HARNESS_B_LO \/ TG.G_HARNESS_B_HI <= lo) -> tw_at TMAP_B (csw_view m') Bw.
Proof.
  intros m m' lo hi Bw H MU D. unfold csw_view in *.
  exact (@TMAP_B_kept rsegs m m' lo hi Bw H MU D).
Qed.

(* the frame store keeps `addressable` (a shadow byte of application memory is not in the frame) *)
Lemma sd_addr_tp : forall (m m' : word -> option byte) (sp p n : Z),
  addressable m p n -> munch [(sp - 16, sp)] m m' -> app_mem (sp - 16) -> app_mem (sp - 1) ->
  addressable m' p n.
Proof.
  intros m m' sp p n (HP & HN & HE & AB) MU A1 A2.
  split; [exact HP|]. split; [exact HN|]. split; [exact HE|].
  intros i Hi. destruct (AB i Hi) as (APP & k & MK & SK).
  split; [exact APP|]. exists k. split; [|exact SK].
  unfold shadow_addr, ASAN_K in MK |- *.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP, A1, A2.
  eapply mrd_tp; [exact MU | | | exact MK].
  - destruct APP as [APP|APP]; Z.div_mod_to_equations; lia.
  - destruct APP as [APP|APP]; destruct A1 as [A1|A1]; destruct A2 as [A2|A2]; Z.div_mod_to_equations; lia.
Qed.

(* THE SHADOW BYTES OF g_s's PAYLOAD ARE 0. The payload is a whole number of granules (its base is 8-aligned and its
   length a multiple of 8), so for any offset o the last byte of o's granule is in the payload: its shadow_ok gives
   k = 0 or 7 < k <= 7, that is k = 0. *)
Lemma sd_shadow0 : forall (m : word -> option byte) (P N o A : Z),
  addressable m P N -> P mod 8 = 0 -> N mod 8 = 0 -> 0 <= o < N -> (P + o) / 8 + ASAN_K = A ->
  exists k : byte, mrd rsegs m (wa A) = Some k /\ bv_unsigned k = 0.
Proof.
  intros m P N o A (HP & HN & HE & AB) MP MN Ho <-.
  pose proof (Z.mod_pos_bound o 8 ltac:(lia)) as MB.
  destruct (AB (o - o mod 8 + 7) ltac:(Z.div_mod_to_equations; lia)) as (APP & k & MK & SK).
  unfold shadow_addr in MK. unfold shadow_ok in SK.
  assert (D : (P + (o - o mod 8 + 7)) / 8 = (P + o) / 8) by (Z.div_mod_to_equations; lia).
  assert (E : (P + (o - o mod 8 + 7)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
  rewrite D in MK. rewrite E in SK.
  exists k. split; [exact MK|].
  pose proof (bv_signed_in_range 8 k ltac:(lia)) as RS. unfold bv_half_modulus, bv_modulus in RS.
  change (2 ^ Z.of_N 8 / 2) with 128 in RS.
  assert (S0 : bv_signed k = 0) by (destruct SK as [K0|K]; lia).
  pose proof (byte_range k) as RB.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in S0.
  replace (2 ^ Z.of_N 8) with 256 in S0 by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma sd_byte0_signed : forall k : byte, bv_unsigned k = 0 -> bv_signed k = 0.
Proof.
  intros k H. pose proof (byte_range k) as R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 8) with 256 by reflexivity. rewrite H. reflexivity.
Qed.

Lemma sd_sxb0 : forall k : byte, bv_unsigned k = 0 -> bv_eqb (sxb k) (Z_to_bv 64 0) = true.
Proof.
  intros k H. rewrite sxb_eq0. apply Z.eqb_eq. apply sd_byte0_signed. exact H.
Qed.

Lemma sd_zxb0 : forall k : byte, bv_unsigned k = 0 -> bv_eqb (zxb k) (Z_to_bv 64 0) = true.
Proof. intros k H. unfold zxb. rewrite H. apply bv_eqb_refl. Qed.

(* ============================================================================
   Register arithmetic
   ============================================================================ *)

(* The kit folds closed literal arithmetic after every step (Step.v fold_closed_in_goal), so a register computed
   from literals is a numeral. Only the scan's address &s->queue[i].display = 0x5dfd39 + 32 i has a variable part;
   this is its shift by 3. *)
Lemma sd_shr : forall A D, 0 <= A < 2^64 -> A / 8 = D ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 A)) 3) = Z_to_bv 64 D.
Proof.
  intros A D HA <-. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma sd_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma sd_eqb_sl : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E.
  assert (E2 : (x - y) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in E2; [|lia]. destruct E2 as [c Ec]. nia.
Qed.

Lemma sd_ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma sd_lts_lit : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_lts. rewrite !signed_lit by lia. reflexivity. Qed.

Lemma sd_to_u64 : forall z, Z_to_bv 64 z = Z_to_bv 64 (TS0.u64 z).
Proof.
  intros z. apply bv_eq. rewrite !unsigned_lit_wrap. unfold TS0.u64. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* (uint64_t) v * 1000 + w, the inlined ms (:77) added to a uint64_t field *)
Lemma sd_ms : forall u v, 0 <= u < 2^64 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 u) * 1000 + v) = Z_to_bv 64 (TS0.u64 (v + TS0.ms_m u)).
Proof.
  intros u v Hu. rewrite unsigned_lit by exact Hu. apply bv_eq. rewrite !unsigned_lit_wrap.
  unfold TS0.u64, TS0.ms_m, TS0.u64. rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_r, Z.add_comm. reflexivity.
Qed.

Lemma sd_u64_range : forall z, 0 <= TS0.u64 z < 2^64.
Proof. intros z. unfold TS0.u64. apply Z.mod_pos_bound. lia. Qed.
Lemma sd_min_range : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= TS0.min64_m a b < 2^64.
Proof. intros a b Ha Hb. unfold TS0.min64_m. destruct (a <? b); lia. Qed.
Lemma sd_min_l : forall a b, a < b -> TS0.min64_m a b = a.
Proof. intros a b H. unfold TS0.min64_m. rewrite (proj2 (Z.ltb_lt a b) H). reflexivity. Qed.
Lemma sd_min_r : forall a b, b <= a -> TS0.min64_m a b = b.
Proof. intros a b H. unfold TS0.min64_m. rewrite (proj2 (Z.ltb_ge a b) H). reflexivity. Qed.

Ltac simpb H := cbn [negb orb andb Z.eqb Pos.eqb] in H.

(* An instrumented check of g_s + o (o a literal): its shadow byte k is 0 (the proof's SH), read through rd1. *)
Ltac sd_chk o :=
  let k := fresh "k" in let MK := fresh "MK" in let K := fresh "K" in
  lazymatch goal with
  | SH : forall (o' A : Z), _ -> _ -> exists k' : byte, _ |- _ =>
      destruct (SH o ((6157888 + o) / 8 + 2147450880) ltac:(lia) eq_refl) as (k & MK & K);
      pose proof (rd1 _ _ _ MK); clear MK
  end.

(* The bne after a check's shadow load: the byte is 0, so it falls through to the field load. *)
Ltac sd_fall :=
  match goal with
  | K : bv_unsigned ?k = 0 |- context [bv_eqb (sxb ?k) (Z_to_bv 64 0)] => rewrite (sd_sxb0 k K); clear K
  | K : bv_unsigned ?k = 0 |- context [bv_eqb (zxb ?k) (Z_to_bv 64 0)] => rewrite (sd_zxb0 k K); clear K
  end; cbn [negb]; cbv iota;
  repeat match goal with H : ov_read_bytes _ _ _ 1%nat = Some [_] |- _ => clear H end.

(* The c-byte load of the field at g_s + o (o a literal), from the world (the proof's RD). *)
Ltac sd_ld o c :=
  lazymatch goal with
  | RD : forall (k' : Z) (c' : nat) (A : Z), _ |- _ => pose proof (RD o c (6157888 + o) ltac:(lia) ltac:(lia) eq_refl)
  end.

Ltac sd_clear := repeat match goal with H : ov_read_bytes _ _ _ _ = Some _ |- _ => clear H end.

(* ============================================================================
   The run
   ============================================================================ *)

Theorem diginet_session_deadline_holds_F : diginet_session_deadline_contract_F.
Proof.
  unfold diginet_session_deadline_contract_F, DIGINET_SESSION_DEADLINE, DIGINET_SESSION_DEADLINE_FRAME,
    DIGINET_SESSION_DEADLINE_S, DIGINET_SESSION_DEADLINE_SN.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo now r Bw HA0 HA1 Hnow HW HM ST HLO HOFF AP1 AP2 CELLS OG OC ADS
    RFR RGOT RCELL RPAY RSH.
  subst a0 a1.
  unfold TB_g_s in *. unfold TW.SZ_g_s in *. unfold GOT_CELL_K in RGOT, OG. unfold CELL_K in RCELL, OC.
  unfold off_stk in OG, OC. unfold off_stk, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in HOFF.
  change (shadow_addr (6157888 + 18264 - 1) - shadow_addr 6157888 + 1) with 2283 in RSH.
  change (shadow_addr 6157888) with 2148220616 in RSH.
  rewrite dl_split in HM.
  (* the ranges of the world values the code loads *)
  pose proof (TWorldLemmas.s32_range Bw TW.A_S_state) as Rst.
  change (TW.s32_at Bw TW.A_S_state) with (TW.S_state Bw) in Rst.
  pose proof (TWorldLemmas.s32_range Bw TW.A_S_inflight) as Rinf.
  change (TW.s32_at Bw TW.A_S_inflight) with (TW.S_inflight Bw) in Rinf.
  pose proof (TWorldLemmas.s32_range Bw TW.A_S_display_sent) as Rds.
  change (TW.s32_at Bw TW.A_S_display_sent) with (TW.S_display_sent Bw) in Rds.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_S_queued 4) as Rq.
  change (TW.u_at Bw TW.A_S_queued 4) with (TW.S_queued Bw) in Rq.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_S_wake_sent_us 8) as Rws.
  change (TW.u_at Bw TW.A_S_wake_sent_us 8) with (TW.S_wake_sent_us Bw) in Rws.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_S_last_rx_us 8) as Rlr.
  change (TW.u_at Bw TW.A_S_last_rx_us 8) with (TW.S_last_rx_us Bw) in Rlr.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_S_next_keepalive_us 8) as Rnk.
  change (TW.u_at Bw TW.A_S_next_keepalive_us 8) with (TW.S_next_keepalive_us Bw) in Rnk.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_S_backoff_until_us 8) as Rbk.
  change (TW.u_at Bw TW.A_S_backoff_until_us 8) with (TW.S_backoff_until_us Bw) in Rbk.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_S_inflight_sent_us 8) as Ris.
  change (TW.u_at Bw TW.A_S_inflight_sent_us 8) with (TW.S_inflight_sent_us Bw) in Ris.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_S_last_display_us 8) as Rld.
  change (TW.u_at Bw TW.A_S_last_display_us 8) with (TW.S_last_display_us Bw) in Rld.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_S_cfg_wake_timeout_ms 4) as Rwt.
  change (TW.u_at Bw TW.A_S_cfg_wake_timeout_ms 4) with (TW.S_cfg_wake_timeout_ms Bw) in Rwt.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_S_cfg_offline_ms 4) as Rom.
  change (TW.u_at Bw TW.A_S_cfg_offline_ms 4) with (TW.S_cfg_offline_ms Bw) in Rom.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_S_cfg_ack_timeout_ms 4) as Rat.
  change (TW.u_at Bw TW.A_S_cfg_ack_timeout_ms 4) with (TW.S_cfg_ack_timeout_ms Bw) in Rat.
  pose proof (TWorldLemmas.u_at_range Bw TW.A_S_cfg_display_gap_us 4) as Rgp.
  change (TW.u_at Bw TW.A_S_cfg_display_gap_us 4) with (TW.S_cfg_display_gap_us Bw) in Rgp.
  change (8 * Z.of_nat 8) with 64 in Rws, Rlr, Rnk, Rbk, Ris, Rld.
  change (8 * Z.of_nat 4) with 32 in Rq, Rwt, Rom, Rat, Rgp.
  (* the stack *)
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  lazymatch goal with |- ExecF.evtF _ _ ?Q _ => set (QQ := Q) end.
  carve_frame 16%nat ST.
  (* 0x8a6c0-0x8a6c4: the frame and the store of ra *)
  step. step.
  lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp + -16) _ |- _ => rename mm into mF end.
  lazymatch goal with H : rw_cells _ mF (bv_unsigned sp + -16) ?cs |- _ =>
    set (FRC := cs) in H; rename H into FR end.
  (* the world, the payload's shadow and the two runtime cells, after the only store *)
  assert (HWF : tw_at TMAP_B (csw_view mF) Bw).
  { apply (sd_kept m mF (bv_unsigned sp - 16) (bv_unsigned sp) Bw HW MU).
    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia. }
  pose proof (sd_addr_tp m mF (bv_unsigned sp) 6157888 18264 ADS MU AP1 AP2) as ADSF.
  pose proof CELLS as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  assert (CK0 : bytes_at rsegs mF 706168 (le8 (wa 2147450880)))
    by (eapply bytes_tp; [exact MU | rewrite length_le8; lia | exact CK]).
  assert (GCK0 : bytes_at rsegs mF 670960 (le8 (wa 706168)))
    by (eapply bytes_tp; [exact MU | rewrite length_le8; lia | exact GCK]).
  clear CK GCK CELLS.
  (* every shadow byte of the payload is 0, and lies in the footprint *)
  assert (SH : forall o A, 0 <= o < 18264 -> (6157888 + o) / 8 + 2147450880 = A ->
    exists k : byte, mrd rsegs mF (wa A) = Some k /\ bv_unsigned k = 0).
  { intros o A Ho HA. apply (sd_shadow0 mF 6157888 18264 o A ADSF ltac:(reflexivity) ltac:(reflexivity) Ho).
    unfold ASAN_K. exact HA. }
  assert (RKSH : forall o A, 0 <= o < 18264 -> (6157888 + o) / 8 + 2147450880 = A -> ExecF.rng RNG A 1).
  { intros o A Ho <-. apply (rng_sub' RNG 2148220616 2283); [exact RSH|]. Z.div_mod_to_equations. lia. }
  (* every load of the payload, in the form the load step reads *)
  assert (RD : forall k (c : nat) A, 0 <= k -> k + Z.of_nat c <= 18264 -> 6157888 + k = A ->
    ov_read_bytes rsegs mF (wa A) c = Some (TW.sub Bw (TW.OFF_g_s + k) c)).
  { intros k c A Hk Hkc HA. apply (sd_rd mF Bw k c A HWF Hk ltac:(unfold TW.SZ_g_s; lia)).
    unfold TB_g_s. exact HA. }
  (* ---- the return, 0x8a884 ---- *)
  assert (EPI : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 : word),
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1
                (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 0x8a884) fc None mF (seg_rom rsegs))).
  { intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30.
    unfold FRC in FR.
    step. release_frame FR ST (bv_unsigned sp). step. step.
    apply evtF_done. unfold QQ. do 14 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WMo|]. split; [exact ST | exact HWF]. }
  (* ---- the clamp of :502, 0x8a9a0: bgeu a1,a0 to 0x8a880 (a0 = now), else jal to the return ---- *)
  assert (CLAMP : forall (dv : Z) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 : word),
    0 <= dv < 2^64 -> r = dl_clamp now dv ->
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1
                (Z_to_bv 64 dv) (Z_to_bv 64 now) x12 x13 x14 x15 x16 x17
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 0x8a9a0) fc None mF (seg_rom rsegs))).
  { intros dv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 Rd Hr.
    step. rewrite sd_ltu_lit by lia. destruct (Z.ltb_spec now dv) as [L|L]; cbn [negb]; cbv iota.
    - step. assert (Er : Z_to_bv 64 r = Z_to_bv 64 dv)
        by (rewrite Hr; unfold dl_clamp; rewrite (proj2 (Z.ltb_ge dv now) ltac:(lia)); reflexivity).
      rewrite <- Er. apply EPI.
    - step. assert (Er : Z_to_bv 64 r = Z_to_bv 64 now)
        by (rewrite Hr; unfold dl_clamp;
            destruct (Z.eqb_spec dv now) as [->|N];
            [rewrite (proj2 (Z.ltb_ge now now) ltac:(lia)); reflexivity
            |rewrite (proj2 (Z.ltb_lt dv now) ltac:(lia)); reflexivity]).
      rewrite <- Er. apply EPI. }
  (* ---- :500, 0x8a998: a0 = min64 (d, a4) ---- *)
  assert (JMIN : forall (d t : Z) (x5 x6 x7 x12 x13 x15 x16 x17 x28 x29 x30 : word),
    0 <= d < 2^64 -> 0 <= t < 2^64 -> r = dl_clamp now (TS0.min64_m d t) ->
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1
                (Z_to_bv 64 d) (Z_to_bv 64 now) x12 x13 (Z_to_bv 64 t) x15 x16 x17
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 0x8a998) fc None mF (seg_rom rsegs))).
  { intros d t x5 x6 x7 x12 x13 x15 x16 x17 x28 x29 x30 Rd Rt Hr.
    step. rewrite sd_ltu_lit by lia. destruct (Z.ltb_spec d t) as [L|L]; cbv iota.
    - apply (CLAMP d); [lia|]. rewrite Hr, (sd_min_l d t L). reflexivity.
    - step. apply (CLAMP t); [lia|]. rewrite Hr, (sd_min_r d t L). reflexivity. }
  (* ---- :498-499, 0x8a93c: the display gap; t4 = display_only, a4 = t ---- *)
  assert (JDSP : forall (d t dsp : Z) (x5 x6 x7 x13 x16 x17 x28 x30 : word),
    0 <= d < 2^64 -> 0 <= t < 2^64 -> 0 <= dsp < 2^64 ->
    r = dl_clamp now (TS0.min64_m d (dl_tdisp Bw dsp t)) ->
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1
                (Z_to_bv 64 d) (Z_to_bv 64 now) (Z_to_bv 64 6157888) x13
                (Z_to_bv 64 t) (Z_to_bv 64 2147450880) x16 x17
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 (Z_to_bv 64 dsp) x30 t6)
          F (Z_to_bv 64 0x8a93c) fc None mF (seg_rom rsegs))).
  { intros d t dsp x5 x6 x7 x13 x16 x17 x28 x30 Rd Rt Rdsp Hr.
    (* 0x8a93c: beq t4, zero *)
    step. rewrite sd_eqb_lit by lia. destruct (Z.eqb_spec dsp 0) as [E|E]; cbv iota.
    - apply (JMIN d t); [lia|lia|]. rewrite Hr. unfold dl_tdisp. rewrite E. reflexivity.
    - (* 0x8a940-0x8a950: the check of s->display_sent *)
      sd_chk 208. step. step. step. step. step. sd_fall.
      (* 0x8a954: a3 = s->display_sent *)
      sd_ld 208 4%nat. step. rewrite lw_world.
      change (TW.s32_at Bw (TW.OFF_g_s + 208)) with (TW.S_display_sent Bw). sd_clear.
      (* 0x8a958: beq a3, zero *)
      step. rewrite sd_eqb_sl by lia. destruct (Z.eqb_spec (TW.S_display_sent Bw) 0) as [E2|E2]; cbv iota.
      + apply (JMIN d t); [lia|lia|]. rewrite Hr. unfold dl_tdisp. rewrite E2.
        rewrite (proj2 (Z.eqb_neq dsp 0) E). reflexivity.
      + (* 0x8a95c-0x8a96c: the check of s->last_display_us (8 bytes) *)
        sd_chk 200. step. step. step. step. step. sd_fall.
        (* 0x8a970-0x8a984: the check of s->cfg.display_gap_us; a3 = s->last_display_us *)
        sd_chk 48. sd_ld 200 8%nat.
        step. step. step. step.
        step. rewrite ld_world. change (TW.u_at Bw (TW.OFF_g_s + 200) 8) with (TW.S_last_display_us Bw).
        step. sd_fall.
        (* 0x8a988-0x8a98c: a2 = cfg.display_gap_us; a3 = last_display_us + gap *)
        sd_ld 48 4%nat. step. rewrite lwu_world.
        change (TW.u_at Bw (TW.OFF_g_s + 48) 4) with (TW.S_cfg_display_gap_us Bw). sd_clear.
        step. rewrite (sd_to_u64 (TW.S_last_display_us Bw + TW.S_cfg_display_gap_us Bw)).
        (* 0x8a990-0x8a994: a4 = max (g, t) *)
        step. rewrite sd_ltu_lit by (first [apply sd_u64_range | lia]).
        destruct (Z.ltb_spec (TS0.u64 (TW.S_last_display_us Bw + TW.S_cfg_display_gap_us Bw)) t) as [L|L];
          cbv iota.
        * apply (JMIN d t); [lia|lia|]. rewrite Hr. unfold dl_tdisp.
          rewrite (proj2 (Z.eqb_neq dsp 0) E), (proj2 (Z.eqb_neq _ _) E2). cbn [negb andb].
          rewrite (proj2 (Z.ltb_lt _ _) L). reflexivity.
        * step.
          apply (JMIN d (TS0.u64 (TW.S_last_display_us Bw + TW.S_cfg_display_gap_us Bw)));
            [lia | apply sd_u64_range |].
          rewrite Hr. unfold dl_tdisp.
          rewrite (proj2 (Z.eqb_neq dsp 0) E), (proj2 (Z.eqb_neq _ _) E2). cbn [negb andb].
          rewrite (proj2 (Z.ltb_ge _ _) L). reflexivity. }
  (* ---- :495-497, the scan at 0x8a8f4: a3 = t0 = &s->queue[i].display = 0x5dfd39 + 32 i, t1 = i + 1, a7 = 32 i,
     t2 = ~(s + 1760), t3 = 513, a4 = t ---- *)
  assert (LOOP : forall (k : nat) (d t i : Z) (x29 x30 : word),
    0 <= d < 2^64 -> 0 <= t < 2^64 -> Z.of_nat k = TW.S_queued Bw - (i + 1) -> 0 <= i < 512 ->
    match TS0.deadline_display_only_m Bw (i + 1) (TW.S_queue_display Bw i) k with
    | Some dsp => r = dl_clamp now (TS0.min64_m d (dl_tdisp Bw dsp t))
    | None => False
    end ->
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp
                (Z_to_bv 64 (6159673 + 32 * i)) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 18446744073703391967) s0 s1
                (Z_to_bv 64 d) (Z_to_bv 64 now) (Z_to_bv 64 6157888)
                (Z_to_bv 64 (6159673 + 32 * i)) (Z_to_bv 64 t) (Z_to_bv 64 2147450880)
                (Z_to_bv 64 (TW.S_queued Bw)) (Z_to_bv 64 (32 * i))
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 513) x29 x30 t6)
          F (Z_to_bv 64 0x8a8f4) fc None mF (seg_rom rsegs))).
  { induction k as [|k IH]; intros d t i x29 x30 Rd Rt Hk Hi LM.
    all: pose proof (TWorldLemmas.u_at_range Bw (TW.A_S_queue_display i) 1) as Rdi;
         change (TW.u_at Bw (TW.A_S_queue_display i) 1) with (TW.S_queue_display Bw i) in Rdi;
         change (8 * Z.of_nat 1) with 8 in Rdi.
    all: assert (EA : 6157888 + (1785 + 32 * i) = 6159673 + 32 * i) by lia.
    all: destruct (SH (1785 + 32 * i) ((6159673 + 32 * i) / 8 + 2147450880) ltac:(lia)
                      ltac:(rewrite EA; reflexivity)) as (kd & MKd & Kd).
    all: pose proof (RKSH (1785 + 32 * i) ((6159673 + 32 * i) / 8 + 2147450880) ltac:(lia)
                          ltac:(rewrite EA; reflexivity)) as RKd.
    all: pose proof (RD (1785 + 32 * i) 1%nat (6159673 + 32 * i) ltac:(lia) ltac:(lia) ltac:(lia)) as RDd.
    all: replace (TW.OFF_g_s + (1785 + 32 * i)) with (TW.A_S_queue_display i) in RDd
           by (unfold TW.A_S_queue_display; lia).
    all: pose proof (rd1 mF _ _ MKd) as RD1; clear MKd.
    (* 0x8a8f4: beq t1, t3, the UBSan bounds test of queue[i] (i = 512): not taken, i < 512 *)
    all: step; rewrite sd_eqb_lit by lia;
         rewrite (proj2 (Z.eqb_neq (i + 1) 513) ltac:(lia)); cbv iota.
    (* 0x8a8f8: bltu t2, a7, the UBSan pointer-overflow test: not taken, 32 i < ~(s + 1760) *)
    all: step; rewrite sd_ltu_lit by lia;
         rewrite (proj2 (Z.ltb_ge 18446744073703391967 (32 * i)) ltac:(lia)); cbv iota.
    (* 0x8a8fc-0x8a908: the check of &s->queue[i].display *)
    all: step; rewrite (sd_shr (6159673 + 32 * i) ((6159673 + 32 * i) / 8) ltac:(lia) eq_refl).
    all: step.
    all: step.
    all: step; rewrite (sd_sxb0 kd Kd); cbn [negb]; cbv iota; clear RD1 RKd.
    (* 0x8a90c: t4 = s->queue[i].display *)
    all: step; rewrite lbu_world;
         change (TW.u_at Bw (TW.A_S_queue_display i) 1) with (TW.S_queue_display Bw i); clear RDd.
    (* 0x8a910: bgeu t1, a6 *)
    all: step; rewrite sd_ltu_lit by lia.
    - (* k = 0: i + 1 = queued, the scan ends with display_only = queue[i].display *)
      cbn [TS0.deadline_display_only_m] in LM.
      replace (i + 1 <? TW.S_queued Bw) with false by (symmetry; apply Z.ltb_ge; lia).
      cbn [negb]. cbv iota.
      apply (JDSP d t (TW.S_queue_display Bw i)); [lia | lia | lia | exact LM].
    - replace (i + 1 <? TW.S_queued Bw) with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [negb]. cbv iota.
      (* 0x8a914-0x8a920: a3, t0 += 32; t1 += 1; a7 += 32 *)
      step. step. step. step.
      (* 0x8a924: bne t4, zero *)
      step. rewrite sd_eqb_lit by lia.
      cbn [TS0.deadline_display_only_m] in LM.
      destruct (Z.eqb_spec (TW.S_queue_display Bw i) 0) as [E|E]; cbn [negb]; cbv iota.
      + (* display = 0: 0x8a928 jumps to 0x8a93c with display_only = 0 *)
        rewrite E in LM. simpb LM.
        step. rewrite E. apply (JDSP d t 0); [lia | lia | lia | exact LM].
      + (* display <> 0 (the destruct already put false for its test in LM): the next turn *)
        simpb LM.
        unfold TW.S_queue_N in LM.
        destruct (Z.leb_spec 512 (i + 1)) as [Hb|Hb]; simpb LM; [contradiction|].
        replace (6159673 + 32 * i + 32) with (6159673 + 32 * (i + 1)) by lia.
        replace (32 * i + 32) with (32 * (i + 1)) by lia.
        replace (i + 2) with (i + 1 + 1) by lia.
        apply (IH d t (i + 1)); [lia | lia | lia | lia | exact LM]. }
  (* ---- 0x8a890: inflight = 0; a6 is the online flag ---- *)
  assert (JQ : forall (d : Z) (online : bool) (x5 x6 x7 x13 x14 x17 x28 x29 x30 : word),
    0 <= d < 2^64 ->
    match (if online && negb (TW.S_queued Bw =? 0) then
             match TS0.deadline_display_only_m Bw 0 1 (Z.to_nat (TW.S_queued Bw)) with
             | None => None
             | Some dsp => Some (TS0.min64_m d (dl_t Bw now dsp))
             end
           else Some d) with
    | None => None
    | Some d0 => Some (dl_clamp now d0)
    end = Some r ->
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1
                (Z_to_bv 64 d) (Z_to_bv 64 now) (Z_to_bv 64 6157888) x13 x14 (Z_to_bv 64 2147450880)
                (Z_to_bv 64 (TC.b2z online)) x17
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 0x8a890) fc None mF (seg_rom rsegs))).
  { intros d online x5 x6 x7 x13 x14 x17 x28 x29 x30 Rd HR.
    (* 0x8a890: beq a6, zero *)
    step. destruct online; cbn [TC.b2z andb] in HR |- *.
    - change (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0)) with false. cbv iota.
      (* 0x8a894-0x8a8ac: a3 = &s->queued (lui, addiw, add), and its check *)
      sd_chk 18144. step. step. step. step. step. step. step. sd_fall.
      (* 0x8a8b0: a6 = s->queued *)
      sd_ld 18144 4%nat. step. rewrite lwu_world.
      change (TW.u_at Bw (TW.OFF_g_s + 18144) 4) with (TW.S_queued Bw). sd_clear.
      (* 0x8a8b4: beq a6, zero *)
      step. rewrite sd_eqb_lit by lia.
      destruct (Z.eqb_spec (TW.S_queued Bw) 0) as [Q0|Q0]; cbv iota.
      + rewrite Q0 in HR. simpb HR. injection HR as HR.
        apply (CLAMP d); [lia | symmetry; exact HR].
      + simpb HR.
        (* 0x8a8b8-0x8a8c8: the check of s->backoff_until_us *)
        sd_chk 192. step. step. step. step. step. sd_fall.
        (* 0x8a8cc: a4 = backoff_until_us *)
        sd_ld 192 8%nat. step. rewrite ld_world.
        change (TW.u_at Bw (TW.OFF_g_s + 192) 8) with (TW.S_backoff_until_us Bw). sd_clear.
        rewrite (dd_first Bw (TW.S_queued Bw) ltac:(lia)) in HR.
        (* 0x8a8d0-0x8a8d4: a4 = t = max (now, backoff_until_us) (:494) *)
        step. rewrite sd_ltu_lit by lia.
        destruct (Z.ltb_spec now (TW.S_backoff_until_us Bw)) as [L|L]; cbv iota; [|step].
        * (* 0x8a8d8-0x8a8f0: the scan's setup, then the scan from i = 0 *)
          step. step. step. step. step. step. step.
          apply (LOOP (Z.to_nat (TW.S_queued Bw - (0 + 1))) d (TW.S_backoff_until_us Bw) 0);
            [lia | lia | lia | lia |].
          destruct (TS0.deadline_display_only_m Bw (0 + 1) (TW.S_queue_display Bw 0)
                     (Z.to_nat (TW.S_queued Bw - (0 + 1)))) as [dsp|]; cbv iota in HR |- *;
            [injection HR as HR | discriminate HR].
          rewrite <- HR. unfold dl_t. rewrite (proj2 (Z.ltb_lt _ _) L). reflexivity.
        * step. step. step. step. step. step. step.
          apply (LOOP (Z.to_nat (TW.S_queued Bw - (0 + 1))) d now 0); [lia | lia | lia | lia |].
          destruct (TS0.deadline_display_only_m Bw (0 + 1) (TW.S_queue_display Bw 0)
                     (Z.to_nat (TW.S_queued Bw - (0 + 1)))) as [dsp|]; cbv iota in HR |- *;
            [injection HR as HR | discriminate HR].
          rewrite <- HR. unfold dl_t. rewrite (proj2 (Z.ltb_ge _ _) L). reflexivity.
    - change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
      simpb HR. injection HR as HR. apply (CLAMP d); [lia | symmetry; exact HR]. }
  (* ---- the join of :491, 0x8a824 ---- *)
  assert (JOIN : forall (d : Z) (online : bool) (x5 x6 x7 x13 x14 x17 x28 x29 x30 : word),
    0 <= d < 2^64 -> dl_tail Bw now d online = Some r ->
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1
                (Z_to_bv 64 d) (Z_to_bv 64 now) (Z_to_bv 64 6157888) x13 x14 (Z_to_bv 64 2147450880)
                (Z_to_bv 64 (TC.b2z online)) x17
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 0x8a824) fc None mF (seg_rom rsegs))).
  { intros d online x5 x6 x7 x13 x14 x17 x28 x29 x30 Rd HT.
    unfold dl_tail in HT.
    (* 0x8a824-0x8a834: the check of s->inflight *)
    sd_chk 212. step. step. step. step. step. sd_fall.
    (* 0x8a838: a3 = s->inflight *)
    sd_ld 212 4%nat. step. rewrite lw_world.
    change (TW.s32_at Bw (TW.OFF_g_s + 212)) with (TW.S_inflight Bw). sd_clear.
    (* 0x8a83c: beq a3, zero *)
    step. rewrite sd_eqb_sl by lia.
    destruct (Z.eqb_spec (TW.S_inflight Bw) 0) as [I0|I0]; cbv iota.
    - simpb HT.
      apply (JQ d online); [lia | exact HT].
    - simpb HT. injection HT as HT.
      (* 0x8a840-0x8a850: the check of s->inflight_sent_us *)
      sd_chk 1752. step. step. step. step. step. sd_fall.
      (* 0x8a854-0x8a868: the check of s->cfg.ack_timeout_ms; a1 = s->inflight_sent_us *)
      sd_chk 28. sd_ld 1752 8%nat.
      step. step. step. step.
      step. rewrite ld_world.
      change (TW.u_at Bw (TW.OFF_g_s + 1752) 8) with (TW.S_inflight_sent_us Bw).
      step. sd_fall.
      (* 0x8a86c-0x8a878: a1 = inflight_sent_us + ms (cfg.ack_timeout_ms) *)
      sd_ld 28 4%nat. step. rewrite lwu_world.
      change (TW.u_at Bw (TW.OFF_g_s + 28) 4) with (TW.S_cfg_ack_timeout_ms Bw). sd_clear.
      step. step. step. rewrite sd_ms by lia.
      (* 0x8a87c-0x8a880: a0 = min64 (d, that), then the return WITHOUT the clamp *)
      step. rewrite sd_ltu_lit by (first [apply sd_u64_range | lia]).
      destruct (Z.ltb_spec d (TS0.u64 (TW.S_inflight_sent_us Bw
                 + TS0.ms_m (TW.S_cfg_ack_timeout_ms Bw)))) as [L|L]; cbv iota.
      + rewrite (sd_min_l _ _ L) in HT. rewrite HT. apply EPI.
      + step. rewrite (sd_min_r _ _ L) in HT. rewrite HT. apply EPI. }
  (* ---- the online arm's tail, 0x8a7c4: a0 = dv, the check and load of s->inflight ---- *)
  assert (J212 : forall (dv : Z) (x5 x6 x7 x13 x14 x16 x17 x28 x29 x30 : word),
    0 <= dv < 2^64 -> dl_tail Bw now (dl_dO2 Bw dv) true = Some r ->
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1
                (Z_to_bv 64 dv) (Z_to_bv 64 now) (Z_to_bv 64 6157888) x13 x14 (Z_to_bv 64 2147450880)
                x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 0x8a7c4) fc None mF (seg_rom rsegs))).
  { intros dv x5 x6 x7 x13 x14 x16 x17 x28 x29 x30 Rdv HT.
    (* the min of :488-489, reached at 0x8a81c with a3 = mx, the max of the two deadlines *)
    assert (JMX : forall (mx : Z) (y5 y6 y7 y14 y17 : word), 0 <= mx < 2^64 ->
      TW.S_inflight Bw = 0 ->
      mx = (if TW.S_backoff_until_us Bw <? TW.S_next_keepalive_us Bw then TW.S_next_keepalive_us Bw
            else TW.S_backoff_until_us Bw) ->
      ExecF.evtF rsegs RNG QQ
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp y5 y6 y7 s0 s1
                  (Z_to_bv 64 dv) (Z_to_bv 64 now) (Z_to_bv 64 6157888) (Z_to_bv 64 mx) y14
                  (Z_to_bv 64 2147450880) (Z_to_bv 64 1) y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
            F (Z_to_bv 64 0x8a81c) fc None mF (seg_rom rsegs))).
    { intros mx y5 y6 y7 y14 y17 Rmx I0 Emx.
      unfold dl_dO2 in HT. rewrite I0 in HT. simpb HT. rewrite <- Emx in HT.
      step. rewrite sd_ltu_lit by lia. destruct (Z.ltb_spec dv mx) as [L|L]; cbv iota.
      - rewrite <- (sd_min_l dv mx L).
        apply (JOIN (TS0.min64_m dv mx) true); [apply sd_min_range; lia | exact HT].
      - step. rewrite <- (sd_min_r dv mx L).
        apply (JOIN (TS0.min64_m dv mx) true); [apply sd_min_range; lia | exact HT]. }
    (* 0x8a7c4-0x8a7d4: the check of s->inflight *)
    sd_chk 212. step. step. step. step. step. sd_fall.
    (* 0x8a7d8-0x8a7e0: a3 = s->inflight; a6 = 1; bne a3, zero *)
    sd_ld 212 4%nat. step. rewrite lw_world.
    change (TW.s32_at Bw (TW.OFF_g_s + 212)) with (TW.S_inflight Bw). sd_clear.
    step. step. rewrite sd_eqb_sl by lia.
    destruct (Z.eqb_spec (TW.S_inflight Bw) 0) as [I0|I0]; cbn [negb]; cbv iota.
    - (* inflight = 0: 0x8a7e4-0x8a818, the two checks, the two 8-byte loads and their max *)
      sd_chk 184. step. step. step. step. step. sd_fall.
      sd_chk 192. step. step. step. step. step. sd_fall.
      sd_ld 184 8%nat. sd_ld 192 8%nat.
      step. rewrite ld_world.
      change (TW.u_at Bw (TW.OFF_g_s + 184) 8) with (TW.S_next_keepalive_us Bw).
      step. rewrite ld_world.
      change (TW.u_at Bw (TW.OFF_g_s + 192) 8) with (TW.S_backoff_until_us Bw). sd_clear.
      step. rewrite sd_ltu_lit by lia.
      destruct (Z.ltb_spec (TW.S_backoff_until_us Bw) (TW.S_next_keepalive_us Bw)) as [L2|L2]; cbv iota.
      + apply (JMX (TW.S_next_keepalive_us Bw)); [lia | exact I0 | reflexivity].
      + step. apply (JMX (TW.S_backoff_until_us Bw)); [lia | exact I0 | reflexivity].
    - (* inflight <> 0: straight to the join, online *)
      apply (JOIN dv true); [exact Rdv|].
      unfold dl_dO2 in HT. rewrite (proj2 (Z.eqb_neq _ _) I0) in HT. exact HT. }
  (* ---- the waking arm's join, 0x8a764: a6 = 0, then the join at 0x8a824 ---- *)
  assert (JWK : forall (dv : Z) (x5 x6 x7 x13 x14 x16 x17 x28 x29 x30 : word),
    0 <= dv < 2^64 -> dl_tail Bw now dv false = Some r ->
    ExecF.evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 s0 s1
                (Z_to_bv 64 dv) (Z_to_bv 64 now) (Z_to_bv 64 6157888) x13 x14 (Z_to_bv 64 2147450880)
                x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 0x8a764) fc None mF (seg_rom rsegs))).
  { intros dv x5 x6 x7 x13 x14 x16 x17 x28 x29 x30 Rdv HT.
    step. step. apply (JOIN dv false); [exact Rdv | exact HT]. }
  (* ---- the head: 0x8a6c8-0x8a71c, the state dispatch ---- *)
  (* 0x8a6c8-0x8a6d4: a2 = s; a0 = now + 1000000 *)
  step. step. step. step.
  rewrite (sd_to_u64 (now + 1000000)).
  (* 0x8a6d8: beq a2,zero: not taken *)
  step. rewrite sd_eqb_lit by lia. cbn [Z.eqb]. cbv iota.
  (* 0x8a6dc-0x8a6e0: the UBSan alignment check of s: s & 7 = 0, not taken *)
  step. step. rewrite sd_eqb_lit by lia. cbn [Z.eqb negb]. cbv iota.
  (* 0x8a6e4-0x8a6ec: a3 = [GOT_CELL_K] = CELL_K; a5 = [CELL_K] = 0x7fff8000, the shadow base *)
  assert (RDG : ov_read_bytes rsegs mF (wa 670960) 8 = Some (le8 (wa 706168))).
  { replace (wa 670960) with (wa (670960 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs mF 670960 _ 0 8 GCK0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDC : ov_read_bytes rsegs mF (wa 706168) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 706168) with (wa (706168 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs mF 706168 _ 0 8 CK0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  step. step. step. sd_clear.
  (* 0x8a6f0-0x8a700: the check of s->state *)
  sd_chk 112. step. step. step. step. step. sd_fall.
  (* 0x8a704: a3 = s->state *)
  sd_ld 112 4%nat. step. rewrite lw_world.
  change (TW.s32_at Bw (TW.OFF_g_s + 112)) with (TW.S_state Bw). sd_clear.
  (* 0x8a708-0x8a710: a4 = 1; a6 = 0; blt a4, a3 *)
  step. step. step. rewrite sd_lts_lit by lia.
  destruct (Z.ltb_spec 1 (TW.S_state Bw)) as [Hgt|Hle]; cbv iota.
  - (* state >= 2: 0x8a76c-0x8a770 *)
    step. step. rewrite sd_eqb_sl by lia.
    destruct (Z.eqb_spec (TW.S_state Bw) 2) as [S2|S2]; cbv iota.
    + (* ---- state 2: the online arm ---- *)
      assert (HD2 : dl_tail Bw now (dl_dO2 Bw (TS0.min64_m (TS0.u64 (now + 1000000))
                      (TS0.u64 (TW.S_last_rx_us Bw + TS0.ms_m (TW.S_cfg_offline_ms Bw))))) true = Some r).
      { rewrite <- HM. unfold dl_dO, dl_dO2. rewrite S2. reflexivity. }
      (* 0x8a780-0x8a790: the check of s->last_rx_us *)
      sd_chk 176. step. step. step. step. step. sd_fall.
      (* 0x8a794-0x8a7a8: the check of s->cfg.offline_ms; a4 = s->last_rx_us *)
      sd_chk 40. sd_ld 176 8%nat.
      step. step. step. step.
      step. rewrite ld_world. change (TW.u_at Bw (TW.OFF_g_s + 176) 8) with (TW.S_last_rx_us Bw).
      step. sd_fall.
      (* 0x8a7ac-0x8a7c0: d = min64 (d, last_rx_us + ms (offline_ms)) *)
      sd_ld 40 4%nat. step. rewrite lwu_world.
      change (TW.u_at Bw (TW.OFF_g_s + 40) 4) with (TW.S_cfg_offline_ms Bw). sd_clear.
      step. step. step. rewrite sd_ms by lia.
      step. rewrite sd_ltu_lit by (first [apply sd_u64_range | lia]).
      destruct (Z.ltb_spec (TS0.u64 (now + 1000000))
                 (TS0.u64 (TW.S_last_rx_us Bw + TS0.ms_m (TW.S_cfg_offline_ms Bw)))) as [L1|L1]; cbv iota.
      * rewrite <- (sd_min_l _ _ L1). apply J212; [apply sd_min_range; apply sd_u64_range | exact HD2].
      * step. rewrite <- (sd_min_r _ _ L1).
        apply J212; [apply sd_min_range; apply sd_u64_range | exact HD2].
    + (* state <> 2: 0x8a774-0x8a778 *)
      step. step. rewrite sd_eqb_sl by lia.
      destruct (Z.eqb_spec (TW.S_state Bw) 3) as [S3|S3]; cbn [negb]; cbv iota.
      * (* state 3: 0x8a77c jumps to the return with a0 = d *)
        step. rewrite S3 in HM. simpb HM. injection HM as HM. rewrite HM. apply EPI.
      * (* state > 3: the join, not online *)
        apply (JOIN (TS0.u64 (now + 1000000)) false); [apply sd_u64_range|].
        rewrite <- HM. unfold dl_dO.
        rewrite ?(proj2 (Z.eqb_neq _ _) S2), ?(proj2 (Z.eqb_neq _ _) S3),
                ?(proj2 (Z.eqb_neq (TW.S_state Bw) 0) ltac:(lia)),
                ?(proj2 (Z.eqb_neq (TW.S_state Bw) 1) ltac:(lia)).
        reflexivity.
  - (* state <= 1: 0x8a714 *)
    step. rewrite sd_eqb_sl by lia.
    destruct (Z.eqb_spec (TW.S_state Bw) 0) as [S0z|S0z]; cbv iota.
    + (* state 0: the return with a0 = d *)
      rewrite S0z in HM. simpb HM. injection HM as HM. rewrite HM. apply EPI.
    + (* 0x8a718-0x8a71c: state == 1? *)
      step. step. rewrite sd_eqb_sl by lia.
      destruct (Z.eqb_spec (TW.S_state Bw) 1) as [S1|S1]; cbn [negb]; cbv iota.
      * (* ---- state 1: the waking arm ---- *)
        assert (HD1 : dl_tail Bw now (TS0.min64_m (TS0.u64 (now + 1000000))
                        (TS0.u64 (TW.S_wake_sent_us Bw + TS0.ms_m (TW.S_cfg_wake_timeout_ms Bw)))) false
                      = Some r).
        { rewrite <- HM. unfold dl_dO. rewrite S1. reflexivity. }
        (* 0x8a720-0x8a730: the check of s->wake_sent_us *)
        sd_chk 152. step. step. step. step. step. sd_fall.
        (* 0x8a734-0x8a748: the check of s->cfg.wake_timeout_ms; a4 = s->wake_sent_us *)
        sd_chk 44. sd_ld 152 8%nat.
        step. step. step. step.
        step. rewrite ld_world. change (TW.u_at Bw (TW.OFF_g_s + 152) 8) with (TW.S_wake_sent_us Bw).
        step. sd_fall.
        (* 0x8a74c-0x8a760: d = min64 (d, wake_sent_us + ms (wake_timeout_ms)) *)
        sd_ld 44 4%nat. step. rewrite lwu_world.
        change (TW.u_at Bw (TW.OFF_g_s + 44) 4) with (TW.S_cfg_wake_timeout_ms Bw). sd_clear.
        step. step. step. rewrite sd_ms by lia.
        step. rewrite sd_ltu_lit by (first [apply sd_u64_range | lia]).
        destruct (Z.ltb_spec (TS0.u64 (now + 1000000))
                   (TS0.u64 (TW.S_wake_sent_us Bw + TS0.ms_m (TW.S_cfg_wake_timeout_ms Bw)))) as [L|L];
          cbv iota.
        -- rewrite <- (sd_min_l _ _ L).
           apply JWK; [apply sd_min_range; apply sd_u64_range | exact HD1].
        -- step. rewrite <- (sd_min_r _ _ L).
           apply JWK; [apply sd_min_range; apply sd_u64_range | exact HD1].
      * (* state < 0: the join, not online *)
        apply (JOIN (TS0.u64 (now + 1000000)) false); [apply sd_u64_range|].
        rewrite <- HM. unfold dl_dO.
        rewrite ?(proj2 (Z.eqb_neq (TW.S_state Bw) 3) ltac:(lia)),
                ?(proj2 (Z.eqb_neq _ _) S0z), ?(proj2 (Z.eqb_neq _ _) S1),
                ?(proj2 (Z.eqb_neq (TW.S_state Bw) 2) ltac:(lia)).
        reflexivity.
Qed.

Print Assumptions diginet_session_deadline_holds_F.
