(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 715 of its 809 lines of code are new or changed and 936 lines of the source are left out. *)
(* diginet_session_wake_seg_mid: Lemma wake_mid : wake_mid_stmt (lib/A/Prog/diginet_session_wake_seg_cut.v), the mid
   piece of the image-A ASan walk of diginet_session_wake (fuzz_transport.asan 0x866fc = transport_sigma
   TS_diginet_session_wake, AF_diginet_session_wake = 0x5498 of lib/A/Prog/DgnTransportList.v), from the mid cut
   WAKE_MID (+0x264, 0x86960) to the notice cut WAKE_NTC (+0x350) and the e2 cut WAKE_E2 (+0x410). The walk holds the
   caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 []) with the class-2 frame owned; the runs are
   lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x.
     run 1   +0x264 .. +0x270  `ld s7, 16(s1)`: e2_len, the out cell send_control filled (the region at sp1 + 16 holds
                               60: wake_mid_cur's garr8 of put 8 60, wm_klp_val); a0 = s + 216, a1 = s6 = e2, a2 = 60;
     +0x274                    `jal __asan_memcpy`: lib/A/Prog/TransportGCg.v gx_intrin_at at OCpy. The destination
                               [s + 216, s + 276) is bytes of g_s (G: writable by TransportGRwA.v G_HARNESS_rw, its
                               shadow 0 by trans_wake_cells through DgnTransportCg.v decode_zshadow_ra); the source
                               [e2, e2 + 60) is the own frame's (wake_mid_cur's decode_rd_ok, kept by run 1); the two are
                               apart (a frame byte is not an image byte: frm_img). Run 1's six regions are kept across
                               the call (YC1h.v jafter_call_keep_hi): the call changes [s + 216, s + 276) and the ESTACK
                               bytes below sp1 only;
     run 2   +0x278 .. +0x340  the seven checked accesses of g_s, each check reading a zero shadow byte of g_s's payload
                               (the shadow entries WM_SH, wm_shok): the 8-byte store of 60 at s + 1736, the 8-byte load
                               / + 1 / store at s + 18224 (s5), the 4-byte load of s + 160, the stores of 1 at s + 212,
                               of the loaded counter at s + 1744, of 0 at s + 1748 and of now at s + 1752; s5 = s + 112,
                               s6 = its shadow address, the checked load s7 = S_state, s11 = 1, up to `bne s7, s11`;
     +0x344                    `bne s7, s11`, taken up from a state with no region (wm_entry2, paj_branch): s7 is
                               S_state Bw (the load reads atom 35 = B1's 4 bytes at s + 112, and send_control keeps
                               S_state: wake_mid_cur); taken (S_state Bw <> S_WAKING) the pc is +0x350 and the piece
                               concludes by wake_ntc_at; not taken, `li a0, 0` and `j` reach +0x410 and it concludes by
                               wake_e2_at.
   The memory facts are proved once at the end of run 2 (memory m5) and moved to each cut's memory, whose view is the same
   (CURF): what the call keeps (acall_kept_g over wake_wr Bw: TransportGFrame.v dk_kept_step_gw, every byte the piece
   may change is an ESTACK byte below sp1 or a byte of wm_wr, which lies in wake_wr Bw and in G: wm_wr_in), the 13 saved
   words and the flag-pointer word (outside both), the world relation at wake_w3 B1 e2 now (wm_writes: TWorldG.v tw_upd
   for the memcpy's 60 bytes and the six stores, in the model's order; the values from run 2's regions, wm_field). The
   model: wake_model on the path of wake_mid_cur, rs >= 0, then set_state_m's two cases
   (diginet_session_wake_seg_keep.v wk_set_state_same, wk_set_state_go, wk_notice_keep, wk_w3_keep). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
diginet_session_wake_cg diginet_session_wake_seg_cut diginet_session_wake_seg_keep.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

Definition WM_B0 : Z * Z := (0, 0).
(* The entry state at +0x264. Atoms 0 .. 31: the registers at the cut; 32: the shadow base; 33: B1's 8 bytes at
   s + 18224 (stats.tx_wakes); 34: B1's 4 bytes at s + 160 (host_counter); 35: B1's 4 bytes at s + 112 (state).
   Regions: e2_len at sp1 + 16 (60, read only), state and host_counter (read only), and the bytes run 2 stores:
   [s + 212, s + 216), [s + 1736, s + 1760) and stats.tx_wakes (based at s5 = s + 18224). *)
Definition wm_rg_klp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 16 24 0 0 [YP09.mkChunk 16 (YP09.CVal 8 (SLit 60))].
Definition wm_rg_st : YP09.region :=
  YP09.mkRegion (Some 19%nat) 112 116 0 0 [YP09.mkChunk 112 (YP09.CVal 4 (SOff 35 0))].
Definition wm_rg_hc : YP09.region :=
  YP09.mkRegion (Some 19%nat) 160 164 0 0 [YP09.mkChunk 160 (YP09.CVal 4 (SOff 34 0))].
Definition wm_rg_inf : YP09.region := YP09.mkRegion (Some 19%nat) 212 216 212 216 [].
Definition wm_rg_il : YP09.region := YP09.mkRegion (Some 19%nat) 1736 1760 1736 1760 [].
Definition wm_rg_tx : YP09.region :=
  YP09.mkRegion (Some 21%nat) 0 8 0 8 [YP09.mkChunk 0 (YP09.CVal 8 (SOff 33 0))].
Definition wm_regions : smem := [wm_rg_klp; wm_rg_st; wm_rg_hc; wm_rg_inf; wm_rg_il; wm_rg_tx].
Definition wm_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF WAKE_S WAKE_S 6);
           (21%nat, mkAF (WAKE_S + 18224) (WAKE_S + 18224) 4); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 64 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_wm0 : sstate := mkSS WAKE_MID sr_atoms wm_regions None wm_facts.
(* The shadow entries of run 2's checks ([s + 112, s + 1760) and s5's 8 bytes), and the shadow base s10. *)
Definition WM_SH : list shent := [mkSHE 19 112 1760; mkSHE 21 0 8].
Definition WM_Bx : sv := SOff 26 0.
(* `bne s7, s11` at +0x344, taken up from a state with no region. *)
Definition WM_C2 : Z := AF_diginet_session_wake + 0x344.
Definition ss_wm2 : sstate := mkSS WM_C2 sr_atoms [] None (mkFacts [] [] []).

(* The bytes the runs may store (the windows of the writable regions), and every byte of g_s the piece may change. *)
Definition wm_win (a : Z) : Prop :=
  (WAKE_S + 212 <= a < WAKE_S + 216) \/ (WAKE_S + 1736 <= a < WAKE_S + 1760) \/
  (WAKE_S + 18224 <= a < WAKE_S + 18232).
Definition wm_wr (a : Z) : Prop := (WAKE_S + 216 <= a < WAKE_S + 276) \/ wm_win a.

(* ------------------------------------------------------------------ *)
(* Model-side facts                                                    *)
(* ------------------------------------------------------------------ *)

(* g_s's payload bytes are bytes of G. *)
Lemma wm_inG : forall a, WAKE_S <= a < WAKE_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df9c0, 18264). split.
- unfold TG.G_HARNESS. cbn [In]. tauto.
- unfold in_zr, WAKE_S, TA_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* Every byte the piece may change in g_s is a byte of wake_wr Bw and of G. *)
Lemma wm_wr_in : forall Bw a, wm_wr a -> wake_wr Bw a /\ inG TG.G_HARNESS a.
Proof.
intros Bw a Ha. split; [|apply wm_inG; unfold wm_wr, wm_win, WAKE_S, TA_g_s, TW.SZ_g_s in *; lia].
unfold wm_wr, wm_win in Ha. unfold wake_wr, twa_fld.
unfold TW.A_S_inflight_frame, TW.A_S_inflight_len, TW.A_S_stats_tx_wakes, TW.A_S_inflight, TW.A_S_inflight_counter,
  TW.A_S_inflight_retries, TW.A_S_inflight_sent_us, TW.OFF_g_s, SENDCTL_F, WAKE_S, TA_g_s in *.
destruct Ha as [H|[H|[H|H]]].
- do 4 right; left. lia.
- do 7 right; left. lia.
- destruct (Z_lt_ge_dec a (6158784 + 1744)) as [L1|L1]; [do 5 right; left; lia|].
  destruct (Z_lt_ge_dec a (6158784 + 1748)) as [L2|L2]; [do 8 right; left; lia|].
  destruct (Z_lt_ge_dec a (6158784 + 1752)) as [L3|L3]; [do 9 right; left; lia|].
  do 10 right; left. lia.
- do 6 right; left. lia.
Qed.

(* byte k of a value read modulo a larger power of two *)
Lemma wm_byte_mod : forall x N k, 0 <= k -> k + 8 <= N -> Z.shiftr (x mod 2 ^ N) k mod 256 = Z.shiftr x k mod 256.
Proof.
intros x N k Hk HkN. change 256 with (2 ^ 8). apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 8) as [H8|H8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* the sign-extended 4-byte load of an atom *)
Lemma wm_sext : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
intros E n v H R. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma wm_nth_zs : forall (l : list byte) j, nth j (TW.zs l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
intros l. unfold TW.zs. induction l as [|x l IH]; intros [|j]; cbn [nth map]; try reflexivity. apply IH.
Qed.

(* A sequence of writes inside one payload row: each span written with its bytes, every other payload byte kept. *)
Lemma wm_writes : forall T o b n (ws : list (Z * list byte)) rd rd' Bw,
  tw_ok T -> In (o, b, n) T -> tw_at T rd Bw ->
  Forall (fun w => 0 <= fst w /\ fst w + Z.of_nat (length (snd w)) <= n /\
     forall j, (j < length (snd w))%nat ->
       rd' (b + fst w + Z.of_nat j) = Some (bv_unsigned (nth j (snd w) (Z_to_bv 8 0)))) ws ->
  (forall x, tw_in T x ->
     Forall (fun w => ~ (b + fst w <= x < b + fst w + Z.of_nat (length (snd w)))) ws -> rd' x = rd x) ->
  tw_at T rd' (fold_left (fun X w => TW.upd X (o + fst w) (snd w)) ws Bw).
Proof.
intros T o b n ws. induction ws as [|w ws IH]; intros rd rd' Bw Hok Hin Hat Hws Hout.
- cbn [fold_left]. apply (tw_kept T rd rd' Bw Hat). intros x Hx. apply Hout; [exact Hx | constructor].
- apply Forall_cons_iff in Hws as [(Hk & Hkn & Hv) Hws]. cbn [fold_left].
  set (rd1 := fun x => if ((b + fst w <=? x) && (x <? b + fst w + Z.of_nat (length (snd w))))%bool then rd' x else rd x).
  apply (IH rd1 rd' (TW.upd Bw (o + fst w) (snd w)) Hok Hin).
  + apply (tw_upd T rd rd1 Bw o b n (fst w) (snd w) Hok Hat Hin Hk Hkn).
    * intros j Hj. unfold rd1.
      replace ((b + fst w <=? b + fst w + Z.of_nat j) && (b + fst w + Z.of_nat j <? b + fst w + Z.of_nat (length (snd w))))%bool
        with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      exact (Hv j Hj).
    * intros x Hx Hn. unfold rd1.
      destruct ((b + fst w <=? x) && (x <? b + fst w + Z.of_nat (length (snd w))))%bool eqn:Eb; [|reflexivity].
      exfalso. apply andb_true_iff in Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  + exact Hws.
  + intros x Hx Hall. unfold rd1.
    destruct ((b + fst w <=? x) && (x <? b + fst w + Z.of_nat (length (snd w))))%bool eqn:Eb; [reflexivity|].
    apply Hout; [exact Hx|]. constructor; [|exact Hall].
    apply andb_false_iff in Eb. destruct Eb as [Eb|Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia.
Qed.

(* The memcpy's 60 bytes and the six stores of +0x278 .. +0x324, in the model's order and form. *)
Definition wm_ws (B1 e2 : list byte) (now : Z) : list (Z * list byte) :=
  [(216, e2); (1736, TW.put 8 (Z.of_nat (length e2)));
   (18224, TW.put 8 (TS0.u64 (TW.S_stats_tx_wakes
                               (TW.set_S_inflight_len (TW.set_S_inflight_frame B1 e2) (Z.of_nat (length e2))) + 1)));
   (212, TW.put 4 1); (1744, TW.put 4 (TW.S_host_counter (wake_w2 B1 e2))); (1748, TW.put 4 0);
   (1752, TW.put 8 now)].

Lemma wm_ws_w3 : forall B1 e2 now,
  fold_left (fun X w => TW.upd X (TW.OFF_g_s + fst w) (snd w)) (wm_ws B1 e2 now) B1 = wake_w3 B1 e2 now.
Proof.
intros B1 e2 now. unfold wm_ws. cbn [fold_left fst snd].
change (TW.OFF_g_s + 216) with TW.A_S_inflight_frame.
change (TW.OFF_g_s + 1736) with TW.A_S_inflight_len.
change (TW.OFF_g_s + 18224) with TW.A_S_stats_tx_wakes.
change (TW.OFF_g_s + 212) with TW.A_S_inflight.
change (TW.OFF_g_s + 1744) with TW.A_S_inflight_counter.
change (TW.OFF_g_s + 1748) with TW.A_S_inflight_retries.
change (TW.OFF_g_s + 1752) with TW.A_S_inflight_sent_us.
unfold wake_w3, wake_w2. cbv zeta.
unfold TW.set_S_inflight_sent_us, TW.set_S_inflight_retries, TW.set_S_inflight_counter, TW.set_S_inflight,
  TW.set_S_stats_tx_wakes, TW.set_S_inflight_len, TW.set_S_inflight_frame.
reflexivity.
Qed.

(* stats.tx_wakes and host_counter, read after the stores before them, are B1's *)
Lemma wm_tx_eq : forall B1 e2, length B1 = Z.to_nat TW.W_LEN -> length e2 = 60%nat ->
  TW.S_stats_tx_wakes (TW.set_S_inflight_len (TW.set_S_inflight_frame B1 e2) (Z.of_nat (length e2))) =
  TW.u_at B1 (TW.OFF_g_s + 18224) 8.
Proof.
intros B1 e2 HB HL. unfold TW.S_stats_tx_wakes, TW.set_S_inflight_len, TW.set_S_inflight_frame.
wk_out. reflexivity.
Qed.

Lemma wm_hc_eq : forall B1 e2, length B1 = Z.to_nat TW.W_LEN -> length e2 = 60%nat ->
  TW.u_at (wake_w2 B1 e2) TW.A_S_host_counter 4 = TW.u_at B1 (TW.OFF_g_s + 160) 4.
Proof.
intros B1 e2 HB HL. unfold wake_w2. cbv zeta.
unfold TW.set_S_stats_tx_wakes, TW.set_S_inflight_len, TW.set_S_inflight_frame.
unfold TW.A_S_host_counter. wk_out. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Tactics                                                             *)
(* ------------------------------------------------------------------ *)

Ltac wm_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
Ltac wm_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* the write right of a run from the six regions: three read-only, three bytes of G *)
Ltac wm_awr U19x U21x :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  do 3 (apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  do 2 (apply awr_ok_x_cons_g; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19x in Ha; apply wm_inG;
          unfold TW.SZ_g_s; lia |]);
  apply awr_ok_x_cons_g; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U21x in Ha; apply wm_inG;
          unfold TW.SZ_g_s; lia |];
  apply awr_ok_x_nil.
Ltac wm_awr0 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.
(* the windows a run wrote, each inside wm_win *)
Ltac wm_wins Hin Hx U19x U21x :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U19x, ?U21x in Hx;
    first [lia | left; lia | right; left; lia | right; right; lia] |]);
  destruct Hin.
(* After the run to a cut from a state with no region: every byte of the view as at m5 (KD), presence grown (GR). *)
Ltac wm_after_cut HS W KD GR m5 msF :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end;
  assert (KD : forall a, aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) m5 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a; rewrite (aview_wrap64 tfibsegs _ (ms_mem msF) a), (aview_wrap64 tfibsegs _ m5 a);
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
    match goal with HFx : frame_of ?E ?rs (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (can_aview_kept_frame E rs (w_H W) m5 (ms_mem msF) 0 HFx ltac:(lia)
               ltac:(let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
                     intros x Hx; unfold in_wrange; intros (r & Hr & _); vm_compute in Hr; destruct Hr) _ Ha) end
  | ];
  assert (GR : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].
Ltac wm_kreg HS EEx r n Q H :=
  lazymatch type of Q with _ = ?v =>
    wm_reg HS r v H ltac:(cbn [sv_denot]; rewrite (EEx n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.

(* ------------------------------------------------------------------ *)
(* The machine-side lemmas                                             *)
(* ------------------------------------------------------------------ *)

Section wm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* Every range of g_s's payload is addressable at every AR state: whole granules of the record's zero shadow. *)
Lemma wm_ra : forall ly S (W : world segs) mem md q n,
  trans_wake_cells B -> @AR rc segs B ly S W mem md -> WAKE_S <= q -> q + n <= WAKE_S + TW.SZ_g_s ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q n.
Proof.
intros ly S W mem md q n HZ HAR Hq Hqn x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : WAKE_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= WAKE_S + TW.SZ_g_s)
  by (unfold WAKE_S, TA_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md WAKE_S (WAKE_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The shadow entries of run 2 hold at every AR state. *)
Lemma wm_shok : forall ly S (W : world segs) mem md (E : env),
  trans_wake_cells B -> @AR rc segs B ly S W mem md ->
  bv_unsigned (ew E 19) = WAKE_S -> bv_unsigned (ew E 21) = WAKE_S + 18224 -> bv_unsigned (ew E 26) = SHADOW_OFF ->
  sh_ok segs WM_Bx WM_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E HZ HAR U19 U21 U26.
assert (CS : WAKE_S = 6158784) by reflexivity.
assert (UB : U E WM_Bx = SHADOW_OFF).
{ unfold U, WM_Bx. cbn [sv_denot]. rewrite U26, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
unfold sh_ok, WM_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range segs (w_H W) mem _ WM_Bx 19 (WAKE_S + 112) 1648 WAKE_S 112 1760
    (wm_ra ly S W mem md (WAKE_S + 112) 1648 HZ HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) UB).
  + unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. rewrite CS; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. rewrite CS in Hx. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range segs (w_H W) mem _ WM_Bx 21 (WAKE_S + 18224) 8 (WAKE_S + 18224) 0 8
    (wm_ra ly S W mem md (WAKE_S + 18224) 8 HZ HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) UB).
  + unfold U. cbn [sv_denot]. rewrite U21, Z.add_0_r. apply unsigned_lit_small. rewrite CS; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. rewrite CS in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The walk's valuation at the mid cut. *)
Definition wm_E (regs : bvmap 5 word) (TX HC ST : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 TX; Z_to_bv 64 HC; Z_to_bv 64 ST]).
Definition wm_E2 (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF]).

(* The entry state at +0x264, and the shadow entries. *)
Lemma wm_entry0 : forall ly S (W : world segs) regs mem md TX HC ST sp1,
  trans_wake_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  YK11.getr regs 19 = w64 WAKE_S -> YK11.getr regs 21 = w64 (WAKE_S + 18224) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  0 <= TX < 2 ^ 64 -> 0 <= HC < 2 ^ 32 -> 0 <= ST < 2 ^ 32 ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 16) 8 60 ->
  val_mem segs (mrestrict (w_H W) mem) (WAKE_S + 112) 4 ST ->
  val_mem segs (mrestrict (w_H W) mem) (WAKE_S + 160) 4 HC ->
  val_mem segs (mrestrict (w_H W) mem) (WAKE_S + 18224) 8 TX ->
  st_ok_pi segs VAL (wm_E regs TX HC ST) ss_wm0
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WAKE_MID)) mem (YK11.seg_rom segs))) /\
  sh_ok segs WM_Bx WM_SH (wm_E regs TX HC ST) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md TX HC ST sp1 HZ HAR R9 Hsp Hsp32 R19 R21 R26 HTX HHC HST V16 V112 V160 V18224.
assert (CS : WAKE_S = 6158784) by reflexivity.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (wm_E regs TX HC ST) n = YK11.getr regs r)
  by (intros n r Hn; unfold wm_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew (wm_E regs TX HC ST) 33 = Z_to_bv 64 TX)
  by (unfold wm_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (wm_E regs TX HC ST) 34 = Z_to_bv 64 HC)
  by (unfold wm_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew (wm_E regs TX HC ST) 35 = Z_to_bv 64 ST)
  by (unfold wm_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (U9 : bv_unsigned (ew (wm_E regs TX HC ST) 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew (wm_E regs TX HC ST) 19) = WAKE_S)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; rewrite CS; lia).
assert (U21 : bv_unsigned (ew (wm_E regs TX HC ST) 21) = WAKE_S + 18224)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; rewrite CS; lia).
assert (U26 : bv_unsigned (ew (wm_E regs TX HC ST) 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew (wm_E regs TX HC ST) 33) = TX) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (wm_E regs TX HC ST) 34) = HC) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew (wm_E regs TX HC ST) 35) = ST) by (rewrite E35; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_wm0, wm_regions.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [wm_rg_klp wm_rg_st wm_rg_hc wm_rg_inf wm_rg_il wm_rg_tx
         YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ sp1 16 8 (SLit 60) 60); [reflexivity | zside | zside | exact V16].
    * rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ WAKE_S 112 4 (SOff 35 0) ST);
        [cbn [sv_denot]; rewrite U35, Z.add_0_r; reflexivity | exact HST | lia | exact V112].
    * rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ WAKE_S 160 4 (SOff 34 0) HC);
        [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | exact HHC | lia | exact V160].
    * rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (WAKE_S + o) G_HARNESS_rw).
      apply wm_inG. unfold TW.SZ_g_s. lia.
    * rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (WAKE_S + o) G_HARNESS_rw).
      apply wm_inG. unfold TW.SZ_g_s. lia.
    * rewrite U21. split; [lia|]. split; [rewrite CS; lia|]. split.
      -- intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (WAKE_S + 18224 + o) G_HARNESS_rw).
         apply wm_inG. unfold TW.SZ_g_s. lia.
      -- constructor; [|constructor].
         apply (chunk_ok_val segs _ _ (WAKE_S + 18224) 0 8 (SOff 33 0) TX);
           [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact HTX | lia |].
         rewrite Z.add_0_r. exact V18224.
  + apply pairwise_disjoint_of_extents.
    unfold wm_rg_klp, wm_rg_st, wm_rg_hc, wm_rg_inf, wm_rg_il, wm_rg_tx, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U19, U21. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite CS. repeat split; first [exact I | lia].
  + unfold wm_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U19, U21, U26, U33, U34, U35.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- exact (wm_shok ly S W mem md _ HZ HAR U19 U21 U26).
Qed.

(* The state at +0x344 with no region. *)
Lemma wm_entry2 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (wm_E2 regs) ss_wm2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WM_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_wm2.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* A chunk of a region, read byte by byte through the view. *)
Lemma wm_field : forall E H (m : word -> option byte) n bb cs lo hi wlo whi od (w : N) e x,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = bb -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 x ->
  Z.of_N w <= 8 ->
  forall j, (j < N.to_nat w)%nat -> aview segs H m (bb + od + Z.of_nat j) = Some (YO0f.le_byte x (N.to_nat w) j).
Proof.
intros E H m n bb cs lo hi wlo whi od w e x (_ & _ & _ & Hcs) Hn Hc He Hw j Hj.
pose proof (N_nat_Z w) as Hnw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck (Z.of_nat j) ltac:(unfold YP09.c_len; cbn [YP09.cv_len YP09.c_val]; lia)) as (b & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. rewrite He in Hb1. injection Hb1 as <-.
unfold aview. rewrite Hb2. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (2 ^ 64). unfold YO0f.le_byte.
rewrite (wm_byte_mod x 64 (8 * Z.of_nat j)) by lia.
rewrite (wm_byte_mod x (8 * Z.of_nat (N.to_nat w)) (8 * Z.of_nat j)) by lia.
reflexivity.
Qed.

(* A garr8 byte, read through the view. *)
Lemma wm_aview_garr8 : forall H (m : word -> option byte) a l j,
  garr8 segs (mrestrict H m) a l -> (j < length l)%nat -> aview segs H m (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m a l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite tw_le_byte1 by lia. apply Z.mod_small. lia.
Qed.

(* e2_len: the 8 bytes send_control stored at klp hold 60. *)
Lemma wm_klp_val : forall mm a, garr8 segs mm a (TW.zs (TW.put 8 60)) -> val_mem segs mm a 8 60.
Proof.
intros mm a Hg kk Hk. assert (Hl : length (TW.zs (TW.put 8 60)) = 8%nat) by (vm_compute; reflexivity).
destruct (Hg kk ltac:(rewrite Hl; exact Hk)) as [Hv _]. specialize (Hv 0%nat ltac:(lia)).
cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. rewrite Hv. f_equal. f_equal.
do 8 (destruct kk as [|kk]; [vm_compute; reflexivity|]). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The mid piece                                                       *)
(* ------------------------------------------------------------------ *)

Lemma wake_mid : @wake_mid_stmt fx rc B MT.
Proof.
unfold wake_mid_stmt. intros NTC E2C.
unfold wake_mid_at. intros HLAWS AI0 AS0 NT0.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' B1 e2 rs pos sp1 F ly2 S2 W2
  mem2 md2 e regs2 HFIX HMID HREGS.
pose proof HLAWS as (HPCS & HCELLS & HZ & HGU & HGNE0 & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HFIX as (HJe & Hra & Hra4 & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw & Hfn & Hm & HTF0
  & HTFO0 & HROM0 & HAP & Hfly & Hcmd & Hcnt & Hev & Esp1 & EF & HF4096 & HF64 & HFc & HFapp).
pose proof HMID as (HCUR & Hdk & Hfor & HSC & Hrs & He2 & HST1 & HGOT1 & Htw1 & Hfn1 & Hg8e2 & Hrd2 & Hg8klp).
pose proof HCUR as (HJ & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof HREGS as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q24 & Q25) & Q19 & Q20 & Q21 & Q22 & Q26).
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof wake_stk_bounds as (WS1 & WS2 & WS3 & WS4 & WS5 & WS6).
assert (CS : WAKE_S = 6158784) by reflexivity.
assert (CT : TA_g_s = 6158784) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HNS : ESTACK <= NOTICE_STK) by (unfold NOTICE_STK; lia).
unfold WAKE_FBYTES in HFc.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (can_sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
replace (32 * ((spZ regs + -128) / 32)) with sp1 in Hsp1r, Hsp1al, Hsp1al16
  by (rewrite Esp1; unfold WAKE_FRAME; f_equal; f_equal; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe) as HAR.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
assert (Hin2 : In (WAKE_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 WAKE_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
assert (NGF : forall a, F <= a < F + 256 -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  apply (frm_img segs B LAWS _ _ _ _ _ WAKE_CID pos a HAR2 Hin2); [|exact Hi].
  rewrite EFA. change (fs_frame_bytes WAKE_CID) with 256. lia. }
(* the values the entry state's chunks hold: B1's bytes *)
assert (HLB1 : length B1 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw1).
set (TX := TW.u_at B1 (TW.OFF_g_s + 18224) 8).
set (HC := TW.u_at B1 (TW.OFF_g_s + 160) 4).
set (ST := TW.u_at B1 (TW.OFF_g_s + 112) 4).
assert (RTX : 0 <= TX < 2 ^ 64) by exact (TWL.u_at_range B1 _ 8).
assert (RHC : 0 <= HC < 2 ^ 32) by exact (TWL.u_at_range B1 _ 4).
assert (RST : 0 <= ST < 2 ^ 32) by exact (TWL.u_at_range B1 _ 4).
assert (V112 : val_mem segs (mrestrict (w_H W2) mem2) (WAKE_S + 112) 4 ST)
  by exact (tw_read_val segs _ TMAP_A B1 TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 TMAP_A_ok Htw1 TMAP_A_g_s
              ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
assert (V160 : val_mem segs (mrestrict (w_H W2) mem2) (WAKE_S + 160) 4 HC)
  by exact (tw_read_val segs _ TMAP_A B1 TW.OFF_g_s TA_g_s TW.SZ_g_s 160 4 TMAP_A_ok Htw1 TMAP_A_g_s
              ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
assert (V18224 : val_mem segs (mrestrict (w_H W2) mem2) (WAKE_S + 18224) 8 TX)
  by exact (tw_read_val segs _ TMAP_A B1 TW.OFF_g_s TA_g_s TW.SZ_g_s 18224 8 TMAP_A_ok Htw1 TMAP_A_g_s
              ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
unfold WAKE_KLPOFF in Hg8klp. pose proof (wm_klp_val _ _ Hg8klp) as Vklp.
change (TW.A_S_stats_tx_wakes - TW.OFF_g_s) with 18224 in Q21.
unfold WAKE_E2OFF in Q22, Hg8e2, Hrd2. unfold SENDCTL_F in Hrd2.
destruct (wm_entry0 ly2 S2 W2 regs2 mem2 md2 TX HC ST sp1 HZ HAR2 Q9 ltac:(lia) Hsp1al Q19 Q21 Q26
  RTX RHC RST Vklp V112 V160 V18224) as [HS SHOK].
set (E0 := wm_E regs2 TX HC ST) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, wm_E; apply Eimg_env).
assert (EE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = YK11.getr regs2 rr)
  by (intros n rr Hn; unfold E0, wm_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U19 : bv_unsigned (ew E0 19) = WAKE_S)
  by (rewrite (EE0 19%nat 19%bv eq_refl), Q19; apply unsigned_lit_small; rewrite CS; lia).
assert (U21 : bv_unsigned (ew E0 21) = WAKE_S + 18224)
  by (rewrite (EE0 21%nat 21%bv eq_refl), Q21; apply unsigned_lit_small; rewrite CS; lia).
assert (U26 : bv_unsigned (ew E0 26) = SHADOW_OFF)
  by (rewrite (EE0 26%nat 26%bv eq_refl), Q26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E0 9) = sp1) by (rewrite (EE0 9%nat 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
assert (E33 : ew E0 33 = Z_to_bv 64 TX)
  by (unfold E0, wm_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E0 34 = Z_to_bv 64 HC)
  by (unfold E0, wm_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E0 35 = Z_to_bv 64 ST)
  by (unfold E0, wm_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
(* run 1, +0x264 .. +0x274 *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ wm_awr U19 U21. }
rename HF into HF1, HFr into HFr1, HG into HG1.
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
rename ms into ms1.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ wm_win a ->
  aview segs (w_H W2) (ms_mem ms1) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ wm_win HFr1); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. unfold wm_win. wm_wins Hin Hx U19 U21. }
wm_reg HS (10%bv : bv 5) (w64 (WAKE_S + 216)) Ra10 ltac:(cbn [sv_denot]; rewrite U19; reflexivity).
wm_reg HS (11%bv : bv 5) (w64 (F + 144)) Ra11
  ltac:(cbn [sv_denot]; rewrite (EE0 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q22).
wm_reg HS (12%bv : bv 5) (w64 60) Ra12 ltac:(reflexivity).
wm_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 22288)) Ra1 ltac:(apply codeptr_val; exact HEI).
wm_reg HS (2%bv : bv 5) (w64 sp1) Ra2
  ltac:(cbn [sv_denot]; rewrite (EE0 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q2).
wm_reg HS (3%bv : bv 5) (w64 (as_gp B)) Ra3
  ltac:(cbn [sv_denot]; rewrite (EE0 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans Q3 Hgp)).
wm_reg HS (4%bv : bv 5) (w64 (as_tp B)) Ra4
  ltac:(cbn [sv_denot]; rewrite (EE0 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans Q4 Htp)).
assert (Hsp1 : spZ (ms_regs ms1) = sp1) by (unfold spZ at 1; rewrite Ra2; apply unsigned_lit_small; lia).
(* e2's read facts at the memory of the call *)
assert (Hrd1 : decode_rd_ok W2 (ms_mem ms1) (F + 144) 60).
{ apply (trans_rd_ok_view W2 W2 mem2 (ms_mem ms1) (F + 144) 60 Hrd2).
  - intros a Ha. apply K1; [lia|]. intros X. apply (NGF a ltac:(lia)). apply wm_inG.
    unfold wm_win, TW.SZ_g_s in *. lia.
  - intros s Hs. apply K1; [lia|]. unfold wm_win. rewrite CS. lia. }
destruct Hrd1 as (Hv1 & Hra1 & Hh1 & Ham1 & Hq1 & Hq1').
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
destruct (decode_zshadow_ra B ly2 S2 W2 (ms_mem ms1) md1 WAKE_S (WAKE_S + TW.SZ_g_s) (WAKE_S + 216) 60 HAR1 HZ
  ltac:(lia) ltac:(rewrite CS; apply Z.leb_le; vm_compute; reflexivity)
  ltac:(rewrite CS; unfold TW.SZ_g_s; apply Z.leb_le; vm_compute; reflexivity)) as [HraD HhD].
(* +0x274: __asan_memcpy (s + 216, e2, 60) *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OCpy (transport_sigma TS___asan_memcpy)
    (AI0 fx) TG.G_HARNESS W2 (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly S W0 mem0 md0 ((WAKE_CID, pos) :: own) ly2 S2 md1
    (k + e) (WAKE_S + 216) (F + 144) 60 (sp1 - sp0) (Z_to_bv 64 (BASE + 22288)) HGX G_HARNESS_rw HJ Ra10 Ra11 Ra12).
  - lia.
  - rewrite CS. lia.
  - rewrite CS. lia.
  - rewrite Hsp1. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact Ra3.
  - exact Ra4.
  - exact Ra1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right. apply wm_inG.
    unfold TW.SZ_g_s. lia.
  - left. rewrite C5, CS. lia.
  - exact HraD.
  - intros _. exact HhD.
  - cbv beta iota. refine (conj _ (conj _ (conj _ (conj _ (conj Ham1 (conj Hra1 (fun _ => Hh1))))))).
    + lia.
    + lia.
    + intros a Ha. split; [exact (Hv1 a Ha) | rewrite Hsp1; lia].
    + destruct (Z_le_gt_dec (WAKE_S + 216 + 60) (F + 144)) as [Hd|Hd]; [left; exact Hd|].
      destruct (Z_le_gt_dec (F + 144 + 60) (WAKE_S + 216)) as [Hd'|Hd']; [right; exact Hd'|].
      exfalso. apply (NGF (Z.max (WAKE_S + 216) (F + 144))); [lia|]. apply wm_inG.
      unfold TW.SZ_g_s; lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & H10c & Hcpy & Heff & Hgr3).
cbv beta iota in Hcpy.
(* the six regions, kept by the call *)
jafter_call_keep_hi HS 1024%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 9%nat sp1); [exact U9 | | exact Hgr3]. intros a Ha. apply Heff; lia.
  - apply (region_kept_aview _ _ _ _ 19%nat WAKE_S); [exact U19 | | exact Hgr3]. intros a Ha. rewrite CS in Ha.
    apply Heff; rewrite ?CS; lia.
  - apply (region_kept_aview _ _ _ _ 19%nat WAKE_S); [exact U19 | | exact Hgr3]. intros a Ha. rewrite CS in Ha.
    apply Heff; rewrite ?CS; lia.
  - apply (region_kept_aview _ _ _ _ 19%nat WAKE_S); [exact U19 | | exact Hgr3]. intros a Ha. rewrite CS in Ha.
    apply Heff; rewrite ?CS; lia.
  - apply (region_kept_aview _ _ _ _ 19%nat WAKE_S); [exact U19 | | exact Hgr3]. intros a Ha. rewrite CS in Ha.
    apply Heff; rewrite ?CS; lia.
  - apply (region_kept_aview _ _ _ _ 21%nat (WAKE_S + 18224)); [exact U21 | | exact Hgr3]. intros a Ha.
    rewrite CS in Ha. apply Heff; rewrite ?CS; lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regs3) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U19a : bv_unsigned (ew E1 19) = WAKE_S) by (rewrite E1lo by lia; exact U19).
assert (U21a : bv_unsigned (ew E1 21) = WAKE_S + 18224) by (rewrite E1lo by lia; exact U21).
assert (U26a : bv_unsigned (ew E1 26) = SHADOW_OFF) by (rewrite E1lo by lia; exact U26).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
pose proof (wm_shok _ _ _ _ _ E1 HZ HAR3 U19a U21a U26a) as SHOK1.
clear SHOK.
(* run 2, +0x278 .. +0x344 *)
paj_run_tok RUN HS HJ3 SHOK1 YC4b.Bspan.
{ wm_awr U19a U21a. }
rename HF into HF2, HFr into HFr2, HG into HG2.
set (md5 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md5. clear mat.
rename ms into ms5.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E5 := EF) in HS end.
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew E0 n).
{ intros n Hn. unfold E5. repeat rewrite ew_ewset_other by lia. apply E1lo. exact Hn. }
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ wm_win a ->
  aview segs (w_H W2) (ms_mem ms5) a = aview segs (w_H W2) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ wm_win HFr2); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. unfold wm_win. wm_wins Hin Hx U19a U21a. }
(* the registers at +0x344 *)
wm_reg HS (2%bv : bv 5) (w64 sp1) X2
  ltac:(cbn [sv_denot]; rewrite (E5lo 2%nat ltac:(lia)), (EE0 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q2).
wm_reg HS (3%bv : bv 5) (YK11.getr regs 3) X3
  ltac:(cbn [sv_denot]; rewrite (E5lo 3%nat ltac:(lia)), (EE0 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q3).
wm_reg HS (4%bv : bv 5) (YK11.getr regs 4) X4
  ltac:(cbn [sv_denot]; rewrite (E5lo 4%nat ltac:(lia)), (EE0 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q4).
wm_reg HS (8%bv : bv 5) (w64 (spZ regs)) X8
  ltac:(cbn [sv_denot]; rewrite (E5lo 8%nat ltac:(lia)), (EE0 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q8).
wm_reg HS (9%bv : bv 5) (w64 sp1) X9
  ltac:(cbn [sv_denot]; rewrite (E5lo 9%nat ltac:(lia)), (EE0 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q9).
wm_reg HS (18%bv : bv 5) (w64 F) X18
  ltac:(cbn [sv_denot]; rewrite (E5lo 18%nat ltac:(lia)), (EE0 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q18).
wm_reg HS (24%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) X24
  ltac:(cbn [sv_denot]; rewrite (E5lo 24%nat ltac:(lia)), (EE0 24%nat 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q24).
wm_reg HS (25%bv : bv 5) (w64 F) X25
  ltac:(cbn [sv_denot]; rewrite (E5lo 25%nat ltac:(lia)), (EE0 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q25).
wm_reg HS (19%bv : bv 5) (w64 WAKE_S) X19
  ltac:(cbn [sv_denot]; rewrite (E5lo 19%nat ltac:(lia)), (EE0 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q19).
wm_reg HS (26%bv : bv 5) (w64 SHADOW_OFF) X26
  ltac:(cbn [sv_denot]; rewrite (E5lo 26%nat ltac:(lia)), (EE0 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q26).
wm_reg HS (21%bv : bv 5) (w64 (WAKE_S + (TW.A_S_state - TW.OFF_g_s))) X21
  ltac:(cbn [sv_denot]; rewrite (E5lo 19%nat ltac:(lia)), U19; reflexivity).
wm_reg HS (22%bv : bv 5) (w64 (SHADOW_OFF + (WAKE_S + (TW.A_S_state - TW.OFF_g_s)) / 8)) X22
  ltac:(cbn [sv_denot]; rewrite (E5lo 19%nat ltac:(lia)), (E5lo 26%nat ltac:(lia)), U19, U26;
        unfold w64, WAKE_S, TA_g_s, SHADOW_OFF; vm_compute; reflexivity).
assert (E35f : ew E5 35 = Z_to_bv 64 ST) by (rewrite E5lo by lia; exact E35).
wm_reg HS (23%bv : bv 5) (w64 (TW.S_state Bw)) X23
  ltac:(rewrite (wm_sext E5 35 ST E35f RST), <- HST1; reflexivity).
wm_reg HS (27%bv : bv 5) (w64 1) X27 ltac:(reflexivity).
(* run 2's stores, read from its regions *)
pose proof (st_ok_pi_region_nth E5 _ (restrict (w_H W2) ms5) 3 _ HS eq_refl) as RG3. cbn [ms_mem restrict] in RG3.
pose proof (st_ok_pi_region_nth E5 _ (restrict (w_H W2) ms5) 4 _ HS eq_refl) as RG4. cbn [ms_mem restrict] in RG4.
pose proof (st_ok_pi_region_nth E5 _ (restrict (w_H W2) ms5) 5 _ HS eq_refl) as RG5. cbn [ms_mem restrict] in RG5.
assert (U19f : bv_unsigned (ew E5 19) = WAKE_S) by (rewrite E5lo by lia; exact U19).
assert (U21f : bv_unsigned (ew E5 21) = WAKE_S + 18224) by (rewrite E5lo by lia; exact U21).
pose proof (wm_field _ _ _ _ _ _ _ _ _ _ 212 4 (SLit 1) 1 RG3 U19f ltac:(wm_in) eq_refl ltac:(lia)) as VINF.
pose proof (wm_field _ _ _ _ _ _ _ _ _ _ 1736 8 (SLit 60) 60 RG4 U19f ltac:(wm_in) eq_refl ltac:(lia)) as VLEN.
pose proof (wm_field _ _ _ _ _ _ _ _ _ _ 1748 4 (SLit 0) 0 RG4 U19f ltac:(wm_in) eq_refl ltac:(lia)) as VRET.
pose proof (wm_field _ _ _ _ _ _ _ _ _ _ 1744 4 (SExt true 32 (SOff 34 0)) (bv_swrap 32 HC) RG4 U19f ltac:(wm_in)
  (wm_sext E5 34 HC ltac:(rewrite E5lo by lia; exact E34) RHC) ltac:(lia)) as VCNT.
pose proof (wm_field _ _ _ _ _ _ _ _ _ _ 1752 8 (SOff 20 0) now RG4 U19f ltac:(wm_in)
  ltac:(cbn [sv_denot]; rewrite (E5lo 20%nat ltac:(lia)), (EE0 20%nat 20%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Q20) ltac:(lia)) as VSENT.
pose proof (wm_field _ _ _ _ _ _ _ _ _ _ 0 8 (SOff 33 1) (TX + 1) RG5 U21f ltac:(wm_in)
  ltac:(cbn [sv_denot]; rewrite (E5lo 33%nat ltac:(lia)), E33, unsigned_lit_small by lia; reflexivity)
  ltac:(lia)) as VTX.
clear RG3 RG4 RG5.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR5.
set (m5 := ms_mem ms5) in *.
(* every byte outside the ESTACK window below sp1 and wm_wr is the one at the mid cut *)
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp1 - ESTACK <= a < sp1) \/ wm_wr a) ->
  aview segs (w_H W2) m5 a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. unfold wm_wr in Hn.
  rewrite (K3 a Ha ltac:(intros X; apply Hn; right; right; exact X)).
  rewrite (Heff a Ha ltac:(intros X; apply Hn; right; left; lia) ltac:(intros X; apply Hn; left; lia)).
  exact (K1 a Ha ltac:(intros X; apply Hn; right; right; exact X)). }
assert (GR5 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) m5 a).
{ intros a Ha. apply (apresent_grows _ _ _ a HG2). apply Hgr3. exact (apresent_grows _ _ _ a HG1 Ha). }
(* what the call keeps, at m5 *)
assert (KG5 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 m5 (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw)).
{ apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W2 mem2 m5
    (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw) (fun a => (sp1 - ESTACK <= a < sp1) \/ wm_wr a) HAR HK KALL GR5).
  - intros a [X|X] Hc; [lia|]. exfalso.
    pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX (proj2 (wm_wr_in Bw a X))) as Hl. lia.
  - intros b m i Hb Hi [X|X]; [|exact (proj1 (wm_wr_in Bw _ X))]. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a [X|X] Hi HnG _ _.
    + pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
    + exact (HnG (proj2 (wm_wr_in Bw _ X))).
  - intros cid pos0 a Hin Hr [X|X]; [|exact (proj1 (wm_wr_in Bw _ X))]. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
(* the thirteen saved words and the flag-pointer word, at m5 *)
assert (HSV5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) m5) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) WAKE_SAVED).
{ apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HSV o Ho) as Hv.
  assert (Hob : 8 <= fst o <= 104).
  { unfold WAKE_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [Ho|Ho]; [subst o; cbn [fst]; lia|]). destruct Ho. }
  rewrite <- Hv. apply rdword_ext. intros i Hi. apply KALL; [lia|].
  intros [X|X]; [lia|]. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS _ HGX (proj2 (wm_wr_in Bw _ X))).
  lia. }
assert (HFL5 : rdword (aview segs (w_H W2) m5) (F + WAKE_FBYTES - 8) = Some (flag_addr lyc WAKE_CID pos)).
{ rewrite <- HFL. apply rdword_ext. intros i Hi. unfold WAKE_FBYTES. apply KALL; [lia|].
  intros [X|X]; [lia|]. exact (NGF (F + 256 - 8 + i) ltac:(lia) (proj2 (wm_wr_in Bw _ X))). }
(* the world relation at wake_w3 B1 e2 now *)
destruct (wk_w3_keep B1 e2 now HLB1 He2) as (HL2 & HL3 & EST3 & EGOT3 & EFN3).
assert (HWS : Forall (fun w => 0 <= fst w /\ fst w + Z.of_nat (length (snd w)) <= TW.SZ_g_s /\
    forall j, (j < length (snd w))%nat ->
      aview segs (w_H W2) m5 (TA_g_s + fst w + Z.of_nat j) = Some (bv_unsigned (nth j (snd w) (Z_to_bv 8 0))))
  (wm_ws B1 e2 now)).
{ unfold wm_ws. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [lia|]);
    (split; [rewrite ?TWL.length_put, ?He2; unfold TW.SZ_g_s; lia|]); intros j Hj; rewrite ?TWL.length_put in Hj.
  - rewrite He2 in Hj.
    rewrite (K3 (TA_g_s + 216 + Z.of_nat j) ltac:(rewrite CT; lia) ltac:(unfold wm_win; rewrite CS, CT; lia)).
    change TA_g_s with WAKE_S. rewrite (Hcpy (Z.of_nat j) ltac:(lia)).
    rewrite (K1 (F + 144 + Z.of_nat j) ltac:(lia)
      ltac:(intros X; apply (NGF (F + 144 + Z.of_nat j) ltac:(lia)); apply wm_inG; unfold wm_win, TW.SZ_g_s in X |- *;
            lia)).
    rewrite (wm_aview_garr8 _ _ _ _ j Hg8e2 ltac:(unfold TW.zs; rewrite length_map; lia)).
    rewrite wm_nth_zs. reflexivity.
  - rewrite He2. change (Z.of_nat 60) with 60. rewrite tw_le_byte_put by exact Hj. exact (VLEN j Hj).
  - rewrite (wm_tx_eq B1 e2 HLB1 He2). fold TX. rewrite wk_put8_u64 by lia.
    rewrite tw_le_byte_put by exact Hj. pose proof (VTX j Hj) as V. rewrite Z.add_0_r in V. exact V.
  - rewrite tw_le_byte_put by exact Hj. exact (VINF j Hj).
  - unfold TW.S_host_counter. rewrite wk_put4_s32. unfold TW.s32_at. rewrite (wm_hc_eq B1 e2 HLB1 He2). fold HC.
    rewrite tw_le_byte_put by exact Hj. exact (VCNT j Hj).
  - rewrite tw_le_byte_put by exact Hj. exact (VRET j Hj).
  - rewrite tw_le_byte_put by exact Hj. exact (VSENT j Hj). }
assert (HWO : forall x, tw_in TMAP_A x ->
  Forall (fun w => ~ (TA_g_s + fst w <= x < TA_g_s + fst w + Z.of_nat (length (snd w)))) (wm_ws B1 e2 now) ->
  aview segs (w_H W2) m5 x = aview segs (w_H W2) mem2 x).
{ intros x Hx Hall. unfold wm_ws in Hall. rewrite !Forall_cons_iff in Hall.
  destruct Hall as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & _). cbn [fst snd] in N1, N2, N3, N4, N5, N6, N7.
  rewrite He2 in N1. rewrite !TWL.length_put in N2, N3, N4, N5, N6, N7.
  assert (Hg : inG TG.G_HARNESS x).
  { destruct Hx as (o & b & n & Hin & Hb). pose proof (TMAP_A_in_G o b n Hin) as HGr.
    unfold inG. apply Exists_exists. exists (b, n). split; [exact HGr | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS x HGX Hg) as Hl.
  apply KALL; [lia|]. intros [X|X]; [lia|]. unfold wm_wr, wm_win in X. rewrite CS in X.
  rewrite CT in N1, N2, N3, N4, N5, N6, N7. lia. }
assert (TW5 : tw_at TMAP_A (aview segs (w_H W2) m5) (wake_w3 B1 e2 now)).
{ rewrite <- wm_ws_w3.
  exact (wm_writes TMAP_A TW.OFF_g_s TA_g_s TW.SZ_g_s (wm_ws B1 e2 now) _ _ B1 TMAP_A_ok TMAP_A_g_s Htw1 HWS HWO). }
(* the facts both cuts carry, moved to a later memory whose view is the same *)
assert (CURF : forall mF mdF,
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((WAKE_CID, pos) :: own) ly2 S2 W2 mF mdF (k + e) ->
  (forall a, aview segs (w_H W2) mF a = aview segs (w_H W2) m5 a) ->
  (forall a, apresent (w_H W2) m5 a -> apresent (w_H W2) mF a) ->
  wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mF mdF e /\
  tw_at TMAP_A (aview segs (w_H W2) mF) (wake_w3 B1 e2 now)).
{ intros mF mdF HJF KD GR.
  split.
  - refine (conj HJF (conj He (conj Hfrs (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
    + apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W2 m5 mF
        (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw) (fun _ => False) HAR KG5).
      * intros a _ _. exact (KD a).
      * exact GR.
      * intros a [].
      * intros b m i _ _ [].
      * intros a [].
      * intros cid pos0 a _ _ [].
    + refine (Forall_impl _ _ HSV5). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
    + rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL5.
  - apply (tw_kept TMAP_A (aview segs (w_H W2) m5)); [exact TW5 | intros x _; exact (KD x)]. }
(* the model: wake_model on wake_mid_cur's path, then set_state_m *)
rewrite wake_model in Hm.
rewrite (proj2 (Z.eqb_neq _ _) Hdk) in Hm. rewrite Hfor in Hm. change (negb (0 =? 0)) with false in Hm.
rewrite HSC in Hm. cbv beta iota in Hm. rewrite (proj2 (Z.ltb_ge _ _) Hrs) in Hm. cbv beta iota in Hm.
destruct (TSS.set_state_m timg_A TF (wake_w3 B1 e2 now) TS0.DIGINET_S_WAKING TS0.DIGINET_R_WAKE) as [[B2 u2]|] eqn:ESS;
  [|discriminate Hm].
destruct (wake_some_inv _ _ _ _ Hm) as [EB2 Er].
assert (HSR : - 2 ^ 63 <= TW.S_state Bw < 2 ^ 63)
  by (pose proof (wk_s32_range Bw TW.A_S_state) as R; unfold TW.S_state; lia).
(* +0x344: `bne s7, s11`, from a state with no region *)
pmkst HS.
clear HS SHOK1 HEI HEI1.
pose proof (wm_entry2 W2 (ms_regs ms5) m5) as HS.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (wm_E2 (ms_regs ms5)) (mrestrict (w_H W2) m5)) by constructor.
assert (HEIbr : img_env VAL A_LIM (wm_E2 (ms_regs ms5))) by (unfold wm_E2; apply Eimg_env).
assert (EE2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (wm_E2 (ms_regs ms5)) n = YK11.getr (ms_regs ms5) rr)
  by (intros n rr Hn; unfold wm_E2; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (D23 : sv_denot (wm_E2 (ms_regs ms5)) (SOff 23 0) = Z_to_bv 64 (TW.S_state Bw))
  by (cbn [sv_denot]; rewrite (EE2 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X23).
assert (D27 : sv_denot (wm_E2 (ms_regs ms5)) (SOff 27 0) = Z_to_bv 64 1)
  by (cbn [sv_denot]; rewrite (EE2 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X27).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WM_C2)) mm rom) mdx) Q) end.
psrr_branch_tok RUN BR HS SHOK WM_B0.
- (* S_state Bw <> S_WAKING: to the notice cut +0x350 *)
  cbn [branch_taken] in Hc. rewrite D23, D27 in Hc. rewrite (wk_eqb (TW.S_state Bw) 1 HSR ltac:(lia)) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ3 SHOK WM_B0 WAKE_NTC.
  { wm_awr0. }
  wm_after_cut HS W2 KD GR m5 msF.
  wm_kreg HS EE2 (2%bv : bv 5) 2%nat X2 Y2. wm_kreg HS EE2 (3%bv : bv 5) 3%nat X3 Y3.
  wm_kreg HS EE2 (4%bv : bv 5) 4%nat X4 Y4. wm_kreg HS EE2 (8%bv : bv 5) 8%nat X8 Y8.
  wm_kreg HS EE2 (9%bv : bv 5) 9%nat X9 Y9. wm_kreg HS EE2 (18%bv : bv 5) 18%nat X18 Y18.
  wm_kreg HS EE2 (24%bv : bv 5) 24%nat X24 Y24. wm_kreg HS EE2 (25%bv : bv 5) 25%nat X25 Y25.
  wm_kreg HS EE2 (19%bv : bv 5) 19%nat X19 Y19. wm_kreg HS EE2 (21%bv : bv 5) 21%nat X21 Y21.
  wm_kreg HS EE2 (22%bv : bv 5) 22%nat X22 Y22. wm_kreg HS EE2 (23%bv : bv 5) 23%nat X23 Y23.
  wm_kreg HS EE2 (26%bv : bv 5) 26%nat X26 Y26. wm_kreg HS EE2 (27%bv : bv 5) 27%nat X27 Y27.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WAKE_NTC)) mm rom) mdx) Q) end.
  destruct (CURF (ms_mem msF) _ HJ3 KD GR) as (CUR6 & TW6).
  assert (Hne3 : TW.S_state (wake_w3 B1 e2 now) <> TS0.DIGINET_S_WAKING) by (rewrite EST3, HST1; exact Hc).
  destruct (wk_set_state_go timg_A TF (wake_w3 B1 e2 now) TS0.DIGINET_S_WAKING TS0.DIGINET_R_WAKE B2 u2 Hne3 ESS)
    as [SN NM0].
  destruct (wk_set_state_keep (wake_w3 B1 e2 now) TS0.DIGINET_S_WAKING HL3) as (HLs & EGOTs & EFNs & ENs).
  assert (HWON : TS0.DIGINET_S_WAKING <> TS0.DIGINET_S_ONLINE) by (unfold TS0.DIGINET_S_WAKING, TS0.DIGINET_S_ONLINE; lia).
  destruct (wk_notice_keep timg_A TF _ B2 _ _ _ HLs HWON NM0) as [FN2 _].
  rewrite EST3, HST1, EB2 in NM0.
  apply (NTC HLAWS AS0 NT0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' B1 e2 pos sp1 F
    ly2 S2 W2 (ms_mem msF) _ e (ms_regs msF) HFIX).
  + refine (conj CUR6 (conj He2 (conj TW6 (conj _ (conj Hc (conj _ (conj SN (conj NM0 (conj _ (eq_sym Er)))))))))).
    * rewrite EST3. exact HST1.
    * rewrite EGOTs, EGOT3. exact HGOT1.
    * rewrite <- EB2, FN2, EFNs, EFN3. exact Hfn1.
  + refine (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 (conj Y24 Y25)))))))
      (conj Y19 (conj Y21 (conj Y22 (conj Y23 (conj Y26 Y27)))))).
- (* S_state Bw = S_WAKING: `li a0, 0`, `j` to the e2 cut +0x410 *)
  cbn [branch_taken] in Hc. rewrite D23, D27 in Hc. rewrite (wk_eqb (TW.S_state Bw) 1 HSR ltac:(lia)) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ3 SHOK WM_B0 WAKE_E2.
  { wm_awr0. }
  wm_after_cut HS W2 KD GR m5 msF.
  wm_kreg HS EE2 (2%bv : bv 5) 2%nat X2 Y2. wm_kreg HS EE2 (3%bv : bv 5) 3%nat X3 Y3.
  wm_kreg HS EE2 (4%bv : bv 5) 4%nat X4 Y4. wm_kreg HS EE2 (8%bv : bv 5) 8%nat X8 Y8.
  wm_kreg HS EE2 (9%bv : bv 5) 9%nat X9 Y9. wm_kreg HS EE2 (18%bv : bv 5) 18%nat X18 Y18.
  wm_kreg HS EE2 (24%bv : bv 5) 24%nat X24 Y24. wm_kreg HS EE2 (25%bv : bv 5) 25%nat X25 Y25.
  wm_reg HS (10%bv : bv 5) (w64 0) Y10 ltac:(reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WAKE_E2)) mm rom) mdx) Q) end.
  destruct (CURF (ms_mem msF) _ HJ3 KD GR) as (CUR6 & TW6).
  assert (Heq3 : TW.S_state (wake_w3 B1 e2 now) = TS0.DIGINET_S_WAKING) by (rewrite EST3, HST1; exact Hc).
  pose proof (wk_set_state_same timg_A TF (wake_w3 B1 e2 now) TS0.DIGINET_S_WAKING TS0.DIGINET_R_WAKE B2 u2 Heq3 ESS)
    as EB2'.
  apply (E2C HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ly2 S2 W2
    (ms_mem msF) _ e (ms_regs msF) HFIX).
  + refine (conj CUR6 (conj _ _)).
    * rewrite <- EB2, EB2'. exact TW6.
    * rewrite <- EB2, EB2', EFN3. exact Hfn1.
  + refine (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 (conj Y24 Y25))))))) _).
    rewrite Y10, <- Er. reflexivity.
Qed.

End wm.
