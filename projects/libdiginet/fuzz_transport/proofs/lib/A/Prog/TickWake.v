(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its numbers changed; 1131 of its 1294 lines of code are new or changed and 1047 lines of the source are left out. *)
(* TickWake: the wake piece of diginet_session_tick's image-A G-form walk, tick_wake : tick_wake_stmt (TickCut.v),
   code 0x894e8 .. 0x8961c (+0x230 .. +0x364 from the entry 0x892b8). From the wake cut (tick_wake_cur: the state the
   head loaded is S_WAKING, no byte of G stored yet), run 1 (PaRun token engine) does the checked loads of
   g_s.wake_sent_us (s + 152) and g_s.cfg.wake_timeout_ms (s + 44), loads now from s1 + 56 and stops at
   `bltu a1, a0` (+0x270). Taken (no timeout; the model's rest is TickCut.v tick_go): one step to the step cut, with
   the memory and the registers of the cut. Not taken (the session is lost; session_lost_cg.v slost_model): run 2 does
   the checked stores of 0 at s + 212 and s + 168, unpoisons the notice's shadow bytes 18 .. 26 and sets up
   __asan_memset (p + 16, 0, 56) at p = frame + 144, taken through TransportGCg.v gx_intrin_at; run 3 stores the
   notice's first 16 bytes (N_STATE, S_IDLE, old S_WAKING, R_WAKE_TIMEOUT), the checked 0 at s + 112, and loads
   g_s.notify and g_s.notify_ctx; `jalr a2` (+0x334) calls notice through the premise transport_notice_cg (the same G
   journal; its kept facts fold with dk_kept_trans_nf_g); run 4 sets s10 = 0, re-poisons the shadow bytes 18 .. 26 and
   ends at the epilogue cut tick_epi_at. Templates: SlostNtc.v and SlostNtcKit.v (the notice through the session
   pointer), SlostHead.v (the stores at s + 212 and s + 168). trans_src_ok is built and destructed only in
   TickSrcKit.v (trans_src_ok_fake for the notice's 72 bytes, trans_tframe_at_top for TF at the notice call). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AE2y AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import SlostCut SlostNtcKit SlostNtc SlostHead.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGNotice TickSrcKit.
(* session_lost_cg after SlostNtc: its slost_ntc (the notice) over SlostNtc.v's theorem of that name. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
io_send_cg session_lost_cg take_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg TickCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* The shadow byte of g_s (s + 0); the checks of s + 44, s + 96, s + 104, s + 112, s + 152, s + 168 and s + 212 read
   the bytes 5, 12, 13, 14, 19, 21 and 26 after it. *)
Definition TW_SH : Z := 2148220728.
Lemma TW_SH_eq : TW_SH = SHADOW_OFF + TICK_S / 8.
Proof. reflexivity. Qed.

(* Run 1, +0x230 .. +0x270: the two g_s fields it loads (atoms 33, 34), their two shadow bytes, and now at s1 + 56
   (atom 32; s1 is atom 9). s4 is s and s8 the shadow base, as literals. No region has a write window. *)
Definition TW_R1_cfg : YP09.region :=
  YP09.mkRegion None (TICK_S + 44) (TICK_S + 48) 0 0 [YP09.mkChunk (TICK_S + 44) (YP09.CVal 4 (SOff 33 0))].
Definition TW_R1_sent : YP09.region :=
  YP09.mkRegion None (TICK_S + 152) (TICK_S + 160) 0 0 [YP09.mkChunk (TICK_S + 152) (YP09.CVal 8 (SOff 34 0))].
Definition TW_R1_sh : YP09.region :=
  YP09.mkRegion None (TW_SH + 5) (TW_SH + 20) 0 0
    [YP09.mkChunk (TW_SH + 5) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TW_SH + 19) (YP09.CVal 1 (SLit 0))].
Definition TW_R1_now : YP09.region :=
  YP09.mkRegion (Some 9%nat) 56 64 0 0 [YP09.mkChunk 56 (YP09.CVal 8 (SOff 32 0))].
Definition TW_FACTS1 : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition TW_REGS1 : list sv :=
  sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit TICK_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_tw1 : sstate := mkSS TICK_WAKE TW_REGS1 [TW_R1_cfg; TW_R1_sent; TW_R1_sh; TW_R1_now] None TW_FACTS1.

(* Runs 2 and 3, +0x274 .. +0x334: the notice's shadow bytes 18 .. 26 (s3, atom 19), the notice's first 16 bytes
   (s11 = the frame, atom 27), g_s.notify and g_s.notify_ctx (atoms 32, 33) with the window of g_s.state, the windows
   of g_s.desk_counter_valid and g_s.inflight, and the five g_s shadow bytes the checks read. s4 is s, s8 the shadow
   base and s9 the shadow address of s + 112, as literals. *)
Definition TW_C2 : Z := TICK_WAKE + 0x44.
Definition TW_R2_sh : YP09.region := YP09.mkRegion (Some 19%nat) 18 27 18 27 [].
Definition TW_R2_p : YP09.region := YP09.mkRegion (Some 27%nat) 144 160 144 160 [].
Definition TW_R2_ntf : YP09.region :=
  YP09.mkRegion None (TICK_S + 96) (TICK_S + 116) (TICK_S + 112) (TICK_S + 116)
    [YP09.mkChunk (TICK_S + 96) (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk (TICK_S + 104) (YP09.CVal 8 (SOff 33 0))].
Definition TW_R2_dcv : YP09.region := YP09.mkRegion None (TICK_S + 168) (TICK_S + 172) (TICK_S + 168) (TICK_S + 172) [].
Definition TW_R2_inf : YP09.region := YP09.mkRegion None (TICK_S + 212) (TICK_S + 216) (TICK_S + 212) (TICK_S + 216) [].
Definition TW_R2_shg : YP09.region :=
  YP09.mkRegion None (TW_SH + 12) (TW_SH + 27) 0 0
    [YP09.mkChunk (TW_SH + 12) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TW_SH + 13) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (TW_SH + 14) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TW_SH + 21) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (TW_SH + 26) (YP09.CVal 1 (SLit 0))].
Definition TW_FACTS2 : facts :=
  mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3); (27%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition TW_REGS2 : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit TICK_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF))
    (Z_to_bv 5 25) (SLit (TW_SH + 14)).
Definition ss_tw2 : sstate :=
  mkSS TW_C2 TW_REGS2 [TW_R2_sh; TW_R2_p; TW_R2_ntf; TW_R2_dcv; TW_R2_inf; TW_R2_shg] None TW_FACTS2.

(* Run 4, +0x338 (notice's return) .. the epilogue cut: the shadow bytes 18 .. 26 only. *)
Definition TW_C4 : Z := TICK_WAKE + 0x108.
Definition ss_tw4 : sstate := mkSS TW_C4 sr_atoms [TW_R2_sh] None
  (mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] [] []).

(* The bytes the lost arm may change between the cut and the call of notice: the shadow bytes 18 .. 26, the
   notice's 72 bytes, g_s.state, g_s.desk_counter_valid, g_s.inflight, and __asan_memset's window below s1. *)
Definition tw_Z (F sp1 : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 18 <= x < SHADOW_OFF + F / 8 + 27) \/ (F + 144 <= x < F + 216) \/
  (TICK_S + 112 <= x < TICK_S + 116) \/ (TICK_S + 168 <= x < TICK_S + 172) \/
  (TICK_S + 212 <= x < TICK_S + 216) \/ (sp1 - ESTACK <= x < sp1).

(* ------------------------------------------------------------------ *)
(* The model                                                           *)
(* ------------------------------------------------------------------ *)

(* At S_WAKING the model is the lost arm (session_lost_m with R_WAKE_TIMEOUT, result DIGINET_OK) when the wake
   timeout passed, and tick_go otherwise (TickCut.v; the silence test needs S_ONLINE). *)
Lemma tw_model : forall (TF : option TI.tframe) Bw now Bw' r,
  TW.S_state Bw = TS0.DIGINET_S_WAKING ->
  TSS.diginet_session_tick_m timg_A TF Bw now = Some (Bw', r) ->
  if TS0.ms_m (TW.S_cfg_wake_timeout_ms Bw) <=? TS0.u64 (now - TW.S_wake_sent_us Bw)
  then TSS.session_lost_m timg_A TF Bw TS0.DIGINET_R_WAKE_TIMEOUT = Some (Bw', tt) /\ r = DLib.DIGINET_OK
  else tick_go timg_A TF Bw now = Some (Bw', r).
Proof.
  intros TF Bw now Bw' r Hst Hm. rewrite tick_model in Hm. cbv zeta in Hm. rewrite Hst in Hm.
  change ((TS0.DIGINET_S_WAKING =? TS0.DIGINET_S_CLOSED) || (TS0.DIGINET_S_WAKING =? TS0.DIGINET_S_IDLE))
    with false in Hm.
  change (TS0.DIGINET_S_WAKING =? TS0.DIGINET_S_WAKING) with true in Hm.
  change (TS0.DIGINET_S_WAKING =? TS0.DIGINET_S_ONLINE) with false in Hm.
  cbn [andb] in Hm. revert Hm.
  destruct (TS0.ms_m (TW.S_cfg_wake_timeout_ms Bw) <=? TS0.u64 (now - TW.S_wake_sent_us Bw)); intros Hm.
  - destruct (TSS.session_lost_m timg_A TF Bw TS0.DIGINET_R_WAKE_TIMEOUT) as [[B1 u]|]; [|discriminate Hm].
    destruct u. destruct (tick_some_inv _ _ _ _ Hm) as [E1 E2]. subst. split; reflexivity.
  - exact Hm.
Qed.

(* `bltu a1, a0` at +0x270 with a1 = now - wake_sent_us (the engine's now + sent * -1) and a0 = the zero-extended
   cfg.wake_timeout_ms times 1000: taken exactly when the model's timeout test is false (the plain walk's tmo_bin). *)
Lemma tw_tmo : forall (E : env) now x t,
  ew E 32 = Z_to_bv 64 now -> ew E 34 = Z_to_bv 64 x -> ew E 33 = Z_to_bv 64 t ->
  0 <= now < 2 ^ 64 -> 0 <= x < 2 ^ 64 -> 0 <= t < 2 ^ 32 ->
  branch_taken BC_LTU
    (sv_denot E (SAlu ALU_ADD (SOff 32 0) (SMd M_MUL (SOff 34 0) (SLit (-1)))))
    (sv_denot E (SMd M_MUL (SExt false 32 (SOff 33 0)) (SLit 1000)))
  = negb (TS0.ms_m t <=? TS0.u64 (now - x)).
Proof.
  intros E now x t E32 E34 E33 Hn Hx Ht.
  rewrite branch_ltu_U, U_SAlu. cbn [zalu_raw]. rewrite !U_SMd. cbn [zmd_raw].
  rewrite U_zext, (U_atom E 32 now E32 Hn), (U_atom E 34 x E34 Hx), (U_atom E 33 t E33 ltac:(lia)), !U_SLit.
  unfold zcanon, M64, TS0.ms_m, TS0.u64.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
  change (1000 mod 2 ^ 64) with 1000.
  rewrite (Z.mod_small t (2 ^ 32)) by lia.
  rewrite (Z.mod_small (t * 1000) (2 ^ 64)) by lia.
  rewrite Z.add_mod_idemp_r by lia.
  replace (now + x * (2 ^ 64 - 1)) with ((now - x) + x * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia.
  rewrite Z.leb_antisym, negb_involutive. reflexivity.
Qed.

(* g_s.notify is not one of the three fields the lost arm stores. *)
Lemma tw_notify : forall Bw, length Bw = Z.to_nat TW.W_LEN ->
  TW.S_notify (slost_w2 Bw) = TW.u_at Bw (TW.OFF_g_s + 96) 8.
Proof.
  intros Bw L. rewrite (sn_notify Bw L). unfold slost_w1, TW.set_S_desk_counter_valid, TW.set_S_inflight.
  rewrite !rd_upd_W by wside. reflexivity.
Qed.

(* The world relation after the stores of 0 at s + 212, s + 168 and s + 112 (SlostHead.v slh_tw_w1, then
   TWorldG.v tw_write). *)
Lemma tw_w2 : forall (rd rd' : Z -> option Z) Bw,
  tw_at TMAP_A rd Bw ->
  (forall j, 0 <= j < 4 -> rd' (TICK_S + 212 + j) = Some 0) ->
  (forall j, 0 <= j < 4 -> rd' (TICK_S + 168 + j) = Some 0) ->
  (forall j, 0 <= j < 4 -> rd' (TICK_S + 112 + j) = Some 0) ->
  (forall x, tw_in TMAP_A x -> ~ (TICK_S + 212 <= x < TICK_S + 216) -> ~ (TICK_S + 168 <= x < TICK_S + 172) ->
     ~ (TICK_S + 112 <= x < TICK_S + 116) -> rd' x = rd x) ->
  tw_at TMAP_A rd' (slost_w2 Bw).
Proof.
intros rd rd' Bw Hat HI HD HS HO.
assert (CS : TICK_S = TA_g_s) by reflexivity.
set (rdm := fun x => if ((TICK_S + 112 <=? x) && (x <? TICK_S + 116))%bool then rd x else rd' x).
assert (H1 : tw_at TMAP_A rdm (slost_w1 Bw)).
{ apply (slh_tw_w1 rd rdm Bw Hat).
  - intros j Hj. unfold rdm. cbv beta.
    destruct ((TICK_S + 112 <=? SLOST_S + 212 + j) && (SLOST_S + 212 + j <? TICK_S + 116))%bool eqn:Eb.
    + exfalso. apply andb_true_iff in Eb. destruct Eb as [_ E2]. apply Z.ltb_lt in E2.
      unfold SLOST_S, TICK_S in *. lia.
    + exact (HI j Hj).
  - intros j Hj. unfold rdm. cbv beta.
    destruct ((TICK_S + 112 <=? SLOST_S + 168 + j) && (SLOST_S + 168 + j <? TICK_S + 116))%bool eqn:Eb.
    + exfalso. apply andb_true_iff in Eb. destruct Eb as [_ E2]. apply Z.ltb_lt in E2.
      unfold SLOST_S, TICK_S in *. lia.
    + exact (HD j Hj).
  - intros x Hx H2 H3. unfold rdm. cbv beta.
    destruct ((TICK_S + 112 <=? x) && (x <? TICK_S + 116))%bool eqn:Eb; [reflexivity|].
    apply andb_false_iff in Eb.
    apply HO; [exact Hx | exact H2 | exact H3 |].
    destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia. }
rewrite sn_w2_eq.
apply (tw_write TMAP_A rdm rd' _ TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 0 TMAP_A_ok H1 TMAP_A_g_s);
  [lia | unfold TW.SZ_g_s; lia | |].
- intros j Hj. rewrite <- CS, (HS (Z.of_nat j) ltac:(lia)).
  destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
- intros x Hx Hn. unfold rdm. cbv beta. rewrite <- CS in Hn.
  destruct ((TICK_S + 112 <=? x) && (x <? TICK_S + 116))%bool eqn:Eb; [|reflexivity].
  apply andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  exfalso. apply Hn. lia.
Qed.

(* An 8-byte store of 0x600000001 leaves the 4 bytes of 1, then the 4 bytes of 6. *)
Lemma tw_vm_split : forall (segs : list Segment) (m : word -> option byte) a,
  val_mem segs m a 8 25769803777 -> val_mem segs m a 4 1 /\ val_mem segs m (a + 4) 4 6.
Proof.
  intros segs m a H. split; intros k Hk.
  - pose proof (H k ltac:(lia)) as Hk'.
    destruct k as [|[|[|[|k]]]]; [exact Hk' | exact Hk' | exact Hk' | exact Hk' | lia].
  - pose proof (H (4 + k)%nat ltac:(lia)) as Hk'.
    replace (a + 4 + Z.of_nat k) with (a + Z.of_nat (4 + k)) by lia.
    destruct k as [|[|[|[|k]]]]; [exact Hk' | exact Hk' | exact Hk' | exact Hk' | lia].
Qed.

(* The 72 bytes of the notice at p: the stores of 2 (8 bytes) and 0x600000001 (8 bytes: old = 1, reason = 6) and
   the memset's 56 zeros, read as WalkNotify.v ntc_state_bytes 0 1 6. *)
Lemma tw_nb : forall (segs : list Segment) (H : word -> bool) (m : word -> option byte) p,
  val_mem segs (mrestrict H m) p 8 2 ->
  val_mem segs (mrestrict H m) (p + 8) 8 25769803777 ->
  (forall a, p + 16 <= a < p + 72 -> aview segs H m a = Some 0) ->
  garr8 segs (mrestrict H m) p (map DSpec.bz (WN.ntc_state_bytes 0 1 6)).
Proof.
  intros segs H m p V0 V8 Z0.
  destruct (tw_vm_split segs _ _ V8) as [V8a V12].
  unfold WN.ntc_state_bytes.
  change (TW.put 4 2 ++ TW.put 4 0 ++ TW.put 4 1 ++ TW.put 4 6 ++ repeat (DSpec.b8 0) 56)
    with (TW.put 8 2 ++ TW.put 4 1 ++ TW.put 4 6 ++ repeat (DSpec.b8 0) 56).
  rewrite !map_app. apply garr8_app. split; [exact (garr8_of_put segs _ _ 8 2 V0) |].
  rewrite length_map, TWL.length_put. replace (p + Z.of_nat 8) with (p + 8) by lia.
  apply garr8_app. split; [exact (garr8_of_put segs _ _ 4 1 V8a) |].
  rewrite length_map, TWL.length_put. replace (p + 8 + Z.of_nat 4) with (p + 8 + 4) by lia.
  apply garr8_app. split; [exact (garr8_of_put segs _ _ 4 6 V12) |].
  rewrite length_map, TWL.length_put. replace (p + 8 + 4 + Z.of_nat 4) with (p + 16) by lia.
  rewrite map_repeat. change (DSpec.bz (DSpec.b8 0)) with 0.
  apply garr8_zeros. intros a Ha.
  pose proof (Z0 a ltac:(lia)) as Za. unfold aview in Za.
  destruct (YP09.mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Za].
  cbn in Za. injection Za as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The written range lies below the shadow band                        *)
(* ------------------------------------------------------------------ *)

(* A field of fixed place: its last byte, computed. *)
Ltac tw_lo1 H :=
  lazymatch type of H with
  | twa_fld ?o ?b ?A ?n ?x =>
      let v := eval vm_compute in (b + (A - o) + n) in
      let E := fresh "E" in
      assert (E : b + (A - o) + n = v) by (vm_compute; reflexivity);
      unfold twa_fld in H; rewrite E in H; unfold SHADOW_OFF; lia
  end.

Lemma tw_nwr_lo : forall Bw (n : TI.ntc) a, notice_wr Bw n a -> a < SHADOW_OFF.
Proof.
  intros Bw n a H.
  assert (HG : TA_GOT <= a < TA_GOT + 224 \/ TA_M <= a < TA_M + 1648).
  { unfold notice_wr in H.
    destruct H as [(_ & [(Hg & Hf) | Hf]) | [(_ & Hf) | [(_ & Hf) | [(_ & Hf) | [(_ & Hf) | (_ & Hf)]]]]].
    - left. unfold twa_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ, TC.TRANS_MAX, TW.OFF_GOT in *. lia.
    - left. unfold twa_fld, TW.A_GOT_n, TW.OFF_GOT in Hf. lia.
    - left. unfold twa_fld, TW.A_GOT_acked, TW.OFF_GOT in Hf. lia.
    - right. unfold twa_fld, TW.A_M_fly_on, TW.OFF_M in Hf. lia.
    - left. unfold twa_fld, TW.A_GOT_desk, TW.OFF_GOT in Hf. lia.
    - left. unfold twa_fld, TW.A_GOT_ndata, TW.OFF_GOT in Hf. lia.
    - left. unfold twa_fld, TW.A_GOT_foreign, TW.OFF_GOT in Hf. lia. }
  unfold TA_GOT, TA_M, SHADOW_OFF in *. lia.
Qed.

(* Every byte of tick_wr lies in a harness global, below the shadow band (it is never a frame's shadow byte). *)
Lemma tw_wr_lo : forall Bw a, tick_wr Bw a -> a < SHADOW_OFF.
Proof.
  intros Bw a H. unfold tick_wr, senddata_wr, iosend_wr in H.
  repeat match type of H with _ \/ _ => destruct H as [H | H] end.
  all: first
    [ tw_lo1 H
    | exact (tw_nwr_lo _ _ _ H)
    | destruct H as (s & Hs & H);
      unfold twa_fld, TW.A_Cmd_st, TW.OFF_g_cmd, TA_g_cmd, TC.CMDS_MAX, TW.A_S_queue_bytes, TW.OFF_g_s, TA_g_s,
        TW.S_queue_N, TW.S_queue_ESZ, SHADOW_OFF in *; lia ].
Qed.

Section tw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* ------------------------------------------------------------------ *)
(* Facts on the state                                                  *)
(* ------------------------------------------------------------------ *)

(* g_s's shadow bytes are 0 at every AR state (trans_tick_cells). *)
Lemma tw_gsh0 : forall ly S (W : world segs) mem md o,
  trans_tick_cells B -> @AR rc segs B ly S W mem md -> 0 <= o < 2283 ->
  aview segs (w_H W) mem (TW_SH + o) = Some 0.
Proof.
  intros ly S W mem md o HTC HAR Ho.
  replace (TW_SH + o) with (FCells.shadow_addr (TICK_S + 8 * o)).
  - apply (decode_zshadow_rd B ly S W mem md TICK_S (TICK_S + TW.SZ_g_s) _ HAR); [| | | exact HTC].
    + unfold TICK_S, TA_g_s. rewrite Z.add_mod, Z.mul_comm, Z.mod_mul by lia. reflexivity.
    + lia.
    + unfold TW.SZ_g_s. lia.
  - unfold FCells.shadow_addr, FCells.ASAN_K, TW_SH, TICK_S, TA_g_s.
    replace (6158784 + 8 * o) with ((769848 + o) * 8) by lia.
    rewrite Z.div_mul by lia. lia.
Qed.

(* The notice at p = F + 144, as notice's statement reads it (check_state_data_cg.v trans_ntc_at): SlostNtc.v
   sn_ntc_at for the class-5 frame. *)
Lemma tw_ntc_at : forall lyc S2 (W : world segs) memN mdN (regsC : bvmap 5 word) Bw old why F pos,
  AR_laws segs B -> @AR rc segs B lyc S2 W memN mdN -> In (TICK_CID, pos) (frames S2) ->
  F = frame_addr lyc TICK_CID pos -> 4096 <= F -> F mod 64 = 0 -> F + 2048 <= alloc_ceiling -> in_app F 2048 ->
  F + 2048 <= spZ regsC - NOTICE_STK ->
  TW.S_state (slost_w1 Bw) = old -> - 2 ^ 31 <= old < 2 ^ 31 -> 0 <= why < 2 ^ 31 ->
  (forall i, 18 <= i < 27 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  garr8 segs (mrestrict (w_H W) memN) (F + 144) (map DSpec.bz (WN.ntc_state_bytes 0 old why)) ->
  trans_ntc_at B lyc S2 W memN regsC NOTICE_STK (F + 144) (slost_ntc Bw why).
Proof.
  intros lyc S2 W memN mdN regsC Bw old why F pos LAWS HAR Hin EF HF0 HF64 HFc HFapp Hwin Eold Hold Hwhy ZS HNB.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_frames _ _ LAWS lyc S2 W memN mdN TICK_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
  rewrite <- EF in HFb, HFsh. change (fs_frame_bytes TICK_CID) with 2048 in HFb.
  change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh. change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  unfold trans_ntc_at.
  split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
  split.
  { apply trans_src_ok_fake.
    - exists TICK_CID, pos. split; [exact Hin|]. rewrite <- EF. change (fs_frame_bytes TICK_CID) with 2048.
      unfold NTC_SIZE. lia.
    - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
      + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
      + apply (frame_ra_zero _ F (F + 144) 72 18 27); [lia | exact DFm8 | lia | lia | exact ZS].
      + apply (frame_hull_vis _ F 2048 (F + 144) 72); [lia | exact HF64 | reflexivity | lia | lia | lia |].
        intros i Hi. change (2048 / 8) with 256 in Hi. change (shadow_addr F) with (SHADOW_OFF + F / 8).
        apply can_aview_vis. exact (proj1 (HFsh i Hi)).
      + apply (amem_range_sub_app F 2048); [exact HFapp | lia | lia | lia | lia].
      + lia.
      + lia. }
  split; [left; unfold NTC_SIZE; lia|].
  exists (WN.ntc_state_bytes 0 old why).
  split; [exact HNB|].
  unfold slost_ntc. rewrite Eold.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
    TI.n_body TI.n_ann length].
  unfold WN.ntc_state_bytes, TW.s32_at.
  assert (Z0 : TW.u_at (TW.put 4 2 ++ TW.put 4 0 ++ TW.put 4 old ++ TW.put 4 why ++ repeat (DSpec.b8 0) 56) 48 8 = 0)
    by WN.ntc_field.
  rewrite Z0.
  split; [rewrite ?length_app, ?TWL.length_put, ?repeat_length; reflexivity |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field; apply WN.swrap32_mod; exact Hold |].
  split; [WN.ntc_field; apply WN.swrap32_mod; lia |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [WN.ntc_field |].
  split; [apply garr8_nil |].
  split; [exact (trans_src_ok_null B lyc S2 W memN) |].
  split; [left; lia |].
  WN.ntc_field.
Qed.

(* notice's stores (an N_STATE notice: bytes of GOT) are apart from the notice's own bytes (a frame is not image),
   from its empty body, and from TF (tick_apart: they are bytes of tick_wr, its wake row). *)
Lemma tw_apart : forall lyc S2 (W2 : world segs) mem2 md2 (W : world segs) memN (TF : option TI.tframe) Bw F pos,
  AR_laws segs B -> @AR rc segs B lyc S2 W2 mem2 md2 -> In (TICK_CID, pos) (frames S2) ->
  F = frame_addr lyc TICK_CID pos -> tick_apart TF Bw ->
  notice_apart W memN (F + 144) (slost_ntc Bw TS0.DIGINET_R_WAKE_TIMEOUT) TF (slost_w2 Bw).
Proof.
  intros lyc S2 W2 mem2 md2 W memN TF Bw F pos LAWS HAR Hin EF Hap x Hx.
  assert (Hw : tick_wr Bw x) by (do 13 right; left; exact Hx).
  pose proof (notice_wr_G (slost_w2 Bw) (slost_ntc Bw TS0.DIGINET_R_WAKE_TIMEOUT) x Hx) as Hg.
  split; [|split].
  - intros Hr. apply (frm_img segs B LAWS lyc S2 W2 mem2 md2 TICK_CID pos x HAR Hin);
      [rewrite <- EF; change (fs_frame_bytes TICK_CID) with 2048; unfold NTC_SIZE in Hr; lia|].
    exact (trans_g_img x Hg).
  - intros NB _ _. split.
    + unfold slost_ntc. cbn [TI.n_body length Z.of_nat]. lia.
    + intros Hn. exfalso. apply Hn. reflexivity.
  - intros fr Hfr. exact (Hap x Hw fr Hfr).
Qed.

(* The facts the wake cut carries move to a later memory whose view is the same at every address. *)
Lemma tw_pre_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 mem3 md3,
  tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((TICK_CID, pos) :: own) lyc S2 W mem3 md3 (k + 0) ->
  (forall a, aview segs (w_H W) mem3 a = aview segs (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a) ->
  tick_pre_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem3 md3.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2 mem3 md3
  (((HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) & HN) & Hbl & HGK & Htw) HJ3 KD GR.
refine (conj (conj (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))) _)
  (conj Hbl (conj _ _))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b m i Hb Hi Hn. rewrite KD. exact (K2 b m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HN.
- intros a Ha. rewrite KD. exact (HGK a Ha).
- apply (tw_kept TMAP_A (aview segs (w_H W) mem2)); [exact Htw | intros x _; exact (KD x)].
Qed.

(* ------------------------------------------------------------------ *)
(* The entry states of the runs                                        *)
(* ------------------------------------------------------------------ *)

Definition tw_vals1 (Bw : list byte) (now : Z) : list word :=
  [Z_to_bv 64 now; Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 44) 4); Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 152) 8)].
Definition tw_E1 (regs : bvmap 5 word) (Bw : list byte) (now : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs (tw_vals1 Bw now)).

Lemma tw_entry1_0 : forall ly S (W : world segs) regs mem md Bw now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 - 64 -> sp1 mod 32 = 0 ->
  0 <= now < 2 ^ 64 -> rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  st_ok_pi segs VAL (tw_E1 regs Bw now)
    (mkSS TICK_WAKE sr_atoms [TW_R1_cfg; TW_R1_sent; TW_R1_sh; TW_R1_now] None TW_FACTS1)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_WAKE)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bw now sp1 HTC HAR Htw R9 Hsp Hsp32 Hnow Hrd.
  set (E := tw_E1 regs Bw now).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, tw_E1; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (tw_vals1 Bw now) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, tw_E1; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34.
  cbn [Nat.add nth tw_vals1] in E32, E33, E34.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 44) 4) as R33.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 152) 8) as R34.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R33. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R34.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TW_R1_cfg TW_R1_sent TW_R1_sh TW_R1_now
        base_val]; rewrite ?U9.
    + split; [unfold TICK_S, TA_g_s; lia|]. split; [unfold TICK_S, TA_g_s; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 (TICK_S + 44) 4 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 44) 4));
        [apply DEN; [exact E33 | lia] | exact R33 | lia |].
      replace (0 + (TICK_S + 44)) with (TA_g_s + 44) by (unfold TICK_S; lia).
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 44 4 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold TICK_S, TA_g_s; lia|]. split; [unfold TICK_S, TA_g_s; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 (TICK_S + 152) 8 (SOff 34 0) (TW.u_at Bw (TW.OFF_g_s + 152) 8));
        [apply DEN; [exact E34 | exact R34] | exact R34 | lia |].
      replace (0 + (TICK_S + 152)) with (TA_g_s + 152) by (unfold TICK_S; lia).
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 152 8 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold TW_SH; lia|]. split; [unfold TW_SH; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 (TW_SH + 5) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. apply AE2y.val_mem1_of_aview. exact (tw_gsh0 ly S W mem md 5 HTC HAR ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (TW_SH + 19) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. apply AE2y.val_mem1_of_aview. exact (tw_gsh0 ly S W mem md 19 HTC HAR ltac:(lia)).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 56 8 (SOff 32 0) now); [apply DEN; [exact E32 | exact Hnow] | exact Hnow | lia |].
      apply val_mem_of_rdword. exact Hrd.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, TW_R1_cfg, TW_R1_sent, TW_R1_sh, TW_R1_now.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold TW_SH, SHADOW_OFF, TICK_S, TA_g_s in *. repeat split; first [exact I | lia].
  - unfold TW_FACTS1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma tw_entry1 : forall ly S (W : world segs) regs mem md Bw now sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 <= 2 ^ 47 - 64 -> sp1 mod 32 = 0 ->
  0 <= now < 2 ^ 64 -> rdword (aview segs (w_H W) mem) (sp1 + 56) = Some now ->
  st_ok_pi segs VAL (tw_E1 regs Bw now) ss_tw1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_WAKE)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bw now sp1 HTC HAR Htw R9 R20 R24 Hsp Hsp32 Hnow Hrd.
  rewrite restrict_mkst_fx.
  pose proof (tw_entry1_0 ly S W regs mem md Bw now sp1 HTC HAR Htw R9 Hsp Hsp32 Hnow Hrd) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  exact H2.
Qed.

Definition tw_vals2 (Bw : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 96) 8); Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 104) 8)].
Definition tw_E2 (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transport) (Ereg regs (tw_vals2 Bw)).

Lemma tw_entry2_0 : forall ly S (W : world segs) regs mem md Bw F,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 27 = w64 F ->
  4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 -> in_app F 2048 ->
  (F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F) ->
  (forall a, F + 144 <= a < F + 160 -> apresent (w_H W) mem a) ->
  (forall i, 18 <= i < 27 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (tw_E2 regs Bw)
    (mkSS TW_C2 sr_atoms [TW_R2_sh; TW_R2_p; TW_R2_ntf; TW_R2_dcv; TW_R2_inf; TW_R2_shg] None TW_FACTS2)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TW_C2)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bw F HTC HAR Htw R19 R27 HF0 HF64 HFc HFapp HFG Hpf Hpsh.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (Hg : 64 <= F / 64 * 64) by lia.
  set (E := tw_E2 regs Bw).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, tw_E2; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
    by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U27 : bv_unsigned (ew E 27) = F)
    by (rewrite (EE 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j (tw_vals2 Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, tw_E2; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  cbn [Nat.add nth tw_vals2] in E32, E33.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 96) 8) as R32.
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 104) 8) as R33.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32, R33.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (HGW : forall o, TICK_S <= o < TICK_S + TW.SZ_g_s -> writable_at segs (mrestrict (w_H W) mem) o).
  { intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS o G_HARNESS_rw).
    unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
    split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, TICK_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia]. }
  assert (ZG : forall o, 0 <= o < 2283 ->
    val_mem segs (mrestrict (w_H W) mem) (0 + (TW_SH + o)) (N.to_nat 1) 0).
  { intros o Ho. rewrite Z.add_0_l. apply AE2y.val_mem1_of_aview. exact (tw_gsh0 ly S W mem md o HTC HAR Ho). }
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TW_R2_sh TW_R2_p TW_R2_ntf TW_R2_dcv
        TW_R2_inf TW_R2_shg base_val]; rewrite ?U19, ?U27.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
    + split; [unfold TICK_S, TA_g_s; lia|]. split; [unfold TICK_S, TA_g_s; lia|]. split.
      * intros o Ho. apply HGW. unfold TW.SZ_g_s. lia.
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val segs E _ 0 (TICK_S + 96) 8 (SOff 32 0) (TW.u_at Bw (TW.OFF_g_s + 96) 8));
             [apply DEN; [exact E32 | exact R32] | exact R32 | lia |].
           replace (0 + (TICK_S + 96)) with (TA_g_s + 96) by (unfold TICK_S; lia).
           exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 96 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ 0 (TICK_S + 104) 8 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 104) 8));
             [apply DEN; [exact E33 | exact R33] | exact R33 | lia |].
           replace (0 + (TICK_S + 104)) with (TA_g_s + 104) by (unfold TICK_S; lia).
           exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 104 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold TICK_S, TA_g_s; lia|]. split; [unfold TICK_S, TA_g_s; lia|]. split; [|constructor].
      intros o Ho. apply HGW. unfold TW.SZ_g_s. lia.
    + split; [unfold TICK_S, TA_g_s; lia|]. split; [unfold TICK_S, TA_g_s; lia|]. split; [|constructor].
      intros o Ho. apply HGW. unfold TW.SZ_g_s. lia.
    + split; [unfold TW_SH; lia|]. split; [unfold TW_SH; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 (TW_SH + 12) 1 (SLit 0) 0); [reflexivity | lia | lia | exact (ZG 12 ltac:(lia))].
      * apply (chunk_ok_val segs E _ 0 (TW_SH + 13) 1 (SLit 0) 0); [reflexivity | lia | lia | exact (ZG 13 ltac:(lia))].
      * apply (chunk_ok_val segs E _ 0 (TW_SH + 14) 1 (SLit 0) 0); [reflexivity | lia | lia | exact (ZG 14 ltac:(lia))].
      * apply (chunk_ok_val segs E _ 0 (TW_SH + 21) 1 (SLit 0) 0); [reflexivity | lia | lia | exact (ZG 21 ltac:(lia))].
      * apply (chunk_ok_val segs E _ 0 (TW_SH + 26) 1 (SLit 0) 0); [reflexivity | lia | lia | exact (ZG 26 ltac:(lia))].
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, TW_R2_sh, TW_R2_p, TW_R2_ntf, TW_R2_dcv, TW_R2_inf, TW_R2_shg.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U27.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, TW_SH, SHADOW_OFF, TICK_S, TA_g_s, TW.SZ_g_s in *.
    rewrite HF8. repeat split; first [exact I | lia].
  - unfold TW_FACTS2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19, U27.
    change (2 ^ 3) with 8. change (2 ^ 6) with 64.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma tw_entry2 : forall ly S (W : world segs) regs mem md Bw F,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 27 = w64 F ->
  YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF -> YK11.getr regs 25 = w64 (TW_SH + 14) ->
  4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 -> in_app F 2048 ->
  (F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F) ->
  (forall a, F + 144 <= a < F + 160 -> apresent (w_H W) mem a) ->
  (forall i, 18 <= i < 27 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (tw_E2 regs Bw) ss_tw2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TW_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bw F HTC HAR Htw R19 R27 R20 R24 R25 HF0 HF64 HFc HFapp HFG Hpf Hpsh.
  rewrite restrict_mkst_fx.
  pose proof (tw_entry2_0 ly S W regs mem md Bw F HTC HAR Htw R19 R27 HF0 HF64 HFc HFapp HFG Hpf Hpsh) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 25) (TW_SH + 14) H2 R25 eq_refl) as H3.
  exact H3.
Qed.

(* The symbolic state at +0x338 (after notice returns): the registers as atoms, the shadow bytes 18 .. 26. *)
Lemma tw_entry4 : forall (W : world segs) regs mem F,
  YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> 4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 ->
  (forall i, 18 <= i < 27 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) ss_tw4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TW_C4)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F R19 HF0 HF64 HFc Hpsh.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  set (E := Eimg (PI := PI_transport) (Ereg regs [])).
  assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
    by (unfold E; rewrite (ew_Eimg_Ereg_nat regs [] 19 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small;
        unfold SHADOW_OFF; lia).
  rewrite restrict_mkst_fx. unfold ss_tw4.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TW_R2_sh base_val]. rewrite U19.
    split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19. change (2 ^ 3) with 8.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The run tactics                                                     *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac
   (SlostNtc.v's section tactic sn_reg). *)
Ltac sn_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "sn_reg: no match for" T; fail
  end.

(* The write rights of a run whose regions have no write window. *)
Ltac tw_awr_vac :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* The write rights of runs 2 and 3 (the six regions of ss_tw2; U19 / U27: the bases' values; EF: the frame's
   address). *)
Ltac tw_awr2 U19 U27 EF :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19 in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- EF; change (fs_frame_bytes TICK_CID / 8) with 256; lia |];
  eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U27 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite <- EF; change (fs_frame_bytes TICK_CID) with 2048; lia |];
  do 3 (apply awr_ok_x_cons_g;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      unfold inG; apply Exists_exists; exists (TA_g_s, TW.SZ_g_s);
      split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia] |]);
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_nil.

(* Every byte kept by a run whose regions have no write window. *)
Ltac tw_kept_vac HFr KD :=
  lazymatch type of HFr with frame_of ?E ?rs (mrestrict ?H ?m) (mrestrict ?H ?m') =>
    assert (KD : forall a, aview segs H m' a = aview segs H m a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in
      intros a; rewrite (aview_wrap64 segs _ m' a), (aview_wrap64 segs _ m a);
      pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
      apply (kept_of_frame E rs H m m' (fun _ => False) HFr); [| exact Ha | intros []];
      let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
      let Hiw := fresh "Hiw" in let Hx := fresh "Hx" in
      intros b wlo whi x Hiw Hx; cbv beta; sn_win Hiw Hx ltac:(lia)
    | ] end.

Lemma tw_wake : @tick_wake_stmt fx rc B MT.
Proof.
unfold tick_wake_stmt. intros STEP EPI. unfold tick_wake_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F S2 mem2 md2
  regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HTC & HGU & HGNE & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGE).
pose proof CALLEES as (HSF8 & HMS & HN & HIO & HSFR & HS00 & HSD & HTK).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & Hsp16 & Hlo & Hhi & Hnow & Htw0 & Hgf & Hm & HTF & Hrom &
  Hapart & Hinv & Hc5 & Hc0 & Hc2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((((HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Hnow56) & Hbl & HGK & Htw1) & Hst).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R19 & R20 & R22 & R23 & R24 & R25) & R21).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold TICK_FBYTES in HFc, HFapp, HFLw.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HTS : TICK_STK = 208 + SENDDATA_STK) by reflexivity.
assert (HNS : NOTICE_STK <= SENDDATA_STK) by (apply Z.leb_le; reflexivity).
assert (HES : ESTACK <= NOTICE_STK) by (apply Z.leb_le; reflexivity).
assert (EST : ESTACK = 4096) by reflexivity.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. unfold TICK_FRAME.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (r0 := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (Hsp1b : 2 ^ 46 <= sp1 <= 2 ^ 47 - 64) by lia.
assert (USP : spZ regs2 = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hin : In (TICK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 TICK_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
rewrite <- EF in HFb, HFsh.
change (fs_frame_bytes TICK_CID) with 2048 in HFb. change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh.
destruct (FFL lyc S2 W mem2 md2 TICK_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
set (FL := flag_addr lyc TICK_CID pos) in *.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
assert (HFG : F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 2048) TICK_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (TICK_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 2048 /\ TICK_S <= x < TICK_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F TICK_S) as [h3|h3]; [exists TICK_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2).
  apply (frm_img segs B LAWS lyc S2 W mem2 md2 TICK_CID pos x HAR2 Hin);
    [rewrite <- EF; change (fs_frame_bytes TICK_CID) with 2048; lia|].
  apply trans_g_img. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, TICK_S in *; cbn [fst snd]; lia]. }
(* the model at S_WAKING *)
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw0).
pose proof (tw_model TF Bw now Bw' r Hst Hm) as HMW.
(* +0x230 .. +0x270: the checked loads of s + 152 and s + 44, now from s1 + 56, `bltu a1, a0` *)
pose proof (tw_entry1 lyc S2 W regs2 mem2 md2 Bw now sp1 HTC HAR2 Htw1 R9 R20 R24 Hsp1b (proj2 Hsp1) Hnow Hnow56)
  as HS.
set (E1 := tw_E1 regs2 Bw now) in HS.
assert (HEI : img_env VAL A_LIM E1) by (unfold E1, tw_E1; apply Eimg_env).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = YK11.getr regs2 r)
  by (intros n r0 Hn; unfold E1, tw_E1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK : sh_ok segs SN_Bx (@nil shent) E1 (mrestrict (w_H W) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
paj_run_tok RUN HS HJ1 SHOK SN_B0.
{ tw_awr_vac. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
tw_kept_vac HFr KD1.
assert (GR1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (EX1 : forall j, (j < 3)%nat -> ew E1 (32 + j) = nth j (tw_vals1 Bw now) (Z_to_bv 64 0))
  by (intros j Hj; unfold E1, tw_E1; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX1 0%nat ltac:(lia)) as E32. pose proof (EX1 1%nat ltac:(lia)) as E33.
pose proof (EX1 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth tw_vals1] in E32, E33, E34.
pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 44) 4) as R33.
pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 152) 8) as R34.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R33. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R34.
pose proof (tw_tmo E1 now (TW.u_at Bw (TW.OFF_g_s + 152) 8) (TW.u_at Bw (TW.OFF_g_s + 44) 4) E32 E34 E33 Hnow R34 R33)
  as HTMO.
change (TW.u_at Bw (TW.OFF_g_s + 152) 8) with (TW.S_wake_sent_us Bw) in HTMO.
change (TW.u_at Bw (TW.OFF_g_s + 44) 4) with (TW.S_cfg_wake_timeout_ms Bw) in HTMO.
psrr_branch_tok RUN BR HS SHOK SN_B0.
- (* now - wake_sent_us below the timeout: no timeout, one step to the step cut (+0x3c8) *)
  rewrite HTMO in Hc. apply negb_true_iff in Hc. rewrite Hc in HMW. clear Hc.
  paj_run_to_tok RUNTO HS HJ1 SHOK SN_B0 TICK_STEP.
  { tw_awr_vac. }
  lazymatch type of HS with context [restrict _ ?m] => rename m into msS end.
  set (md3 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md3. clear mat.
  tw_kept_vac HFr KD2.
  assert (GR2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem msS) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  sn_reg HS (Z_to_bv 5 2) (YK11.getr regs2 (Z_to_bv 5 2)) Y2
    ltac:(cbn [sv_denot]; rewrite (EE1 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS (Z_to_bv 5 3) (YK11.getr regs2 (Z_to_bv 5 3)) Y3
    ltac:(cbn [sv_denot]; rewrite (EE1 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS (Z_to_bv 5 4) (YK11.getr regs2 (Z_to_bv 5 4)) Y4
    ltac:(cbn [sv_denot]; rewrite (EE1 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 8)) Y8
    ltac:(cbn [sv_denot]; rewrite (EE1 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS (Z_to_bv 5 9) (YK11.getr regs2 (Z_to_bv 5 9)) Y9
    ltac:(cbn [sv_denot]; rewrite (EE1 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS (Z_to_bv 5 18) (YK11.getr regs2 (Z_to_bv 5 18)) Y18
    ltac:(cbn [sv_denot]; rewrite (EE1 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS (Z_to_bv 5 19) (YK11.getr regs2 (Z_to_bv 5 19)) Y19
    ltac:(cbn [sv_denot]; rewrite (EE1 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS (Z_to_bv 5 21) (YK11.getr regs2 (Z_to_bv 5 21)) Y21
    ltac:(cbn [sv_denot]; rewrite (EE1 21%nat (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS (Z_to_bv 5 22) (YK11.getr regs2 (Z_to_bv 5 22)) Y22
    ltac:(cbn [sv_denot]; rewrite (EE1 22%nat (Z_to_bv 5 22) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS (Z_to_bv 5 23) (YK11.getr regs2 (Z_to_bv 5 23)) Y23
    ltac:(cbn [sv_denot]; rewrite (EE1 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS (Z_to_bv 5 25) (YK11.getr regs2 (Z_to_bv 5 25)) Y25
    ltac:(cbn [sv_denot]; rewrite (EE1 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS (Z_to_bv 5 27) (YK11.getr regs2 (Z_to_bv 5 27)) Y27
    ltac:(cbn [sv_denot]; rewrite (EE1 27%nat (Z_to_bv 5 27) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS (Z_to_bv 5 20) (w64 TICK_S) Y20 ltac:(reflexivity).
  sn_reg HS (Z_to_bv 5 24) (w64 SHADOW_OFF) Y24 ltac:(reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_STEP)) mm rom) mdx) Q) end.
  apply (STEP LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F S2
    (ms_mem msS) md3 (ms_regs msS) HFIX).
  + split; [| exact HMW].
    apply (tw_pre_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs now Bw pos sp1 F S2 mem2 md2
      (ms_mem msS) md3 (proj1 HCUR) HJ1).
    * intros a. rewrite KD2. exact (KD1 a).
    * intros a Ha. exact (GR2 a (GR1 a Ha)).
  + refine (conj (conj (conj (eq_trans Y2 R2) (conj (eq_trans Y3 R3) (conj (eq_trans Y4 R4) (conj (eq_trans Y8 R8)
      (conj (eq_trans Y9 R9) (conj (eq_trans Y18 R18) (eq_trans Y27 R27))))))) (conj (eq_trans Y19 R19) (conj Y20
      (conj (eq_trans Y22 R22) (conj (eq_trans Y23 R23) (conj Y24 (eq_trans Y25 R25))))))) (eq_trans Y21 R21)).
- (* the wake timeout passed: the session is lost *)
  rewrite HTMO in Hc. apply negb_false_iff in Hc. rewrite Hc in HMW. clear Hc.
  destruct HMW as [HSL Er]. subst r.
  (* +0x270 not taken: one step to +0x274 *)
  paj_run_to_tok RUNTO HS HJ1 SHOK SN_B0 TW_C2.
  { tw_awr_vac. }
  lazymatch type of HS with context [restrict _ ?m] => rename m into msB end.
  set (md3 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md3. clear mat.
  tw_kept_vac HFr KD2.
  assert (GR2 : forall a, apresent (w_H W) (ms_mem ms1) a -> apresent (w_H W) (ms_mem msB) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (KDB : forall a, aview segs (w_H W) (ms_mem msB) a = aview segs (w_H W) mem2 a)
    by (intros a; rewrite KD2; exact (KD1 a)).
  assert (GRB : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem msB) a)
    by (intros a Ha; exact (GR2 a (GR1 a Ha))).
  clear KD1 KD2 GR1 GR2.
  (* the registers at +0x274 *)
  sn_reg HS (Z_to_bv 5 2) (w64 sp1) V2
    ltac:(cbn [sv_denot]; rewrite (EE1 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
  sn_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) V3
    ltac:(cbn [sv_denot]; rewrite (EE1 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans R3 Hgp)).
  sn_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) V4
    ltac:(cbn [sv_denot]; rewrite (EE1 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact (eq_trans R4 Htp)).
  sn_reg HS (Z_to_bv 5 8) (w64 (spZ regs)) V8
    ltac:(cbn [sv_denot]; rewrite (EE1 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R8).
  sn_reg HS (Z_to_bv 5 9) (w64 sp1) V9
    ltac:(cbn [sv_denot]; rewrite (EE1 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R9).
  sn_reg HS (Z_to_bv 5 18) (w64 F) V18
    ltac:(cbn [sv_denot]; rewrite (EE1 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R18).
  sn_reg HS (Z_to_bv 5 19) (w64 (SHADOW_OFF + F / 8)) V19
    ltac:(cbn [sv_denot]; rewrite (EE1 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R19).
  sn_reg HS (Z_to_bv 5 25) (w64 (TW_SH + 14)) V25
    ltac:(cbn [sv_denot]; rewrite (EE1 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R25).
  sn_reg HS (Z_to_bv 5 27) (w64 F) V27
    ltac:(cbn [sv_denot]; rewrite (EE1 27%nat (Z_to_bv 5 27) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R27).
  sn_reg HS (Z_to_bv 5 20) (w64 TICK_S) V20 ltac:(reflexivity).
  sn_reg HS (Z_to_bv 5 24) (w64 SHADOW_OFF) V24 ltac:(reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TW_C2)) mm rom) mdx) Q) end.
  clear HS SHOK.
  set (regsB := ms_regs msB) in *. set (mB := ms_mem msB) in *. clearbody regsB mB. clear msB.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HARB.
  destruct (al_frames _ _ LAWS lyc S2 W mB md3 TICK_CID pos HARB Hin) as (_ & _ & HFbB & HFshB).
  rewrite <- EF in HFbB, HFshB.
  change (fs_frame_bytes TICK_CID) with 2048 in HFbB. change (fs_frame_bytes TICK_CID / 8) with 256 in HFshB.
  rewrite ESH in HFshB.
  assert (HtwB : tw_at TMAP_A (aview segs (w_H W) mB) Bw)
    by (apply (tw_kept TMAP_A (aview segs (w_H W) mem2)); [exact Htw1 | intros x _; exact (KDB x)]).
  (* +0x274 .. +0x2d8: the checked stores of 0 at s + 212 and s + 168, s5 = p, shadow bytes 18 .. 26 := 0, the
     memset's arguments, `jal __asan_memset` *)
  pose proof (tw_entry2 lyc S2 W regsB mB md3 Bw F HTC HARB HtwB V19 V27 V20 V24 V25 HF0 HF64 ltac:(lia) HFapp HFG
    ltac:(intros a Ha; exact (proj1 (HFbB a ltac:(lia))))
    ltac:(intros i Hi; exact (proj1 (HFshB i ltac:(lia))))) as HS.
  set (E2 := tw_E2 regsB Bw) in HS.
  assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2, tw_E2; apply Eimg_env).
  assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = YK11.getr regsB r)
    by (intros n r0 Hn; unfold E2, tw_E2; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  assert (U19 : bv_unsigned (ew E2 19) = SHADOW_OFF + F / 8)
    by (rewrite (EE2 19%nat (Z_to_bv 5 19) eq_refl), V19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U27 : bv_unsigned (ew E2 27) = F)
    by (rewrite (EE2 27%nat (Z_to_bv 5 27) eq_refl), V27; unfold w64; apply unsigned_lit_small; lia).
  assert (SHOK2 : sh_ok segs SN_Bx (@nil shent) E2 (mrestrict (w_H W) mB)) by constructor.
  paj_run_tok RUN HS HJ1 SHOK2 SN_B0.
  { tw_awr2 U19 U27 EF. }
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms2 end.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
  assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ tw_Z F sp1 a ->
    aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) mB a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (tw_Z F sp1) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hiw Hx. cbv beta.
    sn_win Hiw Hx ltac:(rewrite ?U19, ?U27 in Hx; unfold tw_Z, TICK_S, TA_g_s; lia). }
  assert (GA2 : forall a, apresent (w_H W) mB a -> apresent (w_H W) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  first [ pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0
        | pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0 ].
  cbn [ms_mem restrict] in RG0.
  assert (ZS1 : forall i, 18 <= i < 27 -> aview segs (w_H W) (ms_mem ms2) (SHADOW_OFF + F / 8 + i) = Some 0).
  { intros i Hi. rewrite <- U19.
    assert (Hi' : i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26) by lia.
    destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
    apply (sn_chunk0 E2 (w_H W) (ms_mem ms2) (Some 19%nat) _ _ _ _ _ _ RG0);
    cbn [In]; repeat (first [left; reflexivity | right]). }
  clear HF HFr HG RG0.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HARM2.
  destruct (al_frames _ _ LAWS lyc S2 W (ms_mem ms2) md4 TICK_CID pos HARM2 Hin) as (_ & _ & _ & HFsh2).
  rewrite <- EF, ESH in HFsh2. change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh2.
  pmkst HS.
  sn_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 160)) Q10 ltac:(cbn [sv_denot]; rewrite U27; reflexivity).
  sn_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
  sn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 56) Q12 ltac:(reflexivity).
  sn_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
    ltac:(cbn [sv_denot]; rewrite (EE2 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V2).
  sn_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + 33584)) Q1 ltac:(apply codeptr_val; exact HEI2).
  sn_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) Q3
    ltac:(cbn [sv_denot]; rewrite (EE2 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V3).
  sn_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) Q4
    ltac:(cbn [sv_denot]; rewrite (EE2 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V4).
  assert (QSP : spZ (ms_regs ms2) = sp1)
    by (change (bv_unsigned (YK11.getr (ms_regs ms2) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
        apply unsigned_lit_small; lia).
  (* +0x2d8: __asan_memset (p + 16, 0, 56), through the G call kit *)
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
  eapply SRr_bind.
  { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
      (HMS fx) TG.G_HARNESS W (ms_regs ms2) (ms_mem ms2) STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) lyc S2
      md4 (k + 0) (F + 160) 0 56 (sp1 - sp0) (Z_to_bv 64 (BASE + 33584)) HGX G_HARNESS_rw HJ1 Q10 Q11 Q12).
    - lia.
    - lia.
    - lia.
    - rewrite QSP. lia.
    - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
      destruct Hsp1 as (_ & M1). rewrite M1, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
      rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
      apply Z.mod_mul. lia.
    - lia.
    - lia.
    - exact Q3.
    - exact Q4.
    - exact Q1.
    - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
    - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ1|]. intros a Ha. left. rewrite QSP. split.
      + unfold awr_byte. right; right; right. unfold in_frames. exists TICK_CID, pos. split; [left; reflexivity|].
        left. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes TICK_CID) with 2048. lia.
      + lia.
    - apply (amem_range_sub_app F 2048); [exact HFapp | lia | lia | lia | lia].
    - apply (frame_ra_zero _ F (F + 160) 56 20 27); [lia | exact DFm8 | lia | lia |].
      intros i Hi. exact (ZS1 i ltac:(lia)).
    - intros _. apply (frame_hull_vis _ F 2048 (F + 160) 56); [lia | exact HF64 | reflexivity | lia | lia | lia |].
      intros i Hi. change (2048 / 8) with 256 in Hi. change (shadow_addr F) with (SHADOW_OFF + F / 8).
      apply can_aview_vis. exact (proj1 (HFsh2 i Hi)).
    - exact I. }
  cbv beta. intros W2 c2 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HA0M & HsetM & HeffM & HgrM).
  assert (HSHF : SHADOW_OFF + F / 8 + 256 <= F \/ F + 2048 <= SHADOW_OFF + F / 8).
  { pose proof (Z.mul_div_le F 8 ltac:(lia)) as Hd1.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]).
    - right. unfold SHADOW_OFF. lia.
    - left. unfold SHADOW_OFF. lia. }
  assert (HACE : alloc_ceiling <= sp1 - NOTICE_STK) by lia.
  assert (KAM : forall a, 0 <= a < 2 ^ 64 -> ~ tw_Z F sp1 a ->
    aview segs (w_H W) memM a = aview segs (w_H W) mB a).
  { intros a Ha Hn. rewrite HeffM; [exact (KR2 a Ha Hn) | exact Ha | |].
    - intros Hd. apply Hn. right. left. lia.
    - intros Hd. apply Hn. right; right; right; right; right. lia. }
  assert (GAM : forall a, apresent (w_H W) mB a -> apresent (w_H W) memM a)
    by (intros a Ha; exact (HgrM a (GA2 a Ha))).
  jafter_call_keep_hi HS 1024%nat regsM (mrestrict (w_H W) memM) HPM [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - apply (region_kept_aview _ _ _ _ 19%nat (SHADOW_OFF + F / 8)); [exact U19 | | exact HgrM].
      intros a Ha. unfold SHADOW_OFF in *. apply HeffM; [lia | destruct HSHF; lia | lia].
    - apply (region_kept_aview _ _ _ _ 27%nat F); [exact U27 | | exact HgrM].
      intros a Ha. apply HeffM; lia.
    - apply sn_rk_none; [| exact HgrM]. intros a Ha.
      apply HeffM; [lia | destruct HFG; unfold TICK_S, TA_g_s, TW.SZ_g_s in *; lia | lia].
    - apply sn_rk_none; [| exact HgrM]. intros a Ha.
      apply HeffM; [lia | destruct HFG; unfold TICK_S, TA_g_s, TW.SZ_g_s in *; lia | lia].
    - apply sn_rk_none; [| exact HgrM]. intros a Ha.
      apply HeffM; [lia | destruct HFG; unfold TICK_S, TA_g_s, TW.SZ_g_s in *; lia | lia].
    - apply sn_rk_none; [| exact HgrM]. intros a Ha.
      apply HeffM; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
        destruct HFapp as (_ & [HL | (HH1 & HH2)]); lia | lia]. }
  specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  set (E3 := havoc E2 1024 (map (YK11.getr regsM) CLOB)) in HS.
  assert (HEIC : img_env VAL A_LIM E3) by (apply img_env_havoc_hi; [exact HEI2 | cbv; lia]).
  assert (E3lo : forall n, (n < 1024)%nat -> ew E3 n = ew E2 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
  assert (U19b : bv_unsigned (ew E3 19) = SHADOW_OFF + F / 8) by (rewrite E3lo by lia; exact U19).
  assert (U27b : bv_unsigned (ew E3 27) = F) by (rewrite E3lo by lia; exact U27).
  assert (SHOK3 : sh_ok segs SN_Bx (@nil shent) E3 (mrestrict (w_H W) memM)) by constructor.
  assert (ZMM : forall a, F + 160 <= a < F + 216 -> aview segs (w_H W) memM a = Some 0).
  { intros a Ha. replace a with ((F + 160) + (a - (F + 160))) by lia.
    rewrite (HsetM (a - (F + 160)) ltac:(lia)). reflexivity. }
  clear dependent ms2.
  (* +0x2dc .. +0x334: the notice's first 16 bytes, the checked 0 at s + 112, the checked loads of s + 96 and
     s + 104, up to `jalr a2` *)
  paj_run_tok RUN HS HJ2 SHOK3 SN_B0.
  { tw_awr2 U19b U27b EF. }
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms3 end.
  set (md5 := with_vm_backing (m_vm_lazy mdM) mat mdM) in *. clearbody md5. clear mat.
  assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ tw_Z F sp1 a ->
    aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) memM a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (tw_Z F sp1) HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hiw Hx. cbv beta.
    sn_win Hiw Hx ltac:(rewrite ?U19b, ?U27b in Hx; unfold tw_Z, TICK_S, TA_g_s; lia). }
  assert (ZMN : forall a, F + 160 <= a < F + 216 -> aview segs (w_H W) (ms_mem ms3) a = Some 0).
  { intros a Ha. rewrite <- (ZMM a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun x => (SHADOW_OFF + F / 8 + 18 <= x < SHADOW_OFF + F / 8 + 27) \/
      (F + 144 <= x < F + 160) \/ (TICK_S + 112 <= x < TICK_S + 116) \/ (TICK_S + 168 <= x < TICK_S + 172) \/
      (TICK_S + 212 <= x < TICK_S + 216)) HFr); [| lia |].
    - intros b wlo whi x Hiw Hx. cbv beta.
      sn_win Hiw Hx ltac:(rewrite ?U19b, ?U27b in Hx; unfold TICK_S, TA_g_s; lia).
    - cbv beta. unfold TICK_S, TA_g_s, SHADOW_OFF, TW.SZ_g_s in *.
      intros [Hx | [Hx | [Hx | [Hx | Hx]]]]; [destruct HSHF as [Hg | Hg]; lia | lia | destruct HFG as [Hg | Hg]; lia
        | destruct HFG as [Hg | Hg]; lia | destruct HFG as [Hg | Hg]; lia]. }
  assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ tw_Z F sp1 a ->
    aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) mem2 a)
    by (intros a Ha Hn; rewrite (KR3 a Ha Hn), (KAM a Ha Hn); exact (KDB a)).
  assert (GAN : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms3) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAM a (GRB a Ha)))).
  clear HF HFr HG.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS1.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS2.
  pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RS3.
  pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RS4.
  cbn [ms_mem restrict] in RS0, RS1, RS2, RS3, RS4.
  assert (ZSN : forall i, 18 <= i < 27 -> aview segs (w_H W) (ms_mem ms3) (SHADOW_OFF + F / 8 + i) = Some 0).
  { intros i Hi. rewrite <- U19b.
    assert (Hi' : i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26) by lia.
    destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
    apply (sn_chunk0 E3 (w_H W) (ms_mem ms3) (Some 19%nat) _ _ _ _ _ _ RS0);
    cbn [In]; repeat (first [left; reflexivity | right]). }
  pose proof (sn_chunk_val E3 (w_H W) (ms_mem ms3) _ _ _ _ _ _ 144 8 (SLit 2) RS1
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP0.
  pose proof (sn_chunk_val E3 (w_H W) (ms_mem ms3) _ _ _ _ _ _ 152 8 (SLit 25769803777) RS1
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP8.
  pose proof (sn_chunk_val E3 (w_H W) (ms_mem ms3) _ _ _ _ _ _ 6158896 4 (SLit 0) RS2
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG112.
  pose proof (sn_chunk_val E3 (w_H W) (ms_mem ms3) _ _ _ _ _ _ 6158952 4 (SLit 0) RS3
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG168.
  pose proof (sn_chunk_val E3 (w_H W) (ms_mem ms3) _ _ _ _ _ _ 6158996 4 (SLit 0) RS4
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG212.
  cbn [base_val] in VP0, VP8, VG112, VG168, VG212. rewrite U27b in VP0, VP8.
  change (N.to_nat 8) with 8%nat in VP0, VP8. change (N.to_nat 4) with 4%nat in VG112, VG168, VG212.
  change (bv_unsigned (sv_denot E3 (SLit 2)) mod 2 ^ (8 * Z.of_N 8)) with 2 in VP0.
  change (bv_unsigned (sv_denot E3 (SLit 25769803777)) mod 2 ^ (8 * Z.of_N 8)) with 25769803777 in VP8.
  change (bv_unsigned (sv_denot E3 (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VG112, VG168, VG212.
  assert (VP8' : val_mem segs (mrestrict (w_H W) (ms_mem ms3)) (F + 144 + 8) 8 25769803777)
    by (replace (F + 144 + 8) with (F + 152) by lia; exact VP8).
  pose proof (tw_nb segs (w_H W) (ms_mem ms3) (F + 144) VP0 VP8' ltac:(intros a Ha; exact (ZMN a ltac:(lia)))) as HNB.
  assert (Z112 : forall j, 0 <= j < 4 -> aview segs (w_H W) (ms_mem ms3) (TICK_S + 112 + j) = Some 0).
  { intros j Hj. apply (slh_aview_of_val0 (w_H W) (ms_mem ms3) (TICK_S + 112) 4); [|lia].
    replace (TICK_S + 112) with (0 + 6158896) by (unfold TICK_S, TA_g_s; lia). exact VG112. }
  assert (Z168 : forall j, 0 <= j < 4 -> aview segs (w_H W) (ms_mem ms3) (TICK_S + 168 + j) = Some 0).
  { intros j Hj. apply (slh_aview_of_val0 (w_H W) (ms_mem ms3) (TICK_S + 168) 4); [|lia].
    replace (TICK_S + 168) with (0 + 6158952) by (unfold TICK_S, TA_g_s; lia). exact VG168. }
  assert (Z212 : forall j, 0 <= j < 4 -> aview segs (w_H W) (ms_mem ms3) (TICK_S + 212 + j) = Some 0).
  { intros j Hj. apply (slh_aview_of_val0 (w_H W) (ms_mem ms3) (TICK_S + 212) 4); [|lia].
    replace (TICK_S + 212) with (0 + 6158996) by (unfold TICK_S, TA_g_s; lia). exact VG212. }
  (* the model on the lost arm: the state is S_WAKING, so not S_IDLE, and notice gives Bw' *)
  assert (Eold : TW.S_state (slost_w1 Bw) = 1) by (rewrite (proj1 (slh_w1_facts Bw HLB)), Hst; reflexivity).
  assert (HNI : TW.S_state (slost_w1 Bw) <> TS0.DIGINET_S_IDLE)
    by (rewrite Eold; unfold TS0.DIGINET_S_IDLE; lia).
  destruct (sn_model TF Bw TS0.DIGINET_R_WAKE_TIMEOUT Bw' HSL HNI) as (HNT & HNM).
  (* what the call kept, from its entry to the call of notice *)
  destruct (dkg_nf_sep segs B LAWS transport_segs_low lyc Sc S2 W mem2 md2 TICK_CID pos F FL HAR2 Hfrs Hbl EF eq_refl FFL)
    as (N1 & N2 & N3 & N4).
  assert (NZG : forall x, inG TG.G_HARNESS x -> ~ (TICK_S + 112 <= x < TICK_S + 116) ->
    ~ (TICK_S + 168 <= x < TICK_S + 172) -> ~ (TICK_S + 212 <= x < TICK_S + 216) -> ~ tw_Z F sp1 x).
  { intros x Hx H1 H2 H3 Hz. pose proof (inG_low segs B transport_segs_low _ x HGX Hx) as Hl. unfold kLowMemEnd in Hl.
    destruct Hz as [Hz | [Hz | [Hz | [Hz | [Hz | Hz]]]]].
    - unfold SHADOW_OFF in Hz. lia.
    - apply (N2 x); [left; change (fs_frame_bytes TICK_CID) with 2048; lia | exact (trans_g_img x Hx)].
    - exact (H1 Hz).
    - exact (H2 Hz).
    - exact (H3 Hz).
    - lia. }
  assert (HSZ : forall a, tw_Z F sp1 a ->
    (spZ regs - TICK_STK <= a < spZ regs) \/ dkg_nf TICK_CID F FL a \/ inG TG.G_HARNESS a).
  { intros a [Hz | [Hz | [Hz | [Hz | [Hz | Hz]]]]].
    - right; left; right; left. change (fs_frame_bytes TICK_CID / 8) with 256. lia.
    - right; left; left. change (fs_frame_bytes TICK_CID) with 2048. lia.
    - right; right. apply slh_inG. unfold SLOST_S, TICK_S, TW.SZ_g_s in *. lia.
    - right; right. apply slh_inG. unfold SLOST_S, TICK_S, TW.SZ_g_s in *. lia.
    - right; right. apply slh_inG. unfold SLOST_S, TICK_S, TW.SZ_g_s in *. lia.
    - left; lia. }
  pose proof (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc lyc S2 W memc mdc W mem2 md2 mem2
    (ms_mem ms3) (spZ regs - TICK_STK) (spZ regs) TICK_CID pos F FL (tick_wr Bw) (tw_Z F sp1) HGX HARc HAR2 Hfrs
    ltac:(intros bm Hb; rewrite Hbl; exact Hb) eq_refl EF eq_refl FFL ltac:(lia) ltac:(lia) HSZ HK KAN GAN)
    as KCN.
  assert (GKN : gx_kept_ex segs TG.G_HARNESS (tick_wr Bw) W memc W (ms_mem ms3)).
  { intros a Ha Hn. rewrite <- (HGK a Ha).
    apply KAN; [pose proof (inG_low segs B transport_segs_low _ a HGX Ha); unfold kLowMemEnd in *; lia|].
    apply NZG; [exact Ha | | |]; intros Hz; apply Hn.
    - right; right; left. unfold twa_fld, TW.A_S_state, TW.OFF_g_s, TICK_S, TA_g_s in *. lia.
    - right; left. unfold twa_fld, TW.A_S_desk_counter_valid, TW.OFF_g_s, TICK_S, TA_g_s in *. lia.
    - left. unfold twa_fld, TW.A_S_inflight, TW.OFF_g_s, TICK_S, TA_g_s in *. lia. }
  (* the registers at `jalr a2` *)
  assert (E32N : ew E3 32 = Z_to_bv 64 (TI.ti_notice timg_A)).
  { rewrite E3lo by lia. unfold E2, tw_E2. rewrite Eimg_low by (unfold A_TEXT; lia).
    pose proof (ew_Ereg_extra regsB (tw_vals2 Bw) 0) as X. cbn [Nat.add nth tw_vals2] in X. rewrite X.
    rewrite <- (tw_notify Bw HLB), HNT. reflexivity. }
  sn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (TI.ti_notice timg_A)) T12
    ltac:(cbn [sv_denot]; rewrite E32N, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS (Z_to_bv 5 11) (w64 (F + 144)) T11 ltac:(cbn [sv_denot]; rewrite U27b; reflexivity).
  sn_reg HS (Z_to_bv 5 2) (w64 sp1) T2
    ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite (EE2 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact V2).
  sn_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) T3
    ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite (EE2 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact V3).
  sn_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) T4
    ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite (EE2 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact V4).
  sn_reg HS (Z_to_bv 5 8) (w64 (spZ regs)) T8
    ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite (EE2 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact V8).
  sn_reg HS (Z_to_bv 5 9) (w64 sp1) T9
    ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite (EE2 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact V9).
  sn_reg HS (Z_to_bv 5 18) (w64 F) T18
    ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite (EE2 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact V18).
  sn_reg HS (Z_to_bv 5 19) (w64 (SHADOW_OFF + F / 8)) T19
    ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite (EE2 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact V19).
  sn_reg HS (Z_to_bv 5 27) (w64 F) T27
    ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite (EE2 27%nat (Z_to_bv 5 27) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact V27).
  (* +0x334: `jalr a2`, a2 = notice *)
  assert (P4 : 0 <= TI.ti_notice timg_A < 2 ^ 64) by (rewrite (proj1 notice_at); lia).
  assert (P5 : TI.ti_notice timg_A mod 2 = 0) by (rewrite (proj1 notice_at); reflexivity).
  eapply (SRr_jalr_call_pi (PL := PL_transport) (PI := PI_transport) W E3 _ _ _ _ 0x600e7 (1%bv : bv 5)
    (12%bv : bv 5) (TI.ti_notice timg_A) HEIC HS eq_refl);
    [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact T12 | exact P4 | exact P5 |].
  intros matC msJ EmsJ _. subst msJ.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    set (regsC := rg); set (mdC := mdx);
    change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_A) regsC (ms_mem ms3) mdC) Qx) end.
  assert (EBN : BASE + (33672 + 4) = 0x895f0) by (vm_compute; reflexivity).
  assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + (33672 + 4)))
    by (unfold regsC; rewrite YK11.getr_same by (intros Hrc; apply (f_equal bv_unsigned) in Hrc; vm_compute in Hrc;
        discriminate Hrc); reflexivity).
  assert (RCK : forall r : bv 5, bv_unsigned r <> 1 -> YK11.getr regsC r = YK11.getr (ms_regs ms3) r)
    by (intros r0 Hr; unfold regsC; apply YK11.getr_other; intros Ex; apply Hr; rewrite Ex; reflexivity).
  assert (RC2 : YK11.getr regsC 2%bv = w64 sp1) by (rewrite RCK by (vm_compute; discriminate); exact T2).
  assert (RC3 : YK11.getr regsC 3%bv = w64 (as_gp B)) by (rewrite RCK by (vm_compute; discriminate); exact T3).
  assert (RC4 : YK11.getr regsC 4%bv = w64 (as_tp B)) by (rewrite RCK by (vm_compute; discriminate); exact T4).
  assert (RC11 : YK11.getr regsC 11%bv = w64 (F + 144)) by (rewrite RCK by (vm_compute; discriminate); exact T11).
  assert (USPC : spZ regsC = sp1) by (unfold spZ; rewrite RC2; unfold w64; apply unsigned_lit_small; lia).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARN.
  pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & ESLO & ESHI & _).
  assert (HSTKLT : ly_stk_lo lyc < ly_stk_hi lyc) by (rewrite ESLO, ESHI; lia).
  assert (PTW : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms3)) (slost_w2 Bw)).
  { apply (tw_w2 (aview segs (w_H W) mem2) _ Bw Htw1 Z212 Z168 Z112).
    intros x Hx H1 H2 H3.
    assert (HxG : inG TG.G_HARNESS x).
    { destruct Hx as (o & b & n & Hin4 & Hx). unfold inG. apply Exists_exists. exists (b, n).
      split; [exact (TMAP_A_in_G o b n Hin4) | unfold in_zr; cbn [fst snd]; lia]. }
    apply KAN; [pose proof (inG_low segs B transport_segs_low _ x HGX HxG); unfold kLowMemEnd in *; lia|].
    exact (NZG x HxG H3 H2 H1). }
  eapply SRr_bind.
  { exact (HN fx STK sp0 FP ly S W0 mem0 md0 ((TICK_CID, pos) :: own) lyc S2 W (ms_mem ms3) mdC (k + 0) regsC
      (F + 144) (slost_ntc Bw TS0.DIGINET_R_WAKE_TIMEOUT) TF (slost_w2 Bw) Bw'
      ltac:(apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJ2)
      ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
      ltac:(unfold raZ; rewrite RC1, EBN; rewrite unsigned_lit_small by lia; lia)
      RC3 RC4 RC11
      ltac:(rewrite USPC; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; destruct Hsp1 as (_ & M1);
            rewrite M1, Z.add_0_r in D1; rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring;
            apply Z.mod_mul; lia)
      ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
      (tw_ntc_at lyc S2 W (ms_mem ms3) md5 regsC Bw 1 6 F pos LAWS HARN Hin EF HF0 HF64 HFc HFapp
         ltac:(rewrite USPC; lia) Eold ltac:(lia) ltac:(lia) ZSN HNB)
      (trans_tframe_at_top B LAWS HRU HRE lyc Sc W memc mdc S2 (ms_mem ms3) md5 regs regsC TF (tick_wr Bw) TICK_STK
         NOTICE_STK TICK_CID pos
         HARc HARN Hfrs Hbl HSTKLT KCN GKN Hapart (tw_wr_lo Bw) ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) HTF)
      ltac:(intros a Ha; rewrite <- (Hrom a Ha); pose proof KCN as (_ & _ & K3 & _);
            destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He];
            apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He];
            intro Ga; pose proof (inG_G_HARNESS_hull a Ga) as Gh; pose proof (trans_ro_rd_bounds a Ha) as Rb;
            unfold TG.G_HARNESS_LO in Gh; lia)
      PTW HNM
      (tw_apart lyc S2 W mem2 md2 W (ms_mem ms3) TF Bw F pos LAWS HAR2 Hin EF Hapart)
      ltac:(intros HD; exfalso; unfold slost_ntc in HD; cbn [TI.n_kind] in HD;
            unfold TS0.DIGINET_N_STATE, TC.N_DATA in HD; discriminate HD)
      ltac:(unfold TICK_EV in Hev; unfold NOTICE_EV; lia)). }
  intros W3 c3 _ HPOST.
  unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md6 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3).
  assert (He30 : e3 = 0) by (unfold NOTICE_EV in He3; lia). subst e3.
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
  pose proof HJi3 as (HAR3 & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
  clear HJi3 memS3.
  assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
  assert (EF3 : frame_addr ly3 TICK_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF3c; reflexivity).
  assert (Hin3 : In (TICK_CID, pos) (frames S3)) by (rewrite Hfr3; exact Hin).
  destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md6 TICK_CID pos HAR3 Hin3) as (_ & _ & _ & HFsh3).
  rewrite EF3 in HFsh3. change (fs_frame_bytes TICK_CID / 8) with 256 in HFsh3. rewrite ESH in HFsh3.
  assert (Hfrs3 : frames S3 = (TICK_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
  assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3)).
  { intros bm Hbm. rewrite <- Hbl in Hbm. exact (Permutation_in _ (Permutation_sym Hperm3) Hbm). }
  assert (R3_19 : YK11.getr regs3 (Z_to_bv 5 19) = w64 (SHADOW_OFF + F / 8)).
  { rewrite (HP3 19 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). exact T19. }
  (* what the call kept, from its entry to notice's return *)
  assert (KC3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - TICK_STK) (spZ regs)
    (tick_wr Bw)).
  { apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc lyc S2 W memc W (ms_mem ms3) W3 mem3
      (spZ regs - TICK_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (tick_wr Bw)
      (notice_wr (slost_w2 Bw) (slost_ntc Bw TS0.DIGINET_R_WAKE_TIMEOUT)) (dkg_nf TICK_CID F FL)).
    - lia.
    - lia.
    - intros c p. reflexivity.
    - intros f Hf. rewrite Hfrs. right. exact Hf.
    - intros bm Hbm. rewrite Hbl. exact Hbm.
    - exact N1.
    - exact N3.
    - exact KCN.
    - exact HK3.
    - rewrite USPC. lia.
    - rewrite USPC. lia.
    - intros a Ha. left. do 13 right; left. exact Ha. }
  (* +0x338 .. +0x364: s10 = 0, shadow bytes 18 .. 26 := 0xf8, to the epilogue cut *)
  rewrite RC1. change (Z_to_bv 64 (BASE + (33672 + 4))) with (Z_to_bv 64 (BASE + TW_C4)).
  pose proof (tw_entry4 W3 regs3 mem3 F R3_19 HF0 HF64 ltac:(lia)
    ltac:(intros i Hi; exact (proj1 (HFsh3 i ltac:(lia))))) as HS3.
  set (E4 := Eimg (PI := PI_transport) (Ereg regs3 [])) in HS3.
  assert (HEID : img_env VAL A_LIM E4) by (unfold E4; apply Eimg_env).
  assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E4 n = YK11.getr regs3 r)
    by (intros n r0 Hn; unfold E4; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U19c : bv_unsigned (ew E4 19) = SHADOW_OFF + F / 8)
    by (rewrite (EE4 19%nat (Z_to_bv 5 19) eq_refl), R3_19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF;
        lia).
  assert (SHOK4 : sh_ok segs SN_Bx (@nil shent) E4 (mrestrict (w_H W3) mem3)) by constructor.
  paj_run_to_tok RUNTO HS3 HJ3 SHOK4 SN_B0 TICK_EPI.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    eapply awr_ok_x_cons_own with (cid := TICK_CID); [left; reflexivity | |].
    - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19c in Ha.
      right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF3. change (fs_frame_bytes TICK_CID / 8) with 256. lia.
    - apply awr_ok_x_nil. }
  set (md7 := with_vm_backing (m_vm_lazy md6) mat md6) in *. clearbody md7. clear mat.
  lazymatch type of HS3 with context [restrict _ ?m] => rename m into ms4 end.
  assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 18 <= a < SHADOW_OFF + F / 8 + 27) ->
    aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem3 a).
  { intros a Ha Hn.
    apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 18 <= x < SHADOW_OFF + F / 8 + 27) HFr);
      [| exact Ha | exact Hn].
    intros b wlo whi x Hiw Hx. cbv beta. sn_win Hiw Hx ltac:(rewrite ?U19c in Hx; lia). }
  assert (GA4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms4) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  assert (KC4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 (ms_mem ms4) (spZ regs - TICK_STK) (spZ regs)
    (tick_wr Bw)).
  { apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly3 S3 W memc mdc W3 mem3 md6 mem3
      (ms_mem ms4) (spZ regs - TICK_STK) (spZ regs) TICK_CID pos F FL (tick_wr Bw)
      (fun x => SHADOW_OFF + F / 8 + 18 <= x < SHADOW_OFF + F / 8 + 27) HGX HARc HAR3 Hfrs3 Hbl3 ELF3c EF eq_refl FFL
      ltac:(lia) ltac:(lia)); [| exact KC3 | exact KR4 | exact GA4].
    intros a Ha. right. left. right. left. change (fs_frame_bytes TICK_CID / 8) with 256. cbv beta in Ha. lia. }
  pmkst HS3.
  (* the registers the epilogue reads *)
  sn_reg HS3 (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) F2
    ltac:(cbn [sv_denot]; rewrite (EE4 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS3 (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) F3
    ltac:(cbn [sv_denot]; rewrite (EE4 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS3 (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) F4
    ltac:(cbn [sv_denot]; rewrite (EE4 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS3 (Z_to_bv 5 8) (YK11.getr regs3 (Z_to_bv 5 8)) F8
    ltac:(cbn [sv_denot]; rewrite (EE4 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS3 (Z_to_bv 5 9) (YK11.getr regs3 (Z_to_bv 5 9)) F9
    ltac:(cbn [sv_denot]; rewrite (EE4 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS3 (Z_to_bv 5 18) (YK11.getr regs3 (Z_to_bv 5 18)) F18
    ltac:(cbn [sv_denot]; rewrite (EE4 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS3 (Z_to_bv 5 27) (YK11.getr regs3 (Z_to_bv 5 27)) F27
    ltac:(cbn [sv_denot]; rewrite (EE4 27%nat (Z_to_bv 5 27) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sn_reg HS3 (Z_to_bv 5 26) (Z_to_bv 64 0) F26 ltac:(reflexivity).
  (* the bytes the epilogue reads: the saved words above s1 and the frame's last word *)
  pose proof HK3 as (K31 & _ & _ & K34 & _).
  assert (KSTK : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W) mem2 a).
  { intros a Ha. rewrite KR4 by (unfold SHADOW_OFF; lia). rewrite USPC in K31. rewrite K31 by lia.
    apply KAN; [lia|]. unfold tw_Z, TICK_S, TA_g_s, SHADOW_OFF. lia. }
  assert (KFL : forall i, 0 <= i < 8 ->
    aview segs (w_H W3) (ms_mem ms4) (F + 2040 + i) = aview segs (w_H W) mem2 (F + 2040 + i)).
  { intros i Hi. rewrite KR4 by (unfold SHADOW_OFF in *; destruct HSHF; lia).
    rewrite (K34 TICK_CID pos (F + 2040 + i) Hin).
    - apply KAN; [lia|]. unfold tw_Z, TICK_S, TA_g_s, SHADOW_OFF in *.
      intros [Hz | [Hz | [Hz | [Hz | [Hz | Hz]]]]];
        [destruct HSHF; lia | lia | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia
        | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia | destruct HFG as [Hg | Hg]; unfold TW.SZ_g_s in Hg; lia
        | lia].
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes TICK_CID) with 2048. lia.
    - intros Hw.
      pose proof (notice_wr_G (slost_w2 Bw) (slost_ntc Bw TS0.DIGINET_R_WAKE_TIMEOUT) (F + 2040 + i) Hw) as Hg.
      apply (N2 (F + 2040 + i)); [left; change (fs_frame_bytes TICK_CID) with 2048; lia|].
      exact (trans_g_img _ Hg). }
  assert (HSo : forall o, In o TICK_SAVED -> 8 <= fst o <= 104).
  { intros o Ho. unfold TICK_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + TICK_EPI)) mm rom) mdx) Q) end.
  apply (EPI LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now DLib.DIGINET_OK TF Bw Bw' pos
    sp1 F ly3 S3 W3 (ms_mem ms4) md7 0 (ms_regs ms4) HFIX).
  + split; [|split].
    * split; [replace (k + 0) with (k + 0 + 0) by lia; exact HJ3|].
      split; [unfold TICK_EV; lia|].
      split; [exact Hfrs3|].
      split; [rewrite <- Hbl; exact Hperm3|].
      split; [exact ELF3c|].
      split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
      split; [exact KC4|].
      split.
      -- rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
         pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSTK. lia.
      -- unfold TICK_FBYTES. change (flag_addr lyc TICK_CID pos) with FL. rewrite <- HFLw.
         replace (F + 2048 - 8) with (F + 2040) by lia.
         apply rdword_ext. intros i Hi. exact (KFL i Hi).
    * apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Htw3|].
      intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
      apply KR4; [lia | unfold SHADOW_OFF; lia].
    * rewrite (sn_gfn' TF Bw TS0.DIGINET_R_WAKE_TIMEOUT Bw' HLB HNM). exact Hgf.
  + assert (CH : forall n, acallee_saved n -> bv_unsigned (Z_to_bv 5 n) <> 1 ->
      YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr (ms_regs ms3) (Z_to_bv 5 n))
      by (intros n Hn H1; rewrite (HP3 n Hn); exact (RCK _ H1)).
    refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))) F26).
    * exact (eq_trans F2 (eq_trans (CH 2 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T2)).
    * exact (eq_trans F3 (eq_trans (CH 3 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T3 (eq_sym Hgp)))).
    * exact (eq_trans F4 (eq_trans (CH 4 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) (eq_trans T4 (eq_sym Htp)))).
    * exact (eq_trans F8 (eq_trans (CH 8 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T8)).
    * exact (eq_trans F9 (eq_trans (CH 9 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T9)).
    * exact (eq_trans F18 (eq_trans (CH 18 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T18)).
    * exact (eq_trans F27 (eq_trans (CH 27 ltac:(hnf; lia) ltac:(vm_compute; discriminate)) T27)).
Qed.

End tw.

(* The wake piece of the walk of diginet_session_tick (TickCut.v tick_wake_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem tick_wake : forall fx rc B MT, @tick_wake_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@tw_wake fx rc B MT). Qed.

Print Assumptions tick_wake.
