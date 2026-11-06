(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 902 of its 1078 lines of code are new or changed and 963 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SlostHead.v, with its module paths, module names and numbers changed; 2194 of its 2305 lines of code are new or changed and 967 lines of the source are left out. *)
(* diginet_session_init, image B: Theorem transport_diginet_session_init_cg_holds, the statement
   transport_diginet_session_init_cg_holds_stmt of lib/B/Prog/diginet_session_init_cg.v: the machine walk of
   diginet_session_init on fuzz_transport.asan-ubsan at 0x8680c (556 bytes, frame 64).

   The walk is image A's (lib/A/Prog/diginet_session_init_cgW.v) at image B's values. It holds the caller's journal
   ajournal_gx G_HARNESS_B 0 [] (lib/A/W_journalG.v) from the entry to the return; the runs are the symbolic runs of
   lib/A/Prog/PaShadow.v over that journal (lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x); the stores into
   g_s are allowed by awr_ok_x (a byte of G), the calls of __asan_memset / __asan_memcpy by TransportGCg.v
   gx_intrin_at. The three alignment checks image B adds (io & 7 at 0x86848, cfg & 3 at 0x86880, s & 7 at 0x868e8)
   are decided inside the runs: io's atom carries 2^3 alignment, cfg and s are literals.

     run 1  (+0x00 .. +0x50)  the frame, the saves, the three NULL tests, the io alignment check, and the shadow base
                              through its GOT word;
     run 2  (+0x50 .. +0x68)  the instrumented check of the 8-byte load at io + 8, decided by the shadow entry of
                              [io, io + 32), then `beqz s3` on notify;
     run 3  (notify <> 0)     the load of io->send and `beqz a1` on it;
     runs 4-7 (io->send <> 0) the cfg alignment check, the checks and loads of cfg + 52 and cfg + 56 and the three
                              config tests (max_cmds = 0, 255 < max_cmds, max_body outside [24, 1484]), each a branch;
     __asan_memset (s, 0, 18264), the s alignment check, __asan_memcpy (s, cfg, 60), __asan_memcpy (s + 64, io, 32):
                              gx_intrin_at;
     run 8  (+0x104 .. +0x164) the three checked stores at s + 96, s + 104, s + 112, the check and load of cfg + 12
                              and `beqz a0` on it;
     run 9  (desk_mac_set = 0) the epilogue and `ret`;
     __asan_memcpy (s + 120, cfg + 6, 6) and the last run: the checked store of 1 at s + 116, the epilogue and `ret`.
     Each of the five argument tests that fails runs its own epilogue to `ret` with a0 = -1.

   Every error path is unreached because the token engine decides its instrumented check against the run's shadow
   entry: [io, io + 32), [cfg, cfg + 60), [s, s + 18264). The entries hold at every AR state from trans_sinit_cells /
   trans_scfg_cells and, for io, from DgnTransportBCg.v trans_src_ok_rd.

   The post: transport_cg_post over G_HARNESS_B (sinit_close). On the paths that return DIGINET_E_ARG no byte of G
   changes (tw_kept_GB); on the two that return DIGINET_OK the world is built by one TWorldG.v tw_fill_zero (the memset)
   and tw_upd steps (the memcpys and the stores), and the model's output is the same chain of writes
   (sinit_m_ok0 / sinit_m_ok1). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1i YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_config_default_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_init_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LM := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.

(* ------------------------------------------------------------------ *)
(* The model's world                                                   *)
(* ------------------------------------------------------------------ *)

(* Two adjacent writes, the lower one first: one write of the two spans. *)
Lemma sinit_merge : forall (bs v w : list byte) k j, 0 <= k -> j = k + Z.of_nat (length v) ->
  j + Z.of_nat (length w) <= Z.of_nat (length bs) ->
  TW.upd (TW.upd bs k v) j w = TW.upd bs k (v ++ w).
Proof.
intros bs v w k j Hk -> Hl. apply nth_error_ext. intros i.
assert (L1 : length (TW.upd bs k v) = length bs) by (apply TWL.length_upd; lia).
rewrite (TWL.ne_upd (TW.upd bs k v) w (k + Z.of_nat (length v)) i) by (first [ lia | (rewrite L1; lia) ]).
rewrite (TWL.ne_upd bs v k i) by lia.
rewrite (TWL.ne_upd bs (v ++ w) k i) by (first [ lia | (rewrite length_app; lia) ]).
rewrite length_app, (Z2Nat.inj_add k (Z.of_nat (length v))) by lia. rewrite Nat2Z.id.
repeat match goal with |- context [Nat.leb ?a ?b] => destruct (Nat.leb_spec a b) end;
repeat match goal with |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b) end;
cbn [andb]; try reflexivity; try (exfalso; lia);
first [ (rewrite nth_error_app1 by lia; reflexivity) | (rewrite nth_error_app2 by lia; f_equal; lia) ].
Qed.

(* The model's result, read off without `injection` (which head-normalises the world it is given). *)
Lemma sinit_some_inv : forall (x y : list byte) (u v : Z), Some (x, u) = Some (y, v) -> y = x /\ v = u.
Proof. intros x y u v H. injection H as H1 H2. split; symmetry; assumption. Qed.

(* The 32 bytes of the caller's struct diginet_io, as the model and the statement write them. *)
Definition SINIT_IOB (c s r n : Z) : list byte := TW.put 8 c ++ TW.put 8 s ++ TW.put 8 r ++ TW.put 8 n.

Lemma sinit_len_iob : forall c s r n, Z.of_nat (length (SINIT_IOB c s r n)) = 32.
Proof. intros. unfold SINIT_IOB. rewrite !length_app, !TWL.length_put. reflexivity. Qed.

(* The bytes the code writes into g_s on the path that returns DIGINET_OK and finds no desk MAC: the memset's
   18264 zeros, then g_cfg's 60 bytes, the caller's 32 io bytes at 64, and notify / ctx / state at 96. *)
Definition SINIT_W0 (Bw : list byte) (c s r n nt cx : Z) : list byte :=
  TW.upd (TW.upd (TW.upd (TW.upd Bw TW.OFF_g_s (TW.put (Z.to_nat TW.SZ_g_s) 0))
    TW.OFF_g_s (TW.sub Bw TW.OFF_g_cfg (Z.to_nat TW.SZ_g_cfg)))
    (TW.OFF_g_s + 64) (SINIT_IOB c s r n))
    (TW.OFF_g_s + 96) (TW.put 8 nt ++ TW.put 8 cx ++ TW.put 4 0).
(* With a desk MAC: g_cfg's 6 MAC bytes at 120 and desk_known at 116. *)
Definition SINIT_W1 (Bw : list byte) (c s r n nt cx : Z) : list byte :=
  TW.upd (TW.upd (SINIT_W0 Bw c s r n nt cx) (TW.OFF_g_s + 120) (TW.sub Bw (TW.OFF_g_cfg + 6) 6))
    (TW.OFF_g_s + 116) (TW.put 4 1).

Ltac sinit_len HL :=
  repeat (rewrite TWL.length_upd; [ | lia | rewrite ?length_app, ?TWL.length_put, ?TWL.length_sub; lia ]);
  rewrite ?HL; reflexivity.

(* :58-59, a NULL io->send or a NULL notify. *)
Lemma sinit_m_arg : forall Bw Bw' c s r n nt cx v, s = 0 \/ nt = 0 ->
  TS0.diginet_session_init_m Bw c s r n nt cx = Some (Bw', v) -> Bw' = Bw /\ v = TS0.DIGINET_E_ARG.
Proof.
intros Bw Bw' c s r n nt cx v H Hm. unfold TS0.diginet_session_init_m in Hm.
replace ((s =? 0) || (nt =? 0))%bool with true in Hm.
- exact (sinit_some_inv _ _ _ _ Hm).
- symmetry. apply Bool.orb_true_iff. destruct H as [Hs | Hn]; [left; rewrite Hs | right; rewrite Hn];
    apply Z.eqb_refl.
Qed.

(* :60-62, a config out of range. *)
Lemma sinit_m_cfg : forall Bw Bw' c s r n nt cx v,
  TW.Cfg_max_cmds Bw = 0 \/ 255 < TW.Cfg_max_cmds Bw \/ TW.Cfg_max_body Bw < 24 \/ 1484 < TW.Cfg_max_body Bw ->
  TS0.diginet_session_init_m Bw c s r n nt cx = Some (Bw', v) -> Bw' = Bw /\ v = TS0.DIGINET_E_ARG.
Proof.
intros Bw Bw' c s r n nt cx v H Hm. unfold TS0.diginet_session_init_m in Hm.
destruct ((s =? 0) || (nt =? 0))%bool; [exact (sinit_some_inv _ _ _ _ Hm)|].
replace ((TW.Cfg_max_cmds Bw =? 0) || (TW.Cfg_max_body Bw <? TS0.DIGINET_CMD_MAX_LEN)
         || (TS0.DIGINET_MAX_BODY_LEN <? TW.Cfg_max_body Bw) || (255 <? TW.Cfg_max_cmds Bw))%bool with true in Hm.
- exact (sinit_some_inv _ _ _ _ Hm).
- symmetry. unfold TS0.DIGINET_CMD_MAX_LEN, TS0.DIGINET_MAX_BODY_LEN.
  destruct H as [H|[H|[H|H]]].
  + apply Bool.orb_true_iff; left. apply Bool.orb_true_iff; left.
    apply Bool.orb_true_iff; left. apply Z.eqb_eq. exact H.
  + apply Bool.orb_true_iff; right. apply Z.ltb_lt. exact H.
  + apply Bool.orb_true_iff; left. apply Bool.orb_true_iff; left.
    apply Bool.orb_true_iff; right. apply Z.ltb_lt. exact H.
  + apply Bool.orb_true_iff; left. apply Bool.orb_true_iff; right. apply Z.ltb_lt. exact H.
Qed.

Ltac sinit_nz Hm :=
  replace ((_ =? 0) || (_ =? 0))%bool with false in Hm
    by (symmetry; apply Bool.orb_false_iff; split; apply Z.eqb_neq; assumption);
  replace ((TW.Cfg_max_cmds _ =? 0) || (TW.Cfg_max_body _ <? TS0.DIGINET_CMD_MAX_LEN)
           || (TS0.DIGINET_MAX_BODY_LEN <? TW.Cfg_max_body _) || (255 <? TW.Cfg_max_cmds _))%bool with false in Hm
    by (symmetry; unfold TS0.DIGINET_CMD_MAX_LEN, TS0.DIGINET_MAX_BODY_LEN;
        apply Bool.orb_false_iff; split;
        [ apply Bool.orb_false_iff; split;
          [ apply Bool.orb_false_iff; split; [apply Z.eqb_neq; assumption | apply Z.ltb_ge; lia]
          | apply Z.ltb_ge; lia ]
        | apply Z.ltb_ge; lia ]).

(* The model writes the four io fields and notify / ctx / state one by one; the walk writes the io block in one
   memcpy and the three fields in one run. The two agree: adjacent writes are one write of their bytes. *)
Lemma sinit_pack : forall (bs : list byte) k (c s r n nt cx : Z),
  0 <= k -> k + 116 <= Z.of_nat (length bs) ->
  TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd bs (k + 64) (TW.put 8 c)) (k + 72) (TW.put 8 s))
      (k + 80) (TW.put 8 r)) (k + 88) (TW.put 8 n)) (k + 96) (TW.put 8 nt)) (k + 104) (TW.put 8 cx))
      (k + 112) (TW.put 4 0)
  = TW.upd (TW.upd bs (k + 64) (SINIT_IOB c s r n)) (k + 96) (TW.put 8 nt ++ TW.put 8 cx ++ TW.put 4 0).
Proof.
intros bs k c s r n nt cx Hk Hl.
rewrite (sinit_merge bs (TW.put 8 c) (TW.put 8 s) (k + 64) (k + 72))
  by (rewrite ?TWL.length_put; lia).
rewrite (sinit_merge bs (TW.put 8 c ++ TW.put 8 s) (TW.put 8 r) (k + 64) (k + 80))
  by (rewrite ?length_app, ?TWL.length_put; lia).
rewrite (sinit_merge bs ((TW.put 8 c ++ TW.put 8 s) ++ TW.put 8 r) (TW.put 8 n) (k + 64) (k + 88))
  by (rewrite ?length_app, ?TWL.length_put; lia).
rewrite <- !app_assoc.
fold (SINIT_IOB c s r n).
assert (LB : Z.of_nat (length (TW.upd bs (k + 64) (SINIT_IOB c s r n))) = Z.of_nat (length bs))
  by (rewrite TWL.length_upd; [reflexivity | lia | rewrite sinit_len_iob; lia]).
rewrite (sinit_merge (TW.upd bs (k + 64) (SINIT_IOB c s r n)) (TW.put 8 nt) (TW.put 8 cx) (k + 96) (k + 104))
  by (rewrite ?LB, ?TWL.length_put; lia).
rewrite (sinit_merge (TW.upd bs (k + 64) (SINIT_IOB c s r n)) (TW.put 8 nt ++ TW.put 8 cx) (TW.put 4 0)
  (k + 96) (k + 112)) by (rewrite ?LB, ?length_app, ?TWL.length_put; lia).
rewrite <- !app_assoc. reflexivity.
Qed.

(* The lengths of what the memset and the first memcpy write, and the world's length through them. *)
Lemma sinit_lput : Z.of_nat (length (TW.put (Z.to_nat TW.SZ_g_s) 0)) = 18264.
Proof. rewrite TWL.length_put. rewrite Z2Nat.id by (unfold TW.SZ_g_s; lia). reflexivity. Qed.

Lemma sinit_lsub : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  Z.of_nat (length (TW.sub Bw TW.OFF_g_cfg (Z.to_nat TW.SZ_g_cfg))) = 60.
Proof.
intros Bw HL. rewrite TWL.length_sub.
- rewrite Z2Nat.id by (unfold TW.SZ_g_cfg; lia). reflexivity.
- unfold TW.OFF_g_cfg; lia.
- rewrite Z2Nat.id by (unfold TW.SZ_g_cfg; lia). rewrite HL.
  unfold TW.OFF_g_cfg, TW.SZ_g_cfg, TW.W_LEN; lia.
Qed.

Lemma sinit_l1 : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  Z.of_nat (length (TW.upd Bw TW.OFF_g_s (TW.put (Z.to_nat TW.SZ_g_s) 0))) = TW.W_LEN.
Proof.
intros Bw HL. rewrite TWL.length_upd;
  [ exact HL | unfold TW.OFF_g_s; lia
  | rewrite sinit_lput, HL; unfold TW.OFF_g_s, TW.W_LEN; lia ].
Qed.

Lemma sinit_l2 : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  Z.of_nat (length (TW.upd (TW.upd Bw TW.OFF_g_s (TW.put (Z.to_nat TW.SZ_g_s) 0)) TW.OFF_g_s
    (TW.sub Bw TW.OFF_g_cfg (Z.to_nat TW.SZ_g_cfg)))) = TW.W_LEN.
Proof.
intros Bw HL. rewrite TWL.length_upd;
  [ exact (sinit_l1 Bw HL) | unfold TW.OFF_g_s; lia
  | rewrite (sinit_lsub Bw HL), (sinit_l1 Bw HL); unfold TW.OFF_g_s, TW.W_LEN; lia ].
Qed.

(* :63-68 and :74 with no desk MAC. *)
Lemma sinit_m_ok0 : forall Bw Bw' c s r n nt cx v, Z.of_nat (length Bw) = TW.W_LEN ->
  s <> 0 -> nt <> 0 -> TW.Cfg_max_cmds Bw <> 0 -> TW.Cfg_max_cmds Bw <= 255 ->
  24 <= TW.Cfg_max_body Bw -> TW.Cfg_max_body Bw <= 1484 -> TW.Cfg_desk_mac_set Bw = 0 ->
  TS0.diginet_session_init_m Bw c s r n nt cx = Some (Bw', v) ->
  Bw' = SINIT_W0 Bw c s r n nt cx /\ v = DL.DIGINET_OK.
Proof.
intros Bw Bw' c s r n nt cx v HL Hs Hnt H1 H2 H3 H4 Hd Hm.
unfold TS0.diginet_session_init_m in Hm. sinit_nz Hm.
cbv zeta in Hm.
replace (TW.Cfg_desk_mac_set Bw =? 0) with true in Hm by (symmetry; apply Z.eqb_eq; exact Hd).
cbn [negb] in Hm.
unfold TW.set_S_state, TW.set_S_notify_ctx, TW.set_S_notify, TW.set_S_io_now_us, TW.set_S_io_recv,
  TW.set_S_io_send, TW.set_S_io_ctx, TW.A_S_state, TW.A_S_notify_ctx, TW.A_S_notify, TW.A_S_io_now_us,
  TW.A_S_io_recv, TW.A_S_io_send, TW.A_S_io_ctx, TW.A_S_cfg_host_mac, TS0.DIGINET_S_IDLE in Hm.
destruct (sinit_some_inv _ _ _ _ Hm) as [EB Ev]. split; [|exact Ev]. rewrite EB.
change (TW.OFF_g_s + 0 + 0) with TW.OFF_g_s.
change (TW.OFF_g_s + 64 + 0) with (TW.OFF_g_s + 64).
change (TW.OFF_g_s + 64 + 8) with (TW.OFF_g_s + 72).
change (TW.OFF_g_s + 64 + 16) with (TW.OFF_g_s + 80).
change (TW.OFF_g_s + 64 + 24) with (TW.OFF_g_s + 88).
pose proof (sinit_l2 Bw HL) as L2.
rewrite sinit_pack by (rewrite ?L2; unfold TW.OFF_g_s, TW.W_LEN; lia).
reflexivity.
Qed.

(* :63-71 and :74 with a desk MAC. *)
Lemma sinit_m_ok1 : forall Bw Bw' c s r n nt cx v, Z.of_nat (length Bw) = TW.W_LEN ->
  s <> 0 -> nt <> 0 -> TW.Cfg_max_cmds Bw <> 0 -> TW.Cfg_max_cmds Bw <= 255 ->
  24 <= TW.Cfg_max_body Bw -> TW.Cfg_max_body Bw <= 1484 -> TW.Cfg_desk_mac_set Bw <> 0 ->
  TS0.diginet_session_init_m Bw c s r n nt cx = Some (Bw', v) ->
  Bw' = SINIT_W1 Bw c s r n nt cx /\ v = DL.DIGINET_OK.
Proof.
intros Bw Bw' c s r n nt cx v HL Hs Hnt H1 H2 H3 H4 Hd Hm.
unfold TS0.diginet_session_init_m in Hm. sinit_nz Hm.
cbv zeta in Hm.
replace (TW.Cfg_desk_mac_set Bw =? 0) with false in Hm by (symmetry; apply Z.eqb_neq; exact Hd).
cbn [negb] in Hm.
unfold TW.set_S_desk_known, TW.set_S_desk_mac, TW.set_S_state, TW.set_S_notify_ctx, TW.set_S_notify,
  TW.set_S_io_now_us, TW.set_S_io_recv, TW.set_S_io_send, TW.set_S_io_ctx, TW.A_S_desk_known, TW.A_S_desk_mac,
  TW.A_S_state, TW.A_S_notify_ctx, TW.A_S_notify, TW.A_S_io_now_us, TW.A_S_io_recv, TW.A_S_io_send,
  TW.A_S_io_ctx, TW.A_S_cfg_host_mac, TW.Cfg_desk_mac, TW.A_Cfg_desk_mac, TS0.DIGINET_S_IDLE in Hm.
destruct (sinit_some_inv _ _ _ _ Hm) as [EB Ev]. split; [|exact Ev]. rewrite EB.
change (TW.OFF_g_s + 0 + 0) with TW.OFF_g_s.
change (TW.OFF_g_s + 64 + 0) with (TW.OFF_g_s + 64).
change (TW.OFF_g_s + 64 + 8) with (TW.OFF_g_s + 72).
change (TW.OFF_g_s + 64 + 16) with (TW.OFF_g_s + 80).
change (TW.OFF_g_s + 64 + 24) with (TW.OFF_g_s + 88).
pose proof (sinit_l2 Bw HL) as L2.
rewrite sinit_pack by (rewrite ?L2; unfold TW.OFF_g_s, TW.W_LEN; lia).
reflexivity.
Qed.


Lemma sinit_u4 : forall bs kk, 0 <= TW.u_at bs kk 4 < 2 ^ 32.
Proof.
intros bs kk. pose proof (TWL.u_at_range bs kk 4) as HR.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in HR. exact HR.
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the entry                                     *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the entry, 32 the shadow base, 33 io->send, 34 cfg->desk_mac_set,
   35 cfg->max_cmds, 36 cfg->max_body (each a 4-byte field, held as its unsigned value). *)
Definition SINIT_IO_REG : YP09.region :=
  YP09.mkRegion (Some 12%nat) 0 32 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 33%nat 0))].
Definition SINIT_CFG_REG : YP09.region := YP09.mkRegion (Some 11%nat) 0 60 0 0
  [YP09.mkChunk 12 (CVal 4 (SOff 34%nat 0)); YP09.mkChunk 52 (CVal 4 (SOff 35%nat 0));
   YP09.mkChunk 56 (CVal 4 (SOff 36%nat 0))].
(* The bytes the three checked stores write, [s + 96, s + 120); the memcpys write through gx_intrin_at. *)
Definition SINIT_S_REG : YP09.region := YP09.mkRegion (Some 10%nat) 96 116 96 116 [].
(* The byte of desk_known, written only when cfg->desk_mac_set is not 0. *)
Definition SINIT_S2_REG : YP09.region := YP09.mkRegion (Some 10%nat) 116 120 116 120 [].
Definition SINIT_REGS : smem := [stack_region SINIT_FRAME; got_regionP; bcell_regionP 32].
Definition SINIT_FACTS : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF SINIT_S SINIT_S 4);
           (11%nat, mkAF SINIT_CFG SINIT_CFG 4); (12%nat, mkAF 1 (2 ^ 47 - 32) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition SINIT_SS : sstate := mkSS AF_diginet_session_init sr_atoms SINIT_REGS None SINIT_FACTS.
Definition SINIT_BX : sv := SOff 32%nat 0.
Definition SINIT_SH0 : list shent := [].
Definition SINIT_SHIO : list shent := [mkSHE 12%nat 0 32].
Definition SINIT_SHCFG : list shent := [mkSHE 11%nat 0 60].
Definition SINIT_SHSC : list shent := [mkSHE 10%nat 0 18264; mkSHE 11%nat 0 60].
(* The pc after the two loads that bring the shadow base into s5. *)
Definition SINIT_GOT_STOP : Z := AF_diginet_session_init + 0x50.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac sinit_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "sinit_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac sinit_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The region i of a symbolic state HS, its value computed. *)
Ltac sinit_rgn HS i H :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx ?msx =>
      let rr := eval vm_compute in (nth_error (ss_mem ssx) i) in
      lazymatch rr with
      | Some ?r => pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as H
      end
  end.

(* Keep only the regions idxs of a state (the two image cells are needed for the shadow base alone). *)
Ltac sinit_keep HS idxs HS2 :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx ?msx =>
      let rs := eval vm_compute in (pick (ss_mem ssx) idxs) in
      pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(submem_tac) ltac:(vm_compute; reflexivity)) as HS2;
      cbn [ss_pc ss_regs ss_resv ss_facts] in HS2
  end.

(* g_s's and g_cfg's payload bytes are bytes of G. *)
Lemma sinit_inG_s : forall a, SINIT_S <= a < SINIT_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr; cbn [fst snd]; unfold SINIT_S in Ha; lia].
Qed.

Lemma sinit_inG_cfg : forall a, SINIT_CFG <= a < SINIT_CFG + TW.SZ_g_cfg -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TB_g_cfg, TW.SZ_g_cfg).
split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_cfg) | unfold in_zr; cbn [fst snd]; unfold SINIT_CFG in Ha; lia].
Qed.

(* A 4-byte field loaded by `lw`: the sign extension of its unsigned value. *)
Lemma sinit_lw : forall v, 0 <= v < 2 ^ 64 ->
  sext 64 (bv_extract 0 32 (Z_to_bv 64 v)) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
intros v Hv. rewrite LM.sext_small, LM.signed_of_extract by lia. rewrite Z_to_bv_unsigned.
rewrite bv_wrap_small by (unfold bv_modulus; change (Z.of_N 64) with 64; lia). reflexivity.
Qed.

(* The world's length through the four writes of the OK path, and g_cfg's desk MAC read off it. *)
Lemma sinit_l3 : forall Bw0 c s0 r0 n0, Z.of_nat (length Bw0) = TW.W_LEN ->
  Z.of_nat (length (TW.upd (TW.upd (TW.upd Bw0 TW.OFF_g_s (TW.put (Z.to_nat TW.SZ_g_s) 0)) TW.OFF_g_s
    (TW.sub Bw0 TW.OFF_g_cfg (Z.to_nat TW.SZ_g_cfg))) (TW.OFF_g_s + 64) (SINIT_IOB c s0 r0 n0)))
  = TW.W_LEN.
Proof.
intros Bw0 c s0 r0 n0 HL. rewrite TWL.length_upd;
  [ exact (sinit_l2 Bw0 HL) | unfold TW.OFF_g_s; lia
  | rewrite sinit_len_iob, (sinit_l2 Bw0 HL); unfold TW.OFF_g_s, TW.W_LEN; lia ].
Qed.

Lemma sinit_l4 : forall Bw0 c s0 r0 n0 nt cx, Z.of_nat (length Bw0) = TW.W_LEN ->
  Z.of_nat (length (SINIT_W0 Bw0 c s0 r0 n0 nt cx)) = TW.W_LEN.
Proof.
intros Bw0 c s0 r0 n0 nt cx HL. unfold SINIT_W0.
rewrite TWL.length_upd;
  [ exact (sinit_l3 Bw0 c s0 r0 n0 HL) | unfold TW.OFF_g_s; lia
  | rewrite !length_app, !TWL.length_put, (sinit_l3 Bw0 c s0 r0 n0 HL);
    unfold TW.OFF_g_s, TW.W_LEN; lia ].
Qed.

Lemma sinit_sub_W0 : forall Bw0 c s0 r0 n0 nt cx, Z.of_nat (length Bw0) = TW.W_LEN ->
  TW.sub (SINIT_W0 Bw0 c s0 r0 n0 nt cx) (TW.OFF_g_cfg + 6) 6 = TW.sub Bw0 (TW.OFF_g_cfg + 6) 6.
Proof.
intros Bw0 c s0 r0 n0 nt cx HL. unfold SINIT_W0.
rewrite TWL.sub_upd_out;
  [ | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_cfg; lia
  | rewrite !length_app, !TWL.length_put; right; unfold TW.OFF_g_s, TW.OFF_g_cfg; lia
  | rewrite !length_app, !TWL.length_put, (sinit_l3 Bw0 c s0 r0 n0 HL);
    unfold TW.OFF_g_s, TW.W_LEN; lia ].
rewrite TWL.sub_upd_out;
  [ | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_cfg; lia
  | rewrite sinit_len_iob; right; unfold TW.OFF_g_s, TW.OFF_g_cfg; lia
  | rewrite sinit_len_iob, (sinit_l2 Bw0 HL); unfold TW.OFF_g_s, TW.W_LEN; lia ].
rewrite TWL.sub_upd_out;
  [ | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_cfg; lia
  | rewrite (sinit_lsub Bw0 HL); right; unfold TW.OFF_g_s, TW.OFF_g_cfg; lia
  | rewrite (sinit_lsub Bw0 HL), (sinit_l1 Bw0 HL); unfold TW.OFF_g_s, TW.W_LEN; lia ].
rewrite TWL.sub_upd_out;
  [ reflexivity | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_cfg; lia
  | rewrite sinit_lput; right; unfold TW.OFF_g_s, TW.OFF_g_cfg; lia
  | rewrite sinit_lput, HL; unfold TW.OFF_g_s, TW.W_LEN; lia ].
Qed.


(* ------------------------------------------------------------------ *)
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

Section sinitw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma sinit_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  BASE + AF_diginet_session_init = transportb_sigma TB_diginet_session_init.
Proof. vm_compute. repeat split. Qed.

(* The two image regions hold what transport_cells says they hold, at any AR state. *)
Lemma sinit_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H W) mem) got_regionP /\ region_ok segs E (mrestrict (w_H W) mem) (bcell_regionP 32).
Proof.
  intros ly S W mem md E HCELLS HAR E1 E95 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct sinit_vals as (V1 & V95 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  assert (R95 : 0 <= VAL (A_OBJ 95) < 2 ^ 47) by (rewrite V95; unfold FCells.CELL_K; lia).
  unfold got_regionP, bcell_regionP, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split.
  - rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 95) 0) (VAL (A_OBJ 95)));
    [cbn [sv_denot]; rewrite E95, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r, V1, V95. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E95) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 95)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r, V95. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
Qed.

(* g_cfg's 60 bytes are addressable at every AR state: the shadow of its 7 whole granules is 0, the shadow of its
   last granule is 4 (a constant cell of the record). *)
Lemma sinit_cfg_ra : forall ly S (W : world segs) mem md,
  trans_scfg_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF SINIT_CFG 60.
Proof.
intros ly S W mem md [HZ HC] HAR x Hx.
assert (EC : SINIT_CFG = 6155520) by reflexivity.
assert (ECC : SCFG_C = 6155520) by reflexivity.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
rewrite EC in Hx. unfold shadow_of_addr.
destruct (Z_lt_le_dec x (SCFG_C + 56)) as [Hlt|Hge].
- exists 0. split; [|left; reflexivity].
  assert (Hz := decode_zshadow_rd B ly S W mem md SCFG_C (SCFG_C + 56) (8 * (x / 8)) HAR
    ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
  replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
  unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
- exists 4. split; [|right; split; lia].
  specialize (HC ly). destruct HAR as (Mm & _).
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mm) _ HC) as Hh.
  unfold cell_holds in Hh. cbn [c_at c_w YG0f.c_val z1 c1 aeval] in Hh.
  specialize (Hh 0%nat ltac:(lia)). cbn [Z.of_nat] in Hh. rewrite Z.add_0_r in Hh.
  change (le_byte 4 1 0) with 4 in Hh.
  replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (SCFG_C + 56)); [exact Hh|].
  unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF.
  replace ((SCFG_C + 56) / 8) with 769447 by (rewrite ECC; reflexivity). lia.
Qed.

(* g_s's 18264 bytes are addressable: 2283 whole granules, all of zero shadow. *)
Lemma sinit_s_ra : forall ly S (W : world segs) mem md,
  trans_sinit_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF SINIT_S TW.SZ_g_s.
Proof.
intros ly S W mem md [HZ _] HAR x Hx.
assert (EC : SINIT_S = 6157888) by reflexivity.
assert (ES : SINIT_S + TW.SZ_g_s = 6176152) by reflexivity.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold shadow_of_addr.
exists 0. split; [|left; reflexivity].
assert (Hz := decode_zshadow_rd B ly S W mem md SINIT_S (SINIT_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The shadow bytes of g_cfg's payload are visible. *)
Lemma sinit_vis_cfg : forall ly S (W : world segs) mem md s,
  trans_scfg_cells B -> @AR rc segs B ly S W mem md ->
  2148220320 <= s < 2148220328 -> aview segs (w_H W) mem s <> None.
Proof.
intros ly S W mem md s HSC HAR Hs.
assert (Hx : SINIT_CFG <= 8 * (s - SHADOW_OFF) < SINIT_CFG + 60)
  by (unfold SINIT_CFG, TB_g_cfg, SHADOW_OFF; lia).
destruct (sinit_cfg_ra ly S W mem md HSC HAR _ Hx) as (v & Hv & _).
unfold shadow_of_addr in Hv.
replace (SHADOW_OFF + 8 * (s - SHADOW_OFF) / 8) with s in Hv
  by (rewrite Z.mul_comm, Z.div_mul by lia; lia).
rewrite Hv. discriminate.
Qed.

(* The shadow bytes of g_s's payload, and the five guard bytes after them, are visible. *)
Lemma sinit_vis_s : forall ly S (W : world segs) mem md s,
  trans_sinit_cells B -> @AR rc segs B ly S W mem md ->
  2148220616 <= s < 2148222904 -> aview segs (w_H W) mem s <> None.
Proof.
intros ly S W mem md s HSC HAR Hs.
destruct (Z_lt_le_dec s 2148222899) as [Hlt|Hge].
- assert (Hx : SINIT_S <= 8 * (s - SHADOW_OFF) < SINIT_S + TW.SZ_g_s)
    by (unfold SINIT_S, TB_g_s, TW.SZ_g_s, SHADOW_OFF; lia).
  destruct (sinit_s_ra ly S W mem md HSC HAR _ Hx) as (v & Hv & _).
  unfold shadow_of_addr in Hv.
  replace (SHADOW_OFF + 8 * (s - SHADOW_OFF) / 8) with s in Hv
    by (rewrite Z.mul_comm, Z.div_mul by lia; lia).
  rewrite Hv. discriminate.
- destruct HSC as [_ HC]. specialize (HC ly (s - 2148222899) ltac:(lia)). destruct HAR as (Mm & _).
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mm) _ HC) as Hh.
  unfold cell_holds in Hh. cbn [c_at c_w YG0f.c_val z1 c1 aeval] in Hh.
  specialize (Hh 0%nat ltac:(lia)). cbn [Z.of_nat] in Hh. rewrite Z.add_0_r in Hh.
  assert (EH : FCells.shadow_addr (SINIT_S + TW.SZ_g_s) = 2148222899) by reflexivity.
  rewrite EH in Hh. replace (2148222899 + (s - 2148222899)) with s in Hh by lia.
  rewrite Hh. discriminate.
Qed.

(* The shadow hull of a range of g_cfg, and of a range of g_s, is visible (the bounds are closed numerals). *)
Lemma sinit_hull_cfg : forall ly S (W : world segs) mem md a n,
  trans_scfg_cells B -> @AR rc segs B ly S W mem md ->
  2148220320 <= shadow_addr a / 8 * 8 -> shadow_addr (a + n - 1) / 8 * 8 + 8 <= 2148220328 ->
  shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof. intros ly S W mem md a n HSC HAR H1 H2 s Hs. apply (sinit_vis_cfg ly S W mem md s HSC HAR). lia. Qed.

Lemma sinit_hull_s : forall ly S (W : world segs) mem md a n,
  trans_sinit_cells B -> @AR rc segs B ly S W mem md ->
  2148220616 <= shadow_addr a / 8 * 8 -> shadow_addr (a + n - 1) / 8 * 8 + 8 <= 2148222904 ->
  shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof. intros ly S W mem md a n HSC HAR H1 H2 s Hs. apply (sinit_vis_s ly S W mem md s HSC HAR). lia. Qed.

(* The walk's valuation: the 32 registers at the entry, the shadow base, and the four fields it loads. *)
Definition sinit_E (regs : bvmap 5 word) (iosend dmac mcmds mbody : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF; w64 iosend; w64 dmac; w64 mcmds; w64 mbody]).

(* The shadow entries hold: g_cfg's and g_s's from the record, the caller's io block from decode_rd_ok. *)
Lemma sinit_shok_io : forall (W : world segs) memc (E : env) iop,
  decode_rd_ok W memc iop 32 -> ew E 12 = Z_to_bv 64 iop -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs SINIT_BX SINIT_SHIO E (mrestrict (w_H W) memc).
Proof.
intros W memc E iop (_ & HRA & _ & HAM & H0 & H63) E12 E32.
unfold sh_ok, SINIT_SHIO. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H W) memc E SINIT_BX 12 iop 32 iop 0 32 HRA).
- unfold U, SINIT_BX. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in HAM.
  unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
Qed.

Lemma sinit_shok_cfg : forall ly S (W : world segs) mem md (E : env),
  trans_scfg_cells B -> @AR rc segs B ly S W mem md ->
  ew E 11 = Z_to_bv 64 SINIT_CFG -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs SINIT_BX SINIT_SHCFG E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E HSC HAR E11 E32.
unfold sh_ok, SINIT_SHCFG. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H W) mem E SINIT_BX 11 SINIT_CFG 60 SINIT_CFG 0 60
  (sinit_cfg_ra ly S W mem md HSC HAR)).
- unfold U, SINIT_BX. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned.
  apply unsigned_lit_small. unfold SINIT_CFG, TB_g_cfg; lia.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SINIT_CFG, TB_g_cfg, SHADOW_OFF in *. lia.
Qed.

Lemma sinit_shok_sc : forall ly S (W : world segs) mem md (E : env),
  trans_scfg_cells B -> trans_sinit_cells B -> @AR rc segs B ly S W mem md ->
  ew E 10 = Z_to_bv 64 SINIT_S -> ew E 11 = Z_to_bv 64 SINIT_CFG -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs SINIT_BX SINIT_SHSC E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E HSC HSI HAR E10 E11 E32.
unfold sh_ok, SINIT_SHSC. constructor; [|exact (sinit_shok_cfg ly S W mem md E HSC HAR E11 E32)].
apply (shent_ok_of_range segs (w_H W) mem E SINIT_BX 10 SINIT_S TW.SZ_g_s SINIT_S 0 18264
  (sinit_s_ra ly S W mem md HSI HAR)).
- unfold U, SINIT_BX. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
  apply unsigned_lit_small. unfold SINIT_S, TB_g_s; lia.
- lia.
- unfold TW.SZ_g_s; lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SINIT_S, TB_g_s, SHADOW_OFF in *. lia.
Qed.

(* The entry state: the frame below sp, the shadow base's GOT word and its cell. *)
Lemma sinit_entry : forall ly S (W : world segs) regs mem md iosend dmac mcmds mbody iop,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - SINIT_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  YK11.getr regs 10 = w64 SINIT_S -> YK11.getr regs 11 = w64 SINIT_CFG -> YK11.getr regs 12 = w64 iop ->
  1 <= iop <= 2 ^ 47 - 32 -> iop mod 8 = 0 ->
  st_ok_pi segs VAL (sinit_E regs iosend dmac mcmds mbody) SINIT_SS
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_init)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md iosend dmac mcmds mbody iop HCELLS HAR Hpres Hsp Hsp16 H10 H11 H12 Hio Hio8.
  set (E0 := sinit_E regs iosend dmac mcmds mbody).
  assert (ES : SINIT_S = 6157888) by reflexivity.
  assert (EC : SINIT_CFG = 6155520) by reflexivity.
  assert (Er2 : ew E0 2 = YK11.getr regs 2) by (unfold E0, sinit_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite Er2; reflexivity).
  assert (E10 : ew E0 10 = Z_to_bv 64 SINIT_S)
    by (unfold E0, sinit_E; rewrite (ew_Eimg_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (U10 : bv_unsigned (ew E0 10) = SINIT_S) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (E11 : ew E0 11 = Z_to_bv 64 SINIT_CFG)
    by (unfold E0, sinit_E; rewrite (ew_Eimg_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (U11 : bv_unsigned (ew E0 11) = SINIT_CFG) by (rewrite E11; apply unsigned_lit_small; lia).
  assert (E12 : ew E0 12 = Z_to_bv 64 iop)
    by (unfold E0, sinit_E; rewrite (ew_Eimg_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (U12 : bv_unsigned (ew E0 12) = iop) by (rewrite E12; apply unsigned_lit_small; lia).
  assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E0, sinit_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (EOB : forall j, (j < 100)%nat -> ew E0 (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E0, sinit_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct (sinit_img_ok ly S W mem md E0 HCELLS HAR (EOB 1%nat ltac:(lia)) (EOB 95%nat ltac:(lia)) E32)
    as [RG RC].
  destruct sinit_vals as (V1 & V95 & _).
  assert (VB : forall n v0, ew E0 n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E0 (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  rewrite restrict_mkst_fx. unfold SINIT_SS, SINIT_REGS.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [exact RG | apply Forall_cons; [exact RC | apply Forall_nil]]].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold SINIT_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (EOB 95%nat ltac:(lia))) by (rewrite V95; unfold FCells.CELL_K; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V95. unfold FCells.GOT_CELL_K, FCells.CELL_K, SINIT_FRAME in *.
    repeat split; first [exact I | lia].
  + unfold SINIT_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U10, U11, U12, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite ES; reflexivity
      | rewrite EC; reflexivity].
Qed.

(* The walk's valuation agrees with the entry registers below atom 32. *)
Lemma sinit_agree : forall regs iosend dmac mcmds mbody E,
  (forall n, (n < 32)%nat -> ew E n = ew (sinit_E regs iosend dmac mcmds mbody) n) ->
  ed E = ed (sinit_E regs iosend dmac mcmds mbody) ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF; w64 iosend; w64 dmac; w64 mcmds; w64 mbody]) E.
Proof.
  intros regs iosend dmac mcmds mbody E H1 H2. split.
  - intros n Hn. rewrite (H1 n Hn). unfold sinit_E. apply Eimg_low. unfold A_TEXT. lia.
  - rewrite H2. reflexivity.
Qed.

(* The post at the return, from the walk's last facts. *)
Lemma sinit_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs
    (r : Z) (Bw' : list byte) regsF mF mdF,
  AR_laws segs B -> ameter_laws MT -> gx_ok segs B TG.G_HARNESS_B ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - SINIT_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - SINIT_STK -> spZ regs <= 2 ^ 47 ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mF mdF k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SINIT_STK <= a < spZ regs) -> ~ sinit_wr r a ->
     aview segs (w_H W) mF a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mF a) ->
  tw_at TMAP_B (aview segs (w_H W) mF) Bw' ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 -> YK11.getr regsF 10 = w64 r ->
  forall mat, @transport_sinit_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw' r W
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r Bw' regsF mF mdF
    LAWS MTL HGX HAR Hwin Hce Hsp47 Hra HJF KA GA HTW HP RF1 RF10 mat.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : SINIT_STK = 4160) by reflexivity.
  assert (ES : SINIT_S = 6157888) by reflexivity.
  assert (ESZ : TW.SZ_g_s = 18264) by reflexivity.
  assert (GLOW : forall a, inG TG.G_HARNESS_B a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (transportb_segs_low a (proj1 (HGX a Ha)))).
  unfold transport_sinit_post, transport_cg_post.
  exists lyc, Sc, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
  split.
  { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [unfold SINIT_EV; lia|].
  split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc mF
      (spZ regs - SINIT_STK) (spZ regs) (sinit_wr r)
      (fun a => (spZ regs - SINIT_STK <= a < spZ regs) \/ sinit_wr r a) HAR).
    - apply dk_kept_refl_g. exact Hwin.
    - intros a Ha Hn. apply KA; [exact Ha | intros H; apply Hn; left; exact H
        | intros H; apply Hn; right; exact H].
    - exact GA.
    - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso. destruct Hw as [_ Hw]. lia.
    - intros b m i Hb Hi [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
    - intros a [Hw | Hw] Hi HnG _ _.
      + pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
      + apply HnG. apply sinit_inG_s. destruct Hw as [_ Hw]. lia.
    - intros cid pos a Hin Hr' [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      destruct Hr' as [Hr' | Hr']; unfold in_zr, frame_rng in Hr'; cbn [fst snd] in Hr'; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  split; [exact RF10 | exact HTW].
Qed.

(* The write rights of a run: the frame below sp (inside the caller's stack window), a read-only region (no
   writable byte) and [s + 96, s + 120) (bytes of G). *)
Ltac sinit_hb :=
  match goal with
  | |- ?x <= ?y => let a := eval vm_compute in x in let b := eval vm_compute in y in
       change x with a; change y with b; lia
  end.
Ltac sinit_awr_norm :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
Ltac sinit_awr_stack UspE :=
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    repeat rewrite ew_havoc_old in Ha by lia; repeat rewrite ew_ewset_other in Ha by lia; rewrite UspE in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
Ltac sinit_awr_ro :=
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
Ltac sinit_awr_g U10E :=
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    repeat rewrite ew_havoc_old in Ha by lia; repeat rewrite ew_ewset_other in Ha by lia; rewrite U10E in Ha;
    apply sinit_inG_s; unfold TW.SZ_g_s; lia |].

(* io->send, the 8 bytes at io + 8 of the caller's struct. *)
Lemma sinit_io_val : forall (W : world segs) memc iop c s r n,
  YI00.garr8 segs (mrestrict (w_H W) memc) iop (TW.zs (sinit_io_bytes c s r n)) ->
  YI04.val_mem segs (mrestrict (w_H W) memc) (iop + 8) 8 s.
Proof.
intros W memc iop c s r n HG j Hj.
assert (L1 : length (TW.put 8 c) = 8%nat) by apply TWL.length_put.
assert (LL : length (TW.zs (sinit_io_bytes c s r n)) = 32%nat)
  by (unfold TW.zs; rewrite length_map; unfold sinit_io_bytes; rewrite !length_app, !TWL.length_put; reflexivity).
pose proof (YI00.garr8_mbyte segs (mrestrict (w_H W) memc) iop _ (8 + j)%nat HG ltac:(lia)) as Hb.
replace (iop + Z.of_nat (8 + j)) with (iop + 8 + Z.of_nat j) in Hb by lia.
rewrite Hb. f_equal. f_equal.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite LL; lia).
unfold TW.zs. rewrite map_nth. unfold sinit_io_bytes.
rewrite app_nth2 by lia. rewrite L1. replace (8 + j - 8)%nat with j by lia.
rewrite app_nth1 by (rewrite TWL.length_put; lia).
apply tw_le_byte_put. lia.
Qed.

(* The io block's read facts carried to a later memory: its bytes and the whole shadow band are kept. *)
Lemma sinit_rd_kept : forall (W : world segs) m m' q n, 0 < n -> 0 <= q -> q + n <= 2 ^ 47 ->
  decode_rd_ok W m q n ->
  (forall a, q <= a < q + n -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  (forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 + 8 -> aview segs (w_H W) m' s = aview segs (w_H W) m s) ->
  decode_rd_ok W m' q n.
Proof.
intros W m m' q n Hn Hq Hq47 (Hv & Hra & Hh & Ham & H0 & H63) Hb Hs.
assert (SB : forall y, 0 <= y -> y + 1 <= 2 ^ 47 -> SHADOW_OFF <= shadow_addr y < SHADOW_OFF + 2 ^ 44).
{ intros y Hy1 Hy2. unfold shadow_addr, SHADOW_OFF.
  pose proof (Z.div_pos y 8 Hy1 ltac:(lia)) as Hd1.
  assert (Hd2 : y / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
  change ((2 ^ 47 - 1) / 8) with (2 ^ 44 - 1) in Hd2. lia. }
assert (HU : forall y, 0 <= y -> y / 8 * 8 <= y < y / 8 * 8 + 8).
{ intros y Hy. pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia. }
split; [|split; [|split; [|split; [|split]]]]; try assumption.
- intros a Ha. rewrite (Hb a Ha). exact (Hv a Ha).
- intros x Hx. destruct (Hra x Hx) as (v & Hv2 & Hok). exists v. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite Hs; [exact Hv2|].
  pose proof (SB x ltac:(lia) ltac:(lia)) as Hsb. unfold shadow_addr in Hsb. lia.
- intros s Hs2. rewrite Hs; [exact (Hh s Hs2)|].
  assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
  pose proof (SB q ltac:(lia) ltac:(lia)) as Hb1.
  pose proof (SB (q + n - 1) ltac:(lia) ltac:(lia)) as Hb2.
  pose proof (HU (shadow_addr q) ltac:(lia)) as HU1.
  pose proof (HU (shadow_addr (q + n - 1)) ltac:(lia)) as HU2.
  lia.
Qed.

(* A byte read from a memory whose view agrees with another's. *)
Lemma sinit_mbyte_eq : forall (W : world segs) m m' a (b : byte),
  YP09.mbyte segs (mrestrict (w_H W) m) a = Some b ->
  aview segs (w_H W) m' a = aview segs (w_H W) m a ->
  YP09.mbyte segs (mrestrict (w_H W) m') a = Some b.
Proof.
intros W m m' a b Hb Hav.
change (aview segs (w_H W) m' a) with
  (option_map (fun x : byte => bv_unsigned x) (YP09.mbyte segs (mrestrict (w_H W) m') a)) in Hav.
change (aview segs (w_H W) m a) with
  (option_map (fun x : byte => bv_unsigned x) (YP09.mbyte segs (mrestrict (w_H W) m) a)) in Hav.
rewrite Hb in Hav.
destruct (YP09.mbyte segs (mrestrict (w_H W) m') a) as [b'|] eqn:Hb'; [|discriminate Hav].
cbn in Hav. injection Hav as Hav. f_equal. apply bv_eq. exact Hav.
Qed.

(* The caller's io bytes, carried to a memory whose view agrees with the entry's on them. *)
Lemma sinit_iob_kept : forall (W : world segs) m m' iop c s r n,
  YI00.garr8 segs (mrestrict (w_H W) m) iop (TW.zs (sinit_io_bytes c s r n)) ->
  (forall a, iop <= a < iop + 32 -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  YI00.garr8 segs (mrestrict (w_H W) m') iop (TW.zs (sinit_io_bytes c s r n)).
Proof.
intros W m m' iop0 c s r n HG Hk.
assert (LL : length (TW.zs (sinit_io_bytes c s r n)) = 32%nat)
  by (unfold TW.zs; rewrite length_map; unfold sinit_io_bytes; rewrite !length_app, !TWL.length_put; reflexivity).
apply (YI00.garr8_frame segs (mrestrict (w_H W) m) _ iop0 _ HG).
intros a Ha. rewrite LL in Ha.
destruct (YP09.mbyte segs (mrestrict (w_H W) m) a) as [b|] eqn:Hb.
- exact (sinit_mbyte_eq W m m' a b Hb (Hk a ltac:(lia))).
- pose proof (Hk a ltac:(lia)) as Hav.
  change (aview segs (w_H W) m' a) with
    (option_map (fun x : byte => bv_unsigned x) (YP09.mbyte segs (mrestrict (w_H W) m') a)) in Hav.
  change (aview segs (w_H W) m a) with
    (option_map (fun x : byte => bv_unsigned x) (YP09.mbyte segs (mrestrict (w_H W) m) a)) in Hav.
  rewrite Hb in Hav. cbn in Hav.
  destruct (YP09.mbyte segs (mrestrict (w_H W) m') a); [discriminate Hav | reflexivity].
Qed.

(* ---- the three config tests, as the branch conditions state them ---- *)

Lemma sinit_swrap32 : forall u, 0 <= u < 2 ^ 32 ->
  bv_swrap 32 u = (if u <? 2 ^ 31 then u else u - 2 ^ 32).
Proof.
intros u Hu. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec u (2 ^ 31)).
- rewrite Z.mod_small by lia. lia.
- replace (u + 2 ^ 31) with ((u - 2 ^ 31) + 1 * 2 ^ 32) by lia.
  rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
Qed.

Lemma sinit_modneg : forall z, - 2 ^ 63 <= z < 0 -> z mod 2 ^ 64 = z + 2 ^ 64.
Proof.
intros z Hz. replace z with ((z + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma sinit_u64 : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof.
intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (Z.of_N 64) with 64. reflexivity.
Qed.

(* `beqz` on a sign-extended 4-byte field *)
Lemma sinit_cond_eq0 : forall u, 0 <= u < 2 ^ 32 ->
  (bv_unsigned (Z_to_bv 64 (bv_swrap 32 u)) =? 0) = (u =? 0).
Proof.
intros u Hu. rewrite sinit_u64, sinit_swrap32 by lia.
destruct (Z.ltb_spec u (2 ^ 31)).
- rewrite Z.mod_small by lia. reflexivity.
- rewrite sinit_modneg by lia.
  destruct (Z.eqb_spec (u - 2 ^ 32 + 2 ^ 64) 0); destruct (Z.eqb_spec u 0); first [reflexivity | lia].
Qed.

(* `bltu a2, a1` with a2 = 255 *)
Lemma sinit_cond_255 : forall u, 0 <= u < 2 ^ 32 ->
  (255 <? bv_unsigned (Z_to_bv 64 (bv_swrap 32 u))) = (255 <? u).
Proof.
intros u Hu. rewrite sinit_u64, sinit_swrap32 by lia.
destruct (Z.ltb_spec u (2 ^ 31)).
- rewrite Z.mod_small by lia. reflexivity.
- rewrite sinit_modneg by lia.
  destruct (Z.ltb_spec 255 (u - 2 ^ 32 + 2 ^ 64)); destruct (Z.ltb_spec 255 u); first [reflexivity | lia].
Qed.

(* `addiw a1,a1,-1485; bltu a1, -1461` is `max_body < 24 || 1484 < max_body` *)
Lemma sinit_cond_body : forall u, 0 <= u < 2 ^ 32 ->
  (bv_unsigned (Z_to_bv 64 (zalu32 ALU_ADD (bv_swrap 32 u) (-1485))) <? 18446744073709550155)
  = ((u <? 24) || (1484 <? u))%bool.
Proof.
intros u Hu. unfold zalu32, zcanon, zu32, M64, M32. cbn [zalu_raw].
assert (E1 : bv_swrap 32 u mod 2 ^ 32 = u).
{ rewrite sinit_swrap32 by lia. destruct (Z.ltb_spec u (2 ^ 31)).
  - apply Z.mod_small; lia.
  - replace (u - 2 ^ 32) with (u + (-1) * 2 ^ 32) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small; lia. }
assert (E2 : (-1485) mod 2 ^ 32 = 2 ^ 32 - 1485)
  by (replace (-1485) with ((2 ^ 32 - 1485) + (-1) * 2 ^ 32) by lia;
      rewrite Z_mod_plus_full; apply Z.mod_small; lia).
rewrite E1, E2.
assert (E3 : bv_swrap 32 (u + (2 ^ 32 - 1485)) = bv_swrap 32 (u - 1485)).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). f_equal.
  replace (u + (2 ^ 32 - 1485) + 2 ^ 31) with ((u - 1485 + 2 ^ 31) + 1 * 2 ^ 32) by lia.
  rewrite Z_mod_plus_full. reflexivity. }
rewrite E3. rewrite sinit_u64, Z.mod_mod by lia.
assert (HR : - 2 ^ 31 <= bv_swrap 32 (u - 1485) < 2 ^ 31).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32).
  pose proof (Z.mod_pos_bound (u - 1485 + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia. }
assert (ED : bv_swrap 32 (u - 1485) = (if u - 1485 <? - 2 ^ 31 then u - 1485 + 2 ^ 32
              else if u - 1485 <? 2 ^ 31 then u - 1485 else u - 1485 - 2 ^ 32)).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32).
  destruct (Z.ltb_spec (u - 1485) (- 2 ^ 31)).
  - replace (u - 1485 + 2 ^ 31) with ((u - 1485 + 2 ^ 31 + 2 ^ 32) + (-1) * 2 ^ 32) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
  - destruct (Z.ltb_spec (u - 1485) (2 ^ 31)).
    + rewrite Z.mod_small by lia. lia.
    + replace (u - 1485 + 2 ^ 31) with ((u - 1485 - 2 ^ 31) + 1 * 2 ^ 32) by lia.
      rewrite Z_mod_plus_full, Z.mod_small by lia. lia. }
rewrite ED. clear ED HR E1 E2 E3.
destruct (Z.ltb_spec (u - 1485) (- 2 ^ 31)) as [Ha|Ha]; [lia|].
destruct (Z.ltb_spec (u - 1485) (2 ^ 31)) as [Hb|Hb].
- destruct (Z.ltb_spec (u - 1485) 0) as [Hc|Hc].
  + rewrite sinit_modneg by lia.
    destruct (Z.ltb_spec u 24); cbn [orb]; destruct (Z.ltb_spec 1484 u);
      first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
  + rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec u 24); cbn [orb]; destruct (Z.ltb_spec 1484 u);
      first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
- rewrite sinit_modneg by lia.
  destruct (Z.ltb_spec u 24); cbn [orb]; destruct (Z.ltb_spec 1484 u);
    first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

(* The world survives a step that keeps every byte of G's hull. *)
Lemma sinit_tw_keep : forall (W : world segs) m m' Bw0,
  tw_at TMAP_B (aview segs (w_H W) m) Bw0 ->
  (forall a, TG.G_HARNESS_B_LO <= a < TG.G_HARNESS_B_HI -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  tw_at TMAP_B (aview segs (w_H W) m') Bw0.
Proof.
intros W m m' Bw0 Htw0 Hk. apply (tw_kept_GB (aview segs (w_H W) m)); [exact Htw0|].
intros b n i Hin Hi. apply Hk.
pose proof (TG.G_HARNESS_B_in_hull (b, n) Hin) as H. cbn [fst snd] in H. lia.
Qed.

(* The region of g_cfg's three fields, and of the bytes the three checked stores write. *)
Lemma sinit_cfg_region_ok : forall (W : world segs) m Bw0 (E : env),
  tw_at TMAP_B (aview segs (w_H W) m) Bw0 ->
  ew E 11 = Z_to_bv 64 SINIT_CFG ->
  ew E 34 = Z_to_bv 64 (TW.u_at Bw0 (TW.OFF_g_cfg + 12) 4) ->
  ew E 35 = Z_to_bv 64 (TW.u_at Bw0 (TW.OFF_g_cfg + 52) 4) ->
  ew E 36 = Z_to_bv 64 (TW.u_at Bw0 (TW.OFF_g_cfg + 56) 4) ->
  region_ok segs E (mrestrict (w_H W) m) SINIT_CFG_REG.
Proof.
intros W m Bw0 E Htw0 E11 E34 E35 E36.
assert (HU : forall kk, 0 <= kk -> kk + 4 <= TW.SZ_g_cfg ->
  YI04.val_mem segs (mrestrict (w_H W) m) (SINIT_CFG + kk) 4 (TW.u_at Bw0 (TW.OFF_g_cfg + kk) 4)).
{ intros kk H1 H2.
  exact (tw_read_val segs (mrestrict (w_H W) m) TMAP_B Bw0 TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg kk 4%nat
    TMAP_B_ok Htw0 TMAP_B_g_cfg H1 ltac:(cbn [Z.of_nat]; lia)). }
assert (UB : base_val E (Some 11%nat) = SINIT_CFG)
  by (cbn [base_val]; rewrite E11; apply unsigned_lit_small; unfold SINIT_CFG, TB_g_cfg; lia).
unfold SINIT_CFG_REG, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite UB.
split; [unfold SINIT_CFG, TB_g_cfg; lia|]. split; [unfold SINIT_CFG, TB_g_cfg; lia|].
split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val segs E _ SINIT_CFG 12 4 (SOff 34%nat 0) (TW.u_at Bw0 (TW.OFF_g_cfg + 12) 4));
  [ cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (sinit_u4 Bw0 (TW.OFF_g_cfg + 12)) as HR; cbn [Z.of_N]; lia
  | cbn [Z.of_N]; lia
  | exact (HU 12 ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)) ].
- apply (chunk_ok_val segs E _ SINIT_CFG 52 4 (SOff 35%nat 0) (TW.u_at Bw0 (TW.OFF_g_cfg + 52) 4));
  [ cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (sinit_u4 Bw0 (TW.OFF_g_cfg + 52)) as HR; cbn [Z.of_N]; lia
  | cbn [Z.of_N]; lia
  | exact (HU 52 ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)) ].
- apply (chunk_ok_val segs E _ SINIT_CFG 56 4 (SOff 36%nat 0) (TW.u_at Bw0 (TW.OFF_g_cfg + 56) 4));
  [ cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (sinit_u4 Bw0 (TW.OFF_g_cfg + 56)) as HR; cbn [Z.of_N]; lia
  | cbn [Z.of_N]; lia
  | exact (HU 56 ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)) ].
Qed.

Lemma sinit_s_region_ok : forall (W : world segs) m (E : env) lo hi,
  0 <= lo -> lo <= hi -> hi <= TW.SZ_g_s -> ew E 10 = Z_to_bv 64 SINIT_S ->
  region_ok segs E (mrestrict (w_H W) m) (YP09.mkRegion (Some 10%nat) lo hi lo hi []).
Proof.
intros W m E lo hi Hlo Hlh Hhi E10.
assert (UB : base_val E (Some 10%nat) = SINIT_S)
  by (cbn [base_val]; rewrite E10; apply unsigned_lit_small; unfold SINIT_S, TB_g_s; lia).
unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite UB.
split; [unfold SINIT_S, TB_g_s; lia|].
split; [unfold SINIT_S, TB_g_s, TW.SZ_g_s in *; lia|].
split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (SINIT_S + o) G_HARNESS_B_rw).
apply sinit_inG_s. unfold TW.SZ_g_s in *; lia.
Qed.

(* The value of a sign-extended 4-byte field as the branch conditions see it. *)
Lemma sinit_U_ext : forall (E : env) (n : nat) v, 0 <= v < 2 ^ 32 -> ew E n = Z_to_bv 64 v ->
  U E (SExt true 32 (SOff n 0)) = bv_unsigned (Z_to_bv 64 (bv_swrap 32 v)).
Proof.
intros E n v Hv Hew. unfold U. cbn [sv_denot]. rewrite Hew.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. rewrite sinit_lw by lia. reflexivity.
Qed.

Lemma sinit_U_body : forall (E : env) (n : nat) v, 0 <= v < 2 ^ 32 -> ew E n = Z_to_bv 64 v ->
  U E (SAluw ALU_ADD (SExt true 32 (SOff n 0)) (SLit (-1485)))
  = bv_unsigned (Z_to_bv 64 (zalu32 ALU_ADD (bv_swrap 32 v) (-1485))).
Proof.
intros E n v Hv Hew. unfold U. cbn [sv_denot].
rewrite Hew. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. rewrite sinit_lw by lia.
rewrite zalu32_sound. reflexivity.
Qed.

(* The byte of g_cfg at offset j, read off the world relation. *)
Lemma sinit_cfg_bytes : forall (W : world segs) m Bw0 j,
  tw_at TMAP_B (aview segs (w_H W) m) Bw0 -> 0 <= j < 60 ->
  aview segs (w_H W) m (SINIT_CFG + j)
  = Some (bv_unsigned (nth (Z.to_nat j) (TW.sub Bw0 TW.OFF_g_cfg (Z.to_nat TW.SZ_g_cfg)) (Z_to_bv 8 0))).
Proof.
intros W m Bw0 j Htw0 Hj. unfold SINIT_CFG. pose proof Htw0 as (HL & HR).
rewrite (HR TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg j TMAP_B_g_cfg ltac:(unfold TW.SZ_g_cfg; lia)).
f_equal. f_equal. symmetry.
rewrite (tw_nth_sub Bw0 TW.OFF_g_cfg (Z.to_nat TW.SZ_g_cfg) (Z.to_nat j) (Z_to_bv 8 0)
  ltac:(unfold TW.OFF_g_cfg; lia)
  ltac:(rewrite (Z2Nat.inj_lt j TW.SZ_g_cfg) in Hj by (unfold TW.SZ_g_cfg; lia); unfold TW.SZ_g_cfg in *; lia)
  ltac:(rewrite HL; unfold TW.OFF_g_cfg, TW.SZ_g_cfg, TW.W_LEN; lia)).
f_equal. unfold TW.OFF_g_cfg. lia.
Qed.

(* A byte of the caller's io block, read off garr8. *)
Lemma sinit_iob_byte : forall (W : world segs) m iop0 c s0 r0 n0 j,
  YI00.garr8 segs (mrestrict (w_H W) m) iop0 (TW.zs (sinit_io_bytes c s0 r0 n0)) -> 0 <= j < 32 ->
  aview segs (w_H W) m (iop0 + j)
  = Some (bv_unsigned (nth (Z.to_nat j) (sinit_io_bytes c s0 r0 n0) (Z_to_bv 8 0))).
Proof.
intros W m iop0 c s0 r0 n0 j HG Hj.
assert (LL : length (TW.zs (sinit_io_bytes c s0 r0 n0)) = 32%nat)
  by (unfold TW.zs; rewrite length_map; unfold sinit_io_bytes;
      rewrite !length_app, !TWL.length_put; reflexivity).
pose proof (YI00.garr8_mbyte segs (mrestrict (w_H W) m) iop0 _ (Z.to_nat j) HG ltac:(lia)) as Hb.
rewrite Z2Nat.id in Hb by lia.
change (aview segs (w_H W) m (iop0 + j)) with
  (option_map (fun x : byte => bv_unsigned x) (YP09.mbyte segs (mrestrict (w_H W) m) (iop0 + j))).
rewrite Hb. cbn [option_map]. f_equal.
assert (HR : 0 <= nth (Z.to_nat j) (TW.zs (sinit_io_bytes c s0 r0 n0)) 0 < 256)
  by (exact (proj2 (YI00.garr8_nthZ segs (mrestrict (w_H W) m) iop0 _ j HG ltac:(lia) ltac:(lia)))).
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 8) with 8.
rewrite Z.mod_small by lia.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite LL; lia).
unfold TW.zs. rewrite map_nth. reflexivity.
Qed.

(* A byte of a stored field, read off the region's chunk. *)
Lemma sinit_vm_byte : forall (W : world segs) m a (n : nat) v j,
  YI04.val_mem segs (mrestrict (w_H W) m) a n v -> (j < n)%nat ->
  aview segs (w_H W) m (a + Z.of_nat j) = Some (bv_unsigned (nth j (TW.put n v) (Z_to_bv 8 0))).
Proof.
intros W m a n v j HV Hj.
change (aview segs (w_H W) m (a + Z.of_nat j)) with
  (option_map (fun x : byte => bv_unsigned x) (YP09.mbyte segs (mrestrict (w_H W) m) (a + Z.of_nat j))).
rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite (tw_le_byte_put n v j (Z_to_bv 8 0) Hj).
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 8) with 8.
apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* The byte of g_cfg's desk MAC at offset 6 + j, read off the world relation. *)
Lemma sinit_cfg6_bytes : forall (W : world segs) m Bw0 j,
  tw_at TMAP_B (aview segs (w_H W) m) Bw0 -> 0 <= j < 6 ->
  aview segs (w_H W) m (SINIT_CFG + 6 + j)
  = Some (bv_unsigned (nth (Z.to_nat j) (TW.sub Bw0 (TW.OFF_g_cfg + 6) 6) (Z_to_bv 8 0))).
Proof.
intros W m Bw0 j Htw0 Hj. unfold SINIT_CFG. pose proof Htw0 as (HL & HR).
replace (TB_g_cfg + 6 + j) with (TB_g_cfg + (6 + j)) by lia.
rewrite (HR TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg (6 + j) TMAP_B_g_cfg ltac:(unfold TW.SZ_g_cfg; lia)).
f_equal. f_equal. symmetry.
rewrite (tw_nth_sub Bw0 (TW.OFF_g_cfg + 6) 6 (Z.to_nat j) (Z_to_bv 8 0)
  ltac:(unfold TW.OFF_g_cfg; lia) ltac:(lia)
  ltac:(rewrite HL; unfold TW.OFF_g_cfg, TW.W_LEN; lia)).
f_equal. unfold TW.OFF_g_cfg. lia.
Qed.

(* A byte a store left, read off its chunk in the region of g_s. *)
Lemma sinit_store_byte : forall (W : world segs) m (E : env) lo hi cs od (w : N) (e : sv) v j,
  region_ok segs E (mrestrict (w_H W) m) (YP09.mkRegion (Some 10%nat) lo hi lo hi cs) ->
  ew E 10 = Z_to_bv 64 SINIT_S ->
  In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) -> (j < N.to_nat w)%nat ->
  aview segs (w_H W) m (SINIT_S + od + Z.of_nat j)
  = Some (bv_unsigned (nth j (TW.put (N.to_nat w) v) (Z_to_bv 8 0))).
Proof.
intros W m E lo hi cs od w e v j Hreg E10 Hin Hden Hv Hw Hj.
assert (UB : bv_unsigned (ew E 10) = SINIT_S)
  by (rewrite E10; apply unsigned_lit_small; unfold SINIT_S, TB_g_s; lia).
pose proof (field_of_region E (mrestrict (w_H W) m) 10%nat SINIT_S cs lo hi lo hi od w e v
  Hreg UB Hin Hden Hv Hw) as HV.
exact (sinit_vm_byte W m (SINIT_S + od) (N.to_nat w) v j HV Hj).
Qed.

(* The walk. *)
Lemma sinit_holds : @transport_diginet_session_init_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_diginet_session_init_cg_holds_stmt.
intros HCELLS HSC HSI LAWS MTL HGX HSET HCPY.
unfold transport_diginet_session_init_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
  iop io_ctx io_send io_recv io_now ntf ctx r Bw Bw'
  HJ Hra Hra4 Hgp Htp H10 H11 H12 H13 H14 Hsp16 Hlo Hhi Htw Hm
  Hbc Hbs Hbr Hbn Hbnt Hbcx Hiop0 Hiop8 HSRC HIOB HOFF HDISJ Hev.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : SINIT_STK = 4160) by reflexivity.
assert (FF : SINIT_FRAME = 64) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (ES : SINIT_S = 6157888) by reflexivity.
assert (ECF : SINIT_CFG = 6155520) by reflexivity.
assert (ESZ : TW.SZ_g_s = 18264) by reflexivity.
assert (EIL : SINIT_IO_LEN = 32) by reflexivity.
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - SINIT_STK) by lia.
assert (Hm16 : (spZ regs - 64 - sp0) mod 16 = 0).
{ replace (spZ regs - 64 - sp0) with (spZ regs - sp0 + (-4) * 16) by lia.
  rewrite Z_mod_plus_full, Zminus_mod, Hsp16, Hsp0a. reflexivity. }
assert (Hwin : forall a, spZ regs - SINIT_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (HLB : Z.of_nat (length Bw) = TW.W_LEN)
  by (rewrite (tw_len _ _ _ Htw), Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia]).
(* the caller's io block *)
assert (HRD : decode_rd_ok W memc iop SINIT_IO_LEN)
  by (exact (trans_src_ok_rd B LAWS lyc Sc W memc mdc iop SINIT_IO_LEN HAR HSRC ltac:(lia))).
assert (Hiopr : 1 <= iop <= 2 ^ 47 - 32).
{ destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc iop SINIT_IO_LEN HAR HSRC ltac:(lia))
    as [[Hp1 Hp2] | (Hp1 & Hp2 & Hp3 & Hp4)]; unfold SINIT_IO_LEN in *; lia. }
assert (HIOS : forall a, iop <= a < iop + 32 -> ~ (SINIT_S <= a < SINIT_S + TW.SZ_g_s))
  by (unfold SINIT_IO_LEN, TW.SZ_g_s in HDISJ; destruct HDISJ as [HD1 | HD1];
      intros a Ha; unfold TW.SZ_g_s; lia).
assert (HIOW2 : forall a, iop <= a < iop + 32 -> ~ (spZ regs - SINIT_STK <= a < spZ regs))
  by (unfold decode_off_win, SINIT_IO_LEN in HOFF; destruct HOFF as [HO1 | HO1]; intros a Ha; lia).
(* the valuation *)
set (E0 := sinit_E regs io_send (TW.u_at Bw (TW.OFF_g_cfg + 12) 4) (TW.u_at Bw (TW.OFF_g_cfg + 52) 4)
  (TW.u_at Bw (TW.OFF_g_cfg + 56) 4)).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, sinit_E; apply Eimg_env).
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E0 n = YK11.getr regs q)
  by (intros n q Hn; unfold E0, sinit_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E10 : ew E0 10 = Z_to_bv 64 SINIT_S) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (U10 : bv_unsigned (ew E0 10) = SINIT_S) by (rewrite E10; apply unsigned_lit_small; lia).
assert (E11 : ew E0 11 = Z_to_bv 64 SINIT_CFG) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (U11 : bv_unsigned (ew E0 11) = SINIT_CFG) by (rewrite E11; apply unsigned_lit_small; lia).
assert (E12 : ew E0 12 = Z_to_bv 64 iop) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (U12 : bv_unsigned (ew E0 12) = iop) by (rewrite E12; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E0, sinit_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E14 : ew E0 14 = Z_to_bv 64 ctx) by (rewrite (EE 14%nat 14%bv eq_refl); exact H14).
assert (U0L : U E0 (SLit 0) = 0) by (unfold U; cbn [sv_denot]; vm_compute; reflexivity).
assert (E13 : ew E0 13 = Z_to_bv 64 ntf) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13).
assert (U13 : U E0 (SOff 13%nat 0) = ntf) by (apply (U_atom E0 13%nat ntf E13); lia).
assert (E33 : ew E0 33 = Z_to_bv 64 io_send)
  by (unfold E0, sinit_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (U33 : U E0 (SOff 33%nat 0) = io_send) by (apply (U_atom E0 33%nat io_send E33); lia).
assert (E34 : ew E0 34 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_cfg + 12) 4))
  by (unfold E0, sinit_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E0 35 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_cfg + 52) 4))
  by (unfold E0, sinit_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E0 36 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_cfg + 56) 4))
  by (unfold E0, sinit_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
pose proof (sinit_entry lyc Sc W regs memc mdc io_send (TW.u_at Bw (TW.OFF_g_cfg + 12) 4)
  (TW.u_at Bw (TW.OFF_g_cfg + 52) 4) (TW.u_at Bw (TW.OFF_g_cfg + 56) 4) iop HCELLS HAR
  ltac:(intros a Ha; apply Hpres0; lia) Hsp Hsp16 H10 H11 H12 ltac:(lia) Hiop8) as HS.
fold E0 in HS.
assert (SHOK : sh_ok segs SINIT_BX SINIT_SH0 E0 (mrestrict (w_H W) memc)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_init)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x00 .. +0x48: the frame, the seven saves, the three NULL tests, the shadow base through its GOT word *)
paj_run_to_tok RUNTO HS HJ SHOK YC1i.Bspan SINIT_GOT_STOP.
{ sinit_awr_norm. sinit_awr_stack Usp. sinit_awr_ro. sinit_awr_ro. apply awr_ok_x_nil. }
(* the memory is the entry's outside the frame below sp *)
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta.
  sinit_win Hin Hx ltac:(rewrite ?Usp in Hx; lia). }
assert (GA1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (HIOW : forall a, iop <= a < iop + 32 -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a).
{ intros a Ha. apply KR1; [lia | unfold decode_off_win in HOFF; lia]. }
assert (HIOB1 : YI00.garr8 segs (mrestrict (w_H W) (ms_mem ms)) iop
  (TW.zs (sinit_io_bytes io_ctx io_send io_recv io_now)))
  by (apply (sinit_iob_kept W memc (ms_mem ms) iop io_ctx io_send io_recv io_now HIOB HIOW)).
assert (HRD1 : decode_rd_ok W (ms_mem ms) iop SINIT_IO_LEN).
{ apply (sinit_rd_kept W memc (ms_mem ms) iop SINIT_IO_LEN ltac:(lia) ltac:(lia) ltac:(lia) HRD).
  - intros a Ha. apply HIOW. lia.
  - intros s0 Hs0. apply KR1; lia. }
(* the io region replaces the two image cells, whose only use was the shadow base *)
sinit_keep HS [0%nat] HSa. clear HS. rename HSa into HS.
assert (RIO : region_ok segs E0 (mrestrict (w_H W) (ms_mem ms)) SINIT_IO_REG).
{ unfold SINIT_IO_REG, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val segs E0 _ iop 8 8 (SOff 33%nat 0) io_send);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
  exact (sinit_io_val W (ms_mem ms) iop io_ctx io_send io_recv io_now HIOB1). }
pose proof (st_ok_pi_add_region E0 _ _ SINIT_IO_REG HS ltac:(vm_compute; reflexivity) RIO
  ltac:(cbn [ss_mem all_disjoint]; split; [|exact I];
        unfold extent_disjoint, SINIT_IO_REG;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U12, Usp;
        unfold decode_off_win in HOFF; lia)) as HSa.
clear HS. rename HSa into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
clear SHOK.
assert (SHOK : sh_ok segs SINIT_BX SINIT_SHIO E0 (mrestrict (w_H W) (ms_mem ms)))
  by (exact (sinit_shok_io W (ms_mem ms) E0 iop HRD1 E12 E32)).
(* run 2, +0x48 .. +0x60: the checked load of io + 8 and `beqz s3` on notify *)
paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
{ sinit_awr_norm. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
  aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) memc a).
{ intros a Ha H1.
  assert (Hk : aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) (ms_mem ms) a).
  { apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr); [| exact Ha | exact H1].
    intros bq wlo whi x Hx Hxx. cbv beta. sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia; repeat rewrite ew_ewset_other in Hxx by lia; rewrite ?Usp in Hxx; lia). }
  rewrite Hk. apply KR1; assumption. }
assert (GA2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms0) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
clear HF HFr HG.
(* `beqz s3`: notify *)
psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
- (* notify = 0: DIGINET_E_ARG *)
  assert (Hntf : ntf = 0).
  { rewrite branch_eq_U, U13, U0L in Hc. apply Z.eqb_eq in Hc. exact Hc. }
  destruct (sinit_m_arg Bw Bw' io_ctx io_send io_recv io_now ntf ctx r ltac:(right; exact Hntf) Hm)
    as [EBw Er].
  (* the epilogue and `ret` *)
  paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
  { sinit_awr_norm. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
  assert (KRe : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
    aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
  { intros a Ha H1.
    assert (Hk : aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) (ms_mem ms0) a).
    { apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr); [| exact Ha | exact H1].
      intros bq wlo whi x Hx Hxx. cbv beta. sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia; repeat rewrite ew_ewset_other in Hxx by lia; rewrite ?Usp in Hxx; lia). }
    rewrite Hk. apply KR2; assumption. }
  assert (GAe : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ _) => set (EX := EF) in HS end.
  assert (HEF : forall n, (n < 1024)%nat -> ew EX n = ew E0 n)
    by (intros n Hn; unfold EX; repeat rewrite ew_ewset_other by lia; reflexivity).
  sinit_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite HEF by lia;
          rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  sinit_reg HS (Z_to_bv 5 10) (w64 r) RF10 ltac:(rewrite Er; cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms1)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) EX _ ms1 regs
      [w64 SHADOW_OFF; w64 io_send; w64 (TW.u_at Bw (TW.OFF_g_cfg + 12) 4);
       w64 (TW.u_at Bw (TW.OFF_g_cfg + 52) 4); w64 (TW.u_at Bw (TW.OFF_g_cfg + 56) 4)] HS).
    - apply sinit_agree; [intros n Hn; rewrite HEF by lia; reflexivity | reflexivity].
    - vm_compute. reflexivity. }
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  rewrite EBw.
  exact (sinit_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r Bw
    (ms_regs ms1) (ms_mem ms1) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ
    ltac:(intros a Ha H1 H2; apply KRe; [lia | lia])
    GAe
    ltac:(apply (sinit_tw_keep W memc (ms_mem ms1) Bw Htw); intros a Ha; apply KRe;
          unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Ha; lia)
    HPF RF1 RF10 mat').
- (* notify <> 0: the load of io->send and `beqz a1` *)
  assert (Hntf : ntf <> 0).
  { rewrite branch_eq_U, U13, U0L in Hc. intros ->. rewrite Z.eqb_refl in Hc. discriminate Hc. }
  paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
  { sinit_awr_norm. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
  assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
    aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) memc a).
  { intros a Ha H1.
    assert (Hk : aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) (ms_mem ms0) a).
    { apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr); [| exact Ha | exact H1].
      intros bq wlo whi x Hx Hxx. cbv beta. sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia; repeat rewrite ew_ewset_other in Hxx by lia; rewrite ?Usp in Hxx; lia). }
    rewrite Hk. apply KR2; assumption. }
  assert (GA3 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
  + (* io->send = 0: DIGINET_E_ARG *)
    assert (Hsnd : io_send = 0).
    { rewrite branch_eq_U, U33, U0L in Hc0. apply Z.eqb_eq in Hc0. exact Hc0. }
    destruct (sinit_m_arg Bw Bw' io_ctx io_send io_recv io_now ntf ctx r ltac:(left; exact Hsnd) Hm)
      as [EBw Er].
    (* the epilogue and `ret` *)
    paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
    { sinit_awr_norm. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
    assert (KRe : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
      aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) memc a).
    { intros a Ha H1.
      assert (Hk : aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) (ms_mem ms1) a).
      { apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr); [| exact Ha | exact H1].
        intros bq wlo whi x Hx Hxx. cbv beta. sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia; repeat rewrite ew_ewset_other in Hxx by lia; rewrite ?Usp in Hxx; lia). }
      rewrite Hk. apply KR3; assumption. }
    assert (GAe : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms2) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA3 a Ha))).
    clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ _) => set (EX := EF) in HS end.
    assert (HEF : forall n, (n < 1024)%nat -> ew EX n = ew E0 n)
      by (intros n Hn; unfold EX; repeat rewrite ew_ewset_other by lia; reflexivity).
    sinit_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
      ltac:(cbn [sv_denot]; rewrite HEF by lia;
            rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    sinit_reg HS (Z_to_bv 5 10) (w64 r) RF10
      ltac:(rewrite Er; cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity).
    assert (HPF : aregs_preserved regs (ms_regs ms2)).
    { apply (aregs_preserved_of_st_ok segs (w_H W) EX _ ms2 regs
        [w64 SHADOW_OFF; w64 io_send; w64 (TW.u_at Bw (TW.OFF_g_cfg + 12) 4);
         w64 (TW.u_at Bw (TW.OFF_g_cfg + 52) 4); w64 (TW.u_at Bw (TW.OFF_g_cfg + 56) 4)] HS).
      - apply sinit_agree; [intros n Hn; rewrite HEF by lia; reflexivity | reflexivity].
      - vm_compute. reflexivity. }
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'.
    rewrite EBw.
    exact (sinit_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r Bw
      (ms_regs ms2) (ms_mem ms2) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ
      ltac:(intros a Ha H1 H2; apply KRe; [lia | lia])
      GAe
      ltac:(apply (sinit_tw_keep W memc (ms_mem ms2) Bw Htw); intros a Ha; apply KRe;
            unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Ha; lia)
      HPF RF1 RF10 mat').
  + (* io->send <> 0 *)
    assert (Hsnd : io_send <> 0).
    { rewrite branch_eq_U, U33, U0L in Hc0. intros ->. rewrite Z.eqb_refl in Hc0. discriminate Hc0. }
    (* the cfg region replaces the io region, whose only use was io->send *)
    assert (Htw1 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms1)) Bw)
      by (apply (sinit_tw_keep W memc (ms_mem ms1) Bw Htw); intros a Ha; apply KR3;
          unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Ha; lia).
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
    sinit_keep HS [1%nat] HSa. clear HS. rename HSa into HS.
    pose proof (st_ok_pi_add_region E0 _ _ SINIT_CFG_REG HS ltac:(vm_compute; reflexivity)
      (sinit_cfg_region_ok W (ms_mem ms1) Bw E0 Htw1 E11 E34 E35 E36)
      ltac:(cbn [ss_mem all_disjoint]; split; [|exact I];
            unfold extent_disjoint, SINIT_CFG_REG;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U11, Usp;
            unfold SINIT_CFG, TB_g_cfg; lia)) as HSa.
    clear HS. rename HSa into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
    clear SHOK.
    assert (SHOK : sh_ok segs SINIT_BX SINIT_SHCFG E0 (mrestrict (w_H W) (ms_mem ms1)))
      by (exact (sinit_shok_cfg lyc Sc W (ms_mem ms1) _ E0 HSC HAR1 E11 E32)).
    assert (U35 : U E0 (SExt true 32 (SOff 35%nat 0))
      = bv_unsigned (Z_to_bv 64 (bv_swrap 32 (TW.u_at Bw (TW.OFF_g_cfg + 52) 4))))
      by (apply (sinit_U_ext E0 35%nat _ (sinit_u4 Bw (TW.OFF_g_cfg + 52)) E35)).
    assert (U36 : U E0 (SExt true 32 (SOff 36%nat 0))
      = bv_unsigned (Z_to_bv 64 (bv_swrap 32 (TW.u_at Bw (TW.OFF_g_cfg + 56) 4))))
      by (apply (sinit_U_ext E0 36%nat _ (sinit_u4 Bw (TW.OFF_g_cfg + 56)) E36)).
    assert (RDM : 0 <= TW.u_at Bw (TW.OFF_g_cfg + 12) 4 < 2 ^ 32)
      by (exact (sinit_u4 Bw (TW.OFF_g_cfg + 12))).
    assert (RCM : 0 <= TW.u_at Bw (TW.OFF_g_cfg + 52) 4 < 2 ^ 32)
      by (exact (sinit_u4 Bw (TW.OFF_g_cfg + 52))).
    assert (RMB : 0 <= TW.u_at Bw (TW.OFF_g_cfg + 56) 4 < 2 ^ 32)
      by (exact (sinit_u4 Bw (TW.OFF_g_cfg + 56))).
    (* run 4: the checked load of cfg + 52 and `beqz a1` *)
    paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
    { sinit_awr_norm. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
    assert (KR4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
      aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) memc a).
    { intros a Ha H1.
      assert (Hk : aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) (ms_mem ms1) a).
      { apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr); [| exact Ha | exact H1].
        intros bq wlo whi x Hx Hxx. cbv beta. sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia; repeat rewrite ew_ewset_other in Hxx by lia; rewrite ?Usp in Hxx; lia). }
      rewrite Hk. apply KR3; assumption. }
    assert (GA4 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms2) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA3 a Ha))).
    clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
    * (* max_cmds = 0: DIGINET_E_ARG *)
      assert (Hcm : TW.Cfg_max_cmds Bw = 0).
      { rewrite branch_eq_U, U35, U0L, sinit_cond_eq0 in Hc1 by lia.
        apply Z.eqb_eq in Hc1. exact Hc1. }
      destruct (sinit_m_cfg Bw Bw' io_ctx io_send io_recv io_now ntf ctx r ltac:(left; exact Hcm) Hm)
        as [EBw Er].
      (* the epilogue and `ret` *)
      paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
      { sinit_awr_norm. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
      assert (KRe : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
        aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) memc a).
      { intros a Ha H1.
        assert (Hk : aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) (ms_mem ms2) a).
        { apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr); [| exact Ha | exact H1].
          intros bq wlo whi x Hx Hxx. cbv beta. sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia; repeat rewrite ew_ewset_other in Hxx by lia; rewrite ?Usp in Hxx; lia). }
        rewrite Hk. apply KR4; assumption. }
      assert (GAe : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA4 a Ha))).
      clear HF HFr HG.
      lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ _) => set (EX := EF) in HS end.
      assert (HEF : forall n, (n < 1024)%nat -> ew EX n = ew E0 n)
        by (intros n Hn; unfold EX; repeat rewrite ew_ewset_other by lia; reflexivity).
      sinit_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
        ltac:(cbn [sv_denot]; rewrite HEF by lia;
              rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
      sinit_reg HS (Z_to_bv 5 10) (w64 r) RF10
        ltac:(rewrite Er; cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity).
      assert (HPF : aregs_preserved regs (ms_regs ms3)).
      { apply (aregs_preserved_of_st_ok segs (w_H W) EX _ ms3 regs
          [w64 SHADOW_OFF; w64 io_send; w64 (TW.u_at Bw (TW.OFF_g_cfg + 12) 4);
           w64 (TW.u_at Bw (TW.OFF_g_cfg + 52) 4); w64 (TW.u_at Bw (TW.OFF_g_cfg + 56) 4)] HS).
        - apply sinit_agree; [intros n Hn; rewrite HEF by lia; reflexivity | reflexivity].
        - vm_compute. reflexivity. }
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'.
      rewrite EBw.
      exact (sinit_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r Bw
        (ms_regs ms3) (ms_mem ms3) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ
        ltac:(intros a Ha H1 H2; apply KRe; [lia | lia])
        GAe
        ltac:(apply (sinit_tw_keep W memc (ms_mem ms3) Bw Htw); intros a Ha; apply KRe;
              unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Ha; lia)
        HPF RF1 RF10 mat').
    * (* max_cmds <> 0 *)
      assert (Hcm : TW.Cfg_max_cmds Bw <> 0).
      { rewrite branch_eq_U, U35, U0L, sinit_cond_eq0 in Hc1 by lia.
        intros HH. unfold TW.Cfg_max_cmds, TW.A_Cfg_max_cmds in HH.
        rewrite HH, Z.eqb_refl in Hc1. discriminate Hc1. }
      (* run 5: the checked load of cfg + 56 and `bltu a2, a1` on max_cmds *)
      paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
      { sinit_awr_norm. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
      assert (KR5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
        aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) memc a).
      { intros a Ha H1.
        assert (Hk : aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) (ms_mem ms2) a).
        { apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr); [| exact Ha | exact H1].
          intros bq wlo whi x Hx Hxx. cbv beta. sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia; repeat rewrite ew_ewset_other in Hxx by lia; rewrite ?Usp in Hxx; lia). }
        rewrite Hk. apply KR4; assumption. }
      assert (GA5 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms3) a)
        by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA4 a Ha))).
      clear HF HFr HG.
      lazymatch type of HS with st_ok_pi _ _ ?EF _ _ =>
        assert (V35 : U EF (SExt true 32 (SOff 35%nat 0))
          = bv_unsigned (Z_to_bv 64 (bv_swrap 32 (TW.u_at Bw (TW.OFF_g_cfg + 52) 4))))
          by (apply (sinit_U_ext EF 35%nat _ (sinit_u4 Bw (TW.OFF_g_cfg + 52)));
              repeat rewrite ew_ewset_other by lia; exact E35);
        assert (V255 : U EF (SLit 255) = 255) by (unfold U; cbn [sv_denot]; vm_compute; reflexivity)
      end.
      psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
      ** (* 255 < max_cmds: DIGINET_E_ARG *)
        assert (Hcm2 : 255 < TW.Cfg_max_cmds Bw).
        { rewrite branch_ltu_U, V35, V255, sinit_cond_255 in Hc2 by lia.
          apply Z.ltb_lt in Hc2. exact Hc2. }
        destruct (sinit_m_cfg Bw Bw' io_ctx io_send io_recv io_now ntf ctx r
          ltac:(right; left; exact Hcm2) Hm) as [EBw Er].
        (* the epilogue and `ret` *)
        paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
        { sinit_awr_norm. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
        assert (KRe : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
          aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) memc a).
        { intros a Ha H1.
          assert (Hk : aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) (ms_mem ms3) a).
          { apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr); [| exact Ha | exact H1].
            intros bq wlo whi x Hx Hxx. cbv beta. sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia; repeat rewrite ew_ewset_other in Hxx by lia; rewrite ?Usp in Hxx; lia). }
          rewrite Hk. apply KR5; assumption. }
        assert (GAe : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms4) a)
          by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA5 a Ha))).
        clear HF HFr HG.
        lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ _) => set (EX := EF) in HS end.
        assert (HEF : forall n, (n < 1024)%nat -> ew EX n = ew E0 n)
          by (intros n Hn; unfold EX; repeat rewrite ew_ewset_other by lia; reflexivity).
        sinit_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
          ltac:(cbn [sv_denot]; rewrite HEF by lia;
                rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
        sinit_reg HS (Z_to_bv 5 10) (w64 r) RF10
          ltac:(rewrite Er; cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity).
        assert (HPF : aregs_preserved regs (ms_regs ms4)).
        { apply (aregs_preserved_of_st_ok segs (w_H W) EX _ ms4 regs
            [w64 SHADOW_OFF; w64 io_send; w64 (TW.u_at Bw (TW.OFF_g_cfg + 12) 4);
             w64 (TW.u_at Bw (TW.OFF_g_cfg + 52) 4); w64 (TW.u_at Bw (TW.OFF_g_cfg + 56) 4)] HS).
          - apply sinit_agree; [intros n Hn; rewrite HEF by lia; reflexivity | reflexivity].
          - vm_compute. reflexivity. }
        eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
        intros mat'.
        rewrite EBw.
        exact (sinit_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r Bw
          (ms_regs ms4) (ms_mem ms4) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ
          ltac:(intros a Ha H1 H2; apply KRe; [lia | lia])
          GAe
          ltac:(apply (sinit_tw_keep W memc (ms_mem ms4) Bw Htw); intros a Ha; apply KRe;
                unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Ha; lia)
          HPF RF1 RF10 mat').
      ** (* max_cmds <= 255 *)
        assert (Hcm2 : TW.Cfg_max_cmds Bw <= 255).
        { rewrite branch_ltu_U, V35, V255, sinit_cond_255 in Hc2 by lia.
          apply Z.ltb_ge in Hc2. exact Hc2. }
        (* run 6: `addiw` and `bltu` on max_body *)
        paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
        { sinit_awr_norm. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
        assert (KR6 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
          aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) memc a).
        { intros a Ha H1.
          assert (Hk : aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) (ms_mem ms3) a).
          { apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr); [| exact Ha | exact H1].
            intros bq wlo whi x Hx Hxx. cbv beta. sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia; repeat rewrite ew_ewset_other in Hxx by lia; rewrite ?Usp in Hxx; lia). }
          rewrite Hk. apply KR5; assumption. }
        assert (GA6 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms4) a)
          by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA5 a Ha))).
        clear HF HFr HG.
        lazymatch type of HS with st_ok_pi _ _ ?EF _ _ =>
          assert (V36 : U EF (SAluw ALU_ADD (SExt true 32 (SOff 36%nat 0)) (SLit (-1485)))
            = bv_unsigned (Z_to_bv 64 (zalu32 ALU_ADD (bv_swrap 32 (TW.u_at Bw (TW.OFF_g_cfg + 56) 4)) (-1485))))
            by (apply (sinit_U_body EF 36%nat _ (sinit_u4 Bw (TW.OFF_g_cfg + 56)));
                repeat rewrite ew_ewset_other by lia; exact E36);
          assert (VB : U EF (SLit 18446744073709550155) = 18446744073709550155)
            by (unfold U; cbn [sv_denot]; vm_compute; reflexivity)
        end.
        psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
        *** (* max_body outside [24, 1484]: DIGINET_E_ARG *)
          assert (Hmb : TW.Cfg_max_body Bw < 24 \/ 1484 < TW.Cfg_max_body Bw).
          { rewrite branch_ltu_U, V36, VB, sinit_cond_body in Hc3 by lia.
            apply Bool.orb_true_iff in Hc3. destruct Hc3 as [HH | HH];
              [left; apply Z.ltb_lt in HH | right; apply Z.ltb_lt in HH]; exact HH. }
          destruct (sinit_m_cfg Bw Bw' io_ctx io_send io_recv io_now ntf ctx r
            ltac:(right; right; exact Hmb) Hm) as [EBw Er].
          (* the epilogue and `ret` *)
          paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
          { sinit_awr_norm. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
          assert (KRe : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
            aview segs (w_H W) (ms_mem ms5) a = aview segs (w_H W) memc a).
          { intros a Ha H1.
            assert (Hk : aview segs (w_H W) (ms_mem ms5) a = aview segs (w_H W) (ms_mem ms4) a).
            { apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr); [| exact Ha | exact H1].
              intros bq wlo whi x Hx Hxx. cbv beta. sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia; repeat rewrite ew_ewset_other in Hxx by lia; rewrite ?Usp in Hxx; lia). }
            rewrite Hk. apply KR6; assumption. }
          assert (GAe : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms5) a)
            by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA6 a Ha))).
          clear HF HFr HG.
          lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ _) => set (EX := EF) in HS end.
          assert (HEF : forall n, (n < 1024)%nat -> ew EX n = ew E0 n)
            by (intros n Hn; unfold EX; repeat rewrite ew_ewset_other by lia; reflexivity).
          sinit_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
            ltac:(cbn [sv_denot]; rewrite HEF by lia;
                  rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
          sinit_reg HS (Z_to_bv 5 10) (w64 r) RF10
            ltac:(rewrite Er; cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity).
          assert (HPF : aregs_preserved regs (ms_regs ms5)).
          { apply (aregs_preserved_of_st_ok segs (w_H W) EX _ ms5 regs
              [w64 SHADOW_OFF; w64 io_send; w64 (TW.u_at Bw (TW.OFF_g_cfg + 12) 4);
               w64 (TW.u_at Bw (TW.OFF_g_cfg + 52) 4); w64 (TW.u_at Bw (TW.OFF_g_cfg + 56) 4)] HS).
            - apply sinit_agree; [intros n Hn; rewrite HEF by lia; reflexivity | reflexivity].
            - vm_compute. reflexivity. }
          eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
          intros mat'.
          rewrite EBw.
          exact (sinit_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r Bw
            (ms_regs ms5) (ms_mem ms5) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ
            ltac:(intros a Ha H1 H2; apply KRe; [lia | lia])
            GAe
            ltac:(apply (sinit_tw_keep W memc (ms_mem ms5) Bw Htw); intros a Ha; apply KRe;
                  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Ha; lia)
            HPF RF1 RF10 mat').
        *** (* max_body in [24, 1484] *)
          assert (Hmb : 24 <= TW.Cfg_max_body Bw <= 1484).
          { rewrite branch_ltu_U, V36, VB, sinit_cond_body in Hc3 by lia.
            apply Bool.orb_false_iff in Hc3. destruct Hc3 as [H1 H2].
            apply Z.ltb_ge in H1. apply Z.ltb_ge in H2. unfold TW.Cfg_max_body, TW.A_Cfg_max_body. lia. }
          (* run 7: the memset arguments and `jal __asan_memset` *)
          paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
          { sinit_awr_norm. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
          assert (KR7 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
            aview segs (w_H W) (ms_mem ms5) a = aview segs (w_H W) memc a).
          { intros a Ha H1.
            assert (Hk : aview segs (w_H W) (ms_mem ms5) a = aview segs (w_H W) (ms_mem ms4) a).
            { apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr);
                [| exact Ha | exact H1].
              intros bq wlo whi x Hx Hxx. cbv beta.
              sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia; repeat rewrite ew_ewset_other in Hxx by lia; rewrite ?Usp in Hxx; lia). }
            rewrite Hk. apply KR6; assumption. }
          assert (GA7 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms5) a)
            by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA6 a Ha))).
          clear HF HFr HG.
          pmkst HS.
          sinit_reg HS (Z_to_bv 5 10) (Z_to_bv 64 SINIT_S) Q10
            ltac:(cbn [sv_denot]; repeat rewrite ew_ewset_other by lia;
                  rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
          sinit_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
          sinit_reg HS (Z_to_bv 5 12) (Z_to_bv 64 18264) Q12 ltac:(reflexivity).
          sinit_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 64)) Q2
            ltac:(cbn [sv_denot]; repeat rewrite ew_ewset_other by lia; rewrite Usp; f_equal; lia).
          sinit_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 22088)) R1
            ltac:(apply codeptr_val; assumption).
          sinit_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
            ltac:(cbn [sv_denot]; repeat rewrite ew_ewset_other by lia;
                  rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
          sinit_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
            ltac:(cbn [sv_denot]; repeat rewrite ew_ewset_other by lia;
                  rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
          assert (ESP : bv_unsigned (YK11.getr (ms_regs ms5) (Z_to_bv 5 2)) = spZ regs - 64)
            by (rewrite Q2; apply unsigned_lit_small; lia).
          assert (Hsp1 : spZ (ms_regs ms5) = spZ regs - 64) by exact ESP.
          pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR5.
          lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
            change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom)
              mdx) Q) end.
          eapply SRr_bind.
          { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OSet
              (transportb_sigma TB___asan_memset) (HSET fx) TG.G_HARNESS_B W (ms_regs ms5) (ms_mem ms5)
              STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
              SINIT_S 0 18264 (spZ regs - 64 - sp0) (Z_to_bv 64 (BASE + 22088)) HGX G_HARNESS_B_rw HJ Q10 Q11 Q12).
            - lia.
            - unfold SINIT_S, TB_g_s; lia.
            - unfold SINIT_S, TB_g_s; lia.
            - rewrite Hsp1. lia.
            - exact Hm16.
            - lia.
            - lia.
            - exact R3.
            - exact R4.
            - exact R1.
            - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
            - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|].
              intros a Ha. right. apply sinit_inG_s. unfold TW.SZ_g_s; lia.
            - left. unfold kLowMemEnd, SINIT_S, TB_g_s. lia.
            - exact (sinit_s_ra lyc Sc W (ms_mem ms5) _ HSI HAR5).
            - intros _. exact (sinit_hull_s lyc Sc W (ms_mem ms5) _ SINIT_S 18264 HSI HAR5
                ltac:(sinit_hb) ltac:(sinit_hb)).
            - exact I. }
          cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset2 & Heff2 & Hgr2).
          (* the memset's post: g_s is zeroed, nothing else changed *)
          assert (KAm : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SINIT_STK <= a < spZ regs) ->
            ~ (SINIT_S <= a < SINIT_S + TW.SZ_g_s) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memc a).
          { intros a Ha H1 H2. rewrite (Heff2 a Ha ltac:(unfold TW.SZ_g_s in *; lia) ltac:(lia)).
            apply KR7; [exact Ha | lia]. }
          assert (KZm : forall i, 0 <= i < TW.SZ_g_s -> aview segs (w_H W) mem2 (SINIT_S + i) = Some 0)
            by (intros i Hi; rewrite (Hset2 i ltac:(unfold TW.SZ_g_s in *; lia)); reflexivity).
          assert (GAm : forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)
            by (intros a Ha; apply Hgr2; apply GA7; exact Ha).
          assert (Htwm : tw_at TMAP_B (aview segs (w_H W) mem2)
            (TW.upd Bw TW.OFF_g_s (TW.put (Z.to_nat TW.SZ_g_s) 0))).
          { pose proof (tw_fill_zero TMAP_B (aview segs (w_H W) memc) (aview segs (w_H W) mem2) Bw
              TW.OFF_g_s TB_g_s TW.SZ_g_s 0 (Z.to_nat TW.SZ_g_s) TMAP_B_ok Htw TMAP_B_g_s ltac:(lia)
              ltac:(rewrite Z2Nat.id by (unfold TW.SZ_g_s; lia); lia)
              ltac:(intros i Hi; rewrite Z2Nat.id in Hi by (unfold TW.SZ_g_s; lia);
                    rewrite Z.add_0_r; apply KZm; lia)
              ltac:(intros x Hx Hn; rewrite Z.add_0_r in Hn;
                    rewrite Z2Nat.id in Hn by (unfold TW.SZ_g_s; lia);
                    pose proof (TMAP_B_hull x Hx) as Hh;
                    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh;
                    apply KAm; [lia | lia | unfold SINIT_S, TB_g_s in *; lia])) as HT.
            rewrite Z.add_0_r in HT. exact HT. }
          (* the regions the call keeps *)
          jafter_call_keep_hi HS 2048%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat] HS2.
          match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
          { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
            - apply (region_kept_aview _ _ _ _ 11%nat SINIT_CFG);
                [ repeat rewrite ew_ewset_other by lia; exact U11 | | exact Hgr2 ].
              intros a Ha. apply Heff2;
                [ unfold SINIT_CFG, TB_g_cfg in *; lia
                | unfold SINIT_CFG, TB_g_cfg, SINIT_S, TB_g_s, TW.SZ_g_s in *; lia
                | unfold SINIT_CFG, TB_g_cfg in *; lia ].
            - apply (region_kept_aview _ _ _ _ 2%nat (spZ regs));
                [ repeat rewrite ew_ewset_other by lia; exact Usp | | exact Hgr2 ].
              intros a Ha. apply Heff2;
                [ lia
                | unfold SINIT_S, TB_g_s, TW.SZ_g_s in *; lia
                | lia ]. }
          specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
          pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR6.
          clear SHOK.
          lazymatch type of HS with st_ok_pi _ _ ?EF _ _ =>
            assert (HEIc : img_env VAL A_LIM EF) by (apply img_env_havoc_hi; [assumption | cbv; lia]);
            assert (SHOK : sh_ok segs SINIT_BX SINIT_SHCFG EF (mrestrict (w_H W) mem2))
              by (apply (sinit_shok_cfg lyc Sc W mem2 _ EF HSC HAR6);
                  [ rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact E11
                  | rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact E32 ]);
            assert (HEc : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
              by (intros n Hn; rewrite ew_havoc_old by lia;
                  repeat rewrite ew_ewset_other by lia; reflexivity)
          end.
          (* run 8: the first memcpy's arguments and `jal __asan_memcpy` *)
          paj_run_tok RUN HS HJ2 SHOK YC1i.Bspan.
          { sinit_awr_norm. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
          assert (KC1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
            aview segs (w_H W) (ms_mem ms6) a = aview segs (w_H W) mem2 a).
          { intros a Ha H1.
            apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr);
              [| exact Ha | exact H1].
            intros bq wlo whi x Hx Hxx. cbv beta.
            sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia;
                                   repeat rewrite ew_ewset_other in Hxx by lia; rewrite ?Usp in Hxx; lia). }
          assert (GC1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms6) a)
            by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
          clear HF HFr HG.
          assert (Htwc1 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms6))
            (TW.upd Bw TW.OFF_g_s (TW.put (Z.to_nat TW.SZ_g_s) 0))).
          { apply (sinit_tw_keep W mem2 (ms_mem ms6) _ Htwm). intros a Ha. apply KC1;
              [ unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Ha; lia
              | unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Ha; lia ]. }
          pmkst HS.
          sinit_reg HS (Z_to_bv 5 10) (Z_to_bv 64 SINIT_S) P10
            ltac:(cbn [sv_denot]; rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia;
                  rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
          sinit_reg HS (Z_to_bv 5 11) (Z_to_bv 64 SINIT_CFG) P11
            ltac:(cbn [sv_denot]; rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia;
                  rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
          sinit_reg HS (Z_to_bv 5 12) (Z_to_bv 64 60) P12 ltac:(reflexivity).
          sinit_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 64)) P2
            ltac:(cbn [sv_denot]; rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia;
                  rewrite Usp; f_equal; lia).
          sinit_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 22112)) P1
            ltac:(apply codeptr_val; assumption).
          sinit_reg HS (3%bv : bv 5) (w64 (as_gp B)) P3
            ltac:(cbn [sv_denot]; rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia;
                  rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
          sinit_reg HS (4%bv : bv 5) (w64 (as_tp B)) P4
            ltac:(cbn [sv_denot]; rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia;
                  rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
          assert (ESP1 : bv_unsigned (YK11.getr (ms_regs ms6) (Z_to_bv 5 2)) = spZ regs - 64)
            by (rewrite P2; apply unsigned_lit_small; lia).
          assert (Hsp2 : spZ (ms_regs ms6) = spZ regs - 64) by exact ESP1.
          pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR7.
          lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
            change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom)
              mdx) Q) end.
          eapply SRr_bind.
          { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OCpy
              (transportb_sigma TB___asan_memcpy) (HCPY fx) TG.G_HARNESS_B W (ms_regs ms6) (ms_mem ms6)
              STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
              SINIT_S SINIT_CFG 60 (spZ regs - 64 - sp0) (Z_to_bv 64 (BASE + 22112)) HGX G_HARNESS_B_rw HJ2
              P10 P11 P12).
            - lia.
            - unfold SINIT_S, TB_g_s; lia.
            - unfold SINIT_S, TB_g_s; lia.
            - rewrite Hsp2. lia.
            - exact Hm16.
            - lia.
            - lia.
            - exact P3.
            - exact P4.
            - exact P1.
            - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
            - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|].
              intros a Ha. right. apply sinit_inG_s. unfold TW.SZ_g_s; lia.
            - left. unfold kLowMemEnd, SINIT_S, TB_g_s. lia.
            - apply (range_addressable_sub _ _ SINIT_S TW.SZ_g_s);
                [ exact (sinit_s_ra lyc Sc W (ms_mem ms6) _ HSI HAR7)
                | unfold SINIT_S, TB_g_s; lia | unfold SINIT_S, TB_g_s, TW.SZ_g_s; lia ].
            - intros _. exact (sinit_hull_s lyc Sc W (ms_mem ms6) _ SINIT_S 60 HSI HAR7
                ltac:(sinit_hb) ltac:(sinit_hb)).
            - split; [unfold SINIT_CFG, TB_g_cfg; lia|].
              split; [unfold SINIT_CFG, TB_g_cfg; lia|].
              split.
              { intros a Ha. split.
                - apply (gx_rw_vis segs TG.G_HARNESS_B a G_HARNESS_B_rw).
                  apply sinit_inG_cfg. unfold TW.SZ_g_cfg; lia.
                - rewrite Hsp2. unfold SINIT_CFG, TB_g_cfg in *. lia. }
              split; [unfold SINIT_S, TB_g_s, SINIT_CFG, TB_g_cfg; lia|].
              split; [left; unfold kLowMemEnd, SINIT_CFG, TB_g_cfg; lia|].
              split.
              { exact (sinit_cfg_ra lyc Sc W (ms_mem ms6) _ HSC HAR7). }
              intros _. exact (sinit_hull_cfg lyc Sc W (ms_mem ms6) _ SINIT_CFG 60 HSC HAR7
                ltac:(sinit_hb) ltac:(sinit_hb)). }
          cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hcpy3 & Heff3 & Hgr3).
          (* the first memcpy's post: g_cfg's 60 bytes at g_s *)
          assert (Lsub60 : Z.of_nat (length (TW.sub Bw TW.OFF_g_cfg (Z.to_nat TW.SZ_g_cfg))) = 60)
            by (exact (sinit_lsub Bw HLB)).
          assert (Esub : TW.sub (TW.upd Bw TW.OFF_g_s (TW.put (Z.to_nat TW.SZ_g_s) 0))
              TW.OFF_g_cfg (Z.to_nat TW.SZ_g_cfg) = TW.sub Bw TW.OFF_g_cfg (Z.to_nat TW.SZ_g_cfg)).
          { apply TWL.sub_upd_out;
              [ unfold TW.OFF_g_s; lia | unfold TW.OFF_g_cfg; lia
              | rewrite sinit_lput; right; unfold TW.OFF_g_s, TW.OFF_g_cfg; lia
              | rewrite sinit_lput, HLB; unfold TW.OFF_g_s, TW.W_LEN; lia ]. }
          assert (KAp1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SINIT_STK <= a < spZ regs) ->
            ~ (SINIT_S <= a < SINIT_S + TW.SZ_g_s) -> aview segs (w_H W) mem3 a = aview segs (w_H W) mem2 a).
          { intros a Ha H1 H2. rewrite (Heff3 a Ha ltac:(unfold TW.SZ_g_s in *; lia) ltac:(lia)).
            apply KC1; [exact Ha | lia]. }
          assert (GAp1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a)
            by (intros a Ha; apply Hgr3; apply GC1; exact Ha).
          assert (Htwc2 : tw_at TMAP_B (aview segs (w_H W) mem3)
            (TW.upd (TW.upd Bw TW.OFF_g_s (TW.put (Z.to_nat TW.SZ_g_s) 0)) TW.OFF_g_s
               (TW.sub Bw TW.OFF_g_cfg (Z.to_nat TW.SZ_g_cfg)))).
          { pose proof (tw_upd TMAP_B (aview segs (w_H W) (ms_mem ms6)) (aview segs (w_H W) mem3)
              (TW.upd Bw TW.OFF_g_s (TW.put (Z.to_nat TW.SZ_g_s) 0))
              TW.OFF_g_s TB_g_s TW.SZ_g_s 0 (TW.sub Bw TW.OFF_g_cfg (Z.to_nat TW.SZ_g_cfg))
              TMAP_B_ok Htwc1 TMAP_B_g_s ltac:(lia) ltac:(rewrite Lsub60; unfold TW.SZ_g_s; lia)
              ltac:(intros j Hj;
                    assert (Hj' : 0 <= Z.of_nat j < 60) by (rewrite <- Lsub60; lia);
                    rewrite Z.add_0_r;
                    change (TB_g_s + Z.of_nat j) with (SINIT_S + Z.of_nat j);
                    rewrite (Hcpy3 (Z.of_nat j) ltac:(lia));
                    rewrite (sinit_cfg_bytes W (ms_mem ms6) _ (Z.of_nat j) Htwc1 Hj');
                    rewrite Esub, Nat2Z.id; reflexivity)
              ltac:(intros x Hx Hn; rewrite Z.add_0_r, Lsub60 in Hn;
                    pose proof (TMAP_B_hull x Hx) as Hh;
                    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh;
                    apply Heff3; [lia | unfold SINIT_S, TB_g_s in *; lia | lia])) as HT.
            rewrite Z.add_0_r in HT. exact HT. }
          (* the regions the first memcpy keeps *)
          jafter_call_keep_hi HS 2080%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat; 1%nat] HS3.
          match type of HS3 with ?tq -> _ => assert (HRK : tq) end.
          { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
            - apply (region_kept_aview _ _ _ _ 11%nat SINIT_CFG);
                [ rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact U11
                | | exact Hgr3 ].
              intros a Ha. apply Heff3;
                [ unfold SINIT_CFG, TB_g_cfg in *; lia
                | unfold SINIT_CFG, TB_g_cfg, SINIT_S, TB_g_s in *; lia
                | unfold SINIT_CFG, TB_g_cfg in *; lia ].
            - apply (region_kept_aview _ _ _ _ 2%nat (spZ regs));
                [ rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact Usp
                | | exact Hgr3 ].
              intros a Ha. apply Heff3;
                [ lia | unfold SINIT_S, TB_g_s in *; lia | lia ]. }
          specialize (HS3 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
          pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR8.
          clear SHOK.
          lazymatch type of HS with st_ok_pi _ _ ?EF _ _ =>
            assert (HEId : img_env VAL A_LIM EF) by (apply img_env_havoc_hi; [assumption | cbv; lia]);
            assert (SHOK : sh_ok segs SINIT_BX SINIT_SHCFG EF (mrestrict (w_H W) mem3))
              by (apply (sinit_shok_cfg lyc Sc W mem3 _ EF HSC HAR8);
                  [ repeat rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact E11
                  | repeat rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact E32 ])
          end.
          (* run 9: the second memcpy's arguments and `jal __asan_memcpy` *)
          paj_run_tok RUN HS HJ3 SHOK YC1i.Bspan.
          { sinit_awr_norm. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
          assert (KC2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
            aview segs (w_H W) (ms_mem ms7) a = aview segs (w_H W) mem3 a).
          { intros a Ha H1.
            apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr);
              [| exact Ha | exact H1].
            intros bq wlo whi x Hx Hxx. cbv beta.
            sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia;
                                   repeat rewrite ew_ewset_other in Hxx by lia; rewrite ?Usp in Hxx; lia). }
          assert (GC2 : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms7) a)
            by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
          clear HF HFr HG.
          assert (Htwc3 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms7))
            (TW.upd (TW.upd Bw TW.OFF_g_s (TW.put (Z.to_nat TW.SZ_g_s) 0)) TW.OFF_g_s
               (TW.sub Bw TW.OFF_g_cfg (Z.to_nat TW.SZ_g_cfg)))).
          { apply (sinit_tw_keep W mem3 (ms_mem ms7) _ Htwc2). intros a Ha. apply KC2;
              [ unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Ha; lia
              | unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Ha; lia ]. }
          (* the caller's io block and the shadow band are still the entry's *)
          assert (KIO3 : forall a, iop <= a < iop + 32 ->
            aview segs (w_H W) (ms_mem ms7) a = aview segs (w_H W) memc a).
          { intros a Ha. pose proof (HIOS a Ha) as HS1. pose proof (HIOW2 a Ha) as HS2.
            unfold TW.SZ_g_s in HS1.
            rewrite (KC2 a ltac:(lia) ltac:(lia)).
            rewrite (Heff3 a ltac:(lia) ltac:(lia) ltac:(lia)).
            rewrite (KC1 a ltac:(lia) ltac:(lia)).
            rewrite (Heff2 a ltac:(lia) ltac:(lia) ltac:(lia)).
            apply KR7; [lia | lia]. }
          assert (KSH3 : forall s0, SHADOW_OFF <= s0 < SHADOW_OFF + 2 ^ 44 + 8 ->
            aview segs (w_H W) (ms_mem ms7) s0 = aview segs (w_H W) memc s0).
          { intros s0 Hs0. unfold SHADOW_OFF in Hs0.
            rewrite (KC2 s0 ltac:(lia) ltac:(lia)).
            rewrite (Heff3 s0 ltac:(lia) ltac:(unfold SINIT_S, TB_g_s in *; lia) ltac:(lia)).
            rewrite (KC1 s0 ltac:(lia) ltac:(lia)).
            rewrite (Heff2 s0 ltac:(lia) ltac:(unfold SINIT_S, TB_g_s, TW.SZ_g_s in *; lia) ltac:(lia)).
            apply KR7; [lia | lia]. }
          assert (HRD3 : decode_rd_ok W (ms_mem ms7) iop SINIT_IO_LEN)
            by (apply (sinit_rd_kept W memc (ms_mem ms7) iop SINIT_IO_LEN ltac:(lia) ltac:(lia) ltac:(lia)
                 HRD); [exact KIO3 | exact KSH3]).
          pmkst HS.
          sinit_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (SINIT_S + 64)) R210
            ltac:(cbn [sv_denot]; repeat rewrite ew_havoc_old by lia;
                  repeat rewrite ew_ewset_other by lia; rewrite E10;
                  rewrite unsigned_lit_small by (unfold SINIT_S, TB_g_s; lia); reflexivity).
          sinit_reg HS (Z_to_bv 5 11) (Z_to_bv 64 iop) R211
            ltac:(cbn [sv_denot]; repeat rewrite ew_havoc_old by lia;
                  repeat rewrite ew_ewset_other by lia; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned;
                  reflexivity).
          sinit_reg HS (Z_to_bv 5 12) (Z_to_bv 64 32) R212 ltac:(reflexivity).
          sinit_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 64)) R22
            ltac:(cbn [sv_denot]; repeat rewrite ew_havoc_old by lia;
                  repeat rewrite ew_ewset_other by lia; rewrite Usp; f_equal; lia).
          sinit_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 22128)) R21
            ltac:(apply codeptr_val; assumption).
          sinit_reg HS (3%bv : bv 5) (w64 (as_gp B)) R23
            ltac:(cbn [sv_denot]; repeat rewrite ew_havoc_old by lia;
                  repeat rewrite ew_ewset_other by lia;
                  rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
          sinit_reg HS (4%bv : bv 5) (w64 (as_tp B)) R24
            ltac:(cbn [sv_denot]; repeat rewrite ew_havoc_old by lia;
                  repeat rewrite ew_ewset_other by lia;
                  rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
          assert (ESP2 : bv_unsigned (YK11.getr (ms_regs ms7) (Z_to_bv 5 2)) = spZ regs - 64)
            by (rewrite R22; apply unsigned_lit_small; lia).
          assert (Hsp3 : spZ (ms_regs ms7) = spZ regs - 64) by exact ESP2.
          pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR9.
          lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
            change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom)
              mdx) Q) end.
          eapply SRr_bind.
          { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OCpy
              (transportb_sigma TB___asan_memcpy) (HCPY fx) TG.G_HARNESS_B W (ms_regs ms7) (ms_mem ms7)
              STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
              (SINIT_S + 64) iop 32 (spZ regs - 64 - sp0) (Z_to_bv 64 (BASE + 22128)) HGX G_HARNESS_B_rw HJ3
              R210 R211 R212).
            - lia.
            - unfold SINIT_S, TB_g_s; lia.
            - unfold SINIT_S, TB_g_s; lia.
            - rewrite Hsp3. lia.
            - exact Hm16.
            - lia.
            - lia.
            - exact R23.
            - exact R24.
            - exact R21.
            - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
            - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ3|].
              intros a Ha. right. apply sinit_inG_s. unfold TW.SZ_g_s; lia.
            - left. unfold kLowMemEnd, SINIT_S, TB_g_s. lia.
            - apply (range_addressable_sub _ _ SINIT_S TW.SZ_g_s);
                [ exact (sinit_s_ra lyc Sc W (ms_mem ms7) _ HSI HAR9)
                | unfold SINIT_S, TB_g_s; lia | unfold SINIT_S, TB_g_s, TW.SZ_g_s; lia ].
            - intros _. exact (sinit_hull_s lyc Sc W (ms_mem ms7) _ (SINIT_S + 64) 32 HSI HAR9
                ltac:(sinit_hb) ltac:(sinit_hb)).
            - destruct HRD3 as (Hv3 & Hra3 & Hh3 & Ham3 & Hq3 & Hq63).
              split; [lia|]. split; [unfold SINIT_IO_LEN in *; lia|].
              split.
              { intros a Ha. split; [apply Hv3; unfold SINIT_IO_LEN; lia|].
                rewrite Hsp3. unfold decode_off_win, SINIT_STK in HOFF. lia. }
              split; [unfold SINIT_S, TB_g_s, SINIT_IO_LEN, TW.SZ_g_s in *; lia|].
              split; [unfold SINIT_IO_LEN in Ham3; exact Ham3|].
              split; [unfold SINIT_IO_LEN in Hra3; exact Hra3|].
              intros _. unfold SINIT_IO_LEN in Hh3. exact Hh3. }
          cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & _ & Hcpy4 & Heff4 & Hgr4).
          (* the second memcpy's post: the caller's 32 io bytes at g_s + 64 *)
          assert (Liob : Z.of_nat (length (sinit_io_bytes io_ctx io_send io_recv io_now)) = 32)
            by (unfold sinit_io_bytes; rewrite !length_app, !TWL.length_put; reflexivity).
          assert (KAp2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SINIT_STK <= a < spZ regs) ->
            ~ (SINIT_S <= a < SINIT_S + TW.SZ_g_s) ->
            aview segs (w_H W) mem4 a = aview segs (w_H W) (ms_mem ms7) a).
          { intros a Ha H1 H2. apply Heff4; [exact Ha | unfold TW.SZ_g_s in *; lia | lia]. }
          assert (Htwc4 : tw_at TMAP_B (aview segs (w_H W) mem4)
            (TW.upd (TW.upd (TW.upd Bw TW.OFF_g_s (TW.put (Z.to_nat TW.SZ_g_s) 0)) TW.OFF_g_s
               (TW.sub Bw TW.OFF_g_cfg (Z.to_nat TW.SZ_g_cfg)))
               (TW.OFF_g_s + 64) (sinit_io_bytes io_ctx io_send io_recv io_now))).
          { apply (tw_upd TMAP_B (aview segs (w_H W) (ms_mem ms7)) (aview segs (w_H W) mem4) _
              TW.OFF_g_s TB_g_s TW.SZ_g_s 64 (sinit_io_bytes io_ctx io_send io_recv io_now)
              TMAP_B_ok Htwc3 TMAP_B_g_s ltac:(lia) ltac:(rewrite Liob; unfold TW.SZ_g_s; lia)).
            - intros j Hj. assert (Hj' : 0 <= Z.of_nat j < 32) by (rewrite <- Liob; lia).
              change (TB_g_s + 64 + Z.of_nat j) with (SINIT_S + 64 + Z.of_nat j).
              rewrite (Hcpy4 (Z.of_nat j) ltac:(lia)).
              rewrite (KIO3 (iop + Z.of_nat j) ltac:(lia)).
              rewrite (sinit_iob_byte W memc iop io_ctx io_send io_recv io_now (Z.of_nat j) HIOB Hj').
              rewrite Nat2Z.id. reflexivity.
            - intros x Hx Hn. rewrite Liob in Hn.
              pose proof (TMAP_B_hull x Hx) as Hh.
              unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
              apply Heff4; [lia | unfold SINIT_S, TB_g_s in *; lia | lia]. }
          (* the regions the second memcpy keeps, and the region of the three stores *)
          jafter_call_keep_hi HS 2112%nat regs4 (mrestrict (w_H W) mem4) HP4 [0%nat; 1%nat] HS4.
          match type of HS4 with ?tq -> _ => assert (HRK : tq) end.
          { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
            - apply (region_kept_aview _ _ _ _ 11%nat SINIT_CFG);
                [ repeat rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact U11
                | | exact Hgr4 ].
              intros a Ha. apply Heff4;
                [ unfold SINIT_CFG, TB_g_cfg in *; lia
                | unfold SINIT_CFG, TB_g_cfg, SINIT_S, TB_g_s in *; lia
                | unfold SINIT_CFG, TB_g_cfg in *; lia ].
            - apply (region_kept_aview _ _ _ _ 2%nat (spZ regs));
                [ repeat rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact Usp
                | | exact Hgr4 ].
              intros a Ha. apply Heff4;
                [ lia | unfold SINIT_S, TB_g_s in *; lia | lia ]. }
          specialize (HS4 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
          pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR10.
          clear SHOK.
          lazymatch type of HS with st_ok_pi _ _ ?EF _ _ =>
            assert (HEIe : img_env VAL A_LIM EF) by (apply img_env_havoc_hi; [assumption | cbv; lia]);
            assert (QE10 : ew EF 10 = Z_to_bv 64 SINIT_S)
              by (repeat rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact E10);
            assert (QE11 : ew EF 11 = Z_to_bv 64 SINIT_CFG)
              by (repeat rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact E11);
            assert (QE32 : ew EF 32 = Z_to_bv 64 SHADOW_OFF)
              by (repeat rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact E32);
            assert (QU10 : bv_unsigned (ew EF 10) = SINIT_S)
              by (rewrite QE10; apply unsigned_lit_small; unfold SINIT_S, TB_g_s; lia);
            assert (QU11 : bv_unsigned (ew EF 11) = SINIT_CFG)
              by (rewrite QE11; apply unsigned_lit_small; unfold SINIT_CFG, TB_g_cfg; lia);
            assert (QUsp : bv_unsigned (ew EF 2) = spZ regs)
              by (repeat rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact Usp);
            pose proof (st_ok_pi_add_region EF _ _ SINIT_S_REG HS ltac:(vm_compute; reflexivity)
              (sinit_s_region_ok W mem4 EF 96 116 ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) QE10)
              ltac:(cbn [ss_mem all_disjoint]; split; [|split; [|exact I]];
                    unfold extent_disjoint, SINIT_S_REG;
                    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite QU10, ?QU11, ?QUsp;
                    unfold SINIT_S, TB_g_s, SINIT_CFG, TB_g_cfg; lia)) as HSa;
            assert (SHOK : sh_ok segs SINIT_BX SINIT_SHSC EF (mrestrict (w_H W) mem4))
              by (exact (sinit_shok_sc lyc Sc W mem4 _ EF HSC HSI HAR10 QE10 QE11 QE32))
          end.
          clear HS. rename HSa into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
          (* run 10: the three checked stores at s + 96 and the checked load of cfg + 12 *)
          paj_run_tok RUN HS HJ4 SHOK YC1i.Bspan.
          { sinit_awr_norm. sinit_awr_g U10. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
          assert (KRs : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
            ~ (SINIT_S + 96 <= a < SINIT_S + 116) ->
            aview segs (w_H W) (ms_mem ms8) a = aview segs (w_H W) mem4 a).
          { intros a Ha H1 H2.
            apply (kept_of_frame _ _ _ _ _
              (fun x => (spZ regs - 64 <= x < spZ regs) \/ (SINIT_S + 96 <= x < SINIT_S + 116)) HFr);
              [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
            intros bq wlo whi x Hx Hxx. cbv beta.
            sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia;
                                   repeat rewrite ew_ewset_other in Hxx by lia;
                                   rewrite ?Usp, ?U10 in Hxx; first [lia | left; lia | right; lia]). }
          assert (GAs : forall a, apresent (w_H W) mem4 a -> apresent (w_H W) (ms_mem ms8) a)
            by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
          clear HF HFr HG.
          lazymatch type of HS with st_ok_pi _ _ ?EF2 _ _ =>
            assert (QD34 : ew EF2 34 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_cfg + 12) 4))
              by (repeat rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact E34);
            assert (QD10 : bv_unsigned (ew EF2 10) = SINIT_S)
              by (repeat rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia; exact U10);
            assert (V34 : U EF2 (SExt true 32 (SOff 34%nat 0))
              = bv_unsigned (Z_to_bv 64 (bv_swrap 32 (TW.u_at Bw (TW.OFF_g_cfg + 12) 4))))
              by (apply (sinit_U_ext EF2 34%nat _ (sinit_u4 Bw (TW.OFF_g_cfg + 12)) QD34));
            assert (VD0 : U EF2 (SLit 0) = 0) by (unfold U; cbn [sv_denot]; vm_compute; reflexivity);
            assert (QE2 : forall n, (n < 1024)%nat -> ew EF2 n = ew E0 n)
              by (intros n Hn; repeat rewrite ew_havoc_old by lia;
                  repeat rewrite ew_ewset_other by lia; reflexivity)
          end.
          psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
          **** (* cfg->desk_mac_set = 0: return 0, no desk MAC *)
            assert (Hdk : TW.Cfg_desk_mac_set Bw = 0).
            { rewrite branch_eq_U, V34, VD0, sinit_cond_eq0 in Hc4 by lia.
              apply Z.eqb_eq in Hc4. unfold TW.Cfg_desk_mac_set, TW.A_Cfg_desk_mac_set, TW.s32_at.
              rewrite Hc4. reflexivity. }
            assert (Hu12 : TW.u_at Bw (TW.OFF_g_cfg + 12) 4 = 0).
            { unfold TW.Cfg_desk_mac_set, TW.A_Cfg_desk_mac_set, TW.s32_at in Hdk.
              rewrite sinit_swrap32 in Hdk by lia. revert Hdk.
              destruct (Z.ltb_spec (TW.u_at Bw (TW.OFF_g_cfg + 12) 4) (2 ^ 31)); lia. }
            destruct (sinit_m_ok0 Bw Bw' io_ctx io_send io_recv io_now ntf ctx r HLB Hsnd Hntf
              Hcm ltac:(lia) ltac:(lia) ltac:(lia) Hdk Hm) as [EBw Er].
            (* the epilogue and `ret` *)
            paj_run_tok RUN HS HJ4 SHOK YC1i.Bspan.
            { sinit_awr_norm. sinit_awr_g U10. sinit_awr_ro. sinit_awr_stack Usp. apply awr_ok_x_nil. }
            assert (KRf : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
              ~ (SINIT_S + 96 <= a < SINIT_S + 116) ->
              aview segs (w_H W) (ms_mem ms9) a = aview segs (w_H W) (ms_mem ms8) a).
            { intros a Ha H1 H2.
              apply (kept_of_frame _ _ _ _ _
                (fun x => (spZ regs - 64 <= x < spZ regs) \/ (SINIT_S + 96 <= x < SINIT_S + 116)) HFr);
                [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
              intros bq wlo whi x Hx Hxx. cbv beta.
              sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia;
                                     repeat rewrite ew_ewset_other in Hxx by lia;
                                     rewrite ?Usp, ?U10 in Hxx; first [lia | left; lia | right; lia]). }
            assert (GAf : forall a, apresent (w_H W) mem4 a -> apresent (w_H W) (ms_mem ms9) a)
              by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAs a Ha))).
            clear HF HFr HG.
            lazymatch type of HS with st_ok_pi _ _ ?EF3 _ (restrict _ _) => set (EZ := EF3) in HS end.
            assert (HEZ : forall n, (n < 1024)%nat -> ew EZ n = ew E0 n)
              by (intros n Hn; unfold EZ; repeat rewrite ew_havoc_old by lia;
                  repeat rewrite ew_ewset_other by lia; reflexivity).
            sinit_rgn HS 0%nat RGd.
            change (ms_mem (restrict (w_H W) ms9)) with (mrestrict (w_H W) (ms_mem ms9)) in RGd.
            assert (L20 : Z.of_nat (length (TW.put 8 ntf ++ TW.put 8 ctx ++ TW.put 4 0)) = 20)
              by (rewrite !length_app, !TWL.length_put; reflexivity).
            assert (HV20 : forall j, (j < 20)%nat ->
              aview segs (w_H W) (ms_mem ms9) (SINIT_S + 96 + Z.of_nat j)
              = Some (bv_unsigned (nth j (TW.put 8 ntf ++ TW.put 8 ctx ++ TW.put 4 0) (Z_to_bv 8 0)))).
            { intros j Hj. destruct (Nat.ltb_spec j 8) as [H8|H8].
              - rewrite app_nth1 by (rewrite TWL.length_put; lia).
                apply (sinit_store_byte W (ms_mem ms9) EZ 96 116 _ 96 8 (SOff 13%nat 0) ntf j RGd
                  ltac:(rewrite HEZ by lia; exact E10)
                  ltac:(cbn [In]; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity])
                  ltac:(cbn [sv_denot]; rewrite HEZ by lia; rewrite E13, Z.add_0_r, Z_to_bv_bv_unsigned;
                        reflexivity)
                  ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [N.to_nat]; lia)).
              - destruct (Nat.ltb_spec j 16) as [H16|H16].
                + rewrite app_nth2 by (rewrite TWL.length_put; lia). rewrite TWL.length_put.
                  rewrite app_nth1 by (rewrite TWL.length_put; lia).
                  replace (SINIT_S + 96 + Z.of_nat j) with (SINIT_S + 104 + Z.of_nat (j - 8)) by lia.
                  apply (sinit_store_byte W (ms_mem ms9) EZ 96 116 _ 104 8 (SOff 14%nat 0) ctx (j - 8) RGd
                    ltac:(rewrite HEZ by lia; exact E10)
                    ltac:(cbn [In]; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity])
                    ltac:(cbn [sv_denot]; rewrite HEZ by lia; rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned;
                          reflexivity)
                    ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [N.to_nat]; lia)).
                + rewrite app_nth2 by (rewrite TWL.length_put; lia). rewrite TWL.length_put.
                  rewrite app_nth2 by (rewrite TWL.length_put; lia). rewrite TWL.length_put.
                  replace (SINIT_S + 96 + Z.of_nat j) with (SINIT_S + 112 + Z.of_nat (j - 8 - 8)) by lia.
                  apply (sinit_store_byte W (ms_mem ms9) EZ 96 116 _ 112 4 (SLit 0) 0 (j - 8 - 8) RGd
                    ltac:(rewrite HEZ by lia; exact E10)
                    ltac:(cbn [In]; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity])
                    ltac:(cbn [sv_denot]; reflexivity)
                    ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [N.to_nat]; lia)). }
            assert (Htwf : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms9))
              (SINIT_W0 Bw io_ctx io_send io_recv io_now ntf ctx)).
            { unfold SINIT_W0, SINIT_IOB.
              apply (tw_upd TMAP_B (aview segs (w_H W) mem4) (aview segs (w_H W) (ms_mem ms9)) _
                TW.OFF_g_s TB_g_s TW.SZ_g_s 96 (TW.put 8 ntf ++ TW.put 8 ctx ++ TW.put 4 0)
                TMAP_B_ok Htwc4 TMAP_B_g_s ltac:(lia) ltac:(rewrite L20; unfold TW.SZ_g_s; lia)).
              - intros j Hj. assert (Hj20 : (j < 20)%nat) by lia.
                change (TB_g_s + 96 + Z.of_nat j) with (SINIT_S + 96 + Z.of_nat j).
                exact (HV20 j Hj20).
              - intros x Hx Hn. rewrite L20 in Hn. change TB_g_s with SINIT_S in Hn.
                pose proof (TMAP_B_hull x Hx) as Hh.
                unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
                unfold SINIT_S, TB_g_s in Hn |- *.
                rewrite (KRf x ltac:(lia) ltac:(lia) ltac:(lia)).
                apply KRs; [lia | lia | lia]. }
            (* the registers at the return *)
            sinit_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
              ltac:(cbn [sv_denot]; rewrite HEZ by lia;
                    rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
            sinit_reg HS (Z_to_bv 5 10) (w64 r) RF10
              ltac:(cbn [sv_denot]; rewrite HEZ by lia; rewrite E34, Hu12;
                    rewrite unsigned_lit_small by lia; rewrite Z.add_0_r;
                    rewrite sinit_lw by lia; rewrite Er; reflexivity).
            assert (HPF : aregs_preserved regs (ms_regs ms9)).
            { apply (aregs_preserved_of_st_ok segs (w_H W) EZ _ ms9 regs
                [w64 SHADOW_OFF; w64 io_send; w64 (TW.u_at Bw (TW.OFF_g_cfg + 12) 4);
                 w64 (TW.u_at Bw (TW.OFF_g_cfg + 52) 4); w64 (TW.u_at Bw (TW.OFF_g_cfg + 56) 4)] HS).
              - apply sinit_agree; [intros n Hn; rewrite HEZ by lia; reflexivity | reflexivity].
              - vm_compute. reflexivity. }
            eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
            intros mat'.
            rewrite EBw.
            exact (sinit_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r
              (SINIT_W0 Bw io_ctx io_send io_recv io_now ntf ctx)
              (ms_regs ms9) (ms_mem ms9) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ4
              ltac:(intros a Ha H1 H2;
                    assert (Hgs : ~ (SINIT_S <= a < SINIT_S + TW.SZ_g_s))
                      by (intros Hcg; apply H2; split; [exact Er | exact Hcg]);
                    unfold TW.SZ_g_s in Hgs;
                    rewrite (KRf a ltac:(lia) ltac:(lia) ltac:(lia));
                    rewrite (KRs a ltac:(lia) ltac:(lia) ltac:(lia));
                    rewrite (KAp2 a ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_g_s; lia));
                    rewrite (KC2 a ltac:(lia) ltac:(lia));
                    rewrite (KAp1 a ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_g_s; lia));
                    apply KAm; [lia | lia | unfold TW.SZ_g_s; lia])
              ltac:(intros a Ha; apply GAf; apply Hgr4; apply GC2; apply Hgr3; apply GC1; apply Hgr2;
                    apply GA7; exact Ha)
              Htwf HPF RF1 RF10 mat').
          **** (* cfg->desk_mac_set <> 0: the desk MAC memcpy *)
            assert (Hdk : TW.Cfg_desk_mac_set Bw <> 0).
            { rewrite branch_eq_U, V34, VD0, sinit_cond_eq0 in Hc4 by lia.
              unfold TW.Cfg_desk_mac_set, TW.A_Cfg_desk_mac_set, TW.s32_at.
              intros HH. assert (HU0 : TW.u_at Bw (TW.OFF_g_cfg + 12) 4 = 0).
              { pose proof (sinit_u4 Bw (TW.OFF_g_cfg + 12)) as HRg.
                rewrite sinit_swrap32 in HH by lia. revert HH.
                destruct (Z.ltb_spec (TW.u_at Bw (TW.OFF_g_cfg + 12) 4) (2 ^ 31)); lia. }
              rewrite HU0, Z.eqb_refl in Hc4. discriminate Hc4. }
            lazymatch type of HS with st_ok_pi _ _ ?EV _ _ => set (EB := EV) in * end.
            assert (UspB : bv_unsigned (ew EB 2) = spZ regs)
              by (unfold EB; repeat rewrite ew_havoc_old by lia;
                  repeat rewrite ew_ewset_other by lia; exact Usp).
            assert (U10B : bv_unsigned (ew EB 10) = SINIT_S)
              by (unfold EB; repeat rewrite ew_havoc_old by lia;
                  repeat rewrite ew_ewset_other by lia; exact U10).
            assert (Hu12 : TW.u_at Bw (TW.OFF_g_cfg + 12) 4 <> 0).
            { unfold TW.Cfg_desk_mac_set, TW.A_Cfg_desk_mac_set, TW.s32_at in Hdk.
              intros HH. apply Hdk. rewrite HH. reflexivity. }
            destruct (sinit_m_ok1 Bw Bw' io_ctx io_send io_recv io_now ntf ctx r HLB Hsnd Hntf
              Hcm ltac:(lia) ltac:(lia) ltac:(lia) Hdk Hm) as [EBw Er].
            (* the three fields the stores left, and the world after them *)
            sinit_rgn HS 0%nat RGe.
            change (ms_mem (restrict (w_H W) ms8)) with (mrestrict (w_H W) (ms_mem ms8)) in RGe.
            assert (L20 : Z.of_nat (length (TW.put 8 ntf ++ TW.put 8 ctx ++ TW.put 4 0)) = 20)
              by (rewrite !length_app, !TWL.length_put; reflexivity).
            assert (HV20 : forall j, (j < 20)%nat ->
              aview segs (w_H W) (ms_mem ms8) (SINIT_S + 96 + Z.of_nat j)
              = Some (bv_unsigned (nth j (TW.put 8 ntf ++ TW.put 8 ctx ++ TW.put 4 0) (Z_to_bv 8 0)))).
            { intros j Hj. destruct (Nat.ltb_spec j 8) as [H8|H8].
              - rewrite app_nth1 by (rewrite TWL.length_put; lia).
                apply (sinit_store_byte W (ms_mem ms8) EB 96 116 _ 96 8 (SOff 13%nat 0) ntf j RGe
                  ltac:(rewrite QE2 by lia; exact E10)
                  ltac:(cbn [In]; first [left; reflexivity | right; left; reflexivity
                                        | right; right; left; reflexivity])
                  ltac:(cbn [sv_denot]; rewrite QE2 by lia; rewrite E13, Z.add_0_r, Z_to_bv_bv_unsigned;
                        reflexivity)
                  ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [N.to_nat]; lia)).
              - destruct (Nat.ltb_spec j 16) as [H16|H16].
                + rewrite app_nth2 by (rewrite TWL.length_put; lia). rewrite TWL.length_put.
                  rewrite app_nth1 by (rewrite TWL.length_put; lia).
                  replace (SINIT_S + 96 + Z.of_nat j) with (SINIT_S + 104 + Z.of_nat (j - 8)) by lia.
                  apply (sinit_store_byte W (ms_mem ms8) EB 96 116 _ 104 8 (SOff 14%nat 0) ctx (j - 8) RGe
                    ltac:(rewrite QE2 by lia; exact E10)
                    ltac:(cbn [In]; first [left; reflexivity | right; left; reflexivity
                                          | right; right; left; reflexivity])
                    ltac:(cbn [sv_denot]; rewrite QE2 by lia; rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned;
                          reflexivity)
                    ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [N.to_nat]; lia)).
                + rewrite app_nth2 by (rewrite TWL.length_put; lia). rewrite TWL.length_put.
                  rewrite app_nth2 by (rewrite TWL.length_put; lia). rewrite TWL.length_put.
                  replace (SINIT_S + 96 + Z.of_nat j) with (SINIT_S + 112 + Z.of_nat (j - 8 - 8)) by lia.
                  apply (sinit_store_byte W (ms_mem ms8) EB 96 116 _ 112 4 (SLit 0) 0 (j - 8 - 8) RGe
                    ltac:(rewrite QE2 by lia; exact E10)
                    ltac:(cbn [In]; first [left; reflexivity | right; left; reflexivity
                                          | right; right; left; reflexivity])
                    ltac:(cbn [sv_denot]; reflexivity)
                    ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [N.to_nat]; lia)). }
            assert (Htw8 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms8))
              (SINIT_W0 Bw io_ctx io_send io_recv io_now ntf ctx)).
            { unfold SINIT_W0, SINIT_IOB.
              apply (tw_upd TMAP_B (aview segs (w_H W) mem4) (aview segs (w_H W) (ms_mem ms8)) _
                TW.OFF_g_s TB_g_s TW.SZ_g_s 96 (TW.put 8 ntf ++ TW.put 8 ctx ++ TW.put 4 0)
                TMAP_B_ok Htwc4 TMAP_B_g_s ltac:(lia) ltac:(rewrite L20; unfold TW.SZ_g_s; lia)).
              - intros j Hj. assert (Hj20 : (j < 20)%nat) by lia.
                change (TB_g_s + 96 + Z.of_nat j) with (SINIT_S + 96 + Z.of_nat j).
                exact (HV20 j Hj20).
              - intros x Hx Hn. rewrite L20 in Hn. change TB_g_s with SINIT_S in Hn.
                pose proof (TMAP_B_hull x Hx) as Hh.
                unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
                unfold SINIT_S, TB_g_s in Hn |- *.
                apply KRs; [lia | lia | lia]. }
            (* the region of the three stores is no longer needed *)
            sinit_keep HS [1%nat; 2%nat] HSb. clear HS. rename HSb into HS.
            (* run 11: the third memcpy's arguments and `jal __asan_memcpy` *)
            paj_run_tok RUN HS HJ4 SHOK YC1i.Bspan.
            { sinit_awr_norm. sinit_awr_ro. sinit_awr_stack UspB. apply awr_ok_x_nil. }
            assert (KRm : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
              aview segs (w_H W) (ms_mem ms9) a = aview segs (w_H W) (ms_mem ms8) a).
            { intros a Ha H1.
              apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 64 <= x < spZ regs) HFr);
                [| exact Ha | exact H1].
              intros bq wlo whi x Hx Hxx. cbv beta.
              sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia;
                                     repeat rewrite ew_ewset_other in Hxx by lia;
                                     rewrite ?UspB, ?Usp in Hxx; lia). }
            assert (GAd : forall a, apresent (w_H W) (ms_mem ms8) a -> apresent (w_H W) (ms_mem ms9) a)
              by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
            clear HF HFr HG.
            assert (Htw9 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms9))
              (SINIT_W0 Bw io_ctx io_send io_recv io_now ntf ctx)).
            { apply (sinit_tw_keep W (ms_mem ms8) (ms_mem ms9) _ Htw8). intros a Ha. apply KRm;
                [ unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Ha; lia
                | unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Ha; lia ]. }
            pmkst HS.
            sinit_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (SINIT_S + 120)) T10
              ltac:(cbn [sv_denot]; repeat rewrite ew_ewset_other by lia;
                    rewrite QE2 by lia; rewrite E10;
                    rewrite unsigned_lit_small by (unfold SINIT_S, TB_g_s; lia); reflexivity).
            sinit_reg HS (Z_to_bv 5 11) (Z_to_bv 64 (SINIT_CFG + 6)) T11
              ltac:(cbn [sv_denot]; repeat rewrite ew_ewset_other by lia;
                    rewrite QE2 by lia; rewrite E11;
                    rewrite unsigned_lit_small by (unfold SINIT_CFG, TB_g_cfg; lia); reflexivity).
            sinit_reg HS (Z_to_bv 5 12) (Z_to_bv 64 6) T12 ltac:(reflexivity).
            sinit_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 64)) T2
              ltac:(cbn [sv_denot]; repeat rewrite ew_ewset_other by lia;
                    rewrite QE2 by lia; rewrite Usp; f_equal; lia).
            sinit_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 22244)) T1
              ltac:(apply codeptr_val; assumption).
            sinit_reg HS (3%bv : bv 5) (w64 (as_gp B)) T3
              ltac:(cbn [sv_denot]; repeat rewrite ew_ewset_other by lia;
                    rewrite QE2 by lia;
                    rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
            sinit_reg HS (4%bv : bv 5) (w64 (as_tp B)) T4
              ltac:(cbn [sv_denot]; repeat rewrite ew_ewset_other by lia;
                    rewrite QE2 by lia;
                    rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
            assert (ESP3 : bv_unsigned (YK11.getr (ms_regs ms9) (Z_to_bv 5 2)) = spZ regs - 64)
              by (rewrite T2; apply unsigned_lit_small; lia).
            assert (Hsp4 : spZ (ms_regs ms9) = spZ regs - 64) by exact ESP3.
            pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR11.
            lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
              change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy))
                mm rom) mdx) Q) end.
            eapply SRr_bind.
            { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OCpy
                (transportb_sigma TB___asan_memcpy) (HCPY fx) TG.G_HARNESS_B W (ms_regs ms9) (ms_mem ms9)
                STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
                (SINIT_S + 120) (SINIT_CFG + 6) 6 (spZ regs - 64 - sp0) (Z_to_bv 64 (BASE + 22244))
                HGX G_HARNESS_B_rw HJ4 T10 T11 T12).
              - lia.
              - unfold SINIT_S, TB_g_s; lia.
              - unfold SINIT_S, TB_g_s; lia.
              - rewrite Hsp4. lia.
              - exact Hm16.
              - lia.
              - lia.
              - exact T3.
              - exact T4.
              - exact T1.
              - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
              - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ4|].
                intros a Ha. right. apply sinit_inG_s. unfold TW.SZ_g_s; lia.
              - left. unfold kLowMemEnd, SINIT_S, TB_g_s. lia.
              - apply (range_addressable_sub _ _ SINIT_S TW.SZ_g_s);
                  [ exact (sinit_s_ra lyc Sc W (ms_mem ms9) _ HSI HAR11)
                  | unfold SINIT_S, TB_g_s; lia | unfold SINIT_S, TB_g_s, TW.SZ_g_s; lia ].
              - intros _. exact (sinit_hull_s lyc Sc W (ms_mem ms9) _ (SINIT_S + 120) 6 HSI HAR11
                  ltac:(sinit_hb) ltac:(sinit_hb)).
              - split; [unfold SINIT_CFG, TB_g_cfg; lia|].
                split; [unfold SINIT_CFG, TB_g_cfg; lia|].
                split.
                { intros a Ha. split.
                  - apply (gx_rw_vis segs TG.G_HARNESS_B a G_HARNESS_B_rw).
                    apply sinit_inG_cfg. unfold SINIT_CFG, TB_g_cfg, TW.SZ_g_cfg in *; lia.
                  - rewrite Hsp4. unfold SINIT_CFG, TB_g_cfg in *. lia. }
                split; [unfold SINIT_S, TB_g_s, SINIT_CFG, TB_g_cfg; lia|].
                split; [left; unfold kLowMemEnd, SINIT_CFG, TB_g_cfg; lia|].
                split.
                { apply (range_addressable_sub _ _ SINIT_CFG 60);
                    [ exact (sinit_cfg_ra lyc Sc W (ms_mem ms9) _ HSC HAR11)
                    | unfold SINIT_CFG, TB_g_cfg; lia | unfold SINIT_CFG, TB_g_cfg; lia ]. }
                intros _. exact (sinit_hull_cfg lyc Sc W (ms_mem ms9) _ (SINIT_CFG + 6) 6 HSC HAR11
                  ltac:(sinit_hb) ltac:(sinit_hb)). }
            cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & _ & Hcpy5 & Heff5 & Hgr5).
            (* the third memcpy's post: g_cfg's 6 MAC bytes at g_s + 120 *)
            assert (Lmac : Z.of_nat (length (TW.sub Bw (TW.OFF_g_cfg + 6) 6)) = 6).
            { rewrite TWL.length_sub; [reflexivity | unfold TW.OFF_g_cfg; lia
              | rewrite HLB; unfold TW.OFF_g_cfg, TW.W_LEN; lia]. }
            assert (Htw10 : tw_at TMAP_B (aview segs (w_H W) mem5)
              (TW.upd (SINIT_W0 Bw io_ctx io_send io_recv io_now ntf ctx) (TW.OFF_g_s + 120)
                 (TW.sub Bw (TW.OFF_g_cfg + 6) 6))).
            { apply (tw_upd TMAP_B (aview segs (w_H W) (ms_mem ms9)) (aview segs (w_H W) mem5) _
                TW.OFF_g_s TB_g_s TW.SZ_g_s 120 (TW.sub Bw (TW.OFF_g_cfg + 6) 6)
                TMAP_B_ok Htw9 TMAP_B_g_s ltac:(lia) ltac:(rewrite Lmac; unfold TW.SZ_g_s; lia)).
              - intros j Hj. assert (Hj' : 0 <= Z.of_nat j < 6) by (rewrite <- Lmac; lia).
                change (TB_g_s + 120 + Z.of_nat j) with (SINIT_S + 120 + Z.of_nat j).
                rewrite (Hcpy5 (Z.of_nat j) ltac:(lia)).
                rewrite (sinit_cfg6_bytes W (ms_mem ms9) _ (Z.of_nat j) Htw9 Hj').
                rewrite (sinit_sub_W0 Bw io_ctx io_send io_recv io_now ntf ctx HLB), Nat2Z.id.
                reflexivity.
              - intros x Hx Hn. rewrite Lmac in Hn.
                pose proof (TMAP_B_hull x Hx) as Hh.
                unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
                apply Heff5; [lia | unfold SINIT_S, TB_g_s in *; lia | lia]. }
            (* the regions the third memcpy keeps, and the region of the desk_known store *)
            jafter_call_keep_hi HS 2144%nat regs5 (mrestrict (w_H W) mem5) HP5 [0%nat; 1%nat] HS5.
            match type of HS5 with ?tq -> _ => assert (HRK : tq) end.
            { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
              - apply (region_kept_aview _ _ _ _ 11%nat SINIT_CFG);
                  [ repeat rewrite ew_ewset_other by lia; rewrite QE2 by lia; exact U11
                  | | exact Hgr5 ].
                intros a Ha. apply Heff5;
                  [ unfold SINIT_CFG, TB_g_cfg in *; lia
                  | unfold SINIT_CFG, TB_g_cfg, SINIT_S, TB_g_s in *; lia
                  | unfold SINIT_CFG, TB_g_cfg in *; lia ].
              - apply (region_kept_aview _ _ _ _ 2%nat (spZ regs));
                  [ repeat rewrite ew_ewset_other by lia; rewrite QE2 by lia; exact Usp
                  | | exact Hgr5 ].
                intros a Ha. apply Heff5;
                  [ lia | unfold SINIT_S, TB_g_s in *; lia | lia ]. }
            specialize (HS5 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS.
            pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HAR12.
            clear SHOK.
            lazymatch type of HS with st_ok_pi _ _ ?EF4 _ _ =>
              assert (HEIf : img_env VAL A_LIM EF4) by (apply img_env_havoc_hi; [assumption | cbv; lia]);
              assert (SE10 : ew EF4 10 = Z_to_bv 64 SINIT_S)
                by (rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia;
                    rewrite QE2 by lia; exact E10);
              assert (SE11 : ew EF4 11 = Z_to_bv 64 SINIT_CFG)
                by (rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia;
                    rewrite QE2 by lia; exact E11);
              assert (SE32 : ew EF4 32 = Z_to_bv 64 SHADOW_OFF)
                by (rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia;
                    rewrite QE2 by lia; exact E32);
              assert (SU10 : bv_unsigned (ew EF4 10) = SINIT_S)
                by (rewrite SE10; apply unsigned_lit_small; unfold SINIT_S, TB_g_s; lia);
              assert (SU11 : bv_unsigned (ew EF4 11) = SINIT_CFG)
                by (rewrite SE11; apply unsigned_lit_small; unfold SINIT_CFG, TB_g_cfg; lia);
              assert (SUsp : bv_unsigned (ew EF4 2) = spZ regs)
                by (rewrite ew_havoc_old by lia; repeat rewrite ew_ewset_other by lia;
                    rewrite QE2 by lia; exact Usp);
              assert (SElo : forall n, (n < 1024)%nat -> ew EF4 n = ew E0 n)
                by (intros n Hn; rewrite ew_havoc_old by lia;
                    repeat rewrite ew_ewset_other by lia; rewrite QE2 by lia; reflexivity);
              pose proof (st_ok_pi_add_region EF4 _ _ SINIT_S2_REG HS ltac:(vm_compute; reflexivity)
                (sinit_s_region_ok W mem5 EF4 116 120 ltac:(lia) ltac:(lia)
                   ltac:(unfold TW.SZ_g_s; lia) SE10)
                ltac:(cbn [ss_mem all_disjoint]; split; [|split; [|exact I]];
                      unfold extent_disjoint, SINIT_S2_REG;
                      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite SU10, ?SU11, ?SUsp;
                      unfold SINIT_S, TB_g_s, SINIT_CFG, TB_g_cfg; lia)) as HSc;
              assert (SHOK : sh_ok segs SINIT_BX SINIT_SHSC EF4 (mrestrict (w_H W) mem5))
                by (exact (sinit_shok_sc lyc Sc W mem5 _ EF4 HSC HSI HAR12 SE10 SE11 SE32))
            end.
            clear HS. rename HSc into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
            (* run 12: the checked store of 1 at s + 116, the epilogue and `ret` *)
            paj_run_tok RUN HS HJ5 SHOK YC1i.Bspan.
            { sinit_awr_norm. sinit_awr_g U10B. sinit_awr_ro. sinit_awr_stack UspB.
              apply awr_ok_x_nil. }
            assert (KRd : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
              ~ (SINIT_S + 116 <= a < SINIT_S + 120) ->
              aview segs (w_H W) (ms_mem ms10) a = aview segs (w_H W) mem5 a).
            { intros a Ha H1 H2.
              apply (kept_of_frame _ _ _ _ _
                (fun x => (spZ regs - 64 <= x < spZ regs) \/ (SINIT_S + 116 <= x < SINIT_S + 120)) HFr);
                [| exact Ha | intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
              intros bq wlo whi x Hx Hxx. cbv beta.
              sinit_win Hx Hxx ltac:(repeat rewrite ew_havoc_old in Hxx by lia;
                                     repeat rewrite ew_ewset_other in Hxx by lia;
                                     rewrite ?UspB, ?U10B in Hxx;
                                     first [lia | left; lia | right; lia]). }
            assert (GAk : forall a, apresent (w_H W) mem5 a -> apresent (w_H W) (ms_mem ms10) a)
              by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
            clear HF HFr HG.
            lazymatch type of HS with st_ok_pi _ _ ?EF5 _ (restrict _ _) => set (EZ := EF5) in HS end.
            assert (HEZ : forall n, (n < 1024)%nat -> ew EZ n = ew E0 n)
              by (intros n Hn; unfold EZ; repeat rewrite ew_ewset_other by lia;
                  rewrite SElo by lia; reflexivity).
            sinit_rgn HS 0%nat RGf.
            change (ms_mem (restrict (w_H W) ms10)) with (mrestrict (w_H W) (ms_mem ms10)) in RGf.
            assert (Hone : forall j, (j < 4)%nat ->
              aview segs (w_H W) (ms_mem ms10) (SINIT_S + 116 + Z.of_nat j)
              = Some (bv_unsigned (nth j (TW.put 4 1) (Z_to_bv 8 0)))).
            { intros j Hj.
              apply (sinit_store_byte W (ms_mem ms10) EZ 116 120 _ 116 4 (SLit 1) 1 j RGf
                ltac:(rewrite HEZ by lia; exact E10)
                ltac:(cbn [In]; first [left; reflexivity | right; left; reflexivity
                                      | right; right; left; reflexivity])
                ltac:(cbn [sv_denot]; reflexivity)
                ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia) ltac:(cbn [N.to_nat]; lia)). }
            assert (Htwg : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms10))
              (SINIT_W1 Bw io_ctx io_send io_recv io_now ntf ctx)).
            { unfold SINIT_W1.
              apply (tw_upd TMAP_B (aview segs (w_H W) mem5) (aview segs (w_H W) (ms_mem ms10)) _
                TW.OFF_g_s TB_g_s TW.SZ_g_s 116 (TW.put 4 1)
                TMAP_B_ok Htw10 TMAP_B_g_s ltac:(lia)
                ltac:(rewrite TWL.length_put; unfold TW.SZ_g_s; lia)).
              - intros j Hj. rewrite TWL.length_put in Hj.
                change (TB_g_s + 116 + Z.of_nat j) with (SINIT_S + 116 + Z.of_nat j).
                exact (Hone j Hj).
              - intros x Hx Hn. rewrite TWL.length_put in Hn. change TB_g_s with SINIT_S in Hn.
                pose proof (TMAP_B_hull x Hx) as Hh.
                unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
                unfold SINIT_S, TB_g_s in Hn |- *.
                apply KRd; [lia | lia | lia]. }
            (* the registers at the return *)
            sinit_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
              ltac:(cbn [sv_denot]; rewrite HEZ by lia;
                    rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
            sinit_reg HS (Z_to_bv 5 10) (w64 r) RF10
              ltac:(rewrite Er; cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity).
            assert (HPF : aregs_preserved regs (ms_regs ms10)).
            { apply (aregs_preserved_of_st_ok segs (w_H W) EZ _ ms10 regs
                [w64 SHADOW_OFF; w64 io_send; w64 (TW.u_at Bw (TW.OFF_g_cfg + 12) 4);
                 w64 (TW.u_at Bw (TW.OFF_g_cfg + 52) 4); w64 (TW.u_at Bw (TW.OFF_g_cfg + 56) 4)] HS).
              - apply sinit_agree; [intros n Hn; rewrite HEZ by lia; reflexivity | reflexivity].
              - vm_compute. reflexivity. }
            eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
            intros mat'.
            rewrite EBw.
            exact (sinit_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs r
              (SINIT_W1 Bw io_ctx io_send io_recv io_now ntf ctx)
              (ms_regs ms10) (ms_mem ms10) _ LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ5
              ltac:(intros a Ha H1 H2;
                    assert (Hgs : ~ (SINIT_S <= a < SINIT_S + TW.SZ_g_s))
                      by (intros Hcg; apply H2; split; [exact Er | exact Hcg]);
                    unfold TW.SZ_g_s in Hgs;
                    rewrite (KRd a ltac:(lia) ltac:(lia) ltac:(lia));
                    rewrite (Heff5 a ltac:(lia) ltac:(lia) ltac:(lia));
                    rewrite (KRm a ltac:(lia) ltac:(lia));
                    rewrite (KRs a ltac:(lia) ltac:(lia) ltac:(lia));
                    rewrite (KAp2 a ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_g_s; lia));
                    rewrite (KC2 a ltac:(lia) ltac:(lia));
                    rewrite (KAp1 a ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_g_s; lia));
                    apply KAm; [lia | lia | unfold TW.SZ_g_s; lia])
              ltac:(intros a Ha; apply GAk; apply Hgr5; apply GAd; apply GAs; apply Hgr4; apply GC2;
                    apply Hgr3; apply GC1; apply Hgr2; apply GA7; exact Ha)
              Htwg HPF RF1 RF10 mat').
Qed.

End sinitw.

(* The statement of lib/A/Prog/diginet_session_init_cg.v. *)
Theorem transport_diginet_session_init_cg_holds :
  forall fx rc B MT, @transport_diginet_session_init_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@sinit_holds fx rc B MT). Qed.
