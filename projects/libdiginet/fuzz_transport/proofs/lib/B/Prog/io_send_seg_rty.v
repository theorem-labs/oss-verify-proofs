(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 821 of its 896 lines of code are new or changed and 690 lines of the source are left out. *)
(* io_send_seg_rty: the retry arm of the image-B walk of io_send (fuzz_transport.asan-ubsan 41113a03c82f, entry
   0x82ffc = TImgB.v ti_io_send timg_B; the statement is lib/B/Prog/io_send_cg.v transport_io_send_cg_holds_stmt),
   0x830d4 .. 0x83104 = transportb_text + IOS_RTY .. + IOS_AT 0x108 (lib/B/Prog/io_send_seg_cut.v).

   The code (io_send_cg.v header lines 104-106 and 211-215), with sp = the walk's sp (the entry sp less
   IOSEND_FRAME = 160) and M = TB_M:
     0x830d4 - 0x830dc  a2 = sp + 8, a0 = s1 (p), a1 = s0 (len);
     0x830e0            the call of check_inflight_retry (transportb_sigma TB_check_inflight_retry), return address
                        0x830e4 = transportb_text + IOS_AT 0xe8;
     0x830e4 - 0x83100  a0 = M (the listing's object 8); a1 = the 4-byte load of M.fly.retries (M + 108),
                        sign-extended; a2 = the 8-byte load of g_now (object 28); a1 = a1 + 1 (a 64-bit add: the
                        `sw` keeps its low 4 bytes); the 4-byte store of a1 at M + 108; the 8-byte store of a2 at
                        M + 112 (M.fly.sent);
     0x83104            `j` 0x83310 = transportb_text + IOS_EPI.

   The segment is io_send_seg_cut.v ios_rty_arm_stmt: from the cut ios_at_csf (ios_e2_at at the world ios_B0 Bw) to
   ios_e2_at at the world the retry arm leaves, Bw' = set_M_fly_sent (set_M_fly_retries B0
   (u32 (M_fly_retries B0 + 1))) (g_now B0) with B0 = ios_B0 Bw (io_send_segs.v ios_arm_retry). It is proved in three
   steps, as image A's twin lib/A/Prog/io_send_seg_rty.v:
     the call setup  one run of TransportGRunB.v paj_run_x from a state with no region (rty_cs_ss: the three moves
                     read and write no memory); it stops at the call (rty_cs_stop); the cut is carried to the call's
                     memory by rty_keep (no byte changes);
     the call        the DONOR call of check_inflight_retry through TransportGCg.v gx_call_cg with the contract
                     check_inflight_retry_cg.v transport_check_inflight_retry_cg, its post read by
                     DgnTransportBCg.v decode_cg_post_dcg. Its premises are the cut's (the frame and the struct
                     spec_frame f at sp + 8, the world relation at B0), the window (CIR_STK below sp - 160), the
                     model call check_inflight_retry_m B0 frame (ios_arm_retry) and M_fly_len B0 <= SPEC_MAX_FRAME:
                     io_send_seg_cut.v ios_fix's guarded bound on Bw, whose guard M_fly_on Bw <> 0 the model call's
                     first test gives, with M_fly_on and M_fly_len of B0 those of Bw (B0 differs from Bw only at
                     g_fail_next's byte, world offset 0xfdc8; M.fly.on is at 0x60 and M.fly.len at 0x668:
                     rty_fly_len_bound). After it: the journal, the running acall_kept_g by TransportGCg.v
                     dk_kept_trans_nf_g, the frame by DgnTransportBCg.v trans_src_ok_acall_g (ios_laws carries
                     trans_ro_rd_unowned and trans_rom_no_errno), the saved words and the struct (above the callee's
                     window), the world by gx_kept and TWorldG.v tw_kept;
     the tail        one run of TransportGRunB.v paj_run_to_x from rty_ss (M.fly.retries and M.fly.sent writable,
                     g_now read only) to IOS_EPI (rty_stop); the two stored values are read back from the chunks of
                     the run's last state (M + 112: g_now; M + 108: the sign-extended M.fly.retries plus 1, whose four
                     low bytes are u32 (M_fly_retries B0 + 1)), the world is two io_send_seg_world.v ios_tw_step at
                     the M row of TWorldB.v TMAP_B, and the running kept fact grows by the 12 stored bytes, which are
                     bytes of G and of iosend_wr (io_send_seg_world.v ios_wr_fly_retries / ios_wr_fly_sent). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB m_set_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  check_sent_frame_cg check_inflight_retry_cg check_latest_sent_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs io_send_seg_frm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_seg_cut io_send_seg_world.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The model side                                                      *)
(* ------------------------------------------------------------------ *)

Lemma rty_len_B : forall T rd Bw, tw_at T rd Bw -> Z.of_nat (length Bw) = TW.W_LEN.
Proof.
  intros T rd Bw H. rewrite (tw_len T rd Bw H). rewrite Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia].
Qed.

(* ios_B0 Bw stores only g_fail_next's byte (world offset 0xfdc8): M.fly.on (0x60 .. 0x63) and M.fly.len
   (0x668 .. 0x66f) are those of Bw. *)
Lemma rty_B0_on : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> TW.M_fly_on (ios_B0 Bw) = TW.M_fly_on Bw.
Proof.
  intros Bw HL. unfold ios_B0, TW.set_g_fail_next, TW.M_fly_on.
  rewrite (TWL.s32_at_upd_out Bw (TW.put 1 0))
    by (rewrite ?TWL.length_put, ?HL; try change (Z.of_nat 1) with 1;
        unfold TW.A_M_fly_on, TW.OFF_M, TW.OFF_g_fail_next, TW.W_LEN; lia).
  reflexivity.
Qed.

Lemma rty_B0_len : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> TW.M_fly_len (ios_B0 Bw) = TW.M_fly_len Bw.
Proof.
  intros Bw HL. unfold ios_B0, TW.set_g_fail_next, TW.M_fly_len.
  rewrite (TWL.u_at_upd_out Bw (TW.put 1 0))
    by (rewrite ?TWL.length_put, ?HL; try change (Z.of_nat 1) with 1; try change (Z.of_nat 8) with 8;
        unfold TW.A_M_fly_len, TW.OFF_M, TW.OFF_g_fail_next, TW.W_LEN; lia).
  reflexivity.
Qed.

(* check_inflight_retry_m's first test (:459): no frame in flight is None. *)
Lemma rty_cir_on : forall Bx frame Bx', TC.check_inflight_retry_m Bx frame = Some (Bx', tt) -> TW.M_fly_on Bx <> 0.
Proof.
  intros Bx frame Bx' H. unfold TC.check_inflight_retry_m, TC.truth in H. cbv zeta in H.
  destruct (TW.M_fly_on Bx =? 0) eqn:E.
  - cbn [negb orb] in H. discriminate H.
  - apply Z.eqb_neq. exact E.
Qed.

(* The callee's run invariant at the world it is handed: io_send_seg_cut.v ios_fix's guarded bound, whose guard
   the model call gives. *)
Lemma rty_fly_len_bound : forall Bw frame,
  Z.of_nat (length Bw) = TW.W_LEN ->
  (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
  TC.check_inflight_retry_m (ios_B0 Bw) frame = Some (ios_B0 Bw, tt) ->
  TW.M_fly_len (ios_B0 Bw) <= TC.SPEC_MAX_FRAME.
Proof.
  intros Bw frame HL HG HM. rewrite (rty_B0_len Bw HL). apply HG.
  rewrite <- (rty_B0_on Bw HL). exact (rty_cir_on _ _ _ HM).
Qed.

Lemma rty_truth : forall frame, ios_e2_rty frame <> 0 -> TC.truth (DSpec.sf_retry (TC.rf frame)) = true.
Proof.
  intros frame H. unfold TC.truth. apply negb_true_iff. apply Z.eqb_neq. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* Bytes                                                               *)
(* ------------------------------------------------------------------ *)

(* Byte j < w <= 8 of a 64-bit word holding v is byte j of the w-byte little-endian v. *)
Lemma rty_bow : forall v (w j : nat), (j < w)%nat -> (w <= 8)%nat ->
  bv_unsigned (byte_of_word (Z_to_bv 64 v) (Z.of_nat j)) = YO0f.le_byte v w j.
Proof.
intros v w j Hj Hw. unfold byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). change (2 ^ Z.of_N 64) with (2 ^ 64). change 256 with (2 ^ 8).
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* A signed wrap does not change the low bytes. *)
Lemma rty_swrap_mod : forall (n : N) z, bv_swrap n z mod 2 ^ Z.of_N n = z mod 2 ^ Z.of_N n.
Proof.
intros n z. unfold bv_swrap, bv_wrap, bv_modulus. rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma rty_Forall_nth : forall {A : Type} (P : A -> Prop) (l : list A) (n : nat) (x : A),
  Forall P l -> nth_error l n = Some x -> P x.
Proof. intros A P l n x HF Hn. rewrite Forall_forall in HF. apply HF. exact (nth_error_In l n Hn). Qed.

(* The four low bytes of the sign-extended M.fly.retries plus 1 are those of u32 (M.fly.retries + 1). *)
Lemma rty_le_byte_inc : forall x (j : nat),
  YO0f.le_byte (bv_swrap 32 x + 1) 4 j = YO0f.le_byte (DSpec.u32 (x + 1)) 4 j.
Proof.
  intros x j. unfold YO0f.le_byte, DSpec.u32.
  assert (E : (bv_swrap 32 x + 1) mod 2 ^ (8 * Z.of_nat 4) = (x + 1) mod 2 ^ 32 mod 2 ^ (8 * Z.of_nat 4)).
  { pose proof (rty_swrap_mod 32 x) as Hs. change (2 ^ Z.of_N 32) with 4294967296 in Hs.
    change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ 32) with 4294967296.
    rewrite Z.mod_mod by lia. rewrite Zplus_mod, Hs, <- Zplus_mod. reflexivity. }
  rewrite E. reflexivity.
Qed.

(* The value of a sign-extended load of wn bytes. *)
Lemma rty_sext_den : forall (E : env) (n : nat) (wN : N) (wn : nat) (u : Z),
  ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 64 -> Z.of_N wN = 8 * Z.of_nat wn ->
  (0 < wn)%nat -> (wn <= 8)%nat ->
  sv_denot E (SExt true wN (SOff n 0)) = Z_to_bv 64 (bv_swrap wN u).
Proof.
intros E n wN wn u Hn Hu HwN Hwn0 Hwn. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 wN (Z_to_bv 64 u)))
  with (Z_to_bv 64 (bv_signed (bv_extract 0 wN (Z_to_bv 64 u)))).
f_equal. rewrite (LMem.signed_of_extract wN (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The `addi a1, a1, 1` after the sign-extending `lw` of M.fly.retries. *)
Lemma rty_den_inc : forall (E : env) n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1)) = Z_to_bv 64 (bv_swrap 32 u + 1).
Proof.
  intros E n u Hn Hu.
  change (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1)))
    with (alu64 ALU_ADD (sv_denot E (SExt true 32 (SOff n 0))) (Z_to_bv 64 1)).
  rewrite (rty_sext_den E n 32 4 u Hn Hu eq_refl ltac:(lia) ltac:(lia)).
  apply alu64_add_lit.
Qed.

(* ------------------------------------------------------------------ *)
(* The world the tail leaves                                           *)
(* ------------------------------------------------------------------ *)

(* The two stores at the M row, every other payload byte unchanged. *)
Lemma rty_world : forall (Bx : list byte) (rd0 rdF : Z -> option Z),
  tw_at TMAP_B rd0 Bx ->
  (forall j, (j < 4)%nat ->
     rdF (TB_M + 108 + Z.of_nat j) = Some (YO0f.le_byte (DSpec.u32 (TW.M_fly_retries Bx + 1)) 4 j)) ->
  (forall j, (j < 8)%nat -> rdF (TB_M + 112 + Z.of_nat j) = Some (YO0f.le_byte (TW.g_now Bx) 8 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_M + 108 <= x < TB_M + 112) -> ~ (TB_M + 112 <= x < TB_M + 120) ->
     rdF x = rd0 x) ->
  tw_at TMAP_B rdF
    (TW.set_M_fly_sent (TW.set_M_fly_retries Bx (DSpec.u32 (TW.M_fly_retries Bx + 1))) (TW.g_now Bx)).
Proof.
  intros Bx rd0 rdF Htw V108 V112 Hk.
  assert (SM : TW.SZ_M = 1648) by reflexivity.
  unfold TW.set_M_fly_sent, TW.set_M_fly_retries, TW.A_M_fly_sent, TW.A_M_fly_retries.
  pose proof (ios_tw_start rdF rd0 Bx Htw) as H0.
  pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 108 (TW.OFF_M + 96 + 12) 4
    (DSpec.u32 (TW.M_fly_retries Bx + 1)) H0 TMAP_B_M ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V108) as H1.
  pose proof (ios_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 112 (TW.OFF_M + 96 + 16) 8 (TW.g_now Bx) H1
    TMAP_B_M ltac:(lia) ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V112) as H2.
  apply (ios_tw_end rdF rd0 _ _ H2).
  intros x Hx HP. ios_unP HP. apply Hk; (exact Hx || lia).
Qed.

(* The two harness words the tail loads, as the world holds them (unsigned). *)
Definition rty_flyr (Bx : list byte) : Z := TW.u_at Bx TW.A_M_fly_retries 4.
Definition rty_now (Bx : list byte) : Z := TW.u_at Bx TW.OFF_g_now 8.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* The call setup (0x830d4 .. 0x830e0) reads and writes no memory: its state has no region and no fact. *)
Definition rty_cs_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

(* The tail reads and writes only M.fly.retries (M + 108, 4 bytes) and M.fly.sent (M + 112, 8) and reads g_now; it
   touches no stack cell. Atoms beyond the 32 registers: 32 M.fly.retries, 33 g_now. The M region carries the write
   window, so the engine's frame_of keeps every other byte. *)
Definition rty_fly_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 8)) 108 120 108 120 [YP09.mkChunk 108 (CVal 4 (SOff 32 0))].
Definition rty_now_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 28)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition rty_regions : smem := [rty_fly_region; rty_now_region].
Definition rty_facts : facts :=
  mkFacts [(A_OBJ 8, mkAF TB_M TB_M 5); (A_OBJ 28, mkAF TB_g_now TB_g_now 5)] [] [].
Definition rty_ss (pc : Z) : sstate := mkSS pc sr_atoms rty_regions None rty_facts.
(* No instrumented check on either stretch: the empty shadow entry, at the shadow base s4. *)
Definition RTY_SH : list shent := [].
Definition RTY_Bx : sv := SOff 20 0.

(* Where the token engine stops on each stretch, decided over the listing (lib/B/Prog/DgnTransportBList.v). *)
Definition rty_cs_run (pc : Z) :=
  let ss := rty_cs_ss pc in
  let K := run_K A_LIM RTY_Bx RTY_SH ss in
  match sym_runN_pi_tok transportb_tpi transportb_tw K RTY_Bx YC4b.Bspan RTY_SH FUEL ss with
  | (st, r) => (ss_pc (sh_ss st), r)
  end.
Definition rty_run_to (stop pc : Z) :=
  let ss := rty_ss pc in
  let K := run_K A_LIM RTY_Bx RTY_SH ss in
  match sym_run_toN_pi_tok transportb_tpi transportb_tw K RTY_Bx YC4b.Bspan RTY_SH FUEL stop ss with
  | (st, r) => (ss_pc (sh_ss st), r)
  end.

(* The call setup stops at the call of check_inflight_retry (0x830e0), the state's pc being the return address
   0x830e4. *)
Lemma rty_cs_stop : rty_cs_run IOS_RTY = (IOS_AT 0xe8, PTS_call TB_check_inflight_retry).
Proof. vm_compute. reflexivity. Qed.

(* The tail: M.fly.retries + 1 and M.fly.sent = g_now, then the `j` to the epilogue. *)
Lemma rty_stop : rty_run_to IOS_EPI (IOS_AT 0xe8) = (IOS_EPI, PTS_running).
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Tactics                                                             *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac rty_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "rty_reg: no match for" T; fail
  end.

(* The windows a run wrote, each closed by tac. *)
Ltac rty_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* ------------------------------------------------------------------ *)
(* Memory facts at a later memory                                      *)
(* ------------------------------------------------------------------ *)

(* An aview equality is an mbyte equality of the restricted memories (any two hidden sets). *)
Lemma rty_mbyte_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H' m' a = aview tfibsegs H m a ->
  YP09.mbyte tfibsegs (mrestrict H' m') a = YP09.mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (YP09.mbyte tfibsegs (mrestrict H' m') a) as [b1|]; destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b2|];
  cbn [option_map] in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* garr8 at a later memory (and world) that reads the range's bytes as before. *)
Lemma rty_garr8_xw : forall (H H' : word -> bool) (m m' : word -> option byte) p l,
  garr8 tfibsegs (mrestrict H m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> aview tfibsegs H' m' a = aview tfibsegs H m a) ->
  garr8 tfibsegs (mrestrict H' m') p l.
Proof.
intros H H' m m' p l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros i Hi. assert (Ei : i = 0%nat) by lia. subst i.
rewrite (rty_mbyte_of_aview H H' m m' (p + Z.of_nat j + Z.of_nat 0)).
- exact (Hv 0%nat Hi).
- apply Hk. lia.
Qed.

(* The struct at a later memory (and world) that reads its 80 bytes as before. *)
Lemma rty_sframe_xw : forall (W W' : world tfibsegs) mem mem' q fa f,
  (forall a, q <= a < q + 80 -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  trans_sframe_at W mem q fa f -> trans_sframe_at W' mem' q fa f.
Proof.
intros W W' mem mem' q fa f Heq (H0 & H8 & SB & HG & HL & R). split; [exact H0|]. split; [exact H8|].
exists SB. split; [|split; [exact HL | exact R]].
apply (rty_garr8_xw _ _ _ _ _ _ HG). intros a Ha. rewrite length_map, HL in Ha. apply Heq. lia.
Qed.

(* A present byte is visible. *)
Lemma rty_some_of_present : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, YP09.mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

(* ios_regs and s8 .. s11 through a call that keeps the callee-saved registers. *)
Lemma rty_regs_pres : forall regs (r2 r3 : bvmap 5 word) p frame fb,
  ios_regs regs r2 p frame fb -> aregs_preserved r2 r3 -> ios_regs regs r3 p frame fb.
Proof.
intros regs r2 r3 p frame fb (R2 & R3 & R4 & R8 & R9 & R19 & R20) HP. unfold ios_regs.
split; [refine (eq_trans (HP 2 ltac:(unfold acallee_saved; lia)) _); exact R2|].
split; [refine (eq_trans (HP 3 ltac:(unfold acallee_saved; lia)) _); exact R3|].
split; [refine (eq_trans (HP 4 ltac:(unfold acallee_saved; lia)) _); exact R4|].
split; [refine (eq_trans (HP 8 ltac:(unfold acallee_saved; lia)) _); exact R8|].
split; [refine (eq_trans (HP 9 ltac:(unfold acallee_saved; lia)) _); exact R9|].
split; [refine (eq_trans (HP 19 ltac:(unfold acallee_saved; lia)) _); exact R19|].
refine (eq_trans (HP 20 ltac:(unfold acallee_saved; lia)) _); exact R20.
Qed.

Lemma rty_s811 : forall regs (r2 r3 : bvmap 5 word),
  (forall r, 24 <= r <= 27 -> YK11.getr r2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  aregs_preserved r2 r3 ->
  forall r, 24 <= r <= 27 -> YK11.getr r3 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r).
Proof.
intros regs r2 r3 H HP r Hr. rewrite (HP r ltac:(unfold acallee_saved; lia)). exact (H r Hr).
Qed.

(* The registers both runs keep: sp, gp, tp, s0 = len, s1 = p, s3 = the g_fail_next byte, s4 = the shadow base,
   and s8 .. s11, which io_send never writes. *)
Definition rty_kept : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 20%bv; 24%bv; 25%bv; 26%bv; 27%bv].

Lemma rty_regs_step : forall regs (r3 r4 : bvmap 5 word) p frame fail,
  ios_regs regs r3 p frame fail ->
  (forall r, 24 <= r <= 27 -> YK11.getr r3 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  (forall r : bv 5, In r rty_kept -> YK11.getr r4 r = YK11.getr r3 r) ->
  ios_regs regs r4 p frame fail /\
  (forall r, 24 <= r <= 27 -> YK11.getr r4 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
Proof.
  intros regs r3 r4 p frame fail HR G24 M.
  destruct HR as (G2 & G3 & G4 & G8 & G9 & G19 & G20).
  split.
  - unfold ios_regs.
    rewrite (M 2%bv ltac:(unfold rty_kept; cbn [In]; tauto)),
            (M 3%bv ltac:(unfold rty_kept; cbn [In]; tauto)),
            (M 4%bv ltac:(unfold rty_kept; cbn [In]; tauto)),
            (M 8%bv ltac:(unfold rty_kept; cbn [In]; tauto)),
            (M 9%bv ltac:(unfold rty_kept; cbn [In]; tauto)),
            (M 19%bv ltac:(unfold rty_kept; cbn [In]; tauto)),
            (M 20%bv ltac:(unfold rty_kept; cbn [In]; tauto)).
    repeat split; assumption.
  - assert (E24 : Z_to_bv 5 24 = 24%bv) by (apply bv_eq; vm_compute; reflexivity).
    assert (E25 : Z_to_bv 5 25 = 25%bv) by (apply bv_eq; vm_compute; reflexivity).
    assert (E26 : Z_to_bv 5 26 = 26%bv) by (apply bv_eq; vm_compute; reflexivity).
    assert (E27 : Z_to_bv 5 27 = 27%bv) by (apply bv_eq; vm_compute; reflexivity).
    intros r Hr.
    assert (HR4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct HR4 as [E|[E|[E|E]]]; subst r.
    + rewrite E24, (M 24%bv ltac:(unfold rty_kept; cbn [In]; tauto)), <- E24.
      exact (G24 24 ltac:(lia)).
    + rewrite E25, (M 25%bv ltac:(unfold rty_kept; cbn [In]; tauto)), <- E25.
      exact (G24 25 ltac:(lia)).
    + rewrite E26, (M 26%bv ltac:(unfold rty_kept; cbn [In]; tauto)), <- E26.
      exact (G24 26 ltac:(lia)).
    + rewrite E27, (M 27%bv ltac:(unfold rty_kept; cbn [In]; tauto)), <- E27.
      exact (G24 27 ltac:(lia)).
Qed.

Section rty. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The listing's values of the two objects the tail reaches: M and g_now. *)
Lemma rty_vals : VAL (A_OBJ 8) = TB_M /\ VAL (A_OBJ 28) = TB_g_now.
Proof. split; vm_compute; reflexivity. Qed.

(* The return address of the call is the cut IOS_AT 0xe8 (0x830e4). *)
Lemma rty_pc : Z_to_bv 64 (BASE + 7748) = w64 (transportb_text + IOS_AT 0xe8).
Proof. unfold w64. f_equal; try (vm_compute; reflexivity). Qed.

(* The w bytes of a chunk of value v, read through the view. *)
Lemma rty_chunk_rd : forall (E : env) (H : word -> bool) (mm : word -> option byte) (base off : Z)
    (wN : N) (wn : nat) (e : sv) (v : Z),
  Z.of_N wN = Z.of_nat wn -> (wn <= 8)%nat ->
  YP09.chunk_ok segs E (mrestrict H mm) base (YP09.mkChunk off (CVal wN e)) ->
  sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < wn)%nat -> aview segs H mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v wn j).
Proof.
intros E H mm base off wN wn e v HwN Hwn HC He j Hj. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC (Z.of_nat j) ltac:(lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview segs H mm (base + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H mm) (base + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply rty_bow; [exact Hj | exact Hwn].
Qed.

(* The tail's two harness words, read through the world relation at the M and g_now rows of TMAP_B. *)
Lemma rty_cut_vals : forall (W : world segs) mem Bx,
  tw_at TMAP_B (aview segs (w_H W) mem) Bx ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TB_M + 108) 4 (rty_flyr Bx) /\
  YI04.val_mem segs (mrestrict (w_H W) mem) (TB_g_now + 0) 8 (rty_now Bx) /\
  0 <= rty_flyr Bx < 2 ^ 32 /\ 0 <= rty_now Bx < 2 ^ 64.
Proof.
  intros W mem Bx HTW.
  split.
  { exact (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B Bx TW.OFF_M TB_M TW.SZ_M 108 4
             TMAP_B_ok HTW TMAP_B_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)). }
  split.
  { exact (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B Bx TW.OFF_g_now TB_g_now TW.SZ_g_now 0 8
             TMAP_B_ok HTW TMAP_B_g_now ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)). }
  pose proof (TWL.u_at_range Bx TW.A_M_fly_retries 4) as Q3.
  pose proof (TWL.u_at_range Bx TW.OFF_g_now 8) as Q4.
  change (8 * Z.of_nat 4) with 32 in Q3. change (8 * Z.of_nat 8) with 64 in Q4.
  unfold rty_flyr, rty_now. split; lia.
Qed.

(* The call setup's valuation: the 32 registers. *)
Definition rty_cs_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

Lemma rty_cs_agree : forall regs, env_agree 32 (Ereg regs []) (rty_cs_E regs).
Proof.
  intros. split; [intros n Hn; unfold rty_cs_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

Lemma rty_cs_entry : forall (W : world segs) (regs : bvmap 5 word) mem,
  st_ok_pi segs VAL (rty_cs_E regs) (rty_cs_ss IOS_RTY)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + IOS_RTY)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem.
  rewrite restrict_mkst_fx. unfold rty_cs_ss.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - unfold rty_cs_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - exact (conj I (conj I I)).
Qed.

(* The tail's valuation: the registers, M.fly.retries and g_now. *)
Definition rty_E (regs : bvmap 5 word) (flyr now : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 flyr; Z_to_bv 64 now]).

Lemma rty_agree : forall regs flyr now,
  env_agree 32 (Ereg regs [Z_to_bv 64 flyr; Z_to_bv 64 now]) (rty_E regs flyr now).
Proof.
  intros. split; [intros n Hn; unfold rty_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

(* The state the token engine runs the tail from: M.fly.retries (readable, and writable: a byte of G) and g_now
   (read only). *)
Lemma rty_entry : forall (W : world segs) (regs : bvmap 5 word) mem (flyr now : Z),
  0 <= flyr < 2 ^ 32 -> 0 <= now < 2 ^ 64 ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TB_M + 108) 4 flyr ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TB_g_now + 0) 8 now ->
  st_ok_pi segs VAL (rty_E regs flyr now) (rty_ss (IOS_AT 0xe8))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + IOS_AT 0xe8)) mem (YK11.seg_rom segs)))
  /\ sh_ok segs RTY_Bx RTY_SH (rty_E regs flyr now) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem flyr now Hflyr Hnow V108 Vnow.
  assert (EM : TB_M = 0x5dede0) by reflexivity. assert (EN : TB_g_now = 0x5ded80) by reflexivity.
  set (E := rty_E regs flyr now).
  assert (E32 : ew E 32 = Z_to_bv 64 flyr)
    by (unfold E, rty_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 now)
    by (unfold E, rty_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (EOB : forall j, (j < 97)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, rty_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct rty_vals as (V8 & V28).
  assert (B8 : base_val E (Some (A_OBJ 8)) = TB_M).
  { cbn [base_val]. rewrite (EOB 8%nat ltac:(lia)), V8. apply unsigned_lit_small. lia. }
  assert (B28 : base_val E (Some (A_OBJ 28)) = TB_g_now).
  { cbn [base_val]. rewrite (EOB 28%nat ltac:(lia)), V28. apply unsigned_lit_small. lia. }
  assert (U8 : bv_unsigned (ew E (A_OBJ 8)) = TB_M) by exact B8.
  assert (U28 : bv_unsigned (ew E (A_OBJ 28)) = TB_g_now) by exact B28.
  split; [|unfold sh_ok, RTY_SH; constructor].
  rewrite restrict_mkst_fx. unfold rty_ss, rty_regions.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold rty_fly_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite B8. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_M + o) G_HARNESS_B_rw).
        apply (ios_inG_row _ _ _ (TB_M + o) TMAP_B_M). unfold TW.SZ_M. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ TB_M 108 4 (SOff 32 0) flyr);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia
          | exact V108].
    + unfold rty_now_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite B28. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TB_g_now 0 8 (SOff 33 0) now);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia | exact Vnow].
  - apply pairwise_disjoint_of_extents.
    unfold rty_fly_region, rty_now_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite B8, B28.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold rty_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U8, U28. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite ?EM, ?EN; reflexivity].
Qed.

(* The w bytes of chunk c of region idx of the state HS, read through the view. *)
Ltac rty_chunk HS idx c UB wn v tac V :=
  let RG := fresh "RG" in let HC := fresh "HC" in let HC1 := fresh "HCk" in let Hden := fresh "Hden" in
  pose proof (YC4b.st_ok_region_nth _ _ _ idx _ HS eq_refl) as RG;
  cbn [ms_mem restrict] in RG;
  destruct RG as (_ & _ & _ & HC);
  cbn [YP09.r_base YP09.r_chunks base_val] in HC;
  rewrite UB in HC;
  pose proof (rty_Forall_nth _ _ c _ HC eq_refl) as HC1;
  lazymatch type of HC1 with
  | YP09.chunk_ok _ ?Ex _ _ (YP09.mkChunk _ (CVal ?wN ?e)) =>
      assert (Hden : sv_denot Ex e = Z_to_bv 64 v) by tac;
      pose proof (rty_chunk_rd _ _ _ _ _ wN wn _ v eq_refl ltac:(lia) HC1 Hden) as V
  end;
  clear HC HC1 Hden.

(* ------------------------------------------------------------------ *)
(* The running kept fact, the struct's placement, the cut              *)
(* ------------------------------------------------------------------ *)

(* A step of the walk that changes only bytes of io_send's stack window or bytes of G in its written range keeps the
   running kept fact (at any world of the step). *)
Lemma rty_kept_step : forall G lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 mem3 slo shi (E Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B G ->
  @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, Zs a -> (slo <= a < shi) \/ (inG G a /\ E a)) ->
  YM05.alloc_ceiling <= slo -> shi <= 2 ^ 47 ->
  acall_kept_g segs B G lyc Sc W memc W2 mem3 slo shi E.
Proof.
  intros G lyc Sc W memc mdc W2 mem2 mem3 slo shi E Zs LAWS HGX HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZ Hce Hhi.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (GLOW : forall a, inG G a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (inG_low segs B transportb_segs_low G a HGX Ha)).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite Hkp; [apply K1; [exact Ha | exact Hw] | lia |].
    intros HZa. destruct (HZ a HZa) as [Hs | [Hg _]]; [exact (Hw Hs) | pose proof (GLOW a Hg); lia].
  - intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
    rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [_ He]]; [lia | exact (Hn He)].
  - intros a Hi HnG Hno He. pose proof (transportb_segs_low a Hi) as Hlow.
    rewrite Hkp; [apply K3; [exact Hi | exact HnG | exact Hno | exact He] | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [Hg _]]; [lia | exact (HnG Hg)].
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    assert (Ha : 0 <= a < YM05.alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
    rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [_ He]]; [lia | exact (Hn He)].
  - intros a Ha Hw Hp. apply Hgr. apply K5; [exact Ha | exact Hw | exact Hp].
  - intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.

(* The struct's 80 bytes at sp + 8 placed by trans_src_ok at any state of the walk's journal: the machine-stack case,
   with decode_rd_ok (the window's bytes present by the journal, the stack's zero shadow by stack_zshadow_ra). *)
Lemma rty_sf_src : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own ly2 S2 (W2 : world segs) mem2 md2 k q,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly2 S2 W2 mem2 md2 k ->
  sp0 - STK <= q -> q + 88 <= sp0 ->
  trans_src_ok B ly2 S2 W2 mem2 q SF_SIZE.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k q HJ H1 H2.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & HLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold SF_SIZE.
destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 q 80 HAR ltac:(lia) ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia))
  as [HRA HHL].
right. split.
- right. right. left. rewrite Elo, Ehi. lia.
- split; [|split; [exact HRA | split; [exact HHL | split; [| split; lia]]]].
  + intros a Ha. apply rty_some_of_present. apply Hpres. lia.
  + unfold amem_range. right. lia.
Qed.

(* A stretch that changes no byte outside Zs keeps every memory fact of the cut but the world relation, when Zs
   misses the frame, io_send's own 160-byte frame (the struct spec_frame and the saved words) and the shadow band.
   The world relation at the new world Bx' comes from the stretch itself. *)
Lemma rty_keep : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) mem4 md4 (regs4 : bvmap 5 word) Bx Bx'
    (Zs : Z -> Prop),
  AR_laws segs B ->
  0 < Z.of_nat (length frame) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W3) mem4 a = aview segs (w_H W3) mem3 a) ->
  (forall a, p <= a < p + Z.of_nat (length frame) -> ~ Zs a) ->
  (forall a, spZ regs - IOSEND_FRAME <= a < spZ regs -> ~ Zs a) ->
  (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ Zs a) ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly3 S3 W3 mem4 md4 ->
  ios_regs regs regs4 p frame fail ->
  (forall r, 24 <= r <= 27 -> YK11.getr regs4 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  tw_at TMAP_B (aview segs (w_H W3) mem4) Bx' ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem4 md4 regs4 Bx'.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 mem4 md4 regs4 Bx Bx' Zs LAWS Hn0 HSP KV KFR KSK KSD AT CUR RG R24 HTW4.
  destruct AT as (CUR3 & SAVED & RG3 & R243 & SFR & SRCS & GARR & SRCF & HTW).
  assert (EF : IOSEND_FRAME = 160) by reflexivity.
  assert (EO : IOS_F_OFF = 8) by reflexivity.
  assert (ES : SF_SIZE = 80) by reflexivity.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof CUR3 as (HJ3 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
  pose proof (proj1 HJi3) as HAR3.
  pose proof (trans_src_ok_place B LAWS ly3 S3 W3 mem3 md3 p (Z.of_nat (length frame)) HAR3 SRCF
                ltac:(lia)) as HPL.
  assert (HPR : 0 <= p /\ p + Z.of_nat (length frame) <= 2 ^ 64)
    by (destruct HPL as [Pl|Pl]; lia).
  clear HPL.
  assert (KSF : forall a, spZ regs - IOSEND_FRAME + IOS_F_OFF <= a <
                          spZ regs - IOSEND_FRAME + IOS_F_OFF + SF_SIZE -> ~ Zs a)
    by (intros a Ha; apply KSK; lia).
  assert (KSH : forall s, kLowMemEnd <= s < kHighShadowEnd ->
                  aview segs (w_H W3) mem4 s = aview segs (w_H W3) mem3 s)
    by (intros s Hs; apply KV; [lia | apply KSD; exact Hs]).
  split; [exact CUR|].
  split.
  { (* the saved words *)
    unfold ios_saved in SAVED |- *. rewrite Forall_forall in SAVED |- *. intros o Ho.
    assert (Hfo : 8 <= fst o <= 72).
    { unfold IOS_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [Ho|Ho]; [subst o; cbn [fst]; lia|]). destruct Ho. }
    rewrite <- (SAVED o Ho). apply rdword_ext. intros kk Hkk. apply KV; [lia | apply KSK; lia]. }
  split; [exact RG|]. split; [exact R24|].
  split.
  { (* the struct *)
    refine (rty_sframe_xw W3 W3 mem3 mem4 _ _ _ _ SFR). intros a Ha.
    apply KV; [lia | apply KSF; lia]. }
  split.
  { exact (trans_src_ok_view B ly3 S3 W3 W3 mem3 mem4
            (spZ regs - IOSEND_FRAME + IOS_F_OFF) SF_SIZE SRCS
            (fun a Ha => KV a ltac:(lia) (KSF a Ha)) KSH). }
  split.
  { (* the frame *)
    refine (rty_garr8_xw _ _ _ _ _ _ GARR _). intros a Ha. rewrite length_map in Ha.
    apply KV; [lia | apply KFR; exact Ha]. }
  split.
  { exact (trans_src_ok_view B ly3 S3 W3 W3 mem3 mem4 p (Z.of_nat (length frame)) SRCF
            (fun a Ha => KV a ltac:(lia) (KFR a Ha)) KSH). }
  exact HTW4.
Qed.

(* ------------------------------------------------------------------ *)
(* The tail: 0x830e4 .. 0x83104                                        *)
(* ------------------------------------------------------------------ *)

(* From the return of check_inflight_retry: M.fly.retries + 1 and M.fly.sent = g_now, then `j` to the epilogue. *)
Lemma rty_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) (Bx : list byte)
    (Q : world segs -> config -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B -> @AR rc segs B lyc Sc W memc mdc ->
  0 < Z.of_nat (length frame) -> iosend_frame_at p (Z.of_nat (length frame)) ->
  YM05.alloc_ceiling <= spZ regs - IOSEND_STK -> spZ regs <= 2 ^ 47 ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  (forall mem4 md4 regs4,
     ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
       ly3 S3 W3 mem4 md4 regs4
       (TW.set_M_fly_sent (TW.set_M_fly_retries Bx (DSpec.u32 (TW.M_fly_retries Bx + 1))) (TW.g_now Bx)) ->
     SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_EPI) regs4 mem4 md4) Q) ->
  SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_AT 0xe8) regs3 mem3 md3) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx Q LAWS HGX HARc Hn0 Hfr Hce H47 AT HK.
  pose proof AT as AT0.
  destruct AT as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW).
  destruct (rty_cut_vals W3 mem3 Bx HTW) as (V108 & Vnow & Z3 & Z4).
  pose proof CUR as (HJ & HFR & HPM & HMO & HKEPT).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : IOSEND_STK = 8512) by reflexivity.
  assert (FF : IOSEND_FRAME = 160) by reflexivity.
  assert (EM : TB_M = 0x5dede0) by reflexivity.
  assert (EGS : TB_g_s = 0x5df640) by reflexivity.
  assert (SM : TW.SZ_M = 1648) by reflexivity.
  assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
  assert (GLOW : forall a, inG TG.G_HARNESS_B a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (transportb_segs_low a (proj1 (HGX a Ha)))).
  (* the frame misses the 12 stored bytes: it lies outside G, or inside g_s's payload, above M *)
  assert (KFR : forall a, p <= a < p + Z.of_nat (length frame) -> ~ (TB_M + 108 <= a < TB_M + 120)).
  { intros a Ha HW. destruct Hfr as [HnG | [HG1 HG2]].
    - apply (HnG a Ha). apply (ios_inG_row _ _ _ a TMAP_B_M). unfold TW.SZ_M. lia.
    - lia. }
  clear Hfr.
  destruct (rty_entry W3 regs3 mem3 (rty_flyr Bx) (rty_now Bx) Z3 Z4 V108 Vnow) as [HS SHOK].
  set (E0 := rty_E regs3 (rty_flyr Bx) (rty_now Bx)) in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, rty_E; apply Eimg_env).
  assert (X32 : ew E0 32 = Z_to_bv 64 (rty_flyr Bx))
    by (unfold E0, rty_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
  assert (X33 : ew E0 33 = Z_to_bv 64 (rty_now Bx))
    by (unfold E0, rty_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
  destruct rty_vals as (V8 & _).
  assert (UM : bv_unsigned (ew E0 (A_OBJ 8)) = TB_M).
  { unfold E0, rty_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V8.
    apply unsigned_lit_small. lia. }
  assert (UM' : bv_unsigned (ew E0 249%nat) = TB_M) by exact UM.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
                TG.G_HARNESS_B HGX 0 []) as RUNTO.
  unfold cfg_at.
  lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOS_AT 0xe8)) mem3
      (YK11.seg_rom segs)) md3) Qx) end.
  (* the run: a0 = M, a1 = M.fly.retries (sign-extended), a2 = g_now, a1 + 1, the two stores, `j` *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_EPI.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    repeat (first
      [ apply awr_ok_x_cons_g;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
          rewrite UM' in Ha; apply (ios_inG_row _ _ _ a TMAP_B_M); unfold TW.SZ_M; lia |]
      | apply awr_ok_x_cons;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |] ]).
    apply awr_ok_x_nil. }
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
  rename ms into ms1.
  assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_M + 108 <= a < TB_M + 120) ->
    aview segs (w_H W3) (ms_mem ms1) a = aview segs (w_H W3) mem3 a).
  { intros a Ha H1.
    apply (kept_of_frame _ _ _ _ _ (fun x => TB_M + 108 <= x < TB_M + 120) HFr); [| exact Ha | exact H1].
    intros b wlo whi x Hin Hx. cbv beta. rty_win Hin Hx ltac:(rewrite ?UM' in Hx; lia). }
  assert (GA : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  (* the registers the run keeps *)
  pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ rty_kept HS (rty_agree regs3 _ _)
                ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  destruct (rty_regs_step regs regs3 (ms_regs ms1) p frame fail RG R24 KR) as (RG1 & R241).
  (* the two stored values, read from the last state's chunks of M.fly *)
  rty_chunk HS 0%nat 0%nat UM' 8%nat (rty_now Bx)
    ltac:(cbn [sv_denot]; rewrite X33, Z.add_0_r; apply Z_to_bv_bv_unsigned) V112.
  rty_chunk HS 0%nat 1%nat UM' 4%nat (bv_swrap 32 (rty_flyr Bx) + 1)
    ltac:(apply (rty_den_inc E0 32 (rty_flyr Bx) X32); lia) V108'.
  (* the world *)
  assert (HTW1 : tw_at TMAP_B (aview segs (w_H W3) (ms_mem ms1))
           (TW.set_M_fly_sent (TW.set_M_fly_retries Bx (DSpec.u32 (TW.M_fly_retries Bx + 1))) (TW.g_now Bx))).
  { apply (rty_world Bx (aview segs (w_H W3) mem3) (aview segs (w_H W3) (ms_mem ms1)) HTW).
    - intros j Hj. rewrite <- rty_le_byte_inc. exact (V108' j Hj).
    - intros j Hj. exact (V112 j Hj).
    - intros x Hx N1 N2. pose proof (GLOW x (ios_tw_in_G x Hx)) as Hl.
      apply KV; [unfold kLowMemEnd in Hl; lia | lia]. }
  (* the running kept fact: the 12 stored bytes are bytes of G and of iosend_wr *)
  assert (CUR1 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                   ly3 S3 W3 (ms_mem ms1) md4).
  { unfold ios_cur. split; [exact HJ|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
    apply (rty_kept_step TG.G_HARNESS_B lyc Sc W memc mdc W3 mem3 (ms_mem ms1)
      (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame)))
      (fun x => TB_M + 108 <= x < TB_M + 120) LAWS HGX HARc HKEPT KV GA); [| lia | lia].
    intros a Ha. cbv beta in Ha. right. split.
    - apply (ios_inG_row _ _ _ a TMAP_B_M). unfold TW.SZ_M. lia.
    - destruct (Z_lt_le_dec a (TB_M + 112)) as [H1|H1];
        [apply ios_wr_fly_retries; lia | apply ios_wr_fly_sent; lia]. }
  assert (AT1 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                  ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1)
                  (TW.set_M_fly_sent (TW.set_M_fly_retries Bx (DSpec.u32 (TW.M_fly_retries Bx + 1)))
                     (TW.g_now Bx))).
  { apply (rty_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
             ly3 S3 W3 mem3 md3 regs3 (ms_mem ms1) md4 (ms_regs ms1) Bx _
             (fun x => TB_M + 108 <= x < TB_M + 120) LAWS Hn0 HSP KV KFR).
    - intros a Ha. cbv beta. lia.
    - intros a Ha. cbv beta. unfold kLowMemEnd in Ha. lia.
    - exact AT0.
    - exact CUR1.
    - exact RG1.
    - exact R241.
    - exact HTW1. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    change (SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_EPI) rg mm mdx) Q) end.
  exact (HK _ _ _ AT1).
Qed.

(* ------------------------------------------------------------------ *)
(* The retry arm: 0x830d4 .. 0x83104                                   *)
(* ------------------------------------------------------------------ *)

Lemma ios_rty_arm : @ios_rty_arm_stmt fx rc B MT.
Proof.
unfold ios_rty_arm_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw'
  ly3 S3 W3 mem4 md4 regs4 Q HL HFX AT HCMD Hrty HM HA HK.
destruct HL as (HCELLS & _ & HRU & HRE & LAWS & MTL & HGX & HGE & _ & _ & _ & _ & HCIR & _).
destruct HFX as (HJe & Hra0 & Hra4 & Hgp & Htp & _ & _ & Hsp16 & Hlo & Hhi & Hp0 & _ & _ & Hoff & Hfr
  & _ & _ & HTWe & HFLY & _ & Hev).
(* the model: the call at B0 = ios_B0 Bw, its run invariant, the world the arm leaves *)
assert (LB : Z.of_nat (length Bw) = TW.W_LEN) by exact (rty_len_B _ _ _ HTWe).
destruct (ios_arm_retry Bw frame Bw' HA HCMD (rty_truth frame Hrty)) as [HMC EBw'].
clear HCMD.
pose proof (rty_fly_len_bound Bw frame LB HFLY HMC) as HFL.
pose proof (ios_len60 _ _ _ HM) as H60.
subst Bw'.
(* the entry journal: its AR, the stack, the layout *)
pose proof HJe as (_ & _ & (memS & HJei & _) & _). rewrite !Z.add_0_r in HJei.
pose proof HJei as (HARc & HLEc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct HLEc as (_ & _ & _ & _ & _ & EFc & _ & _ & _ & Eloc & Ehic & _).
clear HJei memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : IOSEND_STK = 8512) by reflexivity.
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (CS : CIR_STK = 8240) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hn0 : 0 < Z.of_nat (length frame)) by lia.
assert (Hce : YM05.alloc_ceiling <= spZ regs - IOSEND_STK) by lia.
assert (H47' : spZ regs <= 2 ^ 47) by lia.
(* the tail, from the return of the call *)
assert (KT : forall ly5 S5 (W5 : world segs) mem5 md5 regs5,
   ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
     ly5 S5 W5 mem5 md5 regs5 (ios_B0 Bw) ->
   SRr segs W5 (@cfg_at fx segs (transportb_text + IOS_AT 0xe8) regs5 mem5 md5) Q).
{ intros ly5 S5 W5 mem5 md5 regs5 AT5.
  exact (rty_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame (TW.g_fail_next Bw)
           ly5 S5 W5 mem5 md5 regs5 (ios_B0 Bw) Q LAWS HGX HARc Hn0 Hfr Hce H47' AT5 (HK ly5 S5 W5)). }
clear HK.
(* the cut *)
unfold ios_at_csf in AT.
pose proof AT as AT0.
destruct AT as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW).
pose proof CUR as (HJ & HFR & HPM & HMO & HKEPT).
pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
pose proof HJ as (_ & _ & (memS & HJ2i & _) & _). rewrite !Z.add_0_r in HJ2i.
pose proof HJ2i as (HAR2 & HLE2 & _).
destruct HLE2 as (_ & _ & _ & _ & _ & EF2 & _ & _ & _ & Elo2 & Ehi2 & _).
clear HJ2i memS.
(* the call setup, 0x830d4 .. 0x830e0: a2 = sp + 8, a0 = p, a1 = len, the call of check_inflight_retry *)
pose proof (rty_cs_entry W3 regs4 mem4) as HS.
set (E0 := rty_cs_E regs4) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, rty_cs_E; apply Eimg_env).
assert (SHOK : sh_ok segs RTY_Bx RTY_SH E0 (mrestrict (w_H W3) mem4)) by (unfold sh_ok, RTY_SH; constructor).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs4 r)
  by (intros n r Hn; unfold E0, rty_cs_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs - 160)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, IOSEND_FRAME; apply unsigned_lit_small; lia).
assert (ERA : BASE + 7748 = 536804) by (vm_compute; reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
              TG.G_HARNESS_B HGX 0 []) as RUN.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + IOS_RTY)) mem4
    (YK11.seg_rom segs)) md4) Qx) end.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_nil. }
set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
rename ms into msT.
assert (KV : forall a, 0 <= a < 2 ^ 64 ->
  aview segs (w_H W3) (ms_mem msT) a = aview segs (w_H W3) mem4 a).
{ intros a Ha.
  apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx. cbv beta. rty_win Hin Hx ltac:(lia). }
assert (GA : forall a, apresent (w_H W3) mem4 a -> apresent (w_H W3) (ms_mem msT) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (CUR1 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                 ly3 S3 W3 (ms_mem msT) md5).
{ unfold ios_cur. split; [exact HJ|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
  apply (rty_kept_step TG.G_HARNESS_B lyc Sc W memc mdc W3 mem4 (ms_mem msT)
    (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
    LAWS HGX HARc HKEPT ltac:(intros a Ha _; exact (KV a Ha)) GA ltac:(intros a []) ltac:(lia) ltac:(lia)). }
pose proof CUR1 as (_ & _ & _ & _ & HKEPT1).
pose proof (regs_kept_of_st_ok _ E0 _ _ regs4 _ rty_kept HS (rty_cs_agree regs4)
              ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
destruct (rty_regs_step regs regs4 (ms_regs msT) p frame (TW.g_fail_next Bw) RG R24 KR) as (RG1 & R241).
assert (AT1 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame
                (TW.g_fail_next Bw) ly3 S3 W3 (ms_mem msT) md5 (ms_regs msT) (ios_B0 Bw)).
{ apply (rty_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame (TW.g_fail_next Bw)
           ly3 S3 W3 mem4 md4 regs4 (ms_mem msT) md5 (ms_regs msT) (ios_B0 Bw) (ios_B0 Bw) (fun _ => False)
           LAWS Hn0 HSP).
  - intros a Ha _. exact (KV a Ha).
  - intros a _ [].
  - intros a _ [].
  - intros a _ [].
  - exact AT0.
  - exact CUR1.
  - exact RG1.
  - exact R241.
  - apply (tw_kept TMAP_B _ _ _ HTW). intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KV. lia. }
destruct AT1 as (_ & SAVED1 & _ & _ & SFR1 & _ & GARR1 & SRCF1 & HTW1).
replace (spZ regs - IOSEND_FRAME + IOS_F_OFF) with (spZ regs - 152) in SFR1 by (unfold IOS_F_OFF; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HART.
(* the registers at the call *)
pmkst HS.
rty_reg HS (Z_to_bv 5 10) (w64 p) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R9).
rty_reg HS (Z_to_bv 5 11) (w64 (Z.of_nat (length frame))) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R8).
rty_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (spZ regs - 152)) Q12 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
rty_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 160)) Q2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
rty_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 7748)) RA ltac:(apply codeptr_val; exact HEI).
rty_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
rty_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
assert (ESP : bv_unsigned (YK11.getr (ms_regs msT) (Z_to_bv 5 2)) = spZ regs - 160)
  by (rewrite Q2; apply unsigned_lit_small; lia).
assert (Hsp1 : spZ (ms_regs msT) = spZ regs - 160) by exact ESP.
assert (RAok : YK0s.ret_ok (Z_to_bv 64 (BASE + 7748)))
  by (apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity]).
(* 0x830e0: check_inflight_retry, through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB_check_inflight_retry)) mm rom)
    mdx) Qx) end.
eapply SRr_bind.
{ apply (@gx_call_cg fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3
    (ms_mem msT) md5 (k + 0) _ (ms_regs msT) CIR_STK CIR_EV 0 (fun _ => False)
    (fun _ _ _ => ios_B0 Bw = ios_B0 Bw) HGX HGE HJ).
  intros memS HJd.
  eapply SRr_mono.
  { apply (HCIR fx STK sp0 FP ly S W0 memS md0 own ly3 S3 W3 (ms_mem msT) md5 (k + 0) (ms_regs msT)
      p (spZ regs - 152) frame (ios_B0 Bw) (ios_B0 Bw) HJd).
    - exact (eq_ind_r (fun w => YK0s.ret_ok w) RAok RA).
    - unfold raZ. rewrite RA, ERA, unsigned_lit_small by lia. lia.
    - exact Q3.
    - exact Q4.
    - exact Q10.
    - exact Q11.
    - exact Q12.
    - rewrite Hsp1. replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia.
      rewrite Z_mod_plus_full. exact Hsp16.
    - rewrite Hsp1. lia.
    - rewrite Hsp1. lia.
    - exact Hp0.
    - exact GARR1.
    - exact SRCF1.
    - unfold decode_off_win in *. rewrite Hsp1. lia.
    - exact SFR1.
    - exact (rty_sf_src STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem msT) md5 (k + 0)
        (spZ regs - 152) HJ ltac:(lia) ltac:(lia)).
    - unfold decode_off_win. right. rewrite Hsp1. lia.
    - exact HTW1.
    - exact HMC.
    - exact HFL.
    - unfold CIR_EV, IOSEND_EV in *. lia. }
  cbv beta. intros W5 c5 _ H5. apply decode_cg_post_dcg. exact H5. }
cbv beta.
intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md6 & e & -> & He & HJ5 & HP5 & HFR5 & HPM5 & HK5 & HMO5 & (_ & HGK5)).
assert (Ee : e = 0) by (unfold CIR_EV in He; lia). subst e.
replace (k + 0 + 0) with (k + 0) in HJ5 by lia.
(* the journal at the return *)
pose proof HJ5 as (_ & _ & (memS & HJ5i & _) & _). rewrite !Z.add_0_r in HJ5i.
pose proof HJ5i as (HAR5 & HLE5 & _).
destruct HLE5 as (_ & _ & _ & _ & _ & EF5 & _ & _ & _ & Elo5 & Ehi5 & _).
clear HJ5i memS.
pose proof HK5 as (K51 & _).
(* the frame across the callee: DgnTransportBCg.v trans_src_ok_acall_g *)
destruct (trans_src_ok_acall_g B LAWS HRU HRE ly3 S3 W3 (ms_mem msT) md5 ly5 S5 W5 mem5 md6
  (spZ (ms_regs msT) - CIR_STK) (spZ (ms_regs msT)) (fun _ => False) p (Z.of_nat (length frame))
  HART HAR5 HPM5 HFR5 ltac:(intros cid pos; unfold frame_addr; rewrite EF5, EF2; reflexivity)
  ltac:(rewrite Elo5, Elo2; reflexivity) ltac:(rewrite Ehi5, Ehi2; reflexivity)
  HK5 HGK5 ltac:(intros a _ Hf; exact Hf) ltac:(intros a _ Hf; exact Hf)
  ltac:(unfold decode_off_win in Hoff; rewrite Hsp1; lia) SRCF1 Hn0) as [HSRC5 KF5].
assert (HGA5 : garr8 segs (mrestrict (w_H W5) mem5) p (map DSpec.bz frame)).
{ apply (rty_garr8_xw (w_H W3) (w_H W5) (ms_mem msT) mem5 p _ GARR1). intros a Ha.
  rewrite length_map in Ha. exact (KF5 a Ha). }
(* the running kept fact *)
assert (HK6 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W5 mem5 (spZ regs - IOSEND_STK) (spZ regs)
                 (iosend_wr (Z.of_nat (length frame)))).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly3 S3 W memc W3 (ms_mem msT) W5 mem5
    (spZ regs - IOSEND_STK) (spZ regs) (spZ (ms_regs msT) - CIR_STK) (spZ (ms_regs msT))
    (iosend_wr (Z.of_nat (length frame))) (fun _ => False) (fun _ => False)).
  - lia.
  - lia.
  - intros cid pos. unfold frame_addr. rewrite EF2, EFc. reflexivity.
  - intros f Hf. rewrite HFR. exact Hf.
  - intros bm Hbm. exact (Permutation_in _ (Permutation_sym HPM) Hbm).
  - intros b m i _ _ Hf. exact Hf.
  - intros cid pos a _ _ Hf. exact Hf.
  - exact HKEPT1.
  - exact HK5.
  - rewrite Hsp1. lia.
  - rewrite Hsp1. lia.
  - intros a Hf. destruct Hf. }
(* the saved words, the struct, the world *)
assert (HSV5 : ios_saved W5 mem5 regs).
{ unfold ios_saved in *. rewrite Forall_forall in SAVED1 |- *. intros o Ho. rewrite <- (SAVED1 o Ho).
  assert (Hd : 8 <= fst o <= 72)
    by (unfold IOS_SAVED in Ho; cbn [In] in Ho;
        repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]); destruct Ho).
  apply rdword_ext. intros j Hj.
  rewrite K51 by (rewrite ?Hsp1; lia). reflexivity. }
assert (HSF5 : trans_sframe_at W5 mem5 (spZ regs - 152) p (TC.rf frame)).
{ eapply (rty_sframe_xw W3 W5 (ms_mem msT) mem5); [|exact SFR1].
  intros a Ha. apply K51; [lia | rewrite Hsp1; lia]. }
assert (HTW5 : tw_at TMAP_B (aview segs (w_H W5) mem5) (ios_B0 Bw)).
{ apply (tw_kept TMAP_B _ _ _ HTW1). intros x Hx. exact (HGK5 x (ios_tw_in_G x Hx)). }
(* the registers *)
assert (HR5 : ios_regs regs regs5 p frame (TW.g_fail_next Bw)) by exact (rty_regs_pres _ _ _ _ _ _ RG1 HP5).
pose proof (rty_s811 regs (ms_regs msT) regs5 R241 HP5) as H8115.
assert (HCUR5 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly5 S5 W5 mem5 md6).
{ unfold ios_cur. split; [exact HJ5|]. split; [rewrite HFR5; exact HFR|].
  split; [exact (Permutation_trans HPM5 HPM)|].
  split; [exact (mo_le_trans MT MTL Sc S3 S5 0 0 HMO HMO5) | exact HK6]. }
(* the cut at the return, and the tail *)
rewrite RA, rty_pc.
specialize (KT ly5 S5 W5 mem5 md6 regs5). unfold cfg_at in KT. apply KT.
unfold ios_e2_at.
replace (spZ regs - IOSEND_FRAME + IOS_F_OFF) with (spZ regs - 152) by (unfold IOS_F_OFF; lia).
split; [exact HCUR5|]. split; [exact HSV5|]. split; [exact HR5|]. split; [exact H8115|].
split; [exact HSF5|].
split; [exact (rty_sf_src STK sp0 FP ly S W0 mem0 md0 own ly5 S5 W5 mem5 md6 (k + 0) (spZ regs - 152) HJ5
          ltac:(lia) ltac:(lia))|].
split; [exact HGA5|]. split; [exact HSRC5 | exact HTW5].
Qed.

End rty.
