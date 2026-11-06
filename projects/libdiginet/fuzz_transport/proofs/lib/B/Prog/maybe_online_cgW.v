(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths, module names and numbers changed; 693 of its 784 lines of code are new or changed and 939 lines of the source are left out. *)
(* maybe_online: Theorem transport_maybe_online_cg_holds : the statement transport_maybe_online_cg_holds_stmt of
   lib/B/Prog/maybe_online_cg.v, the machine walk of maybe_online on fuzz_transport.asan-ubsan at 0x8ae8c (332 bytes,
   frame 16), listing lib/B/Prog/DgnTransportBList.v from AF_maybe_online = 0x9bec.

   The walk is a G-form walk: it holds the caller's journal ajournal_gx G_HARNESS_B 0 [] (lib/A/W_journalG.v) from the
   entry to the return or to the tail jump, and the runs are the symbolic runs of lib/A/Prog/PaShadow.v taken over that
   journal (lib/B/Prog/TransportGRunB.v paj_run_x). The state at the entry (mob_entry) has four regions: the 16-byte
   frame below sp (the save of ra), the shadow base's GOT word (object 1, 0xa3cf0) and its cell (object 95, 0xac678),
   and the five g_s fields the code loads, read-only, each chunk holding the world's bytes (TWorldG.v tw_read_val):
     atom 33  S_state (s + 112, 4)          atom 34  S_wake_acked (s + 144, 4)    atom 35  S_e1_named_us (s + 140, 4)
     atom 36  S_last_rx_us (s + 176, 8)     atom 37  S_cfg_keepalive_ms (s + 24, 4)
   a0 = s is atom 10 with the exact fact TB_g_s (64-aligned), so the engine decides the alignment test of s (no branch
   to the trap word 0x8af74). The shadow entry MOB_SH is g_s's whole payload, whose shadow is 0 at every AR state
   (trans_maybeon_cells, DgnTransportBCg.v decode_zshadow_rd: mob_ra, mob_shok), so the engine decides the six
   instrumented checks (s + 112, s + 144, s + 140, s + 176, s + 24, s + 184): no call of __asan_report_* is reached.
   The runs and the splits (DgnTransportBPaLib.v psrr_branch_tok), each side one of the model's tests (maybeon_go):
     run 1   +0x00 .. +0x38: the frame, the save of ra, the decided checks, `bne a1, 1` on S_state;
     run 2   +0x3c .. +0x54: `beqz` on S_wake_acked;
     run 3   +0x58 .. +0x70: `beqz` on S_e1_named_us;
     a taken test: +0xdc .. +0xe4, ra loaded back, `ret` (mob_close_ret: the model's world is Bw, mob_model_ret);
     run 4   +0x74 .. +0xd8: S_next_keepalive_us (s + 184, 8 bytes) joins the state as a writable region of G
             (mob_nk), the store of S_last_rx_us + S_cfg_keepalive_ms * 1000 (mob_val), a1 = a2 = 2, ra loaded back,
             sp + 16, the tail jump to set_state (DgnTransportBList.v PTail TB_set_state).
   At the tail jump the memory relates to the world maybeon_w1 Bw (mob_world1), set_state's contract
   (set_state_cg.v transport_set_state_cg at transportb_sigma TB_set_state, the statement's premise) applies at the
   jump's state with maybe_online's ra, sp and callee-saved registers on the same journal, st = S_ONLINE and
   why = R_ONLINE; its premises come from maybe_online's: the model through maybeon_model_sstate (mob_model_go),
   g_fail_next (mob_gfn), trans_tframe_at (mob_tframe: TF's bytes miss the frame by decode_off_win and the store by
   maybeon_apart), trans_rom_view_rd (mob_rom), sstate_apart (maybeon_wr_sstate), the count and event premises
   (MAYBEON_CID = SSTATE_CID, MAYBEON_EV = SSTATE_EV). Its post is maybe_online's (mob_tail_post: the frame and the
   store lie in the window and in maybeon_wr Bw, set_state's written range in maybeon_wr Bw by maybeon_wr_sstate). *)
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
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg check_state_data_cg notice_cg set_state_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at the entry                                  *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the entry, 32 the shadow base, 33 .. 37 the five loaded fields of g_s. *)
Definition mob_gs : YP09.region := YP09.mkRegion (Some 10%nat) 24 184 0 0
  [YP09.mkChunk 24 (CVal 4 (SOff 37 0)); YP09.mkChunk 112 (CVal 4 (SOff 33 0));
   YP09.mkChunk 140 (CVal 4 (SOff 35 0)); YP09.mkChunk 144 (CVal 4 (SOff 34 0));
   YP09.mkChunk 176 (CVal 8 (SOff 36 0))].
(* S_next_keepalive_us, the writable region of G run 4 adds. *)
Definition mob_nk : YP09.region := YP09.mkRegion (Some 10%nat) 184 192 184 192 [].
Definition mob_regions : smem := [stack_region MAYBEON_FRAME; got_regionP; bcell_regionP 32; mob_gs].
Definition mob_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF TB_g_s TB_g_s 6); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (37%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_mob : sstate := mkSS AF_maybe_online sr_atoms mob_regions None mob_facts.
(* The shadow entry of g_s's payload (18264 bytes), and the shadow base of the token engine. *)
Definition MOB_SH : list shent := [mkSHE 10 0 TW.SZ_g_s].
Definition MOB_Bx : sv := SOff 32 0.

(* The values of atoms 32 .. 37 at the world Bw. *)
Definition mob_vals_l (Bw : list byte) : list word :=
  [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_S_state 4); Z_to_bv 64 (TW.u_at Bw TW.A_S_wake_acked 4);
   Z_to_bv 64 (TW.u_at Bw TW.A_S_e1_named_us 4); Z_to_bv 64 (TW.S_last_rx_us Bw);
   Z_to_bv 64 (TW.S_cfg_keepalive_ms Bw)].

(* The bytes a run may write: the frame, and from run 4 on S_next_keepalive_us. *)
Definition mob_Zr (sp a : Z) : Prop := sp - MAYBEON_FRAME <= a < sp.
Definition mob_Zg (sp a : Z) : Prop := mob_Zr sp a \/ (TB_g_s + 184 <= a < TB_g_s + 192).

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac mob_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "mob_reg: no match for" T; fail
  end.

(* ------------------------------------------------------------------ *)
(* 2. The model's tests and outcomes                                   *)
(* ------------------------------------------------------------------ *)

(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma mob_some_inv : forall Bx By : list byte, Some (Bx, tt) = Some (By, tt) -> By = Bx.
Proof. intros Bx By H. exact (eq_sym (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H)). Qed.

(* The model when the test of :178 fails: no change. *)
Lemma mob_model_ret : forall (I : TI.timg) (F : option TI.tframe) (Bw Bw' : list byte), maybeon_go Bw = false ->
  TSS.maybe_online_m I F Bw = Some (Bw', tt) -> Bw' = Bw.
Proof. intros I F Bw Bw' Hg Hm. rewrite (maybeon_model_sstate I F Bw), Hg in Hm. exact (mob_some_inv _ _ Hm). Qed.

(* The model when the test of :178 holds: set_state_m at maybeon_w1 Bw, S_ONLINE, R_ONLINE. *)
Lemma mob_model_go : forall (I : TI.timg) (F : option TI.tframe) (Bw Bw' : list byte), maybeon_go Bw = true ->
  TSS.maybe_online_m I F Bw = Some (Bw', tt) ->
  TSS.set_state_m I F (maybeon_w1 Bw) TS0.DIGINET_S_ONLINE TS0.DIGINET_R_ONLINE = Some (Bw', tt).
Proof. intros I F Bw Bw' Hg Hm. rewrite (maybeon_model_sstate I F Bw), Hg in Hm. exact Hm. Qed.

Lemma mob_go_s : forall Bw, (TW.S_state Bw =? 1) = false -> maybeon_go Bw = false.
Proof. intros Bw H. unfold maybeon_go. change TS0.DIGINET_S_WAKING with 1. rewrite H. reflexivity. Qed.

Lemma mob_go_w : forall Bw, (TW.S_wake_acked Bw =? 0) = true -> maybeon_go Bw = false.
Proof. intros Bw H. unfold maybeon_go. rewrite H. cbn [negb]. rewrite andb_false_r. reflexivity. Qed.

Lemma mob_go_e : forall Bw, (TW.S_e1_named_us Bw =? 0) = true -> maybeon_go Bw = false.
Proof. intros Bw H. unfold maybeon_go. rewrite H. cbn [negb]. rewrite andb_false_r. reflexivity. Qed.

Lemma mob_go_t : forall Bw, (TW.S_state Bw =? 1) = true -> (TW.S_wake_acked Bw =? 0) = false ->
  (TW.S_e1_named_us Bw =? 0) = false -> maybeon_go Bw = true.
Proof. intros Bw H1 H2 H3. unfold maybeon_go. change TS0.DIGINET_S_WAKING with 1. rewrite H1, H2, H3. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 3. The branch conditions and the stored value at the valuation      *)
(* ------------------------------------------------------------------ *)

Lemma mob_u64 : forall v, bv_unsigned (Z_to_bv 64 v) = v mod 2 ^ 64.
Proof. intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity. Qed.

Lemma mob_eqb_s32 : forall v w, - 2 ^ 31 <= v < 2 ^ 31 -> - 2 ^ 31 <= w < 2 ^ 31 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
  intros v w Hv Hw. unfold bv_eqb. rewrite !mob_u64.
  destruct (Z.eqb_spec v w) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intro E. apply N. Z.div_mod_to_equations. lia.
Qed.

(* The sign-extended 4-byte load of a world field is the model's s32_at. *)
Lemma mob_sext : forall (E : env) (n : nat) Bw k, ew E n = Z_to_bv 64 (TW.u_at Bw k 4) ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (TW.s32_at Bw k).
Proof.
intros E n Bw k Hew. assert (HR : 0 <= TW.u_at Bw k 4 < 2 ^ 32) by exact (TWL.u_at_range Bw k 4).
cbn [sv_denot]. rewrite Hew, Z.add_0_r.
rewrite unsigned_lit_small by lia.
change (Z_to_bv 64 (TW.u_at Bw k 4)) with (le_bytes_to_word (TW.sub Bw k 4)).
apply lw_world.
Qed.

Lemma mob_br_ne : forall (E : env) (n : nat) Bw k c, ew E n = Z_to_bv 64 (TW.u_at Bw k 4) -> - 2 ^ 31 <= c < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit c)) = negb (TW.s32_at Bw k =? c).
Proof.
intros E n Bw k c H Hc. pose proof (TWL.s32_range Bw k) as R. cbn [branch_taken]. rewrite (mob_sext E n Bw k H).
change (sv_denot E (SLit c)) with (Z_to_bv 64 c). rewrite (mob_eqb_s32 (TW.s32_at Bw k) c ltac:(lia) Hc). reflexivity.
Qed.

Lemma mob_br_eq : forall (E : env) (n : nat) Bw k c, ew E n = Z_to_bv 64 (TW.u_at Bw k 4) -> - 2 ^ 31 <= c < 2 ^ 31 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit c)) = (TW.s32_at Bw k =? c).
Proof.
intros E n Bw k c H Hc. pose proof (TWL.s32_range Bw k) as R. cbn [branch_taken]. rewrite (mob_sext E n Bw k H).
change (sv_denot E (SLit c)) with (Z_to_bv 64 c). rewrite (mob_eqb_s32 (TW.s32_at Bw k) c ltac:(lia) Hc). reflexivity.
Qed.

(* The value the store at s + 184 writes (0x8af58): S_last_rx_us + S_cfg_keepalive_ms * 1000 (mod 2^64), the model's
   u64 (S_last_rx_us + ms_m S_cfg_keepalive_ms). *)
Lemma mob_val_u : forall (E : env) Bw,
  ew E 36 = Z_to_bv 64 (TW.S_last_rx_us Bw) -> ew E 37 = Z_to_bv 64 (TW.S_cfg_keepalive_ms Bw) ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 36 0) (SMd M_MUL (SOff 37 0) (SLit 1000)))) =
  TS0.u64 (TW.S_last_rx_us Bw + TS0.ms_m (TW.S_cfg_keepalive_ms Bw)).
Proof.
intros E Bw H36 H37.
assert (R36 : 0 <= TW.S_last_rx_us Bw < 2 ^ 64) by exact (TWL.u_at_range Bw TW.A_S_last_rx_us 8).
assert (R37 : 0 <= TW.S_cfg_keepalive_ms Bw < 2 ^ 32) by exact (TWL.u_at_range Bw TW.A_S_cfg_keepalive_ms 4).
cbn [sv_denot alu64 alu mul_div]. rewrite H36, H37. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap, TS0.ms_m, TS0.u64. change (bv_modulus 64) with (2 ^ 64).
rewrite ?(Z.mod_small (TW.S_last_rx_us Bw) (2 ^ 64)), ?(Z.mod_small (TW.S_cfg_keepalive_ms Bw) (2 ^ 64)),
  ?(Z.mod_small 1000 (2 ^ 64)) by lia.
reflexivity.
Qed.

Lemma mob_val : forall (E : env) Bw,
  ew E 36 = Z_to_bv 64 (TW.S_last_rx_us Bw) -> ew E 37 = Z_to_bv 64 (TW.S_cfg_keepalive_ms Bw) ->
  sv_denot E (SAlu ALU_ADD (SOff 36 0) (SMd M_MUL (SOff 37 0) (SLit 1000))) =
  Z_to_bv 64 (TS0.u64 (TW.S_last_rx_us Bw + TS0.ms_m (TW.S_cfg_keepalive_ms Bw))).
Proof.
intros E Bw H36 H37. rewrite <- (mob_val_u E Bw H36 H37). symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* Byte j < 8 of a 64-bit word holding v is byte j of the 8-byte little-endian v. *)
Lemma mob_bow : forall v j, (j < 8)%nat ->
  bv_unsigned (byte_of_word (Z_to_bv 64 v) (Z.of_nat j)) = YO0f.le_byte v 8 j.
Proof.
intros v j Hj. unfold byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The world and G                                                  *)
(* ------------------------------------------------------------------ *)

(* g_s's payload bytes are bytes of G. *)
Lemma mob_inG : forall a, TB_g_s <= a < TB_g_s + TW.SZ_g_s -> inG G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The bytes of S_next_keepalive_us are in maybeon_wr Bw when the test of :178 holds. *)
Lemma mob_wr_nk : forall Bw a, maybeon_go Bw = true -> TB_g_s + 184 <= a < TB_g_s + 192 -> maybeon_wr Bw a.
Proof. intros Bw a Hg Ha. split; [exact Hg|]. left. unfold twb_fld, TW.A_S_next_keepalive_us. lia. Qed.

(* The 8 bytes of v stored at s + 184, every other payload byte the entry's: the world set_S_next_keepalive_us Bw v. *)
Lemma mob_world1 : forall Bw (rd0 rdT : Z -> option Z) v,
  tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 8)%nat -> rdT (TB_g_s + 184 + Z.of_nat j) = Some (YO0f.le_byte v 8 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_g_s + 184 <= x < TB_g_s + 192) -> rdT x = rd0 x) ->
  tw_at TMAP_B rdT (TW.set_S_next_keepalive_us Bw v).
Proof.
intros Bw rd0 rdT v Htw HV Hk. unfold TW.set_S_next_keepalive_us, TW.A_S_next_keepalive_us.
apply (tw_write TMAP_B rd0 rdT Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 184 8 v TMAP_B_ok Htw TMAP_B_g_s).
- lia.
- change (Z.of_nat 8) with 8. unfold TW.SZ_g_s. lia.
- exact HV.
- intros x Hx Hn. apply Hk; [exact Hx | change (Z.of_nat 8) with 8 in Hn; exact Hn].
Qed.

(* The store at s + 184 keeps g_fail_next. *)
Lemma mob_gfn : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> TW.g_fail_next (maybeon_w1 Bw) = TW.g_fail_next Bw.
Proof.
intros Bw HL. assert (WL : TW.W_LEN = 65616) by reflexivity.
unfold maybeon_w1, TW.g_fail_next, TW.set_S_next_keepalive_us, TW.A_S_next_keepalive_us.
rewrite TWL.u_at_upd_out; [reflexivity | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_fail_next; lia | |].
- right. rewrite TWL.length_put. change (Z.of_nat 8) with 8. unfold TW.OFF_g_s, TW.OFF_g_fail_next. lia.
- rewrite TWL.length_put, HL, WL. change (Z.of_nat 8) with 8. unfold TW.OFF_g_s. lia.
Qed.

Lemma mob_Forall_nth : forall {A : Type} (P : A -> Prop) (l : list A) (n : nat) (x : A),
  Forall P l -> nth_error l n = Some x -> P x.
Proof. intros A P l n x HF Hn. rewrite Forall_forall in HF. apply HF. exact (nth_error_In l n Hn). Qed.

(* ------------------------------------------------------------------ *)
(* 5. The walk's lemmas                                                *)
(* ------------------------------------------------------------------ *)

Section mobw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma mob_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  BASE + AF_maybe_online = transportb_sigma TB_maybe_online.
Proof. vm_compute. repeat split. Qed.

(* The walk's valuation: the 32 registers at the entry, the shadow base and the five loaded fields of Bw. *)
Definition mob_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transportb) (Ereg regs (mob_vals_l Bw)).

Lemma mob_agree : forall regs Bw, env_agree 32 (Ereg regs (mob_vals_l Bw)) (mob_E regs Bw).
Proof. intros regs Bw. split; [intros n Hn; unfold mob_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* The two image regions hold what transport_cells says they hold, at any AR state. *)
Lemma mob_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H W) mem) got_regionP /\ region_ok segs E (mrestrict (w_H W) mem) (bcell_regionP 32).
Proof.
  intros ly S W mem md E HCELLS HAR E1 E95 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct mob_vals as (V1 & V95 & _).
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

(* g_s's payload is addressable at every AR state: the shadow of its 2283 whole granules is 0 (trans_maybeon_cells). *)
Lemma mob_ra : forall ly S (W : world segs) mem md,
  trans_maybeon_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF MAYBEON_S TW.SZ_g_s.
Proof.
intros ly S W mem md HZ HAR x Hx.
assert (ES : MAYBEON_S = 6157888) by reflexivity. assert (SZ : TW.SZ_g_s = 18264) by reflexivity.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold shadow_of_addr.
exists 0. split; [|left; reflexivity].
assert (Hz := decode_zshadow_rd B ly S W mem md MAYBEON_S (MAYBEON_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The run's shadow entry holds at every AR state. *)
Lemma mob_shok : forall ly S (W : world segs) mem md (E : env),
  trans_maybeon_cells B -> @AR rc segs B ly S W mem md ->
  ew E 10 = Z_to_bv 64 MAYBEON_S -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs MOB_Bx MOB_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E HZ HAR E10 E32.
assert (ES : MAYBEON_S = 6157888) by reflexivity. assert (SZ : TW.SZ_g_s = 18264) by reflexivity.
unfold sh_ok, MOB_SH. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H W) mem E MOB_Bx 10 MAYBEON_S TW.SZ_g_s MAYBEON_S 0 TW.SZ_g_s
  (mob_ra ly S W mem md HZ HAR)).
- unfold U, MOB_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
- lia.
- lia.
- intros x Hx. rewrite SZ in Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The entry state, and the shadow entry of g_s. *)
Lemma mob_entry : forall ly S (W : world segs) regs mem md Bw,
  transport_cells B -> trans_maybeon_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  (forall a, spZ regs - MAYBEON_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  YK11.getr regs 10 = w64 MAYBEON_S ->
  st_ok_pi segs VAL (mob_E regs Bw) ss_mob
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_maybe_online)) mem (YK11.seg_rom segs)))
  /\ sh_ok segs MOB_Bx MOB_SH (mob_E regs Bw) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md Bw HCELLS HZ HAR Htw Hpres Hsp Hsp16 H10.
  assert (ES : MAYBEON_S = 6157888) by reflexivity. assert (EG : TB_g_s = 6157888) by reflexivity.
  set (E := mob_E regs Bw).
  assert (E2 : ew E 2 = YK11.getr regs 2) by (unfold E, mob_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 MAYBEON_S)
    by (unfold E, mob_E; rewrite (ew_Eimg_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (U10 : bv_unsigned (ew E 10) = MAYBEON_S) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (mob_vals_l Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, mob_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
  cbn [Nat.add nth mob_vals_l] in E32, E33, E34, E35, E36, E37.
  assert (EOB : forall j, (j < 96)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, mob_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct (mob_img_ok ly S W mem md E HCELLS HAR (EOB 1%nat ltac:(lia)) (EOB 95%nat ltac:(lia)) E32) as [RG RC].
  destruct mob_vals as (V1 & V95 & _).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (R33 : 0 <= TW.u_at Bw TW.A_S_state 4 < 2 ^ 32) by exact (TWL.u_at_range Bw TW.A_S_state 4).
  assert (R34 : 0 <= TW.u_at Bw TW.A_S_wake_acked 4 < 2 ^ 32) by exact (TWL.u_at_range Bw TW.A_S_wake_acked 4).
  assert (R35 : 0 <= TW.u_at Bw TW.A_S_e1_named_us 4 < 2 ^ 32) by exact (TWL.u_at_range Bw TW.A_S_e1_named_us 4).
  assert (R36 : 0 <= TW.S_last_rx_us Bw < 2 ^ 64) by exact (TWL.u_at_range Bw TW.A_S_last_rx_us 8).
  assert (R37 : 0 <= TW.S_cfg_keepalive_ms Bw < 2 ^ 32) by exact (TWL.u_at_range Bw TW.A_S_cfg_keepalive_ms 4).
  split.
  - rewrite restrict_mkst_fx. unfold ss_mob, mob_regions.
    apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [exact RG | apply Forall_cons; [exact RC |]]].
      * unfold stack_region, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Usp. unfold MAYBEON_FRAME in *.
        split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * apply Forall_cons; [|apply Forall_nil].
        unfold mob_gs, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
        -- apply (chunk_ok_val segs E _ MAYBEON_S 24 4 (SOff 37 0) (TW.S_cfg_keepalive_ms Bw));
             [apply DEN; [exact E37 | lia] | exact R37 | lia |].
           replace (TW.S_cfg_keepalive_ms Bw) with (TW.u_at Bw (TW.OFF_g_s + 24) 4) by reflexivity.
           exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 24 4 TMAP_B_ok Htw TMAP_B_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ MAYBEON_S 112 4 (SOff 33 0) (TW.u_at Bw TW.A_S_state 4));
             [apply DEN; [exact E33 | lia] | exact R33 | lia |].
           exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 112 4 TMAP_B_ok Htw TMAP_B_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ MAYBEON_S 140 4 (SOff 35 0) (TW.u_at Bw TW.A_S_e1_named_us 4));
             [apply DEN; [exact E35 | lia] | exact R35 | lia |].
           exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 140 4 TMAP_B_ok Htw TMAP_B_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ MAYBEON_S 144 4 (SOff 34 0) (TW.u_at Bw TW.A_S_wake_acked 4));
             [apply DEN; [exact E34 | lia] | exact R34 | lia |].
           exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 144 4 TMAP_B_ok Htw TMAP_B_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ MAYBEON_S 176 8 (SOff 36 0) (TW.S_last_rx_us Bw));
             [apply DEN; [exact E36 | lia] | exact R36 | lia |].
           exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 176 8 TMAP_B_ok Htw TMAP_B_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + apply pairwise_disjoint_of_extents.
      unfold stack_region, got_regionP, bcell_regionP, mob_gs, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (EOB 95%nat ltac:(lia))) by (rewrite V95; unfold FCells.CELL_K; lia).
      cbn [base_val]. rewrite Usp, U10.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      rewrite V1, V95. unfold FCells.GOT_CELL_K, FCells.CELL_K, MAYBEON_FRAME in *.
      repeat split; first [exact I | lia].
    + unfold mob_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U10, E32, E33, E34, E35, E37.
      rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
      rewrite (unsigned_lit_small (TW.u_at Bw TW.A_S_state 4)) by lia.
      rewrite (unsigned_lit_small (TW.u_at Bw TW.A_S_wake_acked 4)) by lia.
      rewrite (unsigned_lit_small (TW.u_at Bw TW.A_S_e1_named_us 4)) by lia.
      rewrite (unsigned_lit_small (TW.S_cfg_keepalive_ms Bw)) by lia.
      change (2 ^ 4) with 16. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite ES; reflexivity].
  - exact (mob_shok ly S W mem md E HZ HAR E10 E32).
Qed.

(* S_next_keepalive_us as a writable region of G, at any memory. *)
Lemma mob_nk_ok : forall E (m : word -> option byte), bv_unsigned (ew E 10) = TB_g_s -> region_ok segs E m mob_nk.
Proof.
intros E m HU. assert (EG : TB_g_s = 6157888) by reflexivity.
unfold region_ok, mob_nk. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HU. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs G_HARNESS_B (TB_g_s + o) G_HARNESS_B_rw). apply mob_inG. unfold TW.SZ_g_s. lia.
Qed.

(* What the walk keeps, from its entry memory memc to a memory m: the view outside the bytes Zs, and presence. *)
Definition mob_KA (W : world segs) (memc m : word -> option byte) (Zs : Z -> Prop) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) m a = aview segs (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m a).

(* A run whose windows lie in Zs keeps mob_KA. *)
Lemma mob_KA_step : forall E rs (W : world segs) memc (m m' : word -> option byte) (Zs : Z -> Prop),
  mob_KA W memc m Zs ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
  mob_KA W memc m' Zs.
Proof.
intros E rs W memc m m' Zs [K1 K2] Hfr Hg Hw. split.
- intros a Ha Hn. rewrite (YC4b.kept_of_frame E rs (w_H W) m m' Zs Hfr Hw a Ha Hn). exact (K1 a Ha Hn).
- intros a Ha. exact (apresent_grows _ _ _ a Hg (K2 a Ha)).
Qed.

Lemma mob_KA_g : forall (W : world segs) memc m sp, mob_KA W memc m (mob_Zr sp) -> mob_KA W memc m (mob_Zg sp).
Proof.
intros W memc m sp [K1 K2]. split; [|exact K2].
intros a Ha Hn. apply K1; [exact Ha|]. intros Hz. apply Hn. left. exact Hz.
Qed.

(* The 8 bytes of a chunk of value v, read through the view. *)
Lemma mob_chunk_rd : forall (E : env) (H : word -> bool) (mm : word -> option byte) (base off : Z) (e : sv) (v : Z),
  YP09.chunk_ok segs E (mrestrict H mm) base (YP09.mkChunk off (CVal 8 e)) -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < 8)%nat -> aview segs H mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v 8 j).
Proof.
intros E H mm base off e v HC He j Hj. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC (Z.of_nat j) ltac:(cbn; lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview segs H mm (base + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H mm) (base + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. rewrite (mob_bow v j Hj). reflexivity.
Qed.

(* The post at a return: the frame is the only byte written, the model's world is Bw. *)
Lemma mob_close_ret : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw regsF mF mdF,
  AR_laws segs B -> ameter_laws MT ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MAYBEON_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - MAYBEON_STK -> spZ regs <= 2 ^ 47 ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mF mdF k ->
  tw_at TMAP_B (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
  mob_KA W memc mF (mob_Zr (spZ regs)) ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 ->
  forall mat, transport_maybeon_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw W
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw regsF mF mdF
    LAWS MTL HAR Hwin Hce H47 Hra HJF Htw Hgf KAF HP RF1 mat.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : MAYBEON_STK = 8416) by reflexivity.
  destruct KAF as [KA GA].
  unfold transport_maybeon_post, transport_cg_post.
  exists lyc, Sc, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
  split. { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [unfold MAYBEON_EV, SSTATE_EV, NOTICE_EV; lia|].
  split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transportb_segs_low G_HARNESS_B lyc Sc W memc mdc memc mF
      (spZ regs - MAYBEON_STK) (spZ regs) (maybeon_wr Bw) (mob_Zr (spZ regs)) HAR).
    - apply dk_kept_refl_g. exact Hwin.
    - exact KA.
    - exact GA.
    - intros a Ha _. unfold mob_Zr, MAYBEON_FRAME in Ha. lia.
    - intros b m i Hb Hi Hz. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
      unfold mob_Zr, MAYBEON_FRAME in Hz. lia.
    - intros a Hz Hi _ _ _. pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
      unfold mob_Zr, MAYBEON_FRAME in Hz. lia.
    - intros cid pos a Hin Hr Hz. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      unfold mob_Zr, MAYBEON_FRAME in Hz.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  split; [|exact Hgf].
  apply (tw_kept TMAP_B (aview segs (w_H W) memc)); [exact Htw|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hh.
  apply KA; [lia | unfold mob_Zr, MAYBEON_FRAME; lia].
Qed.

(* TF at the tail jump: its bytes miss the frame (decode_off_win) and the store (maybeon_apart), and the shadow band
   is kept. *)
Lemma mob_tframe : forall lyc Sc (W : world segs) memc mdc memT regs regsT K (TF : option TI.tframe),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - K -> spZ regs <= 2 ^ 47 -> spZ regsT = spZ regs ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mob_Zg (spZ regs) a -> aview segs (w_H W) memT a = aview segs (w_H W) memc a) ->
  16 <= K ->
  (forall fr, TF = Some fr -> forall a, TI.tf_addr fr <= a < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) ->
     ~ (TB_g_s + 184 <= a < TB_g_s + 192)) ->
  trans_tframe_at B lyc Sc W memc regs K TF -> trans_tframe_at B lyc Sc W memT regsT K TF.
Proof.
intros lyc Sc W memc mdc memT regs regsT K TF LAWS HAR Hce H47 Hsp KA HK Hap HTF.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EG : TB_g_s = 6157888) by reflexivity.
destruct TF as [fr|]; [|exact I].
destruct HTF as (H0 & Hg & Hs & Ho).
assert (KV : forall a, TI.tf_addr fr <= a < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) ->
  aview segs (w_H W) memT a = aview segs (w_H W) memc a).
{ intros a Ha.
  assert (Hn : 0 < Z.of_nat (length (TI.tf_bytes fr))) by lia.
  pose proof (trans_src_ok_place B LAWS lyc Sc W memc mdc _ _ HAR Hs Hn) as P.
  apply KA.
  - destruct P as [P | P]; lia.
  - unfold mob_Zg, mob_Zr, MAYBEON_FRAME. intros [Hz | Hz].
    + unfold decode_off_win in Ho. destruct Ho as [Ho | Ho]; lia.
    + exact (Hap fr eq_refl a Ha Hz). }
split; [exact H0|]. split.
- apply (garr8_frame segs _ _ _ _ Hg). intros a Ha. rewrite length_map in Ha. apply mbyte_of_aview. exact (KV a Ha).
- split.
  + apply (trans_src_ok_view B lyc Sc W W memc memT _ _ Hs KV).
    intros s Hs'. apply KA; [lia|]. unfold mob_Zg, mob_Zr, MAYBEON_FRAME. intros [Hz | Hz]; lia.
  + unfold decode_off_win in *. rewrite Hsp. exact Ho.
Qed.

(* The TRANS_RO_RD bytes at the tail jump: below 0xa4000, apart from the frame and the store. *)
Lemma mob_rom : forall (W : world segs) memc memT sp,
  alloc_ceiling <= sp - 16 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mob_Zg sp a -> aview segs (w_H W) memT a = aview segs (w_H W) memc a) ->
  trans_rom_view_rd W memc -> trans_rom_view_rd W memT.
Proof.
intros W memc memT sp Hce KA HR. unfold trans_rom_view_rd in *. intros a Ha.
pose proof (trans_ro_rd_bounds a Ha) as Rb. pose proof asan_consts as (C1 & _).
assert (EG : TB_g_s = 6157888) by reflexivity.
rewrite (KA a ltac:(lia)); [exact (HR a Ha)|].
unfold mob_Zg, mob_Zr, MAYBEON_FRAME. intros [Hz | Hz]; lia.
Qed.

(* The post at the tail jump: set_state's post, entered at the world maybeon_w1 Bw with maybe_online's ra, sp and
   callee-saved registers on the same journal, after the frame and the store at s + 184, is maybe_online's. *)
Lemma mob_tail_post : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw Bw' memT regsT,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MAYBEON_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - MAYBEON_STK -> spZ regs <= 2 ^ 47 ->
  mob_KA W memc memT (mob_Zg (spZ regs)) ->
  aregs_preserved regs regsT -> YK11.getr regsT 1 = YK11.getr regs 1 -> spZ regsT = spZ regs ->
  maybeon_go Bw = true ->
  forall W2 c2,
  transport_sstate_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT k regsT (maybeon_w1 Bw) Bw'
    TS0.DIGINET_S_ONLINE TS0.DIGINET_R_ONLINE W2 c2 ->
  transport_maybeon_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' W2 c2.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' memT regsT
    LAWS HAR Hwin Hce H47 [KA GA] HP R1 Hsp Hgo W2 c2 HQ.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : MAYBEON_STK = 8416) by reflexivity. assert (FS' : SSTATE_STK = 8416) by reflexivity.
  assert (EG : TB_g_s = 6157888) by reflexivity.
  unfold transport_sstate_post, transport_cg_post in HQ.
  destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e & Hc & He & HJ2 & HP2 & Hfr & Hperm & HK & HMO & HX).
  unfold transport_maybeon_post, transport_cg_post.
  exists ly2, S2, regs2, mem2, md2, e.
  split; [rewrite Hc, R1; reflexivity|].
  split; [exact He|].
  split; [exact HJ2|].
  split; [exact (aregs_preserved_trans regs regsT regs2 HP HP2)|].
  split; [exact Hfr|].
  split; [exact Hperm|].
  split.
  { rewrite Hsp in HK.
    eapply dk_kept_trans_g with (W1 := W) (memX := memT) (slo' := spZ regs - SSTATE_STK) (shi' := spZ regs)
      (Eo' := sstate_wr (maybeon_w1 Bw) TS0.DIGINET_S_ONLINE TS0.DIGINET_R_ONLINE).
    - exact Hce.
    - lia.
    - apply (dk_kept_step_g segs B LAWS transportb_segs_low G_HARNESS_B lyc Sc W memc mdc memc memT
        (spZ regs - MAYBEON_STK) (spZ regs) (maybeon_wr Bw) (mob_Zg (spZ regs)) HAR).
      + apply dk_kept_refl_g. exact Hwin.
      + exact KA.
      + exact GA.
      + intros a Ha Hca. unfold mob_Zg, mob_Zr, MAYBEON_FRAME in Ha. destruct Ha as [Ha | Ha]; lia.
      + intros b m i Hb Hi Hz. unfold mob_Zg, mob_Zr, MAYBEON_FRAME in Hz. destruct Hz as [Hz | Hz].
        * exfalso. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
        * exact (mob_wr_nk Bw (b + i) Hgo Hz).
      + intros a Hz Hi HnG _ _. unfold mob_Zg, mob_Zr, MAYBEON_FRAME in Hz. destruct Hz as [Hz | Hz].
        * pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
        * apply HnG. apply mob_inG. unfold TW.SZ_g_s. lia.
      + intros cid pos a Hin Hr Hz. unfold mob_Zg, mob_Zr, MAYBEON_FRAME in Hz. destruct Hz as [Hz | Hz].
        * exfalso.
          destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
          pose proof (fs_frame_bytes_nonneg cid) as Hfs.
          destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
          pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
          assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8)
            by (apply Z.div_le_mono; lia).
          unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
        * exact (mob_wr_nk Bw a Hgo Hz).
    - exact HK.
    - lia.
    - lia.
    - intros a Ha. apply (proj2 (maybeon_wr_sstate Bw a)). split; [exact Hgo | right; exact Ha]. }
  split; [exact HMO | exact HX].
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The walk's tactics                                               *)
(* ------------------------------------------------------------------ *)

(* The write rights of a run: the frame's bytes are the caller's stack window, S_next_keepalive_us is G, the other
   regions have no writable byte. *)
Ltac mob_awr Usp U10 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?Usp, ?U10 in Ha;
      first [ lia
            | left; split; [unfold awr_byte; left; lia | lia]
            | right; left; apply mob_inG; unfold TW.SZ_g_s; lia ]
    | ]);
  apply awr_ok_x_nil.

(* The windows of a run lie in Zs. *)
Ltac mob_win Usp U10 :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp, ?U10 in Hx;
      unfold mob_Zg, mob_Zr, MAYBEON_FRAME; first [lia | (left; lia) | (right; lia)] |]);
  destruct Hin.

(* After a run: the model generalized, the kept facts carried to the run's last memory, the old machine states
   dropped, the current one named ms. *)
Ltac mob_after KA HS Usp U10 :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt;
    try clear m0 end;
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    let KA' := fresh "KAn" in
    pose proof (mob_KA_step Ex rs _ _ _ _ _ KA HFr HG ltac:(mob_win Usp U10)) as KA'; clear KA HFr HG;
    rename KA' into KA end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  repeat match goal with old : machine_state |- _ => clear old end;
  lazymatch type of HS with context [restrict _ ?m] => try rename m into ms end.

(* S_next_keepalive_us joins the state as a writable region of G (before run 4). *)
Ltac mob_add HS Usp U10 UG UC :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
    let HS1 := fresh "HS1" in
    pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) mob_nk HS eq_refl (mob_nk_ok Ex _ U10)
      ltac:(cbn [ss_mem]; unfold mob_nk; cbn [YP09.all_disjoint]; unfold YP09.extent_disjoint;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val Nat.add]; rewrite ?Usp, ?U10, ?UG, ?UC;
            unfold FCells.GOT_CELL_K, FCells.CELL_K, TB_g_s;
            repeat match goal with |- _ /\ _ => split end; try exact I; lia)) as HS1;
    clear HS; rename HS1 into HS end;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.

(* ------------------------------------------------------------------ *)
(* 7. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Lemma mob_holds : @transport_maybe_online_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_maybe_online_cg_holds_stmt.
intros HCELLS HZ LAWS MTL HGX HSS.
unfold transport_maybe_online_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TF Bw Bw'
  HJ Hra Hra4 Hgp Htp H10 Hsp16 Hlo Hhi Htw Hgf Hm HTF HROM Hapart Hcnt Hev.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MAYBEON_STK = 8416) by reflexivity.
assert (ES : MAYBEON_S = 6157888) by reflexivity.
assert (EG : TB_g_s = 6157888) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - MAYBEON_STK) by lia.
assert (Hwin : forall a, spZ regs - MAYBEON_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (LB : Z.of_nat (length Bw) = TW.W_LEN)
  by (rewrite (tw_len _ _ _ Htw); rewrite Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia]).
(* The valuation of the walk and its atoms. *)
set (E0 := mob_E regs Bw).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, mob_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros n r Hn; unfold E0, mob_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 6)%nat -> ew E0 (32 + j) = nth j (mob_vals_l Bw) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, mob_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
pose proof (EX 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth mob_vals_l] in E33, E34, E35, E36, E37.
clear EX.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E0 10 = Z_to_bv 64 MAYBEON_S) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (U10 : bv_unsigned (ew E0 10) = TB_g_s) by (rewrite E10; apply unsigned_lit_small; lia).
destruct mob_vals as (V1 & V95 & _).
assert (UG : bv_unsigned (ew E0 242%nat) = FCells.GOT_CELL_K).
{ change 242%nat with (A_OBJ 1). unfold E0, mob_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite V1. apply unsigned_lit_small. unfold FCells.GOT_CELL_K. lia. }
assert (UC : bv_unsigned (ew E0 336%nat) = FCells.CELL_K).
{ change 336%nat with (A_OBJ 95). unfold E0, mob_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite V95. apply unsigned_lit_small. unfold FCells.CELL_K. lia. }
clear V1 V95.
destruct (mob_entry lyc Sc W regs memc mdc Bw HCELLS HZ HAR Htw ltac:(intros a Ha; apply Hpres0; unfold MAYBEON_FRAME in Ha; lia)
  Hsp Hsp16 H10) as [HS SHOK].
fold E0 in HS, SHOK.
assert (KA : mob_KA W memc memc (mob_Zr (spZ regs))) by (split; [intros; reflexivity | intros a Ha; exact Ha]).
pose proof (@paj_run_x fx rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_maybe_online)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x00 .. +0x38: the frame, the save of ra, the alignment test of s and the check of s + 112 (decided),
   a1 = S_state, `bne a1, 1`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ mob_awr Usp U10. }
mob_after KA HS Usp U10.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* S_state <> S_WAKING: the return path *)
  rewrite (mob_br_ne E0 33 Bw TW.A_S_state 1 E33 ltac:(lia)) in Hc. apply negb_true_iff in Hc.
  change (TW.s32_at Bw TW.A_S_state) with (TW.S_state Bw) in Hc.
  pose proof (mob_model_ret timg_B TF Bw Bw' (mob_go_s Bw Hc) Hm) as EB. subst Bw'. clear Hc.
  (* +0xdc .. +0xe4: ra loaded back, sp + 16, `ret`. *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mob_awr Usp U10. }
  mob_after KA HS Usp U10.
  mob_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
    ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (HPF : aregs_preserved regs (ms_regs ms))
    by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (mob_vals_l Bw) HS);
        [exact (mob_agree regs Bw) | vm_compute; reflexivity]).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  exact (mob_close_ret STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (ms_regs ms) (ms_mem ms) _
    LAWS MTL HAR Hwin Hce ltac:(lia) Hra HJ Htw Hgf KA HPF RF1 mat').
- (* S_state = S_WAKING *)
  rewrite (mob_br_ne E0 33 Bw TW.A_S_state 1 E33 ltac:(lia)) in Hc. apply negb_false_iff in Hc.
  change (TW.s32_at Bw TW.A_S_state) with (TW.S_state Bw) in Hc. rename Hc into Hs1.
  (* run 2, +0x3c .. +0x54: the check of s + 144 (decided), a1 = S_wake_acked, `beqz a1`. *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mob_awr Usp U10. }
  mob_after KA HS Usp U10.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* S_wake_acked = 0: the return path *)
    rewrite (mob_br_eq E0 34 Bw TW.A_S_wake_acked 0 E34 ltac:(lia)) in Hc.
    change (TW.s32_at Bw TW.A_S_wake_acked) with (TW.S_wake_acked Bw) in Hc.
    pose proof (mob_model_ret timg_B TF Bw Bw' (mob_go_w Bw Hc) Hm) as EB. subst Bw'. clear Hc.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mob_awr Usp U10. }
    mob_after KA HS Usp U10.
    mob_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
      ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (HPF : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (mob_vals_l Bw) HS);
          [exact (mob_agree regs Bw) | vm_compute; reflexivity]).
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'.
    exact (mob_close_ret STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (ms_regs ms) (ms_mem ms) _
      LAWS MTL HAR Hwin Hce ltac:(lia) Hra HJ Htw Hgf KA HPF RF1 mat').
  + (* S_wake_acked <> 0 *)
    rewrite (mob_br_eq E0 34 Bw TW.A_S_wake_acked 0 E34 ltac:(lia)) in Hc.
    change (TW.s32_at Bw TW.A_S_wake_acked) with (TW.S_wake_acked Bw) in Hc. rename Hc into Hw1.
    (* run 3, +0x58 .. +0x70: the check of s + 140 (decided), a1 = S_e1_named_us, `beqz a1`. *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mob_awr Usp U10. }
    mob_after KA HS Usp U10.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* S_e1_named_us = 0: the return path *)
      rewrite (mob_br_eq E0 35 Bw TW.A_S_e1_named_us 0 E35 ltac:(lia)) in Hc.
      change (TW.s32_at Bw TW.A_S_e1_named_us) with (TW.S_e1_named_us Bw) in Hc.
      pose proof (mob_model_ret timg_B TF Bw Bw' (mob_go_e Bw Hc) Hm) as EB. subst Bw'. clear Hc.
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { mob_awr Usp U10. }
      mob_after KA HS Usp U10.
      mob_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
        ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
      assert (HPF : aregs_preserved regs (ms_regs ms))
        by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (mob_vals_l Bw) HS);
            [exact (mob_agree regs Bw) | vm_compute; reflexivity]).
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'.
      exact (mob_close_ret STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (ms_regs ms) (ms_mem ms) _
        LAWS MTL HAR Hwin Hce ltac:(lia) Hra HJ Htw Hgf KA HPF RF1 mat').
    * (* S_e1_named_us <> 0: the test of :178 holds *)
      rewrite (mob_br_eq E0 35 Bw TW.A_S_e1_named_us 0 E35 ltac:(lia)) in Hc.
      change (TW.s32_at Bw TW.A_S_e1_named_us) with (TW.S_e1_named_us Bw) in Hc. rename Hc into He1.
      pose proof (mob_go_t Bw Hs1 Hw1 He1) as Hgo.
      pose proof (mob_model_go timg_B TF Bw Bw' Hgo Hm) as HmS. clear Hm.
      (* run 4, +0x74 .. +0xd8: S_next_keepalive_us joins the state; the checks of s + 176, s + 24 and s + 184
         (decided), the store at s + 184, a1 = a2 = 2, ra loaded back, sp + 16, the tail jump to set_state. *)
      mob_add HS Usp U10 UG UC.
      pose proof (mob_KA_g W memc _ (spZ regs) KA) as KAg. clear KA.
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { mob_awr Usp U10. }
      mob_after KAg HS Usp U10.
      pmkst HS.
      mob_reg HS (1%bv : bv 5) (YK11.getr regs 1) QR1
        ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
      mob_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) QR2
        ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
      mob_reg HS (3%bv : bv 5) (w64 (as_gp B)) QR3
        ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
      mob_reg HS (4%bv : bv 5) (w64 (as_tp B)) QR4
        ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
      mob_reg HS (Z_to_bv 5 10) (w64 SSTATE_S) QR10
        ltac:(cbn [sv_denot]; rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
      mob_reg HS (Z_to_bv 5 11) (w64 TS0.DIGINET_S_ONLINE) QR11 ltac:(reflexivity).
      mob_reg HS (Z_to_bv 5 12) (w64 TS0.DIGINET_R_ONLINE) QR12 ltac:(reflexivity).
      (* the 8 bytes the store left at s + 184 (region 0, mob_nk, its one chunk) *)
      pose proof (mob_val E0 Bw E36 E37) as HDEN.
      lazymatch type of HS with
      | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?EF _ (restrict ?Hh ?m) =>
        pose proof (st_ok_region_nth (segs := sg) EF _ (restrict Hh m) 0 _ HS eq_refl) as RG0 end.
      cbn [ms_mem restrict] in RG0.
      destruct RG0 as (_ & _ & _ & HC0).
      cbn [YP09.r_base YP09.r_chunks base_val] in HC0.
      rewrite U10 in HC0.
      pose proof (mob_chunk_rd _ _ _ _ _ _ _ (mob_Forall_nth _ _ 0 _ HC0 eq_refl) HDEN) as V184.
      clear HC0.
      assert (HTW1 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms)) (maybeon_w1 Bw)).
      { unfold maybeon_w1. apply (mob_world1 Bw (aview segs (w_H W) memc) _ _ Htw V184).
        intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hh.
        apply (proj1 KAg); [lia | unfold mob_Zg, mob_Zr, MAYBEON_FRAME; intros [Hz | Hz]; [lia | exact (Hn Hz)]]. }
      assert (HPF : aregs_preserved regs (ms_regs ms))
        by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (mob_vals_l Bw) HS);
            [exact (mob_agree regs Bw) | vm_compute; reflexivity]).
      assert (Hsp1 : spZ (ms_regs ms) = spZ regs) by exact (f_equal bv_unsigned QR2).
      assert (Hsp16' : spZ (ms_regs ms) mod 16 = 0) by (rewrite Hsp1; exact Hsp16).
      assert (Hlo' : sp0 - STK <= spZ (ms_regs ms) - SSTATE_STK) by (rewrite Hsp1, <- maybeon_stk_eq; exact Hlo).
      assert (Hhi' : spZ (ms_regs ms) <= sp0) by (rewrite Hsp1; exact Hhi).
      assert (PTF : trans_tframe_at B lyc Sc W (ms_mem ms) (ms_regs ms) SSTATE_STK TF).
      { rewrite <- maybeon_stk_eq.
        apply (mob_tframe lyc Sc W memc mdc (ms_mem ms) regs (ms_regs ms) MAYBEON_STK TF LAWS HAR Hce ltac:(lia)
          Hsp1 (proj1 KAg) ltac:(lia)).
        - intros fr Efr a Ha Hz. exact (Hapart a (mob_wr_nk Bw a Hgo Hz) fr Efr Ha).
        - exact HTF. }
      assert (PROM : trans_rom_view_rd W (ms_mem ms))
        by exact (mob_rom W memc (ms_mem ms) (spZ regs) ltac:(lia) (proj1 KAg) HROM).
      assert (PAP : sstate_apart TF (maybeon_w1 Bw) TS0.DIGINET_S_ONLINE TS0.DIGINET_R_ONLINE).
      { intros x Hx fr Efr.
        exact (Hapart x (proj2 (maybeon_wr_sstate Bw x) (conj Hgo (or_intror Hx))) fr Efr). }
      assert (PGF : TW.g_fail_next (maybeon_w1 Bw) <= 1) by (rewrite (mob_gfn Bw LB); exact Hgf).
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_set_state) rg mm mdx) Q) end.
      eapply SRr_mono.
      { exact (HSS fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) _ k (ms_regs ms)
          TS0.DIGINET_S_ONLINE TS0.DIGINET_R_ONLINE TF (maybeon_w1 Bw) Bw'
          HJ (eq_ind_r YK0s.ret_ok Hra QR1) (eq_ind_r (fun w => 4096 <= bv_unsigned w) Hra4 QR1) QR3 QR4 QR10 QR11 QR12
          Hsp16' Hlo' Hhi' HTW1 PGF HmS
          ltac:(unfold TS0.DIGINET_S_ONLINE; lia) ltac:(unfold TS0.DIGINET_R_ONLINE; lia)
          PTF PROM PAP Hcnt Hev). }
      intros W2 c2 _ HQ.
      exact (mob_tail_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' (ms_mem ms) (ms_regs ms)
        LAWS HAR Hwin Hce ltac:(lia) KAg HPF QR1 Hsp1 Hgo W2 c2 HQ).
Qed.

End mobw.

(* The statement of lib/B/Prog/maybe_online_cg.v. *)
Theorem transport_maybe_online_cg_holds : forall fx rc B MT, @transport_maybe_online_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@mob_holds fx rc B MT). Qed.
