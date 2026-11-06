(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v for libreac/fuzz_grant's program walk: the listing's names are gsym, PALib names fuzz_grant.asan's objects and the wrappers' 4-byte jumps, and fuzz_grant's image bound; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: taken by path from libreac/fuzz_grant's copy (proofs/libreac/fuzz_grant/lib/A/Prog/GrantPaLib.v, file sha256 1750b9b228be; donor not released) for libreac/fuzz_decode's
   program walk: module paths and the listing's names changed. *)
(* Modified by Theorem Labs, 2026-10: image B's twin of this unit's lib/A/Prog/DecodePaLib.v, in the shape of proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBPaLib.v (file sha256 73c9e12166f6; donor not released): the names are dbsym's (the wrappers' free and malloc entries are DB___interceptor_trampoline_free and DB___interceptor_trampoline_malloc); PALib names fuzz_decode.asan-ubsan's objects of lib/B/Prog/DecodeBAddr.v and lib/B/AsanCells.v: the shadow-base GOT word is object 1 (GOT_CELL_K 0x992e8) and its cell object 14 (CELL_K 0xa1338), the side-stack flag's GOT word object 0 (GOT_UAR 0x99340) and its cell object 15 (UAR 0xa1340); the two cells are one object later than image A's 13 and 14 because image B's slots load one more object (object 13, 0x103c8); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/DgnTransportBPaLib.v; 9 of its 34 lines of code are new or changed and 475 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/TransportGRunB.v, with its module paths and module names changed; 398 of its 427 lines of code are new or changed and 5 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_lib.v, with its module paths and module names changed; 780 of its 864 lines of code are new or changed and 343 lines of the source are left out. *)
(* m_tick: Theorem transport_m_tick_cg_holds : the statement transport_m_tick_cg_holds_stmt of lib/B/Prog/m_tick_cg.v,
   the machine walk of m_tick on fuzz_transport.asan-ubsan at 0x8383c (132 bytes, no frame). Image B has no m_lost
   function: on both lost paths m_tick makes m_lost's two stores itself and tail-jumps to m_set.

   The walk holds the caller's journal ajournal_gx G_HARNESS_B 0 [] (lib/A/W_journalG.v) from the entry to the return
   or to the tail jump; the runs are the symbolic runs of lib/A/Prog/PaShadow.v taken over that journal
   (TransportGRunB.v paj_run_x). The run's regions are the six world fields m_tick loads, each a read-only region of
   its harness global whose bytes are the world's (TWorldG.v tw_read_val); each loaded value is an atom of the walk's
   valuation mt_E:
     atom 33  M.state (M + 12, 4 bytes)       atom 34  M.wake_sent (M + 40, 8)    atom 35  g_now (8)
     atom 36  g_cfg.wake_timeout_ms (4)       atom 37  M.last_rx (M + 32, 8)      atom 38  g_cfg.offline_ms (4)
   (M, g_now, g_cfg + 44 and g_cfg + 40 are the listing's image objects 8, 28, 41 and 42.)
   The three branches the run cannot decide are split (DgnTransportBPaLib.v paj_branch); each side is the model's test
   (mt_br_state_eq / mt_br_state_ne / mt_br_on / mt_br_wk):
     M.state = 2 (S_ONLINE):  u64 (g_now - last_rx) >= offline_ms * 1000: a1 = 4, the stores, tail jump; else return;
     M.state <> 2, <> 1:      return;
     M.state = 1 (S_WAKING):  u64 (g_now - wake_sent) < wake_timeout_ms * 1000: return; else a1 = 6, the stores, tail
                              jump.
   No instrumented check and no error or trap path is on the code. A return closes with mt_close_ret: the model's world
   is Bw and every byte is the entry's. On a lost path the two fields M.desk_counter_valid (M + 76) and M.fly.on
   (M + 96) join the state as writable regions of G (mt_dcv, mt_fly) before the last run, which stores 0 in both
   (bytes of G: the run's write right awr_ok_x), sets a0 = 0 and takes the tail jump. The memory then relates to the
   world mt_B1 Bw (m_lost_m's two setters, mt_world1); the statement's premise transport_m_set_cg applies at the jump's
   state with m_tick's ra, sp and callee-saved registers on the same journal, and its post gives m_tick's post
   (mt_tail_post: the two stores and m_set's written range mset_st_wr (mt_B1 Bw) S_IDLE lie in mtick_wr Bw). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg m_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the entry                                     *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the entry, 32 the shadow base (no shadow entry: m_tick has no instrumented check),
   33 .. 38 the six loaded fields. Regions: the loaded bytes of M (object 8), g_now (object 28),
   g_cfg.wake_timeout_ms (object 41) and g_cfg.offline_ms (object 42), each with no writable byte. *)
Definition mt_M : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 12 48 0 0
  [YP09.mkChunk 12 (YP09.CVal 4 (SOff 33 0)); YP09.mkChunk 32 (YP09.CVal 8 (SOff 37 0));
   YP09.mkChunk 40 (YP09.CVal 8 (SOff 34 0))].
Definition mt_now : YP09.region := YP09.mkRegion (Some (A_OBJ 28)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff 35 0))].
Definition mt_wto : YP09.region := YP09.mkRegion (Some (A_OBJ 41)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 36 0))].
Definition mt_off : YP09.region := YP09.mkRegion (Some (A_OBJ 42)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 38 0))].
Definition mt_regions : smem := [mt_M; mt_now; mt_wto; mt_off].
Definition mt_facts : facts :=
  mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (36%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (38%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_mt : sstate := mkSS AF_m_tick sr_atoms mt_regions None mt_facts.
Definition MT_SH : list shent := [].
Definition MT_Bx : sv := SOff 32 0.
(* The two fields m_lost stores, the writable regions of G a lost path adds before its last run. *)
Definition mt_dcv : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 76 80 76 80 [].
Definition mt_fly : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 96 100 96 100 [].
(* Their bytes. *)
Definition mt_Wd (a : Z) : Prop := (TB_M + 76 <= a < TB_M + 80) \/ (TB_M + 96 <= a < TB_M + 100).

(* The values of atoms 32 .. 38 at the world Bw. *)
Definition mt_vals (Bw : list byte) : list word :=
  [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4); Z_to_bv 64 (TW.M_wake_sent Bw);
   Z_to_bv 64 (TW.g_now Bw); Z_to_bv 64 (TW.Cfg_wake_timeout_ms Bw); Z_to_bv 64 (TW.M_last_rx Bw);
   Z_to_bv 64 (TW.Cfg_offline_ms Bw)].

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac mt_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "mt_reg: no match for" T; fail
  end.

(* ------------------------------------------------------------------ *)
(* The model's tests                                                   *)
(* ------------------------------------------------------------------ *)

Lemma mt_some_inv : forall x y : list byte, Some (x, tt) = Some (y, tt) -> y = x.
Proof. intros x y H. injection H as H. symmetry. exact H. Qed.

Lemma mt_rng4 : forall Bw k, 0 <= TW.u_at Bw k 4 < 2 ^ 32.
Proof. intros Bw k. exact (TWL.u_at_range Bw k 4). Qed.
Lemma mt_rng8 : forall Bw k, 0 <= TW.u_at Bw k 8 < 2 ^ 64.
Proof. intros Bw k. exact (TWL.u_at_range Bw k 8). Qed.

(* M.state = 2 and the silence test holds: m_lost (R_SILENCE). *)
Lemma mt_path_on_call : forall Bw, TW.M_state Bw = 2 ->
  (TCB.h_ms_m (TW.Cfg_offline_ms Bw) <=? TS0.u64 (TW.g_now Bw - TW.M_last_rx Bw)) = true ->
  TCB.m_tick_m Bw = TCB.m_lost_m Bw 4 /\ mtick_lost Bw = true.
Proof. intros Bw H1 H2. unfold TCB.m_tick_m, mtick_lost. rewrite H1, H2. split; reflexivity. Qed.

(* M.state = 2 and the silence test fails: no change. *)
Lemma mt_path_on_ret : forall Bw, TW.M_state Bw = 2 ->
  (TCB.h_ms_m (TW.Cfg_offline_ms Bw) <=? TS0.u64 (TW.g_now Bw - TW.M_last_rx Bw)) = false ->
  TCB.m_tick_m Bw = Some (Bw, tt).
Proof. intros Bw H1 H2. unfold TCB.m_tick_m. rewrite H1, H2. reflexivity. Qed.

(* M.state is neither 2 nor 1: no change. *)
Lemma mt_path_idle : forall Bw, TW.M_state Bw <> 2 -> TW.M_state Bw <> 1 -> TCB.m_tick_m Bw = Some (Bw, tt).
Proof.
intros Bw H1 H2. unfold TCB.m_tick_m, TCB.S_WAKING, TCB.S_ONLINE.
rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
Qed.

(* M.state = 1 and the wake limit has not run out: no change. *)
Lemma mt_path_wk_ret : forall Bw, TW.M_state Bw = 1 ->
  (TS0.u64 (TW.g_now Bw - TW.M_wake_sent Bw) <? TCB.h_ms_m (TW.Cfg_wake_timeout_ms Bw)) = true ->
  TCB.m_tick_m Bw = Some (Bw, tt).
Proof.
intros Bw H1 H2. apply Z.ltb_lt in H2. unfold TCB.m_tick_m. rewrite H1.
rewrite (proj2 (Z.leb_gt _ _) H2). reflexivity.
Qed.

(* M.state = 1 and the wake limit has run out: m_lost (R_WAKE_TIMEOUT). *)
Lemma mt_path_wk_call : forall Bw, TW.M_state Bw = 1 ->
  (TS0.u64 (TW.g_now Bw - TW.M_wake_sent Bw) <? TCB.h_ms_m (TW.Cfg_wake_timeout_ms Bw)) = false ->
  TCB.m_tick_m Bw = TCB.m_lost_m Bw 6 /\ mtick_lost Bw = true.
Proof.
intros Bw H1 H2. apply Z.ltb_ge in H2. unfold TCB.m_tick_m, mtick_lost. rewrite H1.
rewrite (proj2 (Z.leb_le _ _) H2). split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The branch conditions at the valuation, in the model's terms        *)
(* ------------------------------------------------------------------ *)

(* The sign-extended 4-byte load of M.state is the model's M_state. *)
Lemma mt_sext_state : forall E Bw, ew E 33 = Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4) ->
  sv_denot E (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (TW.M_state Bw).
Proof.
intros E Bw H. pose proof (mt_rng4 Bw TW.A_M_state) as R. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma mt_eqb_state : forall E Bw c, ew E 33 = Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4) -> 0 <= c < 2 ^ 31 ->
  bv_eqb (sv_denot E (SExt true 32 (SOff 33 0))) (sv_denot E (SLit c)) = (TW.M_state Bw =? c).
Proof.
intros E Bw c H Hc. rewrite (mt_sext_state E Bw H). cbn [sv_denot]. unfold bv_eqb.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (bv_swrap_in_range 32 (TW.u_at Bw TW.A_M_state 4) ltac:(discriminate)) as R.
change (bv_swrap 32 (TW.u_at Bw TW.A_M_state 4)) with (TW.M_state Bw) in R.
change (bv_half_modulus 32) with (2 ^ 31) in R.
rewrite (Z.mod_small c (2 ^ 64)) by lia.
destruct (Z.eqb_spec (TW.M_state Bw) c) as [Heq | Hne].
- rewrite Heq. rewrite (Z.mod_small c (2 ^ 64)) by lia. apply Z.eqb_refl.
- apply Z.eqb_neq. intros HH. apply Hne.
  destruct (Z_lt_le_dec (TW.M_state Bw) 0) as [Hneg | Hpos].
  + rewrite <- (Z.mod_unique (TW.M_state Bw) (2 ^ 64) (-1) (TW.M_state Bw + 2 ^ 64)) in HH by lia. lia.
  + rewrite (Z.mod_small (TW.M_state Bw) (2 ^ 64)) in HH by lia. exact HH.
Qed.

Lemma mt_br_state_eq : forall E Bw c, ew E 33 = Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4) -> 0 <= c < 2 ^ 31 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff 33 0))) (sv_denot E (SLit c)) = (TW.M_state Bw =? c).
Proof. intros E Bw c H Hc. cbn [branch_taken]. exact (mt_eqb_state E Bw c H Hc). Qed.

Lemma mt_br_state_ne : forall E Bw c, ew E 33 = Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4) -> 0 <= c < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff 33 0))) (sv_denot E (SLit c)) = negb (TW.M_state Bw =? c).
Proof. intros E Bw c H Hc. cbn [branch_taken]. rewrite (mt_eqb_state E Bw c H Hc). reflexivity. Qed.

(* x - y (mod 2^64), as the run computes it: x + y * -1, in either order. *)
Lemma mt_neg : forall E n1 n2 x y, ew E n1 = Z_to_bv 64 x -> ew E n2 = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff n1 0) (SMd M_MUL (SOff n2 0) (SLit (-1))))) = TS0.u64 (x - y).
Proof.
intros E n1 n2 x y H1 H2 Rx Ry. cbn [sv_denot alu64 alu mul_div].
rewrite H1, H2. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap, TS0.u64. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small x (2 ^ 64)), (Z.mod_small y (2 ^ 64)) by lia.
rewrite Zplus_mod_idemp_r.
replace (-1 mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace (x + y * (2 ^ 64 - 1)) with (x - y + y * 2 ^ 64) by ring.
apply Z_mod_plus_full.
Qed.

Lemma mt_neg' : forall E n1 n2 x y, ew E n1 = Z_to_bv 64 x -> ew E n2 = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff n2 0) (SLit (-1))) (SOff n1 0))) = TS0.u64 (x - y).
Proof.
intros E n1 n2 x y H1 H2 Rx Ry. cbn [sv_denot alu64 alu mul_div].
rewrite H1, H2. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap, TS0.u64. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small x (2 ^ 64)), (Z.mod_small y (2 ^ 64)) by lia.
rewrite Zplus_mod_idemp_l.
replace (-1 mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace (y * (2 ^ 64 - 1) + x) with (x - y + y * 2 ^ 64) by ring.
apply Z_mod_plus_full.
Qed.

(* v * 1000 (mod 2^64): the model's h_ms_m. *)
Lemma mt_ms : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SMd M_MUL (SOff n 0) (SLit 1000))) = TCB.h_ms_m x.
Proof.
intros E n x H Rx. cbn [sv_denot mul_div].
rewrite H. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite bv_mul_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap, TCB.h_ms_m, TS0.u64. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small x (2 ^ 64)), (Z.mod_small 1000 (2 ^ 64)) by lia. reflexivity.
Qed.

(* The online test (0x838a4, bgeu a1, a2). *)
Lemma mt_br_on : forall E Bw,
  ew E 35 = Z_to_bv 64 (TW.g_now Bw) -> ew E 37 = Z_to_bv 64 (TW.M_last_rx Bw) ->
  ew E 38 = Z_to_bv 64 (TW.Cfg_offline_ms Bw) ->
  branch_taken BC_GEU (sv_denot E (SAlu ALU_ADD (SOff 35 0) (SMd M_MUL (SOff 37 0) (SLit (-1)))))
    (sv_denot E (SMd M_MUL (SOff 38 0) (SLit 1000)))
  = (TCB.h_ms_m (TW.Cfg_offline_ms Bw) <=? TS0.u64 (TW.g_now Bw - TW.M_last_rx Bw)).
Proof.
intros E Bw H35 H37 H38. cbn [branch_taken]. unfold bv_ltu.
pose proof (mt_rng4 Bw TW.A_Cfg_offline_ms) as R38.
rewrite (mt_neg E 35 37 (TW.g_now Bw) (TW.M_last_rx Bw) H35 H37 (mt_rng8 Bw TW.OFF_g_now)
  (mt_rng8 Bw TW.A_M_last_rx)).
rewrite (mt_ms E 38 (TW.Cfg_offline_ms Bw) H38 ltac:(change (TW.Cfg_offline_ms Bw) with
  (TW.u_at Bw TW.A_Cfg_offline_ms 4); lia)).
rewrite Z.leb_antisym. reflexivity.
Qed.

(* The waking test (0x83878, bltu a1, a2). *)
Lemma mt_br_wk : forall E Bw,
  ew E 34 = Z_to_bv 64 (TW.M_wake_sent Bw) -> ew E 35 = Z_to_bv 64 (TW.g_now Bw) ->
  ew E 36 = Z_to_bv 64 (TW.Cfg_wake_timeout_ms Bw) ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 34 0) (SLit (-1))) (SOff 35 0)))
    (sv_denot E (SMd M_MUL (SOff 36 0) (SLit 1000)))
  = (TS0.u64 (TW.g_now Bw - TW.M_wake_sent Bw) <? TCB.h_ms_m (TW.Cfg_wake_timeout_ms Bw)).
Proof.
intros E Bw H34 H35 H36. cbn [branch_taken]. unfold bv_ltu.
pose proof (mt_rng4 Bw TW.A_Cfg_wake_timeout_ms) as R36.
rewrite (mt_neg' E 35 34 (TW.g_now Bw) (TW.M_wake_sent Bw) H35 H34 (mt_rng8 Bw TW.OFF_g_now)
  (mt_rng8 Bw TW.A_M_wake_sent)).
rewrite (mt_ms E 36 (TW.Cfg_wake_timeout_ms Bw) H36 ltac:(change (TW.Cfg_wake_timeout_ms Bw) with
  (TW.u_at Bw TW.A_Cfg_wake_timeout_ms 4); lia)).
reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The world after m_lost's two stores                                 *)
(* ------------------------------------------------------------------ *)

(* m_lost_m's world before its m_set (TCb.v:183). *)
Definition mt_B1 (Bw : list byte) : list byte := TW.set_M_desk_counter_valid (TW.set_M_fly_on Bw 0) 0.

Lemma mt_lost_set : forall Bw why, TCB.m_lost_m Bw why = TCB.m_set_m (mt_B1 Bw) TCB.S_IDLE why.
Proof. intros Bw why. reflexivity. Qed.

Lemma mt_B1_len : forall Bw, Z.of_nat (length Bw) = TW.W_LEN ->
  Z.of_nat (length (TW.upd Bw (TW.OFF_M + 96 + 0) (TW.put 4 0))) = TW.W_LEN.
Proof.
intros Bw HL. assert (WL : TW.W_LEN = 65616) by reflexivity.
rewrite TWL.length_upd_put; [exact HL | unfold TW.OFF_M; lia | try change (Z.of_nat 4) with 4; unfold TW.OFF_M; lia].
Qed.

Lemma mt_B1_state : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> TW.M_state (mt_B1 Bw) = TW.M_state Bw.
Proof.
intros Bw HL. assert (WL : TW.W_LEN = 65616) by reflexivity. pose proof (mt_B1_len Bw HL) as L1.
unfold mt_B1, TW.M_state, TW.set_M_desk_counter_valid, TW.set_M_fly_on, TW.A_M_state, TW.A_M_desk_counter_valid,
  TW.A_M_fly_on.
rewrite (TWL.s32_at_upd_out _ (TW.put 4 0)) by (rewrite ?TWL.length_put, ?L1; try change (Z.of_nat 4) with 4;
  unfold TW.OFF_M in *; lia).
rewrite (TWL.s32_at_upd_out Bw (TW.put 4 0)) by (rewrite ?TWL.length_put; try change (Z.of_nat 4) with 4;
  unfold TW.OFF_M in *; lia).
reflexivity.
Qed.

Lemma mt_B1_n : forall Bw, Z.of_nat (length Bw) = TW.W_LEN -> TW.OW_n (mt_B1 Bw) = TW.OW_n Bw.
Proof.
intros Bw HL. assert (WL : TW.W_LEN = 65616) by reflexivity. pose proof (mt_B1_len Bw HL) as L1.
unfold mt_B1, TW.OW_n, TW.set_M_desk_counter_valid, TW.set_M_fly_on, TW.A_OW_n, TW.A_M_desk_counter_valid,
  TW.A_M_fly_on.
rewrite (TWL.s32_at_upd_out _ (TW.put 4 0)) by (rewrite ?TWL.length_put, ?L1; try change (Z.of_nat 4) with 4;
  unfold TW.OFF_M, TW.OFF_OW in *; lia).
rewrite (TWL.s32_at_upd_out Bw (TW.put 4 0)) by (rewrite ?TWL.length_put; try change (Z.of_nat 4) with 4;
  unfold TW.OFF_M, TW.OFF_OW in *; lia).
reflexivity.
Qed.

(* A view that is rdF on the bytes P marks and rd0 elsewhere: the written bytes so far, the entry's on the others. *)
Definition mt_in (lo n x : Z) : bool := (lo <=? x) && (x <? lo + n).
Definition mt_mix (P : Z -> bool) (rdF rd0 : Z -> option Z) : Z -> option Z :=
  fun x => if P x then rdF x else rd0 x.

Lemma mt_in_true : forall lo n x, lo <= x < lo + n -> mt_in lo n x = true.
Proof. intros lo n x H. unfold mt_in. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma mt_in_false' : forall lo n x, ~ (lo <= x < lo + n) -> mt_in lo n x = false.
Proof.
intros lo n x H. unfold mt_in. destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x (lo + n)); cbn [andb];
  first [reflexivity | exfalso; lia].
Qed.
Lemma mt_in_false : forall lo n x, mt_in lo n x = false -> ~ (lo <= x < lo + n).
Proof. intros lo n x H Hx. rewrite (mt_in_true lo n x Hx) in H. discriminate H. Qed.

Lemma mt_tw_start : forall rdF rd0 Bw, tw_at TMAP_B rd0 Bw -> tw_at TMAP_B (mt_mix (fun _ => false) rdF rd0) Bw.
Proof. intros rdF rd0 Bw H. apply (tw_kept TMAP_B rd0 _ Bw H). intros x _. reflexivity. Qed.

(* One 4-byte store of v at the world offset ko = o + k of the row (o, b, n). *)
Lemma mt_tw_step : forall rdF rd0 P Bw o b n k ko v,
  tw_at TMAP_B (mt_mix P rdF rd0) Bw -> In (o, b, n) TMAP_B -> ko = o + k -> 0 <= k -> k + 4 <= n ->
  (forall j, (j < 4)%nat -> rdF (b + k + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  tw_at TMAP_B (mt_mix (fun x => P x || mt_in (b + k) 4 x) rdF rd0) (TW.upd Bw ko (TW.put 4 v)).
Proof.
intros rdF rd0 P Bw o b n k ko v H Hin Hko Hk Hkn HV. subst ko.
apply (tw_write TMAP_B (mt_mix P rdF rd0) (mt_mix (fun x => P x || mt_in (b + k) 4 x) rdF rd0) Bw o b n k 4 v
  TMAP_B_ok H Hin Hk ltac:(change (Z.of_nat 4) with 4; lia)).
- intros j Hj. unfold mt_mix. cbv beta.
  rewrite (mt_in_true (b + k) 4 (b + k + Z.of_nat j)) by lia. rewrite orb_true_r. exact (HV j Hj).
- intros x Hx Hn. unfold mt_mix. cbv beta. change (Z.of_nat 4) with 4 in Hn.
  rewrite (mt_in_false' (b + k) 4 x) by lia. rewrite orb_false_r. reflexivity.
Qed.

Lemma mt_tw_end : forall rdF rd0 P Bw, tw_at TMAP_B (mt_mix P rdF rd0) Bw ->
  (forall x, tw_in TMAP_B x -> P x = false -> rdF x = rd0 x) -> tw_at TMAP_B rdF Bw.
Proof.
intros rdF rd0 P Bw H Hk. apply (tw_kept TMAP_B (mt_mix P rdF rd0) rdF Bw H).
intros x Hx. unfold mt_mix. destruct (P x) eqn:E; [reflexivity | exact (Hk x Hx E)].
Qed.

Ltac mt_unP HP :=
  cbv beta in HP;
  repeat match type of HP with
  | orb _ _ = false =>
      let Hq := fresh "Hq" in apply orb_false_iff in HP; destruct HP as [HP Hq]; apply mt_in_false in Hq
  end.

(* M.fly.on and M.desk_counter_valid stored 0, every other payload byte the entry's: the world mt_B1 Bw. *)
Lemma mt_world1 : forall Bw rd0 rdF,
  tw_at TMAP_B rd0 Bw ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_M + 76 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_M + 96 <= x < TB_M + 100) -> ~ (TB_M + 76 <= x < TB_M + 80) ->
     rdF x = rd0 x) ->
  tw_at TMAP_B rdF (mt_B1 Bw).
Proof.
intros Bw rd0 rdF Htw V96 V76 Hk.
assert (SM : TW.SZ_M = 1648) by reflexivity.
unfold mt_B1, TW.set_M_desk_counter_valid, TW.set_M_fly_on, TW.A_M_desk_counter_valid, TW.A_M_fly_on.
pose proof (mt_tw_start rdF rd0 Bw Htw) as H0.
pose proof (mt_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 96 (TW.OFF_M + 96 + 0) 0 H0 TMAP_B_M
  ltac:(lia) ltac:(lia) ltac:(lia) V96) as H1.
pose proof (mt_tw_step rdF rd0 _ _ TW.OFF_M TB_M TW.SZ_M 76 (TW.OFF_M + 76) 0 H1 TMAP_B_M
  ltac:(lia) ltac:(lia) ltac:(lia) V76) as H2.
apply (mt_tw_end rdF rd0 _ _ H2).
intros x Hx HP. mt_unP HP. apply Hk; [exact Hx | lia | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* G                                                                   *)
(* ------------------------------------------------------------------ *)

Lemma mt_inG : forall a, TB_M <= a < TB_M + 1648 -> inG G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TB_M, TW.SZ_M).
split; [exact (TMAP_B_in_G _ _ _ TMAP_B_M) | unfold in_zr, TW.SZ_M; cbn [fst snd]; lia].
Qed.

(* A payload byte of the world table is a byte of G. *)
Lemma mt_tw_in_G : forall x, tw_in TMAP_B x -> inG G_HARNESS_B x.
Proof.
intros x (o & b & n & Hin & Hx). unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The exact base of M, 32-byte aligned. *)
Lemma mt_fact : forall E, bv_unsigned (ew E 249%nat) = TB_M -> afact_ok E 249%nat (mkAF TB_M TB_M 5).
Proof.
intros E U. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U.
split; [lia|]. split; [reflexivity | lia].
Qed.

(* The two added regions lie apart from each other and from the loaded fields. *)
Lemma mt_disj : forall E, bv_unsigned (ew E 249%nat) = TB_M -> bv_unsigned (ew E 269%nat) = TB_g_now ->
  bv_unsigned (ew E 282%nat) = TB_g_cfg + 44 -> bv_unsigned (ew E 283%nat) = TB_g_cfg + 40 ->
  YP09.all_disjoint E mt_fly mt_regions /\ YP09.all_disjoint E mt_dcv (mt_fly :: mt_regions).
Proof.
intros E U8 U28 U41 U42. unfold mt_regions, mt_dcv, mt_fly, mt_M, mt_now, mt_wto, mt_off, A_OBJ.
cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val Nat.add].
rewrite U8, U28, U41, U42. unfold TB_M, TB_g_now, TB_g_cfg.
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The write rights of a run: the read-only regions have no writable byte; the regions of M are bytes of G. *)
Ltac mt_awr UME :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia | rewrite UME in Ha; right; left; apply mt_inG; lia ] |]);
  apply awr_ok_x_nil.

(* Byte j < 4 of a 64-bit word holding v is byte j of the 4-byte little-endian v. *)
Lemma mt_bow : forall v j, (j < 4)%nat ->
  bv_unsigned (byte_of_word (Z_to_bv 64 v) (Z.of_nat j)) = YO0f.le_byte v 4 j.
Proof.
intros v j Hj. unfold byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). change (2 ^ Z.of_N 64) with (2 ^ 64). change (8 * Z.of_nat 4) with 32.
change 256 with (2 ^ 8).
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

Section mtw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma mt_vals_img : VAL (A_OBJ 8) = TB_M /\ VAL (A_OBJ 28) = TB_g_now /\ VAL (A_OBJ 41) = TB_g_cfg + 44 /\
  VAL (A_OBJ 42) = TB_g_cfg + 40 /\ BASE + AF_m_tick = transportb_sigma TB_m_tick.
Proof. vm_compute. repeat split. Qed.

(* The walk's valuation: the 32 registers at the entry, the shadow base and the six loaded fields of Bw. *)
Definition mt_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transportb) (Ereg regs (mt_vals Bw)).

Lemma mt_agree : forall regs Bw, env_agree 32 (Ereg regs (mt_vals Bw)) (mt_E regs Bw).
Proof. intros regs Bw. split; [intros n Hn; unfold mt_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* The entry state: the four regions hold the world's bytes. *)
Lemma mt_entry : forall (W : world segs) regs mem Bw,
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  st_ok_pi segs VAL (mt_E regs Bw) ss_mt
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_tick)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem Bw Htw.
  destruct mt_vals_img as (V8 & V28 & V41 & V42 & _).
  set (E := mt_E regs Bw).
  assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, mt_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (B8 : base_val E (Some (A_OBJ 8)) = TB_M)
    by (apply VB; [rewrite (EOB 8%nat ltac:(lia)), V8; reflexivity | unfold TB_M; lia]).
  assert (B28 : base_val E (Some (A_OBJ 28)) = TB_g_now)
    by (apply VB; [rewrite (EOB 28%nat ltac:(lia)), V28; reflexivity | unfold TB_g_now; lia]).
  assert (B41 : base_val E (Some (A_OBJ 41)) = TB_g_cfg + 44)
    by (apply VB; [rewrite (EOB 41%nat ltac:(lia)), V41; reflexivity | unfold TB_g_cfg; lia]).
  assert (B42 : base_val E (Some (A_OBJ 42)) = TB_g_cfg + 40)
    by (apply VB; [rewrite (EOB 42%nat ltac:(lia)), V42; reflexivity | unfold TB_g_cfg; lia]).
  assert (EX : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (mt_vals Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, mt_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
  pose proof (EX 6%nat ltac:(lia)) as E38.
  cbn [Nat.add nth mt_vals] in E32, E33, E34, E35, E36, E37, E38.
  pose proof (mt_rng4 Bw TW.A_M_state) as R33. pose proof (mt_rng8 Bw TW.A_M_wake_sent) as R34.
  pose proof (mt_rng8 Bw TW.OFF_g_now) as R35.
  assert (R36 : 0 <= TW.Cfg_wake_timeout_ms Bw < 2 ^ 32) by exact (mt_rng4 Bw TW.A_Cfg_wake_timeout_ms).
  pose proof (mt_rng8 Bw TW.A_M_last_rx) as R37.
  assert (R38 : 0 <= TW.Cfg_offline_ms Bw < 2 ^ 32) by exact (mt_rng4 Bw TW.A_Cfg_offline_ms).
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  rewrite restrict_mkst_fx. unfold ss_mt.
  apply (pa_entry_st_ok_full (PI := PI_transportb)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold mt_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + unfold mt_M, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B8.
      split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val segs E _ TB_M 12 4 (SOff 33 0) (TW.u_at Bw TW.A_M_state 4));
          [apply DEN; [exact E33 | lia] | exact R33 | lia |].
        exact (tw_read_val segs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 12 4 TMAP_B_ok Htw TMAP_B_M
          ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
      * apply (chunk_ok_val segs E _ TB_M 32 8 (SOff 37 0) (TW.M_last_rx Bw));
          [apply DEN; [exact E37 | exact R37] | exact R37 | lia |].
        exact (tw_read_val segs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 32 8 TMAP_B_ok Htw TMAP_B_M
          ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
      * apply (chunk_ok_val segs E _ TB_M 40 8 (SOff 34 0) (TW.M_wake_sent Bw));
          [apply DEN; [exact E34 | exact R34] | exact R34 | lia |].
        exact (tw_read_val segs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 40 8 TMAP_B_ok Htw TMAP_B_M
          ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold mt_now, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B28.
      split; [unfold TB_g_now; lia|]. split; [unfold TB_g_now; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TB_g_now 0 8 (SOff 35 0) (TW.g_now Bw));
        [apply DEN; [exact E35 | exact R35] | exact R35 | lia |].
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_now TB_g_now TW.SZ_g_now 0 8 TMAP_B_ok Htw TMAP_B_g_now
        ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)).
    + unfold mt_wto, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B41.
      split; [unfold TB_g_cfg; lia|]. split; [unfold TB_g_cfg; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (TB_g_cfg + 44) 0 4 (SOff 36 0) (TW.Cfg_wake_timeout_ms Bw));
        [apply DEN; [exact E36 | lia] | exact R36 | lia |].
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 44 4 TMAP_B_ok Htw TMAP_B_g_cfg
        ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
    + unfold mt_off, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B42.
      split; [unfold TB_g_cfg; lia|]. split; [unfold TB_g_cfg; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (TB_g_cfg + 40) 0 4 (SOff 38 0) (TW.Cfg_offline_ms Bw));
        [apply DEN; [exact E38 | lia] | exact R38 | lia |].
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 40 4 TMAP_B_ok Htw TMAP_B_g_cfg
        ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
  - unfold mt_regions, mt_M, mt_now, mt_wto, mt_off.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B8, B28, B41, B42.
    unfold TB_M, TB_g_now, TB_g_cfg. repeat split; lia.
  - unfold mt_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, E33, E36, E38.
    rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_state 4)) by lia.
    rewrite (unsigned_lit_small (TW.Cfg_wake_timeout_ms Bw)) by lia.
    rewrite (unsigned_lit_small (TW.Cfg_offline_ms Bw)) by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* A field of M of 4 bytes at offset lo, as a writable region of G, at any memory. *)
Lemma mt_wr_ok : forall E (m : word -> option byte) lo, bv_unsigned (ew E (A_OBJ 8)) = TB_M -> 0 <= lo ->
  lo + 4 <= 1648 -> region_ok segs E m (YP09.mkRegion (Some (A_OBJ 8)) lo (lo + 4) lo (lo + 4) []).
Proof.
intros E m lo HU H0 H1. assert (EM : TB_M = 6155744) by reflexivity.
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HU. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs G_HARNESS_B (TB_M + o) G_HARNESS_B_rw). apply mt_inG. lia.
Qed.

(* What the walk keeps, from its entry memory memc to a memory m: every byte's view, and presence. *)
Definition mt_KA (W : world segs) (memc m : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) m a = aview segs (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m a).

(* A run from a state with mt_regions writes nothing. *)
Lemma mt_KA_step : forall E (W : world segs) memc (m m' : word -> option byte),
  mt_KA W memc m ->
  frame_of E mt_regions (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  mt_KA W memc m'.
Proof.
intros E W memc m m' [K1 K2] Hfr Hg. split.
- assert (Hw : forall b wlo whi x, In (b, wlo, whi) (windows mt_regions) ->
    base_val E b + wlo <= x < base_val E b + whi -> (fun _ : Z => False) x).
  { intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; exfalso; lia |]).
    destruct Hin. }
  intros a Ha.
  rewrite (kept_of_frame E mt_regions (w_H W) m m' (fun _ => False) Hfr Hw a Ha (fun x => x)).
  exact (K1 a Ha).
- intros a Ha. exact (apresent_grows _ _ _ a Hg (K2 a Ha)).
Qed.

(* A run from a state with mt_dcv and mt_fly added writes at most their bytes. *)
Lemma mt_KA_store : forall E (W : world segs) memc (m m' : word -> option byte),
  bv_unsigned (ew E 249%nat) = TB_M ->
  mt_KA W memc m ->
  frame_of E (mt_dcv :: mt_fly :: mt_regions) (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mt_Wd a -> aview segs (w_H W) m' a = aview segs (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m' a).
Proof.
intros E W memc m m' UM [K1 K2] Hfr Hg. split.
- assert (Hw : forall b wlo whi x, In (b, wlo, whi) (windows (mt_dcv :: mt_fly :: mt_regions)) ->
    base_val E b + wlo <= x < base_val E b + whi -> mt_Wd x).
  { intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin];
      [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?UM in Hx; unfold mt_Wd; lia |]).
    destruct Hin. }
  intros a Ha Hn.
  rewrite (kept_of_frame E (mt_dcv :: mt_fly :: mt_regions) (w_H W) m m' mt_Wd Hfr Hw a Ha Hn).
  exact (K1 a Ha).
- intros a Ha. exact (apresent_grows _ _ _ a Hg (K2 a Ha)).
Qed.

Lemma mt_tw_keep : forall (W : world segs) memc m Bw, mt_KA W memc m ->
  tw_at TMAP_B (aview segs (w_H W) memc) Bw -> tw_at TMAP_B (aview segs (w_H W) m) Bw.
Proof.
intros W memc m Bw [KA _] H. apply (tw_kept TMAP_B (aview segs (w_H W) memc)); [exact H|].
intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hh.
apply KA. lia.
Qed.

Lemma mt_Forall_nth : forall {A : Type} (P : A -> Prop) (l : list A) (n : nat) (x : A),
  Forall P l -> nth_error l n = Some x -> P x.
Proof. intros A P l n x HF Hn. rewrite Forall_forall in HF. apply HF. exact (nth_error_In l n Hn). Qed.

(* The 4 bytes of a chunk of value v, read through the view. *)
Lemma mt_chunk_rd : forall (E : env) (H : word -> bool) (mm : word -> option byte) (base off : Z) (e : sv) (v : Z),
  YP09.chunk_ok segs E (mrestrict H mm) base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < 4)%nat -> aview segs H mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof.
intros E H mm base off e v HC He j Hj. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC (Z.of_nat j) ltac:(cbn; lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview segs H mm (base + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H mm) (base + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply mt_bow. exact Hj.
Qed.

(* The 4 bytes of the chunk number c of region number idx of the state of HS (at a tail jump), base rewritten by
   UB: forall j < 4, the view at base + off + j is le_byte v 4 j, for Hden : sv_denot E e = Z_to_bv 64 v. *)
Ltac mt_chunk HS idx c UB v Hden V :=
  let RG := fresh "RG" in let HC := fresh "HC" in let HC1 := fresh "HCk" in
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?EF _ (restrict ?Hh ?m) =>
    pose proof (st_ok_region_nth (segs := sg) EF _ (restrict Hh m) idx _ HS eq_refl) as RG end;
  cbn [ms_mem restrict] in RG;
  destruct RG as (_ & _ & _ & HC);
  cbn [YP09.r_base YP09.r_chunks base_val] in HC;
  rewrite UB in HC;
  pose proof (mt_Forall_nth _ _ c _ HC eq_refl) as HC1;
  pose proof (mt_chunk_rd _ _ _ _ _ _ v HC1 Hden) as V;
  clear HC HC1.

(* The post at a return: nothing changed, the model's world is Bw. *)
Lemma mt_close_ret : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw regsF mF mdF,
  AR_laws segs B -> ameter_laws MT ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MTICK_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mF mdF k ->
  tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
  mt_KA W memc mF ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 ->
  forall mat, transport_mtick_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw W
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw regsF mF mdF
    LAWS MTL HAR Hwin Hra HJF Htw KAF HP RF1 mat.
  pose proof KAF as [KA GA].
  unfold transport_mtick_post, transport_cg_post.
  exists lyc, Sc, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
  split.
  { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [unfold MTICK_EV, MSET_EV; lia|].
  split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transportb_segs_low G_HARNESS_B lyc Sc W memc mdc memc mF
      (spZ regs - MTICK_STK) (spZ regs) (mtick_wr Bw) (fun _ => False) HAR).
    - apply dk_kept_refl_g. exact Hwin.
    - intros a Ha _. exact (KA a Ha).
    - exact GA.
    - intros a [].
    - intros b m i _ _ [].
    - intros a [].
    - intros cid pos a _ _ []. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  exact (mt_tw_keep W memc mF Bw KAF Htw).
Qed.

(* The post at the tail jump: m_set's post, entered at the world mt_B1 Bw with m_tick's ra, sp and callee-saved
   registers on the same journal, after the two stores, is m_tick's. *)
Lemma mt_tail_post : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw Bw' memT regsT,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MTICK_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - MTICK_STK -> spZ regs <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mt_Wd a -> aview segs (w_H W) memT a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memT a) ->
  aregs_preserved regs regsT -> YK11.getr regsT 1 = YK11.getr regs 1 -> spZ regsT = spZ regs ->
  mtick_lost Bw = true -> Z.of_nat (length Bw) = TW.W_LEN ->
  forall W2 c2,
  transport_mset_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT k regsT (mt_B1 Bw) TCB.S_IDLE Bw' W2 c2 ->
  transport_mtick_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' W2 c2.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' memT regsT
    LAWS HAR Hwin Hce H47 KA GA HP R1 Hsp HL LB W2 c2 HQ.
  pose proof asan_consts as (C1 & _).
  assert (EM : TB_M = 6155744) by reflexivity.
  assert (ZE : forall a, mt_Wd a -> mtick_wr Bw a).
  { intros a Ha. unfold mtick_wr. split; [exact HL|]. unfold mt_Wd in Ha.
    unfold mlost_wr, twb_fld, TW.A_M_desk_counter_valid, TW.A_M_fly_on.
    destruct Ha as [Ha | Ha]; [left | right; left]; lia. }
  assert (ZG : forall a, mt_Wd a -> inG G_HARNESS_B a) by (intros a Ha; apply mt_inG; unfold mt_Wd in Ha; lia).
  unfold transport_mset_post, transport_cg_post in HQ.
  destruct HQ as (ly2 & S2 & regs2 & mem2 & md2 & e & Hc & He & HJ2 & HP2 & Hfr & Hperm & HK & HMO & HX).
  unfold transport_mtick_post, transport_cg_post.
  exists ly2, S2, regs2, mem2, md2, e.
  split; [rewrite Hc, R1; reflexivity|].
  split; [exact He|].
  split; [exact HJ2|].
  split; [exact (aregs_preserved_trans regs regsT regs2 HP HP2)|].
  split; [exact Hfr|].
  split; [exact Hperm|].
  split.
  { rewrite Hsp in HK.
    eapply dk_kept_trans_g with (W1 := W) (memX := memT) (slo' := spZ regs - MSET_STK) (shi' := spZ regs)
      (Eo' := mset_st_wr (mt_B1 Bw) TCB.S_IDLE).
    - exact Hce.
    - lia.
    - apply (dk_kept_step_g segs B LAWS transportb_segs_low G_HARNESS_B lyc Sc W memc mdc memc memT
        (spZ regs - MTICK_STK) (spZ regs) (mtick_wr Bw) mt_Wd HAR).
      + apply dk_kept_refl_g. exact Hwin.
      + intros a Ha Hn. exact (KA a Ha Hn).
      + exact GA.
      + intros a Ha Hca. exfalso. unfold mt_Wd in Ha. lia.
      + intros b m i _ _ Hz. exact (ZE _ Hz).
      + intros a Ha _ HnG _ _. exact (HnG (ZG a Ha)).
      + intros cid pos a _ _ Hz. exact (ZE a Hz).
    - exact HK.
    - unfold MTICK_STK. lia.
    - lia.
    - intros a Ha. unfold mtick_wr. split; [exact HL|]. unfold mlost_wr. right; right.
      unfold mset_st_wr, mset_wr in Ha |- *. rewrite (mt_B1_state Bw LB), (mt_B1_n Bw LB) in Ha. exact Ha. }
  split; [exact HMO | exact HX].
Qed.

(* After a run: the model generalized, the kept facts carried to the run's last memory, the old machine states
   dropped, the current one named ms. *)
Ltac mt_after KA HS :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt;
    try clear m0 end;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    let KA' := fresh "KAn" in
    pose proof (mt_KA_step _ _ _ _ _ KA HFr HG) as KA'; clear KA HFr HG; rename KA' into KA end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  repeat match goal with old : machine_state |- _ => clear old end;
  lazymatch type of HS with context [restrict _ ?m] => try rename m into ms end.

(* After the run that stores into M: the same, the kept facts outside the two fields. *)
Ltac mt_after_st KA HS UM KAT GAT :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt;
    try clear m0 end;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    destruct (mt_KA_store _ _ _ _ _ UM KA HFr HG) as [KAT GAT]; clear KA HFr HG end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  repeat match goal with old : machine_state |- _ => clear old end;
  lazymatch type of HS with context [restrict _ ?m] => try rename m into ms end.

(* On a lost path: the exact base of M (its 32-byte alignment), which places the two windows outside the shadow
   span (YCbn.v cells_safe_b), and M.fly.on and M.desk_counter_valid as writable regions of G join the state. *)
Ltac mt_add HS UM UM' U28 U41 U42 :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let HS1 := fresh "HS1" in
    pose proof (st_ok_pi_add_fact Ex ss m 249%nat (mkAF TB_M TB_M 5) HS (mt_fact Ex UM')) as HS1;
    clear HS; rename HS1 into HS end;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
    let HS1 := fresh "HS1" in
    pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) mt_fly HS eq_refl (mt_wr_ok Ex _ 96 UM ltac:(lia) ltac:(lia))
      (proj1 (mt_disj Ex UM' U28 U41 U42))) as HS1;
    clear HS; rename HS1 into HS end;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
    let HS1 := fresh "HS1" in
    pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) mt_dcv HS eq_refl (mt_wr_ok Ex _ 76 UM ltac:(lia) ltac:(lia))
      (proj2 (mt_disj Ex UM' U28 U41 U42))) as HS1;
    clear HS; rename HS1 into HS end;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
    let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.

(* The walk. *)
Lemma mt_holds : @transport_m_tick_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_m_tick_cg_holds_stmt.
intros HCELLS LAWS MTL HGX HMS.
unfold transport_m_tick_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw'
  HJ Hra Hra4 Hgp Htp Hsp16 Hlo Hhi Htw Hm Hev.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MTICK_STK = 16) by reflexivity.
assert (EM : TB_M = 6155744) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - MTICK_STK) by lia.
assert (Hwin : forall a, spZ regs - MTICK_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (GLOW : forall a, inG G_HARNESS_B a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (transportb_segs_low a (proj1 (HGX a Ha)))).
assert (LB : Z.of_nat (length Bw) = TW.W_LEN)
  by (rewrite (tw_len _ _ _ Htw); rewrite Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia]).
(* The valuation of the walk and its atoms. *)
set (E0 := mt_E regs Bw).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, mt_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros n r Hn; unfold E0, mt_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 7)%nat -> ew E0 (32 + j) = nth j (mt_vals Bw) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, mt_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
pose proof (EX 5%nat ltac:(lia)) as E37. pose proof (EX 6%nat ltac:(lia)) as E38.
cbn [Nat.add nth mt_vals] in E33, E34, E35, E36, E37, E38.
clear EX.
destruct mt_vals_img as (V8 & V28 & V41 & V42 & _).
assert (UM : bv_unsigned (ew E0 (A_OBJ 8)) = TB_M).
{ unfold E0, mt_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V8.
  apply unsigned_lit_small. unfold TB_M. lia. }
assert (U28 : bv_unsigned (ew E0 (A_OBJ 28)) = TB_g_now).
{ unfold E0, mt_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V28.
  apply unsigned_lit_small. unfold TB_g_now. lia. }
assert (U41 : bv_unsigned (ew E0 (A_OBJ 41)) = TB_g_cfg + 44).
{ unfold E0, mt_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V41.
  apply unsigned_lit_small. unfold TB_g_cfg. lia. }
assert (U42 : bv_unsigned (ew E0 (A_OBJ 42)) = TB_g_cfg + 40).
{ unfold E0, mt_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V42.
  apply unsigned_lit_small. unfold TB_g_cfg. lia. }
assert (UM' : bv_unsigned (ew E0 249%nat) = TB_M) by exact UM.
assert (U28' : bv_unsigned (ew E0 269%nat) = TB_g_now) by exact U28.
assert (U41' : bv_unsigned (ew E0 282%nat) = TB_g_cfg + 44) by exact U41.
assert (U42' : bv_unsigned (ew E0 283%nat) = TB_g_cfg + 40) by exact U42.
clear V8 V28 V41 V42.
pose proof (mt_entry W regs memc Bw Htw) as HS. fold E0 in HS.
assert (SHOK : sh_ok segs MT_Bx MT_SH E0 (mrestrict (w_H W) memc)) by (unfold sh_ok, MT_SH; apply Forall_nil).
assert (KA : mt_KA W memc memc) by (split; [intros; reflexivity | intros a Ha; exact Ha]).
pose proof (@paj_run_x fx rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_tick)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x00 .. +0x10: a0 = &M, a1 = M.state, `beq a1, 2`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ mt_awr UM'. }
mt_after KA HS.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* M.state = S_ONLINE *)
  rewrite (mt_br_state_eq E0 Bw 2 E33 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. rename Hc into Hon.
  (* run 2, +0x48 .. +0x68: the silence test, `bgeu`. *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mt_awr UM'. }
  mt_after KA HS.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + rewrite (mt_br_on E0 Bw E35 E37 E38) in Hc.
    destruct (mt_path_on_call Bw Hon Hc) as [HmE HL]. rewrite HmE in Hm. clear Hc.
    rewrite (mt_lost_set Bw 4) in Hm.
    (* run 3, +0x70 .. +0x80: a1 = 4, the stores of 0 at M + 76 and M + 96, a0 = 0, the tail jump. *)
    mt_add HS UM UM' U28' U41' U42'.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mt_awr UM'. }
    mt_after_st KA HS UM' KAT GAT.
    (* the tail jump to m_set with a0 = 0, a1 = 4: m_set's contract at the jump's state, then mt_tail_post *)
    pmkst HS.
    mt_reg HS (1%bv : bv 5) (YK11.getr regs 1) R1
      ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    mt_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) R2
      ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    mt_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
      ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
    mt_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
      ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
    mt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 0) R10 ltac:(reflexivity).
    mt_reg HS (Z_to_bv 5 11) (Z_to_bv 64 4) R11 ltac:(reflexivity).
    mt_chunk HS 0%nat 0%nat UM' 0 (@eq_refl _ (Z_to_bv 64 0)) V76.
    mt_chunk HS 1%nat 0%nat UM' 0 (@eq_refl _ (Z_to_bv 64 0)) V96.
    assert (HTW1 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms)) (mt_B1 Bw)).
    { apply (mt_world1 Bw (aview segs (w_H W) memc) _ Htw V96 V76).
      intros x Hx N1 N2. pose proof (GLOW x (mt_tw_in_G x Hx)) as Hl. unfold kLowMemEnd in Hl.
      apply KAT; [lia | unfold mt_Wd; lia]. }
    assert (HPF : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (mt_vals Bw) HS);
          [exact (mt_agree regs Bw) | vm_compute; reflexivity]).
    assert (Hsp1 : spZ (ms_regs ms) = spZ regs) by exact (f_equal bv_unsigned R2).
    assert (Hsp16' : spZ (ms_regs ms) mod 16 = 0) by (rewrite Hsp1; exact Hsp16).
    assert (Hlo' : sp0 - STK <= spZ (ms_regs ms) - MSET_STK) by (rewrite Hsp1; exact Hlo).
    assert (Hhi' : spZ (ms_regs ms) <= sp0) by (rewrite Hsp1; exact Hhi).
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_m_set) rg mm mdx) Q) end.
    eapply SRr_mono.
    { exact (HMS fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) _ k (ms_regs ms) TCB.S_IDLE 4 (mt_B1 Bw) Bw'
        HJ (eq_ind_r YK0s.ret_ok Hra R1) (eq_ind_r (fun w => 4096 <= bv_unsigned w) Hra4 R1) R3 R4 R10 R11
        Hsp16' Hlo' Hhi' HTW1 Hm ltac:(unfold TCB.S_IDLE; lia) ltac:(lia) Hev). }
    intros W2 c2 _ HQ.
    exact (mt_tail_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' (ms_mem ms) (ms_regs ms)
      LAWS HAR Hwin Hce ltac:(lia) KAT GAT HPF R1 Hsp1 HL LB W2 c2 HQ).
  + rewrite (mt_br_on E0 Bw E35 E37 E38) in Hc.
    rewrite (mt_path_on_ret Bw Hon Hc) in Hm. apply mt_some_inv in Hm. subst Bw'. clear Hc.
    (* run 3, +0x6c: `ret`. *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mt_awr UM'. }
    mt_after KA HS.
    (* the return: ra and the callee-saved registers are the entry's; nothing changed *)
    mt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
      ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (HPF : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (mt_vals Bw) HS);
          [exact (mt_agree regs Bw) | vm_compute; reflexivity]).
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'.
    exact (mt_close_ret STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (ms_regs ms) (ms_mem ms) _
      LAWS MTL HAR Hwin Hra HJ Htw KA HPF RF1 mat').
- (* M.state <> S_ONLINE *)
  rewrite (mt_br_state_eq E0 Bw 2 E33 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hn2.
  (* run 2, +0x14 .. +0x18: `bne a1, 1`. *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mt_awr UM'. }
  mt_after KA HS.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + rewrite (mt_br_state_ne E0 Bw 1 E33 ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    rewrite (mt_path_idle Bw Hn2 Hc) in Hm. apply mt_some_inv in Hm. subst Bw'. clear Hc.
    (* run 3, +0x6c: `ret`. *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mt_awr UM'. }
    mt_after KA HS.
    (* the return: ra and the callee-saved registers are the entry's; nothing changed *)
    mt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
      ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (HPF : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (mt_vals Bw) HS);
          [exact (mt_agree regs Bw) | vm_compute; reflexivity]).
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'.
    exact (mt_close_ret STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (ms_regs ms) (ms_mem ms) _
      LAWS MTL HAR Hwin Hra HJ Htw KA HPF RF1 mat').
  + rewrite (mt_br_state_ne E0 Bw 1 E33 ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    rename Hc into Hw1.
    (* run 3, +0x1c .. +0x3c: the wake-limit test, `bltu`. *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mt_awr UM'. }
    mt_after KA HS.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * rewrite (mt_br_wk E0 Bw E34 E35 E36) in Hc.
      rewrite (mt_path_wk_ret Bw Hw1 Hc) in Hm. apply mt_some_inv in Hm. subst Bw'. clear Hc.
      (* run 4, +0x6c: `ret`. *)
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { mt_awr UM'. }
      mt_after KA HS.
      (* the return: ra and the callee-saved registers are the entry's; nothing changed *)
      mt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
        ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
      assert (HPF : aregs_preserved regs (ms_regs ms))
        by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (mt_vals Bw) HS);
            [exact (mt_agree regs Bw) | vm_compute; reflexivity]).
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'.
      exact (mt_close_ret STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw (ms_regs ms) (ms_mem ms) _
        LAWS MTL HAR Hwin Hra HJ Htw KA HPF RF1 mat').
    * rewrite (mt_br_wk E0 Bw E34 E35 E36) in Hc.
      destruct (mt_path_wk_call Bw Hw1 Hc) as [HmE HL]. rewrite HmE in Hm. clear Hc.
      rewrite (mt_lost_set Bw 6) in Hm.
      (* run 4, +0x40 .. +0x44 and +0x74 .. +0x80: a1 = 6, the jump to the stores of 0 at M + 76 and M + 96,
         a0 = 0, the tail jump. *)
      mt_add HS UM UM' U28' U41' U42'.
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { mt_awr UM'. }
      mt_after_st KA HS UM' KAT GAT.
      (* the tail jump to m_set with a0 = 0, a1 = 6: m_set's contract at the jump's state, then mt_tail_post *)
      pmkst HS.
      mt_reg HS (1%bv : bv 5) (YK11.getr regs 1) R1
        ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
      mt_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) R2
        ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
      mt_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
        ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
      mt_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
        ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
      mt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 0) R10 ltac:(reflexivity).
      mt_reg HS (Z_to_bv 5 11) (Z_to_bv 64 6) R11 ltac:(reflexivity).
      mt_chunk HS 0%nat 0%nat UM' 0 (@eq_refl _ (Z_to_bv 64 0)) V76.
      mt_chunk HS 1%nat 0%nat UM' 0 (@eq_refl _ (Z_to_bv 64 0)) V96.
      assert (HTW1 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms)) (mt_B1 Bw)).
      { apply (mt_world1 Bw (aview segs (w_H W) memc) _ Htw V96 V76).
        intros x Hx N1 N2. pose proof (GLOW x (mt_tw_in_G x Hx)) as Hl. unfold kLowMemEnd in Hl.
        apply KAT; [lia | unfold mt_Wd; lia]. }
      assert (HPF : aregs_preserved regs (ms_regs ms))
        by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (mt_vals Bw) HS);
            [exact (mt_agree regs Bw) | vm_compute; reflexivity]).
      assert (Hsp1 : spZ (ms_regs ms) = spZ regs) by exact (f_equal bv_unsigned R2).
      assert (Hsp16' : spZ (ms_regs ms) mod 16 = 0) by (rewrite Hsp1; exact Hsp16).
      assert (Hlo' : sp0 - STK <= spZ (ms_regs ms) - MSET_STK) by (rewrite Hsp1; exact Hlo).
      assert (Hhi' : spZ (ms_regs ms) <= sp0) by (rewrite Hsp1; exact Hhi).
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_m_set) rg mm mdx) Q) end.
      eapply SRr_mono.
      { exact (HMS fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) _ k (ms_regs ms) TCB.S_IDLE 6 (mt_B1 Bw) Bw'
          HJ (eq_ind_r YK0s.ret_ok Hra R1) (eq_ind_r (fun w => 4096 <= bv_unsigned w) Hra4 R1) R3 R4 R10 R11
          Hsp16' Hlo' Hhi' HTW1 Hm ltac:(unfold TCB.S_IDLE; lia) ltac:(lia) Hev). }
      intros W2 c2 _ HQ.
      exact (mt_tail_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' (ms_mem ms) (ms_regs ms)
        LAWS HAR Hwin Hce ltac:(lia) KAT GAT HPF R1 Hsp1 HL LB W2 c2 HQ).
Qed.

End mtw.

(* The statement of lib/B/Prog/m_tick_cg.v. *)
Theorem transport_m_tick_cg_holds : forall fx rc B MT, @transport_m_tick_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@mt_holds fx rc B MT). Qed.
