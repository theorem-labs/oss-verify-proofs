(* m_tick: Theorem transport_m_tick_cg_holds : the statement transport_m_tick_cg_holds_stmt of lib/A/Prog/m_tick_cg.v,
   the machine walk of m_tick on fuzz_transport.asan at 0x83c34 (120 bytes, no frame, no store).

   The walk holds the caller's journal ajournal_gx G_HARNESS 0 [] (lib/A/W_journalG.v) from the entry to the return or
   to the tail jump; the runs are the symbolic runs of lib/A/Prog/PaShadow.v taken over that journal (TransportGRunA.v
   paj_run_x). The run's regions are the six world fields m_tick loads, each a read-only region of its harness global
   whose bytes are the world's (TWorldG.v tw_read_val); each loaded value is an atom of the walk's valuation mt_E:
     atom 33  M.state (M + 12, 4 bytes)       atom 34  M.wake_sent (M + 40, 8)    atom 35  g_now (8)
     atom 36  g_cfg.wake_timeout_ms (4)       atom 37  M.last_rx (M + 32, 8)      atom 38  g_cfg.offline_ms (4)
   The three branches the run cannot decide are split (DgnTransportPaLib.v paj_branch); each side is the model's test
   (mt_br_state_eq / mt_br_state_ne / mt_br_on / mt_br_wk):
     M.state = 2 (S_ONLINE):  u64 (g_now - last_rx) >= offline_ms * 1000: a0 = 4, tail jump to m_lost; else return;
     M.state <> 2, <> 1:      return;
     M.state = 1 (S_WAKING):  u64 (g_now - wake_sent) < wake_timeout_ms * 1000: return; else a0 = 6, tail jump.
   No instrumented check and no error path is on the code. A return closes with mt_close_ret: the model's world is Bw
   and every byte is the entry's. A tail jump enters m_lost with m_tick's ra, sp and callee-saved registers on the same
   journal: the statement's premise transport_m_lost_cg applies there, and its post gives m_tick's post (mt_tail_post:
   m_lost's written range mlost_wr Bw is mtick_wr Bw when the model's test holds). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg m_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the entry                                     *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the entry, 32 the shadow base (no shadow entry: m_tick has no instrumented check),
   33 .. 38 the six loaded fields. Regions: the loaded bytes of M (object 8), g_now (object 27),
   g_cfg.wake_timeout_ms (object 40) and g_cfg.offline_ms (object 41), each with no writable byte. *)
Definition mt_M : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 12 48 0 0
  [YP09.mkChunk 12 (YP09.CVal 4 (SOff 33 0)); YP09.mkChunk 32 (YP09.CVal 8 (SOff 37 0));
   YP09.mkChunk 40 (YP09.CVal 8 (SOff 34 0))].
Definition mt_now : YP09.region := YP09.mkRegion (Some (A_OBJ 27)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff 35 0))].
Definition mt_wto : YP09.region := YP09.mkRegion (Some (A_OBJ 40)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 36 0))].
Definition mt_off : YP09.region := YP09.mkRegion (Some (A_OBJ 41)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 38 0))].
Definition mt_regions : smem := [mt_M; mt_now; mt_wto; mt_off].
Definition mt_facts : facts :=
  mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (36%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (38%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_mt : sstate := mkSS AF_m_tick sr_atoms mt_regions None mt_facts.
Definition MT_SH : list shent := [].
Definition MT_Bx : sv := SOff 32 0.

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

(* The write rights of a run started at a state with mt_regions: no region has a writable byte. *)
Ltac mt_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

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

(* The online test (0x83c9c, bgeu a1, a0). *)
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

(* The waking test (0x83c70, bltu a1, a0). *)
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
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

Section mtw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma mt_vals_img : VAL (A_OBJ 8) = TA_M /\ VAL (A_OBJ 27) = TA_g_now /\ VAL (A_OBJ 40) = TA_g_cfg + 44 /\
  VAL (A_OBJ 41) = TA_g_cfg + 40 /\ BASE + AF_m_tick = transport_sigma TS_m_tick.
Proof. vm_compute. repeat split. Qed.

(* The walk's valuation: the 32 registers at the entry, the shadow base and the six loaded fields of Bw. *)
Definition mt_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transport) (Ereg regs (mt_vals Bw)).

Lemma mt_agree : forall regs Bw, env_agree 32 (Ereg regs (mt_vals Bw)) (mt_E regs Bw).
Proof. intros regs Bw. split; [intros n Hn; unfold mt_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* The entry state: the six regions hold the world's bytes. *)
Lemma mt_entry : forall (W : world segs) regs mem Bw,
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  st_ok_pi segs VAL (mt_E regs Bw) ss_mt
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_tick)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem Bw Htw.
  destruct mt_vals_img as (V8 & V27 & V40 & V41 & _).
  set (E := mt_E regs Bw).
  assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, mt_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (B8 : base_val E (Some (A_OBJ 8)) = TA_M)
    by (apply VB; [rewrite (EOB 8%nat ltac:(lia)), V8; reflexivity | unfold TA_M; lia]).
  assert (B27 : base_val E (Some (A_OBJ 27)) = TA_g_now)
    by (apply VB; [rewrite (EOB 27%nat ltac:(lia)), V27; reflexivity | unfold TA_g_now; lia]).
  assert (B40 : base_val E (Some (A_OBJ 40)) = TA_g_cfg + 44)
    by (apply VB; [rewrite (EOB 40%nat ltac:(lia)), V40; reflexivity | unfold TA_g_cfg; lia]).
  assert (B41 : base_val E (Some (A_OBJ 41)) = TA_g_cfg + 40)
    by (apply VB; [rewrite (EOB 41%nat ltac:(lia)), V41; reflexivity | unfold TA_g_cfg; lia]).
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
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold mt_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + unfold mt_M, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B8.
      split; [unfold TA_M; lia|]. split; [unfold TA_M; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val segs E _ TA_M 12 4 (SOff 33 0) (TW.u_at Bw TW.A_M_state 4));
          [apply DEN; [exact E33 | lia] | exact R33 | lia |].
        exact (tw_read_val segs _ TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 12 4 TMAP_A_ok Htw TMAP_A_M
          ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
      * apply (chunk_ok_val segs E _ TA_M 32 8 (SOff 37 0) (TW.M_last_rx Bw));
          [apply DEN; [exact E37 | exact R37] | exact R37 | lia |].
        exact (tw_read_val segs _ TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 32 8 TMAP_A_ok Htw TMAP_A_M
          ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
      * apply (chunk_ok_val segs E _ TA_M 40 8 (SOff 34 0) (TW.M_wake_sent Bw));
          [apply DEN; [exact E34 | exact R34] | exact R34 | lia |].
        exact (tw_read_val segs _ TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 40 8 TMAP_A_ok Htw TMAP_A_M
          ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    + unfold mt_now, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B27.
      split; [unfold TA_g_now; lia|]. split; [unfold TA_g_now; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TA_g_now 0 8 (SOff 35 0) (TW.g_now Bw));
        [apply DEN; [exact E35 | exact R35] | exact R35 | lia |].
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8 TMAP_A_ok Htw TMAP_A_g_now
        ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)).
    + unfold mt_wto, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B40.
      split; [unfold TA_g_cfg; lia|]. split; [unfold TA_g_cfg; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (TA_g_cfg + 44) 0 4 (SOff 36 0) (TW.Cfg_wake_timeout_ms Bw));
        [apply DEN; [exact E36 | lia] | exact R36 | lia |].
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg 44 4 TMAP_A_ok Htw TMAP_A_g_cfg
        ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
    + unfold mt_off, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B41.
      split; [unfold TA_g_cfg; lia|]. split; [unfold TA_g_cfg; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (TA_g_cfg + 40) 0 4 (SOff 38 0) (TW.Cfg_offline_ms Bw));
        [apply DEN; [exact E38 | lia] | exact R38 | lia |].
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg 40 4 TMAP_A_ok Htw TMAP_A_g_cfg
        ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
  - unfold mt_regions, mt_M, mt_now, mt_wto, mt_off.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B8, B27, B40, B41.
    unfold TA_M, TA_g_now, TA_g_cfg. repeat split; lia.
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

Lemma mt_tw_keep : forall (W : world segs) memc m Bw, mt_KA W memc m ->
  tw_at TMAP_A (aview segs (w_H W) memc) Bw -> tw_at TMAP_A (aview segs (w_H W) m) Bw.
Proof.
intros W memc m Bw [KA _] H. apply (tw_kept TMAP_A (aview segs (w_H W) memc)); [exact H|].
intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
apply KA. lia.
Qed.

(* The post at a return: nothing changed, the model's world is Bw. *)
Lemma mt_close_ret : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw regsF mF mdF,
  AR_laws segs B -> ameter_laws MT ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MTICK_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mF mdF k ->
  tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
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
  split; [unfold MTICK_EV, MLOST_EV; lia|].
  split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc mF
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

(* The post at a tail jump: m_lost's post, entered with m_tick's ra, sp and callee-saved registers on the same
   journal, is m_tick's. *)
Lemma mt_tail_post : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw Bw' memT regsT,
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - MTICK_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - MTICK_STK -> spZ regs <= 2 ^ 47 ->
  mt_KA W memc memT ->
  aregs_preserved regs regsT -> YK11.getr regsT 1 = YK11.getr regs 1 -> spZ regsT = spZ regs ->
  mtick_lost Bw = true ->
  forall W2 c2,
  transport_mlost_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT k regsT Bw Bw' W2 c2 ->
  transport_mtick_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' W2 c2.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' memT regsT
    LAWS HAR Hwin Hce H47 KAT HP R1 Hsp HL W2 c2 HQ.
  pose proof KAT as [KA GA].
  unfold transport_mlost_post, transport_cg_post in HQ.
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
    eapply dk_kept_trans_g with (W1 := W) (memX := memT) (slo' := spZ regs - MLOST_STK) (shi' := spZ regs)
      (Eo' := mlost_wr Bw).
    - exact Hce.
    - lia.
    - apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc memT
        (spZ regs - MTICK_STK) (spZ regs) (mtick_wr Bw) (fun _ => False) HAR).
      + apply dk_kept_refl_g. exact Hwin.
      + intros a Ha _. exact (KA a Ha).
      + exact GA.
      + intros a [].
      + intros b m i _ _ [].
      + intros a [].
      + intros cid pos a _ _ [].
    - exact HK.
    - unfold MTICK_STK. lia.
    - lia.
    - intros a Ha. unfold mtick_wr. split; [exact HL | exact Ha]. }
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

(* The walk. *)
Lemma mt_holds : @transport_m_tick_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_m_tick_cg_holds_stmt.
intros HCELLS LAWS MTL HGX HML.
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
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - MTICK_STK) by lia.
assert (Hwin : forall a, spZ regs - MTICK_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
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
pose proof (mt_entry W regs memc Bw Htw) as HS. fold E0 in HS.
assert (SHOK : sh_ok segs MT_Bx MT_SH E0 (mrestrict (w_H W) memc)) by (unfold sh_ok, MT_SH; apply Forall_nil).
assert (KA : mt_KA W memc memc) by (split; [intros; reflexivity | intros a Ha; exact Ha]).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_tick)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x00 .. +0x10: a0 = &M, a1 = M.state, `beq a1, 2`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ mt_awr. }
mt_after KA HS.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* M.state = S_ONLINE *)
  rewrite (mt_br_state_eq E0 Bw 2 E33 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. rename Hc into Hon.
  (* run 2, +0x48 .. +0x68: the silence test, `bgeu`. *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mt_awr. }
  mt_after KA HS.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + rewrite (mt_br_on E0 Bw E35 E37 E38) in Hc.
    destruct (mt_path_on_call Bw Hon Hc) as [HmE HL]. rewrite HmE in Hm. clear Hc.
    (* run 3, +0x70 .. +0x74: a0 = 4, the tail jump. *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mt_awr. }
    mt_after KA HS.
    (* the tail jump to m_lost with a0 = 4: m_lost's contract at the jump's state, then mt_tail_post *)
    pmkst HS.
    mt_reg HS (1%bv : bv 5) (YK11.getr regs 1) R1
      ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    mt_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) R2
      ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    mt_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
      ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
    mt_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
      ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
    mt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 4) R10 ltac:(reflexivity).
    assert (HPF : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (mt_vals Bw) HS);
          [exact (mt_agree regs Bw) | vm_compute; reflexivity]).
    assert (Hsp1 : spZ (ms_regs ms) = spZ regs) by exact (f_equal bv_unsigned R2).
    assert (Hsp16' : spZ (ms_regs ms) mod 16 = 0) by (rewrite Hsp1; exact Hsp16).
    assert (Hlo' : sp0 - STK <= spZ (ms_regs ms) - MLOST_STK) by (rewrite Hsp1; exact Hlo).
    assert (Hhi' : spZ (ms_regs ms) <= sp0) by (rewrite Hsp1; exact Hhi).
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_m_lost) rg mm mdx) Q) end.
    eapply SRr_mono.
    { exact (HML fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) _ k (ms_regs ms) 4 Bw Bw' HJ
        (eq_ind_r YK0s.ret_ok Hra R1) (eq_ind_r (fun w => 4096 <= bv_unsigned w) Hra4 R1) R3 R4 R10
        Hsp16' Hlo' Hhi' (mt_tw_keep W memc (ms_mem ms) Bw KA Htw) Hm ltac:(lia) Hev). }
    intros W2 c2 _ HQ.
    exact (mt_tail_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' (ms_mem ms) (ms_regs ms)
      LAWS HAR Hwin Hce ltac:(lia) KA HPF R1 Hsp1 HL W2 c2 HQ).
  + rewrite (mt_br_on E0 Bw E35 E37 E38) in Hc.
    rewrite (mt_path_on_ret Bw Hon Hc) in Hm. apply mt_some_inv in Hm. subst Bw'. clear Hc.
    (* run 3, +0x6c: `ret`. *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mt_awr. }
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
  { mt_awr. }
  mt_after KA HS.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + rewrite (mt_br_state_ne E0 Bw 1 E33 ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    rewrite (mt_path_idle Bw Hn2 Hc) in Hm. apply mt_some_inv in Hm. subst Bw'. clear Hc.
    (* run 3, +0x6c: `ret`. *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mt_awr. }
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
    { mt_awr. }
    mt_after KA HS.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * rewrite (mt_br_wk E0 Bw E34 E35 E36) in Hc.
      rewrite (mt_path_wk_ret Bw Hw1 Hc) in Hm. apply mt_some_inv in Hm. subst Bw'. clear Hc.
      (* run 4, +0x6c: `ret`. *)
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { mt_awr. }
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
      (* run 4, +0x40 .. +0x44: a0 = 6, the tail jump. *)
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { mt_awr. }
      mt_after KA HS.
      (* the tail jump to m_lost with a0 = 6: m_lost's contract at the jump's state, then mt_tail_post *)
      pmkst HS.
      mt_reg HS (1%bv : bv 5) (YK11.getr regs 1) R1
        ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
      mt_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) R2
        ltac:(cbn [sv_denot]; rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
      mt_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
        ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
      mt_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
        ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
      mt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 6) R10 ltac:(reflexivity).
      assert (HPF : aregs_preserved regs (ms_regs ms))
        by (apply (aregs_preserved_of_st_ok segs (w_H W) E0 _ ms regs (mt_vals Bw) HS);
            [exact (mt_agree regs Bw) | vm_compute; reflexivity]).
      assert (Hsp1 : spZ (ms_regs ms) = spZ regs) by exact (f_equal bv_unsigned R2).
      assert (Hsp16' : spZ (ms_regs ms) mod 16 = 0) by (rewrite Hsp1; exact Hsp16).
      assert (Hlo' : sp0 - STK <= spZ (ms_regs ms) - MLOST_STK) by (rewrite Hsp1; exact Hlo).
      assert (Hhi' : spZ (ms_regs ms) <= sp0) by (rewrite Hsp1; exact Hhi).
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_m_lost) rg mm mdx) Q) end.
      eapply SRr_mono.
      { exact (HML fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) _ k (ms_regs ms) 6 Bw Bw' HJ
          (eq_ind_r YK0s.ret_ok Hra R1) (eq_ind_r (fun w => 4096 <= bv_unsigned w) Hra4 R1) R3 R4 R10
          Hsp16' Hlo' Hhi' (mt_tw_keep W memc (ms_mem ms) Bw KA Htw) Hm ltac:(lia) Hev). }
      intros W2 c2 _ HQ.
      exact (mt_tail_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' (ms_mem ms) (ms_regs ms)
        LAWS HAR Hwin Hce ltac:(lia) KA HPF R1 Hsp1 HL W2 c2 HQ).
Qed.

End mtw.

(* The statement of lib/A/Prog/m_tick_cg.v. *)
Theorem transport_m_tick_cg_holds : forall fx rc B MT, @transport_m_tick_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@mt_holds fx rc B MT). Qed.
