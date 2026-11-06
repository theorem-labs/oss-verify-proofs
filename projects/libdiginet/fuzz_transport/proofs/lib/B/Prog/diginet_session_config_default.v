(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 902 of its 1078 lines of code are new or changed and 963 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SlostHead.v, with its module paths, module names and numbers changed; 542 of its 640 lines of code are new or changed and 980 lines of the source are left out. *)
(* diginet_session_config_default: Theorem transport_diginet_session_config_default_cg_holds : the statement
   transport_diginet_session_config_default_cg_holds_stmt of lib/B/Prog/diginet_session_config_default_cg.v, the
   machine walk of diginet_session_config_default on fuzz_transport.asan-ubsan at 0x865f4 (536 bytes, frame 32).

   The walk is a G-form walk: it holds the caller's journal ajournal_gx G_HARNESS_B 0 [] (lib/A/W_journalG.v) from the
   entry to the return, and the runs are the symbolic runs of lib/A/Prog/PaShadow.v taken over that journal
   (TransportGRunB.v paj_run_x). The stores into g_cfg are allowed by the run's write right awr_ok_x (a byte of G), the
   call of __asan_memset by TransportGCg.v gx_intrin_at.
     run 1 (0x865f4 .. 0x86624)  the frame, the three saves, `beqz a0` (decided: a0 = &g_cfg), s0 = a0, the shadow base
                                 through its GOT word into s1, a2 = 60, a0 = c, a1 = 0, the call of __asan_memset;
     __asan_memset (c, 0, 60)    gx_intrin_at: [c, c + 60) := 0; the destination is G, writable at every memory
                                 (TransportGRwB.v G_HARNESS_B_rw), its shadow is read from the record facts
                                 (trans_scfg_cells: range_addressable and the shadow hull);
     run 2 (0x86628 .. 0x86764)  the UBSan alignment check of c (decided: the fact of atom 10 is c exactly, 32-byte
                                 aligned, so `c & 3` is 0 and the trap word at 0x86768 is not reached), the 10 checked
                                 4-byte stores at c + 16, c + 24 .. c + 56 and the epilogue. Every shadow check is decided
                                 by the run's shadow entry [c, c + 60) (scfg_shok, from trans_scfg_cells): the nine
                                 loads at c + 16 .. c + 52 cover 8 addressable bytes and read 0; the one at c + 56 goes
                                 to the slow path, whose check needs 4 addressable bytes. So no error path
                                 (__asan_report_store4) is reached.
   The two regions of g_cfg that run 2 writes, [c + 16, c + 20) and [c + 24, c + 60), join the state after the memset
   (the memset changes their bytes, so they are not carried through the call); [c + 20, c + 24) (sum_mode) has no
   store and keeps the memset's 0.
   The post: transport_cg_post over G_HARNESS_B (scfg_close): the journal at the return, the callee-saved registers,
   acall_kept_g by TransportGCg.v dk_kept_step_g over the bytes the call may change (its stack window and g_cfg), and
   the world relation at the model's world: the model is upd Bw OFF_g_cfg CFG60 (scfg_model), and the 60 bytes are
   the memset's zeros at [0, 16) and [20, 24) and the 10 stores' values (scfg_cs_okb, decided on the run's last
   state). *)
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
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_config_default_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TWorldLemmas.
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

(* ------------------------------------------------------------------ *)
(* The symbolic state at the entry                                     *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the entry, 32 the shadow base. Regions at the entry: the 32-byte frame below sp
   (the three saves), the shadow base's GOT word (object 1) and its cell (object 95). Atom 10 (c) has the exact,
   32-byte aligned fact c = g_cfg. *)
Definition scfg_regions : smem := [stack_region SCFG_FRAME; got_regionP; bcell_regionP 32].
Definition scfg_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF SCFG_C SCFG_C 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)]
    [] [].
Definition ss_scfg : sstate := mkSS AF_diginet_session_config_default sr_atoms scfg_regions None scfg_facts.
(* The two regions of g_cfg's bytes that run 2 stores (writable: bytes of G), added after the memset. *)
Definition scfg_c_lo : YP09.region := YP09.mkRegion (Some 10%nat) 16 20 16 20 [].
Definition scfg_c_hi : YP09.region := YP09.mkRegion (Some 10%nat) 24 60 24 60 [].
(* The shadow entry of g_cfg's 60 bytes, and the shadow base of the token engine. *)
Definition SCFG_SH : list shent := [mkSHE 10 0 60].
Definition SCFG_Bx : sv := SOff 32 0.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac scfg_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "scfg_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac scfg_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The bytes of g_cfg's payload are bytes of G. *)
Lemma scfg_inG : forall a, SCFG_C <= a < SCFG_C + 60 -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TB_g_cfg, TW.SZ_g_cfg).
split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_cfg) | unfold in_zr, TW.SZ_g_cfg, SCFG_C in *; cbn [fst snd]; lia].
Qed.

(* The write rights of a run: the frame below sp (inside the caller's stack window), the two read-only image
   regions (no writable byte), and the regions of g_cfg (bytes of G). *)
Ltac scfg_awr UspE U10E :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia
            | rewrite UspE in Ha; left; split; [unfold awr_byte; left; lia | lia]
            | rewrite U10E in Ha; right; left; apply scfg_inG; lia ] |]);
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* The model's world and g_cfg's 60 bytes                              *)
(* ------------------------------------------------------------------ *)

(* g_cfg's 60 bytes after the call: the memset's zeros, then the 11 fields (TSess0.v:84-94). *)
Definition CFG60 : list byte :=
  TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd (TW.upd
    (TW.put 60 0) 16 (TW.put 4 1)) 20 (TW.put 4 0)) 24 (TW.put 4 10000)) 28 (TW.put 4 100)) 32 (TW.put 4 5))
    36 (TW.put 4 300)) 40 (TW.put 4 25000)) 44 (TW.put 4 3000)) 48 (TW.put 4 2000)) 52 (TW.put 4 48))
    56 (TW.put 4 314).
Lemma scfg_len60 : length CFG60 = 60%nat.
Proof. vm_compute. reflexivity. Qed.

(* A write inside a span written before is a write into that span's bytes. *)
Lemma scfg_upd_in : forall (bs v w : list byte) k j, 0 <= k -> 0 <= j ->
  j + Z.of_nat (length w) <= Z.of_nat (length v) -> k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  TW.upd (TW.upd bs k v) (k + j) w = TW.upd bs k (TW.upd v j w).
Proof.
intros bs v w k j Hk Hj Hw Hv. apply nth_error_ext. intros i.
assert (L1 : length (TW.upd bs k v) = length bs) by (apply TWL.length_upd; lia).
assert (L2 : length (TW.upd v j w) = length v) by (apply TWL.length_upd; lia).
rewrite (TWL.ne_upd (TW.upd bs k v) w (k + j) i) by (rewrite ?L1; lia).
rewrite (TWL.ne_upd bs (TW.upd v j w) k i) by (rewrite ?L2; lia).
rewrite (TWL.ne_upd bs v k i) by lia.
rewrite (TWL.ne_upd v w j (i - Z.to_nat k)) by lia.
rewrite L2.
repeat match goal with |- context [Nat.leb ?a ?b] => destruct (Nat.leb_spec a b) end;
repeat match goal with |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b) end;
cbn [andb]; try (exfalso; lia); try reflexivity; f_equal; lia.
Qed.

Lemma scfg_some_inv : forall x y : list byte, Some (x, tt) = Some (y, tt) -> y = x.
Proof. intros x y H. injection H as H. symmetry. exact H. Qed.

Ltac scfg_side HL :=
  first [ unfold TW.OFF_g_cfg; lia | lia
        | rewrite HL; apply Z.leb_le; vm_compute; reflexivity
        | apply Z.leb_le; vm_compute; reflexivity ].

(* The model's world after the call: g_cfg's 60 bytes are CFG60, every other byte is Bw's. *)
Lemma scfg_model : forall Bw Bw', length Bw = Z.to_nat TW.W_LEN ->
  TS0.diginet_session_config_default_m Bw = Some (Bw', tt) -> Bw' = TW.upd Bw TW.OFF_g_cfg CFG60.
Proof.
intros Bw Bw' HL Hm.
assert (E : TS0.diginet_session_config_default_m Bw = Some (TW.upd Bw TW.OFF_g_cfg CFG60, tt)).
{ unfold TS0.diginet_session_config_default_m, TW.set_Cfg_auto_wake, TW.set_Cfg_sum_mode, TW.set_Cfg_keepalive_ms,
    TW.set_Cfg_ack_timeout_ms, TW.set_Cfg_max_retries, TW.set_Cfg_backoff_ms, TW.set_Cfg_offline_ms,
    TW.set_Cfg_wake_timeout_ms, TW.set_Cfg_display_gap_us, TW.set_Cfg_max_cmds, TW.set_Cfg_max_body,
    TW.A_Cfg_auto_wake, TW.A_Cfg_sum_mode, TW.A_Cfg_keepalive_ms, TW.A_Cfg_ack_timeout_ms, TW.A_Cfg_max_retries,
    TW.A_Cfg_backoff_ms, TW.A_Cfg_offline_ms, TW.A_Cfg_wake_timeout_ms, TW.A_Cfg_display_gap_us,
    TW.A_Cfg_max_cmds, TW.A_Cfg_max_body, TS0.DIGINET_SUM_BODY.
  cbv zeta.
  change (Z.to_nat TW.SZ_g_cfg) with 60%nat.
  rewrite (scfg_upd_in _ _ _ TW.OFF_g_cfg 16) by scfg_side HL.
  rewrite (scfg_upd_in _ _ _ TW.OFF_g_cfg 20) by scfg_side HL.
  rewrite (scfg_upd_in _ _ _ TW.OFF_g_cfg 24) by scfg_side HL.
  rewrite (scfg_upd_in _ _ _ TW.OFF_g_cfg 28) by scfg_side HL.
  rewrite (scfg_upd_in _ _ _ TW.OFF_g_cfg 32) by scfg_side HL.
  rewrite (scfg_upd_in _ _ _ TW.OFF_g_cfg 36) by scfg_side HL.
  rewrite (scfg_upd_in _ _ _ TW.OFF_g_cfg 40) by scfg_side HL.
  rewrite (scfg_upd_in _ _ _ TW.OFF_g_cfg 44) by scfg_side HL.
  rewrite (scfg_upd_in _ _ _ TW.OFF_g_cfg 48) by scfg_side HL.
  rewrite (scfg_upd_in _ _ _ TW.OFF_g_cfg 52) by scfg_side HL.
  rewrite (scfg_upd_in _ _ _ TW.OFF_g_cfg 56) by scfg_side HL.
  reflexivity. }
rewrite E in Hm. exact (scfg_some_inv _ _ Hm).
Qed.

(* The literal 4-byte chunks of a region (what the run's stores leave), read byte by byte. *)
Definition scfg_cv_lit (cv : YP09.cval) : option (N * Z) :=
  match cv with YP09.CVal w (SLit z) => Some (w, z) | _ => None end.
Fixpoint scfg_cs_val (cs : list YP09.chunk) (x : Z) : option Z :=
  match cs with
  | [] => None
  | c :: cs' =>
      match scfg_cv_lit (YP09.c_val c) with
      | Some (w, z) =>
          if ((YP09.c_off c <=? x) && (x <? YP09.c_off c + Z.of_N w))%bool
          then Some (bv_unsigned (YP09.byte_of_word (Z_to_bv 64 z) (x - YP09.c_off c)))
          else scfg_cs_val cs' x
      | None => scfg_cs_val cs' x
      end
  end.
Lemma scfg_cv_lit_spec : forall cv w z, scfg_cv_lit cv = Some (w, z) -> cv = YP09.CVal w (SLit z).
Proof.
intros cv w z H. destruct cv as [w' v' | ? | ? | ? ? ?]; try discriminate H.
destruct v'; try discriminate H. cbn in H. injection H as H1 H2. subst. reflexivity.
Qed.

(* The bytes of g_cfg run 2 does not store: [0, 16) and sum_mode's [20, 24). *)
Definition scfg_zb (j : nat) : bool := ((j <? 16) || ((20 <=? j) && (j <? 24)))%nat.
Lemma scfg_zb_spec : forall j, scfg_zb j = true -> (j < 16 \/ 20 <= j < 24)%nat.
Proof.
intros j H. unfold scfg_zb in H. apply orb_true_iff in H. destruct H as [H | H].
- left. apply Nat.ltb_lt. exact H.
- right. apply andb_true_iff in H as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. lia.
Qed.

(* g_cfg's 60 bytes, decided against a run's chunk list: the bytes scfg_zb names are CFG60's zeros, the others the
   chunks' bytes. *)
Definition scfg_cs_okb (cs : list YP09.chunk) : bool :=
  forallb (fun j : nat => if scfg_zb j then Z.eqb (bv_unsigned (nth j CFG60 (Z_to_bv 8 0))) 0
    else match scfg_cs_val cs (Z.of_nat j) with
         | Some v => Z.eqb v (bv_unsigned (nth j CFG60 (Z_to_bv 8 0)))
         | None => false end)
  (seq 0 60).
Lemma scfg_cs_okb_spec : forall cs, scfg_cs_okb cs = true -> forall j, (j < 60)%nat ->
  (scfg_zb j = true /\ bv_unsigned (nth j CFG60 (Z_to_bv 8 0)) = 0) \/
  (scfg_zb j = false /\ scfg_cs_val cs (Z.of_nat j) = Some (bv_unsigned (nth j CFG60 (Z_to_bv 8 0)))).
Proof.
intros cs H j Hj. unfold scfg_cs_okb in H. rewrite forallb_forall in H.
specialize (H j ltac:(apply in_seq; lia)). revert H.
destruct (scfg_zb j) eqn:Hz; intros H.
- left. split; [reflexivity | apply Z.eqb_eq; exact H].
- right. split; [reflexivity|]. destruct (scfg_cs_val cs (Z.of_nat j)) as [v|]; [|discriminate H].
  apply Z.eqb_eq in H. rewrite H. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

Section scfgw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma scfg_cs_ok : forall E m b cs x v,
  Forall (YP09.chunk_ok segs E m b) cs -> scfg_cs_val cs x = Some v ->
  option_map (fun bt : byte => bv_unsigned bt) (YP09.mbyte segs m (b + x)) = Some v.
Proof.
intros E m b cs. induction cs as [|c cs IH]; intros x v HF Hv; [discriminate Hv|].
apply Forall_cons_iff in HF as [Hc HF]. cbn [scfg_cs_val] in Hv.
destruct (scfg_cv_lit (YP09.c_val c)) as [[w z]|] eqn:Hl; [|exact (IH x v HF Hv)].
destruct ((YP09.c_off c <=? x) && (x <? YP09.c_off c + Z.of_N w))%bool eqn:Hr; [|exact (IH x v HF Hv)].
injection Hv as <-. apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (scfg_cv_lit_spec _ _ _ Hl) as Ec.
assert (Hi : 0 <= x - YP09.c_off c < YP09.c_len c) by (unfold YP09.c_len; rewrite Ec; cbn [YP09.cv_len]; lia).
destruct (Hc (x - YP09.c_off c) Hi) as (bt & Hb & Hmb).
rewrite Ec in Hb. cbn [YP09.cbyte sv_denot] in Hb. injection Hb as <-.
replace (b + x) with (b + YP09.c_off c + (x - YP09.c_off c)) by lia. rewrite Hmb. reflexivity.
Qed.

Lemma scfg_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  BASE + AF_diginet_session_config_default = transportb_sigma TB_diginet_session_config_default.
Proof. vm_compute. repeat split. Qed.

(* The two image regions hold what transport_cells says they hold, at any AR state. *)
Lemma scfg_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H W) mem) got_regionP /\ region_ok segs E (mrestrict (w_H W) mem) (bcell_regionP 32).
Proof.
  intros ly S W mem md E HCELLS HAR E1 E95 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct scfg_vals as (V1 & V95 & _).
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

(* g_cfg's 60 bytes are addressable at every AR state: the shadow of its 7 whole granules is 0 (a range of
   as_zero_shadow B), the shadow of its last granule is 4 (a constant cell of the record). *)
Lemma scfg_ra : forall ly S (W : world segs) mem md,
  trans_scfg_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF SCFG_C 60.
Proof.
intros ly S W mem md [HZ HC] HAR x Hx.
assert (EC : SCFG_C = 6155520) by reflexivity.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold shadow_of_addr.
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
  replace ((SCFG_C + 56) / 8) with 769447 by (rewrite EC; reflexivity). rewrite EC in *. lia.
Qed.

(* The shadow hull of the memset's destination [c, c + 60) is visible: its 8 shadow bytes are g_cfg's. *)
Lemma scfg_hull : forall ly S (W : world segs) mem md,
  trans_scfg_cells B -> @AR rc segs B ly S W mem md ->
  shadow_hull_vis (aview segs (w_H W) mem) SCFG_C 60.
Proof.
intros ly S W mem md HSC HAR s Hs.
pose proof (scfg_ra ly S W mem md HSC HAR) as HRA.
assert (EC : SCFG_C = 6155520) by reflexivity.
assert (B1 : shadow_addr SCFG_C / 8 * 8 = 2148220320) by reflexivity.
assert (B2 : shadow_addr (SCFG_C + 60 - 1) / 8 * 8 + 8 = 2148220328) by reflexivity.
rewrite B1, B2 in Hs.
assert (Hx : SCFG_C <= SCFG_C + 8 * (s - 2148220320) < SCFG_C + 60) by (rewrite EC; lia).
destruct (HRA _ Hx) as (v & Hv & _).
unfold shadow_of_addr in Hv. rewrite EC in Hv.
replace (SHADOW_OFF + (6155520 + 8 * (s - 2148220320)) / 8) with s in Hv.
- rewrite Hv. discriminate.
- unfold SHADOW_OFF.
  replace (6155520 + 8 * (s - 2148220320)) with ((769440 + (s - 2148220320)) * 8) by lia.
  rewrite Z.div_mul by lia. lia.
Qed.

(* The run's shadow entry holds at every AR state. *)
Lemma scfg_shok : forall ly S (W : world segs) mem md (E : env),
  trans_scfg_cells B -> @AR rc segs B ly S W mem md ->
  ew E 10 = Z_to_bv 64 SCFG_C -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs SCFG_Bx SCFG_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E HSC HAR E10 E32.
assert (EC : SCFG_C = 6155520) by reflexivity.
unfold sh_ok, SCFG_SH. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H W) mem E SCFG_Bx 10 SCFG_C 60 SCFG_C 0 60 (scfg_ra ly S W mem md HSC HAR)).
- unfold U, SCFG_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* A region of g_cfg's bytes [c + lo, c + hi), all writable (bytes of G), with no chunk, at any memory. *)
Lemma scfg_wr_ok : forall E (m : word -> option byte) lo hi, bv_unsigned (ew E 10) = SCFG_C -> 0 <= lo -> hi <= 60 ->
  region_ok segs E m (YP09.mkRegion (Some 10%nat) lo hi lo hi []).
Proof.
intros E m lo hi HU H0 H1. assert (EC : SCFG_C = 6155520) by reflexivity.
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HU. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (SCFG_C + o) G_HARNESS_B_rw). apply scfg_inG. lia.
Qed.

(* The walk's valuation: the 32 registers at the entry and the shadow base. *)
Definition scfg_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).

(* The entry state, and the shadow entry of g_cfg. *)
Lemma scfg_entry : forall ly S (W : world segs) regs mem md,
  transport_cells B -> trans_scfg_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - SCFG_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  YK11.getr regs 10 = w64 SCFG_C ->
  st_ok_pi segs VAL (scfg_E regs) ss_scfg
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_config_default)) mem
      (YK11.seg_rom segs)))
  /\ sh_ok segs SCFG_Bx SCFG_SH (scfg_E regs) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md HCELLS HSC HAR Hpres Hsp Hsp16 H10.
  assert (EC : SCFG_C = 6155520) by reflexivity.
  assert (E2 : ew (scfg_E regs) 2 = YK11.getr regs 2) by (unfold scfg_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew (scfg_E regs) 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (E10 : ew (scfg_E regs) 10 = Z_to_bv 64 SCFG_C)
    by (unfold scfg_E; rewrite (ew_Eimg_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (U10 : bv_unsigned (ew (scfg_E regs) 10) = SCFG_C) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (E32 : ew (scfg_E regs) 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold scfg_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (EOB : forall j, (j < 97)%nat -> ew (scfg_E regs) (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold scfg_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct (scfg_img_ok ly S W mem md (scfg_E regs) HCELLS HAR (EOB 1%nat ltac:(lia)) (EOB 95%nat ltac:(lia)) E32)
    as [RG RC].
  destruct scfg_vals as (V1 & V95 & _).
  assert (VB : forall n v0, ew (scfg_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (scfg_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  split.
  - rewrite restrict_mkst_fx. unfold ss_scfg, scfg_regions.
    apply (pa_entry_st_ok_full (PI := PI_transportb)).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [exact RG | apply Forall_cons; [exact RC | apply Forall_nil]]].
      unfold stack_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. unfold SCFG_FRAME in *.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
    + apply pairwise_disjoint_of_extents.
      unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (EOB 95%nat ltac:(lia))) by (rewrite V95; unfold FCells.CELL_K; lia).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      rewrite V1, V95. unfold FCells.GOT_CELL_K, FCells.CELL_K, SCFG_FRAME in *.
      repeat split; first [exact I | lia].
    + unfold scfg_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U10, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite EC; reflexivity].
  - exact (scfg_shok ly S W mem md (scfg_E regs) HSC HAR E10 E32).
Qed.

(* What the walk keeps, from its entry memory memc to a memory m: the view outside the call's stack window and g_cfg's
   60 bytes is the entry's (KA); presence grows (GA). *)
Definition scfg_KA (W : world segs) (memc m : word -> option byte) (sp : Z) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp - SCFG_STK <= a < sp) -> ~ (SCFG_C <= a < SCFG_C + 60) ->
    aview segs (w_H W) m a = aview segs (w_H W) memc a.
Definition scfg_GA (W : world segs) (memc m : word -> option byte) : Prop :=
  forall a, apresent (w_H W) memc a -> apresent (w_H W) m a.

(* The walk's valuation agrees with the entry registers below atom 32. *)
Lemma scfg_agree : forall regs E, (forall n, (n < 32)%nat -> ew E n = ew (scfg_E regs) n) -> ed E = ed (scfg_E regs) ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF]) E.
Proof.
  intros regs E H1 H2. split.
  - intros n Hn. rewrite (H1 n Hn). unfold scfg_E. apply Eimg_low. unfold A_TEXT. lia.
  - rewrite H2. reflexivity.
Qed.

(* A payload byte of the world table is a byte of G. *)
Lemma scfg_tw_in_G : forall x, tw_in TMAP_B x -> inG TG.G_HARNESS_B x.
Proof.
intros x (o & b & n & Hin & Hx). unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The post at the return, from the walk's last facts. *)
Lemma scfg_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw Bw' regsF mF mdF,
  AR_laws segs B -> ameter_laws MT -> gx_ok segs B TG.G_HARNESS_B ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - SCFG_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - SCFG_STK -> spZ regs <= 2 ^ 47 ->
  YK0s.ret_ok (YK11.getr regs 1) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mF mdF k ->
  tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
  TS0.diginet_session_config_default_m Bw = Some (Bw', tt) ->
  scfg_KA W memc mF (spZ regs) -> scfg_GA W memc mF ->
  (forall i, 0 <= i < 60 ->
     aview segs (w_H W) mF (SCFG_C + i) = Some (bv_unsigned (nth (Z.to_nat i) CFG60 (Z_to_bv 8 0)))) ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 ->
  forall mat, @transport_scfg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw' W
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' regsF mF mdF
    LAWS MTL HGX HAR Hwin Hce Hsp47 Hra HJF Htw Hm KA GA HV60 HP RF1 mat.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : SCFG_STK = 4128) by reflexivity.
  assert (EC : SCFG_C = 6155520) by reflexivity.
  assert (GLOW : forall a, inG TG.G_HARNESS_B a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (transportb_segs_low a (proj1 (HGX a Ha)))).
  unfold transport_scfg_post, transport_cg_post.
  exists lyc, Sc, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
  split.
  { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [unfold SCFG_EV; lia|].
  split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc mF
      (spZ regs - SCFG_STK) (spZ regs) scfg_wr (fun a => (spZ regs - SCFG_STK <= a < spZ regs) \/ scfg_wr a) HAR).
    - apply dk_kept_refl_g. exact Hwin.
    - intros a Ha Hn. apply KA; [exact Ha | intros H; apply Hn; left; exact H
        | intros H; apply Hn; right; unfold scfg_wr, TW.SZ_g_cfg; lia].
    - exact GA.
    - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso. unfold scfg_wr, TW.SZ_g_cfg in Hw. lia.
    - intros b m i Hb Hi [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
    - intros a [Hw | Hw] Hi HnG _ _.
      + pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
      + apply HnG. apply scfg_inG. unfold scfg_wr, TW.SZ_g_cfg in Hw. lia.
    - intros cid pos a Hin Hr [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  (* the world relation at the model's world *)
  rewrite (scfg_model Bw Bw' (tw_len _ _ _ Htw) Hm).
  replace (TW.upd Bw TW.OFF_g_cfg CFG60) with (TW.upd Bw (TW.OFF_g_cfg + 0) CFG60) by (rewrite Z.add_0_r; reflexivity).
  apply (tw_upd TMAP_B (aview segs (w_H W) memc) (aview segs (w_H W) mF) Bw TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 0 CFG60
    TMAP_B_ok Htw TMAP_B_g_cfg).
  - lia.
  - rewrite scfg_len60. unfold TW.SZ_g_cfg. lia.
  - intros j Hj. rewrite scfg_len60 in Hj. specialize (HV60 (Z.of_nat j) ltac:(lia)).
    rewrite Nat2Z.id in HV60. rewrite Z.add_0_r. exact HV60.
  - intros x Hx Hn. rewrite scfg_len60 in Hn. pose proof (GLOW x (scfg_tw_in_G x Hx)) as Hl.
    unfold kLowMemEnd in Hl. unfold TB_g_cfg in Hn.
    apply KA; [lia | lia | lia].
Qed.

(* A region of g_cfg added to the state after the memset lies apart from the state's regions: the frame below sp,
   the two cells of the image, and the other region of g_cfg. *)
Ltac scfg_disj UspE UGE UCE U10E :=
  unfold scfg_c_lo, scfg_c_hi; cbn [ss_mem YP09.all_disjoint]; unfold YP09.extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite ?UspE, ?UGE, ?UCE, ?U10E; unfold FCells.GOT_CELL_K, FCells.CELL_K, SCFG_C, TB_g_cfg;
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.

(* The walk. *)
Lemma scfg_holds : @transport_diginet_session_config_default_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_diginet_session_config_default_cg_holds_stmt.
intros HCELLS HSC LAWS MTL HGX HAI0.
unfold transport_diginet_session_config_default_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw'
  HJ Hra Hra4 Hgp Htp H10 Hsp16 Hlo Hhi Htw Hm Hev.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : SCFG_STK = 4128) by reflexivity.
assert (FF : SCFG_FRAME = 32) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (EC : SCFG_C = 6155520) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - SCFG_STK) by lia.
assert (Hm16 : (spZ regs - 32 - sp0) mod 16 = 0).
{ replace (spZ regs - 32 - sp0) with (spZ regs - sp0 + (-2) * 16) by lia.
  rewrite Z_mod_plus_full, Zminus_mod, Hsp16, Hsp0a. reflexivity. }
assert (Hwin : forall a, spZ regs - SCFG_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
(* The valuation of the walk and its atoms. *)
set (E0 := scfg_E regs).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, scfg_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros n r Hn; unfold E0, scfg_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E10 : ew E0 10 = Z_to_bv 64 SCFG_C) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (U10 : bv_unsigned (ew E0 10) = SCFG_C) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E0, scfg_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
destruct (scfg_entry lyc Sc W regs memc mdc HCELLS HSC HAR ltac:(intros a Ha; apply Hpres0; lia) Hsp Hsp16 H10)
  as [HS SHOK].
fold E0 in HS, SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_config_default)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x00 .. +0x30: the frame, the three saves, `beqz a0` (a0 = c), s0 = c, the shadow base into s1, the
   arguments, `jal __asan_memset`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ scfg_awr Usp U10. }
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 32 <= x < spZ regs) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta.
  scfg_win Hin Hx ltac:(rewrite ?Usp in Hx; lia). }
assert (KA1 : scfg_KA W memc (ms_mem ms) (spZ regs))
  by (intros a Ha H1 H2; apply KR1; [exact Ha | lia]).
assert (GA1 : scfg_GA W memc (ms_mem ms)) by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
pmkst HS.
scfg_reg HS (Z_to_bv 5 10) (Z_to_bv 64 SCFG_C) Q10 ltac:(cbn [sv_denot]; rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
scfg_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
scfg_reg HS (Z_to_bv 5 12) (Z_to_bv 64 60) Q12 ltac:(reflexivity).
scfg_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 32)) Q2 ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
scfg_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 21384)) R1 ltac:(apply codeptr_val; exact HEI).
scfg_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
scfg_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = spZ regs - 32)
  by (rewrite Q2; apply unsigned_lit_small; lia).
assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 32) by exact ESP.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
(* +0x30: __asan_memset (c, 0, 60), through the G call kit. *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OSet (transportb_sigma TB___asan_memset)
    (HAI0 fx) TG.G_HARNESS_B W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc md1 k
    SCFG_C 0 60 (spZ regs - 32 - sp0) (Z_to_bv 64 (BASE + 21384)) HGX G_HARNESS_B_rw HJ Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite Hsp1. lia.
  - exact Hm16.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right. apply scfg_inG. lia.
  - left. unfold kLowMemEnd. lia.
  - exact (scfg_ra _ _ _ _ _ HSC HAR1).
  - intros _. exact (scfg_hull _ _ _ _ _ HSC HAR1).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset2 & Heff2 & Hgr2).
assert (KA2 : scfg_KA W memc mem2 (spZ regs)).
{ intros a Ha H1 H2. rewrite (Heff2 a Ha ltac:(lia) ltac:(lia)). exact (KA1 a Ha H1 H2). }
assert (KZ2 : forall a, SCFG_C <= a < SCFG_C + 60 -> aview segs (w_H W) mem2 a = Some 0).
{ intros a Ha. replace a with (SCFG_C + (a - SCFG_C)) by lia. rewrite (Hset2 (a - SCFG_C) ltac:(lia)). reflexivity. }
assert (GA2 : scfg_GA W memc mem2) by (intros a Ha; apply Hgr2, GA1, Ha).
(* the three regions of the state, kept by the call *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat] HS2.
destruct scfg_vals as (V1 & V95 & _).
assert (UG : bv_unsigned (ew E0 (A_OBJ 1)) = FCells.GOT_CELL_K).
{ unfold E0, scfg_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V1.
  apply unsigned_lit_small. unfold FCells.GOT_CELL_K. lia. }
assert (UC : bv_unsigned (ew E0 (A_OBJ 95)) = FCells.CELL_K).
{ unfold E0, scfg_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V95.
  apply unsigned_lit_small. unfold FCells.CELL_K. lia. }
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (SCFG_C <= a < SCFG_C + 60) -> ~ (spZ regs - 32 - ESTACK <= a < spZ regs - 32) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem ms) a)
  by (intros a Ha H1 H2; apply Heff2; [exact Ha | exact H1 | lia]).
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview _ _ _ _ 2%nat (spZ regs)); [exact Usp | | exact Hgr2].
    intros a Ha. apply KM; lia.
  - apply (region_kept_aview _ _ _ _ (A_OBJ 1) FCells.GOT_CELL_K); [exact UG | | exact Hgr2].
    intros a Ha. unfold FCells.GOT_CELL_K in Ha. apply KM; lia.
  - apply (region_kept_aview _ _ _ _ (A_OBJ 95) FCells.CELL_K); [exact UC | | exact Hgr2].
    intros a Ha. unfold FCells.CELL_K in Ha. apply KM; lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E0 1024 (map (YK11.getr regs2) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite E1lo by lia; exact Usp).
assert (U10_1 : bv_unsigned (ew E1 10) = SCFG_C) by (rewrite E1lo by lia; exact U10).
assert (UG1 : bv_unsigned (ew E1 242%nat) = FCells.GOT_CELL_K) by (rewrite E1lo by lia; exact UG).
assert (UC1 : bv_unsigned (ew E1 336%nat) = FCells.CELL_K) by (rewrite E1lo by lia; exact UC).
(* g_cfg's two regions that run 2 stores join the state *)
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
  let HS1 := fresh "HS1" in
  pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) scfg_c_hi HS eq_refl
    (scfg_wr_ok Ex _ 24 60 U10_1 ltac:(lia) ltac:(lia))
    ltac:(scfg_disj Usp1 UG1 UC1 U10_1)) as HS1;
  clear HS; rename HS1 into HS end.
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
  let HS1 := fresh "HS1" in
  pose proof (st_ok_pi_add_region Ex ss (restrict Hh m) scfg_c_lo HS eq_refl
    (scfg_wr_ok Ex _ 16 20 U10_1 ltac:(lia) ltac:(lia))
    ltac:(scfg_disj Usp1 UG1 UC1 U10_1)) as HS1;
  clear HS; rename HS1 into HS end.
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
  let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (SHOK1 : sh_ok segs SCFG_Bx SCFG_SH E1 (mrestrict (w_H W) mem2)).
{ apply (scfg_shok _ _ _ _ _ E1 HSC HAR2); rewrite E1lo by lia; [exact E10 | exact E32]. }
clear dependent ms.
(* run 2, +0x34 .. +0x170: the alignment check of c, the 10 checked stores into g_cfg, the reloads and `ret`. *)
paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
{ scfg_awr Usp1 U10_1. }
set (mdF := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdF. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?m) => rename m into msF; set (EX := EF) in HS end.
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> ~ (SCFG_C + 16 <= a < SCFG_C + 20) ->
  ~ (SCFG_C + 24 <= a < SCFG_C + 60) -> aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) mem2 a).
{ intros a Ha H1 H2 H3.
  apply (kept_of_frame _ _ _ _ _ (fun x => (spZ regs - 32 <= x < spZ regs) \/ (SCFG_C + 16 <= x < SCFG_C + 20) \/
    (SCFG_C + 24 <= x < SCFG_C + 60)) HFr);
    [| exact Ha | intros [Hx|[Hx|Hx]]; [exact (H1 Hx) | exact (H2 Hx) | exact (H3 Hx)]].
  intros b wlo whi x Hin Hx. cbv beta.
  scfg_win Hin Hx ltac:(rewrite ?Usp1, ?U10_1 in Hx; first [lia | left; lia | right; left; lia | right; right; lia]). }
assert (KAF : scfg_KA W memc (ms_mem msF) (spZ regs))
  by (intros a Ha H1 H2; rewrite KR3 by (exact Ha || lia); exact (KA2 a Ha H1 H2)).
assert (KZF : forall a, (SCFG_C <= a < SCFG_C + 16) \/ (SCFG_C + 20 <= a < SCFG_C + 24) ->
  aview segs (w_H W) (ms_mem msF) a = Some 0)
  by (intros a Ha; rewrite KR3 by lia; apply KZ2; lia).
assert (GAF : scfg_GA W memc (ms_mem msF)) by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
clear HF HFr HG.
assert (HEF : forall n, (n < 1024)%nat -> ew EX n = ew E0 n).
{ intros n Hn. unfold EX. repeat rewrite ew_ewset_other by lia. apply E1lo. exact Hn. }
assert (U10F : bv_unsigned (ew EX 10) = SCFG_C) by (rewrite HEF by lia; exact U10).
(* g_cfg's 60 bytes at the return: the two regions' chunks and the memset's zeros *)
pose proof (st_ok_pi_region_nth EX _ (restrict (w_H W) msF) 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
pose proof (st_ok_pi_region_nth EX _ (restrict (w_H W) msF) 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
lazymatch type of RG0 with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs0) =>
lazymatch type of RG1 with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs1) =>
  assert (HOKB : scfg_cs_okb (cs0 ++ cs1) = true) by (vm_compute; reflexivity) end end.
destruct RG0 as (_ & _ & _ & HCH0). destruct RG1 as (_ & _ & _ & HCH1).
cbn [YP09.r_base YP09.r_chunks base_val] in HCH0, HCH1.
pose proof (proj2 (Forall_app _ _ _) (conj HCH0 HCH1)) as HCH. clear HCH0 HCH1.
assert (HV60 : forall i, 0 <= i < 60 ->
  aview segs (w_H W) (ms_mem msF) (SCFG_C + i) = Some (bv_unsigned (nth (Z.to_nat i) CFG60 (Z_to_bv 8 0)))).
{ intros i Hi. destruct (scfg_cs_okb_spec _ HOKB (Z.to_nat i) ltac:(lia)) as [[Hl Hz] | [Hl Hc]].
  - rewrite Hz. apply KZF. pose proof (scfg_zb_spec _ Hl) as Hzl. lia.
  - rewrite Z2Nat.id in Hc by lia.
    pose proof (scfg_cs_ok _ _ _ _ _ _ HCH Hc) as Hb.
    rewrite U10F in Hb. exact Hb. }
scfg_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
  ltac:(cbn [sv_denot]; rewrite HEF by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HPF : aregs_preserved regs (ms_regs msF)).
{ apply (aregs_preserved_of_st_ok segs (w_H W) EX _ msF regs [w64 SHADOW_OFF] HS).
  - apply scfg_agree; [intros n Hn; rewrite HEF by lia; reflexivity | reflexivity].
  - vm_compute. reflexivity. }
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
exact (scfg_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw Bw' (ms_regs msF) (ms_mem msF) mdF
  LAWS MTL HGX HAR Hwin Hce ltac:(lia) Hra HJ2 Htw Hm KAF GAF HV60 HPF RF1 mat').
Qed.

End scfgw.

(* The statement of lib/B/Prog/diginet_session_config_default_cg.v. *)
Theorem transport_diginet_session_config_default_cg_holds :
  forall fx rc B MT, @transport_diginet_session_config_default_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@scfg_holds fx rc B MT). Qed.
