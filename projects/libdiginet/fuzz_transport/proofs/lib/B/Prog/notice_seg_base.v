(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 678 of its 962 lines of code are new or changed and 855 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcHead.v, with its module paths, module names and numbers changed; 528 of its 590 lines of code are new or changed and 900 lines of the source are left out. *)
(* notice_seg_base: the shared part of the walk of notice on fuzz_transport.asan-ubsan (lib/B/Prog/notice_cgW.v):
   the symbolic states, regions and atoms of the walk, the model's paths of notice_m, the notice the callees get, and
   the steps that change a symbolic state between runs (a register set to an equal value, regions dropped or
   added). The image-B twin of lib/A/Prog/notice_seg_base.v: image B's offsets, objects and auipc values. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg check_state_desk_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  check_inflight_lost_cg check_inflight_acked_cg check_state_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
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
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module LIL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_lost_cg.
Module LIA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_acked_cg.
Module LSO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_online_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* Offsets, atoms, regions                                             *)
(* ------------------------------------------------------------------ *)

(* Listing offsets (from the listing base 0x812a0): the kind load, the bltu, the jump `jr a0`, the six kind
   arms, the epilogue, and the UBSan trap word (`unimp`, 0x83610). *)
Definition NT_KLOAD : Z := AF_notice + 0x30.
Definition NT_BLTU : Z := AF_notice + 0x3c.
Definition NT_JR : Z := AF_notice + 0x58.
Definition NT_DESK : Z := AF_notice + 0x5c.
Definition NT_LOST : Z := AF_notice + 0x80.
Definition NT_DATA : Z := AF_notice + 0x94.
Definition NT_ACKED : Z := AF_notice + 0xb4.
Definition NT_STATE : Z := AF_notice + 0xd8.
Definition NT_FOREIGN : Z := AF_notice + 0x1d4.
Definition NT_EPI : Z := AF_notice + 0x1e8.
Definition NT_TRAP : Z := AF_notice + 0x1f4.
(* The table's six entries (added to the table's address 0x20f7c): the six arms. *)
Definition NT_TBL : list Z := [0x624fc; 0x62578; 0x62534; 0x62554; 0x62520; 0x62674].

(* Atoms: 0 .. 31 the entry registers, 32 the shadow base, 33 .. 36 the notice's kind, state, old and reason (u32
   at p, p + 4, p + 8, p + 12), 37 .. 41 GOT.n, GOT.desk, GOT.ndata, GOT.acked, GOT.foreign (u32 of the world),
   42 the address GOT + 12 * GOT.n (the record GOT.t[GOT.n] is at + 4 .. + 16). *)
Definition nt_vals (NB Bw : list byte) : list word :=
  [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at NB 0 4); Z_to_bv 64 (TW.u_at NB 4 4); Z_to_bv 64 (TW.u_at NB 8 4);
   Z_to_bv 64 (TW.u_at NB 12 4); Z_to_bv 64 (TW.u_at Bw TW.A_GOT_n 4); Z_to_bv 64 (TW.u_at Bw TW.A_GOT_desk 4);
   Z_to_bv 64 (TW.u_at Bw TW.A_GOT_ndata 4); Z_to_bv 64 (TW.u_at Bw TW.A_GOT_acked 4);
   Z_to_bv 64 (TW.u_at Bw TW.A_GOT_foreign 4); Z_to_bv 64 (TB_GOT + 12 * TW.GOT_n Bw)].

(* The regions: the notice's first 16 bytes (read only), the jump table (read only, its six entries), one 4-byte
   field of GOT (writable, its value an atom), M.fly.on (written only, at the auipc value of its store), the record
   GOT.t[GOT.n] (written only, based at atom 42). *)
Definition nt_reg_p : YP09.region := YP09.mkRegion (Some 11%nat) 0 16 0 0
  [YP09.mkChunk 0 (YP09.CVal 4 (SOff 33 0)); YP09.mkChunk 4 (YP09.CVal 4 (SOff 34 0));
   YP09.mkChunk 8 (YP09.CVal 4 (SOff 35 0)); YP09.mkChunk 12 (YP09.CVal 4 (SOff 36 0))].
Definition nt_reg_tbl : YP09.region := YP09.mkRegion (Some (A_OBJ 36)) 0 24 0 0
  [YP09.mkChunk 0 (YP09.CVal 4 (SLit 0x624fc)); YP09.mkChunk 4 (YP09.CVal 4 (SLit 0x62578));
   YP09.mkChunk 8 (YP09.CVal 4 (SLit 0x62534)); YP09.mkChunk 12 (YP09.CVal 4 (SLit 0x62554));
   YP09.mkChunk 16 (YP09.CVal 4 (SLit 0x62520)); YP09.mkChunk 20 (YP09.CVal 4 (SLit 0x62674))].
Definition nt_reg_fld (obj atom : nat) : YP09.region :=
  YP09.mkRegion (Some (A_OBJ obj)) 0 4 0 4 [YP09.mkChunk 0 (YP09.CVal 4 (SOff atom 0))].
Definition nt_reg_fly : YP09.region := YP09.mkRegion (Some (A_HI 73)) (-1636) (-1632) (-1636) (-1632) [].
Definition nt_reg_rec : YP09.region := YP09.mkRegion (Some 42%nat) 4 16 4 16 [].
(* The frame region after the prologue: ra saved at sp - 8. *)
Definition nt_reg_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [YP09.mkChunk (-8) (YP09.CVal 8 (SOff 1 0))].

Definition nt_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 4096 (2 ^ 47 - 72) 3); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)]
    [] [].
Definition ss_nt : sstate :=
  mkSS AF_notice sr_atoms [stack_region 16; got_regionP; bcell_regionP 32] None nt_facts.
Definition NT_SH : list shent := [mkSHE 11 0 72].
Definition NT_Bx : sv := SOff 32 0.

(* The registers at the jump `jr a0` (0x83474), a0 set to the arm's code pointer. *)
Definition nt_regs_jr (a0v : sv) : list sv :=
  [SLit 0; SOff 1 0; SOff 2 (-16); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 8 0; SOff 9 0;
   a0v; SOff 11 0; SOff (A_OBJ 36) 0; SOff 13 0; SOff 14 0; SOff 32 0; SOff 16 0; SOff 17 0; SOff 18 0; SOff 19 0;
   SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0;
   SOff 30 0; SOff 31 0].
Definition nt_ss_jr (a0v : sv) : sstate := mkSS NT_JR (nt_regs_jr a0v) [nt_reg_frame] None nt_facts.

(* ------------------------------------------------------------------ *)
(* The model's paths                                                   *)
(* ------------------------------------------------------------------ *)

Lemma nt_pair_inv : forall (x y : list byte) (u v : unit), Some (x, u) = Some (y, v) -> y = x.
Proof.
  intros x y u v H.
  exact (eq_sym (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => y end) H)).
Qed.

Lemma nt_inc_ok : forall x (P : Z -> option (list byte * unit)) r,
  match TC.int_inc x with Some d => P d | None => None end = Some r -> x <> TC.INT_MAX /\ P (x + 1) = Some r.
Proof.
  intros x P r H. unfold TC.int_inc in H.
  destruct (Z.eqb_spec x TC.INT_MAX) as [E|E]; [discriminate H | split; [exact E | exact H]].
Qed.

Ltac nt_kind Hm Hk :=
  unfold TC.notice_m in Hm; cbv zeta in Hm; rewrite Hk in Hm;
  cbn [TC.N_STATE TC.N_ACKED TC.N_ACK_LOST TC.N_DESK TC.N_DATA TC.N_FOREIGN Z.eqb Pos.eqb] in Hm.

Lemma nt_m_out : forall I F Bw n Bw', (TI.n_kind n < 1 \/ 6 < TI.n_kind n) ->
  TC.notice_m I F Bw n = Some (Bw', tt) -> Bw' = Bw.
Proof.
  intros I F Bw n Bw' Hk Hm. unfold TC.notice_m in Hm. cbv zeta in Hm.
  destruct (Z.eqb_spec (TI.n_kind n) TC.N_STATE) as [E|_]; [unfold TC.N_STATE in E; lia|].
  destruct (Z.eqb_spec (TI.n_kind n) TC.N_ACKED) as [E|_]; [unfold TC.N_ACKED in E; lia|].
  destruct (Z.eqb_spec (TI.n_kind n) TC.N_ACK_LOST) as [E|_]; [unfold TC.N_ACK_LOST in E; lia|].
  destruct (Z.eqb_spec (TI.n_kind n) TC.N_DESK) as [E|_]; [unfold TC.N_DESK in E; lia|].
  destruct (Z.eqb_spec (TI.n_kind n) TC.N_DATA) as [E|_]; [unfold TC.N_DATA in E; lia|].
  destruct (Z.eqb_spec (TI.n_kind n) TC.N_FOREIGN) as [E|_]; [unfold TC.N_FOREIGN in E; lia|].
  exact (nt_pair_inv _ _ _ _ Hm).
Qed.

Lemma nt_m_desk : forall I F Bw n Bw', TI.n_kind n = TC.N_DESK -> TC.notice_m I F Bw n = Some (Bw', tt) ->
  TW.GOT_desk Bw <> TC.INT_MAX /\
  TC.check_state_desk_m I F (TW.set_GOT_desk Bw (TW.GOT_desk Bw + 1)) n = Some (Bw', tt).
Proof.
  intros I F Bw n Bw' Hk Hm. nt_kind Hm Hk.
  exact (nt_inc_ok (TW.GOT_desk Bw) (fun d => TC.check_state_desk_m I F (TW.set_GOT_desk Bw d) n) _ Hm).
Qed.

Lemma nt_m_acked : forall I F Bw n Bw', TI.n_kind n = TC.N_ACKED -> TC.notice_m I F Bw n = Some (Bw', tt) ->
  TW.GOT_acked Bw <> TC.INT_MAX /\
  TC.check_inflight_acked_m (TW.set_GOT_acked Bw (TW.GOT_acked Bw + 1)) n = Some (Bw', tt).
Proof.
  intros I F Bw n Bw' Hk Hm. nt_kind Hm Hk.
  exact (nt_inc_ok (TW.GOT_acked Bw) (fun a => TC.check_inflight_acked_m (TW.set_GOT_acked Bw a) n) _ Hm).
Qed.

Lemma nt_m_foreign : forall I F Bw n Bw', TI.n_kind n = TC.N_FOREIGN -> TC.notice_m I F Bw n = Some (Bw', tt) ->
  TW.GOT_foreign Bw <> TC.INT_MAX /\ Bw' = TW.set_GOT_foreign Bw (TW.GOT_foreign Bw + 1).
Proof.
  intros I F Bw n Bw' Hk Hm. nt_kind Hm Hk.
  destruct (nt_inc_ok (TW.GOT_foreign Bw) (fun fo => Some (TW.set_GOT_foreign Bw fo, tt)) _ Hm) as [H1 H2].
  split; [exact H1 | exact (nt_pair_inv _ _ _ _ H2)].
Qed.

(* The model's guards of a callee, cut down to its Some branch. *)
Ltac nt_unif H :=
  repeat (cbv beta iota zeta in H; match type of H with
    | (if ?c then _ else _) = _ =>
        let E := fresh "E" in destruct c eqn:E; [cbv beta iota zeta in H; try discriminate H|]
    | (match ?x with Some _ => _ | None => _ end) = _ =>
        let E := fresh "E" in destruct x eqn:E; [|cbv beta iota zeta in H; try discriminate H]
    end);
  cbv beta iota zeta in H.

Lemma nt_lost_same : forall B n B' u, TC.check_inflight_lost_m B n = Some (B', u) -> B' = B.
Proof. intros B n B' u H. unfold TC.check_inflight_lost_m in H. nt_unif H. exact (nt_pair_inv _ _ _ _ H). Qed.

Lemma nt_m_lost : forall I F Bw n Bw', TI.n_kind n = TC.N_ACK_LOST -> TC.notice_m I F Bw n = Some (Bw', tt) ->
  TC.check_inflight_lost_m Bw n = Some (Bw, tt) /\ Bw' = TW.set_M_fly_on Bw 0.
Proof.
  intros I F Bw n Bw' Hk Hm. nt_kind Hm Hk.
  destruct (TC.check_inflight_lost_m Bw n) as [[B1 u]|] eqn:EL; [|discriminate Hm].
  pose proof (nt_lost_same _ _ _ _ EL) as ->. destruct u.
  split; [reflexivity | exact (nt_pair_inv _ _ _ _ Hm)].
Qed.

Lemma nt_data_same : forall F B n B' u, TC.check_state_data_m F B n = Some (B', u) -> B' = B.
Proof. intros F B n B' u H. unfold TC.check_state_data_m in H. nt_unif H. exact (nt_pair_inv _ _ _ _ H). Qed.

Lemma nt_m_data : forall I F Bw n Bw', TI.n_kind n = TC.N_DATA -> TC.notice_m I F Bw n = Some (Bw', tt) ->
  TC.check_state_data_m F Bw n = Some (Bw, tt) /\ TW.GOT_ndata Bw <> TC.INT_MAX /\
  Bw' = TW.set_GOT_ndata Bw (TW.GOT_ndata Bw + 1).
Proof.
  intros I F Bw n Bw' Hk Hm. nt_kind Hm Hk.
  destruct (TC.check_state_data_m F Bw n) as [[B1 u]|] eqn:ED; [|discriminate Hm].
  pose proof (nt_data_same _ _ _ _ _ ED) as ->. destruct u.
  destruct (nt_inc_ok (TW.GOT_ndata Bw) (fun d => Some (TW.set_GOT_ndata Bw d, tt)) _ Hm) as [H1 H2].
  split; [reflexivity | split; [exact H1 | exact (nt_pair_inv _ _ _ _ H2)]].
Qed.

(* N_STATE: the record when GOT.n < TRANS_MAX (then 0 <= GOT.n), GOT.n + 1, and check_state_online when the
   state is S_ONLINE. *)
Definition nt_B1 (Bw : list byte) (n : TI.ntc) : list byte :=
  if TW.GOT_n Bw <? TC.TRANS_MAX then
    TW.set_GOT_t_reason (TW.set_GOT_t_old (TW.set_GOT_t_state Bw (TW.GOT_n Bw) (TI.n_state n)) (TW.GOT_n Bw)
      (TI.n_old n)) (TW.GOT_n Bw) (TI.n_reason n)
  else Bw.
Definition nt_B2 (Bw : list byte) (n : TI.ntc) : list byte := TW.set_GOT_n (nt_B1 Bw n) (TW.GOT_n Bw + 1).

Lemma nt_m_state : forall I F Bw n Bw', TI.n_kind n = TC.N_STATE -> TC.notice_m I F Bw n = Some (Bw', tt) ->
  TW.GOT_n Bw <> TC.INT_MAX /\ (TW.GOT_n Bw < TC.TRANS_MAX -> 0 <= TW.GOT_n Bw) /\
  (TI.n_state n = TC.S_ONLINE -> TC.check_state_online_m (nt_B2 Bw n) = Some (Bw', tt)) /\
  (TI.n_state n <> TC.S_ONLINE -> Bw' = nt_B2 Bw n).
Proof.
  intros I F Bw n Bw' Hk Hm. nt_kind Hm Hk. unfold nt_B2, nt_B1.
  destruct (Z.ltb_spec (TW.GOT_n Bw) TC.TRANS_MAX) as [Hlt|Hge].
  - destruct (Z.ltb_spec (TW.GOT_n Bw) 0) as [Hn|Hn]; [cbv beta iota in Hm; discriminate Hm|].
    destruct (nt_inc_ok (TW.GOT_n Bw) (fun g1 =>
      if TI.n_state n =? TC.S_ONLINE then TC.check_state_online_m (TW.set_GOT_n
        (TW.set_GOT_t_reason (TW.set_GOT_t_old (TW.set_GOT_t_state Bw (TW.GOT_n Bw) (TI.n_state n)) (TW.GOT_n Bw)
          (TI.n_old n)) (TW.GOT_n Bw) (TI.n_reason n)) g1)
      else Some (TW.set_GOT_n
        (TW.set_GOT_t_reason (TW.set_GOT_t_old (TW.set_GOT_t_state Bw (TW.GOT_n Bw) (TI.n_state n)) (TW.GOT_n Bw)
          (TI.n_old n)) (TW.GOT_n Bw) (TI.n_reason n)) g1, tt)) _ Hm) as [H1 H2].
    split; [exact H1|]. split; [intros _; exact Hn|].
    destruct (Z.eqb_spec (TI.n_state n) TC.S_ONLINE) as [Es|Es].
    + split; [intros _; exact H2 | intros C; exfalso; exact (C Es)].
    + split; [intros C; exfalso; exact (Es C) | intros _; exact (nt_pair_inv _ _ _ _ H2)].
  - destruct (nt_inc_ok (TW.GOT_n Bw) (fun g1 =>
      if TI.n_state n =? TC.S_ONLINE then TC.check_state_online_m (TW.set_GOT_n Bw g1)
      else Some (TW.set_GOT_n Bw g1, tt)) _ Hm) as [H1 H2].
    split; [exact H1|]. split; [intros C; lia|].
    destruct (Z.eqb_spec (TI.n_state n) TC.S_ONLINE) as [Es|Es].
    + split; [intros _; exact H2 | intros C; exfalso; exact (C Es)].
    + split; [intros C; exfalso; exact (Es C) | intros _; exact (nt_pair_inv _ _ _ _ H2)].
Qed.

(* ------------------------------------------------------------------ *)
(* The notice the callees get                                          *)
(* ------------------------------------------------------------------ *)

(* The announce's version and name cut to their first 10 bytes (the struct's char[10] fields): the bytes of the cut
   announce lie in the announce's 20 bytes, which no store of notice touches (notice_apart), while a longer list
   could reach into them. No callee model reads past byte 9 (DgnSpec.v strz_len_le). *)
Definition nt_ann_cut (a : TI.tann) : TI.tann := TI.TAnn (firstn 10 (TI.ta_version a)) (firstn 10 (TI.ta_name a)).
Definition nt_cut (n : TI.ntc) : TI.ntc :=
  TI.Ntc (TI.n_kind n) (TI.n_state n) (TI.n_old n) (TI.n_reason n) (TI.n_counter n) (TI.n_retry n)
    (TI.n_mac_offset n) (TI.n_pers n) (option_map nt_ann_cut (TI.n_ann n)) (TI.n_body n) (TI.n_body_len n).

Lemma nt_fsl_le : forall F q k, TC.frame_strz_len F q = Some k -> (k <= 9)%nat.
Proof.
  intros [f|] q k E; [|discriminate E]. unfold TC.frame_strz_len, TC.list_strz_len in E. cbv zeta in E.
  destruct (q - TI.tf_addr f <? 0); [discriminate E|].
  destruct (_ <? _)%nat; [discriminate E|]. injection E as <-. apply DSpec.strz_len_le.
Qed.

Lemma nt_firstn10_firstn : forall (l : list byte) k, (k <= 10)%nat -> firstn k (firstn 10 l) = firstn k l.
Proof. intros l k Hk. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma nt_firstn10_len : forall (l : list byte) k, (k < 10)%nat ->
  (length (firstn 10 l) <=? k)%nat = (length l <=? k)%nat.
Proof. intros l k Hk. rewrite length_firstn. apply Bool.eq_iff_eq_true. rewrite !Nat.leb_le. lia. Qed.

Lemma nt_firstn10_nth : forall (l : list byte) k d, (k < 10)%nat -> nth k (firstn 10 l) d = nth k l d.
Proof.
  intros l k d Hk. destruct (Nat.lt_ge_cases k (length l)) as [L|L].
  - rewrite <- (firstn_skipn 10 l) at 2. rewrite app_nth1; [reflexivity|]. rewrite length_firstn. lia.
  - rewrite (nth_overflow (firstn 10 l)) by (rewrite length_firstn; lia). rewrite nth_overflow by lia. reflexivity.
Qed.

Lemma nt_desk_cut : forall I F B n, TC.check_state_desk_m I F B (nt_cut n) = TC.check_state_desk_m I F B n.
Proof.
  intros I F B n. unfold TC.check_state_desk_m, nt_cut.
  cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_counter TI.n_retry TI.n_mac_offset TI.n_pers TI.n_ann
    TI.n_body TI.n_body_len].
  destruct (TI.n_ann n) as [a|]; cbn [option_map]; [|reflexivity].
  unfold nt_ann_cut. cbn [TI.ta_version TI.ta_name]. cbv beta iota zeta.
  destruct (TC.frame_strz_len F (TW.OW_desk_body B + TC.SPEC_ANN_VERSION)) as [vn|] eqn:EV; [|reflexivity].
  destruct (TC.frame_strz_len F (TW.OW_desk_body B + TC.SPEC_ANN_NAME)) as [nn|] eqn:EN; [|reflexivity].
  apply nt_fsl_le in EV. apply nt_fsl_le in EN.
  rewrite (nt_firstn10_firstn (TI.ta_version a) vn), (nt_firstn10_len (TI.ta_version a) vn),
    (nt_firstn10_nth (TI.ta_version a) vn), (nt_firstn10_firstn (TI.ta_name a) nn),
    (nt_firstn10_len (TI.ta_name a) nn), (nt_firstn10_nth (TI.ta_name a) nn) by lia.
  reflexivity.
Qed.

Lemma nt_data_cut : forall F B n, TC.check_state_data_m F B (nt_cut n) = TC.check_state_data_m F B n.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Changing a symbolic state between runs                              *)
(* ------------------------------------------------------------------ *)

Section sst. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* A register set to a value equal to the one it has. *)
Lemma nt_pin : forall E ss ms (r : bv 5) v,
  st_ok_pi segs VAL E ss ms -> YK11.getr (ms_regs ms) r = sv_denot E v -> bv_eqb r 0 = false ->
  st_ok_pi segs VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r v) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms r v HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *.
  cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
  apply (st_ok_regs segs E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
    (sr_set (ss_regs ss) r v) HS).
  intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
  - rewrite sr_get_set_same by exact Hr0. pose proof (st_ok_reg segs E _ ms r HS) as Hq. cbn [ss_regs] in Hq.
    rewrite <- Hq. symmetry. exact Hr.
  - rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

(* Regions dropped. *)
Lemma nt_drop : forall E ss ms rs,
  st_ok_pi segs VAL E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi segs VAL E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms rs HS Hs Hw. unfold st_ok_pi, abs_ss in *.
  exact (st_ok_submem segs E (setpc ss (BASE + ss_pc ss)) ms rs HS Hs Hw).
Qed.

(* A region added. *)
Lemma nt_add : forall E ss ms r,
  st_ok_pi segs VAL E ss ms -> region_wf r = true -> region_ok segs E (ms_mem ms) r -> all_disjoint E r (ss_mem ss) ->
  st_ok_pi segs VAL E (mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms r HS Hw Hr Hd. unfold st_ok_pi, abs_ss, setpc, st_ok, mem_ok in *.
  cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
  destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (M1 & M2 & M3) & H9).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj _ H9)))))))).
  split; [cbn [regions_wf]; rewrite Hw, M1; reflexivity|].
  split; [constructor; [exact Hr | exact M2] | cbn [pairwise_disjoint]; exact (conj Hd M3)].
Qed.
End sst.

(* ------------------------------------------------------------------ *)
(* Bytes, the world's fields, G                                        *)
(* ------------------------------------------------------------------ *)

(* 4 bytes of the notice at p + k, read from its garr8 array: u_at NB k 4. *)
Lemma nt_val4 : forall (mm : word -> option byte) p (NB : list byte) k,
  garr8 tfibsegs mm p (map DSpec.bz NB) -> length NB = 72%nat -> 0 <= k -> k + 4 <= 72 ->
  val_mem tfibsegs mm (p + k) 4 (TW.u_at NB k 4).
Proof.
  intros mm p NB k HG HL Hk Hk4 j Hj.
  assert (Hjl : (Z.to_nat k + j < length (map DSpec.bz NB))%nat) by (rewrite length_map; lia).
  pose proof (garr8_mbyte tfibsegs mm p (map DSpec.bz NB) (Z.to_nat k + j) HG Hjl) as Hb.
  replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia. rewrite Hb. f_equal. f_equal.
  assert (Hls : length (TW.sub NB k 4) = 4%nat) by (unfold TW.sub; rewrite length_firstn, length_skipn; lia).
  unfold TW.u_at. rewrite <- Hls at 2.
  rewrite (tw_le_byte_ble (TW.sub NB k 4) j (Z_to_bv 8 0)) by lia.
  rewrite (tw_nth_sub NB k 4 j (Z_to_bv 8 0)) by lia.
  rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.

Lemma nt_inG_GOT : forall a, TB_GOT <= a < TB_GOT + 224 -> inG TG.G_HARNESS_B a.
Proof.
  intros a Ha. unfold inG, TG.G_HARNESS_B. do 10 apply Exists_cons_tl. apply Exists_cons_hd.
  unfold in_zr. cbn [fst snd]. unfold TB_GOT in Ha. lia.
Qed.
Lemma nt_inG_M : forall a, TB_M <= a < TB_M + 1648 -> inG TG.G_HARNESS_B a.
Proof.
  intros a Ha. unfold inG, TG.G_HARNESS_B. do 5 apply Exists_cons_tl. apply Exists_cons_hd.
  unfold in_zr. cbn [fst snd]. unfold TB_M in Ha. lia.
Qed.

(* The bytes notice stores lie in GOT's or M's payload. *)
Lemma nt_wr_range : forall Bw n a, notice_wr Bw n a -> (TB_GOT <= a < TB_GOT + 224) \/ (TB_M + 96 <= a < TB_M + 100).
Proof.
  intros Bw n a Hw. unfold notice_wr, twb_fld in Hw.
  unfold TW.A_GOT_t_state, TW.A_GOT_n, TW.A_GOT_acked, TW.A_M_fly_on, TW.A_GOT_desk, TW.A_GOT_ndata, TW.A_GOT_foreign,
    TW.OFF_GOT, TW.OFF_M, TW.GOT_t_ESZ, TC.TRANS_MAX in Hw.
  destruct Hw as [(_ & [(Hg & Ha) | Ha]) | [(_ & Ha) | [(_ & Ha) | [(_ & Ha) | [(_ & Ha) | (_ & Ha)]]]]]; lia.
Qed.
Lemma nt_wr_G : forall Bw n a, notice_wr Bw n a -> inG TG.G_HARNESS_B a.
Proof.
  intros Bw n a Hw. destruct (nt_wr_range Bw n a Hw) as [H|H]; [exact (nt_inG_GOT a H) | apply nt_inG_M; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* The call's facts                                                    *)
(* ------------------------------------------------------------------ *)

Section ctx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The premises of notice's statement, and the notice's 72 bytes NB as trans_ntc_at gives them. *)
Record nt_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (p : Z) (n : TI.ntc) (Fr : option TI.tframe) (Bw Bw' NB : list byte) : Prop := {
  c_cells : transport_cells B;
  c_ncells : trans_notice_cells B;
  c_laws : AR_laws segs B;
  c_mtl : ameter_laws MT;
  c_gx : gx_ok segs B TG.G_HARNESS_B;
  c_gxe : gx_noerrno B TG.G_HARNESS_B;
  c_desk : forall fx' : YK11.FPState, @transport_check_state_desk_cg fx' rc B MT (transportb_sigma TB_check_state_desk);
  c_lost : forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIL.transport_check_inflight_lost_cg) fx';
  c_data : forall fx' : YK11.FPState, @transport_check_state_data_cg fx' rc B MT (transportb_sigma TB_check_state_data);
  c_acked : forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIA.transport_check_inflight_acked_cg) fx';
  c_online : forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSO.transport_check_state_online_cg) fx';
  c_J : ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k;
  c_ra : YK0s.ret_ok (YK11.getr regs 1);
  c_ra4 : 4096 <= raZ regs;
  c_gp : YK11.getr regs 3 = w64 (as_gp B);
  c_tp : YK11.getr regs 4 = w64 (as_tp B);
  c_a1 : YK11.getr regs 11 = w64 p;
  c_sp16 : spZ regs mod 16 = 0;
  c_lo : sp0 - STK <= spZ regs - NOTICE_STK;
  c_hi : spZ regs <= sp0;
  c_nt : trans_ntc_at B lyc Sc W memc regs NOTICE_STK p n;
  c_tf : trans_tframe_at B lyc Sc W memc regs NOTICE_STK Fr;
  c_ro : trans_rom_view_rd W memc;
  c_tw : tw_at TMAP_B (aview segs (w_H W) memc) Bw;
  c_m : TC.notice_m timg_B Fr Bw n = Some (Bw', tt);
  c_ap : notice_apart W memc p n Fr Bw;
  c_dt : TI.n_kind n = TC.N_DATA ->
    trans_src_ok B lyc Sc W memc (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (TI.n_body_len n) /\
    decode_off_win regs NOTICE_STK (TC.OW_dn_body Bw (TW.GOT_ndata Bw)) (TI.n_body_len n) /\
    TI.n_body_len n < 2 ^ 32;
  c_ev : st_nev S + k + NOTICE_EV <= EV_MAX;
  c_nb : garr8 segs (mrestrict (w_H W) memc) p (map DSpec.bz NB);
  c_nbl : length NB = 72%nat;
  c_kind : TW.s32_at NB 0 = TI.n_kind n;
  c_state : TW.s32_at NB 4 = TI.n_state n;
  c_old : TW.s32_at NB 8 = TI.n_old n;
  c_reason : TW.s32_at NB 12 = TI.n_reason n;
  c_counter : TW.u_at NB 64 4 = TI.n_counter n;
  c_retry : TW.u_at NB 68 2 = TI.n_retry n
}.

Ltac nt_open HC :=
  pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJ Hra Hra4 Hgp Htp H11 Hsp16 Hlo Hhi
    HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].

(* The facts every segment uses: the call state's AR, the stack window present, the bounds of sp, sp - 16 aligned
   in the journal's window, and where the notice lies. *)
Lemma nt_basics : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB,
  nt_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ->
  @AR rc segs B lyc Sc W memc mdc /\
  (forall a, spZ regs - NOTICE_STK <= a < spZ regs -> apresent (w_H W) memc a) /\
  2 ^ 46 <= spZ regs <= 2 ^ 47 /\ alloc_ceiling <= spZ regs - NOTICE_STK /\ (spZ regs - 16 - sp0) mod 16 = 0 /\
  4096 <= p /\ p + 72 <= 2 ^ 47 /\ p mod 8 = 0 /\ decode_off_win regs NOTICE_STK p 72 /\
  decode_rd_ok W memc p 72.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC. nt_open HC.
  pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HNT as (P0 & P8 & Hsrc & Hoff & _).
  assert (FS : NOTICE_STK = 8240) by reflexivity.
  split; [exact HAR|].
  split; [intros a Ha; apply Hpres0; lia|].
  split; [lia|]. split; [lia|].
  split.
  { replace (spZ regs - 16 - sp0) with (spZ regs - sp0 + (-1) * 16) by lia.
    rewrite Z_mod_plus_full, Zminus_mod, Hsp16, Hsp0a. reflexivity. }
  destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc p NTC_SIZE HAR Hsrc ltac:(unfold NTC_SIZE; lia)) as [Hpl | Hpl];
    unfold NTC_SIZE in Hpl.
  - split; [lia|]. split; [lia|]. split; [exact P8|]. split; [exact Hoff|].
    exact (trans_src_ok_rd B LAWS lyc Sc W memc mdc p NTC_SIZE HAR Hsrc ltac:(unfold NTC_SIZE; lia)).
  - split; [lia|]. split; [lia|]. split; [exact P8|]. split; [exact Hoff|].
    exact (trans_src_ok_rd B LAWS lyc Sc W memc mdc p NTC_SIZE HAR Hsrc ltac:(unfold NTC_SIZE; lia)).
Qed.

(* ------------------------------------------------------------------ *)
(* The valuation and the entry state                                   *)
(* ------------------------------------------------------------------ *)

Definition nt_E (regs : bvmap 5 word) (NB Bw : list byte) : env := Eimg (PI := PI_transportb) (Ereg regs (nt_vals NB Bw)).

Lemma nt_E_reg : forall regs NB Bw n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (nt_E regs NB Bw) n = YK11.getr regs r.
Proof. intros regs NB Bw n r Hn. unfold nt_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma nt_E_atom : forall regs NB Bw j, (j < 11)%nat ->
  ew (nt_E regs NB Bw) (32 + j) = nth j (nt_vals NB Bw) (Z_to_bv 64 0).
Proof. intros regs NB Bw j Hj. unfold nt_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

Lemma nt_cvals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  BASE + AF_notice = TI.ti_notice timg_B /\ VAL (A_OBJ 36) = TRANS_JT_NOTICE /\
  VAL (A_OBJ 13) = TB_GOT /\ VAL (A_OBJ 37) = TB_GOT + 208 /\ VAL (A_OBJ 38) = TB_GOT + 220 /\
  VAL (A_OBJ 39) = TB_GOT + 216 /\ VAL (A_OBJ 40) = TB_GOT + 212 /\ VAL (A_HI 73) - 1636 = TB_M + 96 /\
  VAL (A_HI 72) = TB_GOT + 208 + 1096 /\ VAL (A_HI 74) = TB_GOT + 220 + 1148 /\
  VAL (A_HI 75) = TB_GOT + 216 + 1176 /\ VAL (A_HI 77) = TB_GOT + 212 + 1468 /\ BASE = 0x812a0.
Proof. vm_compute. repeat split. Qed.

(* The two image regions hold what transport_cells says they hold, at any AR state (diginet_session_config_default.v
   scfg_img_ok). *)
Lemma nt_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H W) mem) got_regionP /\ region_ok segs E (mrestrict (w_H W) mem) (bcell_regionP 32).
Proof.
  intros ly S W mem md E HCELLS HAR E1 E95 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct nt_cvals as (V1 & V95 & _).
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

(* The shadow entry of the notice's 72 bytes, at a valuation that agrees on atoms 11 and 32. *)
Lemma nt_shok : forall (W : world segs) m (E : env) p,
  range_addressable (aview segs (w_H W) m) SHADOW_OFF p 72 -> amem_range p 72 -> 0 <= p ->
  ew E 11 = Z_to_bv 64 p -> ew E 32 = Z_to_bv 64 SHADOW_OFF -> p + 72 <= 2 ^ 47 ->
  sh_ok segs NT_Bx NT_SH E (mrestrict (w_H W) m).
Proof.
  intros W m E p HRA Ham Hp0 E11 E32 Hp47.
  unfold sh_ok, NT_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) m E NT_Bx 11 p 72 p 0 72 HRA).
  - unfold U, NT_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  - unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

(* The entry state and the notice's shadow entry. *)
Lemma nt_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB,
  nt_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ->
  st_ok_pi segs VAL (nt_E regs NB Bw) ss_nt
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_notice)) memc (YK11.seg_rom segs)))
  /\ sh_ok segs NT_Bx NT_SH (nt_E regs NB Bw) (mrestrict (w_H W) memc).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC.
  destruct (nt_basics _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)
    as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoff & Hrd).
  nt_open HC.
  set (E0 := nt_E regs NB Bw).
  assert (FS : NOTICE_STK = 8240) by reflexivity.
  assert (E2 : ew E0 2 = YK11.getr regs 2) by (unfold E0; apply nt_E_reg; reflexivity).
  assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (E11 : ew E0 11 = Z_to_bv 64 p) by (unfold E0; rewrite (nt_E_reg regs NB Bw 11 11%bv eq_refl); exact H11).
  assert (U11 : bv_unsigned (ew E0 11) = p) by (rewrite E11; apply unsigned_lit_small; lia).
  assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF) by (exact (nt_E_atom regs NB Bw 0 ltac:(lia))).
  assert (EOB : forall j, (j < 97)%nat -> ew E0 (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E0, nt_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct (nt_img_ok lyc Sc W memc mdc E0 HCELLS HAR (EOB 1%nat ltac:(lia)) (EOB 95%nat ltac:(lia)) E32) as [RG RC].
  destruct nt_cvals as (V1 & V95 & _).
  assert (VB : forall n v0, ew E0 n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E0 (Some n) = v0)
    by (intros n0 v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  destruct Hrd as (_ & HRA & _ & Ham & _ & _).
  split.
  - rewrite restrict_mkst_fx. unfold ss_nt.
    apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [exact RG | apply Forall_cons; [exact RC | apply Forall_nil]]].
      unfold stack_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hwin. lia.
    + apply pairwise_disjoint_of_extents.
      unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (EOB 95%nat ltac:(lia))) by (rewrite V95; unfold FCells.CELL_K; lia).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      rewrite V1, V95. unfold FCells.GOT_CELL_K, FCells.CELL_K in *.
      repeat split; first [exact I | lia].
    + unfold nt_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U11, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
  - exact (nt_shok W memc E0 p HRA Ham ltac:(lia) E11 E32 Hp47).
Qed.

(* ------------------------------------------------------------------ *)
(* What the walk keeps, and the post at a return                       *)
(* ------------------------------------------------------------------ *)

(* The bytes the walk may change: its stack window, and the bytes notice_wr names. *)
Definition nt_Zs (regs : bvmap 5 word) (Bw : list byte) (n : TI.ntc) (a : Z) : Prop :=
  (spZ regs - NOTICE_STK <= a < spZ regs) \/ notice_wr Bw n a.

(* From the entry memory memc to m: the view outside Zs kept, presence grown. *)
Definition nt_KA (W : world segs) (memc m : word -> option byte) (Zs : Z -> Prop) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) m a = aview segs (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m a).

Lemma nt_KA_refl : forall W memc Zs, nt_KA W memc memc Zs.
Proof. intros W memc Zs. split; [intros; reflexivity | intros a Ha; exact Ha]. Qed.

(* A run whose regions' windows lie in Zs. *)
Lemma nt_KA_run : forall E rs (W : world segs) memc (m m' : word -> option byte) (Zs : Z -> Prop),
  nt_KA W memc m Zs ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi x, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= x < base_val E b + whi -> Zs x) ->
  nt_KA W memc m' Zs.
Proof.
  intros E rs W memc m m' Zs [K1 K2] Hfr Hg Hw. split.
  - intros a Ha Hn. rewrite (kept_of_frame E rs (w_H W) m m' Zs Hfr Hw a Ha Hn). exact (K1 a Ha Hn).
  - intros a Ha. exact (apresent_grows _ _ _ a Hg (K2 a Ha)).
Qed.

(* A step that changes only bytes of Zs (a callee's window inside the walk's). *)
Lemma nt_KA_step : forall (W : world segs) memc (m m' : word -> option byte) (Zs Zc : Z -> Prop),
  nt_KA W memc m Zs ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zc a -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  (forall a, Zc a -> Zs a) ->
  nt_KA W memc m' Zs.
Proof.
  intros W memc m m' Zs Zc [K1 K2] Hk Hg HZ. split.
  - intros a Ha Hn. rewrite (Hk a Ha (fun Z => Hn (HZ a Z))). exact (K1 a Ha Hn).
  - intros a Ha. exact (Hg a (K2 a Ha)).
Qed.

(* The post at a return (the `ret` at 0x8360c, or a tail callee's return), from the walk's last facts. *)
Lemma nt_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB regsF mF mdF,
  nt_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mF mdF k ->
  nt_KA W memc mF (nt_Zs regs Bw n) ->
  tw_at TMAP_B (aview segs (w_H W) mF) Bw' ->
  aregs_preserved regs regsF -> YK11.getr regsF 1 = YK11.getr regs 1 ->
  forall mat, @transport_notice_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n Bw Bw' W
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB regsF mF mdF HC HJF [KA GA] HtwF
    HP RF1 mat.
  destruct (nt_basics _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC)
    as (HAR & Hwin & Hsp & Hce & _ & _ & _ & _ & _ & _).
  nt_open HC.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : NOTICE_STK = 8240) by reflexivity.
  assert (GLOW : forall a, inG TG.G_HARNESS_B a -> a < kLowMemEnd).
  { intros a Ha. exact (proj2 (transportb_segs_low a (proj1 (HGX a Ha)))). }
  unfold transport_notice_post, transport_cg_post.
  exists lyc, Sc, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
  split.
  { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [unfold NOTICE_EV; lia|].
  split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc mF
      (spZ regs - NOTICE_STK) (spZ regs) (notice_wr Bw n) (nt_Zs regs Bw n) HAR).
    - apply dk_kept_refl_g. exact Hwin.
    - exact KA.
    - exact GA.
    - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso. pose proof (GLOW a (nt_wr_G _ _ _ Hw)). unfold kLowMemEnd in *. lia.
    - intros b m i Hb Hi [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
    - intros a [Hw | Hw] Hi HnG _ _.
      + pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
      + exact (HnG (nt_wr_G _ _ _ Hw)).
    - intros cid pos a Hin Hr [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  exact HtwF.
Qed.
End ctx.
