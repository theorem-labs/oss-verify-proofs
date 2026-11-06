(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths, module names and numbers changed; 492 of its 579 lines of code are new or changed and 943 lines of the source are left out. *)
(* diginet_session_close_seg_head: Lemma close_head : close_head_stmt (lib/B/Prog/diginet_session_close_segs.v), the
   head piece of image B's walk of diginet_session_close (fuzz_transport.asan-ubsan 0x87648 = transportb_sigma
   TB_diginet_session_close, AF_diginet_session_close = 0x63a8 of lib/B/Prog/DgnTransportBList.v), from the entry to
   the two cuts close_send_at (+0xd8) and close_join_at (+0x8c).

   The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 []); the runs are the symbolic
   runs of lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x. The state at the entry (clo_entry) has four regions:
   the 32-byte frame below sp (the four saves), the shadow base's GOT word (object 1) and its cell (object 95), and the
   three g_s fields the code loads, read-only, each chunk holding the world's bytes (TWorldG.v tw_read_val):
     atom 33  S_desk_known (s + 116, 4)     atom 34  S_foreign (s + 136, 4)     atom 35  S_state (s + 112, 4)
   a0 = s is atom 10 with the exact fact CLOSE_S (64-aligned), so the engine decides `beqz a0` and the alignment test
   of s (no branch to the trap word). The shadow entry CLO_SH is g_s's whole payload, whose shadow is 0 at every AR
   state (trans_close_cells, DgnTransportBCg.v decode_zshadow_rd: clo_ra, clo_shok), so the engine decides the three
   instrumented checks. The runs and the splits (DgnTransportBPaLib.v psrr_branch_tok), each one of close_go's tests:
     run 1   +0x00 .. +0x48: the frame, the four saves, s0 = s, s2 = the shadow base, `beqz` on S_desk_known;
     run 2   +0x4c .. +0x64: `bnez` on S_foreign;
     run 3   +0x68 .. +0x84: `bne` on S_state against 3.
   A test that makes close_go Bw false runs `li s1, 0` (+0x88) to the join cut (r = 0, close_sent_nogo); the taken
   `bne` lands at the send cut. The head writes only its frame, so the world relation at both cuts is at Bw, and the
   four saved words are read back from the stack region of the symbolic state at the cut (clo_saved_of). *)
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
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
diginet_session_close_cg diginet_session_close_segs.
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
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at the entry                                  *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the entry, 32 the shadow base, 33 .. 35 the three loaded fields of g_s. *)
Definition clo_gs : YP09.region := YP09.mkRegion (Some 10%nat) 112 140 0 0
  [YP09.mkChunk 112 (CVal 4 (SOff 35 0)); YP09.mkChunk 116 (CVal 4 (SOff 33 0));
   YP09.mkChunk 136 (CVal 4 (SOff 34 0))].
Definition clo_regions : smem := [stack_region CLOSE_FRAME; got_regionP; bcell_regionP 32; clo_gs].
Definition clo_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF CLOSE_S CLOSE_S 6); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_clo : sstate := mkSS AF_diginet_session_close sr_atoms clo_regions None clo_facts.
(* The shadow entry of g_s's payload (18264 bytes), and the shadow base of the token engine. *)
Definition CLO_SH : list shent := [mkSHE 10 0 TW.SZ_g_s].
Definition CLO_Bx : sv := SOff 32 0.

(* The values of atoms 32 .. 35 at the world Bw. *)
Definition clo_vals_l (Bw : list byte) : list word :=
  [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw TW.A_S_desk_known 4); Z_to_bv 64 (TW.u_at Bw TW.A_S_foreign 4);
   Z_to_bv 64 (TW.u_at Bw TW.A_S_state 4)].

(* The bytes a run may write: the frame. *)
Definition clo_Zr (sp a : Z) : Prop := sp - CLOSE_FRAME <= a < sp.

(* The goal YK11.getr (ms_regs ms) r = v from the symbolic value of r in HS, computed, then tac. *)
Ltac clo_rg HS tac :=
  lazymatch goal with |- YK11.getr (ms_regs ?msx) ?r = ?v =>
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac
  | ?T => idtac "clo_rg: no match for" T; fail
  end end.

(* ------------------------------------------------------------------ *)
(* 2. The model's tests                                                *)
(* ------------------------------------------------------------------ *)

Lemma clo_go_dk : forall Bw, (TW.S_desk_known Bw =? 0) = true -> close_go Bw = false.
Proof. intros Bw H. unfold close_go. rewrite H. reflexivity. Qed.

Lemma clo_go_fo : forall Bw, (TW.S_foreign Bw =? 0) = false -> close_go Bw = false.
Proof. intros Bw H. unfold close_go. rewrite H, andb_false_r. reflexivity. Qed.

Lemma clo_go_st : forall Bw, (TW.S_state Bw =? 3) = true -> close_go Bw = false.
Proof.
intros Bw H. unfold close_go. change TS0.DIGINET_S_CLOSED with 3. rewrite H. cbn [negb]. rewrite andb_false_r.
reflexivity.
Qed.

Lemma clo_go_t : forall Bw, (TW.S_desk_known Bw =? 0) = false -> (TW.S_foreign Bw =? 0) = true ->
  (TW.S_state Bw =? 3) = false -> close_go Bw = true.
Proof. intros Bw H1 H2 H3. unfold close_go. change TS0.DIGINET_S_CLOSED with 3. rewrite H1, H2, H3. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 3. The branch conditions at the valuation                           *)
(* ------------------------------------------------------------------ *)

Lemma clo_u64 : forall v, bv_unsigned (Z_to_bv 64 v) = v mod 2 ^ 64.
Proof. intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity. Qed.

Lemma clo_eqb_s32 : forall v w, - 2 ^ 31 <= v < 2 ^ 31 -> - 2 ^ 31 <= w < 2 ^ 31 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
  intros v w Hv Hw. unfold bv_eqb. rewrite !clo_u64.
  destruct (Z.eqb_spec v w) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intro E. apply N. Z.div_mod_to_equations. lia.
Qed.

(* The sign-extended 4-byte load of a world field is the model's s32_at. *)
Lemma clo_sext : forall (E : env) (n : nat) Bw k, ew E n = Z_to_bv 64 (TW.u_at Bw k 4) ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (TW.s32_at Bw k).
Proof.
intros E n Bw k Hew. assert (HR : 0 <= TW.u_at Bw k 4 < 2 ^ 32) by exact (TWL.u_at_range Bw k 4).
cbn [sv_denot]. rewrite Hew, Z.add_0_r.
rewrite unsigned_lit_small by lia.
change (Z_to_bv 64 (TW.u_at Bw k 4)) with (le_bytes_to_word (TW.sub Bw k 4)).
apply lw_world.
Qed.

Lemma clo_br_ne : forall (E : env) (n : nat) Bw k c, ew E n = Z_to_bv 64 (TW.u_at Bw k 4) -> - 2 ^ 31 <= c < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit c)) = negb (TW.s32_at Bw k =? c).
Proof.
intros E n Bw k c H Hc. pose proof (TWL.s32_range Bw k) as R. cbn [branch_taken]. rewrite (clo_sext E n Bw k H).
change (sv_denot E (SLit c)) with (Z_to_bv 64 c). rewrite (clo_eqb_s32 (TW.s32_at Bw k) c ltac:(lia) Hc). reflexivity.
Qed.

Lemma clo_br_eq : forall (E : env) (n : nat) Bw k c, ew E n = Z_to_bv 64 (TW.u_at Bw k 4) -> - 2 ^ 31 <= c < 2 ^ 31 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit c)) = (TW.s32_at Bw k =? c).
Proof.
intros E n Bw k c H Hc. pose proof (TWL.s32_range Bw k) as R. cbn [branch_taken]. rewrite (clo_sext E n Bw k H).
change (sv_denot E (SLit c)) with (Z_to_bv 64 c). rewrite (clo_eqb_s32 (TW.s32_at Bw k) c ltac:(lia) Hc). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The walk's lemmas                                                *)
(* ------------------------------------------------------------------ *)

Section head. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma clo_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  BASE + AF_diginet_session_close = transportb_sigma TB_diginet_session_close.
Proof. vm_compute. repeat split. Qed.

(* The walk's valuation: the 32 registers at the entry, the shadow base and the three loaded fields of Bw. *)
Definition clo_E (regs : bvmap 5 word) (Bw : list byte) : env := Eimg (PI := PI_transportb) (Ereg regs (clo_vals_l Bw)).

(* The two image regions hold what transport_cells says they hold, at any AR state. *)
Lemma clo_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H W) mem) got_regionP /\ region_ok segs E (mrestrict (w_H W) mem) (bcell_regionP 32).
Proof.
  intros ly S W mem md E HCELLS HAR E1 E95 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct clo_vals as (V1 & V95 & _).
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

(* g_s's payload is addressable at every AR state: the shadow of its 2283 whole granules is 0 (trans_close_cells). *)
Lemma clo_ra : forall ly S (W : world segs) mem md,
  trans_close_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF CLOSE_S TW.SZ_g_s.
Proof.
intros ly S W mem md HZ HAR x Hx.
assert (ES : CLOSE_S = 6157888) by reflexivity. assert (SZ : TW.SZ_g_s = 18264) by reflexivity.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold shadow_of_addr.
exists 0. split; [|left; reflexivity].
assert (Hz := decode_zshadow_rd B ly S W mem md CLOSE_S (CLOSE_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The run's shadow entry holds at every AR state. *)
Lemma clo_shok : forall ly S (W : world segs) mem md (E : env),
  trans_close_cells B -> @AR rc segs B ly S W mem md ->
  ew E 10 = Z_to_bv 64 CLOSE_S -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  sh_ok segs CLO_Bx CLO_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E HZ HAR E10 E32.
assert (ES : CLOSE_S = 6157888) by reflexivity. assert (SZ : TW.SZ_g_s = 18264) by reflexivity.
unfold sh_ok, CLO_SH. constructor; [|constructor].
apply (shent_ok_of_range segs (w_H W) mem E CLO_Bx 10 CLOSE_S TW.SZ_g_s CLOSE_S 0 TW.SZ_g_s
  (clo_ra ly S W mem md HZ HAR)).
- unfold U, CLO_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
- lia.
- lia.
- intros x Hx. rewrite SZ in Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The entry state, and the shadow entry of g_s. *)
Lemma clo_entry : forall ly S (W : world segs) regs mem md Bw,
  transport_cells B -> trans_close_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  (forall a, spZ regs - CLOSE_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  YK11.getr regs 10 = w64 CLOSE_S ->
  st_ok_pi segs VAL (clo_E regs Bw) ss_clo
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_close)) mem (YK11.seg_rom segs)))
  /\ sh_ok segs CLO_Bx CLO_SH (clo_E regs Bw) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md Bw HCELLS HZ HAR Htw Hpres Hsp Hsp16 H10.
  assert (ES : CLOSE_S = 6157888) by reflexivity. assert (EG : TB_g_s = 6157888) by reflexivity.
  set (E := clo_E regs Bw).
  assert (E2 : ew E 2 = YK11.getr regs 2) by (unfold E, clo_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 CLOSE_S)
    by (unfold E, clo_E; rewrite (ew_Eimg_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (U10 : bv_unsigned (ew E 10) = CLOSE_S) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (clo_vals_l Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, clo_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  cbn [Nat.add nth clo_vals_l] in E32, E33, E34, E35.
  assert (EOB : forall j, (j < 96)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, clo_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct (clo_img_ok ly S W mem md E HCELLS HAR (EOB 1%nat ltac:(lia)) (EOB 95%nat ltac:(lia)) E32) as [RG RC].
  destruct clo_vals as (V1 & V95 & _).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (R33 : 0 <= TW.u_at Bw TW.A_S_desk_known 4 < 2 ^ 32) by exact (TWL.u_at_range Bw TW.A_S_desk_known 4).
  assert (R34 : 0 <= TW.u_at Bw TW.A_S_foreign 4 < 2 ^ 32) by exact (TWL.u_at_range Bw TW.A_S_foreign 4).
  assert (R35 : 0 <= TW.u_at Bw TW.A_S_state 4 < 2 ^ 32) by exact (TWL.u_at_range Bw TW.A_S_state 4).
  split.
  - rewrite restrict_mkst_fx. unfold ss_clo, clo_regions.
    apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [exact RG | apply Forall_cons; [exact RC |]]].
      * unfold stack_region, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Usp. unfold CLOSE_FRAME in *.
        split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * apply Forall_cons; [|apply Forall_nil].
        unfold clo_gs, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        -- apply (chunk_ok_val segs E _ CLOSE_S 112 4 (SOff 35 0) (TW.u_at Bw TW.A_S_state 4));
             [apply DEN; [exact E35 | lia] | exact R35 | lia |].
           exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 112 4 TMAP_B_ok Htw TMAP_B_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ CLOSE_S 116 4 (SOff 33 0) (TW.u_at Bw TW.A_S_desk_known 4));
             [apply DEN; [exact E33 | lia] | exact R33 | lia |].
           exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 116 4 TMAP_B_ok Htw TMAP_B_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ CLOSE_S 136 4 (SOff 34 0) (TW.u_at Bw TW.A_S_foreign 4));
             [apply DEN; [exact E34 | lia] | exact R34 | lia |].
           exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 136 4 TMAP_B_ok Htw TMAP_B_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + apply pairwise_disjoint_of_extents.
      unfold stack_region, got_regionP, bcell_regionP, clo_gs, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (EOB 95%nat ltac:(lia))) by (rewrite V95; unfold FCells.CELL_K; lia).
      cbn [base_val]. rewrite Usp, U10.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      rewrite V1, V95. unfold FCells.GOT_CELL_K, FCells.CELL_K, CLOSE_FRAME in *.
      repeat split; first [exact I | lia].
    + unfold clo_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U10, E32, E33, E34, E35.
      rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
      rewrite (unsigned_lit_small (TW.u_at Bw TW.A_S_desk_known 4)) by lia.
      rewrite (unsigned_lit_small (TW.u_at Bw TW.A_S_foreign 4)) by lia.
      rewrite (unsigned_lit_small (TW.u_at Bw TW.A_S_state 4)) by lia.
      change (2 ^ 4) with 16. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite ES; reflexivity].
  - exact (clo_shok ly S W mem md E HZ HAR E10 E32).
Qed.

(* What the walk keeps, from its entry memory memc to a memory m: the view outside the bytes Zs, and presence. *)
Definition clo_KA (W : world segs) (memc m : word -> option byte) (Zs : Z -> Prop) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) m a = aview segs (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m a).

(* A run whose windows lie in Zs keeps clo_KA. *)
Lemma clo_KA_step : forall E rs (W : world segs) memc (m m' : word -> option byte) (Zs : Z -> Prop),
  clo_KA W memc m Zs ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
  clo_KA W memc m' Zs.
Proof.
intros E rs W memc m m' Zs [K1 K2] Hfr Hg Hw. split.
- intros a Ha Hn. rewrite (YC4b.kept_of_frame E rs (w_H W) m m' Zs Hfr Hw a Ha Hn). exact (K1 a Ha Hn).
- intros a Ha. exact (apresent_grows _ _ _ a Hg (K2 a Ha)).
Qed.

(* The four saved words, read back from the stack region of a symbolic state whose valuation gives the entry
   registers. *)
Lemma clo_saved_of : forall (Ex : env) (H : word -> bool) (m : word -> option byte) (regs : bvmap 5 word)
    lo hi wlo whi cs,
  region_ok segs Ex (mrestrict H m) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew Ex 2) = spZ regs ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ex n = YK11.getr regs r) ->
  In (YP09.mkChunk (-8) (CVal 8 (SOff 1 0))) cs -> In (YP09.mkChunk (-16) (CVal 8 (SOff 8 0))) cs ->
  In (YP09.mkChunk (-24) (CVal 8 (SOff 9 0))) cs -> In (YP09.mkChunk (-32) (CVal 8 (SOff 18 0))) cs ->
  Forall (fun o : Z * Z => rdword (aview segs H m) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) CLOSE_SAVED.
Proof.
  intros Ex H m regs lo hi wlo whi cs HR Usp EE I1 I8 I9 I18.
  assert (ONE : forall (n : nat) (rg : bv 5) od, In (YP09.mkChunk od (CVal 8 (SOff n 0))) cs ->
    Z.of_nat n = bv_unsigned rg ->
    rdword (aview segs H m) (spZ regs + od) = Some (bv_unsigned (YK11.getr regs rg))).
  { intros n rg od Hin Hn.
    pose proof (bv_unsigned_in_range 64 (YK11.getr regs rg)) as Rg. unfold bv_modulus in Rg.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in Rg.
    apply (YF0x.val_mem_rdword H m (spZ regs + od) _ Rg).
    apply (can_field_of_region Ex (mrestrict H m) 2 (spZ regs) cs lo hi wlo whi od 8%N (SOff n 0) _ HR Usp Hin).
    - cbn [sv_denot]. rewrite (EE n rg Hn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - cbn. lia.
    - cbn. lia. }
  unfold CLOSE_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - replace (spZ regs - 8) with (spZ regs + -8) by lia. exact (ONE 1%nat (Z_to_bv 5 1) (-8) I1 eq_refl).
  - replace (spZ regs - 16) with (spZ regs + -16) by lia. exact (ONE 8%nat (Z_to_bv 5 8) (-16) I8 eq_refl).
  - replace (spZ regs - 24) with (spZ regs + -24) by lia. exact (ONE 9%nat (Z_to_bv 5 9) (-24) I9 eq_refl).
  - replace (spZ regs - 32) with (spZ regs + -32) by lia. exact (ONE 18%nat (Z_to_bv 5 18) (-32) I18 eq_refl).
Qed.

(* close_cur at a memory of the run whose only written bytes are the frame: the journal, no event, the call's frames,
   blocks, layout and meter, what the call keeps (the frame lies in the window), and the four saved words. *)
Lemma clo_cur : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs TF Bw memF mdF,
  AR_laws segs B -> ameter_laws MT ->
  @AR rc segs B lyc Sc W memc mdc ->
  (forall a, spZ regs - CLOSE_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  alloc_ceiling <= spZ regs - CLOSE_STK -> spZ regs <= 2 ^ 47 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memF mdF k ->
  clo_KA W memc memF (clo_Zr (spZ regs)) ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) memF) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) CLOSE_SAVED ->
  close_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw lyc Sc W memF mdF 0.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TF Bw memF mdF
    LAWS MTL HAR Hwin Hce H47 HJF [KA GA] HSV.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof close_stk_val as (FS & _ & _ & FF).
  unfold close_cur.
  split; [rewrite Z.add_0_r; exact HJF|].
  split; [pose proof close_ev_val as (EV & _); lia|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split; [reflexivity|].
  split; [exact (mo_le_refl MT MTL Sc)|].
  split; [|exact HSV].
  apply (dk_kept_step_g segs B LAWS transportb_segs_low G_HARNESS_B lyc Sc W memc mdc memc memF
    (spZ regs - CLOSE_STK) (spZ regs) (close_wr TF Bw) (clo_Zr (spZ regs)) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - exact KA.
  - exact GA.
  - intros a Ha _. unfold clo_Zr in Ha. lia.
  - intros b m i Hb Hi Hz. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
    unfold clo_Zr in Hz. lia.
  - intros a Hz Hi _ _ _. pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
    unfold clo_Zr in Hz. lia.
  - intros cid pos a Hin Hr Hz. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    unfold clo_Zr in Hz.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

(* The world relation at a memory whose only written bytes are the frame. *)
Lemma clo_tw : forall (W : world segs) memc memF regs Bw,
  2 ^ 46 <= spZ regs -> tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
  clo_KA W memc memF (clo_Zr (spZ regs)) -> tw_at TMAP_B (aview segs (w_H W) memF) Bw.
Proof.
  intros W memc memF regs Bw Hsp Htw [KA _].
  pose proof close_stk_val as (_ & _ & _ & FF).
  apply (tw_kept TMAP_B (aview segs (w_H W) memc)); [exact Htw|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold G_HARNESS_B_LO, G_HARNESS_B_HI in Hh.
  apply KA; [lia | unfold clo_Zr; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The walk's tactics                                               *)
(* ------------------------------------------------------------------ *)

(* The write rights of a run: the frame's bytes are the caller's stack window, the other regions have no writable
   byte. *)
Ltac clo_awr Usp U10 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?Usp, ?U10 in Ha;
      first [ lia
            | left; split; [unfold awr_byte; left; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.

(* The windows of a run lie in the frame. *)
Ltac clo_win Usp U10 :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp, ?U10 in Hx;
      unfold clo_Zr, CLOSE_FRAME; lia |]);
  destruct Hin.

(* After a run: the model generalized, the kept facts carried to the run's last memory, the old machine states
   dropped, the current one named ms. *)
Ltac clo_after KA HS Usp U10 :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt;
    try clear m0 end;
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    let KA' := fresh "KAn" in
    pose proof (clo_KA_step Ex rs _ _ _ _ _ KA HFr HG ltac:(clo_win Usp U10)) as KA'; clear KA HFr HG;
    rename KA' into KA end;
  lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
  repeat match goal with old : machine_state |- _ => clear old end;
  lazymatch type of HS with context [restrict _ ?m] => try rename m into ms end.

(* The stack region (region 0) of the symbolic state HS at its machine state's memory. *)
Ltac clo_region0 HS HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 0 r0 HS); vm_compute; reflexivity)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (st_ok_region_nth Ex ssx (restrict Hh msx) 0 r0 HS); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.

(* The four saved words at the machine state of HS. *)
Ltac clo_saved HS W regs Usp EE HSV :=
  let HR := fresh "HR0" in
  clo_region0 HS HR;
  lazymatch type of HR with region_ok _ _ (mrestrict _ ?mm) _ =>
  assert (HSV : Forall (fun o : Z * Z => rdword (aview tfibsegs (w_H W) mm) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) CLOSE_SAVED)
    by (apply (clo_saved_of _ _ _ _ _ _ _ _ _ HR Usp EE);
        cbn [In]; repeat (first [left; reflexivity | right])) end;
  clear HR.

(* A register the head keeps: its symbolic value is its entry atom. *)
Ltac clo_keep EE :=
  cbn [sv_denot];
  lazymatch goal with |- context [ew ?Ex ?n] => rewrite (EE n (Z_to_bv 5 (Z.of_nat n)) eq_refl) end;
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned.

(* The registers every cut holds (close_regs_base), at the machine state of HS. *)
Ltac clo_base HS EE Usp E32 H10 :=
  unfold close_regs_base;
  split; [clo_rg HS ltac:(cbn [sv_denot]; rewrite Usp;
    lazymatch goal with |- _ = w64 ?z => transitivity (Z_to_bv 64 z) end;
    [f_equal; unfold CLOSE_FRAME; lia | reflexivity])|];
  split; [clo_rg HS ltac:(clo_keep EE; reflexivity)|];
  split; [clo_rg HS ltac:(clo_keep EE; reflexivity)|];
  split; [clo_rg HS ltac:(clo_keep EE; exact H10)|];
  split; [clo_rg HS ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)|];
  let q := fresh "q" in let Hq := fresh "Hq" in
  intros q Hq;
  assert (Hq' : q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia;
  clear Hq;
  repeat (destruct Hq' as [-> | Hq']; [clo_rg HS ltac:(clo_keep EE; reflexivity) |]);
  subst q;
  clo_rg HS ltac:(clo_keep EE; reflexivity).

(* ------------------------------------------------------------------ *)
(* 6. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Lemma close_head : @close_head_stmt fx rc B MT.
Proof.
unfold close_head_stmt. intros SEND JOIN.
unfold transport_diginet_session_close_cg_holds_stmt.
intros HCELLS HCC HRU HRE LAWS MTL HGX HSS HSC.
unfold transport_diginet_session_close_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw'
  HJ Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi Hnow Htw Hgf Hm HTF HROM HAP HTFG Hfly Hcmd Hcnt Hev.
assert (HLAWS : close_laws B MT) by exact (conj HCELLS (conj HCC (conj HRU (conj HRE (conj LAWS (conj MTL HGX)))))).
assert (HFIX : close_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw')
  by exact (conj HJ (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj Hsp16 (conj Hlo (conj Hhi
    (conj Hnow (conj Htw (conj Hgf (conj Hm (conj HTF (conj HROM (conj HAP (conj HTFG (conj Hfly (conj Hcmd
    (conj Hcnt Hev))))))))))))))))))))).
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof close_stk_val as (FS & _ & _ & FF).
assert (CS : CLOSE_S = 6157888) by reflexivity.
assert (EG : TB_g_s = 6157888) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hce : alloc_ceiling <= spZ regs - CLOSE_STK) by lia.
assert (Hwin : forall a, spZ regs - CLOSE_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
(* The valuation of the walk and its atoms. *)
set (E0 := clo_E regs Bw).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, clo_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros n r0 Hn; unfold E0, clo_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 4)%nat -> ew E0 (32 + j) = nth j (clo_vals_l Bw) (Z_to_bv 64 0))
  by (intros j Hj; unfold E0, clo_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth clo_vals_l] in E32, E33, E34, E35.
clear EX.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E0 10 = Z_to_bv 64 CLOSE_S) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (U10 : bv_unsigned (ew E0 10) = CLOSE_S) by (rewrite E10; apply unsigned_lit_small; lia).
destruct (clo_entry lyc Sc W regs memc mdc Bw HCELLS HCC HAR Htw
  ltac:(intros a Ha; apply Hpres0; unfold CLOSE_FRAME in Ha; lia) Hsp Hsp16 H10) as [HS SHOK].
fold E0 in HS, SHOK.
assert (KA : clo_KA W memc memc (clo_Zr (spZ regs))) by (split; [intros; reflexivity | intros a Ha; exact Ha]).
pose proof (@paj_run_x fx rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_close)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* The join cut, from any of the three paths on which close_go Bw is false: B1 = Bw and r = 0. *)
lazymatch goal with |- SRr _ _ _ ?Q =>
assert (JEND : forall (regsF : bvmap 5 word) (memF : word -> option byte) (mdF : Model),
  @W_journalG.ajournal_gx rc tfib_sink_head segs B G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memF mdF k ->
  clo_KA W memc memF (clo_Zr (spZ regs)) ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) memF) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) CLOSE_SAVED ->
  close_go Bw = false -> close_regs_join regs regsF 0 ->
  SRr segs W (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 (BASE + CLOSE_JOIN)) memF (YK11.seg_rom segs)) mdF) Q) end.
{ intros regsF memF mdF HJF KAF HSVF Hgo HRJ.
  assert (Er : 0 = r) by exact (close_r_eq timg_B TF Bw now Bw' Bw 0 r Hm (close_sent_nogo timg_B TF Bw Hgo)).
  apply (JOIN HLAWS HSS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' Bw
    lyc Sc W memF mdF 0 regsF HFIX).
  - refine (conj (clo_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TF Bw memF mdF
      LAWS MTL HAR Hwin Hce ltac:(lia) HJF KAF HSVF) (conj _ (conj (clo_tw W memc memF regs Bw ltac:(lia) Htw KAF) Hgf))).
    rewrite <- Er. exact (close_sent_nogo timg_B TF Bw Hgo).
  - rewrite <- Er. exact HRJ. }
(* run 1, +0x00 .. +0x48: the frame, the four saves, `beqz a0` and the alignment test of s (decided), s0 = s,
   s2 = the shadow base, the check of s + 116 (decided), a0 = S_desk_known, `beqz a0`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ clo_awr Usp U10. }
clo_after KA HS Usp U10.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* S_desk_known Bw = 0: close_go Bw is false, `li s1, 0` and the join cut *)
  rewrite (clo_br_eq E0 33 Bw TW.A_S_desk_known 0 E33 ltac:(lia)) in Hc.
  change (TW.s32_at Bw TW.A_S_desk_known) with (TW.S_desk_known Bw) in Hc.
  pose proof (clo_go_dk Bw Hc) as Hgo. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan CLOSE_JOIN.
  { clo_awr Usp U10. }
  clo_after KA HS Usp U10.
  clo_saved HS W regs Usp EE HSV.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_JOIN)) mm rom) mdx) Q) end.
  apply (JEND (ms_regs ms) (ms_mem ms) _ HJ KA HSV Hgo).
  split; [clo_base HS EE Usp E32 H10 | clo_rg HS ltac:(reflexivity)].
- (* S_desk_known Bw <> 0 *)
  rewrite (clo_br_eq E0 33 Bw TW.A_S_desk_known 0 E33 ltac:(lia)) in Hc.
  change (TW.s32_at Bw TW.A_S_desk_known) with (TW.S_desk_known Bw) in Hc. rename Hc into Hd1.
  (* run 2, +0x4c .. +0x64: the check of s + 136 (decided), a0 = S_foreign, `bnez a0`. *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { clo_awr Usp U10. }
  clo_after KA HS Usp U10.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* S_foreign Bw <> 0: close_go Bw is false, the join cut *)
    rewrite (clo_br_ne E0 34 Bw TW.A_S_foreign 0 E34 ltac:(lia)) in Hc. apply negb_true_iff in Hc.
    change (TW.s32_at Bw TW.A_S_foreign) with (TW.S_foreign Bw) in Hc.
    pose proof (clo_go_fo Bw Hc) as Hgo. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan CLOSE_JOIN.
    { clo_awr Usp U10. }
    clo_after KA HS Usp U10.
    clo_saved HS W regs Usp EE HSV.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_JOIN)) mm rom) mdx) Q) end.
    apply (JEND (ms_regs ms) (ms_mem ms) _ HJ KA HSV Hgo).
    split; [clo_base HS EE Usp E32 H10 | clo_rg HS ltac:(reflexivity)].
  + (* S_foreign Bw = 0 *)
    rewrite (clo_br_ne E0 34 Bw TW.A_S_foreign 0 E34 ltac:(lia)) in Hc. apply negb_false_iff in Hc.
    change (TW.s32_at Bw TW.A_S_foreign) with (TW.S_foreign Bw) in Hc. rename Hc into Hd2.
    (* run 3, +0x68 .. +0x84: the check of s + 112 (decided), a0 = S_state, a1 = 3, `bne a0, a1`. *)
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { clo_awr Usp U10. }
    clo_after KA HS Usp U10.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* S_state Bw <> S_CLOSED: close_go Bw holds, the send cut *)
      rewrite (clo_br_ne E0 35 Bw TW.A_S_state 3 E35 ltac:(lia)) in Hc. apply negb_true_iff in Hc.
      change (TW.s32_at Bw TW.A_S_state) with (TW.S_state Bw) in Hc.
      pose proof (clo_go_t Bw Hd1 Hd2 Hc) as Hgo. clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan CLOSE_SEND.
      { clo_awr Usp U10. }
      clo_after KA HS Usp U10.
      clo_saved HS W regs Usp EE HSV.
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_SEND)) mm rom) mdx) Q) end.
      apply (SEND HLAWS HSS HSC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw'
        (ms_mem ms) _ (ms_regs ms) HFIX).
      -- exact (conj (clo_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TF Bw (ms_mem ms) _
           LAWS MTL HAR Hwin Hce ltac:(lia) HJ KA HSV) (conj (clo_tw W memc (ms_mem ms) regs Bw ltac:(lia) Htw KA) Hgo)).
      -- clo_base HS EE Usp E32 H10.
    * (* S_state Bw = S_CLOSED: close_go Bw is false, `li s1, 0` and the join cut *)
      rewrite (clo_br_ne E0 35 Bw TW.A_S_state 3 E35 ltac:(lia)) in Hc. apply negb_false_iff in Hc.
      change (TW.s32_at Bw TW.A_S_state) with (TW.S_state Bw) in Hc.
      pose proof (clo_go_st Bw Hc) as Hgo. clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan CLOSE_JOIN.
      { clo_awr Usp U10. }
      clo_after KA HS Usp U10.
      clo_saved HS W regs Usp EE HSV.
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_JOIN)) mm rom) mdx) Q) end.
      apply (JEND (ms_regs ms) (ms_mem ms) _ HJ KA HSV Hgo).
      split; [clo_base HS EE Usp E32 H10 | clo_rg HS ltac:(reflexivity)].
Qed.

End head.
