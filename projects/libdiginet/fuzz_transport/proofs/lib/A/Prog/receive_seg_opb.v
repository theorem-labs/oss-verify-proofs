(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module names changed; 610 of its 692 lines of code are new or changed and 477 lines of the source are left out. *)
(* receive_seg_opb: Lemma recv_opb : recv_opb_stmt (lib/A/Prog/receive_seg_cut.v), the opb piece of the image-A ASan walk
   of receive (fuzz_transport.asan 0x837d0 = transport_sigma TS_receive, AF_receive = 0x256c of
   lib/A/Prog/DgnTransportList.v): op_begin (fuzz/fuzz_transport.c:388-394, TCb.v op_begin_m), from the opb cut
   RECV_OPB (+0x064, 0x83834) to the rf cut RECV_RF (+0x0ac, 0x8387c). The walk holds the caller's G journal
   (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 []) at k + 1 events; the runs are lib/A/Prog/TransportGRunA.v paj_run_x /
   paj_run_to_x, each from a state built at its first pc from the machine registers.
     run 1   +0x064 .. +0x074  no memory access: s4 = a0 = &OW (the PHi / PAddHi of object 12), a2 = 0x130, a1 = 0;
     +0x078                    `jal __asan_memset` (OW, 0, 304): TransportGCg.v gx_intrin_at at OSet. The destination
                               is OW's payload, bytes of G (TransportGRwA.v G_HARNESS_rw; transport_twr_ok_g_intro);
                               range_addressable from OW's zero shadow (receive_cg.v trans_recv_cells, read at each
                               granule by DgnTransportCg.v decode_zshadow_rd: ro_zra); shadow_hull_vis of the hull
                               [0x800b6608, 0x800b6638): g_rx_len's zero granule, three 0xf9 guard granules, OW's 38
                               zero granules, six 0xf9 guard granules (ro_hull_ow);
     run 2   +0x07c .. +0x088  a0 = &GOT (object 13), a2 = 0xe0, a1 = 0;
     +0x08c                    `jal __asan_memset` (GOT, 0, 224): the same way; the hull [0x800b4a58, 0x800b4a78) is four
                               0xf9 guard granules of g_s and GOT's 28 zero granules (ro_hull_got);
     run 3   +0x090 .. +0x0a8  a0 = -1, a1 = the 1-byte load of g_fail_next (object 24, region ro_gf, the byte of the
                               world: TWorldG.v tw_read_val), `sw a0, 0xe8(s4)` (OW.desk_off, region ro_dk), a0 = the
                               PHi of pair 82, a2 = 0x1e, `sw a1, -0x6b8(a0)` (M.fail at M + 88, region ro_mf), up to the
                               rf cut (`bltu s2, a2`).
   No instrumented check: each access is at a constant address of a global. The memory facts at the cut: what the call
   keeps (TransportGFrame.v dk_kept_step_gw over recv_wr bytes: each changed byte is in an ESTACK window below the
   frame, inside the call's window, or in OW, GOT or M.fail, which lie in G and in recv_wr bytes: ro_G_in), the seven
   saved words and the frame's bytes in the block (block bytes are not image bytes: YCbq.v blk_img), and the world
   relation at recv_w1 Bw (TWorldG.v tw_fill_set for the memsets, tw_write for the two stores in the model's order,
   desk_off then M.fail; ro_w1 states op_begin_m's world in that form). The registers at the cut: recv_regs_rf
   (the memsets keep the callee-saved registers, the runs keep every register they do not write, a2 = 30). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg m_rx_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import receive_cg receive_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* The return offsets of the two memset calls (+0x078, +0x08c). *)
Definition RO_C1 : Z := AF_receive + 0x7c.
Definition RO_C2 : Z := AF_receive + 0x90.
(* Runs 1 and 2 start from a state with no region (they access no memory). Run 3 starts at +0x090 with atoms 0 .. 31
   the registers, 32 the shadow base, 33 g_fail_next's byte; regions: g_fail_next (object 24, read only), OW.desk_off
   (based on s4 = &OW, atom 20) and M.fail (based on the PHi of pair 82, M + 88 + 1720). The facts pin the two bases
   of the writable regions (the run's shadow check asks each window's range). *)
Definition ro_ss_nil (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Definition ro_gf : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 24)) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SOff 33 0))].
Definition ro_dk : YP09.region := YP09.mkRegion (Some 20%nat) 232 236 232 236 [].
Definition ro_mf : YP09.region := YP09.mkRegion (Some (A_HI 82)) (-1720) (-1716) (-1720) (-1716) [].
Definition ro_facts3 : facts :=
  mkFacts [(20%nat, mkAF TA_OW TA_OW 5); (33%nat, mkAF 0 255 0); (A_HI 82, mkAF (TA_M + 1808) (TA_M + 1808) 0)] [] [].
Definition ro_ss3 : sstate := mkSS RO_C2 sr_atoms [ro_gf; ro_dk; ro_mf] None ro_facts3.

(* The registers the piece keeps: the callee-saved ones but s4. *)
Definition RO_KEEP : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27].
Lemma ro_keep_in : forall r, In r [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] -> In (Z_to_bv 5 r) RO_KEEP.
Proof. intros r Hr. unfold RO_KEEP. apply in_map. exact Hr. Qed.

(* The bytes of G the piece writes: OW's and GOT's payloads and M.fail. *)
Definition ro_G (a : Z) : Prop :=
  (TA_OW <= a < TA_OW + 304) \/ (TA_GOT <= a < TA_GOT + 224) \/ (TA_M + 88 <= a < TA_M + 92).
(* Every byte the piece may change: an ESTACK byte below sp1 = the entry sp - 64, or one of ro_G. *)
Definition ro_Z (sp1 a : Z) : Prop := (sp1 - ESTACK <= a < sp1) \/ ro_G a.

(* ------------------------------------------------------------------ *)
(* Model-side facts                                                    *)
(* ------------------------------------------------------------------ *)

(* M's, OW's and GOT's payloads are bytes of G. *)
Lemma ro_inG : forall a, (TA_M <= a < TA_M + TW.SZ_M) \/ (TA_OW <= a < TA_OW + TW.SZ_OW) \/
  (TA_GOT <= a < TA_GOT + TW.SZ_GOT) -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. destruct Ha as [Ha|[Ha|Ha]].
- exists (TA_M, TW.SZ_M). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_M) | unfold in_zr; cbn [fst snd]; lia].
- exists (TA_OW, TW.SZ_OW). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_OW) | unfold in_zr; cbn [fst snd]; lia].
- exists (TA_GOT, TW.SZ_GOT). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_GOT) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* The bytes of G the piece writes are bytes of G and of the written range. *)
Lemma ro_G_in : forall bytes a, ro_G a -> inG TG.G_HARNESS a /\ recv_wr bytes a.
Proof.
intros bytes a Ha. split.
- apply ro_inG. unfold ro_G, TA_M, TA_OW, TA_GOT, TW.SZ_M, TW.SZ_OW, TW.SZ_GOT in *. lia.
- unfold recv_wr, twa_fld. unfold ro_G in Ha. destruct Ha as [H|[H|H]].
  + left. unfold TW.SZ_OW. lia.
  + right; left. unfold TW.SZ_GOT. lia.
  + right; right; left. unfold TW.A_M_fail, TW.OFF_M. lia.
Qed.

(* A payload byte of the world table is a byte of G. *)
Lemma ro_tw_in_G : forall x, tw_in TMAP_A x -> inG TG.G_HARNESS x.
Proof.
intros x (o & b & n & Hin & Hx). unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* op_begin_m's world, in the form of the walk's world steps: the two memsets (tw_fill_set), the store of -1 at
   OW.desk_off and the store of g_fail_next at M.fail (tw_write). *)
Lemma ro_w1 : forall Bw, length Bw = Z.to_nat TW.W_LEN ->
  recv_w1 Bw =
  TW.upd (TW.upd (TW.upd (TW.upd Bw (TW.OFF_OW + 0) (repeat (Z_to_bv 8 0) (Z.to_nat TW.SZ_OW)))
    (TW.OFF_GOT + 0) (repeat (Z_to_bv 8 0) (Z.to_nat TW.SZ_GOT))) (TW.OFF_OW + 232) (TW.put 4 (-1)))
    (TW.OFF_M + 88) (TW.put 4 (TW.u_at Bw (TW.OFF_g_fail_next + 0) 1)).
Proof.
intros Bw HL.
assert (L0 : Z.of_nat (length Bw) = 65616) by (rewrite HL, Z2Nat.id by (unfold TW.W_LEN; lia); reflexivity).
unfold recv_w1, TC.op_begin_m. cbv beta iota zeta.
lazymatch goal with |- TW.set_M_fail ?X (TW.g_fail_next ?X) = _ =>
  assert (G : TW.g_fail_next X = TW.u_at Bw (TW.OFF_g_fail_next + 0) 1); [|rewrite G; reflexivity] end.
rewrite Z.add_0_r. unfold TW.g_fail_next, TW.set_OW_desk_off, TW.A_OW_desk_off.
lazymatch goal with |- TW.u_at (TW.upd (TW.upd (TW.upd Bw ?k1 ?v1) ?k2 ?v2) ?k3 ?v3) ?kk 1 = _ =>
  assert (L1 : Z.of_nat (length (TW.upd Bw k1 v1)) = 65616)
    by (rewrite TWL.length_upd; [exact L0 | unfold TW.OFF_OW; lia |
        rewrite L0, repeat_length; unfold TW.OFF_OW, TW.SZ_OW; lia]);
  assert (L2 : Z.of_nat (length (TW.upd (TW.upd Bw k1 v1) k2 v2)) = 65616)
    by (rewrite TWL.length_upd; [exact L1 | unfold TW.OFF_GOT; lia |
        rewrite L1, repeat_length; unfold TW.OFF_GOT, TW.SZ_GOT; lia]);
  rewrite (TWL.u_at_upd_out (TW.upd (TW.upd Bw k1 v1) k2 v2) v3 k3 kk 1)
    by (rewrite ?TWL.length_put, ?L2; unfold TW.OFF_OW, TW.OFF_g_fail_next; cbn [Z.of_nat]; lia);
  rewrite (TWL.u_at_upd_out (TW.upd Bw k1 v1) v2 k2 kk 1)
    by (rewrite ?repeat_length, ?L1; unfold TW.OFF_GOT, TW.SZ_GOT, TW.OFF_g_fail_next; cbn [Z.of_nat]; lia);
  rewrite (TWL.u_at_upd_out Bw v1 k1 kk 1)
    by (rewrite ?repeat_length, ?L0; unfold TW.OFF_OW, TW.SZ_OW, TW.OFF_g_fail_next; cbn [Z.of_nat]; lia)
end.
reflexivity.
Qed.

(* The bytes of a store of -1, as the run's chunk holds them (the literal 2 ^ 64 - 1). *)
Lemma ro_le_m1 : forall j, YO0f.le_byte 18446744073709551615 4 j = YO0f.le_byte (-1) 4 j.
Proof.
intros j. unfold YO0f.le_byte.
replace (18446744073709551615 mod 2 ^ (8 * Z.of_nat 4)) with (-1 mod 2 ^ (8 * Z.of_nat 4)) by reflexivity.
reflexivity.
Qed.

(* byte k of a value read modulo a larger power of two *)
Lemma ro_byte_mod : forall x N k, 0 <= k -> k + 8 <= N -> Z.shiftr (x mod 2 ^ N) k mod 256 = Z.shiftr x k mod 256.
Proof.
intros x N k Hk HkN. change 256 with (2 ^ 8). apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 8) as [H8|H8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The machine-side lemmas                                             *)
(* ------------------------------------------------------------------ *)

Section ro. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

Lemma ro_vals : VAL (A_OBJ 12) = TA_OW /\ VAL (A_OBJ 13) = TA_GOT /\ VAL (A_OBJ 24) = TA_g_fail_next /\
  VAL (A_HI 82) = TA_M + 1808.
Proof. vm_compute. repeat split. Qed.

(* The valuations of the runs: the registers at the run's first pc, the shadow base, and for run 3 g_fail_next's
   byte. *)
Definition ro_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF]).
Definition ro_E3 (regs : bvmap 5 word) (gf : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 gf]).

Lemma ro_agree : forall regs extra, env_agree 32 (Ereg regs extra) (Eimg (PI := PI_transport) (Ereg regs extra)).
Proof. intros regs extra. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* A state with no region, at any pc. *)
Lemma ro_entry_nil : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (ro_E regs) (ro_ss_nil pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx. unfold ro_ss_nil.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The state of run 3 at +0x090. *)
Lemma ro_entry3 : forall (W : world segs) regs mem gf,
  YK11.getr regs 20 = w64 TA_OW -> 0 <= gf < 256 ->
  val_mem segs (mrestrict (w_H W) mem) TA_g_fail_next 1 gf ->
  st_ok_pi segs VAL (ro_E3 regs gf) ro_ss3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + RO_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem gf R20 Hgf Vgf.
  destruct ro_vals as (V12 & V13 & V24 & V82).
  set (E := ro_E3 regs gf).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, ro_E3; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (E33 : ew E 33 = Z_to_bv 64 gf)
    by (unfold E, ro_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (U20 : bv_unsigned (ew E 20) = TA_OW)
    by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; unfold TA_OW; lia).
  assert (U24 : bv_unsigned (ew E (A_OBJ 24)) = TA_g_fail_next).
  { unfold E, ro_E3. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V24.
    apply unsigned_lit_small. unfold TA_g_fail_next. lia. }
  assert (U82 : bv_unsigned (ew E (A_HI 82)) = TA_M + 1808).
  { unfold E, ro_E3. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia). rewrite V82.
    apply unsigned_lit_small. unfold TA_M. lia. }
  assert (U33 : bv_unsigned (ew E 33) = gf) by (rewrite E33; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold ro_ss3.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [ro_gf ro_dk ro_mf YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U24. split; [unfold TA_g_fail_next; lia|]. split; [unfold TA_g_fail_next; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ TA_g_fail_next 0 1 (SOff 33 0) gf).
      * cbn [sv_denot]. rewrite E33, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
      * change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      * lia.
      * rewrite Z.add_0_r. exact Vgf.
    + rewrite U20. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
      apply ro_inG. unfold TW.SZ_OW. lia.
    + rewrite U82. split; [unfold TA_M; lia|]. split; [unfold TA_M; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + 1808 + o) G_HARNESS_rw).
      apply ro_inG. unfold TW.SZ_M. lia.
  - apply pairwise_disjoint_of_extents.
    unfold ro_gf, ro_dk, ro_mf, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U20, U24, U82. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold TA_OW, TA_M, TA_g_fail_next. repeat split; first [exact I | lia].
  - unfold ro_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U33, U82. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | unfold TA_OW; reflexivity].
Qed.

(* A zero shadow row of the record makes every byte of an 8-aligned sub-range addressable, at every AR state. *)
Lemma ro_zra : forall ly S (W : world segs) mem md lo hi q n,
  @AR rc segs B ly S W mem md -> decode_zshadow_at B lo hi -> lo mod 8 = 0 -> hi mod 8 = 0 ->
  lo <= q -> q + n <= hi ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q n.
Proof.
intros ly S W mem md lo hi q n HAR HZ Hlo Hhi Hq Hqn x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod lo 8 ltac:(lia)) as Dl. pose proof (Z.div_mod hi 8 ltac:(lia)) as Dh.
replace (shadow_of_addr SHADOW_OFF x) with (FCells.shadow_addr (x / 8 * 8))
  by (unfold shadow_of_addr, FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF; rewrite Z.div_mul by lia; lia).
apply (decode_zshadow_rd B ly S W mem md lo hi); [exact HAR | apply Z_mod_mult | lia | lia | exact HZ].
Qed.

(* A shadow byte of a granule of a zero shadow row is visible. *)
Lemma ro_zs : forall ly S (W : world segs) mem md lo hi s,
  @AR rc segs B ly S W mem md -> decode_zshadow_at B lo hi ->
  lo <= (s - SHADOW_OFF) * 8 -> (s - SHADOW_OFF) * 8 + 8 <= hi ->
  aview segs (w_H W) mem s <> None.
Proof.
intros ly S W mem md lo hi s HAR HZ H1 H2.
assert (ES : FCells.shadow_addr ((s - SHADOW_OFF) * 8) = s)
  by (unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF; rewrite Z.div_mul by lia; lia).
rewrite <- ES. rewrite (decode_zshadow_rd B ly S W mem md lo hi _ HAR (Z_mod_mult _ _) H1 H2 HZ). discriminate.
Qed.

(* A constant 1-byte cell of the record is visible at every AR state. *)
Lemma ro_cell : forall ly S (W : world segs) mem md x v s,
  @AR rc segs B ly S W mem md -> In (z1 (ANum x) v) (as_const B ly) -> x = s -> aview segs (w_H W) mem s <> None.
Proof.
intros ly S W mem md x v s HAR HC <-. destruct HAR as (Mm & _).
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mm) _ HC) as Hh.
unfold cell_holds in Hh. cbn [c_at c_w YG0f.c_val z1 c1 aeval] in Hh.
specialize (Hh 0%nat ltac:(lia)). cbn [Z.of_nat] in Hh. rewrite Z.add_0_r in Hh. rewrite Hh. discriminate.
Qed.

(* The shadow hull of OW's memset: g_rx_len's zero granule, three guard cells, OW's zero granules, six guard cells. *)
Lemma ro_hull_ow : forall ly S (W : world segs) mem md,
  trans_recv_cells B -> @AR rc segs B ly S W mem md -> shadow_hull_vis (aview segs (w_H W) mem) TA_OW 304.
Proof.
intros ly S W mem md (HZO & HZG & HZR & HC) HAR s Hs.
assert (B1 : shadow_addr TA_OW / 8 * 8 = 0x800b6608) by reflexivity.
assert (B2 : shadow_addr (TA_OW + 304 - 1) / 8 * 8 + 8 = 0x800b6638) by reflexivity.
rewrite B1, B2 in Hs.
destruct (HC ly) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & _).
assert (Hc : s = 0x800b6608 \/ (0x800b6609 <= s < 0x800b660c) \/ (0x800b660c <= s < 0x800b6632) \/
  (0x800b6632 <= s < 0x800b6638)) by lia.
destruct Hc as [Hc|[Hc|[Hc|Hc]]].
- apply (ro_zs ly S W mem md TA_g_rx_len (TA_g_rx_len + TW.SZ_g_rx_len) s HAR HZR);
    unfold SHADOW_OFF, TA_g_rx_len, TW.SZ_g_rx_len; lia.
- assert (s = 0x800b6609 \/ s = 0x800b660a \/ s = 0x800b660b) as [ -> | [ -> | -> ] ] by lia.
  + exact (ro_cell ly S W mem md _ _ _ HAR K1 eq_refl).
  + exact (ro_cell ly S W mem md _ _ _ HAR K2 eq_refl).
  + exact (ro_cell ly S W mem md _ _ _ HAR K3 eq_refl).
- apply (ro_zs ly S W mem md TA_OW (TA_OW + TW.SZ_OW) s HAR HZO); unfold SHADOW_OFF, TA_OW, TW.SZ_OW; lia.
- assert (s = 0x800b6632 \/ s = 0x800b6633 \/ s = 0x800b6634 \/ s = 0x800b6635 \/ s = 0x800b6636 \/ s = 0x800b6637)
    as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] by lia.
  + exact (ro_cell ly S W mem md _ _ _ HAR K4 eq_refl).
  + exact (ro_cell ly S W mem md _ _ _ HAR K5 eq_refl).
  + exact (ro_cell ly S W mem md _ _ _ HAR K6 eq_refl).
  + exact (ro_cell ly S W mem md _ _ _ HAR K7 eq_refl).
  + exact (ro_cell ly S W mem md _ _ _ HAR K8 eq_refl).
  + exact (ro_cell ly S W mem md _ _ _ HAR K9 eq_refl).
Qed.

(* The shadow hull of GOT's memset: four guard cells of g_s, GOT's zero granules. *)
Lemma ro_hull_got : forall ly S (W : world segs) mem md,
  trans_recv_cells B -> @AR rc segs B ly S W mem md -> shadow_hull_vis (aview segs (w_H W) mem) TA_GOT 224.
Proof.
intros ly S W mem md (HZO & HZG & HZR & HC) HAR s Hs.
assert (B1 : shadow_addr TA_GOT / 8 * 8 = 0x800b4a58) by reflexivity.
assert (B2 : shadow_addr (TA_GOT + 224 - 1) / 8 * 8 + 8 = 0x800b4a78) by reflexivity.
rewrite B1, B2 in Hs.
destruct (HC ly) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & K11 & K12 & K13).
assert (Hc : (0x800b4a58 <= s < 0x800b4a5c) \/ (0x800b4a5c <= s < 0x800b4a78)) by lia.
destruct Hc as [Hc|Hc].
- assert (s = 0x800b4a58 \/ s = 0x800b4a59 \/ s = 0x800b4a5a \/ s = 0x800b4a5b) as [ -> | [ -> | [ -> | -> ] ] ] by lia.
  + exact (ro_cell ly S W mem md _ _ _ HAR K10 eq_refl).
  + exact (ro_cell ly S W mem md _ _ _ HAR K11 eq_refl).
  + exact (ro_cell ly S W mem md _ _ _ HAR K12 eq_refl).
  + exact (ro_cell ly S W mem md _ _ _ HAR K13 eq_refl).
- apply (ro_zs ly S W mem md TA_GOT (TA_GOT + TW.SZ_GOT) s HAR HZG); unfold SHADOW_OFF, TA_GOT, TW.SZ_GOT; lia.
Qed.

(* A chunk of a region, read byte by byte through the view. *)
Lemma ro_field : forall E H (m : word -> option byte) n bb cs lo hi wlo whi od (w : N) e x,
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
rewrite (ro_byte_mod x 64 (8 * Z.of_nat j)) by lia.
rewrite (ro_byte_mod x (8 * Z.of_nat (N.to_nat w)) (8 * Z.of_nat j)) by lia.
reflexivity.
Qed.

(* The values of run 3's atoms, at the numerals of the computed state. *)
Lemma ro_E3_vals : forall regs gf, YK11.getr regs 20 = w64 TA_OW -> 0 <= gf < 256 ->
  bv_unsigned (ew (ro_E3 regs gf) 20) = TA_OW /\ bv_unsigned (ew (ro_E3 regs gf) 265) = TA_g_fail_next /\
  bv_unsigned (ew (ro_E3 regs gf) 482) = TA_M + 1808 /\ ew (ro_E3 regs gf) 33 = Z_to_bv 64 gf.
Proof.
intros regs gf R20 Hgf. destruct ro_vals as (_ & _ & V24 & V82).
split; [|split; [|split]].
- unfold ro_E3. rewrite (ew_Eimg_Ereg_nat regs _ 20 20%bv eq_refl), R20. apply unsigned_lit_small.
  unfold TA_OW. lia.
- unfold ro_E3. rewrite (Eimg_img _ 265%nat) by (unfold A_TEXT, A_LIM; lia). change 265%nat with (A_OBJ 24).
  rewrite V24. apply unsigned_lit_small. unfold TA_g_fail_next. lia.
- unfold ro_E3. rewrite (Eimg_img _ 482%nat) by (unfold A_TEXT, A_LIM; lia). change 482%nat with (A_HI 82).
  rewrite V82. apply unsigned_lit_small. unfold TA_M. lia.
- unfold ro_E3. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1).
Qed.

(* garr8 at a memory whose view keeps the bytes. *)
Lemma ro_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) base l,
  garr8 segs (mrestrict H m) base l ->
  (forall a, base <= a < base + Z.of_nat (length l) -> aview segs H m' a = aview segs H m a) ->
  garr8 segs (mrestrict H m') base l.
Proof.
intros H m m' base l HG K j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept segs H H m m' (base + Z.of_nat j) 1 _); [|exact Hv].
intros kk Hk. apply K. lia.
Qed.

End ro.

(* ------------------------------------------------------------------ *)
(* Tactics                                                             *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ro_reg HS r v H tac :=
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
(* A run with no writable region. *)
Ltac ro_awr0 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.
(* Membership in a short literal list. *)
Ltac ro_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* ------------------------------------------------------------------ *)
(* The opb piece                                                       *)
(* ------------------------------------------------------------------ *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

Lemma recv_opb : @recv_opb_stmt fx rc B MT.
Proof.
unfold recv_opb_stmt. intros RF.
unfold recv_opb_at. intros HLAWS HCALLS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw' ly2 S2 W2 mem2 md2
  regs2 HFIX HCUR HRES HBLK HTW HREGS.
pose proof HLAWS as (HMPC & HFPC & HCELLS & HRC & HGU & HGE & HRU & HRE & LAWS & MTL & HGX & HGNE).
pose proof HCALLS as (AM & MCPY & MSET & _).
pose proof HFIX as (HJe & Hret & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hch & Hal & Hwlo & Hwhi & _).
pose proof HCUR as (HJ & Hfr & Hperm & HMO & HK & HSV & H4096).
pose proof HREGS as ((Q2 & Q3 & Q4 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27) & Q8 & Q9 & Q18 & Q19 & Q21).
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJe) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
destruct ro_vals as (V12 & V13 & V24 & V82).
assert (CO : TA_OW = 6238304) by reflexivity.
assert (CG : TA_GOT = 6181600) by reflexivity.
assert (CM : TA_M = 6156640) by reflexivity.
assert (CF : TA_g_fail_next = 6156576) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (RSTK : RECV_STK = 16448) by reflexivity.
assert (RFR : RECV_FRAME = 64) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
set (sp1 := spZ regs - 64).
assert (Hm16 : (sp1 - sp0) mod 16 = 0).
{ unfold sp1. replace (spZ regs - 64 - sp0) with (spZ regs - sp0 + (-4) * 16) by lia.
  rewrite Z_mod_plus_full, Zminus_mod, Hal, Hsp0a. reflexivity. }
assert (USP : bv_unsigned (YK11.getr regs2 2) = sp1)
  by (rewrite Q2, RFR; apply unsigned_lit_small; unfold sp1; lia).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
(* ---- run 1, +0x064 .. +0x078: s4 = a0 = &OW, a2 = 304, a1 = 0, `jal __asan_memset` ---- *)
pose proof (ro_entry_nil W2 regs2 mem2 RECV_OPB) as HS.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (ro_E regs2) (mrestrict (w_H W2) mem2)) by constructor.
assert (HEI : img_env VAL A_LIM (ro_E regs2)) by (unfold ro_E; apply Eimg_env).
pose proof HJ as HJ0.
paj_run_tok RUN HS HJ0 SHOK YC4b.Bspan.
{ ro_awr0. }
rename HF into HF1, HFr into HFr1, HG into HG1.
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
rename HJ0 into HJ1.
assert (K1 : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms1) x = aview segs (w_H W2) mem2 x).
{ intros x Hx. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr1); [| exact Hx | intros []].
  intros b wlo whi y Hin. cbn in Hin. destruct Hin. }
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ro_E regs2) n = YK11.getr regs2 r)
  by (intros n r Hn; unfold ro_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (AP1 : forall r, In r RO_KEEP -> YK11.getr (ms_regs ms1) r = YK11.getr regs2 r).
{ apply (regs_kept_of_st_ok segs _ _ (restrict (w_H W2) ms1) regs2 [w64 SHADOW_OFF] RO_KEEP HS (ro_agree _ _)).
  vm_compute. reflexivity. }
pmkst HS.
ro_reg HS (Z_to_bv 5 10) (w64 TA_OW) Ra10
  ltac:(cbn [sv_denot]; unfold ro_E; rewrite (Eimg_img _ 253%nat) by (unfold A_TEXT, A_LIM; lia);
        change 253%nat with (A_OBJ 12); rewrite V12, unsigned_lit_small, Z.add_0_r by (unfold TA_OW; lia);
        reflexivity).
ro_reg HS (Z_to_bv 5 20) (w64 TA_OW) Ra20
  ltac:(cbn [sv_denot]; unfold ro_E; rewrite (Eimg_img _ 253%nat) by (unfold A_TEXT, A_LIM; lia);
        change 253%nat with (A_OBJ 12); rewrite V12, unsigned_lit_small, Z.add_0_r by (unfold TA_OW; lia);
        reflexivity).
ro_reg HS (Z_to_bv 5 11) (w64 0) Ra11 ltac:(reflexivity).
ro_reg HS (Z_to_bv 5 12) (w64 304) Ra12 ltac:(reflexivity).
ro_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + RO_C1)) Ra1 ltac:(apply codeptr_val; exact HEI).
assert (Ra2 : YK11.getr (ms_regs ms1) 2 = YK11.getr regs2 2)
  by exact (AP1 (Z_to_bv 5 2) (ro_keep_in 2 ltac:(ro_in))).
assert (Ra3 : YK11.getr (ms_regs ms1) 3 = w64 (as_gp B))
  by exact (eq_trans (AP1 (Z_to_bv 5 3) (ro_keep_in 3 ltac:(ro_in))) (eq_trans Q3 Hgp)).
assert (Ra4 : YK11.getr (ms_regs ms1) 4 = w64 (as_tp B))
  by exact (eq_trans (AP1 (Z_to_bv 5 4) (ro_keep_in 4 ltac:(ro_in))) (eq_trans Q4 Htp)).
assert (Hsp1 : spZ (ms_regs ms1) = sp1) by (unfold spZ at 1; rewrite Ra2; exact USP).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
(* ---- +0x078: __asan_memset (OW, 0, 304) ---- *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    (MSET fx) TG.G_HARNESS W2 (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly S W0 mem0 md0 own ly2 S2 md1
    (k + 1) TA_OW 0 304 (sp1 - sp0) (Z_to_bv 64 (BASE + RO_C1)) HGX G_HARNESS_rw HJ1 Ra10 Ra11 Ra12).
  - lia.
  - rewrite CO. lia.
  - rewrite CO. lia.
  - rewrite Hsp1. lia.
  - exact Hm16.
  - unfold sp1. lia.
  - rewrite EST. unfold sp1. lia.
  - exact Ra3.
  - exact Ra4.
  - exact Ra1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold RO_C1, AF_receive; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ1|]. intros x Hx. right. apply ro_inG.
    unfold TW.SZ_OW. lia.
  - left. unfold kLowMemEnd. rewrite CO. lia.
  - apply (ro_zra B _ _ _ _ _ TA_OW (TA_OW + TW.SZ_OW) TA_OW 304 HAR1 (proj1 HRC));
      unfold TA_OW, TW.SZ_OW; first [reflexivity | lia].
  - intros _. exact (ro_hull_ow B _ _ _ _ _ HRC HAR1).
  - exact I. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hset3 & Heff3 & Hgr3).
assert (K3 : forall x, 0 <= x < 2 ^ 64 -> ~ (TA_OW <= x < TA_OW + 304) -> ~ (sp1 - ESTACK <= x < sp1) ->
  aview segs (w_H W2) mem3 x = aview segs (w_H W2) mem2 x).
{ intros x Hx N1 N2. rewrite (Heff3 x Hx N1 ltac:(lia)). exact (K1 x Hx). }
clear HS SHOK HEI.
(* ---- run 2, +0x07c .. +0x08c: a0 = &GOT, a2 = 224, a1 = 0, `jal __asan_memset` ---- *)
pose proof (ro_entry_nil W2 regs3 mem3 RO_C1) as HS.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (ro_E regs3) (mrestrict (w_H W2) mem3)) by constructor.
assert (HEI : img_env VAL A_LIM (ro_E regs3)) by (unfold ro_E; apply Eimg_env).
paj_run_tok RUN HS HJ3 SHOK YC4b.Bspan.
{ ro_awr0. }
rename HF into HF2, HFr into HFr2, HG into HG2.
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
lazymatch type of HS with context [restrict _ ?m] => rename m into ms2 end.
assert (K2 : forall x, 0 <= x < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms2) x = aview segs (w_H W2) mem3 x).
{ intros x Hx. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr2); [| exact Hx | intros []].
  intros b wlo whi y Hin. cbn in Hin. destruct Hin. }
assert (AP2 : aregs_preserved regs3 (ms_regs ms2)).
{ apply (aregs_preserved_of_st_ok segs (w_H W2) _ _ ms2 regs3 [w64 SHADOW_OFF] HS (ro_agree _ _)).
  vm_compute. reflexivity. }
assert (CH2 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] ->
  YK11.getr (ms_regs ms2) (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)).
{ intros r Hr. rewrite (AP2 r ltac:(unfold acallee_saved; cbn in Hr; lia)).
  rewrite (HP3 r ltac:(unfold acallee_saved; cbn in Hr; lia)). exact (AP1 _ (ro_keep_in r Hr)). }
pmkst HS.
ro_reg HS (Z_to_bv 5 10) (w64 TA_GOT) Rb10
  ltac:(cbn [sv_denot]; unfold ro_E; rewrite (Eimg_img _ 254%nat) by (unfold A_TEXT, A_LIM; lia);
        change 254%nat with (A_OBJ 13); rewrite V13, unsigned_lit_small, Z.add_0_r by (unfold TA_GOT; lia);
        reflexivity).
ro_reg HS (Z_to_bv 5 11) (w64 0) Rb11 ltac:(reflexivity).
ro_reg HS (Z_to_bv 5 12) (w64 224) Rb12 ltac:(reflexivity).
ro_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + RO_C2)) Rb1 ltac:(apply codeptr_val; exact HEI).
assert (Rb2 : YK11.getr (ms_regs ms2) 2 = YK11.getr regs2 2) by exact (CH2 2 ltac:(ro_in)).
assert (Rb3 : YK11.getr (ms_regs ms2) 3 = w64 (as_gp B)) by exact (eq_trans (CH2 3 ltac:(ro_in)) (eq_trans Q3 Hgp)).
assert (Rb4 : YK11.getr (ms_regs ms2) 4 = w64 (as_tp B)) by exact (eq_trans (CH2 4 ltac:(ro_in)) (eq_trans Q4 Htp)).
assert (Hsp2 : spZ (ms_regs ms2) = sp1) by (unfold spZ at 1; rewrite Rb2; exact USP).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
(* ---- +0x08c: __asan_memset (GOT, 0, 224) ---- *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    (MSET fx) TG.G_HARNESS W2 (ms_regs ms2) (ms_mem ms2) STK sp0 FP ly S W0 mem0 md0 own ly2 S2 md4
    (k + 1) TA_GOT 0 224 (sp1 - sp0) (Z_to_bv 64 (BASE + RO_C2)) HGX G_HARNESS_rw HJ3 Rb10 Rb11 Rb12).
  - lia.
  - rewrite CG. lia.
  - rewrite CG. lia.
  - rewrite Hsp2. lia.
  - exact Hm16.
  - unfold sp1. lia.
  - rewrite EST. unfold sp1. lia.
  - exact Rb3.
  - exact Rb4.
  - exact Rb1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold RO_C2, AF_receive; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ3|]. intros x Hx. right. apply ro_inG.
    unfold TW.SZ_GOT. lia.
  - left. unfold kLowMemEnd. rewrite CG. lia.
  - apply (ro_zra B _ _ _ _ _ TA_GOT (TA_GOT + TW.SZ_GOT) TA_GOT 224 HAR3 (proj1 (proj2 HRC)));
      unfold TA_GOT, TW.SZ_GOT; first [reflexivity | lia].
  - intros _. exact (ro_hull_got B _ _ _ _ _ HRC HAR3).
  - exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md5 & -> & HJ4 & HP4 & _ & Hset4 & Heff4 & Hgr4).
assert (K4 : forall x, 0 <= x < 2 ^ 64 -> ~ (TA_OW <= x < TA_OW + 304) -> ~ (TA_GOT <= x < TA_GOT + 224) ->
  ~ (sp1 - ESTACK <= x < sp1) -> aview segs (w_H W2) mem4 x = aview segs (w_H W2) mem2 x).
{ intros x Hx N1 N2 N3. rewrite (Heff4 x Hx N2 ltac:(lia)), (K2 x Hx). exact (K3 x Hx N1 N3). }
assert (CH4 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] ->
  YK11.getr regs4 (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP4 r ltac:(unfold acallee_saved; cbn in Hr; lia)). exact (CH2 r Hr). }
clear HS SHOK HEI.
(* ---- run 3, +0x090 .. +0x0a8: the load of g_fail_next, the stores at OW.desk_off and M.fail ---- *)
assert (HLB : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ HTW).
set (GF := TW.u_at Bw (TW.OFF_g_fail_next + 0) 1).
assert (RGF : 0 <= GF < 256) by (pose proof (TWL.u_at_range Bw (TW.OFF_g_fail_next + 0) 1) as R; exact R).
assert (VGF2 : val_mem segs (mrestrict (w_H W2) mem2) (TA_g_fail_next + 0) 1 GF)
  by exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_fail_next TA_g_fail_next 1 0 1 TMAP_A_ok HTW TMAP_A_g_fail_next
              ltac:(lia) ltac:(cbn [Z.of_nat]; lia)).
rewrite Z.add_0_r in VGF2.
assert (VGF4 : val_mem segs (mrestrict (w_H W2) mem4) TA_g_fail_next 1 GF).
{ apply (val_mem_kept segs (w_H W2) (w_H W2) mem2 mem4 TA_g_fail_next 1 GF); [|exact VGF2].
  intros kk Hk. cbn [Z.of_nat] in Hk. apply K4; rewrite ?CF, ?CO, ?CG; unfold sp1 in *; lia. }
assert (H20 : acallee_saved 20) by (unfold acallee_saved; lia).
assert (R20 : YK11.getr regs4 20 = w64 TA_OW)
  by exact (eq_trans (HP4 20 H20) (eq_trans (AP2 20 H20) (eq_trans (HP3 20 H20) Ra20))).
(* ---- run 3, +0x090 .. +0x0ac: a0 = -1, the load of g_fail_next, the stores at OW.desk_off and M.fail ---- *)
pose proof (ro_entry3 W2 regs4 mem4 GF R20 RGF VGF4) as HS.
destruct (ro_E3_vals regs4 GF R20 RGF) as (U20 & U265 & U482 & E33).
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (ro_E3 regs4 GF) (mrestrict (w_H W2) mem4)) by constructor.
assert (HEI : img_env VAL A_LIM (ro_E3 regs4 GF)) by (unfold ro_E3; apply Eimg_env).
paj_run_to_tok RUNTO HS HJ4 SHOK YC4b.Bspan RECV_RF.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia|].
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U20 in Hx;
    apply ro_inG; unfold TW.SZ_OW; lia|].
  apply awr_ok_x_cons_g; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U482 in Hx;
    apply ro_inG; unfold TW.SZ_M; lia|].
  apply awr_ok_x_nil. }
rename HF into HF3, HFr into HFr3, HG into HG3.
set (mdF := with_vm_backing (m_vm_lazy md5) mat md5) in *. clearbody mdF. clear mat.
lazymatch type of HS with context [restrict _ ?m] => rename m into msF end.
assert (K5 : forall x, 0 <= x < 2 ^ 64 -> ~ (TA_OW + 232 <= x < TA_OW + 236) -> ~ (TA_M + 88 <= x < TA_M + 92) ->
  aview segs (w_H W2) (ms_mem msF) x = aview segs (w_H W2) mem4 x).
{ intros x Hx N1 N2.
  apply (kept_of_frame _ _ _ _ _ (fun y => (TA_OW + 232 <= y < TA_OW + 236) \/ (TA_M + 88 <= y < TA_M + 92)) HFr3);
    [| exact Hx | intros [X|X]; [exact (N1 X) | exact (N2 X)]].
  intros b wlo whi y Hin Hy. cbv beta.
  lazymatch type of Hin with In ?z ?l => let l' := eval vm_compute in l in change (In z l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin];
    [injection Hin as <- <- <-; cbn [base_val] in Hy; rewrite ?U20, ?U265, ?U482 in Hy;
     first [lia | left; lia | right; lia] |]).
  destruct Hin. }
(* the registers at the rf cut *)
assert (AP3 : aregs_preserved regs4 (ms_regs msF)).
{ apply (aregs_preserved_of_st_ok segs (w_H W2) _ _ msF regs4 [w64 SHADOW_OFF; Z_to_bv 64 GF] HS (ro_agree _ _)).
  vm_compute. reflexivity. }
ro_reg HS (Z_to_bv 5 12) (w64 30) Y12 ltac:(reflexivity).
assert (CHF : forall r, In r [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] ->
  YK11.getr (ms_regs msF) (Z_to_bv 5 r) = YK11.getr regs2 (Z_to_bv 5 r)).
{ intros r Hr. rewrite (AP3 r ltac:(unfold acallee_saved; cbn in Hr; lia)). exact (CH4 r Hr). }
assert (REGF : recv_regs_rf regs (ms_regs msF) by_poll a bytes).
{ unfold recv_regs_rf, recv_regs_opb, recv_regs_keep.
  refine (conj (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))
    (conj _ (conj _ (conj _ (conj _ _))))) Y12).
  - exact (eq_trans (CHF 2 ltac:(ro_in)) Q2).
  - exact (eq_trans (CHF 3 ltac:(ro_in)) Q3).
  - exact (eq_trans (CHF 4 ltac:(ro_in)) Q4).
  - exact (eq_trans (CHF 22 ltac:(ro_in)) Q22).
  - exact (eq_trans (CHF 23 ltac:(ro_in)) Q23).
  - exact (eq_trans (CHF 24 ltac:(ro_in)) Q24).
  - exact (eq_trans (CHF 25 ltac:(ro_in)) Q25).
  - exact (eq_trans (CHF 26 ltac:(ro_in)) Q26).
  - exact (eq_trans (CHF 27 ltac:(ro_in)) Q27).
  - exact (eq_trans (CHF 8 ltac:(ro_in)) Q8).
  - exact (eq_trans (CHF 9 ltac:(ro_in)) Q9).
  - exact (eq_trans (CHF 18 ltac:(ro_in)) Q18).
  - exact (eq_trans (CHF 19 ltac:(ro_in)) Q19).
  - exact (eq_trans (CHF 21 ltac:(ro_in)) Q21). }
(* run 3's two stores, read from its regions *)
pose proof (st_ok_pi_region_nth (ro_E3 regs4 GF) _ (restrict (w_H W2) msF) 1 _ HS eq_refl) as RG1.
cbn [ms_mem restrict] in RG1.
pose proof (st_ok_pi_region_nth (ro_E3 regs4 GF) _ (restrict (w_H W2) msF) 2 _ HS eq_refl) as RG2.
cbn [ms_mem restrict] in RG2.
assert (D33 : sv_denot (ro_E3 regs4 GF) (SOff 33 0) = Z_to_bv 64 GF)
  by (cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
pose proof (ro_field _ _ _ _ _ _ _ _ _ _ 232 4 (SLit 18446744073709551615) 18446744073709551615 RG1 U20
  ltac:(cbn [In]; left; reflexivity) eq_refl ltac:(cbn; lia)) as VDK.
pose proof (ro_field _ _ _ _ _ _ _ _ _ _ (-1720) 4 (SOff 33 0) GF RG2 U482
  ltac:(cbn [In]; left; reflexivity) D33 ltac:(cbn; lia)) as VMF.
clear RG1 RG2.
(* every byte outside ro_Z is the one at the opb cut *)
assert (KALL : forall x, 0 <= x < 2 ^ 64 -> ~ ro_Z sp1 x ->
  aview segs (w_H W2) (ms_mem msF) x = aview segs (w_H W2) mem2 x).
{ intros x Hx Hn. unfold ro_Z, ro_G in Hn.
  rewrite (K5 x Hx ltac:(lia) ltac:(lia)). apply K4; [exact Hx | lia | lia | lia]. }
assert (GR : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) (ms_mem msF) x).
{ intros x Hx. apply (apresent_grows _ _ _ x HG3). apply Hgr4. apply (apresent_grows _ _ _ x HG2). apply Hgr3.
  exact (apresent_grows _ _ _ x HG1 Hx). }
(* the world relation at recv_w1 Bw *)
assert (T1 : tw_at TMAP_A (aview segs (w_H W2) mem3)
  (TW.upd Bw (TW.OFF_OW + 0) (repeat (Z_to_bv 8 0) (Z.to_nat TW.SZ_OW)))).
{ apply (tw_fill_set TMAP_A (aview segs (w_H W2) mem2) _ Bw TW.OFF_OW TA_OW TW.SZ_OW 0 0 TW.SZ_OW TMAP_A_ok HTW
    TMAP_A_OW).
  - lia.
  - unfold TW.SZ_OW. lia.
  - lia.
  - intros i Hi. rewrite Z.add_0_r. exact (Hset3 i ltac:(unfold TW.SZ_OW in Hi; lia)).
  - intros x Hx Hn. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS x HGX (ro_tw_in_G x Hx)) as Hl.
    apply K3; [lia | unfold TW.SZ_OW in Hn; lia | unfold sp1; lia]. }
lazymatch type of T1 with tw_at _ _ ?X1 =>
  assert (T2 : tw_at TMAP_A (aview segs (w_H W2) mem4)
    (TW.upd X1 (TW.OFF_GOT + 0) (repeat (Z_to_bv 8 0) (Z.to_nat TW.SZ_GOT)))) end.
{ apply (tw_fill_set TMAP_A (aview segs (w_H W2) mem3) _ _ TW.OFF_GOT TA_GOT TW.SZ_GOT 0 0 TW.SZ_GOT TMAP_A_ok T1
    TMAP_A_GOT).
  - lia.
  - unfold TW.SZ_GOT. lia.
  - lia.
  - intros i Hi. rewrite Z.add_0_r. exact (Hset4 i ltac:(unfold TW.SZ_GOT in Hi; lia)).
  - intros x Hx Hn. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS x HGX (ro_tw_in_G x Hx)) as Hl.
    rewrite (Heff4 x ltac:(lia) ltac:(unfold TW.SZ_GOT in Hn; lia) ltac:(unfold sp1; lia)).
    exact (K2 x ltac:(lia)). }
set (rdm := fun x => if ((TA_M + 88 <=? x) && (x <? TA_M + 92))%bool then aview segs (w_H W2) mem4 x
  else aview segs (w_H W2) (ms_mem msF) x).
lazymatch type of T2 with tw_at _ _ ?X2 =>
  assert (T3 : tw_at TMAP_A rdm (TW.upd X2 (TW.OFF_OW + 232) (TW.put 4 (-1)))) end.
{ apply (tw_write TMAP_A (aview segs (w_H W2) mem4) rdm _ TW.OFF_OW TA_OW TW.SZ_OW 232 4 (-1) TMAP_A_ok T2
    TMAP_A_OW).
  - lia.
  - unfold TW.SZ_OW. cbn [Z.of_nat]. lia.
  - intros j Hj. unfold rdm.
    replace ((TA_M + 88 <=? TA_OW + 232 + Z.of_nat j) && (TA_OW + 232 + Z.of_nat j <? TA_M + 92))%bool with false
      by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; rewrite CO, CM; lia).
    rewrite (VDK j Hj). exact (f_equal Some (ro_le_m1 j)).
  - intros x Hx Hn. unfold rdm.
    destruct ((TA_M + 88 <=? x) && (x <? TA_M + 92))%bool eqn:Eb; [reflexivity|].
    apply andb_false_iff in Eb.
    pose proof (inG_low segs B transport_segs_low TG.G_HARNESS x HGX (ro_tw_in_G x Hx)) as Hl.
    apply K5; [lia | cbn [Z.of_nat] in Hn; lia |].
    destruct Eb as [Eb|Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia. }
lazymatch type of T3 with tw_at _ _ ?X3 =>
  assert (T4 : tw_at TMAP_A (aview segs (w_H W2) (ms_mem msF)) (TW.upd X3 (TW.OFF_M + 88) (TW.put 4 GF))) end.
{ apply (tw_write TMAP_A rdm _ _ TW.OFF_M TA_M TW.SZ_M 88 4 GF TMAP_A_ok T3 TMAP_A_M).
  - lia.
  - unfold TW.SZ_M. cbn [Z.of_nat]. lia.
  - intros j Hj. replace (TA_M + 88 + Z.of_nat j) with (TA_M + 1808 + -1720 + Z.of_nat j) by lia.
    exact (VMF j Hj).
  - intros x Hx Hn. unfold rdm.
    replace ((TA_M + 88 <=? x) && (x <? TA_M + 92))%bool with false; [reflexivity|].
    symmetry. apply andb_false_iff. cbn [Z.of_nat] in Hn.
    destruct (Z_lt_le_dec x (TA_M + 88)) as [L|L]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
assert (TWF : tw_at TMAP_A (aview segs (w_H W2) (ms_mem msF)) (recv_w1 Bw)) by (rewrite (ro_w1 Bw HLB); exact T4).
clear T1 T2 T3 T4.
(* the frame's bytes in the block, kept *)
assert (HinB : In (a, Z.max 1 (Z.of_nat (length bytes))) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm) (in_eq _ _)).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 HinB) as (_ & Ha4 & Hac & _).
pose proof (req_size_pos (Z.max 1 (Z.of_nat (length bytes))) ltac:(lia)) as [_ Rq].
assert (HBLKF : recv_blk W2 (ms_mem msF) a bytes).
{ unfold recv_blk. apply (ro_garr8_kept (w_H W2) mem2 (ms_mem msF) a (TW.zs bytes) HBLK).
  intros x Hx. unfold TW.zs in Hx. rewrite length_map in Hx.
  apply KALL; [lia|]. unfold ro_Z. intros [X|X].
  - rewrite EST in X. unfold sp1 in X. lia.
  - apply (blk_img segs B LAWS ly2 S2 W2 mem2 md2 a _ x HAR2 HinB ltac:(lia)).
    exact (proj1 (HGX x (proj1 (ro_G_in bytes x X)))). }
(* the seven saved words, kept *)
assert (HSVF : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) (ms_mem msF)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) RECV_SAVED).
{ apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) HSV o Ho) as Hv.
  assert (Hob : 8 <= fst o <= 56).
  { unfold RECV_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [Ho|Ho]; [subst o; cbn [fst]; lia|]). destruct Ho. }
  rewrite <- Hv. apply rdword_ext. intros i Hi. apply KALL; [lia|].
  unfold ro_Z, ro_G. intros [X|X]; [rewrite EST in X; unfold sp1 in X; lia|]. rewrite CO, CG, CM in X. lia. }
(* what the call keeps, at the cut *)
assert (KGF : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (ms_mem msF) (spZ regs - RECV_STK) (spZ regs)
  (recv_wr bytes)).
{ apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W2 mem2 (ms_mem msF)
    (spZ regs - RECV_STK) (spZ regs) (recv_wr bytes) (ro_Z sp1) HARc HK KALL GR).
  - intros x [X|X] Hc.
    + rewrite RSTK. rewrite EST in X. unfold sp1 in X. lia.
    + exfalso. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS x HGX (proj1 (ro_G_in bytes x X))) as Hl.
      lia.
  - intros b m i Hb Hi [X|X]; [|exact (proj2 (ro_G_in bytes _ X))]. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HARc Hb) as (_ & Hb4 & Hbc & _).
    rewrite EST in X. unfold sp1 in X. lia.
  - intros x [X|X] Hi HnG _ _.
    + pose proof (transport_segs_low x Hi) as Hl. unfold kLowMemEnd in Hl. rewrite EST in X. unfold sp1 in X. lia.
    + exact (HnG (proj1 (ro_G_in bytes x X))).
  - intros cid pos0 x Hin Hr [X|X]; [|exact (proj2 (ro_G_in bytes _ X))]. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HARc Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    rewrite EST in X. unfold sp1 in X.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
(* the rf cut *)
pmkst HS.
exact (RF HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a Bw'
  ly2 S2 W2 (ms_mem msF) mdF (ms_regs msF) HFIX
  (conj HJ4 (conj Hfr (conj Hperm (conj HMO (conj KGF (conj HSVF H4096)))))) HRES HBLKF TWF REGF).
Qed.
End s.
