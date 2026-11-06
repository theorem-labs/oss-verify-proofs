(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 445 of its 529 lines of code are new or changed and 946 lines of the source are left out. *)
(* on_announce_seg_e0: Theorem onann_piece_e0 : onann_e0_stmt (lib/A/Prog/OnannCut.v), the e0 piece of the walk of
   on_announce on fuzz_transport.asan (0x87a74 = transport_sigma TS_on_announce), code +0x3f4 .. +0x420
   (0x87e68 .. 0x87e94), from the cut onann_e0_at to the cuts onann_sl1_at (+0x424) and onann_wk_at (+0x518).
   What the code does (a0 = s + 136, s8 = the shadow base, s10 = the shadow byte's address of s + 112, s1 = sp1):
     +0x3f4 .. +0x404  the check of the 4-byte store at s + 136: its shadow byte (g_s's zero shadow, trans_onann_cells)
                       is 0, so `bnez a1` is not taken; s7 = the frame F, reloaded from sp1 + 40;
     +0x408            `sw zero, 0(a0)`: g_s.foreign = 0 (:201), TW.set_S_foreign B2 0 (a byte of G, of onann_wr);
     +0x40c .. +0x410  the check of the 4-byte load at s + 112 through s10: its shadow byte is 0;
     +0x414 .. +0x41c  a0 = s + 112 (from sp1 + 48), a0 = the 4-byte load at s + 112 (S_state, sign-extended), a1 = 2;
     +0x420            `bne a0, a1`: S_ONLINE goes one instruction to +0x424 and concludes by onann_sl1_at; any other
                       state goes to +0x518 and concludes by onann_wk_at with B4 = set_S_foreign B2 0.
   One run (TransportGRunA.v paj_run_x) from a symbolic state whose regions are the two spill slots, g_s's state and
   foreign fields (absolute) and the two shadow bytes (literal 0); the branch is taken up again from a state with no
   region (as SlostHead.v does at +0x178), so the memory at both cuts is the run's. What the call keeps
   (acall_kept_g) crosses the store by TransportGFrame.v dk_kept_nfz_gw (the stored bytes are bytes of G); the world
   by TWorldG.v tw_write; g_fail_next, onann_ri and S_state by the kit's onann_set_keep (on_announce_seg_kit.v: the
   store is set_S_foreign, inside g_s). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic state at +0x3f4                                        *)
(* ------------------------------------------------------------------ *)

(* The shadow bytes of s + 112 (g_s.state) and s + 136 (g_s.foreign). *)
Definition OE0_SH : Z := 2148220742.
Lemma oe0_sh_eq : OE0_SH = SHADOW_OFF + (ONANN_S + 112) / 8 /\ OE0_SH + 3 = SHADOW_OFF + (ONANN_S + 136) / 8.
Proof. split; reflexivity. Qed.
(* sp1 + 40 holds the frame (s2, atom 18), sp1 + 48 holds s + 112. *)
Definition OE0_R_slot : YP09.region :=
  YP09.mkRegion (Some 9%nat) 40 56 0 0
    [YP09.mkChunk 40 (YP09.CVal 8 (SOff 18 0)); YP09.mkChunk 48 (YP09.CVal 8 (SLit (ONANN_S + 112)))].
(* g_s.state, the 4 bytes of atom 32. *)
Definition OE0_R_st : YP09.region :=
  YP09.mkRegion None (ONANN_S + 112) (ONANN_S + 116) 0 0 [YP09.mkChunk (ONANN_S + 112) (YP09.CVal 4 (SOff 32 0))].
(* g_s.foreign, written. *)
Definition OE0_R_fg : YP09.region :=
  YP09.mkRegion None (ONANN_S + 136) (ONANN_S + 140) (ONANN_S + 136) (ONANN_S + 140) [].
(* The two shadow bytes, 0. *)
Definition OE0_R_sh : YP09.region :=
  YP09.mkRegion None OE0_SH (OE0_SH + 4) 0 0
    [YP09.mkChunk OE0_SH (YP09.CVal 1 (SLit 0)); YP09.mkChunk (OE0_SH + 3) (YP09.CVal 1 (SLit 0))].
Definition OE0_FACTS : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition OE0_REGS : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 10) (SLit (ONANN_S + 136))) (Z_to_bv 5 24) (SLit SHADOW_OFF))
    (Z_to_bv 5 26) (SLit OE0_SH).
Definition ss_oe0 : sstate := mkSS ONANN_E0 OE0_REGS [OE0_R_slot; OE0_R_st; OE0_R_fg; OE0_R_sh] None OE0_FACTS.
Definition OE0_Bx : sv := SLit 0.
Definition OE0_B0 : Z * Z := (0, 0).
(* +0x420, `bne a0, a1`, taken up again with no region. *)
Definition OE0_BR : Z := AF_on_announce + 0x420.
Definition ss_oe0b : sstate := mkSS OE0_BR sr_atoms [] None (mkFacts [] [] []).

(* ------------------------------------------------------------------ *)
(* The model's facts                                                   *)
(* ------------------------------------------------------------------ *)

Lemma oe0_fg_eq : forall Bx, TW.set_S_foreign Bx 0 = TW.upd Bx (TW.OFF_g_s + 136) (TW.put 4 0).
Proof. intros Bx. reflexivity. Qed.

(* `bne a0, a1` on the sign-extended state and 2. *)
Lemma oe0_eqb2 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 2) = (v =? 2).
Proof.
intros v Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 2 (2 ^ 64)) by lia.
destruct (Z.eqb_spec v 2) as [-> | Hne]; [reflexivity|].
apply Z.eqb_neq. intros HH. apply Hne.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. exact HH.
Qed.

Lemma oe0_state_range : forall Bx, - 2 ^ 31 <= TW.S_state Bx < 2 ^ 31.
Proof. intros Bx. unfold TW.S_state. apply TWL.s32_range. Qed.

(* The sign-extended 4-byte load of g_s's state is the model's S_state. *)
Lemma oe0_sext : forall E Bx, ew E 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4) ->
  sv_denot E (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.S_state Bx).
Proof.
intros E Bx H. pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 112) 4) as R. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* A byte of the shadow read as 0 is a stored 0. *)
Lemma oe0_vm0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview tfibsegs H m a = Some 0 -> val_mem tfibsegs (mrestrict H m) a 1 0.
Proof.
  intros H m a Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold aview in Hv. destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Hv].
  cbn in Hv. injection Hv as Hb. change (YO0f.le_byte 0 1 0) with 0.
  f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* A chunk of w bytes of the value e reads, byte k, the k-th little-endian byte of e. *)
Lemma oe0_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem tfibsegs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
  intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  exact (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw).
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma oe0_inG : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, ONANN_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
Qed.

Section e0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The valuation of the run: the registers at the cut, then the 4 bytes of g_s's state in B2. *)
Definition oe0_E (regs : bvmap 5 word) (Bx : list byte) : env :=
  Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4)]).

Lemma oe0_entry0 : forall ly S (W : world segs) regs mem md Bx sp1 F,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bx ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 F ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 0 <= F < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 40) = Some F ->
  rdword (aview segs (w_H W) mem) (sp1 + 48) = Some (ONANN_S + 112) ->
  st_ok_pi segs VAL (oe0_E regs Bx) (mkSS ONANN_E0 sr_atoms [OE0_R_slot; OE0_R_st; OE0_R_fg; OE0_R_sh] None OE0_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_E0)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bx sp1 F HZC HAR Htw R9 R18 Hsp Hsp32 HF S40 S48.
  set (E := oe0_E regs Bx).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, oe0_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4))
    by (unfold E, oe0_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 112) 4) as R32.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R32.
  assert (U32 : bv_unsigned (ew E 32) = TW.u_at Bx (TW.OFF_g_s + 112) 4)
    by (rewrite E32; apply unsigned_lit_small; lia).
  assert (ZSH : forall j, j = 0 \/ j = 3 -> val_mem segs (mrestrict (w_H W) mem) (OE0_SH + j) 1 0).
  { intros j Hj. apply oe0_vm0.
    replace (OE0_SH + j) with (FCells.shadow_addr (ONANN_S + 112 + 8 * j)).
    - apply (decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) _ HAR); [| | | exact HZC].
      + unfold ONANN_S, TA_g_s. destruct Hj as [-> | ->]; reflexivity.
      + destruct Hj as [-> | ->]; lia.
      + unfold TW.SZ_g_s. destruct Hj as [-> | ->]; unfold ONANN_S, TA_g_s; lia.
    - unfold FCells.shadow_addr, FCells.ASAN_K, OE0_SH, ONANN_S, TA_g_s.
      destruct Hj as [-> | ->]; reflexivity. }
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks OE0_R_slot OE0_R_st OE0_R_fg OE0_R_sh
        base_val]; rewrite ?U9.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ sp1 40 8 (SOff 18 0) F);
          [cbn [sv_denot]; rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64;
           rewrite unsigned_lit_small, Z.add_0_r by lia; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ S40).
      * apply (chunk_ok_val segs E _ sp1 48 8 (SLit (ONANN_S + 112)) (ONANN_S + 112));
          [reflexivity | unfold ONANN_S, TA_g_s; lia | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ S48).
    + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 (ONANN_S + 112) 4 (SOff 32 0) (TW.u_at Bx (TW.OFF_g_s + 112) 4));
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | exact R32 | lia |].
      replace (0 + (ONANN_S + 112)) with (TA_g_s + 112) by (unfold ONANN_S; lia).
      exact (tw_read_val segs _ TMAP_A Bx TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
      apply oe0_inG. unfold TW.SZ_g_s. lia.
    + split; [unfold OE0_SH; lia|]. split; [unfold OE0_SH; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ 0 OE0_SH 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. pose proof (ZSH 0 ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0.
      * apply (chunk_ok_val segs E _ 0 (OE0_SH + 3) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. exact (ZSH 3 ltac:(lia)).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, OE0_R_slot, OE0_R_st, OE0_R_fg, OE0_R_sh.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold OE0_SH, ONANN_S, TA_g_s. repeat split; first [exact I | lia].
  - unfold OE0_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U32.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma oe0_entry : forall ly S (W : world segs) regs mem md Bx sp1 F,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bx ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 F ->
  YK11.getr regs 10 = w64 (ONANN_S + 136) -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  YK11.getr regs 26 = w64 OE0_SH ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 0 <= F < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 40) = Some F ->
  rdword (aview segs (w_H W) mem) (sp1 + 48) = Some (ONANN_S + 112) ->
  st_ok_pi segs VAL (oe0_E regs Bx) ss_oe0
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_E0)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bx sp1 F HZC HAR Htw R9 R18 R10 R24 R26 Hsp Hsp32 HF S40 S48.
  rewrite restrict_mkst_fx.
  pose proof (oe0_entry0 ly S W regs mem md Bx sp1 F HZC HAR Htw R9 R18 Hsp Hsp32 HF S40 S48) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 10) (ONANN_S + 136) H0 R10 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 26) OE0_SH H2 R26 eq_refl) as H3.
  exact H3.
Qed.

(* The state at +0x420 with no region. *)
Lemma oe0_entryb : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) ss_oe0b
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OE0_BR)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_oe0b.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac oe0_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "oe0_reg: no match for" T; fail
  end.

(* The write right of a run from a state with the four regions of ss_oe0: only g_s.foreign is writable. *)
Ltac oe0_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    apply oe0_inG; unfold ONANN_S, TA_g_s, TW.SZ_g_s in *; lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_nil.

(* After the one instruction from +0x420 (a run from a state with no region): every byte of the view as at +0x420
   (KD), presence grown (GR). *)
Ltac oe0_after_cut HS W KD GR m5 msF :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end;
  assert (KD : forall a, aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) m5 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a; rewrite (aview_wrap64 tfibsegs _ (ms_mem msF) a), (aview_wrap64 tfibsegs _ m5 a);
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
    match goal with HFx : frame_of ?E ?rs (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (can_aview_kept_frame E rs (w_H W) m5 (ms_mem msF) 0 HFx ltac:(lia)
               ltac:(let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
                     intros x Hx; unfold in_wrange; intros (r & Hr & _); vm_compute in Hr; destruct Hr) _ Ha) end
  | ];
  assert (GR : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].

(* The facts every cut carries move to a later memory whose view is the same at every address. *)
Lemma oe0_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2
    (W2 : world segs) mem2 md2 mem3 md3 e,
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONANN_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 mem3 md3 e
  (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 KD GR.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b0 m i Hb Hi Hn. rewrite KD. exact (K2 b0 m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
Qed.

Lemma oe0_slot_move : forall (W2 : world segs) mem2 mem3 sp1 o v,
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  onann_slot W2 mem2 sp1 o v -> onann_slot W2 mem3 sp1 o v.
Proof.
intros W2 mem2 mem3 sp1 o v KD H. unfold onann_slot in *. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact H.
Qed.

Ltac oe0_kreg HS E1lo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    oe0_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (E1lo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac oe0_kregb HS EEb r n Q H :=
  lazymatch type of Q with _ = ?v =>
    oe0_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (EEb n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.

Lemma onann_piece_e0_holds : @onann_e0_stmt fx rc B MT.
Proof.
unfold onann_e0_stmt. intros SL1 WK. unfold onann_e0_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F B2
  ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HZC & HGU & HGNE & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & Hdf & Htw0 & Hgf0 & Hm &
  HTF & Htfg & Hrom & Hap & Hri0 & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ2 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Htw2 & Hb2 & Hcmd & Hk0 & Hgf2 &
  Hri2 & HSA & S0 & S40).
pose proof HSA as (S8 & S16 & S24 & S48).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R20 & R24 & R25 & R26) & R10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as HCV. pose proof alloc_ceiling_lt as HCL.
clear Hret Hra Hgp Htp H10 H11 H12 Hnow Hdf Htw0 Hgf0 Hm HTF Htfg Hrom Hap Hri0 Hcnt Hcnt2 Hev HFapp.
unfold ONANN_FBYTES in HFc, HFLw.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HFR : ONANN_FRAME = 192) by reflexivity.
assert (Hsp1 : spZ regs - 224 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. rewrite HFR.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  set (q := (spZ regs - 192) / 32) in *. set (r := (spZ regs - 192) mod 32) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (HSTKn : 4304 <= ONANN_STK) by (cbv; congruence).
assert (Hin : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F
  (flag_addr lyc ONANN_CID pos) HAR2 Hfrs Hbl HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
assert (HLB2 : length B2 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw2).
(* +0x3f4 .. +0x420: the run *)
pose proof (oe0_entry ly2 S2 W2 regs2 mem2 md2 B2 sp1 F HZC HAR2 Htw2 R9 R18 R10 R24 R26
  ltac:(lia) ltac:(lia) ltac:(lia) S40 S48) as HS.
set (E0 := oe0_E regs2 B2) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, oe0_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, oe0_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E0 32 = Z_to_bv 64 (TW.u_at B2 (TW.OFF_g_s + 112) 4))
  by (unfold E0, oe0_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (SHOK : sh_ok segs OE0_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ2 SHOK OE0_B0.
{ oe0_awr. }
set (md5 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md5. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in HS end.
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n)
  by (intros n Hn; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
set (m5 := ms_mem ms) in *.
(* the run wrote g_s.foreign only *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (ONANN_S + 136 <= a < ONANN_S + 140) ->
  aview segs (w_H W2) m5 a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => ONANN_S + 136 <= x < ONANN_S + 140) HFr);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  lazymatch type of Hiw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hiw end.
  cbn [In] in Hiw.
  repeat (destruct Hiw as [Hiw | Hiw]; [injection Hiw as <- <- <-; cbn [base_val] in Hx; unfold ONANN_S, TA_g_s; lia |]).
  destruct Hiw. }
assert (GR5 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) m5 a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RS2. cbn [ms_mem restrict] in RS2.
pose proof (oe0_chunk_val E1 (w_H W2) m5 _ _ _ _ _ _ (ONANN_S + 136) 4 (SLit 0) RS2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG.
cbn [base_val] in VG. change (N.to_nat 4) with 4%nat in VG.
change (bv_unsigned (sv_denot E1 (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VG.
clear RS2 HF HFr HG.
(* the registers at +0x420 *)
oe0_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (TW.S_state B2)) X10
  ltac:(apply oe0_sext; rewrite E1lo by lia; exact E32).
oe0_reg HS (Z_to_bv 5 11) (Z_to_bv 64 2) X11 ltac:(reflexivity).
oe0_reg HS (Z_to_bv 5 23) (w64 F) X23
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact R18).
oe0_kreg HS E1lo EE (Z_to_bv 5 2) 2%nat R2 X2. oe0_kreg HS E1lo EE (Z_to_bv 5 3) 3%nat R3 X3.
oe0_kreg HS E1lo EE (Z_to_bv 5 4) 4%nat R4 X4. oe0_kreg HS E1lo EE (Z_to_bv 5 8) 8%nat R8 X8.
oe0_kreg HS E1lo EE (Z_to_bv 5 9) 9%nat R9 X9. oe0_kreg HS E1lo EE (Z_to_bv 5 18) 18%nat R18 X18.
oe0_kreg HS E1lo EE (Z_to_bv 5 19) 19%nat R19 X19. oe0_kreg HS E1lo EE (Z_to_bv 5 20) 20%nat R20 X20.
oe0_kreg HS E1lo EE (Z_to_bv 5 25) 25%nat R25 X25.
oe0_reg HS (Z_to_bv 5 24) (w64 SHADOW_OFF) X24 ltac:(reflexivity).
oe0_reg HS (Z_to_bv 5 26) (w64 (SHADOW_OFF + (ONANN_S + 112) / 8)) X26 ltac:(reflexivity).
(* ---- the facts both cuts carry, at m5 ---- *)
assert (NGS : forall a, ONANN_S + 136 <= a < ONANN_S + 140 -> inG TG.G_HARNESS a)
  by (intros a Ha; apply oe0_inG; unfold TW.SZ_g_s; lia).
assert (NIF : forall a, dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos) a -> ~ (ONANN_S + 136 <= a < ONANN_S + 140)).
{ intros a Hn Ha. destruct (HGX a (NGS a Ha)) as [Hi _]. exact (N2 a Hn Hi). }
assert (TW5 : tw_at TMAP_A (aview segs (w_H W2) m5) (TW.set_S_foreign B2 0)).
{ rewrite oe0_fg_eq.
  apply (tw_write TMAP_A (aview segs (w_H W2) mem2) _ B2 TW.OFF_g_s TA_g_s TW.SZ_g_s 136 4 0 TMAP_A_ok Htw2
    TMAP_A_g_s); [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. assert (L0 : YO0f.le_byte 0 4 j = 0)
      by (unfold YO0f.le_byte; rewrite Z.mod_0_l, Z.shiftr_0_l, Z.mod_0_l by lia; reflexivity).
    rewrite L0. unfold aview. replace (TA_g_s + 136 + Z.of_nat j) with (0 + (ONANN_S + 136) + Z.of_nat j)
      by (unfold ONANN_S; lia).
    rewrite (VG j Hj), L0. reflexivity.
  - intros x Hx Hn. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KR; [lia | unfold ONANN_S; cbn [Z.of_nat Pos.of_succ_nat] in Hn; lia]. }
assert (KG5 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 m5 (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)).
{ apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2 m5
    (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F (flag_addr lyc ONANN_CID pos) (onann_wr Bw b)
    (fun x => ONANN_S + 136 <= x < ONANN_S + 140) HGX HARc HAR2 Hfrs Hbl HlyF EF eq_refl FFL);
    [lia | lia | | exact HK | exact KR | exact GR5].
  intros a Ha. right; right. exact (NGS a Ha). }
assert (KS : forall a, alloc_ceiling <= a < 2 ^ 64 -> aview segs (w_H W2) m5 a = aview segs (w_H W2) mem2 a)
  by (intros a Ha; apply KR; [lia | unfold ONANN_S, TA_g_s; lia]).
assert (HSV5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) m5) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ assert (HSo : forall o, In o ONANN_SAVED -> 8 <= fst o <= 104).
  { intros o Ho. unfold ONANN_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
  rewrite Forall_forall in Hsaved |- *. intros o Ho. pose proof (HSo o Ho) as Hob.
  rewrite <- (Hsaved o Ho). apply rdword_ext. intros i Hi. apply KS. lia. }
assert (HFL5 : rdword (aview segs (w_H W2) m5) (F + 1024 - 8) = Some (flag_addr lyc ONANN_CID pos)).
{ rewrite <- HFLw. apply rdword_ext. intros i Hi. apply KR; [lia|].
  apply (NIF (F + 1024 - 8 + i)). left. change (fs_frame_bytes ONANN_CID) with 1024. lia. }
assert (KD5 : forall a, sp1 <= a < spZ regs -> aview segs (w_H W2) m5 a = aview segs (w_H W2) mem2 a)
  by (intros a Ha; apply KS; lia).
assert (SL5 : forall o v, 0 <= o <= 56 -> onann_slot W2 mem2 sp1 o v -> onann_slot W2 m5 sp1 o v).
{ intros o v Ho Hs. unfold onann_slot in *. rewrite <- Hs. apply rdword_ext. intros i Hi. apply KD5. lia. }
assert (CUR5 : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 m5 md5 0).
{ refine (conj _ (conj He0 (conj Hfrs (conj Hperm (conj HlyF (conj Hmo (conj KG5 (conj HSV5 _)))))))).
  - exact HJ2.
  - unfold ONANN_FBYTES. exact HFL5. }
destruct (onann_set_keep B2 0 HLB2 (TW.set_S_foreign B2 0) (or_intror (or_introl eq_refl)))
  as (_ & EGF0 & ERI0 & EST & _).
assert (EGF : TW.g_fail_next (TW.set_S_foreign B2 0) <= 1) by (rewrite EGF0; exact Hgf2).
pose proof (ERI0 Hri2) as ERI. clear EGF0 ERI0.
(* +0x420: `bne a0, a1`, from a state with no region *)
pmkst HS.
clear HS SHOK.
pose proof (oe0_entryb W2 (ms_regs ms) m5) as HS.
set (Eb := Eimg (PI := PI_transport) (Ereg (ms_regs ms) [])) in HS.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) Eb (mrestrict (w_H W2) m5)) by constructor.
assert (HEIb : img_env VAL A_LIM Eb) by (unfold Eb; apply Eimg_env).
assert (EEb : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Eb n = YK11.getr (ms_regs ms) r)
  by (intros n r Hn; unfold Eb; apply ew_Eimg_Ereg_nat; exact Hn).
assert (D10 : sv_denot Eb (SOff 10 0) = Z_to_bv 64 (TW.S_state B2))
  by (cbn [sv_denot]; rewrite (EEb 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X10).
assert (D11 : sv_denot Eb (SOff 11 0) = Z_to_bv 64 2)
  by (cbn [sv_denot]; rewrite (EEb 11%nat (Z_to_bv 5 11) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X11).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OE0_BR)) mm rom) mdx) Q) end.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
psrr_branch_tok RUN BR HS SHOK OE0_B0.
- (* taken: S_state <> S_ONLINE, to the wake test +0x518 *)
  cbn [branch_taken] in Hc. rewrite D10, D11 in Hc.
  rewrite (oe0_eqb2 _ (oe0_state_range B2)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hne : TW.S_state B2 <> TS0.DIGINET_S_ONLINE) by exact Hc.
  assert (HK4 : onann_k_wk timg_A TF (TW.set_S_foreign B2 0) now = Some (Bw', tt)).
  { unfold onann_k_e0 in Hk0. rewrite EST in Hk0.
    rewrite (proj2 (Z.eqb_neq _ _) Hne) in Hk0. exact Hk0. }
  paj_run_to_tok RUNTO HS HJ2 SHOK OE0_B0 ONANN_WK.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_nil. }
  oe0_after_cut HS W2 KD GR m5 msF.
  oe0_kregb HS EEb (Z_to_bv 5 2) 2%nat X2 Y2. oe0_kregb HS EEb (Z_to_bv 5 3) 3%nat X3 Y3.
  oe0_kregb HS EEb (Z_to_bv 5 4) 4%nat X4 Y4. oe0_kregb HS EEb (Z_to_bv 5 8) 8%nat X8 Y8.
  oe0_kregb HS EEb (Z_to_bv 5 9) 9%nat X9 Y9. oe0_kregb HS EEb (Z_to_bv 5 18) 18%nat X18 Y18.
  oe0_kregb HS EEb (Z_to_bv 5 19) 19%nat X19 Y19. oe0_kregb HS EEb (Z_to_bv 5 20) 20%nat X20 Y20.
  oe0_kregb HS EEb (Z_to_bv 5 23) 23%nat X23 Y23. oe0_kregb HS EEb (Z_to_bv 5 24) 24%nat X24 Y24.
  oe0_kregb HS EEb (Z_to_bv 5 10) 10%nat X10 Y10.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_WK)) mm rom) mdx) Q) end.
  apply (WK LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    (TW.set_S_foreign B2 0) ly2 S2 W2 (ms_mem msF) _ (ms_regs msF) HFIX).
  + unfold onann_wk_cur.
    refine (conj (oe0_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 m5 md5
      (ms_mem msF) _ 0 CUR5 HJ2 KD GR) (conj _ (conj HK4 (conj EGF (conj ERI _))))).
    * apply (tw_kept TMAP_A (aview segs (w_H W2) m5)); [exact TW5 | intros x _; exact (KD x)].
    * apply (oe0_slot_move W2 m5 (ms_mem msF) sp1 0 now KD). exact (SL5 0 now ltac:(lia) S0).
  + unfold onann_regs_wk, onann_regs_rel, onann_regs_base.
    refine (conj (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y19)))))) Y23) (conj _ (conj Y20 Y24))).
    refine (eq_trans Y10 _). rewrite EST. reflexivity.
- (* not taken: S_state = S_ONLINE, to the first inlined session_lost +0x424 *)
  cbn [branch_taken] in Hc. rewrite D10, D11 in Hc.
  rewrite (oe0_eqb2 _ (oe0_state_range B2)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  assert (HON : TW.S_state (TW.set_S_foreign B2 0) = TS0.DIGINET_S_ONLINE) by (rewrite EST, Hc; reflexivity).
  assert (HK1 : onann_k_sl1 timg_A TF (TW.set_S_foreign B2 0) now = Some (Bw', tt)).
  { unfold onann_k_e0 in Hk0. rewrite (proj2 (Z.eqb_eq _ _) HON) in Hk0. exact Hk0. }
  paj_run_to_tok RUNTO HS HJ2 SHOK OE0_B0 ONANN_SL1.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_nil. }
  oe0_after_cut HS W2 KD GR m5 msF.
  oe0_kregb HS EEb (Z_to_bv 5 2) 2%nat X2 Y2. oe0_kregb HS EEb (Z_to_bv 5 3) 3%nat X3 Y3.
  oe0_kregb HS EEb (Z_to_bv 5 4) 4%nat X4 Y4. oe0_kregb HS EEb (Z_to_bv 5 8) 8%nat X8 Y8.
  oe0_kregb HS EEb (Z_to_bv 5 9) 9%nat X9 Y9. oe0_kregb HS EEb (Z_to_bv 5 18) 18%nat X18 Y18.
  oe0_kregb HS EEb (Z_to_bv 5 19) 19%nat X19 Y19. oe0_kregb HS EEb (Z_to_bv 5 20) 20%nat X20 Y20.
  oe0_kregb HS EEb (Z_to_bv 5 23) 23%nat X23 Y23. oe0_kregb HS EEb (Z_to_bv 5 24) 24%nat X24 Y24.
  oe0_kregb HS EEb (Z_to_bv 5 25) 25%nat X25 Y25. oe0_kregb HS EEb (Z_to_bv 5 26) 26%nat X26 Y26.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_SL1)) mm rom) mdx) Q) end.
  apply (SL1 LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    B2 ly2 S2 W2 (ms_mem msF) _ (ms_regs msF) HFIX).
  + unfold onann_sl1_cur.
    refine (conj (oe0_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 m5 md5
      (ms_mem msF) _ 0 CUR5 HJ2 KD GR)
      (conj _ (conj Hb2 (conj HON (conj HK1 (conj EGF (conj ERI (conj _ _)))))))).
    * apply (tw_kept TMAP_A (aview segs (w_H W2) m5)); [exact TW5 | intros x _; exact (KD x)].
    * unfold onann_slots_arm.
      refine (conj _ (conj _ (conj _ _))); apply (oe0_slot_move W2 m5 (ms_mem msF) sp1 _ _ KD).
      -- exact (SL5 8 _ ltac:(lia) S8).
      -- exact (SL5 16 _ ltac:(lia) S16).
      -- exact (SL5 24 _ ltac:(lia) S24).
      -- exact (SL5 48 _ ltac:(lia) S48).
    * apply (oe0_slot_move W2 m5 (ms_mem msF) sp1 0 now KD). exact (SL5 0 now ltac:(lia) S0).
  + unfold onann_regs_sl1, onann_regs_arm, onann_regs_base.
    refine (conj (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 Y19))))))
      (conj Y20 (conj Y24 (conj Y25 Y26)))) Y23).
Qed.
End e0.

(* The e0 piece of the walk of on_announce (OnannCut.v onann_e0_stmt), at every machine, run ceiling, record and
   meter. *)
Theorem onann_piece_e0 : forall fx rc B MT, @onann_e0_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@onann_piece_e0_holds fx rc B MT). Qed.
