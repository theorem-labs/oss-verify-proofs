(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v for libreac/fuzz_grant's program walk: the listing's names are gsym, PALib names fuzz_grant.asan's objects and the wrappers' 4-byte jumps, and fuzz_grant's image bound; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: taken by path from libreac/fuzz_grant's copy (proofs/libreac/fuzz_grant/lib/A/Prog/GrantPaLib.v, file sha256 1750b9b228be; donor not released) for libreac/fuzz_decode's
   program walk: module paths and the listing's names changed. *)
(* Modified by Theorem Labs, 2026-10: image B's twin of this unit's lib/A/Prog/DecodePaLib.v, in the shape of proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBPaLib.v (file sha256 73c9e12166f6; donor not released): the names are dbsym's (the wrappers' free and malloc entries are DB___interceptor_trampoline_free and DB___interceptor_trampoline_malloc); PALib names fuzz_decode.asan-ubsan's objects of lib/B/Prog/DecodeBAddr.v and lib/B/AsanCells.v: the shadow-base GOT word is object 1 (GOT_CELL_K 0x992e8) and its cell object 14 (CELL_K 0xa1338), the side-stack flag's GOT word object 0 (GOT_UAR 0x99340) and its cell object 15 (UAR 0xa1340); the two cells are one object later than image A's 13 and 14 because image B's slots load one more object (object 13, 0x103c8); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/DgnTransportBPaLib.v; 9 of its 34 lines of code are new or changed and 475 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/TransportGRunB.v, with its module paths and module names changed; 398 of its 427 lines of code are new or changed and 5 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_lib.v, with its module paths and module names changed; 752 of its 839 lines of code are new or changed and 340 lines of the source are left out. *)
(* m_rx_seg_mac: the segment MAC of the image-A walk of m_rx (statement lib/A/Prog/m_rx_cg.v, kit
   lib/A/Prog/m_rx_seg_kit.v), Lemma mrx_seg_mac: from the cut MAC (0x84abc, the header read) to the cuts DESK
   (0x84b08) and EPI (0x8496c), through the three MAC compares (fuzz_transport.c:285-287; model EPI.mrx_top).
     0x84abc - 0x84ad0  s1 = fa + 6; a1 = HOST (object 6, 0x21040); a2 = 6; a0 = s1; bcmp (fa + 6, HOST, 6);
     0x84ad4            beqz a0: a0 = 0 (src = HOST) goes to the epilogue 0x8496c with a0 = 0;
     0x84ad8 - 0x84ae8  bcmp (fa, HOST, 6); 0x84aec beqz a0: a0 = 0 (dst = HOST) goes to 0x84b08;
     0x84af0 - 0x84b00  bcmp (fa, SPEC_BCAST (object 16, 0x21080), 6); 0x84b04 bnez a0: a0 <> 0 goes to 0x84968
                        (a0 = 0) and the epilogue; a0 = 0 (dst = SPEC_BCAST) goes on to 0x84b08.
   Each run is a symbolic run (TransportGRunA.v paj_run_x / paj_run_to_x) from a fresh state (no region) at the
   segment start or at a call's return address; no run reads or writes memory. Each call is the kit's mrx_bcmp_gx on
   the inner journal: its ranges are frame ranges (mrx_frs: decode_rd_ok of the frame) and HOST / SPEC_BCAST
   (trans_rom_view_rd for their bytes, transport_cells and trans_mrx_cells for their shadow bytes and the rest of
   their aligned group of 8); its result is 0 exactly when the model's beq_bytes holds (garr8 for the frame bytes; the
   image's HOST and SPEC_BCAST bytes are TCb's, decided by vm_compute). A call changes no byte outside its stack window
   [sp - 144 - 2 * ESTACK, sp - 144) and keeps the callee-saved registers, so the frame, the read-only view, the saved
   slots, the spills, the world relation and the header registers hold at each successor cut (mac_mid). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  m_lost_cg m_wake_cg m_maybe_online_cg m_tick_cg desk_named_cg check_state_data_cg m_rx_cg m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* A fresh state at offset pc of the listing: atoms 0 .. 31 the registers, 32 the shadow base; no region (the
   segment's runs touch no memory). *)
Definition mac_facts : facts := mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition mac_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None mac_facts.
Definition MAC_SH : list shent := [].
Definition MAC_Bx : sv := SOff 32 0.
Definition mac_E {rc : YM05.RunCeil} (regs : bvmap 5 word) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF]).
(* The callee-saved registers the first run keeps (all but s1). *)
Definition MAC_KEEP : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac mac_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "mac_reg: no match for" T; fail
  end.

(* The write rights of a run from a state with no region. *)
Ltac mac_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.

(* The closed bounds of a shadow hull hypothesis lo <= s < hi, computed. *)
Ltac mac_hull Hs :=
  lazymatch type of Hs with ?lo <= ?s < ?hi =>
    let lo' := eval vm_compute in lo in let hi' := eval vm_compute in hi in change (lo' <= s < hi') in Hs end.

(* ------------------------------------------------------------------ *)
(* Bytes, the model                                                    *)
(* ------------------------------------------------------------------ *)

Lemma mac_some_inv : forall (x y : list byte) (a b : Z), Some (x, a) = Some (y, b) -> y = x /\ b = a.
Proof. intros x y a b H. injection H as H1 H2. split; symmetry; assumption. Qed.

Lemma mac_mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H m' a = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
  intros H m m' a E. unfold aview in E.
  destruct (mbyte tfibsegs (mrestrict H m') a) as [b1|]; destruct (mbyte tfibsegs (mrestrict H m) a) as [b2|];
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* The j-th byte of a garr8 array under the view. *)
Lemma mac_garr_view : forall (Wx : world tfibsegs) mem p (bs : list byte) j,
  garr8 tfibsegs (mrestrict (w_H Wx) mem) p (map DSpec.bz bs) -> (j < length bs)%nat ->
  aview tfibsegs (w_H Wx) mem (p + Z.of_nat j) = Some (bv_unsigned (nth j bs (Z_to_bv 8 0))).
Proof.
  intros Wx mem p bs j HG Hj.
  assert (Hj' : (j < length (map DSpec.bz bs))%nat) by (rewrite length_map; exact Hj).
  pose proof (garr8_mbyte tfibsegs _ p _ j HG Hj') as Hm.
  rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) in Hm by exact Hj'. rewrite map_nth in Hm.
  unfold aview. rewrite Hm. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold DSpec.bz.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* Two 6-byte lists have the same values exactly when they agree byte by byte. *)
Lemma mac_zs6 : forall l1 l2 : list byte, length l1 = 6%nat -> length l2 = 6%nat ->
  (TW.zs l1 = TW.zs l2 <->
   forall i, 0 <= i < 6 -> bv_unsigned (nth (Z.to_nat i) l1 (Z_to_bv 8 0)) = bv_unsigned (nth (Z.to_nat i) l2 (Z_to_bv 8 0))).
Proof.
  intros l1 l2 L1 L2.
  destruct l1 as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 [|? ?]]]]]]]; cbn in L1; try discriminate L1.
  destruct l2 as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|? ?]]]]]]]; cbn in L2; try discriminate L2.
  unfold TW.zs. cbn [map]. split.
  - intros E i Hi. injection E as E0 E1 E2 E3 E4 E5.
    assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      [exact E0 | exact E1 | exact E2 | exact E3 | exact E4 | exact E5].
  - intros H.
    assert (H0 : bv_unsigned a0 = bv_unsigned b0) by exact (H 0 ltac:(lia)).
    assert (H1 : bv_unsigned a1 = bv_unsigned b1) by exact (H 1 ltac:(lia)).
    assert (H2 : bv_unsigned a2 = bv_unsigned b2) by exact (H 2 ltac:(lia)).
    assert (H3 : bv_unsigned a3 = bv_unsigned b3) by exact (H 3 ltac:(lia)).
    assert (H4 : bv_unsigned a4 = bv_unsigned b4) by exact (H 4 ltac:(lia)).
    assert (H5 : bv_unsigned a5 = bv_unsigned b5) by exact (H 5 ltac:(lia)).
    rewrite H0, H1, H2, H3, H4, H5. reflexivity.
Qed.

(* HOST's and SPEC_BCAST's six bytes in the image (fuzz_transport.c:109, spec.h:69; TCb.v HOST, SPEC_BCAST),
   decided over the loaded segments. *)
Lemma mac_host_rom : forall i, 0 <= i < 6 ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (TRANS_HOST + i)))
  = Some (bv_unsigned (nth (Z.to_nat i) TC.HOST (Z_to_bv 8 0))).
Proof.
  intros i Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.
Lemma mac_bcast_rom : forall i, 0 <= i < 6 ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (TRANS_SPEC_BCAST + i)))
  = Some (bv_unsigned (nth (Z.to_nat i) TC.SPEC_BCAST (Z_to_bv 8 0))).
Proof.
  intros i Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.

(* HOST and SPEC_BCAST lie in TRANS_RO_RD (their registered globals' payloads); every TRANS_RO_RD byte lies below
   0xa5000. *)
Lemma mac_host_ro : forall i, 0 <= i < 6 -> trans_in_ro_rd (TRANS_HOST + i).
Proof.
  intros i Hi. unfold trans_in_ro_rd, TRANS_RO_RD. apply Exists_exists. exists (TRANS_HOST, 6). split.
  - apply in_or_app. right. unfold TRANS_RO_GLOBALS. right. left. reflexivity.
  - unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma mac_bcast_ro : forall i, 0 <= i < 6 -> trans_in_ro_rd (TRANS_SPEC_BCAST + i).
Proof.
  intros i Hi. unfold trans_in_ro_rd, TRANS_RO_RD. apply Exists_exists. exists (TRANS_SPEC_BCAST, 6). split.
  - apply in_or_app. right. unfold TRANS_RO_GLOBALS. right. right. right. left. reflexivity.
  - unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma mac_ro_low : forall a, trans_in_ro_rd a -> 0 <= a < 0xa5000.
Proof.
  intros a H. unfold trans_in_ro_rd in H. apply Exists_exists in H as (zr & Hin & Hz).
  destruct zr as (lo & len). unfold in_zr in Hz. cbn [fst snd] in Hz.
  unfold TRANS_RO_RD, TRANS_RO_GLOBALS in Hin. cbn [app] in Hin.
  repeat (destruct Hin as [Hin | Hin];
    [injection Hin as Hl Hn; subst lo len;
     lazymatch type of Hz with ?l <= _ < _ => let v := eval vm_compute in l in change l with v in Hz end; lia |]).
  destruct Hin.
Qed.

(* A one-byte constant cell of the record, read at an AR state. *)
Lemma mac_le1 : forall v, 0 <= v < 256 -> YG0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256 Hv). exact (Z.mod_small v 256 Hv).
Qed.
Lemma mac_const1 : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v s,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> a = s ->
  aview tfibsegs (w_H W) mem s = Some v.
Proof.
  intros rc B ly S W mem md a v s HAR Hin Hv <-.
  destruct HAR as (Mx & _).
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) _ Hin) as Hc.
  unfold cell_holds in Hc. cbn [c_at c_w YG0f.c_val z1 c1 aeval] in Hc.
  specialize (Hc 0%nat ltac:(lia)). rewrite (mac_le1 v Hv) in Hc.
  replace a with (a + Z.of_nat 0) by lia. exact Hc.
Qed.
Lemma mac_const1_nn : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v s,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> a = s ->
  aview tfibsegs (w_H W) mem s <> None.
Proof.
  intros rc B ly S W mem md a v s H1 H2 H3 H4. rewrite (mac_const1 B ly S W mem md a v s H1 H2 H3 H4). discriminate.
Qed.

(* The four cases of mrx_top (the three compares). *)
Lemma mac_m_src : forall I fr B B' r, TC.beq_bytes (EPI.mrx_src fr) TC.HOST = true ->
  EPI.mrx_top I fr B = Some (B', r) -> B' = B /\ r = 0.
Proof.
  intros I fr B B' r E1 H. unfold EPI.mrx_top in H. rewrite E1 in H. cbn [orb] in H.
  exact (mac_some_inv _ _ _ _ H).
Qed.
Lemma mac_m_dsth : forall I fr B B' r, TC.beq_bytes (EPI.mrx_src fr) TC.HOST = false ->
  TC.beq_bytes (EPI.mrx_dst fr) TC.HOST = true ->
  EPI.mrx_top I fr B = Some (B', r) -> EPI.mrx_desk_m I fr B = Some (B', r).
Proof.
  intros I fr B B' r E1 E2 H. unfold EPI.mrx_top in H. rewrite E1, E2 in H. cbn [orb andb negb] in H. exact H.
Qed.
Lemma mac_m_bc_no : forall I fr B B' r, TC.beq_bytes (EPI.mrx_src fr) TC.HOST = false ->
  TC.beq_bytes (EPI.mrx_dst fr) TC.HOST = false -> TC.beq_bytes (EPI.mrx_dst fr) TC.SPEC_BCAST = false ->
  EPI.mrx_top I fr B = Some (B', r) -> B' = B /\ r = 0.
Proof.
  intros I fr B B' r E1 E2 E3 H. unfold EPI.mrx_top in H. rewrite E1, E2, E3 in H. cbn [orb andb negb] in H.
  exact (mac_some_inv _ _ _ _ H).
Qed.
Lemma mac_m_bc_yes : forall I fr B B' r, TC.beq_bytes (EPI.mrx_src fr) TC.HOST = false ->
  TC.beq_bytes (EPI.mrx_dst fr) TC.HOST = false -> TC.beq_bytes (EPI.mrx_dst fr) TC.SPEC_BCAST = true ->
  EPI.mrx_top I fr B = Some (B', r) -> EPI.mrx_desk_m I fr B = Some (B', r).
Proof.
  intros I fr B B' r E1 E2 E3 H. unfold EPI.mrx_top in H. rewrite E1, E2, E3 in H. cbn [orb andb negb] in H. exact H.
Qed.

(* bv_eqb against 0. *)
Lemma mac_eqb0 : forall a : word, bv_eqb a (Z_to_bv 64 0) = true <-> a = w64 0.
Proof.
  intros a. unfold bv_eqb. split.
  - intros H. apply Z.eqb_eq in H. apply bv_eq. exact H.
  - intros ->. apply Z.eqb_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

Section seg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HMRX : trans_mrx_cells B.
Hypothesis HRO : trans_ro_rd_unowned B.
Hypothesis HNE : trans_rom_no_errno B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS.
Hypothesis HGNE : gx_noerrno B TG.G_HARNESS.
Hypothesis HBCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc tfibsegs B (transport_sigma TS___interceptor_trampoline_bcmp).
Hypothesis HMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc tfibsegs B OCpy (transport_sigma TS___asan_memcpy).
Hypothesis HML : forall fx' : YK11.FPState, @transport_m_lost_cg fx' rc B MT (transport_sigma TS_m_lost).
Hypothesis HDN : forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transport_sigma TS_desk_named).
Hypothesis HMW : forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transport_sigma TS_m_wake).
Hypothesis HMO : forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transport_sigma TS_m_maybe_online).
Hypothesis HMT : forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transport_sigma TS_m_tick).
Variable sp1 : Z.
Variable regs0 : bvmap 5 word.
Variable lyc : alayout.
Variable Sc : astate.
Variable W : world tfibsegs.
Variable memc : word -> option byte.
Variable mdc : Model.
Variable fr : TI.tframe.
Variable n : Z.
Variable Bw' : list byte.
Variable r : Z.
Hypothesis HST : mrx_static B sp1 regs0 lyc Sc W memc mdc fr n.
Local Notation K := (@mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).

Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Local Abbreviation IPOST := (@mrx_ipost fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).
Local Abbreviation fa := (TI.tf_addr fr).

(* The image objects and the pcs: object 6 is HOST, object 16 SPEC_BCAST; the segment's pcs (offsets from the
   listing's base): MAC 0x84abc = 14424, EPI 0x8496c = 14088, DESK 0x84b08 = 14500. *)
Lemma mac_vals : VAL (A_OBJ 6) = TRANS_HOST /\ VAL (A_OBJ 16) = TRANS_SPEC_BCAST /\
  BASE + 14424 = MRX_PC OFF_MAC /\ BASE + 14088 = MRX_PC OFF_EPI /\ BASE + 14500 = MRX_PC OFF_DESK.
Proof. vm_compute. repeat split. Qed.

(* The fresh state at offset pc, from a machine at BASE + pc. *)
Lemma mac_entry : forall (H : word -> bool) regs mem pc,
  st_ok_pi segs VAL (mac_E regs) (mac_ss pc)
    (restrict H (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros H regs mem pc.
  assert (E32 : ew (mac_E regs) 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold mac_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  rewrite restrict_mkst_fx. unfold mac_ss.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint]. exact I.
  - unfold mac_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

Lemma mac_agree : forall regs, env_agree 32 (Ereg regs [w64 SHADOW_OFF]) (mac_E regs).
Proof. intros regs. split; [intros k Hk; unfold mac_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma mac_img : forall regs, img_env VAL A_LIM (mac_E regs).
Proof. intros regs. unfold mac_E. apply Eimg_env. Qed.

(* The symbolic values of the registers the runs leave, at a fresh state's valuation. *)
Lemma mac_sv_reg : forall regs k (q : bv 5) c v, Z.of_nat k = bv_unsigned q -> YK11.getr regs q = w64 v ->
  0 <= v < 2 ^ 64 -> sv_denot (mac_E regs) (SOff k c) = w64 (v + c).
Proof.
  intros regs k q c v Hk Hq Hv. cbn [sv_denot]. unfold mac_E. rewrite (ew_Eimg_Ereg_nat regs _ k q Hk), Hq.
  unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma mac_sv_reg0 : forall regs k (q : bv 5) v, Z.of_nat k = bv_unsigned q -> YK11.getr regs q = w64 v ->
  0 <= v < 2 ^ 64 -> sv_denot (mac_E regs) (SOff k 0) = w64 v.
Proof. intros regs k q v Hk Hq Hv. rewrite (mac_sv_reg regs k q 0 v Hk Hq Hv), Z.add_0_r. reflexivity. Qed.
Lemma mac_sv_obj : forall regs k v, (A_TEXT <= k < A_LIM)%nat -> VAL k = v -> 0 <= v < 2 ^ 64 ->
  sv_denot (mac_E regs) (SOff k 0) = w64 v.
Proof.
  intros regs k v Hk Hv Hr. cbn [sv_denot]. unfold mac_E. rewrite Eimg_img by exact Hk. rewrite Hv.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma mac_sv_a0 : forall regs, sv_denot (mac_E regs) (SOff 10 0) = YK11.getr regs (Z_to_bv 5 10).
Proof.
  intros regs. cbn [sv_denot]. unfold mac_E. rewrite (ew_Eimg_Ereg_nat regs _ 10 (Z_to_bv 5 10) eq_refl).
  rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

(* The two branches on a0 (beqz / bnez). *)
Lemma mac_br_eq : forall regs,
  branch_taken BC_EQ (sv_denot (mac_E regs) (SOff 10 0)) (sv_denot (mac_E regs) (SLit 0)) = true <->
  YK11.getr regs 10 = w64 0.
Proof. intros regs. cbn [branch_taken]. rewrite mac_sv_a0. cbn [sv_denot]. exact (mac_eqb0 _). Qed.
Lemma mac_br_ne : forall regs,
  branch_taken BC_NE (sv_denot (mac_E regs) (SOff 10 0)) (sv_denot (mac_E regs) (SLit 0)) = true <->
  YK11.getr regs 10 <> w64 0.
Proof.
  intros regs. cbn [branch_taken]. rewrite mac_sv_a0. cbn [sv_denot]. rewrite negb_true_iff.
  pose proof (mac_eqb0 (YK11.getr regs (Z_to_bv 5 10))) as Q.
  destruct (bv_eqb (YK11.getr regs (Z_to_bv 5 10)) (Z_to_bv 64 0)).
  - split; [discriminate | intros N; exfalso; apply N; exact (proj1 Q eq_refl)].
  - split; [intros _ Z0; apply Q in Z0; discriminate Z0 | reflexivity].
Qed.
Lemma mac_br_eq_f : forall regs,
  branch_taken BC_EQ (sv_denot (mac_E regs) (SOff 10 0)) (sv_denot (mac_E regs) (SLit 0)) = false ->
  YK11.getr regs 10 <> w64 0.
Proof. intros regs H E. apply (proj2 (mac_br_eq regs)) in E. rewrite E in H. discriminate H. Qed.
Lemma mac_br_ne_f : forall regs,
  branch_taken BC_NE (sv_denot (mac_E regs) (SOff 10 0)) (sv_denot (mac_E regs) (SLit 0)) = false ->
  YK11.getr regs 10 = w64 0.
Proof.
  intros regs H. destruct (bv_eqb (YK11.getr regs 10) (Z_to_bv 64 0)) eqn:Q.
  - exact (proj1 (mac_eqb0 _) Q).
  - exfalso. assert (N : YK11.getr regs 10 <> w64 0) by (intros Z0; apply (proj2 (mac_eqb0 _)) in Z0; congruence).
    apply (proj2 (mac_br_ne regs)) in N. rewrite N in H. discriminate H.
Qed.

(* The static facts. *)
Lemma mac_sp : 2 ^ 46 <= sp1 - MRX_STK /\ sp1 <= 2 ^ 47 /\ MRX_STK = 8352 /\ MRX_FRAME = 144.
Proof.
  pose proof HST as (_ & _ & _ & H46 & H47 & _). split; [exact H46|]. split; [exact H47|].
  split; reflexivity.
Qed.

Section cut.
Variable Wc : world segs.
Variable Bwc : list byte.
Variable regs2 : bvmap 5 word.
Variable mem2 : word -> option byte.
Hypothesis KE : K (MRX_PC OFF_EPI) (R_EPI Bw' r).
Hypothesis KD : K (MRX_PC OFF_DESK) (R_DESK fr n sp1 lyc Sc Bw' r).
Hypothesis HMO2 : mo_le MT Sc Sc 0.
Hypothesis HSV : mrx_saved Wc mem2 sp1 regs0.
Hypothesis HTW : tw_at TMAP_A (aview segs (w_H Wc) mem2) Bwc.
Hypothesis HFRS : mrx_frs fr Wc mem2.
Hypothesis HHDR : mrx_hdr fr n.
Hypothesis H2 : YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME).
Hypothesis H3 : YK11.getr regs2 3 = YK11.getr regs0 3.
Hypothesis H4 : YK11.getr regs2 4 = YK11.getr regs0 4.
Hypothesis H8 : YK11.getr regs2 8 = w64 (TI.tf_addr fr).
Hypothesis H19 : YK11.getr regs2 19 = w64 (mfb fr 18).
Hypothesis H20 : YK11.getr regs2 20 = w64 (DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 14).
Hypothesis HHR : mrx_hregs fr Wc sp1 regs2 mem2.
Hypothesis HM : EPI.mrx_top timg_A fr Bwc = Some (Bw', r).

(* The stack window below the frame: the only bytes a call may change. *)
Definition mac_win (a : Z) : Prop := sp1 - MRX_STK <= a < sp1 - MRX_FRAME.
(* The view at m is the cut's outside that window. *)
Definition mac_KV (m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ mac_win a -> aview segs (w_H Wc) m a = aview segs (w_H Wc) mem2 a.
(* The callee-saved registers are the cut's, but s1 = fa + 6. *)
Definition mac_rg (regs : bvmap 5 word) : Prop :=
  (forall q, acallee_saved q -> q <> 9 -> YK11.getr regs (Z_to_bv 5 q) = YK11.getr regs2 (Z_to_bv 5 q)) /\
  YK11.getr regs (Z_to_bv 5 9) = w64 (fa + 6).
(* A machine between the compares: the inner journal at the current memory, the registers, the view. *)
Definition mac_mid (regs : bvmap 5 word) (m : word -> option byte) (md : Model) : Prop :=
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc Wc m md 0 /\
  mac_rg regs /\ mac_KV m.

Ltac mac_lia := unfold mac_win, MRX_FRAME, ESTACK, TRANS_HOST, TRANS_SPEC_BCAST in *; lia.

(* The frame: placed apart from the stack window, below 2 ^ 63, at least 30 bytes. *)
Lemma mac_fpl : 0 < fa /\ (fa + mlen fr <= sp1 - MRX_STK \/ sp1 <= fa) /\ fa + mlen fr <= 2 ^ 63 /\ 30 <= mlen fr.
Proof.
  pose proof HST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfa0 & _ & _ & Hpl & _).
  pose proof HFRS as (_ & (_ & _ & _ & _ & _ & H63) & _). pose proof HHDR as (Hn & _).
  split; [exact Hfa0|]. split; [exact Hpl|]. split; [exact H63 | lia].
Qed.

Lemma mac_mid_step : forall regs m md regs' m' md',
  mac_mid regs m md -> aregs_preserved regs regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ mac_win a -> aview segs (w_H Wc) m' a = aview segs (w_H Wc) m a) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc Wc m' md' 0 ->
  mac_mid regs' m' md'.
Proof.
  intros regs m md regs' m' md' (HJ & (RG1 & RG9) & KV) HP KV' HJ'.
  split; [exact HJ'|]. split; [split|].
  - intros q Hq H9. rewrite (HP q Hq). exact (RG1 q Hq H9).
  - rewrite (HP 9 ltac:(unfold acallee_saved; lia)). exact RG9.
  - intros a Ha Hw. rewrite (KV' a Ha Hw). exact (KV a Ha Hw).
Qed.

(* A run from a state with no region keeps every byte. *)
Lemma mac_frame_kept : forall (E : env) rs (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H Wc) m) (mrestrict (w_H Wc) m') -> windows rs = [] ->
  forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H Wc) m' a = aview segs (w_H Wc) m a.
Proof.
  intros E rs m m' HF Hw a Ha. apply (kept_of_frame E rs (w_H Wc) m m' (fun _ => False) HF); [|exact Ha | intros []].
  intros b wlo whi x Hin. rewrite Hw in Hin. destruct Hin.
Qed.

(* ---- what the view keeps ---- *)

Lemma mac_frs_kept : forall m, mac_KV m -> mrx_frs fr Wc m.
Proof.
  intros m KV. pose proof HFRS as (G & RD & ROM).
  pose proof mac_fpl as (F0 & FP & F63 & F30). pose proof mac_sp as (SP1 & SP2 & STK & FRM).
  split; [|split].
  - apply (garr8_frame segs _ _ _ _ G). intros a Ha. rewrite length_map in Ha. fold (mlen fr) in Ha.
    apply mac_mbyte_of_aview. apply KV; mac_lia.
  - apply (trans_rd_ok_view Wc Wc mem2 m _ _ RD).
    + intros a Ha. apply KV; mac_lia.
    + intros s Hs. apply KV; unfold kLowMemEnd, kHighShadowEnd in *; mac_lia.
  - intros a Ha. pose proof (mac_ro_low a Ha) as Hl. rewrite (KV a ltac:(lia) ltac:(mac_lia)). exact (ROM a Ha).
Qed.

Lemma mac_saved : forall m, mac_KV m -> mrx_saved Wc m sp1 regs0.
Proof.
  intros m KV. pose proof mac_sp as (SP1 & SP2 & STK & FRM).
  apply (mrx_saved_kept Wc Wc mem2 m sp1 regs0 HSV). intros a Ha. apply KV; mac_lia.
Qed.

Lemma mac_tw : forall m, mac_KV m -> tw_at TMAP_A (aview segs (w_H Wc) m) Bwc.
Proof.
  intros m KV. pose proof mac_sp as (SP1 & SP2 & STK & FRM).
  apply (tw_kept TMAP_A (aview segs (w_H Wc) mem2)); [exact HTW|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KV; mac_lia.
Qed.

Lemma mac_hregs_kept : forall regs m, mac_rg regs -> mac_KV m -> mrx_hregs fr Wc sp1 regs m.
Proof.
  intros regs m (RG & _) KV. pose proof mac_sp as (SP1 & SP2 & STK & FRM).
  pose proof HHR as (S18 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & P16 & P24 & P32).
  assert (CS : forall q, 18 <= q <= 27 -> acallee_saved q) by (intros q Hq; unfold acallee_saved; lia).
  split; [exact (eq_trans (RG 18 (CS 18 ltac:(lia)) ltac:(lia)) S18)|].
  split; [exact (eq_trans (RG 21 (CS 21 ltac:(lia)) ltac:(lia)) S21)|].
  split; [exact (eq_trans (RG 22 (CS 22 ltac:(lia)) ltac:(lia)) S22)|].
  split; [exact (eq_trans (RG 23 (CS 23 ltac:(lia)) ltac:(lia)) S23)|].
  split; [exact (eq_trans (RG 24 (CS 24 ltac:(lia)) ltac:(lia)) S24)|].
  split; [exact (eq_trans (RG 25 (CS 25 ltac:(lia)) ltac:(lia)) S25)|].
  split; [exact (eq_trans (RG 26 (CS 26 ltac:(lia)) ltac:(lia)) S26)|].
  split; [exact (eq_trans (RG 27 (CS 27 ltac:(lia)) ltac:(lia)) S27)|].
  split; [apply (mrx_spill_kept Wc Wc mem2 m sp1 16 fr 25 P16); intros a Ha; apply KV; mac_lia|].
  split; [apply (mrx_spill_kept Wc Wc mem2 m sp1 24 fr 24 P24); intros a Ha; apply KV; mac_lia|].
  apply (mrx_spill_kept Wc Wc mem2 m sp1 32 fr 21 P32); intros a Ha; apply KV; mac_lia.
Qed.

(* ---- the bytes the compares read ---- *)

Lemma mac_frame_view : forall m, mac_KV m -> forall j, 0 <= j < mlen fr ->
  aview segs (w_H Wc) m (fa + j) = Some (bv_unsigned (nth (Z.to_nat j) (TI.tf_bytes fr) (Z_to_bv 8 0))).
Proof.
  intros m KV j Hj. pose proof mac_fpl as (F0 & FP & F63 & F30). pose proof mac_sp as (SP1 & SP2 & STK & FRM).
  rewrite (KV (fa + j)) by mac_lia. pose proof HFRS as (G & _ & _).
  replace (fa + j) with (fa + Z.of_nat (Z.to_nat j)) by lia.
  apply (mac_garr_view Wc mem2 fa (TI.tf_bytes fr) (Z.to_nat j) G). unfold mlen in Hj. lia.
Qed.

Lemma mac_host_view : forall m, mac_KV m -> forall i, 0 <= i < 6 ->
  aview segs (w_H Wc) m (TRANS_HOST + i) = Some (bv_unsigned (nth (Z.to_nat i) TC.HOST (Z_to_bv 8 0))).
Proof.
  intros m KV i Hi. pose proof (mac_frs_kept m KV) as (_ & _ & ROM).
  rewrite (ROM _ (mac_host_ro i Hi)). exact (mac_host_rom i Hi).
Qed.

Lemma mac_bcast_view : forall m, mac_KV m -> forall i, 0 <= i < 6 ->
  aview segs (w_H Wc) m (TRANS_SPEC_BCAST + i) = Some (bv_unsigned (nth (Z.to_nat i) TC.SPEC_BCAST (Z_to_bv 8 0))).
Proof.
  intros m KV i Hi. pose proof (mac_frs_kept m KV) as (_ & _ & ROM).
  rewrite (ROM _ (mac_bcast_ro i Hi)). exact (mac_bcast_rom i Hi).
Qed.

(* The compare of [x, + 6) (x = fa + k) with [y, + 6) holding l is the model's beq_bytes. *)
Lemma mac_cmp : forall m x y k (l : list byte), mac_KV m -> x = fa + k -> 0 <= k -> k + 6 <= mlen fr ->
  length l = 6%nat ->
  (forall i, 0 <= i < 6 -> aview segs (w_H Wc) m (y + i) = Some (bv_unsigned (nth (Z.to_nat i) l (Z_to_bv 8 0)))) ->
  ((forall i, 0 <= i < 6 -> aview segs (w_H Wc) m (x + i) = aview segs (w_H Wc) m (y + i)) <->
   TC.beq_bytes (TW.sub (TI.tf_bytes fr) k 6) l = true).
Proof.
  intros m x y k l KV -> Hk Hk6 Hl HY.
  assert (LS : length (TW.sub (TI.tf_bytes fr) k 6) = 6%nat) by (apply TWL.length_sub; unfold mlen in Hk6; lia).
  assert (FV : forall i, 0 <= i < 6 ->
    aview segs (w_H Wc) m (fa + k + i) = Some (bv_unsigned (nth (Z.to_nat i) (TW.sub (TI.tf_bytes fr) k 6) (Z_to_bv 8 0)))).
  { intros i Hi. replace (fa + k + i) with (fa + (k + i)) by lia.
    rewrite (mac_frame_view m KV (k + i) ltac:(lia)).
    rewrite (tw_nth_sub (TI.tf_bytes fr) k 6 (Z.to_nat i) (Z_to_bv 8 0)) by (unfold mlen in Hk6; lia).
    do 3 f_equal. lia. }
  rewrite EPI.mrx_beq_iff, (mac_zs6 _ _ LS Hl).
  split; intros H i Hi.
  - specialize (H i Hi). rewrite (FV i Hi), (HY i Hi) in H. injection H as H. exact H.
  - rewrite (FV i Hi), (HY i Hi). f_equal. exact (H i Hi).
Qed.

(* ---- the ranges the compares read, as read ranges ---- *)

Lemma mac_rd_frame : forall m x k, mac_KV m -> x = fa + k -> 0 <= k -> k + 6 <= mlen fr -> decode_rd_ok Wc m x 6.
Proof.
  intros m x k KV -> Hk Hk6. pose proof (mac_frs_kept m KV) as (_ & RD & _).
  apply (trans_rd_ok_sub Wc m fa (mlen fr)); [exact RD | lia | lia | lia].
Qed.

Lemma mac_rd_host : forall ly' S' m md', @AR rc segs B ly' S' Wc m md' -> mac_KV m -> decode_rd_ok Wc m TRANS_HOST 6.
Proof.
  intros ly' S' m md' HAR KV.
  destruct (HCELLS ly') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RH & RD & _).
  destruct HMRX as (_ & _ & HC). destruct (HC ly') as (RH8 & RH16 & RH24 & RD8 & RD16 & RD24 & _).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. replace a with (TRANS_HOST + (a - TRANS_HOST)) by lia.
    rewrite (mac_host_view m KV (a - TRANS_HOST) ltac:(lia)). discriminate.
  - intros x Hx. exists 6. split.
    + eapply (mac_const1 B ly' S' Wc m md'); [exact HAR | exact RH | lia |].
      unfold ACells.shadow_addr, ACells.ASAN_K, TRANS_HOST, shadow_of_addr, SHADOW_OFF in *.
      Z.div_mod_to_equations. lia.
    + unfold saddr_ok, TRANS_HOST in *. right. Z.div_mod_to_equations. lia.
  - intros s' Hs. mac_hull Hs.
    assert (Hc : s' = 0x7fffc208 \/ s' = 0x7fffc209 \/ s' = 0x7fffc20a \/ s' = 0x7fffc20b \/ s' = 0x7fffc20c \/
                 s' = 0x7fffc20d \/ s' = 0x7fffc20e \/ s' = 0x7fffc20f) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ eapply mac_const1_nn; [exact HAR | exact RH | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RH8 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RH16 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RH24 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RD | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RD8 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RD16 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RD24 | lia | reflexivity] ].
  - unfold amem_range, kLowMemEnd, TRANS_HOST. lia.
  - unfold TRANS_HOST. lia.
  - unfold TRANS_HOST. lia.
Qed.

Lemma mac_rd_bcast : forall ly' S' m md', @AR rc segs B ly' S' Wc m md' -> mac_KV m ->
  decode_rd_ok Wc m TRANS_SPEC_BCAST 6.
Proof.
  intros ly' S' m md' HAR KV.
  destruct (HCELLS ly') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RB & RO & _).
  destruct HMRX as (_ & _ & HC).
  destruct (HC ly') as (_ & _ & _ & _ & _ & _ & RB8 & RB16 & RB24 & RO8 & RO16 & RO24 & _).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. replace a with (TRANS_SPEC_BCAST + (a - TRANS_SPEC_BCAST)) by lia.
    rewrite (mac_bcast_view m KV (a - TRANS_SPEC_BCAST) ltac:(lia)). discriminate.
  - intros x Hx. exists 6. split.
    + eapply (mac_const1 B ly' S' Wc m md'); [exact HAR | exact RB | lia |].
      unfold ACells.shadow_addr, ACells.ASAN_K, TRANS_SPEC_BCAST, shadow_of_addr, SHADOW_OFF in *.
      Z.div_mod_to_equations. lia.
    + unfold saddr_ok, TRANS_SPEC_BCAST in *. right. Z.div_mod_to_equations. lia.
  - intros s' Hs. mac_hull Hs.
    assert (Hc : s' = 0x7fffc210 \/ s' = 0x7fffc211 \/ s' = 0x7fffc212 \/ s' = 0x7fffc213 \/ s' = 0x7fffc214 \/
                 s' = 0x7fffc215 \/ s' = 0x7fffc216 \/ s' = 0x7fffc217) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ eapply mac_const1_nn; [exact HAR | exact RB | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RB8 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RB16 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RB24 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RO | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RO8 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RO16 | lia | reflexivity]
      | eapply mac_const1_nn; [exact HAR | exact RO24 | lia | reflexivity] ].
  - unfold amem_range, kLowMemEnd, TRANS_SPEC_BCAST. lia.
  - unfold TRANS_SPEC_BCAST. lia.
  - unfold TRANS_SPEC_BCAST. lia.
Qed.

(* ---- the exits ---- *)

Lemma mac_exit_epi : forall regs m md, mac_mid regs m md -> YK11.getr regs 10 = w64 0 -> Bw' = Bwc -> r = 0 ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (MRX_PC OFF_EPI)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md (HJ & RG & KV) R10 EB Er. pose proof RG as (RGS & _).
  apply (KE Wc Bwc).
  apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_EPI) (R_EPI Bw' r) Wc Bwc lyc Sc regs m md HJ).
  - reflexivity.
  - apply Permutation_refl.
  - exact HMO2.
  - exact (eq_trans (RGS 2 ltac:(unfold acallee_saved; lia) ltac:(lia)) H2).
  - exact (eq_trans (RGS 3 ltac:(unfold acallee_saved; lia) ltac:(lia)) H3).
  - exact (eq_trans (RGS 4 ltac:(unfold acallee_saved; lia) ltac:(lia)) H4).
  - exact (mac_saved m KV).
  - exact (mac_tw m KV).
  - unfold R_EPI. split; [symmetry; exact EB | rewrite Er; exact R10].
Qed.

Lemma mac_exit_desk : forall regs m md, mac_mid regs m md -> EPI.mrx_desk_m timg_A fr Bwc = Some (Bw', r) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (MRX_PC OFF_DESK)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md (HJ & RG & KV) HD. pose proof RG as (RGS & RG9).
  apply (KD Wc Bwc).
  apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_DESK) (R_DESK fr n sp1 lyc Sc Bw' r) Wc Bwc lyc Sc
    regs m md HJ).
  - reflexivity.
  - apply Permutation_refl.
  - exact HMO2.
  - exact (eq_trans (RGS 2 ltac:(unfold acallee_saved; lia) ltac:(lia)) H2).
  - exact (eq_trans (RGS 3 ltac:(unfold acallee_saved; lia) ltac:(lia)) H3).
  - exact (eq_trans (RGS 4 ltac:(unfold acallee_saved; lia) ltac:(lia)) H4).
  - exact (mac_saved m KV).
  - exact (mac_tw m KV).
  - unfold R_DESK. split; [reflexivity|]. split; [reflexivity|]. split; [exact (mac_frs_kept m KV)|].
    split; [exact HHDR|].
    split; [exact (eq_trans (RGS 8 ltac:(unfold acallee_saved; lia) ltac:(lia)) H8)|].
    split; [exact RG9|].
    split; [exact (eq_trans (RGS 19 ltac:(unfold acallee_saved; lia) ltac:(lia)) H19)|].
    split; [exact (eq_trans (RGS 20 ltac:(unfold acallee_saved; lia) ltac:(lia)) H20)|].
    split; [exact (mac_hregs_kept regs m RG KV) | exact HD].
Qed.

(* ---- one call of the bcmp wrapper (the kit's mrx_bcmp_gx) ---- *)

Lemma mac_bcmp : forall (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model) (x y : Z) (raw : word)
    (Q : world segs -> config -> Prop),
  mac_mid regsT memT mdT ->
  YK11.getr regsT 10 = w64 x -> YK11.getr regsT 11 = w64 y -> YK11.getr regsT 12 = w64 6 ->
  decode_rd_ok Wc memT x 6 -> decode_rd_ok Wc memT y 6 ->
  (x + 6 <= sp1 - MRX_STK \/ sp1 <= x) -> (y + 6 <= sp1 - MRX_STK \/ sp1 <= y) ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall regs3 mem3 md3, mac_mid regs3 mem3 md3 ->
     (YK11.getr regs3 10 = w64 0 <->
        forall i, 0 <= i < 6 -> aview segs (w_H Wc) memT (x + i) = aview segs (w_H Wc) memT (y + i)) ->
     SRr segs Wc (mkCfg (@YK11.mkst fx regs3 raw mem3 (YK11.seg_rom segs)) md3) Q) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) memT
    (YK11.seg_rom segs)) mdT) Q.
Proof.
  intros regsT memT mdT x y raw Q MID R10 R11 R12 RDX RDY OFX OFY R1 HRAW KK.
  pose proof MID as (HJ & (RG & RG9) & KV).
  pose proof mac_sp as (SP1 & SP2 & STK & FRM).
  pose proof RDX as (HvX & HraX & HhX & HmX & H0X & H63X).
  pose proof RDY as (HvY & HraY & HhY & HmY & H0Y & H63Y).
  pose proof HST as (_ & _ & _ & _ & _ & _ & _ & Hg0 & Ht0 & _).
  assert (R2 : YK11.getr regsT 2 = Z_to_bv 64 (sp1 - MRX_FRAME))
    by exact (eq_trans (RG 2 ltac:(unfold acallee_saved; lia) ltac:(lia)) H2).
  assert (HspT : spZ regsT = sp1 + -144)
    by (unfold spZ; rewrite R2; rewrite unsigned_lit_small; [unfold MRX_FRAME; lia | unfold MRX_FRAME; lia]).
  assert (R3 : YK11.getr regsT 3 = w64 (as_gp B)).
  { rewrite <- Hg0. exact (eq_trans (RG 3 ltac:(unfold acallee_saved; lia) ltac:(lia)) H3). }
  assert (R4 : YK11.getr regsT 4 = w64 (as_tp B)).
  { rewrite <- Ht0. exact (eq_trans (RG 4 ltac:(unfold acallee_saved; lia) ltac:(lia)) H4). }
  assert (SX : src_ok segs Wc regsT memT x 6)
    by (intros a Ha; split; [exact (HvX a Ha) | rewrite HspT; unfold ESTACK; lia]).
  assert (SY : src_ok segs Wc regsT memT y 6)
    by (intros a Ha; split; [exact (HvY a Ha) | rewrite HspT; unfold ESTACK; lia]).
  assert (BX : forall a, x <= a < x + 6 -> ~ (sp1 + -144 - 2 * ESTACK <= a < sp1 + -144)) by (intros a Ha; unfold ESTACK; lia).
  assert (BY : forall a, y <= a < y + 6 -> ~ (sp1 + -144 - 2 * ESTACK <= a < sp1 + -144)) by (intros a Ha; unfold ESTACK; lia).
  eapply SRr_bind.
  { exact (mrx_bcmp_gx B LAWS _ (HBCMP fx) Wc regsT memT MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc mdT 0 x y 6 (-144) raw
      HJ R10 R11 R12 ltac:(lia) H0X H63X H0Y H63Y HspT eq_refl ltac:(lia) ltac:(rewrite STK; unfold ESTACK; lia)
      R3 R4 R1 HRAW SX SY BX BY HmX HmY HraX (fun _ => HhX) HraY (fun _ => HhY)). }
  cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hiff & Hview & _).
  apply (KK regs3 mem3 md3); [|exact Hiff].
  apply (mac_mid_step regsT memT mdT regs3 mem3 md3 MID HP3); [|exact HJ3].
  intros a Ha Hw. apply Hview; [exact Ha|]. unfold mac_win in Hw. unfold ESTACK. lia.
Qed.

(* ---- the phases ---- *)

(* After the third call (0x84b04, bnez a0): a0 <> 0 goes to 0x84968 (a0 = 0) and the epilogue; a0 = 0 to DESK. *)
Lemma mac_p3 : forall regs m md, mac_mid regs m md ->
  TC.beq_bytes (EPI.mrx_src fr) TC.HOST = false -> TC.beq_bytes (EPI.mrx_dst fr) TC.HOST = false ->
  (YK11.getr regs 10 = w64 0 <-> TC.beq_bytes (EPI.mrx_dst fr) TC.SPEC_BCAST = true) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14496)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md MID E1 E2 IFF.
  pose proof MID as (HJ & RG & KV).
  destruct mac_vals as (_ & _ & _ & PEPI & PDESK).
  pose proof (mac_img regs) as HEI. pose proof (mac_agree regs) as AG.
  pose proof (mac_entry (w_H Wc) regs m 14496) as HS.
  assert (SHOK : sh_ok segs MAC_Bx MAC_SH (mac_E regs) (mrestrict (w_H Wc) m)) by (unfold sh_ok, MAC_SH; apply Forall_nil).
  pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* a0 <> 0: dst is not SPEC_BCAST; 0x84968 a0 = 0, then the epilogue *)
    apply (proj1 (mac_br_ne regs)) in Hc.
    assert (E3 : TC.beq_bytes (EPI.mrx_dst fr) TC.SPEC_BCAST = false).
    { destruct (TC.beq_bytes (EPI.mrx_dst fr) TC.SPEC_BCAST) eqn:E3; [|reflexivity].
      exfalso. apply Hc. apply IFF. reflexivity. }
    destruct (mac_m_bc_no _ _ _ _ _ E1 E2 E3 HM) as [EB Er].
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14088.
    { mac_awr. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (mac_E regs) _ ms regs [w64 SHADOW_OFF] HS AG);
          vm_compute; reflexivity).
    pose proof (mac_mid_step regs m md (ms_regs ms) (ms_mem ms) md' MID HP
      (fun a Ha _ => mac_frame_kept _ _ _ _ HFr eq_refl a Ha) HJ) as MID'.
    mac_reg HS (Z_to_bv 5 10) (w64 0) R10 ltac:(reflexivity).
    pmkst HS. rewrite PEPI.
    exact (mac_exit_epi (ms_regs ms) (ms_mem ms) md' MID' R10 EB Er).
  - (* a0 = 0: dst is SPEC_BCAST; DESK *)
    apply mac_br_ne_f in Hc.
    assert (E3 : TC.beq_bytes (EPI.mrx_dst fr) TC.SPEC_BCAST = true) by (apply IFF; exact Hc).
    pose proof (mac_m_bc_yes _ _ _ _ _ E1 E2 E3 HM) as HD.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14500.
    { mac_awr. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (mac_E regs) _ ms regs [w64 SHADOW_OFF] HS AG);
          vm_compute; reflexivity).
    pose proof (mac_mid_step regs m md (ms_regs ms) (ms_mem ms) md' MID HP
      (fun a Ha _ => mac_frame_kept _ _ _ _ HFr eq_refl a Ha) HJ) as MID'.
    pmkst HS. rewrite PDESK.
    exact (mac_exit_desk (ms_regs ms) (ms_mem ms) md' MID' HD).
Qed.

(* After the second call (0x84aec, beqz a0): a0 = 0 goes to DESK; else the third call (0x84af0 - 0x84b00). *)
Lemma mac_p2 : forall regs m md, mac_mid regs m md ->
  TC.beq_bytes (EPI.mrx_src fr) TC.HOST = false ->
  (YK11.getr regs 10 = w64 0 <-> TC.beq_bytes (EPI.mrx_dst fr) TC.HOST = true) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14472)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md MID E1 IFF.
  pose proof MID as (HJ & RG & KV).
  destruct mac_vals as (V6 & V16 & _ & PEPI & PDESK).
  pose proof mac_fpl as (F0 & FP & F63 & F30). pose proof mac_sp as (SP1 & SP2 & STK & FRM).
  assert (S0 : YK11.getr regs (Z_to_bv 5 8) = w64 fa)
    by exact (eq_trans (proj1 RG 8 ltac:(unfold acallee_saved; lia) ltac:(lia)) H8).
  pose proof (mac_img regs) as HEI. pose proof (mac_agree regs) as AG.
  pose proof (mac_entry (w_H Wc) regs m 14472) as HS.
  assert (SHOK : sh_ok segs MAC_Bx MAC_SH (mac_E regs) (mrestrict (w_H Wc) m)) by (unfold sh_ok, MAC_SH; apply Forall_nil).
  pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* a0 = 0: dst is HOST; DESK *)
    apply (proj1 (mac_br_eq regs)) in Hc.
    pose proof (mac_m_dsth _ _ _ _ _ E1 (proj1 IFF Hc) HM) as HD.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14500.
    { mac_awr. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (mac_E regs) _ ms regs [w64 SHADOW_OFF] HS AG);
          vm_compute; reflexivity).
    pose proof (mac_mid_step regs m md (ms_regs ms) (ms_mem ms) md' MID HP
      (fun a Ha _ => mac_frame_kept _ _ _ _ HFr eq_refl a Ha) HJ) as MID'.
    pmkst HS. rewrite PDESK.
    exact (mac_exit_desk (ms_regs ms) (ms_mem ms) md' MID' HD).
  - (* a0 <> 0: dst is not HOST; a0 = fa, a1 = SPEC_BCAST, a2 = 6, `jal bcmp` *)
    apply mac_br_eq_f in Hc.
    assert (E2 : TC.beq_bytes (EPI.mrx_dst fr) TC.HOST = false).
    { destruct (TC.beq_bytes (EPI.mrx_dst fr) TC.HOST) eqn:E2; [|reflexivity].
      exfalso. apply Hc. apply IFF. reflexivity. }
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mac_awr. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (mac_E regs) _ ms regs [w64 SHADOW_OFF] HS AG);
          vm_compute; reflexivity).
    pose proof (mac_mid_step regs m md (ms_regs ms) (ms_mem ms) md' MID HP
      (fun a Ha _ => mac_frame_kept _ _ _ _ HFr eq_refl a Ha) HJ) as MID'.
    mac_reg HS (Z_to_bv 5 10) (w64 fa) Ra0 ltac:(apply (mac_sv_reg0 regs 8 (Z_to_bv 5 8) fa eq_refl S0); lia).
    mac_reg HS (Z_to_bv 5 11) (w64 TRANS_SPEC_BCAST) Ra1
      ltac:(apply (mac_sv_obj regs (A_OBJ 16) TRANS_SPEC_BCAST);
            [unfold A_OBJ, A_TEXT, A_LIM; lia | exact V16 | unfold TRANS_SPEC_BCAST; lia]).
    mac_reg HS (Z_to_bv 5 12) (w64 6) Ra2 ltac:(reflexivity).
    mac_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14496)) Rra ltac:(apply codeptr_val; exact HEI).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) mm rom)
        mdx) Q) end.
    pose proof MID' as (HJ' & _ & KV').
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ') as HAR'.
    apply (mac_bcmp (ms_regs ms) (ms_mem ms) md' fa TRANS_SPEC_BCAST (Z_to_bv 64 (BASE + 14496)) _ MID' Ra0 Ra1 Ra2
      (mac_rd_frame (ms_mem ms) fa 0 KV' ltac:(lia) ltac:(lia) ltac:(lia)) (mac_rd_bcast _ _ _ _ HAR' KV')
      ltac:(lia) ltac:(left; unfold TRANS_SPEC_BCAST; lia) Rra
      (ret_ok_codeptr_v (PI := PI_transport) 14496 ltac:(lia) eq_refl)).
    intros regs3 mem3 md3 MID3 IFF3.
    apply (mac_p3 regs3 mem3 md3 MID3 E1 E2).
    exact (iff_trans IFF3 (mac_cmp (ms_mem ms) fa TRANS_SPEC_BCAST 0 TC.SPEC_BCAST KV' ltac:(lia) ltac:(lia) ltac:(lia)
      eq_refl (mac_bcast_view (ms_mem ms) KV'))).
Qed.

(* After the first call (0x84ad4, beqz a0): a0 = 0 goes to the epilogue with a0 = 0; else the second call
   (0x84ad8 - 0x84ae8). *)
Lemma mac_p1 : forall regs m md, mac_mid regs m md ->
  (YK11.getr regs 10 = w64 0 <-> TC.beq_bytes (EPI.mrx_src fr) TC.HOST = true) ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 14448)) m (YK11.seg_rom segs)) md) IPOST.
Proof.
  intros regs m md MID IFF.
  pose proof MID as (HJ & RG & KV).
  destruct mac_vals as (V6 & V16 & _ & PEPI & PDESK).
  pose proof mac_fpl as (F0 & FP & F63 & F30). pose proof mac_sp as (SP1 & SP2 & STK & FRM).
  assert (S0 : YK11.getr regs (Z_to_bv 5 8) = w64 fa)
    by exact (eq_trans (proj1 RG 8 ltac:(unfold acallee_saved; lia) ltac:(lia)) H8).
  pose proof (mac_img regs) as HEI. pose proof (mac_agree regs) as AG.
  pose proof (mac_entry (w_H Wc) regs m 14448) as HS.
  assert (SHOK : sh_ok segs MAC_Bx MAC_SH (mac_E regs) (mrestrict (w_H Wc) m)) by (unfold sh_ok, MAC_SH; apply Forall_nil).
  pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* a0 = 0: src is HOST; the epilogue with a0 = 0 *)
    apply (proj1 (mac_br_eq regs)) in Hc.
    destruct (mac_m_src _ _ _ _ _ (proj1 IFF Hc) HM) as [EB Er].
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 14088.
    { mac_awr. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (mac_E regs) _ ms regs [w64 SHADOW_OFF] HS AG);
          vm_compute; reflexivity).
    pose proof (mac_mid_step regs m md (ms_regs ms) (ms_mem ms) md' MID HP
      (fun a Ha _ => mac_frame_kept _ _ _ _ HFr eq_refl a Ha) HJ) as MID'.
    mac_reg HS (Z_to_bv 5 10) (w64 0) Ra0 ltac:(rewrite mac_sv_a0; exact Hc).
    pmkst HS. rewrite PEPI.
    exact (mac_exit_epi (ms_regs ms) (ms_mem ms) md' MID' Ra0 EB Er).
  - (* a0 <> 0: src is not HOST; a0 = fa, a1 = HOST, a2 = 6, `jal bcmp` *)
    apply mac_br_eq_f in Hc.
    assert (E1 : TC.beq_bytes (EPI.mrx_src fr) TC.HOST = false).
    { destruct (TC.beq_bytes (EPI.mrx_src fr) TC.HOST) eqn:E1; [|reflexivity].
      exfalso. apply Hc. apply IFF. reflexivity. }
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { mac_awr. }
    set (md' := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md'. clear mat.
    assert (HP : aregs_preserved regs (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok segs (w_H Wc) (mac_E regs) _ ms regs [w64 SHADOW_OFF] HS AG);
          vm_compute; reflexivity).
    pose proof (mac_mid_step regs m md (ms_regs ms) (ms_mem ms) md' MID HP
      (fun a Ha _ => mac_frame_kept _ _ _ _ HFr eq_refl a Ha) HJ) as MID'.
    mac_reg HS (Z_to_bv 5 10) (w64 fa) Ra0 ltac:(apply (mac_sv_reg0 regs 8 (Z_to_bv 5 8) fa eq_refl S0); lia).
    mac_reg HS (Z_to_bv 5 11) (w64 TRANS_HOST) Ra1
      ltac:(apply (mac_sv_obj regs (A_OBJ 6) TRANS_HOST);
            [unfold A_OBJ, A_TEXT, A_LIM; lia | exact V6 | unfold TRANS_HOST; lia]).
    mac_reg HS (Z_to_bv 5 12) (w64 6) Ra2 ltac:(reflexivity).
    mac_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14472)) Rra ltac:(apply codeptr_val; exact HEI).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) mm rom)
        mdx) Q) end.
    pose proof MID' as (HJ' & _ & KV').
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ') as HAR'.
    apply (mac_bcmp (ms_regs ms) (ms_mem ms) md' fa TRANS_HOST (Z_to_bv 64 (BASE + 14472)) _ MID' Ra0 Ra1 Ra2
      (mac_rd_frame (ms_mem ms) fa 0 KV' ltac:(lia) ltac:(lia) ltac:(lia)) (mac_rd_host _ _ _ _ HAR' KV')
      ltac:(lia) ltac:(left; unfold TRANS_HOST; lia) Rra
      (ret_ok_codeptr_v (PI := PI_transport) 14472 ltac:(lia) eq_refl)).
    intros regs3 mem3 md3 MID3 IFF3.
    apply (mac_p2 regs3 mem3 md3 MID3 E1).
    exact (iff_trans IFF3 (mac_cmp (ms_mem ms) fa TRANS_HOST 0 TC.HOST KV' ltac:(lia) ltac:(lia) ltac:(lia)
      eq_refl (mac_host_view (ms_mem ms) KV'))).
Qed.

(* From the cut MAC: run 1 (0x84abc - 0x84ad0: s1 = fa + 6, a1 = HOST, a2 = 6, a0 = s1, `jal bcmp`), the first
   call, then mac_p1. *)
Lemma mac_walk : forall md2,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc Wc mem2
    md2 0 ->
  SRr segs Wc (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (MRX_PC OFF_MAC)) mem2 (YK11.seg_rom segs)) md2) IPOST.
Proof using All.
  intros md2 HJ.
  destruct mac_vals as (V6 & V16 & PMAC & PEPI & PDESK).
  pose proof mac_fpl as (F0 & FP & F63 & F30). pose proof mac_sp as (SP1 & SP2 & STK & FRM).
  rewrite <- PMAC.
  pose proof (mac_img regs2) as HEI. pose proof (mac_agree regs2) as AG.
  pose proof (mac_entry (w_H Wc) regs2 mem2 14424) as HS.
  assert (SHOK : sh_ok segs MAC_Bx MAC_SH (mac_E regs2) (mrestrict (w_H Wc) mem2))
    by (unfold sh_ok, MAC_SH; apply Forall_nil).
  pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUN.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { mac_awr. }
  set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
  pose proof (regs_kept_of_st_ok segs (mac_E regs2) _ _ regs2 [w64 SHADOW_OFF] MAC_KEEP HS AG
    ltac:(vm_compute; reflexivity)) as KP.
  mac_reg HS (Z_to_bv 5 9) (w64 (fa + 6)) Rs1 ltac:(apply (mac_sv_reg regs2 8 (Z_to_bv 5 8) 6 fa eq_refl H8); lia).
  mac_reg HS (Z_to_bv 5 10) (w64 (fa + 6)) Ra0 ltac:(apply (mac_sv_reg regs2 8 (Z_to_bv 5 8) 6 fa eq_refl H8); lia).
  mac_reg HS (Z_to_bv 5 11) (w64 TRANS_HOST) Ra1
    ltac:(apply (mac_sv_obj regs2 (A_OBJ 6) TRANS_HOST);
          [unfold A_OBJ, A_TEXT, A_LIM; lia | exact V6 | unfold TRANS_HOST; lia]).
  mac_reg HS (Z_to_bv 5 12) (w64 6) Ra2 ltac:(reflexivity).
  mac_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14448)) Rra ltac:(apply codeptr_val; exact HEI).
  assert (MID1 : mac_mid (ms_regs ms) (ms_mem ms) md1).
  { split; [exact HJ|]. split; [split|].
    - intros q Hq H9. apply (KP (Z_to_bv 5 q)). unfold MAC_KEEP. apply in_map. unfold acallee_saved in Hq.
      cbn [In]. lia.
    - exact Rs1.
    - intros a Ha _. exact (mac_frame_kept _ _ _ _ HFr eq_refl a Ha). }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) mm rom)
      mdx) Q) end.
  pose proof MID1 as (_ & _ & KV1).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
  apply (mac_bcmp (ms_regs ms) (ms_mem ms) md1 (fa + 6) TRANS_HOST (Z_to_bv 64 (BASE + 14448)) _ MID1 Ra0 Ra1 Ra2
    (mac_rd_frame (ms_mem ms) (fa + 6) 6 KV1 eq_refl ltac:(lia) ltac:(lia)) (mac_rd_host _ _ _ _ HAR1 KV1)
    ltac:(lia) ltac:(left; unfold TRANS_HOST; lia) Rra
    (ret_ok_codeptr_v (PI := PI_transport) 14448 ltac:(lia) eq_refl)).
  intros regs3 mem3 md3 MID3 IFF3.
  apply (mac_p1 regs3 mem3 md3 MID3).
  exact (iff_trans IFF3 (mac_cmp (ms_mem ms) (fa + 6) TRANS_HOST 6 TC.HOST KV1 eq_refl ltac:(lia) ltac:(lia)
    eq_refl (mac_host_view (ms_mem ms) KV1))).
Qed.

End cut.

(* The segment MAC: from the cut MAC to the cuts EPI and DESK. *)
Lemma mrx_seg_mac :
  K (MRX_PC OFF_EPI) (R_EPI Bw' r) ->
  K (MRX_PC OFF_DESK) (R_DESK fr n sp1 lyc Sc Bw' r) ->
  K (MRX_PC OFF_MAC) (R_MAC fr n sp1 lyc Sc Bw' r).
Proof using All.
  intros KE KD Wc Bwc c HAT.
  destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HFR & HPM & HMO2 & HSP & HGP & HTP & HSV & HTW & HR).
  destruct HR as (-> & -> & HFRS & HHDR & H8 & H19 & H20 & HHR & HM).
  exact (mac_walk Wc Bwc regs2 mem2 KE KD HMO2 HSV HTW HFRS HHDR HSP HGP HTP H8 H19 H20 HHR HM md2 HJ).
Qed.

End seg.
