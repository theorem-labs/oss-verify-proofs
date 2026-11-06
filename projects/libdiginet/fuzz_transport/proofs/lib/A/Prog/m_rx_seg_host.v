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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_mac.v; 579 of its 709 lines of code are new or changed and 709 lines of the source are left out. *)
(* m_rx_seg_host: the HOST segment of the image-A walk of m_rx (statement lib/A/Prog/m_rx_cg.v, kit
   lib/A/Prog/m_rx_seg_kit.v): host_offset, inlined at 0x84bbc - 0x84bf4 and 0x84da4 (cmd e1, body_len >= 33).

   mrx_seg_host: from the cut HOST (MRX_PC OFF_HOST, R_HOST) the run reaches the cut ANNT (MRX_PC OFF_ANNT, R_ANNT),
   so the continuation of ANNT gives the continuation of HOST.
   - host_entry, 0x84bbc - 0x84bcc: s5 = 0, s6 = 10, s1 = HOST (A_OBJ 6 = TRANS_HOST), s2 = s0 = fa + 30; then the
     loop head 0x84bd0 (MRX_PC 0x344) with the cut R_LOOP 0. The model: mrx_ann at cmd e1 is host_offset's loop
     (TCb.v host_offset_loop 10 body 0 = Some off), then mrx_ann_tail off (host_ann).
   - host_round i (0 <= i <= 9), from the loop head: a2 = 6, a0 = s2, a1 = s1; the bcmp wrapper at 0x84bdc with
     (fa + 30 + i, HOST, 6) (host_bcmp: the kit's mrx_bcmp_gx; the frame range from mrx_frs, HOST's bytes from the
     read-only view, HOST's shadow from transport_cells and trans_mrx_cells); its result is 0 exactly when the model's
     memcmp of body bytes i .. i + 5 with HOST is (host_beq). Result 0: `mv s4, s5` (0x84da4) and ANNT with off = i.
     Else s5 = i + 1 (addiw), s6 = 9 - i, s2 = fa + 31 + i, `bnez s6`: back to the loop head with R_LOOP (i + 1), or
     after the tenth round the `j` at 0x84bf4 to ANNT with s4 = -1.
   - host_loop: by induction on the rounds left.
   Every run starts from a fresh symbolic state of the machine's registers with no region (the code reads and writes
   no memory); a run and the wrapper keep every byte outside the wrapper's stack window (host_kept), so the frame's
   facts, the saved slots and the world relation carry over (host_frs_kept, host_saved_kept, host_tw_kept). *)
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
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- the symbolic states the segment starts from ---- *)

(* Every run of this segment starts from the registers of a concrete machine state (atoms 0 .. 31) and the shadow base
   (atom 32), with no region: the code of the segment reads and writes no memory. *)
Definition host_Bx : sv := SOff 32 0.
Definition host_SH : list shent := [].
Definition host_facts : facts := mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition host_ss (off : Z) : sstate := mkSS (AF_m_rx + off) sr_atoms [] None host_facts.

(* ---- the model ---- *)

(* The six bytes of HOST (TCb.v HOST), as numbers. *)
Definition host_bytes : list Z := [2; 0; 0; 0; 0; 1].

Lemma host_zs : TW.zs TC.HOST = host_bytes.
Proof. vm_compute. reflexivity. Qed.

Lemma host_nth_skipn : forall (A : Type) (l : list A) (k j : nat) (d : A), nth j (skipn k l) d = nth (k + j) l d.
Proof.
intros A l. induction l as [|x l IH]; intros k j d.
- destruct k, j; reflexivity.
- destruct k as [|k]; [reflexivity | exact (IH k j d)].
Qed.

Lemma host_nth_firstn : forall (A : Type) (l : list A) (k j : nat) (d : A), (j < k)%nat ->
  nth j (firstn k l) d = nth j l d.
Proof.
intros A l. induction l as [|x l IH]; intros k j d Hj.
- destruct k, j; reflexivity.
- destruct k as [|k]; [lia|]. destruct j as [|j]; [reflexivity|]. exact (IH k j d ltac:(lia)).
Qed.

Lemma host_map_firstn : forall (A C : Type) (f : A -> C) k l, map f (firstn k l) = firstn k (map f l).
Proof.
intros A C f k. induction k as [|k IH]; intros l; [reflexivity|].
destruct l as [|x l]; [reflexivity|]. cbn [firstn map]. f_equal. apply IH.
Qed.

Lemma host_map_skipn : forall (A C : Type) (f : A -> C) k l, map f (skipn k l) = skipn k (map f l).
Proof.
intros A C f k. induction k as [|k IH]; intros l; [reflexivity|].
destruct l as [|x l]; [reflexivity|]. cbn [skipn map]. apply IH.
Qed.

(* Byte j of the 6 bytes at offset i of m_rx's body is frame byte 30 + i + j. *)
Lemma host_sub_nth : forall (fr : TI.tframe) i j, 0 <= i -> 0 <= j < 6 ->
  nth (Z.to_nat j) (TW.zs (TW.sub (EPI.mrx_body fr) i 6)) 0 = mfb fr (30 + i + j).
Proof.
intros fr i j Hi Hj. unfold TW.zs, TW.sub, EPI.mrx_body, mfb, DSpec.byte_at.
rewrite host_map_firstn, !host_map_skipn.
rewrite host_nth_firstn by lia. rewrite !host_nth_skipn.
f_equal. lia.
Qed.

Lemma host_sub_len : forall (fr : TI.tframe) i, 0 <= i -> 36 + i <= mlen fr ->
  length (TW.zs (TW.sub (EPI.mrx_body fr) i 6)) = 6%nat.
Proof.
intros fr i Hi Hl. unfold TW.zs, TW.sub, EPI.mrx_body. unfold mlen in Hl.
rewrite length_map, length_firstn, !length_skipn. lia.
Qed.

(* memcmp (body + i, HOST, 6) == 0 in the model, byte by byte. *)
Lemma host_beq : forall (fr : TI.tframe) i, 0 <= i -> 36 + i <= mlen fr ->
  (TC.beq_bytes (TW.sub (EPI.mrx_body fr) i 6) TC.HOST = true <->
   forall j, 0 <= j < 6 -> mfb fr (30 + i + j) = nth (Z.to_nat j) host_bytes 0).
Proof.
intros fr i Hi Hl. unfold TC.beq_bytes. rewrite host_zs.
destruct (list_eq_dec Z.eq_dec (TW.zs (TW.sub (EPI.mrx_body fr) i 6)) host_bytes) as [E|E].
- split; [intros _ j Hj | intros _; reflexivity]. rewrite <- (host_sub_nth fr i j Hi Hj), E. reflexivity.
- split; [intros H; discriminate H|]. intros H. exfalso. apply E.
  apply (nth_ext _ _ 0 0); [rewrite (host_sub_len fr i Hi Hl); reflexivity|].
  intros k Hk. rewrite (host_sub_len fr i Hi Hl) in Hk.
  pose proof (host_sub_nth fr i (Z.of_nat k) Hi ltac:(lia)) as Hn. rewrite Nat2Z.id in Hn. rewrite Hn.
  specialize (H (Z.of_nat k) ltac:(lia)). rewrite Nat2Z.id in H. exact H.
Qed.

(* One round of host_offset's loop (TCb.v:215-224) at i <= 9 with the 6 bytes inside the body. *)
Lemma host_step : forall k body i off, 0 <= i <= 9 -> i + 6 <= Z.of_nat (length body) ->
  TC.host_offset_loop (S k) body i = Some off ->
  (TC.beq_bytes (TW.sub body i 6) TC.HOST = true /\ off = i) \/
  (TC.beq_bytes (TW.sub body i 6) TC.HOST = false /\ TC.host_offset_loop k body (i + 1) = Some off).
Proof.
intros k body i off Hi Hl H. cbn [TC.host_offset_loop] in H.
rewrite (proj2 (Z.leb_le (i + DSpec.SPEC_MAC) TC.SPEC_ANN_UNKNOWN)) in H
  by (unfold DSpec.SPEC_MAC, TC.SPEC_ANN_UNKNOWN; lia).
rewrite (proj2 (Z.ltb_ge (Z.of_nat (length body)) (i + DSpec.SPEC_MAC))) in H by (unfold DSpec.SPEC_MAC; lia).
cbv iota in H.
destruct (TC.beq_bytes (TW.sub body i 6) TC.HOST) eqn:E; cbv iota in H.
- left. split; [reflexivity|]. injection H as H. symmetry. exact H.
- right. split; [reflexivity | exact H].
Qed.

(* mrx_ann at cmd e1, body_len >= 33: host_offset's loop gives off, then mrx_ann_tail off. *)
Lemma host_ann : forall I (fr : TI.tframe) Bwc B3, mfb fr 28 = TC.SPEC_CMD_E1 -> TC.SPEC_ANN_MIN <= EPI.mrx_blen fr ->
  EPI.mrx_ann I fr Bwc = Some (B3, tt) ->
  exists off, TC.host_offset_loop 10 (EPI.mrx_body fr) 0 = Some off /\ EPI.mrx_ann_tail I fr Bwc off = Some (B3, tt).
Proof.
intros I fr Bwc B3 Hc Hb H. unfold EPI.mrx_ann in H.
rewrite (proj2 (Z.ltb_ge (EPI.mrx_blen fr) TC.SPEC_ANN_MIN) Hb) in H.
rewrite (proj2 (Z.eqb_eq (EPI.mrx_fc fr) TC.SPEC_CMD_E1) Hc) in H.
cbv iota in H. unfold TC.host_offset_m in H.
destruct (TC.host_offset_loop 10 (EPI.mrx_body fr) 0) as [off|]; cbv beta iota in H; [|discriminate H].
exists off. split; [reflexivity | exact H].
Qed.

Lemma host_eqb : forall (a b : word), bv_eqb a b = true <-> a = b.
Proof. intros a b. unfold bv_eqb. rewrite Z.eqb_eq. split; [intros H; apply bv_eq; exact H | intros ->; reflexivity]. Qed.

(* `addiw s5, s5, 1` at s5 = i, 0 <= i <= 9. *)
Lemma host_addiw : forall E i, ew E 21 = w64 i -> 0 <= i <= 9 ->
  sv_denot E (SAluw ALU_ADD (SOff 21 0) (SLit 1)) = w64 (i + 1).
Proof.
intros E i H Hi. cbn [sv_denot]. rewrite H.
assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---- HOST in the read-only image ---- *)

Lemma host_rom : forall j, 0 <= j < 6 ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (TRANS_HOST + j))) =
  Some (nth (Z.to_nat j) host_bytes 0).
Proof.
intros j Hj. assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.

Lemma host_inro : forall a, TRANS_HOST <= a < TRANS_HOST + 6 -> trans_in_ro_rd a.
Proof.
intros a Ha. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_HOST, 6). split.
- unfold TRANS_RO_RD, TRANS_RO_GLOBALS. cbn [app In]. do 5 right. left. reflexivity.
- unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma host_rom_view : forall (Wc : world tfibsegs) m, trans_rom_view_rd Wc m -> forall j, 0 <= j < 6 ->
  aview tfibsegs (w_H Wc) m (TRANS_HOST + j) = Some (nth (Z.to_nat j) host_bytes 0).
Proof.
intros Wc m HR j Hj. rewrite (HR (TRANS_HOST + j) (host_inro (TRANS_HOST + j) ltac:(lia))). exact (host_rom j Hj).
Qed.

(* ---- the symbolic machinery ---- *)

(* The value of register rr in the machine state of a symbolic state HS (m_tick.v mt_reg). *)
Ltac host_reg HS rr v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in
      assert (H : YK11.getr (ms_regs msx) rr = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx rr HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in
      assert (H : YK11.getr (ms_regs msx) rr = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx rr HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "host_reg: no match for" T; fail
  end.
(* A register the run kept: atom nn of the start state, whose register value G gives. *)
Ltac host_kreg EE nn rr G := cbn [sv_denot]; rewrite (EE nn rr eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact G.
(* No region: no write right to give. *)
Ltac host_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.

Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition host_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 SHADOW_OFF]).
Lemma host_base : @pa_val _ transport_listing PI_transport A_TEXT + AF_m_rx = transport_sigma TS_m_rx.
Proof. vm_compute. reflexivity. Qed.
Lemma host_pc : forall off, @pa_val _ transport_listing PI_transport A_TEXT + (AF_m_rx + off) = MRX_PC off.
Proof. intros off. unfold MRX_PC. rewrite <- host_base. lia. Qed.

Lemma host_st : forall (Wx : world tfibsegs) regs mem off,
  st_ok_pi tfibsegs (@pa_val _ transport_listing PI_transport) (host_E regs) (host_ss off)
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (@pa_val _ transport_listing PI_transport A_TEXT + (AF_m_rx + off)))
      mem (YK11.seg_rom tfibsegs))).
Proof.
intros Wx regs mem off. rewrite restrict_mkst_fx. unfold host_ss.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- unfold host_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  assert (E32 : ew (host_E regs) 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold host_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  rewrite E32. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, Z.mod_1_r. repeat split; try exact I; lia.
Qed.
End st.

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
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The loop head 0x84bd0 (MRX_PC 0x344), round i: s5 = i, s6 = 10 - i, s2 = fa + 30 + i, s1 = HOST; the rest as
   HOST's; the model: the rounds left of host_offset's loop give off, then mrx_ann_tail off and m_tick. *)
Definition R_LOOP (i : Z) : world tfibsegs -> list byte -> alayout -> astate -> bvmap 5 word ->
    (word -> option byte) -> Prop :=
  fun Wc Bwc ly2 S2 regs2 mem2 =>
    ly2 = lyc /\ S2 = Sc /\ mrx_frs fr Wc mem2 /\ mrx_hdr fr n /\
    mfb fr 28 = TC.SPEC_CMD_E1 /\ TC.SPEC_ANN_MIN <= EPI.mrx_blen fr /\
    YK11.getr regs2 8 = w64 (TI.tf_addr fr + 30) /\ YK11.getr regs2 19 = w64 TA_M /\
    YK11.getr regs2 20 = w64 (-1) /\ YK11.getr regs2 23 = w64 (TW.M_state Bwc) /\
    YK11.getr regs2 25 = w64 (mfb fr 28) /\
    YK11.getr regs2 9 = w64 TRANS_HOST /\ YK11.getr regs2 18 = w64 (TI.tf_addr fr + 30 + i) /\
    YK11.getr regs2 21 = w64 i /\ YK11.getr regs2 22 = w64 (10 - i) /\
    exists off B3, TC.host_offset_loop (Z.to_nat (10 - i)) (EPI.mrx_body fr) i = Some off /\
      EPI.mrx_ann_tail timg_A fr Bwc off = Some (B3, tt) /\ TC.m_tick_m B3 = Some (Bw', tt) /\ r = 1.

Lemma host_len : mrx_hdr fr n -> TC.SPEC_ANN_MIN <= EPI.mrx_blen fr -> 63 <= n /\ n <= mlen fr.
Proof. intros (H1 & _ & H3) Hb. unfold EPI.mrx_blen, TC.SPEC_ANN_MIN in Hb. lia. Qed.

(* What a run or the bcmp wrapper keeps: every byte outside the wrapper's stack window [sp - 2 * ESTACK, sp), sp the
   segment's sp1 - 144. *)
Definition host_kept (Wc : world tfibsegs) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - MRX_FRAME - 2 * ESTACK <= a < sp1 - MRX_FRAME) ->
    aview tfibsegs (w_H Wc) m' a = aview tfibsegs (w_H Wc) m a.

Lemma host_kept_trans : forall (Wc : world tfibsegs) m1 m2 m3, host_kept Wc m1 m2 -> host_kept Wc m2 m3 ->
  host_kept Wc m1 m3.
Proof. intros Wc m1 m2 m3 K1 K2 a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn). Qed.

Lemma host_kept_run : forall E rs (Wc : world tfibsegs) m m',
  frame_of E rs (mrestrict (w_H Wc) m) (mrestrict (w_H Wc) m') -> rs = [] -> host_kept Wc m m'.
Proof.
intros E rs Wc m m' HFr -> a Ha _.
apply (kept_of_frame E [] (w_H Wc) m m' (fun _ => False) HFr); [| exact Ha | intros []].
intros b wlo whi x Hin _. cbn in Hin. destruct Hin.
Qed.

Lemma host_frs_kept : forall (Wc : world tfibsegs) m m', host_kept Wc m m' -> mrx_frs fr Wc m -> mrx_frs fr Wc m'.
Proof.
intros Wc m m' KP (HG & HD & HR).
pose proof HST as (_ & _ & _ & H46 & H47 & _ & _ & _ & _ & _ & _ & Hfa & _ & _ & Hpl & _).
pose proof HD as (_ & _ & _ & _ & Hq0 & Hq63).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EM : MRX_STK = 8352) by reflexivity. assert (EST : ESTACK = 4096) by reflexivity.
assert (EF : MRX_FRAME = 144) by reflexivity.
assert (KF : forall a, TI.tf_addr fr <= a < TI.tf_addr fr + mlen fr ->
  aview tfibsegs (w_H Wc) m' a = aview tfibsegs (w_H Wc) m a) by (intros a Ha; apply KP; lia).
split; [|split].
- apply (garr8_frame tfibsegs _ _ _ _ HG). intros a Ha. apply mbyte_of_aview. apply KF.
  rewrite length_map in Ha. unfold mlen. exact Ha.
- apply (trans_rd_ok_view Wc Wc m m' _ _ HD KF). intros s Hs. apply KP; lia.
- intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Hb. rewrite (KP a ltac:(lia) ltac:(lia)). exact (HR a Ha).
Qed.

Lemma host_saved_kept : forall (Wc : world tfibsegs) m m', host_kept Wc m m' ->
  mrx_saved Wc m sp1 regs0 -> mrx_saved Wc m' sp1 regs0.
Proof.
intros Wc m m' KP H. pose proof HST as (_ & _ & _ & H46 & H47 & _).
assert (EF : MRX_FRAME = 144) by reflexivity. assert (EST : ESTACK = 4096) by reflexivity.
assert (EM : MRX_STK = 8352) by reflexivity.
apply (mrx_saved_kept Wc Wc m m' sp1 regs0 H). intros a Ha. apply KP; lia.
Qed.

Lemma host_tw_kept : forall (Wc : world tfibsegs) m m' Bw, host_kept Wc m m' ->
  tw_at TMAP_A (aview tfibsegs (w_H Wc) m) Bw -> tw_at TMAP_A (aview tfibsegs (w_H Wc) m') Bw.
Proof.
intros Wc m m' Bw KP H. pose proof HST as (_ & _ & _ & H46 & H47 & _).
assert (EF : MRX_FRAME = 144) by reflexivity. assert (EST : ESTACK = 4096) by reflexivity.
assert (EM : MRX_STK = 8352) by reflexivity.
apply (tw_kept TMAP_A (aview tfibsegs (w_H Wc) m)); [exact H|].
intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
apply KP; lia.
Qed.

(* The frame's byte k, through the view. *)
Lemma host_frame_byte : forall (Wc : world tfibsegs) m, mrx_frs fr Wc m -> forall k, 0 <= k < mlen fr ->
  aview tfibsegs (w_H Wc) m (TI.tf_addr fr + k) = Some (mfb fr k).
Proof.
intros Wc m (HG & _ & _) k Hk.
assert (Hj : (Z.to_nat k < length (map DSpec.bz (TI.tf_bytes fr)))%nat) by (rewrite length_map; unfold mlen in Hk; lia).
pose proof (garr8_mbyte tfibsegs _ _ _ _ HG Hj) as Hb.
destruct (HG _ Hj) as [_ Hr].
rewrite Z2Nat.id in Hb by lia.
unfold aview. rewrite Hb. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by lia.
unfold mfb, DSpec.byte_at, TW.zs, DSpec.bz. reflexivity.
Qed.

(* A one-byte constant cell of the record, read at an AR state. *)
Lemma host_cell1 : forall ly S (Wx : world tfibsegs) mem md a v, @AR rc tfibsegs B ly S Wx mem md ->
  In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> aview tfibsegs (w_H Wx) mem a = Some v.
Proof.
intros ly S Wx mem md a v HAR HC Hv. destruct HAR as (Mm & _).
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mm) _ HC) as Hh.
unfold cell_holds in Hh. cbn [c_at c_w YG0f.c_val z1 c1 aeval] in Hh.
specialize (Hh 0%nat ltac:(lia)). cbn [Z.of_nat] in Hh. rewrite Z.add_0_r in Hh.
rewrite Hh. f_equal. unfold YG0f.le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by discriminate. apply Z.mod_small. exact Hv.
Qed.

(* HOST's shadow facts at every AR state: its granule's shadow byte is 6 (transport_cells), and the 8 shadow bytes of
   its aligned group are HOST's and DESK's (transport_cells) and their guard bytes (trans_mrx_cells). *)
Lemma host_sh : forall ly S (Wx : world tfibsegs) mem md, @AR rc tfibsegs B ly S Wx mem md ->
  range_addressable (aview tfibsegs (w_H Wx) mem) SHADOW_OFF TRANS_HOST 6 /\
  shadow_hull_vis (aview tfibsegs (w_H Wx) mem) TRANS_HOST 6.
Proof.
intros ly S Wx mem md HAR.
destruct (HCELLS ly) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CH & CD & _).
destruct HMRX as (_ & _ & HM). destruct (HM ly) as (H8 & H16 & H24 & D8 & D16 & D24 & _).
pose proof (host_cell1 _ _ _ _ _ _ _ HAR CH ltac:(lia)) as V0.
pose proof (host_cell1 _ _ _ _ _ _ _ HAR H8 ltac:(lia)) as V1.
pose proof (host_cell1 _ _ _ _ _ _ _ HAR H16 ltac:(lia)) as V2.
pose proof (host_cell1 _ _ _ _ _ _ _ HAR H24 ltac:(lia)) as V3.
pose proof (host_cell1 _ _ _ _ _ _ _ HAR CD ltac:(lia)) as V4.
pose proof (host_cell1 _ _ _ _ _ _ _ HAR D8 ltac:(lia)) as V5.
pose proof (host_cell1 _ _ _ _ _ _ _ HAR D16 ltac:(lia)) as V6.
pose proof (host_cell1 _ _ _ _ _ _ _ HAR D24 ltac:(lia)) as V7.
change (ACells.shadow_addr TRANS_HOST) with 2147467784 in V0.
change (ACells.shadow_addr (TRANS_HOST + 8)) with 2147467785 in V1.
change (ACells.shadow_addr (TRANS_HOST + 16)) with 2147467786 in V2.
change (ACells.shadow_addr (TRANS_HOST + 24)) with 2147467787 in V3.
change (ACells.shadow_addr TRANS_DESK) with 2147467788 in V4.
change (ACells.shadow_addr (TRANS_DESK + 8)) with 2147467789 in V5.
change (ACells.shadow_addr (TRANS_DESK + 16)) with 2147467790 in V6.
change (ACells.shadow_addr (TRANS_DESK + 24)) with 2147467791 in V7.
split.
- intros x Hx. exists 6. unfold shadow_of_addr.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  unfold TRANS_HOST in Hx.
  assert (Ex : x / 8 = 16904) by lia.
  rewrite Ex. split; [exact V0 | unfold saddr_ok; right; lia].
- intros s Hs. change (shadow_addr TRANS_HOST / 8 * 8) with 2147467784 in Hs.
  change (shadow_addr (TRANS_HOST + 6 - 1) / 8 * 8 + 8) with 2147467792 in Hs.
  assert (Hc : s = 2147467784 \/ s = 2147467785 \/ s = 2147467786 \/ s = 2147467787 \/ s = 2147467788 \/
               s = 2147467789 \/ s = 2147467790 \/ s = 2147467791) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    [rewrite V0 | rewrite V1 | rewrite V2 | rewrite V3 | rewrite V4 | rewrite V5 | rewrite V6 | rewrite V7];
    discriminate.
Qed.

(* The bcmp wrapper at 0x84bdc with (fa + 30 + i, HOST, 6), from the inner journal: its result is 0 exactly when
   the model's memcmp is, and it keeps every byte outside its stack window. *)
Lemma host_bcmp : forall i (Wc : world tfibsegs) regsT memT mdT, 0 <= i <= 9 ->
  @W_journalG.ajournal_gx rc tfib_sink_head tfibsegs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc []
    lyc Sc Wc memT mdT 0 ->
  mrx_frs fr Wc memT -> mrx_hdr fr n -> TC.SPEC_ANN_MIN <= EPI.mrx_blen fr ->
  YK11.getr regsT 10 = w64 (TI.tf_addr fr + 30 + i) -> YK11.getr regsT 11 = w64 TRANS_HOST ->
  YK11.getr regsT 12 = w64 6 -> YK11.getr regsT 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regsT 3 = YK11.getr regs0 3 -> YK11.getr regsT 4 = YK11.getr regs0 4 ->
  YK11.getr regsT 1 = Z_to_bv 64 (BASE + (AF_m_rx + 0x354)) ->
  SRr tfibsegs Wc (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) memT
      (YK11.seg_rom tfibsegs)) mdT)
    (fun W2 c2 => W2 = Wc /\ exists regs3 mem3 md3,
      c2 = mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + (AF_m_rx + 0x354))) mem3 (YK11.seg_rom tfibsegs)) md3 /\
      @W_journalG.ajournal_gx rc tfib_sink_head tfibsegs B TG.G_HARNESS 0 [] MRX_STK sp1 [] lyc Sc W memc mdc []
        lyc Sc Wc mem3 md3 0 /\
      aregs_preserved regsT regs3 /\
      (YK11.getr regs3 10 = w64 0 <-> TC.beq_bytes (TW.sub (EPI.mrx_body fr) i 6) TC.HOST = true) /\
      host_kept Wc memT mem3).
Proof.
intros i Wc regsT memT mdT Hi HJ Hfrs Hhdr Hblen R10 R11 R12 R2 R3 R4 R1.
pose proof HST as (_ & _ & _ & H46 & H47 & _ & _ & Hgp0 & Htp0 & _ & _ & Hfa & _ & _ & Hpl & _).
pose proof (host_len Hhdr Hblen) as [Hn63 Hnl].
pose proof Hfrs as (HG & HD & HR).
pose proof HD as (_ & _ & _ & _ & Hq0 & Hq63).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EM : MRX_STK = 8352) by reflexivity. assert (EST : ESTACK = 4096) by reflexivity.
assert (EF : MRX_FRAME = 144) by reflexivity.
assert (EH : TRANS_HOST = 135232) by reflexivity.
assert (Hl36 : 36 + i <= mlen fr) by lia.
assert (Hspz : spZ regsT = sp1 + -144).
{ unfold spZ. transitivity (bv_unsigned (Z_to_bv 64 (sp1 - MRX_FRAME))); [f_equal; exact R2|].
  rewrite unsigned_lit_small by lia. lia. }
pose proof (trans_rd_ok_sub Wc memT (TI.tf_addr fr) (mlen fr) (TI.tf_addr fr + 30 + i) 6 HD ltac:(lia) ltac:(lia)
  ltac:(lia)) as (Dv & Dra & Dhull & Dam & _ & _).
pose proof (host_sh _ _ _ _ _ (ajournal_gx_AR tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)) as [Hra Hhull].
eapply SRr_mono.
{ apply (mrx_bcmp_gx B LAWS (transport_sigma TS___interceptor_trampoline_bcmp) (HBCMP fx) Wc regsT memT
    MRX_STK sp1 [] lyc Sc W memc mdc [] lyc Sc mdT 0 (TI.tf_addr fr + 30 + i) TRANS_HOST 6 (-144)
    (Z_to_bv 64 (BASE + (AF_m_rx + 0x354))) HJ R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact Hspz.
  - reflexivity.
  - lia.
  - lia.
  - rewrite R3. exact Hgp0.
  - rewrite R4. exact Htp0.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold AF_m_rx; lia | reflexivity].
  - intros a Ha. split; [apply Dv; exact Ha | rewrite Hspz; lia].
  - intros a Ha. split; [|rewrite Hspz; lia].
    rewrite (HR a (host_inro a Ha)). replace a with (TRANS_HOST + (a - TRANS_HOST)) by lia.
    rewrite (host_rom (a - TRANS_HOST)) by lia. discriminate.
  - intros a Ha. lia.
  - intros a Ha. lia.
  - exact Dam.
  - unfold amem_range. left. lia.
  - exact Dra.
  - intros _. exact Dhull.
  - exact Hra.
  - intros _. exact Hhull. }
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & Hc & HJ3 & HP & Hcmp & Hkeep & _).
split; [reflexivity|]. exists regs3, mem3, md3.
split; [exact Hc|]. split; [exact HJ3|]. split; [exact HP|]. split.
- rewrite (host_beq fr i ltac:(lia) Hl36). split.
  + intros H0 j Hj. pose proof (proj1 Hcmp H0 j Hj) as H.
    replace (TI.tf_addr fr + 30 + i + j) with (TI.tf_addr fr + (30 + i + j)) in H by lia.
    rewrite (host_frame_byte Wc memT Hfrs (30 + i + j) ltac:(lia)), (host_rom_view Wc memT HR j Hj) in H.
    injection H as H. exact H.
  + intros H. apply (proj2 Hcmp). intros j Hj. specialize (H j Hj).
    replace (TI.tf_addr fr + 30 + i + j) with (TI.tf_addr fr + (30 + i + j)) by lia.
    rewrite (host_frame_byte Wc memT Hfrs (30 + i + j) ltac:(lia)), (host_rom_view Wc memT HR j Hj).
    f_equal. exact H.
- intros a Ha Hn. apply Hkeep; [exact Ha | lia].
Qed.

(* Round i of the loop, from the loop head 0x84bd0: a2 = 6, a0 = s2, a1 = s1, the bcmp wrapper; 0 gives s4 = s5 = i
   (0x84da4) and ANNT; else s5 = i + 1, s6 = 9 - i, s2 + 1 and back to the loop head, or after the tenth round ANNT with
   s4 = -1. *)
Lemma host_round : forall i, 0 <= i <= 9 ->
  K (MRX_PC OFF_ANNT) (R_ANNT fr n sp1 lyc Sc Bw' r) ->
  (i < 9 -> K (MRX_PC 0x344) (R_LOOP (i + 1))) ->
  K (MRX_PC 0x344) (R_LOOP i).
Proof.
intros i Hi KA KL Wc Bwc c Hat.
destruct Hat as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hsav & Htw & HR).
destruct HR as (-> & -> & Hfrs & Hhdr & Hcmd & Hblen & G8 & G19 & G20 & G23 & G25 & G9 & G18 & G21 & G22 &
  off & B3 & HO & Htail & Htick & Hr1).
pose proof (host_len Hhdr Hblen) as [Hn63 Hnl].
pose proof HST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfa0 & Hfan & _).
assert (Hlb : i + 6 <= Z.of_nat (length (EPI.mrx_body fr)))
  by (unfold EPI.mrx_body; rewrite length_skipn; unfold mlen in Hnl; lia).
replace (Z.to_nat (10 - i)) with (S (Z.to_nat (10 - (i + 1)))) in HO by lia.
pose proof (host_step _ _ _ _ Hi Hlb HO) as HSTEP. clear HO.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
(* run 1, +0x344 .. +0x350: a2 = 6, a0 = s2, a1 = s1, `jal bcmp` *)
rewrite <- (host_pc 0x344).
pose proof (host_st (fx := fx) (rc := rc) Wc regs2 mem2 0x344) as HS.
set (E0 := host_E regs2) in HS.
assert (EE0 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E0 nn = YK11.getr regs2 rr)
  by (intros nn rr Hn; unfold E0, host_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HEI0 : img_env VAL A_LIM E0) by (unfold E0, host_E; apply Eimg_env).
assert (SHOK : sh_ok tfibsegs host_Bx host_SH E0 (mrestrict (w_H Wc) mem2))
  by (unfold sh_ok, host_SH; apply Forall_nil).
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ host_awr. }
pose proof (host_kept_run _ _ Wc _ _ HFr eq_refl) as KP1. clear HF HFr HG.
pmkst HS.
host_reg HS (Z_to_bv 5 10) (w64 (TI.tf_addr fr + 30 + i)) T10 ltac:(host_kreg EE0 18%nat (Z_to_bv 5 18) G18).
host_reg HS (Z_to_bv 5 11) (w64 TRANS_HOST) T11 ltac:(host_kreg EE0 9%nat (Z_to_bv 5 9) G9).
host_reg HS (Z_to_bv 5 12) (w64 6) T12 ltac:(reflexivity).
host_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + (AF_m_rx + 0x354))) T1 ltac:(apply codeptr_val; exact HEI0).
host_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) T2 ltac:(host_kreg EE0 2%nat (Z_to_bv 5 2) Hsp).
host_reg HS (Z_to_bv 5 3) (YK11.getr regs0 3) T3 ltac:(host_kreg EE0 3%nat (Z_to_bv 5 3) Hgp).
host_reg HS (Z_to_bv 5 4) (YK11.getr regs0 4) T4 ltac:(host_kreg EE0 4%nat (Z_to_bv 5 4) Htp).
host_reg HS (Z_to_bv 5 8) (w64 (TI.tf_addr fr + 30)) T8 ltac:(host_kreg EE0 8%nat (Z_to_bv 5 8) G8).
host_reg HS (Z_to_bv 5 9) (w64 TRANS_HOST) T9 ltac:(host_kreg EE0 9%nat (Z_to_bv 5 9) G9).
host_reg HS (Z_to_bv 5 18) (w64 (TI.tf_addr fr + 30 + i)) T18 ltac:(host_kreg EE0 18%nat (Z_to_bv 5 18) G18).
host_reg HS (Z_to_bv 5 19) (w64 TA_M) T19 ltac:(host_kreg EE0 19%nat (Z_to_bv 5 19) G19).
host_reg HS (Z_to_bv 5 20) (w64 (-1)) T20 ltac:(host_kreg EE0 20%nat (Z_to_bv 5 20) G20).
host_reg HS (Z_to_bv 5 21) (w64 i) T21 ltac:(host_kreg EE0 21%nat (Z_to_bv 5 21) G21).
host_reg HS (Z_to_bv 5 22) (w64 (10 - i)) T22 ltac:(host_kreg EE0 22%nat (Z_to_bv 5 22) G22).
host_reg HS (Z_to_bv 5 23) (w64 (TW.M_state Bwc)) T23 ltac:(host_kreg EE0 23%nat (Z_to_bv 5 23) G23).
host_reg HS (Z_to_bv 5 25) (w64 (mfb fr 28)) T25 ltac:(host_kreg EE0 25%nat (Z_to_bv 5 25) G25).
pose proof (host_frs_kept _ _ _ KP1 Hfrs) as HfrsT.
(* +0x350: the bcmp wrapper *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) mm rom)
    mdx) Q) end.
eapply SRr_bind.
{ exact (host_bcmp i Wc (ms_regs ms) (ms_mem ms) _ Hi HJ HfrsT Hhdr Hblen T10 T11 T12 T2 T3 T4 T1). }
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp & KP2).
pose proof (host_kept_trans _ _ _ _ KP1 KP2) as KP12.
assert (PR : forall rr v, acallee_saved rr -> YK11.getr (ms_regs ms) (Z_to_bv 5 rr) = v ->
  YK11.getr regs3 (Z_to_bv 5 rr) = v) by (intros rr v Hrr Hv; rewrite (HP3 rr Hrr); exact Hv).
pose proof (PR 2 _ ltac:(unfold acallee_saved; lia) T2) as P2.
pose proof (PR 3 _ ltac:(unfold acallee_saved; lia) T3) as P3.
pose proof (PR 4 _ ltac:(unfold acallee_saved; lia) T4) as P4.
pose proof (PR 8 _ ltac:(unfold acallee_saved; lia) T8) as P8.
pose proof (PR 9 _ ltac:(unfold acallee_saved; lia) T9) as P9.
pose proof (PR 18 _ ltac:(unfold acallee_saved; lia) T18) as P18.
pose proof (PR 19 _ ltac:(unfold acallee_saved; lia) T19) as P19.
pose proof (PR 20 _ ltac:(unfold acallee_saved; lia) T20) as P20.
pose proof (PR 21 _ ltac:(unfold acallee_saved; lia) T21) as P21.
pose proof (PR 22 _ ltac:(unfold acallee_saved; lia) T22) as P22.
pose proof (PR 23 _ ltac:(unfold acallee_saved; lia) T23) as P23.
pose proof (PR 25 _ ltac:(unfold acallee_saved; lia) T25) as P25.
clear PR HP3 KP1 KP2 HfrsT. clear dependent ms.
(* +0x354: `beqz a0`, from a fresh state at the return *)
pose proof (host_st (fx := fx) (rc := rc) Wc regs3 mem3 0x354) as HS3.
set (E3 := host_E regs3) in HS3.
assert (EE3 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E3 nn = YK11.getr regs3 rr)
  by (intros nn rr Hn; unfold E3, host_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3, host_E; apply Eimg_env).
assert (SHOK3 : sh_ok tfibsegs host_Bx host_SH E3 (mrestrict (w_H Wc) mem3))
  by (unfold sh_ok, host_SH; apply Forall_nil).
psrr_branch_tok RUN BR HS3 SHOK3 YC4b.Bspan.
- (* the bytes agree: off = i *)
  cbn [branch_taken sv_denot] in Hc.
  rewrite (EE3 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned in Hc.
  apply host_eqb in Hc. apply (proj1 Hcmp) in Hc.
  destruct HSTEP as [[_ ->] | [Hb _]]; [|rewrite Hc in Hb; discriminate Hb].
  (* run 2, +0x354 .. +0x51c: `beqz a0` taken, s4 = s5 (0x84da4) *)
  paj_run_to_tok RUNTO HS3 HJ3 SHOK3 YC4b.Bspan (AF_m_rx + OFF_ANNT).
  { host_awr. }
  pose proof (host_kept_trans _ _ _ _ KP12 (host_kept_run _ _ Wc _ _ HFr eq_refl)) as KPF. clear HF HFr HG.
  pmkst HS3.
  host_reg HS3 (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) F2 ltac:(host_kreg EE3 2%nat (Z_to_bv 5 2) P2).
  host_reg HS3 (Z_to_bv 5 3) (YK11.getr regs0 3) F3 ltac:(host_kreg EE3 3%nat (Z_to_bv 5 3) P3).
  host_reg HS3 (Z_to_bv 5 4) (YK11.getr regs0 4) F4 ltac:(host_kreg EE3 4%nat (Z_to_bv 5 4) P4).
  host_reg HS3 (Z_to_bv 5 8) (w64 (TI.tf_addr fr + 30)) F8 ltac:(host_kreg EE3 8%nat (Z_to_bv 5 8) P8).
  host_reg HS3 (Z_to_bv 5 19) (w64 TA_M) F19 ltac:(host_kreg EE3 19%nat (Z_to_bv 5 19) P19).
  host_reg HS3 (Z_to_bv 5 20) (w64 i) F20 ltac:(host_kreg EE3 21%nat (Z_to_bv 5 21) P21).
  host_reg HS3 (Z_to_bv 5 23) (w64 (TW.M_state Bwc)) F23 ltac:(host_kreg EE3 23%nat (Z_to_bv 5 23) P23).
  host_reg HS3 (Z_to_bv 5 25) (w64 (mfb fr 28)) F25 ltac:(host_kreg EE3 25%nat (Z_to_bv 5 25) P25).
  change (BASE + 15172) with (BASE + (AF_m_rx + OFF_ANNT)). rewrite host_pc.
  apply (KA Wc Bwc). eapply (mrx_at_intro B MT).
  + exact HJ3.
  + exact Hfr.
  + exact Hperm.
  + exact Hmo.
  + exact F2.
  + exact F3.
  + exact F4.
  + exact (host_saved_kept _ _ _ KPF Hsav).
  + exact (host_tw_kept _ _ _ _ KPF Htw).
  + unfold R_ANNT. cbv beta. exists i.
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact (host_frs_kept _ _ _ KPF Hfrs)|]. split; [exact Hhdr|].
    split; [right; exact Hcmd|]. split; [exact Hblen|].
    split; [lia|].
    split; [intros H0; rewrite Hcmd in H0; unfold TC.SPEC_CMD_E0, TC.SPEC_CMD_E1 in H0; lia|].
    split; [exact F8|]. split; [exact F19|]. split; [exact F20|]. split; [exact F23|]. split; [exact F25|].
    exists B3. split; [exact Htail|]. split; [exact Htick | exact Hr1].
- (* the bytes differ *)
  cbn [branch_taken sv_denot] in Hc.
  rewrite (EE3 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned in Hc.
  assert (Hb : TC.beq_bytes (TW.sub (EPI.mrx_body fr) i 6) TC.HOST = false).
  { apply Bool.not_true_is_false. intros Eb. apply (proj2 Hcmp) in Eb.
    pose proof (proj2 (host_eqb (YK11.getr regs3 (Z_to_bv 5 10)) (Z_to_bv 64 0)) Eb) as Hx.
    rewrite Hx in Hc. discriminate Hc. }
  destruct HSTEP as [[Hb' _] | [_ HO']]; [rewrite Hb in Hb'; discriminate Hb'|].
  clear Hc.
  (* run 2, +0x354 .. +0x364: s5 = s5 + 1 (addiw), s6 = s6 - 1, s2 = s2 + 1, `bnez s6` *)
  paj_run_tok RUN HS3 HJ3 SHOK3 YC4b.Bspan.
  { host_awr. }
  pose proof (host_kept_trans _ _ _ _ KP12 (host_kept_run _ _ Wc _ _ HFr eq_refl)) as KP3. clear HF HFr HG.
  psrr_branch_tok RUN BR HS3 SHOK3 YC4b.Bspan.
  + (* `bnez s6` taken: back to the loop head, round i + 1 *)
    cbn [branch_taken sv_denot] in Hc.
    rewrite (EE3 22%nat (Z_to_bv 5 22) eq_refl), P22 in Hc. unfold w64 in Hc.
    rewrite unsigned_lit_small in Hc by lia.
    assert (Hi9 : i < 9).
    { destruct (Z.eq_dec i 9) as [E9|E9]; [|lia]. exfalso. subst i. vm_compute in Hc. discriminate Hc. }
    paj_run_to_tok RUNTO HS3 HJ3 SHOK3 YC4b.Bspan (AF_m_rx + 0x344).
    { host_awr. }
    pose proof (host_kept_trans _ _ _ _ KP3 (host_kept_run _ _ Wc _ _ HFr eq_refl)) as KPF. clear HF HFr HG.
    pmkst HS3.
    host_reg HS3 (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) F2 ltac:(host_kreg EE3 2%nat (Z_to_bv 5 2) P2).
    host_reg HS3 (Z_to_bv 5 3) (YK11.getr regs0 3) F3 ltac:(host_kreg EE3 3%nat (Z_to_bv 5 3) P3).
    host_reg HS3 (Z_to_bv 5 4) (YK11.getr regs0 4) F4 ltac:(host_kreg EE3 4%nat (Z_to_bv 5 4) P4).
    host_reg HS3 (Z_to_bv 5 8) (w64 (TI.tf_addr fr + 30)) F8 ltac:(host_kreg EE3 8%nat (Z_to_bv 5 8) P8).
    host_reg HS3 (Z_to_bv 5 19) (w64 TA_M) F19 ltac:(host_kreg EE3 19%nat (Z_to_bv 5 19) P19).
    host_reg HS3 (Z_to_bv 5 20) (w64 (-1)) F20 ltac:(host_kreg EE3 20%nat (Z_to_bv 5 20) P20).
    host_reg HS3 (Z_to_bv 5 23) (w64 (TW.M_state Bwc)) F23 ltac:(host_kreg EE3 23%nat (Z_to_bv 5 23) P23).
    host_reg HS3 (Z_to_bv 5 25) (w64 (mfb fr 28)) F25 ltac:(host_kreg EE3 25%nat (Z_to_bv 5 25) P25).
    host_reg HS3 (Z_to_bv 5 9) (w64 TRANS_HOST) F9 ltac:(host_kreg EE3 9%nat (Z_to_bv 5 9) P9).
    host_reg HS3 (Z_to_bv 5 18) (w64 (TI.tf_addr fr + 30 + (i + 1))) F18
      ltac:(cbn [sv_denot]; rewrite (EE3 18%nat (Z_to_bv 5 18) eq_refl), P18; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia).
    host_reg HS3 (Z_to_bv 5 21) (w64 (i + 1)) F21
      ltac:(apply host_addiw; [rewrite (EE3 21%nat (Z_to_bv 5 21) eq_refl); exact P21 | lia]).
    host_reg HS3 (Z_to_bv 5 22) (w64 (10 - (i + 1))) F22
      ltac:(cbn [sv_denot]; rewrite (EE3 22%nat (Z_to_bv 5 22) eq_refl), P22; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia).
    change (BASE + 14700) with (BASE + (AF_m_rx + 0x344)). rewrite host_pc.
    apply (KL Hi9 Wc Bwc). eapply (mrx_at_intro B MT).
    * exact HJ3.
    * exact Hfr.
    * exact Hperm.
    * exact Hmo.
    * exact F2.
    * exact F3.
    * exact F4.
    * exact (host_saved_kept _ _ _ KPF Hsav).
    * exact (host_tw_kept _ _ _ _ KPF Htw).
    * unfold R_LOOP. cbv beta.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact (host_frs_kept _ _ _ KPF Hfrs)|].
      split; [exact Hhdr|]. split; [exact Hcmd|]. split; [exact Hblen|].
      split; [exact F8|]. split; [exact F19|]. split; [exact F20|]. split; [exact F23|]. split; [exact F25|].
      split; [exact F9|]. split; [exact F18|]. split; [exact F21|]. split; [exact F22|].
      exists off, B3. split; [exact HO'|]. split; [exact Htail|]. split; [exact Htick | exact Hr1].
  + (* `bnez s6` not taken: the tenth miss, s4 = -1, `j` to ANNT (0x84bf4) *)
    cbn [branch_taken sv_denot] in Hc.
    rewrite (EE3 22%nat (Z_to_bv 5 22) eq_refl), P22 in Hc. unfold w64 in Hc.
    rewrite unsigned_lit_small in Hc by lia.
    apply Bool.negb_false_iff in Hc. apply host_eqb in Hc.
    apply (f_equal (fun w : word => bv_unsigned w)) in Hc. cbv beta in Hc.
    rewrite !unsigned_lit_small in Hc by lia.
    assert (Hi9 : i = 9) by lia. subst i.
    change (Z.to_nat (10 - (9 + 1))) with 0%nat in HO'. cbn [TC.host_offset_loop] in HO'.
    injection HO' as HO'. subst off.
    paj_run_to_tok RUNTO HS3 HJ3 SHOK3 YC4b.Bspan (AF_m_rx + OFF_ANNT).
    { host_awr. }
    pose proof (host_kept_trans _ _ _ _ KP3 (host_kept_run _ _ Wc _ _ HFr eq_refl)) as KPF. clear HF HFr HG.
    pmkst HS3.
    host_reg HS3 (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) F2 ltac:(host_kreg EE3 2%nat (Z_to_bv 5 2) P2).
    host_reg HS3 (Z_to_bv 5 3) (YK11.getr regs0 3) F3 ltac:(host_kreg EE3 3%nat (Z_to_bv 5 3) P3).
    host_reg HS3 (Z_to_bv 5 4) (YK11.getr regs0 4) F4 ltac:(host_kreg EE3 4%nat (Z_to_bv 5 4) P4).
    host_reg HS3 (Z_to_bv 5 8) (w64 (TI.tf_addr fr + 30)) F8 ltac:(host_kreg EE3 8%nat (Z_to_bv 5 8) P8).
    host_reg HS3 (Z_to_bv 5 19) (w64 TA_M) F19 ltac:(host_kreg EE3 19%nat (Z_to_bv 5 19) P19).
    host_reg HS3 (Z_to_bv 5 20) (w64 (-1)) F20 ltac:(host_kreg EE3 20%nat (Z_to_bv 5 20) P20).
    host_reg HS3 (Z_to_bv 5 23) (w64 (TW.M_state Bwc)) F23 ltac:(host_kreg EE3 23%nat (Z_to_bv 5 23) P23).
    host_reg HS3 (Z_to_bv 5 25) (w64 (mfb fr 28)) F25 ltac:(host_kreg EE3 25%nat (Z_to_bv 5 25) P25).
    change (BASE + 15172) with (BASE + (AF_m_rx + OFF_ANNT)). rewrite host_pc.
    apply (KA Wc Bwc). eapply (mrx_at_intro B MT).
    * exact HJ3.
    * exact Hfr.
    * exact Hperm.
    * exact Hmo.
    * exact F2.
    * exact F3.
    * exact F4.
    * exact (host_saved_kept _ _ _ KPF Hsav).
    * exact (host_tw_kept _ _ _ _ KPF Htw).
    * unfold R_ANNT. cbv beta. exists (-1).
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact (host_frs_kept _ _ _ KPF Hfrs)|]. split; [exact Hhdr|].
      split; [right; exact Hcmd|]. split; [exact Hblen|].
      split; [lia|]. split; [intros _; reflexivity|].
      split; [exact F8|]. split; [exact F19|]. split; [exact F20|]. split; [exact F23|]. split; [exact F25|].
      exists B3. split; [exact Htail|]. split; [exact Htick | exact Hr1].
Qed.

(* The entry of the segment, 0x84bbc - 0x84bcc: s5 = 0, s6 = 10, s1 = HOST, s2 = s0; then the loop head. *)
Lemma host_entry : K (MRX_PC 0x344) (R_LOOP 0) -> K (MRX_PC OFF_HOST) (R_HOST fr n sp1 lyc Sc Bw' r).
Proof.
intros KL Wc Bwc c Hat.
destruct Hat as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp & Htp & Hsav & Htw & HR).
destruct HR as (-> & -> & Hfrs & Hhdr & Hcmd & Hblen & G8 & G19 & G20 & G23 & G25 & B3 & Hann & Htick & Hr1).
destruct (host_ann timg_A fr Bwc B3 Hcmd Hblen Hann) as (off & HO & Htail).
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
rewrite <- (host_pc OFF_HOST).
pose proof (host_st (fx := fx) (rc := rc) Wc regs2 mem2 OFF_HOST) as HS.
set (E0 := host_E regs2) in HS.
assert (EE0 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E0 nn = YK11.getr regs2 rr)
  by (intros nn rr Hn; unfold E0, host_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HEI0 : img_env VAL A_LIM E0) by (unfold E0, host_E; apply Eimg_env).
assert (SHOK : sh_ok tfibsegs host_Bx host_SH E0 (mrestrict (w_H Wc) mem2))
  by (unfold sh_ok, host_SH; apply Forall_nil).
(* the run, +0x330 .. +0x344 *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + 0x344).
{ host_awr. }
pose proof (host_kept_run _ _ Wc _ _ HFr eq_refl) as KP. clear HF HFr HG.
pmkst HS.
host_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) F2 ltac:(host_kreg EE0 2%nat (Z_to_bv 5 2) Hsp).
host_reg HS (Z_to_bv 5 3) (YK11.getr regs0 3) F3 ltac:(host_kreg EE0 3%nat (Z_to_bv 5 3) Hgp).
host_reg HS (Z_to_bv 5 4) (YK11.getr regs0 4) F4 ltac:(host_kreg EE0 4%nat (Z_to_bv 5 4) Htp).
host_reg HS (Z_to_bv 5 8) (w64 (TI.tf_addr fr + 30)) F8 ltac:(host_kreg EE0 8%nat (Z_to_bv 5 8) G8).
host_reg HS (Z_to_bv 5 19) (w64 TA_M) F19 ltac:(host_kreg EE0 19%nat (Z_to_bv 5 19) G19).
host_reg HS (Z_to_bv 5 20) (w64 (-1)) F20 ltac:(host_kreg EE0 20%nat (Z_to_bv 5 20) G20).
host_reg HS (Z_to_bv 5 23) (w64 (TW.M_state Bwc)) F23 ltac:(host_kreg EE0 23%nat (Z_to_bv 5 23) G23).
host_reg HS (Z_to_bv 5 25) (w64 (mfb fr 28)) F25 ltac:(host_kreg EE0 25%nat (Z_to_bv 5 25) G25).
host_reg HS (Z_to_bv 5 9) (w64 TRANS_HOST) F9
  ltac:(cbn [sv_denot]; rewrite (img_env_atomP E0 247 HEI0 ltac:(unfold A_TEXT, A_LIM; lia));
        apply bv_eq; vm_compute; reflexivity).
host_reg HS (Z_to_bv 5 18) (w64 (TI.tf_addr fr + 30 + 0)) F18
  ltac:(rewrite Z.add_0_r; host_kreg EE0 8%nat (Z_to_bv 5 8) G8).
host_reg HS (Z_to_bv 5 21) (w64 0) F21 ltac:(reflexivity).
host_reg HS (Z_to_bv 5 22) (w64 (10 - 0)) F22 ltac:(reflexivity).
change (BASE + 14700) with (BASE + (AF_m_rx + 0x344)). rewrite host_pc.
apply (KL Wc Bwc). eapply (mrx_at_intro B MT).
- exact HJ.
- exact Hfr.
- exact Hperm.
- exact Hmo.
- exact F2.
- exact F3.
- exact F4.
- exact (host_saved_kept _ _ _ KP Hsav).
- exact (host_tw_kept _ _ _ _ KP Htw).
- unfold R_LOOP. cbv beta.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact (host_frs_kept _ _ _ KP Hfrs)|].
  split; [exact Hhdr|]. split; [exact Hcmd|]. split; [exact Hblen|].
  split; [exact F8|]. split; [exact F19|]. split; [exact F20|]. split; [exact F23|]. split; [exact F25|].
  split; [exact F9|]. split; [exact F18|]. split; [exact F21|]. split; [exact F22|].
  exists off, B3. split; [exact HO|]. split; [exact Htail|]. split; [exact Htick | exact Hr1].
Qed.

Lemma host_loop : K (MRX_PC OFF_ANNT) (R_ANNT fr n sp1 lyc Sc Bw' r) ->
  forall k i, Z.of_nat k = 10 - i -> 0 <= i <= 9 -> K (MRX_PC 0x344) (R_LOOP i).
Proof.
intros KA k. induction k as [|k IH]; intros i Hk Hi; [lia|].
apply (host_round i Hi KA). intros Hi9. apply (IH (i + 1)); lia.
Qed.

Lemma mrx_seg_host :
  K (MRX_PC OFF_ANNT) (R_ANNT fr n sp1 lyc Sc Bw' r) ->
  K (MRX_PC OFF_HOST) (R_HOST fr n sp1 lyc Sc Bw' r).
Proof using All.
intros KA. apply host_entry. exact (host_loop KA 10 0 eq_refl ltac:(lia)).
Qed.

End seg.
