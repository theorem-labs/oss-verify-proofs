(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 485 of its 562 lines of code are new or changed and 953 lines of the source are left out. *)
(* m_rx_seg_set: three segment lemmas of the image-B walk of m_rx (statement lib/B/Prog/m_rx_cg.v, kit
   lib/B/Prog/m_rx_seg_kit.v; listing lib/B/Prog/DgnTransportBList.v after AF_m_rx). Each is `K (successor cuts) ->
   K (its cut)`: from a machine the cut describes, symbolic runs over the walk's inner G journal
   (TransportGRunB.v paj_run_x / paj_run_to_x) and the contract of m_set (m_set_cg.v, G form, in the same journal)
   reach the successor cut, whose mrx_at is built with the kit's mrx_at_intro.
     SET  +0x1cc  `mv a0, zero`, `jal m_set` (a0 = S_IDLE, a1 = why from R_SET), the return at +0x1d4, `j` to +0x3a4 =
                  the TICK cut (mrx_seg_set).
     E0L  +0x36c  `mv a0, zero`, `jal m_set` (a1 = 3), the return at +0x374, `lw a0, 12(s1)` (s1 = &M, callee-saved:
                  M.state of the world m_set leaves, read through the world relation), at +0x378 = the E0W cut
                  (mrx_seg_e0l).
     E0W  +0x378  `bnez a0` (a0 = M.state) to the TICK cut; else g_cfg.auto_wake (object 53, the 4-byte signed load of
                  the world's bytes), `beqz a0` to the TICK cut; else +0x388 = the WAKE cut (mrx_seg_e0w; model
                  EPI.mrx_e0w).
   No run stores a byte; a run from a state with no writable byte keeps every byte's view (YC4b.kept_of_frame). A
   callee is entered on the walk's own journal with ra = the return address, sp = sp1 - 112 and the entry gp / tp;
   its post gives the next cut through the kit's mrx_next (the saved slots lie above m_set's 16-byte window). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg m_wake_cg m_maybe_online_cg m_tick_cg spec_read_frame_cg host_offset_cg desk_named_cg check_state_data_cg
  m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRunB TransportGFrameB CanKit
YC1g YC1h m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require m_rx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_annt.
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
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
Module UMR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T.m_rx.
Module AK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_kit.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module AAN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.m_rx_seg_annt.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- tactics (write rights, pcs and run windows: lib/A/Prog/m_rx_seg_annt.v annt_awr_ro, annt_pc, annt_win) ---- *)

(* The value of register q in the machine state of a symbolic state HS: its symbolic value, computed, then tac. A's
   annt_reg names image A's st_ok_pi_restrict_reg (lib/A/Prog/DgnTransportPaLib.v); this one names image B's
   (lib/B/Prog/DgnTransportBPaLib.v). *)
Ltac set_reg HS q v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) q) in
      assert (H : YK11.getr (ms_regs msx) q = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx q HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) q) in
      assert (H : YK11.getr (ms_regs msx) q = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx q HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "set_reg: no match for" T; fail
  end.

(* A run of a state with no writable byte wrote nothing: every byte's view is the one it started from. *)
Ltac set_kept1 HFr Ha :=
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr);
  [ let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx; AAN.annt_win Hin Hx ltac:(exfalso; lia)
  | exact Ha
  | let Hf := fresh "Hf" in intros Hf; destruct Hf ].
Ltac set_kept HFr :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; set_kept1 HFr Ha.

(* After a run: the model generalized. *)
Ltac set_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    let md := fresh "mdw" in set (md := mdx) in *; clearbody md end.

(* ---- the symbolic states ---- *)

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation sgs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma set_vals : VAL (A_OBJ 53) = TB_g_cfg + 16 /\ BASE + AF_m_rx = transportb_sigma TB_m_rx.
Proof. vm_compute. split; reflexivity. Qed.

Lemma set_img : forall regs xs, img_env VAL A_LIM (Eimg (PI := PI_transportb) (Ereg regs xs)).
Proof. intros regs xs. apply Eimg_env. Qed.

Lemma set_agree : forall regs xs, env_agree 32 (Ereg regs xs) (Eimg (PI := PI_transportb) (Ereg regs xs)).
Proof. intros regs xs. split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma set_shok : forall regs xs (W2 : world sgs) mem,
  sh_ok sgs (SLit 0) [] (Eimg (PI := PI_transportb) (Ereg regs xs)) (mrestrict (w_H W2) mem).
Proof. intros regs xs W2 mem. unfold sh_ok. apply Forall_nil. Qed.

(* The symbolic state at a pc with no region: the registers as atoms, no fact. *)
Definition ss_set (k : Z) : sstate := mkSS k sr_atoms [] None (mkFacts [] [] []).

Lemma set_entry : forall (W2 : world sgs) regs mem k,
  st_ok_pi sgs VAL (Eimg (PI := PI_transportb) (Ereg regs [])) (ss_set k)
    (restrict (w_H W2) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom sgs))).
Proof.
  intros W2 regs mem k. rewrite restrict_mkst_fx. unfold ss_set.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split.
Qed.

(* E0L after m_set's return (+0x374): M.state (s1 + 12, read-only) holds the world's bytes; s1 = &M. *)
Definition E0L_RET : Z := 15600.
Definition e0l_M : YP09.region := YP09.mkRegion (Some 9%nat) 12 16 0 0 [YP09.mkChunk 12 (YP09.CVal 4 (SOff 32 0))].
Definition e0l_facts : facts := mkFacts [(9%nat, mkAF TB_M TB_M 5); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_e0l : sstate := mkSS E0L_RET sr_atoms [e0l_M] None e0l_facts.
Definition e0l_E (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4)]).

Lemma e0l_entry : forall (W2 : world sgs) regs mem Bw,
  tw_at TMAP_B (aview sgs (w_H W2) mem) Bw ->
  YK11.getr regs 9 = w64 TB_M ->
  st_ok_pi sgs VAL (e0l_E regs Bw) ss_e0l
    (restrict (w_H W2) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + E0L_RET)) mem (YK11.seg_rom sgs))).
Proof.
  intros W2 regs mem Bw Htw H9.
  set (E := e0l_E regs Bw).
  assert (E9 : ew E 9 = Z_to_bv 64 TB_M)
    by (unfold E, e0l_E; rewrite (ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (U9 : bv_unsigned (ew E 9) = TB_M) by (rewrite E9; apply unsigned_lit_small; unfold TB_M; lia).
  assert (B9 : base_val E (Some 9%nat) = TB_M) by (cbn [base_val]; exact U9).
  assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at Bw TW.A_M_state 4))
    by (unfold E, e0l_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  pose proof (TWL.u_at_range Bw TW.A_M_state 4) as R32. change (8 * Z.of_nat 4) with 32 in R32.
  assert (DEN : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k 0) = Z_to_bv 64 v)
    by (intros k v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  rewrite restrict_mkst_fx. unfold ss_e0l.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold e0l_M, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
    split; [unfold TB_M; lia|]. split; [unfold TB_M; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val sgs E _ TB_M 12 4 (SOff 32 0) (TW.u_at Bw TW.A_M_state 4));
      [apply DEN; [exact E32 | lia] | exact R32 | lia |].
    exact (tw_read_val sgs _ TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 12 4 TMAP_B_ok Htw TMAP_B_M
      ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold e0l_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, E32.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_M_state 4)) by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

(* E0W (+0x378): g_cfg.auto_wake (object 53, read-only) holds the world's bytes. *)
Definition e0w_aw : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 53)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 32 0))].
Definition e0w_facts : facts := mkFacts [(32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_e0w : sstate := mkSS (AF_m_rx + OFF_E0W) sr_atoms [e0w_aw] None e0w_facts.
Definition e0w_E (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at Bw TW.A_Cfg_auto_wake 4)]).

Lemma e0w_entry : forall (Wc : world sgs) regs mem Bw,
  tw_at TMAP_B (aview sgs (w_H Wc) mem) Bw ->
  st_ok_pi sgs VAL (e0w_E regs Bw) ss_e0w
    (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_m_rx + OFF_E0W))) mem (YK11.seg_rom sgs))).
Proof.
  intros Wc regs mem Bw Htw.
  destruct set_vals as (V53 & _).
  set (E := e0w_E regs Bw).
  assert (B53 : base_val E (Some (A_OBJ 53)) = TB_g_cfg + 16).
  { cbn [base_val]. unfold E, e0w_E. rewrite (Eimg_img _ (A_OBJ 53)) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite V53. apply unsigned_lit_small. unfold TB_g_cfg. lia. }
  assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at Bw TW.A_Cfg_auto_wake 4))
    by (unfold E, e0w_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  pose proof (TWL.u_at_range Bw TW.A_Cfg_auto_wake 4) as R32. change (8 * Z.of_nat 4) with 32 in R32.
  assert (DEN : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k 0) = Z_to_bv 64 v)
    by (intros k v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  rewrite restrict_mkst_fx. unfold ss_e0w.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold e0w_aw, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B53.
    split; [unfold TB_g_cfg; lia|]. split; [unfold TB_g_cfg; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val sgs E _ (TB_g_cfg + 16) 0 4 (SOff 32 0) (TW.u_at Bw TW.A_Cfg_auto_wake 4));
      [apply DEN; [exact E32 | lia] | exact R32 | lia |].
    exact (tw_read_val sgs _ TMAP_B Bw TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 16 4 TMAP_B_ok Htw TMAP_B_g_cfg
      ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold e0w_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32.
    rewrite (unsigned_lit_small (TW.u_at Bw TW.A_Cfg_auto_wake 4)) by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

End h.

Section seg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HMRX : trans_mrx_cells B.
Hypothesis HRO : trans_ro_rd_unowned B.
Hypothesis HNE : trans_rom_no_errno B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS_B.
Hypothesis HGNE : gx_noerrno B TG.G_HARNESS_B.
Hypothesis HSRF : forall fx' : YK11.FPState, @transport_spec_read_frame_cg fx' rc B MT (transportb_sigma TB_spec_read_frame).
Hypothesis HBCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc tfibsegs B (transportb_sigma TB___interceptor_trampoline_bcmp).
Hypothesis HMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc tfibsegs B OCpy (transportb_sigma TB___asan_memcpy).
Hypothesis HHOFF : forall fx' : YK11.FPState, @transport_host_offset_cg fx' rc B MT (transportb_sigma TB_host_offset).
Hypothesis HMSET : forall fx' : YK11.FPState, @transport_m_set_cg fx' rc B MT (transportb_sigma TB_m_set).
Hypothesis HDN : forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transportb_sigma TB_desk_named).
Hypothesis HMW : forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transportb_sigma TB_m_wake).
Hypothesis HMO : forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transportb_sigma TB_m_maybe_online).
Hypothesis HMT : forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transportb_sigma TB_m_tick).
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

Local Abbreviation sgs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The run of `mv a0, zero` and `jal m_set` from a cut (+0x1cc or +0x36c) whose state has no region: at m_set's entry,
   ra = the return address (BASE + AF_m_rx + off + 8), a0 = S_IDLE, a1 and the callee-saved registers as at the cut,
   nothing stored. *)
Lemma set_jal : forall (Wc : world sgs) ly2 S2 regs2 mem2 md2 (off : Z) (Q : world sgs -> config -> Prop),
  @W_journalG.ajournal_gx rc tfib_sink_head sgs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc mem2 md2 0 ->
  (off = OFF_SET \/ off = OFF_E0L) ->
  (forall regsA memA mdA,
     @W_journalG.ajournal_gx rc tfib_sink_head sgs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc memA mdA 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) memA a = aview sgs (w_H Wc) mem2 a) ->
     YK11.getr regsA 1 = Z_to_bv 64 (BASE + (AF_m_rx + off + 8)) ->
     YK11.getr regsA 10 = w64 TC.S_IDLE ->
     YK11.getr regsA 11 = YK11.getr regs2 11 ->
     aregs_preserved regs2 regsA ->
     SRr sgs Wc (@cfg_at fx sgs (transportb_sigma TB_m_set) regsA memA mdA) Q) ->
  SRr sgs Wc (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + off))) mem2 (YK11.seg_rom sgs)) md2) Q.
Proof.
intros Wc ly2 S2 regs2 mem2 md2 off Q HJ Hoff KN.
pose proof (set_img regs2 []) as HEI.
pose proof (set_shok regs2 [] Wc mem2) as SHOK.
assert (EE : forall m (q : bv 5), Z.of_nat m = bv_unsigned q ->
  ew (Eimg (PI := PI_transportb) (Ereg regs2 [])) m = YK11.getr regs2 q)
  by (intros m q Hm; apply ew_Eimg_Ereg_nat; exact Hm).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
destruct Hoff as [-> | ->].
- pose proof (set_entry Wc regs2 mem2 (AF_m_rx + OFF_SET)) as HS.
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { AAN.annt_awr_ro. }
  lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
  assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem msA) a = aview sgs (w_H Wc) mem2 a)
    by (set_kept HFr).
  clear HF HFr HG.
  pmkst HS.
  set_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + (AF_m_rx + OFF_SET + 8))) R1
    ltac:(apply codeptr_val; exact HEI).
  set_reg HS (Z_to_bv 5 10) (w64 TC.S_IDLE) R10 ltac:(reflexivity).
  set_reg HS (Z_to_bv 5 11) (YK11.getr regs2 (Z_to_bv 5 11)) R11
    ltac:(cbn [sv_denot]; rewrite (EE 11%nat (Z_to_bv 5 11) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (HP0 : aregs_preserved regs2 (ms_regs msA))
    by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) (Eimg (PI := PI_transportb) (Ereg regs2 [])) _ msA regs2 [] HS);
        [apply set_agree | vm_compute; reflexivity]).
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (@cfg_at fx sgs (transportb_sigma TB_m_set) rg mm mdx) Qx) end.
  exact (KN _ _ _ HJ KA1 R1 R10 R11 HP0).
- pose proof (set_entry Wc regs2 mem2 (AF_m_rx + OFF_E0L)) as HS.
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { AAN.annt_awr_ro. }
  lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
  assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem msA) a = aview sgs (w_H Wc) mem2 a)
    by (set_kept HFr).
  clear HF HFr HG.
  pmkst HS.
  set_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + (AF_m_rx + OFF_E0L + 8))) R1
    ltac:(apply codeptr_val; exact HEI).
  set_reg HS (Z_to_bv 5 10) (w64 TC.S_IDLE) R10 ltac:(reflexivity).
  set_reg HS (Z_to_bv 5 11) (YK11.getr regs2 (Z_to_bv 5 11)) R11
    ltac:(cbn [sv_denot]; rewrite (EE 11%nat (Z_to_bv 5 11) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (HP0 : aregs_preserved regs2 (ms_regs msA))
    by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) (Eimg (PI := PI_transportb) (Ereg regs2 [])) _ msA regs2 [] HS);
        [apply set_agree | vm_compute; reflexivity]).
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (@cfg_at fx sgs (transportb_sigma TB_m_set) rg mm mdx) Qx) end.
  exact (KN _ _ _ HJ KA1 R1 R10 R11 HP0).
Qed.

(* The `jal m_set` from a cut (+0x1cc or +0x36c) with a1 = why: the run to m_set's entry (set_jal), m_set's contract in
   the walk's journal, then the next cut's common facts at its return (pc BASE + AF_m_rx + off + 8). *)
Lemma set_call : forall (Wc : world sgs) Bwc ly2 S2 regs2 mem2 md2 (off why : Z) (B6 : list byte)
    (Q : world sgs -> config -> Prop),
  @W_journalG.ajournal_gx rc tfib_sink_head sgs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc mem2 md2 0 ->
  frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> mo_le MT Sc S2 0 ->
  YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regs2 3 = YK11.getr regs0 3 -> YK11.getr regs2 4 = YK11.getr regs0 4 ->
  mrx_hi regs0 regs2 -> mrx_saved Wc mem2 sp1 regs0 ->
  tw_at TMAP_B (aview sgs (w_H Wc) mem2) Bwc ->
  YK11.getr regs2 11 = w64 why -> - 2 ^ 31 <= why < 2 ^ 31 ->
  TC.m_set_m Bwc TC.S_IDLE why = Some (B6, tt) ->
  (off = OFF_SET \/ off = OFF_E0L) ->
  (forall W2 ly3 S3 regs3 mem3 md3,
     @W_journalG.ajournal_gx rc tfib_sink_head sgs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly3 S3 W2 mem3 md3 0 ->
     frames S3 = frames Sc -> Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) -> mo_le MT Sc S3 0 ->
     YK11.getr regs3 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
     YK11.getr regs3 3 = YK11.getr regs0 3 -> YK11.getr regs3 4 = YK11.getr regs0 4 ->
     mrx_hi regs0 regs3 -> mrx_saved W2 mem3 sp1 regs0 ->
     tw_at TMAP_B (aview sgs (w_H W2) mem3) B6 ->
     YK11.getr regs3 9 = YK11.getr regs2 9 ->
     SRr sgs W2 (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + (AF_m_rx + off + 8))) mem3 (YK11.seg_rom sgs)) md3) Q) ->
  SRr sgs Wc (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + (AF_m_rx + off))) mem2 (YK11.seg_rom sgs)) md2) Q.
Proof.
intros Wc Bwc ly2 S2 regs2 mem2 md2 off why B6 Q HJ Hfr Hperm Hmo Hsp Hgp2 Htp2 Hhi HSV HTW Hr11 Hwhy Hms Hoff KN.
pose proof HST as (_ & Hsp16 & Hceil & H46 & H47 & _ & _ & Hgp0 & Htp0 & _ & _ & _ & _ & _ & _ & _ & _ & Hnev & _).
assert (FS : MRX_STK = 8384) by (vm_compute; reflexivity).
assert (FH : HOFF_STK = 80 + 2 * ESTACK) by reflexivity.
assert (EST : 0 <= ESTACK) by (unfold ESTACK; lia).
assert (AFV : AF_m_rx = 14716) by (vm_compute; reflexivity).
assert (Hk2 : 0 <= AF_m_rx + off + 8 < 2 ^ 40 /\ (AF_m_rx + off + 8) mod 2 = 0)
  by (rewrite AFV; destruct Hoff as [-> | ->]; unfold OFF_SET, OFF_E0L; (split; [lia | reflexivity])).
apply (set_jal Wc ly2 S2 regs2 mem2 md2 off Q HJ Hoff).
clear HJ.
intros regsA memA mdA HJ KA1 R1 R10 R11' HP0.
unfold MRX_FRAME in *.
assert (R11 : YK11.getr regsA 11 = w64 why) by (rewrite R11'; exact Hr11).
assert (R2 : YK11.getr regsA 2 = Z_to_bv 64 (sp1 - 112))
  by (rewrite <- Hsp; exact (HP0 2 ltac:(unfold acallee_saved; lia))).
assert (R3' : YK11.getr regsA 3 = YK11.getr regs0 3)
  by (rewrite <- Hgp2; exact (HP0 3 ltac:(unfold acallee_saved; lia))).
assert (R4' : YK11.getr regsA 4 = YK11.getr regs0 4)
  by (rewrite <- Htp2; exact (HP0 4 ltac:(unfold acallee_saved; lia))).
assert (R9 : YK11.getr regsA 9 = YK11.getr regs2 9) by exact (HP0 9 ltac:(unfold acallee_saved; lia)).
assert (RH : mrx_hi regs0 regsA)
  by (intros q Hq; rewrite <- (Hhi q Hq); exact (HP0 q ltac:(unfold acallee_saved; lia))).
assert (R3 : YK11.getr regsA 3 = w64 (as_gp B)) by (rewrite R3'; exact Hgp0).
assert (R4 : YK11.getr regsA 4 = w64 (as_tp B)) by (rewrite R4'; exact Htp0).
destruct (mrx_pre sp1 regsA (AF_m_rx + off + 8) Hsp16 Hceil H47 (proj1 Hk2) (proj2 Hk2) R1 R2)
  as (HRO1 & HRA4 & HSP1 & HM16 & HLO & HHI).
assert (HSV1 : mrx_saved Wc memA sp1 regs0)
  by (apply (mrx_saved_kept Wc Wc mem2 memA sp1 regs0 HSV); intros a Ha; apply KA1; lia).
assert (HTW1 : tw_at TMAP_B (aview sgs (w_H Wc) memA) Bwc).
{ apply (tw_kept TMAP_B (aview sgs (w_H Wc) mem2) _ Bwc HTW).
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KA1. lia. }
eapply SRr_bind.
{ apply (HMSET fx MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc memA mdA 0 regsA TC.S_IDLE why Bwc B6);
  [ exact HJ | exact HRO1 | exact HRA4 | exact R3 | exact R4 | exact R10 | exact R11 | exact HM16
  | unfold MSET_STK, MSET_FRAME; lia | exact HHI | exact HTW1 | exact Hms | unfold TC.S_IDLE; lia | exact Hwhy
  | unfold MSET_EV; lia ]. }
cbv beta. intros W2 c2 _ HQ.
unfold transport_mset_post, transport_cg_post in HQ.
destruct HQ as (ly3 & S3 & regs3 & mem3 & md3 & e & Hc3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HX3).
assert (He0 : e = 0) by (unfold MSET_EV in He3; lia). subst e.
rewrite Z.add_0_r in HJ3. rewrite R1 in Hc3. subst c2.
destruct HK3 as (HK1 & _).
assert (K1 : forall a, sp1 - 32 <= a < sp1 -> aview sgs (w_H W2) mem3 a = aview sgs (w_H Wc) memA a).
{ intros a Ha. apply HK1; [lia|]. rewrite HSP1. unfold MSET_STK, MSET_FRAME, MRX_FRAME. lia. }
destruct (mrx_next B MT MTL sp1 regs0 lyc Sc Wc W2 memA mem3 regsA regs3 S2 S3 ly2 ly3 MSET_STK
  ltac:(unfold MSET_STK, MSET_FRAME; lia) ltac:(unfold MSET_STK, MSET_FRAME, MRX_FRAME; lia)
  HSP1 HSV1 K1 HP3 R2 R3' R4' RH Hfr Hfr3 Hperm Hperm3 Hmo Hmo3)
  as (HSV3 & Q2 & Q3 & Q4 & QH & F3 & P3' & M3).
apply (KN W2 ly3 S3 regs3 mem3 md3 HJ3 F3 P3' M3 Q2 Q3 Q4 QH HSV3 HX3).
rewrite <- R9. exact (HP3 9 ltac:(unfold acallee_saved; lia)).
Qed.

(* The end of a run from a cut that wrote nothing, at the cut pc: the common facts of mrx_at. *)
Lemma set_close : forall (Wc : world sgs) Bwc ly2 S2 regs2 mem2 ms md pc R,
  @W_journalG.ajournal_gx rc tfib_sink_head sgs B TG.G_HARNESS_B 0 [] MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc (ms_mem ms) md 0 ->
  frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> mo_le MT Sc S2 0 ->
  YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regs2 3 = YK11.getr regs0 3 -> YK11.getr regs2 4 = YK11.getr regs0 4 ->
  mrx_hi regs0 regs2 -> mrx_saved Wc mem2 sp1 regs0 ->
  tw_at TMAP_B (aview sgs (w_H Wc) mem2) Bwc ->
  (forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem ms) a = aview sgs (w_H Wc) mem2 a) ->
  aregs_preserved regs2 (ms_regs ms) ->
  K pc R -> R Wc Bwc ly2 S2 (ms_regs ms) (ms_mem ms) ->
  SRr sgs Wc (mkCfg (@YK11.mkst fx (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (YK11.seg_rom sgs)) md)
    (mrx_ipost B MT sp1 regs0 lyc Sc W memc mdc Bw' r).
Proof.
intros Wc Bwc ly2 S2 regs2 mem2 ms md pc R HJ Hfr Hperm Hmo Hsp Hgp Htp Hhi HSV HTW KA HP KX HRx.
pose proof HST as (_ & _ & _ & H46 & H47 & _).
assert (FS : MRX_STK = 8384) by (vm_compute; reflexivity).
apply (KX Wc Bwc).
apply (@mrx_at_intro fx rc B MT sp1 regs0 lyc Sc W memc mdc pc R Wc Bwc ly2 S2).
- exact HJ.
- exact Hfr.
- exact Hperm.
- exact Hmo.
- rewrite <- Hsp. exact (HP 2 ltac:(unfold acallee_saved; lia)).
- rewrite <- Hgp. exact (HP 3 ltac:(unfold acallee_saved; lia)).
- rewrite <- Htp. exact (HP 4 ltac:(unfold acallee_saved; lia)).
- intros q Hq. rewrite <- (Hhi q Hq). exact (HP q ltac:(unfold acallee_saved; lia)).
- apply (mrx_saved_kept Wc Wc mem2 (ms_mem ms) sp1 regs0 HSV). intros a Ha. apply KA. lia.
- apply (tw_kept TMAP_B (aview sgs (w_H Wc) mem2) _ Bwc HTW). intros x Hx.
  pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KA. lia.
- exact HRx.
Qed.

(* ---- SET: `mv a0, zero`, `jal m_set`, then the jump to the TICK cut ---- *)
Lemma mrx_seg_set : K (MRX_PC OFF_TICK) (R_TICK Bw' r) -> K (MRX_PC OFF_SET) (R_SET Bw' r).
Proof using All.
intros KT. unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & Hfr & Hperm & Hmo & Hsp & Hgp2 & Htp2 & Hhi & HSV & HTW & HR).
destruct HR as (why & B3 & Hr11 & Hwhy & Hms & Hm3 & Hr1). subst c.
rewrite (mrx_pcv OFF_SET).
apply (set_call Wc Bwc ly2 S2 regs2 mem2 md2 OFF_SET why B3 _ HJ Hfr Hperm Hmo Hsp Hgp2 Htp2
  Hhi HSV HTW Hr11 Hwhy Hms (or_introl eq_refl)).
intros W2 ly3 S3 regs3 mem3 md3 HJ3 F3 P3 M3 Q2 Q3 Q4 QH HSV3 HTW3 _.
(* the return at +0x1d4: `j` to the TICK cut *)
pose proof (set_entry W2 regs3 mem3 (AF_m_rx + OFF_SET + 8)) as HS.
pose proof (set_img regs3 []) as HEI.
pose proof (set_shok regs3 [] W2 mem3) as SHOK.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ3 SHOK (0, 0) (AF_m_rx + OFF_TICK).
{ AAN.annt_awr_ro. }
set_md.
lazymatch type of HS with context [restrict _ ?m] => rename m into msB end.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H W2) (ms_mem msB) a = aview sgs (w_H W2) mem3 a)
  by (set_kept HFr).
clear HF HFr HG.
assert (HP : aregs_preserved regs3 (ms_regs msB))
  by (apply (aregs_preserved_of_st_ok sgs (w_H W2) (Eimg (PI := PI_transportb) (Ereg regs3 [])) _ msB regs3 [] HS);
      [apply set_agree | vm_compute; reflexivity]).
pmkst HS. AAN.annt_pc (MRX_PC OFF_TICK).
apply (set_close W2 B3 ly3 S3 regs3 mem3 msB _ _ _ HJ3 F3 P3 M3 Q2 Q3 Q4 QH HSV3 HTW3 KA HP KT).
split; [exact Hm3 | exact Hr1].
Qed.

(* ---- E0L: `mv a0, zero`, `jal m_set` (a1 = 3), then a0 = M.state at the E0W cut ---- *)
Lemma mrx_seg_e0l : K (MRX_PC OFF_E0W) (R_E0W Bw' r) -> K (MRX_PC OFF_E0L) (R_E0L Bw' r).
Proof using All.
intros KW. unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & Hfr & Hperm & Hmo & Hsp & Hgp2 & Htp2 & Hhi & HSV & HTW & HR).
destruct HR as (B6 & B3 & Hr9 & Hr11 & Hms & He0w & Hm3 & Hr1). subst c.
rewrite (mrx_pcv OFF_E0L).
apply (set_call Wc Bwc ly2 S2 regs2 mem2 md2 OFF_E0L 3 B6 _ HJ Hfr Hperm Hmo Hsp Hgp2 Htp2
  Hhi HSV HTW Hr11 ltac:(lia) Hms (or_intror eq_refl)).
intros W2 ly3 S3 regs3 mem3 md3 HJ3 F3 P3 M3 Q2 Q3 Q4 QH HSV3 HTW3 Q9.
rewrite Hr9 in Q9.
(* the return at +0x374: `lw a0, 12(s1)`, at the E0W cut *)
replace (AF_m_rx + OFF_E0L + 8) with E0L_RET by (vm_compute; reflexivity).
pose proof (e0l_entry W2 regs3 mem3 B6 HTW3 Q9) as HS.
set (E3 := e0l_E regs3 B6) in HS.
assert (HEI : img_env VAL A_LIM E3) by (unfold E3, e0l_E; apply Eimg_env).
assert (SHOK : sh_ok sgs (SLit 0) [] E3 (mrestrict (w_H W2) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (E32 : ew E3 32 = Z_to_bv 64 (TW.u_at B6 TW.A_M_state 4))
  by (unfold E3, e0l_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
pose proof (TWL.u_at_range B6 TW.A_M_state 4) as R32. change (8 * Z.of_nat 4) with 32 in R32.
assert (D32 : sv_denot E3 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.M_state B6))
  by exact (AAN.annt_sext E3 32 _ E32 R32).
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ3 SHOK (0, 0) (AF_m_rx + OFF_E0W).
{ AAN.annt_awr_ro. }
set_md.
lazymatch type of HS with context [restrict _ ?m] => rename m into msB end.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H W2) (ms_mem msB) a = aview sgs (w_H W2) mem3 a)
  by (set_kept HFr).
clear HF HFr HG.
assert (AGR3 : env_agree 32 (Ereg regs3 [Z_to_bv 64 (TW.u_at B6 TW.A_M_state 4)]) E3)
  by (unfold E3, e0l_E; apply set_agree).
assert (HP : aregs_preserved regs3 (ms_regs msB))
  by (apply (aregs_preserved_of_st_ok sgs (w_H W2) E3 _ msB regs3 _ HS AGR3); vm_compute; reflexivity).
set_reg HS (Z_to_bv 5 10) (w64 (TW.M_state B6)) RB10 ltac:(exact D32).
pmkst HS. AAN.annt_pc (MRX_PC OFF_E0W).
apply (set_close W2 B6 ly3 S3 regs3 mem3 msB _ _ _ HJ3 F3 P3 M3 Q2 Q3 Q4 QH HSV3 HTW3 KA HP KW).
exists B3. split; [exact RB10|]. split; [exact He0w|]. split; [exact Hm3 | exact Hr1].
Qed.

(* ---- E0W: a0 = M.state; S_IDLE and g_cfg.auto_wake go to the WAKE cut, else the TICK cut ---- *)
Lemma mrx_seg_e0w : K (MRX_PC OFF_WAKE) (R_WAKE Bw' r) -> K (MRX_PC OFF_TICK) (R_TICK Bw' r) ->
  K (MRX_PC OFF_E0W) (R_E0W Bw' r).
Proof using All.
intros KW KT. unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hperm & Hmo & Hsp & Hgp2 & Htp2 & Hhi & HSV & HTW & HR).
destruct HR as (B3 & Hr10 & He0w & Htk & Hr1).
pose proof (AAN.e0w_model Bwc B3 He0w) as HM. clear He0w.
set (E0 := e0w_E regs2 Bwc).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, e0w_E; apply Eimg_env).
assert (EE : forall n0 (r0 : bv 5), Z.of_nat n0 = bv_unsigned r0 -> ew E0 n0 = YK11.getr regs2 r0)
  by (intros n0 r0 Hn; unfold E0, e0w_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (D10 : sv_denot E0 (SOff 10 0) = Z_to_bv 64 (TW.M_state Bwc))
  by (cbn [sv_denot]; rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hr10).
assert (E32 : ew E0 32 = Z_to_bv 64 (TW.u_at Bwc TW.A_Cfg_auto_wake 4))
  by (unfold E0, e0w_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
pose proof (TWL.u_at_range Bwc TW.A_Cfg_auto_wake 4) as R32. change (8 * Z.of_nat 4) with 32 in R32.
assert (D32 : sv_denot E0 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.Cfg_auto_wake Bwc))
  by exact (AAN.annt_sext E0 32 _ E32 R32).
pose proof (TWL.s32_range Bwc TW.A_M_state) as S10. pose proof (TWL.s32_range Bwc TW.A_Cfg_auto_wake) as S32.
change (TW.s32_at Bwc TW.A_M_state) with (TW.M_state Bwc) in S10.
change (TW.s32_at Bwc TW.A_Cfg_auto_wake) with (TW.Cfg_auto_wake Bwc) in S32.
pose proof (e0w_entry Wc regs2 mem2 Bwc HTW) as HS. fold E0 in HS.
assert (SHOK : sh_ok sgs (SLit 0) [] E0 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok; apply Forall_nil).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX
  0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
assert (AGR : env_agree 32 (Ereg regs2 [Z_to_bv 64 (TW.u_at Bwc TW.A_Cfg_auto_wake 4)]) E0)
  by (unfold E0, e0w_E; apply set_agree).
rewrite (mrx_pcv OFF_E0W).
(* +0x378: `bnez a0` *)
psrr_branch_tok RUN BR HS SHOK (0, 0).
- (* M.state <> S_IDLE: the cut TICK, the world unchanged *)
  rewrite D10 in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (EPI.mrxk_eqb (TW.M_state Bwc) 0 ltac:(lia) ltac:(lia)) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  destruct HM as [[_ HB3] | [[Hs _] | [Hs _]]]; [| exfalso; exact (Hc Hs) | exfalso; exact (Hc Hs)].
  subst B3.
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) (AF_m_rx + OFF_TICK).
  { AAN.annt_awr_ro. }
  set_md.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms end.
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem ms) a = aview sgs (w_H Wc) mem2 a)
    by (set_kept HFr).
  clear HF HFr HG.
  assert (HP : aregs_preserved regs2 (ms_regs ms))
    by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) E0 _ ms regs2 _ HS AGR); vm_compute; reflexivity).
  pmkst HS. AAN.annt_pc (MRX_PC OFF_TICK).
  apply (set_close Wc Bwc ly2 S2 regs2 mem2 ms _ _ _ HJ Hfr Hperm Hmo Hsp Hgp2 Htp2 Hhi HSV HTW KA HP KT).
  split; [exact Htk | exact Hr1].
- (* M.state = S_IDLE: g_cfg.auto_wake *)
  rewrite D10 in Hc. cbn [branch_taken sv_denot] in Hc.
  rewrite (EPI.mrxk_eqb (TW.M_state Bwc) 0 ltac:(lia) ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  destruct HM as [[Hs _] | HM]; [exfalso; exact (Hs Hc)|]. rename Hc into Hst0.
  (* +0x37c .. +0x380: auto_wake; it stops at `beqz a0` *)
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { AAN.annt_awr_ro. }
  set_md.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms2 end.
  assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem ms2) a = aview sgs (w_H Wc) mem2 a)
    by (set_kept HFr).
  clear HF HFr HG.
  assert (HP2 : aregs_preserved regs2 (ms_regs ms2))
    by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) E0 _ ms2 regs2 _ HS AGR); vm_compute; reflexivity).
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  + (* auto_wake = 0: the cut TICK, the world unchanged *)
    rewrite D32 in Hc. cbn [branch_taken sv_denot] in Hc.
    rewrite (EPI.mrxk_eqb (TW.Cfg_auto_wake Bwc) 0 ltac:(lia) ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    destruct HM as [(_ & _ & HB3) | (_ & Ha & _)]; [| exfalso; exact (Ha Hc)].
    subst B3.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) (AF_m_rx + OFF_TICK).
    { AAN.annt_awr_ro. }
    set_md.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms end.
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem ms) a = aview sgs (w_H Wc) mem2 a).
    { intros a Ha. rewrite <- (KA2 a Ha). set_kept1 HFr Ha. }
    clear HF HFr HG.
    assert (HP : aregs_preserved regs2 (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) E0 _ ms regs2 _ HS AGR); vm_compute; reflexivity).
    pmkst HS. AAN.annt_pc (MRX_PC OFF_TICK).
    apply (set_close Wc Bwc ly2 S2 regs2 mem2 ms _ _ _ HJ Hfr Hperm Hmo Hsp Hgp2 Htp2 Hhi HSV HTW KA HP KT).
    split; [exact Htk | exact Hr1].
  + (* auto_wake <> 0: the cut WAKE *)
    rewrite D32 in Hc. cbn [branch_taken sv_denot] in Hc.
    rewrite (EPI.mrxk_eqb (TW.Cfg_auto_wake Bwc) 0 ltac:(lia) ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
    destruct HM as [(_ & Ha & _) | (_ & _ & rw & Hwk)]; [exfalso; exact (Hc Ha)|].
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) (AF_m_rx + OFF_WAKE).
    { AAN.annt_awr_ro. }
    set_md.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms end.
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem ms) a = aview sgs (w_H Wc) mem2 a).
    { intros a Ha. rewrite <- (KA2 a Ha). set_kept1 HFr Ha. }
    clear HF HFr HG.
    assert (HP : aregs_preserved regs2 (ms_regs ms))
      by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) E0 _ ms regs2 _ HS AGR); vm_compute; reflexivity).
    pmkst HS. AAN.annt_pc (MRX_PC OFF_WAKE).
    apply (set_close Wc Bwc ly2 S2 regs2 mem2 ms _ _ _ HJ Hfr Hperm Hmo Hsp Hgp2 Htp2 Hhi HSV HTW KA HP KW).
    exists B3, rw. split; [exact Hwk|]. split; [exact Htk | exact Hr1].
Qed.

End seg.
