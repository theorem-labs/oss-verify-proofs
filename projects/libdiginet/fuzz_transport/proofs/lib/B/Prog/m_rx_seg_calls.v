(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 526 of its 610 lines of code are new or changed and 946 lines of the source are left out. *)
(* m_rx_seg_calls: the call segments of the image-B walk of m_rx (the cuts of lib/B/Prog/m_rx_seg_kit.v, chained in
   m_rx_cgW.v): the epilogue to the return (mrx_seg_epi), and the three `jal`s of a G-form callee that end the walk,
   each from its cut to the cut its return address lies at (mrx_seg_tick, mrx_seg_mo, mrx_seg_wake).

   Every segment runs the symbolic runs of lib/A/Prog/PaShadow.v at image B's listing over the walk's inner G
   journal (lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x), from a state with no region (the `jal`s and the
   jumps after them read no memory) or, for the epilogue, with ONE read-only region: the 4 saved slots of the frame,
   whose chunks hold the entry registers (the cut's mrx_saved, read through YCbq.v val_mem_of_rdword).
     EPI  +0x030 .. +0x044  the 4 loads (ra, s0, s1, s2), `sp = sp + 112`, `ret`: the registers are the entry's
                            (s3 .. s11 are the cut's mrx_hi), nothing changed.
     TICK +0x3a4            `jal m_tick`, the return at +0x3a8, `a0 = 1`, `j` to the epilogue (+0x030).
     MO   +0x3a0            `jal m_maybe_online`, the return at +0x3a4 = the TICK cut.
     WAKE +0x388            `jal m_wake`, the return at +0x38c, `j` to +0x3a4 = the TICK cut.
   A callee is entered on the walk's own journal with ra = the return address, sp = sp1 - 112 and the entry gp / tp
   (the kit's mrx_pre); its post gives the next cut (the kit's mrx_next): the journal, the frames, the blocks and the
   meter compose, the saved slots are kept (they lie above the callee's stack window), and the callee-saved registers
   carry sp, gp, tp and s3 .. s11. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg m_wake_cg m_maybe_online_cg m_tick_cg spec_read_frame_cg host_offset_cg desk_named_cg check_state_data_cg
  m_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require m_rx.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  TransportGRunB TransportGFrameB CanKit YC1g YC1h m_rx_seg_kit.
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
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The value of register q in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac calls_reg HS q v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) q) in
      assert (H : YK11.getr (ms_regs msx) q = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx q HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) q) in
      assert (H : YK11.getr (ms_regs msx) q = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx q HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "calls_reg: no match for" T; fail
  end.

(* The write rights of a run whose regions have no writable byte. *)
Ltac calls_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* A run of such a state wrote nothing: every byte's view is the one it started from. *)
Ltac calls_kept HFr :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr);
  [ let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; exfalso;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia |]);
    destruct Hin
  | exact Ha
  | let Hf := fresh "Hf" in intros Hf; destruct Hf ].

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

(* ---- the walk's valuation: the registers at the cut, the shadow base, the 4 entry registers ---- *)

Definition calls_extra : list word :=
  [Z_to_bv 64 SHADOW_OFF;
   YK11.getr regs0 (Z_to_bv 5 1); YK11.getr regs0 (Z_to_bv 5 8); YK11.getr regs0 (Z_to_bv 5 9);
   YK11.getr regs0 (Z_to_bv 5 18)].
Definition calls_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs calls_extra).
Definition calls_Bx : sv := SOff 32 0.
Definition calls_SH : list shent := [].
Definition calls_F : facts := mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition calls_FE : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].

(* The 4 saved slots of the frame, read-only, each chunk the entry register MRX_SAVES names. *)
Definition calls_epi_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 80 112 0 0
   [YP09.mkChunk 104 (YP09.CVal 8 (SOff 33 0)); YP09.mkChunk 96 (YP09.CVal 8 (SOff 34 0));
    YP09.mkChunk 88 (YP09.CVal 8 (SOff 35 0)); YP09.mkChunk 80 (YP09.CVal 8 (SOff 36 0))].
Definition ss_calls (k : Z) : sstate := mkSS k sr_atoms [] None calls_F.
Definition ss_epi : sstate := mkSS (AF_m_rx + OFF_EPI) sr_atoms [calls_epi_region] None calls_FE.

Lemma calls_img : forall regs, img_env VAL A_LIM (calls_E regs).
Proof. intros regs. unfold calls_E. apply Eimg_env. Qed.

Lemma calls_agree : forall regs, env_agree 32 (Ereg regs calls_extra) (calls_E regs).
Proof.
intros regs. split; [intros m Hm; unfold calls_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

Lemma calls_ew32 : forall regs, ew (calls_E regs) 32%nat = Z_to_bv 64 SHADOW_OFF.
Proof.
intros regs. unfold calls_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs calls_extra 0%nat).
Qed.

Lemma calls_ewr : forall regs (q : bv 5) m, Z.of_nat m = bv_unsigned q -> ew (calls_E regs) m = YK11.getr regs q.
Proof. intros regs q m Hm. unfold calls_E. apply ew_Eimg_Ereg_nat. exact Hm. Qed.

Lemma calls_shok : forall regs (W2 : world sgs) mem,
  sh_ok sgs calls_Bx calls_SH (calls_E regs) (mrestrict (w_H W2) mem).
Proof. intros regs W2 mem. unfold sh_ok, calls_SH. apply Forall_nil. Qed.

(* The static facts of the entry, named. *)
Ltac calls_st :=
  let HH := fresh "HSTx" in
  pose proof HST as HH;
  destruct HH as (Hsp1 & Hsp16 & Hceil & H46 & H47 & Hrao & Hra4 & Hgp0 & Htp0 & Ha00 & Ha10 & Hfa0 & Hfan & Hfam &
                  Hsrc & Hdisj & Hapart & Hnev & HAR).

(* The sizes the segments use, as numerals. *)
Ltac calls_sizes :=
  assert (FS : MRX_STK = 8384) by reflexivity;
  assert (FH : HOFF_STK = 8272) by reflexivity;
  unfold MRX_FRAME in *;
  assert (FM : MRX_FRAME = 112) by reflexivity.

(* ---- the entry states ---- *)

Lemma calls_entry : forall (W2 : world sgs) (regs : bvmap 5 word) mem k,
  st_ok_pi sgs VAL (calls_E regs) (ss_calls k)
    (restrict (w_H W2) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom sgs))).
Proof.
intros W2 regs mem k. rewrite restrict_mkst_fx. unfold ss_calls.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- unfold calls_F, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite calls_ew32. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* One saved slot as a chunk of the frame region. *)
Lemma calls_chunk : forall (Wc : world sgs) mem (E : env) (rz off : Z) (at_ : nat),
  rdword (aview sgs (w_H Wc) mem) (sp1 - MRX_FRAME + off) =
    Some (bv_unsigned (YK11.getr regs0 (Z_to_bv 5 rz))) ->
  ew E at_ = YK11.getr regs0 (Z_to_bv 5 rz) ->
  base_val E (Some 2%nat) = sp1 - MRX_FRAME ->
  YP09.chunk_ok sgs E (mrestrict (w_H Wc) mem) (sp1 - MRX_FRAME)
    (YP09.mkChunk off (YP09.CVal 8 (SOff at_ 0))).
Proof.
intros Wc mem E rz off at_ Hrd Hew Hbase.
pose proof (bv_unsigned_in_range 64 (YK11.getr regs0 (Z_to_bv 5 rz))) as Hr64.
change (bv_modulus 64) with (2 ^ 64) in Hr64.
apply (chunk_ok_val sgs E _ (sp1 - MRX_FRAME) off 8 (SOff at_ 0)
  (bv_unsigned (YK11.getr regs0 (Z_to_bv 5 rz)))).
- cbn [sv_denot]. rewrite Hew, Z.add_0_r. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
- cbn [Z.of_N]. lia.
- exact (val_mem_of_rdword sgs (w_H Wc) mem _ _ Hrd).
Qed.

Lemma calls_entry_epi : forall (W2 : world sgs) (regs : bvmap 5 word) mem,
  YK11.getr regs (Z_to_bv 5 2) = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  mrx_saved W2 mem sp1 regs0 ->
  st_ok_pi sgs VAL (calls_E regs) ss_epi
    (restrict (w_H W2) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_m_rx + OFF_EPI))) mem (YK11.seg_rom sgs))).
Proof.
intros W2 regs mem Hsp HSV. calls_st. calls_sizes.
assert (E2 : ew (calls_E regs) 2%nat = Z_to_bv 64 (sp1 - 112))
  by (rewrite (calls_ewr regs (Z_to_bv 5 2) 2%nat ltac:(vm_compute; reflexivity)); exact Hsp).
assert (U2 : bv_unsigned (ew (calls_E regs) 2%nat) = sp1 - 112)
  by (rewrite E2; apply unsigned_lit_small; lia).
assert (Hbase : base_val (calls_E regs) (Some 2%nat) = sp1 - 112) by (cbn [base_val]; exact U2).
assert (EX : forall j, (j < 5)%nat -> ew (calls_E regs) (32 + j) = nth j calls_extra (Z_to_bv 64 0))
  by (intros j Hj; unfold calls_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 1%nat ltac:(lia)) as A33. pose proof (EX 2%nat ltac:(lia)) as A34.
pose proof (EX 3%nat ltac:(lia)) as A35. pose proof (EX 4%nat ltac:(lia)) as A36.
cbn [Nat.add nth calls_extra] in A33, A34, A35, A36.
assert (SV : forall p, In p MRX_SAVES ->
  rdword (aview sgs (w_H W2) mem) (sp1 - 112 + snd p) =
    Some (bv_unsigned (YK11.getr regs0 (Z_to_bv 5 (fst p)))))
  by (apply Forall_forall; exact HSV).
rewrite restrict_mkst_fx. unfold ss_epi.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold calls_epi_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Hbase. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat (apply Forall_cons; [first
    [ exact (calls_chunk W2 mem _ 1 104 33%nat (SV (1, 104) ltac:(cbn [MRX_SAVES In]; tauto)) A33 Hbase)
    | exact (calls_chunk W2 mem _ 8 96 34%nat (SV (8, 96) ltac:(cbn [MRX_SAVES In]; tauto)) A34 Hbase)
    | exact (calls_chunk W2 mem _ 9 88 35%nat (SV (9, 88) ltac:(cbn [MRX_SAVES In]; tauto)) A35 Hbase)
    | exact (calls_chunk W2 mem _ 18 80 36%nat (SV (18, 80) ltac:(cbn [MRX_SAVES In]; tauto)) A36 Hbase)] |]);
  apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- unfold calls_FE, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite calls_ew32. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  rewrite U2. rewrite Z.pow_0_r, Z.mod_1_r. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
  replace (sp1 - 112) with (sp1 + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
Qed.

(* ---- EPI: the epilogue and the return ---- *)

Lemma mrx_seg_epi : K (MRX_PC OFF_EPI) (R_EPI Bw' r).
Proof using All.
unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & Hfr & Hperm & Hmo & Hsp & Hgp2 & Htp2 & Hhi2 & HSV & HTW &
                 HR).
destruct HR as [HBw Ha0]. subst Bwc. subst c.
calls_st. calls_sizes.
rewrite (mrx_pcv OFF_EPI).
pose proof (calls_entry_epi Wc regs2 mem2 Hsp HSV) as HS.
pose proof (calls_img regs2) as HEI.
pose proof (calls_shok regs2 Wc mem2) as SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
(* the 4 loads, `sp = sp + 112`, stop at `ret` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ calls_awr. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem ms) a = aview sgs (w_H Wc) mem2 a)
  by (calls_kept HFr).
assert (E2 : ew (calls_E regs2) 2%nat = Z_to_bv 64 (sp1 - 112))
  by (rewrite (calls_ewr regs2 (Z_to_bv 5 2) 2%nat ltac:(vm_compute; reflexivity)); exact Hsp).
assert (U2 : bv_unsigned (ew (calls_E regs2) 2%nat) = sp1 - 112)
  by (rewrite E2; apply unsigned_lit_small; lia).
assert (EX : forall j, (j < 5)%nat -> ew (calls_E regs2) (32 + j) = nth j calls_extra (Z_to_bv 64 0))
  by (intros j Hj; unfold calls_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 1%nat ltac:(lia)) as A33. pose proof (EX 2%nat ltac:(lia)) as A34.
pose proof (EX 3%nat ltac:(lia)) as A35. pose proof (EX 4%nat ltac:(lia)) as A36.
cbn [Nat.add nth calls_extra] in A33, A34, A35, A36.
assert (EE : forall m (q : bv 5), Z.of_nat m = bv_unsigned q -> ew (calls_E regs2) m = YK11.getr regs2 q)
  by (intros m q Hm; apply calls_ewr; exact Hm).
assert (Hsp0 : YK11.getr regs0 2 = Z_to_bv 64 sp1).
{ rewrite <- Hsp1. change (spZ regs0) with (bv_unsigned (YK11.getr regs0 2)).
  symmetry. apply Z_to_bv_bv_unsigned. }
(* the restored registers *)
calls_reg HS (1%bv : bv 5) (YK11.getr regs0 1) RF1
  ltac:(cbn [sv_denot]; rewrite A33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
calls_reg HS (Z_to_bv 5 10) (w64 r) RF10
  ltac:(cbn [sv_denot]; rewrite (EE 10%nat (Z_to_bv 5 10) ltac:(vm_compute; reflexivity)), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Ha0).
assert (HPF : aregs_preserved regs0 (ms_regs ms)).
{ intros q Hq. unfold acallee_saved in Hq.
  assert (HQ : (19 <= q <= 27) \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18) by lia.
  clear Hq.
  destruct HQ as [HQ | HQ].
  { (* s3 .. s11: the epilogue does not write them; the cut's mrx_hi *)
    assert (HQ' : q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
    clear HQ.
    repeat (destruct HQ' as [HQ' | HQ']); subst q;
    lazymatch goal with |- YK11.getr _ (Z_to_bv 5 ?qq) = _ =>
      let P := fresh "P" in
      calls_reg HS (Z_to_bv 5 qq) (YK11.getr regs0 (Z_to_bv 5 qq)) P
        ltac:(cbn [sv_denot];
              lazymatch goal with |- context [ew _ ?m] =>
                rewrite (EE m (Z_to_bv 5 qq) ltac:(vm_compute; reflexivity)) end;
              rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact (Hhi2 qq ltac:(lia)));
      exact P end. }
  repeat (destruct HQ as [HQ | HQ]); subst q.
  - calls_reg HS (Z_to_bv 5 2) (YK11.getr regs0 (Z_to_bv 5 2)) P2
      ltac:(cbn [sv_denot]; rewrite U2; replace (sp1 - 112 + 112) with sp1 by lia;
            exact (eq_sym Hsp0)).
    exact P2.
  - calls_reg HS (Z_to_bv 5 3) (YK11.getr regs0 (Z_to_bv 5 3)) P3
      ltac:(cbn [sv_denot]; rewrite (EE 3%nat (Z_to_bv 5 3) ltac:(vm_compute; reflexivity)), Z.add_0_r,
            Z_to_bv_bv_unsigned; exact Hgp2).
    exact P3.
  - calls_reg HS (Z_to_bv 5 4) (YK11.getr regs0 (Z_to_bv 5 4)) P4
      ltac:(cbn [sv_denot]; rewrite (EE 4%nat (Z_to_bv 5 4) ltac:(vm_compute; reflexivity)), Z.add_0_r,
            Z_to_bv_bv_unsigned; exact Htp2).
    exact P4.
  - calls_reg HS (Z_to_bv 5 8) (YK11.getr regs0 (Z_to_bv 5 8)) P8
      ltac:(cbn [sv_denot]; rewrite A34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    exact P8.
  - calls_reg HS (Z_to_bv 5 9) (YK11.getr regs0 (Z_to_bv 5 9)) P9
      ltac:(cbn [sv_denot]; rewrite A35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    exact P9.
  - calls_reg HS (Z_to_bv 5 18) (YK11.getr regs0 (Z_to_bv 5 18)) P18
      ltac:(cbn [sv_denot]; rewrite A36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    exact P18. }
eapply (RET Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
unfold mrx_ipost.
exists ly2, S2, (ms_regs ms), (ms_mem ms).
eexists.
split; [rewrite RF1; unfold YK0s.ret_ok in Hrao; rewrite Hrao; reflexivity|].
split; [apply (ajournal_gx_materialize sgs B LAWS transportb_segs_low); exact HJ|].
split; [exact HPF|].
split; [exact Hfr|].
split; [exact Hperm|].
split; [exact Hmo|].
split; [exact RF10|].
apply (tw_kept TMAP_B (aview sgs (w_H Wc) mem2) _ Bw' HTW).
intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KA. lia.
Qed.

(* ---- the `jal`s of a G-form callee ---- *)

(* The listing offsets: EPI 0x397c + 0x030, WAKE's return 0x397c + 0x38c, MO 0x397c + 0x3a0, TICK 0x397c + 0x3a4
   (MO's return), TICK's return 0x397c + 0x3a8. *)
Lemma calls_pc_epi : BASE + 14764 = MRX_PC OFF_EPI.
Proof. rewrite (mrx_pcv OFF_EPI). f_equal; vm_compute; reflexivity. Qed.
Lemma calls_pc_tick : BASE + 15648 = MRX_PC OFF_TICK.
Proof. rewrite (mrx_pcv OFF_TICK). f_equal; vm_compute; reflexivity. Qed.

(* The run of a `jal` from a cut, and what the callee's contract takes of the state at its entry: the return
   address, sp, gp, tp, s3 .. s11, the saved slots and the world relation at the run's memory. *)
Lemma calls_jal_facts : forall (Wc : world sgs) (Bwc : list byte) mem2 msA (regs2 : bvmap 5 word) (kret : Z),
  0 <= kret < 2 ^ 40 -> kret mod 2 = 0 ->
  YK11.getr (ms_regs msA) 1 = Z_to_bv 64 (BASE + kret) ->
  aregs_preserved regs2 (ms_regs msA) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem msA) a = aview sgs (w_H Wc) mem2 a) ->
  YK11.getr regs2 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regs2 3 = YK11.getr regs0 3 -> YK11.getr regs2 4 = YK11.getr regs0 4 ->
  mrx_hi regs0 regs2 ->
  mrx_saved Wc mem2 sp1 regs0 ->
  tw_at TMAP_B (aview sgs (w_H Wc) mem2) Bwc ->
  YK11.getr (ms_regs msA) 2 = Z_to_bv 64 (sp1 - MRX_FRAME) /\
  YK11.getr (ms_regs msA) 3 = YK11.getr regs0 3 /\ YK11.getr (ms_regs msA) 4 = YK11.getr regs0 4 /\
  YK11.getr (ms_regs msA) 3 = w64 (as_gp B) /\ YK11.getr (ms_regs msA) 4 = w64 (as_tp B) /\
  mrx_hi regs0 (ms_regs msA) /\
  YK0s.ret_ok (YK11.getr (ms_regs msA) 1) /\ 4096 <= raZ (ms_regs msA) /\
  spZ (ms_regs msA) = sp1 - MRX_FRAME /\ spZ (ms_regs msA) mod 16 = 0 /\
  sp1 - MRX_STK <= spZ (ms_regs msA) - HOFF_STK /\ spZ (ms_regs msA) <= sp1 /\
  mrx_saved Wc (ms_mem msA) sp1 regs0 /\
  tw_at TMAP_B (aview sgs (w_H Wc) (ms_mem msA)) Bwc.
Proof.
intros Wc Bwc mem2 msA regs2 kret Hk Hk2 R1 HP0 KA1 Hsp Hgp2 Htp2 Hhi2 HSV HTW.
calls_st. calls_sizes.
assert (R2 : YK11.getr (ms_regs msA) 2 = Z_to_bv 64 (sp1 - 112))
  by (rewrite <- Hsp; exact (HP0 2 ltac:(unfold acallee_saved; lia))).
assert (R3' : YK11.getr (ms_regs msA) 3 = YK11.getr regs0 3)
  by (rewrite <- Hgp2; exact (HP0 3 ltac:(unfold acallee_saved; lia))).
assert (R4' : YK11.getr (ms_regs msA) 4 = YK11.getr regs0 4)
  by (rewrite <- Htp2; exact (HP0 4 ltac:(unfold acallee_saved; lia))).
destruct (mrx_pre sp1 (ms_regs msA) kret Hsp16 Hceil H47 Hk Hk2 R1 R2)
  as (HRO1 & HRA4 & HSP1 & HM16 & HLO & HHI).
split; [exact R2|]. split; [exact R3'|]. split; [exact R4'|].
split; [rewrite R3'; exact Hgp0|]. split; [rewrite R4'; exact Htp0|].
split; [intros q Hq; rewrite <- (Hhi2 q Hq); exact (HP0 q ltac:(unfold acallee_saved; lia))|].
split; [exact HRO1|]. split; [exact HRA4|]. split; [exact HSP1|]. split; [exact HM16|].
split; [exact HLO|]. split; [exact HHI|].
split.
{ apply (mrx_saved_kept Wc Wc mem2 (ms_mem msA) sp1 regs0 HSV). intros a Ha. apply KA1. lia. }
apply (tw_kept TMAP_B (aview sgs (w_H Wc) mem2) _ Bwc HTW).
intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KA1. lia.
Qed.

(* The saved slots' bytes are outside a callee's stack window (spZ - FSTK, spZ), at or above alloc_ceiling. *)
Lemma calls_slots_kept : forall (Wc W2 : world sgs) memA mem3 (regsT : bvmap 5 word) (FSTK : Z),
  spZ regsT = sp1 - MRX_FRAME ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regsT - FSTK <= a < spZ regsT) ->
     aview sgs (w_H W2) mem3 a = aview sgs (w_H Wc) memA a) ->
  forall a, sp1 - 32 <= a < sp1 -> aview sgs (w_H W2) mem3 a = aview sgs (w_H Wc) memA a.
Proof.
intros Wc W2 memA mem3 regsT FSTK HSP K1 a Ha. calls_st. calls_sizes.
apply K1; [lia | rewrite HSP; lia].
Qed.

(* The state after a run that wrote nothing: the saved slots and the world relation at its memory. *)
Lemma calls_after_run : forall (W2 : world sgs) (Bw3 : list byte) mem3 mem4,
  (forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H W2) mem4 a = aview sgs (w_H W2) mem3 a) ->
  mrx_saved W2 mem3 sp1 regs0 ->
  tw_at TMAP_B (aview sgs (w_H W2) mem3) Bw3 ->
  mrx_saved W2 mem4 sp1 regs0 /\ tw_at TMAP_B (aview sgs (w_H W2) mem4) Bw3.
Proof.
intros W2 Bw3 mem3 mem4 KA2 HSV3 HX3. calls_st. calls_sizes.
split.
{ apply (mrx_saved_kept W2 W2 mem3 mem4 sp1 regs0 HSV3). intros a Ha. apply KA2. lia. }
apply (tw_kept TMAP_B (aview sgs (w_H W2) mem3) _ Bw3 HX3).
intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KA2. lia.
Qed.

Lemma mrx_seg_tick : K (MRX_PC OFF_EPI) (R_EPI Bw' r) -> K (MRX_PC OFF_TICK) (R_TICK Bw' r).
Proof using All.
intros KE. unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & Hfr & Hperm & Hmo & Hsp & Hgp2 & Htp2 & Hhi2 & HSV & HTW &
                 HR).
destruct HR as [Hm Hr1]. subst c.
calls_st. calls_sizes.
rewrite (mrx_pcv OFF_TICK).
pose proof (calls_entry Wc regs2 mem2 (AF_m_rx + OFF_TICK)) as HS.
pose proof (calls_img regs2) as HEI.
pose proof (calls_shok regs2 Wc mem2) as SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
(* the `jal m_tick` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ calls_awr. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem msA) a = aview sgs (w_H Wc) mem2 a)
  by (calls_kept HFr).
clear HF HFr HG.
pmkst HS.
calls_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 15652)) R1 ltac:(apply codeptr_val; exact HEI).
assert (HP0 : aregs_preserved regs2 (ms_regs msA))
  by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) (calls_E regs2) _ msA regs2 calls_extra HS);
      [apply calls_agree | vm_compute; reflexivity]).
destruct (calls_jal_facts Wc Bwc mem2 msA regs2 15652 ltac:(lia) ltac:(reflexivity) R1 HP0 KA1 Hsp Hgp2 Htp2 Hhi2
  HSV HTW)
  as (R2 & R3' & R4' & R3 & R4 & RH & HRO1 & HRA4 & HSP1 & HM16 & HLO & HHI & HSV1 & HTW1).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx sgs (transportb_sigma TB_m_tick) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HMT fx MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc (ms_mem msA) _ 0 (ms_regs msA) Bwc Bw');
  [ exact HJ | exact HRO1 | exact HRA4 | exact R3 | exact R4 | exact HM16
  | unfold MTICK_STK, MSET_STK, MSET_FRAME; lia | exact HHI | exact HTW1 | exact Hm
  | unfold MTICK_EV, MSET_EV; lia ]. }
cbv beta. intros W2 c2 _ HQ.
unfold transport_mtick_post, transport_cg_post in HQ.
destruct HQ as (ly3 & S3 & regs3 & mem3 & md3 & e & Hc3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HX3).
assert (He0 : e = 0) by (unfold MTICK_EV, MSET_EV in He3; lia). subst e.
rewrite Z.add_0_r in HJ3. rewrite R1 in Hc3. subst c2.
destruct HK3 as (HK1 & _).
destruct (mrx_next B MT MTL sp1 regs0 lyc Sc Wc W2 (ms_mem msA) mem3 (ms_regs msA) regs3 S2 S3 ly2 ly3 MTICK_STK
  ltac:(unfold MTICK_STK, MSET_STK, MSET_FRAME; lia)
  ltac:(unfold MTICK_STK, MSET_STK, MSET_FRAME; lia)
  HSP1 HSV1 (calls_slots_kept Wc W2 (ms_mem msA) mem3 (ms_regs msA) MTICK_STK HSP1 HK1)
  HP3 R2 R3' R4' RH Hfr Hfr3 Hperm Hperm3 Hmo Hmo3)
  as (HSV3 & Q2 & Q3 & Q4 & QH & F3 & P3' & M3).
(* `a0 = 1` and the jump to the epilogue *)
pose proof (calls_entry W2 regs3 mem3 15652) as HS3.
pose proof (calls_img regs3) as HEI3.
pose proof (calls_shok regs3 W2 mem3) as SHOK3.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 YC4b.Bspan 14764.
{ calls_awr. }
lazymatch type of HS3 with context [restrict _ ?m] => rename m into msB end.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H W2) (ms_mem msB) a = aview sgs (w_H W2) mem3 a)
  by (calls_kept HFr).
assert (EE3 : forall m (q : bv 5), Z.of_nat m = bv_unsigned q -> ew (calls_E regs3) m = YK11.getr regs3 q)
  by (intros m q Hm'; apply calls_ewr; exact Hm').
calls_reg HS3 (Z_to_bv 5 10) (w64 r) RB10 ltac:(rewrite Hr1; reflexivity).
assert (HPB : aregs_preserved regs3 (ms_regs msB))
  by (apply (aregs_preserved_of_st_ok sgs (w_H W2) (calls_E regs3) _ msB regs3 calls_extra HS3);
      [apply calls_agree | vm_compute; reflexivity]).
destruct (calls_after_run W2 Bw' mem3 (ms_mem msB) KA2 HSV3 HX3) as (HSV4 & HTW4).
pmkst HS3. rewrite calls_pc_epi.
apply (KE W2 Bw').
apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_EPI) (R_EPI Bw' r) W2 Bw' ly3 S3 (ms_regs msB)
  (ms_mem msB)).
- exact HJ3.
- exact F3.
- exact P3'.
- exact M3.
- exact (eq_trans (HPB 2 ltac:(unfold acallee_saved; lia)) Q2).
- exact (eq_trans (HPB 3 ltac:(unfold acallee_saved; lia)) Q3).
- exact (eq_trans (HPB 4 ltac:(unfold acallee_saved; lia)) Q4).
- intros q Hq. exact (eq_trans (HPB q ltac:(unfold acallee_saved; lia)) (QH q Hq)).
- exact HSV4.
- exact HTW4.
- split; [reflexivity | exact RB10].
Qed.

(* MO: `jal m_maybe_online`; its return address is the TICK cut. *)
Lemma mrx_seg_mo : K (MRX_PC OFF_TICK) (R_TICK Bw' r) -> K (MRX_PC OFF_MO) (R_MO Bw' r).
Proof using All.
intros KT. unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & Hfr & Hperm & Hmo & Hsp & Hgp2 & Htp2 & Hhi2 & HSV & HTW &
                 HR).
destruct HR as (B3 & Hmon & Hm3 & Hr1). subst c.
calls_st. calls_sizes.
rewrite (mrx_pcv OFF_MO).
pose proof (calls_entry Wc regs2 mem2 (AF_m_rx + OFF_MO)) as HS.
pose proof (calls_img regs2) as HEI.
pose proof (calls_shok regs2 Wc mem2) as SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ calls_awr. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem msA) a = aview sgs (w_H Wc) mem2 a)
  by (calls_kept HFr).
clear HF HFr HG.
pmkst HS.
calls_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 15648)) R1 ltac:(apply codeptr_val; exact HEI).
assert (HP0 : aregs_preserved regs2 (ms_regs msA))
  by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) (calls_E regs2) _ msA regs2 calls_extra HS);
      [apply calls_agree | vm_compute; reflexivity]).
destruct (calls_jal_facts Wc Bwc mem2 msA regs2 15648 ltac:(lia) ltac:(reflexivity) R1 HP0 KA1 Hsp Hgp2 Htp2 Hhi2
  HSV HTW)
  as (R2 & R3' & R4' & R3 & R4 & RH & HRO1 & HRA4 & HSP1 & HM16 & HLO & HHI & HSV1 & HTW1).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx sgs (transportb_sigma TB_m_maybe_online) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HMO fx MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc (ms_mem msA) _ 0 (ms_regs msA) Bwc B3);
  [ exact HJ | exact HRO1 | exact HRA4 | exact R3 | exact R4 | exact HM16
  | unfold MONLINE_STK, MSET_STK, MSET_FRAME; lia | exact HHI | exact HTW1 | exact Hmon
  | unfold MONLINE_EV, MSET_EV; lia ]. }
cbv beta. intros W2 c2 _ HQ.
unfold transport_monline_post, transport_cg_post in HQ.
destruct HQ as (ly3 & S3 & regs3 & mem3 & md3 & e & Hc3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HX3).
assert (He0 : e = 0) by (unfold MONLINE_EV, MSET_EV in He3; lia). subst e.
rewrite Z.add_0_r in HJ3. rewrite R1 in Hc3. subst c2.
destruct HK3 as (HK1 & _).
destruct (mrx_next B MT MTL sp1 regs0 lyc Sc Wc W2 (ms_mem msA) mem3 (ms_regs msA) regs3 S2 S3 ly2 ly3 MONLINE_STK
  ltac:(unfold MONLINE_STK, MSET_STK, MSET_FRAME; lia) ltac:(unfold MONLINE_STK, MSET_STK, MSET_FRAME; lia)
  HSP1 HSV1 (calls_slots_kept Wc W2 (ms_mem msA) mem3 (ms_regs msA) MONLINE_STK HSP1 HK1)
  HP3 R2 R3' R4' RH Hfr Hfr3 Hperm Hperm3 Hmo Hmo3)
  as (HSV3 & Q2 & Q3 & Q4 & QH & F3 & P3' & M3).
rewrite calls_pc_tick.
apply (KT W2 B3).
apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_TICK) (R_TICK Bw' r) W2 B3 ly3 S3 regs3 mem3 md3
  HJ3 F3 P3' M3 Q2 Q3 Q4 QH HSV3 HX3).
split; [exact Hm3 | exact Hr1].
Qed.

(* WAKE: `jal m_wake`, then the jump to the TICK cut. *)
Lemma mrx_seg_wake : K (MRX_PC OFF_TICK) (R_TICK Bw' r) -> K (MRX_PC OFF_WAKE) (R_WAKE Bw' r).
Proof using All.
intros KT. unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & Hfr & Hperm & Hmo & Hsp & Hgp2 & Htp2 & Hhi2 & HSV & HTW &
                 HR).
destruct HR as (B3 & rw & Hmw & Hm3 & Hr1). subst c.
calls_st. calls_sizes.
rewrite (mrx_pcv OFF_WAKE).
pose proof (calls_entry Wc regs2 mem2 (AF_m_rx + OFF_WAKE)) as HS.
pose proof (calls_img regs2) as HEI.
pose proof (calls_shok regs2 Wc mem2) as SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ calls_awr. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem msA) a = aview sgs (w_H Wc) mem2 a)
  by (calls_kept HFr).
clear HF HFr HG.
pmkst HS.
calls_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 15624)) R1 ltac:(apply codeptr_val; exact HEI).
assert (HP0 : aregs_preserved regs2 (ms_regs msA))
  by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) (calls_E regs2) _ msA regs2 calls_extra HS);
      [apply calls_agree | vm_compute; reflexivity]).
destruct (calls_jal_facts Wc Bwc mem2 msA regs2 15624 ltac:(lia) ltac:(reflexivity) R1 HP0 KA1 Hsp Hgp2 Htp2 Hhi2
  HSV HTW)
  as (R2 & R3' & R4' & R3 & R4 & RH & HRO1 & HRA4 & HSP1 & HM16 & HLO & HHI & HSV1 & HTW1).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx sgs (transportb_sigma TB_m_wake) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HMW fx MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc (ms_mem msA) _ 0 (ms_regs msA) Bwc B3 rw);
  [ exact HJ | exact HRO1 | exact HRA4 | exact R3 | exact R4 | exact HM16
  | unfold MWAKE_STK, MWAKE_FRAME, MSET_STK, MSET_FRAME; lia | exact HHI | exact HTW1 | exact Hmw
  | unfold MWAKE_EV, MSET_EV; lia ]. }
cbv beta. intros W2 c2 _ HQ.
unfold transport_mwake_post, transport_cg_post in HQ.
destruct HQ as (ly3 & S3 & regs3 & mem3 & md3 & e & Hc3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HX3).
destruct HX3 as [_ HX3].
assert (He0 : e = 0) by (unfold MWAKE_EV, MSET_EV in He3; lia). subst e.
rewrite Z.add_0_r in HJ3. rewrite R1 in Hc3. subst c2.
destruct HK3 as (HK1 & _).
destruct (mrx_next B MT MTL sp1 regs0 lyc Sc Wc W2 (ms_mem msA) mem3 (ms_regs msA) regs3 S2 S3 ly2 ly3 MWAKE_STK
  ltac:(unfold MWAKE_STK, MWAKE_FRAME, MSET_STK, MSET_FRAME; lia)
  ltac:(unfold MWAKE_STK, MWAKE_FRAME, MSET_STK, MSET_FRAME; lia)
  HSP1 HSV1 (calls_slots_kept Wc W2 (ms_mem msA) mem3 (ms_regs msA) MWAKE_STK HSP1 HK1)
  HP3 R2 R3' R4' RH Hfr Hfr3 Hperm Hperm3 Hmo Hmo3)
  as (HSV3 & Q2 & Q3 & Q4 & QH & F3 & P3' & M3).
(* the jump to the call of m_tick *)
pose proof (calls_entry W2 regs3 mem3 15624) as HS3.
pose proof (calls_img regs3) as HEI3.
pose proof (calls_shok regs3 W2 mem3) as SHOK3.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 YC4b.Bspan 15648.
{ calls_awr. }
lazymatch type of HS3 with context [restrict _ ?m] => rename m into msB end.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H W2) (ms_mem msB) a = aview sgs (w_H W2) mem3 a)
  by (calls_kept HFr).
assert (HPB : aregs_preserved regs3 (ms_regs msB))
  by (apply (aregs_preserved_of_st_ok sgs (w_H W2) (calls_E regs3) _ msB regs3 calls_extra HS3);
      [apply calls_agree | vm_compute; reflexivity]).
destruct (calls_after_run W2 B3 mem3 (ms_mem msB) KA2 HSV3 HX3) as (HSV4 & HTW4).
pmkst HS3. rewrite calls_pc_tick.
apply (KT W2 B3).
apply (mrx_at_intro B MT sp1 regs0 lyc Sc W memc mdc (MRX_PC OFF_TICK) (R_TICK Bw' r) W2 B3 ly3 S3 (ms_regs msB)
  (ms_mem msB)).
- exact HJ3.
- exact F3.
- exact P3'.
- exact M3.
- exact (eq_trans (HPB 2 ltac:(unfold acallee_saved; lia)) Q2).
- exact (eq_trans (HPB 3 ltac:(unfold acallee_saved; lia)) Q3).
- exact (eq_trans (HPB 4 ltac:(unfold acallee_saved; lia)) Q4).
- intros q Hq. exact (eq_trans (HPB q ltac:(unfold acallee_saved; lia)) (QH q Hq)).
- exact HSV4.
- exact HTW4.
- split; [exact Hm3 | exact Hr1].
Qed.

End seg.
