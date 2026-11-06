(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 902 of its 1078 lines of code are new or changed and 963 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SlostHead.v, with its module names and numbers changed; 1131 of its 1216 lines of code are new or changed and 993 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_annt.v; 727 of its 836 lines of code are new or changed and 1107 lines of the source are left out. *)
(* m_rx_seg_calls: the call segments of the image-A walk of m_rx (the cuts of lib/A/Prog/m_rx_seg_kit.v, chained in
   m_rx_cgW.v): the epilogue to the return (mrx_seg_epi), and the five `jal`s of a G-form callee, each from its cut
   to the cut its return address lies at (mrx_seg_tick, mrx_seg_mo, mrx_seg_wake, mrx_seg_lost, mrx_seg_e0l).

   Every segment runs the symbolic runs of lib/A/Prog/PaShadow.v over the walk's inner G journal (TransportGRunA.v
   paj_run_x / paj_run_to_x), from a state with no region (the `jal`s and the jumps after them read no memory) or,
   for the epilogue, with ONE read-only region: the 13 saved slots of the frame, whose chunks hold the entry
   registers (the cut's mrx_saved, read through YCbq.v val_mem_of_rdword).
     EPI  +0x0e0 .. +0x118  the 13 loads, `sp = sp + 144`, `ret`: the registers are the entry's, nothing changed.
     TICK +0x590            `jal m_tick`, the return at +0x594, `a0 = 1`, `j` to the epilogue (+0x0e0).
     MO   +0x58c            `jal m_maybe_online`, the return at +0x590 = the TICK cut.
     WAKE +0x574            `jal m_wake`, the return at +0x578, `j` to +0x590 = the TICK cut.
     LOST +0x3f4            `jal m_lost` (a0 = why), the return at +0x3f8, `j` to +0x590 = the TICK cut.
     E0L  +0x55c            `jal m_lost` (a0 = 3), the return at +0x560 = the E0W cut.
   A callee is entered on the walk's own journal with ra = the return address, sp = sp1 - 144 and the entry gp / tp;
   its post gives the next cut: the journal, the frames, the blocks and the meter compose, the saved slots are kept
   (they lie above the callee's stack window), and the callee-saved registers carry sp, gp, tp and s3. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
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

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac
   (m_tick.v mt_reg). *)
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

(* The write rights of a run whose regions have no writable byte (m_tick.v mt_awr). *)
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

Local Abbreviation sgs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma calls_base : BASE + AF_m_rx = transport_sigma TS_m_rx.
Proof. vm_compute. reflexivity. Qed.

Lemma calls_pcv : forall off, MRX_PC off = BASE + (AF_m_rx + off).
Proof. intros off. unfold MRX_PC. rewrite <- calls_base. ring. Qed.

(* ---- the walk's valuation: the registers at the cut, the shadow base, the 13 entry registers ---- *)

Definition calls_extra : list word :=
  [Z_to_bv 64 SHADOW_OFF;
   YK11.getr regs0 (Z_to_bv 5 1); YK11.getr regs0 (Z_to_bv 5 8); YK11.getr regs0 (Z_to_bv 5 9);
   YK11.getr regs0 (Z_to_bv 5 18); YK11.getr regs0 (Z_to_bv 5 19); YK11.getr regs0 (Z_to_bv 5 20);
   YK11.getr regs0 (Z_to_bv 5 21); YK11.getr regs0 (Z_to_bv 5 22); YK11.getr regs0 (Z_to_bv 5 23);
   YK11.getr regs0 (Z_to_bv 5 24); YK11.getr regs0 (Z_to_bv 5 25); YK11.getr regs0 (Z_to_bv 5 26);
   YK11.getr regs0 (Z_to_bv 5 27)].
Definition calls_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs calls_extra).
Definition calls_Bx : sv := SOff 32 0.
Definition calls_SH : list shent := [].
Definition calls_F : facts := mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition calls_FE : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].

(* The 13 saved slots of the frame, read-only, each chunk the entry register MRX_SAVES names. *)
Definition calls_epi_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 40 144 0 0
   [YP09.mkChunk 136 (YP09.CVal 8 (SOff 33 0)); YP09.mkChunk 128 (YP09.CVal 8 (SOff 34 0));
    YP09.mkChunk 120 (YP09.CVal 8 (SOff 35 0)); YP09.mkChunk 112 (YP09.CVal 8 (SOff 36 0));
    YP09.mkChunk 104 (YP09.CVal 8 (SOff 37 0)); YP09.mkChunk 96 (YP09.CVal 8 (SOff 38 0));
    YP09.mkChunk 88 (YP09.CVal 8 (SOff 39 0)); YP09.mkChunk 80 (YP09.CVal 8 (SOff 40 0));
    YP09.mkChunk 72 (YP09.CVal 8 (SOff 41 0)); YP09.mkChunk 64 (YP09.CVal 8 (SOff 42 0));
    YP09.mkChunk 56 (YP09.CVal 8 (SOff 43 0)); YP09.mkChunk 48 (YP09.CVal 8 (SOff 44 0));
    YP09.mkChunk 40 (YP09.CVal 8 (SOff 45 0))].
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
  destruct HH as (Hsp1 & Hsp16 & Hceil & H46 & H47 & Hrao & Hra4 & Hgp0 & Htp0 & Ha00 & Ha10 & Hfa0 & Hfan &
                  Hsrc & Hdisj & Hapart & Hnev & HAR).

(* ---- the entry states ---- *)

Lemma calls_entry : forall (W2 : world sgs) (regs : bvmap 5 word) mem k,
  st_ok_pi sgs VAL (calls_E regs) (ss_calls k)
    (restrict (w_H W2) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom sgs))).
Proof.
intros W2 regs mem k. rewrite restrict_mkst_fx. unfold ss_calls.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
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
intros W2 regs mem Hsp HSV. calls_st.
assert (FS : MRX_STK = 8352) by reflexivity. unfold MRX_FRAME in *.
assert (E2 : ew (calls_E regs) 2%nat = Z_to_bv 64 (sp1 - 144))
  by (rewrite (calls_ewr regs (Z_to_bv 5 2) 2%nat ltac:(vm_compute; reflexivity)); exact Hsp).
assert (U2 : bv_unsigned (ew (calls_E regs) 2%nat) = sp1 - 144)
  by (rewrite E2; apply unsigned_lit_small; lia).
assert (Hbase : base_val (calls_E regs) (Some 2%nat) = sp1 - 144) by (cbn [base_val]; exact U2).
assert (EX : forall j, (j < 14)%nat -> ew (calls_E regs) (32 + j) = nth j calls_extra (Z_to_bv 64 0))
  by (intros j Hj; unfold calls_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 1%nat ltac:(lia)) as A33. pose proof (EX 2%nat ltac:(lia)) as A34.
pose proof (EX 3%nat ltac:(lia)) as A35. pose proof (EX 4%nat ltac:(lia)) as A36.
pose proof (EX 5%nat ltac:(lia)) as A37. pose proof (EX 6%nat ltac:(lia)) as A38.
pose proof (EX 7%nat ltac:(lia)) as A39. pose proof (EX 8%nat ltac:(lia)) as A40.
pose proof (EX 9%nat ltac:(lia)) as A41. pose proof (EX 10%nat ltac:(lia)) as A42.
pose proof (EX 11%nat ltac:(lia)) as A43. pose proof (EX 12%nat ltac:(lia)) as A44.
pose proof (EX 13%nat ltac:(lia)) as A45.
cbn [Nat.add nth calls_extra] in A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45.
assert (SV : forall p, In p MRX_SAVES ->
  rdword (aview sgs (w_H W2) mem) (sp1 - 144 + snd p) =
    Some (bv_unsigned (YK11.getr regs0 (Z_to_bv 5 (fst p)))))
  by (apply Forall_forall; exact HSV).
rewrite restrict_mkst_fx. unfold ss_epi.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold calls_epi_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Hbase. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat (apply Forall_cons; [first
    [ exact (calls_chunk W2 mem _ 1 136 33%nat (SV (1, 136) ltac:(cbn [MRX_SAVES In]; tauto)) A33 Hbase)
    | exact (calls_chunk W2 mem _ 8 128 34%nat (SV (8, 128) ltac:(cbn [MRX_SAVES In]; tauto)) A34 Hbase)
    | exact (calls_chunk W2 mem _ 9 120 35%nat (SV (9, 120) ltac:(cbn [MRX_SAVES In]; tauto)) A35 Hbase)
    | exact (calls_chunk W2 mem _ 18 112 36%nat (SV (18, 112) ltac:(cbn [MRX_SAVES In]; tauto)) A36 Hbase)
    | exact (calls_chunk W2 mem _ 19 104 37%nat (SV (19, 104) ltac:(cbn [MRX_SAVES In]; tauto)) A37 Hbase)
    | exact (calls_chunk W2 mem _ 20 96 38%nat (SV (20, 96) ltac:(cbn [MRX_SAVES In]; tauto)) A38 Hbase)
    | exact (calls_chunk W2 mem _ 21 88 39%nat (SV (21, 88) ltac:(cbn [MRX_SAVES In]; tauto)) A39 Hbase)
    | exact (calls_chunk W2 mem _ 22 80 40%nat (SV (22, 80) ltac:(cbn [MRX_SAVES In]; tauto)) A40 Hbase)
    | exact (calls_chunk W2 mem _ 23 72 41%nat (SV (23, 72) ltac:(cbn [MRX_SAVES In]; tauto)) A41 Hbase)
    | exact (calls_chunk W2 mem _ 24 64 42%nat (SV (24, 64) ltac:(cbn [MRX_SAVES In]; tauto)) A42 Hbase)
    | exact (calls_chunk W2 mem _ 25 56 43%nat (SV (25, 56) ltac:(cbn [MRX_SAVES In]; tauto)) A43 Hbase)
    | exact (calls_chunk W2 mem _ 26 48 44%nat (SV (26, 48) ltac:(cbn [MRX_SAVES In]; tauto)) A44 Hbase)
    | exact (calls_chunk W2 mem _ 27 40 45%nat (SV (27, 40) ltac:(cbn [MRX_SAVES In]; tauto)) A45 Hbase)] |]);
  apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- unfold calls_FE, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite calls_ew32. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  rewrite U2. rewrite Z.pow_0_r, Z.mod_1_r. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
  replace (sp1 - 144) with (sp1 + (-9) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
Qed.

(* ---- EPI: the epilogue and the return ---- *)

Lemma mrx_seg_epi : K (MRX_PC OFF_EPI) (R_EPI Bw' r).
Proof using All.
unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & Hfr & Hperm & Hmo & Hsp & Hgp2 & Htp2 & HSV & HTW & HR).
destruct HR as [HBw Ha0]. subst Bwc. subst c.
calls_st.
assert (FS : MRX_STK = 8352) by reflexivity. unfold MRX_FRAME in *.
rewrite (calls_pcv OFF_EPI).
pose proof (calls_entry_epi Wc regs2 mem2 Hsp HSV) as HS.
pose proof (calls_img regs2) as HEI.
pose proof (calls_shok regs2 Wc mem2) as SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
(* the 13 loads, `sp = sp + 144`, stop at `ret` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ calls_awr. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem ms) a = aview sgs (w_H Wc) mem2 a)
  by (calls_kept HFr).
assert (E2 : ew (calls_E regs2) 2%nat = Z_to_bv 64 (sp1 - 144))
  by (rewrite (calls_ewr regs2 (Z_to_bv 5 2) 2%nat ltac:(vm_compute; reflexivity)); exact Hsp).
assert (U2 : bv_unsigned (ew (calls_E regs2) 2%nat) = sp1 - 144)
  by (rewrite E2; apply unsigned_lit_small; lia).
assert (EX : forall j, (j < 14)%nat -> ew (calls_E regs2) (32 + j) = nth j calls_extra (Z_to_bv 64 0))
  by (intros j Hj; unfold calls_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 1%nat ltac:(lia)) as A33. pose proof (EX 2%nat ltac:(lia)) as A34.
pose proof (EX 3%nat ltac:(lia)) as A35. pose proof (EX 4%nat ltac:(lia)) as A36.
pose proof (EX 5%nat ltac:(lia)) as A37. pose proof (EX 6%nat ltac:(lia)) as A38.
pose proof (EX 7%nat ltac:(lia)) as A39. pose proof (EX 8%nat ltac:(lia)) as A40.
pose proof (EX 9%nat ltac:(lia)) as A41. pose proof (EX 10%nat ltac:(lia)) as A42.
pose proof (EX 11%nat ltac:(lia)) as A43. pose proof (EX 12%nat ltac:(lia)) as A44.
pose proof (EX 13%nat ltac:(lia)) as A45.
cbn [Nat.add nth calls_extra] in A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45.
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
  assert (HQ : q = 2 \/ q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/
               q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
  clear Hq.
  repeat (destruct HQ as [HQ | HQ]); subst q.
  - calls_reg HS (Z_to_bv 5 2) (YK11.getr regs0 (Z_to_bv 5 2)) P2
      ltac:(cbn [sv_denot]; rewrite U2; replace (sp1 - 144 + 144) with sp1 by lia;
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
    exact P18.
  - calls_reg HS (Z_to_bv 5 19) (YK11.getr regs0 (Z_to_bv 5 19)) P19
      ltac:(cbn [sv_denot]; rewrite A37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    exact P19.
  - calls_reg HS (Z_to_bv 5 20) (YK11.getr regs0 (Z_to_bv 5 20)) P20
      ltac:(cbn [sv_denot]; rewrite A38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    exact P20.
  - calls_reg HS (Z_to_bv 5 21) (YK11.getr regs0 (Z_to_bv 5 21)) P21
      ltac:(cbn [sv_denot]; rewrite A39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    exact P21.
  - calls_reg HS (Z_to_bv 5 22) (YK11.getr regs0 (Z_to_bv 5 22)) P22
      ltac:(cbn [sv_denot]; rewrite A40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    exact P22.
  - calls_reg HS (Z_to_bv 5 23) (YK11.getr regs0 (Z_to_bv 5 23)) P23
      ltac:(cbn [sv_denot]; rewrite A41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    exact P23.
  - calls_reg HS (Z_to_bv 5 24) (YK11.getr regs0 (Z_to_bv 5 24)) P24
      ltac:(cbn [sv_denot]; rewrite A42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    exact P24.
  - calls_reg HS (Z_to_bv 5 25) (YK11.getr regs0 (Z_to_bv 5 25)) P25
      ltac:(cbn [sv_denot]; rewrite A43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    exact P25.
  - calls_reg HS (Z_to_bv 5 26) (YK11.getr regs0 (Z_to_bv 5 26)) P26
      ltac:(cbn [sv_denot]; rewrite A44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    exact P26.
  - calls_reg HS (Z_to_bv 5 27) (YK11.getr regs0 (Z_to_bv 5 27)) P27
      ltac:(cbn [sv_denot]; rewrite A45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    exact P27. }
eapply (RET Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
unfold mrx_ipost.
exists ly2, S2, (ms_regs ms), (ms_mem ms).
eexists.
split; [rewrite RF1; unfold YK0s.ret_ok in Hrao; rewrite Hrao; reflexivity|].
split; [apply (ajournal_gx_materialize sgs B LAWS transport_segs_low); exact HJ|].
split; [exact HPF|].
split; [exact Hfr|].
split; [exact Hperm|].
split; [exact Hmo|].
split; [exact RF10|].
apply (tw_kept TMAP_A (aview sgs (w_H Wc) mem2) _ Bw' HTW).
intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA. lia.
Qed.

(* ---- the `jal`s of a G-form callee ---- *)

Lemma calls_bval : BASE = 0x8488c - AF_m_rx.
Proof. rewrite <- mrx_pc_val, <- calls_base. ring. Qed.

Lemma calls_pc_epi : BASE + 14088 = MRX_PC OFF_EPI.
Proof. rewrite (calls_pcv OFF_EPI). f_equal; vm_compute; reflexivity. Qed.
Lemma calls_pc_tick : BASE + 15288 = MRX_PC OFF_TICK.
Proof. rewrite (calls_pcv OFF_TICK). f_equal; vm_compute; reflexivity. Qed.
Lemma calls_pc_e0w : BASE + 15240 = MRX_PC OFF_E0W.
Proof. rewrite (calls_pcv OFF_E0W). f_equal; vm_compute; reflexivity. Qed.

(* The premises every callee's contract takes of the machine at the `jal`'s target. *)
Lemma calls_pre : forall (regsT : bvmap 5 word) (k : Z),
  0 <= k < 2 ^ 40 -> k mod 2 = 0 ->
  YK11.getr regsT 1 = Z_to_bv 64 (BASE + k) ->
  YK11.getr regsT 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK0s.ret_ok (YK11.getr regsT 1) /\ 4096 <= raZ regsT /\ spZ regsT = sp1 - MRX_FRAME /\
  spZ regsT mod 16 = 0 /\ sp1 - MRX_STK <= spZ regsT - 16 /\ spZ regsT <= sp1.
Proof.
intros regsT k Hk Hk2 R1 R2. calls_st.
assert (FS : MRX_STK = 8352) by reflexivity. unfold MRX_FRAME in *.
assert (HB : BASE = 0x8488c - 0x3628) by (rewrite calls_bval; unfold AF_m_rx; reflexivity).
assert (HS2 : spZ regsT = sp1 - 144).
{ change (spZ regsT) with (bv_unsigned (YK11.getr regsT 2)).
  rewrite R2. apply unsigned_lit_small. lia. }
split; [rewrite R1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | exact Hk2]|].
split.
{ change (raZ regsT) with (bv_unsigned (YK11.getr regsT 1)).
  rewrite R1, unsigned_lit_small by lia. lia. }
split; [exact HS2|].
split; [rewrite HS2; replace (sp1 - 144) with (sp1 + (-9) * 16) by lia;
        rewrite Z_mod_plus_full; exact Hsp16|].
split; [rewrite HS2; lia | rewrite HS2; lia].
Qed.

(* What the next cut takes of the state after a callee's return: the saved slots (they lie above the callee's
   stack window), sp / gp / tp (callee-saved), and the frames, blocks and meter composed with the cut's. *)
Lemma calls_next : forall (Wc W2 : world sgs) memA mem3 (regsT regs3 : bvmap 5 word) S2 S3 ly2 ly3 (FSTK : Z),
  0 <= FSTK -> FSTK <= MRX_STK - MRX_FRAME ->
  spZ regsT = sp1 - MRX_FRAME ->
  mrx_saved Wc memA sp1 regs0 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regsT - FSTK <= a < spZ regsT) ->
     aview sgs (w_H W2) mem3 a = aview sgs (w_H Wc) memA a) ->
  aregs_preserved regsT regs3 ->
  YK11.getr regsT 2 = Z_to_bv 64 (sp1 - MRX_FRAME) ->
  YK11.getr regsT 3 = YK11.getr regs0 3 -> YK11.getr regsT 4 = YK11.getr regs0 4 ->
  frames S2 = frames Sc -> frames S3 = frames S2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  mo_le MT Sc S2 0 -> mo_le MT S2 S3 0 ->
  mrx_saved W2 mem3 sp1 regs0 /\
  YK11.getr regs3 2 = Z_to_bv 64 (sp1 - MRX_FRAME) /\
  YK11.getr regs3 3 = YK11.getr regs0 3 /\ YK11.getr regs3 4 = YK11.getr regs0 4 /\
  frames S3 = frames Sc /\ Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) /\ mo_le MT Sc S3 0.
Proof.
intros Wc W2 memA mem3 regsT regs3 S2 S3 ly2 ly3 FSTK HF0 HF1 HSP HSV K1 HP R2 R3 R4 F2 F3 P2 P3 M2 M3.
calls_st. assert (FS : MRX_STK = 8352) by reflexivity. unfold MRX_FRAME in *.
split.
{ apply (mrx_saved_kept Wc W2 memA mem3 sp1 regs0 HSV).
  intros a Ha. apply K1; [lia | rewrite HSP; lia]. }
split; [rewrite <- R2; exact (HP 2 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R3; exact (HP 3 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R4; exact (HP 4 ltac:(unfold acallee_saved; lia))|].
split; [exact (eq_trans F3 F2)|].
split; [exact (Permutation_trans P3 P2)|].
exact (mle_station MT Sc S2 S3 0 0 MTL M2 M3).
Qed.

(* The run of a `jal` from a cut: the state at the callee's entry, with the registers the contract takes. *)
Ltac calls_jal RUN HS HJ SHOK :=
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan; [ calls_awr | ].

Lemma mrx_seg_tick : K (MRX_PC OFF_EPI) (R_EPI Bw' r) -> K (MRX_PC OFF_TICK) (R_TICK Bw' r).
Proof using All.
intros KE. unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & Hfr & Hperm & Hmo & Hsp & Hgp2 & Htp2 & HSV & HTW & HR).
destruct HR as [Hm Hr1]. subst c.
calls_st. assert (FS : MRX_STK = 8352) by reflexivity. unfold MRX_FRAME in *.
rewrite (calls_pcv OFF_TICK).
pose proof (calls_entry Wc regs2 mem2 (AF_m_rx + OFF_TICK)) as HS.
pose proof (calls_img regs2) as HEI.
pose proof (calls_shok regs2 Wc mem2) as SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
(* the `jal m_tick` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ calls_awr. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem msA) a = aview sgs (w_H Wc) mem2 a)
  by (calls_kept HFr).
clear HF HFr HG.
pmkst HS.
calls_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 15292)) R1 ltac:(apply codeptr_val; exact HEI).
assert (HP0 : aregs_preserved regs2 (ms_regs msA))
  by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) (calls_E regs2) _ msA regs2 calls_extra HS);
      [apply calls_agree | vm_compute; reflexivity]).
assert (R2 : YK11.getr (ms_regs msA) 2 = Z_to_bv 64 (sp1 - 144))
  by (rewrite <- Hsp; exact (HP0 2 ltac:(unfold acallee_saved; lia))).
assert (R3' : YK11.getr (ms_regs msA) 3 = YK11.getr regs0 3)
  by (rewrite <- Hgp2; exact (HP0 3 ltac:(unfold acallee_saved; lia))).
assert (R4' : YK11.getr (ms_regs msA) 4 = YK11.getr regs0 4)
  by (rewrite <- Htp2; exact (HP0 4 ltac:(unfold acallee_saved; lia))).
assert (R3 : YK11.getr (ms_regs msA) 3 = w64 (as_gp B)) by (rewrite R3'; exact Hgp0).
assert (R4 : YK11.getr (ms_regs msA) 4 = w64 (as_tp B)) by (rewrite R4'; exact Htp0).
destruct (calls_pre (ms_regs msA) 15292 ltac:(lia) ltac:(reflexivity) R1 R2)
  as (HRO1 & HRA4 & HSP1 & HM16 & HLO & HHI).
assert (HSV1 : mrx_saved Wc (ms_mem msA) sp1 regs0)
  by (apply (mrx_saved_kept Wc Wc mem2 (ms_mem msA) sp1 regs0 HSV); intros a Ha; apply KA1; lia).
assert (HTW1 : tw_at TMAP_A (aview sgs (w_H Wc) (ms_mem msA)) Bwc).
{ apply (tw_kept TMAP_A (aview sgs (w_H Wc) mem2) _ Bwc HTW).
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA1. lia. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx sgs (transport_sigma TS_m_tick) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HMT fx MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc (ms_mem msA) _ 0 (ms_regs msA) Bwc Bw');
  [ exact HJ | exact HRO1 | exact HRA4 | exact R3 | exact R4 | exact HM16
  | unfold MTICK_STK, MLOST_STK, MLOST_FRAME; lia | exact HHI | exact HTW1 | exact Hm
  | unfold MTICK_EV, MLOST_EV; lia ]. }
cbv beta. intros W2 c2 _ HQ.
unfold transport_mtick_post, transport_cg_post in HQ.
destruct HQ as (ly3 & S3 & regs3 & mem3 & md3 & e & Hc3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HX3).
assert (He0 : e = 0) by (unfold MTICK_EV, MLOST_EV in He3; lia). subst e.
rewrite Z.add_0_r in HJ3. rewrite R1 in Hc3. subst c2.
destruct HK3 as (HK1 & _).
destruct (calls_next Wc W2 (ms_mem msA) mem3 (ms_regs msA) regs3 S2 S3 ly2 ly3 MTICK_STK
  ltac:(unfold MTICK_STK, MLOST_STK, MLOST_FRAME; lia)
  ltac:(unfold MTICK_STK, MLOST_STK, MLOST_FRAME; lia)
  HSP1 HSV1 HK1 HP3 R2 R3' R4' Hfr Hfr3 Hperm Hperm3 Hmo Hmo3)
  as (HSV3 & Q2 & Q3 & Q4 & F3 & P3' & M3).
(* `a0 = 1` and the jump to the epilogue *)
pose proof (calls_entry W2 regs3 mem3 15292) as HS3.
pose proof (calls_img regs3) as HEI3.
pose proof (calls_shok regs3 W2 mem3) as SHOK3.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 YC4b.Bspan 14088.
{ calls_awr. }
lazymatch type of HS3 with context [restrict _ ?m] => rename m into msB end.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H W2) (ms_mem msB) a = aview sgs (w_H W2) mem3 a)
  by (calls_kept HFr).
assert (EE3 : forall m (q : bv 5), Z.of_nat m = bv_unsigned q -> ew (calls_E regs3) m = YK11.getr regs3 q)
  by (intros m q Hm'; apply calls_ewr; exact Hm').
calls_reg HS3 (Z_to_bv 5 10) (w64 r) RB10 ltac:(rewrite Hr1; reflexivity).
calls_reg HS3 (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - 144)) RB2
  ltac:(cbn [sv_denot]; rewrite (EE3 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q2).
calls_reg HS3 (Z_to_bv 5 3) (YK11.getr regs0 3) RB3
  ltac:(cbn [sv_denot]; rewrite (EE3 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q3).
calls_reg HS3 (Z_to_bv 5 4) (YK11.getr regs0 4) RB4
  ltac:(cbn [sv_denot]; rewrite (EE3 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q4).
pmkst HS3. rewrite calls_pc_epi.
apply (KE W2 Bw').
unfold mrx_at. exists ly3, S3, (ms_regs msB), (ms_mem msB). eexists.
split; [reflexivity|].
split; [exact HJ3|].
split; [exact F3|].
split; [exact P3'|].
split; [exact M3|].
split; [exact RB2|].
split; [exact RB3|].
split; [exact RB4|].
split.
{ apply (mrx_saved_kept W2 W2 mem3 (ms_mem msB) sp1 regs0 HSV3). intros a Ha. apply KA2. lia. }
split.
{ apply (tw_kept TMAP_A (aview sgs (w_H W2) mem3) _ Bw' HX3).
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA2. lia. }
split; [reflexivity | exact RB10].
Qed.

(* MO: `jal m_maybe_online`; its return address is the TICK cut. *)
Lemma mrx_seg_mo : K (MRX_PC OFF_TICK) (R_TICK Bw' r) -> K (MRX_PC OFF_MO) (R_MO Bw' r).
Proof using All.
intros KT. unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & Hfr & Hperm & Hmo & Hsp & Hgp2 & Htp2 & HSV & HTW & HR).
destruct HR as (B3 & Hmon & Hm3 & Hr1). subst c.
calls_st. assert (FS : MRX_STK = 8352) by reflexivity. unfold MRX_FRAME in *.
rewrite (calls_pcv OFF_MO).
pose proof (calls_entry Wc regs2 mem2 (AF_m_rx + OFF_MO)) as HS.
pose proof (calls_img regs2) as HEI.
pose proof (calls_shok regs2 Wc mem2) as SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ calls_awr. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem msA) a = aview sgs (w_H Wc) mem2 a)
  by (calls_kept HFr).
clear HF HFr HG.
pmkst HS.
calls_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 15288)) R1 ltac:(apply codeptr_val; exact HEI).
assert (HP0 : aregs_preserved regs2 (ms_regs msA))
  by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) (calls_E regs2) _ msA regs2 calls_extra HS);
      [apply calls_agree | vm_compute; reflexivity]).
assert (R2 : YK11.getr (ms_regs msA) 2 = Z_to_bv 64 (sp1 - 144))
  by (rewrite <- Hsp; exact (HP0 2 ltac:(unfold acallee_saved; lia))).
assert (R3' : YK11.getr (ms_regs msA) 3 = YK11.getr regs0 3)
  by (rewrite <- Hgp2; exact (HP0 3 ltac:(unfold acallee_saved; lia))).
assert (R4' : YK11.getr (ms_regs msA) 4 = YK11.getr regs0 4)
  by (rewrite <- Htp2; exact (HP0 4 ltac:(unfold acallee_saved; lia))).
assert (R3 : YK11.getr (ms_regs msA) 3 = w64 (as_gp B)) by (rewrite R3'; exact Hgp0).
assert (R4 : YK11.getr (ms_regs msA) 4 = w64 (as_tp B)) by (rewrite R4'; exact Htp0).
destruct (calls_pre (ms_regs msA) 15288 ltac:(lia) ltac:(reflexivity) R1 R2)
  as (HRO1 & HRA4 & HSP1 & HM16 & HLO & HHI).
assert (HSV1 : mrx_saved Wc (ms_mem msA) sp1 regs0)
  by (apply (mrx_saved_kept Wc Wc mem2 (ms_mem msA) sp1 regs0 HSV); intros a Ha; apply KA1; lia).
assert (HTW1 : tw_at TMAP_A (aview sgs (w_H Wc) (ms_mem msA)) Bwc).
{ apply (tw_kept TMAP_A (aview sgs (w_H Wc) mem2) _ Bwc HTW).
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA1. lia. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx sgs (transport_sigma TS_m_maybe_online) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HMO fx MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc (ms_mem msA) _ 0 (ms_regs msA) Bwc B3);
  [ exact HJ | exact HRO1 | exact HRA4 | exact R3 | exact R4 | exact HM16
  | unfold MONLINE_STK, MONLINE_FRAME; lia | exact HHI | exact HTW1 | exact Hmon
  | unfold MONLINE_EV; lia ]. }
cbv beta. intros W2 c2 _ HQ.
unfold transport_monline_post, transport_cg_post in HQ.
destruct HQ as (ly3 & S3 & regs3 & mem3 & md3 & e & Hc3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HX3).
assert (He0 : e = 0) by (unfold MONLINE_EV in He3; lia). subst e.
rewrite Z.add_0_r in HJ3. rewrite R1 in Hc3. subst c2.
destruct HK3 as (HK1 & _).
destruct (calls_next Wc W2 (ms_mem msA) mem3 (ms_regs msA) regs3 S2 S3 ly2 ly3 MONLINE_STK
  ltac:(unfold MONLINE_STK, MONLINE_FRAME; lia) ltac:(unfold MONLINE_STK, MONLINE_FRAME; lia)
  HSP1 HSV1 HK1 HP3 R2 R3' R4' Hfr Hfr3 Hperm Hperm3 Hmo Hmo3)
  as (HSV3 & Q2 & Q3 & Q4 & F3 & P3' & M3).
rewrite calls_pc_tick.
apply (KT W2 B3).
unfold mrx_at. exists ly3, S3, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact F3|]. split; [exact P3'|]. split; [exact M3|].
split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact HSV3|]. split; [exact HX3|].
split; [exact Hm3 | exact Hr1].
Qed.

(* WAKE: `jal m_wake`, then the jump to the TICK cut. *)
Lemma mrx_seg_wake : K (MRX_PC OFF_TICK) (R_TICK Bw' r) -> K (MRX_PC OFF_WAKE) (R_WAKE Bw' r).
Proof using All.
intros KT. unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & Hfr & Hperm & Hmo & Hsp & Hgp2 & Htp2 & HSV & HTW & HR).
destruct HR as (B3 & rw & Hmw & Hm3 & Hr1). subst c.
calls_st. assert (FS : MRX_STK = 8352) by reflexivity. unfold MRX_FRAME in *.
rewrite (calls_pcv OFF_WAKE).
pose proof (calls_entry Wc regs2 mem2 (AF_m_rx + OFF_WAKE)) as HS.
pose proof (calls_img regs2) as HEI.
pose proof (calls_shok regs2 Wc mem2) as SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ calls_awr. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem msA) a = aview sgs (w_H Wc) mem2 a)
  by (calls_kept HFr).
clear HF HFr HG.
pmkst HS.
calls_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 15264)) R1 ltac:(apply codeptr_val; exact HEI).
assert (HP0 : aregs_preserved regs2 (ms_regs msA))
  by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) (calls_E regs2) _ msA regs2 calls_extra HS);
      [apply calls_agree | vm_compute; reflexivity]).
assert (R2 : YK11.getr (ms_regs msA) 2 = Z_to_bv 64 (sp1 - 144))
  by (rewrite <- Hsp; exact (HP0 2 ltac:(unfold acallee_saved; lia))).
assert (R3' : YK11.getr (ms_regs msA) 3 = YK11.getr regs0 3)
  by (rewrite <- Hgp2; exact (HP0 3 ltac:(unfold acallee_saved; lia))).
assert (R4' : YK11.getr (ms_regs msA) 4 = YK11.getr regs0 4)
  by (rewrite <- Htp2; exact (HP0 4 ltac:(unfold acallee_saved; lia))).
assert (R3 : YK11.getr (ms_regs msA) 3 = w64 (as_gp B)) by (rewrite R3'; exact Hgp0).
assert (R4 : YK11.getr (ms_regs msA) 4 = w64 (as_tp B)) by (rewrite R4'; exact Htp0).
destruct (calls_pre (ms_regs msA) 15264 ltac:(lia) ltac:(reflexivity) R1 R2)
  as (HRO1 & HRA4 & HSP1 & HM16 & HLO & HHI).
assert (HSV1 : mrx_saved Wc (ms_mem msA) sp1 regs0)
  by (apply (mrx_saved_kept Wc Wc mem2 (ms_mem msA) sp1 regs0 HSV); intros a Ha; apply KA1; lia).
assert (HTW1 : tw_at TMAP_A (aview sgs (w_H Wc) (ms_mem msA)) Bwc).
{ apply (tw_kept TMAP_A (aview sgs (w_H Wc) mem2) _ Bwc HTW).
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA1. lia. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx sgs (transport_sigma TS_m_wake) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HMW fx MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc (ms_mem msA) _ 0 (ms_regs msA) Bwc B3 rw);
  [ exact HJ | exact HRO1 | exact HRA4 | exact R3 | exact R4 | exact HM16
  | unfold MWAKE_STK, MWAKE_FRAME; lia | exact HHI | exact HTW1 | exact Hmw
  | unfold MWAKE_EV; lia ]. }
cbv beta. intros W2 c2 _ HQ.
unfold transport_mwake_post, transport_cg_post in HQ.
destruct HQ as (ly3 & S3 & regs3 & mem3 & md3 & e & Hc3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HX3).
destruct HX3 as [_ HX3].
assert (He0 : e = 0) by (unfold MWAKE_EV in He3; lia). subst e.
rewrite Z.add_0_r in HJ3. rewrite R1 in Hc3. subst c2.
destruct HK3 as (HK1 & _).
destruct (calls_next Wc W2 (ms_mem msA) mem3 (ms_regs msA) regs3 S2 S3 ly2 ly3 MWAKE_STK
  ltac:(unfold MWAKE_STK, MWAKE_FRAME; lia) ltac:(unfold MWAKE_STK, MWAKE_FRAME; lia)
  HSP1 HSV1 HK1 HP3 R2 R3' R4' Hfr Hfr3 Hperm Hperm3 Hmo Hmo3)
  as (HSV3 & Q2 & Q3 & Q4 & F3 & P3' & M3).
(* the jump to the call of m_tick *)
pose proof (calls_entry W2 regs3 mem3 15264) as HS3.
pose proof (calls_img regs3) as HEI3.
pose proof (calls_shok regs3 W2 mem3) as SHOK3.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 YC4b.Bspan 15288.
{ calls_awr. }
lazymatch type of HS3 with context [restrict _ ?m] => rename m into msB end.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H W2) (ms_mem msB) a = aview sgs (w_H W2) mem3 a)
  by (calls_kept HFr).
assert (EE3 : forall m (q : bv 5), Z.of_nat m = bv_unsigned q -> ew (calls_E regs3) m = YK11.getr regs3 q)
  by (intros m q Hm'; apply calls_ewr; exact Hm').
calls_reg HS3 (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - 144)) RB2
  ltac:(cbn [sv_denot]; rewrite (EE3 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q2).
calls_reg HS3 (Z_to_bv 5 3) (YK11.getr regs0 3) RB3
  ltac:(cbn [sv_denot]; rewrite (EE3 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q3).
calls_reg HS3 (Z_to_bv 5 4) (YK11.getr regs0 4) RB4
  ltac:(cbn [sv_denot]; rewrite (EE3 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q4).
pmkst HS3. rewrite calls_pc_tick.
apply (KT W2 B3).
unfold mrx_at. exists ly3, S3, (ms_regs msB), (ms_mem msB). eexists.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact F3|]. split; [exact P3'|]. split; [exact M3|].
split; [exact RB2|]. split; [exact RB3|]. split; [exact RB4|].
split.
{ apply (mrx_saved_kept W2 W2 mem3 (ms_mem msB) sp1 regs0 HSV3). intros a Ha. apply KA2. lia. }
split.
{ apply (tw_kept TMAP_A (aview sgs (w_H W2) mem3) _ B3 HX3).
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA2. lia. }
split; [exact Hm3 | exact Hr1].
Qed.

(* LOST: `jal m_lost` (a0 = why), then the jump to the TICK cut. *)
Lemma mrx_seg_lost : K (MRX_PC OFF_TICK) (R_TICK Bw' r) -> K (MRX_PC OFF_LOST) (R_LOST Bw' r).
Proof using All.
intros KT. unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & Hfr & Hperm & Hmo & Hsp & Hgp2 & Htp2 & HSV & HTW & HR).
destruct HR as (why & B3 & Hr10 & Hwhy & Hml & Hm3 & Hr1). subst c.
calls_st. assert (FS : MRX_STK = 8352) by reflexivity. unfold MRX_FRAME in *.
rewrite (calls_pcv OFF_LOST).
pose proof (calls_entry Wc regs2 mem2 (AF_m_rx + OFF_LOST)) as HS.
pose proof (calls_img regs2) as HEI.
pose proof (calls_shok regs2 Wc mem2) as SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
assert (EE : forall m (q : bv 5), Z.of_nat m = bv_unsigned q -> ew (calls_E regs2) m = YK11.getr regs2 q)
  by (intros m q Hm'; apply calls_ewr; exact Hm').
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ calls_awr. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem msA) a = aview sgs (w_H Wc) mem2 a)
  by (calls_kept HFr).
clear HF HFr HG.
pmkst HS.
calls_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 14880)) R1 ltac:(apply codeptr_val; exact HEI).
calls_reg HS (Z_to_bv 5 10) (w64 why) R10
  ltac:(cbn [sv_denot]; rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hr10).
assert (HP0 : aregs_preserved regs2 (ms_regs msA))
  by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) (calls_E regs2) _ msA regs2 calls_extra HS);
      [apply calls_agree | vm_compute; reflexivity]).
assert (R2 : YK11.getr (ms_regs msA) 2 = Z_to_bv 64 (sp1 - 144))
  by (rewrite <- Hsp; exact (HP0 2 ltac:(unfold acallee_saved; lia))).
assert (R3' : YK11.getr (ms_regs msA) 3 = YK11.getr regs0 3)
  by (rewrite <- Hgp2; exact (HP0 3 ltac:(unfold acallee_saved; lia))).
assert (R4' : YK11.getr (ms_regs msA) 4 = YK11.getr regs0 4)
  by (rewrite <- Htp2; exact (HP0 4 ltac:(unfold acallee_saved; lia))).
assert (R3 : YK11.getr (ms_regs msA) 3 = w64 (as_gp B)) by (rewrite R3'; exact Hgp0).
assert (R4 : YK11.getr (ms_regs msA) 4 = w64 (as_tp B)) by (rewrite R4'; exact Htp0).
destruct (calls_pre (ms_regs msA) 14880 ltac:(lia) ltac:(reflexivity) R1 R2)
  as (HRO1 & HRA4 & HSP1 & HM16 & HLO & HHI).
assert (HSV1 : mrx_saved Wc (ms_mem msA) sp1 regs0)
  by (apply (mrx_saved_kept Wc Wc mem2 (ms_mem msA) sp1 regs0 HSV); intros a Ha; apply KA1; lia).
assert (HTW1 : tw_at TMAP_A (aview sgs (w_H Wc) (ms_mem msA)) Bwc).
{ apply (tw_kept TMAP_A (aview sgs (w_H Wc) mem2) _ Bwc HTW).
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA1. lia. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx sgs (transport_sigma TS_m_lost) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HML fx MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc (ms_mem msA) _ 0 (ms_regs msA) why Bwc B3);
  [ exact HJ | exact HRO1 | exact HRA4 | exact R3 | exact R4 | exact R10 | exact HM16
  | unfold MLOST_STK, MLOST_FRAME; lia | exact HHI | exact HTW1 | exact Hml | exact Hwhy
  | unfold MLOST_EV; lia ]. }
cbv beta. intros W2 c2 _ HQ.
unfold transport_mlost_post, transport_cg_post in HQ.
destruct HQ as (ly3 & S3 & regs3 & mem3 & md3 & e & Hc3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HX3).
assert (He0 : e = 0) by (unfold MLOST_EV in He3; lia). subst e.
rewrite Z.add_0_r in HJ3. rewrite R1 in Hc3. subst c2.
destruct HK3 as (HK1 & _).
destruct (calls_next Wc W2 (ms_mem msA) mem3 (ms_regs msA) regs3 S2 S3 ly2 ly3 MLOST_STK
  ltac:(unfold MLOST_STK, MLOST_FRAME; lia) ltac:(unfold MLOST_STK, MLOST_FRAME; lia)
  HSP1 HSV1 HK1 HP3 R2 R3' R4' Hfr Hfr3 Hperm Hperm3 Hmo Hmo3)
  as (HSV3 & Q2 & Q3 & Q4 & F3 & P3' & M3).
pose proof (calls_entry W2 regs3 mem3 14880) as HS3.
pose proof (calls_img regs3) as HEI3.
pose proof (calls_shok regs3 W2 mem3) as SHOK3.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 YC4b.Bspan 15288.
{ calls_awr. }
lazymatch type of HS3 with context [restrict _ ?m] => rename m into msB end.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H W2) (ms_mem msB) a = aview sgs (w_H W2) mem3 a)
  by (calls_kept HFr).
assert (EE3 : forall m (q : bv 5), Z.of_nat m = bv_unsigned q -> ew (calls_E regs3) m = YK11.getr regs3 q)
  by (intros m q Hm'; apply calls_ewr; exact Hm').
calls_reg HS3 (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - 144)) RB2
  ltac:(cbn [sv_denot]; rewrite (EE3 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q2).
calls_reg HS3 (Z_to_bv 5 3) (YK11.getr regs0 3) RB3
  ltac:(cbn [sv_denot]; rewrite (EE3 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q3).
calls_reg HS3 (Z_to_bv 5 4) (YK11.getr regs0 4) RB4
  ltac:(cbn [sv_denot]; rewrite (EE3 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q4).
pmkst HS3. rewrite calls_pc_tick.
apply (KT W2 B3).
unfold mrx_at. exists ly3, S3, (ms_regs msB), (ms_mem msB). eexists.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact F3|]. split; [exact P3'|]. split; [exact M3|].
split; [exact RB2|]. split; [exact RB3|]. split; [exact RB4|].
split.
{ apply (mrx_saved_kept W2 W2 mem3 (ms_mem msB) sp1 regs0 HSV3). intros a Ha. apply KA2. lia. }
split.
{ apply (tw_kept TMAP_A (aview sgs (w_H W2) mem3) _ B3 HX3).
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA2. lia. }
split; [exact Hm3 | exact Hr1].
Qed.

(* E0L: `jal m_lost` with a0 = 3; its return address is the E0W cut. *)
Lemma mrx_seg_e0l : K (MRX_PC OFF_E0W) (R_E0W Bw' r) -> K (MRX_PC OFF_E0L) (R_E0L Bw' r).
Proof using All.
intros KW. unfold mrx_K. intros Wc Bwc c HAT.
destruct HAT as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & Hfr & Hperm & Hmo & Hsp & Hgp2 & Htp2 & HSV & HTW & HR).
destruct HR as (B6 & B3 & Hm19 & Hr10 & Hml & He0w & Hm3 & Hr1). subst c.
calls_st. assert (FS : MRX_STK = 8352) by reflexivity. unfold MRX_FRAME in *.
rewrite (calls_pcv OFF_E0L).
pose proof (calls_entry Wc regs2 mem2 (AF_m_rx + OFF_E0L)) as HS.
pose proof (calls_img regs2) as HEI.
pose proof (calls_shok regs2 Wc mem2) as SHOK.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
assert (EE : forall m (q : bv 5), Z.of_nat m = bv_unsigned q -> ew (calls_E regs2) m = YK11.getr regs2 q)
  by (intros m q Hm'; apply calls_ewr; exact Hm').
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ calls_awr. }
lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview sgs (w_H Wc) (ms_mem msA) a = aview sgs (w_H Wc) mem2 a)
  by (calls_kept HFr).
clear HF HFr HG.
pmkst HS.
calls_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 15240)) R1 ltac:(apply codeptr_val; exact HEI).
calls_reg HS (Z_to_bv 5 10) (w64 3) R10
  ltac:(cbn [sv_denot]; rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hr10).
assert (HP0 : aregs_preserved regs2 (ms_regs msA))
  by (apply (aregs_preserved_of_st_ok sgs (w_H Wc) (calls_E regs2) _ msA regs2 calls_extra HS);
      [apply calls_agree | vm_compute; reflexivity]).
assert (R2 : YK11.getr (ms_regs msA) 2 = Z_to_bv 64 (sp1 - 144))
  by (rewrite <- Hsp; exact (HP0 2 ltac:(unfold acallee_saved; lia))).
assert (R3' : YK11.getr (ms_regs msA) 3 = YK11.getr regs0 3)
  by (rewrite <- Hgp2; exact (HP0 3 ltac:(unfold acallee_saved; lia))).
assert (R4' : YK11.getr (ms_regs msA) 4 = YK11.getr regs0 4)
  by (rewrite <- Htp2; exact (HP0 4 ltac:(unfold acallee_saved; lia))).
assert (R3 : YK11.getr (ms_regs msA) 3 = w64 (as_gp B)) by (rewrite R3'; exact Hgp0).
assert (R4 : YK11.getr (ms_regs msA) 4 = w64 (as_tp B)) by (rewrite R4'; exact Htp0).
assert (R19 : YK11.getr (ms_regs msA) 19 = w64 TA_M)
  by (rewrite <- Hm19; exact (HP0 19 ltac:(unfold acallee_saved; lia))).
destruct (calls_pre (ms_regs msA) 15240 ltac:(lia) ltac:(reflexivity) R1 R2)
  as (HRO1 & HRA4 & HSP1 & HM16 & HLO & HHI).
assert (HSV1 : mrx_saved Wc (ms_mem msA) sp1 regs0)
  by (apply (mrx_saved_kept Wc Wc mem2 (ms_mem msA) sp1 regs0 HSV); intros a Ha; apply KA1; lia).
assert (HTW1 : tw_at TMAP_A (aview sgs (w_H Wc) (ms_mem msA)) Bwc).
{ apply (tw_kept TMAP_A (aview sgs (w_H Wc) mem2) _ Bwc HTW).
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA1. lia. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx sgs (transport_sigma TS_m_lost) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HML fx MRX_STK sp1 [] lyc Sc W memc mdc [] ly2 S2 Wc (ms_mem msA) _ 0 (ms_regs msA) 3 Bwc B6);
  [ exact HJ | exact HRO1 | exact HRA4 | exact R3 | exact R4 | exact R10 | exact HM16
  | unfold MLOST_STK, MLOST_FRAME; lia | exact HHI | exact HTW1 | exact Hml | lia
  | unfold MLOST_EV; lia ]. }
cbv beta. intros W2 c2 _ HQ.
unfold transport_mlost_post, transport_cg_post in HQ.
destruct HQ as (ly3 & S3 & regs3 & mem3 & md3 & e & Hc3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HX3).
assert (He0 : e = 0) by (unfold MLOST_EV in He3; lia). subst e.
rewrite Z.add_0_r in HJ3. rewrite R1 in Hc3. subst c2.
destruct HK3 as (HK1 & _).
destruct (calls_next Wc W2 (ms_mem msA) mem3 (ms_regs msA) regs3 S2 S3 ly2 ly3 MLOST_STK
  ltac:(unfold MLOST_STK, MLOST_FRAME; lia) ltac:(unfold MLOST_STK, MLOST_FRAME; lia)
  HSP1 HSV1 HK1 HP3 R2 R3' R4' Hfr Hfr3 Hperm Hperm3 Hmo Hmo3)
  as (HSV3 & Q2 & Q3 & Q4 & F3 & P3' & M3).
assert (Q19 : YK11.getr regs3 19 = w64 TA_M)
  by (rewrite <- R19; exact (HP3 19 ltac:(unfold acallee_saved; lia))).
rewrite calls_pc_e0w.
apply (KW W2 B6).
unfold mrx_at. exists ly3, S3, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact F3|]. split; [exact P3'|]. split; [exact M3|].
split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact HSV3|]. split; [exact HX3|].
exists B3. split; [exact Q19|]. split; [exact He0w|]. split; [exact Hm3 | exact Hr1].
Qed.

End seg.
