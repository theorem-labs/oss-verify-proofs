(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths, module names and numbers changed; 158 of its 374 lines of code are new or changed and 814 lines of the source are left out. *)
(* m_rx_seg_head: the head segment of the image-B walk of m_rx (statement lib/B/Prog/m_rx_cg.v, kit
   lib/B/Prog/m_rx_seg_kit.v): from the entry 0x84c1c to the cut SRF (0x84c40, `jal spec_read_frame`).
     0x84c1c - 0x84c2c  sp = sp - 112 and the 4 saves (ra, s0, s1, s2 at sp + 104 .. sp + 80);
     0x84c30 - 0x84c38  s2 = the shadow base (the GOT word A_OBJ 1, then the cell A_OBJ 95 it points to);
     0x84c3c            a2 = sp.
   One run of the inner G journal, to the stop pc 0x84c40. It writes only the 112 bytes below the entry sp, so the
   journal stays at the call state (lyc, Sc), the world relation stays at Bw (the stores are outside G) and the frame's
   bytes, the shadow band and the read-only bytes keep their entry values (the frame lies outside the window). *)
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

(* ---- the symbolic state of the run ---- *)

(* The entry (0x84c1c): the 112-byte frame below sp, the shadow base's GOT word (object 1) and its cell (object 95).
   Atom 32 is the shadow base; no shadow entry (no instrumented access in the run). *)
Definition mh_regions : smem := [stack_region MRX_FRAME; got_regionP; bcell_regionP 32].
Definition mh_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_mh : sstate := mkSS AF_m_rx sr_atoms mh_regions None mh_facts.
Definition MH_Bx : sv := SOff 32 0.
Definition MH_B0 : Z * Z := (0, 0).

(* The 4 saved slots, as chunks of the stack region at the stop: ra, s0, s1, s2 at sp - 8 .. sp - 32. *)
Definition mh_save_chunks : list YP09.chunk :=
  [YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

(* ---- small helpers ---- *)

(* An 8-byte chunk of value v, read back as a word through the view. *)
Lemma mh_rdword_chunk : forall (E : env) (Hh : word -> bool) (mm : word -> option byte) (base off : Z) (e : sv) (v : Z),
  YP09.chunk_ok tfibsegs E (mrestrict Hh mm) base (YP09.mkChunk off (CVal 8 e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview tfibsegs Hh mm) (base + off) = Some v.
Proof.
intros E Hh mm base off e v HC He Hv.
assert (Hb : forall j, (j < 8)%nat -> aview tfibsegs Hh mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v 8 j))
  by (intros j Hj; exact (mrx_chunk_rd E Hh mm base off 8%N e v HC He ltac:(cbn; lia) j ltac:(cbn; lia))).
pose proof (Hb 0%nat ltac:(lia)) as B0. pose proof (Hb 1%nat ltac:(lia)) as B1.
pose proof (Hb 2%nat ltac:(lia)) as B2. pose proof (Hb 3%nat ltac:(lia)) as B3.
pose proof (Hb 4%nat ltac:(lia)) as B4. pose proof (Hb 5%nat ltac:(lia)) as B5.
pose proof (Hb 6%nat ltac:(lia)) as B6. pose proof (Hb 7%nat ltac:(lia)) as B7.
change (Z.of_nat 0) with 0 in B0. rewrite Z.add_0_r in B0.
change (Z.of_nat 1) with 1 in B1. change (Z.of_nat 2) with 2 in B2.
change (Z.of_nat 3) with 3 in B3. change (Z.of_nat 4) with 4 in B4.
change (Z.of_nat 5) with 5 in B5. change (Z.of_nat 6) with 6 in B6.
change (Z.of_nat 7) with 7 in B7.
unfold rdword. rewrite B0, B1, B2, B3, B4, B5, B6, B7. f_equal. exact (le_bytes8 v Hv).
Qed.

Ltac mh_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* The 4 saved slots from the stack region's chunks at the stop (base = the entry sp). *)
Lemma mh_saved_of : forall (E : env) (Wx : world tfibsegs) (mm : word -> option byte) (base : Z) (regsx : bvmap 5 word),
  (forall j : Z, 0 <= j < 32 -> ew E (Z.to_nat j) = YK11.getr regsx (Z_to_bv 5 j)) ->
  (forall c, In c mh_save_chunks -> YP09.chunk_ok tfibsegs E (mrestrict (w_H Wx) mm) base c) ->
  mrx_saved Wx mm base regsx.
Proof.
intros E Wx mm base regsx HE HF.
assert (HD : forall (jz coff : Z), 0 <= jz < 32 ->
  In (YP09.mkChunk coff (CVal 8 (SOff (Z.to_nat jz) 0))) mh_save_chunks ->
  rdword (aview tfibsegs (w_H Wx) mm) (base + coff) = Some (bv_unsigned (YK11.getr regsx (Z_to_bv 5 jz)))).
{ intros jz coff Hj Hin.
  apply (mh_rdword_chunk E (w_H Wx) mm base coff (SOff (Z.to_nat jz) 0));
  [ exact (HF _ Hin)
  | cbn [sv_denot]; rewrite (HE jz Hj), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | apply YK11.u64_range ]. }
unfold mrx_saved, MRX_SAVES.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
- replace (base - MRX_FRAME + 104) with (base + (-8)) by (unfold MRX_FRAME; lia).
  exact (HD 1 (-8) ltac:(lia) ltac:(mh_in)).
- replace (base - MRX_FRAME + 96) with (base + (-16)) by (unfold MRX_FRAME; lia).
  exact (HD 8 (-16) ltac:(lia) ltac:(mh_in)).
- replace (base - MRX_FRAME + 88) with (base + (-24)) by (unfold MRX_FRAME; lia).
  exact (HD 9 (-24) ltac:(lia) ltac:(mh_in)).
- replace (base - MRX_FRAME + 80) with (base + (-32)) by (unfold MRX_FRAME; lia).
  exact (HD 18 (-32) ltac:(lia) ltac:(mh_in)).
Qed.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac mh_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "mh_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs. *)
Ltac mh_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write rights of the run: the 112-byte frame below sp, inside the inner journal's window. *)
Ltac mh_awr UspE :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite UspE in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_nil.

(* A register of s3 .. s11 (x19 .. x27) at the stop is the entry's: the run writes none of them (EE reads the
   entry registers off the valuation). *)
Ltac mh_hi HS EE regs0 :=
  lazymatch goal with |- YK11.getr _ (Z_to_bv 5 ?qz) = _ =>
    let qn := eval vm_compute in (Z.to_nat qz) in
    let Hr := fresh "Hr" in
    mh_reg HS (Z_to_bv 5 qz) (YK11.getr regs0 (Z_to_bv 5 qz)) Hr
      ltac:(cbn [sv_denot]; rewrite (EE qn (Z_to_bv 5 qz) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
    exact Hr
  end.

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

Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma mh_vals : VAL (A_OBJ 1) = BCells.GOT_CELL_K /\ VAL (A_OBJ 95) = BCells.CELL_K /\
  BASE + AF_m_rx = transportb_sigma TB_m_rx.
Proof. vm_compute. repeat split. Qed.

(* The walk's valuation: the 32 entry registers and the shadow base (atom 32). *)
Definition mh_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).

(* The two image regions hold the shadow base, at any AR state (transport_cells rows 1-2). *)
Lemma mh_img_ok : forall ly S (Wx : world segs) mem md (E : env),
  @AR rc segs B ly S Wx mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H Wx) mem) got_regionP /\
  region_ok segs E (mrestrict (w_H Wx) mem) (bcell_regionP 32).
Proof.
  intros ly S Wx mem md E HAR E1 E95 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct mh_vals as (V1 & V95 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H Wx) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H Wx) mem) BCells.CELL_K = Some BCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold BCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H Wx) mem) BCells.GOT_CELL_K = Some BCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold BCells.CELL_K; lia | exact (CH _ I2)]).
  assert (VB : forall nn v0, ew E nn = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some nn) = v0)
    by (intros nn v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (P64 : 2 ^ (8 * Z.of_N 8) = 2 ^ 64) by reflexivity.
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold BCells.GOT_CELL_K; lia).
  assert (R95 : 0 <= VAL (A_OBJ 95) < 2 ^ 47) by (rewrite V95; unfold BCells.CELL_K; lia).
  unfold got_regionP, bcell_regionP, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split.
  - rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 95) 0) (VAL (A_OBJ 95)));
    [cbn [sv_denot]; rewrite E95, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite P64; lia | cbn; lia |].
    rewrite Z.add_0_r, V1, V95. exact (val_mem_of_rdword segs (w_H Wx) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E95) by lia.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 95)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite P64; unfold SHADOW_OFF; lia | cbn; lia |].
    rewrite Z.add_0_r, V95. exact (val_mem_of_rdword segs (w_H Wx) mem _ _ Kcell).
Qed.

(* The entry state of the run. *)
Lemma mh_entry : forall ly S (Wx : world segs) regs mem md,
  @AR rc segs B ly S Wx mem md ->
  (forall a, spZ regs - MRX_FRAME <= a < spZ regs -> apresent (w_H Wx) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (mh_E regs) ss_mh
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_rx)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S Wx regs mem md HAR Hpres Hsp Hsp16.
  assert (E2' : ew (mh_E regs) 2 = YK11.getr regs 2) by (unfold mh_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew (mh_E regs) 2) = spZ regs) by (rewrite E2'; reflexivity).
  assert (E32 : ew (mh_E regs) 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold mh_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (EOB : forall j, (j < 97)%nat -> ew (mh_E regs) (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold mh_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct (mh_img_ok ly S Wx mem md (mh_E regs) HAR (EOB 1%nat ltac:(lia)) (EOB 95%nat ltac:(lia)) E32)
    as [RG RC].
  destruct mh_vals as (V1 & V95 & _).
  assert (VB : forall nn v0, ew (mh_E regs) nn = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (mh_E regs) (Some nn) = v0)
    by (intros nn v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  rewrite restrict_mkst_fx. unfold ss_mh, mh_regions.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [exact RG | apply Forall_cons; [exact RC | apply Forall_nil]]].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold MRX_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (rewrite V1; unfold BCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (EOB 95%nat ltac:(lia))) by (rewrite V95; unfold BCells.CELL_K; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V95. unfold BCells.GOT_CELL_K, BCells.CELL_K, MRX_FRAME in *.
    repeat split; first [exact I | lia].
  - unfold mh_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | unfold SHADOW_OFF; lia].
Qed.

(* ---- the segment ---- *)

Lemma mrx_seg_head : K (MRX_PC OFF_SRF) (R_SRF B fr n sp1 lyc Sc Bw' r) ->
  forall Bw : list byte, @mrx_K_entry fx rc B MT sp1 regs0 lyc Sc W memc mdc fr n Bw Bw' r.
Proof using All.
intros HKS Bw.
unfold mrx_K_entry. intros HJ Hgarr Hrom Htw Hm.
pose proof HST as (Hsp1 & Hsp16 & Hceil & Hslo & Hshi & Hra & Hra4 & Hgp & Htp & Ha0 & Ha1 &
  Hfa0 & Hfan & Hfaml & Hsrc & Hoff & Hapart & Hev & HAR).
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MRX_STK = 8384) by reflexivity.
assert (FF : MRX_FRAME = 112) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs0 <= 2 ^ 47) by (rewrite Hsp1; lia).
set (E0 := mh_E regs0).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, mh_E; apply Eimg_env).
assert (EE : forall nn (rg : bv 5), Z.of_nat nn = bv_unsigned rg -> ew E0 nn = YK11.getr regs0 rg)
  by (intros nn rg Hn; unfold E0, mh_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EZ : forall j : Z, 0 <= j < 32 -> ew E0 (Z.to_nat j) = YK11.getr regs0 (Z_to_bv 5 j)).
{ intros j Hj. apply EE. rewrite Z2Nat.id by lia. symmetry.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32. apply Z.mod_small. lia. }
assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E0, mh_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 0)).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
pose proof (mh_entry lyc Sc W regs0 memc mdc HAR ltac:(intros a Ha; apply Hpres0; lia) Hsp
  ltac:(rewrite Hsp1; exact Hsp16)) as HS.
fold E0 in HS.
assert (SHOK : sh_ok segs MH_Bx [] E0 (mrestrict (w_H W) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
unfold cfg_at.
destruct mh_vals as (_ & _ & VB0).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 (BASE + AF_m_rx)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* the run, +0x000 .. +0x020: the frame, the 4 saves, s2 = the shadow base, a2 = sp; stop at the jal (+0x024) *)
paj_run_to_tok RUNTO HS HJ SHOK MH_B0 (AF_m_rx + 36).
{ mh_awr Usp. }
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody md1. clear mat.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - MRX_FRAME <= a < sp1) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ (w_H W) memc (ms_mem ms) (fun x => sp1 - MRX_FRAME <= x < sp1) HFr);
    [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta.
  mh_win Hin Hx ltac:(rewrite ?Usp in Hx; lia). }
clear HF HFr HG.
(* the registers at the stop *)
pmkst HS.
mh_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) R2
  ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
mh_reg HS (3%bv : bv 5) (YK11.getr regs0 3) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mh_reg HS (4%bv : bv 5) (YK11.getr regs0 4) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mh_reg HS (Z_to_bv 5 10) (w64 (TI.tf_addr fr)) R10
  ltac:(cbn [sv_denot]; rewrite (EE 10%nat (10%bv : bv 5) eq_refl), Ha0, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
mh_reg HS (Z_to_bv 5 11) (w64 n) R11
  ltac:(cbn [sv_denot]; rewrite (EE 11%nat (11%bv : bv 5) eq_refl), Ha1, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
mh_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (sp1 - MRX_FRAME)) RA2
  ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
mh_reg HS (Z_to_bv 5 18) (w64 SHADOW_OFF) R18
  ltac:(cbn [sv_denot]; rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia);
        rewrite Z.add_0_r; reflexivity).
assert (RHI : mrx_hi regs0 (ms_regs ms)).
{ intros q Hq.
  assert (Hq' : q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
  destruct Hq' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; mh_hi HS EE regs0. }
(* the 4 saved slots *)
pose proof (st_ok_pi_region_nth E0 _ _ 0 _ HS eq_refl) as RG0.
cbn [ms_mem restrict] in RG0.
destruct RG0 as (_ & _ & _ & HCH0).
cbn [YP09.r_base YP09.r_chunks base_val] in HCH0. rewrite Usp in HCH0.
assert (HSV : mrx_saved W (ms_mem ms) sp1 regs0).
{ rewrite <- Hsp1. apply (mh_saved_of E0 W (ms_mem ms) (spZ regs0) regs0 EZ).
  intros c Hc. apply (proj1 (Forall_forall _ _) HCH0).
  unfold mh_save_chunks in Hc. cbn [In] in Hc.
  repeat (destruct Hc as [Hc | Hc]; [subst c; mh_in |]). destruct Hc. }
(* the world relation: the run wrote below sp1, outside G *)
assert (TWF : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms)) Bw).
{ apply (tw_kept TMAP_B (aview segs (w_H W) memc)); [exact Htw|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KA; lia. }
(* the frame's bytes, its placement and the read-only view at the stop *)
assert (HFRS : mrx_frs B fr lyc Sc W (ms_mem ms)).
{ apply (mrx_frs_view B fr lyc Sc W W memc (ms_mem ms)).
  - split; [exact Hgarr | split; [exact Hsrc | exact Hrom]].
  - intros a Ha. apply KA; lia.
  - intros s Hs. apply KA; lia.
  - intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Rb. apply KA; lia. }
(* the cut *)
replace (BASE + 14752) with (MRX_PC OFF_SRF)
  by (unfold MRX_PC, OFF_SRF; rewrite <- VB0; unfold AF_m_rx; lia).
apply (HKS W Bw).
eapply mrx_at_intro.
- exact HJ.
- reflexivity.
- apply Permutation_refl.
- exact (mo_le_refl MT MTL Sc).
- exact R2.
- exact R3.
- exact R4.
- exact RHI.
- exact HSV.
- exact TWF.
- unfold R_SRF. split; [reflexivity|]. split; [reflexivity|]. split; [exact HFRS|].
  split; [exact R10|]. split; [exact R11|]. split; [exact RA2|]. split; [exact R18 | exact Hm].
Qed.

End seg.
