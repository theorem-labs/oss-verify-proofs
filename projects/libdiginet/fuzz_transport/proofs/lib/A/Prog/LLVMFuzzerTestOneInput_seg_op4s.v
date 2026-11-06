(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module names changed; 401 of its 453 lines of code are new or changed and 507 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4s: Lemma lc_op4s_ok : lc_op4s_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment OP4S of the image-A walk of LLVMFuzzerTestOneInput (fuzz_transport.asan e89be137db17), from the cut S4
   (lc_st_s4, +0x12c8) to the cut TAIL (lc_st_tail, +0x12ec). The code (offsets from the entry 0x81264, listing
   lib/A/Prog/DgnTransportList.v slot k at 0x81264 + 4k):
     +0x12c8  `li a0, 0`        a0 = ticked = 0;
     +0x12cc  `jal settle`      (return address +0x12d0): settle_cg.v transport_settle_cg (lp_settle), a donor-form
                                callee lifted into the walk's G journal by TransportGCg.v gx_call_cg, from sp = sp1,
                                with tw_at at Bw, settle_m Bw 0 = Some (Bw, tt) (the cut's), invariant (2) at Bw and
                                no event. Invariant (2) comes from the operation's model equation at Bw: at the stream
                                fun _ => 4096 (recv_addr_ok 4096) LLVMFuzzerTestOneInput_st.v lc_tail_agree gives
                                agree timg_A (ops + 1) Bw, and TSim/TickTakeQ.v tt_sq_ok / ttq_sq_d4 bound every
                                queued entry's length by 24. Its post keeps the world (X: Bw = Bw; gx_kept: tw_kept_GA),
                                the callee-saved registers, the frames and blocks, and every byte outside its window
                                [sp1 - SETTLE_STK, sp1): LLVMFuzzerTestOneInput_st.v lc_core_kept carries the core;
                                lc_spills_kept / lc_fsh_kept carry the spill slots and the frame's shadow;
     +0x12d0  `li a0, -8`;
     +0x12d4 .. +0x12e0  `sb a0, 4(s2)` .. `sb a0, 7(s2)`: the frame's shadow bytes 4 .. 7 (c's granules) become 0xf8,
                                c out of scope (lf_shm true false to lf_shm false false). s2 = lc_SH (lc_fr); the four
                                bytes are shadow bytes of the frame the journal owns (TransportGFrame.v
                                awr_ok_x_cons_own). No byte that lc_core reads is a shadow byte, so the core is carried
                                over the stores by its own conjuncts;
     +0x12e4  `mv s8, s3`       the cursor's address into s8;
     +0x12e8  `li s6, 7`.
   Both stretches of straight code are runs of the token engine over the G journal (TransportGRunA.v paj_run_x /
   paj_run_to_x); the first has no region and stops at the jal, the second has one region (the four shadow bytes) and
   runs to TAIL. The tail's witnesses: a = 4096, k' = lo_k op, cn = the cut's c5, the model equation the cut's at
   A = fun _ => 4096. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import settle_cg receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree TickTakeQ.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module TTQ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.TickTakeQ.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states of the two runs                              *)
(* ------------------------------------------------------------------ *)

(* Atoms 0 .. 31: the registers at the run's start; no shadow entry (the segment has no instrumented check). *)
Definition OP_B0 : Z * Z := (0, 0).
Definition OP_Bx : sv := SLit 0.
(* Run 1 from S4 (+0x12c8): no region. *)
Definition op_ss1 : sstate := mkSS (AF_LLVMFuzzerTestOneInput + LO_S4) sr_atoms [] None (mkFacts [] [] []).
(* Run 2 from the return address of the call (+0x12d0): the frame's shadow bytes 4 .. 7 at s2 (atom 18), written. *)
Definition OP_RET : Z := AF_LLVMFuzzerTestOneInput + 0x12d0.
Definition op_rg_sh : YP09.region := YP09.mkRegion (Some 18%nat) 4 8 4 8 [].
Definition op_facts2 : facts := mkFacts [(18%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition op_ss2 : sstate := mkSS OP_RET sr_atoms [op_rg_sh] None op_facts2.

(* The value of register r in the machine state of HS: its symbolic value, computed, then tac. *)
Ltac op_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "op_reg: no match for" T; fail
  end.
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac op_region HS i HR :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
(* The write rights of a run: the regions, computed. *)
Ltac op_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* After a run: the model generalized. *)
Ltac op_after :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end.

(* The frame's shadow map before and after the four stores: equal outside bytes 4 .. 7, which become 0xf8. *)
Lemma op_shm_out : forall j, (j < 32)%nat -> (j < 4 \/ 8 <= j)%nat ->
  nth j (lf_shm true false) 0 = nth j (lf_shm false false) 0.
Proof. intros j Hj Hr. do 32 (destruct j as [|j]; [first [reflexivity | lia] |]). lia. Qed.
Lemma op_shm_in : forall j, (4 <= j < 8)%nat -> nth j (lf_shm false false) 0 = 0xf8.
Proof. intros j Hj. do 8 (destruct j as [|j]; [first [reflexivity | lia] |]). lia. Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition op_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).

Lemma op_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (op_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold op_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma op_env_img : forall regs, img_env VAL A_LIM (op_E regs).
Proof. intros regs. unfold op_E. apply Eimg_env. Qed.
Lemma op_agree : forall regs, env_agree 32 (Ereg regs []) (op_E regs).
Proof. intros regs. split; [intros n Hn; unfold op_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* Run 1's state holds of any machine state at its pc. *)
Lemma op_entry1 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (op_E regs) op_ss1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + LO_S4))) mem
      (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold op_ss1.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* Run 2's state: s2 = SH, the four shadow bytes SH + 4 .. SH + 8 present. *)
Lemma op_entry2 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 18 = w64 SH -> SHADOW_OFF <= SH -> SH + 8 <= 2 ^ 46 ->
  (forall a, SH + 4 <= a < SH + 8 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (op_E regs) op_ss2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OP_RET)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R18 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold op_ss2.
  assert (U18 : bv_unsigned (ew (op_E regs) 18) = SH)
    by (rewrite (op_ew_reg regs 18 18%bv eq_refl), R18; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold op_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U18. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold op_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold op_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.
End e.

(* A kept register at the end of a run whose valuation is op_E regs: the value of its atom rn. *)
Ltac op_kept_tac regs rn rz :=
  cbn [sv_denot]; rewrite (op_ew_reg regs rn (Z_to_bv 5 rz) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity.

(* A one-byte chunk of a literal, read through the view. *)
Lemma op_byte_view : forall (sg : list Segment) E (H : word -> bool) (m : word -> option byte) base off n,
  YP09.chunk_ok sg E (mrestrict H m) base (YP09.mkChunk off (CVal 1 (SLit n))) ->
  aview sg H m (base + off) = Some (bv_unsigned (YP09.byte_of_word (Z_to_bv 64 n) 0)).
Proof.
  intros sg E H m base off n Hc. destruct (Hc 0 ltac:(cbn; lia)) as (b & Eb & Mb).
  cbn [YP09.cbyte YP09.c_val YP09.c_off sv_denot] in Eb, Mb. injection Eb as <-. rewrite Z.add_0_r in Mb.
  unfold aview. rewrite Mb. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Section s. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* A live block is apart from the shadow bytes of a live side-stack frame. *)
Lemma op_blk_sh : forall ly S (W : world segs) m md b nb cid pos x,
  AR_laws segs B -> AR segs B ly S W m md -> In (b, nb) (ablocks B ly S) -> In (cid, pos) (frames S) ->
  shadow_addr (frame_addr ly cid pos) <= x < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
  b <= x < b + req_size nb -> False.
Proof.
  intros ly S W m md b nb cid pos x LAWS HAR Hin Hf Hr Hx.
  destruct (al_blocks _ _ LAWS ly S W m md b nb HAR Hin) as (_ & H4096 & Hce & Happ & _).
  destruct (frames_bounds segs B LAWS ly S W m md cid pos HAR Hf) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hfs) as Hse.
  assert (Hd : (frame_addr ly cid pos + fs_frame_bytes cid) / 8 <= 0x7fffff800000 / 8)
    by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos (frame_addr ly cid pos) 8 ltac:(lia) ltac:(lia)) as Hd0.
  change (0x7fffff800000 / 8) with 0xffffff00000 in Hd.
  unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg in *. lia.
Qed.

Lemma lc_op4s_ok : lc_op4s_stmt B MT XL RLO RHI.
Proof.
unfold lc_op4s_stmt. intros HP cx op W' c' HB HS4.
destruct HP as [HPCS HCELLS HSCFGC HRECVC HSETC HLLC HGU HGN HROU HRNE HRLO HRHI LAWS MTL MTF SMP ASF FFL AIL
  HSINK HMETA ROB ASM2 AMEMCPY ASCFG AMEMSET ASINIT AMWAKE AWAKE ACSWC ARECV AMTICK ATICK ASETTLE ASTRLEN ABAR
  ASUBMIT ACRS ACLOSE ACLS HXL].
clear HPCS HCELLS HSCFGC HRECVC HSETC HLLC HROU HRNE HRLO HRHI MTF SMP ASF FFL AIL HSINK HMETA ROB ASM2 AMEMCPY ASCFG
  AMEMSET ASINIT AMWAKE AWAKE ACSWC ARECV AMTICK ATICK ASTRLEN ABAR ASUBMIT ACRS ACLOSE ACLS HXL.
pose proof (G_HARNESS_gx_ok B HGU) as HGX.
pose proof (G_HARNESS_gx_noerrno B HGN) as HGNE.
destruct HS4 as (ly' & S' & regs' & mem' & md' & e & Bw & c5 & -> & Hopc & HL & HTW & HSET & HOP & HCUR & R20).
destruct HL as (HC & HFR & HSP & HFSH & HOK & He & HMT & R21).
pose proof HOK as (HAG & Hops & Hfin & Hfn & Hk).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
destruct HFR as (R18 & R26).
destruct HCUR as (R19 & R23).
(* the register facts, at Z_to_bv 5 r *)
assert (Rsp' : YK11.getr regs' (Z_to_bv 5 2) = w64 (lc_sp1 cx)) by exact Rsp.
assert (R8' : YK11.getr regs' (Z_to_bv 5 8) = w64 (lc_sp0 cx)) by exact R8.
assert (R9' : YK11.getr regs' (Z_to_bv 5 9) = w64 (lc_sp1 cx)) by exact R9.
assert (Rgp' : YK11.getr regs' (Z_to_bv 5 3) = w64 (as_gp B)) by exact Rgp.
assert (Rtp' : YK11.getr regs' (Z_to_bv 5 4) = w64 (as_tp B)) by exact Rtp.
assert (R18' : YK11.getr regs' (Z_to_bv 5 18) = w64 (lc_SH cx)) by exact R18.
assert (R26' : YK11.getr regs' (Z_to_bv 5 26) = w64 SHADOW_OFF) by exact R26.
assert (R20' : YK11.getr regs' (Z_to_bv 5 20) = w64 LF_S4) by exact R20.
assert (R21' : YK11.getr regs' (Z_to_bv 5 21) = w64 (lo_ops op)) by exact R21.
clear Rsp R8 R9 Rgp Rtp R18 R26 R20 R21.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HBASE : BASE = 0x81264) by (vm_compute; reflexivity).
assert (ESS : SETTLE_STK = 8288) by reflexivity.
assert (HSH0 : SHADOW_OFF <= lc_SH cx /\ lc_SH cx + 32 <= 2 ^ 46).
{ unfold lc_SH, SHADOW_OFF, LF_FBYTES in *. split; [pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)); lia|].
  assert (lc_F cx / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 46) with 0x400000000000.
  change (0x7fffff800000 / 8) with 0xffffff00000 in *. lia. }
destruct HSH0 as [HSHlo HSHhi].
(* invariant (2) of the world settle is handed, from the operation's model equation (lc_tail_agree, tt_sq_ok) *)
assert (HQL : forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN).
{ destruct (lc_tail_agree (l_pl cx) (lo_ops op) (lo_B op) (lo_c op) (lo_k op) 4096 Bw c5 (lo_k op) HAG Hops Hfin Hfn Hk
    ltac:(unfold recv_addr_ok; split; [lia | vm_compute; discriminate]) (HOP (fun _ => 4096))) as (HA1 & _ & _).
  pose proof (TTQ.tt_sq_ok (lo_ops op + 1) Bw (AG.ac_len _ _ _ (AG.ag_core _ _ _ HA1))
    (AG.ac_q _ _ _ (AG.ag_core _ _ _ HA1))) as HF.
  intros i Hi. destruct (TTQ.ttq_sq_d4 Bw i HF Hi) as [Hl _]. unfold TS0.DIGINET_CMD_MAX_LEN. lia. }
(* the event count at the call *)
assert (HEV : st_nev (l_S cx) + e + SETTLE_EV <= EV_MAX).
{ pose proof HB as HB'. unfold lc_base, ACfn.tfib_lib_pre_x in HB'.
  destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
  unfold SETTLE_EV, RECV_EV, ACfn.EV_LIB, TC.OPS_MAX in *. lia. }

(* ---- +0x12c8 .. +0x12cc: a0 = 0, the call of settle ---- *)
unfold lc_cfg.
replace (w64 (transport_text + LO_S4)) with (Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + LO_S4)))
  by (rewrite HBASE; reflexivity).
pose proof (@op_entry1 (l_fx cx) rc W' regs' mem') as HS.
assert (HEI1 : img_env VAL A_LIM (op_E regs')) by apply op_env_img.
assert (SHOK1 : sh_ok segs OP_Bx (@nil shent) (op_E regs') (mrestrict (w_H W') mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUNTO.
paj_run_tok RUN HS HJ SHOK1 OP_B0.
{ op_awr_rs. apply awr_ok_x_nil. }
op_after.
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
assert (KA1 : forall a, aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') mem' a).
{ intros a. rewrite (aview_wrap64 segs (w_H W') (ms_mem ms1) a), (aview_wrap64 segs (w_H W') mem' a).
  apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| apply Z.mod_pos_bound; lia | intros []].
  intros b wlo whi x Hin.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  destruct Hin. }
clear HF HFr HG.
pmkst HS.
(* ra = the return address +0x12d0 (4816) *)
op_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 4816)) R1a ltac:(apply codeptr_val; exact HEI1).
op_reg HS (Z_to_bv 5 2) (YK11.getr regs' (Z_to_bv 5 2)) Q2
  ltac:(cbn [sv_denot]; rewrite (op_ew_reg regs' 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
op_reg HS (Z_to_bv 5 10) (w64 0) Q10 ltac:(reflexivity).
assert (P1 : aregs_preserved regs' (ms_regs ms1))
  by (apply (aregs_preserved_of_st_ok segs (w_H W') (op_E regs') _ ms1 regs' [] HS);
      [ exact (op_agree regs') | vm_compute; reflexivity ]).
assert (Hsp1q : spZ (ms_regs ms1) = lc_sp1 cx).
{ change (bv_unsigned (YK11.getr (ms_regs ms1) (Z_to_bv 5 2)) = lc_sp1 cx). rewrite Q2, Rsp'.
  apply unsigned_lit_small. unfold LF_FRAME in *. lia. }
assert (HTWc : tw_at TMAP_A (aview segs (w_H W') (ms_mem ms1)) Bw)
  by exact (tw_kept TMAP_A _ _ Bw HTW (fun x _ => KA1 x)).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at (l_fx cx) segs (transport_sigma TS_settle) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_call_cg (l_fx cx) rc tfib_sink_head segs B MT TG.G_HARNESS _ _ _ _ _ _ _ _ _ ly' S' W' (ms_mem ms1) _ e
    _ (ms_regs ms1) SETTLE_STK SETTLE_EV 0 (fun _ => False) (fun _ _ _ => Bw = Bw) HGX HGNE HJ).
  intros memS HJS. eapply SRr_mono.
  { apply (ASETTLE (l_fx cx) _ _ _ _ _ _ memS _ _ ly' S' W' (ms_mem ms1) _ e (ms_regs ms1) 0 Bw Bw HJS).
    - rewrite R1a. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
    - change (4096 <= bv_unsigned (YK11.getr (ms_regs ms1) 1%bv)). rewrite R1a, HBASE.
      rewrite unsigned_lit_small by lia. lia.
    - exact (eq_trans (P1 3 ltac:(unfold acallee_saved; lia)) Rgp').
    - exact (eq_trans (P1 4 ltac:(unfold acallee_saved; lia)) Rtp').
    - exact Q10.
    - lia.
    - rewrite Hsp1q. pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D1.
      rewrite Hsp1al, Z.add_0_r in D1. rewrite D1.
      replace (32 * (lc_sp1 cx / 32)) with ((2 * (lc_sp1 cx / 32)) * 16) by ring. apply Z.mod_mul. lia.
    - rewrite Hsp1q, ESS. unfold ACfn.LLVMF_STK, LF_FRAME in *. lia.
    - rewrite Hsp1q. unfold LF_FRAME in *. lia.
    - exact HTWc.
    - exact HSET.
    - exact HQL.
    - exact HEV. }
  intros W2 c2 _ Hp. apply decode_cg_post_dcg. exact Hp. }
cbv beta. intros W3 c3 _ HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & HMO3 & [_ HGK3]).
assert (Ee3 : e3 = 0) by (unfold SETTLE_EV in He3; lia). subst e3. rewrite Z.add_0_r in HJ3.
rewrite R1a.
assert (PP3 : aregs_preserved regs' regs3) by exact (aregs_preserved_trans _ _ _ P1 HP3).
destruct HK3 as (K31 & K32 & K33 & K34 & K35 & K36).
rewrite Hsp1q, ESS in K31.
(* what settle kept: every byte from alloc_ceiling up outside [sp1 - 8288, sp1), the blocks, the frame and its shadow *)
assert (KS3 : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - 8288 <= a < lc_sp1 cx) ->
  aview segs (w_H W3) mem3 a = aview segs (w_H W') mem' a).
{ intros a Ha Hw. exact (eq_trans (K31 a Ha Hw) (KA1 a)). }
assert (KB3 : forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
  aview segs (w_H W3) mem3 (b + i) = aview segs (w_H W') mem' (b + i)).
{ intros b m i Hb Hi. exact (eq_trans (K32 b m i Hb Hi (fun x => x)) (KA1 (b + i))). }
assert (KF3 : forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
  aview segs (w_H W3) mem3 a = aview segs (w_H W') mem' a).
{ intros a Ha. refine (eq_trans (K34 LF_CID (l_fpos cx) a HFin _ (fun x => x)) (KA1 a)).
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFaddr, lf_fbytes.
  change (fs_frame_bytes LF_CID / 8) with 32. unfold lc_SH in Ha. unfold shadow_addr. exact Ha. }
clear K31 K32 K33 K34 K35 K36.
assert (HC3 : lc_core B cx ly3 S3 W3 regs3 mem3 md3 e).
{ apply (lc_core_kept B MT XL RLO RHI cx ly' S' W' regs' mem' md' e SETTLE_STK ly3 S3 W3 regs3 mem3 md3 e LAWS HB HC HJ3
    Hfr3 Hperm3 PP3).
  - rewrite ESS. unfold ACfn.LLVMF_STK. lia.
  - intros a Ha Hw. apply KS3; [exact Ha | rewrite <- ESS; exact Hw].
  - exact KB3.
  - exact KF3. }
assert (HSP3 : lc_spills cx (lf_spill_loop (lc_F cx)) (aview segs (w_H W3) mem3)).
{ apply (lc_spills_kept cx _ (aview segs (w_H W') mem') _); [| | exact HSP].
  - intros o Ho. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES in *; lia)) as V.
    rewrite Forall_forall in V. destruct (V o Ho) as (_ & _ & Ho1 & Ho2). lia.
  - intros a Ha. apply KS3; [unfold LF_FRAME in *; lia | lia]. }
assert (HFSH3 : lc_fsh cx (aview segs (w_H W3) mem3) true false).
{ apply (lc_fsh_kept cx (aview segs (w_H W') mem') _ true false); [|exact HFSH].
  intros a Ha. apply KF3. right. exact Ha. }
assert (HTW3 : tw_at TMAP_A (aview segs (w_H W3) mem3) Bw)
  by exact (tw_kept_GA _ _ Bw HTWc (gx_kept_rows segs TG.G_HARNESS W' (ms_mem ms1) W3 mem3 HGK3)).
assert (T18 : YK11.getr regs3 (Z_to_bv 5 18) = w64 (lc_SH cx))
  by (rewrite (PP3 18 ltac:(unfold acallee_saved; lia)); exact R18').
clear HS SHOK1 HEI1 HTWc KA1 KS3 KB3 KF3 HSP HFSH HTW.
(* ---- +0x12d0 .. +0x12e8: a0 = -8, the four shadow stores, s8 = s3, s6 = 7 ---- *)
pose proof (lc_geom B MT XL RLO RHI cx ly3 S3 W3 regs3 mem3 md3 e HB HC3) as GEO3.
destruct GEO3 as [HAR3 _ _ _ FA3 HFin3 _ HINg3 _].
assert (Hpres3 : forall a, lc_SH cx + 4 <= a < lc_SH cx + 8 -> apresent (w_H W3) mem3 a).
{ intros a Ha. apply (apresent_of_aview segs); [unfold SHADOW_OFF in *; lia | |].
  - intros Hi. pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd, SHADOW_OFF in *. lia.
  - replace a with (lc_SH cx + (a - lc_SH cx)) by lia.
    rewrite (HFSH3 (a - lc_SH cx) ltac:(lia)). discriminate. }
pose proof (@op_entry2 (l_fx cx) rc W3 regs3 mem3 (lc_SH cx) T18 HSHlo ltac:(lia) Hpres3) as HS.
assert (HEI2 : img_env VAL A_LIM (op_E regs3)) by apply op_env_img.
assert (SHOK2 : sh_ok segs OP_Bx (@nil shent) (op_E regs3) (mrestrict (w_H W3) mem3)) by constructor.
assert (U18 : bv_unsigned (ew (op_E regs3) 18) = lc_SH cx)
  by (rewrite (op_ew_reg regs3 18 (Z_to_bv 5 18) eq_refl), T18; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
change (Z_to_bv 64 (BASE + 4816)) with (Z_to_bv 64 (BASE + OP_RET)).
paj_run_to_tok RUNTO HS HJ3 SHOK2 OP_B0 (AF_LLVMFuzzerTestOneInput + LO_TAIL).
{ op_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ LF_CID (l_fpos cx)); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U18 in Ha.
  right. unfold in_zr. cbn [fst snd]. rewrite FA3. change (fs_frame_bytes LF_CID / 8) with 32.
  unfold lc_SH in Ha. unfold shadow_addr. lia. }
op_after.
lazymatch type of HS with context [restrict _ ?m] => rename m into ms2 end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md4 end.
(* the run wrote the four shadow bytes only *)
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_SH cx + 4 <= a < lc_SH cx + 8) ->
  aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn0. apply (kept_of_frame _ _ _ _ _ (fun x => lc_SH cx + 4 <= x < lc_SH cx + 8) HFr);
    [| exact Ha | exact Hn0].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U18 in Hx; lia |]).
  destruct Hin. }
(* what they hold: 0xf8 *)
op_region HS 0%nat HR.
destruct HR as (_ & _ & _ & HCH).
apply Forall_cons_iff in HCH as [H7 HCH]. apply Forall_cons_iff in HCH as [H6 HCH].
apply Forall_cons_iff in HCH as [H5 HCH]. apply Forall_cons_iff in HCH as [H4 _].
apply op_byte_view in H7, H6, H5, H4. cbn [YP09.r_base base_val] in H7, H6, H5, H4. rewrite U18 in H7, H6, H5, H4.
clear HF HFr HG.
(* the registers at TAIL *)
op_reg HS (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) G2 ltac:(op_kept_tac regs3 2%nat 2).
op_reg HS (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) G3 ltac:(op_kept_tac regs3 3%nat 3).
op_reg HS (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) G4 ltac:(op_kept_tac regs3 4%nat 4).
op_reg HS (Z_to_bv 5 8) (YK11.getr regs3 (Z_to_bv 5 8)) G8 ltac:(op_kept_tac regs3 8%nat 8).
op_reg HS (Z_to_bv 5 9) (YK11.getr regs3 (Z_to_bv 5 9)) G9 ltac:(op_kept_tac regs3 9%nat 9).
op_reg HS (Z_to_bv 5 18) (YK11.getr regs3 (Z_to_bv 5 18)) G18 ltac:(op_kept_tac regs3 18%nat 18).
op_reg HS (Z_to_bv 5 20) (YK11.getr regs3 (Z_to_bv 5 20)) G20 ltac:(op_kept_tac regs3 20%nat 20).
op_reg HS (Z_to_bv 5 21) (YK11.getr regs3 (Z_to_bv 5 21)) G21 ltac:(op_kept_tac regs3 21%nat 21).
op_reg HS (Z_to_bv 5 23) (YK11.getr regs3 (Z_to_bv 5 23)) G23 ltac:(op_kept_tac regs3 23%nat 23).
op_reg HS (Z_to_bv 5 26) (YK11.getr regs3 (Z_to_bv 5 26)) G26 ltac:(op_kept_tac regs3 26%nat 26).
op_reg HS (Z_to_bv 5 24) (YK11.getr regs3 (Z_to_bv 5 19)) G24 ltac:(op_kept_tac regs3 19%nat 19).
op_reg HS (Z_to_bv 5 22) (w64 7) G22 ltac:(reflexivity).
pmkst HS.
clear HS SHOK2 HEI2.
(* the frame and the blocks hold no byte the run wrote *)
assert (HFsh : forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> ~ (lc_SH cx + 4 <= a < lc_SH cx + 8)).
{ intros a Ha Hs. destruct (frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 LF_CID (l_fpos cx) HAR3 HFin3)
    as (_ & _ & Happ).
  rewrite FA3, lf_fbytes in Happ. unfold lc_SH in Hs. unfold LF_FBYTES in *.
  destruct Happ as [Hp1 [Hp2 | [Hp2 Hp3]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia. }
assert (HBsh : forall b m i, In (b, m) (ablocks B ly3 S3) -> 0 <= i < req_size m ->
  aview segs (w_H W3) (ms_mem ms2) (b + i) = aview segs (w_H W3) mem3 (b + i)).
{ intros b m i Hb Hi.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 b m HAR3 Hb) as (_ & Hb4096 & Hbce & _).
  apply KR2; [lia|]. intros Hs.
  apply (op_blk_sh ly3 S3 W3 mem3 md3 b m LF_CID (l_fpos cx) (b + i) LAWS HAR3 Hb HFin3); [|lia].
  rewrite FA3. change (fs_frame_bytes LF_CID / 8) with 32. unfold lc_SH in Hs. unfold shadow_addr. lia. }
assert (KHI : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 ->
  aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) mem3 a).
{ intros a Ha. apply KR2; [lia|]. unfold SHADOW_OFF in *. lia. }
(* the core at TAIL: the journal of the run, the rest carried from the core after the call *)
assert (HC4 : lc_core B cx ly3 S3 W3 (ms_regs ms2) (ms_mem ms2) md4 e).
{ pose proof HC3 as (_ & Hfrs3 & HlyF3 & HPERM3 & Rsp3 & R8_3 & R9_3 & Rgp3 & Rtp3 & Hsp1_3 & Hsp1al3 & HSAV3 &
    HF4096_3 & HFal3 & HFceil3 & HFpres3 & HFL3 & HIN3).
  refine (conj HJ3 (conj Hfrs3 (conj HlyF3 (conj HPERM3 (conj (eq_trans G2 Rsp3) (conj (eq_trans G8 R8_3)
    (conj (eq_trans G9 R9_3) (conj (eq_trans G3 Rgp3) (conj (eq_trans G4 Rtp3) (conj Hsp1_3 (conj Hsp1al3
    (conj _ (conj HF4096_3 (conj HFal3 (conj HFceil3 (conj _ (conj _ _))))))))))))))))).
  - unfold lc_saved in HSAV3 |- *. rewrite Forall_forall in HSAV3 |- *. intros o Ho. cbv beta.
    assert (Hor : 8 <= fst o <= 104).
    { unfold LF_SAVED in Ho. repeat (destruct Ho as [<- | Ho]; [cbn; lia|]). destruct Ho. }
    pose proof (HSAV3 o Ho) as Hs. cbv beta in Hs. rewrite <- Hs.
    apply rdword_ext. intros j Hj. apply KHI. unfold LF_FRAME in *. lia.
  - intros a Ha. apply (apresent_transfer segs (w_H W3) (w_H W3) mem3 (ms_mem ms2) a).
    + unfold LF_FBYTES in *. lia.
    + apply (frm_img segs B LAWS ly3 S3 W3 mem3 md3 LF_CID (l_fpos cx) a HAR3 HFin3).
      rewrite FA3, lf_fbytes. exact Ha.
    + apply KR2; [unfold LF_FBYTES in *; lia | exact (HFsh a Ha)].
    + exact (HFpres3 a Ha).
  - rewrite <- HFL3. apply rdword_ext. intros j Hj.
    apply KR2; [unfold LF_FBYTES in *; lia | apply HFsh; unfold LF_FBYTES in *; lia].
  - destruct HIN3 as (HPAYg & HPAYv).
    destruct (Z_lt_le_dec 0 (l_n cx)) as [Hn0 | Hn0].
    + pose proof (HINg3 Hn0) as InP.
      pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
      split.
      * apply (lc_garr8_kept (w_H W3) (w_H W3) mem3 (ms_mem ms2) (l_p cx) _); [|exact HPAYg].
        intros j Hj. rewrite length_map in Hj. destruct Hn as (_ & Hnl). rewrite <- Hnl in Hj.
        exact (HBsh _ _ j InP ltac:(lia)).
      * intros i Hi. exact (eq_trans (HBsh _ _ i InP ltac:(lia)) (HPAYv i Hi)).
    + destruct Hn as (Hn1 & Hnl). split.
      * destruct (l_pl cx) as [|b0 pl0] eqn:Epl; [apply garr8_nil|]. exfalso. cbn [length] in Hnl. lia.
      * intros i Hi. lia. }
(* the frame's shadow: c out of scope *)
assert (HFSH4 : lc_fsh cx (aview segs (w_H W3) (ms_mem ms2)) false false).
{ intros i Hi.
  assert (Hc : (0 <= i < 4 \/ 8 <= i < 32) \/ (i = 4 \/ i = 5 \/ i = 6 \/ i = 7)) by lia.
  destruct Hc as [Hout | Hin].
  - rewrite (KR2 (lc_SH cx + i) ltac:(unfold SHADOW_OFF in *; lia) ltac:(lia)), (HFSH3 i Hi).
    rewrite (op_shm_out (Z.to_nat i) ltac:(lia) ltac:(lia)). reflexivity.
  - rewrite (op_shm_in (Z.to_nat i) ltac:(lia)).
    destruct Hin as [-> | [-> | [-> | ->]]];
      [refine (eq_trans H4 _) | refine (eq_trans H5 _) | refine (eq_trans H6 _) | refine (eq_trans H7 _)];
      vm_compute; reflexivity. }
assert (HSP4 : lc_spills cx (lf_spill_loop (lc_F cx)) (aview segs (w_H W3) (ms_mem ms2))).
{ apply (lc_spills_kept cx _ (aview segs (w_H W3) mem3) _); [| | exact HSP3].
  - intros o Ho. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES in *; lia)) as V.
    rewrite Forall_forall in V. destruct (V o Ho) as (_ & _ & Ho1 & Ho2). lia.
  - intros a Ha. apply KHI. unfold LF_FRAME in *. lia. }
assert (HTW4 : tw_at TMAP_A (aview segs (w_H W3) (ms_mem ms2)) Bw).
{ apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact HTW3|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR2; [lia | unfold SHADOW_OFF in *; lia]. }
(* the meter: settle charged nothing *)
assert (HMT4 : lc_meter MT cx S3 (Z.of_nat (lo_k op))).
{ destruct HMT as (Hle & Hok). split.
  - pose proof (mo_le_trans MT MTL _ _ _ _ _ Hle HMO3) as H. rewrite Z.add_0_r in H. exact H.
  - apply (mo_ok_step MT MTL S' S3 0 _); [rewrite Z.add_0_l; exact Hok | exact HMO3]. }
(* ---- TAIL ---- *)
apply SRr_ret.
exists ly3, S3, (ms_regs ms2), (ms_mem ms2), md4, e, 4096, Bw, c5, (lo_k op).
split; [unfold lc_cfg; rewrite ?HBASE; reflexivity|].
split.
{ refine (conj HC4 (conj (conj _ _) (conj HSP4 (conj HFSH4 (conj HOK (conj He (conj HMT4 _))))))).
  - exact (eq_trans G18 T18).
  - exact (eq_trans G26 (eq_trans (PP3 26 ltac:(unfold acallee_saved; lia)) R26')).
  - exact (eq_trans G21 (eq_trans (PP3 21 ltac:(unfold acallee_saved; lia)) R21')). }
split; [unfold recv_addr_ok; split; [lia | vm_compute; discriminate]|].
split; [exact (HOP (fun _ => 4096))|].
split; [exact HTW4|].
split; [split|].
- exact (eq_trans G24 (eq_trans (PP3 19 ltac:(unfold acallee_saved; lia)) R19)).
- exact (eq_trans G23 (eq_trans (PP3 23 ltac:(unfold acallee_saved; lia)) R23)).
- split; [exact (eq_trans G20 (eq_trans (PP3 20 ltac:(unfold acallee_saved; lia)) R20')) | exact G22].
Qed.

End s.
