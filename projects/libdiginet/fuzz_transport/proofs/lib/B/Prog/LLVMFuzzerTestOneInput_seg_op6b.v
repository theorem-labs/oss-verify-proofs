(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 465 of its 520 lines of code are new or changed and 504 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op6b: Lemma lc_op6b_ok : lc_op6b_stmt (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v),
   the segment OP6B of the image-B walk of LLVMFuzzerTestOneInput, offsets +0x8ec .. +0x8fc of the listing
   lib/B/Prog/DgnTransportBList.v (0x81b8c .. 0x81b9c), from the cut CLS (+0x8ec) to the cut SET56 (+0x900).

   What the code does. +0x8ec `ld a0, 0x98(s1)`: the spill slot the prologue wrote with g_now's page
   (lf_spill_scal, transportb_hi 9). +0x8f0 `ld a1, 0x68c(a0)`: the plain 8-byte load of g_now, whose payload is a
   range of G, so the world relation of the cut gives its bytes. +0x8f4 and +0x8f8: the two words that form
   a0 = the listing's object 9 = g_s's base (TWorldB.v TB_g_s = diginet_session_close_cg.v CLOSE_S). +0x8fc
   `jal diginet_session_close` (0x87648), return address +0x900, which is the cut SET56. No instrumented check and no
   store is on this path, so no __asan_report_* call is reachable here.

   diginet_session_close is a G-form callee composed in the same G journal: its statement
   lib/B/Prog/diginet_session_close_cg.v transport_diginet_session_close_cg is a premise of the walk (lp_close).
   The walk calls it with TF = None, so its trans_tframe_at, close_apart and trans_tf_off_g premises hold
   vacuously. Every byte it stores is a byte of G (l6_close_wr_G: send_control's sendctl_wr 0 0 through io_send's
   iosend_wr field by field, the two g_s fields, notice's stores by TransportGNoticeB.v notice_wr_G), hence an image
   byte below the low memory end, apart from the caller's blocks and its class-2 frame (both outside the image) and
   from that frame's shadow bytes (at or above SHADOW_OFF). What the call keeps therefore carries the cut's core
   (LLVMFuzzerTestOneInput_st.v lc_core_kept), its spill slots (lc_spills_kept) and the frame's 32 shadow bytes
   (lc_fsh_kept), and its callee-saved registers carry the cut's register facts (s2, s3, s4, s6, s8, s10, s11).

   The model. At op code 6 the operation is op_begin, m_close, diginet_session_close and settle (st.v lc_op6_eq).
   TSim/LoopOk.v op_ok at the start facts of the cut (lc_opok) says the whole chain answers Some; that names the
   world B3 the call leaves and gives settle_m B3 0 = Some (B3, tt) (st.v lc_settle_world), which is what SET56
   carries. The operation's result does not read the stream, so the equation holds at every stream.

   The two run invariants diginet_session_close asks at B2, the world of m_close, come from the kit statement K6
   at the start world through TModel/TRunInv.v rk: op_begin writes OW, GOT and M.fail and m_close writes OW.e3,
   M.fail, M.state, OW.t[] and OW.n, none of which run_inv reads, and M.fly.on, which m_close only sets to 0
   (rk_fly_off). g_fail_next B2 = g_fail_next of the start world by TModel/TIoRecv.v gkeep (no write of either
   step reaches that byte), so K6's g_fail_next <= 1 carries too. The class-2 count: the cut holds one class-2
   frame, and 1 + 1 < fs_frames 2. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0 YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg check_state_data_cg notice_cg io_send_cg send_control_cg set_state_cg TransportGNoticeB receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_close_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TRunInv TIoRecv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TImg TCb TSess0 TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module TRI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TRunInv.
Module TIR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TIoRecv.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module LOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LoopOk.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The written range of diginet_session_close                          *)
(* ------------------------------------------------------------------ *)

(* A byte inside a row of G is a byte of G. *)
Lemma l6_inG_row : forall b n a, In (b, n) TG.G_HARNESS_B -> b <= a < b + n -> inG TG.G_HARNESS_B a.
Proof.
  intros b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn; lia].
Qed.

(* A byte of a field of the TMAP_B row (o, b, n), inside the row. *)
Lemma l6_fld_G : forall o b n A w a, In (o, b, n) TMAP_B -> twb_fld o b A w a -> o <= A -> A + w <= o + n ->
  inG TG.G_HARNESS_B a.
Proof.
  intros o b n A w a Hin Ha H1 H2. apply (l6_inG_row b n a (TMAP_B_in_G o b n Hin)).
  unfold twb_fld in Ha. lia.
Qed.

(* The side conditions of l6_fld_G: closed ones by computation (l6_cz), the one with a variable index by lia over
   the unfolded offsets (l6_czl). *)
Ltac l6_cz := apply Z.leb_le; vm_compute; reflexivity.
Ltac l6_czl :=
  unfold TW.A_Cmd_st, TW.OFF_g_cmd, TW.SZ_g_cmd, TW.A_GOT_t_state, TW.GOT_t_ESZ, TW.OFF_GOT, TW.SZ_GOT,
    TC.CMDS_MAX, TC.TRANS_MAX in *; lia.

(* io_send's stores (iosend_wr n), field by field, for any n. *)
Lemma l6_iosend_wr_G : forall n a, iosend_wr n a -> inG TG.G_HARNESS_B a.
Proof.
  intros n a H. unfold iosend_wr in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]].
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_g_fail_next H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_GOT H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_GOT H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_GOT H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_g_last_counter H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_M H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_M H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_M H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_M H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_M H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_M H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_M H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_M H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_M H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_M H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_M H); [l6_cz|].
    pose proof (Z.le_min_r n TC.SPEC_MAX_FRAME) as Hm.
    assert (C : TW.A_M_fly_frame + TC.SPEC_MAX_FRAME <= TW.OFF_M + TW.SZ_M) by l6_cz.
    lia.
  - destruct H as (s & Hs & H). apply (l6_fld_G _ _ _ _ _ a TMAP_B_g_cmd H); l6_czl.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_g_q H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_g_nq H); l6_cz.
Qed.

(* send_control's stores with kp = klp = 0. *)
Lemma l6_sendctl_wr_G : forall a, sendctl_wr 0 0 a -> inG TG.G_HARNESS_B a.
Proof.
  intros a H. unfold sendctl_wr in H. destruct H as [H | [H | (H & _)]].
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_g_s H); l6_cz.
  - exact (l6_iosend_wr_G _ a H).
  - exfalso. exact (H eq_refl).
Qed.

(* Every byte the call stores is a byte of G. *)
Lemma l6_close_wr_G : forall (F : option TI.tframe) Bw a, close_wr F Bw a -> inG TG.G_HARNESS_B a.
Proof.
  intros F Bw a H. unfold close_wr in H. destruct H as [(_ & H) | [H | (B1 & r & _ & _ & [H | H])]].
  - exact (l6_sendctl_wr_G a H).
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_g_s H); l6_cz.
  - apply (l6_fld_G _ _ _ _ _ a TMAP_B_g_s H); l6_cz.
  - exact (notice_wr_G (close_w2 B1) (close_ntc B1) a H).
Qed.

(* So it is an image byte, below the low memory end. *)
Lemma l6_wr_img : forall (F : option TI.tframe) Bw a, close_wr F Bw a -> in_img tfibsegs a.
Proof. intros F Bw a H. exact (trans_g_img a (l6_close_wr_G F Bw a H)). Qed.
Lemma l6_wr_low : forall (F : option TI.tframe) Bw a, close_wr F Bw a -> 0 <= a < kLowMemEnd.
Proof. intros F Bw a H. exact (transportb_segs_low a (l6_wr_img F Bw a H)). Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the cut                                       *)
(* ------------------------------------------------------------------ *)

(* The two memory ranges the run reads: the spill slot at s1 + 152 (atom 9 is s1), which holds g_now's page, and
   g_now's own 8 payload bytes at the absolute address TB_g_now, whose value is the extra atom 32. The run writes
   no byte, so both windows are empty. *)
Definition l6_rg_spill : YP09.region :=
  YP09.mkRegion (Some 9%nat) 152 160 0 0 [YP09.mkChunk 152 (YP09.CVal 8 (SLit (transportb_hi 9)))].
Definition l6_rg_now : YP09.region :=
  YP09.mkRegion None TB_g_now (TB_g_now + 8) 0 0 [YP09.mkChunk TB_g_now (YP09.CVal 8 (SOff 32 0))].
Definition l6_regions : smem := [l6_rg_spill; l6_rg_now].
Definition l6_facts : facts := mkFacts [] [] [].
Definition l6_ss : sstate := mkSS LO_CLS sr_atoms l6_regions None l6_facts.
Definition L6_B0 : Z * Z := (0, 0).
Definition L6_Bx : sv := SLit 0.
(* The spill slot's value and the address the second load forms from it. *)
Lemma l6_page : transportb_hi 9 = 0x5de6f4 /\ transportb_hi 9 + 0x68c = TB_g_now /\ TB_g_s = CLOSE_S.
Proof. repeat split; reflexivity. Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac l6_reg HS r v H tac :=
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
(* The write right of a run from a state whose two regions have no write window. *)
Ltac l6_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
          [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; exfalso; lia |]);
  apply awr_ok_x_nil.
(* A run from a state with no write window writes no byte. *)
Ltac l6_kept HFr KR W mold msn :=
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msn) a = aview tfibsegs (w_H W) mold a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    apply (YC4b.kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []];
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [Hin | Hin];
            [ inversion Hin; subst; cbn [base_val] in Hx; exfalso; lia |]);
    destruct Hin
  | ].
(* A range, from an index in it (plain arithmetic: the kit's lia prunes a hypothesis that holds req_size). *)
Lemma l6_rng : forall b i n : Z, 0 <= i < n -> b <= b + i < b + n.
Proof. intros b i n H. lia. Qed.

(* The frame's bytes and its shadow bytes are addresses (the shadow of a frame below the ceiling is below 2 ^ 64):
   the quotient is named, since the kit's lia drops a hypothesis that holds a division. *)
Lemma l6_addr_rng : forall F a c, 4096 <= F -> F + 256 <= c -> c <= 140737479966720 ->
  (F <= a < F + 256 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 32) -> 0 <= a < 2 ^ 64.
Proof.
intros F a c H0 H1 H2 Ha.
assert (HFc : F <= 140737479966720) by lia.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as D0.
pose proof (Z.div_le_mono F 140737479966720 8 ltac:(lia) HFc) as D1.
change (140737479966720 / 8) with 17592184995840 in D1.
remember (F / 8) as q eqn:Eq. clear Eq.
unfold SHADOW_OFF in *. change (2 ^ 64) with 18446744073709551616.
destruct Ha as [Ha | Ha]; lia.
Qed.

(* A shadow byte of the frame is not below the low memory end, where every byte the call stores lies. *)
Lemma l6_sh_low : forall F a, 0 <= F -> SHADOW_OFF + F / 8 <= a -> a < kLowMemEnd -> False.
Proof.
intros F a H0 H1 H2. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as D0.
remember (F / 8) as q eqn:Eq. clear Eq.
unfold SHADOW_OFF, kLowMemEnd in *. lia.
Qed.

Section seg6b. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The walk's valuation: the 32 registers at the cut and the one value it loads, g_now of the cut's world. *)
Definition l6_E (regs : bvmap 5 word) (nw : Z) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 nw]).

Lemma l6_ew_reg : forall regs nw n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (l6_E regs nw) n = YK11.getr regs r.
Proof. intros regs nw n r Hn. unfold l6_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma l6_env_img : forall regs nw, img_env VAL A_LIM (l6_E regs nw).
Proof. intros regs nw. unfold l6_E. apply Eimg_env. Qed.
Lemma l6_ew_now : forall regs nw, ew (l6_E regs nw) 32 = w64 nw.
Proof.
  intros regs nw. unfold l6_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs [w64 nw] 0%nat).
Qed.
Lemma l6_base_now : BASE = transportb_text /\ VAL (A_OBJ 9) = TB_g_s.
Proof. split; vm_compute; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The model side: the run invariants and g_fail_next at m_close's world *)
(* ------------------------------------------------------------------ *)

(* op_begin's two block writes, as lengths. *)
Lemma l6_zow : Z.of_nat (Z.to_nat TW.SZ_OW) = 304 /\ Z.of_nat (Z.to_nat TW.SZ_GOT) = 224.
Proof. split; reflexivity. Qed.

Local Ltac l6_rside :=
  rewrite ?repeat_length, ?TWL.length_put, ?(proj1 l6_zow), ?(proj2 l6_zow); ri_num; lia.

(* op_begin (TCb.v:388-394) and m_close (:378-386) keep TRunInv.v rk: no byte they write is read by run_inv,
   but M.fly.on, which m_close only sets to 0. *)
Lemma l6_rk : forall (B0 B1 B2 : list byte), length B0 = Z.to_nat TW.W_LEN ->
  TC.op_begin_m B0 = Some (B1, tt) -> TC.m_close_m B1 = Some (B2, tt) -> rk B0 B2.
Proof.
intros B0 B1 B2 LB Hbeg Hcls.
assert (RK1 : rk B0 B1).
{ unfold TC.op_begin_m in Hbeg. cbv zeta in Hbeg.
  apply TIR.some_pair_inv in Hbeg as [EB1 _]. rewrite <- EB1. clear EB1.
  ri_set.
  repeat (apply (rk_upd _ _ _ _ LB); [| l6_rside | l6_rside | l6_rside ]).
  apply rk_refl. }
unfold TC.m_close_m in Hcls. cbv zeta in Hcls. gk_split Hcls.
all: eapply (m_set_rk B0 LB); [| exact Hcls]; ri_set; rk_go.
Qed.

Local Ltac l6_gside :=
  rewrite ?repeat_length, ?TWL.length_put, ?(proj1 l6_zow), ?(proj2 l6_zow);
  unfold TW.A_M_fail, TW.A_M_fly_on, TW.A_OW_desk_off, TW.A_OW_e3, TW.OFF_M, TW.OFF_OW, TW.OFF_GOT,
    TW.OFF_g_fail_next, TW.W_LEN, TW.SZ_OW, TW.SZ_GOT;
  lia.

(* Neither step writes g_fail_next (TIoRecv.v gkeep). *)
Lemma l6_gk : forall (B0 B1 B2 : list byte), length B0 = Z.to_nat TW.W_LEN ->
  TC.op_begin_m B0 = Some (B1, tt) -> TC.m_close_m B1 = Some (B2, tt) -> TIR.gkeep B0 B2.
Proof.
intros B0 B1 B2 LB Hbeg Hcls.
assert (LB' : Z.of_nat (length B0) = TW.W_LEN) by (rewrite LB; reflexivity).
assert (GK1 : TIR.gkeep B0 B1).
{ unfold TC.op_begin_m in Hbeg. cbv zeta in Hbeg.
  apply TIR.some_pair_inv in Hbeg as [EB1 _]. rewrite <- EB1. clear EB1.
  gk_setters.
  repeat (apply TIR.gkeep_upd; [| l6_gside | rewrite LB'; l6_gside | l6_gside ]).
  apply TIR.gkeep_refl. }
unfold TC.m_close_m in Hcls. cbv zeta in Hcls. gk_split Hcls.
all: eapply (TIR.m_set_gk B0 LB); [| exact Hcls]; gk_setters;
     repeat (apply TIR.gkeep_upd; [| l6_gside | rewrite LB'; l6_gside | l6_gside ]);
     exact GK1.
Qed.

(* ------------------------------------------------------------------ *)
(* The segment                                                         *)
(* ------------------------------------------------------------------ *)

Lemma lc_op6b_ok (K1 : lc_rom_view_stmt B MT XL RLO RHI) (K6 : lc_runinv_stmt) : lc_op6b_stmt B MT XL RLO RHI.
Proof.
unfold lc_op6b_stmt. intros HP cx op W c HB HCLS.
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (lp_meter_laws B MT XL RLO RHI HP) as MTL.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
destruct HCLS as (ly1 & S1 & regs1 & mem1 & md1 & e1 & B1 & B2 & Hc & Hopc & HL & Hbeg & Hcls & Htw & Hcur & R20 & R22).
subst c.
pose proof HL as (HC & HFR & HSPL & HFSH & HOPOK & HEV & HMO & R19).
pose proof HOPOK as (HAG & HOPS & HFIO & HFN & HKOP).
pose proof (@lc_geom rc B MT XL RLO RHI cx ly1 S1 W regs1 mem1 md1 e1 HB HC) as GEO.
destruct GEO as [HARc Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof HFR as (R18 & R26).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
change (2 ^ 47) with 140737488355328 in H47.
pose proof asan_consts as ((CVlo & CVhi) & _).
(* the slot's event budget *)
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
(* ---- geometry, as closed arithmetic ---- *)
assert (HSTKFIT : CLOSE_STK + 336 <= LLVMF_STK) by (vm_compute; intros Hx; discriminate Hx).
assert (HCEV : CLOSE_EV = 0) by reflexivity.
assert (Hsp1lo : alloc_ceiling + 32432 <= lc_sp1 cx) by exact Hsp1c.
assert (Hsp1hi : lc_sp1 cx <= lc_sp0 cx) by (unfold LF_FRAME in Hsp1; lia).
assert (Hsp0hi : lc_sp0 cx <= 2 ^ 47) by (unfold lc_sp0 in *; lia).
assert (Hsp1rg : 0 <= lc_sp1 cx < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
(* ---- the model: the operation's chain answers Some ---- *)
assert (LB : length (lo_B op) = Z.to_nat TW.W_LEN) by exact (AG.ac_len _ _ _ (AG.ag_core _ _ _ HAG)).
destruct (LOK.op_ok LP.links_holds timg_B (lo_ops op) (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op)
  HAG HOPS HFIO HFN ltac:(lia) ltac:(change (2 ^ 64) with 18446744073709551616; lia))
  as (Bz & cz & kz & EQ0 & _ & _).
rewrite (lc_op6_eq timg_B (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op) Hopc) in EQ0.
rewrite Hbeg in EQ0. cbv beta iota in EQ0. rewrite Hcls in EQ0. cbv beta iota in EQ0.
destruct (TSS.diginet_session_close_m timg_B None B2 (TW.g_now B2)) as [[B3 r3]|] eqn:ECL;
  cbv beta iota in EQ0; [|discriminate EQ0].
destruct (TC.settle_m B3 0) as [[B4 u4]|] eqn:ESET0; cbv beta iota in EQ0; [|discriminate EQ0].
pose proof (lc_settle_world B3 B4 0 u4 ESET0) as EB4. subst B4.
assert (ESET : TC.settle_m B3 0 = Some (B3, tt)) by (destruct u4; exact ESET0).
clear EQ0 Bz cz kz ESET0.
(* the operation's equation at every stream *)
assert (EQOP : forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_B (lo_B op) A (l_pl cx) (lo_c op) (lo_k op) =
                 Some (B3, (lc_oc (l_pl cx) (lo_c op), lo_k op))).
{ intros A. rewrite (lc_op6_eq timg_B (lo_B op) A (l_pl cx) (lo_c op) (lo_k op) Hopc).
  rewrite Hbeg. cbv beta iota. rewrite Hcls. cbv beta iota. rewrite ECL. cbv beta iota.
  rewrite ESET. reflexivity. }
(* ---- the run invariants at m_close's world ---- *)
destruct (K6 (lo_ops op) (lo_B op) HAG) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8).
assert (RI0 : run_inv (lo_B op)).
{ unfold run_inv. split; [exact I1|]. split; [exact I2|]. split; [exact I4|].
  split; [exact I6|]. split; [exact I7|]. split; [exact I5 | exact I3]. }
destruct (rk_out (lo_B op) B2 LB RI0 (l6_rk (lo_B op) B1 B2 LB Hbeg Hcls)) as (LB2 & RI2).
destruct RI2 as (HINV1 & _ & HINV4 & _).
assert (HGFN : TW.g_fail_next B2 <= 1)
  by (rewrite (proj2 (l6_gk (lo_B op) B1 B2 LB Hbeg Hcls)); exact I8).
(* ---- the symbolic state at the cut ---- *)
set (nw := TW.g_now B2) in *.
set (E := l6_E regs1 nw) in *.
assert (HEI : img_env VAL A_LIM E) by apply l6_env_img.
assert (EWR : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs1 r)
  by (intros nx rx Hnx; apply l6_ew_reg; exact Hnx).
assert (E9 : ew E 9 = YK11.getr regs1 9) by (apply l6_ew_reg; reflexivity).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; lia).
assert (RNW : 0 <= nw < 2 ^ 64).
{ unfold nw, TW.g_now. pose proof (TWL.u_at_range B2 TW.OFF_g_now 8) as Hr.
  change (8 * Z.of_nat 8) with 64 in Hr. lia. }
assert (ENW : ew E 32 = w64 nw) by apply l6_ew_now.
assert (RPG : 0 <= transportb_hi 9 < 2 ^ 64) by (rewrite (proj1 l6_page); lia).
assert (HSP152 : rdword (aview segs (w_H W) mem1) (lc_sp1 cx + 152) = Some (transportb_hi 9)).
{ unfold lc_spills in HSPL. rewrite Forall_forall in HSPL.
  exact (HSPL (152, transportb_hi 9) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm;
    cbn [app In]; repeat first [left; reflexivity | right])). }
assert (HNOWB : val_mem segs (mrestrict (w_H W) mem1) (0 + TB_g_now) 8 nw).
{ pose proof (tw_read_val segs _ TMAP_B B2 TW.OFF_g_now TB_g_now TW.SZ_g_now 0 8 TMAP_B_ok Htw
    TMAP_B_g_now ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)) as Hv.
  rewrite !Z.add_0_r in Hv. rewrite Z.add_0_l. exact Hv. }
assert (HS : st_ok_pi (fx := l_fx cx) segs VAL E l6_ss
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs1 (Z_to_bv 64 (BASE + LO_CLS)) mem1 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold l6_ss.
  apply (@pa_entry_st_ok_full (l_fx cx) rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold l6_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold l6_rg_spill, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (lc_sp1 cx) 152 8 (SLit (transportb_hi 9)) (transportb_hi 9));
        [reflexivity | change (8 * Z.of_N 8) with 64; exact RPG | cbn; lia |].
      eapply val_mem_of_rdword. exact HSP152.
    + unfold l6_rg_now, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [unfold TB_g_now; lia|]. split; [unfold TB_g_now; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 TB_g_now 8 (SOff 32 0) nw);
        [ cbn [sv_denot]; rewrite ENW, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; exact RNW | cbn; lia |].
      exact HNOWB.
  - unfold l6_regions, l6_rg_spill, l6_rg_now.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9. unfold TB_g_now. lia.
  - unfold l6_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    repeat split; exact I. }
assert (SHOK : sh_ok segs L6_Bx (@nil shent) E (mrestrict (w_H W) mem1)) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs1 (Z_to_bv 64 (BASE + LO_CLS)) mem1
    (YK11.seg_rom segs)) md1) Q) end.
(* ---- +0x8ec .. +0x8fc: the two loads, a0 = &g_s, and the call ---- *)
paj_run_tok RUN HS HJ SHOK L6_B0.
{ l6_awr. }
l6_kept HFr KR W mem1 ms.
clear HF HFr HG.
(* the callee-saved registers are the cut's *)
assert (HPRE : aregs_preserved regs1 (ms_regs ms)).
{ intros r Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  repeat (destruct Hr' as [-> | Hr']); try (subst r).
  all: lazymatch goal with
       | |- YK11.getr _ (Z_to_bv 5 ?n) = _ =>
         let Q := fresh "Q" in
         l6_reg HS (Z_to_bv 5 n) (YK11.getr regs1 (Z_to_bv 5 n)) Q
           ltac:(let m := eval vm_compute in (Z.to_nat n) in
                 cbn [sv_denot]; rewrite (EWR m (Z_to_bv 5 n) eq_refl), Z.add_0_r,
                 Z_to_bv_bv_unsigned; reflexivity);
         exact Q
       end. }
(* the call's arguments and its return address *)
l6_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LO_SET56)) Q1 ltac:(apply codeptr_val; exact HEI).
(* a0 is the image atom of object 9: its value through img_env, then a closed computation *)
l6_reg HS (10%bv : bv 5) (w64 CLOSE_S) Q10
  ltac:(cbn [sv_denot];
        lazymatch goal with |- context [ew E ?n] => rewrite (HEI n ltac:(unfold A_TEXT, A_LIM; lia)) end;
        vm_compute; reflexivity).
l6_reg HS (11%bv : bv 5) (w64 nw) Q11
  ltac:(cbn [sv_denot]; rewrite ENW, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Q2 : YK11.getr (ms_regs ms) 2 = w64 (lc_sp1 cx))
  by exact (eq_trans (HPRE 2 ltac:(hnf; lia)) Rsp).
assert (QSP : spZ (ms_regs ms) = lc_sp1 cx)
  by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
(* the world relation and the read-only bytes at the call memory *)
assert (TWc : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms)) B2).
{ apply (tw_kept TMAP_B (aview segs (w_H W) mem1)); [exact Htw|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
  apply KR. lia. }
assert (ROMc : trans_rom_view_rd W (ms_mem ms)).
{ intros a Ha. rewrite KR by (pose proof (trans_ro_rd_bounds a Ha); lia).
  exact (K1 HP cx ly1 S1 W regs1 mem1 md1 e1 HB HC a Ha). }
assert (HCNT : count_cid CLOSE_CID (frames S1) + 1 < fs_frames CLOSE_CID).
{ rewrite Hfrs. vm_compute. reflexivity. }
assert (EBR : BASE + LO_SET56 = 0x81ba0) by (vm_compute; reflexivity).
(* ---- +0x8fc: the call of diginet_session_close ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg
    (Z_to_bv 64 (transportb_sigma TB_diginet_session_close)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ eapply (lp_close B MT XL RLO RHI HP (l_fx cx)).
  - first [exact HJ | apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ].
  - rewrite Q1. apply (ret_ok_codeptr_v (PI := PI_transportb));
      [unfold LO_SET56; lia | reflexivity].
  - unfold raZ. rewrite Q1, EBR. rewrite unsigned_lit_small by lia. lia.
  - exact (eq_trans (HPRE 3 ltac:(hnf; lia)) Rgp).
  - exact (eq_trans (HPRE 4 ltac:(hnf; lia)) Rtp).
  - exact Q10.
  - exact Q11.
  - rewrite QSP. pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D1.
    rewrite Hsp1al, Z.add_0_r in D1. rewrite D1.
    replace (32 * (lc_sp1 cx / 32)) with ((2 * (lc_sp1 cx / 32)) * 16) by ring.
    apply Z.mod_mul. lia.
  - rewrite QSP. unfold LF_FRAME in Hsp1. lia.
  - rewrite QSP. lia.
  - exact RNW.
  - exact TWc.
  - exact HGFN.
  - exact ECL.
  - exact I.
  - exact ROMc.
  - intros x _ fr Hfr. discriminate Hfr.
  - intros fr Hfr. discriminate Hfr.
  - exact HINV1.
  - exact HINV4.
  - exact HCNT.
  - rewrite HCEV, Z.add_0_r. unfold RECV_EV in HEV. unfold EV_LIB in Hev.
    change TC.OPS_MAX with 1024 in HOPS. lia. }
cbv beta.
intros W3 c3 _ HPOST.
unfold transport_close_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & Ec3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
  (HA0 & HTW3 & HGF3)).
assert (Ee3 : e3 = 0) by (rewrite HCEV in He3; lia). subst e3. rewrite Z.add_0_r in HJ3.
rewrite Q1 in Ec3.
(* ---- the cut SET56 ---- *)
apply SRr_ret.
pose proof HK3 as (K31 & K32 & K33 & K34 & K35 & K36). rewrite QSP in K31.
(* the class-2 frame's bytes and its shadow bytes at the return: no byte of either is a byte the call stores *)
assert (KFR : forall a, lc_F cx <= a < lc_F cx + LF_FBYTES ->
  aview segs (@w_H segs W3) mem3 a = aview segs (w_H W) mem1 a).
{ intros a Ha.
  assert (HNW : ~ close_wr None B2 a).
  { intros Hx. exact (frm_img segs B LAWS ly1 S1 W mem1 md1 LF_CID (l_fpos cx) a HARc HFin
      ltac:(rewrite HFaddr; change (fs_frame_bytes LF_CID) with LF_FBYTES; exact Ha) (l6_wr_img None B2 a Hx)). }
  rewrite (K34 LF_CID (l_fpos cx) a HFin
    ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFaddr;
          change (fs_frame_bytes LF_CID) with LF_FBYTES; lia) HNW).
  apply KR. exact (l6_addr_rng (lc_F cx) a alloc_ceiling HF4096 HFceil CVhi (or_introl Ha)). }
assert (KSHB : forall a, lc_SH cx <= a < lc_SH cx + 32 ->
  aview segs (@w_H segs W3) mem3 a = aview segs (w_H W) mem1 a).
{ intros a Ha.
  assert (HNW : ~ close_wr None B2 a).
  { intros Hx. pose proof (l6_wr_low None B2 a Hx) as Hlo.
    exact (l6_sh_low (lc_F cx) a ltac:(lia) ltac:(unfold lc_SH in Ha; exact (proj1 Ha)) (proj2 Hlo)). }
  rewrite (K34 LF_CID (l_fpos cx) a HFin
    ltac:(right; unfold in_zr; cbn [fst snd]; rewrite HFaddr;
          change (fs_frame_bytes LF_CID / 8) with 32; unfold lc_SH, shadow_addr in *; lia) HNW).
  apply KR. exact (l6_addr_rng (lc_F cx) a alloc_ceiling HF4096 HFceil CVhi (or_intror Ha)). }
(* the core, the spill slots and the frame's shadow at the return *)
assert (KCORE : @lc_core rc B cx ly3 S3 W3 regs3 mem3 md3 e1).
{ apply (@lc_core_kept rc B MT XL RLO RHI cx ly1 S1 W regs1 mem1 md1 e1 CLOSE_STK
    ly3 S3 W3 regs3 mem3 md3 e1 HB HC HJ3 Hfr3 Hperm3).
  - intros r Hr. exact (eq_trans (HP3 r Hr) (HPRE r Hr)).
  - split; [vm_compute; intros Hx; discriminate Hx | lia].
  - intros a Ha Hw. rewrite (K31 a Ha Hw). apply KR. lia.
  - intros i Hi.
    pose proof (HINg ltac:(lia)) as InP.
    pose proof (req_size_pos (l_n cx) ltac:(lia)) as (_ & Hq).
    assert (Hi' : 0 <= i < req_size (l_n cx)) by lia.
    assert (HNW : ~ close_wr None B2 (l_p cx + i)).
    { intros Hx. exact (blk_img segs B LAWS ly1 S1 W mem1 md1 (l_p cx) (l_n cx) (l_p cx + i) HARc InP
        (l6_rng (l_p cx) i (req_size (l_n cx)) Hi') (l6_wr_img None B2 _ Hx)). }
    rewrite (K32 (l_p cx) (l_n cx) i InP Hi' HNW).
    apply KR.
    destruct (al_blocks _ _ LAWS ly1 S1 W mem1 md1 (l_p cx) (l_n cx) HARc InP) as (_ & _ & _ & Happ & _ & _).
    pose proof (app_addr_below_ceil (l_p cx + i)
      (in_app_addr _ _ _ Happ (l6_rng (l_p cx) i (req_size (l_n cx)) Hi'))) as HAC.
    pose proof (@ASAN_CEIL_range rc) as (CRa & _).
    change (2 ^ 64) with 18446744073709551616. lia.
  - intros a Ha. apply KFR. unfold LF_FBYTES in *. lia.
  - intros a Ha Hp. apply (apresent_transfer segs (w_H W) (@w_H segs W3) mem1 mem3 a).
    + exact (l6_addr_rng (lc_F cx) a alloc_ceiling HF4096 HFceil CVhi (or_introl Ha)).
    + exact (frm_img segs B LAWS ly1 S1 W mem1 md1 LF_CID (l_fpos cx) a HARc HFin
        ltac:(rewrite HFaddr; change (fs_frame_bytes LF_CID) with LF_FBYTES; exact Ha)).
    + exact (KFR a Ha).
    + exact Hp. }
assert (KSPL : lc_spills cx (lf_spill_loop (lc_F cx)) (aview segs (@w_H segs W3) mem3)).
{ apply (lc_spills_kept cx (lf_spill_loop (lc_F cx)) (aview segs (w_H W) mem1)).
  - intros o Ho. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES in *; lia)) as HV.
    rewrite Forall_forall in HV. pose proof (HV o Ho) as (_ & _ & Hlo & Hhi). split; lia.
  - intros a Ha. transitivity (aview segs (w_H W) (ms_mem ms) a).
    + exact (K31 a ltac:(change (2 ^ 64) with 18446744073709551616; lia) ltac:(lia)).
    + apply KR. change (2 ^ 64) with 18446744073709551616. lia.
  - exact HSPL. }
assert (KFSH : lc_fsh cx (aview segs (@w_H segs W3) mem3) false false).
{ apply (lc_fsh_kept cx (aview segs (w_H W) mem1)); [exact KSHB | exact HFSH]. }
(* the registers the cut names *)
assert (KR18 : YK11.getr regs3 18 = w64 (lc_SH cx))
  by exact (eq_trans (HP3 18 ltac:(hnf; lia)) (eq_trans (HPRE 18 ltac:(hnf; lia)) R18)).
assert (KR26 : YK11.getr regs3 26 = w64 SHADOW_OFF)
  by exact (eq_trans (HP3 26 ltac:(hnf; lia)) (eq_trans (HPRE 26 ltac:(hnf; lia)) R26)).
assert (KR19 : YK11.getr regs3 19 = w64 (lo_ops op))
  by exact (eq_trans (HP3 19 ltac:(hnf; lia)) (eq_trans (HPRE 19 ltac:(hnf; lia)) R19)).
assert (KR20 : YK11.getr regs3 20 = w64 (lc_F cx + 32))
  by exact (eq_trans (HP3 20 ltac:(hnf; lia)) (eq_trans (HPRE 20 ltac:(hnf; lia)) R20)).
assert (KR22 : YK11.getr regs3 22 = w64 1)
  by exact (eq_trans (HP3 22 ltac:(hnf; lia)) (eq_trans (HPRE 22 ltac:(hnf; lia)) R22)).
assert (KCUR : lc_cur cx regs3 24 27 (lc_oc (l_pl cx) (lo_c op))).
{ destruct Hcur as (Hcur1 & Hcur2). split.
  - exact (eq_trans (HP3 24 ltac:(hnf; lia)) (eq_trans (HPRE 24 ltac:(hnf; lia)) Hcur1)).
  - exact (eq_trans (HP3 27 ltac:(hnf; lia)) (eq_trans (HPRE 27 ltac:(hnf; lia)) Hcur2)). }
(* the record *)
exists ly3, S3, regs3, mem3, md3, e1, B3.
split.
{ assert (EPCZ : BASE + LO_SET56 = transportb_text + LO_SET56) by (vm_compute; reflexivity).
  rewrite Ec3. unfold lc_cfg, w64. rewrite EPCZ. reflexivity. }
split; [right; exact Hopc|].
split.
{ split; [exact KCORE|]. split; [exact (conj KR18 KR26)|]. split; [exact KSPL|]. split; [exact KFSH|].
  split; [exact HOPOK|]. split; [exact HEV|]. split; [|exact KR19].
  destruct HMO as (HMle & HMok). split.
  - replace (Z.of_nat (lo_k op) * lf_rcost MT) with (Z.of_nat (lo_k op) * lf_rcost MT + 0) by lia.
    exact (mo_le_trans MT MTL _ _ _ _ _ HMle Hmo3).
  - apply (mo_ok_step MT MTL S1 S3 0 ((TC.OPS_MAX - Z.of_nat (lo_k op)) * lf_rcost MT));
      [rewrite Z.add_0_l; exact HMok | exact Hmo3]. }
split.
{ unfold lc_tw. exact HTW3. }
split; [exact ESET|].
split; [exact EQOP|].
split; [exact KCUR|].
split; [exact KR20 | exact KR22].
Qed.

End seg6b.
