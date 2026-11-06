(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 471 of its 545 lines of code are new or changed and 956 lines of the source are left out. *)
(* receive_seg_head: Lemma recv_head : recv_head_stmt (lib/B/Prog/receive_seg_cut.v), the head piece of the walk of
   receive on fuzz_transport.asan-ubsan (0x836a8 = transportb_sigma TB_receive, AF_receive = 0x2408 of
   lib/B/Prog/DgnTransportBList.v): from the entry to the mal cut (+0x038, the malloc's return 0x836e0).
   The walk holds the CALLER's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []) throughout.
     run 1, +0x000 .. +0x030 (lib/B/Prog/TransportGRunB.v paj_run_x, one run, stopped at the call):
       +0x000           `addi sp, sp, -128`;
       +0x004 .. +0x018 the six saves (ra, s0 .. s4 at sp + 120 .. sp + 80, that is at the entry sp - 8 .. - 48);
       +0x01c .. +0x028 s2 = a3, s3 = a2, s1 = a1 = n, s4 = a0 = p;
       +0x02c .. +0x030 a0 = n + (n = 0 ? 1 : 0) = Z.max 1 n (lib/A/Prog/receive_seg_head.v rh_a0, image-free:
                        `seqz` is ALU_SLTU against 1);
     +0x034           `jal` the malloc wrapper, read inside the G journal by lib/A/Prog/receive_seg_alloc.v
                      gx_malloc_at (YC5d.v amalloc04_rule): o = (sp - 128) - sp0, ASTACK - o <= STK from the window
                      premise and recv_stk_eq, the live and event budgets from RECV_LIVE / RECV_EV, mo_ok from
                      recv_cost by YC5d.v mo_ok_le, the entry chain carried to the call by YCbq.v achain_kept (the
                      run writes only below the entry sp) and turned into chain_pre by achain_chain_pre (s0 is the
                      entry's), and the trace by receive_seg_alloc.v gx_trace0 at recv_fix's malloc trace fact
                      (RECV_RA_MALLOC = 0x836e0).
   The mal cut is then applied (recv_mal_at), with:
     recv_cur: the journal at k + 1 and the frames of the malloc's post; the blocks by Permutation_cons_append of
       its ablocks equation; the meter by its mo_le; acall_kept_g over [sp - RECV_STK, sp) and recv_wr bytes by
       TransportGCg.v dk_kept_refl_g + dk_kept_step_g (the prologue writes only [sp - 128, sp)) and then
       dk_kept_trans_nf_g with NF = the new block's bytes (rh_blk_sep / rh_frm_sep / rh_sh_sep: the new block is
       apart from the caller's blocks, frames, frame shadows and the shadow band); the six saved words read off
       the run's stack region (CanKit.v can_field_of_region, YF0x.v val_mem_rdword) and kept by the malloc's
       acall_kept (they lie at or above the entry sp - 48, above its window [sp - 128 - ASTACK, sp - 128));
       4096 <= a from the rule.
     recv_res: recv_addr_ok a from 4096 <= a and a + req_size m <= alloc_ceiling (AR_laws al_blocks), then the
       model premise of recv_fix at a (the option destructed).
     recv_src: the bytes at p across the two steps (the prologue keeps them by decode_off_win, the malloc by
       rh_src_malloc) and their placement at the new state (rh_src_malloc: DgnTransportBCg.v trans_src_ok_inner
       with decode_rd_ok at the new memory, case by case as trans_src_ok_kept_ge0 takes it); apart from the block
       by rh_src_apart.
     tw_at at Bw: TWorldB.v tw_kept_GB with the G bytes kept (the run writes the stack only; the malloc by
       TransportGCg.v gx_kept_of_acall_kept).
     recv_regs_mal: the run's registers, moved across the call by the rule's aregs_preserved. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg receive_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require receive_seg_alloc receive_seg_head.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module YF0x := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.YF0x.
Module RSA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.receive_seg_alloc.
Module AH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.receive_seg_head.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The run's entry state: the 128-byte frame below sp, nothing else (image B's receive reads no image cell before
   the call: no shadow base, no instrumented access). *)
Definition rh_regions : smem := [stack_region RECV_FRAME].
Definition rh_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_rh : sstate := mkSS AF_receive sr_atoms rh_regions None rh_facts.
Definition RH_SH : list shent := [].
Definition RH_Bx : sv := SOff 32 0.
Definition RH_B0 : Z * Z := (0, 0).

(* The six words the prologue saves, as (offset from the entry sp, register). *)
Definition rh_saved : list (Z * Z) := [(-8, 1); (-16, 8); (-24, 9); (-32, 18); (-40, 19); (-48, 20)].

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac rh_reg HS r v H tac :=
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

(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac rh_region HS i HR :=
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

Ltac rh_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* The windows a run wrote, each inside the bytes Zs. *)
Ltac rh_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write rights of the run: the 128-byte frame below sp, inside the call's own window. *)
Ltac rh_awr UspE :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite UspE in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |];
  apply awr_ok_x_nil.

(* A callee-saved register of the call's post, from its value at the call. *)
Ltac rh_kp HP n K := etransitivity; [apply (HP n); unfold acallee_saved; lia | exact K].

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma rh_base : BASE + AF_receive = transportb_sigma TB_receive.
Proof. vm_compute. reflexivity. Qed.

(* The walk's valuation: the 32 entry registers (and the shadow base as atom 32, which no step reads). *)
Definition rh_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).

(* The entry state of the run. *)
Lemma rh_entry : forall (Wx : world segs) regs mem,
  (forall a, spZ regs - RECV_FRAME <= a < spZ regs -> apresent (w_H Wx) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (rh_E regs) ss_rh
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_receive)) mem (YK11.seg_rom segs))).
Proof.
  intros Wx regs mem Hpres Hsp Hsp16.
  assert (E2' : ew (rh_E regs) 2 = YK11.getr regs 2) by (unfold rh_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew (rh_E regs) 2) = spZ regs) by (rewrite E2'; reflexivity).
  rewrite restrict_mkst_fx. unfold ss_rh, rh_regions.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold RECV_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact (conj I I).
  - unfold rh_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ---- the block the malloc adds is apart from what the call must keep ---- *)

(* It is apart from a block of the caller (YCbq.v sep_blocks_pos at the state after the call, where both are
   blocks of the same state). *)
Lemma rh_blk_sep : AR_laws segs B -> forall ly2 S2 (W2 : world segs) mem2 md2 lyc Sc res m b m',
  @AR rc segs B ly2 S2 W2 mem2 md2 ->
  ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, m)] ->
  In (b, m') (ablocks B lyc Sc) ->
  b + req_size m' <= res \/ res + req_size m <= b.
Proof.
intros LAWS ly2 S2 W2 mem2 md2 lyc Sc res m b m' HAR2 EB Hin.
apply in_split in Hin as (l1 & l2 & El).
assert (Eq : ablocks B ly2 S2 = l1 ++ (b, m') :: l2 ++ (res, m) :: [])
  by (rewrite EB, El, <- app_assoc; reflexivity).
pose proof (sep_blocks_pos segs B LAWS ly2 S2 W2 mem2 md2 (b, m') (res, m) l1 l2 [] HAR2 Eq) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* It is apart from a side-stack frame of the caller (YCbq.v sep_block_frame). *)
Lemma rh_frm_sep : AR_laws segs B -> forall ly2 S2 (W2 : world segs) mem2 md2 lyc res m cid pos,
  @AR rc segs B ly2 S2 W2 mem2 md2 ->
  In (res, m) (ablocks B ly2 S2) -> In (cid, pos) (frames S2) ->
  (forall c q, frame_addr ly2 c q = frame_addr lyc c q) ->
  frame_addr lyc cid pos + fs_frame_bytes cid <= res \/ res + req_size m <= frame_addr lyc cid pos.
Proof.
intros LAWS ly2 S2 W2 mem2 md2 lyc res m cid pos HAR2 HinB HinF Hfa.
pose proof (sep_block_frame segs B LAWS ly2 S2 W2 mem2 md2 res m cid pos HAR2 HinB HinF) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (Hfa cid pos) in Hd. lia.
Qed.

(* No byte of it lies in the shadow band: a block lies in application memory (AR_laws al_blocks' in_app). *)
Lemma rh_sh_sep : AR_laws segs B -> forall ly2 S2 (W2 : world segs) mem2 md2 res m,
  @AR rc segs B ly2 S2 W2 mem2 md2 -> In (res, m) (ablocks B ly2 S2) ->
  forall x, kLowMemEnd <= x < kHighShadowEnd -> ~ (res <= x < res + req_size m).
Proof.
intros LAWS ly2 S2 W2 mem2 md2 res m HAR2 Hin x Hx Hr.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res m HAR2 Hin) as (_ & R1 & R2 & Rapp & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Rapp.
unfold kLowMemEnd, kHighShadowEnd in Hx. lia.
Qed.

(* A shadow byte of a live side-stack frame lies in the shadow band. *)
Lemma rh_fsh_rng : AR_laws segs B -> forall ly2 S2 (W2 : world segs) mem2 md2 cid pos x,
  @AR rc segs B ly2 S2 W2 mem2 md2 -> In (cid, pos) (frames S2) ->
  in_zr x (shadow_addr (frame_addr ly2 cid pos), fs_frame_bytes cid / 8) ->
  kLowMemEnd <= x < kHighShadowEnd.
Proof.
intros LAWS ly2 S2 W2 mem2 md2 cid pos x HAR2 Hin Hr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin) as (F1 & F2 & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfs.
pose proof (shadow_range_end (frame_addr ly2 cid pos) (fs_frame_bytes cid) Hfs) as Hse.
assert (Hd : (frame_addr ly2 cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
change (2 ^ 47 / 8) with (2 ^ 44) in Hd.
pose proof (Z.div_pos (frame_addr ly2 cid pos) 8 ltac:(lia) ltac:(lia)) as Hp.
unfold in_zr in Hr. cbn [fst snd] in Hr.
unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *. lia.
Qed.

(* The range a callee reads is apart from the block the malloc added: a heap block of the caller by rh_blk_sep,
   a side-stack frame by rh_frm_sep, G and TRANS_RO_RD because a block is outside the image (YCbq.v blk_img),
   the machine stack because it lies at or above alloc_ceiling and the block below it. *)
Lemma rh_src_apart : AR_laws segs B -> forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2
    res m q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, m)] -> frames S2 = frames Sc ->
  (forall c pos, frame_addr ly2 c pos = frame_addr lyc c pos) ->
  0 <= m -> trans_src_ok B lyc Sc W memc q n -> 0 < n ->
  q + n <= res \/ res + req_size m <= q.
Proof.
intros LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 res m q n HAR HAR2 EB Hfr Hfa Hm Hs Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HinR : In (res, m) (ablocks B ly2 S2)) by (rewrite EB; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res m HAR2 HinR) as (_ & R1 & R2 & Rapp & _).
pose proof (req_size_pos m Hm) as [Hr1 Hr2].
destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
  pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
  pose proof (rh_blk_sep LAWS ly2 S2 W2 mem2 md2 lyc Sc res m bA nA HAR2 EB Hin) as Hd. lia.
- destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
  + assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfr; exact Hin).
    pose proof (rh_frm_sep LAWS ly2 S2 W2 mem2 md2 lyc res m cid pos HAR2 HinR Hin2 Hfa) as Hd. lia.
  + destruct (Z_le_gt_dec (q + n) res) as [H1|H1]; [left; exact H1|].
    destruct (Z_le_gt_dec (res + req_size m) q) as [H2|H2]; [right; exact H2|].
    exfalso. apply (blk_img segs B LAWS ly2 S2 W2 mem2 md2 res m (Z.max q res) HAR2 HinR ltac:(lia)).
    exact (trans_g_img (Z.max q res) (HG (Z.max q res) ltac:(lia))).
  + right. destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2]. lia.
  + destruct (Z_le_gt_dec (q + n) res) as [H1|H1]; [left; exact H1|].
    destruct (Z_le_gt_dec (res + req_size m) q) as [H2|H2]; [right; exact H2|].
    exfalso. apply (blk_img segs B LAWS ly2 S2 W2 mem2 md2 res m (Z.max q res) HAR2 HinR ltac:(lia)).
    exact (trans_ro_img (Z.max q res) (HR (Z.max q res) ltac:(lia))).
Qed.

(* The placement of a read range across the malloc, and its bytes: DgnTransportBCg.v trans_src_ok_kept_ge0's
   argument, with the blocks GROWING by the new block (so its Permutation premise does not hold). *)
Lemma rh_src_malloc : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  forall lyc Sc (W : world segs) memX mdX ly2 S2 (W2 : world segs) mem2 md2 slo shi res m q n,
  @AR rc segs B lyc Sc W memX mdX -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, m)] -> frames S2 = frames Sc ->
  (forall c pos, frame_addr ly2 c pos = frame_addr lyc c pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  @acall_kept rc segs B lyc Sc W memX W2 mem2 slo shi (fun x => res <= x < res + req_size m) ->
  0 <= m -> (q + n <= res \/ res + req_size m <= q) -> (q + n <= slo \/ shi <= q) ->
  trans_src_ok B lyc Sc W memX q n -> 0 < n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall x, q <= x < q + n -> aview segs (w_H W2) mem2 x = aview segs (w_H W) memX x).
Proof.
intros LAWS HRU HRE HGU HGE lyc Sc W memX mdX ly2 S2 W2 mem2 md2 slo shi res m q n
  HAR HAR2 EB Hfr Hfa Elo Ehi HK Hm Hap Hoff Hs Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HinR : In (res, m) (ablocks B ly2 S2)) by (rewrite EB; apply in_or_app; right; left; reflexivity).
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; rewrite EB; apply in_or_app; left; exact Hbm).
assert (Hf : forall f, In f (frames Sc) -> In f (frames S2)) by (intros f Hf0; rewrite Hfr; exact Hf0).
pose proof (req_size_pos m Hm) as [Hr1 Hr2].
pose proof HK as (K1 & K2 & K3 & K4 & _).
assert (HnE : forall x, q <= x < q + n -> ~ (res <= x < res + req_size m)) by (intros x Hx; lia).
pose proof (rh_sh_sep LAWS ly2 S2 W2 mem2 md2 res m HAR2 HinR) as HnEs.
assert (KS : forall cid pos s, In (cid, pos) (frames Sc) ->
   in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
   aview segs (w_H W2) mem2 s = aview segs (w_H W) memX s).
{ intros cid pos s Hin Hs'. apply (K4 cid pos s Hin (or_intror Hs')). apply HnEs.
  apply (rh_fsh_rng LAWS ly2 S2 W2 mem2 md2 cid pos s HAR2 (Hf _ Hin)).
  rewrite (Hfa cid pos). exact Hs'. }
assert (KV : forall x, q <= x < q + n -> aview segs (w_H W2) mem2 x = aview segs (w_H W) memX x).
{ intros x Hx. destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
  - destruct (al_blocks _ _ LAWS lyc Sc W memX mdX bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
    replace x with (bA + (x - bA)) by lia.
    apply (K2 bA nA (x - bA) Hin ltac:(lia)). replace (bA + (x - bA)) with x by lia. exact (HnE x Hx).
  - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
    + apply (K4 cid pos x Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE x Hx)].
    + pose proof (HG x Hx) as Gx. exact (K3 x (trans_g_img x Gx) (HGU x Gx) (HGE x Gx)).
    + destruct (trans_stk_bounds B lyc Sc W memX mdX HAR) as [T1 T2]. apply K1; lia.
    + pose proof (HR x Hx) as Rx. destruct (trans_ro_rd_scoped B HRU HRE x Rx) as [Ho He].
      exact (K3 x (trans_ro_img x Rx) Ho He). }
split; [|exact KV].
destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
- left. exists bA, nA. split; [exact (Hbl _ Hin) | lia].
- assert (Hrd2 : decode_rd_ok W2 mem2 q n).
  { destruct HL as [HF | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
    - eapply decode_rd_ok_fake_kept_ge0;
        [exact LAWS | exact HAR | exact HF | exact Hrd | lia | exact KV | exact KS].
    - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh].
      eapply trans_rd_ok_sh; [exact Hrd | exact KV | exact Ha | exact Hh].
    - assert (HSA : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF q n /\
                    shadow_hull_vis (aview segs (w_H W2) mem2) q n)
        by (eapply stack_zshadow_ra_ge0; [exact HAR2 | lia | rewrite Elo; lia | rewrite Ehi; lia]).
      destruct HSA as [Ha Hh]. eapply trans_rd_ok_sh; [exact Hrd | exact KV | exact Ha | exact Hh].
    - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh].
      eapply trans_rd_ok_sh; [exact Hrd | exact KV | exact Ha | exact Hh]. }
  eapply trans_src_ok_inner; [exact Hbl | exact Hf | exact Hfa | exact Elo | exact Ehi | exact Hrd2 |].
  exact (or_intror (conj HL Hrd)).
Qed.

(* ---- the piece: the entry, the prologue, the malloc, the mal cut ---- *)

Lemma recv_head : @recv_head_stmt fx rc B MT.
Proof.
unfold recv_head_stmt, recv_entry_at. intros MAL HLAWS HCALLS
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch HFIX.
pose proof HLAWS as (HMPC & HFPC & HCELLS & HRC & HGU & HGE & HRU & HRE & LAWS & MTL & HGX & HGNE).
pose proof HCALLS as (HAM & _).
pose proof HFIX as (HJe & Hret & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hch & Hal & Hwlo & Hwhi & Hbp & Hpf &
  Hn & Hgarr & Hsrc & Htw & Hgf & Hmodel & Hrom & Hrinv & Hdn & Cn1 & Cn2 & Cn3 & Cn4 & Cn5 & Hnev & Hlive & Hmo &
  Hcost & Htm & Htf).
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & Hly & _ & _ & _ & _ & Hnev0 & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
clear HJi memS.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
assert (FS : RECV_STK = 16512) by reflexivity.
assert (FF : RECV_FRAME = 128) by reflexivity.
assert (HAST : ASTACK = 16384) by reflexivity.
assert (Hlen0 : 0 <= Z.of_nat (length bytes)) by lia.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
set (E0 := rh_E regs).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, rh_E; apply Eimg_env).
assert (EE : forall nn (rg : bv 5), Z.of_nat nn = bv_unsigned rg -> ew E0 nn = YK11.getr regs rg)
  by (intros nn rg Hnn; unfold E0, rh_E; apply ew_Eimg_Ereg_nat; exact Hnn).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
pose proof (rh_entry W regs memc ltac:(intros x Hx; apply Hpres0; lia) Hsp Hal) as HS.
fold E0 in HS.
assert (SHOK : sh_ok segs RH_Bx RH_SH E0 (mrestrict (w_H W) memc)) by (unfold sh_ok, RH_SH; apply Forall_nil).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof HJe as HJ.
unfold cfg_at.
pose proof rh_base as VB0.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_receive)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* the run: the frame, the six saves, s1 .. s4, a0 = Z.max 1 n, up to the call *)
paj_run_tok RUN HS HJ SHOK RH_B0.
{ rh_awr Usp. }
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody md1. clear mat.
assert (KT : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - RECV_FRAME <= x < spZ regs) ->
  aview segs (w_H W) (ms_mem ms) x = aview segs (w_H W) memc x).
{ intros x Hx Hnx.
  apply (kept_of_frame _ _ (w_H W) memc (ms_mem ms) (fun y => spZ regs - RECV_FRAME <= y < spZ regs) HFr);
    [| exact Hx | exact Hnx].
  intros b wlo whi y Hin Hy. cbv beta. rh_win Hin Hy ltac:(rewrite ?Usp in Hy; unfold RECV_FRAME; lia). }
assert (GA1 : forall x, apresent (w_H W) memc x -> apresent (w_H W) (ms_mem ms) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
(* the registers at the call *)
rh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 9280)) R1 ltac:(apply codeptr_val; exact HEI).
rh_reg HS (2%bv : bv 5) (Z_to_bv 64 (spZ regs - RECV_FRAME)) R2
  ltac:(cbn [sv_denot]; rewrite Usp; f_equal; unfold RECV_FRAME; lia).
rh_reg HS (3%bv : bv 5) (YK11.getr regs 3) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat (3%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rh_reg HS (4%bv : bv 5) (YK11.getr regs 4) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat (4%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rh_reg HS (8%bv : bv 5) (YK11.getr regs 8) R8
  ltac:(cbn [sv_denot]; rewrite (EE 8%nat (8%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rh_reg HS (9%bv : bv 5) (w64 (Z.of_nat (length bytes))) R9
  ltac:(cbn [sv_denot]; rewrite (EE 11%nat (11%bv : bv 5) eq_refl), H11, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
rh_reg HS (10%bv : bv 5) (Z_to_bv 64 (Z.max 1 (Z.of_nat (length bytes)))) R10
  ltac:(apply (AH.rh_a0 E0 11%nat (Z.of_nat (length bytes)));
        [rewrite (EE 11%nat (11%bv : bv 5) eq_refl); exact H11 | lia]).
rh_reg HS (18%bv : bv 5) (YK11.getr regs 13) R18
  ltac:(cbn [sv_denot]; rewrite (EE 13%nat (13%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rh_reg HS (19%bv : bv 5) (w64 by_poll) R19
  ltac:(cbn [sv_denot]; rewrite (EE 12%nat (12%bv : bv 5) eq_refl), H12, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
rh_reg HS (20%bv : bv 5) (w64 p) R20
  ltac:(cbn [sv_denot]; rewrite (EE 10%nat (10%bv : bv 5) eq_refl), H10, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
rh_reg HS (21%bv : bv 5) (YK11.getr regs 21) R21
  ltac:(cbn [sv_denot]; rewrite (EE 21%nat (21%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rh_reg HS (22%bv : bv 5) (YK11.getr regs 22) R22
  ltac:(cbn [sv_denot]; rewrite (EE 22%nat (22%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rh_reg HS (23%bv : bv 5) (YK11.getr regs 23) R23
  ltac:(cbn [sv_denot]; rewrite (EE 23%nat (23%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rh_reg HS (24%bv : bv 5) (YK11.getr regs 24) R24
  ltac:(cbn [sv_denot]; rewrite (EE 24%nat (24%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rh_reg HS (25%bv : bv 5) (YK11.getr regs 25) R25
  ltac:(cbn [sv_denot]; rewrite (EE 25%nat (25%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rh_reg HS (26%bv : bv 5) (YK11.getr regs 26) R26
  ltac:(cbn [sv_denot]; rewrite (EE 26%nat (26%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rh_reg HS (27%bv : bv 5) (YK11.getr regs 27) R27
  ltac:(cbn [sv_denot]; rewrite (EE 27%nat (27%bv : bv 5) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* the six saved words, read off the run's stack region *)
rh_region HS 0%nat HRsk.
assert (HSVg : forall (o r : Z), In (o, r) rh_saved -> 0 <= r < 32 ->
  rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 r)))).
{ intros o r Hin Hr.
  apply (YF0x.val_mem_rdword (w_H W) (ms_mem ms) (spZ regs + o) (bv_unsigned (YK11.getr regs (Z_to_bv 5 r)))
    (YK11.u64_range _)).
  apply (can_field_of_region E0 _ 2%nat (spZ regs) _ (-128) 0 (-128) 0 o 8%N (SOff (Z.to_nat r) 0)
    (bv_unsigned (YK11.getr regs (Z_to_bv 5 r))) HRsk Usp).
  - unfold rh_saved in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; rh_in |]). destruct Hin.
  - cbn [sv_denot].
    rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)
      ltac:(rewrite Z2Nat.id by lia; symmetry; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
            change (2 ^ Z.of_N 5) with 32; apply Z.mod_small; lia)).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - cbn. apply YK11.u64_range.
  - cbn. lia. }
(* the call's premises *)
assert (Era : BASE + 9280 = RECV_RA_MALLOC)
  by (unfold RECV_RA_MALLOC; rewrite <- VB0; unfold AF_receive; lia).
assert (RET : YK0s.ret_ok (Z_to_bv 64 (BASE + 9280)))
  by (apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity]).
assert (Hraz : raZ (ms_regs ms) = RECV_RA_MALLOC).
{ change (raZ (ms_regs ms)) with (bv_unsigned (YK11.getr (ms_regs ms) 1)). rewrite R1, Era.
  rewrite (proj1 recv_ra_at). apply unsigned_lit_small. lia. }
assert (SPT : spZ (ms_regs ms) = spZ regs - RECV_FRAME).
{ change (spZ (ms_regs ms)) with (bv_unsigned (YK11.getr (ms_regs ms) 2)). rewrite R2.
  apply unsigned_lit_small. unfold RECV_FRAME. lia. }
assert (S0T : s0Z (ms_regs ms) = s0Z regs).
{ change (s0Z (ms_regs ms)) with (bv_unsigned (YK11.getr (ms_regs ms) 8)).
  change (s0Z regs) with (bv_unsigned (YK11.getr regs 8)). rewrite R8. reflexivity. }
assert (Hchm : @achain rc lyc (aview segs (w_H W) (ms_mem ms)) (spZ regs) (s0Z regs) ch).
{ apply (achain_kept lyc (aview segs (w_H W) memc) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch);
    [lia | lia | intros x Hx; apply KT; [lia | unfold RECV_FRAME; lia]]. }
assert (Hcp : chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch).
{ apply (achain_chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (spZ regs) (s0Z regs) ch (ms_regs ms) Hchm);
    [rewrite SPT; unfold RECV_FRAME; lia | exact S0T | rewrite Hraz, (proj1 recv_ra_at); lia]. }
assert (Htr : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms) ch) (as_universe B))
  by (rewrite RSA.gx_trace0, Hraz; exact Htm).
assert (Ho16 : (spZ regs - RECV_FRAME - sp0) mod 16 = 0).
{ replace (spZ regs - RECV_FRAME - sp0) with ((spZ regs - sp0) + (-8) * 16) by (unfold RECV_FRAME; lia).
  rewrite Z_mod_plus_full, Zminus_mod, Hal, Hsp0a. reflexivity. }
assert (Pnev : st_nev Sc < EV_MAX) by (unfold RECV_EV in Hnev; lia).
assert (Plive : blocks_bytes Sc + Z.max 1 (Z.of_nat (length bytes)) <= LIVE_MAX)
  by (unfold RECV_LIVE in Hlive; lia).
pose proof (mo_free_nonneg MT MTL) as Hmfree.
assert (Pmo : mo_ok MT Sc (mo_malloc MT (Z.max 1 (Z.of_nat (length bytes)))))
  by (apply (mo_ok_le MT MTL Sc _ T Hmo); unfold recv_cost in Hcost; lia).
(* the malloc *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg
    (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_malloc)) mm rom) mdx) Q) end.
rewrite <- HMPC.
refine (SRr_bind segs W _ _ _
  (RSA.gx_malloc_at (SK := tfib_sink_head) segs B LAWS transportb_segs_low MT (HAM fx) TG.G_HARNESS_B W
     (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc md1 k
     (Z.max 1 (Z.of_nat (length bytes))) (spZ regs - RECV_FRAME - sp0) (Z_to_bv 64 (BASE + 9280)) ch HJ
     R10 ltac:(unfold MALLOC_MAX; lia) Plive ltac:(rewrite SPT; lia) Ho16 ltac:(lia) ltac:(lia)
     ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp) R1 RET Pnev Hcp Htr Pmo) _).
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & a & -> & HJ2 & HP2 & Ha0 & Hfr2 & Ha4096 & EB & HK
  & MLE).
assert (HAR2 : @AR rc segs B ly2 S2 W2 mem2 md2) by (eapply ajournal_gx_AR; exact HJ2).
assert (HARm : @AR rc segs B lyc Sc W (ms_mem ms) md1) by (eapply ajournal_gx_AR; exact HJ).
assert (ELY : (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) /\
              ly_stk_lo ly2 = ly_stk_lo lyc /\ ly_stk_hi ly2 = ly_stk_hi lyc).
{ destruct (gx_open segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + 1) HJ2)
    as (mS1 & J1 & _ & _).
  destruct (gx_open segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJe)
    as (mS0 & J0 & _ & _).
  destruct J1 as (_ & (_ & _ & _ & _ & _ & F1 & _ & _ & _ & L1 & U1 & _) & _).
  destruct J0 as (_ & (_ & _ & _ & _ & _ & F0 & _ & _ & _ & L0 & U0 & _) & _).
  split; [intros cid pos; unfold frame_addr; rewrite F1, F0; reflexivity|]. split; congruence. }
destruct ELY as (ELYa & ELYlo & ELYhi).
assert (HinR : In (a, Z.max 1 (Z.of_nat (length bytes))) (ablocks B ly2 S2))
  by (rewrite EB; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 a _ HAR2 HinR) as (_ & _ & Hbce & Hbapp & _).
pose proof (req_size_pos (Z.max 1 (Z.of_nat (length bytes))) ltac:(lia)) as [Hrq1 Hrq2].
assert (Haok : recv_addr_ok a) by (unfold recv_addr_ok; lia).
destruct (TOP.receive_m timg_B Bw a bytes by_poll pf) as [[Bw' []] | ] eqn:EM;
  [| exfalso; exact (Hmodel a Haok EM)].
(* what the call has kept, from the entry memory to the malloc's *)
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W (ms_mem ms)
                (spZ regs - RECV_STK) (spZ regs) (recv_wr bytes)).
{ apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc (ms_mem ms)
    (spZ regs - RECV_STK) (spZ regs) (recv_wr bytes) (fun y => spZ regs - RECV_FRAME <= y < spZ regs) HAR).
  - apply dk_kept_refl_g. intros x Hx. apply Hpres0. lia.
  - intros x Hx Hnx. exact (KT x Hx Hnx).
  - intros x Hx. exact (GA1 x Hx).
  - intros x Hx _. cbv beta in Hx. lia.
  - intros b m' i Hb Hi Hzs. exfalso. cbv beta in Hzs.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m' HAR Hb) as (_ & _ & Hbc & _). lia.
  - intros x Hx Hi _ _ _. exfalso. cbv beta in Hx.
    pose proof (transportb_segs_low x Hi) as Hl. unfold kLowMemEnd in Hl. lia.
  - intros cid pos x Hin Hr Hx. exfalso. cbv beta in Hx.
    pose proof (rh_fsh_rng LAWS lyc Sc W memc mdc cid pos x HAR Hin) as Hsh.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (Hsh Hr) as Hb2. unfold kLowMemEnd, kHighShadowEnd in Hb2. lia. }
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2
                (spZ regs - RECV_STK) (spZ regs) (recv_wr bytes)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc lyc Sc W memc W (ms_mem ms) W2 mem2
    (spZ regs - RECV_STK) (spZ regs) (sp0 + (spZ regs - RECV_FRAME - sp0) - ASTACK)
    (sp0 + (spZ regs - RECV_FRAME - sp0)) (recv_wr bytes)
    (fun x => a <= x < a + req_size (Z.max 1 (Z.of_nat (length bytes))))
    (fun x => a <= x < a + req_size (Z.max 1 (Z.of_nat (length bytes))))).
  - lia.
  - lia.
  - intros cid pos. reflexivity.
  - intros f Hf0. exact Hf0.
  - intros bm Hbm. exact Hbm.
  - intros b m' i Hb Hi Hnf. cbv beta in Hnf.
    pose proof (rh_blk_sep LAWS ly2 S2 W2 mem2 md2 lyc Sc a (Z.max 1 (Z.of_nat (length bytes))) b m'
      HAR2 EB Hb) as Hd.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m' HAR Hb) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos m' (proj1 Hn0)) as [Hq1 Hq2]. lia.
  - intros cid pos x Hin Hr Hnf. cbv beta in Hnf.
    assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfr2; exact Hin).
    destruct Hr as [Hr | Hr].
    + pose proof (rh_frm_sep LAWS ly2 S2 W2 mem2 md2 lyc a (Z.max 1 (Z.of_nat (length bytes))) cid pos
        HAR2 HinR Hin2 ELYa) as Hd.
      unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. lia.
    + apply (rh_sh_sep LAWS ly2 S2 W2 mem2 md2 a (Z.max 1 (Z.of_nat (length bytes))) HAR2 HinR x);
        [|exact Hnf].
      apply (rh_fsh_rng LAWS lyc Sc W memc mdc cid pos x HAR Hin). exact Hr.
  - exact Kg1.
  - apply acall_kept_g_of. exact HK.
  - lia.
  - lia.
  - intros x Hx. right. exact Hx. }
assert (GK : gx_kept segs TG.G_HARNESS_B W memc W2 mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS_B W memc W (ms_mem ms) W2 mem2).
  - intros x Hx. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX Hx) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS_B lyc Sc W (ms_mem ms) W2 mem2 _ _ _ HGX HGNE HK). }
assert (TW2 : tw_at TMAP_B (aview segs (w_H W2) mem2) Bw).
{ apply (tw_kept_GB (aview segs (w_H W) memc)); [exact Htw|].
  intros b n0 i Hin Hi. apply GK. unfold inG. apply Exists_exists. exists (b, n0).
  split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
assert (HSVm : forall (o r : Z), In (o, r) rh_saved -> 0 <= r < 32 ->
  rdword (aview segs (w_H W2) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 r)))).
{ intros o r Hin Hr.
  assert (Hob : -48 <= o <= -8).
  { unfold rh_saved in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
  assert (HE : forall i, 0 <= i < 8 ->
    aview segs (w_H W2) mem2 (spZ regs + o + i) = aview segs (w_H W) (ms_mem ms) (spZ regs + o + i))
    by (intros i Hi; apply (proj1 HK); lia).
  rewrite (rdword_ext _ _ _ HE). exact (HSVg o r Hin Hr). }
(* the mal cut *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + RECV_MAL)) mm rom) mdx) Q) end.
apply (MAL HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch
  a Bw' ly2 S2 W2 mem2 md2 regs2 HFIX).
- unfold recv_cur.
  split; [exact HJ2|]. split; [exact Hfr2|].
  split; [rewrite EB; apply Permutation_sym; apply Permutation_cons_append|].
  split; [exact MLE|]. split; [exact Kg2|]. split; [|exact Ha4096].
  unfold RECV_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
    replace (spZ regs - o) with (spZ regs + (- o)) by ring;
    apply (HSVm (- o) r); [unfold rh_saved; rh_in | lia] end.
- unfold recv_res. split; [exact Haok | exact EM].
- unfold recv_src. destruct (Nat.eq_dec (length bytes) 0) as [Hz | Hz].
  + split.
    * destruct bytes as [|b0 bs]; [apply garr8_nil | cbn in Hz; discriminate].
    * intros Hpos. exfalso. lia.
  + destruct (Hsrc ltac:(lia)) as [HSRC0 HOFF0].
    assert (HRD : decode_rd_ok W memc p (Z.of_nat (length bytes)))
      by (eapply trans_src_ok_rd; [exact LAWS | exact HAR | exact HSRC0 | lia]).
    pose proof HRD as (_ & _ & _ & Hmr & Hq0 & Hq63).
    unfold decode_off_win in HOFF0.
    assert (KP1 : forall x, p <= x < p + Z.of_nat (length bytes) ->
      aview segs (w_H W) (ms_mem ms) x = aview segs (w_H W) memc x).
    { intros x Hx. apply KT; [lia | lia]. }
    assert (HSRCm : trans_src_ok B lyc Sc W (ms_mem ms) p (Z.of_nat (length bytes))).
    { eapply trans_src_ok_view; [exact HSRC0 | exact KP1 |].
      intros s Hs. unfold kLowMemEnd, kHighShadowEnd in Hs. apply KT; [lia | unfold RECV_FRAME; lia]. }
    assert (HAP : p + Z.of_nat (length bytes) <= a \/
                  a + req_size (Z.max 1 (Z.of_nat (length bytes))) <= p)
      by (eapply rh_src_apart; [exact LAWS | exact HARm | exact HAR2 | exact EB | exact Hfr2 | exact ELYa
                               | lia | exact HSRCm | lia]).
    destruct (rh_src_malloc LAWS HRU HRE HGU HGE lyc Sc W (ms_mem ms) md1 ly2 S2 W2 mem2 md2
      _ _ a (Z.max 1 (Z.of_nat (length bytes))) p (Z.of_nat (length bytes))
      HARm HAR2 EB Hfr2 ELYa ELYlo ELYhi HK ltac:(lia) HAP ltac:(lia)
      HSRCm ltac:(lia)) as [HSRC2 HKV2].
    split.
    * apply (garr8_frame segs (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) p (TW.zs bytes) Hgarr).
      intros x Hx. unfold TW.zs in Hx. rewrite length_map in Hx.
      apply mbyte_of_aview. rewrite (HKV2 x ltac:(lia)). exact (KP1 x ltac:(lia)).
    * intros Hpos. split; [exact HSRC2 | lia].
- exact TW2.
- unfold recv_regs_mal, recv_regs_keep.
  split.
  + split; [rh_kp HP2 2 R2|]. split; [rh_kp HP2 3 R3|]. split; [rh_kp HP2 4 R4|].
    split; [rh_kp HP2 21 R21|].
    split; [rh_kp HP2 22 R22|]. split; [rh_kp HP2 23 R23|]. split; [rh_kp HP2 24 R24|].
    split; [rh_kp HP2 25 R25|]. split; [rh_kp HP2 26 R26 | rh_kp HP2 27 R27].
  + split; [rh_kp HP2 8 R8|]. split; [rh_kp HP2 9 R9|]. split; [rh_kp HP2 18 R18|].
    split; [rh_kp HP2 19 R19|]. split; [rh_kp HP2 20 R20 | exact Ha0].
Qed.

End s.
