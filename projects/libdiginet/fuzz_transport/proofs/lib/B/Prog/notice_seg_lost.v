(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 678 of its 962 lines of code are new or changed and 855 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcHead.v, with its module paths, module names and numbers changed; 528 of its 590 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/notice_seg_base.v, with its numbers changed; 317 of its 395 lines of code are new or changed and 512 lines of the source are left out. *)
(* notice_seg_lost: the N_ACK_LOST arm of notice's walk on fuzz_transport.asan-ubsan (lib/B/Prog/notice_cgW.v),
   from the jump `jr a0` (0x83474) with a0 = 0x8349c:
     0x8349c - 0x834a0  a0 = p; `jal check_inflight_lost` (0x85408) from sp - 16, return address 0x834a4;
     the call           the leaf statement c_lost (check_inflight_lost_cg.v, read through DgnTransportBCg.v
                        transport_leaf_at) applied from the G journal by TransportGCg.v gx_call_leaf and
                        DgnTransportBLeafb.v decode_leafb_journal: its model call is nt_m_lost's first conjunct at Bw,
                        its bytes of p + 64 and p + 68 come from the notice's garr8 array, its shadow facts from the
                        notice's read range; the leaf keeps every byte outside [sp - 16 - ESTACK, sp - 16);
     0x834a4            the symbolic state rebuilt at the return (DgnTransportBPaLib.v st_ok_pi_after_call, the frame
                        region kept), the region of M.fly.on added (based at the auipc value A_HI 73);
     0x834a4 - 0x834a8  a0 = the auipc value 0x5df4a4; the store of 0 at a0 - 1636 = M + 96 (M.fly.on);
     0x834ac, 0x83604 - 0x8360c  `j` to the epilogue, ra loaded back, sp = sp + 16, return.
   The post: the world is set_M_fly_on Bw 0 (nt_m_lost's second conjunct, nt_tw_set4), every other byte the walk
   keeps. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg check_state_desk_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import notice_seg_base notice_seg_lib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  DgnTransportBLeafb LeafCgKit AsanKA check_state_wake_c check_inflight_lost_c check_inflight_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
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
Module NLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module NLK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module NLE := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.ExecF.
Module NLB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.DgnTransportBLeafb.
Module NKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module CSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_c.
Module LILc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_lost_c.
Module LIL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_inflight_lost_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The leaf's footprint facts at the call memory                       *)
(* ------------------------------------------------------------------ *)

(* 2 bytes of the notice at p + k, read from its garr8 array: u_at NB k 2 (nt_val4's twin). *)
Lemma ntlost_val2 : forall (mm : word -> option byte) p (NB : list byte) k,
  garr8 tfibsegs mm p (map DSpec.bz NB) -> length NB = 72%nat -> 0 <= k -> k + 2 <= 72 ->
  val_mem tfibsegs mm (p + k) 2 (TW.u_at NB k 2).
Proof.
  intros mm p NB k HG HL Hk Hk2 j Hj.
  assert (Hjl : (Z.to_nat k + j < length (map DSpec.bz NB))%nat) by (rewrite length_map; lia).
  pose proof (garr8_mbyte tfibsegs mm p (map DSpec.bz NB) (Z.to_nat k + j) HG Hjl) as Hb.
  replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia. rewrite Hb. f_equal. f_equal.
  assert (Hls : length (TW.sub NB k 2) = 2%nat) by (unfold TW.sub; rewrite length_firstn, length_skipn; lia).
  unfold TW.u_at. rewrite <- Hls at 2.
  rewrite (tw_le_byte_ble (TW.sub NB k 2) j (Z_to_bv 8 0)) by lia.
  rewrite (tw_nth_sub NB k 2 j (Z_to_bv 8 0)) by lia.
  rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.

(* The world relation at the view is the world relation at the leaf form's raw view csw_view: every payload byte
   the relation names is shown by the view, so it is not hidden, and there the raw read is the view's byte. *)
Lemma ntlost_tw_csw : forall (W : world tfibsegs) mem Bw,
  tw_at TMAP_B (aview tfibsegs (w_H W) mem) Bw -> tw_at TMAP_B (CSW.csw_view mem) Bw.
Proof.
  intros W mem Bw H. apply (tw_kept_rows TMAP_B _ _ Bw H).
  intros o b n i Hin Hi. pose proof (proj2 H o b n i Hin Hi) as Hv.
  pose proof (NLB.decode_leafb_aview_vis W mem _ _ Hv) as Hvis.
  unfold CSW.csw_view.
  transitivity (option_map (fun x : byte => bv_unsigned x) (YP09.mbyte tfibsegs (mrestrict (w_H W) mem) (b + i)));
    [|reflexivity].
  f_equal. exact (NLB.decode_leafb_mrd W mem _ Hvis).
Qed.

(* A range of one payload row of the world relation is in the leaf's footprint RNG_W W. *)
Lemma ntlost_rng_row : forall (W : world tfibsegs) mem Bw o b n lo len,
  tw_at TMAP_B (aview tfibsegs (w_H W) mem) Bw -> In (o, b, n) TMAP_B -> b <= lo -> lo + len <= b + n ->
  NLE.rng (NLK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W mem Bw o b n lo len [_ HR] Hin H1 H2.
  pose proof (tw_row TMAP_B o b n TMAP_B_ok Hin) as (_ & _ & _ & Hb0 & Hbn).
  apply (NLB.decode_leafb_rng W); [lia | lia |].
  intros a Ha. pose proof (HR o b n (a - b) Hin ltac:(lia)) as Hv.
  replace (b + (a - b)) with a in Hv by lia.
  exact (NLB.decode_leafb_aview_vis W mem a _ Hv).
Qed.

(* A range of the notice's 72 bytes (each shown by the view) is in RNG_W W. *)
Lemma ntlost_rng_p : forall (W : world tfibsegs) memc p lo len,
  (forall a, p <= a < p + 72 -> aview tfibsegs (w_H W) memc a <> None) -> 0 <= p -> p <= lo ->
  lo + len <= p + 72 -> p + 72 <= 2 ^ 64 ->
  NLE.rng (NLK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W memc p lo len Hv H0 H1 H2 H3. apply (NLB.decode_leafb_rng W); [lia | lia |].
  intros a Ha. destruct (aview tfibsegs (w_H W) memc a) as [v|] eqn:Ev; [|exfalso; exact (Hv a ltac:(lia) Ev)].
  exact (NLB.decode_leafb_aview_vis W memc a v Ev).
Qed.

(* The shadow byte of an addressable byte is in RNG_W W. *)
Lemma ntlost_rng_sh1 : forall (W : world tfibsegs) memc a,
  range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 ->
  NLE.rng (NLK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) (NLC.shadow_addr a) 1.
Proof.
  intros W memc a HRA H0 H1.
  pose proof (NLB.decode_leafb_rng_shadow W memc a 1 HRA H0 ltac:(lia) H1) as H.
  replace (a + 1 - 1) with a in H by lia. rewrite Z.sub_diag, Z.add_0_l in H. exact H.
Qed.

(* A byte of the notice is application memory. *)
Lemma ntlost_app : forall p i, amem_range p 72 -> 0 <= p -> 0 <= i < 72 -> NLC.app_mem (p + i).
Proof.
  intros p i H H0 Hi. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in H.
  unfold NLC.app_mem, NLC.LOWMEM_END, NLC.HIGHMEM_BEG, NLC.APPMEM_END. lia.
Qed.

(* A shadow byte of a byte below 2 ^ 47 lies far below the stack. *)
Lemma ntlost_sh_far : forall x, 0 <= x < 2 ^ 47 -> 0 <= SHADOW_OFF + x / 8 < 2 ^ 46 - 9000.
Proof.
  intros x Hx. unfold SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D0.
  assert (D1 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* What the call leaves besides the journal: the callee-saved registers, every byte outside the leaf's ESTACK
   window below the call's sp, and presence. *)
Definition ntlost_R (regsT : bvmap 5 word) (W : world tfibsegs) (memT : word -> option byte)
    (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  aregs_preserved regsT regs2 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 4096 <= a < spZ regsT) ->
     aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
  (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a).

(* The facts after the call: the entry facts and the auipc value of the store to M.fly.on (its region's base). *)
Definition ntlost_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 4096 (2 ^ 47 - 72) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (A_HI 73, mkAF 6157476 6157476 2)] [] [].

Lemma ntlost_facts_ok : forall E sp p,
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 11) = p -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  bv_unsigned (ew E (A_HI 73)) = 6157476 ->
  2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> 4096 <= p <= 2 ^ 47 - 72 -> p mod 8 = 0 ->
  facts_ok E ntlost_facts.
Proof.
  intros E sp p U2 U11 E32 Uo Hsp Hsp16 Hp Hp8.
  unfold ntlost_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U11, Uo, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | reflexivity].
Qed.

Section lost. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma ntlost_val73 : VAL (A_HI 73) = 6157476.
Proof. vm_compute. reflexivity. Qed.

(* The region of M.fly.on, at the auipc value of its store. *)
Lemma ntlost_fly_ok : forall (W : world tfibsegs) m E,
  bv_unsigned (ew E (A_HI 73)) = VAL (A_HI 73) ->
  region_ok tfibsegs E (mrestrict (w_H W) m) nt_reg_fly.
Proof.
  intros W m E U. destruct nt_cvals as (_ & _ & _ & _ & _ & _ & _ & _ & _ & V73 & _).
  unfold nt_reg_fly, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U. unfold TB_M in V73.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (gx_rw_writable tfibsegs TG.G_HARNESS_B _ G_HARNESS_B_rw).
  apply nt_inG_M. unfold TB_M. lia.
Qed.

Lemma nt_lost : @nt_path fx rc B MT TC.N_ACK_LOST NT_LOST.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E ms md
  HC Ek HS HEI Elo Ed SHOK HJ KA0.
destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
  as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoffp & Hrd).
pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJc Hra Hra4 Hgp Htp H11 Hsp16 Hlo Hhi
    HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : NOTICE_STK = 8240) by reflexivity.
destruct (nt_m_lost timg_B Fr Bw n Bw' Ek Hm) as [HML HBw].
destruct nt_cvals as (V1 & V95 & VN & V36 & V13 & V37 & V38 & V39 & V40 & V73 & V72 & V74 & V75 & V77 & VB).
pose proof ntlost_val73 as V73n.
destruct Hrd as (Hvis & HRA & _ & Ham & _ & _).
assert (Usp : bv_unsigned (ew E 2) = spZ regs)
  by (rewrite (Elo 2%nat ltac:(lia)), (nt_E_reg regs NB Bw 2 2%bv eq_refl); reflexivity).
assert (U11 : bv_unsigned (ew E 11) = p).
{ rewrite (Elo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11 11%bv eq_refl), H11. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (Elo 32%nat ltac:(lia)); exact (nt_E_atom regs NB Bw 0 ltac:(lia))).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
(* run 1: the jump, a0 = p, `jal check_inflight_lost` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
  left. split; [unfold awr_byte; left; lia | lia]. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
assert (KA1 : nt_KA W memc (ms_mem ms1) (nt_Wn regs)).
{ apply (nt_KA_run _ _ W memc _ _ _ KA0 HFr HG).
  intros b wlo whi x Hin Hx. cbv beta.
  nt_win Hin Hx ltac:(rewrite ?Usp in Hx; unfold nt_Wn; lia). }
clear HF HFr HG.
(* the facts the leaf reads, at the call memory *)
pose proof (nt_tw_Wn W memc (ms_mem ms1) regs Bw ltac:(unfold TG.G_HARNESS_B_HI; lia) Htw KA1) as Htw1.
assert (HNB1 : garr8 segs (mrestrict (w_H W) (ms_mem ms1)) p (map DSpec.bz NB)).
{ apply (nt_garr8_keep W memc (ms_mem ms1) (nt_Wn regs) p _ KA1 HNB).
  intros a Ha. rewrite length_map, HNBL in Ha. change (Z.of_nat 72) with 72 in Ha.
  split; [lia|]. unfold nt_Wn. unfold decode_off_win in Hoffp. lia. }
assert (HRA1 : range_addressable (aview segs (w_H W) (ms_mem ms1)) SHADOW_OFF p 72).
{ apply (nt_ra_kept W memc (ms_mem ms1) p 72 (nt_Wn regs) HRA KA1).
  intros x Hx. pose proof (ntlost_sh_far x ltac:(lia)) as Hf. split; [lia|]. unfold nt_Wn. lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
(* the registers at the call *)
nt_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + 8708)) R1c ltac:(apply codeptr_val; exact HEI).
nt_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (spZ regs - 16)) R2c ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
nt_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) R3c
  ltac:(cbn [sv_denot]; rewrite (Elo 3%nat ltac:(lia)), (nt_E_reg regs NB Bw 3 (Z_to_bv 5 3) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact Hgp).
nt_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) R4c
  ltac:(cbn [sv_denot]; rewrite (Elo 4%nat ltac:(lia)), (nt_E_reg regs NB Bw 4 (Z_to_bv 5 4) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact Htp).
nt_reg HS (Z_to_bv 5 10) (Z_to_bv 64 p) R10c
  ltac:(cbn [sv_denot]; rewrite (Elo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11 (Z_to_bv 5 11) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact H11).
assert (R2u : bv_unsigned (YK11.getr (ms_regs ms1) (Z_to_bv 5 2)) = spZ regs - 16)
  by (rewrite R2c; apply unsigned_lit_small; lia).
assert (GSP : spZ (ms_regs ms1) = spZ regs - 16) by exact R2u.
(* the call of check_inflight_lost, through the G call kit and the leaf bridge *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 LILc.CHECK_INFLIGHT_LOST) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_call_leaf fx rc tfib_sink_head segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
    (ms_mem ms1) md1 k _ (YK11.getr (ms_regs ms1) 1) (ntlost_R (ms_regs ms1) W (ms_mem ms1)) HJ).
  intros memS IJ.
  eapply SRr_mono.
  { apply (@NLB.decode_leafb_journal fx rc tfib_sink_head B LAWS W (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly S W0
      memS md0 own lyc Sc md1 k (spZ regs - 16 - sp0) LILc.CHECK_INFLIGHT_LOST None [] (fun _ => Bw = Bw) IJ).
    - rewrite GSP. lia.
    - exact Hm16.
    - lia.
    - unfold ESTACK. lia.
    - change (YK0s.ret_ok (YK11.getr (ms_regs ms1) (Z_to_bv 5 1))). rewrite R1c.
      apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
    - change (YK11.getr (ms_regs ms1) (Z_to_bv 5 3) = w64 (as_gp B)). exact R3c.
    - change (YK11.getr (ms_regs ms1) (Z_to_bv 5 4) = w64 (as_tp B)). exact R4c.
    - intros a Ha. unfold NLK.in_wr in Ha. inversion Ha.
    - intros HPRE.
      pose proof (HLOST fx) as LF.
      unfold transport_leaf_at, LIL.transport_check_inflight_lost_cg in LF.
      specialize (LF lyc Sc W (ms_regs ms1) (ms_mem ms1) md1 p (spZ regs - 16 - 4096) n Bw Bw HPRE R10c).
      cbv zeta in LF.
      apply LF; clear LF.
      + lia.
      + exact Hp8.
      + rewrite <- HK68. pose proof (TWL.u_at_range NB 68 2) as R. change (8 * Z.of_nat 2) with 16 in R. exact R.
      + unfold TW.put.
        apply (NLB.decode_leafb_bytes_le W (ms_mem ms1) (p + 64) 4 (TI.n_counter n) (TW.u_at NB 64 4));
          [exact (nt_val4 _ p NB 64 HNB1 HNBL ltac:(lia) ltac:(lia)) | rewrite HK64; reflexivity | lia | lia].
      + unfold TW.put.
        apply (NLB.decode_leafb_bytes_le W (ms_mem ms1) (p + 68) 2 (TI.n_retry n) (TW.u_at NB 68 2));
          [exact (ntlost_val2 _ p NB 68 HNB1 HNBL ltac:(lia) ltac:(lia)) | rewrite HK68; reflexivity | lia | lia].
      + exact (ntlost_tw_csw W (ms_mem ms1) Bw Htw1).
      + exact HML.
      + rewrite R2u. apply (NLB.decode_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJ); lia.
      + rewrite R2u. unfold LILc.CHECK_INFLIGHT_LOST_FRAME. lia.
      + unfold NKA.off_stk. rewrite R2u.
        unfold LILc.CHECK_INFLIGHT_LOST_FRAME, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
      + exact (NLB.decode_leafb_asan_cells B HCELLS lyc Sc W (ms_mem ms1) md1 HAR1).
      + rewrite R2u. apply (@NLB.decode_leafb_app_stack rc). unfold LILc.CHECK_INFLIGHT_LOST_FRAME. lia.
      + rewrite R2u. apply (@NLB.decode_leafb_app_stack rc). lia.
      + unfold NKA.off_stk. rewrite R2u. unfold LILc.CHECK_INFLIGHT_LOST_FRAME, NLC.GOT_CELL_K. lia.
      + unfold NKA.off_stk. rewrite R2u. unfold LILc.CHECK_INFLIGHT_LOST_FRAME, NLC.CELL_K. lia.
      + unfold NKA.off_stk. rewrite R2u. unfold LILc.CHECK_INFLIGHT_LOST_FRAME.
        unfold decode_off_win in Hoffp. lia.
      + apply (NLB.decode_leafb_addressable W (ms_mem ms1) (p + 64) 4);
          [intros x Hx; apply HRA1; lia | lia | lia | unfold NLC.APPMEM_END; lia |].
        intros i Hi. replace (p + 64 + i) with (p + (64 + i)) by lia. apply ntlost_app; [exact Ham | lia | lia].
      + unfold NKA.off_stk. rewrite R2u. unfold LILc.CHECK_INFLIGHT_LOST_FRAME.
        unfold decode_off_win in Hoffp. lia.
      + apply (NLB.decode_leafb_addressable W (ms_mem ms1) (p + 68) 2);
          [intros x Hx; apply HRA1; lia | lia | lia | unfold NLC.APPMEM_END; lia |].
        intros i Hi. replace (p + 68 + i) with (p + (68 + i)) by lia. apply ntlost_app; [exact Ham | lia | lia].
      + rewrite R2u. apply (NLB.decode_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJ);
          unfold LILc.CHECK_INFLIGHT_LOST_FRAME; lia.
      + apply (ntlost_rng_row W (ms_mem ms1) Bw _ _ _ _ _ Htw1 TMAP_B_M);
          unfold LILc.CHECK_INFLIGHT_LOST_FLY_ON, TW.A_M_fly_on, TW.SZ_M; lia.
      + exact (proj1 (NLB.decode_leafb_rng_cells W)).
      + exact (proj2 (NLB.decode_leafb_rng_cells W)).
      + apply (ntlost_rng_sh1 W memc (p + 64)); [intros x Hx; apply HRA; lia | lia | lia].
      + apply (ntlost_rng_p W memc p (p + 64) 4 Hvis); lia.
      + apply (ntlost_rng_row W (ms_mem ms1) Bw _ _ _ _ _ Htw1 TMAP_B_M);
          unfold LILc.CHECK_INFLIGHT_LOST_FLY_COUNTER, TW.A_M_fly_counter, TW.SZ_M; lia.
      + apply (ntlost_rng_row W (ms_mem ms1) Bw _ _ _ _ _ Htw1 TMAP_B_M);
          unfold LILc.CHECK_INFLIGHT_LOST_FLY_RETRIES, TW.A_M_fly_retries, TW.SZ_M; lia.
      + apply (ntlost_rng_row W (ms_mem ms1) Bw _ _ _ _ _ Htw1 TMAP_B_g_cfg);
          unfold LILc.CHECK_INFLIGHT_LOST_MAX_RETRIES, TW.A_Cfg_max_retries, TW.SZ_g_cfg; lia.
      + apply (ntlost_rng_sh1 W memc (p + 68)); [intros x Hx; apply HRA; lia | lia | lia].
      + apply (ntlost_rng_p W memc p (p + 68) 2 Hvis); lia. }
  cbv beta. intros W2 c2 _ H. destruct H as (-> & regs2 & mem2 & md2 & Hc & IJ2 & HP & _ & Heff & Hgr & _).
  split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Hc|]. split; [exact IJ2|].
  unfold ntlost_R. split; [exact HP|]. split; [|exact Hgr].
  intros a Ha Hn. apply Heff; [exact Ha | intros Hx; apply Hn; unfold ESTACK in Hx; lia | intros Hw; inversion Hw]. }
cbv beta. intros W2 c2 _ H. destruct H as (-> & regs2 & mem2 & md2 & -> & HJ2 & HR2).
unfold ntlost_R in HR2. destruct HR2 as (HP2 & Heff2 & Hgr2).
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ _ ?pc _ _) _) _ =>
  replace pc with (Z_to_bv 64 (BASE + 8708)) by (symmetry; exact R1c) end.
(* the symbolic state at the return: the frame region kept *)
jafter_call_keep_pi HS 43%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  apply (region_kept_aview _ _ _ _ 2%nat (spZ regs)); [exact Usp | | exact Hgr2].
  intros a Ha. apply Heff2; [lia | rewrite GSP; lia]. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E 43 (map (YK11.getr regs2) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1)
  by (unfold E1; apply img_env_havoc; [exact HEI | rewrite length_map; vm_compute; lia]).
assert (E1lo : forall j, (j < 43)%nat -> ew E1 j = ew E j) by (intros j Hj; unfold E1; apply ew_havoc_old; exact Hj).
assert (Ed1 : ed E1 = ed (nt_E regs NB Bw)) by (unfold E1, havoc; cbn [ed]; exact Ed).
clearbody E1.
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite E1lo by lia; exact Usp).
assert (U11_1 : bv_unsigned (ew E1 11) = p) by (rewrite E1lo by lia; exact U11).
assert (E32_1 : ew E1 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite E1lo by lia; exact E32).
assert (U473 : bv_unsigned (ew E1 (A_HI 73)) = VAL (A_HI 73)) by (apply HEI1; unfold A_HI, A_TEXT, A_LIM; lia).
assert (U473n : bv_unsigned (ew E1 473) = VAL (A_HI 73)) by exact U473.
(* the region of M.fly.on and the facts of its base *)
pose proof (nt_add E1 _ _ nt_reg_fly HS ltac:(vm_compute; reflexivity)) as HS2. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
specialize (HS2 (ntlost_fly_ok W mem2 E1 U473)).
specialize (HS2 ltac:(cbn [all_disjoint]; split; [|exact I];
  unfold extent_disjoint, nt_reg_fly, nt_reg_frame;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U473, ?U473n, Usp1; unfold TB_M in V73; lia)).
rename HS2 into HS.
pose proof (nt_facts_set E1 _ _ ntlost_facts HS
  (ntlost_facts_ok E1 (spZ regs) p Usp1 U11_1 E32_1 ltac:(rewrite U473; exact V73n) Hsp Hsp16 ltac:(lia) Hp8)) as HS2.
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2. rename HS2 into HS.
assert (SHOK2 : sh_ok segs NT_Bx [] E1 (mrestrict (w_H W) mem2)) by (unfold sh_ok; constructor).
assert (KA2 : nt_KA W memc mem2 (nt_Zs regs Bw n)).
{ apply (nt_KA_step W memc (ms_mem ms1) mem2 (nt_Zs regs Bw n) (fun a => spZ regs - 16 - 4096 <= a < spZ regs - 16)).
  - exact (nt_KA_mono W memc _ _ _ (nt_Wn_Zs regs Bw n) KA1).
  - intros a Ha Hn. apply Heff2; [exact Ha | rewrite GSP; exact Hn].
  - exact Hgr2.
  - intros a Ha. left. lia. }
clear dependent ms1.
(* run 2: the store of 0 at M.fly.on, the epilogue, to `ret` *)
paj_run_tok RUN HS HJ2 SHOK2 YC4b.Bspan.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?U473, ?U473n in Ha.
    apply nt_inG_M. unfold TB_M in V73 |- *. lia. }
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp1 in Ha.
  left. split; [unfold awr_byte; left; lia | lia]. }
set (mdF := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdF. clear mat.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
assert (KAF : nt_KA W memc (ms_mem msF) (nt_Zs regs Bw n)).
{ apply (nt_KA_run _ _ W memc _ _ _ KA2 HFr HG).
  intros b wlo whi x Hin Hx. cbv beta.
  nt_win Hin Hx ltac:(rewrite ?Usp1, ?U473, ?U473n in Hx; first
    [ left; lia
    | right; unfold notice_wr; right; right; left; split; [exact Ek|];
      unfold twb_fld, TW.A_M_fly_on; unfold TB_M in V73 |- *; lia ]). }
clear HF HFr HG.
(* M.fly.on's 4 bytes at the return *)
pose proof (st_ok_pi_region_nth E1 _ (restrict (w_H W) msF) 0 _ HS eq_refl) as RGF.
cbn [ms_mem restrict] in RGF.
destruct RGF as (_ & _ & _ & HCH). cbn [YP09.r_base YP09.r_chunks base_val] in HCH.
apply Forall_cons_iff in HCH as [HCH _].
rewrite ?U473, ?U473n in HCH.
assert (HV4 : forall j, (j < 4)%nat ->
  aview segs (w_H W) (ms_mem msF) (TB_M + 96 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)).
{ intros j Hj. pose proof (nt_chunk_aview W (ms_mem msF) E1 (VAL (A_HI 73)) (-1636) 4 _ (Z.of_nat j) HCH ltac:(lia))
    as X.
  replace (VAL (A_HI 73) + -1636) with (TB_M + 96) in X by (unfold TB_M in V73 |- *; lia).
  rewrite X. f_equal; cbn [sv_denot]; do 4 (destruct j as [|j]; [vm_compute; reflexivity|]); lia. }
nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
  ltac:(cbn [sv_denot]; rewrite (E1lo 1%nat ltac:(lia)), (Elo 1%nat ltac:(lia)), (nt_E_reg regs NB Bw 1 1%bv eq_refl),
          Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HPF : aregs_preserved regs (ms_regs msF)).
{ apply (aregs_preserved_of_st_ok segs (w_H W) E1 _ msF regs (nt_vals NB Bw) HS).
  - split; [intros j Hj; rewrite (E1lo j ltac:(lia)), (Elo j ltac:(lia)); unfold nt_E; apply Eimg_low; unfold A_TEXT; lia
           | rewrite Ed1; reflexivity].
  - vm_compute. reflexivity. }
assert (HtwF : tw_at TMAP_B (aview segs (w_H W) (ms_mem msF)) Bw').
{ rewrite HBw. unfold TW.set_M_fly_on, TW.A_M_fly_on. rewrite Z.add_0_r.
  apply (nt_tw_set4 W memc (ms_mem msF) Bw TW.OFF_M TB_M TW.SZ_M 96 0 Htw TMAP_B_M);
    [lia | unfold TW.SZ_M; lia | exact HV4 |].
  intros x Hx Hn. pose proof KAF as [KAx _]. apply KAx.
  + pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia.
  + unfold nt_Zs. intros [Hz | Hz].
    * pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_HI in Hh. lia.
    * apply Hn. unfold notice_wr in Hz.
      unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hz, Ek.
      destruct Hz as [(E' & _) | [(E' & _) | [(_ & Hz) | [(E' & _) | [(E' & _) | (E' & _)]]]]]; try lia.
      unfold twb_fld, TW.A_M_fly_on in Hz. lia. }
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
exact (nt_close B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
  (ms_regs msF) (ms_mem msF) mdF HC HJ2 KAF HtwF HPF RF1 mat').
Qed.
End lost.
