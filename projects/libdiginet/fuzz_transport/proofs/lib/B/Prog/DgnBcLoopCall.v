(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths and module names changed; 281 of its 341 lines of code are new or changed and 1079 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the entry state with no region and no fact (cc_entry4), the register read cc_reg and the word lemma cc_rdword_frame of reac-repacer/fuzz_uci's lib/A/Prog/check_clamp_cgW.v, at libdiginet/fuzz_frame's image A and the loop head of diginet_body_check; the call of diginet_msg_next through its caller-journal contract. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of this unit's lib/A/Prog/DgnBcLoopCall.v: module paths lib/B (the image-B core's YB1v / YE2k / YCbq / YC5d, lib/B/Prog/PaJournal.v, the listing files lib/B/Prog/FrameBSyms.v .. FrameBCJ.v, lib/B/Prog/CanKit.v, DgnFrameCg.v, diginet_body_check_cg.v, diginet_msg_next_cg.v, DgnBcCut.v, DgnBcLoopCut.v) and the listing names of image B (frameb_listing, PI_frameb, frameb_sigma FB_diginet_msg_next); image B's numbers (FRAME_BC_STK = 4272, diginet_msg_next's window FRAME_MN_STK = 64, the return address 0x83020); and the two image-B premises of diginet_msg_next's contract, c mod 8 = 0 and m mod 8 = 0, from F mod 32 = 0. *)
(* DgnBcLoopCall (image B): Lemma bl_call : bl_call_stmt (lib/B/Prog/DgnBcLoopCut.v), the call half of one turn of
   the msg_next loop of diginet_body_check, offsets +0x16c .. +0x178 of the listing lib/B/Prog/DgnDecodeBList.v
   (fuzz_decode.asan-ubsan 0x82adc .. 0x82ae8).

   What the code does. +0x16c `mv a0, s5`: a0 := c = F + 32; +0x170 `mv a1, s6`: a1 := m = F + 96; +0x174
   `jal diginet_msg_next`: ra := the address of +0x178, pc := 0x82328. No store, no load.

   One run of the token engine (lib/B/Prog/DgnDecodeBPaLib.v paj_run_tok) from a symbolic state with no region and no
   fact covers the two moves and stops at the call. The callee's contract (lib/B/Prog/diginet_msg_next_cg.v, a
   premise) is applied at the walk's own journal. Its two image-B premises c mod 8 = 0 and m mod 8 = 0 hold because
   F mod 32 = 0 (bc_fix) and c = F + 32, m = F + 96. Its post (DgnDecodeBCg.v decode_cg_post) gives the state at
   +0x178:
     - the journal and the blocks as the post states them, the meter by mo_le_trans;
     - the 13 saved words and the two slots at sp1 + 16 / sp1 + 24 lie above alloc_ceiling and outside the callee's
       window [sp1 - TRANS_MN_STK, sp1) = [sp1 - 64, sp1) (acall_kept, clause 1);
     - the frame's last word and the shadow bytes of c and m lie in the frame's range or its shadow range and
       outside the written range, which holds frame bytes only (acall_kept, clause 4; in_app F 256);
     - the body bytes, placed by trans_src_ok at the cut's state (bc_cur), apart from the frame
       (trans_src_ok_disj_own) and outside the callee's window: trans_src_ok_acall keeps them and the placement;
     - the callee-saved registers are the run's (the run writes a0, a1 and ra only), which are the loop head's. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0p YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib DgnTransportBCJ.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_msg_next_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import CanKit DgnBcCut DgnBcLoopCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module BMN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. Geometry                                                         *)
(* ------------------------------------------------------------------ *)

(* An eight-byte word of a view, kept by a step that keeps its eight bytes. *)
Lemma bl_rdword_frame : forall (rd rd' : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a Hk. unfold rdword.
  pose proof (Hk 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  rewrite K0, (Hk 1 ltac:(lia)), (Hk 2 ltac:(lia)), (Hk 3 ltac:(lia)), (Hk 4 ltac:(lia)),
          (Hk 5 ltac:(lia)), (Hk 6 ltac:(lia)), (Hk 7 ltac:(lia)). reflexivity.
Qed.

(* A range of an eight-aligned frame whose granules lo .. hi - 1 have the shadow byte 0 is addressable. *)
Lemma bl_ra_zero : forall (rd : Z -> option Z) F q n lo hi,
  0 <= F -> F mod 8 = 0 -> F + 8 * lo <= q -> q + n <= F + 8 * hi ->
  (forall i, lo <= i < hi -> rd (SHADOW_OFF + F / 8 + i) = Some 0) ->
  range_addressable rd SHADOW_OFF q n.
Proof.
  intros rd F q n lo hi HF0 HF8 Hlo Hhi HZ x Hx.
  exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr.
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
  set (f := F / 8) in *.
  assert (Ex : x / 8 = f + (x - F) / 8).
  { replace x with (f * 8 + (x - F)) at 1 by lia. apply Z.div_add_l. lia. }
  rewrite Ex, Z.add_assoc. apply HZ. split.
  - apply Z.div_le_lower_bound; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

(* The eight-aligned hull of the shadow bytes of a range in [F + 32, F + 192) of a 32-aligned frame lies inside the
   frame's 32 shadow bytes. *)
Lemma bl_hull : forall (rd : Z -> option Z) F q n,
  0 <= F -> F mod 32 = 0 -> F + 32 <= q -> 0 < n -> q + n <= F + 192 ->
  (forall i, 0 <= i < 32 -> rd (shadow_addr F + i) <> None) ->
  shadow_hull_vis rd q n.
Proof.
  intros rd F q n HF0 HF32 Hlo Hn Hhi HV s Hs.
  unfold shadow_addr, SHADOW_OFF in *.
  pose proof (Z.div_mod F 32 ltac:(lia)) as DF. rewrite HF32, Z.add_0_r in DF.
  assert (EF8 : F / 8 = 4 * (F / 32)).
  { rewrite DF at 1. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by ring. apply Z.div_mul. lia. }
  rewrite EF8 in HV.
  set (g := F / 32) in *.
  pose proof (Z.div_mod q 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia)) as M2.
  set (a := q / 8) in *. set (b := (q + n - 1) / 8) in *.
  set (r1 := q mod 8) in *. set (r2 := (q + n - 1) mod 8) in *.
  pose proof (Z.div_mod (2147450880 + a) 8 ltac:(lia)) as D3.
  pose proof (Z.mod_pos_bound (2147450880 + a) 8 ltac:(lia)) as M3.
  pose proof (Z.div_mod (2147450880 + b) 8 ltac:(lia)) as D4.
  pose proof (Z.mod_pos_bound (2147450880 + b) 8 ltac:(lia)) as M4.
  set (c := (2147450880 + a) / 8) in *. set (d := (2147450880 + b) / 8) in *.
  set (r3 := (2147450880 + a) mod 8) in *. set (r4 := (2147450880 + b) mod 8) in *.
  replace s with (2147450880 + 4 * g + (s - (2147450880 + 4 * g))) by ring.
  apply HV. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic state at +0x16c                                     *)
(* ------------------------------------------------------------------ *)

(* Two register moves and the call, so no region and no fact. *)
Definition ss_bl : sstate := mkSS BC_LOOP sr_atoms [] None (mkFacts [] [] []).
(* The empty shadow span: the run reads no shadow byte. *)
Definition BL_B0 : Z * Z := (0, 0).

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac.
   (YP0l.st_ok is the engine's state relation; DgnLib.st_ok, the model's running status, is also in scope.) *)
Ltac bl_reg HS r v H tac :=
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

(* A callee-saved register of R3, from a register equality at R2 and aregs_preserved R2 R3. *)
Ltac bl_keep :=
  lazymatch goal with |- YK11.getr ?R3x ?r = ?v =>
    match goal with HP : aregs_preserved ?R2x R3x, Hr : YK11.getr ?R2x r = v |- _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      exact (eq_trans (HP z ltac:(hnf; lia)) Hr) end end.

Section lcall. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The environment: the thirty-two registers as atoms 0 .. 31, the shadow base as atom 32, and the image's own values
   above A_TEXT. *)
Definition bl_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).

Lemma bl_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (bl_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold bl_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma bl_env_img : forall regs, img_env VAL A_LIM (bl_E regs).
Proof. intros regs. unfold bl_E. apply Eimg_env. Qed.

Lemma bl_agree : forall regs, env_agree 32 (Ereg regs [w64 SHADOW_OFF]) (bl_E regs).
Proof.
  intros regs. split; [intros n Hn; unfold bl_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

Lemma bl_entry : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (bl_E regs) ss_bl
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + BC_LOOP)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_bl.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    repeat split; exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The half                                                         *)
(* ------------------------------------------------------------------ *)

Lemma bl_call : @bl_call_stmt fx rc B MT.
Proof.
unfold bl_call_stmt.
intros LAWS0 MN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F W2 regs2 mem2 md2
  ly2 S2 cp st mj Q HFIX HCUR HREG Hcp Hst Hcur Hmjl Hmj Hcm HQ.
destruct LAWS0 as (HCELLS & LAWS & MTL & MTF & ASF & FFL & HGU & HGE & HRU & HRE).
destruct HFIX as (HJ0 & Hret & Hra & Hgp & Htp & Hsp16 & Hstk & Hsp0 & Hbody & Hblk & Hcnt & Hnev & Esp1 & EF &
  HF0 & HF32 & HFc & HFapp).
destruct HCUR as (HJ1 & Hperm & Hmo & Hsaved & Hlen & Hslot & HFLw & Hbb & Hsrc2).
unfold bc_cm_zero in Hcm.
destruct HREG as (((R2 & R3 & R4 & R8 & R9 & R23 & R24) & R19 & R25) & R18 & R20 & R21 & R22 & R26 & R27).
unfold BC_FBYTES in HFc, HFapp, HFLw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & Hnev0 & _).
pose proof HJ1 as (HAR2 & Hly2 & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk1 & _).
pose proof Hstk1 as (_ & _ & Hceil1 & Hslo1 & Hshi1 & H47 & _).
assert (HBS : TRANS_BC_STK = 4272) by reflexivity.
assert (HMS : BMN.TRANS_MN_STK = 64) by reflexivity.
rewrite HBS in Hslo1.
destruct (can_sp1_facts (spZ regs - TRANS_BC_FRAME) ltac:(unfold TRANS_BC_FRAME; lia)
  ltac:(rewrite Zminus_mod, Hsp16; reflexivity)) as (Hsp1a & Hsp1b & Hsp1c).
rewrite <- Esp1 in Hsp1a, Hsp1b, Hsp1c. unfold TRANS_BC_FRAME in Hsp1a.
assert (HF8 : F mod 8 = 0) by exact (mod32_mod8 F HF32).
(* the class-2 frame of the walk's journal, at the state of the cut *)
assert (Hin : In (TRANS_BC_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose proof Hly2 as (_ & _ & _ & _ & _ & ELF & _).
assert (EFA : frame_addr ly2 TRANS_BC_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ TRANS_BC_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
change (fs_frame_bytes TRANS_BC_CID / 8) with 32 in HFsh.
change (fs_frame_bytes TRANS_BC_CID) with 256 in HFb.
rewrite EFA in HFb, HFsh.
(* the body, when there are some bytes: placed at the cut's state (bc_cur), apart from the frame (trans_src_ok_disj_own
   at the caller's state), outside this call's window (bc_fix's decode_off_win) *)
pose proof HJ0 as (HAR0 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo2 & Ehi2 & _).
assert (Hfa2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite ELF; reflexivity).
assert (Hsep : (0 < length bb)%nat -> body + Z.of_nat (length bb) <= F \/ F + 256 <= body).
{ intros HL. pose proof (trans_src_ok_disj_own B LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 TRANS_BC_CID pos body
    (Z.of_nat (length bb)) HAR0 HAR2 Hfrs Hperm Hfa2 (proj1 (Hblk HL)) ltac:(lia)) as Hd.
  rewrite EFA in Hd. change (fs_frame_bytes TRANS_BC_CID) with 256 in Hd. exact Hd. }
assert (Hbw : (0 < length bb)%nat -> body + Z.of_nat (length bb) <= spZ regs - TRANS_BC_STK \/ spZ regs <= body)
  by (intros HL; exact (proj2 (Hblk HL))).
(* +0x16c .. +0x174: the two moves, up to the call *)
pose proof (bl_entry W2 regs2 mem2) as HS.
assert (HEI : img_env VAL A_LIM (bl_E regs2)) by apply bl_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (bl_E regs2) (mrestrict (w_H W2) mem2)) by constructor.
pose proof (paj_run (SK := YE2k.tfib_sink_head) (PI := PI_transportb) B LAWS) as RUN.
paj_run_tok RUN HS HJ1 SHOK BL_B0.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_nil. }
lazymatch type of HS with OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?msx) =>
  set (ms1 := msx) in * end.
(* the run stores nothing; HJ1 is now the journal after it *)
lazymatch goal with HFx : frame_of ?Ex ?rsx mem2 (ms_mem ms1) |- _ =>
  assert (Emem : ms_mem ms1 = mem2) by exact (frame_of_read_only Ex rsx mem2 (ms_mem ms1) eq_refl HFx) end.
rewrite Emem in HJ1.
(* the registers at the call *)
assert (HPR : aregs_preserved regs2 (ms_regs ms1)).
{ lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
    apply (aregs_preserved_of_st_ok sg Hh Ex ssx msx regs2 [w64 SHADOW_OFF] HS (bl_agree regs2));
    vm_compute; reflexivity end. }
bl_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + BL_RET)) R1 ltac:(apply codeptr_val; exact HEI).
bl_reg HS (10%bv : bv 5) (w64 (F + 32)) R10
  ltac:(cbn [sv_denot]; rewrite (bl_ew_reg regs2 21 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R21).
bl_reg HS (11%bv : bv 5) (w64 (F + 96)) R11
  ltac:(cbn [sv_denot]; rewrite (bl_ew_reg regs2 22 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R22).
assert (Q2 : YK11.getr (ms_regs ms1) 2 = w64 sp1) by exact (eq_trans (HPR 2 ltac:(hnf; lia)) R2).
assert (Q3 : YK11.getr (ms_regs ms1) 3 = w64 (as_gp B))
  by exact (eq_trans (eq_trans (HPR 3 ltac:(hnf; lia)) R3) Hgp).
assert (Q4 : YK11.getr (ms_regs ms1) 4 = w64 (as_tp B))
  by exact (eq_trans (eq_trans (HPR 4 ltac:(hnf; lia)) R4) Htp).
assert (Hsp : spZ (ms_regs ms1) = sp1) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (EBR : BASE + BL_RET = 574068) by (vm_compute; reflexivity).
(* the premises of diginet_msg_next's contract *)
assert (Pret : YK0s.ret_ok (YK11.getr (ms_regs ms1) 1)).
{ rewrite R1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold BL_RET, AF_diginet_body_check; lia | reflexivity]. }
assert (Pra : 4096 <= raZ (ms_regs ms1)) by (unfold raZ; rewrite R1, EBR, unsigned_lit_small by lia; lia).
assert (Psp16 : spZ (ms_regs ms1) mod 16 = 0) by (rewrite Hsp; exact Hsp1c).
assert (Pwin1 : spZ regs - TRANS_BC_STK <= spZ (ms_regs ms1) - BMN.TRANS_MN_STK) by (rewrite Hsp, HBS, HMS; lia).
assert (Pwin2 : spZ (ms_regs ms1) <= spZ regs) by (rewrite Hsp; lia).
assert (Pblk : (0 < length bb)%nat -> trans_src_ok B ly2 S2 W2 mem2 body (Z.of_nat (length bb))) by exact Hsrc2.
assert (Pbw : (0 < length bb)%nat -> decode_off_win (ms_regs ms1) BMN.TRANS_MN_STK body (Z.of_nat (length bb))).
{ intros HL. pose proof (Hbw HL) as Hw. rewrite HBS in Hw. unfold decode_off_win. rewrite Hsp, HMS. lia. }
assert (Pfk1 : decode_in_fake ly2 S2 (F + 32) BMN.TRANS_MN_CUR_SIZE).
{ exists TRANS_BC_CID, pos. split; [exact Hin|]. rewrite EFA. change (fs_frame_bytes TRANS_BC_CID) with 256.
  unfold BMN.TRANS_MN_CUR_SIZE. lia. }
assert (Pfk2 : decode_in_fake ly2 S2 (F + 96) BMN.TRANS_MN_MSG_SIZE).
{ exists TRANS_BC_CID, pos. split; [exact Hin|]. rewrite EFA. change (fs_frame_bytes TRANS_BC_CID) with 256.
  unfold BMN.TRANS_MN_MSG_SIZE. lia. }
assert (Ptw : forall q n, F <= q -> q + n <= F + 256 ->
  decode_twr_ok B TRANS_BC_STK (spZ regs) [] lyc Sc ly2 S2 [(TRANS_BC_CID, pos)] W2 mem2 (spZ (ms_regs ms1)) q n).
{ intros q n Hq1 Hq2 a Ha. rewrite Hsp.
  destruct (HFb a ltac:(lia)) as (Hp & Ho).
  split; [|split; [exact Hp | split; [exact Ho|]]].
  - unfold awr_byte. right; right; right. unfold in_frames. exists TRANS_BC_CID, pos.
    split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes TRANS_BC_CID) with 256. lia.
  - unfold ESTACK. lia. }
assert (Prd : forall q n lo hi, F + 8 * lo <= q -> 0 < n -> q + n <= F + 8 * hi -> 4 <= lo -> hi <= 24 ->
  (forall i, lo <= i < hi -> aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + i) = Some 0) ->
  decode_rd_ok W2 mem2 q n).
{ intros q n lo hi Hq1 Hn Hq2 Hlo Hhi HZ. unfold decode_rd_ok.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
  - exact (bl_ra_zero _ F q n lo hi ltac:(lia) HF8 Hq1 Hq2 HZ).
  - apply (bl_hull _ F); [lia | exact HF32 | lia | lia | lia |].
    intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
    destruct HFapp as (Hap1 & [HL | [HH1 HH2]]).
    + left. unfold kLowShadowBeg in HL. lia.
    + right. unfold kHighMemBeg in HH1. unfold ASAN_CEIL in HH2. lia.
  - lia.
  - lia. }
assert (Prd1 : decode_rd_ok W2 mem2 (F + 32) BMN.TRANS_MN_CUR_SIZE).
{ unfold BMN.TRANS_MN_CUR_SIZE. apply (Prd _ _ 4 8); try lia. intros i Hi. apply Hcm. lia. }
assert (Prd2 : decode_rd_ok W2 mem2 (F + 96) BMN.TRANS_MN_MSG_SIZE).
{ unfold BMN.TRANS_MN_MSG_SIZE. apply (Prd _ _ 12 17); try lia. intros i Hi. apply Hcm. lia. }
assert (Pow1 : decode_off_win (ms_regs ms1) BMN.TRANS_MN_STK (F + 32) BMN.TRANS_MN_CUR_SIZE)
  by (left; rewrite Hsp, HMS; unfold BMN.TRANS_MN_CUR_SIZE; lia).
assert (Pow2 : decode_off_win (ms_regs ms1) BMN.TRANS_MN_STK (F + 96) BMN.TRANS_MN_MSG_SIZE)
  by (left; rewrite Hsp, HMS; unfold BMN.TRANS_MN_MSG_SIZE; lia).
assert (Pnev : st_nev Sc + 0 + BMN.TRANS_MN_EV <= EV_MAX) by (unfold BMN.TRANS_MN_EV, TRANS_BC_EV in *; lia).
(* image B's premises of the contract: c = F + 32 and m = F + 96 are multiples of 8 *)
assert (Pc8 : (F + 32) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite HF8; reflexivity).
assert (Pm8 : (F + 96) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite HF8; reflexivity).
(* +0x174: the call, at the pc the contract names *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (@cfg_at fx segs (transportb_sigma TB_diginet_msg_next) rg mm mdx) Qx) end.
rewrite Emem.
pose proof (MN fx) as MNf. unfold BMN.transport_diginet_msg_next_cg in MNf.
eapply SRr_bind.
{ exact (MNf TRANS_BC_STK (spZ regs) [] lyc Sc W memc mdc [(TRANS_BC_CID, pos)] ly2 S2 W2 mem2 _ 0 (ms_regs ms1)
    (F + 32) (F + 96) body bb mj cp st HJ1 Pret Pra Q3 Q4 R10 R11 Psp16 Pwin1 Pwin2
    ltac:(lia) ltac:(lia) Pc8 Pm8 Hcp Hst Hcur Hmjl Hmj Hbb Pblk Pbw Pfk1 Pfk2
    (Ptw (F + 32) BMN.TRANS_MN_CUR_SIZE ltac:(lia) ltac:(unfold BMN.TRANS_MN_CUR_SIZE; lia))
    (Ptw (F + 96) BMN.TRANS_MN_MSG_SIZE ltac:(lia) ltac:(unfold BMN.TRANS_MN_MSG_SIZE; lia))
    Prd1 Prd2 Pow1 Pow2
    ltac:(left; unfold BMN.TRANS_MN_CUR_SIZE; lia)
    ltac:(intros HL; pose proof (Hsep HL); unfold BMN.TRANS_MN_CUR_SIZE; lia)
    ltac:(intros HL; pose proof (Hsep HL); unfold BMN.TRANS_MN_MSG_SIZE; lia)
    Pnev). }
(* +0x178: the post of the call *)
intros W3 c3 _ HPOST.
unfold BMN.trans_mn_post, decode_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e & -> & He & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
  Ha03 & Hc3 & Hm3).
assert (He0 : e = 0) by (unfold BMN.TRANS_MN_EV in He; lia). subst e.
change (0 + 0) with 0 in HJ3.
rewrite Hsp, HMS in HK3.
pose proof HK3 as HK3'.
destruct HK3 as (K1 & K2 & _ & K4 & _ & _).
(* the body after the call: its bytes and its placement (trans_src_ok_acall) *)
assert (HSRC3 : (0 < length bb)%nat -> trans_src_ok B ly3 S3 W3 mem3 body (Z.of_nat (length bb)) /\
  (forall a, body <= a < body + Z.of_nat (length bb) -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a)).
{ intros HL. pose proof HJ3 as (HAR3 & Hly3 & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & ELF3 & _ & _ & _ & Elo3 & Ehi3 & _).
  apply (trans_src_ok_acall B LAWS HGU HGE HRU HRE ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md3 (sp1 - 64) sp1
           (BMN.trans_mn_wr (F + 32) (F + 96)) body (Z.of_nat (length bb)) HAR2 HAR3 Hperm3 Hfr3).
  - intros c p. unfold frame_addr. rewrite ELF3, ELF. reflexivity.
  - rewrite Elo3, Elo2. reflexivity.
  - rewrite Ehi3, Ehi2. reflexivity.
  - exact HK3'.
  - intros a Ha HE. pose proof (Hsep HL). unfold BMN.trans_mn_wr in HE. lia.
  - intros a Ha HE. unfold BMN.trans_mn_wr in HE.
    destruct HFapp as (_ & [HL' | [HH1 HH2]]); unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *;
      lia.
  - pose proof (Pbw HL) as Hw. unfold decode_off_win in Hw. rewrite Hsp, HMS in Hw. exact Hw.
  - exact (Hsrc2 HL).
  - lia. }
rewrite R1.
apply (HQ W3 regs3 mem3 md3 ly3 S3).
assert (HPall : aregs_preserved regs2 regs3) by exact (aregs_preserved_trans _ _ _ HPR HP3).
(* where the saved words lie *)
assert (HSo : forall o, In o BC_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold BC_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
unfold bl_after.
split; [|split; [|split; [exact Ha03 | split; [exact Hc3 | split; [exact Hm3|]]]]].
- (* the walk's own journal and the bytes it carries *)
  unfold bc_cur.
  split; [exact HJ3|].
  split; [exact (Permutation_trans Hperm3 Hperm)|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
  split.
  { rewrite Forall_forall in Hsaved |- *. cbv beta in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
    pose proof (HSo o Ho) as Hob.
    apply bl_rdword_frame. intros i Hi. apply K1; lia. }
  split.
  { rewrite <- Hlen. apply bl_rdword_frame. intros i Hi. apply K1; lia. }
  split.
  { rewrite <- Hslot. apply bl_rdword_frame. intros i Hi. apply K1; lia. }
  split.
  { unfold BC_FBYTES. rewrite <- HFLw. apply bl_rdword_frame. intros i Hi.
    apply (K4 TRANS_BC_CID pos _ Hin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes TRANS_BC_CID) with 256. lia.
    - unfold BMN.trans_mn_wr. lia. }
  split.
  { destruct (Nat.eq_dec (length bb) 0) as [E0|E0].
    - apply length_zero_iff_nil in E0. rewrite E0. apply garr8_nil.
    - eapply garr8_frame; [exact Hbb|]. intros a Ha. rewrite length_map in Ha.
      eapply mbyte_of_aview. exact (proj2 (HSRC3 ltac:(lia)) a ltac:(lia)). }
  intros HL. exact (proj1 (HSRC3 HL)).
- (* the loop's registers *)
  unfold bc_regs_loop, bc_regs_scan, bc_regs_rel.
  repeat match goal with |- _ /\ _ => split end.
  all: bl_keep.
- (* the shadow bytes of c and m *)
  intros i Hi. rewrite <- (Hcm i Hi).
  apply (K4 TRANS_BC_CID pos _ Hin).
  + right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes TRANS_BC_CID / 8) with 32.
    unfold shadow_addr. lia.
  + unfold BMN.trans_mn_wr.
    pose proof (Z.div_mod F 8 ltac:(lia)) as D8. rewrite HF8, Z.add_0_r in D8.
    set (f8 := F / 8) in *.
    destruct HFapp as (_ & [HL | [HH1 HH2]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.
End lcall.
