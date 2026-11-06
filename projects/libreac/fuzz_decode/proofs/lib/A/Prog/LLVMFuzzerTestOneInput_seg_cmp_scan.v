(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* LLVMFuzzerTestOneInput_seg_cmp_scan: the scan loop L2 of the cmp segment of the image-A walk of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput, cmp_scan : from cmp_q624 (+0x624, the loop head, entered when the plain check refused) the
   machine SRr-realizes cmp_q734 (+0x734) (lib/A/Prog/LLVMFuzzerTestOneInput_seg_cmp.v).

   The code (offsets from DEC_A_LLVMF, lib/A/Prog/DecodeList.v:421-441, map-code.md section 2): the loop head +0x624
   `srli a4,a1,3; add a4,a4,s2; lb a4,0(a4); bnez a4,+0x658` is the shadow check of the byte at a1 (slow path +0x658
   `andi a5,a1,7; blt a5,a4,+0x634; mv a0,a1; jal __asan_report_load1`, never stepped); +0x634 `lbu a4,0(a3)`,
   s9 one down, a1 one up, `a2 |= (a4 != 0xa5)`, a3 one up, `bnez s9,+0x624` (+0x650); on exit +0x654 `j +0x668`,
   +0x668 `bnez a2,+0xa4c` (abort), +0x66c `addi a1,s4,50; sd a1,64(s1)`, +0x674 `blez a0,+0x734`.

   How it is proved. SRr_loopZ (lib/Reusable/YA0n.v:95) over j, the bytes already read, with the measure olen - j.
   The invariant cs_P j at +0x624: a1 = a3 = out + j, s9 = olen - j, a2 = 0, a0 = -1, the shadow base in s2, a7 =
   out, s4 = res, the frame registers, dec_a_core at the current state, and the memory equal at every address to the
   one cmp_q624 gives. Each iteration seats a fresh symbolic state ss_cs (registers as atoms of their own values, a0
   and a2 pinned to the literals -1 and 0; atom 18 the shadow base; atom 11 (a1) carries the shadow entry of the one
   byte at out + j, from AR's block law for (out, olen); atom 13 (a3) the read-only region holding that byte, 0xa5
   by dec_a_filled), runs it with the token engine (the shadow check's slow block is covered by the entry, so no
   obligation is left) to the back edge and splits on `bnez s9`. Taken: one more step reaches +0x624 with cs_P at
   j + 1 (nothing is stored: every region is read-only, so the memory agrees at every address). Not taken (s9 = 0):
   the run goes on through +0x654 / +0x668 / +0x66c / +0x674 to +0x734 with a writable 8-byte region at s1 + 64 (the
   store of res + 50); the engine decides both exit branches itself (a2 is the literal 0: every byte read is 0xa5;
   a0 is the literal -1), so the abort edge is refuted, never stepped. The store changes only s1 + 64 .. s1 + 72
   (kept_of_frame), and every byte cmp_q734 reads lies below alloc_ceiling (the payload and the copy are heap blocks,
   the fake frame and its shadow, the mode's table, which dec_crt_cells pins in the image) or is a saved word or
   another spill slot.

   Steps follow the scan loop L6 of this walk (LLVMFuzzerTestOneInput_seg_exit_scan.v, sc_loop: the seat, the run,
   the split, the pointwise memory) and libreac/fuzz_boxreg's ReadName.v (pb_read_name, 1d92330b7ad: paj_run_tok,
   psrr_branch_tok, st_ok_pi_add_region / st_ok_pi_add_fact, kept_of_frame, field_of_region). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0s YI00 YO09 YM05 YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require DecodeShape Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
PaRun PaShadow PaJournal PaStep DecodeSyms DecodeList DecodeAddr DecodePa DecodeImg DecodePaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import YC1g YC1h YC1i YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require
reac_upstream_channels_cg reac_decode_plain_le_c reac_upstream_channels_c reac_frame_inspect_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import LLVMFuzzerTestOneInput_seg_cmp_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module CPlain := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_plain_le_c.
Module CChan := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_c.
Module CInsp := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_inspect_c.
Module LUpChannels := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_cg.
(* YC4b switches lia's division handling off for its importers; this file's arithmetic needs it (ReadName.v's line). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                               *)
(* ------------------------------------------------------------------ *)

(* At +0x624, iteration j: every register is the atom of its own value, but a0 and a2 are pinned to the literals -1
   and 0; atom 18 (s2) is the shadow base; atom 11 (a1, which the shadow check reads) and atom 13 (a3, which the load
   reads) are both out + j; the byte at a3 is a read-only region holding the fill. *)
Definition cs_reg : YP09.region := YP09.mkRegion (Some 13%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit DEC_FILL))].
Definition cs_facts : facts := mkFacts [(18%nat, mkAF SB SB 0); (11%nat, PTR 0); (13%nat, PTR 0)] [] [].
Definition cs_regs : list sv := sr_set (sr_set sr_atoms 10%bv (SLit (-1))) 12%bv (SLit 0).
Definition ss_cs : sstate := mkSS 0x624 cs_regs [cs_reg] None cs_facts.
(* The shadow entry of the byte at a1. *)
Definition cs_SH : list shent := [mkSHE 11 0 1].
(* On the exit path: the 8-byte spill slot s1 + 64 that +0x670 writes, and the range of s1 (the realigned stack
   pointer: above alloc_ceiling, below 2 ^ 47, 32-aligned), which keeps its window off the shadow span. *)
Definition cs_s64 : YP09.region := YP09.mkRegion (Some 9%nat) 64 72 64 72 [].
(* 140735332483072 = 0x7fff7f800000 is asan_consts' lower bound of alloc_ceiling (lib/Reusable/YCbq.v:467), the
   fact cmp_facts0 states for atom 9; a closed literal, so that the engine's static check computes. *)
Definition cs_f9 : afact := mkAF 140735332483072 (2 ^ 47) 5.
(* The registers the loop never writes and the invariant reads. *)
Definition cs_keep : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 17%bv; 18%bv; 19%bv; 20%bv; 21%bv; 27%bv].

(* A read-only region list: the run's memory agrees with the old one at every address. *)
Lemma cs_frame_ro : forall E (rs : smem) (m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro HF x. apply HF. intros (r & Hin & Hr).
rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.
(* The write rights of read-only regions. *)
Ltac cs_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]).
(* The model term after a run, named and opaque (it doubles at every run otherwise). *)
Ltac cs_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    let mdv := fresh "mdv" in set (mdv := mdx) in *; clearbody mdv end.
(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac cs_reg_at HS r v H tac :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : YK11.getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
Ltac cs_kin := try unfold cs_keep; cbn [In]; repeat (first [left; reflexivity | right]).
(* A register the run kept: KR (regs_kept_of_st_ok_pi), then the hypothesis that gives its old value. *)
Ltac cs_kept KR := etransitivity; [apply KR; cs_kin | eassumption].
(* The memory after a run of read-only regions agrees with the one before (closed region list for vm_compute). *)
Ltac cs_km HF KM :=
  lazymatch type of HF with frame_of ?Ex ?rs ?m0 ?m1 =>
    pose proof (cs_frame_ro Ex rs m0 m1 ltac:(vm_compute; reflexivity) HF) as KM end.

Section x. Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

(* ------------------------------------------------------------------ *)
(* 2. Memories that agree                                               *)
(* ------------------------------------------------------------------ *)

Lemma cs_aview_pt : forall H (m m2 : word -> option byte), (forall x, m2 x = m x) ->
  forall a, aview decodesegs0 H m2 a = aview decodesegs0 H m a.
Proof. intros H m m2 Hpt a. apply aview_eq_of. unfold mrestrict. rewrite (Hpt (Z_to_bv 64 a)). reflexivity. Qed.
Lemma cs_apresent_pt : forall H (m m2 : word -> option byte), (forall x, m2 x = m x) ->
  forall a, apresent H m a -> apresent H m2 a.
Proof. intros H m m2 Hpt a [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hpt. exact Hb. Qed.
Lemma cs_rdword_pt : forall (r r2 : reader) a, (forall x, r2 x = r x) -> rdword r2 a = rdword r a.
Proof. intros r r2 a Hr. unfold rdword. rewrite !Hr. reflexivity. Qed.
Lemma cs_garr8_pt : forall H (m m2 : word -> option byte) base l, (forall x, m2 x = m x) ->
  garr8 decodesegs0 (mrestrict H m) base l -> garr8 decodesegs0 (mrestrict H m2) base l.
Proof.
intros H m m2 base l Hpt HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. rewrite (mbyte_of_aview decodesegs0 H H m m2 _ (cs_aview_pt H m m2 Hpt _)). exact (Hv k Hk).
Qed.

(* dec_a_core is kept by a stretch that writes no memory and none of s0, s1, sp, gp, tp, given its journal
   (LLVMFuzzerTestOneInput_seg_exit_scan.v sc_core_pt). *)
Lemma cs_core_pt : forall cx ly S (W : world decodesegs0) regs mem md regs2 mem2 md2 k,
  dec_a_core B cx ly S W regs mem md k ->
  @ajournal rc dec_A_sink_head decodesegs0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S W mem2 md2 k ->
  (forall x, mem2 x = mem x) ->
  YK11.getr regs2 2 = YK11.getr regs 2 -> YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
  YK11.getr regs2 8 = YK11.getr regs 8 -> YK11.getr regs2 9 = YK11.getr regs 9 ->
  dec_a_core B cx ly S W regs2 mem2 md2 k.
Proof.
intros cx ly S W regs mem md regs2 mem2 md2 k
  (_ & Hfrs & R8 & R9 & Rsp & Hsp & Hal & R3 & R4 & Hsv & HF1 & HF2 & Hfp & Hfl & Hpay & Hga) HJ Hpt E2 E3 E4 E8 E9.
unfold dec_a_core.
split; [exact HJ|]. split; [exact Hfrs|]. split; [rewrite E8; exact R8|]. split; [rewrite E9; exact R9|].
split; [unfold spZ; rewrite E2; exact Rsp|]. split; [exact Hsp|]. split; [exact Hal|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
split.
{ unfold dec_a_saved in *. eapply Forall_impl; [|exact Hsv]. intros o Ho.
  rewrite (cs_rdword_pt _ _ _ (cs_aview_pt _ _ _ Hpt)). exact Ho. }
split; [exact HF1|]. split; [exact HF2|].
split; [intros a Ha; apply (cs_apresent_pt _ _ _ Hpt); apply Hfp; exact Ha|].
split; [rewrite (cs_rdword_pt _ _ _ (cs_aview_pt _ _ _ Hpt)); exact Hfl|].
split; [exact Hpay|].
exact (cs_garr8_pt _ _ _ _ _ Hpt Hga).
Qed.

(* The 13 saved words lie at d_sp0 - 104 .. d_sp0 - 8 (each 8 bytes). *)
Lemma cs_saved_rng : forall o, In o dec_a_saved_at -> 8 <= fst o <= 104.
Proof.
intros o Ho. unfold dec_a_saved_at in Ho. cbn [In] in Ho.
repeat (destruct Ho as [Ho | Ho]; [subst o; cbn [fst]; lia |]). destruct Ho.
Qed.

(* The stack facts of the journal: the realigned stack pointer lies above alloc_ceiling and below 2 ^ 47. *)
Lemma cs_stack : forall cx ly S (W : world decodesegs0) regs mem md k,
  dec_a_core B cx ly S W regs mem md k ->
  alloc_ceiling <= d_sp1 cx /\ d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 /\ d_sp0 cx <= 2 ^ 47 /\
  d_sp1 cx mod 32 = 0.
Proof.
intros cx ly S W regs mem md k (HJ & _ & _ & _ & _ & Hsp & Hal & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
unfold DEC_LLVMF_STK in Hslo. lia.
Qed.

(* The fake frame lies below alloc_ceiling (AR's frame law at the current layout, whose frame base is the entry's). *)
Lemma cs_frame_low : forall (LAWS : AR_laws decodesegs0 B) cx ly S (W : world decodesegs0) regs mem md k,
  dec_a_core B cx ly S W regs mem md k -> 4096 <= d_F cx /\ d_F cx + 64 <= alloc_ceiling.
Proof.
intros LAWS cx ly S W regs mem md k (HJ & Hfrs & _).
pose proof HJ as (HAR & Hly & _).
assert (HinF : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds decodesegs0 B LAWS _ _ _ _ _ _ _ HAR HinF) as (Hf1 & Hf2 & _).
destruct Hly as (_ & _ & _ & _ & _ & HlyF & _).
assert (HFeq : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite HlyF; reflexivity).
rewrite HFeq in Hf1, Hf2.
assert (Hfb : 64 <= fs_frame_bytes DEC_FCLASS) by (apply Z.leb_le; vm_compute; reflexivity).
lia.
Qed.

(* dec_a_core is kept by a stretch that writes only the spill slot s1 + 64 .. s1 + 72 and none of s0, s1, sp, gp,
   tp, given its journal: the saved words lie above the spill area, the fake frame and the payload below
   alloc_ceiling. *)
Lemma cs_core_kept : forall (LAWS : AR_laws decodesegs0 B) cx ly S (W : world decodesegs0) regs mem md regs2 mem2 md2 k,
  d_n cx = Z.of_nat (length (d_pl cx)) ->
  dec_a_core B cx ly S W regs mem md k ->
  @ajournal rc dec_A_sink_head decodesegs0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S W mem2 md2 k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx + 64 <= a < d_sp1 cx + 72) ->
     aview decodesegs0 (w_H W) mem2 a = aview decodesegs0 (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  YK11.getr regs2 2 = YK11.getr regs 2 -> YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
  YK11.getr regs2 8 = YK11.getr regs 8 -> YK11.getr regs2 9 = YK11.getr regs 9 ->
  dec_a_core B cx ly S W regs2 mem2 md2 k.
Proof.
intros LAWS cx ly S W regs mem md regs2 mem2 md2 k HLEN Hcore HJ HK HP E2 E3 E4 E8 E9.
destruct (cs_stack cx ly S W regs mem md k Hcore) as (Hceil & Hsp & H47 & _).
destruct (cs_frame_low LAWS cx ly S W regs mem md k Hcore) as (HF0 & HF64).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hcore as (HJ0 & Hfrs & R8 & R9 & Rsp & Hsp' & Hal & R3 & R4 & Hsv & HF1 & HF2 & Hfp & Hfl & Hpay & Hga).
pose proof (proj1 HJ0) as HAR.
unfold dec_a_core.
split; [exact HJ|]. split; [exact Hfrs|]. split; [rewrite E8; exact R8|]. split; [rewrite E9; exact R9|].
split; [unfold spZ; rewrite E2; exact Rsp|]. split; [exact Hsp'|]. split; [exact Hal|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
split.
{ unfold dec_a_saved in *. rewrite Forall_forall in Hsv |- *. intros o Ho.
  pose proof (cs_saved_rng o Ho) as Hr.
  rewrite (rdword_ext (aview decodesegs0 (w_H W) mem) (aview decodesegs0 (w_H W) mem2)); [apply Hsv, Ho|].
  intros kk Hkk. apply HK; lia. }
split; [exact HF1|]. split; [exact HF2|].
split; [intros a Ha; apply HP; apply Hfp; exact Ha|].
split.
{ rewrite (rdword_ext (aview decodesegs0 (w_H W) mem) (aview decodesegs0 (w_H W) mem2)); [exact Hfl|].
  intros kk Hkk. apply HK; lia. }
split; [exact Hpay|].
eapply garr8_frame; [exact Hga|].
intros a Ha. apply mbyte_of_aview. rewrite length_map, <- HLEN in Ha.
pose proof (Hpay ltac:(lia)) as Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos0 (d_n cx) ltac:(lia)) as Hreq.
apply HK; lia.
Qed.

(* The rest of what cmp_q734 reads of memory, kept by the same stretch: the mode's table words (below alloc_ceiling
   by the location premise), the fake frame's shadow bytes and the copy of the body (a heap block). *)
Lemma cs_mem_kept : forall (LAWS : AR_laws decodesegs0 B) cx ly S (W : world decodesegs0) regs mem md k mem2
    res mode nch ns,
  d_n cx = Z.of_nat (length (d_pl cx)) ->
  dec_a_core B cx ly S W regs mem md k ->
  In (res, dec_a_len (d_n cx)) (ablocks B ly S) ->
  0 <= mode /\ mode + 12 <= alloc_ceiling ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx + 64 <= a < d_sp1 cx + 72) ->
     aview decodesegs0 (w_H W) mem2 a = aview decodesegs0 (w_H W) mem a) ->
  dec_a_mode_ok cx W mem mode nch ns ->
  dec_a_fsh cx (aview decodesegs0 (w_H W) mem) 0 4 ->
  garr8 decodesegs0 (mrestrict (w_H W) mem) res (map (fun b : byte => bv_unsigned b) (d_body cx)) ->
  dec_a_mode_ok cx W mem2 mode nch ns /\
  dec_a_fsh cx (aview decodesegs0 (w_H W) mem2) 0 4 /\
  garr8 decodesegs0 (mrestrict (w_H W) mem2) res (map (fun b : byte => bv_unsigned b) (d_body cx)).
Proof.
intros LAWS cx ly S W regs mem md k mem2 res mode nch ns HLEN Hcore Hinr Hmloc HK Hmode Hfsh Hgres.
destruct (cs_stack cx ly S W regs mem md k Hcore) as (Hceil & Hsp & H47 & _).
destruct (cs_frame_low LAWS cx ly S W regs mem md k Hcore) as (HF0 & HF64).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (proj1 Hcore)) as HAR.
assert (KLOW : forall a, 0 <= a < alloc_ceiling -> aview decodesegs0 (w_H W) mem2 a = aview decodesegs0 (w_H W) mem a)
  by (intros a Ha; apply HK; lia).
split.
{ destruct Hmode as (Hwhere & Hnch & Hns & Hv4 & Hv8).
  assert (HRD : forall a, 0 <= a -> a + 8 <= alloc_ceiling ->
            rdword (aview decodesegs0 (w_H W) mem2) a = rdword (aview decodesegs0 (w_H W) mem) a)
    by (intros a H0 H1; apply rdword_ext; intros kk Hkk; apply KLOW; lia).
  assert (Hd4 : 0 <= decode_obj 4 /\ decode_obj 4 + 8 <= 2 ^ 40)
    by (split; apply Z.leb_le; vm_compute; reflexivity).
  assert (Hd5 : 0 <= decode_obj 5 /\ decode_obj 5 + 8 <= 2 ^ 40)
    by (split; apply Z.leb_le; vm_compute; reflexivity).
  assert (Hd6 : 0 <= decode_obj 6 /\ decode_obj 6 + 8 <= 2 ^ 40)
    by (split; apply Z.leb_le; vm_compute; reflexivity).
  split.
  { destruct Hwhere as [Hw | [Hw | [Hw | Hw]]].
    - left. rewrite HRD by lia. exact Hw.
    - right; left. rewrite HRD by lia. exact Hw.
    - right; right; left. rewrite HRD by lia. exact Hw.
    - right; right; right. exact Hw. }
  split; [exact Hnch|]. split; [exact Hns|].
  split; (eapply val_mem_kept; [| eassumption]); intros kk Hkk; apply KLOW; cbn [Z.of_nat] in Hkk; lia. }
split.
{ destruct Hfsh as (F1 & F4 & F5 & F6).
  assert (HSH : 0 <= d_SH cx /\ d_SH cx + 8 <= alloc_ceiling) by (unfold d_SH, shadow_addr, SHADOW_OFF; lia).
  unfold dec_a_fsh.
  split; [intros i Hi; rewrite KLOW by lia; apply F1, Hi|].
  split; [rewrite KLOW by lia; exact F4|].
  split; [rewrite KLOW by lia; exact F5|].
  intros i Hi; rewrite KLOW by lia; apply F6, Hi. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (_ & Hr4096 & Hrceil & _).
pose proof (req_size_pos0 (dec_a_len (d_n cx)) ltac:(unfold dec_a_len; lia)) as Hrreq.
assert (LB : Z.of_nat (length (d_body cx)) = dec_a_len (d_n cx))
  by (unfold d_body, dec_a_len, dec_a_u; rewrite length_skipn; lia).
eapply garr8_frame; [exact Hgres|].
intros a Ha. apply mbyte_of_aview. rewrite length_map, LB in Ha. apply KLOW; lia.
Qed.

(* A spill slot off the bytes s1 + 64 .. s1 + 72 is kept by the same stretch. *)
Lemma cs_slot_kept : forall cx (W : world decodesegs0) mem mem2 off v,
  d_sp1 cx + 120 <= 2 ^ 64 -> 0 <= d_sp1 cx -> 0 <= off -> off + 8 <= 64 \/ 72 <= off <= 112 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx + 64 <= a < d_sp1 cx + 72) ->
     aview decodesegs0 (w_H W) mem2 a = aview decodesegs0 (w_H W) mem a) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) off v -> dec_a_slot cx (aview decodesegs0 (w_H W) mem2) off v.
Proof.
intros cx W mem mem2 off v Hhi Hlo Ho Hoff HK Hs. unfold dec_a_slot in *.
rewrite (rdword_ext (aview decodesegs0 (w_H W) mem) (aview decodesegs0 (w_H W) mem2)); [exact Hs|].
intros kk Hkk. apply HK; lia.
Qed.

(* A byte of the view as a one-byte value (ReadName.v rn_val_mem1). *)
Lemma cs_val_mem1 : forall H (m : word -> option byte) a v,
  aview decodesegs0 H m a = Some v -> val_mem decodesegs0 (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv kk Hk. assert (kk = 0%nat) as -> by lia.
destruct (aview_byte decodesegs0 H m a v Hv) as (b & Hb & -> & Hr).
change (a + Z.of_nat 0) with (a + 0). rewrite Z.add_0_r, Hb.
rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* An 8-byte value of the memory is the word the view reads there (LLVMFuzzerTestOneInput_seg_entry.v). *)
Lemma cs_rdword_of_val_mem : forall H mem a v,
  val_mem decodesegs0 (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview decodesegs0 H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (BB : forall k, (k < 8)%nat -> aview decodesegs0 H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (BB 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (BB 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (BB 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (BB 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (BB 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (BB 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (BB 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (BB 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The loop                                                          *)
(* ------------------------------------------------------------------ *)

Section body.
Context {fx : YK11.FPState}.
Local Abbreviation SEGS := (@pa_segs _ decode_listing PI_decode).
Local Abbreviation VAL := (@pa_val _ decode_listing PI_decode).
Local Abbreviation BASE := (@pa_val _ decode_listing PI_decode A_TEXT).
Definition cs_E (regs : bvmap 5 word) : env := Eimg (PI := PI_decode) (Ereg regs []).
Lemma cs_pc : forall k, Z_to_bv 64 (BASE + k) = w64 (DEC_A_LLVMF + k).
Proof. intros k. reflexivity. Qed.

(* The seat at +0x624 (LLVMFuzzerTestOneInput_seg_exit_scan.v sc_entry_it at this loop's head). *)
Lemma cs_entry : forall (LAWS : AR_laws SEGS B) ly S (W : world SEGS) (regs : bvmap 5 word) mem md out n i,
  AR SEGS B ly S W mem md -> In (out, n) (ablocks B ly S) -> 0 <= i < n ->
  YK11.getr regs 10 = w64 (-1) -> YK11.getr regs 12 = w64 0 -> YK11.getr regs 18 = w64 SHADOW_OFF ->
  YK11.getr regs 11 = w64 (out + i) -> YK11.getr regs 13 = w64 (out + i) ->
  aview SEGS (w_H W) mem (out + i) = Some DEC_FILL ->
  st_ok_pi SEGS VAL (cs_E regs) ss_cs
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x624)) mem (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SOff 18 0) cs_SH (cs_E regs) (mrestrict (w_H W) mem).
Proof.
intros LAWS ly S W regs mem md out n i HAR Hin Hi H10 H12 H18 H11 H13 Hfill.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _).
pose proof (req_size_pos0 n ltac:(lia)) as Hreq.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew (cs_E regs) nn = YK11.getr regs r)
  by (intros nn r Hn; unfold cs_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U11 : bv_unsigned (ew (cs_E regs) 11) = out + i)
  by (rewrite (EE 11%nat 11%bv eq_refl), H11; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew (cs_E regs) 13) = out + i)
  by (rewrite (EE 13%nat 13%bv eq_refl), H13; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew (cs_E regs) 18) = SHADOW_OFF)
  by (rewrite (EE 18%nat 18%bv eq_refl), H18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- unfold ss_cs, cs_regs.
  apply (st_ok_pi_pin_reg' (cs_E regs) (mkSS 0x624 (sr_set sr_atoms 10%bv (SLit (-1))) [cs_reg] None cs_facts) _ 12%bv 0);
    [| cbn [ms_regs restrict YK11.mkst]; exact H12 | reflexivity].
  apply (st_ok_pi_pin_reg' (cs_E regs) (mkSS 0x624 sr_atoms [cs_reg] None cs_facts) _ 10%bv (-1));
    [| cbn [ms_regs restrict YK11.mkst]; exact H10 | reflexivity].
  rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold cs_reg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U13.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (cs_E regs) _ (out + i) 0 1 (SLit DEC_FILL) DEC_FILL);
      [reflexivity | unfold DEC_FILL; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (cs_val_mem1 _ _ _ _ Hfill).
  + exact (conj I I).
  + split; [|split; [exact I | exact I]].
    cbn [cs_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite U18, U11, U13, !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF.
    repeat split; try exact I; lia.
- unfold sh_ok, cs_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) mem (cs_E regs) (SOff 18 0) 11 (out + i) 1 (out + i) 0 1).
  + eapply (range_addressable_of_block SEGS B LAWS ly S W mem md out n (out + i) 1 HAR Hin); lia.
  + apply U_atom; [rewrite (EE 18%nat 18%bv eq_refl); exact H18 | unfold SHADOW_OFF; lia].
  + apply U_atom; [rewrite (EE 11%nat 11%bv eq_refl); exact H11 | lia].
  + lia.
  + lia.
  + intros xx Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia.
Qed.

(* The state at the loop head +0x624 before iteration j. *)
Definition cs_P (cx : dctx) (ly : alayout) (S : astate) (W : world decodesegs0) (mem0 : word -> option byte)
    (res out olen : Z) (j : Z) : world decodesegs0 -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs mem md,
    c' = mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x624)) mem (YK11.seg_rom decodesegs0)) md /\
    0 <= j < olen /\
    dec_a_core B cx ly S W regs mem md dec_ev_5fc /\ dec_a_fr cx regs /\
    (forall x, mem x = mem0 x) /\
    YK11.getr regs 10 = w64 (-1) /\ YK11.getr regs 12 = w64 0 /\ YK11.getr regs 18 = w64 SHADOW_OFF /\
    YK11.getr regs 17 = w64 out /\ YK11.getr regs 20 = w64 res /\
    YK11.getr regs 11 = w64 (out + j) /\ YK11.getr regs 13 = w64 (out + j) /\
    YK11.getr regs 25 = w64 (olen - j).

Lemma cs_body : forall (LAWS : AR_laws decodesegs0 B) (HCELLS : dec_crt_cells B) (cx : dctx) ly S
    (W : world decodesegs0) regs0 mem0 md0 res out mode nch ns,
  d_n cx = Z.of_nat (length (d_pl cx)) ->
  frm_zero (@fp_csr fx) ->
  dec_a_core B cx ly S W regs0 mem0 md0 dec_ev_5fc ->
  Permutation (ablocks B ly S) (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++
                                  [(out, dec_a_olen nch ns)]) ->
  4096 <= res -> 4096 <= out ->
  mo_le MT (d_S cx) S (dec_spent_5fc MT (d_n cx)) -> mo_ok MT S (dec_rest_5fc MT) ->
  CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = false ->
  dec_a_fr cx regs0 ->
  YK11.getr regs0 10 = w64 (-1) ->
  YK11.getr regs0 11 = w64 out -> YK11.getr regs0 13 = w64 out -> YK11.getr regs0 17 = w64 out ->
  YK11.getr regs0 12 = w64 0 ->
  YK11.getr regs0 18 = w64 SHADOW_OFF ->
  YK11.getr regs0 20 = w64 res ->
  YK11.getr regs0 25 = w64 (dec_a_olen nch ns) ->
  dec_a_mode_ok cx W mem0 mode nch ns ->
  dec_a_fsh cx (aview decodesegs0 (w_H W) mem0) 0 4 ->
  garr8 decodesegs0 (mrestrict (w_H W) mem0) res (map (fun b : byte => bv_unsigned b) (d_body cx)) ->
  dec_a_filled W mem0 out (dec_a_olen nch ns) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem0) 40 SHADOW_OFF ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem0) 56 (dec_a_len (d_n cx)) ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem0) 72 out ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem0) 112 (d_F cx) ->
  SRr decodesegs0 W
    (mkCfg (@YK11.mkst fx regs0 (w64 (DEC_A_LLVMF + 0x624)) mem0 (YK11.seg_rom decodesegs0)) md0)
    (cmp_q734 B MT cx).
Proof.
intros LAWS HCELLS cx ly S W regs0 mem0 md0 res out mode nch ns HLEN Hfrm Hcore0 Hperm Hres4096 Hout4096 Hmle Hmok
  HP Hfr0 R10 R11 R13 R17 R12 R18 R20 R25 Hmode Hfsh Hgres Hfill S40 S56 S72 S112.
assert (Holen1 : 1 <= dec_a_olen nch ns).
{ unfold dec_a_olen. destruct ((0 <? nch) && (0 <? ns)) eqn:E; [|lia].
  apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1, E2. nia. }
remember (dec_a_olen nch ns) as olen eqn:Eolen.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (cs_stack cx ly S W regs0 mem0 md0 dec_ev_5fc Hcore0) as (Hceil & Hsp & H47 & Hsp32).
destruct (cs_frame_low LAWS cx ly S W regs0 mem0 md0 dec_ev_5fc Hcore0) as (HF0 & HF64).
pose proof (proj1 (proj1 Hcore0)) as HAR0.
assert (Hino : In (out, olen) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
assert (Hinr : In (res, dec_a_len (d_n cx)) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hino) as (_ & _ & Hoceil & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinr) as (_ & _ & Hrceil & _).
pose proof (req_size_pos0 olen ltac:(lia)) as Horeq.
pose proof (req_size_pos0 (dec_a_len (d_n cx)) ltac:(unfold dec_a_len; lia)) as Hrreq.
(* where the mode's two geometry words lie: in one of the three tables the pointer cells of dec_crt_cells name (the
   rows picked by statement), or in the fake frame *)
assert (Hmloc : 0 <= mode /\ mode + 12 <= alloc_ceiling).
{ destruct Hmode as (Hwhere & _).
  pose proof (HCELLS ly) as HCL.
  repeat match type of HCL with _ /\ _ => let H1 := fresh "Row" in destruct HCL as [H1 HCL] end.
  assert (Hc4 : In (z8 (ANum (decode_obj 4%nat)) 0x20d40) (as_const B ly)) by assumption.
  assert (Hc5 : In (z8 (ANum (decode_obj 5%nat)) 0x20d80) (as_const B ly)) by assumption.
  assert (Hc6 : In (z8 (ANum (decode_obj 6%nat)) 0x20d60) (as_const B ly)) by assumption.
  pose proof (am_const _ _ _ _ (proj1 HAR0)) as HCst. rewrite Forall_forall in HCst.
  destruct Hwhere as [Hw | [Hw | [Hw | Hw]]].
  - pose proof (fun Hv => rdword_cell B ly _ _ _ Hv (HCst _ Hc4)) as Hh. specialize (Hh ltac:(lia)).
    rewrite Hh in Hw. injection Hw as <-. lia.
  - pose proof (fun Hv => rdword_cell B ly _ _ _ Hv (HCst _ Hc5)) as Hh. specialize (Hh ltac:(lia)).
    rewrite Hh in Hw. injection Hw as <-. lia.
  - pose proof (fun Hv => rdword_cell B ly _ _ _ Hv (HCst _ Hc6)) as Hh. specialize (Hh ltac:(lia)).
    rewrite Hh in Hw. injection Hw as <-. lia.
  - lia. }
pose proof (paj_run (fx := fx) (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUN.
pose proof (paj_run_to (fx := fx) (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_decode)) as BR.
refine (SRr_loopZ decodesegs0 Z (fun j => olen - j) (cs_P cx ly S W mem0 res out olen) (cmp_q734 B MT cx) _ 0 W _ _).
2: { split; [reflexivity|]. exists regs0, mem0, md0. split; [reflexivity|].
     split; [lia|]. split; [exact Hcore0|]. split; [exact Hfr0|]. split; [intros x; reflexivity|].
     split; [exact R10|]. split; [exact R12|]. split; [exact R18|]. split; [exact R17|]. split; [exact R20|].
     split; [rewrite Z.add_0_r; exact R11|]. split; [rewrite Z.add_0_r; exact R13|]. rewrite Z.sub_0_r. exact R25. }
intros j W' c' (-> & regs & mem & md & -> & Hj & Hcore & Hfr & Hpt0 & T10 & T12 & T18 & T17 & T20 & T11 & T13 & T25).
pose proof Hcore as (HJ & _ & _ & T9 & _).
pose proof (proj1 HJ) as HAR.
assert (Hfj : aview decodesegs0 (w_H W) mem (out + j) = Some DEC_FILL)
  by (rewrite (cs_aview_pt _ _ _ Hpt0); apply Hfill; lia).
destruct (cs_entry LAWS ly S W regs mem md out olen j HAR Hino ltac:(lia) T10 T12 T18 T11 T13 Hfj) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (cs_E regs)) by apply Eimg_env.
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew (cs_E regs) nn = YK11.getr regs r)
  by (intros nn r Hn; unfold cs_E; apply ew_Eimg_Ereg_nat; exact Hn).
lazymatch goal with |- SRr _ _ _ ?Q =>
  change (SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x624)) mem (YK11.seg_rom SEGS)) md) Q) end.
clear HAR.
(* +0x624 .. +0x650: the shadow check (fast path), the load, the accumulator, up to the back edge. *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cs_awr. }
cs_md.
cs_km HF KM1. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (AG1 : forall n, (n < 512)%nat -> ew Ex n = ew (cs_E regs) n)
    by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; reflexivity) end.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* `bnez s9` taken: one more step to +0x624, the invariant at j + 1. *)
  assert (Hlt : j + 1 < olen).
  { rewrite branch_ne_U in Hc.
    rewrite (U_atom_off _ 25 (olen - j) (-1)) in Hc;
      [| rewrite (AG1 25%nat) by lia; rewrite (EE 25%nat 25%bv eq_refl); exact T25 | lia | lia].
    rewrite U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x624.
  { cs_awr. }
  cs_md.
  cs_km HF KM2. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AG : forall n, (n < 512)%nat -> ew Ex n = ew (cs_E regs) n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG1; exact Hnn]) end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) =>
    assert (HAE : env_agree 32 (Ereg regs []) Ex)
      by (split; [intros nn Hnn; rewrite (AG nn) by lia; unfold cs_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
    pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs [] cs_keep HS HAE
      ltac:(vm_compute; reflexivity)) as KR;
    assert (Hptm : forall x, ms_mem msx x = mem x) by (intros x; rewrite KM2, KM1; reflexivity)
  end.
  cs_reg_at HS (10%bv : bv 5) (w64 (-1)) Q10 ltac:(reflexivity).
  cs_reg_at HS (12%bv : bv 5) (w64 0) Q12 ltac:(reflexivity).
  cs_reg_at HS (11%bv : bv 5) (w64 (out + (j + 1))) Q11
    ltac:(cbn [sv_denot]; rewrite (AG 11%nat) by lia; rewrite (EE 11%nat 11%bv eq_refl), T11; unfold w64;
          rewrite unsigned_lit_small by lia; f_equal; lia).
  cs_reg_at HS (13%bv : bv 5) (w64 (out + (j + 1))) Q13
    ltac:(cbn [sv_denot]; rewrite (AG 13%nat) by lia; rewrite (EE 13%nat 13%bv eq_refl), T13; unfold w64;
          rewrite unsigned_lit_small by lia; f_equal; lia).
  cs_reg_at HS (25%bv : bv 5) (w64 (olen - (j + 1))) Q25
    ltac:(cbn [sv_denot]; rewrite (AG 25%nat) by lia; rewrite (EE 25%nat 25%bv eq_refl), T25; unfold w64;
          rewrite unsigned_lit_small by lia; f_equal; lia).
  destruct Hfr as (F19 & F21 & F27).
  pmkst HS. rewrite cs_pc.
  apply SRr_ret. cbv beta. right. exists (j + 1). split; [lia|].
  unfold cs_P. split; [reflexivity|].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => exists (ms_regs msx), (ms_mem msx) end.
  eexists. split; [reflexivity|].
  split; [lia|].
  split; [apply (cs_core_pt cx ly S W regs mem md _ _ _ dec_ev_5fc Hcore HJ Hptm); apply KR; cs_kin|].
  split; [split; [cs_kept KR|]; split; cs_kept KR|].
  split; [intros x; rewrite Hptm; apply Hpt0|].
  split; [exact Q10|]. split; [exact Q12|]. split; [cs_kept KR|]. split; [cs_kept KR|]. split; [cs_kept KR|].
  split; [exact Q11|]. split; [exact Q13|]. exact Q25.
- (* `bnez s9` not taken (s9 = 0): +0x654 `j`, +0x668 `bnez a2` (a2 = 0), +0x66c / +0x670 the store of res + 50 at
     s1 + 64, +0x674 `blez a0` (a0 = -1), +0x734. *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (U9 : bv_unsigned (ew Ex 9) = d_sp1 cx)
      by (rewrite (AG1 9%nat) by lia; rewrite (EE 9%nat 9%bv eq_refl), T9; unfold w64; apply unsigned_lit_small; lia);
    assert (U13 : bv_unsigned (ew Ex 13) = out + j)
      by (rewrite (AG1 13%nat) by lia; rewrite (EE 13%nat 13%bv eq_refl), T13; unfold w64; apply unsigned_lit_small;
          lia) end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    pose proof (st_ok_pi_add_fact Ex ssx msx 9 cs_f9 HS
      ltac:(unfold afact_ok, cs_f9; cbn [af_lo af_hi af_al2]; rewrite U9; change (2 ^ 5) with 32; repeat split; lia))
      as HS1;
    clear HS; rename HS1 into HS end.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) =>
    assert (HR64 : region_ok SEGS Ex (ms_mem (restrict (w_H W) msx)) cs_s64);
    [ unfold cs_s64, region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val restrict ms_mem];
      rewrite U9; split; [lia|]; split; [lia|];
      split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres1; unfold DEC_LLVMF_STK; lia | constructor]
    | ];
    pose proof (st_ok_pi_add_region Ex ssx _ cs_s64 HS eq_refl HR64) as HS1 end.
  match type of HS1 with ?A -> _ => assert (HDJ : A) end.
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
      let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, cs_s64. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U13. repeat split; lia. }
  specialize (HS1 HDJ). clear HS HDJ HR64. rename HS1 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x734.
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (d_sp1 cx - d_sp0 cx));
      [ reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold DEC_LLVMF_STK; lia | cbn [YP09.r_whi]; lia | cs_awr ]. }
  cs_md.
  (* the store wrote only s1 + 64 .. s1 + 72; every byte stays present *)
  lazymatch goal with
  | HFr : frame_of ?Ex ?rsx (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1), HG : mem_grows (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1) |- _ =>
    assert (KMx : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx + 64 <= a < d_sp1 cx + 72) ->
              aview decodesegs0 Hh m1 a = aview decodesegs0 Hh m0 a);
    [ intros a Ha Hn;
      refine (kept_of_frame Ex rsx Hh m0 m1 (fun x => d_sp1 cx + 64 <= x < d_sp1 cx + 72) HFr _ a Ha Hn);
      intros bb wlo whi xx Hin Hr;
      let wsv := eval vm_compute in (windows rsx) in change (In (bb, wlo, whi) wsv) in Hin;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr|]); try contradiction;
      cbv beta; first [lia | rewrite U9 in Hr; lia]
    | ];
    assert (GRx : forall a, apresent Hh m0 a -> apresent Hh m1 a)
      by (intros a Ha; exact (apresent_grows Hh m0 m1 a HG Ha));
    assert (Hpt1 : forall x, m0 x = mem0 x) by (intros x; rewrite KM1; apply Hpt0)
  end.
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msf) =>
    assert (KMf : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx + 64 <= a < d_sp1 cx + 72) ->
              aview decodesegs0 (w_H W) (ms_mem msf) a = aview decodesegs0 (w_H W) mem0 a)
      by (intros a Ha Hn; etransitivity; [exact (KMx a Ha Hn) | apply cs_aview_pt; exact Hpt1]);
    assert (GRf : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem msf) a)
      by (intros a Ha; apply GRx; apply (cs_apresent_pt _ mem); [intros x; rewrite KM1; reflexivity | exact Ha]);
    assert (AG : forall n, (n < 512)%nat -> ew Ex n = ew (cs_E regs) n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG1; exact Hnn])
  end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) =>
    assert (HAE : env_agree 32 (Ereg regs []) Ex)
      by (split; [intros nn Hnn; rewrite (AG nn) by lia; unfold cs_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
    pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs [] cs_keep HS HAE
      ltac:(vm_compute; reflexivity)) as KR
  end.
  (* the slot s1 + 64 holds res + 50 *)
  lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf ?msr =>
    let rr0 := eval vm_compute in (nth_error (ss_mem ssf) 0) in
    lazymatch rr0 with Some ?r0 => pose proof (st_ok_pi_region_nth Ef ssf msr 0 r0 HS eq_refl) as HR64f end end.
  lazymatch type of HS with st_ok_pi _ _ ?Ef _ (restrict _ ?msf) =>
    assert (U9f : bv_unsigned (ew Ef 9) = d_sp1 cx)
      by (rewrite (AG 9%nat) by lia; rewrite (EE 9%nat 9%bv eq_refl), T9; unfold w64; apply unsigned_lit_small; lia);
    assert (E20 : ew Ef 20 = Z_to_bv 64 res)
      by (rewrite (AG 20%nat) by lia; rewrite (EE 20%nat 20%bv eq_refl), T20; reflexivity);
    lazymatch type of HR64f with
    | region_ok _ _ _ (YP09.mkRegion (Some 9%nat) ?lo ?hi ?wlo ?whi [YP09.mkChunk 64 (CVal 8 ?e)]) =>
      assert (He : sv_denot Ef e = Z_to_bv 64 (res + 50))
        by (rewrite denot_lit_U; f_equal;
            first [ apply (U_atom_off Ef 20 res 50 E20); lia
                  | rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom Ef 20 res E20) by lia; rewrite U_lit by lia;
                    unfold zcanon, M64; apply Z.mod_small; lia ]);
      pose proof (field_of_region Ef _ 9 (d_sp1 cx) _ lo hi wlo whi 64 8%N e (res + 50) HR64f U9f
        ltac:(cbn [In]; left; reflexivity) He ltac:(cbn; lia) ltac:(cbn; lia)) as V64
    end;
    assert (S64 : dec_a_slot cx (aview decodesegs0 (w_H W) (ms_mem msf)) 64 (res + 50));
    [ unfold dec_a_slot; apply cs_rdword_of_val_mem; [|lia];
      cbn [ms_mem restrict] in V64; change (N.to_nat 8) with 8%nat in V64; exact V64
    | ];
    destruct (cs_mem_kept LAWS cx ly S W regs0 mem0 md0 dec_ev_5fc (ms_mem msf) res mode nch ns HLEN Hcore0 Hinr
      Hmloc KMf Hmode Hfsh Hgres) as (MMODE & MFSH & MGRES);
    assert (KS : forall off v, 0 <= off -> off + 8 <= 64 \/ 72 <= off <= 112 ->
      dec_a_slot cx (aview decodesegs0 (w_H W) mem0) off v ->
      dec_a_slot cx (aview decodesegs0 (w_H W) (ms_mem msf)) off v)
      by (intros off v H0 Hoff; apply (cs_slot_kept cx W mem0 (ms_mem msf) off v ltac:(lia) ltac:(lia) H0 Hoff KMf))
  end.
  destruct Hfr as (F19 & F21 & F27).
  pmkst HS. rewrite cs_pc.
  lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rg _ ?mm _) ?mdx) _ =>
    apply SRr_ret; cbv beta; left; unfold cmp_q734; exists fx, ly, S, rg, mm, mdx, res, out, mode, nch, ns end.
  split; [reflexivity|]. split; [exact Hfrm|].
  split.
  { apply (cs_core_kept LAWS cx ly S W regs mem md _ _ _ dec_ev_5fc HLEN Hcore HJ).
    - intros a Ha Hn. rewrite (KMf a Ha Hn). symmetry. exact (cs_aview_pt _ _ _ Hpt0 a).
    - exact GRf.
    - apply KR; cs_kin.
    - apply KR; cs_kin.
    - apply KR; cs_kin.
    - apply KR; cs_kin.
    - apply KR; cs_kin. }
  split; [rewrite Eolen in Hperm; exact Hperm|]. split; [exact Hres4096|]. split; [exact Hout4096|].
  split; [exact Hmle|]. split; [exact Hmok|].
  split; [split; [cs_kept KR|]; split; cs_kept KR|].
  split; [cs_kept KR|]. split; [cs_kept KR|]. split; [cs_kept KR|].
  split; [exact MMODE|]. split; [exact MFSH|]. split; [exact MGRES|].
  split; [intros Hp; rewrite HP in Hp; discriminate|].
  split; [apply KS; [lia | lia | exact S40]|].
  split; [apply KS; [lia | lia | exact S56]|].
  split; [exact S64|].
  split; [apply KS; [lia | lia | exact S72]|].
  apply KS; [lia | lia | exact S112].
Qed.

End body.

Lemma cmp_scan : @cmp_prem rc RA_LLVMF B MT -> forall (cx : dctx) (W : world decodesegs0) (c : config),
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_a_rom cx -> @cmp_q624 rc B MT cx W c -> SRr decodesegs0 W c (@cmp_q734 rc B MT cx).
Proof.
intros HPREM cx W c HB HR H624.
destruct HPREM as (HPCF & HUTR & HCELLS & HROR & HRONE & LAWS & ML & MTL & ABCMP & AFREE & LUC).
destruct H624 as (fx' & ly' & S' & regs' & mem' & md' & res & out & mode & nch & ns & -> & Hfrm & Hcore & Hperm &
  Hres & Hout & Hmle & Hmok & HP & Hfr & R10 & R11 & R13 & R17 & R12 & R18 & R20 & R25 & Hmode & Hfsh & Hgres & Hfill &
  S40 & S56 & S72 & S112).
assert (HLEN : d_n cx = Z.of_nat (length (d_pl cx))).
{ unfold dec_a_base, dec_lib_pre_x in HB.
  destruct HB as (_Hafn & _Hra & _Ha0 & _Ha1 & _Hblk & Hlen & _). exact Hlen. }
exact (@cs_body fx' LAWS HCELLS cx ly' S' W regs' mem' md' res out mode nch ns HLEN Hfrm Hcore Hperm Hres Hout
  Hmle Hmok HP Hfr R10 R11 R13 R17 R12 R18 R20 R25 Hmode Hfsh Hgres Hfill S40 S56 S72 S112).
Qed.

End x.
