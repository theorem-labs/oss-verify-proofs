(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMrecT2.v (commit ce1a656b52b7, file sha256 7aa165e6e753) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrecT2.v (commit 67fc7ef5787, lane B1 drain composition, DoRecycle chain; the chain's two function pairs, Quarantine::DoRecycle and LocalCache::Deallocate, re-checked EQUAL-mod-pcrel by cmpkit 4bbd3a74be89 strictcmp2 16982e3ef42b; file sha256 d7b3f343cd2a) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (lane B1 / H2, a prior worker; interface DMwalkIF.v at dc3949af11c):
   DoRecycle's entry segment onto the loop head ([T_E_r], DGif1dc.T_E + DGif1daE.T_E_e + DGif1daM.T_E_em) and its
   return on an empty batch list ([RETE_r], DGif1dc.RETE_x + RETE_e + RETE_em), over the opaque relations.
   rule 24: proves function __sanitizer::Quarantine<__asan::QuarantineCallback, __asan::AsanChunk>::DoRecycle (entry
   transitions; lane B1 reuse search the internal file LOOKUP-B1-drain.txt, B1LookupCheck CONFIRM). *)
(* Theorem Labs, 2026-10-30 (a prior worker): the image-B (asan-ubsan) twin of lib/A/DMrecT2.v at 14a6b2561a69, relocated by a Theorem Labs lane alreloc a5c53bb2bed4ad03 (every moved numeral a DoRecycle / LocalCache::Deallocate pc, +0x58) with the A twins A<r> renamed to the B twins Y<r>; the comment blocks above keep the A file's text and its A pcs. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFf2 YFh9 YFha YFhc YFhb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhf YFhd YFhl YFhg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DIfaceR DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMwalkIF DMrecS DMrecL DMrecS2 DMrecS3 DMrecT1. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormHitG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormLocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoG ErrnoApart. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import ErrnoApartcgif.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, KSTACK, TFIB_IMG_END, TFIB_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, YFh9.YFRAME, YFha.YFRAME, YFhc.YFRAME, YFhb.YFRAME, DMwalkIF.DRSTACK_X in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.
Hypothesis TB : TfibSyms B.
Hypothesis HRM : DMwalkIF.rmaxd_ok RMAXD.
Hypothesis RV : DMwalkIF.di_rview_x_t B ARXr DRq RMAXD.
Hypothesis FR : di_frame_t ARXr AOX.
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : DMwalkIF.dr_pre_r B ARXr AOX DRq (as_inst B) ly X0 P0 W0 regs0 mem0 md0.
Local Notation sp0 := (YFhd.sp0 regs0).
Local Notation sp1 := (YFhd.sp1 regs0).
Local Notation T := (ly_T ly).
Local Notation zlen := (@YFhd.zlen _).
Local Notation SB := (ly_space ly).
Local Notation hdra := (YFhd.hdra B ly).
Local Notation accr := (DMrecL.accr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation ostr := (DMrecL.ostr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation OSTr := (DMrecL.OSTr B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Ltac open_PRE := pose proof PRE as (HAR0 & Hinst & HDQ & LY & IMG & HSTK & HBL & LENP & INIT & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & CELLS).
Local Notation entry_facts := (DMrecS2.entry_facts_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation sp_facts := (DMrecS2.sp_facts_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation HLY := (DMrecS3.HLY B ARXr AOX DRq ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation slot_facts := (DMrecS.slot_facts_r B ARXr DRq RMAXD HRM RV ly HLY).
Local Notation lastaddr := (YFhg.lastaddr ly).
Local Notation DRSTACK_X := DMwalkIF.DRSTACK_X.
Ltac nsp := unfold ascratch in *; unfold spZ, raZ, YFhd.sp1, YFhd.sp0, DMrecL.SYr in *; numconst.

Local Notation ARXr_after_stack_write := (DMrecT1.ARXr_after_stack_write B ARXr AOX DRq FR ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation ek_stk := (DMrecT1.ek_stk B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation mk_stk := (DMrecT1.mk_stk B ARXr AOX DRq ly X0 P0 W0 regs0 mem0 md0 PRE).
Local Notation batch_cells_xfer_r := (DMrecT1.batch_cells_xfer_r B ly).

Lemma T_E_r : forall W' c', YFh9.at_OE W0 ly regs0 mem0 md0 (zlen P0) W' c' -> OSTr X0 P0 W' c'.
Proof.
intros W' c' HP. destruct HP as (-> & NZ & regs & mem & mat & -> & R2 & CS & R8 & R9 & R18 & R19 & R21 & R10 & MQ & PRS & CB & SV).
open_PRE. unfold spZ in *.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
assert (WST : forall a, YFh9.WIN regs0 a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; unfold YFh9.WIN in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, YFh9.WIN regs0 a \/ ~ YFh9.WIN regs0 a) by (intros a; unfold YFh9.WIN; apply ivl_dec).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YFh9.WIN regs0 a -> aview tfibsegs (w_H W0) mem a = aview tfibsegs (w_H W0) mem0 a).
{ intros a Ha Hn. exact (aview_after_write (w_H W0) mem0 mem _ a MQ Ha Hn). }
unfold YFeuC.plist_cells, qc_cells in CELLS. cbn [qc_list qc_bytes] in CELLS.
apply Forall_cons_iff in CELLS as [C0 CELLS]. apply Forall_cons_iff in CELLS as [C8 CELLS]. apply Forall_cons_iff in CELLS as [C16 CELLS]. apply Forall_cons_iff in CELLS as [C24 CB0].
assert (AGT : forall a, sp0 <= a < sp0 + 32 -> aview tfibsegs (w_H W0) mem a = aview tfibsegs (w_H W0) mem0 a).
{ intros a Ha. apply AG; [clear - Ha U0 S2; nsp; lia|]. unfold YFh9.WIN. clear - Ha. nsp. lia. }
assert (LZR : 0 <= lastaddr P0 < ASAN_CEIL).
{ unfold YFhg.lastaddr. destruct (rev P0) as [|bl initr] eqn:ER; [ceil; unfold ASAN_CEIL; lia|].
assert (Hbl : In bl P0) by (apply in_rev; rewrite ER; left; reflexivity).
pose proof (slot_facts X0 W0 mem0 md0 _ _ (b_self bl) HAR0 HDQ (in_map b_self _ _ Hbl)) as (B1 & B2 & _).
clear - B1 B2. numconst. lia. }
exists (lastaddr P0), (sum_bytes P0 mod 2 ^ 64), regs, mem, (with_vm_backing (m_vm_lazy md0) mat md0). split; [reflexivity|].
constructor.
- constructor.
+ exact (ARXr_after_stack_write X0 W0 mem0 mem md0 mat _ HAR0 (fun a O => O) WST WDEC MQ PRS).
+ apply wle_refl.
+ apply same_io_with_vm_backing.
+ intros a O; exact O.
+ intros a Ha _ _ NS _. apply AG; [exact Ha|]. intros Hw. apply NS. left. unfold spZ, YFh9.WIN in *. clear - Hw. nsp. lia.
+ intros a Ha. apply (presence_after_write W0 mem0 mem _ a WDEC MQ PRS); [unfold DMrecL.SYr in Ha; clear - Ha S1 S2; nsp; lia|].
apply HPRES. unfold DMrecL.SYr in Ha. clear - Ha. nsp. lia.
+ exact INIT.
+ intros x _ _ NS _. apply MQ. intros Hw. apply NS. left. unfold spZ, YFh9.WIN in *. clear - Hw. nsp. lia.
+ apply (ek_stk (sp0 - YFh9.YFRAME) sp0); [clear - E1; nsp; lia | exact MQ].
+ apply (mk_stk (sp0 - YFh9.YFRAME) sp0); [clear - E1; nsp; lia | clear - E2; nsp; lia | exact MQ].
- exact HDQ.
- exact HBL.
- intros ->. apply NZ. reflexivity.
- unfold YFhd.zlen. unfold DMwalkIF.zl in LENP. exact LENP.
- unfold YFhd.common_regs. splits; apply CS; cbn; tauto.
- unfold YFhd.loop_regs. splits; try assumption; rewrite R2; unfold YFhd.sp1; reflexivity.
- exact R10.
- split; [| exact SV]. eapply val_mem_addr; [exact CB | clear; nsp; lia].
- unfold YFhd.tmp_cells. cbv zeta. split; [|split; [|split; [|split; [|split]]]].
+ eapply val_mem_keep; [|exact (YF0x.cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C0)]. cbn [aeval]. intros a' Ha'. apply AGT. cbn in Ha'. lia.
+ eapply val_mem_keep; [|pose proof (YF0x.cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C8) as V; cbn [aeval aoff] in V; destruct P0 as [|b0 P']; cbn [aeval batch_exp firstaddr] in V |- *; exact V]. cbn [aeval aoff]. intros a' Ha'. apply AGT. cbn in Ha'. lia.
+ eapply val_mem_keep; [|pose proof (YF0x.cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C16) as V; cbn [aeval aoff] in V; unfold YFhg.lastaddr; destruct (rev P0) as [|bl initr]; cbn [aeval batch_exp] in V |- *; exact V]. cbn [aeval aoff]. intros a' Ha'. apply AGT. cbn in Ha'. lia.
+ eapply val_mem_keep; [|apply val_mem_mod64; pose proof (YF0x.cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C24) as V; cbn [aeval aoff] in V; exact V]. cbn [aeval aoff]. intros a' Ha'. apply AGT. cbn in Ha'. lia.
+ exact LZR.
+ apply mod64_range.
- apply (batch_cells_xfer_r P0 (aview tfibsegs (w_H W0) mem0)); [exact HBL | | exact CB0].
intros b a Hb Hs. pose proof (slot_facts X0 W0 mem0 md0 _ _ (b_self b) HAR0 HDQ (in_map b_self _ _ Hb)) as (B1 & B2 & _ & _ & _ & _ & _ & _ & BNS).
apply AG; [unfold bslot, kBatchBytes in Hs; clear - Hs B1 B2; numconst; lia|]. intros Hw.
exact (BNS a Hs (WST a Hw)).
Qed.

(* the return on an empty batch list *)
Lemma RETE_r : forall sz W' c', P0 = [] -> YFh9.at_RETE W0 regs0 mem0 md0 sz W' c' ->
DMwalkIF.dr_leaf_r B ARXr AOX DRq (as_inst B) ly X0 W0 regs0 mem0 md0 (tt, X0) W' c'.
Proof.
intros sz W' c' EP HP.
open_PRE. unfold spZ in *.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
destruct HP as (-> & _ & regs & mem & mat & -> & R2 & CS & MQ & PRS).
assert (WST : forall a, YFh9.WIN regs0 a -> ly_stk_lo ly <= a < ly_stk_hi ly) by (intros a Ha; unfold YFh9.WIN in Ha; clear - Ha E1 E2; nsp; lia).
assert (WDEC : forall a, YFh9.WIN regs0 a \/ ~ YFh9.WIN regs0 a) by (intros a; unfold YFh9.WIN; apply ivl_dec).
exists regs, mem, (with_vm_backing (m_vm_lazy md0) mat md0). split.
{ unfold cfg_at, raZ. rewrite Z_to_bv_bv_unsigned || (unfold w64; rewrite Z_to_bv_bv_unsigned). reflexivity. }
cbn [snd]. split.
{ split; [exact (ARXr_after_stack_write X0 W0 mem0 mem md0 mat _ HAR0 (fun a O => O) WST WDEC MQ PRS)|].
split; [apply layout_le_refl|]. split; [apply wle_refl|]. split.
{ apply aregs_intro; first [exact R2 | apply CS; cbn; tauto]. }
split; [apply same_io_with_vm_backing|]. split.
{ intros a Ha _ _ NS _. apply (aview_after_write (w_H W0) mem0 mem _ a MQ Ha).
intros Hw. apply NS. left. unfold YFh9.WIN in Hw. clear - Hw. nsp. lia. }
intros a Ha. apply (presence_after_write W0 mem0 mem _ a WDEC MQ PRS); [clear - Ha S1 U0; nsp; lia|].
apply HPRES. clear - Ha. nsp. lia. }
split. { intros x _ _ NS _. apply MQ. intros Hw. apply NS. left. unfold YFh9.WIN in Hw. clear - Hw. nsp. lia. }
split. { apply (ek_stk (sp0 - YFh9.YFRAME) sp0); [clear - E1; nsp; lia | exact MQ]. }
split. { apply (mk_stk (sp0 - YFh9.YFRAME) sp0); [clear - E1; nsp; lia | clear - E2; nsp; lia | exact MQ]. }
split. { rewrite EP in HDQ. exact HDQ. }
split. { exact INIT. }
split. { intros a O; exact O. }
intros a Ha. apply (presence_after_write W0 mem0 mem _ a WDEC MQ PRS); [clear - Ha S1 S2 U0; nsp; lia|]. apply HPRES. clear - Ha. nsp. lia.
Qed.
End e.
End c.
