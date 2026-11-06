(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 333 of its 378 lines of code are new or changed and 1879 lines of the source are left out. *)
(* TickBEpi: Theorem tick_epi : tick_epi_stmt (lib/B/Prog/TickCutB.v), the epilogue piece of the image-B walk of
   diginet_session_tick, offsets +0x608 .. +0x674 of the listing lib/B/Prog/DgnTransportBList.v
   (fuzz_transport.asan-ubsan 0x896a4 .. 0x89710).
   rule 24: proves no function (one piece of the walk; the walk is composed at TickCutB.v tick_holds_of).

   What the code does. +0x608 `lui`/`addiw` a0 = 0x45e0360e and +0x610 `sd a0, 0(s11)`: the frame's first word
   (s11 = F); +0x614 `beqz s2`: s2 = F >= 4096, so the real-stack arm at +0x628 is never entered (the engine decides the
   branch from the atom fact of s2); +0x618 a1 = 0x700 = 1792, +0x61c a0 = s2 = F, +0x620 `jal __asan_stack_free_5`:
   the release of the class-5 frame; +0x624 `j +0x634`; +0x634 a0 = s10 = the result; +0x638 `addi sp, s0, -192`; the
   13 reloads +0x63c .. +0x66c of ra, s0, s1, s2 .. s11 from the words the prologue saved below the entry sp
   (TickCutB.v TICK_SAVED); +0x670 `addi sp, sp, 192`; +0x674 `ret`.

   Two runs of the position-abstract engine over the caller's G journal (lib/B/Prog/TransportGRunB.v paj_run_x at
   G_HARNESS_B, no shadow entry): run 1 from +0x608 to the call (one region: the frame's first word, written), run 2
   from the return +0x624 to the `ret` (one region: the 13 saved words below s0 = the entry sp, read), which
   lib/B/Prog/DgnTransportBPaLib.v paj_ret_at takes. The call between them is lib/A/Prog/TransportGRt.v
   gx_stack_free_cls_at (image-free) at the statement's astack_free_cls_realizes premise (tick_callees, its seventh
   contract): its frame word at F + 2040 is the cut's (tick_cur), kept by run 1.

   The post (lib/B/Prog/diginet_session_tick_cg.v transport_tick_post, TransportGCg.v transport_cg_post over
   G_HARNESS_B): the caller's G journal after the free, with own and the frame released (stack_free_state); the
   callee-saved registers are the 13 reloads, sp = s0 = the entry sp, gp and tp untouched; a0 = s10 = r; the frames
   the caller's (lib/B/Prog/CanKit.v can_sf_frames); the state changed in st_fs only, so the meter bound is the cut's
   (mo_le_set_fs_r). What the call kept: the cut's acall_kept_g, carried by TransportGRt.v dk_kept_free_gw over the
   bytes the three steps may change (the own frame, its shadow bytes, its flag byte: TransportGCg.v dkg_nf; the ESTACK
   bytes below sp1). The world relation at Bw': the cut's, kept since no byte of G is one of those bytes
   (lib/B/Prog/TWorldB.v tw_kept_GB). The proof is image A's lib/A/Prog/TickEpi.v at image B's listing, image, G,
   addresses (the return +0x624, the size a1 = 1792) and the bundle's order. trans_src_ok is not used. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame TransportGRt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg TickCutB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The two symbolic states                                          *)
(* ------------------------------------------------------------------ *)

(* The return of the call of __asan_stack_free_5 (`jal` at +0x620). *)
Definition TEPI_C2 : Z := AF_diginet_session_tick + 0x624.

(* Run 1 at +0x608: the registers as atoms 0 .. 31; the frame's first word (s11, written); s2 = s11 = F is at least
   4096 (decides the `beqz s2` at +0x614) and 64-aligned. *)
Definition tepi_rg_hd : YP09.region := YP09.mkRegion (Some 27%nat) 0 8 0 8 [].
Definition tepi_facts1 : facts := mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 6); (27%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition ss_tepi1 : sstate := mkSS TICK_EPI sr_atoms [tepi_rg_hd] None tepi_facts1.

(* Run 2 at +0x624: the registers after the call as atoms 0 .. 31, atoms 32 .. 44 the entry values of ra, s0, s1,
   s2 .. s11 (TICK_SAVED, in its order); one region, the 13 saved words below s0 = the entry sp (read). *)
Definition tepi_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 34 0)); YP09.mkChunk (-32) (CVal 8 (SOff 35 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 40 0)); YP09.mkChunk (-80) (CVal 8 (SOff 41 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 42 0)); YP09.mkChunk (-96) (CVal 8 (SOff 43 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 44 0))].
Definition ss_tepi2 : sstate := mkSS TEPI_C2 sr_atoms [tepi_rg_sv] None (mkFacts [] [] []).

(* No shadow entry: the shadow base of the token engine is not read, and the span is empty. *)
Definition TEPI_Bx : sv := SOff 32 0.
Definition TEPI_B0 : Z * Z := (0, 0).

(* The entry values of the saved registers, in TICK_SAVED's order. *)
Definition tepi_extra (regs : bvmap 5 word) : list word :=
  map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) TICK_SAVED.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac tepi_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "tepi_reg: no match for" T; fail
  end.

(* The value of a register in the goal, from HS: its symbolic value, computed. *)
Ltac tepi_regv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case closed
   by tac. *)
Ltac tepi_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

Section epi. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition tepi_E1 (regs2 : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs2 []).
Definition tepi_E2 (regs3 regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs3 (tepi_extra regs)).

(* The symbolic state at +0x608 holds of the machine state there. *)
Lemma tepi_entry1 : forall (W : world segs) (regs2 : bvmap 5 word) mem (F : Z),
  YK11.getr regs2 18 = w64 F -> YK11.getr regs2 27 = w64 F ->
  4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (tepi_E1 regs2) ss_tepi1
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + TICK_EPI)) mem (YK11.seg_rom segs))).
Proof.
intros W regs2 mem F R18 R27 HF0 HF64 HFc Hpf.
assert (U18 : bv_unsigned (ew (tepi_E1 regs2) 18) = F)
  by (unfold tepi_E1; rewrite (can_ew_Eimg_Ereg_nat regs2 [] 18 18%bv eq_refl), R18; unfold w64;
      apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew (tepi_E1 regs2) 27) = F)
  by (unfold tepi_E1; rewrite (can_ew_Eimg_Ereg_nat regs2 [] 27 27%bv eq_refl), R27; unfold w64;
      apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_tepi1.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold tepi_rg_hd, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U27. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
- apply pairwise_disjoint_of_extents.
  unfold tepi_rg_hd, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- unfold tepi_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18, U27.
  change (2 ^ 6) with 64.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The symbolic state at +0x624 holds of the machine state there. *)
Lemma tepi_entry2 : forall (W : world segs) (regs3 regs : bvmap 5 word) mem (SP : Z),
  YK11.getr regs3 8 = w64 SP -> alloc_ceiling <= SP - 104 -> SP <= 2 ^ 47 ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (SP - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) TICK_SAVED ->
  st_ok_pi segs VAL (tepi_E2 regs3 regs) ss_tepi2
    (restrict (w_H W) (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + TEPI_C2)) mem (YK11.seg_rom segs))).
Proof.
intros W regs3 regs mem SP R8 HSP HSP47 Hsaved.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := tepi_E2 regs3 regs).
assert (U8 : bv_unsigned (ew E 8) = SP)
  by (unfold E, tepi_E2; rewrite (can_ew_Eimg_Ereg_nat regs3 _ 8 8%bv eq_refl), R8; unfold w64;
      apply unsigned_lit_small; lia).
unfold TICK_SAVED in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss_tepi2.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold tepi_rg_sv, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  all: lazymatch goal with |- YP09.chunk_ok _ _ _ ?b (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
    match goal with Sv : rdword _ (?b0 - ?o) = Some (bv_unsigned ?x) |- _ =>
      apply (chunk_ok_val segs E _ b off 8 (SOff n 0) (bv_unsigned x));
      [ cbn [sv_denot]; rewrite Z.add_0_r; reflexivity
      | let Hrr := fresh "Hrr" in pose proof (bv_unsigned_in_range 64 x) as Hrr;
        change (bv_modulus 64) with (2 ^ 64) in Hrr; exact Hrr
      | zside
      | replace (b + off) with (b0 - o) by lia; exact (val_mem_of_rdword segs _ _ _ _ Sv) ]
    end end.
- apply pairwise_disjoint_of_extents.
  unfold tepi_rg_sv, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma tick_epi_ok : @tick_epi_stmt fx rc B MT.
Proof.
unfold tick_epi_stmt, tick_epi_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
destruct LAWS0 as (_ & _ & _ & _ & _ & _ & _ & LAWS & MTL & MTF & _ & FFL & HGX & _).
destruct CALLEES as (_ & _ & _ & _ & _ & _ & ASF0 & _ & _ & _).
pose proof (ASF0 fx) as ASF. clear ASF0.
destruct HFIX as (HJ0 & Hret & _ & Hgp & Htp & _ & _ & Hsp16 & Hstk & Hsp0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
destruct HCUR as ((HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw) & HTW2 & Hgf2).
destruct HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R27) & R26).
unfold TICK_FBYTES in HFc, HFapp, HFLw.
replace (F + 2048 - 8) with (F + 2040) in HFLw by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (FR : TICK_FRAME = 192) by reflexivity.
(* the call's window lies above alloc_ceiling, below 2 ^ 47 *)
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hsp0a & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4304 <= TICK_STK).
{ unfold TICK_STK, TICK_FRAME, TICK_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm; assert (Ha : a = 4096) by reflexivity end.
  lia. }
(* sp1, the realigned stack pointer: at most 208 below the entry sp, 32-aligned *)
destruct (can_sp1_facts (spZ regs - TICK_FRAME) ltac:(lia) ltac:(rewrite Zminus_mod, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
(* the frame, its shadow bytes and its flag byte at the cut *)
assert (Hin : In (TICK_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 TICK_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
assert (EFL : flag_addr ly2 TICK_CID pos = flag_addr lyc TICK_CID pos)
  by (unfold flag_addr; rewrite ELF; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ TICK_CID pos HAR2 Hin) as (_ & _ & HFb & _).
change (fs_frame_bytes TICK_CID) with 2048 in HFb. rewrite EFA in HFb.
destruct (FFL ly2 S2 W2 mem2 md2 TICK_CID pos HAR2 Hin) as (_ & _ & _ & (_ & _ & HFLc)).
rewrite EFL in HFLc.
remember (flag_addr lyc TICK_CID pos) as FL eqn:EFL0.
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 TICK_CID pos F FL HAR2 Hfrs Hbl
  ELF EF EFL0 FFL) as (N1 & N2 & N3 & N4).
(* +0x608 .. +0x620: the header word, `beqz s2` (not taken), a1, a0, up to `jal __asan_stack_free_5` *)
pose proof (tepi_entry1 W2 regs2 mem2 F R18 R27 HF0 HF64 ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))) as HS.
set (E1 := tepi_E1 regs2) in HS.
assert (HEI : img_env VAL A_LIM E1) by (unfold E1, tepi_E1; apply Eimg_env).
assert (SHOK : sh_ok segs TEPI_Bx (@nil shent) E1 (mrestrict (w_H W2) mem2)) by constructor.
assert (EE1 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E1 n = YK11.getr regs2 rr)
  by (intros n rr Hn; unfold E1, tepi_E1; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U27 : bv_unsigned (ew E1 27) = F)
  by (rewrite (EE1 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
paj_run_tok RUN HS HJ1 SHOK TEPI_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ TICK_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U27 in Ha.
  left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes TICK_CID) with 2048. lia. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
(* what run 1 kept: every byte but the header word; presence grows *)
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ _ _ _ (fun x => F <= x < F + 8) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin' Hx. cbv beta.
  tepi_win Hin' Hx ltac:(rewrite ?U27 in Hx; lia). }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (HFLw1 : rdword (aview segs (w_H W2) (ms_mem ms)) (F + 2040) = Some FL).
{ rewrite <- HFLw. apply rdword_ext. intros k0 Hk0. apply KR1; lia. }
pmkst HS.
tepi_reg HS (10%bv : bv 5) (w64 F) Q10
  ltac:(cbn [sv_denot]; rewrite (EE1 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R18).
tepi_reg HS (11%bv : bv 5) (w64 1792) Q11 ltac:(reflexivity).
tepi_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + TEPI_C2)) Q1 ltac:(apply codeptr_val; exact HEI).
tepi_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite (EE1 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
tepi_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE1 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, R3; exact Hgp).
tepi_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE1 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, R4; exact Htp).
tepi_reg HS (8%bv : bv 5) (w64 (spZ regs)) Q8
  ltac:(cbn [sv_denot]; rewrite (EE1 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R8).
tepi_reg HS (26%bv : bv 5) (w64 r) Q26
  ltac:(cbn [sv_denot]; rewrite (EE1 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R26).
(* +0x620: __asan_stack_free_5 (F, 1792), through the G kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_stack_free_5)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ apply (gx_stack_free_cls_at (SK := tfib_sink_head) segs B LAWS transportb_segs_low
    (transportb_sigma TB___asan_stack_free_5) TICK_CID ASF FFL TG.G_HARNESS_B W2 (ms_regs ms) (ms_mem ms)
    STK sp0 FP ly S W0 mem0 md0 own ly2 S2 md1 (k + e) pos 1792 (sp1 - sp0) (Z_to_bv 64 (BASE + TEPI_C2)) HJ1).
  - rewrite EFA. exact Q10.
  - exact Q11.
  - rewrite EFA, EFL. change (fs_frame_bytes TICK_CID) with 2048.
    replace (F + 2048 - 8) with (F + 2040) by lia. exact HFLw1.
  - unfold spZ at 1. rewrite Q2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold TEPI_C2, AF_diginet_session_tick; lia | reflexivity]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hkeep3 & Hgr3).
rewrite EFA, EFL in Hkeep3. rewrite EFL in Hgr3.
change (fs_frame_bytes TICK_CID / 8) with 256 in Hkeep3.
replace (sp0 + (sp1 - sp0)) with sp1 in Hkeep3 by lia.
unfold shadow_addr in Hkeep3.
assert (P3 : YK11.getr regs3 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs ms) 3); [exact (HP3 3 ltac:(unfold acallee_saved; lia)) | exact Q3]).
assert (P4 : YK11.getr regs3 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs ms) 4); [exact (HP3 4 ltac:(unfold acallee_saved; lia)) | exact Q4]).
assert (P8 : YK11.getr regs3 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms) 8); [exact (HP3 8 ltac:(unfold acallee_saved; lia)) | exact Q8]).
assert (P26 : YK11.getr regs3 26 = w64 r)
  by (transitivity (YK11.getr (ms_regs ms) 26); [exact (HP3 26 ltac:(unfold acallee_saved; lia)) | exact Q26]).
(* what run 1 and the free kept: every byte but the own frame, its shadow bytes, its flag byte and the ESTACK bytes
   below sp1 *)
assert (K13 : forall a, 0 <= a < 2 ^ 64 -> ~ dkg_nf TICK_CID F FL a -> ~ (sp1 - ESTACK <= a < sp1) ->
  aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn Hw. unfold dkg_nf in Hn.
  change (fs_frame_bytes TICK_CID / 8) with 256 in Hn. change (fs_frame_bytes TICK_CID) with 2048 in Hn.
  rewrite (Hkeep3 a Ha).
  - apply KR1; [exact Ha | intros h; apply Hn; left; lia].
  - intros h. apply Hn. right; left. lia.
  - intros h. apply Hn. right; right. exact h.
  - exact Hw. }
assert (G13 : forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> a <> FL ->
  apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a)
  by (intros a Ha Hi Hne Hp; exact (Hgr3 a Ha Hi Hne (GA1 a Hp))).
(* the 13 saved words, kept *)
assert (Hsaved3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem3) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) TICK_SAVED).
{ apply Forall_forall. intros o Hino.
  pose proof (proj1 (Forall_forall _ _) Hsaved o Hino) as Ho. cbv beta in Ho |- *.
  assert (Hr8 : 8 <= fst o <= 104).
  { unfold TICK_SAVED in Hino. cbn [In] in Hino.
    repeat (destruct Hino as [Hino | Hino]; [subst o; cbn [fst]; lia |]). destruct Hino. }
  rewrite <- Ho. apply rdword_ext. intros k0 Hk0.
  apply K13; [lia | | lia].
  unfold dkg_nf. change (fs_frame_bytes TICK_CID / 8) with 256. change (fs_frame_bytes TICK_CID) with 2048.
  intros [h | [h | h]].
  - lia.
  - unfold SHADOW_OFF in h. pose proof (Z.mul_div_le F 8 ltac:(lia)). lia.
  - lia. }
clear HS SHOK HEI HEI0 EE1 U27 E1.
(* +0x624 .. +0x674: `j`, a0 = s10, sp = s0 - 192, the 13 reloads, sp = sp + 192, `ret` *)
pose proof (tepi_entry2 W2 regs3 regs mem3 (spZ regs) P8 ltac:(lia) ltac:(lia) Hsaved3) as HS.
set (E2 := tepi_E2 regs3 regs) in HS.
assert (HEI : img_env VAL A_LIM E2) by (unfold E2, tepi_E2; apply Eimg_env).
assert (SHOK : sh_ok segs TEPI_Bx (@nil shent) E2 (mrestrict (w_H W2) mem3)) by constructor.
clear dependent ms.
paj_run_tok RUN HS HJ3 SHOK TEPI_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_nil. }
set (mdF := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdF. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?m) => rename m into msF; set (EX := EF) in HS end.
(* run 2 wrote nothing *)
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem3 a).
{ intros a Ha.
  apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | intros h; exact h].
  intros b wlo whi x Hin' Hx. cbv beta.
  tepi_win Hin' Hx ltac:(lia). }
assert (GA3 : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem msF) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the registers at the `ret` *)
assert (RF1 : YK11.getr (ms_regs msF) 1 = YK11.getr regs 1).
{ tepi_regv HS. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (RF10 : YK11.getr (ms_regs msF) 10 = w64 r).
{ tepi_regv HS. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  transitivity (YK11.getr regs3 26); [reflexivity | exact P26]. }
assert (HP : aregs_preserved regs (ms_regs msF)).
{ intros rr Hr. unfold acallee_saved in Hr.
  assert (Hr' : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
    rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
  clear Hr.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    tepi_regv HS; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  all: first
    [ reflexivity
    | transitivity (YK11.getr regs3 3); [reflexivity | rewrite P3; symmetry; exact Hgp]
    | transitivity (YK11.getr regs3 4); [reflexivity | rewrite P4; symmetry; exact Htp]
    | transitivity (YK11.getr regs3 8); [reflexivity|];
      rewrite P8; unfold w64, spZ; apply Z_to_bv_bv_unsigned ]. }
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
(* the post *)
assert (Eab' : ablocks B ly2 (stack_free_state TICK_CID pos S2) = ablocks B ly2 S2)
  by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ dkg_nf TICK_CID F FL a -> ~ (sp1 - ESTACK <= a < sp1) ->
  aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn Hw; rewrite (KR3 a Ha); exact (K13 a Ha Hn Hw)).
unfold transport_tick_post, transport_cg_post.
exists ly2, (stack_free_state TICK_CID pos S2), (ms_regs msF), (ms_mem msF),
  (with_vm_backing (m_vm_lazy mdF) mat' mdF), e.
split; [rewrite RF1; unfold YK0s.ret_ok in Hret; rewrite Hret; reflexivity|].
split; [exact He|].
split; [apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ3|].
split; [exact HP|].
split; [exact (can_sf_frames TICK_CID pos S2 (frames Sc) Hfrs)|].
split; [rewrite Eab'; exact Hperm|].
split.
{ (* the cut's acall_kept_g, over the own frame, its shadow bytes, its flag byte and the ESTACK bytes below sp1 *)
  apply (dk_kept_free_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc ly2 S2 W2 mem2 md2
    (ms_mem msF) (spZ regs - TICK_STK) (spZ regs) (sp1 - ESTACK) sp1 TICK_CID pos F FL (tick_wr Bw)
    HARc HAR2 Hfrs Hbl ELF EF EFL0 FFL); [lia | lia | lia | lia | exact HK | exact KP |].
  intros a Ha Hi Hne Hp. exact (GA3 a (G13 a Ha Hi Hne Hp)). }
split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact Hmo|].
split; [exact RF10|].
(* the world relation at Bw': no byte of G is a byte the three steps wrote *)
split; [|exact Hgf2].
apply (tw_kept_GB (aview segs (w_H W2) mem2)); [exact HTW2|].
intros b n i Hbn Hi.
assert (HG : inG TG.G_HARNESS_B (b + i))
  by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
destruct (HGX _ HG) as [HiG _].
pose proof (transportb_segs_low _ HiG) as Hl. unfold kLowMemEnd in Hl.
apply KP; [lia | intros Hn; exact (N2 _ Hn HiG) | lia].
Qed.

End epi.

Theorem tick_epi : forall fx rc B MT, @tick_epi_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@tick_epi_ok fx rc B MT). Qed.

Print Assumptions tick_epi.
