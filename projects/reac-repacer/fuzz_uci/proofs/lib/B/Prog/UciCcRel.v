(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): aj_flag_store_xR is aj_flag_store_x over a journal at
   a world relation R and the step relation SRrG R (YSRrG.SRrG_msteps for the run, YCbqG's R forms for the journal);
   the run keeps the world, so no law of R is read, and the R form takes R reflexive and transitive as every R rule
   does. aj_flag_store_x keeps its statement and is the instance at wle. aj_stack_malloc_at_xR (the call's own journal
   enters the caller's at R by reflexivity and transitivity; the post's own-call journal stays at wle) and
   aj_set_shadow_at_xR are the other two rules over R; their old names are the instances at wle. *)
(* Modified by Theorem Labs, 2026-10: cgif's frame-area call rule aj_stack_malloc_at (proofs/cgif/cgif_file_fuzzer/lib/
   YCbq.v:1749-1809, this tree's copy lib/Reusable/YCbq.v:1749) restated over YCbqG.v's journal ajournal_x (allocator
   invariant a parameter ARx, ghost head set Hp after S / Hpc after Sc, program statics PST), for the frame-area
   contract astack_malloc_realizes_x of the frozen lib/Reusable/FCiface.v (frameclass d9a884240c6e, sha256
   673aac5ee2f6ed86). Generic: no image
   class, no address, no allocator instance.
   Differences from the donor, each minimal:
   (a) cgif read the model's progress and post from model_laws (stack_malloc_progressP, ml_stack_malloc through
       am_wf); here they are ONE hypothesis in ARx form, SMX, which an instance discharges from its own model laws
       (the cf instance: YG05cf.v stack_malloc_progress_cf and stack_malloc_ok_cf with Wf_cf from ARcf);
   (b) the call's own journal is call_effect_journal_x (YGcallx.v:251) at PST = [], lifted by ajournal_x_nil_pst, and
       composed by ajournal_x_sub (YCbqG.v, footprint FP1 = []); Hp is threaded unchanged (FCiface: a frame-area call
       neither poisons nor unpoisons a head);
   (c) the frame's presence (FCiface's post) is also returned, which a caller writing its new frame needs;
   (d) as cgif's aj_stack_malloc_atS (cgif_file_fuzzer lib/YC85.v:292), the post ends with the call's own journal and
       `exists f, S2 = set_fs f Sc` (the call changes st_fs only), so a caller carries a state fact across the call.
   SECOND RULE, aj_flag_store_x: cgif's aj_flag_store (YCbq.v:2362-2439, the inline release under astack_free_law)
   for the LISTING engine over ajournal_x; its ARx-form hypotheses and their cf discharges are stated at the rule
   (ASFX = YG0dcf.v astack_free_law_cf; FFLX = the two conjuncts of cgif's frame_flag_lawP the rule reads, over ARx;
   SFX = YG05cf.v stack_free_ok_cf).
   THIRD RULE, aj_set_shadow_at_x: cgif's frame-area set_shadow call rule (cgif_rgb_fuzzer lib/YC05.v:206) over
   ajournal_x for FCiface's aset_shadow_realizes_x, taken from WalkH6's set-shadow-v2.patch (cold/h-hpreset-7-walk-H6
   321efcb143d) unchanged but for its comment.
   Rule 24: no ajournal_x port of aj_stack_malloc_at or aj_flag_store existed on any branch read (WalkS8a confirmed,
   2026-10-28 ~23:40Z; h-hpreset-7 stopped c-omx-alloc's lane for both); cgif's released YCbq.v is the source ported.
   Numerals: 0, 10 (cgif's class range), 16 (stack alignment), 64 (the smallest frame), 4096 (= ESTACK, YG0d.v),
   2 ^ 40, 2 ^ 64: LENGTH / DERIVED. No ADDRESS. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallSx.v, with its module paths and module names changed; 408 of its 467 lines of code are new or changed and 302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_exit_tail.v, with its module paths, module names and numbers changed; 209 of its 292 lines of code are new or changed and 384 lines of the source are left out. *)
(* The image-B twin of this unit's lib/A/Prog/UciCcRel.v (commit 240736c54b6), for fuzz_uci.asan-ubsan: the B core and the lib/B/Prog listing modules, and image B's offsets (the piece runs +0x24c .. +0x31c, eight bytes later than image A's, because of the UBSan alignment guard at +0x124 / +0x128). *)
(* UciCcRel: Lemma cc_rel : cc_rel_stmt (lib/B/Prog/UciCcCut.v), the release-and-return piece of check_clamp,
   offsets +0x24c .. +0x31c of the audited listing lib/B/Prog/UciPList.v.

   What the code does. +0x24c `li a0, -8` and three `sb a0, 4..6(s6)`: the local's three shadow bytes;
   +0x25c `lui`/`addiw` a0 = 0x45e0360e and +0x264 `sd a0, 0(s7)`: the released-frame magic into the frame's first
   word (s7 = F); +0x268 `beqz s2`: s2 = F >= 4096, so the arm at +0x2bc (the machine-stack case) is never entered
   (the engine decides the branch from the atom fact of s2); +0x26c `li a0, -11` and sixteen `sb a0, i(s6)`: the
   frame's sixteen shadow bytes become 0xf5; +0x2b0 `ld a0, 120(s2)`: the flag pointer FL from the frame's last word;
   +0x2b4 `sb zero, 0(a0)`: the flag byte, which releases the frame (lib/B/Prog/UciCcKit.v ucc_flag_store_pi);
   +0x2b8 `j +0x2ec`; +0x2ec `addi sp, s0, -96`; the ten reloads +0x2f0 .. +0x314 of ra and s0 .. s8 from the words
   the prologue saved below the entry sp; +0x318 `addi sp, sp, 96`; +0x31c `ret`.

   One run of the plain position-abstract engine (lib/B/Prog/PaSym.v sym_run_pi: no shadow token, so the writable
   shadow region is allowed) covers +0x24c .. +0x31c and stops at the `ret`, which lib/B/Prog/UciPPaLib.v paj_ret_at
   takes; the release-and-return idiom of proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_seg_exit_tail.v.
   The symbolic state: the registers at +0x24c as atoms 0 .. 31, atom 32 the flag pointer FL, atoms 33 .. 42 the entry
   values of ra, s0, s1, s2 .. s8 (UciCcCut.v's list of saved words, in its order); regions: the frame's first word
   (s7, written), its last word (s2, read: FL), its sixteen shadow bytes (s6, written), the flag byte (atom 32,
   written) and the ten saved words below s0 = the entry sp (read).

   The post: the journal after the flag store has own = [] and the frame released (stack_free_state), and goes back
   into the caller's journal (ajournal_sub); what the call kept is that journal's (acall_kept_of_journal); the
   callee-saved registers are the ten reloads, sp = s0 = the entry sp, and gp, tp, s9 .. s11 untouched; the state
   changed in st_fs only, so the meter bound is the cut's (mo_le_set_fs_r). *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YCbq.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0p YG0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import PaJournal.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import
UciPSyms UciPList UciPAddr UciPPa UciPImg UciPPaLib UciPCJ.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import Cells Step Frame ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import UciCg UciCcKit UciCcLeafb.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import check_clamp_cg UciCcCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x24c and the run to the ret              *)
(* ------------------------------------------------------------------ *)

(* The `ret` of check_clamp. *)
Definition CR_RET : Z := AF_check_clamp + 0x31c.
(* The saved words, as cc_rel_stmt lists them: (distance below the entry sp, register). *)
Definition CR_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24)].

Definition cr_rg_f0 : YP09.region := YP09.mkRegion (Some 23%nat) 0 8 0 8 [].
Definition cr_rg_f120 : YP09.region :=
  YP09.mkRegion (Some 18%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 32 0))].
Definition cr_rg_sh : YP09.region := YP09.mkRegion (Some 22%nat) 0 16 0 16 [].
Definition cr_rg_fl : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition cr_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-80) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0))].
(* s2 = F is at least 4096 (decides the `beqz s2` at +0x268) and 32-aligned. *)
Definition cr_facts : facts := mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition ss_cr : sstate :=
  mkSS CC_REL sr_atoms [cr_rg_f0; cr_rg_f120; cr_rg_sh; cr_rg_fl; cr_rg_sv] None cr_facts.
Definition CR_FUEL : N := 64.
Definition cr_ss_end : sstate := Eval vm_compute in fst (sym_runN_pi uci_tpi CR_FUEL ss_cr).
Definition cr_st_end : prun_status usym := Eval vm_compute in snd (sym_runN_pi uci_tpi CR_FUEL ss_cr).
Lemma cr_run : sym_runN_pi uci_tpi CR_FUEL ss_cr = (cr_ss_end, cr_st_end).
Proof. vm_compute. reflexivity. Qed.
Lemma cr_stop : ucc_plain_stop cr_st_end.
Proof. exact I. Qed.
Lemma cr_end_pc : ss_pc cr_ss_end = CR_RET.
Proof. reflexivity. Qed.

(* The environment: the registers at +0x24c, then FL, then the entry values of the saved registers. *)
Definition cr_extra (regs : bvmap 5 word) (FL : Z) : list word :=
  w64 FL :: map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) CR_SAVED.

(* The value of register r in the machine state of HS: its symbolic value, computed. *)
Ltac cr_regv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

Section rel. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ uci_listing PI_uci).
Local Abbreviation BASE := (@pa_val _ uci_listing PI_uci A_TEXT).

Definition cr_E (regs2 regs : bvmap 5 word) (FL : Z) : env := Eimg (PI := PI_uci) (Ereg regs2 (cr_extra regs FL)).

Lemma cr_ew_reg : forall regs2 regs FL n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (cr_E regs2 regs FL) n = YK11.getr regs2 r.
Proof. intros regs2 regs FL n r Hn. unfold cr_E. apply ucc_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma cr_ew_x : forall regs2 regs FL j, (j < 11)%nat ->
  ew (cr_E regs2 regs FL) (32 + j) = nth j (cr_extra regs FL) (Z_to_bv 64 0).
Proof. intros regs2 regs FL j Hj. unfold cr_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* The symbolic state at +0x24c holds of the machine state there. *)
Lemma cr_entry : forall (W : world segs) (regs2 regs : bvmap 5 word) mem (F FL SP : Z),
  YK11.getr regs2 8 = w64 SP -> YK11.getr regs2 18 = Z_to_bv 64 F ->
  YK11.getr regs2 22 = Z_to_bv 64 (SHADOW_OFF + F / 8) -> YK11.getr regs2 23 = Z_to_bv 64 F ->
  4096 <= F -> F mod 32 = 0 -> F + 128 <= alloc_ceiling -> in_app F 128 ->
  4096 <= FL < alloc_ceiling -> (FL < F \/ F + 128 <= FL) ->
  (FL < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 16 <= FL) ->
  alloc_ceiling + 80 <= SP <= 2 ^ 47 ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem a) ->
  (forall i, 0 <= i < 16 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  apresent (w_H W) mem FL ->
  rdword (aview segs (w_H W) mem) (F + 120) = Some FL ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (SP - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) CR_SAVED ->
  st_ok_pi segs VAL (cr_E regs2 regs FL) ss_cr
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CC_REL)) mem (YK11.seg_rom segs))).
Proof.
intros W regs2 regs mem F FL SP R8 R18 R22 R23 HF0 HF32 HFc HFapp HFL HFLF HFLS HSP Hpf Hpsh HpFL HFLw Hsaved.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF8 : F mod 8 = 0)
  by (pose proof (Z.div_mod F 32 ltac:(lia)) as D32; replace F with (F / 32 * 4 * 8) by lia; apply Z_mod_mult).
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. rewrite HF8, Z.add_0_r in D8.
set (E := cr_E regs2 regs FL).
assert (U8 : bv_unsigned (ew E 8) = SP)
  by (unfold E; rewrite (cr_ew_reg regs2 regs FL 8 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = F)
  by (unfold E; rewrite (cr_ew_reg regs2 regs FL 18 18%bv eq_refl), R18; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF + F / 8)
  by (unfold E; rewrite (cr_ew_reg regs2 regs FL 22 22%bv eq_refl), R22; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U23 : bv_unsigned (ew E 23) = F)
  by (unfold E; rewrite (cr_ew_reg regs2 regs FL 23 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (cr_ew_x regs2 regs FL 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
unfold CR_SAVED in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss_cr.
apply (@pa_entry_st_ok_full fx rc uci_listing PI_uci).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks cr_rg_f0 cr_rg_f120 cr_rg_sh cr_rg_fl
      cr_rg_sv base_val];
    rewrite ?U8, ?U18, ?U22, ?U23, ?U32.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ F 120 8 (SOff 32 0) FL);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ HFLw).
  + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). replace (FL + o) with FL by lia. exact HpFL.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
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
  unfold extent_of_region, cr_rg_f0, cr_rg_f120, cr_rg_sh, cr_rg_fl, cr_rg_sv.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U8, U18, U22, U23, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat split; first [exact I | lia].
- unfold cr_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18.
  change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma cc_rel : @cc_rel_stmt fx rc B MT.
Proof.
unfold cc_rel_stmt.
intros ASF FFL MTL MTF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem md S2 pos sp1 F
  HJ0 HJ1 Hfrs Eab Hnev EF R2 R8 R18 R22 R23 K3 K4 K25 K26 K27 Hret Hsaved HFLw Hmo
  Hsp16 Hsp1al Hsp1r Hlo Hhi HF0 HF32 HFc HCELLS LAWS Hcnt.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ0 as (HARc & _).
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk1 & _).
pose proof Hstk1 as (_ & _ & Hceil1 & Hslo1 & Hshi1 & H47 & _).
assert (Hcc : CC_STK = 4208) by reflexivity.
assert (Hin : In (CC_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ CC_CID pos HAR2 Hin) as (_ & HFapp & HFb & HFsh).
destruct (FFL lyc S2 W mem md CC_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
change (fs_frame_bytes CC_CID / 8) with 16 in HFsh.
change (fs_frame_bytes CC_CID) with 128 in HFapp, HFb.
rewrite <- EF in HFapp, HFb, HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
assert (HFLF : flag_addr lyc CC_CID pos < F \/ F + 128 <= flag_addr lyc CC_CID pos).
{ destruct (Z_lt_le_dec (flag_addr lyc CC_CID pos) F) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec (flag_addr lyc CC_CID pos) (F + 128)) as [h2|h2]; [|right; exact h2].
  exfalso. exact (proj2 (HFb _ (conj h h2)) HFLo). }
assert (HFLS : flag_addr lyc CC_CID pos < SHADOW_OFF + F / 8 \/
               SHADOW_OFF + F / 8 + 16 <= flag_addr lyc CC_CID pos).
{ destruct (Z_lt_le_dec (flag_addr lyc CC_CID pos) (SHADOW_OFF + F / 8)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec (flag_addr lyc CC_CID pos) (SHADOW_OFF + F / 8 + 16)) as [h2|h2]; [|right; exact h2].
  exfalso. pose proof (proj2 (HFsh (flag_addr lyc CC_CID pos - (SHADOW_OFF + F / 8)) ltac:(lia))) as Hno.
  replace (SHADOW_OFF + F / 8 + (flag_addr lyc CC_CID pos - (SHADOW_OFF + F / 8))) with (flag_addr lyc CC_CID pos)
    in Hno by lia.
  exact (Hno HFLo). }
pose proof (cr_entry W regs2 regs mem F (flag_addr lyc CC_CID pos) (spZ regs) R8 R18 R22 R23 HF0 HF32 HFc HFapp
  ltac:(lia) HFLF HFLS ltac:(unfold CC_STK, CC_FRAME, CC_ALIGN, ESTACK in *; lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i Hi)))
  HFLp HFLw Hsaved) as HS.
set (E := cr_E regs2 regs (flag_addr lyc CC_CID pos)) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, cr_E; apply Eimg_env).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF + F / 8).
{ pose proof (Z.div_lt_upper_bound F 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  unfold E; rewrite (cr_ew_reg regs2 regs _ 22 22%bv eq_refl), R22; apply unsigned_lit_small; unfold SHADOW_OFF; lia. }
assert (U23 : bv_unsigned (ew E 23) = F)
  by (unfold E; rewrite (cr_ew_reg regs2 regs _ 23 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 (flag_addr lyc CC_CID pos)) by exact (cr_ew_x regs2 regs _ 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = flag_addr lyc CC_CID pos)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
(* +0x24c .. +0x31c in one run, the flag store at +0x2b4 releasing the frame. *)
refine (ucc_flag_store_pi (SK := tfib_sink_head) B LAWS ASF FFL W CR_FUEL E ss_cr cr_ss_end cr_st_end
  (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CC_REL)) mem (YK11.seg_rom segs))
  CC_STK (spZ regs) [] lyc Sc W memc mdc [] lyc S2 md 0 CC_CID pos _ HEI HS cr_run cr_stop HJ1 _ _ _ _).
- unfold CC_CID. lia.
- (* the run writes the frame's first word, its shadow and the flag byte *)
  intros a (r & Hinr & Ha). unfold ss_cr in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<- | [<- | [<- | [<- | [<- | []]]]]];
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi cr_rg_f0 cr_rg_f120 cr_rg_sh cr_rg_fl cr_rg_sv] in Ha;
    rewrite ?U22, ?U23, ?U32 in Ha.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists CC_CID, pos.
    split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes CC_CID) with 128. lia.
  + lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists CC_CID, pos.
    split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes CC_CID / 8) with 16.
    rewrite ESH. lia.
  + right. lia.
  + lia.
- (* the flag byte is 0 after the run *)
  intros msr HSr.
  lazymatch goal with |- _ = Some _ =>
    let rr := eval vm_compute in (nth_error (ss_mem cr_ss_end) 3) in
    lazymatch rr with Some ?r3 =>
      pose proof (ucc_region_nth (segs := segs) _ _ msr 3 r3 HSr eq_refl) as HR3 end end.
  pose proof (ucc_field_of_region (segs := segs) E (ms_mem msr) 32 (flag_addr lyc CC_CID pos) _ 0 1 0 1 0 1%N
    (SLit 0) 0 HR3 U32 ltac:(cbn [In]; auto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(cbn; lia)).
  lazymatch type of V with _ = Some (Z_to_bv 8 ?x) => replace x with 0 in V by (vm_compute; reflexivity) end.
  replace (flag_addr lyc CC_CID pos + 0 + Z.of_nat 0) with (flag_addr lyc CC_CID pos) in V by lia.
  exact V.
- (* the return *)
  intros ms2 mat2 HS2 HJ2 _ _ _.
  set (md2 := with_vm_backing (m_vm_lazy md) mat2 md) in *. clearbody md2.
  eapply (paj_ret_at (L := uci_listing) (PL := PL_uci) (PI := PI_uci) W E cr_ss_end ms2 md2 _ HS2 eq_refl
    ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2).
  pose proof (ajournal_materialize segs B LAWS uci_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ2) as HJ3.
  fold md3 in HJ3. clearbody md3.
  (* the registers at the ret *)
  assert (R1e : YK11.getr (ms_regs ms2) 1 = YK11.getr regs 1).
  { cr_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (HP : aregs_preserved regs (ms_regs ms2)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      cr_regv HS2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    all: first
      [ reflexivity
      | transitivity (YK11.getr regs2 3); [apply cr_ew_reg; reflexivity | exact K3]
      | transitivity (YK11.getr regs2 4); [apply cr_ew_reg; reflexivity | exact K4]
      | transitivity (YK11.getr regs2 25); [apply cr_ew_reg; reflexivity | exact K25]
      | transitivity (YK11.getr regs2 26); [apply cr_ew_reg; reflexivity | exact K26]
      | transitivity (YK11.getr regs2 27); [apply cr_ew_reg; reflexivity | exact K27]
      | transitivity (YK11.getr regs2 8); [apply cr_ew_reg; reflexivity|];
        rewrite R8; unfold w64, spZ; apply Z_to_bv_bv_unsigned ]. }
  assert (Hpc : v_jalr (YK11.getr (ms_regs ms2) 1) 0 = YK11.getr regs 1) by (rewrite R1e; exact Hret).
  assert (Eab' : ablocks B lyc (stack_free_state CC_CID pos S2) = ablocks B lyc Sc).
  { transitivity (ablocks B lyc S2); [unfold ablocks; rewrite blocks_stack_free_state; reflexivity | exact Eab]. }
  unfold uci_cc_post.
  exists lyc, (stack_free_state CC_CID pos S2), (ms_regs ms2), (ms_mem ms2), md3.
  split; [rewrite Hpc; reflexivity|].
  split.
  { change own with ([] ++ own).
    eapply (ajournal_sub segs B LAWS uci_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CC_STK
      (spZ regs) [] [] lyc (stack_free_state CC_CID pos S2) W (ms_mem ms2) md3 0 HJ0 HJ3);
    [lia | lia | intros a (rg & Hrg & _); destruct Hrg]. }
  split; [exact HP|].
  split; [exact (ucc_sf_frames CC_CID pos S2 (frames Sc) Hfrs)|].
  split; [rewrite Eab'; apply Permutation_refl|].
  split.
  { eapply (acall_kept_of_journal segs B uci_segs_low CC_STK (spZ regs) [] [] lyc Sc W memc mdc lyc
      (stack_free_state CC_CID pos S2) W (ms_mem ms2) md3 0 (fun _ => False) HJ3 HARc).
    - intros a (rg & Hrg & _); destruct Hrg.
    - intros b m i Hb _ _. rewrite Eab'. exact Hb.
    - exact sink_closed_nil. }
  unfold stack_free_state. apply (mo_le_set_fs_r MT MTF). exact Hmo.
Qed.

End rel.
