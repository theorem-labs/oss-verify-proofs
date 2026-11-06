(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 494 of its 552 lines of code are new or changed and 1866 lines of the source are left out. *)
(* build_and_receive_seg_rel (image B): Theorem bar_rel_piece : bar_rel_stmt (lib/B/Prog/build_and_receive_segs.v), the
   release piece of the image-B walk of build_and_receive (fuzz_transport.asan-ubsan 0x85998), from the cut BAR_REL
   (+0x374, the return address of the call of receive) to the `ret` at +0x3e8. The image-A twin is
   lib/A/Prog/build_and_receive_seg_rel.v; image B's release reloads the frame from the slot s1 + 24 for its test
   (image A kept it in s4). Three position-abstract runs (lib/B/Prog/TransportGRunB.v paj_run_x) and two calls:
     run A  +0x374 .. +0x378  a1 = 190, a0 = s11 = the shadow address of frame[]; no byte written;
     +0x37c                   `jal __asan_set_shadow_f8` (lib/A/Prog/TransportGRt.v gx_set_shadow_at): the frame's
                              shadow bytes 4 .. 193 := 0xf8, frame[] out of scope;
     run B  +0x380 .. +0x394  the header word 0x45e0360e at the frame (`lui a0, 0x45e03`, `addiw a0, a0, 1550`,
                              `sd a0, 0(s2)`), a0 = the slot s1 + 24 (the frame, bar_cur's last conjunct), `beqz a0`
                              NOT taken (4096 <= the frame, so the real-stack arm at +0x3a0 is not entered), a1 = 1696;
     +0x398                   `jal __asan_stack_free_5` (TransportGRt.v gx_stack_free_cls_at): the frame's 256
                              shadow bytes := 0xf5 and its flag byte released;
     run C  +0x39c .. +0x3e4  `j +0x3ac`, sp = s0 - 192, the 13 reloads of BAR_SAVED, sp = sp + 192;
     +0x3e8                   the `ret` (lib/B/Prog/DgnTransportBPaLib.v paj_ret_at).
   No UBSan branch (to the trap word at +0x3ec) lies in +0x374 .. +0x3e8.
   The bytes the piece may change are the own frame's (TransportGCg.v dkg_nf: its 2048 bytes, its 256 shadow bytes,
   its flag byte) and the ESTACK bytes below the realigned sp, which lie in the call's own stack window; so the
   cut's acall_kept_g carries to the return (br_kept_nfz, TransportGFrame.v dk_kept_nfz_gw with the presence of the
   window from the journal), and the world relation at Bw' carries over G (no byte of G is one of them). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit TransportGFrameB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg TransportGRt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg build_and_receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import build_and_receive_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The three symbolic states                                        *)
(* ------------------------------------------------------------------ *)

(* The return points of the two calls. *)
Definition BR_C1 : Z := AF_build_and_receive + 0x380.
Definition BR_C2 : Z := AF_build_and_receive + 0x39c.
Definition BR_B0 : Z * Z := (0, 0).

(* run A, +0x374: two `addi`, no region. *)
Definition ss_bra : sstate := mkSS BAR_REL sr_atoms [] None (mkFacts [] [] []).

(* run B, +0x380: the frame's first word, written through s2 (atom 18), and the slot s1 + 24 (s1 = atom 9), which
   holds atom 18; `beqz a0` on the slot's value is decided by the fact on atom 18. *)
Definition brb_rg_hd : YP09.region := YP09.mkRegion (Some 18%nat) 0 8 0 8 [].
Definition brb_rg_s24 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 18 0))].
Definition brb_facts : facts := mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition ss_brb : sstate := mkSS BR_C1 sr_atoms [brb_rg_hd; brb_rg_s24] None brb_facts.

(* run C, +0x39c: the 13 saved words below s0 = atom 8, as atoms 32 .. 44. *)
Definition brc_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 34 0)); YP09.mkChunk (-32) (CVal 8 (SOff 35 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 40 0)); YP09.mkChunk (-80) (CVal 8 (SOff 41 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 42 0)); YP09.mkChunk (-96) (CVal 8 (SOff 43 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 44 0))].
Definition ss_brc : sstate := mkSS BR_C2 sr_atoms [brc_rg_sv] None (mkFacts [] [] []).

(* A byte of a 2048-byte frame in application memory is not one of the frame's shadow bytes. *)
Lemma br_frame_not_shadow {rc : YM05.RunCeil} : forall F i, in_app F 2048 -> 0 <= i < 2048 ->
  ~ (SHADOW_OFF + F / 8 <= F + i < SHADOW_OFF + F / 8 + 256).
Proof.
intros F i (H4 & [HL | (HH & _)]) Hi; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *;
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le F 8 ltac:(lia)); lia.
Qed.

(* The callee-saved registers, one by one. *)
Lemma br_saved_cases : forall r, acallee_saved r ->
  r = 2 \/ r = 3 \/ r = 4 \/ (r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27).
Proof.
intros r Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]];
  [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
  | right; right; right; left; reflexivity | right; right; right; right; left; reflexivity |].
do 5 right. lia.
Qed.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac br_reg HS r v H tac :=
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
(* A register the run did not write, from the equation Q of its value at the run's start. *)
Ltac br_kreg HS EW r n Q H :=
  lazymatch type of Q with _ = ?v =>
    br_reg HS r v H ltac:(cbn [sv_denot]; rewrite (EW n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The value of a register at the end of run C, as its symbolic value. *)
Ltac br_regv HS :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      rewrite (st_ok_restrict_reg sg Hh Ex ssx msx _ HS);
      lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
      lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.
(* The awr obligation's regions, computed. *)
Ltac br_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A run's frame keeps every byte outside Zs (U: the base of a written window). *)
Ltac br_frame_kept HFr Zs U :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
  intros a Ha Hn; apply (kept_of_frame _ _ _ _ _ Zs HFr); [| exact Ha | exact Hn];
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [injection Hin as <- <- <-; cbn [base_val] in Hx; cbv beta; first [exfalso; lia | rewrite U in Hx; lia] |]);
  destruct Hin.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition bra_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).
Definition brb_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).
Definition brc_extra (regs : bvmap 5 word) : list word :=
  map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) BAR_SAVED.
Definition brc_E (regsC regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regsC (brc_extra regs)).

(* run A's state at +0x374: no region, no fact. *)
Lemma bra_entry : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (bra_E regs) ss_bra
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + BAR_REL)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. unfold ss_bra.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* run B's state at +0x380: the frame's first word, writable, and the slot s1 + 24, which holds the frame. *)
Lemma brb_entry : forall (W : world segs) regs mem (F sp1 : Z),
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 F ->
  4096 <= F -> F + 8 <= sp1 -> F mod 64 = 0 -> sp1 + 32 <= 2 ^ 47 ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem a) ->
  rdword (aview segs (w_H W) mem) (sp1 + 24) = Some F ->
  st_ok_pi segs VAL (brb_E regs) ss_brb
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + BR_C1)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F sp1 R9 R18 HF0 HFs HF64 Hs47 Hpf Hrd.
set (E := brb_E regs).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E, brb_E; rewrite (can_ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl), R9; unfold w64;
      apply unsigned_lit_small; lia).
assert (E18 : ew E 18 = w64 F)
  by (unfold E, brb_E; rewrite (can_ew_Eimg_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_brb.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks brb_rg_hd brb_rg_s24 base_val];
    rewrite ?U9, ?U18.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ sp1 24 8 (SOff 18 0) F);
      [cbn [sv_denot]; rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ Hrd).
- apply pairwise_disjoint_of_extents.
  unfold brb_rg_hd, brb_rg_s24, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U18. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold brb_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18.
  change (2 ^ 6) with 64.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* run C's state at +0x39c: the 13 saved words below the entry sp. *)
Lemma brc_entry : forall (W : world segs) (regsC regs : bvmap 5 word) mem (SP : Z),
  YK11.getr regsC 8 = w64 SP -> 104 <= SP <= 2 ^ 47 ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (SP - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) BAR_SAVED ->
  st_ok_pi segs VAL (brc_E regsC regs) ss_brc
    (restrict (w_H W) (@YK11.mkst fx regsC (Z_to_bv 64 (BASE + BR_C2)) mem (YK11.seg_rom segs))).
Proof.
intros W regsC regs mem SP R8 HSP Hsaved.
set (E := brc_E regsC regs).
assert (U8 : bv_unsigned (ew E 8) = SP)
  by (unfold E, brc_E; rewrite (can_ew_Eimg_Ereg_nat regsC _ 8 8%bv eq_refl), R8; unfold w64;
      apply unsigned_lit_small; lia).
unfold BAR_SAVED in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss_brc.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [brc_rg_sv YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U8.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
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
  unfold brc_rg_sv, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma br_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W'
    mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* TransportGFrame.v dk_kept_nfz_gw whose presence premise is only the statement's window at the new memory: the
   release states presence for its own scratch and nowhere else, so a step after it has no presence growth to offer.
   The changed bytes of the frame lie below the allocation ceiling, where acall_kept_g asks no presence, and the
   window's presence comes from the journal (br_jpres). The proof is dk_kept_step_gw's, with that one clause from the
   premise. *)
Lemma br_kept_nfz : forall (LAWS : AR_laws segs B) G lyc Sc ly2 S2 (W : world segs) memc mdc (W1 : world segs)
    mem2 md2 memY slo shi cid fpos F FL (Eo Zs : Z -> Prop),
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W1 mem2 md2 ->
  frames S2 = (cid, fpos) :: frames Sc ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  ly_F ly2 = ly_F lyc ->
  F = frame_addr lyc cid fpos -> FL = flag_addr lyc cid fpos -> frame_flag_lawP segs B ->
  YM05.alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall a, Zs a -> (slo <= a < shi) \/ dkg_nf cid F FL a) ->
  acall_kept_g segs B G lyc Sc W memc W1 mem2 slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) memY a = aview segs (w_H W1) mem2 a) ->
  (forall a, slo <= a < shi -> apresent (w_H W1) memY a) ->
  acall_kept_g segs B G lyc Sc W memc W1 memY slo shi Eo.
Proof.
intros LAWS G lyc Sc ly2 S2 W memc mdc W1 mem2 md2 memY slo shi cid fpos F FL Eo Zs HAR HAR2 Hfrs Hbl ELF EF EFL
  FFL Hce Hshi HZ (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hpw.
destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W1 mem2 md2 cid fpos F FL HAR2 Hfrs Hbl ELF
  EF EFL FFL) as (N1 & N2 & N3 & N4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (NZ : forall a, YM05.alloc_ceiling <= a -> ~ (slo <= a < shi) -> ~ Zs a).
{ intros a Ha Hw HZa. destruct (HZ a HZa) as [X | X]; [exact (Hw X) | pose proof (N4 a X) as Hx; lia]. }
assert (NZl : forall a, a < YM05.alloc_ceiling -> ~ dkg_nf cid F FL a -> ~ Zs a).
{ intros a Ha Hn HZa. destruct (HZ a HZa) as [X | X]; [lia | exact (Hn X)]. }
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite Hkp; [exact (K1 a Ha Hw) | lia | exact (NZ a ltac:(lia) Hw)].
- intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
  rewrite Hkp; [exact (K2 b m i Hb Hi Hn) | lia |].
  apply NZl; [lia | intros X; exact (N1 b m i Hb Hi X)].
- intros a Hi HnG Hno He. pose proof (transportb_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite Hkp; [exact (K3 a Hi HnG Hno He) | lia |].
  apply NZl; [lia | intros X; exact (N2 a X Hi)].
- intros c0 pos0 a Hin Hr Hn.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c0 pos0 HAR Hin) as (G4096 & Gce & _).
  pose proof (fs_frame_bytes_nonneg c0) as Hfs.
  assert (Ha : 0 <= a < YM05.alloc_ceiling).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc c0 pos0) (fs_frame_bytes c0) Hfs) as Hse.
    assert (Hd : (frame_addr lyc c0 pos0 + fs_frame_bytes c0) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc c0 pos0) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  rewrite Hkp; [exact (K4 c0 pos0 a Hin Hr Hn) | lia |].
  apply NZl; [lia | intros X; exact (N3 c0 pos0 a Hin Hr X)].
- intros a Ha Hw Hp. pose proof (K5 a Ha Hw Hp) as HpX.
  apply (apresent_of_aview segs);
    [lia | intros Hi; pose proof (transportb_segs_low a Hi) as Hl; unfold kLowMemEnd in Hl; lia |].
  rewrite Hkp; [exact (can_aview_vis (segs := segs) _ _ a HpX) | lia | exact (NZ a ltac:(lia) Hw)].
- exact Hpw.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Lemma bar_rel_holds : @bar_rel_stmt fx rc B MT.
Proof.
unfold bar_rel_stmt, bar_rel_at.
intros c RT OK pos ly2 S2 W2 mem2 md2 regs2 e a Bw' CUR RG Haok Hm Htw2 Hgf2.
pose proof RT as (_ & HCELLS & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGNE & _ & SF8 & _ & _ &
  _ & _ & SFREE).
pose proof OK as (HJc & Hret & Hra4 & Hgp & Htp & _).
destruct CUR as (HJ & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw & HS24).
destruct RG as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R25 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
(* the entry stack facts (build_and_receive_segs.v bar_ok_sp) *)
destruct (bar_ok_sp B MT c OK)
  as (HARc & HSPr & HCE & Hpres0 & Hsp16 & Hsp0al & Hlo & Hhi & HS1al & HS1r & Hwin0 & Hs16).
set (SP := bar_SP c) in *.
set (sp1 := bar_sp1 c) in *.
set (F := bar_F c pos) in *.
set (FL := flag_addr (cx_lyc c) BAR_CID pos) in *.
assert (ERS : ESTACK <= RECV_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (EBS : BAR_STK = 208 + RECV_STK) by exact bar_stk_eq.
assert (Hwin : SP - BAR_STK <= sp1 - ESTACK) by lia.
(* the frame *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
assert (Hin : In (BAR_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (Hfa : forall cid p, frame_addr ly2 cid p = frame_addr (cx_lyc c) cid p)
  by (intros cid p; unfold frame_addr; rewrite ELF; reflexivity).
assert (EFA : frame_addr ly2 BAR_CID pos = F) by (unfold F, bar_F; apply Hfa).
assert (EFL : flag_addr ly2 BAR_CID pos = FL) by (unfold FL, flag_addr; rewrite ELF; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin) as (_ & HFapp & HFpres & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ BAR_CID pos HAR2 Hin) as (HF64 & _ & _).
rewrite EFA in HFapp, HFpres, HFc, HF0, HF64, HFsh.
rewrite bar_fbytes in HFapp, HFpres, HFc, HFsh.
change (BAR_FBYTES / 8) with 256 in HFsh. unfold BAR_FBYTES in HFapp, HFpres, HFc, HFsh.
assert (HFd : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hbl : forall bm, In bm (ablocks B (cx_lyc c) (cx_Sc c)) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low (cx_lyc c) (cx_Sc c) ly2 S2 W2 mem2 md2 BAR_CID pos F FL
  HAR2 Hfrs Hbl ELF eq_refl eq_refl FFL) as (N1 & N2 & N3 & N4).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
(* ---- run A, +0x374 .. +0x378 ---- *)
pose proof (bra_entry W2 regs2 mem2) as HS.
assert (HEI : img_env VAL A_LIM (bra_E regs2)) by (unfold bra_E; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (bra_E regs2) (mrestrict (w_H W2) mem2)) by constructor.
assert (EWA : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (bra_E regs2) n = YK11.getr regs2 r)
  by (intros n r Hn; unfold bra_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + BAR_REL)) mem2 (YK11.seg_rom segs)) md2) Q) end.
paj_run_tok RUN HS HJ SHOK BR_B0.
{ br_awr_rs. apply awr_ok_x_nil. }
rename HF into HFa, HFr into HFra, HG into HGa.
lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
br_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + BR_C1)) A1 ltac:(apply codeptr_val; exact HEI).
br_reg HS (10%bv : bv 5) (w64 (SHADOW_OFF + F / 8 + 4)) A10
  ltac:(cbn [sv_denot]; rewrite (EWA 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R27).
br_reg HS (11%bv : bv 5) (w64 190) A11 ltac:(reflexivity).
br_kreg HS EWA (2%bv : bv 5) 2%nat R2 A2. br_kreg HS EWA (3%bv : bv 5) 3%nat R3 A3.
br_kreg HS EWA (4%bv : bv 5) 4%nat R4 A4. br_kreg HS EWA (8%bv : bv 5) 8%nat R8 A8.
br_kreg HS EWA (9%bv : bv 5) 9%nat R9 A9. br_kreg HS EWA (18%bv : bv 5) 18%nat R18 A18.
(* run A writes no byte *)
assert (KA : forall a0, 0 <= a0 < 2 ^ 64 -> ~ False ->
  aview segs (w_H W2) (ms_mem msA) a0 = aview segs (w_H W2) mem2 a0) by br_frame_kept HFra (fun _ : Z => False) A2.
(* +0x37c: __asan_set_shadow_f8 on the frame's shadow bytes 4 .. 193 *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_set_shadow_f8)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_set_shadow_at (SK := tfib_sink_head) segs B LAWS transportb_segs_low
    (transportb_sigma TB___asan_set_shadow_f8) 0xf8 (SF8 fx) TG.G_HARNESS_B W2 rg mm
    (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((BAR_CID, pos) :: cx_own c) ly2 S2 mdx (cx_k c + e) BAR_CID pos (SHADOW_OFF + F / 8 + 4) 190
    (sp1 - cx_sp0 c) (Z_to_bv 64 (BASE + BR_C1)) HJ) end.
  - left; reflexivity.
  - exact A10.
  - exact A11.
  - lia.
  - unfold shadow_addr. rewrite EFA. lia.
  - unfold shadow_addr. rewrite EFA, bar_fbytes. change (BAR_FBYTES / 8) with 256. lia.
  - unfold spZ at 1. rewrite A2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hs16, Hsp0al. reflexivity.
  - lia.
  - unfold BAR_STK, BAR_FRAME, BAR_ALIGN in *. lia.
  - exact A3.
  - exact A4.
  - exact A1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold BR_C1, AF_build_and_receive; lia | reflexivity]. }
cbv beta.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hk3 & Hgr3).
assert (T2 : YK11.getr regs3 2 = w64 sp1)
  by (transitivity (YK11.getr (ms_regs msA) 2); [exact (HP3 2 ltac:(unfold acallee_saved; lia)) | exact A2]).
assert (T3 : YK11.getr regs3 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs msA) 3); [exact (HP3 3 ltac:(unfold acallee_saved; lia)) | exact A3]).
assert (T4 : YK11.getr regs3 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs msA) 4); [exact (HP3 4 ltac:(unfold acallee_saved; lia)) | exact A4]).
assert (T8 : YK11.getr regs3 8 = w64 SP)
  by (transitivity (YK11.getr (ms_regs msA) 8); [exact (HP3 8 ltac:(unfold acallee_saved; lia)) | exact A8]).
assert (T9 : YK11.getr regs3 9 = w64 sp1)
  by (transitivity (YK11.getr (ms_regs msA) 9); [exact (HP3 9 ltac:(unfold acallee_saved; lia)) | exact A9]).
assert (T18 : YK11.getr regs3 18 = w64 F)
  by (transitivity (YK11.getr (ms_regs msA) 18); [exact (HP3 18 ltac:(unfold acallee_saved; lia)) | exact A18]).
(* the slot s1 + 24 (the frame), kept by run A and the call *)
assert (HS24b : rdword (aview segs (w_H W2) mem3) (sp1 + 24) = Some F).
{ rewrite <- HS24. apply rdword_ext. intros i Hi.
  rewrite (Hk3 (sp1 + 24 + i) ltac:(lia) ltac:(unfold SHADOW_OFF; lia)).
  exact (KA (sp1 + 24 + i) ltac:(lia) ltac:(tauto)). }
(* ---- run B, +0x380 .. +0x394 ---- *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
destruct (al_frames _ _ LAWS _ _ _ _ _ BAR_CID pos HAR3 Hin) as (_ & _ & HFb3 & _).
rewrite EFA, bar_fbytes in HFb3. unfold BAR_FBYTES in HFb3.
clear HS SHOK HEI.
pose proof (brb_entry W2 regs3 mem3 F sp1 T9 T18 HF0 ltac:(lia) HF64 ltac:(lia)
  ltac:(intros a0 Ha0; exact (proj1 (HFb3 a0 ltac:(lia)))) HS24b) as HS.
assert (HEI : img_env VAL A_LIM (brb_E regs3)) by (unfold brb_E; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (brb_E regs3) (mrestrict (w_H W2) mem3)) by constructor.
assert (EWB : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (brb_E regs3) n = YK11.getr regs3 r)
  by (intros n r Hn; unfold brb_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (UB18 : bv_unsigned (ew (brb_E regs3) 18) = F)
  by (rewrite (EWB 18%nat 18%bv eq_refl), T18; unfold w64; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + BR_C1)) mem3 (YK11.seg_rom segs)) md3) Q) end.
paj_run_tok RUN HS HJ3 SHOK BR_B0.
{ br_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ BAR_CID pos); [left; reflexivity | |].
  - intros a0 Ha0. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha0. rewrite UB18 in Ha0.
    left. unfold in_zr. cbn [fst snd]. rewrite bar_fbytes. unfold BAR_FBYTES.
    change (frame_addr (cx_lyc c) BAR_CID pos) with F. lia.
  - apply awr_ok_x_cons; [intros a0 Ha0; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha0; lia |].
    apply awr_ok_x_nil. }
rename HF into HFb, HFr into HFrb, HG into HGb.
lazymatch type of HS with context [restrict _ ?m] => rename m into msB end.
br_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + BR_C2)) B1 ltac:(apply codeptr_val; exact HEI).
br_reg HS (10%bv : bv 5) (w64 F) B10
  ltac:(cbn [sv_denot]; rewrite (EWB 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact T18).
br_reg HS (11%bv : bv 5) (w64 1696) B11 ltac:(reflexivity).
br_kreg HS EWB (2%bv : bv 5) 2%nat T2 B2. br_kreg HS EWB (3%bv : bv 5) 3%nat T3 B3.
br_kreg HS EWB (4%bv : bv 5) 4%nat T4 B4. br_kreg HS EWB (8%bv : bv 5) 8%nat T8 B8.
(* run B writes the frame's first word only *)
assert (KB : forall a0, 0 <= a0 < 2 ^ 64 -> ~ (F <= a0 < F + 8) ->
  aview segs (w_H W2) (ms_mem msB) a0 = aview segs (w_H W2) mem3 a0)
  by br_frame_kept HFrb (fun x : Z => F <= x < F + 8) UB18.
(* the frame's last word, at the stack free *)
assert (HFLB : rdword (aview segs (w_H W2) (ms_mem msB)) (frame_addr ly2 BAR_CID pos + fs_frame_bytes BAR_CID - 8)
  = Some (flag_addr ly2 BAR_CID pos)).
{ rewrite EFA, EFL, bar_fbytes. unfold BAR_FBYTES.
  rewrite <- HFLw. unfold BAR_FBYTES. apply rdword_ext. intros i Hi.
  rewrite (KB (F + 2048 - 8 + i) ltac:(lia) ltac:(lia)).
  pose proof (br_frame_not_shadow F (2040 + i) HFapp ltac:(lia)) as HNS.
  rewrite (Hk3 (F + 2048 - 8 + i) ltac:(lia) ltac:(lia)).
  exact (KA (F + 2048 - 8 + i) ltac:(lia) ltac:(tauto)). }
(* +0x398: __asan_stack_free_5 releases the frame *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_stack_free_5)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_stack_free_cls_at (SK := tfib_sink_head) segs B LAWS transportb_segs_low
    (transportb_sigma TB___asan_stack_free_5) BAR_CID (SFREE fx) FFL
    TG.G_HARNESS_B W2 rg mm (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    (cx_own c) ly2 S2 mdx (cx_k c + e) pos 1696 (sp1 - cx_sp0 c) (Z_to_bv 64 (BASE + BR_C2)) HJ3) end.
  - rewrite EFA. exact B10.
  - exact B11.
  - exact HFLB.
  - unfold spZ at 1. rewrite B2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hs16, Hsp0al. reflexivity.
  - lia.
  - unfold BAR_STK, BAR_FRAME, BAR_ALIGN in *. lia.
  - exact B3.
  - exact B4.
  - exact B1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold BR_C2, AF_build_and_receive; lia | reflexivity]. }
cbv beta.
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hf54 & Hk4 & Hpres4).
assert (V3 : YK11.getr regs4 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs msB) 3); [exact (HP4 3 ltac:(unfold acallee_saved; lia)) | exact B3]).
assert (V4 : YK11.getr regs4 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs msB) 4); [exact (HP4 4 ltac:(unfold acallee_saved; lia)) | exact B4]).
assert (V8 : YK11.getr regs4 8 = w64 SP)
  by (transitivity (YK11.getr (ms_regs msB) 8); [exact (HP4 8 ltac:(unfold acallee_saved; lia)) | exact B8]).
(* every byte outside the own frame and the runtime entries' window is the cut's *)
assert (KP4 : forall a0, 0 <= a0 < 2 ^ 64 -> ~ (sp1 - ESTACK <= a0 < sp1) -> ~ dkg_nf BAR_CID F FL a0 ->
  aview segs (w_H W2) mem4 a0 = aview segs (w_H W2) mem2 a0).
{ intros a0 Ha0 Hw Hd. unfold dkg_nf in Hd.
  rewrite bar_fbytes in Hd. unfold BAR_FBYTES in Hd. change (2048 / 8) with 256 in Hd.
  assert (Hd1 : ~ (F <= a0 < F + 2048)) by (intros X; apply Hd; left; exact X).
  assert (Hd2 : ~ (SHADOW_OFF + F / 8 <= a0 < SHADOW_OFF + F / 8 + 256))
    by (intros X; apply Hd; right; left; exact X).
  assert (Hd3 : a0 <> FL) by (intros X; apply Hd; right; right; exact X).
  clear Hd.
  rewrite (Hk4 a0 Ha0); [| unfold shadow_addr; rewrite EFA, bar_fbytes; unfold BAR_FBYTES;
      change (2048 / 8) with 256; lia
    | rewrite EFL; exact Hd3 | lia].
  rewrite (KB a0 Ha0 ltac:(lia)).
  rewrite (Hk3 a0 Ha0 ltac:(lia)).
  exact (KA a0 Ha0 ltac:(tauto)). }
(* the 13 saved words at the stack free's return *)
assert (HSo : forall o, In o BAR_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold BAR_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia |]). destruct Ho. }
assert (Hsaved4 : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem4) (SP - fst o) =
    Some (bv_unsigned (YK11.getr (cx_regs c) (Z_to_bv 5 (snd o))))) BAR_SAVED).
{ apply Forall_forall. intros o Hino. cbv beta.
  pose proof (proj1 (Forall_forall _ _) Hsaved o Hino) as Ho. cbv beta in Ho.
  pose proof (HSo o Hino) as Hfo.
  rewrite <- Ho. apply rdword_ext. intros i Hi.
  apply KP4; [lia | lia | intros X; pose proof (N4 _ X); lia]. }
(* ---- run C, +0x39c .. +0x3e4 ---- *)
clear HS SHOK HEI.
pose proof (brc_entry W2 regs4 (cx_regs c) mem4 SP V8 ltac:(lia) Hsaved4) as HS.
assert (HEI : img_env VAL A_LIM (brc_E regs4 (cx_regs c))) by (unfold brc_E; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (brc_E regs4 (cx_regs c)) (mrestrict (w_H W2) mem4))
  by constructor.
assert (EWC : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (brc_E regs4 (cx_regs c)) n = YK11.getr regs4 r)
  by (intros n r Hn; unfold brc_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + BR_C2)) mem4 (YK11.seg_rom segs)) md4) Q) end.
paj_run_tok RUN HS HJ4 SHOK BR_B0.
{ br_awr_rs.
  apply awr_ok_x_cons; [intros a0 Ha0; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha0; lia |].
  apply awr_ok_x_nil. }
rename HF into HFc', HFr into HFrc, HG into HGc.
lazymatch type of HS with context [restrict _ ?m] => rename m into msC end.
(* run C writes no byte *)
assert (KC : forall a0, 0 <= a0 < 2 ^ 64 -> ~ False ->
  aview segs (w_H W2) (ms_mem msC) a0 = aview segs (w_H W2) mem4 a0) by br_frame_kept HFrc (fun _ : Z => False) V8.
(* the registers at the ret *)
assert (C1e : YK11.getr (ms_regs msC) 1 = YK11.getr (cx_regs c) 1).
{ br_regv HS. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (HP : aregs_preserved (cx_regs c) (ms_regs msC)).
{ intros r Hr. apply br_saved_cases in Hr.
  destruct Hr as [-> | [-> | [-> | Hr]]].
  - br_regv HS. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EWC 8%nat 8%bv eq_refl), V8.
    unfold SP, bar_SP, w64, spZ. apply Z_to_bv_bv_unsigned.
  - br_regv HS. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EWC 3%nat 3%bv eq_refl), V3.
    symmetry. exact Hgp.
  - br_regv HS. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EWC 4%nat 4%bv eq_refl), V4.
    symmetry. exact Htp.
  - destruct Hr as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
      br_regv HS; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity. }
assert (Hpc : v_jalr (YK11.getr (ms_regs msC) 1) 0 = YK11.getr (cx_regs c) 1) by (rewrite C1e; exact Hret).
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md5 := mdx) in * end.
clearbody md5.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  eapply (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb) W2 Ex ssx msx md5 _ HS eq_refl
    ltac:(clear; vm_compute; reflexivity)) end.
intros mat3.
set (md6 := with_vm_backing (m_vm_lazy md5) mat3 md5).
pose proof (ajournal_gx_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ4)
  as HJ6.
fold md6 in HJ6. clearbody md6.
(* every byte outside the own frame and the window is the cut's, at the return *)
assert (KP5 : forall a0, 0 <= a0 < 2 ^ 64 -> ~ ((sp1 - ESTACK <= a0 < sp1) \/ dkg_nf BAR_CID F FL a0) ->
  aview segs (w_H W2) (ms_mem msC) a0 = aview segs (w_H W2) mem2 a0).
{ intros a0 Ha0 Hn. rewrite (KC a0 Ha0 ltac:(tauto)).
  apply KP4; [exact Ha0 | intros X; apply Hn; left; exact X | intros X; apply Hn; right; exact X]. }
assert (Eab' : ablocks B ly2 (stack_free_state BAR_CID pos S2) = ablocks B ly2 S2)
  by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
unfold bar_post, transport_bar_post, transport_cg_post.
exists ly2, (stack_free_state BAR_CID pos S2), (ms_regs msC), (ms_mem msC), md6, e.
split; [rewrite Hpc; reflexivity|].
split; [exact He|].
split; [exact HJ6|].
split; [exact HP|].
split; [exact (can_sf_frames BAR_CID pos S2 (frames (cx_Sc c)) Hfrs)|].
split; [rewrite Eab'; exact Hperm|].
split.
{ apply (br_kept_nfz LAWS TG.G_HARNESS_B (cx_lyc c) (cx_Sc c) ly2 S2 (cx_W c) (cx_memc c) (cx_mdc c) W2 mem2 md2
    (ms_mem msC) (SP - BAR_STK) SP BAR_CID pos F FL
    (recv_wr (bar_fr c)) (fun a0 => (sp1 - ESTACK <= a0 < sp1) \/ dkg_nf BAR_CID F FL a0)
    HARc HAR2 Hfrs Hbl ELF eq_refl eq_refl FFL HCE ltac:(lia)).
  - intros a0 [X | X]; [left; lia | right; exact X].
  - exact HK.
  - exact KP5.
  - intros a0 Ha0. exact (br_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6 a0 ltac:(lia)). }
split.
{ replace (recv_cost MT (Z.of_nat (length (bar_frame (cx_dst c) (cx_src c) (cx_send c) (cx_ack c)
       (cx_retry c) (cx_cmd c) (cx_body c))))) with (recv_cost MT (bar_N c)).
  - unfold stack_free_state. apply (mo_le_set_fs_r MT MTF). exact Hmo.
  - f_equal. symmetry. exact (bar_ok_frame_len B MT c OK). }
(* X: the model's address, world and the world relation at the return *)
exists a, Bw'. split; [exact Haok|]. split; [exact Hm|]. split; [|exact Hgf2].
apply (tw_kept_GB (aview segs (w_H W2) mem2)); [exact Htw2|].
intros b n i Hbn Hi.
assert (HG : inG TG.G_HARNESS_B (b + i))
  by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
destruct (HGX _ HG) as [HiG _].
pose proof (transportb_segs_low _ HiG) as Hl. unfold kLowMemEnd in Hl.
apply KP5; [lia|]. intros [X | X]; [lia | exact (N2 _ X HiG)].
Qed.

End s.

(* The release piece of the walk of build_and_receive, at every machine, run ceiling, record and meter. *)
Theorem bar_rel_piece : forall fx rc B MT, @bar_rel_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@bar_rel_holds fx rc B MT). Qed.
