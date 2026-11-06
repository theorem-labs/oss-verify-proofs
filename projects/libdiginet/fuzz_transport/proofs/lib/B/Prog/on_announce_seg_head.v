(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 621 of its 765 lines of code are new or changed and 995 lines of the source are left out. *)
(* on_announce_seg_head: Lemma onann_head_piece : onann_head_stmt (lib/B/Prog/OnannCutB.v), the head of the walk of
   on_announce on fuzz_transport.asan-ubsan (0x87cc8 = transportb_sigma TB_on_announce, AF_on_announce = 0x6a28 of
   lib/B/Prog/DgnTransportBList.v), from the entry to the parse cut onann_lp_at (+0x19c, 0x87e64), which it is given.
   The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []); the runs are the
   position-abstract runs of lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x:
     run 1  +0x000 .. +0x070  the frame (`addi sp, sp, -192`, `sd zero, 0(sp)`, the 13 saves), s0 = the entry sp, the
                              realign into s1, s7 = now, s6 = fp, the two runtime cells through their GOT words (the
                              flag word is 1, so `beq a2, zero` at +0x06c is not taken), s8 = the shadow base,
                              s4 = s, a0 = 352, up to `jal __asan_stack_malloc_3`;
     +0x074                   the class-3 stack malloc: the statement's astack_malloc_realizes premise through
                              lib/A/Prog/TransportGFrame.v gx_stack_malloc_at (image-free; the frame F in a0,
                              4096 <= F, its 512 bytes and 64 shadow bytes present, its last word the flag address);
     run 2  +0x078 .. +0x0e4  s9 = s3 = F, `bne s9, zero` taken (the real-stack arm of +0x08c .. +0x0a4 is not
                              reached), the 8-byte store of F at s1 + 80, s10 = a = F + 32, the frame's 24-byte
                              header (0x41b58ab3, the description string (A_OBJ 79), the function's address
                              (A_OBJ 80)) and s2 = the frame's first shadow byte (`srli s2, s3, 3`, `add s2, s2, s8`);
     run 3  +0x0e8 .. +0x198  the frame's 44 shadow bytes (352 bytes): 0..3 = 0xf1, 4..8 = 0 (a, usable), 9..13 = 0xf2,
                              14..22 = 0xf8 (n), 23..27 = 0xf2, 28..36 = 0xf8 (fn), 37..43 = 0xf3; the run stops at
                              the parse cut ONANN_LP.
   The head decides no branch by a model fact and stores no byte of G, so the cut carries the world relation at the
   ENTRY world Bw. The three written ranges are the frame's header [F, F + 24), its 44 shadow bytes and the machine
   frame's slot [sp1 + 80, sp1 + 88). What the call keeps (acall_kept_g) runs from the entry to the stack malloc's
   return (TransportGCg.v dk_kept_step_g, then dk_kept_trans_g with the call's acall_kept) and from there over those
   three ranges (dk_kept_own_g), at the empty written range; the cut's acall_kept_g over onann_wr Bw b is that,
   weakened. The cut's 5 zero shadow bytes of a (4 .. 8) are the `sb zero` stores of +0x0fc and +0x18c .. +0x198,
   read back off run 3's region (lib/B/Prog/CanKit.v can_field_of_region, lib/B/Prog/TransportGNoticeB.v
   aview_of_val_mem1). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI09 YG0s.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module YF0x := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.YF0x.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states of the three runs                            *)
(* ------------------------------------------------------------------ *)

(* No shadow band: no run of the head reads a shadow byte (the head has no instrumented check). *)
Definition ONH_B0 : Z * Z := (0, 0).

(* run 1, +0x000 .. +0x070: the stack frame and the four image cells (the shadow base's GOT word and its cell, the
   side-stack flag's GOT word and its cell; transport_cells rows 1, 2, 6, 7). *)
Definition onh_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff (A_OBJ 96) 0))].
Definition onh_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 96)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SLit 1))].
Definition onh_img_regions : smem := [got_regionP; bcell_regionP 32; onh_got_uar; onh_uar_cell].
Definition onh_regions1 : smem := stack_region ONANN_FRAME :: onh_img_regions.
Definition onh_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_onh1 : sstate := mkSS AF_on_announce sr_atoms onh_regions1 None onh_facts1.

(* run 2, +0x078 .. +0x0e4: the frame F in a0 (atom 10), the frame word at s1 + 80 (atom 9) and the frame's 24-byte
   header at F; s8 (atom 24) is the shadow base. `bne s9, zero` at +0x088 is decided by atom 10's PTR fact. *)
Definition ONH_C1 : Z := AF_on_announce + 0x78.
Definition ONH_C2 : Z := AF_on_announce + 0xe8.
Definition onh_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 80 88 80 88 [].
Definition onh_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition onh_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, YC4b.PTR 6); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_onh2 : sstate := mkSS ONH_C1 sr_atoms [onh_rg_slot; onh_rg_hdr] None onh_facts2.

(* run 3, +0x0e8 .. +0x198: the frame's 44 shadow bytes at s2 (atom 18), a run to the parse cut. *)
Definition onh_rg_sh : YP09.region := YP09.mkRegion (Some 18%nat) 0 44 0 44 [].
Definition onh_facts3 : facts := mkFacts [(18%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_onh3 : sstate := mkSS ONH_C2 sr_atoms [onh_rg_sh] None onh_facts3.

(* The words the prologue saves, as (offset from the entry stack pointer, register). *)
Definition onh_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].

(* ------------------------------------------------------------------ *)
(* 2. The engine's readers, as lib/B/Prog/DgnTransportBPaLib.v states them *)
(* ------------------------------------------------------------------ *)

Ltac onh_reg HS r v H tac :=
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
(* A register the run does not write, at the run's end, from the equation Q of its value at the run's start. *)
Ltac onh_kreg HS Elo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    onh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (Elo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac onh_region HS i HR :=
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
Ltac onh_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac onh_msname HS nm :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?mf) => rename mf into nm
  | st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into nm
  end.
Ltac onh_u64 x := pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
Ltac onh_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The addresses a run's regions can write, computed; each case is closed by lia from the window's bounds. *)
Ltac onh_windows Hin Hx :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx | ]).

Section hd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma onh_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 96) = FCells.UAR /\
  BASE + AF_on_announce = transportb_sigma TB_on_announce.
Proof. vm_compute. repeat split. Qed.

(* The valuation of every run of the head: the 32 registers and the shadow base (atom 32). *)
Definition onh_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).

Lemma onh_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (onh_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold onh_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma onh_ew_32 : forall regs, ew (onh_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. unfold onh_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma onh_ew_obj : forall regs i, (i < 97)%nat -> ew (onh_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold onh_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma onh_env_img : forall regs, img_env VAL A_LIM (onh_E regs).
Proof. intros regs. unfold onh_E. apply Eimg_env. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma onh_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 96) = Z_to_bv 64 (VAL (A_OBJ 96)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) onh_img_regions /\
  pairwise_disjoint E onh_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E95 E0 E96 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct onh_vals as (V1 & V95 & V0 & V96 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (Kguar : rdword (aview segs (w_H W) mem) FCells.GOT_UAR = Some FCells.UAR)
    by (apply (rdword_cell B ly); [unfold FCells.UAR; lia | exact (CH _ I7)]).
  assert (Kuar : rd32 (aview segs (w_H W) mem) FCells.UAR 1).
  { pose proof (CH _ I6) as H6. unfold cell_holds in H6. cbn [c_at c_val c_w z4 c4 aeval] in H6.
    intros k Hk. exact (H6 k Hk). }
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  split.
  - unfold onh_img_regions, got_regionP, bcell_regionP, onh_got_uar, onh_uar_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      split; [rewrite V1; unfold FCells.GOT_CELL_K; lia|].
      split; [rewrite V1; unfold FCells.GOT_CELL_K; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 95) 0) (VAL (A_OBJ 95)));
      [cbn [sv_denot]; rewrite E95, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite V95; unfold FCells.CELL_K; lia | lia |].
      rewrite Z.add_0_r, V1, V95. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E95) by (rewrite V95; unfold FCells.CELL_K; lia).
      split; [rewrite V95; unfold FCells.CELL_K; lia|].
      split; [rewrite V95; unfold FCells.CELL_K; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 95)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r, V95. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (rewrite V0; unfold FCells.GOT_UAR; lia).
      split; [rewrite V0; unfold FCells.GOT_UAR; lia|].
      split; [rewrite V0; unfold FCells.GOT_UAR; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 96) 0) (VAL (A_OBJ 96)));
      [cbn [sv_denot]; rewrite E96, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite V96; unfold FCells.UAR; lia | lia |].
      rewrite Z.add_0_r, V0, V96. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
    + rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) E96) by (rewrite V96; unfold FCells.UAR; lia).
      split; [rewrite V96; unfold FCells.UAR; lia|].
      split; [rewrite V96; unfold FCells.UAR; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 96)) 0 4 (SLit 1) 1); [reflexivity | lia | lia |].
      rewrite Z.add_0_r, V96. exact (can_val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold onh_img_regions, got_regionP, bcell_regionP, onh_got_uar, onh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E95) by (rewrite V95; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) E96) by (rewrite V96; unfold FCells.UAR; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V95, V0, V96. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The entry state of run 1 (the 13 saves and the zero word go into the stack region). *)
Lemma onh_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - ONANN_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (onh_E regs) ss_onh1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_on_announce)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_onh1, onh_regions1.
  assert (Usp : bv_unsigned (ew (onh_E regs) 2) = spZ regs)
    by (rewrite (onh_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (onh_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply onh_ew_32.
  destruct (onh_img_ok ly S W mem md (onh_E regs) HCELLS HAR
    (onh_ew_obj regs 1 ltac:(lia)) (onh_ew_obj regs 95 ltac:(lia))
    (onh_ew_obj regs 0 ltac:(lia)) (onh_ew_obj regs 96 ltac:(lia)) E32) as [HRs HPd].
  destruct onh_vals as (V1 & V95 & V0 & V96 & _).
  assert (VB : forall n v0, ew (onh_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (onh_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold ONANN_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold onh_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, onh_got_uar, onh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (onh_ew_obj regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (onh_ew_obj regs 95 ltac:(lia)))
      by (rewrite V95; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (onh_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) (onh_ew_obj regs 96 ltac:(lia)))
      by (rewrite V96; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V95, V0, V96. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, ONANN_FRAME.
    repeat split; first [exact I | lia].
  - unfold onh_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2: the slot s1 + 80 (atom 9) and the frame's header at F (atom 10), both writable and
   apart (the frame lies below the allocation ceiling, the machine frame above it). *)
Lemma onh_entry2 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  4096 <= F -> F + 512 <= alloc_ceiling -> F mod 64 = 0 -> alloc_ceiling <= spv ->
  (forall a, spv + 80 <= a < spv + 88 -> apresent (w_H W) mem a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (onh_E regs) ss_onh2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONH_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R24 Hsp Hsp32 HF0 HFc HF64 Hac Hps Hpf.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite restrict_mkst_fx. unfold ss_onh2.
  assert (U2 : bv_unsigned (ew (onh_E regs) 2) = spv)
    by (rewrite (onh_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (onh_E regs) 9) = spv)
    by (rewrite (onh_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (onh_E regs) 10) = F)
    by (rewrite (onh_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew (onh_E regs) 24) = SHADOW_OFF)
    by (rewrite (onh_ew_reg regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (onh_E regs) 32) = SHADOW_OFF)
    by (rewrite (onh_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold onh_rg_slot, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hps. lia.
    + unfold onh_rg_hdr, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
  - apply pairwise_disjoint_of_extents.
    unfold onh_rg_slot, onh_rg_hdr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold onh_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, YC4b.PTR. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U24, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 3: the frame's 44 shadow bytes at s2 (atom 18). *)
Lemma onh_entry3 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 18 = w64 SH -> SHADOW_OFF <= SH -> SH + 44 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 44 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (onh_E regs) ss_onh3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONH_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R18 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_onh3.
  assert (U18 : bv_unsigned (ew (onh_E regs) 18) = SH)
    by (rewrite (onh_ew_reg regs 18 18%bv eq_refl), R18; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold onh_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U18. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold onh_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold onh_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma onh_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' kk,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem'
    md' kk ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' kk HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Lemma onann_head_piece : @onann_head_stmt fx rc B MT.
Proof.
unfold onann_head_stmt. intros LP.
unfold transport_on_announce_cg_holds_stmt.
intros HPCS HCELLS HSC HGU HGNE HROU HRNE LAWS MTL MTF SMP ASF FFL ASM0 ANP0 PFR0 BCMP0 MSET0 NTC0 SST0 WAKE0 MON0 SHW0.
unfold transport_on_announce_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  HJe Hra Hra4 Hgp Htp H10 H11 H12 Hsp16 Hlo Hhi Hnow HDF Htw Hfn Hm HTF HTFG HROM HAP Hri1 Hri2 Hri3 Hcnt3 Hcnt1
  Hcnt2 Hev.
pose proof (ASM0 fx) as ASM.
pose proof (G_HARNESS_gx_ok B HGU) as HGX.
pose proof (G_HARNESS_gx_noerrno B HGNE) as HGN.
assert (HLAWS : @onann_laws rc B MT).
{ unfold onann_laws.
  split; [exact HPCS|]. split; [exact HCELLS|]. split; [exact HSC|]. split; [exact HGU|].
  split; [exact HGNE|]. split; [exact HROU|]. split; [exact HRNE|]. split; [exact LAWS|].
  split; [exact MTL|]. split; [exact MTF|]. split; [exact SMP|]. split; [exact ASF|].
  split; [exact FFL|]. split; [exact HGX | exact HGN]. }
assert (HCALL : @onann_callees rc B MT).
{ unfold onann_callees.
  split; [exact ASM0|]. split; [exact ANP0|]. split; [exact PFR0|]. split; [exact BCMP0|].
  split; [exact MSET0|]. split; [exact NTC0|]. split; [exact SST0|]. split; [exact WAKE0|].
  split; [exact MON0 | exact SHW0]. }
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FF : ONANN_FRAME = 192) by reflexivity.
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HBS : 4304 <= ONANN_STK).
{ unfold ONANN_STK, ONANN_FRAME, ONANN_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpres1 : forall a, spZ regs - ONANN_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
pose proof (onh_entry1 lyc Sc W regs memc mdc HCELLS HAR Hpres1 Hsp Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (onh_E regs)) by apply onh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (onh_E regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (onh_E regs) 2) = spZ regs)
  by (rewrite (onh_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof HJe as HJ.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_on_announce)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* ---- run 1, +0x000 .. +0x070 ---- *)
paj_run_tok RUN HS HJ SHOK ONH_B0.
{ onh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1. onh_msname HS ms1.
set (sp1 := 32 * ((spZ regs + -192) / 32)).
destruct (can_sp1_facts (spZ regs + -192) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192) by (clear - Hsp1r; lia).
assert (E2' : ew (onh_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (onh_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
onh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 27296)) R1 ltac:(apply codeptr_val; exact HEI).
onh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (onh_E regs) 2 (spZ regs) (-192) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
onh_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (onh_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
onh_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (onh_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
onh_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
onh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (onh_E regs) 2 (spZ regs) (-192) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
onh_reg HS (20%bv : bv 5) (w64 ONANN_S) R20
  ltac:(cbn [sv_denot]; rewrite (onh_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
onh_reg HS (22%bv : bv 5) (w64 fp) R22
  ltac:(cbn [sv_denot]; rewrite (onh_ew_reg regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
onh_reg HS (23%bv : bv 5) (w64 now) R23
  ltac:(cbn [sv_denot]; rewrite (onh_ew_reg regs 12 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H12).
onh_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) R24
  ltac:(cbn [sv_denot]; rewrite (onh_ew_32 regs), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* the thirteen words the prologue saved, read back from the stack region the run wrote *)
onh_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) onh_saved -> -104 <= o <= -8).
{ intros o r Hin. unfold onh_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) onh_saved ->
  rdword (aview segs (w_H W) (ms_mem ms1)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. unfold onh_saved in Hin.
  apply (YF0x.val_mem_rdword (w_H W) (ms_mem ms1) (spZ regs + o) (bv_unsigned (YK11.getr regs r))
    ltac:(onh_u64 (YK11.getr regs r))).
  apply (can_field_of_region (onh_E regs) _ 2 (spZ regs) _ (-192) 0 (-192) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r)) 0) (bv_unsigned (YK11.getr regs r)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (onh_ew_reg regs (Z.to_nat (bv_unsigned r)) r ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; onh_u64 (YK11.getr regs r)
  | cbn; lia ]. }
clear HRsk.
(* ---- +0x074: the class-3 stack malloc ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_stack_malloc_3)) mm rom)
    mdx) Q) end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (TransportGFrame.gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transportb_segs_low SMP ONANN_CID
    ASM ltac:(unfold ONANN_CID; lia) TG.G_HARNESS_B W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k
    (sp1 - sp0) (Z_to_bv 64 (BASE + 27296)) HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - exact Hcnt3. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ ONANN_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ ONANN_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ ONANN_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes ONANN_CID / 8) with 64 in HFsh.
change (fs_frame_bytes ONANN_CID) with 512 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc ONANN_CID pos) in *.
(* the thirteen saved words, kept by the class-3 call *)
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) onh_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho.
  rewrite <- (HSV o r Hin). unfold rdword. rewrite !(proj1 HK1) by lia. reflexivity. }
assert (Q2 : YK11.getr regs2 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms1) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact R2]).
assert (Q3 : YK11.getr regs2 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs ms1) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact R3]).
assert (Q4 : YK11.getr regs2 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs ms1) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact R4]).
assert (Q8 : YK11.getr regs2 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms1) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8]).
assert (Q9 : YK11.getr regs2 9 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms1) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9]).
assert (Q20 : YK11.getr regs2 20 = w64 ONANN_S)
  by (transitivity (YK11.getr (ms_regs ms1) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
assert (Q22 : YK11.getr regs2 22 = w64 fp)
  by (transitivity (YK11.getr (ms_regs ms1) 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact R22]).
assert (Q23 : YK11.getr regs2 23 = w64 now)
  by (transitivity (YK11.getr (ms_regs ms1) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact R23]).
assert (Q24 : YK11.getr regs2 24 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms1) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact R24]).
clear HS.
set (memT := ms_mem ms1) in *. set (regsT := ms_regs ms1) in *. clearbody memT regsT. clear ms1.
(* what the call keeps from memc to mem2 (the memory the stack malloc returned) *)
assert (Hwin : forall a, spZ regs - ONANN_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 192 <= a < spZ regs) ->
  aview segs (w_H W) memT a = aview segs (w_H W) memc a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 192 <= x < spZ regs) HFr1);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. onh_windows Hin Hx; first [rewrite ?Usp in Hx; lia | destruct Hin]. }
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W memT (spZ regs - ONANN_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc memT
    (spZ regs - ONANN_STK) (spZ regs) (fun _ => False) (fun x => spZ regs - 192 <= x < spZ regs) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - intros a Ha Hn. exact (KT a Ha Hn).
  - intros a Ha. exact (apresent_grows _ _ _ a HG1 Ha).
  - intros a Ha _. lia.
  - intros b0 m i Hb Hi Hzs. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a Ha Hi _ _ _. pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  - intros cid pos0 a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
rewrite Zplus_minus in HK1.
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W mem2 (spZ regs - ONANN_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W memT W mem2 (spZ regs - ONANN_STK) (spZ regs)
    (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False)); [lia | lia | exact Kg1 | | lia | lia | tauto].
  apply acall_kept_g_of. exact HK1. }
assert (GK2 : gx_kept segs TG.G_HARNESS_B W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS_B W memc W memT W mem2).
  - intros a Ha. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Ha) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS_B lyc Sc W memT W mem2 _ _ _ HGX HGN HK1). }
clear KT Kg1 HF1 HFr1 HG1.
(* ---- run 2, +0x078 .. +0x0e4: the frame word at s1 + 80, the header, s2 = the frame's shadow address ---- *)
pose proof (onh_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q24 ltac:(lia) Hsp1al ltac:(lia) ltac:(lia) HF64
  ltac:(lia)
  ltac:(intros a Ha; apply (onh_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); lia)
  ltac:(intros a Ha; apply Hfpres; lia)) as HS.
assert (HEI2 : img_env VAL A_LIM (onh_E regs2)) by apply onh_env_img.
clear HEI. rename HEI2 into HEI.
assert (SHOK2 : sh_ok segs (SOff 32 0) (@nil shent) (onh_E regs2) (mrestrict (w_H W) mem2)) by constructor.
clear SHOK. rename SHOK2 into SHOK.
assert (U9a : bv_unsigned (ew (onh_E regs2) 9) = sp1)
  by (rewrite (onh_ew_reg regs2 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
assert (U10a : bv_unsigned (ew (onh_E regs2) 10) = F)
  by (rewrite (onh_ew_reg regs2 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + ONH_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
clear HJ. rename HJ2 into HJ.
paj_run_to_tok RUNTO HS HJ SHOK ONH_B0 ONH_C2.
{ onh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9a in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  eapply (TransportGFrame.awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONANN_CID pos);
    [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10a in Ha.
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes ONANN_CID) with 512.
  change (frame_addr lyc ONANN_CID pos) with F. lia. }
rename HF into HF2, HFr into HFr2, HG into HG2. onh_msname HS ms3.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 80 <= a < sp1 + 88 \/ F <= a < F + 24) ->
  aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 80 <= x < sp1 + 88 \/ F <= x < F + 24) HFr2);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. onh_windows Hin Hx;
    first [rewrite ?U9a, ?U10a in Hx; first [left; lia | right; lia] | destruct Hin]. }
pose proof HG2 as G2. clear HF2 HFr2 HG2.
(* the registers at +0x0e8 *)
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (Ea := EF) in * end.
assert (Ealo : forall n, (n < 1024)%nat -> ew Ea n = ew (onh_E regs2) n)
  by (intros n Hn; unfold Ea; rewrite ?ew_ewset_other by lia; reflexivity).
assert (EA10 : ew Ea 10 = Z_to_bv 64 F)
  by (rewrite (Ealo 10%nat ltac:(lia)), (onh_ew_reg regs2 10 10%bv eq_refl); exact Ha0).
assert (EA24 : ew Ea 24 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (Ealo 24%nat ltac:(lia)), (onh_ew_reg regs2 24 24%bv eq_refl); exact Q24).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
onh_kreg HS Ealo (onh_ew_reg regs2) (2%bv : bv 5) 2%nat Q2 T2.
onh_kreg HS Ealo (onh_ew_reg regs2) (3%bv : bv 5) 3%nat Q3 T3.
onh_kreg HS Ealo (onh_ew_reg regs2) (4%bv : bv 5) 4%nat Q4 T4.
onh_kreg HS Ealo (onh_ew_reg regs2) (8%bv : bv 5) 8%nat Q8 T8.
onh_kreg HS Ealo (onh_ew_reg regs2) (9%bv : bv 5) 9%nat Q9 T9.
onh_kreg HS Ealo (onh_ew_reg regs2) (20%bv : bv 5) 20%nat Q20 T20.
onh_kreg HS Ealo (onh_ew_reg regs2) (22%bv : bv 5) 22%nat Q22 T22.
onh_kreg HS Ealo (onh_ew_reg regs2) (23%bv : bv 5) 23%nat Q23 T23.
onh_kreg HS Ealo (onh_ew_reg regs2) (24%bv : bv 5) 24%nat Q24 T24.
onh_reg HS (18%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T18
  ltac:(exact (can_denot_shadow Ea 10 24 F SHADOW_OFF EA10 EA24 HFbv
               ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
onh_reg HS (19%bv : bv 5) (w64 F) T19
  ltac:(cbn [sv_denot]; rewrite (Ealo 10%nat ltac:(lia)), (onh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Ha0).
onh_reg HS (25%bv : bv 5) (w64 F) T25
  ltac:(cbn [sv_denot]; rewrite (Ealo 10%nat ltac:(lia)), (onh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Ha0).
onh_reg HS (26%bv : bv 5) (w64 (F + 32)) T26
  ltac:(cbn [sv_denot]; rewrite (Ealo 10%nat ltac:(lia)), (onh_ew_reg regs2 10 10%bv eq_refl), Ha0;
        unfold w64; rewrite (unsigned_lit_small F) by lia; reflexivity).
(* ---- run 3, +0x0e8 .. +0x198: the frame's 44 shadow bytes, to the parse cut ---- *)
pmkst HS.
clear HS SHOK HEI.
pose proof (onh_entry3 W (ms_regs ms3) (ms_mem ms3) (SHADOW_OFF + F / 8) T18
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2);
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
assert (HEI : img_env VAL A_LIM (onh_E (ms_regs ms3))) by apply onh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (onh_E (ms_regs ms3)) (mrestrict (w_H W) (ms_mem ms3)))
  by constructor.
assert (U18b : bv_unsigned (ew (onh_E (ms_regs ms3)) 18) = SHADOW_OFF + F / 8)
  by (rewrite (onh_ew_reg (ms_regs ms3) 18 18%bv eq_refl), T18; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONH_C2)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK ONH_B0 ONANN_LP.
{ onh_awr_rs.
  eapply (TransportGFrame.awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONANN_CID pos);
    [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U18b in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes ONANN_CID / 8) with 64.
  change (frame_addr lyc ONANN_CID pos) with F. unfold shadow_addr. lia. }
rename HF into HF3, HFr into HFr3, HG into HG3. onh_msname HS msF.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 44) ->
  aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) (ms_mem ms3) a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 44) HFr3);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. onh_windows Hin Hx; first [rewrite ?U18b in Hx; lia | destruct Hin]. }
pose proof HG3 as G3.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E3 := EF) in * end.
assert (E3lo : forall n, (n < 1024)%nat -> ew E3 n = ew (onh_E (ms_regs ms3)) n)
  by (intros n Hn; unfold E3; rewrite ?ew_ewset_other by lia; reflexivity).
onh_kreg HS E3lo (onh_ew_reg (ms_regs ms3)) (2%bv : bv 5) 2%nat T2 X2.
onh_kreg HS E3lo (onh_ew_reg (ms_regs ms3)) (3%bv : bv 5) 3%nat T3 X3.
onh_kreg HS E3lo (onh_ew_reg (ms_regs ms3)) (4%bv : bv 5) 4%nat T4 X4.
onh_kreg HS E3lo (onh_ew_reg (ms_regs ms3)) (8%bv : bv 5) 8%nat T8 X8.
onh_kreg HS E3lo (onh_ew_reg (ms_regs ms3)) (9%bv : bv 5) 9%nat T9 X9.
onh_kreg HS E3lo (onh_ew_reg (ms_regs ms3)) (18%bv : bv 5) 18%nat T18 X18.
onh_kreg HS E3lo (onh_ew_reg (ms_regs ms3)) (19%bv : bv 5) 19%nat T19 X19.
onh_kreg HS E3lo (onh_ew_reg (ms_regs ms3)) (20%bv : bv 5) 20%nat T20 X20.
onh_kreg HS E3lo (onh_ew_reg (ms_regs ms3)) (22%bv : bv 5) 22%nat T22 X22.
onh_kreg HS E3lo (onh_ew_reg (ms_regs ms3)) (23%bv : bv 5) 23%nat T23 X23.
onh_kreg HS E3lo (onh_ew_reg (ms_regs ms3)) (24%bv : bv 5) 24%nat T24 X24.
onh_kreg HS E3lo (onh_ew_reg (ms_regs ms3)) (25%bv : bv 5) 25%nat T25 X25.
onh_kreg HS E3lo (onh_ew_reg (ms_regs ms3)) (26%bv : bv 5) 26%nat T26 X26.
(* a's five shadow bytes 4 .. 8, the `sb zero` stores of +0x0fc and +0x18c .. +0x198 *)
onh_region HS 0%nat HRsh.
assert (USH : bv_unsigned (ew E3 18) = SHADOW_OFF + F / 8) by (rewrite E3lo by lia; exact U18b).
assert (SH4 : aview segs (w_H W) (ms_mem msF) (SHADOW_OFF + F / 8 + 4) = Some 0).
{ apply (aview_of_val_mem1 (w_H W) (ms_mem msF) (SHADOW_OFF + F / 8 + 4) 0); [|lia].
  exact (can_field_of_region E3 _ 18 (SHADOW_OFF + F / 8) _ 0 44 0 44 4 1%N (SLit 0) 0 HRsh USH
    ltac:(onh_in) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (SH5 : aview segs (w_H W) (ms_mem msF) (SHADOW_OFF + F / 8 + 5) = Some 0).
{ apply (aview_of_val_mem1 (w_H W) (ms_mem msF) (SHADOW_OFF + F / 8 + 5) 0); [|lia].
  exact (can_field_of_region E3 _ 18 (SHADOW_OFF + F / 8) _ 0 44 0 44 5 1%N (SLit 0) 0 HRsh USH
    ltac:(onh_in) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (SH6 : aview segs (w_H W) (ms_mem msF) (SHADOW_OFF + F / 8 + 6) = Some 0).
{ apply (aview_of_val_mem1 (w_H W) (ms_mem msF) (SHADOW_OFF + F / 8 + 6) 0); [|lia].
  exact (can_field_of_region E3 _ 18 (SHADOW_OFF + F / 8) _ 0 44 0 44 6 1%N (SLit 0) 0 HRsh USH
    ltac:(onh_in) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (SH7 : aview segs (w_H W) (ms_mem msF) (SHADOW_OFF + F / 8 + 7) = Some 0).
{ apply (aview_of_val_mem1 (w_H W) (ms_mem msF) (SHADOW_OFF + F / 8 + 7) 0); [|lia].
  exact (can_field_of_region E3 _ 18 (SHADOW_OFF + F / 8) _ 0 44 0 44 7 1%N (SLit 0) 0 HRsh USH
    ltac:(onh_in) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (SH8 : aview segs (w_H W) (ms_mem msF) (SHADOW_OFF + F / 8 + 8) = Some 0).
{ apply (aview_of_val_mem1 (w_H W) (ms_mem msF) (SHADOW_OFF + F / 8 + 8) 0); [|lia].
  exact (can_field_of_region E3 _ 18 (SHADOW_OFF + F / 8) _ 0 44 0 44 8 1%N (SLit 0) 0 HRsh USH
    ltac:(onh_in) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
clear HRsh.
assert (ZSH : forall i, 4 <= i < 9 -> aview segs (w_H W) (ms_mem msF) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | ->]]]]; [exact SH4 | exact SH5 | exact SH6 | exact SH7 | exact SH8]. }
(* ---- the facts the cut carries, at the memory of +0x19c ---- *)
lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?bb ?g ?xo ?o ?stk ?sp ?fpp ?l ?s ?w0 ?m0
    ?d0 ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (mdF := md') in * end.
assert (KF : forall a, 0 <= a < 2 ^ 64 ->
  ~ (F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 44 \/ sp1 + 80 <= a < sp1 + 88) ->
  aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  rewrite (K3 a Ha ltac:(intros X; apply Hn; tauto)).
  exact (K2 a Ha ltac:(intros X; apply Hn; tauto)). }
assert (GF : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem msF) a).
{ intros a Ha. apply (apresent_grows _ _ _ a G3). exact (apresent_grows _ _ _ a G2 Ha). }
assert (NGF : forall a, F <= a < F + 512 -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  exact (frm_img segs B LAWS _ _ _ _ _ ONANN_CID pos a HAR2 Hin2
    ltac:(change (fs_frame_bytes ONANN_CID) with 512; lia) Hi). }
assert (NGH : forall a, SHADOW_OFF <= a -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl.
  unfold kLowMemEnd, SHADOW_OFF in *. lia. }
assert (NGS : forall a, F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 44 \/
  sp1 + 80 <= a < sp1 + 88 -> ~ inG TG.G_HARNESS_B a).
{ intros a [X | [X | X]];
  [apply NGF; lia | apply NGH; unfold SHADOW_OFF in *; lia | apply NGH; unfold SHADOW_OFF; lia]. }
assert (Htw2 : tw_at TMAP_B (aview segs (w_H W) mem2) Bw).
{ apply (tw_kept_GB (aview segs (w_H W) memc)); [exact Htw|]. intros b0 n i Hin Hi.
  apply GK2. unfold inG. apply Exists_exists. exists (b0, n).
  split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
assert (GXE : forall a, inG TG.G_HARNESS_B a -> aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) mem2 a).
{ intros a Hg.
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  apply KF; [lia|]. intros X. exact (NGS a X Hg). }
assert (HtwF : tw_at TMAP_B (aview segs (w_H W) (ms_mem msF)) Bw).
{ apply (tw_kept_GB (aview segs (w_H W) mem2)); [exact Htw2|]. intros b0 n i Hin Hi.
  apply GXE. unfold inG. apply Exists_exists. exists (b0, n).
  split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
(* what the call keeps, at the cut: the three ranges are the own frame's header, its shadow bytes and the slot *)
assert (KG : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W (ms_mem msF) (spZ regs - ONANN_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_own_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc S2 W memc mdc mem2 md2 mem2
    (ms_mem msF) (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F (flag_addr lyc ONANN_CID pos)
    (fun _ => False)
    (fun a => F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 44 \/ sp1 + 80 <= a < sp1 + 88)
    HGX HAR HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL); [lia | lia | intros a [] | | exact Kg2 | | exact GF].
  - intros a [X | [X | X]].
    + right; right; left. unfold dkg_nf. left. change (fs_frame_bytes ONANN_CID) with 512. lia.
    + right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes ONANN_CID / 8) with 64.
      unfold shadow_addr. lia.
    + left. lia.
  - intros a Ha Hn. exact (KF a Ha Hn). }
(* the thirteen saved words and the frame's last word, at the cut *)
assert (HSVF : forall (o : Z) (r : bv 5), In (o, r) onh_saved ->
  rdword (aview segs (w_H W) (ms_mem msF)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho. rewrite <- (HSV2 o r Hin).
  apply YCbq.rdword_ext. intros i Hi. apply KF; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HFWF : Forall (fun o : Z * Z => rdword (aview segs (w_H W) (ms_mem msF)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ unfold ONANN_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
    replace (spZ regs - o) with (spZ regs + - o) by ring;
    apply (HSVF (- o) (Z_to_bv 5 r)); unfold onh_saved; cbn [In];
    repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end. }
assert (HFLF : rdword (aview segs (w_H W) (ms_mem msF)) (F + ONANN_FBYTES - 8) =
  Some (flag_addr lyc ONANN_CID pos)).
{ rewrite <- Hflag. unfold ONANN_FBYTES. apply YCbq.rdword_ext. intros i Hi. apply KF; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  intros [X | [X | X]]; [lia | | lia].
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
assert (CUR : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F lyc S2 W
  (ms_mem msF) mdF 0).
{ refine (conj _ (conj _ (conj Hfrs2 (conj _ (conj eq_refl (conj HMO (conj _ (conj HFWF HFLF)))))))).
  - rewrite Z.add_0_r. exact HJ.
  - split; [lia|]. vm_compute. discriminate.
  - rewrite Eab2. apply Permutation_refl.
  - apply (acall_kept_g_weaken segs B TG.G_HARNESS_B lyc Sc W memc W (ms_mem msF) (spZ regs - ONANN_STK)
      (spZ regs) (fun _ => False) (onann_wr Bw b)); [tauto | exact KG]. }
(* the caller's facts, as the cut states them *)
assert (HRI : onann_ri Bw).
{ unfold onann_ri. split; [exact Hri1|]. split; [exact Hri2 | exact Hri3]. }
assert (HFIX : onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F).
{ unfold onann_fix.
  split; [exact HJe|]. split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp|].
  split; [exact Htp|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|].
  split; [exact Hsp16|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hnow|].
  split; [exact HDF|]. split; [exact Htw|]. split; [exact Hfn|]. split; [exact Hm|].
  split; [exact HTF|]. split; [exact HTFG|]. split; [exact HROM|]. split; [exact HAP|].
  split; [exact HRI|]. split; [exact Hcnt3|]. split; [exact Hcnt1|]. split; [exact Hcnt2|].
  split; [exact Hev|].
  split; [unfold sp1, ONANN_FRAME; replace (spZ regs - 192) with (spZ regs + -192) by lia; reflexivity|].
  split; [reflexivity|]. split; [exact HF0|]. split; [exact HF64|].
  split; [unfold ONANN_FBYTES; lia | unfold ONANN_FBYTES; exact HFapp]. }
(* ---- the parse cut, +0x19c ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_LP)) mm rom) mdx) Q) end.
apply (LP HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F lyc S2 W (ms_mem msF) _ (ms_regs msF) HFIX).
- unfold onann_lp_cur. exact (conj CUR (conj HtwF ZSH)).
- unfold onann_regs_pf, onann_regs_ign, onann_regs_rel, ONANN_A.
  refine (conj (conj (conj X2 (conj _ (conj _ (conj X8 (conj X9 (conj X18 (conj X19 X25)))))))
    (conj X20 X24)) (conj X22 (conj X23 X26))).
  + rewrite X3. symmetry. exact Hgp.
  + rewrite X4. symmetry. exact Htp.
Qed.

End hd.
