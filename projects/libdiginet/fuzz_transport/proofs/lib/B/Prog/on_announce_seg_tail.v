(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 697 of its 763 lines of code are new or changed and 1858 lines of the source are left out. *)
(* on_announce_seg_tail: Lemma onann_tail_piece : onann_tail_stmt (lib/B/Prog/OnannCutB.v), the release of the walk
   of on_announce on fuzz_transport.asan-ubsan: its three cuts onann_fnrel_at (+0x5f4, 0x882bc), onann_nrel_at
   (+0x61c, 0x882e4) and onann_arel_at (+0x644, 0x8830c), offsets +0x5f4 .. +0x770 of the listing
   lib/B/Prog/DgnTransportBList.v (AF_on_announce = 0x6a28; 0x882bc .. 0x88438), to the `ret` and the statement's
   post (on_announce_cg.v transport_onann_post).

   What the code does (s2 = SHADOW_OFF + F / 8, s3 = s9 = F, the class-3 frame). +0x5f4 `li a0, -8` and nine
   `sb a0, i(s2)`: fn's shadow bytes 28 .. 36 := 0xf8; +0x61c the same for n's shadow bytes 14 .. 22; +0x644 the same
   for a's shadow bytes 4 .. 8; +0x65c `lui`/`addiw` a0 = 0x45e0360e and +0x664 `sd a0, 0(s3)`: the frame's first
   word; +0x668 `beq s9, zero`: s9 = F >= 4096, so the real-stack arm at +0x684 is never entered (the run's atom fact
   of s9); +0x66c `li a1, 64`, +0x670 `mv a0, s2`, +0x674 `jal __asan_set_shadow_f5`: the frame's 64 shadow bytes
   := 0xf5 (lib/A/Prog/TransportRtCg.v aset_shadow_realizes, through TransportGCg.v aj_gx_entry_at in the caller's
   G journal); +0x678 `ld a0, 504(s9)`: the flag pointer FL from the frame's last word; +0x67c `sb zero, 0(a0)`: the
   flag byte, which releases the frame (lib/B/Prog/TransportGFrameB.v gx_flag_store_pi); +0x680 `j +0x734`; +0x734
   `addi sp, s0, -192`; the 13 reloads +0x738 .. +0x768 of ra, s0, s1, s2 .. s11 from the words the prologue saved
   below the entry sp (OnannCutB.v ONANN_SAVED); +0x76c `addi sp, sp, 192`; +0x770 `ret`.

   Run 1 (one run of the token engine over the caller's G journal, lib/B/Prog/TransportGRunB.v paj_run_x, from any of
   the three cuts: the state ss_otl1 pc is the same at each) goes through the shadow stores, the header word and the
   branch and stops at __asan_set_shadow_f5's entry; its regions: the frame's shadow bytes 4 .. 36 (s2, written) and
   the frame's first word (s3, written), both bytes of the own frame (TransportGFrame.v awr_ok_x_cons_own). otl_post1
   carries the cut's facts (onann_rel_cur) to the run's memory (otl_cur_step: the run changed only own-frame bytes,
   TransportGFrame.v dk_kept_nf_gw; the saved words lie above alloc_ceiling, the frame's last word is not a byte the
   run wrote, the world's bytes are image bytes, TWorldB.v tw_kept_GB). otl_call takes the call: the callee's post
   (its 64 bytes 0xf5, every other byte kept) lifted into the G journal by aj_gx_entry_at, onann_rel_cur carried
   again by otl_cur_step, the registers the release reads kept (aregs_preserved). Run 2 (otl_rel2: one run of the
   plain position-abstract engine, lib/A/Prog/PaSym.v sym_run_pi, from +0x678 to the `ret`, which
   DgnTransportBPaLib.v paj_ret_at takes) is inside gx_flag_store_pi; its regions: the frame's last word (s9,
   offset 504, read: FL, atom 32), the flag byte (atom 32, written) and the 13 saved words below s0 = the entry sp
   (read, atoms 33 .. 45).

   The post (TransportGCg.v transport_cg_post over G_HARNESS_B): the caller's G journal after the flag store, with
   own and the frame released (stack_free_state); the callee-saved registers are the 13 reloads, sp = s0 = the entry
   sp, gp and tp untouched; the frames the caller's (CanKit.v can_sf_frames); the state changed in st_fs only, so the
   meter bound is the cut's (mo_le_set_fs_r). What the call kept: the cut's acall_kept_g, carried over run 2 by
   dk_kept_nf_gw (the run changed only the flag byte, a byte of TransportGCg.v dkg_nf). The world relation at Bw':
   the cut's (onann_rel_cur), kept since no byte of G is a byte of dkg_nf (tw_kept_GB). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit TransportGFrameB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The two runs                                                       *)
(* ------------------------------------------------------------------ *)

(* The return address of __asan_set_shadow_f5 (`ld a0, 504(s9)`) and the `ret` of on_announce. *)
Definition OTL_RA : Z := AF_on_announce + 0x678.
Definition OTL_RET : Z := AF_on_announce + 0x770.

(* Run 1, from a release cut to __asan_set_shadow_f5's entry: the frame's shadow bytes 4 .. 36 (s2, atom 18) and its
   first word (s3, atom 19), both written; s9 (atom 25) at least 4096 decides `beq s9, zero`. *)
Definition otl_rg_sh : YP09.region := YP09.mkRegion (Some 18%nat) 4 37 4 37 [].
Definition otl_rg_hd : YP09.region := YP09.mkRegion (Some 19%nat) 0 8 0 8 [].
Definition otl_facts1 : facts :=
  mkFacts [(18%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3); (19%nat, mkAF 4096 (2 ^ 47) 6);
           (25%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition ss_otl1 (pc : Z) : sstate := mkSS pc sr_atoms [otl_rg_sh; otl_rg_hd] None otl_facts1.
(* No shadow token: the run reads no shadow byte and writes the frame's. *)
Definition OTL_Bx : sv := SLit 0.
Definition OTL_B0 : Z * Z := (0, 0).
(* The bytes run 1 may change, and the bytes __asan_set_shadow_f5 fills. *)
Definition otl_Z1 (F x : Z) : Prop :=
  (F <= x < F + 8) \/ (SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 37).
Definition otl_Zc (F x : Z) : Prop := SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 64.

(* Run 2, from +0x678 to the `ret`: the frame's last word (s9 + 504, atom 25; FL = atom 32), the flag byte (atom 32,
   written), the 13 saved words below s0 (atom 8; ONANN_SAVED in its order, atoms 33 .. 45). *)
Definition otl_rg_fp : YP09.region :=
  YP09.mkRegion (Some 25%nat) 504 512 0 0 [YP09.mkChunk 504 (CVal 8 (SOff 32 0))].
Definition otl_rg_fl : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition otl_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
Definition otl_facts2 : facts := mkFacts [(25%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition ss_otl2 : sstate := mkSS OTL_RA sr_atoms [otl_rg_fp; otl_rg_fl; otl_rg_sv] None otl_facts2.
Definition OTL_FUEL : N := 64.
Definition otl_ss_end : sstate := Eval vm_compute in fst (sym_runN_pi transportb_tpi OTL_FUEL ss_otl2).
Definition otl_st_end : prun_status tbsym := Eval vm_compute in snd (sym_runN_pi transportb_tpi OTL_FUEL ss_otl2).
Lemma otl_run2 : sym_runN_pi transportb_tpi OTL_FUEL ss_otl2 = (otl_ss_end, otl_st_end).
Proof. vm_compute. reflexivity. Qed.
Lemma otl_stop : can_plain_stop otl_st_end.
Proof. exact I. Qed.
(* Run 2 stops at the `ret` at +0x770. *)
Lemma otl_end_pc : ss_pc otl_ss_end = OTL_RET.
Proof. reflexivity. Qed.

(* Run 2's valuation past the registers: FL, then the entry values of the saved registers. *)
Definition otl_extra (regs : bvmap 5 word) (FL : Z) : list word :=
  w64 FL :: map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) ONANN_SAVED.

(* The value of register r in the machine state of HS: its symbolic value, computed. *)
Ltac otl_regv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.
(* A register of the machine state of HS (a position-abstract state, or the state at a callee's entry). *)
Ltac otl_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* A register the run does not write, from the equation Q of its value at the run's start. *)
Ltac otl_kreg HS Elo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    otl_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (Elo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* Run 1's write right: its two regions are bytes of the own frame (its shadow bytes, its first word). *)
Ltac otl_awr U18 U19 EFA ESH pos :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  eapply TransportGFrame.awr_ok_x_cons_own with (cid := ONANN_CID) (pos := pos); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U18 in Ha;
    right; unfold in_zr; cbn [fst snd]; rewrite EFA, ESH; change (fs_frame_bytes ONANN_CID / 8) with 64; lia |];
  eapply TransportGFrame.awr_ok_x_cons_own with (cid := ONANN_CID) (pos := pos); [left; reflexivity | |];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes ONANN_CID) with 512; lia |];
  apply awr_ok_x_nil.

(* F / 8 of a 64-aligned frame address, as facts the kit's lia reads (it keeps F / 8 an atom). *)
Lemma otl_f8 : forall F, 4096 <= F -> F mod 64 = 0 -> F + 512 <= 2 ^ 47 ->
  F = 8 * (F / 8) /\ 512 <= F / 8 <= 2 ^ 44.
Proof.
intros F HF0 HF64 HFc.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (HF8 : F / 8 = 8 * (F / 64))
  by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
split; lia.
Qed.

Section otl. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Local Notation POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b :=
  (@transport_onann_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).
Local Notation AT pc regs2 mem2 md2 :=
  (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + pc)) mem2 (YK11.seg_rom segs)) md2).

(* The callee's return address and the `ret` in the image's addresses. *)
Lemma otl_pcs : BASE + OTL_RA = 0x88340 /\ BASE + OTL_RET = 0x88438.
Proof. split; reflexivity. Qed.

(* The 512 bytes of an application frame are apart from their 64 shadow bytes. *)
Lemma otl_shf : forall F, 4096 <= F -> F mod 64 = 0 -> F + 512 <= 2 ^ 47 -> in_app F 512 ->
  SHADOW_OFF + F / 8 + 64 <= F \/ F + 512 <= SHADOW_OFF + F / 8.
Proof.
intros F HF0 HF64 HFc HFapp. destruct (otl_f8 F HF0 HF64 HFc) as (D8 & B8).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
  [right | left]; unfold SHADOW_OFF; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic states hold of the machine states                    *)
(* ------------------------------------------------------------------ *)

Definition otl_E1 (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

(* Run 1's state at any of the three cuts. *)
Lemma otl_entry1 : forall (W : world segs) regs mem F pc,
  YK11.getr regs 18 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 19 = w64 F -> YK11.getr regs 25 = w64 F ->
  4096 <= F -> F mod 64 = 0 -> F + 512 <= 2 ^ 47 ->
  (SHADOW_OFF + F / 8 + 64 <= F \/ F + 512 <= SHADOW_OFF + F / 8) ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 37 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (otl_E1 regs) (ss_otl1 pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F pc R18 R19 R25 HF0 HF64 HFc HSHF Hpf Hpsh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (HF8 : F / 8 = 8 * (F / 64))
  by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
set (E := otl_E1 regs).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, otl_E1; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF + F / 8)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U19 : bv_unsigned (ew E 19) = F)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = F)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_otl1.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks otl_rg_sh otl_rg_hd base_val];
    rewrite ?U18, ?U19.
  + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, otl_rg_sh, otl_rg_hd.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U18, U19.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct HSHF as [HS1 | HS1]; repeat split; first [exact I | lia].
- unfold otl_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18, U19, U25.
  change (2 ^ 3) with 8. change (2 ^ 6) with 64.
  assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
  { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
    apply Z.mod_mul. lia. }
  unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Definition otl_E2 (regs2 regs : bvmap 5 word) (FL : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 (otl_extra regs FL)).

Lemma otl_ew_reg2 : forall regs2 regs FL n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (otl_E2 regs2 regs FL) n = YK11.getr regs2 r.
Proof. intros regs2 regs FL n r Hn. unfold otl_E2. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma otl_ew_x2 : forall regs2 regs FL j, (j < 14)%nat ->
  ew (otl_E2 regs2 regs FL) (32 + j) = nth j (otl_extra regs FL) (Z_to_bv 64 0).
Proof. intros regs2 regs FL j Hj. unfold otl_E2. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* Run 2's state at +0x678. *)
Lemma otl_entry2 : forall (W : world segs) (regs2 regs : bvmap 5 word) mem (F FL SP : Z),
  YK11.getr regs2 8 = w64 SP -> YK11.getr regs2 25 = w64 F ->
  4096 <= F -> F mod 64 = 0 -> F + 512 <= alloc_ceiling ->
  4096 <= FL < alloc_ceiling -> (FL < F \/ F + 512 <= FL) ->
  alloc_ceiling <= SP - 104 -> SP <= 2 ^ 47 ->
  apresent (w_H W) mem FL ->
  rdword (aview segs (w_H W) mem) (F + 504) = Some FL ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (SP - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED ->
  st_ok_pi segs VAL (otl_E2 regs2 regs FL) ss_otl2
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OTL_RA)) mem (YK11.seg_rom segs))).
Proof.
intros W regs2 regs mem F FL SP R8 R25 HF0 HF64 HFc HFL HFLF HSP HSP47 HpFL HFLw Hsaved.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := otl_E2 regs2 regs FL).
assert (U8 : bv_unsigned (ew E 8) = SP)
  by (unfold E; rewrite (otl_ew_reg2 regs2 regs FL 8 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = F)
  by (unfold E; rewrite (otl_ew_reg2 regs2 regs FL 25 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small;
      lia).
assert (E32 : ew E 32 = w64 FL) by exact (otl_ew_x2 regs2 regs FL 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
unfold ONANN_SAVED in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss_otl2.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks otl_rg_fp otl_rg_fl otl_rg_sv
      base_val];
    rewrite ?U8, ?U25, ?U32.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ F 504 8 (SOff 32 0) FL);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ HFLw).
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
  unfold extent_of_region, otl_rg_fp, otl_rg_fl, otl_rg_sv.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U8, U25, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct HFLF as [HL1 | HL1]; repeat split; first [exact I | lia].
- unfold otl_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25.
  change (2 ^ 6) with 64.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The cut's facts over a step that changes only own-frame bytes      *)
(* ------------------------------------------------------------------ *)

(* sp0 is 16-aligned (the caller's journal at entry, YCbq.v astk_ok). *)
Lemma otl_sp0 : forall {STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F},
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  sp0 mod 16 = 0.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F HFIX.
destruct HFIX as (HJ0 & _).
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
exact (proj1 Hstk0).
Qed.

(* What a release cut's facts give: AR at the call and at the cut state, the own frame (live, at F, its 512 bytes and
   64 shadow bytes present), the call's window above alloc_ceiling and below 2 ^ 47, the flag byte FL (present, a
   byte below alloc_ceiling outside the frame), and the realigned sp1. *)
Lemma otl_cur_ar : forall {STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
          ly2 S2 W2 mem2 md2 e},
  AR_laws segs B -> frame_flag_lawP segs B ->
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
  @AR rc segs B lyc Sc W memc mdc /\ @AR rc segs B ly2 S2 W2 mem2 md2 /\
  (forall c p, flag_addr ly2 c p = flag_addr lyc c p) /\
  In (ONANN_CID, pos) (frames S2) /\ frame_addr ly2 ONANN_CID pos = F /\
  (forall a, F <= a < F + 512 -> apresent (w_H W2) mem2 a /\ ~ aowned B ly2 S2 a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H W2) mem2 (SHADOW_OFF + F / 8 + i)) /\
  4096 <= F /\ F mod 64 = 0 /\ F + 512 <= alloc_ceiling /\ in_app F 512 /\
  alloc_ceiling <= spZ regs - ONANN_STK /\ spZ regs <= 2 ^ 47 /\
  apresent (w_H W2) mem2 (flag_addr lyc ONANN_CID pos) /\
  4096 <= flag_addr lyc ONANN_CID pos < alloc_ceiling /\
  (flag_addr lyc ONANN_CID pos < F \/ F + 512 <= flag_addr lyc ONANN_CID pos) /\
  spZ regs - 208 <= sp1 <= spZ regs - 192.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ly2 S2 W2 mem2
  md2 e LAWS FFL HFIX HCUR.
pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw).
unfold ONANN_FBYTES in HFc, HFapp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4304 <= ONANN_STK).
{ unfold ONANN_STK, ONANN_FRAME, ONANN_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
assert (Hin : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 ONANN_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
assert (Efl : forall c p, flag_addr ly2 c p = flag_addr lyc c p)
  by (intros c p; unfold flag_addr; rewrite ELF; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ ONANN_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
destruct (FFL ly2 S2 W2 mem2 md2 ONANN_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
rewrite Efl in HFLp, HFLo, HFL4096, HFLc.
change (fs_frame_bytes ONANN_CID) with 512 in HFb.
change (fs_frame_bytes ONANN_CID / 8) with 64 in HFsh.
rewrite EFA in HFb, HFsh.
assert (HFLF : flag_addr lyc ONANN_CID pos < F \/ F + 512 <= flag_addr lyc ONANN_CID pos).
{ destruct (Z_lt_le_dec (flag_addr lyc ONANN_CID pos) F) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec (flag_addr lyc ONANN_CID pos) (F + 512)) as [h2|h2]; [|right; exact h2].
  exfalso. exact (proj2 (HFb _ (conj h h2)) HFLo). }
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192).
{ rewrite Esp1. unfold ONANN_FRAME.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (r := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  lia. }
refine (conj HARc (conj HAR2 (conj Efl (conj Hin (conj EFA (conj HFb (conj _ (conj HF0 (conj HF64 (conj HFc
  (conj HFapp (conj _ (conj _ (conj HFLp (conj (conj HFL4096 HFLc) (conj HFLF Hsp1)))))))))))))))).
- intros i Hi. exact (proj1 (HFsh i Hi)).
- lia.
- lia.
Qed.

(* onann_rel_cur at a later memory memY of the same state, when the step changed only bytes Zs of the frame's first
   word or of its 64 shadow bytes, and the G journal holds at memY. *)
Lemma otl_cur_step : onann_laws B MT ->
  forall {STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
          ly2 S2 W2 memX mdX e memY mdY} (Zs : Z -> Prop),
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_rel_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b pos F ly2 S2 W2 memX mdX e ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 memY mdY (k + e) ->
  (forall a, Zs a -> (F <= a < F + 8) \/ otl_Zc F a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) memY a = aview segs (w_H W2) memX a) ->
  (forall a, apresent (w_H W2) memX a -> apresent (w_H W2) memY a) ->
  onann_rel_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b pos F ly2 S2 W2 memY mdY e.
Proof.
intros HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 memX mdX e memY mdY Zs HFIX HCUR HJY HZ KP GA.
pose proof HLAWS as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & FFL & HGX & _).
pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & EF & _).
pose proof HCUR as (HCUR0 & HTW2 & Hgf2).
pose proof HCUR0 as (HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw).
destruct (otl_cur_ar LAWS FFL HFIX HCUR0) as (HARc & HAR2 & _ & _ & _ & _ & _ & HF0 & HF64 & HFc & HFapp & Hwin &
  H47 & _ & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HBS : 4304 <= ONANN_STK).
{ unfold ONANN_STK, ONANN_FRAME, ONANN_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (TransportGFrame.dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 memX mdX ONANN_CID pos F
  (flag_addr lyc ONANN_CID pos) HAR2 Hfrs Hbl ELF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
pose proof (otl_shf F HF0 HF64 ltac:(lia) HFapp) as HSHF.
unfold otl_Zc in HZ.
assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos) a ->
  aview segs (w_H W2) memY a = aview segs (w_H W2) memX a).
{ intros a Ha Hn. apply KP; [exact Ha|]. intros Hz. apply Hn. unfold dkg_nf.
  change (fs_frame_bytes ONANN_CID / 8) with 64. change (fs_frame_bytes ONANN_CID) with 512.
  destruct (HZ a Hz) as [H1 | H1]; [left | right; left]; lia. }
unfold onann_rel_cur. split; [|split; [|exact Hgf2]].
- unfold onann_cur.
  split; [exact HJY|]. split; [exact He|]. split; [exact Hfrs|]. split; [exact Hperm|].
  split; [exact ELF|]. split; [exact Hmo|].
  split.
  { exact (TransportGFrame.dk_kept_nf_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc ly2 S2 W2
      memX mdX memY (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F (flag_addr lyc ONANN_CID pos) (onann_wr Bw b)
      HARc HAR2 Hfrs Hbl ELF EF eq_refl FFL HK KD GA). }
  split.
  { apply Forall_forall. intros o Hin. cbv beta.
    pose proof (proj1 (Forall_forall _ _) Hsaved o Hin) as Hv. cbv beta in Hv.
    assert (Ho : 8 <= fst o <= 104).
    { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
    rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KD; [lia|]. intros Hn. pose proof (N4 _ Hn). lia. }
  { unfold ONANN_FBYTES in HFLw |- *. rewrite <- HFLw. apply YCbq.rdword_ext. intros i Hi. apply KP; [lia|].
    intros Hz. destruct (HZ _ Hz) as [H1 | H1]; [lia|]. destruct HSHF as [Hs | Hs]; lia. }
- apply (tw_kept_GB (aview segs (w_H W2) memX)); [exact HTW2|].
  intros b0 n i Hbn Hi.
  assert (HG : inG TG.G_HARNESS_B (b0 + i))
    by (unfold inG; apply Exists_exists; exists (b0, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
  destruct (HGX _ HG) as [HiG _].
  pose proof (transportb_segs_low _ HiG) as Hl. unfold kLowMemEnd in Hl.
  apply KD; [lia | intros Hn; exact (N2 _ Hn HiG)].
Qed.

(* ------------------------------------------------------------------ *)
(* 4. Run 2: the flag store, the reloads, the `ret`                      *)
(* ------------------------------------------------------------------ *)

Lemma otl_rel2 : onann_laws B MT ->
  forall {STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
          ly2 S2 W2 mem2 md2 e} (regs2 : bvmap 5 word),
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_rel_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b pos F ly2 S2 W2 mem2 md2 e ->
  onann_regs_rel regs regs2 sp1 F ->
  SRr segs W2 (AT OTL_RA regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).
Proof.
intros HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
pose proof HLAWS as (_ & _ & _ & _ & _ & _ & _ & LAWS & MTL & MTF & _ & ASF & FFL & HGX & _).
pose proof HFIX as (HJ0 & Hret & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & EF & _).
pose proof HCUR as (HCUR0 & HTW2 & Hgf2).
pose proof HCUR0 as (HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw).
destruct (otl_cur_ar LAWS FFL HFIX HCUR0) as (HARc & HAR2 & Efl & _ & _ & _ & _ & HF0 & HF64 & HFc & _ & Hwin &
  H47 & HFLp & HFLb & HFLF & _).
destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25).
unfold ONANN_FBYTES in HFLw. replace (F + 512 - 8) with (F + 504) in HFLw by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HBS : 4304 <= ONANN_STK).
{ unfold ONANN_STK, ONANN_FRAME, ONANN_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
set (FL := flag_addr lyc ONANN_CID pos) in *.
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (TransportGFrame.dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F FL
  HAR2 Hfrs Hbl ELF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
pose proof (otl_entry2 W2 regs2 regs mem2 F FL (spZ regs) R8 R25 HF0 HF64 HFc HFLb HFLF ltac:(lia) ltac:(lia)
  HFLp HFLw Hsaved) as HS.
set (E := otl_E2 regs2 regs FL) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, otl_E2; apply Eimg_env).
assert (U25 : bv_unsigned (ew E 25) = F)
  by (unfold E; rewrite (otl_ew_reg2 regs2 regs _ 25 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (otl_ew_x2 regs2 regs _ 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
(* +0x678 .. +0x770 in one run, the flag store at +0x67c releasing the frame. *)
refine (gx_flag_store_pi (SK := tfib_sink_head) B LAWS ASF FFL TG.G_HARNESS_B W2 OTL_FUEL E ss_otl2 otl_ss_end
  otl_st_end (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OTL_RA)) mem2 (YK11.seg_rom segs))
  STK sp0 FP ly S W0 mem0 md0 own ly2 S2 md2 (k + e) ONANN_CID pos _ HEI HS otl_run2 otl_stop HJ1 _ _ _ _).
- unfold ONANN_CID. lia.
- (* the run writes the flag byte only *)
  intros a (rg & Hinr & Ha). unfold ss_otl2 in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<- | [<- | [<- | []]]];
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi otl_rg_fp otl_rg_fl otl_rg_sv] in Ha; rewrite ?U32 in Ha.
  + lia.
  + right. rewrite Efl. change (flag_addr lyc ONANN_CID pos) with FL. lia.
  + lia.
- (* the flag byte is 0 after the run *)
  intros msr HSr.
  lazymatch goal with |- _ = Some _ =>
    let rr := eval vm_compute in (nth_error (ss_mem otl_ss_end) 1) in
    lazymatch rr with Some ?r1 =>
      pose proof (can_region_nth (segs := segs) _ _ msr 1 r1 HSr eq_refl) as HR1 end end.
  pose proof (can_field_of_region (segs := segs) E (ms_mem msr) 32 FL _ 0 1 0 1 0 1%N
    (SLit 0) 0 HR1 U32 ltac:(cbn [In]; auto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(cbn; lia)).
  lazymatch type of V with _ = Some (Z_to_bv 8 ?x) => replace x with 0 in V by (vm_compute; reflexivity) end.
  replace (FL + 0 + Z.of_nat 0) with FL in V by lia.
  rewrite Efl. exact V.
- (* the return *)
  intros ms2 mat2 HS2 HJ2 _ HF2 HG2.
  set (md3 := with_vm_backing (m_vm_lazy md2) mat2 md2) in *. clearbody md3.
  (* what the run kept: every byte outside the own frame, its shadow bytes and its flag byte; presence grows *)
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ dkg_nf ONANN_CID F FL a ->
    aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) mem2 a).
  { apply (kept_of_frame (segs := segs) E (ss_mem ss_otl2) (w_H W2) mem2 (ms_mem ms2) _ HF2).
    intros b0 wlo whi x Hw Hx. unfold ss_otl2, windows in Hw.
    cbn [ss_mem map In YP09.r_base YP09.r_wlo YP09.r_whi otl_rg_fp otl_rg_fl otl_rg_sv] in Hw.
    unfold dkg_nf. change (fs_frame_bytes ONANN_CID / 8) with 64. change (fs_frame_bytes ONANN_CID) with 512.
    destruct Hw as [Hw | [Hw | [Hw | []]]]; injection Hw as <- <- <-;
      cbn [base_val] in Hx; rewrite ?U25, ?U32 in Hx.
    + lia.
    + right; right. lia.
    + lia. }
  assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG2 Ha)).
  eapply (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb) W2 E otl_ss_end ms2 md3 _
    HS2 eq_refl ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat3 md3).
  pose proof (ajournal_gx_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ2)
    as HJ3.
  fold md4 in HJ3. clearbody md4.
  (* the registers at the ret *)
  assert (R1e : YK11.getr (ms_regs ms2) 1 = YK11.getr regs 1).
  { otl_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (HP : aregs_preserved regs (ms_regs ms2)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      otl_regv HS2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    all: first
      [ reflexivity
      | transitivity (YK11.getr regs2 3); [apply otl_ew_reg2; reflexivity | exact R3]
      | transitivity (YK11.getr regs2 4); [apply otl_ew_reg2; reflexivity | exact R4]
      | transitivity (YK11.getr regs2 8); [apply otl_ew_reg2; reflexivity|];
        rewrite R8; unfold w64, spZ; apply Z_to_bv_bv_unsigned ]. }
  assert (Hpc : v_jalr (YK11.getr (ms_regs ms2) 1) 0 = YK11.getr regs 1) by (rewrite R1e; exact Hret).
  assert (Eab' : ablocks B ly2 (stack_free_state ONANN_CID pos S2) = ablocks B ly2 S2)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  unfold transport_onann_post, transport_cg_post.
  exists ly2, (stack_free_state ONANN_CID pos S2), (ms_regs ms2), (ms_mem ms2), md4, e.
  split; [rewrite Hpc; reflexivity|].
  split; [exact He|].
  split; [exact HJ3|].
  split; [exact HP|].
  split; [exact (can_sf_frames ONANN_CID pos S2 (frames Sc) Hfrs)|].
  split; [rewrite Eab'; exact Hperm|].
  split.
  { (* the cut's acall_kept_g, over the run's one byte (the flag byte, a byte of dkg_nf) *)
    exact (TransportGFrame.dk_kept_nf_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc ly2 S2 W2
      mem2 md2 (ms_mem ms2) (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F FL (onann_wr Bw b)
      HARc HAR2 Hfrs Hbl ELF EF eq_refl FFL HK KP GA). }
  split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact Hmo|].
  (* the world relation at Bw': no byte of G is a byte the run wrote *)
  split; [|exact Hgf2].
  apply (tw_kept_GB (aview segs (w_H W2) mem2)); [exact HTW2|].
  intros b0 n i Hbn Hi.
  assert (HG : inG TG.G_HARNESS_B (b0 + i))
    by (unfold inG; apply Exists_exists; exists (b0, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
  destruct (HGX _ HG) as [HiG _].
  pose proof (transportb_segs_low _ HiG) as Hl. unfold kLowMemEnd in Hl.
  apply KP; [lia | intros Hn; exact (N2 _ Hn HiG)].
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The call of __asan_set_shadow_f5                                   *)
(* ------------------------------------------------------------------ *)

Lemma otl_call : onann_laws B MT -> onann_callees B MT ->
  forall {STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
          ly2 S2 W2 memT mdT e} (regsT : bvmap 5 word),
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_rel_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b pos F ly2 S2 W2 memT mdT e ->
  onann_regs_rel regs regsT sp1 F ->
  YK11.getr regsT 10 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regsT 11 = w64 64 ->
  YK11.getr regsT 1 = Z_to_bv 64 (BASE + OTL_RA) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transportb_sigma TB___asan_set_shadow_f5)) memT
      (YK11.seg_rom segs)) mdT)
    (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).
Proof.
intros HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 memT mdT e regsT HFIX HCUR HREGS R10 R11 R1.
pose proof HLAWS as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & FFL & HGX & _).
pose proof HCALL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HSET).
pose proof HFIX as (HJ0 & _ & _ & Hgp & Htp & _ & _ & _ & _ & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & Esp1 & _).
pose proof (otl_sp0 HFIX) as Hsp0a.
pose proof HCUR as (HCUR0 & _ & _).
pose proof HCUR0 as (HJ1 & _).
destruct (otl_cur_ar LAWS FFL HFIX HCUR0) as (_ & _ & _ & Hin2 & EFA & _ & _ & HF0 & HF64 & HFc & HFapp & Hwin &
  H47 & _ & _ & _ & Hsp1).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HBS : 4304 <= ONANN_STK).
{ unfold ONANN_STK, ONANN_FRAME, ONANN_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
assert (QSP : spZ regsT = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (O16 : (sp1 - sp0) mod 16 = 0).
{ apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). apply Z.divide_sub_r.
  - rewrite Esp1. exists (2 * ((spZ regs - ONANN_FRAME) / 32)). ring.
  - exact (proj1 (Z.mod_divide _ 16 ltac:(lia)) Hsp0a). }
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
(* +0x674: __asan_set_shadow_f5 (shadow_addr F, 64), lifted into the caller's G journal *)
eapply SRr_bind.
{ apply (@aj_gx_entry_at fx rc tfib_sink_head segs B LAWS transportb_segs_low TG.G_HARNESS_B 0 [] 4096
    (transportb_sigma TB___asan_set_shadow_f5) (otl_Zc F)
    (fun (_ : bvmap 5 word) (m : word -> option byte) =>
       (forall i, 0 <= i < 64 -> aview segs (w_H W2) m (SHADOW_OFF + F / 8 + i) = Some 0xf5) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ otl_Zc F a -> aview segs (w_H W2) m a = aview segs (w_H W2) memT a))
    W2 regsT memT STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 mdT (k + e) (sp1 - sp0)
    (Z_to_bv 64 (BASE + OTL_RA)) HGX eq_refl HJ1).
  - rewrite QSP. lia.
  - exact O16.
  - lia.
  - apply Z.le_refl.
  - lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold OTL_RA, AF_on_announce; lia | reflexivity].
  - exact G_HARNESS_B_rw.
  - intros a Ha _. split; [|lia].
    unfold awr_byte. right; right; right. unfold in_frames. exists ONANN_CID, pos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA, ESH. change (fs_frame_bytes ONANN_CID / 8) with 64.
    unfold otl_Zc in Ha. lia.
  - intros HPRE _.
    eapply SRr_mono.
    { exact (HSET fx ly2 S2 W2 regsT memT mdT ONANN_CID pos (SHADOW_OFF + F / 8) 64 HPRE Hin2 R10 R11 ltac:(lia)
        ltac:(rewrite EFA, ESH; lia) ltac:(rewrite EFA, ESH; change (fs_frame_bytes ONANN_CID / 8) with 64; lia)). }
    cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HAR' & HP' & Hsame & Hfill & Hkeep & _ & Hgr).
    unfold aentry_post. split; [reflexivity|]. exists regs', mem', md'.
    split; [reflexivity|]. split; [exact HAR'|]. split; [exact HP'|]. split; [exact Hsame|].
    split; [split; [exact Hfill | exact Hkeep]|].
    split; [intros a Ha Hn _; exact (Hkeep a Ha Hn) | exact Hgr]. }
cbv beta. intros W' c2 _ (-> & regsV & memV & mdV & -> & HJV & HPV & (_ & HkeepV) & _ & HgrV).
pose proof (otl_cur_step HLAWS (otl_Zc F) HFIX HCUR HJV ltac:(intros a Ha; right; exact Ha) HkeepV HgrV) as HCURV.
assert (HREGSV : onann_regs_rel regs regsV sp1 F).
{ unfold onann_regs_rel.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - transitivity (YK11.getr regsT 2); [exact (HPV 2 ltac:(unfold acallee_saved; lia)) | exact R2].
  - transitivity (YK11.getr regsT 3); [exact (HPV 3 ltac:(unfold acallee_saved; lia)) | exact R3].
  - transitivity (YK11.getr regsT 4); [exact (HPV 4 ltac:(unfold acallee_saved; lia)) | exact R4].
  - transitivity (YK11.getr regsT 8); [exact (HPV 8 ltac:(unfold acallee_saved; lia)) | exact R8].
  - transitivity (YK11.getr regsT 9); [exact (HPV 9 ltac:(unfold acallee_saved; lia)) | exact R9].
  - transitivity (YK11.getr regsT 18); [exact (HPV 18 ltac:(unfold acallee_saved; lia)) | exact R18].
  - transitivity (YK11.getr regsT 19); [exact (HPV 19 ltac:(unfold acallee_saved; lia)) | exact R19].
  - transitivity (YK11.getr regsT 25); [exact (HPV 25 ltac:(unfold acallee_saved; lia)) | exact R25]. }
exact (otl_rel2 HLAWS regsV HFIX HCURV HREGSV).
Qed.

(* ------------------------------------------------------------------ *)
(* 6. Run 1, from a release cut to the call                              *)
(* ------------------------------------------------------------------ *)

(* At __asan_set_shadow_f5's entry after run 1: the cut's facts at the run's memory, then the call. *)
Lemma otl_post1 : onann_laws B MT -> onann_callees B MT ->
  forall {STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
          ly2 S2 W2 mem2 md2 e} (regs2 regsF : bvmap 5 word) (memF : word -> option byte) (mdF : Model),
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_rel_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b pos F ly2 S2 W2 mem2 md2 e ->
  onann_regs_rel regs regs2 sp1 F ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 memF mdF (k + e) ->
  frame_of (otl_E1 regs2) [otl_rg_sh; otl_rg_hd] (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) memF) ->
  mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) memF) ->
  onann_regs_rel regs regsF sp1 F ->
  YK11.getr regsF 10 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regsF 11 = w64 64 ->
  YK11.getr regsF 1 = Z_to_bv 64 (BASE + OTL_RA) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 (transportb_sigma TB___asan_set_shadow_f5)) memF
      (YK11.seg_rom segs)) mdF)
    (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).
Proof.
intros HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 regsF memF mdF HFIX HCUR HREGS HJF HFr HG HREGSF R10 R11 R1.
pose proof HLAWS as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & FFL & _).
pose proof HCUR as (HCUR0 & _ & _).
destruct (otl_cur_ar LAWS FFL HFIX HCUR0) as (_ & _ & _ & _ & _ & _ & _ & HF0 & HF64 & HFc & _).
pose proof HREGS as (_ & _ & _ & _ & _ & R18 & R19 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (otl_E1 regs2) n = YK11.getr regs2 r)
  by (intros n r Hn; unfold otl_E1; apply can_ew_Eimg_Ereg_nat; exact Hn).
destruct (otl_f8 F HF0 HF64 ltac:(lia)) as (D8 & B8).
assert (U18 : bv_unsigned (ew (otl_E1 regs2) 18) = SHADOW_OFF + F / 8)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U19 : bv_unsigned (ew (otl_E1 regs2) 19) = F)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
(* run 1 wrote the frame's first word and its shadow bytes 4 .. 36 only *)
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ otl_Z1 F a ->
  aview segs (w_H W2) memF a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn.
  apply (kept_of_frame (segs := segs) (otl_E1 regs2) [otl_rg_sh; otl_rg_hd] (w_H W2) mem2 memF (otl_Z1 F) HFr);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. unfold windows in Hin.
  cbn [map In YP09.r_base YP09.r_wlo YP09.r_whi otl_rg_sh otl_rg_hd] in Hin.
  unfold otl_Z1.
  destruct Hin as [Hin | [Hin | []]]; injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U18, ?U19 in Hx.
  - right. lia.
  - left. lia. }
assert (GR : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memF a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (Z1sub : forall a, otl_Z1 F a -> (F <= a < F + 8) \/ otl_Zc F a)
  by (intros a [Ha | Ha]; [left | right; unfold otl_Zc]; lia).
pose proof (otl_cur_step HLAWS (otl_Z1 F) HFIX HCUR HJF Z1sub KF GR) as HCURF.
exact (otl_call HLAWS HCALL regsF HFIX HCURF HREGSF R10 R11 R1).
Qed.

(* The release from any of its three cuts. *)
Lemma otl_from : onann_laws B MT -> onann_callees B MT ->
  forall {STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
          ly2 S2 W2 mem2 md2 e} (regs2 : bvmap 5 word) (pc0 : Z),
  pc0 = ONANN_FNREL \/ pc0 = ONANN_NREL \/ pc0 = ONANN_AREL ->
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_rel_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b pos F ly2 S2 W2 mem2 md2 e ->
  onann_regs_rel regs regs2 sp1 F ->
  SRr segs W2 (AT pc0 regs2 mem2 md2) (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).
Proof.
intros HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 pc0 Hpc HFIX HCUR HREGS.
pose proof HLAWS as (_ & _ & _ & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & FFL & HGX & _).
pose proof HCUR as (HCUR0 & _ & _).
pose proof HCUR0 as (HJ1 & _).
destruct (otl_cur_ar LAWS FFL HFIX HCUR0) as (_ & _ & _ & _ & EFA & HFb & HFsh & HF0 & HF64 & HFc & HFapp & _).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
pose proof (otl_shf F HF0 HF64 ltac:(lia) HFapp) as HSHF.
destruct (otl_f8 F HF0 HF64 ltac:(lia)) as (D8 & B8).
pose proof (otl_entry1 W2 regs2 mem2 F pc0 R18 R19 R25 HF0 HF64 ltac:(lia) HSHF
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (HFsh i ltac:(lia)))) as HS.
clear HFb HFsh HSHF.
set (E := otl_E1 regs2) in HS.
assert (HEIa : img_env VAL A_LIM E) by (unfold E, otl_E1; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E, otl_E1; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF + F / 8)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U19 : bv_unsigned (ew E 19) = F)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs OTL_Bx (@nil shent) E (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
destruct Hpc as [-> | [-> | ->]].
- (* from +0x5f4: fn's, n's and a's shadow bytes, the header word, `beq s9`, to the call *)
  paj_run_tok RUN HS HJ1 SHOK OTL_B0.
  { otl_awr U18 U19 EFA ESH pos. }
  lazymatch type of HS with ?T ?sg ?EF ?ssx (restrict _ ?mf) => set (E5 := EF) in HS; rename mf into msF end.
  assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew E n)
    by (intros n Hn; unfold E5; rewrite ?ew_ewset_other by lia; reflexivity).
  otl_kreg HS E5lo EE (2%bv : bv 5) 2%nat R2 X2. otl_kreg HS E5lo EE (3%bv : bv 5) 3%nat R3 X3.
  otl_kreg HS E5lo EE (4%bv : bv 5) 4%nat R4 X4. otl_kreg HS E5lo EE (8%bv : bv 5) 8%nat R8 X8.
  otl_kreg HS E5lo EE (9%bv : bv 5) 9%nat R9 X9. otl_kreg HS E5lo EE (18%bv : bv 5) 18%nat R18 X18.
  otl_kreg HS E5lo EE (19%bv : bv 5) 19%nat R19 X19. otl_kreg HS E5lo EE (25%bv : bv 5) 25%nat R25 X25.
  otl_reg HS (10%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) X10
    ltac:(cbn [sv_denot]; rewrite (E5lo 18%nat ltac:(lia)), (EE 18%nat 18%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact R18).
  otl_reg HS (11%bv : bv 5) (w64 64) X11 ltac:(reflexivity).
  otl_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + OTL_RA)) X1 ltac:(apply codeptr_val; exact HEI).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_set_shadow_f5)) mm rom) mdx)
      Q) end.
  exact (otl_post1 HLAWS HCALL regs2 (ms_regs msF) (ms_mem msF) _ HFIX HCUR HREGS HJ1 HFr HG
    (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 (conj X19 X25))))))) X10 X11 X1).
- (* from +0x61c: n's and a's shadow bytes, the header word, `beq s9`, to the call *)
  paj_run_tok RUN HS HJ1 SHOK OTL_B0.
  { otl_awr U18 U19 EFA ESH pos. }
  lazymatch type of HS with ?T ?sg ?EF ?ssx (restrict _ ?mf) => set (E5 := EF) in HS; rename mf into msF end.
  assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew E n)
    by (intros n Hn; unfold E5; rewrite ?ew_ewset_other by lia; reflexivity).
  otl_kreg HS E5lo EE (2%bv : bv 5) 2%nat R2 X2. otl_kreg HS E5lo EE (3%bv : bv 5) 3%nat R3 X3.
  otl_kreg HS E5lo EE (4%bv : bv 5) 4%nat R4 X4. otl_kreg HS E5lo EE (8%bv : bv 5) 8%nat R8 X8.
  otl_kreg HS E5lo EE (9%bv : bv 5) 9%nat R9 X9. otl_kreg HS E5lo EE (18%bv : bv 5) 18%nat R18 X18.
  otl_kreg HS E5lo EE (19%bv : bv 5) 19%nat R19 X19. otl_kreg HS E5lo EE (25%bv : bv 5) 25%nat R25 X25.
  otl_reg HS (10%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) X10
    ltac:(cbn [sv_denot]; rewrite (E5lo 18%nat ltac:(lia)), (EE 18%nat 18%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact R18).
  otl_reg HS (11%bv : bv 5) (w64 64) X11 ltac:(reflexivity).
  otl_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + OTL_RA)) X1 ltac:(apply codeptr_val; exact HEI).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_set_shadow_f5)) mm rom) mdx)
      Q) end.
  exact (otl_post1 HLAWS HCALL regs2 (ms_regs msF) (ms_mem msF) _ HFIX HCUR HREGS HJ1 HFr HG
    (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 (conj X19 X25))))))) X10 X11 X1).
- (* from +0x644: a's shadow bytes, the header word, `beq s9`, to the call *)
  paj_run_tok RUN HS HJ1 SHOK OTL_B0.
  { otl_awr U18 U19 EFA ESH pos. }
  lazymatch type of HS with ?T ?sg ?EF ?ssx (restrict _ ?mf) => set (E5 := EF) in HS; rename mf into msF end.
  assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew E n)
    by (intros n Hn; unfold E5; rewrite ?ew_ewset_other by lia; reflexivity).
  otl_kreg HS E5lo EE (2%bv : bv 5) 2%nat R2 X2. otl_kreg HS E5lo EE (3%bv : bv 5) 3%nat R3 X3.
  otl_kreg HS E5lo EE (4%bv : bv 5) 4%nat R4 X4. otl_kreg HS E5lo EE (8%bv : bv 5) 8%nat R8 X8.
  otl_kreg HS E5lo EE (9%bv : bv 5) 9%nat R9 X9. otl_kreg HS E5lo EE (18%bv : bv 5) 18%nat R18 X18.
  otl_kreg HS E5lo EE (19%bv : bv 5) 19%nat R19 X19. otl_kreg HS E5lo EE (25%bv : bv 5) 25%nat R25 X25.
  otl_reg HS (10%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) X10
    ltac:(cbn [sv_denot]; rewrite (E5lo 18%nat ltac:(lia)), (EE 18%nat 18%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact R18).
  otl_reg HS (11%bv : bv 5) (w64 64) X11 ltac:(reflexivity).
  otl_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + OTL_RA)) X1 ltac:(apply codeptr_val; exact HEI).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_set_shadow_f5)) mm rom) mdx)
      Q) end.
  exact (otl_post1 HLAWS HCALL regs2 (ms_regs msF) (ms_mem msF) _ HFIX HCUR HREGS HJ1 HFr HG
    (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 (conj X19 X25))))))) X10 X11 X1).
Qed.

(* ------------------------------------------------------------------ *)
(* 7. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma onann_tail_piece : @onann_tail_stmt fx rc B MT.
Proof.
unfold onann_tail_stmt, onann_arel_at, onann_nrel_at, onann_fnrel_at.
split; [|split].
- intros HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
  exact (otl_from HLAWS HCALL regs2 ONANN_AREL (or_intror (or_intror eq_refl)) HFIX HCUR HREGS).
- intros HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
  exact (otl_from HLAWS HCALL regs2 ONANN_NREL (or_intror (or_introl eq_refl)) HFIX HCUR HREGS).
- intros HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
  exact (otl_from HLAWS HCALL regs2 ONANN_FNREL (or_introl eq_refl) HFIX HCUR HREGS).
Qed.

End otl.
