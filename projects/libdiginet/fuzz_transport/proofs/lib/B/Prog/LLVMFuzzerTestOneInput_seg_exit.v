(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 369 of its 412 lines of code are new or changed and 1881 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_exit: lc_exit_ok, the EXIT segment (lc_exit_stmt of
   lib/B/Prog/LLVMFuzzerTestOneInput_segs.v) of the image-B walk of fuzz_transport.asan-ubsan's
   LLVMFuzzerTestOneInput: offsets +0x188 .. +0x240 and +0x2f8 .. +0x338 of the listing
   lib/B/Prog/DgnTransportBList.v (0x81428 .. 0x814e0 and 0x81598 .. 0x815d8), from the cut lc_st_exit to the slot's
   post lc_post.

   What the code does. +0x188 `li a0, -8` and the four `sb a0, i(s2)` at +0x18c .. +0x198: io's four shadow bytes
   (s2 = SHADOW_OFF + F / 8, the frame's shadow) become 0xf8, io out of scope. +0x19c `lui` / +0x1a0 `addiw`
   a0 = 0x45e0360e, +0x1a4 `ld a1, 136(s1)` and +0x1a8 `sd a0, 0(a1)`: that header word into the frame's first word
   (136(s1) holds F). +0x1ac `ld a1, 128(s1)` and +0x1b0 `beqz a1`: 128(s1) holds F >= 4096, so the real-stack arm
   +0x278 .. +0x2f4 is never entered (the engine decides the branch from the atom fact of the spilled frame
   address). +0x1b4 `li a0, -11` and the 32 `sb a0, i(s2)` at +0x1b8 .. +0x234: every shadow byte of F becomes 0xf5
   (a released frame). +0x238 `ld a0, 248(a1)`: the flag pointer FL from F's last word; +0x23c `sb zero, 0(a0)`: the
   flag byte goes to 0, which releases the frame. +0x240 `j +0x2f8`; +0x2f8 `mv a0, zero`; +0x2fc
   `addi sp, s0, -320`; the 13 reloads +0x300 .. +0x330 of ra, s0, s1, s2 .. s11 from the words the prologue saved
   below the entry sp (LLVMFuzzerTestOneInput_segs.v LF_SAVED); +0x334 `addi sp, sp, 320`; +0x338 `ret` to the
   caller's ra.

   How it is proved. One run of the plain position-abstract engine (lib/A/Prog/PaSym.v sym_run_pi: no shadow token,
   so a writable shadow region is allowed) covers +0x188 .. +0x338 and stops at the `ret`, which
   lib/B/Prog/DgnTransportBPaLib.v paj_ret_at takes; the release is lib/B/Prog/TransportGFrameB.v gx_flag_store_pi,
   which holds the caller's G journal across the run and hands it back with the frame gone (own = [], the state
   stack_free_state). The symbolic state at +0x188: the registers as atoms 0 .. 31, atom 32 the frame address
   spilled at 136(s1), atom 33 the one spilled at 128(s1), atom 34 the flag pointer FL, atoms 35 .. 47 the entry
   values of the 13 saved registers in LF_SAVED's order; regions: the two spill words (s1, read), the frame's first
   word (atom 32, written), its last word (atom 33, offset 248, read: FL), the frame's 32 shadow bytes (s2,
   written), the flag byte (atom 34, written) and the 13 saved words below s0 (read).

   The post (lc_post, lib/B/YCfn.v tfib_lib_post_x): the cut's journal at FP = [] with own = [] after the release,
   widened to the post's FP = [sink_token] by LLVMFuzzerTestOneInput_st.v lc_fp_token; its event count is at most
   EV_LIB (at most RECV_EV per reception, k <= OPS_MAX); the callee-saved registers are the 13 reloads, sp = s0 =
   the entry sp, gp and tp untouched; a0 = 0; the blocks are the entry's up to order (lc_core; the release changes
   no block); the file descriptors and the file system are the entry's (lc_journal_io at FP = []); asink_none and
   ameta_inv from the premises lp_sink_kept (its premise ~ sink_open_fp [] is YCbq.v sink_closed_nil) and
   lp_meta_kept; the meter from the cut's mo_le at k * lf_rcost MT <= OPS_MAX * lf_rcost MT =
   transport_llvmf_cost MT n <= XL n (lp_cost); and the input's bytes, which the run cannot touch (TransportGCg.v
   dkg_nf, apart from every block of the entry by lib/A/Prog/TransportGFrame.v dkg_nf_sep_gw). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YO09 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg CanKit TransportGFrameB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x188 and the run to the ret              *)
(* ------------------------------------------------------------------ *)

(* The `ret` of LLVMFuzzerTestOneInput. *)
Definition LX_RET : Z := 0x338.

(* The two spill words at 128(s1) and 136(s1) (atom 9 = s1), read: both hold the frame address F (atoms 33 and 32);
   the frame's first word (atom 32), written; its last word (atom 33, offset 248), read: the flag pointer FL
   (atom 34); the frame's 32 shadow bytes (atom 18 = s2), written; the flag byte (atom 34), written; the 13 saved
   words below s0 (atom 8), read: the word at s0 - o holds atom 35 + i for the i-th entry (o, r) of LF_SAVED. *)
Definition lx_rg_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 128 144 0 0
    [YP09.mkChunk 128 (CVal 8 (SOff 33 0)); YP09.mkChunk 136 (CVal 8 (SOff 32 0))].
Definition lx_rg_hd : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 8 [].
Definition lx_rg_fp : YP09.region :=
  YP09.mkRegion (Some 33%nat) 248 256 0 0 [YP09.mkChunk 248 (CVal 8 (SOff 34 0))].
Definition lx_rg_sh : YP09.region := YP09.mkRegion (Some 18%nat) 0 32 0 32 [].
Definition lx_rg_fl : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 1 [].
Definition lx_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 35 0)); YP09.mkChunk (-16) (CVal 8 (SOff 36 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 37 0)); YP09.mkChunk (-32) (CVal 8 (SOff 38 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 39 0)); YP09.mkChunk (-48) (CVal 8 (SOff 40 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 41 0)); YP09.mkChunk (-64) (CVal 8 (SOff 42 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 43 0)); YP09.mkChunk (-80) (CVal 8 (SOff 44 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 45 0)); YP09.mkChunk (-96) (CVal 8 (SOff 46 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 47 0))].
(* Both spilled frame addresses are at least 4096 (which decides the `beqz a1` at +0x1b0) and 32-aligned. *)
Definition lx_facts : facts := mkFacts [(32%nat, mkAF 4096 (2 ^ 47) 5); (33%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition lx_ss : sstate :=
  mkSS LO_EXIT sr_atoms [lx_rg_sp; lx_rg_hd; lx_rg_fp; lx_rg_sh; lx_rg_fl; lx_rg_sv] None lx_facts.
Definition LX_FUEL : N := 96.
Definition lx_ss_end : sstate := Eval vm_compute in fst (sym_runN_pi transportb_tpi LX_FUEL lx_ss).
Definition lx_st_end : prun_status tbsym := Eval vm_compute in snd (sym_runN_pi transportb_tpi LX_FUEL lx_ss).
Lemma lx_run : sym_runN_pi transportb_tpi LX_FUEL lx_ss = (lx_ss_end, lx_st_end).
Proof. vm_compute. reflexivity. Qed.
Lemma lx_stop : can_plain_stop lx_st_end.
Proof. exact I. Qed.
Lemma lx_end_pc : ss_pc lx_ss_end = LX_RET.
Proof. reflexivity. Qed.

(* The value of register r in the machine state of HS: its symbolic value, computed. *)
Ltac lx_regv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

(* A shadow address is a word: F / 8 is an atom of the goal, so its two bounds are given by hand (the kit's lia
   prunes a hypothesis that is not plain arithmetic). *)
Lemma lx_sh_u64 : forall F : Z, 0 <= F -> F < 2 ^ 64 -> 0 <= SHADOW_OFF + F / 8 < 2 ^ 64.
Proof.
intros F H0 H1.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as A.
pose proof (Z.div_lt_upper_bound F 8 (2 ^ 61) ltac:(lia) ltac:(lia)) as Bq.
unfold SHADOW_OFF. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Section seg_exit. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The environment: the registers at +0x188, then the two spilled frame addresses, the flag pointer, and the entry
   values of the saved registers. *)
Definition lx_extra (cx : lcx) : list word :=
  w64 (lc_F cx) :: w64 (lc_F cx) :: w64 (lc_FL cx) ::
  map (fun o : Z * Z => YK11.getr (l_regs cx) (Z_to_bv 5 (snd o))) LF_SAVED.
Definition lx_E (regs2 : bvmap 5 word) (cx : lcx) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 (lx_extra cx)).

Lemma lx_ew_reg : forall regs2 cx n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (lx_E regs2 cx) n = YK11.getr regs2 r.
Proof. intros regs2 cx n r Hn. unfold lx_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma lx_ew_x : forall regs2 cx j, (j < 16)%nat ->
  ew (lx_E regs2 cx) (32 + j) = nth j (lx_extra cx) (Z_to_bv 64 0).
Proof. intros regs2 cx j Hj. unfold lx_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

Section en. Context {fx : YK11.FPState}.

(* The symbolic state at +0x188 holds of the machine state there. *)
Lemma lx_entry : forall (W : world segs) (regs2 : bvmap 5 word) (cx : lcx) mem,
  YK11.getr regs2 8 = w64 (lc_sp0 cx) -> YK11.getr regs2 9 = w64 (lc_sp1 cx) ->
  YK11.getr regs2 18 = w64 (lc_SH cx) ->
  4096 <= lc_F cx -> lc_F cx mod 32 = 0 -> lc_F cx + 256 <= alloc_ceiling -> in_app (lc_F cx) 256 ->
  4096 <= lc_FL cx < alloc_ceiling ->
  (lc_FL cx < lc_F cx \/ lc_F cx + 256 <= lc_FL cx) ->
  (lc_FL cx < lc_SH cx \/ lc_SH cx + 32 <= lc_FL cx) ->
  alloc_ceiling <= lc_sp1 cx -> lc_sp1 cx + 320 <= lc_sp0 cx -> lc_sp0 cx <= 2 ^ 47 ->
  (forall a, lc_F cx <= a < lc_F cx + 8 -> apresent (w_H W) mem a) ->
  (forall i, 0 <= i < 32 -> apresent (w_H W) mem (lc_SH cx + i)) ->
  apresent (w_H W) mem (lc_FL cx) ->
  rdword (aview segs (w_H W) mem) (lc_F cx + 248) = Some (lc_FL cx) ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem) ->
  lc_saved cx (aview segs (w_H W) mem) ->
  st_ok_pi segs VAL (lx_E regs2 cx) lx_ss
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + LO_EXIT)) mem (YK11.seg_rom segs))).
Proof.
intros W regs2 cx mem R8 R9 R18 HF0 HF32 HFc HFapp HFLr HFLF HFLS HSP1c HSP1 HSP47 Hpf Hpsh HpFL HFLw HSPL HSV.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF8 : lc_F cx mod 8 = 0).
{ pose proof (Z.div_mod (lc_F cx) 32 ltac:(lia)) as D32. rewrite HF32, Z.add_0_r in D32.
  replace (lc_F cx) with (lc_F cx / 32 * 4 * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (lc_F cx) 8 ltac:(lia)) as D8. rewrite HF8, Z.add_0_r in D8.
assert (ESH : lc_SH cx = SHADOW_OFF + lc_F cx / 8) by reflexivity.
set (E := lx_E regs2 cx).
assert (U8 : bv_unsigned (ew E 8) = lc_sp0 cx)
  by (unfold E; rewrite (lx_ew_reg regs2 cx 8 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx)
  by (unfold E; rewrite (lx_ew_reg regs2 cx 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = lc_SH cx)
  by (unfold E; rewrite (lx_ew_reg regs2 cx 18 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small;
      rewrite ESH; unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = w64 (lc_F cx)) by exact (lx_ew_x regs2 cx 0 ltac:(lia)).
assert (E33 : ew E 33 = w64 (lc_F cx)) by exact (lx_ew_x regs2 cx 1 ltac:(lia)).
assert (E34 : ew E 34 = w64 (lc_FL cx)) by exact (lx_ew_x regs2 cx 2 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = lc_F cx) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = lc_F cx) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = lc_FL cx) by (rewrite E34; unfold w64; apply unsigned_lit_small; lia).
unfold lc_spills, lf_spill_sm in HSPL.
apply Forall_cons_iff in HSPL as [Hs128 HSPL]. apply Forall_cons_iff in HSPL as [Hs136 _].
cbn [fst snd] in Hs128, Hs136.
unfold lc_saved, LF_SAVED in HSV.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold lx_ss.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks lx_rg_sp lx_rg_hd lx_rg_fp lx_rg_sh
      lx_rg_fl lx_rg_sv base_val];
    rewrite ?U8, ?U9, ?U18, ?U32, ?U33, ?U34.
  + (* the two spill words of the frame *)
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val segs E _ (lc_sp1 cx) 128 8 (SOff 33 0) (lc_F cx));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword segs _ _ _ _ Hs128).
    * apply (chunk_ok_val segs E _ (lc_sp1 cx) 136 8 (SOff 32 0) (lc_F cx));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword segs _ _ _ _ Hs136).
  + (* the frame's first word *)
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
  + (* the frame's last word: the flag pointer *)
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ (lc_F cx) 248 8 (SOff 34 0) (lc_FL cx));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ HFLw).
  + (* the frame's 32 shadow bytes *)
    split; [rewrite ESH; unfold SHADOW_OFF; lia|]. split; [rewrite ESH; unfold SHADOW_OFF; lia|].
    split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
  + (* the flag byte *)
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). replace (lc_FL cx + o) with (lc_FL cx) by lia. exact HpFL.
  + (* the 13 saved words *)
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
  unfold extent_of_region, lx_rg_sp, lx_rg_hd, lx_rg_fp, lx_rg_sh, lx_rg_fl, lx_rg_sv.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U8, U9, U18, U32, U33, U34.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite ESH in *.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat split; first [exact I | lia].
- unfold lx_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32, U33.
  change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

End en.

Lemma lc_exit_ok : lc_exit_stmt B MT XL RLO RHI.
Proof.
unfold lc_exit_stmt.
intros HP cx W' c' HB HST.
destruct HST as (ly' & S' & regs' & mem' & md' & e & k & Ec & HC & HFR & HSP & HFSH & Hk & He & HMT).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (lp_asf B MT XL RLO RHI HP) as ASF.
pose proof (lp_ffl B MT XL RLO RHI HP) as FFL.
pose proof (lp_sink_kept B MT XL RLO RHI HP) as HSINK.
pose proof (lp_meta_kept B MT XL RLO RHI HP) as HMETA.
pose proof (lp_meter_laws B MT XL RLO RHI HP) as MTL.
pose proof (lp_meter_fs_laws B MT XL RLO RHI HP) as MTF.
pose proof (lp_cost B MT XL RLO RHI HP) as HXL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the geometry of the cut *)
destruct (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC)
  as [HARg Hsp0al Hstkg Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & R2 & R8 & R9 & RGP & RTP & Hsp1 & Hsp1al & HSAVED & HF4096 & HFal64
  & HFceil & HFpres & HFLw & HIN).
pose proof HFR as (R18 & R26).
pose proof HMT as (HMLE & HMOK).
destruct Hstkg as (Hceil & Hslo & Hshi & H47).
destruct Hn as (Hn26 & Hnl).
unfold LF_FBYTES in HFceil, HFpres, HFLw. unfold LF_FRAME in Hsp1. unfold LLVMF_STK in Hslo.
(* the slot's pre *)
pose proof HB as HB'. unfold lc_base, tfib_lib_pre_x in HB'.
destruct HB' as (HAFN & Hra & Ha0 & Ha1 & Hpn & Hnl' & Hgarr & Hfrs0 & Hev & Hlive & Hrod & Hsink0 & Hfd0 & Hfss0
  & Hmeta0 & Hmok0).
pose proof HAFN as (HAR0 & Hret0 & Hra4 & Hgp0 & Htp0 & _).
(* the frame, its shadow and its flag byte at the cut *)
assert (EFA : frame_addr ly' LF_CID (l_fpos cx) = lc_F cx) by exact HFaddr.
assert (EFL : flag_addr ly' LF_CID (l_fpos cx) = lc_FL cx)
  by (unfold lc_FL, flag_addr; rewrite HlyF; reflexivity).
assert (ESH : lc_SH cx = SHADOW_OFF + lc_F cx / 8) by reflexivity.
assert (ESHa : shadow_addr (lc_F cx) = lc_SH cx) by reflexivity.
destruct (al_frames _ _ LAWS _ _ _ _ _ LF_CID (l_fpos cx) HARg HFin) as (_ & HFapp & HFb & HFsh).
destruct (FFL ly' S' W' mem' md' LF_CID (l_fpos cx) HARg HFin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
change (fs_frame_bytes LF_CID) with 256 in HFb, HFapp.
change (fs_frame_bytes LF_CID / 8) with 32 in HFsh.
rewrite EFA in HFb, HFsh, HFapp. rewrite EFL in HFLp, HFLo, HFL4096, HFLc.
rewrite ESHa in HFsh.
assert (HF32 : lc_F cx mod 32 = 0).
{ pose proof (Z.div_mod (lc_F cx) 64 ltac:(lia)) as D. rewrite HFal64, Z.add_0_r in D. rewrite D.
  replace (64 * (lc_F cx / 64)) with ((2 * (lc_F cx / 64)) * 32) by lia. apply Z_mod_mult. }
assert (HF8 : lc_F cx mod 8 = 0).
{ pose proof (Z.div_mod (lc_F cx) 32 ltac:(lia)) as D32. rewrite HF32, Z.add_0_r in D32.
  replace (lc_F cx) with (lc_F cx / 32 * 4 * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (lc_F cx) 8 ltac:(lia)) as D8. rewrite HF8, Z.add_0_r in D8.
assert (HFLF : lc_FL cx < lc_F cx \/ lc_F cx + 256 <= lc_FL cx).
{ destruct (Z_lt_le_dec (lc_FL cx) (lc_F cx)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec (lc_FL cx) (lc_F cx + 256)) as [h2|h2]; [|right; exact h2].
  exfalso. exact (proj2 (HFb _ (conj h h2)) HFLo). }
assert (HFLS : lc_FL cx < lc_SH cx \/ lc_SH cx + 32 <= lc_FL cx).
{ destruct (Z_lt_le_dec (lc_FL cx) (lc_SH cx)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec (lc_FL cx) (lc_SH cx + 32)) as [h2|h2]; [|right; exact h2].
  exfalso. pose proof (proj2 (HFsh (lc_FL cx - lc_SH cx) ltac:(lia))) as Hno.
  replace (lc_SH cx + (lc_FL cx - lc_SH cx)) with (lc_FL cx) in Hno by lia. exact (Hno HFLo). }
(* the own frame, its shadow bytes and its flag byte are apart from the entry's blocks and the image *)
assert (Hbl : forall bm, In bm (ablocks B (l_ly cx) (l_S cx)) -> In bm (ablocks B ly' S'))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERM | exact Hb]).
destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low (l_ly cx) (l_S cx) ly' S' W' mem' md' LF_CID (l_fpos cx)
  (lc_F cx) (lc_FL cx) HARg ltac:(rewrite Hfrs, Hfrs0; reflexivity) Hbl HlyF eq_refl eq_refl FFL)
  as (N1 & N2 & N3 & N4).
(* the entry state of the run *)
pose proof (lx_entry (fx := l_fx cx) W' regs' cx mem' R8 R9 R18 HF4096 HF32 HFceil HFapp
  ltac:(lia) HFLF HFLS ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i Hi)))
  HFLp ltac:(replace (lc_F cx + 248) with (lc_F cx + 256 - 8) by lia; exact HFLw)
  HSP HSAVED) as HS.
set (E := lx_E regs' cx) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, lx_E; apply Eimg_env).
assert (U18 : bv_unsigned (ew E 18) = lc_SH cx).
{ unfold E. rewrite (lx_ew_reg regs' cx 18 18%bv eq_refl), R18. unfold w64. apply unsigned_lit_small.
  rewrite ESH. apply lx_sh_u64; lia. }
assert (E32 : ew E 32 = w64 (lc_F cx)) by exact (lx_ew_x regs' cx 0 ltac:(lia)).
assert (E33 : ew E 33 = w64 (lc_F cx)) by exact (lx_ew_x regs' cx 1 ltac:(lia)).
assert (E34 : ew E 34 = w64 (lc_FL cx)) by exact (lx_ew_x regs' cx 2 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = lc_F cx) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = lc_F cx) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = lc_FL cx) by (rewrite E34; unfold w64; apply unsigned_lit_small; lia).
subst c'. unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + LO_EXIT)) mem'
    (YK11.seg_rom segs)) md') Q)
end.
(* +0x188 .. +0x338 in one run, the flag store at +0x23c releasing the frame *)
refine (gx_flag_store_pi (SK := tfib_sink_head) B LAWS ASF FFL TG.G_HARNESS_B W' LX_FUEL E lx_ss lx_ss_end
  lx_st_end (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + LO_EXIT)) mem' (YK11.seg_rom segs))
  LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [] ly' S' md' e LF_CID (l_fpos cx) _
  HEI HS lx_run lx_stop HJ _ _ _ _).
- unfold LF_CID. lia.
- (* the run writes the frame's first word, its 32 shadow bytes and the flag byte *)
  intros a (rg & Hinr & Ha). unfold lx_ss in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi lx_rg_sp lx_rg_hd lx_rg_fp lx_rg_sh lx_rg_fl lx_rg_sv] in Ha;
    rewrite ?U18, ?U32, ?U33, ?U34 in Ha.
  + lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists LF_CID, (l_fpos cx).
    split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes LF_CID) with 256. lia.
  + lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists LF_CID, (l_fpos cx).
    split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA, ESHa.
    change (fs_frame_bytes LF_CID / 8) with 32. lia.
  + right. rewrite EFL. lia.
  + lia.
- (* the flag byte is 0 after the run *)
  intros msr HSr.
  lazymatch goal with |- _ = Some _ =>
    let rr := eval vm_compute in (nth_error (ss_mem lx_ss_end) 4) in
    lazymatch rr with Some ?r4 =>
      pose proof (can_region_nth (segs := segs) _ _ msr 4 r4 HSr eq_refl) as HR4 end end.
  pose proof (can_field_of_region (segs := segs) E (ms_mem msr) 34 (lc_FL cx) _ 0 1 0 1 0 1%N
    (SLit 0) 0 HR4 U34 ltac:(cbn [In]; auto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(cbn; lia)).
  lazymatch type of V with _ = Some (Z_to_bv 8 ?x) => replace x with 0 in V by (vm_compute; reflexivity) end.
  replace (lc_FL cx + 0 + Z.of_nat 0) with (lc_FL cx) in V by lia.
  rewrite EFL. exact V.
- (* the return *)
  intros ms2 mat2 HS2 HJ2 _ HF2 HG2.
  set (md3 := with_vm_backing (m_vm_lazy md') mat2 md') in *. clearbody md3.
  (* what the run kept: every byte outside the own frame, its shadow bytes and its flag byte *)
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ dkg_nf LF_CID (lc_F cx) (lc_FL cx) a ->
    aview segs (w_H W') (ms_mem ms2) a = aview segs (w_H W') mem' a).
  { apply (kept_of_frame (segs := segs) E (ss_mem lx_ss) (w_H W') mem' (ms_mem ms2) _ HF2).
    intros b wlo whi x Hw Hx. unfold lx_ss, windows in Hw.
    cbn [ss_mem map In YP09.r_base YP09.r_wlo YP09.r_whi lx_rg_sp lx_rg_hd lx_rg_fp lx_rg_sh lx_rg_fl lx_rg_sv]
      in Hw.
    unfold dkg_nf. change (fs_frame_bytes LF_CID / 8) with 32. change (fs_frame_bytes LF_CID) with 256.
    destruct Hw as [Hw | [Hw | [Hw | [Hw | [Hw | [Hw | []]]]]]]; injection Hw as <- <- <-;
      cbn [base_val] in Hx; rewrite ?U18, ?U32, ?U33, ?U34 in Hx.
    + lia.
    + left. lia.
    + lia.
    + right; left. rewrite <- ESH. lia.
    + right; right. lia.
    + lia. }
  eapply (paj_ret_at (fx := l_fx cx) (PL := PL_transportb) (PI := PI_transportb) W' E lx_ss_end ms2 md3 _
    HS2 eq_refl ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat3 md3).
  pose proof (ajournal_gx_materialize segs B LAWS transportb_segs_low
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ2) as HJ3.
  fold md4 in HJ3. clearbody md4.
  (* the registers at the ret *)
  assert (R1e : YK11.getr (ms_regs ms2) 1 = YK11.getr (l_regs cx) 1).
  { lx_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10e : YK11.getr (ms_regs ms2) 10 = w64 0).
  { lx_regv HS2. reflexivity. }
  assert (HPr : aregs_preserved (l_regs cx) (ms_regs ms2)).
  { intros rr Hr. unfold acallee_saved in Hr.
    assert (Hr' : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
      rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      lx_regv HS2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    all: first
      [ reflexivity
      | transitivity (YK11.getr regs' 3); [apply lx_ew_reg; reflexivity|];
        rewrite RGP; symmetry; exact Hgp0
      | transitivity (YK11.getr regs' 4); [apply lx_ew_reg; reflexivity|];
        rewrite RTP; symmetry; exact Htp0
      | transitivity (YK11.getr regs' 8); [apply lx_ew_reg; reflexivity|];
        rewrite R8; unfold w64, lc_sp0, spZ; apply Z_to_bv_bv_unsigned ]. }
  assert (Hpc : v_jalr (YK11.getr (ms_regs ms2) 1) 0 = w64 RA_LLVMF).
  { rewrite R1e. unfold YK0s.ret_ok in Hret0. rewrite Hret0. rewrite <- Hra. unfold w64, raZ.
    symmetry. apply Z_to_bv_bv_unsigned. }
  assert (HIO : m_fds md4 = m_fds (l_md cx) /\ m_fs md4 = m_fs (l_md cx)).
  { eapply (lc_journal_io B). exact HJ3. }
  destruct HIO as (Efd & Efs).
  assert (Eab : ablocks B ly' (stack_free_state LF_CID (l_fpos cx) S') = ablocks B ly' S')
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  (* the meter ladder: k receptions cost at most OPS_MAX * lf_rcost MT = transport_llvmf_cost MT n <= XL n *)
  assert (Hrc : 0 <= lf_rcost MT).
  { unfold lf_rcost. pose proof (mo_malloc_nonneg MT MTL 65535 ltac:(lia)). pose proof (mo_free_nonneg MT MTL).
    lia. }
  assert (Hcost : k * lf_rcost MT <= XL (l_n cx)).
  { pose proof (HXL (l_n cx) ltac:(lia)) as HL. rewrite (lf_cost_eq MT (l_n cx)) in HL.
    assert (k * lf_rcost MT <= TC.OPS_MAX * lf_rcost MT) by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  assert (EVL : e <= EV_LIB).
  { assert (ER : RECV_EV = 2) by reflexivity. assert (EO : TC.OPS_MAX = 1024) by reflexivity.
    rewrite ER in He. rewrite EO in Hk. unfold EV_LIB. lia. }
  unfold lc_post.
  exists ly', (stack_free_state LF_CID (l_fpos cx) S'), (ms_regs ms2), (ms_mem ms2), md4, e.
  split; [unfold cfg_at; rewrite Hpc; reflexivity|].
  unfold tfib_lib_post_x.
  split; [apply (lc_fp_token B); exact HJ3|].
  split; [exact EVL|].
  split; [exact HPr|].
  split; [exact R10e|].
  split; [rewrite Eab; exact HPERM|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hfss0|].
  split; [eapply HSINK; [exact HJ3 | exact sink_closed_nil | exact Hsink0]|].
  split; [eapply HMETA; [exact HJ3 | exact Hmeta0]|].
  split.
  { unfold stack_free_state. apply (mo_le_set_fs_r MT MTF).
    exact (mo_le_mono MT MTL _ _ _ _ HMLE Hcost). }
  (* the input's bytes: the run writes none of them *)
  intros i Hi.
  destruct Hpn as [(Hz & _) | (Hn0 & Hinb)]; [lia|].
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' (l_p cx) (l_n cx) HARg (HINg ltac:(lia)))
    as (_ & Hp4096 & Hpce & _).
  pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hrq1 & Hrq2).
  rewrite (KP (l_p cx + i) ltac:(lia) (N1 (l_p cx) (l_n cx) i Hinb ltac:(lia))).
  exact (proj2 HIN i Hi).
Qed.

End seg_exit.

Print Assumptions lc_exit_ok.
