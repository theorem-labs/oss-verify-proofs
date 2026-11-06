(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 467 of its 510 lines of code are new or changed and 1881 lines of the source are left out. *)
(* diginet_session_wake_seg_rel (image B): the release pieces of the image-B walk of diginet_session_wake
   (lib/B/Prog/diginet_session_wake_seg_cut.v): Lemma wakeb_rel : wakeb_rel_stmt and Lemma wakeb_e2 : wakeb_e2_stmt,
   offsets +0x2fc .. +0x3f8 of the listing lib/B/Prog/DgnTransportBList.v (fuzz_transport.asan-ubsan
   0x86d34 .. 0x86e30); image B's twin of lib/A/Prog/diginet_session_wake_seg_rel.v (a class-1 frame of 128 bytes with
   16 shadow bytes, and 12 saved words, in place of image A's class-2 frame of 256 bytes, 32 shadow bytes, 13 saved
   words).

   wakeb_rel, +0x320 .. +0x3f8. +0x320 `lui`/`addiw` a1 = 0x45e0360e and +0x328 `sd a1, 0(s9)`: the frame's first
   word (s9 = F); +0x32c `beqz s2`: s2 = F >= 4096, so the real-stack arm at +0x380 (16 stores of 0 to the frame's
   shadow bytes) is never entered (the engine decides the branch from the atom fact of s2); +0x330 `li a1, -11` and 16
   `sb a1, i(s8)`: the frame's 16 shadow bytes (s8 = SHADOW_OFF + F / 8) := 0xf5; +0x374 `ld a1, 0x78(s2)`: the flag
   pointer FL from the frame's last word (F + 120); +0x378 `sb zero, 0(a1)`: the flag byte, which releases the frame
   (lib/B/Prog/TransportGFrameB.v gx_flag_store_pi); +0x37c `j +0x3c0`; +0x3c0 `addi sp, s0, -0x80`;
   the 12 reloads +0x3c4 .. +0x3f0 of ra, s0, s1, s2 .. s10 from the words the prologue saved below the entry sp (the
   cut file's WAKEB_SAVED); +0x3f4 `addi sp, sp, 0x80`; +0x3f8 `ret`. a0 is not written: it carries the model's
   result r (wakeb_regs_rel) to the return; s11 is never written by the function: it carries the entry value
   (wakeb_regs_core's s11 clause) to the return.

   One run of the plain position-abstract engine (lib/A/Prog/PaSym.v sym_run_pi over image B's listing: no shadow
   token, so the writable shadow region is allowed) covers +0x320 .. +0x3f8 and stops at the `ret`, which
   lib/B/Prog/DgnTransportBPaLib.v paj_ret_at takes. The symbolic state: the registers at +0x320 as atoms 0 .. 31,
   atom 32 the flag pointer FL, atoms 33 .. 44 the entry values of ra, s0, s1, s2 .. s10 (WAKEB_SAVED, in its order);
   regions: the frame's first word (s9, written), its last word (s2, offset 120, read: FL), its 16 shadow bytes (s8,
   written), the flag byte (atom 32, written) and the 12 saved words below s0 = the entry sp (read).

   The post (diginet_session_wake_cg.v transport_wake_post, TransportGCg.v transport_cg_post over G_HARNESS_B): the
   caller's G journal after the flag store, with own and the frame released (stack_free_state); the callee-saved
   registers are the 12 reloads and s11 (the cut's), sp = s0 = the entry sp, gp and tp untouched, a0 = r; the frames
   the caller's (CanKit.v can_sf_frames); the state changed in st_fs only, so the meter bound is the cut's
   (mo_le_set_fs_r). What the call kept: the cut's acall_kept_g, carried over the run by TransportGFrame.v
   dk_kept_step_gw, whose four side conditions on the bytes the run may change (the own frame, its shadow bytes, its
   flag byte: TransportGCg.v dkg_nf) are TransportGFrame.v dkg_nf_sep_gw's. The world relation at Bw': the cut's, kept
   since no byte of G is a byte of dkg_nf (TWorldB.v tw_kept_GB).

   wakeb_e2, +0x2fc .. +0x31c. +0x2fc `addi a1, zero, -8` and eight `sb a1, k(s8)` at k = 8, 9, 0xa, 0xb, 4, 5, 6, 7:
   the frame's shadow bytes 4 .. 11 := 0xf8 (e2, F + 32, out of scope again). One token run of
   lib/B/Prog/TransportGRunB.v paj_run_to_x (G_HARNESS_B, no out window, no shadow entry) from a state with one region
   (the eight shadow bytes, s8 + 4 .. s8 + 12, written: a byte of the own frame's shadow, TransportGFrame.v
   awr_ok_x_cons_own) up to +0x320. The run changes a1 and those eight bytes only, so at its end the release cut's
   state holds at the same registers (wakeb_regs_rel) and the memory the run left: the journal is the run's; the
   frames, blocks, layout and meter are unchanged; acall_kept_g moves by dk_kept_step_gw over dkg_nf (dkg_nf_sep_gw's
   side conditions); the 12 saved words are above alloc_ceiling and the shadow bytes below it (dkg_nf_sep_gw); the
   flag-pointer word at F + 120 is a byte of the frame, apart from the frame's shadow (in_app F 128); the world
   relation is over G, whose bytes lie below kLowMemEnd (tw_kept_GB). The wakeb_rel_at hypothesis concludes. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require TransportGFrameB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
diginet_session_wake_cg diginet_session_wake_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess.
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
(* 1. The symbolic state at +0x320 and the run to the ret              *)
(* ------------------------------------------------------------------ *)

Definition wbrel_rg_hd : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 0 8 [].
Definition wbrel_rg_fp : YP09.region :=
  YP09.mkRegion (Some 18%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 32 0))].
Definition wbrel_rg_sh : YP09.region := YP09.mkRegion (Some 24%nat) 0 16 0 16 [].
Definition wbrel_rg_fl : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition wbrel_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-96) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0))].
(* s2 = s9 = F is at least 4096 (decides the `beqz s2` at +0x32c) and 32-aligned. *)
Definition wbrel_facts : facts := mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 5); (25%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition ss_wbrel : sstate :=
  mkSS WAKEB_REL sr_atoms [wbrel_rg_hd; wbrel_rg_fp; wbrel_rg_sh; wbrel_rg_fl; wbrel_rg_sv] None wbrel_facts.
Definition WBREL_FUEL : N := 96.
Definition wbrel_ss_end : sstate := Eval vm_compute in fst (sym_runN_pi transportb_tpi WBREL_FUEL ss_wbrel).
Definition wbrel_st_end : prun_status tbsym := Eval vm_compute in snd (sym_runN_pi transportb_tpi WBREL_FUEL ss_wbrel).
Lemma wbrel_run : sym_runN_pi transportb_tpi WBREL_FUEL ss_wbrel = (wbrel_ss_end, wbrel_st_end).
Proof. vm_compute. reflexivity. Qed.
Lemma wbrel_stop : can_plain_stop wbrel_st_end.
Proof. exact I. Qed.
(* The run stops at the `ret` at +0x3f8. *)
Lemma wbrel_end_pc : ss_pc wbrel_ss_end = WAKEB_RET.
Proof. reflexivity. Qed.

(* The environment: the registers at +0x320, then FL, then the entry values of the saved registers. *)
Definition wbrel_extra (regs : bvmap 5 word) (FL : Z) : list word :=
  w64 FL :: map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) WAKEB_SAVED.

(* The value of register r in the machine state of HS: its symbolic value, computed. *)
Ltac wbrel_regv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic state at +0x2fc (the e2 cut)                        *)
(* ------------------------------------------------------------------ *)

Definition WBE2_B0 : Z * Z := (0, 0).
(* The frame's shadow bytes 4 .. 11 (s8 + 4 .. s8 + 0xb), written. *)
Definition wbe2_rg_sh : YP09.region := YP09.mkRegion (Some 24%nat) 4 12 4 12 [].
Definition wbe2_facts : facts := mkFacts [(24%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_wbe2 : sstate := mkSS WAKEB_E2 sr_atoms [wbe2_rg_sh] None wbe2_facts.

(* The awr obligation's regions, computed. *)
Ltac wbe2_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.

Section rel. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition wbrel_E (regs2 regs : bvmap 5 word) (FL : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 (wbrel_extra regs FL)).

Lemma wbrel_ew_reg : forall regs2 regs FL n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (wbrel_E regs2 regs FL) n = YK11.getr regs2 r.
Proof. intros regs2 regs FL n r Hn. unfold wbrel_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma wbrel_ew_x : forall regs2 regs FL j, (j < 13)%nat ->
  ew (wbrel_E regs2 regs FL) (32 + j) = nth j (wbrel_extra regs FL) (Z_to_bv 64 0).
Proof. intros regs2 regs FL j Hj. unfold wbrel_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* The symbolic state at +0x320 holds of the machine state there. *)
Lemma wbrel_entry : forall (W : world segs) (regs2 regs : bvmap 5 word) mem (F FL SP : Z),
  YK11.getr regs2 8 = w64 SP -> YK11.getr regs2 18 = w64 F ->
  YK11.getr regs2 24 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs2 25 = w64 F ->
  4096 <= F -> F mod 32 = 0 -> F + 128 <= alloc_ceiling -> in_app F 128 ->
  4096 <= FL < alloc_ceiling -> (FL < F \/ F + 128 <= FL) ->
  (FL < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 16 <= FL) ->
  alloc_ceiling <= SP - 96 -> SP <= 2 ^ 47 ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem a) ->
  (forall i, 0 <= i < 16 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  apresent (w_H W) mem FL ->
  rdword (aview segs (w_H W) mem) (F + 120) = Some FL ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (SP - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) WAKEB_SAVED ->
  st_ok_pi segs VAL (wbrel_E regs2 regs FL) ss_wbrel
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + WAKEB_REL)) mem (YK11.seg_rom segs))).
Proof.
intros W regs2 regs mem F FL SP R8 R18 R24 R25 HF0 HF32 HFc HFapp HFL HFLF HFLS HSP HSP47
  Hpf Hpsh HpFL HFLw Hsaved.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF8 : F mod 8 = 0)
  by (pose proof (Z.div_mod F 32 ltac:(lia)) as D32; replace F with (F / 32 * 4 * 8) by lia; apply Z_mod_mult).
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. rewrite HF8, Z.add_0_r in D8.
set (E := wbrel_E regs2 regs FL).
assert (U8 : bv_unsigned (ew E 8) = SP)
  by (unfold E; rewrite (wbrel_ew_reg regs2 regs FL 8 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (E18 : ew E 18 = w64 F) by (unfold E; rewrite (wbrel_ew_reg regs2 regs FL 18 18%bv eq_refl); exact R18).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF + F / 8)
  by (unfold E; rewrite (wbrel_ew_reg regs2 regs FL 24 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (E25 : ew E 25 = w64 F) by (unfold E; rewrite (wbrel_ew_reg regs2 regs FL 25 25%bv eq_refl); exact R25).
assert (U25 : bv_unsigned (ew E 25) = F) by (rewrite E25; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (wbrel_ew_x regs2 regs FL 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
unfold WAKEB_SAVED in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss_wbrel.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks wbrel_rg_hd wbrel_rg_fp wbrel_rg_sh
      wbrel_rg_fl wbrel_rg_sv base_val];
    rewrite ?U8, ?U18, ?U24, ?U25, ?U32.
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
  unfold extent_of_region, wbrel_rg_hd, wbrel_rg_fp, wbrel_rg_sh, wbrel_rg_fl, wbrel_rg_sv.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U8, U18, U24, U25, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat split; first [exact I | lia].
- unfold wbrel_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18, U25.
  change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The environment of the e2 run: the registers at +0x2fc and the shadow base (atom 32, the run's token). *)
Definition wbe2_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).

Lemma wbe2_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (wbe2_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold wbe2_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma wbe2_env_img : forall regs, img_env VAL A_LIM (wbe2_E regs).
Proof. intros regs. unfold wbe2_E. apply Eimg_env. Qed.

(* The symbolic state at +0x2fc holds of the machine state there. *)
Lemma wbe2_entry : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 24 = w64 SH -> SHADOW_OFF <= SH -> SH + 12 <= 2 ^ 46 ->
  (forall a, SH + 4 <= a < SH + 12 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (wbe2_E regs) ss_wbe2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WAKEB_E2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R24 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_wbe2.
  assert (U24 : bv_unsigned (ew (wbe2_E regs) 24) = SH)
    by (rewrite (wbe2_ew_reg regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold wbe2_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold wbe2_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold wbe2_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U24. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* A register at the end of the e2 run, from the equation Q of its value at +0x2fc. *)
Ltac wbe2_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
  lazymatch type of HS with st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : YK11.getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v);
       cbn [sv_denot]; rewrite (wbe2_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q)
  end end.

(* ------------------------------------------------------------------ *)
(* 3. The release piece                                                 *)
(* ------------------------------------------------------------------ *)

Lemma wakeb_rel : @wakeb_rel_stmt fx rc B MT.
Proof.
unfold wakeb_rel_stmt, wakeb_rel_at.
intros LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 e
  regs2 HFIX HCUR HREGS.
destruct LAWS0 as (_ & _ & _ & _ & _ & _ & _ & LAWS & MTL & MTF & _ & ASF & FFL & HGX & _).
destruct HFIX as (HJ0 & Hret & _ & _ & _ & _ & _ & _ & Hstk & Hsp0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & EF & HF0 & HF64 & HFc & HFapp).
destruct HCUR as ((HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw) & HTW2 & Hgf2).
destruct HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R24 & R25 & R27) & R10).
unfold WAKEB_FBYTES in HFc, HFapp, HFLw.
replace (F + 128 - 8) with (F + 120) in HFLw by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF32 : F mod 32 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((2 * (F / 64)) * 32) by lia. apply Z_mod_mult. }
(* the call's window lies above alloc_ceiling, below 2 ^ 47 *)
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof wakeb_stk_bounds as (_ & _ & _ & HBS & _ & _).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
(* the frame, its shadow bytes and its flag byte at the cut *)
assert (Hin : In (WAKE_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 WAKE_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
assert (EFL : flag_addr ly2 WAKE_CID pos = flag_addr lyc WAKE_CID pos)
  by (unfold flag_addr; rewrite ELF; reflexivity).
rewrite <- EFL in HFLw.
destruct (al_frames _ _ LAWS _ _ _ _ _ WAKE_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
destruct (FFL ly2 S2 W2 mem2 md2 WAKE_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
set (FL := flag_addr ly2 WAKE_CID pos) in *.
change (fs_frame_bytes WAKE_CID / 8) with 16 in HFsh.
change (fs_frame_bytes WAKE_CID) with 128 in HFb.
rewrite EFA in HFb, HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
assert (HFLF : FL < F \/ F + 128 <= FL).
{ destruct (Z_lt_le_dec FL F) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec FL (F + 128)) as [h2|h2]; [|right; exact h2].
  exfalso. exact (proj2 (HFb _ (conj h h2)) HFLo). }
assert (HFLS : FL < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 16 <= FL).
{ destruct (Z_lt_le_dec FL (SHADOW_OFF + F / 8)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec FL (SHADOW_OFF + F / 8 + 16)) as [h2|h2]; [|right; exact h2].
  exfalso. pose proof (proj2 (HFsh (FL - (SHADOW_OFF + F / 8)) ltac:(lia))) as Hno.
  replace (SHADOW_OFF + F / 8 + (FL - (SHADOW_OFF + F / 8))) with FL in Hno by lia.
  exact (Hno HFLo). }
(* the own frame, its shadow bytes and its flag byte are apart from the call's blocks, the image and the call's frames *)
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (TransportGFrame.dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 WAKE_CID pos F FL
  HAR2 Hfrs Hbl ELF EF EFL FFL) as (N1 & N2 & N3 & N4).
pose proof (wbrel_entry W2 regs2 regs mem2 F FL (spZ regs) R8 R18 R24 R25 HF0 HF32 HFc HFapp
  ltac:(lia) HFLF HFLS ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i Hi)))
  HFLp HFLw Hsaved) as HS.
set (E := wbrel_E regs2 regs FL) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, wbrel_E; apply Eimg_env).
assert (U18 : bv_unsigned (ew E 18) = F)
  by (unfold E; rewrite (wbrel_ew_reg regs2 regs _ 18 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF + F / 8).
{ pose proof (Z.div_lt_upper_bound F 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  unfold E; rewrite (wbrel_ew_reg regs2 regs _ 24 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small;
  unfold SHADOW_OFF; lia. }
assert (U25 : bv_unsigned (ew E 25) = F)
  by (unfold E; rewrite (wbrel_ew_reg regs2 regs _ 25 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (wbrel_ew_x regs2 regs _ 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
(* +0x320 .. +0x3f8 in one run, the flag store at +0x378 releasing the frame. *)
refine (TransportGFrameB.gx_flag_store_pi (SK := tfib_sink_head) B LAWS ASF FFL TG.G_HARNESS_B W2 WBREL_FUEL E ss_wbrel
  wbrel_ss_end wbrel_st_end (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + WAKEB_REL)) mem2 (YK11.seg_rom segs))
  STK sp0 FP ly S W0 mem0 md0 own ly2 S2 md2 (k + e) WAKE_CID pos _ HEI HS wbrel_run wbrel_stop HJ1 _ _ _ _).
- unfold WAKE_CID. lia.
- (* the run writes the frame's first word, its shadow and the flag byte *)
  intros a (rg & Hinr & Ha). unfold ss_wbrel in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<- | [<- | [<- | [<- | [<- | []]]]]];
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi wbrel_rg_hd wbrel_rg_fp wbrel_rg_sh wbrel_rg_fl wbrel_rg_sv] in Ha;
    rewrite ?U24, ?U25, ?U32 in Ha.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists WAKE_CID, pos.
    split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes WAKE_CID) with 128. lia.
  + lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists WAKE_CID, pos.
    split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes WAKE_CID / 8) with 16.
    rewrite ESH. lia.
  + right. change (flag_addr ly2 WAKE_CID pos) with FL. lia.
  + lia.
- (* the flag byte is 0 after the run *)
  intros msr HSr.
  lazymatch goal with |- _ = Some _ =>
    let rr := eval vm_compute in (nth_error (ss_mem wbrel_ss_end) 3) in
    lazymatch rr with Some ?r3 =>
      pose proof (can_region_nth (segs := segs) _ _ msr 3 r3 HSr eq_refl) as HR3 end end.
  pose proof (can_field_of_region (segs := segs) E (ms_mem msr) 32 FL _ 0 1 0 1 0 1%N
    (SLit 0) 0 HR3 U32 ltac:(cbn [In]; auto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(cbn; lia)).
  lazymatch type of V with _ = Some (Z_to_bv 8 ?x) => replace x with 0 in V by (vm_compute; reflexivity) end.
  replace (FL + 0 + Z.of_nat 0) with FL in V by lia.
  exact V.
- (* the return *)
  intros ms2 mat2 HS2 HJ2 _ HF2 HG2.
  set (md3 := with_vm_backing (m_vm_lazy md2) mat2 md2) in *. clearbody md3.
  (* what the run kept: every byte outside the own frame, its shadow bytes and its flag byte; presence grows *)
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ dkg_nf WAKE_CID F FL a ->
    aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) mem2 a).
  { apply (kept_of_frame (segs := segs) E (ss_mem ss_wbrel) (w_H W2) mem2 (ms_mem ms2) _ HF2).
    intros b wlo whi x Hw Hx. unfold ss_wbrel, windows in Hw.
    cbn [ss_mem map In YP09.r_base YP09.r_wlo YP09.r_whi wbrel_rg_hd wbrel_rg_fp wbrel_rg_sh wbrel_rg_fl wbrel_rg_sv]
      in Hw.
    unfold dkg_nf. change (fs_frame_bytes WAKE_CID / 8) with 16. change (fs_frame_bytes WAKE_CID) with 128.
    destruct Hw as [Hw | [Hw | [Hw | [Hw | [Hw | []]]]]]; injection Hw as <- <- <-;
      cbn [base_val] in Hx; rewrite ?U18, ?U24, ?U25, ?U32 in Hx.
    + left. lia.
    + lia.
    + right; left. lia.
    + right; right. lia.
    + lia. }
  assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG2 Ha)).
  eapply (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb) W2 E wbrel_ss_end ms2 md3 _
    HS2 eq_refl ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat3 md3).
  pose proof (ajournal_gx_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ2)
    as HJ3.
  fold md4 in HJ3. clearbody md4.
  (* the registers at the ret *)
  assert (R1e : YK11.getr (ms_regs ms2) 1 = YK11.getr regs 1).
  { wbrel_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10e : YK11.getr (ms_regs ms2) 10 = w64 r).
  { wbrel_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    transitivity (YK11.getr regs2 10); [apply wbrel_ew_reg; reflexivity | exact R10]. }
  assert (HP : aregs_preserved regs (ms_regs ms2)).
  { intros r0 Hr. unfold acallee_saved in Hr.
    assert (Hr' : r0 = 2 \/ r0 = 3 \/ r0 = 4 \/ r0 = 8 \/ r0 = 9 \/ r0 = 18 \/ r0 = 19 \/ r0 = 20 \/ r0 = 21 \/
      r0 = 22 \/ r0 = 23 \/ r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      wbrel_regv HS2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    all: first
      [ reflexivity
      | transitivity (YK11.getr regs2 3); [apply wbrel_ew_reg; reflexivity | exact R3]
      | transitivity (YK11.getr regs2 4); [apply wbrel_ew_reg; reflexivity | exact R4]
      | transitivity (YK11.getr regs2 27); [apply wbrel_ew_reg; reflexivity | exact R27]
      | transitivity (YK11.getr regs2 8); [apply wbrel_ew_reg; reflexivity|];
        rewrite R8; unfold w64, spZ; apply Z_to_bv_bv_unsigned ]. }
  assert (Hpc : v_jalr (YK11.getr (ms_regs ms2) 1) 0 = YK11.getr regs 1) by (rewrite R1e; exact Hret).
  assert (Eab' : ablocks B ly2 (stack_free_state WAKE_CID pos S2) = ablocks B ly2 S2)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  unfold transport_wake_post, transport_cg_post.
  exists ly2, (stack_free_state WAKE_CID pos S2), (ms_regs ms2), (ms_mem ms2), md4, e.
  split; [rewrite Hpc; reflexivity|].
  split; [exact He|].
  split; [exact HJ3|].
  split; [exact HP|].
  split; [exact (can_sf_frames WAKE_CID pos S2 (frames Sc) Hfrs)|].
  split; [rewrite Eab'; exact Hperm|].
  split.
  { (* the cut's acall_kept_g, over the run's bytes (the own frame, its shadow, its flag byte) *)
    apply (TransportGFrame.dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2
      (ms_mem ms2) (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw) (dkg_nf WAKE_CID F FL) HARc HK KP GA).
    - intros a Ha Hc. pose proof (N4 a Ha). lia.
    - intros b m i Hb Hi Ha. exfalso. exact (N1 b m i Hb Hi Ha).
    - intros a Ha Hi _ _ _. exfalso. exact (N2 a Ha Hi).
    - intros c p a Hc Hr Ha. exfalso. exact (N3 c p a Hc Hr Ha). }
  split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact Hmo|].
  (* a0 = r, and the world relation at Bw': no byte of G is a byte the run wrote *)
  split; [exact R10e|].
  split; [|exact Hgf2].
  apply (tw_kept_GB (aview segs (w_H W2) mem2)); [exact HTW2|].
  intros b n i Hbn Hi.
  assert (HG : inG TG.G_HARNESS_B (b + i))
    by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
  destruct (HGX _ HG) as [HiG _].
  pose proof (transportb_segs_low _ HiG) as Hl. unfold kLowMemEnd in Hl.
  apply KP; [lia | intros Hn; exact (N2 _ Hn HiG)].
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The e2 piece                                                      *)
(* ------------------------------------------------------------------ *)

Lemma wakeb_e2 : @wakeb_e2_stmt fx rc B MT.
Proof.
unfold wakeb_e2_stmt, wakeb_e2_at.
intros REL LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ly2 S2 W2 mem2
  md2 e regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (_ & _ & _ & _ & _ & _ & _ & LAWS & MTL & MTF & _ & ASF & FFL & HGX & _).
pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw) & HTW2 & Hgf2).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R24 & R25 & R27) & R10).
unfold WAKEB_FBYTES in HFc, HFapp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the call's window lies above alloc_ceiling, below 2 ^ 47 *)
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof wakeb_stk_bounds as (_ & _ & _ & HBS & _ & _).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
(* the frame and its shadow bytes at the cut *)
assert (Hin : In (WAKE_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 WAKE_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ WAKE_CID pos HAR2 Hin) as (_ & _ & _ & HFsh).
change (fs_frame_bytes WAKE_CID / 8) with 16 in HFsh.
rewrite EFA in HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
set (FL := flag_addr lyc WAKE_CID pos).
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (TransportGFrame.dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 WAKE_CID pos F FL
  HAR2 Hfrs Hbl ELF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8.
assert (HFhi : F + 128 <= 2 ^ 47) by lia.
assert (HF8hi : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
(* +0x2fc .. +0x31c in one run, the eight shadow stores. *)
pose proof (wbe2_entry W2 regs2 mem2 (SHADOW_OFF + F / 8) R24 ltac:(lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; replace a with (SHADOW_OFF + F / 8 + (a - (SHADOW_OFF + F / 8))) by lia;
        exact (proj1 (HFsh (a - (SHADOW_OFF + F / 8)) ltac:(lia))))) as HS.
assert (HEI : img_env VAL A_LIM (wbe2_E regs2)) by apply wbe2_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (wbe2_E regs2) (mrestrict (w_H W2) mem2)) by constructor.
assert (U24 : bv_unsigned (ew (wbe2_E regs2) 24) = SHADOW_OFF + F / 8)
  by (rewrite (wbe2_ew_reg regs2 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ1 SHOK WBE2_B0 WAKEB_REL.
{ wbe2_awr_rs.
  eapply (TransportGFrame.awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ WAKE_CID pos);
    [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U24 in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes WAKE_CID / 8) with 16.
  rewrite EFA, ESH. lia. }
match goal with H : img_env _ _ _ |- _ => lazymatch H with HEI => fail | _ => clear H end end.
(* the run wrote the frame's shadow bytes 4 .. 11 only; presence grows *)
assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 12) ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 4 <= x < SHADOW_OFF + F / 8 + 12) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hw Hx.
  lazymatch type of Hw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hw end.
  cbn [In] in Hw.
  repeat (destruct Hw as [Hw | Hw]; [injection Hw as <- <- <-; cbn [base_val] in Hx; rewrite ?U24 in Hx; lia |]).
  destruct Hw. }
assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ dkg_nf WAKE_CID F FL a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply KD; [exact Ha|]. intros Hx. apply Hn. unfold dkg_nf.
  change (fs_frame_bytes WAKE_CID / 8) with 16. right; left. lia. }
assert (KS : forall a, alloc_ceiling <= a < 2 ^ 64 ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply KD; [lia|]. intros Hx.
  assert (Hn : dkg_nf WAKE_CID F FL a)
    by (unfold dkg_nf; change (fs_frame_bytes WAKE_CID / 8) with 16; right; left; lia).
  pose proof (N4 a Hn). lia. }
(* the registers at +0x320: the run wrote a1 only *)
wbe2_kreg HS regs2 (2%bv : bv 5) 2%nat R2 Y2. wbe2_kreg HS regs2 (3%bv : bv 5) 3%nat R3 Y3.
wbe2_kreg HS regs2 (4%bv : bv 5) 4%nat R4 Y4. wbe2_kreg HS regs2 (8%bv : bv 5) 8%nat R8 Y8.
wbe2_kreg HS regs2 (9%bv : bv 5) 9%nat R9 Y9. wbe2_kreg HS regs2 (18%bv : bv 5) 18%nat R18 Y18.
wbe2_kreg HS regs2 (24%bv : bv 5) 24%nat R24 Y24. wbe2_kreg HS regs2 (25%bv : bv 5) 25%nat R25 Y25.
wbe2_kreg HS regs2 (27%bv : bv 5) 27%nat R27 Y27.
wbe2_kreg HS regs2 (10%bv : bv 5) 10%nat R10 Y10.
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WAKEB_REL)) mm rom) mdx) Q) end.
apply (REL LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F ly2 S2 W2
  (ms_mem ms) _ e (ms_regs ms) HFIX).
- (* the release cut's state at the memory the run left *)
  refine (conj (conj HJ1 (conj He (conj Hfrs (conj Hperm (conj ELF (conj Hmo (conj _ (conj _ _)))))))) (conj _ Hgf2)).
  + (* the cut's acall_kept_g, over the run's bytes (the own frame's shadow) *)
    apply (TransportGFrame.dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2
      (ms_mem ms) (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw) (dkg_nf WAKE_CID F FL) HARc HK KP GA).
    * intros a Ha Hc. pose proof (N4 a Ha). lia.
    * intros b m i Hb Hi Ha. exfalso. exact (N1 b m i Hb Hi Ha).
    * intros a Ha Hi _ _ _. exfalso. exact (N2 a Ha Hi).
    * intros c p a Hc Hr Ha. exfalso. exact (N3 c p a Hc Hr Ha).
  + (* the 12 saved words lie above alloc_ceiling *)
    assert (HSB : Forall (fun o : Z * Z => 8 <= fst o <= 96) WAKEB_SAVED)
      by (unfold WAKEB_SAVED; repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia).
    apply Forall_forall. intros o Hoin. cbv beta.
    pose proof (proj1 (Forall_forall _ _) Hsaved o Hoin) as Ho.
    pose proof (proj1 (Forall_forall _ _) HSB o Hoin) as Hb.
    cbn beta in Ho, Hb.
    rewrite (rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms)) (spZ regs - fst o));
      [exact Ho|].
    intros k0 Hk0. apply KS. lia.
  + (* the frame's last word is a byte of the frame, apart from the frame's shadow *)
    rewrite (rdword_ext (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem ms)) (F + WAKEB_FBYTES - 8));
      [exact HFLw|].
    intros k0 Hk0. unfold WAKEB_FBYTES. apply KD; [lia|].
    destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
  + (* the world relation at Bw': no byte of G is a byte the run wrote *)
    apply (tw_kept_GB (aview segs (w_H W2) mem2)); [exact HTW2|].
    intros b n i Hbn Hi.
    assert (HG0 : inG TG.G_HARNESS_B (b + i))
      by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
    destruct (HGX _ HG0) as [HiG _].
    pose proof (transportb_segs_low _ HiG) as Hl. unfold kLowMemEnd in Hl.
    apply KP; [lia | intros Hn; exact (N2 _ Hn HiG)].
- (* the registers *)
  exact (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 (conj Y24 (conj Y25 Y27)))))))) Y10).
Qed.

End rel.

Print Assumptions wakeb_rel.
Print Assumptions wakeb_e2.
