(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 369 of its 416 lines of code are new or changed and 1877 lines of the source are left out. *)
(* SendctlRel: Lemma sendctl_rel : sendctl_rel_stmt (lib/A/Prog/SendctlCut.v), the release piece of send_control,
   offsets +0x24c .. +0x3a4 of the listing lib/A/Prog/DgnTransportList.v (fuzz_transport.asan 0x86fa8 .. 0x87100).

   What the code does. +0x24c `li a0, -8` and ten `sb a0, i(s8)`: the frame's shadow bytes 16, 17, 8 .. 11 and
   4 .. 7 (s8 = SHADOW_OFF + F / 8) := 0xf8 (f and h out of scope); +0x278 `lui`/`addiw` a0 = 0x45e0360e and +0x280
   `sd a0, 0(s9)`: the frame's first word (s9 = F); +0x284 `beqz s2`: s2 = F >= 4096, so the real-stack arm at +0x318
   is never entered (the engine decides the branch from the atom fact of s2); +0x288 `li a0, -11` and 32
   `sb a0, i(s8)`: the frame's 32 shadow bytes := 0xf5; +0x30c `ld a0, 248(s2)`: the flag pointer FL from the frame's
   last word; +0x310 `sb zero, 0(a0)`: the flag byte, which releases the frame (lib/A/Prog/TransportGFrame.v
   gx_flag_store_pi); +0x314 `j +0x368`; +0x368 `mv a0, s5`: the result; +0x36c `addi sp, s0, -128`; the 12 reloads
   +0x370 .. +0x39c of ra, s0, s1, s2 .. s10 from the words the prologue saved below the entry sp
   (SendctlCut.v SENDCTL_SAVED); +0x3a0 `addi sp, sp, 128`; +0x3a4 `ret`.

   One run of the plain position-abstract engine (lib/A/Prog/PaSym.v sym_run_pi: no shadow token, so the writable
   shadow region is allowed) covers +0x24c .. +0x3a4 and stops at the `ret`, which lib/A/Prog/DgnTransportPaLib.v
   paj_ret_at takes. The symbolic state: the registers at +0x24c as atoms 0 .. 31, atom 32 the flag pointer FL, atoms
   33 .. 44 the entry values of ra, s0, s1, s2 .. s10 (SENDCTL_SAVED, in its order); regions: the frame's first word
   (s9, written), its last word (s2, offset 248, read: FL), its 32 shadow bytes (s8, written), the flag byte (atom 32,
   written) and the 12 saved words below s0 = the entry sp (read).

   The post (send_control_cg.v transport_sendctl_post, TransportGCg.v transport_cg_post_out over G_HARNESS with the
   out cells sendctl_outs kp klp): the caller's G journal after the flag store, with own and the frame released
   (stack_free_state); the callee-saved registers are the 12 reloads, sp = s0 = the entry sp, gp, tp and s11
   untouched; a0 = s5 = r; the frames the caller's (CanKit.v can_sf_frames); the state changed in st_fs only, so the
   meter bound is the cut's (mo_le_set_fs_r). What the call kept: the cut's acall_kept_g, already read at the memory
   with the out cells put back (gover (sendctl_outs kp klp) mem2 memc), carried over the run by TransportGFrame.v
   dk_kept_step_gw at the two gover memories (scr_gover_view, scr_gover_pres below: an out byte reads memc on both
   sides, any other byte reduces to the run's own kept fact), whose four side conditions on the bytes the run may
   change (the own frame, its shadow bytes, its flag byte: TransportGCg.v dkg_nf) are TransportGFrame.v
   dkg_nf_sep_gw's. The world relation at Bw': the cut's, kept since no byte of G is a byte of dkg_nf (TWorldA.v
   tw_kept_GA). The out cells (sendctl_outcells): each byte of [kp, kp + 60) and [klp, klp + 8) is a write right of
   the caller's journal at entry (transport_twr_ok_g, not a byte of G), so an awr_byte: in the caller's stack window
   (at or above alloc_ceiling, the own frame below it), in a block of the call (dkg_nf_sep_gw's first clause) or in a
   frame the caller owns (a frame of frames Sc: its third clause); so the run keeps it, and garr8 carries by val_mem.
   The cells' lengths: K and KL are the caller's (60 and 8 bytes), f is [] or the model's 60 bytes
   (SendctlCut.v sendctl_model, sendctl_len_fr), put 8 has 8 bytes. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_build_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import CanKit TransportGFrame SendctlCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TImg TSess0 TSess.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x24c and the run to the ret              *)
(* ------------------------------------------------------------------ *)

(* The `ret` of send_control. *)
Definition SENDCTL_RET : Z := AF_send_control + 0x3a4.

Definition scr_rg_hd : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 0 8 [].
Definition scr_rg_fp : YP09.region :=
  YP09.mkRegion (Some 18%nat) 248 256 0 0 [YP09.mkChunk 248 (CVal 8 (SOff 32 0))].
Definition scr_rg_sh : YP09.region := YP09.mkRegion (Some 24%nat) 0 32 0 32 [].
Definition scr_rg_fl : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition scr_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-96) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0))].
(* s2 = s9 = F is at least 4096 (decides the `beqz s2` at +0x284) and 32-aligned. *)
Definition scr_facts : facts := mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 5); (25%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition ss_scr : sstate :=
  mkSS SENDCTL_REL sr_atoms [scr_rg_hd; scr_rg_fp; scr_rg_sh; scr_rg_fl; scr_rg_sv] None scr_facts.
Definition SCR_FUEL : N := 96.
Definition scr_ss_end : sstate := Eval vm_compute in fst (sym_runN_pi transport_tpi SCR_FUEL ss_scr).
Definition scr_st_end : prun_status tsym := Eval vm_compute in snd (sym_runN_pi transport_tpi SCR_FUEL ss_scr).
Lemma scr_run : sym_runN_pi transport_tpi SCR_FUEL ss_scr = (scr_ss_end, scr_st_end).
Proof. vm_compute. reflexivity. Qed.
Lemma scr_stop : can_plain_stop scr_st_end.
Proof. exact I. Qed.
Lemma scr_end_pc : ss_pc scr_ss_end = SENDCTL_RET.
Proof. reflexivity. Qed.

(* The environment: the registers at +0x24c, then FL, then the entry values of the saved registers. *)
Definition scr_extra (regs : bvmap 5 word) (FL : Z) : list word :=
  w64 FL :: map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) SENDCTL_SAVED.

(* The value of register r in the machine state of HS: its symbolic value, computed. *)
Ltac scr_regv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

Section rel. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition scr_E (regs2 regs : bvmap 5 word) (FL : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs2 (scr_extra regs FL)).

Lemma scr_ew_reg : forall regs2 regs FL n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (scr_E regs2 regs FL) n = YK11.getr regs2 r.
Proof. intros regs2 regs FL n r Hn. unfold scr_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma scr_ew_x : forall regs2 regs FL j, (j < 13)%nat ->
  ew (scr_E regs2 regs FL) (32 + j) = nth j (scr_extra regs FL) (Z_to_bv 64 0).
Proof. intros regs2 regs FL j Hj. unfold scr_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* The symbolic state at +0x24c holds of the machine state there. *)
Lemma scr_entry : forall (W : world segs) (regs2 regs : bvmap 5 word) mem (F FL SP : Z),
  YK11.getr regs2 8 = w64 SP -> YK11.getr regs2 18 = w64 F ->
  YK11.getr regs2 24 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs2 25 = w64 F ->
  4096 <= F -> F mod 32 = 0 -> F + 256 <= alloc_ceiling -> in_app F 256 ->
  4096 <= FL < alloc_ceiling -> (FL < F \/ F + 256 <= FL) ->
  (FL < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 32 <= FL) ->
  alloc_ceiling <= SP - 96 -> SP <= 2 ^ 47 ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem a) ->
  (forall i, 0 <= i < 32 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  apresent (w_H W) mem FL ->
  rdword (aview segs (w_H W) mem) (F + 248) = Some FL ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (SP - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SENDCTL_SAVED ->
  st_ok_pi segs VAL (scr_E regs2 regs FL) ss_scr
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SENDCTL_REL)) mem (YK11.seg_rom segs))).
Proof.
intros W regs2 regs mem F FL SP R8 R18 R24 R25 HF0 HF32 HFc HFapp HFL HFLF HFLS HSP HSP47
  Hpf Hpsh HpFL HFLw Hsaved.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF8 : F mod 8 = 0)
  by (pose proof (Z.div_mod F 32 ltac:(lia)) as D32; replace F with (F / 32 * 4 * 8) by lia; apply Z_mod_mult).
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. rewrite HF8, Z.add_0_r in D8.
set (E := scr_E regs2 regs FL).
assert (U8 : bv_unsigned (ew E 8) = SP)
  by (unfold E; rewrite (scr_ew_reg regs2 regs FL 8 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (E18 : ew E 18 = w64 F) by (unfold E; rewrite (scr_ew_reg regs2 regs FL 18 18%bv eq_refl); exact R18).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF + F / 8)
  by (unfold E; rewrite (scr_ew_reg regs2 regs FL 24 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (E25 : ew E 25 = w64 F) by (unfold E; rewrite (scr_ew_reg regs2 regs FL 25 25%bv eq_refl); exact R25).
assert (U25 : bv_unsigned (ew E 25) = F) by (rewrite E25; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (scr_ew_x regs2 regs FL 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
unfold SENDCTL_SAVED in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss_scr.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks scr_rg_hd scr_rg_fp scr_rg_sh
      scr_rg_fl scr_rg_sv base_val];
    rewrite ?U8, ?U18, ?U24, ?U25, ?U32.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ F 248 8 (SOff 32 0) FL);
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
  unfold extent_of_region, scr_rg_hd, scr_rg_fp, scr_rg_sh, scr_rg_fl, scr_rg_sv.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U8, U18, U24, U25, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat split; first [exact I | lia].
- unfold scr_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18, U25.
  change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The kept fact and the out cells over the run                      *)
(* ------------------------------------------------------------------ *)

(* At the memory with the out cells put back, a byte the run keeps is kept: an out byte reads memc on both sides. *)
Lemma scr_gover_view : forall (outs : list (Z * Z)) (H : word -> bool) (m m' mc : word -> option byte) a,
  (inGb outs (bv_unsigned (Z_to_bv 64 a)) = false -> aview segs H m' a = aview segs H m a) ->
  aview segs H (gover outs m' mc) a = aview segs H (gover outs m mc) a.
Proof.
intros outs H m m' mc a Hk. destruct (inGb outs (bv_unsigned (Z_to_bv 64 a))) eqn:Eb.
- apply (aview_eq_of segs). unfold mrestrict, gover. rewrite Eb. reflexivity.
- rewrite (aview_eq_of segs H m' (gover outs m' mc) a) by (unfold mrestrict, gover; rewrite Eb; reflexivity).
  rewrite (aview_eq_of segs H m (gover outs m mc) a) by (unfold mrestrict, gover; rewrite Eb; reflexivity).
  exact (Hk eq_refl).
Qed.

(* Presence that grows over the run grows at the memory with the out cells put back. *)
Lemma scr_gover_pres : forall (outs : list (Z * Z)) (H : word -> bool) (m m' mc : word -> option byte) a,
  (apresent H m a -> apresent H m' a) ->
  apresent H (gover outs m mc) a -> apresent H (gover outs m' mc) a.
Proof.
intros outs H m m' mc a Hg Hp. unfold apresent, gover in Hp |- *. cbv beta in Hp |- *.
destruct Hp as (Hh & b & Hb).
destruct (inGb outs (bv_unsigned (Z_to_bv 64 a))) eqn:Eb.
- split; [exact Hh | exists b; exact Hb].
- destruct (Hg (conj Hh (ex_intro _ b Hb))) as (Hh' & b' & Hb').
  split; [exact Hh' | exists b'; exact Hb'].
Qed.

(* The bytes of a cell the run keeps keep their values. *)
Lemma scr_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) q (l : list Z),
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H m' (q + j) = aview segs H m (q + j)) ->
  garr8 segs (mrestrict H m) q l -> garr8 segs (mrestrict H m') q l.
Proof.
intros H m m' q l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
apply (val_mem_kept segs H H m m' (q + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros i Hi. change (Z.of_nat 1) with 1 in Hi. replace (q + Z.of_nat j + i) with (q + Z.of_nat j) by lia.
apply Hk. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma sendctl_rel : @sendctl_rel_stmt fx rc B MT.
Proof.
unfold sendctl_rel_stmt, sendctl_rel_at.
intros LAWS0 _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
destruct LAWS0 as (_ & _ & _ & _ & _ & LAWS & MTL & MTF & _ & ASF & FFL & HGX & _).
destruct HFIX as (HJ0 & Hret & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp0 & _ & _ & HKP & HTW0 & _ & HM &
  _ & _ & _ & _ & _ & _ & EF & HF0 & HF64 & HFc & HFapp).
destruct HCUR as ((HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw & _) & HTW2 & Hgf2 & HOUT).
destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R24 & R25 & R27).
unfold SENDCTL_FBYTES in HFc, HFapp, HFLw.
replace (F + 256 - 8) with (F + 248) in HFLw by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF32 : F mod 32 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((2 * (F / 64)) * 32) by lia. apply Z_mod_mult. }
(* the f the model built: [] or 60 bytes *)
assert (LF : f = [] \/ length f = 60%nat).
{ destruct (sendctl_model _ _ _ _ _ _ _ _ HM) as [(_ & _ & _ & Hf) | (_ & _ & Hf & _)]; [left; exact Hf|].
  right. rewrite Hf. apply sendctl_len_fr. exact (tw_len _ _ _ HTW0). }
clear HM.
(* the caller's stack window lies above alloc_ceiling, below 2 ^ 47; the caller's own frames are frames of Sc *)
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & HfrsC & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4240 <= SENDCTL_STK).
{ unfold SENDCTL_STK, SENDCTL_FRAME, SENDCTL_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm; assert (Ha : a = 4096) by reflexivity end.
  lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
(* the frame, its shadow bytes and its flag byte at the cut *)
assert (Hin : In (SENDCTL_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 SENDCTL_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
assert (EFL : flag_addr ly2 SENDCTL_CID pos = flag_addr lyc SENDCTL_CID pos)
  by (unfold flag_addr; rewrite ELF; reflexivity).
rewrite <- EFL in HFLw.
destruct (al_frames _ _ LAWS _ _ _ _ _ SENDCTL_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
destruct (FFL ly2 S2 W2 mem2 md2 SENDCTL_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
set (FL := flag_addr ly2 SENDCTL_CID pos) in *.
change (fs_frame_bytes SENDCTL_CID / 8) with 32 in HFsh.
change (fs_frame_bytes SENDCTL_CID) with 256 in HFb.
rewrite EFA in HFb, HFsh.
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
rewrite ESH in HFsh.
assert (HFLF : FL < F \/ F + 256 <= FL).
{ destruct (Z_lt_le_dec FL F) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec FL (F + 256)) as [h2|h2]; [|right; exact h2].
  exfalso. exact (proj2 (HFb _ (conj h h2)) HFLo). }
assert (HFLS : FL < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 32 <= FL).
{ destruct (Z_lt_le_dec FL (SHADOW_OFF + F / 8)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec FL (SHADOW_OFF + F / 8 + 32)) as [h2|h2]; [|right; exact h2].
  exfalso. pose proof (proj2 (HFsh (FL - (SHADOW_OFF + F / 8)) ltac:(lia))) as Hno.
  replace (SHADOW_OFF + F / 8 + (FL - (SHADOW_OFF + F / 8))) with FL in Hno by lia.
  exact (Hno HFLo). }
(* the own frame, its shadow bytes and its flag byte are apart from the call's blocks, the image and the call's frames *)
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 SENDCTL_CID pos F FL HAR2 Hfrs Hbl
  ELF EF EFL FFL) as (N1 & N2 & N3 & N4).
(* and apart from every byte the caller's journal lets a callee write *)
assert (NFW : forall a, awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  ~ dkg_nf SENDCTL_CID F FL a).
{ intros a Hw Hn.
  destruct Hw as [Hw | [(_ & b & m & Hb & Hr) | [(b & m & Hb & _ & Hr) | (c0 & p0 & Hc & Hr)]]].
  - pose proof (N4 a Hn). lia.
  - apply (N1 b m (a - b) Hb ltac:(lia)). replace (b + (a - b)) with a by lia. exact Hn.
  - apply (N1 b m (a - b) Hb ltac:(lia)). replace (b + (a - b)) with a by lia. exact Hn.
  - assert (Hc' : In (c0, p0) (frames Sc)) by (rewrite HfrsC; apply in_or_app; left; exact Hc).
    exact (N3 c0 p0 a Hc' Hr Hn). }
pose proof (scr_entry W2 regs2 regs mem2 F FL (spZ regs) R8 R18 R24 R25 HF0 HF32 HFc HFapp
  ltac:(lia) HFLF HFLS ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i Hi)))
  HFLp HFLw Hsaved) as HS.
set (E := scr_E regs2 regs FL) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, scr_E; apply Eimg_env).
assert (U18 : bv_unsigned (ew E 18) = F)
  by (unfold E; rewrite (scr_ew_reg regs2 regs _ 18 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF + F / 8).
{ pose proof (Z.div_lt_upper_bound F 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  unfold E; rewrite (scr_ew_reg regs2 regs _ 24 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small;
  unfold SHADOW_OFF; lia. }
assert (U25 : bv_unsigned (ew E 25) = F)
  by (unfold E; rewrite (scr_ew_reg regs2 regs _ 25 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (scr_ew_x regs2 regs _ 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
(* +0x24c .. +0x3a4 in one run, the flag store at +0x310 releasing the frame. *)
refine (gx_flag_store_pi (SK := tfib_sink_head) B LAWS ASF FFL TG.G_HARNESS W2 SCR_FUEL E ss_scr scr_ss_end
  scr_st_end (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SENDCTL_REL)) mem2 (YK11.seg_rom segs))
  STK sp0 FP ly S W0 mem0 md0 own ly2 S2 md2 (k + e) SENDCTL_CID pos _ HEI HS scr_run scr_stop HJ1 _ _ _ _).
- unfold SENDCTL_CID. lia.
- (* the run writes the frame's first word, its shadow and the flag byte *)
  intros a (rg & Hinr & Ha). unfold ss_scr in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<- | [<- | [<- | [<- | [<- | []]]]]];
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi scr_rg_hd scr_rg_fp scr_rg_sh scr_rg_fl scr_rg_sv] in Ha;
    rewrite ?U24, ?U25, ?U32 in Ha.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists SENDCTL_CID, pos.
    split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes SENDCTL_CID) with 256. lia.
  + lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists SENDCTL_CID, pos.
    split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes SENDCTL_CID / 8) with 32.
    rewrite ESH. lia.
  + right. change (flag_addr ly2 SENDCTL_CID pos) with FL. lia.
  + lia.
- (* the flag byte is 0 after the run *)
  intros msr HSr.
  lazymatch goal with |- _ = Some _ =>
    let rr := eval vm_compute in (nth_error (ss_mem scr_ss_end) 3) in
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
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ dkg_nf SENDCTL_CID F FL a ->
    aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) mem2 a).
  { apply (kept_of_frame (segs := segs) E (ss_mem ss_scr) (w_H W2) mem2 (ms_mem ms2) _ HF2).
    intros b wlo whi x Hw Hx. unfold ss_scr, windows in Hw.
    cbn [ss_mem map In YP09.r_base YP09.r_wlo YP09.r_whi scr_rg_hd scr_rg_fp scr_rg_sh scr_rg_fl scr_rg_sv]
      in Hw.
    unfold dkg_nf. change (fs_frame_bytes SENDCTL_CID / 8) with 32. change (fs_frame_bytes SENDCTL_CID) with 256.
    destruct Hw as [Hw | [Hw | [Hw | [Hw | [Hw | []]]]]]; injection Hw as <- <- <-;
      cbn [base_val] in Hx; rewrite ?U18, ?U24, ?U25, ?U32 in Hx.
    + left. lia.
    + lia.
    + right; left. lia.
    + right; right. lia.
    + lia. }
  assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG2 Ha)).
  eapply (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport) W2 E scr_ss_end ms2 md3 _
    HS2 eq_refl ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat3 md3).
  pose proof (ajournal_gx_materialize segs B LAWS transport_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ2)
    as HJ3.
  fold md4 in HJ3. clearbody md4.
  (* the registers at the ret *)
  assert (R1e : YK11.getr (ms_regs ms2) 1 = YK11.getr regs 1).
  { scr_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10e : YK11.getr (ms_regs ms2) 10 = w64 r).
  { scr_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    transitivity (YK11.getr regs2 21); [apply scr_ew_reg; reflexivity | exact R21]. }
  assert (HP : aregs_preserved regs (ms_regs ms2)).
  { intros rr Hr. unfold acallee_saved in Hr.
    assert (Hr' : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
      rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      scr_regv HS2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    all: first
      [ reflexivity
      | transitivity (YK11.getr regs2 3); [apply scr_ew_reg; reflexivity | exact R3]
      | transitivity (YK11.getr regs2 4); [apply scr_ew_reg; reflexivity | exact R4]
      | transitivity (YK11.getr regs2 27); [apply scr_ew_reg; reflexivity | exact R27]
      | transitivity (YK11.getr regs2 8); [apply scr_ew_reg; reflexivity|];
        rewrite R8; unfold w64, spZ; apply Z_to_bv_bv_unsigned ]. }
  assert (Hpc : v_jalr (YK11.getr (ms_regs ms2) 1) 0 = YK11.getr regs 1) by (rewrite R1e; exact Hret).
  assert (Eab' : ablocks B ly2 (stack_free_state SENDCTL_CID pos S2) = ablocks B ly2 S2)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  unfold transport_sendctl_post, transport_cg_post_out.
  exists ly2, (stack_free_state SENDCTL_CID pos S2), (ms_regs ms2), (ms_mem ms2), md4, e.
  split; [rewrite Hpc; reflexivity|].
  split; [exact He|].
  split; [exact HJ3|].
  split; [exact HP|].
  split; [exact (can_sf_frames SENDCTL_CID pos S2 (frames Sc) Hfrs)|].
  split; [rewrite Eab'; exact Hperm|].
  split.
  { (* the cut's acall_kept_g at the memory with the out cells put back, over the run's bytes (the own frame, its
       shadow, its flag byte) *)
    apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W2
      (gover (sendctl_outs kp klp) mem2 memc) (gover (sendctl_outs kp klp) (ms_mem ms2) memc)
      (spZ regs - SENDCTL_STK) (spZ regs) (sendctl_wr kp klp) (dkg_nf SENDCTL_CID F FL) HARc HK).
    - intros a Ha Hn. apply scr_gover_view. intros _. exact (KP a Ha Hn).
    - intros a Hp. exact (scr_gover_pres (sendctl_outs kp klp) (w_H W2) mem2 (ms_mem ms2) memc a (GA a) Hp).
    - intros a Ha Hc. pose proof (N4 a Ha). lia.
    - intros b m i Hb Hi Ha. exfalso. exact (N1 b m i Hb Hi Ha).
    - intros a Ha Hi _ _ _. exfalso. exact (N2 a Ha Hi).
    - intros c p a Hc Hr Ha. exfalso. exact (N3 c p a Hc Hr Ha). }
  split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact Hmo|].
  split; [exact R10e|].
  (* the world relation at Bw': no byte of G is a byte the run wrote *)
  split.
  { apply (tw_kept_GA (aview segs (w_H W2) mem2)); [exact HTW2|].
    intros b n i Hbn Hi.
    assert (HG : inG TG.G_HARNESS (b + i))
      by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
    destruct (HGX _ HG) as [HiG _].
    pose proof (transport_segs_low _ HiG) as Hl. unfold kLowMemEnd in Hl.
    apply KP; [lia | intros Hn; exact (N2 _ Hn HiG)]. }
  split; [exact Hgf2|].
  (* the out cells: the caller's write rights, kept by the run *)
  destruct HOUT as [Hk0 | (GK & GKL)]; [left; exact Hk0|].
  destruct HKP as [Hk0 | (_ & _ & TWK & RDK & _ & NGK & LK & _ & _ & TWKL & RDKL & _ & NGKL & LKL & _ & _)];
    [left; exact Hk0|].
  right.
  destruct RDK as (_ & _ & _ & _ & Hkp0 & Hkpn). destruct RDKL as (_ & _ & _ & _ & Hklp0 & Hklpn).
  unfold SENDCTL_F in *.
  assert (LZK : length (TW.zs (match f with [] => K | _ => f end)) = 60%nat).
  { unfold TW.zs. rewrite length_map. clear - LK LF.
    destruct f as [|b0 f0]; [exact LK|]. destruct LF as [LF|LF]; [discriminate LF | exact LF]. }
  assert (LZKL : length (TW.zs (match f with [] => KL | _ => TW.put 8 (Z.of_nat (length f)) end)) = 8%nat).
  { unfold TW.zs. rewrite length_map. clear - LKL.
    destruct f as [|b0 f0]; [exact LKL | apply TWL.length_put]. }
  split.
  + apply (scr_garr8_kept (w_H W2) mem2 (ms_mem ms2) kp _); [|exact GK].
    intros j Hj. rewrite LZK in Hj. change (Z.of_nat 60) with 60 in Hj.
    apply KP; [lia|].
    destruct (TWK (kp + j) ltac:(lia)) as [(Hw & _) | HGj]; [exact (NFW _ Hw)|].
    exfalso. exact (NGK (kp + j) ltac:(lia) HGj).
  + apply (scr_garr8_kept (w_H W2) mem2 (ms_mem ms2) klp _); [|exact GKL].
    intros j Hj. rewrite LZKL in Hj. change (Z.of_nat 8) with 8 in Hj.
    apply KP; [lia|].
    destruct (TWKL (klp + j) ltac:(lia)) as [(Hw & _) | HGj]; [exact (NFW _ Hw)|].
    exfalso. exact (NGKL (klp + j) ltac:(lia) HGj).
Qed.

End rel.

Print Assumptions sendctl_rel.
