(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 329 of its 370 lines of code are new or changed and 1883 lines of the source are left out. *)
(* on_data_seg_rel: Theorem od_rel : forall fx rc B MT, @od_rel_stmt fx rc B MT (lib/B/Prog/on_data_seg_cut.v), the
   release piece of the image-B walk of on_data, offsets +0x40c .. +0x53c of the listing lib/B/Prog/DgnTransportBList.v
   (fuzz_transport.asan-ubsan 0x88e54 .. 0x88f84); image B's twin of lib/A/Prog/on_data_seg_rel.v (the code is the
   same 77 words, 0x14 bytes further on).

   What the code does. +0x40c `lui`/`addiw` a0 = 0x45e0360e and +0x414 `sd a0, 0(s10)`: the frame's first word
   (s10 = F); +0x418 `ld a1, 24(s1)`: the frame word at s1 + 24 (s1 = sp1), which holds F (od_rel_cur); +0x41c
   `beqz a1`: a1 = F >= 4096, so the real-stack arm at +0x4b0 is never entered (the engine decides the branch from the
   atom fact of s10, the value the load gives); +0x420 `li a0, -11` and 32 `sb a0, i(s9)`: the frame's 32 shadow
   bytes (s9 = SHADOW_OFF + F / 8) := 0xf5; +0x4a4 `ld a0, 248(a1)`: the flag pointer FL from the frame's last word;
   +0x4a8 `sb zero, 0(a0)`: the flag byte, which releases the frame (lib/B/Prog/TransportGFrameB.v
   gx_flag_store_pi); +0x4ac `j +0x500`; +0x500 `addi sp, s0, -160`; the 13 reloads +0x504 .. +0x534 of ra, s0, s1,
   s2 .. s11 from the words the prologue saved below the entry sp (on_data_seg_cut.v OD_SAVED); +0x538
   `addi sp, sp, 160`; +0x53c `ret`.

   One run of the plain position-abstract engine (lib/A/Prog/PaSym.v sym_run_pi over image B's listing: no shadow
   token, so the writable shadow region is allowed) covers +0x40c .. +0x53c and stops at the `ret`, which
   lib/B/Prog/DgnTransportBPaLib.v paj_ret_at takes. The symbolic state: the registers at +0x40c as atoms 0 .. 31,
   atom 32 the flag pointer FL, atoms 33 .. 45 the entry values of ra, s0, s1, s2 .. s11 (OD_SAVED, in its order);
   regions: the frame's first word (s10, written), its last word (s10, offset 248, read: FL), its 32 shadow bytes
   (s9, written), the flag byte (atom 32, written), the 13 saved words below s0 = the entry sp (read) and the frame
   word at s1 + 24 (read: the value of s10).

   The post (on_data_cg.v transport_ondata_post, TransportGCg.v transport_cg_post over G_HARNESS_B): the caller's G
   journal after the flag store, with own and the frame released (stack_free_state); the callee-saved registers are
   the 13 reloads, sp = s0 = the entry sp, gp and tp untouched; the frames the caller's (CanKit.v can_sf_frames); the
   state changed in st_fs only, so the meter bound is the cut's (mo_le_set_fs_r). What the call kept: the cut's
   acall_kept_g over ondata_wr Bw b, carried over the run by lib/A/Prog/TransportGFrame.v dk_kept_step_gw, whose four
   side conditions on the bytes the run may change (the own frame, its shadow bytes, its flag byte: TransportGCg.v
   dkg_nf) are TransportGFrame.v dkg_nf_sep_gw's. The world relation at Bw': the cut's, kept since no byte of G is a
   byte of dkg_nf (TWorldB.v tw_kept_GB); g_fail_next Bw' <= 1 is the cut's. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGFrameB on_data_seg_cut.
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
(* 1. The symbolic state at +0x40c and the run to the ret              *)
(* ------------------------------------------------------------------ *)

(* The `ret` of on_data. *)
Definition odr_RET : Z := AF_on_data + 0x53c.

(* The realigned stack pointer sp1 = 32 * ((sp - 160) / 32) lies in (sp - 192, sp - 160]. *)
Lemma odr_sp1_bounds : forall sp, sp - 192 < 32 * ((sp - 160) / 32) <= sp - 160.
Proof.
intros sp.
pose proof (Z.div_mod (sp - 160) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (sp - 160) 32 ltac:(lia)) as M.
lia.
Qed.

Definition odr_rg_hd : YP09.region := YP09.mkRegion (Some 26%nat) 0 8 0 8 [].
Definition odr_rg_fp : YP09.region :=
  YP09.mkRegion (Some 26%nat) 248 256 0 0 [YP09.mkChunk 248 (CVal 8 (SOff 32 0))].
Definition odr_rg_sh : YP09.region := YP09.mkRegion (Some 25%nat) 0 32 0 32 [].
Definition odr_rg_fl : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition odr_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
(* The frame word at s1 + 24: it holds F, the value of s10. *)
Definition odr_rg_fs : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 26 0))].
(* s10 = F is at least 4096 (decides the `beqz a1` at +0x41c) and 32-aligned. *)
Definition odr_facts : facts := mkFacts [(26%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition odr_ss : sstate :=
  mkSS OD_REL sr_atoms [odr_rg_hd; odr_rg_fp; odr_rg_sh; odr_rg_fl; odr_rg_sv; odr_rg_fs] None odr_facts.
(* 57 instructions on the path to the ret. *)
Definition odr_FUEL : N := 96.
Definition odr_ss_end : sstate := Eval vm_compute in fst (sym_runN_pi transportb_tpi odr_FUEL odr_ss).
Definition odr_st_end : prun_status tbsym := Eval vm_compute in snd (sym_runN_pi transportb_tpi odr_FUEL odr_ss).
Lemma odr_run : sym_runN_pi transportb_tpi odr_FUEL odr_ss = (odr_ss_end, odr_st_end).
Proof. vm_compute. reflexivity. Qed.
Lemma odr_stop : can_plain_stop odr_st_end.
Proof. exact I. Qed.
(* The run stops at the `ret` at +0x53c. *)
Lemma odr_end_pc : ss_pc odr_ss_end = odr_RET.
Proof. reflexivity. Qed.

(* The environment: the registers at +0x40c, then FL, then the entry values of the saved registers. *)
Definition odr_extra (regs : bvmap 5 word) (FL : Z) : list word :=
  w64 FL :: map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) OD_SAVED.

(* The value of register r in the machine state of HS: its symbolic value, computed. *)
Ltac odr_regv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

Section rel. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The cut point and the `ret` in the image's addresses. *)
Lemma odr_pcs : BASE + OD_REL = 0x88e54 /\ BASE + odr_RET = 0x88f84.
Proof. split; reflexivity. Qed.

Definition odr_E (regs2 regs : bvmap 5 word) (FL : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 (odr_extra regs FL)).

Lemma odr_ew_reg : forall regs2 regs FL n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (odr_E regs2 regs FL) n = YK11.getr regs2 r.
Proof. intros regs2 regs FL n r Hn. unfold odr_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma odr_ew_x : forall regs2 regs FL j, (j < 14)%nat ->
  ew (odr_E regs2 regs FL) (32 + j) = nth j (odr_extra regs FL) (Z_to_bv 64 0).
Proof. intros regs2 regs FL j Hj. unfold odr_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* The symbolic state at +0x40c holds of the machine state there. *)
Lemma odr_entry : forall (W : world segs) (regs2 regs : bvmap 5 word) mem (F FL SP SP1 : Z),
  YK11.getr regs2 8 = w64 SP -> YK11.getr regs2 9 = w64 SP1 ->
  YK11.getr regs2 25 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs2 26 = w64 F ->
  4096 <= F -> F mod 32 = 0 -> F + 256 <= alloc_ceiling -> in_app F 256 ->
  4096 <= FL < alloc_ceiling -> (FL < F \/ F + 256 <= FL) ->
  (FL < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 32 <= FL) ->
  alloc_ceiling <= SP - 104 -> SP <= 2 ^ 47 ->
  alloc_ceiling <= SP1 -> SP1 + 32 <= SP - 104 ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem a) ->
  (forall i, 0 <= i < 32 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  apresent (w_H W) mem FL ->
  rdword (aview segs (w_H W) mem) (F + 248) = Some FL ->
  rdword (aview segs (w_H W) mem) (SP1 + 24) = Some F ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (SP - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) OD_SAVED ->
  st_ok_pi segs VAL (odr_E regs2 regs FL) odr_ss
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OD_REL)) mem (YK11.seg_rom segs))).
Proof.
intros W regs2 regs mem F FL SP SP1 R8 R9 R25 R26 HF0 HF32 HFc HFapp HFL HFLF HFLS HSP HSP47 HS1 HS1b
  Hpf Hpsh HpFL HFLw Hs24 Hsaved.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF8 : F mod 8 = 0)
  by (pose proof (Z.div_mod F 32 ltac:(lia)) as D32; replace F with (F / 32 * 4 * 8) by lia; apply Z_mod_mult).
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. rewrite HF8, Z.add_0_r in D8.
set (E := odr_E regs2 regs FL).
assert (U8 : bv_unsigned (ew E 8) = SP)
  by (unfold E; rewrite (odr_ew_reg regs2 regs FL 8 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = SP1)
  by (unfold E; rewrite (odr_ew_reg regs2 regs FL 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF + F / 8)
  by (unfold E; rewrite (odr_ew_reg regs2 regs FL 25 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (E26 : ew E 26 = w64 F) by (unfold E; rewrite (odr_ew_reg regs2 regs FL 26 26%bv eq_refl); exact R26).
assert (U26 : bv_unsigned (ew E 26) = F) by (rewrite E26; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (odr_ew_x regs2 regs FL 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
unfold OD_SAVED in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold odr_ss.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks odr_rg_hd odr_rg_fp odr_rg_sh
      odr_rg_fl odr_rg_sv odr_rg_fs base_val];
    rewrite ?U8, ?U9, ?U25, ?U26, ?U32.
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
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ SP1 24 8 (SOff 26 0) F);
      [cbn [sv_denot]; rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ Hs24).
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, odr_rg_hd, odr_rg_fp, odr_rg_sh, odr_rg_fl, odr_rg_sv, odr_rg_fs.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U8, U9, U25, U26, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat split; first [exact I | lia].
- unfold odr_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U26.
  change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma odr_rel_at : @od_rel_stmt fx rc B MT.
Proof.
unfold od_rel_stmt, od_rel_at.
intros LAWS0 _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HREGS.
destruct LAWS0 as (_ & _ & _ & _ & _ & _ & _ & LAWS & MTL & MTF & _ & ASF & FFL & HGX & _).
destruct HFIX as ((HJ0 & Hret & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp0 & _) & _ & Esp1 & EF & HF0 & HF64 & HFc &
  HFapp).
destruct HCUR as ((HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw) & Hs24 & HTW2 & Hgf2).
destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R25 & R26).
unfold OD_FBYTES in HFc, HFapp, HFLw.
replace (F + 256 - 8) with (F + 248) in HFLw by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF32 : F mod 32 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((2 * (F / 64)) * 32) by lia. apply Z_mod_mult. }
(* the call's window lies above alloc_ceiling, below 2 ^ 47 *)
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4272 <= ONDATA_STK).
{ unfold ONDATA_STK, ONDATA_FRAME, ONDATA_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm; assert (Ha : a = 4096) by reflexivity end.
  lia. }
(* the realigned sp1 lies in (sp - 192, sp - 160] *)
assert (Hsp1 : spZ regs - 192 < sp1 <= spZ regs - 160)
  by (rewrite Esp1; unfold ONDATA_FRAME; exact (odr_sp1_bounds (spZ regs))).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
(* the frame, its shadow bytes and its flag byte at the cut *)
assert (Hin : In (ONDATA_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 ONDATA_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
assert (EFL : flag_addr ly2 ONDATA_CID pos = flag_addr lyc ONDATA_CID pos)
  by (unfold flag_addr; rewrite ELF; reflexivity).
rewrite <- EFL in HFLw.
destruct (al_frames _ _ LAWS _ _ _ _ _ ONDATA_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
destruct (FFL ly2 S2 W2 mem2 md2 ONDATA_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
set (FL := flag_addr ly2 ONDATA_CID pos) in *.
change (fs_frame_bytes ONDATA_CID / 8) with 32 in HFsh.
change (fs_frame_bytes ONDATA_CID) with 256 in HFb.
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
destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONDATA_CID pos F FL HAR2 Hfrs Hbl
  ELF EF EFL FFL) as (N1 & N2 & N3 & N4).
pose proof (odr_entry W2 regs2 regs mem2 F FL (spZ regs) sp1 R8 R9 R25 R26 HF0 HF32 HFc HFapp
  ltac:(lia) HFLF HFLS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i Hi)))
  HFLp HFLw Hs24 Hsaved) as HS.
set (E := odr_E regs2 regs FL) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, odr_E; apply Eimg_env).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E; rewrite (odr_ew_reg regs2 regs _ 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF + F / 8).
{ pose proof (Z.div_lt_upper_bound F 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  unfold E; rewrite (odr_ew_reg regs2 regs _ 25 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small;
  unfold SHADOW_OFF; lia. }
assert (U26 : bv_unsigned (ew E 26) = F)
  by (unfold E; rewrite (odr_ew_reg regs2 regs _ 26 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (odr_ew_x regs2 regs _ 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
(* +0x40c .. +0x53c in one run, the flag store at +0x4a8 releasing the frame. *)
refine (TransportGFrameB.gx_flag_store_pi (SK := tfib_sink_head) B LAWS ASF FFL TG.G_HARNESS_B W2 odr_FUEL E odr_ss
  odr_ss_end odr_st_end (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OD_REL)) mem2 (YK11.seg_rom segs))
  STK sp0 FP ly S W0 mem0 md0 own ly2 S2 md2 (k + e) ONDATA_CID pos _ HEI HS odr_run odr_stop HJ1 _ _ _ _).
- unfold ONDATA_CID. lia.
- (* the run writes the frame's first word, its shadow and the flag byte *)
  intros a (rg & Hinr & Ha). unfold odr_ss in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi odr_rg_hd odr_rg_fp odr_rg_sh odr_rg_fl odr_rg_sv odr_rg_fs]
      in Ha;
    rewrite ?U25, ?U26, ?U32 in Ha.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists ONDATA_CID, pos.
    split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes ONDATA_CID) with 256. lia.
  + lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists ONDATA_CID, pos.
    split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes ONDATA_CID / 8) with 32.
    rewrite ESH. lia.
  + right. change (flag_addr ly2 ONDATA_CID pos) with FL. lia.
  + lia.
  + lia.
- (* the flag byte is 0 after the run *)
  intros msr HSr.
  lazymatch goal with |- _ = Some _ =>
    let rr := eval vm_compute in (nth_error (ss_mem odr_ss_end) 3) in
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
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ dkg_nf ONDATA_CID F FL a ->
    aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) mem2 a).
  { apply (kept_of_frame (segs := segs) E (ss_mem odr_ss) (w_H W2) mem2 (ms_mem ms2) _ HF2).
    intros b0 wlo whi x Hw Hx. unfold odr_ss, windows in Hw.
    cbn [ss_mem map In YP09.r_base YP09.r_wlo YP09.r_whi odr_rg_hd odr_rg_fp odr_rg_sh odr_rg_fl odr_rg_sv
      odr_rg_fs] in Hw.
    unfold dkg_nf. change (fs_frame_bytes ONDATA_CID / 8) with 32. change (fs_frame_bytes ONDATA_CID) with 256.
    destruct Hw as [Hw | [Hw | [Hw | [Hw | [Hw | [Hw | []]]]]]]; injection Hw as <- <- <-;
      cbn [base_val] in Hx; rewrite ?U9, ?U25, ?U26, ?U32 in Hx.
    + left. lia.
    + lia.
    + right; left. lia.
    + right; right. lia.
    + lia.
    + lia. }
  assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG2 Ha)).
  eapply (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb) W2 E odr_ss_end ms2 md3 _
    HS2 eq_refl ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat3 md3).
  pose proof (ajournal_gx_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ2)
    as HJ3.
  fold md4 in HJ3. clearbody md4.
  (* the registers at the ret *)
  assert (R1e : YK11.getr (ms_regs ms2) 1 = YK11.getr regs 1).
  { odr_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (HP : aregs_preserved regs (ms_regs ms2)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      odr_regv HS2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    all: first
      [ reflexivity
      | transitivity (YK11.getr regs2 3); [apply odr_ew_reg; reflexivity | exact R3]
      | transitivity (YK11.getr regs2 4); [apply odr_ew_reg; reflexivity | exact R4]
      | transitivity (YK11.getr regs2 8); [apply odr_ew_reg; reflexivity|];
        rewrite R8; unfold w64, spZ; apply Z_to_bv_bv_unsigned ]. }
  assert (Hpc : v_jalr (YK11.getr (ms_regs ms2) 1) 0 = YK11.getr regs 1) by (rewrite R1e; exact Hret).
  assert (Eab' : ablocks B ly2 (stack_free_state ONDATA_CID pos S2) = ablocks B ly2 S2)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  unfold transport_ondata_post, transport_cg_post.
  exists ly2, (stack_free_state ONDATA_CID pos S2), (ms_regs ms2), (ms_mem ms2), md4, e.
  split; [rewrite Hpc; reflexivity|].
  split; [exact He|].
  split; [exact HJ3|].
  split; [exact HP|].
  split; [exact (can_sf_frames ONDATA_CID pos S2 (frames Sc) Hfrs)|].
  split; [rewrite Eab'; exact Hperm|].
  split.
  { (* the cut's acall_kept_g, over the run's bytes (the own frame, its shadow, its flag byte) *)
    apply (dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2 (ms_mem ms2)
      (spZ regs - ONDATA_STK) (spZ regs) (ondata_wr Bw b) (dkg_nf ONDATA_CID F FL) HARc HK KP GA).
    - intros a Ha Hc. pose proof (N4 a Ha). lia.
    - intros b0 m i Hb Hi Ha. exfalso. exact (N1 b0 m i Hb Hi Ha).
    - intros a Ha Hi _ _ _. exfalso. exact (N2 a Ha Hi).
    - intros c p a Hc Hr Ha. exfalso. exact (N3 c p a Hc Hr Ha). }
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

End rel.

Theorem od_rel : forall fx rc B MT, @od_rel_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@odr_rel_at fx rc B MT). Qed.

Print Assumptions od_rel.
