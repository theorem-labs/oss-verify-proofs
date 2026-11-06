(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 551 of its 604 lines of code are new or changed and 1871 lines of the source are left out. *)
(* SrxBRel: the release and ignored pieces of diginet_session_rx's image-B G-form walk (lib/B/Prog/SrxBCut.v):
   srxb_rel_ok : srxb_rel_stmt and srxb_ign_ok : srxb_ign_stmt, offsets +0x1d4 .. +0x2e0 of the listing
   lib/B/Prog/DgnTransportBList.v (fuzz_transport.asan-ubsan 0x87958 .. 0x87a64). The code is image A's
   (lib/A/Prog/SrxRel.v) 12 bytes later; the proof is that file's at image B's names.

   The release, +0x1e0 .. +0x2e0. +0x1e0 `li a1, -8` and 8 `sb a1, i(s9)`: the frame's shadow bytes 4 .. 11 := 0xf8
   (s9 = SHADOW_OFF + F / 8); +0x204 `lui`/`addiw` a1 = 0x45e0360e and +0x20c `sd a1, 0(s10)`: the frame's first word
   (s10 = F); +0x210 `beqz s2`: s2 = F >= 4096, so the real-stack arm at +0x264 .. +0x2a0 is never entered (the engine
   decides the branch from the atom fact of s2); +0x214 `li a1, -11` and 16 `sb a1, i(s9)`: the frame's 16 shadow bytes
   := 0xf5; +0x258 `ld a1, 120(s2)`: the flag pointer FL from the frame's last word; +0x25c `sb zero, 0(a1)`: the flag
   byte, which releases the frame (lib/B/Prog/TransportGFrameB.v gx_flag_store_pi); +0x260 `j +0x2a4`; +0x2a4
   `addi sp, s0, -160`; the 13 reloads +0x2a8 .. +0x2d8 of ra, s0, s1, s2 .. s11 from the words the prologue saved
   below the entry sp (SrxBCut.v SRXB_SAVED); +0x2dc `addi sp, sp, 160`; +0x2e0 `ret`.

   One run of the plain position-abstract engine (lib/A/Prog/PaSym.v sym_run_pi over image B's listing,
   transportb_tpi: no shadow token, so the writable shadow region is allowed) covers +0x1e0 .. +0x2e0 and stops at the
   `ret`, which lib/B/Prog/DgnTransportBPaLib.v paj_ret_at takes. The symbolic state: the registers at +0x1e0 as atoms
   0 .. 31, atom 32 the flag pointer FL, atoms 33 .. 45 the entry values of ra, s0, s1, s2 .. s11 (SRXB_SAVED, in its
   order); regions: the frame's first word (s10, written), its last word (s2, offset 120, read: FL), its 16 shadow
   bytes (s9, written), the flag byte (atom 32, written) and the 13 saved words below s0 = the entry sp (read). a0, the
   result, is not touched.

   The post (diginet_session_rx_cg.v transport_srx_post, TransportGCg.v transport_cg_post over G_HARNESS_B): the
   caller's G journal after the flag store, with own and the frame released (stack_free_state); the callee-saved
   registers are the 13 reloads, sp = s0 = the entry sp, gp and tp untouched; the frames the caller's (CanKit.v
   can_sf_frames); the state changed in st_fs only, so the meter bound is the cut's (mo_le_set_fs_r). What the call
   kept: the cut's acall_kept_g, carried over the run by lib/A/Prog/TransportGFrame.v dk_kept_step_gw, whose four side
   conditions on the bytes the run may change (the own frame, its shadow bytes, its flag byte: TransportGCg.v dkg_nf)
   are TransportGFrame.v dkg_nf_sep_gw's. The world relation at Bw': the cut's, kept since no byte of G is a byte of
   dkg_nf (TWorldB.v tw_kept_GB).

   The ignored path, +0x1d4 .. +0x1dc: `ld a2, 0(a1)`, `addi a2, a2, 1`, `sd a2, 0(a1)` with a1 = s + 18184
   (g_s.stats.rx_ignored; every path to +0x1d4 checked its shadow byte before the jump), then the release cut. One run
   of the token engine over the caller's G journal (lib/B/Prog/TransportGRunB.v paj_run_to_x), whose one region is the
   8 bytes of the counter, a region of G holding atom 32, the world's u_at at that field; the store is allowed by the
   run's write right (W_journalG.v awr_ok_x_cons_g). After it the counter's bytes are those of TSess0.v u64 (u + 1),
   so the memory relates to srx_ign Bx (TWorldG.v tw_write), g_fail_next is unchanged (the store misses it), the run
   kept every other byte (what the call kept: TransportGFrame.v dk_kept_nfz_gw, the changed bytes being bytes of G;
   the 13 saved words and the frame's last word lie outside G), and the release piece concludes. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import CanKit SrxBCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require TransportGFrameB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module YO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YO0f.
Module GFB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.TransportGFrameB.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The release: the symbolic state at +0x1e0 and the run to the ret *)
(* ------------------------------------------------------------------ *)

(* The `ret` of diginet_session_rx. *)
Definition SRXB_RET : Z := AF_diginet_session_rx + 0x2e0.

Definition sbr_rg_hd : YP09.region := YP09.mkRegion (Some 26%nat) 0 8 0 8 [].
Definition sbr_rg_fp : YP09.region :=
  YP09.mkRegion (Some 18%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 32 0))].
Definition sbr_rg_sh : YP09.region := YP09.mkRegion (Some 25%nat) 0 16 0 16 [].
Definition sbr_rg_fl : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition sbr_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
(* s2 = s10 = F is at least 4096 (decides the `beqz s2` at +0x210) and 32-aligned. *)
Definition sbr_facts : facts := mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 5); (26%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition ss_sbr : sstate :=
  mkSS SRXB_REL sr_atoms [sbr_rg_hd; sbr_rg_fp; sbr_rg_sh; sbr_rg_fl; sbr_rg_sv] None sbr_facts.
Definition SBR_FUEL : N := 96.
Definition sbr_ss_end : sstate := Eval vm_compute in fst (sym_runN_pi transportb_tpi SBR_FUEL ss_sbr).
Definition sbr_st_end : prun_status tbsym := Eval vm_compute in snd (sym_runN_pi transportb_tpi SBR_FUEL ss_sbr).
Lemma sbr_run : sym_runN_pi transportb_tpi SBR_FUEL ss_sbr = (sbr_ss_end, sbr_st_end).
Proof. vm_compute. reflexivity. Qed.
Lemma sbr_stop : can_plain_stop sbr_st_end.
Proof. exact I. Qed.
Lemma sbr_end_pc : ss_pc sbr_ss_end = SRXB_RET.
Proof. reflexivity. Qed.

(* The environment: the registers at +0x1e0, then FL, then the entry values of the saved registers. *)
Definition sbr_extra (regs : bvmap 5 word) (FL : Z) : list word :=
  w64 FL :: map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) SRXB_SAVED.

(* The value of register r in the machine state of HS: its symbolic value, computed. *)
Ltac sbr_regv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

(* ------------------------------------------------------------------ *)
(* 2. The ignored path: the symbolic state at +0x1d4                   *)
(* ------------------------------------------------------------------ *)

(* g_s.stats.rx_ignored: its one region (base a1, atom 11; it holds atom 32), a1's value and alignment. *)
Definition sbi_rg : YP09.region := YP09.mkRegion (Some 11%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition sbi_facts : facts := mkFacts [(11%nat, mkAF SRXB_RXIGN SRXB_RXIGN 3)] [] [].
Definition ss_sbi : sstate := mkSS SRXB_IGN sr_atoms [sbi_rg] None sbi_facts.
Definition SBI_Bx : sv := SLit 0.
Definition SBI_B0 : Z * Z := (0, 0).

(* The world's offset of the counter. *)
Lemma sbi_off : TW.A_S_stats_rx_ignored = TW.OFF_g_s + 18184.
Proof. reflexivity. Qed.

(* The model's ignored world, at the numeral offset. *)
Lemma sbi_ign_eq : forall Bx,
  srx_ign Bx = TW.upd Bx (TW.OFF_g_s + 18184) (TW.put 8 (TS0.u64 (TW.u_at Bx (TW.OFF_g_s + 18184) 8 + 1))).
Proof. intros Bx. reflexivity. Qed.

(* The store misses g_fail_next. *)
Lemma sbi_gfn : forall Bx, length Bx = Z.to_nat TW.W_LEN -> TW.g_fail_next (srx_ign Bx) = TW.g_fail_next Bx.
Proof.
intros Bx HL.
assert (LZ : Z.of_nat (length Bx) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
rewrite sbi_ign_eq. unfold TW.g_fail_next.
rewrite TWL.u_at_upd_out;
  [reflexivity | unfold TW.OFF_g_s; lia | unfold TW.OFF_g_fail_next; lia
  | rewrite TWL.length_put; unfold TW.OFF_g_s, TW.OFF_g_fail_next; lia
  | rewrite TWL.length_put, LZ; unfold TW.OFF_g_s, TW.W_LEN; lia].
Qed.

(* The register value the store leaves, as the model's u64 of the sum. *)
Lemma sbi_sum : forall (E : env) u, ew E 32 = Z_to_bv 64 u -> 0 <= u < 2 ^ 64 ->
  sv_denot E (SOff 32 1) = Z_to_bv 64 (TS0.u64 (u + 1)).
Proof.
intros E u H Hu. cbn [sv_denot]. rewrite H, (unsigned_lit_small u) by exact Hu.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, TS0.u64. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section rel. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition sbr_E (regs2 regs : bvmap 5 word) (FL : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 (sbr_extra regs FL)).

Lemma sbr_ew_reg : forall regs2 regs FL n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (sbr_E regs2 regs FL) n = YK11.getr regs2 r.
Proof. intros regs2 regs FL n r Hn. unfold sbr_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma sbr_ew_x : forall regs2 regs FL j, (j < 14)%nat ->
  ew (sbr_E regs2 regs FL) (32 + j) = nth j (sbr_extra regs FL) (Z_to_bv 64 0).
Proof. intros regs2 regs FL j Hj. unfold sbr_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* The symbolic state at +0x1e0 holds of the machine state there. *)
Lemma sbr_entry : forall (W : world segs) (regs2 regs : bvmap 5 word) mem (F FL SP : Z),
  YK11.getr regs2 8 = w64 SP -> YK11.getr regs2 18 = w64 F ->
  YK11.getr regs2 25 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs2 26 = w64 F ->
  4096 <= F -> F mod 32 = 0 -> F + 128 <= alloc_ceiling -> in_app F 128 ->
  4096 <= FL < alloc_ceiling -> (FL < F \/ F + 128 <= FL) ->
  (FL < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 16 <= FL) ->
  alloc_ceiling <= SP - 104 -> SP <= 2 ^ 47 ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem a) ->
  (forall i, 0 <= i < 16 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  apresent (w_H W) mem FL ->
  rdword (aview segs (w_H W) mem) (F + 120) = Some FL ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (SP - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SRXB_SAVED ->
  st_ok_pi segs VAL (sbr_E regs2 regs FL) ss_sbr
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SRXB_REL)) mem (YK11.seg_rom segs))).
Proof.
intros W regs2 regs mem F FL SP R8 R18 R25 R26 HF0 HF32 HFc HFapp HFL HFLF HFLS HSP HSP47
  Hpf Hpsh HpFL HFLw Hsaved.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF8 : F mod 8 = 0)
  by (pose proof (Z.div_mod F 32 ltac:(lia)) as D32; replace F with (F / 32 * 4 * 8) by lia; apply Z_mod_mult).
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. rewrite HF8, Z.add_0_r in D8.
set (E := sbr_E regs2 regs FL).
assert (U8 : bv_unsigned (ew E 8) = SP)
  by (unfold E; rewrite (sbr_ew_reg regs2 regs FL 8 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (E18 : ew E 18 = w64 F) by (unfold E; rewrite (sbr_ew_reg regs2 regs FL 18 18%bv eq_refl); exact R18).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF + F / 8)
  by (unfold E; rewrite (sbr_ew_reg regs2 regs FL 25 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (E26 : ew E 26 = w64 F) by (unfold E; rewrite (sbr_ew_reg regs2 regs FL 26 26%bv eq_refl); exact R26).
assert (U26 : bv_unsigned (ew E 26) = F) by (rewrite E26; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (sbr_ew_x regs2 regs FL 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
unfold SRXB_SAVED in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss_sbr.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks sbr_rg_hd sbr_rg_fp sbr_rg_sh
      sbr_rg_fl sbr_rg_sv base_val];
    rewrite ?U8, ?U18, ?U25, ?U26, ?U32.
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
  unfold extent_of_region, sbr_rg_hd, sbr_rg_fp, sbr_rg_sh, sbr_rg_fl, sbr_rg_sv.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U8, U18, U25, U26, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat split; first [exact I | lia].
- unfold sbr_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18, U26.
  change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The release piece                                                *)
(* ------------------------------------------------------------------ *)

Lemma sbr_rel : @srxb_rel_stmt fx rc B MT.
Proof.
unfold srxb_rel_stmt, srxb_rel_at.
intros LAWS0 _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HTW2 Hgf2 HREGS.
destruct LAWS0 as (_ & _ & _ & _ & _ & _ & _ & LAWS & MTL & MTF & _ & ASF & FFL & HGX & _).
destruct HFIX as (HJ0 & Hret & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF & HF0 & HF64 & HFc & HFapp).
destruct HCUR as (HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw).
destruct HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22) & R10).
unfold SRXB_FBYTES in HFc, HFapp, HFLw.
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
assert (HBS : 4240 <= SRX_STK).
{ unfold SRX_STK, SRX_FRAME, SRX_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm; assert (Ha : a = 8192) by reflexivity end.
  lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
(* the frame, its shadow bytes and its flag byte at the cut *)
assert (Hin : In (SRX_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 SRX_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
assert (EFL : flag_addr ly2 SRX_CID pos = flag_addr lyc SRX_CID pos)
  by (unfold flag_addr; rewrite ELF; reflexivity).
rewrite <- EFL in HFLw.
destruct (al_frames _ _ LAWS _ _ _ _ _ SRX_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
destruct (FFL ly2 S2 W2 mem2 md2 SRX_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
set (FL := flag_addr ly2 SRX_CID pos) in *.
change (fs_frame_bytes SRX_CID / 8) with 16 in HFsh.
change (fs_frame_bytes SRX_CID) with 128 in HFb.
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
destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 SRX_CID pos F FL HAR2 Hfrs Hbl
  ELF EF EFL FFL) as (N1 & N2 & N3 & N4).
pose proof (sbr_entry W2 regs2 regs mem2 F FL (spZ regs) R8 R18 R25 R26 HF0 HF32 HFc HFapp
  ltac:(lia) HFLF HFLS ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i Hi)))
  HFLp HFLw Hsaved) as HS.
set (E := sbr_E regs2 regs FL) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, sbr_E; apply Eimg_env).
assert (U18 : bv_unsigned (ew E 18) = F)
  by (unfold E; rewrite (sbr_ew_reg regs2 regs _ 18 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF + F / 8).
{ pose proof (Z.div_lt_upper_bound F 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  unfold E; rewrite (sbr_ew_reg regs2 regs _ 25 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small;
  unfold SHADOW_OFF; lia. }
assert (U26 : bv_unsigned (ew E 26) = F)
  by (unfold E; rewrite (sbr_ew_reg regs2 regs _ 26 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (sbr_ew_x regs2 regs _ 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
(* +0x1e0 .. +0x2e0 in one run, the flag store at +0x25c releasing the frame. *)
refine (GFB.gx_flag_store_pi (SK := tfib_sink_head) B LAWS ASF FFL TG.G_HARNESS_B W2 SBR_FUEL E ss_sbr sbr_ss_end
  sbr_st_end (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SRXB_REL)) mem2 (YK11.seg_rom segs))
  STK sp0 FP ly S W0 mem0 md0 own ly2 S2 md2 (k + e) SRX_CID pos _ HEI HS sbr_run sbr_stop HJ1 _ _ _ _).
- unfold SRX_CID. lia.
- (* the run writes the frame's first word, its shadow and the flag byte *)
  intros a (rg & Hinr & Ha). unfold ss_sbr in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<- | [<- | [<- | [<- | [<- | []]]]]];
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi sbr_rg_hd sbr_rg_fp sbr_rg_sh sbr_rg_fl sbr_rg_sv] in Ha;
    rewrite ?U25, ?U26, ?U32 in Ha.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists SRX_CID, pos.
    split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes SRX_CID) with 128. lia.
  + lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists SRX_CID, pos.
    split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes SRX_CID / 8) with 16.
    rewrite ESH. lia.
  + right. change (flag_addr ly2 SRX_CID pos) with FL. lia.
  + lia.
- (* the flag byte is 0 after the run *)
  intros msr HSr.
  lazymatch goal with |- _ = Some _ =>
    let rr := eval vm_compute in (nth_error (ss_mem sbr_ss_end) 3) in
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
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ dkg_nf SRX_CID F FL a ->
    aview segs (w_H W2) (ms_mem ms2) a = aview segs (w_H W2) mem2 a).
  { apply (kept_of_frame (segs := segs) E (ss_mem ss_sbr) (w_H W2) mem2 (ms_mem ms2) _ HF2).
    intros b0 wlo whi x Hw Hx. unfold ss_sbr, windows in Hw.
    cbn [ss_mem map In YP09.r_base YP09.r_wlo YP09.r_whi sbr_rg_hd sbr_rg_fp sbr_rg_sh sbr_rg_fl sbr_rg_sv]
      in Hw.
    unfold dkg_nf. change (fs_frame_bytes SRX_CID / 8) with 16. change (fs_frame_bytes SRX_CID) with 128.
    destruct Hw as [Hw | [Hw | [Hw | [Hw | [Hw | []]]]]]; injection Hw as <- <- <-;
      cbn [base_val] in Hx; rewrite ?U18, ?U25, ?U26, ?U32 in Hx.
    + left. lia.
    + lia.
    + right; left. lia.
    + right; right. lia.
    + lia. }
  assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG2 Ha)).
  eapply (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb) W2 E sbr_ss_end ms2 md3 _
    HS2 eq_refl ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat3 md3).
  pose proof (ajournal_gx_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ2)
    as HJ3.
  fold md4 in HJ3. clearbody md4.
  (* the registers at the ret *)
  assert (R1e : YK11.getr (ms_regs ms2) 1 = YK11.getr regs 1).
  { sbr_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10e : YK11.getr (ms_regs ms2) 10 = w64 r).
  { sbr_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    transitivity (YK11.getr regs2 10); [apply sbr_ew_reg; reflexivity | exact R10]. }
  assert (HP : aregs_preserved regs (ms_regs ms2)).
  { intros r0 Hr. unfold acallee_saved in Hr.
    assert (Hr' : r0 = 2 \/ r0 = 3 \/ r0 = 4 \/ r0 = 8 \/ r0 = 9 \/ r0 = 18 \/ r0 = 19 \/ r0 = 20 \/ r0 = 21 \/
      r0 = 22 \/ r0 = 23 \/ r0 = 24 \/ r0 = 25 \/ r0 = 26 \/ r0 = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      sbr_regv HS2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    all: first
      [ reflexivity
      | transitivity (YK11.getr regs2 3); [apply sbr_ew_reg; reflexivity | exact R3]
      | transitivity (YK11.getr regs2 4); [apply sbr_ew_reg; reflexivity | exact R4]
      | transitivity (YK11.getr regs2 8); [apply sbr_ew_reg; reflexivity|];
        rewrite R8; unfold w64, spZ; apply Z_to_bv_bv_unsigned ]. }
  assert (Hpc : v_jalr (YK11.getr (ms_regs ms2) 1) 0 = YK11.getr regs 1) by (rewrite R1e; exact Hret).
  assert (Eab' : ablocks B ly2 (stack_free_state SRX_CID pos S2) = ablocks B ly2 S2)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  unfold transport_srx_post, transport_cg_post.
  exists ly2, (stack_free_state SRX_CID pos S2), (ms_regs ms2), (ms_mem ms2), md4, e.
  split; [rewrite Hpc; reflexivity|].
  split; [exact He|].
  split; [exact HJ3|].
  split; [exact HP|].
  split; [exact (can_sf_frames SRX_CID pos S2 (frames Sc) Hfrs)|].
  split; [rewrite Eab'; exact Hperm|].
  split.
  { (* the cut's acall_kept_g, over the run's bytes (the own frame, its shadow, its flag byte) *)
    apply (dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2 (ms_mem ms2)
      (spZ regs - SRX_STK) (spZ regs) (srx_wr b) (dkg_nf SRX_CID F FL) HARc HK KP GA).
    - intros a Ha Hc. pose proof (N4 a Ha). lia.
    - intros b0 m i Hb Hi Ha. exfalso. exact (N1 b0 m i Hb Hi Ha).
    - intros a Ha Hi _ _ _. exfalso. exact (N2 a Ha Hi).
    - intros c p a Hc Hr Ha. exfalso. exact (N3 c p a Hc Hr Ha). }
  split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact Hmo|].
  split; [exact R10e|].
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

Theorem srxb_rel_ok : forall fx rc B MT, @srxb_rel_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@sbr_rel fx rc B MT). Qed.

(* ------------------------------------------------------------------ *)
(* 4. The ignored piece                                                *)
(* ------------------------------------------------------------------ *)

Section ign. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* g_s's payload bytes are bytes of G. *)
Lemma sbi_inG : forall a, SRX_S <= a < SRX_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_s) | unfold in_zr, SRX_S in *; cbn [fst snd]; lia].
Qed.

(* The bytes a chunk of a region holding the value v leaves in the memory. *)
Lemma sbi_cval : forall (H : word -> bool) (m : word -> option byte) (E : env) bopt lo hi wlo whi cs off (wd : N)
    (val : sv) (v : Z) (c : nat) j,
  YP09.region_ok segs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (CVal wd val)) cs ->
  Z.of_N wd = Z.of_nat c -> sv_denot E val = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_nat c) ->
  (j < c)%nat -> (c <= 8)%nat ->
  aview segs H m (base_val E bopt + off + Z.of_nat j) = Some (YO.le_byte v c j).
Proof.
intros H m E bopt lo hi wlo whi cs off wd val v c j (_ & _ & _ & Hcs) Hin Hwd Hval Hv Hj Hc8.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hch. cbn [YP09.r_base] in Hch.
assert (Hv64 : 0 <= v < 2 ^ 64).
{ split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hv)|]. apply Z.pow_le_mono_r; lia. }
destruct (Hch (Z.of_nat j) ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (bt & Hb & Hm).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb. rewrite Hval in Hb.
unfold YP09.byte_of_word in Hb. injection Hb as <-.
unfold aview. cbn [YP09.c_off] in Hm. rewrite Hm. cbn [option_map]. f_equal.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small v (2 ^ 64)) by lia.
unfold YO.le_byte. rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat c))) by lia. reflexivity.
Qed.

(* The valuation of the run: the registers at +0x1d4, then the world's 8 bytes of the counter. *)
Definition sbi_E (regs : bvmap 5 word) (Bx : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 18184) 8)]).

Lemma sbi_entry : forall (W : world segs) regs mem Bx,
  tw_at TMAP_B (aview segs (w_H W) mem) Bx ->
  YK11.getr regs 11 = w64 SRXB_RXIGN ->
  st_ok_pi segs VAL (sbi_E regs Bx) ss_sbi
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SRXB_IGN)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem Bx Htw R11.
set (E := sbi_E regs Bx).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, sbi_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U11 : bv_unsigned (ew E 11) = SRXB_RXIGN)
  by (rewrite (EE 11%nat 11%bv eq_refl), R11; unfold w64; apply unsigned_lit_small;
      unfold SRXB_RXIGN, SRX_S, TB_g_s; lia).
assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 18184) 8)).
{ unfold E, sbi_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 18184) 8) as R32.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32.
rewrite restrict_mkst_fx. unfold ss_sbi.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks sbi_rg base_val]. rewrite U11.
  split; [unfold SRXB_RXIGN, SRX_S, TB_g_s; lia|]. split; [unfold SRXB_RXIGN, SRX_S, TB_g_s; lia|]. split.
  + intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (SRXB_RXIGN + o) G_HARNESS_B_rw).
    apply sbi_inG. unfold SRXB_RXIGN, TW.SZ_g_s. lia.
  + apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ SRXB_RXIGN 0 8 (SOff 32 0) (TW.u_at Bx (TW.OFF_g_s + 18184) 8));
      [ cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by exact R32; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact R32
      | cbn; lia |].
    replace (SRXB_RXIGN + 0) with (TB_g_s + 18184) by (unfold SRXB_RXIGN, SRX_S; lia).
    exact (tw_read_val segs _ TMAP_B Bx TW.OFF_g_s TB_g_s TW.SZ_g_s 18184 8 TMAP_B_ok Htw TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- unfold sbi_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U11. change (2 ^ 3) with 8.
  unfold SRXB_RXIGN, SRX_S, TB_g_s.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | vm_compute; reflexivity].
Qed.

(* An atom register the run does not touch keeps its value at the cut. *)
Lemma sbi_off0 : forall (E : env) n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Ltac sbi_keep HS E5lo EE n r R :=
  sbr_regv HS;
  etransitivity; [apply sbi_off0|];
  etransitivity; [exact (E5lo n ltac:(lia))|];
  etransitivity; [exact (EE n r eq_refl)|];
  exact R.

Lemma sbi_ign : @srxb_ign_stmt fx rc B MT.
Proof.
unfold srxb_ign_stmt, srxb_ign_at.
intros REL LAWS0 CALLS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' Bx pos sp1 F
  ly2 S2 W2 mem2 md2 e regs2 HFIX HCUR HTWx HGFx EBw' HREGS.
pose proof LAWS0 as (_ & _ & _ & _ & _ & _ & _ & LAWS & MTL & MTF & _ & ASF & FFL & HGX & _).
pose proof HFIX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R27) & R21 & R22) & R10 & R11).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold SRXB_FBYTES in HFc, HFapp.
(* the call's window lies above alloc_ceiling, below 2 ^ 47 *)
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
assert (HBS : 4240 <= SRX_STK).
{ unfold SRX_STK, SRX_FRAME, SRX_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm; assert (Ha : a = 8192) by reflexivity end.
  lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
assert (HLx : length Bx = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ HTWx).
assert (Hin : In (SRX_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 SRX_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
(* +0x1d4 .. +0x1dc: the load of g_s.stats.rx_ignored, + 1, the store back, to the release cut *)
pose proof (sbi_entry W2 regs2 mem2 Bx HTWx R11) as HS.
set (E0 := sbi_E regs2 Bx) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, sbi_E; apply Eimg_env).
assert (EE : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E0 n = YK11.getr regs2 r0)
  by (intros n r0 Hn; unfold E0, sbi_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U11 : bv_unsigned (ew E0 11) = SRXB_RXIGN)
  by (rewrite (EE 11%nat 11%bv eq_refl), R11; unfold w64; apply unsigned_lit_small;
      unfold SRXB_RXIGN, SRX_S, TB_g_s; lia).
assert (E32 : ew E0 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 18184) 8)).
{ unfold E0, sbi_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 0). }
pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 18184) 8) as R32.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32.
assert (SHOK : sh_ok segs SBI_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS HJ1 SHOK SBI_B0 SRXB_REL.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U11 in Ha;
      apply sbi_inG; unfold SRXB_RXIGN, TW.SZ_g_s in *; lia |].
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E5 := EF) in * end.
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew E0 n)
  by (intros n Hn; unfold E5; rewrite ?ew_ewset_other by lia; reflexivity).
(* the run wrote the counter's 8 bytes only; presence grows *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (SRXB_RXIGN <= a < SRXB_RXIGN + 8) ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SRXB_RXIGN <= x < SRXB_RXIGN + 8) HFr);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  lazymatch type of Hiw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hiw end.
  cbn [In] in Hiw.
  destruct Hiw as [Hiw | []]. injection Hiw as <- <- <-. cbn [base_val] in Hx. rewrite U11 in Hx. lia. }
assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
(* the counter's bytes after the store: u64 (u + 1) *)
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (E32' : ew E5 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 18184) 8)) by (rewrite E5lo by lia; exact E32).
assert (U11' : bv_unsigned (ew E5 11) = SRXB_RXIGN) by (rewrite E5lo by lia; exact U11).
set (v := TS0.u64 (TW.u_at Bx (TW.OFF_g_s + 18184) 8 + 1)).
assert (Hv : 0 <= v < 2 ^ (8 * Z.of_nat 8))
  by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); unfold v, TS0.u64; apply Z.mod_pos_bound; lia).
assert (TWB : forall j, (j < 8)%nat ->
  aview segs (w_H W2) (ms_mem ms) (TB_g_s + 18184 + Z.of_nat j) = Some (YO.le_byte v 8 j)).
{ intros j Hj.
  lazymatch type of RG0 with YP09.region_ok _ _ _ (YP09.mkRegion ?bo ?lo ?hi ?wl ?wh ?cs) =>
    lazymatch cs with context [YP09.mkChunk ?off (CVal 8 ?e)] =>
      pose proof (sbi_cval (w_H W2) (ms_mem ms) E5 bo lo hi wl wh cs off 8 e v 8 j RG0
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl
        (sbi_sum E5 (TW.u_at Bx (TW.OFF_g_s + 18184) 8) E32' R32) Hv Hj ltac:(lia)) as X
    end end.
  cbn [base_val] in X. rewrite U11' in X.
  replace (TB_g_s + 18184) with (SRXB_RXIGN + 0) by (unfold SRXB_RXIGN, SRX_S; lia). exact X. }
(* the world relation at srx_ign Bx *)
assert (TW5 : tw_at TMAP_B (aview segs (w_H W2) (ms_mem ms)) (srx_ign Bx)).
{ rewrite sbi_ign_eq. fold v.
  apply (tw_write TMAP_B (aview segs (w_H W2) mem2) _ Bx TW.OFF_g_s TB_g_s TW.SZ_g_s 18184 8 v TMAP_B_ok HTWx
    TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | exact TWB |].
  intros x Hx Hn. destruct Hx as (o & b0 & n & Hin3 & Hx).
  assert (HxG : inG TG.G_HARNESS_B x).
  { unfold inG. apply Exists_exists. exists (b0, n).
    split; [exact (TMAP_B_in_G o b0 n Hin3) | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transportb_segs_low _ x HGX HxG) as Hl. unfold kLowMemEnd in Hl.
  apply KR; [lia | unfold SRXB_RXIGN, SRX_S in *; cbn [Z.of_nat Pos.of_succ_nat] in Hn; lia]. }
(* what the call kept, at the cut's memory *)
assert (KG : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (ms_mem ms) (spZ regs - SRX_STK) (spZ regs)
  (srx_wr b)).
{ apply (dk_kept_nfz_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2
    (ms_mem ms) (spZ regs - SRX_STK) (spZ regs) SRX_CID pos F (flag_addr lyc SRX_CID pos) (srx_wr b)
    (fun x => SRXB_RXIGN <= x < SRXB_RXIGN + 8) HGX HARc HAR2 Hfrs Hbl ELF EF eq_refl FFL ltac:(lia) ltac:(lia));
    [| exact HK | exact KR | exact GA].
  intros a Ha. right; right. apply sbi_inG. cbv beta in Ha. unfold SRXB_RXIGN, TW.SZ_g_s in *. lia. }
(* the thirteen saved words and the frame's last word lie outside G *)
assert (HSo : forall o, In o SRXB_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold SRXB_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
assert (HSV : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) (ms_mem ms)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SRXB_SAVED).
{ rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
  pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi.
  apply KR; [lia | unfold SRXB_RXIGN, SRX_S, TB_g_s in *; lia]. }
assert (HFL : rdword (aview segs (w_H W2) (ms_mem ms)) (F + SRXB_FBYTES - 8) = Some (flag_addr lyc SRX_CID pos)).
{ rewrite <- HFLw. apply rdword_ext. intros i Hi. unfold SRXB_FBYTES in *.
  apply KR; [lia|]. intros Hx.
  apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 SRX_CID pos (F + 128 - 8 + i) HAR2 Hin);
    [try (unfold in_zr, frame_rng; cbn [fst snd]); rewrite ?EFA, ?srxb_fbytes_eq; unfold SRXB_FBYTES; lia|].
  apply trans_g_img. apply sbi_inG. unfold SRXB_RXIGN, TW.SZ_g_s in *. lia. }
assert (CUR : srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 (ms_mem ms) md1 e)
  by exact (conj HJ1 (conj He (conj Hfrs (conj Hperm (conj ELF (conj Hmo (conj KG (conj HSV HFL)))))))).
(* the registers the release reads *)
pmkst HS.
assert (Y2 : YK11.getr (ms_regs ms) 2 = w64 sp1) by sbi_keep HS E5lo EE 2%nat (2%bv : bv 5) R2.
assert (Y3 : YK11.getr (ms_regs ms) 3 = YK11.getr regs 3) by sbi_keep HS E5lo EE 3%nat (3%bv : bv 5) R3.
assert (Y4 : YK11.getr (ms_regs ms) 4 = YK11.getr regs 4) by sbi_keep HS E5lo EE 4%nat (4%bv : bv 5) R4.
assert (Y8 : YK11.getr (ms_regs ms) 8 = w64 (spZ regs)) by sbi_keep HS E5lo EE 8%nat (8%bv : bv 5) R8.
assert (Y9 : YK11.getr (ms_regs ms) 9 = w64 sp1) by sbi_keep HS E5lo EE 9%nat (9%bv : bv 5) R9.
assert (Y18 : YK11.getr (ms_regs ms) 18 = w64 F) by sbi_keep HS E5lo EE 18%nat (18%bv : bv 5) R18.
assert (Y19 : YK11.getr (ms_regs ms) 19 = w64 now) by sbi_keep HS E5lo EE 19%nat (19%bv : bv 5) R19.
assert (Y20 : YK11.getr (ms_regs ms) 20 = w64 SRX_S) by sbi_keep HS E5lo EE 20%nat (20%bv : bv 5) R20.
assert (Y25 : YK11.getr (ms_regs ms) 25 = w64 (SHADOW_OFF + F / 8))
  by sbi_keep HS E5lo EE 25%nat (25%bv : bv 5) R25.
assert (Y26 : YK11.getr (ms_regs ms) 26 = w64 F) by sbi_keep HS E5lo EE 26%nat (26%bv : bv 5) R26.
assert (Y27 : YK11.getr (ms_regs ms) 27 = w64 SHADOW_OFF) by sbi_keep HS E5lo EE 27%nat (27%bv : bv 5) R27.
assert (Y21 : YK11.getr (ms_regs ms) 21 = w64 (SRX_S + 18152)) by sbi_keep HS E5lo EE 21%nat (21%bv : bv 5) R21.
assert (Y22 : YK11.getr (ms_regs ms) 22 = w64 (F + SRX_F)) by sbi_keep HS E5lo EE 22%nat (22%bv : bv 5) R22.
assert (Y10 : YK11.getr (ms_regs ms) 10 = w64 r) by sbi_keep HS E5lo EE 10%nat (10%bv : bv 5) R10.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_REL)) mm rom) mdx) Q) end.
apply (REL LAWS0 CALLS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F
  ly2 S2 W2 (ms_mem ms) md1 e (ms_regs ms) HFIX CUR).
- rewrite EBw'. exact TW5.
- rewrite EBw', (sbi_gfn Bx HLx). exact HGFx.
- exact (conj (conj (conj Y2 (conj Y3 (conj Y4 (conj Y8 (conj Y9 (conj Y18 (conj Y19 (conj Y20 (conj Y25
    (conj Y26 Y27)))))))))) (conj Y21 Y22)) Y10).
Qed.

End ign.

Theorem srxb_ign_ok : forall fx rc B MT, @srxb_ign_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@sbi_ign fx rc B MT). Qed.
