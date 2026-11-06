(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 283 of its 322 lines of code are new or changed and 1885 lines of the source are left out. *)
(* MonRel: Lemma mon_rel : mon_rel_stmt (lib/A/Prog/MonCut.v), the release piece of the image-A walk of maybe_online,
   offsets +0x290 .. +0x3b4 of the listing lib/A/Prog/DgnTransportList.v (fuzz_transport.asan 0x8b400 .. 0x8b524).

   What the code does. +0x290 `lui`/`addiw` a0 = 0x45e0360e and +0x298 `sd a0, 0(s7)`: the frame's first word
   (s7 = F); +0x29c `beqz s2`: s2 = F >= 4096, so the real-stack arm at +0x330 is never entered (the engine decides the
   branch from the atom fact of s2); +0x2a0 `li a0, -11` and 32 `sb a0, i(s6)`: the frame's 32 shadow bytes (s6 =
   SHADOW_OFF + F / 8) := 0xf5; +0x324 `ld a0, 248(s2)`: the flag pointer FL from the frame's last word; +0x328
   `sb zero, 0(a0)`: the flag byte, which releases the frame (lib/A/Prog/TransportGFrame.v gx_flag_store_pi);
   +0x32c `j +0x380`; +0x380 `addi sp, s0, -96`; the 11 reloads +0x384 .. +0x3ac of ra, s0, s1, s2 .. s9 from the
   words the prologue saved below the entry sp (MonCut.v MON_SAVED); +0x3b0 `addi sp, sp, 96`; +0x3b4 `ret`. s10 and
   s11 are not written (the cut carries their entry values).

   One run of the plain position-abstract engine (lib/A/Prog/PaSym.v sym_run_pi: no shadow token, so the writable
   shadow region is allowed) covers +0x290 .. +0x3b4 and stops at the `ret`, which lib/A/Prog/DgnTransportPaLib.v
   paj_ret_at takes.
   The symbolic state: the registers at +0x290 as atoms 0 .. 31, atom 32 the flag pointer FL, atoms 33 .. 43 the
   entry values of ra, s0, s1, s2 .. s9 (MON_SAVED, in its order); regions: the frame's first word (s7, written), its
   last word (s2, offset 248, read: FL), its 32 shadow bytes (s6, written), the flag byte (atom 32, written) and the
   11 saved words below s0 = the entry sp (read).

   The post: the caller's G journal after the flag store has own (the frame released: stack_free_state), as
   gx_flag_store_pi's continuation gives it. What the call kept is the cut's acall_kept_g carried over the run's
   writes (lib/A/Prog/TransportGFrame.v dk_kept_nf_gw: the run writes only the own frame's bytes, its shadow bytes and its
   flag byte, which TransportGFrame.v dkg_nf_sep_gw puts apart from the call's blocks, frames and image bytes and below
   the allocation ceiling). The world relation at Bw' is the cut's: no byte of G is written (TransportGFrame.v tw_kept_nf_g
   at TWorldA.v TMAP_A). The callee-saved registers are the 11 reloads, sp = s0 - 96 + 96 = the entry sp, and gp, tp,
   s10, s11 untouched; the state changed in st_fs only, so the meter bound is the cut's (mo_le_set_fs_r). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import notice_cg maybe_online_cg MonCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x290 and the run to the ret              *)
(* ------------------------------------------------------------------ *)

(* The `ret` of maybe_online. *)
Definition MON_RET : Z := AF_maybe_online + 0x3b4.

Definition rel_rg_hd : YP09.region := YP09.mkRegion (Some 23%nat) 0 8 0 8 [].
Definition rel_rg_fp : YP09.region :=
  YP09.mkRegion (Some 18%nat) 248 256 0 0 [YP09.mkChunk 248 (CVal 8 (SOff 32 0))].
Definition rel_rg_sh : YP09.region := YP09.mkRegion (Some 22%nat) 0 32 0 32 [].
Definition rel_rg_fl : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition rel_rg_sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-88) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 43 0))].
(* s2 = F is at least 4096 (decides the `beqz s2` at +0x29c) and 32-aligned. *)
Definition rel_facts : facts := mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition ss_rel : sstate :=
  mkSS MON_REL sr_atoms [rel_rg_hd; rel_rg_fp; rel_rg_sh; rel_rg_fl; rel_rg_sv] None rel_facts.
Definition REL_FUEL : N := 96.
Definition rel_ss_end : sstate := Eval vm_compute in fst (sym_runN_pi transport_tpi REL_FUEL ss_rel).
Definition rel_st_end : prun_status tsym := Eval vm_compute in snd (sym_runN_pi transport_tpi REL_FUEL ss_rel).
Lemma rel_run : sym_runN_pi transport_tpi REL_FUEL ss_rel = (rel_ss_end, rel_st_end).
Proof. vm_compute. reflexivity. Qed.
Lemma rel_stop : can_plain_stop rel_st_end.
Proof. exact I. Qed.
Lemma rel_end_pc : ss_pc rel_ss_end = MON_RET.
Proof. reflexivity. Qed.

(* The environment: the registers at +0x290, then FL, then the entry values of the saved registers. *)
Definition rel_extra (regs : bvmap 5 word) (FL : Z) : list word :=
  w64 FL :: map (fun o : Z * Z => YK11.getr regs (Z_to_bv 5 (snd o))) MON_SAVED.

(* The value of register r in the machine state of HS: its symbolic value, computed. *)
Ltac rel_regv HS :=
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

Definition rel_E (regs2 regs : bvmap 5 word) (FL : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs2 (rel_extra regs FL)).

Lemma rel_ew_reg : forall regs2 regs FL n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (rel_E regs2 regs FL) n = YK11.getr regs2 r.
Proof. intros regs2 regs FL n r Hn. unfold rel_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma rel_ew_x : forall regs2 regs FL j, (j < 12)%nat ->
  ew (rel_E regs2 regs FL) (32 + j) = nth j (rel_extra regs FL) (Z_to_bv 64 0).
Proof. intros regs2 regs FL j Hj. unfold rel_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* The symbolic state at +0x290 holds of the machine state there. *)
Lemma rel_entry : forall (W : world segs) (regs2 regs : bvmap 5 word) mem (F FL SP : Z),
  YK11.getr regs2 8 = w64 SP -> YK11.getr regs2 18 = w64 F ->
  YK11.getr regs2 22 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs2 23 = w64 F ->
  4096 <= F -> F mod 32 = 0 -> F + 256 <= alloc_ceiling -> in_app F 256 ->
  4096 <= FL < alloc_ceiling -> (FL < F \/ F + 256 <= FL) ->
  (FL < SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 32 <= FL) ->
  alloc_ceiling <= SP - 88 -> SP <= 2 ^ 47 ->
  (forall a, F <= a < F + 8 -> apresent (w_H W) mem a) ->
  (forall i, 0 <= i < 32 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  apresent (w_H W) mem FL ->
  rdword (aview segs (w_H W) mem) (F + 248) = Some FL ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem) (SP - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) MON_SAVED ->
  st_ok_pi segs VAL (rel_E regs2 regs FL) ss_rel
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + MON_REL)) mem (YK11.seg_rom segs))).
Proof.
intros W regs2 regs mem F FL SP R8 R18 R22 R23 HF0 HF32 HFc HFapp HFL HFLF HFLS HSP HSP47
  Hpf Hpsh HpFL HFLw Hsaved.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF8 : F mod 8 = 0)
  by (pose proof (Z.div_mod F 32 ltac:(lia)) as D32; replace F with (F / 32 * 4 * 8) by lia; apply Z_mod_mult).
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. rewrite HF8, Z.add_0_r in D8.
set (E := rel_E regs2 regs FL).
assert (U8 : bv_unsigned (ew E 8) = SP)
  by (unfold E; rewrite (rel_ew_reg regs2 regs FL 8 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF + F / 8)
  by (unfold E; rewrite (rel_ew_reg regs2 regs FL 22 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (E18 : ew E 18 = w64 F) by (unfold E; rewrite (rel_ew_reg regs2 regs FL 18 18%bv eq_refl); exact R18).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = F)
  by (unfold E; rewrite (rel_ew_reg regs2 regs FL 23 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (rel_ew_x regs2 regs FL 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
unfold MON_SAVED in Hsaved.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [?Sv H] end.
cbn [fst snd] in *.
rewrite restrict_mkst_fx. unfold ss_rel.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks rel_rg_hd rel_rg_fp rel_rg_sh
      rel_rg_fl rel_rg_sv base_val];
    rewrite ?U8, ?U18, ?U22, ?U23, ?U32.
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
  unfold extent_of_region, rel_rg_hd, rel_rg_fp, rel_rg_sh, rel_rg_fl, rel_rg_sv.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U8, U18, U22, U23, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat split; first [exact I | lia].
- unfold rel_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18.
  change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma mon_rel : @mon_rel_stmt fx rc B MT.
Proof.
unfold mon_rel_stmt, mon_rel_at.
intros LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TF Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 e
  regs2 HFIX HREL HREGS.
destruct LAWS0 as (HSM & HCELLS & HMCELLS & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
destruct HFIX as (HJ0 & Hret & Hra & Hgp & Htp & Ha0 & Hsp16 & Hstk & Hsp0 & Htw0 & Hgf0 & Hm & Htf & Hrom & Hap &
  Hcnt & Hnev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
destruct HREL as ((HJ1 & He & Hfrs & Hperm & ELF & Hmo & HK & Hsaved & HFLw) & Htw2 & Hgf2).
destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R22 & R23 & R26 & R27).
unfold MON_FBYTES in HFc, HFapp, HFLw.
replace (F + 256 - 8) with (F + 248) in HFLw by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the call's journal: its AR and its stack window *)
pose proof HJ0 as (_ & _ & (memS0 & HJ0i & _) & _).
rewrite !Z.add_0_r in HJ0i.
pose proof HJ0i as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil0 & Hslo0 & Hshi0 & H47 & _).
clear HJ0i memS0.
(* the cut's journal: its AR *)
pose proof HJ1 as (_ & _ & (memS1 & HJ1i & _) & _).
pose proof HJ1i as (HAR2 & _).
clear HJ1i memS1.
assert (HBS : 112 <= MAYBEON_STK)
  by (pose proof (Z.le_max_l ESTACK NOTICE_STK); unfold MAYBEON_STK, MAYBEON_FRAME, MAYBEON_ALIGN, ESTACK in *; lia).
assert (HSPc : alloc_ceiling <= spZ regs - MAYBEON_STK) by lia.
assert (HSP47 : spZ regs <= 2 ^ 47) by lia.
assert (HF32 : F mod 32 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with (F / 64 * 2 * 32) by lia. apply Z_mod_mult. }
(* the frame at the cut *)
assert (Hin : In (MAYBEON_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly2 MAYBEON_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite ELF; reflexivity).
assert (EFL : flag_addr ly2 MAYBEON_CID pos = flag_addr lyc MAYBEON_CID pos)
  by (unfold flag_addr; rewrite ELF; reflexivity).
rewrite <- EFL in HFLw.
destruct (al_frames _ _ LAWS _ _ _ _ _ MAYBEON_CID pos HAR2 Hin) as (_ & _ & HFb & HFsh).
destruct (FFL ly2 S2 W2 mem2 md2 MAYBEON_CID pos HAR2 Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLc)).
set (FL := flag_addr ly2 MAYBEON_CID pos) in *.
change (fs_frame_bytes MAYBEON_CID / 8) with 32 in HFsh.
change (fs_frame_bytes MAYBEON_CID) with 256 in HFb.
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
pose proof (rel_entry W2 regs2 regs mem2 F FL (spZ regs) R8 R18 R22 R23 HF0 HF32 HFc HFapp
  ltac:(lia) HFLF HFLS ltac:(lia) HSP47
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFsh i Hi)))
  HFLp HFLw Hsaved) as HS.
set (E := rel_E regs2 regs FL) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, rel_E; apply Eimg_env).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF + F / 8).
{ pose proof (Z.div_lt_upper_bound F 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
  unfold E; rewrite (rel_ew_reg regs2 regs _ 22 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small;
  unfold SHADOW_OFF; lia. }
assert (U18 : bv_unsigned (ew E 18) = F)
  by (unfold E; rewrite (rel_ew_reg regs2 regs _ 18 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = F)
  by (unfold E; rewrite (rel_ew_reg regs2 regs _ 23 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 FL) by exact (rel_ew_x regs2 regs _ 0 ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
(* each byte the run may write is a byte of the own frame, of its shadow, or its flag byte *)
assert (HWIN : forall b wlo whi x, In (b, wlo, whi) (windows (ss_mem ss_rel)) ->
    base_val E b + wlo <= x < base_val E b + whi -> dkg_nf MAYBEON_CID F FL x).
{ intros b wlo whi x Hw Hx.
  lazymatch type of Hw with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hw end.
  cbn [In] in Hw. unfold dkg_nf. change (fs_frame_bytes MAYBEON_CID) with 256. change (256 / 8) with 32.
  destruct Hw as [Hw | [Hw | [Hw | [Hw | [Hw | []]]]]]; injection Hw as <- <- <-; cbn [base_val] in Hx;
    rewrite ?U18, ?U22, ?U23, ?U32 in Hx; lia. }
(* the own frame (its bytes, its shadow bytes, its flag byte) holds no image byte *)
assert (HBL : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; exact (Permutation_in _ (Permutation_sym Hperm) Hb)).
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 MAYBEON_CID pos F FL HAR2 Hfrs
  HBL ELF EF EFL FFL) as (_ & N2 & _ & _).
(* +0x290 .. +0x3b4 in one run, the flag store at +0x328 releasing the frame. *)
refine (gx_flag_store_pi (SK := tfib_sink_head) B LAWS ASF FFL TG.G_HARNESS W2 REL_FUEL E ss_rel rel_ss_end
  rel_st_end (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + MON_REL)) mem2 (YK11.seg_rom segs))
  STK sp0 FP ly S W0 mem0 md0 own ly2 S2 md2 (k + e) MAYBEON_CID pos _ HEI HS rel_run rel_stop HJ1 _ _ _ _).
- unfold MAYBEON_CID. lia.
- (* the run writes the frame's first word, its shadow and the flag byte *)
  intros a (rg & Hinr & Ha). unfold ss_rel in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<- | [<- | [<- | [<- | [<- | []]]]]];
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi rel_rg_hd rel_rg_fp rel_rg_sh rel_rg_fl rel_rg_sv] in Ha;
    rewrite ?U18, ?U22, ?U23, ?U32 in Ha.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists MAYBEON_CID, pos.
    split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes MAYBEON_CID) with 256. lia.
  + lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists MAYBEON_CID, pos.
    split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes MAYBEON_CID / 8) with 32.
    rewrite ESH. lia.
  + right. change (flag_addr ly2 MAYBEON_CID pos) with FL. lia.
  + lia.
- (* the flag byte is 0 after the run *)
  intros msr HSr.
  lazymatch goal with |- _ = Some _ =>
    let rr := eval vm_compute in (nth_error (ss_mem rel_ss_end) 3) in
    lazymatch rr with Some ?r3 =>
      pose proof (can_region_nth (segs := segs) _ _ msr 3 r3 HSr eq_refl) as HR3 end end.
  pose proof (can_field_of_region (segs := segs) E (ms_mem msr) 32 FL _ 0 1 0 1 0 1%N
    (SLit 0) 0 HR3 U32 ltac:(cbn [In]; auto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(cbn; lia)).
  lazymatch type of V with _ = Some (Z_to_bv 8 ?x) => replace x with 0 in V by (vm_compute; reflexivity) end.
  replace (FL + 0 + Z.of_nat 0) with FL in V by lia.
  exact V.
- (* the return *)
  intros ms2 mat2 HS2 HJ2 _ HFR HGR.
  set (md3 := with_vm_backing (m_vm_lazy md2) mat2 md2) in *. clearbody md3.
  eapply (paj_ret_at (L := transport_listing) (PL := PL_transport) (PI := PI_transport) W2 E rel_ss_end ms2 md3 _
    HS2 eq_refl ltac:(clear; vm_compute; reflexivity)).
  intros mat3.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat3 md3).
  pose proof (ajournal_gx_materialize segs B LAWS transport_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ2)
    as HJ3.
  fold md4 in HJ3. clearbody md4.
  (* the bytes the run changed are the own frame's *)
  pose proof (kept_of_frame (segs := segs) E (ss_mem ss_rel) (w_H W2) mem2 (ms_mem ms2) (dkg_nf MAYBEON_CID F FL)
    HFR HWIN) as KEEP.
  (* the registers at the ret *)
  assert (R1e : YK11.getr (ms_regs ms2) 1 = YK11.getr regs 1).
  { rel_regv HS2. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (HP : aregs_preserved regs (ms_regs ms2)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      rel_regv HS2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    all: first
      [ reflexivity
      | transitivity (YK11.getr regs2 3); [apply rel_ew_reg; reflexivity | exact R3]
      | transitivity (YK11.getr regs2 4); [apply rel_ew_reg; reflexivity | exact R4]
      | transitivity (YK11.getr regs2 26); [apply rel_ew_reg; reflexivity | exact R26]
      | transitivity (YK11.getr regs2 27); [apply rel_ew_reg; reflexivity | exact R27]
      | transitivity (YK11.getr regs2 8); [apply rel_ew_reg; reflexivity|];
        rewrite R8; unfold w64, spZ; apply Z_to_bv_bv_unsigned ]. }
  assert (Hpc : v_jalr (YK11.getr (ms_regs ms2) 1) 0 = YK11.getr regs 1) by (rewrite R1e; exact Hret).
  assert (Eab' : ablocks B ly2 (stack_free_state MAYBEON_CID pos S2) = ablocks B ly2 S2)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  unfold transport_maybeon_post, transport_cg_post.
  exists ly2, (stack_free_state MAYBEON_CID pos S2), (ms_regs ms2), (ms_mem ms2), md4, e.
  split; [rewrite Hpc; reflexivity|].
  split; [exact He|].
  split; [exact HJ3|].
  split; [exact HP|].
  split; [exact (can_sf_frames MAYBEON_CID pos S2 (frames Sc) Hfrs)|].
  split; [rewrite Eab'; exact Hperm|].
  split.
  { exact (dk_kept_nf_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc ly2 S2 W2 mem2 md2
      (ms_mem ms2) (spZ regs - MAYBEON_STK) (spZ regs) MAYBEON_CID pos F FL (maybeon_wr Bw) HARc HAR2 Hfrs HBL ELF EF
      EFL FFL HK KEEP (fun a Ha => apresent_grows _ _ _ a HGR Ha)). }
  split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact Hmo|].
  split; [|exact Hgf2].
  exact (tw_kept_nf_g segs B transport_segs_low TMAP_A TG.G_HARNESS W2 mem2 (ms_mem ms2) Bw' MAYBEON_CID F FL
    TMAP_A_in_G HGX N2 KEEP Htw2).
Qed.

End rel.
