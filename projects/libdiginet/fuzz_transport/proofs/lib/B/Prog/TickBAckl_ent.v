(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module paths, module names and numbers changed; 335 of its 408 lines of code are new or changed and 1137 lines of the source are left out. *)
(* TickBAckl_ent: the symbolic states of the three runs of the ack-lost piece of diginet_session_tick's image-B walk
   (lib/B/Prog/TickBAckl.v) and their entry lemmas, from the facts at each run's first instruction. Image B's twin of
   image A's TickAckl_ent.v: image B's listing (lib/B/Prog/DgnTransportBList.v), g_s at TWorldB.v TB_g_s, the notice
   at frame + 32 (its shadow bytes 4 .. 12; image A: frame + 256, bytes 32 .. 40), the state in s9.
   rule 24: proves no function (lemmas for a piece of a walk; the walk is composed at TickCutB.v tick_holds_of).
   - run 1, +0x488 .. +0x4f0 (the cut tick_ackl_at, up to `jal __asan_memset`): the check of s + 212 through t1, the
     saves of t2 and a7 at s1 + 24 / s1 + 32, the store of 0 at s + 212, the checked load / store of stats.ack_lost
     at s + 18240, s10 = frame + 32, the frame's shadow bytes 4 .. 12, the memset's arguments;
   - run 2, +0x4f4 .. +0x558 (after the memset, up to `jalr a2`): kind and state (s9) at p, the checked load of the
     counter at s + 1744 and its store at p + 64, the retry (the saved t2) at p + 68, the checked loads of g_s.notify
     and g_s.notify_ctx, a1 = p;
   - run 3, +0x55c .. +0x590 (after notice, to the tail cut): the frame's shadow bytes 4 .. 12, a7, t0 and t1 loaded
     back from s1 + 32, s1 + 48 and s1 + 40, `j` to +0x5c0.
   Each check reads a shadow byte of g_s's payload, 0 by trans_tick_cells (DgnTransportBCg.v decode_zshadow_rd), held
   as a region of literal zeros at its numeral address; s, the shadow base, t1 and a7 are pinned to their values. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k YE2y AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
diginet_session_tick_cg TickCutB TickBKit TickBAckl_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The shadow bytes the checks read, at their numeral addresses: those of s + 212 (through t1), s + 18240,
   s + 1744, s + 96 and s + 104 (the last two adjacent). *)
Definition TBA_SH212 : Z := 2148220642.
Definition TBA_SHAL : Z := 2148222896.
Definition TBA_SHC : Z := 2148220834.
Definition TBA_SHN : Z := 2148220628.
Lemma tba_sh_eq :
  TBA_SH212 = SHADOW_OFF + (TICK_S + 212) / 8 /\ TBA_SH212 = FCells.shadow_addr (TICK_S + 208) /\
  TBA_SHAL = FCells.shadow_addr (TICK_S + 18240) /\ TBA_SHC = FCells.shadow_addr (TICK_S + 1744) /\
  TBA_SHN = FCells.shadow_addr (TICK_S + 96) /\ TBA_SHN + 1 = FCells.shadow_addr (TICK_S + 104).
Proof. repeat split; reflexivity. Qed.
(* The run's pcs: the return of the memset (+0x4f4) and of notice (+0x55c), as offsets of the listing. *)
Definition TBA_C2 : Z := TICK_ACKL + 0x6c.
Definition TBA_C3 : Z := TICK_ACKL + 0xd4.

Definition TBA_B0 : Z * Z := (0, 0).
Definition TBA_Bx : sv := SLit 0.

(* run 1 *)
Definition TBA1_sh : YP09.region := YP09.mkRegion (Some 19%nat) 4 13 4 13 [].
Definition TBA1_win : YP09.region := YP09.mkRegion (Some 9%nat) 24 40 24 40 [].
Definition TBA1_inf : YP09.region :=
  YP09.mkRegion None (TICK_S + 212) (TICK_S + 216) (TICK_S + 212) (TICK_S + 216) [].
Definition TBA1_al : YP09.region :=
  YP09.mkRegion None (TICK_S + 18240) (TICK_S + 18248) (TICK_S + 18240) (TICK_S + 18248)
    [YP09.mkChunk (TICK_S + 18240) (YP09.CVal 8 (SOff 32 0))].
Definition TBA1_sh1 : YP09.region :=
  YP09.mkRegion None TBA_SH212 (TBA_SH212 + 1) 0 0 [YP09.mkChunk TBA_SH212 (YP09.CVal 1 (SLit 0))].
Definition TBA1_sh2 : YP09.region :=
  YP09.mkRegion None TBA_SHAL (TBA_SHAL + 1) 0 0 [YP09.mkChunk TBA_SHAL (YP09.CVal 1 (SLit 0))].
Definition TBA_RS1 : smem := [TBA1_sh; TBA1_win; TBA1_inf; TBA1_al; TBA1_sh1; TBA1_sh2].
Definition TBA_FACTS1 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] [] [].
Definition TBA_REGS1 : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 6) (SLit (SHADOW_OFF + (TICK_S + 212) / 8)))
    (Z_to_bv 5 17) (SLit (TICK_S + 18144))) (Z_to_bv 5 20) (SLit TICK_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_tba1 : sstate := mkSS TICK_ACKL TBA_REGS1 TBA_RS1 None TBA_FACTS1.

(* run 2: p = frame + 32 is 32-aligned (frame mod 64 = 0). *)
Definition TBA2_p0 : YP09.region := YP09.mkRegion (Some 26%nat) 0 8 0 8 [].
Definition TBA2_p64 : YP09.region := YP09.mkRegion (Some 26%nat) 64 72 64 70 [].
Definition TBA2_win : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (YP09.CVal 8 (SOff 33 0))].
Definition TBA2_cnt : YP09.region :=
  YP09.mkRegion None (TICK_S + 1744) (TICK_S + 1748) 0 0 [YP09.mkChunk (TICK_S + 1744) (YP09.CVal 4 (SOff 32 0))].
Definition TBA2_nt : YP09.region :=
  YP09.mkRegion None (TICK_S + 96) (TICK_S + 112) 0 0
    [YP09.mkChunk (TICK_S + 96) (YP09.CVal 8 (SOff 34 0)); YP09.mkChunk (TICK_S + 104) (YP09.CVal 8 (SOff 35 0))].
Definition TBA2_shc : YP09.region :=
  YP09.mkRegion None TBA_SHC (TBA_SHC + 1) 0 0 [YP09.mkChunk TBA_SHC (YP09.CVal 1 (SLit 0))].
Definition TBA2_shn : YP09.region :=
  YP09.mkRegion None TBA_SHN (TBA_SHN + 2) 0 0
    [YP09.mkChunk TBA_SHN (YP09.CVal 1 (SLit 0)); YP09.mkChunk (TBA_SHN + 1) (YP09.CVal 1 (SLit 0))].
Definition TBA_RS2 : smem := [TBA2_p0; TBA2_p64; TBA2_win; TBA2_cnt; TBA2_nt; TBA2_shc; TBA2_shn].
Definition TBA_FACTS2 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (26%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition TBA_REGS2 : list sv :=
  sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit TICK_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF).
Definition ss_tba2 : sstate := mkSS TBA_C2 TBA_REGS2 TBA_RS2 None TBA_FACTS2.

(* run 3 *)
Definition TBA3_sh : YP09.region := YP09.mkRegion (Some 19%nat) 4 13 4 13 [].
Definition TBA3_win : YP09.region :=
  YP09.mkRegion (Some 9%nat) 32 56 0 0
    [YP09.mkChunk 32 (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk 40 (YP09.CVal 8 (SOff 33 0));
     YP09.mkChunk 48 (YP09.CVal 8 (SOff 34 0))].
Definition TBA_RS3 : smem := [TBA3_sh; TBA3_win].
Definition TBA_FACTS3 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] [] [].
Definition ss_tba3 : sstate := mkSS TBA_C3 sr_atoms TBA_RS3 None TBA_FACTS3.

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* A shadow byte of g_s's payload is 0 at every AR state (trans_tick_cells). *)
Lemma tba_zsh : forall ly S (W : world segs) mem md a,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  a mod 8 = 0 -> TICK_S <= a -> a + 8 <= TICK_S + TW.SZ_g_s ->
  val_mem segs (mrestrict (w_H W) mem) (FCells.shadow_addr a) 1 0.
Proof.
  intros ly S W mem md a HSC HAR H8 H1 H2. apply YE2y.val_mem1_of_aview.
  exact (decode_zshadow_rd B ly S W mem md TICK_S (TICK_S + TW.SZ_g_s) a HAR H8 H1 H2 HSC).
Qed.

(* A frame address F and its shadow address, from F mod 64 = 0. *)
Lemma tba_f8 : forall F, 0 <= F -> F mod 64 = 0 -> F / 8 = 8 * (F / 64) /\ F = 64 * (F / 64).
Proof.
  intros F HF0 HF64. pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  split; [|exact DF].
  rewrite DF at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.div_mul. lia.
Qed.

(* ---- run 1 ---- *)

Definition tba_E1 (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 18240) 8)]).

Lemma tba_entry1_0 : forall ly S (W : world segs) regs mem md Bw F sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 9 = w64 sp1 ->
  4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 ->
  (F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F) ->
  2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall a, sp1 + 24 <= a < sp1 + 40 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (tba_E1 regs Bw) (mkSS TICK_ACKL sr_atoms TBA_RS1 None TBA_FACTS1)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_ACKL)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bw F sp1 HSC HAR Htw R19 R9 HF0 HF64 HFc HFG Hs0 Hs1 Hs32 Hpw Hpsh.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (tba_f8 F ltac:(lia) HF64) as (HF8 & DF).
  set (E := tba_E1 regs Bw).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, tba_E1; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
    by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 18240) 8))
    by (unfold E, tba_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  pose proof (TWL.u_at_range Bw (TW.OFF_g_s + 18240) 8) as R32.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32.
  assert (D32 : sv_denot E (SOff 32 0) = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 18240) 8))
    by (cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by exact R32; reflexivity).
  assert (Hg : forall o, 0 <= o < TW.SZ_g_s -> inG TG.G_HARNESS_B (TICK_S + o))
    by (intros o Ho; apply (tkb_row _ _ _ _ TMAP_B_g_s); unfold TICK_S, TB_g_s; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TBA1_sh TBA1_win TBA1_inf TBA1_al
        TBA1_sh1 TBA1_sh2 base_val]; rewrite ?U19, ?U9.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpw. lia.
    + split; [unfold TICK_S, TB_g_s; lia|]. split; [unfold TICK_S, TB_g_s; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (0 + o) G_HARNESS_B_rw).
      replace (0 + o) with (TICK_S + (o - TICK_S)) by lia. apply Hg. unfold TW.SZ_g_s. lia.
    + split; [unfold TICK_S, TB_g_s; lia|]. split; [unfold TICK_S, TB_g_s; lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (0 + o) G_HARNESS_B_rw).
        replace (0 + o) with (TICK_S + (o - TICK_S)) by lia. apply Hg. unfold TW.SZ_g_s. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ 0 (TICK_S + 18240) 8 (SOff 32 0) (TW.u_at Bw (TW.OFF_g_s + 18240) 8));
          [exact D32 | exact R32 | unfold TICK_S, TB_g_s; lia |].
        replace (0 + (TICK_S + 18240)) with (TB_g_s + 18240) by (unfold TICK_S; lia).
        exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 18240 8 TMAP_B_ok Htw TMAP_B_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold TBA_SH212; lia|]. split; [unfold TBA_SH212; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 TBA_SH212 1 (SLit 0) 0); [reflexivity | lia | unfold TBA_SH212; lia |].
      rewrite Z.add_0_l. rewrite (proj1 (proj2 tba_sh_eq)).
      apply (tba_zsh ly S W mem md _ HSC HAR); [reflexivity | lia | unfold TW.SZ_g_s; lia].
    + split; [unfold TBA_SHAL; lia|]. split; [unfold TBA_SHAL; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 TBA_SHAL 1 (SLit 0) 0); [reflexivity | lia | unfold TBA_SHAL; lia |].
      rewrite Z.add_0_l. rewrite (proj1 (proj2 (proj2 tba_sh_eq))).
      apply (tba_zsh ly S W mem md _ HSC HAR); [reflexivity | lia | unfold TW.SZ_g_s; lia].
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, TBA_RS1, TBA1_sh, TBA1_win, TBA1_inf, TBA1_al, TBA1_sh1, TBA1_sh2.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold TBA_SH212, TBA_SHAL, SHADOW_OFF, TICK_S, TB_g_s, TW.SZ_g_s in *.
    rewrite HF8. repeat split; first [exact I | lia].
  - unfold TBA_FACTS1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19, U9.
    change (2 ^ 3) with 8. change (2 ^ 5) with 32.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma tba_entry1 : forall ly S (W : world segs) regs mem md Bw F sp1,
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 9 = w64 sp1 ->
  YK11.getr regs 6 = w64 (SHADOW_OFF + (TICK_S + 212) / 8) -> YK11.getr regs 17 = w64 (TICK_S + 18144) ->
  YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 ->
  (F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F) ->
  2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall a, sp1 + 24 <= a < sp1 + 40 -> apresent (w_H W) mem a) ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (tba_E1 regs Bw) ss_tba1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TICK_ACKL)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bw F sp1 HSC HAR Htw R19 R9 R6 R17 R20 R24 HF0 HF64 HFc HFG Hs0 Hs1 Hs32 Hpw Hpsh.
  rewrite restrict_mkst_fx.
  pose proof (tba_entry1_0 ly S W regs mem md Bw F sp1 HSC HAR Htw R19 R9 HF0 HF64 HFc HFG Hs0 Hs1 Hs32 Hpw Hpsh)
    as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 6) (SHADOW_OFF + (TICK_S + 212) / 8) H0 R6 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 17) (TICK_S + 18144) H1 R17 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H2 R20 eq_refl) as H3.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H3 R24 eq_refl) as H4.
  exact H4.
Qed.

(* ---- run 2 ---- *)

(* The valuation of run 2: the registers after the memset, then the counter (4 bytes at s + 1744), the saved t2,
   g_s.notify and g_s.notify_ctx, the last three of the world Bx. *)
Definition tba_E2 (regs : bvmap 5 word) (t2 : word) (Bx : list byte) : env :=
  Eimg (PI := PI_transportb)
    (Ereg regs [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 1744) 4); t2; Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 96) 8);
                Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 104) 8)]).

Lemma tba_entry2_0 : forall ly S (W : world segs) regs mem md Bx F sp1 (t2 : word),
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bx ->
  YK11.getr regs 26 = w64 (F + 32) -> YK11.getr regs 9 = w64 sp1 ->
  4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 -> in_app F 2048 ->
  (F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F) ->
  2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 -> F + 2048 <= sp1 ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 24) 8 (bv_unsigned t2) ->
  (forall a, F + 32 <= a < F + 104 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (tba_E2 regs t2 Bx) (mkSS TBA_C2 sr_atoms TBA_RS2 None TBA_FACTS2)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TBA_C2)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bx F sp1 t2 HSC HAR Htw R26 R9 HF0 HF64 HFc HFapp HFG Hs0 Hs1 Hs32 HFs Vt2 Hpp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (tba_f8 F ltac:(lia) HF64) as (HF8 & DF).
  set (E := tba_E2 regs t2 Bx).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, tba_E2; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U26 : bv_unsigned (ew E 26) = F + 32)
    by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
      nth j [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 1744) 4); t2; Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 96) 8);
             Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 104) 8)] (Z_to_bv 64 0))
    by (intros j Hj; unfold E, tba_E2; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  cbn [Nat.add nth] in E32, E33, E34, E35.
  pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 1744) 4) as R32.
  pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 96) 8) as R34.
  pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 104) 8) as R35.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R32.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R34, R35.
  pose proof (bv_unsigned_in_range 64 t2) as R33. unfold bv_modulus in R33. change (2 ^ Z.of_N 64) with (2 ^ 64) in R33.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (Hrd : forall k (m : nat), 0 <= k -> k + Z.of_nat m <= TW.SZ_g_s ->
    val_mem segs (mrestrict (w_H W) mem) (TICK_S + k) m (TW.u_at Bx (TW.OFF_g_s + k) m)).
  { intros k m Hk Hkm. replace (TICK_S + k) with (TB_g_s + k) by (unfold TICK_S; lia).
    exact (tw_read_val segs _ TMAP_B Bx TW.OFF_g_s TB_g_s TW.SZ_g_s k m TMAP_B_ok Htw TMAP_B_g_s Hk Hkm). }
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TBA2_p0 TBA2_p64 TBA2_win TBA2_cnt
        TBA2_nt TBA2_shc TBA2_shn base_val]; rewrite ?U26, ?U9.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpp. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpp. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 24 8 (SOff 33 0) (bv_unsigned t2));
        [apply DEN; [rewrite E33; symmetry; apply Z_to_bv_bv_unsigned | exact R33] | exact R33 | lia | exact Vt2].
    + split; [unfold TICK_S, TB_g_s; lia|]. split; [unfold TICK_S, TB_g_s; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 (TICK_S + 1744) 4 (SOff 32 0) (TW.u_at Bx (TW.OFF_g_s + 1744) 4));
        [apply DEN; [exact E32 | lia] | exact R32 | unfold TICK_S, TB_g_s; lia |].
      rewrite Z.add_0_l. apply Hrd; unfold TW.SZ_g_s; lia.
    + split; [unfold TICK_S, TB_g_s; lia|]. split; [unfold TICK_S, TB_g_s; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 96) 8 (SOff 34 0) (TW.u_at Bx (TW.OFF_g_s + 96) 8));
          [apply DEN; [exact E34 | exact R34] | exact R34 | unfold TICK_S, TB_g_s; lia |].
        rewrite Z.add_0_l. apply Hrd; unfold TW.SZ_g_s; lia.
      * apply (chunk_ok_val segs E _ 0 (TICK_S + 104) 8 (SOff 35 0) (TW.u_at Bx (TW.OFF_g_s + 104) 8));
          [apply DEN; [exact E35 | exact R35] | exact R35 | unfold TICK_S, TB_g_s; lia |].
        rewrite Z.add_0_l. apply Hrd; unfold TW.SZ_g_s; lia.
    + split; [unfold TBA_SHC; lia|]. split; [unfold TBA_SHC; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 TBA_SHC 1 (SLit 0) 0); [reflexivity | lia | unfold TBA_SHC; lia |].
      rewrite Z.add_0_l. rewrite (proj1 (proj2 (proj2 (proj2 tba_sh_eq)))).
      apply (tba_zsh ly S W mem md _ HSC HAR); [reflexivity | lia | unfold TW.SZ_g_s; lia].
    + split; [unfold TBA_SHN; lia|]. split; [unfold TBA_SHN; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ 0 TBA_SHN 1 (SLit 0) 0); [reflexivity | lia | unfold TBA_SHN; lia |].
        rewrite Z.add_0_l. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 tba_sh_eq))))).
        apply (tba_zsh ly S W mem md _ HSC HAR); [reflexivity | lia | unfold TW.SZ_g_s; lia].
      * apply (chunk_ok_val segs E _ 0 (TBA_SHN + 1) 1 (SLit 0) 0); [reflexivity | lia | unfold TBA_SHN; lia |].
        rewrite Z.add_0_l. rewrite (proj2 (proj2 (proj2 (proj2 (proj2 tba_sh_eq))))).
        apply (tba_zsh ly S W mem md _ HSC HAR); [reflexivity | lia | unfold TW.SZ_g_s; lia].
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, TBA_RS2, TBA2_p0, TBA2_p64, TBA2_win, TBA2_cnt, TBA2_nt, TBA2_shc, TBA2_shn.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U26, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
    unfold TBA_SHC, TBA_SHN, SHADOW_OFF, TICK_S, TB_g_s, TW.SZ_g_s in *.
    repeat split; first [exact I | lia].
  - unfold TBA_FACTS2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U26, U9.
    change (2 ^ 5) with 32.
    assert (M32 : (F + 32) mod 32 = 0).
    { rewrite DF. replace (64 * (F / 64) + 32) with ((2 * (F / 64) + 1) * 32) by ring. apply Z.mod_mul. lia. }
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma tba_entry2 : forall ly S (W : world segs) regs mem md Bx F sp1 (t2 : word),
  trans_tick_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bx ->
  YK11.getr regs 26 = w64 (F + 32) -> YK11.getr regs 9 = w64 sp1 ->
  YK11.getr regs 20 = w64 TICK_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 -> in_app F 2048 ->
  (F + 2048 <= TICK_S \/ TICK_S + TW.SZ_g_s <= F) ->
  2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 -> F + 2048 <= sp1 ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 24) 8 (bv_unsigned t2) ->
  (forall a, F + 32 <= a < F + 104 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (tba_E2 regs t2 Bx) ss_tba2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TBA_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bx F sp1 t2 HSC HAR Htw R26 R9 R20 R24 HF0 HF64 HFc HFapp HFG Hs0 Hs1 Hs32 HFs Vt2 Hpp.
  rewrite restrict_mkst_fx.
  pose proof (tba_entry2_0 ly S W regs mem md Bx F sp1 t2 HSC HAR Htw R26 R9 HF0 HF64 HFc HFapp HFG Hs0 Hs1 Hs32 HFs
    Vt2 Hpp) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) TICK_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  exact H2.
Qed.

(* ---- run 3 ---- *)

Definition tba_E3 (regs : bvmap 5 word) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 (TICK_S + 18144); w64 TBA_SH212; w64 (TICK_S + 212)]).

Lemma tba_entry3 : forall (W : world segs) regs mem F sp1,
  YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 9 = w64 sp1 ->
  4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 ->
  2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall i, 4 <= i < 13 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 32) 8 (TICK_S + 18144) ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 40) 8 TBA_SH212 ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 48) 8 (TICK_S + 212) ->
  st_ok_pi segs VAL (tba_E3 regs) ss_tba3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + TBA_C3)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F sp1 R19 R9 HF0 HF64 HFc Hs0 Hs1 Hs32 Hpsh V32 V40 V48.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (tba_f8 F ltac:(lia) HF64) as (HF8 & DF).
  set (E := tba_E3 regs).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, tba_E3; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
    by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) =
      nth j [w64 (TICK_S + 18144); w64 TBA_SH212; w64 (TICK_S + 212)] (Z_to_bv 64 0))
    by (intros j Hj; unfold E, tba_E3; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34.
  cbn [Nat.add nth] in E32, E33, E34.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks TBA3_sh TBA3_win base_val];
      rewrite ?U19, ?U9.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ sp1 32 8 (SOff 32 0) (TICK_S + 18144));
          [apply DEN; [exact E32 | unfold TICK_S, TB_g_s; lia] | unfold TICK_S, TB_g_s; lia | lia | exact V32].
      * apply (chunk_ok_val segs E _ sp1 40 8 (SOff 33 0) TBA_SH212);
          [apply DEN; [exact E33 | unfold TBA_SH212; lia] | unfold TBA_SH212; lia | lia | exact V40].
      * apply (chunk_ok_val segs E _ sp1 48 8 (SOff 34 0) (TICK_S + 212));
          [apply DEN; [exact E34 | unfold TICK_S, TB_g_s; lia] | unfold TICK_S, TB_g_s; lia | lia | exact V48].
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, TBA_RS3, TBA3_sh, TBA3_win.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SHADOW_OFF in *. rewrite HF8. repeat split; first [exact I | lia].
  - unfold TBA_FACTS3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19, U9.
    change (2 ^ 3) with 8. change (2 ^ 5) with 32.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

End ent.
