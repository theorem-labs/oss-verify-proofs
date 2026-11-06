(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_set_resweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxSetResweep.v, with its module paths, module names and numbers changed; 174 of its 248 lines of code are new or changed and 208 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacHuntHeardAnything.v, with its module paths and module names changed; 119 of its 150 lines of code are new or changed and 217 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YE00 YC5d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81 YC1h.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoEntSeatStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition dsh_our : Z -> Z := dsh (fun o => match o with OOUR => true | _ => false end).
Definition pchunk8 (l : list (Z * sv)) : list YP09.chunk := map (fun kv => YP09.mkChunk (fst kv) (CVal 8 (snd kv))) l.
Definition ps_C2 : list YP09.chunk := pchunk8
  [(184, SOff AT_SH 30); (416, SOff AT_F 0); (352, SOff AT_F 240); (328, SOff AT_F 1664); (376, SOff AT_F 1728);
   (264, SOff AT_F 1792); (288, SOff AT_F 1856); (256, SOff AT_F 1920); (360, SOff AT_F 2000); (400, SOff AT_SH 0);
   (384, SOff AT_F 2160); (240, SOff AT_F 2624); (144, SOff AT_F 2960); (320, SOff AT_F 2064)].
Definition ps_C4 : list YP09.chunk := ps_C2 ++ pchunk8 [(40, SOff AT_F 0)].
Definition ps_C5 : list YP09.chunk := ps_C4 ++ pchunk8 [(272, SOff AT_F 32); (32, SOff AT_F 0)].
Definition dfhdr3 : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SLit MAGIC_LIVE)); YP09.mkChunk 8 (CVal 8 (SOff (A_OBJ 2) 0));
   YP09.mkChunk 16 (CVal 8 (SOff (A_OBJ 3) 0))].
Definition p_regions (shf : Z -> Z) (acs : list YP09.chunk) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 472 acs;
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 DFRAME_SIZE dfhdr3;
   fshadow_region AT_SH DFRAME_CLASS 0 DFRAME_SH (dsh_chunks shf)].
Definition p_kregions (shf : Z -> Z) (acs fcs : list YP09.chunk) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 472 acs;
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 DFRAME_SIZE (dfhdr_chunks ++ fcs);
   fshadow_region AT_SH DFRAME_CLASS 0 DFRAME_SH (dsh_chunks shf);
   got_regionP; bcell_regionP 32].
Definition ss_p (pc : Z) (sr : list sv) (shf : Z -> Z) (acs fcs : list YP09.chunk) (extra : smem) (G : facts)
  : sstate := mkSS pc sr (p_kregions shf acs fcs ++ extra) None G.
Definition p_land_chk (shf : Z -> Z) (acs : list YP09.chunk) (rs : smem) : bool :=
  existsb (region_cover AT_STK (-104) 0 dsave_chunks) rs &&
  existsb (region_cover AT_A 0 472 acs) rs &&
  existsb (region_cover AT_F 0 (fs_frame_bytes DFRAME_CLASS) dfhdr_chunks) rs &&
  existsb (sh_region_ok shf) rs.

Definition POFF_C2 : Z := 0x504.
Definition POFF_C3 : Z := 0x5b4.
Definition POFF_C4 : Z := 0x728.
Definition POFF_C5 : Z := 0x78c.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Definition p_frame (cx : dcx) (shf : Z -> Z) (acs : list YP09.chunk) (W : world SEGS) (mem : word -> option byte) : Prop :=
  exists E : env, d_E cx E /\ Forall (region_ok SEGS E (rd W mem)) (p_regions shf acs) /\
  rdword (aview SEGS (w_H W) mem) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
Definition p_n3 (cx : dcx) : Z := Z.max 0 (c_n cx - 7).
Definition p_setup (cx : dcx) : Z := rdb (c_pl cx) 6.
Definition p_rbase (cx : dcx) (regs : bvmap 5 word) (B : asyms) : Prop :=
  spZ regs = d_A cx /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 8 = w64 (d_S cx) /\ getr regs 9 = w64 (d_A cx) /\ getr regs 18 = w64 SHADOW_OFF /\
  getr regs 20 = w64 (d_FB cx + 32) /\ getr regs 22 = w64 (d_obj cx OS) /\
  getr regs 24 = w64 (d_FB cx) /\ getr regs 25 = w64 (d_FB cx) /\ getr regs 26 = w64 (d_obj cx OOUR).
Definition p_rC2 (cx : dcx) (B : asyms) (regs : bvmap 5 word) : Prop :=
  p_rbase cx regs B /\ getr regs 21 = w64 (c_p cx) /\ getr regs 23 = w64 (c_n cx) /\
  getr regs 12 = w64 0 /\ getr regs 13 = w64 6 /\ getr regs 14 = w64 7.
Definition p_rC3 (cx : dcx) (B : asyms) (regs : bvmap 5 word) : Prop :=
  p_rbase cx regs B /\ getr regs 19 = w64 (p_setup cx) /\ getr regs 21 = w64 (d_cur cx (p_n3 cx)) /\
  getr regs 27 = w64 (p_n3 cx).
Definition p_rC4 (cx : dcx) (h : Z) (B : asyms) (regs : bvmap 5 word) : Prop :=
  p_rC3 cx B regs /\ getr regs 23 = w64 h.
Definition p_rC5 (cx : dcx) (h : Z) (B : asyms) (regs : bvmap 5 word) : Prop :=
  p_rbase cx regs B /\ getr regs 19 = w64 h /\ getr regs 21 = w64 (d_cur cx (p_n3 cx)) /\
  getr regs 27 = w64 (p_n3 cx).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Definition pro_C2 (cx : dcx) : world SEGS -> config -> Prop :=
  d_at B MT XM_LIB RLO RHI tfib_K cx POFF_C2 0 0 (fun regs ly3 S3 W3 mem3 md3 =>
    0 <= c_canary cx < 2 ^ 64 /\
    p_rC2 cx B regs /\ p_frame cx dsh_our ps_C2 W3 mem3 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)).
Definition pro_C3 (cx : dcx) : world SEGS -> config -> Prop :=
  d_at B MT XM_LIB RLO RHI tfib_K cx POFF_C3 0 0 (fun regs ly3 S3 W3 mem3 md3 =>
    0 <= c_canary cx < 2 ^ 64 /\
    p_rC3 cx B regs /\ p_frame cx dsh_our ps_C2 W3 mem3 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
    garr8 SEGS (rd W3 mem3) (d_obj cx OOUR) (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx)))).
Definition pro_C4 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  d_at B MT XM_LIB RLO RHI tfib_K cx POFF_C4 EV_PRO (ACC_PRO MT) (fun regs ly3 S3 W3 mem3 md3 =>
    0 <= c_canary cx < 2 ^ 64 /\
    p_rC4 cx h B regs /\ p_frame cx dsh_loop ps_C4 W3 mem3 /\ d_blocks B cx h [] ly3 S3 /\
    garr8 SEGS (rd W3 mem3) (d_obj cx OOUR) (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx)))).
Definition pro_C5 (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  d_at B MT XM_LIB RLO RHI tfib_K cx POFF_C5 EV_PRO (ACC_PRO MT) (fun regs ly3 S3 W3 mem3 md3 =>
    0 <= c_canary cx < 2 ^ 64 /\
    p_rC5 cx h B regs /\ p_frame cx dsh_loop ps_C5 W3 mem3 /\ d_blocks B cx h [] ly3 S3 /\
    val_mem SEGS (rd W3 mem3) (d_A cx + 216) 8 h /\
    exists T G Lk H : list byte, d_objs cx h T G Lk H W3 mem3).
Definition pro_segA : Prop :=
  forall (fq : YK11.FPState) ly S (W : world SEGS) (regs : bvmap 5 word) mem md p n pl M,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  tfib_lib_pre_x B MT XM_LIB RLO RHI tfib_K regs ly S W mem md p n pl M -> dpre_extra W mem ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_LLVMFuzzerTestOneInput) regs mem md)
    (fun W' c' => exists cx : dcx,
       c_ly cx = ly /\ c_S cx = S /\ c_W cx = W /\ c_regs cx = regs /\ c_mem cx = mem /\
       c_md cx = md /\ c_p cx = p /\ c_n cx = n /\ c_pl cx = pl /\ c_M cx = M /\ pro_C2 cx W' c').
Definition pro_segB : Prop :=
  forall (cx : dcx) (W : world SEGS) (c : config), pro_C2 cx W c -> SRr SEGS W c (pro_C3 cx).
Definition pro_segC : Prop :=
  forall (cx : dcx) (W : world SEGS) (c : config), pro_C3 cx W c ->
  SRr SEGS W c (fun W' c' => exists h, pro_C4 cx h W' c').
Definition pro_segD : Prop :=
  forall (cx : dcx) (h : Z) (W : world SEGS) (c : config), pro_C4 cx h W c -> SRr SEGS W c (pro_C5 cx h).
Definition pro_segE : Prop :=
  forall (cx : dcx) (h : Z) (W : world SEGS) (c : config), pro_C5 cx h W c ->
  SRr SEGS W c (fun W' c' => loop_inv B MT XM_LIB RLO RHI tfib_K cx h 0 W' c' \/
                             exit_pre B MT XM_LIB RLO RHI tfib_K cx h W' c').
Theorem pro_of_segs : pro_segA -> pro_segB -> pro_segC -> pro_segD -> pro_segE ->
  pro_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros SA SB SC SD SE. unfold pro_spec.
  intros fq ly S W regs mem md p n pl M Hf Hpre Hext.
  eapply SRr_bind; [exact (SA fq ly S W regs mem md p n pl M Hf Hpre Hext)|].
  cbv beta. intros W1 c1 _ (cx & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & H2).
  eapply SRr_bind; [exact (SB cx W1 c1 H2)|].
  cbv beta. intros W2 c2 _ H3.
  eapply SRr_bind; [exact (SC cx W2 c2 H3)|].
  cbv beta. intros W3 c3 _ (h & H4).
  eapply SRr_bind; [exact (SD cx h W3 c3 H4)|].
  cbv beta. intros W4 c4 _ H5.
  eapply SRr_mono; [exact (SE cx h W4 c4 H5)|].
  cbv beta. intros W5 c5 _ H6.
  exists cx, h. repeat (split; [assumption|]). exact H6.
Qed.
End h.
End f.
End d.
