(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_set_resweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxSetResweep.v, with its module paths, module names and numbers changed; 174 of its 248 lines of code are new or changed and 208 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacHuntHeardAnything.v, with its module names changed; 98 of its 127 lines of code are new or changed and 219 lines of the source are left out. *)
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
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition AT_FL : nat := 530%nat.
Definition AT_X : nat := 531%nat.
Definition dfhdr_chunks : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SLit MAGIC_LIVE)); YP09.mkChunk 8 (CVal 8 (SOff (A_OBJ 2) 0));
   YP09.mkChunk 16 (CVal 8 (SOff (A_OBJ 3) 0)); YP09.mkChunk 4088 (CVal 8 (SOff AT_FL 0))].
Definition d_kregions (shf : Z -> Z) (acs fcs : list YP09.chunk) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 472 (dslot_chunks ++ acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 DFRAME_SIZE (dfhdr_chunks ++ fcs);
   fshadow_region AT_SH DFRAME_CLASS 0 DFRAME_SH (dsh_chunks shf);
   got_regionP; bcell_regionP 32].
Definition ss_d (pc : Z) (sr : list sv) (shf : Z -> Z) (acs fcs : list YP09.chunk) (extra : smem) (G : facts)
  : sstate := mkSS pc sr (d_kregions shf acs fcs ++ extra) None G.
Definition d_alias : list (sv * sv) :=
  [(SAlu ALU_ADD (SAlu ALU_SRL (SOff AT_F 0) (SLit 3)) (SOff 32 0), SOff AT_SH 0)].
Definition d_atoms : list (nat * afact) :=
  [(AT_STK, mkAF (2 ^ 46) (2 ^ 47) 4); (AT_A, mkAF (2 ^ 46 - 1024) (2 ^ 47) 5);
   (AT_F, mkAF 4096 140737479966720 5); (AT_SH, mkAF (SB + 512) (SB + 17592186044416) 2);
   (32%nat, mkAF SB SB 0)].
Definition d_facts (fa : list (nat * afact)) (cs : list acond) : facts := mkFacts (d_atoms ++ fa) cs d_alias.

Definition cval_eqb (a b : cval) : bool :=
  match a, b with
  | CVal w v, CVal w' v' => N.eqb w w' && sv_eqb v v'
  | CZero l, CZero l' => Z.eqb l l'
  | CImg l, CImg l' => Z.eqb l l'
  | CData d s l, CData d' s' l' => Nat.eqb d d' && Z.eqb s s' && Z.eqb l l'
  | _, _ => false
  end.
Definition chunk_eqb (a b : YP09.chunk) : bool := Z.eqb (YP09.c_off a) (YP09.c_off b) && cval_eqb (YP09.c_val a) (YP09.c_val b).
Definition chunks_cover (tgt src : list YP09.chunk) : bool := forallb (fun c => existsb (chunk_eqb c) src) tgt.
Definition region_cover (b : nat) (lo hi : Z) (tgt : list YP09.chunk) (r : YP09.region) : bool :=
  obase_eqb (YP09.r_base r) (Some b) && (YP09.r_lo r <=? lo) && (hi <=? YP09.r_hi r) && chunks_cover tgt (YP09.r_chunks r).
Definition sh_byte_ok (cs : list YP09.chunk) (shf : Z -> Z) (k : Z) : bool :=
  match find_chunk cs k 1 with
  | Some (YP09.mkChunk o (CVal w (SLit v))) =>
      Z.eqb (Z.shiftr (v mod 2 ^ 64) (8 * (k - o)) mod 256) (shf k) && (0 <=? shf k) && (shf k <? 256)
  | _ => false
  end.
Definition sh_region_ok (shf : Z -> Z) (r : YP09.region) : bool :=
  obase_eqb (YP09.r_base r) (Some AT_SH) && (YP09.r_lo r <=? 0) && (fs_frame_bytes DFRAME_CLASS / 8 <=? YP09.r_hi r) &&
  forallb (fun k => sh_byte_ok (YP09.r_chunks r) shf (Z.of_nat k)) (seq 0 (Z.to_nat DFRAME_SH)).
Definition d_land_chk (shf : Z -> Z) (rs : smem) : bool :=
  existsb (region_cover AT_STK (-104) 0 dsave_chunks) rs &&
  existsb (region_cover AT_A 0 472 dslot_chunks) rs &&
  existsb (region_cover AT_F 0 (fs_frame_bytes DFRAME_CLASS) dfhdr_chunks) rs &&
  existsb (sh_region_ok shf) rs.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Definition d_env (cx : dcx) (E : env) (vals : list word) : env :=
  havoc E AT_FL (Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) :: vals).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Definition d_ctx (cx : dcx) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (mem3 : word -> option byte)
  (md3 : Model) (k : Z) : Prop :=
  d_base B MT XM_LIB RLO RHI tfib_K cx /\
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 mem3 md3 k /\
  frames S3 = [(DFRAME_CLASS, c_fpos cx)].
Definition d_seat_stmt : Prop :=
  AR_laws SEGS B -> PALib B ->
  forall (fq : YK11.FPState) (cx : dcx) (shf : Z -> Z) ly3 S3 (W3 : world SEGS) (regs : bvmap 5 word) mem3 md3 k
    (E : env) (pc : Z) (sr : list sv) (vals : list word) (acs fcs : list YP09.chunk) (extra : smem) (G : facts),
  d_ctx cx ly3 S3 W3 mem3 md3 k ->
  d_E cx E -> Forall (region_ok SEGS E (rd W3 mem3)) (d_regions cx shf) ->
  rdword (aview SEGS (w_H W3) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  regs_ok (d_env cx E vals) sr regs ->
  facts_ok (d_env cx E vals) G ->
  Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W3 mem3) (d_A cx)) acs ->
  Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W3 mem3) (d_FB cx)) fcs ->
  Forall (region_ok SEGS (d_env cx E vals) (rd W3 mem3)) extra ->
  pairwise_disjoint (d_env cx E vals) extra ->
  Forall (fun r => all_disjoint (d_env cx E vals) r (d_kregions shf acs fcs)) extra ->
  regions_wf (d_kregions shf acs fcs ++ extra) = true ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) (ss_d pc sr shf acs fcs extra G)
    (restrict (w_H W3) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) mem3 (YK11.seg_rom SEGS))).
Definition d_facts_stmt : Prop :=
  AR_laws SEGS B ->
  forall (cx : dcx) ly3 S3 (W3 : world SEGS) mem3 md3 k (E : env) (vals : list word) fa cs,
  d_ctx cx ly3 S3 W3 mem3 md3 k -> d_E cx E ->
  atoms_ok (d_env cx E vals) fa -> conds_ok (d_env cx E vals) cs ->
  facts_ok (d_env cx E vals) (d_facts fa cs).
Definition d_land_stmt : Prop :=
  AR_laws SEGS B -> frame_flag_lawP SEGS B ->
  forall (fq : YK11.FPState) (cx : dcx) (h : Z) (shf : Z -> Z) ly3 S3 (W3 : world SEGS) md3 k
    (E : env) (ss : sstate) (ms : machine_state),
  d_ctx cx ly3 S3 W3 (ms_mem ms) md3 k ->
  d_E cx E -> ew E AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W3) ms) ->
  d_land_chk shf (ss_mem ss) = true ->
  val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 216) 8 h ->
  val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 152) 8 (h + 440) ->
  d_frame cx h shf W3 (ms_mem ms) /\ d_shadow cx shf W3 (ms_mem ms).
End h.
End f.
End d.
