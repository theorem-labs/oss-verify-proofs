(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim StoreOk Frame Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ZlibStmtBase ExSmallIface FlLibStmt FlLibIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState Inflate InflateRc InflateSync.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflCtx6 IRep6 Sync6.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation RSX := Src_zlib_example_flush_fuzzer_repro.M.loaded_segments.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma L_ISY6_ok : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (s : inflate_state) (zc : ZCall)
                  (sp ra inp outp zcl fa ff : Z),
    let p := ip_p q in let strm := ip_strm q in
    let s' := fst (inflateSync_m ivar_ref s zc) in let r := snd (inflateSync_m ivar_ref s zc) in
    getr regs 10 = Z_to_bv 64 strm -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = Z_to_bv 64 ra ->
    ra_ok ra -> sp mod 16 = 0 -> zcl + FL_FRA <= sp -> sp <= 2 ^ 47 -> FL_IMG_TOP <= zcl ->
    blocks_ok mem zcl (iblocks q) -> img_clear mem -> 0 < strm -> strm + 112 <= 2 ^ 63 -> strm mod 8 = 0 -> 0 < inp ->
    store_ok RSX mem (Z_to_bv 64 (sp - 96)) 96%nat = true -> store_ok RSX mem (Z_to_bv 64 strm) 112%nat = true ->
    all_apart ((sp - 96, 96) :: (strm, 112) :: (inp, zlength (zc_input zc)) :: iblocks q) ->
    (forall a n, In (a, n) [(sp - 96, 96); (strm, 112); (inp, zlength (zc_input zc))] -> a + n <= FL_RO_LO \/ FL_IMG_TOP <= a) ->
    inp + zlength (zc_input zc) < 2 ^ 63 -> zlength (zc_input zc) < 2 ^ 32 ->
    FL_IREP mem q s -> holds RSX mem inp (zc_input zc) ->
    izs_cells FL_MSGA mem strm inp (zlength (zc_input zc)) outp (zc_avail_out zc) (zc_strm zc) p fa ff -> fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    SSAFE6 s zc ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps RSX (mkst regs (Z_to_bv 64 FL_A_ISY) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - 96), 96) :: (Z_to_bv 64 strm, 112) :: wz (iblocks q))
      /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep regs regs' FL_KEEP
      /\ zr_output r = [] /\ 0 <= zr_consumed r <= zlength (zc_input zc)
      /\ FL_IREP mem' q s'
      /\ izs_cells FL_MSGA mem' strm (inp + zr_consumed r) (zlength (zc_input zc) - zr_consumed r) outp (zc_avail_out zc) (zr_strm r) p fa ff
      /\ (ip_w q = 0 <-> is_window_blk s' = None) .
Proof.
  unfold FL_IREP, IRANGES. exact (inflateSync_fl_isy FL_MSGA FL_MSGA_null).
Qed.
End FXG.
