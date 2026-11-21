(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim StoreOk Frame Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState Inflate InflateRc InflateCall HarnessKit HarnessFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflCtx6 IRep6 ICall6 ICall6B.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ZlibStmtBase ExSmallIface FlLibStmt FlLibIface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation RSX := Src_zlib_example_flush_fuzzer_repro.M.loaded_segments.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma TW_LOCAL6_ok : forall (R0 RW : bvmap 5 word) q inp outp s zc f (M M' : word -> option byte),
      let sp := bv_unsigned (getr R0 2) in
      (forall a, (sp - FL_ZWD <= bv_unsigned a < sp \/ ip_p q <= bv_unsigned a < ip_p q + FL_ISTATE_N \/
                  ip_strm q <= bv_unsigned a < ip_strm q + 112 \/ outp <= bv_unsigned a < outp + zc_avail_out zc \/
                  inp <= bv_unsigned a < inp + zlength (zc_input zc)) -> M' a = M a) ->
      (forall a, sp - FL_FRA <= bv_unsigned a < sp - FL_ZWD -> M' a <> None) ->
      TWF R0 RW q inp outp s zc f M -> TWF R0 RW q inp outp s zc f M'.
Proof. exact twf_local. Qed.

Lemma L_INF6_ok : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (s : inflate_state) (zc : ZCall) (f : Z)
                  (sp ra inp outp zcl fa ff : Z) (ans : option (blk * (Z -> Z))),
    let p := ip_p q in let strm := ip_strm q in
    getr regs 10 = Z_to_bv 64 strm -> getr regs 11 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = Z_to_bv 64 ra ->
    ra_ok ra -> sp mod 16 = 0 -> zcl + FL_FRA <= sp -> sp <= 2 ^ 47 -> FL_IMG_TOP <= zcl ->
    blocks_ok mem zcl (iblocks q) -> img_clear mem -> 0 < strm -> strm + 112 <= 2 ^ 47 -> strm mod 8 = 0 -> 0 < inp -> 0 < outp ->
    store_ok RSX mem (Z_to_bv 64 (sp - FL_FRA)) (Z.to_nat FL_FRA) = true -> store_ok RSX mem (Z_to_bv 64 strm) 112%nat = true ->
    store_ok RSX mem (Z_to_bv 64 outp) (Z.to_nat (zc_avail_out zc)) = true ->
    all_apart ((sp - FL_FRA, FL_FRA) :: (strm, 112) :: (outp, zc_avail_out zc) :: (inp, zlength (zc_input zc)) :: iblocks q) ->
    (forall a n, In (a, n) [(sp - FL_FRA, FL_FRA); (strm, 112); (outp, zc_avail_out zc); (inp, zlength (zc_input zc))] -> a + n <= FL_RO_LO \/ FL_IMG_TOP <= a) ->
    inp + zlength (zc_input zc) < 2 ^ 63 -> outp + zc_avail_out zc < 2 ^ 63 -> zc_avail_out zc < 2 ^ 31 -> zlength (zc_input zc) < 2 ^ 31 ->
    FL_IREP mem q s -> (ip_w q = 0 <-> is_window_blk s = None) -> holds RSX mem inp (zc_input zc) ->
    izs_cells FL_MSGA mem strm inp (zlength (zc_input zc)) outp (zc_avail_out zc) (zc_strm zc) p fa ff -> fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    FL_ISAFE s zc f ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte) (nout : Z),
      0 <= nout <= zc_avail_out zc
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - FL_IFR), FL_IFR) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, nout) :: wz (iblocks q))
      /\ match snd (inflate_p ivar_ref ans s zc f) with
         | None =>
             let s' := fst (fst (inflate_p ivar_ref ans s zc f)) in let r := snd (fst (inflate_p ivar_ref ans s zc f)) in
             msteps RSX (mkst regs (Z_to_bv 64 FL_A_INFLATE) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
             /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep regs regs' FL_KEEP
             /\ (~ RR (zr_rc r) ->
                 nout = zlength (zr_output r) /\ 0 <= zr_consumed r <= zlength (zc_input zc)
                 /\ FL_IREP mem' q s'
                 /\ izs_cells FL_MSGA mem' strm (inp + zr_consumed r) (zlength (zc_input zc) - zr_consumed r) (outp + nout) (zc_avail_out zc - nout)
                              (zr_strm r) p fa ff
                 /\ holds RSX mem' outp (zr_output r)
                 /\ (ip_w q = 0 <-> is_window_blk s' = None))
         | Some sz =>
             sz = FL_WIN_N /\ ip_w q = 0 /\
             msteps RSX (mkst regs (Z_to_bv 64 FL_A_INFLATE) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 FL_A_ZW) mem' (seg_rom RSX))
             /\ getr regs' 13 = Z_to_bv 64 fa /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 FL_WIN_N /\ getr regs' 12 = Z_to_bv 64 1
             /\ getr regs' 2 = Z_to_bv 64 (sp - FL_ZWD) /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
             /\ TWF regs regs' q inp outp s zc f mem'
         end.
Proof.
  intros regs mem q s zc f sp ra inp outp zcl fa ff ans. cbv zeta.
  intros G10 G11 G2 G1 RA SP16 HZC SP47 HTOP BOK IC S0 S47 S8 INP0 OUTP0 SOKf SOKz SOKo AP IMG BI BO NO31 N31 IR WIFF HLD ZS FA FF SAFE.
  destruct (snd (inflate_p ivar_ref ans s zc f)) as [sz|] eqn:E.
  - destruct (inflate_fl_W regs mem q s zc f sp ra inp outp zcl fa ff G10 G11 G2 G1 RA SP16 HZC SP47 HTOP BOK IC S0 S47 S8 INP0 OUTP0 SOKf SOKz SOKo AP IMG BI BO NO31 N31 IR WIFF HLD ZS FA FF SAFE ans sz E)
      as (regs' & mem' & nout & Hn & FM & W).
    exists regs', mem', nout. split; [exact Hn|]. split; [exact FM|]. exact W.
  - destruct (inflate_fl_R regs mem q s zc f sp ra inp outp zcl fa ff G10 G11 G2 G1 RA SP16 HZC SP47 HTOP BOK IC S0 S47 S8 INP0 OUTP0 SOKf SOKz SOKo AP IMG BI BO NO31 N31 IR WIFF HLD ZS FA FF SAFE ans E)
      as (regs' & mem' & nout & Hn & FM & R).
    exists regs', mem', nout. split; [exact Hn|]. split; [exact FM|]. exact R.
Qed.

Lemma L_INB6_ok : forall (R0 RW regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (s : inflate_state) (zc : ZCall) (f : Z)
                  (sp ra inp outp zcl fa ff w : Z) (b : blk),
    let p := ip_p q in let strm := ip_strm q in let q' := IP strm p w in
    let ans := Some (b, fun _ => 0) in
    TWF R0 RW q inp outp s zc f mem -> rkeep RW regs FL_KEEP ->
    getr R0 2 = Z_to_bv 64 sp -> getr R0 1 = Z_to_bv 64 ra -> getr R0 11 = Z_to_bv 64 f ->
    getr regs 10 = Z_to_bv 64 w -> getr regs 2 = Z_to_bv 64 (sp - FL_ZWD) ->
    zcl + FL_FRA <= sp -> sp <= 2 ^ 47 -> img_clear mem ->
    fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    blk_okz RSX mem FL_IMG_TOP zcl w FL_WIN_N -> zeros_at RSX mem w FL_WIN_N ->
    all_apart ((w, FL_WIN_N) :: (sp - FL_FRA, FL_FRA) :: (strm, 112) :: (outp, zc_avail_out zc) :: (inp, zlength (zc_input zc)) :: iblocks q) ->
    snd (inflate_p ivar_ref ans s zc f) = Some FL_WIN_N ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte) (nout : Z),
      let s' := fst (fst (inflate_p ivar_ref ans s zc f)) in let r := snd (fst (inflate_p ivar_ref ans s zc f)) in
      msteps RSX (mkst regs (Z_to_bv 64 FL_A_ZB) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
      /\ 0 <= nout <= zc_avail_out zc
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - FL_IFR), FL_IFR) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, nout) :: wz (iblocks q'))
      /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep R0 regs' FL_KEEP
      /\ (~ RR (zr_rc r) ->
          nout = zlength (zr_output r) /\ 0 <= zr_consumed r <= zlength (zc_input zc)
          /\ FL_IREP mem' q' s'
          /\ izs_cells FL_MSGA mem' strm (inp + zr_consumed r) (zlength (zc_input zc) - zr_consumed r) (outp + nout) (zc_avail_out zc - nout) (zr_strm r) p fa ff
          /\ holds RSX mem' outp (zr_output r)).
Proof.
  intros R0 RW regs mem q s zc f sp ra inp outp zcl fa ff w b. cbv zeta.
  intros HT RK G2 G1 G11 P10 P2 HZC SP47 IC FA FF BW ZW AP HA.
  exact (inflate_fl_inb R0 RW regs mem q s zc f sp ra inp outp zcl fa ff w b HT RK G2 G1 P10 P2 HZC SP47 IC FA FF BW ZW AP HA).
Qed.
End FXG.
