(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim StoreOk Frame Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Export ZlibStmtBase ExSmallIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface DeflateState Deflate InflateState Inflate InflateRc InflateSync
     HarnessKit HarnessFacts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation RSEGS := Src_zlib_example_flush_fuzzer_repro.M.loaded_segments.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition FL_A_DI      : Z := 0x16468.
Definition FL_A_DEFLATE : Z := 0x16c80.
Definition FL_A_II      : Z := 0x1ce50.
Definition FL_A_INFLATE : Z := 0x1cf48.
Definition FL_A_ZW      : Z := 0x1ed50.
Definition FL_A_ZB      : Z := 0x1ed54.
Definition FL_A_ISY     : Z := 0x1eefc.
Definition FL_ZCALLOC   : Z := 0x19ff8.
Definition FL_ZCFREE    : Z := 0x1a008.
Definition FL_DATALEN   : Z := 0x3a680.
Definition FL_RO_LO     : Z := 0x10000.
Definition FL_RO_HI     : Z := 0x293d8.
Definition FL_IMG_TOP   : Z := 0x5c000.
Definition FL_FRA       : Z := 1024.
Definition FL_IFR       : Z := 416.
Definition FL_ZWD       : Z := 272.
Definition FL_DSTATE_N  : Z := 5968.      Definition FL_DBLK_N : Z := 65536.
Definition FL_ISTATE_N  : Z := 7176.      Definition FL_WIN_N  : Z := 32768.

Definition FL_KEEP : list reg := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition rkeep (regs regs' : bvmap 5 word) (l : list reg) : Prop := forall r, In r l -> getr regs' r = getr regs r.
Definition ra_ok (ra : Z) : Prop := 0 <= ra < 2 ^ 64 /\ ra mod 2 = 0.

Record dptrs : Type := DP { dp_strm : Z; dp_s : Z; dp_wnd : Z; dp_prv : Z; dp_hd : Z; dp_pb : Z }.
Definition dblocks (q : dptrs) : list (Z * Z) :=
  [(dp_s q, FL_DSTATE_N); (dp_wnd q, FL_DBLK_N); (dp_prv q, FL_DBLK_N); (dp_hd q, FL_DBLK_N); (dp_pb q, FL_DBLK_N)].
Record iptrs : Type := IP { ip_strm : Z; ip_p : Z; ip_w : Z }.
Definition iblocks (q : iptrs) : list (Z * Z) :=
  (ip_p q, FL_ISTATE_N) :: (if ip_w q =? 0 then [] else [(ip_w q, FL_WIN_N)]).

Section WithSegs.
Let RS := RSEGS.
Definition blocks_ok (mem : word -> option byte) (zc : Z) (l : list (Z * Z)) : Prop :=
  Forall (fun bn => blk_okz RS mem FL_IMG_TOP zc (fst bn) (snd bn)) l.
Definition img_clear (mem : word -> option byte) : Prop := forall i, FL_RO_LO <= i < FL_RO_HI -> mem (Z_to_bv 64 i) = None.
Definition wz (l : list (Z * Z)) : list (word * Z) := map (fun bn => (Z_to_bv 64 (fst bn), snd bn)) l.

Definition izs_cells (ma : Z -> Z) (mem : word -> option byte) (strm : Z) (next_in avail_in next_out avail_out : Z) (z : zstrm) (state fa ff : Z) : Prop :=
  cell8 RS mem strm next_in /\ cell4 RS mem (strm + 8) avail_in /\ cell8 RS mem (strm + 16) (zs_total_in z) /\
  cell8 RS mem (strm + 24) next_out /\ cell4 RS mem (strm + 32) avail_out /\ cell8 RS mem (strm + 40) (zs_total_out z) /\
  cell8 RS mem (strm + 48) (ma (zs_msg z)) /\
  cell8 RS mem (strm + 56) state /\ cell8 RS mem (strm + 64) fa /\ cell8 RS mem (strm + 72) ff /\ cell8 RS mem (strm + 80) 0 /\
  cell8 RS mem (strm + 96) (zs_adler z).
Definition zs_cells (ma : Z -> Z) (mem : word -> option byte) (strm : Z) (next_in avail_in next_out avail_out : Z) (z : zstrm) (state fa ff : Z) : Prop :=
  izs_cells ma mem strm next_in avail_in next_out avail_out z state fa ff /\ cell4 RS mem (strm + 88) (zs_data_type z).

Record fl_lib : Type := FL_LIB {
  fl_drep : (word -> option byte) -> dptrs -> deflate_state -> Prop;
  fl_irep : (word -> option byte) -> iptrs -> inflate_state -> Prop;
  fl_tw   : bvmap 5 word -> bvmap 5 word -> iptrs -> Z -> Z -> inflate_state -> ZCall -> Z -> (word -> option byte) -> Prop;
  fl_msga : Z -> Z;
  fl_msga_null : fl_msga MSG_NULL = 0;
  fl_dsafe : deflate_state -> Z -> Prop;
  fl_isafe : inflate_state -> ZCall -> Z -> Prop;
  fl_ssafe : inflate_state -> ZCall -> Prop;
  fl_ds0 : deflate_state;
  fl_is0 : inflate_state;
  fl_is0_nowin : is_window_blk fl_is0 = None;

  fl_drep_frame : forall m m' q s, fl_drep m q s ->
      (forall (a : word) b k, In (b, k) (dblocks q) -> b <= bv_unsigned a < b + k -> m' a = m a) -> fl_drep m' q s;
  fl_irep_frame : forall m m' q s, fl_irep m q s ->
      (forall (a : word) b k, In (b, k) (iblocks q) -> b <= bv_unsigned a < b + k -> m' a = m a) -> fl_irep m' q s;
  fl_drep_strm : forall m q s cs, fl_drep m q s -> fl_drep m q (set_strm s cs);
  fl_drep_strm' : forall m q s cs, fl_drep m q (set_strm s cs) -> fl_drep m q s;
  fl_drep_cells : forall m q s, fl_drep m q s ->
      cell8 RS m (dp_s q) (dp_strm q) /\ cell4 RS m (dp_s q + 8) (ds_status s) /\ cell8 RS m (dp_s q + 16) (dp_pb q) /\
      cell8 RS m (dp_s q + 96) (dp_wnd q) /\ cell8 RS m (dp_s q + 112) (dp_prv q) /\ cell8 RS m (dp_s q + 120) (dp_hd q);
  fl_irep_cells : forall m q s, fl_irep m q s ->
      cell8 RS m (ip_p q) (ip_strm q) /\ cell4 RS m (ip_p q + 8) (is_mode s) /\ 16180 <= is_mode s <= 16211 /\ cell8 RS m (ip_p q + 88) (ip_w q);   (* 1.4: state->window at 88 (1.3.1: 72) *)
  fl_tw_local : forall (R0 RW : bvmap 5 word) q inp outp s zc f (M M' : word -> option byte),
      let sp := bv_unsigned (getr R0 2) in
      (forall a, (sp - FL_ZWD <= bv_unsigned a < sp \/ ip_p q <= bv_unsigned a < ip_p q + FL_ISTATE_N \/
                  ip_strm q <= bv_unsigned a < ip_strm q + 112 \/ outp <= bv_unsigned a < outp + zc_avail_out zc \/
                  inp <= bv_unsigned a < inp + zlength (zc_input zc)) -> M' a = M a) ->
      (forall a, sp - FL_FRA <= bv_unsigned a < sp - FL_ZWD -> M' a <> None) ->
      fl_tw R0 RW q inp outp s zc f M -> fl_tw R0 RW q inp outp s zc f M';

  fl_di : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : dptrs) (zc ra v16 v24 v32 : Z) (sv20 sv21 sv22 sv23 : word) (fa ff : Z),
    let h := dp_strm q - 8 in let s := dp_s q in
    getr regs 2 = Z_to_bv 64 (h - 80) -> getr regs 8 = Z_to_bv 64 (dp_strm q) -> getr regs 9 = Z_to_bv 64 s ->
    getr regs 10 = Z_to_bv 64 (dp_pb q) -> getr regs 20 = Z_to_bv 64 (s + 5888) ->
    getr regs 18 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 6 -> getr regs 21 = Z_to_bv 64 1 -> getr regs 22 = Z_to_bv 64 15 -> getr regs 23 = Z_to_bv 64 8 ->
    h mod 16 = 0 -> zc + FL_FRA <= h -> h + 120 <= 2 ^ 47 -> FL_IMG_TOP <= zc ->
    blocks_ok mem zc (dblocks q) -> all_apart (dblocks q) -> img_clear mem ->
    store_ok RS mem (Z_to_bv 64 (h - FL_FRA)) (Z.to_nat (FL_FRA + 120)) = true ->
    ra_ok ra -> 0 <= v16 < 2 ^ 63 -> 0 <= v24 < 2 ^ 63 -> 0 <= v32 < 2 ^ 63 ->
    zeros_at RS mem (dp_wnd q) FL_DBLK_N -> zeros_at RS mem (dp_prv q) FL_DBLK_N -> zeros_at RS mem (dp_hd q) FL_DBLK_N -> zeros_at RS mem (dp_pb q) FL_DBLK_N ->
    zeros_at RS mem (s + 12) 36 -> zeros_at RS mem (s + 52) 4 -> zeros_at RS mem (s + 64) 16 -> zeros_at RS mem (s + 92) 4 ->
    zeros_at RS mem (s + 104) 8 -> zeros_at RS mem (s + 128) 4 -> zeros_at RS mem (s + 148) 5748 -> zeros_at RS mem (s + 5900) 52 -> zeros_at RS mem (s + 5960) 8 ->   (* 1.4: the 5968-byte state's tail around high_water (s + 5952) *)
    cell8 RS mem s (dp_strm q) -> cell4 RS mem (s + 8) 42 -> cell4 RS mem (s + 48) 1 -> cell8 RS mem (s + 56) 0 ->
    cell4 RS mem (s + 80) 32768 -> cell4 RS mem (s + 84) 15 -> cell4 RS mem (s + 88) 32767 ->
    cell8 RS mem (s + 96) (dp_wnd q) -> cell8 RS mem (s + 112) (dp_prv q) -> cell8 RS mem (s + 120) (dp_hd q) ->
    cell4 RS mem (s + 132) 32768 -> cell4 RS mem (s + 136) 15 -> cell4 RS mem (s + 140) 32767 -> cell4 RS mem (s + 144) 5 ->
    cell4 RS mem (s + 5896) 16384 -> cell8 RS mem (s + 5952) 0 -> (* 1.4: high_water at 5952 *)
    cell8 RS mem (h - 8) ra -> cell8 RS mem (h - 16) v16 -> cell8 RS mem (h - 24) v24 -> cell8 RS mem (h - 32) v32 -> cell8 RS mem (h - 40) FL_DATALEN ->
    cellw RS mem (h - 48) sv20 -> cellw RS mem (h - 56) sv21 -> cellw RS mem (h - 64) sv22 -> cellw RS mem (h - 72) sv23 ->
    cellw RS mem (h - 80) (getr regs 24) ->   (* 1.4: the prologue also saved s8 (x24) at 0(sp) = h - 80; the epilogue reloads it *)
    cell8 RS mem (h + 56) 0 -> cell8 RS mem (h + 64) s -> cell8 RS mem (h + 72) fa -> cell8 RS mem (h + 80) ff -> cell8 RS mem (h + 88) 0 ->
    fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps RS (mkst regs (Z_to_bv 64 FL_A_DI) mem (seg_rom RS)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RS))
      /\ frame_mod mem mem' ((Z_to_bv 64 (h - FL_FRA), FL_FRA) :: (Z_to_bv 64 (h + 8), 112) :: wz (dblocks q))
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 h
      /\ getr regs' 8 = Z_to_bv 64 v16 /\ getr regs' 9 = Z_to_bv 64 v24 /\ getr regs' 18 = Z_to_bv 64 v32 /\ getr regs' 19 = Z_to_bv 64 FL_DATALEN
      /\ getr regs' 20 = sv20 /\ getr regs' 21 = sv21 /\ getr regs' 22 = sv22 /\ getr regs' 23 = sv23
      /\ rkeep regs regs' [3; 4; 24; 25; 26; 27]%bv
      /\ cell8 RS mem' (h + 24) 0 /\ cell8 RS mem' (h + 48) 0 /\ cell8 RS mem' (h + 56) 0 /\ cell8 RS mem' (h + 64) s
      /\ cell8 RS mem' (h + 72) fa /\ cell8 RS mem' (h + 80) ff /\ cell8 RS mem' (h + 88) 0 /\ cell4 RS mem' (h + 96) 2 /\ cell8 RS mem' (h + 104) 1
      /\ fl_drep mem' q fl_ds0;

  fl_dfl : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : dptrs) (s : deflate_state) (zc : ZCall) (f : Z)
                  (sp ra inp outp zcl fa ff : Z),
    let ds := set_strm s (cstrm_of_call zc) in
    let X  := fst (deflate_core ds f) in let rc := snd (deflate_core ds f) in
    let nout := Z.of_nat (length (cs_out_rev (ds_strm X))) in
    getr regs 10 = Z_to_bv 64 (dp_strm q) -> getr regs 11 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = Z_to_bv 64 ra ->
    ra_ok ra -> sp mod 16 = 0 -> zcl + FL_FRA <= sp -> sp <= 2 ^ 47 -> FL_IMG_TOP <= zcl ->
    blocks_ok mem zcl (dblocks q) -> img_clear mem ->
    0 < dp_strm q -> dp_strm q + 112 <= 2 ^ 63 -> dp_strm q mod 8 = 0 -> 0 < inp -> 0 < outp ->
    store_ok RS mem (Z_to_bv 64 (sp - FL_FRA)) (Z.to_nat FL_FRA) = true ->
    store_ok RS mem (Z_to_bv 64 (dp_strm q)) 112%nat = true ->
    store_ok RS mem (Z_to_bv 64 outp) (Z.to_nat (zc_avail_out zc)) = true ->
    all_apart ((sp - FL_FRA, FL_FRA) :: (dp_strm q, 112) :: (outp, zc_avail_out zc) :: (inp, zlength (zc_input zc)) :: dblocks q) ->
    (forall a n, In (a, n) ((sp - FL_FRA, FL_FRA) :: (dp_strm q, 112) :: (outp, zc_avail_out zc) :: dblocks q) -> a + n <= FL_RO_LO \/ FL_IMG_TOP <= a) ->
    inp + zlength (zc_input zc) < 2 ^ 63 -> outp + zc_avail_out zc < 2 ^ 63 ->
    fl_drep mem q s -> holds RS mem inp (zc_input zc) ->
    zs_cells fl_msga mem (dp_strm q) inp (zlength (zc_input zc)) outp (zc_avail_out zc) (zc_strm zc) (dp_s q) fa ff ->
    fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    fl_dsafe ds f ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps RS (mkst regs (Z_to_bv 64 FL_A_DEFLATE) mem (seg_rom RS)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RS))
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - FL_FRA), FL_FRA) :: (Z_to_bv 64 (dp_strm q), 112) :: (Z_to_bv 64 outp, nout) :: wz (dblocks q))
      /\ getr regs' 10 = Z_to_bv 64 rc /\ 0 <= rc <= 1 /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep regs regs' FL_KEEP
      /\ fl_drep mem' q X
      /\ 0 <= nout <= zc_avail_out zc /\ 0 <= cs_next_in (ds_strm X) <= zlength (zc_input zc)
      /\ zs_cells fl_msga mem' (dp_strm q) (inp + cs_next_in (ds_strm X)) (zlength (zc_input zc) - cs_next_in (ds_strm X))
                      (outp + nout) (zc_avail_out zc - nout)
                      (zr_strm (zret_of_cs (ds_strm X) rc)) (dp_s q) fa ff
      /\ holds RS mem' outp (cs_output (ds_strm X));

  fl_ii : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (zc t ra v16 v24 v32 fa ff ni ai : Z),
    let p := ip_p q in let strm := ip_strm q in
    ip_w q = 0 ->
    getr regs 2 = Z_to_bv 64 (t - 32) -> getr regs 10 = Z_to_bv 64 p -> getr regs 9 = Z_to_bv 64 strm ->
    t mod 16 = 0 -> zc + FL_FRA <= t -> t <= 2 ^ 47 -> FL_IMG_TOP <= zc ->
    blocks_ok mem zc (iblocks q) -> img_clear mem -> 0 < strm -> strm mod 8 = 0 -> strm + 112 <= 2 ^ 47 ->
    store_ok RS mem (Z_to_bv 64 (t - FL_FRA)) (Z.to_nat FL_FRA) = true -> store_ok RS mem (Z_to_bv 64 strm) 112%nat = true ->
    all_apart [(t - FL_FRA, FL_FRA); (strm, 112); (p, FL_ISTATE_N)] -> (strm + 112 <= FL_RO_LO \/ FL_IMG_TOP <= strm) ->
    ra_ok ra -> 0 <= v16 < 2 ^ 63 -> 0 <= v24 < 2 ^ 63 -> 0 <= v32 < 2 ^ 63 ->
    zeros_at RS mem p FL_ISTATE_N ->
    cell8 RS mem (t - 8) ra -> cell8 RS mem (t - 16) v16 -> cell8 RS mem (t - 24) v24 -> cell8 RS mem (t - 32) v32 ->
    cell8 RS mem (strm + 48) 0 -> cell8 RS mem (strm + 64) fa -> cell8 RS mem (strm + 72) ff -> cell8 RS mem (strm + 80) 0 ->
    fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    cell8 RS mem strm ni -> cell4 RS mem (strm + 8) ai ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps RS (mkst regs (Z_to_bv 64 FL_A_II) mem (seg_rom RS)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RS))
      /\ frame_mod mem mem' [(Z_to_bv 64 (t - FL_FRA), FL_FRA); (Z_to_bv 64 strm, 112); (Z_to_bv 64 p, FL_ISTATE_N)]
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 t
      /\ getr regs' 8 = Z_to_bv 64 v16 /\ getr regs' 9 = Z_to_bv 64 v24 /\ getr regs' 18 = Z_to_bv 64 v32
      /\ rkeep regs regs' [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
      /\ cell8 RS mem' (strm + 16) 0 /\ cell8 RS mem' (strm + 40) 0 /\ cell8 RS mem' (strm + 48) 0 /\ cell8 RS mem' (strm + 56) p
      /\ cell8 RS mem' (strm + 64) fa /\ cell8 RS mem' (strm + 72) ff /\ cell8 RS mem' (strm + 80) 0 /\ cell8 RS mem' (strm + 96) 1
      /\ fl_irep mem' q fl_is0
      /\ cell8 RS mem' strm ni /\ cell4 RS mem' (strm + 8) ai;

  fl_inf : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (s : inflate_state) (zc : ZCall) (f : Z)
                  (sp ra inp outp zcl fa ff : Z) (ans : option (blk * (Z -> Z))),
    let p := ip_p q in let strm := ip_strm q in
    getr regs 10 = Z_to_bv 64 strm -> getr regs 11 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = Z_to_bv 64 ra ->
    ra_ok ra -> sp mod 16 = 0 -> zcl + FL_FRA <= sp -> sp <= 2 ^ 47 -> FL_IMG_TOP <= zcl ->
    blocks_ok mem zcl (iblocks q) -> img_clear mem -> 0 < strm -> strm + 112 <= 2 ^ 47 -> strm mod 8 = 0 -> 0 < inp -> 0 < outp ->
    store_ok RS mem (Z_to_bv 64 (sp - FL_FRA)) (Z.to_nat FL_FRA) = true -> store_ok RS mem (Z_to_bv 64 strm) 112%nat = true ->
    store_ok RS mem (Z_to_bv 64 outp) (Z.to_nat (zc_avail_out zc)) = true ->
    all_apart ((sp - FL_FRA, FL_FRA) :: (strm, 112) :: (outp, zc_avail_out zc) :: (inp, zlength (zc_input zc)) :: iblocks q) ->
    (forall a n, In (a, n) [(sp - FL_FRA, FL_FRA); (strm, 112); (outp, zc_avail_out zc); (inp, zlength (zc_input zc))] -> a + n <= FL_RO_LO \/ FL_IMG_TOP <= a) ->
    inp + zlength (zc_input zc) < 2 ^ 63 -> outp + zc_avail_out zc < 2 ^ 63 -> zc_avail_out zc < 2 ^ 31 -> zlength (zc_input zc) < 2 ^ 31 ->
    fl_irep mem q s -> (ip_w q = 0 <-> is_window_blk s = None) -> holds RS mem inp (zc_input zc) ->
    izs_cells fl_msga mem strm inp (zlength (zc_input zc)) outp (zc_avail_out zc) (zc_strm zc) p fa ff -> fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    fl_isafe s zc f ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte) (nout : Z),
      0 <= nout <= zc_avail_out zc
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - FL_IFR), FL_IFR) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, nout) :: wz (iblocks q))
      /\ match snd (inflate_p ivar_ref ans s zc f) with
         | None =>
             let s' := fst (fst (inflate_p ivar_ref ans s zc f)) in let r := snd (fst (inflate_p ivar_ref ans s zc f)) in
             msteps RS (mkst regs (Z_to_bv 64 FL_A_INFLATE) mem (seg_rom RS)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RS))
             /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep regs regs' FL_KEEP
             /\ (~ RR (zr_rc r) ->
                 nout = zlength (zr_output r) /\ 0 <= zr_consumed r <= zlength (zc_input zc)
                 /\ fl_irep mem' q s'
                 /\ izs_cells fl_msga mem' strm (inp + zr_consumed r) (zlength (zc_input zc) - zr_consumed r) (outp + nout) (zc_avail_out zc - nout)
                              (zr_strm r) p fa ff
                 /\ holds RS mem' outp (zr_output r)
                 /\ (ip_w q = 0 <-> is_window_blk s' = None))
         | Some sz =>
             sz = FL_WIN_N /\ ip_w q = 0 /\
             msteps RS (mkst regs (Z_to_bv 64 FL_A_INFLATE) mem (seg_rom RS)) (mkst regs' (Z_to_bv 64 FL_A_ZW) mem' (seg_rom RS))
             /\ getr regs' 13 = Z_to_bv 64 fa /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 FL_WIN_N /\ getr regs' 12 = Z_to_bv 64 1
             /\ getr regs' 2 = Z_to_bv 64 (sp - FL_ZWD) /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
             /\ fl_tw regs regs' q inp outp s zc f mem'
         end;

  fl_inb : forall (R0 RW regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (s : inflate_state) (zc : ZCall) (f : Z)
                  (sp ra inp outp zcl fa ff w : Z) (b : blk),
    let p := ip_p q in let strm := ip_strm q in let q' := IP strm p w in
    let ans := Some (b, fun _ => 0) in
    fl_tw R0 RW q inp outp s zc f mem -> rkeep RW regs FL_KEEP ->
    getr R0 2 = Z_to_bv 64 sp -> getr R0 1 = Z_to_bv 64 ra -> getr R0 11 = Z_to_bv 64 f ->
    getr regs 10 = Z_to_bv 64 w -> getr regs 2 = Z_to_bv 64 (sp - FL_ZWD) ->
    zcl + FL_FRA <= sp -> sp <= 2 ^ 47 -> img_clear mem ->
    fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    blk_okz RS mem FL_IMG_TOP zcl w FL_WIN_N -> zeros_at RS mem w FL_WIN_N ->
    all_apart ((w, FL_WIN_N) :: (sp - FL_FRA, FL_FRA) :: (strm, 112) :: (outp, zc_avail_out zc) :: (inp, zlength (zc_input zc)) :: iblocks q) ->
    snd (inflate_p ivar_ref ans s zc f) = Some FL_WIN_N ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte) (nout : Z),
      let s' := fst (fst (inflate_p ivar_ref ans s zc f)) in let r := snd (fst (inflate_p ivar_ref ans s zc f)) in
      msteps RS (mkst regs (Z_to_bv 64 FL_A_ZB) mem (seg_rom RS)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RS))
      /\ 0 <= nout <= zc_avail_out zc
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - FL_IFR), FL_IFR) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, nout) :: wz (iblocks q'))
      /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep R0 regs' FL_KEEP
      /\ (~ RR (zr_rc r) ->
          nout = zlength (zr_output r) /\ 0 <= zr_consumed r <= zlength (zc_input zc)
          /\ fl_irep mem' q' s'
          /\ izs_cells fl_msga mem' strm (inp + zr_consumed r) (zlength (zc_input zc) - zr_consumed r) (outp + nout) (zc_avail_out zc - nout) (zr_strm r) p fa ff
          /\ holds RS mem' outp (zr_output r));

  fl_isy : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (s : inflate_state) (zc : ZCall)
                  (sp ra inp outp zcl fa ff : Z),
    let p := ip_p q in let strm := ip_strm q in
    let s' := fst (inflateSync_m ivar_ref s zc) in let r := snd (inflateSync_m ivar_ref s zc) in
    getr regs 10 = Z_to_bv 64 strm -> getr regs 2 = Z_to_bv 64 sp -> getr regs 1 = Z_to_bv 64 ra ->
    ra_ok ra -> sp mod 16 = 0 -> zcl + FL_FRA <= sp -> sp <= 2 ^ 47 -> FL_IMG_TOP <= zcl ->
    blocks_ok mem zcl (iblocks q) -> img_clear mem -> 0 < strm -> strm + 112 <= 2 ^ 63 -> strm mod 8 = 0 -> 0 < inp ->
    store_ok RS mem (Z_to_bv 64 (sp - 96)) 96%nat = true -> store_ok RS mem (Z_to_bv 64 strm) 112%nat = true ->
    all_apart ((sp - 96, 96) :: (strm, 112) :: (inp, zlength (zc_input zc)) :: iblocks q) ->
    (forall a n, In (a, n) [(sp - 96, 96); (strm, 112); (inp, zlength (zc_input zc))] -> a + n <= FL_RO_LO \/ FL_IMG_TOP <= a) ->
    inp + zlength (zc_input zc) < 2 ^ 63 -> zlength (zc_input zc) < 2 ^ 32 ->
    fl_irep mem q s -> holds RS mem inp (zc_input zc) ->
    izs_cells fl_msga mem strm inp (zlength (zc_input zc)) outp (zc_avail_out zc) (zc_strm zc) p fa ff -> fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    fl_ssafe s zc ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps RS (mkst regs (Z_to_bv 64 FL_A_ISY) mem (seg_rom RS)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RS))
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - 96), 96) :: (Z_to_bv 64 strm, 112) :: wz (iblocks q))
      /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep regs regs' FL_KEEP
      /\ zr_output r = [] /\ 0 <= zr_consumed r <= zlength (zc_input zc)
      /\ fl_irep mem' q s'
      /\ izs_cells fl_msga mem' strm (inp + zr_consumed r) (zlength (zc_input zc) - zr_consumed r) outp (zc_avail_out zc) (zr_strm r) p fa ff
      /\ (ip_w q = 0 <-> is_window_blk s' = None)
}.
End WithSegs.

End FXG.
