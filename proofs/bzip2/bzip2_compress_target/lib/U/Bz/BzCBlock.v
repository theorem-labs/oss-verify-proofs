(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCHuff BzCMtf.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams BzParamsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
Record cbloc := CBL {
  cb_fs : option fsres;        (* [comment removed for export] *)
  cb_ms : option msres;        (* [comment removed for export] *)
  cb_budget : Z;
  cb_yy : zarr; cb_sm : option smloc }.

(* [comment removed for export] *)
Fixpoint find_orig (n : nat) (arr1 : zarr) (i : Z) : Z :=
  match n with
  | O => -1
  | S n' => if rd32 arr1 i =? 0 then i else find_orig n' arr1 (i + 1)
  end.

(* [comment removed for export] *)
Definition blockSort (e : est) (lj : zarr) : est * option fsres * option msres * Z :=
  let nblock := e_nblock e in
  let '(arr1, arr2, ftab, fs, ms, budget) :=
    (if nblock <? 10000 then
       let r := fallbackSort (e_arr1 e) (e_arr2 e) (e_ftab e) lj lj lj lj nblock in
       (fr_fm r, fr_ec r, fr_bh r, Some r, @None msres, 0)
     else
       let qoff := (let i := nblock + BZ_N_OVERSHOOT in if Z.land i 1 =? 0 then i else i + 1) in
       let wfact := WORKFACTOR in
       let wfact := if wfact <? 1 then 1 else if 100 <? wfact then 100 else wfact in
       let budgetInit := nblock * ((wfact - 1) / 3) in
       let m := mainSort (e_arr1 e) (e_arr2 e) (e_ftab e) lj lj lj lj lj lj lj qoff nblock budgetInit in
       if mr_budget m <? 0 then
         let r := fallbackSort (mr_ptr m) (mr_block m) (mr_ftab m) lj lj lj lj nblock in
         (fr_fm r, fr_ec r, fr_bh r, Some r, Some m, mr_budget m)
       else (mr_ptr m, mr_block m, mr_ftab m, @None fsres, Some m, mr_budget m)) in
  let origPtr := find_orig (Z.to_nat nblock) arr1 0 in
  (EST (e_mode e) (e_state e) (e_avail_in_expect e) arr1 arr2 ftab origPtr
       (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
       (e_bw e) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e)
       (e_len e) (e_code e) (e_rfreq e) (e_len_pack e),
   fs, ms, budget).

(* [comment removed for export] *)
Definition lay_zbits (arr2 : zarr) (nblock : Z) (zb : list Z) : zarr := zarr_of_list_at arr2 nblock zb.

Definition BZ_HDR_B : Z := 66. Definition BZ_HDR_Z : Z := 90. Definition BZ_HDR_h : Z := 104. Definition BZ_HDR_0 : Z := 48.

(* [comment removed for export] *)
Definition compressBlock (e : est) (is_last : bool) (lj : zarr) : est * cbloc :=
  let nblock := e_nblock e in
  (* [comment removed for export] *)
  let '(e1, fs, ms, budget) :=
    (if 0 <? nblock then
       let blockCRC := crc_final (e_blockCRC e) in
       let c := e_combinedCRC e in
       let c := Z.lor ((Z.shiftl c 1) mod 4294967296) (Z.shiftr c 31) in
       let c := Z.lxor c blockCRC in
       let e0 := EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
                     (e_state_in_ch e) (e_state_in_len e) nblock (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
                     (BW (bw_buff (e_bw e)) (bw_live (e_bw e)) 0 znew) blockCRC c (e_blockNo e) (e_nMTF e) (e_mtfFreq e)
                     (e_selector e) (e_selectorMtf e) (e_len e) (e_code e) (e_rfreq e) (e_len_pack e) in
       blockSort e0 lj
     else (est_set_bw e (BW (bw_buff (e_bw e)) (bw_live (e_bw e)) (bw_numZ (e_bw e)) znew), @None fsres, @None msres, 0)) in
  (* [comment removed for export] *)
  let b := e_bw e1 in
  let b := (if e_blockNo e1 =? 1 then
              let b := BW 0 0 (bw_numZ b) (bw_zb b) in
              let b := bsPutUChar b BZ_HDR_B in let b := bsPutUChar b BZ_HDR_Z in
              let b := bsPutUChar b BZ_HDR_h in bsPutUChar b (BZ_HDR_0 + BLOCKSIZE100K)
            else b) in
  (* [comment removed for export] *)
  let '(e2, yy, sm) :=
    (if 0 <? nblock then
       let b := bsPutUChar b 49 in let b := bsPutUChar b 65 in let b := bsPutUChar b 89 in
       let b := bsPutUChar b 38 in let b := bsPutUChar b 83 in let b := bsPutUChar b 89 in
       let b := bsPutUInt32 b (e_blockCRC e1) in
       let b := bsW b 1 0 in
       let b := bsW b 24 (e_origPtr e1) in
       let '(eg, yy) := generateMTFValues (est_set_bw e1 b) lj in
       let '(es, sm) := sendMTFValues eg lj lj lj lj lj lj lj in
       (es, yy, Some sm)
     else (est_set_bw e1 b, lj, @None smloc)) in
  (* [comment removed for export] *)
  let b := e_bw e2 in
  let b := (if is_last then
              let b := bsPutUChar b 23 in let b := bsPutUChar b 114 in let b := bsPutUChar b 69 in
              let b := bsPutUChar b 56 in let b := bsPutUChar b 80 in let b := bsPutUChar b 144 in
              let b := bsPutUInt32 b (e_combinedCRC e2) in
              bs_finish BS_FUEL b
            else b) in
  let e3 := est_set_bw e2 b in
  let e4 := EST (e_mode e3) (e_state e3) (e_avail_in_expect e3) (e_arr1 e3) (lay_zbits (e_arr2 e3) nblock (bw_bytes b)) (e_ftab e3) (e_origPtr e3)
                (e_state_in_ch e3) (e_state_in_len e3) (e_nblock e3) (e_state_out_pos e3) (e_nInUse e3) (e_inUse e3) (e_unseqToSeq e3)
                (e_bw e3) (e_blockCRC e3) (e_combinedCRC e3) (e_blockNo e3) (e_nMTF e3) (e_mtfFreq e3) (e_selector e3) (e_selectorMtf e3)
                (e_len e3) (e_code e3) (e_rfreq e3) (e_len_pack e3) in
  (e4, CBL fs ms budget yy sm).

End ACeilS1.
