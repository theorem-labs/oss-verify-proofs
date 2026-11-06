(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint fss_in (fuel : nat) (fm ec : zarr) (ec_tmp j hi step : Z) : zarr * Z :=
  match fuel with
  | O => (fm, j)
  | S f =>
      if (j <=? hi) && (rd32 ec (rd32 fm j) <? ec_tmp)
      then fss_in f (wr32 fm (j - step) (rd32 fm j)) ec ec_tmp (j + step) hi step
      else (fm, j)
  end.
(* [comment removed for export] *)
Definition fss_iter (fm ec : zarr) (i hi step : Z) : zarr :=
  let tmp := rd32 fm i in
  let ec_tmp := rd32 ec tmp in
  let '(fm1, j) := fss_in (S (Z.to_nat (hi - i))) fm ec ec_tmp (i + step) hi step in
  wr32 fm1 (j - step) tmp.
(* [comment removed for export] *)
Fixpoint fss_outer (n : nat) (fm ec : zarr) (i hi step : Z) : zarr :=
  match n with
  | O => fm
  | S n' => fss_outer n' (fss_iter fm ec i hi step) ec (i - 1) hi step
  end.
Lemma fss_outer_S : forall n fm ec i hi step,
  fss_outer (S n) fm ec i hi step = fss_outer n (fss_iter fm ec i hi step) ec (i - 1) hi step.
Proof. reflexivity. Qed.

Definition fallbackSimpleSort (fm ec : zarr) (lo hi : Z) : zarr :=
  if lo =? hi then fm else
  let fm1 := if 3 <? hi - lo then fss_outer (Z.to_nat (hi - 4 - lo + 1)) fm ec (hi - 4) hi 4 else fm in
  fss_outer (Z.to_nat (hi - 1 - lo + 1)) fm1 ec (hi - 1) hi 1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fswap (fm : zarr) (a b : Z) : zarr :=
  let tmp := rd32 fm a in
  wr32 (wr32 fm a (rd32 fm b)) b tmp.
(* [comment removed for export] *)
Fixpoint fvswap (fuel : nat) (fm : zarr) (p1 p2 n : Z) : zarr :=
  match fuel with
  | O => fm
  | S f => if 0 <? n then fvswap f (fswap fm p1 p2) (p1 + 1) (p2 + 1) (n - 1) else fm
  end.

(* [comment removed for export] *)
Record fpart := FP { fp_fm : zarr; fp_unLo : Z; fp_unHi : Z; fp_ltLo : Z; fp_gtHi : Z }.

(* [comment removed for export] *)
Fixpoint fpart_lo (fuel : nat) (ec : zarr) (med : Z) (p : fpart) : fpart :=
  match fuel with
  | O => p
  | S f =>
      if fp_unHi p <? fp_unLo p then p else
      let n := rd32 ec (rd32 (fp_fm p) (fp_unLo p)) - med in
      if n =? 0 then
        fpart_lo f ec med (FP (fswap (fp_fm p) (fp_unLo p) (fp_ltLo p)) (fp_unLo p + 1) (fp_unHi p) (fp_ltLo p + 1) (fp_gtHi p))
      else if 0 <? n then p
      else fpart_lo f ec med (FP (fp_fm p) (fp_unLo p + 1) (fp_unHi p) (fp_ltLo p) (fp_gtHi p))
  end.
(* [comment removed for export] *)
Fixpoint fpart_hi (fuel : nat) (ec : zarr) (med : Z) (p : fpart) : fpart :=
  match fuel with
  | O => p
  | S f =>
      if fp_unHi p <? fp_unLo p then p else
      let n := rd32 ec (rd32 (fp_fm p) (fp_unHi p)) - med in
      if n =? 0 then
        fpart_hi f ec med (FP (fswap (fp_fm p) (fp_unHi p) (fp_gtHi p)) (fp_unLo p) (fp_unHi p - 1) (fp_ltLo p) (fp_gtHi p - 1))
      else if n <? 0 then p
      else fpart_hi f ec med (FP (fp_fm p) (fp_unLo p) (fp_unHi p - 1) (fp_ltLo p) (fp_gtHi p))
  end.
(* [comment removed for export] *)
Fixpoint fpart_loop (fuel : nat) (sz : nat) (ec : zarr) (med : Z) (p : fpart) : fpart :=
  match fuel with
  | O => p
  | S f =>
      let p1 := fpart_lo (S sz) ec med p in
      let p2 := fpart_hi (S sz) ec med p1 in
      if fp_unHi p2 <? fp_unLo p2 then p2
      else fpart_loop f sz ec med
             (FP (fswap (fp_fm p2) (fp_unLo p2) (fp_unHi p2)) (fp_unLo p2 + 1) (fp_unHi p2 - 1) (fp_ltLo p2) (fp_gtHi p2))
  end.

(* [comment removed for export] *)
Record fqs := FQS { fq_fm : zarr; fq_sp : Z; fq_slo : zarr; fq_shi : zarr; fq_r : Z }.

Definition fpush (q : fqs) (lz hz : Z) : fqs :=
  FQS (fq_fm q) (fq_sp q + 1) (zset (fq_slo q) (fq_sp q) lz) (zset (fq_shi q) (fq_sp q) hz) (fq_r q).

Definition fmin (a b : Z) : Z := if a <? b then a else b.

(* [comment removed for export] *)
Definition fqs_iter (ec : zarr) (q : fqs) : fqs :=
  let sp := fq_sp q - 1 in
  let lo := zget (fq_slo q) sp in
  let hi := zget (fq_shi q) sp in
  let q1 := FQS (fq_fm q) sp (fq_slo q) (fq_shi q) (fq_r q) in
  if hi - lo <? 10 then
    FQS (fallbackSimpleSort (fq_fm q) ec lo hi) sp (fq_slo q) (fq_shi q) (fq_r q)
  else
    let r := ((fq_r q * 7621) + 1) mod 32768 in
    let r3 := r mod 3 in
    let fm := fq_fm q in
    let med := if r3 =? 0 then rd32 ec (rd32 fm lo)
               else if r3 =? 1 then rd32 ec (rd32 fm (Z.shiftr (lo + hi) 1))
               else rd32 ec (rd32 fm hi) in
    let sz := Z.to_nat (hi - lo + 1) in
    let p := fpart_loop (S sz) sz ec med (FP fm lo hi lo hi) in
    let unLo := fp_unLo p in let unHi := fp_unHi p in let ltLo := fp_ltLo p in let gtHi := fp_gtHi p in
    if gtHi <? ltLo then FQS (fp_fm p) sp (fq_slo q) (fq_shi q) r
    else
      let n := fmin (ltLo - lo) (unLo - ltLo) in
      let fm1 := fvswap (S (Z.to_nat n)) (fp_fm p) lo (unLo - n) n in
      let m := fmin (hi - gtHi) (gtHi - unHi) in
      let fm2 := fvswap (S (Z.to_nat m)) fm1 unLo (hi - m + 1) m in
      let n' := lo + unLo - ltLo - 1 in
      let m' := hi - (gtHi - unHi) + 1 in
      let q2 := FQS fm2 sp (fq_slo q) (fq_shi q) r in
      if hi - m' <? n' - lo then fpush (fpush q2 lo n') m' hi
      else fpush (fpush q2 m' hi) lo n'.

Fixpoint fqs_loop (fuel : nat) (ec : zarr) (q : fqs) : fqs :=
  match fuel with
  | O => q
  | S f => if 0 <? fq_sp q then fqs_loop f ec (fqs_iter ec q) else q
  end.
Lemma fqs_loop_S : forall f ec q, fqs_loop (S f) ec q = (if 0 <? fq_sp q then fqs_loop f ec (fqs_iter ec q) else q).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition fqs_fuel (loSt hiSt : Z) : nat := Z.to_nat (2 * (hiSt - loSt) + 8).

(* [comment removed for export] *)
Definition fallbackQSort3 (fm ec slo shi : zarr) (loSt hiSt : Z) : fqs :=
  fqs_loop (fqs_fuel loSt hiSt) ec (fpush (FQS fm 0 slo shi 0) loSt hiSt).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bh_word (bh : zarr) (zz : Z) : Z := zget bh (Z.shiftr zz 5).
Definition set_bh (bh : zarr) (zz : Z) : zarr :=
  zset bh (Z.shiftr zz 5) (Z.lor (bh_word bh zz) (Z.shiftl 1 (Z.land zz 31))).
Definition clear_bh (bh : zarr) (zz : Z) : zarr :=
  zset bh (Z.shiftr zz 5) (Z.land (bh_word bh zz) (Z.lxor (Z.shiftl 1 (Z.land zz 31)) 4294967295)).
Definition isset_bh (bh : zarr) (zz : Z) : bool :=
  negb (Z.land (bh_word bh zz) (Z.shiftl 1 (Z.land zz 31)) =? 0).
Definition unaligned_bh (zz : Z) : bool := negb (Z.land zz 31 =? 0).

(* [comment removed for export] *)
Fixpoint fs_ftab_zero (n : nat) (ft : zarr) (i : Z) : zarr :=
  match n with O => ft | S n' => fs_ftab_zero n' (zset ft i 0) (i + 1) end.
(* [comment removed for export] *)
Fixpoint fs_count (n : nat) (ft ec : zarr) (i : Z) : zarr :=
  match n with O => ft | S n' => fs_count n' (zincr ft (rd8 ec i)) ec (i + 1) end.
(* [comment removed for export] *)
Fixpoint fs_copy (n : nat) (fc ft : zarr) (i : Z) : zarr :=
  match n with O => fc | S n' => fs_copy n' (zset fc i (zget ft i)) ft (i + 1) end.
(* [comment removed for export] *)
Fixpoint fs_accum (n : nat) (ft : zarr) (i : Z) : zarr :=
  match n with O => ft | S n' => fs_accum n' (zset ft i (zget ft i + zget ft (i - 1))) (i + 1) end.
(* [comment removed for export] *)
Fixpoint fs_distrib (n : nat) (ft fm ec : zarr) (i : Z) : zarr * zarr :=
  match n with
  | O => (ft, fm)
  | S n' => let j := rd8 ec i in let k := zget ft j - 1 in
            fs_distrib n' (zset ft j k) (wr32 fm k i) ec (i + 1)
  end.
(* [comment removed for export] *)
Fixpoint fs_bh_zero (n : nat) (bh : zarr) (i : Z) : zarr :=
  match n with O => bh | S n' => fs_bh_zero n' (zset bh i 0) (i + 1) end.
(* [comment removed for export] *)
Fixpoint fs_bh_init (n : nat) (bh ft : zarr) (i : Z) : zarr :=
  match n with O => bh | S n' => fs_bh_init n' (set_bh bh (zget ft i)) ft (i + 1) end.
(* [comment removed for export] *)
Fixpoint fs_sentinel (n : nat) (bh : zarr) (nblock i : Z) : zarr :=
  match n with
  | O => bh
  | S n' => fs_sentinel n' (clear_bh (set_bh bh (nblock + 2 * i)) (nblock + 2 * i + 1)) nblock (i + 1)
  end.

(* [comment removed for export] *)
Fixpoint fs_eclass (n : nat) (ec fm bh : zarr) (H nblock i j : Z) : zarr :=
  match n with
  | O => ec
  | S n' =>
      let j' := if isset_bh bh i then i else j in
      let k := rd32 fm i - H in
      let k' := if k <? 0 then k + nblock else k in
      fs_eclass n' (wr32 ec k' j') fm bh H nblock (i + 1) j'
  end.

(* [comment removed for export] *)
Fixpoint fs_scan_set_unal (fuel : nat) (bh : zarr) (k : Z) : Z :=      (* [comment removed for export] *)
  match fuel with O => k | S f => if isset_bh bh k && unaligned_bh k then fs_scan_set_unal f bh (k + 1) else k end.
Fixpoint fs_scan_word_ff (fuel : nat) (bh : zarr) (k : Z) : Z :=       (* [comment removed for export] *)
  match fuel with O => k | S f => if bh_word bh k =? 4294967295 then fs_scan_word_ff f bh (k + 32) else k end.
Fixpoint fs_scan_set (fuel : nat) (bh : zarr) (k : Z) : Z :=           (* [comment removed for export] *)
  match fuel with O => k | S f => if isset_bh bh k then fs_scan_set f bh (k + 1) else k end.
Fixpoint fs_scan_clr_unal (fuel : nat) (bh : zarr) (k : Z) : Z :=      (* [comment removed for export] *)
  match fuel with O => k | S f => if negb (isset_bh bh k) && unaligned_bh k then fs_scan_clr_unal f bh (k + 1) else k end.
Fixpoint fs_scan_word_00 (fuel : nat) (bh : zarr) (k : Z) : Z :=       (* [comment removed for export] *)
  match fuel with O => k | S f => if bh_word bh k =? 0 then fs_scan_word_00 f bh (k + 32) else k end.
Fixpoint fs_scan_clr (fuel : nat) (bh : zarr) (k : Z) : Z :=           (* [comment removed for export] *)
  match fuel with O => k | S f => if negb (isset_bh bh k) then fs_scan_clr f bh (k + 1) else k end.

(* [comment removed for export] *)
Fixpoint fs_headers (n : nat) (bh ec fm : zarr) (i cc : Z) : zarr :=
  match n with
  | O => bh
  | S n' => let cc1 := rd32 ec (rd32 fm i) in
            if negb (cc =? cc1) then fs_headers n' (set_bh bh i) ec fm (i + 1) cc1
            else fs_headers n' bh ec fm (i + 1) cc
  end.

(* [comment removed for export] *)
Record fbs := FBS { fb_fm : zarr; fb_ec : zarr; fb_bh : zarr; fb_slo : zarr; fb_shi : zarr; fb_r : Z; fb_nnd : Z; fb_done : bool }.

(* [comment removed for export] *)
Definition fs_bucket_iter (nblock : Z) (s : fbs) : fbs :=
  let bh := fb_bh s in
  let F := Z.to_nat (nblock + 70) in
  let k := fb_r s + 1 in
  let k := fs_scan_set_unal F bh k in
  let k := if isset_bh bh k then fs_scan_set F bh (fs_scan_word_ff F bh k) else k in
  let l := k - 1 in
  if nblock <=? l then FBS (fb_fm s) (fb_ec s) bh (fb_slo s) (fb_shi s) (fb_r s) (fb_nnd s) true else
  let k := fs_scan_clr_unal F bh k in
  let k := if negb (isset_bh bh k) then fs_scan_clr F bh (fs_scan_word_00 F bh k) else k in
  let r := k - 1 in
  if nblock <=? r then FBS (fb_fm s) (fb_ec s) bh (fb_slo s) (fb_shi s) r (fb_nnd s) true else
  if l <? r then
    let nnd := fb_nnd s + (r - l + 1) in
    let q := fallbackQSort3 (fb_fm s) (fb_ec s) (fb_slo s) (fb_shi s) l r in
    let fm := fq_fm q in
    let bh' := fs_headers (Z.to_nat (r - l + 1)) bh (fb_ec s) fm l (-1) in
    FBS fm (fb_ec s) bh' (fq_slo q) (fq_shi q) r nnd false
  else FBS (fb_fm s) (fb_ec s) bh (fb_slo s) (fb_shi s) r (fb_nnd s) false.

Fixpoint fs_bucket_loop (fuel : nat) (nblock : Z) (s : fbs) : fbs :=
  match fuel with
  | O => s
  | S f => if fb_done s then s else fs_bucket_loop f nblock (fs_bucket_iter nblock s)
  end.

(* [comment removed for export] *)
Record fhs := FHS { fh_fm : zarr; fh_ec : zarr; fh_bh : zarr; fh_slo : zarr; fh_shi : zarr; fh_H : Z; fh_done : bool }.

(* [comment removed for export] *)
Definition fs_H_iter (nblock : Z) (s : fhs) : fhs :=
  let ec := fs_eclass (Z.to_nat nblock) (fh_ec s) (fh_fm s) (fh_bh s) (fh_H s) nblock 0 0 in
  let b := fs_bucket_loop (Z.to_nat (nblock + 2)) nblock (FBS (fh_fm s) ec (fh_bh s) (fh_slo s) (fh_shi s) (-1) 0 false) in
  let H := fh_H s * 2 in
  FHS (fb_fm b) (fb_ec b) (fb_bh b) (fb_slo b) (fb_shi b) H ((nblock <? H) || (fb_nnd b =? 0)).

Fixpoint fs_H_loop (fuel : nat) (nblock : Z) (s : fhs) : fhs :=
  match fuel with
  | O => s
  | S f => if fh_done s then s else fs_H_loop f nblock (fs_H_iter nblock s)
  end.

(* [comment removed for export] *)
Fixpoint fs_skip0 (fuel : nat) (fc : zarr) (j : Z) : Z :=
  match fuel with O => j | S f => if zget fc j =? 0 then fs_skip0 f fc (j + 1) else j end.
Fixpoint fs_rebuild (n : nat) (ec fc fm : zarr) (i j : Z) : zarr * zarr * Z :=
  match n with
  | O => (ec, fc, j)
  | S n' => let j := fs_skip0 258%nat fc j in
            let fc := zset fc j (zget fc j - 1) in
            fs_rebuild n' (wr8 ec (rd32 fm i) j) fc fm (i + 1) j
  end.

(* [comment removed for export] *)
Record fsres := FSR { fr_fm : zarr; fr_ec : zarr; fr_bh : zarr; fr_ftab : zarr; fr_fcopy : zarr; fr_slo : zarr; fr_shi : zarr; fr_j : Z }.

Definition fallbackSort (fm ec bh ftab0 fcopy0 slo0 shi0 : zarr) (nblock : Z) : fsres :=
  let ft := fs_ftab_zero 257%nat ftab0 0 in
  let ft := fs_count (Z.to_nat nblock) ft ec 0 in
  let fc := fs_copy 256%nat fcopy0 ft 0 in
  let ft := fs_accum 256%nat ft 1 in
  let '(ft, fm) := fs_distrib (Z.to_nat nblock) ft fm ec 0 in
  let nBhtab := 2 + nblock / 32 in
  let bh := fs_bh_zero (Z.to_nat nBhtab) bh 0 in
  let bh := fs_bh_init 256%nat bh ft 0 in
  let bh := fs_sentinel 32%nat bh nblock 0 in
  let hs := fs_H_loop (Z.to_nat 64) nblock (FHS fm ec bh slo0 shi0 1 false) in
  let '(ec', fc', j) := fs_rebuild (Z.to_nat nblock) (fh_ec hs) fc (fh_fm hs) 0 0 in
  FSR (fh_fm hs) ec' (fh_bh hs) ft fc' (fh_slo hs) (fh_shi hs) j.
