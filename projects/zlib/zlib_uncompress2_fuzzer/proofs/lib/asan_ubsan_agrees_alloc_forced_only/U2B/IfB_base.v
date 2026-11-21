(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes Image ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation amem := (word -> option byte).
Section CANSEC1. Context {rc : runConstT}.

Definition if_locals (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 : word) : list cell :=
  [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72; C8 v80; C8 v88; C8 v96; C8 v104; C8 v112; C8 v120; C8 v128;
   C8 v136; C8 v144; C8 v152; C8 v160].

Definition if_frm (Zs S OB bo wsz whave wnext Wd lb db : Z) : list cell :=
  if_locals (Z_to_bv 64 (wnext + wsz)) (Z_to_bv 64 (S + 7160)) (Z_to_bv 64 whave) (Z_to_bv 64 (OB + bo)) (Z_to_bv 64 Wd) (Z_to_bv 64 (2 ^ db - 1))
            (Z_to_bv 64 (Z.shiftr (S + 104) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (S + 96) 3 + 2147450880)) (Z_to_bv 64 (S + 104)) (Z_to_bv 64 (S + 96))
            (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880)) (Z_to_bv 64 (Zs + 32)) (Z_to_bv 64 (Z.shiftr (Zs + 24) 3 + 2147450880)) (Z_to_bv 64 (Zs + 24))
            (Z_to_bv 64 (Z.shiftr (Zs + 8) 3 + 2147450880)) (Z_to_bv 64 (Zs + 8)) (Z_to_bv 64 (Z.shiftr Zs 3 + 2147450880))
            (Z_to_bv 64 wsz) (Z_to_bv 64 wnext) (Z_to_bv 64 1) (Z_to_bv 64 (2 ^ lb - 1)).

Definition ifW (SP Zs S OB osz : Z) : list (Z * Z) :=
  [(SP - 272, SP - 104); (Zs, Zs + 56); (S + 8, S + 12); (S + 96, S + 108); (OB, OB + osz)].

Definition xms (SP Zs S D n OB osz la da : Z) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x10 x11 x14 x15 x19 x24 x28 x29 x30 : word) (ci hold bits : Z) (pc : Z) (m : amem) : machine_state :=
  MS (mkR (Z_to_bv 64 31) (Z_to_bv 64 (SP + -272)) gp tp x5 x6 x7
          (Z_to_bv 64 (Z.lxor la 18446744073709551615)) (Z_to_bv 64 (Z.lxor da 18446744073709551615)) x10 x11 (Z_to_bv 64 Zs)
          (Z_to_bv 64 (D + ci)) x14 x15 (Z_to_bv 64 (OB + osz - 257)) (Z_to_bv 64 la) (Z_to_bv 64 (D + n - 5)) x19
          (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 S) (Z_to_bv 64 63) x24 (Z_to_bv 64 hold) (Z_to_bv 64 bits) (Z_to_bv 64 da)
          x28 x29 x30 (Z_to_bv 64 (-1)))
     FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs).
Definition gms (SP Zs S D n OB osz la da : Z) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 : word) (ci co hold bits : Z) (pc : Z) (m : amem) : machine_state :=
  xms SP Zs S D n OB osz la da gp tp FR fc x5 x6 x7 x10 x11 x14 x15 (Z_to_bv 64 (OB + co)) x24 x28 x29 x30 ci hold bits pc m.
Definition oms (SP Zs S D n OB osz la da : Z) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32)
    (x5 x7 x10 x11 x14 x15 x19 x24 x28 x29 x30 : word) (ci co hold bits : Z) (pc : Z) (m : amem) : machine_state :=
  xms SP Zs S D n OB osz la da gp tp FR fc x5 (Z_to_bv 64 (OB + co)) x7 x10 x11 x14 x15 x19 x24 x28 x29 x30 ci hold bits pc m.
Definition fms (SP Zs S D n OB osz la da : Z) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32)
    (x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 : word) (ci co hold bits : Z) (pc : Z) (m : amem) : machine_state :=
  gms SP Zs S D n OB osz la da gp tp FR fc (Z_to_bv 64 14) x6 x7 x10 x11 x14 x15 x24 x28 x29 x30 ci co hold bits pc m.

Definition fW (n osz ci bits co : Z) : Z := 8 * (n - ci) + bits + (osz - co).

Definition if_tab (RNG : footprint) (W : list (Z * Z)) (m1 : amem) (A na : Z) (rd : Z -> Z) : Prop :=
  bytes_at bsegs m1 A (u32s (fws rd (Z.to_nat na))) /\ A mod 4 = 0 /\ 0 < A /\ 0 <= na /\ A + 4 * na <= 2 ^ 47 /\ rng RNG A (4 * na)
  /\ (forall i, 0 <= i < na -> 0 <= rd i < 4294967296)
  /\ disjoint_from W A (4 * na)
  /\ exists s1 s2, shadow_bytes m1 s1 s2 (fun _ => 0) /\ rng RNG s1 (s2 - s1) /\ disjoint_from W s1 (s2 - s1)
                   /\ s1 <= Z.shiftr A 3 + 2147450880 /\ Z.shiftr (A + 4 * na - 1) 3 + 2147450880 < s2.

Definition if_ctx (RNG : footprint) (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z)
    (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem) : Prop :=
  let W := ifW SP Zs S OB osz in
  (Zs mod 8 = 0 /\ S mod 16 = 0 /\ OB mod 8 = 0 /\ D mod 8 = 0 /\ 0 < Zs /\ Zs + 112 <= lo /\ 0 < S /\ S + 7176 <= lo /\ 1 <= D /\ D + n <= lo /\
   0 < OB /\ OB + osz <= lo /\ 17594333495296 <= lo /\ lo <= SP - 272 /\ SP + 16 < 140737488355328 /\
   (Zs + 112 <= S \/ S + 7176 <= Zs) /\ (Zs + 112 <= OB \/ OB + osz <= Zs) /\ (S + 7176 <= OB \/ OB + osz <= S)) /\
  (6 <= n < 67108864 /\ 258 <= osz <= 262144 /\ 1 <= lb <= 15 /\ 1 <= db <= 15 /\ 0 <= bo /\
   0 <= whave <= wsz /\ 0 <= wnext <= wsz /\ (wsz = 0 \/ wsz = 32768) /\ (wnext = 0 \/ whave = wsz \/ wnext = whave)) /\
  (rng RNG (SP - 272) 272 /\ rng RNG Zs 112 /\ rng RNG (Z.shiftr Zs 3 + 2147450880) 14 /\ rng RNG S 7176 /\
   rng RNG (Z.shiftr S 3 + 2147450880) 897 /\ rng RNG D n /\ rng RNG (Z.shiftr D 3 + 2147450880) (n / 8 + 1) /\
   rng RNG OB osz /\ rng RNG (Z.shiftr OB 3 + 2147450880) ((osz + 7) / 8) /\ rng_aimg RNG) /\
  (shadow_bytes m1 (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0) /\
   shadow_bytes m1 (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0) /\
   shadow_bytes m1 (Z.shiftr OB 3 + 2147450880) (Z.shiftr OB 3 + 2147450880 + (osz + 7) / 8) (fun _ => 0) /\
   disjoint_from W (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14 - (Z.shiftr Zs 3 + 2147450880)) /\
   disjoint_from W (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880)) /\
   disjoint_from W (Z.shiftr OB 3 + 2147450880) (Z.shiftr OB 3 + 2147450880 + (osz + 7) / 8 - (Z.shiftr OB 3 + 2147450880))) /\
  (if_tab RNG W m1 la na rdL /\ if_tab RNG W m1 da nd rdD /\ tab_ok LENS rdL lb na = true /\ tab_ok DISTS rdD db nd = true /\
   bytes_at bsegs m1 D (map (Z_to_bv 8) payload) /\ Forall (fun c => 0 <= c < 256) payload /\ Z.of_nat (length payload) = n /\
   unpoisoned m1 D (D + n) /\ disjoint_from W D n /\
   disjoint_from W (shad D) (shad (D + n - 1) + 1 - shad D) /\
   rw_cells bsegs m1 (S + 7160) [C4 (Z_to_bv 64 1)] /\
   (forall i, 0 <= i < 32768 -> 0 <= fw i < 256) /\
   (wsz <> 0 -> f8arr bsegs m1 Wd 32768 fw /\ Wd mod 8 = 0 /\ 0 < Wd /\ Wd + 32768 <= lo /\ rng RNG Wd 32768 /\
                rng RNG (Z.shiftr Wd 3 + 2147450880) 4096 /\ disjoint_from W Wd 32768 /\
                shadow_bytes m1 (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096) (fun _ => 0) /\
                disjoint_from W (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096 - (Z.shiftr Wd 3 + 2147450880)))).

Record sdc := SDC { d_ti : word; d_to : word; d_alloc : word; d_free : word; d_opq : word; d_dt : word; d_adl : word; d_res : word;
                    d_p1 : word; d_p2 : word; d_p3 : word }.
Record idc := IDC { i_strm : word; i_last : word; i_wrap : word; i_havedict : word; i_flags : word; i_dmax : word; i_check : word;
                    i_total : word; i_head : word; i_wbits : word; i_length : word; i_offset : word; i_extra : word;
                    i_ncode : word; i_nlen : word; i_ndist : word; i_have : word; i_next : word }.
Definition if_sc (S : Z) (sd : sdc) (ni ai no ao msg : word) : list cell :=
  strm_cells ni ai (d_ti sd) no ao (d_to sd) msg (Z_to_bv 64 S) (d_alloc sd) (d_free sd) (d_opq sd) (d_dt sd) (d_adl sd) (d_res sd)
             (d_p1 sd) (d_p2 sd) (d_p3 sd).
Definition if_ic (wsz whave wnext Wd la da lb db : Z) (id : idc) (mode hw bw : word) : list cell :=
  istate_cells (i_strm id) mode (i_last id) (i_wrap id) (i_havedict id) (i_flags id) (i_dmax id) (i_check id) (i_total id) (i_head id)
               (i_wbits id) (Z_to_bv 64 wsz) (Z_to_bv 64 whave) (Z_to_bv 64 wnext) (Z_to_bv 64 Wd) hw bw
               (i_length id) (i_offset id) (i_extra id) (Z_to_bv 64 la) (Z_to_bv 64 da) (Z_to_bv 64 lb) (Z_to_bv 64 db)
               (i_ncode id) (i_nlen id) (i_ndist id) (i_have id) (i_next id).

Definition if_inv (SP Zs S OB osz bo wsz whave wnext Wd la da lb db : Z) (m1 m : amem)
    (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word) (fo : Z -> Z) : Prop :=
  mem_inv bsegs m /\ munch (ifW SP Zs S OB osz) m1 m /\ wmono bsegs m1 m /\
  rw_cells bsegs m (SP + -272) (if_frm Zs S OB bo wsz whave wnext Wd lb db) /\
  rw_cells bsegs m Zs (if_sc S sd ni ai no ao msg) /\ rw_cells bsegs m S (if_ic wsz whave wnext Wd la da lb db id mode hw bw) /\
  f8arr bsegs m OB (Z.to_nat osz) fo /\ (forall i, 0 <= i < osz -> 0 <= fo i < 256).

End CANSEC1.
