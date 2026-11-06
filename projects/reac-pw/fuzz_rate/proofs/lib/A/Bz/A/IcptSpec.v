(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/A/IcptSpec.v, with its module paths changed; 4 of its 38 lines of code are new or changed and 3 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/IcptSpec.v (cold/port-fm-rtprintf-param 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/Bz/A/IcptSpec.table). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Bz/A/IcptSpec.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* Ported by RtStr from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/IcptSpec.v, unchanged. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition memchr_chk (c n : Z) (buf : list byte) : Z :=
  match find_byte c (firstn (Z.to_nat n) buf) with Some i => Z.of_nat i + 1 | None => n end.

(* [comment removed for export] *)
Definition strnlen_ok (s n : Z) (buf : list byte) : Prop := memchr_ok s 0 n buf.
Definition strnlen_chk (n : Z) (buf : list byte) : Z := memchr_chk 0 n buf.

(* [comment removed for export] *)
Definition strnlen_known (k : Z) (buf : list byte) : Prop := Z.min (strnlen_res k buf + 1) k <= Z.of_nat (length buf).

(* [comment removed for export] *)
Fixpoint strncmp_idx_aux (b1 b2 : list byte) (k : nat) : nat :=
  match k with
  | O => O
  | S k' => match b1, b2 with
            | x :: b1', y :: b2' => if negb (bv_unsigned x =? bv_unsigned y) || (bv_unsigned x =? 0) then O
                                    else S (strncmp_idx_aux b1' b2' k')
            | _, _ => O
            end
  end.
Definition strncmp_idx (n : Z) (b1 b2 : list byte) : Z := Z.of_nat (strncmp_idx_aux b1 b2 (Z.to_nat n)).
Definition strncmp_sz (n : Z) (b1 b2 : list byte) : Z := Z.min (strncmp_idx n b1 b2 + 1) n.
(* [comment removed for export] *)
Definition strncmp_ok (n : Z) (b1 b2 : list byte) : Prop :=
  strncmp_sz n b1 b2 <= Z.of_nat (length b1) /\ strncmp_sz n b1 b2 <= Z.of_nat (length b2).
Definition strncmp_res (n : Z) (b1 b2 : list byte) : Z :=
  let i := Z.to_nat (strncmp_idx n b1 b2) in
  if strncmp_idx n b1 b2 =? n then 0
  else match nth_error b1 i, nth_error b2 i with
       | Some x, Some y => if bv_unsigned x <? bv_unsigned y then -1 else if bv_unsigned y <? bv_unsigned x then 1 else 0
       | _, _ => 0
       end.

Example strncmp_res_ex1 : strncmp_res 3 [Z_to_bv 8 97; Z_to_bv 8 98; Z_to_bv 8 99] [Z_to_bv 8 97; Z_to_bv 8 98; Z_to_bv 8 100] = -1.
Proof. vm_compute. reflexivity. Qed.
Example strncmp_res_ex2 : strncmp_res 2 [Z_to_bv 8 97; Z_to_bv 8 98; Z_to_bv 8 99] [Z_to_bv 8 97; Z_to_bv 8 98; Z_to_bv 8 100] = 0.
Proof. vm_compute. reflexivity. Qed.
Example strncmp_sz_ex : strncmp_sz 11 [Z_to_bv 8 97; Z_to_bv 8 0] [Z_to_bv 8 98] = 1.
Proof. vm_compute. reflexivity. Qed.
