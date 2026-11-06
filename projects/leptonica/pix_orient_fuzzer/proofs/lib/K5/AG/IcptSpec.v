(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import StrFun.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_IcptSpec () := "K47Corelib7Numbers7BinNums1Z03K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02c69OSSVerify5KrLib2K52AG8IcptSpec;strncmp_resC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib2K52AG8IcptSpec:strncmp_szC1?~~~~~~~~~~~~~~~".
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
Proof.
ltac2:(KReplay.run1 (kr_t_IcptSpec ()) [] "p;1p;2p;3g0000j1;Tg000Nj2:Tg000hj12Tg001Mj13Tg001kj10Tg002Pj19Tg002nj17Tg003Qj24Tg0047j16Tg004Wj31Tg0057j35Tg0066j38Tg006PR0g006nR1#;R2':%21R3#3%01#0#0#9R1#7R4%03#0R3#0R5#0#2#3,41R6%25R5#0#3,41R7%25#3,41%64R551451431%23#0#0#3,41=1459147914635=802do"). Qed.
Example strncmp_res_ex2 : strncmp_res 2 [Z_to_bv 8 97; Z_to_bv 8 98; Z_to_bv 8 99] [Z_to_bv 8 97; Z_to_bv 8 98; Z_to_bv 8 100] = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_IcptSpec ()) [] "p;2p;1p;3g000Nj2:Tg001kj10Tg001Mj12Tg002Pj15Tg002nj19Tg000hj13Tg003Qj24Tg0047j16Tg004Wj31Tg0057j37Tg0066j38Tg006PR0g007SR1':g006nR2#0R3#2%03#0#5R3#9R4%32#0#0R2#0R5#0#3#2,43R6%35R5#0#2,43R7%35#2,43%64R551451431%32#0#0#2,43=1459147914637=801do"). Qed.
Example strncmp_sz_ex : strncmp_sz 11 [Z_to_bv 8 97; Z_to_bv 8 0] [Z_to_bv 8 98] = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_IcptSpec ()) [] "p;1p;2p;3g001Mj12Tg000Nj2:Tg001kj10Tg000hj11Tg002Pj19Tg002nj18Tg003Qj24Tg0047j16Tg004Wj33Tg0081j37Tg0066j35Tg006PR0g006nR1#2R2':%01R3#1#1#2%03#0#9R3#8R4%11#0#0#0R1#0#1#2,43g007S,43%64R553433%11#0#2,43=34537=502do"). Qed.
