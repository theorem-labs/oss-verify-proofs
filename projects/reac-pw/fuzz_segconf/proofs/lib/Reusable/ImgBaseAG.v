(* copied from proofs/cgif/cgif_file_fuzzer/lib/ImgBaseAG.v @ 95e6f1d72b6 (c-asan, frozen), module paths changed only. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* The image facts of the PRIMARY Allocate interface (AGif0n), and the image-free geometry it borrows.

   [AGImg] holds what AGif0n's statements say about the image beyond [AImg] (ImgBase.v): the allocator instance's
   window, the two zones, the shadow map's offset and the three code addresses.  An instance file (cgif_file:
   AGif0cgif.v) gives them their values; a relocated target gives its own.

   The rest of this file is the geometry AGif0n reads out of the walk files AGis (the g path) and AGj6 (the k
   path), whose bodies have no image content: it is COPIED here so that the walk files and their proofs stay as
   they are (c-asan 2026-10-29 02:30Z).  Each copy carries the line it came from and goes away when that file is
   ported.  [SHBv] is NOT a copy: the walk files write the shadow map's offset as a literal, and here it is the
   field [ag_shadow], so that every definition below it copies byte for byte. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YGAlloc ImgBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The image facts of the primary interface.                                                                        *)
Class AGImg {IM : AImg} : Type := MkAGImg {
  (* the allocator instance's window (cgif_file: AGif0cgif.inst_ok) *)
  ag_inst_ok : Z -> Prop;
  (* the constant cells' zone and the depot's write zone (cgif_file: AGif0cgif.CZONE; AGis.DZONE = AGj6.DZONE) *)
  ag_czone : alayout -> Z -> Prop;
  ag_dzone : alayout -> Z -> Prop;
  (* the shadow map's offset (cgif_file: AGis.SHBv) *)
  ag_shadow : Z;
  (* the depot's entry, the refill callee's entry, and the return address into Allocate after the refill call *)
  ag_depot_put : Z;
  ag_refill : Z;
  ag_refill_ret : Z
}.
Context {IM : AImg} {AG : AGImg}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The image-free geometry, copied from the walk files.                                                             *)
(* copy of YFhy.v:45, remove when YFhy.v is ported *)
Definition rz_of (k : Z) : Z := 16 * 2 ^ k.
(* copy of AGhy.v:38, remove when AGhy.v is ported *)
Definition AFSTACK : Z := 4096.
(* copy of AGis.v:67, remove when AGis.v is ported *)
Definition hdr_byte1 (jb : Z) : Z :=
zcanon (Z.lor (zcanon (Z.land (zcanon (Z.lor (zcanon (Z.land (zcanon (Z.lor (zcanon (Z.land (zcanon (jb + 0)) (zcanon (-4)))) (zcanon 1))) (zcanon 143))) (zcanon 16))) (zcanon 243))) (zcanon 0)).
(* The shadow map's offset, as the interface sees it (the walk files write the literal). *)
Definition SHBv : Z := ag_shadow.

(* The model-level names of the primary path. *)
(* copy of YFl0.v:58, remove when YFl0.v is ported *)
Definition DEP_STK : Z := 512.
(* copy of YFl1.v:23, remove when YFl1.v is ported *)
Definition RSTACK : Z := 1024.
(* copy of YFl0.v:59, remove when YFl0.v is ported *)
Definition depot_after (z : Z) (tr : list Z) (S : astate) : astate :=
if z =? 0 then S else set_depot (st_depot S ++ [tr]) S.
(* copy of YFi3.v:22, remove when YFi3.v is ported *)
Definition st_popped (S : astate) (cl : Z) (l : list Z) : astate :=
set_cache (zupd cl (mkPC (pc_max (cache S cl)) l) (st_cache S)) S.
(* copy of YFi3.v:24, remove when YFi3.v is ported *)
Definition pop_part (c : Z) : M (option Z) :=
p <- get_pc c ;;
match pc_chunks p with
| [] => ret None
| l => let off := last l 0 in
set_pc c (mkPC (pc_max p) (removelast l)) ;;
ret (Some (region_off c + off))
end.
(* copy of YFi3.v:48, remove when YFi3.v is ported *)
Definition new_chunk (cl off n : Z) : chunk := mkChunk (PPrim (region_off cl + off)) n CAllocated.
(* copy of YFi3.v:49, remove when YFi3.v is ported *)
Definition st_final (S : astate) (cl : Z) (l : list Z) (off n : Z) (tr : list Z) (z : Z) : astate :=
let s1 := depot_after z tr (st_popped S cl l) in
set_chunks (upd_chunk (st_chunks s1) (new_chunk cl off n)) s1.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The g path's geometry (AGis's Section g, with the variables its definitions use).                                *)
Section g.
Variables (ly : alayout).
Variables (regs0 : bvmap 5 word) (n : Z).
Variables (cl cnt v : Z).
Variable kz : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
(* copy of AGis.v:159, remove when AGis.v is ported *)
Definition RZ : Z := rz_of kz.
(* copy of AGis.v:161, remove when AGis.v is ported *)
Definition N8D : Z := n / 8 * 8.
(* copy of AGis.v:162, remove when AGis.v is ported *)
Definition Pv : Z := T + t_cache + 80 * cl.
(* copy of AGis.v:163, remove when AGis.v is ported *)
Definition PVv : Z := Pv + 16 + 4 * (cnt - 1).
(* copy of AGis.v:164, remove when AGis.v is ported *)
Definition Kv : Z := SB + cl * 2 ^ 32 + 16 * v.
(* copy of AGis.v:166, remove when AGis.v is ported *)
Definition SKv : Z := SHBv + Kv / 8.
(* copy of AGis.v:167, remove when AGis.v is ported *)
Definition SSLOTv : Z := T + t_stats + 112 + 8 * cl.
(* copy of AGis.v:168, remove when AGis.v is ported *)
Definition PBv : Z := SHBv + (Kv + RZ + N8D) / 8.
(* copy of AGis.v:169, remove when AGis.v is ported *)
Definition Uv : Z := Kv + RZ.
(* copy of AGis.v:170, remove when AGis.v is ported *)
Definition SUv : Z := SHBv + Uv / 8.
(* copy of AGis.v:203, remove when AGis.v is ported *)
Definition WINT (a : Z) : Prop :=
(Pv <= a < Pv + 4) \/ (T + 2768 <= a < T + 2824) \/ (SSLOTv <= a < SSLOTv + 8) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
(* copy of AGis.v:205, remove when AGis.v is ported *)
Definition PBW (odd : bool) (a : Z) : Prop := odd = true /\ PBv <= a < PBv + 1.
(* copy of AGis.v:206, remove when AGis.v is ported *)
Definition WIN (odd : bool) (a : Z) : Prop :=
(sp0 - AFSTACK <= a < sp0) \/ WINT a \/ ((Kv <= a < Kv + 16) \/ (Uv - 16 <= a < Uv)) \/ PBW odd a.
End g.

(* ---------------------------------------------------------------------------------------------------------------- *)
End a.

(* The k path's geometry (AGj6's Section g: redzone 16, and the header size is NPv).                                *)
Module K6.
(* copy of AGj6.v:67, remove when AGj6.v is ported *)
Definition hdr_byte1 (jb : Z) : Z :=
zcanon (Z.lor (zcanon (Z.land (zcanon (Z.lor (zcanon (Z.land (zcanon (Z.lor (zcanon (Z.land (zcanon (jb + 0)) (zcanon (-4)))) (zcanon 1))) (zcanon 143))) (zcanon 16))) (zcanon 243))) (zcanon 0)).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {AG : AGImg}.
Local Open Scope am_scope.
Section g.
Variables (ly : alayout).
Variables (regs0 : bvmap 5 word) (n : Z).
Variables (cl cnt v : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
(* copy of AGj6.v:157, remove when AGj6.v is ported *)
Definition RZ : Z := 16.
(* copy of AGj6.v:158, remove when AGj6.v is ported *)
Definition NPv : Z := Z.max n 1.
(* copy of AGj6.v:160, remove when AGj6.v is ported *)
Definition N8D : Z := NPv / 8 * 8.
(* copy of AGj6.v:161, remove when AGj6.v is ported *)
Definition Pv : Z := T + t_cache + 80 * cl.
(* copy of AGj6.v:163, remove when AGj6.v is ported *)
Definition Kv : Z := SB + cl * 2 ^ 32 + 16 * v.
(* copy of AGj6.v:166, remove when AGj6.v is ported *)
Definition SSLOTv : Z := T + t_stats + 112 + 8 * cl.
(* copy of AGj6.v:167, remove when AGj6.v is ported *)
Definition PBv : Z := SHBv + (Kv + RZ + N8D) / 8.
(* copy of AGj6.v:168, remove when AGj6.v is ported *)
Definition Uv : Z := Kv + RZ.
(* copy of AGj6.v:169, remove when AGj6.v is ported *)
Definition SUv : Z := SHBv + Uv / 8.
(* copy of AGj6.v:203, remove when AGj6.v is ported *)
Definition WINT (a : Z) : Prop :=
(Pv <= a < Pv + 4) \/ (T + 2768 <= a < T + 2824) \/ (SSLOTv <= a < SSLOTv + 8) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
(* copy of AGj6.v:205, remove when AGj6.v is ported *)
Definition PBW (odd : bool) (a : Z) : Prop := odd = true /\ PBv <= a < PBv + 1.
(* copy of AGj6.v:206, remove when AGj6.v is ported *)
Definition WIN (odd : bool) (a : Z) : Prop :=
(sp0 - AFSTACK <= a < sp0) \/ WINT a \/ ((Kv <= a < Kv + 16) \/ (Uv - 16 <= a < Uv)) \/ PBW odd a.
End g.
End a.
End K6.
