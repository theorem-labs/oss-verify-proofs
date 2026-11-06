(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/AGif0cgif.v at 95e6f1d72b6 (sha256 1f95f9769bfa) into lib/B (libreac/fuzz_decode image B, fuzz_decode.asan-ubsan), with its module paths changed and its image numerals moved to fuzz_decode.asan-ubsan (pin sha256 5d05689fd5b1) by symbol + offset (alreloc 9b786608301; KEEP, regenerated and resolved values per proofs/libreac/fuzz_decode/provenance/alloc-reloc/B/resolve.txt); later the model label became the model's tag (449860 -> 12). *)
(* The cgif_file side of the primary Allocate interface AGif0n: cgif's machine-level predicates, the instance of the
   interface's image class ImgBaseAG.AGImg, and the lemmas that tie AGif0n to cgif_file's walk.

   - Section p: the predicates over cgif's image and AGis's geometry that the walk files read (AGiz / AGj0 / AGjd /
     AGje: [hview], [inst_ok]; AGix: [CZONE], [hit_writes]; the DG walk: [inst_ok], [CZONE]): the allocator
     instance's window [inst_ok] / [inst_ok_img], the constant cells' zone [CZONE], the hit-g view [hview], the
     hit-g writes [hit_writes] and the walk's frame [wframe].  They were AGif0.v's Section a, with these names and
     this text.  AGif0n restates hview / hit_writes / wframe over the class fields; at the cgif instance each is
     convertible with the one here.
   - [AGImg_cgif]: the allocator instance's window ([inst_ok]), the constant cells' zone ([CZONE]), the depot
     zone (AGis.DZONE, = AGj6.DZONE), the shadow map's offset (AGis.SHBv), and the three code addresses: the depot's
     entry (YFl0.A_StackDepotPut), the refill callee's entry (YFl1.A_Refill) and the return address into Allocate
     after the refill call ([A_REFILL_RET], a named constant so that the canonical projection has a constant key).
   - The lemmas moved out of the interface because they read cgif's walk: at_RET_w and at_RETk_w (AGis.at_RET /
     AGj6.at_RET give the interface's at_RETw / at_RETkw) and malloc_join_t_cgif (the interface's join with the spin
     tag 12 is YFi3.malloc_join).  Their statements and proofs are the ones AGif0n had; only the names are
     qualified.
   - hview_cgif: AGif0n's restated view gives [hview] of Section p, for a consumer (AGik, AGil) that passes the view
     on to a walk lemma stated over cgif's.
  A cgif_file consumer of AGif0n does [Require Import AGif2cgif AGif0cgif].  hview, hit_writes and wframe have the
  same short names here and in AGif0n, and the module imported LAST gives the short name: a consumer that means
  AGif0n's imports AGif0cgif before AGif0n. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YFhy AGhy AGis YFi3. From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YGAlloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require AGj6.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import ImgBase. From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import AGif2cgif.
(* ImgBaseAG and AGif0n are used qualified: importing them would hide AGis's geometry names behind the copies. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require ImgBaseAG AGif0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Machine-level predicates.                                                                                        *)

(* The allocator instance object [inst, inst + 0xe60): 8-aligned, in the image's data between the globals at
   0x9b168 and 0x9eb60 (the seed reads both; cgif_file's instance is TFIB_INST = 0x9dcd8). *)
Definition inst_ok (inst : Z) : Prop := 0x9b170 <= inst /\ inst + 0xe60 <= 0x9eb60 /\ inst mod 8 = 0.
Lemma inst_ok_img : forall inst, inst_ok inst -> TFIB_IMG_LO <= inst /\ inst + 0xe60 <= 0x173208.
Proof. intros inst (H1 & H2 & _). unfold TFIB_IMG_LO. lia. Qed.

(* The constant cells' zone: the cells of [as_const] lie here for the image tfib (AGix.const_cells_zone). *)
Definition CZONE (ly : alayout) (a : Z) : Prop :=
(0x10000 <= a < 0x5f6000) \/ (0x7fff8000 <= a < 0x800b6c00) \/ (ly_T ly <= a < ly_T ly + 80) \/ (ly_C ly <= a < ly_C ly + 160) \/
(TFIB_TSD <= a < TFIB_TSD + 8) \/ (ly_D ly <= a < ly_D ly + 4096).

(* (a) The view: the cells the hit-g seed (AGhy.SSG, regions REG0G) reads, for the cached chunk at class-region
   offset [16 * v] of class [cl] with [cnt] cached entries, over the instance [inst]. *)
Record hview (B : asyms) (W : world tfibsegs) (ly : alayout) (inst : Z) (mem : word -> option byte) (cl cnt v : Z) : Prop := {
  hv_ly : layout_ok ly;
  hv_img : img_cover ly;
  hv_tsd : ly_tsd ly = TFIB_TSD;
  hv_cnt : 1 <= cnt <= 16;
  hv_v : 0 <= v /\ v mod 2 = 0 /\ 16 * v + class_size cl <= 2 ^ 31;
  (* the image's constant cells (global literals, the thread and context objects' fixed words) *)
  hv_const : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly);
  (* the instance's fields: primary.space at +0x20, and the two words at +0xe20 *)
  hv_inst : val_mem tfibsegs (mrestrict (w_H W) mem) (inst + 0x20) 8 (ly_space ly) /\
            val_mem tfibsegs (mrestrict (w_H W) mem) (inst + 0xe20) 8 0x10000000000 /\
            val_mem tfibsegs (mrestrict (w_H W) mem) (inst + 0xe28) 8 0x108000010;
  (* the per-thread cache cell of the class: count, class size, the last entry *)
  hv_cache : val_mem tfibsegs (mrestrict (w_H W) mem) (Pv ly cl) 4 cnt /\
             val_mem tfibsegs (mrestrict (w_H W) mem) (Pv ly cl + 8) 8 (class_size cl) /\
             val_mem tfibsegs (mrestrict (w_H W) mem) (PVv ly cl cnt) 4 v;
  (* the thread's unwinding flag is clear, its junk words are present *)
  hv_unw : val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + t_unwinding) 1 0;
  hv_junk : forall a, ly_T ly + t_cache_stats <= a < ly_T ly + t_unwinding -> apresent (w_H W) mem a;
  (* the cached chunk is present, and its shadow is present and poisoned (250) *)
  hv_chunk : forall a, Kv ly cl v <= a < Kv ly cl v + class_size cl -> apresent (w_H W) mem a;
  hv_shadow : forall s, SKv ly cl v <= s < SKv ly cl v + class_size cl / 8 ->
              apresent (w_H W) mem s /\ val_mem tfibsegs (mrestrict (w_H W) mem) s 1 250
}.

(* (d) The allocator memory the hit-g walk writes, besides Allocate's stack window and the new block: the thread
   cache cells, the chunk header, the partial shadow byte (odd sizes), the depot zone and the block's shadow. *)
Definition hit_writes (ly : alayout) (n cl v kz : Z) (odd : bool) (a : Z) : Prop :=
WINT ly cl a \/ ((Kv ly cl v <= a < Kv ly cl v + 16) \/ (Uv ly cl v kz - 16 <= a < Uv ly cl v kz)) \/ PBW ly n cl v kz odd a \/
DZONE ly a \/ (SUv ly cl v kz <= a < SUv ly cl v kz + N8D n / 8).

(* The walk's frame at Allocate's entry, over the virtual register file regs0 of the walk's environment (atom 2 =
   the entry sp, 12 = the trace buffer, 13 = the stack object). *)
Definition wframe (W : world tfibsegs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (tr : list Z) : Prop :=
(ly_stk_lo ly + AFSTACK <= bv_unsigned (getr regs0 2) /\ ly_bot ly < bv_unsigned (getr regs0 2) /\
 bv_unsigned (getr regs0 2) <= ly_stk_hi ly /\ bv_unsigned (getr regs0 2) mod 16 = 0) /\
(1 <= length tr <= 30)%nat /\
(bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 13) /\ bv_unsigned (getr regs0 13) + 16 <= ly_stk_hi ly /\
 bv_unsigned (getr regs0 13) mod 8 = 0) /\
(bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 12) /\ bv_unsigned (getr regs0 12) + 8 * 30 <= ly_stk_hi ly /\
 bv_unsigned (getr regs0 12) mod 8 = 0) /\
(forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem0 a).
End p.

(* The return address into Allocate after its call of the refill callee. *)
Definition A_REFILL_RET : Z := 0x35abc.

#[export] Instance AGImg_cgif : @ImgBaseAG.AGImg AImg_cgif := {|
  ImgBaseAG.ag_inst_ok := inst_ok;
  ImgBaseAG.ag_czone := CZONE;
  ImgBaseAG.ag_dzone := AGis.DZONE;
  ImgBaseAG.ag_shadow := AGis.SHBv;
  ImgBaseAG.ag_depot_put := A_StackDepotPut;
  ImgBaseAG.ag_refill := A_Refill;
  ImgBaseAG.ag_refill_ret := A_REFILL_RET
|}.
(* Also canonical, as AImg_cgif is: [apply] and [destruct] elaborate their term without instance search. *)
Canonical Structure AGImg_cgif.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

Lemma at_RET_w : forall W ly regs0 mem0 md0 n cl cnt v jb kz DPOST odd z W' c',
AGis.at_RET W ly regs0 mem0 md0 n cl cnt v jb kz DPOST odd z W' c' -> AGif0n.at_RETw W ly regs0 mem0 md0 n cl cnt v jb kz DPOST odd z W' c'.
Proof.
intros W ly regs0 mem0 md0 n cl cnt v jb kz DPOST odd z W' c' H. unfold AGis.at_RET, AGif0n.at_RETw in *. cbv zeta in *.
destruct H as (HW & regs' & mem' & mat & Hc & R10 & RCS & DD & MEQF & PRS & PRW & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11).
split; [exact HW|]. exists regs', mem', mat. repeat (split; [assumption|]). exact V10.
Qed.
Lemma at_RETk_w : forall W ly regs0 mem0 md0 n cl cnt v jb DPOST odd z W' c',
AGj6.at_RET W ly regs0 mem0 md0 n cl cnt v jb DPOST odd z W' c' -> AGif0n.at_RETkw W ly regs0 mem0 md0 n cl cnt v jb DPOST odd z W' c'.
Proof.
intros W ly regs0 mem0 md0 n cl cnt v jb DPOST odd z W' c' H. unfold AGj6.at_RET, AGif0n.at_RETkw in *. cbv zeta in *.
destruct H as (HW & regs' & mem' & mat & Hc & R10 & RCS & DD & MEQF & PRS & PRW & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11).
split; [exact HW|]. exists regs', mem', mat. repeat (split; [assumption|]). exact V10.
Qed.
Lemma malloc_join_t_cgif : forall n trace c, AGif0n.malloc_join_t 12 n trace c = malloc_join n trace c.
Proof. reflexivity. Qed.
(* The interface's view (AGif0n.hview, over the class fields and the copied geometry) gives cgif's [hview] (Section
   p), which the walk files' view lemmas and seeds read (AGiz / AGj0 for the g path, AGjd / AGje for the k path). *)
Lemma hview_cgif : forall B (W : world tfibsegs) ly inst mem cl cnt v,
AGif0n.hview B W ly inst mem cl cnt v -> hview B W ly inst mem cl cnt v.
Proof. intros B W ly inst mem cl cnt v H. destruct H; constructor; assumption. Qed.
End a.
