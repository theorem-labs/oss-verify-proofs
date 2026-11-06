(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YN06 YQ0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02
YI1i YP14 YI08 YI0c YI0g YI3h YI4v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition PC_LH : Z := 0x13c24.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable API : AllocAPI src2_msyms.
Local Notation segs := src2segs.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Definition at_LH (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (fdp : Z) : Prop :=
rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lc Ac memc mdc /\
rgba_regs regs0 regs1 /\ (fmt = 3 \/ fmt = 4) /\ 1 <= N /\ (ha = 0 \/ (ha = 1 /\ fmt = 4)) /\
256 <= ht_cnt (ch_H C) /\ 0 <= i < ht_cnt (ch_H C) /\
getr regs1 18 = Z_to_bv 64 (3 * i) /\ getr regs1 19 = Z_to_bv 64 i /\ getr regs1 25 = Z_to_bv 64 (ch_p C) /\
getr regs1 22 = Z_to_bv 64 (2 ^ 32 - 1) /\ getr regs1 23 = Z_to_bv 64 (ch_h C) /\ getr regs1 26 = Z_to_bv 64 (ch_u C) /\
getr regs1 27 = Z_to_bv 64 (fdp + 4 * i) /\ getr regs1 24 = Z_to_bv 64 fdp /\ getr regs1 9 = Z_to_bv 64 fmt /\
getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 8 = Z_to_bv 64 r /\ getr regs1 21 = Z_to_bv 64 2 /\
slots_mid regs0 cfp N fattr memc pnew fimg /\ slots_q regs0 W bef beffmt img fattr memc ha /\
fcfg_at regs0 fattr delay memc fimg 0 0 /\ rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur memc /\
cgif_at memc g s /\ img_at N img fmt memc imgl /\
obj_at segs memc (ch_c C) LAY_Cht [ch_f C; ch_h C; ch_u C; ch_p C; ch_x C; ht_cnt (ch_H C); ch_T C] /\
cht_arrays segs memc (ch_f C) (ch_h C) (ch_u C) (ch_p C) (ch_x C) (ch_H C) /\
ht_inv (ch_H C) (ch_ent C) /\ ht_T (ch_H C) = ch_T C /\ In (ch_T C) ts_chain /\ zsum (map snd (ch_ent C)) <= N /\
(forall j, 0 <= j < i -> val_mem segs memc (fdp + 4 * j) 4 (getz (map snd (ch_ent C)) j)) /\
(forall k, 0 <= k < 4 * ht_cnt (ch_H C) -> exists b, mbyte segs memc (fdp + k) = Some b) /\
pnew <> 0 /\ fimg <> 0 /\ fdp <> 0 /\ fdp mod 16 = 0 /\
Permutation (blocks Lc Ac) (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ [(fdp, 4 * ht_cnt (ch_H C))]).
Definition K_LH (i : Z) : Prop := forall regs1 Lc Ac memc mdc ha pnew fimg imgl C fdp,
at_LH regs1 Lc Ac memc mdc i ha pnew fimg imgl C fdp ->
SR segs (cfg_at regs1 PC_LH memc mdc) (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
End c.
End a.
