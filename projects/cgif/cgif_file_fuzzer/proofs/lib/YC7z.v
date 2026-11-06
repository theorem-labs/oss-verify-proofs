(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v YI00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition HDR_OUT : Z := 1024.
Definition FRAME_OUT (N : Z) : Z := 2 * N + 2048.
Definition CLOSE_OUT (N : Z) : Z := 3 * FRAME_OUT N + 1.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Definition rc_int (v : Z) : Z := if v <? 2 ^ 31 then v else v - 2 ^ 32.
Section c.
Variable segs : list Segment.
Section d.
Variable K : asink_syms.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Definition WCBF_STK : Z := WCB_STK + AFWRITE_STK.
Definition twcbF_spec (wfn : Z) : Prop :=
forall W ly S regs mem md ch (g p n pf : Z) (Sg bs : list Z),
afn_pre segs B WCBF_STK ly S W regs mem md ch ->
getr regs 10 = w64 g -> getr regs 11 = w64 p -> getr regs 12 = w64 n ->
In (g, CGIF_OBJ) (ablocks B ly S) -> val_mem segs (rdW W mem) (g + 80) 8 pf ->
In (pf, FILE_BLOCK) (ablocks B ly S) -> asink_at segs K (rdW W mem) md pf Sg ->
garr8 segs (rdW W mem) p bs -> n = Z.of_nat (length bs) -> 1 <= n <= 2 ^ 30 ->
Z.of_nat (length Sg) + n <= SINK_MAX ->
(p + n <= pf \/ pf + FILE_BLOCK <= p) -> (p + n <= spZ regs - WCBF_STK \/ spZ regs <= p) -> 0 <= p -> amem_range p n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n -> shadow_hull_vis (aview segs (w_H W) mem) p n ->
SRr segs W (cfg_at segs wfn regs mem md)
(fun W' c' => exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal segs B WCBF_STK (spZ regs) (asink_fp pf) ly S W mem md [] ly S W' mem' md' 0 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
asink_at segs K (rdW W' mem') md' pf (Sg ++ bs)).
Definition trawclose_specX (a : Z) (rctrace : list Z) (wfn hw : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (raw g rcur pf ctx : Z) rest (Sg : list Z),
afn_pre segs B TRAWCLOSE_STK ly S W regs mem md ch ->
getr regs 10 = w64 raw ->
Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (pf, FILE_BLOCK) :: rest) ->
val_mem segs (rdW W mem) raw 8 wfn ->
val_mem segs (rdW W mem) (raw + 8) 8 g ->
val_mem segs (rdW W mem) (raw + 40) 4 rcur -> 0 <= rcur < 2 ^ 32 ->
val_mem segs (rdW W mem) (g + 56) 8 hw ->
val_mem segs (rdW W mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem segs (rdW W mem) (g + 80) 8 pf ->
asink_at segs K (rdW W mem) md pf Sg -> Z.of_nat (length Sg) + 1 <= SINK_MAX ->
st_nev S + EV_RAWCLOSE <= EV_MAX ->
In rctrace (as_universe B) ->
mo_ok MT S (mo_free MT) ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base segs B TRAWCLOSE_STK (ablocks_fp [(raw, RAW_SIZE)] ++ asink_fp pf) regs ly S W mem md EV_RAWCLOSE
(fun ly' S' W' regs' mem' md' =>
getr regs' 10 = w64 (rc_int rcur) /\
Permutation (ablocks B ly' S') ((g, CGIF_SIZE) :: (pf, FILE_BLOCK) :: rest) /\
asink_at segs K (rdW W' mem') md' pf (Sg ++ [59]) /\
mo_le MT S S' (mo_free MT))).
End e.
End d.
End c.
End b.
