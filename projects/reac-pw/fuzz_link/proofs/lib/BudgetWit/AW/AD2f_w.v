(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2f.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD2f.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* ADAPTED by Theorem Labs, 2026-10 (a Theorem Labs lane), beyond relocation. Donor = cgif A/AD2f.v;
   "donor :N" is a donor line.
   1. ACfl -> Prog/PcapEntry + Prog/PcapEntryA (porter ruling 1): A_LLVMF / RA_LLVMF / A_EMPTY / LLVMF_STK /
      G_HARNESS now come from lib/A/Prog/PcapEntryA.v (the ASan image's constants), EV_LIB / LIVE_LIB from
      lib/A/Prog/PcapEntry.v. Donor :13.
   2. The harness globals' hull [DRV_G_LO, DRV_G_HI) = [0x5d3f40, 0x5d3f80) (AD1y.v:20-21) is clipped out of
      IMG_L, IMG_LC and L_pieces (donor :151-152, :178), outermost, after STDOUT and SOBUF, because the PROGRAM
      call writes G_HARNESS (PcapEntryA.v:23) while the donor's call writes nothing outside its window; the new
      vm_compute lemma L_mem_avoids_G (end of file) states the side condition a Theorem Labs lane's AD1r needs.
   COUNTS, re-derived from the start-up region list (lib/A/AD2j.v IMG_REGIONS, a working branch). pcap's
   list has 14 R_A1* regions where cgif's has 15 (donor AD2j.v:155), and a Theorem Labs lane's cut of R_A5a around the hull
   (R_A5a_1 = [0x5dca90, 0x5dcac0), R_A5a_2 = [0x631300, 0x631b6c)) adds one, so IMG_REGIONS again has 33 regions
   and every length / skipn numeral is the donor's: length (ss_mem S_Pm) = 3 + 33 + 3 = 39, firstn 33 (skipn 3
   ...) = IMG_REGIONS, skipn 36 = RT_REGIONS (AD20.v:50, three regions). STDOUT [0xa6090, 0xa6178) lies strictly
   inside R_A3 and SOBUF [0x652318, 0x652728) strictly inside R_A8, and no region of the cut list meets the hull,
   so length IMG_L = length IMG_LC = 33 + 2 = 35 and the G clip adds no piece; length L_pieces = 1 + 2 + 33 + 5 =
   41 = length (ss_mem sPE0), its five trailing [] standing for RT_REGIONS, RBh and R161.
   ONE COUNT CHANGES, IMG_B_eq (donor :195-196). The loop rewrites two image regions: the one holding the init
   flag and R_A7b. cgif's flag 0x6359d0 heads R_A5a at index 24; pcap's A_INITFLAG 0x5dca90 (s4 at 0x82034;
   sb at 0x82080 writes +0, sb at 0x820b8 writes +4) heads R_A5a_1 at index 23, R_A5a_2 at index 24 is not
   written, and R_A7b stays at index 28. So for IMG_B firstn 24 -> firstn 23 and firstn 3 (skipn 25) ->
   firstn 4 (skipn 24); for IMG_E (only +4 written) firstn 24 -> firstn 23 and skipn 25 -> skipn 24; skipn 29
   and the lengths 33 stay.
   MEASURED by temporary vm_compute probes on the dev union (a build machine, log
   (internal), since deleted): lengths IMG_REGIONS 33, RT_REGIONS 3,
   ss_mem S_Pm 39, ss_mem sB0 / sB1 / sPE0 41; IMG_B and IMG_E 33, IMG_L and IMG_LC 35; L_pieces 41, L_mem 39;
   the regions where firstn 33 (skipn 3 (ss_mem sB0 / sB1)) differs from IMG_REGIONS are [23; 28], where IMG_E
   differs from it [23]. All these numerals follow AD2j: re-check them whenever it is regenerated. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK00 YP0m YP09 YP02 YP0l YP06 YP03 YP0g YP08 YN3q YN3v YI04 YL09 YL02 YL04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1y_w AD2h_w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO05.
(* ADAPTED (porter ruling 1): cgif's A/ACfl.v is not ported; fuzz_pcap's entry-call constants (A_LLVMF
   0x827d4, RA_LLVMF 0x820c8, A_EMPTY 0x5dcaa0, LLVMF_STK and the harness globals G_HARNESS) are
   lib/A/Prog/PcapEntryA.v's, EV_LIB and LIVE_LIB lib/A/Prog/PcapEntry.v's. Donor AD2f.v:14
   `Require Export ACeg ACfl`. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.BudgetWit.AW Require Export ACeg_w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition A_INITFLAG : Z := 0x5dca90.
Definition R161 : YP09.region := YP09.mkRegion (Some 161%nat) 0 4 0 0 [mkChunk 0 (CData 3 0 4)].
Definition RBh (h : Z) : YP09.region := YP09.mkRegion (Some A_BUF) 0 h 0 0 [mkChunk 0 (CData 2 0 h)].
Definition fact_P : afact := mkAF 4098 140737479966720 0.
Definition S_Pm : sstate := Eval vm_compute in mkSS (ss_pc S_P) (ss_regs S_P) (removelast (ss_mem S_P)) None (ss_facts S_P).
Definition ssP (h : Z) : sstate :=
mkSS (ss_pc S_P) (sr_set (ss_regs S_P) 10%bv (SOff 161 0))
(ss_mem S_Pm ++ [RBh h; R161]) None
(mkFacts ((161%nat, fact_P) :: f_atoms (ss_facts S_P)) (f_conds (ss_facts S_P)) (f_alias (ss_facts S_P))).
Definition ssP1 : sstate := Eval vm_compute in (ssP 3).
Definition sB1 : sstate := Eval vm_compute in (run_lp ssP1).
Definition clip_chunk (lo hi : Z) (c : YP09.chunk) : list YP09.chunk :=
let a := YP09.c_off c in let l := c_len c in
let a' := Z.max a lo in let b' := Z.min (a + l) hi in
if b' <=? a' then [] else
match YP09.c_val c with
| CImg _ => [mkChunk a' (CImg (b' - a'))]
| CZero _ => [mkChunk a' (CZero (b' - a'))]
| CVal w v => if ((lo <=? a) && (a + l <=? hi))%bool then [c] else []
| CData d s _ => [mkChunk a' (CData d (s + (a' - a)) (b' - a'))]
end.
Definition clip_region (lo hi : Z) (r : YP09.region) : YP09.region :=
YP09.mkRegion (r_base r) (Z.max (r_lo r) lo) (Z.min (r_hi r) hi)
(if (r_whi r <=? r_wlo r)%bool then 0 else Z.max (r_wlo r) lo) (if (r_whi r <=? r_wlo r)%bool then 0 else Z.min (r_whi r) hi)
(flat_map (clip_chunk lo hi) (r_chunks r)).
Definition STDOUT_LO : Z := 0xa6090.  Definition STDOUT_HI : Z := 0xa6178.
Definition SOBUF_LO : Z := 0x652318.   Definition SOBUF_HI : Z := 0x652728.
Definition IMG_B : smem := firstn 68 (skipn 3 (ss_mem sB1)).
Definition clip_out (lo hi : Z) (r : YP09.region) : list YP09.region :=
if ((hi <=? r_lo r) || (r_hi r <=? lo))%bool then [r] else
(if (r_lo r <? lo)%bool then [clip_region (r_lo r) lo r] else []) ++ (if (hi <? r_hi r)%bool then [clip_region hi (r_hi r) r] else []).
(* ADAPTED (porter ruling 3): the image regions the loop state keeps across the PROGRAM call must also leave
   out the harness globals' hull [DRV_G_LO, DRV_G_HI) = [0x5d3f40, 0x5d3f80) (AD1y.v:20-21), because the call
   writes G_HARNESS (PcapEntryA.v:23) and the donor's harness writes nothing outside its window. The hull is
   clipped out exactly the way STDOUT and SOBUF already are (donor AD2f.v:152-153). *)
Definition IMG_L0 : smem := Eval vm_compute in flat_map (fun r => flat_map (clip_out DRV_G_LO DRV_G_HI) (flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r))) IMG_B.
