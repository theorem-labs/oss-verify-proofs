(* reac_declared_vlan_add (reac_declared_vlan.c:65-80; fuzz_segconf.asan 0x89e4c, 492 bytes, 123 instructions;
   frame 112 bytes, no side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's
   lib/A/Prog form (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/reac_declared_vlan_add_c.v:11-151 (vtab_pre :54-60,
   add_pre :64-70, vtab_W :74-76, the O3 lemmas add_W_spares_guard and add_guard_kept :115-133, the return value
   :142, the write list :144-145, the post :147-149), restated over the ASan reader.
   What the code does (objdump of fuzz_segconf.asan, 0x89e4c-0x8a034): -1 when tab, n or parent is 0 (three beqz,
   0x89e88-0x89e98; the premise excludes them); lw of the count cell n (0x89ec4) into s10; when it is > 0 the search
   (0x89ed8 .. bnez 0x89f0c, s7 = tab + 18 i, s11 counting down) loads tab[i].vid (lhu at 0x89ee8) and, when it
   equals vid (the whole register: a uint16_t argument arrives zero-extended), calls strcmp(tab[i].parent, parent)
   (jal 0x89ef8); the first 0 returns 0; then count >= max (bge s10, s5 at 0x89f28, signed) returns -1; else
   memset(tab + 18 count, 0, 18) through the checked __asan_memset (jal 0x89f40), lw of the count cell again
   (0x89f4c), strncpy(tab + 18 count, parent, 15) (jal 0x89f60), lw again (0x89f6c), tab[count].vid = vid (sh
   0x89f90), count + 1 into the count cell (lw 0x89f94, sw 0x89f9c), and it returns 1. The branches are the plain
   build's, so the plain post holds: a0 and the table are SegModel.vlan_add t max p vid (1 appended, 0 duplicate,
   -1 full; -1 is the word 2 ^ 64 - 1, w64's Z_to_bv 64), the count cell holds the new length.
   What it reads: the shadow base (the GOT word as_got_shadow B, image A 0xa2a50, loaded at 0x89eac; AR's const
   law); the count cell; the entries tab[0 .. count) (the vid fields inline, the parent strings through strcmp);
   the string at parent with its slack (strcmp, strncpy). It never reads or writes the guard entry tab[max]. What
   it writes outside its stack window: when it appends, the entry tab[count] (memset 18 bytes, strncpy 15, sh 2)
   and the count cell. FOOTPRINT: vtab_W below, the plain write list (:74-76) without its first range [sp - depth,
   sp), the stack window, which apost_base keeps by STK_reac_declared_vlan_add. No abort site
   (provenance/evidence/image-tables/program.asan.tsv line 33).
   ASAN FACTS ADDED over the plain contract (rd = aview segs (w_H W) mem):
   - inline checks 1, 3 and 4, load4 of the count cell at 0x89ec4, 0x89f4c and 0x89f6c (one shadow index, s9 at
     0x89eb4-0x89eb8; shadow tests 0x89ebc-0x89ec0, 0x89f44-0x89f48, 0x89f64-0x89f68; slow paths 0x89fec, 0x8a000,
     0x8a014; error arms __asan_report_load4 at 0x89ffc, 0x8a010, 0x8a024): killed by vtab_pre's sa_addr rd n 4,
     which also covers the unchecked lw / sw of the count at 0x89f94 / 0x89f9c.
   - inline check 2, load2 of tab[i].vid at 0x89ee8 (shadow test 0x89ed8-0x89ee4, slow path 0x89f14, error arm
     __asan_report_load2 at 0x89f24), i < count = length t <= max: killed by vtab_pre's sa_addr rd tab
     (RVLAN_SIZE * max).
   - inline check 5, store2 of tab[count].vid at 0x89f90 (shadow test 0x89f80-0x89f8c, slow path 0x8a028, error arm
     __asan_report_store2 at 0x8a034), count < max on that path: killed by the same sa_addr.
   - interceptor ranges: strcmp reads tab[i].parent, inside the entries (sa_addr rd tab (RVLAN_SIZE * max); its
     slack lies inside the block), and parent (sa_addr rd parent (length p + 1); sa_str's slack, the atail_vis row
     17 asks; length p + 1 < 2 ^ 32, aread_ok's bound). The checked memset writes [tab + 18 count, + 18):
     aintrin_realizes OSet (lib/Reusable/YG0d.v:326) asks it addressable with its band (sa_addr) and in a place the
     call may write (the block: sa_heap). strncpy (row 12) reads parent and writes [tab + 18 count, + 15):
     amem_range parent (length p + 8) and amem_range tab (RVLAN_SIZE * max + 8) are the band room row 12's
     template, RtString.astrcpy_realizes (fuzz_command lib/A/Rt/RtString.v:214-238 at origin/ossv/recipes
     501c0d516c69), asks of its source and of its destination (tab + 18 count + 15 + 8 <= tab + 18 max + 8 for
     count < max).
   - where each object lies: the table by sa_heap over its max + 1 entries (the harness's calloc(cap + 1, 18) at
     LLVMFuzzerTestOneInput 0x857b8; the guard entry tab[max] is the block's last 18 bytes); the count cell by
     sa_dst (the harness's class-3 side-stack frame + 256, 0x84fcc-0x84fd0); parent by sa_loc
     (reac_segconf_declared's class-1 side-stack frame + 32). Every arm keeps them outside this call's stack
     window, which replaces the plain apart premises from [lo, sp) and the plain free-entries writability; the
     count cell stays apart from the block, and parent's read span from the block (sa_disj, with seg_spec.cstr_span
     for the plain length + 8), as in the plain pre.
   - GUARD (obligation O3): the plain file proves add_guard_kept (:125-133), guard_at m' from munch W. This file
     holds no proof, so the A post states it, sa_guardtab rd tab max -> sa_guardtab rd' tab max, and the walk
     proves it from the journal (the block is live at both ends by sa_noalloc, and vtab_W misses tab[max]).
   - arodata_okP over the read-only window RLO RHI: rows 17 and 12 ask rt_rom_view (fuzz_command
     lib/A/Rt/RtDefs.v:145).
   - sa_kept segs W mem W' mem' regs STK_reac_declared_vlan_add (vtab_E tab n t t') in the post, t' the table
     after the call: every byte outside the stack window and the footprint reads as at the entry, the shadow of an
     image object included, which the journal alone does not keep (SegABase.v's sa_kept, found by the G4 / G5
     walks); vtab_E is vtab_W's ranges, one disjunct each. (It implies the GUARD
     conjunct too, since tab[max] is in neither; that conjunct stays, its consumers name it.) True of the code: it
     takes no side-stack frame and calls no set_shadow entry (provenance/evidence/image-tables/program.asan.tsv line 33,
     callsites.asan.tsv lines 385-392); its own stores are the saved registers in its frame (0x89e50-0x89e80),
     tab[count].vid (0x89f90) and the count cell (0x89f9c), on the append path only, where t' = t ++ [e] and the
     first range is exactly tab[count]; the checked memset writes only [tab + 18 count, + 18) and its ESTACK
     scratch (aintrin_realizes, lib/Reusable/YG0d.v:343); strcmp writes only its scratch (the RtString form,
     art_post's keep clause with E = False); strncpy writes its scratch and [tab + 18 count, + 15), which ROW 12'S
     POST MUST STATE AS ITS ONLY WRITTEN RANGE (astrcpy_realizes's form: E = the destination range).
   - no side-stack frame and no printf: apost_base, EV_reac_declared_vlan_add = 0, post tail sa_noalloc.
   Call site (provenance/evidence/image-tables/callsites.asan.tsv line 369): reac_segconf_declared 0x89a14 with a0 = tab, a1 = max,
   a2 = n (ld 32, 40, 48 of s1: declared's spills of its own a1, a2, a3 at 0x8989c-0x898a4), a3 = frame + 32 (s10,
   the C string split left there), a4 = the vid (lhu at 0x89a00 from frame + 64: below 2 ^ 16).
   image A: A_reac_declared_vlan_add = 0x89e4c; STK_reac_declared_vlan_add = 112 + 2 * ESTACK (INFERENCE: its frame
   above the 2 * ESTACK windows of row 17 and of row 12, whose accepted text asks 2 * ESTACK; the checked memset
   asks ESTACK); RLO RHI = image A's RELRO bounds.
   IMAGE-INDEPENDENT: no image module is Required; A_reac_declared_vlan_add, STK_reac_declared_vlan_add, RLO, RHI
   and every image cell are parameters (or fields of B).
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626): row 17 in the accepted v1,
   5e0b8a44fdc; row 12 accepted at 80d098bd1905):
     RtString.astrcmp_realizes (row 17), at the strcmp trampoline (image A 0x43a14);
     RtSeg.astrncpy_realizes (pc) (row 12, lib/A/Rt/RtSeg.v:197 at 80d098bd1905), at the strncpy trampoline
       (image A 0x43ab4);
     aintrin_realizes OSet (lib/Reusable/YG0d.v:326; the frame's text, not the interceptor lane's), at pc_memset
       (image A __asan_memset 0x55d7c).
   They are NOT premises of this contract: the statement does not mention them. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* The bytes add and reac_segconf_declared write outside their stack windows: the entries appended to a table of
   length t that now has length t', and the count cell when the table grew (the plain vtab_W, :74-76, without its
   stack window range). *)
Definition vtab_W (tab n : Z) (t t' : list (list Z * Z)) : list (Z * Z) :=
[(tab + seg_spec.RVLAN_SIZE * Z.of_nat (length t), tab + seg_spec.RVLAN_SIZE * Z.of_nat (length t'))] ++
(if (length t <? length t')%nat then [(n, n + 4)] else []).
(* The byte set of vtab_W, one disjunct per range: what add's sa_kept exempts besides the stack window. *)
Definition vtab_E (tab n : Z) (t t' : list (list Z * Z)) (a : Z) : Prop :=
(tab + seg_spec.RVLAN_SIZE * Z.of_nat (length t) <= a < tab + seg_spec.RVLAN_SIZE * Z.of_nat (length t')) \/
(if (length t <? length t')%nat then n <= a < n + 4 else False).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* The table and count cell add and reac_segconf_declared receive (the plain vtab_pre, :54-60, over the reader
   rd = aview segs (w_H W) mem; regs are the entry registers of the call that asks it): tab a nonzero 16-aligned
   live heap block of max + 1 entries whose first length t entries hold t (sa_rtab), length t <= max < 2 ^ 31,
   the entries tab[0 .. max) addressable with the band room strncpy's destination needs past them; the count cell
   a nonzero 4-aligned int holding length t, addressable, in a place the call may write, apart from the block. The
   guard entry tab[max] is the block's last entry and is neither read nor written. Outside the sections:
   vtab_pre segs B ly S W mem regs tab max n t. *)
Definition vtab_pre (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
(regs : bvmap 5 word) (tab max n : Z) (t : list (list Z * Z)) : Prop :=
tab <> 0 /\ tab mod 16 = 0 /\ sa_rtab (aview segs (w_H W) mem) tab t /\ Z.of_nat (length t) <= max < 2 ^ 31 /\
sa_heap B ly S tab (seg_spec.RVLAN_SIZE * (max + 1)) /\
sa_addr (aview segs (w_H W) mem) tab (seg_spec.RVLAN_SIZE * max) /\
amem_range tab (seg_spec.RVLAN_SIZE * max + 8) /\
n <> 0 /\ n mod 4 = 0 /\ sa_val (aview segs (w_H W) mem) n 4 (Z.of_nat (length t)) /\
sa_dst segs B ly S W mem regs n 4 /\ sa_addr (aview segs (w_H W) mem) n 4 /\
sa_disj n 4 tab (seg_spec.RVLAN_SIZE * (max + 1)).
(* What add asks of its caller (the plain add_pre, :64-70): vtab_pre; parent the C string p with its slack (sa_str:
   strcmp's and strncpy's word reads), its bytes and NUL addressable, the band room strncpy's source needs, in a heap
   block, a side-stack frame or the image, its read span apart from the block; vid the uint16_t. Outside the
   sections: add_pre segs B ly S W mem regs tab max n parent vid t p. *)
Definition add_pre (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
(regs : bvmap 5 word) (tab max n parent vid : Z) (t : list (list Z * Z)) (p : list Z) : Prop :=
vtab_pre ly S W mem regs tab max n t /\
parent <> 0 /\ sa_str (aview segs (w_H W) mem) parent p /\
sa_addr (aview segs (w_H W) mem) parent (Z.of_nat (length p) + 1) /\ Z.of_nat (length p) + 1 < 2 ^ 32 /\
amem_range parent (Z.of_nat (length p) + 8) /\
sa_loc segs B ly S parent (Z.of_nat (length p) + 1) /\
sa_disj parent (seg_spec.cstr_span parent p) tab (seg_spec.RVLAN_SIZE * (max + 1)) /\
0 <= vid < 65536.
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_reac_declared_vlan_add : Z := 0.
Definition reac_declared_vlan_add_contract (A_reac_declared_vlan_add STK_reac_declared_vlan_add RLO RHI : Z)
: Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (tab max n parent vid : Z) (t : list (list Z * Z)) (p : list Z),
afn_pre segs B STK_reac_declared_vlan_add ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 tab -> 0 <= tab < 2 ^ 64 -> getr regs 11 = w64 max -> 0 <= max < 2 ^ 64 ->
getr regs 12 = w64 n -> 0 <= n < 2 ^ 64 -> getr regs 13 = w64 parent -> 0 <= parent < 2 ^ 64 ->
getr regs 14 = w64 vid -> 0 <= vid < 2 ^ 64 ->
add_pre ly S W mem regs tab max n parent vid t p ->
st_nev S + EV_reac_declared_vlan_add <= EV_MAX ->
SRr segs W (cfg_at segs A_reac_declared_vlan_add regs mem md)
(apost_base segs B STK_reac_declared_vlan_add (vtab_W tab n t (snd (SegModel.vlan_add t max p vid))) regs ly S W
mem md EV_reac_declared_vlan_add
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (fst (SegModel.vlan_add t max p vid)) /\
 sa_rtab (aview segs (w_H W') mem') tab (snd (SegModel.vlan_add t max p vid)) /\
 sa_val (aview segs (w_H W') mem') n 4 (Z.of_nat (length (snd (SegModel.vlan_add t max p vid)))) /\
 (sa_guardtab (aview segs (w_H W) mem) tab max -> sa_guardtab (aview segs (w_H W') mem') tab max) /\
 sa_kept segs W mem W' mem' regs STK_reac_declared_vlan_add (vtab_E tab n t (snd (SegModel.vlan_add t max p vid))) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
