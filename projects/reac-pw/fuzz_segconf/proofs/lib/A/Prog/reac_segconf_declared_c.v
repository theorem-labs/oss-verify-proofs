(* reac_segconf_declared (reac_segconf.c:561-580; fuzz_segconf.asan 0x89854, 824 bytes, 206 instructions; frame
   192 bytes and a realignment, side-stack frame class 1): the contract of the ASan build's code, in
   plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/reac_segconf_declared_c.v:13-137 (declared_pre :59-67,
   declared_W :70-71, the O3 lemmas declared_W_spares_guard and declared_guard_kept :87-117, the return value :127,
   the write list :129-130, the post :132-135), restated over the ASan reader.
   What the code does (objdump of fuzz_segconf.asan, 0x89854-0x89b88): addi sp, sp, -192, then andi sp, sp, -32
   (0x89894: at most 16 more bytes); s1, the realigned sp, holds the spills (a1, a2, a3 at 0x8989c-0x898a4).
   THE SIDE-STACK FRAME. It reads the use-after-return flag (the GOT word as_got_uar B, image A 0xa2aa8, which holds
   0xac000 = __asan_option_detect_stack_use_after_return = as_uar_cell B; lw at 0x898b8) and the shadow base (the
   GOT word as_got_shadow B, 0xa2a50, which holds 0xabff8 = as_shadow_cell B; ld at 0x898bc); AR's const law gives
   all four cells, the flag = 1 (lib/Reusable/YG0f.v:192-194), so it calls __asan_stack_malloc_1 with a0 = 0x60 (jal
   0x898cc; provenance/evidence/image-tables/callsites.asan.tsv line 367), which with stack_malloc_progressP and room returns a class-1
   frame; the real-stack branch (0x898e0-0x898f8, a 4096-byte probe loop) is dead. The frame's description (image A
   0x176dc, read from the pin: 2 32 16 10 parent:570 64 2 7 vid:571) puts parent[16] at frame + 32 and vid at
   frame + 64. The code writes the frame header (0x89920-0x89928) and the frame's shadow (f1 f1 f1 f1, f8 f8 f2 f2,
   f8 f3 f3 f3 at 0x89934-0x89968: parent and vid out of scope), makes parent and vid addressable (00 00, 02) before
   each split call (0x899d8-0x899e4) and out of scope again after the add call (0x89a28-0x89a30). At the return it
   writes the magic 0x45e0360e into frame[0] (0x89a84) and, the frame being fake, marks its 16 shadow bytes f5
   (0x89a90-0x89ad0) and clears the flag byte whose address is the frame's last word (ld 120, sb zero at
   0x89ad4-0x89ad8): astack_free_law and frame_flag_lawP.
   THE LOOP. c = NULL returns 0 (beqz 0x89974); lw of c->n (c + 0x2c80, 0x89994), n <= 0 returns 0; for each
   i < c->n (head 0x899c0, latch blt s7, a0 at 0x89a4c, c->n reloaded at 0x89a3c on every pass; s6 = c + 356 i,
   s9 = s6 + 24) it skips seg[i] when lw of seg[i].ignore (0x899d0) is nonzero, else calls
   reac_declared_vlan_split(c + 356 i, frame + 32, 16, frame + 64) (jal 0x899f8); on 1 it loads the vid (lhu
   0x89a00) and calls reac_declared_vlan_add(tab, max, n, frame + 32, vid) (jal 0x89a14); a negative result returns
   -1 (bltz 0x89a18), else added += r (addw 0x89a20). It returns added, or -1, in a0 (ld 56 of s1 at 0x89b10). The
   branches are the plain build's, so the plain post holds: a0 = fst (SegModel.r_declared rcs t max), the table
   holds snd of it and the count cell n its length.
   What it reads: the four cells above; c->n, seg[i].ignore and seg[i].name for i < c->n; through add, the table
   entries and the count cell; through split's strtol, the errno cell and the stack-protector cells. What it writes
   outside its stack window and its own side-stack frame: the entries add appends and the count cell when the table
   grows, never the guard entry tab[max].
   FOOTPRINT: declared_W below, the plain write list (:70-71) without the stack window (vtab_W's first range, kept
   by STK_reac_segconf_declared) and without the errno cell, which the kit treats as runtime scratch (see
   lib/A/Prog/reac_declared_vlan_split_c.v). Its own side-stack frame and that frame's shadow are not in the
   footprint either: the frame is not in frames S at the entry, and the journal keeps only those frames
   (lib/Reusable/YCbq.v:481-483), as in fuzz_command's lib/A/Prog/number_c.v, whose class-0 frame is not in its
   footprint.
   ERRNO, a change from the plain post: the plain post keeps the errno cell at ev (:135); the A post has no errno
   conjunct. split's and add's sa_kept keep the cell (reac_declared_vlan_split_c.v, its ERRNO paragraph), but this
   post carries no keep clause (next paragraph), so it does not state it. The plain errno_ok premise and its apart
   conjuncts (:64-65) go: the walk reads the cell for row 3 through AR_errno_present (split's head comment).
   NO sa_kept (SegABase.v), by the image-A owner's decision: the code writes its class-1 frame, the
   frame's shadow and the frame's flag byte (0x89920-0x89968, 0x899d8-0x899e4, 0x89a28-0x89a30, 0x89a84-0x89ad8),
   none of them in the stack window or the footprint, and astack_malloc_realizes 1 may change every byte aowned at
   its entry or its exit (lib/Reusable/YG0d.v:306-307). The smaller set the walk can prove kept is every byte
   outside the window, outside declared_W's ranges and not aowned B ly S: stack_malloc changes only st_fs
   (lib/Reusable/YG00.v:570-579), so a byte aowned after it was aowned before; the frame, its shadow and its flag
   byte are aowned at the entry (ly_F is in owned_extents, lib/Reusable/YG0f.v:299-302; the shadow of every byte of
   lm_zone or hm_zone that is not a client byte is aowned, lib/Reusable/YG0n.v:236-242). That set leaves out the
   shadow of every image object, so it does not give what sa_kept is for; the one caller reads no image object
   after this call (check_declared on the heap tables, then four frees, LLVMFuzzerTestOneInput 0x85c10-0x85c30).
   No abort site (provenance/evidence/image-tables/program.asan.tsv line 30).
   ASAN FACTS ADDED over the plain contract (rd = aview segs (w_H W) mem):
   - inline check 1, load4 of c->n at 0x89994 (shadow index 0x89984-0x89988, test 0x8998c-0x89990, slow path
     0x89b70, error arm __asan_report_load4 at 0x89b80); inline check 2, load4 of seg[i].ignore at 0x899d0 (test
     0x899c0-0x899cc, slow path 0x89a54, error arm __asan_report_load4 at 0x89b88); inline check 3, load4 of c->n at
     0x89a3c, the reload (test 0x89a34-0x89a38, slow path 0x89a64, error arm __asan_report_load4 at 0x89a70): all
     three killed by declared_pre's sa_addr rd c SEG_C_SIZE (0x2c80 + 4 and 356 * 31 + 24 + 4 are below 16616).
   - what the callees ask: split's segment c + 356 i lies in the same addressable block, with the band room row 3
     asks (356 * 31 + 15 + 8 < 16616); add's table and count cell are vtab_pre's, passed unchanged; parent and vid
     are this call's own frame, addressable when it calls split and add.
   - where each object lies: c by sa_heap (the reader's malloc(0x40e8) block, LLVMFuzzerTestOneInput 0x84f80); the
     table by sa_heap over max + 1 entries and the count cell by sa_dst (vtab_pre of
     lib/A/Prog/reac_declared_vlan_add_c.v). Every arm keeps them off this call's stack window, which replaces the
     plain apart premises from [lo, sp), sa_img_end and blk_noimg (a block holds no image byte: the kit's lemma
     blk_img, lib/Reusable/YCbq.v:251-252). c stays apart from the table block and from the count cell (sa_disj),
     as in the plain pre.
   - sa_room S: room for its class-1 side-stack frame (LLVMFuzzerTestOneInput's class-3 frame is in frames S
     already; its own is the first of the nest below the harness).
   - sa_ssp rd gotw guard, the plain ssp_ok, handed to split for its strtol (row 3); gotw and guard are parameters.
   - GUARD (obligation O3): the plain file proves declared_guard_kept (:104-117); the A post states it,
     sa_guardtab rd tab max -> sa_guardtab rd' tab max, as add's A post does, and the walk proves it from add's.
   - arodata_okP over the read-only window RLO RHI, handed to split and add (their interceptors ask rt_rom_view).
   - no printf: apost_base, EV_reac_segconf_declared = 0 (the side-stack frame is not an allocator event), post
     tail sa_noalloc (its only state change is the frame it takes and releases: exists f, S' = set_fs f S).
   Call site (provenance/evidence/image-tables/callsites.asan.tsv line 52): LLVMFuzzerTestOneInput 0x85bf0 with a0 = c (ld 160 of s1,
   the malloc(0x40e8) block of 0x84f80), a1 = tab (s8, the calloc(cap + 1, 18) block of 0x857b8; INFERENCE: s8 is
   traced through its spill at 0x85a8c and its reload at 0x85b84 only), a2 = cap (ld 32 of s1), a3 = n (ld 48 of
   s1, the harness's class-3 frame + 256, 0x84fcc-0x84fd0). check_declared (0x85c10) reads what the post gives.
   image A: A_reac_segconf_declared = 0x89854; STK_reac_segconf_declared = 192 + 16 + 64 + 3 * ESTACK (INFERENCE: its
   frame and realignment above split's window, the widest of split's, add's (112 + 2 * ESTACK) and
   __asan_stack_malloc_1's (ESTACK)); RLO RHI = image A's RELRO bounds; gotw = 0xa36d8, guard = 0x5ff078.
   IMAGE-INDEPENDENT: no image module is Required; A_reac_segconf_declared, STK_reac_segconf_declared, RLO, RHI,
   gotw, guard and every other image cell are parameters (or fields of B).
   The WALK takes these as Section hypotheses (none is the interceptor lane's: the side-stack classes 0, 1, 3 and
   the kit laws are the image-A owner's frame, provenance/evidence/interceptors/INTERFACE-A-interceptors.md
   (commit 7068323e2626), its Not in this layer paragraph, at e45889d6935a and in the accepted v1 5e0b8a44fdc):
     astack_malloc_realizes 1 (lib/Reusable/YG0d.v:293), at __asan_stack_malloc_1 (image A 0x3e6f0);
     stack_malloc_progressP (lib/Reusable/YCbq.v:1096); astack_free_law (YG0d.v:309); frame_flag_lawP
       (YCbq.v:1090);
     reac_declared_vlan_split_contract (lib/A/Prog/reac_declared_vlan_split_c.v) at split's entry and stack (image
       A 0x89b8c), with this contract's RLO RHI gotw guard;
     reac_declared_vlan_add_contract (lib/A/Prog/reac_declared_vlan_add_c.v) at add's entry and stack (image A
       0x89e4c), with this contract's RLO RHI.
   The interceptors are the callees' walks' hypotheses: rows 3, 11, 16 (split), 9 (name_ok), 12, 17 (add).
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_add_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* The bytes it writes outside its stack window and its own side-stack frame: add's appended entries and the count
   cell when the table grew (the plain declared_W, :70-71, without the stack window and the errno cell). *)
Definition declared_W (tab n : Z) (t t' : list (list Z * Z)) : list (Z * Z) := vtab_W tab n t t'.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* What reac_segconf_declared asks of its caller (the plain declared_pre, :59-67, over the reader
   rd = aview segs (w_H W) mem; regs are this call's entry registers): c the reader's block, a nonzero 16-aligned
   live heap block of SEG_C_SIZE bytes holding rcs, all of it addressable; the table and count cell (vtab_pre),
   apart from c; the stack-protector cells split's strtol compares. The plain errno_ok, stack_ok, apart-from-[lo,
   sp), sa_img_end, blk_noimg and mem_inv conjuncts are afn_pre's and the places' here (head comment). Outside the
   sections: declared_pre segs B ly S W mem regs c tab max n rcs t gotw guard. *)
Definition declared_pre (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
(regs : bvmap 5 word) (c tab max n : Z) (rcs : rconf) (t : list (list Z * Z)) (gotw guard : Z) : Prop :=
c <> 0 /\ c mod 16 = 0 /\ sa_rconf (aview segs (w_H W) mem) c rcs /\ sa_heap B ly S c seg_spec.SEG_C_SIZE /\
sa_addr (aview segs (w_H W) mem) c seg_spec.SEG_C_SIZE /\
vtab_pre segs B ly S W mem regs tab max n t /\
sa_disj c seg_spec.SEG_C_SIZE tab (seg_spec.RVLAN_SIZE * (max + 1)) /\ sa_disj n 4 c seg_spec.SEG_C_SIZE /\
sa_ssp (aview segs (w_H W) mem) gotw guard.
(* the events this call spends: 0, it reaches no allocator entry (nor do split and add); its side-stack frame is not
   an allocator event *)
Definition EV_reac_segconf_declared : Z := 0.
Definition reac_segconf_declared_contract
(A_reac_segconf_declared STK_reac_segconf_declared RLO RHI gotw guard : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c tab max n : Z) (rcs : rconf) (t : list (list Z * Z)),
afn_pre segs B STK_reac_segconf_declared ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 11 = w64 tab -> 0 <= tab < 2 ^ 64 ->
getr regs 12 = w64 max -> 0 <= max < 2 ^ 64 -> getr regs 13 = w64 n -> 0 <= n < 2 ^ 64 ->
declared_pre ly S W mem regs c tab max n rcs t gotw guard ->
(* room for its class-1 side-stack frame *)
sa_room S ->
st_nev S + EV_reac_segconf_declared <= EV_MAX ->
SRr segs W (cfg_at segs A_reac_segconf_declared regs mem md)
(apost_base segs B STK_reac_segconf_declared (declared_W tab n t (snd (SegModel.r_declared rcs t max))) regs ly S
W mem md EV_reac_segconf_declared
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (fst (SegModel.r_declared rcs t max)) /\
 sa_rtab (aview segs (w_H W') mem') tab (snd (SegModel.r_declared rcs t max)) /\
 sa_val (aview segs (w_H W') mem') n 4 (Z.of_nat (length (snd (SegModel.r_declared rcs t max)))) /\
 (sa_guardtab (aview segs (w_H W) mem) tab max -> sa_guardtab (aview segs (w_H W') mem') tab max) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
