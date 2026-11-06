(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene. The four segment cuts of the
   __asan_stack_malloc_8 walk, and the composition of the four into the class-8 contract of
   lib/Reusable/AsStackSz.v (cgif_rgb_fuzzer lib/YG0e.v:17). The composition is PROVED here; the four segment
   statements are Props that the four proof lanes discharge, one lane each. No Axiom, no Admitted,
   no admit. *)

(*   This file holds NO literal address: every address and class constant is a name of lib/A/Rt/StackMalloc8Tbl.v,
   which also re-exports the two image-free callee summaries of lib/Reusable/AsStackLeaf.v. Same Tbl / walk split
   as a Theorem Labs lane's lib/A/Rt/StackMalloc4Tbl.v + StackMalloc4.v (libreac/fuzz_grant at 798447a1772) and a Theorem Labs lane's
   class 3. These cuts are tied to the ASAN image: every Prop is stated over `tfibsegs` (lib/A/AB1v.v, the asan
   segment list) and over this asan Tbl's pcs. So the asan-ubsan side needs its own copy of this file over its
   own segment list and lib/AU/Rt/StackMalloc8Tbl.v (a Theorem Labs lane's review, 23:43Z), not a Tbl twin alone.

   The cut boundaries (CLASS8-DESIGN.md section 5, DELTA-7to8.md):
     Seg A  PC_STACK_MALLOC_8 -> PC_SM8_LOOP: the prologue, the TLS fake-stack load, and the tests the premises
            refute (the GC call at entry +0x48 by AR's z1 (AF 96) 0, the `blez a2` at entry +0x5c by AR's
            z8 (AF 88) 20, i.e. kStackSizeLog = 20, and the null fake stack at entry +0x30 by [TP] = F).
     Seg B  PC_SM8_LOOP -> PC_SM8_FOUND: the 64-frame flag-search loop (one generic loop lemma over fs_probe).
     Seg C  PC_SM8_FOUND -> PC_POISON_SHADOW: the frame setup (hint := hint', flag := 1, [frame+0x18] := s0,
            [frame + fs_frame_bytes 8 - 8] := flag address) and the MemToShadow call.
     Seg D  PC_POISON_SHADOW -> return: the PoisonShadow call and the epilogue.

   WHERE AR IS CLOSED: astack_malloc_law_ok (Reusable/YG0t.v:662) is applied in Seg C BEFORE the MemToShadow jal
   at entry +0x12c, and sm8_midCD carries `AR ... S' ...`. MEASURED reason: AR S is already false after the writes
   at PC_SM8_FOUND + 0x4 / + 0x10, the four writes the law needs are all done before that jal, and the MemToShadow
   summary needs AR at its call point. Carrying AR S' forward spares Seg D the same proof; Seg D then only moves
   AR through the PoisonShadow summary (which keeps it) and the epilogue (which writes nothing).

   Seg C's lane states `mem_to_shadow_realizes tfibsegs B PC_MEM_TO_SHADOW -> sm8_segC` and Seg D's lane states
   `poison_shadow_realizes tfibsegs B PC_POISON_SHADOW -> sm8_segD` (a Theorem Labs lane owns both summaries; a Theorem Labs lane's
   decision, 22:36Z: one published summary each, no inline walk). Neither hypothesis appears in the Props below.

   The start-up tables of a Theorem Labs lane's dry run are unsatisfiable (a review ruling, 22:25Z), so nothing here depends on
   them: no A/AB01, A/AB03, A/AD2j, A/AD1k, A/AF0m, nor their Y twins, in this file or in its imports. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05 AsStackSz.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Rt Require Import StackMalloc8Tbl.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.

(* The data and the premises of the contract, carried into every segment. *)
Definition sm8_entry (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (pos : Z) (S' : astate) (n : Z) : Prop :=
ecall_pre tfibsegs B ly S W regs mem md /\
getr regs 10 = w64 n /\ 8 <= n <= fs_frame_bytes CID8 /\ n mod 8 = 0 /\
count_cid CID8 (frames S) < fs_frames CID8 /\
apath (stack_malloc CID8 S) [] (PFake CID8 pos, S').

(* The five callee-saved words the prologue writes at entry +0x4 .. +0x14 and the epilogue reads back at
   +0x144 .. +0x154. They stay untouched from Seg A to the epilogue, so every cut carries them. *)
Definition sm8_saved (W : world tfibsegs) (regs : bvmap 5 word) (memX : word -> option byte) : Prop :=
rdword (aview tfibsegs (w_H W) memX) (spZ regs - 8) = Some (raZ regs) /\
rdword (aview tfibsegs (w_H W) memX) (spZ regs - 16) = Some (bv_unsigned (getr regs 8)) /\
rdword (aview tfibsegs (w_H W) memX) (spZ regs - 24) = Some (bv_unsigned (getr regs 9)) /\
rdword (aview tfibsegs (w_H W) memX) (spZ regs - 32) = Some (bv_unsigned (getr regs 18)) /\
rdword (aview tfibsegs (w_H W) memX) (spZ regs - 40) = Some (bv_unsigned (getr regs 19)).

(* The callee-saved registers the function never writes: gp, tp and s4..s11. With sm8_saved they give
   aregs_preserved at the return. *)
Definition sm8_regs_kept (regs regsX : bvmap 5 word) : Prop :=
forall r, r = 3 \/ r = 4 \/ 20 <= r <= 27 -> getr regsX (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).

(* Memory outside the walk's stack window is the caller's memory, byte for byte in the RAW memory. It must be
   raw, not reader-level: AR's ahs / ahz (YG0n.v:442-447) constrain raw bytes at band addresses that aview
   hides (YG0q.v:634 aview_band_hidden), so a reader-level clause cannot carry AR to Seg C. *)
Definition sm8_mem_kept (regs : bvmap 5 word) (mem memX : word -> option byte) : Prop :=
forall z : word, ~ (spZ regs - SM8_WIN <= bv_unsigned z < spZ regs) -> memX z = mem z.

Definition sm8_stack_pres (W : world tfibsegs) (regs : bvmap 5 word) (memX : word -> option byte) : Prop :=
forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) memX a.

(* Cut 1, at PC_SM8_LOOP. The register values are MEASURED from the prologue and the frame-count setup
   (entry +0x0 .. +0x98):
     sp = sp0 - SM8_FRAME (+0x0)        s0 = sp0 (+0x18)                s1 = n (+0x1c)
     s2 = F, the thread's fake stack (+0x2c)                            s3 = [F+88] = kStackSizeLog (+0x38)
     a0 = 1 << (kStackSizeLog - 14) = fs_frames 8 = 64, the loop counter (+0x50 .. +0x58)
     a1 = F + kFakeFlagsOff (+0x80, `add a1,s2,a3` with a3 = lui 1 = 4096)
     a2 = [F + 8*8] = the class-8 hint (+0x74)
     a3 = hint + 63 (+0x94)             a4 = F + 4096 + (1020 << 5) = flag_addr ly 8 0 (+0x84)
     a5 = ~((-1) << 6) = 63, the index mask (+0x88)                     a6 = hint + 64 (+0x98)
   Memory is the caller's memory plus the five saved words. *)
Definition sm8_midAB (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z)
(regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
getr regs1 2 = w64 (spZ regs - SM8_FRAME) /\
getr regs1 8 = w64 (spZ regs) /\
getr regs1 9 = w64 n /\
getr regs1 18 = w64 (ly_F ly) /\
getr regs1 19 = w64 kStackSizeLog /\
getr regs1 10 = w64 (fs_frames CID8) /\
getr regs1 11 = w64 (ly_F ly + kFakeFlagsOff) /\
getr regs1 12 = w64 (znth 0 CID8 (fs_hint (st_fs S))) /\
getr regs1 13 = w64 (znth 0 CID8 (fs_hint (st_fs S)) + fs_frames CID8 - 1) /\
getr regs1 14 = w64 (flag_addr ly CID8 0) /\
getr regs1 15 = w64 (fs_frames CID8 - 1) /\
getr regs1 16 = w64 (znth 0 CID8 (fs_hint (st_fs S)) + fs_frames CID8) /\
sm8_regs_kept regs regs1 /\ sm8_saved W regs mem1 /\
sm8_mem_kept regs mem mem1 /\ sm8_stack_pres W regs mem1 /\
same_but_materialized md md1.

(* Cut 2, at PC_SM8_FOUND, the exit the loop takes on a free flag (`beqz t0` at PC_SM8_LOOP + 0xc).
   MEASURED: the loop writes no memory and changes only t0, a0, a2, a3 and a7.
     a2 = hint' - 1 (the hint the model's fs_probe returns, less one: the loop adds 1 per iteration and
          PC_SM8_FOUND adds the last one)
     a7 = pos (PC_SM8_LOOP + 0x0, `and a7,a2,a5`)       a3 = flag_addr ly 8 pos (PC_SM8_LOOP + 0x4)
   The registers Seg C still needs from Seg A (sp, s0, s1, s2, s3, a1) are unchanged. *)
Definition sm8_midBC (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n pos hint' : Z)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
fs_probe (Z.to_nat (fs_frames CID8)) (fs_live (st_fs S)) CID8 (znth 0 CID8 (fs_hint (st_fs S)))
= Some (pos, hint') /\
getr regs2 12 = w64 (hint' - 1) /\
getr regs2 17 = w64 pos /\
getr regs2 13 = w64 (flag_addr ly CID8 pos) /\
getr regs2 2 = w64 (spZ regs - SM8_FRAME) /\
getr regs2 8 = w64 (spZ regs) /\
getr regs2 9 = w64 n /\
getr regs2 18 = w64 (ly_F ly) /\
getr regs2 19 = w64 kStackSizeLog /\
getr regs2 11 = w64 (ly_F ly + kFakeFlagsOff) /\
sm8_regs_kept regs regs2 /\ sm8_saved W regs mem2 /\
sm8_mem_kept regs mem mem2 /\ sm8_stack_pres W regs mem2 /\
same_but_materialized md md2.

(* Cut 3, at PC_POISON_SHADOW, entered by the jal at entry +0x13c.
   MEASURED from PC_SM8_FOUND to that jal. The writes of the phase, and the only writes outside the stack
   window, are
     [F + 8*8] := hint'                           (PC_SM8_FOUND + 0x4)
     [flag_addr ly 8 pos] := 1                    (PC_SM8_FOUND + 0x10, one byte)
     [frame + 0x18] := s0                         (PC_SM8_FOUND + 0x34)
     [frame + fs_frame_bytes 8 - 8] := flag addr  (PC_SM8_FOUND + 0x3c)
   so AR holds for S' here (astack_malloc_law_ok; AR puts no value on a fake frame's shadow, CLASS8-DESIGN.md
   section 2). MemToShadow writes nothing. The registers at the call:
     ra = PC_SM8_MSRET   a0 = frame   a1 = n   a2 = 0   s2 = frame   sp = sp0 - SM8_FRAME   s0 = sp0   s1 = n *)
Definition sm8_midCD (ly : alayout) (S S' : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n pos : Z)
(regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
AR tfibsegs B ly S' W mem3 md3 /\
getr regs3 1 = w64 PC_SM8_MSRET /\
getr regs3 10 = w64 (frame_addr ly CID8 pos) /\
getr regs3 11 = w64 n /\
getr regs3 12 = w64 0 /\
getr regs3 2 = w64 (spZ regs - SM8_FRAME) /\
getr regs3 8 = w64 (spZ regs) /\
getr regs3 9 = w64 n /\
getr regs3 18 = w64 (frame_addr ly CID8 pos) /\
0 <= pos < fs_frames CID8 /\
sm8_regs_kept regs regs3 /\ sm8_saved W regs mem3 /\ sm8_stack_pres W regs mem3 /\
same_but_materialized md md3 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SM8_WIN <= a < spZ regs) ->
~ (ly_F ly + 8 * CID8 <= a < ly_F ly + 8 * CID8 + 8) -> a <> flag_addr ly CID8 pos ->
~ (frame_addr ly CID8 pos <= a < frame_addr ly CID8 pos + fs_frame_bytes CID8) ->
aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) mem a) /\
rdword (aview tfibsegs (w_H W) mem3) (frame_addr ly CID8 pos + fs_frame_bytes CID8 - 8)
= Some (flag_addr ly CID8 pos) /\
(forall a, frame_addr ly CID8 pos <= a < frame_addr ly CID8 pos + fs_frame_bytes CID8 ->
apresent (w_H W) mem3 a) /\
(forall a, shadow_addr (frame_addr ly CID8 pos) <= a <
shadow_addr (frame_addr ly CID8 pos) + fs_frame_bytes CID8 / 8 -> apresent (w_H W) mem3 a).

Definition sm8_segA : Prop :=
forall ly S W regs mem md pos S' n,
sm8_entry ly S W regs mem md pos S' n ->
SRr tfibsegs W (cfg_at tfibsegs PC_STACK_MALLOC_8 regs mem md)
(fun W' c' => W' = W /\ exists regs1 mem1 md1,
c' = cfg_at tfibsegs PC_SM8_LOOP regs1 mem1 md1 /\
sm8_midAB ly S W regs mem md n regs1 mem1 md1).

Definition sm8_segB : Prop :=
forall ly S W regs mem md pos S' n regs1 mem1 md1,
sm8_entry ly S W regs mem md pos S' n ->
sm8_midAB ly S W regs mem md n regs1 mem1 md1 ->
SRr tfibsegs W (cfg_at tfibsegs PC_SM8_LOOP regs1 mem1 md1)
(fun W' c' => W' = W /\ exists regs2 mem2 md2 hint',
c' = cfg_at tfibsegs PC_SM8_FOUND regs2 mem2 md2 /\
sm8_midBC ly S W regs mem md n pos hint' regs2 mem2 md2).

Definition sm8_segC : Prop :=
forall ly S W regs mem md pos S' n hint' regs2 mem2 md2,
sm8_entry ly S W regs mem md pos S' n ->
sm8_midBC ly S W regs mem md n pos hint' regs2 mem2 md2 ->
SRr tfibsegs W (cfg_at tfibsegs PC_SM8_FOUND regs2 mem2 md2)
(fun W' c' => W' = W /\ exists regs3 mem3 md3,
c' = cfg_at tfibsegs PC_POISON_SHADOW regs3 mem3 md3 /\
sm8_midCD ly S S' W regs mem md n pos regs3 mem3 md3).

Definition sm8_segD : Prop :=
forall ly S W regs mem md pos S' n regs3 mem3 md3,
sm8_entry ly S W regs mem md pos S' n ->
sm8_midCD ly S S' W regs mem md n pos regs3 mem3 md3 ->
SRr tfibsegs W (cfg_at tfibsegs PC_POISON_SHADOW regs3 mem3 md3)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S' W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (frame_addr ly CID8 pos) /\
zero_shadow (aview tfibsegs (w_H W) mem') SHADOW_OFF (frame_addr ly CID8 pos) n /\
rdword (aview tfibsegs (w_H W) mem') (frame_addr ly CID8 pos + fs_frame_bytes CID8 - 8)
= Some (flag_addr ly CID8 pos) /\
(forall a, frame_addr ly CID8 pos <= a < frame_addr ly CID8 pos + fs_frame_bytes CID8 ->
apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a ->
~ (spZ regs - ESTACK <= a < spZ regs) ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).

(* Class 8 stays OUTSIDE scene's AsanAPI record (a review ruling (A), 2026-10-28 23:21Z): scene's pc_stack_malloc
   table keeps cid 8 at 0, because the record's astack_malloc_realizes (YG0d.v:285-299) posts zero_shadow of the
   whole class frame with no size premise, and __asan_stack_malloc_8 zeroes only the requested n/8 shadow bytes.
   Consumers (the entry walk, the glue) take the class-8 leaf as ONE named Section hypothesis, with exactly this
   name and type:
     Hypothesis stack_malloc_8_sz : astack_malloc_sz_realizes tfibsegs B PC_STACK_MALLOC_8 CID8.
   It is discharged by m8_of_segs below from sm8_segA .. sm8_segD, the four proved segments (StackMalloc8Closed.v). *)
Lemma m8_of_segs : sm8_segA -> sm8_segB -> sm8_segC -> sm8_segD ->
astack_malloc_sz_realizes tfibsegs B PC_STACK_MALLOC_8 CID8.
Proof.
intros HA HB HC HD ly S W regs mem md pos S' n HPRE Hn Hrng Hmod Hcnt Hpath.
assert (HE : sm8_entry ly S W regs mem md pos S' n).
{ unfold sm8_entry. split; [exact HPRE|]. split; [exact Hn|]. split; [exact Hrng|].
split; [exact Hmod|]. split; [exact Hcnt | exact Hpath]. }
eapply SRr_bind; [exact (HA ly S W regs mem md pos S' n HE)|].
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HM1).
eapply SRr_bind; [exact (HB ly S W regs mem md pos S' n regs1 mem1 md1 HE HM1)|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & hint' & -> & HM2).
eapply SRr_bind; [exact (HC ly S W regs mem md pos S' n hint' regs2 mem2 md2 HE HM2)|].
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HM3).
exact (HD ly S W regs mem md pos S' n regs3 mem3 md3 HE HM3).
Qed.
End e.
End d.
