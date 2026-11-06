(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_scene/lib/A/P_check_step_cut.v (the entry facts, cut states
   and segment statements of check_step's walk) and the composer cs_chain of proofs/libreac/fuzz_scene/lib/A/P_check_step.v
   lines 91-105, both at origin/ossv/recipes 501c0d516c69, for reac-pw/fuzz_rate's check_csv on image A: the contract is
   a callee contract (RtPgCSpec.rt_check_csv_specX, post rt_cpost_o) that continues the caller's journal instead of
   opening one, so every cut carries the caller's journal with check_csv's class-2 frame pushed on the front of own;
   four segments instead of five; the entry facts are the contract's premises; the cuts carry the frame's shadow bytes,
   the realigned frame's cells and the bytes the post compares with the call's state. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvCut.v at b929052adf57; the same cut for
   image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the entry, the three cut pcs, the own frame (192
   instead of 160) and the stack bound (RtPgImgB.T_csv_STK_B) are image B's; the realigned frame's cells are image B's
   five (F twice, n, the list length, buf); the registers every cut carries are image B's (s1 = R1, s8 = F + 32, no
   register holds F) and so are the registers live at each cut. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address below is measured on its unstripped
   twin sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded bytes are the same): the
   statements of record for the walk of check_csv (0x837c0, 1284 bytes, 321 instructions) against
   RtPgCSpec.rt_check_csv_specX rsegs B MT 0x837c0 2 T_csv_STK_B 0x21520.
   Proves no function (kind: statement text). The four segment statements CC_S0_stmt .. CC_S3_stmt are Definitions of
   type Prop, proved by the segment walks; the composer cc_chain (SRr_bind four times, Reusable/YA0n.v) is closed: Qed,
   under no hypothesis. cc_rbase_eq / cc_rbase_bounds are the arithmetic of the realigned base.

   Segments and cut pcs:
     S0  0x837c0 .. 0x83948: the 13 saves, the realignment (`andi sp,sp,-32` 0x83800), the cell R1 + 40 := n, the two
         GOT reads, the class-2 side-stack frame (`li a0,160` + `jal` 0x83838 to the class-2 allocation entry
         0x3d164), the cells R1 + 48 := the list length, R1 + 56 := buf, R1 + 32 := F, R1 + 80 := F, R1 + 24 := F, the
         frame header, the 20 shadow granules (0x838e8-0x83940).
     S1  0x83948 .. 0x83a90: the three passes (i = 0, 1, 2), one statement for every mask; the four bound tests of
         image B's UBSan checks 0x83978 (k = 8), 0x839d4 (n > 39), 0x839fc (k > 8), 0x83a08 (n' + j = 40) branch to
         the `unimp` 0x83c70 and are not taken.
     S2  0x83a90 .. 0x83b38: the reloads of buf, the length and n from the cells, the length test, the n = 0 / n > 0
         arms (the bcmp wrapper at 0x42200, `jal` 0x83abc), the pointer-overflow test buf + c (0x83ac8, to the
         `unimp` 0x83c70, not taken), the last byte and granules 4-8 back to 0xf8; both arms join at 0x83b38.
     S3  0x83b38 .. ret: the retired magic (through the cell R1 + 24), the 32 0xf5 granules, the flag clear (the
         release, the frame read from the cell R1 + 32) and the epilogue.
   Every cut carries the entry facts cc_pre (the contract's premises, as one conjunction) and cc_frame:
   - the caller's journal (YCbq.v ajournal) from its own entry, with own = (2, fpos) :: own and k unchanged (a
     side-stack frame adds no event), at the call's layout lyc; frames = (2, fpos) :: frames Sc with (2, fpos) not among
     the frames of the call; the heap blocks, the chunks, the sections, st_sec_reserved, the event count and the live
     bytes as at the call; the meter mo_le MT Sc S1 0; the I/O state as at the call (same_io); every byte outside the
     stack window [sp - T_csv_STK_B, sp) that the runtime did not own at the call reads as at the call. The post
     (rt_cpost_o) asks each of these of the return state; after the release (YCbq.v aj_flag_store) the state is
     stack_free_state 2 fpos S1, whose frames are frames Sc again, and the owned set is the call's (aowned reads only
     the layout, the chunks and the frames);
   - the frame F = frame_addr lyc 2 fpos: 4096 <= F, F + 256 <= alloc_ceiling, in_app F 256, F mod 32 = 0; the flag
     pointer word at F + 248; the 13 saved registers ra, s0, s1, s2 .. s11 at sp - 8 - 8 j (j < 13), sp the entry sp;
     the realigned frame's cells R1 + 24 = F (`sd a1,24(s1)` 0x838d8), R1 + 32 = F (`sd a0,32(s1)` 0x83870), R1 + 40
     = n (`sd a1,40(s1)` 0x83810), R1 + 48 = |csv_list mask| (`sd s3,48(s1)` 0x83844), R1 + 56 = buf (`sd s2,56(s1)`
     0x83848), R1 = cc_rbase sp = (sp - 192) and -32;
   - gp, tp as at entry; s0 = sp (0x837fc); s1 = R1 (0x83804); s7 = shadow_addr F (0x83898 + 0x838e4); s8 = F + 32
     (want, 0x83880).
   What each cut adds (the registers live at the cut: set on every path to it, read after it):
   - 0x83948 (cc_st1): shadow CC_SH_A, granules 20-31 = 0 (the allocation zeroes all 32); sp = R1; t0 = 10, t1 = 18,
     t2 = 39, t3 = 0 (bytes built), t4 = 0x21520 (closed_list), t5 = 0x66666667, t6 = 44; a2 = i = 0, a3 = F + 112
     (d), a4 = -8, a6 = 3, a7 = 8, s3 = F + 111; s6 = mask (a3 at entry); s9 = SHADOW_OFF (0x83828).
   - 0x83a90 (cc_st2): shadow CC_SH_A (each pass that brings d into scope puts granule 14 back to 0xf8, 0x83a6c);
     want = the bytes csv_bytes (csv_list mask) at F + 32; sp = R1; t3 = |csv_list mask|; s9 = SHADOW_OFF.
   - 0x83b38 (cc_st3): shadow CC_SH_C (granules 4-8 0xf8, 0x83ae4-0x83af8 / 0x83b18-0x83b30); want as at 0x83a90.
     No register besides cc_frame's is live (the release reads s1, s7 and the cells R1 + 24 / R1 + 32, the
     epilogue s0). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YK06.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
(* T_csv_STK_B, check_csv's image-B stack bound (192 + 16 + 2 ESTACK). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the constants ======================================== *)
(* check_csv's entry, its side-stack class (the class-2 allocation entry, 256-byte frames: fs_frame_bytes 2), and
   closed_list (.rodata, 3 x 4 bytes). *)
Definition CC_A : Z := 0x837c0.
Definition CC_CID : Z := 2.
Definition CC_TCL : Z := 0x21520.
(* The cut pcs: the loop head with i = 0, the pc after the three passes, the join of the two tail arms. *)
Definition CC_PC1 : Z := 0x83948.
Definition CC_PC2 : Z := 0x83a90.
Definition CC_PC3 : Z := 0x83b38.
(* The own frame (`addi sp,sp,-192` 0x837c0) and the realigned base R1 = (sp - 192) and -32 (`andi sp,sp,-32`
   0x83800; `mv s1,sp` 0x83804). *)
Definition CC_FRAME : Z := 192.
Definition cc_rbase (sp : Z) : Z := Z.land (sp - CC_FRAME) (-32).
(* The registers the prologue saves (0x837c8-0x837f8), in the order of their slots below the entry sp:
   ra at sp - 8, s0 at sp - 16, s1 at sp - 24, s2 .. s11 at sp - 32 .. sp - 104. *)
Definition cc_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
(* The 20 shadow granules the prologue writes at shadow_addr F + 0 .. + 19 (0x838e8-0x83940): 0-3 left guard 0xf1,
   4-8 want[40] at F + 32 in scope (0x00), 9-13 middle guard 0xf2, 14 d[8] at F + 112 out of scope (0xf8), 15-19 right
   guard 0xf3. CC_SH_C: the same after the tail marks want out of scope (granules 4-8 0xf8). *)
Definition CC_SH_A : list Z :=
[0xf1; 0xf1; 0xf1; 0xf1; 0; 0; 0; 0; 0; 0xf2; 0xf2; 0xf2; 0xf2; 0xf2; 0xf8; 0xf3; 0xf3; 0xf3; 0xf3; 0xf3].
Definition CC_SH_C : list Z :=
[0xf1; 0xf1; 0xf1; 0xf1; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf2; 0xf2; 0xf2; 0xf2; 0xf2; 0xf8; 0xf3; 0xf3; 0xf3; 0xf3; 0xf3].

(* The realigned base is (sp - 192) rounded down to 32; from a 16-aligned sp it is sp - 192 or sp - 208. *)
Lemma cc_rbase_eq : forall sp, cc_rbase sp = (sp - CC_FRAME) / 32 * 32.
Proof.
intros sp. unfold cc_rbase. change (-32) with (Z.lnot (Z.ones 5)).
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma cc_rbase_bounds : forall sp, sp mod 16 = 0 ->
cc_rbase sp mod 32 = 0 /\ sp - CC_FRAME - 16 <= cc_rbase sp <= sp - CC_FRAME.
Proof.
intros sp Hsp. rewrite cc_rbase_eq. unfold CC_FRAME. split; [apply Z.mod_mul; lia|].
pose proof (Z.div_mod (sp - 192) 32 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound (sp - 192) 32 ltac:(lia)) as Hb.
pose proof (Z.div_mod sp 16 ltac:(lia)) as Hs. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* The 13 saved registers of the entry registers regs, in their slots below the entry sp. *)
Definition cc_saved (regs : bvmap 5 word) (rd : reader) : Prop :=
forall j, (j < 13)%nat ->
rdword rd (spZ regs - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr regs (Z_to_bv 5 (nth j cc_saved_regs 0)))).

(* The entry facts: the premises of rt_check_csv_specX rsegs B MT 0x837c0 2 T_csv_STK_B 0x21520, as one conjunction,
   over the contract's variables in the contract's order. *)
Definition cc_pre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (buf n mask : Z) : Prop :=
rt_cpre rsegs B STK sp0 FP ly S W0 mem0 md0 own k T_csv_STK_B regs lyc Sc W memc mdc /\
getr regs 10 = w64 buf /\ getr regs 11 = w64 n /\ 0 <= n <= 23 /\
getr regs 12 = w64 (Z.of_nat (length (RateCsv.csv_list mask))) /\ getr regs 13 = w64 mask /\ 0 <= mask < 2 ^ 64 /\
0 < buf /\ buf + Z.max n 1 <= 2 ^ 63 /\
(exists m, In (buf, m) (ablocks B lyc Sc) /\ Z.max n 1 <= m) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF buf (Z.max n 1) /\
shadow_hull_vis (aview rsegs (w_H W) memc) buf (Z.max n 1) /\ amem_range buf (Z.max n 1) /\
(buf + Z.max n 1 <= spZ regs - T_csv_STK_B \/ spZ regs <= buf) /\
(n = 0 -> garr8 rsegs (mrestrict (w_H W) memc) buf [0x5a]) /\
(0 < n -> garr8 rsegs (mrestrict (w_H W) memc) buf (RateCsv.csv_cut (RateCsv.csv_list mask) n ++ [0])) /\
0 <= CC_CID <= 10 /\ count_cid CC_CID (frames Sc) < fs_frames CC_CID /\
rt_i32tab rsegs (w_H W) memc CC_TCL RateCfg.closed_list.

(* The contract's post at the instance. *)
Definition cc_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) : world rsegs -> config -> Prop :=
rt_cpost_o rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T_csv_STK_B regs lyc Sc W memc mdc
(fun f => f = fx) (fun x => aowned B lyc Sc x) (fun _ _ _ => True).

(* What every cut carries besides the entry facts (header): the journal with the frame (2, fpos) on the front of own,
   the state facts the post compares with the call's state, the frame's bounds, flag pointer word, saved registers
   and realigned cells, and the registers that hold gp, tp, s0 = sp, s1 = R1, s7 = shadow_addr F and s8 = F + 32. *)
Definition cc_frame (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (buf n mask : Z)
(fpos : Z) (S1 : astate) (W1 : world rsegs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 ((CC_CID, fpos) :: own) lyc S1 W1 mem1 md1 k /\
frames S1 = (CC_CID, fpos) :: frames Sc /\ ~ In (CC_CID, fpos) (frames Sc) /\
ablocks B lyc S1 = ablocks B lyc Sc /\
st_chunks S1 = st_chunks Sc /\ st_secs S1 = st_secs Sc /\ st_sec_reserved S1 = st_sec_reserved Sc /\
st_nev S1 = st_nev Sc /\ blocks_bytes S1 = blocks_bytes Sc /\
mo_le MT Sc S1 0 /\ same_io mdc md1 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_csv_STK_B <= a < spZ regs) -> ~ aowned B lyc Sc a ->
 aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a) /\
4096 <= frame_addr lyc CC_CID fpos /\ frame_addr lyc CC_CID fpos + 256 <= alloc_ceiling /\
in_app (frame_addr lyc CC_CID fpos) 256 /\ frame_addr lyc CC_CID fpos mod 32 = 0 /\
rdword (aview rsegs (w_H W1) mem1) (frame_addr lyc CC_CID fpos + 248) = Some (flag_addr lyc CC_CID fpos) /\
cc_saved regs (aview rsegs (w_H W1) mem1) /\
rdword (aview rsegs (w_H W1) mem1) (cc_rbase (spZ regs) + 24) = Some (frame_addr lyc CC_CID fpos) /\
rdword (aview rsegs (w_H W1) mem1) (cc_rbase (spZ regs) + 32) = Some (frame_addr lyc CC_CID fpos) /\
rdword (aview rsegs (w_H W1) mem1) (cc_rbase (spZ regs) + 40) = Some n /\
rdword (aview rsegs (w_H W1) mem1) (cc_rbase (spZ regs) + 48) = Some (Z.of_nat (length (RateCsv.csv_list mask))) /\
rdword (aview rsegs (w_H W1) mem1) (cc_rbase (spZ regs) + 56) = Some buf /\
getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\ getr regs1 8 = w64 (spZ regs) /\
getr regs1 9 = w64 (cc_rbase (spZ regs)) /\
getr regs1 23 = w64 (shadow_addr (frame_addr lyc CC_CID fpos)) /\
getr regs1 24 = w64 (frame_addr lyc CC_CID fpos + 32).

(* 0x83948, the loop head with i = 0. *)
Definition cc_st1 (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (buf n mask : Z)
(fpos : Z) (S1 : astate) (W1 : world rsegs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
cc_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask /\
cc_frame STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 /\
rt_fsh rsegs (w_H W1) mem1 (frame_addr lyc CC_CID fpos) (CC_SH_A ++ repeat 0 12) /\
getr regs1 2 = w64 (cc_rbase (spZ regs)) /\
getr regs1 5 = w64 10 /\ getr regs1 6 = w64 18 /\ getr regs1 7 = w64 39 /\
getr regs1 12 = w64 0 /\ getr regs1 13 = w64 (frame_addr lyc CC_CID fpos + 112) /\ getr regs1 14 = w64 (-8) /\
getr regs1 16 = w64 3 /\ getr regs1 17 = w64 8 /\
getr regs1 19 = w64 (frame_addr lyc CC_CID fpos + 111) /\ getr regs1 22 = w64 mask /\
getr regs1 25 = w64 SHADOW_OFF /\ getr regs1 28 = w64 0 /\ getr regs1 29 = w64 CC_TCL /\
getr regs1 30 = w64 0x66666667 /\ getr regs1 31 = w64 44.

(* 0x83a90, after the three passes: want holds the list, t3 its length. *)
Definition cc_st2 (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (buf n mask : Z)
(fpos : Z) (S1 : astate) (W1 : world rsegs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
cc_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask /\
cc_frame STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 /\
rt_fsh rsegs (w_H W1) mem1 (frame_addr lyc CC_CID fpos) (CC_SH_A ++ repeat 0 12) /\
mbytes_at rsegs (mrestrict (w_H W1) mem1) (frame_addr lyc CC_CID fpos + 32)
(RateCsv.csv_bytes (RateCsv.csv_list mask)) /\
getr regs1 2 = w64 (cc_rbase (spZ regs)) /\
getr regs1 25 = w64 SHADOW_OFF /\
getr regs1 28 = w64 (Z.of_nat (length (RateCsv.csv_list mask))).

(* 0x83b38, the join of the two tail arms: want out of scope. *)
Definition cc_st3 (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (buf n mask : Z)
(fpos : Z) (S1 : astate) (W1 : world rsegs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
cc_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask /\
cc_frame STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 /\
rt_fsh rsegs (w_H W1) mem1 (frame_addr lyc CC_CID fpos) (CC_SH_C ++ repeat 0 12) /\
mbytes_at rsegs (mrestrict (w_H W1) mem1) (frame_addr lyc CC_CID fpos + 32)
(RateCsv.csv_bytes (RateCsv.csv_list mask)).

(* ---- the four segment statements ---- *)
Definition CC_S0_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf n mask : Z),
cc_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask ->
SRr rsegs W (cfg_at rsegs CC_A regs memc mdc)
(fun W1 c1 => exists fpos S1 regs1 mem1 md1, c1 = cfg_at rsegs CC_PC1 regs1 mem1 md1 /\
cc_st1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1).
Definition CC_S1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf n mask : Z)
(fpos : Z) S1 W1 (regs1 : bvmap 5 word) mem1 md1,
cc_st1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 ->
SRr rsegs W1 (cfg_at rsegs CC_PC1 regs1 mem1 md1)
(fun W2 c2 => exists S2 regs2 mem2 md2, c2 = cfg_at rsegs CC_PC2 regs2 mem2 md2 /\
cc_st2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S2 W2 regs2 mem2 md2).
Definition CC_S2_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf n mask : Z)
(fpos : Z) S1 W1 (regs1 : bvmap 5 word) mem1 md1,
cc_st2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 ->
SRr rsegs W1 (cfg_at rsegs CC_PC2 regs1 mem1 md1)
(fun W2 c2 => exists S2 regs2 mem2 md2, c2 = cfg_at rsegs CC_PC3 regs2 mem2 md2 /\
cc_st3 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S2 W2 regs2 mem2 md2).
Definition CC_S3_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf n mask : Z)
(fpos : Z) S1 W1 (regs1 : bvmap 5 word) mem1 md1,
cc_st3 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 ->
SRr rsegs W1 (cfg_at rsegs CC_PC3 regs1 mem1 md1)
(cc_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).

(* The composition: the contract from the four segment statements, by SRr_bind alone. *)
Lemma cc_chain : CC_S0_stmt -> CC_S1_stmt -> CC_S2_stmt -> CC_S3_stmt ->
rt_check_csv_specX rsegs B MT 0x837c0 2 T_csv_STK_B 0x21520.
Proof.
intros H0 H1 H2 H3. unfold rt_check_csv_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask
P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19.
assert (HP : cc_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask)
by (unfold cc_pre, CC_CID, CC_TCL; tauto).
eapply SRr_bind; [exact (H0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask HP)|].
intros W1 c1 _ (fpos & S1 & regs1 & mem1 & md1 & -> & HS1).
eapply SRr_bind;
[exact (H1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 HS1)|].
intros W2 c2 _ (S2 & regs2 & mem2 & md2 & -> & HS2).
eapply SRr_bind;
[exact (H2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S2 W2 regs2 mem2 md2 HS2)|].
intros W3 c3 _ (S3 & regs3 & mem3 & md3 & -> & HS3).
exact (H3 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S3 W3 regs3 mem3 md3 HS3).
Qed.
End d.

About cc_chain.
Print Assumptions cc_chain.
