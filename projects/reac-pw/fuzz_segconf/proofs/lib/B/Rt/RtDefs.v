(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the premise and conclusion parts that cgif_file_fuzzer's lib/YG0d.v states inside each interceptor contract (ecall_pre with a stack window, src_ok, dest_ok, amem_range, range_addressable, shadow_hull_vis, and the post of amemcmp_realizes), taken out as named definitions with the stack window as a parameter, for the string, number and format entries of plugin-hostd/fuzz_command that cgif_file_fuzzer does not call; module names. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtDefs.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Rt/RtDefs.v for fuzz_segconf.asan-ubsan: module paths; and the image-B values named in the commit message. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

(* The scratch window of a runtime call: [stk] bytes below the stack pointer at entry. cgif_file_fuzzer writes the
   window out at each contract, with ESTACK for most entries and 2 * ESTACK for bcmp and strnlen (YG0d.v:352-371,
   :401-419). The string entries of fuzz_command.asan hold up to 2032 + 160 bytes of frame of their own and call
   musl, so each statement below names its own window. *)
Definition ascratch_stk (stk : Z) (regs : bvmap 5 word) (a : Z) : Prop := spZ regs - stk <= a < spZ regs.

Definition ecall_pre_stk (stk : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
ecall_pre segs B ly S W regs mem md /\
ly_stk_lo ly + stk <= spZ regs /\
(forall a, ascratch_stk stk regs a -> apresent (w_H W) mem a).

(* A range the entry may read: cgif_file_fuzzer's src_ok + amem_range + range_addressable + shadow_hull_vis
   (YG0d.v:313-314, 316, 341-343), with the scratch window as a parameter. *)
Definition aread_ok (stk : Z) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (x n : Z) : Prop :=
0 <= x /\ x + n <= 2 ^ 63 /\ 0 <= n < 2 ^ 32 /\
(forall a, x <= a < x + n -> aview segs (w_H W) mem a <> None /\ ~ ascratch_stk stk regs a) /\
amem_range x n /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n /\
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n).

(* A range the entry may write: cgif_file_fuzzer's dest_ok (YG0d.v:311-312) with the window as a parameter. *)
Definition awrite_ok (stk : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (d n : Z) : Prop :=
0 <= d /\ d + n <= 2 ^ 63 /\ 0 <= n < 2 ^ 32 /\
(forall a, d <= a < d + n ->
writable_at segs (mrestrict (w_H W) mem) a /\ ~ aowned B ly S a /\ ~ ascratch_stk stk regs a) /\
amem_range d n /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n /\
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n).

(* The bytes a word-at-a-time musl loop may touch after the terminator at [e]: the same premise cgif_file_fuzzer's
   strnlen and memchr contracts carry (YG0d.v:392, :411). *)
Definition atail_vis (W : world segs) (mem : word -> option byte) (e : Z) : Prop :=
forall a, e < a < e - e mod 8 + 8 -> aview segs (w_H W) mem a <> None.

Definition abytes_at (W : world segs) (mem : word -> option byte) (a : Z) (l : list byte) : Prop :=
forall i, (i < length l)%nat -> aview segs (w_H W) mem (a + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0))).

(* A C string: the same shape the plain proof of fuzz_command uses (lib/Prog/strcmp_c.v:13-14). *)
Definition astr_at (W : world segs) (mem : word -> option byte) (a : Z) (s : list byte) : Prop :=
abytes_at W mem a (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s.

Definition astr_len (s : list byte) : Z := Z.of_nat (length s).

(* The same two notions as a reader takes them, which is the shape the program contracts of lib/A/Prog use. The
   two bridges below say that the reader form over [aview segs (w_H W) mem] and the form above are the same
   statement, so a program walk that meets a runtime contract rewrites with one lemma. *)
Definition abytes_atR (rd : reader) (a : Z) (l : list byte) : Prop :=
forall i, (i < length l)%nat -> rd (a + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0))).

Definition astr_atR (rd : reader) (p : Z) (s : list byte) : Prop :=
abytes_atR rd p (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s.

Lemma abytes_atR_view : forall W mem a l,
abytes_atR (aview segs (w_H W) mem) a l <-> abytes_at W mem a l.
Proof. intros W mem a l. unfold abytes_atR, abytes_at. split; intros H i Hi; exact (H i Hi). Qed.

Lemma astr_atR_view : forall W mem p s,
astr_atR (aview segs (w_H W) mem) p s <-> astr_at W mem p s.
Proof.
intros W mem p s. unfold astr_atR, astr_at. split; intros [H1 H2]; split; try exact H2;
[apply abytes_atR_view | apply abytes_atR_view]; exact H1.
Qed.

(* The conclusion of an entry that returns to [ra], keeps the model state [S], writes only inside its scratch
   window and inside [E], and leaves [Q] true of the registers and the memory it returns. The parts are those of
   cgif_file_fuzzer's amemcmp_realizes conclusion (YG0d.v:344-351). *)
Definition art_post (stk : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(Q : bvmap 5 word -> (word -> option byte) -> Prop) : world segs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
Q regs' mem' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ ascratch_stk stk regs a -> ~ E a ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(forall a, ascratch_stk stk regs a -> apresent (w_H W) mem' a).

(* The stack-protector cells musl reads in strspn, strcspn and the code under them: a pointer word that
   holds the address of the guard object, and the guard word itself. The plain proof of the same binary
   states the same two cells at a call of strspn (lib/Prog/strspn_c.v:35-36). *)
Definition aguard_ok (W : world segs) (mem : word -> option byte) (gotw guard : Z) : Prop :=
rdword (aview segs (w_H W) mem) gotw = Some guard /\
(exists can, rdword (aview segs (w_H W) mem) guard = Some can).


(* The errno cell of the image: musl's strtol writes it, and so does the atoi entry, which calls strtol. *)
Definition aerrno_cell (a : Z) : Prop := as_errno B <= a < as_errno B + 4.

(* The read-only image bytes the runtime entries of this image read on the paths their walks take. A global
   rom_view is not a premise a caller can give: part of .rodata and of the relocated pointer words is owned by the
   runtime (as_owned_static), and arodata_okP says nothing about those. So each contract asks only for the words
   its code reads, as cgif's own interceptor contracts do with mconsts_view over the two musl word-loop constants
   (A/AE39.v:26-45, amemchr0_realizesM, amemchr0_of_M).

   The list is measured: for every function each walk steps through (the interceptor body, musl's body, the range
   check, the shadow helpers; NOT the start-up path, which the walks prune), every address its instructions name
   that lies in .rodata, widened to the symbol that covers it, by the read-only range scanner.
   The named objects are musl's word-loop
   constants 0x10320, 0x10358, 0x10370, the 0xf5 word 0x10340 that __asan_stack_free_5 stores, musl's printf
   prefix table 0x10b87, its state table (0x24098, 464), xdigits (0x24268, 16) and __intscan's digit table
   (0x24278, 257); the rest are the message strings the entries form pointers to. No range of the list meets
   Tfib_owned_static (A/AF0m.v), so a caller discharges the whole list from arodata_okP. *)
Definition RT_ROM_RANGES : list (Z * Z) :=
[ (0x10320, 8); (0x10350, 8); (0x10368, 8); (0x103d8, 8); (0x107e6, 8); (0x107fd, 8);
(0x10b77, 8); (0x124d1, 8); (0x127e7, 8); (0x12889, 8); (0x131a4, 8); (0x131b0, 8); (0x1321b, 8); (0x13ae9, 8);
(0x13af1, 8); (0x13b8b, 8); (0x141b3, 8); (0x14b64, 8); (0x153c4, 8); (0x154fa, 8); (0x15bd0, 8); (0x163af, 8);
(0x1640f, 8); (0x16b3a, 8); (0x1712f, 8); (0x17a94, 8); (0x17b31, 8); (0x18414, 8); (0x19b76, 8); (0x1a25c, 8);
(0x1a263, 8); (0x1a2c5, 8); (0x1ab2b, 8); (0x1ab36, 8); (0x1ab3d, 8); (0x1b473, 8); (0x1c54b, 8); (0x1cd78, 8);
(0x1cd96, 8); (0x1d55e, 8); (0x1dab8, 8); (0x1ec73, 8); (0x1f543, 8); (0x1fbed, 8); (0x204c0, 8); (0x20819, 8);
(0x23318, 8); (0x233f8, 8); (0x23418, 8); (0x23460, 464); (0x23630, 16); (0x23640, 257); (0x23741, 8) ].

Definition rconsts_view (W : world segs) (mem : word -> option byte) (rr : list (Z * Z)) : Prop :=
forall lo n a, In (lo, n) rr -> lo <= a < lo + n ->
aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).

(* The premise itself is the form the other porters of this stream use (libreac/fuzz_identity lib/A/Rt/WrapRo.v
   `aro_unowned`): every read-only byte of the image that the runtime does NOT own reads as the image has it. It is
   the in-segment half of the program walks' arodata_okP, so a caller already has it, and it survives a call whose
   post keeps the bytes that are unowned before and after. RT_ROM_RANGES above is then what each WALK needs out of
   it, and `rconsts_of_rt_rom` takes it, given that the ranges are in the image's read-only segments, unowned and
   not the errno cell (checked by computation for this image in RtRom.v). *)
Definition rt_rom_view (W : world segs) (mem : word -> option byte) : Prop :=
forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ aerrno_cell a ->
aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).

Lemma rconsts_of_rt_rom : forall W mem rr,
(forall lo n a, In (lo, n) rr -> lo <= a < lo + n ->
 in_rom segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ aerrno_cell a) ->
rt_rom_view W mem -> rconsts_view W mem rr.
Proof.
intros W mem rr Hs Hv lo n a Hin Ha.
destruct (Hs lo n a Hin Ha) as (H1 & H2 & H3). exact (Hv a H1 H2 H3).
Qed.

Lemma rt_rom_view_keep : forall W mem mem',
rt_rom_view W mem ->
(forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ aerrno_cell a ->
 aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
rt_rom_view W mem'.
Proof. intros W mem mem' Hv Hk a H1 H2 H3. rewrite (Hk a H1 H2 H3). exact (Hv a H1 H2 H3). Qed.

Lemma rconsts_view_incl : forall W mem rr rr', incl rr' rr -> rconsts_view W mem rr -> rconsts_view W mem rr'.
Proof. intros W mem rr rr' Hi Hv lo n a Hin Ha. exact (Hv lo n a (Hi _ Hin) Ha). Qed.

Lemma rconsts_of_rom_view : forall W mem rr,
(forall lo n a, In (lo, n) rr -> lo <= a < lo + n -> in_rom segs a) ->
rom_view segs W mem -> rconsts_view W mem rr.
Proof. intros W mem rr Hr Hv lo n a Hin Ha. exact (Hv a (Hr lo n a Hin Ha)). Qed.


End c.
End b.
