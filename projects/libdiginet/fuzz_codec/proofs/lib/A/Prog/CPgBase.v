(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: lines 18-46 of proofs/libreac/fuzz_knock/lib/A/APgBase.v
   (origin/ossv/recipes 4b6f0df50aa7: in_roP, arodata_okP, ro_below_ofl, ro_spares, arodata_ok_journalP), in the
   form projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgBase.v states them, for libdiginet/fuzz_codec's ASan builds; knock's
   afobj / apost_base are not carried (codec hands its callees objects that are 4-aligned, so the contracts use
   the caller-journal shapes of lib/A/Prog/CodecCJ.v instead). The rest of this file is codec's own. *)
(* The vocabulary the A-level contracts of fuzz_codec's own functions are stated over.
   - the image's read-only data (in_roP / arodata_okP), image-independent;
   - the register forms of the C arguments, the byte-list results and the call record, carried from the
     plain contracts' lib/Prog/codec_cells.v with `list Z` in place of `list byte` (the ASan memory
     predicates garr8 / val_mem read Z, not the plain image's bytes);
   - the premise bundles every contract uses: what a call may write (cdst_ok), what it reads (crd_ok), how
     a personality argument arrives (pers_argA), where the call record lies (kcall_atA);
   - the stack each call uses below its caller's sp, measured from the image;
   - the shared journal premise (cdc_entry) and the shared post (cdc_post).
   IMAGE-INDEPENDENT: no image module is required here; the addresses a contract needs (the personality
   table, the glyph table) are parameters of the contract that states them. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================= the image's read-only data (knock APgBase) ======================= *)
Definition in_roP (segs : list Segment) (rlo rhi : Z) (a : Z) : Prop :=
(exists s, In s segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))
\/ (rlo <= a < rhi).
Definition arodata_okP (segs : list Segment) (rlo rhi : Z) (B : asyms) (rd : reader) : Prop :=
forall a, in_roP segs rlo rhi a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Class ro_below_ofl (segs : list Segment) (rlo rhi : Z) {SK : YI16.sink_head} : Prop :=
ro_below_ofl_at : forall a, in_roP segs rlo rhi a -> a < YI16.sk_ofl_head.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variables rlo rhi : Z.
Hypothesis relro_img : forall a, rlo <= a < rhi -> in_img segs a.
Context {RO : ro_below_ofl segs rlo rhi}.
Lemma ro_spares : forall FP a, in_roP segs rlo rhi a -> fp_spares FP a.
Proof. intros FP a Hro. apply fp_spares_below. exact (@ro_below_ofl_at segs rlo rhi SK RO a Hro). Qed.
Lemma arodata_ok_journalP : forall B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> arodata_okP segs rlo rhi B (aview segs (w_H W') mem').
Proof.
intros B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (ro_spares FP a Hro)].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
exact (relro_img a Hgot).
Qed.
End e.
End d.

(* ============== the carried vocabulary of the plain contracts, over list Z ==============
   lib/Prog/codec_cells.v states these over `list byte` of the plain image; the ASan reader gives Z, so the
   same functions are restated over `list Z`. Each one is the plain text with `bv_unsigned (Z_to_bv 8 .)`
   written as the modulo it is (DgnSpec's u8). *)

(* A 32-bit C argument v as the callers pass it: they load the field with lw, so the register holds v
   sign-extended from bit 31. *)
Definition arg_u32A (r : word) (v : Z) : Prop := 0 <= v < 2 ^ 32 /\ r = w64 (s32 v).
(* An int argument v in [-2^31, 2^31): the register holds v sign-extended. *)
Definition arg_s32A (r : word) (v : Z) : Prop := - 2 ^ 31 <= v < 2 ^ 31 /\ r = w64 v.
(* A uint8_t / uint16_t argument (w = 8 / 16) loaded with lbu / lhu: zero-extended. *)
Definition arg_zxA (w : Z) (r : word) (v : Z) : Prop := 0 <= v < 2 ^ w /\ r = w64 v.

(* The bytes before the first 0 of a C string. *)
Fixpoint cstringZ (l : list Z) : list Z :=
match l with [] => [] | x :: l' => if x =? 0 then [] else x :: cstringZ l' end.

(* The four low bytes of a 32-bit key. *)
Definition le4Z (k : Z) : list Z :=
[k mod 256; (k / 256) mod 256; (k / 65536) mod 256; (k / 16777216) mod 256].

(* The 32 bytes of a command after an encoder returns (rc, o), from the 32 bytes before the call: on
   failure (o = None) unchanged; on success bytes[0..len), len, display and key written, the bytes from
   len to 24 and the padding unchanged. *)
Definition cmd_outZ (before : list Z) (o : option cmd) : list Z :=
match o with
| None => before
| Some (bs, key, disp) =>
    map u8 bs ++ skipn (length bs) (firstn 24 before) ++ [u8 (Z.of_nat (length bs)); u8 disp]
      ++ firstn 2 (skipn 26 before) ++ le4Z key
end.
(* The len, display and key fields of the 32 bytes o of a command. *)
Definition cmd_lenZ (o : list Z) : Z := nth 24 o 0.
Definition cmd_displayZ (o : list Z) : Z := nth 25 o 0.
Definition cmd_keyZ (o : list Z) : Z := fold_right (fun b acc => b + 256 * acc) 0 (firstn 4 (skipn 28 o)).

(* The two announce names, "CNTRL|24" and "MAINUNIT". *)
Definition NAME_C24A : list Z := [0x43; 0x4e; 0x54; 0x52; 0x4c; 0x7c; 0x32; 0x34].
Definition NAME_PCA : list Z := [0x4d; 0x41; 0x49; 0x4e; 0x55; 0x4e; 0x49; 0x54].
(* diginet_personality_of (diginet_codec.c:27-33) on the argument register value d, with the address of
   personalities[0] as the parameter P. *)
Definition pers_ofA (P : Z) (d : Z) : Z := if d =? 1 then P else if d =? 2 then P + 24 else 0.
(* diginet_personality_from_name (diginet_codec.c:17-25) for the C string tb. *)
Definition from_name_resA (P : Z) (tb : list Z) : Z :=
if list_eq_dec Z.eq_dec (cstringZ tb) NAME_C24A then P
else if list_eq_dec Z.eq_dec (cstringZ tb) NAME_PCA then P + 24 else 0.

(* struct call (fuzz_codec.c:74-90; 184 bytes), over list Z. *)
Record kcallZ := mkKcallZ {
  kz_kind : Z; kz_p : Z; kz_desk : Z;
  kz_a : Z; kz_b : Z; kz_c : Z; kz_delta : Z;
  kz_bytes : list Z; kz_n : Z; kz_rc : Z;
  kz_before : list Z; kz_out : list Z;
  kz_want_rc : Z; kz_want : list Z; kz_want_len : Z; kz_want_key : Z; kz_want_display : Z }.
(* Each scalar field in the range of its C type, each array of its C length. *)
Definition kcall_wfZ (k : kcallZ) : Prop :=
  - 2 ^ 31 <= kz_kind k < 2 ^ 31 /\ 0 <= kz_p k < 2 ^ 64 /\ 0 <= kz_desk k < 2 ^ 64 /\
  0 <= kz_a k < 2 ^ 32 /\ 0 <= kz_b k < 2 ^ 32 /\ 0 <= kz_c k < 2 ^ 32 /\ - 2 ^ 31 <= kz_delta k < 2 ^ 31 /\
  0 <= kz_n k < 2 ^ 64 /\ - 2 ^ 31 <= kz_rc k < 2 ^ 31 /\ - 2 ^ 31 <= kz_want_rc k < 2 ^ 31 /\
  0 <= kz_want_len k < 2 ^ 64 /\ 0 <= kz_want_key k < 2 ^ 32 /\ - 2 ^ 31 <= kz_want_display k < 2 ^ 31 /\
  length (kz_bytes k) = 24%nat /\ length (kz_before k) = 32%nat /\ length (kz_out k) = 32%nat /\
  length (kz_want k) = 24%nat.
(* k with want, want_len and want_display replaced (what owe_sysex writes). *)
Definition set_wantZ (k : kcallZ) (w : list Z) (wl wd : Z) : kcallZ :=
  mkKcallZ (kz_kind k) (kz_p k) (kz_desk k) (kz_a k) (kz_b k) (kz_c k) (kz_delta k)
           (kz_bytes k) (kz_n k) (kz_rc k) (kz_before k) (kz_out k)
           (kz_want_rc k) w wl (kz_want_key k) wd.

(* ========================= the stack each call uses below its caller's sp =========================
   Measured from image A: the real frame of the prologue, 32 bytes more where the function realigns sp
   (`andi sp,sp,-32` with sp 16-aligned), and below that the window the deepest call it makes needs --
   ESTACK for a frame request or for __asan_memset / __asan_memcpy, 2 * ESTACK for the bcmp and strcmp
   wrappers (lib/Reusable/YG0d.v abcmp_realizes), or the callee's own T. The real-stack fallback of a frame
   request is not reached (the use-after-return cell reads 1, and the frame-room premise keeps the request
   from being refused); T does not cover it. *)
Definition T_pers_of : Z := 0.
Definition T_ring_dot : Z := 0.
Definition T_ring_fill : Z := 0.
Definition T_meter_mask : Z := 0.
Definition T_meter_segs : Z := 0.
Definition T_seg7 : Z := 16.
Definition T_owed_seg7 : Z := 16.
Definition T_fader : Z := 16.
Definition T_button : Z := 16.
Definition T_touch : Z := 16.
Definition T_vpot : Z := 16.
Definition T_jog : Z := 16.
Definition T_sleds : Z := 16.
Definition T_cleds : Z := 16.
Definition T_sysex : Z := 48 + ESTACK.
Definition T_ring : Z := 48 + ESTACK.
Definition T_meter : Z := 48 + ESTACK.
Definition T_counter : Z := 64 + ESTACK.
Definition T_scribble : Z := 160 + T_sysex.
Definition T_scribble_text : Z := 16 + ESTACK.
Definition T_counter_text : Z := 192 + ESTACK.
Definition T_owed_counter_text : Z := 192 + ESTACK.
Definition T_from_name : Z := 48 + 2 * ESTACK.
Definition T_text_arg : Z := 32 + ESTACK.
Definition T_check_refusal : Z := 16.
Definition T_check_range : Z := 32 + 2 * ESTACK.
Definition T_check_bytes : Z := 32 + 2 * ESTACK.
Definition T_check_masks : Z := 48.
Definition T_check_seg7 : Z := 48 + T_owed_seg7.
Definition T_check_pers : Z := 32 + T_from_name.
Definition T_check_text_scribble : Z := 160 + 2 * ESTACK.
(* 192 of its own (real frame 160, 32 for the realignment at image A 0x83b9c), then the deepest window
   below it: the bcmp wrapper's 2 * ESTACK, which is deeper than either text callee's T. *)
Definition T_check_text_counter : Z := 192 + 2 * ESTACK.
(* No own function of codec calls the allocator or makes a system call, and a side-stack frame request
   counts no event and adds no heap block. *)
Definition EV_CDC : Z := 0.
Definition LIVE_CDC : Z := 0.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section f.
Variable B : asyms.
Variable MT : ameter_ops.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* [q, q + n) is off the window the call and its own calls use below sp. For a byte of a heap block or of
   a side-stack frame this follows from the journal (the window is above the allocator ceiling); an object
   on the caller's machine stack takes the right disjunct. *)
Definition coff_win (sp T q n : Z) : Prop := q + n <= sp - T \/ sp <= q.

(* A range the call reads, with instrumented loads or through a wrapper: its bytes readable and marked
   usable, the shadow bytes of its 8-byte window readable, in application memory, off the call's window. *)
Definition crd_ok (W : world segs) (memc : word -> option byte) (sp T q n : Z) : Prop :=
0 <= q /\ q + n <= 2 ^ 63 /\
(forall a, q <= a < q + n -> aview segs (w_H W) memc a <> None) /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF q n /\
(0 < n -> shadow_hull_vis (aview segs (w_H W) memc) q n) /\
amem_range q n /\ coff_win sp T q n.

(* The shadow of a range of the image says `usable` in EVERY state of the run, not only at the call's
   entry. A fact taken at the entry state does not reach the read: a side-stack frame request keeps only
   the bytes that are not the runtime's own (lib/Reusable/YG0d.v astack_malloc_realizes), a call keeps
   the bytes of the image outside the runtime's own statics and the errno word, but not the shadow of one (lib/A/Prog/CodecCJ.v tcj_kept), and the shadow byte
   of a global IS the runtime's own (aowned covers the shadow of the low and high memory zones,
   YG0n.v:427-433). The start-up certificate of the registered globals gives the invariant form
   (lib/A/Prog/CodecRo.v globs_marked / img_shadow_vis, through ro_usable_glob / ro_hull), so every
   contract asks for that and no caller has to re-prove it per state. *)
Definition cimg_usable (q n : Z) : Prop :=
forall ly' S' (W' : world segs) mem' md', AR segs B ly' S' W' mem' md' ->
range_addressable (aview segs (w_H W') mem') SHADOW_OFF q n /\
(0 < n -> shadow_hull_vis (aview segs (w_H W') mem') q n).
(* A range of the image a call reads. Every byte of it is in the image, is none of the runtime's own
   statics, and is off the errno word. The first two make the byte not the runtime's at all
   (AR_owned_image_law), so a side-stack frame request keeps it; the third is what a CALL keeps it by,
   because a call's post keeps an image byte only outside errno (lib/A/Prog/CodecCJ.v tcj_kept's image
   clause, and the same clause of ajournal). A function that reads an image object again after a call of
   its own -- diginet_counter_encode re-reads p->counter_addr after diginet_sysex_encode returns (image B
   0x870dc; image A inlines sysex_encode there) -- has
   nothing else to carry those bytes by. The range is also in application memory, off the call's window,
   and its shadow is usable in every state. *)
Definition cimg_range (sp T q n : Z) : Prop :=
0 <= q /\ 0 < n /\ q + n <= 2 ^ 63 /\ amem_range q n /\ coff_win sp T q n /\
(forall a, q <= a < q + n ->
   in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) /\
cimg_usable q n.

(* [q, q + n) lies in ONE object of the call state: one heap block, or one live side-stack frame. The
   bytes of either are the client's (aclient_byte, YG0n.v:421-426), so the call's own frame request, its
   calls and the fill and copy helpers all keep them. The shadow of the range comes from AR at whatever
   state the read happens in -- for a block from AR_shadow_law, for a live frame from the walk's own map
   -- and the copy helper asks for the shadow window of the whole range (shadow_hull_vis), which AR gives
   only inside ONE object; a range that straddled two would not have it. *)
Definition cobj_ok (lyc : alayout) (Sc : astate) (q n : Z) : Prop :=
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= q /\ q + n <= b + req_size m) \/
(exists cid pos, In (cid, pos) (frames Sc) /\
 frame_addr lyc cid pos <= q /\ q + n <= frame_addr lyc cid pos + fs_frame_bytes cid).

(* A range the call writes: in a heap block or a live side-stack frame of the call state, the caller's to
   write, marked usable, its shadow window readable (the wrappers ask for that), off the call's window. *)
Definition cdst_ok (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world segs) (memc : word -> option byte)
(sp T q n : Z) : Prop :=
0 < q /\ q + n <= 2 ^ 63 /\
tdst_ok B lyc Sc q n /\
twr_ok segs B STK sp0 FP ly S lyc Sc own W memc sp q n /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF q n /\
(0 < n -> shadow_hull_vis (aview segs (w_H W) memc) q n) /\
amem_range q n /\ coff_win sp T q n.

(* The personality argument in a0: NULL for None, else the address of a registered personality whose four
   byte fields at p + 16 .. p + 19 are those of d. The encoders read those four bytes only. *)
Definition pers_argA (W : world segs) (memc : word -> option byte) (sp T p : Z) (pd : option desk) : Prop :=
match pd with
| None => p = 0
| Some d =>
    0 < p /\ p + 20 <= 2 ^ 63 /\
    0 <= d_dev d < 256 /\ 0 <= d_strips d < 256 /\ 0 <= d_chars d < 256 /\ 0 <= d_counter d < 256 /\
    garr8 segs (rd W memc) (p + 16) [d_dev d; d_strips d; d_chars d; d_counter d] /\
    cimg_range sp T (p + 16) 4
end.
(* The four personality bytes are not bytes the call writes (the fresh review of the plain contracts,
   defect D1 / D2: a read area may not overlap an area the function writes first). *)
Definition cpers_disj (pd : option desk) (p q n : Z) : Prop :=
match pd with None => True | Some _ => p + 20 <= q \/ q + n <= p + 16 end.

(* Where the call record lies: its 184 bytes at q hold the fields of k. *)
Definition kcall_atA (W : world segs) (memc : word -> option byte) (q : Z) (k : kcallZ) : Prop :=
val_mem segs (rd W memc) q 4 (kz_kind k) /\
val_mem segs (rd W memc) (q + 8) 8 (kz_p k) /\
val_mem segs (rd W memc) (q + 16) 8 (kz_desk k) /\
val_mem segs (rd W memc) (q + 24) 4 (kz_a k) /\
val_mem segs (rd W memc) (q + 28) 4 (kz_b k) /\
val_mem segs (rd W memc) (q + 32) 4 (kz_c k) /\
val_mem segs (rd W memc) (q + 36) 4 (kz_delta k) /\
garr8 segs (rd W memc) (q + 40) (kz_bytes k) /\
val_mem segs (rd W memc) (q + 64) 8 (kz_n k) /\
val_mem segs (rd W memc) (q + 72) 4 (kz_rc k) /\
garr8 segs (rd W memc) (q + 76) (kz_before k) /\
garr8 segs (rd W memc) (q + 108) (kz_out k) /\
val_mem segs (rd W memc) (q + 140) 4 (kz_want_rc k) /\
garr8 segs (rd W memc) (q + 144) (kz_want k) /\
val_mem segs (rd W memc) (q + 168) 8 (kz_want_len k) /\
val_mem segs (rd W memc) (q + 176) 4 (kz_want_key k) /\
val_mem segs (rd W memc) (q + 180) 4 (kz_want_display k).

(* The caller's journal and the facts every call of codec's own code needs, with T the stack the call
   uses below the caller's sp (K A/APgCSpec.v:61-77; Q QPgCSpec.v:95-106). *)
Definition cdc_entry (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
(regs : bvmap 5 word) (T : Z) : Prop :=
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - T /\ spZ regs <= sp0 /\
st_nev S + k + EV_CDC <= EV_MAX /\ blocks_bytes Sc + LIVE_CDC <= LIVE_MAX.

(* The post every call of codec's own code has: the caller's journal extended by the call's events, the
   callee-saved registers and the frames of the call state kept, the blocks a permutation, the input and
   the meter unchanged, everything kept but the call's own stack window and the bytes E it writes
   (CodecCJ's tcj_kept), and the call's own result R. *)
Definition cdc_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word) (T : Z)
(E : Z -> Prop)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(R : world segs -> (word -> option byte) -> bvmap 5 word -> Prop)
: world segs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_CDC) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
tcj_kept segs B T lyc Sc W memc W2 mem2 (spZ regs) E /\
R W2 mem2 regs2.
(* A call that writes nothing outside its own stack window. *)
Definition cno_wr : Z -> Prop := fun _ => False.
(* A range the call writes on the caller's machine stack (text_arg's struct fuzz_in): the stack's shadow
   is zero in every state (AR_zshadow_law), so the usable facts come from the layout, not from a block. *)
Definition cdstk_ok (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world segs) (memc : word -> option byte)
(sp T q n : Z) : Prop :=
0 < q /\ q + n <= 2 ^ 63 /\
ly_stk_lo lyc <= q /\ q + n <= ly_stk_hi lyc /\
twr_ok segs B STK sp0 FP ly S lyc Sc own W memc sp q n /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF q n /\
(0 < n -> shadow_hull_vis (aview segs (w_H W) memc) q n) /\
amem_range q n /\ coff_win sp T q n.
(* The tables of the image a call reads: the read-only data holds the image's bytes, and each range is
   inside the read window and usable in every state (cimg_range). The list is the call's own ranges and
   those of every function it calls. *)
Definition cimg_rd (RLO RHI : Z) (W : world segs) (memc : word -> option byte) (sp T : Z)
(l : list (Z * Z)) : Prop :=
arodata_okP segs RLO RHI B (aview segs (w_H W) memc) /\
Forall (fun r => (forall i, 0 <= i < snd r -> in_roP segs RLO RHI (fst r + i)) /\
                 cimg_range sp T (fst r) (snd r)) l.
(* A C string the call reads: its bytes, a 0 among them, and the range marked usable. *)
Definition cstr_rd (W : world segs) (memc : word -> option byte) (sp T q : Z) (tb : list Z) : Prop :=
0 < q /\ garr8 segs (mrestrict (w_H W) memc) q tb /\ In 0 tb /\
crd_ok W memc sp T q (Z.of_nat (length tb)).
End f.
End c.
End b.

(* text_arg (fuzz_codec.c:523-529) on the cursor bytes data (struct fuzz_in, fuzz.h:29-70), carried from
   lib/Prog/codec_cells.v over list Z: fuzz_u16 takes two bytes, a missing byte reads 0; fuzz_take gives
   the text length. *)
Definition text_u16Z (data : list Z) : Z := nth 0 data 0 + 256 * nth 1 data 0.
Definition text_hdrZ (data : list Z) : nat := Nat.min 2 (length data).
Definition text_lenZ (data : list Z) : nat :=
Nat.min (Z.to_nat (text_u16Z data mod 65)) (length data - text_hdrZ data).
Definition text_takenZ (data : list Z) : list Z := firstn (text_lenZ data) (skipn (text_hdrZ data) data).
Definition text_usedZ (data : list Z) : nat := (text_hdrZ data + text_lenZ data)%nat.
