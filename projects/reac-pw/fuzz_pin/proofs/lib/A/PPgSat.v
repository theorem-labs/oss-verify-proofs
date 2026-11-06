(* The T0.6 record (stream rule 1j-bis) of reac-pw/fuzz_pin's ASan-level contracts (lib/A/PPgCSpec.v,
   lib/A/PPgWrap.v) and of lib/A/PPgLib.v's statement. This file proves no function of the binary (kind:
   satisfiability audit). It holds no Admitted, admit, Axiom or Parameter.

   THE METER IS THE REAL ONE. The consumer of PPgLib's statement fixes the meter: lib/A/AD2o.v hands the
   driver `ameter_triv` (knock's lib/A/AD2o.v:39-41 at origin/ossv/recipes 6ebe35ba632 passes
   `ameter_triv APgLib.XL0 APgLib.XL0 APgLib.RO_LO APgLib.RO_HI` into DRV_MAINX, and knock's
   lib/A/APgLib.v:305 states knock_lib_x_all at `TfibB ameter_triv XL0 XL0 RO_LO RO_HI`; fuzz_qdisc's and
   fuzz_grant's closes do the same). Pin's close does the same (lib/A/PPgLib.v pin_lib_x_all). So
   `ameter_triv` is pin's own meter at that call. The one meter PREMISE of the contracts, LIB1's
   `mo_ok MT S (XM_LIB n)`, is witnessed at it by pin_sat_meter; the callee contracts state the meter only
   in their posts (`mo_le MT Sc S2 0`).

   WHICH LEMMA COVERS WHICH CLAUSE. Three kinds, as the lane owner approved them: (a) a closed lemma at pin's
   measured numbers; (b) a closed lemma at the reflexive journal of any entry state; (c) a call-site lemma
   that needs the walk's state, named with its file and call-site address in
   proofs/reac-pw/fuzz_pin/provenance/P4-WALKPLAN.md section 6 as a P4b deliverable, and, for the top
   claim, P5's closed theorem lib/A/AD2o.v ASAN_T_closed. A clause is put under (c) only when it names the
   walk's own state (a frame of `own`, a heap block of `ablocks`, the allocator relation at the real B).

   | contract | clause | covered by |
   |---|---|---|
   | all six | pin_pre_kit (journal, ra, gp, tp, sp, chain, event count) | (b) pin_pre_kit_init, at own = [] and k = 0; the joint instance with a frame in own is (c) |
   | CK1 | a0 = 0 iff a1 <> 0, at the harness's two cases (accepted: rc 0, want a row; refused: rc -1, want 0) | (a) pin_sat_regs |
   | CR1 | a0 = a1 | (a) pin_sat_regs (a word equals itself) |
   | CA1 | c <> 0, c mod 8 = 0, 0 <= cid, the two frame bounds at the real count slot (frame + 0x20 of a 64-byte class-0 frame) | (a) pin_sat_frame_cells |
   | CA1 | off the stack window | (a) the arithmetic, at an 8-aligned cell far below the window: pin_sat_outcell (stated at the harness's out-cell, the same arithmetic); that the real count slot lies there (the side stack is below alloc_ceiling <= ly_stk_lo) is (c) pin_cat_site |
   | CA1 | In (cid, pos) own, afobj | (c) pin_cat_site (needs the walk's frame) |
   | CT1 / CP1 | pin_cat_ok: the bytes (22 pointers at the rows, 11 tokens and NULs), bounds, amem_range, alignment | (a) pin_sat_cat |
   | CT1 / CP1 | pin_cat_ok and pin_ro_str: range_addressable | (a) pin_sat_shadow_real: each clause's (address, length) IS a measured asan_globals descriptor, and the real shadow the start-up writes for that descriptor makes it addressable |
   | CT1 / CP1 | pin_cat_ok and pin_ro_str: shadow_hull_vis and the NUL-word tail | (a) only as consistency: pin_sat_cat / pin_sat_colon at a reader that marks every byte readable show these clauses do not contradict the others. At the real B they need the readable shadow words and tail bytes listed below: (c), P5, through pin_ro_law |
   | CT1 / CP1 | pin_cat_off_stack | (a) pin_sat_cat_off_stack |
   | CT1 / CP1 | arodata_okP, jointly with pin_cat_ok | (c): LIB1.4 is a premise of the top claim; jointly with the real bytes it is P5's (AD2o at TfibB) |
   | CT1 | the probe bytes at sa, their bounds, shadow, amem_range, off-stack | (a) pin_sat_probe |
   | CP1 | pin_spec_str (the string, its NUL, its tail, amem_range, off-stack) | (a) pin_sat_spec_str |
   | CP1 | the string is inside one heap block (b, m): the arithmetic | (a) pin_sat_spec_str; that (b, m) is in ablocks is (c) pin_parse_site |
   | CP1 | the ':' set string (bytes, bounds, amem_range) | (a) pin_sat_colon |
   | CP1 | the ':' set string off the stack window | (a) pin_sat_colon_off_stack |
   | CP1 | the two out-cells: alignment, no overlap, off the window, off the string, inside the class-1 frame at its real offsets (+0x20, +0x40 of 128 bytes) | (a) pin_sat_outcell, pin_sat_frame_cells |
   | CP1 | the out-cells' In own and afobj | (c) pin_parse_site |
   | CP1, and the harness walk's hypothesis | pin_ro_law (F-RO-LAW): at every state of the allocator relation whose read-only bytes read as the image, pin_cat_ok and pin_ro_str hold | (c) P5, ONCE, at tfibsegs / TfibB: the bytes from the image, the shadow from the start-up shadow cells listed below. Its parts that need no state are (a): pin_sat_cat and pin_sat_colon (the byte, bound and range clauses at the measured numbers), pin_sat_shadow_real (the shadow clauses at the real descriptors), pin_sat_img_ranges (the objects lie in image A's loaded segments, which arodata_okP reaches) |
   | CP1 | one class-0 frame free | (a) pin_sat_fs0 at the harness's call (frames Sc = [(1, pos)]); that frames Sc is that list is (c) pin_parse_site |
   | strncmp | amem_range x (len + 8), amem_range y (len + 8) at pin's two arguments | (a) pin_sat_ncmp_range |
   | LIB1 | mo_ok at the real meter | (a) pin_sat_meter |
   | LIB1 | the whole pre at the driver's entry state | (c) P5's AD2o.ASAN_T_closed, as the fuzz_qdisc lane recorded for its own close |
   | CT1 / CP1 (results) | the result functions are not degenerate | (a) pin_sat_res |

   WHAT pin_ro_law NEEDS AT THE REAL B (P5 discharges it at TfibB from the allocator relation's zero-shadow
   ranges and const cells, which the generated start-up tables carry). Computed from image A's asan_globals
   descriptors (beg, size; each string's slot is 32 bytes, or 64 for the display strings) with SHADOW_OFF
   0x7fff8000. Three kinds of fact, per object:
   (i) range_addressable: the object's own shadow cells, 0 for a whole granule and size mod 8 for the last.
   (ii) shadow_hull_vis: every cell of the 8-byte shadow words that hold those cells must be READABLE (any
       value): these words also hold the slot's 0xf9 redzone cells and the neighbouring object's cells.
   (iii) pin_str_tail: the bytes after the NUL up to the end of its 8-byte word must be readable. They are
       the global's redzone padding in .rodata: when B's static owned ranges do not cover them,
       arodata_okP gives them; when they do, they must come from B's const cells.
   object (beg/size)       hull word (cells)                         own cells       tail bytes
   ':'    0x20d80/2        0x7fffc1b0..b7 = 2 f9 f9 f9 ? ? ? ?         b0=2            0x20d82..0x20d87
   s1608  0x20dc0/6        0x7fffc1b8..bf = 6 f9 f9 f9 0 0 7 f9        b8=6            0x20dc6..0x20dc7
   s0808  0x20e20/6        0x7fffc1c0..c7 = f9 f9 f9 f9 6 f9 f9 f9     c4=6            0x20e26..0x20e27
   s4000s 0x20e80/7        0x7fffc1d0..d7 = 7 f9 f9 f9 0 0 0 5         d0=7            0x20e87
   s4000s-0832 0x20ee0/12  0x7fffc1d8..df = f9 f9 f9 f9 0 4 f9 f9      dc=0, dd=4      0x20eec..0x20eef
   s0816  0x20f40/6        0x7fffc1e8..ef = 6 f9 f9 f9 0 0 7 f9        e8=6            0x20f46..0x20f47
   s2416  0x20fa0/6        0x7fffc1f0..f7 = f9 f9 f9 f9 6 f9 f9 f9     f4=6            0x20fa6..0x20fa7
   s4000d 0x21000/7        0x7fffc200..07 = 7 f9 f9 f9 0 0 0 f9        200=7           0x21007
   s4000m 0x21060/7        0x7fffc208..0f = f9 f9 f9 f9 7 f9 f9 f9     20c=7           0x21067
   fr4000 0x210c0/7        0x7fffc218..1f = 7 f9 f9 f9 0 0 7 f9        218=7           0x210c7
   fr0040 0x21120/7        0x7fffc220..27 = f9 f9 f9 f9 7 f9 f9 f9     224=7           0x21127
   fr2020 0x21180/7        0x7fffc230..37 = 7 f9 f9 f9 0 0 0 f9        230=7           0x21187
   fuzz_catalogue 0x97ee0/3256: own cells 0x8000afdc .. 0x8000b172 = 0 (407 cells); hull words
                           0x8000afd8 .. 0x8000b177 (the first four and the last five cells are the
                           neighbours' or the redzone's); no tail (the table is read by 8-byte loads only).
   In the ':' word, cells 0x7fffc1b4..b7 are the shadow of 0x20da0..0x20dbf, which no descriptor names (the
   module-name string); the hull asks only that they be readable. The other cells of each word are the
   slot's redzone (f9) and the neighbouring display string's own cells (0, size mod 8). The display strings
   themselves are not read by any pin function: the code only passes and compares their pointers.

   THE NUMBERS. Every number below was read from the pinned image A (fuzz_pin.asan, sha256
   3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16) with pyelftools 0.33: the table
   fuzz_catalogue at 0x97ee0 (3256 bytes, 11 rows of 0x128), its 11 token pointers and 11 display
   pointers, the ':' set string at 0x20d80, the (beg, size) pairs of the 24 asan_globals descriptors at
   0x9d910, and the loaded segments [0x10000, 0x2f31c) (r--) and [0x97ac8, 0x9a000) (the relro part of
   rw-). In image B the 22 string pointers and the ':' string are the SAME and the table is at 0x98000;
   this file is image A's witness, so it carries image A's table address.

   HOW THE BYTE CLAUSES ARE CHECKED. W_M is a memory that holds exactly the measured bytes at the measured
   addresses; W_val_ok / W_garr_ok are boolean checks of one object each against W_M, and val_mem_of_ok /
   garr8_of_ok turn one successful check into the clause, so each object costs one computation. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YI00 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.

(* ------------------------------- image A's measured numbers ------------------------------- *)
Definition PIN_CAT : Z := 0x97ee0.
Definition PIN_TOKP : list Z :=
[0x20dc0; 0x20e20; 0x20e80; 0x20ee0; 0x20f40; 0x20fa0; 0x21000; 0x21060; 0x210c0; 0x21120; 0x21180].
Definition PIN_DISPP : list Z :=
[0x20de0; 0x20e40; 0x20ea0; 0x20f00; 0x20f60; 0x20fc0; 0x21020; 0x21080; 0x210e0; 0x21140; 0x211a0].
Definition PIN_TP (i : nat) : Z := nth i PIN_TOKP 0.
Definition PIN_DP (i : nat) : Z := nth i PIN_DISPP 0.
Definition PIN_COLONP : Z := 0x20d80.
(* the (beg, size) pairs of the 24 asan_globals descriptors of image A (asan_globals 0x9d910, 64 bytes each) *)
Definition PIN_GLOBS : list (Z * Z) :=
[(0x20d80, 2); (0x20dc0, 6); (0x20de0, 23); (0x20e20, 6); (0x20e40, 22); (0x20e80, 7); (0x20ea0, 29);
 (0x20ee0, 12); (0x20f00, 29); (0x20f40, 6); (0x20f60, 23); (0x20fa0, 6); (0x20fc0, 24); (0x21000, 7);
 (0x21020, 24); (0x21060, 7); (0x21080, 24); (0x210c0, 7); (0x210e0, 23); (0x21120, 7); (0x21140, 23);
 (0x21180, 7); (0x211a0, 24); (0x97ee0, 3256)].
(* image A's loaded segments that hold the strings (r--) and the table (the relro part of rw-) *)
Definition PIN_SEG_RO_LO : Z := 0x10000.
Definition PIN_SEG_RO_HI : Z := 0x2f31c.
Definition PIN_SEG_RELRO_LO : Z := 0x97ac8.
Definition PIN_SEG_RELRO_HI : Z := 0x9a000.
(* a heap block the harness could hand reac_box_pin_parse, and a spec string in it: "s0808:x" *)
Definition PIN_SA : Z := 0x500000.
Definition PIN_SPEC : list byte := map (fun z => Z_to_bv 8 z) [115; 48; 56; 48; 56; 58; 120].
(* the two out-cells of a live call, in a class-1 frame at PIN_F1 (+0x20, +0x40: 0x808bc / 0x808c0) *)
Definition PIN_F1 : Z := 0x600000.
Definition PIN_MO : Z := PIN_F1 + 0x20.
Definition PIN_LB : Z := PIN_F1 + 0x40.

Ltac wnum := vm_compute; first [reflexivity | discriminate].

(* ------------------------------- the witness memory and the checks ------------------------------- *)
Definition le8z (v : Z) : list Z := map (fun k => YO0f.le_byte v 8 k) (seq 0 8).
Definition W_cells : list (Z * list Z) := Eval vm_compute in
flat_map (fun i => [(row_addr PIN_CAT i, le8z (PIN_TP i)); (row_addr PIN_CAT i + 8, le8z (PIN_DP i))])
 (seq 0 CAT_N)
++ map (fun i => (PIN_TP i, pin_zbytes (tok_bytes i) ++ [0])) (seq 0 CAT_N)
++ [(PIN_COLONP, [COLON; 0]); (PIN_SA, pin_zbytes PIN_SPEC ++ [0])].
Fixpoint W_look (a : Z) (cs : list (Z * list Z)) : option Z :=
match cs with
| [] => None
| (b, l) :: t => if (b <=? a) && (a <? b + Z.of_nat (length l))
                 then nth_error l (Z.to_nat (a - b)) else W_look a t
end.
Definition W_M : word -> option byte :=
fun w => option_map (Z_to_bv 8) (W_look (bv_unsigned w) W_cells).
(* the reader of the consistency witness: every byte present and marked usable *)
Definition W_RD : reader := fun _ => Some 0.

Lemma bu64 : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof.
intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_small. exact Hx.
Qed.

Lemma W_M_look : forall segs a v, 0 <= a < 2 ^ 64 -> W_look a W_cells = Some v ->
mbyte segs W_M a = Some (Z_to_bv 8 v).
Proof. intros segs a v Ha H. unfold mbyte, W_M. rewrite (bu64 a Ha), H. reflexivity. Qed.

Definition W_val_ok (a : Z) (n : nat) (v : Z) : bool :=
forallb (fun k => match W_look (a + Z.of_nat k) W_cells with
                  | Some x => x =? YO0f.le_byte v n k | None => false end) (seq 0 n).
Lemma val_mem_of_ok : forall segs a n v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> W_val_ok a n v = true ->
val_mem segs W_M a n v.
Proof.
intros segs a n v Ha Hn H k Hk. unfold W_val_ok in H. rewrite forallb_forall in H.
assert (Hin : In k (seq 0 n)) by (apply in_seq; lia).
specialize (H k Hin). destruct (W_look (a + Z.of_nat k) W_cells) as [x|] eqn:E; [|discriminate].
apply Z.eqb_eq in H. subst x. apply W_M_look; [lia | exact E].
Qed.

Definition W_garr_ok (b : Z) (l : list Z) : bool :=
forallb (fun j => W_val_ok (b + Z.of_nat j) 1 (nth j l 0)) (seq 0 (length l)) &&
forallb (fun z => (0 <=? z) && (z <? 256)) l.
Lemma garr8_of_ok : forall segs b l, 0 <= b -> b + Z.of_nat (length l) <= 2 ^ 64 -> W_garr_ok b l = true ->
garr8 segs W_M b l.
Proof.
intros segs b l Hb Hl H j Hj. unfold W_garr_ok in H. apply andb_prop in H as [H1 H2].
rewrite forallb_forall in H1, H2. split.
- apply val_mem_of_ok; [lia | lia |]. apply H1. apply in_seq. lia.
- specialize (H2 (nth j l 0) (nth_In l 0 Hj)). apply andb_prop in H2 as [H3 H4].
  apply Z.leb_le in H3. apply Z.ltb_lt in H4. lia.
Qed.

Lemma W_RD_ra : forall a len, range_addressable W_RD SHADOW_OFF a len.
Proof. intros a len x Hx. exists 0. split; [reflexivity | left; reflexivity]. Qed.
Lemma W_RD_hull : forall a len, shadow_hull_vis W_RD a len.
Proof. intros a len s Hs. unfold W_RD. discriminate. Qed.
Lemma W_RD_tail : forall x, pin_str_tail W_RD x.
Proof. intros x a Ha. unfold W_RD. discriminate. Qed.

(* ------------------------------- the real shadow bytes of pin's globals -------------------------------
   The start-up marks a global of sz bytes at beg: the whole granules get 0 and the last one gets sz mod 8.
   pin_real_rd is that reader for one global. *)
Definition pin_gsh (beg sz g : Z) : Z := if sz - (g - beg) >=? 8 then 0 else sz - (g - beg).
Definition pin_real_rd (beg sz : Z) : reader :=
fun a => if a <? SHADOW_OFF then Some 0 else Some (pin_gsh beg sz ((a - SHADOW_OFF) * 8)).

Lemma pin_real_ra : forall beg sz, 0 <= beg -> beg mod 8 = 0 -> 0 < sz ->
range_addressable (pin_real_rd beg sz) SHADOW_OFF beg sz.
Proof.
intros beg sz Hb0 Hb Hsz x Hx.
assert (Hx0 : 0 <= x) by lia.
assert (Hdiv : 0 <= x / 8) by (apply Z.div_pos; lia).
unfold pin_real_rd, shadow_of_addr.
rewrite (proj2 (Z.ltb_ge (SHADOW_OFF + x / 8) SHADOW_OFF)) by lia.
eexists. split; [reflexivity|].
replace (SHADOW_OFF + x / 8 - SHADOW_OFF) with (x / 8) by lia.
assert (Hg : x / 8 * 8 = x - x mod 8) by (pose proof (Z.div_mod x 8 ltac:(lia)); lia).
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm.
unfold pin_gsh. rewrite Hg.
destruct (Z.geb_spec (sz - (x - x mod 8 - beg)) 8) as [Hge|Hlt]; [left; reflexivity|].
right. split; lia.
Qed.

Definition glob_is (beg sz : Z) : bool := existsb (fun r => (fst r =? beg) && (snd r =? sz)) PIN_GLOBS.
Lemma glob_is_In : forall beg sz, glob_is beg sz = true -> In (beg, sz) PIN_GLOBS.
Proof.
intros beg sz H. unfold glob_is in H. apply existsb_exists in H as ([b s] & Hin & H).
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. cbn in H1, H2. subst. exact Hin.
Qed.

(* Each clause instance of F-CAT / F-SET is a measured descriptor, and the real shadow of that descriptor
   makes the clause's range addressable: a wrong length in a clause, or a mismeasured pointer, fails here. *)
Lemma pin_sat_shadow_real :
In (PIN_CAT, CAT_BYTES) PIN_GLOBS /\
range_addressable (pin_real_rd PIN_CAT CAT_BYTES) SHADOW_OFF PIN_CAT CAT_BYTES /\
Z.of_nat (length pin_colon_bytes) + 1 = 2 /\ In (PIN_COLONP, 2) PIN_GLOBS /\
range_addressable (pin_real_rd PIN_COLONP 2) SHADOW_OFF PIN_COLONP 2 /\
(forall i, (i < CAT_N)%nat ->
 In (PIN_TP i, pin_tokn i + 1) PIN_GLOBS /\
 range_addressable (pin_real_rd (PIN_TP i) (pin_tokn i + 1)) SHADOW_OFF (PIN_TP i) (pin_tokn i + 1)).
Proof.
split; [apply glob_is_In; wnum|].
split; [apply pin_real_ra; wnum|].
split; [reflexivity|].
split; [apply glob_is_In; wnum|].
split; [apply pin_real_ra; wnum|].
intros i Hi.
assert (H : glob_is (PIN_TP i) (pin_tokn i + 1) = true /\ 0 <= PIN_TP i /\ PIN_TP i mod 8 = 0 /\ 0 < pin_tokn i + 1).
{ do 11 (destruct i as [|i]; [repeat split; wnum|]). exfalso; unfold CAT_N in Hi; lia. }
destruct H as (H1 & H2 & H3 & H4). split; [exact (glob_is_In _ _ H1) | exact (pin_real_ra _ _ H2 H3 H4)].
Qed.

(* ------------------------------- the pin-specific premises, at pin's numbers ------------------------------- *)
Lemma pin_sat_cat : forall segs, pin_cat_ok segs W_M W_RD PIN_CAT PIN_TP PIN_DP.
Proof.
intros segs. unfold pin_cat_ok.
split; [wnum|]. split; [wnum|]. split; [wnum|]. split; [left; wnum|].
split; [apply W_RD_ra|].
intros i Hi.
assert (H : W_val_ok (row_addr PIN_CAT i) 8 (PIN_TP i) = true /\ W_val_ok (row_addr PIN_CAT i + 8) 8 (PIN_DP i) = true /\
 W_garr_ok (PIN_TP i) (pin_zbytes (tok_bytes i) ++ [0]) = true /\
 0 <= PIN_TP i /\ 0 <= PIN_DP i /\ PIN_TP i < 2 ^ 64 /\ PIN_DP i < 2 ^ 64 /\
 row_addr PIN_CAT i + 16 <= 2 ^ 64 /\ 0 <= row_addr PIN_CAT i /\
 0 < PIN_TP i /\ PIN_TP i + pin_tokn i + 1 <= 2 ^ 63 /\ pin_tokn i + 1 < 2 ^ 32 /\
 PIN_TP i + pin_tokn i + 8 <= kLowMemEnd - 1).
{ do 11 (destruct i as [|i]; [repeat split; wnum|]). exfalso; unfold CAT_N in Hi; lia. }
destruct H as (V1 & V2 & G & T0 & D0 & T1 & D1 & R16 & R0 & T2 & T3 & T4 & T5).
assert (Hlen : Z.of_nat (length (pin_zbytes (tok_bytes i) ++ [0])) = pin_tokn i + 1).
{ unfold pin_zbytes, pin_tokn. rewrite length_app, length_map. cbn [length]. lia. }
split; [apply val_mem_of_ok; [lia | cbn; lia | exact V1]|].
split; [apply val_mem_of_ok; [lia | cbn; lia | exact V2]|].
split; [lia|]. split; [lia|].
unfold pin_ro_str. fold (pin_tokn i).
split; [lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
split; [apply garr8_of_ok; [lia | rewrite Hlen; lia | exact G]|].
split; [apply W_RD_ra|]. split; [apply W_RD_hull | apply W_RD_tail].
Qed.

Lemma pin_sat_colon : forall segs, pin_ro_str segs W_M W_RD PIN_COLONP pin_colon_bytes.
Proof.
intros segs. unfold pin_ro_str.
split; [wnum|]. split; [wnum|]. split; [wnum|]. split; [left; wnum|].
split; [apply garr8_of_ok; [wnum | wnum | wnum]|].
split; [apply W_RD_ra|]. split; [apply W_RD_hull | apply W_RD_tail].
Qed.

Lemma pin_sat_colon_off_stack : forall (regs : bvmap 5 word) STK_f,
0 <= STK_f -> 0x1000000 <= spZ regs - STK_f ->
forall x, PIN_COLONP <= x <= PIN_COLONP + 1 -> ~ (spZ regs - STK_f <= x < spZ regs).
Proof. intros regs STK_f H0 Hsp x Hx. unfold PIN_COLONP in Hx. lia. Qed.

Lemma PIN_SPEC_len : Z.of_nat (length PIN_SPEC) = 7.
Proof. reflexivity. Qed.

(* CP1.2 at a spec string in a heap block (PIN_SA, 8): the string clauses, and the block arithmetic. *)
Lemma pin_sat_spec_str : forall segs (regs : bvmap 5 word),
0x1000000 <= spZ regs - T_parse_STK ->
pin_spec_str segs W_M W_RD regs T_parse_STK PIN_SA PIN_SPEC /\
(exists b m, b <= PIN_SA /\ PIN_SA + Z.of_nat (length PIN_SPEC) + 1 <= b + req_size m).
Proof.
intros segs regs Hsp. split.
2:{ exists PIN_SA, 8. unfold req_size. cbn. lia. }
unfold pin_spec_str. rewrite PIN_SPEC_len.
split.
{ intros H. apply (in_map (fun b : byte => bv_unsigned b)) in H.
  assert (E : map (fun b : byte => bv_unsigned b) PIN_SPEC = [115; 48; 56; 48; 56; 58; 120]) by reflexivity.
  rewrite E in H. cbn [In] in H. assert (E0 : bv_unsigned NUL = 0) by reflexivity. rewrite E0 in H. lia. }
split; [wnum|]. split; [wnum|]. split; [wnum|].
split; [apply garr8_of_ok; [wnum | wnum | wnum]|].
split; [apply W_RD_ra|]. split; [apply W_RD_hull|]. split; [apply W_RD_tail|].
split; [left; wnum|].
intros x Hx. unfold PIN_SA in Hx. lia.
Qed.

Lemma pin_sat_cat_off_stack : forall (regs : bvmap 5 word) STK_f,
0 <= STK_f -> 0x1000000 <= spZ regs - STK_f -> pin_cat_off_stack PIN_CAT PIN_TP regs STK_f.
Proof.
intros regs STK_f H0 Hsp. unfold pin_cat_off_stack. split.
- intros x Hx. unfold PIN_CAT, CAT_BYTES in Hx. lia.
- intros i x Hi Hx.
  assert (HT : PIN_TP i + pin_tokn i <= 0x211c0 /\ 0 <= PIN_TP i).
  { do 11 (destruct i as [|i]; [split; wnum|]). exfalso; unfold CAT_N in Hi; lia. }
  lia.
Qed.

(* CA1's and CP1's cell geometry at the real offsets: the count slot is frame + 0x20 of a 64-byte class-0
   frame (0x80c74 `addi s6,s11,0x20`), the out-cells are frame + 0x20 and frame + 0x40 of the harness's
   128-byte class-1 frame (0x808bc / 0x808c0); frames are 32-aligned (al_frames, lib/Reusable/YG0d.v:460). *)
Lemma pin_sat_frame_cells : forall F0 F1, 0 < F0 -> F0 mod 32 = 0 -> 0 < F1 -> F1 mod 32 = 0 ->
F0 + 0x20 <> 0 /\ (F0 + 0x20) mod 8 = 0 /\ F0 mod 8 = 0 /\ F0 <= F0 + 0x20 /\ F0 + 0x20 + 8 <= F0 + fs_frame_bytes 0 /\
(F1 + 0x20) mod 8 = 0 /\ (F1 + 0x40) mod 8 = 0 /\ F1 mod 8 = 0 /\
F1 <= F1 + 0x20 /\ F1 + 0x20 + 8 <= F1 + fs_frame_bytes 1 /\
F1 <= F1 + 0x40 /\ F1 + 0x40 + 8 <= F1 + fs_frame_bytes 1 /\
(F1 + 0x20 + 8 <= F1 + 0x40 \/ F1 + 0x40 + 8 <= F1 + 0x20).
Proof.
intros F0 F1 H0 H1 H2 H3.
change (fs_frame_bytes 0) with 64. change (fs_frame_bytes 1) with 128.
repeat split; lia.
Qed.

(* The out-cells at concrete values: not 0, 8-aligned, no overlap, off the window, off the string. *)
Lemma pin_sat_outcell : forall (regs : bvmap 5 word) STK_f,
0 <= STK_f -> 0x1000000 <= spZ regs - STK_f ->
PIN_MO <> 0 /\ PIN_MO mod 8 = 0 /\ PIN_LB mod 8 = 0 /\ (PIN_MO + 8 <= PIN_LB \/ PIN_LB + 8 <= PIN_MO) /\
(forall x, pin_out_cell PIN_MO PIN_LB x -> ~ (spZ regs - STK_f <= x < spZ regs)) /\
(forall x, pin_out_cell PIN_MO PIN_LB x -> ~ (PIN_SA <= x <= PIN_SA + Z.of_nat (length PIN_SPEC))) /\
(spZ regs <= PIN_MO \/ PIN_MO + 8 <= spZ regs - STK_f) /\
pin_parse_live PIN_SA PIN_MO PIN_LB = true.
Proof.
intros regs STK_f H0 Hsp. pose proof PIN_SPEC_len as HL.
unfold pin_out_cell, PIN_MO, PIN_LB, PIN_F1, PIN_SA in *.
split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [left; lia|].
split; [intros x Hx; lia|]. split; [intros x Hx; lia|]. split; [right; lia|].
reflexivity.
Qed.

(* The results are not degenerate: at the witness string the parse accepts row 1 and names the label just
   past the ':'; without label text it names DP 1; at a probe that is no token the row lookup is 0 and the
   parse refuses; a NULL out pointer refuses. *)
Lemma pin_sat_res :
row_ptr PIN_CAT (tok_bytes 1) = row_addr PIN_CAT 1 /\
row_ptr PIN_CAT (map (fun z => Z_to_bv 8 z) [122; 122]) = 0 /\
pin_parse_res PIN_CAT PIN_DP PIN_SA PIN_MO PIN_LB PIN_SPEC = Some (row_addr PIN_CAT 1, PIN_SA + 6) /\
pin_parse_res PIN_CAT PIN_DP PIN_SA PIN_MO PIN_LB (map (fun z => Z_to_bv 8 z) [115; 48; 56; 48; 56])
  = Some (row_addr PIN_CAT 1, PIN_DP 1) /\
pin_parse_res PIN_CAT PIN_DP PIN_SA 0 PIN_LB PIN_SPEC = None /\
parse_rc (pin_parse_res PIN_CAT PIN_DP PIN_SA PIN_MO PIN_LB PIN_SPEC) = 0 /\
parse_rc (pin_parse_res PIN_CAT PIN_DP PIN_SA PIN_MO PIN_LB (map (fun z => Z_to_bv 8 z) [122; 122])) = -1.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* CK1 / CR1 at the harness's two cases: accepted (rc 0, want the row) and refused (rc -1, want 0). *)
Lemma pin_sat_regs :
(w64 0 = w64 0 <-> w64 (row_addr PIN_CAT 1) <> w64 0) /\
(w64 (-1) = w64 0 <-> w64 0 <> w64 0) /\
w64 (row_addr PIN_CAT 1) = w64 (row_addr PIN_CAT 1).
Proof.
assert (Hne : w64 (row_addr PIN_CAT 1) <> w64 0).
{ intros H. apply (f_equal (@bv_unsigned 64)) in H. cbv in H. discriminate H. }
assert (Hm1 : w64 (-1) <> w64 0).
{ intros H. apply (f_equal (@bv_unsigned 64)) in H. cbv in H. discriminate H. }
split; [split; [intros _; exact Hne | intros _; reflexivity]|].
split; [split; [intros H; exfalso; exact (Hm1 H) | intros H; exfalso; exact (H eq_refl)] | reflexivity].
Qed.

(* LIB1's meter premise at the meter the close fixes. *)
Lemma pin_sat_meter : forall S x, mo_ok ameter_triv S x.
Proof. intros S x. exact I. Qed.

(* The arithmetic half of pin_ro_law's byte part: the table, each token with its NUL word and the ':' set
   with its NUL word lie inside image A's loaded segments (the relro part of rw- and r--). *)
Lemma pin_sat_img_ranges :
(forall x, PIN_CAT <= x < PIN_CAT + CAT_BYTES -> PIN_SEG_RELRO_LO <= x < PIN_SEG_RELRO_HI) /\
(forall i x, (i < CAT_N)%nat -> PIN_TP i <= x < pin_word_end (PIN_TP i + pin_tokn i) ->
 PIN_SEG_RO_LO <= x < PIN_SEG_RO_HI) /\
(forall x, PIN_COLONP <= x < pin_word_end (PIN_COLONP + 1) -> PIN_SEG_RO_LO <= x < PIN_SEG_RO_HI).
Proof.
split; [intros x Hx; unfold PIN_CAT, CAT_BYTES, PIN_SEG_RELRO_LO, PIN_SEG_RELRO_HI in *; lia|].
split.
- intros i x Hi Hx.
  assert (H : PIN_SEG_RO_LO <= PIN_TP i /\ pin_word_end (PIN_TP i + pin_tokn i) <= PIN_SEG_RO_HI).
  { do 11 (destruct i as [|i]; [split; wnum|]). exfalso; unfold CAT_N in Hi; lia. }
  lia.
- intros x Hx. assert (H : pin_word_end (PIN_COLONP + 1) = 0x20d88) by reflexivity. rewrite H in Hx.
  unfold PIN_COLONP, PIN_SEG_RO_LO, PIN_SEG_RO_HI in *. lia.
Qed.

(* the strncmp wrapper's two range premises at pin's two arguments: each token, and the spec string *)
Lemma pin_sat_ncmp_range :
(forall i, (i < CAT_N)%nat -> amem_range (PIN_TP i) (pin_tokn i + 8)) /\
amem_range PIN_SA (Z.of_nat (length PIN_SPEC) + 8).
Proof.
split; [|left; wnum].
intros i Hi. do 11 (destruct i as [|i]; [left; wnum|]). exfalso; unfold CAT_N in Hi; lia.
Qed.

(* CT1's probe: the n bytes the harness hands fuzz_catalogue_row are the first bytes of the spec string. *)
Lemma pin_sat_probe : forall segs (regs : bvmap 5 word),
0x1000000 <= spZ regs - T_row_STK ->
garr8 segs W_M PIN_SA (pin_zbytes (firstn 5 PIN_SPEC)) /\
range_addressable W_RD SHADOW_OFF PIN_SA (Z.of_nat (length (firstn 5 PIN_SPEC))) /\
shadow_hull_vis W_RD PIN_SA (Z.of_nat (length (firstn 5 PIN_SPEC))) /\
amem_range PIN_SA (Z.of_nat (length (firstn 5 PIN_SPEC))) /\
(forall x, PIN_SA <= x < PIN_SA + Z.of_nat (length (firstn 5 PIN_SPEC)) ->
 ~ (spZ regs - T_row_STK <= x < spZ regs)) /\
row_ptr PIN_CAT (firstn 5 PIN_SPEC) = row_addr PIN_CAT 1.
Proof.
intros segs regs Hsp.
assert (HL : Z.of_nat (length (firstn 5 PIN_SPEC)) = 5) by reflexivity.
split; [apply garr8_of_ok; [wnum | wnum | wnum]|].
split; [apply W_RD_ra|]. split; [apply W_RD_hull|].
split; [left; wnum|].
split; [intros x Hx; rewrite HL in Hx; unfold PIN_SA in Hx; lia|].
vm_compute; reflexivity.
Qed.

(* CP1.7 at the harness's call: its own class-1 frame is the only one in use, so a class-0 frame is free. *)
Lemma pin_sat_fs0 : forall pos, count_cid 0 [(1, pos)] < fs_frames 0.
Proof. intros pos. wnum. Qed.

(* ------------------------------- (b): the kit premises at any entry state ------------------------------- *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Lemma pin_pre_kit_init : forall STK FP ly S W regs mem md ch STK_f EV,
afn_pre segs B STK ly S W regs mem md ch ->
0 <= STK_f <= STK -> st_nev S + EV <= EV_MAX ->
pin_pre_kit segs B STK (spZ regs) FP ly S W mem md [] ly S W mem md 0 regs ch STK_f EV.
Proof.
intros STK FP ly S W regs mem md ch STK_f EV HPRE HSTK HEV.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & HSTK0 & _).
unfold pin_pre_kit.
split; [exact (ajournal_init segs B STK FP ly S W regs mem md ch HPRE)|].
split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp|]. split; [exact Htp|].
split; [exact Hch|]. split; [exact Hal16|].
split; [lia|]. split; [lia|]. lia.
Qed.
End c.
End b.

Print Assumptions pin_sat_cat.
Print Assumptions pin_sat_colon.
Print Assumptions pin_sat_colon_off_stack.
Print Assumptions pin_sat_spec_str.
Print Assumptions pin_sat_cat_off_stack.
Print Assumptions pin_sat_frame_cells.
Print Assumptions pin_sat_outcell.
Print Assumptions pin_sat_res.
Print Assumptions pin_sat_regs.
Print Assumptions pin_sat_meter.
Print Assumptions pin_sat_img_ranges.
Print Assumptions pin_sat_ncmp_range.
Print Assumptions pin_sat_probe.
Print Assumptions pin_sat_shadow_real.
Print Assumptions pin_sat_fs0.
Print Assumptions pin_pre_kit_init.
