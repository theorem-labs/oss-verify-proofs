(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the copy segment of the image-B walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput (llvm_b_copy_stmt of LLVMFuzzerTestOneInput_segs.v), with proof steps adapted from proofs/libreac/fuzz_boxreg/lib/A/Prog/ReadName.v (a working branch: the run / branch / call pattern); ew_Eimg_Ereg_nat and img_env_atomP copied from this unit's lib/A/Prog/YC1g.v / YC1h.v at image B's PAImg; the malloc call step and eb_ch / eb_chain_at / eb_trace_at / eb_rdword_of_bytes / eb_rdword_of_val_mem copied from lib/B/Prog/LLVMFuzzerTestOneInput_segB.v (a working branch 84be2173fcc); the two leaf calls in the shape of lib/B/Prog/LLVMFuzzerTestOneInput_leafb.v's dec_leafb_inspect; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segC.v, with its module paths and module names changed; 2590 of its 2760 lines of code are new or changed and 2192 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_copy: the image-A walk's segment llvm_a_copy, +0x234 .. +0x3bc of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput: `Theorem llvm_a_copy_ok : llvm_a_copy_stmt` (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), proved
   in the Pa engine.

   The code (lib/A/Prog/DecodeList.v:169-267, offset = 4 * (line - 28)): the NULL check of the payload copy (+0x23c,
   refuted by 4096 <= res), __asan_memcpy (+0x250), the two reac_frame_is_reac calls (+0x25c on the non-empty path,
   +0x2b0 on the empty one) with the two shadow-checked header reads at res + 12 and res + 13, the abort edge at
   +0x2b8, reac_frame_clean_len (+0x2c0) and the abort edges of the clean-length algebra (+0x2cc, +0x2d4, +0x2fc,
   +0x340), the two four-byte shadow checks on the mode's nch and ns fields (+0x344, +0x354), the geometry spills to
   s1, and malloc #2 (+0x3bc). Every branch into +0xa4c..+0xb60 is refuted, never stepped (a Theorem Labs lane 2026-10-29 02:13Z:
   every __asan_report_* returns, so a report call is not terminal and the statement asks the block to be unreachable).

   The proof is cut at the segment's calls, one Section per part (the Sections repeat the statement file's Variables):
   1. the state the segment carries between its calls (cp_core, cp_at, cp_st), the lemma that carries it across a step
      that writes only the copy and the stack below s1 + 96 (cp_core_kept), the mode's geometry from the statement's
      pointer and shadow rows (cp_mode_table, cp_mode_facts; the one shadow-zero read is cp_tbl_sh0), the image's two div-36 words (cp_rom_div), the arithmetic of the
      listing's two divisibility tests (dec_div36_64, dec_div36_32), and the statements of the five calls;
   2. __asan_memcpy (res, p + u, len) by the statement's aintrin_realizes (YC85.v aj_intrin_atS): cp_call_memcpy;
   3. reac_frame_is_reac and reac_frame_clean_len by their dec_leaf_at premises, through the shared leaf bridge
      lib/A/Prog/LLVMFuzzerTestOneInput_leafb.v (dec_leafb_journal): cp_call_isreac, cp_call_clean;
   4. malloc #2 by amalloc04_rule (YC85.v amalloc04_sub), the trace from dec_llvmf_utraces, ending at llvm_a_st_3c0
      (after lib/A/Prog/LLVMFuzzerTestOneInput_seg_early.v e_call): cp_call_malloc2;
   5. the symbolic runs between the calls, in the idiom of libreac/fuzz_boxreg's lib/A/Prog/ReadName.v at
      a working branch 1d92330b7ad (an sstate naming the regions and facts, paj_run /
      paj_branch, awr_ok, the shadow side conditions): cp_stage_a (+0x234), cp_stage_b (+0x254), cp_stage_c (+0x260),
      cp_stage_d (+0x2b4), cp_stage_e (+0x2c4); and the composition llvm_a_copy_ok. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0s YI00 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
PaRun PaShadow DecodeSyms DecodeList DecodePa.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
PaStep DecodePaLib DecodeImg DecodeCJ YC1g YC1h YC1i YC81 YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
DecodeAddr check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs
LLVMFuzzerTestOneInput_leafb.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Img0 AsanCells DecodeShape.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Mem Frame ExecF MState PropExec.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require
LeafCgKit reac_frame_is_reac_cg reac_frame_clean_len_cg reac_frame_is_reac_c reac_frame_clean_len_c AsanKA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* lib/Reusable/YM03.v:182-189 redefines lia / nia globally with context pruning and retries; this file uses the
   plain tactics (YM03.v:179-180 lf_lia_orig / lf_nia_orig), measured 28x faster (a Theorem Labs lane, 2026-10-29 06:41Z). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

Module YI16 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.
Module DMem := OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib.Mem.
Module DFrame := OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib.Frame.
Module DExecF := OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib.ExecF.
Module DMState := OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib.MState.
Module DCells := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.AsanCells.
Module DImg := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Img0.
Module LKit := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.LeafCgKit.
Module LIR := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_is_reac_cg.
Module LCL := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_clean_len_cg.
Module CIR := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_is_reac_c.
Module CCL := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_clean_len_c.
Module DKA := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.AsanKA.

(* ------------------------------------------------------------------ *)
(* The listing's two divisibility-by-36 tests (+0x2d8..+0x2fc, +0x308..+0x32c)  *)
(* ------------------------------------------------------------------ *)

(* The two magic multipliers are the inverses of 9 modulo 2 ^ 32 and modulo 2 ^ 64. *)
Lemma dec_inv9_32 : (9 * 954437177) mod 2 ^ 32 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_inv9_64 : (9 * 10248191152060862009) mod 2 ^ 64 = 1.
Proof. vm_compute. reflexivity. Qed.

(* The 64-bit test the listing runs at +0x2d8..+0x2fc on a value already known to be a multiple of 36:
   x * KM mod 2 ^ 64 is exactly 4 * (x / 36). *)
Lemma dec_div36_64 : forall x : Z,
  0 <= x < 2 ^ 26 -> x mod 36 = 0 ->
  (x * 10248191152060862009) mod 2 ^ 64 = 4 * (x / 36).
Proof.
  intros x Hx Hm.
  pose proof (Z.div_mod x 36 ltac:(lia)) as Hd.
  rewrite Hm, Z.add_0_r in Hd.
  clear Hm.
  set (q := x / 36) in *.
  clearbody q.
  subst x.
  change (2 ^ 26) with 67108864 in Hx.
  change (2 ^ 64) with 18446744073709551616.
  (* 36 * KM = 4 * (9 * KM) = 4 * (5 * 2 ^ 64 + 1). *)
  replace (36 * q * 10248191152060862009)
    with (4 * q + 20 * q * 18446744073709551616) by ring.
  rewrite Z.mod_add by lia.
  apply Z.mod_small; lia.
Qed.

(* dec36_chk f n checks f at 0, 1, ..., n - 1. *)
Fixpoint dec36_chk (f : Z -> bool) (n : nat) : bool :=
  match n with
  | O => true
  | S k => (f (Z.of_nat k) && dec36_chk f k)%bool
  end.

Lemma dec36_chk_ok : forall (f : Z -> bool) (n : nat),
  dec36_chk f n = true -> forall m, 0 <= m < Z.of_nat n -> f m = true.
Proof.
  intros f n; induction n as [|n IH]; intros H m Hm.
  - simpl in Hm. lia.
  - simpl in H. apply andb_true_iff in H as [H1 H2].
    rewrite Nat2Z.inj_succ in Hm.
    destruct (Z.eq_dec m (Z.of_nat n)) as [->|Hne]; [exact H1|].
    apply IH; [exact H2|lia].
Qed.

(* For the residue m = (len - 54) mod 36 and w = m * K32 mod 2 ^ 32:
   - w + 2 ^ 23 < 2 ^ 32, so adding 4 * q (q < 2 ^ 21) never wraps;
   - m = 0 gives w = 0;
   - m <> 0 gives w mod 4 <> 0, or w >= 4 * 119304648. *)
Definition dec36_okw (m w : Z) : bool :=
  ((w + 8388608 <? 4294967296) &&
   (if m =? 0 then w =? 0 else negb (w mod 4 =? 0) || (477218592 <=? w)))%bool.

Definition dec36_ok (m : Z) : bool := dec36_okw m ((m * 954437177) mod 4294967296).

Lemma dec36_ok_all : dec36_chk dec36_ok 36%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec36_ok_lt36 : forall m, 0 <= m < 36 -> dec36_ok m = true.
Proof.
  intros m Hm.
  apply (dec36_chk_ok dec36_ok 36%nat dec36_ok_all).
  exact Hm.
Qed.

(* The 32-bit test the listing runs at +0x308..+0x32c: the harness's `(len - 54) is a multiple of 36` as the
   compiler computes it.  v is the low 32 bits of len * K32 - 6; the machine then rotates v right by 2 and
   compares unsigned with 119304648. *)
Lemma dec_div36_32 : forall len v : Z,
  54 <= len < 2 ^ 26 ->
  v = (len * 954437177 - 6) mod 2 ^ 32 ->
  (((v mod 4 =? 0) && (v / 4 <? 119304648))%bool = ((len - 54) mod 36 =? 0)).
Proof.
  intros len v Hlen Hv.
  revert Hv.
  pose proof (Z.div_mod (len - 54) 36 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (len - 54) 36 ltac:(lia)) as Hm.
  set (q := (len - 54) / 36) in *.
  set (m := (len - 54) mod 36) in *.
  clearbody q m.
  assert (Hl : len = 54 + 36 * q + m) by lia.
  clear Hd.
  subst len.
  change (2 ^ 26) with 67108864 in Hlen.
  assert (Hq : 0 <= q <= 1864133) by lia.
  clear Hlen.
  intro Hv.
  change (2 ^ 32) with 4294967296 in Hv.
  (* 54 * K32 - 6 = 12 * 2 ^ 32 and 36 * K32 = 4 + 8 * 2 ^ 32, since 9 * K32 = 2 ^ 33 + 1. *)
  replace ((54 + 36 * q + m) * 954437177 - 6)
    with (4 * q + m * 954437177 + (12 + 8 * q) * 4294967296) in Hv by ring.
  rewrite Z.mod_add, <- Z.add_mod_idemp_r in Hv by lia.
  pose proof (Z.mod_pos_bound (m * 954437177) 4294967296 ltac:(lia)) as Hw0.
  pose proof (dec36_ok_lt36 m Hm) as Hok.
  unfold dec36_ok, dec36_okw in Hok.
  set (w := (m * 954437177) mod 4294967296) in *.
  clearbody w.
  apply andb_true_iff in Hok as [Hw Hc].
  apply Z.ltb_lt in Hw.
  revert Hc.
  rewrite Z.mod_small in Hv by lia.
  subst v.
  destruct (Z.eqb_spec m 0) as [Hm0|Hm0]; intro Hc; simpl in Hc.
  - (* m = 0: v = 4 * q and q < 119304648. *)
    apply Z.eqb_eq in Hc.
    subst w.
    rewrite Z.add_0_r, (Z.mul_comm 4 q), Z.mod_mul, Z.div_mul by lia.
    apply andb_true_iff; split; [reflexivity | apply Z.ltb_lt; lia].
  - (* m <> 0: v mod 4 = w mod 4 and v / 4 = w / 4 + q. *)
    rewrite (Z.add_comm (4 * q) w), (Z.mul_comm 4 q), Z.mod_add, Z.div_add by lia.
    apply orb_true_iff in Hc as [Hc|Hc].
    + apply negb_true_iff in Hc.
      rewrite Hc.
      reflexivity.
    + apply Z.leb_le in Hc.
      assert (119304648 <= w / 4) by (apply Z.div_le_lower_bound; lia).
      apply andb_false_iff; right.
      apply Z.ltb_ge.
      lia.
Qed.


Lemma cp_regs_ok_set : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> getr regs r = sv_denot E e -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e H He rr.
destruct (bv_eqb r 0) eqn:H0; [unfold sr_set; rewrite H0; apply H|].
destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact H0. exact He.
- rewrite sr_get_set_other by exact Hne. apply H.
Qed.

(* k is one of the three mode cells (In k [4; 5; 6]). *)
Ltac cp_in := cbn [In]; repeat (first [left; reflexivity | right]).

Section seg.
Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable asink_img_laws : list Segment -> asyms -> asink_syms -> Prop.
Variable ro_below_ofl : list Segment -> Z -> Z -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
(* The engine's projections of the image instance (DecodeImg.v PI_decode); they compute to decodesegs0 and
   decode_val, but the kit's lemmas are stated over them. *)
#[local] Notation SEGS := (@pa_segs _ decode_listing (@PI_decode _)).
#[local] Notation VAL := (@pa_val _ decode_listing (@PI_decode _)).

(* A one-byte constant cell of B (YG0f.v z1), read through AR's am_const. *)
Lemma cp_z1 : forall ly (rd : reader) a v, 0 <= v < 256 -> cell_holds B ly rd (z1 (ANum a) v) -> rd a = Some v.
Proof.
intros ly rd a v Hv Hc. unfold cell_holds in Hc. cbn [c_at c_val c_w z1 c1 aeval] in Hc.
pose proof (Hc 0%nat ltac:(lia)) as H0. cbv [Z.of_nat] in H0. rewrite Z.add_0_r in H0. rewrite H0. f_equal.
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite !Z.mod_small; [reflexivity | change (2 ^ 8) with 256; lia | ].
rewrite Z.mod_small; change (2 ^ 8) with 256; lia.
Qed.

(* A range inside one shadow granule is addressable when its granule's shadow byte lets it through. *)
Lemma cp_ra_of_shadow : forall (rd : reader) a n s,
  0 <= a -> 0 < n -> a mod 8 + n <= 8 ->
  rd (shadow_of_addr SHADOW_OFF a) = Some s -> (s = 0 \/ (a mod 8 + n <= s /\ s < 8)) ->
  range_addressable rd SHADOW_OFF a n.
Proof.
intros rd a n s Ha Hn Hfit Hs Hok x Hx. exists s.
pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
rewrite (shadow_of_addr_same_granule SHADOW_OFF a x) by lia. split; [exact Hs|].
destruct Hok as [-> | [H1 H2]]; [left; reflexivity | right].
assert (Hxm : x mod 8 = x - 8 * (a / 8)).
{ transitivity ((x - 8 * (a / 8) + (a / 8) * 8) mod 8); [f_equal; lia|].
  rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
lia.
Qed.

(* The table each mode cell points at: the image's own word in decode_obj 4 / 5 / 6 (no address is written by hand;
   vm_compute reads it from the image, as lib/A/Prog/LLVMFuzzerTestOneInput_seg_early.v e_tbl does). *)
Definition cp_m_rom (a : Z) : option Z :=
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom decodesegs0 (Z_to_bv 64 a)).
Definition cp_m_tbl (k : nat) : Z := match rdword cp_m_rom (decode_obj k) with Some v => v | None => 0 end.
(* Replace cp_m_tbl k by its value, through an equation closed by vm_compute (a `change` would make the kernel
   re-run the image lookup with its lazy machine). *)
(* Each table's address, computed once (one image lookup per table: a vm_compute of cp_m_tbl reads the image). *)
Definition cp_T4 : Z := Eval vm_compute in cp_m_tbl 4.
Definition cp_T5 : Z := Eval vm_compute in cp_m_tbl 5.
Definition cp_T6 : Z := Eval vm_compute in cp_m_tbl 6.
Lemma cp_m_tbl_4 : cp_m_tbl 4 = cp_T4. Proof. vm_compute. reflexivity. Qed.
Lemma cp_m_tbl_5 : cp_m_tbl 5 = cp_T5. Proof. vm_compute. reflexivity. Qed.
Lemma cp_m_tbl_6 : cp_m_tbl 6 = cp_T6. Proof. vm_compute. reflexivity. Qed.
Ltac cp_m_tbl_val := rewrite ?cp_m_tbl_4, ?cp_m_tbl_5, ?cp_m_tbl_6; unfold cp_T4, cp_T5, cp_T6.

(* Close the goal with the hypothesis that IS it, syntactically (assumption would try every row of dec_crt_cells up
   to conversion, unfolding decode_obj). *)
Ltac cp_hyp := lazymatch goal with |- ?G => lazymatch goal with H : G |- _ => exact H end end.

(* The pointer rows of dec_crt_cells B (check_round_trip_cg.v): mode cell k holds the table's address, found by its
   statement, never by its position. *)
Lemma cp_m_ptr : dec_crt_cells B -> forall l k, In k [4; 5; 6]%nat ->
  In (z8 (ANum (decode_obj k)) (cp_m_tbl k)) (as_const B l).
Proof.
intros HC l k Hk. pose proof (HC l) as H. decompose [and] H.
cbn [In] in Hk; destruct Hk as [<- | [<- | [<- | []]]]; cp_m_tbl_val; cp_hyp.
Qed.
Lemma cp_m_tbl_range : forall k, In k [4; 5; 6]%nat -> 0 <= cp_m_tbl k < 2 ^ 64.
Proof. intros k Hk. cbn [In] in Hk; destruct Hk as [<- | [<- | [<- | []]]]; cp_m_tbl_val; lia. Qed.
(* Where the three tables lie (computed from the image). *)
Lemma cp_m_tbl_facts : forall k, In k [4; 5; 6]%nat ->
  4096 <= cp_m_tbl k /\ cp_m_tbl k + 16 <= alloc_ceiling /\ cp_m_tbl k mod 8 = 0 /\ CCL.A_T + 8 <= cp_m_tbl k /\
  IMG_LO <= cp_m_tbl k /\ cp_m_tbl k + 16 <= IMG_TOP.
Proof.
intros k Hk. pose proof alloc_ceiling_val as Hac. pose proof IMG_LO_val as HLO. pose proof IMG_TOP_val as HTOP.
cbn [In] in Hk; destruct Hk as [<- | [<- | [<- | []]]]; cp_m_tbl_val;
  repeat split; first [reflexivity | unfold CCL.A_T; lia].
Qed.
(* The table words a mode's two fields are read from, [T + 4, T + 12), are DEC_RO_RD bytes (check_round_trip_cg.v),
   so the read-only view shows them as the image holds them. The range is found by search, not by position. *)
Lemma cp_tbl_ro_rd : forall k, In k [4; 5; 6]%nat -> forall x, cp_m_tbl k + 4 <= x < cp_m_tbl k + 12 -> dec_in_ro_rd x.
Proof.
intros k Hk x Hx. cbn [In] in Hk; destruct Hk as [<- | [<- | [<- | []]]]; revert Hx; cp_m_tbl_val; intros Hx;
  unfold dec_in_ro_rd, DEC_RO_RD;
  repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
Qed.

(* The value-4 shadow row of a table's second granule (12 bytes = 8 + a 4-byte partial granule), found by its
   statement. *)
Lemma cp_tbl_sh4 : dec_crt_cells B -> forall ly S (W : world decodesegs0) mem md k,
  AR decodesegs0 B ly S W mem md -> In k [4; 5; 6]%nat ->
  aview decodesegs0 (w_H W) mem (DCells.shadow_addr (cp_m_tbl k + 8)) = Some 4.
Proof.
intros HC ly S W mem md k HAR Hk. pose proof HAR as (M & _).
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ M)) as Hconst.
pose proof (HC ly) as H. decompose [and] H.
cbn [In] in Hk; destruct Hk as [<- | [<- | [<- | []]]]; cp_m_tbl_val;
  apply (cp_z1 ly _ _ 4 ltac:(lia)); apply Hconst;
  match goal with H : In (z1 (ANum (DCells.shadow_addr ?a)) 4) _ |- In (z1 (ANum (DCells.shadow_addr ?b)) 4) _ =>
    let Eab := fresh in assert (Eab : b = a) by reflexivity; rewrite Eab; exact H end.
Qed.

(* The one place this file reads a table's shadow zero (its first granule): the dec_tab_zshadow_at conjunct of
   dec_crt_cells for the table, found by its statement, read at this state by dec_tab_zshadow_rd (AR's am_zshadow
   over the as_zero_shadow range the conjunct names). *)
Lemma cp_tbl_sh0 : dec_crt_cells B -> forall ly S (W : world decodesegs0) mem md k,
  AR decodesegs0 B ly S W mem md -> In k [4; 5; 6]%nat ->
  aview decodesegs0 (w_H W) mem (DCells.shadow_addr (cp_m_tbl k)) = Some 0.
Proof.
intros HC ly S W mem md k HAR Hk.
pose proof (HC ly) as H. decompose [and] H.
cbn [In] in Hk; destruct Hk as [<- | [<- | [<- | []]]]; cp_m_tbl_val;
  (apply (dec_tab_zshadow_rd B ly S W mem md _ HAR); [reflexivity | cp_hyp]).
Qed.

(* The mode tables: each mode cell decode_obj 4 / 5 / 6 holds one table's address (its pointer row), and each table's
   shadow is 0 for its first granule (cp_tbl_sh0) and 4 for its second (cp_tbl_sh4), which is what the two
   four-byte reads at mode + 4 and mode + 8 ask of the token engine (measured: ob_n = 4 at both). *)
Lemma cp_mode_table : dec_crt_cells B -> forall ly S (W : world decodesegs0) mem md (m : Z),
  AR decodesegs0 B ly S W mem md ->
  (rdword (aview decodesegs0 (w_H W) mem) (decode_obj 4) = Some m \/
   rdword (aview decodesegs0 (w_H W) mem) (decode_obj 5) = Some m \/
   rdword (aview decodesegs0 (w_H W) mem) (decode_obj 6) = Some m) ->
  4096 <= m /\ m + 16 <= alloc_ceiling /\ m mod 8 = 0 /\ CCL.A_T + 8 <= m /\
  range_addressable (aview decodesegs0 (w_H W) mem) SHADOW_OFF (m + 4) 4 /\
  range_addressable (aview decodesegs0 (w_H W) mem) SHADOW_OFF (m + 8) 4 /\ IMG_LO <= m /\ m + 16 <= IMG_TOP.
Proof using rc B.
intros HC ly S W mem md m HAR Hm. pose proof HAR as (M & _).
assert (Hp : forall k, In k [4; 5; 6]%nat -> rdword (aview decodesegs0 (w_H W) mem) (decode_obj k) = Some (cp_m_tbl k))
  by (intros k Hk; exact (rdword_cell B ly _ _ _ (cp_m_tbl_range k Hk)
        (proj1 (Forall_forall _ _) (am_const _ _ _ _ M) _ (cp_m_ptr HC ly k Hk)))).
(* m is the word of one of the three cells; k stays a variable, so no step below evaluates the image lookup. *)
assert (Hk : exists k, In k [4; 5; 6]%nat /\ rdword (aview decodesegs0 (w_H W) mem) (decode_obj k) = Some m)
  by (destruct Hm as [Hm | [Hm | Hm]]; [exists 4%nat | exists 5%nat | exists 6%nat]; (split; [cp_in | exact Hm])).
destruct Hk as (k & Hk & Hm').
pose proof (eq_trans (eq_sym (Hp k Hk)) Hm') as E. injection E as <-. clear Hm Hm'.
destruct (cp_m_tbl_facts k Hk) as (Hm0 & Hm1 & Hm8 & HmT & HmL & HmH).
pose proof (cp_tbl_sh0 HC ly S W mem md k HAR Hk) as Hz0.
pose proof (cp_tbl_sh4 HC ly S W mem md k HAR Hk) as Hz4.
set (m := cp_m_tbl k) in Hm0, Hm1, Hm8, HmT, HmL, HmH, Hz0, Hz4 |- *.
pose proof (Z.div_mod m 8 ltac:(lia)) as D. rewrite Hm8, Z.add_0_r in D.
assert (Esh : forall c, 0 <= c < 8 -> shadow_of_addr SHADOW_OFF (m + c) = DCells.shadow_addr m).
{ intros c Hc. unfold shadow_of_addr, DCells.shadow_addr, DCells.ASAN_K, SHADOW_OFF.
  replace (m + c) with (c + (m / 8) * 8) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
assert (Esh8 : shadow_of_addr SHADOW_OFF (m + 8) = DCells.shadow_addr (m + 8))
  by (unfold shadow_of_addr, DCells.shadow_addr, DCells.ASAN_K, SHADOW_OFF; lia).
repeat split; try assumption.
- apply (cp_ra_of_shadow _ (m + 4) 4 0); [lia | lia | | | left; reflexivity].
  + replace (m + 4) with (4 + (m / 8) * 8) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia.
  + rewrite Esh by lia. exact Hz0.
- apply (cp_ra_of_shadow _ (m + 8) 4 4); [lia | lia | | | right].
  + replace (m + 8) with (0 + (m / 8 + 1) * 8) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia.
  + rewrite Esh8. exact Hz4.
  + replace (m + 8) with (0 + (m / 8 + 1) * 8) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

(* The two div-36 words of lib/A/Prog/reac_frame_clean_len_c.v (A_M = decode_obj 7, A_T = decode_obj 8) that the
   listing loads at +0x2dc and +0x2e8: read-only bytes of the image (DEC_RO_RD), kept from the entry by the
   journal's image clause (YCbq.v:362) once dec_ro_rd_scoped keeps them off the owned statics and errno. *)
Lemma cp_rom_div : forall (cx : dctx) own ly' S' (W' : world decodesegs0) mem' md' k,
  (forall a, dec_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  dec_a_rom cx ->
  @ajournal rc dec_A_sink_head decodesegs0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) own ly' S' W' mem' md' k ->
  rdword (aview decodesegs0 (w_H W') mem') CCL.A_M = Some CCL.KM /\
  rdword (aview decodesegs0 (w_H W') mem') CCL.A_T = Some CCL.KT.
Proof.
intros cx own ly' S' W' mem' md' k HSC HROM HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _).
assert (Hkeep : forall a, dec_in_ro_rd a -> aview decodesegs0 (w_H W') mem' a =
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom decodesegs0 (Z_to_bv 64 a))).
{ intros a Ha. destruct (HSC a Ha) as [Hown Herr].
  destruct (dec_ro_rd_rom_clean a Ha) as [Hrom _].
  rewrite (G3 a).
  - exact (HROM a Hrom).
  - destruct Hrom as (sg & Hin & _ & Hlo). exists sg. split; [exact Hin | lia].
  - exact Hown.
  - exact Herr.
  - apply fp_spares_closed. intros (r & Hr & _). destruct Hr. }
split.
- rewrite (rdword_ext (fun a => option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom decodesegs0 (Z_to_bv 64 a)))
    (aview decodesegs0 (w_H W') mem') CCL.A_M).
  + vm_compute. reflexivity.
  + intros i Hi. apply Hkeep. unfold dec_in_ro_rd, DEC_RO_RD. apply Exists_cons_hd. unfold in_zr, CCL.A_M.
    cbn [fst snd]. lia.
- rewrite (rdword_ext (fun a => option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom decodesegs0 (Z_to_bv 64 a)))
    (aview decodesegs0 (w_H W') mem') CCL.A_T).
  + vm_compute. reflexivity.
  + intros i Hi. apply Hkeep. unfold dec_in_ro_rd, DEC_RO_RD.
    apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr, CCL.A_T. cbn [fst snd]. lia.
Qed.

(* The environment above the registers: the slots named in ss_copy. *)
Definition cp_extra (cx : dctx) (res mode nch ns : Z) : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 res; Z_to_bv 64 (dec_a_len (d_n cx)); Z_to_bv 64 mode;
   Z_to_bv 64 (d_F cx); Z_to_bv 64 (d_SH cx); Z_to_bv 64 (d_p cx + dec_a_u (d_n cx));
   Z_to_bv 64 (nch mod 2 ^ 32); Z_to_bv 64 (ns mod 2 ^ 32);
   Z_to_bv 64 (bv_unsigned (nth 12 (d_body cx) (Z_to_bv 8 0)));
   Z_to_bv 64 (bv_unsigned (nth 13 (d_body cx) (Z_to_bv 8 0)))].

(* The mode is a table of the image or the frame's own 12-byte local; either way its two fields are 8-aligned,
   inside the application window, and their shadow lets the two four-byte reads through. *)
Lemma cp_mode_facts : forall (cx : dctx) ly S (W : world decodesegs0) mem md mode nch ns,
  dec_crt_cells B -> AR_laws decodesegs0 B ->
  AR decodesegs0 B ly S W mem md ->
  In (DEC_FCLASS, d_fpos cx) (frames S) ->
  frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx ->
  4096 <= d_F cx -> d_F cx mod 32 = 0 ->
  dec_a_fsh cx (aview decodesegs0 (w_H W) mem) 0 4 ->
  dec_a_mode_ok cx W mem mode nch ns ->
  4096 <= mode /\ mode + 16 <= alloc_ceiling /\ mode mod 8 = 0 /\ (mode + 16 <= CCL.A_M \/ CCL.A_T + 8 <= mode) /\
  range_addressable (aview decodesegs0 (w_H W) mem) SHADOW_OFF (mode + 4) 4 /\
  range_addressable (aview decodesegs0 (w_H W) mem) SHADOW_OFF (mode + 8) 4 /\
  (forall b n, In (b, n) (ablocks B ly S) -> mode + 16 <= b \/ b + req_size n <= mode).
Proof.
intros cx ly S W mem md mode nch ns HCELLS LAWS HAR Hin Hfa HF4096 HFmod HFSH HMODE.
pose proof HMODE as (Hwhich & _ & _ & _ & _).
destruct Hwhich as [Hc | [Hc | [Hc | Hloc]]];
  [ destruct (cp_mode_table HCELLS ly S W mem md mode HAR (or_introl Hc)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8)
  | destruct (cp_mode_table HCELLS ly S W mem md mode HAR (or_intror (or_introl Hc)))
      as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8)
  | destruct (cp_mode_table HCELLS ly S W mem md mode HAR (or_intror (or_intror Hc)))
      as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8)
  | ].
1-3: repeat split; try assumption; [right; exact T4 |];
  intros b n Hbn; pose proof (blk_off_imgP B ly S W mem md b n HAR Hbn) as Hoff; unfold off_img in Hoff;
  pose proof IMG_LO_val; pose proof IMG_TOP_val; lia.
destruct (frames_bounds decodesegs0 B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin) as (_ & Hhi & _).
pose proof (frm_off_imgP B ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin) as Hoff.
pose proof IMG_LO_val as HLO. pose proof IMG_TOP_val as HTOP.
pose proof alloc_ceiling_val as Hac.
assert (Hfb : fs_frame_bytes DEC_FCLASS = 64) by reflexivity.
rewrite Hfa, Hfb in Hhi, Hoff.
pose proof HFSH as (_ & Hb4 & Hb5 & _).
assert (Hm8 : d_F cx mod 8 = 0) by (apply mod32_mod8; exact HFmod).
pose proof (Z.div_mod (d_F cx) 8 ltac:(lia)) as HD. rewrite Hm8, Z.add_0_r in HD.
assert (HSHv : d_SH cx = SHADOW_OFF + d_F cx / 8) by reflexivity.
split; [lia|]. split; [lia|].
split; [subst mode; replace (d_F cx + 32) with ((d_F cx / 8 + 4) * 8) by lia; apply Z.mod_mul; lia|].
split; [subst mode; unfold CCL.A_M, CCL.A_T; lia|].
subst mode. split; [|split; [|intros b n Hbn;
  pose proof (sep_block_frame decodesegs0 B LAWS ly S W mem md b n DEC_FCLASS (d_fpos cx) HAR Hbn Hin) as Hd;
  unfold zdisjoint in Hd; cbn [fst snd] in Hd; rewrite Hfa, Hfb in Hd; lia]].
- intros x Hx. exists 0. split; [| left; reflexivity].
  replace (shadow_of_addr SHADOW_OFF x) with (d_SH cx + 4); [exact Hb4|].
  unfold shadow_of_addr. rewrite HSHv.
  replace x with ((x - d_F cx - 32) + (d_F cx / 8 + 4) * 8) by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small (x - d_F cx - 32) 8) by lia. lia.
- intros x Hx. exists 4. split.
  + replace (shadow_of_addr SHADOW_OFF x) with (d_SH cx + 5); [exact Hb5|].
    unfold shadow_of_addr. rewrite HSHv.
    replace x with ((x - d_F cx - 40) + (d_F cx / 8 + 5) * 8) by lia.
    rewrite Z.div_add by lia. rewrite (Z.div_small (x - d_F cx - 40) 8) by lia. lia.
  + right. split; [|lia].
    replace x with ((x - d_F cx - 40) + (d_F cx / 8 + 5) * 8) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The state the segment carries between its calls                     *)
(* ------------------------------------------------------------------ *)

(* The copy's bytes once __asan_memcpy has filled it (llvm_a_st_3c0's garr8 conjunct); for an empty copy it says
   nothing. *)
Definition cp_body (cx : dctx) : list Z := map (fun b : byte => bv_unsigned b) (d_body cx).
Definition cp_filled (cx : dctx) (res : Z) (W : world decodesegs0) (mem : word -> option byte) : Prop :=
  garr8 decodesegs0 (mrestrict (w_H W) mem) res (cp_body cx).
(* s9 and s7 hold the mode and its nch field's address from +0x234 to +0x388. *)
Definition cp_rm (mode : Z) (regs : bvmap 5 word) : Prop :=
  YK11.getr regs 25 = w64 mode /\ YK11.getr regs 23 = w64 (mode + 4).

(* Every point of the segment: llvm_a_st_234's frame invariant and memory facts, with s4 already the copy
   (`mv s4, a0` at +0x234). The registers the segment rewrites (a0 .. a2, ra, s7, s8, s9) are each cut point's own
   (the R of cp_at). *)
Definition cp_core (cx : dctx) (res mode nch ns : Z) (ly' : alayout) (S' : astate) (W' : world decodesegs0)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  dec_a_core B cx ly' S' W' regs' mem' md' dec_ev_234 /\
  ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] /\
  4096 <= res /\
  mo_le MT (d_S cx) S' (dec_spent_234 MT (d_n cx)) /\ mo_ok MT S' (dec_rest_234 MT) /\
  dec_a_fr cx regs' /\
  YK11.getr regs' 18 = w64 SHADOW_OFF /\
  YK11.getr regs' 20 = w64 res /\
  YK11.getr regs' 22 = w64 (mode + 8) /\
  YK11.getr regs' 26 = w64 (dec_a_len (d_n cx)) /\
  dec_a_mode_ok cx W' mem' mode nch ns /\
  dec_a_fsh cx (aview decodesegs0 (w_H W') mem') 0 4 /\
  dec_a_slot cx (aview decodesegs0 (w_H W') mem') 112 (d_F cx).

(* A configuration of the segment at pc word pcw: cp_core, the floating-point state llvm_a_st_234 asks, the cut
   point's registers R and its extra memory facts M. *)
Definition cp_at (pcw : word) (cx : dctx) (res mode nch ns : Z) (R : bvmap 5 word -> Prop)
    (M : world decodesegs0 -> (word -> option byte) -> Prop) : world decodesegs0 -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md',
    c' = mkCfg (@YK11.mkst fx' regs' pcw mem' (YK11.seg_rom decodesegs0)) md' /\
    frm_zero (@fp_csr fx') /\
    cp_core cx res mode nch ns ly' S' W' regs' mem' md' /\ R regs' /\ M W' mem'.
(* ... at the function's offset pc. *)
Definition cp_st (pc : Z) : dctx -> Z -> Z -> Z -> Z -> (bvmap 5 word -> Prop) ->
    (world decodesegs0 -> (word -> option byte) -> Prop) -> world decodesegs0 -> config -> Prop :=
  cp_at (w64 (DEC_A_LLVMF + pc)).

(* Memory facts carried where their bytes are kept (libreac/fuzz_decode lib/A/Prog/LLVMFuzzerTestOneInput_seg_early.v
   e_val_mem_moved / e_garr8_kept / e_saved_kept / e_fsh_kept / e_slot_kept, the same text). *)
Lemma cp_val_mem_moved : forall H H' (m m' : word -> option byte) a n v,
  (forall k, 0 <= k < Z.of_nat n -> aview decodesegs0 H' m' (a + k) = aview decodesegs0 H m (a + k)) ->
  val_mem decodesegs0 (mrestrict H m) a n v -> val_mem decodesegs0 (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hkn. specialize (Hk (Z.of_nat k) ltac:(lia)). unfold aview in Hk.
rewrite (Hv k Hkn) in Hk. destruct (mbyte decodesegs0 (mrestrict H' m') (a + Z.of_nat k)) as [b'|]; cbn in Hk; [|discriminate].
injection Hk as Hk. f_equal. apply bv_eq. exact Hk.
Qed.
Lemma cp_garr8_kept : forall H H' (m m' : word -> option byte) base l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview decodesegs0 H' m' (base + j) = aview decodesegs0 H m (base + j)) ->
  garr8 decodesegs0 (mrestrict H m) base l -> garr8 decodesegs0 (mrestrict H' m') base l.
Proof.
intros H H' m m' base l HK HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
apply (cp_val_mem_moved H H' m m' (base + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk. replace (base + Z.of_nat j + k) with (base + (Z.of_nat j + k)) by lia. apply HK. lia.
Qed.
Lemma cp_saved_kept : forall cx (r r' : reader),
  (forall a, d_sp0 cx - 104 <= a < d_sp0 cx -> r' a = r a) -> dec_a_saved cx r -> dec_a_saved cx r'.
Proof.
intros cx r r' Hk Hs. unfold dec_a_saved in *. rewrite Forall_forall in Hs |- *.
intros [off q] Hin. rewrite <- (Hs (off, q) Hin). cbn [fst snd].
assert (Ho : 8 <= off <= 104) by (unfold dec_a_saved_at in Hin; cbn [In] in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia|]); destruct Hin).
apply rdword_ext. intros j Hj. apply Hk. lia.
Qed.
Lemma cp_fsh_kept : forall cx (r r' : reader) b4 b5,
  (forall i, 0 <= i < 8 -> r' (d_SH cx + i) = r (d_SH cx + i)) -> dec_a_fsh cx r b4 b5 -> dec_a_fsh cx r' b4 b5.
Proof.
intros cx r r' b4 b5 Hk (H0 & H4 & H5 & H6). unfold dec_a_fsh.
split; [intros i Hi; rewrite Hk by lia; exact (H0 i Hi)|].
split; [rewrite Hk by lia; exact H4|]. split; [rewrite Hk by lia; exact H5|].
intros i Hi; rewrite Hk by lia; exact (H6 i Hi).
Qed.
Lemma cp_slot_kept : forall cx (r r' : reader) off v,
  (forall i, 0 <= i < 8 -> r' (d_sp1 cx + off + i) = r (d_sp1 cx + off + i)) ->
  dec_a_slot cx r off v -> dec_a_slot cx r' off v.
Proof. intros cx r r' off v Hk Hs. unfold dec_a_slot in *. rewrite <- Hs. apply rdword_ext. exact Hk. Qed.

(* cp_core survives a step that keeps the journal and every view byte off the copy and off the stack below
   s1 + 96 (the callee's window below sp = s1, and the spill slots +32 .. +96 the segment writes at +0x370..+0x398):
   the saved words (above s1 + 120), the fake frame and its shadow, the payload, the mode and its cells, and the
   slot 112(s1) all lie off both. *)
Lemma cp_core_kept : forall (cx : dctx) (res mode nch ns : Z) ly S (W : world decodesegs0) regs mem md mem2 md2,
  AR_laws decodesegs0 B -> dec_crt_cells B -> d_n cx = Z.of_nat (length (d_pl cx)) ->
  cp_core cx res mode nch ns ly S W regs mem md ->
  @ajournal rc dec_A_sink_head decodesegs0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S W mem2 md2 dec_ev_234 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + dec_a_len (d_n cx)) -> ~ (d_sp1 cx - 4096 <= a < d_sp1 cx + 96) ->
     aview decodesegs0 (w_H W) mem2 a = aview decodesegs0 (w_H W) mem a) ->
  cp_core cx res mode nch ns ly S W regs mem2 md2.
Proof.
intros cx res mode nch ns ly S W regs mem md mem2 md2 LAWS HCELLS Hlen HCORE HJ2 K.
destruct HCORE as (HC & Hbl & Hres & Hmle & Hmok & Hfr & R18 & R20 & R22 & R26 & HMODE & HFSH & HSLOT).
pose proof HC as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1a & Hgp & Htp & Hsaved & HF4 & HFa & HFp & HFL & Hblk & Hga).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof HJ2 as (HAR2 & _).
pose proof Hstk as (Hsp0a & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof alloc_ceiling_val as Hac. pose proof IMG_LO_val as HLO. pose proof IMG_TOP_val as HTOP.
unfold DEC_LLVMF_STK, d_sp0 in *.
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hfb : fs_frame_bytes DEC_FCLASS = 64) by reflexivity.
destruct (frames_bounds decodesegs0 B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin0) as (_ & HFhi & _).
rewrite EFA, Hfb in HFhi.
assert (Hinr : In (res, dec_a_len (d_n cx)) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (_ & _ & Hrceil & Hrapp & _).
pose proof (req_size_pos0 (dec_a_len (d_n cx)) ltac:(unfold dec_a_len; lia)) as (_ & Hreq).
pose proof (sep_block_frame decodesegs0 B LAWS ly S W mem md _ _ _ _ HAR Hinr Hin0) as HdF.
rewrite EFA, Hfb in HdF. unfold zdisjoint in HdF. cbn [fst snd] in HdF.
pose proof (blk_off_imgP B ly S W mem md res _ HAR Hinr) as Hroff. unfold off_img in Hroff.
destruct (cp_mode_facts cx ly S W mem md mode nch ns HCELLS LAWS HAR Hin0 EFA HF4 HFa HFSH HMODE)
  as (Hm0 & Hm1 & Hm8 & HmD & HmS4 & HmS8 & HmB).
pose proof (HmB res _ Hinr) as HmR.
(* the stack window starts above every allocator byte *)
assert (HW : alloc_ceiling + 4096 <= d_sp1 cx) by lia.
assert (KA : forall a, 0 <= a -> a + 1 <= alloc_ceiling -> ~ (res <= a < res + dec_a_len (d_n cx)) ->
  aview decodesegs0 (w_H W) mem2 a = aview decodesegs0 (w_H W) mem a).
{ intros a Ha0 Ha1 Hnr. apply K; [lia | exact Hnr | lia]. }
assert (KS : forall a, d_sp1 cx + 96 <= a < 2 ^ 47 ->
  aview decodesegs0 (w_H W) mem2 a = aview decodesegs0 (w_H W) mem a).
{ intros a Ha. apply K; lia. }
assert (KSH : forall i, 0 <= i < 8 ->
  aview decodesegs0 (w_H W) mem2 (d_SH cx + i) = aview decodesegs0 (w_H W) mem (d_SH cx + i)).
{ intros i Hi. assert (HSHv : d_SH cx = SHADOW_OFF + d_F cx / 8) by reflexivity.
  pose proof (Z.div_pos (d_F cx) 8 ltac:(lia) ltac:(lia)) as HFd.
  assert (HFd2 : d_F cx / 8 <= d_F cx) by (apply Z.div_le_upper_bound; lia).
  unfold SHADOW_OFF in HSHv. apply K.
  - lia.
  - intros Hr. apply (fshadow_not_app (d_F cx) 8 res (dec_a_len (d_n cx)) (d_SH cx + i) HF4); [lia | | | exact Hr].
    + assert (0 <= dec_a_len (d_n cx)) by (unfold dec_a_len; lia).
      apply (in_app_sub res (req_size (dec_a_len (d_n cx))) res (dec_a_len (d_n cx)) Hrapp); lia.
    + lia.
  - assert (HFd3 : 8 * (d_F cx / 8) <= d_F cx) by (apply Z.mul_div_le; lia). lia. }
unfold cp_core.
split.
{ split; [exact HJ2|]. split; [exact Hfrs|]. split; [exact R8|]. split; [exact R9|]. split; [exact Hsp|].
  split; [exact Hsp1r|]. split; [exact Hsp1a|]. split; [exact Hgp|]. split; [exact Htp|].
  split; [apply (cp_saved_kept cx (aview decodesegs0 (w_H W) mem));
    [intros a Ha; unfold d_sp0 in Ha; apply KS; lia | exact Hsaved]|].
  split; [exact HF4|]. split; [exact HFa|].
  split.
  { intros a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin0) as (_ & _ & Hfp2 & _).
    rewrite EFA, Hfb in Hfp2. exact (proj1 (Hfp2 a Ha)). }
  split; [rewrite <- HFL; apply rdword_ext; intros j Hj; apply KA; lia|].
  split; [exact Hblk|].
  destruct (Z.eq_dec (d_n cx) 0) as [Hn0 | Hn0].
  - rewrite Hn0 in Hlen. destruct (d_pl cx); [intros j Hj; cbn in Hj; lia | cbn in Hlen; lia].
  - assert (Hpin : In (d_p cx, d_n cx) (ablocks B ly S)) by (apply Hblk; lia).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos0 (d_n cx) ltac:(lia)) as (_ & Hpreq).
    assert (Hne : (d_p cx, d_n cx) <> (res, dec_a_len (d_n cx))) by (intros Heq; injection Heq as _ Hq; unfold dec_a_len in Hq; lia).
    pose proof (sep_blocks decodesegs0 B LAWS ly S W mem md _ _ _ _ HAR Hpin Hinr Hne) as HdP.
    unfold zdisjoint in HdP. cbn [fst snd] in HdP.
    apply (cp_garr8_kept (w_H W) (w_H W) mem mem2 (d_p cx) _); [| exact Hga].
    intros j Hj. rewrite length_map, <- Hlen in Hj. apply KA; lia. }
split; [exact Hbl|]. split; [exact Hres|]. split; [exact Hmle|]. split; [exact Hmok|]. split; [exact Hfr|].
split; [exact R18|]. split; [exact R20|]. split; [exact R22|]. split; [exact R26|].
split.
{ destruct HMODE as (Hwhich & Hnch & Hns & V4 & V8).
  assert (Hcell : forall k, (k = 4 \/ k = 5 \/ k = 6)%nat ->
    rdword (aview decodesegs0 (w_H W) mem2) (decode_obj k) = rdword (aview decodesegs0 (w_H W) mem) (decode_obj k)).
  { intros k Hk. apply rdword_ext. intros j Hj.
    assert (Hob : IMG_LO <= decode_obj k /\ decode_obj k + 8 <= IMG_TOP)
      by (rewrite HLO, HTOP; destruct Hk as [-> | [-> | ->]]; vm_compute; split; congruence).
    apply KA; lia. }
  split.
  { destruct Hwhich as [Hc | [Hc | [Hc | Hc]]];
      [ left; rewrite Hcell by auto; exact Hc
      | right; left; rewrite Hcell by auto; exact Hc
      | right; right; left; rewrite Hcell by auto; exact Hc
      | right; right; right; exact Hc ]. }
  split; [exact Hnch|]. split; [exact Hns|].
  split; (eapply cp_val_mem_moved; [| eassumption]); intros j Hj; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj;
    apply KA; lia. }
split; [apply (cp_fsh_kept cx (aview decodesegs0 (w_H W) mem)); [exact KSH | exact HFSH]|].
apply (cp_slot_kept cx (aview decodesegs0 (w_H W) mem)); [intros i Hi; apply KS; lia | exact HSLOT].
Qed.

(* cp_core's registers are callee-saved (YG0d.v acallee_saved: sp, gp, tp, s0, s1, s2 .. s11), so a call that
   preserves them (aregs_preserved) keeps cp_core and cp_rm. *)
Lemma cp_core_regs : forall (cx : dctx) (res mode nch ns : Z) ly S (W : world decodesegs0) regs regs2 mem md,
  cp_core cx res mode nch ns ly S W regs mem md -> aregs_preserved regs regs2 ->
  cp_core cx res mode nch ns ly S W regs2 mem md.
Proof.
intros cx res mode nch ns ly S W regs regs2 mem md HCORE P.
destruct HCORE as (HC & Hbl & Hres & Hmle & Hmok & (F19 & F21 & F27) & R18 & R20 & R22 & R26 & HMODE & HFSH & HSLOT).
destruct HC as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1a & Hgp & Htp & Hrest).
assert (Q : forall r : Z, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) by exact P.
split; [|split; [exact Hbl|]].
{ split; [exact HJ|]. split; [exact Hfrs|].
  split; [exact (eq_trans (Q 8 ltac:(unfold acallee_saved; lia)) R8)|].
  split; [exact (eq_trans (Q 9 ltac:(unfold acallee_saved; lia)) R9)|].
  split; [unfold spZ in *; rewrite <- Hsp; f_equal; exact (Q 2 ltac:(unfold acallee_saved; lia))|].
  split; [exact Hsp1r|]. split; [exact Hsp1a|].
  split; [exact (eq_trans (Q 3 ltac:(unfold acallee_saved; lia)) Hgp)|].
  split; [exact (eq_trans (Q 4 ltac:(unfold acallee_saved; lia)) Htp)|].
  exact Hrest. }
split; [exact Hres|]. split; [exact Hmle|]. split; [exact Hmok|].
split; [split; [exact (eq_trans (Q 19 ltac:(unfold acallee_saved; lia)) F19)|];
        split; [exact (eq_trans (Q 21 ltac:(unfold acallee_saved; lia)) F21)|
                exact (eq_trans (Q 27 ltac:(unfold acallee_saved; lia)) F27)]|].
split; [exact (eq_trans (Q 18 ltac:(unfold acallee_saved; lia)) R18)|].
split; [exact (eq_trans (Q 20 ltac:(unfold acallee_saved; lia)) R20)|].
split; [exact (eq_trans (Q 22 ltac:(unfold acallee_saved; lia)) R22)|].
split; [exact (eq_trans (Q 26 ltac:(unfold acallee_saved; lia)) R26)|].
split; [exact HMODE|]. split; [exact HFSH|]. exact HSLOT.
Qed.
Lemma cp_rm_regs : forall mode regs regs2, cp_rm mode regs -> aregs_preserved regs regs2 -> cp_rm mode regs2.
Proof.
intros mode regs regs2 (R25 & R23) P.
assert (Q : forall r : Z, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) by exact P.
split; [exact (eq_trans (Q 25 ltac:(unfold acallee_saved; lia)) R25) | exact (eq_trans (Q 23 ltac:(unfold acallee_saved; lia)) R23)].
Qed.

(* ------------------------------------------------------------------ *)
(* The segment's calls                                                  *)
(* ------------------------------------------------------------------ *)

(* +0x250: __asan_memcpy (res, p + u, len), by the statement's aintrin_realizes (YC85.v aj_intrin_atS). *)
Definition cp_call_memcpy_stmt : Prop :=
  AR_laws decodesegs0 B -> dec_crt_cells B ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc decodesegs0 B OCpy (decode_sigma DS___asan_memcpy)) ->
  forall (cx : dctx) (res mode nch ns : Z) (W : world decodesegs0) (c : config),
    dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
    0 < dec_a_len (d_n cx) ->
    cp_at (Z_to_bv 64 (decode_sigma DS___asan_memcpy)) cx res mode nch ns
      (fun r => cp_rm mode r /\ YK11.getr r 10 = w64 res /\ YK11.getr r 11 = w64 (d_p cx + dec_a_u (d_n cx)) /\
                YK11.getr r 12 = w64 (dec_a_len (d_n cx)) /\ YK11.getr r 1 = w64 (DEC_A_LLVMF + 0x254))
      (fun _ _ => True) W c ->
    SRr decodesegs0 W c (cp_st 0x254 cx res mode nch ns (cp_rm mode) (cp_filled cx res)).

(* +0x25c (a1 = len, returning to +0x260) and +0x2b0 (a1 = 0, the empty copy, returning to +0x2b4):
   reac_frame_is_reac (res, a1), by the statement's dec_leaf_at premise. *)
Definition cp_call_isreac_stmt : Prop :=
  AR_laws decodesegs0 B -> dec_crt_cells B ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LIR.dec_reac_frame_is_reac_cg) fx) ->
  forall (cx : dctx) (res mode nch ns a1v retpc : Z) (W : world decodesegs0) (c : config),
    dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
    (a1v = dec_a_len (d_n cx) \/ a1v = 0) -> (retpc = 0x260 \/ retpc = 0x2b4) ->
    cp_at (Z_to_bv 64 (decode_sigma DS_reac_frame_is_reac)) cx res mode nch ns
      (fun r => cp_rm mode r /\ YK11.getr r 10 = w64 res /\ YK11.getr r 11 = w64 a1v /\
                YK11.getr r 1 = w64 (DEC_A_LLVMF + retpc))
      (cp_filled cx res) W c ->
    SRr decodesegs0 W c (cp_st retpc cx res mode nch ns
      (fun r => cp_rm mode r /\ YK11.getr r 10 = w64 (CIR.is_reac_result res a1v (d_body cx)))
      (cp_filled cx res)).

(* +0x2c0: reac_frame_clean_len (len), by the statement's dec_leaf_at premise; its two read-only words come from
   the entry's read-only view through the journal's image clause (cp_rom_div). *)
Definition cp_call_clean_stmt : Prop :=
  AR_laws decodesegs0 B -> dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCL.dec_reac_frame_clean_len_cg) fx) ->
  forall (cx : dctx) (res mode nch ns : Z) (W : world decodesegs0) (c : config),
    dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
    dec_a_rom cx ->
    cp_at (Z_to_bv 64 (decode_sigma DS_reac_frame_clean_len)) cx res mode nch ns
      (fun r => cp_rm mode r /\ YK11.getr r 10 = w64 (dec_a_len (d_n cx)) /\
                YK11.getr r 1 = w64 (DEC_A_LLVMF + 0x2c4))
      (cp_filled cx res) W c ->
    SRr decodesegs0 W c (cp_st 0x2c4 cx res mode nch ns
      (fun r => cp_rm mode r /\
                YK11.getr r 10 = w64 (CCL.reac_frame_clean_len_model (dec_a_len (d_n cx))))
      (cp_filled cx res)).

(* +0x3bc: malloc #2 (olen), by the statement's amalloc04_rule (YC85.v amalloc04_sub); its post is the segment's,
   llvm_a_st_3c0. The spill slots 32 .. 88 (s1) are the stores at +0x370 .. +0x398. *)
Definition cp_call_malloc2_stmt : Prop :=
  pc_wrap_malloc (as_code B) = decode_sigma DS___interceptor_trampoline_malloc ->
  dec_llvmf_utraces RA_LLVMF B -> dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws decodesegs0 B -> ameter_laws MT ->
  (forall fx : YK11.FPState, @amalloc04_rule fx rc dec_A_sink_head decodesegs0 B MT) ->
  forall (cx : dctx) (res mode nch ns : Z) (W : world decodesegs0) (c : config),
    dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
    dec_a_rom cx ->
    cp_at (Z_to_bv 64 (decode_sigma DS___interceptor_trampoline_malloc)) cx res mode nch ns
      (fun r => YK11.getr r 10 = w64 (dec_a_olen nch ns) /\ YK11.getr r 1 = w64 (DEC_A_LLVMF + 0x3c0) /\
                YK11.getr r 24 = w64 (dec_a_prod nch ns) /\ YK11.getr r 25 = w64 (dec_a_olen nch ns) /\
                YK11.getr r 23 = w64 (ns mod 2 ^ 32))
      (fun W' m => cp_filled cx res W' m /\
         dec_a_slot cx (aview decodesegs0 (w_H W') m) 32 (dec_a_fits0 nch ns) /\
         dec_a_slot cx (aview decodesegs0 (w_H W') m) 48 (nch mod 2 ^ 64) /\
         dec_a_slot cx (aview decodesegs0 (w_H W') m) 64 mode /\
         dec_a_slot cx (aview decodesegs0 (w_H W') m) 80 (nch mod 2 ^ 32) /\
         dec_a_slot cx (aview decodesegs0 (w_H W') m) 88 (ns mod 2 ^ 64)) W c ->
    SRr decodesegs0 W c (llvm_a_st_3c0 B MT cx).

End seg.


(* ------------------------------------------------------------------ *)
(* 2. __asan_memcpy at +0x250                                          *)
(* ------------------------------------------------------------------ *)

Section seg.
Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable asink_img_laws : list Segment -> asyms -> asink_syms -> Prop.
Variable ro_below_ofl : list Segment -> Z -> Z -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
#[local] Notation SEGS := (@pa_segs _ decode_listing (@PI_decode _)).
#[local] Notation VAL := (@pa_val _ decode_listing (@PI_decode _)).

(* The two fields of the slot pre (dec_lib_pre_x) this call reads, found by type. *)
Lemma cpm_base_pn : forall cx,
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  (d_n cx = 0 /\ d_p cx = A_EMPTY) \/ (0 < d_n cx < 2 ^ 26 /\ In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))).
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma cpm_base_len : forall cx,
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  d_n cx = Z.of_nat (length (d_pl cx)).
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.

(* A value / byte array read at one address is read at another where the view shows the same bytes. *)
Lemma cpm_val_mem_shift : forall H H' (m m' : word -> option byte) a a' n v,
  (forall k, 0 <= k < Z.of_nat n -> aview decodesegs0 H' m' (a' + k) = aview decodesegs0 H m (a + k)) ->
  val_mem decodesegs0 (mrestrict H m) a n v -> val_mem decodesegs0 (mrestrict H' m') a' n v.
Proof.
intros H H' m m' a a' n v Hk Hv k Hkn. specialize (Hk (Z.of_nat k) ltac:(lia)). unfold aview in Hk.
rewrite (Hv k Hkn) in Hk.
destruct (mbyte decodesegs0 (mrestrict H' m') (a' + Z.of_nat k)) as [b'|]; cbn in Hk; [|discriminate].
injection Hk as Hk. f_equal. apply bv_eq. exact Hk.
Qed.
Lemma cpm_garr8_shift : forall H H' (m m' : word -> option byte) base base' l,
  (forall j, 0 <= j < Z.of_nat (length l) ->
     aview decodesegs0 H' m' (base' + j) = aview decodesegs0 H m (base + j)) ->
  garr8 decodesegs0 (mrestrict H m) base l -> garr8 decodesegs0 (mrestrict H' m') base' l.
Proof.
intros H H' m m' base base' l HK HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
apply (cpm_val_mem_shift H H' m m' (base + Z.of_nat j) (base' + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk. replace (base' + Z.of_nat j + k) with (base' + (Z.of_nat j + k)) by lia.
replace (base + Z.of_nat j + k) with (base + (Z.of_nat j + k)) by lia. apply HK. lia.
Qed.

(* +0x250: __asan_memcpy (res, p + u, len) by aj_intrin_atS; back at +0x254 the copy holds the payload body. *)
Lemma cp_call_memcpy : cp_call_memcpy_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold cp_call_memcpy_stmt.
intros LAWS HCELLS AI cx res mode nch ns W c HB Hlen0
  (fx' & ly' & S' & regs' & mem' & md' & -> & Hfrm & HCORE & (HRM & R10 & R11 & R12 & R1) & _).
pose proof HCORE as (HC & Hbl & Hres & _).
pose proof HC as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1a & Hgp & Htp & Hsaved & HF4 & HFa & HFp & HFL & Hblk & Hga).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof alloc_ceiling_val as Hac.
pose proof (cpm_base_pn cx HB) as Hpn. pose proof (cpm_base_len cx HB) as Hlenpl.
assert (HSTK : DEC_LLVMF_STK = 32768) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hn : 3 < d_n cx < 2 ^ 26) by (unfold dec_a_len in Hlen0; destruct Hpn as [(Hn0 & _) | (Hn0 & _)]; lia).
assert (Hu : dec_a_u (d_n cx) = 3) by (unfold dec_a_u; lia).
assert (Hl : dec_a_len (d_n cx) = d_n cx - 3) by (unfold dec_a_len; lia).
(* the two blocks: the payload (p, n) and the copy (res, len) *)
assert (Hpin : In (d_p cx, d_n cx) (ablocks B ly' S')) by (apply Hblk; lia).
assert (Hrin : In (res, dec_a_len (d_n cx)) (ablocks B ly' S'))
  by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hrin) as (_ & Hr4096 & Hrceil & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin) as (_ & Hp4096 & Hpceil & _ & Hppres & _ & _).
pose proof (req_size_pos0 (dec_a_len (d_n cx)) ltac:(lia)) as (_ & Hrq).
pose proof (req_size_pos0 (d_n cx) ltac:(lia)) as (_ & Hpq).
assert (Hne : (d_p cx, d_n cx) <> (res, dec_a_len (d_n cx))) by (intros Heq; injection Heq as _ Hq; lia).
pose proof (sep_blocks _ _ LAWS _ _ _ _ _ _ _ _ _ HAR Hpin Hrin Hne) as Hdj.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
(* the stack: sp = s1 = sp0 + o, 16-aligned, its 4096-byte callee window above every allocator byte *)
assert (Hsp016 : (d_sp1 cx - d_sp0 cx) mod 16 = 0).
{ pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D1. pose proof (Z.div_mod (d_sp0 cx) 16 ltac:(lia)) as D2.
  unfold d_sp0 in *. rewrite Hsp1a in D1. rewrite Hsp0a in D2.
  replace (d_sp1 cx - spZ (d_regs cx)) with ((2 * (d_sp1 cx / 32) - spZ (d_regs cx) / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
assert (HW : alloc_ceiling + 4096 <= d_sp1 cx) by lia.
assert (Hsrc : 0 <= d_p cx + dec_a_u (d_n cx) /\ d_p cx + dec_a_u (d_n cx) + dec_a_len (d_n cx) <= 2 ^ 63 /\
  src_ok decodesegs0 W regs' mem' (d_p cx + dec_a_u (d_n cx)) (dec_a_len (d_n cx)) /\
  (res + dec_a_len (d_n cx) <= d_p cx + dec_a_u (d_n cx) \/
   d_p cx + dec_a_u (d_n cx) + dec_a_len (d_n cx) <= res) /\
  amem_range (d_p cx + dec_a_u (d_n cx)) (dec_a_len (d_n cx)) /\
  range_addressable (aview decodesegs0 (w_H W) mem') SHADOW_OFF (d_p cx + dec_a_u (d_n cx)) (dec_a_len (d_n cx)) /\
  (0 < dec_a_len (d_n cx) ->
   shadow_hull_vis (aview decodesegs0 (w_H W) mem') (d_p cx + dec_a_u (d_n cx)) (dec_a_len (d_n cx)))).
{ split; [lia|]. split; [lia|].
  split.
  { intros a Ha. split; [apply (aview_some_of_apresent decodesegs0); exact (proj1 (Hppres a ltac:(lia)))|].
    rewrite Hsp, Hes. lia. }
  split; [lia|].
  split; [eapply (amem_range_of_block decodesegs0 B LAWS _ _ _ _ _ _ _ _ _ HAR Hpin); lia|].
  split; [eapply (range_addressable_of_block decodesegs0 B LAWS _ _ _ _ _ _ _ _ _ HAR Hpin); lia|].
  intros Hk0. eapply (shadow_hull_vis_of_block decodesegs0 B LAWS _ _ _ _ _ _ _ _ _ HAR Hpin); lia. }
eapply SRr_mono.
{ apply (aj_intrin_atS (fx := fx') (SK := dec_A_sink_head) decodesegs0 B LAWS decode_segs_low OCpy
    (decode_sigma DS___asan_memcpy) (AI fx') W regs' mem' DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx)
    (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' md' dec_ev_234 res (d_p cx + dec_a_u (d_n cx))
    (dec_a_len (d_n cx)) (d_sp1 cx - d_sp0 cx) (w64 (DEC_A_LLVMF + 0x254)) HJ R10 R11 R12
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Hsp; lia) Hsp016 ltac:(lia) ltac:(rewrite Hes, HSTK; lia)
    Hgp Htp R1 (@ret_ok_codeptr_v rc decode_listing PI_decode 0x254 ltac:(lia) eq_refl)).
  - intros a Ha. split.
    + exact (dec_leafb_awr_new B LAWS DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) ly' S' W mem' md'
        [(DEC_FCLASS, d_fpos cx)] [(res, dec_a_len (d_n cx))] res (dec_a_len (d_n cx)) a HAR Hbl
        (or_introl eq_refl) ltac:(lia)).
    + rewrite Hes. lia.
  - eapply (amem_range_of_block decodesegs0 B LAWS _ _ _ _ _ _ _ _ _ HAR Hrin); lia.
  - eapply (range_addressable_of_block decodesegs0 B LAWS _ _ _ _ _ _ _ _ _ HAR Hrin); lia.
  - intros Hk0. eapply (shadow_hull_vis_of_block decodesegs0 B LAWS _ _ _ _ _ _ _ _ _ HAR Hrin); lia.
  - exact Hsrc. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & _ & Hcopy & Hkeep & _).
cbv iota in Hcopy.
unfold cp_st, cp_at.
exists fx', ly', S', regs2, mem2, md2.
split; [reflexivity|]. split; [exact Hfrm|].
split.
{ apply (cp_core_regs B MT cx res mode nch ns ly' S' W regs' regs2 mem2 md2); [|exact HP].
  apply (cp_core_kept B MT cx res mode nch ns ly' S' W regs' mem' md' mem2 md2 LAWS HCELLS Hlenpl HCORE HJ2).
  intros a Ha Hnr Hns. apply Hkeep; [exact Ha | exact Hnr | rewrite Hes; lia]. }
split; [exact (cp_rm_regs mode regs' regs2 HRM HP)|].
(* the copy: [res, res + len) holds the payload's bytes from p + u on, i.e. the body skipn u pl *)
unfold cp_filled, cp_body, d_body.
rewrite <- (firstn_skipn (Z.to_nat (dec_a_u (d_n cx))) (d_pl cx)) in Hga.
rewrite map_app in Hga.
apply garr8_app in Hga as [_ Hga2].
rewrite length_map, length_firstn in Hga2.
eapply (cpm_garr8_shift (w_H W) (w_H W) mem' mem2 _ res _); [|exact Hga2].
intros j Hj. rewrite length_map, length_skipn in Hj.
rewrite (Hcopy j ltac:(lia)).
f_equal. lia.
Qed.

End seg.

(* ------------------------------------------------------------------ *)
(* 3. reac_frame_is_reac (+0x25c, +0x2b0) and reac_frame_clean_len (+0x2c0) *)
(* ------------------------------------------------------------------ *)

Section seg.
Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable asink_img_laws : list Segment -> asyms -> asink_syms -> Prop.
Variable ro_below_ofl : list Segment -> Z -> Z -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
#[local] Notation SEGS := (@pa_segs _ decode_listing (@PI_decode _)).
#[local] Notation VAL := (@pa_val _ decode_listing (@PI_decode _)).

(* ------------------------------------------------------------------ *)
(* What both leaf calls read                                           *)
(* ------------------------------------------------------------------ *)

(* The payload length, read by type from the slot pre (no positional destruct of dec_lib_pre_x). *)
Lemma cp_base_len : forall (cx : dctx),
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  d_n cx = Z.of_nat (length (d_pl cx)).
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.

(* The body the copy holds is as long as the copy. *)
Lemma cp_body_len : forall (cx : dctx), d_n cx = Z.of_nat (length (d_pl cx)) ->
  Z.of_nat (length (d_body cx)) = dec_a_len (d_n cx).
Proof. intros cx H. unfold d_body, dec_a_u, dec_a_len. rewrite length_skipn. lia. Qed.

(* The listing's base is the function's entry. *)
Lemma cp_base_eq : VAL A_TEXT = DEC_A_LLVMF.
Proof. vm_compute. reflexivity. Qed.

(* The three return addresses of the segment's leaf calls are code pointers. *)
Lemma cp_ret_ok : forall retpc, retpc = 0x260 \/ retpc = 0x2b4 \/ retpc = 0x2c4 ->
  YK0s.ret_ok (w64 (DEC_A_LLVMF + retpc)).
Proof.
intros retpc H. rewrite <- cp_base_eq. unfold w64.
destruct H as [-> | [-> | ->]]; apply ret_ok_codeptr_v; first [lia | reflexivity].
Qed.

(* The stack and the copy's block, as cp_core holds them: sp = s1, the window below sp lies in the journal's stack
   range and above every allocator byte, and the copy is a block below alloc_ceiling. *)
Lemma cp_geom : forall (cx : dctx) (res mode nch ns : Z) ly S (W : world decodesegs0) regs mem md,
  AR_laws decodesegs0 B ->
  cp_core B MT cx res mode nch ns ly S W regs mem md ->
  spZ regs = d_sp1 cx /\ (d_sp1 cx - d_sp0 cx) mod 16 = 0 /\
  alloc_ceiling + 32000 <= d_sp1 cx /\ d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 /\ d_sp0 cx <= 2 ^ 47 /\
  d_sp0 cx - DEC_LLVMF_STK + 4096 <= d_sp1 cx /\
  In (res, dec_a_len (d_n cx)) (ablocks B ly S) /\
  4096 <= res /\ res + req_size (dec_a_len (d_n cx)) <= alloc_ceiling /\
  0 <= dec_a_len (d_n cx) <= req_size (dec_a_len (d_n cx)).
Proof.
intros cx res mode nch ns ly S W regs mem md LAWS HCORE.
pose proof HCORE as (HC & Hbl & _).
pose proof HC as (HJ & _ & _ & _ & Hsp & Hsp1r & Hsp1a & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_val as Hac.
assert (Hinr : In (res, dec_a_len (d_n cx)) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (_ & Hr4096 & Hrceil & _).
assert (Hl0 : 0 <= dec_a_len (d_n cx)) by (unfold dec_a_len; lia).
assert (Hreq : dec_a_len (d_n cx) <= req_size (dec_a_len (d_n cx)))
  by (unfold req_size; destruct (Z.eqb_spec (dec_a_len (d_n cx)) 0); lia).
assert (H16 : d_sp1 cx mod 16 = 0).
{ pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D. rewrite Hsp1a, Z.add_0_r in D. rewrite D.
  replace (32 * (d_sp1 cx / 32)) with ((2 * (d_sp1 cx / 32)) * 16) by lia. apply Z.mod_mul. lia. }
unfold DEC_LLVMF_STK in *.
split; [exact Hsp|].
split; [rewrite Zminus_mod, H16, Hsp0a; reflexivity|].
split; [clear - Hsp1r Hceil Hslo Hac; lia|].
split; [exact Hsp1r|].
split; [clear - Hshi H47; lia|].
split; [clear - Hsp1r; lia|].
split; [exact Hinr|].
split; [exact Hr4096|]. split; [exact Hrceil|].
split; [exact Hl0 | exact Hreq].
Qed.

(* ------------------------------------------------------------------ *)
(* reac_frame_clean_len's two read-only words                          *)
(* ------------------------------------------------------------------ *)

(* A run of view bytes, read raw (Mem.bytes_at). *)
Lemma cp_view_bytes : forall (W : world decodesegs0) mem a (bs : list byte),
  (forall i, (i < length bs)%nat ->
     aview decodesegs0 (w_H W) mem (a + Z.of_nat i) = Some (bv_unsigned (nth i bs (Z_to_bv 8 0)))) ->
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  DMem.bytes_at decodesegs0 mem a bs.
Proof.
intros W mem a bs HV H0 Ht. split; [exact H0|]. split; [exact Ht|]. intros i Hi.
destruct (dec_leafb_mrd_aview W mem _ _ (HV i Hi)) as (b & Hb & Hbv).
rewrite Hb, (nth_error_nth' bs (Z_to_bv 8 0) Hi). f_equal. apply bv_eq. exact Hbv.
Qed.

(* The DEC_RO_RD bytes still show the image's read-only bytes: the entry's rom_view (dec_a_rom) carried by the
   journal's image clause, which dec_ro_rd_scoped keeps off the owned statics and errno (cp_rom_div's argument). *)
Lemma cp_ro_kept : forall (cx : dctx) own ly' S' (W' : world decodesegs0) mem' md' k,
  dec_ro_rd_unowned B -> dec_rom_no_errno B -> dec_a_rom cx ->
  @ajournal rc dec_A_sink_head decodesegs0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) own ly' S' W' mem' md' k ->
  forall a, dec_in_ro_rd a ->
    aview decodesegs0 (w_H W') mem' a =
    option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom decodesegs0 (Z_to_bv 64 a)).
Proof.
intros cx own ly' S' W' mem' md' k HROS HRNE HROM HJ a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _).
destruct (dec_ro_rd_scoped B HROS HRNE a Ha) as [Hown Herr].
destruct (dec_ro_rd_rom_clean a Ha) as [Hrom _].
rewrite (G3 a).
- exact (HROM a Hrom).
- destruct Hrom as (sg & Hin & _ & Hlo). exists sg. split; [exact Hin | lia].
- exact Hown.
- exact Herr.
- apply fp_spares_closed. intros (r & Hr & _). destruct Hr.
Qed.

(* The two div-36 words at A_M / A_T, raw, as the leaf reads them. *)
Lemma cp_clean_bytes : forall (W : world decodesegs0) mem,
  (forall a, dec_in_ro_rd a ->
     aview decodesegs0 (w_H W) mem a =
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom decodesegs0 (Z_to_bv 64 a))) ->
  DMem.bytes_at decodesegs0 mem CCL.A_M (DMem.le8 (Z_to_bv 64 CCL.KM)) /\
  DMem.bytes_at decodesegs0 mem CCL.A_T (DMem.le8 (Z_to_bv 64 CCL.KT)).
Proof.
intros W mem HK. split.
- apply (cp_view_bytes W); [| unfold CCL.A_M; lia | rewrite DMem.length_le8; unfold CCL.A_M; lia].
  intros i Hi. rewrite DMem.length_le8 in Hi. rewrite HK.
  + clear - Hi. do 8 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
  + unfold dec_in_ro_rd, DEC_RO_RD. apply Exists_cons_hd. unfold in_zr, CCL.A_M. cbn [fst snd]. lia.
- apply (cp_view_bytes W); [| unfold CCL.A_T; lia | rewrite DMem.length_le8; unfold CCL.A_T; lia].
  intros i Hi. rewrite DMem.length_le8 in Hi. rewrite HK.
  + clear - Hi. do 8 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
  + unfold dec_in_ro_rd, DEC_RO_RD. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
    unfold in_zr, CCL.A_T. cbn [fst snd]. lia.
Qed.

(* Image bytes are never hidden (the world's w_Hoff), so the leaf's footprint may read A_M and A_T. *)
Lemma cp_rng_img : forall (W : world decodesegs0) a, a = CCL.A_M \/ a = CCL.A_T ->
  DExecF.rng (LKit.RNG_W (world decodesegs0) (@w_H decodesegs0) W) a 8.
Proof.
intros W a Ha.
assert (Hb : 0 <= a /\ a + 8 <= 2 ^ 64) by (destruct Ha as [-> | ->]; unfold CCL.A_M, CCL.A_T; lia).
apply (dec_leafb_rng W); [lia | lia |].
intros x Hx. replace x with (a + (x - a)) by lia.
apply (dec_leafb_covers_visible (w_H W) a 8); [exact (w_Hoff W) | | lia | lia].
destruct Ha as [-> | ->]; vm_compute; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The two calls                                                        *)
(* ------------------------------------------------------------------ *)

Lemma cp_call_isreac : cp_call_isreac_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold cp_call_isreac_stmt.
intros LAWS HCELLS LEAF cx res mode nch ns a1v retpc W c HB Ha1v Hretpc HAT.
destruct HAT as (fx' & ly' & S' & regs' & mem' & md' & -> & Hfrm & HCORE & (HRM & R10 & R11 & R1) & HFILL).
pose proof (cp_ret_ok retpc ltac:(destruct Hretpc as [-> | ->]; [left | right; left]; reflexivity)) as Hrok.
clear Hretpc.
pose proof HCORE as (HC & _).
pose proof HC as (HJ & _ & _ & _ & _ & _ & _ & Hgp & Htp & _).
pose proof HJ as (HAR & _).
destruct (cp_geom cx res mode nch ns ly' S' W regs' mem' md' LAWS HCORE)
  as (HSP & Ho16 & G1 & G2 & G3 & G4 & Hinr & Hr4096 & Hrceil & Hreq).
pose proof alloc_ceiling_val as Hac.
pose proof (cp_base_len cx HB) as Hlen.
pose proof (cp_body_len cx Hlen) as Hblen.
assert (Ha1b : 0 <= a1v <= dec_a_len (d_n cx)) by (destruct Ha1v as [-> | ->]; lia).
assert (Ha1 : 14 <= a1v -> 14 <= dec_a_len (d_n cx)) by (intros H; destruct Ha1v as [-> | ->]; lia).
clear Ha1v.
assert (A0 : bv_unsigned (YK11.getr regs' (Z_to_bv 5 10)) = res).
{ assert (E : YK11.getr regs' (Z_to_bv 5 10) = w64 res) by exact R10. rewrite E. unfold w64.
  apply unsigned_lit_small. clear - Hr4096 Hrceil Hreq Hac. lia. }
assert (A1 : bv_unsigned (YK11.getr regs' (Z_to_bv 5 11)) = a1v).
{ assert (E : YK11.getr regs' (Z_to_bv 5 11) = w64 a1v) by exact R11. rewrite E. unfold w64.
  apply unsigned_lit_small. clear - Ha1b Hr4096 Hrceil Hreq Hac. lia. }
assert (SP : bv_unsigned (YK11.getr regs' (Z_to_bv 5 2)) = d_sp1 cx) by exact HSP.
assert (Psp : spZ regs' = d_sp0 cx + (d_sp1 cx - d_sp0 cx)) by (rewrite HSP; ring).
assert (HPC : decode_sigma DS_reac_frame_is_reac = CIR.REAC_FRAME_IS_REAC) by (vm_compute; reflexivity).
rewrite HPC.
eapply SRr_mono.
{ refine (@dec_leafb_journal fx' rc dec_A_sink_head B LAWS W regs' mem' DEC_LLVMF_STK (d_sp0 cx) []
    (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' md' dec_ev_234
    (d_sp1 cx - d_sp0 cx) CIR.REAC_FRAME_IS_REAC
    (Some (CIR.is_reac_result (bv_unsigned (YK11.getr regs' (Z_to_bv 5 10)))
                              (bv_unsigned (YK11.getr regs' (Z_to_bv 5 11))) (d_body cx)))
    [] (fun _ => True) HJ Psp Ho16 _ _ _ Hgp Htp _ _).
  - clear - G2. lia.
  - unfold ESTACK, DEC_LLVMF_STK. clear - G2. lia.
  - pose proof Hrok as H. rewrite <- R1 in H. exact H.
  - intros a Ha. inversion Ha.
  - intros HPRE.
    refine (LEAF fx' ly' S' W regs' mem' md' (d_body cx) (d_sp1 cx - 16) HPRE _ _ _ _ _ _ _ _);
      unfold CIR.REAC_FRAME_IS_REAC_FRAME; rewrite ?SP, ?A0, ?A1.
    + eapply (dec_leafb_stk_journal (SK := dec_A_sink_head)); [exact HJ | | ];
        unfold DEC_LLVMF_STK in *; clear - G2 G4; lia.
    + lia.
    + intros _ H14. pose proof (Ha1 H14) as H14l.
      split; [clear - Hblen H14l; lia|].
      split; [apply (dec_leafb_bytes_garr8 W mem' res (d_body cx) HFILL); clear - Hblen Hr4096 Hrceil Hreq Hac; lia|].
      split; [unfold DKA.off_stk; rewrite SP; left; clear - Hrceil Hreq H14l G1; lia|].
      split; [apply dec_leafb_app_stack; clear - G1 G2 G3 Hac; lia|].
      split; [apply dec_leafb_app_stack; clear - G1 G2 G3 Hac; lia|].
      split; [exact (dec_leafb_asan_cells B HCELLS ly' S' W mem' md' HAR)|].
      split; [unfold DKA.off_stk, DCells.GOT_CELL_K; rewrite SP; left; clear - G1 Hac; lia|].
      split; [unfold DKA.off_stk, DCells.CELL_K; rewrite SP; left; clear - G1 Hac; lia|].
      apply (dec_leafb_addressable_block B LAWS ly' S' W mem' md' res (dec_a_len (d_n cx)));
        [exact HAR | exact Hinr | lia | lia | clear - Hreq H14l; lia].
    + eapply (dec_leafb_rng_journal (SK := dec_A_sink_head)); [exact HJ | | ];
        unfold DEC_LLVMF_STK in *; clear - G2 G4; lia.
    + intros _ _. exact (proj1 (dec_leafb_rng_cells W)).
    + intros _ _. exact (proj2 (dec_leafb_rng_cells W)).
    + intros _ H14. pose proof (Ha1 H14) as H14l.
      apply (dec_leafb_rng_block B LAWS ly' S' W mem' md' res (dec_a_len (d_n cx)));
        [exact HAR | exact Hinr | lia | clear - Hreq H14l; lia].
    + intros _ H14. pose proof (Ha1 H14) as H14l.
      apply (dec_leafb_rng_shadow_block B LAWS ly' S' W mem' md' res (dec_a_len (d_n cx)));
        [exact HAR | exact Hinr | lia | lia | clear - Hreq H14l; lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HRES & HK & _ & _).
unfold cp_st, cp_at.
exists fx', ly', S', regs2, mem2, md2.
split.
{ lazymatch goal with |- mkCfg (YK11.mkst _ ?x _ _) _ = _ =>
    replace x with (w64 (DEC_A_LLVMF + retpc)) by first [exact R1 | exact (eq_sym R1)] end.
  reflexivity. }
split; [exact Hfrm|].
split.
{ apply (cp_core_regs B MT cx res mode nch ns ly' S' W regs' regs2 mem2 md2); [|exact HP].
  apply (cp_core_kept B MT cx res mode nch ns ly' S' W regs' mem' md' mem2 md2 LAWS HCELLS Hlen HCORE HJ2).
  intros a Ha _ Hw. apply HK; [exact Ha | | intros Hx; inversion Hx].
  rewrite HSP. unfold ESTACK. intros Hx. apply Hw. clear - Hx. lia. }
split.
{ split; [exact (cp_rm_regs mode regs' regs2 HRM HP)|].
  pose proof (HRES _ eq_refl) as H10. rewrite A0, A1 in H10. exact H10. }
unfold cp_filled.
apply (cp_garr8_kept (w_H W) (w_H W) mem' mem2 res (cp_body cx)); [|exact HFILL].
intros j Hj. unfold cp_body in Hj. rewrite length_map, Hblen in Hj.
apply HK; [clear - Hj Hr4096 Hrceil Hreq Hac; lia | | intros Hx; inversion Hx].
rewrite HSP. unfold ESTACK. clear - Hj Hrceil Hreq G1. lia.
Qed.

Lemma cp_call_clean : cp_call_clean_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold cp_call_clean_stmt.
intros LAWS HCELLS HROS HRNE LEAF cx res mode nch ns W c HB HROM HAT.
destruct HAT as (fx' & ly' & S' & regs' & mem' & md' & -> & Hfrm & HCORE & (HRM & R10 & R1) & HFILL).
pose proof (cp_ret_ok 0x2c4 ltac:(right; right; reflexivity)) as Hrok.
pose proof HCORE as (HC & _).
pose proof HC as (HJ & _ & _ & _ & _ & _ & _ & Hgp & Htp & _).
destruct (cp_geom cx res mode nch ns ly' S' W regs' mem' md' LAWS HCORE)
  as (HSP & Ho16 & G1 & G2 & G3 & G4 & Hinr & Hr4096 & Hrceil & Hreq).
pose proof alloc_ceiling_val as Hac.
pose proof (cp_base_len cx HB) as Hlen.
assert (A0 : bv_unsigned (YK11.getr regs' (Z_to_bv 5 10)) = dec_a_len (d_n cx)).
{ assert (E : YK11.getr regs' (Z_to_bv 5 10) = w64 (dec_a_len (d_n cx))) by exact R10. rewrite E. unfold w64.
  apply unsigned_lit_small. clear - Hr4096 Hrceil Hreq Hac. lia. }
destruct (cp_clean_bytes W mem' (cp_ro_kept cx _ _ _ _ _ _ _ HROS HRNE HROM HJ)) as (HM & HT).
assert (Psp : spZ regs' = d_sp0 cx + (d_sp1 cx - d_sp0 cx)) by (rewrite HSP; ring).
assert (HPC : decode_sigma DS_reac_frame_clean_len = CCL.REAC_FRAME_CLEAN_LEN) by (vm_compute; reflexivity).
rewrite HPC.
eapply SRr_mono.
{ refine (@dec_leafb_journal fx' rc dec_A_sink_head B LAWS W regs' mem' DEC_LLVMF_STK (d_sp0 cx) []
    (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' md' dec_ev_234
    (d_sp1 cx - d_sp0 cx) CCL.REAC_FRAME_CLEAN_LEN
    (Some (CCL.reac_frame_clean_len_model (bv_unsigned (YK11.getr regs' (Z_to_bv 5 10)))))
    [] (fun m2 => m2 = mem') HJ Psp Ho16 _ _ _ Hgp Htp _ _).
  - clear - G2. lia.
  - unfold ESTACK, DEC_LLVMF_STK. clear - G2. lia.
  - pose proof Hrok as H. rewrite <- R1 in H. exact H.
  - intros a Ha. inversion Ha.
  - intros HPRE.
    exact (LEAF fx' ly' S' W regs' mem' md' HPRE HM HT (cp_rng_img W _ (or_introl eq_refl))
             (cp_rng_img W _ (or_intror eq_refl))). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HRES & _ & _ & ->).
unfold cp_st, cp_at.
exists fx', ly', S', regs2, mem', md2.
split.
{ lazymatch goal with |- mkCfg (YK11.mkst _ ?x _ _) _ = _ =>
    replace x with (w64 (DEC_A_LLVMF + 0x2c4)) by first [exact R1 | exact (eq_sym R1)] end.
  reflexivity. }
split; [exact Hfrm|].
split.
{ apply (cp_core_regs B MT cx res mode nch ns ly' S' W regs' regs2 mem' md2); [|exact HP].
  apply (cp_core_kept B MT cx res mode nch ns ly' S' W regs' mem' md' mem' md2 LAWS HCELLS Hlen HCORE HJ2).
  intros a _ _ _. reflexivity. }
split.
{ split; [exact (cp_rm_regs mode regs' regs2 HRM HP)|].
  pose proof (HRES _ eq_refl) as H10. rewrite A0 in H10. exact H10. }
exact HFILL.
Qed.

End seg.

(* ------------------------------------------------------------------ *)
(* 4. malloc #2 at +0x3bc                                              *)
(* ------------------------------------------------------------------ *)

Section seg.
Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable asink_img_laws : list Segment -> asyms -> asink_syms -> Prop.
Variable ro_below_ofl : list Segment -> Z -> Z -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
#[local] Notation SEGS := (@pa_segs _ decode_listing (@PI_decode _)).
#[local] Notation VAL := (@pa_val _ decode_listing (@PI_decode _)).

Local Abbreviation dbase :=
  (@dec_a_base rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI).

(* ------------------------------------------------------------------ *)
(* 1. dec_a_base's fields, read by type (the e_base lemmas of seg_early.v) *)
(* ------------------------------------------------------------------ *)

Lemma cp_m_base_pn : forall cx, dbase cx ->
  (d_n cx = 0 /\ d_p cx = A_EMPTY) \/ (0 < d_n cx < 2 ^ 26 /\ In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))).
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma cp_m_base_afn : forall cx, dbase cx ->
  @afn_pre rc decodesegs0 B DEC_LLVMF_STK (d_ly cx) (d_S cx) (d_W cx) (d_regs cx) (d_mem cx) (d_md cx) [].
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma cp_m_base_ra : forall cx, dbase cx -> raZ (d_regs cx) = RA_LLVMF.
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma cp_m_base_len : forall cx, dbase cx -> d_n cx = Z.of_nat (length (d_pl cx)).
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma cp_m_base_garr : forall cx, dbase cx ->
  garr8 decodesegs0 (mrestrict (w_H (d_W cx)) (d_mem cx)) (d_p cx) (map (fun b : byte => bv_unsigned b) (d_pl cx)).
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma cp_m_base_nev : forall cx, dbase cx -> st_nev (d_S cx) + DEC_EV_LIB <= EV_MAX.
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma cp_m_base_bb : forall cx, dbase cx -> blocks_bytes (d_S cx) + DEC_LIVE_LIB <= LIVE_MAX.
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
(* The fields of afn_pre (lib/Reusable/YCbq.v:336), found by type. *)
Lemma cp_m_afn_stk : forall ly S W regs mem md ch, @afn_pre rc decodesegs0 B DEC_LLVMF_STK ly S W regs mem md ch ->
  astk_ok DEC_LLVMF_STK ly (spZ regs).
Proof. intros ly S W regs mem md ch H. unfold afn_pre in H. decompose [and] H. assumption. Qed.
Lemma cp_m_afn_ra4 : forall ly S W regs mem md ch, @afn_pre rc decodesegs0 B DEC_LLVMF_STK ly S W regs mem md ch ->
  4096 <= raZ regs.
Proof. intros ly S W regs mem md ch H. unfold afn_pre in H. decompose [and] H. assumption. Qed.
Lemma cp_m_afn_chain : forall ly S W regs mem md ch, @afn_pre rc decodesegs0 B DEC_LLVMF_STK ly S W regs mem md ch ->
  achain ly (aview decodesegs0 (w_H W) mem) (spZ regs) (s0Z regs) ch.
Proof. intros ly S W regs mem md ch H. unfold afn_pre in H. decompose [and] H. assumption. Qed.

Lemma cp_m_bv_small : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.
Lemma cp_m_ra3c0 : 4096 <= DEC_A_LLVMF + 0x3c0 < 2 ^ 40.
Proof. unfold DEC_A_LLVMF, decode_text, AF_LLVMFuzzerTestOneInput. lia. Qed.
(* What the rest of the walk spends from +0x3c0 on is not negative. *)
Lemma cp_m_rest_nonneg : ameter_laws MT -> 0 <= dec_rest_3c0 MT.
Proof.
intros MTL. unfold dec_rest_3c0, dec_rest_4fc, dec_rest_5fc, dec_rest_748, dec_rest_86c, dec_crt_cost_max.
pose proof (mo_malloc_nonneg MT MTL 1440 ltac:(lia)).
pose proof (mo_malloc_nonneg MT MTL 1920 ltac:(lia)). pose proof (mo_malloc_nonneg MT MTL 1016 ltac:(lia)).
pose proof (mo_free_nonneg MT MTL). lia.
Qed.
(* The output length malloc #2 asks for: 1 <= olen <= 48387 (lib/U/Prog/fd_down.v:25). *)
Lemma cp_m_olen : forall nch ns, -128 <= nch <= 127 -> -128 <= ns <= 127 -> 1 <= dec_a_olen nch ns <= 48387.
Proof.
intros nch ns Hc Hs. unfold dec_a_olen.
destruct (Z.ltb_spec 0 nch) as [H1|H1]; destruct (Z.ltb_spec 0 ns) as [H2|H2]; cbn [andb]; [nia | lia | lia | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The call trace at +0x3bc (seg_early.v e_trace, at ra = +0x3c0)   *)
(* ------------------------------------------------------------------ *)

Lemma cp_m_trace : forall (HUTR : dec_llvmf_utraces RA_LLVMF B) cx lyT ST W regsT memT mdT k,
  dbase cx -> dec_a_core B cx lyT ST W regsT memT mdT k ->
  YK11.getr regsT 1 = w64 (DEC_A_LLVMF + 0x3c0) ->
  exists ch, chain_pre lyT (aview decodesegs0 (w_H W) memT) regsT ch /\
             In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B).
Proof.
intros HUTR cx lyT ST W regsT memT mdT k HB HC R1.
destruct HC as (HJ & _ & R8 & _ & Hsp & Hsp1r & Hsp1a & _ & _ & Hsaved & _).
pose proof (cp_m_base_ra cx HB) as Hra. pose proof (cp_m_base_afn cx HB) as HAFN.
pose proof (cp_m_afn_ra4 _ _ _ _ _ _ _ HAFN) as Hra4. pose proof (cp_m_afn_stk _ _ _ _ _ _ _ HAFN) as Hstk.
pose proof (cp_m_afn_chain _ _ _ _ _ _ _ HAFN) as Hch.
pose proof Hstk as (Hsp0a & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold DEC_LLVMF_STK in *.
pose proof HJ as (_ & Hly & _).
assert (Etop : ly_top lyT = ly_top (d_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
pose proof cp_m_ra3c0 as HRA.
assert (Hraz : raZ regsT = DEC_A_LLVMF + 0x3c0) by (unfold raZ; rewrite R1; apply cp_m_bv_small; lia).
assert (Hs0z : s0Z regsT = d_sp0 cx) by (unfold s0Z; rewrite R8; apply cp_m_bv_small; unfold d_sp0; lia).
unfold dec_a_saved, dec_a_saved_at in Hsaved.
apply Forall_cons_iff in Hsaved as [S1 Hsaved]. apply Forall_cons_iff in Hsaved as [S8 _]. cbn [fst snd] in S1, S8.
assert (EU : forall sp, In sp [[]; [RA_LLVMF]] ->
  In (dec_utrace (pc_malloc_ra0 (as_code B)) ((DEC_A_LLVMF + 0x3c0) :: sp)) (as_universe B)).
{ intros sp Hsp'. apply (proj1 (HUTR sp Hsp')). unfold DEC_LLVMF_RA_MALLOC. cbn [map In]. right. left. reflexivity. }
unfold d_sp0 in *.
destruct (Z_lt_ge_dec (spZ (d_regs cx)) (ly_top (d_ly cx) - 16)) as [Hlt | Hge].
- exists [(spZ (d_regs cx), RA_LLVMF, s0Z (d_regs cx))]. split.
  + unfold chain_pre. split; [rewrite Hraz; lia|].
    unfold frame0_ok. rewrite Hsp, Etop.
    replace (d_sp1 cx + 16 <? ly_top (d_ly cx)) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold bad_next. rewrite Hs0z.
    replace ((spZ (d_regs cx) <=? d_sp1 cx) || (ly_top (d_ly cx) - 16 <=? spZ (d_regs cx)) ||
             negb (spZ (d_regs cx) mod 8 =? 0))%bool with false.
    2: { symmetry. apply orb_false_intro; [apply orb_false_intro|].
         - apply Z.leb_gt. lia. - apply Z.leb_gt. lia.
         - apply negb_false_iff. apply Z.eqb_eq. pose proof (Z.div_mod (spZ (d_regs cx)) 16 ltac:(lia)) as D. rewrite Hsp0a in D.
           Z.div_mod_to_equations. lia. }
    split; [lia|]. cbn [fpchain].
    split; [reflexivity|].
    split; [pose proof (Z.div_mod (spZ (d_regs cx)) 16 ltac:(lia)) as D; rewrite Hsp0a in D; Z.div_mod_to_equations; lia|].
    split; [rewrite S1; f_equal; exact Hra|]. split; [exact S8|]. split; [rewrite <- Hra; exact Hra4|].
    destruct Hch as [(Hbad & _) | (Hv1 & Hv2 & Hv3 & Hfp & _)].
    * unfold bad_next. replace ((s0Z (d_regs cx) <=? spZ (d_regs cx)) || (ly_top (d_ly cx) - 16 <=? s0Z (d_regs cx)) ||
        negb (s0Z (d_regs cx) mod 8 =? 0))%bool with true; [reflexivity|].
      symmetry. destruct Hbad as [Hb | [Hb | Hb]].
      -- apply orb_true_intro. left. apply orb_true_intro. left. apply Z.leb_le. lia.
      -- apply orb_true_intro. left. apply orb_true_intro. right. apply Z.leb_le. lia.
      -- apply orb_true_intro. right. apply negb_true_iff. apply Z.eqb_neq. exact Hb.
    * unfold bad_next. replace ((s0Z (d_regs cx) <=? spZ (d_regs cx)) || (ly_top (d_ly cx) - 16 <=? s0Z (d_regs cx)) ||
        negb (s0Z (d_regs cx) mod 8 =? 0))%bool with false.
      2: { symmetry. apply orb_false_intro; [apply orb_false_intro|].
           - apply Z.leb_gt. lia. - apply Z.leb_gt. lia. - apply negb_false_iff. apply Z.eqb_eq. exact Hv3. }
      cbn [fpchain] in Hfp |- *. destruct Hfp as (r & Hr & Hr4). exists r. split; [|exact Hr4].
      rewrite <- Hr. apply rdword_ext. intros j Hj.
      apply (@aview_above_of_journal rc dec_A_sink_head decode_listing PI_decode B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
      lia.
  + unfold call_trace0, unwind_of_chain. rewrite Hraz.
    pose proof (EU [RA_LLVMF] ltac:(cp_in)) as EU1. unfold dec_utrace in EU1. cbn [flat_map app] in EU1 |- *.
    exact EU1.
- exists []. split.
  + unfold chain_pre. split; [rewrite Hraz; lia|].
    unfold frame0_ok. rewrite Hsp, Etop.
    replace (d_sp1 cx + 16 <? ly_top (d_ly cx)) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold bad_next. rewrite Hs0z.
    replace ((spZ (d_regs cx) <=? d_sp1 cx) || (ly_top (d_ly cx) - 16 <=? spZ (d_regs cx)) ||
             negb (spZ (d_regs cx) mod 8 =? 0))%bool with true; [reflexivity|].
    symmetry. apply orb_true_intro. left. apply orb_true_intro. right. apply Z.leb_le. lia.
  + unfold call_trace0, unwind_of_chain. rewrite Hraz.
    pose proof (EU [] ltac:(cp_in)) as EU0. unfold dec_utrace in EU0. cbn [flat_map app] in EU0 |- *.
    exact EU0.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The mode across the call                                          *)
(* ------------------------------------------------------------------ *)

(* dec_a_mode_ok across a call: a table mode through its pointer row (AR's am_const at both states) and the table
   words through the read-only view at both states (dec_rom_view_rd: they are DEC_RO_RD bytes, cp_tbl_ro_rd); the
   frame-local mode through the fake frame's bytes. *)
Lemma cp_m_mode_kept : forall (cx : dctx) ly S (W : world decodesegs0) mem md ly2 S2 (W2 : world decodesegs0) mem2 md2
    (mode nch ns : Z),
  dec_crt_cells B -> AR decodesegs0 B ly S W mem md -> AR decodesegs0 B ly2 S2 W2 mem2 md2 ->
  dec_rom_view_rd W mem -> dec_rom_view_rd W2 mem2 ->
  (forall a, d_F cx <= a < d_F cx + 64 -> aview decodesegs0 (w_H W2) mem2 a = aview decodesegs0 (w_H W) mem a) ->
  dec_a_mode_ok cx W mem mode nch ns -> dec_a_mode_ok cx W2 mem2 mode nch ns.
Proof.
intros cx ly S W mem md ly2 S2 W2 mem2 md2 mode nch ns HC HAR HAR2 ROV1 ROV2 KF (Hwhich & Hnch & Hns & V4 & V8).
assert (Hw : forall a v, In (z8 (ANum a) v) (as_const B ly) -> In (z8 (ANum a) v) (as_const B ly2) -> 0 <= v < 2 ^ 64 ->
  rdword (aview decodesegs0 (w_H W) mem) a = Some v /\ rdword (aview decodesegs0 (w_H W2) mem2) a = Some v).
{ intros a v I1 I2 Hv. destruct HAR as (M1 & _). destruct HAR2 as (M2 & _). split.
  - exact (rdword_cell B ly _ a v Hv (proj1 (Forall_forall _ _) (am_const _ _ _ _ M1) _ I1)).
  - exact (rdword_cell B ly2 _ a v Hv (proj1 (Forall_forall _ _) (am_const _ _ _ _ M2) _ I2)). }
assert (TBL : forall k, In k [4; 5; 6]%nat -> rdword (aview decodesegs0 (w_H W) mem) (decode_obj k) = Some mode ->
  dec_a_mode_ok cx W2 mem2 mode nch ns).
{ intros k Hk Hc.
  destruct (Hw _ _ (cp_m_ptr B HC ly k Hk) (cp_m_ptr B HC ly2 k Hk) (cp_m_tbl_range k Hk)) as (E1 & E2).
  rewrite E1 in Hc. injection Hc as <-.
  split; [cbn [In] in Hk; destruct Hk as [<- | [<- | [<- | []]]]; [left | right; left | right; right; left]; exact E2|].
  split; [exact Hnch|]. split; [exact Hns|].
  split; (eapply cp_val_mem_moved; [|eassumption]); intros j Hj; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj;
    lazymatch goal with |- aview _ _ _ ?x = _ =>
      rewrite (ROV2 x (cp_tbl_ro_rd k Hk x ltac:(lia))), (ROV1 x (cp_tbl_ro_rd k Hk x ltac:(lia))); reflexivity end. }
destruct Hwhich as [Hc | [Hc | [Hc | Hloc]]].
- exact (TBL 4%nat ltac:(cp_in) Hc).
- exact (TBL 5%nat ltac:(cp_in) Hc).
- exact (TBL 6%nat ltac:(cp_in) Hc).
- split; [right; right; right; exact Hloc|]. split; [exact Hnch|]. split; [exact Hns|].
  subst mode.
  split; (eapply cp_val_mem_moved; [|eassumption]); intros j Hj; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj;
    apply KF; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. malloc #2 at +0x3bc                                               *)
(* ------------------------------------------------------------------ *)

(* malloc (olen) by amalloc04_rule through YC85.v:191 amalloc04_sub, as seg_early.v e_call does malloc #1. The call
   keeps every byte llvm_a_st_3c0 reads: the saved words and the spill slots lie above sp (acall_kept's first
   clause), the copy is a block of the state (its second), the fake frame and its shadow are the state's own frame
   (its fourth); the payload comes from the entry by the journal's block clause, a table mode by its pointer row and
   the read-only view of the table words at both states (cp_ro_kept). *)
Lemma cp_call_malloc2 : cp_call_malloc2_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold cp_call_malloc2_stmt.
intros HPCM HUTR HCELLS HROS HRNE LAWS MTL AM cx res mode nch ns W c HB HR HAT.
destruct HAT as (fx' & ly' & S' & regs' & mem' & md' & -> & Hfrm & HCORE & (R10 & R1 & R24 & R25 & R23) &
  (HFILL & S32 & S48 & S64 & S80 & S88)).
rewrite <- HPCM.
pose proof HCORE as (HC & Hbl & Hres & Hmle & Hmok & (R19 & R21 & R27) & R18 & R20 & R22 & R26 & HMODE & HFSH & HSLOT).
pose proof HC as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1a & Hgp & Htp & Hsaved & HF4 & HFa & HFp & HFL & Hblk & Hga).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0a & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cp_m_base_pn cx HB) as Hpn. pose proof (cp_m_base_len cx HB) as Hlen.
pose proof (cp_m_base_garr cx HB) as Hgarr.
pose proof (cp_m_base_nev cx HB) as Hnev0. pose proof (cp_m_base_bb cx HB) as Hbb.
pose proof HMODE as (_ & Hnch & Hns & _ & _).
pose proof (cp_m_olen nch ns Hnch Hns) as Holen.
assert (Hn26 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
assert (Hlen0 : 0 <= dec_a_len (d_n cx) <= d_n cx) by (unfold dec_a_len; lia).
pose proof (cp_m_rest_nonneg MTL) as Hrest.
pose proof (mo_malloc_mono MT MTL (dec_a_olen nch ns) 48387 ltac:(lia)) as Hmono.
unfold DEC_LLVMF_STK in *.
assert (Hsp016 : (d_sp1 cx - d_sp0 cx) mod 16 = 0).
{ pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D1. pose proof (Z.div_mod (d_sp0 cx) 16 ltac:(lia)) as D2.
  unfold d_sp0 in *. rewrite Hsp1a in D1. rewrite Hsp0a in D2.
  replace (d_sp1 cx - spZ (d_regs cx)) with ((2 * (d_sp1 cx / 32) - spZ (d_regs cx) / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
destruct (cp_m_trace HUTR cx ly' S' W regs' mem' md' dec_ev_234 HB HC R1) as (ch & Hch & Htr).
eapply SRr_mono.
{ eapply (amalloc04_sub (SK := dec_A_sink_head) decodesegs0 B LAWS decode_segs_low MT (AM fx') W regs' mem' 32768
    (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' md' dec_ev_234
    (dec_a_olen nch ns) (d_sp1 cx - d_sp0 cx) (w64 (DEC_A_LLVMF + 0x3c0)) ch HJ R10).
  - unfold MALLOC_MAX. lia.
  - rewrite (blocks_bytes_bsum B ly' S'), Hbl, bsum_app, bsum_cons, <- (blocks_bytes_bsum B (d_ly cx) (d_S cx)).
    cbn [snd]. change (bsum []) with 0. unfold dec_a_len, DEC_LIVE_LIB, LIVE_MAX in *. lia.
  - lia.
  - exact Hsp016.
  - lia.
  - unfold ASTACK. lia.
  - exact Hgp.
  - exact Htp.
  - exact R1.
  - exact (@ret_ok_codeptr_v rc decode_listing PI_decode 0x3c0 ltac:(lia) eq_refl).
  - unfold dec_ev_234, DEC_EV_LIB, EV_MAX in *. lia.
  - exact Hch.
  - exact Htr.
  - apply (mo_ok_le MT MTL S' _ _ Hmok). unfold dec_rest_234. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & out & -> & HJ2 & HP2 & Hout & Hfr2 & Hout4 & Hbl2 & HK & MLE & _).
pose proof HJ2 as (HAR2 & Hly2 & _).
pose proof HK as (HK1 & HK2 & HK3 & HK4 & HK5 & HK6).
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S')) by (rewrite Hfrs; left; reflexivity).
assert (Hin2 : In (DEC_FCLASS, d_fpos cx) (frames S2)) by (rewrite Hfr2; exact Hin0).
assert (EFT : frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (EF2 : frame_addr ly2 DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly2 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Houtin : In (out, dec_a_olen nch ns) (ablocks B ly2 S2))
  by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Houtin) as (_ & _ & Houtc & Houtapp & _).
pose proof (sep_block_frame decodesegs0 B LAWS ly2 S2 W2 mem2 md2 _ _ _ _ HAR2 Houtin Hin2) as Hdisj.
rewrite EF2 in Hdisj. replace (fs_frame_bytes DEC_FCLASS) with 64 in Hdisj by reflexivity.
unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj.
pose proof (req_size_pos0 (dec_a_olen nch ns) ltac:(lia)) as Hrq.
(* the frame's bytes and its shadow are the call's to keep *)
assert (KF : forall a, d_F cx <= a < d_F cx + 64 -> aview decodesegs0 (w_H W2) mem2 a = aview decodesegs0 (w_H W) mem' a).
{ intros a Ha. apply (HK4 DEC_FCLASS (d_fpos cx) a Hin0).
  - left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFT.
    replace (fs_frame_bytes DEC_FCLASS) with 64 by reflexivity. lia.
  - intros Hx. cbv beta in Hx. lia. }
destruct (frames_bounds decodesegs0 B LAWS ly' S' W mem' md' _ _ HAR Hin0) as (_ & HFc & _).
rewrite EFT in HFc. replace (fs_frame_bytes DEC_FCLASS) with 64 in HFc by reflexivity.
assert (KS : forall a, d_SH cx <= a < d_SH cx + 8 -> aview decodesegs0 (w_H W2) mem2 a = aview decodesegs0 (w_H W) mem' a).
{ intros a Ha. apply (HK4 DEC_FCLASS (d_fpos cx) a Hin0).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFT. replace (fs_frame_bytes DEC_FCLASS / 8) with 8 by reflexivity.
    unfold d_SH in Ha. lia.
  - intros Hx. cbv beta in Hx.
    pose proof (Z.div_pos (d_F cx) 8 ltac:(lia) ltac:(lia)) as HFd.
    assert (HFd2 : 8 * (d_F cx / 8) <= d_F cx) by (apply Z.mul_div_le; lia).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Houtapp.
    unfold d_SH, shadow_addr, SHADOW_OFF in Ha. lia. }
assert (KA : forall a, d_sp1 cx <= a < 2 ^ 64 -> aview decodesegs0 (w_H W2) mem2 a = aview decodesegs0 (w_H W) mem' a).
{ intros a Ha. apply HK1; [lia | unfold ASTACK; lia]. }
(* the copy's block is the state's, apart from the new block *)
assert (Hresin : In (res, dec_a_len (d_n cx)) (ablocks B ly' S'))
  by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hdro : res + req_size (dec_a_len (d_n cx)) <= out \/ out + req_size (dec_a_olen nch ns) <= res).
{ pose proof (sep_blocks_pos decodesegs0 B LAWS ly2 S2 W2 mem2 md2 (res, dec_a_len (d_n cx)) (out, dec_a_olen nch ns)
    (ablocks B (d_ly cx) (d_S cx)) [] [] HAR2) as D.
  specialize (D ltac:(rewrite Hbl2, Hbl, <- app_assoc; reflexivity)).
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. exact D. }
assert (Hbody : Z.of_nat (length (cp_body cx)) = dec_a_len (d_n cx)).
{ clear - Hlen. unfold cp_body, d_body. rewrite length_map, length_skipn. unfold dec_a_u, dec_a_len. lia. }
assert (KR : forall j, 0 <= j < Z.of_nat (length (cp_body cx)) ->
  aview decodesegs0 (w_H W2) mem2 (res + j) = aview decodesegs0 (w_H W) mem' (res + j)).
{ intros j Hj. pose proof (req_size_pos0 (dec_a_len (d_n cx)) ltac:(lia)) as Hrql.
  apply (HK2 res (dec_a_len (d_n cx)) j Hresin); [lia|]. intros Hx. cbv beta in Hx. lia. }
assert (HRS : forall r, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)) by exact HP2.
unfold llvm_a_st_3c0.
exists fx', ly2, S2, regs2, mem2, md2, res, out, mode, nch, ns.
split; [reflexivity|].
split; [exact Hfrm|].
split.
{ split; [exact HJ2|].
  split; [rewrite Hfr2; exact Hfrs|].
  split; [exact (eq_trans (HRS 8 ltac:(unfold acallee_saved; lia)) R8)|].
  split; [exact (eq_trans (HRS 9 ltac:(unfold acallee_saved; lia)) R9)|].
  split; [unfold spZ in *; rewrite <- Hsp; f_equal; exact (HRS 2 ltac:(unfold acallee_saved; lia))|].
  split; [exact Hsp1r|]. split; [exact Hsp1a|].
  split; [exact (eq_trans (HRS 3 ltac:(unfold acallee_saved; lia)) Hgp)|].
  split; [exact (eq_trans (HRS 4 ltac:(unfold acallee_saved; lia)) Htp)|].
  split; [apply (cp_saved_kept cx (aview decodesegs0 (w_H W) mem'));
    [intros a Ha; apply KA; unfold d_sp0 in *; lia | exact Hsaved]|].
  split; [exact HF4|]. split; [exact HFa|].
  split.
  { intros a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin2) as (_ & _ & Hfp2 & _).
    rewrite EF2 in Hfp2. replace (fs_frame_bytes DEC_FCLASS) with 64 in Hfp2 by reflexivity.
    exact (proj1 (Hfp2 a Ha)). }
  split; [rewrite <- HFL; apply rdword_ext; intros j Hj; apply KF; lia|].
  split; [intros Hn0; rewrite Hbl2; apply in_or_app; left; exact (Hblk Hn0)|].
  destruct Hpn as [(Hn0 & Hp0) | (Hn0 & Hpin)].
  - rewrite Hlen in Hn0. destruct (d_pl cx); [intros j Hj; cbn in Hj; lia | cbn in Hn0; lia].
  - apply (cp_garr8_kept (w_H (d_W cx)) (w_H W2) (d_mem cx) mem2 (d_p cx) _); [| exact Hgarr].
    intros j Hj. rewrite length_map, <- Hlen in Hj.
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    pose proof (req_size_pos (d_n cx) ltac:(lia)) as Hrn.
    apply (F2 (d_p cx) (d_n cx) j Hpin);
      [rewrite Hbl2, Hbl; apply in_or_app; left; apply in_or_app; left; exact Hpin | lia | intros (rg & [] & _)]. }
split; [rewrite Hbl2, Hbl, <- app_assoc; reflexivity|].
split; [exact Hres|]. split; [exact Hout4|].
split.
{ unfold dec_spent_3c0.
  apply (mo_le_mono MT MTL _ _ (dec_spent_234 MT (d_n cx) + mo_malloc MT (dec_a_olen nch ns)));
    [apply (mo_le_trans MT MTL _ S'); [exact Hmle | exact MLE] | lia]. }
split.
{ apply (mo_ok_step MT MTL S' S2 (mo_malloc MT (dec_a_olen nch ns))); [|exact MLE].
  apply (mo_ok_le MT MTL S' _ _ Hmok). unfold dec_rest_234. lia. }
split; [split; [exact (eq_trans (HRS 19 ltac:(unfold acallee_saved; lia)) R19)|];
        split; [exact (eq_trans (HRS 21 ltac:(unfold acallee_saved; lia)) R21)|
                exact (eq_trans (HRS 27 ltac:(unfold acallee_saved; lia)) R27)]|].
split; [exact Hout|].
split; [exact (eq_trans (HRS 18 ltac:(unfold acallee_saved; lia)) R18)|].
split; [exact (eq_trans (HRS 20 ltac:(unfold acallee_saved; lia)) R20)|].
split; [exact (eq_trans (HRS 26 ltac:(unfold acallee_saved; lia)) R26)|].
split; [exact (eq_trans (HRS 24 ltac:(unfold acallee_saved; lia)) R24)|].
split; [exact (eq_trans (HRS 25 ltac:(unfold acallee_saved; lia)) R25)|].
split; [exact (eq_trans (HRS 23 ltac:(unfold acallee_saved; lia)) R23)|].
split; [exact (eq_trans (HRS 22 ltac:(unfold acallee_saved; lia)) R22)|].
split; [exact (cp_m_mode_kept cx ly' S' W mem' md' ly2 S2 W2 mem2 md2 mode nch ns HCELLS HAR HAR2
          (cp_ro_kept B cx _ _ _ _ _ _ _ HROS HRNE HR HJ) (cp_ro_kept B cx _ _ _ _ _ _ _ HROS HRNE HR HJ2) KF HMODE)|].
split; [apply (cp_fsh_kept cx (aview decodesegs0 (w_H W) mem')); [intros i Hi; apply KS; lia | exact HFSH]|].
split; [exact (cp_garr8_kept (w_H W) (w_H W2) mem' mem2 res (cp_body cx) KR HFILL)|].
split; [apply (cp_slot_kept cx (aview decodesegs0 (w_H W) mem')); [intros i Hi; apply KA; lia | exact S32]|].
split; [apply (cp_slot_kept cx (aview decodesegs0 (w_H W) mem')); [intros i Hi; apply KA; lia | exact S48]|].
split; [apply (cp_slot_kept cx (aview decodesegs0 (w_H W) mem')); [intros i Hi; apply KA; lia | exact S64]|].
split; [apply (cp_slot_kept cx (aview decodesegs0 (w_H W) mem')); [intros i Hi; apply KA; lia | exact S80]|].
split; [apply (cp_slot_kept cx (aview decodesegs0 (w_H W) mem')); [intros i Hi; apply KA; lia | exact S88]|].
apply (cp_slot_kept cx (aview decodesegs0 (w_H W) mem')); [intros i Hi; apply KA; lia | exact HSLOT].
Qed.

End seg.

(* ------------------------------------------------------------------ *)
(* 5. The symbolic runs between the calls, and the segment             *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* The entry symbolic state at +0x234                                   *)
(* ------------------------------------------------------------------ *)

(* The named slots of the environment, above the 32 registers:
   32 the shadow base (the engine's Bx), 33 the payload copy res, 34 its length, 35 the mode, 36 the fake
   frame, 37 its shadow address, 38 the body pointer p + u, 39 nch, 40 ns, 41 and 42 the two header bytes the
   is_reac check reads at res + 12 and res + 13. *)
Definition cp_frame : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 120 32 96 [YP09.mkChunk 112 (CVal 8 (SOff 36 0))].
Definition cp_mode : YP09.region :=
  YP09.mkRegion (Some 35%nat) 4 12 0 0 [YP09.mkChunk 4 (CVal 4 (SOff 39 0)); YP09.mkChunk 8 (CVal 4 (SOff 40 0))].
Definition cp_res : YP09.region :=
  YP09.mkRegion (Some 33%nat) 12 14 0 0 [YP09.mkChunk 12 (CVal 1 (SOff 41 0)); YP09.mkChunk 13 (CVal 1 (SOff 42 0))].
Definition cp_km : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 7)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit CCL.KM))].
Definition cp_kt : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 8)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit CCL.KT))].
Definition cp_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (32%nat, mkAF SB SB 0); (33%nat, mkAF 4096 (2 ^ 47 - 16) 4);
           (35%nat, mkAF 4096 (2 ^ 47 - 16) 3)] [] [].
(* The registers at +0x234 that the segment addresses through: a0 = res, s10 = len, s9 = mode, s7 = mode + 4,
   s6 = mode + 8, s2 = the shadow base, s8 = p + u, s3 = s5 = the frame. *)
Definition cp_regs0 :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set
    sr_atoms 10%bv (SOff 33 0)) 26%bv (SOff 34 0)) 25%bv (SOff 35 0)) 23%bv (SOff 35 4))
    22%bv (SOff 35 8)) 18%bv (SOff 32 0)) 24%bv (SOff 38 0)) 19%bv (SOff 36 0)) 21%bv (SOff 36 0).
(* The register map of every later point: s4 = res (from +0x238 on), a0 free. *)
Definition cp_regs1 :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set
    sr_atoms 20%bv (SOff 33 0)) 26%bv (SOff 34 0)) 25%bv (SOff 35 0)) 23%bv (SOff 35 4))
    22%bv (SOff 35 8)) 18%bv (SOff 32 0)) 19%bv (SOff 36 0)) 21%bv (SOff 36 0).


Section seg.
Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable asink_img_laws : list Segment -> asyms -> asink_syms -> Prop.
Variable ro_below_ofl : list Segment -> Z -> Z -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
#[local] Notation SEGS := (@pa_segs _ decode_listing (@PI_decode _)).
#[local] Notation VAL := (@pa_val _ decode_listing (@PI_decode _)).


(* The environment of every run: registers 0 .. 31, then the named slots of cp_extra. *)
Lemma cp_E_eqs : forall (regs : bvmap 5 word) (cx : dctx) (res mode nch ns : Z),
  let E := Eimg (Ereg regs (cp_extra cx res mode nch ns)) in
  ew E 2 = getr regs 2 /\ ew E 3 = getr regs 3 /\ ew E 4 = getr regs 4 /\ ew E 9 = getr regs 9 /\
  ew E 32 = Z_to_bv 64 SB /\ ew E 33 = Z_to_bv 64 res /\ ew E 34 = Z_to_bv 64 (dec_a_len (d_n cx)) /\
  ew E 35 = Z_to_bv 64 mode /\ ew E 36 = Z_to_bv 64 (d_F cx) /\
  ew E 38 = Z_to_bv 64 (d_p cx + dec_a_u (d_n cx)) /\
  ew E 39 = Z_to_bv 64 (nch mod 2 ^ 32) /\ ew E 40 = Z_to_bv 64 (ns mod 2 ^ 32) /\
  ew E 41 = Z_to_bv 64 (bv_unsigned (nth 12 (d_body cx) (Z_to_bv 8 0))) /\
  ew E 42 = Z_to_bv 64 (bv_unsigned (nth 13 (d_body cx) (Z_to_bv 8 0))) /\
  ew E (A_OBJ 7) = Z_to_bv 64 CCL.A_M /\ ew E (A_OBJ 8) = Z_to_bv 64 CCL.A_T.
Proof.
intros regs cx res mode nch ns E.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cp_extra cx res mode nch ns)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
repeat split;
  first [ subst E; reflexivity
        | rewrite EL by (unfold A_TEXT; lia);
          first [ exact (ew_Ereg_nat regs _ 2 2%bv eq_refl) | exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)
                | exact (ew_Ereg_nat regs _ 4 4%bv eq_refl) | exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)
                | exact (ew_Ereg_extra regs _ 0) | exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
                | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4) | exact (ew_Ereg_extra regs _ 6)
                | exact (ew_Ereg_extra regs _ 7) | exact (ew_Ereg_extra regs _ 8) | exact (ew_Ereg_extra regs _ 9)
                | exact (ew_Ereg_extra regs _ 10) ] ].
Qed.

(* The symbolic state at a point of the segment (pc, register map sr), from cp_core's facts: the spill area at s1
   (written at +0x370 .. +0x398, 112(s1) holding the frame), the mode's two fields, the two div-36 words. *)
Lemma cp_seat : forall (fx : YK11.FPState) (pc : Z) sr (cx : dctx) ly' S' (W' : world decodesegs0) regs' mem' md'
    (res mode nch ns : Z),
  regs_ok (Eimg (Ereg regs' (cp_extra cx res mode nch ns))) sr regs' ->
  dec_a_core B cx ly' S' W' regs' mem' md' dec_ev_234 ->
  4096 <= res -> res <= 2 ^ 47 - 16 -> res mod 16 = 0 ->
  dec_a_mode_ok cx W' mem' mode nch ns ->
  dec_a_slot cx (aview decodesegs0 (w_H W') mem') 112 (d_F cx) ->
  rdword (aview decodesegs0 (w_H W') mem') CCL.A_M = Some CCL.KM ->
  rdword (aview decodesegs0 (w_H W') mem') CCL.A_T = Some CCL.KT ->
  4096 <= mode -> mode + 16 <= alloc_ceiling -> mode mod 8 = 0 -> (mode + 16 <= CCL.A_M \/ CCL.A_T + 8 <= mode) ->
  d_F cx + 64 <= alloc_ceiling ->
  st_ok_pi (fx := fx) SEGS VAL (Eimg (Ereg regs' (cp_extra cx res mode nch ns)))
    (mkSS pc sr [cp_frame; cp_mode; cp_km; cp_kt] None cp_facts)
    (restrict (w_H W') (@YK11.mkst fx regs' (Z_to_bv 64 (VAL A_TEXT + pc)) mem' (YK11.seg_rom SEGS))).
Proof.
intros fx pc sr cx ly' S' W' regs' mem' md' res mode nch ns HREGS HC Hr0 Hr1 Hr16 HMODE HSLOT HKM HKT
  Hm0 Hm1 Hm8 HmD HFhi.
destruct HC as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1 & Hsp1m & Hgp & Htp & HSAV & HF4096 & HFmod & HFpres & HFL &
  Hblk & HGARR).
destruct HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs2 & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk & G5 &
  HQT).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct HMODE as (_ & Hnch & Hns & Vnch & Vns).
pose proof alloc_ceiling_val as Hac.
pose proof IMG_LO_val as HLO. pose proof IMG_TOP_val as HTOP.
assert (HSTK : DEC_LLVMF_STK = 32768) by reflexivity.
unfold dec_a_slot in HSLOT.
rewrite restrict_mkst_fx.
pose proof (cp_E_eqs regs' cx res mode nch ns) as EQS. cbv zeta in EQS.
set (E := Eimg (Ereg regs' (cp_extra cx res mode nch ns))) in EQS, HREGS |- *.
destruct EQS as (E2 & E3 & E4 & E9 & E32 & E33 & E34 & E35 & E36 & E38 & E39 & E40 & E41 & E42 & E7o & E8o).
assert (Usp : bv_unsigned (ew E 2) = d_sp1 cx) by (rewrite E2; exact Hsp).
assert (Us1 : bv_unsigned (ew E 9) = d_sp1 cx)
  by (rewrite E9, Hs1; unfold w64; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (Ures : bv_unsigned (ew E 33) = res) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Umode : bv_unsigned (ew E 35) = mode) by (rewrite E35; apply unsigned_lit_small; lia).
assert (UKM : bv_unsigned (ew E (A_OBJ 7)) = CCL.A_M) by (rewrite E7o; apply unsigned_lit_small; unfold CCL.A_M; lia).
assert (UKT : bv_unsigned (ew E (A_OBJ 8)) = CCL.A_T) by (rewrite E8o; apply unsigned_lit_small; unfold CCL.A_T; lia).
apply (pa_entry_st_ok_full (fx := fx)).
- exact HREGS.
- vm_compute. reflexivity.
- (* the regions *)
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [cp_frame cp_mode cp_km cp_kt YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Us1. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable decodesegs0); apply Hpres; unfold d_sp0 in *; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val decodesegs0 E _ (d_sp1 cx) 112 8 (SOff 36 0) (d_F cx));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword decodesegs0 (w_H W') mem' _ _ HSLOT).
  + rewrite Umode. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val decodesegs0 E _ mode 4 4 (SOff 39 0) (nch mod 2 ^ 32));
        [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (Z.mod_pos_bound nch (2 ^ 32) ltac:(lia)); zside | zside | exact Vnch].
    * apply (chunk_ok_val decodesegs0 E _ mode 8 4 (SOff 40 0) (ns mod 2 ^ 32));
        [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (Z.mod_pos_bound ns (2 ^ 32) ltac:(lia)); zside | zside | exact Vns].
  + rewrite UKM. split; [unfold CCL.A_M; lia|]. split; [unfold CCL.A_M; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val decodesegs0 E _ CCL.A_M 0 8 (SLit CCL.KM) CCL.KM);
      [reflexivity | unfold CCL.KM; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword decodesegs0 (w_H W') mem' _ _ HKM).
  + rewrite UKT. split; [unfold CCL.A_T; lia|]. split; [unfold CCL.A_T; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val decodesegs0 E _ CCL.A_T 0 8 (SLit CCL.KT) CCL.KT);
      [reflexivity | unfold CCL.KT; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword decodesegs0 (w_H W') mem' _ _ HKT).
- (* pairwise disjoint: the spill area is the stack, the mode is below alloc_ceiling and off the two words *)
  apply pairwise_disjoint_of_extents. unfold cp_frame, cp_mode, cp_km, cp_kt, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite Us1, Umode, UKM, UKT.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold d_sp0 in *. unfold CCL.A_M, CCL.A_T in *.
  repeat split; lia.
- (* the facts *)
  split; [|split; [exact I | exact I]].
  cbn [cp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Us1, USB, Ures, Umode.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold d_sp0 in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
Qed.

(* The register map at +0x234 (cp_regs0: a0 = res, s4 still the input length) is the cut point's. *)
Lemma cp_regs0_ok : forall (cx : dctx) (regs : bvmap 5 word) (res mode nch ns : Z),
  YK11.getr regs 10 = w64 res -> YK11.getr regs 18 = w64 SHADOW_OFF ->
  YK11.getr regs 24 = w64 (d_p cx + dec_a_u (d_n cx)) -> YK11.getr regs 26 = w64 (dec_a_len (d_n cx)) ->
  YK11.getr regs 25 = w64 mode -> YK11.getr regs 23 = w64 (mode + 4) -> YK11.getr regs 22 = w64 (mode + 8) ->
  dec_a_fr cx regs -> 0 <= mode < 2 ^ 63 ->
  regs_ok (Eimg (Ereg regs (cp_extra cx res mode nch ns))) cp_regs0 regs.
Proof.
intros cx regs res mode nch ns H10 H18 H24 H26 H25 H23 H22 (H19 & H21 & H27) Hm.
pose proof (cp_E_eqs regs cx res mode nch ns) as EQS. cbv zeta in EQS.
destruct EQS as (E2 & E3 & E4 & E9 & E32 & E33 & E34 & E35 & E36 & E38 & _).
unfold cp_regs0.
repeat (apply cp_regs_ok_set; [| cbn [sv_denot]; first
    [ rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; first [exact H21 | exact H19]
    | rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; exact H24
    | rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; exact H18
    | rewrite E35, unsigned_lit_small by lia; first [exact H22 | exact H23 | rewrite Z.add_0_r; exact H25]
    | rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; exact H26
    | rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; exact H10 ] ]).
apply regs_ok_Eimg_Ereg.
Qed.

(* ... and the one of every later point (cp_regs1: s4 = res, a0 free). *)
Lemma cp_regs1_ok : forall (cx : dctx) (regs : bvmap 5 word) (res mode nch ns : Z),
  YK11.getr regs 20 = w64 res -> YK11.getr regs 18 = w64 SHADOW_OFF -> YK11.getr regs 26 = w64 (dec_a_len (d_n cx)) ->
  YK11.getr regs 25 = w64 mode -> YK11.getr regs 23 = w64 (mode + 4) -> YK11.getr regs 22 = w64 (mode + 8) ->
  dec_a_fr cx regs -> 0 <= mode < 2 ^ 63 ->
  regs_ok (Eimg (Ereg regs (cp_extra cx res mode nch ns))) cp_regs1 regs.
Proof.
intros cx regs res mode nch ns H20 H18 H26 H25 H23 H22 (H19 & H21 & H27) Hm.
pose proof (cp_E_eqs regs cx res mode nch ns) as EQS. cbv zeta in EQS.
destruct EQS as (E2 & E3 & E4 & E9 & E32 & E33 & E34 & E35 & E36 & E38 & _).
unfold cp_regs1.
repeat (apply cp_regs_ok_set; [| cbn [sv_denot]; first
    [ rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; first [exact H21 | exact H19]
    | rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; exact H18
    | rewrite E35, unsigned_lit_small by lia; first [exact H22 | exact H23 | rewrite Z.add_0_r; exact H25]
    | rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; exact H26
    | rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; exact H20 ] ]).
apply regs_ok_Eimg_Ereg.
Qed.

(* A register the run did not touch has its entry value. *)
Lemma cp_reg_same : forall (E0 E' : env) sr regs (srx : list sv) (regs2 : bvmap 5 word) (r : bv 5) k c,
  regs_ok E0 sr regs ->
  (forall n, (n < 512)%nat -> ew E' n = ew E0 n) ->
  getr regs2 r = sv_denot E' (sr_get srx r) ->
  sr_get srx r = SOff k c -> sr_get sr r = SOff k c -> (k < 512)%nat ->
  getr regs2 r = getr regs r.
Proof.
intros E0 E' sr regs srx regs2 r k c HR AG H2 E1 E2 Hk.
rewrite H2, E1, (HR r), E2. cbn [sv_denot]. rewrite (AG k Hk). reflexivity.
Qed.

(* cp_core moves to a new memory (cp_core_kept) and to new registers that agree on cp_core's. *)
Lemma cp_core_xfer : forall (cx : dctx) (res mode nch ns : Z) ly S (W : world decodesegs0) regs mem md regs2 mem2 md2,
  AR_laws decodesegs0 B -> dec_crt_cells B -> d_n cx = Z.of_nat (length (d_pl cx)) ->
  cp_core B MT cx res mode nch ns ly S W regs mem md ->
  @ajournal rc dec_A_sink_head decodesegs0 B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S W mem2 md2 dec_ev_234 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - 4096 <= a < d_sp1 cx + 96) ->
     aview decodesegs0 (w_H W) mem2 a = aview decodesegs0 (w_H W) mem a) ->
  (forall r : Z, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27] ->
     YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  cp_core B MT cx res mode nch ns ly S W regs2 mem2 md2.
Proof.
intros cx res mode nch ns ly S W regs mem md regs2 mem2 md2 LAWS HCELLS Hlen HCORE HJ2 K P.
pose proof (cp_core_kept B MT cx res mode nch ns ly S W regs mem md mem2 md2 LAWS HCELLS Hlen HCORE HJ2
  ltac:(intros a Ha _ Hs; exact (K a Ha Hs))) as HC2.
destruct HC2 as (HC & Hbl & Hres & Hmle & Hmok & (F19 & F21 & F27) & R18 & R20 & R22 & R26 & HMODE & HFSH & HSLOT).
destruct HC as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1a & Hgp & Htp & Hrest).
split; [|split; [exact Hbl|]].
{ split; [exact HJ|]. split; [exact Hfrs|].
  split; [exact (eq_trans (P 8 ltac:(cbn [In]; lia)) R8)|].
  split; [exact (eq_trans (P 9 ltac:(cbn [In]; lia)) R9)|].
  split; [unfold spZ in *; rewrite <- Hsp; f_equal; exact (P 2 ltac:(cbn [In]; lia))|].
  split; [exact Hsp1r|]. split; [exact Hsp1a|].
  split; [exact (eq_trans (P 3 ltac:(cbn [In]; lia)) Hgp)|].
  split; [exact (eq_trans (P 4 ltac:(cbn [In]; lia)) Htp)|].
  exact Hrest. }
split; [exact Hres|]. split; [exact Hmle|]. split; [exact Hmok|].
split; [split; [exact (eq_trans (P 19 ltac:(cbn [In]; lia)) F19)|];
        split; [exact (eq_trans (P 21 ltac:(cbn [In]; lia)) F21)|
                exact (eq_trans (P 27 ltac:(cbn [In]; lia)) F27)]|].
split; [exact (eq_trans (P 18 ltac:(cbn [In]; lia)) R18)|].
split; [exact (eq_trans (P 20 ltac:(cbn [In]; lia)) R20)|].
split; [exact (eq_trans (P 22 ltac:(cbn [In]; lia)) R22)|].
split; [exact (eq_trans (P 26 ltac:(cbn [In]; lia)) R26)|].
split; [exact HMODE|]. split; [exact HFSH|]. exact HSLOT.
Qed.

Lemma cp_getr_upd_other : forall regs (r : bv 5) v, bv_unsigned r <> 20 ->
  YK11.getr (YK11.regupd regs 20 v) r = YK11.getr regs r.
Proof.
intros regs r v H. unfold YK11.getr. destruct (bv_eqb r 0); [reflexivity|].
apply regupd_other. intros ->. apply H. reflexivity.
Qed.
Lemma cp_getr_upd_same : forall regs v, YK11.getr (YK11.regupd regs 20 v) 20 = v.
Proof. intros regs v. unfold YK11.getr. cbn [bv_eqb]. vm_compute (bv_eqb _ _). apply regupd_same. Qed.

(* llvm_a_st_234's facts are cp_core once s4 holds the copy (`mv s4, a0` at +0x234). *)
Lemma cp_core_234 : forall (cx : dctx) (res mode nch ns : Z) ly S (W : world decodesegs0) regs mem md,
  dec_a_core B cx ly S W regs mem md dec_ev_234 ->
  ablocks B ly S = ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] -> 4096 <= res ->
  mo_le MT (d_S cx) S (dec_spent_234 MT (d_n cx)) -> mo_ok MT S (dec_rest_234 MT) ->
  dec_a_fr cx regs -> YK11.getr regs 18 = w64 SHADOW_OFF -> YK11.getr regs 22 = w64 (mode + 8) ->
  YK11.getr regs 26 = w64 (dec_a_len (d_n cx)) ->
  dec_a_mode_ok cx W mem mode nch ns -> dec_a_fsh cx (aview decodesegs0 (w_H W) mem) 0 4 ->
  dec_a_slot cx (aview decodesegs0 (w_H W) mem) 112 (d_F cx) ->
  cp_core B MT cx res mode nch ns ly S W (YK11.regupd regs 20 (w64 res)) mem md.
Proof.
intros cx res mode nch ns ly S W regs mem md HC Hbl Hres Hmle Hmok (F19 & F21 & F27) R18 R22 R26 HMODE HFSH HSLOT.
destruct HC as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1a & Hgp & Htp & Hrest).
assert (U : forall r : bv 5, bv_unsigned r <> 20 -> YK11.getr (YK11.regupd regs 20 (w64 res)) r = YK11.getr regs r)
  by (intros r Hr; apply cp_getr_upd_other; exact Hr).
split; [|split; [exact Hbl|]].
{ split; [exact HJ|]. split; [exact Hfrs|].
  split; [rewrite U by (vm_compute; discriminate); exact R8|].
  split; [rewrite U by (vm_compute; discriminate); exact R9|].
  split; [unfold spZ in *; rewrite U by (vm_compute; discriminate); exact Hsp|].
  split; [exact Hsp1r|]. split; [exact Hsp1a|].
  split; [rewrite U by (vm_compute; discriminate); exact Hgp|].
  split; [rewrite U by (vm_compute; discriminate); exact Htp|].
  exact Hrest. }
split; [exact Hres|]. split; [exact Hmle|]. split; [exact Hmok|].
split; [split; [rewrite U by (vm_compute; discriminate); exact F19|];
        split; [rewrite U by (vm_compute; discriminate); exact F21|
                rewrite U by (vm_compute; discriminate); exact F27]|].
split; [rewrite U by (vm_compute; discriminate); exact R18|].
split; [exact (cp_getr_upd_same regs (w64 res))|].
split; [rewrite U by (vm_compute; discriminate); exact R22|].
split; [rewrite U by (vm_compute; discriminate); exact R26|].
split; [exact HMODE|]. split; [exact HFSH|]. exact HSLOT.
Qed.

(* The bytes a run kept: off the writable windows of its regions; here only the spill area s1 + 32 .. s1 + 96. *)
Definition cp_kept (W : world decodesegs0) (m m0 : word -> option byte) (lo hi : Z) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview decodesegs0 (w_H W) m a = aview decodesegs0 (w_H W) m0 a.
Lemma cp_kept_refl : forall W m lo hi, cp_kept W m m lo hi.
Proof. intros W m lo hi a _ _. reflexivity. Qed.
Lemma cp_kept_step : forall (E : env) rs (W : world decodesegs0) m0 m1 m2 lo hi,
  cp_kept W m1 m0 lo hi ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  (forall a, in_wrange E rs a -> lo <= a < hi) ->
  cp_kept W m2 m0 lo hi.
Proof.
intros E rs W m0 m1 m2 lo hi K HF HW a Ha Hs. rewrite <- (K a Ha Hs). unfold aview, mbyte.
rewrite HF; [reflexivity|]. rewrite unsigned_lit_small by lia. intros Hin. apply Hs. exact (HW a Hin).
Qed.



(* An atom whose slot holds a small value. *)
Lemma cp_denot_off : forall (E : env) k v c, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff k c) = Z_to_bv 64 (v + c).
Proof. intros E k v c H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
(* The function's base, the listing's A_TEXT value. *)
Lemma cp_base : VAL A_TEXT = DEC_A_LLVMF.
Proof. vm_compute. reflexivity. Qed.
(* An empty copy is trivially filled. *)
Lemma cp_filled_nil : forall (cx : dctx) res (W : world decodesegs0) m,
  d_n cx = Z.of_nat (length (d_pl cx)) -> dec_a_len (d_n cx) = 0 -> cp_filled cx res W m.
Proof.
intros cx res W m Hl H0 j Hj. exfalso. unfold cp_body, d_body in Hj. rewrite length_map, length_skipn in Hj.
unfold dec_a_len, dec_a_u in *. lia.
Qed.

(* A register the run did not touch, at a call (st_ok) or inside the walk (st_ok_pi): its entry value. *)
Ltac cp_same HS HREGS AG :=
  lazymatch goal with |- YK11.getr ?regs2 ?r = YK11.getr ?regs ?r =>
  lazymatch type of HREGS with regs_ok ?E0 ?sr _ =>
  lazymatch type of HS with
  | st_ok ?segs ?Ex ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    lazymatch e with SOff ?k ?c =>
      exact (cp_reg_same E0 Ex sr regs (ss_regs ss) regs2 r k c HREGS AG
        (st_ok_restrict_reg segs H Ex ss ms r HS) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; lia)) end
  | st_ok_pi ?segs ?val ?Ex ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    lazymatch e with SOff ?k ?c =>
      exact (cp_reg_same E0 Ex sr regs (ss_regs ss) regs2 r k c HREGS AG
        (st_ok_pi_restrict_reg H Ex ss ms r HS) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; lia)) end
  end end end.
(* cp_core's twelve registers at a call: untouched by the run, except s4 at +0x234 (U20). *)
Ltac cp_agree HS HREGS AG :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ first [ rewrite cp_getr_upd_other by (vm_compute; congruence); cp_same HS HREGS AG
            | cp_same HS HREGS AG ] | ]);
  try destruct Hr.

(* The write rights of a run and the environment bookkeeping (ReadName.v rn_awr / rn_env / rn_reg). *)
(* The write rights of a run: its one writable region is the spill area at s1 (slot 9), inside the walk's own
   stack window [sp0 - STK, sp0); every other region is read only. AG says slot 9 is the entry's. *)
Ltac cp_awr :=
  let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew _ n = ew _ n |- _ => H end in
  let Us1 := lazymatch goal with H : bv_unsigned (ew _ 9) = d_sp1 _ |- _ => H end in
  lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat);
    [ reflexivity | first [exact Us1 | rewrite (AG 9%nat) by lia; exact Us1]
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; unfold d_sp0, DEC_LLVMF_STK in *; lia |] ].

(* After a run or a call the environment grows above slot 511; AG says the slots below are those of the entry
   (libreac/fuzz_boxreg ReadName.v rn_env, the same text). *)
Ltac cp_env HS AG :=
  let Ex := lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => Ex | st_ok _ ?Ex _ _ => Ex end in
  lazymatch type of AG with forall n, _ -> ew ?Eo n = ew ?E0 n =>
  lazymatch Ex with
  | Eo => idtac
  | _ => let AG2 := fresh "AG" in
    assert (AG2 : forall n, (n < 512)%nat -> ew Ex n = ew E0 n)
      by (intros nn Hnn; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia];
          first [reflexivity | apply AG; exact Hnn]);
    clear AG; rename AG2 into AG
  end end;
  repeat match goal with H : img_env _ _ ?Ey |- _ => lazymatch Ey with Ex => fail | _ => clear H end end.
(* A register's symbolic value, without unfolding its denotation (ReadName.v rn_reg). *)
Ltac cp_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* After a run: the bytes it kept (cp_kept_step), off the spill area s1 + 32 .. s1 + 96, the one writable window. *)
Ltac cp_kupd KEPT :=
  let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew _ n = ew _ n |- _ => H end in
  let Us1 := lazymatch goal with H : bv_unsigned (ew _ 9) = d_sp1 _ |- _ => H end in
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2) |- _ =>
    let rs' := eval vm_compute in rs in change rs with rs' in HFr;
    let K2 := fresh "KEPT" in
    pose proof (cp_kept_step Ex rs' W _ m1 m2 _ _ KEPT HFr) as K2;
    lazymatch type of K2 with ?A -> _ =>
      let HW := fresh "HW" in
      assert (HW : A);
      [ let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
        intros a (r & Hin & Hr); cbn [In] in Hin;
        repeat (destruct Hin as [<- | Hin];
          [ cbn [cp_frame cp_mode cp_km cp_kt cp_res YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
            try rewrite (AG 9%nat) in Hr by lia; first [rewrite Us1 in Hr; lia | lia] |]);
        destruct Hin
      | specialize (K2 HW); clear HW ] end;
    clear KEPT HFr; rename K2 into KEPT
  end;
  repeat match goal with
  | H : frame_of _ _ _ _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  end.

(* +0x234 .. the first call: `mv s4, a0`, the empty-copy test (+0x238, +0x244), the NULL check of the copy
   (+0x23c, refuted by 4096 <= res), and the call: __asan_memcpy (res, p + u, len) at +0x250 when len <> 0,
   reac_frame_is_reac (res, 0) at +0x2b0 when len = 0. *)
Lemma cp_stage_a : forall (fx : YK11.FPState) (cx : dctx) ly' S' (W' : world decodesegs0) regs' mem' md'
    (res mode nch ns : Z),
  AR_laws decodesegs0 B -> dec_crt_cells B ->
  (forall a, dec_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx -> dec_a_rom cx ->
  frm_zero (@fp_csr fx) ->
  dec_a_core B cx ly' S' W' regs' mem' md' dec_ev_234 ->
  ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] -> 4096 <= res ->
  mo_le MT (d_S cx) S' (dec_spent_234 MT (d_n cx)) -> mo_ok MT S' (dec_rest_234 MT) ->
  dec_a_fr cx regs' ->
  YK11.getr regs' 10 = w64 res -> YK11.getr regs' 18 = w64 SHADOW_OFF ->
  YK11.getr regs' 24 = w64 (d_p cx + dec_a_u (d_n cx)) -> YK11.getr regs' 26 = w64 (dec_a_len (d_n cx)) ->
  YK11.getr regs' 25 = w64 mode -> YK11.getr regs' 23 = w64 (mode + 4) -> YK11.getr regs' 22 = w64 (mode + 8) ->
  dec_a_mode_ok cx W' mem' mode nch ns -> dec_a_fsh cx (aview decodesegs0 (w_H W') mem') 0 4 ->
  dec_a_slot cx (aview decodesegs0 (w_H W') mem') 112 (d_F cx) ->
  SRr decodesegs0 W' (mkCfg (@YK11.mkst fx regs' (w64 (DEC_A_LLVMF + 0x234)) mem' (YK11.seg_rom decodesegs0)) md')
    (fun W2 c2 =>
       (0 < dec_a_len (d_n cx) /\
        cp_at B MT (Z_to_bv 64 (decode_sigma DS___asan_memcpy)) cx res mode nch ns
          (fun r => cp_rm mode r /\ YK11.getr r 10 = w64 res /\ YK11.getr r 11 = w64 (d_p cx + dec_a_u (d_n cx)) /\
                    YK11.getr r 12 = w64 (dec_a_len (d_n cx)) /\ YK11.getr r 1 = w64 (DEC_A_LLVMF + 0x254))
          (fun _ _ => True) W2 c2) \/
       (dec_a_len (d_n cx) = 0 /\
        cp_at B MT (Z_to_bv 64 (decode_sigma DS_reac_frame_is_reac)) cx res mode nch ns
          (fun r => cp_rm mode r /\ YK11.getr r 10 = w64 res /\ YK11.getr r 11 = w64 0 /\
                    YK11.getr r 1 = w64 (DEC_A_LLVMF + 0x2b4))
          (cp_filled cx res) W2 c2)).
Proof.
intros fx cx ly' S' W' regs' mem' md' res mode nch ns LAWS HCELLS HSC HB HR Hfrm HC Hbl Hres MLE MOK HFR
  H10 H18 H24 H26 H25 H23 H22 HMODE HFSH HSLOT.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof HC as (HJc & Hfrs & Hs0 & Hs1 & Hsp & Hsp1 & Hsp1m & Hgp & Htp & HSAV & HF4096 & HFmod & HFpres & HFL &
  Hblk & HGARR).
pose proof HJc as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
unfold DEC_LLVMF_STK in *.
assert (Hfin : In (DEC_FCLASS, d_fpos cx) (frames S')) by (rewrite Hfrs; left; reflexivity).
assert (Hfa : frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds decodesegs0 B LAWS ly' S' W' mem' md' DEC_FCLASS (d_fpos cx) HAR Hfin) as (_ & HFhi & _).
rewrite Hfa in HFhi. change (fs_frame_bytes DEC_FCLASS) with 64 in HFhi.
assert (Hinr : In (res, dec_a_len (d_n cx)) (ablocks B ly' S'))
  by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (Hr16 & _ & Hrceil & Hrapp & _).
destruct (cp_mode_facts B cx ly' S' W' mem' md' mode nch ns HCELLS LAWS HAR Hfin Hfa HF4096 HFmod HFSH HMODE)
  as (Hm0 & Hm1 & Hm8 & HmD & HmS4 & HmS8 & HmB).
destruct (cp_rom_div B cx [(DEC_FCLASS, d_fpos cx)] ly' S' W' mem' md' dec_ev_234 HSC HR HJc) as (HKM & HKT).
assert (Hn26 : 0 <= d_n cx < 2 ^ 26).
{ clear - HB. unfold dec_a_base, dec_lib_pre_x in HB.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : (d_n cx = 0 /\ _) \/ (0 < d_n cx < 2 ^ 26 /\ _) |- _ =>
    destruct H as [[Hz _] | [Hz _]]; lia end. }
assert (Hlenpl : d_n cx = Z.of_nat (length (d_pl cx)))
  by (clear - HB; unfold dec_a_base, dec_lib_pre_x in HB; decompose [and] HB; assumption).
assert (Hlen : 0 <= dec_a_len (d_n cx) < 2 ^ 26) by (unfold dec_a_len; lia).
pose proof (cp_core_234 cx res mode nch ns ly' S' W' regs' mem' md' HC Hbl Hres MLE MOK HFR H18 H22 H26 HMODE HFSH
  HSLOT) as HCORE.
pose proof (req_size_pos0 (dec_a_len (d_n cx)) ltac:(unfold dec_a_len; lia)) as Hreq.
pose proof (cp_regs0_ok cx regs' res mode nch ns H10 H18 H24 H26 H25 H23 H22 HFR ltac:(lia)) as HREGS.
pose proof (cp_seat fx 0x234 cp_regs0 cx ly' S' W' regs' mem' md' res mode nch ns HREGS
  HC Hres ltac:(lia) Hr16 HMODE HSLOT HKM HKT Hm0 Hm1 Hm8 HmD HFhi) as HS.
pose proof (cp_E_eqs regs' cx res mode nch ns) as EQS. cbv zeta in EQS.
set (E := Eimg (Ereg regs' (cp_extra cx res mode nch ns))) in HS, HREGS, EQS.
destruct EQS as (E2 & E3 & E4 & E9 & E32 & E33 & E34 & E35 & E36 & E38 & E39 & E40 & E41 & E42 & E7o & E8o).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Us1 : bv_unsigned (ew E 9) = d_sp1 cx) by (rewrite E9, Hs1; unfold w64; apply unsigned_lit_small; lia).
assert (AG : forall n, (n < 512)%nat -> ew E n = ew E n) by reflexivity.
clearbody E.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W') mem')) by constructor.
pose proof (cp_kept_refl W' mem' (d_sp1 cx - 4096) (d_sp1 cx + 96)) as KEPT.
pose (RUN := @paj_run fx rc dec_A_sink_head decode_listing PL_decode (@PI_decode rc) B LAWS).
pose (BR := @paj_branch fx rc decode_listing (@PI_decode rc)).
change (w64 (DEC_A_LLVMF + 0x234)) with (Z_to_bv 64 (VAL A_TEXT + 0x234)).
change (YK11.seg_rom decodesegs0) with (YK11.seg_rom SEGS).
(* 1. +0x234 .. +0x238: s4 := res, then the branch on len = 0. *)
paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
cp_kupd KEPT.
cp_env HS AG.
psrr_branch_tok RUN BR HS SHOK Bspan.
all: rewrite branch_eq_U, (U_atom _ 34 (dec_a_len (d_n cx)) ltac:(rewrite AG by lia; exact E34)), U_lit in Hc by lia.
(* 2. len = 0: straight to reac_frame_is_reac (res, 0) at +0x2b0; len <> 0: the NULL check at +0x23c (refuted by
      4096 <= res) and __asan_memcpy at +0x250. *)
all: paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
all: cp_kupd KEPT.
all: cp_env HS AG.
all: pmkst HS.
all: apply SRr_ret.
(* the two calls *)
all: lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?msx) |- _ =>
  cp_reg HS (10%bv : bv 5) Ra0; cp_reg HS (11%bv : bv 5) Ra1; cp_reg HS (1%bv : bv 5) Rra end.
- (* len = 0: reac_frame_is_reac (res, 0) *)
  right. split; [apply Z.eqb_eq in Hc; exact Hc|].
  exists fx, ly', S'. eexists _, _, _. split; [reflexivity|]. split; [exact Hfrm|].
  split.
  { apply (cp_core_xfer cx res mode nch ns ly' S' W' (YK11.regupd regs' 20 (w64 res)) mem' md' _ _ _
      LAWS HCELLS Hlenpl HCORE HJc KEPT).
    intros r Hr; cbn [In] in Hr. decompose [or] Hr; clear Hr; try contradiction; subst r;
      try (rewrite cp_getr_upd_other by (vm_compute; congruence); cp_same HS HREGS AG).
    (* s4 := a0 = res at +0x234 *)
    transitivity (w64 res); [| symmetry; exact (cp_getr_upd_same regs' (w64 res))].
    cp_reg HS (20%bv : bv 5) R20. etransitivity; [exact R20|].
    rewrite (cp_denot_off E 33 res 0 E33) by lia. rewrite Z.add_0_r. reflexivity. }
  split; [|exact (cp_filled_nil cx res W' _ Hlenpl ltac:(apply Z.eqb_eq in Hc; exact Hc))].
  split; [split; [transitivity (YK11.getr regs' 25); [cp_same HS HREGS AG | exact H25]
                 | transitivity (YK11.getr regs' 23); [cp_same HS HREGS AG | exact H23]]|].
  split; [rewrite Ra0, (cp_denot_off E 33 res 0 E33), Z.add_0_r by lia; reflexivity|].
  split; [rewrite Ra1; reflexivity|].
  rewrite Rra. etransitivity; [apply codeptr_val; assumption|]. rewrite cp_base. reflexivity.
- (* len <> 0: __asan_memcpy (res, p + u, len) *)
  left. split; [apply Z.eqb_neq in Hc; lia|].
  exists fx, ly', S'. eexists _, _, _. split; [reflexivity|]. split; [exact Hfrm|].
  split.
  { apply (cp_core_xfer cx res mode nch ns ly' S' W' (YK11.regupd regs' 20 (w64 res)) mem' md' _ _ _
      LAWS HCELLS Hlenpl HCORE HJc KEPT).
    intros r Hr; cbn [In] in Hr. decompose [or] Hr; clear Hr; try contradiction; subst r;
      try (rewrite cp_getr_upd_other by (vm_compute; congruence); cp_same HS HREGS AG).
    transitivity (w64 res); [| symmetry; exact (cp_getr_upd_same regs' (w64 res))].
    cp_reg HS (20%bv : bv 5) R20. etransitivity; [exact R20|].
    rewrite (cp_denot_off E 33 res 0 E33) by lia. rewrite Z.add_0_r. reflexivity. }
  split; [|exact I].
  split; [split; [transitivity (YK11.getr regs' 25); [cp_same HS HREGS AG | exact H25]
                 | transitivity (YK11.getr regs' 23); [cp_same HS HREGS AG | exact H23]]|].
  split; [rewrite Ra0, (cp_denot_off E 33 res 0 E33), Z.add_0_r by lia; reflexivity|].
  assert (Hpu : 0 <= d_p cx + dec_a_u (d_n cx) < 2 ^ 64).
  { apply Z.eqb_neq in Hc. assert (Hn0 : 0 < d_n cx) by (unfold dec_a_len in Hc; lia).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (Hblk Hn0)) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos0 (d_n cx) ltac:(lia)) as (_ & Hpreq). unfold dec_a_u. lia. }
  split; [rewrite Ra1, (cp_denot_off E 38 _ 0 E38), Z.add_0_r by lia; reflexivity|].
  split; [cp_reg HS (12%bv : bv 5) Ra2; rewrite Ra2, (cp_denot_off E 34 _ 0 E34), Z.add_0_r by lia; reflexivity|].
  rewrite Rra. etransitivity; [apply codeptr_val; assumption|]. rewrite cp_base. reflexivity.
Qed.


(* The copy lies below alloc_ceiling, so a step that keeps everything off the stack window keeps it filled. *)
Lemma cp_filled_kept : forall (cx : dctx) res (W : world decodesegs0) m m2 lo hi,
  cp_kept W m2 m lo hi -> 0 <= res -> res + dec_a_len (d_n cx) <= lo -> lo <= 2 ^ 64 ->
  d_n cx = Z.of_nat (length (d_pl cx)) -> cp_filled cx res W m -> cp_filled cx res W m2.
Proof.
intros cx res W m m2 lo hi K H0 Hlo Hlo2 Hl HF. unfold cp_filled in *.
apply (cp_garr8_kept (w_H W) (w_H W) m m2 res _); [|exact HF].
intros j Hj. unfold cp_body, d_body in Hj. rewrite length_map, length_skipn in Hj.
apply K; unfold dec_a_len, dec_a_u in *; lia.
Qed.

(* +0x254 .. +0x25c: `mv a0, s4; mv a1, s10`, and reac_frame_is_reac (res, len). *)
Lemma cp_stage_b : forall (fx : YK11.FPState) (cx : dctx) (res mode nch ns : Z) ly S (W : world decodesegs0) regs mem md,
  AR_laws decodesegs0 B -> dec_crt_cells B ->
  (forall a, dec_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx -> dec_a_rom cx ->
  frm_zero (@fp_csr fx) ->
  cp_core B MT cx res mode nch ns ly S W regs mem md -> cp_rm mode regs -> cp_filled cx res W mem ->
  SRr decodesegs0 W (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x254)) mem (YK11.seg_rom decodesegs0)) md)
    (cp_at B MT (Z_to_bv 64 (decode_sigma DS_reac_frame_is_reac)) cx res mode nch ns
       (fun r => cp_rm mode r /\ YK11.getr r 10 = w64 res /\ YK11.getr r 11 = w64 (dec_a_len (d_n cx)) /\
                 YK11.getr r 1 = w64 (DEC_A_LLVMF + 0x260))
       (cp_filled cx res)).
Proof.
intros fx cx res mode nch ns ly S W regs mem md LAWS HCELLS HSC HB HR Hfrm HCORE HRM HFILL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof HCORE as (HC & Hbl & Hres & MLE & MOK & HFR & H18 & H20 & H22 & H26 & HMODE & HFSH & HSLOT).
pose proof HRM as (H25 & H23).
pose proof HC as (HJc & Hfrs & Hs0 & Hs1 & Hsp & Hsp1 & Hsp1m & Hgp & Htp & HSAV & HF4096 & HFmod & HFpres & HFL &
  Hblk & HGARR).
pose proof HJc as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
unfold DEC_LLVMF_STK in *.
assert (Hfin : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Hfa : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds decodesegs0 B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hfin) as (_ & HFhi & _).
rewrite Hfa in HFhi. change (fs_frame_bytes DEC_FCLASS) with 64 in HFhi.
assert (Hinr : In (res, dec_a_len (d_n cx)) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (Hr16 & _ & Hrceil & Hrapp & _).
destruct (cp_mode_facts B cx ly S W mem md mode nch ns HCELLS LAWS HAR Hfin Hfa HF4096 HFmod HFSH HMODE)
  as (Hm0 & Hm1 & Hm8 & HmD & HmS4 & HmS8 & HmB).
destruct (cp_rom_div B cx [(DEC_FCLASS, d_fpos cx)] ly S W mem md dec_ev_234 HSC HR HJc) as (HKM & HKT).
assert (Hn26 : 0 <= d_n cx < 2 ^ 26).
{ clear - HB. unfold dec_a_base, dec_lib_pre_x in HB.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : (d_n cx = 0 /\ _) \/ (0 < d_n cx < 2 ^ 26 /\ _) |- _ =>
    destruct H as [[Hz _] | [Hz _]]; lia end. }
assert (Hlenpl : d_n cx = Z.of_nat (length (d_pl cx)))
  by (clear - HB; unfold dec_a_base, dec_lib_pre_x in HB; decompose [and] HB; assumption).
assert (Hlen : 0 <= dec_a_len (d_n cx) < 2 ^ 26) by (unfold dec_a_len; lia).
pose proof (req_size_pos0 (dec_a_len (d_n cx)) ltac:(unfold dec_a_len; lia)) as Hreq.
pose proof (cp_regs1_ok cx regs res mode nch ns H20 H18 H26 H25 H23 H22 HFR ltac:(lia)) as HREGS.
pose proof (cp_seat fx 0x254 cp_regs1 cx ly S W regs mem md res mode nch ns HREGS
  HC Hres ltac:(lia) Hr16 HMODE HSLOT HKM HKT Hm0 Hm1 Hm8 HmD HFhi) as HS.
pose proof (cp_E_eqs regs cx res mode nch ns) as EQS. cbv zeta in EQS.
set (E := Eimg (Ereg regs (cp_extra cx res mode nch ns))) in HS, HREGS, EQS.
destruct EQS as (E2 & E3 & E4 & E9 & E32 & E33 & E34 & E35 & E36 & E38 & E39 & E40 & E41 & E42 & E7o & E8o).
assert (E10 : ew E 10 = getr regs 10)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Us1 : bv_unsigned (ew E 9) = d_sp1 cx) by (rewrite E9, Hs1; unfold w64; apply unsigned_lit_small; lia).
assert (AG : forall n, (n < 512)%nat -> ew E n = ew E n) by reflexivity.
clearbody E.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (cp_kept_refl W mem (d_sp1 cx - 4096) (d_sp1 cx + 96)) as KEPT.
pose (RUN := @paj_run fx rc dec_A_sink_head decode_listing PL_decode (@PI_decode rc) B LAWS).
pose (BR := @paj_branch fx rc decode_listing (@PI_decode rc)).
change (w64 (DEC_A_LLVMF + 0x254)) with (Z_to_bv 64 (VAL A_TEXT + 0x254)).
change (YK11.seg_rom decodesegs0) with (YK11.seg_rom SEGS).
paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
cp_kupd KEPT.
cp_env HS AG.
pmkst HS.
apply SRr_ret.
cp_reg HS (10%bv : bv 5) Ra0. cp_reg HS (11%bv : bv 5) Ra1. cp_reg HS (1%bv : bv 5) Rra.
exists fx, ly, S. eexists _, _, _. split; [reflexivity|]. split; [exact Hfrm|].
  split; [apply (cp_core_xfer cx res mode nch ns ly S W regs mem md _ _ _ LAWS HCELLS Hlenpl HCORE HJc KEPT);
          cp_agree HS HREGS AG|].
  split; [|exact (cp_filled_kept cx res W mem _ _ _ KEPT ltac:(lia) ltac:(lia) ltac:(lia) Hlenpl HFILL)].
  split; [split; [transitivity (YK11.getr regs 25); [cp_same HS HREGS AG | exact H25]
                 | transitivity (YK11.getr regs 23); [cp_same HS HREGS AG | exact H23]]|].
split; [rewrite Ra0, (cp_denot_off E 33 res 0 E33), Z.add_0_r by lia; reflexivity|].
split; [rewrite Ra1, (cp_denot_off E 34 _ 0 E34), Z.add_0_r by lia; reflexivity|].
rewrite Rra. etransitivity; [apply codeptr_val; assumption|]. rewrite cp_base. reflexivity.
Qed.

(* +0x2b4 .. +0x2c0: `li a1, 0`, the abort edge `bne a0, a1` (+0x2b8, refuted: is_reac returned 0), `mv a0, s10`,
   and reac_frame_clean_len (len). *)
Lemma cp_stage_d : forall (fx : YK11.FPState) (cx : dctx) (res mode nch ns : Z) ly S (W : world decodesegs0) regs mem md,
  AR_laws decodesegs0 B -> dec_crt_cells B ->
  (forall a, dec_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx -> dec_a_rom cx ->
  frm_zero (@fp_csr fx) ->
  cp_core B MT cx res mode nch ns ly S W regs mem md -> cp_rm mode regs -> cp_filled cx res W mem ->
  YK11.getr regs 10 = w64 0 ->
  SRr decodesegs0 W (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x2b4)) mem (YK11.seg_rom decodesegs0)) md)
    (cp_at B MT (Z_to_bv 64 (decode_sigma DS_reac_frame_clean_len)) cx res mode nch ns
       (fun r => cp_rm mode r /\ YK11.getr r 10 = w64 (dec_a_len (d_n cx)) /\
                 YK11.getr r 1 = w64 (DEC_A_LLVMF + 0x2c4))
       (cp_filled cx res)).
Proof.
intros fx cx res mode nch ns ly S W regs mem md LAWS HCELLS HSC HB HR Hfrm HCORE HRM HFILL H10.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof HCORE as (HC & Hbl & Hres & MLE & MOK & HFR & H18 & H20 & H22 & H26 & HMODE & HFSH & HSLOT).
pose proof HRM as (H25 & H23).
pose proof HC as (HJc & Hfrs & Hs0 & Hs1 & Hsp & Hsp1 & Hsp1m & Hgp & Htp & HSAV & HF4096 & HFmod & HFpres & HFL &
  Hblk & HGARR).
pose proof HJc as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
unfold DEC_LLVMF_STK in *.
assert (Hfin : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Hfa : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds decodesegs0 B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hfin) as (_ & HFhi & _).
rewrite Hfa in HFhi. change (fs_frame_bytes DEC_FCLASS) with 64 in HFhi.
assert (Hinr : In (res, dec_a_len (d_n cx)) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (Hr16 & _ & Hrceil & Hrapp & _).
destruct (cp_mode_facts B cx ly S W mem md mode nch ns HCELLS LAWS HAR Hfin Hfa HF4096 HFmod HFSH HMODE)
  as (Hm0 & Hm1 & Hm8 & HmD & HmS4 & HmS8 & HmB).
destruct (cp_rom_div B cx [(DEC_FCLASS, d_fpos cx)] ly S W mem md dec_ev_234 HSC HR HJc) as (HKM & HKT).
assert (Hn26 : 0 <= d_n cx < 2 ^ 26).
{ clear - HB. unfold dec_a_base, dec_lib_pre_x in HB.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : (d_n cx = 0 /\ _) \/ (0 < d_n cx < 2 ^ 26 /\ _) |- _ =>
    destruct H as [[Hz _] | [Hz _]]; lia end. }
assert (Hlenpl : d_n cx = Z.of_nat (length (d_pl cx)))
  by (clear - HB; unfold dec_a_base, dec_lib_pre_x in HB; decompose [and] HB; assumption).
assert (Hlen : 0 <= dec_a_len (d_n cx) < 2 ^ 26) by (unfold dec_a_len; lia).
pose proof (req_size_pos0 (dec_a_len (d_n cx)) ltac:(unfold dec_a_len; lia)) as Hreq.
pose proof (cp_regs1_ok cx regs res mode nch ns H20 H18 H26 H25 H23 H22 HFR ltac:(lia)) as HREGS.
pose proof (cp_seat fx 0x2b4 cp_regs1 cx ly S W regs mem md res mode nch ns HREGS
  HC Hres ltac:(lia) Hr16 HMODE HSLOT HKM HKT Hm0 Hm1 Hm8 HmD HFhi) as HS.
pose proof (cp_E_eqs regs cx res mode nch ns) as EQS. cbv zeta in EQS.
set (E := Eimg (Ereg regs (cp_extra cx res mode nch ns))) in HS, HREGS, EQS.
destruct EQS as (E2 & E3 & E4 & E9 & E32 & E33 & E34 & E35 & E36 & E38 & E39 & E40 & E41 & E42 & E7o & E8o).
assert (E10 : ew E 10 = getr regs 10)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Us1 : bv_unsigned (ew E 9) = d_sp1 cx) by (rewrite E9, Hs1; unfold w64; apply unsigned_lit_small; lia).
assert (AG : forall n, (n < 512)%nat -> ew E n = ew E n) by reflexivity.
clearbody E.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (cp_kept_refl W mem (d_sp1 cx - 4096) (d_sp1 cx + 96)) as KEPT.
pose (RUN := @paj_run fx rc dec_A_sink_head decode_listing PL_decode (@PI_decode rc) B LAWS).
pose (BR := @paj_branch fx rc decode_listing (@PI_decode rc)).
change (w64 (DEC_A_LLVMF + 0x2b4)) with (Z_to_bv 64 (VAL A_TEXT + 0x2b4)).
change (YK11.seg_rom decodesegs0) with (YK11.seg_rom SEGS).
paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
cp_kupd KEPT.
cp_env HS AG.
psrr_branch_tok RUN BR HS SHOK Bspan.
all: rewrite branch_ne_U, (U_atom _ 10 0 ltac:(rewrite AG by lia; rewrite E10; exact H10)), U_lit in Hc by lia.
1: (exfalso; cbn in Hc; discriminate).
paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
cp_kupd KEPT.
cp_env HS AG.
pmkst HS.
apply SRr_ret.
cp_reg HS (10%bv : bv 5) Ra0. cp_reg HS (1%bv : bv 5) Rra.
exists fx, ly, S. eexists _, _, _. split; [reflexivity|]. split; [exact Hfrm|].
  split; [apply (cp_core_xfer cx res mode nch ns ly S W regs mem md _ _ _ LAWS HCELLS Hlenpl HCORE HJc KEPT);
          cp_agree HS HREGS AG|].
  split; [|exact (cp_filled_kept cx res W mem _ _ _ KEPT ltac:(lia) ltac:(lia) ltac:(lia) Hlenpl HFILL)].
  split; [split; [transitivity (YK11.getr regs 25); [cp_same HS HREGS AG | exact H25]
                 | transitivity (YK11.getr regs 23); [cp_same HS HREGS AG | exact H23]]|].
split; [rewrite Ra0, (cp_denot_off E 34 _ 0 E34), Z.add_0_r by lia; reflexivity|].
rewrite Rra. etransitivity; [apply codeptr_val; assumption|]. rewrite cp_base. reflexivity.
Qed.

(* The copy's bytes, as cp_filled lists them. *)
Lemma cp_body_nth : forall (cx : dctx) (i : nat), nth i (cp_body cx) 0 = bv_unsigned (nth i (d_body cx) (Z_to_bv 8 0)).
Proof. intros cx i. unfold cp_body. exact (map_nth (fun b : byte => bv_unsigned b) (d_body cx) (Z_to_bv 8 0) i). Qed.
Lemma cp_cbody_len : forall (cx : dctx), d_n cx = Z.of_nat (length (d_pl cx)) ->
  Z.of_nat (length (cp_body cx)) = dec_a_len (d_n cx).
Proof. intros cx Hl. unfold cp_body, d_body. rewrite length_map, length_skipn. unfold dec_a_len, dec_a_u. lia. Qed.

(* +0x29c .. +0x2a4: `lbu a1; addi a1, a1, -25; sltiu a1, a1, 1` is b13 = 25. *)
Lemma cp_b13_test : forall (E : env) b, ew E 42 = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_SLTU (SAlu ALU_ADD (SExt false 8 (SOff 42 0)) (SLit (-25))) (SLit 1)) = if b =? 25 then 1 else 0.
Proof.
intros E b Hb Hr.
rewrite !U_SAlu, U_SExt, (U_atom E 42 b Hb), !U_SLit by lia. cbn [zalu_raw Z.of_N]. unfold zcanon, M64.
destruct (Z.eqb_spec b 25) as [-> | Hne]; [vm_compute; reflexivity|].
match goal with |- (if ?c then 1 else 0) mod _ = 0 => replace c with false; [reflexivity|] end.
symmetry. apply Z.ltb_ge. rewrite (Z.mod_small 1) by lia. rewrite (Z.mod_small (b mod 2 ^ 8)) by (pose proof (Z.mod_pos_bound b (2 ^ 8)); lia).
rewrite (Z.mod_small b (2 ^ 8)) by lia.
assert (H1 : (-25) mod 2 ^ 64 = 2 ^ 64 - 25) by reflexivity. rewrite H1.
destruct (Z_lt_ge_dec b 25).
- rewrite Z.mod_small by lia. lia.
- replace (b + (2 ^ 64 - 25)) with ((b - 25) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* +0x260 .. +0x2c0: `li a1, 14; bltu s10, a1` (+0x264), the two shadow-checked header reads at res + 12 / res + 13
   (+0x268 .. +0x29c, slow paths refuted by the copy's block), `bne b12, 136` (+0x284), the abort edge
   `bne a0, a1` (+0x2b8, refuted by is_reac's result), `mv a0, s10`, and reac_frame_clean_len (len). *)
Lemma cp_stage_c : forall (fx : YK11.FPState) (cx : dctx) (res mode nch ns : Z) ly S (W : world decodesegs0) regs mem md,
  AR_laws decodesegs0 B -> dec_crt_cells B ->
  (forall a, dec_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx -> dec_a_rom cx ->
  frm_zero (@fp_csr fx) ->
  cp_core B MT cx res mode nch ns ly S W regs mem md -> cp_rm mode regs -> cp_filled cx res W mem ->
  YK11.getr regs 10 = w64 (CIR.is_reac_result res (dec_a_len (d_n cx)) (d_body cx)) ->
  SRr decodesegs0 W (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x260)) mem (YK11.seg_rom decodesegs0)) md)
    (cp_at B MT (Z_to_bv 64 (decode_sigma DS_reac_frame_clean_len)) cx res mode nch ns
       (fun r => cp_rm mode r /\ YK11.getr r 10 = w64 (dec_a_len (d_n cx)) /\
                 YK11.getr r 1 = w64 (DEC_A_LLVMF + 0x2c4))
       (cp_filled cx res)).
Proof.
intros fx cx res mode nch ns ly S W regs mem md LAWS HCELLS HSC HB HR Hfrm HCORE HRM HFILL H10.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof HCORE as (HC & Hbl & Hres & MLE & MOK & HFR & H18 & H20 & H22 & H26 & HMODE & HFSH & HSLOT).
pose proof HRM as (H25 & H23).
pose proof HC as (HJc & Hfrs & Hs0 & Hs1 & Hsp & Hsp1 & Hsp1m & Hgp & Htp & HSAV & HF4096 & HFmod & HFpres & HFL &
  Hblk & HGARR).
pose proof HJc as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
unfold DEC_LLVMF_STK in *.
assert (Hfin : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Hfa : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds decodesegs0 B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hfin) as (_ & HFhi & _).
rewrite Hfa in HFhi. change (fs_frame_bytes DEC_FCLASS) with 64 in HFhi.
assert (Hinr : In (res, dec_a_len (d_n cx)) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (Hr16 & _ & Hrceil & Hrapp & _).
destruct (cp_mode_facts B cx ly S W mem md mode nch ns HCELLS LAWS HAR Hfin Hfa HF4096 HFmod HFSH HMODE)
  as (Hm0 & Hm1 & Hm8 & HmD & HmS4 & HmS8 & HmB).
destruct (cp_rom_div B cx [(DEC_FCLASS, d_fpos cx)] ly S W mem md dec_ev_234 HSC HR HJc) as (HKM & HKT).
assert (Hn26 : 0 <= d_n cx < 2 ^ 26).
{ clear - HB. unfold dec_a_base, dec_lib_pre_x in HB.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : (d_n cx = 0 /\ _) \/ (0 < d_n cx < 2 ^ 26 /\ _) |- _ =>
    destruct H as [[Hz _] | [Hz _]]; lia end. }
assert (Hlenpl : d_n cx = Z.of_nat (length (d_pl cx)))
  by (clear - HB; unfold dec_a_base, dec_lib_pre_x in HB; decompose [and] HB; assumption).
assert (Hlen : 0 <= dec_a_len (d_n cx) < 2 ^ 26) by (unfold dec_a_len; lia).
pose proof (req_size_pos0 (dec_a_len (d_n cx)) ltac:(unfold dec_a_len; lia)) as Hreq.
pose proof (cp_regs1_ok cx regs res mode nch ns H20 H18 H26 H25 H23 H22 HFR ltac:(lia)) as HREGS.
pose proof (cp_seat fx 0x260 cp_regs1 cx ly S W regs mem md res mode nch ns HREGS
  HC Hres ltac:(lia) Hr16 HMODE HSLOT HKM HKT Hm0 Hm1 Hm8 HmD HFhi) as HS.
pose proof (cp_E_eqs regs cx res mode nch ns) as EQS. cbv zeta in EQS.
set (E := Eimg (Ereg regs (cp_extra cx res mode nch ns))) in HS, HREGS, EQS.
destruct EQS as (E2 & E3 & E4 & E9 & E32 & E33 & E34 & E35 & E36 & E38 & E39 & E40 & E41 & E42 & E7o & E8o).
assert (E10 : ew E 10 = getr regs 10)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Us1 : bv_unsigned (ew E 9) = d_sp1 cx) by (rewrite E9, Hs1; unfold w64; apply unsigned_lit_small; lia).
assert (AG : forall n, (n < 512)%nat -> ew E n = ew E n) by reflexivity.
clearbody E.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (cp_kept_refl W mem (d_sp1 cx - 4096) (d_sp1 cx + 96)) as KEPT.
pose (RUN := @paj_run fx rc dec_A_sink_head decode_listing PL_decode (@PI_decode rc) B LAWS).
pose (BR := @paj_branch fx rc decode_listing (@PI_decode rc)).
change (w64 (DEC_A_LLVMF + 0x260)) with (Z_to_bv 64 (VAL A_TEXT + 0x260)).
change (YK11.seg_rom decodesegs0) with (YK11.seg_rom SEGS).
assert (HIR : 0 <= CIR.is_reac_result res (dec_a_len (d_n cx)) (d_body cx) <= 1)
  by (unfold CIR.is_reac_result; repeat destruct (_ && _)%bool; destruct (_ || _)%bool; lia).
paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
cp_kupd KEPT.
cp_env HS AG.
psrr_branch_tok RUN BR HS SHOK Bspan.
all: rewrite branch_ltu_U, (U_atom _ 34 (dec_a_len (d_n cx)) ltac:(rewrite AG by lia; exact E34)), U_lit in Hc by lia.
- (* len < 14: is_reac returned 0, the abort edge at +0x2b8 is refuted *)
  apply Z.ltb_lt in Hc. rename Hc into Hlt.
  assert (HIR0 : CIR.is_reac_result res (dec_a_len (d_n cx)) (d_body cx) = 0)
    by (unfold CIR.is_reac_result; rewrite (proj2 (Z.ltb_lt _ _) Hlt), orb_true_r; reflexivity).
  paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
  cp_kupd KEPT.
  cp_env HS AG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  all: rewrite branch_ne_U, (U_atom _ 10 _ ltac:(rewrite AG by lia; rewrite E10; exact H10)), U_lit in Hc by lia.
  1: (exfalso; rewrite HIR0 in Hc; cbn in Hc; discriminate).
  paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
  cp_kupd KEPT.
  cp_env HS AG.
  pmkst HS.
  apply SRr_ret.
  cp_reg HS (10%bv : bv 5) Ra0. cp_reg HS (1%bv : bv 5) Rra.
  exists fx, ly, S. eexists _, _, _. split; [reflexivity|]. split; [exact Hfrm|].
    split; [apply (cp_core_xfer cx res mode nch ns ly S W regs mem md _ _ _ LAWS HCELLS Hlenpl HCORE HJc KEPT);
            cp_agree HS HREGS AG|].
    split; [|exact (cp_filled_kept cx res W mem _ _ _ KEPT ltac:(lia) ltac:(lia) ltac:(lia) Hlenpl HFILL)].
    split; [split; [transitivity (YK11.getr regs 25); [cp_same HS HREGS AG | exact H25]
                   | transitivity (YK11.getr regs 23); [cp_same HS HREGS AG | exact H23]]|].
  split; [rewrite Ra0; erewrite (cp_denot_off _ 34%nat); [rewrite Z.add_0_r; reflexivity | try rewrite (AG 34%nat) by lia; exact E34 | lia]|].
  rewrite Rra. etransitivity; [apply codeptr_val; assumption|]. rewrite cp_base. reflexivity.
- (* len >= 14: the header reads *)
  apply Z.ltb_ge in Hc. rename Hc into Hge.
  pose proof (cp_cbody_len cx Hlenpl) as HBL.
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) |- _ =>
    pose proof (cp_filled_kept cx res W mem (ms_mem msx) _ _ KEPT ltac:(lia) ltac:(lia) ltac:(lia) Hlenpl HFILL) as HF1;
    assert (HRs : region_ok SEGS Ex (ms_mem (restrict (w_H W) msx)) cp_res);
    [ unfold region_ok; cbn [cp_res YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val
        ms_mem restrict];
      try rewrite (AG 33%nat) by lia; rewrite E33, unsigned_lit_small by lia;
      split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
      constructor; [|constructor; [|constructor]];
      [ apply (chunk_ok_val decodesegs0 Ex _ res 12 1 (SOff 41 0) (bv_unsigned (nth 12 (d_body cx) (Z_to_bv 8 0))));
        [ cbn [sv_denot]; try rewrite (AG 41%nat) by lia; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (bv_unsigned_in_range 8 (nth 12 (d_body cx) (Z_to_bv 8 0))) as Hb; change (bv_modulus 8) with 256 in Hb; zside
        | zside
        | destruct (HF1 12%nat ltac:(lia)) as [Hv _]; rewrite cp_body_nth in Hv; exact Hv ]
      | apply (chunk_ok_val decodesegs0 Ex _ res 13 1 (SOff 42 0) (bv_unsigned (nth 13 (d_body cx) (Z_to_bv 8 0))));
        [ cbn [sv_denot]; try rewrite (AG 42%nat) by lia; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (bv_unsigned_in_range 8 (nth 13 (d_body cx) (Z_to_bv 8 0))) as Hb; change (bv_modulus 8) with 256 in Hb; zside
        | zside
        | destruct (HF1 13%nat ltac:(lia)) as [Hv _]; rewrite cp_body_nth in Hv; exact Hv ] ]
    | ];
    pose proof (st_ok_pi_add_region Ex ssx _ cp_res HS eq_refl HRs) as HS1;
    assert (Ures : bv_unsigned (ew Ex 33) = res)
      by (try rewrite (AG 33%nat) by lia; rewrite E33; apply unsigned_lit_small; lia);
    assert (Us1x : bv_unsigned (ew Ex 9) = d_sp1 cx) by (try rewrite (AG 9%nat) by lia; exact Us1);
    assert (Umode : bv_unsigned (ew Ex 35) = mode)
      by (try rewrite (AG 35%nat) by lia; rewrite E35; apply unsigned_lit_small; lia);
    assert (UKM : bv_unsigned (ew Ex 248) = CCL.A_M)
      by (change 248%nat with (A_OBJ 7); try rewrite (AG (A_OBJ 7)) by (cbv; lia); rewrite E7o;
          apply unsigned_lit_small; unfold CCL.A_M; lia);
    assert (UKT : bv_unsigned (ew Ex 249) = CCL.A_T)
      by (change 249%nat with (A_OBJ 8); try rewrite (AG (A_OBJ 8)) by (cbv; lia); rewrite E8o;
          apply unsigned_lit_small; unfold CCL.A_T; lia) end.
  pose proof (blk_off_imgP B ly S W mem md res _ HAR Hinr) as Hroff. unfold off_img in Hroff.
  pose proof IMG_LO_val as HLO. pose proof IMG_TOP_val as HTOP.
  pose proof (HmB res _ Hinr) as HmR.
  match type of HS1 with ?A -> _ => assert (HDJ : A);
    [ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
        let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint, cp_res; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite Ures, Us1x, Umode, UKM, UKT; unfold CCL.A_M, CCL.A_T in *; repeat split; lia
    | specialize (HS1 HDJ); clear HS HDJ; rename HS1 into HS ] end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
  set (b12 := bv_unsigned (nth 12 (d_body cx) (Z_to_bv 8 0))) in *.
  set (b13 := bv_unsigned (nth 13 (d_body cx) (Z_to_bv 8 0))) in *.
  assert (Hb12 : 0 <= b12 < 256)
    by (subst b12; pose proof (bv_unsigned_in_range 8 (nth 12 (d_body cx) (Z_to_bv 8 0))) as Hb;
        change (bv_modulus 8) with 256 in Hb; lia).
  assert (Hb13 : 0 <= b13 < 256)
    by (subst b13; pose proof (bv_unsigned_in_range 8 (nth 13 (d_body cx) (Z_to_bv 8 0))) as Hb;
        change (bv_modulus 8) with 256 in Hb; lia).
  (* +0x268 .. +0x284: the shadow of res + 12 (the copy's block), b12, and `bne b12, 136` *)
  paj_run_tok RUN HS HJc SHOK Bspan;
    [ rewrite (U_atom _ 32 SB ltac:(try rewrite (AG 32%nat) by lia; exact E32)) by (unfold SB; lia);
      rewrite (U_atom_off _ 33 res 12 ltac:(try rewrite (AG 33%nat) by lia; exact E33)) by lia;
      eapply (range_addressable_of_block decodesegs0 B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJc) Hinr); lia
    | cp_awr |].
  cp_kupd KEPT.
  cp_env HS AG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  all: rewrite branch_ne_U, U_SExt, (U_atom _ 41 b12 ltac:(try rewrite (AG 41%nat) by lia; exact E41)), U_lit in Hc
         by lia.
  all: cbn [Z.of_N] in Hc; rewrite (Z.mod_small b12) in Hc by lia; rewrite zcanon_id in Hc by (unfold M64; lia).
  + (* b12 <> 136: is_reac returned 0 *)
    apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hb12ne.
    assert (HIR0 : CIR.is_reac_result res (dec_a_len (d_n cx)) (d_body cx) = 0).
    { unfold CIR.is_reac_result, CIR.is_reac_byte. change (bv_unsigned (nth 12 (d_body cx) (Z_to_bv 8 0))) with b12.
      replace (res =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (dec_a_len (d_n cx) <? 14) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (b12 =? 136) with false by (symmetry; apply Z.eqb_neq; exact Hb12ne). reflexivity. }
    paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
    cp_kupd KEPT. cp_env HS AG.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    { exfalso; rewrite branch_ne_U, (U_atom _ 10 _ ltac:(rewrite AG by lia; rewrite E10; exact H10)), U_lit in Hc by lia.
      rewrite HIR0 in Hc. cbn in Hc. discriminate. }
    paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
    cp_kupd KEPT. cp_env HS AG. pmkst HS. apply SRr_ret.
    cp_reg HS (10%bv : bv 5) Ra0. cp_reg HS (1%bv : bv 5) Rra.
    exists fx, ly, S. eexists _, _, _. split; [reflexivity|]. split; [exact Hfrm|].
    split; [apply (cp_core_xfer cx res mode nch ns ly S W regs mem md _ _ _ LAWS HCELLS Hlenpl HCORE HJc KEPT);
            cp_agree HS HREGS AG|].
    split; [|exact (cp_filled_kept cx res W mem _ _ _ KEPT ltac:(lia) ltac:(lia) ltac:(lia) Hlenpl HFILL)].
    split; [split; [transitivity (YK11.getr regs 25); [cp_same HS HREGS AG | exact H25]
                   | transitivity (YK11.getr regs 23); [cp_same HS HREGS AG | exact H23]]|].
    split; [rewrite Ra0; erewrite (cp_denot_off _ 34%nat); [rewrite Z.add_0_r; reflexivity | try rewrite (AG 34%nat) by lia; exact E34 | lia]|].
    rewrite Rra. etransitivity; [apply codeptr_val; assumption|]. rewrite cp_base. reflexivity.
  + (* b12 = 136: the shadow of res + 13, b13, a1 = (b13 = 25) *)
    apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb12eq.
    paj_run_tok RUN HS HJc SHOK Bspan;
      [ rewrite (U_atom _ 32 SB ltac:(try rewrite (AG 32%nat) by lia; exact E32)) by (unfold SB; lia);
        rewrite (U_atom_off _ 33 res 13 ltac:(try rewrite (AG 33%nat) by lia; exact E33)) by lia;
        eapply (range_addressable_of_block decodesegs0 B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJc) Hinr); lia
      | cp_awr |].
    cp_kupd KEPT.
    cp_env HS AG.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    all: rewrite branch_ne_U, (U_atom _ 10 _ ltac:(rewrite AG by lia; rewrite E10; exact H10)),
           (cp_b13_test _ b13 ltac:(rewrite AG by lia; exact E42) Hb13) in Hc by lia.
    assert (HIRb : CIR.is_reac_result res (dec_a_len (d_n cx)) (d_body cx) = if b13 =? 25 then 1 else 0).
    { unfold CIR.is_reac_result, CIR.is_reac_byte.
      change (bv_unsigned (nth 12 (d_body cx) (Z_to_bv 8 0))) with b12.
      change (bv_unsigned (nth 13 (d_body cx) (Z_to_bv 8 0))) with b13.
      replace (res =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (dec_a_len (d_n cx) <? 14) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite Hb12eq. reflexivity. }
    { exfalso. rewrite HIRb, Z.eqb_refl in Hc. cbn in Hc. discriminate. }
    paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
    cp_kupd KEPT. cp_env HS AG. pmkst HS. apply SRr_ret.
    cp_reg HS (10%bv : bv 5) Ra0. cp_reg HS (1%bv : bv 5) Rra.
    exists fx, ly, S. eexists _, _, _. split; [reflexivity|]. split; [exact Hfrm|].
    split; [apply (cp_core_xfer cx res mode nch ns ly S W regs mem md _ _ _ LAWS HCELLS Hlenpl HCORE HJc KEPT);
            cp_agree HS HREGS AG|].
    split; [|exact (cp_filled_kept cx res W mem _ _ _ KEPT ltac:(lia) ltac:(lia) ltac:(lia) Hlenpl HFILL)].
    split; [split; [transitivity (YK11.getr regs 25); [cp_same HS HREGS AG | exact H25]
                   | transitivity (YK11.getr regs 23); [cp_same HS HREGS AG | exact H23]]|].
    split; [rewrite Ra0; erewrite (cp_denot_off _ 34%nat); [rewrite Z.add_0_r; reflexivity | try rewrite (AG 34%nat) by lia; exact E34 | lia]|].
    rewrite Rra. etransitivity; [apply codeptr_val; assumption|]. rewrite cp_base. reflexivity.
Qed.

(* The clean length (lib/A/Prog/reac_frame_clean_len_c.v): the input length, or two less when the length is
   54 + a multiple of 36. *)
Lemma cp_clean_cases : forall n, 0 <= n ->
  (CCL.reac_frame_clean_len_model n = n /\ ~ (54 <= n /\ (n - 54) mod 36 = 0)) \/
  (CCL.reac_frame_clean_len_model n = n - 2 /\ 54 <= n /\ (n - 54) mod 36 = 0).
Proof.
intros n Hn. unfold CCL.reac_frame_clean_len_model.
destruct (54 <=? n) eqn:E1; destruct ((n - 52) mod 36 =? 2) eqn:E2; cbn [andb].
- right. apply Z.leb_le in E1. apply Z.eqb_eq in E2. split; [reflexivity|]. split; [lia|].
  Z.div_mod_to_equations. lia.
- left. split; [reflexivity|]. apply Z.eqb_neq in E2. intros [H1 H2]. apply E2. Z.div_mod_to_equations. lia.
- left. split; [reflexivity|]. apply Z.leb_gt in E1. lia.
- left. split; [reflexivity|]. apply Z.leb_gt in E1. lia.
Qed.

(* The value of a 32-bit ALU result, as U_SAlu is for the 64-bit ones. *)
Lemma cp_U_SAluw : forall E op a b,
  U E (SAluw op a b) = zcanon (bv_swrap 32 (zalu_raw 31 32 op (U E a mod 2 ^ 32) (U E b mod 2 ^ 32))).
Proof. intros E op a b. rewrite U_of_S, S_SAluw. reflexivity. Qed.

(* +0x338 .. +0x33c: `xor a0, a0, s10; snez a0, a0` is 1 exactly when the two registers differ. *)
Lemma cp_snez_xor : forall E a b,
  U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR a b)) = if U E a =? U E b then 0 else 1.
Proof.
intros E a b. rewrite !U_SAlu, U_SLit. cbn [zalu_raw].
pose proof (U_range E a) as Ha. pose proof (U_range E b) as Hb. unfold M64 in Ha, Hb.
pose proof (OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib.PropExec.Z_lxor_range _ _ Ha Hb) as Hx.
rewrite (zcanon_id (Z.lxor _ _)) by (unfold M64; lia).
destruct (Z.eqb_spec (U E a) (U E b)) as [He | Hne].
- rewrite He, Z.lxor_nilpotent. reflexivity.
- assert (Hnz : Z.lxor (U E a) (U E b) <> 0) by (rewrite Z.lxor_eq_0_iff; exact Hne).
  change (zcanon 0) with 0. destruct (0 <? Z.lxor (U E a) (U E b)) eqn:Hl; [reflexivity|].
  apply Z.ltb_ge in Hl. lia.
Qed.

(* Disjoint bits: a value below 2 ^ k or-ed with a multiple of 2 ^ k is their sum
   (lib/A/Prog/reac_frame_clean_len.v lor_low, the same text). *)
Lemma cp_lor_low : forall k x y, 0 <= k -> 0 <= x < 2 ^ k -> 0 <= y -> Z.lor x (y * 2 ^ k) = y * 2 ^ k + x.
Proof.
intros k x y Hk Hx Hy. rewrite <- Z.shiftl_mul_pow2 by lia.
assert (H0 : Z.land x (Z.shiftl y k) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k).
  - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite <- (Z.mod_small x (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
rewrite <- (Z.lxor_lor _ _ H0), <- (Z.add_nocarry_lxor _ _ H0), Z.shiftl_mul_pow2 by lia. lia.
Qed.

(* `slliw a2, a1, 30` on the low word v: its two low bits land in bits 30 and 31, and bit 31 sign-extends. *)
Definition cp_y30 (r : Z) : Z :=
  (if r =? 0 then 0 else if r =? 1 then 1 else if r =? 2 then 2 ^ 34 - 2 else 2 ^ 34 - 1) * 2 ^ 30.
Lemma cp_sllw30 : forall v, 0 <= v < 2 ^ 32 -> zcanon (bv_swrap 32 (Z.shiftl v 30)) = cp_y30 (v mod 4).
Proof.
intros v Hv. rewrite Z.shiftl_mul_pow2 by lia.
pose proof (Z.div_mod v 4 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound v 4 ltac:(lia)) as Hr.
set (q := v / 4) in *. set (r := v mod 4) in *. clearbody q r. subst v.
unfold bv_swrap, bv_wrap, zcanon.
replace ((4 * q + r) * 2 ^ 30 + bv_half_modulus 32) with ((r * 2 ^ 30 + 2 ^ 31) + q * bv_modulus 32)
  by (change (bv_half_modulus 32) with (2 ^ 31); change (bv_modulus 32) with (2 ^ 32); ring).
rewrite Z.mod_add by (change (bv_modulus 32) with (2 ^ 32); lia).
assert (Hr4 : r = 0 \/ r = 1 \/ r = 2 \/ r = 3) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

(* `srliw a1, a1, 2; or a1, a1, a2; sltu a1, a1, 119304648` on the low word v. *)
Lemma cp_rot32 : forall v, 0 <= v < 2 ^ 32 ->
  zcanon (if zcanon (Z.lor (zcanon (bv_swrap 32 (Z.shiftr v 2))) (zcanon (bv_swrap 32 (Z.shiftl v 30))))
             <? 119304648 then 1 else 0) =
  if (v mod 4 =? 0) && (v / 4 <? 119304648) then 1 else 0.
Proof.
intros v Hv. rewrite (cp_sllw30 v Hv).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
assert (Hq : 0 <= v / 4 < 2 ^ 30) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Eq : zcanon (bv_swrap 32 (v / 4)) = v / 4).
{ unfold bv_swrap, bv_wrap, zcanon, M64. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). rewrite (Z.mod_small (v / 4 + 2 ^ 31)) by lia.
  rewrite Z.add_simpl_r. apply Z.mod_small. lia. }
rewrite Eq.
pose proof (Z.mod_pos_bound v 4 ltac:(lia)) as Hr.
set (q := v / 4) in *. set (r := v mod 4) in *. clearbody q r.
assert (Hr4 : r = 0 \/ r = 1 \/ r = 2 \/ r = 3) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]].
- change (cp_y30 0) with 0. rewrite Z.lor_0_r. unfold zcanon, M64. rewrite (Z.mod_small q) by lia.
  destruct (q <? 119304648); reflexivity.
- change (cp_y30 1) with (1 * 2 ^ 30). rewrite cp_lor_low by lia. unfold zcanon, M64.
  rewrite (Z.mod_small (1 * 2 ^ 30 + q)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
- change (cp_y30 2) with ((2 ^ 34 - 2) * 2 ^ 30). rewrite cp_lor_low by lia. unfold zcanon, M64.
  rewrite (Z.mod_small ((2 ^ 34 - 2) * 2 ^ 30 + q)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
- change (cp_y30 3) with ((2 ^ 34 - 1) * 2 ^ 30). rewrite cp_lor_low by lia. unfold zcanon, M64.
  rewrite (Z.mod_small ((2 ^ 34 - 1) * 2 ^ 30 + q)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

(* +0x308 .. +0x32c: the harness's `(len - 54) % 36 == 0` as the listing computes it (dec_div36_32). *)
Lemma cp_test32 : forall E len, U E (SOff 34 0) = len -> 54 <= len < 2 ^ 26 ->
  U E (SAlu ALU_SLTU
         (SAlu ALU_OR
            (SAluw ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff 34 0) (SLit 954437177)) (SLit (-6))) (SLit 2))
            (SAluw ALU_SLL (SAlu ALU_ADD (SMd M_MUL (SOff 34 0) (SLit 954437177)) (SLit (-6))) (SLit 30)))
         (SLit 119304648)) = if (len - 54) mod 36 =? 0 then 1 else 0.
Proof.
intros E len HU Hl.
assert (HX : U E (SAlu ALU_ADD (SMd M_MUL (SOff 34 0) (SLit 954437177)) (SLit (-6))) = len * 954437177 - 6).
{ rewrite U_SAlu, U_SMd, !U_SLit, HU. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
  change (954437177 mod 2 ^ 64) with 954437177. change ((-6) mod 2 ^ 64) with 18446744073709551610.
  rewrite (Z.mod_small (len * 954437177)) by lia.
  replace (len * 954437177 + 18446744073709551610) with ((len * 954437177 - 6) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
rewrite U_SAlu, U_SLit, U_SAlu, !cp_U_SAluw, HX, !U_SLit. cbn [zalu_raw].
change (Z.land (zcanon 2 mod 2 ^ 32) 31) with 2. change (Z.land (zcanon 30 mod 2 ^ 32) 31) with 30.
change (zcanon 119304648) with 119304648.
pose proof (Z.mod_pos_bound (len * 954437177 - 6) (2 ^ 32) ltac:(lia)) as Hv.
rewrite (cp_rot32 _ Hv).
exact (f_equal (fun b : bool => if b then 1 else 0) (dec_div36_32 len _ Hl eq_refl)).
Qed.

(* +0x2d8 .. +0x2f8 on a clean length c = 52 + 36 k: the engine's form of `ror ((c - 52) * KM, 2)` is k
   (dec_div36_64; the shifted-out half is c * KM * 2 ^ 62 = c * 2 ^ 62 mod 2 ^ 64 = 0 as 4 divides c). *)
Lemma cp_test64 : forall E c, bv_unsigned (ew E 10) = c -> 52 <= c < 2 ^ 26 -> (c - 52) mod 36 = 0 ->
  U E (SAlu ALU_OR (SAlu ALU_SRL (SMd M_MUL (SOff 10 (-52)) (SLit 10248191152060862009)) (SLit 2))
         (SMd M_MUL (SOff 10 0) (SLit 47261439850130342148203327256459739136))) = (c - 52) / 36.
Proof.
intros E c HV Hc Hm.
assert (Hm4 : c mod 4 = 0) by (Z.div_mod_to_equations; lia).
assert (Hq : 0 <= (c - 52) / 36 <= c) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
rewrite !U_SAlu, !U_SMd, !U_SOff, !U_SLit, HV. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
change (10248191152060862009 mod 2 ^ 64) with 10248191152060862009.
change (47261439850130342148203327256459739136 mod 2 ^ 64) with (2 ^ 62).
change (Z.land (2 mod 2 ^ 64) 63) with 2.
rewrite (Z.mod_small (c + -52)) by lia. rewrite Z.add_0_r, (Z.mod_small c) by lia.
replace (c + -52) with (c - 52) by lia.
rewrite (dec_div36_64 (c - 52)) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. rewrite (Z.mul_comm 4), Z.div_mul by lia.
replace (c * 2 ^ 62) with (c / 4 * 2 ^ 64) by (Z.div_mod_to_equations; lia).
rewrite Z.mod_mul by lia. rewrite (Z.mod_small ((c - 52) / 36)) by lia. rewrite Z.lor_0_r.
apply Z.mod_small. lia.
Qed.

(* A shadow fact at the entry's memory holds at a memory that kept every byte below lo: the shadow of the
   application window lies below 2 ^ 46. *)
Lemma cp_ra_kept : forall (W : world decodesegs0) m m0 lo hi a n,
  cp_kept W m m0 lo hi -> 0 <= a -> a + n <= 2 ^ 48 -> 2 ^ 46 <= lo ->
  range_addressable (aview decodesegs0 (w_H W) m0) SHADOW_OFF a n ->
  range_addressable (aview decodesegs0 (w_H W) m) SB a n.
Proof.
intros W m m0 lo hi a n K Ha Hn Hlo HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
assert (Hd : 0 <= x / 8 < 2 ^ 45) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
change SB with SHADOW_OFF. unfold shadow_of_addr in *. unfold cp_kept in K.
rewrite K; [exact Hs | unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia].
Qed.

(* Sign-wrapping the low bits of a small signed value gives it back. *)
Lemma cp_swrap32 : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 (x mod 2 ^ 32) = x.
Proof.
intros x Hx. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
change (bv_modulus 32) with (2 ^ 32). rewrite Z.add_mod_idemp_l by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma cp_swrap64 : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> bv_swrap 64 (x mod 2 ^ 64) = x.
Proof.
intros x Hx. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63).
change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* +0x360 / +0x36c: `lwu a3` of the nch field then `sext.w a0, a3`, and `lw a2` of the ns field: the two
   fields as 64-bit words. *)
Lemma cp_U_nch : forall E nch, ew E 39 = Z_to_bv 64 (nch mod 2 ^ 32) -> - 2 ^ 31 <= nch < 2 ^ 31 ->
  U E (SAluw ALU_ADD (SExt false 32 (SOff 39 0)) (SLit 0)) = nch mod 2 ^ 64.
Proof.
intros E nch H Hn. pose proof (Z.mod_pos_bound nch (2 ^ 32) ltac:(lia)) as Hm.
rewrite cp_U_SAluw, U_SExt, U_SLit, (U_atom E 39 _ H) by lia. cbv beta iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). change (zcanon 0 mod 2 ^ 32) with 0. rewrite Z.add_0_r.
rewrite (Z.mod_mod nch) by lia. rewrite (zcanon_id (nch mod 2 ^ 32)) by (unfold M64; lia).
rewrite (Z.mod_mod nch) by lia. rewrite cp_swrap32 by lia. reflexivity.
Qed.
Lemma cp_U_ns : forall E ns, ew E 40 = Z_to_bv 64 (ns mod 2 ^ 32) -> - 2 ^ 31 <= ns < 2 ^ 31 ->
  U E (SExt true 32 (SOff 40 0)) = ns mod 2 ^ 64.
Proof.
intros E ns H Hn. pose proof (Z.mod_pos_bound ns (2 ^ 32) ltac:(lia)) as Hm.
rewrite U_SExt, (U_atom E 40 _ H) by lia. cbv beta iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_mod ns) by lia. rewrite cp_swrap32 by lia. reflexivity.
Qed.

(* +0x374 .. +0x384: a0 = (0 < nch) & (0 < ns), the spill at 32(s1) and the test at +0x39c. *)
Lemma cp_fits : forall E nch ns, ew E 39 = Z_to_bv 64 (nch mod 2 ^ 32) -> ew E 40 = Z_to_bv 64 (ns mod 2 ^ 32) ->
  - 2 ^ 31 <= nch < 2 ^ 31 -> - 2 ^ 31 <= ns < 2 ^ 31 ->
  U E (SAlu ALU_AND (SAlu ALU_SLT (SLit 0) (SAluw ALU_ADD (SExt false 32 (SOff 39 0)) (SLit 0)))
         (SAlu ALU_SLT (SLit 0) (SExt true 32 (SOff 40 0)))) = dec_a_fits0 nch ns.
Proof.
intros E nch ns H39 H40 Hc Hs.
rewrite !U_SAlu, (cp_U_nch E nch H39 Hc), (cp_U_ns E ns H40 Hs), U_SLit. cbn [zalu_raw].
change (zcanon 0) with 0. change (bv_swrap 64 0) with 0. rewrite !cp_swrap64 by lia.
unfold dec_a_fits0. destruct (0 <? nch), (0 <? ns); reflexivity.
Qed.

(* `lwu a3` (+0x364) as a 64-bit word: the nch field's four bytes. *)
Lemma cp_U_nch32 : forall E nch, ew E 39 = Z_to_bv 64 (nch mod 2 ^ 32) ->
  U E (SExt false 32 (SOff 39 0)) = nch mod 2 ^ 32.
Proof.
intros E nch H. pose proof (Z.mod_pos_bound nch (2 ^ 32) ltac:(lia)) as Hm.
rewrite U_SExt, (U_atom E 39 _ H) by lia. cbv beta iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_mod nch) by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* `slli a2, a2, 32; srli s7, a2, 32` (+0x380, +0x388): s7 is the ns field zero-extended. *)
Lemma cp_U_s7 : forall E ns, ew E 40 = Z_to_bv 64 (ns mod 2 ^ 32) -> - 2 ^ 31 <= ns < 2 ^ 31 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SExt true 32 (SOff 40 0)) (SLit 32)) (SLit 32)) = ns mod 2 ^ 32.
Proof.
intros E ns H Hn. rewrite !U_SAlu, (cp_U_ns E ns H Hn), !U_SLit. cbn [zalu_raw].
change (Z.land (zcanon 32) 63) with 32.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
assert (Hy : (ns mod 2 ^ 64) mod 2 ^ 32 = ns mod 2 ^ 32)
  by (apply Z.mod_mod_divide; exists (2 ^ 32); reflexivity).
pose proof (Z.mod_pos_bound ns (2 ^ 32) ltac:(lia)) as Hb.
set (y := ns mod 2 ^ 64) in *.
unfold zcanon, M64.
replace ((y * 2 ^ 32) mod 2 ^ 64) with ((y mod 2 ^ 32) * 2 ^ 32)
  by (change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); rewrite Z.mul_mod_distr_r by lia; reflexivity).
rewrite Z.div_mul by lia. rewrite Hy. apply Z.mod_small. lia.
Qed.

(* `mul s8, s7, a3` (+0x38c): the product of the two four-byte fields. *)
Lemma cp_U_prod : forall E nch ns, ew E 39 = Z_to_bv 64 (nch mod 2 ^ 32) -> ew E 40 = Z_to_bv 64 (ns mod 2 ^ 32) ->
  - 2 ^ 31 <= ns < 2 ^ 31 ->
  U E (SMd M_MUL (SAlu ALU_SRL (SAlu ALU_SLL (SExt true 32 (SOff 40 0)) (SLit 32)) (SLit 32))
         (SExt false 32 (SOff 39 0))) = dec_a_prod nch ns.
Proof.
intros E nch ns H39 H40 Hs. rewrite U_SMd, (cp_U_s7 E ns H40 Hs), (cp_U_nch32 E nch H39). cbn [zmd_raw].
unfold dec_a_prod, zcanon, M64. f_equal. apply Z.mul_comm.
Qed.

(* `slli a0, s8, 1; add a0, a0, s8; sltiu s9, a0, 1; add s9, a0, s9` (+0x3a8 .. +0x3b4) on a positive product. *)
Lemma cp_olen3 : forall E x p, U E x = p -> 1 <= p < 2 ^ 60 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL x (SLit 1)) x)
         (SAlu ALU_SLTU (SAlu ALU_ADD (SAlu ALU_SLL x (SLit 1)) x) (SLit 1))) = 3 * p.
Proof.
intros E x p Hx Hp. rewrite !U_SAlu, !U_SLit, Hx. cbn [zalu_raw].
change (Z.land (zcanon 1) 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
unfold zcanon, M64. rewrite (Z.mod_small (p * 2)) by lia. rewrite (Z.mod_small (p * 2 + p)) by lia.
change (1 mod 2 ^ 64) with 1. rewrite (proj2 (Z.ltb_ge _ _)) by lia. change (0 mod 2 ^ 64) with 0.
rewrite Z.add_0_r. rewrite Z.mod_small by lia. lia.
Qed.

(* `mv a0, s9` (+0x3b8). *)
Lemma cp_add0 : forall E x, U E (SAlu ALU_ADD x (SLit 0)) = U E x.
Proof.
intros E x. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (zcanon 0) with 0. rewrite Z.add_0_r.
apply zcanon_id. apply U_range.
Qed.

(* The two values of the olen computation. *)
Lemma cp_olen_cases : forall nch ns, -128 <= nch <= 127 -> -128 <= ns <= 127 ->
  (dec_a_fits0 nch ns = 1 /\ dec_a_olen nch ns = 3 * dec_a_prod nch ns /\ 1 <= dec_a_prod nch ns < 2 ^ 60) \/
  (dec_a_fits0 nch ns = 0 /\ dec_a_olen nch ns = 1).
Proof.
intros nch ns Hc Hs. unfold dec_a_fits0, dec_a_olen, dec_a_prod.
destruct (0 <? nch) eqn:E1, (0 <? ns) eqn:E2; cbn [andb].
- left. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
  rewrite (Z.mod_small nch), (Z.mod_small ns) by lia. rewrite Z.mod_small by nia.
  split; [reflexivity|]. split; [ring|]. nia.
- right; split; reflexivity.
- right; split; reflexivity.
- right; split; reflexivity.
Qed.

(* A spill slot of s1, read back through the frame region (YC4b.v field_of_region,
   lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v rdword_of_val_mem). *)
Lemma cp_rdword_of_val_mem : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B8 : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B8 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B8 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B8 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B8 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B8 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B8 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B8 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B8 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma cp_slot_of : forall E (H : word -> bool) (m : word -> option byte) lo hi wlo whi cs b off e v,
  region_ok decodesegs0 E (mrestrict H m) (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 9) = b -> In (YP09.mkChunk off (CVal 8 e)) cs -> U E e = v ->
  rdword (aview decodesegs0 H m) (b + off) = Some v.
Proof.
intros E H m lo hi wlo whi cs b off e v HR Hb Hin HU.
pose proof (U_range E e) as Hr. rewrite HU in Hr. unfold M64 in Hr.
apply cp_rdword_of_val_mem; [|exact Hr].
exact (field_of_region E _ 9 b cs lo hi wlo whi off 8%N e v HR Hb Hin
  ltac:(rewrite denot_lit_U, HU; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* +0x2c4 .. +0x3bc: the clean-length algebra and its abort edges (+0x2c4 beq, +0x2cc, +0x2d4, +0x2fc, +0x304,
   +0x340, all refuted), the two four-byte shadow checks on the mode's fields (+0x344, +0x354), the geometry loads
   and spills to s1 (+0x360 .. +0x398), the olen computation (+0x39c .. +0x3b8), and the call of malloc #2. *)
Lemma cp_stage_e : forall (fx : YK11.FPState) (cx : dctx) (res mode nch ns : Z) ly S (W : world decodesegs0) regs mem md,
  AR_laws decodesegs0 B -> dec_crt_cells B ->
  (forall a, dec_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx -> dec_a_rom cx ->
  frm_zero (@fp_csr fx) ->
  cp_core B MT cx res mode nch ns ly S W regs mem md -> cp_rm mode regs -> cp_filled cx res W mem ->
  YK11.getr regs 10 = w64 (CCL.reac_frame_clean_len_model (dec_a_len (d_n cx))) ->
  SRr decodesegs0 W (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x2c4)) mem (YK11.seg_rom decodesegs0)) md)
    (cp_at B MT (Z_to_bv 64 (decode_sigma DS___interceptor_trampoline_malloc)) cx res mode nch ns
      (fun r => YK11.getr r 10 = w64 (dec_a_olen nch ns) /\ YK11.getr r 1 = w64 (DEC_A_LLVMF + 0x3c0) /\
                YK11.getr r 24 = w64 (dec_a_prod nch ns) /\ YK11.getr r 25 = w64 (dec_a_olen nch ns) /\
                YK11.getr r 23 = w64 (ns mod 2 ^ 32))
      (fun W' m => cp_filled cx res W' m /\
         dec_a_slot cx (aview decodesegs0 (w_H W') m) 32 (dec_a_fits0 nch ns) /\
         dec_a_slot cx (aview decodesegs0 (w_H W') m) 48 (nch mod 2 ^ 64) /\
         dec_a_slot cx (aview decodesegs0 (w_H W') m) 64 mode /\
         dec_a_slot cx (aview decodesegs0 (w_H W') m) 80 (nch mod 2 ^ 32) /\
         dec_a_slot cx (aview decodesegs0 (w_H W') m) 88 (ns mod 2 ^ 64))).
Proof.
intros fx cx res mode nch ns ly S W regs mem md LAWS HCELLS HSC HB HR Hfrm HCORE HRM HFILL H10.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof HCORE as (HC & Hbl & Hres & MLE & MOK & HFR & H18 & H20 & H22 & H26 & HMODE & HFSH & HSLOT).
pose proof HRM as (H25 & H23).
pose proof HC as (HJc & Hfrs & Hs0 & Hs1 & Hsp & Hsp1 & Hsp1m & Hgp & Htp & HSAV & HF4096 & HFmod & HFpres & HFL &
  Hblk & HGARR).
pose proof HJc as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
unfold DEC_LLVMF_STK in *.
assert (Hfin : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Hfa : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds decodesegs0 B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hfin) as (_ & HFhi & _).
rewrite Hfa in HFhi. change (fs_frame_bytes DEC_FCLASS) with 64 in HFhi.
assert (Hinr : In (res, dec_a_len (d_n cx)) (ablocks B ly S))
  by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (Hr16 & _ & Hrceil & Hrapp & _).
destruct (cp_mode_facts B cx ly S W mem md mode nch ns HCELLS LAWS HAR Hfin Hfa HF4096 HFmod HFSH HMODE)
  as (Hm0 & Hm1 & Hm8 & HmD & HmS4 & HmS8 & HmB).
destruct (cp_rom_div B cx [(DEC_FCLASS, d_fpos cx)] ly S W mem md dec_ev_234 HSC HR HJc) as (HKM & HKT).
assert (Hn26 : 0 <= d_n cx < 2 ^ 26).
{ clear - HB. unfold dec_a_base, dec_lib_pre_x in HB.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : (d_n cx = 0 /\ _) \/ (0 < d_n cx < 2 ^ 26 /\ _) |- _ =>
    destruct H as [[Hz _] | [Hz _]]; lia end. }
assert (Hlenpl : d_n cx = Z.of_nat (length (d_pl cx)))
  by (clear - HB; unfold dec_a_base, dec_lib_pre_x in HB; decompose [and] HB; assumption).
assert (Hlen : 0 <= dec_a_len (d_n cx) < 2 ^ 26) by (unfold dec_a_len; lia).
pose proof (req_size_pos0 (dec_a_len (d_n cx)) ltac:(unfold dec_a_len; lia)) as Hreq.
pose proof (cp_regs1_ok cx regs res mode nch ns H20 H18 H26 H25 H23 H22 HFR ltac:(lia)) as HREGS.
pose proof (cp_seat fx 0x2c4 cp_regs1 cx ly S W regs mem md res mode nch ns HREGS
  HC Hres ltac:(lia) Hr16 HMODE HSLOT HKM HKT Hm0 Hm1 Hm8 HmD HFhi) as HS.
pose proof (cp_E_eqs regs cx res mode nch ns) as EQS. cbv zeta in EQS.
set (E := Eimg (Ereg regs (cp_extra cx res mode nch ns))) in HS, HREGS, EQS.
destruct EQS as (E2 & E3 & E4 & E9 & E32 & E33 & E34 & E35 & E36 & E38 & E39 & E40 & E41 & E42 & E7o & E8o).
assert (E10 : ew E 10 = getr regs 10)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Us1 : bv_unsigned (ew E 9) = d_sp1 cx) by (rewrite E9, Hs1; unfold w64; apply unsigned_lit_small; lia).
assert (AG : forall n, (n < 512)%nat -> ew E n = ew E n) by reflexivity.
clearbody E.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
pose proof (cp_kept_refl W mem (d_sp1 cx - 4096) (d_sp1 cx + 96)) as KEPT.
pose (RUN := @paj_run fx rc dec_A_sink_head decode_listing PL_decode (@PI_decode rc) B LAWS).
pose (BR := @paj_branch fx rc decode_listing (@PI_decode rc)).
change (w64 (DEC_A_LLVMF + 0x2c4)) with (Z_to_bv 64 (VAL A_TEXT + 0x2c4)).
change (YK11.seg_rom decodesegs0) with (YK11.seg_rom SEGS).
set (len := dec_a_len (d_n cx)) in *.
assert (Umode : bv_unsigned (ew E 35) = mode) by (rewrite E35; apply unsigned_lit_small; lia).
assert (Hsp1b : 2 ^ 46 + 4096 <= d_sp1 cx) by (unfold d_sp0 in *; lia).
pose proof HMODE as (_ & Hnch & Hns & _).
destruct (cp_clean_cases len ltac:(lia)) as [[Hcl Hnd] | [Hcl [H54 Hd]]]; rewrite Hcl in H10.
- (* clean = len: +0x2c4 jumps to +0x300 *)
  assert (U10 : U E (SOff 10 0) = len) by (apply U_atom; [rewrite E10; exact H10 | lia]).
  assert (U34 : U E (SOff 34 0) = len) by (apply U_atom; [exact E34 | lia]).
  psrr_branch_tok RUN BR HS SHOK Bspan.
  all: rewrite branch_eq_U, U10, U34, Z.eqb_refl in Hc.
  2: (exfalso; discriminate Hc).
  clear Hc.
  paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
  cp_kupd KEPT.
  cp_env HS AG.
  (* +0x304: len < 54 skips the 32-bit test *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  all: rewrite branch_ltu_U, U34, U_lit in Hc by lia.
  all: rename Hc into H54c.
  all: paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
  all: cp_kupd KEPT.
  all: cp_env HS AG.
  (* +0x340: a1 (0, or the 32-bit test, false here) against a0 = (clean <> len) = 0 *)
  all: psrr_branch_tok RUN BR HS SHOK Bspan.
  all: rewrite branch_ne_U, (cp_snez_xor E), U10, U34, Z.eqb_refl in Hc.
  1,2: rewrite U_lit in Hc by lia.
  3,4: rewrite (cp_test32 E len U34) in Hc by (apply Z.ltb_ge in H54c; lia).
  3,4: rewrite (proj2 (Z.eqb_neq ((len - 54) mod 36) 0)) in Hc
         by (apply Z.ltb_ge in H54c; intros Hm; apply Hnd; split; [lia | exact Hm]).
  1,3: (exfalso; cbn in Hc; discriminate Hc).
  all: clear Hc H54c.
  (* the two paths at +0x344 wait for the common tail after the bullets *)
  all: shelve.
- (* clean = len - 2 *)
  assert (V10 : bv_unsigned (ew E 10) = len - 2) by (rewrite E10, H10; unfold w64; apply unsigned_lit_small; lia).
  assert (U10 : U E (SOff 10 0) = len - 2) by (apply U_atom; [rewrite E10; exact H10 | lia]).
  assert (U34 : U E (SOff 34 0) = len) by (apply U_atom; [exact E34 | lia]).
  psrr_branch_tok RUN BR HS SHOK Bspan.
  all: rewrite branch_eq_U, U10, U34 in Hc.
  1: (exfalso; apply Z.eqb_eq in Hc; lia).
  clear Hc.
  paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
  cp_kupd KEPT.
  cp_env HS AG.
  (* +0x2cc: clean >= 52 *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  all: rewrite branch_ltu_U, U10, U_lit in Hc by lia.
  1: (exfalso; apply Z.ltb_lt in Hc; lia).
  clear Hc.
  paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
  cp_kupd KEPT.
  cp_env HS AG.
  (* +0x2d4: clean + 2 = len *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  all: rewrite branch_ne_U, U_SOff, V10, U34, Z.sub_add, zcanon_id, Z.eqb_refl in Hc by (unfold M64; lia).
  1: (exfalso; discriminate Hc).
  clear Hc.
  paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
  cp_kupd KEPT.
  cp_env HS AG.
  (* +0x2fc: the rotate is (clean - 52) / 36, below KT *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  all: rewrite branch_geu_U, (cp_test64 E (len - 2) V10), U_lit in Hc by (Z.div_mod_to_equations; lia).
  1: (exfalso; apply negb_true_iff, Z.ltb_ge in Hc;
      assert ((len - 2 - 52) / 36 <= len) by (apply Z.div_le_upper_bound; lia); lia).
  clear Hc.
  paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
  cp_kupd KEPT.
  cp_env HS AG.
  (* +0x304: 54 <= len *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  all: rewrite branch_ltu_U, U34, U_lit in Hc by lia.
  1: (exfalso; apply Z.ltb_lt in Hc; lia).
  clear Hc.
  paj_run_tok RUN HS HJc SHOK Bspan; [cp_awr |].
  cp_kupd KEPT.
  cp_env HS AG.
  (* +0x340: a1 = the 32-bit test = 1 against a0 = (clean <> len) = 1 *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  all: rewrite branch_ne_U, (cp_snez_xor E), U10, U34, (cp_test32 E len U34), Hd in Hc by lia.
  all: rewrite (proj2 (Z.eqb_neq (len - 2) len)) in Hc by lia.
  1: (exfalso; cbn in Hc; discriminate Hc).
  clear Hc.
  shelve.
(* the three paths at +0x344, together *)
Unshelve.
(* +0x344 .. the jal of malloc #2 at +0x3bc, the same on the three paths that leave +0x340 not taken: the run
   through the two four-byte shadow checks (their range_addressable obligations at mode + 4 / mode + 8, carried
   from the entry's memory by cp_ra_kept) *)
all: paj_run_tok RUN HS HJc SHOK Bspan.
all: lazymatch goal with
| |- range_addressable _ _ _ _ =>
  rewrite (U_atom _ 32 SB E32), U_SOff, Umode, zcanon_id by (unfold SB, M64; lia);
  eapply (cp_ra_kept W _ mem _ _ _ 4 KEPT); [lia | lia | lia | first [exact HmS4 | exact HmS8]]
| |- awr_ok _ _ _ _ _ _ _ _ _ => cp_awr
| |- _ => idtac end.
all: cp_kupd KEPT.
all: cp_env HS AG.
(* +0x39c: olen = 3 * nch * ns when both are positive, else 1 *)
all: psrr_branch_tok RUN BR HS SHOK Bspan.
all: rewrite branch_ne_U, (cp_fits _ nch ns ltac:(rewrite AG by lia; exact E39) ltac:(rewrite AG by lia; exact E40)),
  U_lit in Hc by lia.
all: rename Hc into Hfit.
all: paj_run_tok RUN HS HJc SHOK Bspan.
all: lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => cp_awr | |- _ => idtac end.
all: cp_kupd KEPT.
all: cp_env HS AG.
(* the jal of malloc #2: the post, cp_core, the registers, the copy and the five spill slots *)
all: pmkst HS.
all: apply SRr_ret.
all: lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?msx) |- _ =>
  cp_reg HS (10%bv : bv 5) Ra0; cp_reg HS (1%bv : bv 5) Rra; cp_reg HS (24%bv : bv 5) Rs8;
  cp_reg HS (25%bv : bv 5) Rs9; cp_reg HS (23%bv : bv 5) Rs7 end.
all: lazymatch goal with HS : st_ok _ ?Ex _ _ |- _ =>
  assert (X39 : ew Ex 39 = Z_to_bv 64 (nch mod 2 ^ 32)) by (rewrite AG by lia; exact E39);
  assert (X40 : ew Ex 40 = Z_to_bv 64 (ns mod 2 ^ 32)) by (rewrite AG by lia; exact E40);
  assert (X35 : ew Ex 35 = Z_to_bv 64 mode) by (rewrite AG by lia; exact E35);
  assert (X9 : bv_unsigned (ew Ex 9) = d_sp1 cx) by (rewrite AG by lia; exact Us1) end.
all: lazymatch goal with HS : st_ok _ ?Ex ?ss ?msr |- _ =>
  let rr := eval vm_compute in (nth_error (ss_mem ss) 0) in
  lazymatch rr with Some ?r0 => pose proof (st_ok_region_nth Ex ss msr 0 r0 HS eq_refl) as HRS end end.
all: cbn [ms_mem restrict] in HRS.
all: destruct (cp_olen_cases nch ns Hnch Hns) as [(F1 & O3 & Hp) | (F0 & O1)];
  rewrite ?F1, ?F0 in Hfit; cbn in Hfit; try (exfalso; discriminate Hfit).
all: exists fx, ly, S. all: eexists _, _, _.
all: split; [reflexivity|]. all: split; [exact Hfrm|].
all: split; [apply (cp_core_xfer cx res mode nch ns ly S W regs mem md _ _ _ LAWS HCELLS Hlenpl HCORE HJc KEPT);
             cp_agree HS HREGS AG|].
all: split.
all: lazymatch goal with
| |- cp_filled _ _ _ _ /\ _ =>
  split; [exact (cp_filled_kept cx res W mem _ _ _ KEPT ltac:(lia) ltac:(fold len; lia) ltac:(lia) Hlenpl HFILL)|];
  unfold dec_a_slot;
  split; [exact (cp_slot_of _ _ _ _ _ _ _ _ _ 32 _ _ HRS X9 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                   (cp_fits _ nch ns X39 X40 ltac:(lia) ltac:(lia)))|];
  split; [exact (cp_slot_of _ _ _ _ _ _ _ _ _ 48 _ _ HRS X9 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                   (cp_U_nch _ nch X39 ltac:(lia)))|];
  split; [exact (cp_slot_of _ _ _ _ _ _ _ _ _ 64 _ _ HRS X9 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                   (U_atom _ 35 mode X35 ltac:(lia)))|];
  split; [exact (cp_slot_of _ _ _ _ _ _ _ _ _ 80 _ _ HRS X9 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                   (cp_U_nch32 _ nch X39))|];
  exact (cp_slot_of _ _ _ _ _ _ _ _ _ 88 _ _ HRS X9 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
           (cp_U_ns _ ns X40 ltac:(lia)))
| |- _ =>
  split; [rewrite Ra0, denot_lit_U;
          first [ rewrite cp_add0, (cp_olen3 _ _ _ (cp_U_prod _ nch ns X39 X40 ltac:(lia)) Hp), O3
                | rewrite U_lit, O1 by lia ]; reflexivity|];
  split; [rewrite Rra; etransitivity; [apply codeptr_val; assumption|]; rewrite cp_base; reflexivity|];
  split; [rewrite Rs8, denot_lit_U, (cp_U_prod _ nch ns X39 X40 ltac:(lia)); reflexivity|];
  split; [rewrite Rs9, denot_lit_U;
          first [ rewrite (cp_olen3 _ _ _ (cp_U_prod _ nch ns X39 X40 ltac:(lia)) Hp), O3
                | rewrite U_lit, O1 by lia ]; reflexivity|];
  rewrite Rs7, denot_lit_U, (cp_U_s7 _ ns X40 ltac:(lia)); reflexivity
end.
Qed.

(* From the call of reac_frame_clean_len to the segment's post: the call, stage E, malloc #2. *)
Lemma cp_tail :
  pc_wrap_malloc (as_code B) = decode_sigma DS___interceptor_trampoline_malloc ->
  dec_llvmf_utraces RA_LLVMF B -> dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws decodesegs0 B -> ameter_laws MT ->
  (forall fx : YK11.FPState, @amalloc04_rule fx rc dec_A_sink_head decodesegs0 B MT) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCL.dec_reac_frame_clean_len_cg) fx) ->
  forall (cx : dctx) (res mode nch ns : Z) (W : world decodesegs0) (c : config),
    dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx -> dec_a_rom cx ->
    cp_at B MT (Z_to_bv 64 (decode_sigma DS_reac_frame_clean_len)) cx res mode nch ns
      (fun r => cp_rm mode r /\ YK11.getr r 10 = w64 (dec_a_len (d_n cx)) /\
                YK11.getr r 1 = w64 (DEC_A_LLVMF + 0x2c4))
      (cp_filled cx res) W c ->
    SRr decodesegs0 W c (llvm_a_st_3c0 B MT cx).
Proof.
intros HPCM HUTR HCELLS HROZ HRNE LAWS MTL AMALLOC LCLEAN cx res mode nch ns W c HB HR H.
pose proof (dec_ro_rd_scoped B HROZ HRNE) as HSC.
eapply SRr_bind; [exact (cp_call_clean asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI LAWS HCELLS HROZ HRNE LCLEAN cx res mode nch ns W c HB HR H)|].
intros W7 c7 _ H7.
destruct H7 as (fx7 & ly7 & S7 & regs7 & mem7 & md7 & -> & Hfrm7 & HCORE7 & (HRM7 & H107) & HF7).
eapply SRr_bind; [exact (cp_stage_e fx7 cx res mode nch ns ly7 S7 W7 regs7 mem7 md7 LAWS HCELLS HSC HB HR Hfrm7 HCORE7
  HRM7 HF7 H107)|].
intros W8 c8 _ H8.
exact (cp_call_malloc2 asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI HPCM HUTR HCELLS HROZ HRNE LAWS MTL AMALLOC cx res mode nch ns W8 c8 HB HR H8).
Qed.

Theorem llvm_a_copy_ok :
  llvm_a_copy_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_a_copy_stmt.
intros HPCM HUTR HCELLS HROZ HRNE LAWS ML MTL AMEMCPY AMALLOC LIS LCLEAN cx W' c' HB HR H234.
pose proof (dec_ro_rd_scoped B HROZ HRNE) as HSC.
destruct H234 as (fx & ly' & S' & regs' & mem' & md' & res & mode & nch & ns & -> & Hfrm & HC & Hbl & Hres &
  MLE & MOK & HFR & H10 & H18 & H20 & H24 & H26 & H25 & H23 & H22 & HMODE & HFSH & HSLOT).
eapply SRr_bind; [exact (cp_stage_a fx cx ly' S' W' regs' mem' md' res mode nch ns LAWS HCELLS HSC HB HR Hfrm HC Hbl
  Hres MLE MOK HFR H10 H18 H24 H26 H25 H23 H22 HMODE HFSH HSLOT)|].
intros W2 c2 _ [[Hlen0 Hat] | [Hlen0 Hat]].
- (* len <> 0: __asan_memcpy, stage B, reac_frame_is_reac (res, len), stage C *)
  eapply SRr_bind; [exact (cp_call_memcpy asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI LAWS HCELLS AMEMCPY cx res mode nch ns W2 c2 HB Hlen0 Hat)|].
  intros W3 c3 _ H3.
  destruct H3 as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & -> & Hfrm3 & HCORE3 & HRM3 & HF3).
  eapply SRr_bind; [exact (cp_stage_b fx3 cx res mode nch ns ly3 S3 W3 regs3 mem3 md3 LAWS HCELLS HSC HB HR Hfrm3
    HCORE3 HRM3 HF3)|].
  intros W4 c4 _ H4.
  eapply SRr_bind; [exact (cp_call_isreac asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI LAWS HCELLS LIS cx res mode nch ns (dec_a_len (d_n cx))
    0x260 W4 c4 HB (or_introl eq_refl) (or_introl eq_refl) H4)|].
  intros W5 c5 _ H5.
  destruct H5 as (fx5 & ly5 & S5 & regs5 & mem5 & md5 & -> & Hfrm5 & HCORE5 & (HRM5 & H105) & HF5).
  eapply SRr_bind; [exact (cp_stage_c fx5 cx res mode nch ns ly5 S5 W5 regs5 mem5 md5 LAWS HCELLS HSC HB HR Hfrm5
    HCORE5 HRM5 HF5 H105)|].
  intros W6 c6 _ H6.
  exact (cp_tail HPCM HUTR HCELLS HROZ HRNE LAWS MTL AMALLOC LCLEAN cx res mode nch ns W6 c6 HB HR H6).
- (* len = 0: reac_frame_is_reac (res, 0), stage D *)
  eapply SRr_bind; [exact (cp_call_isreac asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI LAWS HCELLS LIS cx res mode nch ns 0
    0x2b4 W2 c2 HB (or_intror eq_refl) (or_intror eq_refl) Hat)|].
  intros W5 c5 _ H5.
  destruct H5 as (fx5 & ly5 & S5 & regs5 & mem5 & md5 & -> & Hfrm5 & HCORE5 & (HRM5 & H105) & HF5).
  assert (H105' : YK11.getr regs5 10 = w64 0).
  { rewrite H105. unfold CIR.is_reac_result. rewrite orb_true_r. reflexivity. }
  eapply SRr_bind; [exact (cp_stage_d fx5 cx res mode nch ns ly5 S5 W5 regs5 mem5 md5 LAWS HCELLS HSC HB HR Hfrm5
    HCORE5 HRM5 HF5 H105')|].
  intros W6 c6 _ H6.
  exact (cp_tail HPCM HUTR HCELLS HROZ HRNE LAWS MTL AMALLOC LCLEAN cx res mode nch ns W6 c6 HB HR H6).
Qed.

End seg.
