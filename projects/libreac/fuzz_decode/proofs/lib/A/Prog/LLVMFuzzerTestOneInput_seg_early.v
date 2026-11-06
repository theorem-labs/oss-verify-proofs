(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module names changed; 1124 of its 1192 lines of code are new or changed and 513 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_early: the segment llvm_a_early of the image-A walk of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v llvm_a_early_stmt), offsets +0x074 .. +0x230 of
   the audited listing lib/A/Prog/DecodeList.v, stepped through the Pa engine (lib/A/Prog/PaRun.v, PaShadow.v,
   PaJournal.v, DecodePaLib.v) in the idiom of libreac/fuzz_boxreg's lib/A/Prog/ReadName.v (pb_read_name at
   a working branch 1d92330b7ad).

   What the code does from the return of __asan_stack_malloc_0 (+0x074). a0 is the fake frame F (4096 <= F), so
   `bnez s3` at +0x084 is decided by the engine and the real-frame arm with its probe loop (+0x088 .. +0x0a0) is
   never entered. s3 = s5 = F; the ASan frame record (magic, descriptor obj2, pc obj3) is stored at F, F + 8,
   F + 16; s11 = (F >> 3) + s2, the frame's shadow, gets 0xf8 0xf8 0xf3 0xf3 at +4 .. +7 and 0xf1 x4 at +0 .. +3;
   112(s1) := F; the size test `srli a0, s4, 26; bnez a0` at +0x0fc .. +0x104 is refuted by dec_a_base
   (n < 2 ^ 26), so llvm_a_st_104 is never produced. Then the length dispatch: n = 0 (+0x140) takes the table of
   decode_obj 4; n >= 1 reads data[0] (shadow check +0x118, slow path +0xa7c), n >= 2 data[1] (+0x174, +0xacc),
   n >= 3 data[2] (+0x1a0, +0xb08): each shadow check's slow path is closed by the engine's token rule
   (PaShadow.v tok_branch_pi) against the range_addressable obligation that the caller's input block discharges
   (AR's block law), so no branch into +0xa4c .. +0xb60 is ever followed. The 12-byte local at F + 32 is unpoisoned
   (shadow +4 := 0, +5 := 4) and written {48000, nch, ns}; sel = data[0] & 3 picks the table of decode_obj 4
   (sel 0), decode_obj 6 (sel 1), decode_obj 5 (sel 2) or the local (sel 3); finally malloc (n - 3 or 0) at +0x230,
   discharged by the statement's amalloc04_rule through YC85.v amalloc04_sub, with the call trace from
   dec_llvmf_utraces.

   The shadow-checking runs use the span YC4b.Bspan; the runs that write the frame or its shadow use the empty span
   (0, 0), and in the checking runs the frame and shadow regions are carried read-only (their window would meet the
   shadow band), which the engine's cells_safe_b asks.

   The mode cells' pointer words are constant cells of dec_crt_cells B (check_round_trip_cg.v), which AR's am_const
   keeps at every state (e_mode_ptr); the tables' +4 / +8 words are DEC_RO_RD bytes, the entry's rom_view carried by
   the journal's image clause with dec_ro_rd_scoped (e_mode_geom); no hypothesis is carried. The
   fields of dec_lib_pre_x, afn_pre and dec_crt_cells are read by type (decompose), never by position. *)
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
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0s YI00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow DecodeSyms DecodeList DecodePa.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaJournal DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep DecodePaLib YC1g YC1h YC81 YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeAddr DecodeImg check_round_trip_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 0. The image's mode tables and the walk's symbolic picture           *)
(* ------------------------------------------------------------------ *)

(* The read-only view of the image and the table each mode cell points at: the image's own word in decode_obj 4 / 5 / 6
   (no address is written by hand; vm_compute reads it from the image). *)
Definition e_romrd (a : Z) : option Z :=
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom decodesegs0 (Z_to_bv 64 a)).
Definition e_tbl (k : nat) : Z := match rdword e_romrd (decode_obj k) with Some v => v | None => 0 end.
(* The table geometry every table holds at +4 / +8 (nch, ns). *)
Definition E_NCH : Z := 40.
Definition E_NS : Z := 12.

(* The regions of the state at +0x074: the fake frame (written below +48), its eight shadow bytes, the spill slot
   112(s1), and the three mode cells (read only). Atoms: registers 0..31 (Ereg), 32 = the frame's shadow address,
   33 / 34 / 35 = the first three input bytes. *)
Definition e_rg_frame : YP09.region := YP09.mkRegion (Some 10%nat) 0 64 0 48 [].
Definition e_rg_sh : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 8 [].
Definition e_rg_spill : YP09.region := YP09.mkRegion (Some 9%nat) 112 120 112 120 [].
Definition e_rg_cell (k : nat) : YP09.region :=
  YP09.mkRegion (Some (A_OBJ k)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit (e_tbl k)))].
Definition e_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 4096 (2 ^ 47) 5);
           (18%nat, mkAF SB SB 0); (20%nat, mkAF 0 (2 ^ 26 - 1) 0); (32%nat, mkAF SB (SB + 2 ^ 44) 0);
           (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0)] []
          [shadow_decl 10 18 32].
Definition ss074 : sstate :=
  mkSS 0x74 sr_atoms [e_rg_frame; e_rg_sh; e_rg_spill; e_rg_cell 4; e_rg_cell 5; e_rg_cell 6] None e_facts.
(* The first input bytes as the payload region reads them (atom 33 + i at p + i), the read-only and writable forms
   of a region, and the empty span of the runs that check no shadow. *)
Definition e_rg_p (i : nat) : YP09.region :=
  YP09.mkRegion (Some 24%nat) (Z.of_nat i) (Z.of_nat i + 1) 0 0 [YP09.mkChunk (Z.of_nat i) (CVal 1 (SOff (33 + i) 0))].
Definition e_ro (r : YP09.region) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 (YP09.r_chunks r).
Definition e_rw (r : YP09.region) (wl wh : Z) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) wl wh (YP09.r_chunks r).
Definition E_B0 : Z * Z := (0, 0).

Section early. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := dec_A_sink_head.
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
Local Abbreviation segs := decodesegs0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).
Local Abbreviation BASE := (@pa_val _ decode_listing PI_decode A_TEXT).

Local Abbreviation dbase := (@dec_a_base rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI).
Local Abbreviation dcore := (@dec_a_core rc B).
Local Abbreviation ajr := (@ajournal rc tfib_sink_head segs B).

Definition e_byte (cx : dctx) (i : nat) : Z := bv_unsigned (nth i (d_pl cx) (Z_to_bv 8 0)).
Definition e_extra (cx : dctx) : list word :=
  [w64 (d_SH cx); w64 (e_byte cx 0); w64 (e_byte cx 1); w64 (e_byte cx 2)].
Definition e_E (regs : bvmap 5 word) (cx : dctx) : env := @Eimg rc decode_listing PI_decode (Ereg regs (e_extra cx)).

(* ------------------------------------------------------------------ *)
(* 1. The image facts the dispatch reads, and dec_a_base's fields      *)
(* ------------------------------------------------------------------ *)

(* The fields of the slot pre this segment reads, each found by its type (no positional destruct of the generated
   conjunction dec_lib_pre_x). *)
Lemma e_base_pn : forall cx, dbase cx ->
  (d_n cx = 0 /\ d_p cx = A_EMPTY) \/ (0 < d_n cx < 2 ^ 26 /\ In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))).
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma e_base_afn : forall cx, dbase cx ->
  @afn_pre rc segs B DEC_LLVMF_STK (d_ly cx) (d_S cx) (d_W cx) (d_regs cx) (d_mem cx) (d_md cx) [].
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma e_base_ra : forall cx, dbase cx -> raZ (d_regs cx) = RA_LLVMF.
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma e_base_len : forall cx, dbase cx -> d_n cx = Z.of_nat (length (d_pl cx)).
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma e_base_garr : forall cx, dbase cx ->
  garr8 segs (rd (d_W cx) (d_mem cx)) (d_p cx) (map (fun b : byte => bv_unsigned b) (d_pl cx)).
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma e_base_nev : forall cx, dbase cx -> st_nev (d_S cx) + DEC_EV_LIB <= EV_MAX.
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma e_base_bb : forall cx, dbase cx -> blocks_bytes (d_S cx) + DEC_LIVE_LIB <= LIVE_MAX.
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
(* The fields of afn_pre (lib/Reusable/YCbq.v:336), found by type. *)
Lemma e_afn_stk : forall ly S W regs mem md ch, @afn_pre rc segs B DEC_LLVMF_STK ly S W regs mem md ch ->
  astk_ok DEC_LLVMF_STK ly (spZ regs).
Proof. intros ly S W regs mem md ch H. unfold afn_pre in H. decompose [and] H. assumption. Qed.
Lemma e_afn_ra4 : forall ly S W regs mem md ch, @afn_pre rc segs B DEC_LLVMF_STK ly S W regs mem md ch ->
  4096 <= raZ regs.
Proof. intros ly S W regs mem md ch H. unfold afn_pre in H. decompose [and] H. assumption. Qed.
Lemma e_afn_chain : forall ly S W regs mem md ch, @afn_pre rc segs B DEC_LLVMF_STK ly S W regs mem md ch ->
  achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch.
Proof. intros ly S W regs mem md ch H. unfold afn_pre in H. decompose [and] H. assumption. Qed.

Lemma e_val_mem_of_view : forall H (mem : word -> option byte) a n V,
  (forall j, (j < n)%nat -> aview segs H mem (a + Z.of_nat j) = Some (YO0f.le_byte V n j)) ->
  val_mem segs (mrestrict H mem) a n V.
Proof.
intros H mem a n V Hv j Hj. destruct (aview_byte segs H mem _ _ (Hv j Hj)) as (b & Hb & Hbv & _).
rewrite Hb. f_equal. rewrite Hbv. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
symmetry. apply Z.mod_small. pose proof (bv_unsigned_in_range 8 b) as Hr. exact Hr.
Qed.
(* The pointer rows of dec_crt_cells B (check_round_trip_cg.v), found by type (no positional destruct of the
   generated conjunction). *)
Lemma e_cells : dec_crt_cells B -> forall ly kk, In kk [4; 5; 6]%nat ->
  In (z8 (ANum (decode_obj kk)) (e_tbl kk)) (as_const B ly).
Proof.
intros HC ly kk Hkk. pose proof (HC ly) as H. decompose [and] H.
cbn [In] in Hkk; destruct Hkk as [<- | [<- | [<- | []]]];
  lazymatch goal with |- context [e_tbl ?k] => let v := eval vm_compute in (e_tbl k) in change (e_tbl k) with v end;
  assumption.
Qed.
(* The mode cells' pointer words at every AR state (AR's am_const). *)
Lemma e_mode_ptr : forall ly' S' (W' : world segs) mem' md' kk,
  dec_crt_cells B -> AR segs B ly' S' W' mem' md' -> In kk [4; 5; 6]%nat ->
  rdword (aview segs (w_H W') mem') (decode_obj kk) = Some (e_tbl kk).
Proof.
intros ly' S' W' mem' md' kk HC HAR Hkk.
pose proof (e_cells HC ly' kk Hkk) as I1.
destruct HAR as (Mx & _).
apply (rdword_cell B ly'); [| exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) _ I1)].
cbn [In] in Hkk; destruct Hkk as [<- | [<- | [<- | []]]]; vm_compute; split; congruence.
Qed.
(* The DEC_RO_RD bytes still show the image's read-only bytes at any memory the journal reaches from the entry: the
   entry's rom_view (dec_a_rom) carried by the journal's image clause (YCbq.v:362), kept off the owned statics and
   errno by dec_ro_rd_scoped (seg_copy.v cp_ro_kept's argument). *)
Lemma e_ro_kept : forall (cx : dctx) own ly' S' (W' : world segs) mem' md' k,
  dec_ro_rd_unowned B -> dec_rom_no_errno B -> dec_a_rom cx ->
  ajr DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) own ly' S' W' mem' md' k ->
  forall a, dec_in_ro_rd a -> aview segs (w_H W') mem' a = e_romrd a.
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
(* A table's two fields, [T + 4, T + 12), are DEC_RO_RD bytes (found by search, not by position). *)
Lemma e_tbl_ro_rd : forall k, In k [4; 5; 6]%nat -> forall x, e_tbl k + 4 <= x < e_tbl k + 12 -> dec_in_ro_rd x.
Proof.
intros k Hk x Hx. cbn [In] in Hk; destruct Hk as [<- | [<- | [<- | []]]];
  (lazymatch type of Hx with context [e_tbl ?kk] =>
     let v := eval vm_compute in (e_tbl kk) in change (e_tbl kk) with v in Hx end);
  unfold dec_in_ro_rd, DEC_RO_RD;
  repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
Qed.
(* The tables' geometry (nch at +4, ns at +8) at any memory the journal reaches from the entry. *)
Lemma e_mode_geom : forall (cx : dctx) own ly' S' (W' : world segs) mem' md' k kk,
  dec_ro_rd_unowned B -> dec_rom_no_errno B -> dec_a_rom cx ->
  ajr DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) own ly' S' W' mem' md' k ->
  In kk [4; 5; 6]%nat ->
  val_mem segs (rd W' mem') (e_tbl kk + 4) 4 (E_NCH mod 2 ^ 32) /\
  val_mem segs (rd W' mem') (e_tbl kk + 8) 4 (E_NS mod 2 ^ 32).
Proof.
intros cx own ly' S' W' mem' md' k kk HROS HRNE HROM HJ Hkk.
assert (HT : forall o, 4 <= o < 12 -> aview segs (w_H W') mem' (e_tbl kk + o) = e_romrd (e_tbl kk + o)).
{ intros o Ho. apply (e_ro_kept cx own ly' S' W' mem' md' k HROS HRNE HROM HJ).
  apply (e_tbl_ro_rd kk Hkk). lia. }
split; apply e_val_mem_of_view; intros j Hj; rewrite <- Z.add_assoc; rewrite HT by lia;
  (destruct j as [|[|[|[|j]]]]; [| | | | lia]);
  cbn [In] in Hkk; destruct Hkk as [<- | [<- | [<- | []]]]; clear; vm_compute; reflexivity.
Qed.


(* ------------------------------------------------------------------ *)
(* 2. The symbolic state at +0x074                                      *)
(* ------------------------------------------------------------------ *)

Lemma e_tbl_range : forall k, In k [4; 5; 6]%nat -> IMG_LO <= e_tbl k /\ e_tbl k + 16 <= IMG_TOP.
Proof.
intros k Hk. pose proof IMG_LO_val as L. pose proof IMG_TOP_val as T.
cbn [In] in Hk; destruct Hk as [<- | [<- | [<- | []]]];
  lazymatch goal with |- _ <= e_tbl ?kk /\ _ => let v := eval vm_compute in (e_tbl kk) in change (e_tbl kk) with v end; lia.
Qed.
Lemma e_ew_low : forall regs cx n, (n < A_TEXT)%nat -> ew (e_E regs cx) n = ew (Ereg regs (e_extra cx)) n.
Proof. intros regs cx n Hn. unfold e_E. apply Eimg_low. exact Hn. Qed.
Lemma e_ew_obj : forall regs cx k, (k < 15)%nat -> ew (e_E regs cx) (A_OBJ k) = Z_to_bv 64 (decode_obj k).
Proof.
intros regs cx k Hk. unfold e_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
cbn [pa_val PI_decode]. unfold decode_val. replace (A_OBJ k =? A_TEXT)%nat with false by (symmetry; apply Nat.eqb_neq; unfold A_OBJ, A_TEXT; lia).
replace (A_OBJ k <? A_HI 0)%nat with true by (symmetry; apply Nat.ltb_lt; unfold A_OBJ, A_HI; lia).
f_equal. f_equal. unfold A_OBJ. lia.
Qed.
Lemma e_bv_small : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.
Lemma e_ra234 : 4096 <= DEC_A_LLVMF + 0x234 < 2 ^ 40.
Proof. unfold DEC_A_LLVMF, decode_text, AF_LLVMFuzzerTestOneInput. lia. Qed.
(* Memory facts carried where their bytes are kept (the lemmas of a Theorem Labs lane's lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v
   val_mem_moved / rdword_kept, here at the frame's own clauses). *)
Lemma e_val_mem_moved : forall H H' (m m' : word -> option byte) a n v,
  (forall k, 0 <= k < Z.of_nat n -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hkn. specialize (Hk (Z.of_nat k) ltac:(lia)). unfold aview in Hk.
rewrite (Hv k Hkn) in Hk. destruct (mbyte segs (mrestrict H' m') (a + Z.of_nat k)) as [b'|]; cbn in Hk; [|discriminate].
injection Hk as Hk. f_equal. apply bv_eq. exact Hk.
Qed.
Lemma e_garr8_kept : forall H H' (m m' : word -> option byte) base l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' m' (base + j) = aview segs H m (base + j)) ->
  garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H' m') base l.
Proof.
intros H H' m m' base l HK HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
apply (e_val_mem_moved H H' m m' (base + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk. replace (base + Z.of_nat j + k) with (base + (Z.of_nat j + k)) by lia. apply HK. lia.
Qed.
Lemma e_rdword_of_val_mem : forall H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (B8 : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (YO0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YO0f.le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B8 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B8 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B8 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B8 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B8 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B8 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B8 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B8 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma e_saved_kept : forall cx (r r' : reader),
  (forall a, d_sp0 cx - 104 <= a < d_sp0 cx -> r' a = r a) -> dec_a_saved cx r -> dec_a_saved cx r'.
Proof.
intros cx r r' Hk Hs. unfold dec_a_saved in *. rewrite Forall_forall in Hs |- *.
intros [off q] Hin. rewrite <- (Hs (off, q) Hin). cbn [fst snd].
assert (Ho : 8 <= off <= 104) by (unfold dec_a_saved_at in Hin; cbn [In] in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia|]); destruct Hin).
apply rdword_ext. intros j Hj. apply Hk. lia.
Qed.
Lemma e_fsh_kept : forall cx (r r' : reader) b4 b5,
  (forall i, 0 <= i < 8 -> r' (d_SH cx + i) = r (d_SH cx + i)) -> dec_a_fsh cx r b4 b5 -> dec_a_fsh cx r' b4 b5.
Proof.
intros cx r r' b4 b5 Hk (H0 & H4 & H5 & H6). unfold dec_a_fsh.
split; [intros i Hi; rewrite Hk by lia; exact (H0 i Hi)|].
split; [rewrite Hk by lia; exact H4|]. split; [rewrite Hk by lia; exact H5|].
intros i Hi; rewrite Hk by lia; exact (H6 i Hi).
Qed.
Lemma e_slot_kept : forall cx (r r' : reader) off v,
  (forall i, 0 <= i < 8 -> r' (d_sp1 cx + off + i) = r (d_sp1 cx + off + i)) ->
  dec_a_slot cx r off v -> dec_a_slot cx r' off v.
Proof. intros cx r r' off v Hk Hs. unfold dec_a_slot in *. rewrite <- Hs. apply rdword_ext. exact Hk. Qed.
(* What the rest of the walk spends from +0x234 on is not negative. *)
Lemma e_rest_nonneg : ameter_laws MT -> 0 <= dec_rest_234 MT.
Proof.
intros MTL. unfold dec_rest_234, dec_rest_3c0, dec_rest_4fc, dec_rest_5fc, dec_rest_748, dec_rest_86c, dec_crt_cost_max.
pose proof (mo_malloc_nonneg MT MTL 48387 ltac:(lia)). pose proof (mo_malloc_nonneg MT MTL 1440 ltac:(lia)).
pose proof (mo_malloc_nonneg MT MTL 1920 ltac:(lia)). pose proof (mo_malloc_nonneg MT MTL 1016 ltac:(lia)).
pose proof (mo_free_nonneg MT MTL). lia.
Qed.
(* The mode the dispatch leaves at the call, before the call's memory step: a table (its cell and geometry are the
   image's, e_mode_ptr / e_mode_geom) or the frame's local with the two words the dispatch stored. *)
Definition e_mode_at (cx : dctx) (W : world segs) (m : word -> option byte) (mode nch ns : Z) : Prop :=
  (exists k, In k [4; 5; 6]%nat /\ mode = e_tbl k /\ nch = E_NCH /\ ns = E_NS) \/
  (mode = d_F cx + 32 /\ -128 <= nch <= 127 /\ -128 <= ns <= 127 /\
   val_mem segs (rd W m) (d_F cx + 36) 4 (nch mod 2 ^ 32) /\ val_mem segs (rd W m) (d_F cx + 40) 4 (ns mod 2 ^ 32)).
(* The bytes the segment's runs may write: the frame below +48, its eight shadow bytes, the spill slot 112(s1). *)
Definition e_win (cx : dctx) (a : Z) : Prop :=
  (d_F cx <= a < d_F cx + 48) \/ (d_SH cx <= a < d_SH cx + 8) \/ (d_sp1 cx + 112 <= a < d_sp1 cx + 120).
Lemma e_denot_SOff : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n c v Hn Hv. rewrite denot_lit_U, U_SOff, Hn, unsigned_lit_small by exact Hv.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold zcanon, bv_wrap, M64. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.
Lemma e_denot_SOffg : forall E n c v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n c v Hn. rewrite denot_lit_U, U_SOff, Hn.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold zcanon, bv_wrap, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma e_view_of_val_mem1 : forall H (mem : word -> option byte) a v,
  val_mem segs (mrestrict H mem) a 1 v -> 0 <= v < 256 -> aview segs H mem a = Some v.
Proof.
intros H mem a v Hv Hr. unfold aview. pose proof (Hv 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte.
change (bv_modulus 8) with 256. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, !Z.mod_small by lia. reflexivity.
Qed.
(* dec_a_core carried across a run that wrote only e_win and kept sp, gp, tp, s0, s1. *)
Lemma e_core_move : forall (LAWS : AR_laws segs B) cx ly S W regs m md regs' m' md' k,
  dbase cx -> dcore cx ly S W regs m md k ->
  ajr DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)]
    ly S W m' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ e_win cx a -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  (forall r, In r [2; 3; 4; 8; 9] -> YK11.getr regs' (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  ablocks B ly S = ablocks B (d_ly cx) (d_S cx) ->
  dcore cx ly S W regs' m' md' k.
Proof.
intros LAWS cx ly S W regs m md regs' m' md' k HB HC HJ' KR RR Hbl.
pose proof HC as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1a & Hgp & Htp & Hsaved & HF4 & HFa & HFp & HFL & Hblk & Hga).
pose proof HJ' as (HAR' & Hly' & _).
pose proof (e_afn_stk _ _ _ _ _ _ _ (e_base_afn cx HB)) as Hstk.
pose proof Hstk as (Hsp0a & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold DEC_LLVMF_STK in *.
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly' as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds segs B LAWS ly S W m' md' _ _ HAR' Hin0) as (_ & HFc & _).
destruct (al_frames _ _ LAWS ly S W m' md' _ _ HAR' Hin0) as (_ & Happ & Hfp' & _).
rewrite EF in HFc, Happ, Hfp'. replace (fs_frame_bytes DEC_FCLASS) with 64 in HFc, Happ, Hfp' by reflexivity.
assert (ESH : d_SH cx = SHADOW_OFF + d_F cx / 8) by reflexivity.
split; [exact HJ'|]. split; [exact Hfrs|].
split; [rewrite <- R8; exact (RR 8 ltac:(cbn; tauto))|].
split; [rewrite <- R9; exact (RR 9 ltac:(cbn; tauto))|].
split; [rewrite <- Hsp; unfold spZ; f_equal; exact (RR 2 ltac:(cbn; tauto))|].
split; [exact Hsp1r|]. split; [exact Hsp1a|].
split; [rewrite <- Hgp; exact (RR 3 ltac:(cbn; tauto))|].
split; [rewrite <- Htp; exact (RR 4 ltac:(cbn; tauto))|].
split.
{ apply (e_saved_kept cx (aview segs (w_H W) m)); [|exact Hsaved].
  intros a Ha. apply KR; [unfold d_sp0 in *; lia|]. unfold e_win, d_sp0 in *.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. rewrite ESH. unfold SHADOW_OFF. lia. }
split; [exact HF4|]. split; [exact HFa|].
split; [intros a Ha; exact (proj1 (Hfp' a Ha))|].
split; [rewrite <- HFL; apply rdword_ext; intros j Hj; apply KR; [lia|]; unfold e_win;
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ; rewrite ESH; unfold SHADOW_OFF, d_sp0 in *; lia|].
split; [exact Hblk|].
pose proof (e_base_pn cx HB) as Hpn. pose proof (e_base_len cx HB) as Hlen. pose proof (e_base_garr cx HB) as Hgarr.
destruct Hpn as [(Hn0 & Hp0) | (Hn0 & Hpin)].
- rewrite Hlen in Hn0. destruct (d_pl cx); [intros j Hj; cbn in Hj; lia | cbn in Hn0; lia].
- apply (e_garr8_kept (w_H (d_W cx)) (w_H W) (d_mem cx) m' (d_p cx) _); [| exact Hgarr].
  intros j Hj. rewrite length_map, <- Hlen in Hj.
  pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  pose proof (req_size_pos (d_n cx) ltac:(lia)) as Hrn.
  apply (F2 (d_p cx) (d_n cx) j Hpin); [rewrite Hbl; exact Hpin | lia | intros (rg & [] & _)].
Qed.
(* The frame's eight shadow bytes, the spill slot and the local, read from the regions of the state at the call. *)
Lemma e_fsh_of_region : forall E H (m : word -> option byte) cs cx,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some 32%nat) 0 8 0 8 cs) ->
  bv_unsigned (ew E 32) = d_SH cx ->
  (forall i, 0 <= i < 8 -> exists v, In (YP09.mkChunk i (CVal 1 (SLit v))) cs /\
     v mod 256 = (if i <? 4 then DEC_SH_LEFT else if i =? 4 then 0 else if i =? 5 then 4 else DEC_SH_RIGHT)) ->
  dec_a_fsh cx (aview segs H m) 0 4.
Proof.
intros E H m cs cx HR Hb Hc.
assert (K : forall i, 0 <= i < 8 -> aview segs H m (d_SH cx + i) =
  Some (if i <? 4 then DEC_SH_LEFT else if i =? 4 then 0 else if i =? 5 then 4 else DEC_SH_RIGHT)).
{ intros i Hi. destruct (Hc i Hi) as (v & Hin & Hv).
  pose proof (field_of_region_any E _ 32 (d_SH cx) cs 0 8 0 8 i 1 (SLit v) HR Hb Hin ltac:(cbn; lia)) as V.
  cbn [sv_denot N.to_nat Pos.to_nat Z.of_N] in V. rewrite unsigned_lit in V.
  replace (zcanon v mod 2 ^ (8 * 1)) with (v mod 256) in V by (unfold zcanon, M64;
    rewrite (Z.mod_mod_divide v (2 ^ 64) (2 ^ (8 * 1))); [reflexivity | exists (2 ^ 56); reflexivity]).
  rewrite <- Hv. apply e_view_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia]. }
unfold dec_a_fsh. split; [intros i Hi; rewrite K by lia; destruct (Z.ltb_spec i 4); [reflexivity | lia]|].
split; [rewrite K by lia; reflexivity|]. split; [rewrite K by lia; reflexivity|].
intros i Hi. rewrite K by lia. destruct (Z.ltb_spec i 4); [lia|]. destruct (Z.eqb_spec i 4); [lia|].
destruct (Z.eqb_spec i 5); [lia | reflexivity].
Qed.
Lemma e_slot_of_region : forall E H (m : word -> option byte) cs cx,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some 9%nat) 112 120 112 120 cs) ->
  bv_unsigned (ew E 9) = d_sp1 cx -> In (YP09.mkChunk 112 (CVal 8 (SOff 10 0))) cs ->
  ew E 10 = Z_to_bv 64 (d_F cx) -> 0 <= d_F cx < 2 ^ 64 ->
  dec_a_slot cx (aview segs H m) 112 (d_F cx).
Proof.
intros E H m cs cx HR Hb Hin H10 HF.
pose proof (field_of_region_any E _ 9 (d_sp1 cx) cs 112 120 112 120 112 8 (SOff 10 0) HR Hb Hin ltac:(cbn; lia)) as V.
rewrite (e_denot_SOff E 10 0 (d_F cx) H10 HF), Z.add_0_r, unsigned_lit_small, Z.mod_small in V by (cbn; lia).
unfold dec_a_slot. apply e_rdword_of_val_mem; [exact V | exact HF].
Qed.
Lemma e_local_of_region : forall E H (m : word -> option byte) cs cx e1 e2 nch ns,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some 10%nat) 0 64 0 48 cs) ->
  bv_unsigned (ew E 10) = d_F cx ->
  In (YP09.mkChunk 36 (CVal 4 e1)) cs -> In (YP09.mkChunk 40 (CVal 4 e2)) cs ->
  bv_unsigned (sv_denot E e1) mod 2 ^ 32 = nch mod 2 ^ 32 -> bv_unsigned (sv_denot E e2) mod 2 ^ 32 = ns mod 2 ^ 32 ->
  val_mem segs (mrestrict H m) (d_F cx + 36) 4 (nch mod 2 ^ 32) /\
  val_mem segs (mrestrict H m) (d_F cx + 40) 4 (ns mod 2 ^ 32).
Proof.
intros E H m cs cx e1 e2 nch ns HR Hb I1 I2 V1 V2.
pose proof (field_of_region_any E _ 10 (d_F cx) cs 0 64 0 48 36 4 e1 HR Hb I1 ltac:(cbn; lia)) as W1.
pose proof (field_of_region_any E _ 10 (d_F cx) cs 0 64 0 48 40 4 e2 HR Hb I2 ltac:(cbn; lia)) as W2.
change (8 * Z.of_N 4) with 32 in W1, W2. rewrite V1 in W1. rewrite V2 in W2. split; assumption.
Qed.
(* The two signed bytes of the local: `lbu; slli 56; srai 56` (nch, +0x184 / +0x1c0 / +0x1d0) and `lb` (ns, +0x1b0). *)
Definition e_s8 (v : Z) : Z := if v <? 128 then v else v - 256.
Lemma e_sx_sra : forall E v, ew E 34 = Z_to_bv 64 v -> 0 <= v < 256 ->
  bv_unsigned (sv_denot E (SAlu ALU_SRA (SAlu ALU_SLL (SOff 34 0) (SLit 56)) (SLit 56))) mod 2 ^ 32 =
  e_s8 v mod 2 ^ 32.
Proof.
intros E v H34 Hv.
set (E' := mkEnv (fun _ => Z_to_bv 64 v) (ed E)).
assert (HA : env_agree_p (fun n => Nat.eqb n 34) E E').
{ split; [|reflexivity]. intros n Hn. apply Nat.eqb_eq in Hn. subst n. cbn [ew E']. symmetry. exact H34. }
rewrite <- (sv_denot_agree_p (fun n => Nat.eqb n 34) E E' (SAlu ALU_SRA (SAlu ALU_SLL (SOff 34 0) (SLit 56)) (SLit 56)) HA eq_refl).
assert (Hb : forallb (fun n => Z.eqb (bv_unsigned (sv_denot (mkEnv (fun _ => Z_to_bv 64 (Z.of_nat n)) (ed E))
  (SAlu ALU_SRA (SAlu ALU_SLL (SOff 34 0) (SLit 56)) (SLit 56))) mod 2 ^ 32) (e_s8 (Z.of_nat n) mod 2 ^ 32))
  (seq 0 256) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb (Z.to_nat v)). rewrite Z2Nat.id in Hb by lia.
apply Z.eqb_eq. apply Hb. apply in_seq. lia.
Qed.
Lemma e_sx_lb : forall E v, ew E 35 = Z_to_bv 64 v -> 0 <= v < 256 ->
  bv_unsigned (sv_denot E (SExt true 8 (SOff 35 0))) mod 2 ^ 32 = e_s8 v mod 2 ^ 32.
Proof.
intros E v H35 Hv.
set (E' := mkEnv (fun _ => Z_to_bv 64 v) (ed E)).
assert (HA : env_agree_p (fun n => Nat.eqb n 35) E E').
{ split; [|reflexivity]. intros n Hn. apply Nat.eqb_eq in Hn. subst n. cbn [ew E']. symmetry. exact H35. }
rewrite <- (sv_denot_agree_p (fun n => Nat.eqb n 35) E E' (SExt true 8 (SOff 35 0)) HA eq_refl).
assert (Hb : forallb (fun n => Z.eqb (bv_unsigned (sv_denot (mkEnv (fun _ => Z_to_bv 64 (Z.of_nat n)) (ed E))
  (SExt true 8 (SOff 35 0))) mod 2 ^ 32) (e_s8 (Z.of_nat n) mod 2 ^ 32)) (seq 0 256) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb (Z.to_nat v)). rewrite Z2Nat.id in Hb by lia.
apply Z.eqb_eq. apply Hb. apply in_seq. lia.
Qed.
Lemma e_s8_range : forall v, 0 <= v < 256 -> -128 <= e_s8 v <= 127.
Proof. intros v Hv. unfold e_s8. destruct (Z.ltb_spec v 128); lia. Qed.
Lemma e_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. apply bv_eq. unfold U. pose proof (U_SOff E n 0) as H. unfold U in H. rewrite H, Z.add_0_r.
  apply zcanon_id. pose proof (bv_unsigned_in_range 64 (ew E n)) as Hr. change (bv_modulus 64) with M64 in Hr. lia. Qed.

Section ef. Context {fx : YK11.FPState}.
Lemma e_entry : forall (LAWS : AR_laws segs B) (cx : dctx) (W' : world segs) ly' S' regs' mem' md',
  dbase cx -> dec_crt_cells B ->
  dcore cx ly' S' W' regs' mem' md' dec_ev_074 ->
  YK11.getr regs' 10 = w64 (d_F cx) -> YK11.getr regs' 18 = w64 SHADOW_OFF -> YK11.getr regs' 20 = w64 (d_n cx) ->
  @st_ok_pi segs decode_val fx (e_E regs' cx) ss074
    (restrict (w_H W') (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + 0x74)) mem' (YK11.seg_rom segs))).
Proof.
intros LAWS cx W' ly' S' regs' mem' md' HB HR HC R10 R18 R20.
pose proof HC as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1a & Hgp & Htp & Hsaved & HF4 & HFa & HFp & HFL & Hblk & Hga).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0a & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S')) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (al_frames _ _ LAWS ly' S' W' mem' md' _ _ HAR Hin0) as (Hfa32 & Happ & Hfpres & Hshp).
destruct (frames_bounds segs B LAWS ly' S' W' mem' md' _ _ HAR Hin0) as (Hf0 & Hfc & _).
pose proof (@frm_off_imgP rc decode_listing PI_decode B ly' S' W' mem' md' _ _ HAR Hin0) as Himg.
replace (fs_frame_bytes DEC_FCLASS) with 64 in * by reflexivity.
rewrite EF in Hfa32, Happ, Hfpres, Hshp, Hf0, Hfc, Himg.
pose proof IMG_LO_val as IL. pose proof IMG_TOP_val as IT.
assert (ESH : d_SH cx = SHADOW_OFF + d_F cx / 8) by reflexivity.
pose proof (e_mode_ptr _ _ _ _ _ 4 HR HAR ltac:(cbn; tauto)) as M4.
pose proof (e_mode_ptr _ _ _ _ _ 5 HR HAR ltac:(cbn; tauto)) as M5.
pose proof (e_mode_ptr _ _ _ _ _ 6 HR HAR ltac:(cbn; tauto)) as M6.
pose proof (e_tbl_range 4 ltac:(cbn; tauto)) as T4. pose proof (e_tbl_range 5 ltac:(cbn; tauto)) as T5.
pose proof (e_tbl_range 6 ltac:(cbn; tauto)) as T6.
pose proof (e_base_pn cx HB) as Hpn.
assert (Hn26 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
unfold DEC_LLVMF_STK in *.
set (E := e_E regs' cx).
assert (U2 : bv_unsigned (ew E 2) = d_sp1 cx)
  by (unfold E; rewrite e_ew_low by (cbv; lia); rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Hsp).
assert (U9 : bv_unsigned (ew E 9) = d_sp1 cx)
  by (unfold E; rewrite e_ew_low by (cbv; lia); rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), R9; apply e_bv_small; lia).
assert (U10 : bv_unsigned (ew E 10) = d_F cx)
  by (unfold E; rewrite e_ew_low by (cbv; lia); rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl), R10; apply e_bv_small; lia).
assert (E10 : ew E 10 = Z_to_bv 64 (d_F cx))
  by (unfold E; rewrite e_ew_low by (cbv; lia); rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl), R10; reflexivity).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E; rewrite e_ew_low by (cbv; lia); rewrite (ew_Ereg_nat regs' _ 18 18%bv eq_refl), R18; reflexivity).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF) by (rewrite E18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U20 : bv_unsigned (ew E 20) = d_n cx)
  by (unfold E; rewrite e_ew_low by (cbv; lia); rewrite (ew_Ereg_nat regs' _ 20 20%bv eq_refl), R20; apply e_bv_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 (SHADOW_OFF + d_F cx / 8))
  by (unfold E; rewrite e_ew_low by (cbv; lia); exact (ew_Ereg_extra regs' (e_extra cx) 0)).
assert (U32 : bv_unsigned (ew E 32) = d_SH cx)
  by (rewrite E32, ESH; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (UB : forall i, (i < 3)%nat -> bv_unsigned (ew E (33 + i)) = e_byte cx i /\ 0 <= e_byte cx i < 256).
{ intros i Hi. assert (Hb : 0 <= e_byte cx i < 256)
    by (unfold e_byte; pose proof (bv_unsigned_in_range 8 (nth i (d_pl cx) (Z_to_bv 8 0))) as Hr; exact Hr).
  split; [|exact Hb]. unfold E. rewrite e_ew_low by (cbv; lia).
  replace (33 + i)%nat with (32 + S i)%nat by lia. rewrite ew_Ereg_extra.
  destruct i as [|[|[|i]]]; [| | | lia]; cbn [nth e_extra]; apply e_bv_small; lia. }
assert (UO : forall k, (k < 15)%nat -> bv_unsigned (ew E (A_OBJ k)) = decode_obj k).
{ intros k Hk. unfold E. rewrite e_ew_obj by exact Hk. apply unsigned_lit_small.
  do 15 (destruct k as [|k]; [cbn; lia|]). lia. }
assert (HSHB : 0 <= d_SH cx /\ d_SH cx + 8 <= 2 ^ 64) by (rewrite ESH; unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx. unfold ss074.
apply (@pa_entry_st_ok_full fx rc decode_listing PI_decode).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks e_rg_frame e_rg_sh e_rg_spill e_rg_cell base_val];
    rewrite ?U10, ?U32, ?U9, ?UO by lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply HFp. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). rewrite ESH. unfold shadow_addr in Hshp.
    apply (Hshp o). change (64 / 8) with 8. lia.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. unfold DEC_LLVMF_STK. lia.
  + split; [cbn; lia|]. split; [cbn; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ (decode_obj 4) 0 8 (SLit (e_tbl 4)) (e_tbl 4)); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword segs _ _ _ _ M4).
  + split; [cbn; lia|]. split; [cbn; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ (decode_obj 5) 0 8 (SLit (e_tbl 5)) (e_tbl 5)); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword segs _ _ _ _ M5).
  + split; [cbn; lia|]. split; [cbn; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ (decode_obj 6) 0 8 (SLit (e_tbl 6)) (e_tbl 6)); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword segs _ _ _ _ M6).
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, e_rg_frame, e_rg_sh, e_rg_spill, e_rg_cell.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U10, U32, U9, !UO by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd decode_obj].
  rewrite ESH. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  repeat split; zify; lia.
- unfold e_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  destruct (UB 0%nat ltac:(lia)) as [U33 B33]. destruct (UB 1%nat ltac:(lia)) as [U34 B34].
  destruct (UB 2%nat ltac:(lia)) as [U35 B35]. cbn [Nat.add] in U33, U34, U35.
  rewrite U2, U9, U10, U18, U20, U32, U33, U34, U35.
  rewrite ESH. unfold SB, SHADOW_OFF in *.
  repeat split; try (zify; lia).
  + exact (shadow_decl_ok E 10 18 32 (d_F cx) SHADOW_OFF E10 ltac:(lia) E18 E32).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. malloc #1 at +0x230                                               *)
(* ------------------------------------------------------------------ *)

(* The frame-pointer chain and the call trace at the call: s0 is the entry sp (+0x03c), whose frame record holds
   RA_LLVMF and the caller's s0 (dec_a_saved's first two words); the caller's chain is empty (afn_pre ... []), so
   the trace is [pc_malloc_ra0; +0x234] or [pc_malloc_ra0; +0x234; RA_LLVMF], both in dec_llvmf_utraces. *)
Lemma e_trace : forall (HUTR : dec_llvmf_utraces RA_LLVMF B) cx lyT ST W regsT memT mdT k,
  dbase cx -> dcore cx lyT ST W regsT memT mdT k ->
  YK11.getr regsT 1 = w64 (DEC_A_LLVMF + 0x234) ->
  exists ch, chain_pre lyT (aview segs (w_H W) memT) regsT ch /\
             In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B).
Proof.
intros HUTR cx lyT ST W regsT memT mdT k HB HC R1.
destruct HC as (HJ & _ & R8 & _ & Hsp & Hsp1r & Hsp1a & _ & _ & Hsaved & _).
pose proof (e_base_ra cx HB) as Hra. pose proof (e_base_afn cx HB) as HAFN.
pose proof (e_afn_ra4 _ _ _ _ _ _ _ HAFN) as Hra4. pose proof (e_afn_stk _ _ _ _ _ _ _ HAFN) as Hstk.
pose proof (e_afn_chain _ _ _ _ _ _ _ HAFN) as Hch.
pose proof Hstk as (Hsp0a & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold DEC_LLVMF_STK in *.
pose proof HJ as (_ & Hly & _).
assert (Etop : ly_top lyT = ly_top (d_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
pose proof e_ra234 as HRA.
assert (Hraz : raZ regsT = DEC_A_LLVMF + 0x234) by (unfold raZ; rewrite R1; apply e_bv_small; lia).
assert (Hs0z : s0Z regsT = d_sp0 cx) by (unfold s0Z; rewrite R8; apply e_bv_small; unfold d_sp0; lia).
unfold dec_a_saved, dec_a_saved_at in Hsaved.
apply Forall_cons_iff in Hsaved as [S1 Hsaved]. apply Forall_cons_iff in Hsaved as [S8 _]. cbn [fst snd] in S1, S8.
assert (EU : forall sp, In sp [[]; [RA_LLVMF]] ->
  In (dec_utrace (pc_malloc_ra0 (as_code B)) ((DEC_A_LLVMF + 0x234) :: sp)) (as_universe B)).
{ intros sp Hsp'. apply (proj1 (HUTR sp Hsp')). unfold DEC_LLVMF_RA_MALLOC. cbn [map In]. left. reflexivity. }
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
         - apply negb_false_iff. apply Z.eqb_eq. pose proof (Z.div_mod (spZ (d_regs cx)) 16 ltac:(lia)) as D. rewrite Hsp0a in D. lia. }
    split; [lia|]. cbn [fpchain].
    split; [reflexivity|].
    split; [pose proof (Z.div_mod (spZ (d_regs cx)) 16 ltac:(lia)) as D; rewrite Hsp0a in D; lia|].
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
      apply (@aview_above_of_journal rc tfib_sink_head decode_listing PI_decode B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
      lia.
  + unfold call_trace0, unwind_of_chain. rewrite Hraz.
    pose proof (EU [RA_LLVMF] ltac:(cbn; tauto)) as EU1. unfold dec_utrace in EU1. cbn [flat_map app] in EU1 |- *.
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
    pose proof (EU [] ltac:(cbn; tauto)) as EU0. unfold dec_utrace in EU0. cbn [flat_map app] in EU0 |- *.
    exact EU0.
Qed.

Lemma e_call : forall (LAWS : AR_laws segs B) (MTL : ameter_laws MT)
    (AM : @amalloc04_rule fx rc tfib_sink_head segs B MT) (HUTR : dec_llvmf_utraces RA_LLVMF B)
    (cx : dctx) (W : world segs) lyT ST regsT memT mdT (mode nch ns : Z),
  dbase cx -> dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B -> dec_a_rom cx -> frm_zero (@fp_csr fx) ->
  dcore cx lyT ST W regsT memT mdT dec_ev_074 ->
  ablocks B lyT ST = ablocks B (d_ly cx) (d_S cx) ->
  mo_le MT (d_S cx) ST (dec_spent_074 MT) -> mo_ok MT ST (dec_rest_074 MT (d_n cx)) ->
  YK11.getr regsT 1 = w64 (DEC_A_LLVMF + 0x234) ->
  dec_a_fr cx regsT ->
  YK11.getr regsT 10 = w64 (dec_a_len (d_n cx)) ->
  YK11.getr regsT 18 = w64 SHADOW_OFF ->
  YK11.getr regsT 20 = w64 (d_n cx) ->
  YK11.getr regsT 24 = w64 (d_p cx + dec_a_u (d_n cx)) ->
  YK11.getr regsT 26 = w64 (dec_a_len (d_n cx)) ->
  YK11.getr regsT 25 = w64 mode -> YK11.getr regsT 23 = w64 (mode + 4) -> YK11.getr regsT 22 = w64 (mode + 8) ->
  e_mode_at cx W memT mode nch ns ->
  dec_a_fsh cx (aview segs (w_H W) memT) 0 4 ->
  dec_a_slot cx (aview segs (w_H W) memT) 112 (d_F cx) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (YK11.seg_rom segs)) mdT)
    (fun W2 c2 => llvm_a_st_234 B MT cx W2 c2 \/ llvm_a_st_104 B MT cx W2 c2).
Proof.
intros LAWS MTL AM HUTR cx W lyT ST regsT memT mdT mode nch ns HB HR HROS HRNE HROM Hfrm HC Hbl Hmle Hmok R1 (R19 & R21 & R27)
  R10 R18 R20 R24 R26 R25 R23 R22 HMD HFSH HSLOT.
pose proof HC as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1a & Hgp & Htp & Hsaved & HF4 & HFa & HFp & HFL & Hblk & Hga).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0a & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (e_base_pn cx HB) as Hpn. pose proof (e_base_len cx HB) as Hlen. pose proof (e_base_garr cx HB) as Hgarr.
pose proof (e_base_nev cx HB) as Hnev0. pose proof (e_base_bb cx HB) as Hbb.
unfold DEC_LLVMF_STK, DEC_EV_LIB, DEC_LIVE_LIB, dec_ev_074 in *.
assert (Hn26 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
assert (Hlen0 : 0 <= dec_a_len (d_n cx) <= d_n cx) by (unfold dec_a_len; lia).
pose proof (e_rest_nonneg MTL) as Hrest.
pose proof (mo_malloc_mono MT MTL (dec_a_len (d_n cx)) (d_n cx) Hlen0) as Hmono.
assert (Hsp016 : (d_sp1 cx - d_sp0 cx) mod 16 = 0).
{ pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D1. pose proof (Z.div_mod (d_sp0 cx) 16 ltac:(lia)) as D2.
  unfold d_sp0 in *. rewrite Hsp1a in D1. rewrite Hsp0a in D2.
  replace (d_sp1 cx - spZ (d_regs cx)) with ((2 * (d_sp1 cx / 32) - spZ (d_regs cx) / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
destruct (e_trace HUTR cx lyT ST W regsT memT mdT 0 HB HC R1) as (ch & Hch & Htr).
eapply SRr_mono.
{ eapply (amalloc04_sub (SK := dec_A_sink_head) segs B LAWS decode_segs_low MT AM W regsT memT 32768 (d_sp0 cx) []
    (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] lyT ST mdT 0 (dec_a_len (d_n cx))
    (d_sp1 cx - d_sp0 cx) (w64 (DEC_A_LLVMF + 0x234)) ch HJ R10).
  - unfold MALLOC_MAX. lia.
  - rewrite (blocks_bytes_bsum B lyT ST), Hbl, <- (blocks_bytes_bsum B (d_ly cx) (d_S cx)). unfold LIVE_MAX in *. lia.
  - lia.
  - exact Hsp016.
  - lia.
  - unfold ASTACK. lia.
  - exact Hgp.
  - exact Htp.
  - exact R1.
  - exact (@ret_ok_codeptr_v rc decode_listing PI_decode 0x234 ltac:(lia) eq_refl).
  - unfold EV_MAX in *. lia.
  - exact Hch.
  - exact Htr.
  - apply (mo_ok_le MT MTL ST _ _ Hmok). unfold dec_rest_074. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Hres & Hfr2 & Hr4 & Hbl2 & HK & MLE & _).
pose proof HJ2 as (HAR2 & Hly2 & _).
pose proof HK as (HK1 & HK2 & HK3 & HK4 & HK5 & HK6).
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames ST)) by (rewrite Hfrs; left; reflexivity).
assert (Hin2 : In (DEC_FCLASS, d_fpos cx) (frames S2)) by (rewrite Hfr2; exact Hin0).
assert (EFT : frame_addr lyT DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (EF2 : frame_addr ly2 DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly2 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hresin : In (res, dec_a_len (d_n cx)) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hresin) as (_ & Hres4 & Hresc & Hresapp & _).
pose proof (sep_block_frame segs B LAWS ly2 S2 W2 mem2 md2 _ _ _ _ HAR2 Hresin Hin2) as Hdisj.
rewrite EF2 in Hdisj. replace (fs_frame_bytes DEC_FCLASS) with 64 in Hdisj by reflexivity.
unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj.
pose proof (req_size_pos0 (dec_a_len (d_n cx)) ltac:(lia)) as Hrq.
(* the frame's bytes and its shadow are the call's to keep *)
assert (KF : forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memT a).
{ intros a Ha. apply (HK4 DEC_FCLASS (d_fpos cx) a Hin0); [left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFT;
    replace (fs_frame_bytes DEC_FCLASS) with 64 by reflexivity; lia | lia]. }
destruct (frames_bounds segs B LAWS lyT ST W memT mdT _ _ HAR Hin0) as (_ & HFc & _).
rewrite EFT in HFc. replace (fs_frame_bytes DEC_FCLASS) with 64 in HFc by reflexivity.
assert (KS : forall a, d_SH cx <= a < d_SH cx + 8 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memT a).
{ intros a Ha. apply (HK4 DEC_FCLASS (d_fpos cx) a Hin0).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFT. replace (fs_frame_bytes DEC_FCLASS / 8) with 8 by reflexivity.
    unfold d_SH in Ha. lia.
  - intros Hra'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hresapp.
    unfold d_SH, shadow_addr, SHADOW_OFF in Ha. lia. }
assert (KA : forall a, d_sp1 cx <= a < 2 ^ 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memT a).
{ intros a Ha. apply HK1; [lia | unfold ASTACK; lia]. }
assert (HRS : forall r, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regsT (Z_to_bv 5 r)) by exact HP2.
left. unfold llvm_a_st_234.
exists fx, ly2, S2, regs2, mem2, md2, res, mode, nch, ns.
split; [reflexivity|].
split; [exact Hfrm|].
split.
{ split; [exact HJ2|].
  split; [rewrite Hfr2; exact Hfrs|].
  split; [rewrite <- R8; exact (HRS 8 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- R9; exact (HRS 9 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- Hsp; unfold spZ; f_equal; exact (HRS 2 ltac:(unfold acallee_saved; lia))|].
  split; [lia|]. split; [exact Hsp1a|].
  split; [rewrite <- Hgp; exact (HRS 3 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- Htp; exact (HRS 4 ltac:(unfold acallee_saved; lia))|].
  split; [apply (e_saved_kept cx (aview segs (w_H W) memT)); [intros a Ha; apply KA; unfold d_sp0 in *; lia | exact Hsaved]|].
  split; [exact HF4|]. split; [exact HFa|].
  split.
  { intros a Ha. destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin2) as (_ & _ & Hfp2 & _).
    rewrite EF2 in Hfp2. replace (fs_frame_bytes DEC_FCLASS) with 64 in Hfp2 by reflexivity.
    exact (proj1 (Hfp2 a Ha)). }
  split; [rewrite <- HFL; apply rdword_ext; intros j Hj; apply KF; lia|].
  split; [intros Hn0; rewrite Hbl2, Hbl; apply in_or_app; left; destruct Hpn as [(Hn' & _) | (_ & Hin)]; [lia | exact Hin]|].
  destruct Hpn as [(Hn0 & Hp0) | (Hn0 & Hpin)].
  - rewrite Hlen in Hn0. destruct (d_pl cx); [intros j Hj; cbn in Hj; lia | cbn in Hn0; lia].
  - apply (e_garr8_kept (w_H (d_W cx)) (w_H W2) (d_mem cx) mem2 (d_p cx) _); [| exact Hgarr].
    intros j Hj. rewrite length_map, <- Hlen in Hj.
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    pose proof (req_size_pos (d_n cx) ltac:(lia)) as Hrn.
    apply (F2 (d_p cx) (d_n cx) j Hpin); [rewrite Hbl2, Hbl; apply in_or_app; left; exact Hpin | lia | intros (rg & [] & _)]. }
split; [rewrite Hbl2, Hbl; reflexivity|].
split; [exact Hres4|].
split.
{ unfold dec_spent_234. apply (mo_le_mono MT MTL _ _ (dec_spent_074 MT + mo_malloc MT (dec_a_len (d_n cx))));
  [apply (mo_le_trans MT MTL _ ST); [exact Hmle | exact MLE] | unfold dec_spent_074; lia]. }
split.
{ apply (mo_ok_step MT MTL ST S2 (mo_malloc MT (dec_a_len (d_n cx)))); [|exact MLE].
  apply (mo_ok_le MT MTL ST _ _ Hmok). unfold dec_rest_074. lia. }
split; [split; [rewrite <- R19; exact (HRS 19 ltac:(unfold acallee_saved; lia))|];
        split; [rewrite <- R21; exact (HRS 21 ltac:(unfold acallee_saved; lia))|
                rewrite <- R27; exact (HRS 27 ltac:(unfold acallee_saved; lia))]|].
split; [exact Hres|].
split; [rewrite <- R18; exact (HRS 18 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R20; exact (HRS 20 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R24; exact (HRS 24 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R26; exact (HRS 26 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R25; exact (HRS 25 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R23; exact (HRS 23 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R22; exact (HRS 22 ltac:(unfold acallee_saved; lia))|].
split.
{ destruct HMD as [(kk & Hkk & -> & -> & ->) | (-> & Hnch & Hns & V4 & V8)].
  - pose proof (e_mode_ptr _ _ _ _ _ kk HR HAR2 Hkk) as Mc.
    destruct (e_mode_geom cx _ _ _ _ _ _ _ kk HROS HRNE HROM HJ2 Hkk) as (Mn & Ms).
    split; [cbn [In] in Hkk; destruct Hkk as [<- | [<- | [<- | []]]]; [left | right; left | right; right; left]; exact Mc|].
    unfold E_NCH, E_NS in *. split; [lia|]. split; [lia|]. split; [exact Mn | exact Ms].
  - split; [right; right; right; reflexivity|]. split; [exact Hnch|]. split; [exact Hns|].
    split; [replace (d_F cx + 32 + 4) with (d_F cx + 36) by lia | replace (d_F cx + 32 + 8) with (d_F cx + 40) by lia];
      (eapply e_val_mem_moved; [|eassumption]); intros j Hj; apply KF; cbn in Hj; lia. }
split; [apply (e_fsh_kept cx (aview segs (w_H W) memT)); [intros i Hi; apply KS; lia | exact HFSH]|].
apply (e_slot_kept cx (aview segs (w_H W) memT)); [intros i Hi; apply KA; lia | exact HSLOT].
Qed.

(* The input bytes at p + i (i < n): the entry's (garr8 of the slot pre), kept by the journal (its block clause). *)
Lemma e_payload_byte : forall cx ly S W m md k own i,
  dbase cx ->
  ajr DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) own ly S W m md k ->
  ablocks B ly S = ablocks B (d_ly cx) (d_S cx) ->
  0 <= Z.of_nat i < d_n cx ->
  val_mem segs (mrestrict (w_H W) m) (d_p cx + Z.of_nat i) 1 (e_byte cx i).
Proof.
intros cx ly S W m md k own i HB HJ Hbl Hi.
pose proof (e_base_pn cx HB) as Hpn. pose proof (e_base_len cx HB) as Hlen. pose proof (e_base_garr cx HB) as Hg.
destruct Hpn as [(Hn0 & _) | (Hn0 & Hpin)]; [lia|].
assert (Hil : (i < length (map (fun b : byte => bv_unsigned b) (d_pl cx)))%nat) by (rewrite length_map; lia).
destruct (Hg i Hil) as [Hv _].
replace (nth i (map (fun b : byte => bv_unsigned b) (d_pl cx)) 0) with (e_byte cx i) in Hv.
2: { unfold e_byte. change 0 with ((fun b : byte => bv_unsigned b) (Z_to_bv 8 0)). rewrite map_nth. reflexivity. }
apply (e_val_mem_moved (w_H (d_W cx)) (w_H W) (d_mem cx) m _ 1 _); [|exact Hv].
intros j Hj. cbn in Hj. replace (d_p cx + Z.of_nat i + j) with (d_p cx + (Z.of_nat i + j)) by lia.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (req_size_pos (d_n cx) ltac:(lia)) as Hrn.
apply (F2 (d_p cx) (d_n cx) (Z.of_nat i + j) Hpin); [rewrite Hbl; exact Hpin | lia | intros (rg & [] & _)].
Qed.
Lemma e_region_ok_ro : forall sg E m r, region_ok sg E m r -> region_ok sg E m (e_ro r).
Proof.
intros sg E m r (H1 & H2 & _ & H4). unfold e_ro, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [exact H1|]. split; [exact H2|]. split; [intros o Ho; lia | exact H4].
Qed.
Lemma e_region_ok_rw : forall sg E m r wl wh, region_ok sg E m r ->
  (forall o, wl <= o < wh -> writable_at sg m (base_val E (YP09.r_base r) + o)) -> region_ok sg E m (e_rw r wl wh).
Proof.
intros sg E m r wl wh (H1 & H2 & _ & H4) Hw. unfold e_rw, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [exact H1|]. split; [exact H2|]. split; [exact Hw | exact H4].
Qed.

(* Two regions of the state swapped for regions of the same extent (their read-only or writable copy), so that the
   shadow-checking runs see no window in the shadow band and the writing runs see the frame's windows again. *)
Lemma e_all_disj_ext : forall E r r' rs, YP09.r_base r' = YP09.r_base r -> YP09.r_lo r' = YP09.r_lo r ->
  YP09.r_hi r' = YP09.r_hi r -> all_disjoint E r rs -> all_disjoint E r' rs.
Proof.
intros E r r' rs Hb Hl Hh. induction rs as [|q rs IH]; cbn [all_disjoint]; [auto|].
intros [D1 D2]. split; [unfold extent_disjoint in *; rewrite Hb, Hl, Hh; exact D1 | exact (IH D2)].
Qed.
Lemma e_st_swap2 : forall E pc sr r1 r2 r1' r2' rs rv G (ms : machine_state),
  @st_ok_pi (@pa_segs _ decode_listing PI_decode) (@pa_val _ decode_listing PI_decode) fx E (mkSS pc sr (r1 :: r2 :: rs) rv G) ms ->
  region_wf r1' = true -> region_wf r2' = true ->
  region_ok (@pa_segs _ decode_listing PI_decode) E (ms_mem ms) r1' ->
  region_ok (@pa_segs _ decode_listing PI_decode) E (ms_mem ms) r2' ->
  YP09.r_base r1' = YP09.r_base r1 -> YP09.r_lo r1' = YP09.r_lo r1 -> YP09.r_hi r1' = YP09.r_hi r1 ->
  YP09.r_base r2' = YP09.r_base r2 -> YP09.r_lo r2' = YP09.r_lo r2 -> YP09.r_hi r2' = YP09.r_hi r2 ->
  @st_ok_pi (@pa_segs _ decode_listing PI_decode) (@pa_val _ decode_listing PI_decode) fx E (mkSS pc sr (r1' :: r2' :: rs) rv G) ms.
Proof.
intros E pc sr r1 r2 r1' r2' rs rv G ms H Hw1 Hw2 Ho1 Ho2 B1 L1 H1 B2 L2 H2.
pose proof (st_ok_mem_ok _ E _ ms H) as (Hwf & _ & Hpd).
cbn [ss_mem abs_ss setpc] in Hwf, Hpd. cbn [regions_wf] in Hwf.
apply andb_prop in Hwf as [_ Hwf]. apply andb_prop in Hwf as [_ Hwf].
destruct Hpd as (D1 & D2 & _). cbn [all_disjoint] in D1. destruct D1 as (D12 & D1r).
pose proof (st_ok_pi_submem E (mkSS pc sr (r1 :: r2 :: rs) rv G) ms rs H
  (submem_drop _ _ _ (submem_drop _ _ _ (submem_refl rs))) Hwf) as H0.
pose proof (st_ok_pi_add_region E _ ms r2' H0 Hw2 Ho2 (e_all_disj_ext E r2 r2' rs B2 L2 H2 D2)) as H3.
refine (st_ok_pi_add_region E _ ms r1' H3 Hw1 Ho1 _).
cbn [ss_mem]. split; [|exact (e_all_disj_ext E r1 r1' rs B1 L1 H1 D1r)].
unfold extent_disjoint in *. rewrite B1, L1, H1, B2, L2, H2. exact D12.
Qed.
Lemma e_st_drop : forall E pc sr r rs rv G (ms : machine_state),
  @st_ok_pi (@pa_segs _ decode_listing PI_decode) (@pa_val _ decode_listing PI_decode) fx E (mkSS pc sr (r :: rs) rv G) ms ->
  @st_ok_pi (@pa_segs _ decode_listing PI_decode) (@pa_val _ decode_listing PI_decode) fx E (mkSS pc sr rs rv G) ms.
Proof.
intros E pc sr r rs rv G ms H.
pose proof (st_ok_mem_ok _ E _ ms H) as (Hwf & _).
cbn [ss_mem abs_ss setpc] in Hwf. cbn [regions_wf] in Hwf. apply andb_prop in Hwf as [_ Hwf].
exact (st_ok_pi_submem E (mkSS pc sr (r :: rs) rv G) ms rs H (submem_drop _ _ _ (submem_refl rs)) Hwf).
Qed.
End ef.

(* The right to write each window (YCbq.v awr_byte): the frame and its shadow are the frame this function owns
   (in_frames of own = [(0, fpos)]), the spill slot is in the entry's stack window. *)
Lemma e_awr_F : forall cx STK sp0 FP bl0 blc ly' a,
  frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx -> d_F cx <= a < d_F cx + 64 ->
  awr_byte STK sp0 FP bl0 blc ly' [(DEC_FCLASS, d_fpos cx)] a.
Proof.
intros cx STK sp0 FP bl0 blc ly' a EF Ha. right; right; right. exists DEC_FCLASS, (d_fpos cx).
split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EF.
replace (fs_frame_bytes DEC_FCLASS) with 64 by reflexivity. lia.
Qed.
Lemma e_awr_SH : forall cx STK sp0 FP bl0 blc ly' a,
  frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx -> d_SH cx <= a < d_SH cx + 8 ->
  awr_byte STK sp0 FP bl0 blc ly' [(DEC_FCLASS, d_fpos cx)] a.
Proof.
intros cx STK sp0 FP bl0 blc ly' a EF Ha. right; right; right. exists DEC_FCLASS, (d_fpos cx).
split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite EF.
replace (fs_frame_bytes DEC_FCLASS / 8) with 8 by reflexivity. exact Ha.
Qed.
Lemma e_awr_stk : forall STK sp0 FP bl0 blc ly' own a,
  sp0 - STK <= a < sp0 -> awr_byte STK sp0 FP bl0 blc ly' own a.
Proof. intros STK sp0 FP bl0 blc ly' own a Ha. left. exact Ha. Qed.
Lemma e_ew_reg : forall regs cx n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (e_E regs cx) n = YK11.getr regs r.
Proof. intros regs cx n r Hn Hr. rewrite e_ew_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. Qed.
Lemma e_ew_ext : forall regs cx j, (j < 4)%nat -> ew (e_E regs cx) (32 + j) = nth j (e_extra cx) (Z_to_bv 64 0).
Proof. intros regs cx j Hj. rewrite e_ew_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
(* The windows of the current state: frame (atom 10), shadow (atom 32), spill (atom 9); every other region is read
   only. *)
Ltac e_awr cx EF U10 U32 U9 :=
  lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat (d_F cx));
    [ reflexivity | exact U10 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (e_awr_F cx); [exact EF | lia] |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (d_SH cx));
    [ reflexivity | exact U32 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (e_awr_SH cx); [exact EF | lia] |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat (d_sp1 cx));
    [ reflexivity | exact U9 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply e_awr_stk; unfold DEC_LLVMF_STK; lia |] ].
(* After a run: every byte outside e_win is still the +0x074 byte (ReadName.v rn_kupd's form). *)
Ltac e_kupd cx KR U10 U32 U9 :=
  lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict ?H ?m0) (mrestrict ?H ?m1),
                      HG : mem_grows (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
  lazymatch type of KR with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mb a =>
    let KR2 := fresh "KR" in
    assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ e_win cx a -> aview decodesegs0 H m1 a = aview decodesegs0 H mb a);
    [ intros a Ha Hn; transitivity (aview decodesegs0 H m0 a); [| exact (KR a Ha Hn)];
      refine (kept_of_frame Ex rsx H m0 m1 (e_win cx) HFr _ a Ha Hn);
      intros bb wlo whi x Hin Hr;
      let wsv := eval vm_compute in (windows rsx) in change (In (bb, wlo, whi) wsv) in Hin;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr|]); try contradiction;
      rewrite ?ew_ewset_other in Hr by lia;
      unfold e_win; first [ lia | rewrite U10 in Hr; lia | rewrite U32 in Hr; lia | rewrite U9 in Hr; lia ]
    | clear KR HFr HG; rename KR2 into KR ]
  end end.
(* The model after a run, named and opaque (the measured doubling trap, a Theorem Labs lane's PaWalk.v). *)
Ltac e_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    let md2 := fresh "md" in set (md2 := mdx) in *; clearbody md2 end.
(* The symbolic value of register r in the machine state of HS. *)
Ltac e_rv HS r H :=
  lazymatch type of HS with
  | st_ok ?sg ?Ex ?ss (restrict ?Hh ?msx) =>
    pose proof (st_ok_restrict_reg sg Hh Ex ss msx r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict] in H
  | st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?msx) =>
    pose proof (st_ok_pi_restrict_reg Hh Ex ss msx r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict] in H
  end.
(* A register's value at the call from its symbolic value: a code pointer, an atom of the entry (atoms 10 F,
   18 the shadow base, 20 n, 24 p, 32 the frame's shadow) plus an offset, or a literal. *)
Ltac e_sv HEIx E10x E18x E20x E24x E32x :=
  lazymatch goal with
  | |- sv_denot ?Ex (SOff 240 ?k) = _ =>
    first [ lazymatch goal with HEIy : img_env _ _ Ex |- _ =>
              transitivity (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + k)); [exact (codeptr_val Ex k HEIy) | reflexivity] end
          | transitivity (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + k)); [exact (codeptr_val Ex k HEIx) | reflexivity] ]
  | |- sv_denot ?Ex (SOff 10 ?c) = _ => rewrite (e_denot_SOffg Ex 10 c _ E10x); unfold w64; f_equal; lia
  | |- sv_denot ?Ex (SOff 18 ?c) = _ => rewrite (e_denot_SOffg Ex 18 c _ E18x); unfold w64; f_equal; lia
  | |- sv_denot ?Ex (SOff 20 ?c) = _ =>
    rewrite (e_denot_SOffg Ex 20 c _ E20x); unfold w64; f_equal; unfold dec_a_len, dec_a_u in *; lia
  | |- sv_denot ?Ex (SOff 24 ?c) = _ =>
    rewrite (e_denot_SOffg Ex 24 c _ E24x); unfold w64; f_equal; unfold dec_a_len, dec_a_u in *; lia
  | |- sv_denot ?Ex (SOff 32 ?c) = _ => rewrite (e_denot_SOffg Ex 32 c _ E32x); unfold w64; f_equal; lia
  | |- sv_denot ?Ex (SLit ?z) = _ =>
    cbn [sv_denot]; unfold w64; f_equal; first [unfold dec_a_len, dec_a_u in *; lia | vm_compute; reflexivity]
  end.
Ltac e_regg HS HEIx E10x E18x E20x E24x E32x :=
  lazymatch goal with |- YK11.getr _ ?r = _ =>
    let H := fresh "Hrv" in e_rv HS r H; rewrite H; clear H; e_sv HEIx E10x E18x E20x E24x E32x end.
(* The region at index i of the state at the call. *)
Ltac e_region HS i HR :=
  lazymatch type of HS with st_ok ?sg ?Ex ?ss (restrict ?Hh ?msx) =>
    let r := eval vm_compute in (nth i (ss_mem ss) e_rg_frame) in
    assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r)
      by (apply (st_ok_region_nth Ex ss (restrict Hh msx) i r HS); vm_compute; reflexivity);
    cbn [ms_mem restrict] in HR end.
Ltac e_inl := cbn [In]; repeat (first [left; reflexivity | right]).
(* The eight chunks of the frame's shadow region at the call. *)
Ltac e_fsh_chunks :=
  intros i Hi; assert (Hi8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia;
  destruct Hi8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  eexists; (split; [e_inl | vm_compute; reflexivity]).
(* The region at index i of a state before a call, and the state in normal form. *)
Ltac e_region_pi HS i HR :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?msx =>
    let r := eval vm_compute in (nth i (ss_mem ss) e_rg_frame) in
    assert (HR : region_ok sg Ex (ms_mem msx) r)
      by (apply (st_ok_pi_region_nth Ex ss msx i r HS); vm_compute; reflexivity) end.
Ltac e_norm HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?ms => let v := eval vm_compute in ss in change ss with v in HS end.
(* The first two regions (the frame and its shadow) read only, for a shadow-checking run. *)
Ltac e_ro2 HS :=
  e_norm HS;
  let HR1 := fresh "HR" in let HR2 := fresh "HR" in
  e_region_pi HS 0%nat HR1; e_region_pi HS 1%nat HR2;
  lazymatch type of HS with st_ok_pi _ _ ?Ex (mkSS ?pc ?sr (?r1 :: ?r2 :: ?rs) ?rv ?G) ?msx =>
    let HS2 := fresh "HS" in
    pose proof (e_st_swap2 Ex pc sr r1 r2 (e_ro r1) (e_ro r2) rs rv G msx HS eq_refl eq_refl
      (e_region_ok_ro _ _ _ _ HR1) (e_region_ok_ro _ _ _ _ HR2) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as HS2;
    clear HS HR1 HR2; rename HS2 into HS end;
  e_norm HS.

Lemma e_srl26 : forall E v, ew E 20 = Z_to_bv 64 v -> 0 <= v < 2 ^ 26 ->
  U E (SAlu ALU_SRL (SOff 20 0) (SLit 26)) = 0.
Proof.
intros E v Hv Hr. rewrite U_SAlu, U_SLit, U_SOff, Hv, unsigned_lit_small by lia. cbn [zalu_raw].
change (Z.land (zcanon 26) 63) with 26. rewrite Z.add_0_r, (zcanon_id v) by (unfold M64; lia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma e_U_atom_off : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  U E (SOff n c) = v + c.
Proof. intros E n c v Hn H0 H1. rewrite U_SOff, Hn, unsigned_lit_small by exact H0. apply zcanon_id. unfold M64. lia. Qed.

(* The region at index i of the state (either form). *)
Ltac e_region_any HS i HR := first [ e_region HS i HR | e_region_pi HS i HR; cbn [ms_mem restrict] in HR ].
(* The mode is the table of decode_obj k. *)
Ltac e_mtbl k := left; exists k; split; [cbn; tauto | repeat split].


(* ------------------------------------------------------------------ *)
(* 4. The walk                                                          *)
(* ------------------------------------------------------------------ *)

Theorem llvm_a_early_ok :
  llvm_a_early_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_a_early_stmt.
intros HPCM HUTR HCELLS HROS HRNE LAWS ML MTL AMALLOC cx W' c' HB HR H074.
destruct H074 as (fx' & ly' & S' & regs' & mem' & md' & -> & Hfrm & HC & Hbl & Hmle & Hmok & R10 & R18 & R20 & R24 & Hz).
pose proof (AMALLOC fx') as AM. clear AMALLOC.
pose proof (@e_entry fx' LAWS cx W' ly' S' regs' mem' md' HB HCELLS HC R10 R18 R20) as HS.
pose proof HC as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1a & Hgp & Htp & _ & HF4 & HFa & _).
pose proof (proj1 HJ) as HAR0. pose proof (proj1 (proj2 HJ)) as Hly0.
pose proof (e_afn_stk _ _ _ _ _ _ _ (e_base_afn cx HB)) as Hstk.
pose proof Hstk as (Hsp0a & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (e_base_pn cx HB) as Hpn.
assert (Hn26 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S')) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly0 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds decodesegs0 B LAWS ly' S' W' mem' md' _ _ HAR0 Hin0) as (_ & HFc & _).
destruct (al_frames _ _ LAWS ly' S' W' mem' md' _ _ HAR0 Hin0) as (_ & Happ & _).
rewrite EF in HFc, Happ. replace (fs_frame_bytes DEC_FCLASS) with 64 in HFc, Happ by reflexivity.
assert (ESH : d_SH cx = SHADOW_OFF + d_F cx / 8) by reflexivity.
unfold DEC_LLVMF_STK in Hslo.
set (E0 := e_E regs' cx) in HS.
assert (E10 : ew E0 10 = Z_to_bv 64 (d_F cx)) by (unfold E0; rewrite (e_ew_reg regs' cx 10 10%bv) by (lia || reflexivity); exact R10).
assert (E18 : ew E0 18 = Z_to_bv 64 SHADOW_OFF) by (unfold E0; rewrite (e_ew_reg regs' cx 18 18%bv) by (lia || reflexivity); exact R18).
assert (E20 : ew E0 20 = Z_to_bv 64 (d_n cx)) by (unfold E0; rewrite (e_ew_reg regs' cx 20 20%bv) by (lia || reflexivity); exact R20).
assert (E24 : ew E0 24 = Z_to_bv 64 (d_p cx)) by (unfold E0; rewrite (e_ew_reg regs' cx 24 24%bv) by (lia || reflexivity); exact R24).
assert (E9 : ew E0 9 = Z_to_bv 64 (d_sp1 cx)) by (unfold E0; rewrite (e_ew_reg regs' cx 9 9%bv) by (lia || reflexivity); exact R9).
assert (E32 : ew E0 32 = Z_to_bv 64 (d_SH cx)) by (unfold E0; exact (e_ew_ext regs' cx 0 ltac:(lia))).
assert (RF : 0 <= d_F cx < 2 ^ 64) by lia.
assert (RSH : 0 <= d_SH cx < 2 ^ 64) by (rewrite ESH; unfold SHADOW_OFF; lia).
assert (RS1 : 0 <= d_sp1 cx < 2 ^ 64) by (unfold d_sp0 in *; lia).
assert (U10 : bv_unsigned (ew E0 10) = d_F cx) by (rewrite E10; apply unsigned_lit_small; exact RF).
assert (U32 : bv_unsigned (ew E0 32) = d_SH cx) by (rewrite E32; apply unsigned_lit_small; exact RSH).
assert (U9 : bv_unsigned (ew E0 9) = d_sp1 cx) by (rewrite E9; apply unsigned_lit_small; exact RS1).
assert (HEI : img_env (@pa_val _ decode_listing PI_decode) A_LIM E0) by (unfold E0, e_E; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 18 0) [] E0 (mrestrict (w_H W') mem')) by constructor.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ e_win cx a -> aview segs (w_H W') mem' a = aview segs (w_H W') mem' a)
  by reflexivity.
pose proof (paj_run (fx := fx') (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUN.
pose proof (paj_run_to (fx := fx') (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUNTO.
pose proof (@paj_branch fx' rc decode_listing PI_decode) as BR.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ decode_listing PI_decode) Wx
    (mkCfg (YK11.mkst regs' (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + 0x74)) mem'
      (YK11.seg_rom (@pa_segs _ decode_listing PI_decode))) md') Q) end.
(* 1. +0x074 .. +0x104: s3 = s5 = F (the `bnez s3` is decided: F >= 4096), the frame record, the redzone poison,
   112(s1) := F, up to the size test's `bnez a0`. *)
paj_run_tok RUN HS HJ SHOK E_B0; [e_awr cx EF U10 U32 U9 |].
e_kupd cx KR U10 U32 U9. e_md.
psrr_branch_tok RUN BR HS SHOK E_B0.
(* the early edge: n >> 26 <> 0, refuted by n < 2 ^ 26 *)
{ exfalso. rewrite branch_ne_U, (e_srl26 E0 (d_n cx) E20 Hn26), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
(* 2. +0x108 .. +0x114: the `beqz s4` of the length dispatch. *)
paj_run_tok RUN HS HJ SHOK E_B0; [e_awr cx EF U10 U32 U9 |].
e_kupd cx KR U10 U32 U9. e_md.
psrr_branch_tok RUN BR HS SHOK E_B0.
(* 3. n = 0 (+0x140 .. +0x230): the local's unpoison, {48000, 0, 0}, the table of decode_obj 4, malloc 0. *)
{ assert (Hn0 : d_n cx = 0)
    by (rewrite branch_eq_U, (U_atom E0 20 (d_n cx) E20), U_lit in Hc by lia; apply Z.eqb_eq in Hc; exact Hc).
  paj_run_tok RUN HS HJ SHOK E_B0; [e_awr cx EF U10 U32 U9 |].
  e_kupd cx KR U10 U32 U9. e_md.
  pmkst HS.
  change (pa_sigma DS___interceptor_trampoline_malloc) with (decode_sigma DS___interceptor_trampoline_malloc).
  rewrite <- HPCM.
  e_region HS 1%nat HR1. e_region HS 2%nat HR2.
  lazymatch goal with |- SRr _ ?Wx (mkCfg (YK11.mkst ?rg _ ?mm _) ?mdx) _ =>
    refine (@e_call fx' LAWS MTL AM HUTR cx Wx ly' S' rg mm mdx (e_tbl 4) E_NCH E_NS HB HCELLS HROS HRNE HR Hfrm _ Hbl Hmle Hmok
      _ _ _ _ _ _ _ _ _ _ _ _ _) end.
  - apply (e_core_move LAWS cx ly' S' W' regs' mem' md' _ _ _ 0 HB HC HJ KR); [|exact Hbl].
    intros r Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]];
      (lazymatch goal with |- YK11.getr _ ?r = _ => let H := fresh "Hrv" in e_rv HS r H; rewrite H, e_denot0 end;
       unfold E0; apply e_ew_reg; [lia | reflexivity]).
  - e_regg HS HEI E10 E18 E20 E24 E32.
  - split; [|split]; e_regg HS HEI E10 E18 E20 E24 E32.
  - e_regg HS HEI E10 E18 E20 E24 E32.
  - e_regg HS HEI E10 E18 E20 E24 E32.
  - e_regg HS HEI E10 E18 E20 E24 E32.
  - e_regg HS HEI E10 E18 E20 E24 E32.
  - e_regg HS HEI E10 E18 E20 E24 E32.
  - e_regg HS HEI E10 E18 E20 E24 E32.
  - e_regg HS HEI E10 E18 E20 E24 E32.
  - e_regg HS HEI E10 E18 E20 E24 E32.
  - left. exists 4%nat. split; [cbn; tauto | repeat split].
  - apply (e_fsh_of_region E0 _ _ _ cx HR1 U32). e_fsh_chunks.
  - apply (e_slot_of_region E0 _ _ _ cx HR2 U9); [e_inl | exact E10 | exact RF]. }
(* 4. n >= 1: the input block holds data[0..n), so its shadow is addressable; the frame and its shadow become read
   only and the byte at p a region (atom 33). *)
assert (Hn0 : d_n cx <> 0)
  by (rewrite branch_eq_U, (U_atom E0 20 (d_n cx) E20), U_lit in Hc by lia; apply Z.eqb_neq in Hc; exact Hc).
clear Hc.
destruct Hpn as [(Hzn & _) | (Hn1 & Hpin)]; [lia|].
assert (Hpin' : In (d_p cx, d_n cx) (ablocks B ly' S')) by (rewrite Hbl; exact Hpin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hpin') as (_ & Hp4 & Hpc & Hpa & _).
pose proof (@blk_off_imgP rc decode_listing PI_decode B ly' S' W' _ _ _ _ (proj1 HJ) Hpin') as Hpimg.
pose proof (sep_block_frame decodesegs0 B LAWS ly' S' W' _ _ _ _ _ _ (proj1 HJ) Hpin' Hin0) as Hpf.
rewrite EF in Hpf. replace (fs_frame_bytes DEC_FCLASS) with 64 in Hpf by reflexivity.
unfold zdisjoint, off_img in Hpf, Hpimg. cbn [fst snd] in Hpf.
pose proof IMG_LO_val as HIL0. pose proof IMG_TOP_val as HIT0.
pose proof (req_size_pos (d_n cx) ltac:(lia)) as Hrq.
assert (RP : 0 <= d_p cx < 2 ^ 64) by lia.
assert (U24 : bv_unsigned (ew E0 24) = d_p cx) by (rewrite E24; apply unsigned_lit_small; exact RP).
assert (EB : forall i, (i < 3)%nat -> ew E0 (33 + i) = Z_to_bv 64 (e_byte cx i)).
{ intros i Hi. replace (33 + i)%nat with (32 + S i)%nat by lia. unfold E0. rewrite e_ew_ext by lia.
  destruct i as [|[|[|i]]]; [reflexivity | reflexivity | reflexivity | lia]. }
assert (RB : forall i, 0 <= e_byte cx i < 256)
  by (intros i; unfold e_byte; pose proof (bv_unsigned_in_range 8 (nth i (d_pl cx) (Z_to_bv 8 0))) as Hr; exact Hr).
assert (UO : forall k, (k < 15)%nat -> bv_unsigned (ew E0 (A_OBJ k)) = decode_obj k).
{ intros k Hk. unfold E0. rewrite e_ew_obj by exact Hk. apply unsigned_lit_small.
  do 15 (destruct k as [|k]; [cbn; lia|]). lia. }
assert (O4 : bv_unsigned (ew E0 245) = decode_obj 4) by exact (UO 4%nat ltac:(lia)).
assert (O5 : bv_unsigned (ew E0 246) = decode_obj 5) by exact (UO 5%nat ltac:(lia)).
assert (O6 : bv_unsigned (ew E0 247) = decode_obj 6) by exact (UO 6%nat ltac:(lia)).
pose proof IMG_LO_val as IL. pose proof IMG_TOP_val as IT.
e_ro2 HS.
(* The rest is one tactic expression: its helpers name this proof's hypotheses (HS, HJ, KR, cx, E0, U10, ...),
   which a toplevel Ltac definition cannot. *)
(* e_tok: a shadow-token obligation of input byte p + c, from the input block's shadow (AR's block and shadow laws). *)
let e_tok := fun _ => first
  [ exact I
  | try (change (rd_of ?sg (mrestrict ?H ?m)) with (aview sg H m));
    lazymatch goal with |- range_addressable _ (U ?Ex (SOff 18 0)) (U ?Ex (SOff 24 ?c)) ?len =>
      rewrite (e_U_atom_off Ex 18 0 SHADOW_OFF E18) by (unfold SHADOW_OFF; lia);
      rewrite (e_U_atom_off Ex 24 c (d_p cx) E24) by lia;
      rewrite ?Z.add_0_r;
      eapply range_addressable_of_block; [ (first [exact LAWS | exact (proj1 HJ)]) .. | exact Hpin' | lia | lia ] end ] in
(* e_addp i: the region of input byte i (atom 33 + i at p + i) joins the state; i < n. *)
let e_addp := fun i =>
  (assert (Hni : Z.of_nat i + 1 <= d_n cx)
     by (first [clear -Hn1; cbn; lia | clear -Hn2; cbn; lia | clear -Hn3; cbn; lia]);
   lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?msx) =>
     assert (HRp : region_ok sg Ex (ms_mem (restrict Hh msx)) (e_rg_p i)) end;
   [ unfold e_rg_p, region_ok;
     cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
     rewrite ?ew_ewset_other by lia; rewrite U24;
     split; [lia|]; split; [lia|]; split; [intros o Ho; cbn in Ho; lia|];
     apply Forall_cons; [|apply Forall_nil];
     lazymatch goal with |- YP09.chunk_ok _ ?Ey _ _ _ =>
       apply (chunk_ok_val _ Ey _ (d_p cx) (Z.of_nat i) 1 (SOff (33 + i) 0) (e_byte cx i));
       [ rewrite (e_denot_SOffg Ey (33 + i) 0 (e_byte cx i) (EB i ltac:(lia))), Z.add_0_r; reflexivity
       | cbn; exact (RB i)
       | cbn; lia
       | exact (e_payload_byte cx ly' S' W' _ _ 0 _ i HB HJ Hbl ltac:(cbn; lia)) ] end
   | ];
   lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?msx) =>
     assert (HDJ : all_disjoint Ex (e_rg_p i) (ss_mem ss)) end;
   [ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
       let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
     cbn [all_disjoint]; unfold extent_disjoint, e_rg_p; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
     rewrite ?ew_ewset_other by lia; rewrite U24, U10, U32, U9, O4, O5, O6; cbn [decode_obj];
     rewrite ESH; unfold SHADOW_OFF;
     repeat split;
     first [ clear -Hpf Hrq Hni; lia
           | clear -Hpimg IL IT Hrq Hni; lia
           | clear -Hpa Happ Hrq Hni; pose proof (@ASAN_CEIL_range rc) as AC;
             unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia
           | clear -Hpc Hceil Hslo Hsp1r Hrq Hni; unfold d_sp0 in *; lia ]
   | ];
   lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?msx) =>
     let HS2 := fresh "HS" in
     pose proof (st_ok_pi_add_region Ex ss (restrict Hh msx) (e_rg_p i) HS eq_refl HRp HDJ) as HS2;
     clear HS HRp HDJ Hni; rename HS2 into HS end;
   e_norm HS) in
(* e_up: at +0x1c8 the input-byte regions go, the frame and its shadow are writable again (AR's frame law). *)
let e_up := fun _ =>
  (e_norm HS;
   repeat (lazymatch type of HS with
           | st_ok_pi _ _ _ (mkSS _ _ (YP09.mkRegion (Some 24%nat) _ _ _ _ _ :: _) _ _) _ => apply e_st_drop in HS
           end);
   let HR1 := fresh "HR" in let HR2 := fresh "HR" in
   e_region_pi HS 0%nat HR1; e_region_pi HS 1%nat HR2;
   let HFP := fresh "HFP" in let HSHP := fresh "HSHP" in
   destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hin0) as (_ & _ & HFP & HSHP);
   try rewrite EF in HFP; try rewrite EF in HSHP;
   try replace (fs_frame_bytes DEC_FCLASS) with 64 in HFP by reflexivity;
   try replace (fs_frame_bytes DEC_FCLASS) with 64 in HSHP by reflexivity;
   lazymatch type of HS with st_ok_pi _ _ ?Ex (mkSS ?pc ?sr (?r1 :: ?r2 :: ?rs) ?rv ?G) ?msx =>
     let W1 := fresh "W1" in let W2 := fresh "W2" in
     assert (W1 : forall o, 0 <= o < 48 -> writable_at segs (ms_mem msx) (base_val Ex (YP09.r_base r1) + o))
       by (intros o Ho; cbn [ms_mem restrict base_val YP09.r_base]; rewrite ?ew_ewset_other by lia; rewrite U10;
           apply (apresent_writable segs); exact (proj1 (HFP (d_F cx + o) ltac:(lia))));
     assert (W2 : forall o, 0 <= o < 8 -> writable_at segs (ms_mem msx) (base_val Ex (YP09.r_base r2) + o))
       by (intros o Ho; cbn [ms_mem restrict base_val YP09.r_base]; rewrite ?ew_ewset_other by lia; rewrite U32, ESH;
           apply (apresent_writable segs); unfold shadow_addr in HSHP; apply (HSHP o); change (64 / 8) with 8; lia);
     let HS2 := fresh "HS" in
     pose proof (e_st_swap2 Ex pc sr r1 r2 (e_rw r1 0 48) (e_rw r2 0 8) rs rv G msx HS eq_refl eq_refl
       (e_region_ok_rw _ _ _ _ 0 48 HR1 W1) (e_region_ok_rw _ _ _ _ 0 8 HR2 W2)
       eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as HS2;
     clear HS HR1 HR2 HFP HSHP W1 W2; rename HS2 into HS end;
   e_norm HS) in
(* e_fin: malloc #1 from the state at the call, e_call with every premise but the mode (the one goal left). *)
let e_fin := fun mode nch ns =>
  (pmkst HS;
   change (pa_sigma DS___interceptor_trampoline_malloc) with (decode_sigma DS___interceptor_trampoline_malloc);
   rewrite <- HPCM;
   let HR1 := fresh "HRs" in let HR2 := fresh "HRp" in
   e_region_any HS 1%nat HR1; e_region_any HS 2%nat HR2;
   lazymatch goal with |- SRr _ ?Wx (mkCfg (YK11.mkst ?rg _ ?mm _) ?mdx) _ =>
     refine (@e_call fx' LAWS MTL AM HUTR cx Wx ly' S' rg mm mdx mode nch ns HB HCELLS HROS HRNE HR Hfrm _ Hbl Hmle Hmok
       _ _ _ _ _ _ _ _ _ _ _ _ _) end;
   [ apply (e_core_move LAWS cx ly' S' W' regs' mem' md' _ _ _ 0 HB HC HJ KR); [|exact Hbl];
     let r := fresh "r" in let Hr := fresh "Hr" in
     intros r Hr; cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]];
     (lazymatch goal with |- YK11.getr _ ?rr = _ => let H := fresh "Hrv" in e_rv HS rr H; rewrite H, e_denot0 end;
      rewrite ?ew_ewset_other by lia; unfold E0; apply e_ew_reg; [lia | reflexivity])
   | e_regg HS HEI E10 E18 E20 E24 E32
   | split; [|split]; e_regg HS HEI E10 E18 E20 E24 E32
   | e_regg HS HEI E10 E18 E20 E24 E32
   | e_regg HS HEI E10 E18 E20 E24 E32
   | e_regg HS HEI E10 E18 E20 E24 E32
   | e_regg HS HEI E10 E18 E20 E24 E32
   | e_regg HS HEI E10 E18 E20 E24 E32
   | e_regg HS HEI E10 E18 E20 E24 E32
   | e_regg HS HEI E10 E18 E20 E24 E32
   | e_regg HS HEI E10 E18 E20 E24 E32
   | idtac
   | apply (e_fsh_of_region _ _ _ _ cx HR1 U32); e_fsh_chunks
   | apply (e_slot_of_region _ _ _ _ cx HR2 U9); [e_inl | exact E10 | exact RF] ]) in
(* e_mloc: the mode is the frame's local; its two signed words are the frame region's chunks at +36 / +40. *)
let e_vloc := fun _ =>
  lazymatch goal with |- context [sv_denot ?Ey _] =>
  first [ exact (e_sx_sra Ey _ (EB 1%nat ltac:(lia)) (RB 1%nat))
        | exact (e_sx_lb Ey _ (EB 2%nat ltac:(lia)) (RB 2%nat))
        | cbn [sv_denot]; rewrite unsigned_lit_small by lia; reflexivity ] end in
let e_mloc := fun _ =>
  (right; split; [reflexivity|];
   let HR0 := fresh "HRf" in e_region_any HS 0%nat HR0;
   split; [first [exact (e_s8_range _ (RB 1%nat)) | lia]|];
   split; [first [exact (e_s8_range _ (RB 2%nat)) | lia]|];
   eapply (e_local_of_region _ _ _ _ cx _ _ _ _ HR0 U10); [e_inl | e_inl | e_vloc tt | e_vloc tt]) in
(* e_step: one run to the next stop (a branch or the call), with its awr and kept-bytes bookkeeping. *)
let e_step := fun Bs =>
  (paj_run_tok RUN HS HJ SHOK Bs; [ (e_tok tt) .. | e_awr cx EF U10 U32 U9 | ];
   e_kupd cx KR U10 U32 U9; e_md) in
let e_step_to := fun Bs stop =>
  (paj_run_to_tok RUNTO HS HJ SHOK Bs stop; [ (e_tok tt) .. | e_awr cx EF U10 U32 U9 | ];
   e_kupd cx KR U10 U32 U9; e_md) in
(* e_tail: from +0x1c8 (the three n >= 1 arms), the unpoison, the local's words, the mode select on
   sel = data[0] & 3 and malloc #1; the local mode (sel = 3) is the one goal left. *)
let e_tail := fun nch ns =>
  (e_up tt;
   e_step E_B0;
   psrr_branch_tok RUN BR HS SHOK E_B0;
   [ (* 1 < sel: +0x1f4 *) clear Hc; e_step E_B0;
     psrr_branch_tok RUN BR HS SHOK E_B0;
     [ (* sel <> 2: the local, +0x220 *) clear Hc; e_step E_B0; e_fin constr:(d_F cx + 32) nch ns
     | (* sel = 2: decode_obj 5, +0x1fc *) clear Hc; e_step E_B0; e_fin constr:(e_tbl 5) E_NCH E_NS; e_mtbl 5%nat ]
   | (* sel <= 1: +0x1e4 *) clear Hc; e_step E_B0;
     psrr_branch_tok RUN BR HS SHOK E_B0;
     [ (* sel <> 0: decode_obj 6, +0x208 *) clear Hc; e_step E_B0; e_fin constr:(e_tbl 6) E_NCH E_NS; e_mtbl 6%nat
     | (* sel = 0: decode_obj 4, +0x1e8 *) clear Hc; e_step E_B0; e_fin constr:(e_tbl 4) E_NCH E_NS; e_mtbl 4%nat ] ]) in
(* e_hc: the branch condition `bne s4, k` in terms of n (the run's environment extends E0). *)
let e_hc := fun _ =>
  (rewrite branch_ne_U in Hc;
   lazymatch type of Hc with context [U ?Ey (SOff 20 0)] => rewrite (U_atom Ey 20 (d_n cx) E20) in Hc by lia end;
   rewrite ?U_lit in Hc by lia) in
(* data[0]'s region and the pointer fact of p. *)
e_addp 0%nat;
(lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?msx =>
   let HS2 := fresh "HS" in
   pose proof (st_ok_pi_add_fact Ex ss msx 24 (PTR 0) HS
     ltac:(unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite U24, Z.pow_0_r, Z.mod_1_r; lia)) as HS2;
   clear HS; rename HS2 into HS end);
e_norm HS;
(* +0x118 .. +0x134: data[0]'s shadow check (token rule, slow path +0xa7c), lbu, `bne s4, a2` (n = 1?). *)
e_step Bspan;
psrr_branch_tok RUN BR HS SHOK Bspan;
[ (* 5. n <> 1 (+0x174 .. +0x190): data[1]'s shadow check, lbu, `bne s4, a5` (n = 2?). *)
  assert (Hn2 : 2 <= d_n cx)
    by (e_hc tt; assert (d_n cx <> 1) by (intro E1; rewrite E1 in Hc; discriminate Hc); lia);
  clear Hc; e_addp 1%nat;
  e_step Bspan;
  psrr_branch_tok RUN BR HS SHOK Bspan;
  [ (* 6. n >= 3 (+0x1a0 .. +0x1c4): data[2]'s shadow check, lb, s10 = n - 3, s8 = p + 3. *)
    assert (Hn3 : 3 <= d_n cx)
      by (e_hc tt; assert (d_n cx <> 2) by (intro E1; rewrite E1 in Hc; discriminate Hc); lia);
    clear Hc; e_addp 2%nat;
    e_step_to Bspan 456;
    e_tail constr:(e_s8 (e_byte cx 1)) constr:(e_s8 (e_byte cx 2));
    e_mloc tt
  | (* 7. n = 2 (+0x194 .. +0x1c4): s10 = 0, ns = 0, s8 = p + 2. *)
    assert (Heq2 : d_n cx = 2)
      by (e_hc tt; destruct (Z.eqb_spec (d_n cx) 2) as [|Hne]; [assumption|];
          apply Z.eqb_neq in Hne; try rewrite Hne in Hc; discriminate Hc);
    clear Hc;
    e_step_to Bspan 456;
    e_tail constr:(e_s8 (e_byte cx 1)) constr:(0);
    e_mloc tt ]
| (* 8. n = 1 (+0x138 .. +0x1c4): nch = ns = 0, s10 = 0, s8 = p + 1. *)
  assert (Heq1 : d_n cx = 1)
    by (e_hc tt; destruct (Z.eqb_spec (d_n cx) 1) as [|Hne]; [assumption|];
        apply Z.eqb_neq in Hne; try rewrite Hne in Hc; discriminate Hc);
  clear Hc;
  e_step_to Bspan 456;
  e_tail constr:(0) constr:(0);
  e_mloc tt ].
Qed.

End early.
