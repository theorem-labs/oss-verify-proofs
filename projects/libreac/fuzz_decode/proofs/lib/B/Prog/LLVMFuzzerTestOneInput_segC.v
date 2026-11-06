(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the copy segment of the image-B walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput (llvm_b_copy_stmt of LLVMFuzzerTestOneInput_segs.v), with proof steps adapted from proofs/libreac/fuzz_boxreg/lib/A/Prog/ReadName.v (a working branch: the run / branch / call pattern); ew_Eimg_Ereg_nat and img_env_atomP copied from this unit's lib/A/Prog/YC1g.v / YC1h.v at image B's PAImg; the malloc call step and eb_ch / eb_chain_at / eb_trace_at / eb_rdword_of_bytes / eb_rdword_of_val_mem copied from lib/B/Prog/LLVMFuzzerTestOneInput_segB.v (a working branch 84be2173fcc); the two leaf calls in the shape of lib/B/Prog/LLVMFuzzerTestOneInput_leafb.v's dec_leafb_inspect; module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YImgTop YO09 YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
  YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBAddr
  DecodeBPa DecodeBPaLib DecodeBImg check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_frame_is_reac_c reac_frame_clean_len_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_leafb.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require LiaTwx2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.
(* YC4b switches lia's division handling off for its importers; this file's arithmetic needs it (ReadName.v's line). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* PaTable's YM03.v:182-189 redefines lia / nia globally (context pruning, retries); this file uses the lia the
   donor proofs were built under, lib/Lib/LiaTwx2.v:187-190's (zify_prune first), and YM03.v:180's nia. *)
Local Ltac Lia.lia ::=
  first [ LiaTwx2.zify_prune; LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

(* ------------------------------------------------------------------ *)
(* 1. Image B's copies of the YC1g / YC1h step helpers                  *)
(* ------------------------------------------------------------------ *)

Section hb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable dbsym} {PL : PAListing L} {PI : PAImg L}.
#[local] Abbreviation VAL := (pa_val).
Lemma ew_Eimg_Ereg_natB : forall (regs : bvmap 5 word) extra n (r : bv 5),
Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma img_env_atomB : forall E a, img_env VAL A_LIM E -> (A_TEXT <= a < A_LIM)%nat -> ew E a = Z_to_bv 64 (VAL a).
Proof. intros E a HE Ha. rewrite <- (HE a Ha). symmetry. apply Z_to_bv_bv_unsigned. Qed.
End hb.

(* ------------------------------------------------------------------ *)
(* 2. Memory helpers                                                    *)
(* ------------------------------------------------------------------ *)

Section mh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
(* After grant's lib/A/Prog/GrantFrame.v val_mem_moved: a value read at a moved address. *)
Lemma cp_val_mem_moved : forall H H' (m m' : word -> option byte) a b n v,
(forall k, 0 <= k < Z.of_nat n -> aview segs H' m' (b + k) = aview segs H m (a + k)) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') b n v.
Proof.
intros H H' m m' a b n v Hk Hv k Hkn. specialize (Hk (Z.of_nat k) ltac:(lia)). unfold aview in Hk.
rewrite (Hv k Hkn) in Hk. destruct (mbyte segs (mrestrict H' m') (b + Z.of_nat k)) as [b'|]; cbn in Hk; [|discriminate].
injection Hk as Hk. f_equal. apply bv_eq. exact Hk.
Qed.
Lemma cp_garr8_kept : forall H H' (m m' : word -> option byte) base l,
(forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' m' (base + j) = aview segs H m (base + j)) ->
garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H' m') base l.
Proof.
intros H H' m m' base l HK HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
apply (cp_val_mem_moved H H' m m' (base + Z.of_nat j) (base + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk. replace (base + Z.of_nat j + k) with (base + (Z.of_nat j + k)) by lia. apply HK. lia.
Qed.
Lemma cp_rdword_kept : forall (r r' : reader) a, (forall i, 0 <= i < 8 -> r' (a + i) = r (a + i)) -> rdword r' a = rdword r a.
Proof.
intros r r' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma cp_val_mem_of_rd32 : forall H mem a v,
rd32 (aview segs H mem) a v -> val_mem segs (mrestrict H mem) a 4 v.
Proof.
intros H mem a v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
(* A four-byte value is determined by its bytes. *)
Lemma cp_le4_eq : forall v w, 0 <= w < 2 ^ 32 -> (forall k, (k < 4)%nat -> le_byte v 4 k = le_byte w 4 k) -> v mod 2 ^ 32 = w.
Proof.
intros v w Hw Hk.
assert (E : forall z k, (k < 4)%nat -> le_byte z 4 k = (z mod 2 ^ 32) / 2 ^ (8 * Z.of_nat k) mod 256).
{ intros z k _. unfold le_byte. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
pose proof (Hk 0%nat ltac:(lia)) as K0. pose proof (Hk 1%nat ltac:(lia)) as K1.
pose proof (Hk 2%nat ltac:(lia)) as K2. pose proof (Hk 3%nat ltac:(lia)) as K3.
rewrite !E in K0, K1, K2, K3 by lia. rewrite (Z.mod_small w) in K0, K1, K2, K3 by lia.
cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in K0, K1, K2, K3.
change (2 ^ (8 * 0)) with 1 in K0. change (2 ^ (8 * 1)) with 256 in K1.
change (2 ^ (8 * 2)) with 65536 in K2. change (2 ^ (8 * 3)) with 16777216 in K3.
pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)) as Bv.
set (x := v mod 2 ^ 32) in *. clearbody x. rewrite Z.div_1_r in K0, K0.
lia.
Qed.
Lemma cp_val_mem_rd32 : forall H mem a v w,
val_mem segs (mrestrict H mem) a 4 v -> rd32 (aview segs H mem) a w -> 0 <= w < 2 ^ 32 -> v mod 2 ^ 32 = w.
Proof.
intros H mem a v w Hv Hr Hw. apply cp_le4_eq; [exact Hw|]. intros k Hk.
pose proof (Hv k Hk) as Hm. pose proof (Hr k Hk) as Ha. unfold aview in Ha. rewrite Hm in Ha. cbn in Ha.
injection Ha as Ha. rewrite <- Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
symmetry. apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.
End mh.

(* ------------------------------------------------------------------ *)
(* 3. The invariant between the copy segment's calls                    *)
(* ------------------------------------------------------------------ *)

Section sg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := dec_B_sink_head.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegsB0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).
Local Abbreviation BASE := (decodeb_val A_TEXT).
Local Abbreviation st27c := (llvm_b_st_27c B MT).
Local Abbreviation len cx := (dec_b_len (d_n cx)).

(* The three mode tables of the image (the RELRO words decodeb_obj 4 / 5 / 6 point at them; dec_crt_cells rows). *)
Definition cp_tbl : list Z := [0x20d60; 0x20da0; 0x20d80].
(* Where the mode is: the frame's local, or a table whose two fields are 40 and 12. *)
Definition cp_mode_where (cx : dctx) (mode nch ns : Z) : Prop :=
  mode = d_F cx + 32 \/ (In mode cp_tbl /\ nch = 40 /\ ns = 12).

(* Everything llvm_b_st_27c states that this segment keeps, at a state where the frame is still in its spill slots;
   the copy's bytes are added once __asan_memcpy has run (cp_inv). *)
Definition cp_base0 (cx : dctx) (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) (res mode nch ns : Z) : Prop :=
  dec_b_core B cx ly' S' W' regs' mem' md' dec_ev_27c /\
  ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) ++ [(res, len cx)] /\
  4096 <= res /\
  mo_le MT (d_S cx) S' (dec_spent_27c MT (d_n cx)) /\ mo_ok MT S' (dec_rest_27c MT) /\
  dec_b_frs cx (aview segs (w_H W') mem') /\
  YK11.getr regs' 18 = w64 SHADOW_OFF /\
  YK11.getr regs' 20 = w64 (len cx) /\
  YK11.getr regs' 21 = w64 mode /\
  YK11.getr regs' 22 = w64 (mode + 8) /\
  YK11.getr regs' 23 = w64 (mode + 4) /\
  dec_b_mode_ok cx W' mem' mode nch ns /\
  cp_mode_where cx mode nch ns /\
  dec_b_fsh cx (aview segs (w_H W') mem') 0 4 /\
  dec_b_slot cx (aview segs (w_H W') mem') 112 (d_F cx).
(* From +0x27c on, s11 is the copy. *)
Definition cp_base (cx : dctx) (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) (res mode nch ns : Z) : Prop :=
  cp_base0 cx ly' S' W' regs' mem' md' res mode nch ns /\ YK11.getr regs' 27 = w64 res.
Definition cp_inv (cx : dctx) (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) (res mode nch ns : Z) : Prop :=
  cp_base cx ly' S' W' regs' mem' md' res mode nch ns /\
  garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)).

(* The bytes cp_base reads: the 13 saved words, the four spill slots it states, the fake frame, its shadow, and the
   caller's payload. *)
Definition cp_kz (cx : dctx) (a : Z) : Prop :=
  (d_sp0 cx - 104 <= a < d_sp0 cx) \/ (d_sp1 cx <= a < d_sp1 cx + 24) \/ (d_sp1 cx + 112 <= a < d_sp1 cx + 120) \/
  (d_F cx <= a < d_F cx + 64) \/ (d_SH cx <= a < d_SH cx + 8) \/
  (0 < d_n cx /\ d_p cx <= a < d_p cx + d_n cx).

(* The read-only bytes the walk reads (DEC_RO_RD) as the image holds them, at any state of the walk's journal: the
   journal's image clause (YCbq.v:362) keeps them from the entry, where HROM shows them, because they are neither
   owned statics nor errno (dec_ro_rd_scoped). *)
Lemma cp_rom_view_rd : forall cx ly S W mem md k,
  dec_ro_rd_unowned B -> dec_rom_no_errno B -> dec_b_rom cx ->
  @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S W mem md k ->
  dec_rom_view_rd W mem.
Proof.
intros cx ly S W mem md k HO HE HR HJ a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (dec_ro_rd_rom_clean a Ha) as [Hrom _].
destruct (dec_ro_rd_scoped B HO HE a Ha) as [Hno Hne].
rewrite F3; [| destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | lia] | exact Hno | exact Hne
  | intros (r & Hr & _); destruct Hr].
apply HR. exact Hrom.
Qed.
(* An 8-byte read-only word of DEC_RO_RD, read through dec_rom_view_rd. *)
Lemma cp_rom_word : forall W mem a v, dec_rom_view_rd W mem ->
  (forall i, 0 <= i < 8 -> dec_in_ro_rd (a + i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 x))) a = Some v ->
  val_mem segs (rd W mem) a 8 v.
Proof.
intros W mem a v HV Hin Hr. apply val_mem_of_rdword.
rewrite <- Hr. apply cp_rdword_kept. intros i Hi. apply HV. apply Hin. exact Hi.
Qed.
Lemma cp_in_ro_rd : forall a n i, In (a, n) DEC_RO_RD -> 0 <= i < n -> dec_in_ro_rd (a + i).
Proof. intros a n i Hin Hi. apply Exists_exists. exists (a, n). split; [exact Hin | unfold in_zr; cbn; lia]. Qed.

(* The three .got pointer words of the tables (dec_crt_cells rows 18-20). *)
Lemma cp_tbl_rows : forall ly, dec_crt_cells B ->
  In (z8 (ANum (decodeb_obj 4)) 0x20d60) (as_const B ly) /\ In (z8 (ANum (decodeb_obj 5)) 0x20da0) (as_const B ly) /\
  In (z8 (ANum (decodeb_obj 6)) 0x20d80) (as_const B ly).
Proof.
intros ly HC. destruct (HC ly) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  P4 & P5 & P6 & _).
exact (conj P4 (conj P5 P6)).
Qed.

(* The tables' two fields as the image holds them: 40 at t + 4, 12 at t + 8 (read on the pinned image). *)
Lemma cp_rom_fields : forall t, In t cp_tbl ->
  (forall k, (k < 4)%nat ->
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 (t + 4 + Z.of_nat k))) =
     Some (le_byte 40 4 k)) /\
  (forall k, (k < 4)%nat ->
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 (t + 8 + Z.of_nat k))) =
     Some (le_byte 12 4 k)).
Proof.
intros t Ht. unfold cp_tbl in Ht. cbn in Ht.
destruct Ht as [<- | [<- | [<- | []]]]; split; intros k Hk;
  (do 4 (destruct k as [|k]; [vm_compute; reflexivity|])); lia.
Qed.
(* The fields through the read-only view (DEC_RO_RD's table ranges (t + 4, 8)). *)
Lemma cp_tbl_rd32 : forall (W : world segs) mem t, dec_rom_view_rd W mem -> In t cp_tbl ->
  rd32 (aview segs (w_H W) mem) (t + 4) 40 /\ rd32 (aview segs (w_H W) mem) (t + 8) 12.
Proof.
intros W mem t HRV Ht.
assert (IN : forall i, 0 <= i < 8 -> dec_in_ro_rd (t + 4 + i)).
{ intros i Hi. pose proof Ht as Ht'. unfold cp_tbl in Ht'. cbn in Ht'.
  destruct Ht' as [<- | [<- | [<- | []]]]; (apply (cp_in_ro_rd _ 8); [cbn; auto 10 | lia]). }
destruct (cp_rom_fields t Ht) as (R4 & R8).
split; intros k Hk.
- rewrite (HRV _ (IN (Z.of_nat k) ltac:(lia))). exact (R4 k Hk).
- replace (t + 8 + Z.of_nat k) with (t + 4 + (4 + Z.of_nat k)) by lia.
  rewrite (HRV _ (IN (4 + Z.of_nat k) ltac:(lia))).
  replace (t + 4 + (4 + Z.of_nat k)) with (t + 8 + Z.of_nat k) by lia. exact (R8 k Hk).
Qed.
Lemma cp_tbl_fields : forall (W : world segs) mem t, dec_rom_view_rd W mem -> In t cp_tbl ->
  val_mem segs (rd W mem) (t + 4) 4 40 /\ val_mem segs (rd W mem) (t + 8) 4 12.
Proof.
intros W mem t HRV Ht. destruct (cp_tbl_rd32 W mem t HRV Ht) as (F4 & F8).
split; apply cp_val_mem_of_rd32; assumption.
Qed.

(* What the walk needs to read DEC_RO_RD at any state of its journal (cp_rom_view_rd). *)
Definition cp_romctx (cx : dctx) : Prop := dec_ro_rd_unowned B /\ dec_rom_no_errno B /\ dec_b_rom cx.

(* What the frame invariant gives about the walk's addresses: the entry sp is a stack address well above the
   allocator ceiling, and the fake frame is the one frame of the state, in application memory below the ceiling. *)
Lemma cp_core_facts : forall cx ly S W regs mem md k,
  AR_laws segs B -> dec_b_core B cx ly S W regs mem md k ->
  alloc_ceiling + 32768 <= d_sp0 cx <= 2 ^ 47 /\ d_sp0 cx mod 16 = 0 /\
  frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx /\ In (DEC_FCLASS, d_fpos cx) (frames S) /\
  d_F cx + 64 <= alloc_ceiling /\ in_app (d_F cx) 64.
Proof.
intros cx ly S W regs mem md k LAWS Hc.
destruct Hc as (HJ & Hfrms & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & _ & Hceil & Hlo & Hhi & H47 & _).
assert (EF : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx).
{ unfold d_F, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hin : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrms; left; reflexivity).
destruct (frames_bounds segs B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin) as (_ & Hfc & Hfa).
rewrite EF in Hfc, Hfa. change (fs_frame_bytes DEC_FCLASS) with 64 in Hfc, Hfa.
unfold DEC_LLVMF_STK in *. split; [lia|]. split; [exact Hal|]. split; [exact EF|]. split; [exact Hin|]. split; [exact Hfc | exact Hfa].
Qed.

(* cp_base0 at a later state of the same journal: the callee-saved registers but s11 kept, and every byte it reads
   kept; a table's pointer word is a constant cell of B (dec_crt_cells) and its fields are read-only image bytes
   (DEC_RO_RD, cp_rom_view_rd), so both are re-read at the new state. *)
Lemma cp_base0_kept : forall cx ly S W regs mem md res mode nch ns W2 regs2 mem2 md2 (Zs : Z -> Prop),
  AR_laws segs B -> dec_crt_cells B -> cp_romctx cx -> d_n cx = Z.of_nat (length (d_pl cx)) ->
  cp_base0 cx ly S W regs mem md res mode nch ns ->
  @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S W2 mem2 md2 dec_ev_27c ->
  (forall r, acallee_saved r -> r <> 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W2) mem2 a) ->
  (forall a, Zs a -> ~ cp_kz cx a) ->
  cp_base0 cx ly S W2 regs2 mem2 md2 res mode nch ns.
Proof.
intros cx ly S W regs mem md res mode nch ns W2 regs2 mem2 md2 Zs LAWS HC RC Hnl HB HJ2 HP HK HPr HZ.
pose proof (cp_core_facts cx ly S W regs mem md _ LAWS (proj1 HB)) as (Hsp0 & Hsp16 & EF & Hin & HFc & HFa).
destruct HB as (Hcore & Hbl & Hres & Hmle & Hmok & Hfrs & R18 & R20 & R21 & R22 & R23 & Hmode & Hwhere & Hfsh & H112).
destruct Hcore as (HJ & Hfrms & R8 & R9 & Rsp & Hsp1 & Hsp32 & R3 & R4 & Hsaved & HF4096 & HF32 & HFpres & HFL & Hpay & Hgarr).
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KA : forall a, cp_kz cx a -> 0 <= a < 2 ^ 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha H64. apply HK; [exact H64|]. intros Hz. exact (HZ a Hz Ha). }
assert (HSH : 0 <= d_SH cx /\ d_SH cx + 8 < 2 ^ 64).
{ unfold d_SH, shadow_addr. unfold in_app in HFa. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
assert (Hpb : 0 < d_n cx -> 4096 <= d_p cx /\ d_p cx + d_n cx <= alloc_ceiling).
{ intros Hn. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (Hpay Hn)) as (_ & H4096 & Hc & _).
  pose proof (req_size_pos (d_n cx) ltac:(lia)). lia. }
assert (RG : forall r, acallee_saved r -> r <> 27 -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) by exact HP.
assert (SL : forall off v, 0 <= off -> (off + 8 <= 24 \/ off = 112) -> dec_b_slot cx (aview segs (w_H W) mem) off v ->
  dec_b_slot cx (aview segs (w_H W2) mem2) off v).
{ intros off v Ho Ho2 Hs. unfold dec_b_slot in *. rewrite (cp_rdword_kept (aview segs (w_H W) mem)); [exact Hs|]. intros i Hi. apply KA; [|lia].
  unfold cp_kz. destruct Ho2 as [Ho2 | ->]; [right; left; lia | right; right; left; lia]. }
refine (conj _ (conj Hbl (conj Hres (conj Hmle (conj Hmok (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
  (conj _ (conj Hwhere (conj _ _)))))))))))))).
- refine (conj HJ2 (conj Hfrms (conj _ (conj _ (conj _ (conj Hsp1 (conj Hsp32 (conj _ (conj _ (conj _ (conj HF4096
    (conj HF32 (conj _ (conj _ (conj Hpay _))))))))))))))).
  + transitivity (YK11.getr regs 8); [apply (RG 8); [unfold acallee_saved; lia | lia] | exact R8].
  + transitivity (YK11.getr regs 9); [apply (RG 9); [unfold acallee_saved; lia | lia] | exact R9].
  + unfold spZ in *. rewrite <- Rsp. f_equal. apply (RG 2); [unfold acallee_saved; lia | lia].
  + transitivity (YK11.getr regs 3); [apply (RG 3); [unfold acallee_saved; lia | lia] | exact R3].
  + transitivity (YK11.getr regs 4); [apply (RG 4); [unfold acallee_saved; lia | lia] | exact R4].
  + unfold dec_b_saved in *. rewrite Forall_forall in *. intros o Ho.
    assert (Hfo : 8 <= fst o <= 104).
    { unfold dec_b_saved_at in Ho. cbn in Ho. repeat (destruct Ho as [<- | Ho]; [cbn; lia|]). contradiction. }
    rewrite (cp_rdword_kept (aview segs (w_H W) mem)); [exact (Hsaved o Ho)|]. intros i Hi. apply KA; [unfold cp_kz; left; lia | lia].
  + intros a Ha. apply HPr. exact (HFpres a Ha).
  + rewrite (cp_rdword_kept (aview segs (w_H W) mem)); [exact HFL|]. intros i Hi. apply KA; [unfold cp_kz; right; right; right; left; lia | lia].
  + apply (cp_garr8_kept segs (w_H W) (w_H W2) mem mem2); [|exact Hgarr]. intros j Hj. rewrite length_map in Hj.
    apply KA; [unfold cp_kz; right; right; right; right; right; lia | pose proof (Hpb ltac:(lia)); lia].
- destruct Hfrs as (S0 & S8 & S16). split; [|split]; apply SL; first [assumption | lia].
- transitivity (YK11.getr regs 18); [apply (RG 18); [unfold acallee_saved; lia | lia] | exact R18].
- transitivity (YK11.getr regs 20); [apply (RG 20); [unfold acallee_saved; lia | lia] | exact R20].
- transitivity (YK11.getr regs 21); [apply (RG 21); [unfold acallee_saved; lia | lia] | exact R21].
- transitivity (YK11.getr regs 22); [apply (RG 22); [unfold acallee_saved; lia | lia] | exact R22].
- transitivity (YK11.getr regs 23); [apply (RG 23); [unfold acallee_saved; lia | lia] | exact R23].
- destruct Hwhere as [Hcu | (Hin_t & -> & ->)].
  + destruct Hmode as (_ & Hnch & Hns & V4 & V8). refine (conj (or_intror (or_intror (or_intror Hcu))) (conj Hnch (conj Hns (conj _ _)))).
    * apply (val_mem_kept segs (w_H W) (w_H W2) mem mem2); [|exact V4]. intros k Hk. cbn in Hk.
      apply KA; [unfold cp_kz; right; right; right; left; lia | lia].
    * apply (val_mem_kept segs (w_H W) (w_H W2) mem mem2); [|exact V8]. intros k Hk. cbn in Hk.
      apply KA; [unfold cp_kz; right; right; right; left; lia | lia].
  + pose proof (proj1 HJ2) as HAR2.
    assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W2) mem2) c).
    { intros c Hc. destruct HAR2 as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
    destruct (cp_tbl_rows ly HC) as (P4 & P5 & P6).
    destruct RC as (HO & HE & HR).
    destruct (cp_tbl_fields W2 mem2 mode (cp_rom_view_rd cx ly S W2 mem2 md2 _ HO HE HR HJ2) Hin_t) as (V4' & V8').
    change (40 mod 2 ^ 32) with 40. change (12 mod 2 ^ 32) with 12.
    split; [|split; [lia|split; [lia|split; [exact V4' | exact V8']]]].
    unfold cp_tbl in Hin_t. cbn in Hin_t. destruct Hin_t as [<- | [<- | [<- | []]]].
    * left. apply (rdword_cell B ly); [lia | exact (CH _ P4)].
    * right; left. apply (rdword_cell B ly); [lia | exact (CH _ P5)].
    * right; right; left. apply (rdword_cell B ly); [lia | exact (CH _ P6)].
- destruct Hfsh as (L1 & L4 & L5 & L6). unfold dec_b_fsh.
  split; [|split; [|split]].
  + intros i Hi. rewrite KA; [apply L1; lia | unfold cp_kz; right; right; right; right; left; lia | lia].
  + rewrite KA; [exact L4 | unfold cp_kz; right; right; right; right; left; lia | lia].
  + rewrite KA; [exact L5 | unfold cp_kz; right; right; right; right; left; lia | lia].
  + intros i Hi. rewrite KA; [apply L6; lia | unfold cp_kz; right; right; right; right; left; lia | lia].
- apply SL; [lia | right; reflexivity | exact H112].
Qed.
Lemma cp_base_kept : forall cx ly S W regs mem md res mode nch ns W2 regs2 mem2 md2 (Zs : Z -> Prop),
  AR_laws segs B -> dec_crt_cells B -> cp_romctx cx -> d_n cx = Z.of_nat (length (d_pl cx)) ->
  cp_base cx ly S W regs mem md res mode nch ns ->
  @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S W2 mem2 md2 dec_ev_27c ->
  aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W2) mem2 a) ->
  (forall a, Zs a -> ~ cp_kz cx a) ->
  cp_base cx ly S W2 regs2 mem2 md2 res mode nch ns.
Proof.
intros cx ly S W regs mem md res mode nch ns W2 regs2 mem2 md2 Zs LAWS HC RC Hnl (HB0 & R27) HJ2 HP HK HPr HZ.
split.
- apply (cp_base0_kept cx ly S W regs mem md res mode nch ns W2 regs2 mem2 md2 Zs LAWS HC RC Hnl HB0 HJ2); try assumption.
  intros r Hr _. exact (HP r Hr).
- transitivity (YK11.getr regs 27); [apply (HP 27); unfold acallee_saved; lia | exact R27].
Qed.

(* At +0x27c the mode is the local or one of the three tables (dec_crt_cells' pointer rows, the fields through the
   read-only view). *)
Lemma cp_where_of : forall cx ly S W mem md mode nch ns,
  dec_crt_cells B -> AR segs B ly S W mem md -> dec_rom_view_rd W mem ->
  dec_b_mode_ok cx W mem mode nch ns -> cp_mode_where cx mode nch ns.
Proof.
intros cx ly S W mem md mode nch ns HC HAR HRV Hmode.
destruct Hmode as (Hsel & Hnch & Hns & V4 & V8).
assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
{ intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
destruct (cp_tbl_rows ly HC) as (P4 & P5 & P6).
assert (FT : forall t, In t cp_tbl -> t = mode -> cp_mode_where cx mode nch ns).
{ intros t Ht <-. right. split; [exact Ht|].
  destruct (cp_tbl_rd32 W mem t HRV Ht) as (F4 & F8).
  pose proof (cp_val_mem_rd32 segs (w_H W) mem _ _ 40 V4 F4 ltac:(lia)) as E4.
  pose proof (cp_val_mem_rd32 segs (w_H W) mem _ _ 12 V8 F8 ltac:(lia)) as E8.
  rewrite Z.mod_mod in E4, E8 by lia. split; lia. }
destruct Hsel as [R | [R | [R | R]]]; [ | | | left; exact R].
- rewrite (rdword_cell B ly (aview segs (w_H W) mem) (decodeb_obj 4) 0x20d60 ltac:(lia) (CH _ P4)) in R.
  injection R as R. exact (FT 0x20d60 ltac:(cbn; auto) R).
- rewrite (rdword_cell B ly (aview segs (w_H W) mem) (decodeb_obj 5) 0x20da0 ltac:(lia) (CH _ P5)) in R.
  injection R as R. exact (FT 0x20da0 ltac:(cbn; auto) R).
- rewrite (rdword_cell B ly (aview segs (w_H W) mem) (decodeb_obj 6) 0x20d80 ltac:(lia) (CH _ P6)) in R.
  injection R as R. exact (FT 0x20d80 ltac:(cbn; auto) R).
Qed.

(* The copy's length and the body: len = n - u, the body is the last len input bytes. *)
Lemma cp_len_facts : forall cx, 0 <= d_n cx -> d_n cx = Z.of_nat (length (d_pl cx)) ->
  0 <= len cx /\ 0 <= dec_b_u (d_n cx) /\ dec_b_u (d_n cx) + len cx = d_n cx /\
  Z.of_nat (length (d_body cx)) = len cx /\ (0 < len cx -> dec_b_u (d_n cx) = 3).
Proof.
intros cx Hn Hl. unfold d_body, dec_b_len, dec_b_u in *. rewrite length_skipn. lia.
Qed.
Lemma cp_body_nth : forall cx j, d_n cx = Z.of_nat (length (d_pl cx)) -> 0 <= d_n cx ->
  (j < length (d_body cx))%nat ->
  nth j (map (fun b : byte => bv_unsigned b) (d_body cx)) 0 =
  nth (Z.to_nat (dec_b_u (d_n cx)) + j) (map (fun b : byte => bv_unsigned b) (d_pl cx)) 0.
Proof.
intros cx j Hl Hn Hj. unfold d_body in *.
assert (Hlt : (Z.to_nat (dec_b_u (d_n cx)) + j < length (d_pl cx))%nat) by (rewrite length_skipn in Hj; lia).
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
rewrite map_nth, nth_skipn.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hlt).
rewrite map_nth. reflexivity.
Qed.

(* A step that writes no byte, as the symbolic run sees it: every region of its list read-only. *)
Lemma cp_frame_ro : forall E (rs : smem) (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hro x. apply HF. intros (r & Hr & Ha).
rewrite forallb_forall in Hro. pose proof (Hro r Hr) as Hw. apply Z.leb_le in Hw. lia.
Qed.
Lemma cp_aview_ext : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, aview segs H m' a = aview segs H m a.
Proof. intros H m m' Hm a. unfold aview, mbyte, mrestrict. rewrite Hm. reflexivity. Qed.
Lemma cp_apresent_ext : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, apresent H m a -> apresent H m' a.
Proof. intros H m m' Hm a (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite Hm. exact Hb. Qed.

(* The copy and the call windows are apart from every byte cp_base reads. *)
Lemma cp_kz_apart : forall cx ly S W regs mem md res mode nch ns a,
  AR_laws segs B -> d_n cx = Z.of_nat (length (d_pl cx)) -> 0 <= d_n cx ->
  cp_base0 cx ly S W regs mem md res mode nch ns ->
  (res <= a < res + len cx \/ d_sp1 cx - ESTACK <= a < d_sp1 cx) -> ~ cp_kz cx a.
Proof.
intros cx ly S W regs mem md res mode nch ns a LAWS Hnl Hn0 HB Ha.
pose proof (cp_core_facts cx ly S W regs mem md _ LAWS (proj1 HB)) as (Hsp0 & Hsp16 & EF & Hin & HFc & HFa).
destruct HB as (Hcore & Hbl & Hres & _).
destruct Hcore as (HJ & Hfrms & R8 & R9 & Rsp & Hsp1 & Hsp32 & R3 & R4 & Hsaved & HF4096 & HF32 & HFpres & HFL & Hpay & Hgarr).
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cp_len_facts cx Hn0 Hnl) as (L0 & U0 & LU & LB & L3).
assert (Hinr : In (res, len cx) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (_ & H4096 & Hrc & Hrapp & _).
pose proof (req_size_pos (len cx) L0) as Hrq.
assert (HSH : SHADOW_OFF <= d_SH cx /\ d_SH cx + 8 <= kHighShadowEnd).
{ unfold d_SH, shadow_addr. unfold in_app in HFa. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
pose proof (sep_block_frame segs B LAWS ly S W mem md res (len cx) DEC_FCLASS (d_fpos cx) HAR Hinr Hin) as Hsf.
rewrite EF in Hsf. change (fs_frame_bytes DEC_FCLASS) with 64 in Hsf. unfold zdisjoint in Hsf. cbn [fst snd] in Hsf.
unfold cp_kz, ESTACK in *. unfold in_app in Hrapp. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
intros Hk. destruct Ha as [Ha | Ha].
- destruct Hk as [Hk | [Hk | [Hk | [Hk | [Hk | (Hnp & Hk)]]]]]; try lia.
  pose proof (Hpay Hnp) as Hinp.
  assert (Hne : (d_p cx, d_n cx) <> (res, len cx)) by (intros Hq; injection Hq as _ Hq; lia).
  pose proof (sep_blocks segs B LAWS ly S W mem md _ _ _ _ HAR Hinp Hinr Hne) as Hsb.
  pose proof (req_size_pos (d_n cx) ltac:(lia)). unfold zdisjoint in Hsb. cbn [fst snd] in Hsb. lia.
- destruct Hk as [Hk | [Hk | [Hk | [Hk | [Hk | (Hnp & Hk)]]]]]; try lia.
  pose proof (Hpay Hnp) as Hinp.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinp) as (_ & _ & Hpc & _).
  pose proof (req_size_pos (d_n cx) ltac:(lia)). lia.
Qed.

(* The callee-saved registers but s11: what a run or a call keeps and cp_base0_kept asks. *)
Definition cp_kept_regs : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv.
Lemma cp_saved_in : forall r, acallee_saved r -> r <> 27 -> In (Z_to_bv 5 r) cp_kept_regs.
Proof.
intros r Hr Hn. unfold acallee_saved in Hr.
assert (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26) as Hc by lia.
unfold cp_kept_regs.
repeat (destruct Hc as [-> | Hc]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
subst r. repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
Section rk. Context {fx : YK11.FPState}.
Lemma cp_regs_kept : forall E ss ms regs0 extra,
  st_ok segs E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) cp_kept_regs = true ->
  forall r, acallee_saved r -> r <> 27 -> YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r).
Proof.
intros E ss ms regs0 extra HS HA Hl r Hr Hn.
exact (regs_kept_of_st_ok segs E ss ms regs0 extra cp_kept_regs HS HA Hl _ (cp_saved_in r Hr Hn)).
Qed.
End rk.

(* ------------------------------------------------------------------ *)
(* 4. The cut points between the calls                                  *)
(* ------------------------------------------------------------------ *)

(* At the entry of reac_frame_is_reac: from +0x2a4 (rk = 0x2a8, a1 = len) or from +0x30c (rk = 0x310, a1 = 0). *)
Definition cp_P_ir (rk : Z) (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (decodeb_sigma DB_reac_frame_is_reac)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    cp_inv cx ly' S' W' regs' mem' md' res mode nch ns /\
    YK11.getr regs' 1 = w64 (DEC_A_LLVMF + rk) /\
    YK11.getr regs' 10 = w64 res /\
    YK11.getr regs' 11 = w64 (if rk =? 0x2a8 then len cx else 0).

(* Back at rk with is_reac's answer in a0. *)
Definition cp_Q_ir (rk : Z) (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + rk)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    cp_inv cx ly' S' W' regs' mem' md' res mode nch ns /\
    YK11.getr regs' 10 =
      w64 (reac_frame_is_reac_c.is_reac_result res (if rk =? 0x2a8 then len cx else 0) (d_body cx)).

(* At the entry of reac_frame_clean_len (+0x31c), a0 = len. *)
Definition cp_P_cl (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (decodeb_sigma DB_reac_frame_clean_len)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    cp_inv cx ly' S' W' regs' mem' md' res mode nch ns /\
    YK11.getr regs' 1 = w64 (DEC_A_LLVMF + 0x320) /\
    YK11.getr regs' 10 = w64 (len cx).

(* Back at +0x320 with the clean length in a0. *)
Definition cp_Q_cl (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x320)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    cp_inv cx ly' S' W' regs' mem' md' res mode nch ns /\
    YK11.getr regs' 10 = w64 (reac_frame_clean_len_c.reac_frame_clean_len_model (len cx)).

(* ------------------------------------------------------------------ *)
(* 5. Stage A: +0x27c to the first call of reac_frame_is_reac           *)
(* ------------------------------------------------------------------ *)

#[local] Abbreviation PIB := (@PI_decodeb rc).
#[local] Abbreviation SEGS := (@pa_segs rc decodeb_listing PIB).
#[local] Abbreviation VAL := (@pa_val rc decodeb_listing PIB).

(* The value of register r in the machine state of a symbolic state HS (segA's reg_at). *)
Ltac cp_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?valx ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* After a run whose regions are all read-only: its memory is the old one (cp_frame_ro); the frame and growth facts
   of the run are dropped. *)
Ltac cp_fnil MEQ :=
  lazymatch goal with HF : frame_of _ ?rs ?m0 ?m1, M : forall x, ?m0 x = ?mb x |- _ =>
    let F := fresh "FN" in
    assert (F : forall x, m1 x = mb x)
      by (intros x; rewrite (cp_frame_ro _ rs m0 m1 HF ltac:(vm_compute; reflexivity) x); apply M);
    clear HF M; rename F into MEQ
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Lemma cp_stage_A : forall cx W' c',
  AR_laws segs B -> dec_crt_cells B -> cp_romctx cx ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (decodeb_sigma DB___asan_memcpy)) ->
  dec_b_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  st27c cx W' c' ->
  SRr segs W' c' (fun W2 c2 => cp_P_ir 0x2a8 cx W2 c2 \/ cp_P_ir 0x310 cx W2 c2).
Proof.
intros cx W' c' LAWS HC RC AMEMCPY HBASE H27.
pose proof HBASE as (HAFN & _ & _ & _ & Hpn & Hnl & _).
assert (Hn0 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hq _]]; lia).
destruct H27 as (fx' & ly' & S' & regs' & mem' & md' & res & mode & nch & ns & -> & Hfrm & Hcore & Hbl & Hres & Hmle
  & Hmok & Hfrs & R10 & R18 & R19 & R24 & R20 & R21 & R23 & R22 & Hmode & Hfsh & H112).
assert (HB0 : cp_base0 cx ly' S' W' regs' mem' md' res mode nch ns).
{ refine (conj Hcore (conj Hbl (conj Hres (conj Hmle (conj Hmok (conj Hfrs (conj R18 (conj R20 (conj R21 (conj R22
    (conj R23 (conj Hmode (conj _ (conj Hfsh H112)))))))))))))).
  destruct RC as (HO & HE & HR).
  exact (cp_where_of cx ly' S' W' mem' md' mode nch ns HC (proj1 (proj1 Hcore))
    (cp_rom_view_rd cx ly' S' W' mem' md' _ HO HE HR (proj1 Hcore)) Hmode). }
pose proof (cp_core_facts cx ly' S' W' regs' mem' md' _ LAWS Hcore) as (Hsp0 & Hsp16 & EF & Hin & HFc & HFa).
pose proof Hcore as (HJ & Hfrms & R8 & R9 & Rsp & Hsp1 & Hsp32 & R3 & R4 & Hsaved & HF4096 & HF32 & HFpres & HFL & Hpay
  & Hgarr).
pose proof (cp_len_facts cx ltac:(lia) Hnl) as (L0 & U0 & LU & LB & L3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hinr : In (res, len cx) (ablocks B ly' S')) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hrc : res + len cx <= alloc_ceiling).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hinr) as (_ & _ & Hc & _).
  pose proof (req_size_pos (len cx) L0). lia. }
pose proof (@paj_run fx' rc dec_B_sink_head decodeb_listing PL_decodeb PIB B LAWS) as RUN.
pose proof (@paj_branch fx' rc decodeb_listing PIB) as BR.
set (E := Eimg (PI := PIB) (Ereg regs' [])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = YK11.getr regs' r).
{ intros kk r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  unfold E. rewrite (Eimg_low (PI := PIB) (Ereg regs' []) kk ltac:(unfold A_TEXT; lia)).
  exact (ew_Ereg_nat regs' [] kk r Hk). }
assert (HAE : env_agree 32 (Ereg regs' []) E).
{ split; [|reflexivity]. intros k Hk. unfold E. rewrite (Eimg_low (PI := PIB) (Ereg regs' []) k ltac:(unfold A_TEXT; lia)).
  reflexivity. }
set (ss := mkSS 0x27c sr_atoms [] None (mkFacts [] [] [])).
assert (HS : st_ok_pi SEGS VAL E ss
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 (decodeb_val A_TEXT + 0x27c)) mem' (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss. apply (pa_entry_st_ok_full (PI := PIB)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - constructor.
  - repeat split; exact I. }
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W') mem')) by constructor.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr SEGS Wx (mkCfg (mkst regs' (Z_to_bv 64 (decodeb_val A_TEXT + 0x27c)) mem' (seg_rom SEGS)) md') Q) end.
assert (MEQ : forall x, mem' x = mem' x) by reflexivity.
paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
cp_fnil MEQ.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* len = 0: straight to +0x30c *)
  rewrite branch_eq_U, (U_atom E 20 (len cx) ltac:(rewrite (EE 20%nat 20%bv eq_refl); exact R20) ltac:(lia)),
    U_lit in Hc by lia.
  apply Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
  cp_fnil MEQ.
  rewrite wvb_collapse in HJ.
  cp_reg HS (1%bv : bv 5) (w64 (DEC_A_LLVMF + 0x310)) G1 ltac:(apply (codeptr_val (PI := PIB)); exact HEI1).
  cp_reg HS (10%bv : bv 5) (w64 res) G10
    ltac:(cbn [sv_denot]; rewrite (EE 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R10).
  cp_reg HS (11%bv : bv 5) (w64 0) G11 ltac:(reflexivity).
  cp_reg HS (27%bv : bv 5) (w64 res) G27
    ltac:(cbn [sv_denot]; rewrite (EE 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R10).
  pose proof (cp_regs_kept E _ _ regs' [] HS HAE ltac:(vm_compute; reflexivity)) as GK.
  pmkst HS.
  apply SRr_ret. right.
  exists fx', ly', S', (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md') mat0 md'), res, mode, nch, ns.
  split; [reflexivity|]. split; [exact Hfrm|].
  split; [split; [split|] |].
  + apply (cp_base0_kept cx ly' S' W' regs' mem' md' res mode nch ns W' (ms_regs ms0) (ms_mem ms0) _ (fun _ => False)
      LAWS HC RC Hnl HB0 HJ).
    * exact GK.
    * intros a _ _. apply cp_aview_ext. exact MEQ.
    * intros a. apply cp_apresent_ext. exact MEQ.
    * intros a [].
  + exact G27.
  + intros j Hj. rewrite length_map in Hj. lia.
  + split; [exact G1|]. split; [exact G10|]. exact G11.
- (* len > 0: the NULL check of the copy, then __asan_memcpy *)
  rewrite branch_eq_U, (U_atom E 20 (len cx) ltac:(rewrite (EE 20%nat 20%bv eq_refl); exact R20) ltac:(lia)),
    U_lit in Hc by lia.
  apply Z.eqb_neq in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
  cp_fnil MEQ.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. rewrite branch_eq_U, (U_atom E 10 res ltac:(rewrite (EE 10%nat 10%bv eq_refl); exact R10) ltac:(lia)),
      U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0. lia. }
  paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
  cp_fnil MEQ.
  repeat rewrite wvb_collapse in HJ.
  assert (Hn3 : 3 < d_n cx) by (unfold dec_b_len in *; lia).
  pose proof (Hpay ltac:(lia)) as Hinp.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hinp) as (_ & Hp4096 & Hpc & Hpapp & Hppres & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hinr) as (_ & Hr4096 & Hrc2 & Hrapp & Hrpres & _).
  pose proof (req_size_pos (d_n cx) ltac:(lia)) as Hrqp. pose proof (req_size_pos (len cx) ltac:(lia)) as Hrql.
  assert (Hrqe : req_size (len cx) = len cx) by (unfold req_size; destruct (Z.eqb_spec (len cx) 0); lia).
  assert (Hne : (d_p cx, d_n cx) <> (res, len cx)) by (intros Hq; injection Hq as _ Hq; lia).
  pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hinp Hinr Hne) as Hsb.
  unfold zdisjoint in Hsb. cbn [fst snd] in Hsb.
  assert (Hnew : ~ In (res, len cx) (ablocks B (d_ly cx) (d_S cx))).
  { intros Hin0. apply in_split in Hin0 as (l1 & l2 & El).
    pose proof (sep_blocks_pos segs B LAWS _ _ _ _ _ (res, len cx) (res, len cx) l1 l2 [] (proj1 HJ)) as Hd.
    rewrite Hbl, El, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia. }
  assert (Gsp0 : spZ (ms_regs ms1) = spZ regs').
  { unfold spZ. f_equal. refine (eq_trans (st_ok_restrict_reg _ _ _ _ _ (Z_to_bv 5 2) HS) _).
    change (sv_denot E (SOff 2 0) = YK11.getr regs' (Z_to_bv 5 2)).
    cbn [sv_denot]. rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  cp_reg HS (1%bv : bv 5) (Z_to_bv 64 (decodeb_val A_TEXT + 0x29c)) G1 ltac:(apply (codeptr_val (PI := PIB)); assumption).
  cp_reg HS (10%bv : bv 5) (w64 res) G10
    ltac:(cbn [sv_denot]; rewrite (EE 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R10).
  cp_reg HS (11%bv : bv 5) (w64 (d_p cx + dec_b_u (d_n cx))) G11
    ltac:(cbn [sv_denot]; rewrite (EE 24%nat 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R24).
  cp_reg HS (12%bv : bv 5) (w64 (len cx)) G12
    ltac:(cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R20).
  cp_reg HS (3%bv : bv 5) (w64 (as_gp B)) G3
    ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R3).
  cp_reg HS (4%bv : bv 5) (w64 (as_tp B)) G4
    ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R4).
  pmkst HS.
  eapply SRr_bind.
  { eapply (aj_intrin_atS (SK := dec_B_sink_head) segs B LAWS decodeb_segs_low OCpy (decodeb_sigma DB___asan_memcpy)
      (AMEMCPY fx') W' (ms_regs ms1) (ms_mem ms1) DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
      (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' _ dec_ev_27c res (d_p cx + dec_b_u (d_n cx)) (len cx)
      (d_sp1 cx - d_sp0 cx) (Z_to_bv 64 (decodeb_val A_TEXT + 0x29c)) HJ G10 G11 G12).
    - lia.
    - lia.
    - lia.
    - rewrite Gsp0, Rsp. lia.
    - lia.
    - lia.
    - unfold ESTACK, DEC_LLVMF_STK. lia.
    - exact G3.
    - exact G4.
    - exact G1.
    - apply (ret_ok_codeptr_v (PI := PIB)); [lia | reflexivity].
    - intros a Ha. split; [right; right; left; exists res, (len cx); split; [exact Hinr|]; split; [exact Hnew | lia]|].
      unfold ESTACK. lia.
    - eapply (amem_range_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hinr); lia.
    - eapply (range_addressable_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hinr); lia.
    - intros Hl0. eapply (shadow_hull_vis_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hinr); lia.
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split; [apply (aview_some_of_apresent segs); exact (proj1 (Hppres a ltac:(lia)))|].
        rewrite Gsp0, Rsp. unfold ESTACK. lia. }
      split; [lia|].
      split; [eapply (amem_range_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hinp); lia|].
      split; [eapply (range_addressable_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hinp); lia|].
      intros Hl0. eapply (shadow_hull_vis_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hinp); lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hd2 & Heff & Hkeep & Hpres2 & Hsbm).
  pose proof (cp_regs_kept E _ _ regs' [] HS HAE ltac:(vm_compute; reflexivity)) as GK1.
  jafter_call_keep_pi HS 200%nat regs2 (mrestrict (w_H W') mem2) HP2 (@nil nat) HS2.
  specialize (HS2 (Forall_nil _)). rewrite <- restrict_mkst_fx in HS2.
  set (E2 := havoc E 200 (map (getr regs2) CLOB)) in HS2.
  assert (HEIc : img_env VAL A_LIM E2) by (apply (img_env_havoc (PI := PIB)); [assumption | cbv; lia]).
  assert (EE2 : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E2 k = YK11.getr regs' r).
  { intros kk r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
    unfold E2. rewrite ew_havoc_old by lia. exact (EE kk r Hk). }
  assert (HAE2 : env_agree 32 (Ereg regs' []) E2).
  { split; [|reflexivity]. intros k Hk. unfold E2. rewrite ew_havoc_old by lia. exact (proj1 HAE k Hk). }
  assert (SHOK2 : sh_ok SEGS (SOff 18 0) [] E2 (mrestrict (w_H W') mem2)) by constructor.
  clear SHOK.
  lazymatch goal with |- SRr _ ?Wx (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
    change (SRr SEGS Wx (mkCfg (mkst rg (Z_to_bv 64 (decodeb_val A_TEXT + 0x29c)) mm (seg_rom SEGS)) mdx) Q) end.
  assert (MEQ2 : forall x, mem2 x = mem2 x) by reflexivity.
  paj_run_tok RUN HS2 HJ2 SHOK2 Bspan; [apply awr_ok_nil |].
  cp_fnil MEQ2.
  repeat rewrite wvb_collapse in HJ2.
  cp_reg HS2 (1%bv : bv 5) (w64 (DEC_A_LLVMF + 0x2a8)) G1' ltac:(apply (codeptr_val (PI := PIB)); assumption).
  cp_reg HS2 (10%bv : bv 5) (w64 res) G10'
    ltac:(cbn [sv_denot]; rewrite (EE2 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R10).
  cp_reg HS2 (11%bv : bv 5) (w64 (len cx)) G11'
    ltac:(cbn [sv_denot]; rewrite (EE2 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R20).
  cp_reg HS2 (27%bv : bv 5) (w64 res) G27'
    ltac:(cbn [sv_denot]; rewrite (EE2 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R10).
  pose proof (cp_regs_kept E2 _ _ regs' [] HS2 HAE2 ltac:(vm_compute; reflexivity)) as GK.
  pmkst HS2.
  apply SRr_ret. left.
  lazymatch goal with |- context [mkCfg (mkst ?rgf _ ?mmf _) ?mdf] =>
    exists fx', ly', S', rgf, mmf, mdf, res, mode, nch, ns end.
  split; [reflexivity|]. split; [exact Hfrm|].
  split; [split; [split|] |].
  + apply (cp_base0_kept cx ly' S' W' regs' mem' md' res mode nch ns W' _ _ _
      (fun a => res <= a < res + len cx \/ d_sp1 cx - ESTACK <= a < d_sp1 cx) LAWS HC RC Hnl HB0 HJ2).
    * exact GK.
    * intros a Ha HnZ. rewrite (cp_aview_ext _ _ _ MEQ2 a).
      rewrite (Hkeep a Ha ltac:(intros Hq; apply HnZ; left; exact Hq) ltac:(intros Hq; apply HnZ; right; lia)).
      exact (cp_aview_ext _ _ _ MEQ a).
    * intros a Hpa. apply (cp_apresent_ext _ _ _ MEQ2). apply Hpres2.
      apply (cp_apresent_ext (w_H W') mem' (ms_mem ms1)); [exact MEQ | exact Hpa].
    * intros a Ha. exact (cp_kz_apart cx ly' S' W' regs' mem' md' res mode nch ns a LAWS Hnl ltac:(lia) HB0 Ha).
  + exact G27'.
  + intros j Hj. rewrite length_map in Hj.
    rewrite (cp_body_nth cx j Hnl ltac:(lia) Hj).
    assert (Hj2 : (Z.to_nat (dec_b_u (d_n cx)) + j < length (map (fun b : byte => bv_unsigned b) (d_pl cx)))%nat)
      by (rewrite length_map; lia).
    destruct (Hgarr _ Hj2) as [Hv Hr8]. split; [|exact Hr8].
    apply (cp_val_mem_moved segs (w_H W') (w_H W') mem' _ (d_p cx + Z.of_nat (Z.to_nat (dec_b_u (d_n cx)) + j))
      (res + Z.of_nat j) 1); [|exact Hv].
    intros k Hk. cbn in Hk. assert (k = 0) as -> by lia. rewrite !Z.add_0_r.
    rewrite (cp_aview_ext _ _ _ MEQ2).
    replace (res + Z.of_nat j) with (res + Z.of_nat j) by reflexivity.
    rewrite (Heff (Z.of_nat j) ltac:(lia)).
    rewrite (cp_aview_ext _ _ _ MEQ). f_equal. lia.
  + split; [exact G1'|]. split; [exact G10'|]. exact G11'.
Qed.

(* ------------------------------------------------------------------ *)
(* 6. Stage C: is_reac's answer checked (+0x2a8 / +0x310 .. +0x31c)     *)
(* ------------------------------------------------------------------ *)

(* ReadName.v's rn_env: after a run the environment grows above slot 511; AG says the slots below are the seat's. *)
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

(* The facts every seat of this segment states: s2 is the shadow base, s11 the copy (a heap address). *)
Definition cp_facts : facts := mkFacts [(18%nat, mkAF SB SB 0); (27%nat, mkAF 4096 0x7fffff800000 0)] [] [].
Definition cp_ss (pc : Z) (rs : smem) : sstate := mkSS pc sr_atoms rs None cp_facts.

Lemma cp_seat : forall (fx' : YK11.FPState) (W : world segs) regs mem extra pc res,
  YK11.getr regs 18 = w64 SHADOW_OFF -> YK11.getr regs 27 = w64 res -> 4096 <= res <= 0x7fffff800000 ->
  st_ok_pi SEGS VAL (Eimg (PI := PIB) (Ereg regs extra)) (cp_ss pc [])
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (decodeb_val A_TEXT + pc)) mem (seg_rom SEGS))).
Proof.
intros fx' W regs mem extra pc res R18 R27 Hr.
rewrite restrict_mkst_fx. unfold cp_ss. apply (pa_entry_st_ok_full (PI := PIB)).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- constructor.
- split; [|split; [exact I | exact I]].
  cbn [cp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (ew_Eimg_Ereg_natB regs extra 18 18%bv eq_refl), (ew_Eimg_Ereg_natB regs extra 27 27%bv eq_refl), R18, R27.
  unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF. repeat split; lia.
Qed.

Lemma cp_isreac_small : forall f l bs, l < 14 -> reac_frame_is_reac_c.is_reac_result f l bs = 0.
Proof.
intros f l bs Hl. unfold reac_frame_is_reac_c.is_reac_result.
replace (l <? 14) with true by (symmetry; apply Z.ltb_lt; exact Hl). rewrite orb_true_r. reflexivity.
Qed.

(* The close of stage C at the call of reac_frame_clean_len: a0 = s4 = len, ra = +0x320, and cp_inv kept (the
   stage writes no byte and keeps every callee-saved register). *)
Ltac cp_close_cl cx res HS HJ MEQ AG EE HAE R20 R27 Hfrm HB0 Hgr LAWS HC RC Hnl :=
  let G1 := fresh "G1" in let G10 := fresh "G10" in let G27 := fresh "G27" in let GK := fresh "GK" in
  repeat rewrite wvb_collapse in HJ;
  cp_reg HS (1%bv : bv 5) (w64 (DEC_A_LLVMF + 0x320)) G1 ltac:(apply (codeptr_val (PI := PIB)); assumption);
  cp_reg HS (10%bv : bv 5) (w64 (len cx)) G10
    ltac:(cbn [sv_denot]; try rewrite (AG 20%nat ltac:(lia)); rewrite (EE 20%nat 20%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact R20);
  cp_reg HS (27%bv : bv 5) (w64 res) G27
    ltac:(cbn [sv_denot]; try rewrite (AG 27%nat ltac:(lia)); rewrite (EE 27%nat 27%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact R27);
  let HAEx := fresh "HAEx" in
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (HAEx : env_agree 32 (Ereg _ _) Ex)
      by (split; [intros k Hk; try rewrite (AG k ltac:(lia)); exact (proj1 HAE k Hk)
                 | cbn [ed ewset]; exact (proj2 HAE)]) end;
  pose proof (cp_regs_kept _ _ _ _ _ HS HAEx ltac:(vm_compute; reflexivity)) as GK;
  pmkst HS;
  apply SRr_ret;
  lazymatch goal with |- context [mkCfg (mkst ?rgf _ ?mmf _) ?mdf] =>
    do 3 eexists; exists rgf, mmf, mdf; do 4 eexists end;
  split; [reflexivity|]; split; [exact Hfrm|];
  split; [split; [split|] |];
  [ apply (cp_base0_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => False) LAWS HC RC Hnl HB0 HJ);
    [ exact GK
    | intros a _ _; apply cp_aview_ext; exact MEQ
    | intros a; apply cp_apresent_ext; exact MEQ
    | intros a [] ]
  | exact G27
  | apply (cp_garr8_kept segs _ _ _ _ _ _ (fun j _ => cp_aview_ext _ _ _ MEQ _) Hgr)
  | split; [exact G1 | exact G10] ].

Lemma cp_stage_C1 : forall cx W' c',
  AR_laws segs B -> dec_crt_cells B -> cp_romctx cx ->
  dec_b_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  cp_Q_ir 0x310 cx W' c' -> SRr segs W' c' (cp_P_cl cx).
Proof.
intros cx W' c' LAWS HC RC HBASE HQ.
pose proof HBASE as (HAFN & _ & _ & _ & Hpn & Hnl & _).
assert (Hn0 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hq _]]; lia).
destruct HQ as (fx' & ly' & S' & regs' & mem' & md' & res & mode & nch & ns & -> & Hfrm & ((HB0 & R27) & Hgr) & R10).
pose proof HB0 as (Hcore & Hbl & Hres & Hmle & Hmok & Hfrs & R18 & R20 & R21 & R22 & R23 & Hmode & Hwhere & Hfsh & H112).
pose proof Hcore as (HJ & _).
pose proof (cp_len_facts cx ltac:(lia) Hnl) as (L0 & U0 & LU & LB & L3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hinr : In (res, len cx) (ablocks B ly' S')) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hrc : res + len cx <= alloc_ceiling).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hinr) as (_ & _ & Hc & _).
  pose proof (req_size_pos (len cx) L0). lia. }
pose proof (@paj_run fx' rc dec_B_sink_head decodeb_listing PL_decodeb PIB B LAWS) as RUN.
pose proof (@paj_branch fx' rc decodeb_listing PIB) as BR.
set (E := Eimg (PI := PIB) (Ereg regs' [])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = YK11.getr regs' r).
{ intros kk r Hk. unfold E. apply ew_Eimg_Ereg_natB. exact Hk. }
assert (HAE : env_agree 32 (Ereg regs' []) E).
{ split; [|reflexivity]. intros k Hk. unfold E. rewrite (Eimg_low (PI := PIB) (Ereg regs' []) k ltac:(unfold A_TEXT; lia)).
  reflexivity. }
pose proof (cp_seat fx' W' regs' mem' [] 0x310 res R18 R27 ltac:(lia)) as HS. fold E in HS.
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W') mem')) by constructor.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr SEGS Wx (mkCfg (mkst regs' (Z_to_bv 64 (decodeb_val A_TEXT + 0x310)) mem' (seg_rom SEGS)) md') Q) end.
assert (MEQ : forall x, mem' x = mem' x) by reflexivity.
paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
cp_fnil MEQ.
assert (AG : forall n, (n < 512)%nat -> ew E n = ew E n) by reflexivity.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ne_U, U_lit in Hc by lia.
  assert (R10' : YK11.getr regs' 10 = w64 0) by (rewrite R10; f_equal; apply cp_isreac_small; cbn; lia).
  rewrite (U_atom E 10 0) in Hc by (first [rewrite (EE 10%nat 10%bv eq_refl); exact R10' | lia]).
  cbn in Hc. discriminate. }
paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
cp_fnil MEQ.
cp_env HS AG.
cp_close_cl cx res HS HJ MEQ AG EE HAE R20 R27 Hfrm HB0 Hgr LAWS HC RC Hnl.
Qed.

(* The two header bytes is_reac reads, and the read-only region of the copy that holds them (+0x2d0, +0x2f8). *)
Definition cp_b12 (cx : dctx) : Z := reac_frame_is_reac_c.is_reac_byte (d_body cx) 12.
Definition cp_b13 (cx : dctx) : Z := reac_frame_is_reac_c.is_reac_byte (d_body cx) 13.
Definition cp_hdr_region : YP09.region :=
  YP09.mkRegion (Some 27%nat) 12 14 0 0 [YP09.mkChunk 12 (CVal 1 (SOff 32 0)); YP09.mkChunk 13 (CVal 1 (SOff 33 0))].
Lemma cp_body_byte : forall cx (i : nat), (i < length (d_body cx))%nat ->
  nth i (map (fun b : byte => bv_unsigned b) (d_body cx)) 0 = reac_frame_is_reac_c.is_reac_byte (d_body cx) i.
Proof.
intros cx i Hi. unfold reac_frame_is_reac_c.is_reac_byte.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hi).
apply map_nth.
Qed.

Lemma cp_isreac_val : forall f l bs, f <> 0 -> 14 <= l ->
  reac_frame_is_reac_c.is_reac_result f l bs =
  if (reac_frame_is_reac_c.is_reac_byte bs 12 =? 0x88) && (reac_frame_is_reac_c.is_reac_byte bs 13 =? 0x19) then 1 else 0.
Proof.
intros f l bs Hf Hl. unfold reac_frame_is_reac_c.is_reac_result.
replace (f =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hf).
replace (l <? 14) with false by (symmetry; apply Z.ltb_ge; exact Hl). reflexivity.
Qed.

(* `addi a1, a1, -0x19; seqz a1, a1` at +0x2fc / +0x300 on a byte. *)
Lemma cp_seqz25 : forall E x b, U E x = b -> 0 <= b < 256 ->
  U E (SAlu ALU_SLTU (SAlu ALU_ADD x (SLit (-25))) (SLit 1)) = if b =? 25 then 1 else 0.
Proof.
intros E x b Hx Hb. rewrite !U_SAlu, !U_SLit, Hx. cbn [zalu_raw]. unfold zcanon, M64.
destruct (Z.eqb_spec b 25) as [-> | Hne]; [reflexivity|].
change ((-25) mod 2 ^ 64) with 18446744073709551591. change (1 mod 2 ^ 64) with 1.
replace ((b + 18446744073709551591) mod 2 ^ 64 <? 1) with false; [reflexivity|].
symmetry. apply Z.ltb_ge. pose proof (Z.mod_pos_bound (b + 18446744073709551591) (2 ^ 64) ltac:(lia)). lia.
Qed.

Lemma cp_stage_C2 : forall cx W' c',
  AR_laws segs B -> dec_crt_cells B -> cp_romctx cx ->
  dec_b_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  cp_Q_ir 0x2a8 cx W' c' -> SRr segs W' c' (cp_P_cl cx).
Proof.
intros cx W' c' LAWS HC RC HBASE HQ.
pose proof HBASE as (HAFN & _ & _ & _ & Hpn & Hnl & _).
assert (Hn0 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hq _]]; lia).
destruct HQ as (fx' & ly' & S' & regs' & mem' & md' & res & mode & nch & ns & -> & Hfrm & ((HB0 & R27) & Hgr) & R10).
pose proof HB0 as (Hcore & Hbl & Hres & Hmle & Hmok & Hfrs & R18 & R20 & R21 & R22 & R23 & Hmode & Hwhere & Hfsh & H112).
pose proof Hcore as (HJ & _).
pose proof (cp_len_facts cx ltac:(lia) Hnl) as (L0 & U0 & LU & LB & L3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hinr : In (res, len cx) (ablocks B ly' S')) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hrc : res + len cx <= alloc_ceiling).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hinr) as (_ & _ & Hc & _).
  pose proof (req_size_pos (len cx) L0). lia. }
cbn [Z.eqb Pos.eqb] in R10.
pose proof (@paj_run fx' rc dec_B_sink_head decodeb_listing PL_decodeb PIB B LAWS) as RUN.
pose proof (@paj_branch fx' rc decodeb_listing PIB) as BR.
set (E := Eimg (PI := PIB) (Ereg regs' [Z_to_bv 64 (cp_b12 cx); Z_to_bv 64 (cp_b13 cx)])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = YK11.getr regs' r).
{ intros kk r Hk. unfold E. apply ew_Eimg_Ereg_natB. exact Hk. }
assert (E32 : ew E 32 = Z_to_bv 64 (cp_b12 cx))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (cp_b13 cx))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 1)).
assert (HAE : env_agree 32 (Ereg regs' [Z_to_bv 64 (cp_b12 cx); Z_to_bv 64 (cp_b13 cx)]) E).
{ split; [|reflexivity]. intros k Hk. unfold E. rewrite (Eimg_low (PI := PIB) _ k ltac:(unfold A_TEXT; lia)).
  reflexivity. }
pose proof (cp_seat fx' W' regs' mem' [Z_to_bv 64 (cp_b12 cx); Z_to_bv 64 (cp_b13 cx)] 0x2a8 res R18 R27 ltac:(lia))
  as HS. fold E in HS.
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W') mem')) by constructor.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr SEGS Wx (mkCfg (mkst regs' (Z_to_bv 64 (decodeb_val A_TEXT + 0x2a8)) mem' (seg_rom SEGS)) md') Q) end.
assert (MEQ : forall x, mem' x = mem' x) by reflexivity.
assert (AG : forall n, (n < 512)%nat -> ew E n = ew E n) by reflexivity.
paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
cp_fnil MEQ.
assert (UL : U E (SOff 20 0) = len cx) by (apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl); exact R20 | lia]).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* len < 14: to +0x310 *)
  rewrite branch_ltu_U, UL, U_lit in Hc by lia. apply Z.ltb_lt in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
  cp_fnil MEQ.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. rewrite branch_ne_U, U_lit in Hc0 by lia.
    assert (R10' : YK11.getr regs' 10 = w64 0) by (rewrite R10; f_equal; apply cp_isreac_small; lia).
    rewrite (U_atom E 10 0) in Hc0 by (first [rewrite (EE 10%nat 10%bv eq_refl); exact R10' | lia]).
    cbn in Hc0. discriminate. }
  paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil |].
  cp_fnil MEQ.
  cp_env HS AG.
  cp_close_cl cx res HS HJ MEQ AG EE HAE R20 R27 Hfrm HB0 Hgr LAWS HC RC Hnl.
- (* 14 <= len: the two header bytes are in the copy *)
  rewrite branch_ltu_U, UL, U_lit in Hc by lia. apply Z.ltb_ge in Hc.
  assert (Ub : bv_unsigned (ew E 27) = res).
  { rewrite (EE 27%nat 27%bv eq_refl), R27. apply unsigned_lit_small. lia. }
  assert (B12 : 0 <= cp_b12 cx < 256 /\ 0 <= cp_b13 cx < 256).
  { unfold cp_b12, cp_b13, reac_frame_is_reac_c.is_reac_byte.
    pose proof (bv_unsigned_in_range 8 (nth 12 (d_body cx) (Z_to_bv 8 0))) as Q1.
    pose proof (bv_unsigned_in_range 8 (nth 13 (d_body cx) (Z_to_bv 8 0))) as Q2.
    change (bv_modulus 8) with 256 in Q1, Q2. lia. }
  assert (HR : region_ok SEGS E (ms_mem (restrict (w_H W') ms)) cp_hdr_region).
  { unfold cp_hdr_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val restrict ms_mem].
    rewrite Ub. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    assert (VB : forall (i : nat), (i < length (d_body cx))%nat ->
      val_mem segs (rd W' (ms_mem ms)) (res + Z.of_nat i) 1 (reac_frame_is_reac_c.is_reac_byte (d_body cx) i)).
    { intros i Hi. rewrite <- (cp_body_byte cx i Hi).
      apply (val_mem_kept segs (w_H W') (w_H W') mem' (ms_mem ms)); [intros k Hk; apply cp_aview_ext; exact MEQ|].
      apply (proj1 (Hgr i ltac:(rewrite length_map; exact Hi))). }
    constructor; [|constructor; [|constructor]].
    - apply (chunk_ok_val SEGS E _ res 12 1 (SOff 32 0) (cp_b12 cx));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact (VB 12%nat ltac:(lia)).
    - apply (chunk_ok_val SEGS E _ res 13 1 (SOff 33 0) (cp_b13 cx));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact (VB 13%nat ltac:(lia)). }
  lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict (w_H W') ms) |- _ =>
    pose proof (st_ok_pi_add_region (PI := PIB) E ssx _ cp_hdr_region HS eq_refl HR ltac:(cbn; exact I)) as HS1 end.
  clear HS. rename HS1 into HS.
  assert (U18 : U E (SOff 18 0) = SHADOW_OFF)
    by (apply U_atom; [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | unfold SHADOW_OFF; lia]).
  assert (OB : forall c, 0 <= c -> c < len cx ->
    range_addressable (rd_of SEGS (rd W' (ms_mem ms))) (U E (SOff 18 0)) (U E (SOff 27 c)) 1).
  { intros c Hc0 Hc1. rewrite U18, (U_atom_off E 27 res c) by (first [rewrite (EE 27%nat 27%bv eq_refl); exact R27 | lia]).
    change (rd_of SEGS (rd W' (ms_mem ms))) with (aview segs (w_H W') (ms_mem ms)).
    eapply (range_addressable_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hinr); try lia.
    pose proof (req_size_pos (len cx) L0). lia. }
  paj_run_tok RUN HS HJ SHOK Bspan;
    [ apply OB; lia
    | lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
        let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
      apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]
    | ].
  cp_fnil MEQ.
  cp_env HS AG.
  assert (RV : reac_frame_is_reac_c.is_reac_result res (len cx) (d_body cx) =
    if (cp_b12 cx =? 0x88) && (cp_b13 cx =? 0x19) then 1 else 0) by (apply cp_isreac_val; lia).
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (U12 : U Ex (SExt false 8 (SOff 32 0)) = cp_b12 cx);
    [ rewrite U_zext, (U_atom Ex 32 (cp_b12 cx)) by (first [rewrite (AG 32%nat ltac:(lia)); exact E32 | lia]);
      change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia
    | ] end.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* frame[12] <> 0x88: to +0x310 *)
    rewrite branch_ne_U, U12, U_lit in Hc0 by lia. apply negb_true_iff, Z.eqb_neq in Hc0.
    paj_run_tok RUN HS HJ SHOK Bspan;
      [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
          let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
        apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]
      | ].
    cp_fnil MEQ.
    cp_env HS AG.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    { exfalso. rewrite branch_ne_U, U_lit in Hc1 by lia.
      assert (R10' : YK11.getr regs' 10 = w64 0).
      { rewrite R10, RV. f_equal. replace (cp_b12 cx =? 136) with false by (symmetry; apply Z.eqb_neq; exact Hc0).
        reflexivity. }
      lazymatch type of Hc1 with context [U ?Ex (SOff 10 0)] =>
        rewrite (U_atom Ex 10 0) in Hc1 by (first [rewrite (AG 10%nat ltac:(lia)), (EE 10%nat 10%bv eq_refl); exact R10' | lia])
      end.
      cbn in Hc1. discriminate. }
    paj_run_tok RUN HS HJ SHOK Bspan;
      [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
          let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
        apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]
      | ].
    cp_fnil MEQ.
    cp_env HS AG.
    cp_close_cl cx res HS HJ MEQ AG EE HAE R20 R27 Hfrm HB0 Hgr LAWS HC RC Hnl.
  + (* frame[12] = 0x88 *)
    rewrite branch_ne_U, U12, U_lit in Hc0 by lia. apply negb_false_iff, Z.eqb_eq in Hc0.
    paj_run_tok RUN HS HJ SHOK Bspan;
      [ lazymatch goal with |- range_addressable (rd_of SEGS (rd W' ?m)) (U ?Ex (SOff 18 0)) (U ?Ex (SOff 27 ?c)) 1 =>
          rewrite (U_atom Ex 18 SHADOW_OFF)
            by (first [rewrite (AG 18%nat ltac:(lia)), (EE 18%nat 18%bv eq_refl); exact R18 | unfold SHADOW_OFF; lia]);
          rewrite (U_atom_off Ex 27 res c)
            by (first [rewrite (AG 27%nat ltac:(lia)), (EE 27%nat 27%bv eq_refl); exact R27 | lia]);
          change (rd_of SEGS (rd W' m)) with (aview segs (w_H W') m);
          eapply (range_addressable_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hinr); try lia;
          pose proof (req_size_pos (len cx) L0); lia end
      | lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
          let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
        apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]
      | ].
    cp_fnil MEQ.
    cp_env HS AG.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    { exfalso. rewrite branch_ne_U in Hc1.
      lazymatch type of Hc1 with context [U ?Ex (SOff 10 0)] =>
        assert (U13 : U Ex (SExt false 8 (SOff 33 0)) = cp_b13 cx);
        [ rewrite U_zext, (U_atom Ex 33 (cp_b13 cx)) by (first [rewrite (AG 33%nat ltac:(lia)); exact E33 | lia]);
          change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia
        | ];
        rewrite (cp_seqz25 Ex _ (cp_b13 cx) U13 ltac:(lia)) in Hc1;
        rewrite (U_atom Ex 10 (if cp_b13 cx =? 25 then 1 else 0)) in Hc1
          by (first [rewrite (AG 10%nat ltac:(lia)), (EE 10%nat 10%bv eq_refl), R10, RV, Hc0; reflexivity
                    | destruct (cp_b13 cx =? 25); lia])
      end.
      rewrite Z.eqb_refl in Hc1. discriminate. }
    paj_run_tok RUN HS HJ SHOK Bspan;
      [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
          let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
        apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]
      | ].
    cp_fnil MEQ.
    cp_env HS AG.
    cp_close_cl cx res HS HJ MEQ AG EE HAE R20 R27 Hfrm HB0 Hgr LAWS HC RC Hnl.
Qed.

(* ------------------------------------------------------------------ *)
(* 7. Stage D1: +0x320 .. +0x3a0, the clean-length checks                *)
(* ------------------------------------------------------------------ *)

(* The shadow rows of the three tables (dec_crt_cells rows 21-26): granule 0 is in an as_zero_shadow range of B,
   granule 1 is a constant cell of value 4. *)
Lemma cp_tbl_shadow_rows : forall ly, dec_crt_cells B ->
  (dec_tab_zshadow_at B 0x20d60 /\ In (z1 (ANum (AsanCells.shadow_addr 0x20d68)) 4) (as_const B ly)) /\
  (dec_tab_zshadow_at B 0x20da0 /\ In (z1 (ANum (AsanCells.shadow_addr 0x20da8)) 4) (as_const B ly)) /\
  (dec_tab_zshadow_at B 0x20d80 /\ In (z1 (ANum (AsanCells.shadow_addr 0x20d88)) 4) (as_const B ly)).
Proof.
intros ly HC. destruct (HC ly) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & S0 & S1 & S2 & S3 & S4 & S5 & _).
exact (conj (conj S0 S1) (conj (conj S2 S3) (conj S4 S5))).
Qed.

Lemma cp_tbl_addr : forall t x (r : reader), t mod 8 = 0 ->
  r (AsanCells.shadow_addr t) = Some 0 -> r (AsanCells.shadow_addr (t + 8)) = Some 4 -> t + 4 <= x < t + 4 + 8 ->
  exists s, r (SHADOW_OFF + x / 8) = Some s /\ saddr_ok x s.
Proof.
intros t x r H8 R0 R4 Hx. unfold AsanCells.shadow_addr, AsanCells.ASAN_K in *. destruct (Z.lt_ge_cases x (t + 8)) as [Hl | Hg].
- exists 0. split; [replace (SHADOW_OFF + x / 8) with (t / 8 + 2147450880) by (unfold SHADOW_OFF; lia); exact R0 | left; reflexivity].
- exists 4. split; [replace (SHADOW_OFF + x / 8) with ((t + 8) / 8 + 2147450880) by (unfold SHADOW_OFF; lia); exact R4
  | right; lia].
Qed.

(* The two mode fields are addressable (their shadow, read at +0x3a0 / +0x3b0, refutes the two load4 reports):
   the local's two shadow bytes are 0 and 4 (dec_b_fsh); a table's granule 0 reads 0 through AR's as_zero_shadow
   (dec_tab_zshadow_rd) and its granule 1 is a constant cell of value 4 (dec_crt_cells). *)
Lemma cp_mode_addr : forall cx ly S W regs mem md res mode nch ns,
  AR_laws segs B -> dec_crt_cells B -> cp_base0 cx ly S W regs mem md res mode nch ns ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (mode + 4) 8.
Proof.
intros cx ly S W regs mem md res mode nch ns LAWS HC HB.
pose proof (cp_core_facts cx ly S W regs mem md _ LAWS (proj1 HB)) as (Hsp0 & Hsp16 & EF & Hin & HFc & HFa).
destruct HB as (Hcore & Hbl & Hres & Hmle & Hmok & Hfrs & R18 & R20 & R21 & R22 & R23 & Hmode & Hwhere & Hfsh & H112).
destruct Hcore as (HJ & Hfrms & R8 & R9 & Rsp & Hsp1 & Hsp32 & R3 & R4 & Hsaved & HF4096 & HF32 & HFpres & HFL & Hpay & Hgarr).
pose proof (proj1 HJ) as HAR.
intros x Hx. unfold shadow_of_addr.
destruct Hwhere as [-> | (Hin_t & _ & _)].
- destruct Hfsh as (_ & L4 & L5 & _). unfold d_SH, shadow_addr in L4, L5.
  assert (Hq : (d_F cx + 32 + 4 <= x < d_F cx + 40 /\ x / 8 = d_F cx / 8 + 4) \/
               (d_F cx + 40 <= x < d_F cx + 44 /\ x / 8 = d_F cx / 8 + 5)) by lia.
  destruct Hq as [(Hr & ->) | (Hr & ->)].
  + exists 0. split; [rewrite Z.add_assoc; exact L4 | left; reflexivity].
  + exists 4. split; [rewrite Z.add_assoc; exact L5 | right; lia].
- assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (R1 : forall a v, In (z1 (ANum a) v) (as_const B ly) -> aview segs (w_H W) mem a = Some (le_byte v 1 0)).
  { intros a v Hr. pose proof (CH _ Hr) as H1. unfold cell_holds in H1. cbn [c_at c_val c_w z1 c1 aeval] in H1.
    pose proof (H1 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. exact H0. }
  destruct (cp_tbl_shadow_rows ly HC) as ((T0 & T1) & (T2 & T3) & (T4 & T5)).
  unfold cp_tbl in Hin_t. cbn in Hin_t.
  destruct Hin_t as [<- | [<- | [<- | []]]].
  + pose proof (dec_tab_zshadow_rd B ly S W mem md 0x20d60 HAR eq_refl T0) as Q0. pose proof (R1 _ _ T1) as Q1.
    change (le_byte 4 1 0) with 4 in Q1. exact (cp_tbl_addr 0x20d60 x _ eq_refl Q0 Q1 Hx).
  + pose proof (dec_tab_zshadow_rd B ly S W mem md 0x20da0 HAR eq_refl T2) as Q0. pose proof (R1 _ _ T3) as Q1.
    change (le_byte 4 1 0) with 4 in Q1. exact (cp_tbl_addr 0x20da0 x _ eq_refl Q0 Q1 Hx).
  + pose proof (dec_tab_zshadow_rd B ly S W mem md 0x20d80 HAR eq_refl T4) as Q0. pose proof (R1 _ _ T5) as Q1.
    change (le_byte 4 1 0) with 4 in Q1. exact (cp_tbl_addr 0x20d80 x _ eq_refl Q0 Q1 Hx).
Qed.

Definition CP_KM : Z := 0x8e38e38e38e38e39.
Definition CP_T36 : Z := 0x071c71c71c71c71c.
Definition cp_r_km : YP09.region := YP09.mkRegion (Some (A_OBJ 7)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit CP_KM))].
Definition cp_r_t36 : YP09.region := YP09.mkRegion (Some (A_OBJ 8)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit CP_T36))].
(* Stage D2's seat at +0x3a0: the mode's two fields (read at +0x3bc / +0x3c4) and the spill slots 32 .. 80 of s1
   (written at +0x3d4 .. +0x3f0). *)
Definition cp_r_nch : YP09.region := YP09.mkRegion (Some 23%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition cp_r_ns : YP09.region := YP09.mkRegion (Some 22%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition cp_r_stk : YP09.region := YP09.mkRegion (Some 9%nat) 32 80 32 80 [].
Definition cp_regsD : smem := [cp_r_nch; cp_r_ns; cp_r_stk].
Definition cp_factsD : facts :=
  mkFacts [(18%nat, mkAF SB SB 0); (27%nat, mkAF 4096 0x7fffff800000 0); (22%nat, mkAF 4096 0x7fffff800000 0);
           (23%nat, mkAF 4096 0x7fffff800000 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition cp_ssD : sstate := mkSS 0x3a0 sr_atoms cp_regsD None cp_factsD.
Lemma cp_rom_km : rdword (fun x => option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 x))) 0x10310
  = Some CP_KM.
Proof. vm_compute. reflexivity. Qed.
Lemma cp_rom_t36 : rdword (fun x => option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 x))) 0x10360
  = Some CP_T36.
Proof. vm_compute. reflexivity. Qed.
Lemma cp_obj_vals : decodeb_val (A_OBJ 7) = 0x10310 /\ decodeb_val (A_OBJ 8) = 0x10360.
Proof. vm_compute. split; reflexivity. Qed.
Lemma cp_ro_img : forall a, (0x10310 <= a < 0x10318 \/ 0x10360 <= a < 0x10368) -> in_img segs a.
Proof.
intros a Ha. assert (Hr : dec_in_ro_rd a).
{ destruct Ha as [Ha | Ha].
  - replace a with (0x10310 + (a - 0x10310)) by lia. apply (cp_in_ro_rd _ 8); [cbn; auto | lia].
  - replace a with (0x10360 + (a - 0x10360)) by lia. apply (cp_in_ro_rd _ 8); [cbn; auto 10 | lia]. }
destruct (dec_ro_rd_rom_clean a Hr) as [(sg & Hin & _ & Hb) _]. exists sg. split; [exact Hin | lia].
Qed.

(* The write rights of stage D's regions: the read-only ones, and the spill area [s1 + 32, s1 + 80) in the caller's
   stack window (the environment may have grown above slot 511 since the seat). *)
Ltac cp_awr_ro :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac cp_awrD cx Ub9 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]);
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (d_sp1 cx - d_sp0 cx));
  [ reflexivity | repeat rewrite ew_ewset_other by lia; try rewrite Ub9; lia | cbn; try unfold DEC_LLVMF_STK; lia
  | cbn; lia | apply awr_ok_nil ].

(* At +0x3a0, after the clean-length checks: the invariant, nothing else. *)
Definition cp_R3a0 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x3a0)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    cp_inv cx ly' S' W' regs' mem' md' res mode nch ns.

Lemma cp_clean_cases : forall l, 0 <= l ->
  (reac_frame_clean_len_c.reac_frame_clean_len_model l = l /\ ~ (54 <= l /\ (l - 54) mod 36 = 0)) \/
  (reac_frame_clean_len_c.reac_frame_clean_len_model l = l - 2 /\ 54 <= l /\ (l - 54) mod 36 = 0).
Proof.
intros l Hl. unfold reac_frame_clean_len_c.reac_frame_clean_len_model.
destruct (54 <=? l) eqn:E1; destruct ((l - 52) mod 36 =? 2) eqn:E2; cbn [andb].
- right. apply Z.leb_le in E1. apply Z.eqb_eq in E2. split; [reflexivity|]. split; [lia|]. lia.
- left. split; [reflexivity|]. apply Z.eqb_neq in E2. intros (H1 & H2). apply E2. lia.
- left. split; [reflexivity|]. apply Z.leb_gt in E1. lia.
- left. split; [reflexivity|]. apply Z.leb_gt in E1. lia.
Qed.

(* The clean-length checks' arithmetic (+0x334..+0x39c). *)
Lemma cp_U_snez_xor : forall E c l, U E (SOff 10 0) = c -> U E (SOff 20 0) = l ->
  U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SOff 10 0) (SOff 20 0))) = if c =? l then 0 else 1.
Proof.
intros E c l Hc Hl. pose proof (U_range E (SOff 10 0)) as R1. pose proof (U_range E (SOff 20 0)) as R2.
rewrite !U_SAlu, U_SLit, Hc, Hl. cbn [zalu_raw]. unfold zcanon, M64 in *.
rewrite Hc in R1. rewrite Hl in R2.
assert (Hx : 0 <= Z.lxor c l) by (apply Z.lxor_nonneg; lia).
assert (Hx2 : Z.lxor c l < 2 ^ 64).
{ destruct (Z.eq_dec (Z.lxor c l) 0) as [-> | Hn]; [lia|].
  apply Z.log2_lt_pow2; [lia|].
  pose proof (Z.log2_lxor c l ltac:(lia) ltac:(lia)) as HL.
  assert (Lc : Z.log2 c < 64).
  { destruct (Z.eq_dec c 0) as [-> | Hc0]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  assert (Ll : Z.log2 l < 64).
  { destruct (Z.eq_dec l 0) as [-> | Hl0]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  lia. }
rewrite (Z.mod_small 0) by lia. rewrite (Z.mod_small (Z.lxor c l)) by lia.
destruct (Z.eqb_spec c l) as [-> | Hne].
- rewrite Z.lxor_nilpotent. reflexivity.
- assert (Z.lxor c l <> 0) by (intros Hq; apply Hne; apply Z.lxor_eq_0_iff; exact Hq).
  replace (0 <? Z.lxor c l) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Definition CP_KMSH : Z := 47261439850130342148203327256459739136.
Lemma cp_U_rot64 : forall E c, bv_unsigned (ew E 10) = c -> 52 <= c < 2 ^ 26 -> (c - 52) mod 36 = 0 ->
  U E (SAlu ALU_OR (SAlu ALU_SRL (SMd M_MUL (SOff 10 (-52)) (SLit CP_KM)) (SLit 2)) (SMd M_MUL (SOff 10 0) (SLit CP_KMSH)))
  = (c - 52) / 36.
Proof.
intros E c Hc Hr H36. rewrite !U_SAlu, !U_SMd, !U_SOff, !U_SLit, Hc. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
set (q := (c - 52) / 36). assert (Eq : c - 52 = 36 * q) by (unfold q; lia).
assert (Q0 : 0 <= q < 2 ^ 21) by (unfold q; lia).
rewrite (Z.mod_small (c + -52)) by lia. rewrite (Z.mod_small (c + 0)) by lia. rewrite Z.add_0_r.
change (CP_KM mod 2 ^ 64) with CP_KM. change (CP_KMSH mod 2 ^ 64) with (2 ^ 62).
change (Z.land (2 mod 2 ^ 64) 63) with 2.
replace (c + -52) with (36 * q) by lia.
replace ((36 * q * CP_KM) mod 2 ^ 64) with (4 * q).
2:{ apply (Z.mod_unique _ _ (20 * q)); [lia|]. unfold CP_KM. lia. }
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. rewrite Z.mul_comm, Z.div_mul by lia.
replace ((c * 2 ^ 62) mod 2 ^ 64) with 0.
2:{ apply (Z.mod_unique _ _ (13 + 9 * q)); [lia|]. lia. }
rewrite (Z.mod_small q) by lia. rewrite Z.lor_0_r. apply Z.mod_small. lia.
Qed.

(* +0x364..+0x38c: the residue test in 32-bit arithmetic, a rotate of (len * 0x38e38e39 - 6) by 2 compared with
   0x71c71c8; it is 1 exactly when len - 54 is a multiple of 36. *)
Lemma cp_lor_low_high : forall a h, 0 <= a < 2 ^ 30 -> 0 <= h -> Z.lor a (h * 2 ^ 30) = a + h * 2 ^ 30.
Proof.
intros a h Ha Hh. rewrite <- (Z.shiftl_mul_pow2 h 30) by lia.
assert (Hd : Z.land a (Z.shiftl h 30) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 30) as [Hl | Hg].
  - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite <- (Z.mod_small a (2 ^ 30)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
rewrite <- Z.lxor_lor by exact Hd. rewrite <- Z.add_nocarry_lxor by exact Hd. reflexivity.
Qed.
Lemma cp_nt32 : forall l, 54 <= l < 2 ^ 26 ->
  ((l * 954437177 - 6) mod 2 ^ 32) mod 4 = (l - 54) mod 4 /\
  ((((l * 954437177 - 6) mod 2 ^ 32) mod 4 = 0 /\ ((l * 954437177 - 6) mod 2 ^ 32) / 4 < 119304648) <->
   (l - 54) mod 36 = 0).
Proof.
intros l Hl.
set (v := (l * 954437177 - 6) mod 2 ^ 32).
assert (Dv : exists k, l * 954437177 - 6 = 2 ^ 32 * k + v /\ 0 <= v < 2 ^ 32).
{ exists ((l * 954437177 - 6) / 2 ^ 32). unfold v. split; [apply Z.div_mod; lia | apply Z.mod_pos_bound; lia]. }
destruct Dv as (k & Ek & Hv).
split; [lia|]. split.
- intros (H4 & Hq).
  assert (Ew : v = 4 * (v / 4)) by lia.
  assert (E9 : 9 * v - (l - 54) = 2 ^ 32 * (2 * l - 9 * k)) by lia.
  assert (Hm : 2 * l - 9 * k = 0) by lia.
  lia.
- intros H36.
  assert (Eq : exists q, l - 54 = 36 * q /\ 0 <= q < 2 ^ 21) by (exists ((l - 54) / 36); lia).
  destruct Eq as (q & Eq & Hq).
  assert (E4 : l * 954437177 - 6 = 2 ^ 32 * (12 + 8 * q) + 4 * q) by lia.
  assert (Ev : v = 4 * q) by lia.
  lia.
Qed.
Definition CP_X32 : sv := SAlu ALU_ADD (SMd M_MUL (SOff 20 0) (SLit 954437177)) (SLit (-6)).
Lemma cp_U_res32 : forall E l, bv_unsigned (ew E 20) = l -> 54 <= l < 2 ^ 26 ->
  U E (SAlu ALU_SLTU (SAlu ALU_OR (SAluw ALU_SRL CP_X32 (SLit 2)) (SAluw ALU_SLL CP_X32 (SLit 30))) (SLit 119304648))
  = if (l - 54) mod 36 =? 0 then 1 else 0.
Proof.
intros E l Hl Hr.
assert (UX : U E CP_X32 mod 2 ^ 32 = (l * 954437177 - 6) mod 2 ^ 32).
{ unfold CP_X32. rewrite U_SAlu, U_SMd, U_SOff, !U_SLit, Hl. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
  rewrite Z.add_0_r, (Z.mod_small l) by lia. change (954437177 mod 2 ^ 64) with 954437177.
  change ((-6) mod 2 ^ 64) with 18446744073709551610. lia. }
destruct (cp_nt32 l Hr) as (H4 & Hiff).
set (v := (l * 954437177 - 6) mod 2 ^ 32) in *.
assert (Hv : 0 <= v < 2 ^ 32) by (unfold v; apply Z.mod_pos_bound; lia).
assert (USR : U E (SAluw ALU_SRL CP_X32 (SLit 2)) = v / 4).
{ rewrite U_of_S, S_SAluw, UX, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 2 mod 2 ^ 32) 31) with 2.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  unfold bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
  lia. }
set (r := v mod 4) in *.
set (h := if r <? 2 then r else r + 2 ^ 34 - 4).
assert (USL : U E (SAluw ALU_SLL CP_X32 (SLit 30)) = h * 2 ^ 30).
{ rewrite U_of_S, S_SAluw, UX, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 30 mod 2 ^ 32) 31) with 30.
  rewrite Z.shiftl_mul_pow2 by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, h. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
  assert (Dv : v = 4 * (v / 4) + r) by (unfold r; lia).
  assert (Hr4 : 0 <= r < 4) by (unfold r; lia).
  destruct (Z.ltb_spec r 2); lia. }
rewrite U_SAlu, U_SAlu, USR, USL, U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
change (119304648 mod 2 ^ 64) with 119304648.
assert (Hr4 : 0 <= r < 4) by (unfold r; lia).
assert (Hh : 0 <= h <= 2 ^ 34 - 1) by (unfold h; destruct (Z.ltb_spec r 2); lia).
try rewrite (Z.mod_small (v / 4)) by lia. try rewrite (Z.mod_small (h * 2 ^ 30)) by lia.
rewrite (cp_lor_low_high (v / 4) h) by lia.
rewrite (Z.mod_small (v / 4 + h * 2 ^ 30)) by lia.
destruct (Z.eqb_spec r 0) as [Hr0 | Hr0].
- assert (Eh : h = 0) by (unfold h; rewrite Hr0; reflexivity). rewrite Eh, Z.mul_0_l, Z.add_0_r.
  destruct (Z.ltb_spec (v / 4) 119304648) as [Hlt | Hge].
  + replace ((l - 54) mod 36 =? 0) with true by (symmetry; apply Z.eqb_eq; apply Hiff; lia). reflexivity.
  + replace ((l - 54) mod 36 =? 0) with false; [reflexivity|]. symmetry. apply Z.eqb_neq. intros Hq.
    apply Hiff in Hq. lia.
- assert (Eh : 1 <= h) by (unfold h; destruct (Z.ltb_spec r 2); lia).
  replace (v / 4 + h * 2 ^ 30 <? 119304648) with false by (symmetry; apply Z.ltb_ge; lia).
  replace ((l - 54) mod 36 =? 0) with false; [reflexivity|]. symmetry. apply Z.eqb_neq. intros Hq. lia.
Qed.

(* The close of stage D1 at +0x3a0: cp_inv kept (no byte written, every callee-saved register kept). *)
Ltac cp_close_3a0 cx res HS HJ MEQ AG EE HAE R27 Hfrm HB0 Hgr LAWS HC RC Hnl :=
  let G27 := fresh "G27" in let GK := fresh "GK" in
  repeat rewrite wvb_collapse in HJ;
  cp_reg HS (27%bv : bv 5) (w64 res) G27
    ltac:(cbn [sv_denot]; try rewrite (AG 27%nat ltac:(lia)); rewrite (EE 27%nat 27%bv eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; exact R27);
  let HAEx := fresh "HAEx" in
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (HAEx : env_agree 32 (Ereg _ _) Ex)
      by (split; [intros k Hk; try rewrite (AG k ltac:(lia)); exact (proj1 HAE k Hk)
                 | cbn [ed ewset]; exact (proj2 HAE)]) end;
  pose proof (cp_regs_kept _ _ _ _ _ HS HAEx ltac:(vm_compute; reflexivity)) as GK;
  pmkst HS;
  apply SRr_ret;
  lazymatch goal with |- context [mkCfg (mkst ?rgf _ ?mmf _) ?mdf] =>
    do 3 eexists; exists rgf, mmf, mdf; do 4 eexists end;
  split; [reflexivity|]; split; [exact Hfrm|];
  split; [split|];
  [ apply (cp_base0_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => False) LAWS HC RC Hnl HB0 HJ);
    [ exact GK
    | intros a _ _; apply cp_aview_ext; exact MEQ
    | intros a; apply cp_apresent_ext; exact MEQ
    | intros a [] ]
  | exact G27
  | apply (cp_garr8_kept segs _ _ _ _ _ _ (fun j _ => cp_aview_ext _ _ _ MEQ _) Hgr) ].

Lemma cp_stage_D1 : forall cx W' c',
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B -> AR_laws segs B ->
  dec_b_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_b_rom cx ->
  cp_Q_cl cx W' c' -> SRr segs W' c' (cp_R3a0 cx).
Proof.
intros cx W' c' HC HO HE LAWS HBASE HROMc HQ.
assert (RC : cp_romctx cx) by exact (conj HO (conj HE HROMc)).
pose proof HBASE as (HAFN & _ & _ & _ & Hpn & Hnl & _).
assert (Hn0 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hq _]]; lia).
destruct HQ as (fx' & ly' & S' & regs' & mem' & md' & res & mode & nch & ns & -> & Hfrm & ((HB0 & R27) & Hgr) & R10).
pose proof (cp_core_facts cx ly' S' W' regs' mem' md' _ LAWS (proj1 HB0)) as (Hsp0 & Hsp16 & EF & Hin & HFc & HFa).
pose proof HB0 as (Hcore & Hbl & Hres & Hmle & Hmok & Hfrs & R18 & R20 & R21 & R22 & R23 & Hmode & Hwhere & Hfsh & H112).
pose proof Hcore as (HJ & Hfrms & R8 & R9 & Rsp & Hsp1 & Hsp32 & R3 & R4 & Hsaved & HF4096 & HF32 & HFpres & HFL & Hpay
  & Hgarr).
pose proof (cp_len_facts cx ltac:(lia) Hnl) as (L0 & U0 & LU & LB & L3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hinr : In (res, len cx) (ablocks B ly' S')) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hrc : res + len cx <= alloc_ceiling).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hinr) as (_ & _ & Hc & _).
  pose proof (req_size_pos (len cx) L0). lia. }
pose proof (cp_rom_view_rd cx ly' S' W' mem' md' _ HO HE HROMc HJ) as HRV.
pose proof Hmode as (Hsel & Hnch & Hns & V4 & V8).
assert (Hmr : 4096 <= mode /\ mode + 12 <= alloc_ceiling /\
  (forall a, mode + 4 <= a < mode + 12 -> ~ (0x10310 <= a < 0x10318 \/ 0x10360 <= a < 0x10368))).
{ destruct Hwhere as [-> | (Hin_t & _ & _)].
  - split; [lia|]. split; [lia|]. intros a Ha Hro.
    apply (frm_img segs B LAWS _ _ _ _ _ _ _ a (proj1 HJ) Hin); [rewrite EF; change (fs_frame_bytes DEC_FCLASS) with 64; lia|].
    exact (cp_ro_img a Hro).
  - unfold cp_tbl in Hin_t. cbn in Hin_t. destruct Hin_t as [<- | [<- | [<- | []]]]; (split; [lia|]); (split; [lia|]);
    intros a Ha; lia. }
pose proof (@paj_run fx' rc dec_B_sink_head decodeb_listing PL_decodeb PIB B LAWS) as RUN.
pose proof (@paj_branch fx' rc decodeb_listing PIB) as BR.
set (XT := [Z_to_bv 64 (nch mod 2 ^ 32); Z_to_bv 64 (ns mod 2 ^ 32)]).
set (E := Eimg (PI := PIB) (Ereg regs' XT)).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = YK11.getr regs' r).
{ intros kk r Hk. unfold E. apply ew_Eimg_Ereg_natB. exact Hk. }
assert (E32 : ew E 32 = Z_to_bv 64 (nch mod 2 ^ 32))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (ns mod 2 ^ 32))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 1)).
assert (HAE : env_agree 32 (Ereg regs' XT) E).
{ split; [|reflexivity]. intros k Hk. unfold E. rewrite (Eimg_low (PI := PIB) _ k ltac:(unfold A_TEXT; lia)).
  reflexivity. }
assert (UB : forall (k : nat) (r : bv 5) v, Z.of_nat k = bv_unsigned r -> YK11.getr regs' r = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E k) = v).
{ intros k r v Hk Hr Hv. rewrite (EE k r Hk), Hr. apply unsigned_lit_small. exact Hv. }
assert (Ub7 : bv_unsigned (ew E (A_OBJ 7)) = 0x10310).
{ rewrite (img_env_atomB (PI := PIB) E (A_OBJ 7) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  change (pa_val (A_OBJ 7)) with (decodeb_val (A_OBJ 7)). rewrite (proj1 cp_obj_vals). reflexivity. }
assert (Ub8 : bv_unsigned (ew E (A_OBJ 8)) = 0x10360).
{ rewrite (img_env_atomB (PI := PIB) E (A_OBJ 8) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  change (pa_val (A_OBJ 8)) with (decodeb_val (A_OBJ 8)). rewrite (proj2 cp_obj_vals). reflexivity. }
assert (Ub23 : bv_unsigned (ew E 23) = mode + 4) by (apply (UB 23%nat 23%bv); [reflexivity | exact R23 | lia]).
assert (Ub22 : bv_unsigned (ew E 22) = mode + 8) by (apply (UB 22%nat 22%bv); [reflexivity | exact R22 | lia]).
assert (Ub9 : bv_unsigned (ew E 9) = d_sp1 cx) by (apply (UB 9%nat 9%bv); [reflexivity | exact R9 | lia]).
assert (Ub18 : bv_unsigned (ew E 18) = SHADOW_OFF)
  by (apply (UB 18%nat 18%bv); [reflexivity | exact R18 | unfold SHADOW_OFF; lia]).
assert (Ub27 : bv_unsigned (ew E 27) = res) by (apply (UB 27%nat 27%bv); [reflexivity | exact R27 | lia]).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hjpres & _).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x320 sr_atoms [cp_r_km; cp_r_t36] None cp_facts)
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 (decodeb_val A_TEXT + 0x320)) mem' (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply (pa_entry_st_ok_full (PI := PIB)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold cp_r_km, cp_r_t36.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Ub7. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0x10310 0 8 (SLit CP_KM) CP_KM); [reflexivity | unfold CP_KM; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply (cp_rom_word W' mem' 0x10310 CP_KM HRV); [|exact cp_rom_km].
      intros i Hi. apply (cp_in_ro_rd _ 8); [cbn; auto | lia].
    + rewrite Ub8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0x10360 0 8 (SLit CP_T36) CP_T36); [reflexivity | unfold CP_T36; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply (cp_rom_word W' mem' 0x10360 CP_T36 HRV); [|exact cp_rom_t36].
      intros i Hi. apply (cp_in_ro_rd _ 8); [cbn; auto 10 | lia].
  - apply pairwise_disjoint_of_extents.
    unfold cp_r_km, cp_r_t36, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Ub7, Ub8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [cp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Ub18, Ub27. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF. repeat split; lia. }
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W') mem')) by constructor.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr SEGS Wx (mkCfg (mkst regs' (Z_to_bv 64 (decodeb_val A_TEXT + 0x320)) mem' (seg_rom SEGS)) md') Q) end.
assert (AG : forall n, (n < 512)%nat -> ew E n = ew E n) by reflexivity.
assert (MEQ : forall x, mem' x = mem' x) by reflexivity.
paj_run_tok RUN HS HJ SHOK Bspan; [cp_awr_ro |].
cp_fnil MEQ.
set (cl := reac_frame_clean_len_c.reac_frame_clean_len_model (len cx)) in R10.
assert (Hcl : 0 <= cl <= len cx) by (unfold cl, reac_frame_clean_len_c.reac_frame_clean_len_model;
  destruct ((54 <=? len cx) && ((len cx - 52) mod 36 =? 2)) eqn:Eb; [apply andb_true_iff in Eb as [Eb _]; apply Z.leb_le in Eb|]; lia).
assert (UL : U E (SOff 20 0) = len cx) by (apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl); exact R20 | lia]).
assert (UA : U E (SOff 10 0) = cl) by (apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl); exact R10 | lia]).
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite branch_eq_U, UA, UL in Hc. apply Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [cp_awr_ro |].
  cp_fnil MEQ.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + rewrite branch_ltu_U, UL, U_lit in Hc0 by lia. apply Z.ltb_lt in Hc0.
    paj_run_tok RUN HS HJ SHOK Bspan; [cp_awr_ro |].
    cp_fnil MEQ.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    { exfalso. rewrite branch_ne_U, U_lit, (cp_U_snez_xor E cl (len cx) UA UL) in Hc1 by lia.
      rewrite (proj2 (Z.eqb_eq cl (len cx)) Hc) in Hc1. cbn in Hc1. discriminate. }
    pose proof (@paj_run_to fx' rc dec_B_sink_head decodeb_listing PL_decodeb PIB B LAWS) as RUNTO.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x3a0; [cp_awr_ro |].
    cp_fnil MEQ.
    cp_close_3a0 cx res HS HJ MEQ AG EE HAE R27 Hfrm HB0 Hgr LAWS HC RC Hnl.
  + rewrite branch_ltu_U, UL, U_lit in Hc0 by lia. apply Z.ltb_ge in Hc0.
    paj_run_tok RUN HS HJ SHOK Bspan; [cp_awr_ro |].
    cp_fnil MEQ.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    { exfalso. rewrite branch_ne_U, (cp_U_snez_xor E cl (len cx) UA UL) in Hc1.
      fold CP_X32 in Hc1. rewrite (cp_U_res32 E (len cx)) in Hc1
        by (first [rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia | lia]).
      rewrite (proj2 (Z.eqb_eq cl (len cx)) Hc) in Hc1.
      destruct (cp_clean_cases (len cx) L0) as [(_ & Hn36) | (Hq & _)]; [| fold cl in Hq; lia].
      replace ((len cx - 54) mod 36 =? 0) with false in Hc1
        by (symmetry; apply Z.eqb_neq; intros Hq; apply Hn36; split; [lia | exact Hq]).
      cbn in Hc1. discriminate. }
    pose proof (@paj_run_to fx' rc dec_B_sink_head decodeb_listing PL_decodeb PIB B LAWS) as RUNTO.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x3a0; [cp_awr_ro |].
    cp_fnil MEQ.
    cp_close_3a0 cx res HS HJ MEQ AG EE HAE R27 Hfrm HB0 Hgr LAWS HC RC Hnl.
- rewrite branch_eq_U, UA, UL in Hc. apply Z.eqb_neq in Hc.
  destruct (cp_clean_cases (len cx) L0) as [(Hq & _) | (Hq & H54 & H36)]; [exfalso; apply Hc; exact Hq|].
  fold cl in Hq.
  paj_run_tok RUN HS HJ SHOK Bspan; [cp_awr_ro |].
  cp_fnil MEQ.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. rewrite branch_ltu_U, UA, U_lit in Hc0 by lia. apply Z.ltb_lt in Hc0. lia. }
  paj_run_tok RUN HS HJ SHOK Bspan; [cp_awr_ro |].
  cp_fnil MEQ.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. rewrite branch_ne_U, UL in Hc1.
    rewrite (U_atom_off E 10 cl 2) in Hc1 by (first [rewrite (EE 10%nat 10%bv eq_refl); exact R10 | lia]).
    replace (cl + 2 =? len cx) with true in Hc1 by (symmetry; apply Z.eqb_eq; lia). cbn in Hc1. discriminate. }
  paj_run_tok RUN HS HJ SHOK Bspan; [cp_awr_ro |].
  cp_fnil MEQ.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. rewrite branch_ltu_U, U_lit in Hc2 by (unfold CP_T36; lia).
    fold CP_KM CP_KMSH in Hc2.
    rewrite (cp_U_rot64 E cl) in Hc2 by (first [rewrite (EE 10%nat 10%bv eq_refl), R10; apply unsigned_lit_small; lia | lia]).
    apply Z.ltb_lt in Hc2. unfold CP_T36 in Hc2. lia. }
  paj_run_tok RUN HS HJ SHOK Bspan; [cp_awr_ro |].
  cp_fnil MEQ.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. rewrite branch_ltu_U, UL, U_lit in Hc3 by lia. apply Z.ltb_lt in Hc3. lia. }
  paj_run_tok RUN HS HJ SHOK Bspan; [cp_awr_ro |].
  cp_fnil MEQ.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. rewrite branch_ne_U, (cp_U_snez_xor E cl (len cx) UA UL) in Hc4.
    fold CP_X32 in Hc4. rewrite (cp_U_res32 E (len cx)) in Hc4
      by (first [rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia | lia]).
    replace (cl =? len cx) with false in Hc4 by (symmetry; apply Z.eqb_neq; exact Hc).
    replace ((len cx - 54) mod 36 =? 0) with true in Hc4 by (symmetry; apply Z.eqb_eq; exact H36).
    cbn in Hc4. discriminate. }
  pose proof (@paj_run_to fx' rc dec_B_sink_head decodeb_listing PL_decodeb PIB B LAWS) as RUNTO.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x3a0; [cp_awr_ro |].
  cp_fnil MEQ.
  cp_close_3a0 cx res HS HJ MEQ AG EE HAE R27 Hfrm HB0 Hgr LAWS HC RC Hnl.
Qed.

(* ------------------------------------------------------------------ *)
(* 8. Stage D2: +0x3a0 .. malloc #2's entry (+0x414)                     *)
(* ------------------------------------------------------------------ *)

Lemma cp_ra_sub : forall (r : Z -> option Z) s a n a' n', range_addressable r s a n -> a <= a' -> a' + n' <= a + n ->
  range_addressable r s a' n'.
Proof. intros r s a n a' n' H H1 H2 x Hx. apply H. lia. Qed.

(* The call chain malloc #2 sees, and its unwind trace: LLVMFuzzerTestOneInput_segB.v (a working branch
   84be2173fcc) eb_ch / eb_chain_at / eb_trace_at, copied; the return address is +0x418. *)
Definition cp_ch (cx : dctx) : list (Z * Z * Z) :=
  if d_sp0 cx + 16 <? ly_top (d_ly cx) then [(d_sp0 cx, raZ (d_regs cx), s0Z (d_regs cx))] else [].
Lemma cp_chain_at : forall cx ly' S' (W' : world segs) mem' md' k (regsT : bvmap 5 word),
  dec_b_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly' S' W' mem' md' k ->
  dec_b_saved cx (aview segs (w_H W') mem') ->
  spZ regsT = d_sp1 cx -> s0Z regsT = d_sp0 cx -> 4096 <= raZ regsT ->
  d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 ->
  chain_pre ly' (aview segs (w_H W') mem') regsT (cp_ch cx).
Proof.
intros cx ly' S' W' mem' md' k regsT HB HJ Hsv Hsp Hs0 Hra Hsp1.
pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & _ & H47 & _ & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & HF1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
change DEC_LLVMF_STK with 32768 in *. unfold d_sp0 in *.
apply (achain_chain_pre ly' _ (d_sp1 cx) (spZ (d_regs cx)) _ regsT); [| lia | exact Hs0 | exact Hra].
apply (achain_ly_top (d_ly cx)); [exact Etop|].
unfold cp_ch, d_sp0. destruct (Z.ltb_spec (spZ (d_regs cx) + 16) (ly_top (d_ly cx))) as [Hlt | Hge].
- assert (Hal8 : spZ (d_regs cx) mod 8 = 0).
  { pose proof (Z.div_mod (spZ (d_regs cx)) 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
    replace (16 * (spZ (d_regs cx) / 16)) with ((2 * (spZ (d_regs cx) / 16)) * 8) by lia. apply Z_mod_mult. }
  unfold dec_b_saved, dec_b_saved_at in Hsv. rewrite Forall_forall in Hsv.
  pose proof (Hsv (8, 1) ltac:(cbn; auto)) as H8. pose proof (Hsv (16, 8) ltac:(cbn; auto)) as H16.
  cbn [fst snd] in H8, H16.
  apply (achain_push _ _ _ _ _ _ _ _ Hch); [lia | | exact H8 | exact H16 | exact Hra4 | lia | exact Hal8 | lia | lia].
  intros a Ha. apply HF1; lia.
- left. split; [right; left; lia | reflexivity].
Qed.
Lemma cp_trace_at : forall cx (regsT : bvmap 5 word),
  dec_b_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_llvmf_utraces RA_LLVMF B -> raZ regsT = DEC_A_LLVMF + 0x418 ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (cp_ch cx)) (as_universe B).
Proof.
intros cx regsT HB HU Hra. pose proof HB as (_ & Hra_eq & _).
unfold cp_ch. destruct (_ <? _).
- destruct (HU [RA_LLVMF] ltac:(cbn; auto)) as (Hm & _).
  specialize (Hm (DEC_A_LLVMF + 0x418) ltac:(unfold DEC_LLVMF_RA_MALLOC; cbn [map In]; auto)).
  unfold call_trace0, unwind_of_chain, dec_utrace in *. cbn [flat_map app] in *.
  rewrite Hra, Hra_eq. exact Hm.
- destruct (HU [] ltac:(cbn; auto)) as (Hm & _).
  specialize (Hm (DEC_A_LLVMF + 0x418) ltac:(unfold DEC_LLVMF_RA_MALLOC; cbn [map In]; auto)).
  unfold call_trace0, unwind_of_chain, dec_utrace in *. cbn [flat_map app] in *.
  rewrite Hra. exact Hm.
Qed.

(* The values +0x3bc .. +0x40c compute from the two mode fields (atoms 32 = nch mod 2^32, 33 = ns mod 2^32). *)
Definition cp_a3 : sv := SExt false 32 (SOff 32 0).
Definition cp_a2 : sv := SExt true 32 (SOff 33 0).
Definition cp_zns : sv := SAlu ALU_SRL (SAlu ALU_SLL cp_a2 (SLit 32)) (SLit 32).
Definition cp_prod : sv := SMd M_MUL cp_zns cp_a3.
Definition cp_s7 : sv := SAluw ALU_ADD cp_a3 (SLit 0).
Definition cp_fit : sv := SAlu ALU_AND (SAlu ALU_SLT (SLit 0) cp_s7) (SAlu ALU_SLT (SLit 0) cp_a2).
Definition cp_x3 : sv := SAlu ALU_ADD (SAlu ALU_SLL cp_prod (SLit 1)) cp_prod.
Definition cp_s10 : sv := SAlu ALU_ADD cp_x3 (SAlu ALU_SLTU cp_x3 (SLit 1)).
Lemma cp_swrap32 : forall v, -2 ^ 31 <= v < 2 ^ 31 -> bv_swrap 32 (v mod 2 ^ 32) = v.
Proof.
intros v Hv. unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus.
change (2 ^ Z.of_N 32 / 2) with (2 ^ 31). change (2 ^ Z.of_N 32) with (2 ^ 32). lia.
Qed.
Lemma cp_swrap64 : forall v, -2 ^ 63 <= v < 2 ^ 63 -> bv_swrap 64 (v mod 2 ^ 64) = v.
Proof.
intros v Hv. unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64 / 2) with (2 ^ 63). change (2 ^ Z.of_N 64) with (2 ^ 64). lia.
Qed.
Lemma cp_denot_w64 : forall Ex e X, U Ex e = X mod 2 ^ 64 -> sv_denot Ex e = w64 X.
Proof.
intros Ex e X H. rewrite denot_lit_U, H. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma cp_Ua3 : forall Ex nch, U Ex (SOff 32 0) = nch mod 2 ^ 32 -> U Ex cp_a3 = nch mod 2 ^ 32.
Proof. intros Ex nch H. unfold cp_a3. rewrite U_zext, H. change (2 ^ Z.of_N 32) with (2 ^ 32). apply Z.mod_mod. lia. Qed.
Lemma cp_Ua2 : forall Ex ns, U Ex (SOff 33 0) = ns mod 2 ^ 32 -> -128 <= ns <= 127 -> U Ex cp_a2 = ns mod 2 ^ 64.
Proof.
intros Ex ns H Hs. unfold cp_a2. rewrite U_SExt, H. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite Z.mod_mod by lia. rewrite cp_swrap32 by lia. reflexivity.
Qed.
Lemma cp_Us7 : forall Ex nch, U Ex (SOff 32 0) = nch mod 2 ^ 32 -> -128 <= nch <= 127 -> U Ex cp_s7 = nch mod 2 ^ 64.
Proof.
intros Ex nch H Hn. unfold cp_s7. rewrite U_of_S, S_SAluw, (cp_Ua3 Ex nch H), U_SLit. cbn [zalu_raw].
change (zcanon 0) with 0. rewrite Z.mod_mod, Z.mod_0_l, Z.add_0_r by lia. rewrite cp_swrap32 by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
Lemma cp_Uzns : forall Ex ns, U Ex (SOff 33 0) = ns mod 2 ^ 32 -> -128 <= ns <= 127 -> U Ex cp_zns = ns mod 2 ^ 32.
Proof.
intros Ex ns H Hs. unfold cp_zns. rewrite !U_SAlu, (cp_Ua2 Ex ns H Hs), !U_SLit. cbn [zalu_raw].
change (zcanon 32) with 32. change (Z.land 32 63) with 32.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold zcanon, M64.
assert (A : (ns mod 2 ^ 64 * 2 ^ 32) mod 2 ^ 64 = (ns mod 2 ^ 32) * 2 ^ 32).
{ replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) at 2 by reflexivity. rewrite Z.mul_mod_distr_r by lia. f_equal. lia. }
rewrite A, Z.div_mul by lia. apply Z.mod_small. pose proof (Z.mod_pos_bound ns (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma cp_Uprod : forall Ex nch ns, U Ex (SOff 32 0) = nch mod 2 ^ 32 -> U Ex (SOff 33 0) = ns mod 2 ^ 32 ->
  -128 <= ns <= 127 -> U Ex cp_prod = dec_b_prod nch ns.
Proof.
intros Ex nch ns H32 H33 Hs. unfold cp_prod. rewrite U_SMd, (cp_Uzns Ex ns H33 Hs), (cp_Ua3 Ex nch H32).
cbn [zmd_raw]. unfold zcanon, M64, dec_b_prod. rewrite Z.mul_comm. reflexivity.
Qed.
Lemma cp_Ufit : forall Ex nch ns, U Ex (SOff 32 0) = nch mod 2 ^ 32 -> U Ex (SOff 33 0) = ns mod 2 ^ 32 ->
  -128 <= nch <= 127 -> -128 <= ns <= 127 -> U Ex cp_fit = dec_b_fits0 nch ns.
Proof.
intros Ex nch ns H32 H33 Hn Hs. unfold cp_fit. rewrite !U_SAlu, (cp_Us7 Ex nch H32 Hn), (cp_Ua2 Ex ns H33 Hs), !U_SLit.
cbn [zalu_raw]. change (zcanon 0) with 0. change (bv_swrap 64 0) with 0.
rewrite !cp_swrap64 by lia. unfold dec_b_fits0.
destruct (Z.ltb_spec 0 nch); destruct (Z.ltb_spec 0 ns); vm_compute; reflexivity.
Qed.
Lemma cp_Us10 : forall Ex nch ns, U Ex (SOff 32 0) = nch mod 2 ^ 32 -> U Ex (SOff 33 0) = ns mod 2 ^ 32 ->
  0 < nch <= 127 -> 0 < ns <= 127 -> U Ex cp_s10 = dec_b_olen nch ns.
Proof.
intros Ex nch ns H32 H33 Hn Hs.
assert (P : U Ex cp_prod = nch * ns).
{ rewrite (cp_Uprod Ex nch ns H32 H33 ltac:(lia)). unfold dec_b_prod.
  rewrite (Z.mod_small nch), (Z.mod_small ns) by lia. apply Z.mod_small. nia. }
assert (Q : 1 <= nch * ns <= 16129) by nia.
unfold cp_s10, cp_x3. rewrite !U_SAlu, P, !U_SLit. cbn [zalu_raw].
change (zcanon 1) with 1. change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
unfold zcanon, M64. rewrite (Z.mod_small (nch * ns * 2)) by lia. rewrite (Z.mod_small (nch * ns * 2 + nch * ns)) by lia.
replace (nch * ns * 2 + nch * ns <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
unfold dec_b_olen. replace ((0 <? nch) && (0 <? ns)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
rewrite Z.mod_0_l by lia. rewrite Z.add_0_r. rewrite Z.mod_small by lia. lia.
Qed.

(* The windows of stage D2's regions: only the spill slots [s1 + 32, s1 + 80) are writable. *)
Lemma cp_win : forall Ex (rs : smem) sp1,
  windows rs = [(Some 23%nat, 0, 0); (Some 22%nat, 0, 0); (Some 9%nat, 32, 80)] -> bv_unsigned (ew Ex 9) = sp1 ->
  forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi ->
  sp1 + 32 <= a < sp1 + 80.
Proof.
intros Ex rs sp1 Hw H9 b wlo whi a Hin Ha. rewrite Hw in Hin.
destruct Hin as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <- <-; cbn [base_val] in Ha; lia.
Qed.
(* The spill slots are apart from every byte cp_base0 reads. *)
Lemma cp_kz_spill : forall cx ly S W regs mem md res mode nch ns a,
  AR_laws segs B -> cp_base0 cx ly S W regs mem md res mode nch ns ->
  d_sp1 cx + 32 <= a < d_sp1 cx + 80 -> ~ cp_kz cx a.
Proof.
intros cx ly S W regs mem md res mode nch ns a LAWS HB Ha.
pose proof (cp_core_facts cx ly S W regs mem md _ LAWS (proj1 HB)) as (Hsp0 & Hsp16 & EF & Hin & HFc & HFa).
destruct HB as (Hcore & _).
destruct Hcore as (HJ & Hfrms & R8 & R9 & Rsp & Hsp1 & Hsp32 & R3 & R4 & Hsaved & HF4096 & HF32 & HFpres & HFL & Hpay & Hgarr).
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSH : SHADOW_OFF <= d_SH cx /\ d_SH cx + 8 <= kHighShadowEnd).
{ unfold d_SH, shadow_addr. unfold in_app in HFa. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
unfold cp_kz. unfold in_app in HFa. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
intros Hk. destruct Hk as [Hk | [Hk | [Hk | [Hk | [Hk | (Hnp & Hk)]]]]]; try lia.
pose proof (Hpay Hnp) as Hinp.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinp) as (_ & _ & Hpc & _).
pose proof (req_size_pos (d_n cx) ltac:(lia)). lia.
Qed.
(* LLVMFuzzerTestOneInput_segB.v (a working branch 84be2173fcc) eb_rdword_of_bytes /
   eb_rdword_of_val_mem, copied. *)
Lemma cp_rdword_of_bytes : forall (r : reader) a v, 0 <= v < 2 ^ 64 ->
  (forall k, (k < 8)%nat -> r (a + Z.of_nat k) = Some (le_byte v 8 k)) -> rdword r a = Some v.
Proof.
intros r a v Hv B0. unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B0 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B0 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B0 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B0 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B0 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B0 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B0 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B0 7%nat) by lia.
f_equal. apply le_bytes8. exact Hv.
Qed.
Lemma cp_rdword_of_val_mem : forall H (mem : word -> option byte) a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros H mem a v Hv Hr. apply cp_rdword_of_bytes; [exact Hr|].
intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.
(* The mode at a later state: a table's pointer word is re-read from dec_crt_cells' rows and its fields through the
   read-only view; the local's fields are kept. *)
Lemma cp_mode_ok_keep : forall cx ly S W mem md W0 mem0 mode nch ns,
  dec_crt_cells B -> AR segs B ly S W mem md -> dec_rom_view_rd W mem -> cp_mode_where cx mode nch ns ->
  dec_b_mode_ok cx W0 mem0 mode nch ns ->
  (forall a, d_F cx + 36 <= a < d_F cx + 44 -> aview segs (w_H W) mem a = aview segs (w_H W0) mem0 a) ->
  dec_b_mode_ok cx W mem mode nch ns.
Proof.
intros cx ly S W mem md W0 mem0 mode nch ns HC HAR HRV Hwhere Hmode HK.
destruct Hwhere as [Hcu | (Hin_t & -> & ->)].
- destruct Hmode as (_ & Hnch & Hns & V4 & V8). subst mode.
  refine (conj (or_intror (or_intror (or_intror eq_refl))) (conj Hnch (conj Hns (conj _ _)))).
  + apply (val_mem_kept segs (w_H W0) (w_H W) mem0 mem); [|exact V4]. intros k Hk. cbn in Hk. apply HK. lia.
  + apply (val_mem_kept segs (w_H W0) (w_H W) mem0 mem); [|exact V8]. intros k Hk. cbn in Hk. apply HK. lia.
- assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  destruct (cp_tbl_rows ly HC) as (P4 & P5 & P6).
  destruct (cp_tbl_fields W mem mode HRV Hin_t) as (V4' & V8').
  change (40 mod 2 ^ 32) with 40. change (12 mod 2 ^ 32) with 12.
  split; [|split; [lia|split; [lia|split; [exact V4' | exact V8']]]].
  unfold cp_tbl in Hin_t. cbn in Hin_t. destruct Hin_t as [<- | [<- | [<- | []]]].
  + left. apply (rdword_cell B ly); [lia | exact (CH _ P4)].
  + right; left. apply (rdword_cell B ly); [lia | exact (CH _ P5)].
  + right; right; left. apply (rdword_cell B ly); [lia | exact (CH _ P6)].
Qed.

(* At malloc #2's entry (+0x414): cp_base0 at the registers of +0x3a0 (regsK), the call's registers regs' agreeing
   with them on the registers it keeps, the values +0x3bc .. +0x410 computed, and the four spills. *)
Definition cp_at414 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' (regs' regsK : bvmap 5 word) mem' md' (res mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 (decodeb_sigma DB___interceptor_trampoline_malloc)) mem'
                  (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    cp_base0 cx ly' S' W' regsK mem' md' res mode nch ns /\
    (forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 27] -> YK11.getr regs' (Z_to_bv 5 r) = YK11.getr regsK (Z_to_bv 5 r)) /\
    YK11.getr regsK 27 = w64 res /\
    YK11.getr regs' 1 = w64 (DEC_A_LLVMF + 0x418) /\
    YK11.getr regs' 10 = w64 (dec_b_olen nch ns) /\
    YK11.getr regs' 22 = w64 (dec_b_prod nch ns) /\
    YK11.getr regs' 23 = w64 nch /\
    YK11.getr regs' 24 = w64 (dec_b_fits0 nch ns) /\
    YK11.getr regs' 26 = w64 (dec_b_olen nch ns) /\
    garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    dec_b_slot cx (aview segs (w_H W') mem') 32 SHADOW_OFF /\
    dec_b_slot cx (aview segs (w_H W') mem') 56 (ns mod 2 ^ 32) /\
    dec_b_slot cx (aview segs (w_H W') mem') 64 (nch mod 2 ^ 32) /\
    dec_b_slot cx (aview segs (w_H W') mem') 72 (ns mod 2 ^ 64).

(* A run of stage D2 keeps every byte outside the spill slots: kept_of_frame, with the region list's windows
   computed on the closed list first (never vm_compute under an evar). *)
Ltac cp_keep_of cx Ub9 HFrx K :=
  lazymatch type of HFrx with frame_of ?E1 ?rs1 (mrestrict ?Hx ?m0) (mrestrict ?Hx ?m1) =>
    let W1 := fresh "W1" in let B1 := fresh "B1" in
    assert (W1 : windows rs1 = [(Some 23%nat, 0, 0); (Some 22%nat, 0, 0); (Some 9%nat, 32, 80)])
      by (vm_compute; reflexivity);
    assert (B1 : bv_unsigned (ew E1 9) = d_sp1 cx) by (repeat rewrite ew_ewset_other by lia; exact Ub9);
    pose proof (kept_of_frame (segs := decodesegsB0) E1 rs1 Hx m0 m1
                  (fun a => d_sp1 cx + 32 <= a < d_sp1 cx + 80) HFrx (cp_win E1 rs1 (d_sp1 cx) W1 B1)) as K;
    clear W1 B1
  end.

Lemma cp_stage_D2 : forall cx W' c',
  dec_crt_cells B -> cp_romctx cx -> AR_laws segs B ->
  dec_b_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  cp_R3a0 cx W' c' -> SRr segs W' c' (cp_at414 cx).
Proof.
intros cx W' c' HC RC LAWS HBASE HQ.
pose proof HBASE as (HAFN & _ & _ & _ & Hpn & Hnl & _).
assert (Hn0 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hq _]]; lia).
destruct HQ as (fx' & ly' & S' & regs' & mem' & md' & res & mode & nch & ns & -> & Hfrm & ((HB0 & R27) & Hgr)).
pose proof (cp_core_facts cx ly' S' W' regs' mem' md' _ LAWS (proj1 HB0)) as (Hsp0 & Hsp16 & EF & Hin & HFc & HFa).
pose proof HB0 as (Hcore & Hbl & Hres & Hmle & Hmok & Hfrs & R18 & R20 & R21 & R22 & R23 & Hmode & Hwhere & Hfsh & H112).
pose proof Hcore as (HJ & Hfrms & R8 & R9 & Rsp & Hsp1 & Hsp32 & R3 & R4 & Hsaved & HF4096 & HF32 & HFpres & HFL & Hpay
  & Hgarr).
pose proof (cp_len_facts cx ltac:(lia) Hnl) as (L0 & U0 & LU & LB & L3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hinr : In (res, len cx) (ablocks B ly' S')) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hrc : res + len cx <= alloc_ceiling).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hinr) as (_ & _ & Hc & _).
  pose proof (req_size_pos (len cx) L0). lia. }
pose proof (cp_mode_addr cx ly' S' W' regs' mem' md' res mode nch ns LAWS HC HB0) as HMA.
pose proof Hmode as (Hsel & Hnch & Hns & V4 & V8).
assert (Hmr : 4096 <= mode /\ mode + 12 <= alloc_ceiling).
{ destruct Hwhere as [-> | (Hin_t & _ & _)]; [lia|].
  unfold cp_tbl in Hin_t. cbn in Hin_t. destruct Hin_t as [<- | [<- | [<- | []]]]; lia. }
pose proof (@paj_run fx' rc dec_B_sink_head decodeb_listing PL_decodeb PIB B LAWS) as RUN.
pose proof (@paj_branch fx' rc decodeb_listing PIB) as BR.
set (XT := [Z_to_bv 64 (nch mod 2 ^ 32); Z_to_bv 64 (ns mod 2 ^ 32)]).
set (E := Eimg (PI := PIB) (Ereg regs' XT)).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = YK11.getr regs' r).
{ intros kk r Hk. unfold E. apply ew_Eimg_Ereg_natB. exact Hk. }
assert (E32 : ew E 32 = Z_to_bv 64 (nch mod 2 ^ 32))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (ns mod 2 ^ 32))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 1)).
assert (HAE : env_agree 32 (Ereg regs' XT) E).
{ split; [|reflexivity]. intros k Hk. unfold E. rewrite (Eimg_low (PI := PIB) _ k ltac:(unfold A_TEXT; lia)).
  reflexivity. }
assert (UB : forall (k : nat) (r : bv 5) v, Z.of_nat k = bv_unsigned r -> YK11.getr regs' r = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E k) = v).
{ intros k r v Hk Hr Hv. rewrite (EE k r Hk), Hr. apply unsigned_lit_small. exact Hv. }
assert (Ub23 : bv_unsigned (ew E 23) = mode + 4) by (apply (UB 23%nat 23%bv); [reflexivity | exact R23 | lia]).
assert (Ub22 : bv_unsigned (ew E 22) = mode + 8) by (apply (UB 22%nat 22%bv); [reflexivity | exact R22 | lia]).
assert (Ub9 : bv_unsigned (ew E 9) = d_sp1 cx) by (apply (UB 9%nat 9%bv); [reflexivity | exact R9 | lia]).
assert (Ub18 : bv_unsigned (ew E 18) = SHADOW_OFF)
  by (apply (UB 18%nat 18%bv); [reflexivity | exact R18 | unfold SHADOW_OFF; lia]).
assert (Ub27 : bv_unsigned (ew E 27) = res) by (apply (UB 27%nat 27%bv); [reflexivity | exact R27 | lia]).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hjpres & _).
assert (HS : st_ok_pi SEGS VAL E cp_ssD
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 (decodeb_val A_TEXT + 0x3a0)) mem' (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold cp_ssD. apply (pa_entry_st_ok_full (PI := PIB)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold cp_regsD, cp_r_nch, cp_r_ns, cp_r_stk.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Ub23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (mode + 4) 0 4 (SOff 32 0) (nch mod 2 ^ 32));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact V4.
    + rewrite Ub22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (mode + 8) 0 4 (SOff 33 0) (ns mod 2 ^ 32));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact V8.
    + rewrite Ub9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hjpres. unfold DEC_LLVMF_STK. lia.
  - apply pairwise_disjoint_of_extents.
    unfold cp_regsD, cp_r_nch, cp_r_ns, cp_r_stk, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Ub23, Ub22, Ub9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [cp_factsD f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Ub18, Ub27, Ub22, Ub23, Ub9.
    rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. unfold SB, SHADOW_OFF.
    repeat split; lia. }
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W') mem')) by constructor.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr SEGS Wx (mkCfg (mkst regs' (Z_to_bv 64 (decodeb_val A_TEXT + 0x3a0)) mem' (seg_rom SEGS)) md') Q) end.
assert (AG : forall n, (n < 512)%nat -> ew E n = ew E n) by reflexivity.
assert (U18 : U E (SOff 18 0) = SHADOW_OFF)
  by (apply U_atom; [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | unfold SHADOW_OFF; lia]).
assert (U22 : U E (SOff 22 0) = mode + 8) by (apply U_atom; [rewrite (EE 22%nat 22%bv eq_refl); exact R22 | lia]).
assert (U23 : U E (SOff 23 0) = mode + 4) by (apply U_atom; [rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia]).
paj_run_tok RUN HS HJ SHOK Bspan;
  [ rewrite U18, U22; exact (cp_ra_sub _ _ _ _ (mode + 8) 4 HMA ltac:(lia) ltac:(lia))
  | rewrite U18, U23; exact (cp_ra_sub _ _ _ _ (mode + 4) 4 HMA ltac:(lia) ltac:(lia))
  | cp_awrD cx Ub9
  | ].
cp_env HS AG.
(* the two field atoms and the kept registers, at any later environment of this stage *)
assert (HU2 : forall Ex, (forall n, (n < 512)%nat -> ew Ex n = ew E n) ->
  U Ex (SOff 32 0) = nch mod 2 ^ 32 /\ U Ex (SOff 33 0) = ns mod 2 ^ 32).
{ intros Ex HA. pose proof (Z.mod_pos_bound nch (2 ^ 32) ltac:(lia)). pose proof (Z.mod_pos_bound ns (2 ^ 32) ltac:(lia)).
  split; apply U_atom; [rewrite (HA 32%nat ltac:(lia)); exact E32 | lia | rewrite (HA 33%nat ltac:(lia)); exact E33 | lia]. }
assert (HK2 : forall Ex (r : bv 5) (k : nat), (forall n, (n < 512)%nat -> ew Ex n = ew E n) ->
  Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> sv_denot Ex (SOff k 0) = YK11.getr regs' r).
{ intros Ex r k HA Hk Hk32. cbn [sv_denot]. rewrite (HA k ltac:(lia)), (EE k r Hk), Z.add_0_r, Z_to_bv_bv_unsigned.
  reflexivity. }
assert (HB9 : forall Ex, (forall n, (n < 512)%nat -> ew Ex n = ew E n) -> bv_unsigned (ew Ex 9) = d_sp1 cx)
  by (intros Ex HA; rewrite (HA 9%nat ltac:(lia)); exact Ub9).
assert (Hpos : 0 <= nch mod 2 ^ 32 < 2 ^ 32 /\ 0 <= ns mod 2 ^ 32 < 2 ^ 32)
  by (split; apply Z.mod_pos_bound; lia).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* both fields positive: +0x400, s10 = 3 * nch * ns *)
  rewrite branch_ne_U, U_lit in Hc by lia. fold cp_a3 cp_a2 cp_s7 cp_fit in Hc.
  lazymatch type of Hc with context [U ?Ex cp_fit] => destruct (HU2 Ex AG) as (HU32 & HU33) end.
  rewrite (cp_Ufit _ nch ns HU32 HU33 Hnch Hns) in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hfit : 0 < nch /\ 0 < ns).
  { unfold dec_b_fits0 in Hc. destruct (Z.ltb_spec 0 nch); destruct (Z.ltb_spec 0 ns); cbn in Hc; first [lia | congruence]. }
  clear HU32 HU33.
  paj_run_tok RUN HS HJ SHOK Bspan; [cp_awrD cx Ub9 |].
  cp_env HS AG.
  lazymatch type of HS with st_ok _ ?Ex _ _ => destruct (HU2 Ex AG) as (HU32 & HU33); pose proof (HB9 Ex AG) as U9c end.
  repeat rewrite wvb_collapse in HJ.
  cp_reg HS (1%bv : bv 5) (w64 (DEC_A_LLVMF + 0x418)) G1 ltac:(apply (codeptr_val (PI := PIB)); assumption).
  cp_reg HS (10%bv : bv 5) (w64 (dec_b_olen nch ns)) G10
    ltac:(apply cp_denot_w64; fold cp_a3 cp_a2 cp_zns cp_prod cp_x3 cp_s10;
          rewrite U_SAlu, U_SLit, (cp_Us10 _ nch ns HU32 HU33 ltac:(lia) ltac:(lia)); cbn [zalu_raw];
          change (zcanon 0) with 0; rewrite Z.add_0_r; reflexivity).
  cp_reg HS (26%bv : bv 5) (w64 (dec_b_olen nch ns)) G26
    ltac:(apply cp_denot_w64; fold cp_a3 cp_a2 cp_zns cp_prod cp_x3 cp_s10;
          rewrite (cp_Us10 _ nch ns HU32 HU33 ltac:(lia) ltac:(lia)); symmetry; apply Z.mod_small;
          unfold dec_b_olen; destruct (_ && _); nia).
  cp_reg HS (22%bv : bv 5) (w64 (dec_b_prod nch ns)) G22
    ltac:(apply cp_denot_w64; fold cp_a3 cp_a2 cp_zns cp_prod; rewrite (cp_Uprod _ nch ns HU32 HU33 Hns);
          unfold dec_b_prod; symmetry; apply Z.mod_mod; lia).
  cp_reg HS (23%bv : bv 5) (w64 nch) G23
    ltac:(apply cp_denot_w64; fold cp_a3 cp_s7; rewrite (cp_Us7 _ nch HU32 Hnch); reflexivity).
  cp_reg HS (24%bv : bv 5) (w64 (dec_b_fits0 nch ns)) G24
    ltac:(apply cp_denot_w64; fold cp_a3 cp_a2 cp_s7 cp_fit; rewrite (cp_Ufit _ nch ns HU32 HU33 Hnch Hns);
          unfold dec_b_fits0; destruct (_ && _); reflexivity).
  cp_reg HS (2%bv : bv 5) (YK11.getr regs' 2) K2 ltac:(exact (HK2 _ 2%bv 2%nat AG eq_refl ltac:(lia))).
  cp_reg HS (3%bv : bv 5) (YK11.getr regs' 3) K3 ltac:(exact (HK2 _ 3%bv 3%nat AG eq_refl ltac:(lia))).
  cp_reg HS (4%bv : bv 5) (YK11.getr regs' 4) K4 ltac:(exact (HK2 _ 4%bv 4%nat AG eq_refl ltac:(lia))).
  cp_reg HS (8%bv : bv 5) (YK11.getr regs' 8) K8 ltac:(exact (HK2 _ 8%bv 8%nat AG eq_refl ltac:(lia))).
  cp_reg HS (9%bv : bv 5) (YK11.getr regs' 9) K9 ltac:(exact (HK2 _ 9%bv 9%nat AG eq_refl ltac:(lia))).
  cp_reg HS (18%bv : bv 5) (YK11.getr regs' 18) K18 ltac:(exact (HK2 _ 18%bv 18%nat AG eq_refl ltac:(lia))).
  cp_reg HS (20%bv : bv 5) (YK11.getr regs' 20) K20 ltac:(exact (HK2 _ 20%bv 20%nat AG eq_refl ltac:(lia))).
  cp_reg HS (21%bv : bv 5) (YK11.getr regs' 21) K21 ltac:(exact (HK2 _ 21%bv 21%nat AG eq_refl ltac:(lia))).
  cp_reg HS (27%bv : bv 5) (YK11.getr regs' 27) K27 ltac:(exact (HK2 _ 27%bv 27%nat AG eq_refl ltac:(lia))).
  pose proof (st_ok_region_nth _ _ _ 2 _ HS eq_refl) as HR. cbn [restrict ms_mem] in HR.
  pose proof (field_of_region _ _ 9 (d_sp1 cx) _ _ _ _ _ 32 8 (SOff 18 0) SHADOW_OFF HR U9c ltac:(cbn; auto 10)
    ltac:(rewrite (HK2 _ 18%bv 18%nat AG eq_refl ltac:(lia)); exact R18) ltac:(unfold SHADOW_OFF; cbn; lia)
    ltac:(cbn; lia)) as S32.
  pose proof (field_of_region _ _ 9 (d_sp1 cx) _ _ _ _ _ 56 8 cp_zns (ns mod 2 ^ 32) HR U9c ltac:(cbn; auto 10)
    ltac:(apply cp_denot_w64; rewrite (cp_Uzns _ ns HU33 Hns); symmetry; apply Z.mod_small; lia) ltac:(cbn; lia)
    ltac:(cbn; lia)) as S56.
  pose proof (field_of_region _ _ 9 (d_sp1 cx) _ _ _ _ _ 64 8 cp_a3 (nch mod 2 ^ 32) HR U9c ltac:(cbn; auto 10)
    ltac:(apply cp_denot_w64; rewrite (cp_Ua3 _ nch HU32); symmetry; apply Z.mod_small; lia) ltac:(cbn; lia)
    ltac:(cbn; lia)) as S64.
  pose proof (field_of_region _ _ 9 (d_sp1 cx) _ _ _ _ _ 72 8 cp_a2 (ns mod 2 ^ 64) HR U9c ltac:(cbn; auto 10)
    ltac:(apply cp_denot_w64; rewrite (cp_Ua2 _ ns HU33 Hns); symmetry; apply Z.mod_mod; lia)
    ltac:(pose proof (Z.mod_pos_bound ns (2 ^ 64) ltac:(lia)); cbn; lia) ltac:(cbn; lia)) as S72.
  cp_keep_of cx Ub9 HFr K0. cp_keep_of cx Ub9 HFr0 K1.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx + 32 <= a < d_sp1 cx + 80) ->
    aview segs (w_H W') (ms_mem ms0) a = aview segs (w_H W') mem' a)
    by (intros a Ha Hn; etransitivity; [exact (K1 a Ha Hn) | exact (K0 a Ha Hn)]).
  clear K0 K1.
  assert (PRES : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem ms0) a)
    by (intros a Hp; apply (apresent_grows _ _ _ _ HG0); apply (apresent_grows _ _ _ _ HG); exact Hp).
  pmkst HS.
  apply SRr_ret.
  lazymatch goal with |- cp_at414 _ _ (mkCfg (mkst ?rgf _ ?mmf _) ?mdf) =>
    exists fx', ly', S', rgf, regs', mmf, mdf, res, mode, nch, ns end.
  split; [reflexivity|]. split; [exact Hfrm|].
  split.
  { apply (cp_base0_kept cx ly' S' W' regs' mem' md' res mode nch ns W' regs' _ _
      (fun a => d_sp1 cx + 32 <= a < d_sp1 cx + 80) LAWS HC RC Hnl HB0 HJ).
    - intros r _ _. reflexivity.
    - exact KEEP.
    - exact PRES.
    - intros a Ha. exact (cp_kz_spill cx ly' S' W' regs' mem' md' res mode nch ns a LAWS HB0 Ha). }
  split.
  { intros r Hr. cbn in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]];
      first [exact K2 | exact K3 | exact K4 | exact K8 | exact K9 | exact K18 | exact K20 | exact K21 | exact K27]. }
  split; [exact R27|]. split; [exact G1|]. split; [exact G10|]. split; [exact G22|]. split; [exact G23|].
  split; [exact G24|]. split; [exact G26|].
  split.
  { eapply cp_garr8_kept; [|exact Hgr]. intros j Hj. rewrite length_map in Hj. apply KEEP; lia. }
  split; [apply cp_rdword_of_val_mem; [exact S32 | unfold SHADOW_OFF; lia]|].
  split; [apply cp_rdword_of_val_mem; [exact S56 | lia]|].
  split; [apply cp_rdword_of_val_mem; [exact S64 | lia]|].
  apply cp_rdword_of_val_mem; [exact S72 | apply Z.mod_pos_bound; lia].
- (* a field <= 0: +0x3f8, s10 = 1 *)
  rewrite branch_ne_U, U_lit in Hc by lia. fold cp_a3 cp_a2 cp_s7 cp_fit in Hc.
  lazymatch type of Hc with context [U ?Ex cp_fit] => destruct (HU2 Ex AG) as (HU32 & HU33) end.
  rewrite (cp_Ufit _ nch ns HU32 HU33 Hnch Hns) in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hol1 : dec_b_olen nch ns = 1).
  { unfold dec_b_fits0, dec_b_olen in *. destruct (_ && _); [discriminate | reflexivity]. }
  clear HU32 HU33.
  paj_run_tok RUN HS HJ SHOK Bspan; [cp_awrD cx Ub9 |].
  cp_env HS AG.
  lazymatch type of HS with st_ok _ ?Ex _ _ => destruct (HU2 Ex AG) as (HU32 & HU33); pose proof (HB9 Ex AG) as U9c end.
  repeat rewrite wvb_collapse in HJ.
  cp_reg HS (1%bv : bv 5) (w64 (DEC_A_LLVMF + 0x418)) G1 ltac:(apply (codeptr_val (PI := PIB)); assumption).
  cp_reg HS (10%bv : bv 5) (w64 (dec_b_olen nch ns)) G10 ltac:(rewrite Hol1; reflexivity).
  cp_reg HS (26%bv : bv 5) (w64 (dec_b_olen nch ns)) G26 ltac:(rewrite Hol1; reflexivity).
  cp_reg HS (22%bv : bv 5) (w64 (dec_b_prod nch ns)) G22
    ltac:(apply cp_denot_w64; fold cp_a3 cp_a2 cp_zns cp_prod; rewrite (cp_Uprod _ nch ns HU32 HU33 Hns);
          unfold dec_b_prod; symmetry; apply Z.mod_mod; lia).
  cp_reg HS (23%bv : bv 5) (w64 nch) G23
    ltac:(apply cp_denot_w64; fold cp_a3 cp_s7; rewrite (cp_Us7 _ nch HU32 Hnch); reflexivity).
  cp_reg HS (24%bv : bv 5) (w64 (dec_b_fits0 nch ns)) G24
    ltac:(apply cp_denot_w64; fold cp_a3 cp_a2 cp_s7 cp_fit; rewrite (cp_Ufit _ nch ns HU32 HU33 Hnch Hns);
          unfold dec_b_fits0; destruct (_ && _); reflexivity).
  cp_reg HS (2%bv : bv 5) (YK11.getr regs' 2) K2 ltac:(exact (HK2 _ 2%bv 2%nat AG eq_refl ltac:(lia))).
  cp_reg HS (3%bv : bv 5) (YK11.getr regs' 3) K3 ltac:(exact (HK2 _ 3%bv 3%nat AG eq_refl ltac:(lia))).
  cp_reg HS (4%bv : bv 5) (YK11.getr regs' 4) K4 ltac:(exact (HK2 _ 4%bv 4%nat AG eq_refl ltac:(lia))).
  cp_reg HS (8%bv : bv 5) (YK11.getr regs' 8) K8 ltac:(exact (HK2 _ 8%bv 8%nat AG eq_refl ltac:(lia))).
  cp_reg HS (9%bv : bv 5) (YK11.getr regs' 9) K9 ltac:(exact (HK2 _ 9%bv 9%nat AG eq_refl ltac:(lia))).
  cp_reg HS (18%bv : bv 5) (YK11.getr regs' 18) K18 ltac:(exact (HK2 _ 18%bv 18%nat AG eq_refl ltac:(lia))).
  cp_reg HS (20%bv : bv 5) (YK11.getr regs' 20) K20 ltac:(exact (HK2 _ 20%bv 20%nat AG eq_refl ltac:(lia))).
  cp_reg HS (21%bv : bv 5) (YK11.getr regs' 21) K21 ltac:(exact (HK2 _ 21%bv 21%nat AG eq_refl ltac:(lia))).
  cp_reg HS (27%bv : bv 5) (YK11.getr regs' 27) K27 ltac:(exact (HK2 _ 27%bv 27%nat AG eq_refl ltac:(lia))).
  pose proof (st_ok_region_nth _ _ _ 2 _ HS eq_refl) as HR. cbn [restrict ms_mem] in HR.
  pose proof (field_of_region _ _ 9 (d_sp1 cx) _ _ _ _ _ 32 8 (SOff 18 0) SHADOW_OFF HR U9c ltac:(cbn; auto 10)
    ltac:(rewrite (HK2 _ 18%bv 18%nat AG eq_refl ltac:(lia)); exact R18) ltac:(unfold SHADOW_OFF; cbn; lia)
    ltac:(cbn; lia)) as S32.
  pose proof (field_of_region _ _ 9 (d_sp1 cx) _ _ _ _ _ 56 8 cp_zns (ns mod 2 ^ 32) HR U9c ltac:(cbn; auto 10)
    ltac:(apply cp_denot_w64; rewrite (cp_Uzns _ ns HU33 Hns); symmetry; apply Z.mod_small; lia) ltac:(cbn; lia)
    ltac:(cbn; lia)) as S56.
  pose proof (field_of_region _ _ 9 (d_sp1 cx) _ _ _ _ _ 64 8 cp_a3 (nch mod 2 ^ 32) HR U9c ltac:(cbn; auto 10)
    ltac:(apply cp_denot_w64; rewrite (cp_Ua3 _ nch HU32); symmetry; apply Z.mod_small; lia) ltac:(cbn; lia)
    ltac:(cbn; lia)) as S64.
  pose proof (field_of_region _ _ 9 (d_sp1 cx) _ _ _ _ _ 72 8 cp_a2 (ns mod 2 ^ 64) HR U9c ltac:(cbn; auto 10)
    ltac:(apply cp_denot_w64; rewrite (cp_Ua2 _ ns HU33 Hns); symmetry; apply Z.mod_mod; lia)
    ltac:(pose proof (Z.mod_pos_bound ns (2 ^ 64) ltac:(lia)); cbn; lia) ltac:(cbn; lia)) as S72.
  cp_keep_of cx Ub9 HFr K0. cp_keep_of cx Ub9 HFr0 K1.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx + 32 <= a < d_sp1 cx + 80) ->
    aview segs (w_H W') (ms_mem ms0) a = aview segs (w_H W') mem' a)
    by (intros a Ha Hn; etransitivity; [exact (K1 a Ha Hn) | exact (K0 a Ha Hn)]).
  clear K0 K1.
  assert (PRES : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem ms0) a)
    by (intros a Hp; apply (apresent_grows _ _ _ _ HG0); apply (apresent_grows _ _ _ _ HG); exact Hp).
  pmkst HS.
  apply SRr_ret.
  lazymatch goal with |- cp_at414 _ _ (mkCfg (mkst ?rgf _ ?mmf _) ?mdf) =>
    exists fx', ly', S', rgf, regs', mmf, mdf, res, mode, nch, ns end.
  split; [reflexivity|]. split; [exact Hfrm|].
  split.
  { apply (cp_base0_kept cx ly' S' W' regs' mem' md' res mode nch ns W' regs' _ _
      (fun a => d_sp1 cx + 32 <= a < d_sp1 cx + 80) LAWS HC RC Hnl HB0 HJ).
    - intros r _ _. reflexivity.
    - exact KEEP.
    - exact PRES.
    - intros a Ha. exact (cp_kz_spill cx ly' S' W' regs' mem' md' res mode nch ns a LAWS HB0 Ha). }
  split.
  { intros r Hr. cbn in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]];
      first [exact K2 | exact K3 | exact K4 | exact K8 | exact K9 | exact K18 | exact K20 | exact K21 | exact K27]. }
  split; [exact R27|]. split; [exact G1|]. split; [exact G10|]. split; [exact G22|]. split; [exact G23|].
  split; [exact G24|]. split; [exact G26|].
  split.
  { eapply cp_garr8_kept; [|exact Hgr]. intros j Hj. rewrite length_map in Hj. apply KEEP; lia. }
  split; [apply cp_rdword_of_val_mem; [exact S32 | unfold SHADOW_OFF; lia]|].
  split; [apply cp_rdword_of_val_mem; [exact S56 | lia]|].
  split; [apply cp_rdword_of_val_mem; [exact S64 | lia]|].
  apply cp_rdword_of_val_mem; [exact S72 | apply Z.mod_pos_bound; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 9. The leaf calls: reac_frame_is_reac (+0x2a4, +0x30c) and            *)
(*    reac_frame_clean_len (+0x31c)                                      *)
(* ------------------------------------------------------------------ *)

(* The two leaves' call steps, after LLVMFuzzerTestOneInput_leafb.v's dec_leafb_inspect (its shape, at
   reac_frame_is_reac's and reac_frame_clean_len's statements, lib/B/Prog/reac_frame_is_reac_cg.v and
   reac_frame_clean_len_cg.v), through the shared bridge's dec_leafb_journal. *)
Lemma cp_leaf_is_reac : forall (fx : YK11.FPState),
  dec_crt_cells B -> AR_laws segs B ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LIsReac.dec_reac_frame_is_reac_cg) fx') ->
  forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
         (o raw len : Z) (bs : list byte),
  @ajournal rc dec_B_sink_head segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (YK11.getr regsT 1) -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 10 = w64 raw -> YK11.getr regsT 11 = w64 len -> 0 <= raw < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  (raw <> 0 -> 14 <= len -> In (raw, len) (ablocks B lyc Sc) /\ Z.of_nat (length bs) = len /\
     garr8 segs (rd W memT) raw (map (fun b : byte => bv_unsigned b) bs)) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 reac_frame_is_reac_c.REAC_FRAME_IS_REAC) memT
                       (YK11.seg_rom segs)) mdc)
    (dec_leafb_ret (fx := fx) (SK := dec_B_sink_head) B STK sp0 FP ly S W0 mem md own lyc Sc W memT k regsT
       (reac_frame_is_reac_c.is_reac_result raw len bs) [] (fun _ => True)).
Proof.
intros fx HC LAWS HLEAF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw len bs
  HJ Hsp Hal Hneg Hbud Hra Hgp Htp H10 H11 Hraw Hlen HB.
pose proof (dec_leafb_frame_bounds B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o
  HJ Hsp Hneg Hbud) as (Hsp1 & Hsp2 & Hsp3 & Hsp4).
pose proof (proj1 HJ) as HAR.
assert (HspL : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp0 + o) by exact Hsp.
assert (Hsp1L : alloc_ceiling + ESTACK <= bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) by exact Hsp1.
assert (Hsp2L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) <= sp0) by exact Hsp2.
pose proof alloc_ceiling_val as HCEIL.
unfold ESTACK in Hsp1L, Hsp4.
assert (Ha1 : bv_unsigned (YK11.getr regsT 11) = len) by (rewrite H11; unfold w64; apply unsigned_lit_small; lia).
assert (Ha0 : bv_unsigned (YK11.getr regsT 10) = raw) by (rewrite H10; unfold w64; apply unsigned_lit_small; lia).
assert (Ha1L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 11)) = len) by exact Ha1.
assert (Ha0L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 10)) = raw) by exact Ha0.
eapply SRr_mono;
  [ eapply (dec_leafb_journal B LAWS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o
              reac_frame_is_reac_c.REAC_FRAME_IS_REAC (Some (reac_frame_is_reac_c.is_reac_result raw len bs)) []
              (fun _ => True) HJ Hsp Hal Hneg Hbud Hra Hgp Htp)
  | cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & Hp2 & Hres2 & Heff2 & Hgr2 & _);
    split; [reflexivity|]; exists regs2, mem2, md2;
    split; [exact Hc2|]; split; [exact HJ2|]; split; [exact Hp2|];
    split; [exact (Hres2 _ eq_refl)|]; split; [exact Heff2|]; split; [exact Hgr2 | exact I] ].
- intros a Ha. inversion Ha.
- intros HPRE. rewrite <- Ha0L, <- Ha1L.
  refine (HLEAF fx lyc Sc W regsT memT mdc bs (sp0 - STK) HPRE _ _ _ _ _).
  + exact (dec_leafb_stk_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k (sp0 - STK)
             (spZ regsT) HJ ltac:(lia) ltac:(lia)).
  + unfold reac_frame_is_reac_c.REAC_FRAME_IS_REAC_FRAME. lia.
  + rewrite Ha0L, Ha1L. intros Hr0 H14.
    destruct (HB Hr0 H14) as (Hin & Hbl & HG).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ raw len HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & _).
    pose proof (req_size_pos len ltac:(lia)) as [Hq1 Hq2].
    split; [lia|].
    split; [apply (dec_leafb_bytes_garr8 W memT raw bs HG); lia|].
    split; [unfold BKA.off_stk, reac_frame_is_reac_c.REAC_FRAME_IS_REAC_FRAME; left; lia|].
    split; [apply dec_leafb_app_stack; unfold reac_frame_is_reac_c.REAC_FRAME_IS_REAC_FRAME; lia|].
    split; [apply dec_leafb_app_stack; lia|].
    split; [exact (dec_leafb_asan_cells B HC lyc Sc W memT mdc HAR)|].
    split; [unfold BKA.off_stk, reac_frame_is_reac_c.REAC_FRAME_IS_REAC_FRAME, BCells.GOT_CELL_K; left; lia|].
    split; [unfold BKA.off_stk, reac_frame_is_reac_c.REAC_FRAME_IS_REAC_FRAME, BCells.CELL_K; left; lia|].
    exact (dec_leafb_addressable_block B LAWS lyc Sc W memT mdc raw len (raw + 12) 2 HAR Hin
             ltac:(lia) ltac:(lia) ltac:(lia)).
  + apply (dec_leafb_rng_journal (SK := dec_B_sink_head) B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k);
      [exact HJ | unfold reac_frame_is_reac_c.REAC_FRAME_IS_REAC_FRAME; lia
       | unfold reac_frame_is_reac_c.REAC_FRAME_IS_REAC_FRAME; lia].
  + rewrite Ha0L, Ha1L. intros Hr0 H14.
    destruct (HB Hr0 H14) as (Hin & Hbl & HG).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ raw len HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & _).
    pose proof (req_size_pos len ltac:(lia)) as [Hq1 Hq2].
    split; [exact (proj1 (dec_leafb_rng_cells W))|].
    split; [exact (proj2 (dec_leafb_rng_cells W))|].
    split; [exact (dec_leafb_rng_block B LAWS lyc Sc W memT mdc raw len (raw + 12) 2 HAR Hin ltac:(lia) ltac:(lia))|].
    pose proof (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc raw len (raw + 12) 2 HAR Hin
      ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
    unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
    replace ((raw + 12 + 2 - 1) / 8 + 2147450880 - ((raw + 12) / 8 + 2147450880) + 1)
      with ((raw + 12 + 2 - 1) / 8 - (raw + 12) / 8 + 1) in HS by lia.
    exact HS.
Qed.

Lemma cp_rom_kt : rdword (fun x => option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 x))) 0x103c8
  = Some reac_frame_clean_len_c.KT.
Proof. vm_compute. reflexivity. Qed.

Lemma cp_leaf_clean_len : forall (fx : YK11.FPState),
  AR_laws segs B ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LCleanLen.dec_reac_frame_clean_len_cg) fx') ->
  forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o v : Z),
  @ajournal rc dec_B_sink_head segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (YK11.getr regsT 1) -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 10 = w64 v -> 0 <= v < 2 ^ 64 ->
  dec_rom_view_rd W memT ->
  SRr segs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 reac_frame_clean_len_c.REAC_FRAME_CLEAN_LEN) memT
                       (YK11.seg_rom segs)) mdc)
    (dec_leafb_ret (fx := fx) (SK := dec_B_sink_head) B STK sp0 FP ly S W0 mem md own lyc Sc W memT k regsT
       (reac_frame_clean_len_c.reac_frame_clean_len_model v) [] (fun m2 => m2 = memT)).
Proof.
intros fx LAWS HLEAF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o v
  HJ Hsp Hal Hneg Hbud Hra Hgp Htp H10 Hv HRV.
assert (Ha0 : bv_unsigned (YK11.getr regsT 10) = v) by (rewrite H10; unfold w64; apply unsigned_lit_small; lia).
assert (Ha0L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 10)) = v) by exact Ha0.
assert (VM : val_mem segs (rd W memT) 0x10310 8 CP_KM).
{ apply (cp_rom_word W memT 0x10310 CP_KM HRV); [|exact cp_rom_km].
  intros i Hi. apply (cp_in_ro_rd _ 8); [cbn; auto | lia]. }
assert (VT : val_mem segs (rd W memT) 0x103c8 8 reac_frame_clean_len_c.KT).
{ apply (cp_rom_word W memT 0x103c8 _ HRV); [|exact cp_rom_kt].
  intros i Hi. apply (cp_in_ro_rd _ 8); [cbn; auto 10 | lia]. }
assert (VIS : forall a n v', val_mem segs (rd W memT) a n v' -> forall x, a <= x < a + Z.of_nat n ->
  w_H W (Z_to_bv 64 x) = false).
{ intros a n v' HV x Hx. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
  exact (dec_leafb_mbyte_vis W memT _ _ (HV (Z.to_nat (x - a)) ltac:(lia))). }
eapply SRr_mono;
  [ eapply (dec_leafb_journal B LAWS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o
              reac_frame_clean_len_c.REAC_FRAME_CLEAN_LEN
              (Some (reac_frame_clean_len_c.reac_frame_clean_len_model v)) [] (fun m2 => m2 = memT)
              HJ Hsp Hal Hneg Hbud Hra Hgp Htp)
  | cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & Hp2 & Hres2 & Heff2 & Hgr2 & HX);
    split; [reflexivity|]; exists regs2, mem2, md2;
    split; [exact Hc2|]; split; [exact HJ2|]; split; [exact Hp2|];
    split; [exact (Hres2 _ eq_refl)|]; split; [exact Heff2|]; split; [exact Hgr2 | exact HX] ].
- intros a Ha. inversion Ha.
- intros HPRE. rewrite <- Ha0L.
  refine (HLEAF fx lyc Sc W regsT memT mdc HPRE _ _ _ _).
  + unfold LMem.le8, word_to_le_bytes.
    apply (dec_leafb_bytes_le W memT _ 8 _ CP_KM VM);
      [rewrite Z_to_bv_unsigned; vm_compute; reflexivity | unfold reac_frame_clean_len_c.A_M; lia
       | unfold reac_frame_clean_len_c.A_M; lia].
  + unfold LMem.le8, word_to_le_bytes.
    apply (dec_leafb_bytes_le W memT _ 8 _ reac_frame_clean_len_c.KT VT);
      [rewrite Z_to_bv_unsigned; vm_compute; reflexivity | unfold reac_frame_clean_len_c.A_T; lia
       | unfold reac_frame_clean_len_c.A_T; lia].
  + apply (dec_leafb_rng W); [unfold reac_frame_clean_len_c.A_M; lia | unfold reac_frame_clean_len_c.A_M; lia |].
    intros a Ha. exact (VIS _ 8%nat _ VM a ltac:(unfold reac_frame_clean_len_c.A_M in Ha; cbn; lia)).
  + apply (dec_leafb_rng W); [unfold reac_frame_clean_len_c.A_T; lia | unfold reac_frame_clean_len_c.A_T; lia |].
    intros a Ha. exact (VIS _ 8%nat _ VT a ltac:(unfold reac_frame_clean_len_c.A_T in Ha; cbn; lia)).
Qed.

(* The call steps of the segment: +0x2a4 / +0x30c (cp_P_ir -> cp_Q_ir) and +0x31c (cp_P_cl -> cp_Q_cl). *)
Lemma cp_stage_B_ir : forall rk cx W' c',
  dec_crt_cells B -> cp_romctx cx -> AR_laws segs B ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LIsReac.dec_reac_frame_is_reac_cg) fx') ->
  dec_b_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  (rk = 0x2a8 \/ rk = 0x310) ->
  cp_P_ir rk cx W' c' -> SRr segs W' c' (cp_Q_ir rk cx).
Proof.
intros rk cx W' c' HC RC LAWS HLEAF HBASE Hrk HP.
pose proof HBASE as (HAFN & _ & _ & _ & Hpn & Hnl & _).
assert (Hn0 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hq _]]; lia).
destruct HP as (fx' & ly' & S' & regs' & mem' & md' & res & mode & nch & ns & -> & Hfrm & ((HB0 & R27) & Hgr) & R1 & R10 & R11).
pose proof (cp_core_facts cx ly' S' W' regs' mem' md' _ LAWS (proj1 HB0)) as (Hsp0 & Hsp16 & EF & Hin & HFc & HFa).
pose proof HB0 as (Hcore & Hbl & Hres & _).
pose proof Hcore as (HJ & Hfrms & R8 & R9 & Rsp & Hsp1 & Hsp32 & R3 & R4 & _).
pose proof (cp_len_facts cx ltac:(lia) Hnl) as (L0 & U0 & LU & LB & L3).
assert (Hinr : In (res, len cx) (ablocks B ly' S')) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hrc : res + len cx <= alloc_ceiling).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) Hinr) as (_ & _ & Hc & _).
  pose proof (req_size_pos (len cx) L0). lia. }
set (l1 := if rk =? 0x2a8 then len cx else 0) in *.
assert (Hl1 : 0 <= l1 <= len cx) by (unfold l1; destruct (rk =? 0x2a8); lia).
assert (Ho16 : (d_sp1 cx - d_sp0 cx) mod 16 = 0).
{ rewrite Zminus_mod, Hsp16.
  assert (H16 : d_sp1 cx mod 16 = 0).
  { pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D. rewrite D.
    replace (32 * (d_sp1 cx / 32)) with ((2 * (d_sp1 cx / 32)) * 16) by lia. apply Z_mod_mult. }
  rewrite H16. reflexivity. }
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
eapply SRr_mono.
{ apply (cp_leaf_is_reac fx' HC LAWS HLEAF W' regs' mem' DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx)
    (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' md' dec_ev_27c (d_sp1 cx - d_sp0 cx) res l1 (d_body cx) HJ).
  - rewrite <- Rsp. lia.
  - exact Ho16.
  - lia.
  - unfold ESTACK, DEC_LLVMF_STK. lia.
  - rewrite R1. destruct Hrk as [-> | ->]; apply (ret_ok_codeptr_v (PI := PIB)); first [lia | reflexivity].
  - exact R3.
  - exact R4.
  - exact R10.
  - exact R11.
  - lia.
  - lia.
  - intros _ H14. unfold l1 in *. destruct (Z.eqb_spec rk 0x2a8); [|lia].
    split; [exact Hinr|]. split; [exact LB | exact Hgr]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres2 & Heff2 & Hgr2 & _).
exists fx', ly', S', regs2, mem2, md2, res, mode, nch, ns.
split; [rewrite R1; reflexivity|]. split; [exact Hfrm|].
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - ESTACK <= a < d_sp1 cx) ->
  aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a).
{ intros a Ha Hn. apply Heff2; [exact Ha | rewrite Rsp; exact Hn | intros Hw; inversion Hw]. }
split; [split|].
- apply (cp_base_kept cx ly' S' W' regs' mem' md' res mode nch ns W' regs2 mem2 md2
    (fun a => d_sp1 cx - ESTACK <= a < d_sp1 cx) LAWS HC RC Hnl (conj HB0 R27) HJ2 HP2 KEEP Hgr2).
  intros a Ha. exact (cp_kz_apart cx ly' S' W' regs' mem' md' res mode nch ns a LAWS Hnl ltac:(lia) HB0 (or_intror Ha)).
- eapply cp_garr8_kept; [|exact Hgr]. intros j Hj. rewrite length_map in Hj. apply KEEP; unfold ESTACK; lia.
- exact Hres2.
Qed.

Lemma cp_stage_B_cl : forall cx W' c',
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B -> AR_laws segs B ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LCleanLen.dec_reac_frame_clean_len_cg) fx') ->
  dec_b_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_b_rom cx ->
  cp_P_cl cx W' c' -> SRr segs W' c' (cp_Q_cl cx).
Proof.
intros cx W' c' HC HO HE LAWS HLEAF HBASE HROMc HP.
assert (RC : cp_romctx cx) by exact (conj HO (conj HE HROMc)).
pose proof HBASE as (HAFN & _ & _ & _ & Hpn & Hnl & _).
assert (Hn0 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hq _]]; lia).
destruct HP as (fx' & ly' & S' & regs' & mem' & md' & res & mode & nch & ns & -> & Hfrm & ((HB0 & R27) & Hgr) & R1 & R10).
pose proof (cp_core_facts cx ly' S' W' regs' mem' md' _ LAWS (proj1 HB0)) as (Hsp0 & Hsp16 & EF & Hin & HFc & HFa).
pose proof HB0 as (Hcore & _).
pose proof Hcore as (HJ & Hfrms & R8 & R9 & Rsp & Hsp1 & Hsp32 & R3 & R4 & _).
pose proof (cp_len_facts cx ltac:(lia) Hnl) as (L0 & U0 & LU & LB & L3).
assert (Ho16 : (d_sp1 cx - d_sp0 cx) mod 16 = 0).
{ rewrite Zminus_mod, Hsp16.
  assert (H16 : d_sp1 cx mod 16 = 0).
  { pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D. rewrite D.
    replace (32 * (d_sp1 cx / 32)) with ((2 * (d_sp1 cx / 32)) * 16) by lia. apply Z_mod_mult. }
  rewrite H16. reflexivity. }
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
eapply SRr_mono.
{ apply (cp_leaf_clean_len fx' LAWS HLEAF W' regs' mem' DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx)
    (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' md' dec_ev_27c (d_sp1 cx - d_sp0 cx) (len cx) HJ).
  - rewrite <- Rsp. lia.
  - exact Ho16.
  - lia.
  - unfold ESTACK, DEC_LLVMF_STK. lia.
  - rewrite R1. apply (ret_ok_codeptr_v (PI := PIB)); [lia | reflexivity].
  - exact R3.
  - exact R4.
  - exact R10.
  - lia.
  - exact (cp_rom_view_rd cx ly' S' W' mem' md' _ HO HE HROMc HJ). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres2 & Heff2 & Hgr2 & ->).
exists fx', ly', S', regs2, mem', md2, res, mode, nch, ns.
split; [rewrite R1; reflexivity|]. split; [exact Hfrm|].
split; [split|].
- apply (cp_base_kept cx ly' S' W' regs' mem' md' res mode nch ns W' regs2 mem' md2 (fun _ => False)
    LAWS HC RC Hnl (conj HB0 R27) HJ2 HP2).
  + intros a _ _. reflexivity.
  + intros a Ha. exact Ha.
  + intros a [].
- exact Hgr.
- exact Hres2.
Qed.

(* ------------------------------------------------------------------ *)
(* 10. malloc #2 (+0x414) to llvm_b_st_418                               *)
(* ------------------------------------------------------------------ *)

Lemma cp_rest_418_nonneg : ameter_laws MT -> 0 <= dec_rest_418 MT.
Proof.
intros ML. unfold dec_rest_418, dec_rest_5cc, dec_rest_6f0, dec_rest_840, dec_rest_96c, dec_crt_cost_max.
pose proof (mo_free_nonneg MT ML).
pose proof (mo_malloc_nonneg MT ML 48387 ltac:(lia)). pose proof (mo_malloc_nonneg MT ML 1920 ltac:(lia)).
pose proof (mo_malloc_nonneg MT ML 1016 ltac:(lia)). pose proof (mo_malloc_nonneg MT ML 1440 ltac:(lia)).
lia.
Qed.
Lemma cp_olen_range : forall nch ns, -128 <= nch <= 127 -> -128 <= ns <= 127 -> 1 <= dec_b_olen nch ns <= 48387.
Proof. intros nch ns H1 H2. unfold dec_b_olen. destruct (Z.ltb_spec 0 nch); destruct (Z.ltb_spec 0 ns); cbn; nia. Qed.

(* The call step: LLVMFuzzerTestOneInput_segB.v's eb_tail_fx (a working branch 84be2173fcc, its
   malloc #1 step, lines 664-795), at malloc #2: amalloc04_sub, then every fact of llvm_b_st_418 from what the call
   keeps (the stack above sp1, the blocks, the frame and its shadow) and the registers it preserves. *)
Lemma cp_stage_D3 : forall cx W' c',
  pc_wrap_malloc (as_code B) = decodeb_sigma DB___interceptor_trampoline_malloc ->
  dec_llvmf_utraces RA_LLVMF B ->
  dec_crt_cells B -> cp_romctx cx -> AR_laws segs B -> ameter_laws MT ->
  (forall fx : YK11.FPState, @amalloc04_rule fx rc dec_B_sink_head segs B MT) ->
  dec_b_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  cp_at414 cx W' c' -> SRr segs W' c' (llvm_b_st_418 B MT cx).
Proof.
intros cx W' c' HPCM HUTR HC RC LAWS MTL AMALLOC HBASE HQ.
pose proof HBASE as (HPRE & Hra_eq & R10e & R11e & Hpn & Hnl & Hgarr0 & Hfr0 & Hnev & Hlive & _).
pose proof HPRE as (HAR0 & _).
assert (Hn0 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hq _]]; lia).
destruct HQ as (fx' & ly' & S' & regs' & regsK & mem' & md' & res & mode & nch & ns & -> & Hfrm & HB0 & GK & R27
  & G1 & G10 & G22 & G23 & G24 & G26 & Hgr & S32 & S56 & S64 & S72).
pose proof (cp_core_facts cx ly' S' W' regsK mem' md' _ LAWS (proj1 HB0)) as (Hsp0 & Hsp16 & EF & Hin & HFc & HFa).
pose proof HB0 as (Hcore & Hbl & Hres & Hmle & Hmok & Hfrs & R18 & R20 & R21 & R22 & R23 & Hmode & Hwhere & Hfsh & H112).
pose proof Hcore as (HJ & Hfrms & R8 & R9 & Rsp & Hsp1 & Hsp32 & R3 & R4 & Hsaved & HF4096 & HF32 & HFpres & HFL & Hpay
  & Hgarr).
pose proof (cp_len_facts cx ltac:(lia) Hnl) as (L0 & U0 & LU & LB & L3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hmode as (Hsel & Hnch & Hns & V4 & V8).
pose proof (cp_olen_range nch ns Hnch Hns) as Hol.
set (olen := dec_b_olen nch ns) in *.
assert (Hinr : In (res, len cx) (ablocks B ly' S')) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Q2 : YK11.getr regs' 2 = YK11.getr regsK 2) by exact (GK 2 ltac:(cbn; tauto)).
assert (Q3 : YK11.getr regs' 3 = w64 (as_gp B)) by (rewrite <- R3; exact (GK 3 ltac:(cbn; tauto))).
assert (Q4 : YK11.getr regs' 4 = w64 (as_tp B)) by (rewrite <- R4; exact (GK 4 ltac:(cbn; tauto))).
assert (HspT : spZ regs' = d_sp1 cx) by (unfold spZ in *; rewrite Q2; exact Rsp).
assert (Hs0T : s0Z regs' = d_sp0 cx).
{ unfold s0Z. transitivity (bv_unsigned (w64 (d_sp0 cx))).
  - f_equal. rewrite <- R8. exact (GK 8 ltac:(cbn; tauto)).
  - unfold w64. apply unsigned_lit_small. lia. }
assert (HraT : raZ regs' = DEC_A_LLVMF + 0x418) by (unfold raZ; rewrite G1; vm_compute; reflexivity).
rewrite <- HPCM.
assert (HnevS : st_nev S' < EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hn' & _). unfold DEC_EV_LIB, dec_ev_27c in *. lia. }
assert (Hbb : blocks_bytes S' = blocks_bytes (d_S cx) + len cx).
{ rewrite (blocks_bytes_bsum B ly' S'), (blocks_bytes_bsum B (d_ly cx) (d_S cx)), Hbl, bsum_app. cbn. lia. }
pose proof (cp_rest_418_nonneg MTL) as Hr418.
pose proof (mo_malloc_mono MT MTL olen 48387 ltac:(lia)) as Hmono.
pose proof (mo_malloc_nonneg MT MTL olen ltac:(lia)) as Hmon0.
assert (Ho16 : (d_sp1 cx - d_sp0 cx) mod 16 = 0).
{ rewrite Zminus_mod, Hsp16.
  assert (H16 : d_sp1 cx mod 16 = 0).
  { pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D. rewrite Hsp32, Z.add_0_r in D. rewrite D.
    replace (32 * (d_sp1 cx / 32)) with ((2 * (d_sp1 cx / 32)) * 16) by lia. apply Z_mod_mult. }
  rewrite H16. reflexivity. }
eapply SRr_mono.
{ eapply (amalloc04_sub (SK := dec_B_sink_head) segs B LAWS (@pa_segs_low rc decodeb_listing PIB) MT (AMALLOC fx') W'
    regs' mem' DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly' S' md' dec_ev_27c olen (d_sp1 cx - d_sp0 cx) (YK11.getr regs' 1)
    (cp_ch cx) HJ G10).
  - unfold MALLOC_MAX. lia.
  - rewrite Hbb. unfold DEC_LIVE_LIB, LIVE_MAX in *. lia.
  - rewrite HspT. lia.
  - exact Ho16.
  - lia.
  - unfold ASTACK, DEC_LLVMF_STK. lia.
  - exact Q3.
  - exact Q4.
  - reflexivity.
  - rewrite G1. apply (ret_ok_codeptr_v (PI := PIB)); [lia | reflexivity].
  - exact HnevS.
  - apply (cp_chain_at cx ly' S' W' mem' md' dec_ev_27c regs' HBASE HJ Hsaved HspT Hs0T); [|lia].
    rewrite HraT. unfold DEC_A_LLVMF, decodeb_text, AF_LLVMFuzzerTestOneInput. lia.
  - exact (cp_trace_at cx regs' HBASE HUTR HraT).
  - apply (mo_ok_le MT MTL S' _ _ Hmok). unfold dec_rest_27c. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & out & -> & HJ2 & HP2 & Hout & Hfr2 & Hout4096 & Hbl2 & HK & MLE
  & HJm).
replace (d_sp0 cx + (d_sp1 cx - d_sp0 cx) - ASTACK) with (d_sp1 cx - ASTACK) in HK by lia.
replace (d_sp0 cx + (d_sp1 cx - d_sp0 cx)) with (d_sp1 cx) in HK by lia.
change (dec_ev_27c + 1) with dec_ev_418 in HJ2.
pose proof HK as (HK1 & HK2 & HK3 & HK4 & HK5 & HK6).
pose proof HJ2 as (HAR2 & Hly2 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR0 Hly2) as (_ & Efa2 & _).
assert (HfaS2 : frame_addr ly2 DEC_FCLASS (d_fpos cx) = d_F cx) by (rewrite Efa2; reflexivity).
assert (Hfb : fs_frame_bytes DEC_FCLASS = 64) by (vm_compute; reflexivity).
assert (Hfin2 : In (DEC_FCLASS, d_fpos cx) (frames S2)) by (rewrite Hfr2; exact Hin).
assert (Hrin2 : In (res, len cx) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact Hinr).
assert (Hoin2 : In (out, olen) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
pose proof (req_size_pos olen ltac:(lia)) as (Hoq1 & Hoq2).
pose proof (req_size_pos (len cx) L0) as (Hrq1 & Hrq2).
assert (Hnew : ~ In (out, olen) (ablocks B ly' S')).
{ intros Hin0. apply in_split in Hin0 as (l1 & l2 & El).
  pose proof (sep_blocks_pos segs B LAWS _ _ _ _ _ (out, olen) (out, olen) l1 l2 [] HAR2) as Hd.
  rewrite Hbl2, El, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hoin2) as (_ & Ho4096 & Hoceil & Hoapp & _).
pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR2 Hoin2 Hfin2) as HdF.
unfold zdisjoint in HdF. cbn [fst snd] in HdF. rewrite HfaS2, Hfb in HdF.
assert (HSH : SHADOW_OFF <= d_SH cx /\ d_SH cx + 8 <= kHighShadowEnd).
{ unfold d_SH, shadow_addr. unfold in_app in HFa. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
(* what the call kept *)
assert (FK : forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a).
{ intros a Ha. apply (HK4 DEC_FCLASS (d_fpos cx) a Hin).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, Hfb. lia.
  - cbv beta. lia. }
assert (FSK : forall a, d_SH cx <= a < d_SH cx + 8 -> aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a).
{ intros a Ha. apply (HK4 DEC_FCLASS (d_fpos cx) a Hin).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF, Hfb. unfold d_SH in Ha. change (64 / 8) with 8. lia.
  - cbv beta. unfold in_app in Hoapp. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
assert (SK : forall a, d_sp1 cx <= a < d_sp0 cx -> aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a).
{ intros a Ha. apply HK1; unfold ASTACK; lia. }
assert (Hne : (res, len cx) <> (out, olen)) by (intros Hq; rewrite Hq in Hinr; exact (Hnew Hinr)).
pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR2 Hrin2 Hoin2 Hne) as Hdro.
unfold zdisjoint in Hdro. cbn [fst snd] in Hdro.
assert (RK : forall i, 0 <= i < len cx -> aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W') mem' (res + i)).
{ intros i Hi. apply (HK2 res (len cx) i Hinr); [lia | cbv beta; lia]. }
assert (PK : forall i, 0 <= i < Z.of_nat (length (map (fun b : byte => bv_unsigned b) (d_pl cx))) ->
  aview segs (w_H W2) mem2 (d_p cx + i) = aview segs (w_H W') mem' (d_p cx + i)).
{ intros i Hi. rewrite length_map, <- Hnl in Hi.
  assert (Hpin1 : In (d_p cx, d_n cx) (ablocks B ly' S')) by (apply Hpay; lia).
  assert (Hpin2 : In (d_p cx, d_n cx) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact Hpin1).
  assert (Hnp : (d_p cx, d_n cx) <> (out, olen)) by (intros Heq; rewrite Heq in Hpin1; exact (Hnew Hpin1)).
  pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR2 Hpin2 Hoin2 Hnp) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  pose proof (req_size_pos (d_n cx) ltac:(lia)) as (_ & Hrqn).
  apply (HK2 (d_p cx) (d_n cx) i Hpin1); [lia | cbv beta; lia]. }
unfold llvm_b_st_418. cbv beta.
exists fx', ly2, S2, regs2, mem2, md2, res, out, mode, nch, ns.
split; [rewrite G1; reflexivity|].
split; [exact Hfrm|].
split.
{ unfold dec_b_core.
  split; [exact HJ2|].
  split; [rewrite Hfr2; exact Hfrms|].
  split; [transitivity (YK11.getr regs' 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | etransitivity; [exact (GK 8 ltac:(cbn; tauto)) | exact R8]]|].
  split; [transitivity (YK11.getr regs' 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | etransitivity; [exact (GK 9 ltac:(cbn; tauto)) | exact R9]]|].
  split; [rewrite <- HspT; unfold spZ; f_equal; exact (HP2 2 ltac:(unfold acallee_saved; lia))|].
  split; [exact Hsp1|]. split; [exact Hsp32|].
  split; [transitivity (YK11.getr regs' 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact Q3]|].
  split; [transitivity (YK11.getr regs' 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact Q4]|].
  split.
  { unfold dec_b_saved in *. rewrite Forall_forall in *. intros o Ho.
    assert (Hfo : 8 <= fst o <= 104).
    { unfold dec_b_saved_at in Ho. cbn in Ho. repeat (destruct Ho as [<- | Ho]; [cbn; lia|]). contradiction. }
    rewrite (cp_rdword_kept (aview segs (w_H W') mem')); [exact (Hsaved o Ho)|]. intros i Hi. apply SK. lia. }
  split; [exact HF4096|]. split; [exact HF32|].
  split; [intros a Ha; destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR2 Hfin2) as (_ & _ & HFp & _);
          rewrite HfaS2, Hfb in HFp; exact (proj1 (HFp a Ha))|].
  split; [rewrite (cp_rdword_kept (aview segs (w_H W') mem')); [exact HFL|]; intros i Hi; apply FK; lia|].
  split; [intros Hn; rewrite Hbl2; apply in_or_app; left; exact (Hpay Hn)|].
  exact (cp_garr8_kept segs _ _ _ _ _ _ PK Hgarr). }
split; [rewrite Hbl2, Hbl, <- app_assoc; reflexivity|].
split; [exact Hres|]. split; [exact Hout4096|].
split; [apply (mo_le_mono MT MTL _ _ (dec_spent_27c MT (d_n cx) + mo_malloc MT olen));
        [exact (mo_le_trans MT MTL _ _ _ _ _ Hmle MLE) | unfold dec_spent_418; lia]|].
split; [apply (mo_ok_step MT MTL S' S2 (mo_malloc MT olen) _);
        [apply (mo_ok_le MT MTL S' _ _ Hmok); unfold dec_rest_27c; lia | exact MLE]|].
split.
{ destruct Hfrs as (F0 & F8 & F16). unfold dec_b_frs, dec_b_slot in *.
  split; [|split]; (rewrite (cp_rdword_kept (aview segs (w_H W') mem')); [assumption | intros i Hi; apply SK; lia]). }
split; [exact Hout|].
split; [transitivity (YK11.getr regs' 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | etransitivity; [exact (GK 18 ltac:(cbn; tauto)) | exact R18]]|].
split; [transitivity (YK11.getr regs' 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | etransitivity; [exact (GK 27 ltac:(cbn; tauto)) | exact R27]]|].
split; [transitivity (YK11.getr regs' 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | etransitivity; [exact (GK 20 ltac:(cbn; tauto)) | exact R20]]|].
split; [transitivity (YK11.getr regs' 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | etransitivity; [exact (GK 21 ltac:(cbn; tauto)) | exact R21]]|].
split; [transitivity (YK11.getr regs' 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact G22]|].
split; [transitivity (YK11.getr regs' 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact G23]|].
split; [transitivity (YK11.getr regs' 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact G24]|].
split; [transitivity (YK11.getr regs' 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact G26]|].
split; [destruct RC as (HO & HE & HR);
        apply (cp_mode_ok_keep cx ly2 S2 W2 mem2 md2 W' mem' mode nch ns HC HAR2
                 (cp_rom_view_rd cx ly2 S2 W2 mem2 md2 _ HO HE HR HJ2) Hwhere Hmode); intros a Ha; apply FK; lia|].
split.
{ destruct Hfsh as (L1 & L4 & L5 & L6). unfold dec_b_fsh.
  split; [|split; [|split]].
  - intros i Hi. rewrite FSK by lia. apply L1. lia.
  - rewrite FSK by lia. exact L4.
  - rewrite FSK by lia. exact L5.
  - intros i Hi. rewrite FSK by lia. apply L6. lia. }
split; [eapply cp_garr8_kept; [|exact Hgr]; intros j Hj; rewrite length_map in Hj; apply RK; lia|].
unfold dec_b_slot in *.
split; [rewrite (cp_rdword_kept (aview segs (w_H W') mem')); [exact S32 | intros i Hi; apply SK; lia]|].
split; [rewrite (cp_rdword_kept (aview segs (w_H W') mem')); [exact S56 | intros i Hi; apply SK; lia]|].
split; [rewrite (cp_rdword_kept (aview segs (w_H W') mem')); [exact S64 | intros i Hi; apply SK; lia]|].
split; [rewrite (cp_rdword_kept (aview segs (w_H W') mem')); [exact S72 | intros i Hi; apply SK; lia]|].
rewrite (cp_rdword_kept (aview segs (w_H W') mem')); [exact H112 | intros i Hi; apply SK; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 11. The segment                                                       *)
(* ------------------------------------------------------------------ *)

(* +0x31c's call to the end: reac_frame_clean_len, the clean-length checks, the mode reads and malloc #2. *)
Lemma cp_tail : forall cx W' c',
  pc_wrap_malloc (as_code B) = decodeb_sigma DB___interceptor_trampoline_malloc ->
  dec_llvmf_utraces RA_LLVMF B ->
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx : YK11.FPState, @amalloc04_rule fx rc dec_B_sink_head segs B MT) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCleanLen.dec_reac_frame_clean_len_cg) fx) ->
  dec_b_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_b_rom cx ->
  cp_P_cl cx W' c' -> SRr segs W' c' (llvm_b_st_418 B MT cx).
Proof.
intros cx W' c' HPCM HUTR HC HO HE LAWS MTL AMALLOC LCL HB HR HP.
eapply SRr_bind; [exact (cp_stage_B_cl cx W' c' HC HO HE LAWS LCL HB HR HP) |].
intros W1 c1 _ HQ.
eapply SRr_bind; [exact (cp_stage_D1 cx W1 c1 HC HO HE LAWS HB HR HQ) |].
intros W2 c2 _ H3a0.
assert (RC : cp_romctx cx) by exact (conj HO (conj HE HR)).
eapply SRr_bind; [exact (cp_stage_D2 cx W2 c2 HC RC LAWS HB H3a0) |].
intros W3 c3 _ H414.
exact (cp_stage_D3 cx W3 c3 HPCM HUTR HC RC LAWS MTL AMALLOC HB H414).
Qed.

Theorem llvm_b_copy_ok :
  llvm_b_copy_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_b_copy_stmt.
intros HPCM HUTR HC HO HE LAWS ML MTL AMEMCPY AMALLOC LIS LCL cx W' c' HB HR H27.
assert (RC : cp_romctx cx) by exact (conj HO (conj HE HR)).
eapply SRr_bind; [exact (cp_stage_A cx W' c' LAWS HC RC AMEMCPY HB H27) |].
intros W1 c1 _ [HP | HP].
- eapply SRr_bind; [exact (cp_stage_B_ir 0x2a8 cx W1 c1 HC RC LAWS LIS HB (or_introl eq_refl) HP) |].
  intros W2 c2 _ HQ.
  eapply SRr_bind; [exact (cp_stage_C2 cx W2 c2 LAWS HC RC HB HQ) |].
  intros W3 c3 _ HP3.
  exact (cp_tail cx W3 c3 HPCM HUTR HC HO HE LAWS MTL AMALLOC LCL HB HR HP3).
- eapply SRr_bind; [exact (cp_stage_B_ir 0x310 cx W1 c1 HC RC LAWS LIS HB (or_intror eq_refl) HP) |].
  intros W2 c2 _ HQ.
  eapply SRr_bind; [exact (cp_stage_C1 cx W2 c2 LAWS HC RC HB HQ) |].
  intros W3 c3 _ HP3.
  exact (cp_tail cx W3 c3 HPCM HUTR HC HO HE LAWS MTL AMALLOC LCL HB HR HP3).
Qed.

End sg.
