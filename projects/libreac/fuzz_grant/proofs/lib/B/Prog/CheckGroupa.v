(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of check_groupa on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v. *)
(* Modified by Theorem Labs, 2026-10: the contract of check_groupa on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACe6.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of check_groupa on image B (fuzz_grant.asan-ubsan, bin fde52226dc48, symbols 5a5ee7c02b4e), over image B's walk layer lib/B/Prog and its contract walk_check_groupa (lib/B/Prog/GrantBContracts.v), with image B's slots, objects, copy length, frame bounds and the B-only trap guard 0x821f4. *)
(* Ported from lib/A/Prog/CheckGroupaWalk.v at a working branch 5aae1e8a0ce (from a working branch 1611e16025b). *)
(* check_groupa (fuzz_grant.c:116, 0x82074 in fuzz_grant.asan-ubsan, BASE + AF_check_groupa = BASE + 0x1638): the
   walk on the position-abstract listing that proves its contract (walk_check_groupa, GrantBContracts.v).

   The function takes a class-2 frame F from the side stack for frames (__asan_stack_malloc_2 at 0x820f0), copies
   the fifty bytes of __const.check_groupa.frame (object 9: T0z ++ repeat 0 34) to F + 32 (__asan_memcpy at
   0x821ec), then the 34-byte row over F + 48 (__asan_memcpy at 0x82208), so F + [32, 82) holds `T0 ++ row`; it
   calls reac_ctrl_parse (0x82230), reac_headamp_tx_effective (0x8225c), reac_ctrl_headamp_record_verify (0x82268)
   and reac_ctrl_checksum_verify (0x82274), sums frame[34..40) itself and compares the parsed value with `want`.
   Every comparison that leads to the abort() path (0x82428) holds by Pau's model facts about the row, so the
   abort() path is not reached; the one trap guard, 0x821f4 (F + 32 >= 2^64 - 16), is false since F < 2^47.
   Differences from image A's walk: the stop and return slots (B's listing), the first copy's length (50, not 16),
   the objects of the shadow-base cell and of the side-stack flag cell (35 and 36, not 32 and 33), ch < 256 (not
   48), the stack bound (STK_check_groupa = 144 + STK_reac_ctrl_parse), reac_ctrl_parse's caller-journal contract
   (twr_ok, tb_live_frames_client, tcj_kept), tx_effective's tx = 0 arm, image B's frame bounds (frm_off_imgB) and
   a journal with an empty footprint in place of the section's ro_below_ofl instance. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YM05.
(* The contracts first, so that the walk layer's names (SB of YC81 above all) are the ones in scope below. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantPaLib YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC81 YC4b YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantFrame YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1i ACbf GrantACjr ACj1 GrantACja GrantRo GrantTop.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel GroupaModel RcModel RcLeaf RcParse.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require ParseLink HeadampLayout.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Module HL := OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.HeadampLayout.
(* Proof speed (an internal proof-speed note): lia case-splits every disjunction and mod fact in the context, so
   four of cg_walk's slowest steps hide them first and show them again right after. Local: nothing exported. *)
Local Definition cg_hold (A : Prop) : Prop := A.
Local Lemma cg_hide : forall A : Prop, A -> cg_hold A. Proof. intros A H. exact H. Qed.
Local Ltac cg_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply cg_hide in H
  | H : _ mod _ = _ |- _ => apply cg_hide in H end.
Local Ltac cg_show_all := repeat match goal with H : cg_hold _ |- _ => unfold cg_hold in H end.
Local Ltac cg_show_disj := repeat match goal with H : cg_hold (_ \/ _) |- _ => unfold cg_hold in H end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* image B's stack bound for the call, as GrantBContracts.v states it: 144 bytes (the 128-byte frame and the 16
   that `andi sp,sp,-32` may drop) over reac_ctrl_parse's, the deepest callee. *)
Notation TCG_STK := STK_check_groupa (only parsing).
Lemma TCG_STK_parse : STK_check_groupa = 144 + STK_reac_ctrl_parse.
Proof. reflexivity. Qed.
Lemma TCG_STK_val : STK_check_groupa = 8480.
Proof. reflexivity. Qed.
Section e.
Variable B : asyms.

(* ---- Pau's model facts about the row, as the walk needs them ---------------------------------- *)
(* The row's bytes are bytes; T0 ++ row is the 50-byte frame `F50` that reac_ctrl_parse reads. *)
Lemma cg_row_bytes : forall ch p v, 0 <= ch < 256 -> 0 <= p < 3 -> 0 <= v < 256 ->
  Forall (fun z => 0 <= z < 256) (T0z ++ GAz ch p v).
Proof.
intros ch p v Hc Hp Hv. apply Forall_app. split; [repeat constructor; lia|].
apply GA_bytes_range; lia.
Qed.
Lemma cg_nth_byte : forall (l : list Z) i, Forall (fun z => 0 <= z < 256) l -> 0 <= nth i l 0 < 256.
Proof.
intros l i H. revert i. induction H as [|x l Hx Hl IH]; intros [|i]; cbn; [lia | lia | exact Hx | apply IH].
Qed.
Lemma cg_cp_v_F50 : forall ch p v i, 0 <= ch < 256 -> 0 <= p < 3 -> 0 <= v < 256 ->
  cp_v (F50 ch p v) i = nth i (T0z ++ GAz ch p v) 0.
Proof.
intros ch p v i Hc Hp Hv. unfold cp_v, cp_b, cp_z, F50, T0, GA, bl. rewrite <- map_app.
change (Z_to_bv 8 0) with (Z_to_bv 8 0 : byte). rewrite map_nth.
apply u8_lit. apply cg_nth_byte. apply cg_row_bytes; assumption.
Qed.
(* The inner record TAG..CKSUM (row bytes 18..23) closes: reac_ctrl_headamp_record_verify returns 0
   (Pau: F50_ga_sum, GroupaModel.v:33). *)
Lemma cg_hv : forall ch p v, 0 <= ch < 256 -> 0 <= p < 3 -> 0 <= v < 256 ->
  hv (Z_to_bv 8 4) (Z_to_bv 8 3) (map (Z_to_bv 8) [1; 1; ch; p; v; ga_r ch p v]) = true.
Proof.
intros ch p v Hc Hp Hv. pose proof (ga_r_range ch p v) as Hr. pose proof (F50_ga_sum ch p v) as HS.
unfold hv, rsum. cbn [map psum nth]. rewrite !u8_lit by lia. cbn [Z.eqb Pos.eqb andb].
replace (0 + 1 + 1 + ch + p + v + ga_r ch p v) with (1 + 1 + ch + p + v + ga_r ch p v) by lia.
rewrite HS. reflexivity.
Qed.
(* The block [2..33] sums to 0 mod 256: reac_ctrl_checksum_verify returns 0 (Pau: GA_sum_block,
   GrantSweepModel.v:100). *)
Lemma cg_blocksum : forall ch p v, 0 <= ch < 256 -> 0 <= p < 3 -> 0 <= v < 256 ->
  blocksum (map (Z_to_bv 8) (skipn 2 (GAz ch p v))) = 0.
Proof.
intros ch p v Hc Hp Hv. pose proof (ga_r_range ch p v). pose proof (ga_c_range ch p v).
pose proof (GA_sum_block ch p v) as HS. unfold sum_from, GAz in HS. cbn [skipn fold_right] in HS.
unfold blocksum, GAz. cbn [skipn map psum nth]. rewrite !u8_lit by lia.
rewrite <- HS. f_equal. lia.
Qed.
(* check_groupa's own sum of frame[34..40) = row[18..24) is 0 mod 128 (Pau: F50_ga_sum). *)
Lemma cg_sum128 : forall ch p v, Z.land (2 + ch + p + v + ga_r ch p v) 127 = 0.
Proof.
intros ch p v. pose proof (ga_r_range ch p v) as Hr.
change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128.
replace (2 + ch + p + v + ga_r ch p v) with (1 + 1 + ch + p + v + ga_r ch p v) by lia.
apply F50_ga_sum.
Qed.

(* reac_ctrl_parse reads the frame as HEADAMP (6) and stores ch, param, value at p+30..32
   (Pau: parse_F50, ParseLink.v:11). *)
Lemma cg_parse_fields : forall ch p v,
  fst (ctrlparse 50 (F50 ch p v)) = 6 /\
  nth 30 (snd (ctrlparse 50 (F50 ch p v))) cp_z = Z_to_bv 8 ch /\
  nth 31 (snd (ctrlparse 50 (F50 ch p v))) cp_z = Z_to_bv 8 p /\
  nth 32 (snd (ctrlparse 50 (F50 ch p v))) cp_z = Z_to_bv 8 v.
Proof.
intros ch p v. destruct (ParseLink.parse_F50 ch p v) as [H6 HX]. split; [exact H6|].
set (X := snd (ctrlparse 50 (F50 ch p v))) in *.
assert (HL : (30 <= length X)%nat).
{ pose proof (f_equal (@length _) HX) as HLX. rewrite !length_app, length_firstn, length_skipn in HLX. cbn [length] in HLX. lia. }
rewrite HX. rewrite !app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn, Nat.min_l by lia. cbn. auto.
Qed.

(* The record bytes frame[34..40) = row[18..24) and the frame's fields. *)
Lemma cg_nth_rec : forall ch p v,
  nth 34 (T0z ++ GAz ch p v) 0 = 1 /\ nth 35 (T0z ++ GAz ch p v) 0 = 1 /\ nth 36 (T0z ++ GAz ch p v) 0 = ch /\
  nth 37 (T0z ++ GAz ch p v) 0 = p /\ nth 38 (T0z ++ GAz ch p v) 0 = v /\ nth 39 (T0z ++ GAz ch p v) 0 = ga_r ch p v.
Proof. intros ch p v. repeat split; reflexivity. Qed.

(* ---- The walk ---------------------------------------------------------------------------------- *)
(* Atoms of the entry state: 0..31 the registers at entry; 32 = the shadow offset; 33 = the record
   checksum byte `ga_r ch p v` of the row (its byte 23). *)
Definition cg_extra (r : Z) : list word := map (Z_to_bv 64) [SHADOW_OFF; r].
Definition ECG (regs : bvmap 5 word) (r : Z) : env := Eimg (Ereg regs (cg_extra r)).
Definition cg_regions : smem :=
  [ stack_region 144; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 36); uar_cell_regionP (A_OBJ 36) ].
Definition cg_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 0 255 0); (12%nat, mkAF 0 2 0); (14%nat, mkAF 0 255 0);
            (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 127 0) ] [] [].
Definition ss_cg : sstate := mkSS AF_check_groupa sr_atoms cg_regions None cg_facts.
Definition cg_SH : list shent := [].
Definition CGBx : sv := SOff 32 0.
Definition CGspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* A byte chunk of a region of the symbolic state is the byte in memory. *)
Lemma cg_chunk_aview : forall E ss (H : word -> bool) msX i n b lo hi wlo whi cs od e v,
  st_ok SEGS E ss (restrict H msX) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 ->
  aview SEGS H (ms_mem msX) (b + od) = Some v.
Proof.
intros E ss H msX i n b lo hi wlo whi cs od e v HS Hi Hb Hc He Hv.
pose proof (st_ok_region_nth E ss (restrict H msX) i _ HS Hi) as HR. cbn [ms_mem restrict] in HR.
pose proof (field_of_region E _ n b cs lo hi wlo whi od 1%N e v HR Hb Hc He ltac:(cbn; lia) ltac:(cbn; lia)) as V.
exact (aview_of_val_mem1 SEGS H (ms_mem msX) (b + od) v V Hv).
Qed.
(* Shadow bytes 0 over whole granules mark the bytes usable. *)
Lemma cg_ra_zero : forall (rd : Z -> option Z) F k n, F mod 8 = 0 -> 0 <= k -> 0 <= n ->
  (forall i, 0 <= i < n -> rd (SB + F / 8 + k + i) = Some 0) -> range_addressable rd SHADOW_OFF (F + 8 * k) (8 * n).
Proof.
intros rd F k n HF Hk Hn Hz. apply zero_shadow_range.
- rewrite Z.add_mod, HF by lia. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
- rewrite Z.mul_comm. apply Z_mod_mult.
- intros i Hi. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
  replace ((F + 8 * k) / 8) with (F / 8 + k).
  + replace (8 * n / 8) with n in Hi by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    replace (SB + (F / 8 + k) + i) with (SB + F / 8 + k + i) by lia. apply Hz. lia.
  + rewrite Z.mul_comm, Z.div_add by lia. reflexivity.
Qed.

(* The head-amp table is a heap block no call writes (every footprint is empty). *)
Lemma cg_tx_kept : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k tx T,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  In (tx, HL.TX_SIZE) (ablocks B ly S) -> In (tx, HL.TX_SIZE) (ablocks B ly' S') -> (forall a, ~ inFP FP a) ->
  obj_at SEGS (mrestrict (w_H W0) mem0) tx HL.LAY_TX (HL.tx_vals T) ->
  obj_at SEGS (mrestrict (w_H W') mem') tx HL.LAY_TX (HL.tx_vals T).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k tx T HJ Hb Hb' HnF HO.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (obj_at_transport_range SEGS _ _ tx HL.LAY_TX (HL.tx_vals T) 460 HO ltac:(vm_compute; reflexivity)).
intros i Hi.
apply (mbyte_of_aview SEGS). pose proof (req_size_pos HL.TX_SIZE ltac:(unfold HL.TX_SIZE; lia)) as [_ Hrq].
apply (F2 tx HL.TX_SIZE i Hb Hb'); [unfold HL.TX_SIZE in *; lia | apply HnF].
Qed.
(* arodata_okP survives a journal whose footprint is empty: the read-only bytes are image bytes that are neither an
   owned static nor errno, and the empty footprint opens no sink (PaBase.v arodata_ok_journalP, with
   sink_closed_nil in place of the read-only range's bound under the sink head). *)
Lemma cg_rod_journal : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem').
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (fp_spares_closed [] a sink_closed_nil)].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
exact (pa_relro_img a Hgot).
Qed.
(* reac_ctrl_parse's post keeps the caller's bytes in the tcj_kept form; when the bytes it may write lie below the
   allocation ceiling, that is the acall_kept form the walk layer's tactics read. *)
Lemma cg_tcj_acall : forall STK lyc Sc W memc W2 mem2 sp (E : Z -> Prop),
  (forall a, E a -> a < alloc_ceiling) ->
  tcj_kept B STK lyc Sc W memc W2 mem2 sp E -> acall_kept SEGS B lyc Sc W memc W2 mem2 (sp - STK) sp E.
Proof.
intros STK lyc Sc W memc W2 mem2 sp E HE (K1 & K2 & K3 & K4 & K5 & K6).
split; [|split; [exact K2 | split; [exact K3 | split; [exact K4 | split; [exact K5 | exact K6]]]]].
intros a Ha Hn. apply K1; [exact Ha | exact Hn | intros He; pose proof (HE a He); lia].
Qed.
(* Every byte of a live frame of the side stack for frames, and every shadow byte of one, is a client byte. *)
Lemma cg_live_client : forall ly S, tb_live_frames_client B ly S.
Proof.
intros ly S cid pos a Hin Ha. right. exists (cid, pos). split; [exact Hin|]. cbn [fst snd].
unfold frame_rng in Ha. exact Ha.
Qed.

(* A run of bytes read off the frame, as the verify contracts take it. *)
Lemma cg_garr8_frame : forall H m b (L L' : list Z) k,
  (forall i, (i < length L)%nat -> aview SEGS H m (b + Z.of_nat i) = Some (nth i L 0)) ->
  (k + length L' <= length L)%nat ->
  (forall j, (j < length L')%nat -> nth j L' 0 = nth (k + j) L 0) ->
  garr8 SEGS (mrestrict H m) (b + Z.of_nat k) L'.
Proof.
intros H m b L L' k HA Hk HN j Hj. rewrite (HN j Hj).
pose proof (HA (k + j)%nat ltac:(lia)) as Ha.
replace (b + Z.of_nat k + Z.of_nat j) with (b + Z.of_nat (k + j)) by lia.
exact (val_mem1_of_aview SEGS H m _ _ Ha).
Qed.
(* frame[0..50) is an object of check_groupa's side-stack frame: its shadow bytes 4..9 are 0, byte 10 is 2. *)
Lemma cg_afobj50 : forall ly' S' W' m F fpos, In (2, fpos) (frames S') -> frame_addr ly' 2 fpos = F -> F mod 8 = 0 ->
  (forall j, 4 <= j < 10 -> aview SEGS (w_H W') m (SB + F / 8 + j) = Some 0) ->
  aview SEGS (w_H W') m (SB + F / 8 + 10) = Some 2 ->
  afobj SEGS B ly' S' W' m (F + 32) 50.
Proof.
intros ly' S' W' m F fpos Hin EF HF80 ZP Z10.
split; [exists 2, fpos; split; [exact Hin|]; rewrite EF; change (fs_frame_bytes 2) with 256; repeat split; lia|].
split; [rewrite Z.add_mod, HF80 by lia; reflexivity|].
replace 50 with (48 + 2) by lia. apply range_addressable_app; [lia | |].
- replace (F + 32) with (F + 8 * 4) by lia. replace 48 with (8 * 6) by lia.
  apply cg_ra_zero; [exact HF80 | lia | lia |]. intros i Hi.
  replace (SB + F / 8 + 4 + i) with (SB + F / 8 + (4 + i)) by lia. apply ZP. lia.
- replace (F + 32 + 48) with (F + 80) by lia. apply range_addressable_partial; [| | lia].
  + unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF. replace ((F + 80) / 8) with (F / 8 + 10).
    { replace (SB + (F / 8 + 10)) with (SB + F / 8 + 10) by lia. exact Z10. }
    { replace (F + 80) with (F + 10 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  + rewrite Z.add_mod, HF80 by lia. reflexivity.
Qed.

(* check_groupa's own sum of frame[34..40), as the symbolic run computes it, is 0 mod 128
   (Pau: F50_ga_sum, GroupaModel.v:33, through cg_sum128). *)
Lemma cg_sum_sv : forall Ev ch p v, 0 <= ch < 256 -> 0 <= p < 3 -> 0 <= v < 256 ->
  ew Ev 11 = Z_to_bv 64 ch -> ew Ev 12 = Z_to_bv 64 p -> ew Ev 14 = Z_to_bv 64 v -> ew Ev 33 = Z_to_bv 64 (ga_r ch p v) ->
  sv_denot Ev (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 2) (SOff 12 0)) (SOff 14 0)) (SOff 33 0)) (SLit 127)) = Z_to_bv 64 0.
Proof.
intros Ev ch p v Hc Hp Hv E11 E12 E14 E33. pose proof (ga_r_range ch p v) as Hr.
cbn [sv_denot]. rewrite E11, E12, E14, E33. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r, !alu64_add_lit.
apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (ch + 2 + p + v + ga_r ch p v)) by lia. rewrite (Z.mod_small 127) by lia. rewrite (Z.mod_small 0) by lia.
replace (ch + 2 + p + v + ga_r ch p v) with (2 + ch + p + v + ga_r ch p v) by lia. apply cg_sum128.
Qed.

(* Releasing a side-stack frame changes only the frame-stack part of the state. *)
Lemma cg_set_fs_free : forall f S cid pos, exists g, stack_free_state cid pos (set_fs f S) = set_fs g S.
Proof. intros f S0 cid pos. eexists. unfold stack_free_state, set_fs. cbn. reflexivity. Qed.
Lemma cg_set_fs_set_fs : forall f g S, set_fs g (set_fs f S) = set_fs g S.
Proof. intros f g S0. reflexivity. Qed.

(* The runtime callees, the image facts and the four callee contracts the walk takes; pb_check_groupa below
   discharges each from hyps_check_groupa and walk_check_groupa's premises. *)
Section h.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.

Lemma cg_entry : forall ly S W (regs : bvmap 5 word) mem md ch0 (ch p v : Z),
  afn_pre SEGS B TCG_STK ly S W regs mem md ch0 ->
  getr regs 11 = w64 ch -> getr regs 12 = w64 p -> getr regs 14 = w64 v ->
  0 <= ch < 256 -> 0 <= p < 3 -> 0 <= v < 256 ->
  st_ok_pi SEGS VAL (ECG regs (ga_r ch p v)) ss_cg
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_groupa)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS CGBx cg_SH (ECG regs (ga_r ch p v)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch0 ch p v HPRE H11 H12 H14 Rch Rp Rv.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TCG_STK = 8480) by reflexivity.
pose proof (ga_r_range ch p v) as Rr.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kuar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 35 ltac:(lia)) as Hob35. pose proof (pa_obj_img 36 ltac:(lia)) as Hob36.
rewrite IMG_LO_B_val, IMG_TOP_B_val in Hob0, Hob1, Hob35, Hob36.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep. rewrite (pal_uar_cell B TL) in Hsep.
rewrite restrict_mkst_fx.
set (E := ECG regs (ga_r ch p v)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cg_extra (ga_r ch p v))) n)
  by (intros n Hn; subst E; unfold ECG; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 ch) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E14 : ew E 14 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (ga_r ch p v)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (EO : forall i, (i < 37)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
  by (intros i Hi; subst E; unfold ECG; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w).
{ intros n w Hn Hw. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hw. }
assert (VO : forall i, (i < 37)%nat -> base_val E (Some (A_OBJ i)) = VAL (A_OBJ i)).
{ intros i Hi. apply VB; [exact (EO i Hi) | pose proof (pa_val_range (A_OBJ i)); lia]. }
split.
- unfold ss_cg. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cg_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VO 1%nat) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
      [cbn [sv_denot]; rewrite (EO 35%nat) by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VO 35%nat) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VO 0%nat) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 36) 0) (VAL (A_OBJ 36)));
      [cbn [sv_denot]; rewrite (EO 36%nat) by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 36)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
    * rewrite (VO 36%nat) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 36)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
  + apply pairwise_disjoint_of_extents.
    unfold cg_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VO 0%nat), (VO 1%nat), (VO 35%nat), (VO 36%nat) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 FFS Hstk0 Hob0 Hob1 Hob35 Hob36 Hsep. clear. intros.
    rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
    repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok cg_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E11, E12, E14, E32, E33.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 FFS Hstk0 Hal16 Rch Rp Rv Rr. clear. unfold SHADOW_OFF. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cg_SH. constructor.
Qed.

Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA GS___asan_memcpy).
Hypothesis ASM2 : astack_malloc_realizes SEGS B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis HIMGSH : img_shadow_vis SEGS B.
Hypothesis HGLOBS : globs_marked SEGS B GRANT_GLOBS_B.
(* __const.check_groupa.frame (object 9): a registered global of 50 bytes, inside image B's read range with
   64-byte margins, whose bytes are T0z ++ repeat 0 34. *)
Hypothesis HIMG9 : IMG_check_groupa B.
Hypothesis TPARSE : tb_reac_ctrl_parse_spec B.
Hypothesis TEFF : tb_reac_headamp_tx_effective_spec B.
Hypothesis TRV : tb_reac_ctrl_headamp_record_verify_spec B.
Hypothesis TCKV : tb_reac_ctrl_checksum_verify_spec B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

Ltac cg_kept_intrin Hfr Hpres AG :=
  lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ _ _ _) =>
   lazymatch n with 2%nat => idtac | 60%nat => idtac | 529%nat => idtac end;
   eapply region_kept_aview;
   [ evalE AG
   | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; [lia | unfold ESTACK in *; zone_lia | unfold ESTACK in *; zone_lia]
   | exact Hpres ] end.

(* After a call into which the frame region was not kept: put the frame region back, with its last
   word (the flag address) as the only chunk. *)
Ltac cg_add_frame HS HJx VFLx RF E528 AG Hfin F FL :=
  let HFp := fresh "HFp" in
  let L := rnLAWS in
  destruct (al_frames _ _ L _ _ _ _ _ 2 _ (proj1 HJx) Hfin) as (_ & _ & HFp & _);
  change (fs_frame_bytes 2) with 256 in HFp; fold F in HFp;
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  let HS3 := fresh "HS3" in
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 0 256 0 24 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
  rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
  [ let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFp (F + o) ltac:(lia)))
  | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 248 8 _ FL);
    [cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VFLx] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite RF; evalE AG; unfold SB; repeat split; zone_lia)) as HS3;
  clear HS; rename HS3 into HS end; clear HFp; norm_ss HS.

(* Bytes outside every writable window of the symbolic state are kept by a run. *)
Ltac cg_win HFr Zs KN AG :=
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ Zs HFr
    ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
          let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
          intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
            [injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; evalE AG; intros Hrr; unfold SB in *; lia|]);
          destruct Hin)) as KN.

Ltac cg_b1 Ev F off val Hav AG :=
  apply (chunk_ok_val SEGS Ev _ F off 1 _ val);
  [ first [ reflexivity
          | cbn [sv_denot]; rewrite ?(AG 11%nat), ?(AG 12%nat), ?(AG 14%nat) by lia;
            lazymatch goal with H : ew _ _ = Z_to_bv 64 val |- _ => rewrite H end; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity ]
  | zside | zside | exact (proj1 (val_mem1_of_aview SEGS _ _ _ _ Hav)) ].

(* The writable windows of the flag-store run: the machine stack, the side-stack frame and its shadow,
   and the flag byte. *)
Ltac cg_wrange AG fpos F EFA EFL Hsp1 FFS :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; rewrite FFS; clear - Hr Hsp1; lia
| left; right; right; right; exists 2, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
| fail 2 "cg_wrange" ]
| ]);
destruct Hin.

Lemma cg_walk : tb_check_groupa_spec B.
Proof.
unfold tb_check_groupa_spec.
intros ly S W regs mem md ch0 row ch p tx rb rn T HPRE Hfr7 Htop32 HROD H10 H11 H12 H13 H14 Rch Rp Htx HTlen HTobj Hrb Hrbl Hrbh HROW.
destruct HIMG9 as (HG9 & HM9lo & HM9hi & HROD9).
unfold IMG_LO, IMG_HI in HM9lo, HM9hi. pose proof IMG_LO_B_val as HIMGlo. pose proof IMG_TOP_B_val as HIMGhi.
rewrite IMG_LO_B_val in HM9lo. rewrite IMG_TOP_B_val in HM9hi.
pose proof (eff_range T tx ch p) as Rv.
set (v := eff T tx ch p) in *.
pose proof (ga_r_range ch p v) as Rr.
destruct (cg_entry ly S W regs mem md ch0 ch p v HPRE H11 H12 H14 Rch Rp Rv) as [HS SHOK].
pose proof (ajournal_init SEGS B TCG_STK [] ly S W regs mem md ch0 HPRE) as HJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TCG_STK = 8480) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
remember (ECG regs (ga_r ch p v)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ECG; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 ch) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 p) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (E14 : ew E 14 = Z_to_bv 64 v) by (rewrite (EE 14%nat 14%bv eq_refl); exact H14).
assert (E13 : ew E 13 = Z_to_bv 64 tx) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13).
assert (E10 : ew E 10 = Z_to_bv 64 row) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E33 : ew E 33 = Z_to_bv 64 (ga_r ch p v)) by (rewrite HE; unfold ECG; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
unfold cfg_at. change (w64 (BASE + AF_check_groupa)) with (Z_to_bv 64 (BASE + AF_check_groupa)).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity.
img_factsF E. img_hull_factsF.
(* S0: from the entry to just after `andi sp,sp,-32` (0x820b4): slot AF_check_groupa + 0x44 = 0x167c. *)
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK CGspan 5756. { awrFL AG 0 0 EFA0. }
upd_aboveW_init HFr AG HUP. clear_frames.
(* S1: sp1 = (sp - 128) & -32 becomes atom 60; the stack region keeps its saved registers, region 60 is
   the aligned area [sp1, sp1 + 24). *)
set (sp1 := 32 * ((spZ regs + -128) / 32)).
destruct (sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by lia. clear Hsp1r.
assert (E2 : ew E 2 = getr regs 2) by exact (EE 2%nat 2%bv eq_refl).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(denot_and_m32 Ev 2 (spZ regs) (-128) ltac:(try (rewrite (AG 2%nat) by lia); rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(lia) ltac:(lia) ltac:(lia)) R2 end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 60 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 60%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E60 : ew Ev 60 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 60%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS; rename HS3 into HS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 24 0 24 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E60, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply HJpres; rewrite FFS; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; repeat split; zone_lia)) as HS3 end.
clear HJpres. clear HS; rename HS3 into HS. norm_ss HS.
reshok HS.
(* S1': to the call of __asan_stack_malloc_2 (0x820f0). *)
hei_havoc HS; paj_run_tok RUN HS HJ SHOK CGspan. { awrFL AG 0 0 EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG.
(* S2: the side-stack frame of class 2. *)
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite (palf_sm2 B TLF).
pose proof (count_cid_le_length 2 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML SMP 2 ASM2 ltac:(lia) W (ms_regs msX) (ms_mem msX) TCG_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ HJ) end.
  - unfold spZ at 1. rewrite R2. evalE AG.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - rewrite FFS, Hes; lia.
  - rewrite R3. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - change (fs_frames 2) with 4096. lia. }
cbv beta. clear R2 R3 R4 R1 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & _ & (fS2 & ES2)).
rewrite Hes in HK. replace (spZ regs + (sp1 - spZ regs) - 4096) with (sp1 - 4096) in HK by lia.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by lia.
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; lia. }
clear HUP. rename HUP2 into HUP.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgB _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
set (F := frame_addr ly 2 fpos) in *. set (FL := flag_addr ly 2 fpos) in *.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; first [keptFL HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)]).
(* S3: the frame's atoms and regions: 516 = F (the frame), 528 = its flag address, 529 = its shadow
   F / 8 + SB, with the alias 529 = (F >> 3) + SB the code computes; the frame is writable, its shadow
   is zero (aj_stack_malloc_atS) and its last word holds the flag address. *)
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 528%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; subst E; reflexivity) end.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL ly S2 W mem2 md2 2 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 516 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 528 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 529 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 516 32 529 F SB RF ltac:(lia) E32' E529)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS;
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 248 8 _ FL);
[cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + 248) with (F + 256 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
assert (ZS : forall j, 0 <= j < 4 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
replace (SB + F / 8 + 8 * j + ii) with (SB + F / 8 + (8 * j + ii)) by lia. apply Hz. change (256 / 8) with 32. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(fshadow_region 529 2 0 32 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 2 / 8) with 32; rewrite E529, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
apply (proj1 (HFSpres o ltac:(change (256 / 8) with 32; lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 0) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 16 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 16) with (SB + F / 8 + 8 * 2) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 24 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 24) with (SB + F / 8 + 8 * 3) by lia; apply ZS; lia]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 2 / 8) with 32; rewrite E529, RF; evalE AG; unfold SB; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
(* S4: header, shadow poisoning, to the first __asan_memcpy (0x821ec). *)
hei_havoc HS; paj_run_shc RUNP RUNC HS HJ2. { awrFL AG fpos F EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG.
(* S5: __asan_memcpy (F + 32, __const.check_groupa.frame, 50); object 9 holds T0z ++ repeat 0 34. The shadow
   bytes 4..9 of F are 00 and byte 10 is 02 (0x82188..0x82190, 0x821cc..0x821d8), so the fifty bytes are usable. *)
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (ZP0 : forall j, 4 <= j < 10 -> aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + j) = Some 0)
  by (intros j Hj; assert (Hj' : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9) by lia; repeat (destruct Hj' as [-> | Hj']); try (subst j);
      (eapply (cg_chunk_aview Ex ssx (w_H W) msX 0%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia]));
assert (Z10a : aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + 10) = Some 2)
  by (eapply (cg_chunk_aview Ex ssx (w_H W) msX 0%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia]);
pose proof (HROD9 (w_H W) (ms_mem msX) (cg_rod_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROD)) as G9;
destruct (ro_read_ok_glob SEGS B GRANT_GLOBS_B ly S2 W (ms_mem msX) _ (VAL (A_OBJ 9)) 50 (VAL (A_OBJ 9)) 50
  HGLOBS HG9 HIMGSH (proj1 HJ2) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(unfold IMG_LO; rewrite IMG_LO_B_val; lia) ltac:(unfold IMG_HI; rewrite IMG_TOP_B_val; lia)) as [RA9 HV9]
end.
destruct HFLrng as [[HFLapp HFLceil] HFLrng'].
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msX) 1 _ HS eq_refl) as HRfr; cbn [ms_mem restrict] in HRfr;
pose proof (field_of_region Ex _ 516 F _ _ _ _ _ 248 8%N (SOff 528 0) FL HRfr ltac:(evalE AG) ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VFL;
clear HRfr end.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA GS___asan_memcpy) AMEMCPY _ (ms_regs msX) (ms_mem msX) TCG_STK (spZ regs) [] ly S W mem md [(2, fpos)]
  ly S2 _ 0 (F + 32) (VAL (A_OBJ 9)) 50 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 6068)) HJ2) end.
  - rewrite Ra0. unfold w64. evalE AG.
  - rewrite Ra1. lazymatch goal with |- ew ?Ex _ = _ => let H := rnHEI Ex in exact (img_env_atomP Ex (A_OBJ 9) H ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) end.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ at 1. rewrite Rsp. evalE AG.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - rewrite Hes, FFS. lia.
  - rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + right; right; right; exists 2, fpos; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 2) with 256; fold F; lia.
    + unfold ESTACK. lia.
  - apply (amem_range_sub_app F 256 (F + 32) 50 HFhigh HFceil); lia.
  - assert (HF80 : F mod 8 = 0) by (rewrite HFq; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; apply Z_mod_mult).
    replace 50 with (48 + 2) by lia. apply range_addressable_app; [lia | |].
    + replace (F + 32) with (F + 8 * 4) by lia. replace 48 with (8 * 6) by lia.
      apply cg_ra_zero; [exact HF80 | lia | lia |]. intros i Hi.
      replace (SB + F / 8 + 4 + i) with (SB + F / 8 + (4 + i)) by lia. apply ZP0. lia.
    + replace (F + 32 + 48) with (F + 80) by lia. apply range_addressable_partial; [| | lia].
      * unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF. replace ((F + 80) / 8) with (F / 8 + 10).
        { replace (SB + (F / 8 + 10)) with (SB + F / 8 + 10) by lia. exact Z10a. }
        { replace (F + 80) with (F + 10 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      * rewrite Z.add_mod, HF80 by lia. reflexivity.
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ 2 fpos (F + 32) 50 (proj1 HJ2) Hfin2); fold F; try change (fs_frame_bytes 2) with 256; lia.
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - destruct (G9 (Z.to_nat (a - VAL (A_OBJ 9))) ltac:(change (length (T0z ++ repeat 0 34)) with 50%nat; lia)) as [Vm Vr].
        replace (VAL (A_OBJ 9) + Z.of_nat (Z.to_nat (a - VAL (A_OBJ 9)))) with a in Vm by lia.
        rewrite (aview_of_val_mem1 SEGS _ _ _ _ Vm Vr). discriminate.
      - unfold spZ. rewrite Rsp. evalE AG. unfold ESTACK. lia. }
    split; [lia|].
    split; [left; unfold kLowMemEnd; lia|].
    split; [exact RA9 | intros _; exact HV9]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff1 & Hfr4 & Hpres4 & HSM4).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp ZP0 Z10a.
assert (HUP4 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). apply Hfr4; [lia | lia | unfold ESTACK; lia]. }
clear HUP. rename HUP4 into HUP.
(* S6: what the first copy leaves: frame[0..16) = T0 (the first 16 bytes of __const.check_groupa.frame). *)
assert (TB : forall i, 0 <= i < 16 -> aview SEGS (w_H W) mem4 (F + 32 + i) = Some (nth (Z.to_nat i) T0z 0)).
{ intros i Hi. rewrite (Heff1 i ltac:(lia)).
  destruct (G9 (Z.to_nat i) ltac:(change (length (T0z ++ repeat 0 34)) with 50%nat; lia)) as [Vm Vr].
  rewrite Z2Nat.id in Vm by lia. rewrite app_nth1 in Vm, Vr by (cbn [length T0z]; lia).
  exact (aview_of_val_mem1 SEGS _ _ _ _ Vm Vr). }
assert (VFL4 : val_mem SEGS (mrestrict (w_H W) mem4) (F + 248) 8 FL).
{ apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) (ms_mem ms1) mem4 (F + 248) 8 FL); [|exact VFL].
  intros x Hx. apply Hfr4; [lia | cbn in Hx; lia | unfold ESTACK; lia]. }
aconstsF HJ2 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
reseat HS HJ4 HP4 [0; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first [cg_kept_intrin Hfr4 Hpres4 AG
 | keptFL HK HJ4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 ltac:(idtac; fail) ltac:(idtac; fail)
]).
cg_hide_all. cg_show_disj.
cg_add_frame HS HJ4 VFL4 RF E528 AG Hfin2 F FL.
cg_show_all.
(* S7: to the second __asan_memcpy (0x82208). Image B's one trap guard lies on the way: 0x821f4
   `bgeu s7, a0` with s7 = F + 32 and a0 = -16, false because F < 2^47 (atom 516's fact). *)
hei_havoc HS; paj_run_shc RUNP RUNC HS HJ4. { awrFL AG fpos F EFA0. }
cg_win HFr (fun a => (F <= a < F + 24) \/ (SB + F / 8 <= a < SB + F / 8 + 32) \/ (sp1 <= a < sp1 + 24) \/ (spZ regs - 104 <= a < spZ regs)) KN7 AG.
assert (TB2 : forall i, 0 <= i < 16 -> aview SEGS (w_H W) (ms_mem ms2) (F + 32 + i) = Some (nth (Z.to_nat i) T0z 0))
  by (intros i Hi; rewrite <- (TB i Hi); apply KN7; [lia | cbv beta; unfold SB; zone_lia]).
assert (VFL2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms2)) (F + 248) 8 FL)
  by (apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem4 (ms_mem ms2) (F + 248) 8 FL); [intros x Hx; apply KN7; [lia | cbv beta; cbn in Hx; unfold SB; zone_lia] | exact VFL4]).
clear KN7.
upd_aboveW HUP HFr AG. clear HF HFr HG.
(* S8: __asan_memcpy (F + 48, row, 34). *)
destruct (al_blocks _ _ LAWS ly S W mem md rb rn HAR Hrb) as (Hrb16 & Hrb4096 & Hrbceil & Hrbh_ia & _ & _).
pose proof (blk_off_imgB _ _ _ _ _ _ rb rn HAR Hrb) as Hrb_img.
pose proof (req_size_pos rn ltac:(lia)) as [_ Hrq].
assert (Hrb2 : In (rb, rn) (ablocks B ly S2)) by (rewrite Eab; exact Hrb).
pose proof (sep_block_frame SEGS B LAWS ly S2 _ _ _ rb rn 2 fpos HAR2 Hrb2 Hfin2) as HdRF.
unfold zdisjoint in HdRF. cbn [fst snd] in HdRF. change (fs_frame_bytes 2) with 256 in HdRF. fold F in HdRF.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (Z6 : aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + 6) = Some 0)
  by (eapply (cg_chunk_aview Ex ssx (w_H W) msX 1%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia]);
assert (Z7 : aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + 7) = Some 0)
  by (eapply (cg_chunk_aview Ex ssx (w_H W) msX 1%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia]);
assert (Z8 : aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + 8) = Some 0)
  by (eapply (cg_chunk_aview Ex ssx (w_H W) msX 1%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia]);
assert (Z9 : aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + 9) = Some 0)
  by (eapply (cg_chunk_aview Ex ssx (w_H W) msX 1%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia]);
assert (Z10 : aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + 10) = Some 2)
  by (eapply (cg_chunk_aview Ex ssx (w_H W) msX 1%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia]);
assert (GR : garr8 SEGS (mrestrict (w_H W) (ms_mem msX)) row (GAz ch p v))
  by (eapply (garr8_journal_block_x SEGS B); [exact HJ4 | exact Hrb | exact Hrb2 | lia | cbn [length GAz]; lia
     | intros a _ Hin; exact (inFP_nil _ Hin) | exact HROW])
end.
assert (HF80 : F mod 8 = 0) by (rewrite HFq; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; apply Z_mod_mult).
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA GS___asan_memcpy) AMEMCPY _ (ms_regs msX) (ms_mem msX) TCG_STK (spZ regs) [] ly S W mem md [(2, fpos)]
  ly S2 _ 0 (F + 48) row 34 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 6096)) HJ4) end.
  - rewrite Ra0. unfold w64. evalE AG.
  - rewrite Ra1. evalE AG; try (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ at 1. rewrite Rsp. evalE AG.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - rewrite Hes, FFS. lia.
  - rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + right; right; right; exists 2, fpos; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 2) with 256; fold F; lia.
    + unfold ESTACK. lia.
  - apply (amem_range_sub_app F 256 (F + 48) 34 HFhigh HFceil); lia.
  - replace 34 with (32 + 2) by lia. apply range_addressable_app; [lia | |].
    + replace (F + 48) with (F + 8 * 6) by lia. replace 32 with (8 * 4) by lia.
      apply cg_ra_zero; [exact HF80 | lia | lia |]. intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as [-> | [-> | [-> | ->]]] by lia.
      * rewrite Z.add_0_r. exact Z6.
      * replace (SB + F / 8 + 6 + 1) with (SB + F / 8 + 7) by lia. exact Z7.
      * replace (SB + F / 8 + 6 + 2) with (SB + F / 8 + 8) by lia. exact Z8.
      * replace (SB + F / 8 + 6 + 3) with (SB + F / 8 + 9) by lia. exact Z9.
    + replace (F + 48 + 32) with (F + 80) by lia. apply range_addressable_partial; [| | lia].
      * unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF. replace ((F + 80) / 8) with (F / 8 + 10).
        { replace (SB + (F / 8 + 10)) with (SB + F / 8 + 10) by lia. exact Z10. }
        { replace (F + 80) with (F + 10 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      * rewrite Z.add_mod, HF80 by lia. reflexivity.
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ 2 fpos (F + 48) 34 (proj1 HJ4) Hfin2); fold F; try change (fs_frame_bytes 2) with 256; lia.
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - destruct (GR (Z.to_nat (a - row)) ltac:(cbn [length GAz]; lia)) as [Vm Vr].
        replace (row + Z.of_nat (Z.to_nat (a - row))) with a in Vm by lia.
        rewrite (aview_of_val_mem1 SEGS _ _ _ _ Vm Vr). discriminate.
      - unfold spZ. rewrite Rsp. evalE AG. unfold ESTACK. lia. }
    split; [lia|].
    split; [apply (amem_range_of_block SEGS B LAWS ly S2 _ _ _ rb rn _ _ (proj1 HJ4) Hrb2); lia|].
    split; [apply (range_addressable_of_block SEGS B LAWS ly S2 _ _ _ rb rn _ _ (proj1 HJ4) Hrb2); lia|].
    intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S2 _ _ _ rb rn _ _ (proj1 HJ4) Hrb2); lia. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff2 & Hfr5 & Hpres5 & HSM5).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp Z6 Z7 Z8 Z9 Z10.
(* S9: what the second copy leaves: frame[16..50) = the row. *)
assert (HUP5 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem5 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). apply Hfr5; [lia | lia | unfold ESTACK; lia]. }
clear HUP. rename HUP5 into HUP.
assert (TB5 : forall i, 0 <= i < 16 -> aview SEGS (w_H W) mem5 (F + 32 + i) = Some (nth (Z.to_nat i) T0z 0))
  by (intros i Hi; rewrite <- (TB2 i Hi); apply Hfr5; [lia | lia | unfold ESTACK; lia]).
assert (RB5 : forall i, 0 <= i < 34 -> aview SEGS (w_H W) mem5 (F + 48 + i) = Some (nth (Z.to_nat i) (GAz ch p v) 0)).
{ intros i Hi. rewrite (Heff2 i Hi). destruct (GR (Z.to_nat i) ltac:(cbn [length GAz]; lia)) as [Vm Vr].
  rewrite Z2Nat.id in Vm by lia. exact (aview_of_val_mem1 SEGS _ _ _ _ Vm Vr). }
assert (VFL5 : val_mem SEGS (mrestrict (w_H W) mem5) (F + 248) 8 FL).
{ apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) (ms_mem ms2) mem5 (F + 248) 8 FL); [|exact VFL2].
  intros x Hx. apply Hfr5; [lia | cbn in Hx; lia | unfold ESTACK; lia]. }
aconstsF HJ4 Kgot6 Kcell6 Kguar6 Kuar6. aconstsF HJ5 Kgot7 Kcell7 Kguar7 Kuar7.
reseat HS HJ5 HP5 [1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first [cg_kept_intrin Hfr5 Hpres5 AG
 | keptFL HK HJ5 AG Kgot6 Kgot7 Kcell6 Kcell7 Kguar6 Kguar7 Kuar6 Kuar7 ltac:(idtac; fail) ltac:(idtac; fail)
]).
cg_hide_all. cg_show_disj.
cg_add_frame HS HJ5 VFL5 RF E528 AG Hfin2 F FL.
cg_show_all.
(* S10: the parsed struct is marked usable; to reac_ctrl_parse (0x82230). *)
hei_havoc HS; paj_run_shc RUNP RUNC HS HJ5. { awrFL AG fpos F EFA0. }
cg_win HFr (fun a => (F <= a < F + 24) \/ (SB + F / 8 <= a < SB + F / 8 + 32) \/ (sp1 <= a < sp1 + 24) \/ (spZ regs - 104 <= a < spZ regs)) KN10 AG.
cg_hide_all.
assert (FB : forall i, (i < 50)%nat -> aview SEGS (w_H W) (ms_mem ms3) (F + 32 + Z.of_nat i) = Some (cp_v (F50 ch p v) i)).
{ intros i Hi. rewrite (cg_cp_v_F50 ch p v i Rch Rp Rv). rewrite KN10 by (cbv beta; unfold SB; zone_lia).
  destruct (Nat.lt_ge_cases i 16) as [Hlt | Hge].
  - rewrite app_nth1 by (cbn [length T0z]; lia). rewrite (TB5 (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
  - rewrite app_nth2 by (cbn [length T0z]; lia). change (length T0z) with 16%nat.
    replace (F + 32 + Z.of_nat i) with (F + 48 + Z.of_nat (i - 16)) by lia.
    rewrite (RB5 (Z.of_nat (i - 16))) by (cbn [length GAz] in *; lia). rewrite Nat2Z.id. reflexivity. }
assert (VFL3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms3)) (F + 248) 8 FL)
  by (apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem5 (ms_mem ms3) (F + 248) 8 FL); [intros x Hx; apply KN10; [lia | cbv beta; cbn in Hx; unfold SB; zone_lia] | exact VFL5]).
cg_show_all.
clear KN10.
upd_aboveW HUP HFr AG. clear HF HFr HG.
(* S11: reac_ctrl_parse (f, 50, o), f = F + 32, o = F + 128; in the caller-journal form. *)
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (ZP : forall j, (j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 16 \/ j = 17 \/ j = 18 \/ j = 19) ->
  aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + j) = Some 0)
  by (intros j Hj; repeat (destruct Hj as [-> | Hj]); try (subst j);
      (eapply (cg_chunk_aview Ex ssx (w_H W) msX 1%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia]));
assert (Z10 : aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + 10) = Some 2)
  by (eapply (cg_chunk_aview Ex ssx (w_H W) msX 1%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia]);
assert (Z20 : aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + 20) = Some 4)
  by (eapply (cg_chunk_aview Ex ssx (w_H W) msX 1%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia]);
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msX) 3 _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
  ltac:(evalE AG) ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; unfold raZ; rewrite Z_to_bv_bv_unsigned; reflexivity)
  ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
  ltac:(evalE AG) ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; unfold s0Z; rewrite Z_to_bv_bv_unsigned; reflexivity)
  ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0
end; clear HRstk;
pose proof (cg_rod_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5 HROD) as HROD5
end.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Hal8 : spZ regs mod 8 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hal16; [|lia]; destruct Hal16 as [q Hq]; exists (2 * q); lia).
lazymatch goal with |- SRr _ _ {| cfg_ms := ?msX; cfg_model := _ |} _ =>
assert (Hch1 : achain ly (aview SEGS (w_H W) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch0))
  by (replace (spZ regs + -8) with (spZ regs - 8) in Vra by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs0 by lia;
      exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch ltac:(lia) HUP
        (rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(lia) Hal8 ltac:(lia) ltac:(lia))) end.
assert (RA3 : getr (ms_regs ms3) 1 = Z_to_bv 64 (BASE + 6136)) by exact Rra.
assert (SP3 : spZ (ms_regs ms3) = sp1) by (unfold spZ at 1; rewrite Rsp; evalE AG).
assert (S03 : s0Z (ms_regs ms3) = spZ regs) by (unfold s0Z; rewrite Rs0; evalE AG).
pmkst HS.
rewrite pa_sigma_reac_ctrl_parse.
fs_roF HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
  change (mkCfg (mkst (ms_regs msX) (Z_to_bv 64 (BASE + AF_reac_ctrl_parse)) (ms_mem msX) (seg_rom SEGS)) mdX)
    with (cfg_at SEGS (BASE + AF_reac_ctrl_parse) (ms_regs msX) (ms_mem msX) mdX);
  eapply (TPARSE TCG_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly S2 W (ms_mem msX) mdX 0 (ms_regs msX)
    ((spZ regs, raZ regs, s0Z regs) :: ch0) (F + 32) 50 (F + 128) (F50 ch p v) HJ5 HROD5) end.
  - rewrite RA3. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite RA3. pose proof pa_B_ok as HB. rewrite unsigned_lit_small by lia. lia.
  - rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - rewrite Ra0. unfold w64. evalE AG.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. unfold w64. evalE AG.
  - lia.
  - rewrite SP3, S03. exact Hch1.
  - rewrite SP3. exact Hsp1al16.
  - rewrite SP3, TCG_STK_parse. lia.
  - rewrite SP3. lia.
  - rewrite Hfrs2. cbn [length]. lia.
  - exact (cg_live_client ly S2).
  - split; [exists 2, fpos; split; [exact Hfin2|]; fold F; change (fs_frame_bytes 2) with 256; repeat split; lia|].
    split; [rewrite Z.add_mod, HF80 by lia; reflexivity|].
    replace 50 with (48 + 2) by lia. apply range_addressable_app; [lia | |].
    + replace (F + 32) with (F + 8 * 4) by lia. replace 48 with (8 * 6) by lia.
      apply cg_ra_zero; [exact HF80 | lia | lia |]. intros i Hi.
      replace (SB + F / 8 + 4 + i) with (SB + F / 8 + (4 + i)) by lia. apply ZP. lia.
    + replace (F + 32 + 48) with (F + 80) by lia. apply range_addressable_partial; [| | lia].
      * unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF. replace ((F + 80) / 8) with (F / 8 + 10).
        { replace (SB + (F / 8 + 10)) with (SB + F / 8 + 10) by lia. exact Z10. }
        { replace (F + 80) with (F + 10 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      * rewrite Z.add_mod, HF80 by lia. reflexivity.
  - split; [exists 2, fpos; split; [exact Hfin2|]; fold F; change (fs_frame_bytes 2) with 256; repeat split; lia|].
    split; [rewrite Z.add_mod, HF80 by lia; reflexivity|].
    replace 36 with (32 + 4) by lia. apply range_addressable_app; [lia | |].
    + replace (F + 128) with (F + 8 * 16) by lia. replace 32 with (8 * 4) by lia.
      apply cg_ra_zero; [exact HF80 | lia | lia |]. intros i Hi.
      replace (SB + F / 8 + 16 + i) with (SB + F / 8 + (16 + i)) by lia. apply ZP. lia.
    + replace (F + 128 + 32) with (F + 160) by lia. apply range_addressable_partial; [| | lia].
      * unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF. replace ((F + 160) / 8) with (F / 8 + 20).
        { replace (SB + (F / 8 + 20)) with (SB + F / 8 + 20) by lia. exact Z20. }
        { replace (F + 160) with (F + 20 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      * rewrite Z.add_mod, HF80 by lia. reflexivity.
  - lia.
  - intros a Ha. split; [right; right; right; exists 2, fpos; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 2) with 256; fold F; lia|].
    destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ5) Hfin2) as (_ & _ & HFp5 & _).
    change (fs_frame_bytes 2) with 256 in HFp5. fold F in HFp5.
    destruct (HFp5 a ltac:(lia)) as [Hpa Hna].
    split; [exact Hpa|]. split; [exact Hna|]. rewrite SP3. unfold ESTACK. lia.
  - exact (length_F50 ch p v).
  - exact FB. }
cbv beta. intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hfrs6 & Hab6 & (fS6 & ES6) & Ha06 & Hout6 & HK6).
(* reac_ctrl_parse's tcj_kept, read in the acall_kept form: the result [F + 128, F + 164) lies below the ceiling. *)
apply cg_tcj_acall in HK6; [|intros a Ha; cbv beta in Ha; lia].
(* S12: after reac_ctrl_parse: its result 6 and the fields p.ch, p.param, p.value. *)
destruct (cg_parse_fields ch p v) as (P6 & Pch & Pp & Pv).
pose proof HK6 as (K61 & _ & _ & K64 & _).
assert (HUP6 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W6) mem6 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). apply K61; [lia | rewrite SP3; lia]. }
clear HUP. rename HUP6 into HUP.
assert (KF6 : forall a, F <= a < F + 256 -> ~ (F + 128 <= a < F + 128 + 36) -> aview SEGS (w_H W6) mem6 a = aview SEGS (w_H W) (ms_mem ms3) a).
{ intros a Ha Hn. apply (K64 2 fpos a Hfin2); [left; unfold in_zr, frame_rng; cbn [fst snd]; fold F; change (fs_frame_bytes 2) with 256; lia | exact Hn]. }
assert (FB6 : forall i, (i < 50)%nat -> aview SEGS (w_H W6) mem6 (F + 32 + Z.of_nat i) = Some (nth i (T0z ++ GAz ch p v) 0)).
{ intros i Hi. rewrite KF6 by lia. rewrite (FB i Hi). rewrite (cg_cp_v_F50 ch p v i Rch Rp Rv). reflexivity. }
assert (VFL6 : val_mem SEGS (mrestrict (w_H W6) mem6) (F + 248) 8 FL).
{ apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W6) (ms_mem ms3) mem6 (F + 248) 8 FL); [|exact VFL3].
  intros x Hx. apply KF6; cbn in Hx; lia. }
assert (FO6 : forall i, (i < 3)%nat -> aview SEGS (w_H W6) mem6 (F + 158 + Z.of_nat i) = Some (nth i [ch; p; v] 0)).
{ intros i Hi. replace (F + 158 + Z.of_nat i) with (F + 128 + Z.of_nat (30 + i)) by lia. rewrite (Hout6 (30 + i)%nat) by lia.
  assert (i = 0 \/ i = 1 \/ i = 2)%nat as [-> | [-> | ->]] by lia; cbn [Nat.add nth].
  - rewrite Pch, u8_lit by lia. reflexivity.
  - rewrite Pp, u8_lit by lia. reflexivity.
  - rewrite Pv, u8_lit by lia. reflexivity. }
clear KF6.
aconstsF HJ5 Kgot8 Kcell8 Kguar8 Kuar8. aconstsF HJ6 Kgot9 Kcell9 Kguar9 Kuar9.
reseat HS HJ6 HP6 [1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first [keptFL HK6 HJ6 AG Kgot8 Kgot9 Kcell8 Kcell9 Kguar8 Kguar9 Kuar8 Kuar9 ltac:(idtac; intro; zone_lia) ltac:(idtac; fail)
]).
assert (Hfin6 : In (2, fpos) (frames S6)) by (rewrite Hfrs6; exact Hfin2).
pose proof HJ6 as (_ & Hly6 & _). destruct (al_layout _ _ LAWS _ _ _ _ _ ly6 HAR Hly6) as (_ & EFA6 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ6) Hfin6) as (_ & _ & HFp6 & HFSp6).
rewrite EFA6 in HFp6, HFSp6.
change (fs_frame_bytes 2 / 8) with 32 in HFSp6. change (fs_frame_bytes 2) with 256 in HFp6. fold F in HFp6, HFSp6.
fs_rwF HS E529 HFSp6.
destruct (cg_nth_rec ch p v) as (N34 & N35 & N36 & N37 & N38 & N39).
assert (A66 : aview SEGS (w_H W6) mem6 (F + 66) = Some 1) by (rewrite <- N34; rewrite <- (FB6 34%nat) by lia; f_equal; lia).
assert (A67 : aview SEGS (w_H W6) mem6 (F + 67) = Some 1) by (rewrite <- N35; rewrite <- (FB6 35%nat) by lia; f_equal; lia).
assert (A68 : aview SEGS (w_H W6) mem6 (F + 68) = Some ch) by (rewrite <- N36; rewrite <- (FB6 36%nat) by lia; f_equal; lia).
assert (A69 : aview SEGS (w_H W6) mem6 (F + 69) = Some p) by (rewrite <- N37; rewrite <- (FB6 37%nat) by lia; f_equal; lia).
assert (A70 : aview SEGS (w_H W6) mem6 (F + 70) = Some v) by (rewrite <- N38; rewrite <- (FB6 38%nat) by lia; f_equal; lia).
assert (A71 : aview SEGS (w_H W6) mem6 (F + 71) = Some (ga_r ch p v)) by (rewrite <- N39; rewrite <- (FB6 39%nat) by lia; f_equal; lia).
assert (A158 : aview SEGS (w_H W6) mem6 (F + 158) = Some ch) by (rewrite <- (Z.add_0_r (F + 158)); exact (FO6 0%nat ltac:(lia))).
assert (A159 : aview SEGS (w_H W6) mem6 (F + 159) = Some p) by (replace (F + 159) with (F + 158 + Z.of_nat 1) by lia; exact (FO6 1%nat ltac:(lia))).
assert (A160 : aview SEGS (w_H W6) mem6 (F + 160) = Some v) by (replace (F + 160) with (F + 158 + Z.of_nat 2) by lia; exact (FO6 2%nat ltac:(lia))).
cg_hide_all. cg_show_disj.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 0 256 0 24
  [YP09.mkChunk 248 (CVal 8 (SOff 528 0)); YP09.mkChunk 66 (CVal 1 (SLit 1)); YP09.mkChunk 67 (CVal 1 (SLit 1));
   YP09.mkChunk 68 (CVal 1 (SOff 11 0)); YP09.mkChunk 69 (CVal 1 (SOff 12 0)); YP09.mkChunk 70 (CVal 1 (SOff 14 0));
   YP09.mkChunk 71 (CVal 1 (SOff 33 0)); YP09.mkChunk 158 (CVal 1 (SOff 11 0)); YP09.mkChunk 159 (CVal 1 (SOff 12 0));
   YP09.mkChunk 160 (CVal 1 (SOff 14 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
  rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
  [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFp6 (F + o) ltac:(lia)))
  | apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ F 248 8 _ FL);
      [cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VFL6]|];
    apply Forall_cons; [cg_b1 Ev F 66 1 A66 AG|];
    apply Forall_cons; [cg_b1 Ev F 67 1 A67 AG|];
    apply Forall_cons; [cg_b1 Ev F 68 ch A68 AG|];
    apply Forall_cons; [cg_b1 Ev F 69 p A69 AG|];
    apply Forall_cons; [cg_b1 Ev F 70 v A70 AG|];
    apply Forall_cons; [cg_b1 Ev F 71 (ga_r ch p v) A71 AG|];
    apply Forall_cons; [cg_b1 Ev F 158 ch A158 AG|];
    apply Forall_cons; [cg_b1 Ev F 159 p A159 AG|];
    apply Forall_cons; [cg_b1 Ev F 160 v A160 AG|];
    apply Forall_nil ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite RF; evalE AG; unfold SB; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
cg_show_all.
clear A66 A67 A68 A69 A70 A71 A158 A159 A160.
(* a0 = 6, the parser's HEADAMP. *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (10%bv : bv 5) (SLit 6) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite Ha06, P6; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
(* S13: the three field checks hold; to reac_headamp_tx_effective (tx, ch, param). *)
rewrite RA3.
hei_havoc HS; paj_run_shc RUNP RUNC HS HJ6.
all: try (awrFL AG fpos F EFA6).
cg_win HFr (fun a => (F <= a < F + 24) \/ (SB + F / 8 <= a < SB + F / 8 + 32) \/ (sp1 <= a < sp1 + 24) \/ (spZ regs - 104 <= a < spZ regs)) KN13 AG.
cg_hide_all.
lazymatch goal with |- SRr _ _ {| cfg_ms := ?msX; cfg_model := _ |} _ =>
assert (FB13 : forall i, (i < 50)%nat -> aview SEGS (w_H W6) (ms_mem msX) (F + 32 + Z.of_nat i) = Some (nth i (T0z ++ GAz ch p v) 0))
  by (intros i Hi; rewrite <- (FB6 i Hi); apply KN13; [lia | cbv beta; unfold SB; zone_lia]);
assert (VFL13 : val_mem SEGS (mrestrict (w_H W6) (ms_mem msX)) (F + 248) 8 FL)
  by (apply (val_mem_aview_kept_x SEGS (w_H W6) (w_H W6) mem6 (ms_mem msX) (F + 248) 8 FL); [intros x Hx; apply KN13; [lia | cbv beta; cbn in Hx; unfold SB; zone_lia] | exact VFL6])
end.
cg_show_all.
clear KN13.
upd_aboveW HUP HFr AG. clear HF HFr HG.
prreg HS (10%bv : bv 5) Rb0. prreg HS (11%bv : bv 5) Rb1. prreg HS (12%bv : bv 5) Rb2. prreg HS (1%bv : bv 5) Rbra.
prreg HS (2%bv : bv 5) Rbsp. prreg HS (3%bv : bv 5) Rbgp. prreg HS (4%bv : bv 5) Rbtp. prreg HS (8%bv : bv 5) Rbs0.
pose proof Hly6 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop6 & _).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msY) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W6) msY) 3 _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
  ltac:(evalE AG) ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; unfold raZ; rewrite Z_to_bv_bv_unsigned; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qra) ltac:(cbn; lia)) as Vra2;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
  ltac:(evalE AG) ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; unfold s0Z; rewrite Z_to_bv_bv_unsigned; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qs0) ltac:(cbn; lia)) as Vs02
end; clear HRstk;
assert (Hch2 : achain ly6 (aview SEGS (w_H W6) (ms_mem msY)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch0))
  by (apply (achain_ly_top ly ly6 _ _ _ _ Etop6);
      replace (spZ regs + -8) with (spZ regs - 8) in Vra2 by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs02 by lia;
      exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch ltac:(lia) HUP
        (rdword_of_val_mem SEGS _ _ _ _ Vra2 Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs02 Qs0) Hra4 ltac:(lia) Hal8 ltac:(lia) ltac:(lia)))
end.
clear Vra2 Vs02.
assert (Htx6 : In (tx, HL.TX_SIZE) (ablocks B ly6 S6)) by (rewrite Hab6, Eab; exact Htx).
lazymatch goal with |- SRr _ _ {| cfg_ms := ?msX; cfg_model := _ |} _ =>
assert (HTobj6 : obj_at SEGS (mrestrict (w_H W6) (ms_mem msX)) tx HL.LAY_TX (HL.tx_vals T))
  by (eapply cg_tx_kept; [exact HJ6 | exact Htx | exact Htx6 | intros a (rg & [] & _) | exact HTobj])
end.
pmkst HS.
rewrite pa_sigma_reac_headamp_tx_effective.
fs_roF HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
  eapply (cl_callS B LAWS W6 (ms_regs msX) (ms_mem msX) _ TCG_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly6 S6 mdX 0
    STK_reac_headamp_tx_effective [] 0 (sp1 - spZ regs) (getr (ms_regs msX) 1) ((spZ regs, raZ regs, s0Z regs) :: ch0)
    (fun ly' S' W' regs' mem' md' => ly' = ly6 /\ S' = S6 /\ W' = W6 /\ getr regs' 10 = w64 (eff T tx ch p) /\
       (tx <> 0 -> obj_at SEGS (mrestrict (w_H W6) mem') tx HL.LAY_TX (HL.tx_vals T))) HJ6) end.
  - unfold spZ at 1. rewrite Rbsp. evalE AG.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - unfold STK_reac_headamp_tx_effective. rewrite Hes. lia.
  - rewrite FFS. unfold STK_reac_headamp_tx_effective. rewrite Hes. lia.
  - rewrite Rbgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Rbtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - reflexivity.
  - rewrite Rbra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Rbra. pose proof pa_B_ok as HB. rewrite unsigned_lit_small by lia. lia.
  - replace (spZ regs + (sp1 - spZ regs)) with sp1 by lia.
    replace (s0Z _) with (spZ regs) by (unfold s0Z; rewrite Rbs0; evalE AG). exact Hch2.
  - intros HPRE7.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg ?pcx ?mm ?rom) ?mdd) _ =>
    change (mkCfg (mkst rg pcx mm rom) mdd) with (cfg_at SEGS (BASE + AF_reac_headamp_tx_effective) rg mm mdd) end.
    (* tx_effective's contract allows tx = 0; here the table is a live block, its right arm. *)
    apply (TEFF ly6 S6 W6 _ _ _ _ tx ch p T HPRE7); [ | | | lia | lia | exact HTlen | right; split; [exact Htx6 | exact HTobj6]].
    + rewrite Rb0. rewrite (AG 13%nat) by lia. exact E13.
    + rewrite Rb1. rewrite (AG 11%nat) by lia. exact E11.
    + rewrite Rb2. rewrite (AG 12%nat) by lia. exact E12.
  - intros a (rg & [] & _). }
cbv beta. intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HJ7c & HP7 & (-> & -> & -> & Ha07 & HTobj7)).
rewrite Rbra.
assert (HK7 : acall_kept SEGS B ly6 S6 W6 (ms_mem ms4) W6 mem7 (spZ regs + (sp1 - spZ regs) - STK_reac_headamp_tx_effective) (spZ regs + (sp1 - spZ regs)) (fun _ => False)).
{ eapply (acall_kept_of_journal SEGS B Hsegs); [exact HJ7c | exact (proj1 HJ6) | intros a (rg & [] & _) | intros b m i Hb _ _; exact Hb | exact sink_closed_nil]. }
aconstsF HJ6 Qgot7p Qcell7p Qguar7p Quar7p.
pose proof HK7 as (K71 & _ & _ & K74 & _).
assert (HUP7 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W6) mem7 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). apply K71; [lia | lia]. }
clear HUP. rename HUP7 into HUP.
assert (KF7 : forall a, F <= a < F + 256 -> aview SEGS (w_H W6) mem7 a = aview SEGS (w_H W6) (ms_mem ms4) a).
{ intros a Ha. apply (K74 2 fpos a Hfin6); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA6; fold F; change (fs_frame_bytes 2) with 256; lia | intros []]. }
assert (FB7 : forall i, (i < 50)%nat -> aview SEGS (w_H W6) mem7 (F + 32 + Z.of_nat i) = Some (nth i (T0z ++ GAz ch p v) 0))
  by (intros i Hi; rewrite KF7 by lia; exact (FB13 i Hi)).
assert (VFL7 : val_mem SEGS (mrestrict (w_H W6) mem7) (F + 248) 8 FL)
  by (apply (val_mem_aview_kept_x SEGS (w_H W6) (w_H W6) (ms_mem ms4) mem7 (F + 248) 8 FL); [intros x Hx; apply KF7; cbn in Hx; lia | exact VFL13]).
clear KF7 K71 K74.
aconstsF HJ7 Qgot7 Qcell7 Qguar7 Quar7.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ7) Hfin6) as (_ & _ & HFp7 & HFSp7).
rewrite EFA6 in HFp7, HFSp7. change (fs_frame_bytes 2 / 8) with 32 in HFSp7. change (fs_frame_bytes 2) with 256 in HFp7. fold F in HFp7, HFSp7.
reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first [keptFL HK7 HJ7 AG Qgot7p Qgot7 Qcell7p Qcell7 Qguar7p Qguar7 Quar7p Quar7 ltac:(idtac; fail)
     ltac:(idtac; match goal with |- apresent _ _ ?x => apply (proj1 (HFp7 x ltac:(lia))) end)
]).
fs_rwF HS E529 HFSp7.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (10%bv : bv 5) (SOff 14 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite (AG 14%nat) by lia; rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned, Ha07; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
(* S15: p.value = the effective value; to reac_ctrl_headamp_record_verify (frame). *)
hei_havoc HS; paj_run_shc RUNP RUNC HS HJ7.
all: try (awrFL AG fpos F EFA6).
cg_win HFr (fun a => (F <= a < F + 24) \/ (SB + F / 8 <= a < SB + F / 8 + 32) \/ (sp1 <= a < sp1 + 24) \/ (spZ regs - 104 <= a < spZ regs)) KN7 AG.
cg_hide_all.
lazymatch goal with |- SRr _ _ {| cfg_ms := ?msX; cfg_model := _ |} _ =>
assert (FB7r : forall i, (i < 50)%nat -> aview SEGS (w_H W6) (ms_mem msX) (F + 32 + Z.of_nat i) = Some (nth i (T0z ++ GAz ch p v) 0))
  by (intros i Hi; rewrite <- (FB7 i Hi); apply KN7; [lia | cbv beta; unfold SB; zone_lia]);
assert (VFL7r : val_mem SEGS (mrestrict (w_H W6) (ms_mem msX)) (F + 248) 8 FL)
  by (apply (val_mem_aview_kept_x SEGS (w_H W6) (w_H W6) mem7 (ms_mem msX) (F + 248) 8 FL); [intros x Hx; apply KN7; [lia | cbv beta; cbn in Hx; unfold SB; zone_lia] | exact VFL7])
end.
cg_show_all.
clear KN7.
upd_aboveW HUP HFr AG. clear HF HFr HG.
prreg HS (10%bv : bv 5) Rc8a0. prreg HS (1%bv : bv 5) Rc8ra.
prreg HS (2%bv : bv 5) Rc8sp. prreg HS (3%bv : bv 5) Rc8gp. prreg HS (4%bv : bv 5) Rc8tp. prreg HS (8%bv : bv 5) Rc8s0.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msY) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W6) msY) 3 _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
  ltac:(evalE AG) ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; unfold raZ; rewrite Z_to_bv_bv_unsigned; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qra) ltac:(cbn; lia)) as Vra2;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
  ltac:(evalE AG) ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; unfold s0Z; rewrite Z_to_bv_bv_unsigned; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qs0) ltac:(cbn; lia)) as Vs02
end; clear HRstk;
assert (Hch8 : achain ly6 (aview SEGS (w_H W6) (ms_mem msY)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch0))
  by (apply (achain_ly_top ly ly6 _ _ _ _ Etop6);
      replace (spZ regs + -8) with (spZ regs - 8) in Vra2 by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs02 by lia;
      exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch ltac:(lia) HUP
        (rdword_of_val_mem SEGS _ _ _ _ Vra2 Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs02 Qs0) Hra4 ltac:(lia) Hal8 ltac:(lia) ltac:(lia)));
assert (ZP8 : forall j, 4 <= j < 10 -> aview SEGS (w_H W6) (ms_mem msY) (SB + F / 8 + j) = Some 0)
  by (intros j Hj; assert (Hj' : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9) by lia; repeat (destruct Hj' as [-> | Hj']); try (subst j);
      (eapply (cg_chunk_aview Ex ssx (w_H W6) msY 1%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia]));
assert (Z108 : aview SEGS (w_H W6) (ms_mem msY) (SB + F / 8 + 10) = Some 2)
  by (eapply (cg_chunk_aview Ex ssx (w_H W6) msY 1%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia])
end.
clear Vra2 Vs02.
pmkst HS.
rewrite pa_sigma_reac_ctrl_headamp_record_verify.
fs_roF HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
  eapply (cl_callS B LAWS W6 (ms_regs msX) (ms_mem msX) _ TCG_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly6 S6 mdX 0
    STK_reac_ctrl_headamp_record_verify [] 0 (sp1 - spZ regs) (getr (ms_regs msX) 1) ((spZ regs, raZ regs, s0Z regs) :: ch0)
    (fun ly' S' W' regs' mem' md' => ly' = ly6 /\ S' = S6 /\ W' = W6 /\ getr regs' 10 = w64 (if hv (Z_to_bv 8 4) (Z_to_bv 8 3) (map (Z_to_bv 8) [1; 1; ch; p; v; ga_r ch p v]) then 0 else -1)) HJ7) end.
  - unfold spZ at 1. rewrite Rc8sp. evalE AG.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - unfold STK_reac_ctrl_headamp_record_verify. lia.
  - rewrite FFS. unfold STK_reac_ctrl_headamp_record_verify. lia.
  - rewrite Rc8gp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Rc8tp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - reflexivity.
  - rewrite Rc8ra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Rc8ra. pose proof pa_B_ok as HB. rewrite unsigned_lit_small by lia. lia.
  - replace (spZ regs + (sp1 - spZ regs)) with sp1 by lia.
    replace (s0Z _) with (spZ regs) by (unfold s0Z; rewrite Rc8s0; evalE AG). exact Hch8.
  - intros HPRE8.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg ?pcx ?mm ?rom) ?mdd) _ =>
    change (mkCfg (mkst rg pcx mm rom) mdd) with (cfg_at SEGS (BASE + AF_reac_ctrl_headamp_record_verify) rg mm mdd) end.
    apply (TRV ly6 S6 W6 _ _ _ _ (F + 32) 4 3 [1; 1; ch; p; v; ga_r ch p v] HPRE8).
    + rewrite Rc8a0. unfold w64. evalE AG.
    + exact (cg_afobj50 ly6 S6 W6 _ F fpos Hfin6 ltac:(rewrite EFA6; reflexivity) HF80 ZP8 Z108).
    + replace (F + 32 + 18) with (F + 32 + Z.of_nat 18) by lia.
      apply (cg_garr8_frame _ _ _ (T0z ++ GAz ch p v)).
      * intros i Hi. apply FB7r. change (length (T0z ++ GAz ch p v)) with 50%nat in Hi. lia.
      * cbn. lia.
      * intros j Hj. cbn [length] in Hj. destruct j as [|[|j]]; [reflexivity | reflexivity | lia].
    + reflexivity.
    + replace (F + 32 + 34) with (F + 32 + Z.of_nat 34) by lia.
      apply (cg_garr8_frame _ _ _ (T0z ++ GAz ch p v)).
      * intros i Hi. apply FB7r. change (length (T0z ++ GAz ch p v)) with 50%nat in Hi. lia.
      * cbn. lia.
      * intros j Hj. cbn [length] in Hj. destruct j as [|[|[|[|[|[|j]]]]]]; try reflexivity; lia.
  - intros a (rg & [] & _). }
cbv beta. intros W8 c8 _ (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HJ8c & HP8 & (-> & -> & -> & Ha08)).
rewrite Rc8ra. rewrite (cg_hv ch p v Rch Rp Rv) in Ha08.
lazymatch type of HJ8c with ajournal _ _ _ _ _ _ _ _ ?memc _ _ _ _ _ _ _ _ =>
assert (HK8 : acall_kept SEGS B ly6 S6 W6 memc W6 mem8 (spZ regs + (sp1 - spZ regs) - STK_reac_ctrl_headamp_record_verify) (spZ regs + (sp1 - spZ regs)) (fun _ => False))
by (eapply (acall_kept_of_journal SEGS B Hsegs); [exact HJ8c | exact (proj1 HJ7) | intros a (rg & [] & _) | intros b m i Hb _ _; exact Hb | exact sink_closed_nil]) end.
aconstsF HJ7 Qgot8p Qcell8p Qguar8p Quar8p.
pose proof HK8 as (K81 & _ & _ & K84 & _).
assert (HUP8 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W6) mem8 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). apply K81; [lia | lia]. }
clear HUP. rename HUP8 into HUP.
lazymatch type of HK8 with acall_kept _ _ _ _ _ ?memc _ _ _ _ _ =>
assert (KF8 : forall a, F <= a < F + 256 -> aview SEGS (w_H W6) mem8 a = aview SEGS (w_H W6) memc a)
 by (intros a Ha; apply (K84 2 fpos a Hfin6); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA6; fold F; change (fs_frame_bytes 2) with 256; lia | intros []]) end.
assert (FB8 : forall i, (i < 50)%nat -> aview SEGS (w_H W6) mem8 (F + 32 + Z.of_nat i) = Some (nth i (T0z ++ GAz ch p v) 0))
  by (intros i Hi; rewrite KF8 by lia; exact (FB7r i Hi)).
assert (VFL8 : val_mem SEGS (mrestrict (w_H W6) mem8) (F + 248) 8 FL)
  by (eapply (val_mem_aview_kept_x SEGS (w_H W6) (w_H W6) _ mem8 (F + 248) 8 FL); [intros x Hx; apply KF8; cbn in Hx; lia | exact VFL7r]).
clear KF8 K81 K84.
aconstsF HJ8 Qgot8 Qcell8 Qguar8 Quar8.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ8) Hfin6) as (_ & _ & HFp8 & HFSp8).
rewrite EFA6 in HFp8, HFSp8. change (fs_frame_bytes 2 / 8) with 32 in HFSp8. change (fs_frame_bytes 2) with 256 in HFp8. fold F in HFp8, HFSp8.
reseat HS HJ8 HP8 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first [keptFL HK8 HJ8 AG Qgot8p Qgot8 Qcell8p Qcell8 Qguar8p Qguar8 Quar8p Quar8 ltac:(idtac; fail)
     ltac:(idtac; match goal with |- apresent _ _ ?x => apply (proj1 (HFp8 x ltac:(lia))) end)
]).
fs_rwF HS E529 HFSp8.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (10%bv : bv 5) (SLit 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite Ha08; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
(* S16: to reac_ctrl_checksum_verify (frame). *)
hei_havoc HS; paj_run_shc RUNP RUNC HS HJ8.
all: try (awrFL AG fpos F EFA6).
cg_win HFr (fun a => (F <= a < F + 24) \/ (SB + F / 8 <= a < SB + F / 8 + 32) \/ (sp1 <= a < sp1 + 24) \/ (spZ regs - 104 <= a < spZ regs)) KN8 AG.
cg_hide_all.
lazymatch goal with |- SRr _ _ {| cfg_ms := ?msX; cfg_model := _ |} _ =>
assert (FB8r : forall i, (i < 50)%nat -> aview SEGS (w_H W6) (ms_mem msX) (F + 32 + Z.of_nat i) = Some (nth i (T0z ++ GAz ch p v) 0))
  by (intros i Hi; rewrite <- (FB8 i Hi); apply KN8; [lia | cbv beta; unfold SB; zone_lia]);
assert (VFL8r : val_mem SEGS (mrestrict (w_H W6) (ms_mem msX)) (F + 248) 8 FL)
  by (apply (val_mem_aview_kept_x SEGS (w_H W6) (w_H W6) mem8 (ms_mem msX) (F + 248) 8 FL); [intros x Hx; apply KN8; [lia | cbv beta; cbn in Hx; unfold SB; zone_lia] | exact VFL8])
end.
cg_show_all.
clear KN8.
upd_aboveW HUP HFr AG. clear HF HFr HG.
prreg HS (10%bv : bv 5) Rc9a0. prreg HS (1%bv : bv 5) Rc9ra.
prreg HS (2%bv : bv 5) Rc9sp. prreg HS (3%bv : bv 5) Rc9gp. prreg HS (4%bv : bv 5) Rc9tp. prreg HS (8%bv : bv 5) Rc9s0.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msY) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W6) msY) 3 _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
  ltac:(evalE AG) ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; unfold raZ; rewrite Z_to_bv_bv_unsigned; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qra) ltac:(cbn; lia)) as Vra2;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
  ltac:(evalE AG) ltac:(cbn; tauto)
  ltac:(cbn [sv_denot]; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; unfold s0Z; rewrite Z_to_bv_bv_unsigned; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qs0) ltac:(cbn; lia)) as Vs02
end; clear HRstk;
assert (Hch9 : achain ly6 (aview SEGS (w_H W6) (ms_mem msY)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch0))
  by (apply (achain_ly_top ly ly6 _ _ _ _ Etop6);
      replace (spZ regs + -8) with (spZ regs - 8) in Vra2 by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs02 by lia;
      exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch ltac:(lia) HUP
        (rdword_of_val_mem SEGS _ _ _ _ Vra2 Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs02 Qs0) Hra4 ltac:(lia) Hal8 ltac:(lia) ltac:(lia)));
assert (ZP9 : forall j, 4 <= j < 10 -> aview SEGS (w_H W6) (ms_mem msY) (SB + F / 8 + j) = Some 0)
  by (intros j Hj; assert (Hj' : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9) by lia; repeat (destruct Hj' as [-> | Hj']); try (subst j);
      (eapply (cg_chunk_aview Ex ssx (w_H W6) msY 1%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia]));
assert (Z109 : aview SEGS (w_H W6) (ms_mem msY) (SB + F / 8 + 10) = Some 2)
  by (eapply (cg_chunk_aview Ex ssx (w_H W6) msY 1%nat); [exact HS | reflexivity | evalE AG | cbn; tauto | reflexivity | lia])
end.
clear Vra2 Vs02.
pmkst HS.
rewrite pa_sigma_reac_ctrl_checksum_verify.
fs_roF HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
  eapply (cl_callS B LAWS W6 (ms_regs msX) (ms_mem msX) _ TCG_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly6 S6 mdX 0
    STK_reac_ctrl_checksum_verify [] 0 (sp1 - spZ regs) (getr (ms_regs msX) 1) ((spZ regs, raZ regs, s0Z regs) :: ch0)
    (fun ly' S' W' regs' mem' md' => ly' = ly6 /\ S' = S6 /\ W' = W6 /\ getr regs' 10 = w64 (if blocksum (map (Z_to_bv 8) (skipn 2 (GAz ch p v))) =? 0 then 0 else -1)) HJ8) end.
  - unfold spZ at 1. rewrite Rc9sp. evalE AG.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - unfold STK_reac_ctrl_checksum_verify. lia.
  - rewrite FFS. unfold STK_reac_ctrl_checksum_verify. lia.
  - rewrite Rc9gp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Rc9tp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - reflexivity.
  - rewrite Rc9ra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Rc9ra. pose proof pa_B_ok as HB. rewrite unsigned_lit_small by lia. lia.
  - replace (spZ regs + (sp1 - spZ regs)) with sp1 by lia.
    replace (s0Z _) with (spZ regs) by (unfold s0Z; rewrite Rc9s0; evalE AG). exact Hch9.
  - intros HPRE9.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg ?pcx ?mm ?rom) ?mdd) _ =>
    change (mkCfg (mkst rg pcx mm rom) mdd) with (cfg_at SEGS (BASE + AF_reac_ctrl_checksum_verify) rg mm mdd) end.
    apply (TCKV ly6 S6 W6 _ _ _ _ (F + 32) (skipn 2 (GAz ch p v)) HPRE9).
    + rewrite Rc9a0. unfold w64. evalE AG.
    + exact (cg_afobj50 ly6 S6 W6 _ F fpos Hfin6 ltac:(rewrite EFA6; reflexivity) HF80 ZP9 Z109).
    + reflexivity.
    + replace (F + 32 + 18) with (F + 32 + Z.of_nat 18) by lia.
      apply (cg_garr8_frame _ _ _ (T0z ++ GAz ch p v)).
      * intros i Hi. apply FB8r. change (length (T0z ++ GAz ch p v)) with 50%nat in Hi. lia.
      * cbn. lia.
      * intros j Hj. change (length (skipn 2 (GAz ch p v))) with 32%nat in Hj.
        do 32 (destruct j as [|j]; [reflexivity|]). lia.
  - intros a (rg & [] & _). }
cbv beta. intros W9 c9 _ (ly9 & S9 & regs9 & mem9 & md9 & -> & HJ9 & HJ9c & HP9 & (-> & -> & -> & Ha09)).
rewrite Rc9ra. rewrite (cg_blocksum ch p v Rch Rp Rv) in Ha09. cbn [Z.eqb] in Ha09.
lazymatch type of HJ9c with ajournal _ _ _ _ _ _ _ _ ?memc _ _ _ _ _ _ _ _ =>
assert (HK9 : acall_kept SEGS B ly6 S6 W6 memc W6 mem9 (spZ regs + (sp1 - spZ regs) - STK_reac_ctrl_checksum_verify) (spZ regs + (sp1 - spZ regs)) (fun _ => False))
by (eapply (acall_kept_of_journal SEGS B Hsegs); [exact HJ9c | exact (proj1 HJ8) | intros a (rg & [] & _) | intros b m i Hb _ _; exact Hb | exact sink_closed_nil]) end.
aconstsF HJ8 Qgot9p Qcell9p Qguar9p Quar9p.
pose proof HK9 as (K91 & _ & _ & K94 & _).
assert (HUP9 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W6) mem9 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). apply K91; [lia | lia]. }
clear HUP. rename HUP9 into HUP.
lazymatch type of HK9 with acall_kept _ _ _ _ _ ?memc _ _ _ _ _ =>
assert (KF9 : forall a, F <= a < F + 256 -> aview SEGS (w_H W6) mem9 a = aview SEGS (w_H W6) memc a)
 by (intros a Ha; apply (K94 2 fpos a Hfin6); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA6; fold F; change (fs_frame_bytes 2) with 256; lia | intros []]) end.
assert (FB9 : forall i, (i < 50)%nat -> aview SEGS (w_H W6) mem9 (F + 32 + Z.of_nat i) = Some (nth i (T0z ++ GAz ch p v) 0))
  by (intros i Hi; rewrite KF9 by lia; exact (FB8r i Hi)).
assert (VFL9 : val_mem SEGS (mrestrict (w_H W6) mem9) (F + 248) 8 FL)
  by (eapply (val_mem_aview_kept_x SEGS (w_H W6) (w_H W6) _ mem9 (F + 248) 8 FL); [intros x Hx; apply KF9; cbn in Hx; lia | exact VFL8r]).
clear KF9 K91 K94.
aconstsF HJ9 Qgot9 Qcell9 Qguar9 Quar9.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ9) Hfin6) as (_ & _ & HFp9 & HFSp9).
rewrite EFA6 in HFp9, HFSp9. change (fs_frame_bytes 2 / 8) with 32 in HFSp9. change (fs_frame_bytes 2) with 256 in HFp9. fold F in HFp9, HFSp9.
reseat HS HJ9 HP9 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first [keptFL HK9 HJ9 AG Qgot9p Qgot9 Qcell9p Qcell9 Qguar9p Qguar9 Quar9p Quar9 ltac:(idtac; fail)
     ltac:(idtac; match goal with |- apresent _ _ ?x => apply (proj1 (HFp9 x ltac:(lia))) end)
]).
fs_rwF HS E529 HFSp9.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (10%bv : bv 5) (SLit 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite Ha09; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
(* S17: the record sum and the value check; to the exit. *)
hei_havoc HS; paj_run_shc RUNP RUNC HS HJ9.
all: try (awrFL AG fpos F EFA6).
upd_aboveW HUP HFr AG. clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ (* the sum is not 0 mod 128: unreachable *)
  exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
  rewrite (cg_sum_sv Ev ch p v Rch Rp Rv ltac:(rewrite (AG 11%nat) by lia; exact E11) ltac:(rewrite (AG 12%nat) by lia; exact E12)
    ltac:(rewrite (AG 14%nat) by lia; exact E14) E33) in Hc end.
  vm_compute in Hc. discriminate Hc. }
clear Hc.
(* S18: p.value == want; to the next stop. *)
paj_run_sh RUNP HS HJ9.
all: try (awrFL AG fpos F EFA6).
upd_aboveW HUP HFr AG. clear HF HFr HG.
(* S19: the flag store releases the side-stack frame; the epilogue; the return. *)
assert (EFL6 : forall c p0, flag_addr ly6 c p0 = flag_addr ly c p0)
  by (intros c p0; unfold flag_addr; pose proof Hly6 as (_ & _ & _ & _ & _ & EF6 & _); rewrite EF6; reflexivity).
destruct (FFL _ _ _ _ _ 2 fpos (proj1 HJ9) Hfin6) as (HFLpres9 & HFLown9 & HFLrng9).
rewrite EFL6 in HFLpres9, HFLown9, HFLrng9. fold FL in HFLpres9, HFLown9, HFLrng9.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ9) Hfin6) as (_ & _ & HFpX & _).
rewrite EFA6 in HFpX. change (fs_frame_bytes 2) with 256 in HFpX. fold F in HFpX.
assert (HnoF : forall a, F <= a < F + 256 -> ~ aowned B ly6 S6 a) by (intros a Ha; exact (proj2 (HFpX a Ha))).
(* Image B's own bound for the flag byte, which image A's walk got from off_img: the flag address of a live frame
   is no byte of the layout's image range (AR_client_img_law), and that range covers [IMG_LO_B, IMG_TOP_B)
   (pa_img_cover). On the integration tree off_img is lib/B/YCbq.v's, over image B's top 0x5fb000; the walk does not
   depend on which. *)
assert (HFLnz : ~ in_zr FL (ly_img ly6)).
{ refine (proj1 (al_client_img _ _ LAWS ly6 S6 _ _ _ FL (proj1 HJ9) _)).
  right; right. exists 2, fpos. split; [exact Hfin6|]. rewrite EFL6. reflexivity. }
destruct (proj1 HJ9) as (M9 & LG9 & _).
pose proof (pa_img_cover _ _ _ LG9) as [CV1 CV2].
cg_hide_all.
assert (HFLoff : FL + 1 <= IMG_LO_B \/ IMG_TOP_B <= FL)
  by (unfold in_zr in HFLnz; cbn [fst snd] in HFLnz; lia).
clear HFLnz M9 LG9 CV1 CV2.
add_flag_region HS AG E528 HFLpres9 HFLrng9 HFLown9 HnoF HnoF HnoF.
paj_run_flag_sh RUNF HS HJ9; [lia | cg_wrange AG fpos F EFA6 EFL6 Hsp1 FFS | flag0 E528 EFL6 |].
cg_show_all.
prreg HS (1%bv : bv 5) R1.
lazymatch goal with |- SRr _ ?Wx _ _ => eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
intros mat'. unfold tb_check_groupa_post, apost_base.
lazymatch type of HJ9 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end.
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ9|].
split; [apply aregs_preserved_eqs; creg HS AG EE|].
split; [pose proof HJ9 as (_ & _ & _ & _ & _ & Hfr9 & _); exact Hfr9|].
split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly6 S6); rewrite Hab6; exact Eab|].
rewrite ES6, ES2, cg_set_fs_set_fs. apply cg_set_fs_free.
Qed.
End h.

(* The walk: hyps_check_groupa and the four callee contracts give check_groupa's contract. IMG_RO_BELOW is not
   used: this walk carries arodata_okP across its calls with cg_rod_journal, whose journals have an empty
   footprint, so the read-only range needs no bound under the sink head. *)
Theorem pb_check_groupa : walk_check_groupa B.
Proof.
unfold walk_check_groupa, hyps_check_groupa, RT_LAWS, RT_PALIB, RT_PALIBF, RT_ML, RT_MEMCPY, RT_SM, RT_SMP,
  RT_ASF, RT_FFL, RT_TP_FS, RT_IMGSH, RT_GLOBS.
intros (HL & HTL & HTLF & HML & HCPY & HSM2 & HSMP & HASF & HFFL & _ & HISH & HGL & _ & HIMG) HP HE HR HC.
eapply cg_walk; eassumption.
Qed.
End e.
End d.
End b.
