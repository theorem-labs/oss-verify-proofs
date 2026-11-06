(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module names changed; 406 of its 502 lines of code are new or changed and 485 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_exit_crt: the piece ex_crt_stmt of the exit segment of the image-A walk of
   libreac/fuzz_decode's LLVMFuzzerTestOneInput (lib/A/Prog/LLVMFuzzerTestOneInput_seg_exit_cuts.v).

   ex_crt_ok : ex_crt_stmt. From ex_st_960 to ex_st_978: the five instructions +0x960 .. +0x970 of DecodeList.v:628-632
   (li a3,12; ld s2,64(s1); mv a0,s2; mv a1,s7; mv a2,s6), stepped by the Pa engine, and the `jal check_round_trip` at
   +0x974 (DecodeList.v:633), discharged by the statement's premise dec_check_round_trip_cg
   (lib/A/Prog/check_round_trip_cg.v:150) at the caller's journal of dec_a_core.

   The contract's premises: the geometry nch = upstream_result len = up_nch len = w, even, 2 <= w <= 40, from
   up_ok = true (ex_up_geom); the two blocks (res, len) and (upb, 36 w) of ex_blocks; the braid relation of
   check_braid_c.braid_off from the two byte arrays of ex_st_960 and reac_decode_c.braid_out (ex_crt_braid); the
   frame-pointer chain [(sp0, RA_LLVMF, caller s0)] by YCbq.v achain_push from the entry chain and the saved words
   (or [] when sp0 is within 16 bytes of the stack top); the room facts from dec_a_base; the meter from mo_ok at
   dec_rest_86c. The post: acall_kept with no written range keeps every byte the next pieces read.

   Proof steps follow lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v (a Theorem Labs lane's, 4d4ce59e5f2: the entry sstate, reg_at,
   garr8_kept / rdword_kept, the call and the dec_a_core build) and libreac/fuzz_boxreg's ReadName.v (1d92330b7ad). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
  DecodeSyms DecodeList DecodeAddr DecodePa DecodePaLib DecodeImg YC4b YC1g YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import check_round_trip_cg LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_exit_cuts.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require check_braid_c reac_decode_c reac_upstream_channels_c
  reac_upstream_decode_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module CDec := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_c.
Module CChan := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_c.
Module CUp := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_decode_c.
Module DCBc := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.check_braid_c.
(* YC4b switches lia's division handling off for its importers; this file's arithmetic needs it (ReadName.v's line). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. The C facts                                                       *)
(* ------------------------------------------------------------------ *)

(* An accepted third reac_upstream_decode: len = 52 + 36 w with w even in 2 .. 40 (up_nch needs 124 <= len), and
   then reac_upstream_channels' result is the same w. *)
Lemma ex_up_geom : forall raw out len bs, CUp.up_ok raw out len bs = true ->
  exists w, len = 52 + 36 * w /\ Z.even w = true /\ 2 <= w <= 40 /\
    CUp.up_nch len = w /\ CChan.upstream_result len = w.
Proof.
intros raw out len bs H. unfold CUp.up_ok in H. rewrite !andb_true_iff in H.
destruct H as ((((((_ & _) & Hn) & _) & _) & _) & _).
apply Z.leb_le in Hn.
assert (Hc : ((124 <=? len) && ((len - 52) mod 36 =? 0) && (((len - 52) / 36) mod 2 =? 0) &&
  ((len - 52) / 36 <=? 40))%bool = true).
{ revert Hn. unfold CUp.up_nch.
  destruct ((124 <=? len) && ((len - 52) mod 36 =? 0) && (((len - 52) / 36) mod 2 =? 0) && ((len - 52) / 36 <=? 40))%bool;
  intros Hn; [reflexivity | simpl in Hn; lia]. }
assert (Hup : CUp.up_nch len = (len - 52) / 36) by (unfold CUp.up_nch; rewrite Hc; reflexivity).
rewrite !andb_true_iff in Hc. destruct Hc as (((H1 & H2) & H3) & H4).
apply Z.leb_le in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. apply Z.leb_le in H4.
pose proof (Z.div_mod (len - 52) 36 ltac:(lia)) as Hd.
revert Hd H3 H4 Hup. remember ((len - 52) / 36) as w eqn:Hw. intros Hd H3 H4 Hup.
assert (Hl : len = 52 + 36 * w) by lia.
assert (Hw2 : 2 <= w) by lia.
assert (He : Z.even w = true).
{ rewrite (Z.div_mod w 2) by lia. rewrite H3, Z.add_0_r, Z.even_mul. reflexivity. }
exists w. split; [exact Hl|]. split; [exact He|]. split; [lia|]. split; [exact Hup|].
unfold CChan.upstream_result, CChan.upstream_ok, CChan.upstream_width. rewrite <- Hw.
rewrite (Z.mod_small w (2 ^ 32)) by lia. rewrite He, H2.
replace (52 <=? len) with true by (symmetry; apply Z.leb_le; lia).
replace (2 <=? w) with true by (symmetry; apply Z.leb_le; lia).
replace (w <=? 40) with true by (symmetry; apply Z.leb_le; lia).
reflexivity.
Qed.

(* reac_decode_c.braid_pos is check_braid_c's audio offset. *)
Lemma ex_braid_pos : forall w ch s j, 0 <= ch -> 0 <= j < 3 ->
  CDec.braid_pos s ch w j = 3 * (s * w + 2 * (ch / 2)) + DCBc.braid_off ch j.
Proof.
intros w ch s j Hch Hj.
pose proof (Z.div_mod ch 2 ltac:(lia)) as Hd. rewrite Zmod_even in Hd.
unfold CDec.braid_pos, DCBc.braid_off. rewrite Zmod_even.
assert (j = 0 \/ j = 1 \/ j = 2) as [-> | [-> | ->]] by lia;
destruct (Z.even ch);
try change (0 =? 0) with true; try change (1 =? 0) with false; try change (2 =? 0) with false;
try change (1 =? 1) with true; try change (2 =? 1) with false;
cbv beta iota zeta; lia.
Qed.

Lemma ex_braid_off_range : forall ch j, 0 <= DCBc.braid_off ch j <= 5.
Proof.
intros ch j. unfold DCBc.braid_off.
destruct (Z.even ch); destruct (j =? 0); try destruct (j =? 1); lia.
Qed.

Lemma ex_nth_map_bv : forall (l : list byte) n, (n < length l)%nat ->
  nth n (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
induction l as [|b l IH]; intros n Hn; [cbn in Hn; lia|].
destruct n as [|n]; [reflexivity|]. cbn [map nth]. apply IH. cbn [length] in Hn. lia.
Qed.

Lemma ex_len_braid_out : forall bs nch ns, length (CDec.braid_out bs nch ns) = Z.to_nat (3 * nch * ns).
Proof. intros. unfold CDec.braid_out. rewrite !length_map, length_seq. reflexivity. Qed.

Lemma ex_nth_braid_out : forall bs nch ns n, (n < Z.to_nat (3 * nch * ns))%nat ->
  nth n (CDec.braid_out bs nch ns) (Z_to_bv 8 0) = CDec.braid_byte bs nch ns (Z.of_nat n).
Proof.
intros bs nch ns n Hn. unfold CDec.braid_out.
rewrite (nth_indep _ (Z_to_bv 8 0) (CDec.braid_byte bs nch ns (Z.of_nat 0)))
  by (rewrite !length_map, length_seq; exact Hn).
rewrite map_nth, map_nth, seq_nth by exact Hn. reflexivity.
Qed.

Lemma ex_body_len : forall n (pl : list byte), n = Z.of_nat (length pl) ->
  Z.of_nat (length (skipn (Z.to_nat (dec_a_u n)) pl)) = dec_a_len n.
Proof. intros n pl Hn. rewrite length_skipn. unfold dec_a_u, dec_a_len. lia. Qed.

Lemma ex_saved_at_range : forall o, In o dec_a_saved_at -> 8 <= fst o <= 104.
Proof. intros o Ho. unfold dec_a_saved_at in Ho. repeat (destruct Ho as [<-|Ho]; [cbn; lia|]). destruct Ho. Qed.

(* ------------------------------------------------------------------ *)
(* 2. Memory helpers (a Theorem Labs lane's seg_entry.v garr8_kept / rdword_kept)   *)
(* ------------------------------------------------------------------ *)

Section mh. Context {rc : YM05.RunCeil}.
Local Abbreviation segs := decodesegs0.

Lemma ex_rdword_range : forall H (mem : word -> option byte) a v,
  rdword (aview segs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
repeat match type of Hw with context [aview segs H mem ?x] =>
  let Hx := fresh "Hx" in destruct (aview segs H mem x) eqn:Hx; [|discriminate Hw];
  apply (aview_byte segs) in Hx; destruct Hx as (? & _ & -> & ?) end.
injection Hw as <-. lia.
Qed.

Lemma ex_rdword_kept : forall (r r' : reader) a, (forall i, 0 <= i < 8 -> r' (a + i) = r (a + i)) ->
  rdword r' a = rdword r a.
Proof.
intros r r' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma ex_garr8_kept : forall H H' (m m' : word -> option byte) base l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' m' (base + j) = aview segs H m (base + j)) ->
  garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H' m') base l.
Proof.
intros H H' m m' base l HK HG. apply (garr8_frame segs _ _ _ _ HG). intros a Ha.
apply (mbyte_of_aview segs). replace a with (base + (a - base)) by lia. apply HK. lia.
Qed.

(* The braid relation check_round_trip asks, from the copy at res (the body) and the upstream buffer at upb (the
   braid of the body). Sample (ch, s) of pcm is byte 3 (ch * 12 + s) + j of braid_out, which is body[50 + braid_pos],
   i.e. the byte of audio = res + 50 at 3 (s w + 2 (ch / 2)) + braid_off ch j. *)
Lemma ex_crt_braid : forall (H : word -> bool) mem res upb (body : list byte) w,
  garr8 segs (mrestrict H mem) res (map (fun b : byte => bv_unsigned b) body) ->
  garr8 segs (mrestrict H mem) upb (map (fun b : byte => bv_unsigned b) (CDec.braid_out body w 12)) ->
  Z.of_nat (length body) = 52 + 36 * w -> Z.even w = true -> 2 <= w ->
  dec_crt_braid (aview segs H mem) (res + 50) upb w 12.
Proof.
intros H mem res upb body w GR GU Hlen Hev Hw ch s j Hch Hs Hj.
assert (Hw2 : w mod 2 = 0) by (rewrite Zmod_even, Hev; reflexivity).
pose proof (ex_braid_off_range ch j) as Hoff.
set (i := 3 * (ch * 12 + s) + j).
assert (Hi0 : 0 <= i < 36 * w) by (unfold i; lia).
assert (Hi3 : i / 3 = ch * 12 + s) by (unfold i; lia).
assert (Hs12 : (ch * 12 + s) mod 12 = s) by lia.
assert (Hc12 : (ch * 12 + s) / 12 = ch) by lia.
assert (Hj3 : i mod 3 = j) by (unfold i; lia).
set (k := 50 + (3 * (s * w + 2 * (ch / 2)) + DCBc.braid_off ch j)).
assert (Hsw : 0 <= s * w <= 11 * w) by nia.
assert (Hk0 : 0 <= k < 52 + 36 * w) by (unfold k; lia).
assert (HinU : (Z.to_nat i < length (map (fun b : byte => bv_unsigned b) (CDec.braid_out body w 12)))%nat)
  by (rewrite length_map, ex_len_braid_out; lia).
pose proof (garr8_mbyte segs _ _ _ _ GU HinU) as M1.
rewrite Z2Nat.id in M1 by lia.
rewrite ex_nth_map_bv in M1 by (rewrite ex_len_braid_out; lia).
rewrite ex_nth_braid_out in M1 by lia.
rewrite Z2Nat.id in M1 by lia.
unfold CDec.braid_byte in M1. rewrite Hi3, Hs12, Hc12, Hj3, ex_braid_pos in M1 by lia. fold k in M1.
assert (HinR : (Z.to_nat k < length (map (fun b : byte => bv_unsigned b) body))%nat)
  by (rewrite length_map; lia).
pose proof (garr8_mbyte segs _ _ _ _ GR HinR) as M2.
rewrite Z2Nat.id in M2 by lia.
rewrite ex_nth_map_bv in M2 by lia.
exists (bv_unsigned (nth (Z.to_nat k) body (Z_to_bv 8 0))). unfold aview. cbv beta. split.
- replace (upb + 3 * (ch * 12 + s) + j) with (upb + i) by (unfold i; lia).
  rewrite M1. cbn [option_map]. rewrite Z_to_bv_unsigned. f_equal.
  apply bv_wrap_small. apply bv_unsigned_in_range.
- replace (res + 50 + 3 * (s * w + 2 * (ch / 2)) + DCBc.braid_off ch j) with (res + k) by (unfold k; lia).
  rewrite M2. cbn [option_map]. rewrite Z_to_bv_unsigned. f_equal.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* The read-only view at the end of a caller's journal with no open FILE, on the read-only reads DEC_RO_RD
   (check_round_trip_cg.v dec_rom_view_rd): the journal's image clause (YCbq.v:362) keeps the entry view there, since
   dec_ro_rd_scoped keeps those bytes off the owned statics and errno. *)
Lemma ex_crt_ro_scoped : forall B, dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  forall STK sp0 ly S W0 mem0 md0 own ly' S' W' mem' md' k,
  @ajournal rc dec_A_sink_head segs B STK sp0 [] ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  rom_view segs W0 mem0 -> dec_rom_view_rd W' mem'.
Proof.
intros B HO HE STK sp0 ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ HR0 a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (dec_ro_rd_scoped B HO HE a Ha) as [Hno Hne].
destruct (dec_ro_rd_rom_clean a Ha) as [Hrom _].
rewrite (F3 a); [exact (HR0 a Hrom) | | exact Hno | exact Hne | apply fp_spares_closed; intros (r & [] & _)].
destruct Hrom as (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr].
Qed.
End mh.

(* ------------------------------------------------------------------ *)
(* 3. The symbolic state at +0x960                                      *)
(* ------------------------------------------------------------------ *)

(* Atom 32 is the shadow base (the token engine's Bx; no shadow access occurs in the five instructions), atom 33 the
   word res + 50 at 64(s1) that `ld s2,64(s1)` reads: one read-only chunk of a region on s1 (atom 9). *)
Definition ex_rg : YP09.region := YP09.mkRegion (Some 9%nat) 64 72 64 64 [YP09.mkChunk 64 (CVal 8 (SOff 33 0))].
Definition ex_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ex_ss : sstate := mkSS 0x960 sr_atoms [ex_rg] None ex_facts.
Definition ex_extra (v : Z) : list word := [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 v].
Ltac awr_ro_rec := first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]; awr_ro_rec ].

Section en. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation SEGS := (@pa_segs _ decode_listing PI_decode).
Local Abbreviation VAL := (@pa_val _ decode_listing PI_decode).
Local Abbreviation BASE := (@pa_val _ decode_listing PI_decode A_TEXT).
Definition EEX (regs : bvmap 5 word) (v : Z) : env := Eimg (PI := PI_decode) (Ereg regs (ex_extra v)).
Lemma ex_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem sp1 v,
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  rdword (aview SEGS (w_H W) mem) (sp1 + 64) = Some v ->
  st_ok_pi SEGS VAL (EEX regs v) ex_ss
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + 0x960)) mem (YK11.seg_rom SEGS))).
Proof.
intros W regs mem sp1 v H9 Hsp1 Hal R64.
pose proof (ex_rdword_range (w_H W) mem _ _ R64) as Hv.
rewrite restrict_mkst_fx. unfold ex_ss.
set (E := EEX regs v).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ex_extra v)) n)
  by (intros n Hn; unfold E, EEX; apply Eimg_low; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9;
      apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold ex_rg, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ sp1 64 8 (SOff 33 0) v);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  exact (val_mem_of_rdword SEGS _ _ _ _ R64).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I].
  cbn [ex_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.
End en.

(* The value of register r in the machine state of a symbolic state HS (a Theorem Labs lane's reg_at). *)
Ltac reg_at HS r v H tac :=
  lazymatch type of HS with st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : YK11.getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* ------------------------------------------------------------------ *)
(* 4. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Section x. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := dec_A_sink_head.
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
Local Abbreviation segs := decodesegs0.

Theorem ex_crt_ok : ex_crt_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold ex_crt_stmt.
intros _ _ HOIS HNOE LAWS _ AML _ HCRT cx W' c' HBASE HROMcx H960.
unfold ex_st_960 in H960.
destruct H960 as (fx' & ly' & S' & regs' & mem' & md' & res & upb & -> & Hfrm & HCORE & HPERM & Hres4 & Hupb4 &
  HMLE & HMOK & HFR & R20 & R22 & R23 & HUP & GRES & GUPB & HFSH & HSLOT).
destruct HCORE as (HJ & Hfrs & R8 & R9 & Rsp & Hsp1b & Hsp1al & Rgp & Rtp & HSAV & HF4096 & HFal & HFpres & HFL &
  HPAYb & HPAYg).
unfold dec_a_base, dec_lib_pre_x in HBASE.
(* dec_lib_pre_x by projection and by type, never by position *)
pose proof (proj1 HBASE) as HAFN.
assert (Hra0 : raZ (d_regs cx) = RA_LLVMF) by (decompose [and] HBASE; assumption).
assert (Hnl : d_n cx = Z.of_nat (length (d_pl cx))) by (decompose [and] HBASE; assumption).
assert (Hev0 : st_nev (d_S cx) + DEC_EV_LIB <= EV_MAX) by (decompose [and] HBASE; assumption).
assert (Hlive0 : blocks_bytes (d_S cx) + DEC_LIVE_LIB <= LIVE_MAX) by (decompose [and] HBASE; assumption).
assert (Hn26' : d_n cx < 2 ^ 26)
  by (decompose [and] HBASE; match goal with H : _ \/ _ |- _ => destruct H as [[? _] | [? _]]; lia end).
destruct HAFN as (_ & _ & Hra4096 & _ & _ & _ & _ & Hch0 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & Hbot & _ & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hstkv : DEC_LLVMF_STK = 32768) by reflexivity.
assert (HCSTK : DEC_CRT_STK = 16480) by reflexivity.
unfold dec_a_saved in HSAV.
(* the geometry of the accepted upstream decode *)
destruct (ex_up_geom _ _ _ _ HUP) as (w & Hlenw & Hwev & Hwr & Hupn & Hupr).
assert (Huo : ex_uolen cx = 36 * w).
{ unfold ex_uolen. rewrite Hupr. unfold dec_a_uolen.
  replace (0 <? w) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
assert (Hbl : Z.of_nat (length (d_body cx)) = dec_a_len (d_n cx)) by (unfold d_body; apply ex_body_len; exact Hnl).
assert (Hn26 : dec_a_len (d_n cx) < 2 ^ 26) by (unfold dec_a_len; lia).
assert (RQR : req_size (dec_a_len (d_n cx)) = dec_a_len (d_n cx))
  by (unfold req_size; destruct (Z.eqb_spec (dec_a_len (d_n cx)) 0); lia).
assert (RQU : req_size (ex_uolen cx) = ex_uolen cx)
  by (unfold req_size; destruct (Z.eqb_spec (ex_uolen cx) 0); lia).
assert (Hsp1r : 2 ^ 46 <= d_sp1 cx <= 2 ^ 47) by lia.
(* the two blocks the call reads *)
assert (InR : In (res, dec_a_len (d_n cx)) (ablocks B ly' S')).
{ apply (Permutation_in _ (Permutation_sym HPERM)). unfold ex_blocks. apply in_or_app. right.
  cbn [app In]. left. reflexivity. }
assert (InU : In (upb, ex_uolen cx) (ablocks B ly' S')).
{ apply (Permutation_in _ (Permutation_sym HPERM)). unfold ex_blocks. apply in_or_app. right.
  cbn [app In]. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR InR) as (_ & HR4096 & HRceil & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR InU) as (_ & HU4096 & HUceil & _).
(* the fake frame *)
assert (HinF : In (DEC_FCLASS, d_fpos cx) (frames S')) by (rewrite Hfrs; left; reflexivity).
assert (HFaddr : frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds segs B LAWS ly' S' W' mem' md' DEC_FCLASS (d_fpos cx) HAR HinF) as (_ & HFceil & _).
rewrite HFaddr in HFceil. change (fs_frame_bytes DEC_FCLASS) with 64 in HFceil.
(* +0x960 .. +0x970 and the jal at +0x974 *)
pose proof (ex_entry (fx := fx') W' regs' mem' (d_sp1 cx) (res + 50) R9 Hsp1r Hsp1al HSLOT) as HS.
assert (HEI : img_env (@pa_val _ decode_listing PI_decode) A_LIM (EEX regs' (res + 50))) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ decode_listing PI_decode) (SOff 32 0) (@nil shent) (EEX regs' (res + 50))
  (mrestrict (w_H W') mem')) by constructor.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (EEX regs' (res + 50)) n = YK11.getr regs' r)
  by (intros nn r Hn; unfold EEX; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew (EEX regs' (res + 50)) 33 = Z_to_bv 64 (res + 50))
  by (unfold EEX; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 1)).
pose proof (paj_run (fx := fx') (rc := rc) (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUN.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ decode_listing PI_decode) Wx
    (mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + 0x960)) mem'
      (YK11.seg_rom (@pa_segs _ decode_listing PI_decode))) md') Q) end.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  awr_ro_rec. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in *; clearbody md1 end.
(* the run wrote nothing *)
assert (KR0 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha.
  lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1) |- _ =>
    refine (kept_of_frame Ex rsx Hh m0 m1 (fun _ => False) HFr _ a Ha (fun x => x));
    let wsv := eval vm_compute in (windows rsx) in change (windows rsx) with wsv end.
  intros bb wlo whi x Hin Hr. cbn [In] in Hin. destruct Hin as [Hq | []]. injection Hq as <- <- <-. lia. }
(* the registers at the call *)
reg_at HS (1%bv : bv 5) (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + 2424)) Q1
  ltac:(apply codeptr_val; assumption).
reg_at HS (10%bv : bv 5) (w64 (res + 50)) Q10
  ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (18%bv : bv 5) (w64 (res + 50)) Q18
  ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (11%bv : bv 5) (w64 upb) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R23).
reg_at HS (12%bv : bv 5) (w64 w) Q12
  ltac:(cbn [sv_denot]; rewrite (EE 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; rewrite R22, Hupr;
        reflexivity).
reg_at HS (13%bv : bv 5) (w64 12) Q13 ltac:(reflexivity).
reg_at HS (2%bv : bv 5) (YK11.getr regs' 2) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (3%bv : bv 5) (YK11.getr regs' 3) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (4%bv : bv 5) (YK11.getr regs' 4) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (8%bv : bv 5) (YK11.getr regs' 8) Q8
  ltac:(cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (9%bv : bv 5) (YK11.getr regs' 9) Q9
  ltac:(cbn [sv_denot]; rewrite (EE 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (19%bv : bv 5) (YK11.getr regs' 19) Q19
  ltac:(cbn [sv_denot]; rewrite (EE 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (20%bv : bv 5) (YK11.getr regs' 20) Q20
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (21%bv : bv 5) (YK11.getr regs' 21) Q21
  ltac:(cbn [sv_denot]; rewrite (EE 21%nat 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (22%bv : bv 5) (YK11.getr regs' 22) Q22
  ltac:(cbn [sv_denot]; rewrite (EE 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (23%bv : bv 5) (YK11.getr regs' 23) Q23
  ltac:(cbn [sv_denot]; rewrite (EE 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (27%bv : bv 5) (YK11.getr regs' 27) Q27
  ltac:(cbn [sv_denot]; rewrite (EE 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HspR1 : spZ (ms_regs ms) = d_sp1 cx) by (unfold spZ; rewrite Q2; exact Rsp).
assert (Hs0R1 : s0Z (ms_regs ms) = d_sp0 cx) by (unfold s0Z; rewrite Q8, R8; apply unsigned_lit_small; lia).
assert (HraR1 : raZ (ms_regs ms) = DEC_A_LLVMF + 0x978) by (unfold raZ; rewrite Q1; vm_compute; reflexivity).
(* the frame-pointer chain at the call *)
assert (HCH : exists ch, achain ly' (aview segs (w_H W') (ms_mem ms)) (spZ (ms_regs ms)) (s0Z (ms_regs ms)) ch /\
  In (raZ (ms_regs ms) :: spine ch) (CTX_check_round_trip RA_LLVMF)).
{ rewrite HspR1, Hs0R1, HraR1.
  destruct (Z_lt_le_dec (d_sp0 cx) (ly_top ly' - 16)) as [Hlt | Hge].
  - exists [(d_sp0 cx, RA_LLVMF, s0Z (d_regs cx))]. split.
    + apply (achain_push ly' (aview segs (w_H (d_W cx)) (d_mem cx)) _ (d_sp0 cx) (s0Z (d_regs cx)) RA_LLVMF []
        (d_sp1 cx)).
      * apply (achain_ly_top (d_ly cx) ly'); [exact Etop | exact Hch0].
      * rewrite Etop. lia.
      * intros a Ha. rewrite KR0 by lia. apply F1; lia.
      * rewrite (ex_rdword_kept (aview segs (w_H W') mem')) by (intros i Hi; apply KR0; lia).
        pose proof (proj1 (Forall_forall _ _) HSAV (8, 1) ltac:(unfold dec_a_saved_at; cbn [In]; left; reflexivity))
          as S8.
        cbn [fst snd] in S8. rewrite S8. f_equal. exact Hra0.
      * rewrite (ex_rdword_kept (aview segs (w_H W') mem')) by (intros i Hi; apply KR0; lia).
        pose proof (proj1 (Forall_forall _ _) HSAV (16, 8)
          ltac:(unfold dec_a_saved_at; cbn [In]; right; left; reflexivity)) as S16.
        cbn [fst snd] in S16. rewrite S16. reflexivity.
      * rewrite <- Hra0. exact Hra4096.
      * lia.
      * lia.
      * exact Hlt.
      * lia.
    + cbn [spine map fst snd]. unfold CTX_check_round_trip, DEC_LLVMF_RA_CRT. cbn [map flat_map app In].
      right. right. right. left. reflexivity.
  - exists []. split.
    + left. split; [right; left; lia | reflexivity].
    + cbn [spine map]. unfold CTX_check_round_trip, DEC_LLVMF_RA_CRT. cbn [map flat_map app In].
      right. right. left. reflexivity. }
destruct HCH as (ch & Pch & Pctx).
(* the braid relation, the meter *)
assert (HBR : dec_crt_braid (aview segs (w_H W') (ms_mem ms)) (res + 50) upb w 12).
{ apply (ex_crt_braid (w_H W') (ms_mem ms) res upb (d_body cx) w); [| | lia | exact Hwev | lia].
  - apply (ex_garr8_kept (w_H W') (w_H W') mem' (ms_mem ms) res _); [|exact GRES].
    intros j Hj. rewrite length_map, Hbl in Hj. apply KR0. lia.
  - rewrite <- Hupn. apply (ex_garr8_kept (w_H W') (w_H W') mem' (ms_mem ms) upb _); [|exact GUPB].
    intros j Hj. rewrite length_map, ex_len_braid_out, Hupn in Hj. apply KR0. rewrite RQU, Huo in HUceil. lia. }
assert (HCOST : dec_crt_cost MT w 12 <= dec_crt_cost_max MT).
{ unfold dec_crt_cost, dec_crt_cost_max.
  pose proof (mo_malloc_mono MT AML (4 * (w * 12)) 1920 ltac:(lia)).
  pose proof (mo_malloc_mono MT AML (8 * w) 1016 ltac:(lia)).
  pose proof (mo_malloc_mono MT AML (3 * (w * 12)) 1440 ltac:(lia)). lia. }
assert (HLIVE : blocks_bytes S' + DEC_CRT_LIVE <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HPERM). unfold ex_blocks. rewrite !bsum_app.
  rewrite (blocks_bytes_bsum B (d_ly cx) (d_S cx)) in Hlive0.
  rewrite !bsum_cons. cbn [snd]. change (bsum []) with 0.
  rewrite Huo. unfold DEC_CRT_LIVE, LIVE_MAX. unfold DEC_LIVE_LIB, LIVE_MAX in Hlive0.
  lia. }
(* the calloc depth: astk_ok's ly_bot ly + STK < sp0 + ASTACK, ly_top kept by layout_le, sp = sp1 >= sp0 - 240 *)
assert (HDEPTH : ly_bot ly' + DEC_CALLOC_DEPTH + DEC_CRT_FRAME < spZ (ms_regs ms)).
{ rewrite HspR1. unfold ly_bot in Hbot |- *. rewrite Etop. unfold DEC_CALLOC_DEPTH, DEC_CRT_FRAME, ASTACK in *. lia. }
(* the read-only view at the call memory, on the DEC_RO_RD bytes the contract asks (dec_rom_view_rd) *)
pose proof (ex_crt_ro_scoped B HOIS HNOE _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROMcx) as HROMs.
(* the call: check_round_trip (res + 50, upb, w, 12) by its contract *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (YK11.mkst rg (Z_to_bv 64 (decode_sigma DS_check_round_trip)) mm rom) mdx) Q) end.
eapply SRr_mono.
{ exact (HCRT fx' DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly' S' W' (ms_mem ms) md1 dec_ev_86c (ms_regs ms)
    (res + 50) upb w 12 res (dec_a_len (d_n cx)) upb (ex_uolen cx) (dec_rest_86c MT) ch HJ
    ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_decode)); [lia | reflexivity])
    ltac:(rewrite HraR1; unfold DEC_A_LLVMF, AF_LLVMFuzzerTestOneInput, decode_text; lia)
    ltac:(rewrite Q3; exact Rgp) ltac:(rewrite Q4; exact Rtp) Q10 Q11 Q12 Q13 Pch Pctx
    ltac:(rewrite HspR1; lia) ltac:(rewrite HspR1, Hstkv, HCSTK; lia) ltac:(rewrite HspR1; lia)
    Hfrm Hwev ltac:(lia) ltac:(lia) ltac:(lia) HDEPTH
    InR ltac:(lia) ltac:(lia) InU ltac:(lia) ltac:(rewrite Huo; lia)
    HBR HROMs ltac:(unfold dec_ev_86c, DEC_CRT_EV; unfold DEC_EV_LIB in Hev0; lia) HLIVE
    HMOK ltac:(unfold dec_rest_86c; pose proof (mo_free_nonneg MT AML); lia)). }
intros W2 c2 _ Hpost.
destruct Hpost as (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfrm2 & HJ2 & HP2 & Hfr2 & HPerm2 & HK & HMLE2).
destruct HK as (K1 & K2 & _ & K4 & _ & _).
(* what the call kept: the words above sp1, the heap blocks, the fake frame and its shadow *)
assert (KA : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (d_sp1 cx - DEC_CRT_STK <= a < d_sp1 cx) ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a).
{ intros a Ha Hn. rewrite K1 by (first [lia | rewrite HspR1; exact Hn]). apply KR0. lia. }
assert (KB : forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
  aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W') mem' (b + i)).
{ intros b m i Hin Hi. etransitivity; [exact (K2 b m i Hin Hi (fun x => x))|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4096 & Hbceil & _). apply KR0. lia. }
assert (KF : forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a).
{ intros a Ha. etransitivity.
  { apply (K4 DEC_FCLASS (d_fpos cx) a HinF); [| exact (fun x => x)].
    left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite HFaddr. change (fs_frame_bytes DEC_FCLASS) with 64. lia. }
  apply KR0. lia. }
assert (KSH : forall i, 0 <= i < 8 ->
  aview segs (w_H W2) mem2 (d_SH cx + i) = aview segs (w_H W') mem' (d_SH cx + i)).
{ intros i Hi. etransitivity.
  { apply (K4 DEC_FCLASS (d_fpos cx) (d_SH cx + i) HinF); [| exact (fun x => x)].
    right. unfold in_zr. cbn [fst snd]. rewrite HFaddr. change (fs_frame_bytes DEC_FCLASS / 8) with 8.
    unfold d_SH. lia. }
  apply KR0. unfold d_SH, shadow_addr, SHADOW_OFF. lia. }
unfold ex_st_978.
exists fx2, ly2, S2, regs2, mem2, md2, res, upb.
split; [rewrite Q1; reflexivity|].
split; [exact Hfrm2|].
split.
{ split; [exact HJ2|].
  split; [rewrite Hfr2; exact Hfrs|].
  split; [transitivity (YK11.getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | rewrite Q8; exact R8]|].
  split; [transitivity (YK11.getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | rewrite Q9; exact R9]|].
  split; [unfold spZ at 1; transitivity (bv_unsigned (YK11.getr (ms_regs ms) 2));
    [f_equal; exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact HspR1]|].
  split; [exact Hsp1b|]. split; [exact Hsp1al|].
  split; [transitivity (YK11.getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | rewrite Q3; exact Rgp]|].
  split; [transitivity (YK11.getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | rewrite Q4; exact Rtp]|].
  split.
  { unfold dec_a_saved. apply Forall_forall. intros o Ho.
    pose proof (ex_saved_at_range o Ho) as Hor.
    rewrite (ex_rdword_kept (aview segs (w_H W') mem')) by (intros i Hi; apply KA; rewrite ?HCSTK; lia).
    exact (proj1 (Forall_forall _ _) HSAV o Ho). }
  split; [exact HF4096|]. split; [exact HFal|].
  split.
  { intros a Ha. apply (apresent_transfer segs (w_H W') (w_H W2) mem' mem2 a); [lia | | exact (KF a Ha) | exact (HFpres a Ha)].
    apply (frm_img segs B LAWS ly' S' W' mem' md' DEC_FCLASS (d_fpos cx) a HAR HinF).
    rewrite HFaddr. change (fs_frame_bytes DEC_FCLASS) with 64. lia. }
  split; [rewrite (ex_rdword_kept (aview segs (w_H W') mem')) by (intros i Hi; apply KF; lia); exact HFL|].
  split; [intros Hn0; apply (Permutation_in _ (Permutation_sym HPerm2)); exact (HPAYb Hn0)|].
  destruct (Z_lt_le_dec 0 (d_n cx)) as [Hn0 | Hn0].
  - pose proof (HPAYb Hn0) as InP.
    apply (ex_garr8_kept (w_H W') (w_H W2) mem' mem2 (d_p cx) _); [|exact HPAYg].
    intros j Hj. rewrite length_map, <- Hnl in Hj.
    pose proof (req_size_pos (d_n cx) ltac:(lia)). apply (KB _ _ j InP). lia.
  - destruct (d_pl cx) as [|b0 pl0] eqn:Epl; [apply garr8_nil|].
    try rewrite Epl in Hnl. cbn [length] in Hnl. lia. }
split; [exact (Permutation_trans HPerm2 HPERM)|].
split; [exact Hres4|]. split; [exact Hupb4|].
split.
{ eapply mle_weaken; [exact AML | eapply mle_station; [exact AML | exact HMLE | exact HMLE2] | lia]. }
split.
{ eapply (mok_station MT S' S2 (dec_rest_86c MT) (dec_crt_cost MT w 12)); [exact AML | exact HMOK | exact HMLE2 | |].
  - pose proof (mo_free_nonneg MT AML). lia.
  - unfold dec_rest_86c. lia. }
split.
{ unfold dec_a_fr in HFR |- *. destruct HFR as (F19 & F21 & F27).
  split; [transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | rewrite Q19; exact F19]|].
  split; [transitivity (YK11.getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | rewrite Q21; exact F21]|].
  transitivity (YK11.getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | rewrite Q27; exact F27]. }
split; [transitivity (YK11.getr (ms_regs ms) 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact Q18]|].
split; [transitivity (YK11.getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | rewrite Q20; exact R20]|].
split; [transitivity (YK11.getr (ms_regs ms) 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | rewrite Q22; exact R22]|].
split; [transitivity (YK11.getr (ms_regs ms) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | rewrite Q23; exact R23]|].
split; [exact HUP|].
split.
{ apply (ex_garr8_kept (w_H W') (w_H W2) mem' mem2 res _); [|exact GRES].
  intros j Hj. rewrite length_map, Hbl in Hj. apply (KB _ _ j InR). rewrite RQR. lia. }
split.
{ apply (ex_garr8_kept (w_H W') (w_H W2) mem' mem2 upb _); [|exact GUPB].
  intros j Hj. rewrite length_map, ex_len_braid_out, Hupn in Hj. apply (KB _ _ j InU). rewrite RQU, Huo. lia. }
unfold dec_a_fsh in HFSH |- *. destruct HFSH as (L1 & L4 & L5 & L6).
split; [intros i Hi; rewrite KSH by lia; exact (L1 i Hi)|].
split; [rewrite KSH by lia; exact L4|].
split; [rewrite KSH by lia; exact L5|].
intros i Hi; rewrite KSH by lia; exact (L6 i Hi).
Qed.

End x.
