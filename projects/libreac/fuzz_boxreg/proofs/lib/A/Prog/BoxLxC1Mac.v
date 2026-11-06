(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryUnset), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryUnset.v, with its module paths and module names changed; 2736 of its 2810 lines of code are new or changed and 731 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC1g YC1h YC81 YC85 BoxFrame BoxCJ BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require ReacBoxregFind ReacBoxregAdd LowestFree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxDefs BoxLxSeat.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require
Boxreg LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_case1
reac_boxreg_add_c reac_boxreg_find_c lowest_free_c reac_boxreg_add_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxC1Defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA BS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_bcmp).
Hypothesis TFIND : ReacBoxregFind.treac_boxreg_find_spec B.
Hypothesis TADD : ReacBoxregAdd.treac_boxreg_add_spec B.
Hypothesis TLOWFREE : LowestFree.tlowest_free_spec B.
Hypothesis HZERO : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 6))
  (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis HRMB : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 4)) [0; 64; 171; 0; 0].
Hypothesis HMRG : Forall (fun g => IMG_LO + 64 <= fst g /\ fst g + snd g + 64 <= IMG_HI) BX_G.
Variable POST : bcx -> world SEGS -> config -> Prop.

(* ---- a Theorem Labs lane: 0x803a8 (GP_T 1) .. 0x806cc (PC1_nch): read_mac (&in, op & 4, mac) inlined, then the nch byte ----

   The walk runs in the engine's own symbolic state, built from the machine state at GP_T 1 (as GrantEntryUnset.v):
   the environment `cm_E` is the current registers (atoms 0 .. 31) and the phase's values (atoms 32 ..):
     32 the input cursor c_p + pos, 33 the bytes left c_n - pos, 34 the frame F,
     35 .. 41 the input bytes at the cursor (byte j is the input byte pos + j, 0 past the input).
   s2 (atom 18) holds SHADOW_OFF, so the shadow address `srli rd,a,3; add rd,rd,s2` of a cursor byte reaches the
   token engine as `match_x`'s pattern with Bx = SOff 18 0. The regions: the two windows of the spill area the
   piece stores (slot 0x58; the cursor slots 0x88 / 0x90, with slot 0x70 = mac read beside them), mac (F + 32 ..
   F + 38) and the input bytes at the cursor. The rest of the machine frame, the frame, prev, the registry, the
   saved words, the frame's shadow and the input are kept by `frame_of` (and by memcpy's own frame).
   Each path is unrolled under a case split on kk = min (bytes left, cap): the atom fact of atom 33 is [kk, kk]
   (kk < cap) or [cap, 2 ^ 26], so the engine decides every `beqz a1`; a real shadow entry over the kk input bytes
   at the cursor (and one over mac) lets the engine take each cursor shadow test without an obligation. *)

Local Ltac cm_zbool :=
repeat match goal with
| H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
| H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
end.

Definition CM_SB : Z := 0x7fff8000.
Definition CM_CEIL : Z := 0x7fffff800000.
Definition cm_Bx : sv := SOff 18%nat 0.
Definition cm_span : Z * Z := (CM_SB, CM_SB + 2 ^ 44 - 1).
(* slot 0x58 (nch), stored *)
Definition cm_spill_lo : YP09.region := YP09.mkRegion (Some 9%nat) 0x58 0x60 0x58 0x60 [].
(* slot 0x70 (mac, read) and the cursor slots 0x88 / 0x90 (stored) *)
Definition cm_spill_hi : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x70 0x98 0x88 0x98
    [YP09.mkChunk 0x70 (CVal 8 (SOff 34 32)); YP09.mkChunk 0x88 (CVal 8 (SOff 32 0));
     YP09.mkChunk 0x90 (CVal 8 (SOff 33 0))].
(* mac = F + 32 .. F + 38 *)
Definition cm_frame (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 34%nat) 32 38 32 38 cs.
(* kk input bytes at the cursor, atom 35 + j at offset j *)
Definition cm_inb (kk : nat) : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 (Z.of_nat kk) 0 0
    (map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (35 + j) 0))) (seq 0 kk)).
Definition cm_af0 : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF CM_SB CM_SB 0);
   (32%nat, mkAF 4096 CM_CEIL 0); (34%nat, mkAF 4096 CM_CEIL 6)].
Definition cm_ss0 : sstate :=
  mkSS PC1_mac0 sr_atoms [cm_spill_lo; cm_spill_hi; cm_frame []] None (mkFacts cm_af0 [] []).
Definition cm_SH0 : list shent := [mkSHE 34 32 38].
Definition cm_SH (kk : nat) : list shent :=
  if (kk =? 0)%nat then cm_SH0 else cm_SH0 ++ [mkSHE 32 0 (Z.of_nat kk)].
(* The fact of atom 33 (bytes left) under the case kk of the split at cap. *)
Definition cm_remf (cap kk : nat) : afact :=
  if (kk <? cap)%nat then mkAF (Z.of_nat kk) (Z.of_nat kk) 0 else mkAF (Z.of_nat cap) (2 ^ 26) 0.
(* The input byte j at the cursor (0 past the input). *)
Definition cm_inbyte (cx : bcx) (pos : Z) (j : nat) : Z :=
  if (Z.to_nat pos + j <? length (c_pl cx))%nat
  then bv_unsigned (nth (Z.to_nat pos + j) (c_pl cx) (Z_to_bv 8 0)) else 0.
Definition cm_ex (cx : bcx) (fp pos : Z) : list word :=
  map w64 ([c_p cx + pos; c_n cx - pos; gF cx fp] ++ map (cm_inbyte cx pos) (seq 0 7)).
Definition cm_E (regs : bvmap 5 word) (cx : bcx) (fp pos : Z) : env := Eimg (Ereg regs (cm_ex cx fp pos)).

(* ---- small facts on the environment and the chunks ---- *)
Lemma cm_ew_ex : forall (regs : bvmap 5 word) extra j, (j < 200)%nat ->
  ew (Eimg (Ereg regs extra)) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j Hj. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

Lemma cm_ex_byte : forall cx fp pos j, (j < 7)%nat ->
  nth (3 + j) (cm_ex cx fp pos) (Z_to_bv 64 0) = w64 (cm_inbyte cx pos j).
Proof. intros cx fp pos j Hj. do 7 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Lemma cm_inbyte_range : forall cx pos j, 0 <= cm_inbyte cx pos j < 256.
Proof.
  intros cx pos j. unfold cm_inbyte. destruct (_ <? _)%nat; [|lia].
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat pos + j) (c_pl cx) (Z_to_bv 8 0))) as H.
  change (bv_modulus 8) with 256 in H. exact H.
Qed.

Lemma cm_U : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. unfold w64. apply unsigned_lit_small. exact Hv. Qed.

Lemma cm_UO : forall E n v x, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 -> U E (SOff n x) = v + x.
Proof.
  intros E n v x H Hv Hx. rewrite U_SOff, H. unfold w64. rewrite unsigned_lit_small by exact Hv.
  apply zcanon_id. unfold M64. lia.
Qed.

Lemma cm_den : forall E n v x, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof. intros E n v x H Hv Hx. rewrite denot_lit_U, (cm_UO E n v x H Hv Hx). reflexivity. Qed.

Lemma cm_chunk8 : forall E (H : word -> bool) (m : word -> option byte) base off e v,
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H m) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H m) base (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros E H m base off e v He Hv Hr.
  apply (chunk_ok_val SEGS E _ base off 8%N e v He); [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
  cbn [N.to_nat]. apply (val_mem_of_rdword SEGS H m). exact Hr.
Qed.

Lemma cm_chunk1 : forall E (H : word -> bool) (m : word -> option byte) base off e v,
  sv_denot E e = Z_to_bv 64 v -> aview SEGS H m (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H m) base (YP09.mkChunk off (CVal 1 e)).
Proof.
  intros E H m base off e v He Hr.
  destruct (val_mem1_of_aview SEGS H m (base + off) v Hr) as [Hvm Hv].
  apply (chunk_ok_val SEGS E _ base off 1%N e v He); [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | exact Hvm].
Qed.

(* A chunk of a region, read back as a value of memory. *)
Lemma cm_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem SEGS m (b + od) (N.to_nat w) v.
Proof.
  intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
  exact (val_of_chunk_ok SEGS E m b od w e v Hck He Hv Hw).
Qed.

(* The margins of read_mac.base (A_OBJ 4), from HMRG. *)
Lemma cm_rmb_marg : IMG_LO + 64 <= VAL (A_OBJ 4) /\ VAL (A_OBJ 4) + 5 + 64 <= IMG_HI.
Proof.
  rewrite Forall_forall in HMRG. exact (HMRG (VAL (A_OBJ 4), 5) ltac:(unfold BX_G; cbn [In]; tauto)).
Qed.

(* ---- the geometry of the phase ---- *)
Section cm_geo_s.
Variables (cx : bcx) (fp k : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model).
Variable r : Z.
Hypothesis HB : gb_base B MT cx.
Hypothesis HJ : ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k.
Hypothesis HFR : frames S3 = [(GB_CID, fp)].
Hypothesis HBLK : gblk1 B cx ly3 S3 r.

Lemma cm_geo :
  (spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + 32768 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
   spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256 /\ c_sp1 cx mod 32 = 0) /\
  (4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512 /\ gF cx fp mod 64 = 0 /\
   (gF cx fp + 512 <= IMG_LO \/ IMG_TOP <= gF cx fp)) /\
  (r mod 16 = 0 /\ 4096 <= r /\ r + 288 <= alloc_ceiling /\ in_app r 288 /\ In (r, REG_SIZE) (ablocks B ly3 S3)) /\
  (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r) /\
  ((c_n cx = 0 /\ c_p cx = GB_EMPTY) \/
   (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ 4096 <= c_p cx /\
    c_p cx + c_n cx <= alloc_ceiling /\ in_app (c_p cx) (c_n cx) /\
    (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx) /\
    (c_p cx + c_n cx <= r \/ r + 288 <= c_p cx))).
Proof.
  pose proof (gb_sp_facts B MT cx HB) as (Hs1 & Hs2 & Hs3 & Hs4).
  pose proof (gb_sp1_al B MT cx HB) as Hs5.
  pose proof (gb_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF1 & HF2 & HF3 & HF6 & _).
  pose proof (gb_F_al B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as HF4.
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
  pose proof HJ as (HAR3 & _).
  assert (Hrb : In (r, REG_SIZE) (ablocks B ly3 S3))
    by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 Hrb) as (Hr16 & Hr4096 & Hrc & Hria & _).
  change (req_size REG_SIZE) with 288 in Hrc, Hria.
  destruct (al_sep _ _ LAWS _ _ _ _ _ HAR3) as [HSEP _].
  rewrite HFR in HSEP. cbn [map fst snd] in HSEP. rewrite EF in HSEP.
  change (fs_frame_bytes GB_CID) with 512 in HSEP.
  unfold gblk1 in HBLK. rewrite HBLK, map_app in HSEP. cbn [map fst snd] in HSEP.
  change (req_size REG_SIZE) with 288 in HSEP.
  rewrite <- app_assoc in HSEP. cbn [app] in HSEP.
  assert (DRF : r + 288 <= gF cx fp \/ gF cx fp + 512 <= r).
  { pose proof (pairwise_In zdisjoint _ (r, 288) (gF cx fp, 512)
      (map (fun b => (fst b, req_size (snd b))) (ablocks B (c_ly cx) (c_S cx)) ++ [(r, 288)]) [(gF cx fp, 512)]
      ltac:(rewrite <- app_assoc; reflexivity) HSEP ltac:(apply in_or_app; right; left; reflexivity)
      ltac:(left; reflexivity)) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
  split; [exact (conj Hs1 (conj Hs2 (conj Hs3 (conj Hs4 Hs5))))|].
  split; [exact (conj HF1 (conj HF2 (conj HF3 (conj HF4 HF6))))|].
  split; [exact (conj Hr16 (conj Hr4096 (conj Hrc (conj Hria Hrb))))|]. split; [exact DRF|].
  pose proof HB as (_ & _ & _ & Hinp & _).
  destruct Hinp as [H0 | (Hn & Hin)]; [left; exact H0 | right].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpc & Hpia & _).
  assert (Hrqe : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hrqe in Hpc, Hpia.
  assert (Hm : In (c_p cx, c_n cx) (map (fun b => (fst b, req_size (snd b))) (ablocks B (c_ly cx) (c_S cx)))).
  { pose proof (in_map (fun b => (fst b, req_size (snd b))) _ _ Hin) as Hm0. cbn [fst snd] in Hm0.
    rewrite Hrqe in Hm0. exact Hm0. }
  assert (DPF : c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx).
  { pose proof (pairwise_In zdisjoint _ (c_p cx, c_n cx) (gF cx fp, 512)
      (map (fun b => (fst b, req_size (snd b))) (ablocks B (c_ly cx) (c_S cx)) ++ [(r, 288)]) [(gF cx fp, 512)]
      ltac:(rewrite <- app_assoc; reflexivity) HSEP ltac:(apply in_or_app; left; exact Hm)
      ltac:(left; reflexivity)) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
  assert (DPR : c_p cx + c_n cx <= r \/ r + 288 <= c_p cx).
  { pose proof (pairwise_In zdisjoint _ (c_p cx, c_n cx) (r, 288)
      (map (fun b => (fst b, req_size (snd b))) (ablocks B (c_ly cx) (c_S cx))) [(r, 288); (gF cx fp, 512)]
      eq_refl HSEP Hm ltac:(left; reflexivity)) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
  split; [lia|]. split; [exact Hin3|]. split; [exact Hp4096|]. split; [exact Hpc|].
  split; [exact Hpia|]. split; [exact DPF | exact DPR].
Qed.

End cm_geo_s.

(* ---- the seat at GP_T 1 ---- *)
Lemma cm_seat : forall cx fp k ly3 S3 W3 ms3 md3 r pos,
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GB_CID, fp)] -> gblk1 B cx ly3 S3 r ->
  gb_body cx fp PC1_mac0 W3 ms3 GSH_it -> gcursor cx W3 ms3 pos ->
  st_ok_pi SEGS VAL (cm_E (ms_regs ms3) cx fp pos) cm_ss0 (restrict (w_H W3) ms3) /\
  sh_ok SEGS cm_Bx cm_SH0 (cm_E (ms_regs ms3) cx fp pos) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
  intros cx fp k ly3 S3 W3 ms3 md3 r pos HB HJ HFR HBLK HBODY HCUR.
  pose proof (cm_geo cx fp k ly3 S3 W3 ms3 md3 r HB HJ HFR HBLK)
    as ((Hs1 & Hs2 & Hs3 & Hs4 & Hs5) & (HF1 & HF2 & HF3 & HF4 & HF6) & _ & _ & Hinp).
  pose proof asan_consts as (Hac & _).
  pose proof HBODY as (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & HSV & HSH & HLEN
    & HFL & (S18 & S28 & S70 & S78 & S80) & HIN).
  pose proof HCUR as (Hpos & S88 & S90).
  unfold gslot in S70, S88, S90.
  pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
  assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ GB_CID fp HAR3 Hfin) as (_ & _ & HFpres & _).
  rewrite EF in HFpres. change (fs_frame_bytes GB_CID) with 512 in HFpres.
  assert (Hcur : 4096 <= c_p cx + pos /\ c_p cx + pos <= 0x7fffff800000).
  { destruct Hinp as [(Hn0 & Hp0) | (_ & _ & Hp4 & Hpc' & _)]; unfold GB_EMPTY in *; lia. }
  assert (Hms : restrict (w_H W3) ms3 =
    mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PC1_mac0)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
  { destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hrv, Hsv, Hro, Hfr, Hfc.
    subst. reflexivity. }
  remember (cm_E (ms_regs ms3) cx fp pos) as E eqn:HE.
  assert (F9 : ew E 9 = w64 (c_sp1 cx)) by (subst E; unfold cm_E; rewrite (ew_Eimg_Ereg_nat _ _ 9 9%bv eq_refl); exact G9).
  assert (F18 : ew E 18 = w64 SHADOW_OFF) by (subst E; unfold cm_E; rewrite (ew_Eimg_Ereg_nat _ _ 18 18%bv eq_refl); exact G18).
  assert (F32 : ew E 32 = w64 (c_p cx + pos))
    by (subst E; unfold cm_E; change 32%nat with (32 + 0)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F33 : ew E 33 = w64 (c_n cx - pos))
    by (subst E; unfold cm_E; change 33%nat with (32 + 1)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F34 : ew E 34 = w64 (gF cx fp))
    by (subst E; unfold cm_E; change 34%nat with (32 + 2)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (apply (cm_U E 9); [exact F9 | lia]).
  assert (U34 : bv_unsigned (ew E 34) = gF cx fp) by (apply (cm_U E 34); [exact F34 | lia]).
  assert (Hwin : forall o, 0 <= o < 0x98 -> writable_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + o))
    by (intros o Ho; apply (apresent_writable SEGS); apply HJpres; unfold GB_STK; lia).
  split.
  - rewrite Hms. unfold cm_ss0. apply pa_entry_st_ok_full.
    + subst E. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok; cbv zeta;
        cbn [cm_spill_lo cm_spill_hi cm_frame YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks
             YP09.base_val].
      * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwin; lia | apply Forall_nil].
      * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwin; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (cm_chunk8 _ _ _ _ _ _ (gF cx fp + 32)); [apply (cm_den E 34 (gF cx fp) 32 F34); lia | lia |].
           unfold GO_MAC in S70. exact S70.
        -- apply (cm_chunk8 _ _ _ _ _ _ (c_p cx + pos)); [| lia | exact S88].
           rewrite (cm_den E 32 (c_p cx + pos) 0 F32) by lia. rewrite Z.add_0_r. reflexivity.
        -- apply (cm_chunk8 _ _ _ _ _ _ (c_n cx - pos)); [| lia | exact S90].
           rewrite (cm_den E 33 (c_n cx - pos) 0 F33) by lia. rewrite Z.add_0_r. reflexivity.
      * rewrite U34. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (gF cx fp + o) ltac:(lia))).
    + cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
      cbn [cm_spill_lo cm_spill_hi cm_frame YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
      rewrite U9, U34. repeat split; lia.
    + split; [|split; exact I]. cbn [f_atoms cm_af0 atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U34, (cm_U E 18 SHADOW_OFF F18), (cm_U E 32 (c_p cx + pos) F32) by (unfold SHADOW_OFF; lia).
      unfold CM_SB, CM_CEIL, SHADOW_OFF. change (2 ^ 5) with 32. change (2 ^ 6) with 64. change (2 ^ 0) with 1.
      rewrite !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - unfold sh_ok, cm_SH0. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E cm_Bx 34 (gF cx fp + 32) 6 (gF cx fp) 32 38).
    + pose proof (gb_mac_ra B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR 0 6 HSH ltac:(lia) ltac:(lia)) as H.
      unfold GO_MAC in H. rewrite Z.add_0_r in H. exact H.
    + unfold cm_Bx. exact (U_atom E 18 SHADOW_OFF F18 ltac:(unfold SHADOW_OFF; lia)).
    + exact (U_atom E 34 (gF cx fp) F34 ltac:(lia)).
    + lia.
    + lia.
    + intros x Hx. revert HF3 Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. clear. intros. lia.
Qed.


(* ---- the memory the piece keeps ---- *)
(* The bytes the piece may change: memcpy's own stack window below sp1, slot 0x58, the cursor slots, mac. *)
Definition cm_out (cx : bcx) (fp a : Z) : Prop :=
  ~ (c_sp1 cx - 4096 <= a < c_sp1 cx) /\ ~ (c_sp1 cx + 0x58 <= a < c_sp1 cx + 0x60) /\
  ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98) /\ ~ (gF cx fp + 32 <= a < gF cx fp + 38).
Definition cm_keep (cx : bcx) (fp : Z) (W3 : world SEGS) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> cm_out cx fp a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Definition cm_ms (cx : bcx) (m : word -> option byte) : machine_state :=
  mkst (c_regs cx) (Z_to_bv 64 0) m (seg_rom SEGS).
(* What c1_base and C1_nch ask of the memory and the piece does not touch. *)
Definition cm_mem0 (cx : bcx) (fp : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (i r : Z) (bs : list byte)
  (m : word -> option byte) : Prop :=
  c1mem cx fp W3 (cm_ms cx m) bs /\ gslots_r cx fp W3 (cm_ms cx m) r (Boxreg.bx_fabric bs) /\
  gslot cx W3 (cm_ms cx m) 0x68 i /\ gslot cx W3 (cm_ms cx m) 0x48 (Boxreg.bx_n bs) /\
  greg B ly3 S3 W3 (cm_ms cx m) r bs.

Lemma cm_keep_refl : forall cx fp W3 m, cm_keep cx fp W3 m m.
Proof. intros cx fp W3 m a _ _. reflexivity. Qed.
Lemma cm_keep_trans : forall cx fp W3 m1 m2 m3, cm_keep cx fp W3 m1 m2 -> cm_keep cx fp W3 m2 m3 -> cm_keep cx fp W3 m1 m3.
Proof. intros cx fp W3 m1 m2 m3 H1 H2 a Ha Ho. rewrite (H2 a Ha Ho). exact (H1 a Ha Ho). Qed.

(* A run keeps every byte outside its regions' write windows. *)
Lemma cm_keep_frame : forall cx fp W3 E rs (m m' : word -> option byte),
  frame_of E rs m m' -> (forall a, 0 <= a < 2 ^ 64 -> in_wrange E rs a -> ~ cm_out cx fp a) -> cm_keep cx fp W3 m m'.
Proof.
  intros cx fp W3 E rs m m' HF Hw a Ha Ho. unfold aview, mbyte, mrestrict.
  rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha.
  intros Hin. exact (Hw a Ha Hin Ho).
Qed.

Lemma cm_rdword_keep : forall cx fp W3 m m' a v, cm_keep cx fp W3 m m' ->
  (forall j, 0 <= j < 8 -> 0 <= a + j < 2 ^ 64 /\ cm_out cx fp (a + j)) ->
  rdword (aview SEGS (w_H W3) m) a = Some v -> rdword (aview SEGS (w_H W3) m') a = Some v.
Proof.
  intros cx fp W3 m m' a v HK Hj H. rewrite <- H. apply rdword_ext. intros j Hj8.
  destruct (Hj j Hj8) as [Hr Ho]. exact (HK _ Hr Ho).
Qed.

Section cm_keep_s.
Variables (cx : bcx) (fp : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (i r : Z) (bs : list byte).
Hypothesis Hsp : alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256.
Hypothesis HF : 4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512.
Hypothesis Hr : 4096 <= r /\ r + 288 <= alloc_ceiling /\ (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r).
Hypothesis Hin : c_n cx = 0 \/
  (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx)).

Local Ltac cm_out_tac :=
  pose proof asan_consts as (Hac0 & _);
  unfold cm_out, gSH, shadow_of_addr, GO_PREV, REG_SIZE, GB_STK in *;
  repeat match goal with |- _ /\ _ => split end; try lia.

Lemma cm_mem0_keep : forall m m', cm_mem0 cx fp ly3 S3 W3 i r bs m -> cm_keep cx fp W3 m m' ->
  cm_mem0 cx fp ly3 S3 W3 i r bs m'.
Proof.
  intros m m' HM HK.
  pose proof asan_consts as (Hac & _).
  destruct HF as (HF1 & HF2 & HF3).
  assert (HSHb : SHADOW_OFF <= gSH cx fp /\ gSH cx fp + 64 <= SHADOW_OFF + 2 ^ 44 /\
    (gF cx fp + 512 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= gF cx fp)).
  { unfold gSH, shadow_of_addr. pose proof (Z.div_pos (gF cx fp) 8 ltac:(lia) ltac:(lia)).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in HF3 |- *.
    assert (gF cx fp / 8 < 2 ^ 44 - 64) by (apply Z.div_lt_upper_bound; lia). lia. }
  unfold SHADOW_OFF in HSHb.
  destruct HM as ((HSV & HSH & HFL & HIN & (S18 & S28 & S70 & S78 & S80) & HPV) & (S10 & S20 & S38 & S40 & S50 & S60)
    & S68 & S48 & (Hrin & Hrlen & Hrb)).
  unfold gslot in *. cbn [cm_ms ms_mem mkst] in *.
  assert (KS : forall off v, (0x10 <= off <= 0x50 \/ off = 0x60 \/ (0x68 <= off <= 0x80)) ->
    rdword (aview SEGS (w_H W3) m) (c_sp1 cx + off) = Some v -> rdword (aview SEGS (w_H W3) m') (c_sp1 cx + off) = Some v).
  { intros off v Hoff H. apply (cm_rdword_keep cx fp W3 m m' _ v HK); [|exact H]. intros j Hj. split; [lia|].
    unfold cm_out. lia. }
  split; [split; [|split; [|split; [|split; [|split]]]] | split; [|split; [|split]]].
  - destruct HSV as (Hra & Hsj). unfold gsaved. cbn [cm_ms ms_mem mkst]. split.
    + apply (cm_rdword_keep cx fp W3 m m' _ _ HK); [|exact Hra]. intros j Hj. split; [lia|]. unfold cm_out. lia.
    + intros j Hj. apply (cm_rdword_keep cx fp W3 m m' _ _ HK); [|exact (Hsj j Hj)]. intros q Hq. split; [lia|].
      unfold cm_out. lia.
  - intros q Hq. unfold gshadow in HSH. cbn [cm_ms ms_mem mkst] in HSH |- *.
    change (length GSH_it) with 52%nat in Hq.
    rewrite (HK (gSH cx fp + Z.of_nat q)); [exact (HSH q ltac:(change (length GSH_it) with 52%nat; exact Hq)) | lia |].
    unfold cm_out. lia.
  - cbn [cm_ms ms_mem mkst]. apply (cm_rdword_keep cx fp W3 m m' _ _ HK); [|exact HFL]. intros j Hj.
    change (fs_frame_bytes GB_CID) with 512. split; [lia|]. unfold cm_out. lia.
  - cbn [cm_ms ms_mem mkst]. apply (garr8_frame SEGS _ _ _ _ HIN). intros a Ha. rewrite length_map in Ha.
    fold (c_n cx) in Ha.
    apply (mbyte_of_aview SEGS). apply HK; [destruct Hin as [Hn0 | (Hp4 & Hpc & _)]; lia|].
    unfold cm_out. destruct Hin as [Hn0 | (Hp4 & Hpc & Hpf)]; lia.
  - unfold gslots_fr, gslot. cbn [cm_ms ms_mem mkst].
    split; [apply KS; [lia | exact S18]|]. split; [apply KS; [lia | exact S28]|].
    split; [apply KS; [lia | exact S70]|]. split; [apply KS; [lia | exact S78] | apply KS; [lia | exact S80]].
  - intros q Hq. unfold gprev in HPV. cbn [cm_ms ms_mem mkst] in HPV |- *.
    rewrite (HK (gF cx fp + GO_PREV + q)); [exact (HPV q Hq) | unfold GO_PREV, REG_SIZE in *; lia |].
    unfold cm_out, GO_PREV, REG_SIZE in *. lia.
  - unfold gslots_r, gslot. cbn [cm_ms ms_mem mkst].
    split; [apply KS; [lia | exact S10]|]. split; [apply KS; [lia | exact S20]|].
    split; [apply KS; [lia | exact S38]|]. split; [apply KS; [lia | exact S40]|].
    split; [apply KS; [lia | exact S50] | apply KS; [lia | exact S60]].
  - unfold gslot. cbn [cm_ms ms_mem mkst]. apply KS; [lia | exact S68].
  - unfold gslot. cbn [cm_ms ms_mem mkst]. apply KS; [lia | exact S48].
  - unfold greg. cbn [cm_ms ms_mem mkst]. split; [exact Hrin|]. split; [exact Hrlen|]. intros q Hq.
    rewrite (HK (r + q)); [exact (Hrb q Hq) | unfold REG_SIZE in Hq; lia |]. unfold cm_out, REG_SIZE in *. lia.
Qed.

End cm_keep_s.

(* ---- the input bytes at the cursor ---- *)
Lemma cm_inbyte_aview : forall cx pos (W3 : world SEGS) (m : word -> option byte) j,
  garr8 SEGS (mrestrict (w_H W3) m) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  0 <= pos -> pos + Z.of_nat j < c_n cx ->
  aview SEGS (w_H W3) m (c_p cx + pos + Z.of_nat j) = Some (cm_inbyte cx pos j).
Proof.
  intros cx pos W3 m j HIN Hpos Hj.
  assert (Hlt : (Z.to_nat pos + j < length (c_pl cx))%nat) by (unfold c_n in Hj; lia).
  destruct (HIN (Z.to_nat pos + j)%nat ltac:(rewrite length_map; exact Hlt)) as [Hv Hb].
  replace (c_p cx + Z.of_nat (Z.to_nat pos + j)%nat) with (c_p cx + pos + Z.of_nat j) in Hv by lia.
  apply (aview_of_val_mem1 SEGS) in Hv; [|exact Hb]. rewrite Hv. f_equal.
  unfold cm_inbyte. replace (Z.to_nat pos + j <? length (c_pl cx))%nat with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hlt).
  apply map_nth.
Qed.

Lemma cm_inb_ok : forall cx pos (W3 : world SEGS) (m : word -> option byte) E kk,
  ew E 32 = w64 (c_p cx + pos) -> (forall j, (j < 7)%nat -> ew E (35 + j) = w64 (cm_inbyte cx pos j)) ->
  garr8 SEGS (mrestrict (w_H W3) m) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  (kk <= 7)%nat -> 0 <= pos -> pos + Z.of_nat kk <= c_n cx -> 0 <= c_p cx + pos -> c_p cx + pos + 7 < 2 ^ 64 ->
  YP09.region_ok SEGS E (mrestrict (w_H W3) m) (cm_inb kk).
Proof.
  intros cx pos W3 m E kk F32 FB HIN Hk Hpos Hkn Hc0 Hc1.
  unfold YP09.region_ok, cm_inb. cbv zeta.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite (cm_U E 32 _ F32) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
  apply (cm_chunk1 _ _ _ _ _ _ (cm_inbyte cx pos j)).
  - pose proof (cm_inbyte_range cx pos j) as Hr.
    rewrite (cm_den E (35 + j) (cm_inbyte cx pos j) 0 (FB j ltac:(lia))) by lia. rewrite Z.add_0_r. reflexivity.
  - exact (cm_inbyte_aview cx pos W3 m j HIN Hpos ltac:(lia)).
Qed.

Lemma cm_inb_sh : forall cx pos ly S (W : world SEGS) mem md E kk,
  AR SEGS B ly S W mem md -> In (c_p cx, c_n cx) (ablocks B ly S) -> 0 < c_n cx -> in_app (c_p cx) (c_n cx) ->
  c_p cx + c_n cx <= alloc_ceiling ->
  ew E 18 = w64 SHADOW_OFF -> ew E 32 = w64 (c_p cx + pos) -> 0 <= pos -> pos + Z.of_nat kk <= c_n cx ->
  shent_ok SEGS cm_Bx E (mrestrict (w_H W) mem) (mkSHE 32 0 (Z.of_nat kk)).
Proof.
  intros cx pos ly S W mem md E kk HAR Hin Hn Hia Hce F18 F32 Hpos Hkn.
  pose proof asan_consts as (Hac & _).
  assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  apply (shent_ok_of_range SEGS (w_H W) mem E cm_Bx 32 (c_p cx + pos) (Z.of_nat kk) (c_p cx + pos) 0 (Z.of_nat kk)).
  - apply (range_addressable_of_block SEGS B LAWS ly S W mem md (c_p cx) (c_n cx)); [exact HAR | exact Hin | lia | lia].
  - unfold cm_Bx. exact (U_atom E 18 SHADOW_OFF F18 ltac:(unfold SHADOW_OFF; lia)).
  - apply (U_atom E 32 _ F32). unfold in_app in Hia. lia.
  - lia.
  - lia.
  - intros x Hx. revert Hia Hx Hpos Hkn. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL.
    clear. intros. lia.
Qed.

Lemma cm_remf_ok : forall E cx pos (cap kk : nat), ew E 33 = w64 (c_n cx - pos) -> 0 <= pos <= c_n cx ->
  c_n cx < 2 ^ 26 -> (cap <= 7)%nat -> kk = Z.to_nat (Z.min (c_n cx - pos) (Z.of_nat cap)) ->
  afact_ok E 33 (cm_remf cap kk).
Proof.
  intros E cx pos cap kk F33 Hpos Hn Hcap Hkk. unfold afact_ok, cm_remf.
  rewrite (cm_U E 33 _ F33) by lia.
  destruct (Nat.ltb_spec kk cap); cbn [af_lo af_hi af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; lia.
Qed.

Definition cm_add (ss : sstate) (cap kk : nat) : sstate :=
  if (kk =? 0)%nat then add_atom ss 33 (cm_remf cap kk)
  else mkSS (ss_pc (add_atom ss 33 (cm_remf cap kk))) (ss_regs (add_atom ss 33 (cm_remf cap kk)))
         (cm_inb kk :: ss_mem (add_atom ss 33 (cm_remf cap kk))) (ss_resv (add_atom ss 33 (cm_remf cap kk)))
         (ss_facts (add_atom ss 33 (cm_remf cap kk))).

Lemma cm_addin : forall E ss (ms : machine_state) (W3 : world SEGS) (cap kk : nat),
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms) ->
  sh_ok SEGS cm_Bx cm_SH0 E (mrestrict (w_H W3) (ms_mem ms)) ->
  afact_ok E 33 (cm_remf cap kk) ->
  (kk = 0%nat \/ (YP09.region_wf (cm_inb kk) = true /\
     YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (cm_inb kk) /\ YP09.all_disjoint E (cm_inb kk) (ss_mem ss) /\
     shent_ok SEGS cm_Bx E (mrestrict (w_H W3) (ms_mem ms)) (mkSHE 32 0 (Z.of_nat kk)))) ->
  st_ok_pi SEGS VAL E (cm_add ss cap kk) (restrict (w_H W3) ms) /\
  sh_ok SEGS cm_Bx (cm_SH kk) E (mrestrict (w_H W3) (ms_mem ms)).
Proof.
  intros E ss ms W3 cap kk HS SH Hf Hk.
  pose proof (st_ok_pi_add_fact E ss _ 33 (cm_remf cap kk) HS Hf) as HS1.
  unfold cm_add, cm_SH. destruct Hk as [-> | (Hwf & Hok & Hdj & Hsh)].
  - cbn [Nat.eqb]. split; [exact HS1 | exact SH].
  - destruct (Nat.eqb_spec kk 0) as [-> | Hk0].
    + split; [exact HS1 | exact SH].
    + split.
      * apply (st_ok_pi_add_region E _ _ (cm_inb kk) HS1 Hwf); [exact Hok | exact Hdj].
      * unfold sh_ok in *. apply Forall_app. split; [exact SH | apply Forall_cons; [exact Hsh | apply Forall_nil]].
Qed.

(* The frame window F + 32 .. F + 38 is the owned frame's. *)
Lemma cm_mac_frames : forall cx fp ly3 a, frame_addr ly3 GB_CID fp = gF cx fp ->
  gF cx fp + 32 <= a < gF cx fp + 38 -> in_frames ly3 [(GB_CID, fp)] a.
Proof.
  intros cx fp ly3 a EF Ha. exists GB_CID, fp. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes GB_CID) with 512. lia.
Qed.

Local Ltac cm_awr d U9 U34 HFA :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
  repeat first
    [ apply awr_ok_nil
    | (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |])
    | (apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat d);
        [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ])
    | (apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF _ _));
        [reflexivity | exact U34
        | intros ?a ?Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]) ].

(* The windows of the piece's regions lie in what it may change. *)
Local Ltac cm_wins U9 U34 :=
  lazymatch goal with |- forall a, _ -> in_wrange ?E0 ?rs a -> _ =>
    let rs' := eval vm_compute in rs in change (forall a, 0 <= a < 2 ^ 64 -> in_wrange E0 rs' a -> ~ cm_out _ _ a) end;
  let a := fresh "a" in let Ha := fresh "Ha" in let r0 := fresh "r0" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a Ha (r0 & Hr & Hb); cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
  destruct Hr.


Lemma cm_and4 : forall E v, ew E 22 = w64 v -> 0 <= v < 256 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff 22 0) (SLit 4))) (sv_denot E (SLit 0)) = negb (Z.land v 4 =? 0).
Proof.
  intros E v H Hv. rewrite branch_ne_U, U_and_lit by lia. rewrite (U_atom E 22 v H) by lia. rewrite U_lit by lia.
  reflexivity.
Qed.

Lemma cm_inb_wf : forall kk, YP09.region_wf (cm_inb kk) = true.
Proof.
  intros kk. unfold YP09.region_wf, cm_inb.
  cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Z.leb_refl. cbn [andb orb].
  rewrite (proj2 (Z.leb_le 0 (Z.of_nat kk))) by lia. cbn [andb].
  apply forallb_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
  unfold YP09.chunk_inside. cbn [YP09.r_lo YP09.r_hi YP09.c_off YP09.c_len YP09.c_val YP09.cv_len].
  rewrite (proj2 (Z.leb_le 0 (Z.of_nat j))) by lia. cbn [andb]. change (Z.of_N 1) with 1.
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

Lemma cm_mac6 : forall E' (W : world SEGS) (m : word -> option byte) rbase e0 e1 e2 e3 e4 e5,
  YP09.region_ok SEGS E' (mrestrict (w_H W) m)
    (YP09.mkRegion (Some 34%nat) 32 38 32 38
      [YP09.mkChunk 37 (CVal 1 e5); YP09.mkChunk 36 (CVal 1 e4); YP09.mkChunk 35 (CVal 1 e3);
       YP09.mkChunk 34 (CVal 1 e2); YP09.mkChunk 33 (CVal 1 e1); YP09.mkChunk 32 (CVal 1 e0)]) ->
  bv_unsigned (ew E' 34) = rbase ->
  exists M, length M = 6%nat /\
    forall j, 0 <= j < 6 -> aview SEGS (w_H W) m (rbase + 32 + j) =
      Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0))).
Proof.
  intros E' W m rbase e0 e1 e2 e3 e4 e5 HR Hb.
  pose (v := fun e => bv_unsigned (sv_denot E' e) mod 2 ^ (8 * Z.of_N 1)).
  assert (Hvr : forall e, 0 <= v e < 256) by (intros e; unfold v; change (2 ^ (8 * Z.of_N 1)) with 256; apply Z.mod_pos_bound; lia).
  assert (Hvb : forall e, bv_unsigned (Z_to_bv 8 (v e)) = v e)
    by (intros e; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; apply Hvr).
  pose (M := [Z_to_bv 8 (v e0); Z_to_bv 8 (v e1); Z_to_bv 8 (v e2); Z_to_bv 8 (v e3); Z_to_bv 8 (v e4); Z_to_bv 8 (v e5)]).
  assert (Hval : forall o e, In (YP09.mkChunk o (CVal 1 e))
      [YP09.mkChunk 37 (CVal 1 e5); YP09.mkChunk 36 (CVal 1 e4); YP09.mkChunk 35 (CVal 1 e3);
       YP09.mkChunk 34 (CVal 1 e2); YP09.mkChunk 33 (CVal 1 e1); YP09.mkChunk 32 (CVal 1 e0)] ->
      aview SEGS (w_H W) m (rbase + o) = Some (v e)).
  { intros o e Hin.
    pose proof (YC4b.field_of_region_any E' (mrestrict (w_H W) m) 34%nat rbase _ 32 38 32 38 o 1 e HR Hb Hin ltac:(cbn [Z.of_N]; lia)) as Hvm.
    cbn [N.to_nat] in Hvm. apply (aview_of_val_mem1 SEGS); [exact Hvm | apply Hvr]. }
  clearbody v. exists M. split; [reflexivity|]. intros j Hj.
  assert (Hj6 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
  destruct Hj6 as [Q|[Q|[Q|[Q|[Q|Q]]]]]; rewrite Q.
  - change (Z.to_nat 0) with 0%nat. unfold M. cbn [nth]. rewrite Hvb. replace (rbase + 32 + 0) with (rbase + 32) by lia. apply (Hval 32 e0). cbn [In]. tauto.
  - change (Z.to_nat 1) with 1%nat. unfold M. cbn [nth]. rewrite Hvb. replace (rbase + 32 + 1) with (rbase + 33) by lia. apply (Hval 33 e1). cbn [In]. tauto.
  - change (Z.to_nat 2) with 2%nat. unfold M. cbn [nth]. rewrite Hvb. replace (rbase + 32 + 2) with (rbase + 34) by lia. apply (Hval 34 e2). cbn [In]. tauto.
  - change (Z.to_nat 3) with 3%nat. unfold M. cbn [nth]. rewrite Hvb. replace (rbase + 32 + 3) with (rbase + 35) by lia. apply (Hval 35 e3). cbn [In]. tauto.
  - change (Z.to_nat 4) with 4%nat. unfold M. cbn [nth]. rewrite Hvb. replace (rbase + 32 + 4) with (rbase + 36) by lia. apply (Hval 36 e4). cbn [In]. tauto.
  - change (Z.to_nat 5) with 5%nat. unfold M. cbn [nth]. rewrite Hvb. replace (rbase + 32 + 5) with (rbase + 37) by lia. apply (Hval 37 e5). cbn [In]. tauto.
Qed.

(* The same, for a mac region whose chunks are in the order the walk of path A leaves them. *)
Lemma cm_mac6g : forall E' (W : world SEGS) (m : word -> option byte) cs rbase e0 e1 e2 e3 e4 e5,
  YP09.region_ok SEGS E' (mrestrict (w_H W) m) (YP09.mkRegion (Some 34%nat) 32 38 32 38 cs) ->
  bv_unsigned (ew E' 34) = rbase ->
  In (YP09.mkChunk 32 (CVal 1 e0)) cs -> In (YP09.mkChunk 33 (CVal 1 e1)) cs -> In (YP09.mkChunk 34 (CVal 1 e2)) cs ->
  In (YP09.mkChunk 35 (CVal 1 e3)) cs -> In (YP09.mkChunk 36 (CVal 1 e4)) cs -> In (YP09.mkChunk 37 (CVal 1 e5)) cs ->
  exists M, length M = 6%nat /\
    forall j, 0 <= j < 6 -> aview SEGS (w_H W) m (rbase + 32 + j) =
      Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0))).
Proof.
  intros E' W m cs rbase e0 e1 e2 e3 e4 e5 HR Hb I0 I1 I2 I3 I4 I5.
  pose (v := fun e => bv_unsigned (sv_denot E' e) mod 2 ^ (8 * Z.of_N 1)).
  assert (Hvr : forall e, 0 <= v e < 256) by (intros e; unfold v; change (2 ^ (8 * Z.of_N 1)) with 256; apply Z.mod_pos_bound; lia).
  assert (Hvb : forall e, bv_unsigned (Z_to_bv 8 (v e)) = v e)
    by (intros e; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; apply Hvr).
  pose (M := [Z_to_bv 8 (v e0); Z_to_bv 8 (v e1); Z_to_bv 8 (v e2); Z_to_bv 8 (v e3); Z_to_bv 8 (v e4); Z_to_bv 8 (v e5)]).
  assert (Hval : forall o e, In (YP09.mkChunk o (CVal 1 e)) cs -> 32 <= o -> o + 1 <= 38 ->
      aview SEGS (w_H W) m (rbase + o) = Some (v e)).
  { intros o e Hin Ho1 Ho2.
    pose proof (YC4b.field_of_region_any E' (mrestrict (w_H W) m) 34%nat rbase _ 32 38 32 38 o 1 e HR Hb Hin ltac:(cbn [Z.of_N]; lia)) as Hvm.
    cbn [N.to_nat] in Hvm. apply (aview_of_val_mem1 SEGS); [exact Hvm | apply Hvr]. }
  clearbody v. exists M. split; [reflexivity|]. intros j Hj.
  assert (Hj6 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
  destruct Hj6 as [Q|[Q|[Q|[Q|[Q|Q]]]]]; rewrite Q.
  - change (Z.to_nat 0) with 0%nat. unfold M. cbn [nth]. rewrite Hvb. replace (rbase + 32 + 0) with (rbase + 32) by lia. apply (Hval 32 e0 I0); lia.
  - change (Z.to_nat 1) with 1%nat. unfold M. cbn [nth]. rewrite Hvb. replace (rbase + 32 + 1) with (rbase + 33) by lia. apply (Hval 33 e1 I1); lia.
  - change (Z.to_nat 2) with 2%nat. unfold M. cbn [nth]. rewrite Hvb. replace (rbase + 32 + 2) with (rbase + 34) by lia. apply (Hval 34 e2 I2); lia.
  - change (Z.to_nat 3) with 3%nat. unfold M. cbn [nth]. rewrite Hvb. replace (rbase + 32 + 3) with (rbase + 35) by lia. apply (Hval 35 e3 I3); lia.
  - change (Z.to_nat 4) with 4%nat. unfold M. cbn [nth]. rewrite Hvb. replace (rbase + 32 + 4) with (rbase + 36) by lia. apply (Hval 36 e4 I4); lia.
  - change (Z.to_nat 5) with 5%nat. unfold M. cbn [nth]. rewrite Hvb. replace (rbase + 32 + 5) with (rbase + 37) by lia. apply (Hval 37 e5 I5); lia.
Qed.


Lemma cm_slot8 : forall E' (W : world SEGS) (m : word -> option byte) lo hi wlo whi cs sp1 off e,
  YP09.region_ok SEGS E' (mrestrict (w_H W) m) (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E' 9) = sp1 -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  0 <= bv_unsigned (sv_denot E' e) mod 2 ^ (8 * Z.of_N 8) < 2 ^ 64 ->
  rdword (aview SEGS (w_H W) m) (sp1 + off) = Some (bv_unsigned (sv_denot E' e) mod 2 ^ (8 * Z.of_N 8)).
Proof.
  intros E' W m lo hi wlo whi cs sp1 off e HR Hb Hin Hv.
  pose proof (YC4b.field_of_region_any E' (mrestrict (w_H W) m) 9%nat sp1 cs lo hi wlo whi off 8 e HR Hb Hin ltac:(cbn [Z.of_N]; lia)) as Hvm.
  cbn [N.to_nat] in Hvm. apply (rdword_of_val_mem SEGS (w_H W) m); [exact Hvm | exact Hv].
Qed.

Lemma cm_slot_off : forall E' (W : world SEGS) (m : word -> option byte) lo hi wlo whi cs sp1 off n d base,
  YP09.region_ok SEGS E' (mrestrict (w_H W) m) (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E' 9) = sp1 -> In (YP09.mkChunk off (CVal 8 (SOff n d))) cs ->
  ew E' n = w64 base -> 0 <= base < 2 ^ 64 -> 0 <= base + d < 2 ^ 64 ->
  rdword (aview SEGS (w_H W) m) (sp1 + off) = Some (base + d).
Proof.
  intros E' W m lo hi wlo whi cs sp1 off n d base HR Hb Hin Hn Hbv Hbd.
  pose proof (cm_slot8 E' W m lo hi wlo whi cs sp1 off (SOff n d) HR Hb Hin) as H.
  rewrite (cm_den E' n base d Hn Hbv Hbd), (unsigned_lit_small (base + d) ltac:(lia)) in H.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in H. rewrite (Z.mod_small (base + d) (2 ^ 64) ltac:(lia)) in H.
  apply H. lia.
Qed.

Lemma cm_slot_byte : forall E' (W : world SEGS) (m : word -> option byte) lo hi wlo whi cs sp1 off x,
  YP09.region_ok SEGS E' (mrestrict (w_H W) m) (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E' 9) = sp1 -> In (YP09.mkChunk off (CVal 8 (SExt false 8 x))) cs ->
  exists nch, 0 <= nch < 256 /\ rdword (aview SEGS (w_H W) m) (sp1 + off) = Some nch.
Proof.
  intros E' W m lo hi wlo whi cs sp1 off x HR Hb Hin.
  pose proof (U_zext E' 8 x) as Hz. change (2 ^ Z.of_N 8) with 256 in Hz.
  pose proof (bv_unsigned_in_range 64 (sv_denot E' (SExt false 8 x))) as Hrg.
  change (bv_modulus 64) with (2 ^ 64) in Hrg.
  assert (Hnb : bv_unsigned (sv_denot E' (SExt false 8 x)) < 256).
  { change (bv_unsigned (sv_denot E' (SExt false 8 x))) with (U E' (SExt false 8 x)). rewrite Hz.
    apply Z.mod_pos_bound. lia. }
  exists (bv_unsigned (sv_denot E' (SExt false 8 x)) mod 2 ^ (8 * Z.of_N 8)).
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
  split; [rewrite Z.mod_small by lia; lia|].
  apply (cm_slot8 E' W m lo hi wlo whi cs sp1 off (SExt false 8 x) HR Hb Hin).
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
Qed.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the two paths, from the facts of GI_T 1 ---- *)
Section cm_p.
Variables (i : Z) (cx : bcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state).
Variables (md3 : Model) (r : Z) (bs : list byte) (pos op : Z).
Hypothesis HN : gb_from B MT POST (C1_nch B MT i).
Hypothesis HB : gb_base B MT cx.
Hypothesis HJ : ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k.
Hypothesis HFR : frames S3 = [(GB_CID, fp)].
Hypothesis HMO : mo_le MT (c_S cx) S3 acc.
Hypothesis HBODY : gb_body cx fp PC1_mac0 W3 ms3 GSH_it.
Hypothesis Hi : 0 <= i < 64.
Hypothesis Hk : k <= 1 + 2 * i.
Hypothesis Hacc : acc <= GB_A MT i.
Hypothesis HBLK : gblk1 B cx ly3 S3 r.
Hypothesis HREG : greg B ly3 S3 W3 ms3 r bs.
Hypothesis HPRV : gprev cx fp W3 ms3 bs.
Hypothesis HINV : Boxreg.boxreg_inv bs.
Hypothesis R20 : getr (ms_regs ms3) 20 = w64 r.
Hypothesis R22 : getr (ms_regs ms3) 22 = w64 op.
Hypothesis Hop : 0 <= op < 256.
Hypothesis R25 : getr (ms_regs ms3) 25 = w64 (Boxreg.bx_fabric bs).
Hypothesis HSLR : gslots_r cx fp W3 ms3 r (Boxreg.bx_fabric bs).
Hypothesis HCUR : gcursor cx W3 ms3 pos.
Hypothesis H68 : gslot cx W3 ms3 0x68 i.
Hypothesis H48 : gslot cx W3 ms3 0x48 (Boxreg.bx_n bs).

Lemma cm_mem_start : cm_mem0 cx fp ly3 S3 W3 i r bs (ms_mem ms3).
Proof.
  pose proof HBODY as (_ & _ & _ & _ & _ & _ & _ & HSV & HSH & _ & HFL & HSF & HIN).
  split; [|split; [exact HSLR|split; [exact H68|split; [exact H48 | exact HREG]]]].
  split; [exact HSV|]. split; [exact HSH|]. split; [exact HFL|]. split; [exact HIN|]. split; [exact HSF | exact HPRV].
Qed.

Lemma cm_land : forall (msf : machine_state) (md : Model) (M : list byte) (nch posc : Z),
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem msf) md k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  0 <= i < 64 -> k <= 1 + 2 * i -> acc <= GB_A MT i -> gblk1 B cx ly3 S3 r -> Boxreg.boxreg_inv bs ->
  ms_pc_val msf = w64 (BASE + PC1_nch) -> ms_resv msf = None -> ms_svc_pending msf = None ->
  ms_rom msf = seg_rom SEGS -> ms_fregs msf = fp_regs -> ms_fcsr msf = fp_csr -> gregs cx fp msf ->
  getr (ms_regs msf) 20 = w64 r -> getr (ms_regs msf) 19 = w64 (gF cx fp + GO_MAC) ->
  getr (ms_regs msf) 25 = w64 (Boxreg.bx_fabric bs) ->
  cm_mem0 cx fp ly3 S3 W3 i r bs (ms_mem msf) ->
  length M = 6%nat ->
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem msf) (gF cx fp + GO_MAC + j) =
     Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0)))) ->
  0 <= nch < 256 -> gslot cx W3 msf 0x58 nch ->
  0 <= posc <= c_n cx -> gslot cx W3 msf 0x88 (c_p cx + posc) -> gslot cx W3 msf 0x90 (c_n cx - posc) ->
  SRr SEGS W3 (mkCfg msf md) (POST cx).
Proof.
  intros msf md M nch posc HBf HJf HFRf HMOf Hif Hkf Haccf HBLKf HINVf Hpc Hrv Hsv Hro Hfreg Hfcsr Hgregs
    R20f R19f R25f HMf HML Hmac Hnchr Hnchs Hposc Hcur88 Hcur90.
  destruct HMf as (Hc1mem & HSLRf & H68f & H48f & HREGf).
  apply (HN cx fp k acc ly3 S3 W3 msf md HBf HJf HFRf HMOf).
  exists r, bs, posc, M, nch.
  split.
  { unfold c1_core. split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsv|]. split; [exact Hro|].
    split; [exact Hfreg|]. split; [exact Hfcsr | exact Hgregs]. }
  split.
  { unfold c1_base. split; [exact Hif|]. split; [exact Hkf|]. split; [exact Haccf|]. split; [exact HBLKf|].
    split; [exact HINVf|]. split; [exact Hc1mem|].
    split; [exact HSLRf|]. split; [split; [exact Hposc|split; [exact Hcur88|exact Hcur90]]|].
    split; [exact H68f|]. split; [exact H48f | exact R20f]. }
  split; [exact HREGf|].
  split; [split; [exact HML | exact Hmac]|].
  split; [exact Hnchr|]. split; [exact Hnchs|]. split; [exact R19f | exact R25f].
Qed.

(* Path B (op & 4 <> 0): the six-byte loop 0x8048c .. 0x804d8, then the nch byte, to 0x806cc. The split on
   kk = min (c_n - pos, 7) gives atom 33 the fact [kk, kk] (or [7, 2 ^ 26]) and the input region kk bytes; the engine
   decides a `beqz a1` / `bnez a1` only when the range of a1 excludes 0, so for kk <= 6 one branch step at the first
   test where a1 = 0 is taken by hand (its other side contradicts the fact); the branch condition then decides the
   rest. Each case lands with cm_land. *)
Lemma cm_pathB_k0 : Z.land op 4 <> 0 -> Z.to_nat (Z.min (c_n cx - pos) 7) = 0%nat ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros Hop4 HKK.
  pose proof (cm_geo cx fp k ly3 S3 W3 ms3 md3 r HB HJ HFR HBLK)
    as ((Hs1 & Hs2 & Hs3 & Hs4 & Hs5) & (HF1 & HF2 & HF3 & HF4 & HF6) & (Hr16 & Hr4 & Hrc & Hria & Hrin) & HRF & Hinp).
  pose proof asan_consts as (Hac & _).
  destruct (cm_seat cx fp k ly3 S3 W3 ms3 md3 r pos HB HJ HFR HBLK HBODY HCUR) as [HS SHOK].
  pose proof cm_mem_start as HM.
  pose proof HBODY as (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & _).
  pose proof HCUR as (Hpos & _ & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
  pose proof (fun a => cm_mac_frames cx fp ly3 a EF) as HFA.
  remember (cm_E (ms_regs ms3) cx fp pos) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr (ms_regs ms3) rr)
    by (intros q rr Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (F9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F22 : ew E 22 = w64 op) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (F32 : ew E 32 = w64 (c_p cx + pos))
    by (subst E; unfold cm_E; change 32%nat with (32 + 0)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F33 : ew E 33 = w64 (c_n cx - pos))
    by (subst E; unfold cm_E; change 33%nat with (32 + 1)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F34 : ew E 34 = w64 (gF cx fp))
    by (subst E; unfold cm_E; change 34%nat with (32 + 2)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (FB : forall j, (j < 7)%nat -> ew E (35 + j) = w64 (cm_inbyte cx pos j)).
  { intros j Hj. subst E. unfold cm_E. replace (35 + j)%nat with (32 + (3 + j))%nat by lia.
    rewrite cm_ew_ex by lia. apply cm_ex_byte. exact Hj. }
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (apply (cm_U E 9); [exact F9 | lia]).
  assert (U34 : bv_unsigned (ew E 34) = gF cx fp) by (apply (cm_U E 34); [exact F34 | lia]).
  clear HE.
  
  assert (Gsp : alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
    spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256) by lia.
  assert (GF : 4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512) by (split; [lia|]; split; [lia | exact HF3]).
  assert (GR : 4096 <= r /\ r + 288 <= alloc_ceiling /\ (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r)) by lia.
  assert (GI : c_n cx = 0 \/
    (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx)))
    by (destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpc' & _ & Hpf & _)]; [left; exact Hn0 | right; lia]).
  paj_run_tok RUN HS HJ SHOK cm_span.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
      [reflexivity | exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ].
    apply awr_ok_nil. }
  assert (HK1 : cm_keep cx fp W3 (ms_mem ms3) (ms_mem ms)).
  { apply (cm_keep_frame cx fp W3 E _ _ _ HF).
    let rs' := eval vm_compute in (ss_mem cm_ss0) in change (ss_mem cm_ss0) with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]).
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM HK1) as HM1.
  clear HK1 HF HFr HG HM.
  psrr_branch_tok RUN BR HS SHOK cm_span.
  2: { exfalso. rewrite (cm_and4 E op F22 Hop) in Hc. apply Hop4. destruct (Z.eqb_spec (Z.land op 4) 0); [exact e | discriminate Hc]. }

  assert (Hcppos : 0 <= c_p cx + pos < 2 ^ 64).
  { destruct Hinp as [(Hn0 & Hp0) | (_ & _ & Hp4 & Hpc2 & _)]; [rewrite Hp0; unfold GB_EMPTY; lia | lia]. }
  assert (U32 : bv_unsigned (ew E 32) = c_p cx + pos) by (apply (cm_U E 32); [exact F32 | exact Hcppos]).
  clear Hc.
  set (kk := Z.to_nat (Z.min (c_n cx - pos) 7)).
  assert (Hrem : (Z.of_nat kk = c_n cx - pos /\ (kk < 7)%nat) \/ (kk = 7%nat /\ 7 <= c_n cx - pos)).
  { unfold kk. destruct (Z_lt_le_dec (c_n cx - pos) 7) as [Hlt|Hge];
    [left; split; [rewrite Z2Nat.id by lia; rewrite Z.min_l by lia; reflexivity | rewrite Z.min_l by lia; lia]
    | right; rewrite Z.min_r by lia; split; [reflexivity|lia]]. }
  assert (Hkk7 : (kk <= 7)%nat) by (unfold kk; lia).
  assert (Hkkn : pos + Z.of_nat kk <= c_n cx) by (unfold kk; lia).
  pose proof HJ as (HAR3 & _).
  assert (Hcn : c_n cx < 2 ^ 26) by (destruct Hinp as [(Hn0 & _) | (Hn & _)]; lia).
  pose proof HM1 as (HM1c & _).
  destruct HM1c as (_ & _ & _ & HINm & _).
  assert (Hf33 : afact_ok E 33 (cm_remf 7 kk))
    by (apply (cm_remf_ok E cx pos 7 kk F33); [lia | exact Hcn | lia | reflexivity]).
  assert (Haddk : kk = 0%nat \/ (YP09.region_wf (cm_inb kk) = true /\
     YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (cm_inb kk) /\ YP09.all_disjoint E (cm_inb kk) (ss_mem cm_ss0) /\
     shent_ok SEGS cm_Bx E (mrestrict (w_H W3) (ms_mem ms)) (mkSHE 32 0 (Z.of_nat kk)))).
  { destruct (Nat.eq_dec kk 0) as [->|Hk0]; [left; reflexivity|right].
    assert (Hcn0 : 0 < c_n cx) by (unfold kk in Hk0; lia).
    destruct Hinp as [(Hn0 & _) | (_ & Hin2 & Hp4 & Hpc2 & Hpia & HpF & HpR)]; [lia|].
    split; [apply cm_inb_wf|].
    split; [apply (cm_inb_ok cx pos W3 (ms_mem ms) E kk F32 FB HINm Hkk7); [lia | lia | lia | lia]|].
    split.
    { cbn [cm_ss0 ss_mem]. unfold cm_inb, cm_spill_lo, cm_spill_hi, cm_frame.
      cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
      rewrite U32, U9, U34. repeat split; lia. }
    { apply (cm_inb_sh cx pos ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) E kk HAR3 Hin2 Hcn0 Hpia Hpc2 F18 F32); [lia | lia]. } }
  pose proof (cm_addin E _ ms W3 7 kk HS SHOK Hf33 Haddk) as [HS2 SHOK2].
  assert (Hcur7 : 0 <= pos + Z.of_nat kk <= c_n cx) by lia.
  assert (Ekk : kk = 0%nat) by exact HKK.
  rewrite Ekk in HS2, SHOK2, Hrem, Hcur7.
  clear Hf33 Haddk HS SHOK Hkk7.
  lazymatch type of HS2 with context [kk] => fail 100 "cm_pathB: kk remains in HS2" | _ => idtac end.
  lazymatch type of SHOK2 with context [kk] => fail 100 "cm_pathB: kk remains in SHOK2" | _ => idtac end.
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS2 end.
  lazymatch type of SHOK2 with sh_ok _ _ ?sh _ _ => let v := eval vm_compute in sh in change sh with v in SHOK2 end.
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msA end.
  assert (HK1b : cm_keep cx fp W3 (ms_mem ms) (ms_mem msA)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK1b) as HM1b. clear HM1 HK1b HF HFr HG. rename HM1b into HM1.
  destruct Hrem as [(Hremv & _) | (Hbad & _)]; [| discriminate Hbad]. simpl in Hremv.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ =>
    assert (EW33v : bv_unsigned (ew Ee 33) = c_n cx - pos) by (rewrite ?ew_ewset_other by lia; rewrite F33; apply unsigned_lit_small; lia);
    assert (HUk : U Ee (SOff 33 (0)) = 0) by (rewrite U_SOff, EW33v; replace (c_n cx - pos + (0)) with 0 by lia; apply zcanon_id; unfold M64; lia);
    assert (HU0 : U Ee (SLit 0) = 0) by (apply U_lit; lia) end.
  psrr_branch_tok RUN BR HS2 SHOK2 cm_span;
  [ | exfalso; rewrite branch_eq_U, HUk, HU0 in Hc; apply Z.eqb_neq in Hc; lia ].
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ => pose (E' := Ee) end.
  assert (EWlt : forall n, (n < 512)%nat -> ew E' n = ew E n) by (unfold E'; intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msF HS2 eq_refl) as Hmk0. cbn [ss_pc] in Hmk0.
  pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS2 eq_refl) as Rfr.
  pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS2 eq_refl) as Rnch.
  pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS2 eq_refl) as Rcur.
  assert (EW34 : bv_unsigned (ew E' 34) = gF cx fp) by (rewrite (EWlt 34%nat ltac:(lia)); apply (cm_U E 34); [exact F34|lia]).
  assert (EW9 : bv_unsigned (ew E' 9) = c_sp1 cx) by (rewrite (EWlt 9%nat ltac:(lia)); apply (cm_U E 9); [exact F9|lia]).
  assert (EW32 : ew E' 32 = w64 (c_p cx + pos)) by (rewrite (EWlt 32%nat ltac:(lia)); exact F32).
  assert (EW33 : ew E' 33 = w64 (c_n cx - pos)) by (rewrite (EWlt 33%nat ltac:(lia)); exact F33).
  destruct (cm_mac6 E' W3 (ms_mem msF) (gF cx fp) _ _ _ _ _ _ Rfr EW34) as (M & HML & HMac).
  pose proof (cm_slot8 E' W3 (ms_mem msF) _ _ _ _ _ _ 88 (SLit 0) Rnch EW9 ltac:(cbn [In]; tauto) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia)) as Hnch0.
  change (bv_unsigned (sv_denot E' (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in Hnch0.
  set (nch := 0). assert (Hnchr : 0 <= nch < 256) by (unfold nch; lia). assert (Hnchrd : rdword (aview SEGS (w_H W3) (ms_mem msF)) (c_sp1 cx + 88) = Some nch) by exact Hnch0.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 136 32 0 (c_p cx + pos) Rcur EW9 ltac:(cbn [In]; tauto) EW32 Hcppos ltac:(lia)) as Hc88.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 144 33 (0) (c_n cx - pos) Rcur EW9 ltac:(cbn [In]; tauto) EW33 ltac:(lia) ltac:(lia)) as Hc90.
  assert (HK2 : cm_keep cx fp W3 (ms_mem msA) (ms_mem msF)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK2) as HM2.
  assert (RG2 : getr (ms_regs msF) 2 = _) by (prreg HS2 (2%bv : bv 5) PX2; rewrite PX2; rewrite ?(EWlt 2%nat ltac:(lia)); rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (RG8 : getr (ms_regs msF) 8 = _) by (prreg HS2 (8%bv : bv 5) PX8; rewrite PX8; rewrite ?(EWlt 8%nat ltac:(lia)); rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (RG9 : getr (ms_regs msF) 9 = _) by (prreg HS2 (9%bv : bv 5) PX9; rewrite PX9; rewrite ?(EWlt 9%nat ltac:(lia)); rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (RG3 : getr (ms_regs msF) 3 = _) by (prreg HS2 (3%bv : bv 5) PX3; rewrite PX3; rewrite ?(EWlt 3%nat ltac:(lia)); rewrite (EE 3%nat 3%bv eq_refl); exact G3).
  assert (RG4 : getr (ms_regs msF) 4 = _) by (prreg HS2 (4%bv : bv 5) PX4; rewrite PX4; rewrite ?(EWlt 4%nat ltac:(lia)); rewrite (EE 4%nat 4%bv eq_refl); exact G4).
  assert (RG18 : getr (ms_regs msF) 18 = _) by (prreg HS2 (18%bv : bv 5) PX18; rewrite PX18; rewrite ?(EWlt 18%nat ltac:(lia)); rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (RG24 : getr (ms_regs msF) 24 = _) by (prreg HS2 (24%bv : bv 5) PX24; rewrite PX24; rewrite ?(EWlt 24%nat ltac:(lia)); rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (RG20 : getr (ms_regs msF) 20 = _) by (prreg HS2 (20%bv : bv 5) PX20; rewrite PX20; rewrite ?(EWlt 20%nat ltac:(lia)); rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (RG25 : getr (ms_regs msF) 25 = _) by (prreg HS2 (25%bv : bv 5) PX25; rewrite PX25; rewrite ?(EWlt 25%nat ltac:(lia)); rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  prreg HS2 (19%bv : bv 5) PX19. rewrite ?(EWlt 34%nat ltac:(lia)) in PX19; rewrite U34 in PX19.
  apply (cm_land msF _ M nch (pos + 0) HB HJ HFR HMO Hi Hk Hacc HBLK HINV).
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - unfold gregs. split; [exact RG2|]. split; [exact RG8|]. split; [exact RG9|].
    split; [exact RG3|]. split; [exact RG4|]. split; [exact RG18 | exact RG24].
  - exact RG20.
  - unfold GO_MAC; exact PX19.
  - exact RG25.
  - exact HM2.
  - exact HML.
  - unfold GO_MAC. exact HMac.
  - exact Hnchr.
  - unfold gslot. exact Hnchrd.
  - lia.
  - unfold gslot. replace (c_p cx + (pos + 0)) with (c_p cx + pos + 0) by lia. exact Hc88.
  - unfold gslot. replace (c_n cx - (pos + 0)) with (c_n cx - pos + (0)) by lia. exact Hc90.
Qed.

Lemma cm_pathB_k1 : Z.land op 4 <> 0 -> Z.to_nat (Z.min (c_n cx - pos) 7) = 1%nat ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros Hop4 HKK.
  pose proof (cm_geo cx fp k ly3 S3 W3 ms3 md3 r HB HJ HFR HBLK)
    as ((Hs1 & Hs2 & Hs3 & Hs4 & Hs5) & (HF1 & HF2 & HF3 & HF4 & HF6) & (Hr16 & Hr4 & Hrc & Hria & Hrin) & HRF & Hinp).
  pose proof asan_consts as (Hac & _).
  destruct (cm_seat cx fp k ly3 S3 W3 ms3 md3 r pos HB HJ HFR HBLK HBODY HCUR) as [HS SHOK].
  pose proof cm_mem_start as HM.
  pose proof HBODY as (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & _).
  pose proof HCUR as (Hpos & _ & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
  pose proof (fun a => cm_mac_frames cx fp ly3 a EF) as HFA.
  remember (cm_E (ms_regs ms3) cx fp pos) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr (ms_regs ms3) rr)
    by (intros q rr Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (F9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F22 : ew E 22 = w64 op) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (F32 : ew E 32 = w64 (c_p cx + pos))
    by (subst E; unfold cm_E; change 32%nat with (32 + 0)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F33 : ew E 33 = w64 (c_n cx - pos))
    by (subst E; unfold cm_E; change 33%nat with (32 + 1)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F34 : ew E 34 = w64 (gF cx fp))
    by (subst E; unfold cm_E; change 34%nat with (32 + 2)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (FB : forall j, (j < 7)%nat -> ew E (35 + j) = w64 (cm_inbyte cx pos j)).
  { intros j Hj. subst E. unfold cm_E. replace (35 + j)%nat with (32 + (3 + j))%nat by lia.
    rewrite cm_ew_ex by lia. apply cm_ex_byte. exact Hj. }
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (apply (cm_U E 9); [exact F9 | lia]).
  assert (U34 : bv_unsigned (ew E 34) = gF cx fp) by (apply (cm_U E 34); [exact F34 | lia]).
  clear HE.
  
  assert (Gsp : alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
    spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256) by lia.
  assert (GF : 4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512) by (split; [lia|]; split; [lia | exact HF3]).
  assert (GR : 4096 <= r /\ r + 288 <= alloc_ceiling /\ (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r)) by lia.
  assert (GI : c_n cx = 0 \/
    (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx)))
    by (destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpc' & _ & Hpf & _)]; [left; exact Hn0 | right; lia]).
  paj_run_tok RUN HS HJ SHOK cm_span.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
      [reflexivity | exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ].
    apply awr_ok_nil. }
  assert (HK1 : cm_keep cx fp W3 (ms_mem ms3) (ms_mem ms)).
  { apply (cm_keep_frame cx fp W3 E _ _ _ HF).
    let rs' := eval vm_compute in (ss_mem cm_ss0) in change (ss_mem cm_ss0) with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]).
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM HK1) as HM1.
  clear HK1 HF HFr HG HM.
  psrr_branch_tok RUN BR HS SHOK cm_span.
  2: { exfalso. rewrite (cm_and4 E op F22 Hop) in Hc. apply Hop4. destruct (Z.eqb_spec (Z.land op 4) 0); [exact e | discriminate Hc]. }

  assert (Hcppos : 0 <= c_p cx + pos < 2 ^ 64).
  { destruct Hinp as [(Hn0 & Hp0) | (_ & _ & Hp4 & Hpc2 & _)]; [rewrite Hp0; unfold GB_EMPTY; lia | lia]. }
  assert (U32 : bv_unsigned (ew E 32) = c_p cx + pos) by (apply (cm_U E 32); [exact F32 | exact Hcppos]).
  clear Hc.
  set (kk := Z.to_nat (Z.min (c_n cx - pos) 7)).
  assert (Hrem : (Z.of_nat kk = c_n cx - pos /\ (kk < 7)%nat) \/ (kk = 7%nat /\ 7 <= c_n cx - pos)).
  { unfold kk. destruct (Z_lt_le_dec (c_n cx - pos) 7) as [Hlt|Hge];
    [left; split; [rewrite Z2Nat.id by lia; rewrite Z.min_l by lia; reflexivity | rewrite Z.min_l by lia; lia]
    | right; rewrite Z.min_r by lia; split; [reflexivity|lia]]. }
  assert (Hkk7 : (kk <= 7)%nat) by (unfold kk; lia).
  assert (Hkkn : pos + Z.of_nat kk <= c_n cx) by (unfold kk; lia).
  pose proof HJ as (HAR3 & _).
  assert (Hcn : c_n cx < 2 ^ 26) by (destruct Hinp as [(Hn0 & _) | (Hn & _)]; lia).
  pose proof HM1 as (HM1c & _).
  destruct HM1c as (_ & _ & _ & HINm & _).
  assert (Hf33 : afact_ok E 33 (cm_remf 7 kk))
    by (apply (cm_remf_ok E cx pos 7 kk F33); [lia | exact Hcn | lia | reflexivity]).
  assert (Haddk : kk = 0%nat \/ (YP09.region_wf (cm_inb kk) = true /\
     YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (cm_inb kk) /\ YP09.all_disjoint E (cm_inb kk) (ss_mem cm_ss0) /\
     shent_ok SEGS cm_Bx E (mrestrict (w_H W3) (ms_mem ms)) (mkSHE 32 0 (Z.of_nat kk)))).
  { destruct (Nat.eq_dec kk 0) as [->|Hk0]; [left; reflexivity|right].
    assert (Hcn0 : 0 < c_n cx) by (unfold kk in Hk0; lia).
    destruct Hinp as [(Hn0 & _) | (_ & Hin2 & Hp4 & Hpc2 & Hpia & HpF & HpR)]; [lia|].
    split; [apply cm_inb_wf|].
    split; [apply (cm_inb_ok cx pos W3 (ms_mem ms) E kk F32 FB HINm Hkk7); [lia | lia | lia | lia]|].
    split.
    { cbn [cm_ss0 ss_mem]. unfold cm_inb, cm_spill_lo, cm_spill_hi, cm_frame.
      cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
      rewrite U32, U9, U34. repeat split; lia. }
    { apply (cm_inb_sh cx pos ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) E kk HAR3 Hin2 Hcn0 Hpia Hpc2 F18 F32); [lia | lia]. } }
  pose proof (cm_addin E _ ms W3 7 kk HS SHOK Hf33 Haddk) as [HS2 SHOK2].
  assert (Hcur7 : 0 <= pos + Z.of_nat kk <= c_n cx) by lia.
  assert (Ekk : kk = 1%nat) by exact HKK.
  rewrite Ekk in HS2, SHOK2, Hrem, Hcur7.
  clear Hf33 Haddk HS SHOK Hkk7.
  lazymatch type of HS2 with context [kk] => fail 100 "cm_pathB: kk remains in HS2" | _ => idtac end.
  lazymatch type of SHOK2 with context [kk] => fail 100 "cm_pathB: kk remains in SHOK2" | _ => idtac end.
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS2 end.
  lazymatch type of SHOK2 with sh_ok _ _ ?sh _ _ => let v := eval vm_compute in sh in change sh with v in SHOK2 end.
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msA end.
  assert (HK1b : cm_keep cx fp W3 (ms_mem ms) (ms_mem msA)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK1b) as HM1b. clear HM1 HK1b HF HFr HG. rename HM1b into HM1.
  destruct Hrem as [(Hremv & _) | (Hbad & _)]; [| discriminate Hbad]. simpl in Hremv.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ =>
    assert (EW33v : bv_unsigned (ew Ee 33) = c_n cx - pos) by (rewrite ?ew_ewset_other by lia; rewrite F33; apply unsigned_lit_small; lia);
    assert (HUk : U Ee (SOff 33 (-1)) = 0) by (rewrite U_SOff, EW33v; replace (c_n cx - pos + (-1)) with 0 by lia; apply zcanon_id; unfold M64; lia);
    assert (HU0 : U Ee (SLit 0) = 0) by (apply U_lit; lia) end.
  psrr_branch_tok RUN BR HS2 SHOK2 cm_span;
  [ | exfalso; rewrite branch_eq_U, HUk, HU0 in Hc; apply Z.eqb_neq in Hc; lia ].
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ => pose (E' := Ee) end.
  assert (EWlt : forall n, (n < 512)%nat -> ew E' n = ew E n) by (unfold E'; intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msF HS2 eq_refl) as Hmk0. cbn [ss_pc] in Hmk0.
  pose proof (st_ok_pi_region_nth _ _ _ 3%nat _ HS2 eq_refl) as Rfr.
  pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS2 eq_refl) as Rnch.
  pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS2 eq_refl) as Rcur.
  assert (EW34 : bv_unsigned (ew E' 34) = gF cx fp) by (rewrite (EWlt 34%nat ltac:(lia)); apply (cm_U E 34); [exact F34|lia]).
  assert (EW9 : bv_unsigned (ew E' 9) = c_sp1 cx) by (rewrite (EWlt 9%nat ltac:(lia)); apply (cm_U E 9); [exact F9|lia]).
  assert (EW32 : ew E' 32 = w64 (c_p cx + pos)) by (rewrite (EWlt 32%nat ltac:(lia)); exact F32).
  assert (EW33 : ew E' 33 = w64 (c_n cx - pos)) by (rewrite (EWlt 33%nat ltac:(lia)); exact F33).
  destruct (cm_mac6 E' W3 (ms_mem msF) (gF cx fp) _ _ _ _ _ _ Rfr EW34) as (M & HML & HMac).
  pose proof (cm_slot8 E' W3 (ms_mem msF) _ _ _ _ _ _ 88 (SLit 0) Rnch EW9 ltac:(cbn [In]; tauto) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia)) as Hnch0.
  change (bv_unsigned (sv_denot E' (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in Hnch0.
  set (nch := 0). assert (Hnchr : 0 <= nch < 256) by (unfold nch; lia). assert (Hnchrd : rdword (aview SEGS (w_H W3) (ms_mem msF)) (c_sp1 cx + 88) = Some nch) by exact Hnch0.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 136 32 1 (c_p cx + pos) Rcur EW9 ltac:(cbn [In]; tauto) EW32 Hcppos ltac:(lia)) as Hc88.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 144 33 (-1) (c_n cx - pos) Rcur EW9 ltac:(cbn [In]; tauto) EW33 ltac:(lia) ltac:(lia)) as Hc90.
  assert (HK2 : cm_keep cx fp W3 (ms_mem msA) (ms_mem msF)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK2) as HM2.
  assert (RG2 : getr (ms_regs msF) 2 = _) by (prreg HS2 (2%bv : bv 5) PX2; rewrite PX2; rewrite ?(EWlt 2%nat ltac:(lia)); rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (RG8 : getr (ms_regs msF) 8 = _) by (prreg HS2 (8%bv : bv 5) PX8; rewrite PX8; rewrite ?(EWlt 8%nat ltac:(lia)); rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (RG9 : getr (ms_regs msF) 9 = _) by (prreg HS2 (9%bv : bv 5) PX9; rewrite PX9; rewrite ?(EWlt 9%nat ltac:(lia)); rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (RG3 : getr (ms_regs msF) 3 = _) by (prreg HS2 (3%bv : bv 5) PX3; rewrite PX3; rewrite ?(EWlt 3%nat ltac:(lia)); rewrite (EE 3%nat 3%bv eq_refl); exact G3).
  assert (RG4 : getr (ms_regs msF) 4 = _) by (prreg HS2 (4%bv : bv 5) PX4; rewrite PX4; rewrite ?(EWlt 4%nat ltac:(lia)); rewrite (EE 4%nat 4%bv eq_refl); exact G4).
  assert (RG18 : getr (ms_regs msF) 18 = _) by (prreg HS2 (18%bv : bv 5) PX18; rewrite PX18; rewrite ?(EWlt 18%nat ltac:(lia)); rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (RG24 : getr (ms_regs msF) 24 = _) by (prreg HS2 (24%bv : bv 5) PX24; rewrite PX24; rewrite ?(EWlt 24%nat ltac:(lia)); rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (RG20 : getr (ms_regs msF) 20 = _) by (prreg HS2 (20%bv : bv 5) PX20; rewrite PX20; rewrite ?(EWlt 20%nat ltac:(lia)); rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (RG25 : getr (ms_regs msF) 25 = _) by (prreg HS2 (25%bv : bv 5) PX25; rewrite PX25; rewrite ?(EWlt 25%nat ltac:(lia)); rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  prreg HS2 (19%bv : bv 5) PX19. rewrite ?(EWlt 34%nat ltac:(lia)) in PX19; rewrite U34 in PX19.
  apply (cm_land msF _ M nch (pos + 1) HB HJ HFR HMO Hi Hk Hacc HBLK HINV).
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - unfold gregs. split; [exact RG2|]. split; [exact RG8|]. split; [exact RG9|].
    split; [exact RG3|]. split; [exact RG4|]. split; [exact RG18 | exact RG24].
  - exact RG20.
  - unfold GO_MAC; exact PX19.
  - exact RG25.
  - exact HM2.
  - exact HML.
  - unfold GO_MAC. exact HMac.
  - exact Hnchr.
  - unfold gslot. exact Hnchrd.
  - lia.
  - unfold gslot. replace (c_p cx + (pos + 1)) with (c_p cx + pos + 1) by lia. exact Hc88.
  - unfold gslot. replace (c_n cx - (pos + 1)) with (c_n cx - pos + (-1)) by lia. exact Hc90.
Qed.

Lemma cm_pathB_k2 : Z.land op 4 <> 0 -> Z.to_nat (Z.min (c_n cx - pos) 7) = 2%nat ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros Hop4 HKK.
  pose proof (cm_geo cx fp k ly3 S3 W3 ms3 md3 r HB HJ HFR HBLK)
    as ((Hs1 & Hs2 & Hs3 & Hs4 & Hs5) & (HF1 & HF2 & HF3 & HF4 & HF6) & (Hr16 & Hr4 & Hrc & Hria & Hrin) & HRF & Hinp).
  pose proof asan_consts as (Hac & _).
  destruct (cm_seat cx fp k ly3 S3 W3 ms3 md3 r pos HB HJ HFR HBLK HBODY HCUR) as [HS SHOK].
  pose proof cm_mem_start as HM.
  pose proof HBODY as (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & _).
  pose proof HCUR as (Hpos & _ & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
  pose proof (fun a => cm_mac_frames cx fp ly3 a EF) as HFA.
  remember (cm_E (ms_regs ms3) cx fp pos) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr (ms_regs ms3) rr)
    by (intros q rr Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (F9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F22 : ew E 22 = w64 op) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (F32 : ew E 32 = w64 (c_p cx + pos))
    by (subst E; unfold cm_E; change 32%nat with (32 + 0)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F33 : ew E 33 = w64 (c_n cx - pos))
    by (subst E; unfold cm_E; change 33%nat with (32 + 1)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F34 : ew E 34 = w64 (gF cx fp))
    by (subst E; unfold cm_E; change 34%nat with (32 + 2)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (FB : forall j, (j < 7)%nat -> ew E (35 + j) = w64 (cm_inbyte cx pos j)).
  { intros j Hj. subst E. unfold cm_E. replace (35 + j)%nat with (32 + (3 + j))%nat by lia.
    rewrite cm_ew_ex by lia. apply cm_ex_byte. exact Hj. }
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (apply (cm_U E 9); [exact F9 | lia]).
  assert (U34 : bv_unsigned (ew E 34) = gF cx fp) by (apply (cm_U E 34); [exact F34 | lia]).
  clear HE.
  
  assert (Gsp : alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
    spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256) by lia.
  assert (GF : 4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512) by (split; [lia|]; split; [lia | exact HF3]).
  assert (GR : 4096 <= r /\ r + 288 <= alloc_ceiling /\ (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r)) by lia.
  assert (GI : c_n cx = 0 \/
    (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx)))
    by (destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpc' & _ & Hpf & _)]; [left; exact Hn0 | right; lia]).
  paj_run_tok RUN HS HJ SHOK cm_span.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
      [reflexivity | exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ].
    apply awr_ok_nil. }
  assert (HK1 : cm_keep cx fp W3 (ms_mem ms3) (ms_mem ms)).
  { apply (cm_keep_frame cx fp W3 E _ _ _ HF).
    let rs' := eval vm_compute in (ss_mem cm_ss0) in change (ss_mem cm_ss0) with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]).
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM HK1) as HM1.
  clear HK1 HF HFr HG HM.
  psrr_branch_tok RUN BR HS SHOK cm_span.
  2: { exfalso. rewrite (cm_and4 E op F22 Hop) in Hc. apply Hop4. destruct (Z.eqb_spec (Z.land op 4) 0); [exact e | discriminate Hc]. }

  assert (Hcppos : 0 <= c_p cx + pos < 2 ^ 64).
  { destruct Hinp as [(Hn0 & Hp0) | (_ & _ & Hp4 & Hpc2 & _)]; [rewrite Hp0; unfold GB_EMPTY; lia | lia]. }
  assert (U32 : bv_unsigned (ew E 32) = c_p cx + pos) by (apply (cm_U E 32); [exact F32 | exact Hcppos]).
  clear Hc.
  set (kk := Z.to_nat (Z.min (c_n cx - pos) 7)).
  assert (Hrem : (Z.of_nat kk = c_n cx - pos /\ (kk < 7)%nat) \/ (kk = 7%nat /\ 7 <= c_n cx - pos)).
  { unfold kk. destruct (Z_lt_le_dec (c_n cx - pos) 7) as [Hlt|Hge];
    [left; split; [rewrite Z2Nat.id by lia; rewrite Z.min_l by lia; reflexivity | rewrite Z.min_l by lia; lia]
    | right; rewrite Z.min_r by lia; split; [reflexivity|lia]]. }
  assert (Hkk7 : (kk <= 7)%nat) by (unfold kk; lia).
  assert (Hkkn : pos + Z.of_nat kk <= c_n cx) by (unfold kk; lia).
  pose proof HJ as (HAR3 & _).
  assert (Hcn : c_n cx < 2 ^ 26) by (destruct Hinp as [(Hn0 & _) | (Hn & _)]; lia).
  pose proof HM1 as (HM1c & _).
  destruct HM1c as (_ & _ & _ & HINm & _).
  assert (Hf33 : afact_ok E 33 (cm_remf 7 kk))
    by (apply (cm_remf_ok E cx pos 7 kk F33); [lia | exact Hcn | lia | reflexivity]).
  assert (Haddk : kk = 0%nat \/ (YP09.region_wf (cm_inb kk) = true /\
     YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (cm_inb kk) /\ YP09.all_disjoint E (cm_inb kk) (ss_mem cm_ss0) /\
     shent_ok SEGS cm_Bx E (mrestrict (w_H W3) (ms_mem ms)) (mkSHE 32 0 (Z.of_nat kk)))).
  { destruct (Nat.eq_dec kk 0) as [->|Hk0]; [left; reflexivity|right].
    assert (Hcn0 : 0 < c_n cx) by (unfold kk in Hk0; lia).
    destruct Hinp as [(Hn0 & _) | (_ & Hin2 & Hp4 & Hpc2 & Hpia & HpF & HpR)]; [lia|].
    split; [apply cm_inb_wf|].
    split; [apply (cm_inb_ok cx pos W3 (ms_mem ms) E kk F32 FB HINm Hkk7); [lia | lia | lia | lia]|].
    split.
    { cbn [cm_ss0 ss_mem]. unfold cm_inb, cm_spill_lo, cm_spill_hi, cm_frame.
      cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
      rewrite U32, U9, U34. repeat split; lia. }
    { apply (cm_inb_sh cx pos ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) E kk HAR3 Hin2 Hcn0 Hpia Hpc2 F18 F32); [lia | lia]. } }
  pose proof (cm_addin E _ ms W3 7 kk HS SHOK Hf33 Haddk) as [HS2 SHOK2].
  assert (Hcur7 : 0 <= pos + Z.of_nat kk <= c_n cx) by lia.
  assert (Ekk : kk = 2%nat) by exact HKK.
  rewrite Ekk in HS2, SHOK2, Hrem, Hcur7.
  clear Hf33 Haddk HS SHOK Hkk7.
  lazymatch type of HS2 with context [kk] => fail 100 "cm_pathB: kk remains in HS2" | _ => idtac end.
  lazymatch type of SHOK2 with context [kk] => fail 100 "cm_pathB: kk remains in SHOK2" | _ => idtac end.
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS2 end.
  lazymatch type of SHOK2 with sh_ok _ _ ?sh _ _ => let v := eval vm_compute in sh in change sh with v in SHOK2 end.
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msA end.
  assert (HK1b : cm_keep cx fp W3 (ms_mem ms) (ms_mem msA)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK1b) as HM1b. clear HM1 HK1b HF HFr HG. rename HM1b into HM1.
  destruct Hrem as [(Hremv & _) | (Hbad & _)]; [| discriminate Hbad]. simpl in Hremv.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ =>
    assert (EW33v : bv_unsigned (ew Ee 33) = c_n cx - pos) by (rewrite ?ew_ewset_other by lia; rewrite F33; apply unsigned_lit_small; lia);
    assert (HUk : U Ee (SOff 33 (-2)) = 0) by (rewrite U_SOff, EW33v; replace (c_n cx - pos + (-2)) with 0 by lia; apply zcanon_id; unfold M64; lia);
    assert (HU0 : U Ee (SLit 0) = 0) by (apply U_lit; lia) end.
  psrr_branch_tok RUN BR HS2 SHOK2 cm_span;
  [ | exfalso; rewrite branch_eq_U, HUk, HU0 in Hc; apply Z.eqb_neq in Hc; lia ].
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ => pose (E' := Ee) end.
  assert (EWlt : forall n, (n < 512)%nat -> ew E' n = ew E n) by (unfold E'; intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msF HS2 eq_refl) as Hmk0. cbn [ss_pc] in Hmk0.
  pose proof (st_ok_pi_region_nth _ _ _ 3%nat _ HS2 eq_refl) as Rfr.
  pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS2 eq_refl) as Rnch.
  pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS2 eq_refl) as Rcur.
  assert (EW34 : bv_unsigned (ew E' 34) = gF cx fp) by (rewrite (EWlt 34%nat ltac:(lia)); apply (cm_U E 34); [exact F34|lia]).
  assert (EW9 : bv_unsigned (ew E' 9) = c_sp1 cx) by (rewrite (EWlt 9%nat ltac:(lia)); apply (cm_U E 9); [exact F9|lia]).
  assert (EW32 : ew E' 32 = w64 (c_p cx + pos)) by (rewrite (EWlt 32%nat ltac:(lia)); exact F32).
  assert (EW33 : ew E' 33 = w64 (c_n cx - pos)) by (rewrite (EWlt 33%nat ltac:(lia)); exact F33).
  destruct (cm_mac6 E' W3 (ms_mem msF) (gF cx fp) _ _ _ _ _ _ Rfr EW34) as (M & HML & HMac).
  pose proof (cm_slot8 E' W3 (ms_mem msF) _ _ _ _ _ _ 88 (SLit 0) Rnch EW9 ltac:(cbn [In]; tauto) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia)) as Hnch0.
  change (bv_unsigned (sv_denot E' (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in Hnch0.
  set (nch := 0). assert (Hnchr : 0 <= nch < 256) by (unfold nch; lia). assert (Hnchrd : rdword (aview SEGS (w_H W3) (ms_mem msF)) (c_sp1 cx + 88) = Some nch) by exact Hnch0.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 136 32 2 (c_p cx + pos) Rcur EW9 ltac:(cbn [In]; tauto) EW32 Hcppos ltac:(lia)) as Hc88.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 144 33 (-2) (c_n cx - pos) Rcur EW9 ltac:(cbn [In]; tauto) EW33 ltac:(lia) ltac:(lia)) as Hc90.
  assert (HK2 : cm_keep cx fp W3 (ms_mem msA) (ms_mem msF)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK2) as HM2.
  assert (RG2 : getr (ms_regs msF) 2 = _) by (prreg HS2 (2%bv : bv 5) PX2; rewrite PX2; rewrite ?(EWlt 2%nat ltac:(lia)); rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (RG8 : getr (ms_regs msF) 8 = _) by (prreg HS2 (8%bv : bv 5) PX8; rewrite PX8; rewrite ?(EWlt 8%nat ltac:(lia)); rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (RG9 : getr (ms_regs msF) 9 = _) by (prreg HS2 (9%bv : bv 5) PX9; rewrite PX9; rewrite ?(EWlt 9%nat ltac:(lia)); rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (RG3 : getr (ms_regs msF) 3 = _) by (prreg HS2 (3%bv : bv 5) PX3; rewrite PX3; rewrite ?(EWlt 3%nat ltac:(lia)); rewrite (EE 3%nat 3%bv eq_refl); exact G3).
  assert (RG4 : getr (ms_regs msF) 4 = _) by (prreg HS2 (4%bv : bv 5) PX4; rewrite PX4; rewrite ?(EWlt 4%nat ltac:(lia)); rewrite (EE 4%nat 4%bv eq_refl); exact G4).
  assert (RG18 : getr (ms_regs msF) 18 = _) by (prreg HS2 (18%bv : bv 5) PX18; rewrite PX18; rewrite ?(EWlt 18%nat ltac:(lia)); rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (RG24 : getr (ms_regs msF) 24 = _) by (prreg HS2 (24%bv : bv 5) PX24; rewrite PX24; rewrite ?(EWlt 24%nat ltac:(lia)); rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (RG20 : getr (ms_regs msF) 20 = _) by (prreg HS2 (20%bv : bv 5) PX20; rewrite PX20; rewrite ?(EWlt 20%nat ltac:(lia)); rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (RG25 : getr (ms_regs msF) 25 = _) by (prreg HS2 (25%bv : bv 5) PX25; rewrite PX25; rewrite ?(EWlt 25%nat ltac:(lia)); rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  prreg HS2 (19%bv : bv 5) PX19. rewrite ?(EWlt 34%nat ltac:(lia)) in PX19; rewrite U34 in PX19.
  apply (cm_land msF _ M nch (pos + 2) HB HJ HFR HMO Hi Hk Hacc HBLK HINV).
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - unfold gregs. split; [exact RG2|]. split; [exact RG8|]. split; [exact RG9|].
    split; [exact RG3|]. split; [exact RG4|]. split; [exact RG18 | exact RG24].
  - exact RG20.
  - unfold GO_MAC; exact PX19.
  - exact RG25.
  - exact HM2.
  - exact HML.
  - unfold GO_MAC. exact HMac.
  - exact Hnchr.
  - unfold gslot. exact Hnchrd.
  - lia.
  - unfold gslot. replace (c_p cx + (pos + 2)) with (c_p cx + pos + 2) by lia. exact Hc88.
  - unfold gslot. replace (c_n cx - (pos + 2)) with (c_n cx - pos + (-2)) by lia. exact Hc90.
Qed.

Lemma cm_pathB_k3 : Z.land op 4 <> 0 -> Z.to_nat (Z.min (c_n cx - pos) 7) = 3%nat ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros Hop4 HKK.
  pose proof (cm_geo cx fp k ly3 S3 W3 ms3 md3 r HB HJ HFR HBLK)
    as ((Hs1 & Hs2 & Hs3 & Hs4 & Hs5) & (HF1 & HF2 & HF3 & HF4 & HF6) & (Hr16 & Hr4 & Hrc & Hria & Hrin) & HRF & Hinp).
  pose proof asan_consts as (Hac & _).
  destruct (cm_seat cx fp k ly3 S3 W3 ms3 md3 r pos HB HJ HFR HBLK HBODY HCUR) as [HS SHOK].
  pose proof cm_mem_start as HM.
  pose proof HBODY as (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & _).
  pose proof HCUR as (Hpos & _ & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
  pose proof (fun a => cm_mac_frames cx fp ly3 a EF) as HFA.
  remember (cm_E (ms_regs ms3) cx fp pos) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr (ms_regs ms3) rr)
    by (intros q rr Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (F9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F22 : ew E 22 = w64 op) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (F32 : ew E 32 = w64 (c_p cx + pos))
    by (subst E; unfold cm_E; change 32%nat with (32 + 0)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F33 : ew E 33 = w64 (c_n cx - pos))
    by (subst E; unfold cm_E; change 33%nat with (32 + 1)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F34 : ew E 34 = w64 (gF cx fp))
    by (subst E; unfold cm_E; change 34%nat with (32 + 2)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (FB : forall j, (j < 7)%nat -> ew E (35 + j) = w64 (cm_inbyte cx pos j)).
  { intros j Hj. subst E. unfold cm_E. replace (35 + j)%nat with (32 + (3 + j))%nat by lia.
    rewrite cm_ew_ex by lia. apply cm_ex_byte. exact Hj. }
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (apply (cm_U E 9); [exact F9 | lia]).
  assert (U34 : bv_unsigned (ew E 34) = gF cx fp) by (apply (cm_U E 34); [exact F34 | lia]).
  clear HE.
  
  assert (Gsp : alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
    spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256) by lia.
  assert (GF : 4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512) by (split; [lia|]; split; [lia | exact HF3]).
  assert (GR : 4096 <= r /\ r + 288 <= alloc_ceiling /\ (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r)) by lia.
  assert (GI : c_n cx = 0 \/
    (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx)))
    by (destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpc' & _ & Hpf & _)]; [left; exact Hn0 | right; lia]).
  paj_run_tok RUN HS HJ SHOK cm_span.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
      [reflexivity | exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ].
    apply awr_ok_nil. }
  assert (HK1 : cm_keep cx fp W3 (ms_mem ms3) (ms_mem ms)).
  { apply (cm_keep_frame cx fp W3 E _ _ _ HF).
    let rs' := eval vm_compute in (ss_mem cm_ss0) in change (ss_mem cm_ss0) with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]).
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM HK1) as HM1.
  clear HK1 HF HFr HG HM.
  psrr_branch_tok RUN BR HS SHOK cm_span.
  2: { exfalso. rewrite (cm_and4 E op F22 Hop) in Hc. apply Hop4. destruct (Z.eqb_spec (Z.land op 4) 0); [exact e | discriminate Hc]. }

  assert (Hcppos : 0 <= c_p cx + pos < 2 ^ 64).
  { destruct Hinp as [(Hn0 & Hp0) | (_ & _ & Hp4 & Hpc2 & _)]; [rewrite Hp0; unfold GB_EMPTY; lia | lia]. }
  assert (U32 : bv_unsigned (ew E 32) = c_p cx + pos) by (apply (cm_U E 32); [exact F32 | exact Hcppos]).
  clear Hc.
  set (kk := Z.to_nat (Z.min (c_n cx - pos) 7)).
  assert (Hrem : (Z.of_nat kk = c_n cx - pos /\ (kk < 7)%nat) \/ (kk = 7%nat /\ 7 <= c_n cx - pos)).
  { unfold kk. destruct (Z_lt_le_dec (c_n cx - pos) 7) as [Hlt|Hge];
    [left; split; [rewrite Z2Nat.id by lia; rewrite Z.min_l by lia; reflexivity | rewrite Z.min_l by lia; lia]
    | right; rewrite Z.min_r by lia; split; [reflexivity|lia]]. }
  assert (Hkk7 : (kk <= 7)%nat) by (unfold kk; lia).
  assert (Hkkn : pos + Z.of_nat kk <= c_n cx) by (unfold kk; lia).
  pose proof HJ as (HAR3 & _).
  assert (Hcn : c_n cx < 2 ^ 26) by (destruct Hinp as [(Hn0 & _) | (Hn & _)]; lia).
  pose proof HM1 as (HM1c & _).
  destruct HM1c as (_ & _ & _ & HINm & _).
  assert (Hf33 : afact_ok E 33 (cm_remf 7 kk))
    by (apply (cm_remf_ok E cx pos 7 kk F33); [lia | exact Hcn | lia | reflexivity]).
  assert (Haddk : kk = 0%nat \/ (YP09.region_wf (cm_inb kk) = true /\
     YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (cm_inb kk) /\ YP09.all_disjoint E (cm_inb kk) (ss_mem cm_ss0) /\
     shent_ok SEGS cm_Bx E (mrestrict (w_H W3) (ms_mem ms)) (mkSHE 32 0 (Z.of_nat kk)))).
  { destruct (Nat.eq_dec kk 0) as [->|Hk0]; [left; reflexivity|right].
    assert (Hcn0 : 0 < c_n cx) by (unfold kk in Hk0; lia).
    destruct Hinp as [(Hn0 & _) | (_ & Hin2 & Hp4 & Hpc2 & Hpia & HpF & HpR)]; [lia|].
    split; [apply cm_inb_wf|].
    split; [apply (cm_inb_ok cx pos W3 (ms_mem ms) E kk F32 FB HINm Hkk7); [lia | lia | lia | lia]|].
    split.
    { cbn [cm_ss0 ss_mem]. unfold cm_inb, cm_spill_lo, cm_spill_hi, cm_frame.
      cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
      rewrite U32, U9, U34. repeat split; lia. }
    { apply (cm_inb_sh cx pos ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) E kk HAR3 Hin2 Hcn0 Hpia Hpc2 F18 F32); [lia | lia]. } }
  pose proof (cm_addin E _ ms W3 7 kk HS SHOK Hf33 Haddk) as [HS2 SHOK2].
  assert (Hcur7 : 0 <= pos + Z.of_nat kk <= c_n cx) by lia.
  assert (Ekk : kk = 3%nat) by exact HKK.
  rewrite Ekk in HS2, SHOK2, Hrem, Hcur7.
  clear Hf33 Haddk HS SHOK Hkk7.
  lazymatch type of HS2 with context [kk] => fail 100 "cm_pathB: kk remains in HS2" | _ => idtac end.
  lazymatch type of SHOK2 with context [kk] => fail 100 "cm_pathB: kk remains in SHOK2" | _ => idtac end.
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS2 end.
  lazymatch type of SHOK2 with sh_ok _ _ ?sh _ _ => let v := eval vm_compute in sh in change sh with v in SHOK2 end.
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msA end.
  assert (HK1b : cm_keep cx fp W3 (ms_mem ms) (ms_mem msA)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK1b) as HM1b. clear HM1 HK1b HF HFr HG. rename HM1b into HM1.
  destruct Hrem as [(Hremv & _) | (Hbad & _)]; [| discriminate Hbad]. simpl in Hremv.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ =>
    assert (EW33v : bv_unsigned (ew Ee 33) = c_n cx - pos) by (rewrite ?ew_ewset_other by lia; rewrite F33; apply unsigned_lit_small; lia);
    assert (HUk : U Ee (SOff 33 (-3)) = 0) by (rewrite U_SOff, EW33v; replace (c_n cx - pos + (-3)) with 0 by lia; apply zcanon_id; unfold M64; lia);
    assert (HU0 : U Ee (SLit 0) = 0) by (apply U_lit; lia) end.
  psrr_branch_tok RUN BR HS2 SHOK2 cm_span;
  [ | exfalso; rewrite branch_eq_U, HUk, HU0 in Hc; apply Z.eqb_neq in Hc; lia ].
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ => pose (E' := Ee) end.
  assert (EWlt : forall n, (n < 512)%nat -> ew E' n = ew E n) by (unfold E'; intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msF HS2 eq_refl) as Hmk0. cbn [ss_pc] in Hmk0.
  pose proof (st_ok_pi_region_nth _ _ _ 3%nat _ HS2 eq_refl) as Rfr.
  pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS2 eq_refl) as Rnch.
  pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS2 eq_refl) as Rcur.
  assert (EW34 : bv_unsigned (ew E' 34) = gF cx fp) by (rewrite (EWlt 34%nat ltac:(lia)); apply (cm_U E 34); [exact F34|lia]).
  assert (EW9 : bv_unsigned (ew E' 9) = c_sp1 cx) by (rewrite (EWlt 9%nat ltac:(lia)); apply (cm_U E 9); [exact F9|lia]).
  assert (EW32 : ew E' 32 = w64 (c_p cx + pos)) by (rewrite (EWlt 32%nat ltac:(lia)); exact F32).
  assert (EW33 : ew E' 33 = w64 (c_n cx - pos)) by (rewrite (EWlt 33%nat ltac:(lia)); exact F33).
  destruct (cm_mac6 E' W3 (ms_mem msF) (gF cx fp) _ _ _ _ _ _ Rfr EW34) as (M & HML & HMac).
  pose proof (cm_slot8 E' W3 (ms_mem msF) _ _ _ _ _ _ 88 (SLit 0) Rnch EW9 ltac:(cbn [In]; tauto) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia)) as Hnch0.
  change (bv_unsigned (sv_denot E' (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in Hnch0.
  set (nch := 0). assert (Hnchr : 0 <= nch < 256) by (unfold nch; lia). assert (Hnchrd : rdword (aview SEGS (w_H W3) (ms_mem msF)) (c_sp1 cx + 88) = Some nch) by exact Hnch0.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 136 32 3 (c_p cx + pos) Rcur EW9 ltac:(cbn [In]; tauto) EW32 Hcppos ltac:(lia)) as Hc88.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 144 33 (-3) (c_n cx - pos) Rcur EW9 ltac:(cbn [In]; tauto) EW33 ltac:(lia) ltac:(lia)) as Hc90.
  assert (HK2 : cm_keep cx fp W3 (ms_mem msA) (ms_mem msF)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK2) as HM2.
  assert (RG2 : getr (ms_regs msF) 2 = _) by (prreg HS2 (2%bv : bv 5) PX2; rewrite PX2; rewrite ?(EWlt 2%nat ltac:(lia)); rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (RG8 : getr (ms_regs msF) 8 = _) by (prreg HS2 (8%bv : bv 5) PX8; rewrite PX8; rewrite ?(EWlt 8%nat ltac:(lia)); rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (RG9 : getr (ms_regs msF) 9 = _) by (prreg HS2 (9%bv : bv 5) PX9; rewrite PX9; rewrite ?(EWlt 9%nat ltac:(lia)); rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (RG3 : getr (ms_regs msF) 3 = _) by (prreg HS2 (3%bv : bv 5) PX3; rewrite PX3; rewrite ?(EWlt 3%nat ltac:(lia)); rewrite (EE 3%nat 3%bv eq_refl); exact G3).
  assert (RG4 : getr (ms_regs msF) 4 = _) by (prreg HS2 (4%bv : bv 5) PX4; rewrite PX4; rewrite ?(EWlt 4%nat ltac:(lia)); rewrite (EE 4%nat 4%bv eq_refl); exact G4).
  assert (RG18 : getr (ms_regs msF) 18 = _) by (prreg HS2 (18%bv : bv 5) PX18; rewrite PX18; rewrite ?(EWlt 18%nat ltac:(lia)); rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (RG24 : getr (ms_regs msF) 24 = _) by (prreg HS2 (24%bv : bv 5) PX24; rewrite PX24; rewrite ?(EWlt 24%nat ltac:(lia)); rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (RG20 : getr (ms_regs msF) 20 = _) by (prreg HS2 (20%bv : bv 5) PX20; rewrite PX20; rewrite ?(EWlt 20%nat ltac:(lia)); rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (RG25 : getr (ms_regs msF) 25 = _) by (prreg HS2 (25%bv : bv 5) PX25; rewrite PX25; rewrite ?(EWlt 25%nat ltac:(lia)); rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  prreg HS2 (19%bv : bv 5) PX19. rewrite ?(EWlt 34%nat ltac:(lia)) in PX19; rewrite U34 in PX19.
  apply (cm_land msF _ M nch (pos + 3) HB HJ HFR HMO Hi Hk Hacc HBLK HINV).
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - unfold gregs. split; [exact RG2|]. split; [exact RG8|]. split; [exact RG9|].
    split; [exact RG3|]. split; [exact RG4|]. split; [exact RG18 | exact RG24].
  - exact RG20.
  - unfold GO_MAC; exact PX19.
  - exact RG25.
  - exact HM2.
  - exact HML.
  - unfold GO_MAC. exact HMac.
  - exact Hnchr.
  - unfold gslot. exact Hnchrd.
  - lia.
  - unfold gslot. replace (c_p cx + (pos + 3)) with (c_p cx + pos + 3) by lia. exact Hc88.
  - unfold gslot. replace (c_n cx - (pos + 3)) with (c_n cx - pos + (-3)) by lia. exact Hc90.
Qed.

Lemma cm_pathB_k4 : Z.land op 4 <> 0 -> Z.to_nat (Z.min (c_n cx - pos) 7) = 4%nat ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros Hop4 HKK.
  pose proof (cm_geo cx fp k ly3 S3 W3 ms3 md3 r HB HJ HFR HBLK)
    as ((Hs1 & Hs2 & Hs3 & Hs4 & Hs5) & (HF1 & HF2 & HF3 & HF4 & HF6) & (Hr16 & Hr4 & Hrc & Hria & Hrin) & HRF & Hinp).
  pose proof asan_consts as (Hac & _).
  destruct (cm_seat cx fp k ly3 S3 W3 ms3 md3 r pos HB HJ HFR HBLK HBODY HCUR) as [HS SHOK].
  pose proof cm_mem_start as HM.
  pose proof HBODY as (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & _).
  pose proof HCUR as (Hpos & _ & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
  pose proof (fun a => cm_mac_frames cx fp ly3 a EF) as HFA.
  remember (cm_E (ms_regs ms3) cx fp pos) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr (ms_regs ms3) rr)
    by (intros q rr Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (F9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F22 : ew E 22 = w64 op) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (F32 : ew E 32 = w64 (c_p cx + pos))
    by (subst E; unfold cm_E; change 32%nat with (32 + 0)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F33 : ew E 33 = w64 (c_n cx - pos))
    by (subst E; unfold cm_E; change 33%nat with (32 + 1)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F34 : ew E 34 = w64 (gF cx fp))
    by (subst E; unfold cm_E; change 34%nat with (32 + 2)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (FB : forall j, (j < 7)%nat -> ew E (35 + j) = w64 (cm_inbyte cx pos j)).
  { intros j Hj. subst E. unfold cm_E. replace (35 + j)%nat with (32 + (3 + j))%nat by lia.
    rewrite cm_ew_ex by lia. apply cm_ex_byte. exact Hj. }
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (apply (cm_U E 9); [exact F9 | lia]).
  assert (U34 : bv_unsigned (ew E 34) = gF cx fp) by (apply (cm_U E 34); [exact F34 | lia]).
  clear HE.
  
  assert (Gsp : alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
    spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256) by lia.
  assert (GF : 4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512) by (split; [lia|]; split; [lia | exact HF3]).
  assert (GR : 4096 <= r /\ r + 288 <= alloc_ceiling /\ (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r)) by lia.
  assert (GI : c_n cx = 0 \/
    (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx)))
    by (destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpc' & _ & Hpf & _)]; [left; exact Hn0 | right; lia]).
  paj_run_tok RUN HS HJ SHOK cm_span.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
      [reflexivity | exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ].
    apply awr_ok_nil. }
  assert (HK1 : cm_keep cx fp W3 (ms_mem ms3) (ms_mem ms)).
  { apply (cm_keep_frame cx fp W3 E _ _ _ HF).
    let rs' := eval vm_compute in (ss_mem cm_ss0) in change (ss_mem cm_ss0) with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]).
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM HK1) as HM1.
  clear HK1 HF HFr HG HM.
  psrr_branch_tok RUN BR HS SHOK cm_span.
  2: { exfalso. rewrite (cm_and4 E op F22 Hop) in Hc. apply Hop4. destruct (Z.eqb_spec (Z.land op 4) 0); [exact e | discriminate Hc]. }

  assert (Hcppos : 0 <= c_p cx + pos < 2 ^ 64).
  { destruct Hinp as [(Hn0 & Hp0) | (_ & _ & Hp4 & Hpc2 & _)]; [rewrite Hp0; unfold GB_EMPTY; lia | lia]. }
  assert (U32 : bv_unsigned (ew E 32) = c_p cx + pos) by (apply (cm_U E 32); [exact F32 | exact Hcppos]).
  clear Hc.
  set (kk := Z.to_nat (Z.min (c_n cx - pos) 7)).
  assert (Hrem : (Z.of_nat kk = c_n cx - pos /\ (kk < 7)%nat) \/ (kk = 7%nat /\ 7 <= c_n cx - pos)).
  { unfold kk. destruct (Z_lt_le_dec (c_n cx - pos) 7) as [Hlt|Hge];
    [left; split; [rewrite Z2Nat.id by lia; rewrite Z.min_l by lia; reflexivity | rewrite Z.min_l by lia; lia]
    | right; rewrite Z.min_r by lia; split; [reflexivity|lia]]. }
  assert (Hkk7 : (kk <= 7)%nat) by (unfold kk; lia).
  assert (Hkkn : pos + Z.of_nat kk <= c_n cx) by (unfold kk; lia).
  pose proof HJ as (HAR3 & _).
  assert (Hcn : c_n cx < 2 ^ 26) by (destruct Hinp as [(Hn0 & _) | (Hn & _)]; lia).
  pose proof HM1 as (HM1c & _).
  destruct HM1c as (_ & _ & _ & HINm & _).
  assert (Hf33 : afact_ok E 33 (cm_remf 7 kk))
    by (apply (cm_remf_ok E cx pos 7 kk F33); [lia | exact Hcn | lia | reflexivity]).
  assert (Haddk : kk = 0%nat \/ (YP09.region_wf (cm_inb kk) = true /\
     YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (cm_inb kk) /\ YP09.all_disjoint E (cm_inb kk) (ss_mem cm_ss0) /\
     shent_ok SEGS cm_Bx E (mrestrict (w_H W3) (ms_mem ms)) (mkSHE 32 0 (Z.of_nat kk)))).
  { destruct (Nat.eq_dec kk 0) as [->|Hk0]; [left; reflexivity|right].
    assert (Hcn0 : 0 < c_n cx) by (unfold kk in Hk0; lia).
    destruct Hinp as [(Hn0 & _) | (_ & Hin2 & Hp4 & Hpc2 & Hpia & HpF & HpR)]; [lia|].
    split; [apply cm_inb_wf|].
    split; [apply (cm_inb_ok cx pos W3 (ms_mem ms) E kk F32 FB HINm Hkk7); [lia | lia | lia | lia]|].
    split.
    { cbn [cm_ss0 ss_mem]. unfold cm_inb, cm_spill_lo, cm_spill_hi, cm_frame.
      cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
      rewrite U32, U9, U34. repeat split; lia. }
    { apply (cm_inb_sh cx pos ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) E kk HAR3 Hin2 Hcn0 Hpia Hpc2 F18 F32); [lia | lia]. } }
  pose proof (cm_addin E _ ms W3 7 kk HS SHOK Hf33 Haddk) as [HS2 SHOK2].
  assert (Hcur7 : 0 <= pos + Z.of_nat kk <= c_n cx) by lia.
  assert (Ekk : kk = 4%nat) by exact HKK.
  rewrite Ekk in HS2, SHOK2, Hrem, Hcur7.
  clear Hf33 Haddk HS SHOK Hkk7.
  lazymatch type of HS2 with context [kk] => fail 100 "cm_pathB: kk remains in HS2" | _ => idtac end.
  lazymatch type of SHOK2 with context [kk] => fail 100 "cm_pathB: kk remains in SHOK2" | _ => idtac end.
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS2 end.
  lazymatch type of SHOK2 with sh_ok _ _ ?sh _ _ => let v := eval vm_compute in sh in change sh with v in SHOK2 end.
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msA end.
  assert (HK1b : cm_keep cx fp W3 (ms_mem ms) (ms_mem msA)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK1b) as HM1b. clear HM1 HK1b HF HFr HG. rename HM1b into HM1.
  destruct Hrem as [(Hremv & _) | (Hbad & _)]; [| discriminate Hbad]. simpl in Hremv.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ =>
    assert (EW33v : bv_unsigned (ew Ee 33) = c_n cx - pos) by (rewrite ?ew_ewset_other by lia; rewrite F33; apply unsigned_lit_small; lia);
    assert (HUk : U Ee (SOff 33 (-4)) = 0) by (rewrite U_SOff, EW33v; replace (c_n cx - pos + (-4)) with 0 by lia; apply zcanon_id; unfold M64; lia);
    assert (HU0 : U Ee (SLit 0) = 0) by (apply U_lit; lia) end.
  psrr_branch_tok RUN BR HS2 SHOK2 cm_span;
  [ | exfalso; rewrite branch_eq_U, HUk, HU0 in Hc; apply Z.eqb_neq in Hc; lia ].
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ => pose (E' := Ee) end.
  assert (EWlt : forall n, (n < 512)%nat -> ew E' n = ew E n) by (unfold E'; intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msF HS2 eq_refl) as Hmk0. cbn [ss_pc] in Hmk0.
  pose proof (st_ok_pi_region_nth _ _ _ 3%nat _ HS2 eq_refl) as Rfr.
  pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS2 eq_refl) as Rnch.
  pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS2 eq_refl) as Rcur.
  assert (EW34 : bv_unsigned (ew E' 34) = gF cx fp) by (rewrite (EWlt 34%nat ltac:(lia)); apply (cm_U E 34); [exact F34|lia]).
  assert (EW9 : bv_unsigned (ew E' 9) = c_sp1 cx) by (rewrite (EWlt 9%nat ltac:(lia)); apply (cm_U E 9); [exact F9|lia]).
  assert (EW32 : ew E' 32 = w64 (c_p cx + pos)) by (rewrite (EWlt 32%nat ltac:(lia)); exact F32).
  assert (EW33 : ew E' 33 = w64 (c_n cx - pos)) by (rewrite (EWlt 33%nat ltac:(lia)); exact F33).
  destruct (cm_mac6 E' W3 (ms_mem msF) (gF cx fp) _ _ _ _ _ _ Rfr EW34) as (M & HML & HMac).
  pose proof (cm_slot8 E' W3 (ms_mem msF) _ _ _ _ _ _ 88 (SLit 0) Rnch EW9 ltac:(cbn [In]; tauto) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia)) as Hnch0.
  change (bv_unsigned (sv_denot E' (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in Hnch0.
  set (nch := 0). assert (Hnchr : 0 <= nch < 256) by (unfold nch; lia). assert (Hnchrd : rdword (aview SEGS (w_H W3) (ms_mem msF)) (c_sp1 cx + 88) = Some nch) by exact Hnch0.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 136 32 4 (c_p cx + pos) Rcur EW9 ltac:(cbn [In]; tauto) EW32 Hcppos ltac:(lia)) as Hc88.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 144 33 (-4) (c_n cx - pos) Rcur EW9 ltac:(cbn [In]; tauto) EW33 ltac:(lia) ltac:(lia)) as Hc90.
  assert (HK2 : cm_keep cx fp W3 (ms_mem msA) (ms_mem msF)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK2) as HM2.
  assert (RG2 : getr (ms_regs msF) 2 = _) by (prreg HS2 (2%bv : bv 5) PX2; rewrite PX2; rewrite ?(EWlt 2%nat ltac:(lia)); rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (RG8 : getr (ms_regs msF) 8 = _) by (prreg HS2 (8%bv : bv 5) PX8; rewrite PX8; rewrite ?(EWlt 8%nat ltac:(lia)); rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (RG9 : getr (ms_regs msF) 9 = _) by (prreg HS2 (9%bv : bv 5) PX9; rewrite PX9; rewrite ?(EWlt 9%nat ltac:(lia)); rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (RG3 : getr (ms_regs msF) 3 = _) by (prreg HS2 (3%bv : bv 5) PX3; rewrite PX3; rewrite ?(EWlt 3%nat ltac:(lia)); rewrite (EE 3%nat 3%bv eq_refl); exact G3).
  assert (RG4 : getr (ms_regs msF) 4 = _) by (prreg HS2 (4%bv : bv 5) PX4; rewrite PX4; rewrite ?(EWlt 4%nat ltac:(lia)); rewrite (EE 4%nat 4%bv eq_refl); exact G4).
  assert (RG18 : getr (ms_regs msF) 18 = _) by (prreg HS2 (18%bv : bv 5) PX18; rewrite PX18; rewrite ?(EWlt 18%nat ltac:(lia)); rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (RG24 : getr (ms_regs msF) 24 = _) by (prreg HS2 (24%bv : bv 5) PX24; rewrite PX24; rewrite ?(EWlt 24%nat ltac:(lia)); rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (RG20 : getr (ms_regs msF) 20 = _) by (prreg HS2 (20%bv : bv 5) PX20; rewrite PX20; rewrite ?(EWlt 20%nat ltac:(lia)); rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (RG25 : getr (ms_regs msF) 25 = _) by (prreg HS2 (25%bv : bv 5) PX25; rewrite PX25; rewrite ?(EWlt 25%nat ltac:(lia)); rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  prreg HS2 (19%bv : bv 5) PX19. rewrite ?(EWlt 34%nat ltac:(lia)) in PX19; rewrite U34 in PX19.
  apply (cm_land msF _ M nch (pos + 4) HB HJ HFR HMO Hi Hk Hacc HBLK HINV).
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - unfold gregs. split; [exact RG2|]. split; [exact RG8|]. split; [exact RG9|].
    split; [exact RG3|]. split; [exact RG4|]. split; [exact RG18 | exact RG24].
  - exact RG20.
  - unfold GO_MAC; exact PX19.
  - exact RG25.
  - exact HM2.
  - exact HML.
  - unfold GO_MAC. exact HMac.
  - exact Hnchr.
  - unfold gslot. exact Hnchrd.
  - lia.
  - unfold gslot. replace (c_p cx + (pos + 4)) with (c_p cx + pos + 4) by lia. exact Hc88.
  - unfold gslot. replace (c_n cx - (pos + 4)) with (c_n cx - pos + (-4)) by lia. exact Hc90.
Qed.

Lemma cm_pathB_k5 : Z.land op 4 <> 0 -> Z.to_nat (Z.min (c_n cx - pos) 7) = 5%nat ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros Hop4 HKK.
  pose proof (cm_geo cx fp k ly3 S3 W3 ms3 md3 r HB HJ HFR HBLK)
    as ((Hs1 & Hs2 & Hs3 & Hs4 & Hs5) & (HF1 & HF2 & HF3 & HF4 & HF6) & (Hr16 & Hr4 & Hrc & Hria & Hrin) & HRF & Hinp).
  pose proof asan_consts as (Hac & _).
  destruct (cm_seat cx fp k ly3 S3 W3 ms3 md3 r pos HB HJ HFR HBLK HBODY HCUR) as [HS SHOK].
  pose proof cm_mem_start as HM.
  pose proof HBODY as (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & _).
  pose proof HCUR as (Hpos & _ & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
  pose proof (fun a => cm_mac_frames cx fp ly3 a EF) as HFA.
  remember (cm_E (ms_regs ms3) cx fp pos) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr (ms_regs ms3) rr)
    by (intros q rr Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (F9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F22 : ew E 22 = w64 op) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (F32 : ew E 32 = w64 (c_p cx + pos))
    by (subst E; unfold cm_E; change 32%nat with (32 + 0)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F33 : ew E 33 = w64 (c_n cx - pos))
    by (subst E; unfold cm_E; change 33%nat with (32 + 1)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F34 : ew E 34 = w64 (gF cx fp))
    by (subst E; unfold cm_E; change 34%nat with (32 + 2)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (FB : forall j, (j < 7)%nat -> ew E (35 + j) = w64 (cm_inbyte cx pos j)).
  { intros j Hj. subst E. unfold cm_E. replace (35 + j)%nat with (32 + (3 + j))%nat by lia.
    rewrite cm_ew_ex by lia. apply cm_ex_byte. exact Hj. }
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (apply (cm_U E 9); [exact F9 | lia]).
  assert (U34 : bv_unsigned (ew E 34) = gF cx fp) by (apply (cm_U E 34); [exact F34 | lia]).
  clear HE.
  
  assert (Gsp : alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
    spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256) by lia.
  assert (GF : 4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512) by (split; [lia|]; split; [lia | exact HF3]).
  assert (GR : 4096 <= r /\ r + 288 <= alloc_ceiling /\ (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r)) by lia.
  assert (GI : c_n cx = 0 \/
    (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx)))
    by (destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpc' & _ & Hpf & _)]; [left; exact Hn0 | right; lia]).
  paj_run_tok RUN HS HJ SHOK cm_span.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
      [reflexivity | exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ].
    apply awr_ok_nil. }
  assert (HK1 : cm_keep cx fp W3 (ms_mem ms3) (ms_mem ms)).
  { apply (cm_keep_frame cx fp W3 E _ _ _ HF).
    let rs' := eval vm_compute in (ss_mem cm_ss0) in change (ss_mem cm_ss0) with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]).
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM HK1) as HM1.
  clear HK1 HF HFr HG HM.
  psrr_branch_tok RUN BR HS SHOK cm_span.
  2: { exfalso. rewrite (cm_and4 E op F22 Hop) in Hc. apply Hop4. destruct (Z.eqb_spec (Z.land op 4) 0); [exact e | discriminate Hc]. }

  assert (Hcppos : 0 <= c_p cx + pos < 2 ^ 64).
  { destruct Hinp as [(Hn0 & Hp0) | (_ & _ & Hp4 & Hpc2 & _)]; [rewrite Hp0; unfold GB_EMPTY; lia | lia]. }
  assert (U32 : bv_unsigned (ew E 32) = c_p cx + pos) by (apply (cm_U E 32); [exact F32 | exact Hcppos]).
  clear Hc.
  set (kk := Z.to_nat (Z.min (c_n cx - pos) 7)).
  assert (Hrem : (Z.of_nat kk = c_n cx - pos /\ (kk < 7)%nat) \/ (kk = 7%nat /\ 7 <= c_n cx - pos)).
  { unfold kk. destruct (Z_lt_le_dec (c_n cx - pos) 7) as [Hlt|Hge];
    [left; split; [rewrite Z2Nat.id by lia; rewrite Z.min_l by lia; reflexivity | rewrite Z.min_l by lia; lia]
    | right; rewrite Z.min_r by lia; split; [reflexivity|lia]]. }
  assert (Hkk7 : (kk <= 7)%nat) by (unfold kk; lia).
  assert (Hkkn : pos + Z.of_nat kk <= c_n cx) by (unfold kk; lia).
  pose proof HJ as (HAR3 & _).
  assert (Hcn : c_n cx < 2 ^ 26) by (destruct Hinp as [(Hn0 & _) | (Hn & _)]; lia).
  pose proof HM1 as (HM1c & _).
  destruct HM1c as (_ & _ & _ & HINm & _).
  assert (Hf33 : afact_ok E 33 (cm_remf 7 kk))
    by (apply (cm_remf_ok E cx pos 7 kk F33); [lia | exact Hcn | lia | reflexivity]).
  assert (Haddk : kk = 0%nat \/ (YP09.region_wf (cm_inb kk) = true /\
     YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (cm_inb kk) /\ YP09.all_disjoint E (cm_inb kk) (ss_mem cm_ss0) /\
     shent_ok SEGS cm_Bx E (mrestrict (w_H W3) (ms_mem ms)) (mkSHE 32 0 (Z.of_nat kk)))).
  { destruct (Nat.eq_dec kk 0) as [->|Hk0]; [left; reflexivity|right].
    assert (Hcn0 : 0 < c_n cx) by (unfold kk in Hk0; lia).
    destruct Hinp as [(Hn0 & _) | (_ & Hin2 & Hp4 & Hpc2 & Hpia & HpF & HpR)]; [lia|].
    split; [apply cm_inb_wf|].
    split; [apply (cm_inb_ok cx pos W3 (ms_mem ms) E kk F32 FB HINm Hkk7); [lia | lia | lia | lia]|].
    split.
    { cbn [cm_ss0 ss_mem]. unfold cm_inb, cm_spill_lo, cm_spill_hi, cm_frame.
      cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
      rewrite U32, U9, U34. repeat split; lia. }
    { apply (cm_inb_sh cx pos ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) E kk HAR3 Hin2 Hcn0 Hpia Hpc2 F18 F32); [lia | lia]. } }
  pose proof (cm_addin E _ ms W3 7 kk HS SHOK Hf33 Haddk) as [HS2 SHOK2].
  assert (Hcur7 : 0 <= pos + Z.of_nat kk <= c_n cx) by lia.
  assert (Ekk : kk = 5%nat) by exact HKK.
  rewrite Ekk in HS2, SHOK2, Hrem, Hcur7.
  clear Hf33 Haddk HS SHOK Hkk7.
  lazymatch type of HS2 with context [kk] => fail 100 "cm_pathB: kk remains in HS2" | _ => idtac end.
  lazymatch type of SHOK2 with context [kk] => fail 100 "cm_pathB: kk remains in SHOK2" | _ => idtac end.
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS2 end.
  lazymatch type of SHOK2 with sh_ok _ _ ?sh _ _ => let v := eval vm_compute in sh in change sh with v in SHOK2 end.
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msA end.
  assert (HK1b : cm_keep cx fp W3 (ms_mem ms) (ms_mem msA)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK1b) as HM1b. clear HM1 HK1b HF HFr HG. rename HM1b into HM1.
  destruct Hrem as [(Hremv & _) | (Hbad & _)]; [| discriminate Hbad]. simpl in Hremv.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ =>
    assert (EW33v : bv_unsigned (ew Ee 33) = c_n cx - pos) by (rewrite ?ew_ewset_other by lia; rewrite F33; apply unsigned_lit_small; lia);
    assert (HUk : U Ee (SOff 33 (-5)) = 0) by (rewrite U_SOff, EW33v; replace (c_n cx - pos + (-5)) with 0 by lia; apply zcanon_id; unfold M64; lia);
    assert (HU0 : U Ee (SLit 0) = 0) by (apply U_lit; lia) end.
  psrr_branch_tok RUN BR HS2 SHOK2 cm_span;
  [ | exfalso; rewrite branch_eq_U, HUk, HU0 in Hc; apply Z.eqb_neq in Hc; lia ].
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ => pose (E' := Ee) end.
  assert (EWlt : forall n, (n < 512)%nat -> ew E' n = ew E n) by (unfold E'; intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msF HS2 eq_refl) as Hmk0. cbn [ss_pc] in Hmk0.
  pose proof (st_ok_pi_region_nth _ _ _ 3%nat _ HS2 eq_refl) as Rfr.
  pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS2 eq_refl) as Rnch.
  pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS2 eq_refl) as Rcur.
  assert (EW34 : bv_unsigned (ew E' 34) = gF cx fp) by (rewrite (EWlt 34%nat ltac:(lia)); apply (cm_U E 34); [exact F34|lia]).
  assert (EW9 : bv_unsigned (ew E' 9) = c_sp1 cx) by (rewrite (EWlt 9%nat ltac:(lia)); apply (cm_U E 9); [exact F9|lia]).
  assert (EW32 : ew E' 32 = w64 (c_p cx + pos)) by (rewrite (EWlt 32%nat ltac:(lia)); exact F32).
  assert (EW33 : ew E' 33 = w64 (c_n cx - pos)) by (rewrite (EWlt 33%nat ltac:(lia)); exact F33).
  destruct (cm_mac6 E' W3 (ms_mem msF) (gF cx fp) _ _ _ _ _ _ Rfr EW34) as (M & HML & HMac).
  pose proof (cm_slot8 E' W3 (ms_mem msF) _ _ _ _ _ _ 88 (SLit 0) Rnch EW9 ltac:(cbn [In]; tauto) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia)) as Hnch0.
  change (bv_unsigned (sv_denot E' (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in Hnch0.
  set (nch := 0). assert (Hnchr : 0 <= nch < 256) by (unfold nch; lia). assert (Hnchrd : rdword (aview SEGS (w_H W3) (ms_mem msF)) (c_sp1 cx + 88) = Some nch) by exact Hnch0.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 136 32 5 (c_p cx + pos) Rcur EW9 ltac:(cbn [In]; tauto) EW32 Hcppos ltac:(lia)) as Hc88.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 144 33 (-5) (c_n cx - pos) Rcur EW9 ltac:(cbn [In]; tauto) EW33 ltac:(lia) ltac:(lia)) as Hc90.
  assert (HK2 : cm_keep cx fp W3 (ms_mem msA) (ms_mem msF)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK2) as HM2.
  assert (RG2 : getr (ms_regs msF) 2 = _) by (prreg HS2 (2%bv : bv 5) PX2; rewrite PX2; rewrite ?(EWlt 2%nat ltac:(lia)); rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (RG8 : getr (ms_regs msF) 8 = _) by (prreg HS2 (8%bv : bv 5) PX8; rewrite PX8; rewrite ?(EWlt 8%nat ltac:(lia)); rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (RG9 : getr (ms_regs msF) 9 = _) by (prreg HS2 (9%bv : bv 5) PX9; rewrite PX9; rewrite ?(EWlt 9%nat ltac:(lia)); rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (RG3 : getr (ms_regs msF) 3 = _) by (prreg HS2 (3%bv : bv 5) PX3; rewrite PX3; rewrite ?(EWlt 3%nat ltac:(lia)); rewrite (EE 3%nat 3%bv eq_refl); exact G3).
  assert (RG4 : getr (ms_regs msF) 4 = _) by (prreg HS2 (4%bv : bv 5) PX4; rewrite PX4; rewrite ?(EWlt 4%nat ltac:(lia)); rewrite (EE 4%nat 4%bv eq_refl); exact G4).
  assert (RG18 : getr (ms_regs msF) 18 = _) by (prreg HS2 (18%bv : bv 5) PX18; rewrite PX18; rewrite ?(EWlt 18%nat ltac:(lia)); rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (RG24 : getr (ms_regs msF) 24 = _) by (prreg HS2 (24%bv : bv 5) PX24; rewrite PX24; rewrite ?(EWlt 24%nat ltac:(lia)); rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (RG20 : getr (ms_regs msF) 20 = _) by (prreg HS2 (20%bv : bv 5) PX20; rewrite PX20; rewrite ?(EWlt 20%nat ltac:(lia)); rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (RG25 : getr (ms_regs msF) 25 = _) by (prreg HS2 (25%bv : bv 5) PX25; rewrite PX25; rewrite ?(EWlt 25%nat ltac:(lia)); rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  prreg HS2 (19%bv : bv 5) PX19. rewrite ?(EWlt 34%nat ltac:(lia)) in PX19; rewrite U34 in PX19.
  apply (cm_land msF _ M nch (pos + 5) HB HJ HFR HMO Hi Hk Hacc HBLK HINV).
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - unfold gregs. split; [exact RG2|]. split; [exact RG8|]. split; [exact RG9|].
    split; [exact RG3|]. split; [exact RG4|]. split; [exact RG18 | exact RG24].
  - exact RG20.
  - unfold GO_MAC; exact PX19.
  - exact RG25.
  - exact HM2.
  - exact HML.
  - unfold GO_MAC. exact HMac.
  - exact Hnchr.
  - unfold gslot. exact Hnchrd.
  - lia.
  - unfold gslot. replace (c_p cx + (pos + 5)) with (c_p cx + pos + 5) by lia. exact Hc88.
  - unfold gslot. replace (c_n cx - (pos + 5)) with (c_n cx - pos + (-5)) by lia. exact Hc90.
Qed.

Lemma cm_pathB_k6 : Z.land op 4 <> 0 -> Z.to_nat (Z.min (c_n cx - pos) 7) = 6%nat ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros Hop4 HKK.
  pose proof (cm_geo cx fp k ly3 S3 W3 ms3 md3 r HB HJ HFR HBLK)
    as ((Hs1 & Hs2 & Hs3 & Hs4 & Hs5) & (HF1 & HF2 & HF3 & HF4 & HF6) & (Hr16 & Hr4 & Hrc & Hria & Hrin) & HRF & Hinp).
  pose proof asan_consts as (Hac & _).
  destruct (cm_seat cx fp k ly3 S3 W3 ms3 md3 r pos HB HJ HFR HBLK HBODY HCUR) as [HS SHOK].
  pose proof cm_mem_start as HM.
  pose proof HBODY as (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & _).
  pose proof HCUR as (Hpos & _ & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
  pose proof (fun a => cm_mac_frames cx fp ly3 a EF) as HFA.
  remember (cm_E (ms_regs ms3) cx fp pos) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr (ms_regs ms3) rr)
    by (intros q rr Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (F9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F22 : ew E 22 = w64 op) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (F32 : ew E 32 = w64 (c_p cx + pos))
    by (subst E; unfold cm_E; change 32%nat with (32 + 0)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F33 : ew E 33 = w64 (c_n cx - pos))
    by (subst E; unfold cm_E; change 33%nat with (32 + 1)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F34 : ew E 34 = w64 (gF cx fp))
    by (subst E; unfold cm_E; change 34%nat with (32 + 2)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (FB : forall j, (j < 7)%nat -> ew E (35 + j) = w64 (cm_inbyte cx pos j)).
  { intros j Hj. subst E. unfold cm_E. replace (35 + j)%nat with (32 + (3 + j))%nat by lia.
    rewrite cm_ew_ex by lia. apply cm_ex_byte. exact Hj. }
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (apply (cm_U E 9); [exact F9 | lia]).
  assert (U34 : bv_unsigned (ew E 34) = gF cx fp) by (apply (cm_U E 34); [exact F34 | lia]).
  clear HE.
  
  assert (Gsp : alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
    spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256) by lia.
  assert (GF : 4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512) by (split; [lia|]; split; [lia | exact HF3]).
  assert (GR : 4096 <= r /\ r + 288 <= alloc_ceiling /\ (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r)) by lia.
  assert (GI : c_n cx = 0 \/
    (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx)))
    by (destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpc' & _ & Hpf & _)]; [left; exact Hn0 | right; lia]).
  paj_run_tok RUN HS HJ SHOK cm_span.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
      [reflexivity | exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ].
    apply awr_ok_nil. }
  assert (HK1 : cm_keep cx fp W3 (ms_mem ms3) (ms_mem ms)).
  { apply (cm_keep_frame cx fp W3 E _ _ _ HF).
    let rs' := eval vm_compute in (ss_mem cm_ss0) in change (ss_mem cm_ss0) with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]).
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM HK1) as HM1.
  clear HK1 HF HFr HG HM.
  psrr_branch_tok RUN BR HS SHOK cm_span.
  2: { exfalso. rewrite (cm_and4 E op F22 Hop) in Hc. apply Hop4. destruct (Z.eqb_spec (Z.land op 4) 0); [exact e | discriminate Hc]. }

  assert (Hcppos : 0 <= c_p cx + pos < 2 ^ 64).
  { destruct Hinp as [(Hn0 & Hp0) | (_ & _ & Hp4 & Hpc2 & _)]; [rewrite Hp0; unfold GB_EMPTY; lia | lia]. }
  assert (U32 : bv_unsigned (ew E 32) = c_p cx + pos) by (apply (cm_U E 32); [exact F32 | exact Hcppos]).
  clear Hc.
  set (kk := Z.to_nat (Z.min (c_n cx - pos) 7)).
  assert (Hrem : (Z.of_nat kk = c_n cx - pos /\ (kk < 7)%nat) \/ (kk = 7%nat /\ 7 <= c_n cx - pos)).
  { unfold kk. destruct (Z_lt_le_dec (c_n cx - pos) 7) as [Hlt|Hge];
    [left; split; [rewrite Z2Nat.id by lia; rewrite Z.min_l by lia; reflexivity | rewrite Z.min_l by lia; lia]
    | right; rewrite Z.min_r by lia; split; [reflexivity|lia]]. }
  assert (Hkk7 : (kk <= 7)%nat) by (unfold kk; lia).
  assert (Hkkn : pos + Z.of_nat kk <= c_n cx) by (unfold kk; lia).
  pose proof HJ as (HAR3 & _).
  assert (Hcn : c_n cx < 2 ^ 26) by (destruct Hinp as [(Hn0 & _) | (Hn & _)]; lia).
  pose proof HM1 as (HM1c & _).
  destruct HM1c as (_ & _ & _ & HINm & _).
  assert (Hf33 : afact_ok E 33 (cm_remf 7 kk))
    by (apply (cm_remf_ok E cx pos 7 kk F33); [lia | exact Hcn | lia | reflexivity]).
  assert (Haddk : kk = 0%nat \/ (YP09.region_wf (cm_inb kk) = true /\
     YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (cm_inb kk) /\ YP09.all_disjoint E (cm_inb kk) (ss_mem cm_ss0) /\
     shent_ok SEGS cm_Bx E (mrestrict (w_H W3) (ms_mem ms)) (mkSHE 32 0 (Z.of_nat kk)))).
  { destruct (Nat.eq_dec kk 0) as [->|Hk0]; [left; reflexivity|right].
    assert (Hcn0 : 0 < c_n cx) by (unfold kk in Hk0; lia).
    destruct Hinp as [(Hn0 & _) | (_ & Hin2 & Hp4 & Hpc2 & Hpia & HpF & HpR)]; [lia|].
    split; [apply cm_inb_wf|].
    split; [apply (cm_inb_ok cx pos W3 (ms_mem ms) E kk F32 FB HINm Hkk7); [lia | lia | lia | lia]|].
    split.
    { cbn [cm_ss0 ss_mem]. unfold cm_inb, cm_spill_lo, cm_spill_hi, cm_frame.
      cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
      rewrite U32, U9, U34. repeat split; lia. }
    { apply (cm_inb_sh cx pos ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) E kk HAR3 Hin2 Hcn0 Hpia Hpc2 F18 F32); [lia | lia]. } }
  pose proof (cm_addin E _ ms W3 7 kk HS SHOK Hf33 Haddk) as [HS2 SHOK2].
  assert (Hcur7 : 0 <= pos + Z.of_nat kk <= c_n cx) by lia.
  assert (Ekk : kk = 6%nat) by exact HKK.
  rewrite Ekk in HS2, SHOK2, Hrem, Hcur7.
  clear Hf33 Haddk HS SHOK Hkk7.
  lazymatch type of HS2 with context [kk] => fail 100 "cm_pathB: kk remains in HS2" | _ => idtac end.
  lazymatch type of SHOK2 with context [kk] => fail 100 "cm_pathB: kk remains in SHOK2" | _ => idtac end.
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS2 end.
  lazymatch type of SHOK2 with sh_ok _ _ ?sh _ _ => let v := eval vm_compute in sh in change sh with v in SHOK2 end.
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msA end.
  assert (HK1b : cm_keep cx fp W3 (ms_mem ms) (ms_mem msA)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK1b) as HM1b. clear HM1 HK1b HF HFr HG. rename HM1b into HM1.
  destruct Hrem as [(Hremv & _) | (Hbad & _)]; [| discriminate Hbad]. simpl in Hremv.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ =>
    assert (EW33v : bv_unsigned (ew Ee 33) = c_n cx - pos) by (rewrite ?ew_ewset_other by lia; rewrite F33; apply unsigned_lit_small; lia);
    assert (HUk : U Ee (SOff 33 (-6)) = 0) by (rewrite U_SOff, EW33v; replace (c_n cx - pos + (-6)) with 0 by lia; apply zcanon_id; unfold M64; lia);
    assert (HU0 : U Ee (SLit 0) = 0) by (apply U_lit; lia) end.
  psrr_branch_tok RUN BR HS2 SHOK2 cm_span;
  [ exfalso; rewrite branch_ne_U, HUk, HU0, Z.eqb_refl in Hc; discriminate Hc | ].
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ => pose (E' := Ee) end.
  assert (EWlt : forall n, (n < 512)%nat -> ew E' n = ew E n) by (unfold E'; intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msF HS2 eq_refl) as Hmk0. cbn [ss_pc] in Hmk0.
  pose proof (st_ok_pi_region_nth _ _ _ 3%nat _ HS2 eq_refl) as Rfr.
  pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS2 eq_refl) as Rnch.
  pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS2 eq_refl) as Rcur.
  assert (EW34 : bv_unsigned (ew E' 34) = gF cx fp) by (rewrite (EWlt 34%nat ltac:(lia)); apply (cm_U E 34); [exact F34|lia]).
  assert (EW9 : bv_unsigned (ew E' 9) = c_sp1 cx) by (rewrite (EWlt 9%nat ltac:(lia)); apply (cm_U E 9); [exact F9|lia]).
  assert (EW32 : ew E' 32 = w64 (c_p cx + pos)) by (rewrite (EWlt 32%nat ltac:(lia)); exact F32).
  assert (EW33 : ew E' 33 = w64 (c_n cx - pos)) by (rewrite (EWlt 33%nat ltac:(lia)); exact F33).
  destruct (cm_mac6 E' W3 (ms_mem msF) (gF cx fp) _ _ _ _ _ _ Rfr EW34) as (M & HML & HMac).
  pose proof (cm_slot8 E' W3 (ms_mem msF) _ _ _ _ _ _ 88 (SLit 0) Rnch EW9 ltac:(cbn [In]; tauto) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia)) as Hnch0.
  change (bv_unsigned (sv_denot E' (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in Hnch0.
  set (nch := 0). assert (Hnchr : 0 <= nch < 256) by (unfold nch; lia). assert (Hnchrd : rdword (aview SEGS (w_H W3) (ms_mem msF)) (c_sp1 cx + 88) = Some nch) by exact Hnch0.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 136 32 6 (c_p cx + pos) Rcur EW9 ltac:(cbn [In]; tauto) EW32 Hcppos ltac:(lia)) as Hc88.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 144 33 (-6) (c_n cx - pos) Rcur EW9 ltac:(cbn [In]; tauto) EW33 ltac:(lia) ltac:(lia)) as Hc90.
  assert (HK2 : cm_keep cx fp W3 (ms_mem msA) (ms_mem msF)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK2) as HM2.
  assert (RG2 : getr (ms_regs msF) 2 = _) by (prreg HS2 (2%bv : bv 5) PX2; rewrite PX2; rewrite ?(EWlt 2%nat ltac:(lia)); rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (RG8 : getr (ms_regs msF) 8 = _) by (prreg HS2 (8%bv : bv 5) PX8; rewrite PX8; rewrite ?(EWlt 8%nat ltac:(lia)); rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (RG9 : getr (ms_regs msF) 9 = _) by (prreg HS2 (9%bv : bv 5) PX9; rewrite PX9; rewrite ?(EWlt 9%nat ltac:(lia)); rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (RG3 : getr (ms_regs msF) 3 = _) by (prreg HS2 (3%bv : bv 5) PX3; rewrite PX3; rewrite ?(EWlt 3%nat ltac:(lia)); rewrite (EE 3%nat 3%bv eq_refl); exact G3).
  assert (RG4 : getr (ms_regs msF) 4 = _) by (prreg HS2 (4%bv : bv 5) PX4; rewrite PX4; rewrite ?(EWlt 4%nat ltac:(lia)); rewrite (EE 4%nat 4%bv eq_refl); exact G4).
  assert (RG18 : getr (ms_regs msF) 18 = _) by (prreg HS2 (18%bv : bv 5) PX18; rewrite PX18; rewrite ?(EWlt 18%nat ltac:(lia)); rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (RG24 : getr (ms_regs msF) 24 = _) by (prreg HS2 (24%bv : bv 5) PX24; rewrite PX24; rewrite ?(EWlt 24%nat ltac:(lia)); rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (RG20 : getr (ms_regs msF) 20 = _) by (prreg HS2 (20%bv : bv 5) PX20; rewrite PX20; rewrite ?(EWlt 20%nat ltac:(lia)); rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (RG25 : getr (ms_regs msF) 25 = _) by (prreg HS2 (25%bv : bv 5) PX25; rewrite PX25; rewrite ?(EWlt 25%nat ltac:(lia)); rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  prreg HS2 (19%bv : bv 5) PX19. rewrite ?(EWlt 34%nat ltac:(lia)) in PX19; rewrite U34 in PX19.
  apply (cm_land msF _ M nch (pos + 6) HB HJ HFR HMO Hi Hk Hacc HBLK HINV).
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - unfold gregs. split; [exact RG2|]. split; [exact RG8|]. split; [exact RG9|].
    split; [exact RG3|]. split; [exact RG4|]. split; [exact RG18 | exact RG24].
  - exact RG20.
  - unfold GO_MAC; exact PX19.
  - exact RG25.
  - exact HM2.
  - exact HML.
  - unfold GO_MAC. exact HMac.
  - exact Hnchr.
  - unfold gslot. exact Hnchrd.
  - lia.
  - unfold gslot. replace (c_p cx + (pos + 6)) with (c_p cx + pos + 6) by lia. exact Hc88.
  - unfold gslot. replace (c_n cx - (pos + 6)) with (c_n cx - pos + (-6)) by lia. exact Hc90.
Qed.

Lemma cm_pathB_k7 : Z.land op 4 <> 0 -> Z.to_nat (Z.min (c_n cx - pos) 7) = 7%nat ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros Hop4 HKK.
  pose proof (cm_geo cx fp k ly3 S3 W3 ms3 md3 r HB HJ HFR HBLK)
    as ((Hs1 & Hs2 & Hs3 & Hs4 & Hs5) & (HF1 & HF2 & HF3 & HF4 & HF6) & (Hr16 & Hr4 & Hrc & Hria & Hrin) & HRF & Hinp).
  pose proof asan_consts as (Hac & _).
  destruct (cm_seat cx fp k ly3 S3 W3 ms3 md3 r pos HB HJ HFR HBLK HBODY HCUR) as [HS SHOK].
  pose proof cm_mem_start as HM.
  pose proof HBODY as (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & _).
  pose proof HCUR as (Hpos & _ & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
  pose proof (fun a => cm_mac_frames cx fp ly3 a EF) as HFA.
  remember (cm_E (ms_regs ms3) cx fp pos) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr (ms_regs ms3) rr)
    by (intros q rr Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (F9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F22 : ew E 22 = w64 op) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (F32 : ew E 32 = w64 (c_p cx + pos))
    by (subst E; unfold cm_E; change 32%nat with (32 + 0)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F33 : ew E 33 = w64 (c_n cx - pos))
    by (subst E; unfold cm_E; change 33%nat with (32 + 1)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F34 : ew E 34 = w64 (gF cx fp))
    by (subst E; unfold cm_E; change 34%nat with (32 + 2)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (FB : forall j, (j < 7)%nat -> ew E (35 + j) = w64 (cm_inbyte cx pos j)).
  { intros j Hj. subst E. unfold cm_E. replace (35 + j)%nat with (32 + (3 + j))%nat by lia.
    rewrite cm_ew_ex by lia. apply cm_ex_byte. exact Hj. }
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (apply (cm_U E 9); [exact F9 | lia]).
  assert (U34 : bv_unsigned (ew E 34) = gF cx fp) by (apply (cm_U E 34); [exact F34 | lia]).
  clear HE.
  
  assert (Gsp : alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
    spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256) by lia.
  assert (GF : 4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512) by (split; [lia|]; split; [lia | exact HF3]).
  assert (GR : 4096 <= r /\ r + 288 <= alloc_ceiling /\ (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r)) by lia.
  assert (GI : c_n cx = 0 \/
    (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx)))
    by (destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpc' & _ & Hpf & _)]; [left; exact Hn0 | right; lia]).
  paj_run_tok RUN HS HJ SHOK cm_span.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
      [reflexivity | exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ].
    apply awr_ok_nil. }
  assert (HK1 : cm_keep cx fp W3 (ms_mem ms3) (ms_mem ms)).
  { apply (cm_keep_frame cx fp W3 E _ _ _ HF).
    let rs' := eval vm_compute in (ss_mem cm_ss0) in change (ss_mem cm_ss0) with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]).
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM HK1) as HM1.
  clear HK1 HF HFr HG HM.
  psrr_branch_tok RUN BR HS SHOK cm_span.
  2: { exfalso. rewrite (cm_and4 E op F22 Hop) in Hc. apply Hop4. destruct (Z.eqb_spec (Z.land op 4) 0); [exact e | discriminate Hc]. }

  assert (Hcppos : 0 <= c_p cx + pos < 2 ^ 64).
  { destruct Hinp as [(Hn0 & Hp0) | (_ & _ & Hp4 & Hpc2 & _)]; [rewrite Hp0; unfold GB_EMPTY; lia | lia]. }
  assert (U32 : bv_unsigned (ew E 32) = c_p cx + pos) by (apply (cm_U E 32); [exact F32 | exact Hcppos]).
  clear Hc.
  set (kk := Z.to_nat (Z.min (c_n cx - pos) 7)).
  assert (Hrem : (Z.of_nat kk = c_n cx - pos /\ (kk < 7)%nat) \/ (kk = 7%nat /\ 7 <= c_n cx - pos)).
  { unfold kk. destruct (Z_lt_le_dec (c_n cx - pos) 7) as [Hlt|Hge];
    [left; split; [rewrite Z2Nat.id by lia; rewrite Z.min_l by lia; reflexivity | rewrite Z.min_l by lia; lia]
    | right; rewrite Z.min_r by lia; split; [reflexivity|lia]]. }
  assert (Hkk7 : (kk <= 7)%nat) by (unfold kk; lia).
  assert (Hkkn : pos + Z.of_nat kk <= c_n cx) by (unfold kk; lia).
  pose proof HJ as (HAR3 & _).
  assert (Hcn : c_n cx < 2 ^ 26) by (destruct Hinp as [(Hn0 & _) | (Hn & _)]; lia).
  pose proof HM1 as (HM1c & _).
  destruct HM1c as (_ & _ & _ & HINm & _).
  assert (Hf33 : afact_ok E 33 (cm_remf 7 kk))
    by (apply (cm_remf_ok E cx pos 7 kk F33); [lia | exact Hcn | lia | reflexivity]).
  assert (Haddk : kk = 0%nat \/ (YP09.region_wf (cm_inb kk) = true /\
     YP09.region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (cm_inb kk) /\ YP09.all_disjoint E (cm_inb kk) (ss_mem cm_ss0) /\
     shent_ok SEGS cm_Bx E (mrestrict (w_H W3) (ms_mem ms)) (mkSHE 32 0 (Z.of_nat kk)))).
  { destruct (Nat.eq_dec kk 0) as [->|Hk0]; [left; reflexivity|right].
    assert (Hcn0 : 0 < c_n cx) by (unfold kk in Hk0; lia).
    destruct Hinp as [(Hn0 & _) | (_ & Hin2 & Hp4 & Hpc2 & Hpia & HpF & HpR)]; [lia|].
    split; [apply cm_inb_wf|].
    split; [apply (cm_inb_ok cx pos W3 (ms_mem ms) E kk F32 FB HINm Hkk7); [lia | lia | lia | lia]|].
    split.
    { cbn [cm_ss0 ss_mem]. unfold cm_inb, cm_spill_lo, cm_spill_hi, cm_frame.
      cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
      rewrite U32, U9, U34. repeat split; lia. }
    { apply (cm_inb_sh cx pos ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) E kk HAR3 Hin2 Hcn0 Hpia Hpc2 F18 F32); [lia | lia]. } }
  pose proof (cm_addin E _ ms W3 7 kk HS SHOK Hf33 Haddk) as [HS2 SHOK2].
  assert (Hcur7 : 0 <= pos + Z.of_nat kk <= c_n cx) by lia.
  assert (Ekk : kk = 7%nat) by exact HKK.
  rewrite Ekk in HS2, SHOK2, Hrem, Hcur7.
  clear Hf33 Haddk HS SHOK Hkk7.
  lazymatch type of HS2 with context [kk] => fail 100 "cm_pathB: kk remains in HS2" | _ => idtac end.
  lazymatch type of SHOK2 with context [kk] => fail 100 "cm_pathB: kk remains in SHOK2" | _ => idtac end.
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS2 end.
  lazymatch type of SHOK2 with sh_ok _ _ ?sh _ _ => let v := eval vm_compute in sh in change sh with v in SHOK2 end.
  paj_run_to_tok RUNTO HS2 HJ SHOK2 cm_span PC1_nch.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ee _ _ => pose (E' := Ee) end.
  assert (EWlt : forall n, (n < 512)%nat -> ew E' n = ew E n) by (unfold E'; intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msF HS2 eq_refl) as Hmk0. cbn [ss_pc] in Hmk0.
  pose proof (st_ok_pi_region_nth _ _ _ 3%nat _ HS2 eq_refl) as Rfr.
  pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS2 eq_refl) as Rnch.
  pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS2 eq_refl) as Rcur.
  assert (EW34 : bv_unsigned (ew E' 34) = gF cx fp) by (rewrite (EWlt 34%nat ltac:(lia)); apply (cm_U E 34); [exact F34|lia]).
  assert (EW9 : bv_unsigned (ew E' 9) = c_sp1 cx) by (rewrite (EWlt 9%nat ltac:(lia)); apply (cm_U E 9); [exact F9|lia]).
  assert (EW32 : ew E' 32 = w64 (c_p cx + pos)) by (rewrite (EWlt 32%nat ltac:(lia)); exact F32).
  assert (EW33 : ew E' 33 = w64 (c_n cx - pos)) by (rewrite (EWlt 33%nat ltac:(lia)); exact F33).
  destruct (cm_mac6 E' W3 (ms_mem msF) (gF cx fp) _ _ _ _ _ _ Rfr EW34) as (M & HML & HMac).
  destruct (cm_slot_byte E' W3 (ms_mem msF) _ _ _ _ _ _ 88 (SOff 41 0) Rnch EW9 ltac:(cbn [In]; tauto)) as (nch & Hnchr & Hnchrd).
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 136 32 7 (c_p cx + pos) Rcur EW9 ltac:(cbn [In]; tauto) EW32 Hcppos ltac:(lia)) as Hc88.
  pose proof (cm_slot_off E' W3 (ms_mem msF) _ _ _ _ _ _ 144 33 (-7) (c_n cx - pos) Rcur EW9 ltac:(cbn [In]; tauto) EW33 ltac:(lia) ltac:(lia)) as Hc90.
  assert (HK2 : cm_keep cx fp W3 (ms_mem ms) (ms_mem msF)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK2) as HM2.
  assert (RG2 : getr (ms_regs msF) 2 = _) by (prreg HS2 (2%bv : bv 5) PX2; rewrite PX2; rewrite ?(EWlt 2%nat ltac:(lia)); rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (RG8 : getr (ms_regs msF) 8 = _) by (prreg HS2 (8%bv : bv 5) PX8; rewrite PX8; rewrite ?(EWlt 8%nat ltac:(lia)); rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (RG9 : getr (ms_regs msF) 9 = _) by (prreg HS2 (9%bv : bv 5) PX9; rewrite PX9; rewrite ?(EWlt 9%nat ltac:(lia)); rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (RG3 : getr (ms_regs msF) 3 = _) by (prreg HS2 (3%bv : bv 5) PX3; rewrite PX3; rewrite ?(EWlt 3%nat ltac:(lia)); rewrite (EE 3%nat 3%bv eq_refl); exact G3).
  assert (RG4 : getr (ms_regs msF) 4 = _) by (prreg HS2 (4%bv : bv 5) PX4; rewrite PX4; rewrite ?(EWlt 4%nat ltac:(lia)); rewrite (EE 4%nat 4%bv eq_refl); exact G4).
  assert (RG18 : getr (ms_regs msF) 18 = _) by (prreg HS2 (18%bv : bv 5) PX18; rewrite PX18; rewrite ?(EWlt 18%nat ltac:(lia)); rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (RG24 : getr (ms_regs msF) 24 = _) by (prreg HS2 (24%bv : bv 5) PX24; rewrite PX24; rewrite ?(EWlt 24%nat ltac:(lia)); rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (RG20 : getr (ms_regs msF) 20 = _) by (prreg HS2 (20%bv : bv 5) PX20; rewrite PX20; rewrite ?(EWlt 20%nat ltac:(lia)); rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (RG25 : getr (ms_regs msF) 25 = _) by (prreg HS2 (25%bv : bv 5) PX25; rewrite PX25; rewrite ?(EWlt 25%nat ltac:(lia)); rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  prreg HS2 (19%bv : bv 5) PX19. rewrite ?(EWlt 34%nat ltac:(lia)) in PX19; rewrite U34 in PX19.
  apply (cm_land msF _ M nch (pos + 7) HB HJ HFR HMO Hi Hk Hacc HBLK HINV).
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - unfold gregs. split; [exact RG2|]. split; [exact RG8|]. split; [exact RG9|].
    split; [exact RG3|]. split; [exact RG4|]. split; [exact RG18 | exact RG24].
  - exact RG20.
  - unfold GO_MAC; exact PX19.
  - exact RG25.
  - exact HM2.
  - exact HML.
  - unfold GO_MAC. exact HMac.
  - exact Hnchr.
  - unfold gslot. exact Hnchrd.
  - lia.
  - unfold gslot. replace (c_p cx + (pos + 7)) with (c_p cx + pos + 7) by lia. exact Hc88.
  - unfold gslot. replace (c_n cx - (pos + 7)) with (c_n cx - pos + (-7)) by lia. exact Hc90.
Qed.

Lemma cm_pathB : Z.land op 4 <> 0 -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros Hop4.
  assert (Hk7 : (Z.to_nat (Z.min (c_n cx - pos) 7) <= 7)%nat) by lia.
  destruct (Z.to_nat (Z.min (c_n cx - pos) 7)) as [|[|[|[|[|[|[|[|n]]]]]]]] eqn:HKK.
  - exact (cm_pathB_k0 Hop4 HKK).
  - exact (cm_pathB_k1 Hop4 HKK).
  - exact (cm_pathB_k2 Hop4 HKK).
  - exact (cm_pathB_k3 Hop4 HKK).
  - exact (cm_pathB_k4 Hop4 HKK).
  - exact (cm_pathB_k5 Hop4 HKK).
  - exact (cm_pathB_k6 Hop4 HKK).
  - exact (cm_pathB_k7 Hop4 HKK).
  - lia.
Qed.

(* Path A (op & 4 = 0): __asan_memcpy (mac, read_mac.base, 5) at 0x803c4, then mac[5] and the nch byte.
   OPEN: not written. Plan: run from the seat to the jal (state already probed: a0 = s3 = SOff 34 32, a1 = SOff 245 0
   = A_OBJ 4, a2 = SLit 5, ra = SOff 240 0x47c), apply aj_intrin_atS with AMEMCPY (source bytes from gb_base's
   arodata_okP carried by the journal's image field with FP = [], and HRMB; shadow by ro_read_ok_glob with HGLOB,
   HISV and the margins of HMRG (cm_rmb_marg)), rebuild with jafter_call_keep_hi keeping the two spill regions,
   re-add cm_frame with the five literal chunks 00 40 ab 00 00, then the cap-2 split of cm_addin, run to PC1_nch
   (one psrr branch for kk = 0) and land with cm_land. *)
Lemma cm_pathA : Z.land op 4 = 0 -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros Hop4.
  pose proof (cm_geo cx fp k ly3 S3 W3 ms3 md3 r HB HJ HFR HBLK)
    as ((Hs1 & Hs2 & Hs3 & Hs4 & Hs5) & (HF1 & HF2 & HF3 & HF4 & HF6) & (Hr16 & Hr4 & Hrc & Hria & Hrin) & HRF & Hinp).
    pose proof asan_consts as (Hac & _).
  destruct (cm_seat cx fp k ly3 S3 W3 ms3 md3 r pos HB HJ HFR HBLK HBODY HCUR) as [HS SHOK].
  pose proof cm_mem_start as HM.
  pose proof HBODY as (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4 & G18 & G24) & _).
  pose proof HCUR as (Hpos & _ & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EF.
  pose proof (fun a => cm_mac_frames cx fp ly3 a EF) as HFA.
  remember (cm_E (ms_regs ms3) cx fp pos) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr (ms_regs ms3) rr)
    by (intros q rr Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (F9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F22 : ew E 22 = w64 op) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (F32 : ew E 32 = w64 (c_p cx + pos))
    by (subst E; unfold cm_E; change 32%nat with (32 + 0)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F33 : ew E 33 = w64 (c_n cx - pos))
    by (subst E; unfold cm_E; change 33%nat with (32 + 1)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (F34 : ew E 34 = w64 (gF cx fp))
    by (subst E; unfold cm_E; change 34%nat with (32 + 2)%nat; rewrite cm_ew_ex by lia; reflexivity).
  assert (FB : forall j, (j < 7)%nat -> ew E (35 + j) = w64 (cm_inbyte cx pos j)).
  { intros j Hj. subst E. unfold cm_E. replace (35 + j)%nat with (32 + (3 + j))%nat by lia.
    rewrite cm_ew_ex by lia. apply cm_ex_byte. exact Hj. }
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (apply (cm_U E 9); [exact F9 | lia]).
  assert (U34 : bv_unsigned (ew E 34) = gF cx fp) by (apply (cm_U E 34); [exact F34 | lia]).
  clear HE.
  
  assert (Gsp : alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
    spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256) by lia.
  assert (GF : 4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512) by (split; [lia|]; split; [lia | exact HF3]).
  assert (GR : 4096 <= r /\ r + 288 <= alloc_ceiling /\ (r + 288 <= gF cx fp \/ gF cx fp + 512 <= r)) by lia.
  assert (GI : c_n cx = 0 \/
    (4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 512 <= c_p cx)))
    by (destruct Hinp as [(Hn0 & _) | (_ & _ & Hp4 & Hpc' & _ & Hpf & _)]; [left; exact Hn0 | right; lia]).
  paj_run_tok RUN HS HJ SHOK cm_span.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ].
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
      [reflexivity | exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ].
    apply awr_ok_nil. }
  assert (HK1 : cm_keep cx fp W3 (ms_mem ms3) (ms_mem ms)).
  { apply (cm_keep_frame cx fp W3 E _ _ _ HF).
    let rs' := eval vm_compute in (ss_mem cm_ss0) in change (ss_mem cm_ss0) with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]).
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM HK1) as HM1.
  clear HK1 HF HFr HG HM.
  psrr_branch_tok RUN BR HS SHOK cm_span.
  1: { exfalso. rewrite (cm_and4 E op F22 Hop) in Hc. rewrite Hop4 in Hc. cbn in Hc. discriminate. }
  clear Hc.
  
  paj_run_tok RUN HS HJ SHOK cm_span.
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | exact U34 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }
  
  pose proof HJ as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & FROM & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  assert (HM4 : IMG_LO + 64 <= VAL (A_OBJ 4) /\ VAL (A_OBJ 4) + 5 + 64 <= IMG_HI)
    by (rewrite Forall_forall in HMRG; exact (HMRG (VAL (A_OBJ 4), 5) ltac:(unfold BX_G; cbn [In]; tauto))).
  unfold IMG_HI in HM4.
  pose proof (pa_val_range (A_OBJ 4)) as Hv4.
  pose proof (pa_obj_img 4 ltac:(lia)) as Ho4.
  assert (HSRC : forall j, 0 <= j < 5 ->
    aview SEGS (w_H W3) (ms_mem ms0) (VAL (A_OBJ 4) + j) = Some (nth (Z.to_nat j) [0; 64; 171; 0; 0] 0)).
  { intros j Hj. destruct (HRMB j ltac:(cbn; lia)) as (Hrom & Hown & Herr & Hb).
    rewrite (FROM (VAL (A_OBJ 4) + j)); [| destruct Hrom as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]
      | exact Hown | exact Herr | apply fp_spares_closed; exact sink_closed_nil].
    rewrite (HRO (VAL (A_OBJ 4) + j)); [| left; exact Hrom | exact Hown | exact Herr]. exact Hb. }
  assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
  pose proof HM1 as (HM1c & _).
  pose proof HM1c as (_ & HSHm & _).
  pmkst HS.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
  prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
  
  assert (HK2 : cm_keep cx fp W3 (ms_mem ms) (ms_mem ms0)).
  { apply (cm_keep_frame cx fp W3 E _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?U9, ?U34 in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM1 HK2) as HM2.
  clear HM1 HK2 HF HFr HG HM1c HSHm.
  pose proof HM2 as (HM2c & _). pose proof HM2c as (_ & HSHm & _).
  pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _).
  assert (E245 : ew E 245 = Z_to_bv 64 (VAL (A_OBJ 4)))
    by (exact (img_env_atomP E (A_OBJ 4) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
  eapply SRr_bind.
  { eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA BS___asan_memcpy) AMEMCPY W3 (ms_regs ms0) (ms_mem ms0)
      GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k
      (gF cx fp + 32) (VAL (A_OBJ 4)) 5 (c_sp1 cx - spZ (c_regs cx)) _ HJ).
    - rewrite Ra0, U34. reflexivity.
    - rewrite Ra1, E245. reflexivity.
    - rewrite Ra2. reflexivity.
    - lia.
    - lia.
    - lia.
    - unfold spZ at 1. rewrite Rsp, (EE 2%nat 2%bv eq_refl), G2. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - apply Z.mod_divide; [lia|].
      assert (Hm32 : c_sp1 cx mod 32 = 0) by exact Hs5. assert (Hm16 : spZ (c_regs cx) mod 16 = 0) by exact Hs1.
      apply Z.mod_divide in Hm32; [|lia]. apply Z.mod_divide in Hm16; [|lia].
      destruct Hm32 as [a Ha]. destruct Hm16 as [b Hb]. exists (2 * a - b). lia.
    - lia.
    - unfold GB_STK. assert (Hes : ESTACK = 4096) by reflexivity. lia.
    - rewrite Rgp, (EE 3%nat 3%bv eq_refl), G3. exact Hgp0.
    - rewrite Rtp, (EE 4%nat 4%bv eq_refl), G4. exact Htp0.
    - exact Rra.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split; [right; right; right; apply HFA; lia|].
      assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & _). lia.
    - exact (amem_range_sub_app (gF cx fp) 512 (gF cx fp + 32) 5 HF3 HF2 ltac:(lia) ltac:(lia) ltac:(lia)).
    - replace (gF cx fp + 32) with (gF cx fp + GO_MAC + 0) by (unfold GO_MAC; lia).
      exact (gb_mac_ra B MT LAWS cx fp W3 ms0 ly3 S3 _ k HB HJ HFR 0 5 HSHm ltac:(lia) ltac:(lia)).
    - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ GB_CID fp (gF cx fp + 32) 5
        HAR0 Hfin); rewrite ?EF, ?Hfb; lia.
    -
      pose proof (gb_F_facts B MT LAWS cx fp W3 ms0 ly3 S3 _ k HB HJ HFR) as (_ & _ & _ & HIMG & _).
      assert (Hspm : spZ (ms_regs ms0) = c_sp1 cx)
        by (unfold spZ; rewrite Rsp, (EE 2%nat 2%bv eq_refl), G2; unfold w64; apply unsigned_lit_small; lia).
      assert (Hes2 : ESTACK = 4096) by reflexivity.
      split; [lia|]. split; [lia|].
      split.
      { intros a Ha. split.
        - replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia. rewrite HSRC by lia. discriminate.
        - rewrite Hspm. lia. }
      split; [destruct HIMG as [HL|HR]; [left | right]; lia|].
      split; [unfold amem_range, kLowMemEnd; left; lia|].
      destruct (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem ms0) _ (VAL (A_OBJ 4)) 5 (VAL (A_OBJ 4)) 5 HGLOB
        ltac:(unfold BX_G; cbn [In]; tauto) HISV HAR0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_HI; lia)) as [HRA HHU].
      split; [exact HRA | intros _; exact HHU]. }
  cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfrm & Hpres2).
  assert (HMACB : forall j, 0 <= j < 5 ->
    aview SEGS (w_H W3) mem2 (gF cx fp + 32 + j) = Some (nth (Z.to_nat j) [0; 64; 171; 0; 0] 0))
    by (intros j Hj; rewrite (Heff j Hj); exact (HSRC j Hj)).
  assert (HK3 : cm_keep cx fp W3 (ms_mem ms0) mem2).
  { intros a Ha Ho. apply Hfrm; [exact Ha | unfold cm_out in Ho; lia | unfold cm_out in Ho;
      assert (Hes : ESTACK = 4096) by reflexivity; lia]. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM2 HK3) as HM3.
  jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0%nat; 1%nat] HS2.
  match type of HS2 with ?Q -> _ => assert (HQK : Q) end.
  { pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
    assert (Hes : ESTACK = 4096) by reflexivity.
    cbn [ms_mem restrict].
    repeat (apply Forall_cons; [split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val];
      rewrite U9; intros a Ha;
      [ apply (mbyte_of_aview SEGS); apply Hfrm; [lia | lia | lia]
      | intros _; apply (apresent_writable SEGS); apply HJpres; unfold GB_STK; lia ] |]).
    apply Forall_nil. }
  specialize (HS2 HQK). clear HQK HS.
  set (E' := havoc E 512 (map (getr regs2) CLOB)) in HS2.
  assert (EWold : forall n, (n < 512)%nat -> ew E' n = ew E n)
    by (unfold E'; intros nn Hnn; apply YN3v.ew_havoc_old; exact Hnn).
  assert (HEI' : img_env VAL A_LIM E') by (unfold E'; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
  assert (U34' : bv_unsigned (ew E' 34) = gF cx fp) by (rewrite (EWold 34%nat ltac:(lia)); exact U34).
  assert (U9' : bv_unsigned (ew E' 9) = c_sp1 cx) by (rewrite (EWold 9%nat ltac:(lia)); exact U9).
  assert (F18' : ew E' 18 = w64 SHADOW_OFF) by (rewrite (EWold 18%nat ltac:(lia)); exact F18).
  assert (F32' : ew E' 32 = w64 (c_p cx + pos)) by (rewrite (EWold 32%nat ltac:(lia)); exact F32).
  assert (F33' : ew E' 33 = w64 (c_n cx - pos)) by (rewrite (EWold 33%nat ltac:(lia)); exact F33).
  assert (FB' : forall j, (j < 7)%nat -> ew E' (35 + j) = w64 (cm_inbyte cx pos j))
    by (intros j Hj; rewrite (EWold (35 + j)%nat ltac:(lia)); apply FB; exact Hj).
  pose proof HM3 as (HM3c & _). pose proof HM3c as (_ & HSH3 & _).
  assert (SHOK3 : sh_ok SEGS cm_Bx cm_SH0 E' (mrestrict (w_H W3) mem2)).
  { unfold sh_ok, cm_SH0. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W3) mem2 E' cm_Bx 34 (gF cx fp + 32) 6 (gF cx fp) 32 38).
    - replace (gF cx fp + 32) with (gF cx fp + GO_MAC + 0) by (unfold GO_MAC; lia).
      exact (gb_mac_ra B MT LAWS cx fp W3 (cm_ms cx mem2) ly3 S3 _ k HB HJ2 HFR 0 6 HSH3 ltac:(lia) ltac:(lia)).
    - unfold cm_Bx. exact (U_atom E' 18 SHADOW_OFF F18' ltac:(unfold SHADOW_OFF; lia)).
    - exact (U_atom E' 34 (gF cx fp) ltac:(rewrite (EWold 34%nat ltac:(lia)); exact F34) ltac:(lia)).
    - lia.
    - lia.
    - intros x Hx. revert HF3 Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. clear. intros. lia. }
  pose proof HJ2 as (HAR2 & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ GB_CID fp HAR2 Hfin) as (_ & _ & HFpres2 & _).
  rewrite EF, Hfb in HFpres2.
  assert (HRMAC : YP09.region_ok SEGS E' (mrestrict (w_H W3) mem2)
    (YP09.mkRegion (Some 34%nat) 32 38 32 38
      [YP09.mkChunk 32 (CVal 1 (SLit 0)); YP09.mkChunk 33 (CVal 1 (SLit 64)); YP09.mkChunk 34 (CVal 1 (SLit 171));
       YP09.mkChunk 35 (CVal 1 (SLit 0)); YP09.mkChunk 36 (CVal 1 (SLit 0))])).
  { unfold YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite U34'. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (HFpres2 (gF cx fp + o) ltac:(lia)))|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (cm_chunk1 E' (w_H W3) mem2 (gF cx fp) 32 (SLit 0) 0); [reflexivity|].
      replace (gF cx fp + 32) with (gF cx fp + 32 + 0) by lia. exact (HMACB 0 ltac:(lia)).
    - apply (cm_chunk1 E' (w_H W3) mem2 (gF cx fp) 33 (SLit 64) 64); [reflexivity|].
      replace (gF cx fp + 33) with (gF cx fp + 32 + 1) by lia. exact (HMACB 1 ltac:(lia)).
    - apply (cm_chunk1 E' (w_H W3) mem2 (gF cx fp) 34 (SLit 171) 171); [reflexivity|].
      replace (gF cx fp + 34) with (gF cx fp + 32 + 2) by lia. exact (HMACB 2 ltac:(lia)).
    - apply (cm_chunk1 E' (w_H W3) mem2 (gF cx fp) 35 (SLit 0) 0); [reflexivity|].
      replace (gF cx fp + 35) with (gF cx fp + 32 + 3) by lia. exact (HMACB 3 ltac:(lia)).
    - apply (cm_chunk1 E' (w_H W3) mem2 (gF cx fp) 36 (SLit 0) 0); [reflexivity|].
      replace (gF cx fp + 36) with (gF cx fp + 32 + 4) by lia. exact (HMACB 4 ltac:(lia)). }

  lazymatch type of HS2 with st_ok_pi _ _ _ ?ss0 _ => set (SS0 := ss0) in HS2 end.
  assert (WF : YP09.region_wf (YP09.mkRegion (Some 34%nat) 32 38 32 38
      [YP09.mkChunk 32 (CVal 1 (SLit 0)); YP09.mkChunk 33 (CVal 1 (SLit 64)); YP09.mkChunk 34 (CVal 1 (SLit 171));
       YP09.mkChunk 35 (CVal 1 (SLit 0)); YP09.mkChunk 36 (CVal 1 (SLit 0))]) = true) by (vm_compute; reflexivity).
  assert (DJ : YP09.all_disjoint E' (YP09.mkRegion (Some 34%nat) 32 38 32 38
      [YP09.mkChunk 32 (CVal 1 (SLit 0)); YP09.mkChunk 33 (CVal 1 (SLit 64)); YP09.mkChunk 34 (CVal 1 (SLit 171));
       YP09.mkChunk 35 (CVal 1 (SLit 0)); YP09.mkChunk 36 (CVal 1 (SLit 0))]) (ss_mem SS0)).
  { unfold SS0. cbn [ss_mem YP09.all_disjoint]. unfold YP09.extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U9', U34'.
    pose proof asan_consts as (Cq & _). repeat split; try exact I; lia. }
  pose proof (st_ok_pi_add_region E' SS0 _ _ HS2 WF HRMAC DJ) as HS3.
  clear HS2 HRMAC WF DJ.
  set (msA := mkst regs2 (Z_to_bv 64 (BASE + 1148)) mem2 (seg_rom SEGS)).
  lazymatch type of HS3 with st_ok_pi _ _ _ ?ss3 _ => set (SS3 := ss3) in HS3 end.
  change (st_ok_pi SEGS VAL E' SS3 (restrict (w_H W3) msA)) in HS3.
  change (sh_ok SEGS cm_Bx cm_SH0 E' (mrestrict (w_H W3) (ms_mem msA))) in SHOK3.
  assert (Hcppos : 0 <= c_p cx + pos < 2 ^ 64).
  { destruct Hinp as [(Hn0 & Hp0) | (_ & _ & Hp4 & Hpc2 & _)]; [rewrite Hp0; unfold GB_EMPTY; lia | lia]. }
  assert (U32' : bv_unsigned (ew E' 32) = c_p cx + pos) by (apply (cm_U E' 32); [exact F32' | exact Hcppos]).
  assert (Hcn : c_n cx < 2 ^ 26) by (destruct Hinp as [(Hn0 & _) | (Hn & _)]; lia).
  set (kk := Z.to_nat (Z.min (c_n cx - pos) 2)).
  assert (Hkk2 : (kk <= 2)%nat) by (unfold kk; lia).
  assert (Hkkn : pos + Z.of_nat kk <= c_n cx) by (unfold kk; lia).
  pose proof HM3c as (_ & _ & _ & HINm & _).
  assert (Hf33 : afact_ok E' 33 (cm_remf 2 kk))
    by (apply (cm_remf_ok E' cx pos 2 kk F33'); [lia | exact Hcn | lia | reflexivity]).
  assert (Haddk : kk = 0%nat \/ (YP09.region_wf (cm_inb kk) = true /\
     YP09.region_ok SEGS E' (mrestrict (w_H W3) (ms_mem msA)) (cm_inb kk) /\ YP09.all_disjoint E' (cm_inb kk) (ss_mem SS3) /\
     shent_ok SEGS cm_Bx E' (mrestrict (w_H W3) (ms_mem msA)) (mkSHE 32 0 (Z.of_nat kk)))).
  { destruct (Nat.eq_dec kk 0) as [->|Hk0]; [left; reflexivity|right].
    assert (Hcn0 : 0 < c_n cx) by (unfold kk in Hk0; lia).
    destruct Hinp as [(Hn0 & _) | (_ & Hin2 & Hp4 & Hpc2 & Hpia & HpF & HpR)]; [lia|].
    split; [apply cm_inb_wf|].
    split; [apply (cm_inb_ok cx pos W3 (ms_mem msA) E' kk F32' FB' HINm); lia|].
    split.
    { unfold SS3, SS0. cbn [ss_mem]. unfold cm_inb. cbn [YP09.all_disjoint]. unfold YP09.extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U32', U9', U34'. repeat split; try exact I; lia. }
    { apply (cm_inb_sh cx pos ly3 S3 W3 mem2 _ E' kk HAR2 Hin2 Hcn0 Hpia Hpc2 F18' F32'); lia. } }
  pose proof (cm_addin E' _ msA W3 2 kk HS3 SHOK3 Hf33 Haddk) as [HS4 SHOK4].
  clear Hf33 Haddk HS3 SHOK3.
  assert (Kc : kk = 0%nat \/ kk = 1%nat \/ kk = 2%nat) by lia.
  destruct Kc as [Ek|[Ek|Ek]].
  1: {
  rewrite Ek in HS4, SHOK4.
  lazymatch type of HS4 with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS4 end.
  lazymatch type of SHOK4 with sh_ok _ _ ?sh _ _ => let v := eval vm_compute in sh in change sh with v in SHOK4 end.
  paj_run_to_tok RUNTO HS4 HJ2 SHOK4 cm_span PC1_nch.

  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9'; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34' | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }

  
  lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msB end.
  assert (HKx : cm_keep cx fp W3 (ms_mem msA) (ms_mem msB)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9', ?U34', ?U32' in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM3 HKx) as HMq1. clear HM3 HKx HF HFr HG.

  assert (Hz : c_n cx - pos = 0) by (unfold kk in Ek; lia).
  lazymatch type of HS4 with st_ok_pi _ _ ?Ee _ _ =>
    assert (EW33v : bv_unsigned (ew Ee 33) = c_n cx - pos) by (rewrite ?ew_ewset_other by lia; rewrite F33'; apply unsigned_lit_small; lia);
    assert (HUk : U Ee (SOff 33 0) = 0) by (rewrite U_SOff, EW33v; replace (c_n cx - pos + 0) with 0 by lia; apply zcanon_id; unfold M64; lia);
    assert (HU0 : U Ee (SLit 0) = 0) by (apply U_lit; lia) end.
  psrr_branch_tok RUN BR HS4 SHOK4 cm_span;
  [ | exfalso; rewrite branch_eq_U, HUk, HU0 in Hc; apply Z.eqb_neq in Hc; lia ].
  clear HUk HU0 EW33v.
  paj_run_to_tok RUNTO HS4 HJ2 SHOK4 cm_span PC1_nch.

  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9'; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34' | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }

  
  lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  lazymatch type of HS4 with st_ok_pi _ _ ?Ee _ _ => pose (EF2 := Ee) end.
  assert (EWlt : forall n, (n < 512)%nat -> ew EF2 n = ew E' n)
    by (unfold EF2; intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msF HS4 eq_refl) as Hmk0. cbn [ss_pc] in Hmk0.
  pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS4 eq_refl) as Rfr.
  pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS4 eq_refl) as Rnch.
  pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS4 eq_refl) as Rcur.
  assert (EW34 : bv_unsigned (ew EF2 34) = gF cx fp) by (rewrite (EWlt 34%nat ltac:(lia)); exact U34').
  assert (EW9 : bv_unsigned (ew EF2 9) = c_sp1 cx) by (rewrite (EWlt 9%nat ltac:(lia)); exact U9').
  assert (EW32 : ew EF2 32 = w64 (c_p cx + pos)) by (rewrite (EWlt 32%nat ltac:(lia)); exact F32').
  assert (EW33 : ew EF2 33 = w64 (c_n cx - pos)) by (rewrite (EWlt 33%nat ltac:(lia)); exact F33').
  destruct (cm_mac6g EF2 W3 (ms_mem msF) _ (gF cx fp) _ _ _ _ _ _ Rfr EW34
    ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)
    ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)) as (M & HML & HMac).
  pose proof (cm_slot8 EF2 W3 (ms_mem msF) _ _ _ _ _ _ 88 (SLit 0) Rnch EW9 ltac:(cbn [In]; tauto) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia)) as Hnch0.
  change (bv_unsigned (sv_denot EF2 (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in Hnch0.
  set (nch := 0). assert (Hnchr : 0 <= nch < 256) by (unfold nch; lia).
  assert (Hnchrd : rdword (aview SEGS (w_H W3) (ms_mem msF)) (c_sp1 cx + 88) = Some nch) by exact Hnch0.
  pose proof (cm_slot_off EF2 W3 (ms_mem msF) _ _ _ _ _ _ 136 32 0 (c_p cx + pos) Rcur EW9 ltac:(cbn [In]; tauto) EW32 Hcppos ltac:(lia)) as Hc88.
  pose proof (cm_slot_off EF2 W3 (ms_mem msF) _ _ _ _ _ _ 144 33 (-(0)) (c_n cx - pos) Rcur EW9 ltac:(cbn [In]; tauto) EW33 ltac:(lia) ltac:(lia)) as Hc90.

  lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  assert (HKx : cm_keep cx fp W3 (ms_mem msB) (ms_mem msF)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9', ?U34', ?U32' in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HMq1 HKx) as HMq2. clear HMq1 HKx HF HFr HG.

  assert (RG2 : getr (ms_regs msF) 2 = _) by (prreg HS4 (2%bv : bv 5) PX2; rewrite PX2; rewrite ?(EWlt 2%nat ltac:(lia)); rewrite (EWold 2%nat ltac:(lia)), (EE 2%nat 2%bv eq_refl); exact G2).
  assert (RG8 : getr (ms_regs msF) 8 = _) by (prreg HS4 (8%bv : bv 5) PX8; rewrite PX8; rewrite ?(EWlt 8%nat ltac:(lia)); rewrite (EWold 8%nat ltac:(lia)), (EE 8%nat 8%bv eq_refl); exact G8).
  assert (RG9 : getr (ms_regs msF) 9 = _) by (prreg HS4 (9%bv : bv 5) PX9; rewrite PX9; rewrite ?(EWlt 9%nat ltac:(lia)); rewrite (EWold 9%nat ltac:(lia)), (EE 9%nat 9%bv eq_refl); exact G9).
  assert (RG3 : getr (ms_regs msF) 3 = _) by (prreg HS4 (3%bv : bv 5) PX3; rewrite PX3; rewrite ?(EWlt 3%nat ltac:(lia)); rewrite (EWold 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl); exact G3).
  assert (RG4 : getr (ms_regs msF) 4 = _) by (prreg HS4 (4%bv : bv 5) PX4; rewrite PX4; rewrite ?(EWlt 4%nat ltac:(lia)); rewrite (EWold 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl); exact G4).
  assert (RG18 : getr (ms_regs msF) 18 = _) by (prreg HS4 (18%bv : bv 5) PX18; rewrite PX18; rewrite ?(EWlt 18%nat ltac:(lia)); rewrite (EWold 18%nat ltac:(lia)), (EE 18%nat 18%bv eq_refl); exact G18).
  assert (RG24 : getr (ms_regs msF) 24 = _) by (prreg HS4 (24%bv : bv 5) PX24; rewrite PX24; rewrite ?(EWlt 24%nat ltac:(lia)); rewrite (EWold 24%nat ltac:(lia)), (EE 24%nat 24%bv eq_refl); exact G24).
  assert (RG20 : getr (ms_regs msF) 20 = _) by (prreg HS4 (20%bv : bv 5) PX20; rewrite PX20; rewrite ?(EWlt 20%nat ltac:(lia)); rewrite (EWold 20%nat ltac:(lia)), (EE 20%nat 20%bv eq_refl); exact R20).
  assert (RG25 : getr (ms_regs msF) 25 = _) by (prreg HS4 (25%bv : bv 5) PX25; rewrite PX25; rewrite ?(EWlt 25%nat ltac:(lia)); rewrite (EWold 25%nat ltac:(lia)), (EE 25%nat 25%bv eq_refl); exact R25).
  prreg HS4 (19%bv : bv 5) PX19. rewrite ?(EWlt 34%nat ltac:(lia)) in PX19; rewrite U34' in PX19.
  apply (cm_land msF _ M nch (pos + (0)) HB HJ2 HFR HMO Hi Hk Hacc HBLK HINV).
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - unfold gregs. split; [exact RG2|]. split; [exact RG8|]. split; [exact RG9|].
    split; [exact RG3|]. split; [exact RG4|]. split; [exact RG18 | exact RG24].
  - exact RG20.
  - unfold GO_MAC; exact PX19.
  - exact RG25.
  - exact HMq2.
  - exact HML.
  - unfold GO_MAC. exact HMac.
  - exact Hnchr.
  - unfold gslot. exact Hnchrd.
  - lia.
  - unfold gslot. replace (c_p cx + (pos + (0))) with (c_p cx + pos + (0)) by lia. exact Hc88.
  - unfold gslot. replace (c_n cx - (pos + (0))) with (c_n cx - pos + (-(0))) by lia. exact Hc90.
}
  1: {
  rewrite Ek in HS4, SHOK4.
  lazymatch type of HS4 with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS4 end.
  lazymatch type of SHOK4 with sh_ok _ _ ?sh _ _ => let v := eval vm_compute in sh in change sh with v in SHOK4 end.
  paj_run_to_tok RUNTO HS4 HJ2 SHOK4 cm_span PC1_nch.

  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9'; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34' | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }

  
  lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msB end.
  assert (HKx : cm_keep cx fp W3 (ms_mem msA) (ms_mem msB)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9', ?U34', ?U32' in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM3 HKx) as HMq1. clear HM3 HKx HF HFr HG.

  assert (Hz1 : c_n cx - pos = 1) by (unfold kk in Ek; lia).
  lazymatch type of HS4 with st_ok_pi _ _ ?Ee _ _ =>
    assert (EW33v : bv_unsigned (ew Ee 33) = c_n cx - pos) by (rewrite ?ew_ewset_other by lia; rewrite F33'; apply unsigned_lit_small; lia);
    assert (HUk : U Ee (SOff 33 (-1)) = 0) by (rewrite U_SOff, EW33v; replace (c_n cx - pos + (-1)) with 0 by lia; apply zcanon_id; unfold M64; lia);
    assert (HU0 : U Ee (SLit 0) = 0) by (apply U_lit; lia) end.
  psrr_branch_tok RUN BR HS4 SHOK4 cm_span;
  [ | exfalso; rewrite branch_eq_U, HUk, HU0 in Hc; apply Z.eqb_neq in Hc; lia ].
  clear HUk HU0 EW33v.
  paj_run_to_tok RUNTO HS4 HJ2 SHOK4 cm_span PC1_nch.

  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9'; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34' | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }

  
  lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  lazymatch type of HS4 with st_ok_pi _ _ ?Ee _ _ => pose (EF2 := Ee) end.
  assert (EWlt : forall n, (n < 512)%nat -> ew EF2 n = ew E' n)
    by (unfold EF2; intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msF HS4 eq_refl) as Hmk0. cbn [ss_pc] in Hmk0.
  pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS4 eq_refl) as Rfr.
  pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS4 eq_refl) as Rnch.
  pose proof (st_ok_pi_region_nth _ _ _ 3%nat _ HS4 eq_refl) as Rcur.
  assert (EW34 : bv_unsigned (ew EF2 34) = gF cx fp) by (rewrite (EWlt 34%nat ltac:(lia)); exact U34').
  assert (EW9 : bv_unsigned (ew EF2 9) = c_sp1 cx) by (rewrite (EWlt 9%nat ltac:(lia)); exact U9').
  assert (EW32 : ew EF2 32 = w64 (c_p cx + pos)) by (rewrite (EWlt 32%nat ltac:(lia)); exact F32').
  assert (EW33 : ew EF2 33 = w64 (c_n cx - pos)) by (rewrite (EWlt 33%nat ltac:(lia)); exact F33').
  destruct (cm_mac6g EF2 W3 (ms_mem msF) _ (gF cx fp) _ _ _ _ _ _ Rfr EW34
    ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)
    ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)) as (M & HML & HMac).
  pose proof (cm_slot8 EF2 W3 (ms_mem msF) _ _ _ _ _ _ 88 (SLit 0) Rnch EW9 ltac:(cbn [In]; tauto) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia)) as Hnch0.
  change (bv_unsigned (sv_denot EF2 (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in Hnch0.
  set (nch := 0). assert (Hnchr : 0 <= nch < 256) by (unfold nch; lia).
  assert (Hnchrd : rdword (aview SEGS (w_H W3) (ms_mem msF)) (c_sp1 cx + 88) = Some nch) by exact Hnch0.
  pose proof (cm_slot_off EF2 W3 (ms_mem msF) _ _ _ _ _ _ 136 32 1 (c_p cx + pos) Rcur EW9 ltac:(cbn [In]; tauto) EW32 Hcppos ltac:(lia)) as Hc88.
  pose proof (cm_slot_off EF2 W3 (ms_mem msF) _ _ _ _ _ _ 144 33 (-(1)) (c_n cx - pos) Rcur EW9 ltac:(cbn [In]; tauto) EW33 ltac:(lia) ltac:(lia)) as Hc90.

  lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  assert (HKx : cm_keep cx fp W3 (ms_mem msB) (ms_mem msF)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9', ?U34', ?U32' in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HMq1 HKx) as HMq2. clear HMq1 HKx HF HFr HG.

  assert (RG2 : getr (ms_regs msF) 2 = _) by (prreg HS4 (2%bv : bv 5) PX2; rewrite PX2; rewrite ?(EWlt 2%nat ltac:(lia)); rewrite (EWold 2%nat ltac:(lia)), (EE 2%nat 2%bv eq_refl); exact G2).
  assert (RG8 : getr (ms_regs msF) 8 = _) by (prreg HS4 (8%bv : bv 5) PX8; rewrite PX8; rewrite ?(EWlt 8%nat ltac:(lia)); rewrite (EWold 8%nat ltac:(lia)), (EE 8%nat 8%bv eq_refl); exact G8).
  assert (RG9 : getr (ms_regs msF) 9 = _) by (prreg HS4 (9%bv : bv 5) PX9; rewrite PX9; rewrite ?(EWlt 9%nat ltac:(lia)); rewrite (EWold 9%nat ltac:(lia)), (EE 9%nat 9%bv eq_refl); exact G9).
  assert (RG3 : getr (ms_regs msF) 3 = _) by (prreg HS4 (3%bv : bv 5) PX3; rewrite PX3; rewrite ?(EWlt 3%nat ltac:(lia)); rewrite (EWold 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl); exact G3).
  assert (RG4 : getr (ms_regs msF) 4 = _) by (prreg HS4 (4%bv : bv 5) PX4; rewrite PX4; rewrite ?(EWlt 4%nat ltac:(lia)); rewrite (EWold 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl); exact G4).
  assert (RG18 : getr (ms_regs msF) 18 = _) by (prreg HS4 (18%bv : bv 5) PX18; rewrite PX18; rewrite ?(EWlt 18%nat ltac:(lia)); rewrite (EWold 18%nat ltac:(lia)), (EE 18%nat 18%bv eq_refl); exact G18).
  assert (RG24 : getr (ms_regs msF) 24 = _) by (prreg HS4 (24%bv : bv 5) PX24; rewrite PX24; rewrite ?(EWlt 24%nat ltac:(lia)); rewrite (EWold 24%nat ltac:(lia)), (EE 24%nat 24%bv eq_refl); exact G24).
  assert (RG20 : getr (ms_regs msF) 20 = _) by (prreg HS4 (20%bv : bv 5) PX20; rewrite PX20; rewrite ?(EWlt 20%nat ltac:(lia)); rewrite (EWold 20%nat ltac:(lia)), (EE 20%nat 20%bv eq_refl); exact R20).
  assert (RG25 : getr (ms_regs msF) 25 = _) by (prreg HS4 (25%bv : bv 5) PX25; rewrite PX25; rewrite ?(EWlt 25%nat ltac:(lia)); rewrite (EWold 25%nat ltac:(lia)), (EE 25%nat 25%bv eq_refl); exact R25).
  prreg HS4 (19%bv : bv 5) PX19. rewrite ?(EWlt 34%nat ltac:(lia)) in PX19; rewrite U34' in PX19.
  apply (cm_land msF _ M nch (pos + (1)) HB HJ2 HFR HMO Hi Hk Hacc HBLK HINV).
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - unfold gregs. split; [exact RG2|]. split; [exact RG8|]. split; [exact RG9|].
    split; [exact RG3|]. split; [exact RG4|]. split; [exact RG18 | exact RG24].
  - exact RG20.
  - unfold GO_MAC; exact PX19.
  - exact RG25.
  - exact HMq2.
  - exact HML.
  - unfold GO_MAC. exact HMac.
  - exact Hnchr.
  - unfold gslot. exact Hnchrd.
  - lia.
  - unfold gslot. replace (c_p cx + (pos + (1))) with (c_p cx + pos + (1)) by lia. exact Hc88.
  - unfold gslot. replace (c_n cx - (pos + (1))) with (c_n cx - pos + (-(1))) by lia. exact Hc90.
}
  1: {
  rewrite Ek in HS4, SHOK4.
  lazymatch type of HS4 with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS4 end.
  lazymatch type of SHOK4 with sh_ok _ _ ?sh _ _ => let v := eval vm_compute in sh in change sh with v in SHOK4 end.
  paj_run_to_tok RUNTO HS4 HJ2 SHOK4 cm_span PC1_nch.

  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end.
    repeat first
      [ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
      | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
          [reflexivity | rewrite ?ew_ewset_other by lia; rewrite U9'; lia | cbn [YP09.r_wlo]; unfold GB_STK; lia | cbn [YP09.r_whi]; lia | ]
      | apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gF cx fp));
          [reflexivity | rewrite ?ew_ewset_other by lia; exact U34' | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; apply HFA; lia | ]
      | apply awr_ok_nil ]. }

  
  lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  lazymatch type of HS4 with st_ok_pi _ _ ?Ee _ _ => pose (EF2 := Ee) end.
  assert (EWlt : forall n, (n < 512)%nat -> ew EF2 n = ew E' n)
    by (unfold EF2; intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msF HS4 eq_refl) as Hmk0. cbn [ss_pc] in Hmk0.
  pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS4 eq_refl) as Rfr.
  pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS4 eq_refl) as Rnch.
  pose proof (st_ok_pi_region_nth _ _ _ 3%nat _ HS4 eq_refl) as Rcur.
  assert (EW34 : bv_unsigned (ew EF2 34) = gF cx fp) by (rewrite (EWlt 34%nat ltac:(lia)); exact U34').
  assert (EW9 : bv_unsigned (ew EF2 9) = c_sp1 cx) by (rewrite (EWlt 9%nat ltac:(lia)); exact U9').
  assert (EW32 : ew EF2 32 = w64 (c_p cx + pos)) by (rewrite (EWlt 32%nat ltac:(lia)); exact F32').
  assert (EW33 : ew EF2 33 = w64 (c_n cx - pos)) by (rewrite (EWlt 33%nat ltac:(lia)); exact F33').
  destruct (cm_mac6g EF2 W3 (ms_mem msF) _ (gF cx fp) _ _ _ _ _ _ Rfr EW34
    ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)
    ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)) as (M & HML & HMac).
  destruct (cm_slot_byte EF2 W3 (ms_mem msF) _ _ _ _ _ _ 88 (SOff 36 0) Rnch EW9 ltac:(cbn [In]; tauto)) as (nch & Hnchr & Hnchrd).
  pose proof (cm_slot_off EF2 W3 (ms_mem msF) _ _ _ _ _ _ 136 32 2 (c_p cx + pos) Rcur EW9 ltac:(cbn [In]; tauto) EW32 Hcppos ltac:(lia)) as Hc88.
  pose proof (cm_slot_off EF2 W3 (ms_mem msF) _ _ _ _ _ _ 144 33 (-(2)) (c_n cx - pos) Rcur EW9 ltac:(cbn [In]; tauto) EW33 ltac:(lia) ltac:(lia)) as Hc90.

  lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
  assert (HKx : cm_keep cx fp W3 (ms_mem msA) (ms_mem msF)).
  { apply (cm_keep_frame cx fp W3 _ _ _ _ HF).
    let rsx := lazymatch type of HF with frame_of _ ?rs _ _ => rs end in
    let rs' := eval vm_compute in rsx in change rsx with rs'.
    intros a Ha (r0 & Hr & Hb). cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
       rewrite ?U9', ?U34', ?U32' in Hb; unfold cm_out; lia |]);
    destruct Hr. }
  pose proof (cm_mem0_keep cx fp ly3 S3 W3 i r bs Gsp GF GR GI _ _ HM3 HKx) as HMq2. clear HM3 HKx HF HFr HG.

  assert (RG2 : getr (ms_regs msF) 2 = _) by (prreg HS4 (2%bv : bv 5) PX2; rewrite PX2; rewrite ?(EWlt 2%nat ltac:(lia)); rewrite (EWold 2%nat ltac:(lia)), (EE 2%nat 2%bv eq_refl); exact G2).
  assert (RG8 : getr (ms_regs msF) 8 = _) by (prreg HS4 (8%bv : bv 5) PX8; rewrite PX8; rewrite ?(EWlt 8%nat ltac:(lia)); rewrite (EWold 8%nat ltac:(lia)), (EE 8%nat 8%bv eq_refl); exact G8).
  assert (RG9 : getr (ms_regs msF) 9 = _) by (prreg HS4 (9%bv : bv 5) PX9; rewrite PX9; rewrite ?(EWlt 9%nat ltac:(lia)); rewrite (EWold 9%nat ltac:(lia)), (EE 9%nat 9%bv eq_refl); exact G9).
  assert (RG3 : getr (ms_regs msF) 3 = _) by (prreg HS4 (3%bv : bv 5) PX3; rewrite PX3; rewrite ?(EWlt 3%nat ltac:(lia)); rewrite (EWold 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl); exact G3).
  assert (RG4 : getr (ms_regs msF) 4 = _) by (prreg HS4 (4%bv : bv 5) PX4; rewrite PX4; rewrite ?(EWlt 4%nat ltac:(lia)); rewrite (EWold 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl); exact G4).
  assert (RG18 : getr (ms_regs msF) 18 = _) by (prreg HS4 (18%bv : bv 5) PX18; rewrite PX18; rewrite ?(EWlt 18%nat ltac:(lia)); rewrite (EWold 18%nat ltac:(lia)), (EE 18%nat 18%bv eq_refl); exact G18).
  assert (RG24 : getr (ms_regs msF) 24 = _) by (prreg HS4 (24%bv : bv 5) PX24; rewrite PX24; rewrite ?(EWlt 24%nat ltac:(lia)); rewrite (EWold 24%nat ltac:(lia)), (EE 24%nat 24%bv eq_refl); exact G24).
  assert (RG20 : getr (ms_regs msF) 20 = _) by (prreg HS4 (20%bv : bv 5) PX20; rewrite PX20; rewrite ?(EWlt 20%nat ltac:(lia)); rewrite (EWold 20%nat ltac:(lia)), (EE 20%nat 20%bv eq_refl); exact R20).
  assert (RG25 : getr (ms_regs msF) 25 = _) by (prreg HS4 (25%bv : bv 5) PX25; rewrite PX25; rewrite ?(EWlt 25%nat ltac:(lia)); rewrite (EWold 25%nat ltac:(lia)), (EE 25%nat 25%bv eq_refl); exact R25).
  prreg HS4 (19%bv : bv 5) PX19. rewrite ?(EWlt 34%nat ltac:(lia)) in PX19; rewrite U34' in PX19.
  apply (cm_land msF _ M nch (pos + (2)) HB HJ2 HFR HMO Hi Hk Hacc HBLK HINV).
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - rewrite Hmk0 at 1; reflexivity.
  - unfold gregs. split; [exact RG2|]. split; [exact RG8|]. split; [exact RG9|].
    split; [exact RG3|]. split; [exact RG4|]. split; [exact RG18 | exact RG24].
  - exact RG20.
  - unfold GO_MAC; exact PX19.
  - exact RG25.
  - exact HMq2.
  - exact HML.
  - unfold GO_MAC. exact HMac.
  - exact Hnchr.
  - unfold gslot. exact Hnchrd.
  - lia.
  - unfold gslot. replace (c_p cx + (pos + (2))) with (c_p cx + pos + (2)) by lia. exact Hc88.
  - unfold gslot. replace (c_n cx - (pos + (2))) with (c_n cx - pos + (-(2))) by lia. exact Hc90.
  }
Qed.


End cm_p.

Theorem c1_seg_mac : forall i, gb_from B MT POST (C1_nch B MT i) -> gb_from B MT POST (GI_T B MT 1 i).
Proof.
  intros i HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
  destruct HI as (r & bs & pos & op & HBODY & Hi & Hk & Hacc & HBLK & HREG & HPRV & HINV & Hop & Hop3 & R20 & R22
    & R25 & R26 & HSLR & HCUR & H68 & H48).
  specialize (H48 ltac:(lia)).
  change (GP_T 1) with PC1_mac0 in HBODY.
  destruct (Z.eq_dec (Z.land op 4) 0) as [H4 | H4].
  - eapply cm_pathA; eassumption.
  - eapply cm_pathB; eassumption.
Qed.

End c.
End b.
End a.
