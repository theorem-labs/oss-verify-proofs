(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths, module names and addresses changed; 1418 of its 1528 lines of code are new or changed and 904 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgW3a.v; 527 of its 606 lines of code are new or changed and 1449 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the kit of part HDR of
   segment S_E01 of the walk of LLVMFuzzerTestOneInput (lib/A/RtPgE01D.v e01_hdr_stmt, HD 0x808e4 -> CALL 0x52bb4).
   Proves no function (kind: segment lemma, its parts).

   Templates (ported by edit): lib/A/RtPgRoute808.v (the region route of the instrumented 1-byte checks: the
   metadata byte as a one-byte read-only region at an extra atom, reached through alias facts); lib/A/RtPgSteps.v
   PART 2 (one symbolic state per input-length arm, the length register pinned to a literal); the role walk
   proofs/reac-pw/fuzz_role/lib/A/RPgW3a.v at commit 67b6b93ee241 (the input bytes as a region
   at the cursor's atom, the real frame's cells as a write window at s1's atom, reading the last state's registers
   and chunks: w3_reg_atom, w3_slot, w3_chunk8, w3_keep_run, w3_nz); the released libreac/fuzz_boxreg
   lib/A/Prog/BoxLxEntry.v at origin/ossv/recipes (eb_arodata: the read-only view kept by a journal whose
   footprint is empty).

   THE SYMBOLIC STATE AT 0x808e4 (e01h_ss m nv s nf), over the environment Ereg regs (e01h_extra p pl):
   atoms 0 .. 31 the registers, atom 32 the metadata byte's address SHADOW_OFF + p / 8, atoms 33 + k (k < 7) the
   header bytes rh_u8 pl k. s5 (x21) holds nv: the literal n in the arms n = 0 .. 7, its own atom with the fact
   [8, 2^26 - 1] in the arm n >= 8 (nf). The regions: R+0x38 .. R+0x128 as a write window at s1's atom 9; when
   m = min n 7 > 0, the m header bytes at s9's atom 25 and the metadata byte (the literal s: n when n < 8, else 0) at
   atom 32, with one alias fact ((s9 + k) >> 3) + s2 = atom 32 per k < m; when m >= 3, the 8 bytes at 0x10330
   (the constant of `ld` 0x8098c, buflen = byte 2 mod 24) as a base-free read-only region. The engine decides every
   length test and every metadata test from these literals, so each arm is one run to 0x52bb4 (no split, no
   obligation, measured).

   THE LEAF (e01h_leaf): what the run's last state gives, and e01h_call_of, which turns it into
   RtPgE01D.e01_call_facts at the run's quantities e01h_env. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSeg RtPgE01D.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgMem RtPgSteps.
From OSSVerify.reac_pw.fuzz_rate.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the code table ======================================== *)
(* 0x808e4 .. 0x809dc (63), the out-of-line block 0x82b94 .. 0x82c40 (44), the slow blocks of the seven checks *)
Definition e01h_tbl : ctable :=
  build_table rsegs 0x832a8 2 (build_table rsegs 0x83270 2 (build_table rsegs 0x83254 2 (build_table rsegs 0x83218 2
  (build_table rsegs 0x831e4 3 (build_table rsegs 0x83104 3 (build_table rsegs 0x83090 3
  (build_table rsegs 0x82b94 44 (build_table rsegs 0x808e4 63 TEmpty)))))))).
Lemma e01h_tbl_ok : table_ok rsegs e01h_tbl.
Proof. do 8 (apply build_table_ok; [lia|]). apply build_table_ok0. lia. Qed.
Definition E01H_Bx : sv := SOff 18 0.
Definition E01H_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* ======================================== the symbolic state ======================================== *)
Definition e01h_alias (k : nat) : sv * sv :=
  (SAlu ALU_ADD (SAlu ALU_SRL (SOff 25 (Z.of_nat k)) (SLit 3)) (SOff 18 0), SOff 32 0).
Definition e01h_inchunks (m : nat) : list YP09.chunk :=
  map (fun k => YP09.mkChunk (Z.of_nat k) (CVal 1 (SOff (33 + k) 0))) (seq 0 m).
Definition e01h_rIn (m : nat) : YP09.region := YP09.mkRegion (Some 25%nat) 0 (Z.of_nat m) 0 0 (e01h_inchunks m).
Definition e01h_rC (s : Z) : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit s))].
Definition e01h_rR : YP09.region := YP09.mkRegion (Some 9%nat) 0x38 0x128 0x38 0x128 [].
Definition e01h_rK : YP09.region := YP09.mkRegion None 0x10330 0x10338 0 0 [YP09.mkChunk 0x10330 (CImg 8)].
Definition e01h_mem (m : nat) (s : Z) : smem :=
  match m with
  | O => [e01h_rR]
  | 1%nat | 2%nat => [e01h_rR; e01h_rIn m; e01h_rC s]
  | _ => [e01h_rR; e01h_rIn m; e01h_rC s; e01h_rK]
  end.
Definition e01h_bytes_af (m : nat) : list (nat * afact) := map (fun k => ((33 + k)%nat, mkAF 0 255 0)) (seq 0 m).
Definition e01h_af (m : nat) (nf : list (nat * afact)) : list (nat * afact) :=
  (9%nat, mkAF 0x7fff7f800000 0x800000000000 5) :: nf ++
  match m with O => [] | _ => (25%nat, mkAF 4096 0x800000000000 4) :: e01h_bytes_af m end.
Definition e01h_facts (m : nat) (nf : list (nat * afact)) : facts :=
  mkFacts (e01h_af m nf) [] (map e01h_alias (seq 0 m)).
Definition e01h_ss (m : nat) (nv : sv) (s : Z) (nf : list (nat * afact)) : sstate :=
  mkSS 0x808e4 (sr_set sr_atoms (21%bv : bv 5) nv) (e01h_mem m s) None (e01h_facts m nf).
Definition e01h_extra (p : Z) (pl : list byte) : list word :=
  [w64 (SHADOW_OFF + p / 8); w64 (rh_u8 pl 0); w64 (rh_u8 pl 1); w64 (rh_u8 pl 2); w64 (rh_u8 pl 3);
   w64 (rh_u8 pl 4); w64 (rh_u8 pl 5); w64 (rh_u8 pl 6)].
(* the metadata byte of p's first granule (n >= 1) *)
Definition e01h_sv (n : Z) : Z := if n <? 8 then n else 0.
(* buflen = byte 2 mod 24 as the engine builds it (0x80994 .. 0x809a8) *)
Definition e01h_k24e (x : sv) : sv :=
  SAlu ALU_ADD x (SAlu ALU_SUB (SAlu ALU_SLL (SMd M_MULHU x (SLit 768614336404564651)) (SLit 3))
                               (SAlu ALU_SLL (SMd M_MULHU x (SLit 768614336404564651)) (SLit 5))).
Definition e01h_k24f (w : word) : word :=
  alu64 ALU_ADD w (alu64 ALU_SUB (alu64 ALU_SLL (mul_div M_MULHU w (Z_to_bv 64 768614336404564651)) (Z_to_bv 64 3))
                                 (alu64 ALU_SLL (mul_div M_MULHU w (Z_to_bv 64 768614336404564651)) (Z_to_bv 64 5))).
Lemma e01h_k24f_all :
  forallb (fun c => Z.eqb (bv_unsigned (e01h_k24f (Z_to_bv 64 c))) (c mod 24)) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== bytes ======================================== *)
Lemma e01h_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as Hb. exact Hb. Qed.
Lemma e01h_u8_range : forall pl i, 0 <= rh_u8 pl i < 256.
Proof. intros pl i. unfold rh_u8. destruct (nth_error pl i) as [b|]; [apply e01h_byte_range | lia]. Qed.
Lemma e01h_u8_out : forall pl i, (length pl <= i)%nat -> rh_u8 pl i = 0.
Proof. intros pl i H. unfold rh_u8. rewrite (proj2 (nth_error_None pl i) H). reflexivity. Qed.
Lemma e01h_u8_in : forall pl i, (i < length pl)%nat ->
  rh_u8 pl i = nth i (map (fun b : byte => bv_unsigned b) pl) 0.
Proof.
intros pl i H. unfold rh_u8. rewrite (nth_error_nth' pl (Z_to_bv 8 0) H).
pose proof (map_nth (fun b : byte => bv_unsigned b) pl (Z_to_bv 8 0) i) as M. cbv beta in M.
rewrite <- M. reflexivity.
Qed.
Lemma e01h_nth_skipn : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
intros l k. revert l. induction k as [|k IH]; intros l j; [reflexivity|].
destruct l as [|x l]; cbn; [destruct j; reflexivity | apply IH].
Qed.
Lemma e01h_skipn_map : forall (f : byte -> Z) (l : list byte) k, skipn k (map f l) = map f (skipn k l).
Proof.
intros f l k. revert l. induction k as [|k IH]; intros l; [reflexivity|]. destruct l as [|x l]; [reflexivity|]. apply IH.
Qed.
Lemma e01h_garr8_skip : forall m p (l : list Z) k,
  garr8 rsegs m p l -> garr8 rsegs m (p + Z.of_nat k) (skipn k l).
Proof.
intros m p l k H j Hj. rewrite length_skipn in Hj. rewrite e01h_nth_skipn.
replace (p + Z.of_nat k + Z.of_nat j) with (p + Z.of_nat (k + j)) by lia. apply H. lia.
Qed.
Lemma e01h_mod24 : forall c, 0 <= c < 256 -> e01h_k24f (Z_to_bv 64 c) = Z_to_bv 64 (c mod 24).
Proof.
intros c Hc. apply bv_eq. rewrite (unsigned_lit_small (c mod 24)) by (pose proof (Z.mod_pos_bound c 24); lia).
pose proof e01h_k24f_all as A. rewrite forallb_forall in A.
assert (Hin : In c (map Z.of_nat (seq 0 256))) by (apply in_map_iff; exists (Z.to_nat c); split; [lia | apply in_seq; lia]).
specialize (A c Hin). apply Z.eqb_eq in A. exact A.
Qed.

(* ======================================== the environment and the values ======================================== *)
Lemma e01h_ew32 : forall regs p pl, ew (Ereg regs (e01h_extra p pl)) 32 = w64 (SHADOW_OFF + p / 8).
Proof. intros regs p pl. exact (ew_Ereg_extra regs (e01h_extra p pl) 0). Qed.
Lemma e01h_ewb : forall regs p pl k, (k < 7)%nat -> ew (Ereg regs (e01h_extra p pl)) (33 + k) = w64 (rh_u8 pl k).
Proof.
intros regs p pl k Hk. change (33 + k)%nat with (32 + S k)%nat. rewrite ew_Ereg_extra.
destruct k as [|[|[|[|[|[|[|k]]]]]]]; try reflexivity; lia.
Qed.
Lemma e01h_den_off : forall E (k : nat) v c, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k c) = w64 (v + c).
Proof. intros E k v c Hk Hv. cbn [sv_denot]. rewrite Hk. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity. Qed.
Lemma e01h_den_off0 : forall E (k : nat) v, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k 0) = w64 v.
Proof. intros E k v Hk Hv. rewrite (e01h_den_off E k v 0 Hk Hv). rewrite Z.add_0_r. reflexivity. Qed.
Lemma e01h_den_sll8 : forall E (k : nat) b, ew E k = w64 b -> 0 <= b < 256 ->
  sv_denot E (SAlu ALU_SLL (SOff k 0) (SLit 8)) = w64 (Z.shiftl b 8).
Proof.
intros E k b Hk Hb. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_SLL (SOff k 0) (SLit 8)))) with (U E (SAlu ALU_SLL (SOff k 0) (SLit 8))).
rewrite U_SAlu, U_SLit, (U_atom E k b Hk ltac:(lia)). cbn [zalu_raw].
change (Z.land (zcanon 8) 63) with 8. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
unfold w64. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma e01h_den_mod24 : forall E (k : nat) b, ew E k = w64 b -> 0 <= b < 256 ->
  sv_denot E (e01h_k24e (SOff k 0)) = w64 (b mod 24).
Proof.
intros E k b Hk Hb.
assert (Hd : sv_denot E (SOff k 0) = Z_to_bv 64 b) by (exact (e01h_den_off0 E k b Hk ltac:(lia))).
change (sv_denot E (e01h_k24e (SOff k 0))) with (e01h_k24f (sv_denot E (SOff k 0))).
rewrite Hd. exact (e01h_mod24 b Hb).
Qed.
Lemma e01h_nz : forall z, 0 < z < 32 -> Z_to_bv 5 z <> 0%bv.
Proof.
intros z Hz Hc. apply (f_equal (@bv_unsigned 5)) in Hc. rewrite Z_to_bv_unsigned in Hc.
unfold bv_wrap in Hc. change (bv_modulus 5) with 32 in Hc. rewrite Z.mod_small in Hc by lia.
change (@bv_unsigned 5 0%bv) with 0 in Hc. lia.
Qed.
Lemma e01h_nz21 : (21%bv : bv 5) <> 0%bv.
Proof. intros Hc. apply (f_equal (@bv_unsigned 5)) in Hc. vm_compute in Hc. discriminate Hc. Qed.

(* ======================================== the facts ======================================== *)
Lemma e01h_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; cbn in *; [exact H2 | split; [apply H1 | apply IH; apply H1]]. Qed.
Lemma e01h_atoms_forall : forall E l, Forall (fun a => afact_ok E (fst a) (snd a)) l -> atoms_ok E l.
Proof. intros E l H. induction H as [|[n f] l Hx Hl IH]; cbn; [exact I | split; assumption]. Qed.
Lemma e01h_alias_forall : forall E l, Forall (fun a => sv_denot E (fst a) = sv_denot E (snd a)) l -> alias_ok E l.
Proof. intros E l H. induction H as [|[a b] l Hx Hl IH]; cbn; [exact I | split; assumption]. Qed.
Lemma e01h_div8 : forall p k, p mod 8 = 0 -> 0 <= k < 8 -> (p + k) / 8 = p / 8.
Proof.
intros p k Hp Hk. pose proof (Z.div_mod p 8 ltac:(lia)) as E. rewrite Hp, Z.add_0_r in E.
symmetry. apply (Z.div_unique (p + k) 8 (p / 8) k); [left; lia | lia].
Qed.
Lemma e01h_alias_ok : forall regs p pl k,
  getr regs 25 = w64 p -> getr regs 18 = w64 SHADOW_OFF -> 0 <= p -> p + 8 <= 2 ^ 47 -> p mod 8 = 0 -> (k < 8)%nat ->
  sv_denot (Ereg regs (e01h_extra p pl)) (fst (e01h_alias k)) = sv_denot (Ereg regs (e01h_extra p pl)) (snd (e01h_alias k)).
Proof.
intros regs p pl k H25 H18 Hp0 Hp1 Hp8 Hk. cbn [fst snd e01h_alias]. apply U_inj.
set (E := Ereg regs (e01h_extra p pl)).
assert (E25 : ew E 25 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 25 (Z_to_bv 5 25) eq_refl); exact H25).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 18 (Z_to_bv 5 18) eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 (SHADOW_OFF + p / 8)) by (subst E; exact (e01h_ew32 regs p pl)).
assert (Hd0 : 0 <= p / 8) by (apply Z.div_pos; lia).
assert (Hd1 : p / 8 <= p) by (apply Z.div_le_upper_bound; lia).
rewrite U_SAlu, U_SAlu, U_SLit, (U_atom_off E 25 p (Z.of_nat k) E25 ltac:(lia) ltac:(lia)),
  (U_atom E 18 SHADOW_OFF E18 ltac:(unfold SHADOW_OFF; lia)),
  (U_atom E 32 (SHADOW_OFF + p / 8) E32 ltac:(unfold SHADOW_OFF; lia)).
cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (e01h_div8 p (Z.of_nat k) Hp8 ltac:(lia)).
rewrite (zcanon_id (p / 8)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

(* ======================================== the regions ======================================== *)
Section rg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e01h_rIn_ok : forall E (H : word -> bool) mem p (pl : list byte) (m : nat),
  bv_unsigned (ew E 25) = p -> (forall k, (k < 7)%nat -> ew E (33 + k) = w64 (rh_u8 pl k)) ->
  (m <= length pl)%nat -> (m <= 7)%nat -> 0 <= p -> p + 7 < 2 ^ 64 ->
  garr8 rsegs (mrestrict H mem) p (map (fun b : byte => bv_unsigned b) pl) ->
  region_ok rsegs E (mrestrict H mem) (e01h_rIn m).
Proof.
intros E H mem p pl m E25 Eb Hm Hm7 Hp0 Hp1 Hg.
apply (rtm_ro_region rsegs E H mem 25 p 0 (Z.of_nat m) _ E25); [lia | lia |].
unfold e01h_inchunks. apply Forall_forall. intros ch Hin. apply in_map_iff in Hin as (k & <- & Hk). apply in_seq in Hk.
apply (chunk_ok_val rsegs E (mrestrict H mem) p (Z.of_nat k) 1 (SOff (33 + k) 0) (rh_u8 pl k)).
- exact (e01h_den_off0 E (33 + k) (rh_u8 pl k) (Eb k ltac:(lia)) ltac:(pose proof (e01h_u8_range pl k); lia)).
- change (2 ^ (8 * Z.of_N 1)) with 256. apply e01h_u8_range.
- lia.
- rewrite (e01h_u8_in pl k ltac:(lia)). destruct (Hg k ltac:(rewrite length_map; lia)) as [Hv _]. exact Hv.
Qed.
Lemma e01h_rR_ok : forall E (H : word -> bool) mem R,
  bv_unsigned (ew E 9) = R -> 0 <= R -> R + 0x128 <= 2 ^ 64 ->
  (forall o, 0x38 <= o < 0x128 -> apresent H mem (R + o)) ->
  region_ok rsegs E (mrestrict H mem) e01h_rR.
Proof.
intros E H mem R E9 HR0 HR1 Hp.
apply (rtm_rw_region rsegs E H mem 9 R 0x38 0x128 0x38 0x128 [] E9); [lia | lia | exact Hp | apply Forall_nil].
Qed.
Lemma e01h_rC_ok : forall E (H : word -> bool) mem sa s,
  bv_unsigned (ew E 32) = sa -> aview rsegs H mem sa = Some s -> 0 <= sa < 2 ^ 64 ->
  region_ok rsegs E (mrestrict H mem) (e01h_rC s).
Proof.
intros E H mem sa s E32 Hav Hsa.
apply (rtm_cell_region rsegs E H mem 32 sa s (SLit s) E32 Hav); [reflexivity | lia | lia].
Qed.
Lemma e01h_rK_ok : forall E (W : world rsegs) mem, rom_view rsegs W mem ->
  region_ok rsegs E (mrestrict (w_H W) mem) e01h_rK.
Proof.
intros E W mem HR. exact (img_region_ok_rom E W mem 0x10330 8 HR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)).
Qed.
End rg.

(* refold the environment after an unfolding exposed its body *)
Ltac e01h_foldE E := repeat match goal with |- context [ew ?EE ?n] =>
  lazymatch EE with E => fail | _ => change (ew EE n) with (ew E n) end end.

(* ======================================== the symbolic state at 0x808e4 ======================================== *)
Section en. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e01h_entry : forall (W : world rsegs) regs mem (R p : Z) (pl : list byte) (m : nat) nv s nf,
  getr regs 9 = w64 R -> getr regs 25 = w64 p -> getr regs 18 = w64 SHADOW_OFF ->
  getr regs 21 = sv_denot (Ereg regs (e01h_extra p pl)) nv -> atoms_ok (Ereg regs (e01h_extra p pl)) nf ->
  (m <= 7)%nat -> (m <= length pl)%nat ->
  0x7fff7f800000 <= R -> R mod 32 = 0 -> R + 0x128 <= 2 ^ 47 ->
  (forall o, 0x38 <= o < 0x128 -> apresent (w_H W) mem (R + o)) ->
  garr8 rsegs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) ->
  ((0 < m)%nat -> p mod 16 = 0 /\ 4096 <= p /\ p + Z.of_nat m <= R /\ p + 8 <= 2 ^ 47 /\
     aview rsegs (w_H W) mem (SHADOW_OFF + p / 8) = Some s /\
     ~ (p <= SHADOW_OFF + p / 8 < p + Z.of_nat m) /\ (p + Z.of_nat m <= 0x10330 \/ 0x10338 <= p)) ->
  ((3 <= m)%nat -> rom_view rsegs W mem) ->
  st_ok rsegs (Ereg regs (e01h_extra p pl)) (e01h_ss m nv s nf)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 0x808e4) mem (seg_rom rsegs))).
Proof.
intros W regs mem R p pl m nv s nf H9 H25 H18 H21 Hnf Hm7 Hml HR0 HR32 HR1 Hpres Hg Hp Hrom.
set (E := Ereg regs (e01h_extra p pl)) in *.
assert (E9 : ew E 9 = Z_to_bv 64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl); exact H9).
assert (E25 : ew E 25 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 25 (Z_to_bv 5 25) eq_refl); exact H25).
assert (E32 : ew E 32 = Z_to_bv 64 (SHADOW_OFF + p / 8)) by (subst E; exact (e01h_ew32 regs p pl)).
assert (Eb : forall k, (k < 7)%nat -> ew E (33 + k) = w64 (rh_u8 pl k)) by (intros k Hk; subst E; exact (e01h_ewb regs p pl k Hk)).
assert (Ub9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (HG9 : afact_ok E 9 (mkAF 0x7fff7f800000 0x800000000000 5)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ub9. change (2 ^ 5) with 32. lia. }
assert (HRR : region_ok rsegs E (mrestrict (w_H W) mem) e01h_rR) by (apply (e01h_rR_ok E _ mem R Ub9); [lia | lia | exact Hpres]).
rewrite restrict_mkst_fx. unfold e01h_ss.
destruct m as [|m'].
{ (* no header byte is read *)
  apply (entry_st_ok_full rsegs).
  - apply regs_ok_pin; [apply regs_ok_Ereg | exact e01h_nz21 | exact H21].
  - vm_compute. reflexivity.
  - cbn [e01h_mem]. apply Forall_cons; [exact HRR | apply Forall_nil].
  - cbn [e01h_mem pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok, e01h_facts, e01h_af. cbn [f_atoms f_conds f_alias map seq atoms_ok].
    split; [|split; exact I]. split; [exact HG9|]. first [apply e01h_atoms_app; [exact Hnf | exact I] | exact Hnf]. }
destruct (Hp ltac:(lia)) as (Hp16 & Hp4 & HpR & Hp47 & Hav & Hsh & Himg).
assert (Hp8 : p mod 8 = 0).
{ pose proof (Z.div_mod p 16 ltac:(lia)). pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)). lia. }
assert (Ub25 : bv_unsigned (ew E 25) = p) by (rewrite E25; apply unsigned_lit_small; lia).
assert (Hd0 : 0 <= p / 8) by (apply Z.div_pos; lia).
assert (Hd1 : p / 8 <= p) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.mul_div_le p 8 ltac:(lia)) as Hd2.
assert (Ub32 : bv_unsigned (ew E 32) = SHADOW_OFF + p / 8) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HRI : region_ok rsegs E (mrestrict (w_H W) mem) (e01h_rIn (S m')))
  by (apply (e01h_rIn_ok E _ mem p pl (S m') Ub25 Eb Hml Hm7); first [lia | exact Hg]).
assert (HRC : region_ok rsegs E (mrestrict (w_H W) mem) (e01h_rC s))
  by (apply (e01h_rC_ok E _ mem (SHADOW_OFF + p / 8) s Ub32 Hav); unfold SHADOW_OFF; lia).
assert (HGp : atoms_ok E ((25%nat, mkAF 4096 0x800000000000 4) :: e01h_bytes_af (S m'))).
{ cbn [atoms_ok]. split.
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ub25. change (2 ^ 4) with 16. lia.
  - apply e01h_atoms_forall. apply Forall_forall. intros a Ha. unfold e01h_bytes_af in Ha.
    apply in_map_iff in Ha as (k & <- & Hk). apply in_seq in Hk. cbn [fst snd].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (Eb k ltac:(lia)). unfold w64.
    pose proof (e01h_u8_range pl k). rewrite unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
assert (HAL : alias_ok E (map e01h_alias (seq 0 (S m')))).
{ apply e01h_alias_forall. apply Forall_forall. intros a Ha. apply in_map_iff in Ha as (k & <- & Hk). apply in_seq in Hk.
  subst E. apply e01h_alias_ok; [exact H25 | exact H18 | lia | lia | exact Hp8 | lia]. }
assert (HFA : facts_ok E (e01h_facts (S m') nf)).
{ unfold facts_ok, e01h_facts. cbn [f_atoms f_conds f_alias]. split; [|split; [exact I | exact HAL]].
  unfold e01h_af. cbn [atoms_ok]. split; [exact HG9|]. apply e01h_atoms_app; [exact Hnf | exact HGp]. }
destruct m' as [|[|m'']].
- (* m = 1 *)
  apply (entry_st_ok_full rsegs).
  + apply regs_ok_pin; [apply regs_ok_Ereg | exact e01h_nz21 | exact H21].
  + vm_compute. reflexivity.
  + cbn [e01h_mem]. repeat apply Forall_cons; try apply Forall_nil; assumption.
  + apply pairwise_disjoint_of_extents. cbn [e01h_mem map]. unfold extent_of_region, e01h_rR, e01h_rIn, e01h_rC.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. e01h_foldE E. rewrite Ub9, Ub25, Ub32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF in *. repeat split; lia.
  + exact HFA.
- (* m = 2 *)
  apply (entry_st_ok_full rsegs).
  + apply regs_ok_pin; [apply regs_ok_Ereg | exact e01h_nz21 | exact H21].
  + vm_compute. reflexivity.
  + cbn [e01h_mem]. repeat apply Forall_cons; try apply Forall_nil; assumption.
  + apply pairwise_disjoint_of_extents. cbn [e01h_mem map]. unfold extent_of_region, e01h_rR, e01h_rIn, e01h_rC.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. e01h_foldE E. rewrite Ub9, Ub25, Ub32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF in *. repeat split; lia.
  + exact HFA.
- (* m >= 3 *)
  assert (HRK : region_ok rsegs E (mrestrict (w_H W) mem) e01h_rK) by (apply e01h_rK_ok; apply Hrom; lia).
  apply (entry_st_ok_full rsegs).
  + apply regs_ok_pin; [apply regs_ok_Ereg | exact e01h_nz21 | exact H21].
  + destruct m'' as [|[|[|[|[|m'']]]]]; try (exfalso; lia); vm_compute; reflexivity.
  + cbn [e01h_mem]. repeat apply Forall_cons; try apply Forall_nil; assumption.
  + apply pairwise_disjoint_of_extents. cbn [e01h_mem map]. unfold extent_of_region, e01h_rR, e01h_rIn, e01h_rC, e01h_rK.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. e01h_foldE E. rewrite Ub9, Ub25, Ub32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SHADOW_OFF in *. repeat split; lia.
  + exact HFA.
Qed.

(* the write rights of the regions: the real frame's cells lie in the caller's stack window *)
Lemma e01h_awr : forall E (m : nat) s (STK sp0 R : Z) FP bl0 blc ly own,
  bv_unsigned (ew E 9) = R -> sp0 - STK <= R + 0x38 -> R + 0x128 <= sp0 ->
  awr_ok E (e01h_mem m s) STK sp0 FP bl0 blc ly own.
Proof.
intros E m s STK sp0 R FP bl0 blc ly own Ub9 H1 H2.
destruct m as [|[|[|m]]]; cbn [e01h_mem];
(eapply (awr_ok_cons_stack_off E _ _ STK sp0 FP bl0 blc ly own 9 (R - sp0)); [reflexivity | lia | cbn; lia | cbn; lia |]);
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Qed.
End en.

(* ======================================== reading the last state ======================================== *)
Section rd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e01h_reg_atom : forall E ss ms (H : word -> bool) regs extra (r : bv 5),
  st_ok rsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms H regs extra r HS [HA _] Hr.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r); lia). apply ew_Ereg_reg.
Qed.
Lemma e01h_region_nth : forall E ss ms i r,
  st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma e01h_chunk8 : forall E m base off e v,
  YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 8 e)) -> sv_denot E e = w64 v ->
  val_mem rsegs m (base + off) 8 (v mod 2 ^ 64).
Proof.
intros E m base off e v Hc He k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm.
rewrite Hm. f_equal. injection Hb as <-. rewrite He. unfold byte_of_word, w64.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia.
reflexivity.
Qed.
Lemma e01h_slot : forall E m n b lo hi wlo whi cs od e v,
  region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = w64 v -> val_mem rsegs m (b + od) 8 (v mod 2 ^ 64).
Proof.
intros E m n b lo hi wlo whi cs od e v (_ & _ & _ & Hcs) Hn Hc He.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (e01h_chunk8 E m b od e v Hck He).
Qed.
Lemma e01h_keep_run : forall E rs (H : word -> bool) (m1 m2 : word -> option byte) (Zn : Z -> Prop),
  frame_of E rs (mrestrict H m1) (mrestrict H m2) -> (forall a, in_wrange E rs a -> Zn a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m1 a.
Proof.
intros E rs H m1 m2 Zn HF HW a Ha Hz. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
End rd.

(* ======================================== the state at HD, and the leaf ======================================== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : 0x1f0 + ASTACK <= LLVMF_STK.
Hypothesis HEMPTY : 0 < A_EMPTY < kLowMemEnd.
Hypothesis HSTATIC : rh_static_law rsegs B RLO RHI.
Hypothesis HRELRO : forall a, RLO <= a < RHI -> in_img rsegs a.

(* the read-only view of the entry, kept by a journal whose footprint is empty (boxreg eb_arodata) *)
Lemma e01h_arodata : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k,
  ajournal rsegs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  arodata_okP rsegs RLO RHI B (aview rsegs (w_H W) mem) ->
  arodata_okP rsegs RLO RHI B (aview rsegs (w_H W') mem').
Proof using HRELRO.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (fp_spares_closed [] a sink_closed_nil)].
destruct Hro as [(sg & Hs & _ & Hr) | Hgot]; [exists sg; split; [exact Hs | exact Hr]|].
exact (HRELRO a Hgot).
Qed.

(* the 8 bytes at 0x10330 are image bytes *)
Lemma e01h_k24_img : forall a, 0x10330 <= a < 0x10338 -> in_img rsegs a.
Proof.
intros a Ha.
assert (Hb : existsb (fun sg => (Z.of_N (seg_base sg) <=? 0x10330) && (0x10338 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))
  rsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1, H2.
exists sg. split; [exact Hin | lia].
Qed.

(* the metadata byte of the first granule of a block (p, n), n >= 1: 0 when n >= 8, n when n < 8 *)
Lemma e01h_cell : forall ly S W mem md p n, AR rsegs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n ->
  aview rsegs (w_H W) mem (SHADOW_OFF + p / 8) = Some (e01h_sv n).
Proof.
intros ly S W mem md p n HAR Hin Hn.
destruct (al_shadow _ _ (AR_laws_ok rsegs B) ly S W mem md p n HAR Hin) as [(_ & _ & Hc) _].
assert (Hr : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia). rewrite Hr in Hc.
assert (Hq : 0 < (n + 7) / 8) by (apply Z.div_str_pos; lia).
pose proof (Hc 0 ltac:(lia)) as H0. unfold shadow_of_addr in H0. rewrite Z.add_0_r in H0. rewrite H0.
unfold e01h_sv. f_equal. destruct (Z.ltb_spec n 8) as [Hl|Hl].
- rewrite (Z.div_small n 8) by lia. rewrite Z.ltb_irrefl. apply Z.mod_small. lia.
- assert (1 <= n / 8) by (apply Z.div_le_lower_bound; lia). replace (0 <? n / 8) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(* What the arms use of HD. *)
Lemma e01h_pre : forall hx pos lyc Sc W regs mem md,
  rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
  e01_hd B LLVMF_STK hx pos lyc Sc W regs mem md ->
  ajournal rsegs B LLVMF_STK (spZ (h_regs rsegs hx)) [] (h_ly rsegs hx) (h_S rsegs hx) (h_W rsegs hx)
    (h_mem rsegs hx) (h_md rsegs hx) [(RS_CID, pos)] lyc Sc W mem md 0 /\
  getr regs 9 = w64 (e01_R hx) /\ getr regs 18 = w64 SHADOW_OFF /\ getr regs 21 = w64 (h_n rsegs hx) /\
  getr regs 25 = w64 (h_p rsegs hx) /\
  h_n rsegs hx = Z.of_nat (length (h_pl rsegs hx)) /\ 0 <= h_n rsegs hx < 2 ^ 26 /\
  garr8 rsegs (mrestrict (w_H W) mem) (h_p rsegs hx) (map (fun b : byte => bv_unsigned b) (h_pl rsegs hx)) /\
  0x7fff7f800000 <= e01_R hx /\ e01_R hx mod 32 = 0 /\ e01_R hx + 0x128 <= 2 ^ 47 /\
  spZ (h_regs rsegs hx) - LLVMF_STK <= e01_R hx + 0x38 /\ e01_R hx + 0x128 <= spZ (h_regs rsegs hx) /\
  (forall o, 0x38 <= o < 0x128 -> apresent (w_H W) mem (e01_R hx + o)) /\
  rom_view rsegs W mem /\
  (0 < h_n rsegs hx ->
     h_p rsegs hx mod 16 = 0 /\ 4096 <= h_p rsegs hx /\ h_p rsegs hx + h_n rsegs hx <= e01_R hx /\
     h_p rsegs hx + 8 <= 2 ^ 47 /\
     aview rsegs (w_H W) mem (SHADOW_OFF + h_p rsegs hx / 8) = Some (e01h_sv (h_n rsegs hx)) /\
     ~ (h_p rsegs hx <= SHADOW_OFF + h_p rsegs hx / 8 < h_p rsegs hx + h_n rsegs hx) /\
     (h_p rsegs hx + h_n rsegs hx <= 0x10330 \/ 0x10338 <= h_p rsegs hx)).
Proof using HSTK HSTATIC HRELRO.
intros hx pos lyc Sc W regs mem md Hb Hhd.
destruct Hb as (Hpre & Hra & Ha0 & Ha1 & Hcase & Hlen & Hg0 & Hfr0 & Hev & Hlive & Haro).
destruct Hhd as ((HJ & Hfrs & Hbl & Hkept & Hg) & R2 & R3 & R4 & R8 & R9 & R18 & R20 & R21 & R24 & R25 & R26 & Hfsh).
unfold rh_j in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
destruct Hstk as (HS16 & _ & Hc1 & Hc2 & Hc3 & Hc4 & _).
pose proof ASAN_CEIL_range as ((Hce1 & Hce2) & _). unfold ASAN_CEIL in Hce1, Hce2.
pose proof HSTK as HSTK'. unfold ASTACK in HSTK'.
set (S0 := spZ (h_regs rsegs hx)) in *.
assert (ER : e01_R hx = 32 * ((S0 - 0x1e0) / 32)) by reflexivity.
pose proof (Z.div_mod (S0 - 0x1e0) 32 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (S0 - 0x1e0) 32 ltac:(lia)) as Hmb.
assert (HR32 : e01_R hx mod 32 = 0) by (rewrite ER, Z.mul_comm; apply Z_mod_mult).
assert (HRlo : S0 - 0x200 <= e01_R hx <= S0 - 0x1e0) by lia.
assert (Hlen0 : 0 <= h_n rsegs hx) by (rewrite Hlen; lia).
assert (Haro' : arodata_okP rsegs RLO RHI B (aview rsegs (w_H W) mem)) by exact (e01h_arodata _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Haro).
assert (Hrom : rom_view rsegs W mem).
{ destruct (HSTATIC lyc Sc W mem md HAR Haro') as (_ & _ & _ & _ & _ & HR). exact HR. }
split; [exact HJ|]. split; [exact R9|]. split; [exact R18|]. split; [exact R21|]. split; [exact R25|].
split; [exact Hlen|].
split; [destruct Hcase as [[Hn _] | [Hn _]]; lia|].
split; [exact Hg|].
split; [lia|]. split; [exact HR32|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [intros o Ho; apply Hpres; lia|].
split; [exact Hrom|].
intros Hn0. destruct Hcase as [[Hn _] | [Hn26 Hin]]; [lia|].
assert (Hin' : In (h_p rsegs hx, h_n rsegs hx) (ablocks B lyc Sc)) by (rewrite Hbl; exact Hin).
destruct (al_blocks _ _ (AR_laws_ok rsegs B) lyc Sc W mem md _ _ HAR Hin') as (Hm16 & H4096 & Hpc & Happ & _).
assert (Hr : req_size (h_n rsegs hx) = h_n rsegs hx) by (unfold req_size; destruct (Z.eqb_spec (h_n rsegs hx) 0); lia).
rewrite Hr in Hpc, Happ.
split; [exact Hm16|]. split; [exact H4096|]. split; [lia|]. split; [lia|].
split; [exact (e01h_cell lyc Sc W mem md _ _ HAR Hin' Hn0)|].
split.
{ pose proof (rtm_shadow_not_app (h_p rsegs hx) (h_p rsegs hx) (h_n rsegs hx) ltac:(unfold kHighMemEnd; lia) Happ) as Hs.
  unfold shadow_of_addr in Hs. exact Hs. }
destruct (Z_le_gt_dec (h_p rsegs hx + h_n rsegs hx) 0x10330) as [Hl|Hl]; [left; exact Hl|].
destruct (Z_le_gt_dec 0x10338 (h_p rsegs hx)) as [Hh|Hh]; [right; exact Hh|].
exfalso. set (a := Z.max (h_p rsegs hx) 0x10330).
assert (Ha : h_p rsegs hx <= a < h_p rsegs hx + h_n rsegs hx /\ 0x10330 <= a < 0x10338) by lia.
assert (Hlt : h_p rsegs hx <= a < h_p rsegs hx + req_size (h_n rsegs hx)) by (rewrite Hr; lia).
apply (proj2 (al_client_img _ _ (AR_laws_ok rsegs B) lyc Sc W mem md a HAR
  (or_introl (ex_intro _ (h_p rsegs hx) (ex_intro _ (h_n rsegs hx) (conj Hin' Hlt)))))).
apply e01h_k24_img. lia.
Qed.

(* ---- the leaf ---- *)
(* the run's quantities at CALL: the header values of the input bytes (0 past the end), src / left after the header *)
Definition e01h_env (hx : rh_hcx rsegs) (pos : Z) : rt_renv :=
  RtEnv (e01_S hx) (e01_R hx) (e01_F hx pos) 0 0 0 (rt_len (skipn 7 (h_pl rsegs hx)))
    (rh_u8 (h_pl rsegs hx) 0) (rh_u8 (h_pl rsegs hx) 1) (rh_u8 (h_pl rsegs hx) 2 mod 24) (rh_u8 (h_pl rsegs hx) 3)
    (rh_u8 (h_pl rsegs hx) 4) (rh_u8 (h_pl rsegs hx) 5) (rh_u8 (h_pl rsegs hx) 6)
    (h_p rsegs hx + Z.min 7 (h_n rsegs hx)) (h_n rsegs hx - Z.min 7 (h_n rsegs hx)).

(* what the run's last state gives (regs, mem: the state at HD; regs', mem', md': the state at CALL) *)
Definition e01h_leaf (hx : rh_hcx rsegs) (pos : Z) (lyc : alayout) (Sc : astate) (W : world rsegs)
  (regs : bvmap 5 word) (mem : word -> option byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
rh_j rsegs B LLVMF_STK hx [(RS_CID, pos)] lyc Sc W mem' md' 0 /\
(forall r, In r [2; 3; 4; 8; 9; 18; 20; 24; 26] -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
getr regs' 1 = w64 E01_MALLOC_RA /\ getr regs' 10 = w64 Layout.PP_SIZE /\
getr regs' 19 = w64 0x5000 /\ getr regs' 21 = w64 19744 /\
getr regs' 22 = w64 (h_n rsegs hx - Z.min 7 (h_n rsegs hx)) /\
getr regs' 23 = w64 (rh_u8 (h_pl rsegs hx) 3) /\
getr regs' 25 = w64 (h_p rsegs hx + Z.min 7 (h_n rsegs hx)) /\
val_mem rsegs (mrestrict (w_H W) mem') (e01_R hx + 0x38) 8 (Z.shiftl (rh_u8 (h_pl rsegs hx) 6) 8 mod 2 ^ 64) /\
val_mem rsegs (mrestrict (w_H W) mem') (e01_R hx + 0x40) 8 (rh_u8 (h_pl rsegs hx) 5 mod 2 ^ 64) /\
val_mem rsegs (mrestrict (w_H W) mem') (e01_R hx + 0x48) 8 (Z.shiftl (rh_u8 (h_pl rsegs hx) 4) 8 mod 2 ^ 64) /\
val_mem rsegs (mrestrict (w_H W) mem') (e01_R hx + 0x50) 8 ((rh_u8 (h_pl rsegs hx) 2 mod 24) mod 2 ^ 64) /\
val_mem rsegs (mrestrict (w_H W) mem') (e01_R hx + 0x58) 8 (rh_u8 (h_pl rsegs hx) 0 mod 2 ^ 64) /\
val_mem rsegs (mrestrict (w_H W) mem') (e01_R hx + 0x120) 8 (rh_u8 (h_pl rsegs hx) 1 mod 2 ^ 64) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e01_R hx + 0x38 <= a < e01_R hx + 0x128) ->
 aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a).

Lemma e01h_hb3 : forall e, rt_hb e 3 = q_b3 e. Proof. reflexivity. Qed.
Lemma e01h_hb4 : forall e, rt_hb e 4 = q_b4 e. Proof. reflexivity. Qed.
Lemma e01h_hb5 : forall e, rt_hb e 5 = q_b5 e. Proof. reflexivity. Qed.
Lemma e01h_hb6 : forall e, rt_hb e 6 = q_b6 e. Proof. reflexivity. Qed.

(* the leaf is the call state (RtPgE01D.e01_call_facts) *)
Lemma e01h_call_of : forall hx pos lyc Sc W regs mem md regs' mem' md',
  rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
  e01_hd B LLVMF_STK hx pos lyc Sc W regs mem md ->
  e01h_leaf hx pos lyc Sc W regs mem regs' mem' md' ->
  e01_call_facts B LLVMF_STK hx pos (e01h_env hx pos) (skipn 7 (h_pl rsegs hx)) lyc Sc W regs' mem' md'.
Proof using HSTK HEMPTY.
intros hx pos lyc Sc W regs mem md regs' mem' md' Hb Hhd Hl.
pose proof Hb as (Hpre & Hra & Ha0 & Ha1 & Hcase & Hlen & Hg0 & Hfr0 & Hev & Hlive & Haro).
pose proof Hhd as ((HJ & Hfrs & Hbl & Hkept & Hg) & R2 & R3 & R4 & R8 & R9 & R18 & R20 & R21 & R24 & R25 & R26 & Hfsh).
destruct Hl as (HJ' & Hk & L1 & L10 & L19 & L21 & L22 & L23 & L25 & V38 & V40 & V48 & V50 & V58 & V120 & KE).
unfold rh_j in HJ, HJ'.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof HJ' as (HAR' & _).
destruct Hstk as (HS16 & _ & Hc1 & Hc2 & Hc3 & Hc4 & _).
pose proof ASAN_CEIL_range as ((Hce1 & Hce2) & _). unfold ASAN_CEIL in Hce1, Hce2.
pose proof HSTK as HSTK'. unfold ASTACK in HSTK'.
assert (ES : e01_S hx = spZ (h_regs rsegs hx)) by reflexivity.
assert (ER : e01_R hx = 32 * ((spZ (h_regs rsegs hx) - 0x1e0) / 32)) by reflexivity.
pose proof (Z.div_mod (spZ (h_regs rsegs hx) - 0x1e0) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (spZ (h_regs rsegs hx) - 0x1e0) 32 ltac:(lia)) as Hmb.
assert (HRlo : spZ (h_regs rsegs hx) - 0x200 <= e01_R hx <= spZ (h_regs rsegs hx) - 0x1e0) by lia.
assert (HRc : alloc_ceiling + 0x1000 <= e01_R hx) by lia.
clear Hdm Hmb ER.
(* the frame for locals *)
assert (HinF : In (3, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds rsegs B (AR_laws_ok rsegs B) lyc Sc W mem md 3 pos HAR HinF) as (HF1 & HF2 & _).
assert (EF : frame_addr lyc 3 pos = e01_F hx pos).
{ unfold e01_F, frame_addr, RS_CID. destruct Hly as (_ & _ & _ & _ & _ & HlyF & _). rewrite HlyF. reflexivity. }
rewrite EF in HF1, HF2. change (fs_frame_bytes 3) with 512 in HF2.
assert (Hlen0 : 0 <= h_n rsegs hx) by (rewrite Hlen; lia).
(* the input block *)
assert (HIN : (h_n rsegs hx = 0 /\ h_p rsegs hx = A_EMPTY) \/
  (0 < h_n rsegs hx < 2 ^ 26 /\ In (h_p rsegs hx, h_n rsegs hx) (ablocks B lyc Sc) /\
   In (h_p rsegs hx, h_n rsegs hx) (ablocks B (h_ly rsegs hx) (h_S rsegs hx)) /\
   0 < h_p rsegs hx /\ h_p rsegs hx + h_n rsegs hx <= 2 ^ 63 /\ h_p rsegs hx + h_n rsegs hx <= alloc_ceiling)).
{ destruct Hcase as [[Hn Hp] | [Hn Hin]]; [left; split; assumption | right].
  assert (Hin' : In (h_p rsegs hx, h_n rsegs hx) (ablocks B lyc Sc)) by (rewrite Hbl; exact Hin).
  destruct (rt_block_bounds rsegs B (AR_laws_ok rsegs B) lyc Sc W mem md _ _ HAR Hin') as (Hp0 & _ & Hp63).
  destruct (al_blocks _ _ (AR_laws_ok rsegs B) lyc Sc W mem md _ _ HAR Hin') as (_ & _ & Hpc & _).
  assert (Hr : req_size (h_n rsegs hx) = h_n rsegs hx) by (unfold req_size; destruct (Z.eqb_spec (h_n rsegs hx) 0); lia).
  rewrite Hr in Hpc. repeat split; assumption || lia. }
(* the input bytes avoid the window *)
assert (KEin : forall x, h_p rsegs hx <= x < h_p rsegs hx + h_n rsegs hx ->
  aview rsegs (w_H W) mem' x = aview rsegs (w_H W) mem x).
{ intros x Hx. destruct HIN as [[Hn _] | (_ & _ & _ & Hp0 & _ & Hpc)]; [lia|]. apply KE; lia. }
unfold e01_call_facts.
split; [exact HJ'|]. split; [exact Hfrs|]. split; [exact Hbl|].
split; [unfold rh_geo, e01h_env; cbn [q_S q_R q_F]; repeat split|].
split; [exact L1|].
split; [etransitivity; [apply (Hk 2); cbn; tauto | exact R2]|].
split; [etransitivity; [apply (Hk 3); cbn; tauto | exact R3]|].
split; [etransitivity; [apply (Hk 4); cbn; tauto | exact R4]|].
split; [exact L10|].
split.
{ (* the values of C1's list but a0 *)
  unfold rt_cut. cbn [hi_L1 rate_himg_A tl].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd rt_at rt_xv e01h_env q_S q_R q_F q_fl q_mask q_buflen
    q_b3 q_b4 q_b5 q_b6 q_src q_left]; rewrite ?e01h_hb3, ?e01h_hb4, ?e01h_hb5, ?e01h_hb6;
    cbn [e01h_env q_b3 q_b4 q_b5 q_b6].
  - etransitivity; [apply (Hk 8); cbn; tauto | exact R8].
  - etransitivity; [apply (Hk 9); cbn; tauto | exact R9].
  - etransitivity; [apply (Hk 18); cbn; tauto | exact R18].
  - exact L19.
  - etransitivity; [apply (Hk 20); cbn; tauto | exact R20].
  - exact L21.
  - exact L22.
  - rewrite Z.shiftl_0_r. exact L23.
  - etransitivity; [apply (Hk 24); cbn; tauto | exact R24].
  - exact L25.
  - etransitivity; [apply (Hk 26); cbn; tauto | exact R26].
  - exact V38.
  - exact V40.
  - exact V48.
  - exact V50.
  - exact V58.
  - exact V120. }
split.
{ (* the frame's shadow bytes *)
  cbn [e01h_env q_F]. apply (rtm_fsh_kept rsegs _ _ _ _ _ _ Hfsh). intros i Hi.
  change (Z.of_nat (length rate_A_shA)) with 56 in Hi.
  assert (Hd0 : 0 <= e01_F hx pos / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : e01_F hx pos / 8 <= e01_F hx pos) by (apply Z.div_le_upper_bound; lia).
  pose proof (Z.mul_div_le (e01_F hx pos) 8 ltac:(lia)) as Hd2.
  apply KE; unfold shadow_addr, SHADOW_OFF; lia. }
split.
{ (* the header values' bounds *)
  unfold rt_hdr_ok, e01h_env. cbn [q_fl q_mask q_buflen q_b3 q_b4 q_b5 q_b6].
  pose proof (e01h_u8_range (h_pl rsegs hx) 0). pose proof (e01h_u8_range (h_pl rsegs hx) 1).
  pose proof (Z.mod_pos_bound (rh_u8 (h_pl rsegs hx) 2) 24 ltac:(lia)).
  pose proof (e01h_u8_range (h_pl rsegs hx) 3). pose proof (e01h_u8_range (h_pl rsegs hx) 4).
  pose proof (e01h_u8_range (h_pl rsegs hx) 5). pose proof (e01h_u8_range (h_pl rsegs hx) 6). repeat split; lia. }
split.
{ (* the header's tie to the input *)
  unfold rh_hdr, e01h_env. cbn [q_fl q_mask q_buflen q_b3 q_b4 q_b5 q_b6 q_src q_left q_len]. repeat split. }
split.
{ (* the carried cells *)
  unfold rh_kept, rh_cells in *. rewrite Forall_forall in *. intros f Hf. pose proof (Hkept f Hf) as Hf'.
  apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
  - unfold rh_saves_L in Hf. apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj.
    cbn [fst snd rt_at rt_xv e01_env e01h_env q_S] in Hf' |- *.
    apply (rts_val_kept (w_H W) mem mem'); [|exact Hf']. intros k0 Hk0. change (Z.of_nat 8) with 8 in Hk0.
    apply KE; lia.
  - cbn [fst snd rt_at rt_xv e01_env e01h_env q_F] in Hf' |- *.
    apply (rts_val_kept (w_H W) mem mem'); [|exact Hf']. intros k0 Hk0. change (Z.of_nat 8) with 8 in Hk0.
    apply KE; lia. }
(* the input after the header *)
unfold e01_in, e01h_env. cbn [q_src q_left].
assert (Hlr : h_n rsegs hx - Z.min 7 (h_n rsegs hx) = Z.of_nat (length (skipn 7 (h_pl rsegs hx))))
  by (rewrite length_skipn; rewrite Hlen; lia).
split; [exact Hlr|].
split.
{ destruct (Z_lt_le_dec (h_n rsegs hx) 7) as [Hn7|Hn7].
  - rewrite skipn_all2 by lia. cbn [map]. apply garr8_nil.
  - replace (Z.min 7 (h_n rsegs hx)) with (Z.of_nat 7) by lia. rewrite <- e01h_skipn_map.
    apply e01h_garr8_skip.
    change (rtm_bytes rsegs (w_H W) mem' (h_p rsegs hx) (h_pl rsegs hx)).
    apply (rtm_bytes_kept rsegs (w_H W) mem); [exact Hg|].
    intros x Hx. apply KEin. lia. }
destruct HIN as [[Hn Hp] | (Hn & Hin' & Hin & Hp0 & Hp63 & Hpc)].
- (* no input byte *)
  rewrite Hn, Hp. unfold kLowMemEnd in HEMPTY.
  split; [lia|]. split; [lia|]. split; [unfold amem_range, kLowMemEnd; left; lia|]. left; lia.
- split; [lia|]. split; [lia|].
  split; [apply (amem_range_of_block rsegs B (AR_laws_ok rsegs B) lyc Sc W mem' md' (h_p rsegs hx) (h_n rsegs hx));
          [exact HAR' | exact Hin' | lia |]; unfold req_size; destruct (Z.eqb_spec (h_n rsegs hx) 0); lia|].
  destruct (Z_le_gt_dec (h_n rsegs hx) 7) as [Hn7|Hn7]; [left; lia|].
  right. exists (h_p rsegs hx), (h_n rsegs hx). split; [exact Hin|].
  unfold req_size. destruct (Z.eqb_spec (h_n rsegs hx) 0); lia.
Qed.
End b.
