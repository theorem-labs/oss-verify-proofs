(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths, module names and addresses changed; 1120 of its 1233 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW3a.v at 00820c285b0 for reac-pw/fuzz_headamp image A: module paths changed, rs_ -> hs_, rm_ -> hm_, rl_ -> hd_, role -> headamp; every pc moved to headamp's twin; the input cursor is in s11 (role: R+0xc8) and pp in R+0xf0 (role: s11), so run 1 stores pp at R+0xf0 and run 2 reads it into its own atom 32 (role's atom 27 is s11 = the cursor here); role's real-frame cells R+0x90 / 0x98 / 0xb0 / 0xe8 / 0xf8 moved to R+0xb0 / 0xb8 / 0xd0 / 0x108 / 0x118; the memset step is HPgIntrin.hd_memset_at (role: its own copy); the header cut also carries the cap (s8), the null flag (R+0x40), pp (R+0xf0) and the frame for locals in s10. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgW3a.v, with its module paths changed; 573 of its 644 lines of code are new or changed and 1162 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgE01Hk.v at ba6d82f81177 for image B
   (fuzz_rate.asan-ubsan): image B's pcs, code table and registers (cursor s2, shadow offset s4), the real frame's
   write window R+0x30 .. R+0x150, the six header slots and the registers of the leaf, class-4 frame bounds and the
   harness records of lib/AU/RtPgSegB.v. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgE01Ha.v at ba6d82f81177 for image B
   (fuzz_rate.asan-ubsan): image B's pcs (HD 0x809bc, the malloc trampoline 0x52c0c), registers (cursor s2 = x18,
   shadow offset s4 = x20), the leaf's registers 1 10 18 21 22 23 26 and slots R+0x30 .. R+0x148, and the write
   window R+0x30 .. R+0x150. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgE01H.v at ba6d82f81177 for image B
   (fuzz_rate.asan-ubsan): image B's part statement lib/AU/RtPgE01DB.v e01b_hdr_stmt, pcs and stack bound, and the
   kit and arms of lib/AU/RtPgE01HkB.v and lib/AU/RtPgE01HaB.v. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgE01HkB.v, RtPgE01HaB.v and RtPgE01HB.v at
   48db065d2b9c, in one file for reac-pw/fuzz_role image B (fuzz_role.asan-ubsan): module paths fuzz_rate ->
   fuzz_role; role's one header byte in place of rate's seven (the input-length arms n = 0, n = 1 .. 7 and n >= 8,
   each one engine run; the extra atoms the shadow byte's address and byte 0; the seven reads, the constant at
   0x10330 and its read-only view, buflen's mod 24 and the static law dropped); role B's pcs (HD 0x80270, the malloc
   trampoline 0x524c0, ra 0x802c4), code table (0x80270 .. 0x802c0, the slow block 0x8264c .. 0x82654) and
   registers (n in s2 = x18, the cursor p in s5 = x21, the shadow offset in s11 = x27), the leaf's registers
   1 10 18 20 21 22 and slot R+0x40, the write window R+0x40 .. R+0x48; the records of lib/AU/RPgHarn.v (rh_hdr's
   rh_u8, rl_env) and the kits of lib/AU/RPgMem.v and RPgSteps.v (rm_ / rl_ names); the stack bound 0x210. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): part HDR of segment S_E01
   of the walk of LLVMFuzzerTestOneInput, lib/AU/RPgE01D.v e01b_hdr_stmt: from HD 0x80270 (the frame's header and
   shadow written) to CALL 0x524c0 (the `jal` of malloc(19744) at 0x802c0, ra = 0x802c4): role's one header read
   (fuzz_role.c flags = fuzz_u8, fuzz.h:37-43) after its UBSan pointer-overflow test and behind its instrumented
   1-byte check, the flags byte's spill R+0x40, s4 = the cursor after it, s6 = the bytes left, s5 = 0x5000,
   s2 = a0 = 19744. Proves no function (kind: segment lemma).

   THE CODE (0x80270 .. 0x802c0, 21 words, and the check's slow block 0x8264c .. 0x82654, 3 words):
     0x80270 beqz s2 -> 0x802a8          n = 0: 0x802a8 li s6,0 / 0x802ac sd zero,64(s1) / 0x802b0 mv s4,s5
     0x80274 addi s4,s5,1 / 0x80278 li a0,1 / 0x8027c bltu a0,s4 -> 0x80284   (the pointer-overflow test; its
             fall-through 0x80280 `j 0x82604` reaches the trap word `unimp` 0x82604)
     0x80284 srli a0,s5,3 / add a0,a0,s11 / lb a0,0(a0) / 0x80290 beqz a0 -> 0x80298 / 0x80294 j 0x8264c
             (the instrumented check of the 1-byte load at p)
     0x8264c andi a1,s5,7 / 0x82650 bge a1,a0 -> 0x82658 (the error path: 0x8265c `jal errpath_load1`) /
     0x82654 j 0x80298
     0x80298 lbu a0,0(s5) / 0x8029c sd a0,64(s1) (R+0x40 := fl) / 0x802a0 addi s6,s2,-1 / 0x802a4 j 0x802b4
     0x802b4 lui s5,0x5 / 0x802b8 addiw s2,s5,-736 / 0x802bc mv a0,s2 / 0x802c0 jal 0x524c0 (ra = 0x802c4)

   THE SYMBOLIC STATE AT 0x80270 (e01hb_ss m nv s nf), over the environment Ereg regs (e01hb_extra p pl): atoms
   0 .. 31 the registers, atom 32 the shadow byte's address SHADOW_OFF + p / 8, atom 33 the header byte rh_u8 pl 0.
   s2 (x18) holds nv: the literal n in the arms n = 0 .. 7, its own atom with the fact [8, 2^26 - 1] in the arm
   n >= 8 (nf). The regions: R+0x40 .. R+0x48 as a write window at s1's atom 9; when m = min n 1 = 1, the header
   byte at s5's atom 21 and the shadow byte (the literal s: n when n < 8, else 0) at atom 32, with the alias fact
   (s5 >> 3) + s11 = atom 32. The cursor's atom fact [4096, 2^47] (closed numerals, 16-aligned) lets the engine
   decide the pointer-overflow test `bltu 1, p + 1` 0x8027c by itself (p + 1 > 1: the trap jump 0x80280 is not
   taken) and the slow block's `bge (p & 7), s` 0x82650 (p & 7 = 0 < s: the error path 0x82658 is not taken); the
   literals decide the length test 0x80270 and the shadow test 0x80290, so each arm is one run to 0x524c0.

   THE LEAF (e01hb_leaf): what the run's last state gives, and e01hb_call_of, which turns it into
   RPgE01D.e01b_call_facts at the run's quantities e01hb_env (the flags byte, 0 when n = 0; src = p + min 1 n,
   left = n - min 1 n), from which the continuation e01b_from_call runs. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgHarn RPgE01D RPgMem RPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the code table ======================================== *)
(* 0x80270 .. 0x802c0 (21), the check's slow block 0x8264c .. 0x82654 (3) *)
Definition e01hb_tbl : ctable := build_table rsegs 0x8264c 3 (build_table rsegs 0x80270 21 TEmpty).
Lemma e01hb_tbl_ok : table_ok rsegs e01hb_tbl.
Proof. apply build_table_ok; [lia|]. apply build_table_ok0. lia. Qed.
Definition E01HB_Bx : sv := SOff 27 0.
Definition E01HB_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* ======================================== the symbolic state ======================================== *)
Definition e01hb_alias (k : nat) : sv * sv :=
  (SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 (Z.of_nat k)) (SLit 3)) (SOff 27 0), SOff 32 0).
Definition e01hb_inchunks (m : nat) : list YP09.chunk :=
  map (fun k => YP09.mkChunk (Z.of_nat k) (CVal 1 (SOff (33 + k) 0))) (seq 0 m).
Definition e01hb_rIn (m : nat) : YP09.region := YP09.mkRegion (Some 21%nat) 0 (Z.of_nat m) 0 0 (e01hb_inchunks m).
Definition e01hb_rC (s : Z) : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit s))].
Definition e01hb_rR : YP09.region := YP09.mkRegion (Some 9%nat) 0x40 0x48 0x40 0x48 [].
Definition e01hb_mem (m : nat) (s : Z) : smem :=
  match m with
  | O => [e01hb_rR]
  | _ => [e01hb_rR; e01hb_rIn m; e01hb_rC s]
  end.
Definition e01hb_bytes_af (m : nat) : list (nat * afact) := map (fun k => ((33 + k)%nat, mkAF 0 255 0)) (seq 0 m).
Definition e01hb_af (m : nat) (nf : list (nat * afact)) : list (nat * afact) :=
  (9%nat, mkAF 0x7fff7f800000 0x800000000000 5) :: nf ++
  match m with O => [] | _ => (21%nat, mkAF 4096 0x800000000000 4) :: e01hb_bytes_af m end.
Definition e01hb_facts (m : nat) (nf : list (nat * afact)) : facts :=
  mkFacts (e01hb_af m nf) [] (map e01hb_alias (seq 0 m)).
Definition e01hb_ss (m : nat) (nv : sv) (s : Z) (nf : list (nat * afact)) : sstate :=
  mkSS 0x80270 (sr_set sr_atoms (18%bv : bv 5) nv) (e01hb_mem m s) None (e01hb_facts m nf).
Definition e01hb_extra (p : Z) (pl : list byte) : list word :=
  [w64 (SHADOW_OFF + p / 8); w64 (rh_u8 pl 0)].
(* the shadow byte of p's first granule (n >= 1) *)
Definition e01hb_sv (n : Z) : Z := if n <? 8 then n else 0.

(* ======================================== bytes ======================================== *)
Lemma e01hb_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as Hb. exact Hb. Qed.
Lemma e01hb_u8_range : forall pl i, 0 <= rh_u8 pl i < 256.
Proof. intros pl i. unfold rh_u8. destruct (nth_error pl i) as [b|]; [apply e01hb_byte_range | lia]. Qed.
Lemma e01hb_u8_out : forall pl i, (length pl <= i)%nat -> rh_u8 pl i = 0.
Proof. intros pl i H. unfold rh_u8. rewrite (proj2 (nth_error_None pl i) H). reflexivity. Qed.
Lemma e01hb_u8_in : forall pl i, (i < length pl)%nat ->
  rh_u8 pl i = nth i (map (fun b : byte => bv_unsigned b) pl) 0.
Proof.
intros pl i H. unfold rh_u8. rewrite (nth_error_nth' pl (Z_to_bv 8 0) H).
pose proof (map_nth (fun b : byte => bv_unsigned b) pl (Z_to_bv 8 0) i) as M. cbv beta in M.
rewrite <- M. reflexivity.
Qed.
Lemma e01hb_nth_skipn : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
intros l k. revert l. induction k as [|k IH]; intros l j; [reflexivity|].
destruct l as [|x l]; cbn; [destruct j; reflexivity | apply IH].
Qed.
Lemma e01hb_skipn_map : forall (f : byte -> Z) (l : list byte) k, skipn k (map f l) = map f (skipn k l).
Proof.
intros f l k. revert l. induction k as [|k IH]; intros l; [reflexivity|]. destruct l as [|x l]; [reflexivity|]. apply IH.
Qed.
Lemma e01hb_garr8_skip : forall m p (l : list Z) k,
  garr8 rsegs m p l -> garr8 rsegs m (p + Z.of_nat k) (skipn k l).
Proof.
intros m p l k H j Hj. rewrite length_skipn in Hj. rewrite e01hb_nth_skipn.
replace (p + Z.of_nat k + Z.of_nat j) with (p + Z.of_nat (k + j)) by lia. apply H. lia.
Qed.

(* ======================================== the environment and the values ======================================== *)
Lemma e01hb_ew32 : forall regs p pl, ew (Ereg regs (e01hb_extra p pl)) 32 = w64 (SHADOW_OFF + p / 8).
Proof. intros regs p pl. exact (ew_Ereg_extra regs (e01hb_extra p pl) 0). Qed.
Lemma e01hb_ewb : forall regs p pl k, (k < 1)%nat -> ew (Ereg regs (e01hb_extra p pl)) (33 + k) = w64 (rh_u8 pl k).
Proof.
intros regs p pl k Hk. change (33 + k)%nat with (32 + S k)%nat. rewrite ew_Ereg_extra.
destruct k as [|k]; [reflexivity | lia].
Qed.
Lemma e01hb_den_off : forall E (k : nat) v c, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k c) = w64 (v + c).
Proof. intros E k v c Hk Hv. cbn [sv_denot]. rewrite Hk. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity. Qed.
Lemma e01hb_den_off0 : forall E (k : nat) v, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k 0) = w64 v.
Proof. intros E k v Hk Hv. rewrite (e01hb_den_off E k v 0 Hk Hv). rewrite Z.add_0_r. reflexivity. Qed.
Lemma e01hb_nz18 : (18%bv : bv 5) <> 0%bv.
Proof. intros Hc. apply (f_equal (@bv_unsigned 5)) in Hc. vm_compute in Hc. discriminate Hc. Qed.

(* ======================================== the facts ======================================== *)
Lemma e01hb_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; cbn in *; [exact H2 | split; [apply H1 | apply IH; apply H1]]. Qed.
Lemma e01hb_atoms_forall : forall E l, Forall (fun a => afact_ok E (fst a) (snd a)) l -> atoms_ok E l.
Proof. intros E l H. induction H as [|[n f] l Hx Hl IH]; cbn; [exact I | split; assumption]. Qed.
Lemma e01hb_alias_forall : forall E l, Forall (fun a => sv_denot E (fst a) = sv_denot E (snd a)) l -> alias_ok E l.
Proof. intros E l H. induction H as [|[a b] l Hx Hl IH]; cbn; [exact I | split; assumption]. Qed.
Lemma e01hb_div8 : forall p k, p mod 8 = 0 -> 0 <= k < 8 -> (p + k) / 8 = p / 8.
Proof.
intros p k Hp Hk. pose proof (Z.div_mod p 8 ltac:(lia)) as E. rewrite Hp, Z.add_0_r in E.
symmetry. apply (Z.div_unique (p + k) 8 (p / 8) k); [left; lia | lia].
Qed.
Lemma e01hb_alias_ok : forall regs p pl k,
  getr regs 21 = w64 p -> getr regs 27 = w64 SHADOW_OFF -> 0 <= p -> p + 8 <= 2 ^ 47 -> p mod 8 = 0 -> (k < 8)%nat ->
  sv_denot (Ereg regs (e01hb_extra p pl)) (fst (e01hb_alias k)) = sv_denot (Ereg regs (e01hb_extra p pl)) (snd (e01hb_alias k)).
Proof.
intros regs p pl k H21 H27 Hp0 Hp1 Hp8 Hk. cbn [fst snd e01hb_alias]. apply U_inj.
set (E := Ereg regs (e01hb_extra p pl)).
assert (E21 : ew E 21 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 21 (Z_to_bv 5 21) eq_refl); exact H21).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 27 (Z_to_bv 5 27) eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 (SHADOW_OFF + p / 8)) by (subst E; exact (e01hb_ew32 regs p pl)).
assert (Hd0 : 0 <= p / 8) by (apply Z.div_pos; lia).
assert (Hd1 : p / 8 <= p) by (apply Z.div_le_upper_bound; lia).
rewrite U_SAlu, U_SAlu, U_SLit, (U_atom_off E 21 p (Z.of_nat k) E21 ltac:(lia) ltac:(lia)),
  (U_atom E 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)),
  (U_atom E 32 (SHADOW_OFF + p / 8) E32 ltac:(unfold SHADOW_OFF; lia)).
cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (e01hb_div8 p (Z.of_nat k) Hp8 ltac:(lia)).
rewrite (zcanon_id (p / 8)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

(* ======================================== the regions ======================================== *)
Section rg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e01hb_rIn_ok : forall E (H : word -> bool) mem p (pl : list byte) (m : nat),
  bv_unsigned (ew E 21) = p -> (forall k, (k < 1)%nat -> ew E (33 + k) = w64 (rh_u8 pl k)) ->
  (m <= length pl)%nat -> (m <= 1)%nat -> 0 <= p -> p + 1 < 2 ^ 64 ->
  garr8 rsegs (mrestrict H mem) p (map (fun b : byte => bv_unsigned b) pl) ->
  region_ok rsegs E (mrestrict H mem) (e01hb_rIn m).
Proof.
intros E H mem p pl m E21 Eb Hm Hm1 Hp0 Hp1 Hg.
apply (rm_ro_region rsegs E H mem 21 p 0 (Z.of_nat m) _ E21); [lia | lia |].
unfold e01hb_inchunks. apply Forall_forall. intros ch Hin. apply in_map_iff in Hin as (k & <- & Hk). apply in_seq in Hk.
apply (chunk_ok_val rsegs E (mrestrict H mem) p (Z.of_nat k) 1 (SOff (33 + k) 0) (rh_u8 pl k)).
- exact (e01hb_den_off0 E (33 + k) (rh_u8 pl k) (Eb k ltac:(lia)) ltac:(pose proof (e01hb_u8_range pl k); lia)).
- change (2 ^ (8 * Z.of_N 1)) with 256. apply e01hb_u8_range.
- lia.
- rewrite (e01hb_u8_in pl k ltac:(lia)). destruct (Hg k ltac:(rewrite length_map; lia)) as [Hv _]. exact Hv.
Qed.
Lemma e01hb_rR_ok : forall E (H : word -> bool) mem R,
  bv_unsigned (ew E 9) = R -> 0 <= R -> R + 0x48 <= 2 ^ 64 ->
  (forall o, 0x40 <= o < 0x48 -> apresent H mem (R + o)) ->
  region_ok rsegs E (mrestrict H mem) e01hb_rR.
Proof.
intros E H mem R E9 HR0 HR1 Hp.
apply (rm_rw_region rsegs E H mem 9 R 0x40 0x48 0x40 0x48 [] E9); [lia | lia | exact Hp | apply Forall_nil].
Qed.
Lemma e01hb_rC_ok : forall E (H : word -> bool) mem sa s,
  bv_unsigned (ew E 32) = sa -> aview rsegs H mem sa = Some s -> 0 <= sa < 2 ^ 64 ->
  region_ok rsegs E (mrestrict H mem) (e01hb_rC s).
Proof.
intros E H mem sa s E32 Hav Hsa.
apply (rm_cell_region rsegs E H mem 32 sa s (SLit s) E32 Hav); [reflexivity | lia | lia].
Qed.
End rg.

(* refold the environment after an unfolding exposed its body *)
Ltac e01hb_foldE E := repeat match goal with |- context [ew ?EE ?n] =>
  lazymatch EE with E => fail | _ => change (ew EE n) with (ew E n) end end.

(* ======================================== the symbolic state at 0x80270 ======================================== *)
Section en. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e01hb_entry : forall (W : world rsegs) regs mem (R p : Z) (pl : list byte) (m : nat) nv s nf,
  getr regs 9 = w64 R -> getr regs 21 = w64 p -> getr regs 27 = w64 SHADOW_OFF ->
  getr regs 18 = sv_denot (Ereg regs (e01hb_extra p pl)) nv -> atoms_ok (Ereg regs (e01hb_extra p pl)) nf ->
  (m <= 1)%nat -> (m <= length pl)%nat ->
  0x7fff7f800000 <= R -> R mod 32 = 0 -> R + 0x48 <= 2 ^ 47 ->
  (forall o, 0x40 <= o < 0x48 -> apresent (w_H W) mem (R + o)) ->
  garr8 rsegs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) ->
  ((0 < m)%nat -> p mod 16 = 0 /\ 4096 <= p /\ p + Z.of_nat m <= R /\ p + 8 <= 2 ^ 47 /\
     aview rsegs (w_H W) mem (SHADOW_OFF + p / 8) = Some s /\
     ~ (p <= SHADOW_OFF + p / 8 < p + Z.of_nat m)) ->
  st_ok rsegs (Ereg regs (e01hb_extra p pl)) (e01hb_ss m nv s nf)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 0x80270) mem (seg_rom rsegs))).
Proof.
intros W regs mem R p pl m nv s nf H9 H21 H27 H18 Hnf Hm1 Hml HR0 HR32 HR1 Hpres Hg Hp.
set (E := Ereg regs (e01hb_extra p pl)) in *.
assert (E9 : ew E 9 = Z_to_bv 64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl); exact H9).
assert (E21 : ew E 21 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 21 (Z_to_bv 5 21) eq_refl); exact H21).
assert (E32 : ew E 32 = Z_to_bv 64 (SHADOW_OFF + p / 8)) by (subst E; exact (e01hb_ew32 regs p pl)).
assert (Eb : forall k, (k < 1)%nat -> ew E (33 + k) = w64 (rh_u8 pl k)) by (intros k Hk; subst E; exact (e01hb_ewb regs p pl k Hk)).
assert (Ub9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (HG9 : afact_ok E 9 (mkAF 0x7fff7f800000 0x800000000000 5)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ub9. change (2 ^ 5) with 32. lia. }
assert (HRR : region_ok rsegs E (mrestrict (w_H W) mem) e01hb_rR) by (apply (e01hb_rR_ok E _ mem R Ub9); [lia | lia | exact Hpres]).
rewrite restrict_mkst_fx. unfold e01hb_ss.
destruct m as [|m'].
{ (* no header byte is read *)
  apply (entry_st_ok_full rsegs).
  - apply regs_ok_pin; [apply regs_ok_Ereg | exact e01hb_nz18 | exact H18].
  - vm_compute. reflexivity.
  - cbn [e01hb_mem]. apply Forall_cons; [exact HRR | apply Forall_nil].
  - cbn [e01hb_mem pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok, e01hb_facts, e01hb_af. cbn [f_atoms f_conds f_alias map seq atoms_ok].
    split; [|split; exact I]. split; [exact HG9|]. first [apply e01hb_atoms_app; [exact Hnf | exact I] | exact Hnf]. }
destruct m' as [|m'']; [|exfalso; lia].
destruct (Hp ltac:(lia)) as (Hp16 & Hp4 & HpR & Hp47 & Hav & Hsh).
assert (Hp8 : p mod 8 = 0).
{ pose proof (Z.div_mod p 16 ltac:(lia)). pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)). lia. }
assert (Ub21 : bv_unsigned (ew E 21) = p) by (rewrite E21; apply unsigned_lit_small; lia).
assert (Hd0 : 0 <= p / 8) by (apply Z.div_pos; lia).
assert (Hd1 : p / 8 <= p) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.mul_div_le p 8 ltac:(lia)) as Hd2.
assert (Ub32 : bv_unsigned (ew E 32) = SHADOW_OFF + p / 8) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HRI : region_ok rsegs E (mrestrict (w_H W) mem) (e01hb_rIn 1))
  by (apply (e01hb_rIn_ok E _ mem p pl 1 Ub21 Eb Hml Hm1); first [lia | exact Hg]).
assert (HRC : region_ok rsegs E (mrestrict (w_H W) mem) (e01hb_rC s))
  by (apply (e01hb_rC_ok E _ mem (SHADOW_OFF + p / 8) s Ub32 Hav); unfold SHADOW_OFF; lia).
assert (HGp : atoms_ok E ((21%nat, mkAF 4096 0x800000000000 4) :: e01hb_bytes_af 1)).
{ cbn [atoms_ok]. split.
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ub21. change (2 ^ 4) with 16. lia.
  - apply e01hb_atoms_forall. apply Forall_forall. intros a Ha. unfold e01hb_bytes_af in Ha.
    apply in_map_iff in Ha as (k & <- & Hk). apply in_seq in Hk. cbn [fst snd].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (Eb k ltac:(lia)). unfold w64.
    pose proof (e01hb_u8_range pl k). rewrite unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
assert (HAL : alias_ok E (map e01hb_alias (seq 0 1))).
{ apply e01hb_alias_forall. apply Forall_forall. intros a Ha. apply in_map_iff in Ha as (k & <- & Hk). apply in_seq in Hk.
  subst E. apply e01hb_alias_ok; [exact H21 | exact H27 | lia | lia | exact Hp8 | lia]. }
assert (HFA : facts_ok E (e01hb_facts 1 nf)).
{ unfold facts_ok, e01hb_facts. cbn [f_atoms f_conds f_alias]. split; [|split; [exact I | exact HAL]].
  unfold e01hb_af. cbn [atoms_ok]. split; [exact HG9|]. apply e01hb_atoms_app; [exact Hnf | exact HGp]. }
apply (entry_st_ok_full rsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | exact e01hb_nz18 | exact H18].
- vm_compute. reflexivity.
- cbn [e01hb_mem]. repeat apply Forall_cons; try apply Forall_nil; assumption.
- apply pairwise_disjoint_of_extents. cbn [e01hb_mem map]. unfold extent_of_region, e01hb_rR, e01hb_rIn, e01hb_rC.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. e01hb_foldE E. rewrite Ub9, Ub21, Ub32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF in *. repeat split; lia.
- exact HFA.
Qed.

(* the write rights of the regions: the real frame's cell lies in the caller's stack window *)
Lemma e01hb_awr : forall E (m : nat) s (STK sp0 R : Z) FP bl0 blc ly own,
  bv_unsigned (ew E 9) = R -> sp0 - STK <= R + 0x40 -> R + 0x48 <= sp0 ->
  awr_ok E (e01hb_mem m s) STK sp0 FP bl0 blc ly own.
Proof.
intros E m s STK sp0 R FP bl0 blc ly own Ub9 H1 H2.
destruct m as [|m]; cbn [e01hb_mem];
(eapply (awr_ok_cons_stack_off E _ _ STK sp0 FP bl0 blc ly own 9 (R - sp0)); [reflexivity | lia | cbn; lia | cbn; lia |]);
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Qed.
End en.

(* ======================================== reading the last state ======================================== *)
Section rd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e01hb_reg_atom : forall E ss ms (H : word -> bool) regs extra (r : bv 5),
  st_ok rsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms H regs extra r HS [HA _] Hr.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r); lia). apply ew_Ereg_reg.
Qed.
Lemma e01hb_region_nth : forall E ss ms i r,
  st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma e01hb_chunk8 : forall E m base off e v,
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
Lemma e01hb_slot : forall E m n b lo hi wlo whi cs od e v,
  region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = w64 v -> val_mem rsegs m (b + od) 8 (v mod 2 ^ 64).
Proof.
intros E m n b lo hi wlo whi cs od e v (_ & _ & _ & Hcs) Hn Hc He.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (e01hb_chunk8 E m b od e v Hck He).
Qed.
Lemma e01hb_keep_run : forall E rs (H : word -> bool) (m1 m2 : word -> option byte) (Zn : Z -> Prop),
  frame_of E rs (mrestrict H m1) (mrestrict H m2) -> (forall a, in_wrange E rs a -> Zn a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m1 a.
Proof.
intros E rs H m1 m2 Zn HF HW a Ha Hz. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
End rd.

(* ---- reading the last state ---- *)
Ltac e01hb_in := repeat (first [left; reflexivity | right]).
(* a register of the last state: its symbolic value, computed *)
Ltac e01hb_sr HS :=
  lazymatch type of HS with st_ok ?segs ?E ?s (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E s ms _ HS);
    lazymatch goal with |- sv_denot _ (sr_get ?l ?r) = _ =>
      let e := eval vm_compute in (sr_get l r) in change (sr_get l r) with e end
  end.
(* the value of a symbolic term the run left (atom 21 = p, atom 18 = n, atom 33 = the header byte) *)
Ltac e01hb_v En Ep Hpr Hnr :=
  lazymatch goal with
  | |- sv_denot _ (SLit _) = _ =>
      cbn [sv_denot]; unfold w64; f_equal; first [reflexivity | lia | (rewrite e01hb_u8_out by lia; first [reflexivity | lia])]
  | |- sv_denot ?EE (SOff 21 ?c) = _ => rewrite (e01hb_den_off EE 21 _ c Ep Hpr); unfold w64; f_equal; lia
  | |- sv_denot ?EE (SOff 18 ?c) = _ => rewrite (e01hb_den_off EE 18 _ c En Hnr); unfold w64; f_equal; lia
  | |- sv_denot ?EE (SOff ?k 0) = _ =>
      apply e01hb_den_off0; [apply e01hb_ewb; lia | match goal with |- 0 <= rh_u8 ?pl ?i < _ => pose proof (e01hb_u8_range pl i); lia end]
  end.
(* a window of the start regions lies in R+0x40 .. R+0x48 *)
Ltac e01hb_kwr Ub9 :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  cbn [ss_mem e01hb_ss e01hb_mem In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val e01hb_rR e01hb_rIn e01hb_rC] in Hb;
     first [rewrite Ub9 in Hb | idtac]; lia | ]);
  destruct Hr.

(* ======================================== the state at HD, the leaf, the arms and the part ======================================== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : 0x210 + ASTACK <= LLVMF_STK.
Hypothesis HAE : 0 < A_EMPTY < kLowMemEnd.

(* a block live in an AR state: 0 < p, p 16-aligned, p + n <= 2^63 (fuzz_rate's RtPgBase rt_block_bounds) *)
Lemma e01hb_block_bounds : forall ly S W mem md p n, AR rsegs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  0 < p /\ p mod 16 = 0 /\ p + n <= 2 ^ 63.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ (AR_laws_ok rsegs B) ly S W mem md p n HAR Hin) as (H16 & H4096 & Hc & _).
pose proof (@YM05.alloc_ceiling_lt rc) as Hc0. unfold req_size in Hc.
destruct (Z.eqb_spec n 0); lia.
Qed.

(* the shadow byte of the first granule of a block (p, n), n >= 1: 0 when n >= 8, n when n < 8 *)
Lemma e01hb_cell : forall ly S W mem md p n, AR rsegs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n ->
  aview rsegs (w_H W) mem (SHADOW_OFF + p / 8) = Some (e01hb_sv n).
Proof.
intros ly S W mem md p n HAR Hin Hn.
destruct (al_shadow _ _ (AR_laws_ok rsegs B) ly S W mem md p n HAR Hin) as [(_ & _ & Hc) _].
assert (Hr : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia). rewrite Hr in Hc.
assert (Hq : 0 < (n + 7) / 8) by (apply Z.div_str_pos; lia).
pose proof (Hc 0 ltac:(lia)) as H0. unfold shadow_of_addr in H0. rewrite Z.add_0_r in H0. rewrite H0.
unfold e01hb_sv. f_equal. destruct (Z.ltb_spec n 8) as [Hl|Hl].
- rewrite (Z.div_small n 8) by lia. rewrite Z.ltb_irrefl. apply Z.mod_small. lia.
- assert (1 <= n / 8) by (apply Z.div_le_lower_bound; lia). replace (0 <? n / 8) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(* What the arms use of HD. *)
Lemma e01hb_pre : forall hx pos lyc Sc W regs mem md,
  rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
  e01b_hd B LLVMF_STK hx pos lyc Sc W regs mem md ->
  ajournal rsegs B LLVMF_STK (spZ (h_regs rsegs hx)) [] (h_ly rsegs hx) (h_S rsegs hx) (h_W rsegs hx)
    (h_mem rsegs hx) (h_md rsegs hx) [(RH_CID, pos)] lyc Sc W mem md 0 /\
  getr regs 9 = w64 (e01b_R hx) /\ getr regs 27 = w64 SHADOW_OFF /\ getr regs 18 = w64 (h_n rsegs hx) /\
  getr regs 21 = w64 (h_p rsegs hx) /\
  h_n rsegs hx = Z.of_nat (length (h_pl rsegs hx)) /\ 0 <= h_n rsegs hx < 2 ^ 26 /\
  garr8 rsegs (mrestrict (w_H W) mem) (h_p rsegs hx) (map (fun b : byte => bv_unsigned b) (h_pl rsegs hx)) /\
  0x7fff7f800000 <= e01b_R hx /\ e01b_R hx mod 32 = 0 /\ e01b_R hx + 0x48 <= 2 ^ 47 /\
  spZ (h_regs rsegs hx) - LLVMF_STK <= e01b_R hx + 0x40 /\ e01b_R hx + 0x48 <= spZ (h_regs rsegs hx) /\
  (forall o, 0x40 <= o < 0x48 -> apresent (w_H W) mem (e01b_R hx + o)) /\
  (0 < h_n rsegs hx ->
     h_p rsegs hx mod 16 = 0 /\ 4096 <= h_p rsegs hx /\ h_p rsegs hx + h_n rsegs hx <= e01b_R hx /\
     h_p rsegs hx + 8 <= 2 ^ 47 /\
     aview rsegs (w_H W) mem (SHADOW_OFF + h_p rsegs hx / 8) = Some (e01hb_sv (h_n rsegs hx)) /\
     ~ (h_p rsegs hx <= SHADOW_OFF + h_p rsegs hx / 8 < h_p rsegs hx + h_n rsegs hx)).
Proof using HSTK.
intros hx pos lyc Sc W regs mem md Hb Hhd.
destruct Hb as (Hpre & Hra & Ha0 & Ha1 & Hcase & Hlen & Hg0 & Hfr0 & Hev & Hlive & Haro).
destruct Hhd as ((HJ & Hfrs & Hbl & Hkept & Hg) & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R23 & R26 & R27 & Hfsh).
unfold rh_j in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
destruct Hstk as (HS16 & _ & Hc1 & Hc2 & Hc3 & Hc4 & _).
pose proof ASAN_CEIL_range as ((Hce1 & Hce2) & _). unfold ASAN_CEIL in Hce1, Hce2.
pose proof HSTK as HSTK'. unfold ASTACK in HSTK'.
set (S0 := spZ (h_regs rsegs hx)) in *.
assert (ER : e01b_R hx = 32 * ((S0 - 0x200) / 32)) by reflexivity.
pose proof (Z.div_mod (S0 - 0x200) 32 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (S0 - 0x200) 32 ltac:(lia)) as Hmb.
assert (HR32 : e01b_R hx mod 32 = 0) by (rewrite ER, Z.mul_comm; apply Z_mod_mult).
assert (HRlo : S0 - 0x220 <= e01b_R hx <= S0 - 0x200) by lia.
assert (Hlen0 : 0 <= h_n rsegs hx) by (rewrite Hlen; lia).
split; [exact HJ|]. split; [exact R9|]. split; [exact R27|]. split; [exact R18|]. split; [exact R21|].
split; [exact Hlen|].
split; [destruct Hcase as [[Hn _] | [Hn _]]; lia|].
split; [exact Hg|].
split; [lia|]. split; [exact HR32|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [intros o Ho; apply Hpres; lia|].
intros Hn0. destruct Hcase as [[Hn _] | [Hn26 Hin]]; [lia|].
assert (Hin' : In (h_p rsegs hx, h_n rsegs hx) (ablocks B lyc Sc)) by (rewrite Hbl; exact Hin).
destruct (al_blocks _ _ (AR_laws_ok rsegs B) lyc Sc W mem md _ _ HAR Hin') as (Hm16 & H4096 & Hpc & Happ & _).
assert (Hr : req_size (h_n rsegs hx) = h_n rsegs hx) by (unfold req_size; destruct (Z.eqb_spec (h_n rsegs hx) 0); lia).
rewrite Hr in Hpc, Happ.
split; [exact Hm16|]. split; [exact H4096|]. split; [lia|]. split; [lia|].
split; [exact (e01hb_cell lyc Sc W mem md _ _ HAR Hin' Hn0)|].
pose proof (rm_shadow_not_app (h_p rsegs hx) (h_p rsegs hx) (h_n rsegs hx) ltac:(unfold kHighMemEnd; lia) Happ) as Hs.
unfold shadow_of_addr in Hs. exact Hs.
Qed.

(* ---- the leaf ---- *)
(* the run's quantities at CALL: the flags byte (0 past the input's end), src / left after it, the pod length *)
Definition e01hb_env (hx : rh_hcx rsegs) (pos : Z) : rl_env :=
  RLEnv (e01b_S hx) (e01b_R hx) (e01b_F hx pos) 0 0 (rl_len (skipn 1 (h_pl rsegs hx)))
    (rh_u8 (h_pl rsegs hx) 0) (h_p rsegs hx + Z.min 1 (h_n rsegs hx)) (h_n rsegs hx - Z.min 1 (h_n rsegs hx)).

(* what the run's last state gives (regs, mem: the state at HD; regs', mem', md': the state at CALL) *)
Definition e01hb_leaf (hx : rh_hcx rsegs) (pos : Z) (lyc : alayout) (Sc : astate) (W : world rsegs)
  (regs : bvmap 5 word) (mem : word -> option byte)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
rh_j rsegs B LLVMF_STK hx [(RH_CID, pos)] lyc Sc W mem' md' 0 /\
(forall r, In r [2; 3; 4; 8; 9; 19; 23; 26; 27] -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
getr regs' 1 = w64 E01B_MALLOC_RA /\ getr regs' 10 = w64 Layout.PP_SIZE /\
getr regs' 18 = w64 19744 /\
getr regs' 20 = w64 (h_p rsegs hx + Z.min 1 (h_n rsegs hx)) /\
getr regs' 21 = w64 0x5000 /\
getr regs' 22 = w64 (h_n rsegs hx - Z.min 1 (h_n rsegs hx)) /\
val_mem rsegs (mrestrict (w_H W) mem') (e01b_R hx + 0x40) 8 (rh_u8 (h_pl rsegs hx) 0 mod 2 ^ 64) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e01b_R hx + 0x40 <= a < e01b_R hx + 0x48) ->
 aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a).

(* the leaf is the call state (RPgE01D.e01b_call_facts) *)
Lemma e01hb_call_of : forall hx pos lyc Sc W regs mem md regs' mem' md',
  rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
  e01b_hd B LLVMF_STK hx pos lyc Sc W regs mem md ->
  e01hb_leaf hx pos lyc Sc W regs mem regs' mem' md' ->
  e01b_call_facts B LLVMF_STK hx pos (e01hb_env hx pos) (skipn 1 (h_pl rsegs hx)) lyc Sc W regs' mem' md'.
Proof using HSTK HAE.
intros hx pos lyc Sc W regs mem md regs' mem' md' Hb Hhd Hl.
pose proof Hb as (Hpre & Hra & Ha0 & Ha1 & Hcase & Hlen & Hg0 & Hfr0 & Hev & Hlive & Haro).
pose proof Hhd as ((HJ & Hfrs & Hbl & Hkept & Hg) & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R23 & R26 & R27 & Hfsh).
destruct Hl as (HJ' & Hk & L1 & L10 & L18 & L20 & L21 & L22 & V40 & KE).
unfold rh_j in HJ, HJ'.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof HJ' as (HAR' & _).
destruct Hstk as (HS16 & _ & Hc1 & Hc2 & Hc3 & Hc4 & _).
pose proof ASAN_CEIL_range as ((Hce1 & Hce2) & _). unfold ASAN_CEIL in Hce1, Hce2.
pose proof HSTK as HSTK'. unfold ASTACK in HSTK'.
assert (ES : e01b_S hx = spZ (h_regs rsegs hx)) by reflexivity.
assert (ER : e01b_R hx = 32 * ((spZ (h_regs rsegs hx) - 0x200) / 32)) by reflexivity.
pose proof (Z.div_mod (spZ (h_regs rsegs hx) - 0x200) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (spZ (h_regs rsegs hx) - 0x200) 32 ltac:(lia)) as Hmb.
assert (HRlo : spZ (h_regs rsegs hx) - 0x220 <= e01b_R hx <= spZ (h_regs rsegs hx) - 0x200) by lia.
assert (HRc : alloc_ceiling + 0x1000 <= e01b_R hx) by lia.
clear Hdm Hmb ER.
(* the frame for locals *)
assert (HinF : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds rsegs B (AR_laws_ok rsegs B) lyc Sc W mem md 4 pos HAR HinF) as (HF1 & HF2 & _).
assert (EF : frame_addr lyc 4 pos = e01b_F hx pos).
{ unfold e01b_F, frame_addr, RH_CID. destruct Hly as (_ & _ & _ & _ & _ & HlyF & _). rewrite HlyF. reflexivity. }
rewrite EF in HF1, HF2. change (fs_frame_bytes 4) with 1024 in HF2.
assert (Hlen0 : 0 <= h_n rsegs hx) by (rewrite Hlen; lia).
(* the input block *)
assert (HIN : (h_n rsegs hx = 0 /\ h_p rsegs hx = A_EMPTY) \/
  (0 < h_n rsegs hx < 2 ^ 26 /\ In (h_p rsegs hx, h_n rsegs hx) (ablocks B lyc Sc) /\
   In (h_p rsegs hx, h_n rsegs hx) (ablocks B (h_ly rsegs hx) (h_S rsegs hx)) /\
   0 < h_p rsegs hx /\ h_p rsegs hx + h_n rsegs hx <= 2 ^ 63 /\ h_p rsegs hx + h_n rsegs hx <= alloc_ceiling)).
{ destruct Hcase as [[Hn Hp] | [Hn Hin]]; [left; split; assumption | right].
  assert (Hin' : In (h_p rsegs hx, h_n rsegs hx) (ablocks B lyc Sc)) by (rewrite Hbl; exact Hin).
  destruct (e01hb_block_bounds lyc Sc W mem md _ _ HAR Hin') as (Hp0 & _ & Hp63).
  destruct (al_blocks _ _ (AR_laws_ok rsegs B) lyc Sc W mem md _ _ HAR Hin') as (_ & _ & Hpc & _).
  assert (Hr : req_size (h_n rsegs hx) = h_n rsegs hx) by (unfold req_size; destruct (Z.eqb_spec (h_n rsegs hx) 0); lia).
  rewrite Hr in Hpc. repeat split; assumption || lia. }
(* the input bytes avoid the window *)
assert (KEin : forall x, h_p rsegs hx <= x < h_p rsegs hx + h_n rsegs hx ->
  aview rsegs (w_H W) mem' x = aview rsegs (w_H W) mem x).
{ intros x Hx. destruct HIN as [[Hn _] | (_ & _ & _ & Hp0 & _ & Hpc)]; [lia|]. apply KE; lia. }
unfold e01b_call_facts.
split; [exact HJ'|]. split; [exact Hfrs|]. split; [exact Hbl|].
split; [unfold rh_geo, e01hb_env; cbn [e_S e_R e_F]; repeat split|].
split; [exact L1|].
split; [etransitivity; [apply (Hk 2); cbn; tauto | exact R2]|].
split; [etransitivity; [apply (Hk 3); cbn; tauto | exact R3]|].
split; [etransitivity; [apply (Hk 4); cbn; tauto | exact R4]|].
split; [exact L10|].
split.
{ (* the values of C1's list but a0 *)
  unfold rl_cut. cbn [hi_L1 role_himg_B tl].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd rl_at rl_xv e01hb_env e_S e_R e_F e_fl e_src e_left].
  - etransitivity; [apply (Hk 8); cbn; tauto | exact R8].
  - etransitivity; [apply (Hk 9); cbn; tauto | exact R9].
  - exact L18.
  - etransitivity; [apply (Hk 19); cbn; tauto | exact R19].
  - exact L20.
  - exact L21.
  - exact L22.
  - etransitivity; [apply (Hk 23); cbn; tauto | exact R23].
  - etransitivity; [apply (Hk 26); cbn; tauto | exact R26].
  - etransitivity; [apply (Hk 27); cbn; tauto | exact R27].
  - exact V40. }
split.
{ (* the frame's shadow bytes *)
  cbn [e01hb_env e_F]. apply (rm_fsh_kept rsegs _ _ _ _ _ _ Hfsh). intros i Hi.
  assert (HP0 : Z.of_nat (length (hi_shA role_himg_B)) = 88) by (vm_compute; reflexivity). rewrite HP0 in Hi.
  assert (Hd0 : 0 <= e01b_F hx pos / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : e01b_F hx pos / 8 <= e01b_F hx pos) by (apply Z.div_le_upper_bound; lia).
  pose proof (Z.mul_div_le (e01b_F hx pos) 8 ltac:(lia)) as Hd2.
  apply KE; unfold shadow_addr, SHADOW_OFF; lia. }
split.
{ (* the flags byte's bound *)
  cbn [e01hb_env e_fl]. apply e01hb_u8_range. }
split.
{ (* the header's tie to the input *)
  unfold rh_hdr, e01hb_env. cbn [e_fl e_src e_left e_len]. repeat split. }
split.
{ (* the carried cells *)
  unfold rh_kept, rh_cells in *. rewrite Forall_forall in *. intros f Hf. pose proof (Hkept f Hf) as Hf'.
  apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
  - unfold rh_saves_L in Hf. apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj.
    cbn [fst snd rl_at rl_xv e01b_env e01hb_env e_S] in Hf' |- *.
    apply (rl_val_kept (w_H W) mem mem'); [|exact Hf']. intros k0 Hk0. change (Z.of_nat 8) with 8 in Hk0.
    apply KE; lia.
  - cbn [fst snd rl_at rl_xv e01b_env e01hb_env e_F] in Hf' |- *.
    apply (rl_val_kept (w_H W) mem mem'); [|exact Hf']. intros k0 Hk0. change (Z.of_nat 8) with 8 in Hk0.
    apply KE; lia. }
(* the input after the flags byte *)
unfold e01b_in, e01hb_env. cbn [e_src e_left].
assert (Hlr : h_n rsegs hx - Z.min 1 (h_n rsegs hx) = Z.of_nat (length (skipn 1 (h_pl rsegs hx))))
  by (rewrite length_skipn; rewrite Hlen; lia).
split; [exact Hlr|].
split.
{ destruct (Z_lt_le_dec (h_n rsegs hx) 1) as [Hn1|Hn1].
  - rewrite skipn_all2 by lia. cbn [map]. apply garr8_nil.
  - replace (Z.min 1 (h_n rsegs hx)) with (Z.of_nat 1) by lia. rewrite <- e01hb_skipn_map.
    apply e01hb_garr8_skip.
    change (rm_bytes rsegs (w_H W) mem' (h_p rsegs hx) (h_pl rsegs hx)).
    apply (rm_bytes_kept rsegs (w_H W) mem); [exact Hg|].
    intros x Hx. apply KEin. lia. }
destruct HIN as [[Hn Hp] | (Hn & Hin' & Hin & Hp0 & Hp63 & Hpc)].
- (* no input byte *)
  rewrite Hn, Hp. unfold kLowMemEnd in HAE.
  split; [lia|]. split; [lia|]. split; [unfold amem_range, kLowMemEnd; left; lia|]. left; lia.
- split; [lia|]. split; [lia|].
  split; [apply (amem_range_of_block rsegs B (AR_laws_ok rsegs B) lyc Sc W mem' md' (h_p rsegs hx) (h_n rsegs hx));
          [exact HAR' | exact Hin' | lia |]; unfold req_size; destruct (Z.eqb_spec (h_n rsegs hx) 0); lia|].
  destruct (Z_le_gt_dec (h_n rsegs hx) 1) as [Hn1|Hn1]; [left; lia|].
  right. exists (h_p rsegs hx), (h_n rsegs hx). split; [exact Hin|].
  unfold req_size. destruct (Z.eqb_spec (h_n rsegs hx) 0); lia.
Qed.

(* the leaf: e01hb_leaf off the last state *)
Ltac e01hb_leaf_tac hx Ub9 En Ep Hpr Hnr :=
  lazymatch goal with HS : st_ok _ ?EE ?ssf (restrict (w_H ?Wx) ?msx), HFr : frame_of _ _ (mrestrict _ ?m1) _ |- _ =>
  let HR0 := fresh "HR0" in
  let r := eval vm_compute in (nth_error (ss_mem ssf) 0) in
  lazymatch r with Some ?rr => pose proof (e01hb_region_nth _ ssf _ 0 rr HS ltac:(vm_compute; reflexivity)) as HR0 end;
  cbn [ms_mem restrict] in HR0;
  unfold e01hb_leaf;
  split; [assumption|];
  split;
  [ let q := fresh "q" in let Hq := fresh "Hq" in intros q Hq; cbn [In] in Hq;
    repeat (destruct Hq as [<- | Hq]; [eapply (e01hb_reg_atom _ _ msx (w_H Wx) _ _ _ HS (env_agree_refl 32 _));
                                       vm_compute; reflexivity|]);
    destruct Hq |];
  do 6 (split; [e01hb_sr HS; e01hb_v En Ep Hpr Hnr|]);
  split; [eapply (e01hb_slot _ _ 9 _ _ _ _ _ _ _ _ _ HR0 Ub9); [e01hb_in | e01hb_v En Ep Hpr Hnr]|];
  let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
  intros a Ha Hn;
  apply (e01hb_keep_run _ _ (w_H Wx) m1 (ms_mem msx) (fun a => e01b_R hx + 0x40 <= a < e01b_R hx + 0x48) HFr);
  [e01hb_kwr Ub9 | exact Ha | exact Hn]
  end.

(* one arm: from HD to the `jal` of malloc's target, given the input length's case P *)
Definition e01hb_arm_stmt (P : Z -> Prop) : Prop :=
  forall hx pos lyc Sc W regs mem md (Q : world rsegs -> config -> Prop),
  rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
  e01b_hd B LLVMF_STK hx pos lyc Sc W regs mem md -> P (h_n rsegs hx) ->
  (forall regs' mem' md', e01hb_leaf hx pos lyc Sc W regs mem regs' mem' md' ->
     SRr rsegs W (cfg_at rsegs E01B_MALLOC regs' mem' md') Q) ->
  SRr rsegs W (cfg_at rsegs E01B_HD regs mem md) Q.

(* the whole proof of one arm: m bytes read, s2 = nv, the shadow byte s, the extra atom facts nf *)
Local Ltac e01hb_arm m nv s nf nvtac nftac svtac :=
  intros hx pos lyc Sc W regs mem md Q Hb Hhd HN K;
  pose proof Hb as (_ & _ & _ & _ & Hcase & _);
  destruct (e01hb_pre hx pos lyc Sc W regs mem md Hb Hhd)
    as (HJ & H9 & H27 & H18 & H21 & Hlen & Hn26 & Hg & HR0 & HR32 & HR1 & HRs & HRS & Hpres & Hp);
  pose proof (AR_laws_ok rsegs B) as LAWS; pose proof rl_segs_low as Hsegs; pose proof rl_wx as Hwx;
  assert (Hpr : 0 <= h_p rsegs hx < 2 ^ 64)
    by (destruct Hcase as [[Hn0 Hp0] | [Hn0 _]];
        [rewrite Hp0; unfold kLowMemEnd in HAE; lia | destruct (Hp ltac:(lia)) as (_ & ? & _ & ? & _); lia]);
  assert (Hnr : 0 <= h_n rsegs hx < 2 ^ 64) by lia;
  assert (E9 : ew (Ereg regs (e01hb_extra (h_p rsegs hx) (h_pl rsegs hx))) 9 = w64 (e01b_R hx))
    by (rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl); exact H9);
  assert (E21 : ew (Ereg regs (e01hb_extra (h_p rsegs hx) (h_pl rsegs hx))) 21 = w64 (h_p rsegs hx))
    by (rewrite (ew_Ereg_nat regs _ 21 (Z_to_bv 5 21) eq_refl); exact H21);
  assert (E18 : ew (Ereg regs (e01hb_extra (h_p rsegs hx) (h_pl rsegs hx))) 18 = w64 (h_n rsegs hx))
    by (rewrite (ew_Ereg_nat regs _ 18 (Z_to_bv 5 18) eq_refl); exact H18);
  assert (Ub9 : bv_unsigned (ew (Ereg regs (e01hb_extra (h_p rsegs hx) (h_pl rsegs hx))) 9) = e01b_R hx)
    by (rewrite E9; apply unsigned_lit_small; lia);
  assert (HS : st_ok rsegs (Ereg regs (e01hb_extra (h_p rsegs hx) (h_pl rsegs hx))) (e01hb_ss m nv s nf)
     (restrict (w_H W) (mkst regs (Z_to_bv 64 0x80270) mem (seg_rom rsegs))));
  [ apply (e01hb_entry W regs mem (e01b_R hx) (h_p rsegs hx) (h_pl rsegs hx) m nv s nf H9 H21 H27);
    [ nvtac | nftac | lia | lia | exact HR0 | exact HR32 | exact HR1 | exact Hpres | exact Hg
    | let Hm0 := fresh "Hm0" in intros Hm0;
      let A1 := fresh "A" in let A2 := fresh "A" in let A3 := fresh "A" in let A4 := fresh "A" in
      let A5 := fresh "A" in let A6 := fresh "A" in
      destruct (Hp ltac:(lia)) as (A1 & A2 & A3 & A4 & A5 & A6);
      split; [exact A1|]; split; [exact A2|]; split; [lia|]; split; [exact A4|];
      split; [rewrite A5; f_equal; svtac|]; lia ]
  | ];
  unfold cfg_at, E01B_HD; change (w64 0x80270) with (Z_to_bv 64 0x80270);
  assert (SHOK : sh_ok rsegs E01HB_Bx [] (Ereg regs (e01hb_extra (h_p rsegs hx) (h_pl rsegs hx))) (mrestrict (w_H W) mem))
    by (unfold sh_ok; apply Forall_nil);
  aj_run_to_tok e01hb_tbl_ok HS HJ SHOK E01HB_span 0x524c0;
  [ apply (e01hb_awr _ m s LLVMF_STK (spZ (h_regs rsegs hx)) (e01b_R hx) _ _ _ _ _ Ub9); lia
  | let Ems := fresh "Ems" in
    lazymatch goal with HS' : st_ok _ _ _ (restrict _ ?ms) |- _ =>
      pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS' eq_refl) as Ems; cbn [ss_pc] in Ems; rewrite Ems end;
    apply K;
    e01hb_leaf_tac hx Ub9 E18 E21 Hpr Hnr ].

Local Ltac e01hb_nv_lit :=
  idtac; match goal with H : _ = w64 (h_n _ _), HN : h_n _ _ = _ |- _ => etransitivity; [exact H | rewrite HN; reflexivity] end.
Local Ltac e01hb_nv_atom :=
  idtac; match goal with E : ew _ 18 = w64 (h_n _ _), H : getr _ _ = w64 (h_n _ _) |- _ =>
    cbn [sv_denot]; rewrite E; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; exact H end.
Local Ltac e01hb_nf_big :=
  idtac; match goal with E : ew _ 18 = w64 (h_n _ _) |- _ =>
    cbn [atoms_ok]; split; [|exact I]; unfold afact_ok; cbn [af_lo af_hi af_al2];
    rewrite E; unfold w64; rewrite unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia end.
Local Ltac e01hb_sv_lit := idtac; match goal with HN : h_n _ _ = _ |- _ => unfold e01hb_sv; rewrite HN; reflexivity end.
Local Ltac e01hb_sv_big :=
  idtac; match goal with HN : 8 <= h_n ?a ?b |- _ =>
    unfold e01hb_sv; replace (h_n a b <? 8) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity end.

(* THE ARMS (n the input length): n = 0 (`beqz s2` 0x80270 -> 0x802a8, R+0x40 := 0), n = 1 .. 7 (the read of byte 0
   after the pointer-overflow test, the shadow byte n, so the slow block 0x8264c is taken and passes: p & 7 = 0 < n),
   n >= 8 (the read of byte 0, the shadow byte 0). s2 is the literal n when n < 8, its own atom when n >= 8. *)
Lemma e01hb_arm0 : e01hb_arm_stmt (fun n => n = 0).
Proof using HSTK HAE.
e01hb_arm 0%nat (SLit 0) 0 (@nil (nat * afact)) e01hb_nv_lit ltac:(exact I) e01hb_sv_lit.
Qed.
Lemma e01hb_arm1 : e01hb_arm_stmt (fun n => n = 1).
Proof using HSTK HAE.
e01hb_arm 1%nat (SLit 1) 1 (@nil (nat * afact)) e01hb_nv_lit ltac:(exact I) e01hb_sv_lit.
Qed.
Lemma e01hb_arm2 : e01hb_arm_stmt (fun n => n = 2).
Proof using HSTK HAE.
e01hb_arm 1%nat (SLit 2) 2 (@nil (nat * afact)) e01hb_nv_lit ltac:(exact I) e01hb_sv_lit.
Qed.
Lemma e01hb_arm3 : e01hb_arm_stmt (fun n => n = 3).
Proof using HSTK HAE.
e01hb_arm 1%nat (SLit 3) 3 (@nil (nat * afact)) e01hb_nv_lit ltac:(exact I) e01hb_sv_lit.
Qed.
Lemma e01hb_arm4 : e01hb_arm_stmt (fun n => n = 4).
Proof using HSTK HAE.
e01hb_arm 1%nat (SLit 4) 4 (@nil (nat * afact)) e01hb_nv_lit ltac:(exact I) e01hb_sv_lit.
Qed.
Lemma e01hb_arm5 : e01hb_arm_stmt (fun n => n = 5).
Proof using HSTK HAE.
e01hb_arm 1%nat (SLit 5) 5 (@nil (nat * afact)) e01hb_nv_lit ltac:(exact I) e01hb_sv_lit.
Qed.
Lemma e01hb_arm6 : e01hb_arm_stmt (fun n => n = 6).
Proof using HSTK HAE.
e01hb_arm 1%nat (SLit 6) 6 (@nil (nat * afact)) e01hb_nv_lit ltac:(exact I) e01hb_sv_lit.
Qed.
Lemma e01hb_arm7 : e01hb_arm_stmt (fun n => n = 7).
Proof using HSTK HAE.
e01hb_arm 1%nat (SLit 7) 7 (@nil (nat * afact)) e01hb_nv_lit ltac:(exact I) e01hb_sv_lit.
Qed.
Lemma e01hb_arm8 : e01hb_arm_stmt (fun n => 8 <= n).
Proof using HSTK HAE.
e01hb_arm 1%nat (SOff 18 0) 0 [(18%nat, mkAF 8 67108863 0)] e01hb_nv_atom e01hb_nf_big e01hb_sv_big.
Qed.

(* ---- the part ---- *)
Theorem e01b_hdr_ok : e01b_hdr_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof using HSTK HAE.
intros hx POST Hb HK pos lyc Sc W regs mem md Hhd.
assert (Hn0 : 0 <= h_n rsegs hx) by (pose proof Hb as (_ & _ & _ & _ & _ & Hlen & _); rewrite Hlen; lia).
(* each arm's leaf is the call state, from which the continuation runs *)
assert (KC : forall regs' mem' md', e01hb_leaf hx pos lyc Sc W regs mem regs' mem' md' ->
  SRr rsegs W (cfg_at rsegs E01B_MALLOC regs' mem' md') POST).
{ intros regs' mem' md' HL. apply (HK pos (e01hb_env hx pos) (skipn 1 (h_pl rsegs hx)) lyc Sc W regs' mem' md').
  exact (e01hb_call_of hx pos lyc Sc W regs mem md regs' mem' md' Hb Hhd HL). }
(* the input-length arms (n = 1 .. 7 and n >= 8 apart: the input's first shadow byte is n, resp. 0) *)
assert (Hc : h_n rsegs hx = 0 \/ h_n rsegs hx = 1 \/ h_n rsegs hx = 2 \/ h_n rsegs hx = 3 \/ h_n rsegs hx = 4 \/
             h_n rsegs hx = 5 \/ h_n rsegs hx = 6 \/ h_n rsegs hx = 7 \/ 8 <= h_n rsegs hx) by lia.
destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
- exact (e01hb_arm0 hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm1 hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm2 hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm3 hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm4 hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm5 hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm6 hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm7 hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
- exact (e01hb_arm8 hx pos lyc Sc W regs mem md POST Hb Hhd H KC).
Qed.
End b.
