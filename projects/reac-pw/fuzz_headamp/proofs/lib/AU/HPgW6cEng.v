(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at (lines 2155-2206) restated for image A's code with the callee's same_but_materialized kept as same_io in the post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Call.v at 888d1ffb4c3 for reac-pw/fuzz_headamp image A: module paths changed, w_intrin_at renamed hd_intrin_at, role's RPgCfgChanges.cfg_segs_low replaced by HPgSteps.img_segs_low over headamp's segments; the two instances hd_memset_at / hd_memcpy_at are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgIntrin.v; 642 of its 685 lines of code are new or changed and 90 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the shared layer of the walk piece W6c of LLVMFuzzerTestOneInput (0x80c40), ent_build's cases 6, 7 and 8
   (pod.h:340-366) from their switch entries to the join J 0x82618. Proves no function (kind: segment lemma): the
   model side of the three cases, the engine's entry state at a case entry and the plumbing the case walks share.

   THE THREE CASES (image B; listing of the twin).
     case 6 0x81f08  (pod.h:342-347)  t := fuzz_u8; ty := t6[t & 3] (.rodata 0x21120, a registered global of 16
                    bytes); e62.type := ty; sz := 8, 4 or 0 (the compiler folds t6 into `beq a2,2` and `seqz (a2-3)`);
                    then the take block 0x8227c: e62.size := sz, n := min(sz, left), memcpy(e62.body, cur, n).
     case 7 0x81d88  (pod.h:352-356)  t := fuzz_u8; e62.type := t mod 21 (the multiply by 0x87); s := fuzz_u8;
                    sz := s mod 12 (the multiply by [R+0x10] = 0x15555556); the take block 0x8244c.
     case 8 0x81f5c  (pod.h:360-365)  t := fuzz_u8; ty := t8[t & 3] (.rodata 0x21140); e62.type := ty; t & 3 = 3
                    (STRING) or nothing left: size 0; else s := fuzz_u8, size s & 3; the fill block 0x822b0:
                    e62.size := size, memset(e62.body, 0, size).
   Each read of the input is fuzz.h:42's: the UBSan pointer test `addi a0,s2,1; bltu a6,a0` (its `unimp` arm needs
   1 <u cur + 1, which 1 <= cur gives) and the instrumented check of s2 (NE-SLOW, its slow block in 0x827a4 ..
   0x8288c). The table loads carry the instrumented check of the element (NE-SLOW) and a UBSan pointer test whose
   index is at most 12.

   THE REGISTERS AND CELLS AT A CASE ENTRY (image B, measured; the cut hsu_cut_D of lib/AU/HPgSeg.v gives them):
   s1 = x9 = R, s11 = x27 = SHADOW_OFF, a7 = x17 = cur - 1 (the kind byte's address), s2 = x18 = cur (the cursor
   after the kind byte), t1 = x6 = |r| + 1, s4 = x20 = |r|, a6 = x16 = 1; sp = x2 = R, gp, tp. The real-frame cells
   read: [R+0x10] = 0x15555556, [R+0x118] = F + 0x218 (&e62.body), [R+0x130] = F + 0x210 (&e62),
   [R+0x138] = pp + Layout.OFF_LEN, [R+0x148] = pp. e62 = F + 0x210 holds 104 zero bytes and its 13 shadow granules
   are 0 (the pattern hsu_PJ).

   THE ENGINE'S STATE AT A CASE ENTRY. The registers are their own atoms (Ereg regs extra) with s2 pinned to a7 + 1,
   t1 to s4 + 1 and a6 to 1, so the cursor is one atom (17) and what is left another (20). Four extra atoms:
   32 = F, 33 = t and 34 = s (the first two input bytes after the kind byte, 0 past the end), 35 = pp. Regions:
     w6c_RS     R's cells [R+0x10, R+0x150), read only;
     w6c_RE     e62's header [F+0x210, F+0x218), two zero words; the type word [F+0x210, F+0x214) written;
     w6c_RI m   the m input bytes after the kind byte (read only), based at a7;
     w6c_RT tb  a 16-byte table of .rodata at tb, image bytes (added after the input region is dropped: the input
                may lie anywhere the contract allows, the image included, so the two are never in one state).
   The shadow base of the engine's tokens is s11 (atom 27, fact [K, K]); e62's header window is covered by the
   shadow entry w6c_SH. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition W6C_D6 : Z := 0x81f08.      (* case 6's switch entry (the table's entry 6) *)
Definition W6C_D7 : Z := 0x81d88.      (* case 7's switch entry *)
Definition W6C_D8 : Z := 0x81f5c.      (* case 8's switch entry *)
Definition W6C_T6 : Z := 0x8227c.      (* case 6's take block: `sw a2,4(s4)` *)
Definition W6C_T7 : Z := 0x8244c.      (* case 7's take block: `sw a2,4(s4)` (also its two short arms' join) *)
Definition W6C_F8 : Z := 0x822b0.      (* case 8's fill block: `ld s5,0x130(s1)` *)
Definition W6C_CPY : Z := 0x51d8c.     (* __asan_memcpy, the `jal` target at 0x82474 *)
Definition W6C_RCPY : Z := 0x82478.    (* after it *)
Definition W6C_SET : Z := 0x52228.     (* __asan_memset, the `jal` target at 0x822c0 *)
Definition W6C_RSET : Z := 0x822c4.    (* after it *)
Definition W6C_J : Z := 0x82618.       (* the join J (bi_J) *)
Definition W6C_TB6 : Z := 0x21120.     (* ent_build.t, case 6's t[] (4 x 4 bytes) *)
Definition W6C_TB8 : Z := 0x21140.     (* ent_build.t.11, case 8's t[] *)
Definition w6c_pc (c : Z) : Z := if c =? 6 then W6C_D6 else if c =? 7 then W6C_D7 else W6C_D8.

(* ======================================== the code table ========================================
   Every instruction word of [0x81888, 0x828d0): the cases' fast paths and the slow blocks of their checks. *)
Definition W6C_TLO : Z := 0x81888.
Definition W6C_TN : nat := 1042.
Definition w6c_tbl : ctable := Eval vm_compute in build_table rsegs W6C_TLO W6C_TN TEmpty.
Lemma w6c_tbl_ok : table_ok rsegs w6c_tbl.
Proof.
pose proof (build_table_ok0 rsegs W6C_TN W6C_TLO ltac:(unfold W6C_TLO; lia)) as H.
assert (E : build_table rsegs W6C_TLO W6C_TN TEmpty = w6c_tbl) by (vm_compute; reflexivity).
rewrite E in H. exact H.
Qed.

(* ======================================== the model ======================================== *)
(* the pod of one turn whose kind byte reads c *)
Definition w6c_ent (c : Z) (r : list byte) : ent * list byte := ent_build (Z_to_bv 8 c :: r).

(* cases 6, 7 and 8 read the kind byte only through kind % 10 *)
Lemma w6c_build_kind : forall rr kd r, (kd, r) = Cursor.fuzz_u8 rr -> rr <> [] -> In (kd mod 10) [6; 7; 8] ->
ent_build rr = w6c_ent (kd mod 10) r.
Proof.
intros rr kd r Hf Hne Hin. destruct rr as [|b r0]; [contradiction|].
cbn [Cursor.fuzz_u8] in Hf. injection Hf as Hkd Hr. subst r0.
unfold w6c_ent, ent_build. cbn [Cursor.fuzz_u8]. rewrite <- Hkd.
cbv [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; rewrite <- E; reflexivity.
Qed.

(* the 104 bytes of a pod whose body is p padded with zeros to sz bytes *)
Lemma w6c_ent_mem_pad : forall ty sz (p : list byte), (length p <= Z.to_nat sz)%nat -> (Z.to_nat sz <= 96)%nat ->
ent_mem (Ent ty sz (p ++ zeros (Z.to_nat sz - length p))) = le32 ty ++ le32 sz ++ p ++ zeros (96 - length p).
Proof.
intros ty sz p H1 H2. unfold ent_mem. cbn [e_type e_size e_body]. do 2 f_equal.
rewrite length_app, length_zeros, <- app_assoc. f_equal. unfold zeros. rewrite <- repeat_app. f_equal. lia.
Qed.

(* case 6: t, then the type t6[t & 3] and the size (8, 8, 4, 0 for LONG, DOUBLE, ID, NONE) *)
Definition W6C_SZ6 : list Z := [8; 8; 4; 0].
Definition w6c6_ty (j : Z) : Z := nth (Z.to_nat j) t6 0.
Definition w6c6_sz (j : Z) : Z := nth (Z.to_nat j) W6C_SZ6 0.
Lemma w6c6_sz_range : forall j, 0 <= j < 4 -> 0 <= w6c6_sz j <= 8.
Proof.
intros j Hj. assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
destruct Hc as [->|[->|[->| ->]]]; cbv; split; discriminate.
Qed.
Lemma w6c6_model : forall r, w6c_ent 6 r =
(let j := fst (Cursor.fuzz_u8 r) mod 4 in let r1 := snd (Cursor.fuzz_u8 r) in
 let p := firstn (Z.to_nat (w6c6_sz j)) r1 in
 (Ent (w6c6_ty j) (w6c6_sz j) (p ++ zeros (Z.to_nat (w6c6_sz j) - length p)), skipn (Z.to_nat (w6c6_sz j)) r1)).
Proof.
intros r. unfold w6c_ent, ent_build. cbn [Cursor.fuzz_u8].
replace (Z.to_nat (bv_unsigned (Z_to_bv 8 6) mod 10)) with 6%nat by reflexivity. cbv iota beta.
destruct (Cursor.fuzz_u8 r) as [t r1] eqn:Ef. cbn [fst snd].
pose proof (Cursor.fuzz_u8_range r) as Ht. rewrite Ef in Ht. cbn [fst] in Ht.
unfold fuzz_take, w6c6_ty, w6c6_sz.
assert (Hc : t mod 4 = 0 \/ t mod 4 = 1 \/ t mod 4 = 2 \/ t mod 4 = 3) by (pose proof (Z.mod_pos_bound t 4); lia).
destruct Hc as [E|[E|[E|E]]]; rewrite E; reflexivity.
Qed.

(* case 7: the type t mod 21 and the size s mod 12 *)
Lemma w6c7_model : forall r, w6c_ent 7 r =
(let t := fst (Cursor.fuzz_u8 r) in let r1 := snd (Cursor.fuzz_u8 r) in
 let s := fst (Cursor.fuzz_u8 r1) in let r2 := snd (Cursor.fuzz_u8 r1) in
 let p := firstn (Z.to_nat (s mod 12)) r2 in
 (Ent (t mod 21) (s mod 12) (p ++ zeros (Z.to_nat (s mod 12) - length p)), skipn (Z.to_nat (s mod 12)) r2)).
Proof.
intros r. unfold w6c_ent, ent_build. cbn [Cursor.fuzz_u8].
replace (Z.to_nat (bv_unsigned (Z_to_bv 8 7) mod 10)) with 7%nat by reflexivity. cbv iota beta.
destruct (Cursor.fuzz_u8 r) as [t r1]. cbn [fst snd]. destruct (Cursor.fuzz_u8 r1) as [s r2]. cbn [fst snd].
unfold fuzz_take. reflexivity.
Qed.

(* case 8: the type t8[t & 3]; STRING (t & 3 = 3) has no body, the others a zero body of s & 3 bytes *)
Definition w6c8_ty (j : Z) : Z := nth (Z.to_nat j) t8 0.
Lemma w6c8_model : forall r, w6c_ent 8 r =
(let j := fst (Cursor.fuzz_u8 r) mod 4 in let r1 := snd (Cursor.fuzz_u8 r) in
 if j =? 3 then (Ent POD_STRING 0 [], r1)
 else (Ent (w6c8_ty j) (fst (Cursor.fuzz_u8 r1) mod 4) (zeros (Z.to_nat (fst (Cursor.fuzz_u8 r1) mod 4))),
       snd (Cursor.fuzz_u8 r1))).
Proof.
intros r. unfold w6c_ent, ent_build. cbn [Cursor.fuzz_u8].
replace (Z.to_nat (bv_unsigned (Z_to_bv 8 8) mod 10)) with 8%nat by reflexivity. cbv iota beta.
destruct (Cursor.fuzz_u8 r) as [t r1] eqn:Ef. cbn [fst snd].
pose proof (Cursor.fuzz_u8_range r) as Ht. rewrite Ef in Ht. cbn [fst] in Ht.
destruct (Cursor.fuzz_u8 r1) as [s r2]. cbn [fst snd]. unfold w6c8_ty.
assert (Hc : t mod 4 = 0 \/ t mod 4 = 1 \/ t mod 4 = 2 \/ t mod 4 = 3) by (pose proof (Z.mod_pos_bound t 4); lia).
destruct Hc as [E|[E|[E|E]]]; rewrite E; reflexivity.
Qed.

(* ===================== the 256-value check of a byte expression =====================
   An engine value that reads one atom n only is, in any environment where n holds v, its value in the
   environment where every atom holds v; the 256 values are checked by computation. *)
Definition w6c_env (v : Z) : env := mkEnv (fun _ => Z_to_bv 64 v) (fun _ => []).
Definition w6c_chk (e : sv) (f : Z -> Z) : bool :=
forallb (fun n => let v := Z.of_nat n in bv_eqb (sv_denot (w6c_env v) e) (Z_to_bv 64 (f v))) (seq 0 256).
Lemma w6c_chk_ok : forall e f, w6c_chk e f = true ->
forall v, 0 <= v < 256 -> sv_denot (w6c_env v) e = Z_to_bv 64 (f v).
Proof.
intros e f H v Hv. unfold w6c_chk in H. rewrite forallb_forall in H.
specialize (H (Z.to_nat v)). rewrite Z2Nat.id in H by lia.
apply bv_eqb_true_iff. apply H. apply in_seq. lia.
Qed.
(* the goal sv_denot E e = Z_to_bv 64 (f v) for e a closed expression in atom n (ew E n = Z_to_bv 64 v) *)
Ltac w6c_by256 Hn Hv :=
  lazymatch goal with |- sv_denot ?E ?e = Z_to_bv 64 (?f ?v) =>
    transitivity (sv_denot (w6c_env v) e);
    [ cbn [sv_denot]; rewrite ?Hn; reflexivity
    | apply (w6c_chk_ok e f ltac:(vm_compute; reflexivity) v Hv) ] end.

(* ======================================== the engine's state ======================================== *)
Definition w6c_extra (F t s pp : Z) : list word := [w64 F; w64 t; w64 s; w64 pp].
Definition w6c_RS : YP09.region := YP09.mkRegion (Some 9%nat) 0x10 0x150 0 0
  [YP09.mkChunk 0x10 (CVal 8 (SLit 0x15555556)); YP09.mkChunk 0x118 (CVal 8 (SOff 32 0x218));
   YP09.mkChunk 0x130 (CVal 8 (SOff 32 0x210)); YP09.mkChunk 0x138 (CVal 8 (SOff 35 0x4000));
   YP09.mkChunk 0x148 (CVal 8 (SOff 35 0))].
Definition w6c_RE : YP09.region := YP09.mkRegion (Some 32%nat) 0x210 0x218 0x210 0x214
  [YP09.mkChunk 0x210 (CVal 4 (SLit 0)); YP09.mkChunk 0x214 (CVal 4 (SLit 0))].
Definition w6c_RI (m : nat) : YP09.region := YP09.mkRegion (Some 17%nat) 1 (1 + Z.of_nat m) 0 0
  (firstn m [YP09.mkChunk 1 (CVal 1 (SOff 33 0)); YP09.mkChunk 2 (CVal 1 (SOff 34 0))]).
Definition w6c_RT (tb : Z) : YP09.region := YP09.mkRegion None tb (tb + 16) 0 0 [YP09.mkChunk tb (CImg 16)].
Definition w6c_regs (m : nat) : smem :=
  match m with O => [w6c_RS; w6c_RE] | S _ => [w6c_RS; w6c_RE; w6c_RI m] end.
(* the atom facts; lo20 .. hi20 bounds what is left after the kind byte and hi17 the kind byte's address, both
   closed numerals per arm *)
Definition w6c_atoms (lo20 hi20 hi17 : Z) : list (nat * afact) :=
  [(9%nat, mkAF 0x10007fffc000 (2 ^ 47 - 0x220) 5); (32%nat, mkAF 4096 (2 ^ 47 - 1024) 5);
   (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (17%nat, mkAF 0 hi17 0); (20%nat, mkAF lo20 hi20 0);
   (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 (2 ^ 47) 0)].
Definition w6c_ss0 (pc : Z) (m : nat) (lo20 hi20 hi17 : Z) : sstate :=
  mkSS pc sr_atoms (w6c_regs m) None (mkFacts (w6c_atoms lo20 hi20 hi17) [] []).
(* the entry registers: s2 = a7 + 1, t1 = s4 + 1, a6 = 1 *)
Definition w6c_sr : list sv :=
  sr_set (sr_set (sr_set sr_atoms (18%bv : bv 5) (SOff 17 1)) (6%bv : bv 5) (SOff 20 1)) (16%bv : bv 5) (SLit 1).
Definition w6c_ss (pc : Z) (m : nat) (lo20 hi20 hi17 : Z) : sstate :=
  mkSS pc w6c_sr (w6c_regs m) None (mkFacts (w6c_atoms lo20 hi20 hi17) [] []).
Definition w6c_SH : list shent := [mkSHE 32 0x210 0x218].
Definition w6c_Bx : sv := SOff 27 0.
Definition w6c_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma w6c_rom_tb6 : rom_run_b W6C_TB6 16 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w6c_rom_tb8 : rom_run_b W6C_TB8 16 = true.
Proof. vm_compute. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma w6c_U_reg : forall regs extra (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew (Ereg regs extra) n) = v.
Proof. intros regs extra n r v Hn Hr Hv. rewrite (ew_Ereg_nat regs extra n r Hn), Hr. apply unsigned_lit_small. lia. Qed.

Section e.
Variables (regs : bvmap 5 word) (F t s pp : Z).
Local Notation E := (Ereg regs (w6c_extra F t s pp)).
Lemma w6c_e32 : ew E 32 = w64 F. Proof. exact (ew_Ereg_extra regs _ 0). Qed.
Lemma w6c_e33 : ew E 33 = w64 t. Proof. exact (ew_Ereg_extra regs _ 1). Qed.
Lemma w6c_e34 : ew E 34 = w64 s. Proof. exact (ew_Ereg_extra regs _ 2). Qed.
Lemma w6c_e35 : ew E 35 = w64 pp. Proof. exact (ew_Ereg_extra regs _ 3). Qed.
End e.

(* ---- the entry state ---- *)
Lemma w6c_entry0 : forall pc (m : nat) (W : world rsegs) (regs : bvmap 5 word) memc (R F cur pp : Z)
  (r : list byte) (lo20 hi20 hi17 : Z),
  0 <= pc ->
  getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF -> getr regs 17 = w64 (cur - 1) ->
  getr regs 20 = w64 (Z.of_nat (length r)) ->
  0x10007fffc000 <= R <= 2 ^ 47 - 0x220 -> R mod 32 = 0 ->
  4096 <= F <= 2 ^ 47 - 1024 -> F mod 32 = 0 -> F + 1024 <= R ->
  1 <= cur -> cur - 1 <= hi17 -> lo20 <= Z.of_nat (length r) <= hi20 -> 0 <= pp <= 2 ^ 47 ->
  cur + Z.of_nat (length r) <= 2 ^ 47 ->
  (m <= length r)%nat -> (m <= 2)%nat ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x10) 8 0x15555556 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (F + 0x210) 4 0 ->
  val_mem rsegs (mrestrict (w_H W) memc) (F + 0x214) 4 0 ->
  (forall o, 0x210 <= o < 0x218 -> apresent (w_H W) memc (F + o)) ->
  hm_bytes rsegs (w_H W) memc cur r ->
  (forall a, cur <= a < cur + Z.of_nat (length r) -> ~ (R <= a < R + 0x198) /\ ~ (F + 0x20 <= a < F + 0x278)) ->
  st_ok rsegs (Ereg regs (w6c_extra F (u32_b r 0) (u32_b r 1) pp)) (w6c_ss0 pc m lo20 hi20 hi17)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc m W regs memc R F cur pp r lo20 hi20 hi17 Hpc H9 H27 H17 H20 HR HR32 HF HF32 HFR Hc Hc17 H20r Hpp Hcb
  Hm1 Hm2 V10 V118 V130 V138 V148 VE0 VE4 PE Hin Hdis.
rewrite restrict_mkst_fx.
set (E := Ereg regs (w6c_extra F (u32_b r 0) (u32_b r 1) pp)).
pose proof (u32_b_range r 0) as Ht. pose proof (u32_b_range r 1) as Hs.
assert (U9 : bv_unsigned (ew E 9) = R) by (exact (w6c_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (exact (w6c_U_reg regs _ 27 27%bv _ eq_refl H27 ltac:(unfold SHADOW_OFF; lia))).
assert (U17 : bv_unsigned (ew E 17) = cur - 1) by (exact (w6c_U_reg regs _ 17 17%bv _ eq_refl H17 ltac:(lia))).
assert (U20 : bv_unsigned (ew E 20) = Z.of_nat (length r))
  by (exact (w6c_U_reg regs _ 20 20%bv _ eq_refl H20 ltac:(lia))).
assert (U32 : bv_unsigned (ew E 32) = F) by (subst E; rewrite w6c_e32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = u32_b r 0) by (subst E; rewrite w6c_e33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = u32_b r 1) by (subst E; rewrite w6c_e34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = pp) by (subst E; rewrite w6c_e35; apply unsigned_lit_small; lia).
assert (RS : region_ok rsegs E (mrestrict (w_H W) memc) w6c_RS).
{ unfold w6c_RS. apply (hm_ro_region rsegs E (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val rsegs E _ R 0x10 8 (SLit 0x15555556) 0x15555556);
      [reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V10].
  - apply (chunk_ok_val rsegs E _ R 0x118 8 (SOff 32 0x218) (F + 0x218));
      [cbn [sv_denot]; rewrite U32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V118].
  - apply (chunk_ok_val rsegs E _ R 0x130 8 (SOff 32 0x210) (F + 0x210));
      [cbn [sv_denot]; rewrite U32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V130].
  - apply (chunk_ok_val rsegs E _ R 0x138 8 (SOff 35 0x4000) (pp + 0x4000));
      [cbn [sv_denot]; rewrite U35; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V138].
  - apply (chunk_ok_val rsegs E _ R 0x148 8 (SOff 35 0) pp);
      [cbn [sv_denot]; rewrite U35, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V148]. }
assert (RE : region_ok rsegs E (mrestrict (w_H W) memc) w6c_RE).
{ unfold w6c_RE. apply (hm_rw_region rsegs E (w_H W) memc 32%nat F);
    [exact U32 | lia | lia | intros o Ho; apply PE; lia |].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val rsegs E _ F 0x210 4 (SLit 0) 0); [reflexivity | cbn; lia | lia | exact VE0].
  - apply (chunk_ok_val rsegs E _ F 0x214 4 (SLit 0) 0); [reflexivity | cbn; lia | lia | exact VE4]. }
assert (RI : (1 <= m)%nat -> region_ok rsegs E (mrestrict (w_H W) memc) (w6c_RI m)).
{ intros Hm. unfold w6c_RI. apply (hm_ro_region rsegs E (w_H W) memc 17%nat (cur - 1)); [exact U17 | lia | lia |].
  assert (B0 : val_mem rsegs (mrestrict (w_H W) memc) (cur - 1 + 1) 1 (u32_b r 0)).
  { replace (cur - 1 + 1) with (cur + Z.of_nat 0) by lia. rewrite u32_b_eq.
    apply (hm_bytes_byte rsegs (w_H W) memc cur r 0 Hin). lia. }
  assert (B1 : (2 <= m)%nat -> val_mem rsegs (mrestrict (w_H W) memc) (cur - 1 + 2) 1 (u32_b r 1)).
  { intros H2. replace (cur - 1 + 2) with (cur + Z.of_nat 1) by lia. rewrite u32_b_eq.
    apply (hm_bytes_byte rsegs (w_H W) memc cur r 1 Hin). lia. }
  destruct m as [|[|[|m]]]; [lia | | | lia]; cbn [firstn]; repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val rsegs E _ (cur - 1) 1 1 (SOff 33 0) (u32_b r 0));
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | lia | exact B0].
  - apply (chunk_ok_val rsegs E _ (cur - 1) 1 1 (SOff 33 0) (u32_b r 0));
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | lia | exact B0].
  - apply (chunk_ok_val rsegs E _ (cur - 1) 2 1 (SOff 34 0) (u32_b r 1));
      [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | cbn; lia | lia | apply B1; lia]. }
unfold w6c_ss0. apply (entry_st_ok_full rsegs); try change (Ereg regs (w6c_extra F (u32_b r 0) (u32_b r 1) pp)) with E.
- apply regs_ok_Ereg.
- destruct m as [|[|[|m]]]; [| | | lia]; vm_compute; reflexivity.
- destruct m as [|m']; unfold w6c_regs; repeat apply Forall_cons; try apply Forall_nil; try assumption.
  apply RI. lia.
- destruct m as [|m']; unfold w6c_regs; apply pairwise_disjoint_of_extents;
    unfold w6c_RS, w6c_RE, w6c_RI; cbn [map]; unfold extent_of_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
    try change (Ereg regs (w6c_extra F (u32_b r 0) (u32_b r 1) pp)) with E; rewrite ?U9, ?U32, ?U17.
  + repeat split; first [exact I | lia].
  + assert (D1 : cur + Z.of_nat (S m') <= R + 0x10 \/ R + 0x150 <= cur).
    { destruct (Hdis cur ltac:(lia)) as [X _]. destruct (Z_le_gt_dec (R + 0x150) cur) as [Y|Y]; [right; exact Y|].
      left. destruct (Z_le_gt_dec (cur + Z.of_nat (S m')) (R + 0x10)) as [Z1|Z1]; [exact Z1|].
      exfalso. destruct (Z_lt_ge_dec cur R) as [Y2|Y2]; [|lia].
      destruct (Hdis R ltac:(lia)) as [X2 _]. apply X2. lia. }
    assert (D2 : cur + Z.of_nat (S m') <= F + 0x210 \/ F + 0x218 <= cur).
    { destruct (Z_le_gt_dec (F + 0x218) cur) as [Y|Y]; [right; exact Y|].
      left. destruct (Z_le_gt_dec (cur + Z.of_nat (S m')) (F + 0x210)) as [Z1|Z1]; [exact Z1|].
      exfalso. destruct (Z_lt_ge_dec cur (F + 0x210)) as [Y2|Y2].
      - destruct (Hdis (F + 0x210) ltac:(lia)) as [_ X2]. apply X2. lia.
      - destruct (Hdis cur ltac:(lia)) as [_ X2]. apply X2. lia. }
    repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]]. cbn [w6c_atoms f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U27, U17, U20, U33, U34, U35. change (2 ^ 5) with 32. change (2 ^ 0) with 1.
  rewrite !Z.mod_1_r. repeat split; lia.
Qed.

(* the entry state with the three pins *)
Lemma w6c_entry : forall pc (m : nat) (W : world rsegs) (regs : bvmap 5 word) memc (R F cur pp : Z)
  (r : list byte) (lo20 hi20 hi17 : Z),
  0 <= pc ->
  getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF -> getr regs 17 = w64 (cur - 1) ->
  getr regs 18 = w64 cur -> getr regs 20 = w64 (Z.of_nat (length r)) ->
  getr regs 6 = w64 (Z.of_nat (length r) + 1) -> getr regs 16 = w64 1 ->
  0x10007fffc000 <= R <= 2 ^ 47 - 0x220 -> R mod 32 = 0 ->
  4096 <= F <= 2 ^ 47 - 1024 -> F mod 32 = 0 -> F + 1024 <= R ->
  1 <= cur -> cur - 1 <= hi17 -> lo20 <= Z.of_nat (length r) <= hi20 -> 0 <= pp <= 2 ^ 47 ->
  cur + Z.of_nat (length r) <= 2 ^ 47 ->
  (m <= length r)%nat -> (m <= 2)%nat ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x10) 8 0x15555556 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (F + 0x210) 4 0 ->
  val_mem rsegs (mrestrict (w_H W) memc) (F + 0x214) 4 0 ->
  (forall o, 0x210 <= o < 0x218 -> apresent (w_H W) memc (F + o)) ->
  hm_bytes rsegs (w_H W) memc cur r ->
  (forall a, cur <= a < cur + Z.of_nat (length r) -> ~ (R <= a < R + 0x198) /\ ~ (F + 0x20 <= a < F + 0x278)) ->
  st_ok rsegs (Ereg regs (w6c_extra F (u32_b r 0) (u32_b r 1) pp)) (w6c_ss pc m lo20 hi20 hi17)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc m W regs memc R F cur pp r lo20 hi20 hi17 Hpc H9 H27 H17 H18 H20 H6 H16 HR HR32 HF HF32 HFR Hc Hc17 H20r Hpp Hcb
  Hm1 Hm2 V10 V118 V130 V138 V148 VE0 VE4 PE Hin Hdis.
pose proof (w6c_entry0 pc m W regs memc R F cur pp r lo20 hi20 hi17 Hpc H9 H27 H17 H20 HR HR32 HF HF32 HFR Hc Hc17
  H20r Hpp Hcb Hm1 Hm2 V10 V118 V130 V138 V148 VE0 VE4 PE Hin Hdis) as HS0.
set (E := Ereg regs (w6c_extra F (u32_b r 0) (u32_b r 1) pp)) in *.
assert (E17 : ew E 17 = Z_to_bv 64 (cur - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
assert (E20 : ew E 20 = Z_to_bv 64 (Z.of_nat (length r)))
  by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
unfold w6c_ss0 in HS0.
pose proof (st_ok_pin_sv rsegs E _ _ (18%bv : bv 5) (SOff 17 1) HS0 eq_refl
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite E17, unsigned_lit_small by lia; rewrite H18; unfold w64; f_equal; lia))
  as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
pose proof (st_ok_pin_sv rsegs E _ _ (6%bv : bv 5) (SOff 20 1) HS1 eq_refl
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite E20, unsigned_lit_small by lia; rewrite H6; unfold w64; f_equal))
  as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
pose proof (st_ok_pin_lit rsegs E _ _ (16%bv : bv 5) 1 HS2 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; exact H16)) as HS3.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
exact HS3.
Qed.

(* ---- the shadow entry over e62's header: e62 is in scope and lies outside the shadow band ---- *)
Lemma w6c_shok : forall (regs : bvmap 5 word) (H : word -> bool) mem F t s pp,
  getr regs 27 = w64 SHADOW_OFF -> 4096 <= F <= 2 ^ 47 - 1024 ->
  range_addressable (aview rsegs H mem) SHADOW_OFF (F + 0x210) 8 ->
  (forall a, F + 0x210 <= a < F + 0x218 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)) ->
  sh_ok rsegs w6c_Bx w6c_SH (Ereg regs (w6c_extra F t s pp)) (mrestrict H mem).
Proof.
intros regs H mem F t s pp H27 HF Hra Hap.
set (E := Ereg regs (w6c_extra F t s pp)).
assert (U27 : U E (SOff 27 0) = SHADOW_OFF).
{ apply U_atom; [subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; reflexivity | unfold SHADOW_OFF; lia]. }
assert (U32 : U E (SOff 32 0) = F).
{ apply U_atom; [subst E; rewrite w6c_e32; reflexivity | lia]. }
apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range rsegs H mem E w6c_Bx 32 (F + 0x210) 8 F 0x210 0x218 Hra U27 U32); [lia | lia |].
intros x Hx. apply Hap. cbn in Hx. lia.
Qed.

(* ---- a region dropped from, or added at, the end of a state's region list ---- *)
Lemma w6c_pw_app1 : forall E l r, pairwise_disjoint E (l ++ [r]) ->
  pairwise_disjoint E l /\ Forall (fun x => extent_disjoint E x r) l.
Proof.
intros E l r. induction l as [|x l IH]; cbn [app pairwise_disjoint]; [intros _; split; [exact I | constructor]|].
intros [Ha Hp]. destruct (IH Hp) as [Hp' Hf]. split; [|constructor; [|exact Hf]].
- split; [|exact Hp']. clear -Ha. induction l as [|y l IHl]; cbn [app all_disjoint] in *; [exact I|].
  destruct Ha as [H1 H2]. split; [exact H1 | exact (IHl H2)].
- clear -Ha. induction l as [|y l IHl]; cbn [app all_disjoint] in *; [exact (proj1 Ha)|]. exact (IHl (proj2 Ha)).
Qed.
Lemma w6c_pw_app1' : forall E l r, pairwise_disjoint E l -> Forall (fun x => extent_disjoint E x r) l ->
  pairwise_disjoint E (l ++ [r]).
Proof.
intros E l r. induction l as [|x l IH]; cbn [app pairwise_disjoint]; [intros _ _; split; exact I|].
intros [Ha Hp] Hf. inversion Hf as [|? ? Hx Hf']; subst. split; [|exact (IH Hp Hf')].
clear -Ha Hx. induction l as [|y l IHl]; cbn [app all_disjoint] in *; [split; [exact Hx | exact I]|].
destruct Ha as [H1 H2]. split; [exact H1 | exact (IHl H2)].
Qed.
Lemma w6c_regions_wf_app : forall l1 l2, regions_wf (l1 ++ l2) = regions_wf l1 && regions_wf l2.
Proof. intros l1 l2. induction l1 as [|r l1 IH]; [reflexivity|]. cbn [app regions_wf]. rewrite IH, andb_assoc. reflexivity. Qed.
Lemma w6c_st_ok_drop : forall E pc rg l r resv f ms,
  st_ok rsegs E (mkSS pc rg (l ++ [r]) resv f) ms -> st_ok rsegs E (mkSS pc rg l resv f) ms.
Proof.
intros E pc rg l r resv f ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpw) & H9).
repeat (split; [assumption|]). split; [|exact H9]. cbn [ss_mem] in *.
split; [|split].
- rewrite w6c_regions_wf_app in Hwf. apply andb_true_iff in Hwf as [Ha _]. exact Ha.
- apply Forall_app in Hok as [Ha _]. exact Ha.
- exact (proj1 (w6c_pw_app1 E l r Hpw)).
Qed.
Lemma w6c_st_ok_add : forall E pc rg l r' resv f ms,
  st_ok rsegs E (mkSS pc rg l resv f) ms ->
  YP09.region_wf r' = true -> region_ok rsegs E (ms_mem ms) r' ->
  Forall (fun x => extent_disjoint E x r') l ->
  st_ok rsegs E (mkSS pc rg (l ++ [r']) resv f) ms.
Proof.
intros E pc rg l r' resv f ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpw) & H9) Hwf' Hok' Hd.
repeat (split; [assumption|]). split; [|exact H9]. cbn [ss_mem] in *.
split; [|split].
- rewrite w6c_regions_wf_app, Hwf. cbn [regions_wf]. rewrite Hwf'. reflexivity.
- apply Forall_app. split; [exact Hok | constructor; [exact Hok' | constructor]].
- exact (w6c_pw_app1' E l r' Hpw Hd).
Qed.

(* ---- reading a region of the final state ---- *)
Lemma w6c_region_nth : forall E ss ms i r,
  st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma w6c_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.

Section d.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* the leaf of a block: the engine's last state at the block's end pc gives hdu_blk_postE *)
Lemma w6c_post_of_run : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Wr R E ss ms md,
  st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k -> same_io mdc md ->
  (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
  R W (ms_regs ms) (ms_mem ms) ->
  SRr rsegs W (mkCfg ms md)
    (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Wr R).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Wr R E ss ms md HS Hrv Hpc HJ Hio Hregs
  Hkept HR.
apply SRr_ret. exists lyc, Sc, (ms_regs ms), (ms_mem ms), md.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
split; [exact HJ|]. split; [exact Hregs|]. split; [reflexivity|]. split; [apply Permutation_refl|].
split; [exact Hio|]. split; [apply (mo_le_refl MT MTL)|]. split; [exact Hkept | exact HR].
Qed.

(* ======================================== the block statements ======================================== *)
(* the context of a case block: the harness's journal so far, the real frame R (32-aligned, below the entry sp, the
   callees' stack inside the journal's window), the frame for locals F (the side-stack frame (4, pos) the harness
   owns, present); cj_D_facts of lib/AU/HPgCaseBJ.v gives each *)
Definition w6c_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
R mod 32 = 0 /\ alloc_ceiling + T_SEG_STK <= R /\ R + 0x220 <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 - STK <= R - T_SEG_STK /\
In (4, pos) own /\ F = frame_addr lyc 4 pos /\ 4096 <= F /\ F + 1024 <= alloc_ceiling /\ F mod 32 = 0 /\
in_app F 1024 /\ (forall o, 0 <= o < 1024 -> apresent (w_H W) memc (F + o)).

(* the step at a `jal` to __asan_memset / __asan_memcpy, from the kernel's contract of the intrinsic at its entry:
   lib/A/HPgIntrin.v's hd_intrin_at restated over image B's segments (the Section hypothesis INTRIN of the block
   files; lib/AU/HPgCaseB.v's twin discharges it) *)
Definition w6c_intrin_law : Prop :=
forall op pc, aintrin_realizes rsegs B op pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok rsegs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) x n)
| OSet => True end) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) =
match op with OCpy => aview rsegs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).

(* ---- the fill block of case 8 (pod.h:364): 0x822b0 .. J ----
     0x822b0  s5 := [R+0x130] (= F + 0x210); 0x822b4 sw a2,4(s5) (e62.size := a2)
     0x822b8  a0 := [R+0x118] (= F + 0x218); 0x822bc a1 := 0; 0x822c0 jal __asan_memset (e62.body[0..a2) := 0)
     0x822c4  t1 := s4; s4 := s5; j 0x82610; 0x82610 a3 := s2; 0x82614 s2 := [R+0x138] (= pp + OFF_LEN) -> J *)
Definition w6c_fill_clob : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 28; 29; 30; 31]%bv.
Definition w6c_fill_wr (R F sz : Z) : Z -> Prop :=
  fun a => (R - T_SEG_STK <= a < R) \/ (F + 0x214 <= a < F + 0x218 + sz).
Definition w6c_fill_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos pp c2 lf sz : Z),
w6c_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF ->
getr regs 12 = w64 sz -> getr regs 18 = w64 c2 -> getr regs 20 = w64 lf ->
0 <= sz <= 3 -> 0 <= c2 < 2 ^ 64 -> 0 <= lf < 2 ^ 64 -> 0 <= pp <= 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0x210) 104 ->
shadow_hull_vis (aview rsegs (w_H W) memc) (F + 0x210) 104 ->
SRr rsegs W (cfg_at rsegs W6C_F8 regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6C_J w6c_fill_clob
   (w6c_fill_wr R F sz)
   (fun W2 regs2 mem2 => W2 = W /\ getr regs2 13 = w64 c2 /\ getr regs2 6 = w64 lf /\
      getr regs2 18 = w64 (pp + 0x4000) /\ getr regs2 20 = w64 (F + 0x210) /\
      val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x214) 4 sz /\
      (forall i, 0 <= i < sz -> aview rsegs (w_H W2) mem2 (F + 0x218 + i) = Some 0))).

(* ---- the take block of cases 6 and 7 (fuzz.h:59-65 inlined in pod.h:213-217's caller): pc0 = 0x8227c (case 6) or
   0x8244c (case 7), each `sw a2,4(s4)` followed by the same sequence ----
     pc0       sw a2,4(s4)              e62.size := sz
     pc0 + 4   bltu a2,a1 -> pc0 + 12; pc0 + 8 a2 := a1          n := min(sz, left)
     pc0 + 12  not a0,s2; bgeu a0,a2 -> 0x82464                  the UBSan pointer test of fuzz.h:63
     0x82464   s10 := s2 + a2; s5 := a1 - a2; a0 := [R+0x118] (= F + 0x218); a1 := s2
     0x82474   jal __asan_memcpy                                 e62.body[0..n) := the n input bytes at the cursor
     0x82478   a3 := s10; t1 := s5; j 0x82614; 0x82614 s2 := [R+0x138] (= pp + OFF_LEN) -> J *)
Definition w6c_take_clob : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 21; 26; 28; 29; 30; 31]%bv.
Definition w6c_take_wr (R F n : Z) : Z -> Prop :=
  fun a => (R - T_SEG_STK <= a < R) \/ (F + 0x214 <= a < F + 0x218 + n).
Definition w6c_take_stmt (pc0 : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos pp c2 sz : Z)
  (q : list byte),
w6c_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF ->
getr regs 12 = w64 sz -> getr regs 11 = w64 (Z.of_nat (length q)) -> getr regs 18 = w64 c2 ->
getr regs 20 = w64 (F + 0x210) ->
0 <= sz <= 11 -> 0 <= pp <= 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0x210) 104 ->
shadow_hull_vis (aview rsegs (w_H W) memc) (F + 0x210) 104 ->
hm_bytes rsegs (w_H W) memc c2 q ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF c2 (Z.of_nat (length q)) ->
(0 < Z.of_nat (length q) -> shadow_hull_vis (aview rsegs (w_H W) memc) c2 (Z.of_nat (length q))) ->
amem_range c2 (Z.of_nat (length q)) -> 1 <= c2 ->
(forall a, c2 <= a < c2 + Z.of_nat (length q) ->
   ~ (R - T_SEG_STK <= a < R + 0x198) /\ ~ (F + 0x20 <= a < F + 0x278)) ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6C_J w6c_take_clob
   (w6c_take_wr R F (Z.of_nat (length (firstn (Z.to_nat sz) q))))
   (fun W2 regs2 mem2 => W2 = W /\
      getr regs2 13 = w64 (c2 + Z.of_nat (length (firstn (Z.to_nat sz) q))) /\
      getr regs2 6 = w64 (Z.of_nat (length (skipn (Z.to_nat sz) q))) /\
      getr regs2 18 = w64 (pp + 0x4000) /\ getr regs2 20 = w64 (F + 0x210) /\
      val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x214) 4 sz /\
      hm_bytes rsegs (w_H W2) mem2 (F + 0x218) (firstn (Z.to_nat sz) q))).
End d.
End b.

(* ======================================== the tail kit ========================================
   The fill and take blocks run from a state whose regions are R's three cells [R+0x118, R+0x140) (read only) and,
   before their call, e62's size word [F+0x214, F+0x218) (written, covered by the shadow entry w6c_SH4); after the
   call, R's cells alone. The extra atoms are w6c_extra's (32 = F, 35 = pp; 33, 34 unused). *)
Definition w6c_RSt : YP09.region := YP09.mkRegion (Some 9%nat) 0x118 0x140 0 0
  [YP09.mkChunk 0x118 (CVal 8 (SOff 32 0x218)); YP09.mkChunk 0x130 (CVal 8 (SOff 32 0x210));
   YP09.mkChunk 0x138 (CVal 8 (SOff 35 0x4000))].
Definition w6c_RE4 : YP09.region := YP09.mkRegion (Some 32%nat) 0x214 0x218 0x214 0x218 [].
Definition w6c_tregs (e : bool) : smem := if e then [w6c_RSt; w6c_RE4] else [w6c_RSt].
Definition w6c_tatoms : list (nat * afact) :=
  [(9%nat, mkAF 0x10007fffc000 (2 ^ 47 - 0x220) 5); (32%nat, mkAF 4096 (2 ^ 47 - 1024) 5);
   (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (35%nat, mkAF 0 (2 ^ 47) 0)].
Definition w6c_tss (pc : Z) (e : bool) (G : list (nat * afact)) : sstate :=
  mkSS pc sr_atoms (w6c_tregs e) None (mkFacts (w6c_tatoms ++ G) [] []).
Definition w6c_SH4 : list shent := [mkSHE 32 0x214 0x218].

Lemma w6c_atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; cbn [app atoms_ok] in *; [exact H2|].
destruct H1 as [Ha Hb]. split; [exact Ha | exact (IH Hb)].
Qed.
Lemma w6c_den_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. intros E z Hz. rewrite denot_lit_U, U_SLit, zcanon_id by (unfold M64; lia). reflexivity. Qed.
Lemma w6c_den_off : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof. intros E n v x H Hv Hx. rewrite denot_lit_U, (U_atom_off E n v x H Hv Hx). reflexivity. Qed.
Lemma w6c_den0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. rewrite (w6c_den_off E n v 0 H Hv) by lia. rewrite Z.add_0_r. reflexivity. Qed.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma w6c_tentry : forall pc (e : bool) (G : list (nat * afact)) (W : world rsegs) (regs : bvmap 5 word) memc (R F pp : Z),
  0 <= pc -> getr regs 9 = w64 R -> getr regs 27 = w64 SHADOW_OFF ->
  0x10007fffc000 <= R <= 2 ^ 47 - 0x220 -> R mod 32 = 0 -> 4096 <= F <= 2 ^ 47 - 1024 -> F mod 32 = 0 ->
  F + 1024 <= R -> 0 <= pp <= 2 ^ 47 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) ->
  (e = true -> forall o, 0x214 <= o < 0x218 -> apresent (w_H W) memc (F + o)) ->
  atoms_ok (Ereg regs (w6c_extra F 0 0 pp)) G ->
  st_ok rsegs (Ereg regs (w6c_extra F 0 0 pp)) (w6c_tss pc e G)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc e G W regs memc R F pp Hpc H9 H27 HR HR32 HF HF32 HFR Hpp V118 V130 V138 PE HG.
rewrite restrict_mkst_fx.
set (E := Ereg regs (w6c_extra F 0 0 pp)).
assert (U9 : bv_unsigned (ew E 9) = R) by (exact (w6c_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (exact (w6c_U_reg regs _ 27 27%bv _ eq_refl H27 ltac:(unfold SHADOW_OFF; lia))).
assert (U32 : bv_unsigned (ew E 32) = F) by (subst E; rewrite w6c_e32; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = pp) by (subst E; rewrite w6c_e35; apply unsigned_lit_small; lia).
assert (RS : region_ok rsegs E (mrestrict (w_H W) memc) w6c_RSt).
{ unfold w6c_RSt. apply (hm_ro_region rsegs E (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val rsegs E _ R 0x118 8 (SOff 32 0x218) (F + 0x218));
      [cbn [sv_denot]; rewrite U32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V118].
  - apply (chunk_ok_val rsegs E _ R 0x130 8 (SOff 32 0x210) (F + 0x210));
      [cbn [sv_denot]; rewrite U32; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V130].
  - apply (chunk_ok_val rsegs E _ R 0x138 8 (SOff 35 0x4000) (pp + 0x4000));
      [cbn [sv_denot]; rewrite U35; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact V138]. }
unfold w6c_tss. apply (entry_st_ok_full rsegs); try change (Ereg regs (w6c_extra F 0 0 pp)) with E.
- apply regs_ok_Ereg.
- destruct e; vm_compute; reflexivity.
- destruct e; unfold w6c_tregs; repeat apply Forall_cons; try apply Forall_nil; try exact RS.
  unfold w6c_RE4. apply (hm_rw_region rsegs E (w_H W) memc 32%nat F); [exact U32 | lia | lia | | apply Forall_nil].
  exact (PE eq_refl).
- destruct e; unfold w6c_tregs; apply pairwise_disjoint_of_extents;
    unfold w6c_RSt, w6c_RE4; cbn [map]; unfold extent_of_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
    try change (Ereg regs (w6c_extra F 0 0 pp)) with E; rewrite ?U9, ?U32; repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]]. apply w6c_atoms_ok_app; [|exact HG].
  cbn [w6c_tatoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U27, U35. change (2 ^ 5) with 32. change (2 ^ 0) with 1.
  rewrite !Z.mod_1_r. repeat split; lia.
Qed.

(* the shadow entry over e62's size word: e62 is in scope and lies in application memory *)
Lemma w6c_shok4 : forall (regs : bvmap 5 word) (H : word -> bool) mem F t s pp,
  getr regs 27 = w64 SHADOW_OFF -> 4096 <= F <= 2 ^ 47 - 1024 -> in_app F 1024 ->
  range_addressable (aview rsegs H mem) SHADOW_OFF (F + 0x214) 4 ->
  sh_ok rsegs w6c_Bx w6c_SH4 (Ereg regs (w6c_extra F t s pp)) (mrestrict H mem).
Proof.
intros regs H mem F t s pp H27 HF Happ Hra.
set (E := Ereg regs (w6c_extra F t s pp)).
assert (U27 : U E (SOff 27 0) = SHADOW_OFF).
{ apply U_atom; [subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; reflexivity | unfold SHADOW_OFF; lia]. }
assert (U32 : U E (SOff 32 0) = F).
{ apply U_atom; [subst E; rewrite w6c_e32; reflexivity | lia]. }
apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range rsegs H mem E w6c_Bx 32 (F + 0x214) 4 F 0x214 0x218 Hra U27 U32); [lia | lia |].
intros x Hx. cbn in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
pose proof alloc_ceiling_lt. lia.
Qed.

(* the write windows of a tail state, and that each byte of them belongs to the frame the harness owns *)
Lemma w6c_tw : forall E (e : bool) a, in_wrange E (w6c_tregs e) a ->
  bv_unsigned (ew E 32) + 0x214 <= a < bv_unsigned (ew E 32) + 0x218.
Proof.
intros E e a (r & Hin & Ha). destruct e; unfold w6c_tregs in Hin; cbn [In] in Hin;
  repeat destruct Hin as [<-|Hin]; try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val w6c_RSt w6c_RE4] in Ha; lia.
Qed.
Lemma w6c_tawr : forall E (e : bool) STK sp0 FP bl0 blc lyc own F pos,
  bv_unsigned (ew E 32) = F -> In (4, pos) own -> F = frame_addr lyc 4 pos ->
  awr_ok E (w6c_tregs e) STK sp0 FP bl0 blc lyc own.
Proof.
intros E e STK sp0 FP bl0 blc lyc own F pos U32 Hown HF a Ha. pose proof (w6c_tw E e a Ha) as Hw. rewrite U32 in Hw.
unfold awr_byte. right; right; right. exists 4, pos. split; [exact Hown|]. left.
unfold in_zr. cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 4) with 1024. lia.
Qed.
(* a register outside clob is callee-saved, when the computation says so over the 31 registers *)
Definition w6c_cs_b (z : Z) : bool :=
  (z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)).
Lemma w6c_cs : forall clob : list (bv 5),
  forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob || w6c_cs_b (bv_unsigned r)) nz_regs = true ->
  forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> acallee_saved (bv_unsigned r).
Proof.
intros clob Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (in_nz_regs r Hr0)) as Hq. cbv beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply Hn. apply existsb_exists in Hq as (c0 & Hc & Hb). apply bv_eqb_eq in Hb. subst c0. exact Hc.
- unfold w6c_cs_b in Hq. unfold acallee_saved.
  repeat rewrite orb_true_iff in Hq. rewrite andb_true_iff, ?Z.eqb_eq, ?Z.leb_le in Hq. lia.
Qed.
Lemma w6c_reg_cs : forall (regs1 regs2 : bvmap 5 word) (r : bv 5), aregs_preserved regs1 regs2 ->
  acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs1 r.
Proof. intros regs1 regs2 r HP Hr. pose proof (HP _ Hr) as X. rewrite !Z_to_bv_bv_unsigned in X. exact X. Qed.
(* an n-byte value kept by a run that keeps its bytes *)
Lemma w6c_val_kept : forall (H H' : word -> bool) m m' a n v, val_mem rsegs (mrestrict H m) a n v ->
  (forall i, 0 <= i < Z.of_nat n -> aview rsegs H' m' (a + i) = aview rsegs H m (a + i)) ->
  val_mem rsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v V K k Hk. apply (hm_aview_mbyte rsegs). rewrite K by lia.
unfold aview. rewrite (V k Hk). cbn [option_map]. reflexivity.
Qed.
(* a run whose regions have no write window keeps every byte *)
Lemma w6c_frame_ro : forall E (m m' : word -> option byte), frame_of E (w6c_tregs false) m m' -> forall x, m' x = m x.
Proof.
intros E m m' HF x. apply HF. intros (r & Hin & Ha). cbn [w6c_tregs In] in Hin. destruct Hin as [<-|[]].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val w6c_RSt] in Ha. lia.
Qed.
Lemma w6c_tw_sk : forall E rs (e : bool) a, YP09.skeleton rs = YP09.skeleton (w6c_tregs e) -> in_wrange E rs a ->
  bv_unsigned (ew E 32) + 0x214 <= a < bv_unsigned (ew E 32) + 0x218.
Proof. intros E rs e a Hsk Ha. apply (w6c_tw E e a). exact (in_wrange_skeleton E rs (w6c_tregs e) a Hsk Ha). Qed.
Lemma w6c_tawr_sk : forall E rs (e : bool) STK sp0 FP bl0 blc lyc own F pos,
  YP09.skeleton rs = YP09.skeleton (w6c_tregs e) ->
  bv_unsigned (ew E 32) = F -> In (4, pos) own -> F = frame_addr lyc 4 pos ->
  awr_ok E rs STK sp0 FP bl0 blc lyc own.
Proof.
intros E rs e STK sp0 FP bl0 blc lyc own F pos Hsk U32 Hown HF a Ha.
exact (w6c_tawr E e STK sp0 FP bl0 blc lyc own F pos U32 Hown HF a (in_wrange_skeleton E rs (w6c_tregs e) a Hsk Ha)).
Qed.
Lemma w6c_den_add : forall E a b va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
  0 <= va -> 0 <= vb -> va + vb < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (va + vb).
Proof.
intros E a b va vb Ha Hb H1 H2 H3. rewrite denot_lit_U, U_SAlu, (U_atom E a va Ha), (U_atom E b vb Hb) by lia.
cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma w6c_den_subm : forall E a b va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb -> 0 <= vb <= va ->
  va < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff a 0) (SMd M_MUL (SOff b 0) (SLit (-1)))) = Z_to_bv 64 (va - vb).
Proof.
intros E a b va vb Ha Hb H1 H2. rewrite denot_lit_U, U_SAlu, U_SMd, (U_atom E a va Ha), (U_atom E b vb Hb), U_SLit by lia.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64. f_equal. rewrite Zplus_mod_idemp_r.
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace (va + vb * (2 ^ 64 - 1)) with ((va - vb) + vb * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
End t.

(* a register of the engine's last state, as its symbolic value *)
Ltac w6c_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?Ev ?ssv (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H Ev ssv ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ssv) r) in
    change (sr_get (ss_regs ssv) r) with e end.
(* region i of the engine's last state *)
Ltac w6c_rnth HS i Hr :=
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let o := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch o with Some ?r =>
      let Hn := fresh "Hn" in
      assert (Hn : nth_error (ss_mem ss) i = Some r) by (vm_compute; reflexivity);
      pose proof (w6c_region_nth _ _ _ i r HS Hn) as Hr; clear Hn; cbn [restrict ms_mem] in Hr
    end end.
(* an env fact carried over the fresh atoms of a token run *)
Ltac w6c_ew HS H :=
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  let H' := fresh H "'" in
  lazymatch type of H with
  | ew _ ?n = ?v => assert (H' : ew Ev n = v) by (rewrite ?ew_ewset_other by lia; exact H)
  | bv_unsigned (ew _ ?n) = ?v => assert (H' : bv_unsigned (ew Ev n) = v) by (rewrite ?ew_ewset_other by lia; exact H)
  end end.
(* the side goals of a kept-register rewrite at a literal register: bv_unsigned r <> 0 and ~ In r l *)
Ltac w6c_side :=
  first [ vm_compute; discriminate
        | let X := fresh "X" in intros X; cbv [In] in X;
          repeat (destruct X as [X|X]; [discriminate X|]); exact X ].
(* after a run: the kept-bytes fact KE (every byte outside Zn as at the block's start) moves to the run's last
   memory; wrl proves that the run's write windows lie in Zn *)
Ltac w6c_keep Zn wrl :=
  lazymatch goal with
  | HFrx : frame_of ?Ev ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2),
    KE : forall a, 0 <= a < 2 ^ 64 -> ~ _ -> aview _ _ ?m1 a = _ |- _ =>
    let KS := fresh "KS" in
    pose proof (cb_kept_run Zn Ev rs H _ m1 m2 KE HFrx ltac:(wrl)) as KS;
    clear KE HFrx; rename KS into KE
  end.

Print Assumptions w6c_tbl_ok.
Print Assumptions w6c_build_kind.
Print Assumptions w6c_ent_mem_pad.
Print Assumptions w6c6_model.
Print Assumptions w6c7_model.
Print Assumptions w6c8_model.
Print Assumptions w6c_chk_ok.
Print Assumptions w6c_entry.
Print Assumptions w6c_shok.
Print Assumptions w6c_st_ok_drop.
Print Assumptions w6c_st_ok_add.
Print Assumptions w6c_post_of_run.
