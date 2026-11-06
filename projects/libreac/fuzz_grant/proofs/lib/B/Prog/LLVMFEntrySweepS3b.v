(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS3b), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySweepS3b.v. *)
(* Segment 3, part b, of the sweep phase of fuzz_grant's entry function on IMAGE B:
   0x81684 .. 0x8173c (fuzz_grant.c:328-332) — the second group-A loop and the block that
   sets the group-B loop up. For every channel c = 1 .. a.width - 1 (the head 0x81684,
   s2 = c) and every parameter p = 0, 1, 2 (the head 0x81694, s7 = p) the harness calls
   want_of(was_set, set_to, (a.base + c) & 0xff, p & 0xff) (0x816e8) for the value it wants
   and check_groupa on sweep row 8 + 3c + p (0x81700). The parameter loop's back edge is
   `bne s7,s6` at 0x81708 (s6 = 3), the channel loop's is `bltu s2,a0` at 0x81718 against
   a.width read again at 0x81710, and the exit falls through 0x8171c .. 0x81738 into the
   group-B loop (0x8173c, i = 0).
   Three branches are refuted here, all into the UBSan trap `unimp` 0x81f48: 0x8169c (the
   32-bit sum 8 + 3c + p is the 64-bit one, as it is at most 127), 0x816ac (the row
   s + 34 (8 + 3c + p) is not null, as s >= 4096) and 0x816c0 (the row does not wrap
   below s, as the sweep buffer lies below the allocator's ceiling, and the index is not
   negative). The engine decides all three from the facts and the aliases of the turn's
   seat (`g1_atoms`, `g1_alias`), whose proofs are the arithmetic of the refutation.

   The walk is a nested induction: the outer one on the channels left (a.width - c), the
   inner one on the parameters left (3 - p). The two calls are LLVMFEntrySweepS3d.v's
   `gsw_want` and `gsw_cga`; the ground is LLVMFEntrySweepS1c.v and LLVMFEntrySweepS3c.v.

   Adapted from lib/A/Prog/GrantEntrySweepS3b.v (a working branch afd75724b5b, blob f467c3a4a, 1307 lines),
   which carries no licence header of its own.
   Image B calls want_of where image A reads was_set and set_to in line and calls reac_headamp_default, indexes the row as 8 + 3c + p from s11 behind three UBSan guards into the trap 0x81f48, keeps c, 3c + 8, 34, 3 and p in s2, s4, s5, s6 and s7, and reloads `a`, the two frame arrays and the table from spill slots 120, 136, 128 and 152. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib GrantRo GrantBContracts
LLVMFEntryDefs LLVMFEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC45 YC85 GrantFrame GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* Image A's text was written with this flag false; `Local` keeps the setting here. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
LLVMFEntrySweepS1c LLVMFEntrySweepS3c LLVMFEntrySweepS3d.

(* ---- the listing offsets of this segment (address - 0x80a3c) ---- *)
Definition GPS_g1in : Z := 0xc58.   (* 0x81694, the head of the parameter loop *)
Definition GPS_g1hd : Z := 0xcb0.   (* 0x816ec, after want_of                  *)
Definition GPS_g1cg : Z := 0xcc8.   (* 0x81704, after check_groupa             *)

(* ---- the model facts of one turn ---- *)
Lemma g1_nth_map_bu : forall (l : list byte) i,
  nth i (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth i l (Z_to_bv 8 0)).
Proof. induction l as [|x l IH]; intros [|i]; cbn [map nth]; try reflexivity. apply IH. Qed.

Lemma g1_nth_concat34 : forall (L : list (list byte)) k j, Forall (fun r => length r = 34%nat) L ->
  (k < length L)%nat -> (j < 34)%nat ->
  nth (34 * k + j) (concat L) (Z_to_bv 8 0) = nth j (nth k L []) (Z_to_bv 8 0).
Proof.
  induction L as [|r L IH]; intros k j HF Hk Hj; cbn [length] in Hk; [lia|].
  inversion HF as [|r0 L0 Hr HL]; subst. cbn [concat].
  destruct k as [|k].
  - cbn [nth]. replace (34 * 0 + j)%nat with j by lia. apply app_nth1. lia.
  - rewrite app_nth2 by lia. rewrite Hr. replace (34 * S k + j - 34)%nat with (34 * k + j)%nat by lia.
    cbn [nth]. apply IH; [exact HL | lia | exact Hj].
Qed.

(* Row 11 + 3 * (c - 1) + p of the sweep, which image B indexes as 8 + 3c + p, is Pau's
   group-A row for the channel a.base + c and the value the table gives
   (SweepRowCheck.v nth_row_A, BuildSweepModel.v nth_sweep_vals). *)
Lemma g1_sweep_row : forall T t base w (c p : nat) j, (1 <= c < w)%nat -> (p < 3)%nat -> (j < 34)%nat ->
  0 <= base -> base + Z.of_nat w <= 48 ->
  nth (34 * (11 + 3 * (c - 1) + p) + j)
      (map (fun b : byte => bv_unsigned b) (SWEEP base w (sweep_vals T t base w))) 0 =
  nth j (GAz (base + Z.of_nat c) (Z.of_nat p) (eff T t (base + Z.of_nat c) (Z.of_nat p))) 0.
Proof.
  intros T t base w c p j Hc Hp Hj Hb Hw.
  rewrite g1_nth_map_bu, SWEEP_rows.
  rewrite g1_nth_concat34; [| apply Forall_rowok_len, sweep_rows_ok | | exact Hj].
  2:{ pose proof (length_sweep_rows base w (sweep_vals T t base w) ltac:(lia)). lia. }
  rewrite nth_row_A by first [lia | exact Hp]. unfold ga_row, vz.
  rewrite (nth_sweep_vals T t base w c p (Z_to_bv 8 0)) by lia.
  rewrite bv8_small by (apply eff_range).
  rewrite (Z.mod_small (base + Z.of_nat c)) by lia.
  pose proof (eff_range T t (base + Z.of_nat c) (Z.of_nat p)) as Hv.
  rewrite <- g1_nth_map_bu. unfold GA. rewrite map_unsigned_bl; [reflexivity|].
  apply GA_bytes_range; lia.
Qed.

Lemma g1_sweep_len : forall base w vals, (1 <= w)%nat ->
  Z.of_nat (length (SWEEP base w vals)) = 34 * (8 + 3 * Z.of_nat w).
Proof.
  intros base w vals Hw. rewrite SWEEP_rows.
  assert (HL : forall L : list (list byte), Forall (fun r => length r = 34%nat) L ->
    length (concat L) = (34 * length L)%nat).
  { induction L as [|r L IH]; intros HF; [reflexivity|]. inversion HF; subst. cbn [concat].
    rewrite length_app, IH by assumption. cbn [length]. lia. }
  rewrite HL by (apply Forall_rowok_len, sweep_rows_ok).
  rewrite Nat2Z.inj_mul, length_sweep_rows by lia. reflexivity.
Qed.

Lemma g1_GAz_len : forall ch p v, length (GAz ch p v) = 34%nat.
Proof. reflexivity. Qed.

(* the row of the sweep the turn (c, p) checks: s + 34 * (8 + 3c + p), `mul s9,a0,s5` and
   `add s9,s9,s11` at 0x816a4 / 0x816a8 *)
Definition g1_row (s : Z) (c p : nat) : Z := s + 34 * (8 + 3 * Z.of_nat c + Z.of_nat p).

(* ---- the value-level facts of the seats ---- *)
Lemma g1_afact : forall (E : env) n lo hi v,
  ew E n = Z_to_bv 64 v -> 0 <= lo -> lo <= v <= hi -> hi < 2 ^ 64 -> afact_ok E n (mkAF lo hi 0).
Proof.
  intros E n lo hi v H Hlo Hv Hhi. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite H. rewrite unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
Qed.

Lemma g1_alias_add : forall (E : env) n m r a b,
  ew E n = Z_to_bv 64 a -> ew E m = Z_to_bv 64 b -> ew E r = Z_to_bv 64 (a + b) ->
  0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = sv_denot E (SOff r 0).
Proof.
  intros E n m r a b Hn Hm Hr Ha Hb Hab. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E n a) by first [exact Hn | lia].
  rewrite (U_atom E m b) by first [exact Hm | lia].
  rewrite (U_atom E r (a + b)) by first [exact Hr | lia].
  apply zcanon_id. unfold M64. lia.
Qed.

Lemma g1_alias_and : forall (E : env) n a, ew E n = Z_to_bv 64 a -> 0 <= a < 256 ->
  sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 255)) = sv_denot E (SOff n 0).
Proof.
  intros E n a H Ha. apply U_inj. rewrite U_and_lit by lia.
  rewrite (U_atom E n a) by first [exact H | lia].
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* `mul s9,a0,s5` and `add s9,s9,s11`: s5 holds 34, so the row is s + 34 * (8 + 3c + p). *)
Lemma g1_alias_row : forall (E : env) i s r,
  ew E 37 = Z_to_bv 64 i -> ew E 21 = Z_to_bv 64 34 -> ew E 27 = Z_to_bv 64 s -> ew E 38 = Z_to_bv 64 r ->
  r = s + 34 * i -> 0 <= i < 2 ^ 10 -> 0 <= s -> r < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 37 0) (SOff 21 0)) (SOff 27 0)) = sv_denot E (SOff 38 0).
Proof.
  intros E i s r H37 H21 H27 H38 Hr Hi Hs Hr64. apply U_inj.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
  rewrite (U_atom E 37 i) by first [exact H37 | lia].
  rewrite (U_atom E 21 34) by first [exact H21 | lia].
  rewrite (U_atom E 27 s) by first [exact H27 | lia].
  rewrite (U_atom E 38 r) by first [exact H38 | lia].
  rewrite (zcanon_id (i * 34)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* The UBSan pointer-overflow guard 0x816b0 .. 0x816c0: `sltu a1,s9,s11` is 0 because the
   row does not wrap below s, and `slti a0,a0,0` is 0 because the index is not negative,
   so `xor a0,a1,a0` is 0 and `xori a0,a0,1` is 1: `beqz a0` to the trap is not taken. *)
Lemma g1_alias_ovf : forall (E : env) r s,
  ew E 38 = Z_to_bv 64 r -> ew E 27 = Z_to_bv 64 s -> 0 <= s <= r -> r < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 38 0) (SOff 27 0)) (SLit 0)) = sv_denot E (SLit 0).
Proof.
  intros E r s H38 H27 Hs Hr. apply U_inj.
  rewrite !U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 38 r) by first [exact H38 | lia].
  rewrite (U_atom E 27 s) by first [exact H27 | lia].
  rewrite (proj2 (Z.ltb_ge r s)) by lia.
  rewrite !U_SLit. reflexivity.
Qed.

(* `slli a0,s2,1; add a0,a0,s2` is 3c, which the alias names atom 32 (= 3c + 8) minus 8,
   so that `addiw s4,a0,8` is atom 32 itself. *)
Lemma g1_alias_mul3 : forall (E : env) c,
  ew E 18 = Z_to_bv 64 c -> ew E 32 = Z_to_bv 64 (8 + 3 * c) -> 0 <= c < 2 ^ 40 ->
  sv_denot E (SMd M_MUL (SOff 18 0) (SLit 3)) = sv_denot E (SOff 32 (-8)).
Proof.
  intros E c H18 H32 Hc. apply U_inj.
  rewrite U_SMd. cbn [zmd_raw].
  rewrite (U_atom E 18 c) by first [exact H18 | lia].
  rewrite (U_lit E 3) by lia.
  rewrite (U_atom_off E 32 (8 + 3 * c) (-8)) by first [exact H32 | lia].
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma g1_sv_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma g1_VB : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> YP09.base_val E (Some n) = v.
Proof. intros E n v H Hv. cbn [YP09.base_val]. rewrite H. apply unsigned_lit_small. exact Hv. Qed.

Lemma g1_zeq64 : forall a b : Z, a = b -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b ->. reflexivity. Qed.

Lemma g1_zeq64m : forall a b : Z, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
  intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). exact H.
Qed.

(* ---- the registers a turn keeps ---- *)
(* From the head of the parameter loop to the return of check_groupa: sp, gp, tp, s0, s1,
   s2 = c, s3 = the frame's shadow, s4 = 3c + 8, s5 = 34, s6 = 3, s7 = p, s11 = s. *)
Definition g1_kl : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 27]%bv.

Lemma g1_in_bv5 : forall (r : bv 5) (l : list (bv 5)),
  existsb (fun x : bv 5 => bv_unsigned x =? bv_unsigned r) l = true -> In r l.
Proof.
  intros r l. induction l as [|x l IH]; cbn [existsb In]; [discriminate|].
  intros H. apply orb_prop in H as [H|H]; [left; apply bv_eq; apply Z.eqb_eq; exact H | right; apply IH; exact H].
Qed.
Ltac g1_kl_in := unfold g1_kl; apply g1_in_bv5; vm_compute; reflexivity.

Lemma g1_kl_ap : forall (r0 r1 : bvmap 5 word), aregs_preserved r0 r1 ->
  forall r : bv 5, In r g1_kl -> getr r1 r = getr r0 r.
Proof.
  intros r0 r1 H r Hr. unfold g1_kl in Hr.
  destruct Hr as [<-|Hr]; [apg H (2%bv : bv 5) 2; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (3%bv : bv 5) 3; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (4%bv : bv 5) 4; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (8%bv : bv 5) 8; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (9%bv : bv 5) 9; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (18%bv : bv 5) 18; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (19%bv : bv 5) 19; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (20%bv : bv 5) 20; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (21%bv : bv 5) 21; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (22%bv : bv 5) 22; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (23%bv : bv 5) 23; reflexivity|].
  destruct Hr as [<-|Hr]; [apg H (27%bv : bv 5) 27; reflexivity|].
  destruct Hr.
Qed.

(* ---- the symbolic states of this part ---- *)
(* A window of the machine frame with the spill slots a run reads back, and the two bytes
   of `a` (a.base and a.width) as the region of `a`'s address. Both are read-only. *)
Definition g1_RS (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 9%nat) 0 192 0 0 cs.
Definition g1_RA (nb n0 n1 : nat) : YP09.region :=
  YP09.mkRegion (Some nb) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SOff n0 0)); YP09.mkChunk 1 (CVal 1 (SOff n1 0))].

(* The head of the parameter loop, 0x81694, to the call of want_of at 0x816e8. Atoms: 32 the
   address of `a` (slot 120), 33 set_to (slot 128), 34 was_set (slot 136), 35 a.base, 36
   a.width, 37 the index 8 + 3c + p, 38 the row s + 34 * (8 + 3c + p), 39 the channel
   a.base + c. The facts and aliases decide the three UBSan guards of the turn:
   0x8169c (`addw a1,s4,s7` is the 64-bit sum, as s4 in 11 .. 125 and s7 in 0 .. 2),
   0x816ac (the row is at least 4096) and 0x816c0 (`g1_alias_ovf`, and the index is at
   least 11, so `slti a0,a0,0` is 0). *)
Definition g1_regions : YP09.smem :=
  [g1_RS [YP09.mkChunk 120 (CVal 8 (SOff 32 0)); YP09.mkChunk 128 (CVal 8 (SOff 33 0));
          YP09.mkChunk 136 (CVal 8 (SOff 34 0))];
   g1_RA 32 35 36].
Definition g1_atoms : list (nat * afact) :=
  [(20%nat, mkAF 11 125 0); (23%nat, mkAF 0 2 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0);
   (37%nat, mkAF 11 127 0); (38%nat, mkAF 4096 (2 ^ 47) 0); (39%nat, mkAF 0 255 0)].
Definition g1_alias : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 20 0) (SOff 23 0), SOff 37 0);
    (SAlu ALU_ADD (SMd M_MUL (SOff 37 0) (SOff 21 0)) (SOff 27 0), SOff 38 0);
    (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 38 0) (SOff 27 0)) (SLit 0), SLit 0);
    (SAlu ALU_ADD (SOff 35 0) (SOff 18 0), SOff 39 0);
    (SAlu ALU_AND (SOff 39 0) (SLit 255), SOff 39 0);
    (SAlu ALU_AND (SOff 23 0) (SLit 255), SOff 23 0) ].
Definition ss_g1 : sstate := mkSS GPS_g1in sr_atoms g1_regions None (mkFacts g1_atoms [] g1_alias).

(* After want_of, 0x816ec, to the call of check_groupa at 0x81700: atom 32 is the table
   (slot 152), which `ld a3,152(s1)` reads. *)
Definition ss_g1hd : sstate :=
  mkSS GPS_g1hd sr_atoms [g1_RS [YP09.mkChunk 152 (CVal 8 (SOff 32 0))]] None (mkFacts [] [] []).

(* After check_groupa, 0x81704: the two loop tests, and a.width read again at 0x81710.
   Atoms: 32 the address of `a` (slot 120), 33 a.base, 34 a.width. *)
Definition ss_g1cg : sstate :=
  mkSS GPS_g1cg sr_atoms [g1_RS [YP09.mkChunk 120 (CVal 8 (SOff 32 0))]; g1_RA 32 33 34] None
    (mkFacts [(18%nat, mkAF 1 39 0); (23%nat, mkAF 0 2 0); (34%nat, mkAF 0 255 0)] [] []).

(* The head of the channel loop, 0x81684, to the head of the parameter loop: atom 32 is
   3c + 8, which `addiw s4,a0,8` at 0x81690 computes. *)
Definition ss_g1o : sstate :=
  mkSS GPS_ga1 sr_atoms [] None
    (mkFacts [(32%nat, mkAF 11 125 0)] [] [(SMd M_MUL (SOff 18 0) (SLit 3), SOff 32 (-8))]).

(* The memory a run over read-only regions leaves: the one it started from. *)
Ltac g1_mem HM :=
  lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
    pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM end;
  cbn [ms_mem mkst] in HM;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* A register the engine gives as an atom plus an offset, as the cut's number. *)
Ltac g1_zreg Q EQ :=
  rewrite Q; rewrite ?EQ; rewrite ?alu64_add_lit; rewrite ?unsigned_lit_small by lia;
  first [ reflexivity | apply g1_zeq64; lia | apply g1_zeq64m; reflexivity
        | match goal with |- ?g => fail 100 "g1_zreg GOAL" g end ].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma g1_awr_ro : forall E rs STK sp0 FP bl0 blc ly own,
  rs_read_only rs = true -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
  intros E rs STK sp0 FP bl0 blc ly own H. induction rs as [|r rs IH]; [apply awr_ok_nil|].
  cbn [rs_read_only forallb] in H. apply andb_prop in H as [H1 H2].
  apply awr_ok_cons_ro; [apply Z.leb_le; exact H1 | apply IH; exact H2].
Qed.
(* The write check of a run over read-only regions. *)
Ltac g1_awr := apply g1_awr_ro; vm_compute; reflexivity.
Section b.
Context {PI : PAImg grant_listing}.
Context {RO : ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition g1_E (regs : bvmap 5 word) (xs : list Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) xs)).

Lemma g1_E_reg : forall (regs : bvmap 5 word) xs n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (g1_E regs xs) n = getr regs r.
Proof. intros regs xs n r Hn. unfold g1_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma g1_E_x : forall (regs : bvmap 5 word) xs j, (32 + j < A_TEXT)%nat ->
  ew (g1_E regs xs) (32 + j) = Z_to_bv 64 (nth j xs 0).
Proof.
  intros regs xs j Hj. unfold g1_E. rewrite Eimg_low by exact Hj. rewrite ew_Ereg_extra.
  exact (map_nth (Z_to_bv 64) xs 0 j).
Qed.

(* the atoms 32 .. 39 of the parameter loop's seat *)
Definition g1_xs (cx : ecx) (fp s : Z) (c p : nat) : list Z :=
  [gF cx fp + GO_A; gF cx fp + GO_SET; gF cx fp + GO_WAS; sw_base (c_pl cx); sw_in (c_pl cx);
   8 + 3 * Z.of_nat c + Z.of_nat p; g1_row s c p; sw_base (c_pl cx) + Z.of_nat c].

(* The two bytes of `a` as the region of its address. *)
Lemma g1_rokA : forall E (H : word -> bool) mem (nb n0 n1 : nat) A b i,
  ew E nb = Z_to_bv 64 A -> ew E n0 = Z_to_bv 64 b -> ew E n1 = Z_to_bv 64 i ->
  aview SEGS H mem A = Some b -> aview SEGS H mem (A + 1) = Some i ->
  0 <= A -> A + 2 <= 2 ^ 64 ->
  YP09.region_ok SEGS E (mrestrict H mem) (g1_RA nb n0 n1).
Proof.
  intros E H mem nb n0 n1 A b i Eb E0 E1 Hb Hi HA0 HA1.
  pose proof (gs_val_mem_of_byte H mem A b Hb) as Vb. pose proof (gs_byte_range H mem A b Hb) as Rb.
  pose proof (gs_val_mem_of_byte H mem (A + 1) i Hi) as Vi. pose proof (gs_byte_range H mem (A + 1) i Hi) as Ri.
  unfold YP09.region_ok, g1_RA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (g1_VB E nb A Eb) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val SEGS E _ A 0 1 (SOff n0 0) b); [rewrite g1_sv_SOff0; exact E0 | zside | zside |].
    rewrite Z.add_0_r. exact Vb.
  - apply (chunk_ok_val SEGS E _ A 1 1 (SOff n1 0) i); [rewrite g1_sv_SOff0; exact E1 | zside | zside |].
    exact Vi.
Qed.

(* The seat at the head of the parameter loop, 0x81694, from the cut's registers, spill
   slots and the two bytes of `a`. *)
Lemma g1_seat : forall cx fp s (c p : nat) (W : world SEGS) (regs : bvmap 5 word) mem,
  getr regs 9 = w64 (c_sp1 cx) -> getr regs 18 = w64 (Z.of_nat c) ->
  getr regs 20 = w64 (8 + 3 * Z.of_nat c) -> getr regs 21 = w64 34 ->
  getr regs 23 = w64 (Z.of_nat p) -> getr regs 27 = w64 s ->
  0 <= c_sp1 cx -> c_sp1 cx + 192 <= 2 ^ 64 ->
  0 <= gF cx fp -> gF cx fp + GO_A + 2 <= c_sp1 cx ->
  (1 <= c)%nat -> Z.of_nat c <= 39 -> (p < 3)%nat ->
  0 <= sw_base (c_pl cx) -> sw_base (c_pl cx) + Z.of_nat c < 256 ->
  4096 <= s -> g1_row s c p <= 2 ^ 47 ->
  rdword (aview SEGS (w_H W) mem) (c_sp1 cx + 120) = Some (gF cx fp + GO_A) ->
  rdword (aview SEGS (w_H W) mem) (c_sp1 cx + 128) = Some (gF cx fp + GO_SET) ->
  rdword (aview SEGS (w_H W) mem) (c_sp1 cx + 136) = Some (gF cx fp + GO_WAS) ->
  aview SEGS (w_H W) mem (gF cx fp + GO_A) = Some (sw_base (c_pl cx)) ->
  aview SEGS (w_H W) mem (gF cx fp + (GO_A + 1)) = Some (sw_in (c_pl cx)) ->
  st_ok_pi SEGS VAL (g1_E regs (g1_xs cx fp s c p)) ss_g1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + GPS_g1in)) mem (seg_rom SEGS))).
Proof.
  intros cx fp s c p W regs mem R9 R18 R20 R21 R23 R27 Hsp0 Hsp1 HF0 HFA Hc1 Hc39 Hp3 Hb0 Hch Hs4 HR
    S120 S128 S136 A0 A1.
  rewrite Z.add_assoc in A1.
  pose proof (gs_byte_range _ _ _ _ A0) as Rb0. pose proof (gs_byte_range _ _ _ _ A1) as Rb1.
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (g1_E regs (g1_xs cx fp s c p)) n = getr regs r)
    by (intros n r Hn; apply g1_E_reg; exact Hn).
  assert (E32 : ew (g1_E regs (g1_xs cx fp s c p)) 32 = Z_to_bv 64 (gF cx fp + GO_A))
    by exact (g1_E_x _ _ 0 ltac:(cbv; lia)).
  assert (E33 : ew (g1_E regs (g1_xs cx fp s c p)) 33 = Z_to_bv 64 (gF cx fp + GO_SET))
    by exact (g1_E_x _ _ 1 ltac:(cbv; lia)).
  assert (E34 : ew (g1_E regs (g1_xs cx fp s c p)) 34 = Z_to_bv 64 (gF cx fp + GO_WAS))
    by exact (g1_E_x _ _ 2 ltac:(cbv; lia)).
  assert (E35 : ew (g1_E regs (g1_xs cx fp s c p)) 35 = Z_to_bv 64 (sw_base (c_pl cx)))
    by exact (g1_E_x _ _ 3 ltac:(cbv; lia)).
  assert (E36 : ew (g1_E regs (g1_xs cx fp s c p)) 36 = Z_to_bv 64 (sw_in (c_pl cx)))
    by exact (g1_E_x _ _ 4 ltac:(cbv; lia)).
  assert (E37 : ew (g1_E regs (g1_xs cx fp s c p)) 37 = Z_to_bv 64 (8 + 3 * Z.of_nat c + Z.of_nat p))
    by exact (g1_E_x _ _ 5 ltac:(cbv; lia)).
  assert (E38 : ew (g1_E regs (g1_xs cx fp s c p)) 38 = Z_to_bv 64 (g1_row s c p))
    by exact (g1_E_x _ _ 6 ltac:(cbv; lia)).
  assert (E39 : ew (g1_E regs (g1_xs cx fp s c p)) 39 = Z_to_bv 64 (sw_base (c_pl cx) + Z.of_nat c))
    by exact (g1_E_x _ _ 7 ltac:(cbv; lia)).
  assert (E9 : ew (g1_E regs (g1_xs cx fp s c p)) 9 = Z_to_bv 64 (c_sp1 cx))
    by (rewrite (ER 9%nat 9%bv eq_refl); exact R9).
  assert (E18 : ew (g1_E regs (g1_xs cx fp s c p)) 18 = Z_to_bv 64 (Z.of_nat c))
    by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E20 : ew (g1_E regs (g1_xs cx fp s c p)) 20 = Z_to_bv 64 (8 + 3 * Z.of_nat c))
    by (rewrite (ER 20%nat 20%bv eq_refl); exact R20).
  assert (E21 : ew (g1_E regs (g1_xs cx fp s c p)) 21 = Z_to_bv 64 34)
    by (rewrite (ER 21%nat 21%bv eq_refl); exact R21).
  assert (E23 : ew (g1_E regs (g1_xs cx fp s c p)) 23 = Z_to_bv 64 (Z.of_nat p))
    by (rewrite (ER 23%nat 23%bv eq_refl); exact R23).
  assert (E27 : ew (g1_E regs (g1_xs cx fp s c p)) 27 = Z_to_bv 64 s)
    by (rewrite (ER 27%nat 27%bv eq_refl); exact R27).
  assert (U9 : bv_unsigned (ew (g1_E regs (g1_xs cx fp s c p)) 9%nat) = c_sp1 cx)
    by (rewrite E9; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold ss_g1. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold g1_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold g1_RS. apply (gs_slotreg_ok W _ mem _ (c_sp1 cx) 0 0 U9 Hsp0 Hsp1 ltac:(intros o Ho; lia)).
      repeat apply Forall_cons; try apply Forall_nil.
      * exact (gs_slot_chunk W _ mem 120 32 _ (c_sp1 cx) E32 U9 S120).
      * exact (gs_slot_chunk W _ mem 128 33 _ (c_sp1 cx) E33 U9 S128).
      * exact (gs_slot_chunk W _ mem 136 34 _ (c_sp1 cx) E34 U9 S136).
    + apply (g1_rokA _ _ mem 32 35 36 (gF cx fp + GO_A) (sw_base (c_pl cx)) (sw_in (c_pl cx)) E32 E35 E36 A0 A1);
        unfold GO_A in *; lia.
  - unfold g1_regions, g1_RS, g1_RA. cbn [YP09.pairwise_disjoint YP09.all_disjoint].
    unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (g1_VB _ 9 _ E9) by lia. rewrite (g1_VB _ 32 _ E32) by (unfold GO_A in *; lia).
    unfold GO_A in *. repeat split; lia.
  - split; [| split; [exact I |]].
    + unfold g1_atoms. cbn [f_atoms atoms_ok].
      split; [exact (g1_afact _ 20 11 125 _ E20 ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [exact (g1_afact _ 23 0 2 _ E23 ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [exact (g1_afact _ 35 0 255 _ E35 ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [exact (g1_afact _ 36 0 255 _ E36 ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [exact (g1_afact _ 37 11 127 _ E37 ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [exact (g1_afact _ 38 4096 (2 ^ 47) _ E38 ltac:(lia) ltac:(unfold g1_row in *; lia) ltac:(lia))|].
      split; [exact (g1_afact _ 39 0 255 _ E39 ltac:(lia) ltac:(lia) ltac:(lia)) | exact I].
    + unfold g1_alias. cbn [f_alias alias_ok].
      (* 0x81694 `add a0,s4,s7` (and `addw a1,s4,s7`, which the facts on atoms 20 and 23 make
         the same sum): the index 8 + 3c + p *)
      split; [exact (g1_alias_add _ 20 23 37 _ _ E20 E23 E37 ltac:(lia) ltac:(lia) ltac:(lia))|].
      (* 0x816a4 / 0x816a8: the row *)
      split; [exact (g1_alias_row _ _ s _ E37 E21 E27 E38 ltac:(unfold g1_row; lia) ltac:(lia) ltac:(lia)
                       ltac:(lia))|].
      (* 0x816b0 .. 0x816b8: the row does not wrap below s *)
      split; [exact (g1_alias_ovf _ _ s E38 E27 ltac:(unfold g1_row in *; lia) ltac:(lia))|].
      (* 0x816cc `add a0,a0,s2`: the channel a.base + c *)
      split; [exact (g1_alias_add _ 35 18 39 _ _ E35 E18 E39 ltac:(lia) ltac:(lia) ltac:(lia))|].
      (* 0x816d0 `andi s8,a0,0xff` and 0x816d4 `andi s10,s7,0xff`: the masks change nothing *)
      split; [exact (g1_alias_and _ 39 _ E39 ltac:(lia))|].
      split; [exact (g1_alias_and _ 23 _ E23 ltac:(lia)) | exact I].
Qed.

(* The seat after want_of, 0x816ec, from the table's spill slot. *)
Lemma g1_seat2 : forall (cx : ecx) t (W : world SEGS) (regs : bvmap 5 word) mem,
  getr regs 9 = w64 (c_sp1 cx) -> 0 <= c_sp1 cx -> c_sp1 cx + 192 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) mem) (c_sp1 cx + 152) = Some t ->
  st_ok_pi SEGS VAL (g1_E regs [t]) ss_g1hd
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + GPS_g1hd)) mem (seg_rom SEGS))).
Proof.
  intros cx t W regs mem R9 Hsp0 Hsp1 S152.
  assert (U9 : bv_unsigned (ew (g1_E regs [t]) 9%nat) = c_sp1 cx)
    by (rewrite (g1_E_reg _ _ 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold ss_g1hd. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold g1_RS. apply (gs_slotreg_ok W _ mem _ (c_sp1 cx) 0 0 U9 Hsp0 Hsp1 ltac:(intros o Ho; lia)).
    apply Forall_cons; [|apply Forall_nil].
    exact (gs_slot_chunk W _ mem 152 32 _ (c_sp1 cx) (g1_E_x _ _ 0 ltac:(cbv; lia)) U9 S152).
  - cbn. tauto.
  - split; [exact I | split; exact I].
Qed.

(* The seat after check_groupa, 0x81704. *)
Lemma g1_seat3 : forall cx fp (c p : nat) (W : world SEGS) (regs : bvmap 5 word) mem,
  getr regs 9 = w64 (c_sp1 cx) -> getr regs 18 = w64 (Z.of_nat c) -> getr regs 23 = w64 (Z.of_nat p) ->
  0 <= c_sp1 cx -> c_sp1 cx + 192 <= 2 ^ 64 ->
  0 <= gF cx fp -> gF cx fp + GO_A + 2 <= c_sp1 cx ->
  (1 <= c)%nat -> Z.of_nat c <= 39 -> (p < 3)%nat ->
  rdword (aview SEGS (w_H W) mem) (c_sp1 cx + 120) = Some (gF cx fp + GO_A) ->
  aview SEGS (w_H W) mem (gF cx fp + GO_A) = Some (sw_base (c_pl cx)) ->
  aview SEGS (w_H W) mem (gF cx fp + (GO_A + 1)) = Some (sw_in (c_pl cx)) ->
  st_ok_pi SEGS VAL (g1_E regs [gF cx fp + GO_A; sw_base (c_pl cx); sw_in (c_pl cx)]) ss_g1cg
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + GPS_g1cg)) mem (seg_rom SEGS))).
Proof.
  intros cx fp c p W regs mem R9 R18 R23 Hsp0 Hsp1 HF0 HFA Hc1 Hc39 Hp3 S120 A0 A1.
  rewrite Z.add_assoc in A1.
  pose proof (gs_byte_range _ _ _ _ A0) as Rb0. pose proof (gs_byte_range _ _ _ _ A1) as Rb1.
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
    ew (g1_E regs [gF cx fp + GO_A; sw_base (c_pl cx); sw_in (c_pl cx)]) n = getr regs r)
    by (intros n r Hn; apply g1_E_reg; exact Hn).
  assert (E32 : ew (g1_E regs [gF cx fp + GO_A; sw_base (c_pl cx); sw_in (c_pl cx)]) 32 = Z_to_bv 64 (gF cx fp + GO_A))
    by exact (g1_E_x _ _ 0 ltac:(cbv; lia)).
  assert (E33 : ew (g1_E regs [gF cx fp + GO_A; sw_base (c_pl cx); sw_in (c_pl cx)]) 33 = Z_to_bv 64 (sw_base (c_pl cx)))
    by exact (g1_E_x _ _ 1 ltac:(cbv; lia)).
  assert (E34 : ew (g1_E regs [gF cx fp + GO_A; sw_base (c_pl cx); sw_in (c_pl cx)]) 34 = Z_to_bv 64 (sw_in (c_pl cx)))
    by exact (g1_E_x _ _ 2 ltac:(cbv; lia)).
  assert (E9 : ew (g1_E regs [gF cx fp + GO_A; sw_base (c_pl cx); sw_in (c_pl cx)]) 9 = Z_to_bv 64 (c_sp1 cx))
    by (rewrite (ER 9%nat 9%bv eq_refl); exact R9).
  assert (E18 : ew (g1_E regs [gF cx fp + GO_A; sw_base (c_pl cx); sw_in (c_pl cx)]) 18 = Z_to_bv 64 (Z.of_nat c))
    by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E23 : ew (g1_E regs [gF cx fp + GO_A; sw_base (c_pl cx); sw_in (c_pl cx)]) 23 = Z_to_bv 64 (Z.of_nat p))
    by (rewrite (ER 23%nat 23%bv eq_refl); exact R23).
  assert (U9 : bv_unsigned (ew (g1_E regs [gF cx fp + GO_A; sw_base (c_pl cx); sw_in (c_pl cx)]) 9%nat) = c_sp1 cx)
    by (rewrite E9; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold ss_g1cg. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold g1_RS. apply (gs_slotreg_ok W _ mem _ (c_sp1 cx) 0 0 U9 Hsp0 Hsp1 ltac:(intros o Ho; lia)).
      apply Forall_cons; [|apply Forall_nil].
      exact (gs_slot_chunk W _ mem 120 32 _ (c_sp1 cx) E32 U9 S120).
    + apply (g1_rokA _ _ mem 32 33 34 (gF cx fp + GO_A) (sw_base (c_pl cx)) (sw_in (c_pl cx)) E32 E33 E34 A0 A1);
        unfold GO_A in *; lia.
  - unfold g1_RS, g1_RA. cbn [YP09.pairwise_disjoint YP09.all_disjoint].
    unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (g1_VB _ 9 _ E9) by lia. rewrite (g1_VB _ 32 _ E32) by (unfold GO_A in *; lia).
    unfold GO_A in *. repeat split; lia.
  - split; [| split; [exact I | exact I]].
    cbn [f_atoms atoms_ok].
    split; [exact (g1_afact _ 18 1 39 _ E18 ltac:(lia) ltac:(lia) ltac:(lia))|].
    split; [exact (g1_afact _ 23 0 2 _ E23 ltac:(lia) ltac:(lia) ltac:(lia))|].
    split; [exact (g1_afact _ 34 0 255 _ E34 ltac:(lia) ltac:(lia) ltac:(lia)) | exact I].
Qed.

(* The seat at the head of the channel loop, 0x81684. *)
Lemma g1_seat_o : forall (c : nat) (W : world SEGS) (regs : bvmap 5 word) mem,
  getr regs 18 = w64 (Z.of_nat c) -> (1 <= c)%nat -> Z.of_nat c <= 39 ->
  st_ok_pi SEGS VAL (g1_E regs [8 + 3 * Z.of_nat c]) ss_g1o
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + GPS_ga1)) mem (seg_rom SEGS))).
Proof.
  intros c W regs mem R18 Hc1 Hc39.
  assert (E18 : ew (g1_E regs [8 + 3 * Z.of_nat c]) 18 = Z_to_bv 64 (Z.of_nat c))
    by (rewrite (g1_E_reg _ _ 18 18%bv eq_refl); exact R18).
  assert (E32 : ew (g1_E regs [8 + 3 * Z.of_nat c]) 32 = Z_to_bv 64 (8 + 3 * Z.of_nat c))
    by exact (g1_E_x _ _ 0 ltac:(cbv; lia)).
  rewrite restrict_mkst_fx. unfold ss_g1o. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [| split; [exact I |]].
    + cbn [f_atoms atoms_ok].
      split; [exact (g1_afact _ 32 11 125 _ E32 ltac:(lia) ltac:(lia) ltac:(lia)) | exact I].
    + cbn [f_alias alias_ok].
      split; [exact (g1_alias_mul3 _ (Z.of_nat c) E18 E32 ltac:(lia)) | exact I].
Qed.

(* The two words of the machine frame a callee's call chain needs: ra and s0. *)
Lemma g1_saved : forall cx (W3 : world SEGS) (ms : machine_state), gsaved cx W3 ms ->
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) /\
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)).
Proof.
  intros cx W3 ms (H8 & HJ). split; [exact H8|].
  pose proof (HJ 0 ltac:(lia)) as Hj0.
  replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in Hj0 by lia.
  cbn [Z.ltb Z.compare] in Hj0. exact Hj0.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the invariant of one turn, at the three pcs it passes ---- *)
Definition g1_at (pc : Z) (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (t s : Z) (c p : nat) : Prop :=
  ge_body cx fp pc W3 ms3 GSH_a /\ k <= 2 /\ acc <= GE_A2 MT - mo_free MT /\
  gsw_blk B cx fp ly3 S3 W3 ms3 t s /\ gsw_rows cx W3 ms3 t s /\
  gslot cx W3 ms3 88 (2 ^ 64 - 1 - s) /\
  (1 <= c)%nat /\ Z.of_nat c < sw_in (c_pl cx) /\ (p < 3)%nat /\
  getr (ms_regs ms3) 18 = w64 (Z.of_nat c) /\
  getr (ms_regs ms3) 20 = w64 (8 + 3 * Z.of_nat c) /\
  getr (ms_regs ms3) 21 = w64 34 /\ getr (ms_regs ms3) 22 = w64 3 /\
  getr (ms_regs ms3) 23 = w64 (Z.of_nat p) /\
  getr (ms_regs ms3) 27 = w64 s /\ getr (ms_regs ms3) 19 = w64 (gSH cx fp).

(* What the walk hands to the next cut inside the turn. *)
Definition g1_K (POST : ecx -> world SEGS -> config -> Prop) (pc : Z) (cx : ecx) (fp k acc t s : Z)
  (c p : nat) : Prop :=
  forall ly4 S4 W4 (ms4 : machine_state) md4,
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly4 S4 W4 (ms_mem ms4) md4 k ->
  YG01.frames S4 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S4 acc ->
  g1_at pc cx fp k acc ly4 S4 W4 ms4 t s c p ->
  SRr SEGS W4 (mkCfg ms4 md4) (POST cx).

Section d.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTF : ameter_fs_laws MT.
(* The two program functions a turn calls, by their own contracts. *)
Hypothesis WOF : tb_want_of_spec B.
Hypothesis TCG : tb_check_groupa_spec B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the call of check_groupa at 0x81700 and the landing at 0x81704 ---- *)
(* `ms0` is the state at the head of the parameter loop; want_of and the two runs kept
   every register of `g1_kl` and every byte the cuts name. *)
Lemma g1_call : forall POST cx fp k acc ly3 S3 W3 (ms0 : machine_state) (regsT : bvmap 5 word) memT mdT
  t s c p,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 memT mdT k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  g1_at GPS_g1in cx fp k acc ly3 S3 W3 ms0 t s c p ->
  vkeep (gsw_out cx fp t s) W3 (ms_mem ms0) W3 memT ->
  (forall r : bv 5, In r g1_kl -> getr regsT r = getr (ms_regs ms0) r) ->
  getr regsT 1 = Z_to_bv 64 (BASE + GPS_g1cg) ->
  getr regsT 10 = w64 (g1_row s c p) ->
  getr regsT 11 = w64 (sw_base (c_pl cx) + Z.of_nat c) ->
  getr regsT 12 = w64 (Z.of_nat p) ->
  getr regsT 13 = w64 t ->
  getr regsT 14 = w64 (eff (T_end (c_pl cx)) t (sw_base (c_pl cx) + Z.of_nat c) (Z.of_nat p)) ->
  g1_K POST GPS_g1cg cx fp k acc t s c p ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA GS_check_groupa)) memT (seg_rom SEGS)) mdT) (POST cx).
Proof.
  intros POST cx fp k acc ly3 S3 W3 ms0 regsT memT mdT t s c p HB HJ HFR Hmo HG VK0 KR
    Rra R10 R11 R12 R13 R14 K.
  destruct HG as (HBD & Hk & Hacc & HBLK & HROWS & H88 & Hc1 & Hc2 & Hp3 & R18 & R20 & R21 & R22 & R23
    & R27 & R19).
  pose proof HBD as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & (S8 & S16) & _).
  pose proof HBLK as (Hab & Hins & (Hint & _) & _ & _ & _ & _ & _ & _ & _ & _ & Hok & _).
  pose proof HROWS as (Hwant & HSW).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 memT mdT t s HB HJ HFR Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0 & Htc & Hs0 & Hsc & HPB).
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0.
  (* gs_ok_range (LLVMFEntrySweepS1c.v): 0 <= a.base, 1 <= a.width <= 40, a.base + a.width <= 48 *)
  pose proof (gs_ok_range _ Hok) as (Bb0 & (Bi1 & Bi40) & Bbi).
  pose proof (sw_bytes_len cx t Hok Hwant) as Hswl.
  assert (Hsweep : Z.of_nat (length (sw_bytes (c_pl cx) t)) = 34 * (8 + 3 * sw_in (c_pl cx))).
  { unfold sw_bytes. rewrite g1_sweep_len by lia. rewrite Z2Nat.id by lia. reflexivity. }
  assert (BLKT : gsw_blk B cx fp ly3 S3 W3 (mkst regsT (Z_to_bv 64 0) memT (seg_rom SEGS)) t s)
    by exact (gsw_blk_move B cx fp ly3 S3 W3 ms0 ly3 S3 W3 (mkst regsT (Z_to_bv 64 0) memT (seg_rom SEGS)) t s
                HBLK eq_refl VK0 ltac:(lia)).
  assert (H8 : rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx))).
  { eapply rdword_vkeep; [exact VK0 | | exact S8]. intros kk Hkk. left; left. lia. }
  assert (H16 : rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { pose proof (S16 0 ltac:(lia)) as Hj0.
    replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in Hj0 by lia.
    cbn [Z.ltb Z.compare] in Hj0.
    eapply rdword_vkeep; [exact VK0 | | exact Hj0]. intros kk Hkk. left; left. lia. }
  (* row 8 + 3c + p = 11 + 3 (c - 1) + p of the sweep: Pau's group-A row for the channel
     a.base + c, p and the value the table gives *)
  assert (HROW : garr8 SEGS (mrestrict (w_H W3) memT) (g1_row s c p)
    (GAz (sw_base (c_pl cx) + Z.of_nat c) (Z.of_nat p)
         (eff (T_end (c_pl cx)) t (sw_base (c_pl cx) + Z.of_nat c) (Z.of_nat p)))).
  { replace (g1_row s c p) with (s + Z.of_nat (34 * (11 + 3 * (c - 1) + p))) by (unfold g1_row; lia).
    apply (garr8_slice _ s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) _
      (34 * (11 + 3 * (c - 1) + p))).
    - eapply garr8_vkeep; [exact VK0 | | exact HSW].
      intros a Ha. rewrite length_map in Ha. right; right. lia.
    - rewrite length_map, g1_GAz_len. lia.
    - intros j Hj. rewrite g1_GAz_len in Hj. unfold sw_bytes, sw_vals.
      apply g1_sweep_row; lia. }
  assert (Q2 : getr regsT 2 = w64 (c_sp1 cx)) by (rewrite KR by g1_kl_in; exact G2).
  assert (Q3 : getr regsT 3 = getr (c_regs cx) 3) by (rewrite KR by g1_kl_in; exact G3).
  assert (Q4 : getr regsT 4 = getr (c_regs cx) 4) by (rewrite KR by g1_kl_in; exact G4).
  assert (Q8 : getr regsT 8 = w64 (spZ (c_regs cx))) by (rewrite KR by g1_kl_in; exact G8).
  eapply SRr_bind.
  { (* ch = a.base + c in 0 .. 47 and p < 3 as for want_of (g1_in); the row lies inside the
       sweep, as 9 + 3c + p <= 8 + 3 a.width (c < a.width, p < 3) *)
    exact (gsw_cga B MT LAWS TCG cx fp k ly3 S3 W3 regsT memT mdT GPS_g1cg t s (g1_row s c p)
      (sw_base (c_pl cx) + Z.of_nat c) (Z.of_nat p) HB HJ HFR BLKT Q2 Q3 Q4 Q8 Rra
      ltac:(unfold GPS_g1cg; lia) eq_refl H8 H16 R10 R11 R12 R13 R14
      ltac:(lia) ltac:(lia) ltac:(unfold g1_row; lia) ltac:(unfold g1_row; lia) HROW). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hfr2 & Hab2 & (f & Hfs) & HP2 & HK2).
  assert (VK : vkeep (gsw_out cx fp t s) W3 (ms_mem ms0) W2 mem2) by exact (vkeep_trans _ _ _ _ _ _ _ VK0 HK2).
  assert (KP : forall r : bv 5, In r g1_kl -> getr regs2 r = getr (ms_regs ms0) r).
  { intros r Hr. rewrite (g1_kl_ap _ _ HP2 r Hr). exact (KR r Hr). }
  apply (K ly2 S2 W2 (mkst regs2 (Z_to_bv 64 (BASE + GPS_g1cg)) mem2 (seg_rom SEGS)) md2).
  - exact HJ2.
  - rewrite Hfr2. exact HFR.
  - rewrite Hfs. apply (mo_le_set_fs_r MT MTF). exact Hmo.
  - unfold g1_at.
    split.
    { apply (ge_body_move cx fp GPS_g1in GPS_g1cg W3 W2 ms0 regs2 mem2 GSH_a HBD).
      - eapply vkeep_sub; [| exact VK]. intros a Ha. left. exact Ha.
      - lia.
      - apply KP; g1_kl_in.
      - apply KP; g1_kl_in.
      - apply KP; g1_kl_in.
      - apply KP; g1_kl_in.
      - apply KP; g1_kl_in. }
    split; [exact Hk|]. split; [exact Hacc|].
    split; [eapply gsw_blk_move; [exact HBLK | exact Hab2 | exact VK | lia]|].
    split; [eapply gsw_rows_move; [exact Hok | exact HROWS | exact VK]|].
    split; [unfold gslot; unfold gslot in H88; eapply rdword_vkeep; [exact VK | | exact H88];
            intros kk Hkk; left; left; lia|].
    split; [exact Hc1|]. split; [exact Hc2|]. split; [exact Hp3|].
    cbn [ms_regs mkst].
    split; [rewrite KP by g1_kl_in; exact R18|].
    split; [rewrite KP by g1_kl_in; exact R20|].
    split; [rewrite KP by g1_kl_in; exact R21|].
    split; [rewrite KP by g1_kl_in; exact R22|].
    split; [rewrite KP by g1_kl_in; exact R23|].
    split; [rewrite KP by g1_kl_in; exact R27|].
    rewrite KP by g1_kl_in. exact R19.
Qed.

(* ---- one turn: 0x81694 -> the call of check_groupa at 0x81700 ---- *)
Lemma g1_in : forall POST cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3 t s c p,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  g1_at GPS_g1in cx fp k acc ly3 S3 W3 ms3 t s c p ->
  g1_K POST GPS_g1cg cx fp k acc t s c p ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST cx fp k acc ly3 S3 W3 ms3 md3 t s c p HB HJ HFR Hmo HG K.
  pose proof HG as HG0.
  destruct HG as (HBD & Hk & Hacc & HBLK & HROWS & H88 & Hc1 & Hc2 & Hp3 & R18 & R20 & R21 & R22 & R23
    & R27 & R19).
  pose proof HBD as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4) & (S8 & S16) & HSH & _).
  pose proof HBLK as (Hab & Hins & (Hint & Ht0 & _) & _ & _ & HREL & _ & HSL & _ & _ & _ & Hok & A0 & A1).
  destruct HSL as (L8 & L16 & L40 & L48 & L56 & L64 & L72 & L80 & L96 & L104 & L112 & L120 & L128 & L136
    & L144 & L152).
  pose proof HROWS as (Hwant & HSW).
  (* gs_ok_range (LLVMFEntrySweepS1c.v): 0 <= a.base, 1 <= a.width <= 40, a.base + a.width <= 48 *)
  pose proof (gs_ok_range _ Hok) as (Bb0 & (Bi1 & Bi40) & Bbi).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ HFR Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0' & Htc & Hs0 & Hsc & HPB).
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0.
  pose proof (@alloc_ceiling_lt rc) as HACL.
  pose proof (sw_mbytes_ge (c_pl cx)) as Hsm.
  pose proof (sw_bytes_len cx t Hok Hwant) as Hswl.
  assert (Hsweep : Z.of_nat (length (sw_bytes (c_pl cx) t)) = 34 * (8 + 3 * sw_in (c_pl cx))).
  { unfold sw_bytes. rewrite g1_sweep_len by lia. rewrite Z2Nat.id by lia. reflexivity. }
  (* the turn's row lies inside the sweep buffer: 9 + 3c + p <= 8 + 3 a.width *)
  assert (HRB : g1_row s c p + 34 <= s + sw_mbytes (c_pl cx)) by (unfold g1_row; lia).
  pose proof (g1_seat cx fp s c p W3 (ms_regs ms3) (ms_mem ms3) G9 R18 R20 R21 R23 R27
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold GO_A; lia) Hc1 ltac:(lia) Hp3 Bb0 ltac:(lia) Hs0
    ltac:(lia) L120 L128 L136 A0 A1) as HS.
  rewrite (ms_shape ms3 (BASE + GPS_g1in) Hpc Hrv Hsv Hrom Hfr Hfc).
  remember (g1_E (ms_regs ms3) (g1_xs cx fp s c p)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) (map (Z_to_bv 64) (g1_xs cx fp s c p))) E)
    by (subst E; apply env_agree_Eimg).
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
    by (intros n r Hn; subst E; apply g1_E_reg; exact Hn).
  assert (E33 : ew E 33 = Z_to_bv 64 (gF cx fp + GO_SET)) by (subst E; exact (g1_E_x _ _ 1 ltac:(cbv; lia))).
  assert (E34 : ew E 34 = Z_to_bv 64 (gF cx fp + GO_WAS)) by (subst E; exact (g1_E_x _ _ 2 ltac:(cbv; lia))).
  assert (E38 : ew E 38 = Z_to_bv 64 (g1_row s c p)) by (subst E; exact (g1_E_x _ _ 6 ltac:(cbv; lia))).
  assert (E39 : ew E 39 = Z_to_bv 64 (sw_base (c_pl cx) + Z.of_nat c))
    by (subst E; exact (g1_E_x _ _ 7 ltac:(cbv; lia))).
  assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat p)) by (rewrite (ER 23%nat 23%bv eq_refl); exact R23).
  clear HE.
  assert (SHOK : sh_ok SEGS Bx3 [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  (* run 1: 0x81694 -> the call of want_of at 0x816e8. The engine decides the three UBSan
     guards from the seat's facts and aliases (`g1_seat`): 0x8169c, 0x816ac and 0x816c0 are
     not taken. *)
  paj_run_tok RUN HS HJ SHOK Bsp3; [g1_awr|].
  g1_mem HM1.
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msW end.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ (ms_regs ms3) _ g1_kl HS HAE ltac:(vm_compute; reflexivity)) as KF.
  cbn [ms_regs restrict] in KF.
  prreg HS (1%bv : bv 5) Ra. prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
  prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3.
  prreg HS (24%bv : bv 5) Ra24. prreg HS (25%bv : bv 5) Ra25. prreg HS (26%bv : bv 5) Ra26.
  pmkst HS.
  (* `andi s8,a0,0xff` at 0x816d0, the row in s9 (0x816a8) and `andi s10,s7,0xff` at 0x816d4 *)
  assert (Q24 : getr (ms_regs msW) 24 = w64 (sw_base (c_pl cx) + Z.of_nat c)) by g1_zreg Ra24 E39.
  assert (Q25 : getr (ms_regs msW) 25 = w64 (g1_row s c p)) by g1_zreg Ra25 E38.
  assert (Q26 : getr (ms_regs msW) 26 = w64 (Z.of_nat p)) by g1_zreg Ra26 E23.
  assert (VKW : vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W3 (ms_mem msW))
    by (apply vkeep_mem; intros x; rewrite HM1; reflexivity).
  eapply SRr_bind.
  { apply (gsw_want B MT LAWS WOF cx fp k ly3 S3 W3 (ms_regs msW) (ms_mem msW) _ GPS_g1hd t s
      (sw_base (c_pl cx) + Z.of_nat c) (Z.of_nat p) HB HJ HFR).
    - exact (gsw_blk_move B cx fp ly3 S3 W3 ms3 ly3 S3 W3 (mkst (ms_regs msW) (Z_to_bv 64 0) (ms_mem msW) (seg_rom SEGS))
        t s HBLK eq_refl VKW ltac:(lia)).
    - intros i Hi. rewrite HM1. exact (HSH i Hi).
    - rewrite KF by g1_kl_in. exact G2.
    - rewrite KF by g1_kl_in. exact G3.
    - rewrite KF by g1_kl_in. exact G4.
    - rewrite KF by g1_kl_in. exact G8.
    - rewrite Ra. reflexivity.
    - unfold GPS_g1hd. lia.
    - reflexivity.
    - rewrite HM1. exact S8.
    - rewrite HM1. pose proof (S16 0 ltac:(lia)) as Hj0.
      replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in Hj0 by lia.
      cbn [Z.ltb Z.compare] in Hj0. exact Hj0.
    - (* `ld a0,136(s1)`: was_set *) g1_zreg Ra0 E34.
    - (* `ld a1,128(s1)`: set_to *) g1_zreg Ra1 E33.
    - (* `mv a2,s8`: c' = (a.base + c) & 0xff *) g1_zreg Ra2 E39.
    - (* `mv a3,s10`: p' = p & 0xff *) g1_zreg Ra3 E23.
    - (* THE c DISCHARGE (0 <= c' < 48): c' = (a.base + c) & 0xff, a.base the byte
         `lbu a0,0(a0)` read at 0x816c8 from slot 120's address and c = s2; the mask is
         the identity (alias `andi s8,a0,0xff`, as a.base + c < 256). gsw_blk's `ok` gives
         0 <= a.base and a.base + a.width <= 48 (gs_ok_range, Bb0 and Bbi), and the cut
         gives 1 <= c < a.width (g1_at's Hc1 and Hc2: the entry guard 0x81674 and the back
         edge 0x81718), so 0 <= c' <= a.base + a.width - 1 <= 47. *)
      lia.
    - (* THE p DISCHARGE (0 <= p' < 3): p' = s7 & 0xff, s7 the inner counter (0 at 0x81684,
         + 1 at 0x81704); the mask is the identity (alias `andi s10,s7,0xff`), and the cut
         carries (p < 3)%nat (g1_at's Hp3: the back edge `bne s7,s6` at 0x81708 with
         s6 = 3). *)
      lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2 & H10).
  clear HS SHOK Ra Ra0 Ra1 Ra2 Ra3 Ra24 Ra25 Ra26.
  (* run 2: 0x816ec -> the call of check_groupa at 0x81700 *)
  assert (VK1 : vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W3 mem2) by exact (vkeep_trans _ _ _ _ _ _ _ VKW HK2).
  assert (S152 : rdword (aview SEGS (w_H W3) mem2) (c_sp1 cx + 152) = Some t).
  { eapply rdword_vkeep; [exact VK1 | | exact L152]. intros kk Hkk. left; left. lia. }
  assert (R9b : getr regs2 9 = w64 (c_sp1 cx)) by (apg HP2 (9%bv : bv 5) 9; rewrite KF by g1_kl_in; exact G9).
  pose proof (g1_seat2 cx t W3 regs2 mem2 R9b ltac:(lia) ltac:(lia) S152) as HS2.
  remember (g1_E regs2 [t]) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (HAE2 : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [t])) E2) by (subst E2; apply env_agree_Eimg).
  assert (ER2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
    by (intros n r Hn; subst E2; apply g1_E_reg; exact Hn).
  assert (F32 : ew E2 32 = Z_to_bv 64 t) by (subst E2; exact (g1_E_x _ _ 0 ltac:(cbv; lia))).
  clear HE2.
  assert (SHOK2 : sh_ok SEGS Bx3 [] E2 (mrestrict (w_H W3) mem2)) by constructor.
  paj_run_tok RUN HS2 HJ2 SHOK2 Bsp3; [g1_awr|].
  g1_mem HM2.
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msC end.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs2 _ g1_kl HS2 HAE2 ltac:(vm_compute; reflexivity)) as KF2.
  cbn [ms_regs restrict] in KF2.
  prreg HS2 (1%bv : bv 5) Rb. prreg HS2 (10%bv : bv 5) Rb0. prreg HS2 (11%bv : bv 5) Rb1.
  prreg HS2 (12%bv : bv 5) Rb2. prreg HS2 (13%bv : bv 5) Rb3. prreg HS2 (14%bv : bv 5) Rb4.
  pmkst HS2.
  apply (g1_call POST cx fp k acc ly3 S3 W3 ms3 (ms_regs msC) (ms_mem msC) _ t s c p HB HJ2 HFR Hmo HG0).
  - rewrite HM2. exact VK1.
  - intros r Hr. rewrite (KF2 r Hr), (g1_kl_ap _ _ HP2 r Hr). exact (KF r Hr).
  - rewrite Rb. reflexivity.
  - (* `mv a0,s9`: the row *)
    rewrite Rb0, (ER2 25%nat 25%bv eq_refl). apg HP2 (25%bv : bv 5) 25. exact Q25.
  - (* `mv a1,s8`: the channel *)
    rewrite Rb1, (ER2 24%nat 24%bv eq_refl). apg HP2 (24%bv : bv 5) 24. exact Q24.
  - (* `mv a2,s10`: p *)
    rewrite Rb2, (ER2 26%nat 26%bv eq_refl). apg HP2 (26%bv : bv 5) 26. exact Q26.
  - (* `ld a3,152(s1)`: the table *) g1_zreg Rb3 F32.
  - (* `mv a4,a0`: the value want_of gave *)
    rewrite Rb4, (ER2 10%nat 10%bv eq_refl). exact H10.
  - exact K.
Qed.

(* ---- after check_groupa: 0x81704 -> 0x81694, 0x81684 or 0x8173c ---- *)
Lemma g1_cg : forall POST cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3 t s c p,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  g1_at GPS_g1cg cx fp k acc ly3 S3 W3 ms3 t s c p ->
  ((S p < 3)%nat -> g1_K POST GPS_g1in cx fp k acc t s c (S p)) ->
  (forall ly4 S4 W4 (ms4 : machine_state) md4,
     ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
       [(GE_CID, fp)] ly4 S4 W4 (ms_mem ms4) md4 k ->
     YG01.frames S4 = [(GE_CID, fp)] -> mo_le MT (c_S cx) S4 acc ->
     GIS_ga1 B MT cx fp k acc ly4 S4 W4 ms4 md4 ->
     getr (ms_regs ms4) 18 = w64 (Z.of_nat c + 1) ->
     SRr SEGS W4 (mkCfg ms4 md4) (POST cx)) ->
  ge_from B MT POST (GIS_gbhd B MT) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST cx fp k acc ly3 S3 W3 ms3 md3 t s c p HB HJ HFR Hmo HG INNER OUTC NEXT.
  destruct HG as (HBD & Hk & Hacc & HBLK & HROWS & H88 & Hc1 & Hc2 & Hp3 & R18 & R20 & R21 & R22 & R23
    & R27 & R19).
  pose proof HBD as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4) & _).
  pose proof HBLK as (Hab & Hins & (Hint & _) & _ & _ & _ & _ & HSL & _ & _ & _ & Hok & A0 & A1).
  destruct HSL as (L8 & L16 & L40 & L48 & L56 & L64 & L72 & L80 & L96 & L104 & L112 & L120 & L128 & L136
    & L144 & L152).
  pose proof (gs_ok_range _ Hok) as (Bb0 & (Bi1 & Bi40) & Bbi).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ HFR Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0 & Htc & Hs0 & Hsc & HPB).
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0.
  pose proof (@alloc_ceiling_lt rc) as HACL.
  pose proof (sw_mbytes_ge (c_pl cx)) as Hsm.
  pose proof (g1_seat3 cx fp c p W3 (ms_regs ms3) (ms_mem ms3) G9 R18 R23 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold GO_A; lia) Hc1 ltac:(lia) Hp3 L120 A0 A1) as HS.
  rewrite (ms_shape ms3 (BASE + GPS_g1cg) Hpc Hrv Hsv Hrom Hfr Hfc).
  remember (g1_E (ms_regs ms3) [gF cx fp + GO_A; sw_base (c_pl cx); sw_in (c_pl cx)]) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) (map (Z_to_bv 64) [gF cx fp + GO_A; sw_base (c_pl cx); sw_in (c_pl cx)])) E)
    by (subst E; apply env_agree_Eimg).
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
    by (intros n r Hn; subst E; apply g1_E_reg; exact Hn).
  assert (E34 : ew E 34 = Z_to_bv 64 (sw_in (c_pl cx))) by (subst E; exact (g1_E_x _ _ 2 ltac:(cbv; lia))).
  assert (E18 : ew E 18 = Z_to_bv 64 (Z.of_nat c)) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
  assert (E22 : ew E 22 = Z_to_bv 64 3) by (rewrite (ER 22%nat 22%bv eq_refl); exact R22).
  assert (E23 : ew E 23 = Z_to_bv 64 (Z.of_nat p)) by (rewrite (ER 23%nat 23%bv eq_refl); exact R23).
  assert (E27 : ew E 27 = Z_to_bv 64 s) by (rewrite (ER 27%nat 27%bv eq_refl); exact R27).
  clear HE.
  assert (SHOK : sh_ok SEGS Bx3 [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  (* 0x81704 `addiw s7,s7,1`, then the test of the parameter loop `bne s7,s6` at 0x81708 *)
  paj_run_tok RUN HS HJ SHOK Bsp3; [g1_awr|].
  g1_mem HM1.
  psrr_branch_tok RUN BR HS SHOK Bsp3.
  - (* p + 1 <> 3: the next parameter, back to 0x81694 *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom_off _ 23%nat (Z.of_nat p) 1) in Hc; [| cbn [ew ewset Nat.eqb]; exact E23 | lia | lia].
    rewrite (U_atom _ 22%nat 3) in Hc; [| cbn [ew ewset Nat.eqb]; exact E22 | lia].
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bsp3 GPS_g1in; [g1_awr|].
    g1_mem HM2.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msP end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ (ms_regs ms3) _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 27]%bv HS HAE
      ltac:(vm_compute; reflexivity)) as KF.
    cbn [ms_regs restrict] in KF.
    prreg HS (23%bv : bv 5) Q23.
    pmkst HS.
    rewrite HM2, HM1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg ?msf ?mdf) _ => apply (INNER ltac:(lia) ly3 S3 W3 msf mdf HJ HFR Hmo) end.
    unfold g1_at. cbn [ms_regs ms_mem mkst].
    split.
    { apply (ge_body_move cx fp GPS_g1cg GPS_g1in W3 W3 ms3 _ _ GSH_a HBD).
      - apply vkeep_mem. intros x. reflexivity.
      - lia.
      - apply KF; g1_kl_in.
      - apply KF; g1_kl_in.
      - apply KF; g1_kl_in.
      - apply KF; g1_kl_in.
      - apply KF; g1_kl_in. }
    split; [exact Hk|]. split; [exact Hacc|].
    split; [eapply gsw_blk_move; [exact HBLK | reflexivity | apply vkeep_mem; intros x; reflexivity | lia]|].
    split; [eapply (gsw_rows_move cx fp); [exact Hok | exact HROWS | apply vkeep_mem; intros x; reflexivity]|].
    split; [exact H88|].
    split; [exact Hc1|]. split; [exact Hc2|]. split; [lia|].
    split; [rewrite KF by g1_kl_in; exact R18|].
    split; [rewrite KF by g1_kl_in; exact R20|].
    split; [rewrite KF by g1_kl_in; exact R21|].
    split; [rewrite KF by g1_kl_in; exact R22|].
    split; [g1_zreg Q23 E23|].
    split; [rewrite KF by g1_kl_in; exact R27|].
    rewrite KF by g1_kl_in. exact R19.
  - (* p + 1 = 3: the channel is done; 0x8170c .. 0x81714 read a.width again and add 1 to c *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom_off _ 23%nat (Z.of_nat p) 1) in Hc; [| cbn [ew ewset Nat.eqb]; exact E23 | lia | lia].
    rewrite (U_atom _ 22%nat 3) in Hc; [| cbn [ew ewset Nat.eqb]; exact E22 | lia].
    apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_tok RUN HS HJ SHOK Bsp3; [g1_awr|].
    g1_mem HM2.
    (* the test of the channel loop `bltu s2,a0` at 0x81718 *)
    psrr_branch_tok RUN BR HS SHOK Bsp3.
    + (* c + 1 < a.width: the next channel, back to 0x81684 *)
      rewrite branch_ltu_U in Hc0.
      rewrite (U_atom_off _ 18%nat (Z.of_nat c) 1) in Hc0; [| cbn [ew ewset Nat.eqb]; exact E18 | lia | lia].
      rewrite (U_atom _ 34%nat (sw_in (c_pl cx))) in Hc0; [| cbn [ew ewset Nat.eqb]; exact E34 | lia].
      apply Z.ltb_lt in Hc0.
      paj_run_to_tok RUNTO HS HJ SHOK Bsp3 GPS_ga1; [g1_awr|].
      g1_mem HM3.
      lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msO end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ (ms_regs ms3) _ [2; 3; 4; 8; 9; 19; 21; 22; 27]%bv HS HAE
        ltac:(vm_compute; reflexivity)) as KF.
      cbn [ms_regs restrict] in KF.
      prreg HS (18%bv : bv 5) Q18.
      pmkst HS.
      rewrite HM3, HM2, HM1 in HJ |- *.
      lazymatch goal with |- SRr _ _ (mkCfg ?msf ?mdf) _ => apply (OUTC ly3 S3 W3 msf mdf HJ HFR Hmo) end.
      * unfold GIS_ga1. exists t, s, (S c). cbn [ms_regs ms_mem mkst].
        split.
        { apply (ge_body_move cx fp GPS_g1cg GPS_ga1 W3 W3 ms3 _ _ GSH_a HBD).
          - apply vkeep_mem. intros x. reflexivity.
          - lia.
          - apply KF; g1_kl_in.
          - apply KF; g1_kl_in.
          - apply KF; g1_kl_in.
          - apply KF; g1_kl_in.
          - apply KF; g1_kl_in. }
        split; [exact Hk|]. split; [exact Hacc|].
        split; [eapply gsw_blk_move; [exact HBLK | reflexivity | apply vkeep_mem; intros x; reflexivity | lia]|].
        split; [eapply (gsw_rows_move cx fp); [exact Hok | exact HROWS | apply vkeep_mem; intros x; reflexivity]|].
        split; [exact H88|].
        split; [lia|]. split; [lia|].
        (* `addiw s2,s2,1` at 0x81714 *)
        split; [g1_zreg Q18 E18|].
        split; [rewrite KF by g1_kl_in; exact R21|].
        split; [rewrite KF by g1_kl_in; exact R22|].
        split; [rewrite KF by g1_kl_in; exact R27|].
        rewrite KF by g1_kl_in. exact R19.
      * cbn [ms_regs mkst]. g1_zreg Q18 E18.
    + (* a.width <= c + 1: out of the loop, through 0x8171c .. 0x81738 to the group-B loop,
         0x8173c with i = 0 *)
      rewrite branch_ltu_U in Hc0.
      rewrite (U_atom_off _ 18%nat (Z.of_nat c) 1) in Hc0; [| cbn [ew ewset Nat.eqb]; exact E18 | lia | lia].
      rewrite (U_atom _ 34%nat (sw_in (c_pl cx))) in Hc0; [| cbn [ew ewset Nat.eqb]; exact E34 | lia].
      apply Z.ltb_ge in Hc0.
      paj_run_to_tok RUNTO HS HJ SHOK Bsp3 GPS_gbhd; [g1_awr|].
      g1_mem HM3.
      lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msG end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ (ms_regs ms3) _ [2; 3; 4; 8; 9; 19; 27]%bv HS HAE
        ltac:(vm_compute; reflexivity)) as KF.
      cbn [ms_regs restrict] in KF.
      prreg HS (18%bv : bv 5) Q18. prreg HS (24%bv : bv 5) Q24. prreg HS (20%bv : bv 5) Q20.
      prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (21%bv : bv 5) Q21.
      prreg HS (25%bv : bv 5) Q25.
      pmkst HS.
      rewrite HM3, HM2, HM1 in HJ |- *.
      lazymatch goal with |- SRr _ _ (mkCfg ?msf ?mdf) _ => apply (NEXT cx fp k acc ly3 S3 W3 msf mdf HB HJ HFR Hmo) end.
      unfold GIS_gbhd. exists t, s, 0%nat. cbn [ms_regs ms_mem mkst].
      split.
      { apply (ge_body_move cx fp GPS_g1cg GPS_gbhd W3 W3 ms3 _ _ GSH_a HBD).
        - apply vkeep_mem. intros x. reflexivity.
        - lia.
        - apply KF; g1_kl_in.
        - apply KF; g1_kl_in.
        - apply KF; g1_kl_in.
        - apply KF; g1_kl_in.
        - apply KF; g1_kl_in. }
      split; [exact Hk|]. split; [exact Hacc|].
      split; [eapply gsw_blk_move; [exact HBLK | reflexivity | apply vkeep_mem; intros x; reflexivity | lia]|].
      split; [eapply (gsw_rows_move cx fp); [exact Hok | exact HROWS | apply vkeep_mem; intros x; reflexivity]|].
      split; [exact H88|].
      split; [lia|].
      (* `mv s2,zero`, `mv s8,zero`, `addi s4,s11,170`, `addi s6,s11,190`, `addi s7,s11,186`,
         `li s5,-8` and the auipc/addi pair 0x81730/0x81738 of POLL (object 6) *)
      split; [g1_zreg Q18 E27|].
      split; [g1_zreg Q24 E27|].
      split; [g1_zreg Q20 E27|].
      split; [g1_zreg Q22 E27|].
      split; [g1_zreg Q23 E27|].
      split; [g1_zreg Q21 E27|].
      split; [rewrite Q25, (img_env_atomP E _ HEI) by (unfold A_TEXT, A_LIM; lia); apply g1_zeq64;
              change (A_OBJ 6) with 247%nat; lia|].
      split; [rewrite KF by g1_kl_in; exact R27|].
      rewrite KF by g1_kl_in. exact R19.
Qed.

(* ---- the parameter loop, by induction on the parameters left (3 - p) ---- *)
Lemma g1_inner : forall POST (n : nat) cx fp k acc t s c,
  (forall ly4 S4 W4 (ms4 : machine_state) md4,
     ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
       [(GE_CID, fp)] ly4 S4 W4 (ms_mem ms4) md4 k ->
     YG01.frames S4 = [(GE_CID, fp)] -> mo_le MT (c_S cx) S4 acc ->
     GIS_ga1 B MT cx fp k acc ly4 S4 W4 ms4 md4 ->
     getr (ms_regs ms4) 18 = w64 (Z.of_nat c + 1) ->
     SRr SEGS W4 (mkCfg ms4 md4) (POST cx)) ->
  ge_from B MT POST (GIS_gbhd B MT) ->
  forall p ly3 S3 W3 (ms3 : machine_state) md3, (3 - p = n)%nat ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  g1_at GPS_g1in cx fp k acc ly3 S3 W3 ms3 t s c p ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST n. induction n as [|n IH]; intros cx fp k acc t s c OUTC NEXT p ly3 S3 W3 ms3 md3
    Hn HB HJ HFR Hmo HG.
  { destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & Hp3 & _). lia. }
  apply (g1_in POST cx fp k acc ly3 S3 W3 ms3 md3 t s c p HB HJ HFR Hmo HG).
  intros ly4 S4 W4 ms4 md4 HJ4 Hfr4 Hmo4 HG4.
  apply (g1_cg POST cx fp k acc ly4 S4 W4 ms4 md4 t s c p HB HJ4 Hfr4 Hmo4 HG4).
  - intros Hsp ly5 S5 W5 ms5 md5 HJ5 Hfr5 Hmo5 HG5.
    exact (IH cx fp k acc t s c OUTC NEXT (S p) ly5 S5 W5 ms5 md5 ltac:(lia) HB HJ5 Hfr5 Hmo5 HG5).
  - exact OUTC.
  - exact NEXT.
Qed.

(* ---- the channel loop, by induction on the channels left (a.width - c). The block
   0x81684 .. 0x81690 sets p to 0 and s4 to 3c + 8. ---- *)
Lemma g1_outer : forall POST (m : nat),
  ge_from B MT POST (GIS_gbhd B MT) ->
  forall cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3,
  Z.to_nat (sw_in (c_pl cx) - bv_unsigned (getr (ms_regs ms3) 18)) = m ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  GIS_ga1 B MT cx fp k acc ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST m. induction m as [|m IH]; intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 Hm HB HJ HFR Hmo HGI;
  destruct HGI as (t & s & c & HBD & Hk & Hacc & HBLK & HROWS & H88 & Hc1 & Hc2 & R18 & R21 & R22 & R27 & R19);
  pose proof HBLK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hok & _);
  pose proof (gs_ok_range _ Hok) as (Bb0 & (Bi1 & Bi40) & Bbi);
  rewrite R18 in Hm; unfold w64 in Hm; rewrite unsigned_lit_small in Hm by lia.
  { lia. }
  pose proof HBD as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4) & _).
  pose proof HBLK as (Hab & Hins & (Hint & _) & _).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ HFR Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0 & Htc & Hs0 & Hsc & HPB).
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0.
  pose proof (g1_seat_o c W3 (ms_regs ms3) (ms_mem ms3) R18 Hc1 ltac:(lia)) as HS.
  rewrite (ms_shape ms3 (BASE + GPS_ga1) Hpc Hrv Hsv Hrom Hfr Hfc).
  remember (g1_E (ms_regs ms3) [8 + 3 * Z.of_nat c]) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) (map (Z_to_bv 64) [8 + 3 * Z.of_nat c])) E)
    by (subst E; apply env_agree_Eimg).
  assert (E32 : ew E 32 = Z_to_bv 64 (8 + 3 * Z.of_nat c)) by (subst E; exact (g1_E_x _ _ 0 ltac:(cbv; lia))).
  clear HE.
  assert (SHOK : sh_ok SEGS Bx3 [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  (* 0x81684 `mv s7,zero`, 0x81688 .. 0x81690 s4 := 3c + 8, on to the head 0x81694 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bsp3 GPS_g1in; [g1_awr|].
  g1_mem HM1.
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msI end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ (ms_regs ms3) _ [2; 3; 4; 8; 9; 18; 19; 21; 22; 27]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as KF.
  cbn [ms_regs restrict] in KF.
  prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23.
  pmkst HS.
  rewrite HM1 in HJ |- *.
  apply (g1_inner POST 3%nat cx fp k acc t s c) with (p := 0%nat) (ly3 := ly3) (S3 := S3).
  - (* the next channel, by the induction hypothesis *)
    intros ly4 S4 W4 ms4 md4 HJ4 Hfr4 Hmo4 HGI4 R184.
    apply (IH NEXT cx fp k acc ly4 S4 W4 ms4 md4); try assumption.
    rewrite R184. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact NEXT.
  - reflexivity.
  - exact HB.
  - exact HJ.
  - exact HFR.
  - exact Hmo.
  - unfold g1_at. cbn [ms_regs ms_mem mkst].
    split.
    { apply (ge_body_move cx fp GPS_ga1 GPS_g1in W3 W3 ms3 _ _ GSH_a HBD).
      - apply vkeep_mem. intros x. reflexivity.
      - lia.
      - apply KF; g1_kl_in.
      - apply KF; g1_kl_in.
      - apply KF; g1_kl_in.
      - apply KF; g1_kl_in.
      - apply KF; g1_kl_in. }
    split; [exact Hk|]. split; [exact Hacc|].
    split; [eapply gsw_blk_move; [exact HBLK | reflexivity | apply vkeep_mem; intros x; reflexivity | lia]|].
    split; [eapply (gsw_rows_move cx fp); [exact Hok | exact HROWS | apply vkeep_mem; intros x; reflexivity]|].
    split; [exact H88|].
    split; [exact Hc1|]. split; [exact Hc2|]. split; [lia|].
    split; [rewrite KF by g1_kl_in; exact R18|].
    split; [g1_zreg Q20 E32|].
    split; [rewrite KF by g1_kl_in; exact R21|].
    split; [rewrite KF by g1_kl_in; exact R22|].
    split; [g1_zreg Q23 E32|].
    split; [rewrite KF by g1_kl_in; exact R27|].
    rewrite KF by g1_kl_in. exact R19.
Qed.

Lemma g1_main : ge_from B MT (ge_post B MT) (GIS_gbhd B MT) ->
  ge_from B MT (ge_post B MT) (GIS_ga1 B MT).
Proof.
  intros NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR Hmo HGI.
  exact (g1_outer (ge_post B MT) _ NEXT cx fp k acc ly3 S3 W3 ms3 md3 eq_refl HB HJ HFR Hmo HGI).
Qed.

End d.
End c.
End b.
End a.

Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section zb.
Context {PI : PAImg grant_listing}.

(* 0x81684 -> 0x8173c: the second group-A loop of the sweep phase, from the contracts of
   want_of and check_groupa (GrantBContracts.v tb_want_of_spec, tb_check_groupa_spec). *)
Lemma gsw_seg_ga1 : forall (B : asyms) (MT : ameter_ops),
  GrantBContracts.tb_want_of_spec B -> GrantBContracts.tb_check_groupa_spec B -> @SEG_ga1 fx rc SK PI B MT.
Proof.
  intros B MT WOF TCG RT NEXT.
  destruct RT as (LAWS & TL & TLF & ML & MTL & MTF & AMALLOC4 & AFREE4 & ABCMP & HVIS & HGL & RO).
  exact (g1_main B MT LAWS MTF WOF TCG NEXT).
Qed.

End zb.
End z.
