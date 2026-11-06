(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACfg.v, with its module paths and module names changed; 398 of its 428 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/diginet_counter_text_A_x.v, with its module paths and module names changed; 1044 of its 1092 lines of code are new or changed and 380 lines of the source are left out. *)
(* diginet_counter_text at image B (fuzz_codec.asan-ubsan 0x869e4): the segment L2 of diginet_counter_text_B_inv.v,
   one digit of the second loop, from the loop-2 head 0x86cd0 (P_L2 with S kk digits left) to the head again (P_L2 with
   kk left) or to the exit 0x86dac (P_X).
   The code (listing lines 189-243), from = n - 8 + i:
     0x86cd0 subw a1,a4,a5 (a4 = i, a5 = 8 - n: from, 32-bit); 0x86cd4 sub t1,a4,a5 (from, 64-bit); 0x86cd8 bne a1,t1
       -> the trap 0x86eac: not taken, from fits 32 bits (l2_bne); 0x86cdc bltz a1.
     from >= 0: 0x86ce0 bltu a6,a1 -> trap: not taken, a6 = 7 >= from (l2_bltu7); 0x86ce4 bltu s2,a1 -> trap: not taken,
       s2 = ~(F + 32) >= from (l2_bltu_not); 0x86ce8 t1 = s11 + a1 = F + 32 + from; lbu t1 = s[from] (no check at
       image B); 0x86cf0 beqz a0 -> trap: not taken, a0 = sg + i >= 4096 (decided by atom 10's fact); to 0x86d00.
     from < 0 (0x86cf8): t1 = 0; 0x86cfc beqz a0 -> trap: not taken (as 0x86cf0).
     0x86d00 t2 = ld 56(s1) = sg; 0x86d04 bltu a0,t2 -> trap: not taken, sg + i >= sg (l2_bltu_sg); the instrumented
       check of the store to seg[i] at a0 (0x86d08 .. 0x86d14: seg[i]'s shadow byte is usable, so the slow path
       0x86d68 .. 0x86d70 returns to 0x86d18 and errpath_store1 0x86ed0 is not called: shadow entry mkSHE 10 0 1);
       sb t1,0(t0) (t0 = a0); 0x86d1c bltz a1 -> 0x86d50 (decided by the condition of 0x86cdc).
     from >= 0: a1 = from << 2; 0x86d24 bltu s3,a1 -> trap: not taken, s3 = ~(F + 64) >= 4 from (l2_bltu_not4);
       a1 = t4 + a1 = F + 64 + 4 from; its 4-byte instrumented check (0x86d2c .. 0x86d38: the frame's shadow bytes
       8 .. 11 are 00, so the slow path 0x86d74 .. 0x86d7c returns to 0x86d3c and errpath_load4 0x86d84 is not
       called: mkSHE 35 0 4); lw a1 = dot[from]; beqz a1 -> 0x86d50; beq a3,a7 (a3 = 8 - i, a7 = 1) -> 0x86da8
       a0 = -11 -> 0x86dac; else a2 |= 1 << i (sllw a1,a7,a4); to 0x86d50.
     0x86d50: a3 -= 1, a4 = addiw a4,1, a0 += 1, t0 += 1; bnez a3 -> 0x86cd0; else 0x86d88: a3 = ld 24(s1) = dt, the
       check of the store to dt (slow path 0x86ec0 .. 0x86ec8 returns to 0x86d9c, errpath_store1 0x86ecc not called:
       mkSHE 33 0 1), a0 = 0, sb a2,0(a3); to 0x86dac.
   The walk case-splits on the sign of from and starts from a symbolic state built from the boundary (l2_start): atoms
   0..31 the registers, 32 = SB, 33 = dt, 34 = F + 32 + from, 35 = F + 64 + 4 from, 36 = s[from], 37 = dot[from],
   38 = the byte dt holds, 39 = sg. Registers: t0 is read as atom 10 (a0 holds the same address), s10 as atom 32 (SB).
   Regions: seg[i] (atom 10, written), dt (atom 33, written), the spills 24(s1) = dt and 56(s1) = sg (atom 9), and for
   from >= 0 s[from] (atom 34) and dot[from] (atom 35). The engine runs to 0x86cec and 0x86d2c, where t1 and a1 are
   set to atoms 34 and 35 (their values are sums the engine cannot name), and on through the undecided branches; each
   UBSan branch is split and its trap side refuted. Every write lands on seg[i] or dt (KE below); the boundary at the
   end comes from l2_back / l2_exit. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import diginet_counter_text_B_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic start state at 0x86cd0 -------------------------------------------------------------------- *)
Definition l2_sr : list sv := sr_set (sr_set sr_atoms (5%bv : bv 5) (SOff 10 0)) (26%bv : bv 5) (SOff 32 0).
Definition l2_rseg : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 1 [].
Definition l2_rdt : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 38 0))].
Definition l2_rsp : YP09.region := YP09.mkRegion (Some 9%nat) 24 64 0 0
  [YP09.mkChunk 24 (CVal 8 (SOff 33 0)); YP09.mkChunk 56 (CVal 8 (SOff 39 0))].
Definition l2_rs : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition l2_rd : YP09.region := YP09.mkRegion (Some 35%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 37 0))].
Definition l2_mem (b : bool) : smem := [l2_rseg; l2_rdt; l2_rsp] ++ (if b then [l2_rs; l2_rd] else []).
(* an address of a block or a frame of the call state *)
Definition L2P : afact := mkAF 4096 (2 ^ 47 - 8) 0.
Definition l2_atoms (b : bool) : list (nat * afact) :=
  [(32%nat, mkAF SB SB 0); (10%nat, L2P); (33%nat, L2P); (38%nat, mkAF 0 255 0); (39%nat, L2P)] ++
  (if b then [(34%nat, L2P); (35%nat, L2P); (36%nat, mkAF 0 127 0); (37%nat, mkAF 0 1 0)] else []).
Definition l2_ss0 (b : bool) : sstate := mkSS PC_L2 l2_sr (l2_mem b) None (mkFacts (l2_atoms b) [] []).
Definition l2_SH (b : bool) : list shent := [mkSHE 10 0 1; mkSHE 33 0 1] ++ (if b then [mkSHE 35 0 4] else []).

(* the windows of a state with l2_mem's shape: seg[i] (atom 10) and dt (atom 33) *)
Lemma l2_wrange : forall E rs a, (skeleton rs = skeleton (l2_mem true) \/ skeleton rs = skeleton (l2_mem false)) ->
  in_wrange E rs a -> a = bv_unsigned (ew E 10) \/ a = bv_unsigned (ew E 33).
Proof.
intros E rs a Hsk0 Hin. assert (Hb : exists b, skeleton rs = skeleton (l2_mem b))
  by (destruct Hsk0 as [H | H]; [exists true | exists false]; exact H).
destruct Hb as (b & Hsk). apply (in_wrange_skeleton E rs (l2_mem b) a Hsk) in Hin.
destruct Hin as (r & Hr & Ha). unfold l2_mem in Hr. apply in_app_or in Hr.
destruct Hr as [[<- | [<- | [<- | []]]] | Hr];
[ cbn [l2_rseg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; left; lia
| cbn [l2_rdt YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; right; lia
| cbn [l2_rsp YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
destruct b; [|destruct Hr]. destruct Hr as [<- | [<- | []]];
cbn [l2_rs l2_rd YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia.
Qed.

(* ---- the engine's values as integers ------------------------------------------------------------------------ *)
Lemma l2_mod64_32 : forall z, z mod 2 ^ 64 mod 2 ^ 32 = z mod 2 ^ 32.
Proof. intros z. Z.div_mod_to_equations. lia. Qed.
(* a1 = subw a4,a5 = i - (8 - n) = from *)
Lemma l2_U_a1 : forall E n i, ew E 14 = w64 i -> ew E 15 = w64 (8 - n) -> 0 <= n <= 8 -> 0 <= i < 8 ->
  U E (SAluw ALU_SUB (SOff 14 0) (SOff 15 0)) = (n - 8 + i) mod 2 ^ 64.
Proof.
intros E n i H14 H15 Hn Hi. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite !U_SOff, H14, H15, !Z.add_0_r.
unfold w64. rewrite !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite ?Z.mod_mod by lia. rewrite ?l2_mod64_32.
rewrite ?(Z.mod_small i (2 ^ 32)) by lia. rewrite ?(Z.mod_small (8 - n) (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
f_equal. Z.div_mod_to_equations. lia.
Qed.
Lemma l2_D_a1 : forall E n i, ew E 14 = w64 i -> ew E 15 = w64 (8 - n) -> 0 <= n <= 8 -> 0 <= i < 8 ->
  sv_denot E (SAluw ALU_SUB (SOff 14 0) (SOff 15 0)) = Z_to_bv 64 (n - 8 + i).
Proof.
intros E n i H14 H15 Hn Hi. rewrite denot_lit_U, (l2_U_a1 E n i H14 H15 Hn Hi).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.
(* t1 = sub a4,a5 = a4 + a5 * (-1) = from, 64-bit *)
Lemma l2_U_t1 : forall E n i, ew E 14 = w64 i -> ew E 15 = w64 (8 - n) -> 0 <= n <= 8 -> 0 <= i < 8 ->
  U E (SAlu ALU_ADD (SOff 14 0) (SMd M_MUL (SOff 15 0) (SLit (-1)))) = (n - 8 + i) mod 2 ^ 64.
Proof.
intros E n i H14 H15 Hn Hi. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E 14 i H14) by lia. rewrite (U_atom E 15 (8 - n) H15) by lia. rewrite U_SLit.
unfold zcanon, M64.
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace ((8 - n) * (2 ^ 64 - 1)) with ((n - 8) + (8 - n) * 2 ^ 64) by ring.
rewrite Z.mod_add by lia. rewrite Z.add_mod_idemp_r by lia. f_equal. lia.
Qed.
(* bne a1,t1 -> the trap: the two values agree *)
Lemma l2_bne : forall E n i, ew E 14 = w64 i -> ew E 15 = w64 (8 - n) -> 0 <= n <= 8 -> 0 <= i < 8 ->
  branch_taken BC_NE (sv_denot E (SAluw ALU_SUB (SOff 14 0) (SOff 15 0)))
    (sv_denot E (SAlu ALU_ADD (SOff 14 0) (SMd M_MUL (SOff 15 0) (SLit (-1))))) = false.
Proof.
intros E n i H14 H15 Hn Hi. rewrite branch_ne_U, (l2_U_a1 E n i H14 H15 Hn Hi), (l2_U_t1 E n i H14 H15 Hn Hi).
rewrite Z.eqb_refl. reflexivity.
Qed.
(* bltz a1 *)
Lemma l2_bltz : forall E n i, ew E 14 = w64 i -> ew E 15 = w64 (8 - n) -> 0 <= n <= 8 -> 0 <= i < 8 ->
  branch_taken BC_LT (sv_denot E (SAluw ALU_SUB (SOff 14 0) (SOff 15 0))) (sv_denot E (SLit 0)) = (n - 8 + i <? 0).
Proof.
intros E n i H14 H15 Hn Hi. rewrite (l2_D_a1 E n i H14 H15 Hn Hi). cbn [sv_denot branch_taken]. unfold bv_lts.
rewrite !signed_lit. unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63).
change (bv_modulus 64) with (2 ^ 64).
replace (((n - 8 + i) mod 2 ^ 64 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63) with (n - 8 + i) by (Z.div_mod_to_equations; lia).
replace ((0 mod 2 ^ 64 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63) with 0 by reflexivity. reflexivity.
Qed.
(* bltu a6,a1 -> the trap: a6 = 7 >= from *)
Lemma l2_bltu7 : forall E n i, ew E 16 = w64 7 -> ew E 14 = w64 i -> ew E 15 = w64 (8 - n) -> 0 <= n <= 8 ->
  0 <= i < 8 -> 0 <= n - 8 + i ->
  branch_taken BC_LTU (sv_denot E (SOff 16 0)) (sv_denot E (SAluw ALU_SUB (SOff 14 0) (SOff 15 0))) = false.
Proof.
intros E n i H16 H14 H15 Hn Hi Hf. rewrite branch_ltu_U, (U_atom E 16 7 H16) by lia.
rewrite (l2_U_a1 E n i H14 H15 Hn Hi), Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.
(* bltu s2,a1 -> the trap: s2 = ~(F + 32) >= from *)
Lemma l2_bltu_not : forall E k x n i, ew E k = w64 (cw_not x) -> ew E 14 = w64 i -> ew E 15 = w64 (8 - n) ->
  0 <= n <= 8 -> 0 <= i < 8 -> 0 <= n - 8 + i -> 0 <= x -> x + 8 <= 2 ^ 63 ->
  branch_taken BC_LTU (sv_denot E (SOff k 0)) (sv_denot E (SAluw ALU_SUB (SOff 14 0) (SOff 15 0))) = false.
Proof.
intros E k x n i Hk H14 H15 Hn Hi Hf Hx0 Hx. rewrite branch_ltu_U, (U_atom E k (cw_not x) Hk) by (unfold cw_not; lia).
rewrite (l2_U_a1 E n i H14 H15 Hn Hi), Z.mod_small by lia. apply Z.ltb_ge. unfold cw_not. lia.
Qed.
(* a1 << 2 = 4 from *)
Lemma l2_U_sll2 : forall E n i, ew E 14 = w64 i -> ew E 15 = w64 (8 - n) -> 0 <= n <= 8 -> 0 <= i < 8 ->
  0 <= n - 8 + i -> U E (SAlu ALU_SLL (SAluw ALU_SUB (SOff 14 0) (SOff 15 0)) (SLit 2)) = 4 * (n - 8 + i).
Proof.
intros E n i H14 H15 Hn Hi Hf. rewrite U_SAlu. cbn [zalu_raw]. rewrite (l2_U_a1 E n i H14 H15 Hn Hi), U_SLit.
unfold zcanon, M64. rewrite (Z.mod_small 2) by lia. change (Z.land 2 63) with 2.
rewrite (Z.mod_small (n - 8 + i)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite Z.mul_comm. apply Z.mod_small. lia.
Qed.
(* bltu s3,a1 (a1 = from << 2) -> the trap: s3 = ~(F + 64) >= 4 from *)
Lemma l2_bltu_not4 : forall E k x n i, ew E k = w64 (cw_not x) -> ew E 14 = w64 i -> ew E 15 = w64 (8 - n) ->
  0 <= n <= 8 -> 0 <= i < 8 -> 0 <= n - 8 + i -> 0 <= x -> x + 32 <= 2 ^ 63 ->
  branch_taken BC_LTU (sv_denot E (SOff k 0))
    (sv_denot E (SAlu ALU_SLL (SAluw ALU_SUB (SOff 14 0) (SOff 15 0)) (SLit 2))) = false.
Proof.
intros E k x n i Hk H14 H15 Hn Hi Hf Hx0 Hx. rewrite branch_ltu_U, (U_atom E k (cw_not x) Hk) by (unfold cw_not; lia).
rewrite (l2_U_sll2 E n i H14 H15 Hn Hi Hf). apply Z.ltb_ge. unfold cw_not. lia.
Qed.
(* bltu a0,t2 -> the trap: a0 = sg + i >= t2 = sg *)
Lemma l2_bltu_sg : forall E sg i, ew E 10 = w64 (sg + i) -> ew E 39 = Z_to_bv 64 sg -> 0 <= sg -> 0 <= i ->
  sg + i < 2 ^ 64 -> branch_taken BC_LTU (sv_denot E (SOff 10 0)) (sv_denot E (SOff 39 0)) = false.
Proof.
intros E sg i H10 H39 Hs Hi Hsi. rewrite branch_ltu_U, (U_atom E 10 (sg + i) H10) by lia.
rewrite (U_atom E 39 sg H39) by lia. apply Z.ltb_ge. lia.
Qed.
(* t1 = s11 + a1 = F + 32 + from *)
Lemma l2_D_t1s : forall E n i F, ew E 14 = w64 i -> ew E 15 = w64 (8 - n) -> ew E 27 = w64 (F + 32) ->
  0 <= n <= 8 -> 0 <= i < 8 -> 0 <= n - 8 + i -> 0 <= F -> F + 64 <= 2 ^ 63 ->
  sv_denot E (SAlu ALU_ADD (SOff 27 0) (SAluw ALU_SUB (SOff 14 0) (SOff 15 0))) = Z_to_bv 64 (F + 32 + (n - 8 + i)).
Proof.
intros E n i F H14 H15 H27 Hn Hi Hf HF HF2. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 27 (F + 32) H27) by lia.
rewrite (l2_U_a1 E n i H14 H15 Hn Hi), (Z.mod_small (n - 8 + i)) by lia.
unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
(* a1 = t4 + (a1 << 2) = F + 64 + 4 from *)
Lemma l2_D_a1d : forall E n i F, ew E 14 = w64 i -> ew E 15 = w64 (8 - n) -> ew E 29 = w64 (F + 64) ->
  0 <= n <= 8 -> 0 <= i < 8 -> 0 <= n - 8 + i -> 0 <= F -> F + 128 <= 2 ^ 63 ->
  sv_denot E (SAlu ALU_ADD (SOff 29 0) (SAlu ALU_SLL (SAluw ALU_SUB (SOff 14 0) (SOff 15 0)) (SLit 2))) =
  Z_to_bv 64 (F + 64 + 4 * (n - 8 + i)).
Proof.
intros E n i F H14 H15 H29 Hn Hi Hf HF HF2. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 29 (F + 64) H29) by lia.
rewrite (l2_U_sll2 E n i H14 H15 Hn Hi Hf). unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
(* sllw a1,a7,a4 = 1 << i, i <= 6 *)
Lemma l2_U_sllw : forall E i, ew E 17 = w64 1 -> ew E 14 = w64 i -> 0 <= i <= 6 ->
  U E (SAluw ALU_SLL (SOff 17 0) (SOff 14 0)) = 2 ^ i.
Proof.
intros E i H17 H14 Hi. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite !U_SOff, H17, H14, !Z.add_0_r.
unfold w64. rewrite !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite !(Z.mod_small 1 (2 ^ 64)) by lia. rewrite !(Z.mod_small i (2 ^ 64)) by lia.
rewrite !(Z.mod_small 1 (2 ^ 32)) by lia. rewrite !(Z.mod_small i (2 ^ 32)) by lia.
assert (Hl : Z.land i 31 = i)
  by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; change (2 ^ 5) with 32; lia).
rewrite Hl, Z.shiftl_1_l.
assert (Hp : 0 < 2 ^ i <= 64) by (split; [apply Z.pow_pos_nonneg; lia | change 64 with (2 ^ 6); apply Z.pow_le_mono_r; lia]).
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
generalize dependent (2 ^ i). intros p Hp.
change (2 ^ 64) with 18446744073709551616 in *. change (2 ^ 32) with 4294967296 in *. change (2 ^ 31) with 2147483648 in *.
Z.div_mod_to_equations. lia.
Qed.
Lemma l2_lor_small : forall d i, 0 <= d < 128 -> 0 <= i <= 6 -> 0 <= Z.lor d (2 ^ i) < 128.
Proof.
intros d i Hd Hi.
assert (Hp : 0 < 2 ^ i <= 64) by (split; [apply Z.pow_pos_nonneg; lia | change 64 with (2 ^ 6); apply Z.pow_le_mono_r; lia]).
split; [apply Z.lor_nonneg; lia|].
destruct (Z.eq_dec (Z.lor d (2 ^ i)) 0) as [E|E]; [rewrite E; lia|].
assert (Hpos : 0 < Z.lor d (2 ^ i)) by (pose proof (Z.lor_nonneg d (2 ^ i)); lia).
change 128 with (2 ^ 7). apply (Z.log2_lt_pow2 _ _ Hpos). rewrite Z.log2_lor by lia. rewrite Z.log2_pow2 by lia.
apply Z.max_lub_lt; [|lia].
destruct (Z.eq_dec d 0) as [->|Hd0]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. change (2 ^ 7) with 128. lia.
Qed.
(* or a2,a2,a1 *)
Lemma l2_D_or : forall E d i, ew E 12 = w64 d -> ew E 17 = w64 1 -> ew E 14 = w64 i -> 0 <= d < 128 -> 0 <= i <= 6 ->
  sv_denot E (SAlu ALU_OR (SOff 12 0) (SAluw ALU_SLL (SOff 17 0) (SOff 14 0))) = Z_to_bv 64 (Z.lor d (2 ^ i)).
Proof.
intros E d i H12 H17 H14 Hd Hi. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (l2_U_sllw E i H17 H14 Hi), U_SOff, H12, Z.add_0_r.
unfold w64. rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
pose proof (l2_lor_small d i Hd Hi) as Hl.
rewrite !(Z.mod_small d (2 ^ 64)) by lia.
apply Z.mod_small. lia.
Qed.
(* addiw a4,a4,1 = i + 1 *)
Lemma l2_D_addiw : forall E i, ew E 14 = w64 i -> 0 <= i < 8 ->
  sv_denot E (SAluw ALU_ADD (SOff 14 0) (SLit 1)) = Z_to_bv 64 (i + 1).
Proof.
intros E i H14 Hi. rewrite denot_lit_U. f_equal.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite U_SOff, H14, Z.add_0_r, U_SLit.
unfold w64. rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite ?Z.mod_mod by lia. rewrite ?l2_mod64_32.
rewrite ?(Z.mod_small i (2 ^ 32)) by lia. rewrite ?(Z.mod_small 1 (2 ^ 64)) by lia.
rewrite ?(Z.mod_small 1 (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
Z.div_mod_to_equations. lia.
Qed.

(* ---- list and memory helpers ---------------------------------------------------------------------------------- *)
Lemma l2_nth_set_ne : forall (sacc sj : list Z) (i j : nat) (v : Z), length sacc = i -> (length sj = 8)%nat ->
  (i < 8)%nat -> j <> i -> nth j (sacc ++ v :: skipn (S i) sj) 0 = nth j (sacc ++ skipn i sj) 0.
Proof.
intros sacc sj i j v Hl Hsj Hi Hj.
destruct (Nat.lt_ge_cases j i) as [Hlt | Hge].
- rewrite !app_nth1 by lia. reflexivity.
- rewrite !app_nth2 by lia. rewrite Hl.
  replace (j - i)%nat with (S (j - S i)) by lia. cbn [nth]. rewrite !nth_skipn.
  f_equal. lia.
Qed.
Lemma l2_nth_set_eq : forall (sacc sj : list Z) (i : nat) (v : Z), length sacc = i ->
  nth i (sacc ++ v :: skipn (S i) sj) 0 = v.
Proof. intros sacc sj i v Hl. rewrite app_nth2 by lia. rewrite Hl, Nat.sub_diag. reflexivity. Qed.
Lemma l2_len_set : forall (sacc sj : list Z) (i : nat) (v : Z), length sacc = i -> (length sj = 8)%nat -> (i < 8)%nat ->
  length (sacc ++ v :: skipn (S i) sj) = 8%nat.
Proof. intros sacc sj i v Hl Hsj Hi. rewrite length_app. cbn [length]. rewrite length_skipn. lia. Qed.
Lemma l2_rdword_kept : forall (rd rd' : Z -> option Z) a, (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rdword.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma l2_vm_mod1 : forall (m : word -> option byte) a v, val_mem tfibsegs m a 1 (v mod 256) -> val_mem tfibsegs m a 1 v.
Proof.
intros m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma l2_nth_range : forall (P : Z -> Prop) (l : list Z) k, Forall P l -> P 0 -> P (nth k l 0).
Proof.
intros P l k H H0. destruct (Nat.lt_ge_cases k (length l)) as [Hk | Hk].
- exact (proj1 (Forall_forall P l) H _ (nth_In l 0 Hk)).
- rewrite nth_overflow by exact Hk. exact H0.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI SEG7TBL : Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Local Notation JRN g pos ly2 S2 W2 mem2 md2 :=
  (ajournal tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    ((1, pos) :: cg_own g) ly2 S2 W2 mem2 md2 (cg_k g)).

(* ---- what the walk takes from the contract's premises --------------------------------------------------------- *)
Lemma l2_pre : forall g, ct_pre B g ->
  ajournal tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    (cg_own g) (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) (cg_mdc g) (cg_k g) /\
  cdst_ok tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_lyc g) (cg_Sc g) (cg_own g)
    (cg_W g) (cg_memc g) (cg_sp g) TB_counter_text (cg_sg g) 8 /\
  cdst_ok tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_lyc g) (cg_Sc g) (cg_own g)
    (cg_W g) (cg_memc g) (cg_sp g) TB_counter_text (cg_dt g) 1 /\
  length (cg_sj g) = 8%nat /\ (cg_sg g + 8 <= cg_dt g \/ cg_dt g + 1 <= cg_sg g) /\
  alloc_ceiling <= cg_sp g - TB_counter_text /\ cg_sp g <= 2 ^ 47 /\ cg_sp g mod 16 = 0.
Proof.
intros g (HE & _ & _ & _ & Hsg & _ & Hlen & _ & Hdt & _ & Hdisj & _).
pose proof (cw_entry_stack B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TB_counter_text HE
  ltac:(unfold TB_counter_text, ESTACK; lia)) as (H1 & H2 & _ & H4 & _).
pose proof HE as (HJ & _).
split; [exact HJ|]. split; [exact Hsg|]. split; [exact Hdt|]. split; [exact Hlen|]. split; [exact Hdisj|].
unfold cg_sp. split; [exact H1|]. split; [exact H2 | exact H4].
Qed.
(* the boundary's journal: the state's frames are the frame's and the call state's, its frame addresses those of
   the call state *)
Lemma l2_jfacts : forall g pos ly2 S2 W2 mem2 md2, ct_pre B g -> JRN g pos ly2 S2 W2 mem2 md2 ->
  AR tfibsegs B ly2 S2 W2 mem2 md2 /\ frames S2 = (1, pos) :: frames (cg_Sc g) /\
  (forall c p, frame_addr ly2 c p = frame_addr (cg_lyc g) c p) /\
  AR tfibsegs B (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) (cg_mdc g).
Proof.
intros g pos ly2 S2 W2 mem2 md2 Hpre HJ.
destruct (l2_pre g Hpre) as (HJc & _).
pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrc & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfr2 & _).
split; [exact HAR2|]. split; [rewrite Hfr2, Hfrc; reflexivity|]. split; [|exact HARc].
intros c p. unfold frame_addr.
destruct Hlyc as (_ & _ & _ & _ & _ & EF & _). destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _). rewrite EF, EF2. reflexivity.
Qed.
(* the frame's place *)
Lemma l2_frame : forall g pos ly2 S2 W2 mem2 md2, ct_pre B g -> JRN g pos ly2 S2 W2 mem2 md2 ->
  4096 <= cg_F g pos /\ cg_F g pos + 128 <= alloc_ceiling /\ cg_F g pos mod 32 = 0 /\ in_app (cg_F g pos) 128.
Proof.
intros g pos ly2 S2 W2 mem2 md2 Hpre HJ.
destruct (l2_jfacts g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (HAR2 & Hfrs & Efa & _).
assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 1 pos HAR2 Hin) as (H1 & H2 & H3).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 1 pos HAR2 Hin) as (H32 & _).
unfold cg_F. rewrite Efa in H1, H2, H3, H32. replace (fs_frame_bytes 1) with 128 in * by reflexivity.
split; [exact H1|]. split; [exact H2|]. split; [exact H32 | exact H3].
Qed.
(* a byte of the window, of the frame or of the frame's shadow is not a byte the call writes *)
Lemma l2_off : forall g pos ly2 S2 W2 mem2 md2 a x, ct_pre B g -> JRN g pos ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) -> ct_wr g x ->
  (cg_sp g - TB_counter_text <= a < cg_sp g \/ cg_F g pos <= a < cg_F g pos + 128 \/
   SB + cg_F g pos / 8 <= a < SB + cg_F g pos / 8 + 16) -> a <> x.
Proof.
intros g pos ly2 S2 W2 mem2 md2 a x Hpre HJ Hperm Hx Ha ->.
destruct (l2_pre g Hpre) as (_ & Hsg & Hdt & _).
destruct (l2_jfacts g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (HAR2 & Hfrs & Efa & _).
assert (Hq : exists q n, cdst_ok tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_lyc g) (cg_Sc g)
  (cg_own g) (cg_W g) (cg_memc g) (cg_sp g) TB_counter_text q n /\ q <= x < q + n)
  by (destruct Hx; [exists (cg_sg g), 8 | exists (cg_dt g), 1]; split; assumption).
destruct Hq as (q & n & (Hq0 & Hqn & Htd & _ & _ & _ & _ & Hcw) & Hxq).
destruct Ha as [Ha | Ha].
- unfold coff_win in Hcw. lia.
- assert (Hz : in_zr x (frame_rng ly2 (1, pos)) \/ in_zr x (shadow_addr (frame_addr ly2 1 pos), fs_frame_bytes 1 / 8)).
  { unfold in_zr, frame_rng, shadow_addr. cbn [fst snd]. rewrite Efa. fold (cg_F g pos).
    replace (fs_frame_bytes 1) with 128 by reflexivity. change (128 / 8) with 16. unfold SB in Ha. unfold SHADOW_OFF.
    lia. }
  destruct (cw_fresh_own B LAWS (cg_lyc g) (cg_Sc g) ly2 S2 W2 mem2 md2 1 pos x HAR2 Hfrs Hperm Efa Hz)
    as (_ & _ & Hfb & Hff).
  destruct (Htd x Hxq) as [(bb & m & Hin & Hr) | (cid & p & Hin & Hr)].
  + exact (Hfb bb m (x - bb) Hin ltac:(lia) ltac:(lia)).
  + exact (proj1 (Hff cid p Hin) Hr).
Qed.
(* a byte the call writes is present at the boundary *)
Lemma l2_present : forall g pos ly2 S2 W2 mem2 md2 x, ct_pre B g -> JRN g pos ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) -> ct_wr g x -> apresent (w_H W2) mem2 x.
Proof.
intros g pos ly2 S2 W2 mem2 md2 x Hpre HJ Hperm Hx.
destruct (l2_pre g Hpre) as (_ & Hsg & Hdt & _).
destruct (l2_jfacts g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (HAR2 & Hfrs & Efa & _).
assert (Hq : exists q n, tdst_ok B (cg_lyc g) (cg_Sc g) q n /\ q <= x < q + n)
  by (destruct Hx as [Hx | Hx];
      [exists (cg_sg g), 8; split; [exact (proj1 (proj2 (proj2 Hsg))) | lia]
      | exists (cg_dt g), 1; split; [exact (proj1 (proj2 (proj2 Hdt))) | lia]]).
destruct Hq as (q & n & Htd & Hxq).
destruct (Htd x Hxq) as [(bb & m & Hin & Hr) | (cid & p & Hin & Hr)].
- assert (Hin2 : In (bb, m) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bb m HAR2 Hin2) as (_ & _ & _ & _ & Hp & _).
  exact (proj1 (Hp x Hr)).
- assert (Hin2 : In (cid, p) (frames S2)) by (rewrite Hfrs; right; exact Hin).
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid p HAR2 Hin2) as (_ & _ & Hp & _).
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. rewrite <- Efa in Hr. exact (proj1 (Hp x Hr)).
Qed.

(* ---- what a digit keeps: the run wrote only seg[i] and dt ------------------------------------------------------ *)
Lemma l2_keep : forall g pos ly2 S2 regs2 mem2 md2 W2 i n s dot sacc regs3 mem3 v,
  ct_pre B g -> JRN g pos ly2 S2 W2 mem2 md2 ->
  tcj_kept tfibsegs B TB_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) W2 mem2 (cg_sp g) (ct_wr g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) ->
  ct_common g pos regs2 mem2 W2 -> ct_arrays g pos W2 mem2 n s dot -> 0 <= n <= 8 ->
  garr8 tfibsegs (rd W2 mem2) (cg_sg g) (sacc ++ skipn (Z.to_nat i) (cg_sj g)) ->
  length sacc = Z.to_nat i -> 0 <= i < 8 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (a = cg_sg g + i \/ a = cg_dt g) ->
     aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  val_mem tfibsegs (rd W2 mem3) (cg_sg g + i) 1 v -> 0 <= v < 256 ->
  getr regs3 2 = getr regs2 2 -> getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 ->
  getr regs3 8 = getr regs2 8 -> getr regs3 9 = getr regs2 9 -> getr regs3 24 = getr regs2 24 ->
  getr regs3 26 = getr regs2 26 ->
  tcj_kept tfibsegs B TB_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) W2 mem3 (cg_sp g) (ct_wr g) /\
  ct_common g pos regs3 mem3 W2 /\ ct_arrays g pos W2 mem3 n s dot /\
  garr8 tfibsegs (rd W2 mem3) (cg_sg g) (sacc ++ v :: skipn (S (Z.to_nat i)) (cg_sj g)).
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 i n s dot sacc regs3 mem3 v Hpre HJ HK Hperm Hcom Harr Hn Hseg Hlen Hi KE HG
  Hv Hvr R2 R3 R4 R8 R9 R24 R26.
destruct (l2_pre g Hpre) as (_ & Hsg & Hdt & Hlsj & Hdisj & Hce & H47 & H16).
destruct (l2_jfacts g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (HAR2 & Hfrs & Efa & HARc).
destruct (l2_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (HF0 & HFc & HF32 & HFapp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hsg as (Hsg0 & Hsg63 & _). pose proof Hdt as (Hdt0 & Hdt63 & _).
assert (Hsp1 : cg_sp g - 224 < cg_sp1 g <= cg_sp g - 192).
{ unfold cg_sp1. pose proof (Z.div_mod (cg_sp g - 192) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (cg_sp g - 192) 32 ltac:(lia)). lia. }
assert (HT : TB_counter_text = 4320) by reflexivity.
assert (KZ : forall a, (cg_sp g - TB_counter_text <= a < cg_sp g \/ cg_F g pos <= a < cg_F g pos + 128 \/
   SB + cg_F g pos / 8 <= a < SB + cg_F g pos / 8 + 16) -> aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha. apply KE.
  - assert (0 <= cg_F g pos / 8 <= cg_F g pos) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    unfold SB in Ha. lia.
  - intros [Ha2 | Ha2].
    + apply (l2_off g pos ly2 S2 W2 mem2 md2 a (cg_sg g + i) Hpre HJ Hperm ltac:(left; lia) Ha Ha2).
    + apply (l2_off g pos ly2 S2 W2 mem2 md2 a (cg_dt g) Hpre HJ Hperm ltac:(right; lia) Ha Ha2). }
assert (VK : forall a k vv, (forall x, a <= x < a + Z.of_nat k -> cg_sp g - TB_counter_text <= x < cg_sp g \/
   cg_F g pos <= x < cg_F g pos + 128 \/ SB + cg_F g pos / 8 <= x < SB + cg_F g pos / 8 + 16) ->
   val_mem tfibsegs (rd W2 mem2) a k vv -> val_mem tfibsegs (rd W2 mem3) a k vv).
{ intros a k vv Hz Hvm. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hvm].
  intros x Hx. apply KZ. exact (Hz x Hx). }
split.
{ apply (cw_kept_step B LAWS TB_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) (cg_mdc g) W2 mem2 mem3
    (cg_sp g) (ct_wr g) (fun a => a = cg_sg g + i \/ a = cg_dt g) Hce HARc HK KE).
  - intros a [-> | ->]; right; left.
    + split; [unfold ct_wr; left; lia|]. intros Him.
      exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low _ _ _ _ _ (cg_sg g) 8 (cg_sg g + i) HARc
        (proj1 (proj2 (proj2 Hsg))) ltac:(lia) Him).
    + split; [unfold ct_wr; right; lia|]. intros Him.
      exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low _ _ _ _ _ (cg_dt g) 1 (cg_dt g) HARc
        (proj1 (proj2 (proj2 Hdt))) ltac:(lia) Him).
  - intros a Ha. exact (HG a Ha). }
split.
{ destruct Hcom as (C8 & C2r & C9 & C3r & C4r & C24 & C26 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12
    & V13 & S24 & S32 & S40 & S48 & S56 & Hfl & Hsh).
  unfold ct_common.
  rewrite R8, R2, R9, R3, R4, R24, R26.
  do 7 (split; [assumption|]).
  do 13 (split; [apply VK; [intros x Hx; left; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; lia | assumption]|]).
  do 5 (split; [apply VK; [intros x Hx; left; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; lia | assumption]|]).
  split.
  - rewrite <- Hfl. apply l2_rdword_kept. intros k Hk. apply KZ. right; left. lia.
  - intros j Hj. destruct (Hsh j Hj) as (Hvj & Hrj). split; [|exact Hrj].
    apply VK; [|exact Hvj]. intros x Hx. right; right.
    unfold CT_FRAME_SHADOW in Hj. cbn [length] in Hj. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia. }
split.
{ destruct Harr as (A1 & A2). split.
  - intros k Hk. apply VK; [|exact (A1 k Hk)]. intros x Hx. right; left.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
  - intros k Hk. apply VK; [|exact (A2 k Hk)]. intros x Hx. right; left.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia. }
intros j Hj.
rewrite (l2_len_set sacc (cg_sj g) (Z.to_nat i) v Hlen Hlsj ltac:(lia)) in Hj.
destruct (Nat.eq_dec j (Z.to_nat i)) as [-> | Hne].
- rewrite (l2_nth_set_eq sacc (cg_sj g) (Z.to_nat i) v Hlen). rewrite Z2Nat.id by lia. split; [exact Hv | exact Hvr].
- rewrite (l2_nth_set_ne sacc (cg_sj g) (Z.to_nat i) j v Hlen Hlsj ltac:(lia) Hne).
  assert (Hj2 : (j < length (sacc ++ skipn (Z.to_nat i) (cg_sj g)))%nat)
    by (rewrite length_app, length_skipn; lia).
  destruct (Hseg j Hj2) as (Hvj & Hrj). split; [|exact Hrj].
  apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hvj].
  intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply KE; [lia|].
  intros [Hx2 | Hx2]; [|lia]. assert (Z.of_nat j <> i) by lia. lia.
Qed.

(* ---- the two ends of a digit ----------------------------------------------------------------------------------- *)
Lemma l2_back : forall g pos kk ly2 S2 regs2 mem2 md2 W2 i n s dot sacc regs3 mem3 md3 v d',
  ct_pre B g -> JRN g pos ly2 S2 W2 mem2 md2 ->
  tcj_kept tfibsegs B TB_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) W2 mem2 (cg_sp g) (ct_wr g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) -> ~ In (1, pos) (frames (cg_Sc g)) ->
  same_io (cg_mdc g) md2 -> mo_le MT (cg_Sc g) S2 0 ->
  ct_common g pos regs2 mem2 W2 -> ct_l1 n s dot -> ct_arrays g pos W2 mem2 n s dot ->
  garr8 tfibsegs (rd W2 mem2) (cg_sg g) (sacc ++ skipn (Z.to_nat i) (cg_sj g)) ->
  length sacc = Z.to_nat i -> Forall (fun v => 0 <= v < 128) sacc -> 0 <= i -> i + 1 < 8 ->
  Z.of_nat kk = 8 - (i + 1) ->
  JRN g pos ly2 S2 W2 mem3 md3 -> same_io md2 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (a = cg_sg g + i \/ a = cg_dt g) ->
     aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  val_mem tfibsegs (rd W2 mem3) (cg_sg g + i) 1 v -> 0 <= v < 128 ->
  val_mem tfibsegs (rd W2 mem3) (cg_dt g) 1 (cg_dj g) ->
  getr regs3 2 = getr regs2 2 -> getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 ->
  getr regs3 8 = getr regs2 8 -> getr regs3 9 = getr regs2 9 -> getr regs3 24 = getr regs2 24 ->
  getr regs3 26 = getr regs2 26 ->
  getr regs3 10 = w64 (cg_sg g + (i + 1)) -> getr regs3 5 = w64 (cg_sg g + (i + 1)) ->
  getr regs3 12 = w64 d' -> getr regs3 13 = w64 (8 - (i + 1)) -> getr regs3 14 = w64 (i + 1) ->
  getr regs3 15 = w64 (8 - n) -> getr regs3 16 = w64 7 -> getr regs3 17 = w64 1 ->
  getr regs3 27 = w64 (cg_F g pos + 32) -> getr regs3 29 = w64 (cg_F g pos + 64) ->
  getr regs3 18 = w64 (cw_not (cg_F g pos + 32)) -> getr regs3 19 = w64 (cw_not (cg_F g pos + 64)) ->
  counter_text_spec (cg_tb g) = ct2_go n s dot (i + 1) kk (sacc ++ [v]) d' -> 0 <= d' < 128 ->
  ct_cut B MT g pos PC_L2 (P_L2 g pos kk) W2 (cfg_at tfibsegs PC_L2 regs3 mem3 md3).
Proof.
intros g pos kk ly2 S2 regs2 mem2 md2 W2 i n s dot sacc regs3 mem3 md3 v d' Hpre HJ HK Hperm Hni Hio Hmo Hcom Hl1
  Harr Hseg Hlen Hsacc Hi0 Hi1 Hkk HJ3 Hio3 KE HG Hv Hvr Hdj R2 R3 R4 R8 R9 R24 R26 R10 R5 R12 R13 R14 R15 R16 R17
  R27 R29 R18 R19 Hspec Hd'.
pose proof Hl1 as ((Hn & _) & _).
destruct (l2_keep g pos ly2 S2 regs2 mem2 md2 W2 i n s dot sacc regs3 mem3 v Hpre HJ HK Hperm Hcom Harr Hn Hseg Hlen
  ltac:(lia) KE HG Hv ltac:(lia) R2 R3 R4 R8 R9 R24 R26) as (K3 & C3 & A3 & G3).
exists ly2, S2, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact K3|]. split; [exact Hperm|]. split; [exact Hni|].
split; [exact (same_io_trans _ _ _ Hio Hio3)|]. split; [exact Hmo|]. split; [exact C3|].
exists (i + 1), n, d', s, dot, (sacc ++ [v]).
split; [exact R10|]. split; [exact R5|]. split; [exact R12|]. split; [exact R13|]. split; [exact R14|].
split; [exact R15|]. split; [exact R16|]. split; [exact R17|]. split; [exact R27|]. split; [exact R29|].
split; [exact R18|]. split; [exact R19|].
split; [exact Hkk|]. split; [lia|]. split; [exact Hspec|]. split; [exact Hl1|].
split; [rewrite length_app, Hlen; cbn [length]; lia|].
split; [apply Forall_app; split; [exact Hsacc | constructor; [lia | constructor]]|].
split; [exact Hd'|]. split; [exact A3|].
split; [|exact Hdj].
replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite <- app_assoc. exact G3.
Qed.
Lemma l2_exit : forall g pos ly2 S2 regs2 mem2 md2 W2 i n s dot sacc regs3 mem3 md3 v r dres dv,
  ct_pre B g -> JRN g pos ly2 S2 W2 mem2 md2 ->
  tcj_kept tfibsegs B TB_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) W2 mem2 (cg_sp g) (ct_wr g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) -> ~ In (1, pos) (frames (cg_Sc g)) ->
  same_io (cg_mdc g) md2 -> mo_le MT (cg_Sc g) S2 0 ->
  ct_common g pos regs2 mem2 W2 -> ct_l1 n s dot -> ct_arrays g pos W2 mem2 n s dot ->
  garr8 tfibsegs (rd W2 mem2) (cg_sg g) (sacc ++ skipn (Z.to_nat i) (cg_sj g)) ->
  length sacc = Z.to_nat i -> 0 <= i < 8 ->
  JRN g pos ly2 S2 W2 mem3 md3 -> same_io md2 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (a = cg_sg g + i \/ a = cg_dt g) ->
     aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  val_mem tfibsegs (rd W2 mem3) (cg_sg g + i) 1 v -> 0 <= v < 256 ->
  val_mem tfibsegs (rd W2 mem3) (cg_dt g) 1 dv ->
  getr regs3 2 = getr regs2 2 -> getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 ->
  getr regs3 8 = getr regs2 8 -> getr regs3 9 = getr regs2 9 -> getr regs3 24 = getr regs2 24 ->
  getr regs3 26 = getr regs2 26 ->
  getr regs3 10 = w64 r ->
  counter_text_spec (cg_tb g) = (r, sacc ++ [v], dres) -> (r = 0 -> i = 7 /\ dv = dres) ->
  ct_cut B MT g pos PC_X (P_X g) W2 (cfg_at tfibsegs PC_X regs3 mem3 md3).
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 i n s dot sacc regs3 mem3 md3 v r dres dv Hpre HJ HK Hperm Hni Hio Hmo Hcom Hl1
  Harr Hseg Hlen Hi HJ3 Hio3 KE HG Hv Hvr Hdv R2 R3 R4 R8 R9 R24 R26 R10 Hspec Hcase.
pose proof Hl1 as ((Hn & _) & _).
destruct (l2_pre g Hpre) as (_ & _ & _ & Hlsj & _).
destruct (l2_keep g pos ly2 S2 regs2 mem2 md2 W2 i n s dot sacc regs3 mem3 v Hpre HJ HK Hperm Hcom Harr Hn Hseg Hlen
  Hi KE HG Hv Hvr R2 R3 R4 R8 R9 R24 R26) as (K3 & C3 & A3 & G3).
exists ly2, S2, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact K3|]. split; [exact Hperm|]. split; [exact Hni|].
split; [exact (same_io_trans _ _ _ Hio Hio3)|]. split; [exact Hmo|]. split; [exact C3|].
unfold P_X, ct_res. rewrite Hspec.
split; [exact R10|]. split.
- intros Hr0. destruct (Hcase Hr0) as (-> & <-). split; [|exact Hdv].
  replace (skipn (S (Z.to_nat 7)) (cg_sj g)) with (@nil Z) in G3
    by (symmetry; apply skipn_all2; change (S (Z.to_nat 7)) with 8%nat; lia).
  exact G3.
- intros _. exists (sacc ++ v :: skipn (S (Z.to_nat i)) (cg_sj g)), dv.
  split; [exact G3|]. split; [apply l2_len_set; [exact Hlen | exact Hlsj | lia] | exact Hdv].
Qed.

(* ---- the symbolic state at the boundary ---------------------------------------------------------------------- *)
(* the shadow byte the frame's shadow holds, as the engine's shadow reader gives it *)
Lemma l2_rdof_of_vm : forall (m : word -> option byte) a v, val_mem tfibsegs m a 1 v -> 0 <= v < 256 ->
  rd_of tfibsegs m a = Some v.
Proof.
intros m a v H Hv. pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite (le_byte_small v 1 0 ltac:(cbn; lia) ltac:(lia)) in H0.
assert (Hsh : Z.shiftr v (8 * Z.of_nat 0) = v) by (cbn [Z.of_nat]; rewrite Z.mul_0_r, Z.shiftr_0_r; reflexivity).
rewrite Hsh in H0. unfold rd_of. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.
(* the frame's shadow bytes 4 (s[8]) and 8 .. 11 (dot[8]) are 00: those ranges are addressable *)
Lemma l2_ra_frame : forall (W : world tfibsegs) mem F, garr8 tfibsegs (rd W mem) (SB + F / 8) CT_FRAME_SHADOW ->
  F mod 8 = 0 -> 0 <= F ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 32) 8 /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 64) 32.
Proof.
intros W mem F Hsh HF8 HF0.
assert (HZ : forall j, ((4 <= j < 5)%nat \/ (8 <= j < 12)%nat) -> aview tfibsegs (w_H W) mem (SB + F / 8 + Z.of_nat j) = Some 0).
{ intros j Hj. destruct (Hsh j ltac:(cbn [length CT_FRAME_SHADOW]; lia)) as (Hv & _).
  assert (Hn : nth j CT_FRAME_SHADOW 0 = 0)
    by (destruct Hj as [Hj|Hj]; do 12 (destruct j as [|j]; [first [reflexivity | lia] |]); lia).
  rewrite Hn in Hv. exact (l2_rdof_of_vm _ _ 0 Hv ltac:(lia)). }
assert (HFq : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
assert (D32 : (F + 32) / 8 = F / 8 + 4) by (rewrite HFq at 1; replace (8 * (F / 8) + 32) with ((F / 8 + 4) * 8) by lia; apply Z.div_mul; lia).
assert (D64 : (F + 64) / 8 = F / 8 + 8) by (rewrite HFq at 1; replace (8 * (F / 8) + 64) with ((F / 8 + 8) * 8) by lia; apply Z.div_mul; lia).
assert (M32 : (F + 32) mod 8 = 0) by (rewrite HFq at 1; replace (8 * (F / 8) + 32) with ((F / 8 + 4) * 8) by lia; apply Z_mod_mult).
assert (M64 : (F + 64) mod 8 = 0) by (rewrite HFq at 1; replace (8 * (F / 8) + 64) with ((F / 8 + 8) * 8) by lia; apply Z_mod_mult).
split; apply zero_shadow_range; try assumption; try reflexivity.
- intros k Hk. change (8 / 8) with 1 in Hk. unfold shadow_of_addr. rewrite D32.
  replace (SHADOW_OFF + (F / 8 + 4) + k) with (SB + F / 8 + Z.of_nat 4) by (unfold SB, SHADOW_OFF; cbn [Z.of_nat]; lia).
  apply HZ. left; lia.
- intros k Hk. change (32 / 8) with 4 in Hk. unfold shadow_of_addr. rewrite D64.
  replace (SHADOW_OFF + (F / 8 + 8) + k) with (SB + F / 8 + Z.of_nat (8 + Z.to_nat k)) by (unfold SB, SHADOW_OFF; lia).
  apply HZ. right; lia.
Qed.

Definition l2_xs (g : ct_ctx) (pos n i : Z) (s dot : list Z) : list Z :=
  [cg_dt g; cg_F g pos + 32 + (n - 8 + i); cg_F g pos + 64 + 4 * (n - 8 + i);
   nth (Z.to_nat (n - 8 + i)) s 0; nth (Z.to_nat (n - 8 + i)) dot 0; cg_dj g mod 256; cg_sg g].
Lemma l2_start : forall (b : bool) g pos ly2 S2 regs2 mem2 md2 W2 i n s dot,
  ct_pre B g -> JRN g pos ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) ->
  ct_common g pos regs2 mem2 W2 ->
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cg_sg g) 8 ->
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cg_dt g) 1 ->
  getr regs2 10 = w64 (cg_sg g + i) -> getr regs2 5 = w64 (cg_sg g + i) -> 0 <= i < 8 ->
  ct_l1 n s dot -> ct_arrays g pos W2 mem2 n s dot ->
  val_mem tfibsegs (rd W2 mem2) (cg_dt g) 1 (cg_dj g) ->
  (b = true -> 0 <= n - 8 + i) ->
  st_ok tfibsegs (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) (l2_ss0 b)
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_L2) mem2 (seg_rom tfibsegs))) /\
  sh_ok tfibsegs CW_Bx (l2_SH b) (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) (rd W2 mem2).
Proof.
intros b g pos ly2 S2 regs2 mem2 md2 W2 i n s dot Hpre HJ Hperm Hcom Hrsg Hrdt R10 R5 Hi Hl1 Harr Hdj Hb.
destruct (l2_pre g Hpre) as (_ & Hsg & Hdt & _ & Hdisj & Hce & H47 & _).
destruct (l2_jfacts g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (HAR2 & Hfrs & Efa & HARc).
destruct (l2_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (HF0 & HFc & HF32 & HFapp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hlt.
pose proof Hsg as (Hsg0 & Hsg63 & Hsgtd & _ & _ & _ & Hsgam & Hsgcw).
pose proof Hdt as (Hdt0 & Hdt63 & Hdttd & _ & _ & _ & Hdtam & Hdtcw).
pose proof (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ (cg_sg g) 8 (cg_sg g + 7) HARc Hsgtd ltac:(lia)) as (Bs7 & _).
pose proof (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ (cg_sg g) 8 (cg_sg g) HARc Hsgtd ltac:(lia)) as (Bs0 & _).
pose proof (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ (cg_dt g) 1 (cg_dt g) HARc Hdttd ltac:(lia)) as (Bd & _).
assert (Hnf : forall x, ct_wr g x -> ~ (cg_F g pos <= x < cg_F g pos + 128))
  by (intros x Hx Hin; exact (l2_off g pos ly2 S2 W2 mem2 md2 x x Hpre HJ Hperm Hx ltac:(right; left; exact Hin) eq_refl)).
pose proof (Hnf (cg_sg g + i) ltac:(unfold ct_wr; left; lia)) as N1.
pose proof (Hnf (cg_dt g) ltac:(unfold ct_wr; right; lia)) as N2.
assert (Hsp1 : cg_sp g - 224 < cg_sp1 g <= cg_sp g - 192).
{ unfold cg_sp1. pose proof (Z.div_mod (cg_sp g - 192) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (cg_sp g - 192) 32 ltac:(lia)). lia. }
assert (HT : TB_counter_text = 4320) by reflexivity.
pose proof Hcom as (_ & _ & C9 & _ & _ & _ & C26 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vdt & _ & _ & _
  & Vsg & _ & Hsh).
pose proof Hl1 as ((Hn & _) & Hdot & _ & Hs).
pose proof (l2_nth_range (fun v => 0 <= v < 128) s (Z.to_nat (n - 8 + i)) Hs ltac:(cbv beta; lia)) as Hsv. cbv beta in Hsv.
pose proof (l2_nth_range (fun v => 0 <= v <= 1) dot (Z.to_nat (n - 8 + i)) Hdot ltac:(cbv beta; lia)) as Hdv. cbv beta in Hdv.
pose proof (Z.mod_pos_bound (cg_dj g) 256 ltac:(lia)) as Hdjm.
assert (E10 : ew (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) 10 = Z_to_bv 64 (cg_sg g + i))
  by (rewrite (cw_ew_reg regs2 _ 10 10%bv eq_refl); exact R10).
assert (E9 : ew (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) 9 = Z_to_bv 64 (cg_sp1 g))
  by (rewrite (cw_ew_reg regs2 _ 9 9%bv eq_refl); exact C9).
assert (E32 : ew (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) 32 = Z_to_bv 64 SB) by apply cw_ew_SB.
assert (X33 : ew (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) 33 = Z_to_bv 64 (cg_dt g))
  by exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 0).
assert (X34 : ew (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) 34 = Z_to_bv 64 (cg_F g pos + 32 + (n - 8 + i)))
  by exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 1).
assert (X35 : ew (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) 35 = Z_to_bv 64 (cg_F g pos + 64 + 4 * (n - 8 + i)))
  by exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 2).
assert (X36 : ew (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) 36 = Z_to_bv 64 (nth (Z.to_nat (n - 8 + i)) s 0))
  by exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 3).
assert (X37 : ew (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) 37 = Z_to_bv 64 (nth (Z.to_nat (n - 8 + i)) dot 0))
  by exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 4).
assert (X38 : ew (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) 38 = Z_to_bv 64 (cg_dj g mod 256))
  by exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 5).
assert (X39 : ew (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) 39 = Z_to_bv 64 (cg_sg g))
  by exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 6).
assert (Hfr8 : cg_F g pos mod 8 = 0) by exact (mod32_mod8 _ HF32).
destruct (l2_ra_frame W2 mem2 (cg_F g pos) Hsh Hfr8 ltac:(lia)) as (RAs & RAd).
assert (AMf : forall o k, 0 <= o -> o + k <= 128 -> amem_range (cg_F g pos + o) k).
{ intros o k Ho Hk. unfold amem_range. rewrite C3, C4, C5. unfold in_app in HFapp.
  unfold kLowShadowBeg, ASAN_CEIL in HFapp. rewrite ?C3 in HFapp. unfold kHighMemBeg in HFapp. lia. }
split.
- rewrite restrict_mkst_fx. unfold l2_ss0. apply (entry_st_ok_full tfibsegs).
  + unfold l2_sr. apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |] | reflexivity |].
    * rewrite sv_denot_SOff0, E10. exact R5.
    * rewrite sv_denot_SOff0, E32. exact C26.
  + destruct b; vm_compute; reflexivity.
  + unfold l2_mem. apply Forall_app. split.
    * apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      -- unfold region_ok, l2_rseg.
         cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
         rewrite E10, unsigned_lit_small by lia.
         split; [lia|]. split; [lia|]. split; [|constructor].
         intros o Ho. replace (cg_sg g + i + o) with (cg_sg g + i) by lia. apply (apresent_writable tfibsegs).
         apply (l2_present g pos ly2 S2 W2 mem2 md2 (cg_sg g + i) Hpre HJ Hperm). unfold ct_wr; left; lia.
      -- unfold region_ok, l2_rdt.
         cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
         rewrite X33, unsigned_lit_small by lia.
         split; [lia|]. split; [lia|]. split.
         ++ intros o Ho. replace (cg_dt g + o) with (cg_dt g) by lia. apply (apresent_writable tfibsegs).
            apply (l2_present g pos ly2 S2 W2 mem2 md2 (cg_dt g) Hpre HJ Hperm). unfold ct_wr; right; lia.
         ++ constructor; [|constructor].
            apply (chunk_ok_val tfibsegs _ _ (cg_dt g) 0 1 (SOff 38 0) (cg_dj g mod 256));
            [rewrite sv_denot_SOff0; exact X38 | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
            rewrite Z.add_0_r. exact (cw_val_mem_mod _ _ 1 _ Hdj).
      -- unfold region_ok, l2_rsp.
         cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
         rewrite E9, unsigned_lit_small by lia.
         split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
         constructor; [|constructor; [|constructor]].
         ++ apply (chunk_ok_val tfibsegs _ _ (cg_sp1 g) 24 8 (SOff 33 0) (cg_dt g));
            [rewrite sv_denot_SOff0; exact X33 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Vdt].
         ++ apply (chunk_ok_val tfibsegs _ _ (cg_sp1 g) 56 8 (SOff 39 0) (cg_sg g));
            [rewrite sv_denot_SOff0; exact X39 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Vsg].
    * destruct b; [|apply Forall_nil]. specialize (Hb eq_refl).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- unfold region_ok, l2_rs.
         cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
         rewrite X34, unsigned_lit_small by lia.
         split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
         constructor; [|constructor].
         apply (chunk_ok_val tfibsegs _ _ (cg_F g pos + 32 + (n - 8 + i)) 0 1 (SOff 36 0) (nth (Z.to_nat (n - 8 + i)) s 0));
         [rewrite sv_denot_SOff0; exact X36 | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
         rewrite Z.add_0_r. exact (proj2 Harr (n - 8 + i) ltac:(lia)).
      -- unfold region_ok, l2_rd.
         cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
         rewrite X35, unsigned_lit_small by lia.
         split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
         constructor; [|constructor].
         apply (chunk_ok_val tfibsegs _ _ (cg_F g pos + 64 + 4 * (n - 8 + i)) 0 4 (SOff 37 0) (nth (Z.to_nat (n - 8 + i)) dot 0));
         [rewrite sv_denot_SOff0; exact X37 | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
         rewrite Z.add_0_r. exact (proj1 Harr (n - 8 + i) ltac:(lia)).
  + apply pairwise_disjoint_of_extents.
    destruct b; [specialize (Hb eq_refl)|];
    unfold l2_mem, l2_rseg, l2_rdt, l2_rsp, l2_rs, l2_rd, extent_of_region;
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite ?E10, ?X33, ?E9, ?X34, ?X35; rewrite !unsigned_lit_small by lia;
    cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
    unfold coff_win in Hsgcw, Hdtcw;
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  + split; [|split; exact I].
    unfold l2_atoms, L2P. destruct b; [specialize (Hb eq_refl)|]; cbn [f_atoms app atoms_ok]; unfold afact_ok;
    cbn [af_lo af_hi af_al2];
    rewrite ?E10, ?X33, ?E32, ?X34, ?X35, ?X36, ?X37, ?X38, ?X39;
    rewrite !unsigned_lit_small by (unfold SB; lia); rewrite ?Z.pow_0_r, ?Z.mod_1_r;
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
- unfold sh_ok, l2_SH. apply Forall_app. split.
  + assert (RA1 : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cg_sg g + i + 0) 1)
      by (apply (range_addressable_sub _ _ (cg_sg g) 8); [exact Hrsg | lia | lia]).
    assert (AM1 : amem_range (cg_sg g + i + 0) 1) by (unfold amem_range in *; lia).
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * exact (cw_shent_ra_off W2 mem2 _ 10 (cg_sg g + i) 0 1 RA1 AM1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E10 E32).
    * exact (cw_shent_ra W2 mem2 _ 33 (cg_dt g) 1 Hrdt Hdtam ltac:(lia) ltac:(lia) ltac:(lia) X33 E32).
  + destruct b; [|apply Forall_nil]. specialize (Hb eq_refl).
    assert (RA3 : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (cg_F g pos + 64 + 4 * (n - 8 + i)) 4)
      by (apply (range_addressable_sub _ _ (cg_F g pos + 64) 32); [exact RAd | lia | lia]).
    assert (AM3 : amem_range (cg_F g pos + 64 + 4 * (n - 8 + i)) 4)
      by (replace (cg_F g pos + 64 + 4 * (n - 8 + i)) with (cg_F g pos + (64 + 4 * (n - 8 + i))) by lia; apply AMf; lia).
    apply Forall_cons; [|apply Forall_nil].
    exact (cw_shent_ra W2 mem2 _ 35 (cg_F g pos + 64 + 4 * (n - 8 + i)) 4 RA3 AM3 ltac:(lia) ltac:(lia) ltac:(lia) X35 E32).
Qed.

(* ---- the write rights of the runs: seg[i] and dt are the caller's to write ------------------------------------- *)
Lemma l2_awr_byte : forall g pos ly2 S2 W2 mem2 md2 x, ct_pre B g -> JRN g pos ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) -> ct_wr g x ->
  awr_byte (cg_STK g) (cg_sp0 g) (cg_FP g) (ablocks B (cg_ly g) (cg_S g)) (ablocks B ly2 S2) ly2
    ((1, pos) :: cg_own g) x.
Proof.
intros g pos ly2 S2 W2 mem2 md2 x Hpre HJ Hperm Hx.
destruct (l2_pre g Hpre) as (_ & Hsg & Hdt & _).
destruct (l2_jfacts g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (_ & _ & Efa & _).
assert (Hw : awr_byte (cg_STK g) (cg_sp0 g) (cg_FP g) (ablocks B (cg_ly g) (cg_S g)) (ablocks B (cg_lyc g) (cg_Sc g))
  (cg_lyc g) (cg_own g) x).
{ destruct Hx as [Hx | Hx];
  [ destruct Hsg as (_ & _ & _ & Htw & _) | destruct Hdt as (_ & _ & _ & Htw & _) ]; exact (proj1 (Htw x Hx)). }
destruct Hw as [H | [(H1 & b & m & Hin & Hr) | [(b & m & Hin & Hn & Hr) | (cid & p & Hin & Hr)]]].
- left. exact H.
- right; left. split; [exact H1|]. exists b, m. split; [exact (Permutation_in _ (Permutation_sym Hperm) Hin) | exact Hr].
- right; right; left. exists b, m. split; [exact (Permutation_in _ (Permutation_sym Hperm) Hin)|]. split; [exact Hn | exact Hr].
- right; right; right. exists cid, p. split; [right; exact Hin|]. rewrite (Efa cid p). exact Hr.
Qed.
Lemma l2_awr : forall g pos ly2 S2 W2 mem2 md2 E rs, ct_pre B g -> JRN g pos ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) ->
  (skeleton rs = skeleton (l2_mem true) \/ skeleton rs = skeleton (l2_mem false)) ->
  ct_wr g (bv_unsigned (ew E 10)) -> ct_wr g (bv_unsigned (ew E 33)) ->
  awr_ok E rs (cg_STK g) (cg_sp0 g) (cg_FP g) (ablocks B (cg_ly g) (cg_S g)) (ablocks B ly2 S2) ly2 ((1, pos) :: cg_own g).
Proof.
intros g pos ly2 S2 W2 mem2 md2 E rs Hpre HJ Hperm Hsk H10 H33 a Hin.
destruct (l2_wrange E rs a Hsk Hin) as [-> | ->]; apply (l2_awr_byte g pos ly2 S2 W2 mem2 md2); assumption.
Qed.

(* ---- the second loop's step (the plain walk's ct2_neg / ct2_nodot / ct2_dot) ---------------------------------- *)
Lemma l2_ct2_neg : forall n s dot i k sg d, n - 8 + i < 0 ->
  ct2_go n s dot i (S k) sg d = ct2_go n s dot (i + 1) k (sg ++ [0]) d.
Proof.
intros n s dot i k sg d H. cbn [ct2_go]. replace (i - (8 - n)) with (n - 8 + i) by lia.
rewrite (proj2 (Z.ltb_lt _ _) H), (proj2 (Z.leb_gt 0 _) H). reflexivity.
Qed.
Lemma l2_ct2_nodot : forall n s dot i k sg d, 0 <= n - 8 + i -> nth (Z.to_nat (n - 8 + i)) dot 0 = 0 ->
  ct2_go n s dot i (S k) sg d = ct2_go n s dot (i + 1) k (sg ++ [nth (Z.to_nat (n - 8 + i)) s 0]) d.
Proof.
intros n s dot i k sg d H H0. cbn [ct2_go]. replace (i - (8 - n)) with (n - 8 + i) by lia.
rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.leb_le _ _) H), H0. reflexivity.
Qed.
Lemma l2_ct2_dot : forall n s dot i k sg d, 0 <= n - 8 + i -> nth (Z.to_nat (n - 8 + i)) dot 0 <> 0 ->
  ct2_go n s dot i (S k) sg d =
  if i =? 7 then (E_RANGE, sg ++ [nth (Z.to_nat (n - 8 + i)) s 0], d)
  else ct2_go n s dot (i + 1) k (sg ++ [nth (Z.to_nat (n - 8 + i)) s 0]) (Z.lor d (2 ^ i)).
Proof.
intros n s dot i k sg d H H0. cbn [ct2_go]. replace (i - (8 - n)) with (n - 8 + i) by lia.
rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.leb_le _ _) H), (proj2 (Z.eqb_neq _ _) H0). reflexivity.
Qed.

(* ---- the walk's tactics ---------------------------------------------------------------------------------------- *)
(* a fact of the start env read in a later env (the runs only add token atoms above 39) *)
Ltac pe H := rewrite ?ew_ewset_other by lia; exact H.
Ltac l2_ewr n := lazymatch goal with |- context [ew ?E n] => lazymatch goal with H : ew E n = _ |- _ => rewrite H end end.
(* the write premise of a run *)
Ltac l2_awr_t := idtac; lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
  eapply (l2_awr _ _ _ _ _ _ _ Ea rsa); [eassumption | eassumption | eassumption
  | first [left; vm_compute; reflexivity | right; vm_compute; reflexivity]
  | rewrite ?ew_ewset_other by lia; l2_ewr 10%nat; unfold w64; rewrite unsigned_lit_small by lia; unfold ct_wr; lia
  | rewrite ?ew_ewset_other by lia; l2_ewr 33%nat; rewrite unsigned_lit_small by lia; unfold ct_wr; lia ] end.
(* a run's writes are seg[i] or dt *)
Ltac l2_kwr := idtac; let a := fresh "a" in let Hin := fresh "Hin" in intros a Hin; cbv beta;
  lazymatch type of Hin with in_wrange ?Ef ?rsf _ =>
  let HW := fresh "HW" in
  pose proof (l2_wrange Ef rsf a ltac:(first [left; vm_compute; reflexivity | right; vm_compute; reflexivity]) Hin) as HW;
  rewrite ?ew_ewset_other in HW by lia;
  lazymatch type of HW with _ = bv_unsigned (ew ?E0 _) \/ _ =>
    lazymatch goal with H10 : ew E0 10 = _, H33 : ew E0 33 = _ |- _ => rewrite H10, H33 in HW end end;
  unfold w64 in HW; rewrite !unsigned_lit_small in HW by lia; exact HW end.
(* the presence of bytes through a run *)
Ltac l2_pres := match goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict _ ?m2),
  HPR : forall a, apresent ?H ?m0 a -> apresent ?H ?m1 a |- _ =>
  let P := fresh "P" in pose proof (fun a (h : apresent H m0 a) => apresent_grows H m1 m2 a HG (HPR a h)) as P;
  clear HPR; rename P into HPR end.
Ltac l2_step := l2_pres; cw_keep l2_kwr.
(* a0 .. at the stop, as the engine's value *)
Ltac l2_getreg R := lazymatch goal with |- getr (ms_regs ?msf) ?r = _ =>
  lazymatch goal with HS : st_ok ?segs ?Ex ?ss (restrict ?H msf) |- _ =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  assert (R : getr (ms_regs msf) r = sv_denot Ex e) by exact (st_ok_restrict_reg segs H Ex ss msf r HS) end end.
(* a register the digit keeps *)
Ltac l2_same HE := let R := fresh "R" in l2_getreg R; rewrite R; clear R; rewrite sv_denot_SOff0;
  rewrite ?ew_ewset_other by lia; rewrite HE;
  first [ apply cw_ew_reg; reflexivity
        | rewrite cw_ew_SB; lazymatch goal with C : getr _ 26 = w64 SB |- _ => rewrite C; reflexivity end ].
(* a register that is an offset of a start atom *)
Ltac l2_offr := let R := fresh "R" in l2_getreg R; rewrite R; clear R;
  lazymatch goal with |- sv_denot _ (SOff ?nn _) = _ => cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
   lazymatch goal with H : ew _ nn = w64 _ |- _ => rewrite H end;
   unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
   change (2 ^ Z.of_N 64) with (2 ^ 64); rewrite Z.add_mod_idemp_l by lia; f_equal; lia end.
(* a byte the final state's region j holds at offset 0 *)
Ltac l2_chk j vtac := lazymatch goal with HS : st_ok ?segs ?Ex ?ssx (restrict ?H ?msx) |- val_mem _ _ ?A _ _ =>
  let rs := eval vm_compute in (ss_mem ssx) in let r := eval vm_compute in (nth j rs got_region) in
  let HR := fresh "HR" in pose proof (st_ok_region_nth Ex ssx (restrict H msx) j r HS ltac:(vm_compute; reflexivity)) as HR;
  lazymatch r with YP09.mkRegion (Some ?nb) ?lo ?hi ?wlo ?whi [YP09.mkChunk 0 (CVal ?w ?e)] =>
    replace A with (A + 0) by lia;
    apply (field_of_region Ex _ nb A [YP09.mkChunk 0 (CVal w e)] lo hi wlo whi 0 w e _ HR);
    [ rewrite ?ew_ewset_other by lia; l2_ewr nb; try unfold w64; apply unsigned_lit_small; lia
    | left; reflexivity | vtac | cbn; lia | cbn; lia ] end end.
Ltac kio := first [apply same_io_refl | eapply same_io_trans; [| apply cw_same_io_wvb]; kio].
(* the state at the stop as the cut's configuration *)
Ltac l2_mk := lazymatch goal with HS : st_ok _ ?Ef ?ssf (restrict ?H ?msf) |- _ =>
  rewrite (st_ok_restrict_mkst tfibsegs H Ef ssf msf HS eq_refl) end.
(* register r := atom k, by the value tactic pf *)
Ltac l2_setr r k pf := lazymatch goal with HS : st_ok ?segs ?Ex ?ssx (restrict ?H ?ms) |- _ =>
  let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
  let HS2 := fresh "HS" in
  assert (HS2 : st_ok segs Ex (mkSS (ss_pc ssx) (sr_set (ss_regs ssx) r (SOff k 0)) (ss_mem ssx) (ss_resv ssx)
    (ss_facts ssx)) (restrict H ms));
  [ apply (ast_ok_set_reg_fp segs Ex ssx (restrict H ms) r (SOff k 0) HS eq_refl);
    change (ms_regs (restrict H ms)) with (ms_regs ms);
    rewrite (st_ok_restrict_reg segs H Ex ssx ms r HS);
    change (sr_get (ss_regs ssx) r) with e; rewrite sv_denot_SOff0; pf
  | clear HS; rename HS2 into HS; norm_ss HS ] end.
(* a UBSan branch to the trap: its taken side contradicts the value lemma pf (pf rewrites Hc to false = true) *)
Ltac l2_trap Hc pf := cw_branch Hc; [ exfalso; lazymatch type of Hc with branch_taken _ (sv_denot ?Ec _) _ = _ =>
  pf Ec; discriminate Hc end |].

(* ---- the segment --------------------------------------------------------------------------------------------- *)
Theorem ct_l2_holds : ct_seg_L2 B MT RLO RHI SEG7TBL.
Proof using MTL TL LAWS ML.
unfold ct_seg_L2. intros g pos kk W2 c2 Hpre Hnow Hcut.
destruct Hcut as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & Hperm & Hni & Hio & Hmo & Hcom & HP).
destruct HP as (i & n & d & s & dot & sacc & R10 & R5 & R12 & R13 & R14 & R15 & R16 & R17 & R27 & R29 & R18 & R19
  & Hkk & Hi & Hspec & Hl1 & Hlen & Hsacc & Hd & Harr & Hseg & Hdt).
pose proof (Hnow pos ly2 S2 W2 mem2 md2 HJ HK Hperm Hni) as (_ & Hrsg & Hrdt & _).
pose proof Hcom as (C8 & C2 & C9 & C3 & C4 & C24 & C26 & _).
pose proof Hl1 as ((Hn & Hdl & Hdz) & Hdot & Hsl & Hs).
destruct (l2_pre g Hpre) as (_ & Hsg & Hdtc & Hlsj & Hdisj & Hce & H47 & _).
destruct (l2_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (HF0 & HFc & _ & _).
pose proof asan_consts as (CC1 & _).
pose proof alloc_ceiling_lt as Hlt.
pose proof Hsg as (Hsg0 & Hsg63 & _). pose proof Hdtc as (Hdt0 & Hdt63 & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (Z.mod_pos_bound (cg_dj g) 256 ltac:(lia)) as Hdjm.
pose proof (l2_nth_range (fun v => 0 <= v < 128) s (Z.to_nat (n - 8 + i)) Hs ltac:(cbv beta; lia)) as Hsv. cbv beta in Hsv.
pose proof (l2_nth_range (fun v => 0 <= v <= 1) dot (Z.to_nat (n - 8 + i)) Hdot ltac:(cbv beta; lia)) as Hdv. cbv beta in Hdv.
assert (Hkk' : Z.of_nat kk = 8 - (i + 1)) by lia.
unfold cfg_at. change (w64 PC_L2) with (Z_to_bv 64 PC_L2).
pose proof HJ as HJ1. rename HJ into HJb. rename HJ1 into HJ.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (a = cg_sg g + i \/ a = cg_dt g) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
assert (HPR : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros a h; exact h).
destruct (Z_lt_ge_dec (n - 8 + i) 0) as [Hneg | Hnn].
- (* from < 0: seg[i] := 0 *)
  destruct (l2_start false g pos ly2 S2 regs2 mem2 md2 W2 i n s dot Hpre HJb Hperm Hcom Hrsg Hrdt R10 R5 Hi Hl1 Harr
    Hdt ltac:(discriminate)) as (HS & SHOK).
  remember (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) as E eqn:HE.
  assert (E10 : ew E 10 = w64 (cg_sg g + i)) by (rewrite HE, (cw_ew_reg regs2 _ 10 10%bv eq_refl); exact R10).
  assert (E12 : ew E 12 = w64 d) by (rewrite HE, (cw_ew_reg regs2 _ 12 12%bv eq_refl); exact R12).
  assert (E13 : ew E 13 = w64 (8 - i)) by (rewrite HE, (cw_ew_reg regs2 _ 13 13%bv eq_refl); exact R13).
  assert (E14 : ew E 14 = w64 i) by (rewrite HE, (cw_ew_reg regs2 _ 14 14%bv eq_refl); exact R14).
  assert (E15 : ew E 15 = w64 (8 - n)) by (rewrite HE, (cw_ew_reg regs2 _ 15 15%bv eq_refl); exact R15).
  assert (E16 : ew E 16 = w64 7) by (rewrite HE, (cw_ew_reg regs2 _ 16 16%bv eq_refl); exact R16).
  assert (E17 : ew E 17 = w64 1) by (rewrite HE, (cw_ew_reg regs2 _ 17 17%bv eq_refl); exact R17).
  assert (E18 : ew E 18 = w64 (cw_not (cg_F g pos + 32))) by (rewrite HE, (cw_ew_reg regs2 _ 18 18%bv eq_refl); exact R18).
  assert (E19 : ew E 19 = w64 (cw_not (cg_F g pos + 64))) by (rewrite HE, (cw_ew_reg regs2 _ 19 19%bv eq_refl); exact R19).
  assert (E27 : ew E 27 = w64 (cg_F g pos + 32)) by (rewrite HE, (cw_ew_reg regs2 _ 27 27%bv eq_refl); exact R27).
  assert (E29 : ew E 29 = w64 (cg_F g pos + 64)) by (rewrite HE, (cw_ew_reg regs2 _ 29 29%bv eq_refl); exact R29).
  assert (X33 : ew E 33 = Z_to_bv 64 (cg_dt g)) by (rewrite HE; exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 0)).
  assert (X38 : ew E 38 = Z_to_bv 64 (cg_dj g mod 256)) by (rewrite HE; exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 5)).
  assert (X39 : ew E 39 = Z_to_bv 64 (cg_sg g)) by (rewrite HE; exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 6)).
  (* 0x86cd0 subw, sub; bne a1,t1 -> the trap: not taken *)
  cw_run l2_awr_t. l2_step.
  l2_trap Hc1 ltac:(fun Ec => rewrite (l2_bne Ec n i ltac:(pe E14) ltac:(pe E15) ltac:(lia) ltac:(lia)) in Hc1).
  (* bltz a1: taken (from < 0) *)
  cw_run l2_awr_t. l2_step.
  cw_branch Hc2.
  2: { exfalso. lazymatch type of Hc2 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
         rewrite (l2_bltz Ec n i ltac:(pe E14) ltac:(pe E15) ltac:(lia) ltac:(lia)) in Hc2 end.
       apply Z.ltb_ge in Hc2. lia. }
  (* 0x86cf8 t1 = 0, beqz a0 (decided); 0x86d00 t2 = sg, bltu a0,t2 -> the trap: not taken *)
  cw_run l2_awr_t. l2_step.
  l2_trap Hc3 ltac:(fun Ec => rewrite (l2_bltu_sg Ec (cg_sg g) i ltac:(pe E10) ltac:(pe X39) ltac:(lia) ltac:(lia)
    ltac:(lia)) in Hc3).
  (* the check of seg[i], sb t1,0(t0), bltz a1 (decided), 0x86d50 .., to bnez a3 *)
  cw_run_to l2_awr_t 552364. l2_step.
  cw_branch Hc4.
  all: lazymatch type of Hc4 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
    rewrite branch_ne_U, (U_atom_off Ec 13 (8 - i) (-1) ltac:(pe E13) ltac:(lia) ltac:(lia)), U_lit in Hc4 by lia end.
  + (* back to 0x86cd0 *)
    apply negb_true_iff, Z.eqb_neq in Hc4.
    cw_run_to l2_awr_t 552144. l2_step.
    apply SRr_ret. left. l2_mk.
    refine (l2_back g pos kk ly2 S2 regs2 mem2 md2 W2 i n s dot sacc _ _ _ 0 d Hpre HJb HK Hperm Hni Hio Hmo Hcom Hl1
      Harr Hseg Hlen Hsacc _ _ _ HJ _ KE HPR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    * lia.
    * lia.
    * exact Hkk'.
    * kio.
    * l2_chk 0%nat ltac:(reflexivity).
    * lia.
    * apply l2_vm_mod1. l2_chk 1%nat ltac:(rewrite sv_denot_SOff0; pe X38).
    * l2_same HE.
    * l2_same HE.
    * l2_same HE.
    * l2_same HE.
    * l2_same HE.
    * l2_same HE.
    * l2_same HE.
    * l2_offr.
    * l2_offr.
    * l2_offr.
    * l2_offr.
    * let R := fresh "R" in l2_getreg R; rewrite R.
      lazymatch goal with |- sv_denot ?Ex _ = _ => rewrite (l2_D_addiw Ex i ltac:(pe E14) ltac:(lia)) end. reflexivity.
    * l2_offr.
    * l2_offr.
    * l2_offr.
    * l2_offr.
    * l2_offr.
    * l2_offr.
    * l2_offr.
    * rewrite Hspec. apply l2_ct2_neg. lia.
    * lia.
  + (* i = 7: 0x86d88 *dt := dots, a0 := 0, to 0x86dac *)
    apply negb_false_iff, Z.eqb_eq in Hc4.
    assert (Hi7 : i = 7) by lia. assert (Hk0 : kk = 0%nat) by lia. subst kk.
    cw_run_to l2_awr_t 552364. l2_step.
    apply SRr_ret. right. l2_mk.
    refine (l2_exit g pos ly2 S2 regs2 mem2 md2 W2 i n s dot sacc _ _ _ 0 0 d d Hpre HJb HK Hperm Hni Hio Hmo Hcom Hl1
      Harr Hseg Hlen _ HJ _ KE HPR _ _ _ _ _ _ _ _ _ _ _ _ _).
    * lia.
    * kio.
    * l2_chk 0%nat ltac:(reflexivity).
    * lia.
    * l2_chk 1%nat ltac:(rewrite sv_denot_SOff0; pe E12).
    * l2_same HE.
    * l2_same HE.
    * l2_same HE.
    * l2_same HE.
    * l2_same HE.
    * l2_same HE.
    * l2_same HE.
    * let R := fresh "R" in l2_getreg R; rewrite R; reflexivity.
    * rewrite Hspec, l2_ct2_neg by lia. reflexivity.
    * intros _. split; [exact Hi7 | reflexivity].
- (* from >= 0: seg[i] := s[from]; a dot on digit i *)
  assert (Hfrom : 0 <= n - 8 + i) by lia.
  destruct (l2_start true g pos ly2 S2 regs2 mem2 md2 W2 i n s dot Hpre HJb Hperm Hcom Hrsg Hrdt R10 R5 Hi Hl1 Harr
    Hdt (fun _ => Hfrom)) as (HS & SHOK).
  remember (Ereg regs2 (cw_extra (l2_xs g pos n i s dot))) as E eqn:HE.
  assert (E10 : ew E 10 = w64 (cg_sg g + i)) by (rewrite HE, (cw_ew_reg regs2 _ 10 10%bv eq_refl); exact R10).
  assert (E12 : ew E 12 = w64 d) by (rewrite HE, (cw_ew_reg regs2 _ 12 12%bv eq_refl); exact R12).
  assert (E13 : ew E 13 = w64 (8 - i)) by (rewrite HE, (cw_ew_reg regs2 _ 13 13%bv eq_refl); exact R13).
  assert (E14 : ew E 14 = w64 i) by (rewrite HE, (cw_ew_reg regs2 _ 14 14%bv eq_refl); exact R14).
  assert (E15 : ew E 15 = w64 (8 - n)) by (rewrite HE, (cw_ew_reg regs2 _ 15 15%bv eq_refl); exact R15).
  assert (E16 : ew E 16 = w64 7) by (rewrite HE, (cw_ew_reg regs2 _ 16 16%bv eq_refl); exact R16).
  assert (E17 : ew E 17 = w64 1) by (rewrite HE, (cw_ew_reg regs2 _ 17 17%bv eq_refl); exact R17).
  assert (E18 : ew E 18 = w64 (cw_not (cg_F g pos + 32))) by (rewrite HE, (cw_ew_reg regs2 _ 18 18%bv eq_refl); exact R18).
  assert (E19 : ew E 19 = w64 (cw_not (cg_F g pos + 64))) by (rewrite HE, (cw_ew_reg regs2 _ 19 19%bv eq_refl); exact R19).
  assert (E27 : ew E 27 = w64 (cg_F g pos + 32)) by (rewrite HE, (cw_ew_reg regs2 _ 27 27%bv eq_refl); exact R27).
  assert (E29 : ew E 29 = w64 (cg_F g pos + 64)) by (rewrite HE, (cw_ew_reg regs2 _ 29 29%bv eq_refl); exact R29).
  assert (X33 : ew E 33 = Z_to_bv 64 (cg_dt g)) by (rewrite HE; exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 0)).
  assert (X34 : ew E 34 = Z_to_bv 64 (cg_F g pos + 32 + (n - 8 + i)))
    by (rewrite HE; exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 1)).
  assert (X35 : ew E 35 = Z_to_bv 64 (cg_F g pos + 64 + 4 * (n - 8 + i)))
    by (rewrite HE; exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 2)).
  assert (X36 : ew E 36 = Z_to_bv 64 (nth (Z.to_nat (n - 8 + i)) s 0))
    by (rewrite HE; exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 3)).
  assert (X37 : ew E 37 = Z_to_bv 64 (nth (Z.to_nat (n - 8 + i)) dot 0))
    by (rewrite HE; exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 4)).
  assert (X38 : ew E 38 = Z_to_bv 64 (cg_dj g mod 256)) by (rewrite HE; exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 5)).
  assert (X39 : ew E 39 = Z_to_bv 64 (cg_sg g)) by (rewrite HE; exact (cw_ew_x regs2 (l2_xs g pos n i s dot) 6)).
  set (v := nth (Z.to_nat (n - 8 + i)) s 0) in *.
  set (dv := nth (Z.to_nat (n - 8 + i)) dot 0) in *.
  (* 0x86cd0 subw, sub; bne a1,t1 -> the trap: not taken *)
  cw_run l2_awr_t. l2_step.
  l2_trap Hc1 ltac:(fun Ec => rewrite (l2_bne Ec n i ltac:(pe E14) ltac:(pe E15) ltac:(lia) ltac:(lia)) in Hc1).
  (* bltz a1: not taken (from >= 0) *)
  cw_run l2_awr_t. l2_step.
  cw_branch Hc2.
  { exfalso. lazymatch type of Hc2 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
      rewrite (l2_bltz Ec n i ltac:(pe E14) ltac:(pe E15) ltac:(lia) ltac:(lia)) in Hc2 end.
    apply Z.ltb_lt in Hc2. lia. }
  (* bltu a6,a1 -> the trap: not taken *)
  cw_run l2_awr_t. l2_step.
  l2_trap Hc3 ltac:(fun Ec => rewrite (l2_bltu7 Ec n i ltac:(pe E16) ltac:(pe E14) ltac:(pe E15) ltac:(lia) ltac:(lia)
    ltac:(lia)) in Hc3).
  (* bltu s2,a1 -> the trap: not taken *)
  cw_run l2_awr_t. l2_step.
  l2_trap Hc4 ltac:(fun Ec => rewrite (l2_bltu_not Ec 18 (cg_F g pos + 32) n i ltac:(pe E18) ltac:(pe E14) ltac:(pe E15)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hc4).
  (* 0x86ce8 t1 = s11 + a1, to 0x86cec: t1 := atom 34 *)
  cw_run_to l2_awr_t 552172. l2_step.
  l2_setr (6%bv : bv 5) 34%nat ltac:(idtac; lazymatch goal with |- _ = sv_denot ?Ex _ =>
    rewrite (l2_D_t1s Ex n i (cg_F g pos) ltac:(pe E14) ltac:(pe E15) ltac:(pe E27) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia)); pe X34 end).
  (* lbu t1 = s[from], beqz a0 (decided); 0x86d00 t2 = sg, bltu a0,t2 -> the trap: not taken *)
  cw_run l2_awr_t. l2_step.
  l2_trap Hc5 ltac:(fun Ec => rewrite (l2_bltu_sg Ec (cg_sg g) i ltac:(pe E10) ltac:(pe X39) ltac:(lia) ltac:(lia)
    ltac:(lia)) in Hc5).
  (* the check of seg[i], seg[i] := s[from], bltz a1 (decided), a1 = from << 2; bltu s3,a1 -> the trap: not taken *)
  cw_run l2_awr_t. l2_step.
  l2_trap Hc6 ltac:(fun Ec => rewrite (l2_bltu_not4 Ec 19 (cg_F g pos + 64) n i ltac:(pe E19) ltac:(pe E14)
    ltac:(pe E15) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hc6).
  (* 0x86d28 a1 = t4 + a1, to 0x86d2c: a1 := atom 35 *)
  cw_run_to l2_awr_t 552236. l2_step.
  l2_setr (11%bv : bv 5) 35%nat ltac:(idtac; lazymatch goal with |- _ = sv_denot ?Ex _ =>
    rewrite (l2_D_a1d Ex n i (cg_F g pos) ltac:(pe E14) ltac:(pe E15) ltac:(pe E29) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia)); pe X35 end).
  (* the check of dot[from], lw, to beqz a1 *)
  cw_run_to l2_awr_t 552364. l2_step.
  cw_branch Hc7.
  all: lazymatch type of Hc7 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
    rewrite branch_eq_U, (U_atom Ec 37 dv ltac:(pe X37) ltac:(lia)), U_lit in Hc7 by lia end.
  + (* dot[from] = 0: to 0x86d50 .., bnez a3 *)
    apply Z.eqb_eq in Hc7.
    cw_run_to l2_awr_t 552364. l2_step.
    cw_branch Hc8.
    all: lazymatch type of Hc8 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
      rewrite branch_ne_U, (U_atom_off Ec 13 (8 - i) (-1) ltac:(pe E13) ltac:(lia) ltac:(lia)), U_lit in Hc8 by lia end.
    * (* back to 0x86cd0 *)
      apply negb_true_iff, Z.eqb_neq in Hc8.
      cw_run_to l2_awr_t 552144. l2_step.
      apply SRr_ret. left. l2_mk.
      refine (l2_back g pos kk ly2 S2 regs2 mem2 md2 W2 i n s dot sacc _ _ _ v d Hpre HJb HK Hperm Hni Hio Hmo Hcom Hl1
        Harr Hseg Hlen Hsacc _ _ _ HJ _ KE HPR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      -- lia.
      -- lia.
      -- exact Hkk'.
      -- kio.
      -- l2_chk 0%nat ltac:(rewrite sv_denot_SOff0; pe X36).
      -- lia.
      -- apply l2_vm_mod1. l2_chk 1%nat ltac:(rewrite sv_denot_SOff0; pe X38).
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- l2_offr.
      -- l2_offr.
      -- l2_offr.
      -- l2_offr.
      -- let R := fresh "R" in l2_getreg R; rewrite R.
         lazymatch goal with |- sv_denot ?Ex _ = _ => rewrite (l2_D_addiw Ex i ltac:(pe E14) ltac:(lia)) end. reflexivity.
      -- l2_offr.
      -- l2_offr.
      -- l2_offr.
      -- l2_offr.
      -- l2_offr.
      -- l2_offr.
      -- l2_offr.
      -- rewrite Hspec. apply l2_ct2_nodot; [lia | exact Hc7].
      -- lia.
    * (* i = 7: *dt := dots, a0 := 0 *)
      apply negb_false_iff, Z.eqb_eq in Hc8.
      assert (Hi7 : i = 7) by lia. assert (Hk0 : kk = 0%nat) by lia. subst kk.
      cw_run_to l2_awr_t 552364. l2_step.
      apply SRr_ret. right. l2_mk.
      refine (l2_exit g pos ly2 S2 regs2 mem2 md2 W2 i n s dot sacc _ _ _ v 0 d d Hpre HJb HK Hperm Hni Hio Hmo Hcom Hl1
        Harr Hseg Hlen _ HJ _ KE HPR _ _ _ _ _ _ _ _ _ _ _ _ _).
      -- lia.
      -- kio.
      -- l2_chk 0%nat ltac:(rewrite sv_denot_SOff0; pe X36).
      -- lia.
      -- l2_chk 1%nat ltac:(rewrite sv_denot_SOff0; pe E12).
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- let R := fresh "R" in l2_getreg R; rewrite R; reflexivity.
      -- rewrite Hspec, l2_ct2_nodot by lia. reflexivity.
      -- intros _. split; [exact Hi7 | reflexivity].
  + (* dot[from] <> 0: to beq a3,a7 *)
    apply Z.eqb_neq in Hc7.
    cw_run_to l2_awr_t 552364. l2_step.
    cw_branch Hc8.
    all: lazymatch type of Hc8 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
      rewrite branch_eq_U, (U_atom Ec 13 (8 - i) ltac:(pe E13) ltac:(lia)), (U_atom Ec 17 1 ltac:(pe E17) ltac:(lia)) in Hc8 end.
    * (* digit 7 with a dot: 0x86da8 a0 := -11 *)
      apply Z.eqb_eq in Hc8. assert (Hi7 : i = 7) by lia.
      cw_run_to l2_awr_t 552364. l2_step.
      apply SRr_ret. right. l2_mk.
      refine (l2_exit g pos ly2 S2 regs2 mem2 md2 W2 i n s dot sacc _ _ _ v E_RANGE d (cg_dj g mod 256) Hpre HJb HK Hperm
        Hni Hio Hmo Hcom Hl1 Harr Hseg Hlen _ HJ _ KE HPR _ _ _ _ _ _ _ _ _ _ _ _ _).
      -- lia.
      -- kio.
      -- l2_chk 0%nat ltac:(rewrite sv_denot_SOff0; pe X36).
      -- lia.
      -- l2_chk 1%nat ltac:(rewrite sv_denot_SOff0; pe X38).
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- l2_same HE.
      -- let R := fresh "R" in l2_getreg R; rewrite R. unfold w64, E_RANGE. cbn [sv_denot].
         apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
      -- rewrite Hspec, l2_ct2_dot by lia. rewrite (proj2 (Z.eqb_eq i 7) Hi7). reflexivity.
      -- intros Hr. discriminate Hr.
    * (* a dot on digit i < 7: a2 |= 1 << i, to 0x86d50 .., bnez a3 *)
      apply Z.eqb_neq in Hc8. assert (Hi6 : i <= 6) by lia.
      cw_run_to l2_awr_t 552364. l2_step.
      cw_branch Hc9.
      all: lazymatch type of Hc9 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
        rewrite branch_ne_U, (U_atom_off Ec 13 (8 - i) (-1) ltac:(pe E13) ltac:(lia) ltac:(lia)), U_lit in Hc9 by lia end.
      -- apply negb_true_iff, Z.eqb_neq in Hc9.
         cw_run_to l2_awr_t 552144. l2_step.
         apply SRr_ret. left. l2_mk.
         refine (l2_back g pos kk ly2 S2 regs2 mem2 md2 W2 i n s dot sacc _ _ _ v (Z.lor d (2 ^ i)) Hpre HJb HK Hperm Hni
           Hio Hmo Hcom Hl1 Harr Hseg Hlen Hsacc _ _ _ HJ _ KE HPR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
         ++ lia.
         ++ lia.
         ++ exact Hkk'.
         ++ kio.
         ++ l2_chk 0%nat ltac:(rewrite sv_denot_SOff0; pe X36).
         ++ lia.
         ++ apply l2_vm_mod1. l2_chk 1%nat ltac:(rewrite sv_denot_SOff0; pe X38).
         ++ l2_same HE.
         ++ l2_same HE.
         ++ l2_same HE.
         ++ l2_same HE.
         ++ l2_same HE.
         ++ l2_same HE.
         ++ l2_same HE.
         ++ l2_offr.
         ++ l2_offr.
         ++ let R := fresh "R" in l2_getreg R; rewrite R.
            lazymatch goal with |- sv_denot ?Ex _ = _ =>
              rewrite (l2_D_or Ex d i ltac:(pe E12) ltac:(pe E17) ltac:(pe E14) Hd ltac:(lia)) end. reflexivity.
         ++ l2_offr.
         ++ let R := fresh "R" in l2_getreg R; rewrite R.
            lazymatch goal with |- sv_denot ?Ex _ = _ => rewrite (l2_D_addiw Ex i ltac:(pe E14) ltac:(lia)) end. reflexivity.
         ++ l2_offr.
         ++ l2_offr.
         ++ l2_offr.
         ++ l2_offr.
         ++ l2_offr.
         ++ l2_offr.
         ++ l2_offr.
         ++ rewrite Hspec, l2_ct2_dot by lia. rewrite (proj2 (Z.eqb_neq i 7) ltac:(lia)). reflexivity.
         ++ exact (l2_lor_small d i Hd ltac:(lia)).
      -- exfalso. apply negb_false_iff, Z.eqb_eq in Hc9. lia.
Time Qed.
End h.
End d.
