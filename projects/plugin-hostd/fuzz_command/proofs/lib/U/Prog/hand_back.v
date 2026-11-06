(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 684 of its 782 lines of code are new or changed and 919 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/arg_s.v, with its addresses and numbers changed; 1437 of its 1551 lines of code are new or changed and 668 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strlen_c memcpy_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition hbu_mid1 (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (S old : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists m' junk,
    ms' = MS (mkR (Z_to_bv 64 0x162b0) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 S)
                  s1 (Z_to_bv 64 old) (Z_to_bv 64 old) a2 a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 0x3429c) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x18ad0) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 48)%Z [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma hbu_run1 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S lo old : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z -> (213952 <= lo)%Z ->
  rw_cells rsegs m 213944 [C8 (Z_to_bv 64 old)] ->
  evt rsegs (hbu_mid1 ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc S old m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16284) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S lo old ST LO HI FLD.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 11 step.
  apply evt_done. unfold hbu_mid1. do 2 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition hbu_mid2 (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x162c4) sp gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length str) + 1))
                  (Z_to_bv 64 (Z.of_nat (length str) + 1)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15a88) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ bytes_at rsegs m' S (str ++ Z_to_bv 8 0 :: slack).

Lemma hbu_run2 : strlen_contract ->
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S : Z) (str slack : list byte),
  (0 <= S < 2 ^ 64)%Z ->
  bytes_at rsegs m S (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv rsegs m ->
  evt rsegs (hbu_mid2 sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 S) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x162b0) fc None m (seg_rom rsegs)).
Proof.
  intros SLEN ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S str slack HS BS NONUL PAD MI.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB. rewrite length_app in SB. cbn [length] in SB.
  assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (UL : bv_unsigned (Z_to_bv 64 (Z.of_nat (length str))) = Z.of_nat (length str)) by (apply unsigned_lit; lia).
  pose proof (munch_refl [] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str slack).
  1-4: rewrite ?US; first [eassumption | lia].
  cbv delta [mkR].
  do 3 step.
  rewrite ?UL.
  apply evt_done. unfold hbu_mid2.
  do 15 eexists. split; [reflexivity|].
  rewrite ?US in *.
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition hbu_mid3 (sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S p : Z) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x162ec) sp gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length str) + 1))
                  (Z_to_bv 64 (Z.of_nat (length str) + 1)) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15a88) fc None m' (seg_rom rsegs)
    /\ munch [(p, p + (Z.of_nat (length str) + 1)); (213944, 213952)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' p [CB (length (str ++ [Z_to_bv 8 0])) (str ++ [Z_to_bv 8 0])]
    /\ rw_cells rsegs m' 213944 [C8 (Z_to_bv 64 p)]
    /\ bytes_at rsegs m' S (str ++ Z_to_bv 8 0 :: slack).

Lemma hbu_run3 : memcpy_contract -> strlen_contract ->
  forall ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (S p : Z) (w : word) (str slack junk : list byte),
  (0 <= S < 2 ^ 64)%Z -> (0 <= p)%Z ->
  bytes_at rsegs m S (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  rw_cells rsegs m p [CB (length (str ++ [Z_to_bv 8 0])) junk] ->
  rw_cells rsegs m 213944 [C8 w] ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= p \/ p + (Z.of_nat (length str) + 1) <= S)%Z ->
  (S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= 213944 \/ 213952 <= S)%Z ->
  (p + (Z.of_nat (length str) + 1) <= 213944 \/ 213952 <= p)%Z ->
  mem_inv rsegs m ->
  evt rsegs (hbu_mid3 sp gp tp (Z_to_bv 64 0x3429c) s4 s5 s6 s7 s8 s9 s10 s11 F fc S p str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length str) + 1)) (Z_to_bv 64 p)
             a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x3429c) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x162c4) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY SLEN ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S p w str slack junk HS HP BS NONUL PAD DST FLD SEP SEPF SEPP MI.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB.
  rewrite length_app in SB, SEP, SEPF. cbn [length] in SB, SEP, SEPF.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  rewrite length_app in DB. cbn [length] in DB.
  assert (LS : Z.to_nat (Z.of_nat (length str) + 1) = length (str ++ [Z_to_bv 8 0]))
    by (rewrite length_app; cbn [length]; lia).
  assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (UP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 (Z.of_nat (length str) + 1)) = (Z.of_nat (length str) + 1)%Z)
    by (apply unsigned_lit; lia).
  assert (UL : bv_unsigned (Z_to_bv 64 (Z.of_nat (length str))) = Z.of_nat (length str)) by (apply unsigned_lit; lia).
  assert (SRC : bytes_at rsegs m S (str ++ [Z_to_bv 8 0])).
  { replace (str ++ Z_to_bv 8 0 :: slack) with ((str ++ [Z_to_bv 8 0]) ++ slack) in BS
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS. exact (proj1 BS). }
  pose proof (munch_refl [(p, p + (Z.of_nat (length str) + 1)); (213944, 213952)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  call (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (str ++ [Z_to_bv 8 0]) junk).
  1: rewrite US; exact SRC.
  1: rewrite UN, LS; reflexivity.
  1: rewrite UP, UN, LS; exact DST.
  1: rewrite US, UP, UN; lia.
  1: exact MI.
  rewrite ?UP, ?UN, ?US, ?LS in *.
  do 3 step.
  call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str slack).
  1-4: rewrite ?US; first [eassumption | lia].
  cbv delta [mkR].
  do 3 step.
  rewrite ?UL.
  apply evt_done. unfold hbu_mid3.
  do 15 eexists. split; [reflexivity|].
  rewrite ?US in *.
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. eassumption.
Qed.

Definition hbu_fin (ra0 sp0 gp tp s0v s1v s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S p : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom rsegs)
    /\ munch [(p, p + Z.of_nat (length src))]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' p [CB (length src) src]
    /\ bytes_at rsegs m' S src.

Lemma hbu_run4 : memcpy_contract ->
  forall ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s0v s1v s2v s3v : word) (S p : Z)
    (src junk junk2 : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [CB 8 junk; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  bytes_at rsegs m S src ->
  rw_cells rsegs m p [CB (length src) junk2] ->
  (S + Z.of_nat (length src) <= p \/ p + Z.of_nat (length src) <= S)%Z ->
  (0 <= S < 2 ^ 64)%Z -> (0 <= p < 2 ^ 64)%Z -> (48 <= bv_unsigned sp0)%Z ->
  mem_inv rsegs m ->
  evt rsegs (hbu_fin ra0 sp0 gp tp s0v s1v s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 F fc S p src m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length src)))
             (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x162ec) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s0v s1v s2v s3v S p src junk junk2 FR SRC DST SEP HS HP SPR MI.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 (Z.of_nat (length src))) = Z.of_nat (length src)) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(p, p + Z.of_nat (length src))]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 9 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 48 + 48)) with sp0
    by (replace (bv_unsigned sp0 - 48 + 48)%Z with (bv_unsigned sp0) by lia; symmetry; apply Z_to_bv_bv_unsigned).
  call (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src junk2).
  1: rewrite US; exact SRC.
  1: rewrite UN, Nat2Z.id; reflexivity.
  1: rewrite UD, UN, Nat2Z.id; exact DST.
  1: rewrite US, UD, UN; lia.
  1: exact MI.
  rewrite ?UD, ?UN, ?US, ?Nat2Z.id in *.
  apply evt_done. unfold hbu_fin. do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01 YO0u YO0x YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB
xmalloc_c hand_back_c.
Local Open Scope Z_scope.

Fixpoint hb_rof (l : list (Z * Z * bool)) (a : Z) : bool :=
  match l with
  | [] => false
  | (b, z, w) :: l' => if (b <=? a) && (a + 1 <=? b + z) then negb w else hb_rof l' a
  end.

Lemma hb_ro_addr_rof : forall segs a,
  ro_addr segs a = hb_rof (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) segs) (bv_unsigned a).
Proof.
  intros segs a. unfold ro_addr. generalize (bv_unsigned a) as z.
  induction segs as [|sg segs IH]; intros z; [reflexivity|].
  cbn [find_segment map hb_rof]. destruct (_ && _); [reflexivity | apply IH].
Qed.

Lemma hb_rsegs_proj : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) rsegs =
  [(65536, 12288, false); (77824, 61440, false); (139264, 4096, true); (143360, 204800, true)].
Proof. vm_compute. reflexivity. Qed.

Lemma hb_ro_rsegs : forall a, 0 <= a < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 a) = true <-> 65536 <= a < 139264.
Proof.
  intros a Ha. rewrite hb_ro_addr_rof, hb_rsegs_proj, unsigned_lit by lia. cbn [hb_rof].
  repeat match goal with |- context [?u <=? ?v] => destruct (Z.leb_spec u v) end; cbn [andb negb];
    split; intros; first [reflexivity | discriminate | lia | exfalso; lia].
Qed.

Lemma hb_ro_false : forall a, 0 <= a < 2 ^ 64 -> ~ (65536 <= a < 139264) -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha N. destruct (ro_addr rsegs (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  exfalso. apply N. exact (proj1 (hb_ro_rsegs a Ha) E).
Qed.

Lemma hb_rw_c8 : forall segs m a v, bytes_at segs m a (le8 v) -> wr_at segs m a 8 -> rw_cells segs m a [C8 v].
Proof.
  intros segs m a v Hb Hw. split; [split; [split; exact I | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb] | exact Hw].
Qed.

Lemma hb_c8_bytes : forall segs m a v, rw_cells segs m a [C8 v] -> bytes_at segs m a (le8 v).
Proof. intros segs m a v [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma hb_wr_sub : forall segs m a n k j, wr_at segs m a n -> 0 <= k -> k + j <= n -> wr_at segs m (a + k) j.
Proof.
  intros segs m a n k j (H0 & H1 & H2) Hk Hj. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by ring. apply H2. lia.
Qed.

Lemma hb_bytes_pad : forall segs m a bs (k : nat), bytes_at segs m a bs ->
  a + Z.of_nat (length bs) + Z.of_nat k <= 2 ^ 64 ->
  (forall j, (j < k)%nat -> mbyte segs m (a + Z.of_nat (length bs) + Z.of_nat j) <> None) ->
  exists sl, length sl = k /\ bytes_at segs m a (bs ++ sl).
Proof.
  intros segs m a bs k H Hk Hr.
  exists (map (fun j => match mbyte segs m (a + Z.of_nat (length bs) + Z.of_nat j) with
                        | Some b => b | None => Z_to_bv 8 0 end) (seq 0 k)).
  split; [rewrite length_map, length_seq; reflexivity|].
  apply bytes_at_app. split; [exact H|].
  pose proof (bytes_at_bound _ _ _ _ H) as HB.
  split; [lia|]. split; [rewrite length_map, length_seq; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite (map_nth_error _ _ _ (nth_error_seq_lt 0 k i Hi)). cbn [Nat.add].
  change (mrd segs m (wa (a + Z.of_nat (length bs) + Z.of_nat i)))
    with (mbyte segs m (a + Z.of_nat (length bs) + Z.of_nat i)).
  destruct (mbyte segs m (a + Z.of_nat (length bs) + Z.of_nat i)) eqn:E; [reflexivity | exfalso; exact (Hr i Hi E)].
Qed.

Lemma hb_layout_trans : forall A A1 L L1 L2, layout_le A L L1 -> layout_le A1 L1 L2 ->
  (length (st_regions A) <= length (st_regions A1))%nat -> layout_le A L L2.
Proof.
  unfold layout_le. intros A A1 L L1 L2 (E1 & E2 & E3 & E4) (F1 & F2 & F3 & F4) Hl.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite F4 by lia. apply E4. exact Hr.
Qed.

Lemma hb_ptr_le : forall A L L' p n, WF A -> In (p, n) (user_blocks A) -> layout_le A L L' -> ptr_addr L' p = ptr_addr L p.
Proof.
  intros A L L' p n HW Hin (_ & _ & _ & HR).
  destruct (user_blocks_frame A p n HW Hin) as (g & am & idx & fr & Hu & _ & _ & _ & _ & ->).
  pose proof (used_group_prid_lt [] None U0 A g am HW Hu) as Hlt.
  unfold ptr_addr, frame_ptr, slot_start. destruct (am_mem am) as [r o] eqn:E.
  cbn [padd loc_addr prid] in *. rewrite (HR r Hlt). reflexivity.
Qed.

Lemma hb_vm_self : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma hb_vm_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma hb_pw_in2 : forall {X} (Rl : X -> X -> Prop) l x y, pairwise Rl l -> In x l -> In y l -> x <> y -> Rl x y \/ Rl y x.
Proof.
  intros X Rl l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; cbn in *; [destruct Hx|].
  destruct HP as [Hz HP]. destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - congruence.
  - left. apply Hz. exact Hy.
  - right. apply Hz. exact Hx.
  - apply IH; assumption.
Qed.

Lemma hb_perm_swap3 : forall {X} (l1 l2 l3 : list X), Permutation (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof. intros. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. Qed.

Lemma hb_nd_to : forall {X} (l : list X), base.NoDup l -> List.NoDup l.
Proof.
  intros X l H. induction H as [|x l Hx Hl IH]; constructor; [|exact IH].
  intros Hin. apply Hx. clear -Hin. induction l as [|y l IHl]; [destruct Hin|].
  destruct Hin as [<-|Hin]; [left | right; apply IHl, Hin].
Qed.

Lemma hb_nd_of : forall {X} (l : list X), List.NoDup l -> base.NoDup l.
Proof.
  intros X l H. induction H as [|x l Hx Hl IH]; constructor; [|exact IH].
  intros Hin. apply Hx. clear -Hin. revert Hin. induction l as [|y l IHl]; intros Hin; inversion Hin; subst;
    first [left; reflexivity | right; apply IHl; assumption].
Qed.

Definition others (Q : rlay) : list (Z * Z) := concat (l_calls Q) ++ l_spill Q ++ oblk (l_reply Q).

Lemma lay_perm : forall Q, Permutation (lay_blocks Q) (oblk (l_answer Q) ++ others Q).
Proof.
  intros Q. unfold lay_blocks, others.
  replace (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))
    with ((concat (l_calls Q) ++ l_spill Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) by (rewrite <- !app_assoc; reflexivity).
  replace (concat (l_calls Q) ++ l_spill Q ++ oblk (l_reply Q))
    with ((concat (l_calls Q) ++ l_spill Q) ++ oblk (l_reply Q)) by (rewrite <- !app_assoc; reflexivity).
  apply hb_perm_swap3.
Qed.

Lemma others_lay : forall Q pn, In pn (others Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. apply (Permutation_in _ (Permutation_sym (lay_perm Q))). apply in_or_app. right. exact H. Qed.

Lemma lay_cases : forall Q pn, In pn (lay_blocks Q) -> In pn (others Q) \/ l_answer Q = Some pn.
Proof.
  intros Q pn H. apply (Permutation_in _ (lay_perm Q)) in H. apply in_app_iff in H as [H|H]; [|left; exact H].
  right. destruct (l_answer Q) as [pa|]; cbn in H; [destruct H as [<-|[]]; reflexivity | destruct H].
Qed.

Lemma others_fst_ne : forall segs bl m gr sc R Q o k pn, rep_at segs bl m gr sc R Q -> l_answer Q = Some (o, k) ->
  In pn (others Q) -> fst pn <> o.
Proof.
  intros segs bl m gr sc R Q o k pn (_ & _ & _ & _ & _ & HW & _) E Hin Eq.
  pose proof (Permutation_NoDup (Permutation_map fst (lay_perm Q)) (hb_nd_to _ HW)) as ND.
  rewrite E in ND. cbn [oblk app map fst] in ND. inversion ND as [|? ? N _].
  apply N. rewrite <- Eq. apply in_map. exact Hin.
Qed.

Lemma call_at_pn : forall segs bl m a c P pn, call_at segs bl m a c P -> In pn P -> fst pn <> 0 /\ 1 <= snd pn /\ In pn bl.
Proof.
  intros segs bl m a c P pn (_ & _ & HL & _ & _ & _ & HK) Hin.
  destruct (In_nth_error P pn Hin) as [k Ek].
  assert (Hk : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Ek; discriminate).
  destruct (nth_error (snd c) k) as [sx|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (HK k sx pn Es Ek) as (_ & H0 & Hin' & Hsz & _). split; [exact H0|]. split; [lia | exact Hin'].
Qed.

Lemma lay_facts : forall segs bl m gr sc R Q pn, rep_at segs bl m gr sc R Q -> In pn (lay_blocks Q) ->
  fst pn <> 0 /\ 1 <= snd pn /\ In pn bl.
Proof.
  intros segs bl m gr sc R Q pn (HS & HC & HA & HP & HX & HW) Hin.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold lay_blocks in Hin. rewrite !in_app_iff in Hin.
  destruct Hin as [Hin|[Hin|[Hin|Hin]]].
  - apply in_concat in Hin as (P & HP' & HinP).
    destruct (In_nth_error _ _ HP') as [i Ei].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    exact (call_at_pn _ _ _ _ _ _ _ (proj1 (C4 i c P Ec Ei)) HinP).
  - exact (call_at_pn _ _ _ _ _ _ _ C5 Hin).
  - unfold answer_at in HA. revert HA Hin.
    destruct (r_answer R) as [t|]; destruct (l_answer Q) as [[po ko]|]; cbn [oblk In]; intros HA Hin;
      try contradiction.
    destruct Hin as [<-|[]]. destruct HA as (N1 & N2 & N3 & N4 & _). cbn [fst snd] in *.
    split; [exact N2|]. split; [lia | exact N3].
  - unfold reply_at in HP. revert HP Hin.
    destruct (r_reply R) as [y|]; destruct (l_reply Q) as [[po ko]|]; cbn [oblk In]; intros HP Hin;
      try contradiction.
    destruct Hin as [<-|[]]. destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & _). cbn [fst snd] in *.
    split; [exact P3|]. split; [|exact P5]. destruct y; [contradiction | cbn [length] in P6; lia].
Qed.

Lemma rep_at_set_answer : forall segs bl bl' m m' gr sc R Q x p1 n,
  rep_at segs bl m gr sc R Q ->
  (forall a, (gr <= a < gr + REC_SIZE /\ ~ (gr + OFF_ANSWER <= a < gr + OFF_ANSWER + 8)) \/ sc <= a < sc + SC_SIZE ->
     mbyte segs m' a = mbyte segs m a) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs m a -> writable_at segs m' a) ->
  (forall pn, In pn (others Q) -> In pn bl' /\ fst pn <> p1 /\
     forall i, 0 <= i < snd pn -> mbyte segs m' (fst pn + i) = mbyte segs m (fst pn + i)) ->
  bytes_at segs m' (gr + OFF_ANSWER) (le8 (Z_to_bv 64 p1)) ->
  p1 <> 0 -> In (p1, n) bl' -> Z.of_nat (length x) + 1 <= n <= LMAX + 2 ->
  bytes_at segs m' p1 (x ++ [Z_to_bv 8 0]) -> no0 x -> Z.of_nat (length x) <= LMAX ->
  iv_apart p1 n gr REC_SIZE -> iv_apart p1 n sc SC_SIZE ->
  rep_at segs bl' m' gr sc (set_answer R (Some x)) (RLay (l_calls Q) (l_spill Q) (Some (p1, n)) (l_reply Q)).
Proof.
  intros segs bl bl' m m' gr sc R Q x p1 n HR KG KW KQ FB P0 PIN PSZ PB PNO PL PA1 PA2.
  destruct HR as (HS & HC & HA & HP & HX & HW).
  pose proof HS as (S1 & S2 & S3 & S4 & S5).
  pose proof S3 as S3'. unfold iv_apart, REC_SIZE, SC_SIZE in S3'.
  assert (KG1 : forall y, gr <= y < gr + 912 \/ gr + 920 <= y < gr + 960 -> mbyte segs m' y = mbyte segs m y).
  { intros y Hy. apply KG. left. unfold REC_SIZE, OFF_ANSWER. lia. }
  assert (KS1 : forall y, sc <= y < sc + 56 -> mbyte segs m' y = mbyte segs m y).
  { intros y Hy. apply KG. right. unfold SC_SIZE. lia. }
  assert (KQ' : forall pn, In pn (others Q) -> In pn bl' /\
     forall i, 0 <= i < snd pn -> mbyte segs m' (fst pn + i) = mbyte segs m (fst pn + i)).
  { intros pn H. destruct (KQ pn H) as (H1 & _ & H3). split; assumption. }
  unfold rep_at. split; [| split; [| split; [| split; [| split]]]].
  - unfold g1_storage. refine (conj S1 (conj S2 (conj S3 (conj _ _)))).
    + apply (wr_at_keep segs m); [exact S4|]. intros i Hi. apply KW. left. unfold REC_SIZE in *. lia.
    + apply (wr_at_keep segs m); [exact S5|]. intros i Hi. apply KW. right. unfold SC_SIZE in *. lia.
  - destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
    unfold g1_calls. cbn [r_calls r_spill set_answer l_calls l_spill].
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (bytes_at_keep_in segs m m' gr (gr + 912)); [exact C3 | unfold OFF_NCALLS; lia | rewrite length_le4; unfold OFF_NCALLS; lia |].
      intros y Hy. apply KG1. lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hil : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (call_at_keep segs bl bl' m m'); [exact Hc | |].
      * intros y Hy. apply KG1. unfold OFF_CALLS, CALL_SIZE in *. lia.
      * intros pn Hpn. apply KQ'. unfold others. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + apply (call_at_keep segs bl bl' m m'); [exact C5 | |].
      * intros y Hy. apply KS1. unfold CALL_SIZE in Hy. lia.
      * intros pn Hpn. apply KQ'. unfold others. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - unfold answer_at. cbn [r_answer set_answer l_answer fst snd].
    exact (conj FB (conj P0 (conj PIN (conj PSZ (conj PB (conj PNO PL)))))).
  - unfold reply_at in *. cbn [r_reply set_answer l_reply].
    revert HP. destruct (r_reply R) as [y|]; destruct (l_reply Q) as [[p n']|] eqn:EP; intros HP; try contradiction.
    + destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). cbn [fst snd] in *.
      assert (Hq : In (p, n') (others Q)).
      { unfold others. rewrite EP. cbn [oblk]. rewrite !in_app_iff. right. right. left. reflexivity. }
      destruct (KQ' _ Hq) as [Kin Kp]. cbn [fst snd] in Kp.
      split; [apply (bytes_at_keep_in segs m m' (gr + 920) (gr + 960));
              [exact P1 | unfold OFF_REPLY; lia | rewrite length_le8; unfold OFF_REPLY; lia | intros z Hz; apply KG1; lia]|].
      split; [apply (bytes_at_keep_in segs m m' (gr + 920) (gr + 960));
              [exact P2 | unfold OFF_REPLY_SIZE; lia | rewrite length_le8; unfold OFF_REPLY_SIZE; lia | intros z Hz; apply KG1; lia]|].
      split; [exact P3|]. split; [exact P4|]. split; [exact Kin|]. split; [exact P6|]. split; [|exact P8].
      apply (bytes_at_keep segs m); [exact P7|]. intros i Hi. apply Kp. lia.
    + destruct HP as [P1 P2].
      split; [apply (bytes_at_keep_in segs m m' (gr + 920) (gr + 960));
              [exact P1 | unfold OFF_REPLY; lia | rewrite length_le8; unfold OFF_REPLY; lia | intros z Hz; apply KG1; lia]|].
      apply (bytes_at_keep_in segs m m' (gr + 920) (gr + 960));
        [exact P2 | unfold OFF_REPLY_SIZE; lia | rewrite length_le8; unfold OFF_REPLY_SIZE; lia | intros z Hz; apply KG1; lia].
  - destruct HX as (X1 & X2 & X3 & X4 & X5 & X6).
      unfold g1_scalars. cbn [r_refuse r_code r_nreplies r_state r_host set_answer].
      refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
      * apply (bytes_at_keep_in segs m m' gr (gr + 912));
          [exact X1 | unfold OFF_REFUSE; lia | rewrite length_le4; unfold OFF_REFUSE; lia | intros z Hz; apply KG1; lia].
      * apply (bytes_at_keep_in segs m m' gr (gr + 912));
          [exact X2 | unfold OFF_CODE; lia | rewrite length_le4; unfold OFF_CODE; lia | intros z Hz; apply KG1; lia].
      * apply (bytes_at_keep_in segs m m' (gr + 920) (gr + 960));
          [exact X3 | unfold OFF_NREPLIES; lia | rewrite length_le4; unfold OFF_NREPLIES; lia | intros z Hz; apply KG1; lia].
      * apply (bytes_at_keep_in segs m m' (gr + 920) (gr + 960));
          [exact X4 | unfold OFF_STATE; lia | rewrite length_le8; unfold OFF_STATE; lia | intros z Hz; apply KG1; lia].
      * apply (bytes_at_keep_in segs m m' (gr + 920) (gr + 960));
          [exact X5 | unfold OFF_HOST; lia | rewrite length_le8; unfold OFF_HOST; lia | intros z Hz; apply KG1; lia].
  - destruct HW as [ND AP]. split.
      * apply hb_nd_of. apply (Permutation_NoDup (Permutation_map fst (Permutation_sym (lay_perm _)))).
        cbn [l_answer oblk app map fst]. constructor.
        -- intros Hin. apply in_map_iff in Hin as (pn & E & Hpn).
           exact (proj1 (proj2 (KQ pn Hpn)) E).
        -- pose proof (Permutation_NoDup (Permutation_map fst (lay_perm Q)) (hb_nd_to _ ND)) as ND'.
           rewrite map_app in ND'. apply NoDup_app_remove_l in ND'. exact ND'.
      * intros pn Hpn. apply (Permutation_in _ (lay_perm _)) in Hpn. cbn [l_answer oblk app] in Hpn.
        destruct Hpn as [<-|Hpn]; [split; assumption|].
        apply AP. apply others_lay. exact Hpn.
Qed.

Lemma call_post_weaken {rc : YM05.RunCeil} : forall B MR L A regs mem md (E1 E2 : Z -> Prop) L' A' regs' mem' md',
  (forall a, E1 a -> E2 a) -> call_post B MR L A regs mem md E1 L' A' regs' mem' md' ->
  call_post B MR L A regs mem md E2 L' A' regs' mem' md'.
Proof.
  intros B MR L A regs mem md E1 E2 L' A' regs' mem' md' HE (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj _ (conj H9 H10))))))))).
  intros a Ha N1 N2 N3 N4. apply H8; [exact Ha | exact N1 | exact N2 | exact N3 | intros E; apply N4, HE, E].
Qed.

Lemma call_post_refl {rc : YM05.RunCeil} : forall B (MR : MR_t) L A regs mem md E, MR L A mem md -> WF A -> bounded A ->
  (forall a, scratch B regs a -> writable_at (ms_segs B) mem a) ->
  call_post B MR L A regs mem md E L A regs mem md.
Proof.
  intros B MR L A regs mem md E H1 H2 H3 H4.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [apply layout_le_refl|].
  split; [intros; reflexivity|]. split; [intros r _; reflexivity|]. split; [exists (m_vmmaps md); apply hb_vm_self|].
  split; [intros; split; [reflexivity | tauto]|]. split; [intros; reflexivity|]. exact H4.
Qed.

Lemma hb_in_fG : forall a, 0x33ff0 <= a < 0x33ff0 + 1020 -> in_globals frame_G a.
Proof. intros a Ha. exists 0x33ff0, 1020. split; [left; reflexivity | exact Ha]. Qed.

Lemma hb_fG_in : forall a, in_globals frame_G a -> 0x33ff0 <= a < 0x33ff0 + 1020.
Proof. intros a (lo & len & [E|[]] & H). injection E as <- <-. exact H. Qed.

Lemma hb_ro_read : forall m m' a, ro_agree rsegs m -> ro_agree rsegs m' -> ro_addr rsegs (Z_to_bv 64 a) = true ->
  mbyte rsegs m' a = mbyte rsegs m a.
Proof. intros m m' a H H' E. rewrite (mbyte_ro_agree _ _ _ H' E), (mbyte_ro_agree _ _ _ H E). reflexivity. Qed.

Lemma hb_cs_cases : forall (P : Z -> Prop), P 3 -> P 4 -> P 20 -> P 21 -> P 22 -> P 23 -> P 24 ->
  P 25 -> P 26 -> P 27 -> forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 -> P r.
Proof.
  intros P H3 H4 H20 H21 H22 H23 H24 H25 H26 H27 r Hr N2 N8 N9 N18 N19. unfold callee_saved in Hr.
  assert (C : r = 3 \/ r = 4 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
              r = 26 \/ r = 27) by lia.
  repeat (destruct C as [C|C]; [subst r; assumption|]). subst r. assumption.
Qed.

Lemma hb_assoc_nd : forall {X Y} (l : list (X * Y)) x y1 y2, List.NoDup (map fst l) -> In (x, y1) l -> In (x, y2) l ->
  y1 = y2.
Proof.
  intros X Y l. induction l as [|[a c] l IH]; intros x y1 y2 ND H1 H2; [destruct H1|].
  cbn [map fst] in ND. inversion ND as [|? ? N ND']; subst.
  destruct H1 as [E1|H1], H2 as [E2|H2].
  - inversion E1; inversion E2; subst; reflexivity.
  - inversion E1; subst. exfalso. apply N. exact (in_map fst _ _ H2).
  - inversion E2; subst. exfalso. apply N. exact (in_map fst _ _ H1).
  - exact (IH x y1 y2 ND' H1 H2).
Qed.

Lemma hb_wm_nil : forall segs m m' a v, munch [] m m' -> word_mem segs m a v -> word_mem segs m' a v.
Proof. intros segs m m' a v MU W k Hk. rewrite <- (W k Hk). unfold mbyte. rewrite (MU _ I). reflexivity. Qed.

Lemma hb_auxv_nil : forall B s lo m m', munch [] m m' -> auxv_pre B s lo m -> auxv_pre B s lo m'.
Proof.
  intros B s lo m m' MU (av & ar & W1 & W2 & W3 & W4 & R).
  exists av, ar. split; [exact (hb_wm_nil _ _ _ _ _ MU W1)|].
  split; [intros k Hk; exact (hb_wm_nil _ _ _ _ _ MU (W2 k Hk))|].
  split; [exact (hb_wm_nil _ _ _ _ _ MU W3)|].
  split; [exact (hb_wm_nil _ _ _ _ _ MU W4)|]. exact R.
Qed.

Lemma hb_pad_le : forall a pad c, (a + pad) mod 8 = 0 -> 0 <= pad < 8 -> c mod 8 = 0 -> a <= c -> a + pad <= c.
Proof.
  intros a pad c H1 H2 H3 H4. apply Z.mod_divide in H1; [|lia]. apply Z.mod_divide in H3; [|lia].
  destruct H1 as [u Hu]. destruct H3 as [v Hv]. lia.
Qed.

Definition cs_keep (regs R : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 ->
    getr R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).

Section X.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis REC_IMG : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis REC_FREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis BSP : block_slack_present B API.
Hypothesis FREE : free_contract B API.
Hypothesis FREE0 : free_null_contract B.
Hypothesis SLEN : strlen_contract.
Hypothesis MCPY : memcpy_contract.
Hypothesis XM : xmalloc_contract B API.

Lemma hb_not_owned : forall L A mem md L1 A1 mem1 md1 a,
  aa_MR API L A mem md -> aa_MR API L1 A1 mem1 md1 -> (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
  ~ owned B L A a -> ~ owned B L1 A1 a.
Proof using AX CTX.
  intros L A mem md L1 A1 mem1 md1 a HM HM1 Ha NO [Ho|Ho].
  - destruct Ha as [Ha|Ha].
    + destruct (owned_low B _ (aa_laws API) _ _ _ _ a HM1 (or_introl Ho)). lia.
    + exact (NO (CTX L A mem md a HM (ax_img AX L1 A1 mem1 md1 a HM1 Ha Ho))).
  - exact (NO (or_intror Ho)).
Qed.

Lemma hb_same_addr : forall L A mem md a k1 k2, aa_MR API L A mem md -> In (a, k1) (blocks L A) ->
  In (a, k2) (blocks L A) -> 1 <= k1 -> 1 <= k2 -> k1 = k2.
Proof.
  intros L A mem md a k1 k2 HM H1 H2 P1 P2. destruct (Z.eq_dec k1 k2) as [E|NE]; [exact E|]. exfalso.
  destruct (hb_pw_in2 _ _ _ _ (mr_blocks_disjoint B _ (aa_laws API) L A mem md HM) H1 H2 ltac:(congruence)) as [D|D];
    unfold ranges_disjoint in D; cbn in D; lia.
Qed.

Lemma hb_blk_img : forall L A mem md a k i, aa_MR API L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  ~ in_img B (a + i).
Proof using AX.
  intros L A mem md a k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & E & Hq).
  cbn in E. injection E as <- <-. exact (ax_blocks_img AX L A mem md q k' i HM Hq Hi).
Qed.

Lemma hb_blk_read : forall L A mem md q k a, aa_MR API L A mem md -> In (q, k) (blocks L A) ->
  q <= a < 8 * ((q + k + 7) / 8) -> mbyte (ms_segs B) mem a <> None.
Proof using BSP.
  intros L A mem md q k a HM Hin Ha.
  assert (P : present mem a).
  { destruct (Z_lt_ge_dec a (q + k)) as [H|H].
    - replace a with (q + (a - q)) by ring. exact (proj1 (block_facts B _ (aa_laws API) _ _ _ _ _ _ (a - q) HM Hin ltac:(lia))).
    - exact (BSP L A mem md q k a HM Hin ltac:(lia)). }
  destruct P as [bb E]. unfold mbyte. rewrite E. discriminate.
Qed.

Theorem hand_back_holds : hand_back_contract B API.
Proof using SEGS FREE_PC ERRNO_LOW GOTG REC_IMG REC_FREE AX CTX BSP FREE FREE0 SLEN MCPY XM.
  unfold hand_back_contract, hand_back_ret.
  intros L A regs mem md s x slack R O b PRE A0 SRC NONUL LMX PAD DISJ HOME REP OAP RES ROOM RA.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold HAND_BACK_K, XMALLOC_K, HAND_BACK, LMAX in *. change ALLOC_STACK with 8192 in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (Nat2Z.is_nonneg (length x)) as L0.
  set (l := Z.of_nat (length x)) in *.
  assert (ROOM1 : room_slots (sb_malloc b (l + 1)) (l + 1))
    by exact (room_slots_mono (sb_malloc b (l + 1)) (sb_malloc (sb_malloc b (l + 1)) (l + 1)) (l + 1) (l + 1)
                (sb_le_malloc (sb_malloc b (l + 1)) (l + 1) ltac:(lia)) ltac:(lia) ROOM).
  assert (LALL : Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) = l + 1 + Z.of_nat (length slack))
    by (rewrite length_app; cbn [length]; lia).
  assert (LSRC : Z.of_nat (length (x ++ [Z_to_bv 8 0])) = l + 1) by (rewrite length_app; cbn [length]; lia).
  rewrite LALL in DISJ, OAP.
  rewrite SEGS in RA, HWS, HERR, SRC.
  unfold str_home in HOME. rewrite SEGS in HOME.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite LALL in SB.
  destruct REP as (Q & HQ & HO).
  pose proof HQ as (HS & HC & HAns & HRep & HX & HW).
  assert (OLD : exists old, Mem.bytes_at (ms_segs B) mem (G_REC + OFF_ANSWER) (Mem.le8 (Z_to_bv 64 old)) /\
     ((old = 0 /\ l_answer Q = None) \/
      (exists ko, old <> 0 /\ l_answer Q = Some (old, ko) /\ In (old, ko) (blocks L A) /\ 1 <= ko))).
  { unfold answer_at in HAns. revert HAns.
    destruct (r_answer R) as [t|]; destruct (l_answer Q) as [[po ko]|] eqn:EA; intros HAns; try contradiction.
    - destruct HAns as (N1 & N2 & N3 & N4 & _). cbn [fst snd] in *. exists po. split; [exact N1|].
      right. exists ko. split; [exact N2|]. split; [reflexivity|]. split; [exact N3 | lia].
    - exists 0. split; [exact HAns | left; split; reflexivity]. }
  destruct OLD as (old & OLDF & OLDC).
  assert (OLDR : old = 0 \/ (4096 <= old /\ old < alloc_ceiling)).
  { destruct OLDC as [[-> _]|(ko & _ & _ & Hin & Hk)]; [left; reflexivity | right].
    destruct (block_facts B _ LAWS _ _ _ _ _ _ 0 HMR Hin ltac:(lia)) as (_ & H1 & H2 & _). lia. }
  assert (FA : G_REC + OFF_ANSWER = 213944) by reflexivity.
  rewrite FA, SEGS in OLDF.
  pose proof HS as (_ & _ & _ & WRG & _). rewrite SEGS in WRG.
  assert (FLD0 : rw_cells rsegs mem 213944 [C8 (Z_to_bv 64 old)]).
  { apply hb_rw_c8; [exact OLDF|].
    replace 213944 with (G_REC + 912) by reflexivity. apply (hb_wr_sub _ _ _ REC_SIZE); [exact WRG | lia | unfold REC_SIZE; lia]. }
  assert (FRO : forall i, 0 <= i < 8 -> ro_addr rsegs (wa (213944 + i)) = false).
  { intros i Hi. unfold wa. apply hb_ro_false; lia. }
  assert (FLDn : rw_cells rsegs (normalize rsegs mem) 213944 [C8 (Z_to_bv 64 old)]).
  { apply rw_cells_normalize; [exact RA | exact FLD0 |]. intros i Hi. cbn in Hi. apply FRO. lia. }
  assert (ST : stk rsegs (normalize rsegs mem) (bv_unsigned sp - 8256) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E].
    assert (NE : normalize rsegs mem (wa a) = mem (wa a)) by (apply normalize_rw; unfold wa; apply ro_addr_hi; lia).
    unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity]. }
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 s) by exact A0. rewrite R10.
    eapply (evt_normalize rsegs); [exact WX | exact RA |].
    eapply hbu_run1; [exact ST | lia | lia | exact FLDn]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (m1n & junk & -> & MU1n & WM1n & FR1n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 WM1n) as WM1.
  pose proof (ro_agree_same rsegs _ _ RA RO1) as RA1.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR1r FR1n) as FR1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x162b0) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 s) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = reg_get regs 9) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_18 : getr R1 18 = reg_get regs 18) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_19 : getr R1 19 = Z_to_bv 64 0x3429c) by (rewrite (getr_of_eqv _ _ 19 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 old) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 48 <= a < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 48, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (Hp & H4 & Hc & _).
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  assert (AUX1 : st_init_done A = false -> auxv_pre B (ly_sec L) (bv_unsigned sp - 48) m1).
  { intros HI. pose proof (HAUX HI) as HAX.
    destruct HAX as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & L1 & L2).
    exists av, ar.
    split.
    { eapply word_mem_munch; [exact MU1 | | exact W1]. intros k Hk.
      assert (SO : owned B L A (ms_libc B + 8 + Z.of_nat k)) by (right; unfold static_owned; lia).
      destruct (owned_low B _ LAWS _ _ _ _ _ HMR SO). split; [lia | apply OUT1; lia]. }
    split.
    { intros k Hk. eapply word_mem_munch; [exact MU1 | | exact (W2 k Hk)]. intros k' Hk'.
      split; [lia | apply OUT1; lia]. }
    split.
    { eapply word_mem_munch; [exact MU1 | | exact W3]. intros k Hk. split; [lia | apply OUT1; lia]. }
    split.
    { eapply word_mem_munch; [exact MU1 | | exact W4]. intros k Hk. split; [lia | apply OUT1; lia]. }
    lia. }
  assert (CP1 : call_pre B (aa_MR API) L A R1 m1 md).
  { split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
    split; [rewrite E1_1; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite SP1; replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring;
            rewrite Z.mod_add by lia; exact HAL|].
    split; [rewrite SP1; change ALLOC_STACK with 8192; lia|].
    split; [rewrite SP1; lia|].
    split; [intros a Ha; rewrite SP1 in Ha; change ALLOC_STACK with 8192 in Ha; rewrite SEGS; apply WM1; apply HWS; lia|].
    split; [rewrite E1_4; exact HTP|].
    split; [intros a Ha; rewrite SEGS; apply WM1; apply HERR; exact Ha|].
    rewrite SP1. exact AUX1. }
  assert (FSTEP : SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x18ad0) m1 (seg_rom rsegs)) md)
    (fun c => exists L1 A1 R2 m2 md1 c1 c2,
       c = mkCfg (mkst R2 (Z_to_bv 64 0x162b0) m2 (seg_rom rsegs)) md1 /\
       call_post B (aa_MR API) L A R1 m1 md (fun a => exists k, In (old, k) (blocks L A) /\ old <= a < old + k)
         L1 A1 R2 m2 md1 /\
       ((old = 0 /\ blocks L A = c1 ++ c2 /\ blocks L1 A1 = c1 ++ c2) \/
        (exists ko, old <> 0 /\ l_answer Q = Some (old, ko) /\ blocks L A = c1 ++ (old, ko) :: c2 /\
           blocks L1 A1 = c1 ++ c2)) /\
       blocks_kept B L A m1 m2 (fun a => a = old) /\
       ro_agree rsegs m2 /\ guard_kept B m1 m2 /\
       (forall q k, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) O -> In (q, k) (user_blocks A1)) /\
       (st_init_done A1 = false -> auxv_pre B (ly_sec L1) (bv_unsigned sp - 48) m2) /\
       (length (st_regions A) <= length (st_regions A1))%nat /\
       res_ok_slots A1 (sb_shift b A A1) /\ sb_le (sb_shift b A A1) b)).
  { destruct OLDC as [[O0 EA]|(ko & ONZ & EA & OIN & OK1)].
    - subst old. eapply SR_mono.
      { pose proof (FREE0 R1 m1 md) as F0. rewrite SEGS, FREE_PC in F0.
        apply F0; [rewrite E1_1; apply bv_eq; vm_compute; reflexivity | exact E1_10 | exact Hh | exact Hl]. }
      intros cfg ->. exists L, A, R1, m1, md, (blocks L A), [].
      split; [rewrite E1_1; reflexivity|].
      split.
      { apply call_post_refl; [exact MR1 | exact HWF | exact HBD |].
        intros a Ha. unfold scratch in Ha. rewrite SP1 in Ha. change ALLOC_STACK with 8192 in Ha.
        rewrite SEGS. destruct Ha as [Ha|Ha]; apply WM1; [apply HWS; lia | apply HERR; exact Ha]. }
      split; [left; split; [reflexivity|]; rewrite app_nil_r; split; reflexivity|].
      split; [intros a k i _ _ _; reflexivity|].
      split; [exact RA1|]. split; [intros i _; reflexivity|].
      split; [intros q k Hq _; exact Hq|].
      split; [exact AUX1|]. split; [lia|]. rewrite sb_shift_refl. split; [exact RES | apply sb_le_refl].
    - assert (OINu : exists q0, In (q0, ko) (user_blocks A) /\ ptr_addr L q0 = old).
      { unfold blocks in OIN. apply in_map_iff in OIN as ([q0 k0] & E & Hq). cbn in E. injection E as E1 E2.
        subst k0. exists q0. split; [exact Hq | exact E1]. }
      destruct OINu as (q0 & Hq0 & PA0).
      assert (ID : st_init_done A = true).
      { destruct (st_init_done A) eqn:E; [reflexivity|]. exfalso.
        pose proof HWF as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinit) & _).
        destruct (Hinit E) as (Hm & _). unfold user_blocks, used_metas in Hq0. rewrite Hm in Hq0. cbn in Hq0. exact Hq0. }
      eapply SR_mono.
      { pose proof (FREE L A R1 m1 md q0 ko b) as F1. rewrite SEGS, FREE_PC in F1.
        apply F1; [exact CP1 | exact RA1 | exact Hq0 | rewrite PA0; exact E1_10 | exact RES]. }
      intros cfg (L1 & A1 & R2 & m2 & md1 & -> & POST & (c1 & c2 & BL1 & BL2) & KEPT & RA2 & GK & UB & INIT & REG & RES1).
      exists L1, A1, R2, m2, md1, c1, c2.
      split; [rewrite E1_1; reflexivity|].
      split.
      { eapply call_post_weaken; [|exact POST]. intros a Ha. exists ko. rewrite <- PA0. split; [rewrite PA0; exact OIN | exact Ha]. }
      split; [right; exists ko; split; [exact ONZ|]; split; [exact EA|]; rewrite <- PA0; split; [exact BL1 | exact BL2]|].
      split; [rewrite <- PA0; exact KEPT|].
      split; [exact RA2|]. split; [exact GK|].
      split.
      { intros q k Hq HnO. apply UB; [exact Hq|]. intros ->. apply HnO. rewrite PA0.
        assert (KK : k = ko) by exact (hb_assoc_nd _ q0 k ko (user_block_ptrs_NoDup A HWF) Hq Hq0).
        subst k. apply HO. apply (Permutation_in _ (Permutation_sym (lay_perm Q))). apply in_or_app. left.
        rewrite EA. cbn [oblk In]. left. reflexivity. }
      split; [intros HI; rewrite (INIT ID) in HI; discriminate|].
      split; [exact REG|].
      rewrite <- (sb_shift_del b L A L1 A1 c1 c2 _ ko BL1 BL2). split; [exact RES1 | apply sb_free_le; lia]. }
  eapply SR_bind; [exact FSTEP|].
  intros cfg (L1 & A1 & R2 & m2 & md1 & c1 & c2 & -> & POST1 & DEC1 & KEPT1 & RA2 & GK1 & UB1 & AUX2 & REG1 & RES1 & SLE).

  destruct POST1 as (HMR1 & HWF1 & HBD1 & HLE1 & HSTAB1 & HPRES1 & HVM1 & HFRAME1 & HBLKS1 & HSCR1).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR1) as (Hh1 & Hl1 & Hmat1).
  assert (EL : l = Z.of_nat (length x)) by reflexivity.
  assert (NOWN : forall L0 A0 m0 md0 a, aa_MR API L0 A0 m0 md0 -> alloc_ceiling <= a -> ~ owned B L0 A0 a).
  { intros L0' A0' m0 md0 a HM Ha Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HM Ho). lia. }
  assert (EOLD : forall a, (exists k, In (old, k) (blocks L A) /\ old <= a < old + k) -> a < alloc_ceiling /\ ~ in_img B a).
  { intros a (k & Hk & Ha). destruct (block_facts B _ LAWS _ _ _ _ _ _ (a - old) HMR Hk ltac:(lia)) as (_ & _ & H3 & _).
    split; [lia|]. replace a with (old + (a - old)) by ring. exact (hb_blk_img L A mem md old k (a - old) HMR Hk ltac:(lia)). }
  assert (HI1 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 48 - 8192 <= a < bv_unsigned sp - 48) ->
     mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)).
  { intros a Ha Hs. rewrite <- SEGS. apply HFRAME1; [left; exact Ha | apply (NOWN _ _ _ _ a HMR) | apply (NOWN _ _ _ _ a HMR1) | |];
      try lia.
    - unfold scratch. rewrite SP1. change ALLOC_STACK with 8192. intros [H|H]; lia.
    - intros HE. destruct (EOLD a HE). lia. }
  assert (REC1 : forall a, in_globals frame_G a ->
     mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)).
  { intros a Ha. destruct (REC_IMG a Ha) as (Ii & Ns & Nc & Ne). pose proof (in_img_low B SEGS a Ii) as Hlo.
    rewrite <- SEGS. apply HFRAME1; [right; exact Ii | exact (REC_FREE L A m1 md a MR1 Ha) | exact (REC_FREE L1 A1 m2 md1 a HMR1 Ha) | |].
    - unfold scratch. rewrite SP1. change ALLOC_STACK with 8192. intros [H|H]; [lia | exact (Ne H)].
    - intros HE. destruct (EOLD a HE). contradiction. }
  set (pad := (- (s + l + 1)) mod 8) in *.
  assert (PADR : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
  assert (PADA : (s + l + 1 + pad) mod 8 = 0).
  { unfold pad. rewrite Zplus_mod_idemp_r. replace (s + l + 1 + - (s + l + 1)) with 0 by ring. reflexivity. }
  assert (PR0 : forall j, 0 <= j < pad -> mbyte rsegs mem (s + l + 1 + j) <> None).
  { intros j Hj E. pose proof SRC as (_ & _ & HB).
    assert (Hlt : (Z.to_nat (l + 1 + j) < length (x ++ Z_to_bv 8 0 :: slack))%nat)
      by (rewrite length_app; cbn [length]; lia).
    specialize (HB (Z.to_nat (l + 1 + j)) Hlt).
    change (mrd rsegs mem (wa (s + Z.of_nat (Z.to_nat (l + 1 + j)))))
      with (mbyte rsegs mem (s + Z.of_nat (Z.to_nat (l + 1 + j)))) in HB.
    rewrite Z2Nat.id in HB by lia. replace (s + (l + 1 + j)) with (s + l + 1 + j) in HB by ring.
    rewrite E in HB. symmetry in HB. apply nth_error_None in HB. lia. }
  assert (TX0 : bytes_at rsegs mem s (x ++ [Z_to_bv 8 0])).
  { replace (x ++ Z_to_bv 8 0 :: slack) with ((x ++ [Z_to_bv 8 0]) ++ slack) in SRC
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in SRC. exact (proj1 SRC). }
  assert (QNE : forall q k, In (q, k) (blocks L A) -> q <= s -> s + (l + 1) <= q + k -> q <> old).
  { intros q k Hq H1 H2 ->. destruct OLDC as [[O0 _]|(ko & ONZ & EA & OIN & OK1)].
    - rewrite O0 in Hq. destruct (block_facts B _ LAWS _ _ _ _ _ _ 0 HMR Hq ltac:(lia)) as (_ & H4 & _). lia.
    - assert (OO : In (old, ko) O).
      { apply HO. apply (Permutation_in _ (Permutation_sym (lay_perm Q))). apply in_or_app. left.
        rewrite EA. cbn [oblk In]. left. reflexivity. }
      pose proof (OAP _ OO) as AP. cbn [fst snd] in AP. unfold iv_apart in AP.
      assert (KK : k = ko) by exact (hb_same_addr L A mem md old k ko HMR Hq OIN ltac:(lia) OK1).
      subst ko. lia. }
  assert (QIN1 : forall q k, In (q, k) (blocks L A) -> q <> old -> In (q, k) (blocks L1 A1)).
  { intros q k Hq Hne. destruct DEC1 as [(_ & BA & BA1)|(ko & _ & _ & BA & BA1)]; rewrite BA1; [rewrite <- BA; exact Hq|].
    rewrite BA in Hq. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left; exact Hq|].
    destruct Hq as [Hq|Hq]; [injection Hq as E _; congruence | right; exact Hq]. }
  assert (RO_PAD : (forall i, 0 <= i < l + 1 -> ro_addr rsegs (Z_to_bv 64 (s + i)) = true) ->
     forall j, 0 <= j < pad -> ro_addr rsegs (Z_to_bv 64 (s + l + 1 + j)) = true).
  { intros H3 j Hj. pose proof (H3 l ltac:(lia)) as Hl'. apply hb_ro_rsegs in Hl'; [|lia].
    apply hb_ro_rsegs; [lia|]. Z.div_mod_to_equations. lia. }
  assert (BLK_PAD : forall q k j, q <= s -> s + (l + 1) <= q + k -> 0 <= j < pad ->
     q <= s + l + 1 + j < 8 * ((q + k + 7) / 8)).
  { intros q k j H1 H2 Hj. Z.div_mod_to_equations. lia. }
  assert (TX2 : bytes_at rsegs m2 s (x ++ [Z_to_bv 8 0]) /\
                (forall j, 0 <= j < pad -> mbyte rsegs m2 (s + l + 1 + j) <> None)).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
    - assert (K : forall i, 0 <= i < l + 1 + pad -> mbyte rsegs m2 (s + i) = mbyte rsegs mem (s + i)).
      { intros i Hi. rewrite (proj1 (HI1 (s + i) ltac:(lia) ltac:(lia))).
        apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
      split.
      + apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LSRC in Hi. apply K. lia.
      + intros j Hj. replace (s + l + 1 + j) with (s + (l + 1 + j)) by ring. rewrite K by lia.
        replace (s + (l + 1 + j)) with (s + l + 1 + j) by ring. exact (PR0 j Hj).
    - pose proof (QNE q k Hq H1 H2) as Hne.
      split.
      + apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LSRC in Hi.
        destruct (block_facts B _ LAWS _ _ _ _ _ _ (s + i - q) HMR Hq ltac:(lia)) as (_ & _ & H4 & _).
        pose proof (KEPT1 q k (s + i - q) Hq Hne ltac:(lia)) as E. replace (q + (s + i - q)) with (s + i) in E by ring.
        rewrite <- SEGS. rewrite E. apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia].
      + intros j Hj. rewrite <- SEGS. apply (hb_blk_read L1 A1 m2 md1 q k); [exact HMR1 | exact (QIN1 q k Hq Hne) |].
        exact (BLK_PAD q k j H1 H2 Hj).
    - split.
      + apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LSRC in Hi.
        exact (hb_ro_read _ _ _ RA RA2 (H3 i Hi)).
      + intros j Hj. rewrite (hb_ro_read _ _ _ RA RA2 (RO_PAD H3 j Hj)). exact (PR0 j Hj). }
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (HPRES1 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_4 : reg_get R2 4 = reg_get regs 4) by exact (eq_trans (HPRES1 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (E2_8 : reg_get R2 8 = Z_to_bv 64 s) by exact (eq_trans (HPRES1 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (E2_9 : reg_get R2 9 = reg_get regs 9) by exact (eq_trans (HPRES1 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (E2_18 : reg_get R2 18 = reg_get regs 18) by exact (eq_trans (HPRES1 18 ltac:(unfold callee_saved; lia)) E1_18).
  assert (E2_19 : reg_get R2 19 = Z_to_bv 64 0x3429c) by exact (eq_trans (HPRES1 19 ltac:(unfold callee_saved; lia)) E1_19).
  assert (CK1 : cs_keep regs R1).
  { unfold cs_keep. apply (hb_cs_cases (fun r => getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))); cbv beta;
      match goal with |- getr _ (Z_to_bv 5 ?k) = _ => rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X1 eq_refl) end;
      reflexivity. }
  assert (CK2 : cs_keep regs R2).
  { intros r Hr N2 N8 N9 N18 N19. rewrite (HPRES1 r Hr). exact (CK1 r Hr N2 N8 N9 N18 N19). }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 48)
                  [CB 8 junk; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (HI1 (bv_unsigned sp - 48 + i) ltac:(lia) ltac:(lia)) as [E W]. split; [exact E | apply W]. }  pose proof XM as XMC. unfold xmalloc_contract in XMC. rewrite SEGS in XMC.
  assert (EP : pad = (- (s + l + 1)) mod 8) by reflexivity.
  destruct TX2 as [TXB2 TXR2].
  destruct (hb_bytes_pad rsegs m2 s (x ++ [Z_to_bv 8 0]) (Z.to_nat pad) TXB2) as (sl1 & SL1 & BS1).
  { rewrite LSRC, Z2Nat.id by lia. lia. }
  { intros j Hj. rewrite LSRC. replace (s + (l + 1) + Z.of_nat j) with (s + l + 1 + Z.of_nat j) by ring.
    apply TXR2. lia. }
  rewrite <- app_assoc in BS1. cbn [app] in BS1.
  eapply evt_SR_canon; [ | exact Hh1 | exact Hl1 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E2_8.
    eapply (evt_normalize rsegs); [exact WX | exact RA2 |].
    eapply (hbu_run2 SLEN);
      [lia | apply bytes_at_normalize; [exact RA2 | exact BS1] | exact NONUL
      | rewrite SL1, Z2Nat.id by lia; lia | apply mem_inv_normalize]. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & RO3) & EQ3).
  destruct Q3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3n
    & -> & MU3n & WM3n & MI3n & BS3n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL3) as [EC3 MR3r].
  revert EC3 MR3r RO3 EQ3. generalize (ms_mem can3) as m3. intros m3 EC3 MR3r RO3 EQ3. subst can3.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3 MU3n) as MU3.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3 WM3n) as WM3.
  pose proof (ro_agree_same rsegs _ _ RA2 RO3) as RA3.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MR3r) BS3n) as BS3.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x162c4) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; exact E2_2).
  assert (E3_4 : getr R3 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs; exact E2_4).
  assert (E3_8 : getr R3 8 = Z_to_bv 64 s) by (rewrite (getr_of_eqv _ _ 8 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_9 : getr R3 9 = Z_to_bv 64 (l + 1)) by (rewrite (getr_of_eqv _ _ 9 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 (l + 1)) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_18 : getr R3 18 = reg_get regs 18) by (rewrite (getr_of_eqv _ _ 18 X3 eq_refl); simp_regs; exact E2_18).
  assert (E3_19 : getr R3 19 = Z_to_bv 64 0x3429c)
    by (rewrite (getr_of_eqv _ _ 19 X3 eq_refl); simp_regs; exact E2_19).
  assert (SP3 : spZ R3 = bv_unsigned sp - 48) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  assert (CK3 : cs_keep regs R3).
  { assert (CK3' : cs_keep R2 R3).
    { unfold cs_keep. apply (hb_cs_cases (fun r => getr R3 (Z_to_bv 5 r) = getr R2 (Z_to_bv 5 r))); cbv beta;
        match goal with |- getr _ (Z_to_bv 5 ?k) = _ => rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X3 eq_refl) end;
        reflexivity. }
    intros r Hr N2 N8 N9 N18 N19. rewrite (CK3' r Hr N2 N8 N9 N18 N19). exact (CK2 r Hr N2 N8 N9 N18 N19). }
  assert (MR3 : aa_MR API L1 A1 m3 md1).
  { eapply (mr_frame B _ LAWS L1 A1 m2 m3 md1 md1 HMR1).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR1 Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU3 | lia | exact I].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR1 Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU3 | lia | exact I | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L1 A1 m2 md1 p n i HMR1 Hin Hi) as (Hp & H4 & Hc & _).
      eapply munch_present; [exact MU3 | lia | exact I | exact Hp].
    - reflexivity.
    - exact Hh1.
    - exact Hl1.
    - exact Hmat1. }
  assert (CP3 : call_pre_k B (aa_MR API) XMALLOC_K L1 A1 R3 m3 md1).
  { split; [exact MR3|]. split; [exact HWF1|]. split; [exact HBD1|].
    split; [rewrite E3_1; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite SP3; replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring;
            rewrite Z.mod_add by lia; exact HAL|].
    split; [rewrite SP3; unfold XMALLOC_K; change ALLOC_STACK with 8192; lia|].
    split; [rewrite SP3; lia|].
    split.
    { intros a Ha. rewrite SP3 in Ha. unfold XMALLOC_K in Ha. change ALLOC_STACK with 8192 in Ha.
      rewrite SEGS. apply WM3.
      destruct (Z_lt_ge_dec a (bv_unsigned sp - 48 - 8192)) as [D|D].
      - apply (proj1 (proj2 (HI1 a ltac:(lia) ltac:(lia)))). apply WM1. apply HWS. lia.
      - rewrite <- SEGS. apply HSCR1. left. rewrite SP1. change ALLOC_STACK with 8192. lia. }
    split; [rewrite E3_4; exact HTP|].
    split; [intros a Ha; rewrite SEGS; apply WM3; rewrite <- SEGS; apply HSCR1; right; exact Ha|].
    intros HI. rewrite SP3. exact (hb_auxv_nil _ _ _ _ _ MU3 (AUX2 HI)). }
  assert (XS : xmalloc_size (l + 1) = l + 1) by (unfold xmalloc_size; destruct (Z.eqb_spec (l + 1) 0); lia).
  eapply SR_bind.
  { eapply (XMC L1 A1 R3 m3 md1 (l + 1) (sb_shift b A A1) CP3 E3_10); [unfold LMAX; lia | exact RES1 | | exact RA3].
    rewrite XS. exact (room_slots_mono _ _ (l + 1) (l + 1) (sb_malloc_mono _ _ (l + 1) SLE) ltac:(lia) ROOM1). }
  intros cfg RET.
  destruct RET as (L2 & A2 & R4 & m4 & md2 & p1 & -> & POST2 & A0' & NZ1 & AL1 & FRESH1 & (b1 & b2 & BLK1 & BLK2)
    & KEPT2 & RA4 & GK2 & UB2 & INIT2 & REG2 & RES2).
  rewrite XS in *.
  try rewrite SEGS in RA4.
  destruct POST2 as (HMR2 & HWF2 & HBD2 & HLE2 & HSTAB2 & HPRES2 & HVM2 & HFRAME2 & HBLKS2 & HSCR2).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & Hmat2).
  pose proof FRESH1 as (FR1_lo & FR1_hi & FR1_img).
  rewrite E3_1.
  assert (INB1 : In (p1, l + 1) (blocks L2 A2)) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
  assert (FNO : forall L0 A0 m0 md0 a, aa_MR API L0 A0 m0 md0 -> 213944 <= a < 213952 -> ~ owned B L0 A0 a).
  { intros Lx Ax m0 md0 a HM Ha. apply (REC_FREE Lx Ax m0 md0 a HM). apply hb_in_fG. lia. }
  assert (FIMG : forall a, 213944 <= a < 213952 -> in_img B a).
  { intros a Ha. exact (proj1 (REC_IMG a (hb_in_fG a ltac:(lia)))). }
  assert (HI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 48 - 8208 <= a < bv_unsigned sp - 48) ->
     mbyte rsegs m4 a = mbyte rsegs m3 a /\ (writable_at rsegs m3 a <-> writable_at rsegs m4 a)).
  { intros a Ha Hs. rewrite <- SEGS. apply HFRAME2.
    - left. exact Ha.
    - apply (NOWN _ _ _ _ a MR3). lia.
    - apply (NOWN _ _ _ _ a HMR2). lia.
    - unfold scratch_k, XMALLOC_K. rewrite SP3. change ALLOC_STACK with 8192. intros [H|H]; lia.
    - intros F. exact F. }
  assert (REC2 : forall a, in_globals frame_G a ->
     mbyte rsegs m4 a = mbyte rsegs m3 a /\ (writable_at rsegs m3 a <-> writable_at rsegs m4 a)).
  { intros a Ha. destruct (REC_IMG a Ha) as (Ii & Ns & Nc & Ne). pose proof (in_img_low B SEGS a Ii) as Hlo.
    rewrite <- SEGS. apply HFRAME2.
    - right. exact Ii.
    - exact (REC_FREE L1 A1 m3 md1 a MR3 Ha).
    - exact (REC_FREE L2 A2 m4 md2 a HMR2 Ha).
    - unfold scratch_k, XMALLOC_K. rewrite SP3. change ALLOC_STACK with 8192. intros [H|H]; [lia | exact (Ne H)].
    - intros F. exact F. }
  assert (E4_2 : reg_get R4 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (HPRES2 2 ltac:(unfold callee_saved; lia)) E3_2).
  assert (E4_4 : reg_get R4 4 = reg_get regs 4) by exact (eq_trans (HPRES2 4 ltac:(unfold callee_saved; lia)) E3_4).
  assert (E4_8 : reg_get R4 8 = Z_to_bv 64 s) by exact (eq_trans (HPRES2 8 ltac:(unfold callee_saved; lia)) E3_8).
  assert (E4_9 : reg_get R4 9 = Z_to_bv 64 (Z.of_nat (length x) + 1))
    by exact (eq_trans (HPRES2 9 ltac:(unfold callee_saved; lia)) E3_9).
  assert (E4_18 : reg_get R4 18 = reg_get regs 18)
    by exact (eq_trans (HPRES2 18 ltac:(unfold callee_saved; lia)) E3_18).
  assert (E4_19 : reg_get R4 19 = Z_to_bv 64 0x3429c)
    by exact (eq_trans (HPRES2 19 ltac:(unfold callee_saved; lia)) E3_19).
  assert (E4_10 : reg_get R4 10 = Z_to_bv 64 p1) by exact A0'.
  assert (CK4 : cs_keep regs R4).
  { intros r Hr N2 N8 N9 N18 N19. rewrite (HPRES2 r Hr). exact (CK3 r Hr N2 N8 N9 N18 N19). }
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 48)
                  [CB 8 junk; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m2); [exact FR2|]. intros i Hi. cbn in Hi.
    split; [apply (munch_mbyte _ _ _ _ _ MU3); [lia | exact I]|].
    apply (munch_writable _ _ _ _ _ MU3); [lia | exact I]. }
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 48)
                  [CB 8 junk; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct (HI2 (bv_unsigned sp - 48 + i) ltac:(lia) ltac:(lia)) as [E W]. split; [exact E | apply W]. }
  assert (FLD1 : rw_cells rsegs m1 213944 [C8 (Z_to_bv 64 old)]).
  { apply (rw_cells_transfer rsegs mem); [exact FLD0|]. intros i Hi. cbn in Hi.
    split; [apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]|].
    apply (munch_writable _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  assert (FLD2 : rw_cells rsegs m2 213944 [C8 (Z_to_bv 64 old)]).
  { apply (rw_cells_transfer rsegs m1); [exact FLD1|]. intros i Hi. cbn in Hi.
    destruct (REC1 (213944 + i) (hb_in_fG (213944 + i) ltac:(lia))) as [E W]. split; [exact E | apply W]. }
  assert (FLD3 : rw_cells rsegs m3 213944 [C8 (Z_to_bv 64 old)]).
  { apply (rw_cells_transfer rsegs m2); [exact FLD2|]. intros i Hi. cbn in Hi.
    split; [apply (munch_mbyte _ _ _ _ _ MU3); [lia | exact I]|].
    apply (munch_writable _ _ _ _ _ MU3); [lia | exact I]. }
  assert (FLD4 : rw_cells rsegs m4 213944 [C8 (Z_to_bv 64 old)]).
  { apply (rw_cells_transfer rsegs m3); [exact FLD3|]. intros i Hi. cbn in Hi.
    destruct (REC2 (213944 + i) (hb_in_fG (213944 + i) ltac:(lia))) as [E W]. split; [exact E | apply W]. }
  assert (QIN2 : forall q k, In (q, k) (blocks L1 A1) -> In (q, k) (blocks L2 A2)).
  { intros q k Hq. rewrite BLK2 in Hq. rewrite BLK1. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff;
      [left; exact Hq | right; right; exact Hq]. }
  assert (TX4 : bytes_at rsegs m4 s (x ++ [Z_to_bv 8 0]) /\
                (forall j, 0 <= j < pad -> mbyte rsegs m4 (s + l + 1 + j) <> None)).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
    - assert (K : forall i, 0 <= i < l + 1 + pad -> mbyte rsegs m4 (s + i) = mbyte rsegs m2 (s + i)).
      { intros i Hi. rewrite (proj1 (HI2 (s + i) ltac:(lia) ltac:(lia))).
        apply (munch_mbyte _ _ _ _ _ MU3); [lia | exact I]. }
      split.
      + apply (bytes_at_transfer rsegs m2); [exact TXB2|]. intros i Hi. rewrite LSRC in Hi. apply K. lia.
      + intros j Hj. replace (s + l + 1 + j) with (s + (l + 1 + j)) by ring. rewrite K by lia.
        replace (s + (l + 1 + j)) with (s + l + 1 + j) by ring. exact (TXR2 j Hj).
    - pose proof (QNE q k Hq H1 H2) as Hne.
      pose proof (QIN1 q k Hq Hne) as Hq1.
      split.
      + apply (bytes_at_transfer rsegs m2); [exact TXB2|]. intros i Hi. rewrite LSRC in Hi.
        destruct (block_facts B _ LAWS _ _ _ _ _ _ (s + i - q) HMR Hq ltac:(lia)) as (_ & H4 & H5 & _).
        pose proof (KEPT2 q k (s + i - q) Hq1 (fun F => F) ltac:(lia)) as E.
        replace (q + (s + i - q)) with (s + i) in E by ring.
        rewrite <- SEGS, E. apply (munch_mbyte _ _ _ _ _ MU3); [lia | exact I].
      + intros j Hj. rewrite <- SEGS. apply (hb_blk_read L2 A2 m4 md2 q k); [exact HMR2 | exact (QIN2 q k Hq1) |].
        exact (BLK_PAD q k j H1 H2 Hj).
    - split.
      + apply (bytes_at_transfer rsegs m2); [exact TXB2|]. intros i Hi. rewrite LSRC in Hi.
        exact (hb_ro_read _ _ _ RA2 RA4 (H3 i Hi)).
      + intros j Hj. rewrite (hb_ro_read _ _ _ RA2 RA4 (RO_PAD H3 j Hj)). exact (TXR2 j Hj). }
  destruct TX4 as [TXB4 TXR4].
  destruct (hb_bytes_pad rsegs m4 s (x ++ [Z_to_bv 8 0]) (Z.to_nat pad) TXB4) as (sl2 & SL2 & BS4).
  { rewrite LSRC, Z2Nat.id by lia. lia. }
  { intros j Hj. rewrite LSRC. replace (s + (l + 1) + Z.of_nat j) with (s + l + 1 + Z.of_nat j) by ring.
    apply TXR4. lia. }
  rewrite <- app_assoc in BS4. cbn [app] in BS4.
  assert (LBS : Z.of_nat (length (x ++ Z_to_bv 8 0 :: sl2)) = l + 1 + pad).
  { rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add, Nat2Z.inj_succ, SL2, Z2Nat.id by lia. unfold l. lia. }
  destruct (present_rw_cells rsegs (normalize rsegs m4) p1 (length (x ++ [Z_to_bv 8 0]))) as [junkd DST4];
    [lia | rewrite LSRC; lia | |].
  { intros i Hi. rewrite LSRC in Hi. destruct (proj1 (block_facts B _ LAWS _ _ _ _ _ _ i HMR2 INB1 Hi)) as [bb E].
    exists bb. rewrite normalize_rw; [exact E|]. apply (ro_addr_out B SEGS); [lia | apply FR1_img; lia]. }
  assert (SEPP1 : s + (l + 1) <= p1 \/ p1 + (l + 1) <= s).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
    - right. lia.
    - pose proof (QIN1 q k Hq (QNE q k Hq H1 H2)) as Hq1. rewrite BLK2 in Hq1.
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR2 BLK1 Hq1) as Dj. lia.
    - destruct (Z_le_gt_dec (s + (l + 1)) p1) as [D|D]; [left; exact D|].
      destruct (Z_le_gt_dec (p1 + (l + 1)) s) as [D'|D']; [right; exact D'|]. exfalso.
      apply (FR1_img (Z.max s p1 - p1)); [lia|].
      replace (p1 + (Z.max s p1 - p1)) with (s + (Z.max s p1 - s)) by lia.
      apply (ro_in_img B SEGS); [lia | apply H3; lia]. }
  assert (P18 : p1 mod 8 = 0). { clear -AL1. Z.div_mod_to_equations. lia. }
  assert (SEPP1' : s + (l + 1 + pad) <= p1 \/ p1 + (l + 1) <= s).
  { destruct SEPP1 as [D|D]; [left | right; exact D].
    replace (s + (l + 1 + pad)) with (s + l + 1 + pad) by ring. apply hb_pad_le; [exact PADA | lia | exact P18 | lia]. }
  assert (SEPF : s + (l + 1 + pad) <= 213944 \/ 213952 <= s).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
    - right. lia.
    - destruct (Z_le_gt_dec (s + (l + 1)) 213944) as [D|D].
      + left. replace (s + (l + 1 + pad)) with (s + l + 1 + pad) by ring.
        apply hb_pad_le; [exact PADA | lia | reflexivity | lia].
      + right. destruct (Z_le_gt_dec 213952 s) as [D'|D']; [exact D'|]. exfalso.
        apply (hb_blk_img L A mem md q k (Z.max s 213944 - q) HMR Hq); [lia|].
        replace (q + (Z.max s 213944 - q)) with (Z.max s 213944) by ring. apply FIMG. lia.
    - pose proof (H3 l ltac:(lia)) as Hl'. apply hb_ro_rsegs in Hl'; [|lia].
      left. replace (s + (l + 1 + pad)) with (s + l + 1 + pad) by ring.
      apply hb_pad_le; [exact PADA | lia | reflexivity | lia]. }
  assert (SEPPF : p1 + (l + 1) <= 213944 \/ 213952 <= p1).
  { destruct (Z_le_gt_dec (p1 + (l + 1)) 213944) as [D|D]; [left; exact D|].
    destruct (Z_le_gt_dec 213952 p1) as [D'|D']; [right; exact D'|]. exfalso.
    apply (FR1_img (Z.max p1 213944 - p1)); [lia|]. replace (p1 + (Z.max p1 213944 - p1)) with (Z.max p1 213944) by ring.
    apply FIMG. lia. }
  assert (FLD4n : rw_cells rsegs (normalize rsegs m4) 213944 [C8 (Z_to_bv 64 old)]).
  { apply rw_cells_normalize; [exact RA4 | exact FLD4 |]. intros i Hi. cbn in Hi. apply FRO. lia. }
  pose proof (bytes_at_normalize rsegs m4 s _ RA4 BS4) as BS4n.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E4_8, E4_9, E4_10, E4_19. try rewrite SEGS.
    eapply (evt_normalize rsegs); [exact WX | exact RA4 |].
    eapply (hbu_run3 MCPY SLEN) with (S := s) (p := p1) (str := x) (slack := sl2) (junk := junkd);
      [lia | lia | exact BS4n | exact NONUL | rewrite SL2, Z2Nat.id by lia; lia | exact DST4 | exact FLD4n
      | rewrite LBS; exact SEPP1' | rewrite LBS; exact SEPF | exact SEPPF | apply mem_inv_normalize]. }
  intros ms5 (can5 & (s5n & Q5 & REL5 & RO5) & EQ5).
  destruct Q5 as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m5n
    & -> & MU5n & WM5n & MI5n & DST5n & FLD5n & BS5n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL5) as [EC5 MR5r].
  revert EC5 MR5r RO5 EQ5. generalize (ms_mem can5) as m5. intros m5 EC5 MR5r RO5 EQ5. subst can5.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m4 RA4) MR5r RO5 MU5n) as MU5.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m4 RA4) MR5r RO5 WM5n) as WM5.
  pose proof (ro_agree_same rsegs _ _ RA4 RO5) as RA5.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR5r DST5n) as DST5.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR5r FLD5n) as FLD5.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MR5r) BS5n) as BS5.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  change (Z.of_nat (length x)) with l in MU5.
  assert (E5_1 : getr R5 1 = Z_to_bv 64 0x162ec) by (rewrite (getr_of_eqv _ _ 1 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X5 eq_refl); simp_regs; exact E4_2).
  assert (E5_4 : getr R5 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X5 eq_refl); simp_regs; exact E4_4).
  assert (E5_8 : getr R5 8 = Z_to_bv 64 s) by (rewrite (getr_of_eqv _ _ 8 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_9 : getr R5 9 = Z_to_bv 64 (l + 1)) by (rewrite (getr_of_eqv _ _ 9 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_10 : getr R5 10 = Z_to_bv 64 (l + 1)) by (rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_18 : getr R5 18 = Z_to_bv 64 p1) by (rewrite (getr_of_eqv _ _ 18 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_19 : getr R5 19 = Z_to_bv 64 0x3429c)
    by (rewrite (getr_of_eqv _ _ 19 X5 eq_refl); simp_regs; reflexivity).
  assert (SP5 : spZ R5 = bv_unsigned sp - 48) by (unfold spZ; rewrite E5_2; apply unsigned_lit; lia).
  assert (CK5 : cs_keep regs R5).
  { assert (CK5' : cs_keep R4 R5).
    { unfold cs_keep. apply (hb_cs_cases (fun r => getr R5 (Z_to_bv 5 r) = getr R4 (Z_to_bv 5 r))); cbv beta;
        match goal with |- getr _ (Z_to_bv 5 ?k) = _ => rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X5 eq_refl) end;
        reflexivity. }
    intros r Hr N2 N8 N9 N18 N19. rewrite (CK5' r Hr N2 N8 N9 N18 N19). exact (CK4 r Hr N2 N8 N9 N18 N19). }
  assert (OUT5 : forall a, 0 <= a < 2 ^ 64 -> ~ (p1 <= a < p1 + (l + 1)) -> ~ (213944 <= a < 213952) ->
            outside [(p1, p1 + (l + 1)); (213944, 213952)] a)
    by (intros a _ H1 H2; cbn [outside]; split; [lia | split; [lia | exact I]]).
  assert (MR5 : aa_MR API L2 A2 m5 md2).
  { eapply (mr_frame B _ LAWS L2 A2 m4 m5 md2 md2 HMR2).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR2 Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU5 | lia | apply OUT5; [lia | |]].
      + intros Hin. apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - p1) HMR2 INB1 ltac:(lia))))).
        replace (p1 + (a - p1)) with a by ring. exact Ho.
      + intros Hf. exact (FNO _ _ _ _ a HMR2 Hf Ho).
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR2 Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU5 | lia | apply OUT5; [lia | |] | exact Hp].
      + intros Hin. apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - p1) HMR2 INB1 ltac:(lia))))).
        replace (p1 + (a - p1)) with a by ring. exact Ho.
      + intros Hf. exact (FNO _ _ _ _ a HMR2 Hf Ho).
    - intros q n i Hin Hi. destruct (mr_blocks B _ LAWS L2 A2 m4 md2 q n i HMR2 Hin Hi) as (Hp & H4 & Hc & _).
      pose proof (ax_blocks_img AX _ _ _ _ q n i HMR2 Hin Hi) as NI.
      destruct (Z_le_gt_dec p1 (ptr_addr L2 q + i)) as [D1|D1];
        [destruct (Z_lt_ge_dec (ptr_addr L2 q + i) (p1 + (l + 1))) as [D2|D2]|].
      + apply (present_of_writable_out B SEGS m5 (ptr_addr L2 q + i) ltac:(lia)); [exact NI|].
        pose proof DST5 as [_ (_ & _ & W)].
        assert (Hb : 0 <= ptr_addr L2 q + i - p1 <
                     Z.of_nat (cells_size [CB (length (x ++ [Z_to_bv 8 0])) (x ++ [Z_to_bv 8 0])]))
          by (cbn [cells_size csize]; rewrite Nat.add_0_r, LSRC; lia).
        specialize (W (ptr_addr L2 q + i - p1) Hb).
        replace (p1 + (ptr_addr L2 q + i - p1)) with (ptr_addr L2 q + i) in W by ring. exact W.
      + eapply munch_present; [exact MU5 | lia | apply OUT5; [lia | lia | intros Hf; exact (NI (FIMG _ Hf))] | exact Hp].
      + eapply munch_present; [exact MU5 | lia | apply OUT5; [lia | lia | intros Hf; exact (NI (FIMG _ Hf))] | exact Hp].
    - reflexivity.
    - exact Hh2.
    - exact Hl2.
    - exact Hmat2. }
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 48)
                  [CB 8 junk; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m4); [exact FR4|]. intros i Hi. cbn in Hi.
    split; [apply (munch_mbyte _ _ _ _ _ MU5); [lia | apply OUT5; lia]|].
    apply (munch_writable _ _ _ _ _ MU5); [lia | apply OUT5; lia]. }
  assert (CP5 : call_pre_k B (aa_MR API) XMALLOC_K L2 A2 R5 m5 md2).
  { split; [exact MR5|]. split; [exact HWF2|]. split; [exact HBD2|].
    split; [rewrite E5_1; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite SP5; replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring;
            rewrite Z.mod_add by lia; exact HAL|].
    split; [rewrite SP5; unfold XMALLOC_K; change ALLOC_STACK with 8192; lia|].
    split; [rewrite SP5; lia|].
    split.
    { intros a Ha. rewrite SP5 in Ha. rewrite SEGS. apply WM5. rewrite <- SEGS. apply HSCR2.
      unfold scratch_k. left. rewrite SP3. lia. }
    split; [rewrite E5_4; exact HTP|].
    split; [intros a Ha; rewrite SEGS; apply WM5; rewrite <- SEGS; apply HSCR2; unfold scratch_k; right; exact Ha|].
    intros HI. rewrite INIT2 in HI. discriminate. }
  eapply SR_bind.
  { eapply (XMC L2 A2 R5 m5 md2 (l + 1) (sb_malloc (sb_shift b A A1) (l + 1)) CP5 E5_10);
      [unfold LMAX; lia | exact RES2 | | exact RA5].
    rewrite XS. exact (room_slots_mono _ _ (l + 1) (l + 1)
                         (sb_malloc_mono _ _ (l + 1) (sb_malloc_mono _ _ (l + 1) SLE)) ltac:(lia) ROOM). }
  intros cfg RET.
  destruct RET as (L' & A' & R6 & m6 & md3 & p2 & -> & POST3 & A0'' & NZ2 & AL2 & FRESH2 & (b1' & b2' & BLK1' & BLK2')
    & KEPT3 & RA6 & GK3 & UB3 & INIT3 & REG3 & RES3).
  rewrite XS in *.
  try rewrite SEGS in RA6.
  destruct POST3 as (HMR3 & HWF3 & HBD3 & HLE3 & HSTAB3 & HPRES3 & HVM3 & HFRAME3 & HBLKS3 & HSCR3).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR3) as (Hh3 & Hl3 & Hmat3).
  pose proof FRESH2 as (FR2_lo & FR2_hi & FR2_img).
  rewrite E5_1.
  assert (INB2 : In (p2, l + 1) (blocks L' A')) by (rewrite BLK1'; apply in_or_app; right; left; reflexivity).
  assert (HI3 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 48 - 8208 <= a < bv_unsigned sp - 48) ->
     mbyte rsegs m6 a = mbyte rsegs m5 a /\ (writable_at rsegs m5 a <-> writable_at rsegs m6 a)).
  { intros a Ha Hs. rewrite <- SEGS. apply HFRAME3.
    - left. exact Ha.
    - apply (NOWN _ _ _ _ a MR5). lia.
    - apply (NOWN _ _ _ _ a HMR3). lia.
    - unfold scratch_k, XMALLOC_K. rewrite SP5. change ALLOC_STACK with 8192. intros [H|H]; lia.
    - intros F. exact F. }
  assert (REC3 : forall a, in_globals frame_G a ->
     mbyte rsegs m6 a = mbyte rsegs m5 a /\ (writable_at rsegs m5 a <-> writable_at rsegs m6 a)).
  { intros a Ha. destruct (REC_IMG a Ha) as (Ii & Ns & Nc & Ne). pose proof (in_img_low B SEGS a Ii) as Hlo.
    rewrite <- SEGS. apply HFRAME3.
    - right. exact Ii.
    - exact (REC_FREE L2 A2 m5 md2 a MR5 Ha).
    - exact (REC_FREE L' A' m6 md3 a HMR3 Ha).
    - unfold scratch_k, XMALLOC_K. rewrite SP5. change ALLOC_STACK with 8192. intros [H|H]; [lia | exact (Ne H)].
    - intros F. exact F. }
  assert (E6_2 : reg_get R6 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (HPRES3 2 ltac:(unfold callee_saved; lia)) E5_2).
  assert (E6_4 : reg_get R6 4 = reg_get regs 4) by exact (eq_trans (HPRES3 4 ltac:(unfold callee_saved; lia)) E5_4).
  assert (E6_8 : reg_get R6 8 = Z_to_bv 64 s) by exact (eq_trans (HPRES3 8 ltac:(unfold callee_saved; lia)) E5_8).
  assert (E6_9 : reg_get R6 9 = Z_to_bv 64 (l + 1)) by exact (eq_trans (HPRES3 9 ltac:(unfold callee_saved; lia)) E5_9).
  assert (E6_10 : reg_get R6 10 = Z_to_bv 64 p2) by exact A0''.
  assert (CK6 : cs_keep regs R6).
  { intros r Hr N2 N8 N9 N18 N19. rewrite (HPRES3 r Hr). exact (CK5 r Hr N2 N8 N9 N18 N19). }
  assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp - 48)
                  [CB 8 junk; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m5); [exact FR5|]. intros i Hi. cbn in Hi.
    destruct (HI3 (bv_unsigned sp - 48 + i) ltac:(lia) ltac:(lia)) as [E W]. split; [exact E | apply W]. }
  assert (BS5' : bytes_at rsegs m5 s (x ++ [Z_to_bv 8 0])).
  { pose proof BS5 as BS5c.
    replace (x ++ Z_to_bv 8 0 :: sl2) with ((x ++ [Z_to_bv 8 0]) ++ sl2) in BS5c by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS5c. exact (proj1 BS5c). }
  assert (TX6 : bytes_at rsegs m6 s (x ++ [Z_to_bv 8 0])).
  { apply (bytes_at_transfer rsegs m5); [exact BS5'|]. intros i Hi. rewrite LSRC in Hi.
    destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
    - exact (proj1 (HI3 (s + i) ltac:(lia) ltac:(lia))).
    - pose proof (QIN2 q k (QIN1 q k Hq (QNE q k Hq H1 H2))) as Hq2.
      pose proof (KEPT3 q k (s + i - q) Hq2 (fun F => F) ltac:(lia)) as E.
      replace (q + (s + i - q)) with (s + i) in E by ring. rewrite <- SEGS. exact E.
    - exact (hb_ro_read _ _ _ RA5 RA6 (H3 i Hi)). }
  destruct (present_rw_cells rsegs (normalize rsegs m6) p2 (length (x ++ [Z_to_bv 8 0]))) as [junke DST6];
    [lia | rewrite LSRC; lia | |].
  { intros i Hi. rewrite LSRC in Hi. destruct (proj1 (block_facts B _ LAWS _ _ _ _ _ _ i HMR3 INB2 Hi)) as [bb E].
    exists bb. rewrite normalize_rw; [exact E|]. apply (ro_addr_out B SEGS); [lia | apply FR2_img; lia]. }
  assert (SEPP2 : s + (l + 1) <= p2 \/ p2 + (l + 1) <= s).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
    - right. lia.
    - pose proof (QIN2 q k (QIN1 q k Hq (QNE q k Hq H1 H2))) as Hq2. rewrite BLK2' in Hq2.
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR3 BLK1' Hq2) as Dj. lia.
    - destruct (Z_le_gt_dec (s + (l + 1)) p2) as [D|D]; [left; exact D|].
      destruct (Z_le_gt_dec (p2 + (l + 1)) s) as [D'|D']; [right; exact D'|]. exfalso.
      apply (FR2_img (Z.max s p2 - p2)); [lia|].
      replace (p2 + (Z.max s p2 - p2)) with (s + (Z.max s p2 - s)) by lia.
      apply (ro_in_img B SEGS); [lia | apply H3; lia]. }
  assert (FR6n : rw_cells rsegs (normalize rsegs m6) (bv_unsigned sp - 48)
                   [CB 8 junk; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                    C8 (reg_get regs 1)]).
  { apply rw_cells_normalize; [exact RA6 | exact FR6 |]. intros i Hi. cbn in Hi. unfold wa. apply ro_addr_hi. lia. }
  pose proof (bytes_at_normalize rsegs m6 s _ RA6 TX6) as TX6n.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E6_2, E6_8, E6_10. try rewrite SEGS.
    replace (reg_get R6 9) with (Z_to_bv 64 (Z.of_nat (length (x ++ [Z_to_bv 8 0]))))
      by (rewrite LSRC; symmetry; exact E6_9).
    eapply (evt_normalize rsegs); [exact WX | exact RA6 |].
    eapply (hbu_run4 MCPY) with (sp0 := sp) (S := s) (p := p2) (src := x ++ [Z_to_bv 8 0]);
      [exact FR6n | exact TX6n | exact DST6 | rewrite LSRC; exact SEPP2 | lia | lia | lia | apply mem_inv_normalize]. }
  intros ms7 (can7 & (s7n & Q7 & REL7 & RO7) & EQ7).
  destruct Q7 as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m7n
    & -> & MU7n & WM7n & MI7n & DST7n & SRC7n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL7) as [EC7 MR7r].
  revert EC7 MR7r RO7 EQ7. generalize (ms_mem can7) as m7. intros m7 EC7 MR7r RO7 EQ7. subst can7.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m6 RA6) MR7r RO7 MU7n) as MU7.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m6 RA6) MR7r RO7 WM7n) as WM7.
  pose proof (ro_agree_same rsegs _ _ RA6 RO7) as RA7.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR7r DST7n) as DST7.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MR7r) SRC7n) as SRC7.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ7 eq_refl eq_refl) as (R7 & -> & X7).
  rewrite LSRC in MU7.
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite RP.
  assert (OUT7 : forall a, 0 <= a < 2 ^ 64 -> ~ (p2 <= a < p2 + (l + 1)) -> outside [(p2, p2 + (l + 1))] a)
    by (intros a _ Ha; cbn [outside]; split; [exact Ha | exact I]).
  assert (MR7 : aa_MR API L' A' m7 md3).
  { eapply (mr_frame B _ LAWS L' A' m6 m7 md3 md3 HMR3).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR3 Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU7 | lia | apply OUT7; [lia|]]. intros Hin.
      apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - p2) HMR3 INB2 ltac:(lia))))).
      replace (p2 + (a - p2)) with a by ring. exact Ho.
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR3 Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU7 | lia | apply OUT7; [lia|] | exact Hp]. intros Hin.
      apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - p2) HMR3 INB2 ltac:(lia))))).
      replace (p2 + (a - p2)) with a by ring. exact Ho.
    - intros q n i Hin Hi. destruct (mr_blocks B _ LAWS L' A' m6 md3 q n i HMR3 Hin Hi) as (Hp & H4 & Hc & _).
      destruct (Z_le_gt_dec p2 (ptr_addr L' q + i)) as [D1|D1];
        [destruct (Z_lt_ge_dec (ptr_addr L' q + i) (p2 + (l + 1))) as [D2|D2]|].
      + apply (present_of_writable_out B SEGS m7 (ptr_addr L' q + i) ltac:(lia)).
        * replace (ptr_addr L' q + i) with (p2 + (ptr_addr L' q + i - p2)) by ring. apply FR2_img. lia.
        * pose proof DST7 as [_ (_ & _ & W)].
          assert (Hb : 0 <= ptr_addr L' q + i - p2 <
                       Z.of_nat (cells_size [CB (length (x ++ [Z_to_bv 8 0])) (x ++ [Z_to_bv 8 0])]))
            by (cbn [cells_size csize]; rewrite Nat.add_0_r, LSRC; lia).
          specialize (W (ptr_addr L' q + i - p2) Hb).
          replace (p2 + (ptr_addr L' q + i - p2)) with (ptr_addr L' q + i) in W by ring. exact W.
      + eapply munch_present; [exact MU7 | lia | apply OUT7; lia | exact Hp].
      + eapply munch_present; [exact MU7 | lia | apply OUT7; lia | exact Hp].
    - reflexivity.
    - exact Hh3.
    - exact Hl3.
    - exact Hmat3. }
  rewrite SEGS in HQ.
  assert (C12 : blocks L1 A1 = c1 ++ c2) by (destruct DEC1 as [(_ & _ & E)|(ko & _ & _ & _ & E)]; exact E).
  assert (CSUB : forall pn, In pn (c1 ++ c2) -> In pn (blocks L A)).
  { intros pn Hp. destruct DEC1 as [(_ & E & _)|(ko & _ & _ & E & _)]; rewrite E; [exact Hp|].
    apply in_app_iff in Hp as [Hp|Hp]; apply in_app_iff; [left; exact Hp | right; right; exact Hp]. }
  assert (B12 : forall pn, In pn (blocks L1 A1) -> In pn (blocks L2 A2)).
  { intros [q k] Hq. exact (QIN2 q k Hq). }
  assert (B2F : forall pn, In pn (blocks L2 A2) -> In pn (blocks L' A')).
  { intros pn Hp. rewrite BLK2' in Hp. rewrite BLK1'. apply in_app_iff in Hp as [Hp|Hp]; apply in_app_iff;
      [left; exact Hp | right; right; exact Hp]. }
  assert (D12 : p1 + (l + 1) <= p2 \/ p2 + (l + 1) <= p1).
  { pose proof INB1 as H. rewrite BLK2' in H. exact (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR3 BLK1' H). }
  assert (OLD2 : (old = 0 /\ l_answer Q = None /\ blocks L A = c1 ++ c2) \/
     (exists ko, old <> 0 /\ l_answer Q = Some (old, ko) /\ 1 <= ko /\ In (old, ko) O /\
        blocks L A = c1 ++ (old, ko) :: c2)).
  { destruct DEC1 as [(O0 & E & _)|(ko & ONZ & EA & E & _)].
    - left. destruct OLDC as [(_ & EA)|(ko & ONZ & _)]; [|congruence]. split; [exact O0|]. split; [exact EA | exact E].
    - right. exists ko. destruct OLDC as [(O0 & _)|(ko' & _ & EA' & _ & K1)]; [congruence|].
      rewrite EA in EA'. inversion EA'; subst.
      split; [exact ONZ|]. split; [exact EA|]. split; [exact K1|]. split; [|exact E].
      apply HO. apply (Permutation_in _ (Permutation_sym (lay_perm Q))). apply in_or_app. left.
      rewrite EA. cbn [oblk In]. left. reflexivity. }
  assert (OTH : forall pn, In pn (others Q) ->
     fst pn <> 0 /\ 1 <= snd pn /\ In pn (blocks L A) /\ fst pn <> old /\ In pn (blocks L1 A1)).
  { intros [pa pk] Hp. destruct (lay_facts _ _ _ _ _ _ _ _ HQ (others_lay Q _ Hp)) as (F0 & F1 & F2). cbn [fst snd] in *.
    assert (Fo : pa <> old).
    { destruct OLDC as [(O0 & _)|(ko & _ & EA & _)]; [rewrite O0; exact F0|].
      exact (others_fst_ne _ _ _ _ _ _ _ _ _ (pa, pk) HQ EA Hp). }
    split; [exact F0|]. split; [exact F1|]. split; [exact F2|]. split; [exact Fo|]. exact (QIN1 pa pk F2 Fo). }
  assert (APART : forall q k, 0 < k -> (forall i, 0 <= i < k -> ~ in_img B (q + i)) ->
     iv_apart q k G_REC REC_SIZE /\ iv_apart q k REC_SC SC_SIZE).
  { intros q k Hk Hn.
    assert (GR : forall c n, 0x33ff0 <= c -> c + n <= 0x33ff0 + 1020 -> 0 < n -> iv_apart q k c n).
    { intros c n H1 H2 H3. unfold iv_apart.
      destruct (Z_le_gt_dec (q + k) c) as [D|D]; [left; exact D|]. right.
      destruct (Z_le_gt_dec (c + n) q) as [D'|D']; [exact D'|]. exfalso.
      apply (Hn (Z.max q c - q)); [lia|]. replace (q + (Z.max q c - q)) with (Z.max q c) by ring.
      exact (proj1 (REC_IMG _ (hb_in_fG (Z.max q c) ltac:(lia)))). }
    split; apply GR; unfold G_REC, REC_SIZE, REC_SC, SC_SIZE; lia. }
  assert (BK : forall a k i, In (a, k) (blocks L A) -> a <> old -> 0 <= i < k ->
     mbyte rsegs m7 (a + i) = mbyte rsegs mem (a + i)).
  { intros a k i Hin Hne Hi.
    destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hin Hi) as (_ & H4 & H5 & _).
    pose proof (hb_blk_img L A mem md a k i HMR Hin Hi) as NI.
    pose proof (QIN1 a k Hin Hne) as Hin1. pose proof (QIN2 a k Hin1) as Hin2.
    assert (DJ1 : a + k <= p1 \/ p1 + (l + 1) <= a).
    { assert (H : In (a, k) (b1 ++ b2)) by (rewrite <- BLK2; exact Hin1).
      exact (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR2 BLK1 H). }
    assert (DJ2 : a + k <= p2 \/ p2 + (l + 1) <= a).
    { assert (H : In (a, k) (b1' ++ b2')) by (rewrite <- BLK2'; exact Hin2).
      exact (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR3 BLK1' H). }
    rewrite <- SEGS.
    rewrite (munch_mbyte _ _ _ _ _ MU7) by (first [lia | apply OUT7; lia]).
    rewrite (KEPT3 a k i Hin2 (fun F => F) Hi).
    rewrite (munch_mbyte _ _ _ _ _ MU5) by (first [lia | apply OUT5; [lia | lia | intros Hf; exact (NI (FIMG _ Hf))]]).
    rewrite (KEPT2 a k i Hin1 (fun F => F) Hi).
    rewrite (munch_mbyte _ _ _ _ _ MU3) by (first [lia | exact I]).
    rewrite (KEPT1 a k i Hin Hne Hi).
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  assert (RECK : forall a, in_globals frame_G a -> ~ (213944 <= a < 213952) -> mbyte rsegs m7 a = mbyte rsegs mem a).
  { intros a Ha Hf. pose proof (in_img_low B SEGS a (proj1 (REC_IMG a Ha))) as Hlo.
    assert (NQ1 : ~ (p1 <= a < p1 + (l + 1))).
    { intros Hp. apply (FR1_img (a - p1)); [lia|]. replace (p1 + (a - p1)) with a by ring.
      exact (proj1 (REC_IMG a Ha)). }
    assert (NQ2 : ~ (p2 <= a < p2 + (l + 1))).
    { intros Hp. apply (FR2_img (a - p2)); [lia|]. replace (p2 + (a - p2)) with a by ring.
      exact (proj1 (REC_IMG a Ha)). }
    rewrite (munch_mbyte _ _ _ _ _ MU7) by (first [lia | apply OUT7; lia]).
    rewrite (proj1 (REC3 a Ha)).
    rewrite (munch_mbyte _ _ _ _ _ MU5) by (first [lia | apply OUT5; lia]).
    rewrite (proj1 (REC2 a Ha)).
    rewrite (munch_mbyte _ _ _ _ _ MU3) by (first [lia | exact I]).
    rewrite (proj1 (REC1 a Ha)).
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  assert (RECW : forall a, in_globals frame_G a -> writable_at rsegs mem a -> writable_at rsegs m7 a).
  { intros a Ha W. pose proof (in_img_low B SEGS a (proj1 (REC_IMG a Ha))) as Hlo.
    apply WM7. apply (proj1 (proj2 (REC3 a Ha))). apply WM5. apply (proj1 (proj2 (REC2 a Ha))). apply WM3.
    apply (proj1 (proj2 (REC1 a Ha))).
    apply (proj1 (munch_writable _ _ _ _ a MU1 ltac:(lia) (OUT1 a ltac:(lia) ltac:(lia)))). exact W. }
  assert (PB : bytes_at rsegs m7 p1 (x ++ [Z_to_bv 8 0])).
  { pose proof DST5 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    apply (bytes_at_transfer rsegs m5); [exact HB|]. intros i Hi. rewrite LSRC in Hi.
    rewrite (munch_mbyte _ _ _ _ _ MU7) by (first [lia | apply OUT7; lia]).
    rewrite <- SEGS. exact (KEPT3 p1 (l + 1) i INB1 (fun F => F) Hi). }
  assert (PB2 : bytes_at rsegs m7 p2 (x ++ [Z_to_bv 8 0])).
  { pose proof DST7 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
  assert (FLD7 : bytes_at rsegs m7 213944 (le8 (Z_to_bv 64 p1))).
  { apply (bytes_at_transfer rsegs m5); [exact (hb_c8_bytes _ _ _ _ FLD5)|].
    intros i Hi. rewrite length_le8 in Hi. cbn in Hi.
    assert (NQ : ~ (p2 <= 213944 + i < p2 + (l + 1))).
    { intros Hp. apply (FR2_img (213944 + i - p2)); [lia|]. replace (p2 + (213944 + i - p2)) with (213944 + i) by ring.
      apply FIMG. lia. }
    rewrite (munch_mbyte _ _ _ _ _ MU7) by (first [lia | apply OUT7; lia]).
    exact (proj1 (REC3 (213944 + i) (hb_in_fG (213944 + i) ltac:(lia)))). }
  assert (BCH : forall pn, In pn (blocks L' A') <->
     In pn (c1 ++ c2) \/ pn = (p1, l + 1) \/ pn = (p2, l + 1)).
  { intros pn. split.
    - intros Hp. rewrite BLK1' in Hp. apply in_app_iff in Hp as [Hp|[Hp|Hp]].
      + assert (H2 : In pn (blocks L2 A2)) by (rewrite BLK2'; apply in_or_app; left; exact Hp).
        rewrite BLK1 in H2. apply in_app_iff in H2 as [H2|[H2|H2]].
        * left. rewrite <- C12, BLK2. apply in_or_app. left. exact H2.
        * right. left. symmetry. exact H2.
        * left. rewrite <- C12, BLK2. apply in_or_app. right. exact H2.
      + right. right. symmetry. exact Hp.
      + assert (H2 : In pn (blocks L2 A2)) by (rewrite BLK2'; apply in_or_app; right; exact Hp).
        rewrite BLK1 in H2. apply in_app_iff in H2 as [H2|[H2|H2]].
        * left. rewrite <- C12, BLK2. apply in_or_app. left. exact H2.
        * right. left. symmetry. exact H2.
        * left. rewrite <- C12, BLK2. apply in_or_app. right. exact H2.
    - intros [Hp|[Hp|Hp]].
      + apply B2F. apply B12. rewrite C12. exact Hp.
      + subst pn. apply B2F. exact INB1.
      + subst pn. exact INB2. }
  assert (NP1 : ~ In (p1, l + 1) (c1 ++ c2)).
  { intros H. rewrite <- C12, BLK2 in H. pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR2 BLK1 H). lia. }
  assert (NP2 : ~ In (p2, l + 1) (c1 ++ c2)).
  { intros H. assert (H2 : In (p2, l + 1) (b1' ++ b2')) by (rewrite <- BLK2'; apply B12; rewrite C12; exact H).
    pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR3 BLK1' H2). lia. }
  set (Q' := RLay (l_calls Q) (l_spill Q) (Some (p1, l + 1)) (l_reply Q)).
  assert (OQ : forall pn, In pn (lay_blocks Q') <-> (In pn O /\ fst pn <> old) \/ pn = (p1, l + 1)).
  { intros pn. split.
    - intros Hp. destruct (lay_cases Q' pn Hp) as [Ho|Ha].
      + left. destruct (OTH pn Ho) as (_ & _ & _ & F3 & _). split; [apply HO; apply others_lay; exact Ho | exact F3].
      + right. unfold Q' in Ha. cbn [l_answer] in Ha. inversion Ha. reflexivity.
    - intros [(Hp & Hne) | ->].
      + apply HO in Hp. destruct (lay_cases Q pn Hp) as [Ho|Ha].
        * apply others_lay. exact Ho.
        * exfalso. destruct OLDC as [(_ & EA)|(ko & _ & EA & _)]; rewrite EA in Ha; [discriminate|].
          inversion Ha; subst. apply Hne. reflexivity.
      + apply (Permutation_in _ (Permutation_sym (lay_perm Q'))). apply in_or_app. left.
        unfold Q'. cbn [l_answer oblk In]. left. reflexivity. }
  assert (OP2 : forall pn, In pn (lay_blocks Q') -> fst pn <> p2).
  { intros pn Hp. destruct (lay_cases Q' pn Hp) as [Ho|Ha].
    - destruct (OTH pn Ho) as (_ & F1 & _ & _ & F4). destruct pn as [pa pk]. cbn [fst snd] in *.
      assert (H2 : In (pa, pk) (b1' ++ b2')) by (rewrite <- BLK2'; apply B12; exact F4).
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR3 BLK1' H2). lia.
    - unfold Q' in Ha. cbn [l_answer] in Ha. inversion Ha. cbn [fst]. lia. }
  assert (PZ : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
  assert (PAIR : forall pn, In pn (blocks L' A') ->
     (In pn (blocks L A) /\ ~ In pn O) \/ In pn (lay_blocks Q') \/ pn = (p2, l + 1)).
  { intros pn Hp. apply BCH in Hp. destruct Hp as [Hp | [ -> | -> ]].
    - destruct (in_dec PZ pn O) as [HpO|HpO]; [right; left | left; split; [exact (CSUB pn Hp) | exact HpO]].
      apply OQ. left. split; [exact HpO|].
      destruct (lay_facts _ _ _ _ _ _ _ _ HQ (proj1 (HO pn) HpO)) as (F0 & F1 & F2).
      destruct OLD2 as [(O0 & _ & _)|(ko & ONZ & EA & K1 & OO & E)]; [rewrite O0; exact F0|].
      intros Eq. destruct pn as [pa pk]. cbn [fst snd] in *. subst pa.
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR E Hp). lia.
    - right. left. apply OQ. right. reflexivity.
    - right. right. reflexivity. }
  assert (E7_2 : getr R7 2 = sp) by (rewrite (getr_of_eqv _ _ 2 X7 eq_refl); simp_regs; reflexivity).
  assert (E7_8 : getr R7 8 = reg_get regs 8) by (rewrite (getr_of_eqv _ _ 8 X7 eq_refl); simp_regs; reflexivity).
  assert (E7_9 : getr R7 9 = reg_get regs 9) by (rewrite (getr_of_eqv _ _ 9 X7 eq_refl); simp_regs; reflexivity).
  assert (E7_18 : getr R7 18 = reg_get regs 18) by (rewrite (getr_of_eqv _ _ 18 X7 eq_refl); simp_regs; reflexivity).
  assert (E7_19 : getr R7 19 = reg_get regs 19) by (rewrite (getr_of_eqv _ _ 19 X7 eq_refl); simp_regs; reflexivity).
  assert (E7_10 : getr R7 10 = Z_to_bv 64 p2) by (rewrite (getr_of_eqv _ _ 10 X7 eq_refl); simp_regs; reflexivity).
  assert (RP7 : regs_preserved regs R7).
  { assert (K76 : cs_keep R6 R7).
    { unfold cs_keep. apply (hb_cs_cases (fun r => getr R7 (Z_to_bv 5 r) = getr R6 (Z_to_bv 5 r))); cbv beta;
        match goal with |- getr _ (Z_to_bv 5 ?k) = _ => rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X7 eq_refl) end;
        reflexivity. }
    intros r Hr.
    destruct (Z.eq_dec r 2) as [->|N2]; [exact E7_2|].
    destruct (Z.eq_dec r 8) as [->|N8]; [exact E7_8|].
    destruct (Z.eq_dec r 9) as [->|N9]; [exact E7_9|].
    destruct (Z.eq_dec r 18) as [->|N18]; [exact E7_18|].
    destruct (Z.eq_dec r 19) as [->|N19]; [exact E7_19|].
    rewrite (K76 r Hr N2 N8 N9 N18 N19). exact (CK6 r Hr N2 N8 N9 N18 N19). }
  assert (LLE : layout_le A L L').
  { exact (hb_layout_trans A A2 L L2 L' (hb_layout_trans A A1 L L1 L2 HLE1 HLE2 REG1) HLE3 ltac:(lia)). }
  assert (GIMG : forall i, 0 <= i < 8 -> in_img B (0x22d40 + i)).
  { intros i Hi. apply (in_img_found B SEGS); [lia|].
    assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct C as [C | [C | [C | [C | [C | [C | [C | C]]]]]]]; subst i; intro F; vm_compute in F; discriminate F. }
  apply SR_ret.
  exists L', A', R7, m7, md3, p1, p2, old, (lay_blocks Q').
  split; [reflexivity|].
  split; [rewrite FA; exact OLDF|].
  split.
  { split; [exact MR7|]. split; [exact HWF3|]. split; [exact HBD3|]. split; [exact LLE|].
    split; [intros p n Hin _; exact (hb_ptr_le A L L' p n HWF Hin LLE)|].
    split; [exact RP7|].
    split; [destruct HVM1 as [vm1 ->]; destruct HVM2 as [vm2 ->]; destruct HVM3 as [vm3 ->]; exists vm3;
            rewrite !hb_vm_twice; reflexivity|].
    split.
    { intros a HA NO1 NO2 NS NE. cbn beta in NE.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct HA as [HA|HA]; [lia | pose proof (in_img_low B SEGS a HA); lia]).
      assert (NSP : ~ (bv_unsigned sp - 8256 <= a < bv_unsigned sp)).
      { intro H. apply NS. left. unfold spZ. change (getr regs 2) with sp. lia. }
      assert (NER : ~ (errno_addr B <= a < errno_addr B + 4)) by (intro H; apply NS; right; exact H).
      assert (NF : ~ (213944 <= a < 213952)) by (intro H; apply NE; left; rewrite FA; lia).
      assert (NQ1 : ~ (p1 <= a < p1 + (l + 1))) by (intro H; apply NE; right; right; left; lia).
      assert (NQ2 : ~ (p2 <= a < p2 + (l + 1))) by (intro H; apply NE; right; right; right; lia).
      assert (NO1' : ~ owned B L1 A1 a) by exact (hb_not_owned L A mem md L1 A1 m2 md1 a HMR HMR1 HA NO1).
      assert (NO2' : ~ owned B L2 A2 a) by exact (hb_not_owned L A mem md L2 A2 m4 md2 a HMR HMR2 HA NO1).
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as E01.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as W01.
      assert (H12 : mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                    (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
      { apply HFRAME1; [exact HA | exact NO1 | exact NO1' | | intros HE; apply NE; right; left; exact HE].
        unfold scratch. rewrite SP1. change ALLOC_STACK with 8192. intros [H|H]; [lia | exact (NER H)]. }
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU3 AR I) as E23.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU3 AR I) as W23.
      assert (H34 : mbyte (ms_segs B) m4 a = mbyte (ms_segs B) m3 a /\
                    (writable_at (ms_segs B) m3 a <-> writable_at (ms_segs B) m4 a)).
      { apply HFRAME2; [exact HA | exact NO1' | exact NO2' | | intros F; exact F].
        unfold scratch_k, XMALLOC_K. rewrite SP3. change ALLOC_STACK with 8192. intros [H|H]; [lia | exact (NER H)]. }
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU5 AR (OUT5 a AR NQ1 NF)) as E45.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU5 AR (OUT5 a AR NQ1 NF)) as W45.
      assert (H56 : mbyte (ms_segs B) m6 a = mbyte (ms_segs B) m5 a /\
                    (writable_at (ms_segs B) m5 a <-> writable_at (ms_segs B) m6 a)).
      { apply HFRAME3; [exact HA | exact NO2' | exact NO2 | | intros F; exact F].
        unfold scratch_k, XMALLOC_K. rewrite SP5. change ALLOC_STACK with 8192. intros [H|H]; [lia | exact (NER H)]. }
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU7 AR (OUT7 a AR NQ2)) as E67.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU7 AR (OUT7 a AR NQ2)) as W67.
      split; [rewrite E67, (proj1 H56), E45, (proj1 H34), E23, (proj1 H12), E01; reflexivity|].
      rewrite W01, (proj2 H12), W23, (proj2 H34), W45, (proj2 H56), W67. tauto. }
    split.
    { intros p n i Hin Hin' Hne Hi. cbn beta in Hne.
      assert (Hb : In (ptr_addr L p, n) (blocks L A))
        by (unfold blocks; exact (in_map (fun b0 => (ptr_addr L (fst b0), snd b0)) _ _ Hin)).
      rewrite SEGS. exact (BK _ _ _ Hb Hne Hi). }
    intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
    rewrite SEGS. apply WM7.
    destruct Ha as [Ha|Ha]; [|rewrite <- SEGS; apply HSCR3; unfold scratch_k; right; exact Ha].
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 48)) as [D|D].
    - rewrite <- SEGS. apply HSCR3. unfold scratch_k. left. unfold XMALLOC_K. rewrite SP5.
      change ALLOC_STACK with 8192. lia.
    - pose proof FR6 as [_ (_ & _ & WR6)]. cbn [cells_size csize Nat.add] in WR6.
      specialize (WR6 (a - (bv_unsigned sp - 48)) ltac:(lia)).
      replace (bv_unsigned sp - 48 + (a - (bv_unsigned sp - 48))) with a in WR6 by ring. exact WR6. }
  split; [exact E7_10|].
  split; [lia|].
  split; [exact AL1|]. split; [exact AL2|]. split; [exact FRESH1|]. split; [exact FRESH2|].
  split.
  { exists c1, c2. split; [|split; [exact BCH | split; [exact NP1 | exact NP2]]].
    destruct OLD2 as [(O0 & _ & E)|(ko & ONZ & _ & _ & OO & E)];
      [left; split; [exact O0 | exact E] | right; exists ko; split; [exact ONZ|]; split; [exact OO | exact E]]. }
  split; [intros a k i Hin Hne Hi; rewrite SEGS; exact (BK a k i Hin Hne Hi)|].
  split; [intros q k Hq HnO; apply UB3; apply UB2; exact (UB1 q k Hq HnO)|].
  split.
  { unfold g_rec_rep, rec_rep. exists Q'. split; [|intros pn; split; auto].
    cbn [fst hand_back].
    apply (rep_at_set_answer rsegs (blocks L A) (blocks L' A') mem m7 G_REC REC_SC R Q x p1 (l + 1) HQ).
    - intros a [(Ha & Hf)|Ha]; apply RECK.
      + apply hb_in_fG. unfold G_REC, REC_SIZE in Ha. lia.
      + unfold G_REC, OFF_ANSWER in Hf. lia.
      + apply hb_in_fG. unfold REC_SC, SC_SIZE in Ha. lia.
      + unfold REC_SC, SC_SIZE in Ha. lia.
    - intros a Ha. apply RECW. apply hb_in_fG. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha. lia.
    - intros pn Hp. destruct (OTH pn Hp) as (F0 & F1 & F2 & F3 & F4). split; [exact (B2F _ (B12 _ F4))|]. split.
      + destruct pn as [pa pk]. cbn [fst snd] in *. rewrite BLK2 in F4.
        pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR2 BLK1 F4). lia.
      + intros i Hi. destruct pn as [pa pk]. cbn [fst snd] in *. exact (BK pa pk i F2 F3 Hi).
    - rewrite FA. exact FLD7.
    - exact NZ1.
    - exact (B2F _ INB1).
    - split; [lia|]. try unfold LMAX. lia.
    - exact PB.
    - exact NONUL.
    - try unfold LMAX. lia.
    - exact (proj1 (APART p1 (l + 1) ltac:(lia) FR1_img)).
    - exact (proj2 (APART p1 (l + 1) ltac:(lia) FR1_img)). }
  split; [exact OQ|].
  split; [exact OP2|].
  split; [exact PAIR|].
  split; [exact PB|].
  split; [cbn [snd hand_back]; exact PB2|].
  split; [exact SRC7|].
  split; [exact RA7|].
  split.
  { unfold guard_kept in *. intros i Hi. rewrite GOTG in GK1, GK2, GK3 |- *.
    transitivity (mbyte (ms_segs B) m6 (0x22d40 + i)).
    { apply (munch_mbyte _ _ _ _ _ MU7); [lia|]. apply OUT7; [lia|]. intros Hp.
      apply (FR2_img (0x22d40 + i - p2)); [lia|]. replace (p2 + (0x22d40 + i - p2)) with (0x22d40 + i) by ring.
      exact (GIMG i Hi). }
    transitivity (mbyte (ms_segs B) m5 (0x22d40 + i)); [exact (GK3 i Hi)|].
    transitivity (mbyte (ms_segs B) m4 (0x22d40 + i)).
    { apply (munch_mbyte _ _ _ _ _ MU5); [lia|]. apply OUT5; [lia | | lia]. intros Hp.
      apply (FR1_img (0x22d40 + i - p1)); [lia|]. replace (p1 + (0x22d40 + i - p1)) with (0x22d40 + i) by ring.
      exact (GIMG i Hi). }
    transitivity (mbyte (ms_segs B) m3 (0x22d40 + i)); [exact (GK2 i Hi)|].
    transitivity (mbyte (ms_segs B) m2 (0x22d40 + i)); [apply (munch_mbyte _ _ _ _ _ MU3); [lia | exact I]|].
    transitivity (mbyte (ms_segs B) m1 (0x22d40 + i)); [exact (GK1 i Hi)|].
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [exact INIT3|].
  split; [lia|].
  assert (EB1 : sb_malloc (sb_shift b A A1) (l + 1) = sb_shift b A A2)
    by (rewrite (sb_shift_add (sb_shift b A A1) L1 A1 L2 A2 b1 b2 p1 (l + 1) BLK1 BLK2); apply sb_shift_trans).
  assert (EB2 : sb_malloc (sb_shift b A A2) (l + 1) = sb_shift b A A')
    by (rewrite (sb_shift_add (sb_shift b A A2) L2 A2 L' A' b1' b2' p2 (l + 1) BLK1' BLK2'); apply sb_shift_trans).
  split; [rewrite <- EB2, <- EB1; apply sb_malloc_mono; apply sb_malloc_mono; exact SLE|].
  rewrite <- EB2, <- EB1. exact RES3.
Qed.

End X.
