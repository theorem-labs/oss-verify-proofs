(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths, module names, addresses and numbers changed; 1075 of its 1197 lines of code are new or changed and 2620 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import memcpy_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition ss_mid1 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a1 a2 : word) (v r : Z) (rs : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 b1 b2 b3 b4 b5 b6 b7 t3 t4 t5 t6 m' w,
    ms' = MS (mkR (Z_to_bv 64 0x173b8) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 a2 a1 (Z_to_bv 64 r)
                  b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 0x33ff0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x18ad0) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x343c0, 0x343c4)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 32)%Z [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells rsegs m' 0x343c0 [C4 w]
    /\ rw_cells rsegs m' 0x343c8 [C8 (Z_to_bv 64 r); C8 rs]
    /\ le4 w = le4 (Z_to_bv 64 (v + 1)).

Lemma sx32_small : forall v, (0 <= v < 2 ^ 31)%Z -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v H. unfold sx32. rewrite unsigned_lit by lia. f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma ss_addiw : forall z, (0 <= z < 2 ^ 31 - 1)%Z ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 1)%Z) = Z_to_bv 64 (z + 1)%Z.
Proof.
  intros z Hz. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648%Z. change (bv_modulus 32) with 4294967296%Z.
  change (2 ^ 31)%Z with 2147483648%Z in Hz.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma ss_lts : forall x y, (-2^63 <= x < 2^63)%Z -> (-2^63 <= y < 2^63)%Z ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !Z_to_bv_signed.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with 9223372036854775808%Z.
  change (bv_modulus 64) with 18446744073709551616%Z.
  change (2^63)%Z with 9223372036854775808%Z in Hx, Hy.
  rewrite !Z.mod_small by lia.
  all: f_equal; lia.
Qed.

Lemma ss_run1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v r : Z) (rs : word),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z -> (0x343e0 <= lo)%Z ->
  rw_cells rsegs m 0x343c0 [C4 (Z_to_bv 64 v)] -> (0 <= v < 2 ^ 31 - 1)%Z ->
  rw_cells rsegs m 0x343c8 [C8 (Z_to_bv 64 r); C8 rs] -> (0 <= r < 2 ^ 64)%Z ->
  evt rsegs (ss_mid1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a1 a2 v r rs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1737c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v r rs ST LO LO2 NR Hv RP Hr.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x343c0, 0x343c4)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 9 step. rewrite sx32_small by lia.
  step. rewrite ss_addiw by lia.
  step. rewrite ss_lts by lia. if_false.
  do 4 step.
  apply evt_done. unfold ss_mid1.
  do 16 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|].
  first [reflexivity | rewrite ?sx32_small, ?unsigned_lit by lia; reflexivity].
Qed.

Lemma signed_lit64 : forall z, (- 2 ^ 63 <= z < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z H. unfold bv_signed. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63)%Z. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ss_run2n :
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 : word) (size : Z) (r rs : word),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s02; C8 s01; C8 s00; C8 ra0] ->
  rw_cells rsegs m 0x343c8 [C8 r; C8 rs] ->
  (0x343e0 + 32 <= bv_unsigned sp0)%Z -> (- 2 ^ 31 <= size <= 0)%Z ->
  evt rsegs (fun ms' => exists t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s00 s01 (Z_to_bv 64 size) b1 b2 b3 b4 b5 b6 b7
                     s02 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra0) fc None m' (seg_rom rsegs)
       /\ munch [(0x343c8, 0x343d8)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x343c8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 (Z_to_bv 64 size) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x33ff0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x173b8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 size r rs FR RP SPR Hs.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(0x343c8, 0x343d8)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (SS : bv_signed (Z_to_bv 64 size) = size) by (apply signed_lit64; lia).
  do 3 step. if_true. do 7 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done.
  do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma ss_run2p :
  forall ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 : word) (size : Z) (r rs : word),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s02; C8 s01; C8 s00; C8 ra0] ->
  rw_cells rsegs m 0x343c8 [C8 r; C8 rs] ->
  (0x343e0 + 32 <= bv_unsigned sp0)%Z -> (0 < size < 2 ^ 31)%Z ->
  evt rsegs (fun ms' => exists t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR (Z_to_bv 64 0x173cc) (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0' t1' t2' (Z_to_bv 64 size) s1
                     (Z_to_bv 64 size) b1 b2 b3 b4 b5 b6 b7
                     (Z_to_bv 64 0x33ff0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x15a88) fc None m' (seg_rom rsegs)
       /\ munch [(0x343c8, 0x343d8)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp0 - 32) [C8 s02; C8 s01; C8 s00; C8 ra0]
       /\ rw_cells rsegs m' 0x343c8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 (Z_to_bv 64 size) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x33ff0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x173b8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 size r rs FR RP SPR Hs.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(0x343c8, 0x343d8)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (SS : bv_signed (Z_to_bv 64 size) = size) by (apply signed_lit64; lia).
  do 3 step. if_false. do 2 step.
  apply evt_done.
  do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma ss_run3 : memcpy_contract ->
  forall ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 : word) (size buf p : Z)
    (x junk : list byte) (r rs : word),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [C8 s02; C8 s01; C8 s00; C8 ra0] ->
  rw_cells rsegs m 0x343c8 [C8 r; C8 rs] ->
  (0x343e0 + 32 <= bv_unsigned sp0)%Z -> (0 < size < 2 ^ 31)%Z -> Z.of_nat (length x) = size ->
  bytes_at rsegs m buf x -> rw_cells rsegs m p [CB (length x) junk] ->
  (buf + size <= p \/ p + size <= buf)%Z -> (0 < p)%Z ->
  (p + size <= bv_unsigned sp0 - 32 \/ bv_unsigned sp0 <= p)%Z ->
  (p + size <= 0x343c8 \/ 0x343d8 <= p)%Z -> (buf + size <= 0x343c8 \/ 0x343d8 <= buf)%Z ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s00 s01 (Z_to_bv 64 size) b1 b2 b3 b4 b5 b6 b7
                     s02 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra0) fc None m' (seg_rom rsegs)
       /\ munch [(0x343c8, 0x343d8); (p, p + size)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
       /\ rw_cells rsegs m' 0x343c8 [C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 size)]
       /\ rw_cells rsegs m' p [CB (length x) x]
       /\ bytes_at rsegs m' buf x)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 (Z_to_bv 64 size) (Z_to_bv 64 buf)
             (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x33ff0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x173cc) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 size buf p x junk r rs FR RP SPR Hs LX BX DX SEP P0 PS PG BG MI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ BX) as SB.
  pose proof (rw_cells_bound _ _ _ _ DX) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (munch_refl [(0x343c8, 0x343d8); (p, p + size)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UB : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
  assert (UP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (Z_to_bv 64 size) = size) by (apply unsigned_lit; lia).
  do 4 step.
  call (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x junk).
  1-5: rewrite ?UB, ?UP, ?US; first [eassumption | rewrite <- LX, Nat2Z.id; first [reflexivity | eassumption] | lia].
  do 8 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done.
  rewrite UP, US, <- LX, Nat2Z.id in PC. rewrite UB in POST.
  do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. eassumption.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB RecSeq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecStep RecGlue RecTail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import xmalloc_c socket_send_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require RecAnsB.
Local Open Scope Z_scope.

Lemma rw_cells_mk : forall segs m a cs, cells_wf cs -> bytes_at segs m a (cells_bytes cs) ->
  wr_at segs m a (Z.of_nat (cells_size cs)) -> rw_cells segs m a cs.
Proof. intros segs m a cs H1 H2 H3. split; [split|]; assumption. Qed.

Lemma wr_at_sub : forall segs m a n d k, wr_at segs m a n -> 0 <= d -> 0 <= k -> d + k <= n -> wr_at segs m (a + d) k.
Proof.
  intros segs m a n d k (H1 & H2 & H3) Hd Hk Hn. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + d + i) with (a + (d + i)) by ring. apply H3. lia.
Qed.

Lemma ro_agree_munch : forall segs m m' W, ro_agree segs m -> munch W m m' ->
  (forall x : word, ro_addr segs x = true -> outside W (bv_unsigned x)) -> ro_agree segs m'.
Proof. intros segs m m' W H MU HO a Ha. unfold mrd. rewrite (MU a (HO a Ha)). exact (H a Ha). Qed.

Lemma grec_ro : forallb (fun i => negb (ro_addr rsegs (Z_to_bv 64 (0x33ff0 + Z.of_nat i)))) (seq 0 1020) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma grec_ro_false : forall a, 0x33ff0 <= a < 0x33ff0 + 1020 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. pose proof (proj1 (forallb_forall _ _) grec_ro (Z.to_nat (a - 0x33ff0)) ltac:(apply in_seq; lia)) as H.
  cbv beta in H. rewrite Z2Nat.id in H by lia. replace (0x33ff0 + (a - 0x33ff0)) with a in H by ring.
  apply negb_true_iff in H. exact H.
Qed.

Lemma got_found : forallb (fun i => match find_segment rsegs (0x22d40 + Z.of_nat i) 1 with Some _ => true | None => false end)
  (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma in_fg : forall a, 0x33ff0 <= a < 0x33ff0 + 1020 -> in_globals frame_G a.
Proof. intros a Ha. exists 0x33ff0, 1020. split; [left; reflexivity | exact Ha]. Qed.

Lemma nodup_fst_eq : forall {X : Type} (l : list (X * Z)) p n n', List.NoDup (map fst l) -> In (p, n) l -> In (p, n') l -> n = n'.
Proof.
  intros X l. induction l as [|[q k] l IH]; intros p n n' ND H1 H2; cbn in *; [contradiction|].
  apply List.NoDup_cons_iff in ND as [NI ND'].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - inversion E1; inversion E2; subst; reflexivity.
  - inversion E1; subst. exfalso. apply NI. apply in_map_iff. exists (p, n'). split; [reflexivity | exact H2].
  - inversion E2; subst. exfalso. apply NI. apply in_map_iff. exists (p, n). split; [reflexivity | exact H1].
  - exact (IH p n n' ND' H1 H2).
Qed.

Definition kept_rest (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma kept_rest_trans : forall R1 R2 R3, kept_rest R1 R2 -> kept_rest R2 R3 -> kept_rest R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr N2 N8 N9 N18. rewrite (H2 r Hr N2 N8 N9 N18). exact (H1 r Hr N2 N8 N9 N18). Qed.

Lemma kept_rest_of_pres : forall R R', regs_preserved R R' -> kept_rest R R'.
Proof. intros R R' H r Hr _ _ _ _. exact (H r Hr). Qed.

Ltac kept_rest_tac X :=
  intros rr Hrr Nrr2 Nrr8 Nrr9 Nrr18; unfold callee_saved in Hrr;
  assert (CC : rr = 3 \/ rr = 4 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27)
    by lia;
  clear Hrr Nrr2 Nrr8 Nrr9 Nrr18;
  repeat (destruct CC as [CC|CC]; [subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
    simp_regs; first [reflexivity | unfold getr; reflexivity]|]);
  subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
  simp_regs; first [reflexivity | unfold getr; reflexivity].

Definition nonrep (Q : rlay) : list (Z * Z) := concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q).

Lemma lay_nonrep : forall Q, lay_blocks Q = nonrep Q ++ oblk (l_reply Q).
Proof. intros Q. unfold lay_blocks, nonrep. rewrite <- !app_assoc. reflexivity. Qed.

Lemma lay_setrep : forall Q qn, lay_blocks (RLay (l_calls Q) (l_spill Q) (l_answer Q) qn) = nonrep Q ++ oblk qn.
Proof. intros Q qn. unfold lay_blocks, nonrep. cbn [l_calls l_spill l_answer l_reply]. rewrite <- !app_assoc. reflexivity. Qed.

Lemma rw_cells_munch : forall W m m' a cs, rw_cells rsegs m a cs -> munch W m m' ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> 0 <= a + i < 2 ^ 64 /\ outside W (a + i)) ->
  rw_cells rsegs m' a cs.
Proof.
  intros W m m' a cs H MU K. apply (rw_cells_transfer rsegs m); [exact H|]. intros i Hi. destruct (K i Hi) as [Ra Oa].
  split; [exact (munch_mbyte _ _ _ _ _ MU Ra Oa) | exact (proj1 (munch_writable _ _ _ _ _ MU Ra Oa))].
Qed.

Lemma c8_bytes2 : forall m a v1 v2, rw_cells rsegs m a [C8 v1; C8 v2] ->
  bytes_at rsegs m a (le8 v1) /\ bytes_at rsegs m (a + 8) (le8 v2).
Proof.
  intros m a v1 v2 [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  apply bytes_at_app in Hb as [H1 H2]. rewrite length_le8 in H2. split; [exact H1 | exact H2].
Qed.

Lemma c4_bytes : forall m a v, rw_cells rsegs m a [C4 v] -> bytes_at rsegs m a (le4 v).
Proof. intros m a v [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma cb_bytes : forall m a (n : nat) bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof. intros m a n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma nra_sep : forall s n lo hi, (forall a, s <= a < s + n -> ~ rec_area a) -> G_REC <= lo ->
  hi <= G_REC + REC_SIZE -> lo < hi -> 0 < n -> s + n <= lo \/ hi <= s.
Proof.
  intros s n lo hi H H1 H2 H3 H4. destruct (Z_le_gt_dec (s + n) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi s) as [D'|D']; [right; exact D'|]. exfalso.
  apply (H (Z.max s lo)); [lia|]. unfold rec_area. right. lia.
Qed.

Lemma rep_at_set_reply : forall segs bl bl' m m' gr sc R Q y qn,
  rep_at segs bl m gr sc R Q ->
  (forall a, gr <= a < gr + 920 \/ gr + 924 <= a < gr + 928 \/ gr + 944 <= a < gr + 960 \/ sc <= a < sc + 56 ->
     mbyte segs m' a = mbyte segs m a) ->
  (forall a, gr <= a < gr + REC_SIZE \/ sc <= a < sc + SC_SIZE -> writable_at segs m a -> writable_at segs m' a) ->
  (forall pn, In pn (nonrep Q) -> In pn bl' /\
     forall i, 0 <= i < snd pn -> mbyte segs m' (fst pn + i) = mbyte segs m (fst pn + i)) ->
  (forall pn p1, In pn (nonrep Q) -> In p1 (oblk qn) -> fst pn <> fst p1) ->
  bytes_at segs m' (gr + OFF_NREPLIES) (le4 (Z_to_bv 64 (r_nreplies R + 1))) -> r_nreplies R + 1 < 2 ^ 31 ->
  reply_at segs bl' m' gr y qn ->
  (forall p1, In p1 (oblk qn) -> iv_apart (fst p1) (snd p1) gr REC_SIZE /\ iv_apart (fst p1) (snd p1) sc SC_SIZE) ->
  rep_at segs bl' m' gr sc (set_reply R (r_nreplies R + 1) y) (RLay (l_calls Q) (l_spill Q) (l_answer Q) qn).
Proof.
  intros segs bl bl' m m' gr sc R Q y qn HR KG KW KQ DQ NB NL RP AP.
  destruct HR as (HS & HC & HA & HP & HX & HW).
  unfold rep_at. split; [| split; [| split; [| split; [| split]]]].
  - exact (g1_storage_keep segs m m' gr sc HS KW).
  - destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
    unfold g1_calls. cbn [r_calls r_spill set_reply l_calls l_spill].
    refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (bytes_at_keep_in segs m m' gr (gr + 920));
        [exact C3 | unfold OFF_NCALLS; lia | rewrite length_le4; unfold OFF_NCALLS; lia |].
      intros z Hz. apply KG. lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hil : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (call_at_keep segs bl bl' m m'); [exact Hc | |].
      * intros z Hz. apply KG. unfold OFF_CALLS, CALL_SIZE in *. lia.
      * intros pn Hpn. apply KQ. unfold nonrep. apply in_or_app. left. apply in_concat.
        exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
    + apply (call_at_keep segs bl bl' m m'); [exact C5 | |].
      * intros z Hz. apply KG. unfold CALL_SIZE in Hz. lia.
      * intros pn Hpn. apply KQ. unfold nonrep. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - unfold answer_at in *. cbn [r_answer set_reply l_answer].
    revert HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [[p k]|] eqn:EA; intros HA; try contradiction.
    + destruct HA as (N1 & N2 & N3 & N4 & N5 & N6 & N7). cbn [fst snd] in *.
      assert (Hq : In (p, k) (nonrep Q)).
      { unfold nonrep. rewrite EA. cbn [oblk]. rewrite !in_app_iff. right. right. left. reflexivity. }
      destruct (KQ _ Hq) as [Kin Kp]. cbn [fst snd] in Kp.
      split; [apply (bytes_at_keep_in segs m m' (gr + 912) (gr + 920));
              [exact N1 | unfold OFF_ANSWER; lia | rewrite length_le8; unfold OFF_ANSWER; lia | intros z Hz; apply KG; lia]|].
      split; [exact N2|]. split; [exact Kin|]. split; [exact N4|]. split; [|split; [exact N6 | exact N7]].
      apply (bytes_at_keep segs m); [exact N5|]. intros i Hi. apply Kp. rewrite length_app in Hi. cbn [length] in Hi. lia.
    + apply (bytes_at_keep_in segs m m' (gr + 912) (gr + 920));
        [exact HA | unfold OFF_ANSWER; lia | rewrite length_le8; unfold OFF_ANSWER; lia | intros z Hz; apply KG; lia].
  - cbn [r_reply set_reply l_reply]. exact RP.
  - unfold g1_scalars in *. cbn [r_refuse r_code r_nreplies r_state r_host set_reply].
    destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
    split; [apply (bytes_at_keep_in segs m m' gr (gr + 920));
            [exact X1 | unfold OFF_REFUSE; lia | rewrite length_le4; unfold OFF_REFUSE; lia | intros z Hz; apply KG; lia]|].
    split; [apply (bytes_at_keep_in segs m m' gr (gr + 920));
            [exact X2 | unfold OFF_CODE; lia | rewrite length_le4; unfold OFF_CODE; lia | intros z Hz; apply KG; lia]|].
    split; [exact NB|].
    split; [apply (bytes_at_keep_in segs m m' (gr + 944) (gr + 960));
            [exact X4 | unfold OFF_STATE; lia | rewrite length_le8; unfold OFF_STATE; lia | intros z Hz; apply KG; lia]|].
    split; [apply (bytes_at_keep_in segs m m' (gr + 944) (gr + 960));
            [exact X5 | unfold OFF_HOST; lia | rewrite length_le8; unfold OFF_HOST; lia | intros z Hz; apply KG; lia]|].
    split; [exact X6|]. split; [exact X7|]. split; [lia|]. split; [exact X9 | exact X10].
  - destruct HW as [ND AP0]. unfold g1_own. rewrite lay_setrep. rewrite lay_nonrep in ND, AP0.
    assert (NDn : base.NoDup (map fst (nonrep Q))).
    { apply NoDup_ListNoDup in ND. apply NoDup_ListNoDup. rewrite map_app in ND. exact (List.NoDup_app_remove_r _ _ ND). }
    split.
    + destruct qn as [[p1 k1]|]; cbn [oblk].
      * apply nodup_fst_snoc; [exact NDn|]. intros Hin. apply in_map_iff in Hin as (pn & E & Hpn).
        exact (DQ pn (p1, k1) Hpn (or_introl eq_refl) E).
      * rewrite app_nil_r. exact NDn.
    + intros pn Hpn. apply in_app_or in Hpn as [H|H]; [apply AP0; apply in_or_app; left; exact H | exact (AP pn H)].
Qed.

Lemma match_nonempty : forall (l : list byte), (0 < length l)%nat ->
  match l with [] => None | _ :: _ => Some l end = Some l.
Proof. intros [|c l] H; [cbn in H; lia | reflexivity]. Qed.

Ltac pres_reg_tac X :=
  match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
  simp_regs; first [reflexivity | unfold getr; reflexivity].

Lemma preserved_parts : forall (regs R : bvmap 5 word),
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> getr R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  getr R (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2) -> getr R (Z_to_bv 5 8) = getr regs (Z_to_bv 5 8) ->
  getr R (Z_to_bv 5 9) = getr regs (Z_to_bv 5 9) -> getr R (Z_to_bv 5 18) = getr regs (Z_to_bv 5 18) ->
  regs_preserved regs R.
Proof.
  intros regs R KR E2 E8 E9 E18 r Hr.
  destruct (Z.eq_dec r 2) as [->|N2]; [exact E2|].
  destruct (Z.eq_dec r 8) as [->|N8]; [exact E8|].
  destruct (Z.eq_dec r 9) as [->|N9]; [exact E9|].
  destruct (Z.eq_dec r 18) as [->|N18]; [exact E18|].
  exact (KR r Hr N2 N8 N9 N18).
Qed.

Section Run.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GRD : ms_guard B = 0x54730.
Hypothesis FGI : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis FGO : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTXO : ctx_owned B API.
Hypothesis XM : xmalloc_contract B API.
Hypothesis FREE : free_contract B API.
Hypothesis FREE_NULL : free_null_contract B.
Hypothesis MEMCPY : memcpy_contract.

Lemma blk_out : forall L A m md p n i W, aa_MR API L A m md -> In (p, n) (user_blocks A) -> 0 <= i < n ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> alloc_ceiling <= a \/ in_img B a) ->
  outside W (ptr_addr L p + i) /\ 0 <= ptr_addr L p + i < 2 ^ 64.
Proof using AX.
  intros L A m md p n i W HM Hp Hi HW. pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  destruct (mr_blocks B _ LAWS L A m md p n i HM Hp Hi) as (_ & H4 & H5 & _).
  pose proof (ax_blocks_img AX L A m md p n i HM Hp Hi) as NI.
  split; [|lia]. destruct (outside_dec W (ptr_addr L p + i)) as [H|H]; [exact H|].
  destruct (HW (ptr_addr L p + i) ltac:(lia) H) as [Hc|Hc]; [lia | exact (False_ind _ (NI Hc))].
Qed.

Lemma grec_img : forall a, 0x33ff0 <= a < 0x33ff0 + 1020 -> in_img B a.
Proof using FGI. intros a Ha. exact (proj1 (FGI a (in_fg a Ha))). Qed.

Lemma grec_free : forall a, 0x33ff0 <= a < 0x33ff0 + 1020 -> free_a B a.
Proof using FGI.
  intros a Ha. destruct (FGI a (in_fg a Ha)) as (H1 & H2 & H3 & _). right. auto.
Qed.

Lemma got_img : forall i, 0 <= i < 8 -> in_img B (0x22d40 + i).
Proof using SEGS.
  intros i Hi. apply (in_img_found B SEGS); [lia|].
  pose proof (proj1 (forallb_forall _ _) got_found (Z.to_nat i) ltac:(apply in_seq; lia)) as H.
  cbv beta in H. rewrite Z2Nat.id in H by lia.
  intros F. rewrite F in H. discriminate.
Qed.

Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (buf size : Z) (x : list byte) (R : rstate) (O : list (Z * Z)) (b : sbound) (Q : rlay) (r0 : Z) (rsw : word).
Hypothesis PRE : call_pre_k B (aa_MR API) SOCKET_SEND_K L A regs mem md.
Hypothesis A11 : getr regs 11 = Z_to_bv 64 buf.
Hypothesis A12 : getr regs 12 = Z_to_bv 64 size.
Hypothesis HSZ : -2 ^ 31 <= size < 2 ^ 31.
Hypothesis HREP : rep_at rsegs (blocks L A) mem G_REC REC_SC R Q.
Hypothesis HO : forall pn, In pn O <-> In pn (lay_blocks Q).
Hypothesis NRP : r_nreplies R < 2 ^ 31 - 1.
Hypothesis SZP : 0 < size ->
  size <= LMAX + 2 /\ Z.of_nat (length x) = size /\ Mem.bytes_at rsegs mem buf x /\
  (buf + size <= spZ regs - SOCKET_SEND_K \/ spZ regs <= buf) /\
  buf_home B L A O (spZ regs) buf size /\
  (forall a, buf <= a < buf + size -> ~ rec_area a) /\
  room_slots (sb_malloc b size) size.
Hypothesis SZN : size <= 0 -> x = [].
Hypothesis RA : ro_agree rsegs mem.
Hypothesis F18 : f18_words rsegs mem.
Hypothesis RES : res_ok_slots A b.
Hypothesis RPB : Mem.bytes_at rsegs mem (G_REC + OFF_REPLY) (Mem.le8 (Z_to_bv 64 r0)).
Hypothesis RSB : Mem.bytes_at rsegs mem (G_REC + OFF_REPLY_SIZE) (Mem.le8 rsw).
Hypothesis R0R : 0 <= r0 < 2 ^ 64.
Hypothesis RPQ : match l_reply Q with None => r0 = 0 | Some pn => fst pn = r0 /\ In pn (blocks L A) /\ 1 <= snd pn end.

Definition gone_r (pn : Z * Z) : Prop := In pn (oblk (l_reply Q)).

Definition P1 (c : config) : Prop :=
  exists L1 A1 R2 m2 md2 bl1 bl2 b1 w,
    c = mkCfg (mkst R2 (Z_to_bv 64 0x173b8) m2 (seg_rom rsegs)) md2 /\
    rjr B (aa_MR API) 8240 (spZ regs) socket_send_writes gone_r L A mem md L1 A1 m2 md2 /\
    getr R2 2 = Z_to_bv 64 (spZ regs - 32) /\ getr R2 8 = Z_to_bv 64 size /\ getr R2 9 = Z_to_bv 64 buf /\
    getr R2 18 = Z_to_bv 64 0x33ff0 /\ kept_rest regs R2 /\
    rw_cells rsegs m2 (spZ regs - 32) [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)] /\
    rw_cells rsegs m2 0x343c0 [C4 w] /\ le4 w = le4 (Z_to_bv 64 (r_nreplies R + 1)) /\
    rw_cells rsegs m2 0x343c8 [C8 (Z_to_bv 64 r0); C8 rsw] /\
    blocks L1 A1 = bl1 ++ bl2 /\
    match l_reply Q with None => blocks L A = bl1 ++ bl2 | Some pn => blocks L A = bl1 ++ pn :: bl2 end /\
    ro_agree rsegs m2 /\
    (forall i, 0 <= i < 8 -> mbyte rsegs m2 (0x22d40 + i) = mbyte rsegs mem (0x22d40 + i)) /\
    (st_init_done A = true -> st_init_done A1 = true) /\
    res_ok_slots A1 b1 /\ sb_le b1 b /\ b1 = sb_shift b A A1.

Lemma ss_stage1 : SR rsegs (mkCfg (mkst regs (Z_to_bv 64 SOCKET_SEND) mem (seg_rom rsegs)) md) P1.
Proof using SEGS FREE_PC ERRNO_LOW GOTG FGI FGO AX FREE FREE_NULL PRE A11 A12 HSZ HREP NRP RA RES RPB RSB R0R RPQ x.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SOCKET_SEND_K, XMALLOC_K in HCEIL, HWS. change ALLOC_STACK with 8192 in HCEIL, HWS.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  rewrite SEGS in HWS, HERR.
  pose proof HREP as (HS & HC & HA & HP & HX & HW).
  destruct HS as (S1 & S2 & S3 & S4 & S5).
  destruct HX as (GX1 & GX2 & GX3 & GX4 & GX5 & GX6 & GX7 & GX8 & GX9 & GX10).
  assert (ST : stk rsegs mem (bv_unsigned sp - 8240) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  assert (NR : rw_cells rsegs mem 0x343c0 [C4 (Z_to_bv 64 (r_nreplies R))]).
  { apply rw_cells_mk; [cbn; tauto | |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact GX3.
    - exact (wr_at_sub _ _ _ _ 920 4 S4 ltac:(lia) ltac:(lia) ltac:(unfold REC_SIZE; lia)). }
  assert (RP : rw_cells rsegs mem 0x343c8 [C8 (Z_to_bv 64 r0); C8 rsw]).
  { apply rw_cells_mk; [cbn; tauto | |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact RPB|].
      rewrite length_le8. exact RSB.
    - exact (wr_at_sub _ _ _ _ 928 16 S4 ltac:(lia) ltac:(lia) ltac:(unfold REC_SIZE; lia)). }
  pose proof (rjr_init B (aa_MR API) 8240 socket_send_writes gone_r L A regs mem md PRE0 ltac:(lia)) as RJ0.
  change (spZ regs) with (bv_unsigned sp) in RJ0.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold SOCKET_SEND.
    eapply ss_run1 with (lo := bv_unsigned sp - 8240) (v := r_nreplies R) (r := r0) (rs := rsw);
      [exact ST | lia | lia | exact NR | lia | exact RP | exact R0R]. }
  intros ms1 (can1 & Q1 & EQ1). unfold ss_mid1 in Q1.
  destruct Q1 as (t0' & t1' & t2' & b1' & b2' & b3' & b4' & b5' & b6' & b7' & t3' & t4' & t5' & t6' & m1 & w
    & -> & MU1 & WM1 & FR1 & NR1 & RP1 & W4).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x173b8) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 size) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; exact A12).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 buf) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; exact A11).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 r0) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_18 : getr R1 18 = Z_to_bv 64 0x33ff0) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
  assert (KR1 : kept_rest regs R1) by kept_rest_tac X1.
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (W1C : forall a, 0 <= a < 2 ^ 64 -> ~ outside [(bv_unsigned sp - 32, bv_unsigned sp); (0x343c0, 0x343c4)] a ->
            (bv_unsigned sp - 32 <= a < bv_unsigned sp) \/ (0x343c0 <= a < 0x343c4)) by (intros a _ H; cbn in H; lia).
  assert (RJ1 : rjr B (aa_MR API) 8240 (bv_unsigned sp) socket_send_writes gone_r L A mem md L A m1 md).
  { apply (rjr_munch B (aa_MR API) SEGS LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RJ0 MU1 ltac:(rewrite SEGS; exact WM1)).
    - intros a Ra Hn Hf. destruct (W1C a Ra Hn) as [H|H]; [left; lia|].
      right. unfold socket_send_writes, G_REC, OFF_NREPLIES, OFF_REPLY. lia.
    - intros a Ra Hn. destruct (W1C a Ra Hn) as [H|H].
      + intros Ho. destruct (mr_owned_low B _ LAWS L A mem md a HMR Ho). lia.
      + apply (FGO L A mem md a HMR). apply in_fg. lia.
    - intros a Ha. cbn. lia.
    - intros p n i Hp _ Hi. refine (proj1 (blk_out L A mem md p n i _ HMR Hp Hi _)).
      intros a Ra Hn. destruct (W1C a Ra Hn) as [H|H]; [left; lia | right; apply grec_img; lia].
    - intros p n i Hp Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hp Hi) as (Hpr & _).
      destruct (blk_out L A mem md p n i [(bv_unsigned sp - 32, bv_unsigned sp); (0x343c0, 0x343c4)] HMR Hp Hi) as [Ho Hr].
      { intros a Ra Hn. destruct (W1C a Ra Hn) as [H|H]; [left; lia | right; apply grec_img; lia]. }
      exact (munch_present _ _ _ _ MU1 Hr Ho Hpr). }
  assert (RA1 : ro_agree rsegs m1).
  { apply (ro_agree_munch rsegs mem m1 _ RA MU1). intros y Hy. pose proof (bv_unsigned_in_range 64 y) as Ry.
    unfold bv_modulus in Ry. destruct (outside_dec [(bv_unsigned sp - 32, bv_unsigned sp); (0x343c0, 0x343c4)] (bv_unsigned y))
      as [H|H]; [exact H|]. exfalso.
    destruct (W1C _ Ry H) as [H1|H1].
    - rewrite <- (Z_to_bv_bv_unsigned y), ro_addr_hi in Hy by lia. discriminate.
    - rewrite <- (Z_to_bv_bv_unsigned y), grec_ro_false in Hy by lia. discriminate. }
  assert (GOT1 : forall i, 0 <= i < 8 -> mbyte rsegs m1 (0x22d40 + i) = mbyte rsegs mem (0x22d40 + i)).
  { intros i Hi. apply (munch_mbyte _ _ _ _ _ MU1); [lia|]. cbn. lia. }
  assert (RET1 : YK0s.ret_ok (getr R1 1)) by (rewrite E1_1; apply bv_eq; vm_compute; reflexivity).
  assert (CP1 : call_pre B (aa_MR API) L A R1 m1 md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A R1 m1 md)).
    apply (call_pre_k_of_rjr B (aa_MR API) 8240 (bv_unsigned sp) socket_send_writes gone_r L A mem md L A m1 md
             ALLOC_STACK R1 RJ1 RET1); change ALLOC_STACK with 8192; rewrite ?SP1; [|lia|lia|lia|rewrite E1_4; exact HTP].
    replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring. rewrite Z.mod_add by lia. exact HAL. }
  destruct (l_reply Q) as [[r k0]|] eqn:EQR.
  - destruct RPQ as (Er & Hin & Hk0). cbn [fst snd] in Er, Hk0. subst r.
    destruct (proj1 (YI04.blocks_In L A r0 k0) Hin) as (p0 & EP0 & Hp0).
    assert (INIT0 : st_init_done A = true) by exact (YI04.init_done_of_block A (p0, k0) HWF Hp0).
    pose proof FREE as FR. unfold free_contract in FR. rewrite SEGS, FREE_PC in FR.
    eapply SR_bind.
    { apply (FR L A R1 m1 md p0 k0 b); [exact CP1 | exact RA1 | exact Hp0 | rewrite EP0; exact E1_10 | exact RES]. }
    intros c2 (L1 & A1 & R2 & m2 & md2 & -> & POST & BLK & KEPT & RA2 & GK2 & UB2 & INIT2 & REG2 & RES2).
    destruct BLK as (bl1 & bl2 & BL1 & BL2).
    pose proof POST as POSTk. apply (proj1 (call_post_k_alloc B (aa_MR API) _ _ _ _ _ _ _ _ _ _ _)) in POSTk.
    pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
    rewrite SEGS in PF.
    assert (RJ2 : rjr B (aa_MR API) 8240 (bv_unsigned sp) socket_send_writes gone_r L A mem md L1 A1 m2 md2).
    { eapply (rjr_post B (aa_MR API) SEGS LAWS AX ERRNO_LOW);
        [exact RJ1 | apply call_post_k_rec; exact POSTk | | | | | | |].
      - rewrite SP1. change ALLOC_STACK with 8192. lia.
      - rewrite SP1. lia.
      - intros a Ha Hf. exfalso. cbv beta in Ha.
        destruct (mr_blocks B _ LAWS L A mem md p0 k0 (a - ptr_addr L p0) HMR Hp0 ltac:(lia)) as (_ & H4 & H5 & _).
        pose proof (ax_blocks_img AX L A mem md p0 k0 (a - ptr_addr L p0) HMR Hp0 ltac:(lia)) as NI.
        replace (ptr_addr L p0 + (a - ptr_addr L p0)) with a in NI by ring.
        destruct Hf as [Hf | (Hf & _)]; [lia | exact (NI Hf)].
      - intros p n _ _ _ [].
      - intros p n Hp _ Hn. unfold gone_r. rewrite EQR. cbn [oblk In]. left.
        destruct (YI04.sptr_eq_dec p p0) as [->|Ne]; [|exfalso; exact (Hn (UB2 p n Hp Ne))].
        rewrite EP0. f_equal.
        exact (nodup_fst_eq (user_blocks A) p0 k0 n (user_block_ptrs_NoDup A HWF) Hp0 Hp).
      - exact REG2.
      - intros H. rewrite (INIT2 INIT0) in H. discriminate. }
    apply SR_ret. exists L1, A1, R2, m2, md2, bl1, bl2, (sb_free b k0), w.
    assert (KF : forall a, free_a B a -> ~ (bv_unsigned sp - 8240 <= a < bv_unsigned sp - 32) ->
               ~ (errno_addr B <= a < errno_addr B + 4) -> ~ (r0 <= a < r0 + k0) ->
               mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)).
    { intros a Hf Hs He Hb.
      apply PF; [destruct Hf as [Hf|(Hf & _)]; [left | right]; exact Hf
               | exact (free_a_not_owned B _ LAWS AX L A m1 md a (proj1 CP1) Hf)
               | exact (free_a_not_owned B _ LAWS AX L1 A1 m2 md2 a PM Hf)
               | unfold scratch; unfold spZ; rewrite E1_2, unsigned_lit by lia; change ALLOC_STACK with 8192;
                 intros [H|H]; [lia | exact (He H)]
               | rewrite EP0; exact Hb]. }
    assert (KG : forall a, 0x33ff0 <= a < 0x33ff0 + 1020 ->
               mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)).
    { intros a Ha. destruct (FGI a (in_fg a Ha)) as (I1 & I2 & I3 & I4). apply KF; [exact (grec_free a Ha) | lia | exact I4 |].
      intros Hb. destruct (mr_blocks B _ LAWS L A mem md p0 k0 (a - r0) HMR Hp0 ltac:(lia)) as (_ & H4 & H5 & _).
      pose proof (ax_blocks_img AX L A mem md p0 k0 (a - r0) HMR Hp0 ltac:(lia)) as NI.
      rewrite EP0 in NI. replace (r0 + (a - r0)) with a in NI by ring. exact (NI I1). }
    split; [rewrite E1_1; reflexivity|].
    split; [change (spZ regs) with (bv_unsigned sp); exact RJ2|].
    split; [change (spZ regs) with (bv_unsigned sp); exact (eq_trans (PR 2 ltac:(unfold callee_saved; lia)) E1_2)|].
    split; [exact (eq_trans (PR 8 ltac:(unfold callee_saved; lia)) E1_8)|].
    split; [exact (eq_trans (PR 9 ltac:(unfold callee_saved; lia)) E1_9)|].
    split; [exact (eq_trans (PR 18 ltac:(unfold callee_saved; lia)) E1_18)|].
    split; [exact (kept_rest_trans _ _ _ KR1 (kept_rest_of_pres _ _ PR))|].
    split.
    { change (spZ regs) with (bv_unsigned sp). apply (rw_cells_transfer rsegs m1); [exact FR1|].
      intros i Hi. cbn in Hi. destruct (KF (bv_unsigned sp - 32 + i)) as [K1 K2];
        [unfold free_a; left; lia | lia | lia
        | pose proof (block_facts B _ LAWS _ _ _ _ _ _ 0 HMR Hin ltac:(lia)) as (_ & _ & Hrk & _); lia |].
      split; [exact K1 | apply K2]. }
    split.
    { apply (rw_cells_transfer rsegs m1); [exact NR1|]. intros i Hi. cbn in Hi.
      destruct (KG (0x343c0 + i)) as [K1 K2]; [lia|]. split; [exact K1 | apply K2]. }
    split; [exact W4|].
    split.
    { apply (rw_cells_transfer rsegs m1); [exact RP1|]. intros i Hi. cbn in Hi.
      destruct (KG (0x343c8 + i)) as [K1 K2]; [lia|]. split; [exact K1 | apply K2]. }
    split; [exact BL2|].
    split; [rewrite EQR, <- EP0; exact BL1|].
    split; [exact RA2|].
    split.
    { intros i Hi. rewrite <- (GOT1 i Hi). rewrite <- SEGS. pose proof (GK2 i Hi) as G. rewrite GOTG in G. exact G. }
    split; [exact INIT2|].
    split; [exact RES2|]. split; [apply sb_free_le; lia|].
    exact (sb_shift_del b L A L1 A1 bl1 bl2 _ k0 BL1 BL2).
  - rewrite RPQ in E1_10.
    pose proof FREE_NULL as FN. unfold free_null_contract in FN. rewrite SEGS, FREE_PC in FN.
    eapply SR_bind; [apply FN; [exact RET1 | exact E1_10 | exact Hh | exact Hl] |].
    intros c2 ->. apply SR_ret. exists L, A, R1, m1, md, (blocks L A), [], b, w.
    split; [rewrite E1_1; reflexivity|].
    split; [change (spZ regs) with (bv_unsigned sp); exact RJ1|].
    split; [change (spZ regs) with (bv_unsigned sp); exact E1_2|].
    split; [exact E1_8|]. split; [exact E1_9|]. split; [exact E1_18|]. split; [exact KR1|].
    split; [change (spZ regs) with (bv_unsigned sp); exact FR1|].
    split; [exact NR1|]. split; [exact W4|]. split; [exact RP1|].
    split; [rewrite app_nil_r; reflexivity|].
    split; [rewrite EQR, app_nil_r; reflexivity|].
    split; [exact RA1|]. split; [exact GOT1|]. split; [tauto|].
    split; [exact RES|]. split; [apply sb_le_refl | symmetry; apply sb_shift_refl].
Qed.

Lemma fresh_apart : forall q n lo len, (forall i, 0 <= i < n -> ~ in_img B (q + i)) -> 0 < n ->
  0x33ff0 <= lo -> lo + len <= 0x33ff0 + 1020 -> 0 < len -> iv_apart q n lo len.
Proof.
  intros q n lo len H Hn H1 H2 H3. unfold iv_apart.
  destruct (Z_le_gt_dec (q + n) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec (lo + len) q) as [D'|D']; [right; exact D'|]. exfalso.
  apply (H (Z.max q lo - q)); [lia|]. replace (q + (Z.max q lo - q)) with (Z.max q lo) by lia. apply grec_img. lia.
Qed.

Lemma rjr_munch_rec : forall Lc Ac memc mdc memc' lo hi,
  rjr B (aa_MR API) 8240 (spZ regs) socket_send_writes gone_r L A mem md Lc Ac memc mdc ->
  munch [(lo, hi)] memc memc' -> wmono rsegs memc memc' ->
  (forall a, lo <= a < hi -> socket_send_writes a) ->
  rjr B (aa_MR API) 8240 (spZ regs) socket_send_writes gone_r L A mem md Lc Ac memc' mdc.
Proof.
  intros Lc Ac memc mdc memc' lo hi RJ MU WM HE.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof (rjr_bounds B (aa_MR API) _ _ _ _ _ _ _ _ _ _ _ _ RJ) as (B1 & B2 & B3).
  pose proof RJ as (HMc & _).
  pose proof (proj1 PRE) as HMR.
  assert (WR : forall a, ~ outside [(lo, hi)] a -> 0x33ff0 <= a < 0x33ff0 + 1020).
  { intros a Ha. assert (Hl : lo <= a < hi) by (cbn in Ha; lia). pose proof (HE a Hl) as Hs.
    unfold socket_send_writes, G_REC, OFF_NREPLIES, OFF_REPLY in Hs. lia. }
  apply (rjr_munch B (aa_MR API) SEGS LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RJ MU ltac:(rewrite SEGS; exact WM)).
  - intros a Ra Hn Hf. right. apply HE. cbn in Hn. lia.
  - intros a Ra Hn. apply (FGO Lc Ac memc mdc a HMc). apply in_fg. exact (WR a Hn).
  - intros a Ha. cbn. split; [|exact I]. intros Hl. pose proof (HE a Hl) as Hs.
    unfold socket_send_writes, G_REC, OFF_NREPLIES, OFF_REPLY in Hs. lia.
  - intros p n i Hp _ Hi. pose proof (ax_blocks_img AX L A mem md p n i HMR Hp Hi) as NI.
    destruct (outside_dec [(lo, hi)] (ptr_addr L p + i)) as [H|H]; [exact H|]. exfalso. apply NI. apply grec_img. exact (WR _ H).
  - intros p n i Hp Hi. destruct (mr_blocks B _ LAWS Lc Ac memc mdc p n i HMc Hp Hi) as (Hpr & H4 & H5 & _).
    pose proof (ax_blocks_img AX Lc Ac memc mdc p n i HMc Hp Hi) as NI.
    apply (munch_present _ _ _ _ MU); [lia | | exact Hpr].
    destruct (outside_dec [(lo, hi)] (ptr_addr Lc p + i)) as [H|H]; [exact H|]. exfalso. apply NI. apply grec_img. exact (WR _ H).
Qed.

Lemma rec_kept : forall Lc Ac memc mdc,
  rjr B (aa_MR API) 8240 (spZ regs) socket_send_writes gone_r L A mem md Lc Ac memc mdc ->
  forall a, G_REC <= a < G_REC + REC_SIZE \/ REC_SC <= a < REC_SC + SC_SIZE -> ~ socket_send_writes a ->
  mbyte rsegs memc a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs memc a).
Proof.
  intros Lc Ac memc mdc RJ a Ha Hn. pose proof alloc_ceiling_val as AC.
  pose proof (rjr_bounds B (aa_MR API) _ _ _ _ _ _ _ _ _ _ _ _ RJ) as (B1 & B2 & B3).
  pose proof RJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  assert (Hg : 0x33ff0 <= a < 0x33ff0 + 1020) by (unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia).
  rewrite <- SEGS. apply HF; [exact (grec_free a Hg) | lia | exact (proj2 (proj2 (proj2 (FGI a (in_fg a Hg))))) | exact Hn].
Qed.

Lemma nonrep_lay : forall pn, In pn (nonrep Q) -> In pn (lay_blocks Q).
Proof. intros pn H. rewrite lay_nonrep. apply in_or_app. left. exact H. Qed.

Lemma nonrep_blk : forall pn, In pn (nonrep Q) -> In pn (blocks L A).
Proof. intros pn H. exact (rep_at_blocks rsegs _ _ _ _ _ _ pn HREP (nonrep_lay pn H)). Qed.

Lemma nonrep_notrep : forall pn, In pn (nonrep Q) -> ~ In pn (oblk (l_reply Q)).
Proof.
  intros pn H Hr. pose proof HREP as (_ & _ & _ & _ & _ & ND & _). rewrite lay_nonrep in ND.
  exact (nodup_fst_disj _ _ pn pn ND H Hr eq_refl).
Qed.

Lemma nonrep_pos : forall pn, In pn (nonrep Q) -> 0 < snd pn.
Proof.
  intros pn H. exact (rec_rep_pos rsegs G_REC REC_SC L A mem R O pn (ex_intro _ Q (conj HREP HO))
    (proj2 (HO pn) (nonrep_lay pn H))).
Qed.

Lemma nonrep_iff : forall pn, In pn (nonrep Q) <-> In pn O /\ fst pn <> r0.
Proof.
  intros pn. pose proof (aa_laws API) as LAWS. pose proof HREP as (_ & _ & _ & _ & _ & ND & _). rewrite lay_nonrep in ND.
  pose proof RPQ as RQ. split.
  - intros H. pose proof (nonrep_blk pn H) as Hb. pose proof (nonrep_pos pn H) as Hn.
    split; [apply HO; exact (nonrep_lay pn H)|].
    destruct (l_reply Q) as [[a k]|].
    + destruct RQ as (E & _ & _). cbn [fst] in E. subst a.
      exact (nodup_fst_disj _ _ pn (r0, k) ND H (or_introl eq_refl)).
    + rewrite RQ. intros E. destruct pn as [p n]. cbn [fst snd] in *.
      destruct (block_facts B _ LAWS _ _ _ _ _ _ 0 (proj1 PRE) Hb ltac:(lia)) as (_ & H4 & _). lia.
  - intros (H1 & H2). apply HO in H1. rewrite lay_nonrep in H1. apply in_app_or in H1 as [H|H]; [exact H|].
    exfalso. destruct (l_reply Q) as [[a k]|]; cbn [oblk In] in H; [|exact H].
    destruct H as [E|[]]. subst pn. destruct RQ as (E & _). exact (H2 E).
Qed.

Lemma kept_blk : forall bl1 bl2 pn,
  (match l_reply Q with None => blocks L A = bl1 ++ bl2 | Some p1 => blocks L A = bl1 ++ p1 :: bl2 end) ->
  In pn (blocks L A) -> ~ In pn (oblk (l_reply Q)) -> In pn (bl1 ++ bl2).
Proof.
  intros bl1 bl2 pn BLA H N. destruct (l_reply Q) as [p1|]; rewrite BLA in H; [|exact H].
  apply in_app_or in H as [H|[E|H]]; [apply in_or_app; left; exact H | | apply in_or_app; right; exact H].
  exfalso. apply N. left. exact E.
Qed.

Lemma reply_notin : forall bl1 bl2 p1, 1 <= snd p1 -> blocks L A = bl1 ++ p1 :: bl2 -> ~ In p1 (bl1 ++ bl2).
Proof.
  intros bl1 bl2 [a k] Hk BLA H. pose proof (aa_laws API) as LAWS.
  pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ (proj1 PRE) BLA H) as D. cbn [snd] in Hk. lia.
Qed.

Lemma blk_clause : forall bl1 bl2 pn,
  (match l_reply Q with None => blocks L A = bl1 ++ bl2 | Some p1 => blocks L A = bl1 ++ p1 :: bl2 end) ->
  In pn (bl1 ++ bl2) -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn (nonrep Q).
Proof.
  intros bl1 bl2 pn BLA H.
  assert (HB : In pn (blocks L A)).
  { destruct (l_reply Q) as [p1|]; rewrite BLA; [|exact H].
    apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
  destruct (In_dec pair_dec pn O) as [HI|HI]; [|left; split; assumption].
  right. apply HO in HI. rewrite lay_nonrep in HI. apply in_app_or in HI as [H'|H']; [exact H'|].
  exfalso. pose proof RPQ as RQ. destruct (l_reply Q) as [p1|]; cbn [oblk In] in H'; [|exact H'].
  destruct H' as [E|[]]. subst pn. destruct RQ as (_ & _ & Hk). exact (reply_notin bl1 bl2 p1 Hk BLA H).
Qed.

Lemma reply_clause : forall bl1 bl2,
  (match l_reply Q with None => blocks L A = bl1 ++ bl2 | Some p1 => blocks L A = bl1 ++ p1 :: bl2 end) ->
  match r_reply R with
  | None => r0 = 0 /\ blocks L A = bl1 ++ bl2
  | Some _ => exists k0, In (r0, k0) O /\ blocks L A = bl1 ++ (r0, k0) :: bl2
  end.
Proof.
  intros bl1 bl2 BLA. pose proof HREP as (_ & _ & _ & HPR & _ & _). unfold reply_at in HPR.
  pose proof RPQ as RQ.
  destruct (r_reply R) as [x0|]; destruct (l_reply Q) as [[a k]|] eqn:EQR; try contradiction.
  - destruct RQ as (E & _ & _). cbn [fst] in E. subst a. exists k. split; [|exact BLA].
    apply HO. rewrite lay_nonrep, EQR. apply in_or_app. right. left. reflexivity.
  - split; [exact RQ | exact BLA].
Qed.

Lemma rjr_gone_O : forall a n, gone_r (a, n) -> In a (map fst O).
Proof.
  intros a n H. apply (in_map fst O (a, n)). apply HO. rewrite lay_nonrep. apply in_or_app. right. exact H.
Qed.

Lemma rjr_kept_nonrep : forall L' A' m' md',
  rjr B (aa_MR API) 8240 (spZ regs) socket_send_writes gone_r L A mem md L' A' m' md' ->
  forall pn, In pn (nonrep Q) -> In pn (blocks L' A') /\
    forall i, 0 <= i < snd pn -> mbyte rsegs m' (fst pn + i) = mbyte rsegs mem (fst pn + i).
Proof.
  intros L' A' m' md' RJ pn H.
  pose proof (rjr_others_kept B (aa_MR API) _ _ _ _ _ _ _ _ _ _ _ _ (oblk (l_reply Q)) RJ (fun pn G => G)) as OK.
  pose proof (nonrep_blk pn H) as Hb. pose proof (nonrep_notrep pn H) as Hn.
  unfold blocks in Hb. apply in_map_iff in Hb as ([p k] & E & Hp). cbn [fst snd] in E. subst pn.
  destruct (OK p k Hp Hn) as (Hp' & EA & KB). split.
  - rewrite <- EA. unfold blocks. apply in_map_iff. exists (p, k). split; [reflexivity | exact Hp'].
  - intros i Hi. cbn [fst snd] in *. rewrite <- SEGS. exact (KB i Hi).
Qed.

Lemma buf_kept : forall Lc Ac memc mdc, 0 < size ->
  rjr B (aa_MR API) 8240 (spZ regs) socket_send_writes gone_r L A mem md Lc Ac memc mdc ->
  ro_agree rsegs memc -> Mem.bytes_at rsegs memc buf x.
Proof.
  intros Lc Ac memc mdc Hs RJ RAc. pose proof alloc_ceiling_val as AC.
  pose proof (SZP Hs) as (SZL & LX & BX & BSP & HOME & NRA & ROOM).
  pose proof RJ as (_ & _ & _ & _ & _ & _ & _ & K1 & K2 & K3 & HF & HRM & HKP & _).
  apply (bytes_at_transfer rsegs mem); [exact BX|]. intros i Hi. rewrite LX in Hi.
  unfold buf_home in HOME. rewrite SEGS in HOME.
  destruct HOME as [(H1 & H2) | [(qb & kb & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
  - rewrite <- SEGS. refine (proj1 (HF (buf + i) _ _ _ _)); [unfold free_a; left; lia | lia | lia |].
    unfold socket_send_writes, G_REC, OFF_NREPLIES, OFF_REPLY. lia.
  - unfold blocks in Hq. apply in_map_iff in Hq as ([pb kb'] & E & Hpb). cbn [fst snd] in E.
    injection E as E1 E2. subst qb kb.
    rewrite <- SEGS. replace (buf + i) with (ptr_addr L pb + (buf + i - ptr_addr L pb)) by ring.
    apply (HKP pb kb' (buf + i - ptr_addr L pb) Hpb); [|lia].
    intros G. apply Hnq. exact (rjr_gone_O _ _ G).
  - rewrite (mbyte_ro_agree _ _ _ RAc (H3 i Hi)), (mbyte_ro_agree _ _ _ RA (H3 i Hi)). reflexivity.
Qed.

Definition SPOST (c' : config) : Prop :=
  exists L' A' regs' mem' md' R' O' (r0' q : Z) (bl1 bl2 : list (Z * Z)),
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
    call_post_rec B (aa_MR API) SOCKET_SEND_K L A regs mem md socket_send_writes (fun a => In a (map fst O))
      L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 size /\
    R' = fst (socket_send_m R x) /\
    g_rec_rep rsegs L' A' mem' R' O' /\
    Mem.bytes_at rsegs mem (G_REC + OFF_REPLY) (Mem.le8 (Z_to_bv 64 r0')) /\
    (match r_reply R with
     | None => r0' = 0 /\ blocks L A = bl1 ++ bl2
     | Some _ => exists k0, In (r0', k0) O /\ blocks L A = bl1 ++ (r0', k0) :: bl2
     end) /\
    (size <= 0 -> blocks L' A' = bl1 ++ bl2 /\ (forall pn, In pn O' <-> In pn O /\ fst pn <> r0')) /\
    (0 < size ->
       (exists c1 c2, blocks L' A' = c1 ++ (q, size) :: c2 /\ c1 ++ c2 = bl1 ++ bl2) /\
       fresh_block B q size /\ q mod 16 = 0 /\
       (forall pn, In pn O' <-> (In pn O /\ fst pn <> r0') \/ pn = (q, size))) /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
    others_kept rsegs L A mem L' A' mem' O /\
    ro_agree rsegs mem' /\ f18_words rsegs mem' /\
    (st_init_done A = true -> st_init_done A' = true) /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (if 0 <? size then sb_malloc b size else b) /\
    res_ok_slots A' (sb_shift b A A').

Lemma ss_end : forall L' A' R' m' md' (qn : option (Z * Z)) (q : Z) bl1 bl2 w,
  rjr B (aa_MR API) 8240 (spZ regs) socket_send_writes gone_r L A mem md L' A' m' md' ->
  regs_preserved regs R' -> getr R' 10 = Z_to_bv 64 size ->
  rw_cells rsegs m' 0x343c0 [C4 w] -> le4 w = le4 (Z_to_bv 64 (r_nreplies R + 1)) ->
  reply_at rsegs (blocks L' A') m' G_REC (r_reply (fst (socket_send_m R x))) qn ->
  (forall p1, In p1 (oblk qn) -> iv_apart (fst p1) (snd p1) G_REC REC_SIZE /\ iv_apart (fst p1) (snd p1) REC_SC SC_SIZE /\
     forall pn, In pn (nonrep Q) -> fst pn <> fst p1) ->
  (match l_reply Q with None => blocks L A = bl1 ++ bl2 | Some p1 => blocks L A = bl1 ++ p1 :: bl2 end) ->
  (size <= 0 -> blocks L' A' = bl1 ++ bl2 /\ qn = None) ->
  (0 < size -> qn = Some (q, size) /\ (exists c1 c2, blocks L' A' = c1 ++ (q, size) :: c2 /\ c1 ++ c2 = bl1 ++ bl2) /\
     fresh_block B q size /\ q mod 16 = 0) ->
  ro_agree rsegs m' ->
  (forall i, 0 <= i < 8 -> mbyte rsegs m' (0x22d40 + i) = mbyte rsegs mem (0x22d40 + i)) ->
  (st_init_done A = true -> st_init_done A' = true) ->
  sb_le (sb_shift b A A') (if 0 <? size then sb_malloc b size else b) ->
  res_ok_slots A' (sb_shift b A A') ->
  SPOST (mkCfg (mkst R' (getr regs 1) m' (seg_rom rsegs)) md').
Proof.
  intros L' A' R' m' md' qn q bl1 bl2 w RJ RP A10 NR W4 RPY OWN BLA HN HP RA' GOT' INIT' GRW RES'.
  pose proof RJ as (HM' & _ & _ & _ & _ & HLen & _).
  unfold SPOST.
  exists L', A', R', m', md', (fst (socket_send_m R x)), (nonrep Q ++ oblk qn), r0, q, bl1, bl2.
  split; [reflexivity|].
  split.
  { apply (rjr_final B (aa_MR API) CTXO SOCKET_SEND_K socket_send_writes gone_r (fun a => In a (map fst O))
             L A regs mem md L' A' R' m' md' PRE RJ RP).
    exact rjr_gone_O. }
  split; [exact A10|].
  split; [reflexivity|].
  split.
  { exists (RLay (l_calls Q) (l_spill Q) (l_answer Q) qn). split; [|intros pn; rewrite lay_setrep; reflexivity].
    change (fst (socket_send_m R x)) with (set_reply R (r_nreplies R + 1) (match x with [] => None | _ :: _ => Some x end)).
    apply (rep_at_set_reply rsegs (blocks L A) (blocks L' A') mem m' G_REC REC_SC R Q
             (match x with [] => None | _ :: _ => Some x end) qn HREP).
    - intros a Ha. refine (proj1 (rec_kept L' A' m' md' RJ a _ _)).
      + unfold REC_SIZE, SC_SIZE, G_REC, REC_SC in *. lia.
      + unfold socket_send_writes, G_REC, REC_SC, OFF_NREPLIES, OFF_REPLY in *. lia.
    - intros a Ha _. apply glob_writable. change (Z.of_nat GLOB_N) with 1020.
      unfold GLOB_LO, REC_SIZE, SC_SIZE, G_REC, REC_SC in *. lia.
    - intros pn Hpn. exact (rjr_kept_nonrep L' A' m' md' RJ pn Hpn).
    - intros pn p1 Hpn Hp1. exact (proj2 (proj2 (OWN p1 Hp1)) pn Hpn).
    - change (G_REC + OFF_NREPLIES) with 0x343c0. rewrite <- W4. exact (c4_bytes m' 0x343c0 w NR).
    - lia.
    - exact RPY.
    - intros p1 Hp1. destruct (OWN p1 Hp1) as (H1 & H2 & _). split; assumption. }
  split; [exact RPB|].
  split; [exact (reply_clause bl1 bl2 BLA)|].
  split.
  { intros Hs. destruct (HN Hs) as [EB Eq]. split; [exact EB|]. intros pn. rewrite Eq. cbn [oblk]. rewrite app_nil_r.
    apply nonrep_iff. }
  split.
  { intros Hs. destruct (HP Hs) as (Eq & CC & FB & AL). split; [exact CC|]. split; [exact FB|]. split; [exact AL|].
    intros pn. rewrite Eq. cbn [oblk]. rewrite in_app_iff, (nonrep_iff pn). cbn [In].
    split; intros [H|H];
      [left; exact H | right; destruct H as [H|[]]; symmetry; exact H | left; exact H | right; left; symmetry; exact H]. }
  split.
  { intros pn Hpn. destruct (Z_le_gt_dec size 0) as [Hs|Hs].
    - destruct (HN Hs) as [EB Eq]. rewrite EB in Hpn.
      destruct (blk_clause bl1 bl2 pn BLA Hpn) as [H|H]; [left; exact H | right; apply in_or_app; left; exact H].
    - destruct (HP ltac:(lia)) as (Eq & (c1 & c2 & EB & EC) & _). rewrite EB in Hpn.
      apply in_app_or in Hpn as [H|[H|H]].
      + assert (H' : In pn (bl1 ++ bl2)) by (rewrite <- EC; apply in_or_app; left; exact H).
        destruct (blk_clause bl1 bl2 pn BLA H') as [H2|H2]; [left; exact H2 | right; apply in_or_app; left; exact H2].
      + right. apply in_or_app. right. rewrite Eq. left. exact H.
      + assert (H' : In pn (bl1 ++ bl2)) by (rewrite <- EC; apply in_or_app; right; exact H).
        destruct (blk_clause bl1 bl2 pn BLA H') as [H2|H2]; [left; exact H2 | right; apply in_or_app; left; exact H2]. }
  split.
  { rewrite <- SEGS. apply (rjr_others_kept B (aa_MR API) _ _ _ _ _ _ _ _ _ _ _ _ O RJ).
    intros pn G. apply HO. rewrite lay_nonrep. apply in_or_app. right. exact G. }
  split; [exact RA'|].
  split.
  { destruct (ax_statics AX L' A' m' md' HM') as (_ & (g & Hg & HGW) & _).
    apply (RecAnsB.f18_words_after mem m' g F18); [| exact Hg | rewrite SEGS, GRD in HGW; exact HGW].
    intros i Hi. unfold snprintf_c.GOT_GUARD. exact (GOT' i Hi). }
  split; [exact INIT'|].
  split; [exact HLen|]. split; [exact GRW | exact RES'].
Qed.

Lemma ss_stage2n : forall c, P1 c -> size <= 0 -> SR rsegs c SPOST.
Proof.
  intros c (L1 & A1 & R2 & m2 & md2 & bl1 & bl2 & b1 & w & -> & RJ & E2_2 & E2_8 & E2_9 & E2_18 & KR2 & FR2 & NR2 & W4 & RP2
    & BL1 & BLA & RA2 & GOT2 & INIT2 & RES2 & BLE & EB1) Hs.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SOCKET_SEND_K, XMALLOC_K in HCEIL. change ALLOC_STACK with 8192 in HCEIL.
  set (sp := reg_get regs 2).
  change (spZ regs) with (bv_unsigned sp) in E2_2, FR2, HCEIL.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (R2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 32)) by exact E2_2.
  assert (R2_8 : reg_get R2 8 = Z_to_bv 64 size) by exact E2_8.
  assert (R2_18 : reg_get R2 18 = Z_to_bv 64 0x33ff0) by exact E2_18.
  pose proof RJ as (HM2 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R2_2, R2_8, R2_18.
    eapply ss_run2n; [exact FR2 | exact RP2 | lia | lia]. }
  intros ms3 (can3 & Q3 & EQ3).
  destruct Q3 as (t0' & t1' & t2' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3 & RP3).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (KR3 : kept_rest R2 R3) by kept_rest_tac X3.
  assert (RJ3 : rjr B (aa_MR API) 8240 (spZ regs) socket_send_writes gone_r L A mem md L1 A1 m3 md2).
  { apply (rjr_munch_rec L1 A1 m2 md2 m3 0x343c8 0x343d8 RJ MU3 WM3).
    intros a Ha. unfold socket_send_writes, G_REC, OFF_NREPLIES, OFF_REPLY. lia. }
  assert (NR3 : rw_cells rsegs m3 0x343c0 [C4 w]).
  { apply (rw_cells_munch _ m2 m3 _ _ NR2 MU3). intros i Hi. cbn in Hi. cbn. lia. }
  assert (RA3 : ro_agree rsegs m3).
  { apply (ro_agree_munch rsegs m2 m3 _ RA2 MU3). intros y Hy. pose proof (bv_unsigned_in_range 64 y) as Ry.
    unfold bv_modulus in Ry. cbn. split; [|exact I]. intros H1.
    rewrite <- (Z_to_bv_bv_unsigned y), grec_ro_false in Hy by lia. discriminate. }
  assert (RPC : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite RPC.
  pose proof (SZN Hs) as EX.
  apply SR_ret.
  apply (ss_end L1 A1 R3 m3 md2 None 0 bl1 bl2 w RJ3).
  - apply preserved_parts; [exact (kept_rest_trans _ _ _ KR2 KR3) | | | |];
      pres_reg_tac X3.
  - rewrite (getr_of_eqv _ _ 10 X3 eq_refl). simp_regs. reflexivity.
  - exact NR3.
  - exact W4.
  - change (r_reply (fst (socket_send_m R x))) with (match x with [] => None | _ :: _ => Some x end).
    rewrite EX. unfold reply_at. destruct (c8_bytes2 m3 0x343c8 _ _ RP3) as [P1 P2].
    split; [exact P1 | exact P2].
  - intros p1 [].
  - exact BLA.
  - intros _. split; [exact BL1 | reflexivity].
  - intros H. lia.
  - exact RA3.
  - intros i Hi. rewrite <- (GOT2 i Hi). apply (munch_mbyte _ _ _ _ _ MU3); [lia|]. cbn. lia.
  - exact INIT2.
  - rewrite <- EB1. replace (0 <? size) with false by (symmetry; apply Z.ltb_ge; exact Hs). exact BLE.
  - rewrite <- EB1. exact RES2.
Qed.

Lemma ss_stage2p : forall c, P1 c -> 0 < size -> SR rsegs c SPOST.
Proof.
  intros c (L1 & A1 & R2 & m2 & md2 & bl1 & bl2 & b1 & w & -> & RJ & E2_2 & E2_8 & E2_9 & E2_18 & KR2 & FR2 & NR2 & W4 & RP2
    & BL1 & BLA & RA2 & GOT2 & INIT2 & RES2 & BLE & EB1) Hs.
  pose proof (SZP Hs) as (SZL & LX & BX & BSP & HOME & NRA & ROOM).
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SOCKET_SEND_K, XMALLOC_K in HCEIL. change ALLOC_STACK with 8192 in HCEIL.
  set (sp := reg_get regs 2).
  assert (SPV : spZ regs = bv_unsigned sp) by reflexivity.
  change (spZ regs) with (bv_unsigned sp) in E2_2, FR2, HCEIL, HAL, H63.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (R2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 32)) by exact E2_2.
  assert (R2_8 : reg_get R2 8 = Z_to_bv 64 size) by exact E2_8.
  assert (R2_18 : reg_get R2 18 = Z_to_bv 64 0x33ff0) by exact E2_18.
  pose proof RJ as (HM2 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R2_2, R2_8, R2_18.
    eapply ss_run2p; [exact FR2 | exact RP2 | lia | lia]. }
  intros ms3 (can3 & Q3 & EQ3).
  destruct Q3 as (t0' & t1' & t2' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3 & FR3 & RP3).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (KR3 : kept_rest regs R3) by (apply (kept_rest_trans _ R2); [exact KR2 | kept_rest_tac X3]).
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x173cc) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_8 : getr R3 8 = Z_to_bv 64 size) by (rewrite (getr_of_eqv _ _ 8 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_9 : getr R3 9 = Z_to_bv 64 buf) by (rewrite (getr_of_eqv _ _ 9 X3 eq_refl); simp_regs; exact E2_9).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 size) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_18 : getr R3 18 = Z_to_bv 64 0x33ff0) by (rewrite (getr_of_eqv _ _ 18 X3 eq_refl); simp_regs; reflexivity).
  assert (SP3 : spZ R3 = bv_unsigned sp - 32) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  assert (RJ3 : rjr B (aa_MR API) 8240 (spZ regs) socket_send_writes gone_r L A mem md L1 A1 m3 md2).
  { apply (rjr_munch_rec L1 A1 m2 md2 m3 0x343c8 0x343d8 RJ MU3 WM3).
    intros a Ha. unfold socket_send_writes, G_REC, OFF_NREPLIES, OFF_REPLY. lia. }
  pose proof RJ3 as (HM3 & _).
  assert (RA3 : ro_agree rsegs m3).
  { apply (ro_agree_munch rsegs m2 m3 _ RA2 MU3). intros y Hy. pose proof (bv_unsigned_in_range 64 y) as Ry.
    unfold bv_modulus in Ry. cbn. split; [|exact I]. intros H1.
    rewrite <- (Z_to_bv_bv_unsigned y), grec_ro_false in Hy by lia. discriminate. }
  assert (NR3 : rw_cells rsegs m3 0x343c0 [C4 w]).
  { apply (rw_cells_munch _ m2 m3 _ _ NR2 MU3). intros i Hi. cbn in Hi. cbn. lia. }
  assert (GOT3 : forall i, 0 <= i < 8 -> mbyte rsegs m3 (0x22d40 + i) = mbyte rsegs mem (0x22d40 + i)).
  { intros i Hi. rewrite <- (GOT2 i Hi). apply (munch_mbyte _ _ _ _ _ MU3); [lia|]. cbn. lia. }
  assert (RET3 : YK0s.ret_ok (getr R3 1)) by (rewrite E3_1; apply bv_eq; vm_compute; reflexivity).
  assert (CP3 : call_pre_k B (aa_MR API) XMALLOC_K L1 A1 R3 m3 md2).
  { apply (call_pre_k_of_rjr B (aa_MR API) 8240 (spZ regs) socket_send_writes gone_r L A mem md L1 A1 m3 md2
             XMALLOC_K R3 RJ3 RET3); unfold XMALLOC_K; change ALLOC_STACK with 8192; rewrite ?SP3, ?SPV; [| lia | lia | lia |].
    - replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring. rewrite Z.mod_add by lia. exact HAL.
    - exact (eq_trans (KR3 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) HTP). }
  pose proof XM as XMC. unfold xmalloc_contract in XMC. rewrite SEGS in XMC.
  assert (XS : xmalloc_size size = size) by (unfold xmalloc_size; destruct (Z.eqb_spec size 0); lia).
  assert (ROOM1 : room_slots (sb_malloc b1 size) size)
    by exact (room_slots_mono (sb_malloc b1 size) (sb_malloc b size) size size (sb_malloc_mono b1 b size BLE) ltac:(lia) ROOM).
  eapply SR_bind.
  { apply (XMC L1 A1 R3 m3 md2 size b1); [exact CP3 | exact E3_10 | lia | exact RES2 | rewrite XS; exact ROOM1 | exact RA3]. }
  intros cf4 RET4. rewrite XS in RET4.
  destruct RET4 as (L2 & A2 & R4 & m4 & md4 & q & -> & POST4 & A04 & NZ & AL16 & FRESH & BLK4 & KEPT4 & RA4 & GK4 & UB4
    & INIT4 & REG4 & RES4).
  rewrite SEGS in RA4.
  destruct BLK4 as (b1' & b2' & BLK4a & BLK4b).
  pose proof FRESH as (FR_lo & FR_hi & FR_img).
  pose proof POST4 as (PM4 & PW4 & PB4 & PL4 & PS4 & PR4 & PV4 & PF4 & PK4 & PSc4).
  assert (INB4 : In (q, size) (blocks L2 A2)) by (rewrite BLK4a; apply in_or_app; right; left; reflexivity).
  assert (RJ4 : rjr B (aa_MR API) 8240 (spZ regs) socket_send_writes gone_r L A mem md L2 A2 m4 md4).
  { eapply (rjr_post B (aa_MR API) SEGS LAWS AX ERRNO_LOW); [exact RJ3 | apply call_post_k_rec; exact POST4 | | | | | | |].
    - rewrite SP3, SPV. unfold XMALLOC_K. change ALLOC_STACK with 8192. lia.
    - rewrite SP3, SPV. lia.
    - intros a Fa _. exfalso. exact Fa.
    - intros p n _ _ _ [].
    - intros p n Hp Hc Hn. exfalso. exact (Hn (UB4 p n Hc)).
    - exact REG4.
    - intros H. rewrite INIT4 in H. discriminate. }
  assert (KF4 : forall a, free_a B a -> ~ (bv_unsigned sp - 8240 <= a < bv_unsigned sp - 32) ->
             ~ (errno_addr B <= a < errno_addr B + 4) ->
             mbyte rsegs m4 a = mbyte rsegs m3 a /\ (writable_at rsegs m3 a <-> writable_at rsegs m4 a)).
  { intros a Hf Hs' He. rewrite <- SEGS.
    apply PF4; [destruct Hf as [Hf|(Hf & _)]; [left | right]; exact Hf
              | exact (free_a_not_owned B _ LAWS AX L1 A1 m3 md2 a HM3 Hf)
              | exact (free_a_not_owned B _ LAWS AX L2 A2 m4 md4 a PM4 Hf)
              | unfold scratch_k, XMALLOC_K; rewrite SP3; change ALLOC_STACK with 8192; intros [H|H]; [lia | exact (He H)]
              | intros F; exact F]. }
  assert (KG4 : forall a, 0x33ff0 <= a < 0x33ff0 + 1020 ->
             mbyte rsegs m4 a = mbyte rsegs m3 a /\ (writable_at rsegs m3 a <-> writable_at rsegs m4 a)).
  { intros a Ha. apply KF4; [exact (grec_free a Ha) | lia | exact (proj2 (proj2 (proj2 (FGI a (in_fg a Ha)))))]. }
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct (KF4 (bv_unsigned sp - 32 + i)) as [K1 K2]; [unfold free_a; left; lia | lia | pose proof ERRNO_LOW; lia |].
    split; [exact K1 | apply K2]. }
  assert (RP4 : rw_cells rsegs m4 0x343c8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_transfer rsegs m3); [exact RP3|]. intros i Hi. cbn in Hi.
    destruct (KG4 (0x343c8 + i)) as [K1 K2]; [lia|]. split; [exact K1 | apply K2]. }
  assert (NR4 : rw_cells rsegs m4 0x343c0 [C4 w]).
  { apply (rw_cells_transfer rsegs m3); [exact NR3|]. intros i Hi. cbn in Hi.
    destruct (KG4 (0x343c0 + i)) as [K1 K2]; [lia|]. split; [exact K1 | apply K2]. }
  assert (GOT4 : forall i, 0 <= i < 8 -> mbyte rsegs m4 (0x22d40 + i) = mbyte rsegs mem (0x22d40 + i)).
  { intros i Hi. rewrite <- (GOT3 i Hi). rewrite <- SEGS. pose proof (GK4 i Hi) as G. rewrite GOTG in G. exact G. }
  assert (E4_2 : reg_get R4 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by exact (eq_trans (PR4 2 ltac:(unfold callee_saved; lia)) E3_2).
  assert (E4_8 : reg_get R4 8 = Z_to_bv 64 size) by exact (eq_trans (PR4 8 ltac:(unfold callee_saved; lia)) E3_8).
  assert (E4_9 : reg_get R4 9 = Z_to_bv 64 buf) by exact (eq_trans (PR4 9 ltac:(unfold callee_saved; lia)) E3_9).
  assert (E4_18 : reg_get R4 18 = Z_to_bv 64 0x33ff0)
    by exact (eq_trans (PR4 18 ltac:(unfold callee_saved; lia)) E3_18).
  assert (E4_10 : reg_get R4 10 = Z_to_bv 64 q) by exact A04.
  assert (KR4 : kept_rest regs R4) by exact (kept_rest_trans _ _ _ KR3 (kept_rest_of_pres _ _ PR4)).
  destruct (mr_model _ _ LAWS _ _ _ _ PM4) as (Hh4 & Hl4 & _).
  assert (SEPbq : buf + size <= q \/ q + size <= buf).
  { pose proof HOME as HOME'. unfold buf_home in HOME'. rewrite SEGS in HOME'.
    destruct HOME' as [(H1 & H2) | [(qb & kb & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
    - right. lia.
    - assert (Hn1 : ~ In (qb, kb) (oblk (l_reply Q))) by (intros Hr; apply Hnq; exact (rjr_gone_O qb kb Hr)).
      pose proof (kept_blk bl1 bl2 (qb, kb) BLA Hq Hn1) as Hk.
      rewrite <- BL1, BLK4b in Hk.
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ PM4 BLK4a Hk) as D. lia.
    - destruct (Z_le_gt_dec (buf + size) q) as [D|D]; [left; exact D|].
      destruct (Z_le_gt_dec (q + size) buf) as [D'|D']; [right; exact D'|]. exfalso.
      apply (FR_img (Z.max buf q - q)); [lia|].
      replace (q + (Z.max buf q - q)) with (buf + (Z.max buf q - buf)) by lia.
      apply (ro_in_img B SEGS); [lia | apply H3; lia]. }
  assert (SEPq : q + size <= 0x343c8 \/ 0x343d8 <= q).
  { pose proof (fresh_apart q size 0x343c8 16 FR_img Hs ltac:(lia) ltac:(lia) ltac:(lia)) as D. unfold iv_apart in D. lia. }
  assert (SEPb : buf + size <= 0x343c8 \/ 0x343d8 <= buf).
  { apply (nra_sep buf size 0x343c8 0x343d8 NRA); unfold G_REC, REC_SIZE; lia. }
  assert (BX4 : Mem.bytes_at rsegs m4 buf x) by exact (buf_kept L2 A2 m4 md4 Hs RJ4 RA4).
  destruct (present_rw_cells rsegs (normalize rsegs m4) q (length x)) as [junk DX4]; [lia | rewrite LX; lia | |].
  { intros i Hi. rewrite LX in Hi. destruct (proj1 (block_facts B _ LAWS _ _ _ _ _ _ i PM4 INB4 Hi)) as [bb E].
    exists bb. rewrite normalize_rw; [exact E|]. apply (ro_addr_out B SEGS); [lia | apply FR_img; lia]. }
  assert (FR4n : rw_cells rsegs (normalize rsegs m4) (bv_unsigned sp - 32)
                   [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply rw_cells_normalize; [exact RA4 | exact FR4 |]. intros i Hi. cbn in Hi. unfold wa. apply ro_addr_hi. lia. }
  assert (RP4n : rw_cells rsegs (normalize rsegs m4) 0x343c8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply rw_cells_normalize; [exact RA4 | exact RP4 |]. intros i Hi. cbn in Hi. unfold wa. apply grec_ro_false. lia. }
  pose proof (bytes_at_normalize rsegs m4 buf _ RA4 BX4) as BX4n.
  rewrite E3_1, SEGS.
  eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E4_2, E4_8, E4_9, E4_10, E4_18.
    eapply (evt_normalize rsegs); [exact WX | exact RA4 |].
    eapply (ss_run3 MEMCPY);
      [exact FR4n | exact RP4n | lia | lia | exact LX | exact BX4n | exact DX4 | exact SEPbq | lia | lia | exact SEPq
      | exact SEPb | apply mem_inv_normalize]. }
  intros ms5 (can5 & (s5n & Q5 & REL5 & RO5) & EQ5).
  destruct Q5 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m5n
    & -> & MU5n & WM5n & MI5n & RP5n & DST5n & BX5n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL5) as [EC5 MR5r].
  revert EC5 MR5r RO5 EQ5. generalize (ms_mem can5) as m5. intros m5 EC5 MR5r RO5 EQ5. subst can5.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m4 RA4) MR5r RO5 MU5n) as MU5.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m4 RA4) MR5r RO5 WM5n) as WM5.
  pose proof (ro_agree_same rsegs _ _ RA4 RO5) as RA5.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR5r RP5n) as RP5.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR5r DST5n) as DST5.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  assert (KR5 : kept_rest regs R5) by (apply (kept_rest_trans _ R4); [exact KR4 | kept_rest_tac X5]).
  assert (OUT5 : forall a, 0 <= a < 2 ^ 64 -> ~ (0x343c8 <= a < 0x343d8) -> ~ (q <= a < q + size) ->
            outside [(0x343c8, 0x343d8); (q, q + size)] a) by (intros a _ H1 H2; cbn; tauto).
  assert (RJ5 : rjr B (aa_MR API) 8240 (spZ regs) socket_send_writes gone_r L A mem md L2 A2 m5 md4).
  { apply (rjr_munch B (aa_MR API) SEGS LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RJ4 MU5 ltac:(rewrite SEGS; exact WM5)).
    - intros a Ra Hn Hf. cbn in Hn.
      assert (C : 0x343c8 <= a < 0x343d8 \/ q <= a < q + size) by lia.
      destruct C as [C|C]; [right; unfold socket_send_writes, G_REC, OFF_NREPLIES, OFF_REPLY; lia|].
      exfalso. destruct Hf as [Hf|(Hf & _)]; [lia|]. apply (FR_img (a - q)); [lia|]. replace (q + (a - q)) with a by ring.
      exact Hf.
    - intros a Ra Hn. cbn in Hn.
      assert (C : 0x343c8 <= a < 0x343d8 \/ q <= a < q + size) by lia.
      destruct C as [C|C]; [apply (FGO L2 A2 m4 md4 a PM4); apply in_fg; lia|].
      pose proof (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - q) PM4 INB4 ltac:(lia))))) as NO.
      replace (q + (a - q)) with a in NO by ring. exact NO.
    - intros a Ha. pose proof (rjr_bounds B (aa_MR API) _ _ _ _ _ _ _ _ _ _ _ _ RJ4) as (B1 & _).
      apply OUT5; lia.
    - intros p n i Hp Hg Hi.
      pose proof (rjr_in_cur B (aa_MR API) _ _ _ _ _ _ _ _ _ _ _ _ p n RJ3 Hp Hg) as Hp1.
      pose proof RJ3 as (_ & HWA & _ & _ & HL3 & _).
      pose proof (ptr_addr_stable A L L1 p n HWA Hp HL3) as EA.
      assert (Hin1 : In (ptr_addr L p, n) (b1' ++ b2')).
      { rewrite <- BLK4b, <- EA. unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact Hp1]. }
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ PM4 BLK4a Hin1) as Dj.
      destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hp Hi) as (_ & H4 & H5 & _).
      pose proof (ax_blocks_img AX L A mem md p n i HMR Hp Hi) as NI.
      apply OUT5; [lia | intros Hr; apply NI; apply grec_img; lia | lia].
    - intros p n i Hp Hi. destruct (mr_blocks B _ LAWS L2 A2 m4 md4 p n i PM4 Hp Hi) as (Hpr & H4 & H5 & _).
      pose proof (ax_blocks_img AX L2 A2 m4 md4 p n i PM4 Hp Hi) as NI.
      destruct (Z_le_gt_dec q (ptr_addr L2 p + i)) as [D1|D1];
        [destruct (Z_lt_ge_dec (ptr_addr L2 p + i) (q + size)) as [D2|D2]|].
      + apply (present_of_writable_out B SEGS m5 (ptr_addr L2 p + i) ltac:(lia) NI).
        pose proof DST5 as [_ (_ & _ & W)].
        assert (Hb : 0 <= ptr_addr L2 p + i - q < Z.of_nat (cells_size [CB (length x) x]))
          by (cbn [cells_size csize]; rewrite Nat.add_0_r, LX; lia).
        specialize (W (ptr_addr L2 p + i - q) Hb).
        replace (q + (ptr_addr L2 p + i - q)) with (ptr_addr L2 p + i) in W by ring. exact W.
      + apply (munch_present _ _ _ _ MU5); [lia | apply OUT5; [lia | intros Hr; apply NI; apply grec_img; lia | lia] | exact Hpr].
      + apply (munch_present _ _ _ _ MU5); [lia | apply OUT5; [lia | intros Hr; apply NI; apply grec_img; lia | lia] | exact Hpr]. }
  assert (NR5 : rw_cells rsegs m5 0x343c0 [C4 w]).
  { apply (rw_cells_munch _ m4 m5 _ _ NR4 MU5). intros i Hi. cbn in Hi. split; [lia|]. apply OUT5; [lia | lia |].
    intros Hr. apply (FR_img (0x343c0 + i - q)); [lia|]. replace (q + (0x343c0 + i - q)) with (0x343c0 + i) by ring.
    apply grec_img. lia. }
  assert (GOT5 : forall i, 0 <= i < 8 -> mbyte rsegs m5 (0x22d40 + i) = mbyte rsegs mem (0x22d40 + i)).
  { intros i Hi. rewrite <- (GOT4 i Hi). apply (munch_mbyte _ _ _ _ _ MU5); [lia|]. apply OUT5; [lia | lia |].
    intros Hr. apply (FR_img (0x22d40 + i - q)); [lia|]. replace (q + (0x22d40 + i - q)) with (0x22d40 + i) by ring.
    exact (got_img i Hi). }
  assert (RPC : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite RPC.
  apply SR_ret.
  assert (EXS : match x with [] => None | _ :: _ => Some x end = Some x) by (apply match_nonempty; lia).
  apply (ss_end L2 A2 R5 m5 md4 (Some (q, size)) q bl1 bl2 w RJ5).
  - apply preserved_parts; [exact KR5 | | | |]; pres_reg_tac X5.
  - rewrite (getr_of_eqv _ _ 10 X5 eq_refl). simp_regs. reflexivity.
  - exact NR5.
  - exact W4.
  - change (r_reply (fst (socket_send_m R x))) with (match x with [] => None | _ :: _ => Some x end). rewrite EXS.
    destruct (c8_bytes2 m5 0x343c8 _ _ RP5) as [P1 P2].
    unfold reply_at. cbn [fst snd].
    split; [exact P1|]. split; [rewrite LX; exact P2|]. split; [lia|].
    split; [intros E; rewrite E in LX; cbn in LX; lia|].
    split; [exact INB4|]. split; [lia|]. split; [exact (cb_bytes m5 q _ x DST5) | lia].
  - intros p1 Hp1. cbn [oblk In] in Hp1. destruct Hp1 as [<-|[]]. cbn [fst snd].
    split; [apply fresh_apart; [exact FR_img | exact Hs | unfold G_REC; lia | unfold G_REC, REC_SIZE; lia | unfold REC_SIZE; lia]|].
    split; [apply fresh_apart; [exact FR_img | exact Hs | unfold REC_SC; lia | unfold REC_SC, SC_SIZE; lia | unfold SC_SIZE; lia]|].
    intros pn Hpn E.
    pose proof (nonrep_pos pn Hpn) as Hpos.
    pose proof (kept_blk bl1 bl2 pn BLA (nonrep_blk pn Hpn) (nonrep_notrep pn Hpn)) as Hk.
    rewrite <- BL1, BLK4b in Hk. destruct pn as [p k].
    pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ PM4 BLK4a Hk) as D. cbn [fst snd] in *. lia.
  - exact BLA.
  - intros H. lia.
  - intros _. split; [reflexivity|]. split; [exists b1', b2'; split; [exact BLK4a | rewrite <- BLK4b; exact BL1]|].
    split; [exact FRESH | exact AL16].
  - exact RA5.
  - exact GOT5.
  - intros _. exact INIT4.
  - rewrite <- (sb_shift_trans b A A1 A2), <- EB1, <- (sb_shift_add b1 L1 A1 L2 A2 b1' b2' q size BLK4a BLK4b).
    replace (0 <? size) with true by (symmetry; apply Z.ltb_lt; exact Hs). apply sb_malloc_mono. exact BLE.
  - rewrite <- (sb_shift_trans b A A1 A2), <- EB1, <- (sb_shift_add b1 L1 A1 L2 A2 b1' b2' q size BLK4a BLK4b).
    exact RES4.
Qed.

Lemma ss_main : SR rsegs (mkCfg (mkst regs (Z_to_bv 64 SOCKET_SEND) mem (seg_rom rsegs)) md) SPOST.
Proof.
  eapply SR_bind; [exact ss_stage1|]. intros c HP.
  destruct (Z_le_gt_dec size 0) as [Hs|Hs]; [exact (ss_stage2n c HP Hs) | exact (ss_stage2p c HP ltac:(lia))].
Qed.

End Run.

Section Main.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GRD : ms_guard B = 0x54730.
Hypothesis FGI : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis FGO : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTXO : ctx_owned B API.
Hypothesis XM : xmalloc_contract B API.
Hypothesis FREE : free_contract B API.
Hypothesis FREE_NULL : free_null_contract B.
Hypothesis MEMCPY : memcpy_contract.

Theorem socket_send_holds : socket_send_contract B API.
Proof.
  unfold socket_send_contract.
  intros L A regs mem md buf size x R O b PRE A11 A12 HSZ REP NRP SZP SZN RA F18 RES.
  rewrite SEGS in REP, SZP, RA, F18. rewrite SEGS.
  destruct REP as (Q & HREP & HO).
  pose proof (aa_laws API) as LAWS.
  assert (RF : exists r0 rsw, Mem.bytes_at rsegs mem (G_REC + OFF_REPLY) (Mem.le8 (Z_to_bv 64 r0)) /\
      Mem.bytes_at rsegs mem (G_REC + OFF_REPLY_SIZE) (Mem.le8 rsw) /\ 0 <= r0 < 2 ^ 64 /\
      match l_reply Q with None => r0 = 0 | Some pn => fst pn = r0 /\ In pn (blocks L A) /\ 1 <= snd pn end).
  { pose proof alloc_ceiling_val as AC.
    pose proof HREP as (_ & _ & _ & HPR & _ & _). unfold reply_at in HPR.
    destruct (r_reply R) as [x0|]; destruct (l_reply Q) as [[p0 k0]|]; try contradiction.
    - destruct HPR as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). cbn [fst snd] in *.
      assert (K1 : 1 <= k0) by (destruct x0 as [|c0 x0]; [exfalso; exact (P4 eq_refl) | cbn [length] in P6; lia]).
      destruct (block_facts B _ LAWS _ _ _ _ _ _ 0 (proj1 PRE) P5 ltac:(lia)) as (_ & H4 & H5 & _).
      exists p0, (Z_to_bv 64 (Z.of_nat (length x0))).
      split; [exact P1|]. split; [exact P2|]. split; [lia|]. split; [reflexivity|]. split; [exact P5 | exact K1].
    - destruct HPR as [P1 P2]. exists 0, (Z_to_bv 64 0).
      split; [exact P1|]. split; [exact P2|]. split; [lia | reflexivity]. }
  destruct RF as (r0 & rsw & RPB & RSB & R0R & RPQ).
  eapply SR_mono; [eapply (ss_main B API); eassumption|].
  intros c' H. unfold SPOST in H. exact H.
Qed.

End Main.
