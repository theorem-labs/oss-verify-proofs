(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 615 of its 727 lines of code are new or changed and 899 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F35.v, with its module names changed; 625 of its 686 lines of code are new or changed and 666 lines of the source are left out. *)
(* Segment F28 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, libreac v1.9.0 image B): the port-slot loops of the
   inlined check_ports, slot-plan-asan-ubsan.md section 2 row F28 (no external callee, twin Q05/Q06). The segment
   proved here runs from the moved loop head 0x8292c (the official Inv_B8292c_at of lib/B/Prog/SlotInv.v, whose
   body carries F28GAP since adopt 12) to 0x82aa4 (the official Inv_B82aa4_at, F29's entry); 0x828f0-0x82928 is the
   loop prologue, which F27 owns. The v1.9.0 move of the patched-image seg_F28 (a working branch 4131ff88f40,
   patched 0x828bc-0x82a3c): the loop is the patched one shifted by 0x70; the tail reads the ports words through
   s5 = fr + 128 (FTL's position 1) where the patched tail reloaded [A+248], and the first pointer from [A+136]
   (patched [A+144]).

   The loop (plan 1.3 loop 10, head 0x8292c, latch 0x829b8 `bnez a7`) makes 12 turns over the port codes
   pbs[8 + i] = the bytes at blk + 8 + i = Phi + 26 + i, i = 0 .. 11, with

     a0 = a4 = Phi + 26 + i   the cursor,            a7 = 12 - i    the turns left,
     a2 = n_in  so far,       a1 = n_out so far,     a3 = the empty count so far,
     a5 = the first unknown code so far (0 = none),  a6 = -8 - blk  the room,  t3 = 12.

   Per turn:
     0x8292c add t0,a6,a7 ; 0x82930 beq t0,t3,82fa0     -- trap row T56, NOT taken: t0 = 2^64 - 14 - Phi - i,
                                                           which is at least 25 because Phi + 50 <= 2^64.
     0x82934-0x82940  the instrumented check of the byte at a0: `srli t0,a0,3; add t0,t0,s10; lb t0,0(t0);
                      bnez t0,829c0`.  The byte is addressable (HB with 50 <= flen), so its shadow byte k has
                      k = 0 (fall through) or (a0 mod 8) < k; in the second arm the slow block 0x829c0
                      `andi t1,a0,7; bge t1,t0,8304c` does not reach the error path (report row 8304c) and
                      `j 82944` rejoins.  Both arms reach 0x82944 with t1 generalised.
     0x82944 lbu t0,0(a4)                               -- the code c_i.
     0x82948-0x8295c  a2 += [c_i in {0, 2}] with the int-overflow test T57 (`add` vs `addw`), NOT taken.
     0x82960-0x82974  a1 += [c_i = 1], test T58, NOT taken.
     0x82978-0x8298c  a3 += [c_i = 3], test T59, NOT taken.
     0x82990-0x829a4  a5 := if c_i >= 4 and a5 = 0 then c_i else a5 (the first unknown code).
     0x829a8-0x829b8  a7--, a0++, a4++, a5 := t0, back edge.
   The exit `j 829cc` (0x829bc) leaves a2 = n_in, a1 = n_out, a3 = the empty count, a5 = t0 = the first
   unknown code, all over the full 12 codes.

   The tail 0x829cc-0x82aa0 reads the three ports words through s5 = fr + 128 (4 n_in, 4 n_out, 16 pbs[7]; the
   bundle PORTS) and the first byte at [A+136] = fr + 160 (FIRSTb), and checks them against the loop's counts.
   Its seven FAIL branches (829d4 829e4 829f4 82a40 82a58 82a70 82aa0) are not taken because PORTS and FIRSTb
   hold the very values the loop computed: the two words are multiples of 4, the first byte is the loop's first
   unknown code, 4 (n_in + n_out + nunk + empty) = 48 since every code falls in exactly one class, and
   16 pbs[7] is 16 times the byte at blk + 7.  Its five trap branches (82a00 82a10 82a20 82a34 82a50, with 82a68
   and 82a80) are not taken: every term is in [0, 48] and Phi + 25 >= 26.  The last instrumented check (0x82a8c,
   on blk + 7) converges through the slow block 0x82e28 `andi a3,a0,7; bge a3,a2,830cc; j 82a98`.

   The segment writes no memory and makes no call: it keeps every register but t0, t1, t2 and a0-a7, so FRA
   moves by sl_fra_move, ENT by ent_mat, and the exit's LK, FTL, FTURN and IFS (S j) by F27's f27_exit. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import F27.
Import ListNotations.
(* lib.B.Prog's chain loads lib/Reusable/YK11.v, so the short name YK11 would resolve to that copy; this file's
   registers, mkst and FPState must be image B's, as SlotInv's and Tac_slot's are. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Mem.
Module ULPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.PropExec.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

(* ========================= the port-code model ========================= *)

(* RcLeaf and RcPorts index the same byte of the same list. *)
Lemma f28_bt_u8 : forall bs i, RcLeaf.bt bs i = RcPorts.rc_u8 bs i.
Proof. intros bs i. reflexivity. Qed.

Lemma f28_ubyte : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range _ b) as H. unfold bv_modulus in H. exact H. Qed.

(* The 8-bit twin of MState.Z_to_bv_bv_unsigned. *)
Lemma f28_zb_id : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma f28_u8_range : forall bs i, 0 <= RcPorts.rc_u8 bs i < 256.
Proof. intros bs i. unfold RcPorts.rc_u8. apply f28_ubyte. Qed.

(* The fourth class of a port code: the empty slots (code 3).  reac_ctrl's check_ports counts them inline; the
   model keeps only n_in, n_out and the unknown count, so the count lives here. *)
Fixpoint f28_nemp (bs : list byte) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => f28_nemp bs k' + (if RcPorts.rc_u8 bs (8 + k')%nat =? 3 then 1 else 0)
  end.

Lemma f28_cnt_bound : forall f bs k, 0 <= RcLeaf.cnt f bs k <= Z.of_nat k.
Proof.
  intros f bs k. induction k as [|k IH]; cbn [RcLeaf.cnt]; [lia|].
  destruct (f (RcLeaf.bt bs (8 + k)%nat)); lia.
Qed.

Lemma f28_nemp_bound : forall bs k, 0 <= f28_nemp bs k <= Z.of_nat k.
Proof.
  intros bs k. induction k as [|k IH]; cbn [f28_nemp]; [lia|].
  destruct (RcPorts.rc_u8 bs (8 + k)%nat =? 3); lia.
Qed.

Lemma f28_nunk_bound : forall bs k, 0 <= RcPorts.pu_nunk bs k <= Z.of_nat k.
Proof.
  intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_nunk]; [lia|].
  destruct (4 <=? RcPorts.rc_u8 bs (8 + k)%nat); lia.
Qed.

(* Every code falls in exactly one of the four classes, so the four counts add up to the number of slots. *)
Lemma f28_total : forall bs k,
  RcLeaf.cnt RcLeaf.is_in bs k + RcLeaf.cnt RcLeaf.is_out bs k + f28_nemp bs k + RcPorts.pu_nunk bs k
  = Z.of_nat k.
Proof.
  intros bs k. induction k as [|k IH]; [reflexivity|].
  cbn [RcLeaf.cnt f28_nemp RcPorts.pu_nunk].
  rewrite (f28_bt_u8 bs (8 + k)%nat).
  pose proof (f28_u8_range bs (8 + k)%nat) as Hr.
  change (RcLeaf.is_in (RcPorts.rc_u8 bs (8 + k)%nat))
    with ((RcPorts.rc_u8 bs (8 + k)%nat =? 0) || (RcPorts.rc_u8 bs (8 + k)%nat =? 2))%bool.
  change (RcLeaf.is_out (RcPorts.rc_u8 bs (8 + k)%nat)) with (RcPorts.rc_u8 bs (8 + k)%nat =? 1).
  destruct (Z.eqb_spec (RcPorts.rc_u8 bs (8 + k)%nat) 0) as [E0|E0];
  destruct (Z.eqb_spec (RcPorts.rc_u8 bs (8 + k)%nat) 2) as [E2|E2];
  destruct (Z.eqb_spec (RcPorts.rc_u8 bs (8 + k)%nat) 1) as [E1|E1];
  destruct (Z.eqb_spec (RcPorts.rc_u8 bs (8 + k)%nat) 3) as [E3|E3];
  destruct (Z.leb_spec 4 (RcPorts.rc_u8 bs (8 + k)%nat)) as [E4|E4];
  cbn [orb]; lia.
Qed.

(* The first unknown code is 0 exactly while no slot is unknown, and is a code of 4 .. 255 after one is. *)
Lemma f28_first_nunk : forall bs k,
  (RcPorts.pu_nunk bs k = 0 /\ RcPorts.pu_first bs k = 0) \/
  (0 < RcPorts.pu_nunk bs k /\ 4 <= RcPorts.pu_first bs k < 256).
Proof.
  intros bs k. induction k as [|k IH].
  - left. split; reflexivity.
  - cbn [RcPorts.pu_nunk RcPorts.pu_first].
    pose proof (f28_u8_range bs (8 + k)%nat) as Hr.
    pose proof (f28_nunk_bound bs k) as Hb.
    destruct (Z.leb_spec 4 (RcPorts.rc_u8 bs (8 + k)%nat)) as [E4|E4].
    + destruct IH as [(Hz & Hf)|(Hp & Hf)].
      * rewrite Hz. cbn [Z.eqb andb]. right.
        replace (4 <=? RcPorts.rc_u8 bs (8 + k)%nat) with true by (symmetry; apply Z.leb_le; lia).
        lia.
      * replace (RcPorts.pu_nunk bs k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [andb]. right. lia.
    + replace (4 <=? RcPorts.rc_u8 bs (8 + k)%nat) with false by (symmetry; apply Z.leb_gt; lia).
      rewrite andb_false_r.
      destruct IH as [(Hz & Hf)|(Hp & Hf)]; [left | right]; lia.
Qed.

(* The machine form of the pu_first step: the code continues the run when the slot is known (c < 4) or when a
   first unknown code was already found (a5 <> 0). *)
Lemma f28_first_step : forall bs k,
  RcPorts.pu_first bs (S k) =
    (if ((RcPorts.rc_u8 bs (8 + k)%nat <? 4) || negb (RcPorts.pu_first bs k =? 0))%bool
     then RcPorts.pu_first bs k else RcPorts.rc_u8 bs (8 + k)%nat).
Proof.
  intros bs k. cbn [RcPorts.pu_first].
  pose proof (f28_u8_range bs (8 + k)%nat) as Hr.
  destruct (f28_first_nunk bs k) as [(Hz & Hf)|(Hp & Hf)].
  - rewrite Hz, Hf. cbn [Z.eqb andb negb orb].
    destruct (Z.ltb_spec (RcPorts.rc_u8 bs (8 + k)%nat) 4) as [E|E].
    + replace (4 <=? RcPorts.rc_u8 bs (8 + k)%nat) with false by (symmetry; apply Z.leb_gt; lia).
      reflexivity.
    + replace (4 <=? RcPorts.rc_u8 bs (8 + k)%nat) with true by (symmetry; apply Z.leb_le; lia).
      reflexivity.
  - replace (RcPorts.pu_nunk bs k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (RcPorts.pu_first bs k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite andb_false_l, orb_true_r. reflexivity.
Qed.

(* 0x828dc `andi a2,t0,253` then `seqz`: the code is an input slot exactly when c & 0xfd = 0. *)
Lemma f28_land253 : forall c, 0 <= c < 256 -> (Z.land c 253 =? 0) = RcLeaf.is_in c.
Proof.
  intros c Hc.
  assert (E : forallb (fun z => Bool.eqb (Z.land z 253 =? 0) (RcLeaf.is_in z))
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in E.
  assert (Hin : In c (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
  pose proof (E c Hin) as H. cbv beta in H. apply Bool.eqb_prop in H. exact H.
Qed.

(* reac_ports_parse and reac_ports_unknown accept the same blocks (plain twin b7_decl_same). *)
Lemma f28_decl_same : forall bs, RcLeaf.decl bs = RcPorts.pu_decl bs.
Proof. intros bs. reflexivity. Qed.

(* With r = 0 the two ports counts are the model's slot counts over the 12 codes. *)
Lemma f28_unk_rp0 : forall inp j, t_rp inp j = 0 ->
  t_unk inp j = 4 * RcPorts.pu_nunk (t_pbs inp j) 12 /\
  t_first inp j = RcPorts.pu_first (t_pbs inp j) 12.
Proof.
  intros inp j H. unfold t_rp, t_unk, t_first in *. rewrite <- f28_decl_same.
  destruct (RcLeaf.decl (t_pbs inp j)); [|discriminate H]. split; reflexivity.
Qed.

(* n_in / n_out are the counts over the 12 codes.  Proved over an abstract list and used by rewriting: converting
   n_in (t_pbs ..) into cnt is_in (t_pbs ..) 12 in place makes the kernel unfold the slot model (minutes). *)
Lemma f28_n_in : forall bs, RcLeaf.n_in bs = RcLeaf.cnt RcLeaf.is_in bs 12.
Proof. intros bs. reflexivity. Qed.

Lemma f28_n_out : forall bs, RcLeaf.n_out bs = RcLeaf.cnt RcLeaf.is_out bs 12.
Proof. intros bs. reflexivity. Qed.

(* ========================= byte, shadow and word helpers ========================= *)

Lemma f28_rd1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (ULMem.wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (ULMem.bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.

Lemma f28_rd4 : forall m a v, u32 m a v -> ov_read_bytes rsegs m (ULMem.wa a) 4 = Some (ULMem.le4 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold u32 in H.
  pose proof (ULMem.bytes_at_ov_read rsegs m a _ 0 4 H ltac:(rewrite ULMem.length_le4; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH.
  rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by (rewrite ULMem.length_le4; lia). exact HH.
Qed.

Lemma f28_rd8 : forall m a v, q64 m a v -> ov_read_bytes rsegs m (ULMem.wa a) 8 = Some (ULMem.le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold q64 in H.
  pose proof (ULMem.bytes_at_ov_read rsegs m a _ 0 8 H ltac:(rewrite ULMem.length_le8; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH.
  rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by (rewrite ULMem.length_le8; lia). exact HH.
Qed.

(* `lbu` zero-extends: zxb b is the word of the unsigned byte value. *)
Lemma f28_zxb_eq : forall b : byte, ULMem.zxb b = Z_to_bv 64 (bv_unsigned b).
Proof. intros b. reflexivity. Qed.

Lemma f28_zxb_lit : forall v, 0 <= v < 256 -> ULMem.zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. rewrite f28_zxb_eq. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

(* The `lw` at 0x82960 / 0x82970 / 0x82a2c sign-extends the low 32 bits; a value below 2^31 is kept. *)
Lemma f28_sx32_small : forall v, 0 <= v < 2 ^ 31 -> ULMem.sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold ULMem.sx32. rewrite (MState.unsigned_lit v) by lia. f_equal.
  unfold bv_swrap. change (bv_half_modulus 32) with (2 ^ 31). unfold bv_wrap.
  change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_small by lia. lia.
Qed.

(* The `addw` / `addiw` / `slliw` results: a value in [-2^31, 2^31) is its own 32-bit sign wrap. *)
Lemma f28_swrap_small : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_swrap 32 v = v.
Proof.
  intros v Hv. unfold bv_swrap. change (bv_half_modulus 32) with (2 ^ 31). unfold bv_wrap.
  change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_small by lia. lia.
Qed.

(* Two spill bases equal as 64-bit values give the same word address at every offset (F27's f27_wa_shift). *)
Lemma f28_wa_shift : forall x y d, Z_to_bv 64 x = Z_to_bv 64 y -> ULMem.wa (x + d) = ULMem.wa (y + d).
Proof.
  intros x y d E. unfold ULMem.wa. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
  assert (E' : x mod 2 ^ 64 = y mod 2 ^ 64) by exact E.
  apply bv_eq. rewrite !Z_to_bv_unsigned.
  change ((x + d) mod 2 ^ 64 = (y + d) mod 2 ^ 64).
  rewrite Zplus_mod, E', <- Zplus_mod. reflexivity.
Qed.

(* ---- The branch conditions and the ALU results the runs meet, in plain form. ---- *)

Lemma f28_eqb_true : forall x y, x = y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros x y ->. apply bv_eqb_refl. Qed.

(* The trap test T56 (0x828c0 beq t0,t3): x = -14 - Phi - i is negative and x + 2^64 is not 12. *)
Lemma f28_eqb_ne : forall x y, - 2 ^ 64 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x <> y -> x + 2 ^ 64 <> y ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy H1 H2. unfold bv_eqb. rewrite (MState.unsigned_lit y) by lia.
  rewrite MState.unsigned_lit_wrap. apply Z.eqb_neq. intro E.
  destruct (Z.leb_spec 0 x) as [L|L].
  - rewrite Z.mod_small in E by lia. lia.
  - assert (E2 : x mod 2 ^ 64 = x + 2 ^ 64).
    { rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
    lia.
Qed.

(* `seqz` (sltiu x,1) of a value in [-2^63, 2^63). *)
Lemma f28_seqz : forall x, - 2 ^ 63 <= x < 2 ^ 63 ->
  ULPE.v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 (if x =? 0 then 1 else 0).
Proof.
  intros x Hx. assert (HP : 2 ^ 64 = 2 * 2 ^ 63) by reflexivity.
  unfold ULPE.v_sltiu. change (bv_wrap 64 1) with 1.
  rewrite MState.unsigned_lit_wrap.
  destruct (Z.eqb_spec x 0) as [E|E].
  - subst x. reflexivity.
  - replace (x mod 2 ^ 64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge.
    destruct (Z.leb_spec 0 x) as [L|L].
    + rewrite Z.mod_small by lia. lia.
    + rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* 0x828dc-0x828e0 `andi a2,t0,253 ; seqz t2,a2`: 1 exactly for an input slot. *)
Lemma f28_seqz_in : forall c, 0 <= c < 256 ->
  ULPE.v_sltiu (Z_to_bv 64 (Z.land c 253)) 1 = Z_to_bv 64 (if RcLeaf.is_in c then 1 else 0).
Proof.
  intros c Hc. assert (HP : 2 ^ 63 = 9223372036854775808) by reflexivity.
  assert (E : forallb (fun z => ((0 <=? Z.land z 253) && (Z.land z 253 <=? 253))%bool)
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in E.
  assert (Hin : In c (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
  pose proof (E c Hin) as B. cbv beta in B. apply andb_prop in B as (B1 & B2).
  apply Z.leb_le in B1. apply Z.leb_le in B2.
  rewrite f28_seqz by lia. rewrite (f28_land253 c Hc). reflexivity.
Qed.

(* 0x828f0 / 0x828f8 `addi t1,t0,-1 ; seqz t1,t1`: 1 exactly for an output slot. *)
Lemma f28_seqz_m1 : forall c, 0 <= c < 256 ->
  ULPE.v_sltiu (Z_to_bv 64 (c + -1)) 1 = Z_to_bv 64 (if RcLeaf.is_out c then 1 else 0).
Proof.
  intros c Hc. assert (HP : 2 ^ 63 = 9223372036854775808) by reflexivity.
  rewrite f28_seqz by lia. unfold RcLeaf.is_out.
  destruct (Z.eqb_spec (c + -1) 0); destruct (Z.eqb_spec c 1); try reflexivity; lia.
Qed.

(* 0x82908 / 0x82910 `addi t1,t0,-3 ; seqz t1,t1`: 1 exactly for an empty slot. *)
Lemma f28_seqz_m3 : forall c, 0 <= c < 256 ->
  ULPE.v_sltiu (Z_to_bv 64 (c + -3)) 1 = Z_to_bv 64 (if c =? 3 then 1 else 0).
Proof.
  intros c Hc. assert (HP : 2 ^ 63 = 9223372036854775808) by reflexivity.
  rewrite f28_seqz by lia.
  destruct (Z.eqb_spec (c + -3) 0); destruct (Z.eqb_spec c 3); try reflexivity; lia.
Qed.

(* 0x82920 `sltiu t1,t0,4`: the code is known (below 4). *)
Lemma f28_sltiu4 : forall c, 0 <= c < 256 ->
  ULPE.v_sltiu (Z_to_bv 64 c) 4 = Z_to_bv 64 (if c <? 4 then 1 else 0).
Proof.
  intros c Hc. assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold ULPE.v_sltiu. change (bv_wrap 64 4) with 4.
  rewrite (MState.unsigned_lit c) by lia. destruct (c <? 4); reflexivity.
Qed.

(* 0x82928 `snez t2,t2` (sltu t2,x0,t2): a first unknown code was found. *)
Lemma f28_snez : forall f, 0 <= f < 256 ->
  ULPE.v_sltu (Z_to_bv 64 0) (Z_to_bv 64 f) = Z_to_bv 64 (if f =? 0 then 0 else 1).
Proof.
  intros f Hf. assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold ULPE.v_sltu, ULPE.c_ltu, bv_ltu.
  rewrite (MState.unsigned_lit f) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.eqb_spec f 0) as [E|E].
  - subst f. reflexivity.
  - replace (0 <? f) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* 0x8292c `or t1,t2,t1`: the run goes on with the old first code exactly when the f28_first_step test holds. *)
Lemma f28_or : forall f c,
  Z.lor (if f =? 0 then 0 else 1) (if c <? 4 then 1 else 0) =
  (if ((c <? 4) || negb (f =? 0))%bool then 1 else 0).
Proof. intros f c. destruct (f =? 0), (c <? 4); reflexivity. Qed.

Lemma f28_land255 : forall f, 0 <= f < 256 -> Z.land f 255 = f.
Proof.
  intros f Hf. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small.
  change (2 ^ 8) with 256. lia.
Qed.

(* 0x82964 `andi a0,a4,3`: a multiple of 4 has no low bits. *)
Lemma f28_land43 : forall n, Z.land (4 * n) 3 = 0.
Proof.
  intros n. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.

(* 0x82974-0x82978 `or a5,a0,s7 ; andi a5,a5,3` on two multiples of 4 below 49 (checked over 13 x 13 values). *)
Lemma f28_lor44 : forall a b, 0 <= a <= 12 -> 0 <= b <= 12 ->
  0 <= Z.lor (4 * a) (4 * b) < 64 /\ Z.land (Z.lor (4 * a) (4 * b)) 3 = 0.
Proof.
  intros a b Ha Hb.
  assert (E : forallb (fun x => forallb (fun y =>
      ((0 <=? Z.lor (4 * x) (4 * y)) && (Z.lor (4 * x) (4 * y) <? 64) &&
       (Z.land (Z.lor (4 * x) (4 * y)) 3 =? 0))%bool)
      (map Z.of_nat (seq 0 13))) (map Z.of_nat (seq 0 13)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in E.
  assert (Ha' : In a (map Z.of_nat (seq 0 13))).
  { apply in_map_iff. exists (Z.to_nat a). split; [lia|]. apply in_seq. lia. }
  assert (Hb' : In b (map Z.of_nat (seq 0 13))).
  { apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia. }
  pose proof (E a Ha') as E1. cbv beta in E1. rewrite forallb_forall in E1. pose proof (E1 b Hb') as E2.
  cbv beta in E2. apply andb_prop in E2 as (E3 & E4). apply andb_prop in E3 as (E5 & E6).
  apply Z.leb_le in E5. apply Z.ltb_lt in E6. apply Z.eqb_eq in E4.
  split; [split; assumption | exact E4].
Qed.

(* 0x829b4 / 0x829e4 / 0x829fc `srliw x,x,30` of a small count plus 2^29: 0, so the trap is not taken. *)
Lemma f28_srliw30 : forall x, 0 <= x < 2 ^ 30 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 x) 30)) = Z_to_bv 64 0.
Proof.
  intros x Hx. assert (HP : 2 ^ 32 = 4 * 2 ^ 30) by reflexivity.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma f28_shl2 : forall x, Z.shiftl x 2 = 4 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia. Qed.

Lemma f28_shl4 : forall x, Z.shiftl x 4 = 16 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. lia. Qed.

Lemma f28_ite10 : forall b : bool, 0 <= (if b then 1 else 0) <= 1.
Proof. intros []; cbn; lia. Qed.

Lemma f28_ite01 : forall b : bool, 0 <= (if b then 0 else 1) <= 1.
Proof. intros []; cbn; lia. Qed.

(* One instrumented 1-byte shadow read of an addressable byte X: the shadow byte b is readable at
   (X >> 3) + ASAN_K and passes the check (b = 0, or X mod 8 < b).  (Image-B twin of F17's f17_shadow.) *)
Lemma f28_shadow : forall m X, addressable m X 1 ->
  exists b : byte, ov_read_bytes rsegs m (ULMem.wa (Z.shiftr X 3 + ASAN_K)) 1 = Some [b]
    /\ (bv_signed b = 0 \/ X mod 8 < bv_signed b) /\ -128 <= bv_signed b < 128.
Proof.
  intros m X HA. destruct (meta_byte m X 1 HA ltac:(lia)) as (b & RO & OK & IS).
  exists b. split; [| split].
  - pose proof (cells_at_read rsegs m (Z.shiftr X 3 + ASAN_K) [C1 b] 0%nat (C1 b) RO eq_refl) as H.
    cbn [csize cbytes] in H. rewrite Z.add_0_r in H. exact H.
  - destruct OK as [H|H]; [left; exact H | right; lia].
  - pose proof (sbyte_range b); lia.
Qed.

Lemma f28_nth_firstn : forall (l : list byte) N i d, (i < N)%nat -> nth i (firstn N l) d = nth i l d.
Proof.
  induction l as [|x l IH]; intros N i d Hi.
  - rewrite firstn_nil. reflexivity.
  - destruct N as [|N]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma f28_nth_skipn : forall (l : list byte) K i d, nth i (skipn K l) d = nth (K + i) l d.
Proof.
  induction l as [|x l IH]; intros K i d.
  - rewrite skipn_nil, !nth_overflow by (cbn; lia). reflexivity.
  - destruct K as [|K]; [reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.

(* The 20 ports bytes are a prefix of the 32 block bytes. *)
Lemma f28_pbs_blk : forall inp j i, (i < 20)%nat ->
  nth i (t_pbs inp j) (Z_to_bv 8 0) = nth i (t_blk inp j) (Z_to_bv 8 0).
Proof.
  intros inp j i Hi. unfold t_pbs, t_blk, bsl.
  rewrite !f28_nth_firstn by lia. reflexivity.
Qed.

Lemma f28_blk_length : forall inp j, 50 <= t_len inp j -> length (t_blk inp j) = 32%nat.
Proof.
  intros inp j H. unfold t_blk, bsl, t_g.
  rewrite length_firstn, length_skipn, fr50_length. lia.
Qed.

(* The byte at a + t of a byte run at a. *)
Lemma f28_byte : forall m a bs t, (t < length bs)%nat -> LMem.bytes_at rsegs m a bs ->
  LMem.bytes_at rsegs m (a + Z.of_nat t) [nth t bs (Z_to_bv 8 0)].
Proof.
  intros m a bs t Ht (H0 & H1 & H2).
  split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
  cbn [nth]. replace (a + Z.of_nat t + Z.of_nat 0) with (a + Z.of_nat t) by lia.
  rewrite (H2 t ltac:(lia)).
  transitivity (Some (nth t bs (Z_to_bv 8 0))); [apply nth_error_nth'; exact Ht | reflexivity].
Qed.

(* mkR_of regs is definitionally the explicit 31-slot register map; exposing it lets `step` read a slot we have
   rewritten to a concrete value. *)
Lemma f28_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a known register slot `getr regs r` to its carried concrete value, from H : rg regs r v. *)
Ltac f28_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* Keep the register values the step tactics leave in plain form `Z_to_bv 64 v`: drop a `bv_unsigned` of a
   literal word, a 32-bit sign wrap of a small value, `+ 0` and the shifts by 2 and 4 (bounds from the context). *)
Ltac f28_norm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (MState.unsigned_lit x) by lia
  | |- context [bv_swrap 32 ?x] => rewrite (f28_swrap_small x) by lia
  | |- context [Z.add ?x 0] => rewrite (Z.add_0_r x)
  | |- context [Z.shiftl ?x 2] => rewrite (f28_shl2 x)
  | |- context [Z.shiftl ?x 4] => rewrite (f28_shl4 x)
  end.

(* Replace the condition of the branch at the head of the goal by its value v: by computation (f28_brc), by the
   proof pf of `c = v` (f28_br), or, for a `bne` / `bnez` on two equal values, by f28_eqb_true (f28_nt). *)
Ltac f28_brc v :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v by (vm_compute; reflexivity); cbv_concl_iota
  end.
Ltac f28_br v pf :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v by (symmetry; pf); cbv_concl_iota
  end.
Ltac f28_nt := f28_br false ltac:(rewrite f28_eqb_true by lia; reflexivity).

(* The register map of a generalised slot is `bvmap_set k rr R`; the step tactics read a slot only out of an
   explicit tree, so fold the set back into the tree (k is a literal, so its key computes). *)
Ltac f28_fixmap :=
  lazymatch goal with
  | |- evt _ _ (MS (bvmap_set ?k ?v ?R) _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key k) in
      let R' := eval cbv beta iota delta [tset] in (tset p v R) in
      change (bvmap_set k v R) with R'
  end.

(* The instrumented check `lb k,0(x) ; bnez k,slow` of the byte Xe (F17's `converge`): the fast arm (k = 0) and the
   slow arm (Xe mod 8 < k: the slow block's `andi s,a,7 ; bge s,k,report` is not taken and its `j` rejoins) reach
   the fall-through `cont` with only the slow block's register `scratch` changed, so the goal becomes
   `forall rr, evt .. cont` with that register generalised (introduced). *)
Ltac f28_converge scratch Xe b OK BD :=
  match goal with
  | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?cont) ?fc ?rv ?m ?ro) =>
      let Gc := fresh "Gc" in
      enough (Gc : forall rr, evt segs Q (MS (bvmap_set scratch rr R) F cont fc rv m ro)) by
        (let K0 := fresh "K0" in
         destruct (Z.eqb_spec (bv_signed b) 0) as [K0|K0];
         [ match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (unfold sxb; rewrite K0; vm_compute; reflexivity) end;
           cbv_concl_iota;
           match goal with |- evt _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end
         | let Hmb := fresh "Hmb" in let Hlt := fresh "Hlt" in
           pose proof (Z.mod_pos_bound Xe 8 ltac:(lia)) as Hmb;
           assert (Hlt : Xe mod 8 < bv_signed b) by (destruct OK as [HH|HH]; [exfalso; apply K0; exact HH | lia]);
           match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with true by (unfold sxb; rewrite bv_eqb_lit by lia;
               replace (bv_signed b =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity) end;
           cbv_concl_iota; step; step;
           match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
             replace c with false by (rewrite (MState.unsigned_lit Xe) by lia;
               rewrite land7 by lia; rewrite lts_sxb by lia;
               replace (Xe mod 8 <? bv_signed b) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity) end;
           cbv_concl_iota; step;
           match goal with |- evt _ _ (MS ?R2 _ _ _ _ _ _) => exact (Gc (Sem.reg_get R2 scratch)) end ])
  end; intro; f28_fixmap.

(* ========================= the two machine runs ========================= *)

(* The 12-turn port-slot loop, by the number k of turns left.  At the head 0x8292c with the cursor at
   Phi + 26 + i (i + k = 12) and the four partial counts, the run reaches 0x829cc with the counts over all 12
   codes, t0 = a5 = the first unknown code and a7 = 0, and continues there by the last premise.  Each turn reads
   the byte Phi + 26 + i and its shadow byte ((Phi + 26 + i) >> 3) + 0x7fff8000; it writes no memory.
   Touched address ranges: [Phi + 26, Phi + 38) and their shadow bytes. *)
Lemma f28_loop : forall (k i : nat) (Q : _ -> Prop)
  (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s11 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (pbs : list byte),
  (i + k = 12)%nat -> (0 < k)%nat -> 0 < phi -> phi + 50 <= 2 ^ 64 ->
  (forall t, (t < 12)%nat ->
     bytes_at rsegs m (phi + 26 + Z.of_nat t) [nth (8 + t)%nat pbs (Z_to_bv 8 0)]) ->
  (forall t, (t < 12)%nat -> addressable m (phi + 26 + Z.of_nat t) 1) ->
  (forall t1' t2' : word,
     evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 (RcPorts.pu_first pbs 12)) t1' t2' s0 s1
          (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out pbs 12))
          (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in pbs 12)) (Z_to_bv 64 (f28_nemp pbs 12))
          (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 (RcPorts.pu_first pbs 12))
          (Z_to_bv 64 (-8 - (phi + 18))) (Z_to_bv 64 0) s2 s3 s4 s5 s6 s7 s8 s9
          (Z_to_bv 64 ASAN_K) s11 (Z_to_bv 64 12) t4 t5 t6)
        F (Z_to_bv 64 0x829cc) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
       (Z_to_bv 64 (phi + 26 + Z.of_nat i)) (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_out pbs i))
       (Z_to_bv 64 (RcLeaf.cnt RcLeaf.is_in pbs i)) (Z_to_bv 64 (f28_nemp pbs i))
       (Z_to_bv 64 (phi + 26 + Z.of_nat i)) (Z_to_bv 64 (RcPorts.pu_first pbs i))
       (Z_to_bv 64 (-8 - (phi + 18))) (Z_to_bv 64 (12 - Z.of_nat i)) s2 s3 s4 s5 s6 s7 s8 s9
       (Z_to_bv 64 ASAN_K) s11 (Z_to_bv 64 12) t4 t5 t6)
     F (Z_to_bv 64 0x8292c) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros i Q ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s11 t4 t5 t6
    F fc m phi pbs Hik Hk Hphi0 Hphi50 HB HA HQ; [lia|].
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
  assert (HP31 : 2 ^ 31 = 2147483648) by reflexivity.
  assert (Hi : (i < 12)%nat) by lia.
  pose proof (f28_rd1 m _ _ (HB i Hi)) as RB.
  destruct (f28_shadow m (phi + 26 + Z.of_nat i) (HA i Hi)) as (b & RS & OK & BD).
  pose proof (f28_cnt_bound RcLeaf.is_in pbs i) as Bin.
  pose proof (f28_cnt_bound RcLeaf.is_out pbs i) as Bout.
  pose proof (f28_nemp_bound pbs i) as Bemp.
  assert (Bfst : 0 <= RcPorts.pu_first pbs i < 256)
    by (destruct (f28_first_nunk pbs i) as [(_ & E)|(_ & E)]; lia).
  (* 0x8292c add t0,a6,a7 ; 0x82930 beq t0,t3,82fa0 (trap T56): t0 = 2^64 - 14 - Phi - i is not 12 *)
  step. step. f28_br false ltac:(apply f28_eqb_ne; lia).
  (* 0x82934 srli t0,a0,3 ; add t0,t0,s10 ; lb t0,0(t0) ; 0x82940 bnez t0,829c0: the instrumented check of the
     byte Phi + 26 + i; the slow block 0x829c0 `andi t1,a0,7 ; bge t1,t0,8304c ; j 82944` rejoins with t1 changed *)
  step. step. rewrite (MState.unsigned_lit (phi + 26 + Z.of_nat i)) by lia.
  step. step. f28_converge (Z_to_bv 5 6) (phi + 26 + Z.of_nat i) b OK BD.
  (* 0x82944 lbu t0,0(a4): the code c = pbs[8 + i] *)
  step. rewrite f28_zxb_eq.
  remember (bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0))) as c eqn:Ec.
  assert (Bc : 0 <= c < 256) by (subst c; apply f28_ubyte).
  pose proof (f28_ite10 (RcLeaf.is_in c)) as B1.
  pose proof (f28_ite10 (RcLeaf.is_out c)) as B2.
  pose proof (f28_ite10 (c =? 3)) as B3.
  pose proof (f28_ite10 (c <? 4)) as B4.
  pose proof (f28_ite01 (RcPorts.pu_first pbs i =? 0)) as B5.
  (* 0x82948 sext.w t1,a2 ; andi a2,t0,253 ; seqz t2,a2 ; add a2,t1,t2 ; addw t1,t1,t2 ;
     0x8295c bne t1,a2 (trap T57: no 32-bit overflow) *)
  step. f28_norm. step. f28_norm. step. rewrite (f28_seqz_in c Bc).
  step. step. f28_norm. step. f28_nt.
  (* 0x82960 addi t1,t0,-1 ; sext.w t2,a1 ; seqz t1,t1 ; add a1,t2,t1 ; addw t1,t2,t1 ; bne t1,a1 (trap T58) *)
  step. step. f28_norm. step. rewrite (f28_seqz_m1 c Bc).
  step. step. f28_norm. step. f28_nt.
  (* 0x82978 addi t1,t0,-3 ; sext.w t2,a3 ; seqz t1,t1 ; add a3,t2,t1 ; addw t1,t2,t1 ; bne t1,a3 (trap T59) *)
  step. step. f28_norm. step. rewrite (f28_seqz_m3 c Bc).
  step. step. f28_norm. step. f28_nt.
  (* 0x82990 sltiu t1,t0,4 ; andi t2,a5,255 ; snez t2,t2 ; or t1,t2,t1 ; 0x829a0 beqz t1,829a8 *)
  step. rewrite (f28_sltiu4 c Bc).
  step. f28_norm. rewrite (f28_land255 (RcPorts.pu_first pbs i) Bfst).
  step. rewrite (f28_snez (RcPorts.pu_first pbs i) Bfst).
  step. f28_norm. rewrite f28_or.
  step.
  destruct ((c <? 4) || negb (RcPorts.pu_first pbs i =? 0))%bool eqn:EB; cbv_concl_iota.
  - (* the slot is known or a first unknown code was found: not taken; 0x829a4 mv t0,a5 keeps that code *)
    f28_brc false. step. f28_norm.
    assert (Ef : RcPorts.pu_first pbs (S i) = RcPorts.pu_first pbs i).
    { rewrite f28_first_step. unfold RcPorts.rc_u8. rewrite <- Ec, EB. reflexivity. }
    (* 0x829a8 addi a7,a7,-1 ; addi a0,a0,1 ; addi a4,a4,1 ; mv a5,t0 ; 0x829b8 bnez a7,8292c *)
    step. step. step. step. f28_norm. step.
    rewrite <- Ef. subst c.
    change (RcLeaf.cnt RcLeaf.is_in pbs i +
              (if RcLeaf.is_in (bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0))) then 1 else 0))
      with (RcLeaf.cnt RcLeaf.is_in pbs (S i)).
    change (RcLeaf.cnt RcLeaf.is_out pbs i +
              (if RcLeaf.is_out (bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0))) then 1 else 0))
      with (RcLeaf.cnt RcLeaf.is_out pbs (S i)).
    change (f28_nemp pbs i + (if bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0)) =? 3 then 1 else 0))
      with (f28_nemp pbs (S i)).
    replace (phi + 26 + Z.of_nat i + 1) with (phi + 26 + Z.of_nat (S i)) by lia.
    replace (12 - Z.of_nat i + -1) with (12 - Z.of_nat (S i)) by lia.
    destruct k as [|k].
    + (* i = 11: the back edge is not taken; 0x829bc j 829cc *)
      assert (E11 : i = 11%nat) by lia. subst i.
      f28_brc false. step.
      replace (phi + 26 + Z.of_nat 12) with (phi + 38) by lia.
      apply HQ.
    + f28_br true ltac:(rewrite bv_eqb_lit by lia; apply Bool.negb_true_iff, Z.eqb_neq; lia).
      apply (IH (S i)); [lia | lia | exact Hphi0 | exact Hphi50 | exact HB | exact HA | exact HQ].
  - (* the slot is the first unknown one: taken to 0x829a8 with t0 = c *)
    f28_brc true.
    assert (Ef : RcPorts.pu_first pbs (S i) = c).
    { rewrite f28_first_step. unfold RcPorts.rc_u8. rewrite <- Ec, EB. reflexivity. }
    (* 0x829a8 addi a7,a7,-1 ; addi a0,a0,1 ; addi a4,a4,1 ; mv a5,t0 ; 0x829b8 bnez a7,8292c *)
    step. step. step. step. f28_norm. step.
    replace (Z_to_bv 64 c) with (Z_to_bv 64 (RcPorts.pu_first pbs (S i))) by (rewrite Ef; reflexivity).
    clear Ef. subst c.
    change (RcLeaf.cnt RcLeaf.is_in pbs i +
              (if RcLeaf.is_in (bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0))) then 1 else 0))
      with (RcLeaf.cnt RcLeaf.is_in pbs (S i)).
    change (RcLeaf.cnt RcLeaf.is_out pbs i +
              (if RcLeaf.is_out (bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0))) then 1 else 0))
      with (RcLeaf.cnt RcLeaf.is_out pbs (S i)).
    change (f28_nemp pbs i + (if bv_unsigned (nth (8 + i)%nat pbs (Z_to_bv 8 0)) =? 3 then 1 else 0))
      with (f28_nemp pbs (S i)).
    replace (phi + 26 + Z.of_nat i + 1) with (phi + 26 + Z.of_nat (S i)) by lia.
    replace (12 - Z.of_nat i + -1) with (12 - Z.of_nat (S i)) by lia.
    destruct k as [|k].
    + assert (E11 : i = 11%nat) by lia. subst i.
      f28_brc false. step.
      replace (phi + 26 + Z.of_nat 12) with (phi + 38) by lia.
      apply HQ.
    + f28_br true ltac:(rewrite bv_eqb_lit by lia; apply Bool.negb_true_iff, Z.eqb_neq; lia).
      apply (IH (S i)); [lia | lia | exact Hphi0 | exact Hphi50 | exact HB | exact HA | exact HQ].
Qed.

(* The tail 0x829cc -> 0x82aa4: the three ports words (through s5 = fr + 128), the first byte and the byte blk + 7
   with its instrumented check; every FAIL and trap branch is shown not taken from the loop's counts.  The reads
   are given in the `ov_read_bytes` form the load steps consume.
   Touched address ranges: [A + 136, A + 144), [A + 312, A + 320), [fr + 128, fr + 140), [fr + 160, fr + 161),
   [Phi + 25, Phi + 26) and the shadow byte of Phi + 25. *)
Lemma f28_tail : forall (Q : _ -> Prop)
  (ra sp gp tp t1 t2 s0 s2 s3 s4 s6 s8 s9 s11 t3 t4 t5 t6 a7 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
  (A fr phi nin nout nemp nunk first bt7 : Z),
  0 < phi -> phi + 50 <= 2 ^ 64 ->
  0 <= nin <= 12 -> 0 <= nout <= 12 -> 0 <= nemp <= 12 -> 0 <= nunk <= 12 ->
  nin + nout + nemp + nunk = 12 -> 0 <= first < 256 -> 0 <= bt7 < 256 ->
  ov_read_bytes rsegs m (ULMem.wa (A + 136)) 8 = Some (ULMem.le8 (Z_to_bv 64 (fr + 160))) ->
  ov_read_bytes rsegs m (ULMem.wa (A + 312)) 8 = Some (ULMem.le8 (Z_to_bv 64 (phi + 18))) ->
  ov_read_bytes rsegs m (ULMem.wa (fr + 128)) 4 = Some (ULMem.le4 (Z_to_bv 64 (4 * nin))) ->
  ov_read_bytes rsegs m (ULMem.wa (fr + 132)) 4 = Some (ULMem.le4 (Z_to_bv 64 (4 * nout))) ->
  ov_read_bytes rsegs m (ULMem.wa (fr + 136)) 4 = Some (ULMem.le4 (Z_to_bv 64 (16 * bt7))) ->
  ov_read_bytes rsegs m (ULMem.wa (fr + 160)) 1 = Some [Z_to_bv 8 first] ->
  ov_read_bytes rsegs m (ULMem.wa (phi + 25)) 1 = Some [Z_to_bv 8 bt7] ->
  addressable m (phi + 25) 1 ->
  (forall a0' a1' a2' a3' a4' a5' a6' : word,
     Q (MS (mkR ra sp gp tp (Z_to_bv 64 first) t1 t2 s0 (Z_to_bv 64 A)
          a0' a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 (Z_to_bv 64 (fr + 128)) s6 (Z_to_bv 64 (4 * nunk)) s8 s9
          (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x82aa4) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp (Z_to_bv 64 first) t1 t2 s0 (Z_to_bv 64 A)
       (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 nout) (Z_to_bv 64 nin) (Z_to_bv 64 nemp)
       (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 first) (Z_to_bv 64 (-8 - (phi + 18))) a7
       s2 s3 s4 (Z_to_bv 64 (fr + 128)) s6 (Z_to_bv 64 (4 * nunk)) s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     F (Z_to_bv 64 0x829cc) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t1 t2 s0 s2 s3 s4 s6 s8 s9 s11 t3 t4 t5 t6 a7 F fc m A fr phi nin nout nemp nunk
    first bt7 Hphi0 Hphi50 Bin Bout Bemp Bunk Btot Bfst Bb7 R136 R312 RP0 RP1 RP2 RF R7 HA7 HQ.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HP63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
  assert (HP31 : 2 ^ 31 = 2147483648) by reflexivity.
  assert (HP30 : 2 ^ 30 = 1073741824) by reflexivity.
  destruct (f28_shadow m (phi + 25) HA7) as (b & RS & OK & BD).
  (* 0x829cc lw a4,0(s5) = 4 n_in ; andi a0,a4,3 ; bnez a0 (FAIL 829d4) *)
  step. rewrite (f28_sx32_small (4 * nin)) by lia.
  step. f28_norm. rewrite f28_land43. step. f28_nt.
  (* 0x829d8 lw a0,4(s5) = 4 n_out ; or a5,a0,s7 ; andi a5,a5,3 ; bnez a5 (FAIL 829e4) *)
  step. rewrite (f28_sx32_small (4 * nout)) by lia.
  destruct (f28_lor44 nout nunk ltac:(lia) ltac:(lia)) as (Blor & Elor).
  step. f28_norm. step. f28_norm. rewrite Elor. step. f28_nt.
  (* 0x829e8 ld a5,136(s1) = fr + 160 ; lbu a5,0(a5) = the first byte ; andi a6,t0,255 ; bne a5,a6 (FAIL 829f4) *)
  step. step. rewrite (f28_zxb_lit first Bfst).
  step. f28_norm. rewrite (f28_land255 first Bfst). step. f28_nt.
  (* 0x829f8 add a5,a4,a0 ; addw a6,a4,a0 ; bne a6,a5 (trap 82a00) ; sext.w a6,a5 ; add a5,a6,s7 ;
     addw a6,a6,s7 ; bne a6,a5 (trap 82a10) *)
  step. step. f28_norm. step. f28_nt.
  step. f28_norm. step. step. f28_norm. step. f28_nt.
  (* 0x82a14 lui a6,0x20000 ; add a6,a3,a6 ; srliw a6,a6,30 ; bnez a6 (trap 82a20: n_empty < 2^30 - 2^29) *)
  step. step. step. f28_norm. rewrite (f28_srliw30 (nemp + 536870912)) by lia. step. f28_nt.
  (* 0x82a24 slliw a6,a3,2 ; sext.w a5,a5 ; add a3,a5,a6 ; addw a5,a5,a6 ; bne a5,a3 (trap 82a34) ;
     sext.w a3,a3 ; li a5,48 ; bne a3,a5 (FAIL 82a40: every code is in exactly one class, so the sum is 48) *)
  step. f28_norm. step. f28_norm. step. step. f28_norm. step. f28_nt.
  step. f28_norm. step. step. f28_nt.
  (* 0x82a44 lui a3,0x20000 ; add a3,a2,a3 ; srliw a3,a3,30 ; bnez a3 (trap 82a50) ; slliw a2,a2,2 ;
     bne a4,a2 (FAIL 82a58) *)
  step. step. step. f28_norm. rewrite (f28_srliw30 (nin + 536870912)) by lia. step. f28_nt.
  step. f28_norm. step. f28_nt.
  (* 0x82a5c lui a2,0x20000 ; add a2,a1,a2 ; srliw a2,a2,30 ; bnez a2 (trap 82a68) ; slliw a1,a1,2 ;
     bne a0,a1 (FAIL 82a70) *)
  step. step. step. f28_norm. rewrite (f28_srliw30 (nout + 536870912)) by lia. step. f28_nt.
  step. f28_norm. step. f28_nt.
  (* 0x82a74 ld a0,312(s1) = Phi + 18 ; addi a0,a0,7 ; li a1,8 ; bltu a0,a1 (trap 82a80: Phi + 25 >= 8) *)
  step. step. step. step. f28_br false ltac:(rewrite bv_ltu_lit by lia; apply Z.ltb_ge; lia).
  (* 0x82a84 srli a1,a0,3 ; add a1,a1,s10 ; lb a2,0(a1) ; lw a1,8(s5) = 16 b7 ;
     0x82a94 bnez a2,82e28: the instrumented check of Phi + 25; the slow block 0x82e28
     `andi a3,a0,7 ; bge a3,a2,830cc ; j 82a98` rejoins with a3 changed *)
  step. step. rewrite (MState.unsigned_lit (phi + 25)) by lia.
  step. step. rewrite (f28_sx32_small (16 * bt7)) by lia.
  step. f28_converge (Z_to_bv 5 13) (phi + 25) b OK BD.
  (* 0x82a98 lbu a0,0(a0) = b7 ; slli a0,a0,4 ; bne a1,a0 (FAIL 82aa0) *)
  step. rewrite (f28_zxb_lit bt7 Bb7).
  step. f28_norm. step. f28_nt.
  apply evt_done. apply HQ.
Qed.

Section F28.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* ========================= the segment lemma ========================= *)

Lemma seg_F28 : forall j, Hat B APIf ra (Inv_B82aa4_at B APIf ra) j -> Hat B APIf ra (Inv_B8292c_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  unfold Inv_B8292c_at, FCUTP, CUTST in HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & Hs2 & Hs4 & HFT & _ &
    HFTL & HIFS & HK & Hrp & H23 & HPORTS & HFIRST & H10 & H14 & H16 & H17 & H11 & H12 & H13 & H15 & H28).
  subst c. rewrite SEGS.
  (* s5 = fr + 128 (FTL's position 1): the tail reads the three ports words through it *)
  pose proof HFTL as (Hs5 & _).
  (* the FRA facts the runs read: s10 = 0x7fff8000, the spill base, the model not halted *)
  assert (Hhalt : m_halted md = None) by (destruct HFRA as (A0 & sp0 & s50 & HF); tauto).
  assert (Hr26 : rg regs 26 ASAN_K) by (destruct HFRA as (A0 & sp0 & s50 & HF); tauto).
  destruct (fra_fr_spill B APIf ra g fr _ regs mem md HFRA)
    as (A & Hr9 & HA & _).
  (* the pieces of the kept bundle *)
  pose proof HK as (HLK & H18 & H27 & Hphi0 & Hphi50 & Hfl & Hblk & H312 & H272 & H24 & H104 & H136).
  (* the ports model at r = 0 *)
  destruct (f28_unk_rp0 (g_in g) j Hrp) as (Hunk & Hfirst).
  destruct HPORTS as (HP0 & _). destruct (HP0 Hrp) as (HW0 & HW1 & HW2).
  (* n_in / n_out as the counts the loop computes, by rewriting (f28_n_in): a conversion here would make the
     unifier and the kernel unfold the slot model *)
  rewrite f28_n_in in HW0. rewrite f28_n_out in HW1.
  pose proof (f28_blk_length (g_in g) j ltac:(unfold flen in Hfl; lia)) as Hblen.
  (* the twelve code bytes and the byte blk + 7, with their addressability *)
  assert (Hbyte : forall t, (t < 12)%nat ->
    bytes_at rsegs mem (phi + 26 + Z.of_nat t) [nth (8 + t)%nat (t_pbs (g_in g) j) (Z_to_bv 8 0)]).
  { intros t Ht. rewrite (f28_pbs_blk (g_in g) j (8 + t)%nat ltac:(lia)).
    replace (phi + 26 + Z.of_nat t) with (phi + 18 + Z.of_nat (8 + t)%nat) by lia.
    apply f28_byte; [rewrite Hblen; lia | exact Hblk]. }
  assert (Hb7 : bytes_at rsegs mem (phi + 25)
                  [Z_to_bv 8 (RcLeaf.bt (t_pbs (g_in g) j) 7)]).
  { unfold RcLeaf.bt. rewrite (f28_pbs_blk (g_in g) j 7%nat ltac:(lia)).
    rewrite f28_zb_id.
    replace (phi + 25) with (phi + 18 + Z.of_nat 7%nat) by lia.
    apply f28_byte; [rewrite Hblen; lia | exact Hblk]. }
  assert (Haddr : forall t, (t < 12)%nat -> addressable mem (phi + 26 + Z.of_nat t) 1).
  { intros t Ht. destruct HHB as (_ & Had).
    replace (phi + 26 + Z.of_nat t) with (phi + (26 + Z.of_nat t)) by lia.
    apply (addressable_sub mem phi (AC.a_size (flen g j)) (26 + Z.of_nat t) 1 Had);
      unfold AC.a_size, flen in *; lia. }
  assert (Haddr7 : addressable mem (phi + 25) 1).
  { destruct HHB as (_ & Had).
    apply (addressable_sub mem phi (AC.a_size (flen g j)) 25 1 Had);
      unfold AC.a_size, flen in *; lia. }
  (* bounds of the four slot counts and of the first unknown code *)
  pose proof (f28_cnt_bound RcLeaf.is_in (t_pbs (g_in g) j) 12) as Bin.
  pose proof (f28_cnt_bound RcLeaf.is_out (t_pbs (g_in g) j) 12) as Bout.
  pose proof (f28_nemp_bound (t_pbs (g_in g) j) 12) as Bemp.
  pose proof (f28_nunk_bound (t_pbs (g_in g) j) 12) as Bunk.
  pose proof (f28_total (t_pbs (g_in g) j) 12) as Btot.
  change (Z.of_nat 12) with 12 in Bin, Bout, Bemp, Bunk, Btot.
  assert (Bfirst : 0 <= RcPorts.pu_first (t_pbs (g_in g) j) 12 < 256)
    by (destruct (f28_first_nunk (t_pbs (g_in g) j) 12) as [(_ & E)|(_ & E)]; lia).
  pose proof (f28_u8_range (t_pbs (g_in g) j) 7%nat) as B7.
  (* the reads of the tail in the form its load steps consume; the spill base of each spill is s1 = A *)
  destruct H136 as (A3 & H93 & Hq136). destruct H312 as (A1 & H91 & Hq312).
  pose proof (f28_rd8 mem _ _ Hq136) as RD136.
  pose proof (f28_rd8 mem _ _ Hq312) as RD312.
  rewrite (f28_wa_shift A3 A 136) in RD136 by (unfold rg in *; rewrite <- H93, <- Hr9; reflexivity).
  rewrite (f28_wa_shift A1 A 312) in RD312 by (unfold rg in *; rewrite <- H91, <- Hr9; reflexivity).
  unfold FIRSTb in HFIRST. rewrite Hfirst in HFIRST.
  (* the one lazy run of this segment: Tac_slot.sl_run (AsanLift.evt_SR_canon_lazy).  It reads the ports words,
     the first byte, the twelve code bytes, the byte Phi + 25 and their shadow bytes; it writes no memory. *)
  apply (sl_run regs (Z_to_bv 64 0x8292c) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x82aa4 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
       getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
       getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27)
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* the loop from its first turn, then the tail *)
    rewrite f28_mkR_of_expand.
    f28_slot H10. f28_slot H14. f28_slot H16. f28_slot H17. f28_slot H11. f28_slot H12. f28_slot H13.
    f28_slot H15. f28_slot H28. f28_slot Hr26. f28_slot Hr9. f28_slot H23. f28_slot Hs5.
    rewrite Hunk.
    replace (Z_to_bv 64 (phi + 26)) with (Z_to_bv 64 (phi + 26 + Z.of_nat 0)) by (f_equal; lia).
    eapply f28_loop with (k := 12%nat) (i := 0%nat) (phi := phi) (pbs := t_pbs (g_in g) j);
      [reflexivity | lia | exact Hphi0 | exact Hphi50 | exact Hbyte | exact Haddr |].
    intros t1' t2'.
    eapply f28_tail with (A := A) (fr := fr) (phi := phi)
      (nin := RcLeaf.cnt RcLeaf.is_in (t_pbs (g_in g) j) 12)
      (nout := RcLeaf.cnt RcLeaf.is_out (t_pbs (g_in g) j) 12)
      (nemp := f28_nemp (t_pbs (g_in g) j) 12) (nunk := RcPorts.pu_nunk (t_pbs (g_in g) j) 12)
      (first := RcPorts.pu_first (t_pbs (g_in g) j) 12) (bt7 := RcLeaf.bt (t_pbs (g_in g) j) 7);
      [ exact Hphi0 | exact Hphi50 | lia | lia | lia | lia | lia | exact Bfirst | exact B7
      | exact RD136 | exact RD312
      | exact (f28_rd4 _ _ _ HW0) | exact (f28_rd4 _ _ _ HW1) | exact (f28_rd4 _ _ _ HW2)
      | exact (f28_rd1 _ _ _ HFIRST) | exact (f28_rd1 _ _ _ Hb7) | exact Haddr7 | ].
    intros a0' a1' a2' a3' a4' a5' a6'. cbv beta.
    do 3 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    (* K (registers 2 3 4 8 9 18 19 20 21 24 26 27): f28_slot rewrote s1 and s10 inside K too, so each is
       reflexive *)
    repeat (split; [reflexivity|]). reflexivity.
  - intros R pc' mem' regs' md'
      (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E24 & E26 & E27) Hreg Hmat.
    subst pc' mem'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact E27).
    destruct (f27_exit g j phi fr regs regs' mem HK Hs4 HFTL HFT HIFS Fr9 Fr18 Fr20 Fr21 Fr24 Fr27)
      as (X18 & X20 & XFT & XLK & XFTL & XIFS).
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', mem, md', fr.
    split; [reflexivity|].
    split.
    { apply (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA);
        assumption. }
    split; [eapply ent_mat; [exact HENT | exact Hmat]|].
    split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
    split; [exact X18|]. split; [exact X20|]. split; [exact XFT|].
    split; [exact XLK|]. split; [exact XFTL | exact XIFS].
Qed.

End F28.
