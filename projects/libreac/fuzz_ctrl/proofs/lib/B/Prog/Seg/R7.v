(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names, addresses and numbers changed; 1202 of its 1292 lines of code are new or changed and 921 lines of the source are left out. *)
(* Segment R7 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81710, 0x81760],
   21 instructions, cut Inv_B81710_at b -> cuts Inv_B81764_at b and Inv_B81ac0_at b (plan-asan-ubsan.md section 2,
   row R7, the ubsan twin R06; section 4, MALLOC = wrapper_malloc at 0x534b8). rule 24: no function proved (a slot
   segment).
   The code tests the build_as count a0 = n = rnb g b at 0x81710 `beqz a0,0x81ac0`; the cut does not say n <> 0,
   so the segment has two exits.
   - n = 0 (the row's E(b) is false): the branch is taken to the round-trip latch 0x81ac0 with the registers and the
     memory of the cut (r7_evt0), so the exit is Inv_B81ac0_at b: FRA moves by sl_fra_move, ENT by ent_mat, and a
     turn whose count is 0 keeps the records (rt_st (S b) = rt_st b, r7_st_skip). R6X g (S b) at the latch follows
     from the moved RBE (r6x_of_rbe).
   - n <> 0: the count is kept in s2 (0x81714 mv s2,a0; v1.8 had s9) and three inline range checks run on it. Each
     check falls through to `j 0x82fa4` (the abort sink; plan 1.5 rows 3-5) when it fails:
     - 0x81718-0x81720: n - 1493 >= -1441 unsigned, that is 52 <= n <= 1492;
     - 0x81728-0x81734: (n - 52) mod 2^16 >= 36 (s5 = 36);
     - 0x8173c-0x81754: (n - 52) - 36 * ((((n - 52) << 48) *hu [A + 128]) >> 21) = 0 mod 2^16, the division by 36
       through the magic word [A + 128] = 0xe38f0000.
     The count is rt_n(in, b) = 52 + 36 u with u even in [2, 40] (r7_rnb_shape), so every check holds and no error
     edge is taken; r7_evt runs the block on each of the 20 values of n. The range holds no instrumented shadow
     check (no lb/lbu of a shadow byte), no UBSan trap and no store.
     Then 0x8175c mv a0,s2 and 0x81760 jal wrapper_malloc: the allocator, taken on the frame's AsanAllocAPI law
     aa_malloc (never its code), from the a_call_pre that fra_call_pre builds from FRA + ENT (ret_ok from the jal:
     ra = 0x81764; K = AK_MALLOC = 4096 <= FN_STACK).
   The v1.9 aa_malloc (Contract.v amalloc_at) also asks for a per-class bound Bc of the call heap g_H g with its
   room; it comes from ENT's 14th conjunct (SOME bound BE of the entry heap with BE c + BC_ctrl c <= 2 ^ 22) by
   Tac_cls.sl_malloc_cls, with Bc = Bc_of BE = BE + BC_ctrl.  ENT's 14th conjunct names only the ghost, so the
   exit's ENT keeps the same witness (r7_ent_call).
   At the return the new block (q, rnb g b) is the exit cut's hb1 phi (rnb g b) (the allocator appends it to the
   live-block list; sl_mid_perm and r7_ent_call take the permutation; a_size (rnb g b) = rnb g b since
   rnb g b >= 124). FRA, ENT, the spills, the frame bytes and their shadow bytes and the count pins are carried
   across the call by a_call_post's frame clause: every byte the exit cut reads is on the real stack at or above
   sp, in the frame (the real stack or the side stack FS), a shadow byte of a real-stack, FS or image byte, the
   input block (also a live block), a musl client cell (the sink words), a read-only image byte (the catalogue's
   box bytes and row-name strings) or a RELRO byte of the image (the row table, the catalogue row), none of which
   the allocator owns (a_laws_not_owned, a_laws_client, a_laws_ro_not_owned, and frame_facts for frame_RELRO), and
   none of which is in the allocator's window [sp - 4096, sp), errno, the OOM flag or the new block. ENT's
   append #1 (the entry blocks' shadow) moves because those shadow bytes are owned in neither state.
   R7's exit carries RBE (21 spills, OUTA, the row-name clause, our[] addressable, the row table / box /
   catalogue-row image bytes, PRA, [A+152], [A+112], the fragment record's 72 addressable bytes and [A+160]),
   which move across the call as frame / frame-shadow / image bytes. FRA's input facts move across the call too:
   the input block is a live block of g_H g (fra_in_apart), so its bytes and its shadow bytes are the allocator's
   of neither state. The entry carries the turn records IDBr / FGBr and, on n <> 0, out[]'s frame bytes rt_F at
   fr + 544 (build_as's post, produced by R6); the allocator writes only the new block and its own metadata, so
   both are carried as frame bytes to Inv_B81764_at. s11 = 32 (rg regs 27 32) is carried to both exits: the
   branch keeps it and the allocator keeps it (a_callee_saved). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require RtmB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmit RcEmitLib reac_ctrl_build_as_c RcSynth.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_cls.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module REL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcEmitLib.
Module BAP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Module BAC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_as_c.
Module RS6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.

(* ---- the count: rt_n(in, b) is 0 or 52 + 36 u with u even in [2, 40] ---- *)

Lemma r7_rnb_shape : forall inp b, rt_n inp b <> 0 ->
  exists u, 2 <= u <= 40 /\ Z.even u = true /\ rt_n inp b = 52 + 36 * u.
Proof.
  intros inp b H. unfold rt_n in *.
  destruct (rt_E inp b) eqn:E; [|exfalso; apply H; reflexivity].
  unfold rt_E, BAP.ba_E in E. apply andb_true_iff in E as (E1 & _).
  destruct (REL.em_wok_range _ E1) as (Hr & Hev).
  exists (rt_uw inp). split; [exact Hr | split; [exact Hev | reflexivity]].
Qed.

(* the 20 values of a non-zero count *)
Definition r7_nv (n : Z) : Prop :=
  n = 124 \/ n = 196 \/ n = 268 \/ n = 340 \/ n = 412 \/ n = 484 \/ n = 556 \/ n = 628 \/ n = 700 \/ n = 772 \/
  n = 844 \/ n = 916 \/ n = 988 \/ n = 1060 \/ n = 1132 \/ n = 1204 \/ n = 1276 \/ n = 1348 \/ n = 1420 \/ n = 1492.

(* 52 + 72 k for k in [1, 20], by enumerating k (a 20-way disjunctive goal is too wide for lia's case split). *)
Lemma r7_nv_of : forall k, 1 <= k <= 20 -> r7_nv (52 + 72 * k).
Proof.
  intros k Hk.
  assert (E : k = Z.of_nat (Z.to_nat k)) by lia.
  rewrite E. clear E.
  assert (Hn : (1 <= Z.to_nat k <= 20)%nat) by lia.
  revert Hn. generalize (Z.to_nat k). clear k Hk. intros n Hn.
  unfold r7_nv.
  do 21 (destruct n as [|n];
    [ first [ exfalso; lia
            | vm_compute; repeat (first [left; reflexivity | right]); reflexivity ] | ]).
  exfalso; lia.
Qed.

Lemma r7_rnb_nv : forall inp b, rt_n inp b <> 0 -> r7_nv (rt_n inp b).
Proof.
  intros inp b H. destruct (r7_rnb_shape inp b H) as (u & Hu & Hev & ->).
  apply Z.even_spec in Hev. destruct Hev as (k & ->).
  replace (52 + 36 * (2 * k)) with (52 + 72 * k) by lia.
  apply r7_nv_of. lia.
Qed.

Lemma r7_nv_range : forall n, r7_nv n -> 124 <= n <= 1492.
Proof. intros n H. unfold r7_nv in H. lia. Qed.

(* ---- the run 0x81710 .. 0x81760 (21 instructions, ending at the allocator's entry) ---- *)

(* A branch whose condition is a closed term (every register it reads holds a literal here). *)
Ltac r7_if_true :=
  first [ if_true
        | lazymatch goal with
          | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
              replace c with true; [cbv_concl_iota | symmetry; vm_compute; reflexivity]
          end ].
Ltac r7_if_false :=
  first [ if_false
        | lazymatch goal with
          | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
              replace c with false; [cbv_concl_iota | symmetry; vm_compute; reflexivity]
          end ].

(* 0x81710 beqz a0 (not taken); 0x81714 .. 0x81720 bgeu a0,a1 (taken); 0x81728 .. 0x81734 bgeu a2,s5 (taken);
   0x8173c .. 0x81754 beqz a0 (taken); 0x8175c mv a0,s2; 0x81760 jal wrapper_malloc. *)
Ltac r7_run :=
  step; r7_if_false;
  do 4 step; r7_if_true;
  do 4 step; r7_if_true;
  do 7 step; r7_if_true;
  do 2 step;
  finish; try simp_regs; first [reflexivity | vm_compute; reflexivity].

Lemma r7_evt : forall (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                       : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
  a0 = Z_to_bv 64 n -> s5 = Z_to_bv 64 36 -> r7_nv n ->
  ro_cells rsegs m (bv_unsigned s1 + 128) [C8 (Z_to_bv 64 0xe38f0000)] ->
  evt rsegs
    (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x534b8) fc None m (seg_rom rsegs) /\
       getr R 1 = Z_to_bv 64 0x81764 /\ getr R 10 = Z_to_bv 64 n /\ getr R 18 = Z_to_bv 64 n /\
       getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
       getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
       getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11)
    (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81710) fc None m (seg_rom rsegs)).
Proof.
  intros rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m n -> -> Hn HRO.
  unfold r7_nv in Hn.
  repeat match goal with Hd : _ \/ _ |- _ => destruct Hd as [Hd|Hd] end.
  all: subst n; r7_run.
Qed.

(* 0x81710 beqz a0,0x81ac0 taken on a zero count: one instruction, every register and the memory kept. *)
Lemma r7_evt0 : forall (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                        : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  a0 = Z_to_bv 64 0 ->
  evt rsegs
    (fun ms' => exists R, ms' = MS R F (Z_to_bv 64 0x81ac0) fc None m (seg_rom rsegs) /\
       getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
       getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
       getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 18 = s2 /\ getr R 27 = s11)
    (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81710) fc None m (seg_rom rsegs)).
Proof.
  intros rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ->.
  step; r7_if_true.
  finish; try simp_regs; first [reflexivity | vm_compute; reflexivity].
Qed.

(* ---- register, cell and byte helpers ---- *)

Lemma r7_mkR_of : forall regs,
  Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* A spilled word read by `ld`, as one read-only cell of the stepping engine. *)
Lemma r7_ro8 : forall m a v, q64 m a v -> ro_cells rsegs m a [C8 (Z_to_bv 64 v)].
Proof. intros m a v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

(* Bytes whose cells keep their contents. *)
Lemma r7_keep_bytes : forall m m' a bs,
  bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte rsegs m' x = mbyte rsegs m x) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). exact (HK (a + Z.of_nat i) ltac:(lia)).
Qed.

(* A buffer stays addressable when its shadow bytes keep their contents (ADDR-KEEP). *)
Lemma r7_addr_keep : forall m m' p n,
  addressable m p n ->
  (forall i, 0 <= i < n -> mbyte rsegs m' (shadow_addr (p + i)) = mbyte rsegs m (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H0 & H1 & H2 & H) HK. split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Happ & bb & Hb & Hok).
  split; [exact Happ|]. exists bb. split; [|exact Hok]. rewrite <- Hb. exact (HK i Hi).
Qed.

(* A register value read twice in [0, 2^64). *)
Lemma r7_rg_eq : forall regs r x y, rg regs r x -> rg regs r y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x = y.
Proof.
  intros regs r x y Hx Hy Hxr Hyr. pose proof (rg_eq64 regs r x y Hx Hy) as Hm.
  rewrite !Z.mod_small in Hm by lia. exact Hm.
Qed.

(* A callee-saved register of an allocator entry, at a register named by a numeral. *)
Lemma r7_regs_kept_at : forall regs regs' (r : reg) (z : Z),
  AC.a_regs_kept regs regs' -> AC.a_callee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HK Hc <-. exact (HK z Hc). Qed.

(* The shadow byte of the frame's 8 k-th byte. *)
Lemma r7_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof.
  intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

(* ---- image placement, on the image's segment table ---- *)

(* The image's loaded segments all end below GT = 0x5fe000. *)
Lemma r7_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r7_img_range : forall x, AC.a_in_img x -> 0 <= x < 6283264.
Proof.
  intros x (s & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) r7_img_top s Hin) as Hs. cbv beta in Hs.
  apply Z.leb_le in Hs. pose proof (N2Z.is_nonneg (seg_base s)). lia.
Qed.

Definition r7_img_cov (lo hi : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs.

Lemma r7_img_cov_in : forall lo hi x, r7_img_cov lo hi = true -> lo <= x < hi -> AC.a_in_img x.
Proof.
  intros lo hi x H Hx. unfold r7_img_cov in H. apply existsb_exists in H. destruct H as (s & Hin & Hb).
  apply andb_true_iff in Hb as (H1 & H2). apply Z.leb_le in H1, H2.
  exists s. split; [exact Hin | lia].
Qed.

(* The registered globals are image bytes (they are in the image's first loaded segment); so are the musl sink
   cells (the fourth segment). *)
Lemma r7_ag_cov : forallb (fun p => r7_img_cov (fst p) (fst p + snd p)) AF.frame_AG = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r7_ag_img : forall a, in_globals AF.frame_AG a -> AC.a_in_img a.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) r7_ag_cov (lo, len) Hin) as H. cbn [fst snd] in H.
  exact (r7_img_cov_in _ _ _ H Hr).
Qed.

Lemma r7_sink_cov_a : r7_img_cov 0x5fc8e1 0x5fc8e2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma r7_sink_cov_b : r7_img_cov 0x5fcd40 0x5fcd50 = true.
Proof. vm_compute. reflexivity. Qed.

(* The client objects of musl's stdio the sink words live in (Contract.v a_client: [0x5dc680, 0x5fc910) holds
   __threaded at 0x5fc8e1; [0x5fc918, 0x5fd9f8) holds the open-file lock 0x5fcd40 and the list head 0x5fcd48). *)
Lemma r7_client_a : forall a, 0x5dc680 <= a < 0x5dc680 + 131728 -> AC.in_blocks AC.a_client a.
Proof. intros a Ha. exists 0x5dc680, 131728. split; [cbn; tauto | exact Ha]. Qed.
Lemma r7_client_b : forall a, 0x5fc918 <= a < 0x5fc918 + 4320 -> AC.in_blocks AC.a_client a.
Proof. intros a Ha. exists 0x5fc918, 4320. split; [cbn; tauto | exact Ha]. Qed.

(* The image's first loaded segment [0x10000, 0x30104) is read-only; it holds the catalogue's box bytes (at
   BOXA = 0x21140) and the row-name strings ([0x214a0, 0x218e0]). *)
Definition r7_ro_cov (lo hi : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? lo) &&
                    (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs.

Lemma r7_ro_cov_ok : r7_ro_cov 0x21140 0x218f0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r7_ro_in : forall x, 0x21140 <= x < 0x218f0 -> AC.a_in_ro x.
Proof.
  intros x Hx. pose proof r7_ro_cov_ok as H. unfold r7_ro_cov in H.
  apply existsb_exists in H. destruct H as (s & Hin & Hb).
  apply andb_true_iff in Hb as (Hb & H2). apply andb_true_iff in Hb as (Hw & H1).
  apply negb_true_iff in Hw. apply Z.leb_le in H1, H2.
  exists s. split; [exact Hin|]. split; [exact Hw | lia].
Qed.

Lemma r7_ro_img : forall x, AC.a_in_ro x -> AC.a_in_img x.
Proof. intros x (s & Hin & _ & Hr). exists s. split; [exact Hin | exact Hr]. Qed.

(* The image's RELRO globals are one block [0x9f168, 0x9f168 + 9344) (v1.9 frame_RELRO); the row table
   (BA_FR + 72 .. + 240) and the catalogue row (mrow .. mrow + 296) lie in it. *)
Lemma r7_relro_range : forall a, in_globals AF.frame_RELRO a -> 0x9f168 <= a < 0x9f168 + 9344.
Proof.
  intros a (lo & len & Hin & Hr). unfold AF.frame_RELRO in Hin. cbn [In] in Hin.
  destruct Hin as [E|[]]; inversion E; subst; lia.
Qed.

Lemma r7_relro_in : forall x, 0x9f168 <= x < 0x9f168 + 9344 -> in_globals AF.frame_RELRO x.
Proof.
  intros x Hx. exists 0x9f168, 9344.
  split; [unfold AF.frame_RELRO; cbn [In]; left; reflexivity | lia].
Qed.

(* The row table ba_tbl is 168 bytes (7 rows of 24). *)
Lemma r7_tbl_len : Z.of_nat (length BAP.ba_tbl) = 168.
Proof. vm_compute. reflexivity. Qed.

(* The catalogue row mrow(in) lies at CAT + 296 * istar with istar in [0, 10], so in RELRO's middle block. *)
Lemma r7_mrow_range : forall inp, 0x9f620 <= mrow inp <= 0x9f620 + 296 * 10.
Proof.
  intros inp. unfold mrow, CAT, CAT_ROW.
  assert (Hi : 0 <= istar inp < CAT_N) by (unfold istar; apply Z.mod_pos_bound; unfold CAT_N; lia).
  unfold CAT_N in Hi. lia.
Qed.

(* The catalogue row rt_mb(in) is 296 bytes. *)
Lemma r7_mb_len : forall inp, length (rt_mb inp) = 296%nat.
Proof.
  intros inp. unfold rt_mb, rowb, img.
  destruct (Lib.Image.image_bytes rsegs (CAT + CAT_ROW * istar inp) 296) eqn:Ei;
    [exact (Lib.Image.image_bytes_length rsegs 296 _ _ Ei) | apply repeat_length].
Qed.

(* The row name of every catalogue row that has one lies in [0x214a0, 0x218e0] (by computation on the 11 rows of
   BOX_CATALOGUE; rt_mb inp is row istar inp, istar inp < 11). *)
Lemma r7_rows_b :
  forallb (fun i => (RS6.has (rowb i) =? 0) || (RS6.rname (rowb i) =? 0) ||
                    ((0x214a0 <=? RS6.rname (rowb i)) && (RS6.rname (rowb i) <=? 0x218e0)))
    [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r7_rname : forall inp, RS6.has (rt_mb inp) <> 0 -> RS6.rname (rt_mb inp) <> 0 ->
  0x214a0 <= RS6.rname (rt_mb inp) <= 0x218e0.
Proof.
  intros inp H1 H2. unfold rt_mb in *.
  assert (Hi : 0 <= istar inp < 11) by (unfold istar, CAT_N; apply Z.mod_pos_bound; lia).
  assert (Hin : In (istar inp) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]) by (cbn [In]; lia).
  pose proof (proj1 (forallb_forall _ _) r7_rows_b _ Hin) as Hb. cbv beta in Hb.
  apply orb_true_iff in Hb as [Hb|Hb]; [apply orb_true_iff in Hb as [Hb|Hb]|].
  - apply Z.eqb_eq in Hb. contradiction.
  - apply Z.eqb_eq in Hb. contradiction.
  - apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1, Hb2. lia.
Qed.

(* The row-name string is at most 16 bytes. *)
Lemma r7_cstr_len : forall k a, (length (img_cstr a k) <= k)%nat.
Proof.
  induction k as [|k IH]; intros a; cbn [img_cstr]; [cbn [length]; lia|].
  match goal with |- context [if ?c then _ else _] => destruct c end; cbn [length];
    [lia | specialize (IH (a + 1)); lia].
Qed.

Lemma r7_nb_len : forall inp, (length (rt_nb inp) <= 16)%nat.
Proof. intros inp. unfold rt_nb. apply r7_cstr_len. Qed.

(* ---- the zero-count exit and the spill bundle ---- *)

(* A turn whose count is 0 leaves the records as they were (SlotModel.rt_st: n =? 0 keeps the state). *)
Lemma r7_st_skip : forall inp b, rt_n inp (Z.of_nat b) = 0 -> rt_st inp (S b) = rt_st inp b.
Proof. intros inp b H. cbn [rt_st]. rewrite H. reflexivity. Qed.

(* A spilled word moves to registers with the same spill base in register 9. *)
Lemma r7_spill_move : forall regs regs' m off v, getr regs' 9 = getr regs 9 -> spill regs m off v -> spill regs' m off v.
Proof. intros regs regs' m off v E (A & HA & Hq). exists A. split; [unfold rg in *; rewrite E; exact HA | exact Hq]. Qed.

(* RBE's spills (the 21, PRA's eleven, [A+152], [A+112] and [A+160]) read the registers only through the spill
   base in register 9; OUTA, the identity record's addressability, the row-name clause, our[] addressability, the
   row table / box / catalogue-row bytes and the fragment record's addressability are facts of the memory
   alone. *)
Lemma r7_rbe_move : forall g fr regs regs' m, getr regs' 9 = getr regs 9 -> RBE g fr regs m -> RBE g fr regs' m.
Proof.
  intros g fr regs regs' m E
    (H128 & H312 & H272 & H264 & H256 & H248 & H56 & H184 & H144 & H8 & H32 & H24 & H16 & H96 & H120 &
     H240 & H232 & H224 & H176 & H208 & H64 & HOUT & Hid38 & HNM & Hour6 & Htbl & Hbox & Hmrow &
     (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b) & H152 & H112 & H2256 &
     H160).
  unfold RBE.
  split; [exact (r7_spill_move _ _ _ _ _ E H128)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H312)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H272)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H264)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H256)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H248)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H56)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H184)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H144)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H8)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H32)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H24)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H16)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H96)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H120)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H240)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H232)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H224)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H176)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H208)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H64)|].
  split; [exact HOUT|]. split; [exact Hid38|]. split; [exact HNM|]. split; [exact Hour6|]. split; [exact Htbl|].
  split; [exact Hbox|]. split; [exact Hmrow|].
  split.
  { unfold PRA.
    split; [exact (r7_spill_move _ _ _ _ _ E P136)|].
    split; [exact (r7_spill_move _ _ _ _ _ E P280)|].
    split; [exact (r7_spill_move _ _ _ _ _ E P168)|].
    split; [exact (r7_spill_move _ _ _ _ _ E P192)|].
    split; [exact (r7_spill_move _ _ _ _ _ E P200)|].
    split; [exact (r7_spill_move _ _ _ _ _ E P216)|].
    split; [exact (r7_spill_move _ _ _ _ _ E P104)|].
    split; [exact (r7_spill_move _ _ _ _ _ E P288)|].
    split; [exact (r7_spill_move _ _ _ _ _ E P296)|].
    split; [exact (r7_spill_move _ _ _ _ _ E P304)|].
    exact (r7_spill_move _ _ _ _ _ E P168b). }
  split; [exact (r7_spill_move _ _ _ _ _ E H152)|].
  split; [exact (r7_spill_move _ _ _ _ _ E H112)|].
  split; [exact H2256 | exact (r7_spill_move _ _ _ _ _ E H160)].
Qed.

(* A spill at A + off (A the spill base in register 9, in [0, 2^64 - 448]) moves to a later state whose register 9
   is the same and whose bytes at [A + off, A + off + 8) are the same. The spill's own base is A: it agrees with A
   modulo 2^64 and A + off + 8 <= 2^64 with 0 <= A + off. *)
Lemma r7_spill_keep : forall regs regs' m m' A off v,
  rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  getr regs' 9 = getr regs 9 ->
  (forall x, A + off <= x < A + off + 8 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  spill regs m off v -> spill regs' m' off v.
Proof.
  intros regs regs' m m' A off v Hr9 HA0 HA1 Hoff E9 HK (A' & HA' & Hq).
  assert (HA'eq : A' = A).
  { pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm.
    pose proof Hq as Hqb. destruct Hqb as (Hq0 & Hq1 & _).
    rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
    rewrite (Z.mod_small A) in Hm by lia.
    assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity.
    rewrite HP in *. Z.div_mod_to_equations. lia. }
  subst A'. exists A. split; [unfold rg in *; rewrite E9; exact Hr9|].
  apply (r7_keep_bytes m m' _ _ Hq). rewrite length_le8. change (Z.of_nat 8) with 8.
  intros x Hx. exact (HK x Hx).
Qed.

(* FSREC (the side-arm frame record) moves to a state that keeps the 16 bytes at tp and every FakeStack byte outside
   the frame body [fr + 24, fr + FRAME_BYTES): the flag byte FS + 36352 + j and the slot's last word fr + 4088 are
   FakeStack bytes (as in Tac_slot.fsrec_munch). *)
Lemma r7_fsrec_keep : forall mem mem' fr,
  FSREC fr mem ->
  (forall i, 0 <= i < 16 -> mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i)) ->
  (forall x, AC.a_in_fs AC.ASYMS mem x -> ~ (fr + 24 <= x < fr + FRAME_BYTES) ->
     mbyte rsegs mem' x = mbyte rsegs mem x) ->
  FSREC fr mem'.
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros mem mem' fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) Htp' HK.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
  assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  assert (Hin : forall x, FS <= x < FS + AC.FS_SIZE -> AC.a_in_fs AC.ASYMS mem x)
    by (intros x Hx; exists FS; split; [exact HFSr | split; [exact Htp | exact Hx]]).
  exists FS, j.
  split.
  { intros k Hk. rewrite (Htp' (Z.of_nat k) ltac:(lia)). exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { apply (r7_keep_bytes mem mem' _ _ Hflag). cbn [length]. change (Z.of_nat 1) with 1.
    intros x Hx. apply HK; [apply Hin|]; lia. }
  { apply (r7_keep_bytes mem mem' _ _ Htail). rewrite length_le8. change (Z.of_nat 8) with 8.
    intros x Hx. rewrite HB6 in Hx. apply HK; [apply Hin|]; lia. }
Qed.

Section R7.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The allocator-law fields this file reads, in the shape its use sites take, read through SlotInv's LawFields
   (lw_*: each generated law is taken apart once there).  a_laws_client's client-cell field has no LawFields
   lemma; r7_client takes it apart here, once (its pattern ends in `_`, so an appended conjunct changes no
   line). *)
Lemma r7_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ end_in_app p n /\
  (forall a, p <= a < p + n -> app_mem a /\ writable_at rsegs mem a /\ ~ AC.a_in_img a /\
     ~ AC.a_on_img_page a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [H1 H2 H3 H4 H5].
  exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.

Lemma r7_fs_place : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ FS mod 4096 = 0 /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md FS HAH Hw HFS.
  destruct (lw_fs_place (APIf rc) H mem md FS HAH Hw HFS) as [H1 H2 H3 H4].
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma r7_nown_both : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (AC.in_blocks H a \/ AC.in_slack H a \/ AC.a_in_fs AC.ASYMS mem a \/
   AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a /\
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (shadow_addr a).
Proof.
  intros H mem md a HAH Hor.
  destruct (lw_not_owned (APIf rc) H mem md a HAH Hor) as [H1 H2]. exact (conj H1 H2).
Qed.

Lemma r7_nown : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (AC.in_blocks H a \/ AC.in_slack H a \/ AC.a_in_fs AC.ASYMS mem a \/
   AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a.
Proof. intros H mem md a HAH Hor. exact (proj1 (r7_nown_both H mem md a HAH Hor)). Qed.

Lemma r7_nown_sh : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (AC.in_blocks H a \/ AC.in_slack H a \/ AC.a_in_fs AC.ASYMS mem a \/
   AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (shadow_addr a).
Proof. intros H mem md a HAH Hor. exact (proj2 (r7_nown_both H mem md a HAH Hor)). Qed.

Lemma r7_client : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (AC.in_blocks AC.a_client a -> ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  (AC.a_in_img a -> ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (shadow_addr a)).
Proof.
  intros H mem md a HAH.
  destruct (AC.a_laws_client _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md a HAH)
    as (Hc & _).
  exact (conj Hc (lw_client_img_shadow (APIf rc) H mem md a HAH)).
Qed.

Lemma r7_mat_le : forall H mem md md', AsanLift.mat_le md md' ->
  (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md') /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md' a <->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md' = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem md md' Hmat.
  destruct (lw_mat_le (APIf rc) H mem md md' Hmat) as [H1 H2 H3 H4].
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

(* Tac_slot.ent_call for a callee whose post heap H' is a permutation of hb' ++ g_H g (the allocator appends the new
   block: g_H ++ [(q, n)]). ENT reads the post heap only through the runtime's ownership of image bytes, which is
   the same for the two orders (ent_owned_img), and through a_laws_not_owned / a_laws_client, which hold for H'. *)
Lemma r7_ent_call : forall g fr hb hb' H' regs mem md regs' mem' md' touched K,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT
    (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
    K (hb ++ g_H g) regs mem md touched H' regs' mem' md' ->
  Permutation (hb' ++ g_H g) H' ->
  0 <= K <= FN_STACK ->
  (forall a, touched a -> app_mem a /\ a < g_S g /\ ~ AC.a_in_img a /\ ~ AC.in_blocks (g_H g) a) ->
  AC.a_errno_kept AC.ASYMS mem mem' ->
  ENT APIf g hb' mem' md'.
Proof.
  intros g fr hb hb' H' regs mem md regs' mem' md' touched K HENT HFRA Hcp Hperm HK Hto Hek.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof HENT as HE0.
  destruct HE0 as (Hasp & Hgtp & HTH & Hfs & Hfz & Hmdl & Hslo & Hshi & Hblk & Himg & Habv & Hshd & Hkshd & Hcls).
  assert (HS0 : 0 <= g_S g) by (rewrite <- Hasp; apply (bv_unsigned_in_range 64)).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & _ & _).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  unfold HIGHMEM_BEG in Hhigh.
  pose proof Hcp as Hah0; apply AC.a_call_post_ah in Hah0.
  assert (Hah' : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb' ++ g_H g) mem' md')
    by exact (AC.a_laws_perm _ _ _ _ _ LAWS H' (hb' ++ g_H g) mem' md' Hah0 (Permutation_sym Hperm)).
  pose proof Hcp as Hsk; apply AC.a_call_post_stklo in Hsk.
  pose proof Hcp as Hskh; apply AC.a_call_post_stkhi in Hskh.
  pose proof Hcp as Hoom; apply AC.a_call_post_oom in Hoom.
  assert (Htp : forall i, 0 <= i < 16 ->
            mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
    by (eapply AC.a_call_post_tp; exact Hcp).
  assert (Hfr : forall a, 0 <= a < 2 ^ 64 ->
            ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
            ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' a ->
            ~ AC.a_window K regs a -> ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) ->
            a <> AC.as_oom AC.ASYMS -> ~ touched a ->
            mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a))
    by (eapply AC.a_call_post_frame; exact Hcp).
  (* the runtime owns an image byte under H' exactly when it owns it under hb' ++ g_H g *)
  assert (Hown' : forall a, AC.a_in_img a ->
            (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb' ++ g_H g) mem' md' a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' a))
    by (intros a Ha; exact (ent_owned_img APIf (hb' ++ g_H g) H' mem' md' mem' md' a Hah' Hah0 eq_refl
                              (fun i _ => eq_refl) Ha)).
  (* the callee's window is inside the slot window, so it is below S *)
  assert (Hwin2 : forall a, AC.a_window K regs a ->
            AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < g_S g).
  { intros a Ha. unfold AC.a_window in Ha. unfold FN_STACK in Hwlo.
    rewrite Haspz in Ha. rewrite Haspz in Hwlo. lia. }
  assert (Hoomimg : AC.a_in_img (AC.as_oom AC.ASYMS)) by exact oom_in_img.
  split; [exact Hasp|]. split; [exact Hgtp|]. split; [exact HTH|]. split; [exact Hfs|]. split; [exact Hfz|].
  split.
  { destruct Hmdl as (lz & mt & vm0 & fds0 & pins0 & Hmd & Hfd).
    pose proof Hcp as Hmd1'. apply AC.a_call_post_model in Hmd1'. destruct Hmd1' as (lz1 & mt1 & vm1 & Hmd1).
    exists lz1, mt1, vm1, fds0, pins0. split; [|exact Hfd].
    exact (md_shape_step (g_md g) md md' lz mt vm0 fds0 (m_fs (g_md g)) pins0 lz1 mt1 vm1 Hmd Hmd1). }
  split; [rewrite Hsk; exact Hslo|].
  split; [rewrite Hskh; exact Hshi|].
  split.
  { intros q k i Hin Hni Hi.
    destruct (r7_blocks (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin)))
      as (_ & Hq4 & Hend & _ & Hall).
    destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & Hnimg & _ & _).
    assert (Hqr : 0 <= q + i < 2 ^ 64)
      by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
    assert (Hinb : AC.in_blocks (g_H g) (q + i)) by (exists q, k; split; [exact Hin | lia]).
    assert (Hinb1 : AC.in_blocks (hb ++ g_H g) (q + i))
      by (exists q, k; split; [apply in_or_app; right; exact Hin | lia]).
    assert (HinH' : In (q, k) H')
      by (eapply Permutation_in; [exact Hperm | apply in_or_app; right; exact Hin]).
    assert (Hinb2 : AC.in_blocks H' (q + i)) by (exists q, k; split; [exact HinH' | lia]).
    assert (Hn1 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md (q + i))
      by exact ((r7_nown (hb ++ g_H g) mem md (q + i) HAH (or_introl Hinb1))).
    assert (Hn2 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' (q + i))
      by exact ((r7_nown H' mem' md' (q + i) Hah0 (or_introl Hinb2))).
    assert (Hnw : ~ AC.a_window K regs (q + i)) by (intro Hw; pose proof (Hwin2 _ Hw); lia).
    assert (Hne : ~ (AC.a_errno AC.ASYMS <= q + i < AC.a_errno AC.ASYMS + 4))
      by (intro He; exact (Hnimg (errno_in_img (q + i) He))).
    assert (Hno : q + i <> AC.as_oom AC.ASYMS) by (intro He; apply Hnimg; rewrite He; exact Hoomimg).
    assert (Hnt : ~ touched (q + i)) by (intro Ht; exact (proj2 (proj2 (proj2 (Hto (q + i) Ht))) Hinb)).
    rewrite (proj1 (Hfr (q + i) Hqr Hn1 Hn2 Hnw Hne Hno Hnt)).
    exact (Hblk q k i Hin Hni Hi). }
  split.
  { intros a Hia Ho1 Ho2 Hg He.
    pose proof (img_below_GT a Hia) as Hag. unfold AC.GT in Hag.
    assert (Ho2' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a)
      by (intro X; apply Ho2;
          exact (proj1 (ent_owned_img APIf (hb ++ g_H g) (hb' ++ g_H g) mem md mem' md' a HAH Hah' Hsk Htp Hia) X)).
    assert (Ho2'' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' a)
      by (intro X; apply Ho2; exact (proj2 (Hown' a Hia) X)).
    destruct (Himg a Hia Ho1 Ho2' Hg He) as (Hm0 & Hw0).
    destruct (Z.eq_dec a (AC.as_oom AC.ASYMS)) as [Eo|Eo].
    - subst a. destruct Hek as (_ & Hoomb).
      split; [rewrite Hoomb; exact Hm0|].
      split; intro X; [exact (proj1 Hoom (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hoom X))].
    - destruct (Hfr a ltac:(lia) Ho2' Ho2'' ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia) He Eo
                  ltac:(intro Ht; exact (proj1 (proj2 (proj2 (Hto a Ht))) Hia))) as (Hm & Hw).
      split; [rewrite Hm; exact Hm0|].
      split; intro X; [exact (proj1 Hw (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hw X))]. }
  split.
  { intros a Ha.
    assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) by lia.
    assert (Hst' : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md' <= a < APPMEM_END)
      by (rewrite Hsk; lia).
    assert (Hno : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a)
      by exact ((r7_nown (hb ++ g_H g) mem md a HAH
                  (or_intror (or_intror (or_intror Hst))))).
    assert (Hno' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' a)
      by exact ((r7_nown H' mem' md' a Hah0
                  (or_intror (or_intror (or_intror Hst'))))).
    destruct (Hfr a ltac:(lia) Hno Hno' ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia)
                ltac:(intro He; pose proof (img_below_GT _ (errno_in_img a He)) as X; unfold AC.GT in X; lia)
                ltac:(intro He; pose proof (img_below_GT _ Hoomimg) as X; unfold AC.GT in X; lia)
                ltac:(intro Ht; pose proof (proj1 (proj2 (Hto a Ht))); lia)) as (Hm & Hw).
    destruct (Habv a Ha) as (Hm0 & Hw0).
    split; [rewrite Hm; exact Hm0|].
    split; intro X; [exact (proj1 Hw (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hw X))]. }
  split.
  { intros a Hor.
    assert (Hb0 : 0 <= a)
      by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT a Hi) as X; unfold AC.GT in X|]; lia).
    assert (Hdiv : 0 <= a / 8 <= a) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (Hsh1 : in_shadow (shadow_addr a)).
    { apply shadow_of_app. destruct Hor as [Hi|Hr];
        [pose proof (img_below_GT a Hi) as X; unfold AC.GT, app_mem, LOWMEM_END in *; left; lia
        |unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia]. }
    assert (Hsr : 0 <= shadow_addr a < 2 ^ 64)
      by (destruct (in_shadow_range (shadow_addr a) Hsh1) as (R1 & R2); lia).
    assert (Hno : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md (shadow_addr a)).
    { destruct Hor as [Hi|Hr].
      - exact ((proj2 (r7_client (hb ++ g_H g) mem md a HAH)) Hi).
      - assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) by lia.
        exact ((r7_nown_sh (hb ++ g_H g) mem md a HAH
                  (or_intror (or_intror (or_intror Hst))))). }
    assert (Hno' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' (shadow_addr a)).
    { destruct Hor as [Hi|Hr].
      - exact ((proj2 (r7_client H' mem' md' a Hah0)) Hi).
      - assert (Hst' : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md' <= a < APPMEM_END)
          by (rewrite Hsk; lia).
        exact ((r7_nown_sh H' mem' md' a Hah0
                  (or_intror (or_intror (or_intror Hst'))))). }
    destruct (in_shadow_range (shadow_addr a) Hsh1) as (R1 & R2).
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh1.
    destruct (Hfr (shadow_addr a) ltac:(lia) Hno Hno'
                ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia)
                ltac:(intro He; pose proof (img_below_GT _ (errno_in_img _ He)) as X; unfold AC.GT in X; lia)
                ltac:(intro He; pose proof (img_below_GT _ Hoomimg) as X; unfold AC.GT in X;
                      rewrite <- He in X; lia)
                ltac:(intro Ht; pose proof (proj1 (Hto _ Ht)) as X;
                      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia)) as (Hm & _).
    rewrite Hm. exact (Hshd a Hor). }
  (* append #1: the shadow byte of an entry-block byte is owned in neither state (a_laws_not_owned, the block
     being a live block of both heaps) and is none of the window, errno, the flag and the new block *)
  split.
  { intros q k i Hin Hni Hi.
  destruct (r7_blocks (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (_ & Hq4 & Hend & _ & Hall).
  destruct (Hall (q + i) ltac:(lia)) as (Happq & _).
  assert (Hinb1 : AC.in_blocks (hb ++ g_H g) (q + i))
    by (exists q, k; split; [apply in_or_app; right; exact Hin | lia]).
  assert (HinH' : In (q, k) H')
    by (eapply Permutation_in; [exact Hperm | apply in_or_app; right; exact Hin]).
  assert (Hinb2 : AC.in_blocks H' (q + i)) by (exists q, k; split; [exact HinH' | lia]).
  pose proof (r7_nown_sh (hb ++ g_H g) mem md (q + i) HAH (or_introl Hinb1)) as Hno.
  pose proof (r7_nown_sh H' mem' md' (q + i) Hah0 (or_introl Hinb2)) as Hno'.
  pose proof (shadow_of_app (q + i) Happq) as Hsh1.
  destruct (in_shadow_range (shadow_addr (q + i)) Hsh1) as (R1 & R2).
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh1.
  destruct (Hfr (shadow_addr (q + i)) ltac:(lia) Hno Hno'
              ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia)
              ltac:(intro He; pose proof (img_below_GT _ (errno_in_img _ He)) as X; unfold AC.GT in X; lia)
              ltac:(intro He; pose proof (img_below_GT _ Hoomimg) as X; unfold AC.GT in X;
                    rewrite <- He in X; lia)
              ltac:(intro Ht; pose proof (proj1 (Hto _ Ht)) as X;
                    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia)) as (Hm & _).
  rewrite Hm. exact (Hkshd q k i Hin Hni Hi). }
  (* #14 (the per-class fact) names only the ghost: the same witness (Tac_slot's ent_class_of; ent_class_call
     states it for a post heap hb' ++ g_H g, while the allocator's post heap H' here is a permutation of it). *)
  exact (ent_class_of APIf g hb mem md HENT).
Qed.

(* ---- the allocator call ----
   0x81760 jal wrapper_malloc (0x534b8): the ONE use of the frame's allocator contract aa_malloc (Contract.v
   amalloc_at) in this file, so a later allocator-contract change breaks this lemma only.  Its class premises
   come from ENT's 14th conjunct (Tac_cls.sl_malloc_cls, Bc = Bc_of BE: the entry heap's share BE plus the slot's
   own share BC_ctrl); the rest from the caller. *)
Lemma r7_malloc : forall g regs mem md n (P : config -> Prop),
  ENT APIf g [] mem md ->
  AC.a_call_pre AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
    AC.AK_MALLOC (g_H g) regs mem md ->
  getr regs 10 = Z_to_bv 64 n -> 0 <= n <= AC.ANMAX ->
  AC.a_live_bytes (g_H g) + AC.a_size n <= AC.ALIVE_MAX -> AC.a_place_room (g_H g) (AC.a_size n) ->
  (forall c', AC.amalloc_ret AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
      (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
      (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc)) AC.AK_MALLOC (g_H g) regs mem md n c' -> SR rsegs c' P) ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 0x534b8) mem (seg_rom rsegs)) md) P.
Proof.
  intros g regs mem md n P HENT HPRE E10 Hn Hlive Hroom K.
  pose proof (AC.aa_malloc AC.ASYMS AsanRTInv.RT (APIf rc)) as HMAL.
  unfold AC.amalloc_contract, AC.amalloc_at in HMAL.
  assert (EM : AC.as_malloc AC.ASYMS = 0x534b8) by reflexivity.
  destruct (Tac_cls.sl_malloc_cls APIf g [] mem md n HENT) as (BE & _ & _ & HBc1 & HBc2 & _).
  eapply (SR_bind rsegs); [|exact K].
  rewrite <- EM.
  exact (HMAL (g_H g) regs mem md n (Tac_cls.Bc_of BE) HPRE E10 Hn Hlive Hroom HBc1 HBc2).
Qed.

(* ---- the segment lemma ---- *)

Lemma seg_R7 : forall b : nat, Hat B APIf ra (Inv_B81764_at B APIf ra) b -> Hat B APIf ra (Inv_B81ac0_at B APIf ra) b -> Hat B APIf ra (Inv_B81710_at B APIf ra) b.
Proof.
  intros b Hexit Hlatch g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & A & Ec & HFRA & HENT & Hgn & Hb6 & Hnmax & Hsz &
    HA64 & Hr9 & Hr21 & Ha0 & Hmag & HRBE & HIDB & HFGB & HRTF & Hr22 & HOUR & HCUR & HX544 & HZ6 & Hr27).
  subst c. rewrite SEGS.
  unfold OUTA in HX544.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9' & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HSbnd : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HA'64 : 0 <= A' < 2 ^ 64) by lia.
  assert (HAeq : A' = A) by exact (r7_rg_eq regs 9 A' A Hr9' Hr9 HA'64 HA64).
  subst A'.
  destruct (Z.eq_dec (rnb g b) 0) as [Hz|Hnz].
  { (* a zero count: 0x81710 beqz a0,0x81ac0 is taken, to the round-trip latch *)
    apply (sl_run regs (Z_to_bv 64 0x81710) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x81ac0 /\ mem' = mem /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
         getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
         getr R 18 = getr regs 18 /\ getr R 27 = getr regs 27)
      (Post B APIf ra g)).
    - exact Hhalt.
    - rewrite r7_mkR_of.
      eapply evt_mono.
      + eapply r7_evt0. unfold a0v, rg in Ha0. rewrite Ha0, Hz. reflexivity.
      + intros ms' (R & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P21 & P22 & P23 & P24 & P25 & P26 & P18 & P27).
        exists R, (Z_to_bv 64 0x81ac0), mem. split; [exact Hms|].
        split; [reflexivity|]. split; [reflexivity|].
        split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
        split; [exact P9|]. split; [exact P19|]. split; [exact P21|]. split; [exact P22|].
        split; [exact P23|]. split; [exact P24|]. split; [exact P25|]. split; [exact P26|].
        split; [exact P18 | exact P27].
    - intros R pc' mem' regs'' md'
        (Hpc & Hmem & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & K18 & K27) Hreg Hmat.
      subst pc' mem'.
      assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
      assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
      assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
      assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
      assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
      assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
      assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
      assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
      assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
      assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
      assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
      assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
      assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
      assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
      pose proof (r7_rbe_move g fr regs regs'' mem E9 HRBE) as HRBE''.
      rewrite <- SEGS. apply Hlatch.
      exists regs'', mem, md', fr.
      split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr [] regs regs'' mem md md' HFRA);
          [exact E2 | exact E3 | exact E4 | exact E8 | exact E9 | exact E19 | exact E26 | exact Hmat]. }
      split; [eapply ent_mat; [exact HENT | exact Hmat]|].
      split; [exact Hgn|].
      split; [exact Hb6|].
      split; [unfold rg in *; rewrite E22; exact Hr22|].
      split.
      { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
        split; [exact Hc0|]. split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]. }
      split; [exact HOUR|].
      split; [unfold RID; rewrite (r7_st_skip (g_in g) b Hz); exact HIDB|].
      split; [unfold RFG; rewrite (r7_st_skip (g_in g) b Hz); exact HFGB|].
      split; [exact HRBE''|].
      split; [unfold rg in *; rewrite E21; exact Hr21|].
      split; [exact (r6x_of_rbe g (S b) fr regs'' mem HRBE'')|].
      unfold rg in *; rewrite E27; exact Hr27. }
  (* a non-zero count: the checks pass and the allocator is called *)
  assert (HNV : r7_nv (rnb g b)) by exact (r7_rnb_nv (g_in g) (Z.of_nat b) Hnz).
  assert (HNR : 124 <= rnb g b <= 1492) by exact (r7_nv_range _ HNV).
  (* frame placement and the stack window *)
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  pose proof (sl_frame_apart_win B APIf ra g fr [] regs mem md HFRA) as HAPART.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HERRv : AC.a_errno AC.ASYMS = 6145452) by reflexivity.
  assert (HOOMv : AC.as_oom AC.ASYMS = 1227040) by reflexivity.
  assert (HGTv : AC.GT = 6283264) by reflexivity.
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  rewrite Haspz in Hlo, Hstkw, HAPART.
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  (* the magic word, as the engine's read-only cell *)
  assert (ROmag : ro_cells rsegs mem (bv_unsigned (getr regs 9) + 128) [C8 (Z_to_bv 64 0xe38f0000)])
    by (rewrite HbvA; exact (r7_ro8 mem (A + 128) 0xe38f0000 Hmag)).
  (* the run: 21 instructions to the allocator's entry 0x534b8 *)
  apply (sl_run regs (Z_to_bv 64 0x81710) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x534b8 /\ mem' = mem /\
       getr R 1 = Z_to_bv 64 0x81764 /\ getr R 10 = Z_to_bv 64 (rnb g b) /\
       getr R 18 = Z_to_bv 64 (rnb g b) /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 27 = getr regs 27)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite r7_mkR_of.
    eapply evt_mono.
    + eapply r7_evt; [exact Ha0 | exact Hr21 | exact HNV | exact ROmag].
    + intros ms' (R & Hms & P1 & P10 & P18 & P2 & P3 & P4 & P8 & P9 & P19 & P21 & P22 & P23 & P24 & P25 & P26 &
                  P27).
      exists R, (Z_to_bv 64 0x534b8), mem. split; [exact Hms|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact P1|]. split; [exact P10|]. split; [exact P18|].
      split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P21|]. split; [exact P22|]. split; [exact P23|].
      split; [exact P24|]. split; [exact P25|]. split; [exact P26 | exact P27].
  - intros R pc' mem' regs'' md'
      (Hpc & Hmem & K1 & K10 & K18 & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & K27)
      Hreg Hmat.
    subst pc' mem'.
    assert (E1 : getr regs'' 1 = Z_to_bv 64 0x81764) by (rewrite Hreg; exact K1).
    assert (E10 : getr regs'' 10 = Z_to_bv 64 (rnb g b)) by (rewrite Hreg; exact K10).
    assert (E18 : getr regs'' 18 = Z_to_bv 64 (rnb g b)) by (rewrite Hreg; exact K18).
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
    assert (HFRAc : FRA B APIf ra g fr [] regs'' mem md')
      by (apply (sl_fra_move B APIf ra g fr [] regs regs'' mem md md' HFRA);
          [exact E2 | exact E3 | exact E4 | exact E8 | exact E9 | exact E19 | exact E26 | exact Hmat]).
    assert (HENTc : ENT APIf g [] mem md') by (eapply ent_mat; [exact HENT | exact Hmat]).
    destruct (r7_mat_le (g_H g) mem md md' Hmat) as (HAHm & _ & Hlom & Hhim).
    assert (HAH' : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) mem md') by exact (HAHm HAH).
    assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md')
      by exact (AC.a_laws_stack_high _ _ _ _ _ ALAWS (g_H g) mem md' HAH').
    (* the allocation pre at the call, from FRA + ENT *)
    assert (HPREc : AC.a_call_pre AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
                      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
                      AC.AK_MALLOC (g_H g) regs'' mem md').
    { apply (fra_call_pre B APIf ra g fr [] regs'' mem md' AC.AK_MALLOC HFRAc HENTc).
      - unfold YK0s.ret_ok. rewrite E1. vm_compute. reflexivity.
      - unfold AC.AK_MALLOC. rewrite HFN. lia. }
    (* the allocator, on the frame's law (r7_malloc; its class premises from ENT's 14th conjunct) *)
    apply (r7_malloc g regs'' mem md' (rnb g b) _ HENTc HPREc E10 Hnmax).
    + unfold AC.ALIVE_MAX, AC.a_size in *. lia.
    + left. unfold AC.a_size, AC.A_PRIMARY_MAX. lia.
    + intros c' (regs3 & mem3 & md3 & q & Ec' & Hqa0 & HNB & HPOST & HKERR & HOWN0).
      assert (Hsize : AC.a_size (rnb g b) = rnb g b) by (unfold AC.a_size; lia).
      rewrite Hsize in HNB, HPOST, HOWN0.
      rewrite E1 in Ec'. subst c'.
      (* the post's projections *)
      pose proof HPOST as HAH3; apply AC.a_call_post_ah in HAH3.
      pose proof HPOST as HKR; apply AC.a_call_post_regs in HKR.
      pose proof HPOST as HMOD; apply AC.a_call_post_model in HMOD.
      pose proof HPOST as HSTK3; apply AC.a_call_post_stklo in HSTK3.
      pose proof HPOST as HRO3; apply AC.a_call_post_ro in HRO3.
      assert (HTP3 : forall i, 0 <= i < 16 ->
                mbyte rsegs mem3 (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
        by (eapply AC.a_call_post_tp; exact HPOST).
      assert (HWIN3 : forall a, AC.a_window AC.AK_MALLOC regs'' a -> writable_at rsegs mem3 a)
        by (eapply AC.a_call_post_win_writable; exact HPOST).
      assert (HWP : forall a, AC.a_window AC.AK_MALLOC regs'' a -> exists bb, mbyte rsegs mem3 a = Some bb)
        by (eapply AC.a_call_post_win_present; exact HPOST).
      assert (HFRM : forall a, 0 <= a < 2 ^ 64 ->
                ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) mem md' a ->
                ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g ++ [(q, rnb g b)]) mem3 md3 a ->
                ~ AC.a_window AC.AK_MALLOC regs'' a ->
                ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) -> a <> AC.as_oom AC.ASYMS ->
                ~ (q <= a < q + rnb g b) ->
                mbyte rsegs mem3 a = mbyte rsegs mem a /\
                (writable_at rsegs mem a <-> writable_at rsegs mem3 a))
        by (eapply AC.a_call_post_frame; exact HPOST).
      destruct HNB as (Hqnz & Hqal & Hq4096 & Hqlo & Hqapp & Hqbytes & Hqaddr & Hqslack & Hqslack2).
      (* callee-saved registers *)
      assert (G2 : getr regs3 2 = getr regs'' 2)
        by (apply (r7_regs_kept_at regs'' regs3 2 2 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G3 : getr regs3 3 = getr regs'' 3)
        by (apply (r7_regs_kept_at regs'' regs3 3 3 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G4 : getr regs3 4 = getr regs'' 4)
        by (apply (r7_regs_kept_at regs'' regs3 4 4 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G8 : getr regs3 8 = getr regs'' 8)
        by (apply (r7_regs_kept_at regs'' regs3 8 8 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G9 : getr regs3 9 = getr regs'' 9)
        by (apply (r7_regs_kept_at regs'' regs3 9 9 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G19 : getr regs3 19 = getr regs'' 19)
        by (apply (r7_regs_kept_at regs'' regs3 19 19 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G21 : getr regs3 21 = getr regs'' 21)
        by (apply (r7_regs_kept_at regs'' regs3 21 21 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G22 : getr regs3 22 = getr regs'' 22)
        by (apply (r7_regs_kept_at regs'' regs3 22 22 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G23 : getr regs3 23 = getr regs'' 23)
        by (apply (r7_regs_kept_at regs'' regs3 23 23 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G24 : getr regs3 24 = getr regs'' 24)
        by (apply (r7_regs_kept_at regs'' regs3 24 24 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G25 : getr regs3 25 = getr regs'' 25)
        by (apply (r7_regs_kept_at regs'' regs3 25 25 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G26 : getr regs3 26 = getr regs'' 26)
        by (apply (r7_regs_kept_at regs'' regs3 26 26 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G18 : getr regs3 18 = getr regs'' 18)
        by (apply (r7_regs_kept_at regs'' regs3 18 18 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      assert (G27 : getr regs3 27 = getr regs'' 27)
        by (apply (r7_regs_kept_at regs'' regs3 27 27 HKR ltac:(unfold AC.a_callee_saved; lia));
            apply bv_eq; reflexivity).
      (* the window of the allocator entry, in the caller's terms *)
      assert (Haspc : AC.aspZ regs'' = sp) by (unfold AC.aspZ; rewrite E2; exact Haspz).
      assert (HWv : forall x, AC.a_window AC.AK_MALLOC regs'' x <-> sp - 4096 <= x < sp)
        by (intros x; unfold AC.a_window, AC.AK_MALLOC; rewrite Haspc; tauto).
      (* ownership classes: the real stack, the side stack, their shadow bytes, the client cells and the shadow
         bytes of image bytes are never the allocator's, in either state *)
      assert (NO1 : forall x, AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END \/
                      AC.a_in_fs AC.ASYMS mem x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) mem md' x /\
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) mem md' (shadow_addr x)).
      { intros x Hx. apply (r7_nown_both (g_H g) mem md' x HAH').
        destruct Hx as [Hx|Hx]; [right; right; right; exact Hx | right; right; left; exact Hx]. }
      assert (Hfsmem : forall x, AC.a_in_fs AC.ASYMS mem x -> AC.a_in_fs AC.ASYMS mem3 x).
      { intros x (FSb & HFSr & Hw & Hr). exists FSb. split; [exact HFSr|]. split; [|exact Hr].
        intros k Hk. rewrite (HTP3 (Z.of_nat k) ltac:(lia)). exact (Hw k Hk). }
      assert (NO2 : forall x, AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END \/
                      AC.a_in_fs AC.ASYMS mem x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g ++ [(q, rnb g b)]) mem3 md3 x /\
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g ++ [(q, rnb g b)]) mem3 md3
                          (shadow_addr x)).
      { intros x Hx.
        apply (r7_nown_both (g_H g ++ [(q, rnb g b)]) mem3 md3 x HAH3).
        destruct Hx as [Hx|Hx]; [right; right; right; rewrite HSTK3; exact Hx
                                | right; right; left; exact (Hfsmem x Hx)]. }
      assert (NOc1 : forall x, AC.in_blocks AC.a_client x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) mem md' x)
        by (intros x Hx; exact (proj1 (r7_client (g_H g) mem md' x HAH') Hx)).
      assert (NOc2 : forall x, AC.in_blocks AC.a_client x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g ++ [(q, rnb g b)]) mem3 md3 x)
        by (intros x Hx; exact (proj1 (r7_client (g_H g ++ [(q, rnb g b)]) mem3 md3 x
              HAH3) Hx)).
      assert (NOi1 : forall x, AC.a_in_img x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) mem md' (shadow_addr x))
        by (intros x Hx; exact ((proj2 (r7_client (g_H g) mem md' x HAH')) Hx)).
      assert (NOi2 : forall x, AC.a_in_img x ->
                      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g ++ [(q, rnb g b)]) mem3 md3
                          (shadow_addr x))
        by (intros x Hx; exact ((proj2 (r7_client (g_H g ++ [(q, rnb g b)]) mem3 md3
              x HAH3)) Hx)).
      (* the new block's bytes are app memory off the image *)
      assert (Hqin : In (q, rnb g b) (g_H g ++ [(q, rnb g b)]))
        by (apply in_or_app; right; left; reflexivity).
      assert (Hqappm : forall x, q <= x < q + rnb g b -> app_mem x /\ ~ AC.a_in_img x).
      { intros x Hx.
        destruct (r7_blocks (g_H g ++ [(q, rnb g b)]) mem3 md3 q (rnb g b) HAH3 Hqin)
          as (_ & _ & _ & _ & Hb).
        destruct (Hb x Hx) as (Ha1 & _ & Ha3 & _). split; [exact Ha1 | exact Ha3]. }
      assert (Hqstk : q + rnb g b <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md')
        by (rewrite <- HSTK3; exact Hqlo).
      (* THE TRANSPORT: a byte the allocator entry may not touch keeps its value and its writability *)
      assert (KEEP : forall x, 0 <= x < 2 ^ 64 ->
                ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) mem md' x ->
                ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g ++ [(q, rnb g b)]) mem3 md3 x ->
                ~ (sp - 4096 <= x < sp) ->
                ~ (AC.a_errno AC.ASYMS <= x < AC.a_errno AC.ASYMS + 4) -> x <> AC.as_oom AC.ASYMS ->
                ~ (q <= x < q + rnb g b) ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                (writable_at rsegs mem x <-> writable_at rsegs mem3 x)).
      { intros x Hx No1 No2 Nw Ne Noo Nt.
        apply (HFRM x Hx No1 No2); [ intro Hc; apply Nw; exact (proj1 (HWv x) Hc)
                                   | exact Ne | exact Noo | exact Nt]. }
      (* class A: the real stack at or above sp *)
      assert (KST : forall x, sp <= x <= g_S g ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                (writable_at rsegs mem x <-> writable_at rsegs mem3 x)).
      { intros x Hx. apply KEEP; try lia.
        - apply NO1. left. lia.
        - apply NO2. left. lia. }
      (* class F: the side stack's bytes *)
      assert (KFS : forall x, AC.a_in_fs AC.ASYMS mem x ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                (writable_at rsegs mem x <-> writable_at rsegs mem3 x)).
      { intros x Hx. pose proof Hx as Hx'. destruct Hx' as (FSb & HFSr & Hw & Hr).
        destruct (r7_fs_place (g_H g) mem md' FSb HAH' Hw HFSr)
          as (HGT & Hend & _ & Happ).
        pose proof (Happ x Hr) as Happx.
        unfold app_mem in Happx.
        apply KEEP.
        - lia.
        - exact (proj1 (NO1 x (or_intror Hx))).
        - exact (proj1 (NO2 x (or_intror Hx))).
        - lia.
        - lia.
        - lia.
        - intro Hc. exact (proj1 (proj2 (proj2 (proj2 (Hqbytes x Hc)))) (Hfsmem x Hx)). }
      (* the frame bytes are on the real stack or in the side stack *)
      assert (HFRC : forall x, fr <= x < fr + FRAME_BYTES ->
                AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END \/
                AC.a_in_fs AC.ASYMS mem x).
      { intros x Hx. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
        - left. rewrite Hlom. exact (Hreal x Hx).
        - right. exact (Hfs x Hx). }
      (* class B: the frame, on either arm *)
      assert (KFR : forall x, fr <= x < fr + FRAME_BYTES ->
                mbyte rsegs mem3 x = mbyte rsegs mem x /\
                (writable_at rsegs mem x <-> writable_at rsegs mem3 x)).
      { intros x Hx. destruct (HFRC x Hx) as [Hc|Hc]; [|exact (KFS x Hc)].
        apply KEEP.
        - unfold HIGHMEM_BEG in Hhigh. lia.
        - exact (proj1 (NO1 x (or_introl Hc))).
        - exact (proj1 (NO2 x (or_introl Hc))).
        - intro Hc2. exact (HAPART x Hx Hc2).
        - lia.
        - lia.
        - lia. }
      (* class C: the shadow bytes of real-stack and side-stack bytes *)
      assert (KSHX : forall x, AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END \/
                       AC.a_in_fs AC.ASYMS mem x ->
                mbyte rsegs mem3 (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
      { intros x Hcls.
        assert (Happx : app_mem x).
        { destruct Hcls as [Hc|Hc].
          - unfold app_mem. lia.
          - destruct Hc as (FSb & HFSr & Hw & Hr).
            destruct (r7_fs_place (g_H g) mem md' FSb HAH' Hw HFSr)
              as (_ & _ & _ & Happ). exact (Happ x Hr). }
        assert (Hshd : in_shadow (shadow_addr x)) by (apply shadow_of_app; exact Happx).
        pose proof (in_shadow_range _ Hshd) as Hrr.
        pose proof Hshd as Hshd'.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hshd'.
        refine (proj1 (KEEP (shadow_addr x) _ _ _ _ _ _ _)).
        - lia.
        - exact (proj2 (NO1 _ Hcls)).
        - exact (proj2 (NO2 _ Hcls)).
        - lia.
        - lia.
        - lia.
        - intro Hc. destruct (Hqappm _ Hc) as (Happq & _).
          exact (app_not_shadow _ Happq Hshd). }
      assert (KSH : forall x, 0 <= x < FRAME_SHADOW ->
                mbyte rsegs mem3 (Sfr fr + x) = mbyte rsegs mem (Sfr fr + x)).
      { intros x Hx. rewrite <- r7_sh8. apply KSHX. apply HFRC. lia. }
      (* class D: the shadow bytes of the image (the registered globals, the row-name strings, the catalogue row) *)
      assert (KAG : forall x, AC.a_in_img x ->
                mbyte rsegs mem3 (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
      { intros x Hx.
        pose proof (r7_img_range x Hx) as Himgb.
        assert (Hshd : in_shadow (shadow_addr x)) by (apply shadow_of_app; unfold app_mem; lia).
        pose proof (in_shadow_range _ Hshd) as Hrr.
        pose proof Hshd as Hshd'.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hshd'.
        refine (proj1 (KEEP (shadow_addr x) _ _ _ _ _ _ _)).
        - lia.
        - exact (NOi1 x Hx).
        - exact (NOi2 x Hx).
        - lia.
        - lia.
        - lia.
        - intro Hc. destruct (Hqappm _ Hc) as (Happx & _).
          exact (app_not_shadow _ Happx Hshd). }
      (* class E: the musl client cells the sink words live in *)
      assert (KCL : forall x, AC.in_blocks AC.a_client x -> AC.a_in_img x ->
                ~ (AC.a_errno AC.ASYMS <= x < AC.a_errno AC.ASYMS + 4) -> x <> AC.as_oom AC.ASYMS ->
                mbyte rsegs mem3 x = mbyte rsegs mem x).
      { intros x Hcl Himg Ne Noo.
        pose proof (r7_img_range x Himg) as Hr.
        refine (proj1 (KEEP x _ _ _ _ _ _ _)).
        - lia.
        - exact (NOc1 x Hcl).
        - exact (NOc2 x Hcl).
        - lia.
        - exact Ne.
        - exact Noo.
        - intro Hc. exact (proj2 (Hqappm x Hc) Himg). }
      (* class G: the image's read-only bytes (box bytes at BOXA, the catalogue's row-name strings) *)
      assert (KRO : forall x, 0x21140 <= x < 0x218f0 -> mbyte rsegs mem3 x = mbyte rsegs mem x).
      { intros x Hx.
        assert (Hroin : AC.a_in_ro x) by (apply r7_ro_in; lia).
        refine (proj1 (KEEP x _ _ _ _ _ _ _)).
        - lia.
        - exact (AC.a_laws_ro_not_owned _ _ _ _ _ ALAWS (g_H g) mem md' x HAH' Hroin).
        - exact (AC.a_laws_ro_not_owned _ _ _ _ _ ALAWS (g_H g ++ [(q, rnb g b)]) mem3 md3 x HAH3 Hroin).
        - lia.
        - lia.
        - lia.
        - intro Hc. exact (proj2 (Hqappm x Hc) (r7_ro_img x Hroin)). }
      (* class H: the image's RELRO bytes (the row table at BA_FR + 72, the catalogue row at mrow): frame_facts
         says the runtime owns none of them, in any state *)
      pose proof FF as (_ & _ & _ & _ & Hhead & Hlock & Hthr & _ & _ & _ & HRimg & HOWNG & _).
      assert (KRELRO : forall x, 0x9f168 <= x < 0x9f168 + 9344 -> mbyte rsegs mem3 x = mbyte rsegs mem x).
      { intros x Hx. pose proof (r7_relro_in x Hx) as Hin.
        refine (proj1 (KEEP x _ _ _ _ _ _ _)).
        - lia.
        - exact (fun X => proj2 (HOWNG rc _ _ _ _ X) Hin).
        - exact (fun X => proj2 (HOWNG rc _ _ _ _ X) Hin).
        - lia.
        - lia.
        - lia.
        - intro Hc. exact (proj2 (Hqappm x Hc) (HRimg x Hin)). }
      (* the input block's bytes (a live block of g_H g for g_n > 0): kept, and its shadow bytes kept *)
      assert (KINP : forall x, g_p g <= x < g_p g + g_n g -> mbyte rsegs mem3 x = mbyte rsegs mem x).
      { intros x Hx.
        assert (Hn0 : 0 < g_n g) by lia.
        destruct (Hinblk Hn0) as (Hin & _).
        destruct (fra_in_apart B APIf ra g fr [] regs mem md HFRA x Hx) as (Happ & Hlo2 & Hnfr & Himg).
        assert (Hr64 : 0 <= x < 2 ^ 64)
          by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happ; lia).
        assert (Hinb1 : AC.in_blocks (g_H g) x) by (exists (g_p g), (g_n g); split; [exact Hin | lia]).
        refine (proj1 (KEEP x _ _ _ _ _ _ _)).
        - exact Hr64.
        - exact ((r7_nown (g_H g) mem md' x HAH' (or_introl Hinb1))).
        - assert (Hinb2 : AC.in_blocks (g_H g ++ [(q, rnb g b)]) x)
            by (exists (g_p g), (g_n g); split; [apply in_or_app; left; exact Hin | lia]).
          exact ((r7_nown (g_H g ++ [(q, rnb g b)]) mem3 md3 x HAH3
                    (or_introl Hinb2))).
        - lia.
        - intro He. exact (Himg (errno_in_img x He)).
        - intro He. apply Himg. rewrite He. exact oom_in_img.
        - intro Hc. exact (proj1 (Hqbytes x Hc) Hinb1). }
      assert (KINPSH : forall x, g_p g <= x < g_p g + g_n g ->
                mbyte rsegs mem3 (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
      { intros x Hx.
        assert (Hn0 : 0 < g_n g) by lia.
        destruct (Hinblk Hn0) as (Hin & _).
        destruct (fra_in_apart B APIf ra g fr [] regs mem md HFRA x Hx) as (Happ & Hlo2 & Hnfr & Himg).
        assert (Hinb1 : AC.in_blocks (g_H g) x) by (exists (g_p g), (g_n g); split; [exact Hin | lia]).
        assert (Hshd : in_shadow (shadow_addr x)) by (apply shadow_of_app; exact Happ).
        pose proof (in_shadow_range _ Hshd) as Hrr.
        pose proof Hshd as Hshd'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hshd'.
        refine (proj1 (KEEP (shadow_addr x) _ _ _ _ _ _ _)).
        - lia.
        - exact ((r7_nown_sh (g_H g) mem md' x HAH' (or_introl Hinb1))).
        - assert (Hinb2 : AC.in_blocks (g_H g ++ [(q, rnb g b)]) x)
            by (exists (g_p g), (g_n g); split; [apply in_or_app; left; exact Hin | lia]).
          exact ((r7_nown_sh (g_H g ++ [(q, rnb g b)]) mem3 md3 x HAH3
                    (or_introl Hinb2))).
        - lia.
        - lia.
        - lia.
        - intro Hc. destruct (Hqappm _ Hc) as (Happq & _). exact (app_not_shadow _ Happq Hshd). }
      (* the RELRO globals stay image-agreeing *)
      assert (Hgimg3 : G_img_c B AF.frame_RELRO mem3).
      { intros a Ha. pose proof (Hgimg a Ha) as Hg0. pose proof (r7_relro_range a Ha) as Hra.
        rewrite SEGS in Hg0 |- *.
        destruct (KEEP a ltac:(lia)
                    (fun X => proj2 (HOWNG rc _ _ _ _ X) Ha) (fun X => proj2 (HOWNG rc _ _ _ _ X) Ha)
                    ltac:(lia) ltac:(lia) ltac:(lia)
                    (fun Hc => proj2 (Hqappm a Hc) (HRimg a Ha))) as (Hmb & _).
        rewrite Hmb. exact Hg0. }
      assert (Hsn3 : sink_none B mem3 md3).
      { pose proof HFRAc as (A2 & sp2 & s52 & _ & _ & _ & Hsnc & _).
        destruct Hsnc as ((Hthrm & Hlockm) & Hohd & Hfd).
        destruct HMOD as (lz & mt & vm' & Emd3).
        split; [split|split].
        - eapply YI14.val_mem_frame; [|exact Hthrm].
          intros x Hx. rewrite Hthr in Hx. cbn in Hx. try rewrite SEGS.
          apply KCL.
          + apply r7_client_a. lia.
          + exact (r7_img_cov_in 0x5fc8e1 0x5fc8e2 x r7_sink_cov_a ltac:(lia)).
          + lia.
          + lia.
        - eapply YI14.val_mem_frame; [|exact Hlockm].
          intros x Hx. rewrite Hlock in Hx. cbn in Hx. try rewrite SEGS.
          apply KCL.
          + apply r7_client_b. lia.
          + exact (r7_img_cov_in 0x5fcd40 0x5fcd50 x r7_sink_cov_b ltac:(lia)).
          + lia.
          + lia.
        - intros k Hk. pose proof (Hohd k Hk) as Hk'.
          try rewrite SEGS in Hk'. try rewrite SEGS.
          rewrite KCL.
          + exact Hk'.
          + apply r7_client_b. rewrite Hhead. lia.
          + eapply r7_img_cov_in; [exact r7_sink_cov_b | rewrite Hhead; lia].
          + rewrite Hhead. lia.
          + rewrite Hhead. lia.
        - rewrite Emd3. exact Hfd. }
      assert (Hwin3 : stk rsegs mem3 (g_S g - AF.SLOT_STACK) (g_S g)).
      { pose proof Hwin as HwinD. destruct HwinD as (W0 & W1 & W).
        split; [exact W0|]. split; [exact W1|].
        intros x Hx.
        destruct (Z_lt_le_dec x sp) as [Hbelow|Habove].
        - destruct (Z_lt_le_dec x (sp - 4096)) as [Hlow|Hupw].
          + assert (Hcls : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' <= x < APPMEM_END) by lia.
            destruct (W x Hx) as (Hw & bb & Hb).
            destruct (KEEP x ltac:(lia) (proj1 (NO1 x (or_introl Hcls)))
                        (proj1 (NO2 x (or_introl Hcls))) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(lia)) as (Hmb & Hwr).
            split; [exact (proj1 Hwr Hw)|]. exists bb. rewrite <- Hb. exact Hmb.
          + assert (Hwx : AC.a_window AC.AK_MALLOC regs'' x) by (apply (HWv x); lia).
            split; [exact (HWIN3 x Hwx) | exact (HWP x Hwx)].
        - destruct (W x Hx) as (Hw & bb & Hb).
          destruct (KST x ltac:(lia)) as (Hmb & Hwr).
          split; [exact (proj1 Hwr Hw)|]. exists bb. rewrite <- Hb. exact Hmb. }
      assert (HAG3 : forall a, in_globals AF.frame_AG a -> addressable mem3 a 1).
      { intros a Hin. apply (r7_addr_keep mem mem3 a 1 (HAG a Hin)).
        intros i Hi. replace (a + i) with a by lia. apply KAG. exact (r7_ag_img a Hin). }
      (* the slot window outside the frame stays addressable: its shadow bytes are real-stack shadow *)
      assert (HWA3 : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) ->
                addressable mem3 a 1).
      { intros a H1 H2. apply (r7_addr_keep mem mem3 a 1 (HWA a H1 H2)).
        intros i Hi. replace (a + i) with a by lia. apply KSHX. left. rewrite Hlom. lia. }
      (* the frame record of the side arm *)
      assert (HREC3 : FSREC fr mem -> FSREC fr mem3).
      { intros HR. apply (r7_fsrec_keep mem mem3 fr HR HTP3).
        intros x Hx _. exact (proj1 (KFS x Hx)). }
      (* the spills and the frame words at mem3 *)
      assert (Q336 : q64 mem3 (A + 336) fr).
      { apply (r7_keep_bytes mem mem3 _ _ Hspill). rewrite length_le8.
        change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KST x ltac:(lia))). }
      assert (Q40 : q64 mem3 (A + 40) fr).
      { apply (r7_keep_bytes mem mem3 _ _ Hfr56). rewrite length_le8.
        change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KST x ltac:(lia))). }
      assert (Qsaved : bytes_at rsegs mem3 (g_S g - 104) (saved_bytes ra g)).
      { apply (r7_keep_bytes mem mem3 _ _ Hsaved).
        unfold saved_bytes. rewrite !length_app, !length_le8. cbn [Nat.add].
        change (Z.of_nat 104) with 104. intros x Hx. exact (proj1 (KST x ltac:(lia))). }
      assert (Qhdr1 : q64 mem3 fr 0x41b58ab3).
      { apply (r7_keep_bytes mem mem3 _ _ Hhdr1). rewrite length_le8.
        change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (Qhdr2 : q64 mem3 (fr + 16) AF.ENTRY).
      { apply (r7_keep_bytes mem mem3 _ _ Hhdr2). rewrite length_le8.
        change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (QOUR : OURb g fr mem3).
      { unfold OURb in *. apply (r7_keep_bytes mem mem3 _ _ HOUR). rewrite OUR_length.
        change (Z.of_nat 6) with 6. intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (Qsh : exists sh, bytes_at rsegs mem3 (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
      { destruct Hsh as (sh & Hb & Hl). exists sh. split; [|exact Hl].
        apply (r7_keep_bytes mem mem3 _ _ Hb). rewrite Hl, FRAME_SHADOW_val.
        change (Z.of_nat (Z.to_nat 392)) with 392. intros x Hx.
        replace x with (Sfr fr + (x - Sfr fr)) by lia. apply KSH. lia. }
      assert (QCUR : CUR g 7 regs3).
      { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
        split; [exact Hc0|]. split; [rewrite G23, E23; exact Hc23 | rewrite G25, E25; exact Hc25]. }
      (* the input facts at mem3 (for sl_mid_perm) *)
      assert (HINPb : bytes_at rsegs mem3 (g_p g) (g_in g)).
      { apply (r7_keep_bytes mem mem3 _ _ Hinb). intros x Hx. apply KINP. exact Hx. }
      assert (HINPad : 0 < g_n g -> addressable mem3 (g_p g) (g_n g)).
      { intro Hn0. destruct (Hinblk Hn0) as (_ & Had).
        apply (r7_addr_keep mem mem3 (g_p g) (g_n g) Had).
        intros i Hi. apply KINPSH. lia. }
      (* FRA at the exit *)
      assert (Hperm : Permutation (hb1 q (rnb g b) ++ g_H g) (g_H g ++ [(q, rnb g b)]))
        by (unfold hb1; apply Permutation_app_comm).
      assert (HFRAx : FRA B APIf ra g fr (hb1 q (rnb g b)) regs3 mem3 md3).
      { apply (sl_mid_perm B APIf ra g fr [] (hb1 q (rnb g b)) (g_H g ++ [(q, rnb g b)]) regs'' mem md'
                 regs3 mem3 md3 (fun a => q <= a < q + rnb g b) AC.AK_MALLOC HFRAc HPOST Hperm).
        - unfold hb1. cbn [length]. lia.
        - exact Hsn3.
        - exact Hgimg3.
        - exact Qhdr1.
        - exact Qhdr2.
        - intros A2 HA2 HA2r. rewrite E9 in HA2.
          assert (EA2 : A2 = A) by exact (r7_rg_eq regs 9 A2 A HA2 Hr9 HA2r HA64). subst A2. exact Q336.
        - intros A2 HA2 HA2r v Hv. rewrite E9 in HA2.
          assert (EA2 : A2 = A) by exact (r7_rg_eq regs 9 A2 A HA2 Hr9 HA2r HA64). subst A2.
          apply (r7_keep_bytes mem mem3 _ _ Hv). rewrite length_le8.
          change (Z.of_nat 8) with 8. intros x Hx. exact (proj1 (KST x ltac:(lia))).
        - intros A2 HA2 HA2r. rewrite E9 in HA2.
          assert (EA2 : A2 = A) by exact (r7_rg_eq regs 9 A2 A HA2 Hr9 HA2r HA64). subst A2. exact Q40.
        - exact Qsh.
        - exact Qsaved.
        - exact Hwin3.
        - exact HAG3.
        - exact HWA3.
        - exact HREC3.
        - exact HINPb.
        - exact HINPad.
        - rewrite G2; reflexivity.
        - rewrite G3; reflexivity.
        - rewrite G4; reflexivity.
        - rewrite G8; reflexivity.
        - rewrite G9; reflexivity.
        - rewrite G19; reflexivity.
        - rewrite G26; reflexivity. }
      (* ENT at the exit *)
      assert (HENTx : ENT APIf g (hb1 q (rnb g b)) mem3 md3).
      { apply (r7_ent_call g fr [] (hb1 q (rnb g b)) (g_H g ++ [(q, rnb g b)]) regs'' mem md' regs3 mem3 md3
                 (fun a => q <= a < q + rnb g b) AC.AK_MALLOC HENTc HFRAc HPOST Hperm).
        - unfold AC.AK_MALLOC. rewrite HFN. lia.
        - intros a Ha. destruct (Hqappm a Ha) as (Happ & Himg).
          split; [exact Happ|]. split; [lia|]. split; [exact Himg|].
          exact (proj1 (Hqbytes a Ha)).
        - exact HKERR. }
      (* RBE at the exit: the spills (above the spill base A >= sp), OUTA and the identity record's 38 bytes
         (frame bytes, kept through their shadow), the row-name clause (read-only image), our[] addressable, the
         row table / box / catalogue-row bytes and the fragment record's 72 addressable bytes (frame shadow) *)
      assert (HRBE3 : RBE g fr regs3 mem3).
      { assert (E9' : getr regs3 9 = getr regs 9) by (rewrite G9; exact E9).
        assert (HA0 : 0 <= A) by lia.
        assert (HA1 : A + 448 <= 2 ^ 64) by lia.
        assert (HKA : forall off, 0 <= off <= 440 -> forall x, A + off <= x < A + off + 8 ->
                  mbyte rsegs mem3 x = mbyte rsegs mem x)
          by (intros off Hoff x Hx; exact (proj1 (KST x ltac:(lia)))).
        assert (SKP : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs3 mem3 off v)
          by (intros off v Hoff Hs;
              exact (r7_spill_keep regs regs3 mem mem3 A off v Hr9 HA0 HA1 Hoff E9' (HKA off Hoff) Hs)).
        destruct HRBE as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
                          S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUTA & Hid38 & HNM & Hour6 &
                          Htbl & Hbox & Hmrow & HPRA & S152 & S112 & H2256 & S160).
        unfold RBE.
        do 21 (split; [apply SKP; [lia | assumption]|]).
        split.
        { unfold OUTA in *. apply (r7_addr_keep mem mem3 (fr + 544) 1492 HOUTA).
          intros i Hi. apply KSHX. apply HFRC. lia. }
        split.
        { apply (r7_addr_keep mem mem3 (fr + 2176) 38 Hid38).
          intros i Hi. apply KSHX. apply HFRC. lia. }
        split.
        { intros Hnm. destruct (HNM Hnm) as (Hok & Hbs & Had & Hpos & Hhi).
          destruct Hnm as (Hh & Hrn).
          pose proof (r7_rname (g_in g) Hh Hrn) as Hrng.
          pose proof (r7_nb_len (g_in g)) as Hlen.
          split; [exact Hok|]. split.
          - apply (r7_keep_bytes mem mem3 _ _ Hbs). intros x Hx. apply KRO. lia.
          - split; [|split; [exact Hpos | exact Hhi]].
            apply (r7_addr_keep mem mem3 _ _ Had). intros i Hi. apply KAG. apply r7_ro_img. apply r7_ro_in.
            lia. }
        split.
        { apply (r7_addr_keep mem mem3 (fr + 2624) 6 Hour6).
          intros i Hi. apply KSHX. apply HFRC. lia. }
        split.
        { apply (r7_keep_bytes mem mem3 _ _ Htbl). rewrite r7_tbl_len.
          assert (EBA : BAC.BA_FR = 656896) by reflexivity.
          intros x Hx. apply KRELRO. rewrite EBA in Hx. lia. }
        split.
        { apply (r7_keep_bytes mem mem3 _ _ Hbox).
          assert (Hl6 : Z.of_nat (length box6) = 6) by reflexivity.
          assert (EBOX : BOXA = 135488) by reflexivity.
          rewrite Hl6. intros x Hx. apply KRO. rewrite EBOX in Hx. lia. }
        split.
        { apply (r7_keep_bytes mem mem3 _ _ Hmrow). rewrite r7_mb_len.
          pose proof (r7_mrow_range (g_in g)) as Hmr.
          intros x Hx. apply KRELRO. lia. }
        split.
        { unfold PRA in *. destruct HPRA as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11).
          do 10 (split; [apply SKP; [lia | assumption]|]). apply SKP; [lia | assumption]. }
        split; [apply SKP; [lia | exact S152]|].
        split; [apply SKP; [lia | exact S112]|].
        split.
        { apply (r7_addr_keep mem mem3 (fr + 2256) 72 H2256).
          intros i Hi. apply KSHX. apply HFRC. lia. }
        apply SKP; [lia | exact S160]. }
      (* the turn records and out[]'s frame bytes rt_F (the bytes R8's copy reads): frame bytes, kept *)
      assert (QIDB : IDBr g fr (RID (g_in g) b) mem3).
      { unfold IDBr in *. apply (r7_keep_bytes mem mem3 _ _ HIDB). rewrite RtmB.rb_RID_len.
        intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (QFGB : FGBr g fr (RFG (g_in g) b) mem3).
      { unfold FGBr in *. apply (r7_keep_bytes mem mem3 _ _ HFGB). rewrite (RtmB.rb_RFG_len (g_in g) b ltac:(lia)).
        intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      assert (QRTF : bytes_at rsegs mem3 (fr + 544) (rt_F (g_in g) (Z.of_nat b))).
      { destruct (RtmB.rb_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & _ & HFl).
        apply (r7_keep_bytes mem mem3 _ _ (HRTF Hnz)). rewrite HFl. fold (rnb g b). rewrite Z2Nat.id by lia.
        intros x Hx. exact (proj1 (KFR x ltac:(lia))). }
      (* the out[] buffer's rnb bytes stay addressable: their shadow bytes are frame shadow *)
      assert (Qaddr : addressable mem3 (fr + 544) (rnb g b)).
      { apply (r7_addr_keep mem mem3 (fr + 544) (rnb g b)
                 (addressable_prefix mem (fr + 544) 1492 (rnb g b) HX544 ltac:(lia))).
        intros i Hi. apply KSHX. apply HFRC. lia. }
      (* the exit cut *)
      rewrite <- SEGS. apply Hexit.
      exists q, regs3, mem3, md3, fr.
      split; [reflexivity|].
      split; [exact HFRAx|].
      split; [exact HENTx|].
      split; [exact Hgn|].
      split; [exact Hb6|].
      split; [exact Hnz|].
      split; [unfold a0v, rg; exact Hqa0|].
      split; [split; [exact Hqnz | rewrite Hsize; exact Hqaddr]|].
      split; [unfold rg; rewrite G18; exact E18|].
      split; [exact HRBE3|].
      split; [unfold rg in *; rewrite G21, E21; exact Hr21|].
      split; [exact QIDB|].
      split; [exact QFGB|].
      split; [exact QRTF|].
      split; [unfold rg in *; rewrite G22, E22; exact Hr22|].
      split; [exact QOUR|].
      split; [exact QCUR|].
      split; [exact Qaddr|].
      unfold rg in *. rewrite G27, E27. exact Hr27.
Qed.

End R7.
