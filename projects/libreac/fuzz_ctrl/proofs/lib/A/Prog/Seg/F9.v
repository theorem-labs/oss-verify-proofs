(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 2560 of its 2603 lines of code are new or changed and 353 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F6.v, with its module paths, module names and addresses changed; 2503 of its 3129 lines of code are new or changed and 1977 lines of the source are left out. *)
(* Segment F9 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): 0x81f88-0x81ff0, through the call
   `jal reac_ctrl_identity_reply@0x81ff0` to its return point 0x81ff4, with the out-of-line slow paths
   0x82984-0x8298c (back to 0x81f98) and 0x8299c-0x829a4 (back to 0x81fb8).

   0x81f88-0x81f94 is an instrumented 1-byte check of the name byte at a0 = kind_name_addr (t_k ...) (the result of
   the kind_name call at 0x81f84): it loads the shadow byte at (a0 >> 3) + s10 (s10 = ASAN_K) and compares it with
   0; when that byte is not 0 the slow path 0x82984 compares (a0 land 7) with it and returns to 0x81f98. Both arms
   are proved and the error call 0x82cb4 is NOT reached, because the name bytes are addressable: the name address
   is one of the registered globals (AF.frame_AG), whose bytes FRA carries as addressable.
   0x81f98 lbu a1,0(a0) reads the first name byte; it is not 63 ('?') because the kind is t_k (g_in g) j <= 13
   (RcParse.ctrlparse_kind_range) and no kind_names entry starts with '?', so `bne a1,63` at 0x81fa0 goes to
   0x81fc0 and neither the second checked byte (0x81fa4-0x81fb4, slow path 0x8299c) nor the `beqz a0,82bf4` at
   0x81fbc is reached.
   0x81fc0-0x81fe4 writes the three frame shadow bytes S(fr)+32, +34, +38 (byte 2, then 0, 0) and the three frame
   cells [s1+256] = fr+256 (2 bytes), [s1+272] = fr+272 (8), [s1+264] = fr+304 (8), all zero; then 0x81fe8-0x81fec
   put a0 = s7 = phi and a1 = s2 = len and 0x81ff0 calls reac_ctrl_identity_reply, composed on its lib/A contract
   (reac_ctrl_identity_reply_c.v, a Section Hypothesis), landing at the F10 entry 0x81ff4.

   Entry cut SlotInv.Inv_A81f88_at, exit cut SlotInv.Inv_A81ff4_at (the official texts). The contract asks for
   mem_inv, which no cut carries: the call runs on MemNorm.normalize of the memory and comes back through
   MemNorm.evt_normalize (f9_evtB), with lib/A/RoAdapt.v's transports for its premises and post and three local ones
   RoAdapt does not carry (the thread cells f9_tls_rel, the side-stack placement f9_place_rel and the frame-pointer
   bundle f9_fp_rel). The frame's placement against the callee's window is SlotInv.fra_frame's K-form (f9_PL_of),
   the callee's window comes from SlotInv.fra_win and FRA's window conjunct. The carry of the span (FLSI, LK, b5_C,
   b5_K, IDj, b5_F17, b5_W240, b5_PF) is written by no instruction of F9 and by no part of the contract's post:
   it moves across the six stores and the call by munch transport (f9_exit_of). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcReply RcParse RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib RcAsanFP
  asan_stack_malloc_c reac_ctrl_kind_name_c reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
(* `Frame` and `MState` alone can resolve to the UL copies that the Seg helpers load; pin them to lib/Lib. *)
Module Frame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module MState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.

Ltac f9_bjoin G r := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => exact (G (Sem.reg_get R r)) end.

Ltac f9_until_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; f9_until_if
  | _ => idtac
  end.

(* One instrumented 1-byte check of the byte X (srli; add s10; lb; bnez; slow path andi/bge/j), the error call not
   reached: the register r is generalized at the join. *)

Ltac f9_chk X r k RK OK :=
  step; rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
  step; step; clear RK; f9_until_if;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (pose proof (rc_byte_signed k); lia);
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?Bb) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evt segs Q (MS (bvmap_set r rr R) F Bb fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ f9_bjoin G r
        | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7;
          step;
          rewrite (rc_lts_signed (X mod 8) (bv_signed k))
            by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); pose proof (rc_byte_signed k); lia);
          replace (X mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia);
          cbn [negb]; cbv iota; step;
          f9_bjoin G r ]
      | intros ?; simp_regs; clear OK ]
  end.

(* The six byte ranges F9 writes before the call (0x81fc4-0x81fe4). *)

Definition f9_WA (S3 fr : Z) : list ivl :=
  [(S3 + 32, S3 + 33); (fr + 256, fr + 258); (S3 + 34, S3 + 35); (fr + 272, fr + 280);
   (S3 + 38, S3 + 39); (fr + 304, fr + 312)].

Lemma f9_neq63 : forall c : byte, bv_unsigned c <> 63 -> bv_eqb (zxb c) (Z_to_bv 64 63) = false.
Proof.
  intros c H. apply Bool.not_true_iff_false. intro HC. apply bv_eqb_eq in HC.
  apply (f_equal (bv_unsigned (n:=64))) in HC. unfold zxb in HC.
  pose proof (bv_unsigned_in_range 8 c) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N 8) with 256 in Hr.
  rewrite !MState.unsigned_lit in HC by lia. lia.
Qed.

Lemma f9_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0 in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by lia. exact HH.
Qed.

Lemma f9_pres_one : forall bs m (a x : word) v, m x = Some v ->
  exists w, write_to_mem m a bs x = Some w.
Proof.
  induction bs as [|b bs IH]; intros m a x v H; cbn; [exists v; exact H|].
  destruct (bv_eqb x a) eqn:E.
  - apply (IH _ _ _ b). rewrite E. reflexivity.
  - apply (IH _ _ _ v). rewrite E. exact H.
Qed.

Lemma f9_pres : forall m (a : word) bs q,
  (exists b, mbyte rsegs m q = Some b) -> exists b, mbyte rsegs (write_to_mem m a bs) q = Some b.
Proof.
  intros m a bs q H. unfold mbyte in *.
  destruct (m (Z_to_bv 64 q)) as [v|] eqn:E.
  - destruct (f9_pres_one bs m a (Z_to_bv 64 q) v E) as (w & Hw). rewrite Hw. exists w. reflexivity.
  - destruct (write_to_mem m a bs (Z_to_bv 64 q)) as [w|] eqn:E2; [exists w; reflexivity | exact H].
Qed.

(* store_ok for the current memory, from a wr_at of the original memory. *)

Ltac f9_sok W a k n :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "HS" in
      assert (H : store_ok rsegs mm (wa (a + k)) n = true)
        by (eapply (wr_at_store_ok rsegs mm a _ k n); [repeat apply wr_at_write; exact W | lia | lia]);
      rewrite ?Z.add_0_r in H
  end.

(* Every byte of [a, a + n) readable gives a byte list there. *)

Lemma f9_bytes_ex : forall m (n : nat) a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat i)) = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b & Hb). change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hbs & Hl).
    { intros i Hi. destruct (H (S i) ltac:(lia)) as (b' & Hb'). exists b'.
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact Hb'. }
    exists (b :: bs). split; [|cbn; lia].
    destruct Hbs as (H0 & H1 & H2). split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact Hb.
    + cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply H2. cbn in Hi. lia.
Qed.

(* A spill read in the current memory, from a bytes_at of the original memory. *)

Ltac f9_rdcur a v H :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let R := fresh "RL" in
      assert (R : ov_read_bytes rsegs mm (wa a) 8 = Some (le8 (Z_to_bv 64 v)))
        by (apply f9_rd8;
            [ repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia]); exact H
            | apply length_le8 ])
  end.

Ltac f9_bw :=
  repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia]).

(* 0x81f88 - 0x81fe4: the checked read of the name byte at a0 = X (not '?'), then the three frame shadow bytes and
   the three frame cells. *)

Lemma f9_evtA :
  forall (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Q : machine_state -> Prop)
         (X A S3 fr phi len : Z) (b c0 : byte),
    0 <= X < 2 ^ 47 -> 0 <= S3 -> 0 <= fr -> 0 <= A ->
    fr + FRAME_BYTES <= A -> A + 416 <= 2 ^ 64 -> S3 + FRAME_SHADOW <= A ->
    (S3 + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= S3) ->
    ov_read_bytes rsegs m (wa (X / 8 + ASAN_K)) 1 = Some [b] ->
    (bv_signed b = 0 \/ X mod 8 < bv_signed b) ->
    ov_read_bytes rsegs m (wa X) 1 = Some [c0] -> bv_unsigned c0 <> 63 ->
    wr_at rsegs m S3 FRAME_SHADOW ->
    wr_at rsegs m (fr + 256) 2 -> wr_at rsegs m (fr + 272) 8 -> wr_at rsegs m (fr + 304) 8 ->
    bytes_at rsegs m (A + 256) (le8 (Z_to_bv 64 (fr + 256))) ->
    bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 (fr + 272))) ->
    bytes_at rsegs m (A + 264) (le8 (Z_to_bv 64 (fr + 304))) ->
    (forall (m1 : word -> option byte),
       munch (f9_WA S3 fr) m m1 -> wmono rsegs m m1 ->
       (forall q, (exists bq, mbyte rsegs m q = Some bq) -> exists bq, mbyte rsegs m1 q = Some bq) ->
       bytes_at rsegs m1 (S3 + 32) (le1 (Z_to_bv 64 2)) ->
       bytes_at rsegs m1 (S3 + 34) (le1 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (S3 + 38) (le1 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (fr + 256) (le2 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (fr + 272) (le8 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (fr + 304) (le8 (Z_to_bv 64 0)) ->
       wr_at rsegs m1 (fr + 256) 2 -> wr_at rsegs m1 (fr + 272) 8 -> wr_at rsegs m1 (fr + 304) 8 ->
       Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 2) (zxb c0) (Z_to_bv 64 (fr + 256))
                  (Z_to_bv 64 (fr + 272)) (Z_to_bv 64 (fr + 304)) a5 a6 a7
                  (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi) s8 s9 (Z_to_bv 64 ASAN_K) s11
                  t3 t4 t5 t6)
             Fr (Z_to_bv 64 0x81fe8) fc None m1 (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi) s8 s9 (Z_to_bv 64 ASAN_K) s11
               t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f88) fc None m (seg_rom rsegs)).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6
    Fr fc m Q X A S3 fr phi len b c0 HX HS30 Hfr0 HA0 HfrA HA64 HS3A HS3fr
    RK OK RC0 HC0 Wsh Wa Wp Wn Q256 Q272 Q264 HQ.
  (* 0x81f88-0x81f94 the instrumented check of the byte X *)
  f9_chk X (Z_to_bv 5 12) b RK OK.
  (* 0x81f98 lbu a1,0(a0) ; 0x81f9c li a2,63 ; 0x81fa0 bne a1,a2 taken to 0x81fc0 *)
  step. step. step. rewrite (f9_neq63 c0 HC0). cbn [negb]. cbv iota.
  (* 0x81fc0 li a0,2 ; 0x81fc4 sb a0,32(s3) *)
  step.
  f9_sok Wsh S3 32 1%nat. step.
  (* 0x81fc8 ld a2,256(s1) ; 0x81fcc sh zero,0(a2) *)
  f9_rdcur (A + 256) (fr + 256) Q256. step.
  f9_sok Wa (fr + 256) 0 2%nat. step.
  (* 0x81fd0 sb zero,34(s3) *)
  f9_sok Wsh S3 34 1%nat. step.
  (* 0x81fd4 ld a3,272(s1) ; 0x81fd8 sd zero,0(a3) *)
  f9_rdcur (A + 272) (fr + 272) Q272. step.
  f9_sok Wp (fr + 272) 0 8%nat. step.
  (* 0x81fdc sb zero,38(s3) *)
  f9_sok Wsh S3 38 1%nat. step.
  (* 0x81fe0 ld a4,264(s1) ; 0x81fe4 sd zero,0(a4) *)
  f9_rdcur (A + 264) (fr + 304) Q264. step.
  f9_sok Wn (fr + 304) 0 8%nat. step.
  apply evt_done. apply HQ.
  - cbv [f9_WA].
    repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
    apply munch_refl.
  - repeat apply wmono_write. apply wmono_refl.
  - intros q Hq. repeat apply f9_pres. exact Hq.
  - f9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - repeat apply wr_at_write. exact Wa.
  - repeat apply wr_at_write. exact Wp.
  - repeat apply wr_at_write. exact Wn.
Qed.

Lemma l5_addr_keep : forall m m' W p n,
  addressable m p n -> Frame.munch W m m' ->
  (forall i, 0 <= i < n -> Frame.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros m m' W p n (H1 & H2 & H3 & H) MU HW.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|].
  exists b. split; [|exact Hk].
  assert (Hr : 0 <= shadow_addr (p + i) < 2 ^ 64).
  { unfold shadow_addr, ASAN_K. unfold APPMEM_END in H3. Z.div_mod_to_equations. lia. }
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by exact Hr. exact (HW i Hi).
Qed.

(* The shadow map is monotone, and strictly so across a whole granule. *)

Lemma l5_sh_mono : forall x y, 0 <= x <= y -> shadow_addr x <= shadow_addr y.
Proof.
  intros x y H. unfold shadow_addr. pose proof (Z.div_le_mono x y 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma l5_sh_lt : forall x y, 0 <= x -> x + 8 <= y -> shadow_addr x < shadow_addr y.
Proof.
  intros x y H0 H. unfold shadow_addr.
  pose proof (Z.div_le_mono (x + 1 * 8) y 8 ltac:(lia) ltac:(lia)) as Hm.
  rewrite Z.div_add in Hm by lia. lia.
Qed.

(* The allocator laws this file takes apart (a_laws_blocks, a_laws_fs_place, a_laws_fs_store) and a_fs_ok, each
   taken apart once here and used by name at every site (a Theorem Labs lane's rule for generated laws until N+1). Each law is
   split by decompose and each fact is found by its type, not by its position: a conjunct appended at any level is
   one more unused hypothesis here. f9_fs_ok_of builds a_fs_ok, so it names every conjunct; it is the one line a
   new a_fs_ok conjunct changes. a_laws_thread and a_laws_fs_state are f9_thread / f9_fs_state (Section S_l1). *)
Section S_laws.
Context {fx : YK11.FPState}.

Lemma f9_blocks : forall Bs AH own lo hi, AC.a_laws Bs AH own lo hi ->
  forall H mem md p n, AH H mem md -> In (p, n) H ->
  4096 <= p /\ p + n <= lo mem md /\ (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_fs Bs mem a).
Proof.
  intros Bs AH own lo hi L H mem md p n HAH Hin.
  pose proof (AC.a_laws_blocks _ _ _ _ _ L H mem md p n HAH Hin) as X. decompose [and] X. clear X.
  split; [assumption|]. split; [assumption|].
  intros a Ha.
  lazymatch goal with HP : forall x, p <= x < p + n -> _ |- _ => pose proof (HP a Ha) as Y end.
  decompose [and] Y. split; assumption.
Qed.

Lemma f9_fs_place : forall Bs AH own lo hi, AC.a_laws Bs AH own lo hi ->
  forall H mem md b, AH H mem md -> word_mem rsegs mem (AC.as_tp Bs) b -> 0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= lo mem md /\ b mod 4096 = 0 /\
  (forall a, b <= a < b + AC.FS_SIZE -> app_mem a).
Proof.
  intros Bs AH own lo hi L H mem md b HAH Hw Hb.
  pose proof (AC.a_laws_fs_place _ _ _ _ _ L H mem md b HAH Hw Hb) as X. decompose [and] X. clear X.
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Lemma f9_fs_store : forall Bs AH own lo hi, AC.a_laws Bs AH own lo hi ->
  forall H mem mem' md FS, AH H mem md -> word_mem rsegs mem (AC.as_tp Bs) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (lo mem md) a -> ~ (FS <= a < FS + AC.FS_SIZE) ->
     ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.a_fs_ok mem' FS ->
  AH H mem' md /\ (forall a, own H mem' md a <-> own H mem md a) /\ lo mem' md = lo mem md /\
  hi mem' md = hi mem md.
Proof.
  intros Bs AH own lo hi L H mem mem' md FS HAH Hw HFS Hag Hwm Hok.
  pose proof (AC.a_laws_fs_store _ _ _ _ _ L H mem mem' md FS HAH Hw HFS Hag Hwm Hok) as X.
  decompose [and] X. clear X.
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Lemma f9_fs_ok_to : forall mem FS, AC.a_fs_ok mem FS ->
  word_mem rsegs mem (FS + 88) 20 /\ mbyte rsegs mem (FS + 96) = Some (Z_to_bv 8 0) /\
  (forall c, (c <= 10)%nat -> exists h, word_mem rsegs mem (AC.a_fs_hint FS c) h) /\
  (forall c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 1)).
Proof.
  intros mem FS X. unfold AC.a_fs_ok in X. decompose [and] X. clear X.
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Lemma f9_fs_ok_of : forall mem FS,
  (forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b) ->
  word_mem rsegs mem (FS + 88) 20 -> mbyte rsegs mem (FS + 96) = Some (Z_to_bv 8 0) ->
  (forall c, (c <= 10)%nat -> exists h, word_mem rsegs mem (AC.a_fs_hint FS c) h) ->
  (forall c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 1)) ->
  AC.a_fs_ok mem FS.
Proof. intros mem FS H1 H2 H3 H4 H5. exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))). Qed.

End S_laws.

Section S_l5.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The FIRST body a frame-loop state carries has at most 23 bytes: fs0's is empty and an opening turn takes at
   most the 23 bytes of the 50-byte record from offset 27 (SlotModel.turn). FSb's bytes_at at fr + 2880 so lies
   inside the 35-byte object first.sroa.7. *)
Lemma f9_fs_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens _ _); cbn [fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

(* The frame placement this segment's stores and the callee need: the frame in app memory above GT, apart from the
   callee's window [sp - 9072, sp) with one granule to spare (fra_frame's K-form at K = 9072 + 8), below the spill
   base, and, when it lies in the FakeStack FS, above FS's class-6 frames and inside FS. *)
Definition f9_PL (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\ AC.GT <= fr /\
  (fr + FRAME_BYTES + 8 <= AC.aspZ regs - 9072 \/ AC.aspZ regs <= fr) /\
  (forall A, rg regs 9 A -> 0 <= A < 2 ^ 64 -> fr + FRAME_BYTES <= A) /\
  (forall FS, word_mem rsegs m (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS <= fr < FS + AC.FS_SIZE ->
     FS + 36864 + 6 * 2 ^ 20 <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE).

(* f9_PL from the base: fra_app, fra_frame (K-form at K = 9080 <= FN_STACK, the spill base, the FakeStack bound)
   and b5_FS's FS-conditional containment. *)
Lemma f9_PL_of : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md -> b5_FS fr mem -> f9_PL fr regs mem.
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros g fr hb regs mem md HFRA (HFS1 & _).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hapart & H9 & HFSfr & _).
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  split; [exact Happ|]. split; [exact Hgt|].
  split; [destruct (Hapart 9080 ltac:(lia)) as [H|H]; [left | right]; lia|].
  split.
  { intros A HA HAr. unfold rg in HA. rewrite HA, MState.unsigned_lit in H9 by lia. exact H9. }
  intros FS Hw HFSr Hin. split.
  - pose proof (HFSfr FS Hw HFSr). lia.
  - exact (HFS1 FS Hw HFSr Hin).
Qed.


(* The heap block (phi, len) lies below stklo <= sp - SLOT_STACK, so it is apart from the callee's stack window and
   below 2^64; 4096 <= phi. Holds for any 0 <= len. *)

Lemma l5_dj0 : forall g fr phi len hb regs mem md,
  FRA B APIf ra g fr ((phi, len) :: hb) regs mem md -> 0 <= len ->
  (phi + 50 <= AC.aspZ regs - 9072 \/ AC.aspZ regs <= phi) /\
  phi + 50 <= 2 ^ 64 /\ 0 < phi.
Proof.
  intros g fr phi len hb regs mem md HFRA Hlen.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWAf &
    HTop1 & HTop2 & HTop3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (f9_blocks _ _ _ _ _ LAWS _ _ _ phi len HAH ltac:(cbn; left; reflexivity)) as (Hp4096 & Hpst & _).
  destruct Hwin as (Hw0 & Hw1 & _).
  rewrite Haspz. unfold AF.SLOT_STACK in *.
  split; [left; lia|]. split; lia.
Qed.

(* A nonempty heap block's first byte is not in the side stack (a_laws_blocks: no block byte is a_in_fs). *)

Lemma l5_notfs : forall g fr phi len hb regs mem md,
  FRA B APIf ra g fr ((phi, len) :: hb) regs mem md -> 0 < len -> ~ AC.a_in_fs AC.ASYMS mem phi.
Proof.
  intros g fr phi len hb regs mem md HFRA Hlen.
  destruct HFRA as (A & sp & s5 & HRT & HAH & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (f9_blocks _ _ _ _ _ LAWS _ _ _ phi len HAH ltac:(cbn; left; reflexivity)) as (_ & _ & Hbyte).
  exact (proj2 (Hbyte phi ltac:(lia))).
Qed.

(* The full disjointness: the block is also apart from the frame cells [fr + 256, fr + 312). Real arm: phi + len <=
   stklo <= fr. Side arm (frame in the side stack FS): phi is not a_in_fs, so phi is below FS (hence below the frame)
   or at or above FS + FS_SIZE (hence above the frame). *)

Lemma l5_dj1 : forall g fr phi len hb regs mem md,
  FRA B APIf ra g fr ((phi, len) :: hb) regs mem md -> f9_PL fr regs mem -> 0 <= len ->
  ~ AC.a_in_fs AC.ASYMS mem phi ->
  (phi + 50 <= fr + 256 \/ fr + 312 <= phi) /\
  (phi + 50 <= AC.aspZ regs - 9072 \/ AC.aspZ regs <= phi) /\
  phi + 50 <= 2 ^ 64 /\ 0 < phi.
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros g fr phi len hb regs mem md HFRA HPL Hlen Hnfs.
  split; [|exact (l5_dj0 g fr phi len hb regs mem md HFRA Hlen)].
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWAf &
    HTop1 & HTop2 & HTop3 & Hhb & Hlive).
  destruct HPL as (Happ & Hgt & _ & _ & HFSb).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (f9_blocks _ _ _ _ _ LAWS _ _ _ phi len HAH ltac:(cbn; left; reflexivity)) as (Hp4096 & Hpst & _).
  assert (Hspb : sp <= 2 ^ 64) by (destruct Hwin as (_ & Hb & _); lia).
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. destruct Ha as [Ha|Ha]; lia. }
  destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
  - (* real arm: phi + len <= stklo <= fr *)
    left. destruct (Hreal fr ltac:(lia)) as (Hr & _). lia.
  - (* side arm: the FS base b at tp, with the frame in [b + 36864 + 6 * 2^20, b + FS_SIZE) *)
    destruct (Hfs fr ltac:(lia)) as (b & Hbr & Hwb & Hblo & Hbhi).
    destruct (HFSb b Hwb Hbr ltac:(lia)) as (Hlo36 & Hhi36).
    destruct (Z_lt_le_dec phi b) as [Hl|Hg].
    + left. lia.
    + destruct (Z_lt_le_dec phi (b + AC.FS_SIZE)) as [Hl2|Hg2].
      * exfalso. apply Hnfs. exists b. split; [exact Hbr | split; [exact Hwb | lia]].
      * right. lia.
Qed.

(* The nonempty-block case: l5_dj1 with l5_notfs. *)

Lemma l5_dj : forall g fr phi len hb regs mem md,
  FRA B APIf ra g fr ((phi, len) :: hb) regs mem md -> f9_PL fr regs mem -> 0 < len ->
  (phi + 50 <= fr + 256 \/ fr + 312 <= phi) /\
  (phi + 50 <= AC.aspZ regs - 9072 \/ AC.aspZ regs <= phi) /\
  phi + 50 <= 2 ^ 64 /\ 0 < phi.
Proof.
  intros g fr phi len hb regs mem md HFRA HPL Hlen.
  exact (l5_dj1 g fr phi len hb regs mem md HFRA HPL ltac:(lia) (l5_notfs g fr phi len hb regs mem md HFRA Hlen)).
Qed.

End S_l5.

Definition f9_pre (phi len pa pp pn S FS TP : Z) (m : word -> option byte) (G ja jp jn : list byte) : Prop :=
  0 <= phi < 2^64 /\ 0 <= len < 2^64 /\ 0 <= pa < 2^64 /\ 0 <= pp < 2^64 /\ 0 <= pn < 2^64 /\
  S < 2^64 /\ S mod 16 = 0 /\
  REAC_CTRL_IDENTITY_REPLY_K <= S /\ stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S /\
  ro_agree rsegs m /\ length G = 50%nat /\
  (reply_args phi pa pp pn = true -> 50 <= len ->
     phi + 50 <= 2^64 /\ bytes_at rsegs m phi G /\
     (phi + 50 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= phi)) /\
  (reply_args phi pa pp pn = true ->
     pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
     rw_cells rsegs m pa [CB 2 ja] /\ rw_cells rsegs m pp [CB 8 jp] /\ rw_cells rsegs m pn [CB 8 jn] /\
     (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
     (pa + 2 <= phi \/ phi + 50 <= pa) /\ (pp + 8 <= phi \/ phi + 50 <= pp) /\ (pn + 8 <= phi \/ phi + 50 <= pn) /\
     (pa + 2 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pa) /\
     (pp + 8 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pp) /\
     (pn + 8 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pn)) /\
  asan_cells m /\ shadow_rw m /\
  HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K /\ S <= APPMEM_END /\
  addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
  (reply_args phi pa pp pn = true -> 50 <= len -> addressable m phi 50) /\
  (reply_args phi pa pp pn = true ->
     addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
     (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) /\
  addressable m REAC_CTRL_PARSE_BC 6 /\
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] /\
  fp [1%nat] m TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
    (reac_ctrl_identity_reply_W phi pa pp pn S) (reac_ctrl_identity_reply_D phi len pa pp pn) /\
  reac_ctrl_identity_reply_tls m TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S.

(* ---- The call on the normalized memory (MemNorm): the contract asks for mem_inv, which no cut carries. RoAdapt
   (lib/A/RoAdapt.v) moves stk, rw_cells, asan_cells, shadow_rw and addressable across mem_rel; the three bundles
   it does not carry are below: the thread cells, the side-stack placement and the frame-pointer bundle. ---- *)

Lemma f9_stk_norm : forall m m0 lo hi, mem_rel rsegs m m0 -> 6283264 <= lo ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi REL Hlo H. apply (rel_stk_norm m m0 lo hi REL); [|exact H].
  destruct H as (_ & Hb & _). intros x Hx. apply ro_addr_false_hi. lia.
Qed.

Lemma f9_rw_norm : forall m m0 a cs, mem_rel rsegs m m0 -> 6283264 <= a ->
  rw_cells rsegs m a cs -> rw_cells rsegs m0 a cs.
Proof.
  intros m m0 a cs REL Ha H. apply (rel_rw_norm m m0 a cs REL); [|exact H].
  destruct H as (_ & (_ & Hb & _)). intros i Hi. apply ro_addr_false_hi. lia.
Qed.

(* The thread cells (asan_tls_cells) are bytes_at facts. *)
Lemma f9_tls_tr : forall m m0 TP DT TS C T DB k,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  asan_tls_cells m TP DT TS C T DB k -> asan_tls_cells m0 TP DT TS C T DB k.
Proof.
  intros m m0 TP DT TS C T DB k R H.
  destruct H as (H1 & H2 & H3 & H4 & H5 & Hk & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15
                 & H16 & H17 & HDB & H19).
  unfold asan_tls_cells.
  split; [exact (R _ _ H1)|]. split; [exact (R _ _ H2)|]. split; [exact (R _ _ H3)|].
  split; [exact (R _ _ H4)|]. split; [exact (R _ _ H5)|]. split; [exact Hk|].
  split; [exact (R _ _ H7)|]. split; [exact (R _ _ H8)|]. split; [exact (R _ _ H9)|].
  split; [exact (R _ _ H10)|]. split; [exists tb, te; exact (R _ _ H11)|].
  split; [exact (R _ _ H12)|]. split; [exact (R _ _ H13)|]. split; [exact (R _ _ H14)|].
  split; [exact (R _ _ H15)|]. split; [exact (R _ _ H16)|]. split; [exact (R _ _ H17)|].
  split; [exact HDB|]. exact (R _ _ H19).
Qed.

Lemma f9_tls_rel : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  (asan_tls_cells m TP DT TS C T DB k <-> asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k REL. split; apply f9_tls_tr; intros a bs H.
  - exact (proj1 (bytes_at_rel rsegs m m0 a bs REL) H).
  - exact (proj2 (bytes_at_rel rsegs m m0 a bs REL) H).
Qed.

(* The side-stack placement (fs_place): its stk lies at or above ASAN_GT, so above every read-only byte. *)
Lemma f9_place_rel : forall m m0 FS, mem_rel rsegs m m0 -> (fs_place m FS <-> fs_place m0 FS).
Proof.
  intros m m0 FS REL. unfold fs_place.
  split; intros (P1 & P2 & P3 & P4 & P5); (split; [exact P1|]); (split; [exact P2|]); (split; [exact P3|]);
    (split; [exact P4|]).
  - apply (f9_stk_norm m m0 _ _ REL); [unfold ASAN_GT in P3; lia | exact P5].
  - exact (rel_stk_back m m0 _ _ REL P5).
Qed.

(* The frame-pointer bundle fp: its thread cells, its placement and its byte facts. *)
Lemma f9_fp_rel : forall cs m m0 TP FS lo hi W D, mem_rel rsegs m m0 ->
  (fp cs m TP FS lo hi W D <-> fp cs m0 TP FS lo hi W D).
Proof.
  intros cs m m0 TP FS lo hi W D REL.
  pose proof (fun a bs => bytes_at_rel rsegs m m0 a bs REL) as R.
  unfold fp.
  split; intros (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & HDd);
    exists DT, TS, C, T, DB, k.
  - split; [exact (proj1 (f9_tls_rel m m0 TP DT TS C T DB k REL) HT)|].
    split; [exact (proj1 (R _ _) HTP)|].
    split; [exact (proj1 (f9_place_rel m m0 FS REL) HP)|].
    split; [exact (proj1 (R _ _) H88)|].
    split; [exact (proj1 (R _ _) H96)|].
    split.
    { eapply Forall_impl; [|exact HCL]. intros c (Hc & h & fl & Hh & Hfl & Hfll & Hflb).
      split; [exact Hc|]. exists h, fl. split; [exact (proj1 (R _ _) Hh)|].
      split; [exact (proj1 (R _ _) Hfl)|]. split; [exact Hfll | exact Hflb]. }
    split; [exact HFS|]. split; [exact HA|]. split; [exact HWd | exact HDd].
  - split; [exact (proj2 (f9_tls_rel m m0 TP DT TS C T DB k REL) HT)|].
    split; [exact (proj2 (R _ _) HTP)|].
    split; [exact (proj2 (f9_place_rel m m0 FS REL) HP)|].
    split; [exact (proj2 (R _ _) H88)|].
    split; [exact (proj2 (R _ _) H96)|].
    split.
    { eapply Forall_impl; [|exact HCL]. intros c (Hc & h & fl & Hh & Hfl & Hfll & Hflb).
      split; [exact Hc|]. exists h, fl. split; [exact (proj2 (R _ _) Hh)|].
      split; [exact (proj2 (R _ _) Hfl)|]. split; [exact Hfll | exact Hflb]. }
    split; [exact HFS|]. split; [exact HA|]. split; [exact HWd | exact HDd].
Qed.

(* A machine state with no pending syscall is the MS of its own fields. *)
Lemma f9_ms_eta : forall ms, ms_svc_pending ms = None ->
  ms = MS (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms) (ms_mem ms) (ms_rom ms).
Proof. intros ms H. destruct ms. cbn in H. subst. reflexivity. Qed.

(* 0x81fe8 - 0x81ff0 and the call: the two argument moves and the identity_reply call on its contract, run on
   MemNorm.normalize m and brought back to m (munch_rel / wmono_rel / ro_agree_same and RoAdapt's rel_*_back). *)
Lemma f9_evtB :
  forall (ra0 sp gp tp t0 t1 t2 s0 a0 a1 s4 s5 s6 s8 s9 s11 a5 a6 a7 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
         (A S3 fr phi len S FS TP : Z) (G ja jp jn : list byte),
    reac_ctrl_identity_reply_contract ->
    sp = Z_to_bv 64 S -> tp = Z_to_bv 64 TP -> 0 <= TP < 2 ^ 64 -> 6283264 <= fr ->
    f9_pre phi len (fr + 256) (fr + 272) (fr + 304) S FS TP m G ja jp jn ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       munch (reac_ctrl_identity_reply_fp phi len (fr + 256) (fr + 272) (fr + 304) S G ++
              fp_w [1%nat] FS ++
              [(shadow_addr (S - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr S)]) m m' ->
       wmono rsegs m m' -> ro_agree rsegs m' ->
       stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
       (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G = true ->
          rw_cells rsegs m' (fr + 256) [CB 2 (reply_addr G)] /\
          rw_cells rsegs m' (fr + 272) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
          rw_cells rsegs m' (fr + 304) [CB 8 (le8 (Z_to_bv 64 (ir_s G - 13)))]) ->
       asan_cells m' -> shadow_rw m' ->
       addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
       fp [1%nat] m' TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
         (reac_ctrl_identity_reply_W phi (fr + 256) (fr + 272) (fr + 304) S)
         (reac_ctrl_identity_reply_D phi len (fr + 256) (fr + 272) (fr + 304)) ->
       reac_ctrl_identity_reply_tls m' TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
       Q (MS (mkR (Z_to_bv 64 0x81ff4) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                  (Z_to_bv 64 (reply_ret phi len (fr + 256) (fr + 272) (fr + 304) G))
                  a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi)
                  s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
             Fr (Z_to_bv 64 0x81ff4) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 (Z_to_bv 64 (fr + 256)) (Z_to_bv 64 (fr + 272))
               (Z_to_bv 64 (fr + 304)) a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 S3) s4 s5 s6 (Z_to_bv 64 phi)
               s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81fe8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a0 a1 s4 s5 s6 s8 s9 s11 a5 a6 a7 t3 t4 t5 t6 Fr fc m Q A S3 fr phi len S0 FS TP
    G ja jp jn HIR Hsp Htp HTP Hfr Hpre HK.
  destruct Hpre as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 &
    P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28).
  assert (HK9 : REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  pose proof (mem_rel_normalize rsegs m P10) as REL.
  (* the contract's premises on the normalized memory *)
  assert (P9n : stk rsegs (normalize rsegs m) (S0 - REAC_CTRL_IDENTITY_REPLY_K) S0)
    by (apply (f9_stk_norm m _ _ _ REL); [lia | exact P9]).
  pose proof (mem_inv_normalize rsegs m) as MIn.
  assert (P12n : reply_args phi (fr + 256) (fr + 272) (fr + 304) = true -> 50 <= len ->
     phi + 50 <= 2 ^ 64 /\ bytes_at rsegs (normalize rsegs m) phi G /\
     (phi + 50 <= S0 - REAC_CTRL_IDENTITY_REPLY_K \/ S0 <= phi)).
  { intros Ha Hl. destruct (P12 Ha Hl) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [|exact Q3].
    exact (proj1 (bytes_at_rel rsegs m _ _ _ REL) Q2). }
  assert (P13n : reply_args phi (fr + 256) (fr + 272) (fr + 304) = true ->
       (fr + 256) mod 2 = 0 /\ (fr + 272) mod 8 = 0 /\ (fr + 304) mod 8 = 0 /\
       rw_cells rsegs (normalize rsegs m) (fr + 256) [CB 2 ja] /\
       rw_cells rsegs (normalize rsegs m) (fr + 272) [CB 8 jp] /\
       rw_cells rsegs (normalize rsegs m) (fr + 304) [CB 8 jn] /\
       (fr + 256 + 2 <= fr + 272 \/ fr + 272 + 8 <= fr + 256) /\
       (fr + 256 + 2 <= fr + 304 \/ fr + 304 + 8 <= fr + 256) /\
       (fr + 272 + 8 <= fr + 304 \/ fr + 304 + 8 <= fr + 272) /\
       (fr + 256 + 2 <= phi \/ phi + 50 <= fr + 256) /\ (fr + 272 + 8 <= phi \/ phi + 50 <= fr + 272) /\
       (fr + 304 + 8 <= phi \/ phi + 50 <= fr + 304) /\
       (fr + 256 + 2 <= S0 - REAC_CTRL_IDENTITY_REPLY_K \/ S0 <= fr + 256) /\
       (fr + 272 + 8 <= S0 - REAC_CTRL_IDENTITY_REPLY_K \/ S0 <= fr + 272) /\
       (fr + 304 + 8 <= S0 - REAC_CTRL_IDENTITY_REPLY_K \/ S0 <= fr + 304)).
  { intros Ha. destruct (P13 Ha) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
    split; [exact (f9_rw_norm m _ (fr + 256) _ REL ltac:(lia) Q4)|].
    split; [exact (f9_rw_norm m _ (fr + 272) _ REL ltac:(lia) Q5)|].
    split; [exact (f9_rw_norm m _ (fr + 304) _ REL ltac:(lia) Q6)|].
    exact Q7. }
  pose proof (rel_ac_norm m _ REL P14) as P14n.
  pose proof (rel_sw_norm m _ REL P15) as P15n.
  pose proof (rel_addr_norm m _ _ _ REL P18) as P18n.
  assert (P19n : reply_args phi (fr + 256) (fr + 272) (fr + 304) = true -> 50 <= len ->
                 addressable (normalize rsegs m) phi 50)
    by (intros Ha Hl; exact (rel_addr_norm m _ _ _ REL (P19 Ha Hl))).
  assert (P20n : reply_args phi (fr + 256) (fr + 272) (fr + 304) = true ->
       addressable (normalize rsegs m) (fr + 256) 2 /\ addressable (normalize rsegs m) (fr + 272) 8 /\
       addressable (normalize rsegs m) (fr + 304) 8 /\
       (fr + 256 + 2 <= RT_LO \/ RT_HI <= fr + 256) /\ (fr + 272 + 8 <= RT_LO \/ RT_HI <= fr + 272) /\
       (fr + 304 + 8 <= RT_LO \/ RT_HI <= fr + 304)).
  { intros Ha. destruct (P20 Ha) as (Q1 & Q2 & Q3 & Q4).
    split; [exact (rel_addr_norm m _ _ _ REL Q1)|]. split; [exact (rel_addr_norm m _ _ _ REL Q2)|].
    split; [exact (rel_addr_norm m _ _ _ REL Q3) | exact Q4]. }
  pose proof (rel_addr_norm m _ _ _ REL P21) as P21n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) P22) as P22n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) P23) as P23n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) P24) as P24n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) P25) as P25n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) P26) as P26n.
  pose proof (proj1 (f9_fp_rel _ m _ _ _ _ _ _ _ REL) P27) as P27n.
  assert (P28n : reac_ctrl_identity_reply_tls (normalize rsegs m) TP FS (S0 - REAC_CTRL_IDENTITY_REPLY_K) S0).
  { intros DT TS C T DB k HT. apply P28. exact (proj2 (f9_tls_rel m _ _ _ _ _ _ _ _ REL) HT). }
  clear P9 P12 P13 P14 P15 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 P28.
  assert (Etp : bv_unsigned tp = TP) by (rewrite Htp; apply MState.unsigned_lit; exact HTP).
  rewrite <- Etp in P27n, P28n.
  pose proof HIR as HC. unfold reac_ctrl_identity_reply_contract, REAC_CTRL_IDENTITY_REPLY in HC.
  (* 0x81fe8 mv a0,s7 ; 0x81fec mv a1,s2 ; 0x81ff0 jal reac_ctrl_identity_reply *)
  step. step. step.
  eapply evt_cut.
  { eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact P10 |].
    eapply HC with (fr := phi) (len := len) (pa := fr + 256) (pp := fr + 272) (pn := fr + 304) (S := S0)
      (FS := FS) (g := G) (ja := ja) (jp := jp) (jn := jn);
      first [ reflexivity | exact Hsp | assumption ]. }
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    E & MU & WM & MI & ST & HR & HAC' & HSW' & HAD' & HFP' & HTLS') & HREL & HROs).
  subst s0'.
  destruct HREL as (Er & Ef & Epc & Esvc & Erv & Efc & Erom & Hrel).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in Er, Ef, Epc, Esvc, Erv,
    Efc, Erom, Hrel.
  rewrite (f9_ms_eta ms' Esvc), Er, Ef, Epc, Erv, Efc, Erom.
  rewrite Etp in HFP', HTLS'.
  replace (ret_pc (Z_to_bv 64 532468)) with (Z_to_bv 64 532468)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evt_done.
  apply HK.
  - exact (munch_rel rsegs _ m (normalize rsegs m) (ms_mem ms') m0' REL Hrel HROs MU).
  - exact (wmono_rel rsegs m (normalize rsegs m) (ms_mem ms') m0' REL Hrel HROs WM).
  - exact (ro_agree_same rsegs m (ms_mem ms') P10 HROs).
  - exact (rel_stk_back _ _ _ _ Hrel ST).
  - intros Hok. destruct (HR Hok) as (R1 & R2 & R3).
    split; [exact (rel_rw_back _ _ _ _ Hrel R1)|].
    split; [exact (rel_rw_back _ _ _ _ Hrel R2) | exact (rel_rw_back _ _ _ _ Hrel R3)].
  - exact (rel_ac_back _ _ Hrel HAC').
  - exact (rel_sw_back _ _ Hrel HSW').
  - exact (rel_addr_back _ _ _ _ Hrel HAD').
  - exact (proj2 (f9_fp_rel _ _ _ _ _ _ _ _ _ Hrel) HFP').
  - intros DT TS C T DB k HT. apply HTLS'. exact (proj1 (f9_tls_rel _ _ _ _ _ _ _ _ _ Hrel) HT).
Qed.


Lemma l1_dj_pt : forall (Q : Z -> Prop) a b c d, a < b -> c < d ->
  (forall x, a <= x < b -> Q x) -> (forall x, c <= x < d -> ~ Q x) -> RcLay.ly_dj a b c d.
Proof.
  intros Q a b c d Hab Hcd HQ HnQ. unfold RcLay.ly_dj.
  destruct (Z_le_gt_dec b c) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec d a) as [H2|H2]; [right; exact H2|].
  exfalso. apply (HnQ (Z.max a c) ltac:(lia)). apply HQ. lia.
Qed.

Lemma l1_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

Lemma l1_word_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia.
Qed.

Lemma l1_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (l1_byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs).
  { rewrite bytes_le_to_Z_le_val. exact (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2 ^ 8)%Z.
    change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma l1_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by (cbn; lia).
  rewrite <- L at 1. apply l1_le_bytes_to_Z.
Qed.

(* A single present byte is a one-byte bytes_at. *)

Lemma l1_byte_at : forall m a b, 0 <= a -> a + 1 <= 2 ^ 64 -> mbyte rsegs m a = Some b ->
  bytes_at rsegs m a [b].
Proof.
  intros m a b H0 H1 Hb. split; [exact H0|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
  cbn [nth_error]. replace (a + Z.of_nat 0) with a by lia. exact Hb.
Qed.

(* A range of present bytes, all satisfying P, is a bytes_at of a list of that length. *)

Lemma l1_bytes_PN : forall (P : byte -> Prop) m a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = k /\ Forall P bs.
Proof.
  intros P m a k. revert a. induction k as [|k IH]; intros a H0 H1 H.
  - exists []. split; [|split; [reflexivity | constructor]].
    split; [exact H0|]. split; [cbn [length]; lia|]. intros i Hi; cbn [length] in Hi; lia.
  - destruct (H 0 ltac:(lia)) as (b & Hb & HPb).
    assert (Hrec : forall i, 0 <= i < Z.of_nat k -> exists b', mbyte rsegs m (a + 1 + i) = Some b' /\ P b').
    { intros i Hi. destruct (H (1 + i) ltac:(lia)) as (b' & Hb' & HP'). exists b'.
      split; [|exact HP']. replace (a + 1 + i) with (a + (1 + i)) by lia. exact Hb'. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrec) as (bs & Hbs & Hlen & HPbs).
    exists (b :: bs). split; [|split; [cbn [length]; lia | constructor; assumption]].
    destruct Hbs as (_ & _ & Hnth).
    split; [exact H0|]. split; [cbn [length]; rewrite Hlen; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + replace (a + Z.of_nat 0) with (a + 0) by lia. exact Hb.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hnth. cbn [length] in Hi. lia.
Qed.

Lemma l1_bytes_P : forall (P : byte -> Prop) m a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ Z.of_nat (length bs) = n /\ Forall P bs.
Proof.
  intros P m a n H0 Hn H1 H.
  destruct (l1_bytes_PN P m a (Z.to_nat n) H0 ltac:(rewrite Z2Nat.id by lia; lia)
              ltac:(rewrite Z2Nat.id by lia; exact H)) as (bs & Hbs & Hlen & HP).
  exists bs. split; [exact Hbs|]. split; [rewrite Hlen, Z2Nat.id by lia; reflexivity | exact HP].
Qed.

(* Eight present bytes read as some word. *)

Lemma l1_word_present : forall m a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b) ->
  exists w : word, bytes_at rsegs m a (le8 w).
Proof.
  intros m a H0 H1 H.
  assert (HP : forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b /\ True).
  { intros i Hi. destruct (H i Hi) as (b & Hb). exists b. split; [exact Hb | exact I]. }
  destruct (l1_bytes_P (fun _ => True) m a 8 H0 ltac:(lia) H1 HP) as (bs & Hbs & Hlen & _).
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite l1_le8_of_bytes by lia. exact Hbs.
Qed.

(* word_mem pins the value only modulo 2^64. *)

Lemma l1_word_mem_eq : forall m a v1 v2, word_mem rsegs m a v1 -> word_mem rsegs m a v2 ->
  v1 mod 2 ^ 64 = v2 mod 2 ^ 64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (E : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (EB : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    rewrite <- (kb_byte_unsigned v1 8 k), <- (kb_byte_unsigned v2 8 k), EB. reflexivity. }
  assert (M : forall v k, le_byte (v mod 2 ^ 64) 8 k = le_byte v 8 k).
  { intros v k. unfold le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
  pose proof (kb_le8_digits (v1 mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as D1.
  pose proof (kb_le8_digits (v2 mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as D2.
  rewrite !M in D1. rewrite !M in D2.
  rewrite D1 at 1. rewrite D2 at 1.
  rewrite (E 0%nat ltac:(lia)), (E 1%nat ltac:(lia)), (E 2%nat ltac:(lia)), (E 3%nat ltac:(lia)),
    (E 4%nat ltac:(lia)), (E 5%nat ltac:(lia)), (E 6%nat ltac:(lia)), (E 7%nat ltac:(lia)).
  reflexivity.
Qed.

Lemma l1_wm_norm : forall m a x y, word_mem rsegs m a x -> word_mem rsegs m a y ->
  0 <= y < 2 ^ 64 -> - (2 ^ 64) < x < 2 ^ 64 -> x = y \/ x = y - 2 ^ 64.
Proof.
  intros m a x y Hx Hy Hy0 Hx0.
  pose proof (l1_word_mem_eq m a x y Hx Hy) as E.
  rewrite (Z.mod_small y (2 ^ 64)) in E by lia.
  destruct (Z_le_gt_dec 0 x) as [Hs|Hs].
  - left. rewrite (Z.mod_small x (2 ^ 64)) in E by lia. exact E.
  - right.
    assert (EM : (x + 2 ^ 64) mod 2 ^ 64 = x mod 2 ^ 64).
    { replace (x + 2 ^ 64) with (x + 1 * 2 ^ 64) by lia. apply Z_mod_plus_full. }
    rewrite (Z.mod_small (x + 2 ^ 64) (2 ^ 64)) in EM by lia. lia.
Qed.

Lemma l1_sh_lo : forall a, 0 <= a -> LOWMEM_END <= shadow_addr a.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, LOWMEM_END.
  assert (0 <= a / 8) by (apply Z.div_pos; lia). lia.
Qed.

(* The class-1 ranges of the side stack, as plain offsets of FS. *)

Lemma l1_fs_M1 : fs_M 1%nat = 8192.
Proof. reflexivity. Qed.

Lemma l1_fs_B1 : fs_B 1%nat = 128.
Proof. reflexivity. Qed.

Lemma l1_fs_hint1 : forall FS, fs_hint FS 1%nat = FS + 8.
Proof. intros FS. unfold fs_hint. cbn [Z.of_nat]. lia. Qed.

Lemma l1_fs_flag1 : forall FS, fs_flag FS 1%nat 0 = FS + 20480.
Proof.
  intros FS. unfold fs_flag. cbn [Z.of_nat]. change (2 ^ 15) with 32768.
  change (2 ^ (15 - 1)) with 16384. lia.
Qed.

Lemma l1_afs_flag1 : forall FS j, AC.a_fs_flag FS 1%nat j = FS + 20480 + j.
Proof.
  intros FS j. unfold AC.a_fs_flag.
  change (2 ^ (15 - Z.of_nat 1)) with 16384. change (2 ^ 15) with 32768. lia.
Qed.

Lemma l1_fs_frame1_0 : forall FS, fs_frame FS 1%nat 0 = FS + 1085440.
Proof.
  intros FS. unfold fs_frame. rewrite l1_fs_B1. cbn [Z.of_nat]. change (2 ^ 20) with 1048576. lia.
Qed.

Lemma l1_fs_frame1_M : forall FS, fs_frame FS 1%nat (fs_M 1%nat) = FS + 2134016.
Proof.
  intros FS. unfold fs_frame. rewrite l1_fs_B1, l1_fs_M1. cbn [Z.of_nat].
  change (2 ^ 20) with 1048576. lia.
Qed.

Lemma l1_fpw1 : forall FS, fp_w [1%nat] FS =
  [(FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016))].
Proof.
  intros FS. unfold fp_w. cbn [flat_map]. rewrite app_nil_r. unfold fp_w1.
  rewrite l1_fs_hint1, l1_fs_flag1, l1_fs_frame1_0, l1_fs_frame1_M, l1_fs_M1.
  replace (FS + 8 + 8) with (FS + 16) by lia.
  replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  reflexivity.
Qed.

Lemma l1_fs_frame0 : forall FS, fs_frame FS 0%nat 0 = FS + 36864.
Proof.
  intros FS. unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576.
  change (2 ^ 0) with 1. lia.
Qed.

Lemma l1_sh_hi : forall a, a <= APPMEM_END -> shadow_addr a <= HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG.
  assert (D : a / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; unfold APPMEM_END in *; lia).
  lia.
Qed.

(* Each disjointness leaf names image constants, FS / fr / sp offsets and shadow endpoints: unfold the constants
   and let lia use the range facts of the context. *)

Ltac l1_num :=
  cbv [RcLay.ly_dj TLS_INDEX REAL_TLS_GET_ADDR TSD_KEY_INITED TSD_KEY GOT_CF CF GOT_VERBOSITY VERBOSITY DTLS_TPOFF
       RT_TP RT_TSDMAIN RT_GT ASAN_GT AC.as_tp AC.ASYMS AC.GT AC.FS_SIZE FS_SIZE RT_FS_SIZE
       REAC_CTRL_IDENTITY_REPLY_K AF.SLOT_STACK HIGHMEM_BEG APPMEM_END LOWMEM_END LOWSHADOW_END HIGHSHADOW_BEG
       ASAN_K] in *; lia.

Ltac l1_dj_split := repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd].

Section S_l1.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Definition f9_W9 (fr : Z) : list ivl :=
  [(Sfr fr + 32, Sfr fr + 33); (fr + 256, fr + 258); (Sfr fr + 34, Sfr fr + 35); (fr + 272, fr + 280);
   (Sfr fr + 38, Sfr fr + 39); (fr + 304, fr + 312)].

(* The two allocator laws f9_fp_call reads, each taken apart once here and used by name at the site (a Theorem Labs lane's rule
   for generated laws until N+1: an appended conjunct lands in a trailing `_` or in a fact found by its type). The
   thread record (a_laws_thread): C at RT_TSDMAIN, T at C + 152, the allocator's bytes at C + 152 and at T + 48. *)
Lemma f9_thread : forall H mem md, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  exists C T, word_mem rsegs mem RT_TSDMAIN C /\ 0 < C < 2 ^ 64 /\ 0 < T < 2 ^ 64 /\
    word_mem rsegs mem (C + 152) T /\
    (forall i, 0 <= i < 8 ->
       AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (C + 152 + i) /\ app_mem (C + 152 + i)) /\
    (forall i, 0 <= i < 16 ->
       AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (T + 48 + i) /\ exists b, mbyte rsegs mem (T + 48 + i) = Some b).
Proof.
  intros H mem md HAH.
  destruct (AC.a_laws_thread _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md HAH)
    as (_ & _ & _ & C & T & HwC & HCr & HTr & HwT & HC152 & _ & _ & _ & _ & _ & _ & _ & _ & HT48 & _).
  exists C, T. exact (conj HwC (conj HCr (conj HTr (conj HwT (conj HC152 HT48))))).
Qed.

(* The side stack's state and the thread's DTLS word (a_laws_fs_state with a_fs_ok unfolded). Its last conjunct
   at each level is the one this segment needs, so the law is split by decompose and each fact is found by its
   type, not by its position: a conjunct appended at any level is one more unused hypothesis here. *)
Lemma f9_fs_state : forall H mem md FS, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b) /\
  word_mem rsegs mem (FS + 88) 20 /\ mbyte rsegs mem (FS + 96) = Some (Z_to_bv 8 0) /\
  (forall c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 1)) /\
  (exists DB, 0 <= DB < 2 ^ 64 /\ word_mem rsegs mem (AC.as_tp AC.ASYMS + 8) DB /\
     word_mem rsegs mem (DB + 24) (AC.as_tp AC.ASYMS) /\
     forall a, DB + 24 <= a < DB + 32 ->
       app_mem a /\ a < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ AC.a_in_fs AC.ASYMS mem a) /\
  (forall C T, word_mem rsegs mem RT_TSDMAIN C -> 0 <= C < 2 ^ 64 -> word_mem rsegs mem (C + 152) T ->
     0 <= T < 2 ^ 64 -> forall i, 0 <= i < 16 -> app_mem (T + 48 + i)).
Proof.
  intros H mem md FS HAH Hw HFS.
  pose proof (AC.a_laws_fs_state _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw HFS)
    as L.
  unfold AC.a_fs_ok in L. decompose [and ex] L.
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [|assumption].
  lazymatch goal with
  | HD : word_mem rsegs mem (AC.as_tp AC.ASYMS + 8) ?D |- _ =>
      exists D; split; [split; assumption|]; split; [exact HD|]; split; [assumption|];
      intros a Ha;
      match goal with HP : _ |- _ => destruct (HP a Ha) as (Y1 & Y2 & _ & Y4 & _) end;
      split; [exact Y1|]; split; [exact Y2 | exact Y4]
  end.
Qed.

(* The callee's side-stack bundle at the call: fp [1%nat] and the tls clause, from FRA's runtime cells (RT), the
   allocator laws, f9_PL and b5_FS's DTLS word. *)

Lemma f9_fp_call : forall g fr phi len regs mem md,
  FRA B APIf ra g fr [(phi, AC.a_size len)] regs mem md -> f9_PL fr regs mem ->
  AC.aspZ regs <= APPMEM_END ->
  (exists DB, word_mem rsegs mem (AC.as_tp AC.ASYMS + 8) DB /\ 0 <= DB /\ DB + 32 <= 2 ^ 64) ->
  exists FS,
    word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\
    fp [1%nat] mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) (AC.aspZ regs)
      (reac_ctrl_identity_reply_W phi (fr + 256) (fr + 272) (fr + 304) (AC.aspZ regs))
      (reac_ctrl_identity_reply_D phi len (fr + 256) (fr + 272) (fr + 304)) /\
    reac_ctrl_identity_reply_tls mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K)
      (AC.aspZ regs).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros g fr phi len regs mem md HFRA HPL HspA (DBp & HDBp & HDBp0 & HDBp1).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWAf &
    HTop1 & HTop2 & HTop3 & Hhb & Hlive).
  destruct HPL as (Happ & Hgt & Hdisj & HA9 & Hfs9).
  rewrite Haspz in HspA |- *.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof Hloc as Hloc'.
  (* ---- the side stack's base FS ---- *)
  destruct (AsanRTInv.RT_fs_cells _ _ _ HRT)
    as (Htlsidx & Hdtpoff & Hdt & Hdt8 & (FSw & HFSb & HFSok) & (DBw & HDBb & HDBnz)).
  pose proof (bytes_at_le8_word rsegs mem RT_TP FSw HFSb) as HFSwm.
  remember (bv_unsigned FSw) as FS eqn:EFS.
  assert (HFS64 : 0 <= FS < 2 ^ 64) by (rewrite EFS; apply l1_word_range).
  destruct HFSok as (HFSpos & HFSalign & HFSgt & HFSapp).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as NSTK1.
  destruct (f9_fs_place _ _ _ _ _ LAWS _ _ _ _ HAH HFSwm HFS64) as (_ & NFS1 & _ & _).
  destruct (f9_fs_state _ _ _ _ HAH HFSwm HFS64)
    as (HFSpres & HFS88 & HFS96 & HFSflag & (DBz & HDBzr & HDBzw & HDBztp & HDBzp) & HT48app).
  assert (NAPP : APPMEM_END < 2 ^ 64) by (unfold APPMEM_END; lia).
  assert (NFSB : FS + 11571200 <= APPMEM_END)
    by (unfold AC.FS_SIZE in NFS1; unfold AF.SLOT_STACK in Hstklo; lia).
  (* ---- the thread record (f9_thread) ---- *)
  destruct (f9_thread _ _ _ HAH) as (C0 & T0 & HC0wm & HC0rng & HT0rng & HT0wm & HC152 & HT48).
  destruct (AsanRTInv.RT_uw_cells _ _ _ HRT) as (Htsdi & Htsdk & _ & Htp88 & (Cw & HCwb)).
  pose proof (bytes_at_le8_word rsegs mem RT_TSDMAIN Cw HCwb) as HCwm.
  assert (ECw : bv_unsigned Cw = C0).
  { pose proof (l1_word_range Cw) as HR.
    destruct (l1_wm_norm mem RT_TSDMAIN (bv_unsigned Cw) C0 HCwm HC0wm ltac:(lia) ltac:(lia)) as [E|E];
      [exact E | lia]. }
  assert (HCapp : forall x, C0 + 152 <= x < C0 + 160 -> app_mem x).
  { intros x Hx. pose proof (proj2 (HC152 (x - (C0 + 152)) ltac:(lia))) as H.
    replace (C0 + 152 + (x - (C0 + 152))) with x in H by lia. exact H. }
  assert (HCpt : forall x, C0 + 152 <= x < C0 + 160 ->
            x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct (HC152 (x - (C0 + 152)) ltac:(lia)) as (Hown & Hap).
    replace (C0 + 152 + (x - (C0 + 152))) with x in Hown by lia.
    pose proof (HCapp x Hx) as Hax.
    pose proof (AC.a_laws_not_owned _ _ _ _ _ LAWS _ _ _ x HAH) as HNO.
    split.
    - destruct (Z_lt_le_dec x (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)) as [H|H]; [exact H|].
      exfalso. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x < APPMEM_END)
        by (unfold APPMEM_END; lia).
      exact (proj1 (HNO (or_intror (or_intror (or_intror Hst)))) Hown).
    - intros Hin.
      assert (HFSin : AC.a_in_fs AC.ASYMS mem x)
        by (exists FS; split; [exact HFS64 | split; [exact HFSwm | exact Hin]]).
      exact (proj1 (HNO (or_intror (or_intror (or_introl HFSin)))) Hown). }
  assert (HTapp : forall x, T0 + 48 <= x < T0 + 64 -> app_mem x).
  { intros x Hx.
    pose proof (HT48app C0 T0 HC0wm ltac:(lia) HT0wm ltac:(lia) (x - (T0 + 48)) ltac:(lia)) as H.
    replace (T0 + 48 + (x - (T0 + 48))) with x in H by lia. exact H. }
  assert (HTpt : forall x, T0 + 48 <= x < T0 + 64 ->
            x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct (HT48 (x - (T0 + 48)) ltac:(lia)) as (Hown & _).
    replace (T0 + 48 + (x - (T0 + 48))) with x in Hown by lia.
    pose proof (HTapp x Hx) as Hax.
    pose proof (AC.a_laws_not_owned _ _ _ _ _ LAWS _ _ _ x HAH) as HNO.
    split.
    - destruct (Z_lt_le_dec x (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)) as [H|H]; [exact H|].
      exfalso. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x < APPMEM_END)
        by (unfold APPMEM_END; lia).
      exact (proj1 (HNO (or_intror (or_intror (or_intror Hst)))) Hown).
    - intros Hin.
      assert (HFSin : AC.a_in_fs AC.ASYMS mem x)
        by (exists FS; split; [exact HFS64 | split; [exact HFSwm | exact Hin]]).
      exact (proj1 (HNO (or_intror (or_intror (or_introl HFSin)))) Hown). }
  assert (HTpres : forall i, 0 <= i < 16 -> exists b, mbyte rsegs mem (T0 + 48 + i) = Some b).
  { intros i Hi. exact (proj2 (HT48 i Hi)). }
  (* ---- the thread's DTLS word ---- *)
  assert (EDBz : DBz = DBp).
  { pose proof (proj1 (HDBzp (DBz + 24) ltac:(lia))) as Ha1.
    pose proof (proj1 (HDBzp (DBz + 31) ltac:(lia))) as Ha2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha1, Ha2.
    destruct (l1_wm_norm mem (AC.as_tp AC.ASYMS + 8) DBz DBp HDBzw HDBp ltac:(lia) ltac:(lia)) as [E|E];
      [exact E | lia]. }
  assert (EDBw : bv_unsigned DBw = DBp).
  { pose proof (l1_word_range DBw) as HR.
    pose proof (bytes_at_le8_word rsegs mem (RT_TP + 8) DBw HDBb) as HDBwm.
    destruct (l1_wm_norm mem (AC.as_tp AC.ASYMS + 8) (bv_unsigned DBw) DBp HDBwm HDBp ltac:(lia) ltac:(lia))
      as [E|E]; [exact E | lia]. }
  assert (HDBpt : forall x, DBp + 24 <= x < DBp + 32 ->
            app_mem x /\ x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
            ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. rewrite <- EDBz in Hx. destruct (HDBzp x Hx) as (H1 & H2 & H4).
    split; [exact H1|]. split; [exact H2|]. intros Hin. apply H4.
    exists FS. split; [exact HFS64 | split; [exact HFSwm | exact Hin]]. }
  assert (HDB24 : bytes_at rsegs mem (bv_unsigned DBw + 24) (le8 (Z_to_bv 64 (AC.as_tp AC.ASYMS)))).
  { rewrite EDBw, <- EDBz.
    apply (word_mem_le8 rsegs mem (DBz + 24) (AC.as_tp AC.ASYMS) HDBztp);
      [cbv [AC.as_tp AC.ASYMS]; lia | lia | lia]. }
  (* ---- numeric bounds of the thread cells ---- *)
  assert (NC0 : C0 + 160 <= APPMEM_END).
  { pose proof (HCapp (C0 + 159) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NT0 : T0 + 64 <= APPMEM_END).
  { pose proof (HTapp (T0 + 63) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NC : C0 + 160 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (pose proof (proj1 (HCpt (C0 + 159) ltac:(lia))); lia).
  assert (NT : T0 + 64 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (pose proof (proj1 (HTpt (T0 + 63) ltac:(lia))); lia).
  assert (NDB : DBp + 32 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (pose proof (proj1 (proj2 (HDBpt (DBp + 31) ltac:(lia)))); lia).
  (* ---- the words the tls cells name ---- *)
  assert (EDTu : bv_unsigned (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)) = AC.as_tp AC.ASYMS + 32)
    by (apply MState.unsigned_lit; cbv [AC.as_tp AC.ASYMS]; lia).
  assert (ETSu : bv_unsigned (Z_to_bv 64 RT_TSDMAIN) = RT_TSDMAIN)
    by (apply MState.unsigned_lit; unfold RT_TSDMAIN; lia).
  assert (ETu : bv_unsigned (Z_to_bv 64 T0) = T0) by (apply MState.unsigned_lit; lia).
  pose proof (word_mem_le8 rsegs mem (C0 + 152) T0 HT0wm ltac:(lia) ltac:(lia)
                ltac:(unfold APPMEM_END in *; lia)) as HT0b.
  destruct (l1_word_present mem (T0 + 48) ltac:(lia) ltac:(unfold APPMEM_END in *; lia)
      ltac:(intros i Hi; exact (HTpres i ltac:(lia)))) as (tb & Htb).
  assert (HTpres2 : forall i, 0 <= i < 8 -> exists b, mbyte rsegs mem (T0 + 56 + i) = Some b).
  { intros i Hi. replace (T0 + 56 + i) with (T0 + 48 + (8 + i)) by lia. exact (HTpres (8 + i) ltac:(lia)). }
  destruct (l1_word_present mem (T0 + 56) ltac:(lia) ltac:(unfold APPMEM_END in *; lia) HTpres2) as (te & Hte).
  assert (HTBE : bytes_at rsegs mem (T0 + 48) (le8 tb ++ le8 te)).
  { apply (proj2 (bytes_at_app rsegs mem (T0 + 48) (le8 tb) (le8 te))).
    split; [exact Htb|]. rewrite length_le8.
    replace (T0 + 48 + Z.of_nat 8) with (T0 + 56) by lia. exact Hte. }
  destruct (AsanRTInv.RT_cf_cells _ _ _ HRT) as (Hcf1 & _ & _ & _ & _ & Hcf137 & _ & _).
  destruct (AsanRTInv.RT_opt_cells _ _ _ HRT) as (_ & _ & Hopt3 & Hopt4).
  pose proof (AsanRTInv.RT_real_cells _ _ _ HRT) as HREAL.
  assert (HTLS : asan_tls_cells mem (AC.as_tp AC.ASYMS) (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32))
                   (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0).
  { unfold asan_tls_cells. rewrite EDTu, ETSu, ETu, ECw.
    split; [exact Htlsidx|].
    split; [exact (AsanRTInv.real_cell_of mem REAL_TLS_GET_ADDR MUSL_TLS_GET_ADDR HREAL
                     ltac:(vm_compute; reflexivity))|].
    split; [exact Hdt|].
    split; [exact Hdt8|].
    split; [exact Htsdi|].
    split; [lia|].
    split; [exact Htsdk|].
    split; [exact Htp88|].
    split; [exact HCwb|].
    split; [exact HT0b|].
    split; [exists tb, te; exact HTBE|].
    split; [exact Hcf1|].
    split; [exact Hcf137|].
    split; [exact Hopt3|].
    split; [exact Hopt4|].
    split; [exact Hdtpoff|].
    split; [exact HDBb|].
    split; [exact (proj1 HDBnz)|].
    exact HDB24. }
  (* ---- the frame's placement: real stack or side stack ---- *)
  assert (HFSuniq : forall b x, word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> b <= x < b + AC.FS_SIZE ->
            0 <= x < APPMEM_END -> b = FS).
  { intros b x Hb Hbx Hx.
    destruct (l1_wm_norm mem (AC.as_tp AC.ASYMS) b FS Hb HFSwm HFS64
                ltac:(unfold AC.FS_SIZE, APPMEM_END in *; lia)) as [E|E];
      [exact E | unfold AC.FS_SIZE, APPMEM_END in *; lia]. }
  assert (HFRQ : forall x, fr <= x < fr + FRAME_BYTES ->
            AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x \/ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct Hloc as [(_ & _ & Hreal) | (_ & _ & Hfs & _)].
    - left. exact (proj1 (Hreal x Hx)).
    - right. destruct (Hfs x Hx) as (b & Hbr & Hb & Hbx).
      pose proof (Happ x Hx) as Hax. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      rewrite <- (HFSuniq b x Hb Hbx ltac:(unfold APPMEM_END; lia)). exact Hbx. }
  assert (HFRFS : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= fr \/
                  (FS + 36864 + 6 * 2 ^ 20 <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE)).
  { destruct Hloc' as [(_ & _ & Hreal) | (_ & _ & Hfs & _)].
    - left. exact (proj1 (Hreal fr ltac:(lia))).
    - right. destruct (Hfs fr ltac:(lia)) as (b & Hbr & Hb & Hbx).
      pose proof (Happ fr ltac:(lia)) as Hax. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Eb : b = FS) by (apply (HFSuniq b fr Hb Hbx); unfold APPMEM_END; lia).
      rewrite Eb in Hbx. exact (Hfs9 FS HFSwm HFS64 Hbx). }
  (* ---- app memory and shadow memory are apart ---- *)
  assert (HGAP : forall x, LOWMEM_END <= x < HIGHMEM_BEG -> ~ app_mem x).
  { intros x Hx Hap. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (AS_C : RcLay.ly_dj (C0 + 152) (C0 + 160) LOWMEM_END HIGHMEM_BEG).
  { apply (l1_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact HCapp | exact HGAP]. }
  assert (AS_T : RcLay.ly_dj (T0 + 48) (T0 + 64) LOWMEM_END HIGHMEM_BEG).
  { apply (l1_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact HTapp | exact HGAP]. }
  assert (AS_DB : RcLay.ly_dj (DBp + 24) (DBp + 32) LOWMEM_END HIGHMEM_BEG).
  { apply (l1_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia
    | intros x Hx; exact (proj1 (HDBpt x Hx)) | exact HGAP]. }
  assert (AS_FR : RcLay.ly_dj fr (fr + FRAME_BYTES) LOWMEM_END HIGHMEM_BEG).
  { apply (l1_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact Happ | exact HGAP]. }
  (* ---- the shadow of the class-1 frames and of the callee's window lies between the app ranges ---- *)
  assert (SB1a : LOWMEM_END <= shadow_addr (FS + 1085440)) by (apply l1_sh_lo; lia).
  assert (SB1b : shadow_addr (FS + 2134016) <= HIGHMEM_BEG)
    by (apply l1_sh_hi; unfold APPMEM_END in *; lia).
  assert (SB2a : LOWMEM_END <= shadow_addr (sp - REAC_CTRL_IDENTITY_REPLY_K)).
  { apply l1_sh_lo. unfold REAC_CTRL_IDENTITY_REPLY_K, AF.SLOT_STACK, HIGHMEM_BEG in *. lia. }
  assert (SB2b : shadow_addr sp <= HIGHMEM_BEG) by (apply l1_sh_hi; lia).
  (* ---- the thread cells are apart from the frame and from the side stack ---- *)
  assert (DJ_C_FR : RcLay.ly_dj fr (fr + FRAME_BYTES) (C0 + 152) (C0 + 160)).
  { apply (l1_dj_pt (fun x => AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x \/
                              (FS <= x < FS + AC.FS_SIZE)));
      [lia | lia | exact HFRQ |].
    intros x Hx Hq. destruct (HCpt x Hx) as (H1 & H2). destruct Hq as [Hq|Hq]; [lia | exact (H2 Hq)]. }
  assert (DJ_T_FR : RcLay.ly_dj fr (fr + FRAME_BYTES) (T0 + 48) (T0 + 64)).
  { apply (l1_dj_pt (fun x => AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x \/
                              (FS <= x < FS + AC.FS_SIZE)));
      [lia | lia | exact HFRQ |].
    intros x Hx Hq. destruct (HTpt x Hx) as (H1 & H2). destruct Hq as [Hq|Hq]; [lia | exact (H2 Hq)]. }
  assert (DJ_DB_FR : RcLay.ly_dj fr (fr + FRAME_BYTES) (DBp + 24) (DBp + 32)).
  { apply (l1_dj_pt (fun x => AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x \/
                              (FS <= x < FS + AC.FS_SIZE)));
      [lia | lia | exact HFRQ |].
    intros x Hx Hq. destruct (HDBpt x Hx) as (_ & H1 & H2). destruct Hq as [Hq|Hq]; [lia | exact (H2 Hq)]. }
  assert (DJ_C_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (C0 + 152) (C0 + 160)).
  { apply (l1_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
    intros x Hx. exact (proj2 (HCpt x Hx)). }
  assert (DJ_T_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (T0 + 48) (T0 + 64)).
  { apply (l1_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
    intros x Hx. exact (proj2 (HTpt x Hx)). }
  assert (DJ_DB_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (DBp + 24) (DBp + 32)).
  { apply (l1_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
    intros x Hx. exact (proj2 (proj2 (HDBpt x Hx))). }
  (* ---- the heap block of the reply arguments ---- *)
  assert (HPHI : 50 <= len -> forall x, phi <= x < phi + 50 ->
            app_mem x /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros Hlen x Hx.
    destruct (f9_blocks _ _ _ _ _ LAWS _ _ _ phi (AC.a_size len) HAH
                ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & Hb).
    destruct (Hb x ltac:(unfold AC.a_size; lia)) as (Hap & Hnfs).
    split; [exact Hap|]. intros Hin. apply Hnfs.
    exists FS. split; [exact HFS64 | split; [exact HFSwm | exact Hin]]. }
  (* ---- the goal ---- *)
  clear Hloc Hloc' Hs5 Hdisj HFRQ HFSuniq Hfrm Hspm HAm.
  exists FS.
  split; [exact HFSwm|].
  split; [exact HFS64|].
  split.
  { (* fp *)
    exists (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)), (Z_to_bv 64 RT_TSDMAIN), Cw, (Z_to_bv 64 T0), DBw, 0.
    split; [exact HTLS|].
    split; [rewrite EFS, MState.Z_to_bv_bv_unsigned; exact HFSb|].
    split.
    { unfold fs_place. split; [lia|]. split; [exact HFSalign|].
      split; [unfold ASAN_GT, RT_GT in *; lia|].
      split; [intros a Ha; apply HFSapp; unfold FS_SIZE, RT_FS_SIZE in *; lia|].
      split; [lia|]. split; [unfold FS_SIZE in *; lia|].
      intros a Ha. destruct (HFSpres a ltac:(unfold AC.FS_SIZE, FS_SIZE in *; lia)) as (Hw & b & Hb).
      split; [exact Hw | exists b; exact Hb]. }
    split; [exact (word_mem_le8 rsegs mem (FS + 88) 20 HFS88 ltac:(lia) ltac:(lia) ltac:(lia))|].
    split; [apply l1_byte_at; [lia | lia | exact HFS96]|].
    split.
    { apply Forall_cons; [|apply Forall_nil].
      unfold fp_cls. split; [lia|].
      destruct (l1_word_present mem (FS + 8) ltac:(lia) ltac:(lia)
          ltac:(intros i Hi;
                destruct (HFSpres (FS + 8 + i) ltac:(unfold AC.FS_SIZE in *; lia)) as (_ & bb & Hbb);
                exists bb; exact Hbb)) as (h & Hh).
      destruct (l1_bytes_P (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) mem (FS + 20480) 8192
          ltac:(lia) ltac:(lia) ltac:(lia)
          ltac:(intros i Hi;
                pose proof (HFSflag 1%nat i ltac:(lia) ltac:(change (AC.a_fs_M 1%nat) with 8192; lia)) as Hf;
                rewrite l1_afs_flag1 in Hf;
                destruct Hf as [Hf|Hf]; [exists (Z_to_bv 8 0) | exists (Z_to_bv 8 1)];
                  (split; [exact Hf | first [left; reflexivity | right; reflexivity]])))
                as (flags & Hfl & Hfllen & Hflb).
      exists h, flags.
      rewrite l1_fs_hint1, l1_fs_flag1, l1_fs_M1.
      split; [exact Hh|]. split; [exact Hfl|]. split; [exact Hfllen | exact Hflb]. }
    split; [l1_num|].
    split; [intros a Ha; unfold app_mem; right; l1_num|].
    split.
    { (* the caller's writes are apart from the tls cells and the side stack's header *)
      rewrite l1_fs_frame0. unfold reac_ctrl_identity_reply_W, fp_dj.
      cbn [fp_tls app]. rewrite ?EDTu, ?ETSu, ?ETu, ?ECw, ?EDBw.
      clear AS_C AS_T AS_DB AS_FR DJ_C_FS DJ_T_FS DJ_DB_FS HFSalign.
      destruct (reply_args phi (fr + 256) (fr + 272) (fr + 304)); l1_dj_split; l1_num. }
    { (* the caller's data ranges are apart from the class-1 side-stack bytes *)
      clear AS_C AS_T AS_DB DJ_C_FR DJ_T_FR DJ_DB_FR DJ_C_FS DJ_T_FS DJ_DB_FS HFSalign.
      rewrite l1_fpw1. unfold reac_ctrl_identity_reply_D.
      destruct (reply_args phi (fr + 256) (fr + 272) (fr + 304)) eqn:ERA;
        [|unfold fp_dj; apply Forall_nil].
      destruct (len <? 50) eqn:EL.
      - cbn [app]. unfold fp_dj. l1_dj_split; l1_num.
      - apply Z.ltb_ge in EL.
        assert (AS_PHI : RcLay.ly_dj phi (phi + 50) LOWMEM_END HIGHMEM_BEG).
        { apply (l1_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia
          | intros x Hx; exact (proj1 (HPHI EL x Hx)) | exact HGAP]. }
        assert (DJ_PHI_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) phi (phi + 50)).
        { apply (l1_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
            [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
          intros x Hx. exact (proj2 (HPHI EL x Hx)). }
        cbn [app]. unfold fp_dj. l1_dj_split; l1_num. } }
  { (* the tls clause: any witnesses are the ones above *)
    intros DT' TS' C' T' DB' k' HT'.
    assert (HOUT : Forall (fun d => forall x, fst d <= x < snd d -> outside (@nil ivl) x)
                     (fp_tls (AC.as_tp AC.ASYMS) (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32))
                        (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0)).
    { apply Forall_forall. intros d _ x _. exact I. }
    destruct (fl_tls_same mem mem [] (AC.as_tp AC.ASYMS)
                (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)) (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0
                DT' TS' C' T' DB' k' HTLS HT' (munch_refl (@nil ivl) mem) HOUT)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT' TS' C' T' DB' k'.
    rewrite l1_fpw1. unfold fp_dj. cbn [fp_tls app].
    rewrite ?EDTu, ?ETSu, ?ETu, ?ECw, ?EDBw.
    clear HFRFS AS_FR DJ_C_FR DJ_T_FR DJ_DB_FR HFSalign.
    l1_dj_split; l1_num. }
Qed.

End S_l1.

(* Every registered global lies in the image, below AC.GT: checked by computation over AF.frame_AG, as
   Tac_slot's img_tops_ok checks the loaded segments. Push 5c's FRA conjunct "the registered globals are
   addressable" moves across a run that writes no byte below GT and no shadow byte of the image. *)
Definition f9_ag_ok : bool :=
  forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? AC.GT)) AF.frame_AG.

Lemma f9_ag_true : f9_ag_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f9_ag_lt : forall a, in_globals AF.frame_AG a -> 0 <= a < AC.GT.
Proof.
  intros a (lo & n & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) f9_ag_true (lo, n) Hin) as H.
  apply andb_prop in H as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2. cbn in H1, H2. lia.
Qed.

(* A byte of a CB cell the callee wrote is present afterwards (the window fact of FRA asks for exactly this). *)
Lemma f9_cell_byte : forall m a n bs x, rw_cells rsegs m a [CB n bs] -> a <= x < a + Z.of_nat n ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a n bs x ((Hwf & Hb) & _) Hx.
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  destruct Hwf as (Hlen & _). cbn [cell_wf] in Hlen.
  destruct Hb as (H0 & H1 & Hall).
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by (rewrite Hlen; lia).
  pose proof (Hall (Z.to_nat (x - a)) Hi) as Hm.
  rewrite Z2Nat.id in Hm by lia. replace (a + (x - a)) with x in Hm by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:E;
    [exists b; exact Hm | apply nth_error_None in E; lia].
Qed.

(* One byte of an addressable range. *)
Lemma f9_addr1 : forall m p n a, addressable m p n -> p <= a < p + n -> addressable m a 1.
Proof.
  intros m p n a (H0 & Hn & Hhi & Hall) Hx.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + i) with (p + (a - p + i)) by lia. apply Hall. lia.
Qed.

(* A byte read at or above the image's top is a byte of the memory itself (seg_rom has nothing there). *)
Lemma f9_mem_some : forall m x b, 6283264 <= x < 2 ^ 64 -> mbyte rsegs m x = Some b ->
  exists b', m (wa x) = Some b'.
Proof.
  intros m x b Hx H. change (mrd rsegs m (wa x) = Some b) in H. unfold mrd in H.
  destruct (m (wa x)) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso.
  destruct (find_segment rsegs (bv_unsigned (wa x)) 1) as [s|] eqn:Es.
  - destruct (ro_find_below rsegs 6283264 _ 1 s ro_rsegs_low Es ltac:(lia)) as [L|L];
      [rewrite wa_unsigned in L by lia; lia | discriminate L].
  - rewrite (seg_rom_unmapped rsegs (wa x) Es) in H. discriminate H.
Qed.

(* A byte of a bytes_at list is present. *)
Lemma f9_ba_some : forall m a bs x, bytes_at rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, mbyte rsegs m x = Some b.
Proof.
  intros m a bs x (_ & _ & H) Hx.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:E.
  - exists b. rewrite <- E. replace x with (a + Z.of_nat (Z.to_nat (x - a))) at 1 by lia. apply H. lia.
  - apply nth_error_None in E. lia.
Qed.

(* The identity record of every turn has the model's 38 bytes: ID0 has them and ING keeps them. *)
Lemma f9_tID_len : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  assert (H1 : length (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) = 38%nat).
  { unfold rp_id. destruct (ir (t_len inp j) (t_g inp j)); [apply RcIdentModel.ING_length; exact IH | exact IH]. }
  assert (H2 : length (fg_id (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) (t_len inp j)
                  (fs_fg (fst_at inp j)) (t_g inp j)) = 38%nat).
  { unfold fg_id.
    destruct (fg_rf (t_len inp j) (fs_fg (fst_at inp j)) (t_g inp j) =? 1);
      [apply RcIdentModel.ING_length; exact H1 | exact H1]. }
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; exact H2.
Qed.

(* memcmp_model reads only the first n bytes of both lists. *)
Lemma f9_mcmp_firstn : forall n l r, SFA.memcmp_model (firstn n l) (firstn n r) n = SFA.memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros [|a l] [|b r]; cbn; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH | reflexivity].
Qed.

(* A prefix of a bytes_at list. *)
Lemma f9_ba_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n H. rewrite <- (firstn_skipn n bs) in H.
  exact (proj1 (proj1 (bytes_at_app rsegs m a (firstn n bs) (skipn n bs)) H)).
Qed.


Section S_l2.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The numeric constants this section's `lia` calls mix. Each unfold is optional: a hypothesis set that does not
   mention one of them (the cleared FRA conjuncts) must not stop the rest. *)
Local Ltac l2_k :=
  try unfold app_mem in *; try unfold Sfr in *; try unfold shadow_addr in *;
  try unfold AC.GT in *; try unfold AC.FS_SIZE in *; try unfold FS_SIZE in *; try unfold ASAN_GT in *;
  try unfold HIGHMEM_BEG in *; try unfold LOWMEM_END in *; try unfold APPMEM_END in *;
  try unfold ASAN_K in *; try unfold REAC_CTRL_IDENTITY_REPLY_K in *; try unfold AF.SLOT_STACK in *.

(* Two word values read at the same address agree modulo 2^64. *)

Lemma l2_wm_eq : forall m a v v', word_mem rsegs m a v -> word_mem rsegs m a v' -> v mod 2 ^ 64 = v' mod 2 ^ 64.
Proof.
  intros m a v v' H H'.
  assert (P : 2 ^ 64 <> 0) by lia.
  assert (E : forall k, (k < 8)%nat -> le_byte (v mod 2 ^ 64) 8 k = le_byte (v' mod 2 ^ 64) 8 k).
  { intros k Hk. pose proof (H k Hk) as H1. pose proof (H' k Hk) as H2.
    assert (H3 : Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (le_byte v' 8 k)) by congruence.
    apply (f_equal bv_unsigned) in H3. rewrite !kb_byte_unsigned in H3. clear H1 H2. rename H3 into H2.
    unfold le_byte in H2 |- *. change (8 * Z.of_nat 8) with 64 in H2 |- *. rewrite !Z.mod_mod by exact P.
    exact H2. }
  assert (R1 : 0 <= v mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (R2 : 0 <= v' mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  rewrite (kb_le8_digits _ R1), (kb_le8_digits _ R2).
  rewrite !E by lia. reflexivity.
Qed.

Lemma l2_dj_hi : forall (W : list (Z * Z)) a n, (forall lo hi, In (lo, hi) W -> a + n <= lo) -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn [disjoint_from]; [exact I|].
  split; [left; exact (H lo hi (or_introl eq_refl))|].
  apply IH. intros lo' hi' Hin. exact (H lo' hi' (or_intror Hin)).
Qed.

(* Every range at or above GT is apart from the runtime's cells (all below GT). *)

Lemma l2_rt : forall W, (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> rt_disjoint W.
Proof.
  intros W H. unfold rt_disjoint.
  repeat split; apply l2_dj_hi; intros lo hi Hin; pose proof (H lo hi Hin) as Hl; unfold AC.GT in Hl;
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN; lia.
Qed.

(* The class-1 layout of the side stack. *)

Lemma l2_fsc : forall FS, fs_hint FS 1 = FS + 8 /\ fs_flag FS 1 0 = FS + 20480 /\ fs_M 1 = 8192 /\
  fs_frame FS 1 0 = FS + 1085440 /\ fs_frame FS 1 (fs_M 1) = FS + 2134016.
Proof.
  intros FS. unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B.
  change (Z.of_nat 1) with 1. change (2 ^ (15 - 1)) with 16384. change (2 ^ (14 - 1)) with 8192.
  repeat split; lia.
Qed.

(* The call's write list. *)

Definition l2_W (phi len fr sp : Z) (G : list byte) (FS : Z) : list (Z * Z) :=
  reac_ctrl_identity_reply_fp phi len (fr + 256) (fr + 272) (fr + 304) sp G ++ fp_w [1%nat] FS ++
  [(shadow_addr (sp - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr sp)].

Lemma l2_W_eq : forall phi len fr sp G FS, l2_W phi len fr sp G FS =
  (if reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G
   then [(fr + 256, fr + 256 + 2); (fr + 272, fr + 272 + 8); (fr + 304, fr + 304 + 8)] else []) ++
  [(sp - 9072, sp); (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016)); (shadow_addr (sp - 9072), shadow_addr sp)].
Proof.
  intros phi len fr sp G FS. destruct (l2_fsc FS) as (F1 & F2 & F3 & F4 & F5).
  unfold l2_W, reac_ctrl_identity_reply_fp, fp_w, fp_w1, REAC_CTRL_IDENTITY_REPLY_K. cbn [flat_map].
  rewrite F5, F4, F1, F2, F3. rewrite <- !app_assoc. cbn [app].
  replace (FS + 8 + 8) with (FS + 16) by lia. replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  reflexivity.
Qed.

Lemma l2_W_lo : forall phi len fr sp G FS lo hi,
  AC.GT <= fr -> AC.GT <= FS -> AC.GT + 9072 <= sp ->
  In (lo, hi) (l2_W phi len fr sp G FS) -> AC.GT <= lo.
Proof.
  intros phi len fr sp G FS lo hi H1 H2 H3 Hin. rewrite l2_W_eq in Hin.
  unfold AC.GT, shadow_addr, ASAN_K in *.
  destruct (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G); cbn [app In] in Hin;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]); contradiction.
Qed.

Lemma l2_out : forall phi len fr sp G FS x,
  ~ (fr + 256 <= x < fr + 312) -> ~ (sp - 9072 <= x < sp) -> ~ (FS + 8 <= x < FS + 16) ->
  ~ (FS + 20480 <= x < FS + 28672) -> ~ (FS + 1085440 <= x < FS + 2134016) ->
  ~ (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) ->
  ~ (shadow_addr (sp - 9072) <= x < shadow_addr sp) ->
  Frame.outside (l2_W phi len fr sp G FS) x.
Proof.
  intros phi len fr sp G FS x N1 N2 N3 N4 N5 N6 N7. rewrite l2_W_eq.
  destruct (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G); cbn [app Frame.outside];
    repeat split; lia.
Qed.

(* l2_out per reply cell: the gaps [fr + 258, fr + 272) and [fr + 280, fr + 304) are outside the call's write
   list too (the callee writes the three cells themselves, not the frame bytes between them). *)

Lemma l2_out3 : forall phi len fr sp G FS x,
  ~ (fr + 256 <= x < fr + 258) -> ~ (fr + 272 <= x < fr + 280) -> ~ (fr + 304 <= x < fr + 312) ->
  ~ (sp - 9072 <= x < sp) -> ~ (FS + 8 <= x < FS + 16) ->
  ~ (FS + 20480 <= x < FS + 28672) -> ~ (FS + 1085440 <= x < FS + 2134016) ->
  ~ (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) ->
  ~ (shadow_addr (sp - 9072) <= x < shadow_addr sp) ->
  Frame.outside (l2_W phi len fr sp G FS) x.
Proof.
  intros phi len fr sp G FS x N1 N2 N3 N4 N5 N6 N7 N8 N9. rewrite l2_W_eq.
  destruct (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G); cbn [app Frame.outside];
    repeat split; lia.
Qed.

(* A flag byte of a class other than 1 lies at or above FS + 4096 and apart from the class-1 flag bytes
   [FS + 20480, FS + 28672). *)

Lemma l2_flag_other : forall FS c j, (c <= 10)%nat -> c <> 1%nat -> 0 <= j < AC.a_fs_M c ->
  FS + 4096 <= AC.a_fs_flag FS c j /\ (AC.a_fs_flag FS c j < FS + 20480 \/ FS + 28672 <= AC.a_fs_flag FS c j).
Proof.
  intros FS c j Hc Hc1 Hj. unfold AC.a_fs_flag, AC.a_fs_M in *.
  destruct c as [|[|c]].
  - change (2 ^ (14 - Z.of_nat 0)) with 16384 in Hj. change (2 ^ (15 - Z.of_nat 0)) with 32768. lia.
  - exfalso. apply Hc1. reflexivity.
  - assert (P : 2 ^ (15 - Z.of_nat (S (S c))) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* sl_fr_cl (Tac_slot) for a run whose writes may include shadow bytes: RT by RT_meta_write (every shadow byte
   readable after the run), the registered globals and the slot window addressable by the caller (their shadow
   bytes are kept or rewritten by the callee's own post); the rest as sl_fr_cl. *)
Lemma l2_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, 0 <= x < 6283264 -> outside W x) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 16 <= x < A + 312 -> outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> outside W x) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HSH HAH' HSTK HWlo HWhdr HWA HWsaved HWsh
    HWwin HrecK HAG' HWA' E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWAo & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HSH)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo;
          [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo;
          [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA A Hr9 HA64 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split; [|exact (HrecK Hrec)].
        intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. exact (HWsh x ltac:(lia)). }
  split; [exact HWwin|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* L2: FRA and ENT across the identity_reply call (its post's munch over its window, the class-1 side-stack bytes,
   the shadow of its window and, under reply_ok, the three reply cells), and across the lazy-page step md -> md'.
   AH / stklo / stkhi / ownership by a_laws_fs_store (every write outside a_store_ok is in the FakeStack or its
   shadow; a_fs_ok at return from the post's fp); RT by RT_meta_write; the rest by l2_run; ENT by ent_munch (no
   address ENT speaks of is written) and ent_mat. *)
Lemma f9_fra_call : forall g fr hb phi len regs regs' mem mem' md md' FS G,
  FRA B APIf ra g fr hb regs mem md -> f9_PL fr regs mem ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  munch (reac_ctrl_identity_reply_fp phi len (fr + 256) (fr + 272) (fr + 304) (AC.aspZ regs) G ++
         fp_w [1%nat] FS ++
         [(shadow_addr (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr (AC.aspZ regs))]) mem mem' ->
  wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  stk rsegs mem' (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) (AC.aspZ regs) ->
  addressable mem' (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
  (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G = true ->
     rw_cells rsegs mem' (fr + 256) [CB 2 (reply_addr G)] /\
     rw_cells rsegs mem' (fr + 272) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
     rw_cells rsegs mem' (fr + 304) [CB 8 (le8 (Z_to_bv 64 (ir_s G - 13)))]) ->
  shadow_rw mem' ->
  fp [1%nat] mem' (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) (AC.aspZ regs)
    (reac_ctrl_identity_reply_W phi (fr + 256) (fr + 272) (fr + 304) (AC.aspZ regs))
    (reac_ctrl_identity_reply_D phi len (fr + 256) (fr + 272) (fr + 304)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md' /\ (ENT APIf g hb mem md -> ENT APIf g hb mem' md').
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros g fr hb phi len regs regs' mem mem' md md' FS G HFRA HPL Htp HFS MU WM HRO Hstkw HADw Hreply HSRW HFP
    E2 E3 E4 E8 E9 E19 E26 Hmat.
  change (munch (l2_W phi len fr (AC.aspZ regs) G FS) mem mem') in MU.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWAf &
    HTop1 & HTop2 & HTop3 & Hhb & Hlive).
  destruct HPL as (Happ & Hgt & Hwd & HAge & HPLfs).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhi.
  destruct (f9_fs_place _ _ _ _ _ LAWS _ _ _ FS HAH Htp HFS) as (HFSgt & HFSst & _ & HFSapp).
  pose proof (proj1 (AC.a_laws_fs_state _ _ _ _ _ LAWS _ _ _ FS HAH Htp HFS)) as Hok.
  pose proof HFP as (DT & TS & C & T & DB & k & _ & _ & Hplace & _ & _ & Hcls & Hlo & Happw & _ & _).
  destruct Hplace as (_ & _ & _ & _ & HFSstk).
  apply Forall_inv in Hcls.
  rewrite Haspz in *.
  unfold AF.SLOT_STACK in Hstklo.
  assert (HK9 : REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  (* layout facts *)
  assert (HspA : sp <= APPMEM_END /\ HIGHMEM_BEG + 1044480 <= sp).
  { pose proof (Happw (sp - 1) ltac:(lia)) as P. l2_k. lia. }
  assert (HAb : 0 < A /\ A + 312 <= 2 ^ 64).
  { destruct Hspill as (_ & Hb & _). rewrite length_le8 in Hb. split; [l2_k; lia | lia]. }
  assert (HAfr : fr + FRAME_BYTES <= A) by (apply HAge; [exact Hr9 | lia]).
  assert (Hfrlo : (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) /\ fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ fr ltac:(lia)) as P1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as P2. l2_k. lia. }
  assert (HFSlo : FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { pose proof (HFSapp FS ltac:(l2_k; lia)) as P1.
    pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(l2_k; lia)) as P2. l2_k. lia. }
  assert (Hfrhi : FS + 6328320 <= fr /\
    ((AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= fr /\ fr + FRAME_BYTES <= APPMEM_END /\ sp = fr) \/
     (FS <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE))).
  { destruct Hloc as [[_ [Hspfr Hreal]]|[_ [_ [Hfs _]]]].
    - pose proof (Hreal fr ltac:(lia)) as R1. pose proof (Hreal (fr + FRAME_BYTES - 1) ltac:(lia)) as R2.
      split; [l2_k; lia | left; split; [lia | split; lia]].
    - destruct (Hfs fr ltac:(lia)) as (b & Hbr & Hb & Hb1 & Hb2).
      pose proof (l2_wm_eq _ _ _ _ Hb Htp) as Heq.
      assert (HbFS : b = FS) by (rewrite !Z.mod_small in Heq by lia; exact Heq).
      subst b. destruct (HPLfs FS Htp HFS ltac:(lia)) as [P1 P2].
      split; [lia | right; split; lia]. }
  destruct Hfrhi as [Hfrhi Harm].
  (* the side stack's state after the call *)
  assert (Hokp : AC.a_fs_ok mem' FS).
  { destruct (f9_fs_ok_to mem FS Hok) as (O2 & O3 & O4 & O5).
    destruct HFSstk as (_ & _ & HS).
    destruct Hcls as (_ & h1 & fl & Hh1 & Hfl & Hfll & Hflb).
    destruct (l2_fsc FS) as (F1 & F2 & F3 & F4 & F5).
    apply f9_fs_ok_of.
    - intros a Ha. exact (HS a ltac:(l2_k; lia)).
    - apply (kb_word_munch rsegs mem mem' _ (FS + 88) 20 O2 MU). intros j Hj.
      split; [l2_k; lia|]. apply l2_out; l2_k; lia.
    - rewrite (mbyte_munch rsegs _ mem mem' (FS + 96) MU); [exact O3 | l2_k; lia |].
      apply l2_out; l2_k; lia.
    - intros c Hc. destruct (Nat.eq_dec c 1) as [->|Hc1].
      + exists (bv_unsigned h1). exact (bytes_at_le8_word rsegs mem' (fs_hint FS 1) h1 Hh1).
      + destruct (O4 c Hc) as [h Hh]. exists h. apply (kb_word_munch rsegs mem mem' _ _ h Hh MU).
        intros j Hj. unfold AC.a_fs_hint. split; [l2_k; lia|]. apply l2_out; l2_k; lia.
    - intros c j Hc Hj. destruct (Nat.eq_dec c 1) as [->|Hc1].
      + destruct Hfl as (_ & _ & Hfl).
        assert (Hj' : (Z.to_nat j < length fl)%nat).
        { change (AC.a_fs_M 1) with (fs_M 1) in Hj. rewrite F3 in Hfll, Hj. lia. }
        destruct (nth_error fl (Z.to_nat j)) as [b|] eqn:En; [|apply nth_error_None in En; lia].
        pose proof (Hfl (Z.to_nat j) Hj') as Hb. rewrite En, Z2Nat.id in Hb by lia.
        assert (Hin : In b fl) by exact (nth_error_In fl _ En).
        rewrite Forall_forall in Hflb.
        replace (AC.a_fs_flag FS 1 j) with (fs_flag FS 1 0 + j)
          by (rewrite F2; unfold AC.a_fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
        destruct (Hflb b Hin) as [-> | ->]; [left | right]; exact Hb.
      + pose proof (a_fs_flag_range FS c j Hc Hj) as Hr.
        pose proof (l2_flag_other FS c j Hc Hc1 Hj) as Ho.
        rewrite (mbyte_munch rsegs _ mem mem' (AC.a_fs_flag FS c j) MU); [exact (O5 c j Hc Hj) | l2_k; lia |].
        apply l2_out; l2_k; lia. }
  (* AH and stklo across the call (law: stores into the side stack and its shadow) *)
  assert (Hagree : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns Hnf Hnsh. apply MU. rewrite MState.unsigned_lit by exact Ha.
    apply l2_out.
    - intro Hin. destruct Harm as [[R1 [R2 R3]]|[S1 S2]].
      + apply Hns. right. left. l2_k; lia.
      + apply Hnf. l2_k; lia.
    - intro Hin. apply Hns. right. left. l2_k; lia.
    - intro Hin. apply Hnf. l2_k; lia.
    - intro Hin. apply Hnf. l2_k; lia.
    - intro Hin. apply Hnf. l2_k; lia.
    - intro Hin. apply Hnsh. exists (8 * (a - ASAN_K)). l2_k. split; lia.
    - intro Hin. apply Hns. right. right. right. exists (8 * (a - ASAN_K)). l2_k. split; [lia | right; left; lia]. }
  assert (Hwm : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a).
  { intros a _ Hw. exact (WM (Z_to_bv 64 a) Hw). }
  destruct (f9_fs_store _ _ _ _ _ LAWS (hb ++ g_H g) mem mem' md FS HAH Htp HFS Hagree Hwm Hokp)
    as (HAH' & Hown & Hstkeq & Hstkhi).
  clear Hagree Hwm Hokp Hok Hcls HFSstk.
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { apply (l2_run g fr hb regs regs' mem mem' md (l2_W phi len fr sp G FS) HFRA MU WM HRO).
    - apply l2_rt. intros lo hi Hin.
      apply (l2_W_lo phi len fr sp G FS lo hi); [exact Hgt | l2_k; lia | l2_k; lia | exact Hin].
    - intros a Ha. destruct (HSRW a Ha) as (_ & b & Hb). exists b. exact Hb.
    - exact HAH'.
    - exact Hstkeq.
    - intros x Hx. apply l2_out; l2_k; lia.
    - intros x Hx. apply l2_out; l2_k; lia.
    - intros A' HA' HA'r x Hx.
      assert (EA : A' = A).
      { unfold rg in Hr9. rewrite Hr9 in HA'. apply (f_equal (bv_unsigned (n:=64))) in HA'.
        rewrite !MState.unsigned_lit in HA' by lia. lia. }
      subst A'. apply l2_out; l2_k; lia.
    - intros x Hx. apply l2_out; l2_k; lia.
    - intros x Hx. apply l2_out; l2_k; lia.
    - (* the entry-anchored window [S - SLOT_STACK, S) after the call *)
      apply (fl_stk _ mem mem' (g_S g - AF.SLOT_STACK) (g_S g) Hwin MU WM).
      intros x Hx.
      destruct (Z_lt_le_dec x (sp - REAC_CTRL_IDENTITY_REPLY_K)) as [Hl|Hl];
        [left; apply l2_out; l2_k; lia|].
      destruct (Z_lt_le_dec x sp) as [Hl2|Hl2];
        [right; destruct Hstkw as (_ & _ & Hs); exact (proj2 (Hs x ltac:(lia)))|].
      (* at or above sp only the three reply cells of the real arm are written *)
      destruct (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G) eqn:Erok;
        [|left; rewrite l2_W_eq, Erok; cbn [app Frame.outside]; repeat split; l2_k; lia].
      destruct (Hreply eq_refl) as (R1 & R2 & R3).
      destruct (Z_le_gt_dec (fr + 256) x) as [C1|C1]; [destruct (Z_lt_ge_dec x (fr + 258)) as [C2|C2]|].
      + right. exact (f9_cell_byte mem' (fr + 256) 2 _ x R1 ltac:(lia)).
      + destruct (Z_le_gt_dec (fr + 272) x) as [D1|D1]; [destruct (Z_lt_ge_dec x (fr + 280)) as [D2|D2]|].
        * right. exact (f9_cell_byte mem' (fr + 272) 8 _ x R2 ltac:(lia)).
        * destruct (Z_le_gt_dec (fr + 304) x) as [E1|E1]; [destruct (Z_lt_ge_dec x (fr + 312)) as [E2'|E2']|].
          -- right. exact (f9_cell_byte mem' (fr + 304) 8 _ x R3 ltac:(lia)).
          -- left. apply l2_out3; l2_k; lia.
          -- left. apply l2_out3; l2_k; lia.
        * left. apply l2_out3; l2_k; lia.
      + left. apply l2_out3; l2_k; lia.
    - (* the FakeStack frame record: its flag byte and slot word are class-6 cells of FS *)
      intros (FS' & jj & Htp' & HFS'r & Hj & Hfrj & Hflag & Htail).
      assert (EFS : FS' = FS).
      { pose proof (l2_wm_eq _ _ _ _ Htp' Htp) as Hm. rewrite !Z.mod_small in Hm by lia. exact Hm. }
      subst FS'.
      assert (HB6 : fs_B 6 = 4096) by reflexivity.
      assert (HM6 : fs_M 6 = 256) by reflexivity.
      assert (Hfl : fs_flag FS 6 jj = FS + 36352 + jj) by (unfold fs_flag; cbn; lia).
      assert (Hfrv : fr = FS + 6328320 + jj * 4096) by (rewrite Hfrj; unfold fs_frame, fs_B; cbn; lia).
      rewrite HM6 in Hj.
      exists FS, jj.
      split.
      { apply (kb_word_munch rsegs mem mem' (l2_W phi len fr sp G FS) _ FS Htp MU).
        intros k0 Hk0. pose proof (eq_refl : AC.as_tp AC.ASYMS = ltac:(let v := eval cbv in (AC.as_tp AC.ASYMS) in exact v)) as Ktp.
        split; [lia|]. apply l2_out; l2_k; lia. }
      split; [exact HFS|].
      split; [rewrite HM6; exact Hj|].
      split; [exact Hfrj|].
      split.
      { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx. rewrite Hfl in Hx.
        apply l2_out; l2_k; lia. }
      { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx. rewrite HB6 in Hx.
        apply l2_out; l2_k; lia. }
    - (* the registered globals stay addressable: their shadow bytes lie below every byte the call writes *)
      intros a Ha. pose proof (f9_ag_lt a Ha) as Hab.
      apply (addr1_munch (l2_W phi len fr sp G FS) mem mem' a MU); [|exact (HAGf a Ha)].
      apply l2_out; l2_k; lia.
    - (* the slot window outside the frame stays addressable *)
      intros a Ha Hnf.
      destruct (Z_le_gt_dec (sp - REAC_CTRL_IDENTITY_REPLY_K) a) as [Hw1|Hw1];
        [destruct (Z_lt_ge_dec a sp) as [Hw2|Hw2]|].
      + exact (f9_addr1 mem' (sp - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K a HADw ltac:(lia)).
      + apply (addr1_munch (l2_W phi len fr sp G FS) mem mem' a MU); [|exact (HWAf a Ha Hnf)].
        apply l2_out; l2_k; lia.
      + apply (addr1_munch (l2_W phi len fr sp G FS) mem mem' a MU); [|exact (HWAf a Ha Hnf)].
        apply l2_out; l2_k; lia.
    - exact E2.
    - exact E3.
    - exact E4.
    - exact E8.
    - exact E9.
    - exact E19.
    - exact E26. }
  split.
  { apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat. }
  intros HENT.
  pose proof HENT as (Hasp & _).
  assert (HS0 : 0 <= g_S g) by (rewrite <- Hasp; apply (bv_unsigned_in_range 64)).
  eapply ent_mat; [|exact Hmat].
  eapply ent_munch with (W := l2_W phi len fr sp G FS);
    [exact HENT | exact HAH | exact MU | | exact Hstkeq | exact Hstkhi |].
  - intros x Hk. destruct Hk as [Hblk | [Himg | [Habv | [(b & Hor & ->) | Hblks]]]].
    + destruct Hblk as (q & k0 & i & Hin & Hni & Hi & ->).
      destruct (f9_blocks _ _ _ _ _ LAWS (hb ++ g_H g) mem md q k0 HAH (in_or_app _ _ _ (or_intror Hin)))
        as (Hq4 & Hend & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnfs).
      assert (HnF : ~ (FS <= q + i < FS + AC.FS_SIZE)).
      { intro HC. apply Hnfs. exists FS. split; [exact HFS | split; [exact Htp | exact HC]]. }
      apply l2_out; l2_k; lia.
    + pose proof (img_below_GT x Himg) as Hxg. apply l2_out; l2_k; lia.
    + apply l2_out; l2_k; lia.
    + destruct Hor as [Hi|Hr].
      * pose proof (img_below_GT b Hi) as Hbg. apply l2_out; l2_k; lia.
      * apply l2_out; l2_k; lia.
    + (* the shadow byte of an entry block's byte (ent_kept's fifth case): the block byte is app memory off FS
         and below stklo, so its shadow byte is outside every range of the call's write list *)
      destruct Hblks as (q & k0 & i & Hin & Hni & Hi & ->).
      destruct (f9_blocks _ _ _ _ _ LAWS (hb ++ g_H g) mem md q k0 HAH (in_or_app _ _ _ (or_intror Hin)))
        as (Hq4 & Hend & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnfs).
      assert (HnF : ~ (FS <= q + i < FS + AC.FS_SIZE)).
      { intro HC. apply Hnfs. exists FS. split; [exact HFS | split; [exact Htp | exact HC]]. }
      apply l2_out; l2_k; lia.
  - intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.


End S_l2.

Section S_l3.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Lemma l3_sh : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof.
  intros fr k. unfold Sfr, shadow_addr.
  replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

(* An address is outside f9_W9 fr, or one of its three shadow bytes, or in the frame cells [fr + 256, fr + 312). *)

Lemma l3_W_cases : forall fr x,
  outside (f9_W9 fr) x \/ x = Sfr fr + 32 \/ x = Sfr fr + 34 \/ x = Sfr fr + 38 \/ (fr + 256 <= x < fr + 312).
Proof.
  intros fr x. unfold f9_W9. cbn [outside].
  destruct (Z.eq_dec x (Sfr fr + 32)) as [E|N1]; [right; left; exact E|].
  destruct (Z.eq_dec x (Sfr fr + 34)) as [E|N2]; [right; right; left; exact E|].
  destruct (Z.eq_dec x (Sfr fr + 38)) as [E|N3]; [right; right; right; left; exact E|].
  destruct (Z_le_gt_dec (fr + 256) x); [destruct (Z_lt_ge_dec x (fr + 312))|].
  - right; right; right; right; lia.
  - left. repeat split; try exact I; lia.
  - left. repeat split; try exact I; lia.
Qed.

(* Outside f9_W9 per written cell: the frame bytes between the three cells are not written either. *)

Lemma f9_out9 : forall fr x,
  ~ (fr + 256 <= x < fr + 258) -> ~ (fr + 272 <= x < fr + 280) -> ~ (fr + 304 <= x < fr + 312) ->
  x <> Sfr fr + 32 -> x <> Sfr fr + 34 -> x <> Sfr fr + 38 ->
  outside (f9_W9 fr) x.
Proof.
  intros fr x N1 N2 N3 N4 N5 N6. unfold f9_W9. cbn [outside]. repeat split; try exact I; lia.
Qed.

(* Every FakeStack metadata cell is at or above FS. *)

Lemma l3_fs_meta_lo : forall FS q, fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* AH, ownership and the stack bounds across F9's six stores: real arm by a_laws_store (frame bytes real stack, frame
   shadow bytes the shadow of real-stack bytes); side arm by a_fs_ok_store_AH (frame bytes in FS above the metadata,
   shadow bytes the shadow of FS bytes and not app, so not metadata). *)
Lemma l3_ah : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md ->
  munch (f9_W9 fr) mem mem' -> wmono rsegs mem mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) -> exists b, mbyte rsegs mem' q = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md q <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md q) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros g fr hb regs mem mem' md HFRA MU WM HPRES.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWAf &
    HTop1 & HTop2 & HTop3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (Hw2 : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a _ Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. destruct Ha as [Ha|Ha]; lia. }
  unfold AC.GT in Hgt.
  destruct Hloc as [(_ & _ & Hreal)|(_ & HfsbS & Hfs & _)].
  - (* real arm: every written address is a_store_ok *)
    assert (P1 : forall a, 0 <= a < 2 ^ 64 ->
              ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
              mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hn. apply MU. rewrite MState.unsigned_lit by exact Ha.
      destruct (l3_W_cases fr a) as [Ho | [E | [E | [E | Hb]]]]; [exact Ho | exfalso ..];
        apply Hn; unfold AC.a_store_ok.
      - right; right; right. exists (fr + 8 * 32).
        split; [rewrite l3_sh; exact E | right; left; apply Hreal; lia].
      - right; right; right. exists (fr + 8 * 34).
        split; [rewrite l3_sh; exact E | right; left; apply Hreal; lia].
      - right; right; right. exists (fr + 8 * 38).
        split; [rewrite l3_sh; exact E | right; left; apply Hreal; lia].
      - right; left; apply Hreal; lia. }
    exact (AC.a_laws_store _ _ _ _ _ LAWS (hb ++ g_H g) mem mem' md HAH P1 Hw2).
  - (* side arm: the FS word at tp, the frame inside FS above the class-6 frames *)
    destruct (Hfs fr ltac:(lia)) as (b & Hbr & Hwb & Hblo & Hbhi).
    destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (b' & Hbr' & Hwb' & Hblo' & Hbhi').
    assert (Ebb : b' = b).
    { pose proof (l2_wm_eq _ _ _ _ Hwb' Hwb) as E. rewrite !Z.mod_small in E by lia. exact E. }
    subst b'.
    pose proof (HfsbS b Hwb Hbr) as Hb6.
    pose proof (f9_fs_place _ _ _ _ _ LAWS _ _ _ b HAH Hwb Hbr) as (_ & Hstkb & _ & Happfs).
    assert (Hsz : b + AC.FS_SIZE <= 2 ^ 64) by (unfold AC.FS_SIZE, AF.SLOT_STACK, APPMEM_END in *; lia).
    assert (Hmeta : forall q, fs_meta b q -> outside (f9_W9 fr) q).
    { intros q Hq. pose proof (fs_meta_below b q Hq) as Hq1. pose proof (l3_fs_meta_lo b q Hq) as Hq0.
      assert (Hqa : app_mem q) by (apply Happfs; unfold AC.FS_SIZE; lia).
      destruct (l3_W_cases fr q) as [Ho | [E | [E | [E | Hb]]]]; [exact Ho | exfalso ..].
      - apply (AsanRTFacts.app_not_shadow q Hqa). rewrite E, <- (l3_sh fr 32).
        apply AsanRTFacts.shadow_of_app, Happ. lia.
      - apply (AsanRTFacts.app_not_shadow q Hqa). rewrite E, <- (l3_sh fr 34).
        apply AsanRTFacts.shadow_of_app, Happ. lia.
      - apply (AsanRTFacts.app_not_shadow q Hqa). rewrite E, <- (l3_sh fr 38).
        apply AsanRTFacts.shadow_of_app, Happ. lia.
      - lia. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (b <= q < b + AC.FS_SIZE) ->
              ~ (exists c, b <= c < b + AC.FS_SIZE /\ q = shadow_addr c) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq _ Hnr Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
      destruct (l3_W_cases fr q) as [Ho | [E | [E | [E | Hb]]]]; [exact Ho | exfalso ..].
      - apply Hnsh. exists (fr + 8 * 32). split; [unfold AC.FS_SIZE in *; lia | rewrite l3_sh; exact E].
      - apply Hnsh. exists (fr + 8 * 34). split; [unfold AC.FS_SIZE in *; lia | rewrite l3_sh; exact E].
      - apply Hnsh. exists (fr + 8 * 38). split; [unfold AC.FS_SIZE in *; lia | rewrite l3_sh; exact E].
      - apply Hnr. unfold AC.FS_SIZE in *; lia. }
    exact (a_fs_ok_store_AH AC.ASYMS _ _ _ _ (f9_W9 fr) (hb ++ g_H g) mem mem' md b LAWS HAH Hwb Hbr Hsz MU
      Hw2 HPRES Hmeta Hagree).
Qed.

(* L3: FRA and ENT across F9's six stores: sl_fr_meta with the new FRAME_SHADOW-byte shadow list (every byte the stores
   do not write keeps its value, the written ones are present), and ent_store (the stores write the frame and its
   shadow only). *)
Lemma f9_fra_st : forall g fr hb regs regs' mem mem' md,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  munch (f9_W9 fr) mem mem' -> wmono rsegs mem mem' ->
  (forall q, (exists b, mbyte rsegs mem q = Some b) -> exists b, mbyte rsegs mem' q = Some b) ->
  (forall x, fr + 256 <= x < fr + 258 \/ fr + 272 <= x < fr + 280 \/ fr + 304 <= x < fr + 312 ->
     exists b, mbyte rsegs mem' x = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\ ENT APIf g hb mem' md.
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros g fr hb regs regs' mem mem' md HFRA HENT MU WM HPRES HCELL E2 E3 E4 E8 E9 E19 E26.
  destruct (l3_ah g fr hb regs mem mem' md HFRA MU WM (fun q _ Hq => HPRES q Hq))
    as (HAH' & Hown & HSTK & HSTKhi).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (_ & HfrA9 & _ & _).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWAf &
    HTop1 & HTop2 & HTop3 & Hhb & Hlive).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ HAH) as Hhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAfr : fr + FRAME_BYTES <= A).
  { unfold rg in Hr9. rewrite Hr9, MState.unsigned_lit in HfrA9 by lia. exact HfrA9. }
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. destruct Ha as [Ha|Ha]; lia. }
  assert (Hgt' : 6283264 <= fr) by (unfold AC.GT in Hgt; lia).
  assert (Hfrlo : fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { pose proof (Happ fr ltac:(lia)) as P1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as P2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  pose proof (Z.div_mod fr 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound fr 8 ltac:(lia)) as Hmb.
  assert (HSfr : LOWMEM_END <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { unfold Sfr, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG. unfold APPMEM_END in Hub. lia. }
  assert (HKl : LOWMEM_END = 2147450880) by reflexivity.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAhi : HIGHMEM_BEG <= A) by (unfold AF.SLOT_STACK in *; lia).
  assert (Hout : forall x, (x < fr + 256 \/ fr + 312 <= x) -> (x < Sfr fr + 32 \/ Sfr fr + 39 <= x) ->
                   outside (f9_W9 fr) x).
  { intros x Hx1 Hx2. unfold f9_W9. cbn [outside]. repeat split; try exact I; lia. }
  assert (HA'eq : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' HA' HA'r.
    assert (Eb : Z_to_bv 64 A' = Z_to_bv 64 A) by (rewrite <- HA'; exact Hr9).
    apply (f_equal bv_unsigned) in Eb. rewrite !MState.unsigned_lit in Eb by lia. exact Eb. }
  assert (HRO : ro_agree rsegs mem').
  { apply (ro_agree_munch (f9_W9 fr) mem mem' Hro MU). intros x Hx. apply ro_addr_false_w.
    destruct (Z_lt_le_dec (bv_unsigned x) 6283264) as [Hl|Hl]; [|exact Hl].
    exfalso. apply Hx. apply Hout; unfold LOWMEM_END in HSfr; lia. }
  assert (HSHN : exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
  { destruct Hsh as (sh0 & Hb0 & Hl0).
    apply (f9_bytes_ex mem' (Z.to_nat FRAME_SHADOW) (Sfr fr)); [lia | |].
    - destruct Hb0 as (_ & Hb1 & _). rewrite Hl0 in Hb1. exact Hb1.
    - intros i Hi. apply HPRES. destruct Hb0 as (_ & _ & Hb2).
      destruct (nth_error sh0 i) as [bb|] eqn:Enth.
      + exists bb. rewrite <- Enth. apply Hb2. lia.
      + apply nth_error_None in Enth. lia. }
  split.
  - apply (sl_fr_meta B APIf ra empty FF g fr hb regs regs' mem mem' md (f9_W9 fr) HFRA MU WM HRO).
    + unfold rt_disjoint, f9_W9. cbn [disjoint_from].
      unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
        RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
      unfold LOWMEM_END in HSfr.
      repeat split; first [left; lia | exact I].
    + exact HAH'.
    + exact HSTK.
    + exact Happ.
    + exact Hgt.
    + exact HSHN.
    + intros x _ Hnb Hns.
      destruct (l3_W_cases fr x) as [Ho | [E | [E | [E | Hb]]]]; [exact Ho | exfalso; lia ..].
    + intros A' HA' HA'r x Hx. rewrite (HA'eq A' HA' HA'r) in Hx. apply Hout; [right | right]; lia.
    + intros x Hx. apply Hout; [right | right]; lia.
    + intros A' HA' HA'r x Hx. rewrite (HA'eq A' HA' HA'r) in Hx. apply Hout; [right | right]; lia.
    + (* the entry-anchored window: a byte of it is outside the stores, or one of the cells they wrote *)
      intros x Hx.
      destruct (Z_le_gt_dec (fr + 256) x) as [C1|C1]; [destruct (Z_lt_ge_dec x (fr + 258)) as [C2|C2]|].
      * right. destruct (HCELL x ltac:(lia)) as (bb & Hbb). exact (f9_mem_some mem' x bb ltac:(lia) Hbb).
      * destruct (Z_le_gt_dec (fr + 272) x) as [D1|D1]; [destruct (Z_lt_ge_dec x (fr + 280)) as [D2|D2]|].
        -- right. destruct (HCELL x ltac:(lia)) as (bb & Hbb). exact (f9_mem_some mem' x bb ltac:(lia) Hbb).
        -- destruct (Z_le_gt_dec (fr + 304) x) as [F1|F1]; [destruct (Z_lt_ge_dec x (fr + 312)) as [F2|F2]|].
           ++ right. destruct (HCELL x ltac:(lia)) as (bb & Hbb). exact (f9_mem_some mem' x bb ltac:(lia) Hbb).
           ++ left. apply f9_out9; unfold AF.SLOT_STACK in *; lia.
           ++ left. apply f9_out9; unfold AF.SLOT_STACK in *; lia.
        -- left. apply f9_out9; unfold AF.SLOT_STACK in *; lia.
      * left. apply f9_out9; unfold AF.SLOT_STACK in *; lia.
    + (* the registered globals stay addressable: their shadow bytes miss the frame and its shadow *)
      intros a Ha. pose proof (f9_ag_lt a Ha) as Hab.
      apply (addr1_munch (f9_W9 fr) mem mem' a MU); [|exact (HAGf a Ha)].
      apply f9_out9; unfold Sfr, shadow_addr, ASAN_K, AC.GT, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia.
    + exact E2.
    + exact E3.
    + exact E4.
    + exact E8.
    + exact E9.
    + exact E19.
    + exact E26.
  - eapply ent_store with (W := f9_W9 fr); [exact HENT | exact HFRA | exact MU | | exact HSTK | exact HSTKhi |].
    + intros x Hx. destruct (l3_W_cases fr x) as [Ho | [E | [E | [E | Hb]]]];
        [left; exact Ho | right; right; right; lia .. | right; right; left; lia].
    + intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

End S_l3.

Lemma l9_rg_eq : forall regs (r : bv 5) x y, rg regs r x -> rg regs r y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  x = y.
Proof.
  intros regs r x y Hx Hy Bx By. unfold rg in *. rewrite Hx in Hy.
  apply (f_equal (bv_unsigned (n:=64))) in Hy. rewrite !MState.unsigned_lit in Hy by lia. exact Hy.
Qed.

(* A kind-name address is QMARK or a table entry. *)

Lemma l9_kn_in : forall x, In (kind_name_addr x) (QMARK :: kind_name_addrs).
Proof.
  intros x. unfold kind_name_addr. destruct (x <=? 13).
  - destruct (nth_in_or_default (Z.to_nat x) kind_name_addrs QMARK) as [H|H];
      [right; exact H | rewrite H; left; reflexivity].
  - left. reflexivity.
Qed.

(* Each of them is below 2^47 and starts a registered global (AF.frame_AG). *)

Lemma l9_kn_glob : forall a, In a (QMARK :: kind_name_addrs) -> 0 <= a < 2 ^ 47 /\ in_globals AF.frame_AG a.
Proof.
  intros a Hin. unfold QMARK, kind_name_addrs in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [E | Hin];
    [split; [lia | exists a; eexists; split;
       [rewrite <- E; unfold AF.frame_AG; cbn [In]; repeat (first [left; reflexivity | right]) | lia]] |]).
  destruct Hin.
Qed.

(* The first name byte of a kind 0..13 is not '?' (63). *)

Local Ltac l9_nm := eexists; split; [reflexivity | let Hc := fresh "Hc" in intro Hc; vm_compute in Hc; discriminate Hc].

Lemma l9_name0 : forall v, 0 <= v <= 13 ->
  exists c, firstn 1 (skipn 0 (cstr_bytes (kind_name v))) = [c] /\ bv_unsigned c <> 63.
Proof.
  intros v Hv.
  assert (H : v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7 \/ v = 8 \/ v = 9 \/ v = 10 \/
              v = 11 \/ v = 12 \/ v = 13) by lia.
  repeat (destruct H as [-> | H]; [l9_nm |]). subst v. l9_nm.
Qed.

Section S_l9.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The entry facts phase A reads: the frame and spill-base layout, the FRAME_SHADOW frame shadow bytes writable (RT's
   shadow_rw), the name byte's shadow byte (the name address is a registered global, addressable by FRA) and the
   first name byte (not '?'). *)
Lemma f9_entry_of : forall g j phi fr regs mem md A,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  bytes_at rsegs mem (kind_name_addr (t_k (g_in g) j)) (cstr_bytes (kind_name (t_k (g_in g) j))) ->
  0 <= kind_name_addr (t_k (g_in g) j) < 2 ^ 47 /\ 0 <= Sfr fr /\ 0 <= fr /\ 0 <= A /\
  fr + FRAME_BYTES <= A /\ A + 416 <= 2 ^ 64 /\ Sfr fr + FRAME_SHADOW <= A /\
  (Sfr fr + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= Sfr fr) /\
  wr_at rsegs mem (Sfr fr) FRAME_SHADOW /\
  (exists b, ov_read_bytes rsegs mem (wa (kind_name_addr (t_k (g_in g) j) / 8 + ASAN_K)) 1 = Some [b] /\
             (bv_signed b = 0 \/ kind_name_addr (t_k (g_in g) j) mod 8 < bv_signed b)) /\
  (exists c, ov_read_bytes rsegs mem (wa (kind_name_addr (t_k (g_in g) j))) 1 = Some [c] /\ bv_unsigned c <> 63).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros g j phi fr regs mem md A HFRA Hr9 HAb Hname.
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (Hgt & Happ).
  pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA) as (_ & HfrA9 & _ & _).
  destruct HFRA as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9' & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWAf &
    HTop1 & HTop2 & HTop3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhi.
  pose proof Hwin as (Hwb0 & Hwb1 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA0b : 0 <= A0 < 2 ^ 64) by lia.
  assert (EA : A = A0) by exact (l9_rg_eq regs 9 A A0 Hr9 Hr9' HAb HA0b).
  subst A0.
  assert (HAfr : fr + FRAME_BYTES <= A).
  { unfold rg in Hr9. rewrite Hr9, MState.unsigned_lit in HfrA9 by lia. exact HfrA9. }
  assert (Hv13 : 0 <= t_k (g_in g) j <= 13).
  { pose proof (ctrlparse_kind_range (t_len (g_in g) j) (t_g (g_in g) j)) as Hk. unfold t_k. lia. }
  (* the FRAME_SHADOW frame shadow bytes are shadow memory *)
  assert (HshIS : forall i, 0 <= i < FRAME_SHADOW -> in_shadow (Sfr fr + i)).
  { intros i Hi. replace (Sfr fr + i) with (shadow_addr (fr + 8 * i)).
    - apply shadow_of_app. apply Happ. lia.
    - unfold Sfr, shadow_addr. replace (fr + 8 * i) with (fr + i * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (HshB : LOWMEM_END <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (HshIS 0 ltac:(lia)) as S0. pose proof (HshIS (FRAME_SHADOW - 1) ltac:(lia)) as S1.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in S0, S1 |- *. lia. }
  (* the kind-name address and its shadow byte *)
  destruct (l9_kn_glob (kind_name_addr (t_k (g_in g) j)) (l9_kn_in (t_k (g_in g) j))) as (Hkb & Hkg).
  destruct (sl_shadow1 mem (kind_name_addr (t_k (g_in g) j)) (HAGf _ Hkg)) as (b & Hb & Hck & _).
  rewrite Z.shiftr_div_pow2 in Hb by lia. change (2 ^ 3) with 8 in Hb.
  (* the first name byte *)
  pose proof (bytes_at_ov_read rsegs mem (kind_name_addr (t_k (g_in g) j)) (cstr_bytes (kind_name (t_k (g_in g) j)))
    0 1 Hname ltac:(unfold cstr_bytes; rewrite length_app; cbn [length]; lia)) as Hrd.
  destruct (l9_name0 (t_k (g_in g) j) Hv13) as (c & Hc1 & Hc2).
  rewrite Hc1 in Hrd. cbn [Z.of_nat] in Hrd. rewrite Z.add_0_r in Hrd.
  unfold AC.GT in Hgt.
  split; [exact Hkb|].
  split; [unfold LOWMEM_END in HshB; lia|].
  split; [lia|].
  split; [lia|].
  split; [exact HAfr|].
  split; [lia|].
  split.
  { unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
  split.
  { pose proof (Happ fr ltac:(lia)) as Ap0. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Ap1.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ap0, Ap1, HshB. lia. }
  split.
  { refine (conj _ (conj _ _)).
    - unfold LOWMEM_END in HshB. lia.
    - unfold HIGHMEM_BEG in HshB. lia.
    - intros i Hi. exact (proj1 (AsanRTInv.RT_shadow_rw _ _ _ HRT _ (HshIS i Hi))). }
  split; [exists b; split; [exact Hb | exact Hck] | exists c; split; [exact Hrd | exact Hc2]].
Qed.

End S_l9.


Lemma l7_flen0 : forall g j, 0 <= flen g j.
Proof.
  intros g j. unfold flen, t_len, f_len, f_L, f_h, inb, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.bz.
  match goal with |- context [bv_unsigned ?b1] =>
    match goal with |- context [bv_unsigned ?b2] =>
      assert_fails (constr_eq b1 b2);
      pose proof (bv_unsigned_in_range _ b1) as H1; pose proof (bv_unsigned_in_range _ b2) as H2
    end
  end.
  unfold bv_modulus in H1, H2. change (2 ^ Z.of_N 8) with 256 in H1, H2.
  destruct (Z.leb_spec 2 (f_left (g_in g) (fc (g_in g) j))); lia.
Qed.

(* The shadow byte of an app byte is shadow memory; an app byte is not shadow memory. *)

Lemma l7_app_sh : forall a, app_mem a -> in_shadow (shadow_addr a).
Proof.
  intros a Ha.
  unfold app_mem, in_shadow, shadow_addr, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
    APPMEM_END in *.
  destruct Ha as [Ha|Ha]; [left|right]; Z.div_mod_to_equations; lia.
Qed.

Lemma l7_app_nsh : forall a, app_mem a -> ~ in_shadow a.
Proof.
  intros a Ha Hs.
  unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* An app byte apart from the three frame cells is outside the six store ranges. *)

Lemma l7_app_out : forall fr x, 0 <= fr -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> app_mem x ->
  (x < fr + 256 \/ fr + 312 <= x) -> outside (f9_WA (Sfr fr) fr) x.
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros fr x H0 Happ Hx Hpos.
  assert (S1 : in_shadow (Sfr fr + 32)).
  { replace (Sfr fr + 32) with (shadow_addr (fr + 256))
      by (unfold Sfr, shadow_addr; clear - H0; Z.div_mod_to_equations; lia).
    apply l7_app_sh, Happ. lia. }
  assert (S2 : in_shadow (Sfr fr + 34)).
  { replace (Sfr fr + 34) with (shadow_addr (fr + 272))
      by (unfold Sfr, shadow_addr; clear - H0; Z.div_mod_to_equations; lia).
    apply l7_app_sh, Happ. lia. }
  assert (S3 : in_shadow (Sfr fr + 38)).
  { replace (Sfr fr + 38) with (shadow_addr (fr + 304))
      by (unfold Sfr, shadow_addr; clear - H0; Z.div_mod_to_equations; lia).
    apply l7_app_sh, Happ. lia. }
  pose proof (l7_app_nsh x Hx) as Hnx.
  unfold f9_WA. cbn [outside].
  repeat split; intro Hr.
  - apply Hnx. replace x with (Sfr fr + 32) by lia. exact S1.
  - lia.
  - apply Hnx. replace x with (Sfr fr + 34) by lia. exact S2.
  - lia.
  - apply Hnx. replace x with (Sfr fr + 38) by lia. exact S3.
  - lia.
Qed.

(* The shadow byte of an app byte y apart from the frame cells' granules is outside the six store ranges. *)

Lemma l7_sh_out : forall fr y, 0 <= fr -> fr mod 32 = 0 -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  app_mem y -> (y < fr + 256 \/ fr + 312 <= y) -> outside (f9_WA (Sfr fr) fr) (shadow_addr y).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros fr y H0 Hm Happ Hy Hpos.
  pose proof (l7_app_sh y Hy) as Hs.
  assert (Hy0 : 0 <= y) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hy; lia).
  assert (Hc : forall x, fr + 256 <= x < fr + 312 -> x <> shadow_addr y).
  { intros x Hx E. apply (l7_app_nsh x); [apply Happ; lia | rewrite E; exact Hs]. }
  unfold f9_WA. cbn [outside].
  repeat split; intro Hr;
    first [ exact (Hc (shadow_addr y) ltac:(lia) eq_refl)
          | (unfold Sfr, shadow_addr in Hr; clear - Hr Hm Hpos H0 Hy0; Z.div_mod_to_equations; lia) ].
Qed.

(* A byte kept by munch. *)

Lemma l7_mbyte_keep : forall W (m m' : word -> option byte) a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  mbyte rsegs m' a = mbyte rsegs m a.
Proof.
  intros W m m' a MU Ha Ho. unfold mbyte. rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
  rewrite MState.unsigned_lit by lia. exact Ho.
Qed.

(* A word kept by munch, both ways. *)

Lemma l7_wm_keep : forall W (m m' : word -> option byte) a v, munch W m m' -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall x, a <= x < a + 8 -> outside W x) ->
  (word_mem rsegs m a v <-> word_mem rsegs m' a v).
Proof.
  intros W m m' a v MU H0 H1 HO.
  assert (E : forall k, (k < 8)%nat -> mbyte rsegs m' (a + Z.of_nat k) = mbyte rsegs m (a + Z.of_nat k)).
  { intros k Hk. apply (l7_mbyte_keep W); [exact MU | lia | apply HO; lia]. }
  unfold word_mem. split; intros H k Hk.
  - rewrite E by exact Hk. exact (H k Hk).
  - rewrite <- E by exact Hk. exact (H k Hk).
Qed.

(* One byte of a byte list. *)

Lemma l7_byte_of : forall m a bs i b, bytes_at rsegs m a bs -> nth_error bs i = Some b ->
  bytes_at rsegs m (a + Z.of_nat i) [b].
Proof.
  intros m a bs i b (H0 & H1 & H) E.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; congruence).
  split; [lia|]. split; [cbn [length]; lia|].
  intros k Hk. cbn [length] in Hk. assert (Ek : k = 0%nat) by lia. subst k. cbn [nth_error].
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r. rewrite (H i Hi). exact E.
Qed.

(* A frame cell offset k (a multiple of 8) of a 32-aligned frame keeps the alignments the callee asks. *)

Lemma l7_mod : forall fr k d, fr mod 32 = 0 -> d = 2 \/ d = 8 -> k mod 8 = 0 -> (fr + k) mod d = 0.
Proof. intros fr k d H Hd Hk. destruct Hd as [-> | ->]; Z.div_mod_to_equations; lia. Qed.

(* A CB cell from its bytes and its writability. *)

Lemma l7_rw : forall m a bs n, bytes_at rsegs m a bs -> length bs = n -> wr_at rsegs m a (Z.of_nat n) ->
  rw_cells rsegs m a [CB n bs].
Proof.
  intros m a bs n Hb Hl Hw. split.
  - split.
    + cbn [cells_wf cell_wf]. split; [exact Hl | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* The n bytes at fr + k (in one granule of a 32-aligned frame) are addressable when their shadow byte b is 0 or
   at least n. *)

Lemma l7_addr_cell : forall m fr k n (b : byte), fr mod 32 = 0 -> 0 <= fr -> k mod 8 = 0 -> 0 <= k -> 0 <= n <= 8 ->
  (forall a, fr + k <= a < fr + k + n -> app_mem a) -> fr + k + n <= APPMEM_END ->
  bytes_at rsegs m (Sfr fr + k / 8) [b] ->
  (bv_signed b = 0 \/ n <= bv_signed b <= 7) ->
  addressable m (fr + k) n.
Proof.
  intros m fr k n b Hm H0 Hk Hk0 Hn Happ Hend (_ & _ & Hb) Hv.
  pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as E. cbn [nth_error] in E.
  change (Z.of_nat 0) with 0 in E. rewrite Z.add_0_r in E.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Happ; lia|]. exists b. split.
  - replace (shadow_addr (fr + k + i)) with (Sfr fr + k / 8); [exact E|].
    unfold Sfr, shadow_addr. clear - Hm Hk Hk0 H0 Hi Hn. Z.div_mod_to_equations. lia.
  - unfold shadow_ok. destruct Hv as [Hv|Hv]; [left; exact Hv | right].
    split; [|lia]. clear - Hm Hk Hk0 H0 Hi Hn Hv. Z.div_mod_to_equations. lia.
Qed.

Section S_l7.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The identity_reply contract's premises after the six stores, on the stored memory m1: the window and its
   bytes from FRA at m1 (fra_win, the window conjunct, fra_frame's placement), the record from b5_PH, the reply
   cells from the stores themselves, the side-stack bundle from f9_fp_call, the runtime cells from RT. *)
Lemma f9_pre_of : forall g j phi fr regs mem m1 md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs m1 md ->
  HB mem phi (flen g j) -> b5_PH g j phi fr regs mem -> b5_FS fr mem ->
  munch (f9_WA (Sfr fr) fr) mem m1 -> ro_agree rsegs m1 ->
  bytes_at rsegs m1 (Sfr fr + 32) (le1 (Z_to_bv 64 2)) ->
  bytes_at rsegs m1 (Sfr fr + 34) (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (Sfr fr + 38) (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (fr + 256) (le2 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (fr + 272) (le8 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (fr + 304) (le8 (Z_to_bv 64 0)) ->
  wr_at rsegs m1 (fr + 256) 2 -> wr_at rsegs m1 (fr + 272) 8 -> wr_at rsegs m1 (fr + 304) 8 ->
  exists FS, word_mem rsegs m1 (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\ AC.GT <= FS /\
    f9_PL fr regs m1 /\
    f9_pre phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (AC.aspZ regs) FS (AC.as_tp AC.ASYMS) m1
      (t_g (g_in g) j) (le2 (Z_to_bv 64 0)) (le8 (Z_to_bv 64 0)) (le8 (Z_to_bv 64 0)).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros g j phi fr regs mem m1 md HFRA0 HFRA1 HHB HPH HFS HMU HRO1 Bs32 Bs34 Bs38 Ba Bp Bn Wa Wp Wn.
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA0) as (Hgt & Happ).
  pose proof (fra_win B APIf ra g fr _ regs m1 md HFRA1) as (Hwlo1 & Hwstk1).
  pose proof HFRA1 as (A1 & sp1 & s51 & HRT1 & HAH1 & Hro1 & Hsn1 & Hhalt1 & Hgimg1 & Hr21 & Hspm1 & Haspz1 &
    Hstklo1 & Hr41 & Hr81 & Hr91 & Hr31 & Hr191 & Hr261 & Hfrm & Hs51 & HAm1 & HAS1 & Hspa1 & Hfa1 & HA4161 &
    HS41 & HAPP1 & Hspill1 & Hsel1 & Hfr241 & Hloc1 & Hhdr11 & Hhdr21 & Hsh1 & Hwin1 & Hsaved1 & Herrno1 &
    HAG1 & HWA1 & HTop11 & HTop21 & HTop31 & Hhb1 & Hlive1).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ m1 md HAH1) as Hhi1.
  pose proof (l7_flen0 g j) as HL0.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HK9 : REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  assert (Hfr0 : 0x5fe000 <= fr) by exact Hgt.
  assert (Hfrub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. destruct Ha as [Ha|Ha]; lia. }
  assert (HSfr : LOWMEM_END <= Sfr fr).
  { pose proof (shadow_of_app fr (Happ fr ltac:(lia))) as Hs. unfold Sfr.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hs |- *. lia. }
  assert (HspA : AC.aspZ regs <= APPMEM_END) by (rewrite Haspz1; lia).
  pose proof HHB as (Hphi0 & HHBa).
  pose proof HHBa as (Hpa0 & Hpa1 & Hpa2 & Hpa3).
  destruct HPH as (HPHb & HPHp & HPHfs).
  (* ---- the thread words at tp and tp + 8 are outside the stores ---- *)
  assert (Htp_out : forall x, AC.as_tp AC.ASYMS <= x < AC.as_tp AC.ASYMS + 16 -> outside (f9_WA (Sfr fr) fr) x).
  { intros x Hx. cbv [AC.as_tp AC.ASYMS] in Hx.
    cbv [f9_WA]. cbn [outside]. unfold LOWMEM_END in HSfr. repeat split; try exact I; lia. }
  assert (HFS1 : b5_FS fr m1).
  { destruct HFS as (P1 & (DB & HDB & HDB0 & HDB1)). split.
    - intros FS0 HW HF0 HF1. apply (P1 FS0); [|exact HF0 | exact HF1].
      refine (proj2 (l7_wm_keep _ mem m1 (AC.as_tp AC.ASYMS) FS0 HMU _ _ _) HW).
      + cbv [AC.as_tp AC.ASYMS]. lia.
      + cbv [AC.as_tp AC.ASYMS]. lia.
      + intros x Hx. apply Htp_out. lia.
    - exists DB. split; [|split; assumption].
      refine (proj1 (l7_wm_keep _ mem m1 (AC.as_tp AC.ASYMS + 8) DB HMU _ _ _) HDB).
      + cbv [AC.as_tp AC.ASYMS]. lia.
      + cbv [AC.as_tp AC.ASYMS]. lia.
      + intros x Hx. apply Htp_out. lia. }
  pose proof (f9_PL_of B APIf ra g fr _ regs mem md HFRA0 HFS) as HPL0.
  pose proof (f9_PL_of B APIf ra g fr _ regs m1 md HFRA1 HFS1) as HPL1.
  (* ---- the record (phi, len) apart from the frame cells and the callee's window ---- *)
  assert (HDJ : (phi + 50 <= fr + 256 \/ fr + 312 <= phi) /\
                (phi + 50 <= AC.aspZ regs - 9072 \/ AC.aspZ regs <= phi) /\ phi + 50 <= 2 ^ 64 /\ 0 < phi).
  { destruct (Z.eq_dec (flen g j) 0) as [E0|E0].
    - exact (l5_dj1 B APIf ra g fr phi (AC.a_size (flen g j)) [] regs mem md HFRA0 HPL0
               ltac:(unfold AC.a_size; lia) (HPHfs E0)).
    - exact (l5_dj B APIf ra g fr phi (AC.a_size (flen g j)) [] regs mem md HFRA0 HPL0
               ltac:(unfold AC.a_size; lia)). }
  destruct HDJ as (Hdj & Hdw & H64 & Hp0).
  (* ---- the callee's window [S - K, S) in the slot window, above HIGHMEM_BEG ---- *)
  assert (HHI : HIGHMEM_BEG <= AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) by lia.
  destruct HFS1 as (HFS1a & HFS1b).
  destruct (f9_fp_call B APIf ra g fr phi (flen g j) regs m1 md HFRA1 HPL1 HspA HFS1b)
    as (FS & HWFS & HFS64 & HFP & HTLS).
  pose proof (f9_fs_place _ _ _ _ _ LAWS _ m1 md FS HAH1 HWFS HFS64) as (HFSgt & _).
  pose proof HPL0 as (_ & _ & P3 & _ & _).
  exists FS. split; [exact HWFS|]. split; [exact HFS64|]. split; [exact HFSgt|]. split; [exact HPL1|].
  unfold f9_pre.
  (* 0 <= phi, len, pa, pp, pn < 2^64 *)
  split. { unfold AC.a_size, APPMEM_END in Hpa2. lia. }
  split. { unfold AC.a_size, APPMEM_END in Hpa2. lia. }
  split. { unfold APPMEM_END in Hfrub. lia. }
  split. { unfold APPMEM_END in Hfrub. lia. }
  split. { unfold APPMEM_END in Hfrub. lia. }
  (* S < 2^64, S mod 16 = 0, K <= S *)
  split. { unfold APPMEM_END in HspA. lia. }
  split. { rewrite Haspz1. exact Hspm1. }
  split. { unfold HIGHMEM_BEG in HHI. lia. }
  (* stk m1 (S - K) S *)
  split.
  { destruct (stk_split rsegs m1 (AC.aspZ regs - FN_STACK) (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K)
                (AC.aspZ regs) Hwstk1 ltac:(lia)) as (_ & Hs). exact Hs. }
  split. { exact HRO1. }
  split. { unfold t_g. apply fr50_length. }
  (* the record clause *)
  split.
  { intros _ H50L.
    split; [exact H64|]. split.
    - apply (fl_bytes _ mem m1 phi _ (HPHb H50L) HMU).
      intros x Hx. unfold t_g in Hx. rewrite fr50_length in Hx. change (Z.of_nat 50) with 50 in Hx.
      apply l7_app_out; [lia | exact Happ | | lia].
      destruct (Hpa3 (x - phi) ltac:(unfold AC.a_size; lia)) as (Hx' & _).
      replace (phi + (x - phi)) with x in Hx' by lia. exact Hx'.
    - rewrite HK9. exact Hdw. }
  (* the reply_args clause *)
  split.
  { intros _.
    split; [apply l7_mod; [exact Hfrm | left; reflexivity | reflexivity]|].
    split; [apply l7_mod; [exact Hfrm | right; reflexivity | reflexivity]|].
    split; [apply l7_mod; [exact Hfrm | right; reflexivity | reflexivity]|].
    split; [apply l7_rw; [exact Ba | apply length_le2 | exact Wa]|].
    split; [apply l7_rw; [exact Bp | apply length_le8 | exact Wp]|].
    split; [apply l7_rw; [exact Bn | apply length_le8 | exact Wn]|].
    rewrite HK9. repeat split; lia. }
  (* asan_cells, shadow_rw *)
  split. { exact (RT_cells _ _ _ HRT1). }
  split. { exact (RT_shadow_rw _ _ _ HRT1). }
  split. { exact HHI. }
  split. { exact HspA. }
  (* addressable m1 (S - K) K: FRA's window conjunct at m1, the frame apart *)
  split.
  { rewrite HK9.
    split; [unfold HIGHMEM_BEG in HHI; lia|]. split; [lia|]. split; [lia|].
    intros i Hi.
    pose proof (HWA1 (AC.aspZ regs - 9072 + i) ltac:(lia) ltac:(lia)) as Had.
    destruct Had as (_ & _ & _ & Hb). pose proof (Hb 0 ltac:(lia)) as Hb0. rewrite Z.add_0_r in Hb0. exact Hb0. }
  (* addressable m1 phi 50 *)
  split.
  { intros _ H50L.
    apply (l5_addr_keep mem m1 (f9_WA (Sfr fr) fr) phi 50); [| exact HMU |].
    - split; [lia|]. split; [lia|]. split; [unfold AC.a_size in Hpa2; lia|].
      intros i Hi. apply Hpa3. unfold AC.a_size; lia.
    - intros i Hi. destruct (Hpa3 i ltac:(unfold AC.a_size; lia)) as (Happi & _).
      apply l7_sh_out; [lia | exact Hfrm | exact Happ | exact Happi | lia]. }
  (* the three frame cells addressable, apart from the runtime *)
  split.
  { intros _.
    split.
    { apply (l7_addr_cell m1 fr 256 2 (Z_to_bv 8 2));
        [exact Hfrm | lia | reflexivity | lia | lia | intros a Ha; apply Happ; lia | lia | exact Bs32 |].
      right. change (bv_signed (Z_to_bv 8 2)) with 2. lia. }
    split.
    { apply (l7_addr_cell m1 fr 272 8 (Z_to_bv 8 0));
        [exact Hfrm | lia | reflexivity | lia | lia | intros a Ha; apply Happ; lia | lia | exact Bs34 |].
      left. reflexivity. }
    split.
    { apply (l7_addr_cell m1 fr 304 8 (Z_to_bv 8 0));
        [exact Hfrm | lia | reflexivity | lia | lia | intros a Ha; apply Happ; lia | lia | exact Bs38 |].
      left. reflexivity. }
    unfold RT_LO, RT_HI.
    split; [right; lia|]. split; [right; lia|]. right; lia. }
  (* addressable m1 BC 6: the registered global (REAC_CTRL_PARSE_BC, 7), .str.4 *)
  split.
  { unfold REAC_CTRL_PARSE_BC.
    split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
    intros i Hi.
    assert (Hg : addressable m1 (REAC_CTRL_PARSE_BC + i) 1).
    { apply HAG1. exists REAC_CTRL_PARSE_BC, 7. split; [|lia].
      unfold AF.frame_AG, REAC_CTRL_PARSE_BC. cbn [In]. repeat (first [left; reflexivity | right]). }
    destruct Hg as (_ & _ & _ & Hg). pose proof (Hg 0 ltac:(lia)) as Hg0. rewrite Z.add_0_r in Hg0. exact Hg0. }
  (* the image cells *)
  split. { apply real_cell_of; [exact (RT_real_cells _ _ _ HRT1) | vm_compute; reflexivity]. }
  split. { apply real_cell_of; [exact (RT_real_cells _ _ _ HRT1) | vm_compute; reflexivity]. }
  pose proof (RT_cf_cells _ _ _ HRT1) as (CF1 & _ & _ & _ & _ & _ & CF7 & _).
  split. { exact CF1. }
  split. { exact (l7_byte_of m1 (RT_CF + 240) _ 14 (Z_to_bv 8 1) CF7 eq_refl). }
  split. { exact (l7_byte_of m1 (RT_CF + 240) _ 15 (Z_to_bv 8 1) CF7 eq_refl). }
  (* fp and the tls clause *)
  split; [exact HFP | exact HTLS].
Qed.

End S_l7.


Definition f9_WC (phi len fr S FS : Z) (G : list byte) : list ivl :=
  reac_ctrl_identity_reply_fp phi len (fr + 256) (fr + 272) (fr + 304) S G ++ fp_w [1%nat] FS ++
  [(shadow_addr (S - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr S)].

Lemma l8_out_WA : forall fr x, ~ (fr + 256 <= x < fr + 312) ->
  x <> Sfr fr + 32 -> x <> Sfr fr + 34 -> x <> Sfr fr + 38 -> outside (f9_WA (Sfr fr) fr) x.
Proof.
  intros fr x H1 H2 H3 H4. unfold f9_WA. cbn [outside]. repeat split; lia.
Qed.

Lemma l8_out_WC : forall phi len fr S FS G x,
  ~ (fr + 256 <= x < fr + 312) -> ~ (S - 9072 <= x < S) -> ~ (FS + 8 <= x < FS + 2134016) ->
  ~ (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) ->
  ~ (shadow_addr (S - 9072) <= x < shadow_addr S) ->
  outside (f9_WC phi len fr S FS G) x.
Proof.
  intros phi len fr S FS G x H1 H2 H3 H4 H5. unfold f9_WC, reac_ctrl_identity_reply_fp. rewrite l1_fpw1.
  unfold REAC_CTRL_IDENTITY_REPLY_K.
  destruct (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G); cbn [app outside]; repeat split; lia.
Qed.

(* A word read survives a write list that misses its 8 bytes, in both directions. *)

Lemma l8_wm : forall W m m' a v, munch W m m' -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall x, a <= x < a + 8 -> outside W x) ->
  (word_mem rsegs m a v <-> word_mem rsegs m' a v).
Proof.
  intros W m m' a v MU H0 H1 HW.
  assert (E : forall k, (k < 8)%nat -> mbyte rsegs m' (a + Z.of_nat k) = mbyte rsegs m (a + Z.of_nat k)).
  { intros k Hk. unfold mbyte. rewrite (MU (Z_to_bv 64 (a + Z.of_nat k))); [reflexivity|].
    rewrite MState.unsigned_lit by lia. apply HW. lia. }
  split; intros H k Hk; [rewrite (E k Hk) | rewrite <- (E k Hk)]; apply H; exact Hk.
Qed.

(* Bytes carried across two write lists that both miss them. *)

Lemma l8_tr : forall W1 W2 m m1 m2 a bs, bytes_at rsegs m a bs -> munch W1 m m1 -> munch W2 m1 m2 ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> outside W1 x /\ outside W2 x) -> bytes_at rsegs m2 a bs.
Proof.
  intros W1 W2 m m1 m2 a bs H M1 M2 HW.
  eapply fl_bytes;
    [eapply fl_bytes; [exact H | exact M1 | intros x Hx; exact (proj1 (HW x Hx))]
    | exact M2 | intros x Hx; exact (proj2 (HW x Hx))].
Qed.

Lemma l8_q64 : forall W1 W2 m m1 m2 a v, q64 m a v -> munch W1 m m1 -> munch W2 m1 m2 ->
  (forall x, a <= x < a + 8 -> outside W1 x /\ outside W2 x) -> q64 m2 a v.
Proof.
  intros W1 W2 m m1 m2 a v H M1 M2 HW. unfold q64 in *. apply (l8_tr W1 W2 m m1 m2 a _ H M1 M2).
  intros x Hx. apply HW. rewrite length_le8 in Hx. change (Z.of_nat 8) with 8 in Hx. lia.
Qed.

Lemma l8_sh_hi : forall a, 0 <= a < APPMEM_END -> shadow_addr a < HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG. unfold APPMEM_END in Ha.
  assert (D : a / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* The shadow byte k of the frame base is the shadow of the frame granule [fr + 8k, fr + 8k + 8) only. *)

Lemma l8_sh_ne : forall a fr k, fr mod 32 = 0 -> ~ (fr + 8 * k <= a < fr + 8 * k + 8) ->
  shadow_addr a <> Sfr fr + k.
Proof.
  intros a fr k Hf Hn E. apply Hn. unfold Sfr, shadow_addr in E. Z.div_mod_to_equations. lia.
Qed.

(* The thread word at tp (below GT and below the shadow) is outside both write lists. *)

Lemma l8_Otp : forall fr sp FS phi len G x,
  AC.GT <= fr -> AC.GT <= FS -> HIGHMEM_BEG + 9072 <= sp -> LOWMEM_END <= Sfr fr ->
  LOWMEM_END <= shadow_addr (FS + 1085440) -> LOWMEM_END <= shadow_addr (sp - 9072) ->
  AC.as_tp AC.ASYMS <= x < AC.as_tp AC.ASYMS + 8 ->
  outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi len fr sp FS G) x.
Proof.
  intros fr sp FS phi len G x H1 H2 H3 H4 H5 H6 Hx. cbv [AC.as_tp AC.ASYMS] in Hx.
  unfold AC.GT, HIGHMEM_BEG, LOWMEM_END in *.
  split; [apply l8_out_WA | apply l8_out_WC]; lia.
Qed.

(* The spill block [A, ...) (A >= sp >= stklo >= HIGHMEM_BEG, A >= fr + FRAME_BYTES) is outside both write lists. *)

Lemma l8_OA : forall fr sp FS lo A phi len G x,
  HIGHMEM_BEG <= lo -> lo <= sp -> FS + AC.FS_SIZE <= lo -> sp <= A -> fr + FRAME_BYTES <= A -> A <= x ->
  Sfr fr + 39 <= HIGHMEM_BEG -> shadow_addr (FS + 2134016) <= HIGHMEM_BEG -> shadow_addr sp <= HIGHMEM_BEG ->
  outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi len fr sp FS G) x.
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros fr sp FS lo A phi len G x H1 H2 H3 H4 H5 H6 H7 H8 H9. unfold AC.FS_SIZE in *.
  split; [apply l8_out_WA | apply l8_out_WC]; lia.
Qed.

(* A frame byte off the three cells is outside both write lists. *)

Lemma l8_OF : forall fr sp FS phi len G x,
  fr <= x < fr + FRAME_BYTES -> ~ (fr + 256 <= x < fr + 312) ->
  (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) ->
  (fr + FRAME_BYTES + 8 <= sp - 9072 \/ sp <= fr) -> FS + 2134016 <= fr ->
  LOWMEM_END <= Sfr fr -> Sfr fr + 39 <= HIGHMEM_BEG ->
  LOWMEM_END <= shadow_addr (FS + 1085440) -> shadow_addr (FS + 2134016) <= HIGHMEM_BEG ->
  LOWMEM_END <= shadow_addr (sp - 9072) -> shadow_addr sp <= HIGHMEM_BEG ->
  outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi len fr sp FS G) x.
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros fr sp FS phi len G x H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
  split; [apply l8_out_WA | apply l8_out_WC]; lia.
Qed.

(* A heap-block byte (app memory, at most stklo, off the side stack, off the frame cells) is outside both lists. *)

Lemma l8_OB : forall fr sp FS lo phi len G x,
  app_mem x -> x <= lo -> ~ (FS <= x < FS + AC.FS_SIZE) -> ~ (fr + 256 <= x < fr + 312) ->
  lo + 16 <= sp - 9072 ->
  LOWMEM_END <= Sfr fr -> Sfr fr + 39 <= HIGHMEM_BEG ->
  LOWMEM_END <= shadow_addr (FS + 1085440) -> shadow_addr (FS + 2134016) <= HIGHMEM_BEG ->
  LOWMEM_END <= shadow_addr (sp - 9072) -> shadow_addr sp <= HIGHMEM_BEG ->
  outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi len fr sp FS G) x.
Proof.
  intros fr sp FS lo phi len G x H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
  unfold app_mem, AC.FS_SIZE in *.
  split; [apply l8_out_WA | apply l8_out_WC]; lia.
Qed.

(* The shadow byte of such a heap-block byte is outside both lists. *)

Lemma l8_OS : forall fr sp FS lo phi len G a,
  0 <= a < APPMEM_END -> a <= lo -> ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (fr + 256 <= a < fr + 312) ->
  fr mod 32 = 0 -> lo + 16 <= sp - 9072 -> 0 <= FS ->
  (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) ->
  (FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS) ->
  HIGHMEM_BEG <= sp - 9072 ->
  outside (f9_WA (Sfr fr) fr) (shadow_addr a) /\ outside (f9_WC phi len fr sp FS G) (shadow_addr a).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros fr sp FS lo phi len G a Ha Hlo Hfs Hc Hfrm Hsp HFS0 Hfr HFSr Hw.
  pose proof (l1_sh_lo a ltac:(lia)) as Y1. pose proof (l8_sh_hi a Ha) as Y2.
  unfold AC.FS_SIZE in *.
  split.
  - apply l8_out_WA.
    + lia.
    + apply l8_sh_ne; [exact Hfrm | lia].
    + apply l8_sh_ne; [exact Hfrm | lia].
    + apply l8_sh_ne; [exact Hfrm | lia].
  - apply l8_out_WC.
    + lia.
    + lia.
    + lia.
    + destruct (Z_lt_le_dec a FS) as [Hl|Hg].
      * pose proof (l5_sh_lt a (FS + 1085440) ltac:(lia) ltac:(lia)). lia.
      * pose proof (l5_sh_mono (FS + 2134016) a ltac:(lia)). lia.
    + pose proof (l5_sh_lt a (sp - 9072) ltac:(lia) ltac:(lia)). lia.
Qed.


(* The shadow byte of a frame byte off the three cells' granules is outside the stores. *)
Lemma l8_SWA : forall fr x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 256 <= x < fr + 312) -> fr mod 32 = 0 -> 0 <= fr ->
  (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) -> fr + FRAME_BYTES <= APPMEM_END ->
  outside (f9_WA (Sfr fr) fr) (shadow_addr x).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros fr x Hx Hc Hm H0 Hreg Htop.
  pose proof (l1_sh_lo x ltac:(lia)) as Y1. pose proof (l8_sh_hi x ltac:(lia)) as Y2.
  apply l8_out_WA.
  - lia.
  - apply l8_sh_ne; [exact Hm | lia].
  - apply l8_sh_ne; [exact Hm | lia].
  - apply l8_sh_ne; [exact Hm | lia].
Qed.

(* The shadow byte of any frame byte is outside the call's list: it is below HIGHMEM_BEG, above the shadow of the
   class-1 frames (the frame is above them) and apart from the shadow of the callee's window (the frame is a
   granule below the window, or at or above sp). *)
Lemma l8_SWC : forall fr sp FS phi len G x, fr <= x < fr + FRAME_BYTES -> 0 <= FS ->
  (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) -> fr + FRAME_BYTES <= APPMEM_END ->
  (fr + FRAME_BYTES + 8 <= sp - 9072 \/ sp <= fr) -> FS + 2134016 <= fr -> HIGHMEM_BEG <= sp - 9072 ->
  (FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS) ->
  outside (f9_WC phi len fr sp FS G) (shadow_addr x).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros fr sp FS phi len G x Hx HFS0 Hreg Htop Hw HFSfr Hsp HFSr.
  assert (KH : HIGHMEM_BEG = 17594333495296) by reflexivity.
  pose proof (l1_sh_lo x ltac:(lia)) as Y1. pose proof (l8_sh_hi x ltac:(lia)) as Y2.
  unfold AC.FS_SIZE in HFSr.
  apply l8_out_WC.
  - lia.
  - lia.
  - lia.
  - pose proof (l5_sh_mono (FS + 2134016) x ltac:(lia)). lia.
  - destruct Hw as [Hw|Hw].
    + pose proof (l5_sh_lt x (sp - 9072) ltac:(lia) ltac:(lia)). lia.
    + pose proof (l5_sh_mono sp x ltac:(lia)). lia.
Qed.

(* An image byte (below GT) and its shadow byte are outside both write lists. *)
Lemma l8_Olo : forall fr sp FS phi len G x, 0 <= x < AC.GT -> AC.GT <= fr -> AC.GT <= FS ->
  (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) -> fr + FRAME_BYTES <= APPMEM_END ->
  HIGHMEM_BEG <= sp - 9072 -> sp <= APPMEM_END -> (FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS) ->
  (outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi len fr sp FS G) x) /\
  (outside (f9_WA (Sfr fr) fr) (shadow_addr x) /\ outside (f9_WC phi len fr sp FS G) (shadow_addr x)).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros fr sp FS phi len G x Hx Hfr HFS Hreg Htop Hsp Hsp2 HFSr.
  unfold AC.GT, AC.FS_SIZE in *.
  split; split.
  - apply l8_out_WA; unfold Sfr, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply l8_out_WC; unfold Sfr, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply l8_out_WA; unfold Sfr, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply l8_out_WC; unfold Sfr, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia.
Qed.

(* addressable across both write lists, when they miss its shadow bytes. *)
Lemma l8_addr2 : forall W1 W2 m m1 m2 p n, addressable m p n -> munch W1 m m1 -> munch W2 m1 m2 ->
  (forall i, 0 <= i < n -> outside W1 (shadow_addr (p + i)) /\ outside W2 (shadow_addr (p + i))) ->
  addressable m2 p n.
Proof.
  intros W1 W2 m m1 m2 p n H M1 M2 HO.
  assert (H1 : addressable m1 p n).
  { apply (l5_addr_keep m m1 W1 p n H M1). intros i Hi. exact (proj1 (HO i Hi)). }
  apply (l5_addr_keep m1 m2 W2 p n H1 M2). intros i Hi. exact (proj2 (HO i Hi)).
Qed.

(* The kind-name table holds 112 bytes. *)
Lemma f9_kn_len : length kind_name_bytes = 112%nat.
Proof.
  unfold kind_name_bytes, kind_name_addrs. cbn [map concat].
  rewrite !length_app, !length_le8. reflexivity.
Qed.

(* A carried spill (exists-A form) across both write lists: its base is the cut's own A (reg 9 pins it modulo 2^64,
   the q64 bounds put it back in range). *)
Lemma f9_spill_tr : forall regs regs' m m1 m2 W1 W2 A off v,
  rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 -> 0 <= off <= 408 ->
  munch W1 m m1 -> munch W2 m1 m2 ->
  (forall x, A <= x < A + 416 -> outside W1 x /\ outside W2 x) ->
  spill regs m off v -> spill regs' m2 off v.
Proof.
  intros regs regs' m m1 m2 W1 W2 A off v H9 HA HA416 E9 Hoff M1 M2 HO (A' & HA' & Hqv).
  pose proof Hqv as Hb. unfold q64 in Hb. destruct Hb as (Hb0 & Hb1 & _).
  rewrite length_le8 in Hb1. change (Z.of_nat 8) with 8 in Hb1.
  pose proof (rg_eq64 regs 9 A' A HA' H9) as Hm.
  rewrite (Z.mod_small A) in Hm by lia.
  assert (HA'0 : 0 <= A').
  { destruct (Z_le_gt_dec 0 A') as [Hp|Hneg]; [exact Hp|exfalso].
    assert (HmA : A' mod 2 ^ 64 = A' + 2 ^ 64)
      by (rewrite <- (Z.mod_add A' 1 (2 ^ 64)) by lia; rewrite Z.mod_small; lia).
    rewrite HmA in Hm. lia. }
  rewrite (Z.mod_small A') in Hm by lia. subst A'.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|].
  apply (l8_q64 W1 W2 m m1 m2 _ _ Hqv M1 M2). intros x Hx. apply HO. lia.
Qed.

Section S_l8.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The exit body at 0x81ff4: the carry of the span (FLSI with f1_IN and FLC, LK, b5_C, b5_K, IDj, b5_F17, b5_W240,
   b5_PF) and HB move from the entry memory across the six stores (f9_WA) and the call (f9_WC): every cell they
   name is outside both lists (the save area [A, A + 416), the frame off its three reply cells and the shadow of its
   bytes, the record block and its shadow, the harness input block and its shadow, the image below GT and its
   shadow). b5_RC is the three cells' addressability, from the stores' shadow bytes; rg 10 and b5_RPost are the
   contract's post. *)
Lemma f9_exit_of : forall g j phi fr regs regs2 mem m1 m2 md md2 A FS,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs2 m2 md2 ->
  HB mem phi (flen g j) -> FLSI g j fr regs mem -> LK g fr j regs mem ->
  b5_C g j phi fr regs mem -> b5_K g j phi fr regs mem -> IDj g fr j mem ->
  b5_F17 g j phi fr regs mem -> b5_W240 g j regs mem -> b5_PF g j phi fr regs mem ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  munch (f9_WA (Sfr fr) fr) mem m1 ->
  munch (f9_WC phi (flen g j) fr (AC.aspZ regs) FS (t_g (g_in g) j)) m1 m2 ->
  wmono rsegs mem m1 -> wmono rsegs m1 m2 ->
  word_mem rsegs m1 (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> AC.GT <= FS ->
  bytes_at rsegs m1 (Sfr fr + 32) (le1 (Z_to_bv 64 2)) ->
  bytes_at rsegs m1 (Sfr fr + 34) (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (Sfr fr + 38) (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (fr + 256) (le2 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (fr + 272) (le8 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (fr + 304) (le8 (Z_to_bv 64 0)) ->
  getr regs2 2 = getr regs 2 -> getr regs2 9 = getr regs 9 -> getr regs2 18 = getr regs 18 ->
  getr regs2 20 = getr regs 20 -> getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 ->
  getr regs2 23 = getr regs 23 -> getr regs2 24 = getr regs 24 -> getr regs2 25 = getr regs 25 ->
  getr regs2 10 = Z_to_bv 64 (reply_ret phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j)) ->
  (reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = true ->
     b5_RPost phi fr (t_g (g_in g) j) m2) ->
  HB m2 phi (flen g j) /\ FLSI g j fr regs2 m2 /\ LK g fr j regs2 m2 /\ b5_C g j phi fr regs2 m2 /\
  (b5_K g j phi fr regs2 m2 /\ b5_RC fr m2 /\
   rg regs2 10 (reply_ret phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j)) /\
   (reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = true ->
      b5_RPost phi fr (t_g (g_in g) j) m2) /\
   IDj g fr j m2 /\ b5_F17 g j phi fr regs2 m2 /\ b5_W240 g j regs2 m2 /\ b5_PF g j phi fr regs2 m2).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros g j phi fr regs regs2 mem m1 m2 md md2 A FS HFRA0 HFRA HHB HFLSI HLK HbC HbK HIDj HF17 HW240 HPF
    HA9 HAb MU1 MU2 WM1 WM2 HWM HFS HGTFS Bs32 Bs34 Bs38 Ba Bp Bn
    E2 E9 E18 E20 E21 E22 E23 E24 E25 E10 HRP.
  assert (KSL : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (KFS : AC.FS_SIZE = 11571200) by reflexivity.
  assert (KGT : AC.GT = 0x5fe000) by reflexivity.
  assert (KLO : LOWMEM_END = 0x7fff8000) by reflexivity.
  assert (KHI : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (KAP : APPMEM_END = 0x800000000000) by reflexivity.
  pose proof (eq_refl : AC.as_tp AC.ASYMS = ltac:(let v := eval cbv in (AC.as_tp AC.ASYMS) in exact v)) as Ktp.
  assert (KFN : FN_STACK = 1044480) by reflexivity.
  pose proof HbC as (H23 & H18 & (A0 & HrA0 & HA0 & HSP & H232) & HPH & HFR & HFSb & HKN & HFGj & HFSj).
  pose proof HbK as (HG20 & HG22 & HG24 & HG25 & H280 & H176 & Hrargs).
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA0) as (HGTfr & Happ).
  pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA0) as (Hapart & HfrA9 & _ & _).
  pose proof (fra_win B APIf ra g fr _ regs2 m2 md2 HFRA) as (Hwlo2 & _).
  pose proof HFRA as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWAf &
    HTop1 & HTop2 & HTop3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (l7_flen0 g j) as Hlen0.
  destruct HHB as (Hphi0 & HAd).
  (* sp and the spill base *)
  assert (HS : AC.aspZ regs = sp) by (rewrite <- Haspz; unfold AC.aspZ; rewrite E2; reflexivity).
  pose proof Hwin as (Hwb0 & Hwb1 & _).
  assert (HA'b : 0 <= A' < 2 ^ 64) by lia.
  assert (EA : A' = A).
  { pose proof Hr9 as Hr9'. pose proof HA9 as HA9'. unfold rg in Hr9', HA9'. rewrite E9, HA9' in Hr9'.
    apply (f_equal (bv_unsigned (n:=64))) in Hr9'. rewrite !MState.unsigned_lit in Hr9' by lia. lia. }
  subst A'.
  assert (EA0 : A0 = A) by exact (l9_rg_eq regs 9 A0 A HrA0 HA9 HA0 HAb).
  subst A0.
  assert (HA0fr : fr + FRAME_BYTES <= A).
  { unfold rg in HA9. rewrite HA9, MState.unsigned_lit in HfrA9 by lia. exact HfrA9. }
  rewrite HS in MU2, Hapart.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhigh.
  pose proof (Hapart 9080 ltac:(lia)) as HPLc.
  assert (Hlo2 : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) m2 md2 <= sp - FN_STACK) by lia.
  assert (Hsp : HIGHMEM_BEG + 1044480 <= sp) by lia.
  (* frame bounds *)
  assert (HSfr1 : LOWMEM_END <= Sfr fr) by (unfold Sfr; apply l1_sh_lo; lia).
  assert (Hfrapp : fr + FRAME_BYTES <= APPMEM_END /\ (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr)).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem in H1, H2. lia. }
  destruct Hfrapp as (Hfrtop & Hfr_reg).
  assert (HSfr2 : Sfr fr + 39 <= HIGHMEM_BEG).
  { replace (Sfr fr + 39) with (shadow_addr (fr + 39 * 8))
      by (unfold Sfr, shadow_addr; rewrite Z.div_add by lia; lia).
    apply l1_sh_hi. lia. }
  assert (HshW1 : LOWMEM_END <= shadow_addr (sp - 9072)) by (apply l1_sh_lo; lia).
  assert (HshF1 : LOWMEM_END <= shadow_addr (FS + 1085440)) by (apply l1_sh_lo; lia).
  (* the tp word names FS in mem, m1 and m2 *)
  assert (Otp : forall x, AC.as_tp AC.ASYMS <= x < AC.as_tp AC.ASYMS + 8 ->
      outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) x)
    by (intros x Hx; exact (l8_Otp fr sp FS phi (flen g j) (t_g (g_in g) j) x HGTfr HGTFS ltac:(lia)
                             HSfr1 HshF1 HshW1 Hx)).
  assert (HWMmem : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
  { apply (proj2 (l8_wm (f9_WA (Sfr fr) fr) mem m1 (AC.as_tp AC.ASYMS) FS MU1 ltac:(lia) ltac:(lia)
      (fun x Hx => proj1 (Otp x Hx)))). exact HWM. }
  assert (HWM2 : word_mem rsegs m2 (AC.as_tp AC.ASYMS) FS).
  { apply (proj1 (l8_wm _ m1 m2 (AC.as_tp AC.ASYMS) FS MU2 ltac:(lia) ltac:(lia)
      (fun x Hx => proj2 (Otp x Hx)))). exact HWM. }
  destruct (f9_fs_place _ _ _ _ _ LAWS _ _ _ FS HAH HWM2 HFS) as (_ & HFSlo & HFS4096 & HFSapp).
  assert (HFS_reg : FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { pose proof (HFSapp FS ltac:(lia)) as H1. pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as H2.
    unfold app_mem in H1, H2. lia. }
  assert (HshF2 : shadow_addr (FS + 2134016) <= HIGHMEM_BEG) by (apply l1_sh_hi; lia).
  assert (HshW2 : shadow_addr sp <= HIGHMEM_BEG) by (apply l1_sh_hi; lia).
  (* the frame: above stklo (real arm) or in FS above its class-6 frames (side arm) *)
  assert (HFRM : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) m2 md2 <= fr \/
                 (FS + 6328320 <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE)).
  { destruct Hloc as [[_ [_ Hreal]] | [_ [HfsbS [Hside _]]]].
    - left. destruct (Hreal fr ltac:(lia)) as (H & _). exact H.
    - right. pose proof (HfsbS FS HWM2 HFS) as Hb6. split; [exact Hb6|].
      destruct (Hside (fr + FRAME_BYTES - 1) ltac:(lia)) as (b & Hbr & Hwb & Hb1 & Hb2).
      pose proof (l2_wm_eq _ _ _ _ Hwb HWM2) as Heq. rewrite !Z.mod_small in Heq by lia. subst b. lia. }
  assert (HfrFS : FS + 2134016 <= fr) by (destruct HFRM as [H|H]; lia).
  (* the heap block (phi, a_size len): app memory, at most stklo, off FS *)
  assert (HBLK : forall a, phi <= a < phi + AC.a_size (flen g j) ->
      app_mem a /\ a <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) m2 md2 /\ ~ (FS <= a < FS + AC.FS_SIZE)).
  { intros a Ha.
    destruct (f9_blocks _ _ _ _ _ LAWS _ _ _ phi (AC.a_size (flen g j)) HAH
      ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hpst & Hbyte).
    destruct (Hbyte a ltac:(lia)) as (Hap & Hnf). split; [exact Hap|]. split; [lia|].
    intro Hin. apply Hnf. exists FS. split; [exact HFS | split; [exact HWM2 | exact Hin]]. }
  assert (HBc : forall a, phi <= a < phi + AC.a_size (flen g j) -> ~ (fr + 256 <= a < fr + 312)).
  { intros a Ha. destruct (HBLK a Ha) as (_ & Hle & Hnf). destruct HFRM as [H|H]; lia. }
  (* the outside facts *)
  assert (HOA : forall x, A <= x < A + 416 ->
      outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) x).
  { intros x Hx.
    exact (l8_OA fr sp FS (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) m2 md2) A phi (flen g j) (t_g (g_in g) j) x
      Hhigh ltac:(lia) HFSlo Hspa HA0fr ltac:(lia) HSfr2 HshF2 HshW2). }
  assert (HOS : forall i, 0 <= i < AC.a_size (flen g j) ->
      outside (f9_WA (Sfr fr) fr) (shadow_addr (phi + i)) /\
      outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) (shadow_addr (phi + i))).
  { intros i Hi. destruct (HBLK (phi + i) ltac:(lia)) as (Hxa & Hxl & Hxf).
    assert (Hxr : 0 <= phi + i < APPMEM_END) by (unfold app_mem in Hxa; lia).
    exact (l8_OS fr sp FS _ phi (flen g j) (t_g (g_in g) j) (phi + i) Hxr Hxl Hxf (HBc (phi + i) ltac:(lia))
      Hfrm ltac:(lia) ltac:(lia) Hfr_reg HFS_reg ltac:(lia)). }
  assert (HOB : forall x, phi <= x < phi + AC.a_size (flen g j) ->
      outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) x).
  { intros x Hx. destruct (HBLK x Hx) as (Hxa & Hxl & Hxf).
    exact (l8_OB fr sp FS _ phi (flen g j) (t_g (g_in g) j) x Hxa Hxl Hxf (HBc x Hx) ltac:(lia)
      HSfr1 HSfr2 HshF1 HshF2 HshW1 HshW2). }
  assert (HOF : forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 256 <= x < fr + 312) ->
      outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) x).
  { intros x Hx Hc.
    exact (l8_OF fr sp FS phi (flen g j) (t_g (g_in g) j) x Hx Hc Hfr_reg ltac:(lia) HfrFS
      HSfr1 HSfr2 HshF1 HshF2 HshW1 HshW2). }
  assert (HOFS : forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 256 <= x < fr + 312) ->
      outside (f9_WA (Sfr fr) fr) (shadow_addr x) /\
      outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) (shadow_addr x)).
  { intros x Hx Hc. split.
    - exact (l8_SWA fr x Hx Hc Hfrm ltac:(lia) Hfr_reg Hfrtop).
    - exact (l8_SWC fr sp FS phi (flen g j) (t_g (g_in g) j) x Hx ltac:(lia) Hfr_reg Hfrtop ltac:(lia) HfrFS
        ltac:(lia) HFS_reg). }
  assert (HOlo : forall x, 0 <= x < AC.GT ->
      (outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) x) /\
      (outside (f9_WA (Sfr fr) fr) (shadow_addr x) /\
       outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) (shadow_addr x))).
  { intros x Hx. exact (l8_Olo fr sp FS phi (flen g j) (t_g (g_in g) j) x Hx HGTfr HGTFS Hfr_reg Hfrtop
      ltac:(lia) ltac:(lia) HFS_reg). }
  (* the harness input block (f1_IN): an entry block, below stklo and off FS *)
  destruct HFLSI as (((Hp40 & Hp120 & Hp136 & Hp160 & Hp168 & Hp176 & Hp208 & Hp248 & HfAd & HpIN & HpIN2 &
      Hp184 & Hp256 & Hp264 & Hp272 & Hp32) & Hf128 & HfStk & Hf144 & HfAd17) & Hf216 & Hf224 & Hf248 &
    (HIN1 & HIN2 & HIN3) &
    (Hc256 & Hc184 & Hc192 & Hc80 & Hc88 & Hc96 & Hc272 & Hc264 & HcAfg & HcAid & Hc72 & Hc64 & Hc56 & Hc48)).
  assert (HINO : forall x, g_p g <= x < g_p g + g_n g ->
      (outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) x) /\
      (outside (f9_WA (Sfr fr) fr) (shadow_addr x) /\
       outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) (shadow_addr x))).
  { intros x Hx. assert (Hn : 0 < g_n g) by lia.
    destruct (f9_blocks _ _ _ _ _ LAWS _ _ _ (g_p g) (g_n g) HAH
      ltac:(apply in_or_app; right; exact (HIN1 Hn))) as (_ & Hpst & Hbyte).
    destruct (Hbyte x ltac:(lia)) as (Hxa & Hnf).
    assert (Hxf : ~ (FS <= x < FS + AC.FS_SIZE)).
    { intro Hin. apply Hnf. exists FS. split; [exact HFS | split; [exact HWM2 | exact Hin]]. }
    assert (Hxc : ~ (fr + 256 <= x < fr + 312)) by (destruct HFRM as [H|H]; lia).
    split.
    - exact (l8_OB fr sp FS (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) m2 md2) phi (flen g j) (t_g (g_in g) j) x
        Hxa ltac:(lia) Hxf Hxc ltac:(lia)
        HSfr1 HSfr2 HshF1 HshF2 HshW1 HshW2).
    - assert (Hxr : 0 <= x < APPMEM_END) by (unfold app_mem in Hxa; lia).
      exact (l8_OS fr sp FS (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) m2 md2) phi (flen g j) (t_g (g_in g) j) x
        Hxr ltac:(lia) Hxf Hxc Hfrm ltac:(lia) ltac:(lia)
        Hfr_reg HFS_reg ltac:(lia)). }
  (* the frame body: readable and writable after both lists (the reply cells are present: stored, then kept
     or rewritten by the callee) *)
  assert (HStk2 : stk rsegs m2 fr (fr + FRAME_BYTES)).
  { assert (HStk1 : stk rsegs m1 fr (fr + FRAME_BYTES)).
    { apply (fl_stk _ mem m1 fr (fr + FRAME_BYTES) HfStk MU1 WM1). intros x Hx.
      destruct (Z_lt_le_dec x (fr + 256)) as [C1|C1]; [left; exact (proj1 (HOF x Hx ltac:(lia)))|].
      destruct (Z_lt_le_dec x (fr + 312)) as [C2|C2]; [|left; exact (proj1 (HOF x Hx ltac:(lia)))].
      destruct (Z_lt_le_dec x (fr + 258)) as [D1|D1];
        [right; exact (f9_ba_some m1 (fr + 256) _ x Ba ltac:(rewrite length_le2; change (Z.of_nat 2) with 2; lia))|].
      destruct (Z_lt_le_dec x (fr + 272)) as [D2|D2].
      { left. change (outside (f9_W9 fr) x). apply f9_out9; lia. }
      destruct (Z_lt_le_dec x (fr + 280)) as [D3|D3];
        [right; exact (f9_ba_some m1 (fr + 272) _ x Bp ltac:(rewrite length_le8; change (Z.of_nat 8) with 8; lia))|].
      destruct (Z_lt_le_dec x (fr + 304)) as [D4|D4].
      { left. change (outside (f9_W9 fr) x). apply f9_out9; lia. }
      right. exact (f9_ba_some m1 (fr + 304) _ x Bn ltac:(rewrite length_le8; change (Z.of_nat 8) with 8; lia)). }
    apply (fl_stk _ m1 m2 fr (fr + FRAME_BYTES) HStk1 MU2 WM2). intros x Hx.
    destruct (Z_lt_le_dec x (fr + 256)) as [C1|C1]; [left; exact (proj2 (HOF x Hx ltac:(lia)))|].
    destruct (Z_lt_le_dec x (fr + 312)) as [C2|C2]; [|left; exact (proj2 (HOF x Hx ltac:(lia)))].
    destruct (reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j)) eqn:Erok.
    - destruct (HRP eq_refl) as (R1 & R2 & R3).
      destruct (Z_lt_le_dec x (fr + 258)) as [D1|D1];
        [right; exact (f9_cell_byte m2 (fr + 256) 2 _ x R1 ltac:(lia))|].
      destruct (Z_lt_le_dec x (fr + 272)) as [D2|D2].
      { left. change (outside (l2_W phi (flen g j) fr sp (t_g (g_in g) j) FS) x).
        apply l2_out3; unfold shadow_addr, ASAN_K, AC.FS_SIZE in *; lia. }
      destruct (Z_lt_le_dec x (fr + 280)) as [D3|D3];
        [right; exact (f9_cell_byte m2 (fr + 272) 8 _ x R2 ltac:(lia))|].
      destruct (Z_lt_le_dec x (fr + 304)) as [D4|D4].
      { left. change (outside (l2_W phi (flen g j) fr sp (t_g (g_in g) j) FS) x).
        apply l2_out3; unfold shadow_addr, ASAN_K, AC.FS_SIZE in *; lia. }
      right. exact (f9_cell_byte m2 (fr + 304) 8 _ x R3 ltac:(lia)).
    - left. unfold f9_WC, reac_ctrl_identity_reply_fp. rewrite Erok, l1_fpw1.
      unfold REAC_CTRL_IDENTITY_REPLY_K. cbn [app outside].
      unfold shadow_addr, ASAN_K, AC.FS_SIZE in *. repeat split; try exact I; lia. }
  (* the carried spills (exists-A form) *)
  assert (Tsp : forall off v, 0 <= off <= 408 -> spill regs mem off v -> spill regs2 m2 off v).
  { intros off v Hoff Hs.
    exact (f9_spill_tr regs regs2 mem m1 m2 _ _ A off v HA9 HAb ltac:(lia) E9 Hoff MU1 MU2 HOA Hs). }
  assert (TA : forall off v, 0 <= off <= 408 -> q64 mem (A + off) v -> q64 m2 (A + off) v).
  { intros off v Hoff Hq. apply (l8_q64 _ _ mem m1 m2 _ _ Hq MU1 MU2). intros x Hx. apply HOA. lia. }
  assert (TF : forall a bs, bytes_at rsegs mem a bs -> fr <= a -> a + Z.of_nat (length bs) <= fr + 256 ->
            bytes_at rsegs m2 a bs).
  { intros a bs Hb Ha1 Ha2. apply (l8_tr _ _ mem m1 m2 _ _ Hb MU1 MU2). intros x Hx. apply HOF; lia. }
  assert (TF2 : forall a bs, bytes_at rsegs mem a bs -> fr + 312 <= a -> a + Z.of_nat (length bs) <= fr + FRAME_BYTES ->
            bytes_at rsegs m2 a bs).
  { intros a bs Hb Ha1 Ha2. apply (l8_tr _ _ mem m1 m2 _ _ Hb MU1 MU2). intros x Hx. apply HOF; lia. }
  assert (TB : forall a bs, bytes_at rsegs mem a bs -> phi <= a ->
            a + Z.of_nat (length bs) <= phi + AC.a_size (flen g j) -> bytes_at rsegs m2 a bs).
  { intros a bs Hb Ha1 Ha2. apply (l8_tr _ _ mem m1 m2 _ _ Hb MU1 MU2). intros x Hx. apply HOB; lia. }
  assert (TAF : forall p n, addressable mem p n -> fr <= p -> p + n <= fr + FRAME_BYTES ->
            (p + n <= fr + 256 \/ fr + 312 <= p) -> addressable m2 p n).
  { intros p n Ha Hp1 Hp2 Hp3. apply (l8_addr2 _ _ mem m1 m2 _ _ Ha MU1 MU2). intros i Hi. apply HOFS; lia. }
  assert (Hbig : 50 <= flen g j -> AC.a_size (flen g j) = flen g j) by (intros H; unfold AC.a_size; lia).
  (* the conclusion *)
  split.
  { split; [exact Hphi0|]. apply (l8_addr2 _ _ mem m1 m2 _ _ HAd MU1 MU2). exact HOS. }
  split.
  { assert (TINa : addressable mem (g_p g) (g_n g) -> addressable m2 (g_p g) (g_n g)).
    { intros Ha. apply (l8_addr2 _ _ mem m1 m2 _ _ Ha MU1 MU2). intros i Hi.
      exact (proj2 (HINO (g_p g + i) ltac:(lia))). }
    assert (TINb : bytes_at rsegs m2 (g_p g) (g_in g)).
    { apply (l8_tr _ _ mem m1 m2 _ _ HIN3 MU1 MU2). intros x Hx. rewrite <- g_n_len in Hx.
      exact (proj1 (HINO x Hx)). }
    unfold FLSI, FLSH, PRO, f1_IN, FLC.
    split.
    - split.
      + split; [exact (Tsp 40 _ ltac:(lia) Hp40)|].
        split; [exact (Tsp 120 _ ltac:(lia) Hp120)|].
        split; [exact (Tsp 136 _ ltac:(lia) Hp136)|].
        split; [exact (Tsp 160 _ ltac:(lia) Hp160)|].
        split; [exact (Tsp 168 _ ltac:(lia) Hp168)|].
        split; [exact (Tsp 176 _ ltac:(lia) Hp176)|].
        split; [exact (Tsp 208 _ ltac:(lia) Hp208)|].
        split; [exact (Tsp 248 _ ltac:(lia) Hp248)|].
        split; [exact (TAF _ _ HfAd ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact TINb|].
        split; [intros Hn; split; [exact (proj1 (HpIN2 Hn)) | exact (TINa (proj2 (HpIN2 Hn)))]|].
        split; [exact (Tsp 184 _ ltac:(lia) Hp184)|].
        split; [exact (Tsp 256 _ ltac:(lia) Hp256)|].
        split; [exact (Tsp 264 _ ltac:(lia) Hp264)|].
        (* v1.9 PRO position 16: [A + 32] = fr + 2880, first.sroa.7 (A4's 0x813cc) *)
        split; [exact (Tsp 272 _ ltac:(lia) Hp272) | exact (Tsp 32 _ ltac:(lia) Hp32)].
      + split; [exact (Tsp 128 _ ltac:(lia) Hf128)|].
        split; [exact HStk2|].
        split; [exact (Tsp 144 _ ltac:(lia) Hf144)|].
        exact (TAF _ _ HfAd17 ltac:(lia) ltac:(lia) ltac:(lia)).
    - split; [exact (Tsp 216 _ ltac:(lia) Hf216)|].
      split; [exact (Tsp 224 _ ltac:(lia) Hf224)|].
      split; [exact (Tsp 248 _ ltac:(lia) Hf248)|].
      split; [split; [exact HIN1|]; split; [exact (TINa HIN2) | exact TINb]|].
      split; [exact (Tsp 256 _ ltac:(lia) Hc256)|].
      split; [exact (Tsp 184 _ ltac:(lia) Hc184)|].
      split; [exact (Tsp 192 _ ltac:(lia) Hc192)|].
      split; [exact (Tsp 80 _ ltac:(lia) Hc80)|].
      split; [exact (Tsp 88 _ ltac:(lia) Hc88)|].
      split; [exact (Tsp 96 _ ltac:(lia) Hc96)|].
      split; [exact (Tsp 272 _ ltac:(lia) Hc272)|].
      split; [exact (Tsp 264 _ ltac:(lia) Hc264)|].
      split; [exact (TAF _ _ HcAfg ltac:(unfold fragb; lia) ltac:(unfold fragb; lia) ltac:(unfold fragb; lia))|].
      split; [exact (TAF _ _ HcAid ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [exact (Tsp 72 _ ltac:(lia) Hc72)|].
      split; [exact (Tsp 64 _ ltac:(lia) Hc64)|].
      (* v1.9 FLC positions 13 / 14: [A + 56] = fr + 2889, [A + 48] = fr + 2890 (P12's 0x81d34 / 0x81d3c) *)
      split; [exact (Tsp 56 _ ltac:(lia) Hc56) | exact (Tsp 48 _ ltac:(lia) Hc48)]. }
  split.
  { destruct HLK as (HLj & HL21 & HLour). unfold LK. split; [exact HLj|]. split.
    - unfold rg in HL21 |- *. rewrite E21. exact HL21.
    - unfold OURb in *. apply (TF2 _ _ HLour ltac:(lia)). rewrite OUR_length. change (Z.of_nat 6) with 6. lia. }
  split.
  { unfold b5_C.
    split; [unfold rg in H23 |- *; rewrite E23; exact H23|].
    split; [unfold rg in H18 |- *; rewrite E18; exact H18|].
    split.
    { exists A. split; [unfold rg in HA9 |- *; rewrite E9; exact HA9|]. split; [exact HAb|].
      destruct HSP as (Q248 & Q256 & Q144 & Q184 & Q192 & Q80 & Q88 & Q96 & Q272 & Q264).
      split; [|exact (TA 232 _ ltac:(lia) H232)].
      unfold b5_SPILL.
      split; [exact (TA 248 _ ltac:(lia) Q248)|].
      split; [exact (TA 256 _ ltac:(lia) Q256)|].
      split; [exact (TA 144 _ ltac:(lia) Q144)|].
      split; [exact (TA 184 _ ltac:(lia) Q184)|].
      split; [exact (TA 192 _ ltac:(lia) Q192)|].
      split; [exact (TA 80 _ ltac:(lia) Q80)|].
      split; [exact (TA 88 _ ltac:(lia) Q88)|].
      split; [exact (TA 96 _ ltac:(lia) Q96)|].
      split; [exact (TA 272 _ ltac:(lia) Q272) | exact (TA 264 _ ltac:(lia) Q264)]. }
    split.
    { destruct HPH as (HPHb & HPHp & HPHfs). unfold b5_PH.
      split.
      { intros H50. apply (TB _ _ (HPHb H50) ltac:(lia)).
        unfold t_g. rewrite fr50_length. rewrite (Hbig H50). change (Z.of_nat 50) with 50. lia. }
      split; [intros H50; unfold AC.aspZ in *; rewrite E2; exact (HPHp H50)|].
      intros H0 (b & Hbr & Hwb & Hbin). apply (HPHfs H0). exists b. split; [exact Hbr|]. split; [|exact Hbin].
      apply (proj2 (l8_wm _ mem m1 (AC.as_tp AC.ASYMS) b MU1 ltac:(lia) ltac:(lia) (fun x Hx => proj1 (Otp x Hx)))).
      apply (proj2 (l8_wm _ m1 m2 (AC.as_tp AC.ASYMS) b MU2 ltac:(lia) ltac:(lia) (fun x Hx => proj2 (Otp x Hx)))). exact Hwb. }
    split.
    { destruct HFR as (HFRa1 & HFRa2 & HFRb & HFRl). unfold b5_FR.
      split; [exact (TAF _ _ HFRa1 ltac:(unfold fragb; lia) ltac:(unfold fragb; lia) ltac:(unfold fragb; lia))|].
      split; [exact (TAF _ _ HFRa2 ltac:(lia) ltac:(lia) ltac:(lia))|].
      split; [|exact HFRl].
      apply (TF2 _ _ HFRb ltac:(unfold fragb; lia)). rewrite HFRl. unfold fragb. change (Z.of_nat 72) with 72. lia. }
    split.
    { destruct HFSb as (HFS1 & (DB & HDB & HDB0 & HDB1)). unfold b5_FS. split.
      - intros FS0 HFSw HFS0r HFSin. apply (HFS1 FS0); [| exact HFS0r | exact HFSin].
        apply (proj2 (l8_wm _ mem m1 (AC.as_tp AC.ASYMS) FS0 MU1 ltac:(lia) ltac:(lia) (fun x Hx => proj1 (Otp x Hx)))).
        apply (proj2 (l8_wm _ m1 m2 (AC.as_tp AC.ASYMS) FS0 MU2 ltac:(lia) ltac:(lia) (fun x Hx => proj2 (Otp x Hx)))).
        exact HFSw.
      - exists DB. split; [|split; [exact HDB0 | exact HDB1]].
        apply (proj1 (l8_wm _ m1 m2 (AC.as_tp AC.ASYMS + 8) DB MU2 ltac:(lia) ltac:(lia)
          (fun x Hx => proj2 (proj1 (HOlo x ltac:(lia)))))).
        apply (proj1 (l8_wm _ mem m1 (AC.as_tp AC.ASYMS + 8) DB MU1 ltac:(lia) ltac:(lia)
          (fun x Hx => proj1 (proj1 (HOlo x ltac:(lia)))))).
        exact HDB. }
    split.
    { destruct HKN as (HKNb & HKNa). unfold b5_KN. split.
      - apply (l8_tr _ _ mem m1 m2 _ _ HKNb MU1 MU2). rewrite f9_kn_len. intros x Hx.
        change (Z.of_nat 112) with 112 in Hx. exact (proj1 (HOlo x ltac:(unfold KIND_NAME in Hx; lia))).
      - apply (l8_addr2 _ _ mem m1 m2 _ _ HKNa MU1 MU2). intros i Hi.
        exact (proj2 (HOlo (KIND_NAME + i) ltac:(unfold KIND_NAME; lia))). }
    split.
    { unfold FGj, FGb, FGBe in *. destruct HFGj as (HFGb & HFGok). split; [|exact HFGok].
      destruct HFR as (_ & _ & _ & HFRl).
      apply (TF2 _ _ HFGb ltac:(lia)). rewrite HFRl. change (Z.of_nat 72) with 72. lia. }
    { unfold FSj, FSb in *. destruct HFSj as (S104 & S112 & Sbody & Saddr & HFI).
      split; [exact (Tsp 104 _ ltac:(lia) S104)|]. split; [exact (Tsp 112 _ ltac:(lia) S112)|].
      (* v1.9 FSb positions 3 / 4: the FIRST body at fr + 2880 (at most 23 bytes, f9_fs_body_len) and the
         35-byte object first.sroa.7, both frame bytes above the three reply cells *)
      split.
      - apply (TF2 _ _ Sbody ltac:(lia)). pose proof (f9_fs_body_len (g_in g) j) as Hbl. lia.
      - split; [exact (TAF _ _ Saddr ltac:(lia) ltac:(lia) ltac:(lia)) | exact HFI]. } }
  split.
  { unfold b5_K.
    split; [unfold rg in HG20 |- *; rewrite E20; exact HG20|].
    split; [unfold rg in HG22 |- *; rewrite E22; exact HG22|].
    split; [unfold rg in HG24 |- *; rewrite E24; exact HG24|].
    split; [unfold rg in HG25 |- *; rewrite E25; exact HG25|].
    split.
    { destruct H280 as (A2 & HA2 & HA2b & Hq280).
      assert (EA2 : A2 = A) by exact (l9_rg_eq regs 9 A2 A HA2 HA9 HA2b HAb). subst A2.
      exists A. split; [unfold rg in HA9 |- *; rewrite E9; exact HA9|]. split; [exact HAb|].
      exact (TA 280 _ ltac:(lia) Hq280). }
    split; [|exact Hrargs].
    unfold u32 in *. apply (TF _ _ H176 ltac:(lia)). rewrite length_le4. change (Z.of_nat 4) with 4. lia. }
  split.
  { unfold b5_RC.
    assert (AC1 : addressable m1 (fr + 256) 2).
    { apply (l7_addr_cell m1 fr 256 2 (Z_to_bv 8 2));
        [exact Hfrm | lia | reflexivity | lia | lia | intros a Ha; apply Happ; lia | lia | exact Bs32 |].
      right. change (bv_signed (Z_to_bv 8 2)) with 2. lia. }
    assert (AC2 : addressable m1 (fr + 272) 8).
    { apply (l7_addr_cell m1 fr 272 8 (Z_to_bv 8 0));
        [exact Hfrm | lia | reflexivity | lia | lia | intros a Ha; apply Happ; lia | lia | exact Bs34 |].
      left. reflexivity. }
    assert (AC3 : addressable m1 (fr + 304) 8).
    { apply (l7_addr_cell m1 fr 304 8 (Z_to_bv 8 0));
        [exact Hfrm | lia | reflexivity | lia | lia | intros a Ha; apply Happ; lia | lia | exact Bs38 |].
      left. reflexivity. }
    split; [apply (l5_addr_keep m1 m2 _ _ _ AC1 MU2); intros i Hi;
            apply (l8_SWC fr sp FS phi (flen g j) (t_g (g_in g) j)); lia|].
    split; [apply (l5_addr_keep m1 m2 _ _ _ AC2 MU2); intros i Hi;
            apply (l8_SWC fr sp FS phi (flen g j) (t_g (g_in g) j)); lia|].
    apply (l5_addr_keep m1 m2 _ _ _ AC3 MU2); intros i Hi;
      apply (l8_SWC fr sp FS phi (flen g j) (t_g (g_in g) j)); lia. }
  split; [unfold rg; exact E10|].
  split; [exact HRP|].
  split.
  { unfold IDj, IDb, IDBe in *. destruct HIDj as (HIDb & HIDok). split; [|exact HIDok].
    apply (TF2 _ _ HIDb ltac:(lia)). rewrite f9_tID_len. change (Z.of_nat 38) with 38. lia. }
  split.
  { destruct HF17 as (A2 & HA2 & HA2b & Hq192).
    assert (EA2 : A2 = A) by exact (l9_rg_eq regs 9 A2 A HA2 HA9 HA2b HAb). subst A2.
    exists A. split; [unfold rg in HA9 |- *; rewrite E9; exact HA9|]. split; [exact HAb|].
    exact (TA 200 _ ltac:(lia) Hq192). }
  split.
  { destruct HW240 as (A2 & HA2 & HA2b & w240 & Hq240 & Hw240).
    assert (EA2 : A2 = A) by exact (l9_rg_eq regs 9 A2 A HA2 HA9 HA2b HAb). subst A2.
    exists A. split; [unfold rg in HA9 |- *; rewrite E9; exact HA9|]. split; [exact HAb|].
    exists w240. split; [exact (TA 240 _ ltac:(lia) Hq240) | exact Hw240]. }
  { destruct HPF as (A2 & HA2 & HA2b & HR50 & HR8819).
    assert (EA2 : A2 = A) by exact (l9_rg_eq regs 9 A2 A HA2 HA9 HA2b HAb). subst A2.
    exists A. split; [unfold rg in HA9 |- *; rewrite E9; exact HA9|]. split; [exact HAb|].
    split.
    - intros H50. destruct (HR50 H50) as (_ & Hphib).
      pose proof (Hbig H50) as Ebig.
      split.
      { exists (t_g (g_in g) j). split; [|unfold t_g; rewrite fr50_length; lia].
        destruct HPH as (HPHb & _). apply (TB _ _ (HPHb H50) ltac:(lia)).
        unfold t_g. rewrite fr50_length, Ebig. change (Z.of_nat 50) with 50. lia. }
      { apply (TB _ _ Hphib ltac:(lia)). rewrite Ebig.
        assert (Lp : (length (t_phi (g_in g) j) <= Z.to_nat (flen g j))%nat)
          by (unfold t_phi, f_phi, flen, t_len; apply firstn_le_length).
        lia. }
    - intros H8819.
      assert (H50 : 50 <= flen g j).
      { pose proof H8819 as H8. unfold t_8819, t_big in H8. apply andb_prop in H8 as (H8 & _).
        apply andb_prop in H8 as (H8 & _). apply Z.leb_le in H8. exact H8. }
      pose proof (Hbig H50) as Ebig.
      destruct (HR8819 H8819) as ((f16 & v14 & v15 & v16 & v17 & U16 & B14 & B15 & B16 & B17 & V14 & V15 & V16 &
          V17 & S14 & S15 & S16 & S17 & EF & EK) &
        (ls & rs & Q56 & Hls & Hlsl & Hrs & Hrsl & Hcmp & Had186) &
        (ls2 & rs2 & Q48 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcmp2 & Had180)).
      assert (TS : forall k, 14 <= k <= 17 -> b8 mem (Z.shiftr (phi + k) 3 + ASAN_K) 0 ->
                b8 m2 (Z.shiftr (phi + k) 3 + ASAN_K) 0).
      { intros k Hk Hb. unfold b8 in *. apply (l8_tr _ _ mem m1 m2 _ _ Hb MU1 MU2).
        intros x Hx. cbn [length] in Hx. change (Z.of_nat 1) with 1 in Hx.
        rewrite Z.shiftr_div_pow2 in Hx by lia. change (2 ^ 3) with 8 in Hx.
        replace x with (shadow_addr (phi + k)) by (unfold shadow_addr; lia).
        apply (HOS k). lia. }
      split.
      { exists f16, v14, v15, v16, v17.
        split; [unfold u16 in *; apply (TF _ _ U16 ltac:(lia)); rewrite length_le2; change (Z.of_nat 2) with 2; lia|].
        split; [unfold b8 in *; apply (TB _ _ B14 ltac:(lia)); cbn [length]; change (Z.of_nat 1) with 1; lia|].
        split; [unfold b8 in *; apply (TB _ _ B15 ltac:(lia)); cbn [length]; change (Z.of_nat 1) with 1; lia|].
        split; [unfold b8 in *; apply (TB _ _ B16 ltac:(lia)); cbn [length]; change (Z.of_nat 1) with 1; lia|].
        split; [unfold b8 in *; apply (TB _ _ B17 ltac:(lia)); cbn [length]; change (Z.of_nat 1) with 1; lia|].
        split; [exact V14|]. split; [exact V15|]. split; [exact V16|]. split; [exact V17|].
        split; [exact (TS 14 ltac:(lia) S14)|]. split; [exact (TS 15 ltac:(lia) S15)|].
        split; [exact (TS 16 ltac:(lia) S16)|]. split; [exact (TS 17 ltac:(lia) S17)|].
        split; [exact EF | exact EK]. }
      split.
      { exists (firstn 6 ls), (firstn 6 rs).
        assert (Lls : length (firstn 6 ls) = 6%nat) by (rewrite length_firstn; lia).
        assert (Lrs : length (firstn 6 rs) = 6%nat) by (rewrite length_firstn; lia).
        split; [exact (TA 72 _ ltac:(lia) Q56)|].
        split; [apply (TF _ _ (f9_ba_firstn _ _ _ 6 Hls) ltac:(lia)); rewrite Lls; change (Z.of_nat 6) with 6; lia|].
        split; [lia|].
        split; [apply (TB _ _ (f9_ba_firstn _ _ _ 6 Hrs) ltac:(lia)); rewrite Lrs, Ebig; change (Z.of_nat 6) with 6;
                lia|].
        split; [lia|].
        split; [rewrite f9_mcmp_firstn; exact Hcmp|].
        exact (TAF _ _ Had186 ltac:(lia) ltac:(lia) ltac:(lia)). }
      { exists (firstn 6 ls2), (firstn 6 rs2).
        assert (Lls : length (firstn 6 ls2) = 6%nat) by (rewrite length_firstn; lia).
        assert (Lrs : length (firstn 6 rs2) = 6%nat) by (rewrite length_firstn; lia).
        split; [exact (TA 64 _ ltac:(lia) Q48)|].
        split; [apply (TF _ _ (f9_ba_firstn _ _ _ 6 Hls2) ltac:(lia)); rewrite Lls; change (Z.of_nat 6) with 6; lia|].
        split; [lia|].
        split; [apply (TB _ _ (f9_ba_firstn _ _ _ 6 Hrs2) ltac:(lia)); rewrite Lrs, Ebig; change (Z.of_nat 6) with 6;
                lia|].
        split; [lia|].
        split; [rewrite f9_mcmp_firstn; exact Hcmp2|].
        exact (TAF _ _ Had180 ltac:(lia) ltac:(lia) ltac:(lia)). } }
Qed.

End S_l8.


Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract (lib/A/Prog/reac_ctrl_identity_reply_c.v), taken as a Section Hypothesis. *)
Hypothesis HIR : reac_ctrl_identity_reply_contract.

Lemma f9_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a known register slot `getr regs r` to its carried value, from H : rg regs r v. *)
Ltac f9_subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

Lemma seg_F9 : forall j, Hat B APIf ra (Inv_A81ff4_at B APIf ra) j -> Hat B APIf ra (Inv_A81f88_at B APIf ra) j.
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    Hgn & Hj & HHB & HFLSI & HLK & HbC & HbK & Ha0 & HNB & HIDj & HF17 & HW240 & HPF).
  subst c. rewrite SEGS.
  pose proof HbC as (Hs7 & Hs2 & (A & H9 & HAb & HSP & _) & HPH & HFR & HFS & HKN & HFGj & HFSj).
  pose proof HSP as (Hq248 & Hq256 & Hq144 & Hq184 & Hq208 & Hqs64 & Hqs72 & Hqs80 & Hq272 & Hq264).
  pose proof HFLSI as ((_ & _ & HfStk & _ & _) & _).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAGf & HWAf &
    HTop1 & HTop2 & HTop3 & Hhb & Hlive).
  assert (EA2 : A2 = A).
  { pose proof Hwin as (Hwb0 & Hwb1 & _).
    assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
    exact (l9_rg_eq regs 9 A2 A Hr9 H9 ltac:(lia) HAb). }
  subst A2.
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGT & Hfrapp).
  pose proof (f9_PL_of B APIf ra g fr _ regs mem md HFRA HFS) as HPL.
  destruct (f9_entry_of B APIf ra g j phi fr regs mem md A HFRA H9 HAb HNB) as
    (HXb & HS30 & Hfr0 & HA0 & HfrA & HA64 & HS3A & HS3fr & Wsh & (b & RK & OK) & (c0 & RC0 & HC0)).
  assert (Wcell : forall k n, 0 <= k -> 0 <= n -> 256 <= k -> k + n <= 312 -> wr_at rsegs mem (fr + k) n).
  { intros k n Hk Hn Hk1 Hk2. destruct HfStk as (Hs0 & Hs1 & Hs).
    split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (Hs (fr + k + i) ltac:(lia))). }
  (* ---- phase A: 0x81f88 - 0x81fe4 ---- *)
  apply (sl_run_lib regs (Z_to_bv 64 0x81f88) mem md
    (fun R pc' mem1 =>
       pc' = Z_to_bv 64 0x81fe8 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 9 = Z_to_bv 64 A /\ getr R 18 = Z_to_bv 64 (flen g j) /\ getr R 19 = Z_to_bv 64 (Sfr fr) /\
       getr R 23 = Z_to_bv 64 phi /\ getr R 26 = Z_to_bv 64 ASAN_K /\
       getr R 12 = Z_to_bv 64 (fr + 256) /\ getr R 13 = Z_to_bv 64 (fr + 272) /\
       getr R 14 = Z_to_bv 64 (fr + 304) /\
       munch (f9_WA (Sfr fr) fr) mem mem1 /\ wmono rsegs mem mem1 /\
       (forall q, (exists bq, mbyte rsegs mem q = Some bq) -> exists bq, mbyte rsegs mem1 q = Some bq) /\
       bytes_at rsegs mem1 (Sfr fr + 32) (le1 (Z_to_bv 64 2)) /\
       bytes_at rsegs mem1 (Sfr fr + 34) (le1 (Z_to_bv 64 0)) /\
       bytes_at rsegs mem1 (Sfr fr + 38) (le1 (Z_to_bv 64 0)) /\
       bytes_at rsegs mem1 (fr + 256) (le2 (Z_to_bv 64 0)) /\
       bytes_at rsegs mem1 (fr + 272) (le8 (Z_to_bv 64 0)) /\
       bytes_at rsegs mem1 (fr + 304) (le8 (Z_to_bv 64 0)) /\
       wr_at rsegs mem1 (fr + 256) 2 /\ wr_at rsegs mem1 (fr + 272) 8 /\ wr_at rsegs mem1 (fr + 304) 8)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f9_mkR_of_expand.
    f9_subst_slot H9. f9_subst_slot Ha0. f9_subst_slot Hs2. f9_subst_slot Hr19. f9_subst_slot Hs7.
    f9_subst_slot Hr26.
    apply f9_evtA with (X := kind_name_addr (t_k (g_in g) j)) (A := A) (S3 := Sfr fr) (fr := fr) (phi := phi)
                       (len := flen g j) (b := b) (c0 := c0); try assumption.
    + exact (Wcell 256 2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (Wcell 272 8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (Wcell 304 8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros mem1 MU WM PR Bs32 Bs34 Bs38 Ba Bp Bn Wa1 Wp1 Wn1.
      eexists _, _, _. split; [reflexivity|].
      repeat (split; [solve [reflexivity | assumption] | ]); solve [reflexivity | assumption].
  - intros R pc' mem1 regs1 md1 HK Hreg Hmat.
    destruct HK as (Hpc & E2 & E3 & E4 & E8 & E20 & E21 & E22 & E24 & E25 & E9 & E18 & E19 & E23 & E26 &
      E12 & E13 & E14 & MU & WM & PR & Bs32 & Bs34 & Bs38 & Ba & Bp & Bn & Wa1 & Wp1 & Wn1).
    subst pc'.
    assert (Fr2 : getr regs1 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs1 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs1 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs1 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr20 : getr regs1 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (Fr21 : getr regs1 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (Fr22 : getr regs1 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (Fr24 : getr regs1 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (Fr25 : getr regs1 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (R9 : rg regs1 9 A) by (unfold rg; rewrite Hreg; exact E9).
    assert (R18 : rg regs1 18 (flen g j)) by (unfold rg; rewrite Hreg; exact E18).
    assert (R19 : rg regs1 19 (Sfr fr)) by (unfold rg; rewrite Hreg; exact E19).
    assert (R23 : rg regs1 23 phi) by (unfold rg; rewrite Hreg; exact E23).
    assert (R26 : rg regs1 26 ASAN_K) by (unfold rg; rewrite Hreg; exact E26).
    assert (R12 : rg regs1 12 (fr + 256)) by (unfold rg; rewrite Hreg; exact E12).
    assert (R13 : rg regs1 13 (fr + 272)) by (unfold rg; rewrite Hreg; exact E13).
    assert (R14 : rg regs1 14 (fr + 304)) by (unfold rg; rewrite Hreg; exact E14).
    assert (Fr9 : getr regs1 9 = getr regs 9)
      by (unfold rg in R9, H9; rewrite R9; symmetry; exact H9).
    assert (Fr18 : getr regs1 18 = getr regs 18)
      by (unfold rg in R18, Hs2; rewrite R18; symmetry; exact Hs2).
    assert (Fr19 : getr regs1 19 = getr regs 19)
      by (unfold rg in R19, Hr19; rewrite R19; symmetry; exact Hr19).
    assert (Fr23 : getr regs1 23 = getr regs 23)
      by (unfold rg in R23, Hs7; rewrite R23; symmetry; exact Hs7).
    assert (Fr26 : getr regs1 26 = getr regs 26)
      by (unfold rg in R26, Hr26; rewrite R26; symmetry; exact Hr26).
    assert (Haspz1 : AC.aspZ regs1 = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    assert (HGT' : 6283264 <= fr) by (unfold AC.GT in HGT; lia).
    (* the three reply cells are present after the stores *)
    assert (HCELL : forall x, fr + 256 <= x < fr + 258 \/ fr + 272 <= x < fr + 280 \/ fr + 304 <= x < fr + 312 ->
              exists bq, mbyte rsegs mem1 x = Some bq).
    { intros x [Hx | [Hx | Hx]].
      - exact (f9_ba_some mem1 (fr + 256) _ x Ba ltac:(rewrite length_le2; change (Z.of_nat 2) with 2; lia)).
      - exact (f9_ba_some mem1 (fr + 272) _ x Bp ltac:(rewrite length_le8; change (Z.of_nat 8) with 8; lia)).
      - exact (f9_ba_some mem1 (fr + 304) _ x Bn ltac:(rewrite length_le8; change (Z.of_nat 8) with 8; lia)). }
    (* FRA and ENT across the six stores, at the entry registers and at regs1 *)
    destruct (f9_fra_st B APIf ra empty FF g fr _ regs regs mem mem1 md HFRA HENT MU WM PR HCELL
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as (HFRA1r & HENT1).
    destruct (f9_fra_st B APIf ra empty FF g fr _ regs regs1 mem mem1 md HFRA HENT MU WM PR HCELL
                Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26) as (HFRA1 & _).
    assert (HFRA1' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs1 mem1 md1).
    { apply (sl_fra_move B APIf ra g fr _ regs1 regs1 mem1 md md1 HFRA1); try reflexivity. exact Hmat. }
    assert (HENT1' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem1 md1)
      by (eapply ent_mat; [exact HENT1 | exact Hmat]).
    assert (HRO1 : ro_agree rsegs mem1).
    { pose proof HFRA1r as (_ & _ & _ & _ & _ & Hro1 & _). exact Hro1. }
    (* ---- phase B: 0x81fe8 - 0x81ff0, through the call ---- *)
    destruct (f9_pre_of B APIf ra g j phi fr regs mem mem1 md HFRA HFRA1r HHB HPH HFS MU HRO1
                Bs32 Bs34 Bs38 Ba Bp Bn Wa1 Wp1 Wn1) as (FS & HWMtp & HFSb & HGTFS & HPL1 & HPRE).
    assert (HPL1' : f9_PL fr regs1 mem1).
    { destruct HPL1 as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|].
      split; [rewrite Haspz1; exact P3|]. split; [|exact P5].
      intros A' HA' HA'b. apply P4; [|exact HA'b]. unfold rg in *. rewrite Fr9 in HA'. exact HA'. }
    assert (Hsp1 : getr regs1 2 = Z_to_bv 64 (AC.aspZ regs))
      by (rewrite Fr2, Haspz; exact Hr2).
    assert (Htp1 : getr regs1 4 = Z_to_bv 64 (AC.as_tp AC.ASYMS)) by (rewrite Fr4; exact Hr4).
    apply (sl_run_lib regs1 (Z_to_bv 64 0x81fe8) mem1 md1
      (fun R pc' mem2 =>
         pc' = Z_to_bv 64 0x81ff4 /\
         getr R 2 = getr regs1 2 /\ getr R 3 = getr regs1 3 /\ getr R 4 = getr regs1 4 /\
         getr R 8 = getr regs1 8 /\ getr R 20 = getr regs1 20 /\ getr R 21 = getr regs1 21 /\
         getr R 22 = getr regs1 22 /\ getr R 24 = getr regs1 24 /\ getr R 25 = getr regs1 25 /\
         getr R 9 = Z_to_bv 64 A /\ getr R 18 = Z_to_bv 64 (flen g j) /\
         getr R 19 = Z_to_bv 64 (Sfr fr) /\ getr R 23 = Z_to_bv 64 phi /\
         getr R 26 = Z_to_bv 64 ASAN_K /\
         getr R 10 = Z_to_bv 64 (reply_ret phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j)) /\
         munch (f9_WC phi (flen g j) fr (AC.aspZ regs) FS (t_g (g_in g) j)) mem1 mem2 /\
         wmono rsegs mem1 mem2 /\ ro_agree rsegs mem2 /\
         stk rsegs mem2 (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) (AC.aspZ regs) /\
         (reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = true ->
            rw_cells rsegs mem2 (fr + 256) [CB 2 (reply_addr (t_g (g_in g) j))] /\
            rw_cells rsegs mem2 (fr + 272) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
            rw_cells rsegs mem2 (fr + 304) [CB 8 (le8 (Z_to_bv 64 (ir_s (t_g (g_in g) j) - 13)))]) /\
         asan_cells mem2 /\ shadow_rw mem2 /\
         addressable mem2 (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] mem2 (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) (AC.aspZ regs)
           (reac_ctrl_identity_reply_W phi (fr + 256) (fr + 272) (fr + 304) (AC.aspZ regs))
           (reac_ctrl_identity_reply_D phi (flen g j) (fr + 256) (fr + 272) (fr + 304)))
      (Post B APIf ra g)).
    + destruct HFRA1' as (_ & _ & _ & _ & _ & _ & _ & Hh1 & _). exact Hh1.
    + rewrite f9_mkR_of_expand.
      f9_subst_slot R9. f9_subst_slot R12. f9_subst_slot R13. f9_subst_slot R14.
      f9_subst_slot R18. f9_subst_slot R19. f9_subst_slot R23. f9_subst_slot R26.
      apply f9_evtB with (A := A) (S3 := Sfr fr) (fr := fr) (phi := phi) (len := flen g j)
                         (S := AC.aspZ regs) (FS := FS) (TP := AC.as_tp AC.ASYMS)
                         (G := t_g (g_in g) j) (ja := le2 (Z_to_bv 64 0)) (jp := le8 (Z_to_bv 64 0))
                         (jn := le8 (Z_to_bv 64 0)).
      * exact HIR.
      * exact Hsp1.
      * exact Htp1.
      * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      * exact HGT'.
      * exact HPRE.
      * intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mem2
          MUc WMc ROc STc RPc ACc SHc ADc FPc TLc.
        eexists _, _, _. split; [reflexivity|].
        repeat (split; [solve [reflexivity | assumption] | ]); solve [reflexivity | assumption].
    + intros R2 pc2 mem2 regs2 md2 HK2 Hreg2 Hmat2.
      destruct HK2 as (Hpc2 & F2 & F3 & F4 & F8' & F20 & F21 & F22 & F24 & F25 & F9' & F18 & F19 & F23 &
        F26 & F10' & MUc & WMc & ROc & STc & RPc & ACc & SHc & ADc & FPc).
      subst pc2.
      pose proof MUc as MUc1. rewrite <- Haspz1 in MUc1. cbv [f9_WC] in MUc1.
      pose proof STc as STc1. rewrite <- Haspz1 in STc1.
      pose proof ADc as ADc1. rewrite <- Haspz1 in ADc1.
      pose proof FPc as FPc1. rewrite <- Haspz1 in FPc1.
      assert (Eq2 : getr regs2 2 = getr regs 2) by (rewrite Hreg2, F2; exact Fr2).
      assert (Eq9 : getr regs2 9 = getr regs 9)
        by (rewrite Hreg2, F9'; unfold rg in H9; symmetry; exact H9).
      assert (Eq18 : getr regs2 18 = getr regs 18)
        by (rewrite Hreg2, F18; unfold rg in Hs2; symmetry; exact Hs2).
      assert (Eq20 : getr regs2 20 = getr regs 20) by (rewrite Hreg2, F20; exact Fr20).
      assert (Eq21 : getr regs2 21 = getr regs 21) by (rewrite Hreg2, F21; exact Fr21).
      assert (Eq22 : getr regs2 22 = getr regs 22) by (rewrite Hreg2, F22; exact Fr22).
      assert (Eq23 : getr regs2 23 = getr regs 23)
        by (rewrite Hreg2, F23; unfold rg in Hs7; symmetry; exact Hs7).
      assert (Eq24 : getr regs2 24 = getr regs 24) by (rewrite Hreg2, F24; exact Fr24).
      assert (Eq25 : getr regs2 25 = getr regs 25) by (rewrite Hreg2, F25; exact Fr25).
      assert (Eq10 : getr regs2 10 =
                Z_to_bv 64 (reply_ret phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j)))
        by (rewrite Hreg2; exact F10').
      assert (K2 : getr regs2 2 = getr regs1 2) by (rewrite Hreg2; exact F2).
      assert (K3 : getr regs2 3 = getr regs1 3) by (rewrite Hreg2; exact F3).
      assert (K4 : getr regs2 4 = getr regs1 4) by (rewrite Hreg2; exact F4).
      assert (K8 : getr regs2 8 = getr regs1 8) by (rewrite Hreg2; exact F8').
      assert (K9 : getr regs2 9 = getr regs1 9)
        by (rewrite Hreg2, F9'; unfold rg in R9; symmetry; exact R9).
      assert (K19 : getr regs2 19 = getr regs1 19)
        by (rewrite Hreg2, F19; unfold rg in R19; symmetry; exact R19).
      assert (K26 : getr regs2 26 = getr regs1 26)
        by (rewrite Hreg2, F26; unfold rg in R26; symmetry; exact R26).
      (* FRA and ENT across the call and the lazy-page step md1 -> md2 *)
      destruct (f9_fra_call B APIf ra empty FF g fr _ phi (flen g j) regs1 regs2 mem1 mem2 md1 md2 FS
                  (t_g (g_in g) j) HFRA1' HPL1' HWMtp HFSb MUc1 WMc ROc STc1 ADc1 RPc SHc FPc1
                  K2 K3 K4 K8 K9 K19 K26 Hmat2) as (HFRA2 & HENTf).
      pose proof (HENTf HENT1') as HENT2.
      (* the exit body *)
      rewrite <- SEGS. apply Hexit.
      unfold Inv_A81ff4_at, b5_CUT, CUTST.
      exists phi, regs2, mem2, md2, fr.
      split; [reflexivity|].
      split; [exact HFRA2|].
      split; [exact HENT2|].
      split; [exact Hgn|].
      split; [exact Hj|].
      exact (f9_exit_of B APIf ra g j phi fr regs regs2 mem mem1 mem2 md md2 A FS
               HFRA HFRA2 HHB HFLSI HLK HbC HbK HIDj HF17 HW240 HPF H9 HAb MU MUc WM WMc
               HWMtp HFSb HGTFS Bs32 Bs34 Bs38 Ba Bp Bn
               Eq2 Eq9 Eq18 Eq20 Eq21 Eq22 Eq23 Eq24 Eq25 Eq10 RPc).
Qed.

End S.
