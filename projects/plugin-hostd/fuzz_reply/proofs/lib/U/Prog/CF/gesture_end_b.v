(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 664 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass9G.v, with its module paths and module names changed; 466 of its 523 lines of code are new or changed and 607 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/HarnessGlue.v, with its module paths and module names changed; 828 of its 888 lines of code are new or changed and 463 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YO0u YO0x YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strlen_c send_line_c gesture_end_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c send_line_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ge_bytes_at_trunc : forall m A (s t : list byte) n,
  bytes_at rsegs m A (s ++ t) -> bytes_at rsegs m A (s ++ firstn n t).
Proof.
  intros m A s t n H. apply bytes_at_app in H. destruct H as [H1 H2]. apply bytes_at_app. split; [exact H1|].
  rewrite <- (firstn_skipn n t) in H2. apply bytes_at_app in H2. exact (proj1 H2).
Qed.

Lemma ge_head : strlen_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (x slack : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> mem_inv rsegs m ->
  bytes_at rsegs m (bv_unsigned a0) (x ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) x ->
  (- (bv_unsigned a0 + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (bv_unsigned a0 + Z.of_nat (length x) + 8 <= bv_unsigned sp + -16 \/ bv_unsigned sp <= bv_unsigned a0) ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x14d3c) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0' t1' t2' a0 s1 a0
                   (Z_to_bv 64 (Z.of_nat (length x))) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                   t3' t4' t5' t6')
                F (Z_to_bv 64 SEND_LINE) fc None m1 (seg_rom rsegs) /\
       munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
       rw_cells rsegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 GESTURE_END) fc None m (seg_rom rsegs)).
Proof.
  intros SLEN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    x slack ST LO MI HX NZ PAD SEP.
  unfold GESTURE_END, SEND_LINE.
  pose proof (bytes_at_bound _ _ _ _ HX) as XB. rewrite length_app in XB. cbn [length] in XB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (Z.mod_pos_bound (- (bv_unsigned a0 + Z.of_nat (length x) + 1)) 8 ltac:(lia)) as R8.
  remember (Z.to_nat ((- (bv_unsigned a0 + Z.of_nat (length x) + 1)) mod 8)) as k eqn:Ek.
  assert (KZ : Z.of_nat k = (- (bv_unsigned a0 + Z.of_nat (length x) + 1)) mod 8) by (rewrite Ek; apply Z2Nat.id; lia).
  clear Ek.
  assert (HS : bytes_at rsegs m (bv_unsigned a0) (x ++ Z_to_bv 8 0 :: firstn k slack)).
  { replace (x ++ Z_to_bv 8 0 :: firstn k slack) with ((x ++ [Z_to_bv 8 0]) ++ firstn k slack)
      by (rewrite <- app_assoc; reflexivity).
    apply ge_bytes_at_trunc. rewrite <- app_assoc. exact HX. }
  assert (KL : length (firstn k slack) = k) by (apply firstn_length_le; lia).
  clear HX.
  pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  step. step. step. step. step.
  call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x (firstn k slack)).
  1: eassumption.
  1: exact NZ.
  1: rewrite KL; lia.
  1: assumption.
  cbv delta [mkR].
  step. step. step.
  finish.
Qed.

Lemma ge_tail :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (B : Z) (s0v rav : word),
  sp = Z_to_bv 64 B -> 0 <= B -> B + 16 < 2 ^ 64 ->
  rw_cells rsegs m B [C8 s0v; C8 rav] ->
  evt rsegs
    (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (B + 16)) gp tp t0 t1 t2 s0v s1 (Z_to_bv 64 END5_ADDR) (Z_to_bv 64 5)
                            a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 SEND_LINE) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d3c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m B s0v rav
    -> HB0 HB1 FR.
  unfold END5_ADDR, SEND_LINE.
  step. step. step. step. step. step. step.
  apply evt_done. reflexivity.
Qed.

Lemma ge_ub_prid_lt : forall s p n, WF s -> In (p, n) (user_blocks s) -> (prid p < length (st_regions s))%nat.
Proof.
  intros s p n HW Hin.
  destruct (YO0x.user_blocks_frame s p n HW Hin) as (g & am & idx & fr & U & _ & _ & _ & _ & ->).
  unfold frame_ptr. rewrite YO0u.prid_padd, YO0u.prid_slot_start.
  exact (YO0u.used_group_prid_lt [] None U0 s g am HW U).
Qed.

Lemma ge_with_vmmaps_twice : forall h h' md, with_vmmaps h (with_vmmaps h' md) = with_vmmaps h md.
Proof. intros h h' md. destruct md. reflexivity. Qed.

Lemma ge_tr_eq : forall live mx NO CAP XL j o, gesture_end_tr live mx NO CAP XL j o =
  send_line_tr live mx NO CAP XL j o ++ send_line_tr live mx (NO + XL) (send_line_cap live mx NO CAP XL) 5
    (j + nretF (send_line_tr live mx NO CAP XL j o)) (send_line_out live mx NO CAP XL j o).
Proof. reflexivity. Qed.

(* The room for the first send_line, from gesture_end's. *)
Lemma ge_room1 : forall F (bnd : rt_R F) live mx NO CAP XL L A OUT,
  (forall qs, length qs = nretF (gesture_end_tr live mx NO CAP XL 0 (known_at L A OUT)) ->
     roomF F qs bnd (gesture_end_tr live mx NO CAP XL 0 (known_at L A OUT))) ->
  forall qs1, length qs1 = nretF (send_line_tr live mx NO CAP XL 0 (known_at L A OUT)) ->
    roomF F qs1 bnd (send_line_tr live mx NO CAP XL 0 (known_at L A OUT)).
Proof.
  intros F bnd live mx NO CAP XL L A OUT HR. rewrite ge_tr_eq in HR.
  exact (p3a_room_pre F bnd _ _ (proj1 (p3a_slt_wf live mx NO CAP XL 0 (known_at L A OUT) I)) HR).
Qed.

(* The room for the second send_line, run from where the first left the resource state; the first left the block
   OUT1 live under the name its addresses resolve to. *)
Lemma ge_room2 : forall F (bnd : rt_R F) mx NO CAP XL L A OUT L1 A1 OUT1 CAP1 qs1,
  NoDup (map fst (blocks L1 A1)) ->
  length qs1 = nretF (send_line_tr true mx NO CAP XL 0 (known_at L A OUT)) ->
  live_at L1 A1 (resolveF qs1 (send_line_out true mx NO CAP XL 0 (known_at L A OUT))) OUT1 CAP1 ->
  CAP1 = send_line_cap true mx NO CAP XL ->
  (forall qs, length qs = nretF (gesture_end_tr true mx NO CAP XL 0 (known_at L A OUT)) ->
     roomF F qs bnd (gesture_end_tr true mx NO CAP XL 0 (known_at L A OUT))) ->
  forall qs2, length qs2 = nretF (send_line_tr true mx (NO + XL) CAP1 5 0 (known_at L1 A1 OUT1)) ->
    roomF F qs2 (runF F qs1 bnd (send_line_tr true mx NO CAP XL 0 (known_at L A OUT)))
      (send_line_tr true mx (NO + XL) CAP1 5 0 (known_at L1 A1 OUT1)).
Proof.
  intros F bnd mx NO CAP XL L A OUT L1 A1 OUT1 CAP1 qs1 ND LQ LA EC HR.
  destruct (p3a_slt_wf true mx NO CAP XL 0 (known_at L A OUT) I) as [Hw Ho].
  rewrite ge_tr_eq, <- EC in HR.
  exact (p3a_cat_room F bnd _ qs1 _ true mx (NO + XL) CAP1 5 (sptr_of L1 A1 OUT1) Hw Ho LQ
           (fun _ => eq_sym (p3a_live_known L1 A1 _ OUT1 CAP1 ND LA)) HR).
Qed.

(* gesture_end's resource post from the two send_line posts. *)
Lemma ge_res_live : forall F (bnd : rt_R F) mx NO CAP XL L A OUT L1 A1 OUT1 CAP1 L2 A2 OUT2 CAP2 qs1,
  NoDup (map fst (blocks L1 A1)) ->
  length qs1 = nretF (send_line_tr true mx NO CAP XL 0 (known_at L A OUT)) ->
  live_at L1 A1 (resolveF qs1 (send_line_out true mx NO CAP XL 0 (known_at L A OUT))) OUT1 CAP1 ->
  CAP1 = send_line_cap true mx NO CAP XL ->
  CAP2 = send_line_cap true mx (NO + XL) CAP1 5 -> CAP2 <> 0 ->
  (exists qs2, length qs2 = nretF (send_line_tr true mx (NO + XL) CAP1 5 0 (known_at L1 A1 OUT1)) /\
     rt_ok F A2 (runF F qs2 (runF F qs1 bnd (send_line_tr true mx NO CAP XL 0 (known_at L A OUT)))
                   (send_line_tr true mx (NO + XL) CAP1 5 0 (known_at L1 A1 OUT1))) /\
     (true = true ->
        live_at L2 A2 (resolveF qs2 (send_line_out true mx (NO + XL) CAP1 5 0 (known_at L1 A1 OUT1))) OUT2 CAP2)) ->
  exists qs, length qs = nretF (gesture_end_tr true mx NO CAP XL 0 (known_at L A OUT)) /\
    rt_ok F A2 (runF F qs bnd (gesture_end_tr true mx NO CAP XL 0 (known_at L A OUT))) /\
    (true = true -> live_at L2 A2 (resolveF qs (gesture_end_out true mx NO CAP XL 0 (known_at L A OUT))) OUT2 CAP2).
Proof.
  intros F bnd mx NO CAP XL L A OUT L1 A1 OUT1 CAP1 L2 A2 OUT2 CAP2 qs1 ND LQ LA EC EC2 NZ (qs2 & LQ2 & RT2 & LA2).
  destruct (p3a_slt_wf true mx NO CAP XL 0 (known_at L A OUT) I) as [Hw Ho].
  destruct (p3a_cat_run F bnd _ qs1 qs2 _ true mx (NO + XL) CAP1 5 (sptr_of L1 A1 OUT1) Hw Ho LQ
              (fun _ => eq_sym (p3a_live_known L1 A1 _ OUT1 CAP1 ND LA))) as (N & Rn & Fa).
  exists (qs1 ++ qs2).
  rewrite ge_tr_eq. unfold gesture_end_out. rewrite <- EC, Nat.add_0_l.
  split; [rewrite N, length_app, LQ2; reflexivity|].
  split; [rewrite Rn; exact RT2|].
  intros _. rewrite (Fa eq_refl) by (rewrite <- EC2; exact NZ). exact (LA2 eq_refl).
Qed.

Section GP.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis NODUP : blocks_nodup Bm API.

Lemma ge_find_none : forall segs T a,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? T) segs = true -> T <= a ->
  find_segment segs a 1 = None.
Proof using.
  induction segs as [|s segs IH]; intros T a H Ha; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  cbn [find_segment].
  destruct (Z.of_N (seg_base s) <=? a) eqn:E1; destruct (a + 1 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)) eqn:E2;
    cbn [andb]; try exact (IH T a H2 Ha).
  apply Z.leb_le in E2. lia.
Qed.

Lemma ge_rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 32) rsegs = true.
Proof using. vm_compute. reflexivity. Qed.

Lemma ge_rsv_top : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 32) (segments_reserved rsegs) = true.
Proof using. vm_compute. reflexivity. Qed.

Lemma ge_wx : wx_apart rsegs = true.
Proof using. vm_compute. reflexivity. Qed.

Lemma ge_hi_some : forall m a, 2 ^ 32 <= a < 2 ^ 64 -> writable_at rsegs m a -> exists b, m (Z_to_bv 64 a) = Some b.
Proof using.
  intros m a Ha H. unfold writable_at, wview in H. rewrite (unsigned_lit a) in H by lia.
  rewrite (ge_find_none rsegs (2 ^ 32) a ge_rsegs_top) in H by lia.
  destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply H; reflexivity].
Qed.

Lemma ge_hi_rw : forall a, 2 ^ 32 <= a < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof using.
  intros a Ha. unfold ro_addr. rewrite (unsigned_lit a) by lia.
  rewrite (ge_find_none rsegs (2 ^ 32) a ge_rsegs_top) by lia. reflexivity.
Qed.

Lemma ge_stk_norm : forall m lo hi, 2 ^ 32 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> stk rsegs (normalize rsegs m) lo hi.
Proof using.
  intros m lo hi Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (ge_hi_some m a ltac:(lia) (H a Ha)) as [b Hb].
  assert (N : normalize rsegs m (wa a) = Some b) by (unfold normalize, wa; rewrite ge_hi_rw by lia; exact Hb).
  split.
  - unfold wview. rewrite N. discriminate.
  - exists b. unfold mrd. rewrite N. reflexivity.
Qed.

Lemma ge_end5 : forall m, ro_agree rsegs m -> bytes_at rsegs m END5_ADDR END5.
Proof using.
  intros m Hro.
  pose proof (ro_cells_image rsegs (normalize rsegs m) END5_ADDR END5 (mem_inv_normalize rsegs m)
                ltac:(vm_compute; reflexivity) ltac:(unfold END5_ADDR; lia) ltac:(unfold END5_ADDR; cbn; lia)) as RO.
  destruct RO as [_ RO]. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO.
  exact (proj2 (bytes_at_rel rsegs m (normalize rsegs m) END5_ADDR END5 (mem_rel_normalize rsegs m Hro)) RO).
Qed.

Lemma ge_shape3 : forall R pc m ro ms,
  Regs6ss.ms_eqv (MS R fp_regs pc fp_csr None m ro) ms ->
  ms = YK11.mkst (ms_regs ms) pc m ro /\ Regs6ss.xregs_eqv R (ms_regs ms).
Proof using.
  intros R pc m ro [r f p s v c mm o] (X & F2 & P2 & S2 & V2 & C2 & M2 & O2). cbn in *. subst.
  split; [reflexivity | exact X].
Qed.

Lemma ge_shape1 : forall segs R pc m0 ro can ms,
  ms_rel segs can (MS R fp_regs pc fp_csr None m0 ro) -> Regs6ss.ms_eqv can ms ->
  ms = YK11.mkst (ms_regs ms) pc (ms_mem ms) ro /\ Regs6ss.xregs_eqv R (ms_regs ms) /\
  mem_rel segs (ms_mem ms) m0 /\ ms_mem can = ms_mem ms.
Proof using.
  intros segs R pc m0 ro [r1 f1 p1 s1 v1 c1 mm1 o1] [r f p s v c mm o]
    (R1 & F1 & P1 & S1 & V1 & C1 & O1 & M1) (X & F2 & P2 & S2 & V2 & C2 & M2 & O2).
  cbn in *. subst.
  split; [reflexivity|]. split; [exact X|]. split; [exact M1 | reflexivity].
Qed.

Lemma ge_getr_x : forall R R' r, Regs6ss.xregs_eqv R R' -> getr R' r = getr R r.
Proof using.
  intros R R' r H. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply H. exact E.
Qed.

Lemma ge_rp_seq : forall K E F L A regs mem md (m1 : word -> option byte) FL FH
    K1 E1 F1 regs1 L1 A1 regs1' mem1' md1 K2 E2 F2 regs2 L2 A2 regs2' mem2' md2,
  aa_MR API L A mem md -> WF A ->
  (forall a, in_img Bm a -> 0 <= a < YM05.alloc_ceiling) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (FL <= a < FH) -> m1 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, FL <= a < FH -> scratch_k Bm K regs a /\ YM05.alloc_ceiling <= a) ->
  relay_post Bm API K1 E1 F1 L A regs1 m1 md L1 A1 regs1' mem1' md1 ->
  relay_post Bm API K2 E2 F2 L1 A1 regs2 mem1' md1 L2 A2 regs2' mem2' md2 ->
  regs_preserved regs regs2 ->
  (forall a, scratch_k Bm K1 regs1 a -> scratch_k Bm K regs a) ->
  (forall a, scratch_k Bm K2 regs2 a -> scratch_k Bm K regs a) ->
  (forall a, scratch_k Bm K regs a -> ~ scratch_k Bm K2 regs2 a ->
     scratch_k Bm K1 regs1 a /\ YM05.alloc_ceiling <= a < 2 ^ 64) ->
  (forall a, E1 a -> E a) ->
  (forall a, (YM05.alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) -> E2 a -> E a) ->
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ E2 a) ->
  (forall a, F1 a -> F a) ->
  (forall p n, In (p, n) (user_blocks A) -> 0 < n -> ~ F (ptr_addr L p) -> In (p, n) (user_blocks A1) ->
     ~ F2 (ptr_addr L p)) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ~ F (ptr_addr L p) -> ~ E (ptr_addr L p + i) ->
     ~ E1 (ptr_addr L p + i) /\ ~ E2 (ptr_addr L p + i)) ->
  relay_post Bm API K E F L A regs mem md L2 A2 regs2' mem2' md2.
Proof using.
  intros K E F L A regs mem md m1 FL FH K1 E1 F1 regs1 L1 A1 regs1' mem1' md1 K2 E2 F2 regs2 L2 A2 regs2' mem2' md2
    HM HW HIMG HFR HFS P1 P2 HRG HS1 HS2 HS3 HE1 HE2 HE2c HF1 HF2 HB.
  destruct P1 as (M1 & W1 & B1 & LY1 & LN1 & PA1 & SV1 & Z01 & OW1 & RG1 & MD1 & BY1 & BK1 & SC1).
  destruct P2 as (M2 & W2 & B2 & LY2 & LN2 & PA2 & SV2 & Z02 & OW2 & RG2 & MD2 & BY2 & BK2 & SC2).
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL. pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  assert (LYA : layout_le A L L2).
  { destruct LY1 as (C1 & S1 & R1 & G1), LY2 as (C2 & S2 & R2 & G2).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite G2 by lia. apply G1. exact Hr. }
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|]. split; [exact LYA|]. split; [lia|].
  split.
  { intros p n Hp _ _. pose proof (ge_ub_prid_lt A p n HW Hp) as Hr. destruct LYA as (_ & _ & _ & G).
    destruct p as [r o]. unfold ptr_addr. cbn [loc_addr]. cbn [prid] in Hr. rewrite G by exact Hr. reflexivity. }
  assert (SVA : forall p n, In (p, n) (user_blocks A) -> 0 < n -> ~ F (ptr_addr L p) -> In (p, n) (user_blocks A1)).
  { intros p n Hp Hn HF. apply SV1; [exact Hp | exact Hn | intro X; apply HF, HF1, X]. }
  split.
  { intros p n Hp Hn HF. pose proof (SVA p n Hp Hn HF) as H1.
    apply SV2; [exact H1 | exact Hn |].
    rewrite (PA1 p n Hp H1 (fun X => HF (HF1 _ X))). exact (HF2 p n Hp Hn HF H1). }
  split.
  { intros p Hp. destruct (Z01 p Hp) as [H1 Q1]. destruct (Z02 p H1) as [H2 Q2]. split; [exact H2 | congruence]. }
  split.
  { intros a Ha Ho. apply OW1; [exact Ha|]. apply OW2; [exact Ha | exact Ho]. }
  split.
  { intros r Hr. rewrite (RG2 r Hr). exact (HRG r Hr). }
  split.
  { destruct MD1 as (v1 & ->). destruct MD2 as (v2 & ->). exists v2. apply ge_with_vmmaps_twice. }
  split.
  { intros a Ha NO NO2 NS NE.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | pose proof (HIMG a Ha); lia]).
    assert (E0 : m1 (Z_to_bv 64 a) = mem (Z_to_bv 64 a))
      by (apply HFR; [exact Ha64 | intro X; exact (NS (proj1 (HFS a X)))]).
    assert (NO1 : ~ owned Bm L1 A1 a).
    { intro X. destruct Ha as [Ha|Ha].
      - pose proof (mr_owned_low _ _ LAWS _ _ _ _ a M1 X). lia.
      - exact (NO (OW1 a Ha X)). }
    destruct (BY1 a Ha NO NO1 (fun X => NS (HS1 a X)) (fun X => NE (HE1 a X))) as [Y1 Z1].
    destruct (BY2 a Ha NO1 NO2 (fun X => NS (HS2 a X)) (fun X => NE (HE2 a Ha X))) as [Y2 Z2].
    split.
    - rewrite Y2, Y1. unfold mbyte. rewrite E0. reflexivity.
    - rewrite <- Z2, <- Z1. unfold writable_at, wview. rewrite E0. tauto. }
  split.
  { intros p n i Hp Hp2 HF Hi NE. destruct (HB p n i Hp Hi HF NE) as (NE1 & NE2).
    assert (Hn : 0 < n) by lia. pose proof (SVA p n Hp Hn HF) as Hp1.
    assert (NF1 : ~ F1 (ptr_addr L p)) by (intro X; apply HF, HF1, X).
    pose proof (BK2 p n i Hp1 Hp2) as X2. rewrite (PA1 p n Hp Hp1 NF1) in X2.
    rewrite (X2 (HF2 p n Hp Hn HF Hp1) Hi NE2).
    rewrite (BK1 p n i Hp Hp1 NF1 Hi NE1).
    destruct (mr_blocks _ _ LAWS L A mem md p n i HM Hp Hi) as (_ & Hlo & Hhi & _).
    unfold mbyte. rewrite HFR; [reflexivity | lia |].
    intro X. destruct (HFS _ X) as [_ Y]. lia. }
  { intros a Ha.
    assert (D : scratch_k Bm K2 regs2 a \/ ~ scratch_k Bm K2 regs2 a) by (unfold scratch_k; lia).
    destruct D as [S2|S2]; [exact (SC2 a S2)|].
    destruct (HS3 a Ha S2) as [S1 Hc].
    assert (NO1 : ~ owned Bm L1 A1 a) by (intro X; pose proof (mr_owned_low _ _ LAWS _ _ _ _ a M1 X); lia).
    assert (NO2 : ~ owned Bm L2 A2 a) by (intro X; pose proof (mr_owned_low _ _ LAWS _ _ _ _ a M2 X); lia).
    destruct (BY2 a (or_introl Hc) NO1 NO2 S2 (HE2c a Hc)) as [_ Z2].
    apply Z2. exact (SC1 a S1). }
Qed.

Lemma ge_img_low : ms_segs Bm = rsegs -> forall a, in_img Bm a -> 0 <= a < 2 ^ 32.
Proof using.
  intros Hs a [_ (s & Hin & Ha)]. rewrite Hs in Hin. pose proof ge_rsv_top as T.
  rewrite forallb_forall in T. specialize (T s Hin). apply Z.leb_le in T.
  pose proof (bv_unsigned_in_range 64 (fst s)). lia.
Qed.

Lemma ge_unch : forall m m' lo hi, munch [(lo, hi)] m m' ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof using.
  intros m m' lo hi MU a Ha Hn. apply MU. cbn [outside]. rewrite unsigned_lit by lia. split; [exact Hn | exact I].
Qed.

Lemma ge_rw_rel : forall segs m m0 A cs, mem_rel segs m m0 -> rw_cells segs m0 A cs -> rw_cells segs m A cs.
Proof using.
  intros segs m m0 A cs HR [[Wf Bt] Wr]. split; [split; [exact Wf|] |].
  - exact (proj2 (bytes_at_rel segs m m0 A _ HR) Bt).
  - exact (wr_at_rel segs m m0 A _ HR Wr).
Qed.

Lemma ge_yk_getr : forall R r, YK11.getr R r = getr R r.
Proof using. reflexivity. Qed.

Lemma ge_off_nz : forall cl br n, n <> 0 -> send_off cl br n = (cl <? 0) || (br =? 1).
Proof using. intros cl br n Hn. unfold send_off. rewrite (proj2 (Z.eqb_neq n 0) Hn). apply orb_false_r. Qed.

Lemma ge_live_nz : forall cl br dd n, n <> 0 -> send_live cl br dd n = negb ((cl <? 0) || (br =? 1)) && (dd =? 0).
Proof using. intros cl br dd n Hn. unfold send_live. rewrite (ge_off_nz cl br n Hn). reflexivity. Qed.

Lemma ge_pw_mid : forall {X} (R : X -> X -> Prop) l1 x l2 y,
  pairwise R (l1 ++ x :: l2) -> In y (l1 ++ l2) -> R y x \/ R x y.
Proof using.
  intros X R l1. induction l1 as [|a l1 IH]; intros x l2 y Hp Hy; cbn [app pairwise] in Hp, Hy.
  - destruct Hp as [Hp _]. right. apply Hp. exact Hy.
  - destruct Hp as [Ha Ht]. destruct Hy as [<- | Hy].
    + left. apply Ha. apply in_or_app. right. left. reflexivity.
    + exact (IH x l2 y Ht Hy).
Qed.

Lemma ge_pw_unique : forall l1 x l2, pairwise ranges_disjoint (l1 ++ x :: l2) -> 0 < snd x -> ~ In x (l1 ++ l2).
Proof using.
  intros l1 x l2 Hp Hx Hin. destruct (ge_pw_mid _ l1 x l2 x Hp Hin) as [D|D]; unfold ranges_disjoint in D; lia.
Qed.

Lemma ge_pw_apart : forall l1 x l2 y, pairwise ranges_disjoint (l1 ++ x :: l2) -> In y (l1 ++ l2) ->
  fst y + snd y <= fst x \/ fst x + snd x <= fst y.
Proof using.
  intros l1 x l2 y Hp Hy. destruct (ge_pw_mid _ l1 x l2 y Hp Hy) as [D|D]; unfold ranges_disjoint in D; lia.
Qed.

Lemma ge_split_unique : forall {X} (l1 l2 l3 l4 : list X) x,
  l1 ++ x :: l2 = l3 ++ x :: l4 -> ~ In x l1 -> ~ In x l3 -> l1 = l3 /\ l2 = l4.
Proof using.
  intros X l1. induction l1 as [|a l1 IH]; intros l2 l3 l4 x E N1 N3; destruct l3 as [|b l3]; cbn [app] in E.
  - injection E as E. split; [reflexivity | exact E].
  - injection E as E1 E2. exfalso. apply N3. left. symmetry. exact E1.
  - injection E as E1 E2. exfalso. apply N1. left. exact E1.
  - injection E as E1 E2. subst b.
    destruct (IH l2 l3 l4 x E2 (fun Hn => N1 (or_intror Hn)) (fun Hn => N3 (or_intror Hn))) as [-> ->].
    split; reflexivity.
Qed.

Lemma ge_in_drop : forall (l1 l2 : list (Z * Z)) o c q m, In (q, m) (l1 ++ (o, c) :: l2) -> q <> o -> In (q, m) (l1 ++ l2).
Proof using.
  intros l1 l2 o c q m Hin Hq. apply in_app_iff in Hin. apply in_app_iff.
  destruct Hin as [Hin | [E | Hin]]; [left; exact Hin | injection E as E1 E2; congruence | right; exact Hin].
Qed.

Lemma ge_bytes_mbyte : forall segs m m' a bs, bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) -> bytes_at segs m' a bs.
Proof using.
  intros segs m m' a bs (H0 & H1 & H2) HE. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H2 i Hi). exact (HE (Z.of_nat i) ltac:(lia)).
Qed.

Lemma ge_rw_mbyte : forall segs m m' a cs, rw_cells segs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     mbyte segs m' (a + i) = mbyte segs m (a + i) /\ (writable_at segs m (a + i) <-> writable_at segs m' (a + i))) ->
  rw_cells segs m' a cs.
Proof using.
  intros segs m m' a cs [[Wf Bt] (W0 & W1 & W2)] HE. split; [split; [exact Wf|] |].
  - apply (ge_bytes_mbyte segs m m' a _ Bt). intros i Hi. rewrite (cells_bytes_length _ Wf) in Hi. exact (proj1 (HE i Hi)).
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. apply (proj2 (HE i Hi)). exact (W2 i Hi).
Qed.

Lemma ge_blocks_in : forall L A q k, In (q, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = q.
Proof using.
  intros L A q k Hin. unfold blocks in Hin. apply in_map_iff in Hin. destruct Hin as ([p k0] & E & Hin).
  cbn [fst snd] in E. injection E as E1 E2. subst. exists p. split; [exact Hin | reflexivity].
Qed.

Lemma ge_blocks_of : forall L A p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A).
Proof using. intros L A p n Hin. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (p, n) Hin). Qed.

Lemma ge_rp_bytes : forall K E F L A regs mem md L' A' regs' mem' md' p n a bs,
  relay_post Bm API K E F L A regs mem md L' A' regs' mem' md' ->
  In (p, n) (user_blocks A) -> 0 < n -> ~ F (ptr_addr L p) ->
  ptr_addr L p <= a -> a + Z.of_nat (length bs) <= ptr_addr L p + n ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ E (a + i)) ->
  bytes_at (ms_segs Bm) mem a bs ->
  bytes_at (ms_segs Bm) mem' a bs /\ In (p, n) (user_blocks A') /\ ptr_addr L' p = ptr_addr L p.
Proof using.
  intros K E F L A regs mem md L' A' regs' mem' md' p n a bs RP Hp Hn HF Ha1 Ha2 HE HB.
  destruct RP as (_ & _ & _ & _ & _ & PA & SV & _ & _ & _ & _ & _ & BK & _).
  assert (Hp' : In (p, n) (user_blocks A')) by (apply SV; assumption).
  split; [| split; [exact Hp' | exact (PA p n Hp Hp' HF)]].
  apply (ge_bytes_mbyte _ mem mem' a bs HB). intros i Hi.
  replace (a + i) with (ptr_addr L p + (a - ptr_addr L p + i)) by lia.
  apply (BK p n (a - ptr_addr L p + i) Hp Hp' HF); [lia|].
  replace (ptr_addr L p + (a - ptr_addr L p + i)) with (a + i) by lia. exact (HE i Hi).
Qed.

Definition ge_hide (P : Prop) : Prop := P.

Ltac ge_hide_hyp H := let T := type of H in change (ge_hide T) in H.

Lemma ge_cs_enum : forall z, callee_saved z -> z <> 2 -> z <> 8 ->
  z = 3 \/ z = 4 \/ z = 9 \/ z = 18 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/
  z = 25 \/ z = 26 \/ z = 27.
Proof using. intros z Hz N2 N8. unfold callee_saved in Hz. lia. Qed.

Theorem gesture_end_holds (F : ResFormT) : strlen_contract -> send_line_contract Bm API F ->
  gesture_end_contract Bm API F.
Proof using NODUP.
  intros SLEN SL. unfold gesture_end_contract.
  intros L A regs mem md bnd x slack O junk cl br dd ei mx nout cap out ev.
  cbv zeta.
  intros Hseg CP INIT HTP ERRM HERR RO HX NZ PAD XL1 SEPR SEPE SEPS IMR IMC IME IM5 KEY Hcl Hbr Hdd Hei
    CCL CBR CDD CEI COUT CERR HOB HMG RES ROOM.
  ge_hide_hyp SEPR. ge_hide_hyp SEPE. ge_hide_hyp SEPS. ge_hide_hyp Hcl. ge_hide_hyp Hbr. ge_hide_hyp Hdd.
  ge_hide_hyp Hei. ge_hide_hyp HOB.
  unfold GESTURE_END_K, SEND_LINE_K, GESTURE_END_FRAME, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in *.
  destruct CP as (HM & HWF & HBD & HRA & HAL & HSPL & HSPH & HWST & HTPR & HWER & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
  set (S := bv_unsigned (getr regs 2)) in *.
  set (H := bv_unsigned (getr regs 10)) in *.
  assert (ESP : spZ regs = S) by reflexivity.
  rewrite ESP in HAL, HSPL, HSPH, HWST.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RSP. change (bv_unsigned (getr regs 2)) with S in RSP.
  unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ HX) as XB. rewrite length_app in XB. cbn [length] in XB.
  assert (RO' : ro_agree rsegs mem) by (rewrite <- Hseg; exact RO).
  assert (HX' : bytes_at rsegs mem H (x ++ Z_to_bv 8 0 :: slack)) by (rewrite <- Hseg; exact HX).
  assert (STK : stk rsegs (normalize rsegs mem) (S - (16 + (112 + (8192 + 64)))) S).
  { apply ge_stk_norm; [lia | lia |]. intros a Ha. rewrite <- Hseg. exact (HWST a Ha). }
  pose proof (ge_head SLEN (reg_get regs 1) (getr regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
    (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (getr regs 10) (reg_get regs 11)
    (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17)
    (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
    (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29)
    (reg_get regs 30) (reg_get regs 31) fp_regs fp_csr (normalize rsegs mem) _ x slack STK ltac:(lia)
    (mem_inv_normalize rsegs mem) (bytes_at_normalize rsegs mem _ _ RO' HX') NZ PAD
    ltac:(unfold ge_hide in SEPS; lia)) as RUN0.
  pose proof (evt_normalize rsegs _ _ _ _ _ _ mem (seg_rom rsegs) ge_wx RO' RUN0) as RUN1.
  clear RUN0.
  match type of RUN1 with Exec.evt _ ?Q _ => set (Q1 := Q) in RUN1 end.
  assert (RUN2 : Exec.evt (ms_segs Bm) Q1
                   (RegisterBridge.canonical_register_state
                      (YK11.mkst regs (Z_to_bv 64 GESTURE_END) mem (seg_rom (ms_segs Bm))))).
  { rewrite Hseg. exact RUN1. }
  clear RUN1.
  eapply evt_SR_canon; [exact RUN2 | exact Hh | exact Hl |].
  intros ms1 (can1 & Q1c & EQV1). unfold Q1 in Q1c. clear RUN2 Q1.
  destruct Q1c as (s0 & (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1n &
    E0 & MU0 & WM0 & MI0 & FR0) & REL & ROS).
  subst s0.
  destruct (ge_shape1 rsegs _ _ _ _ _ _ REL EQV1) as (E1 & X1 & MR1 & MEQ).
  rewrite MEQ in ROS.
  set (regs1 := ms_regs ms1) in *. set (m1 := ms_mem ms1) in *.
  rewrite E1. rewrite <- Hseg.
  change (bv_unsigned (getr regs 2)) with S in MU0, FR0, X1.
  assert (G1 : getr regs1 1 = Z_to_bv 64 0x14d3c) by (rewrite (ge_getr_x _ _ _ X1); reflexivity).
  assert (G2 : getr regs1 2 = Z_to_bv 64 (S + -16)) by (rewrite (ge_getr_x _ _ _ X1); reflexivity).
  assert (G4 : getr regs1 4 = getr regs 4) by (rewrite (ge_getr_x _ _ _ X1); reflexivity).
  assert (G8 : getr regs1 8 = getr regs 10) by (rewrite (ge_getr_x _ _ _ X1); reflexivity).
  assert (G10 : getr regs1 10 = getr regs 10) by (rewrite (ge_getr_x _ _ _ X1); reflexivity).
  assert (G11 : getr regs1 11 = Z_to_bv 64 (Z.of_nat (length x))) by (rewrite (ge_getr_x _ _ _ X1); reflexivity).
  assert (GCS : forall z, callee_saved z -> z <> 2 -> z <> 8 -> getr regs1 (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z)).
  { intros z Hz N2 N8. rewrite (ge_getr_x _ _ _ X1).
    pose proof (ge_cs_enum z Hz N2 N8) as Hz'.
    repeat (destruct Hz' as [-> | Hz']; [reflexivity|]). rewrite Hz'. reflexivity. }
  clear X1 REL.
  pose proof (mem_rel_normalize rsegs mem RO') as MRN.
  pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m1 m1n MRN MR1 ROS MU0) as MU1.
  pose proof (wmono_rel rsegs mem (normalize rsegs mem) m1 m1n MRN MR1 ROS WM0) as WM1.
  pose proof (ge_rw_rel rsegs m1 m1n _ _ MR1 FR0) as FR1.
  pose proof (ro_agree_same rsegs mem m1 RO' ROS) as RO1.
  pose proof (ge_unch mem m1 _ _ MU1) as UNCH.
  clear MU0 WM0 MI0 FR0 MR1 MRN.
  pose proof (ge_img_low Hseg) as IMGL.
  assert (IERR : 0 <= errno_addr Bm < 2 ^ 32) by (apply IMGL, IME; lia).
  assert (IERR4 : errno_addr Bm + 4 <= 2 ^ 32)
    by (pose proof (IMGL (errno_addr Bm + 3) (IME (errno_addr Bm + 3) ltac:(lia))); lia).
  assert (SLO : 2 ^ 32 + 16 <= S - (16 + (112 + (8192 + 64)))) by lia.
  rewrite Hseg in CCL, CBR, CDD, CEI, COUT, CERR.
  assert (TR : forall A0 cs, rw_cells rsegs mem A0 cs -> 0 <= A0 -> A0 + Z.of_nat (cells_size cs) <= 2 ^ 32 ->
                 rw_cells rsegs m1 A0 cs).
  { intros A0 cs Hc H0 H1. apply (rw_cells_transport rsegs _ mem m1 A0 cs Hc MU1 WM1).
    cbn [disjoint_from]. split; [lia | exact I]. }
  pose proof (TR _ _ CCL ltac:(unfold G_CLIENT; lia) ltac:(unfold G_CLIENT; cbn [cells_size csize]; lia)) as CCL1.
  pose proof (TR _ _ CBR ltac:(unfold G_BROKEN; lia) ltac:(unfold G_BROKEN; cbn [cells_size csize]; lia)) as CBR1.
  pose proof (TR _ _ CDD ltac:(unfold G_DEAD; lia) ltac:(unfold G_DEAD; cbn [cells_size csize]; lia)) as CDD1.
  pose proof (TR _ _ CEI ltac:(unfold G_EINTR; lia) ltac:(unfold G_EINTR; cbn [cells_size csize]; lia)) as CEI1.
  pose proof (TR _ _ COUT ltac:(unfold G_OUTV; lia) ltac:(unfold G_OUTV; cbn [cells_size csize]; lia)) as COUT1.
  pose proof (TR _ _ CERR ltac:(lia) ltac:(cbn [cells_size csize]; lia)) as CERR1.
  assert (BX1 : bytes_at rsegs m1 H x).
  { pose proof HX' as T. apply bytes_at_app in T.
    apply (bytes_at_transport rsegs _ mem m1 H x (proj1 T) MU1). cbn [disjoint_from].
    split; [unfold ge_hide in SEPS; lia | exact I]. }
  assert (BZ1 : bytes_at rsegs m1 (H + Z.of_nat (length x)) [Z_to_bv 8 0]).
  { pose proof HX' as T. apply bytes_at_app in T. destruct T as [_ T].
    change (Z_to_bv 8 0 :: slack) with ([Z_to_bv 8 0] ++ slack) in T. apply bytes_at_app in T.
    apply (bytes_at_transport rsegs _ mem m1 _ _ (proj1 T) MU1). cbn [disjoint_from length].
    split; [unfold ge_hide in SEPS; lia | exact I]. }
  assert (HOB1 : (bv_unsigned cap = 0 /\ bv_unsigned out = 0 /\ bv_unsigned nout = 0 /\ O = []) \/
     (0 < bv_unsigned cap /\ bv_unsigned nout <= bv_unsigned cap /\ In (bv_unsigned out, bv_unsigned cap) (blocks L A) /\
      fresh_block Bm (bv_unsigned out) (bv_unsigned cap) /\ bytes_at (ms_segs Bm) m1 (bv_unsigned out) (O ++ junk) /\
      Z.of_nat (length O) = bv_unsigned nout /\ Z.of_nat (length junk) = bv_unsigned cap - bv_unsigned nout /\
      (H + Z.of_nat (length x) <= bv_unsigned out \/ bv_unsigned out + bv_unsigned cap <= H))).
  { unfold ge_hide in HOB. destruct HOB as [HOB | (C0 & C1 & C2 & C3 & C4 & C5 & CJ & C6)]; [left; exact HOB | right].
    destruct C3 as (F0 & F1 & F2).
    split; [exact C0|]. split; [exact C1|]. split; [exact C2|]. split; [split; [exact F0|]; split; [exact F1 | exact F2]|].
    split; [| split; [exact C5 | split; [exact CJ | lia]]].
    rewrite Hseg. rewrite Hseg in C4.
    apply (bytes_at_transport rsegs _ mem m1 _ _ C4 MU1). cbn [disjoint_from]. rewrite length_app. split; [lia | exact I]. }
  ge_hide_hyp HOB1.
  assert (CP1 : call_pre_k Bm (aa_MR API) (112 + (8192 + 64)) L A regs1 m1 md).
  { split.
    { apply (mr_frame _ _ (aa_laws API) L A mem m1 md md HM).
      - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho).
        unfold mbyte. rewrite UNCH by lia. reflexivity.
      - intros a Ho [b Hb]. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho).
        exists b. rewrite UNCH by lia. exact Hb.
      - intros p n i Hp Hi. destruct (mr_blocks _ _ (aa_laws API) L A mem md p n i HM Hp Hi) as ([b Hb] & B0 & B1 & _).
        exists b. rewrite UNCH by lia. exact Hb.
      - reflexivity.
      - exact Hh.
      - exact Hl.
      - exact Hmat. }
    split; [exact HWF|]. split; [exact HBD|].
    split. { change (YK11.getr regs1 1) with (getr regs1 1). rewrite G1. reflexivity. }
    assert (SP1 : spZ regs1 = S + -16).
    { unfold spZ. change (YK11.getr regs1 2) with (getr regs1 2). rewrite G2. apply unsigned_lit. lia. }
    rewrite SP1.
    split; [lia|]. split; [lia|]. split; [lia|].
    split. { intros a Ha. rewrite Hseg. apply WM1. rewrite <- Hseg. apply HWST. lia. }
    split. { change (YK11.getr regs1 4) with (getr regs1 4). rewrite G4. exact HTPR. }
    split. { intros a Ha. rewrite Hseg. apply WM1. rewrite <- Hseg. exact (HWER a Ha). }
    intros X. rewrite INIT in X. discriminate X. }
  assert (KEY' : exists q k, In (q, k) (blocks L A) /\ q <= H /\ H + Z.of_nat (length x) <= q + k /\ q <> bv_unsigned out).
  { destruct KEY as (q & k & Hq & _ & Q1 & Q2 & Q3). exists q, k. split; [exact Hq|]. split; [exact Q1|]. split; [lia | exact Q3]. }
  assert (ROOM1 : forall qs, length qs = nretF (send_line_tr (send_live cl br dd (Z.of_nat (length x))) (bv_unsigned mx)
                    (bv_unsigned nout) (bv_unsigned cap) (Z.of_nat (length x)) 0 (known_at L A (bv_unsigned out))) ->
                  roomF F qs bnd (send_line_tr (send_live cl br dd (Z.of_nat (length x))) (bv_unsigned mx)
                    (bv_unsigned nout) (bv_unsigned cap) (Z.of_nat (length x)) 0 (known_at L A (bv_unsigned out)))).
  { pose proof (ge_room1 F bnd _ _ _ _ _ L A (bv_unsigned out) ROOM) as R.
    rewrite (ge_live_nz cl br dd (Z.of_nat (length x))) by lia.
    rewrite (ge_live_nz cl br dd (Z.of_nat (length x) + 5)) in R by lia. exact R. }
  pose proof (SL L A regs1 m1 md bnd x O junk cl br dd ei mx nout cap out ev) as SL1.
  cbv zeta in SL1. unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in SL1.
  rewrite G1, G2, G10, G11 in SL1. change (bv_unsigned (getr regs 10)) with H in SL1.
  rewrite (unsigned_lit (Z.of_nat (length x))) in SL1 by lia. rewrite (unsigned_lit (S + -16)) in SL1 by lia.
  specialize (SL1 Hseg CP1 INIT HTP ERRM HERR ltac:(rewrite Hseg; exact RO1) ltac:(rewrite Hseg; exact BX1) eq_refl
    ltac:(unfold ge_hide in SEPR; lia) ltac:(unfold ge_hide in SEPE; lia) ltac:(unfold ge_hide in SEPS; lia)
    IMR IMC IME (or_intror KEY') Hcl Hbr Hdd Hei
    ltac:(rewrite Hseg; exact CCL1) ltac:(rewrite Hseg; exact CBR1) ltac:(rewrite Hseg; exact CDD1)
    ltac:(rewrite Hseg; exact CEI1) ltac:(rewrite Hseg; exact COUT1) ltac:(rewrite Hseg; exact CERR1)
    HOB1 ltac:(lia) RES ROOM1).
  eapply SR_bind; [exact SL1 |]. clear SL1.
  intros c2 POST1.
  destruct POST1 as (L1 & A1 & regs1' & mem1' & md1 & OUT1 & CAP1 & junk1 & EC2 & RP1 & INIT1 & RES1 &
    RO2 & BX2 & CCL2 & CBR2 & CDD2 & CEI2 & NL1 & LV1).
  subst c2.
  pose proof RP1 as RP1c.
  destruct RP1c as (MA1 & WA1 & BA1 & LY1 & LN1 & PA1 & SV1 & Z1 & OW1 & RG1 & MD1 & BY1 & BK1 & SC1).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ MA1) as (Hh1 & Hl1 & Hmat1).
  assert (SPR1 : spZ regs1 = S + -16).
  { unfold spZ. rewrite ge_yk_getr, G2. apply unsigned_lit. lia. }
  assert (FR2 : rw_cells rsegs mem1' (S + -16) [C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (ge_rw_mbyte rsegs m1 mem1' _ _ FR1). intros i Hi. cbn [cells_size csize Nat.add] in Hi. rewrite <- Hseg.
    apply BY1.
    - left. lia.
    - intro X. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM X). lia.
    - intro X. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ MA1 X). lia.
    - unfold scratch_k. rewrite SPR1. lia.
    - unfold send_writes. unfold G_BROKEN, G_EINTR, G_OUTV.
      intros [X | [X | [X | (_ & X)]]]; try lia.
      unfold ge_hide in HOB. destruct HOB as [(C0 & _) | (_ & _ & _ & (_ & F1 & _) & _)]; lia. }
  assert (SP2 : reg_get regs1' 2 = Z_to_bv 64 (S + -16)).
  { pose proof (RG1 2 ltac:(unfold callee_saved; lia)) as X. rewrite !ge_yk_getr in X. exact (eq_trans X G2). }
  pose proof (ge_tail (reg_get regs1' 1) (reg_get regs1' 2) (reg_get regs1' 3) (reg_get regs1' 4) (reg_get regs1' 5)
    (reg_get regs1' 6) (reg_get regs1' 7) (reg_get regs1' 8) (reg_get regs1' 9) (reg_get regs1' 10)
    (reg_get regs1' 11) (reg_get regs1' 12) (reg_get regs1' 13) (reg_get regs1' 14) (reg_get regs1' 15)
    (reg_get regs1' 16) (reg_get regs1' 17) (reg_get regs1' 18) (reg_get regs1' 19) (reg_get regs1' 20)
    (reg_get regs1' 21) (reg_get regs1' 22) (reg_get regs1' 23) (reg_get regs1' 24) (reg_get regs1' 25)
    (reg_get regs1' 26) (reg_get regs1' 27) (reg_get regs1' 28) (reg_get regs1' 29) (reg_get regs1' 30)
    (reg_get regs1' 31) fp_regs fp_csr mem1' (S + -16) (reg_get regs 8) (reg_get regs 1) SP2 ltac:(lia) ltac:(lia)
    FR2) as RUN3.
  match type of RUN3 with Exec.evt _ ?Q _ => set (Q3 := Q) in RUN3 end.
  assert (RUN4 : Exec.evt (ms_segs Bm) Q3
                   (RegisterBridge.canonical_register_state
                      (YK11.mkst regs1' (Z_to_bv 64 0x14d3c) mem1' (seg_rom (ms_segs Bm))))).
  { rewrite Hseg. exact RUN3. }
  clear RUN3.
  eapply evt_SR_canon; [exact RUN4 | exact Hh1 | exact Hl1 |].
  intros ms3 (can3 & Q3c & EQV3). unfold Q3 in Q3c. clear RUN4 Q3. subst can3.
  destruct (ge_shape3 _ _ _ _ _ EQV3) as (E3 & X3).
  set (regs2 := ms_regs ms3) in *.
  rewrite E3. rewrite <- Hseg.
  assert (H1' : getr regs2 1 = getr regs 1) by (rewrite (ge_getr_x _ _ _ X3); reflexivity).
  assert (H2' : getr regs2 2 = Z_to_bv 64 (S + -16 + 16)) by (rewrite (ge_getr_x _ _ _ X3); reflexivity).
  assert (H10' : getr regs2 10 = Z_to_bv 64 END5_ADDR) by (rewrite (ge_getr_x _ _ _ X3); reflexivity).
  assert (H11' : getr regs2 11 = Z_to_bv 64 5) by (rewrite (ge_getr_x _ _ _ X3); reflexivity).
  assert (H4' : getr regs2 4 = getr regs1' 4) by (rewrite (ge_getr_x _ _ _ X3); reflexivity).
  assert (RGP : regs_preserved regs regs2).
  { intros r Hr. rewrite !ge_yk_getr. rewrite (ge_getr_x _ _ _ X3).
    destruct (Z.eq_dec r 2) as [-> | N2].
    { transitivity (Z_to_bv 64 (S + -16 + 16)); [reflexivity|].
      replace (S + -16 + 16) with S by lia. exact (Z_to_bv_bv_unsigned (getr regs 2)). }
    destruct (Z.eq_dec r 8) as [-> | N8]; [reflexivity|].
    transitivity (getr regs1' (Z_to_bv 5 r)).
    { pose proof (ge_cs_enum r Hr N2 N8) as Hz'.
      repeat (destruct Hz' as [-> | Hz']; [reflexivity|]). rewrite Hz'. reflexivity. }
    rewrite <- ge_yk_getr, (RG1 r Hr), ge_yk_getr. exact (GCS r Hr N2 N8). }
  clear X3 EQV3.
  assert (XL0 : Z.of_nat (length x) <> 0) by lia.
  assert (LEN0 : Z.of_nat (length x) + 5 <> 0) by lia.
  rewrite (ge_live_nz cl br dd _ XL0) in RP1, NL1, LV1, PA1, SV1, BY1, BK1, RES1.
  rewrite (ge_live_nz cl br dd _ LEN0) in ROOM.
  rewrite (ge_off_nz cl br _ XL0) in CBR2, CEI2, NL1.
  rewrite (ge_live_nz cl br dd _ LEN0), !(ge_off_nz cl br _ LEN0).
  destruct KEY as (q & kk & Hq & FQ & Q1 & Q2 & Q3). clear KEY'.
  destruct (ge_blocks_in L A q kk Hq) as (pk & Hpk & Epk).
  assert (Kpos : 0 < kk) by lia.
  pose proof FQ as [FQ0 [FQ1 FQ2]].
  pose proof (bv_unsigned_in_range 64 nout) as RNO. unfold bv_modulus in RNO. cbn in RNO.
  assert (GIMG : forall a, G_BROKEN <= a < G_BROKEN + 1 \/ G_EINTR <= a < G_EINTR + 1 \/ G_OUTV + 8 <= a < G_OUTV + 32 ->
                 in_img Bm a).
  { intros a Ha. apply (proj1 (IMR a ltac:(unfold G_BROKEN, G_EINTR, G_OUTV, G_RELAY_LO, G_RELAY_HI in *; lia))). }
  assert (KO : bv_unsigned cap = 0 \/ q + kk <= bv_unsigned out \/ bv_unsigned out + bv_unsigned cap <= q).
  { unfold ge_hide in HOB. destruct HOB as [(C0 & _) | (_ & _ & C2 & _)]; [left; exact C0 | right].
    exact (blocks_disjoint Bm API L A mem md q kk _ _ HM Hq C2 Q3). }
  ge_hide_hyp KO.
  assert (KNE : forall lv' a, q <= a < q + kk -> ~ send_writes lv' (bv_unsigned out) (bv_unsigned cap) a).
  { intros lv' a Ha [X | [X | [X | (_ & X)]]];
      [ apply (FQ2 (a - q) ltac:(lia)); replace (q + (a - q)) with a by lia; apply GIMG; tauto .. |
        unfold ge_hide in KO; lia ]. }
  assert (BK0 : bytes_at (ms_segs Bm) m1 H (x ++ [Z_to_bv 8 0]))
    by (rewrite Hseg; apply bytes_at_app; split; [exact BX1 | exact BZ1]).
  destruct (ge_rp_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ pk kk H (x ++ [Z_to_bv 8 0]) RP1 Hpk Kpos
     ltac:(rewrite Epk; intros [_ X]; exact (Q3 X)) ltac:(rewrite Epk; lia)
     ltac:(rewrite Epk, length_app; cbn [length]; lia)
     ltac:(intros i Hi; apply KNE; rewrite length_app in Hi; cbn [length] in Hi; lia) BK0) as (BK1' & Hpk1 & Epk1).
    assert (SPR2 : spZ regs2 = S).
    { unfold spZ. rewrite ge_yk_getr, H2'. rewrite unsigned_lit by lia. lia. }
    assert (FRW : forall a, S + -16 <= a < S -> writable_at (ms_segs Bm) mem1' a).
    { intros a Ha.
      apply (proj2 (BY1 a ltac:(left; lia)
               ltac:(intro X; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM X); lia)
               ltac:(intro X; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a MA1 X); lia)
               ltac:(unfold scratch_k; rewrite SPR1; lia)
               ltac:(unfold send_writes, G_BROKEN, G_EINTR, G_OUTV; intros [X | [X | [X | (_ & X)]]];
                     [lia | lia | lia | unfold ge_hide in HOB;
                      destruct HOB as [(C0 & _) | (_ & _ & _ & (_ & F1' & _) & _)]; lia]))).
      rewrite Hseg. apply WM1. rewrite <- Hseg. apply HWST. lia. }
    assert (CP2 : call_pre_k Bm (aa_MR API) (112 + (8192 + 64)) L1 A1 regs2 mem1' md1).
    { split; [exact MA1|]. split; [exact WA1|]. split; [exact BA1|].
      split. { rewrite ge_yk_getr, H1', <- ge_yk_getr. exact HRA. }
      rewrite SPR2. split; [lia|]. split; [lia|]. split; [lia|].
      split.
      { intros a Ha. destruct (Z_lt_le_dec a (S + -16)) as [Hlt | Hge].
        - apply SC1. unfold scratch_k. rewrite SPR1. left. lia.
        - apply FRW. lia. }
      split.
      { transitivity (getr regs1' 4); [rewrite ge_yk_getr; exact H4'|].
        transitivity (getr regs1 4); [exact (RG1 4 ltac:(unfold callee_saved; lia))|].
        rewrite G4. exact HTPR. }
      split. { intros a Ha. apply SC1. unfold scratch_k. right. exact Ha. }
      intros X. rewrite INIT1 in X. discriminate X. }
    assert (E5M : bytes_at (ms_segs Bm) mem1' END5_ADDR END5)
      by (rewrite Hseg; apply ge_end5; rewrite <- Hseg; exact RO2).
  set (lv := negb ((cl <? 0) || (br =? 1)) && (dd =? 0)) in *.
  assert (ELV : lv = negb ((cl <? 0) || (br =? 1)) && (dd =? 0)) by reflexivity.
  clearbody lv.
  assert (HS1 : forall a, scratch_k Bm (112 + (8192 + 64)) regs1 a -> scratch_k Bm (16 + (112 + (8192 + 64))) regs a).
  { unfold scratch_k. rewrite SPR1, ESP. intros a [X|X]; [left; lia | right; exact X]. }
  assert (HS2 : forall a, scratch_k Bm (112 + (8192 + 64)) regs2 a -> scratch_k Bm (16 + (112 + (8192 + 64))) regs a).
  { unfold scratch_k. rewrite SPR2, ESP. intros a [X|X]; [left; lia | right; exact X]. }
  assert (HS3 : forall a, scratch_k Bm (16 + (112 + (8192 + 64))) regs a -> ~ scratch_k Bm (112 + (8192 + 64)) regs2 a ->
                scratch_k Bm (112 + (8192 + 64)) regs1 a /\ YM05.alloc_ceiling <= a < 2 ^ 64).
  { unfold scratch_k. rewrite SPR1, SPR2, ESP. intros a [X|X] N; [| exfalso; apply N; right; exact X].
    split; [left; lia | lia]. }
  assert (HFS : forall a, S + -16 <= a < S -> scratch_k Bm (16 + (112 + (8192 + 64))) regs a /\ YM05.alloc_ceiling <= a).
  { intros a Ha. split; [unfold scratch_k; rewrite ESP; left; lia | lia]. }
  assert (HIMG' : forall a, in_img Bm a -> 0 <= a < YM05.alloc_ceiling) by (intros a Ha; pose proof (IMGL a Ha); lia).
  destruct lv.
  { assert (cl = 3 /\ br = 0 /\ dd = 0) as (-> & -> & ->)
      by (unfold ge_hide in Hcl, Hbr, Hdd; destruct Hcl as [-> | ->], Hbr as [-> | ->], Hdd as [-> | ->];
          vm_compute in ELV; first [discriminate ELV | lia]).
    specialize (LV1 eq_refl).
    destruct RES1 as (qs1 & LQ1 & RT1 & LA1). specialize (LA1 eq_refl).
    pose proof (NODUP L1 A1 mem1' md1 MA1) as ND1.
    destruct LV1 as (LC1 & ECAP1 & FB1 & (ev2 & CERR2) & QN1 & (b1 & b2 & c1 & c2 & SH1 & SH2 & SH3) &
      BO1 & JL1 & COUT2).
    pose proof FB1 as [FB10 [FB11 FB12]].
    assert (O1IN : In (OUT1, CAP1) (blocks L1 A1)) by (rewrite SH1; apply in_or_app; right; left; reflexivity).
    assert (QO1 : q <> OUT1) by exact (QN1 q kk Hq Q3 Kpos).
    assert (Hq1 : In (q, kk) (blocks L1 A1)) by (rewrite <- Epk, <- Epk1; apply ge_blocks_of; exact Hpk1).
    pose proof (blocks_disjoint Bm API L1 A1 mem1' md1 q kk OUT1 CAP1 MA1 Hq1 O1IN QO1) as KO1. ge_hide_hyp KO1.
    assert (LO : Z.of_nat (length O) = bv_unsigned nout)
      by (unfold ge_hide in HOB; destruct HOB as [(_ & _ & C & ->) | (_ & _ & _ & _ & _ & C & _)];
          [cbn [length]; lia | exact C]).
    pose proof (SL L1 A1 regs2 mem1' md1
                  (runF F qs1 bnd (send_line_tr true (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap)
                     (Z.of_nat (length x)) 0 (known_at L A (bv_unsigned out)))) END5 (O ++ x) junk1 3 0 0 0 mx
                  (Z_to_bv 64 (bv_unsigned nout + Z.of_nat (length x))) (Z_to_bv 64 CAP1) (Z_to_bv 64 OUT1) ev2) as SL2.
    cbv zeta in SL2. unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in SL2.
    rewrite H1', H2', H10', H11' in SL2.
    rewrite (unsigned_lit (S + -16 + 16)) in SL2 by lia.
    rewrite (unsigned_lit END5_ADDR) in SL2 by (unfold END5_ADDR; lia).
    rewrite (unsigned_lit 5) in SL2 by lia.
    rewrite (unsigned_lit (bv_unsigned nout + Z.of_nat (length x))) in SL2 by lia.
    rewrite (unsigned_lit CAP1) in SL2 by lia.
    rewrite (unsigned_lit OUT1) in SL2 by lia.
    assert (OE5 : END5_ADDR + 5 <= OUT1 \/ OUT1 + CAP1 <= END5_ADDR).
    { destruct (Z_le_gt_dec (END5_ADDR + 5) OUT1) as [Y|Y]; [left; exact Y|].
      destruct (Z_le_gt_dec (OUT1 + CAP1) END5_ADDR) as [Y'|Y']; [right; exact Y'|]. exfalso.
      apply (FB12 (Z.max OUT1 END5_ADDR - OUT1) ltac:(lia)).
      replace (OUT1 + (Z.max OUT1 END5_ADDR - OUT1)) with (Z.max OUT1 END5_ADDR) by lia.
      apply (proj1 (IM5 (Z.max OUT1 END5_ADDR) ltac:(lia))). }
    assert (BO1' : bytes_at (ms_segs Bm) mem1' OUT1 ((O ++ x) ++ junk1)) by (rewrite <- app_assoc; exact BO1).
    assert (LOX : Z.of_nat (length (O ++ x)) = bv_unsigned nout + Z.of_nat (length x)) by (rewrite length_app; lia).
    assert (HOB2L : 0 < CAP1 /\ bv_unsigned nout + Z.of_nat (length x) <= CAP1 /\ In (OUT1, CAP1) (blocks L1 A1) /\
      fresh_block Bm OUT1 CAP1 /\ bytes_at (ms_segs Bm) mem1' OUT1 ((O ++ x) ++ junk1) /\
      Z.of_nat (length (O ++ x)) = bv_unsigned nout + Z.of_nat (length x) /\
      Z.of_nat (length junk1) = CAP1 - (bv_unsigned nout + Z.of_nat (length x)) /\
      (END5_ADDR + 5 <= OUT1 \/ OUT1 + CAP1 <= END5_ADDR)).
    { split; [lia|]. split; [exact LC1|]. split; [exact O1IN|]. split; [exact FB1|]. split; [exact BO1'|].
      split; [exact LOX|]. split; [lia | exact OE5]. }
    pose proof (ge_room2 F bnd (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) (Z.of_nat (length x)) L A
                  (bv_unsigned out) L1 A1 OUT1 CAP1 qs1 ND1 LQ1 LA1 ECAP1 ROOM) as ROOM2.
    specialize (SL2 Hseg CP2 INIT1 HTP ERRM HERR RO2 E5M eq_refl
      ltac:(unfold END5_ADDR, G_RELAY_LO; lia) ltac:(unfold END5_ADDR, G_RELAY_HI in *; lia) ltac:(unfold END5_ADDR; lia)
      IMR IMC IME (or_introl IM5) (or_introl eq_refl) (or_introl eq_refl) (or_introl eq_refl) (or_introl eq_refl)
      CCL2 CBR2 CDD2 CEI2 COUT2 CERR2 (or_intror HOB2L) ltac:(lia) RT1 ROOM2).
    eapply SR_bind; [exact SL2 |]. clear SL2. intros c3 POST2.
    destruct POST2 as (L2 & A2 & regs2' & mem2' & md2 & OUT2 & CAP2 & junk2 & EC3 & RP2 & INIT2 & RES2 &
      RO3 & BE3 & CCL3 & CBR3 & CDD3 & CEI3 & NL2 & LV2).
    subst c3.
    specialize (LV2 eq_refl).
    destruct LV2 as (LC2 & ECAP2 & FB2 & EV3 & QN2 & (d1 & d2 & e1 & e2 & SH4 & SH5 & SH6) & BO2 & JL2 & COUT3).
    destruct (ge_rp_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ pk kk H (x ++ [Z_to_bv 8 0]) RP2 Hpk1 Kpos
       ltac:(rewrite Epk1, Epk; intros [_ X]; exact (QO1 X)) ltac:(rewrite Epk1, Epk; lia)
       ltac:(rewrite Epk1, Epk, length_app; cbn [length]; lia)
       ltac:(intros i Hi; rewrite length_app in Hi; cbn [length] in Hi; intros [X | [X | [X | (_ & X)]]];
             [ apply (FQ2 (H + i - q) ltac:(lia)); replace (q + (H + i - q)) with (H + i) by lia; apply GIMG; tauto .. |
               unfold ge_hide in KO1; lia ])
       BK1') as (BK2' & _ & _).
    apply SR_ret.
    exists L2, A2, regs2', mem2', md2, OUT2, CAP2, junk2.
    split; [reflexivity|].
    split.
    { apply (ge_rp_seq _ _ _ L A regs mem md m1 (S + -16) S _ _ _ regs1 L1 A1 regs1' mem1' md1 _ _ _ regs2 L2 A2 regs2'
               mem2' md2 HM HWF HIMG' UNCH HFS RP1 RP2 RGP HS1 HS2 HS3).
      - intros a X. exact X.
      - intros a Ha [X | [X | [X | (_ & X)]]]; [left; exact X | right; left; exact X | right; right; left; exact X |].
        exfalso. destruct Ha as [Ha | Ha]; [lia|].
        apply (FB12 (a - OUT1) ltac:(lia)). replace (OUT1 + (a - OUT1)) with a by lia. exact Ha.
      - intros a Ha [X | [X | [X | (_ & X)]]]; unfold G_BROKEN, G_EINTR, G_OUTV in X; lia.
      - intros a X. exact X.
      - intros p n Hp Hn HF Hp1 [_ X].
        exact (QN1 (ptr_addr L p) n (ge_blocks_of L A p n Hp) (fun E => HF (conj eq_refl E)) Hn X).
      - intros p n i Hp Hi HF HE. split; [exact HE|].
        intros [X | [X | [X | (_ & X)]]];
          [apply HE; left; exact X | apply HE; right; left; exact X | apply HE; right; right; left; exact X |].
        assert (Hn : 0 < n) by lia.
        pose proof (SV1 p n Hp Hn HF) as Hp1. pose proof (PA1 p n Hp Hp1 HF) as Ep1.
        assert (Hb1 : In (ptr_addr L p, n) (blocks L1 A1)) by (rewrite <- Ep1; apply ge_blocks_of; exact Hp1).
        pose proof (QN1 (ptr_addr L p) n (ge_blocks_of L A p n Hp) (fun E => HF (conj eq_refl E)) Hn) as NE1.
        destruct (blocks_disjoint Bm API L1 A1 mem1' md1 _ _ _ _ MA1 Hb1 O1IN NE1); lia. }
    split; [exact INIT2|].
    split.
    { exact (ge_res_live F bnd (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) (Z.of_nat (length x)) L A
               (bv_unsigned out) L1 A1 OUT1 CAP1 L2 A2 OUT2 CAP2 qs1 ND1 LQ1 LA1 ECAP1 ECAP2 ltac:(lia) RES2). }
    split; [exact RO3|].
    split; [exact BK2'|].
    split; [exact CCL3|]. split; [exact CBR3|]. split; [exact CDD3|]. split; [exact CEI3|].
    split; [intros X; discriminate X|].
    intros _.
    split; [lia|].
    split; [unfold gesture_end_cap; rewrite <- ECAP1; exact ECAP2|].
    split; [exact FB2|]. split; [exact EV3|].
    split.
    { intros q' m' Hq' Hne Hm. apply (QN2 q' m'); [| exact (QN1 q' m' Hq' Hne Hm) | exact Hm].
      assert (Hb : In (q', m') (b1 ++ b2)).
      { destruct SH3 as [(_ & E) | (_ & E)]; rewrite E in Hq'; [exact Hq' | exact (ge_in_drop _ _ _ _ _ _ Hq' Hne)]. }
      rewrite <- SH2 in Hb. rewrite SH1. apply in_app_iff in Hb. apply in_app_iff.
      destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb]. }
    split.
    { destruct SH6 as [(C0 & _) | (_ & SH6)]; [lia|].
      pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ MA1) as PW.
      pose proof PW as PW1. rewrite SH1 in PW1. rewrite SH6 in PW.
      pose proof (ge_pw_unique c1 (OUT1, CAP1) c2 PW1 ltac:(cbn [snd]; lia)) as U1.
      pose proof (ge_pw_unique d1 (OUT1, CAP1) d2 PW ltac:(cbn [snd]; lia)) as U2.
      rewrite SH1 in SH6.
      destruct (ge_split_unique c1 c2 d1 d2 _ SH6 (fun X => U1 (in_or_app _ _ _ (or_introl X)))
                  (fun X => U2 (in_or_app _ _ _ (or_introl X)))) as [<- <-].
      exists b1, b2, e1, e2. split; [exact SH4|]. split; [rewrite SH5; exact SH2 | exact SH3]. }
    split; [rewrite <- app_assoc in BO2; exact BO2|].
    split; [lia|].
    replace (bv_unsigned nout + (Z.of_nat (length x) + 5)) with (bv_unsigned nout + Z.of_nat (length x) + 5) by lia.
    exact COUT3. }
  { specialize (NL1 eq_refl). destruct NL1 as (EB1 & CERR2 & COUT2).
    assert (OFF2 : (cl <? 0) || ((if (cl <? 0) || (br =? 1) then br else dd) =? 1) = true)
      by (unfold ge_hide in Hcl, Hbr, Hdd; destruct Hcl as [-> | ->], Hbr as [-> | ->], Hdd as [-> | ->];
          vm_compute in ELV |- *; first [reflexivity | discriminate ELV]).
    assert (Hbr1 : (if (cl <? 0) || (br =? 1) then br else dd) = 0 \/ (if (cl <? 0) || (br =? 1) then br else dd) = 1)
      by (unfold ge_hide in Hbr, Hdd; destruct ((cl <? 0) || (br =? 1)); [exact Hbr | exact Hdd]).
    assert (Hei1 : (if (cl <? 0) || (br =? 1) then ei else 0) = 0 \/ (if (cl <? 0) || (br =? 1) then ei else 0) = 1)
      by (unfold ge_hide in Hei; destruct ((cl <? 0) || (br =? 1)); [exact Hei | left; reflexivity]).
    ge_hide_hyp Hbr1. ge_hide_hyp Hei1.
    assert (HOB2 : (bv_unsigned cap = 0 /\ bv_unsigned out = 0 /\ bv_unsigned nout = 0 /\ O = []) \/
       (0 < bv_unsigned cap /\ bv_unsigned nout <= bv_unsigned cap /\ In (bv_unsigned out, bv_unsigned cap) (blocks L1 A1) /\
        fresh_block Bm (bv_unsigned out) (bv_unsigned cap) /\ bytes_at (ms_segs Bm) mem1' (bv_unsigned out) (O ++ junk) /\
        Z.of_nat (length O) = bv_unsigned nout /\ Z.of_nat (length junk) = bv_unsigned cap - bv_unsigned nout /\
        (END5_ADDR + 5 <= bv_unsigned out \/ bv_unsigned out + bv_unsigned cap <= END5_ADDR))).
    { unfold ge_hide in HOB1. destruct HOB1 as [C | (C0 & C1 & C2 & C3 & C4 & C5 & CJ & _)]; [left; exact C | right].
      pose proof C3 as [G0 [G1'' G2']].
      destruct (ge_blocks_in L A _ _ C2) as (po & Hpo & Epo).
      destruct (ge_rp_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ po (bv_unsigned cap) (bv_unsigned out) (O ++ junk) RP1 Hpo C0
                 ltac:(intros [X _]; discriminate X) ltac:(rewrite Epo; lia) ltac:(rewrite Epo, length_app; lia)
                 ltac:(intros i Hi [X | [X | [X | (X & _)]]];
                       [ apply (G2' i ltac:(rewrite length_app in Hi; lia)); apply GIMG; tauto .. | discriminate X ])
                 C4) as (B1 & _ & _).
      split; [exact C0|]. split; [exact C1|]. split; [rewrite EB1; exact C2|]. split; [exact C3|].
      split; [exact B1|]. split; [exact C5|]. split; [exact CJ|].
      destruct (Z_le_gt_dec (END5_ADDR + 5) (bv_unsigned out)) as [Y|Y]; [left; exact Y|].
      destruct (Z_le_gt_dec (bv_unsigned out + bv_unsigned cap) END5_ADDR) as [Y'|Y']; [right; exact Y'|]. exfalso.
      apply (G2' (Z.max (bv_unsigned out) END5_ADDR - bv_unsigned out) ltac:(lia)).
      replace (bv_unsigned out + (Z.max (bv_unsigned out) END5_ADDR - bv_unsigned out))
        with (Z.max (bv_unsigned out) END5_ADDR) by lia.
      apply (proj1 (IM5 (Z.max (bv_unsigned out) END5_ADDR) ltac:(lia))). }
    ge_hide_hyp HOB2.
    pose proof (SL L1 A1 regs2 mem1' md1 bnd END5 O junk cl (if (cl <? 0) || (br =? 1) then br else dd) dd
                  (if (cl <? 0) || (br =? 1) then ei else 0) mx nout cap out
                  (if (cl <? 0) || (br =? 1) then ev
                   else if dd =? 1 then Z_to_bv 64 EPIPE_V else if ei =? 1 then Z_to_bv 64 EINTR_V else ev)) as SL2.
    cbv zeta in SL2. unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in SL2.
    rewrite H1', H2', H10', H11' in SL2.
    rewrite (unsigned_lit (S + -16 + 16)) in SL2 by lia.
    rewrite (unsigned_lit END5_ADDR) in SL2 by (unfold END5_ADDR; lia).
    rewrite (unsigned_lit 5) in SL2 by lia.
    rewrite (ge_live_nz cl _ dd 5 ltac:(lia)), !(ge_off_nz cl _ 5 ltac:(lia)), OFF2 in SL2.
    specialize (SL2 Hseg CP2 INIT1 HTP ERRM HERR RO2 E5M eq_refl
      ltac:(unfold END5_ADDR, G_RELAY_LO; lia) ltac:(unfold END5_ADDR, G_RELAY_HI in *; lia) ltac:(unfold END5_ADDR; lia)
      IMR IMC IME (or_introl IM5) Hcl Hbr1 Hdd Hei1 CCL2 CBR2 CDD2 CEI2 COUT2 CERR2 HOB2 ltac:(lia)
      ltac:(destruct RES1 as (qs1 & _ & RT1 & _); exact RT1) (fun _ _ => I)).
    eapply SR_bind; [exact SL2 |]. clear SL2. intros c3 POST2.
    destruct POST2 as (L2 & A2 & regs2' & mem2' & md2 & OUT2 & CAP2 & junk2 & EC3 & RP2 & INIT2 & RES2 &
      RO3 & BE3 & CCL3 & CBR3 & CDD3 & CEI3 & NL2 & LV2).
    subst c3.
    specialize (NL2 eq_refl).
    destruct NL2 as (EB2 & CERR3 & COUT3).
    destruct (ge_rp_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ pk kk H (x ++ [Z_to_bv 8 0]) RP2 Hpk1 Kpos
       ltac:(intros [X _]; discriminate X) ltac:(rewrite Epk1, Epk; lia)
       ltac:(rewrite Epk1, Epk, length_app; cbn [length]; lia)
       ltac:(intros i Hi; apply KNE; rewrite length_app in Hi; cbn [length] in Hi; lia) BK1') as (BK2' & _ & _).
    apply SR_ret.
    exists L2, A2, regs2', mem2', md2, OUT2, CAP2, junk2.
    split; [reflexivity|].
    split.
    { apply (ge_rp_seq _ _ _ L A regs mem md m1 (S + -16) S _ _ _ regs1 L1 A1 regs1' mem1' md1 _ _ _ regs2 L2 A2 regs2'
               mem2' md2 HM HWF HIMG' UNCH HFS RP1 RP2 RGP HS1 HS2 HS3).
      - intros a X. exact X.
      - intros a Ha [X | [X | [X | (X & _)]]]; [left; exact X | right; left; exact X | right; right; left; exact X |
                                                discriminate X].
      - intros a Ha [X | [X | [X | (X & _)]]]; [unfold G_BROKEN in X; lia | unfold G_EINTR in X; lia |
                                                unfold G_OUTV in X; lia | discriminate X].
      - intros a X. exact X.
      - intros p n Hp Hn HF Hp1 [X _]. discriminate X.
      - intros p n i Hp Hi HF HE. split; [exact HE|].
        intros [X | [X | [X | (X & _)]]];
          [apply HE; left; exact X | apply HE; right; left; exact X | apply HE; right; right; left; exact X |
           discriminate X]. }
    split; [exact INIT2|].
    split.
    { destruct RES2 as (qs2 & LQ2 & RT2 & _). exists qs2. split; [exact LQ2|]. split; [exact RT2|].
      intros X; discriminate X. }
    split; [exact RO3|].
    split; [exact BK2'|].
    split; [exact CCL3|]. split; [exact CBR3|]. split; [exact CDD3|]. split; [exact CEI3|].
    split.
    { intros _. split; [rewrite EB2; exact EB1|]. split; [exact CERR3 | exact COUT3]. }
    intros X. discriminate X. }
Qed.

End GP.
