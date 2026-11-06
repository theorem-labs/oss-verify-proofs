(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F22.v f22_loop (:218), f22_lu_evt (:64) and seg_F22's own inline stretch
     0x827f8 -> 0x8283c (:490-498) at a working branch 3803efccea0
     (blob d8085fdbbbc09b84b1eb48c4bc32eaebf4ee6c61);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: split stretches.  f22_loop_F re-runs F22.v:246-265 (the 6-turn sum loop and the result test) on the
     lib.Lib engine with StepF in place of the UL engine's Step (F22.f22_lu_msteps shows the two step relations
     have the same body, so this is the same run).  seg_F22_F re-runs F22.v:490-498 (the whole stretch
     0x827f8 -> 0x8283c, f22_loop at i = 0, k = 6).  f22_lu_evt is the UL bridge that carries the head-amp
     callee contract into seg_F22t's UL run; an _F stretch never runs a callee, so it has no footprint twin:
     the call is split instead into seg_F22t_pre_F (0x8283c -> the callee entry 0x858e4) and seg_F22t_post_F
     (the return pc 0x82844 -> the stretch's end), re-running F22.v:634-653. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_headamp_record_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F22.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module HRV := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_headamp_record_verify_c.
(* The short name PropExec resolves to the UL engine's copy here (the Seg chain loads it last), but StepF steps
   the lib.Lib engine: name its value functions explicitly. *)
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.

(* An access at exactly a region we carry: close it from that region without arithmetic on the shadow address
   (Z.shiftr is opaque to lia; pilot note (b)).  acc_hint is StepF's hook, tried first by solve_acc1. *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      match goal with
      | H : rng RNG E _ |- _ =>
          eapply rng_acc_litZ; [exact H | reflexivity | lia | split; lia]
      end
  end.

(* 0x82830 andi a0,a1,127 ; seqz s7,a0 ; addi s7,s7,-1 over the lib.Lib value functions (F22.f22_s7 is stated
   over the UL engine's PropExec). *)
Lemma f22_s7_lib : forall S, 0 <= S < 2 ^ 64 ->
  Z_to_bv 64 (bv_unsigned (LPE.v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 S)) 127)) 1) + -1)
  = Z_to_bv 64 (if S mod 128 =? 0 then 0 else -1).
Proof.
  intros S HS. rewrite (unsigned_lit S) by lia.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128.
  pose proof (Z.mod_pos_bound S 128 ltac:(lia)) as Hb.
  unfold LPE.v_sltiu. rewrite (unsigned_lit (S mod 128)) by lia. change (bv_wrap 64 1) with 1%Z.
  destruct (Z.eqb_spec (S mod 128) 0) as [E|E].
  - rewrite E. reflexivity.
  - replace (S mod 128 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* The one-byte read facts in the lib.Lib form StepF consumes. *)
Lemma f22_rd1_lib : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.

(* `lbu` zero-extends, over the lib.Lib zxb (F22.f22_zxb_u is stated over the UL engine's). *)
Lemma f22_zxb_u_lib : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply unsigned_lit. pose proof (F22.f22_ubyte b). lia. Qed.

(* After `srli x,a,3` on a = Phi + c: expose the unsigned value of the literal word. *)
Ltac f22_ush := match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3] => rewrite (unsigned_lit X) by lia
  end.

(* The footprint twin of F22.f22_loop: the 6-turn record sum loop 0x827f8 -> 0x8283c, by the number k of turns
   left.  Each turn reads the record byte Phi + 34 + i and its shadow byte ((Phi + 34 + i) >> 3) + 0x7fff8000;
   it writes no memory.  The regions are stated per turn, which is exactly what the run touches. *)
Lemma f22_loop_F : forall (RNG : footprint) (k i : nat) (Q : _ -> Prop)
  (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (rec : list byte),
  (i + k = 6)%nat -> (0 < k)%nat -> 0 < phi -> phi + 50 <= 2 ^ 64 ->
  (forall t, (t < 6)%nat -> bytes_at rsegs m (phi + 34 + Z.of_nat t) [nth t rec (Z_to_bv 8 0)]) ->
  (forall t, (t < 6)%nat -> b8 m (Z.shiftr (phi + 34 + Z.of_nat t) 3 + ASAN_K) 0) ->
  (forall t, (t < 6)%nat -> rng RNG (phi + 34 + Z.of_nat t) 1) ->
  (forall t, (t < 6)%nat -> rng RNG (Z.shiftr (phi + 34 + Z.of_nat t) 3 + ASAN_K) 1) ->
  (forall a0' a1' a4' a5' : word,
     Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' (Z_to_bv 64 (phi + 34))
          (Z_to_bv 64 (2 ^ 64 - (phi + 35))) a4' a5' a6 (Z_to_bv 64 6) s2 s3 s4 s5 s6
          (Z_to_bv 64 (if RcModel.psum rec 6 mod 128 =? 0 then 0 else -1)) s8 s9
          (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8283c) fc None m (seg_rom rsegs))) ->
  evtF rsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat i))
     (Z_to_bv 64 (RcModel.psum rec i)) (Z_to_bv 64 (phi + 34)) (Z_to_bv 64 (2 ^ 64 - (phi + 35))) a4 a5 a6
     (Z_to_bv 64 6) s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x827f8) fc None m
     (seg_rom rsegs)).
Proof.
  intros RNG k. induction k as [|k IH]; intros i Q ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s11
    t3 t4 t5 t6 F fc m phi rec Hik Hk Hphi0 Hphi50 HB HS RB' RS' HQ; [lia|].
  assert (Hi : (i < 6)%nat) by lia.
  pose proof (f22_rd1_lib m _ _ (HB i Hi)) as RB.
  pose proof (f22_rd1_lib m _ _ (HS i Hi)) as RS.
  pose proof (RB' i Hi) as RGb.
  pose proof (RS' i Hi) as RGs.
  pose proof (F22.f22_psum_range rec i) as Rp.
  pose proof (F22.f22_psum_range rec 6) as Rp6.
  pose proof (F22.f22_ubyte (nth i rec (Z_to_bv 8 0))) as Rb.
  assert (U3 : bv_unsigned (Z_to_bv 64 (2 ^ 64 - (phi + 35))) = 2 ^ 64 - (phi + 35))
    by (apply unsigned_lit; lia).
  assert (Ui : bv_unsigned (Z_to_bv 64 (Z.of_nat i)) = Z.of_nat i) by (apply unsigned_lit; lia).
  assert (Ui1 : bv_unsigned (Z_to_bv 64 (Z.of_nat (S i))) = Z.of_nat (S i)) by (apply unsigned_lit; lia).
  (* 0x827f8 bltu a3,a0 (T54: 2^64 - (Phi + 35) >= i, so Phi + 34 + i does not wrap; not taken) *)
  step. if_false.
  (* add a4,a2,a0 ; srli a5,a4,3 ; add a5,a5,s10 ; lb a5 = shadow(Phi + 34 + i) = 0 ; bnez a5 (not taken) *)
  step. step. f22_ush. step. step. step. if_false.
  (* lbu a4 = rec[i] ; addi a0,a0,1 ; add a1,a1,a4 ; bne a0,a7,827f8 *)
  step. step. step. step.
  rewrite (f22_zxb_u_lib (nth i rec (Z_to_bv 8 0))).
  change (RcModel.psum rec i + bv_unsigned (nth i rec (Z_to_bv 8 0))) with (RcModel.psum rec (S i)).
  replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
  destruct k as [|k].
  - (* i = 5: the last turn; the back edge is not taken *)
    assert (E5 : i = 5%nat) by lia. subst i.
    if_false.
    (* 0x82820 j 82830 ; andi a0,a1,127 ; seqz s7,a0 ; addi s7,s7,-1 *)
    step. step. step. step.
    rewrite (f22_s7_lib (RcModel.psum rec 6)) by lia.
    apply evtF_done. apply HQ.
  - (* i < 5: the back edge to 0x827f8 *)
    if_true.
    apply (IH (S i)); [lia | lia | exact Hphi0 | exact Hphi50 | exact HB | exact HS | exact RB' | exact RS'
                      | exact HQ].
Qed.

(* The whole stretch 0x827f8 -> 0x8283c as seg_F22 runs it (F22.v:490-498): f22_loop_F from turn 0, with the
   entry cut's a0 = a1 = 0. *)
Lemma seg_F22_F : forall (RNG : footprint)
  (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (rec : list byte),
  0 < phi -> phi + 50 <= 2 ^ 64 ->
  (forall t, (t < 6)%nat -> bytes_at rsegs m (phi + 34 + Z.of_nat t) [nth t rec (Z_to_bv 8 0)]) ->
  (forall t, (t < 6)%nat -> b8 m (Z.shiftr (phi + 34 + Z.of_nat t) 3 + ASAN_K) 0) ->
  (forall t, (t < 6)%nat -> rng RNG (phi + 34 + Z.of_nat t) 1) ->
  (forall t, (t < 6)%nat -> rng RNG (Z.shiftr (phi + 34 + Z.of_nat t) 3 + ASAN_K) 1) ->
  evtF rsegs RNG
    (fun ms' => exists a0' a1' a4' a5' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' (Z_to_bv 64 (phi + 34))
            (Z_to_bv 64 (2 ^ 64 - (phi + 35))) a4' a5' a6 (Z_to_bv 64 6) s2 s3 s4 s5 s6
            (Z_to_bv 64 (if RcModel.psum rec 6 mod 128 =? 0 then 0 else -1)) s8 s9
            (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8283c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (phi + 34))
         (Z_to_bv 64 (2 ^ 64 - (phi + 35))) a4 a5 a6 (Z_to_bv 64 6) s2 s3 s4 s5 s6 s7 s8 s9
         (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x827f8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m phi rec
    Hphi0 Hphi50 HB HS RB' RS'.
  apply (f22_loop_F RNG 6%nat 0%nat _ ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s11
           t3 t4 t5 t6 F fc m phi rec);
    [reflexivity | lia | exact Hphi0 | exact Hphi50 | exact HB | exact HS | exact RB' | exact RS' |].
  intros a0' a1' a4' a5'. cbv beta. exists a0', a1', a4', a5'. reflexivity.
Qed.

(* The call stretch 0x8283c -> the head-amp callee entry 0x858e4 (F22.v:636): mv a0,s2 ; jal.  No memory
   access, so no rng premise. *)
Lemma seg_F22t_pre_F : forall (RNG : footprint)
  (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z),
  s2v = Z_to_bv 64 phi ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x82844) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 phi) a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 phi) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 HRV.REAC_CTRL_HEADAMP_RECORD_VERIFY) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8283c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi ->.
  step. step.
  apply evtF_done. reflexivity.
Qed.

(* The post half (F22.v:642-653): from the return pc 0x82844 there is no further instruction before the
   stretch's exit cut, so the post is the callee post facts themselves. *)
Lemma seg_F22t_post_F : forall (RNG : footprint)
  (ra' sp gp tp t0' t1 t2 s0 s1 a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (phi lo v : Z),
  munch [(bv_unsigned sp - HRV.REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME, bv_unsigned sp)] m m' ->
  wmono rsegs m m' -> ro_agree rsegs m' ->
  stk rsegs m' lo (bv_unsigned sp) ->
  evtF rsegs RNG
    (fun ms'' => exists (ra'' t0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' : word) (m'' : word -> option byte),
       ms'' = MS (mkR ra'' sp gp tp t0'' t1 t2 s0 s1 (Z_to_bv 64 v) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                      s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x82844) fc None m'' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - HRV.REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME, bv_unsigned sp)] m m''
       /\ wmono rsegs m m'' /\ ro_agree rsegs m'' /\ stk rsegs m'' lo (bv_unsigned sp))
    (MS (mkR ra' sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7'
             s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x82844) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG ra' sp gp tp t0' t1 t2 s0 s1 a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m m' phi lo v MU WM HRO ST.
  apply evtF_done.
  exists ra', t0', a1', a2', a3', a4', a5', a6', a7', m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact HRO | exact ST].
Qed.
