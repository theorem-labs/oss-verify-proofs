(* check_sent_frame_seg_base: the addresses, the bundles, the shared tactics and the straight-line footprint runs
   (lib/Lib/ExecF.v evtF) of check_sent_frame in image A (fuzz_transport.asan, entry 0x83e68 = transport_sigma
   TS_check_sent_frame, listing lib/A/Prog/DgnTransportList.v), for the caller-journal walk of
   lib/A/Prog/check_sent_frame_cg.v (lib/A/Prog/check_sent_frame_cgW.v):
     csf_pro_F   0x83e68 .. 0x83e80: `addi sp,sp,-48` and the five saves (ra, s0 .. s3 at sp + 40 .. sp + 8);
     csf_head_F  0x83e80 .. the call of bcmp at 0x83ed4: s0 = fp, s1 = len, s2 = fa, s3 = the shadow base (read through
                 the GOT word of the runtime cell), the check and the load of f->code (0), the check and the load of
                 f->src (fa + 6), a1 = HOST, a2 = 6;
     csf_mid_F   the first call's return (0x83ed8, a0 = 0) .. the call of bcmp at 0x83f0c: M.desk_known (not 0), the
                 check and the load of f->dst (fa), a1 = M + 4, a2 = 6.
   The rest of the function, from the second call's return to the `ret`, is lib/A/Prog/check_sent_frame_seg_tail.v.

   The bundles: csf_mem (the bytes the runs read: the two runtime cells, the struct's 80 bytes SB at fp, the frame's
   len bytes at fa, the shadow bytes the checks read, M.desk_known and g_cfg.sum_mode as the world's bytes), csf_addr
   (the addresses csf_mem speaks of), csf_rng (the footprint), csf_bnd (the arithmetic) and csf_fx (the model's facts:
   the struct's fields of rf frame, and check_sent_frame_m Bw frame = Some _ read as in the plain walk
   lib/Prog/T/check_sent_frame.v csf_model). The build-independent lemmas of that plain walk (csf_model, csf_rf_ok,
   csf_sys, csum, csf_sum_at, csf_shift, the word compares) are used through the module PCSF. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof DgnTransportSyms DgnTransportAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require check_sent_frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module PCSF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.check_sent_frame.

Definition CSF_ENTRY : Z := transport_sigma TS_check_sent_frame.
Definition CSF_AT (off : Z) : Z := CSF_ENTRY + off.
Definition CSF_BCMP : Z := transport_sigma TS___interceptor_trampoline_bcmp.
(* HOST (fuzz_transport.c:109), the read-only global at 0x21040 = DgnTransportCg.v TRANS_HOST. *)
Definition CSF_HOST : Z := 0x21040.
Definition CSF_HEAD : Z := CSF_AT 0x18.   (* 0x83e80 `mv s0,a2` *)
Definition CSF_RET1 : Z := CSF_AT 0x70.   (* 0x83ed8, the first bcmp returns here *)
Definition CSF_RET2 : Z := CSF_AT 0xa8.   (* 0x83f10, the second bcmp returns here *)

(* What the walk reads: the two runtime cells of the shadow base, the 80 bytes SB of the struct at fp, the len bytes of
   the frame at fa, the shadow byte 0 of every granule of the struct, a shadow byte the check accepts for every byte of
   the frame, M.desk_known (4 bytes at M) and g_cfg.sum_mode (4 bytes at g_cfg + 20), as the world's bytes. *)
Definition csf_mem (m : word -> option byte) (fa fp : Z) (frame SB Bw : list byte) : Prop :=
  ro_cells rsegs m GOT_CELL_K [C8 (wa CELL_K)] /\
  ro_cells rsegs m CELL_K [C8 (wa ASAN_K)] /\
  bytes_at rsegs m fp SB /\
  bytes_at rsegs m fa frame /\
  (forall i, 0 <= i < 80 -> mrd rsegs m (wa ((fp + i) / 8 + ASAN_K)) = Some (Z_to_bv 8 0)) /\
  (forall i, 0 <= i < Z.of_nat (length frame) -> exists k : byte,
     mrd rsegs m (wa ((fa + i) / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ (fa + i) mod 8 < bv_signed k)) /\
  bytes_at rsegs m TA_M (TW.sub Bw TW.A_M_desk_known 4) /\
  bytes_at rsegs m (TA_g_cfg + 20) (TW.sub Bw TW.A_Cfg_sum_mode 4).

(* The addresses csf_mem speaks of. *)
Definition csf_addr (fa fp len : Z) (a : Z) : Prop :=
  (GOT_CELL_K <= a < GOT_CELL_K + 8) \/ (CELL_K <= a < CELL_K + 8) \/
  (fp <= a < fp + 80) \/ (fa <= a < fa + len) \/
  (exists i, 0 <= i < 80 /\ a = (fp + i) / 8 + ASAN_K) \/
  (exists i, 0 <= i < len /\ a = (fa + i) / 8 + ASAN_K) \/
  (TA_M <= a < TA_M + 4) \/ (TA_g_cfg + 20 <= a < TA_g_cfg + 24).

(* The footprint the runs need. *)
Definition csf_rng (RNG : ExecF.footprint) (sp fa fp len : Z) : Prop :=
  ExecF.rng RNG (sp - 48) 48 /\ ExecF.rng RNG GOT_CELL_K 8 /\ ExecF.rng RNG CELL_K 8 /\
  ExecF.rng RNG fp 80 /\ ExecF.rng RNG fa len /\
  (forall i, 0 <= i < 80 -> ExecF.rng RNG ((fp + i) / 8 + ASAN_K) 1) /\
  (forall i, 0 <= i < len -> ExecF.rng RNG ((fa + i) / 8 + ASAN_K) 1) /\
  ExecF.rng RNG TA_M 4 /\ ExecF.rng RNG (TA_g_cfg + 20) 4.

(* The arithmetic: both ranges in the lower half, the struct 8-aligned. *)
Definition csf_bnd (fa fp len : Z) : Prop :=
  0 <= fp /\ fp mod 8 = 0 /\ fp + 80 <= 2 ^ 63 /\ 0 <= fa /\ fa + len <= 2 ^ 63.

(* The model's facts the runs use (check_sent_frame_m Bw frame = Some _, the struct's fields): blen and sum are
   sf_body_len and sf_sum of rf frame at the walk. *)
Definition csf_fx (fa : Z) (frame SB Bw : list byte) (blen sum : Z) : Prop :=
  length SB = 80%nat /\
  TW.s32_at SB 0 = 0 /\ TW.u_at SB 8 8 = fa /\ TW.u_at SB 16 8 = fa + 6 /\
  TW.u_at SB 48 8 = fa + 30 /\ TW.u_at SB 56 8 = blen /\ TW.u_at SB 28 2 = sum /\
  TW.M_desk_known Bw <> 0 /\
  0 <= blen /\ 30 + blen <= Z.of_nat (length frame) /\ blen < 65536 /\
  DS.spec_system_at (TW.zs (skipn 30 frame)) blen < 0 /\
  Z.of_nat (length frame) = Z.max 60 (30 + blen) /\
  (forall k, 30 + blen <= k < Z.of_nat (length frame) -> TW.u_at frame k 1 = 0) /\
  sum = (if TW.Cfg_sum_mode Bw =? 1 then 0 else PCSF.csum frame 30 (Z.to_nat blen) mod 65536) /\
  length Bw = Z.to_nat TW.W_LEN.

Definition csf_fr (junk : list byte) (c3 c2 c1 c0 cra : word) : list cell :=
  [CB 8 junk; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

Ltac csf_pc := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let v := eval vm_compute in pc in change pc with v
  end.

Lemma csf_pro_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    ExecF.rng RNG (bv_unsigned sp - 48) 48 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 junk,
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (CSF_AT 0x18)) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp + -48) /\
         rw_cells rsegs m1 (bv_unsigned sp + -48) (csf_fr junk s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CSF_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO RFR.
  csf_pc.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 6 step.
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => apply evtF_done; exists mm end.
  lazymatch goal with H : rw_cells _ _ _ (CB 8 ?j :: _) |- _ => exists j end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. exact FR.
Qed.

(* `srli rd,rs,3` of an address below 2^64. *)
Lemma csf_shr3 : forall x, 0 <= x < 2 ^ 64 -> Z.shiftr (bv_unsigned (Z_to_bv 64 x)) 3 = x / 8.
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* One read of the bytes at a + k of a byte list bs at a, in TWorld's sub form. *)
Lemma csf_rd : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) n = Some (TW.sub bs k n).
Proof. intros m a bs k n H Hk Hn. apply (bytes_at_read rsegs m a bs k n H Hk). lia. Qed.

(* All the bytes bs at a, read at once. *)
Lemma csf_rd_all : forall m a bs n, bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H <-.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

(* A branch whose condition the tactic tac decides (the goal it gets is `b = c`'s symmetric form, c = b). *)
Ltac brP b tac := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; tac]
  end.

Ltac csf_prep HM HR HB :=
  destruct HM as (RDG & RDS & MSB & MFR & SHp & SHf & MDK & MSM);
  destruct HR as (RFR & RGC & RCK & RSB & RFA & RSp & RSf & RDK & RSM);
  destruct HB as (BP0 & BP8 & BP80 & BF0 & BFL);
  unfold GOT_CELL_K, CELL_K, ASAN_K, TA_M, TA_g_cfg, wa in *.

(* The instrumented check of a load at X inside the struct: the shadow byte of X's granule, 0. *)
Ltac shadow0 SH RS X I :=
  repeat match goal with
  | HH : ov_read_bytes rsegs _ _ 1%nat = Some [Z_to_bv 8 0] |- _ => clear HH
  | HH : ExecF.rng _ (_ / 8 + 2147450880) 1 |- _ => clear HH
  end;
  rewrite (csf_shr3 X) by lia;
  let HS := fresh "HSH" in let HR := fresh "HRG" in
  pose proof (rd1 _ _ _ (SH I ltac:(lia))) as HS;
  pose proof (RS I ltac:(lia)) as HR;
  cbv beta in HS, HR;
  unfold ASAN_K in HS, HR.

(* A branch whose condition is closed. *)
Ltac brF b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (vm_compute; reflexivity); cbv iota
  end.

(* ---- csf_mem across a memory that agrees on the addresses it speaks of ---- *)

Lemma csf_bytes_ext : forall m m' a bs,
  (forall i, (i < length bs)%nat -> mrd rsegs m' (wa (a + Z.of_nat i)) = mrd rsegs m (wa (a + Z.of_nat i))) ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs E (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite E by exact Hi. exact (H i Hi).
Qed.

Lemma csf_ro_ext : forall m m' A cs,
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mrd rsegs m' (wa (A + i)) = mrd rsegs m (wa (A + i))) ->
  ro_cells rsegs m A cs -> ro_cells rsegs m' A cs.
Proof.
  intros m m' A cs E [Hwf (H0 & Hl & Hb)].
  pose proof (cells_bytes_length cs Hwf) as Lc.
  split; [exact Hwf|]. split; [exact H0|]. split; [exact Hl|].
  intros i Hi. rewrite <- (Hb i Hi). apply E. lia.
Qed.

(* csf_mem is kept by a memory that agrees on every address it speaks of. *)
Lemma csf_mem_ext : forall m m' fa fp frame SB Bw,
  length SB = 80%nat ->
  (forall a, csf_addr fa fp (Z.of_nat (length frame)) a -> mrd rsegs m' (wa a) = mrd rsegs m (wa a)) ->
  csf_mem m fa fp frame SB Bw -> csf_mem m' fa fp frame SB Bw.
Proof.
  intros m m' fa fp frame SB Bw LSB E (RDG & RDS & MSB & MFR & SHp & SHf & MDK & MSM).
  assert (L4 : forall l : list byte, length l = 4%nat -> forall i, (i < length l)%nat -> 0 <= Z.of_nat i < 4)
    by (intros l Hl i Hi; lia).
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - apply (csf_ro_ext m m'); [|exact RDG]. intros i Hi. apply E. left. cbn [cells_size csize] in Hi. lia.
  - apply (csf_ro_ext m m'); [|exact RDS]. intros i Hi. apply E. right; left. cbn [cells_size csize] in Hi. lia.
  - apply (csf_bytes_ext m m'); [|exact MSB]. intros i Hi. apply E. right; right; left. lia.
  - apply (csf_bytes_ext m m'); [|exact MFR]. intros i Hi. apply E. right; right; right; left. lia.
  - intros i Hi. rewrite (E ((fp + i) / 8 + ASAN_K)); [exact (SHp i Hi)|].
    right; right; right; right; left. exists i. split; [exact Hi | reflexivity].
  - intros i Hi. destruct (SHf i Hi) as (kb & Hk & Ck). exists kb. split; [|exact Ck].
    rewrite (E ((fa + i) / 8 + ASAN_K)); [exact Hk|].
    right; right; right; right; right; left. exists i. split; [exact Hi | reflexivity].
  - apply (csf_bytes_ext m m'); [|exact MDK]. intros i Hi.
    assert (Hl : (length (TW.sub Bw TW.A_M_desk_known 4) <= 4)%nat)
      by (unfold TW.sub; rewrite length_firstn; lia).
    apply E. right; right; right; right; right; right; left. lia.
  - apply (csf_bytes_ext m m'); [|exact MSM]. intros i Hi.
    assert (Hl : (length (TW.sub Bw TW.A_Cfg_sum_mode 4) <= 4)%nat)
      by (unfold TW.sub; rewrite length_firstn; lia).
    apply E. right; right; right; right; right; right; right. lia.
Qed.

(* Every address csf_mem speaks of lies outside the 48 bytes the prologue writes. *)
Definition csf_sep (sp fa fp len : Z) : Prop :=
  forall a, csf_addr fa fp len a -> 0 <= a < 2 ^ 64 /\ (a + 1 <= sp - 48 \/ sp <= a).

Lemma csf_mem_frame : forall m m1 sp fa fp frame SB Bw, length SB = 80%nat ->
  csf_sep sp fa fp (Z.of_nat (length frame)) -> munch [(sp + -48, sp)] m m1 ->
  csf_mem m fa fp frame SB Bw -> csf_mem m1 fa fp frame SB Bw.
Proof.
  intros m m1 sp fa fp frame SB Bw LSB SEP MU M. apply (csf_mem_ext m m1); [exact LSB | | exact M].
  intros a Ha. destruct (SEP a Ha) as [Hb Hd].
  unfold mrd. rewrite (MU (wa a)); [reflexivity|].
  cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I].
Qed.

Section Head.
Variable RNG : ExecF.footprint.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m : word -> option byte.
Variables fa fp blen sum : Z.
Variables frame SB Bw : list byte.
Hypothesis MEM : csf_mem m fa fp frame SB Bw.
Hypothesis RNGH : csf_rng RNG (bv_unsigned sp) fa fp (Z.of_nat (length frame)).
Hypothesis BND : csf_bnd fa fp (Z.of_nat (length frame)).
Hypothesis FX : csf_fx fa frame SB Bw blen sum.

Local Abbreviation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).

Lemma csf_head_F :
  ExecF.evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 CSF_RET1) SP gp tp t0 t1 t2 (Z_to_bv 64 fp)
                           (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 (fa + 6)) (Z_to_bv 64 CSF_HOST)
                           (Z_to_bv 64 6) a3 a4 a5 a6 a7 (Z_to_bv 64 fa) (Z_to_bv 64 ASAN_K)
                           s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 CSF_BCMP) fc None m (seg_rom rsegs))
    (MS (mkR ra SP gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 fp)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 CSF_HEAD) fc None m (seg_rom rsegs)).
Proof.
  pose proof FX as (LSB & FC0 & F8 & F16 & F48 & F56 & F28 & FDK & FB0 & FBL & FB16 & FSYS & FN & FZ & FSUM & FLB).
  csf_prep MEM RNGH BND. csf_pc.
  pose proof (bytes_at_bound rsegs m _ _ MSB) as BSB. rewrite LSB in BSB.
  (* 0x83e80 mv s0,a2 ; mv s1,a1 ; auipc a1 ; ld a1 (GOT_CELL_K) ; ld s3 (CELL_K) *)
  do 5 step.
  (* 0x83e94 srli a1,a2,3 ; add a1,a1,s3 ; lb a1 : the shadow byte of fp *)
  step. step.
  shadow0 SHp RSp fp 0.
  step.
  (* 0x83ea0 mv s2,a0 ; 0x83ea4 bnez a1: the shadow byte is 0 *)
  step. step. brF false.
  (* 0x83ea8 lw a0,0(s0) : f->code = 0 ; 0x83eac bnez a0 *)
  pose proof (csf_rd m fp SB 0 4 MSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD0.
  step. clear RD0. rewrite lw_world, FC0.
  step. brF false.
  (* 0x83eb0 addi a0,s0,16 ; srli ; add ; lbu a1 : the shadow byte of fp + 16 ; bnez *)
  step. step. step.
  shadow0 SHp RSp (fp + 16) 16.
  step. step. brF false.
  (* 0x83ec4 ld a0,0(a0) : f->src = fa + 6 *)
  pose proof (csf_rd m fp SB 16 8 MSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD16.
  step. clear RD16. rewrite ld_world, F16.
  (* 0x83ec8 auipc a1 ; addi a1 : HOST ; li a2,6 ; jal bcmp *)
  do 4 step.
  apply evtF_done. reflexivity.
Qed.

(* From the first bcmp's return (a0 = 0) to the call of the second: M.desk_known is not 0, f->dst = fa. *)
Lemma csf_mid_F : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  ExecF.evtF rsegs RNG
    (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 CSF_RET2) SP gp tp x5 x6 x7 (Z_to_bv 64 fp)
                     (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 fa) (Z_to_bv 64 (TA_M + 4))
                     (Z_to_bv 64 6) x13 x14 x15 x16 x17 (Z_to_bv 64 fa) (Z_to_bv 64 ASAN_K)
                     s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 CSF_BCMP) fc None m (seg_rom rsegs))
    (MS (mkR x1 SP gp tp x5 x6 x7 (Z_to_bv 64 fp) (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 0)
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fa) (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11
             x28 x29 x30 x31)
         F (Z_to_bv 64 CSF_RET1) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
  pose proof FX as (LSB & FC0 & F8 & F16 & F48 & F56 & F28 & FDK & FB0 & FBL & FB16 & FSYS & FN & FZ & FSUM & FLB).
  csf_prep MEM RNGH BND. csf_pc.
  pose proof (bytes_at_bound rsegs m _ _ MSB) as BSB. rewrite LSB in BSB.
  assert (L4 : length (TW.sub Bw TW.A_M_desk_known 4) = 4%nat)
    by (apply TWorldLemmas.length_sub; [unfold TW.A_M_desk_known, TW.OFF_M; lia|];
        rewrite FLB; unfold TW.A_M_desk_known, TW.OFF_M, TW.W_LEN; lia).
  pose proof (csf_rd_all m _ _ 4 MDK L4) as RMD.
  (* the two cells of the shadow base are not read here; a literal load would try them first *)
  clear RDG RDS.
  pose proof (TWorldLemmas.s32_range Bw TW.A_M_desk_known) as RDR.
  (* 0x83ed8 bnez a0 *)
  step. brF false.
  (* 0x83edc auipc a0 ; addi a1,a0 : M ; lw a0,0(a1) : M.desk_known ; beqz a0 *)
  step. step. step. clear RMD. rewrite lw_world.
  step. brP false ltac:(rewrite (PCSF.csf_eqb0_s32 _ RDR); apply Z.eqb_neq; exact FDK).
  (* 0x83eec addi a0,s0,8 ; srli ; add ; lbu a2 : the shadow byte of fp + 8 ; bnez *)
  step. step. step.
  shadow0 SHp RSp (fp + 8) 8.
  step. step. brF false.
  (* 0x83f00 ld a0,0(a0) : f->dst = fa *)
  pose proof (csf_rd m fp SB 8 8 MSB ltac:(lia) ltac:(rewrite LSB; lia)) as RD8.
  step. clear RD8. rewrite ld_world, F8.
  (* 0x83f04 addi a1,a1,4 : M + 4 ; li a2,6 ; jal bcmp *)
  do 3 step.
  apply evtF_done. reflexivity.
Qed.
End Head.

(* The run from the entry to the call of the first bcmp: the prologue, then the head; csf_mem is carried across the
   prologue's frame write by csf_sep. *)
Lemma csf_run1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo fa fp blen sum : Z) (frame SB Bw : list byte),
    csf_mem m fa fp frame SB Bw -> csf_rng RNG (bv_unsigned sp) fa fp (Z.of_nat (length frame)) ->
    csf_bnd fa fp (Z.of_nat (length frame)) -> csf_fx fa frame SB Bw blen sum ->
    csf_sep (bv_unsigned sp) fa fp (Z.of_nat (length frame)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 junk,
         ms' = MS (mkR (Z_to_bv 64 CSF_RET1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 fp)
                     (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 (fa + 6)) (Z_to_bv 64 CSF_HOST)
                     (Z_to_bv 64 6) a3 a4 a5 a6 a7 (Z_to_bv 64 fa) (Z_to_bv 64 ASAN_K)
                     s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CSF_BCMP) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp + -48) /\
         rw_cells rsegs m1 (bv_unsigned sp + -48) (csf_fr junk s3 s2 s1 s0 ra) /\
         csf_mem m1 fa fp frame SB Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fa) (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 fp)
               a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CSF_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo fa fp
    blen sum frame SB Bw MEM RNGH BND FX SEP ST LO.
  pose proof FX as (LSB & _).
  eapply ExecF.evtF_cut.
  { eapply csf_pro_F; [exact ST | exact LO | exact (proj1 RNGH)]. }
  intros ms0 (m1 & junk & -> & MU & WM & ST1 & FR).
  pose proof (csf_mem_frame m m1 (bv_unsigned sp) fa fp frame SB Bw LSB SEP MU MEM) as MEM1.
  eapply ExecF.evtF_mono.
  { eapply csf_head_F; [exact MEM1 | exact RNGH | exact BND | exact FX]. }
  intros ms' ->. exists m1, junk.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST1|]. split; [exact FR | exact MEM1].
Qed.
