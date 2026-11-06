(* Proof of fp_head_stmt (lib/A/Prog/diginet_frame_parse_segs.v): the run of diginet_frame_parse in fuzz_frame.asan
   (image A) from its entry 0x82080 to the `jal` at 0x8216c (pc 0x50dc0, ra 0x82170), or to the `ret` at 0x82494 with
   a0 = fr_code b <> 0. The run is walked with StepF's step: the prologue writes the 48-byte frame (carved from the stk
   premise; its cells are fp_fr); buf and f are not 0, so neither beqz is taken; with fewer than 30 bytes a0 = -2;
   else s3 = 0x7fff8000 (through the cells at 0x9a7b8 and 0xa2778), then buf[12], buf[13] (a0 = be16 b 12; -3 when
   it is not 0x885f) and buf[14], buf[15] (s4 = be16 b 14; -4 when it is under 16 or over size - 14). Before each byte
   load the code loads the shadow byte k at ((buf + i) >> 3) + 0x7fff8000; the addressable premise gives k = 0 or
   (buf + i) mod 8 < k, so the bnez falls through or the compare at 0x824e0 / 0x824ec / 0x824f8 / 0x82504 goes back to
   the load, and no call of errpath_load1 (0x824e8, 0x824f4, 0x82500, 0x8250c) is reached. Each access lies in a range
   of an rng premise. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof DgnTransportSyms DgnTransportAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_frame_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_parse_segs.
Import ListNotations.
Open Scope Z_scope.

(* The code fr_code b, from the outcomes of the tests on the length, the EtherType and numbytes in the context. *)
Ltac fphead_fc :=
  unfold fr_code, fr_ethertype, fr_numbytes;
  repeat match goal with
  | |- context [Nat.ltb ?x ?y] => destruct (Nat.ltb_spec x y)
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y)
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
  end; cbn [negb orb]; lia.

(* The return at 0x82494 with a code that is not 0: FC says the code, a0 holds it. *)
Ltac fphead_exit FC :=
  apply evtF_done; unfold fp_head_post, FP_FRAME;
  do 8 eexists;
  split; [ lazymatch goal with |- munch [(?x - 48, _)] _ _ => replace (x - 48) with (x + -48) by lia end;
           eassumption |];
  split; [ eassumption |];
  left; split; [ rewrite FC; lia | rewrite FC; reflexivity ].

(* All the bytes bs at a, read at once. *)
Lemma fphead_rd_all : forall m a bs n, bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H <-.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

(* A shadow byte of an application address lies outside a 48-byte frame of application memory. *)
Lemma fphead_shadow_tp : forall m m' lo hi a k, munch [(lo, hi)] m m' -> lo + 48 = hi ->
  app_mem lo -> app_mem (hi - 1) -> app_mem a ->
  mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k -> mrd rsegs m' (wa (a / 8 + ASAN_K)) = Some k.
Proof.
  intros m m' lo hi a k MU E A1 A2 A3 H.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2, A3. unfold ASAN_K in *.
  apply (mrd_tp m m' lo hi _ k MU); [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact H].
Qed.

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of the bytes [a, a + n). *)
Lemma fphead_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  fp_shrng RNG a n -> ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. unfold fp_shrng in H. eapply rng_sub'; [exact H|]. unfold shadow_addr.
  Z.div_mod_to_equations. lia.
Qed.

(* The inlined rd16 at index i: (p[0] << 8) | p[1], as slli and or compute it. *)
Lemma fphead_pack16 : forall l i,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth i l (Z_to_bv 8 0)))) 8)))
        (bv_unsigned (zxb (nth (S i) l (Z_to_bv 8 0)))) = be16 l i.
Proof.
  intros l i. unfold be16, at8, bz, b8, zxb.
  set (x0 := bv_unsigned (nth i l (Z_to_bv 8 0))).
  set (x1 := bv_unsigned (nth (S i) l (Z_to_bv 8 0))).
  assert (R0 : 0 <= x0 < 256) by apply byte_range.
  assert (R1 : 0 <= x1 < 256) by apply byte_range.
  rewrite (unsigned_lit x0), (unsigned_lit x1) by lia.
  rewrite (unsigned_lit (Z.shiftl x0 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia. lia.
Qed.

Theorem fp_head_holds : fp_head_stmt.
Proof.
  unfold fp_head_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf f lo b
    HBUF HBE HF HB ST HLO DBS APW1 APW2 GCK CK DGOT DCELL AB RFR RGOT RCELL RB RSB.
  fp_lits.
  unfold FP_FRAME in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (KEEP : bytes_at rsegs m buf b /\ bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) /\
                 bytes_at rsegs m CELL_K (le8 (wa ASAN_K))) by (split; [|split]; assumption).
  clear HB GCK CK.
  remember (Z_to_bv 64 buf) as wb eqn:EB.
  assert (UB : bv_unsigned wb = buf) by (subst wb; apply unsigned_lit; lia).
  clear EB. subst buf.
  carve_frame 48%nat ST.
  (* 0x82080 addi sp,sp,-48; 0x82084 .. 0x82098 sd ra, s0, s1, s2, s3, s4 *)
  do 7 step.
  (* 0x8209c mv s1,a0; 0x820a0 li a0,-1; 0x820a4 beqz s1 (buf <> 0) *)
  step. step. step. if_cases HZ.
  1: exfalso; zify_cond HZ; lia.
  clear HZ.
  (* 0x820a8 mv s0,a2; 0x820ac beqz a2 (f <> 0) *)
  step. step. if_cases HZ.
  1: exfalso; zify_cond HZ; lia.
  clear HZ.
  (* 0x820b0 mv s2,a1; 0x820b4 li a0,30; 0x820b8 bgeu a1,a0 *)
  step. step. step. if_cases HC; zify_cond HC.
  2: { (* fewer than 30 bytes: 0x820bc li a0,-2; 0x820c0 j 0x82478 *)
    assert (FC : fr_code b = -2)
      by (unfold fr_code; destruct (Nat.ltb_spec (length b) 30); [reflexivity | lia]).
    step. step.
    do 8 step.
    fphead_exit FC. }
  assert (L30 : (30 <= length b)%nat) by lia. specialize (RSB L30).
  destruct KEEP as (HB & GCK & CK).
  unfold off_stk in DBS, DGOT, DCELL.
  unfold GOT_CELL_K, CELL_K, ASAN_K in *.
  pose proof (bytes_tp m m1 _ _ (bv_unsigned wb) b MU ltac:(lia) HB) as HB1.
  pose proof (bytes_tp m m1 _ _ 671888 (le8 (wa 707064)) MU ltac:(rewrite length_le8; lia) GCK) as GCK1.
  pose proof (bytes_tp m m1 _ _ 707064 (le8 (wa 2147450880)) MU ltac:(rewrite length_le8; lia) CK) as CK1.
  pose proof (fphead_rd_all m1 _ _ 8 GCK1 (length_le8 _)) as RDG.
  pose proof (fphead_rd_all m1 _ _ 8 CK1 (length_le8 _)) as RDS.
  clear GCK CK GCK1 CK1 HB.
  (* 0x820c4 auipc a0; 0x820c8 ld a0 (GOT_CELL_K); 0x820cc ld s3 (CELL_K) *)
  step. step. step.
  destruct AB as (P0 & N0 & PE & AB).
  assert (SH : forall i, 0 <= i < Z.of_nat (length b) -> app_mem (bv_unsigned wb + i) /\
            exists k, mrd rsegs m1 (wa ((bv_unsigned wb + i) / 8 + 2147450880)) = Some k /\
                      (bv_signed k = 0 \/ ((bv_unsigned wb + i) mod 8 < bv_signed k /\ bv_signed k <= 7))).
  { intros i Hi. destruct (AB i Hi) as (APP & k & MK & SK). split; [exact APP|]. exists k. split; [|exact SK].
    unfold shadow_addr in MK.
    apply (fphead_shadow_tp m m1 (bv_unsigned sp + -48) (bv_unsigned sp)); [exact MU | lia | exact APW1 | exact APW2
                                                                          | exact APP | exact MK]. }
  clear AB.
  (* buf[12]: 0x820d0 addi a0,s1,12; 0x820d4 srli a1,a0,3; 0x820d8 add a1,a1,s3; 0x820dc lb a1,0(a1);
     0x820e0 bnez a1 (0x824e0 andi a2,a0,7; blt a2,a1 back to 0x820e4) *)
  pose proof (fphead_shadow_byte_rng RNG (bv_unsigned wb) (Z.of_nat (length b)) 12 ltac:(lia) RSB) as RS12.
  unfold shadow_addr, ASAN_K in RS12.
  destruct (SH 12 ltac:(lia)) as (APP12 & k12 & M12 & SK12).
  pose proof (bytes_nth m1 _ b 12 HB1 ltac:(lia)) as F12. change (Z.of_nat 12) with 12 in F12.
  pose proof (Z.mod_pos_bound (bv_unsigned wb + 12) 8 ltac:(lia)) as MB12.
  step. gen_addi wb w12 U12.
  step. gen_shr w12 g12 G12. rewrite U12 in G12.
  step. gen_addi g12 h12 H12.
  pose proof (rng_sub' _ _ _ (bv_unsigned h12) 1 RS12 ltac:(lia)) as RH12.
  pose proof (rdw0 m1 h12 _ _ M12 ltac:(lia)) as R. step. clear R.
  step.
  destruct SK12 as [C12|[C12 Cu12]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C12); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k12) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U12, (lts_low ((bv_unsigned wb + 12) mod 8) k12 MB12), (proj2 (Z.ltb_lt _ _) C12); cbn [negb].
  (* buf[13]: 0x820e4 addi a0,s1,13; 0x820e8 srli; 0x820ec add; 0x820f0 lb a2,0(a1); 0x820f4 lbu a1,12(s1);
     0x820f8 bnez a2 (0x824ec andi a3,a0,7; blt a3,a2 back to 0x820fc) *)
  all: pose proof (fphead_shadow_byte_rng RNG (bv_unsigned wb) (Z.of_nat (length b)) 13 ltac:(lia) RSB) as RS13;
       unfold shadow_addr, ASAN_K in RS13.
  all: destruct (SH 13 ltac:(lia)) as (APP13 & k13 & M13 & SK13).
  all: pose proof (bytes_nth m1 _ b 13 HB1 ltac:(lia)) as F13; change (Z.of_nat 13) with 13 in F13.
  all: pose proof (Z.mod_pos_bound (bv_unsigned wb + 13) 8 ltac:(lia)) as MB13.
  all: step; gen_addi wb w13 U13.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w13) 1 RB ltac:(lia)) as RW13.
  all: step; gen_shr w13 g13 G13; rewrite U13 in G13.
  all: step; gen_addi g13 h13 H13.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h13) 1 RS13 ltac:(lia)) as RH13.
  all: pose proof (rdw0 m1 h13 _ _ M13 ltac:(lia)) as R; step; clear R.
  all: pose proof (rdw m1 wb 12 _ _ F12 eq_refl) as R; step; clear R.
  all: step.
  all: destruct SK13 as [C13|[C13 Cu13]].
  all: lazymatch type of C13 with
       | bv_signed _ = 0 => rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C13); cbn [negb]
       | _ =>
           rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k13) 0) ltac:(lia)); cbn [negb]; step; step;
           rewrite land7, U13, (lts_low ((bv_unsigned wb + 13) mod 8) k13 MB13), (proj2 (Z.ltb_lt _ _) C13);
           cbn [negb]
       end.
  (* 0x820fc lbu a0,0(a0); 0x82100 slli a1,a1,8; 0x82104 or a0,a1,a0: the EtherType *)
  all: pose proof (rdw0 m1 w13 _ _ F13 ltac:(lia)) as R; step; clear R.
  all: step; step.
  all: rewrite ?fphead_pack16.
  (* 0x82108 lui a1,9; 0x8210c addiw a1,a1,-1953; 0x82110 bne a0,a1 *)
  all: step; step; step.
  all: pose proof (be16_range b 12) as R12; pose proof (be16_range b 14) as R14.
  all: if_cases HE; zify_cond HE; rewrite ?unsigned_lit in HE by lia.
  (* an EtherType other than 0x885f: 0x82474 li a0,-3; the epilogue 0x82478 .. 0x82494 *)
  all: lazymatch type of HE with
       | _ <> _ =>
           assert (FC : fr_code b = -3)
             by (unfold fr_code, fr_ethertype; destruct (Nat.ltb_spec (length b) 30); [lia|];
                 destruct (Z.eqb_spec (be16 b 12) 34911); [lia | reflexivity]);
           step; do 8 step; fphead_exit FC
       | _ => idtac
       end.
  (* buf[14]: 0x82114 addi a0,s1,14; 0x82118 srli; 0x8211c add; 0x82120 lb a1,0(a1); 0x82124 bnez a1
     (0x824f8 andi a2,a0,7; blt a2,a1 back to 0x82128) *)
  all: pose proof (fphead_shadow_byte_rng RNG (bv_unsigned wb) (Z.of_nat (length b)) 14 ltac:(lia) RSB) as RS14;
       unfold shadow_addr, ASAN_K in RS14.
  all: destruct (SH 14 ltac:(lia)) as (APP14 & k14 & M14 & SK14).
  all: pose proof (bytes_nth m1 _ b 14 HB1 ltac:(lia)) as F14; change (Z.of_nat 14) with 14 in F14.
  all: pose proof (Z.mod_pos_bound (bv_unsigned wb + 14) 8 ltac:(lia)) as MB14.
  all: step; gen_addi wb w14 U14.
  all: step; gen_shr w14 g14 G14; rewrite U14 in G14.
  all: step; gen_addi g14 h14 H14.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h14) 1 RS14 ltac:(lia)) as RH14.
  all: pose proof (rdw0 m1 h14 _ _ M14 ltac:(lia)) as R; step; clear R.
  all: step.
  all: destruct SK14 as [C14|[C14 Cu14]].
  all: lazymatch type of C14 with
       | bv_signed _ = 0 => rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C14); cbn [negb]
       | _ =>
           rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k14) 0) ltac:(lia)); cbn [negb]; step; step;
           rewrite land7, U14, (lts_low ((bv_unsigned wb + 14) mod 8) k14 MB14), (proj2 (Z.ltb_lt _ _) C14);
           cbn [negb]
       end.
  (* buf[15]: 0x82128 addi a0,s1,15; 0x8212c srli; 0x82130 add; 0x82134 lb a2,0(a1); 0x82138 lbu a1,14(s1);
     0x8213c bnez a2 (0x82504 andi a3,a0,7; blt a3,a2 back to 0x82140) *)
  all: pose proof (fphead_shadow_byte_rng RNG (bv_unsigned wb) (Z.of_nat (length b)) 15 ltac:(lia) RSB) as RS15;
       unfold shadow_addr, ASAN_K in RS15.
  all: destruct (SH 15 ltac:(lia)) as (APP15 & k15 & M15 & SK15).
  all: pose proof (bytes_nth m1 _ b 15 HB1 ltac:(lia)) as F15; change (Z.of_nat 15) with 15 in F15.
  all: pose proof (Z.mod_pos_bound (bv_unsigned wb + 15) 8 ltac:(lia)) as MB15.
  all: step; gen_addi wb w15 U15.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w15) 1 RB ltac:(lia)) as RW15.
  all: step; gen_shr w15 g15 G15; rewrite U15 in G15.
  all: step; gen_addi g15 h15 H15.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h15) 1 RS15 ltac:(lia)) as RH15.
  all: pose proof (rdw0 m1 h15 _ _ M15 ltac:(lia)) as R; step; clear R.
  all: pose proof (rdw m1 wb 14 _ _ F14 eq_refl) as R; step; clear R.
  all: step.
  all: destruct SK15 as [C15|[C15 Cu15]].
  all: lazymatch type of C15 with
       | bv_signed _ = 0 => rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C15); cbn [negb]
       | _ =>
           rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k15) 0) ltac:(lia)); cbn [negb]; step; step;
           rewrite land7, U15, (lts_low ((bv_unsigned wb + 15) mod 8) k15 MB15), (proj2 (Z.ltb_lt _ _) C15);
           cbn [negb]
       end.
  (* 0x82140 lbu a0,0(a0); 0x82144 slli a1,a1,8; 0x82148 or s4,a1,a0: numbytes *)
  all: pose proof (rdw0 m1 w15 _ _ F15 ltac:(lia)) as R; step; clear R.
  all: step; step.
  all: rewrite ?fphead_pack16.
  (* 0x8214c li a1,16; 0x82150 li a0,-4; 0x82154 bltu s4,a1 *)
  all: step; step; step.
  all: if_cases HN; zify_cond HN; rewrite ?unsigned_lit in HN by lia.
  (* numbytes < 16: the epilogue with a0 = -4 *)
  all: lazymatch type of HN with
       | _ < 16 => assert (FC : fr_code b = -4) by fphead_fc; do 8 step; fphead_exit FC
       | _ => idtac
       end.
  (* 0x82158 addi a1,s2,-14; 0x8215c bltu a1,s4 *)
  all: step; step.
  all: if_cases HL; zify_cond HL; rewrite ?unsigned_lit in HL by lia.
  (* numbytes past the buffer: the epilogue with a0 = -4 *)
  all: lazymatch type of HL with
       | _ + -14 < _ => assert (FC : fr_code b = -4) by fphead_fc; do 8 step; fphead_exit FC
       | _ => idtac
       end.
  (* 0x82160 li a2,6; 0x82164 mv a0,s0; 0x82168 mv a1,s1; 0x8216c jal __asan_memcpy *)
  all: assert (FC : fr_code b = 0) by fphead_fc.
  all: do 4 step.
  all: apply evtF_done; unfold fp_head_post, FP_FRAME, fp_fr.
  all: exists m1, wb, wb; do 5 eexists.
  all: replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia.
  all: split; [exact MU|]; split; [exact WM|]; right; split; [exact FC|]; split; [exact FR|].
  all: rewrite Z_to_bv_bv_unsigned; fp_lits.
  all: reflexivity.
Qed.
