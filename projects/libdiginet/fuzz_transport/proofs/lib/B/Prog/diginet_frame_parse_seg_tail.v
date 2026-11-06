(* Proof of fp_tail_stmt (diginet_frame_parse_segs.v): the image-B run of diginet_frame_parse (fuzz_frame.asan-ubsan)
   from FP_SUMR (0x823a8, the return of the diginet_sum16 call, a0 = body_sum) to its return at 0x82424.
     0x823a8 .. 0x823bc  the shadow byte of f + 56, then `sh a0, 56(s0)` (body_sum);
     0x823c0 .. 0x823c4  the shadow byte of f + 18 (at s7), for the 2-byte load of the sum;
     0x823c8 .. 0x823d4  the shadow byte of f + 58;
     0x823d8  `lhu a3, 0(s4)`: the sum at f + 18 (fr_sum, below 2^16);
     0x823e0 .. 0x823ec  a1 = 0, a0 = seqz (a0 xor a3), `sb a0` at f + 58 (sum_matches);
     0x823f0 .. 0x82424  a0 = a1 = 0, ra and s0 .. s7 loaded from the frame at sq, sp = sq + 80, ret.
   Each shadow byte k comes from an addressable premise: k = 0, or (a mod 8) + size - 1 < k, which is the compare of
   the slow path (0x82540 .. 0x82548 for the 2-byte store, 0x82554 .. 0x8255c for the 2-byte load, 0x82568 / 0x8256c
   for the 1-byte store) that goes back to the access. So the calls at 0x82550 (errpath_store2), 0x82564
   (errpath_load2) and 0x82574 (errpath_store1) are not reached. This run has no branch to the unimp word. Every
   access lies in a range of an ExecF.rng premise: the frame at sq, the 64 bytes at f, and the shadow bytes of f. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_frame_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_segs.
Import ListNotations.
Open Scope Z_scope.

(* ---- arithmetic of the loaded sum and of sum_matches ---- *)

(* lhu of a value below 2^16 gives the value back. *)
Lemma fpbtail_zx16 : forall x, 0 <= x < 2^16 -> zx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold zx16. rewrite (unsigned_lit x) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* xor of the two sums, then seqz, stored as one byte. *)
Lemma fpbtail_seqz_cell : forall x y, 0 <= x < 2^16 -> 0 <= y < 2^16 ->
  Z_to_bv 8 (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) (bv_unsigned (Z_to_bv 64 y)))) 1))
  = b8 (if y =? x then 1 else 0).
Proof.
  intros x y Hx Hy. rewrite (unsigned_lit x), (unsigned_lit y) by lia.
  assert (RX : 0 <= Z.lxor x y < 2^16).
  { split; [apply Z.lxor_nonneg; lia|].
    destruct (Z.eq_dec (Z.lxor x y) 0) as [E|E]; [rewrite E; lia|].
    apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg x y); lia|].
    pose proof (Z.log2_lxor x y ltac:(lia) ltac:(lia)) as L.
    assert (Z.log2 x < 16) by (destruct (Z.eq_dec x 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
    assert (Z.log2 y < 16) by (destruct (Z.eq_dec y 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
    lia. }
  unfold v_sltiu. rewrite (unsigned_lit (Z.lxor x y)) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec y x) as [->|N].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - assert (NZ : Z.lxor x y <> 0) by (intros E; apply (proj1 (Z.lxor_eq_0_iff x y)) in E; exact (N (eq_sym E))).
    replace (Z.lxor x y <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* ---- memory facts ---- *)

Lemma fpbtail_le1_any : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma fpbtail_rw_cells_ext : forall m A cs cs', rw_cells rsegs m A cs -> cs = cs' -> rw_cells rsegs m A cs'.
Proof. intros; subst; assumption. Qed.

(* The shadow byte of an application byte is not an application byte. *)
Lemma fpbtail_sh_not_app : forall x, app_mem x -> ~ app_mem (x / 8 + ASAN_K).
Proof.
  intros x H. unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* ... so it lies outside the 64 addressable bytes at p. *)
Lemma fpbtail_sh_outside : forall m p x, addressable m p 64 -> app_mem x ->
  outside [(p, p + 64)] (x / 8 + ASAN_K).
Proof.
  intros m p x (P0 & N0 & PE & AB) Ax. pose proof (fpbtail_sh_not_app x Ax) as N.
  cbn [outside]. split; [|exact I]. intros W. apply N.
  destruct (AB (x / 8 + ASAN_K - p) ltac:(lia)) as (Ay & _).
  replace (p + (x / 8 + ASAN_K - p)) with (x / 8 + ASAN_K) in Ay by lia. exact Ay.
Qed.

Lemma fpbtail_mrd_munch : forall W m m' a b, munch W m m' -> outside W a ->
  mrd rsegs m (wa a) = Some b -> 0 <= a < 2^64 -> mrd rsegs m' (wa a) = Some b.
Proof.
  intros W m m' a b MU Ho H Ha. unfold mrd in *. rewrite MU; [exact H|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* The shadow byte of x in [p, p + n) lies in the shadow range of [p, p + n). *)
Lemma fpbtail_sh_rng : forall RNG p n x, 0 <= p -> p <= x < p + n ->
  ExecF.rng RNG (p / 8 + 2147450880) ((p + n - 1) / 8 + 2147450880 - (p / 8 + 2147450880) + 1) ->
  ExecF.rng RNG (x / 8 + 2147450880) 1.
Proof. intros RNG p n x H0 Hx H. eapply rng_sub'; [exact H|]. Z.div_mod_to_equations. lia. Qed.

(* Two neighbouring bytes in one granule. *)
Lemma fpbtail_next_byte : forall a k, 0 <= a -> a mod 8 < k -> k <= 7 ->
  (a + 1) / 8 = a / 8 /\ (a + 1) mod 8 = a mod 8 + 1.
Proof. intros a k H0 H1 H2. split; Z.div_mod_to_equations; lia. Qed.

(* For a 2-byte access at a: the shadow bytes of a and a + 1 give k = 0, or (a mod 8) + 1 < k <= 7. *)
Lemma fpbtail_shadow2 : forall m a k k1,
  mrd rsegs m (wa (a / 8 + 2147450880)) = Some k -> mrd rsegs m (wa ((a + 1) / 8 + 2147450880)) = Some k1 ->
  0 <= a ->
  (bv_signed k = 0 \/ (a mod 8 < bv_signed k /\ bv_signed k <= 7)) ->
  (bv_signed k1 = 0 \/ ((a + 1) mod 8 < bv_signed k1 /\ bv_signed k1 <= 7)) ->
  bv_signed k = 0 \/ (a mod 8 + 1 < bv_signed k /\ bv_signed k <= 7).
Proof.
  intros m a k k1 MK MK1 Ha SK SK1.
  destruct SK as [C|[C1 C2]]; [left; exact C|right].
  destruct (fpbtail_next_byte a (bv_signed k) Ha C1 C2) as (E1 & M1).
  rewrite E1, MK in MK1. injection MK1 as E. subst k1.
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)). rewrite M1 in SK1. lia.
Qed.

(* ---- the run FP_SUMR -> the return ---- *)

Theorem fp_tail_holds : fp_tail_stmt.
Proof.
  unfold fp_tail_stmt.
  intros RNG ra sq gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s8 s9 s10 s11 t3 t4 t5 t6
    j c7 c6 c5 c4 c3 c2 c1 c0 cra F fc m buf f b fj LFJ PRE FR SQB DSQ RSQ.
  destruct PRE as (FC0 & Hb0 & Hbe & Hf0 & Hfe & BB & HC & CS & DBF & ADB & ADF & RB & RF & RSB & RSF).
  fp_lits.
  unfold FP_FRAME in *. unfold fp_fr in FR. unfold fp_hdr_cells in HC. unfold fp_sh18.
  unfold fp_shrng, shadow_addr in RSF. unfold ASAN_K in *.
  pose proof (u64_range sq) as Rsq.
  clear BB ADB RB RSB DBF CS LFJ FC0 Hb0 Hbe.
  (* the shadow bytes of f + 18 and f + 19 (the 2-byte load), f + 56 and f + 57 (the 2-byte store), f + 58 *)
  pose proof ADF as (Pf & Nf & PEf & ABf).
  unfold APPMEM_END in PEf.
  destruct (ABf 18 ltac:(lia)) as (AP18 & k18 & MK18 & SK18).
  destruct (ABf 19 ltac:(lia)) as (_ & k19 & MK19 & SK19).
  destruct (ABf 56 ltac:(lia)) as (AP56 & k56 & MK56 & SK56).
  destruct (ABf 57 ltac:(lia)) as (_ & k57 & MK57 & SK57).
  destruct (ABf 58 ltac:(lia)) as (AP58 & k58 & MK58 & SK58).
  clear ABf.
  unfold shadow_addr, shadow_ok, ASAN_K in MK18, SK18, MK19, SK19, MK56, SK56, MK57, SK57, MK58, SK58.
  pose proof (Z.mod_pos_bound (f + 18) 8 ltac:(lia)) as MB18.
  pose proof (Z.mod_pos_bound (f + 56) 8 ltac:(lia)) as MB56.
  pose proof (Z.mod_pos_bound (f + 58) 8 ltac:(lia)) as MB58.
  replace (f + 19) with (f + 18 + 1) in MK19, SK19 by lia.
  replace (f + 57) with (f + 56 + 1) in MK57, SK57 by lia.
  pose proof (fpbtail_shadow2 m (f + 18) k18 k19 MK18 MK19 ltac:(lia) SK18 SK19) as SK18'.
  pose proof (fpbtail_shadow2 m (f + 56) k56 k57 MK56 MK57 ltac:(lia) SK56 SK57) as SK56'.
  clear SK18 SK19 MK19 SK56 SK57 MK57 k19 k57.
  assert (R18 : 0 <= (f + 18) / 8 + 2147450880 < 2^64) by (clear - Hf0 Hfe; Z.div_mod_to_equations; lia).
  assert (R58 : 0 <= (f + 58) / 8 + 2147450880 < 2^64) by (clear - Hf0 Hfe; Z.div_mod_to_equations; lia).
  pose proof (fpbtail_sh_outside m f (f + 18) ADF AP18) as O18. unfold ASAN_K in O18.
  pose proof (fpbtail_sh_outside m f (f + 58) ADF AP58) as O58. unfold ASAN_K in O58.
  pose proof (fpbtail_sh_rng RNG f 64 (f + 18) ltac:(lia) ltac:(lia) RSF) as RS18.
  pose proof (fpbtail_sh_rng RNG f 64 (f + 56) ltac:(lia) ltac:(lia) RSF) as RS56.
  pose proof (fpbtail_sh_rng RNG f 64 (f + 58) ltac:(lia) ltac:(lia) RSF) as RS58.
  clear RSF ADF Pf Nf PEf AP18 AP56 AP58.
  pose proof (munch_refl [(f, f + 64)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x823a8 addi a1,s0,56; 0x823ac srli a2,a1,3; 0x823b0 add a2,a2,s5 *)
  step.
  step. gen_shr (Z_to_bv 64 (f + 56)) g56 G56. rewrite (unsigned_lit (f + 56)) in G56 by lia.
  step. gen_addi g56 h56 H56. rewrite G56 in H56.
  pose proof RS56 as RH56. rewrite <- H56 in RH56.
  (* 0x823b4 lb a2,0(a2) *)
  pose proof (rdw0 m h56 _ _ MK56 H56) as R. step. clear R.
  (* 0x823b8 bnez a2; for k56 <> 0, 0x82540 andi a3,a1,7, 0x82544 addi a3,a3,1 and 0x82548 blt a3,a2 go back to
     0x823bc *)
  step.
  destruct SK56' as [C56|[C56 C56']].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C56); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k56) 0) ltac:(lia)); cbn [negb]; step; step; step;
     rewrite land7, (unsigned_lit (f + 56)) by lia;
     rewrite (lts_low ((f + 56) mod 8 + 1) k56 ltac:(lia)), (proj2 (Z.ltb_lt _ _) C56); cbn [negb].
  (* 0x823bc sh a0,56(s0): the cell at f + 56 is body_sum *)
  all: step.
  all: lazymatch type of MU with munch _ _ ?m1 =>
         pose proof (fpbtail_mrd_munch _ m m1 _ _ MU O18 MK18 R18) as M18;
         pose proof (fpbtail_mrd_munch _ m m1 _ _ MU O58 MK58 R58) as M58 end.
  all: clear MK18 MK58 O18 O58.
  (* 0x823c0 lb a1,0(s7): the shadow byte of f + 18 *)
  all: pose proof (rdw0 _ (Z_to_bv 64 ((f + 18) / 8 + 2147450880)) _ _ M18 (unsigned_lit _ R18)) as R.
  all: step; clear R.
  (* 0x823c4 bnez a1; for k18 <> 0, 0x82554 andi a2,s4,7, 0x82558 addi a2,a2,1 and 0x8255c blt a2,a1 go back to
     0x823c8 *)
  all: step.
  all: destruct SK18' as [C18|[C18 C18']].
  all: first [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C18); cbn [negb]
             | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k18) 0) ltac:(lia)); cbn [negb]; step; step; step;
               rewrite land7, (unsigned_lit (f + 18)) by lia;
               rewrite (lts_low ((f + 18) mod 8 + 1) k18 ltac:(lia)), (proj2 (Z.ltb_lt _ _) C18); cbn [negb] ].
  (* 0x823c8 addi a2,s0,58; 0x823cc srli a1,a2,3; 0x823d0 add a1,a1,s5 *)
  all: step.
  all: step; gen_shr (Z_to_bv 64 (f + 58)) g58 G58.
  all: rewrite (unsigned_lit (f + 58)) in G58 by lia.
  all: step; gen_addi g58 h58 H58.
  all: rewrite G58 in H58.
  all: pose proof RS58 as RH58; rewrite <- H58 in RH58.
  (* 0x823d4 lb a1,0(a1) *)
  all: pose proof (rdw0 _ h58 _ _ M58 H58) as R.
  all: step; clear R.
  (* 0x823d8 lhu a3,0(s4): the cell at f + 18 is the sum *)
  all: step.
  all: rewrite (fpbtail_zx16 (fr_sum b)) by (unfold fr_sum; apply be16_range).
  (* 0x823dc bnez a1; for k58 <> 0, 0x82568 andi a4,a2,7 and 0x8256c blt a4,a1 go back to 0x823e0 *)
  all: step.
  all: destruct SK58 as [C58|[C58 C58']].
  all: first [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C58); cbn [negb]
             | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k58) 0) ltac:(lia)); cbn [negb]; step; step;
               rewrite land7, (unsigned_lit (f + 58)) by lia;
               rewrite (lts_low ((f + 58) mod 8) k58 MB58), (proj2 (Z.ltb_lt _ _) C58); cbn [negb] ].
  (* 0x823e0 li a1,0; 0x823e4 xor a0,a0,a3; 0x823e8 seqz a0,a0 *)
  all: step; step; step.
  (* 0x823ec sb a0,0(a2): the cell at f + 58 is sum_matches *)
  all: step.
  all: try (rewrite fpbtail_le1_any; StepF.mem_after_store).
  (* 0x823f0 j 0x823f8; 0x823f8 mv a0,a1; 0x823fc .. 0x8241c ld ra, s0 .. s7 from the frame; 0x82420 addi sp,sp,80;
     0x82424 ret *)
  all: do 13 step.
  all: apply evtF_done.
  all: do 8 eexists.
  all: split; [reflexivity|].
  all: split; [exact MU|].
  all: split; [exact WM|].
  all: eapply fpbtail_rw_cells_ext; [exact HC|].
  all: unfold parse_cells; rewrite ?skipn_skipn; cbn [Nat.add].
  all: repeat match goal with |- (_ :: _) = (_ :: _) => f_equal end.
  all: f_equal; apply fpbtail_seqz_cell; [unfold fr_body_sum; apply sum16_range | unfold fr_sum; apply be16_range].
Qed.
