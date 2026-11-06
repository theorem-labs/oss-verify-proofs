(* Proof of fp_tail_stmt (diginet_frame_parse_segs.v): the image-A run of diginet_frame_parse (fuzz_frame.asan) from
   FP_SUMQ (0x82430) to its return at 0x82494.
     0x82430  beqz a3: body_len = 0 goes to 0x824a0 with a3 = 0 (the sum of no bytes);
     0x82434  a4 = 0, a0 = s1 + 30;
     0x8243c .. 0x82460  the body-sum loop over buf + 30 .. buf + 30 + body_len - 1: the shadow byte of a0 is loaded
              (`lb`), then the byte at a1 (`lbu`) is added to a4; a3 counts down, a0 and a1 step by one;
     0x82498  a3 = (a4 << 48) >> 48, the sum mod 2^16 (fr_body_sum);
     0x824a0 .. 0x824b4  the shadow byte of f + 56, then `sh a3, 56(s0)` (body_sum);
     0x824b8 .. 0x824d8  the shadow byte of f + 58, a0 = 0, a2 = seqz (a3 xor a2), `sb a2` at f + 58 (sum_matches);
     0x82478 .. 0x82494  ra and s0 .. s4 loaded from the frame at sq, sp = sq + 48, ret.
   Each shadow byte k comes from an addressable premise: k = 0, or (a mod 8) + size - 1 < k, which is the compare of
   the slow path (0x82468 / 0x8246c for the 1-byte load, 0x82650 .. 0x82658 for the 2-byte store, 0x82660 / 0x82664
   for the 1-byte store) that goes back to the access. So the calls at 0x82470 (errpath_load1), 0x8265c
   (errpath_store2) and 0x8266c (errpath_store1) are not reached. Every access lies in a range of an ExecF.rng premise:
   the frame at sq, the 64 bytes at f, the bytes at buf, and the shadow bytes of f and of buf. *)
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

(* ---- arithmetic of the cut to 16 bits and of sum_matches ---- *)

(* slli 48, then srli 48: the value mod 2^16. *)
Lemma fptail_shl48_shr48 : forall s,
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 s)) 48))) 48 = s mod 2^16.
Proof.
  intros s. rewrite (unsigned_lit_wrap s). rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit_wrap.
  rewrite Z.shiftr_div_pow2 by lia.
  replace ((s mod 2^64 * 2^48) mod 2^64) with ((s mod 2^64 * 2^48) mod (2^16 * 2^48)) by reflexivity.
  rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
  apply mod_mod_pow2. lia.
Qed.

(* xor of the two sums, then seqz, stored as one byte. *)
Lemma fptail_seqz_cell : forall x y, 0 <= x < 2^16 -> 0 <= y < 2^16 ->
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

Lemma fptail_le1_any : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma fptail_bytes_at_sub : forall m A l k n, bytes_at rsegs m A l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m A l k n H Hkn. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma fptail_rw_cells_ext : forall m A cs cs', rw_cells rsegs m A cs -> cs = cs' -> rw_cells rsegs m A cs'.
Proof. intros; subst; assumption. Qed.

(* The shadow byte of an application byte is not an application byte. *)
Lemma fptail_sh_not_app : forall x, app_mem x -> ~ app_mem (x / 8 + ASAN_K).
Proof.
  intros x H. unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* ... so it lies outside the 64 addressable bytes at p. *)
Lemma fptail_sh_outside : forall m p x, addressable m p 64 -> app_mem x ->
  outside [(p, p + 64)] (x / 8 + ASAN_K).
Proof.
  intros m p x (P0 & N0 & PE & AB) Ax. pose proof (fptail_sh_not_app x Ax) as N.
  cbn [outside]. split; [|exact I]. intros W. apply N.
  destruct (AB (x / 8 + ASAN_K - p) ltac:(lia)) as (Ay & _).
  replace (p + (x / 8 + ASAN_K - p)) with (x / 8 + ASAN_K) in Ay by lia. exact Ay.
Qed.

Lemma fptail_mrd_munch : forall W m m' a b, munch W m m' -> outside W a ->
  mrd rsegs m (wa a) = Some b -> 0 <= a < 2^64 -> mrd rsegs m' (wa a) = Some b.
Proof.
  intros W m m' a b MU Ho H Ha. unfold mrd in *. rewrite MU; [exact H|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* The shadow byte of x in [p, p + n) lies in the shadow range of [p, p + n). *)
Lemma fptail_sh_rng : forall RNG p n x, 0 <= p -> p <= x < p + n ->
  ExecF.rng RNG (p / 8 + 2147450880) ((p + n - 1) / 8 + 2147450880 - (p / 8 + 2147450880) + 1) ->
  ExecF.rng RNG (x / 8 + 2147450880) 1.
Proof. intros RNG p n x H0 Hx H. eapply rng_sub'; [exact H|]. Z.div_mod_to_equations. lia. Qed.

(* Two neighbouring bytes in one granule. *)
Lemma fptail_next_byte : forall a k, 0 <= a -> a mod 8 < k -> k <= 7 ->
  (a + 1) / 8 = a / 8 /\ (a + 1) mod 8 = a mod 8 + 1.
Proof. intros a k H0 H1 H2. split; Z.div_mod_to_equations; lia. Qed.

(* ---- the body-sum loop, 0x8243c .. 0x82464 ---- *)

Section Loop.
Variables (RNG : ExecF.footprint) (P : machine_state -> Prop) (m : word -> option byte) (A : Z)
  (body : list byte) (F : bvmap 5 word) (fc : bv 32)
  (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
Hypothesis HA : 0 <= A.
Hypothesis HAe : A + Z.of_nat (length body) <= 2 ^ 47.
(* For each byte of the body: its range and that of its shadow byte in the footprint, its value, and its shadow byte
   (0, or above the byte's place in its granule). *)
Hypothesis IX : forall j, (j < length body)%nat ->
  ExecF.rng RNG (A + Z.of_nat j) 1 /\ ExecF.rng RNG ((A + Z.of_nat j) / 8 + 2147450880) 1 /\
  mrd rsegs m (wa (A + Z.of_nat j)) = Some (nth j body (Z_to_bv 8 0)) /\
  exists kb : byte, mrd rsegs m (wa ((A + Z.of_nat j) / 8 + 2147450880)) = Some kb /\
    (bv_signed kb = 0 \/ (A + Z.of_nat j) mod 8 < bv_signed kb).

(* Name the register value bv_unsigned x + e as w (eqn E). *)
Ltac fptail_gen_add x w E :=
  lazymatch goal with |- context [Some (Z_to_bv 64 (bv_unsigned x + ?e))] =>
    remember (Z_to_bv 64 (bv_unsigned x + e)) as w eqn:E end.

Local Abbreviation ST pc a0 a1 a3 a4 a5 a6 :=
  (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 a1 x12 a3 a4 a5 a6 x17 x18 (Z_to_bv 64 2147450880) x20
           x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* One pass, 0x8243c -> 0x82460: the checked load of byte i, added to a4. *)
Lemma fptail_iter : forall (i : nat) (x10 x11 x13 x14 x15 x16 : word),
  (i < length body)%nat ->
  bv_unsigned x10 = A + Z.of_nat i -> bv_unsigned x11 = A + Z.of_nat i ->
  1 <= bv_unsigned x13 -> bv_unsigned x14 = sum_bytes (firstn i body) ->
  (forall y10 y11 y13 y14 y15 y16 : word,
     bv_unsigned y10 = A + Z.of_nat i + 1 -> bv_unsigned y11 = A + Z.of_nat i + 1 ->
     bv_unsigned y13 = bv_unsigned x13 - 1 -> bv_unsigned y14 = sum_bytes (firstn (S i) body) ->
     ExecF.evtF rsegs RNG P (ST 0x8badc y10 y11 y13 y14 y15 y16)) ->
  ExecF.evtF rsegs RNG P (ST 0x8bab8 x10 x11 x13 x14 x15 x16).
Proof.
  intros i x10 x11 x13 x14 x15 x16 Hi E10 E11 E13 E14 K.
  destruct (IX i Hi) as (RB & RS & MB & kb & MK & SK).
  pose proof (Z.mod_pos_bound (A + Z.of_nat i) 8 ltac:(lia)) as MB8.
  assert (SB : 0 <= sum_bytes (firstn i body) <= 255 * Z.of_nat i)
    by (pose proof (sum_bytes_range (firstn i body)) as SR; rewrite length_firstn in SR; lia).
  pose proof (byte_range (nth i body (Z_to_bv 8 0))) as BR.
  pose proof (u64_range x13) as R13.
  (* 0x8243c srli a5,a0,3; 0x82440 add a5,a5,s3 *)
  step. gen_shr x10 g G. rewrite E10 in G.
  step. gen_addi g h Hh. rewrite G in Hh.
  pose proof RS as RH. rewrite <- Hh in RH.
  (* 0x82444 lb a5,0(a5) *)
  pose proof (rdw0 m h _ _ MK Hh) as R. step. clear R.
  (* 0x82448 bnez a5; for kb <> 0, 0x82468 andi a6,a0,7 and 0x8246c blt a6,a5 go back to 0x8244c *)
  step.
  destruct SK as [C|C].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed kb) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, E10, (lts_low ((A + Z.of_nat i) mod 8) kb MB8), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  (* 0x8244c lbu a5,0(a1) *)
  all: pose proof RB as RW; rewrite <- E11 in RW.
  all: pose proof (rdw0 m x11 _ _ MB E11) as R; step; clear R.
  (* 0x82450 addi a3,a3,-1; 0x82454 addi a0,a0,1 *)
  all: step; gen_addi x13 n13 U3.
  all: step; gen_addi x10 n10 U0.
  (* 0x82458 add a4,a4,a5 *)
  all: step.
  all: fptail_gen_add x14 n14 E4.
  all: assert (U4 : bv_unsigned n14 = sum_bytes (firstn (S i) body))
         by (rewrite E4, (sum_bytes_firstn_S body i Hi), <- E14; unfold at8, bz, b8, zxb;
             rewrite ?zxb_u; apply unsigned_lit; lia).
  all: clear E4.
  (* 0x8245c addi a1,a1,1 *)
  all: step; gen_addi x11 n11 U1.
  all: apply K; lia.
Qed.

(* The loop from byte i with k + 1 bytes left, to the cut at 0x82498 with a4 = the sum of the body. *)
Lemma fptail_loop : forall (k i : nat) (x10 x11 x13 x14 x15 x16 : word),
  (i + S k = length body)%nat ->
  bv_unsigned x10 = A + Z.of_nat i -> bv_unsigned x11 = A + Z.of_nat i ->
  bv_unsigned x13 = Z.of_nat (S k) -> bv_unsigned x14 = sum_bytes (firstn i body) ->
  (forall y10 y11 y13 y14 y15 y16 : word, bv_unsigned y14 = sum_bytes body ->
     ExecF.evtF rsegs RNG P (ST 0x8bb14 y10 y11 y13 y14 y15 y16)) ->
  ExecF.evtF rsegs RNG P (ST 0x8bab8 x10 x11 x13 x14 x15 x16).
Proof.
  intros k. induction k as [|k IH]; intros i x10 x11 x13 x14 x15 x16 Hk E10 E11 E13 E14 K.
  - apply (fptail_iter i x10 x11 x13 x14 x15 x16); [lia | exact E10 | exact E11 | lia | exact E14 |].
    intros y10 y11 y13 y14 y15 y16 U10 U11 U13 U14.
    (* 0x82460 bnez a3: a3 = 0; 0x82464 j 0x82498 *)
    step. if_cases HZ; zify_cond HZ.
    + exfalso. first [lia | rewrite ?unsigned_lit_wrap in HZ; Z.div_mod_to_equations; lia].
    + step. apply (K y10 y11 y13 y14 y15 y16). rewrite firstn_all2 in U14 by lia. exact U14.
  - apply (fptail_iter i x10 x11 x13 x14 x15 x16); [lia | exact E10 | exact E11 | lia | exact E14 |].
    intros y10 y11 y13 y14 y15 y16 U10 U11 U13 U14.
    (* 0x82460 bnez a3: a3 <> 0, back to 0x8243c *)
    step. if_cases HZ; zify_cond HZ.
    + apply (IH (S i) y10 y11 y13 y14 y15 y16); [lia | lia | lia | lia | exact U14 | exact K].
    + exfalso. first [lia | rewrite ?unsigned_lit_wrap in HZ; Z.div_mod_to_equations; lia].
Qed.

End Loop.

(* ---- the run FP_SUMQ -> the return ---- *)

Theorem fp_tail_holds : fp_tail_stmt.
Proof.
  unfold fp_tail_stmt.
  intros RNG ra sq gp tp t0 t1 t2 a0 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c4 c3 c2 c1 c0 cra
    F fc m buf f b fj LFJ PRE FR SQB DSQ RSQ.
  destruct PRE as (FC0 & Hb0 & Hbe & Hf0 & Hfe & BB & HC & CS & DBF & ADB & ADF & RB & RF & RSB & RSF).
  fp_lits.
  unfold FP_FRAME in *. unfold fp_fr in FR. unfold fp_hdr_cells in HC.
  unfold fp_shrng, shadow_addr in RSB, RSF. unfold ASAN_K in *.
  pose proof (fr_body_len_ok b FC0) as (BL0 & PL0 & BLe).
  pose proof (length_fr_body b FC0) as LFB.
  pose proof (u64_range sq) as Rsq.
  clear CS LFJ.
  (* the shadow bytes of f + 56 (and f + 57, the same granule when the 2-byte check takes the slow path) and f + 58 *)
  pose proof ADF as (Pf & Nf & PEf & ABf).
  unfold APPMEM_END in PEf.
  destruct (ABf 56 ltac:(lia)) as (AP56 & k56 & MK56 & SK56).
  destruct (ABf 57 ltac:(lia)) as (_ & k57 & MK57 & SK57).
  destruct (ABf 58 ltac:(lia)) as (AP58 & k58 & MK58 & SK58).
  clear ABf.
  unfold shadow_addr, shadow_ok, ASAN_K in MK56, SK56, MK57, SK57, MK58, SK58.
  pose proof (Z.mod_pos_bound (f + 56) 8 ltac:(lia)) as MB56.
  pose proof (Z.mod_pos_bound (f + 58) 8 ltac:(lia)) as MB58.
  assert (SK56' : bv_signed k56 = 0 \/ ((f + 56) mod 8 + 1 < bv_signed k56 /\ bv_signed k56 <= 7)).
  { destruct SK56 as [C|[C1 C2]]; [left; exact C|right].
    destruct (fptail_next_byte (f + 56) (bv_signed k56) ltac:(lia) C1 C2) as (E57 & M57).
    replace (f + 57) with (f + 56 + 1) in MK57, SK57 by lia.
    rewrite E57, MK56 in MK57. injection MK57 as E. subst k57.
    rewrite M57 in SK57. lia. }
  clear SK56 MK57 SK57.
  assert (R58 : 0 <= (f + 58) / 8 + 2147450880 < 2^64) by (clear - Hf0 Hfe; Z.div_mod_to_equations; lia).
  pose proof (fptail_sh_outside m f (f + 58) ADF AP58) as O58. unfold ASAN_K in O58.
  pose proof (fptail_sh_rng RNG f 64 (f + 56) ltac:(lia) ltac:(lia) RSF) as RS56.
  pose proof (fptail_sh_rng RNG f 64 (f + 58) ltac:(lia) ltac:(lia) RSF) as RS58.
  clear RSF ADF Pf Nf AP56 AP58.
  pose proof (munch_refl [(f, f + 64)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x824a0 -> the return, with a3 = body_sum *)
  lazymatch goal with |- ExecF.evtF _ _ ?Q _ =>
  assert (TAIL : forall x10 x11 x13 x14 x15 x16 : word, x13 = Z_to_bv 64 (fr_body_sum b) ->
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra sq gp tp t0 t1 t2 (Z_to_bv 64 f) (Z_to_bv 64 buf) x10 x11 (Z_to_bv 64 (fr_sum b)) x13 x14 x15 x16
               a7 s2 (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8bb1c) fc None m (seg_rom rsegs))) end.
  { intros x10 x11 x13 x14 x15 x16 ->.
    clear BB ADB RB RSB DBF.
    (* 0x824a0 addi a0,s0,56; 0x824a4 srli a1,a0,3; 0x824a8 add a1,a1,s3 *)
    step.
    step. gen_shr (Z_to_bv 64 (f + 56)) g56 G56. rewrite (unsigned_lit (f + 56)) in G56 by lia.
    step. gen_addi g56 h56 H56. rewrite G56 in H56.
    pose proof RS56 as RH56. rewrite <- H56 in RH56.
    (* 0x824ac lb a1,0(a1) *)
    pose proof (rdw0 m h56 _ _ MK56 H56) as R. step. clear R.
    (* 0x824b0 bnez a1; for k56 <> 0, 0x82650 andi a4,a0,7, 0x82654 addi a4,a4,1 and 0x82658 blt a4,a1 go back to
       0x824b4 *)
    step.
    destruct SK56' as [C|[C C']].
    1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k56) 0) ltac:(lia)); cbn [negb]; step; step; step;
       rewrite land7, (unsigned_lit (f + 56)) by lia;
       rewrite (lts_low ((f + 56) mod 8 + 1) k56 ltac:(lia)), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    (* 0x824b4 sh a3,56(s0): the cell at f + 56 is body_sum *)
    all: step.
    all: lazymatch type of MU with munch _ _ ?m1 =>
           pose proof (fptail_mrd_munch _ m m1 _ _ MU O58 MK58 R58) as M58 end.
    (* 0x824b8 addi a1,s0,58; 0x824bc srli a0,a1,3; 0x824c0 add a0,a0,s3 *)
    all: step.
    all: step; gen_shr (Z_to_bv 64 (f + 58)) g58 G58.
    all: rewrite (unsigned_lit (f + 58)) in G58 by lia.
    all: step; gen_addi g58 h58 H58.
    all: rewrite G58 in H58.
    all: pose proof RS58 as RH58; rewrite <- H58 in RH58.
    (* 0x824c4 lb a0,0(a0) *)
    all: lazymatch type of MU with munch _ _ ?m1 => pose proof (rdw0 m1 h58 _ _ M58 H58) as R end.
    all: step; clear R.
    (* 0x824c8 bnez a0; for k58 <> 0, 0x82660 andi a4,a1,7 and 0x82664 blt a4,a0 go back to 0x824cc *)
    all: step.
    all: destruct SK58 as [C58|[C58 C58']].
    all: first [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C58); cbn [negb]
               | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k58) 0) ltac:(lia)); cbn [negb]; step; step;
                 rewrite land7, (unsigned_lit (f + 58)) by lia;
                 rewrite (lts_low ((f + 58) mod 8) k58 MB58), (proj2 (Z.ltb_lt _ _) C58); cbn [negb] ].
    (* 0x824cc li a0,0; 0x824d0 xor a2,a3,a2; 0x824d4 seqz a2,a2 *)
    all: step; step; step.
    (* 0x824d8 sb a2,0(a1): the cell at f + 58 is sum_matches *)
    all: step.
    all: try (rewrite fptail_le1_any; StepF.mem_after_store).
    (* 0x824dc j 0x82478; 0x82478 .. 0x8248c ld ra, s0 .. s4 from the frame; 0x82490 addi sp,sp,48; 0x82494 ret *)
    all: do 9 step.
    all: apply evtF_done.
    all: do 8 eexists.
    all: split; [reflexivity|].
    all: split; [exact MU|].
    all: split; [exact WM|].
    all: eapply fptail_rw_cells_ext; [exact HC|].
    all: unfold parse_cells; rewrite ?skipn_skipn; cbn [Nat.add].
    all: repeat match goal with |- (_ :: _) = (_ :: _) => f_equal end.
    all: f_equal; apply fptail_seqz_cell; [unfold fr_body_sum; apply sum16_range | unfold fr_sum; apply be16_range]. }
  (* the body bytes and their shadow bytes *)
  assert (IX : forall j, (j < length (fr_body b))%nat ->
    ExecF.rng RNG (buf + 30 + Z.of_nat j) 1 /\ ExecF.rng RNG ((buf + 30 + Z.of_nat j) / 8 + 2147450880) 1 /\
    mrd rsegs m (wa (buf + 30 + Z.of_nat j)) = Some (nth j (fr_body b) (Z_to_bv 8 0)) /\
    exists kb : byte, mrd rsegs m (wa ((buf + 30 + Z.of_nat j) / 8 + 2147450880)) = Some kb /\
      (bv_signed kb = 0 \/ (buf + 30 + Z.of_nat j) mod 8 < bv_signed kb)).
  { intros j Hj. rewrite LFB in Hj.
    pose proof (fptail_bytes_at_sub _ _ _ 30 (Z.to_nat (fr_body_len b)) BB ltac:(lia)) as HB30.
    change (Z.of_nat 30) with 30 in HB30.
    change (firstn (Z.to_nat (fr_body_len b)) (skipn 30 b)) with (fr_body b) in HB30.
    pose proof (bytes_nth m _ _ j HB30 ltac:(rewrite LFB; lia)) as MBj.
    pose proof ADB as (_ & _ & _ & ABb).
    destruct (ABb (30 + Z.of_nat j) ltac:(lia)) as (_ & kb & MKj & SKj).
    unfold shadow_addr, shadow_ok, ASAN_K in MKj, SKj.
    replace (buf + (30 + Z.of_nat j)) with (buf + 30 + Z.of_nat j) in MKj, SKj by lia.
    split; [|split; [|split]].
    - eapply rng_sub'; [exact RB | lia].
    - eapply fptail_sh_rng; [| | exact RSB]; lia.
    - exact MBj.
    - exists kb. split; [exact MKj|]. destruct SKj as [C|[C _]]; [left|right]; exact C. }
  clear BB ADB RB RSB MK56 MK58 O58 R58 RS56 RS58 SK56' SK58 MB56 MB58.
  (* 0x82430 beqz a3 *)
  step. if_cases HZ; zify_cond HZ.
  - (* body_len = 0: 0x824a0 with a3 = 0, the sum of no bytes *)
    assert (BZ : fr_body_len b = 0)
      by (clear - HZ BL0 BLe Hbe Hb0; first [lia | rewrite ?unsigned_lit_wrap in HZ; Z.div_mod_to_equations; lia]).
    apply TAIL. unfold fr_body_sum, fr_body. rewrite BZ. reflexivity.
  - assert (BNZ : fr_body_len b <> 0)
      by (clear - HZ BL0 BLe Hbe Hb0; first [lia | rewrite ?unsigned_lit_wrap in HZ; Z.div_mod_to_equations; lia]).
    (* 0x82434 li a4,0; 0x82438 addi a0,s1,30 *)
    step. step.
    eapply fptail_loop with (A := buf + 30) (body := fr_body b) (k := (length (fr_body b) - 1)%nat) (i := 0%nat).
    + lia.
    + rewrite LFB. lia.
    + exact IX.
    + rewrite LFB. lia.
    + rewrite unsigned_lit by lia. lia.
    + rewrite unsigned_lit by lia. lia.
    + rewrite unsigned_lit by lia. rewrite LFB. lia.
    + reflexivity.
    + (* 0x82498 slli a3,a4,48; 0x8249c srli a3,a3,48: the sum mod 2^16 *)
      intros y10 y11 y13 y14 y15 y16 U14.
      rewrite <- (Z_to_bv_bv_unsigned y14), U14.
      step. step. rewrite fptail_shl48_shr48.
      apply TAIL. reflexivity.
Qed.
