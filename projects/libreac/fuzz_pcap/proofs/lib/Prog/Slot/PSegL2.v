From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel bcmp_c
  pcap_source_struct pcap_source_struct_next pcap_source_next_lib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PWalkDef PSegL.
Import ListNotations.
Open Scope Z_scope.

(* 0x12ecc-0x12ef0: a0 = 1 when the record at Q carries a VLAN tag, else 0. *)
Lemma pcap_L_tag : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
                          (sw : bool) (Fc : list byte) (Q b : Z),
  s0 = wz (b + Q) -> s7 = wz (bv_swrap 32 (incl sw Fc Q)) -> 0 <= Q ->
  Q + 16 + incl sw Fc Q <= Z.of_nat (length Fc) -> bytes_at rsegs m b Fc ->
  evt rsegs
    (fun ms' => exists a1' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (if tagged sw Fc Q then 1 else 0)) a1' a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x2ec)%Z)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x2c8)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sw Fc Q b E0 E7 HQ HL HB.
  subst s0 s7. unfold wz in *.
  pose proof (hw_range sw Fc Q 8) as RI. change (hw sw Fc Q 8) with (incl sw Fc Q) in RI.
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BB.
  do 2 step.
  rewrite ltu_swrap by lia.
  destruct (Z_lt_le_dec (incl sw Fc Q) 18) as [T18|T18].
  - rewrite (proj2 (Z.ltb_lt _ _) T18). cbv iota.
    assert (TG : tagged sw Fc Q = false) by (unfold tagged; bool_dec; reflexivity).
    step. apply evt_done. eexists. rewrite TG. reflexivity.
  - rewrite (proj2 (Z.ltb_ge _ _) T18). cbv iota.
    pose proof (bytes_at_byte m b Fc (Q + 28) HB ltac:(lia)) as HB28.
    pose proof (bytes_at_byte m b Fc (Q + 29) HB ltac:(lia)) as HB29.
    assert (EZ28 : bv_unsigned (zxb (nth (Z.to_nat (Q + 28)) Fc (Z_to_bv 8 0))) = fb Fc (Q + 28))
      by (rewrite zxb_val; reflexivity).
    assert (EZ29 : bv_unsigned (zxb (nth (Z.to_nat (Q + 29)) Fc (Z_to_bv 8 0))) = fb Fc (Q + 29))
      by (rewrite zxb_val; reflexivity).
    do 3 step.
    destruct (Z.eq_dec (fb Fc (Q + 28)) 129) as [B28|B28].
    + if_false.
      do 2 step.
      assert (EV : v_sltiu (zxb (nth (Z.to_nat (Q + 29)) Fc (Z_to_bv 8 0))) 1 =
                   wz (if tagged sw Fc Q then 1 else 0)).
      { rewrite v_sltiu_b2z, EZ29. change (bv_wrap 64 1) with 1. unfold tagged, wz.
        rewrite (proj2 (Z.leb_le _ _) T18), (proj2 (Z.eqb_eq _ _) B28). cbn [andb].
        assert (R29 : 0 <= fb Fc (Q + 29) < 256) by (unfold fb; apply byte_range).
        destruct (Z.eq_dec (fb Fc (Q + 29)) 0) as [Z0|Z0].
        - rewrite Z0. reflexivity.
        - rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
      step. apply evt_done. eexists. rewrite EV. reflexivity.
    + if_true.
      assert (TG : tagged sw Fc Q = false) by (unfold tagged; bool_dec; reflexivity).
      step. apply evt_done. eexists. rewrite TG. reflexivity.
Qed.

(* The time stamp of a record: mulhu of (sec << 32) with 10^6 * 2^32 gives sec * 10^6 for sec < 2^32. *)
Lemma ts_val : forall s u, 0 <= s < 2 ^ 32 -> 0 <= u < 2 ^ 32 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 s)) 32)) *
                        bv_unsigned (Z_to_bv 64 (1000000 * 2 ^ 32))) 64 +
              Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 u)) 32))) 32) =
  Z_to_bv 64 (s * 1000000 + u).
Proof.
  intros s u Hs Hu. f_equal.
  rewrite (unsigned_lit s), (unsigned_lit u) by lia. rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (s * 2 ^ 32)), (unsigned_lit (u * 2 ^ 32)), (unsigned_lit (1000000 * 2 ^ 32)) by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  replace (s * 2 ^ 32 * (1000000 * 2 ^ 32)) with (s * 1000000 * 2 ^ 64) by ring.
  rewrite !Z.div_mul by lia. reflexivity.
Qed.

(* s8 after the record: Q + ((incl + 16) mod 2^32), with incl small. *)
Lemma s8_next : forall Q I, 0 <= I <= 2040 ->
  Z_to_bv 64 (Q + Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_swrap 32 I + 16))) 32))) 32) =
  Z_to_bv 64 (Q + 16 + I).
Proof.
  intros Q I HI. f_equal.
  assert (E : bv_swrap 32 I = I) by (rewrite swrap32_eq; rewrite Z.mod_small by lia; lia).
  rewrite E, (unsigned_lit (I + 16)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit ((I + 16) * 2 ^ 32)) by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. lia.
Qed.

(* State at the call of pcap_source_next from the record loop (pc 0x132a0, return to 0x13044). *)
Definition QL (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo sp_h cap buf b first q' i : Z) (ms' : machine_state) : Prop :=
  exists (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
          x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                  x27 x28 x29 x30 x31) F (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_next)) fc None m' (seg_rom rsegs) /\
    x1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x440)%Z) /\ x2 = sp /\ x3 = gp /\ x4 = tp /\ x9 = wz cap /\ x10 = wz (sp_h + 32) /\
    x11 = wz buf /\ x12 = wz cap /\ x13 = wz (sp_h + 24) /\ x18 = wz buf /\ x19 = wz first /\ x20 = wz b /\
    x21 = wz 0xff00 /\ x22 = wz (symaddr Symbols.Plain.s_g_file_len) /\ x24 = wz q' /\ x25 = wz (i + 1) /\ x27 = wz (1000000 * 2 ^ 32) /\
    munch [(sp_h + 24, sp_h + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (sp_h + 160) /\
    rw_cells rsegs m' (sp_h + 24) [C8 (wz (-1))].

(* 0x12f6c-0x13040: the time stamp check, ts := -1, s8 := the next record, call pcap_source_next. *)
Lemma pcap_L_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                           t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
                           (sw : bool) (Fc : list byte) (lo sp_h cap buf b first Q i swz : Z),
  bv_unsigned sp = sp_h -> s0 = wz (b + Q) -> s1 = wz cap -> s2 = wz buf -> s3 = wz first -> s4 = wz b ->
  s5 = wz 0xff00 -> s6 = wz (symaddr Symbols.Plain.s_g_file_len) -> s7 = wz (bv_swrap 32 (incl sw Fc Q)) -> s8 = wz Q -> s9 = wz (i + 1) ->
  s10 = wz swz -> s11 = wz (1000000 * 2 ^ 32) -> sw = (swz =? 1) -> (swz = 0 \/ swz = 1) ->
  0 <= Q -> Q + 16 <= Z.of_nat (length Fc) -> 1 <= incl sw Fc Q <= 2040 ->
  bytes_at rsegs m b Fc -> rw_cells rsegs m (sp_h + 24) [C8 (wz (rec_ts sw Fc Q))] ->
  munch [(sp_h + 24, sp_h + 32)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (sp_h + 160) ->
  evt rsegs (QL sp gp tp F fc m0 lo sp_h cap buf b first (Q + 16 + incl sw Fc Q) i)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x368)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m sw Fc lo sp_h cap buf b first Q i swz HSP E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 ESW HSW
    HQ HQ16 HI HB HTS MU WM MI ST.
  subst sp_h s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11. unfold wz in *.
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (hw_range sw Fc Q 0) as R0. pose proof (hw_range sw Fc Q 4) as R4.
  pose proof (bytes_at_byte m b Fc (Q + 0) HB ltac:(lia)) as HB0.
  pose proof (bytes_at_byte m b Fc (Q + 1) HB ltac:(lia)) as HB1.
  pose proof (bytes_at_byte m b Fc (Q + 2) HB ltac:(lia)) as HB2.
  pose proof (bytes_at_byte m b Fc (Q + 3) HB ltac:(lia)) as HB3.
  pose proof (bytes_at_byte m b Fc (Q + 4) HB ltac:(lia)) as HB4.
  pose proof (bytes_at_byte m b Fc (Q + 5) HB ltac:(lia)) as HB5.
  pose proof (bytes_at_byte m b Fc (Q + 6) HB ltac:(lia)) as HB6.
  pose proof (bytes_at_byte m b Fc (Q + 7) HB ltac:(lia)) as HB7.
  replace (b + (Q + 0)) with (b + Q) in HB0 by lia.
  (destruct HSW as [SW|SW]; subst swz;
   [do 11 step; if_true | do 11 step; if_false; do 7 step]);
  rep_reg 10 (Z_to_bv 64 (hw sw Fc Q 0)) ltac:(rewrite ESW; hw_eq);
  [do 11 step; if_true | do 11 step; if_false; do 7 step];
  rep_reg 12 (Z_to_bv 64 (hw sw Fc Q 4)) ltac:(rewrite ESW; hw_eq).
  all: do 3 step; do 2 step; step.
  all: rewrite (ts_val (hw sw Fc Q 0) (hw sw Fc Q 4)) by lia;
       change (hw sw Fc Q 0 * 1000000 + hw sw Fc Q 4) with (rec_ts sw Fc Q).
  all: step; if_false.
  all: do 11 step.
  all: rewrite (s8_next Q (incl sw Fc Q)) by lia;
       assert (EM1 : Z_to_bv 64 18446744073709551615 = wz (-1)) by (apply bv_eq; reflexivity);
       rewrite EM1 in HTS;
       finish; reflexivity.
Qed.
