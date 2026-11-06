(* Shared pieces of the two receiving ops of the ubsan LLVMFuzzerTestOneInput (ops 0 and 8,
   U/Prog/T/LLVMFuzzerTestOneInput_op0.v and _op8.v): the cursor model (fuzz_u8 / fuzz_record on a cursor of
   0, 1 and >= 2 bytes), the model's op as receive_m, the post of llvm_op_recv_stmt built at receive's entry
   0x14d1c, and the return continuation 0x13f70 `mv s3, s0; j 0x14574` to the latch. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- words and bytes *)

Lemma lr_eqb0 : forall z, 0 <= z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = (z =? 0).
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma lr_eqb : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma lr_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* the UBSan check `bgeu s1, sX -> trap` (s1 = 1) after `addi sX, p, 1`: not taken since 1 < sX *)
Ltac lr_notrap :=
  rewrite lr_ltu by lia;
  lazymatch goal with |- context [1 <? ?e] => replace (1 <? e) with true by (symmetry; apply Z.ltb_lt; lia) end;
  cbn [negb].

Lemma lr_byte : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma lr_at8 : forall D i, 0 <= at8 D i < 256.
Proof. intros D i. unfold at8, bz. apply lr_byte. Qed.

(* lbu leaves zxb b in rd; slli reads it back as bv_unsigned *)
Lemma lr_zxb : forall b, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply unsigned_lit. pose proof (lr_byte b). lia. Qed.

(* the two bytes of fuzz_u16 as the code assembles them: `slli a1, a1, 8; or a1, a1, a0` *)
Lemma lr_lor : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> Z.lor (Z.shiftl hi 8) lo = lo + 256 * hi.
Proof. intros lo hi Hl Hh. rewrite Z.lor_comm. apply lor_shiftl8_add; lia. Qed.

Lemma lr_sub1 : forall (D : list byte) k, (k < length D)%nat -> firstn 1 (skipn k D) = [nth k D (b8 0)].
Proof.
  induction D as [|d D IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

(* one byte of the input buffer, as the kit's load hook reads it *)
Lemma lr_read : forall m data D k, bytes_at rsegs m data D -> 0 <= k -> k < Z.of_nat (length D) ->
  ov_read_bytes rsegs m (wa (data + k)) 1 = Some [nth (Z.to_nat k) D (b8 0)].
Proof.
  intros m data D k HD Hk Hl.
  rewrite (bytes_at_read rsegs m data D k 1 HD Hk) by lia.
  rewrite lr_sub1 by lia. reflexivity.
Qed.

Lemma lr_bsub : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  bytes_at rsegs m (a + k) (sub bs k n).
Proof.
  intros m a bs k n (Ha & Hl & H) Hk Hn.
  assert (Ln : length (sub bs k n) = n) by (apply length_sub; lia).
  split; [lia|]. split; [rewrite Ln; lia|].
  intros i Hi. rewrite Ln in Hi. rewrite ne_sub by lia.
  replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply H. lia.
Qed.

(* ---------------------------------------------------------------- the cursor model *)

Lemma lr_u8 : forall D o n, n <> 0 -> fuzz_u8_m D (FuzzIn o n) = (FuzzIn (o + 1) (n - 1), at8 D (Z.to_nat o)).
Proof. intros D o n Hn. unfold fuzz_u8_m. cbn [fi_n fi_off]. destruct (Z.eqb_spec n 0); [lia | reflexivity]. Qed.

Lemma lr_u8_0 : forall D o, fuzz_u8_m D (FuzzIn o 0) = (FuzzIn o 0, 0).
Proof. intros D o. reflexivity. Qed.

(* fuzz_record on an empty cursor, on a cursor of one byte, and on a cursor of two or more bytes *)
Lemma lr_rec0 : forall D o, fuzz_record_m D (FuzzIn o 0) = (FuzzIn o 0, o, 0).
Proof.
  intros D o. unfold fuzz_record_m, fuzz_u16_m. rewrite lr_u8_0. cbv beta iota. rewrite lr_u8_0. cbv beta iota.
  unfold fuzz_take_m. cbn. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma lr_rec1 : forall D o, fuzz_record_m D (FuzzIn o 1) = (FuzzIn (o + 1) 0, o + 1, 0).
Proof.
  intros D o. unfold fuzz_record_m, fuzz_u16_m. rewrite (lr_u8 D o 1) by lia. cbv beta iota.
  replace (1 - 1) with 0 by lia. rewrite lr_u8_0. cbv beta iota.
  unfold fuzz_take_m. cbn [fi_off fi_n].
  lazymatch goal with |- context [if ?w <? 0 then _ else _] =>
    lazymatch w with ?x mod ?y => pose proof (Z.mod_pos_bound x y ltac:(lia)) as Hw end;
    destruct (Z.ltb_spec w 0) as [Hlt|_]; [lia|] end.
  cbv iota. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma lr_rec2 : forall D o n t, 2 <= n ->
  t = (if Z.lor (Z.shiftl (at8 D (Z.to_nat (o + 1))) 8) (at8 D (Z.to_nat o)) <? n - 2
       then Z.lor (Z.shiftl (at8 D (Z.to_nat (o + 1))) 8) (at8 D (Z.to_nat o)) else n - 2) ->
  fuzz_record_m D (FuzzIn o n) = (FuzzIn (o + 2 + t) (n - 2 - t), o + 2, t).
Proof.
  intros D o n t Hn Ht. unfold fuzz_record_m, fuzz_u16_m.
  rewrite (lr_u8 D o n) by lia. cbv beta iota.
  rewrite (lr_u8 D (o + 1) (n - 1)) by lia. cbv beta iota.
  unfold fuzz_take_m. cbn [fi_off fi_n].
  pose proof (lr_at8 D (Z.to_nat o)) as R0. pose proof (lr_at8 D (Z.to_nat (o + 1))) as R1.
  rewrite (lr_lor (at8 D (Z.to_nat o)) (at8 D (Z.to_nat (o + 1)))) in Ht by lia.
  rewrite (Z.lor_comm (at8 D (Z.to_nat o)) (Z.shiftl (at8 D (Z.to_nat (o + 1))) 8)).
  rewrite (lr_lor (at8 D (Z.to_nat o)) (at8 D (Z.to_nat (o + 1)))) by lia.
  rewrite (Z.mod_small (at8 D (Z.to_nat o) + 256 * at8 D (Z.to_nat (o + 1))) (2 ^ 16)) by lia.
  replace (n - 1 - 1) with (n - 2) by lia. replace (o + 1 + 1) with (o + 2) by lia.
  rewrite <- Ht. reflexivity.
Qed.

(* the model's op 0 / op 8 is receive_m of the record's bytes *)
Lemma lr_model0 : forall I B A D c k c1 b c2 off n,
  fuzz_u8_m D c = (c1, b) -> b mod 9 = 0 -> fuzz_record_m D c1 = (c2, off, n) ->
  LLVMFuzzerTestOneInput_op_m I B A D c k =
  match receive_m I B (A k) (sub D off (Z.to_nat n)) 0 0 with
  | Some (B1, _) => Some (B1, (c2, S k))
  | None => None
  end.
Proof.
  intros I B A D c k c1 b c2 off n H1 H2 H3.
  unfold LLVMFuzzerTestOneInput_op_m. rewrite H1. cbv beta iota zeta. rewrite H2, Z.eqb_refl. cbv beta iota.
  rewrite H3. cbv beta iota. reflexivity.
Qed.

Lemma lr_model8 : forall I B A D c k c1 b c2 pf c3 off n,
  fuzz_u8_m D c = (c1, b) -> b mod 9 = 8 -> fuzz_u8_m D c1 = (c2, pf) -> fuzz_record_m D c2 = (c3, off, n) ->
  LLVMFuzzerTestOneInput_op_m I B A D c k =
  match receive_m I B (A k) (sub D off (Z.to_nat n)) 1 pf with
  | Some (B1, _) => Some (B1, (c3, S k))
  | None => None
  end.
Proof.
  intros I B A D c k c1 b c2 pf c3 off n H1 H2 H3 H4.
  unfold LLVMFuzzerTestOneInput_op_m. rewrite H1. cbv beta iota zeta. rewrite H2. cbn [Z.eqb Pos.eqb].
  rewrite H3. cbv beta iota. rewrite H4. cbv beta iota. reflexivity.
Qed.

(* ---------------------------------------------------------------- the post at receive's entry *)

(* the post of llvm_op_recv_stmt, as a named predicate *)
Definition recv_post (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte) (Sp lo ops : Z)
    (c : fuzz_in) (B : list byte) (F : bvmap 5 word) (fc : bv 32) (ms' : machine_state) : Prop :=
  exists (s0 s2 s3 s4 s5 s6 s7 : word) (p : Z) (bytes : list byte) (by_poll pf : Z) (c2 : fuzz_in),
    llvm_at_recv data D regs0 m0 Sp lo ops B LH_RET_RECV s0 s2 s3 s4 s5 s6 s7 p bytes by_poll pf F fc ms' /\
    (forall I A k, LLVMFuzzerTestOneInput_op_m I B A D c k =
       match receive_m I B (A k) bytes by_poll pf with
       | Some (B1, _) => Some (B1, (c2, S k))
       | None => None
       end) /\
    (forall m0' B' F' fc' ms'' (Q' : machine_state -> Prop), g_fail_next B' <= 1 ->
       llvm_ret data D regs0 m0' Sp lo ops B' LH_RET_RECV s0 s2 s3 s4 s5 s6 s7 F' fc' ms'' ->
       (forall ms3, llvm_latch data D regs0 m0' Sp lo ops c2 B' F' fc' ms3 -> evt rsegs Q' ms3) ->
       evt rsegs Q' ms'').

(* the return 0x13f70: mv s3, s0; j 0x14574 (the latch); s0 / s6 hold the cursor after the record *)
Lemma recv_ret : forall data D regs0 m0' Sp lo ops B' c2 s3 s5 s7 F' fc' ms'' (Q' : machine_state -> Prop),
  llvm_cursor D c2 ->
  llvm_ret data D regs0 m0' Sp lo ops B' LH_RET_RECV (Z_to_bv 64 (data + fi_off c2)) (Z_to_bv 64 0x39) s3
    (Z_to_bv 64 7) s5 (Z_to_bv 64 (fi_n c2)) s7 F' fc' ms'' ->
  (forall ms3, llvm_latch data D regs0 m0' Sp lo ops c2 B' F' fc' ms3 -> evt rsegs Q' ms3) ->
  evt rsegs Q' ms''.
Proof.
  intros data D regs0 m0' Sp lo ops B' c2 s3 s5 s7 F' fc' ms'' Q' HC2 H HK.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m &
                 j10 & jio & j60 & -> & HOPS & HM).
  unfold LH_RET_RECV.
  (* 0x13f70 mv s3, s0; 0x13f74 j 0x14574 *)
  step. step.
  apply HK. unfold llvm_latch. do 23 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [exact HC2|]. exact HM.
Qed.

(* the post, from the registers at receive's entry *)
Lemma recv_fin : forall data D regs0 m0 Sp lo ops c B F fc m j10 jio j60
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (roff rn rbp rpf : Z) (rc2 : fuzz_in),
  ra = Z_to_bv 64 LH_RET_RECV -> sp = Z_to_bv 64 Sp -> gp = reg_get regs0 3 -> tp = reg_get regs0 4 ->
  s1 = Z_to_bv 64 1 -> a0 = Z_to_bv 64 (data + roff) -> a1 = Z_to_bv 64 rn ->
  a2 = Z_to_bv 64 rbp -> a3 = Z_to_bv 64 rpf ->
  s8 = Z_to_bv 64 (W_BASE_UBSAN + OFF_M) -> s9 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next) ->
  s10 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) -> s11 = Z_to_bv 64 ops ->
  s0 = Z_to_bv 64 (data + fi_off rc2) -> s2 = Z_to_bv 64 0x39 -> s4 = Z_to_bv 64 7 ->
  s6 = Z_to_bv 64 (fi_n rc2) ->
  0 <= ops < OPS_MAX -> 0 <= roff -> 0 <= rn <= 65535 -> roff + rn <= Z.of_nat (length D) ->
  - 2 ^ 31 <= rbp < 2 ^ 31 -> 0 <= rpf < 2 ^ 32 -> llvm_cursor D rc2 ->
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60 ->
  (forall I A k, LLVMFuzzerTestOneInput_op_m I B A D c k =
     match receive_m I B (A k) (sub D roff (Z.to_nat rn)) rbp rpf with
     | Some (B1, _) => Some (B1, (rc2, S k))
     | None => None
     end) ->
  recv_post data D regs0 m0 Sp lo ops c B F fc
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 LH_RECV) fc None m (seg_rom rsegs)).
Proof.
  intros data D regs0 m0 Sp lo ops c B F fc m j10 jio j60 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 roff rn rbp rpf rc2
    Era Esp Egp Etp Es1 Ea0 Ea1 Ea2 Ea3 Es8 Es9 Es10 Es11 Es0 Es2 Es4 Es6
    HOPS Hoff Hrn Hlen Hbp Hpf HC2 HM HMOD.
  subst ra sp gp tp s1 a0 a1 a2 a3 s8 s9 s10 s11 s0 s2 s4 s6.
  exists (Z_to_bv 64 (data + fi_off rc2)), (Z_to_bv 64 0x39), s3, (Z_to_bv 64 7), s5, (Z_to_bv 64 (fi_n rc2)), s7,
    (data + roff), (sub D roff (Z.to_nat rn)), rbp, rpf, rc2.
  split; [|split; [exact HMOD|]].
  - assert (LS : length (sub D roff (Z.to_nat rn)) = Z.to_nat rn) by (apply length_sub; lia).
    pose proof HM as HM1. unfold llvm_mem in HM1. destruct HM1 as (HD0 & HDL & _ & HD & _).
    unfold llvm_at_recv. exists t0, t1, t2, a4, a5, a6, a7, t3, t4, t5, t6, m, j10, jio, j60.
    rewrite LS, Z2Nat.id by lia.
    split; [reflexivity|].
    split; [exact HOPS|]. split; [lia|]. split; [lia|].
    split; [apply lr_bsub; [exact HD | lia | rewrite Z2Nat.id by lia; lia]|].
    split; [lia|]. split; [lia|]. split; [lia|]. exact HM.
  - intros m0' B' F' fc' ms'' Q' _ HR HK.
    exact (recv_ret data D regs0 m0' Sp lo ops B' rc2 s3 s5 s7 F' fc' ms'' Q' HC2 HR HK).
Qed.

(* the side goals of recv_fin but the model's: register equations, bounds, the cursor, the memory invariant *)
Ltac lr_side HM0 :=
  first [ reflexivity | exact HM0 | (f_equal; cbn [fi_off fi_n]; lia)
        | (unfold llvm_cursor; cbn [fi_off fi_n]; lia) | lia ].

(* the length fuzz_take gives, the machine's t against the model's: the bound of the min as each side writes it *)
Ltac lr_teq Ht :=
  lazymatch goal with |- _ = (if _ <? ?r1 then _ else _) =>
    lazymatch type of Ht with _ = (if _ <? ?r2 then _ else _) =>
      replace r1 with r2 by lia end end;
  exact Ht.
