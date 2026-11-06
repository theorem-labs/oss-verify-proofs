(* text_of (plain, 0x15aa8): the run from the entry to the first exit, over a memory without
   read-only entries (mem_inv). It ends either at the `ret` of the table arm (tab_post), or at the
   `jal malloc` of the copy arm (call_post, at 0x15bf4 + 4 = the malloc entry 0x17514 with
   ra = 0x15bf8). memchr is a callee: its contract (lib/Prog/memchr_c.v) is a Section hypothesis.
   Every instruction is fetched and decoded from the loaded image by `step`. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memchr_c text_of_lem.
Import ListNotations.
Open Scope Z_scope.

Section Pro.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (A0 A1 C0 N : Z) (inp : list byte) (m0 : word -> option byte).
Hypothesis HMC : memchr_contract.

Local Notation W := [(bv_unsigned sp + -48, bv_unsigned sp); (A0, A0 + 16); (A1, A1 + 8)].

(* where things lie: the frame, the cursor (A0, 16 bytes), *own (A1, 8 bytes), the input (C0, N
   bytes) and the `texts` table (133104, 88 bytes) *)
Definition geo : Prop :=
  2 ^ 20 + 48 <= bv_unsigned sp < 2 ^ 63 /\
  0 <= A0 /\ A0 + 16 <= 2 ^ 64 /\ 0 <= A1 /\ A1 + 8 <= 2 ^ 64 /\
  (A0 + 16 <= bv_unsigned sp + -48 \/ bv_unsigned sp <= A0) /\
  (A1 + 8 <= bv_unsigned sp + -48 \/ bv_unsigned sp <= A1) /\
  (A1 + 8 <= A0 \/ A0 + 16 <= A1) /\
  (C0 + N <= A0 \/ A0 + 16 <= C0) /\ (C0 + N <= A1 \/ A1 + 8 <= C0) /\
  (A0 + 16 <= 133104 \/ 133104 + 88 <= A0) /\ (A1 + 8 <= 133104 \/ 133104 + 88 <= A1) /\
  133104 + 88 <= bv_unsigned sp + -48 /\
  Z.of_nat (length inp) = N /\ 0 <= C0 < 2 ^ 64 /\ 0 <= N < 2 ^ 64 /\ C0 + N <= 2 ^ 64.

Ltac geo_intro G :=
  destruct G as (GSP & GA0 & GA0' & GA1 & GA1' & DF0 & DF1 & D01 & DI0 & DI1 & DT0 & DT1 & DTF & LEN & GC0 & GN & GC0').

Definition tab_post (ms' : machine_state) : Prop :=
  exists (j : nat) sp' x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1 v1 v2 adv,
    ms' = MS (mkR ra sp' gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (tl_ptr j)) x11 x12 x13 x14 x15 x16 x17
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m1 (seg_rom rsegs)
    /\ bv_unsigned sp' = bv_unsigned sp /\ (j < 11)%nat
    /\ munch W m0 m1 /\ wmono rsegs m0 m1 /\ mem_inv rsegs m1
    /\ rw_cells rsegs m1 A0 [C8 v1; C8 v2] /\ bv_unsigned v1 = C0 + adv /\ bv_unsigned v2 = N - adv
    /\ 0 <= adv <= N
    /\ rw_cells rsegs m1 A1 [C8 (Z_to_bv 64 0)].

Definition call_post (ms' : machine_state) : Prop :=
  exists (d take n : Z) x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 m1 junk v1 v2,
    ms' = MS (mkR (Z_to_bv 64 0x15bf8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 A1)
                  x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x17514) fc None m1 (seg_rom rsegs)
    /\ bv_unsigned x9 = C0 + d /\ bv_unsigned x10 = n + 1 /\ bv_unsigned x18 = n
    /\ 1 <= d /\ 0 <= take /\ d + take <= N /\ take < 320
    /\ n = strnlen_res take (skipn (Z.to_nat d) inp)
    /\ rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ munch W m0 m1 /\ wmono rsegs m0 m1 /\ mem_inv rsegs m1
    /\ rw_cells rsegs m1 A0 [C8 v1; C8 v2] /\ bv_unsigned v1 = C0 + d + take /\ bv_unsigned v2 = N - d - take
    /\ rw_cells rsegs m1 A1 [C8 (Z_to_bv 64 0)]
    /\ bytes_at rsegs m1 C0 inp.

Ltac uz := first [ reflexivity | lia | (rewrite unsigned_lit by lia; lia) ].

(* the unsigned value of a `beqz` operand, so that if_true / if_false can decide it *)
Ltac br_u :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?e) (Z_to_bv 64 0) then _ else _) _ _ _ _) =>
      let H := fresh "U" in assert (H : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia)
  | _ => idtac
  end.

(* +0x88: the table arm, s = the selector byte (bit 7 clear) or 0 for an empty input *)
Lemma j_tab : forall (m : word -> option byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 v1 v2 : word)
    (s adv : Z) (junk : list byte),
  geo -> bv_unsigned x11 = s -> 0 <= s < 128 ->
  rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m A0 [C8 v1; C8 v2] -> bv_unsigned v1 = C0 + adv -> bv_unsigned v2 = N - adv -> 0 <= adv <= N ->
  rw_cells rsegs m A1 [C8 (Z_to_bv 64 0)] ->
  bytes_at rsegs m 133104 TL_TB ->
  munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs (fun ms => tab_post ms \/ call_post ms)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x15b30) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 v1 v2 s adv junk
    G H11 Hs FR CUR V1 V2 HADV OWN TXT MU WM MI.
  geo_intro G.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (TBL : Z.of_nat (length TL_TB) = 88) by reflexivity.
  assert (E11 : x11 = Z_to_bv 64 s) by (apply bv_eq; rewrite unsigned_lit by lia; exact H11).
  subst x11.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- context [Z_to_bv 64 (133104 + ?E)] =>
    let HE := fresh "HE" in
    assert (HE : E = 8 * (s mod 11));
    [ clear - Hs;
      lazymatch goal with |- ?L = _ =>
        let L' := eval pattern s in L in
        lazymatch L' with ?Fn _ =>
          apply (tl_zcheck Fn (fun z0 => 8 * (z0 mod 11)) 128); [vm_compute; reflexivity | lia] end end
    | rewrite HE; clear HE ] end.
  pose proof (Z.mod_pos_bound s 11 ltac:(lia)) as M11.
  assert (UT : bv_unsigned (Z_to_bv 64 (133104 + 8 * (s mod 11))) = 133104 + 8 * (s mod 11))
    by (apply unsigned_lit; lia).
  pose proof (tl_texts_read m (s mod 11) TXT ltac:(lia)) as RT.
  zstep.
  zstep. zstep.
  zstep. zstep. zstep. zstep. zstep.
  zstep. zstep.
  apply evt_done. left.
  exists (Z.to_nat (s mod 11)). do 19 eexists.
  split; [reflexivity|].
  split; [first [reflexivity | (rewrite unsigned_lit by lia; lia)]|].
  split; [lia|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact CUR|]. split; [exact V1|]. split; [exact V2|]. split; [exact HADV|]. exact OWN.
Qed.

(* +0x11c: s2 = take, the bytes the copy takes; the cursor is still at C0 + d *)
Lemma j_take : forall (m : word -> option byte)
    (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 v1 v2 : word) (d P R take : Z) (junk : list byte),
  geo -> 0 < C0 -> C0 + N <= bv_unsigned sp + -48 ->
  P = C0 + d -> R = N - d -> 1 <= d <= N -> 0 <= take <= R -> take < 320 ->
  rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m A0 [C8 v1; C8 v2] ->
  rw_cells rsegs m A1 [C8 (Z_to_bv 64 0)] ->
  bytes_at rsegs m C0 inp ->
  munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs (fun ms => tab_post ms \/ call_post ms)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 A1) (Z_to_bv 64 P) (Z_to_bv 64 A0)
             (Z_to_bv 64 R) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 take) s3
             s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x15bc4) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 v1 v2 d P R take junk
    G HC0 HCF EP ER HD HT HT3 FR CUR OWN INP MU WM MI.
  geo_intro G.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (UP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
  assert (UT : bv_unsigned (Z_to_bv 64 take) = take) by (apply unsigned_lit; lia).
  assert (UR : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (UPT : bv_unsigned (Z_to_bv 64 (P + take)) = P + take) by (apply unsigned_lit; lia).
  assert (URT : bv_unsigned (Z_to_bv 64 (R - take)) = R - take) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep. zstep.
  destruct (Z.eq_dec take 0) as [T0|T0].
  - subst take. if_true.
    zstep. zstep. first [if_false | idtac]. zstep. zstep. zstep.
    apply evt_done. right.
    exists d, 0, 0. do 21 eexists.
    split; [reflexivity|].
    split; [uz|]. split; [uz|]. split; [uz|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [uz|]. split; [uz|].
    split; [eassumption|]. eassumption.
  - if_false.
    zstep. zstep. zstep. zstep.
    set (buf := skipn (Z.to_nat d) inp).
    assert (BL : Z.of_nat (length buf) = N - d) by (unfold buf; rewrite length_skipn; lia).
    lazymatch goal with H : bytes_at rsegs ?mm C0 inp |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (BUF : bytes_at rsegs mm P buf)
        by (unfold buf; replace P with (C0 + Z.of_nat (Z.to_nat d)) by lia; apply tl_bytes_at_skipn; [exact H | lia])
    end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply HMC with (buf := buf);
        [ rewrite UP; exact BUF
        | rewrite UP, UT; change (bv_unsigned (Z_to_bv 64 0) mod 256) with 0;
          unfold memchr_ok; destruct (find_byte 0 (firstn (Z.to_nat take) buf)); [left|]; lia
        | eassumption ]
      | unfold memchr_post; post_call rsegs mm ] end.
    lazymatch goal with |- context [memchr_res ?a ?c ?k ?b] =>
      replace (memchr_res a c k b) with (memchr_res P 0 take buf)
        by (f_equal; first [reflexivity | symmetry; assumption]) end.
    destruct (tl_strnlen_memchr P take buf ltac:(lia) ltac:(lia) ltac:(lia)) as [SN0 SN1].
    destruct (tl_memchr_range P take buf ltac:(lia)) as [MR|MR].
    + assert (UMR : bv_unsigned (Z_to_bv 64 (memchr_res P 0 take buf)) = 0) by (rewrite MR; reflexivity).
      zstep. if_true.
      zstep. zstep.
      apply evt_done. right.
      exists d, take, take. do 21 eexists.
      split; [reflexivity|].
      split; [uz|]. split; [uz|]. split; [uz|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [symmetry; exact (SN0 MR)|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [uz|]. split; [uz|].
      split; [eassumption|]. eassumption.
    + assert (UMR : bv_unsigned (Z_to_bv 64 (memchr_res P 0 take buf)) = memchr_res P 0 take buf)
        by (apply unsigned_lit; lia).
      assert (UMP : bv_unsigned (Z_to_bv 64 (memchr_res P 0 take buf - P)) = memchr_res P 0 take buf - P)
        by (apply unsigned_lit; lia).
      zstep. if_false.
      zstep. zstep. zstep.
      apply evt_done. right.
      exists d, take, (memchr_res P 0 take buf - P). do 21 eexists.
      split; [reflexivity|].
      split; [uz|]. split; [uz|]. split; [uz|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [symmetry; apply SN1; lia|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [uz|]. split; [uz|].
      split; [eassumption|]. eassumption.
Qed.

(* +0xe8: the length word is b1 + 256 b2 (each byte 0 when the input had run out) *)
Lemma j_copy : forall (m : word -> option byte)
    (x1 x5 x6 x7 x14 x15 x16 x17 x18 x28 x29 x30 x31 v1 v2 : word) (d P R b1 b2 : Z) (junk : list byte),
  geo -> 0 < C0 -> C0 + N <= bv_unsigned sp + -48 ->
  P = C0 + d -> R = N - d -> 1 <= d <= N -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs m A0 [C8 v1; C8 v2] ->
  rw_cells rsegs m A1 [C8 (Z_to_bv 64 0)] ->
  bytes_at rsegs m C0 inp ->
  munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  evt rsegs (fun ms => tab_post ms \/ call_post ms)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 A1) (Z_to_bv 64 P) (Z_to_bv 64 A0)
             (Z_to_bv 64 R) (Z_to_bv 64 b1) (Z_to_bv 64 b2) x14 x15 x16 x17 x18 s3
             s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x15b90) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x14 x15 x16 x17 x18 x28 x29 x30 x31 v1 v2 d P R b1 b2 junk
    G HC0 HCF EP ER HD Hb1 Hb2 FR CUR OWN INP MU WM MI.
  pose proof G as G'. geo_intro G'.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- context [Z_to_bv 64 (?X mod 65536)] =>
    let HE := fresh "HE" in
    assert (HE : X mod 65536 = (b1 + 256 * b2) mod 320);
    [ clear - Hb1 Hb2;
      lazymatch goal with |- ?L = _ =>
        let L' := eval pattern b1, b2 in L in
        lazymatch L' with ?Fn _ _ =>
          apply (tl_zcheck2 Fn (fun y1 y2 => (y1 + 256 * y2) mod 320) 256 256);
          [vm_compute; reflexivity | lia | lia] end end
    | rewrite HE; clear HE ] end.
  pose proof (Z.mod_pos_bound (b1 + 256 * b2) 320 ltac:(lia)) as M320.
  assert (UU : bv_unsigned (Z_to_bv 64 ((b1 + 256 * b2) mod 320)) = (b1 + 256 * b2) mod 320)
    by (apply unsigned_lit; lia).
  assert (UR : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  zstep.
  destruct (Z_lt_le_dec ((b1 + 256 * b2) mod 320) R) as [LT|GE].
  - if_true.
    eapply (j_take m) with (d := d) (P := P) (R := R) (take := (b1 + 256 * b2) mod 320);
      try eassumption; lia.
  - if_false. zstep.
    eapply (j_take m) with (d := d) (P := P) (R := R) (take := R); try eassumption; lia.
Qed.

Lemma pro_entry : forall (w x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (lo : Z),
  geo -> (N <> 0 -> 0 < C0 /\ C0 + N <= bv_unsigned sp + -48) ->
  stk rsegs m0 lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
  rw_cells rsegs m0 A0 [C8 (Z_to_bv 64 C0); C8 (Z_to_bv 64 N)] ->
  rw_cells rsegs m0 A1 [C8 w] ->
  bytes_at rsegs m0 C0 inp -> bytes_at rsegs m0 133104 TL_TB -> mem_inv rsegs m0 ->
  evt rsegs (fun ms => tab_post ms \/ call_post ms)
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 A0) (Z_to_bv 64 A1) x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x15aa8) fc None m0 (seg_rom rsegs)).
Proof.
  intros w x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 lo G HIN ST LO CUR OWN INP TXT MI.
  pose proof G as G'. geo_intro G'.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (TBL : Z.of_nat (length TL_TB) = 88) by reflexivity.
  assert (UA0 : bv_unsigned (Z_to_bv 64 A0) = A0) by (apply unsigned_lit; lia).
  assert (UA1 : bv_unsigned (Z_to_bv 64 A1) = A1) by (apply unsigned_lit; lia).
  assert (UC0 : bv_unsigned (Z_to_bv 64 C0) = C0) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  pose proof (munch_refl W m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  carve_frame 48%nat ST.
  destruct (Z.eq_dec N 0) as [N0|N0].
  - clear INP HIN.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    if_true.
    zstep. zstep.
    eapply j_tab with (s := 0) (adv := 0); first [eassumption | uz].
  - destruct (HIN N0) as [HC0 HCF]. clear HIN.
    destruct (tl_nth_ex inp 0 ltac:(lia)) as [b0 B0].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    if_false.
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with H : bytes_at rsegs ?mm C0 inp |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (tl_rd1 rsegs mm C0 inp 0 b0 H B0) as RD end.
    zstep. zstep. zstep.
    pose proof (bv_unsigned_in_range 8 b0) as Rb0. unfold bv_modulus in Rb0. change (2 ^ Z.of_N 8) with 256 in Rb0.
    if_cases K; zify_cond K; cbv iota.
    + assert (KB : bv_unsigned b0 < 128) by (apply tl_sxb_lt; lia).
      assert (SX : bv_unsigned (sxb b0) = bv_unsigned b0)
        by (rewrite tl_sxb_pos by exact KB; apply unsigned_lit; lia).
      eapply j_tab with (s := bv_unsigned b0) (adv := 1); first [eassumption | uz].
    + zstep. zstep. zstep.
      destruct (Z.eq_dec N 1) as [N1|N1].
      * br_u. if_true.
        zstep. zstep. zstep.
        eapply (j_copy _) with (d := 1); first [eassumption | uz].
      * br_u. if_false.
        destruct (tl_nth_ex inp 1 ltac:(lia)) as [b1 B1].
        pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1. change (2 ^ Z.of_N 8) with 256 in Rb1.
        zstep. zstep. zstep. zstep.
        lazymatch goal with H : bytes_at rsegs ?mm C0 inp |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (tl_rd1 rsegs mm C0 inp 1 b1 H B1) as RD1 end.
        zstep. zstep.
        destruct (Z.eq_dec N 2) as [N2|N2].
        -- br_u. if_true.
           zstep. zstep.
           eapply (j_copy _) with (d := 2); first [eassumption | uz].
        -- br_u. if_false.
           destruct (tl_nth_ex inp 2 ltac:(lia)) as [b2 B2].
           pose proof (bv_unsigned_in_range 8 b2) as Rb2. unfold bv_modulus in Rb2. change (2 ^ Z.of_N 8) with 256 in Rb2.
           zstep. zstep. zstep. zstep.
           lazymatch goal with H : bytes_at rsegs ?mm C0 inp |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
             pose proof (tl_rd1 rsegs mm C0 inp 2 b2 H B2) as RD2 end.
           zstep. zstep. zstep.
           eapply (j_copy _) with (d := 3); first [eassumption | uz].
Qed.

End Pro.
