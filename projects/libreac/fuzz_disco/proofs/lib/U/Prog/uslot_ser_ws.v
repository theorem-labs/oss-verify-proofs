From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model slot_ser_ws.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib printf_facts_c.
Import ListNotations.
Open Scope Z_scope.

Lemma uws_mask : forall c, 0 <= c <= 32 -> Z.land (Z.shiftr WS_MASK c) 1 = if jws_char c then 1 else 0.
Proof.
  intros c Hc. replace c with (Z.of_nat (Z.to_nat c)) by lia.
  assert (Hk : (Z.to_nat c <= 32)%nat) by lia. revert Hk. generalize (Z.to_nat c). clear c Hc. intros k Hk.
  do 33 (destruct k as [|k]; [reflexivity|]). lia.
Qed.

Lemma uws_cond : forall c, 0 <= c <= 32 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 WS_MASK))
                                                         (bv_unsigned (Z_to_bv 64 c) mod 64)))) 1))
         (Z_to_bv 64 0) = negb (jws_char c).
Proof.
  intros c Hc. rewrite (unsigned_lit WS_MASK) by (unfold WS_MASK; lia). rewrite (unsigned_lit c) by lia.
  rewrite (Z.mod_small c 64) by lia.
  assert (HS : 0 <= Z.shiftr WS_MASK c <= WS_MASK).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; unfold WS_MASK; lia|].
    apply Z.div_le_upper_bound; [lia|]. pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) ltac:(lia)).
    unfold WS_MASK; nia. }
  rewrite (unsigned_lit (Z.shiftr WS_MASK c)) by (unfold WS_MASK in *; lia).
  rewrite uws_mask by lia. destruct (jws_char c); reflexivity.
Qed.

Lemma uws_rd : forall m b B i, bytes_at rsegs m b (pf_bytes (B ++ [0])) -> 0 <= i <= jlen B ->
  ov_read_bytes rsegs m (wa (b + i)) 1 = Some [Z_to_bv 8 (jbyte B i)].
Proof.
  intros m b B i H Hi. unfold jlen in Hi.
  pose proof (read1 m b _ (Z.to_nat i) H) as R.
  rewrite Z2Nat.id in R by lia. rewrite R by (unfold pf_bytes; rewrite length_map, length_app; cbn [length]; lia).
  f_equal. f_equal. unfold pf_bytes, jbyte. rewrite map_app.
  destruct (Nat.ltb_spec (Z.to_nat i) (length B)) as [L|L].
  - rewrite app_nth1 by (rewrite length_map; lia). rewrite (map_nth (Z_to_bv 8) B 0). reflexivity.
  - rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map.
    replace (Z.to_nat i - length B)%nat with O by lia. rewrite (nth_overflow B) by lia. reflexivity.
Qed.

Lemma uws_chk : forall b n i, 0 < b -> b + n + 1 < 2 ^ 63 -> 0 <= i <= n ->
  bv_ltu (Z_to_bv 64 (nt b)) (Z_to_bv 64 i) = false.
Proof. intros b n i Hb Hn Hi. rewrite ltu_lit by (unfold nt; lia). apply Z.ltb_ge. unfold nt. lia. Qed.

Ltac uws_trap b B := rewrite (uws_chk b (jlen B)) by lia; cbv iota.

Ltac uws_mask_test B i W := rewrite uws_cond by lia; destruct (jws_char (jbyte B i)) eqn:W; cbn [negb]; cbv iota.

Ltac uws_done := apply evt_done; eexists; reflexivity.

Ltac uws_exit_if B i := rewrite (ws_stop B i ltac:(lia)) by first [assumption | apply ws_big; lia];
  step; rewrite ltu_lit by lia; rewrite (proj2 (Z.ltb_lt i (jlen B))) by lia; cbn [negb]; cbv iota; uws_done.

Ltac uws_exit_no B i := exfalso;
  match goal with HW : json_ws B i = jlen B |- _ =>
    rewrite (ws_stop B i ltac:(lia)) in HW by first [assumption | apply ws_big; lia] end; lia.

Lemma uws_L5 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 32 ->
  s6 = Z_to_bv 64 i ->
  0 <= i -> json_ws B i < jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a1' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (jbyte B (json_ws B i))) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (json_ws B i)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x137d4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x137ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 Ei Hi HW Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 s6.
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 a1 Hk Hi HW.
  induction k as [|k IH]; intros i a0 a1 Hk Hi HW;
    (assert (HiB : i < jlen B) by (apply (ws_lt B i Hi); lia)); [lia|].
  pose proof (uws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. uws_trap b B.
  step. step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. uws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E]. rewrite E in HW |- *.
  pose proof (ws_ge B (i + 1) ltac:(lia)) as G1.
  step. step. rewrite eqb_lit by lia.
  replace (jlen B =? i + 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. eapply (IH (i + 1)); [lia | lia | exact HW].
Qed.

Lemma uws_L6 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 32 ->
  s6 = Z_to_bv 64 i ->
  0 <= i <= jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (json_ws B i)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (if json_ws B i <? jlen B then 0x13818 else 0x13868)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x137e4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 Ei Hi Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 s6.
  step. rewrite ltu_lit by lia. destruct (Z.ltb_spec i (jlen B)) as [L|L]; cbn [negb]; cbv iota.
  2: { assert (EN : i = jlen B) by lia. subst i. rewrite ws_at_end, Z.ltb_irrefl.
       step. rewrite ltu_lit by lia. rewrite Z.ltb_irrefl. cbn [negb]. cbv iota. uws_done. }
  destruct Hi as [Hi _].
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 Hk Hi L.
  induction k as [|k IH]; intros i a0 Hk Hi L; [lia|].
  pose proof (uws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. uws_trap b B.
  step. step. step. ws_byte_test B i; [uws_exit_if B i|].
  step. step. step. uws_mask_test B i W; [|uws_exit_if B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E]. rewrite E.
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (jlen B) (i + 1)) as [EN|EN]; cbn [negb]; cbv iota.
  - step. step. rewrite <- EN, ws_at_end, Z.ltb_irrefl. uws_done.
  - eapply (IH (i + 1)); lia.
Qed.

Lemma uws_L7 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 32 ->
  s6 = Z_to_bv 64 i ->
  0 <= i <= jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (json_ws B i)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13858) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1382c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 Ei Hi Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 s6.
  step. rewrite ltu_lit by lia. destruct (Z.ltb_spec i (jlen B)) as [L|L]; cbn [negb]; cbv iota.
  2: { assert (EN : i = jlen B) by lia. subst i. rewrite ws_at_end. uws_done. }
  destruct Hi as [Hi _].
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 Hk Hi L.
  induction k as [|k IH]; intros i a0 Hk Hi L; [lia|].
  pose proof (uws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. uws_trap b B.
  step. step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. uws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E]. rewrite E.
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (jlen B) (i + 1)) as [EN|EN]; cbn [negb]; cbv iota.
  - step. rewrite <- EN, ws_at_end. uws_done.
  - eapply (IH (i + 1)); lia.
Qed.

Lemma uws_L9 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 32 ->
  s6 = Z_to_bv 64 i ->
  0 <= i <= jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (json_ws B i)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (if json_ws B i <? jlen B then 0x138f0 else 0x13900)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x138bc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 Ei Hi Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 s6.
  step. rewrite ltu_lit by lia. destruct (Z.ltb_spec i (jlen B)) as [L|L]; cbn [negb]; cbv iota.
  2: { assert (EN : i = jlen B) by lia. subst i. rewrite ws_at_end, Z.ltb_irrefl.
       step. rewrite ltu_lit by lia. rewrite Z.ltb_irrefl. cbn [negb]. cbv iota. uws_done. }
  destruct Hi as [Hi _].
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 Hk Hi L.
  induction k as [|k IH]; intros i a0 Hk Hi L; [lia|].
  pose proof (uws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. uws_trap b B.
  step. step. step. ws_byte_test B i; [uws_exit_if B i|].
  step. step. step. uws_mask_test B i W; [|uws_exit_if B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E]. rewrite E.
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (jlen B) (i + 1)) as [EN|EN]; cbn [negb]; cbv iota.
  - step. step. rewrite <- EN, ws_at_end, Z.ltb_irrefl. uws_done.
  - eapply (IH (i + 1)); lia.
Qed.

Lemma uws_L11 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 32 ->
  a0 = Z_to_bv 64 i ->
  0 <= i -> json_ws B i < jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a1' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (json_ws B i)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13978) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1394c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 Ei Hi HW Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 a0.
  pose proof (ws_lt B i Hi HW) as HiB0.
  step. rewrite ltu_lit by lia. rewrite (proj2 (Z.ltb_lt i (jlen B))) by lia.
  cbn [negb]. cbv iota. clear HiB0.
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a1 Hk Hi HW.
  induction k as [|k IH]; intros i a1 Hk Hi HW;
    (assert (HiB : i < jlen B) by (apply (ws_lt B i Hi); lia)); [lia|].
  pose proof (uws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. uws_trap b B.
  step. step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. uws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E]. rewrite E in HW |- *.
  pose proof (ws_ge B (i + 1) ltac:(lia)) as G1.
  step. step. rewrite eqb_lit by lia.
  replace (jlen B =? i + 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. eapply (IH (i + 1)); [lia | lia | exact HW].
Qed.

Lemma uws_L12 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 32 ->
  a1 = Z_to_bv 64 i ->
  0 <= i <= jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (json_ws B i)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x139bc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13990) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 Ei Hi Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 a1.
  step. rewrite ltu_lit by lia. destruct (Z.ltb_spec i (jlen B)) as [L|L]; cbn [negb]; cbv iota.
  2: { assert (EN : i = jlen B) by lia. subst i. rewrite ws_at_end. uws_done. }
  destruct Hi as [Hi _].
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 Hk Hi L.
  induction k as [|k IH]; intros i a0 Hk Hi L; [lia|].
  pose proof (uws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. uws_trap b B.
  step. step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. uws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E]. rewrite E.
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (jlen B) (i + 1)) as [EN|EN]; cbn [negb]; cbv iota.
  - step. rewrite <- EN, ws_at_end. uws_done.
  - eapply (IH (i + 1)); lia.
Qed.

Lemma uws_L13_loop : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 32 ->
  s6 = Z_to_bv 64 i ->
  0 <= i < jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (json_ws B i)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13a04) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139dc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 Ei Hi Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 s6.
  destruct Hi as [Hi L].
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 Hk Hi L.
  induction k as [|k IH]; intros i a0 Hk Hi L; [lia|].
  pose proof (uws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. uws_trap b B.
  step. step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. uws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E]. rewrite E.
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (jlen B) (i + 1)) as [EN|EN]; cbn [negb]; cbv iota.
  - step. rewrite <- EN, ws_at_end. uws_done.
  - eapply (IH (i + 1)); lia.
Qed.

Lemma uws_L13 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 32 ->
  a0 = Z_to_bv 64 i ->
  0 <= i <= jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (json_ws B i)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13a04) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139d4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 Ei Hi Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 a0.
  step. step. rewrite ltu_lit by lia. destruct (Z.ltb_spec i (jlen B)) as [L|L]; cbn [negb]; cbv iota.
  - eapply uws_L13_loop with (b := b) (i := i) (B := B); first [reflexivity | lia | assumption].
  - assert (EN : i = jlen B) by lia. subst i. rewrite ws_at_end. uws_done.
Qed.

Lemma uws_L14 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 32 ->
  a1 = Z_to_bv 64 i ->
  0 <= i <= jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (json_ws B i)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13b44) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b18) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 Ei Hi Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 a1.
  step. rewrite ltu_lit by lia. destruct (Z.ltb_spec i (jlen B)) as [L|L]; cbn [negb]; cbv iota.
  2: { assert (EN : i = jlen B) by lia. subst i. rewrite ws_at_end. uws_done. }
  destruct Hi as [Hi _].
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 Hk Hi L.
  induction k as [|k IH]; intros i a0 Hk Hi L; [lia|].
  pose proof (uws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. uws_trap b B.
  step. step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. uws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E]. rewrite E.
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (jlen B) (i + 1)) as [EN|EN]; cbn [negb]; cbv iota.
  - step. rewrite <- EN, ws_at_end. uws_done.
  - eapply (IH (i + 1)); lia.
Qed.

Lemma uws_L15 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 32 ->
  s6 = Z_to_bv 64 i ->
  0 <= i -> json_ws B i < jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (json_ws B i)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13bac) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b80) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 Ei Hi HW Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 s6.
  pose proof (ws_lt B i Hi HW) as HiB0.
  step. rewrite ltu_lit by lia. rewrite (proj2 (Z.ltb_lt i (jlen B))) by lia.
  cbn [negb]. cbv iota. clear HiB0.
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 Hk Hi HW.
  induction k as [|k IH]; intros i a0 Hk Hi HW;
    (assert (HiB : i < jlen B) by (apply (ws_lt B i Hi); lia)); [lia|].
  pose proof (uws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. uws_trap b B.
  step. step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. uws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E]. rewrite E in HW |- *.
  pose proof (ws_ge B (i + 1) ltac:(lia)) as G1.
  step. step. rewrite eqb_lit by lia.
  replace (jlen B =? i + 1) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. eapply (IH (i + 1)); [lia | lia | exact HW].
Qed.

Lemma uws_L16 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 32 ->
  s6 = Z_to_bv 64 i ->
  0 <= i <= jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (json_ws B i)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13bf0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13bc4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 Ei Hi Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 s6.
  step. rewrite ltu_lit by lia. destruct (Z.ltb_spec i (jlen B)) as [L|L]; cbn [negb]; cbv iota.
  2: { assert (EN : i = jlen B) by lia. subst i. rewrite ws_at_end. uws_done. }
  destruct Hi as [Hi _].
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 Hk Hi L.
  induction k as [|k IH]; intros i a0 Hk Hi L; [lia|].
  pose proof (uws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. uws_trap b B.
  step. step. step. ws_byte_test B i; [ws_exit B i|].
  step. step. step. uws_mask_test B i W; [|ws_exit B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E]. rewrite E.
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (jlen B) (i + 1)) as [EN|EN]; cbn [negb]; cbv iota.
  - step. rewrite <- EN, ws_at_end. uws_done.
  - eapply (IH (i + 1)); lia.
Qed.

Lemma uws_L17 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (B : list Z),
  s1 = Z_to_bv 64 (nt b) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) -> s10 = Z_to_bv 64 32 ->
  s6 = Z_to_bv 64 i ->
  0 <= i <= jlen B -> json_ws B i = jlen B ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  evt rsegs
    (fun ms' => exists a0' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (jlen B)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x13f08) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c08) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b i B
    E1 E2 E3 E4 E10 Ei Hi HW Hb HbB FB BB.
  subst s1 s2 s3 s4 s10 s6.
  step. rewrite ltu_lit by lia. destruct (Z.ltb_spec i (jlen B)) as [L|L]; cbn [negb]; cbv iota.
  2: { assert (EN : i = jlen B) by lia. subst i.
       step. rewrite eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota. uws_done. }
  destruct Hi as [Hi _].
  remember (Z.to_nat (jlen B - i)) as k eqn:Hk.
  revert i a0 Hk Hi L HW.
  induction k as [|k IH]; intros i a0 Hk Hi L HW; [lia|].
  pose proof (uws_rd m b B i BB ltac:(lia)) as RD. pose proof (ws_byte B i FB) as HC.
  step. uws_trap b B.
  step. step. step. ws_byte_test B i; [uws_exit_no B i|].
  step. step. step. uws_mask_test B i W; [|uws_exit_no B i].
  destruct (ws_step B i ltac:(lia) W) as [_ E]. rewrite E in HW.
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (jlen B) (i + 1)) as [EN|EN]; cbn [negb]; cbv iota.
  - step. rewrite <- EN. uws_done.
  - eapply (IH (i + 1)); [lia | lia | lia | exact HW].
Qed.
