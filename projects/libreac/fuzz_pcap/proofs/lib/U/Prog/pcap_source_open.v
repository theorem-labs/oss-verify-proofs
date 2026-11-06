(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 1051 of its 1066 lines of code are new or changed and 45 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel fread_c fread_ro_c pcap_source_struct pcap_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma land7_zero : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Ltac ub_align H := try change (bv_wrap 64 7) with 7; rewrite (land7_zero _ H).

Lemma op_drop : forall m a c cs, rw_cells rsegs m a (c :: cs) -> rw_cells rsegs m (a + Z.of_nat (csize c)) cs.
Proof.
  intros m a c cs [[Hwf Hb] (Ha & Hl & Hw)].
  destruct Hwf as [W1 W2].
  change (c :: cs) with ([c] ++ cs) in Hb.
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  cbn [cells_bytes] in B2. rewrite app_nil_r, cbytes_length in B2 by exact W1.
  cbn [cells_size] in Hl, Hw.
  split; [split; [exact W2 | exact B2] |]. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + Z.of_nat (csize c) + i) with (a + (Z.of_nat (csize c) + i)) by lia. apply Hw. lia.
Qed.

Lemma open_split : forall m a junk (w x y z : word),
  rw_cells rsegs m a [CB 24 junk; C8 w; C8 x; C8 y; C8 z] ->
  rw_cells rsegs m a [CB 24 junk] /\ rw_cells rsegs m (a + 24) [C8 w; C8 x; C8 y; C8 z].
Proof.
  intros m a junk w x y z [[Hwf Hb] (Ha & Hl & Hw)].
  change [CB 24 junk; C8 w; C8 x; C8 y; C8 z] with ([CB 24 junk] ++ [C8 w; C8 x; C8 y; C8 z]) in Hwf, Hb.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  cbn [cells_size csize Nat.add] in Hl, Hw, B2.
  split.
  - split; [split; [exact W1 | exact B1] |]. split; [lia|]. split; [cbn; lia|]. intros i Hi. apply Hw. cbn in Hi. lia.
  - split; [split; [exact W2 | exact B2] |]. split; [lia|]. split; [cbn; lia|]. intros i Hi.
    replace (a + 24 + i) with (a + (24 + i)) by lia. apply Hw. cbn in Hi. lia.
Qed.

Lemma open_frame : forall m a junk (w x y z : word),
  rw_cells rsegs m a [CB 32 junk; C8 w; C8 x; C8 y; C8 z] ->
  exists junk', rw_cells rsegs m (a + 8) [CB 24 junk'] /\ rw_cells rsegs m (a + 8 + 24) [C8 w; C8 x; C8 y; C8 z].
Proof.
  intros m a junk w x y z H.
  pose proof (rw_cells_split_CB rsegs m a [] 32%nat junk [C8 w; C8 x; C8 y; C8 z] [8; 24]%nat H eq_refl) as H2.
  cbn [app mk_CB_cells] in H2.
  apply op_drop in H2. cbn [csize] in H2. change (Z.of_nat 8) with 8 in H2.
  destruct (open_split m (a + 8) _ _ _ _ _ H2) as [G1 G2].
  eexists. split; [exact G1 | exact G2].
Qed.

Lemma open_pro :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp ->
    evt rsegs
      (fun ms' => exists sp' m1 junk,
         ms' = MS (mkR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_open + 0x2c)%Z)) sp' gp tp t0 t1 t2 a0 s1 a1 (Z_to_bv 64 (symaddr (Symbols.Ubsan.Sec.s_rodata + 0x6d)%Z)) a1 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (symaddr Symbols.Ubsan.s_libreac_fuzz_fopen)) fc None m1 (seg_rom rsegs) /\
         bv_unsigned sp' = bv_unsigned sp - 64 /\
         rw_cells rsegs m1 (bv_unsigned sp - 64) [CB 32 junk; C8 s2; C8 s1; C8 s0; C8 ra] /\
         munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 /\ wmono rsegs m m1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_open)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 64%nat ST.
  do 11 step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [apply unsigned_lit; lia|].
  replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia.
  refine (conj _ (conj _ _)); eassumption.
Qed.

Lemma open_null :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f sw olen vtag vid : word) (pad : list byte)
         (sp0 ra0 s0o s1o s2o : word),
    a0 = Z_to_bv 64 0 -> bv_unsigned s0 <> 0 -> bv_unsigned s0 mod 8 = 0 ->
    bv_unsigned sp = bv_unsigned sp0 - 64 -> bv_unsigned sp0 <= bv_unsigned s0 ->
    rw_cells rsegs m (bv_unsigned s0) (ps_cells f sw olen vtag vid pad) ->
    rw_cells rsegs m (bv_unsigned sp + 32) [C8 s2o; C8 s1o; C8 s0o; C8 ra0] ->
    evt rsegs
      (fun ms' => exists a3' m',
         ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 (-1)) a1 a2 a3' a4 a5 a6 a7
                       s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
         rw_cells rsegs m' (bv_unsigned s0) (ps_cells (wz 0) sw (wz 0) (wz 0) (wz 0) pad) /\
         munch [(bv_unsigned s0, bv_unsigned s0 + 22)] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_open + 0x2c)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m f sw olen vtag vid pad sp0 ra0 s0o s1o s2o E0 NZ A8 Hsp HS0 HPS HFR.
  subst a0. unfold ps_cells in HPS.
  pose proof (zr_word s0) as Rs0. unfold inr64 in Rs0.
  pose proof (zr_word sp0) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned s0, bv_unsigned s0 + 22)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_false.
  do 3 step. ub_align A8. if_false.
  do 5 step. if_true.
  step.
  do 6 step.
  apply evt_done.
  assert (ESP : Z_to_bv 64 (bv_unsigned sp + 64) = sp0).
  { rewrite Hsp. replace (bv_unsigned sp0 - 64 + 64) with (bv_unsigned sp0) by lia. apply Z_to_bv_bv_unsigned. }
  rewrite ESP. do 2 eexists. split; [reflexivity|].
  unfold ps_cells, wz. split; [eassumption|]. split; eassumption.
Qed.

Lemma open_tail :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f sw olen vtag vid : word) (pad : list byte)
         (sp0 ra0 s0o s1o s2o : word),
    bv_unsigned sp = bv_unsigned sp0 - 64 -> bv_unsigned sp0 <= bv_unsigned s0 ->
    rw_cells rsegs m (bv_unsigned s0) (ps_cells f sw olen vtag vid pad) ->
    rw_cells rsegs m (bv_unsigned sp + 32) [C8 s2o; C8 s1o; C8 s0o; C8 ra0] ->
    evt rsegs
      (fun ms' => exists m',
         ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
                       s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
         rw_cells rsegs m' (bv_unsigned s0) (ps_cells (wz 0) sw olen vtag vid pad) /\
         munch [(bv_unsigned s0, bv_unsigned s0 + 8)] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_open + 0xc8)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m f sw olen vtag vid pad sp0 ra0 s0o s1o s2o Hsp HS0 HPS HFR.
  unfold ps_cells in HPS.
  pose proof (zr_word s0) as Rs0. unfold inr64 in Rs0.
  pose proof (zr_word sp0) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned s0, bv_unsigned s0 + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 8 step.
  apply evt_done.
  assert (ESP : Z_to_bv 64 (bv_unsigned sp + 64) = sp0).
  { rewrite Hsp. replace (bv_unsigned sp0 - 64 + 64) with (bv_unsigned sp0) by lia. apply Z_to_bv_bv_unsigned. }
  rewrite ESP. eexists. split; [reflexivity|].
  unfold ps_cells, wz. split; [eassumption|]. split; eassumption.
Qed.

Lemma op_nth_firstn : forall (A : Type) (l : list A) n k d, (n < k)%nat -> nth n (firstn k l) d = nth n l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n k d H; destruct k as [|k]; cbn; try lia; [destruct n; reflexivity|].
  destruct n as [|n]; [reflexivity|]. apply IH. lia.
Qed.

Lemma op_byte : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma open_byte : forall m a (Fc : list byte) k,
  bytes_at rsegs m a (firstn 24 Fc) -> (24 <= length Fc)%nat -> 0 <= k < 24 ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) Fc (Z_to_bv 8 0)].
Proof.
  intros m a Fc k H HL Hk.
  rewrite (op_byte m a (firstn 24 Fc) k H) by (rewrite length_firstn; lia).
  rewrite op_nth_firstn by lia. reflexivity.
Qed.

Lemma op_lor : forall a b n, 0 <= n -> 0 <= a -> 0 <= b < 2 ^ n -> a mod 2 ^ n = 0 -> Z.lor a b = a + b.
Proof.
  intros a b n Hn Ha Hb Hm.
  assert (HL : Z.land a b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [Hlt|Hge].
    - rewrite <- (Z.mod_pow2_bits_low a n i Hlt), Hm, Z.bits_0. reflexivity.
    - rewrite <- (Z.mod_small b (2 ^ n)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact HL. symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.

Lemma op_lor_r : forall a b n, 0 <= n -> 0 <= a -> 0 <= b < 2 ^ n -> a mod 2 ^ n = 0 -> Z.lor b a = a + b.
Proof. intros a b n H1 H2 H3 H4. rewrite Z.lor_comm. exact (op_lor a b n H1 H2 H3 H4). Qed.

Lemma op_swrap : forall M, 0 <= M < 2 ^ 32 -> bv_swrap 32 M = if M <? 2 ^ 31 then M else M - 2 ^ 32.
Proof.
  intros M H. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  destruct (Z.ltb_spec M (2 ^ 31)).
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_unique (M + 2 ^ 31) (2 ^ 32) 1 (M + 2 ^ 31 - 2 ^ 32)) by lia. lia.
Qed.

Lemma op_unsigned_neg : forall x, - 2 ^ 64 <= x < 0 -> bv_unsigned (Z_to_bv 64 x) = x + 2 ^ 64.
Proof.
  intros x H. rewrite Z_to_bv_unsigned. unfold bv_wrap. replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
  rewrite <- (Z.mod_unique x (2 ^ 64) (-1) (x + 2 ^ 64)) by lia. reflexivity.
Qed.

Lemma op_bv_wrap64 : forall x, Z_to_bv 64 (x + 2 ^ 64) = Z_to_bv 64 x.
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
  replace (x + 2 ^ 64) with (x + 1 * 2 ^ 64) by lia. apply Z_mod_plus_full.
Qed.

Lemma open_magic : forall c0 c1 c2 c3 : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb c1)) 8)))
                                                    (bv_unsigned (zxb c0)))))
                    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb c2)) 16)))
                       (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (zxb c3)) 24))))))))
  = Z_to_bv 64 (bv_swrap 32 (bv_unsigned c0 + 256 * bv_unsigned c1 + 65536 * bv_unsigned c2 +
                             16777216 * bv_unsigned c3)).
Proof.
  intros c0 c1 c2 c3. unfold zxb.
  pose proof (bv_unsigned_in_range 8 c0) as R0. pose proof (bv_unsigned_in_range 8 c1) as R1.
  pose proof (bv_unsigned_in_range 8 c2) as R2. pose proof (bv_unsigned_in_range 8 c3) as R3.
  unfold bv_modulus in R0, R1, R2, R3. change (2 ^ Z.of_N 8) with 256 in R0, R1, R2, R3.
  set (b0 := bv_unsigned c0) in *. set (b1 := bv_unsigned c1) in *.
  set (b2 := bv_unsigned c2) in *. set (b3 := bv_unsigned c3) in *.
  rewrite (unsigned_lit b0), (unsigned_lit b1), (unsigned_lit b2), (unsigned_lit b3) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (b1 * 2 ^ 8)), (unsigned_lit (b2 * 2 ^ 16)) by lia.
  rewrite (op_lor (b1 * 2 ^ 8) b0 8) by (first [apply Z.mod_mul | idtac]; lia).
  rewrite (unsigned_lit (b1 * 2 ^ 8 + b0)) by lia.
  rewrite (op_swrap (b3 * 2 ^ 24)) by lia.
  rewrite (op_swrap (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)) by lia.
  destruct (Z.ltb_spec (b3 * 2 ^ 24) (2 ^ 31)) as [H3|H3];
    destruct (Z.ltb_spec (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) (2 ^ 31)) as [H4|H4]; try lia.
  - rewrite (unsigned_lit (b3 * 2 ^ 24)) by lia.
    rewrite (op_lor_r (b3 * 2 ^ 24) (b2 * 2 ^ 16) 24) by (first [apply Z.mod_mul | idtac]; lia).
    rewrite (unsigned_lit (b3 * 2 ^ 24 + b2 * 2 ^ 16)) by lia.
    rewrite (op_lor_r (b3 * 2 ^ 24 + b2 * 2 ^ 16) (b1 * 2 ^ 8 + b0) 16).
    + f_equal. lia.
    + lia.
    + lia.
    + lia.
    + replace (b3 * 2 ^ 24 + b2 * 2 ^ 16) with ((b3 * 2 ^ 8 + b2) * 2 ^ 16) by ring. apply Z.mod_mul. lia.
  - rewrite (op_unsigned_neg (b3 * 2 ^ 24 - 2 ^ 32)) by lia.
    rewrite (op_lor_r (b3 * 2 ^ 24 - 2 ^ 32 + 2 ^ 64) (b2 * 2 ^ 16) 24).
    2-4: lia.
    2: { replace (b3 * 2 ^ 24 - 2 ^ 32 + 2 ^ 64) with ((b3 - 2 ^ 8 + 2 ^ 40) * 2 ^ 24) by ring.
         apply Z.mod_mul. lia. }
    rewrite (unsigned_lit (b3 * 2 ^ 24 - 2 ^ 32 + 2 ^ 64 + b2 * 2 ^ 16)) by lia.
    rewrite (op_lor_r (b3 * 2 ^ 24 - 2 ^ 32 + 2 ^ 64 + b2 * 2 ^ 16) (b1 * 2 ^ 8 + b0) 16).
    2-4: lia.
    2: { replace (b3 * 2 ^ 24 - 2 ^ 32 + 2 ^ 64 + b2 * 2 ^ 16) with ((b3 * 2 ^ 8 - 2 ^ 16 + 2 ^ 48 + b2) * 2 ^ 16)
           by ring.
         apply Z.mod_mul. lia. }
    rewrite <- (op_bv_wrap64 (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 - 2 ^ 32)). f_equal. lia.
Qed.

Lemma pcap_magic_range : forall Fc, 0 <= pcap_magic Fc < 2 ^ 32.
Proof.
  intros Fc. unfold pcap_magic, pcap_byte.
  pose proof (bv_unsigned_in_range 8 (nth 0 Fc (Z_to_bv 8 0))) as R0.
  pose proof (bv_unsigned_in_range 8 (nth 1 Fc (Z_to_bv 8 0))) as R1.
  pose proof (bv_unsigned_in_range 8 (nth 2 Fc (Z_to_bv 8 0))) as R2.
  pose proof (bv_unsigned_in_range 8 (nth 3 Fc (Z_to_bv 8 0))) as R3.
  unfold bv_modulus in R0, R1, R2, R3. change (2 ^ Z.of_N 8) with 256 in R0, R1, R2, R3. lia.
Qed.

Lemma op_eqb_sw : forall M k kk, 0 <= M < 2 ^ 32 -> - 2 ^ 31 <= k < 2 ^ 31 -> kk = k mod 2 ^ 32 ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 M)) (Z_to_bv 64 k) = (M =? kk).
Proof.
  intros M k kk HM Hk Hkk. subst kk. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
  rewrite op_swrap by exact HM.
  apply Bool.eq_iff_eq_true. rewrite !Z.eqb_eq.
  destruct (Z.ltb_spec M (2 ^ 31)); split; intros E; Z.div_mod_to_equations; lia.
Qed.

Lemma open_mid : fread_ro_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo b : Z) (Fc : list byte)
         (f sw olen vtag vid : word) (pad junk : list byte) (sp0 ra0 s0o s1o s2o : word),
    bv_unsigned a0 <> 0 -> bv_unsigned s0 <> 0 -> bv_unsigned s0 mod 8 = 0 ->
    bv_unsigned sp = bv_unsigned sp0 - 64 -> bv_unsigned sp0 < 2 ^ 63 -> bv_unsigned sp0 <= bv_unsigned s0 ->
    rw_cells rsegs m (bv_unsigned s0) (ps_cells f sw olen vtag vid pad) ->
    rw_cells rsegs m (bv_unsigned sp + 8) [CB 24 junk] ->
    rw_cells rsegs m (bv_unsigned sp + 32) [C8 s2o; C8 s1o; C8 s0o; C8 ra0] ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp ->
    mstl m (bv_unsigned a0) b Fc 0 (Z_to_bv 64 0) (Z_to_bv 64 0) ->
    RoAdapt.not_ro rsegs (bv_unsigned a0) 1304 -> RoAdapt.not_ro rsegs (bv_unsigned sp + 8) 24 ->
    RoAdapt.not_ro rsegs lo (bv_unsigned sp - lo) ->
    bv_unsigned a0 + 1304 <= lo -> b + Z.of_nat (length Fc) <= lo -> 0x100000 <= lo ->
    MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
         ((pcap_good Fc = true /\
           ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s0o s1o (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                         s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
           rw_cells rsegs m' (bv_unsigned s0) (ps_cells a0 (wz (pcap_sw Fc)) (wz 0) (wz 0) (wz 0) pad) /\
           mstl m' (bv_unsigned a0) b Fc 24 (wz 0) (wz 0)) \/
          (pcap_good Fc = false /\
           (exists s1' s2', ms' = MS (mkR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_open + 0xc8)%Z)) sp gp tp t0' t1' t2' s0 s1' a0 a1' a2' a3' a4' a5' a6' a7'
                         s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 (symaddr Symbols.Ubsan.s_fclose)) fc None m' (seg_rom rsegs)) /\
           rw_cells rsegs m' (bv_unsigned s0) (ps_cells a0 sw (wz 0) (wz 0) (wz 0) pad) /\
           rw_cells rsegs m' (bv_unsigned sp + 32) [C8 s2o; C8 s1o; C8 s0o; C8 ra0] /\
           mstl m' (bv_unsigned a0) b Fc (Z.min 24 (Z.of_nat (length Fc))) (wz 0) (wz 0))) /\
         munch [(bv_unsigned sp - 112, bv_unsigned sp0); (bv_unsigned a0, bv_unsigned a0 + 1304);
                (bv_unsigned s0, bv_unsigned s0 + 22)] m m' /\
         wmono rsegs m m' /\ MemNorm.ro_agree rsegs m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_open + 0x2c)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros HFR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo b Fc f sw olen vtag vid pad junk sp0 ra0 s0o s1o s2o NZ NZ0 A8 Hsp H63 HS0 HPS GH FR ST LO HMS NRH NRG
    NRS HHL HBL HLO RO.
  unfold fread_ro_contract, FREAD in HFR.
  pose proof (zr_word sp0) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word s0) as Rs0. unfold inr64 in Rs0.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof HPS as (_ & HP0 & HP24 & _). unfold ps_cells in HP24. cbn in HP24.
  unfold ps_cells in HPS.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp0); (bv_unsigned a0, bv_unsigned a0 + 1304);
                          (bv_unsigned s0, bv_unsigned s0 + 22)] m) as MUT.
  pose proof (munch_refl [(bv_unsigned s0, bv_unsigned s0 + 22)] m) as MU0.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  step. if_false.
  do 3 step. ub_align A8. if_false.
  do 5 step. if_false.
  do 6 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (Hb0 : 0 < b) by (destruct HMS as (fl & md & q & rb & (buf & _ & _ & _ & _ & Hb & _) & _); exact Hb).
  assert (MS1 : mstl m1 (bv_unsigned a0) b Fc 0 (Z_to_bv 64 0) (Z_to_bv 64 0)).
  { apply (kp_mstl m m1 0 (bv_unsigned s0)); [| exact HMS | lia | lia | lia | lia].
    apply (keep_munch _ _ _ 0 (bv_unsigned s0) MU0); [lia | lia |]. intros x Hx. cbn. split; [lia | exact I]. }
  assert (RO1 : MemNorm.ro_agree rsegs m1).
  { apply (ro_agree_munch _ _ _ RO MU0). intros x Hx. cbn. split; [lia | exact I]. }
  eapply evt_cut.
  { eapply HFR with (lo := lo) (b := b) (Fc := Fc) (p := 0) (pv := Z_to_bv 64 0) (nx := Z_to_bv 64 0) (junk := junk).
    - exact MS1.
    - exact NRH.
    - unfold wz. reflexivity.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. exact GH.
    - rewrite !unsigned_lit by lia. exact NRG.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - exact RO1.
    - exact ST.
    - exact NRS.
    - unfold FREAD_K. lia.
    - exact HHL.
    - exact HBL. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
    & E2 & EA & MUf & WMf & RO2 & ST2 & BY2 & MS2).
  subst ms'.
  unfold fread_j in EA, MUf, BY2, MS2. rewrite (unsigned_lit 24) in EA, MUf, BY2, MS2 by lia.
  rewrite (unsigned_lit (bv_unsigned sp + 8)) in MUf, BY2 by lia.
  rewrite ?Z.sub_0_r in EA, MUf, BY2, MS2. rewrite ?Z.add_0_l in MS2.
  replace (ret_pc (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_open + 0x68)%Z))) with (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_open + 0x68)%Z)) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (KF : forall x, bv_unsigned sp + 32 <= x < 2 ^ 64 ->
     mbyte rsegs m2 x = mbyte rsegs m1 x /\ (writable_at rsegs m1 x -> writable_at rsegs m2 x)).
  { apply (keep_munch _ _ _ (bv_unsigned sp + 32) (2 ^ 64) MUf); [lia | lia |].
    intros x Hx. unfold FREAD_K. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  pose proof (kp_rw_cells m1 m2 _ _ KF _ _ FR ltac:(lia) ltac:(cbn; lia)) as FR2.
  pose proof (kp_rw_cells m1 m2 _ _ KF _ _ HPS ltac:(lia) ltac:(cbn; lia)) as HPS2.
  assert (MUT2 : munch [(bv_unsigned sp - 112, bv_unsigned sp0); (bv_unsigned a0, bv_unsigned a0 + 1304);
                (bv_unsigned s0, bv_unsigned s0 + 22)] m m2).
  { apply (munch_trans _ m m1 m2); [exact MUT|].
    eapply munch_weaken; [| exact MUf]. intros x Hx. unfold FREAD_K in *. cbn [outside] in Hx |- *.
    destruct Hx as (H1 & H2 & H3 & _). repeat split; lia. }
  pose proof (wmono_trans rsegs m m1 m2 WM WMf) as WM2.
  clear MUT MU0 MUf WM WMf GH FR HPS KF MS1 HMS RO1 RO ST.
  destruct (Z_lt_le_dec (Z.of_nat (length Fc)) 24) as [NS|NL].
  - rewrite Z.min_r in EA, MS2 by lia. subst a0'.
    assert (GF : pcap_good Fc = false)
      by (unfold pcap_good; destruct (Z.leb_spec 24 (Z.of_nat (length Fc))); [lia | reflexivity]).
    step.
    if_cases C.
    + do 2 step.
      apply evt_done. do 15 eexists.
      refine (conj (or_intror (conj GF (conj (ex_intro _ _ (ex_intro _ _ eq_refl)) _))) (conj MUT2 (conj WM2 RO2))).
      unfold ps_cells, wz. rewrite Z.min_r by lia. refine (conj HPS2 (conj FR2 MS2)).
    + exfalso. unfold wz, bv_eqb in C. rewrite !unsigned_lit in C by lia.
      apply Bool.negb_false_iff in C. apply Z.eqb_eq in C. lia.
  - rewrite Z.min_l in EA, MS2, BY2 by lia. subst a0'. unfold wz.
    change (Z.to_nat 24) with 24%nat in BY2. change (Z.to_nat 0) with 0%nat in BY2. cbn [skipn] in BY2.
    pose proof (open_byte m2 _ Fc 0 BY2 ltac:(lia) ltac:(lia)) as HR0.
    pose proof (open_byte m2 _ Fc 1 BY2 ltac:(lia) ltac:(lia)) as HR1.
    pose proof (open_byte m2 _ Fc 2 BY2 ltac:(lia) ltac:(lia)) as HR2.
    pose proof (open_byte m2 _ Fc 3 BY2 ltac:(lia) ltac:(lia)) as HR3.
    change (Z.to_nat 0) with 0%nat in HR0. change (Z.to_nat 1) with 1%nat in HR1.
    change (Z.to_nat 2) with 2%nat in HR2. change (Z.to_nat 3) with 3%nat in HR3.
    rewrite Z.add_0_r in HR0.
    replace (bv_unsigned sp + 8 + 1) with (bv_unsigned sp + 9) in HR1 by lia.
    replace (bv_unsigned sp + 8 + 2) with (bv_unsigned sp + 10) in HR2 by lia.
    replace (bv_unsigned sp + 8 + 3) with (bv_unsigned sp + 11) in HR3 by lia.
    pose proof (pcap_magic_range Fc) as MGR.
    pose proof (munch_refl [(bv_unsigned s0, bv_unsigned s0 + 22)] m2) as MUX.
    step. if_false.
    do 2 step.
    try unfold bv_leu. try unfold bv_ltu.
    rewrite (unsigned_lit (bv_unsigned sp + 8)) by lia.
    if_false.
    do 12 step.
    rewrite open_magic.
    change (bv_unsigned (nth 0 Fc (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 Fc (Z_to_bv 8 0)) +
            65536 * bv_unsigned (nth 2 Fc (Z_to_bv 8 0)) + 16777216 * bv_unsigned (nth 3 Fc (Z_to_bv 8 0)))
      with (pcap_magic Fc).
    step.
    assert (ESP : Z_to_bv 64 (bv_unsigned sp + 64) = sp0).
    { rewrite Hsp. replace (bv_unsigned sp0 - 64 + 64) with (bv_unsigned sp0) by lia. apply Z_to_bv_bv_unsigned. }
    rewrite (op_eqb_sw (pcap_magic Fc) (-725372255) 0xD4C3B2A1) by first [lia | reflexivity].
    destruct (Z.eqb_spec (pcap_magic Fc) 0xD4C3B2A1) as [EQ1|NE1]; cbv iota.
    + do 10 step.
      lazymatch goal with H : munch [(bv_unsigned s0, bv_unsigned s0 + 22)] m2 ?mm |- _ => rename mm into m3 end.
      assert (GT : pcap_good Fc = true).
      { unfold pcap_good. rewrite EQ1. destruct (Z.leb_spec 24 (Z.of_nat (length Fc))); [reflexivity | lia]. }
      assert (SW : pcap_sw Fc = 1) by (unfold pcap_sw; rewrite EQ1; reflexivity).
      apply evt_done. rewrite ESP. do 15 eexists.
      refine (conj (or_introl (conj GT (conj eq_refl (conj _ _)))) (conj MUT2 (conj WM2 _))).
      * rewrite SW. unfold ps_cells, wz. exact HPS2.
      * apply (kp_mstl m2 m3 0 (bv_unsigned s0)); [| exact MS2 | lia | lia | lia | lia].
        apply (keep_munch _ _ _ 0 (bv_unsigned s0) MUX); [lia | lia |]. intros x Hx. cbn. split; [lia | exact I].
      * apply (ro_agree_munch _ _ _ RO2 MUX). intros x Hx. cbn. split; [lia | exact I].
    + do 3 step.
      rewrite (op_eqb_sw (pcap_magic Fc) (-1582119980) 0xA1B2C3D4) by first [lia | reflexivity].
      destruct (Z.eqb_spec (pcap_magic Fc) 0xA1B2C3D4) as [EQ2|NE2]; cbn [negb]; cbv iota.
      * do 9 step.
        lazymatch goal with H : munch [(bv_unsigned s0, bv_unsigned s0 + 22)] m2 ?mm |- _ => rename mm into m3 end.
        assert (GT : pcap_good Fc = true).
        { unfold pcap_good. rewrite EQ2. destruct (Z.leb_spec 24 (Z.of_nat (length Fc))); [reflexivity | lia]. }
        assert (SW : pcap_sw Fc = 0) by (unfold pcap_sw; rewrite (proj2 (Z.eqb_neq _ _) NE1); reflexivity).
        apply evt_done. rewrite ESP. do 15 eexists.
        refine (conj (or_introl (conj GT (conj eq_refl (conj _ _)))) (conj MUT2 (conj WM2 _))).
        -- rewrite SW. unfold ps_cells, wz. exact HPS2.
        -- apply (kp_mstl m2 m3 0 (bv_unsigned s0)); [| exact MS2 | lia | lia | lia | lia].
           apply (keep_munch _ _ _ 0 (bv_unsigned s0) MUX); [lia | lia |]. intros x Hx. cbn. split; [lia | exact I].
        -- apply (ro_agree_munch _ _ _ RO2 MUX). intros x Hx. cbn. split; [lia | exact I].
      * do 2 step.
        assert (GF : pcap_good Fc = false).
        { unfold pcap_good. rewrite (proj2 (Z.eqb_neq _ _) NE1), (proj2 (Z.eqb_neq _ _) NE2). cbn [orb].
          apply andb_false_r. }
        apply evt_done. do 15 eexists.
        refine (conj (or_intror (conj GF (conj (ex_intro _ _ (ex_intro _ _ eq_refl)) _))) (conj MUT2 (conj WM2 RO2))).
        unfold ps_cells, wz. rewrite Z.min_l by lia. refine (conj HPS2 (conj FR2 MS2)).
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Contract KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import KindB pcap_lib fmemopen_c fclose_c
  libreac_fuzz_fopen_c pcap_source_open_c.
Local Open Scope Z_scope.

Lemma op_rm_unique : forall (l1 l2 r1 r2 : list (Z * Z)) x, pairwise ranges_disjoint (l1 ++ x :: l2) -> 0 < snd x ->
  l1 ++ x :: l2 = r1 ++ x :: r2 -> l1 ++ l2 = r1 ++ r2.
Proof.
  induction l1 as [|y l1 IH]; intros l2 r1 r2 x HP Hx E.
  - destruct r1 as [|z r1]; cbn in E |- *.
    + injection E as E. exact E.
    + injection E as E1 E. subst z. exfalso. cbn in HP. destruct HP as [HP _].
      assert (Hin : In x l2) by (rewrite E; apply in_or_app; right; left; reflexivity).
      specialize (HP x Hin). unfold ranges_disjoint in HP. lia.
  - destruct r1 as [|z r1]; cbn in E |- *.
    + injection E as E1 E. subst y. exfalso. cbn in HP. destruct HP as [HP _].
      assert (Hin : In x (l1 ++ x :: l2)) by (apply in_or_app; right; left; reflexivity).
      specialize (HP x Hin). unfold ranges_disjoint in HP. lia.
    + injection E as E1 E. subst z. f_equal. apply (IH l2 r1 r2 x); [cbn in HP; exact (proj2 HP) | exact Hx | exact E].
Qed.

Lemma op_stk : forall m lo hi, 0x100000 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> writable_at rsegs m a) ->
  stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha. specialize (H a Ha). split; [exact H|].
  destruct (writable_hi_present m a ltac:(lia) H) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity.
Qed.

Lemma op_fs_range : forall lo n,
  forallb (fun i => match find_segment rsegs (lo + Z.of_nat i) 1 with Some _ => true | None => false end)
    (seq 0 n) = true ->
  forall a, lo <= a < lo + Z.of_nat n -> find_segment rsegs a 1 <> None.
Proof.
  intros lo n H a Ha. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (a - lo)) ltac:(apply in_seq; lia)).
  replace (lo + Z.of_nat (Z.to_nat (a - lo))) with a in H by lia.
  destruct (find_segment rsegs a 1); [discriminate | discriminate H].
Qed.

Lemma op_chain2 : forall (own : Z -> bool) regs R1 R2 R3 R4 R5 M1 M3 M5,
  Regs6ss.xregs_eqv M1 R1 -> regs_preserved R1 R2 -> Regs6ss.xregs_eqv M3 R3 -> regs_preserved R3 R4 ->
  Regs6ss.xregs_eqv M5 R5 ->
  (forall r, callee_saved r -> own r = false ->
     reg_get M5 (Z_to_bv 5 r) = reg_get R4 (Z_to_bv 5 r) /\ reg_get M3 (Z_to_bv 5 r) = reg_get R2 (Z_to_bv 5 r) /\
     reg_get M1 (Z_to_bv 5 r) = reg_get regs (Z_to_bv 5 r)) ->
  (forall r, callee_saved r -> own r = true -> reg_get M5 (Z_to_bv 5 r) = reg_get regs (Z_to_bv 5 r)) ->
  regs_preserved regs R5.
Proof.
  intros own regs R1 R2 R3 R4 R5 M1 M3 M5 X1 P12 X3 P34 X5 K1 K2 r Hr.
  assert (Hk : 0 < r < 32) by (unfold callee_saved in Hr; lia).
  assert (NZ : bv_eqb (Z_to_bv 5 r) 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia. }
  rewrite (getr_of_eqv _ _ _ X5 NZ). unfold getr. rewrite NZ.
  destruct (own r) eqn:O; [exact (K2 r Hr O)|].
  destruct (K1 r Hr O) as (E5 & E3 & E1).
  assert (F4 : reg_get R4 (Z_to_bv 5 r) = reg_get R3 (Z_to_bv 5 r)).
  { pose proof (P34 r Hr) as F. unfold getr in F. rewrite NZ in F. exact F. }
  assert (F2 : reg_get R2 (Z_to_bv 5 r) = reg_get R1 (Z_to_bv 5 r)).
  { pose proof (P12 r Hr) as F. unfold getr in F. rewrite NZ in F. exact F. }
  rewrite E5, F4, <- (X3 _ NZ), E3, F2, <- (X1 _ NZ). exact E1.
Qed.

Section H.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.

Lemma op_pre : forall K f K1 L A regs mem md E L1 A1 mem1 md1 regs1,
  call_pre_k B (aa_MR API) K L A regs mem md ->
  kb_mid B API K (spZ regs) L A mem md E L1 A1 mem1 md1 ->
  st_init_done A1 = true ->
  0 <= f -> 0 <= K1 -> f + K1 <= K ->
  spZ regs1 = spZ regs - f -> spZ regs1 mod 16 = 0 ->
  getr regs1 4 = getr regs 4 -> YK0s.ret_ok (getr regs1 1) ->
  call_pre_k B (aa_MR API) K1 L1 A1 regs1 mem1 md1.
Proof.
  intros K f K1 L A regs mem md E L1 A1 mem1 md1 regs1 (HM & HWF & HB & Hra & Hal & Hlo & Hhi & HW & Htp & Herr & Haux)
    (M1 & W1 & B1 & Y1 & P1 & D1 & F1 & K1' & S1) Hinit Hf HK1 HfK Hsp Hal1 Htp1 Hra1.
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact Hra1|]. split; [exact Hal1|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; apply S1; left; lia|].
  split; [rewrite Htp1; exact Htp|].
  split; [intros a Ha; apply S1; right; exact Ha|].
  intros Hd. rewrite Hinit in Hd. discriminate.
Qed.

Lemma op_seqXX : forall K sp L A mem md E1 L1 A1 mem1 md1 K2 sp2 E2 L2 A2 mem2 md2,
  kb_mid B API K sp L A mem md E1 L1 A1 mem1 md1 ->
  kb_mid B API K2 sp2 L1 A1 mem1 md1 E2 L2 A2 mem2 md2 ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1)) ->
  (length (st_regions A) <= length (st_regions A1))%nat ->
  (forall a, in_img B a -> ~ owned B L A a -> ~ owned B L2 A2 a -> ~ E1 a -> ~ E2 a -> ~ owned B L1 A1 a) ->
  sp - K <= sp2 - K2 -> sp2 <= sp -> alloc_ceiling + K <= sp -> sp <= 2 ^ 64 ->
  (forall a, sp - K <= a < sp -> ~ (sp2 - K2 <= a < sp2) -> ~ E2 a) ->
  kb_mid B API K sp L A mem md (fun a => E1 a \/ E2 a) L2 A2 mem2 md2.
Proof.
  intros K sp L A mem md E1 L1 A1 mem1 md1 K2 sp2 E2 L2 A2 mem2 md2
    (M1 & W1 & B1 & Y1 & P1 & D1 & F1 & K1 & S1) (M2 & W2 & B2 & Y2 & P2 & D2 & F2 & K2' & S2) HU HR HO H1 H2 H3 H4 H5.
  pose proof alloc_ceiling_val as Hc.
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split.
  { destruct Y1 as (Y1a & Y1b & Y1c & Y1d). destruct Y2 as (Y2a & Y2b & Y2c & Y2d).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite (Y2d r ltac:(lia)). exact (Y1d r Hr). }
  split.
  { intros p n Hin Hin2. rewrite (P2 p n (HU p n Hin) Hin2). exact (P1 p n Hin (HU p n Hin)). }
  split.
  { destruct D1 as [vm1 ->]. destruct D2 as [vm2 ->]. exists vm2.
    destruct md as [f0 [mp lz mt] io fs pr li ti]. reflexivity. }
  split.
  { intros a Ha Ho Ho2 Hs He.
    assert (Ho1 : ~ owned B L1 A1 a).
    { destruct Ha as [Ha|Ha].
      - intro Hx. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Hx). lia.
      - apply HO; [exact Ha | exact Ho | exact Ho2 | tauto | tauto]. }
    destruct (F1 a Ha Ho Ho1 ltac:(tauto) ltac:(tauto)) as [E1a E1w].
    destruct (F2 a Ha Ho1 Ho2 ltac:(intros [Hx|Hx]; apply Hs; [left; lia | right; exact Hx]) ltac:(tauto))
      as [E2a E2w].
    split; [congruence | tauto]. }
  split.
  { intros p n i Hin Hin2 Hi. rewrite <- (P1 p n Hin (HU p n Hin)).
    rewrite (K2' p n i (HU p n Hin) Hin2 Hi). rewrite (P1 p n Hin (HU p n Hin)). exact (K1 p n i Hin (HU p n Hin) Hi). }
  intros a Ha.
  assert (Hd : (sp2 - K2 <= a < sp2) \/ (errno_addr B <= a < errno_addr B + 4) \/
               ~ ((sp2 - K2 <= a < sp2) \/ (errno_addr B <= a < errno_addr B + 4))) by lia.
  destruct Hd as [Hd|[Hd|Hd]]; [apply S2; left; exact Hd | apply S2; right; exact Hd |].
  destruct Ha as [Ha|Ha]; [|exfalso; apply Hd; right; exact Ha].
  assert (No1 : ~ owned B L1 A1 a) by (intro Hx; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Hx); lia).
  assert (No2 : ~ owned B L2 A2 a) by (intro Hx; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M2 Hx); lia).
  apply (proj2 (F2 a ltac:(left; lia) No1 No2 Hd ltac:(apply H5; lia))). apply S1. left. exact Ha.
Qed.

Lemma op_present : forall W m m', munch W m m' -> wmono rsegs m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> ~ in_img B x) ->
  forall x, m x <> None -> m' x <> None.
Proof using SEGS.
  intros W m m' MU WM HW x Hx.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  destruct (kb_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (MU x Ho). exact Hx.
  - assert (Wx : writable_at rsegs m (bv_unsigned x)).
    { unfold writable_at, wview. rewrite Z_to_bv_bv_unsigned. destruct (m x) as [bb|]; [discriminate | contradiction]. }
    destruct (present_of_writable_out B SEGS m' (bv_unsigned x) ltac:(lia) (HW (bv_unsigned x) ltac:(lia) Ho)
      (WM _ Wx)) as [bb E].
    rewrite Z_to_bv_bv_unsigned in E. rewrite E. discriminate.
Qed.

Lemma op_img_lit : forall a,
  ((symaddr Symbols.Ubsan.s___libc) <= a < (symaddr (Symbols.Ubsan.s___libc + 0x4)%Z) \/ (symaddr Symbols.Ubsan.s___stack_chk_guard) <= a < (symaddr Symbols.Ubsan.s___sysinfo) \/ (symaddr (Symbols.Ubsan.Sec.s_got + 0x80)%Z) <= a < (symaddr (Symbols.Ubsan.Sec.s_got + 0x88)%Z) \/ (symaddr Symbols.Ubsan.s_ofl_lock) <= a < (symaddr (Symbols.Ubsan.Sec.s_bss + 198696)%Z)) ->
  in_img B a.
Proof using SEGS.
  intros a H.
  assert (F : find_segment rsegs a 1 <> None).
  { destruct H as [H|[H|[H|H]]].
    - apply (op_fs_range (symaddr Symbols.Ubsan.s___libc) 4); [vm_compute; reflexivity | cbn; lia].
    - apply (op_fs_range (symaddr Symbols.Ubsan.s___stack_chk_guard) 8); [vm_compute; reflexivity | cbn; lia].
    - apply (op_fs_range (symaddr (Symbols.Ubsan.Sec.s_got + 0x80)%Z) 8); [vm_compute; reflexivity | cbn; lia].
    - apply (op_fs_range (symaddr Symbols.Ubsan.s_ofl_lock) 16); [vm_compute; reflexivity | cbn; lia]. }
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|contradiction].
  apply (in_img_of_seg B SEGS a seg); [lia | exact E].
Qed.

Section KeepImg.
Variables m m' : word -> option byte.
Hypothesis KI : forall a, in_img B a ->
  mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a -> writable_at rsegs m' a).

Lemma ki_stdio_ok : stdio_ok m -> stdio_ok m'.
Proof using SEGS KI.
  unfold stdio_ok, A_LIBC, A_OFL_LOCK. intros (S1 & S2 & S3).
  split; [|split]; (eapply bytes_at_transfer; [eassumption|]; intros i Hi;
    cbn [length] in Hi; try rewrite length_le4 in Hi; refine (proj1 (KI _ _)); apply op_img_lit; lia).
Qed.

Lemma ki_guard_ok : guard_ok m -> guard_ok m'.
Proof using SEGS KI.
  unfold guard_ok, A_GOT_GUARD, A_GUARD. intros (G1 & g & G2).
  split; [|exists g]; (eapply bytes_at_transfer; [eassumption|]; intros i Hi;
    rewrite length_le8 in Hi; refine (proj1 (KI _ _)); apply op_img_lit; lia).
Qed.

Lemma ki_ofl_one : forall h, ofl_one m h -> ofl_one m' h.
Proof using SEGS KI.
  unfold ofl_one, A_OFL_HEAD. intros h H. eapply rw_cells_transfer; [exact H|]. intros i Hi. cbn in Hi.
  apply KI. apply op_img_lit. lia.
Qed.

Lemma ki_ofl_empty : ofl_empty m -> ofl_empty m'.
Proof using SEGS KI.
  unfold ofl_empty, A_OFL_HEAD. intros H. eapply rw_cells_transfer; [exact H|]. intros i Hi. cbn in Hi.
  apply KI. apply op_img_lit. lia.
Qed.

End KeepImg.

End H.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis ERRNO : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis HFO : libreac_fuzz_fopen_contract B API.
Hypothesis HFR : fread_ro_contract.
Hypothesis HFC : fclose_contract B API.

Theorem pcap_source_open_holds : pcap_source_open_contract B API.
Proof.
  unfold pcap_source_open_contract.
  intros L A regs mem md ps pth b Fc f sw olen vtag vid pad b0 HSEG PRE A0 PSN PS8 PSS HPS HA11 PN0 HPB HPD HG HN26
    HBLK HSO HOE HGU RO RES ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  assert (IL : img_low B).
  { eapply img_low_of_check with (C := (symaddr ImgPages.Ubsan.top)); [unfold img_check; rewrite HSEG; vm_compute; reflexivity | lia]. }
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold OPEN_K in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof HPS as (_ & HP0 & HP24 & _). unfold ps_cells in HP24. cbn in HP24.
  pose proof HPB as (HPB0 & HPB1 & _).
  change (length (PATH_STR ++ [Z_to_bv 8 0])) with 13%nat in HPB1.
  assert (U10 : bv_unsigned (reg_get regs 10) = ps)
    by (change (reg_get regs 10) with (getr regs 10); rewrite A0; apply unsigned_lit; lia).
  assert (ST : stk rsegs mem (bv_unsigned sp - 8304) (bv_unsigned sp)).
  { pose proof (kb_stk B API IL 8304 L A regs mem md PRE0 ltac:(lia)) as X. rewrite HSEG in X. exact X. }
  assert (OUTW : forall x, ~ (bv_unsigned sp - 64 <= x < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 64, bv_unsigned sp)] x) by (intros x Hx; cbn; split; [exact Hx | exact I]).
  assert (NOWN0 : forall a, alloc_ceiling <= a -> ~ owned B L A a).
  { intros a Ha Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho). lia. }
  rewrite HSEG in RO, HWS, HERR.
  rewrite HSEG.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold PCAP_SOURCE_OPEN.
    eapply open_pro with (lo := bv_unsigned sp - 8304); [exact ST | lia]. }
  intros ms1 (can1 & (sp1 & m1 & junk & -> & SP1 & FR1 & MU1 & WM1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_open + 0x2c)%Z)) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); reflexivity).
  assert (E1_2 : getr R1 2 = sp1) by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); reflexivity).
  assert (E1_8 : getr R1 8 = reg_get regs 10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 pth) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); exact HA11).
  assert (E1_11 : getr R1 11 = Z_to_bv 64 A_MODE) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); reflexivity).
  assert (SPZ1 : spZ R1 = bv_unsigned sp - 64) by (unfold spZ; rewrite E1_2; exact SP1).
  pose proof (keep_munch _ _ _ 0 (bv_unsigned sp - 64) MU1 ltac:(lia) ltac:(lia) (fun x Hx => OUTW x ltac:(lia)))
    as KLO.
  pose proof (keep_munch _ _ _ (bv_unsigned sp) (2 ^ 64) MU1 ltac:(lia) ltac:(lia) (fun x Hx => OUTW x ltac:(lia)))
    as KHI.
  destruct (open_frame m1 _ junk _ _ _ _ FR1) as (junk' & FRa & FRb).
  replace (bv_unsigned sp - 64 + 8 + 24) with (bv_unsigned sp - 64 + 32) in FRb by lia.
  assert (MID1 : kb_mid B API 8304 (bv_unsigned sp) L A mem md (fun _ => False) L A m1 md).
  { eapply (kb_mid_A B API IL) with (W := [(bv_unsigned sp - 64, bv_unsigned sp)]);
      [ exact HMR | exact HWF | exact HBD | | exact MU1 | rewrite HSEG; exact WM1 | | ].
    - intros a [Ha|Ha]; rewrite HSEG; [apply HWS; lia | apply HERR; exact Ha].
    - intros x _ Hs _. apply OUTW. lia.
    - intros x Hx _. apply OUTW. lia. }
  assert (CP : call_pre_k B (aa_MR API) 8240 L A R1 m1 md).
  { eapply (kb_pre_A B API) with (K := 8304) (f := 64) (W := [(bv_unsigned sp - 64, bv_unsigned sp)]);
      [ exact PRE0 | lia | lia | lia | exact SPZ1 | | rewrite E1_4; reflexivity | | exact MU1
      | rewrite HSEG; exact WM1 | | ].
    - rewrite SPZ1. replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    - intros x _ Hx. change (spZ regs) with (bv_unsigned sp) in Hx. apply OUTW. lia.
    - intros x Hx _. apply OUTW. lia. }
  assert (HPB1' : bytes_at rsegs m1 pth (PATH_STR ++ [Z_to_bv 8 0])).
  { apply (bytes_at_transfer rsegs mem m1 pth _ HPB). intros i Hi. change (length (PATH_STR ++ [Z_to_bv 8 0])) with 13%nat in Hi.
    apply (munch_mbyte rsegs _ _ _ _ MU1); [lia | apply OUTW; lia]. }
  pose proof HFO as FO. unfold libreac_fuzz_fopen_contract in FO. rewrite HSEG in FO. unfold LIBREAC_FUZZ_FOPEN in FO.
  eapply SR_bind.
  { apply (FO L A R1 m1 md pth b Fc b0 eq_refl CP E1_10 PN0 HPB1').
    - rewrite SPZ1. unfold FOPEN_K. lia.
    - exact E1_11.
    - apply (kp_bytes_at mem m1 0 (bv_unsigned sp - 64) KLO); [exact HG | unfold G_FILE_LEN; lia |].
      rewrite length_app, !length_le8. unfold G_FILE_LEN. lia.
    - exact HN26.
    - intros HL1. destruct (HBLK HL1) as (INB & BF). split; [exact INB|].
      destruct (pl_in_blocks_user L A b _ INB) as (pb & Hpb & Eb).
      pose proof (mr_blocks_range B _ LAWS L A mem md pb _ HMR Hpb) as (Hb4k & HbC). rewrite Eb in Hb4k, HbC.
      apply (kp_bytes_at mem m1 0 (bv_unsigned sp - 64) KLO); [exact BF | lia | lia].
    - apply (kp_stdio_ok mem m1 0 (bv_unsigned sp - 64) KLO HSO); unfold A_LIBC, A_OFL_LOCK; lia.
    - apply (kp_ofl_empty mem m1 0 (bv_unsigned sp - 64) KLO HOE); unfold A_OFL_HEAD; lia.
    - apply (kp_guard_ok mem m1 0 (bv_unsigned sp - 64) KLO HGU); unfold A_GOT_GUARD, A_GUARD; lia.
    - exact (ro_agree_munch _ _ _ RO MU1 (fun x Hx => OUTW x ltac:(lia))).
    - exact RES.
    - exact ROOM. }
  intros c2 RET.
  destruct RET as (L1 & A1 & R2 & m2 & md1 & h & -> & POST & A0' & SO2 & GU2 & RO2 & HZ & HNZ).
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ POST) as [MIDc HPRES].
  pose proof POST as (HMR1 & HWF1 & HBD1 & HLE1 & HPA1 & _ & HVM1 & HFRAME1 & HBLKS1 & HSCR1).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR1) as (Hh1 & Hl1 & Hmat1).
  rewrite SPZ1 in MIDc. unfold FOPEN_K in *.
  rewrite E1_1.
  assert (G2 : reg_get R2 2 = sp1) by exact (eq_trans (HPRES 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (G4 : reg_get R2 4 = reg_get regs 4) by exact (eq_trans (HPRES 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (G8 : reg_get R2 8 = reg_get regs 10) by exact (eq_trans (HPRES 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (NOWN1 : forall a, alloc_ceiling <= a -> ~ owned B L1 A1 a).
  { intros a Ha Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HMR1 Ho). lia. }
  destruct (Nat.eq_dec (length Fc) 0) as [LZ|LNZ].
  - destruct (HZ LZ) as (-> & -> & -> & -> & MUz & OFE2 & RES2).
    rewrite SPZ1 in MUz.
    assert (MID2 : kb_mid B API 8304 (bv_unsigned sp) L A mem md (fun a => False \/ fopen_writes 0 a) L A m2 md).
    { eapply (kb_mid_seqAX B API); [exact MID1 | exact MIDc | lia | lia | lia | lia |].
      intros a _ _ (C & _). apply C. reflexivity. }
    assert (KZ : forall x, bv_unsigned sp - 64 <= x < 2 ^ 64 ->
       mbyte rsegs m2 x = mbyte rsegs m1 x /\ (writable_at rsegs m1 x -> writable_at rsegs m2 x)).
    { apply (keep_munch _ _ _ (bv_unsigned sp - 64) (2 ^ 64) MUz); [lia | lia |].
      intros x Hx. cbn. split; [lia | exact I]. }
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      eapply open_null with (sp0 := sp) (ra0 := reg_get regs 1) (s0o := reg_get regs 8) (s1o := reg_get regs 9)
        (s2o := reg_get regs 18).
      - exact A0'.
      - rewrite G8, U10. exact PSN.
      - rewrite G8, U10. exact PS8.
      - rewrite G2. exact SP1.
      - rewrite G8, U10. lia.
      - rewrite G8, U10. apply (kp_rw_cells m1 m2 _ _ KZ); [| lia | unfold ps_cells; cbn; lia].
        apply (kp_rw_cells mem m1 _ _ KHI); [exact HPS | lia | unfold ps_cells; cbn; lia].
      - rewrite G2, SP1. apply (kp_rw_cells m1 m2 _ _ KZ); [exact FRb | lia | cbn; lia]. }
    intros ms3 (can3 & (a3' & m3 & -> & PS3 & MU3 & WM3) & EQ3).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    rewrite G8, U10 in PS3, MU3.
    assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
    rewrite RP.
    apply SR_ret.
    exists L, A, R3, m3, md, 0.
    split; [reflexivity|].
    assert (OUT3 : forall x, x < ps -> outside [(ps, ps + 22)] x) by (intros x Hx; cbn; split; [lia | exact I]).
    pose proof (keep_munch _ _ _ 0 ps MU3 ltac:(lia) ltac:(lia) (fun x Hx => OUT3 x ltac:(lia))) as KL3.
    assert (MID3 : kb_mid B API 8304 (bv_unsigned sp) L A mem md
                     (fun a => (False \/ fopen_writes 0 a) \/ (ps <= a < ps + 22)) L A m3 md).
    { eapply (kb_mid_tail B API IL) with (W := [(ps, ps + 22)]);
        [ exact MID2 | exact MU3 | rewrite HSEG; exact WM3 | | | | ].
      - apply (op_present B HSEG _ _ _ MU3 WM3). intros x Hx Ho Hi.
        pose proof (in_img_low B HSEG x Hi). apply Ho. cbn. split; [lia | exact I].
      - intros x Hx Hs He. apply outside_one. lia.
      - intros x Hx _. apply outside_one. lia.
      - intros q n i Hin Hin' Hi.
        destruct (mr_blocks B _ LAWS L A mem md q n i HMR Hin Hi) as (_ & Hq1 & Hq2 & _).
        apply outside_one. lia. }
    assert (PRES : regs_preserved regs R3).
    { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9) || (r =? 18)) regs R1 R2 R3 _ _ X1 HPRES X3).
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | split; reflexivity]|]).
        subst r. split; reflexivity.
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | reflexivity]|]).
        subst r. discriminate O. }
    split.
    { apply (kb_post B API); [|exact PRES].
      eapply (kb_mid_E B API); [exact MID3|].
      intros a [[F|HW]|HW]; [destruct F | left; exact HW | right; left; exact HW]. }
    split; [apply (kp_stdio_ok m2 m3 0 ps KL3 SO2); unfold A_LIBC, A_OFL_LOCK; lia|].
    split; [apply (kp_guard_ok m2 m3 0 ps KL3 GU2); unfold A_GOT_GUARD, A_GUARD; lia|].
    split; [exact (ro_agree_munch _ _ _ RO2 MU3 (fun x Hx => OUT3 x ltac:(lia)))|].
    split.
    { intros _.
      split; [rewrite (getr_of_eqv _ _ 10 X3 eq_refl); reflexivity|].
      split; [exact PS3|].
      split; [apply (kp_ofl_empty m2 m3 0 ps KL3 OFE2); unfold A_OFL_HEAD; lia|].
      split; [reflexivity|].
      split.
      { intros a k i Hin _ Hi.
        destruct (block_facts B _ LAWS L A mem md a k i HMR Hin Hi) as (_ & Ha1 & Ha2 & _).
        rewrite (munch_mbyte (ms_segs B) _ _ _ _ MU3) by (try lia; apply OUT3; lia).
        rewrite (munch_mbyte (ms_segs B) _ _ _ _ MUz) by first [lia | cbn; split; [lia | exact I]].
        apply (munch_mbyte (ms_segs B) _ _ _ _ MU1); [lia | apply OUTW; lia]. }
      split; [intros q k Hin _; exact Hin|].
      split; [lia|].
      split; [intros _; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity | exact RES2]|].
      intros C. lia. }
    intros C. unfold pcap_good in C. rewrite LZ in C. cbn in C. discriminate C.
  - destruct (HNZ ltac:(lia)) as (HN0 & HAL16 & FRESH & BLK & KEPT & UBK & INIT & RLEN & RES1 & MSTL & OFL).
    destruct BLK as (b1 & b2 & EB1 & EB).
    pose proof FRESH as (FR4k & FRC & FRimg).
    destruct (HBLK ltac:(lia)) as (INB & BF).
    destruct (pl_in_blocks_user L A b _ INB) as (pb & Hpb & Eb).
    pose proof (mr_blocks_range B _ LAWS L A mem md pb _ HMR Hpb) as (Hb4k & HbC). rewrite Eb in Hb4k, HbC.
    assert (U2_10 : bv_unsigned (reg_get R2 10) = h)
      by (change (reg_get R2 10) with (getr R2 10); rewrite A0'; apply unsigned_lit; lia).
    assert (R2_10 : reg_get R2 10 = Z_to_bv 64 h) by exact A0'.
    assert (INH1 : In (h, 1304) (blocks L1 A1)) by (rewrite EB1; apply in_or_app; right; left; reflexivity).
    assert (MID2 : kb_mid B API 8304 (bv_unsigned sp) L A mem md (fun a => False \/ fopen_writes h a) L1 A1 m2 md1).
    { eapply (kb_mid_seqAX B API); [exact MID1 | exact MIDc | lia | lia | lia | lia |].
      intros a Ha1 Ha2 (_ & HW). unfold fmemopen_writes, A_OFL_HEAD in HW. lia. }
    assert (KH2 : forall a, bv_unsigned sp - 64 <= a < 2 ^ 64 ->
       mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a -> writable_at rsegs m2 a)).
    { intros a Ha. rewrite <- HSEG.
      destruct (HFRAME1 a ltac:(left; lia) (NOWN0 a ltac:(lia)) (NOWN1 a ltac:(lia))) as [E W].
      - unfold scratch_k. rewrite SPZ1. intros [H|H]; lia.
      - unfold fopen_writes, fmemopen_writes, A_OFL_HEAD. intros (_ & [H|H]); lia.
      - split; [exact E | intros Hw; apply W; exact Hw]. }
    eapply evt_SR_canon; [ | exact Hh1 | exact Hl1 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      eapply (open_mid HFR) with (lo := bv_unsigned sp - 8304) (b := b) (Fc := Fc) (f := f) (sw := sw) (olen := olen)
        (vtag := vtag) (vid := vid) (pad := pad) (junk := junk') (sp0 := sp) (ra0 := reg_get regs 1)
        (s0o := reg_get regs 8) (s1o := reg_get regs 9) (s2o := reg_get regs 18).
      - rewrite U2_10. exact HN0.
      - rewrite G8, U10. exact PSN.
      - rewrite G8, U10. exact PS8.
      - rewrite G2. exact SP1.
      - lia.
      - rewrite G8, U10. lia.
      - rewrite G8, U10. apply (kp_rw_cells m1 m2 _ _ KH2); [| lia | unfold ps_cells; cbn; lia].
        apply (kp_rw_cells mem m1 _ _ KHI); [exact HPS | lia | unfold ps_cells; cbn; lia].
      - rewrite G2, SP1. apply (kp_rw_cells m1 m2 _ _ KH2); [exact FRa | lia | cbn; lia].
      - rewrite G2, SP1. apply (kp_rw_cells m1 m2 _ _ KH2); [exact FRb | lia | cbn; lia].
      - rewrite G2, SP1. apply op_stk; [lia | lia |]. intros a Ha. rewrite <- HSEG. apply HSCR1.
        unfold scratch_k. rewrite SPZ1. left. lia.
      - rewrite G2, SP1. lia.
      - rewrite U2_10. exact MSTL.
      - rewrite U2_10. intros i Hi. unfold wa. apply (ro_addr_out B HSEG); [lia | apply FRimg; lia].
      - rewrite G2, SP1. intros i Hi. unfold wa. apply ro_addr_hi. lia.
      - rewrite G2, SP1. intros i Hi. unfold wa. apply ro_addr_hi. lia.
      - rewrite U2_10. lia.
      - lia.
      - lia.
      - exact RO2. }
    intros ms3 (can3 & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3
      & HOR & MU3 & WM3 & RO3) & EQ3).
    rewrite G2, SP1, U2_10, G8, U10 in MU3.
    assert (OUTI : forall a, in_img B a ->
      outside [(bv_unsigned sp - 64 - 112, bv_unsigned sp); (h, h + 1304); (ps, ps + 22)] a).
    { intros a Ha. pose proof (in_img_low B HSEG a Ha) as Hlow. cbn [outside].
      split; [lia|]. split; [|split; [lia | exact I]].
      intros Hin. apply (FRimg (a - h)); [lia|]. replace (h + (a - h)) with a by lia. exact Ha. }
    assert (KI3 : forall a, in_img B a ->
      mbyte rsegs m3 a = mbyte rsegs m2 a /\ (writable_at rsegs m2 a -> writable_at rsegs m3 a)).
    { intros a Ha. pose proof (in_img_low B HSEG a Ha) as Hlow.
      split; [apply (munch_mbyte rsegs _ _ _ _ MU3); [lia | exact (OUTI a Ha)]|].
      intros Hw. apply (proj1 (munch_writable rsegs _ _ _ a MU3 ltac:(lia) (OUTI a Ha))). exact Hw. }
    pose proof (ki_stdio_ok B HSEG m2 m3 KI3 SO2) as SO3.
    pose proof (ki_guard_ok B HSEG m2 m3 KI3 GU2) as GU3.
    pose proof (ki_ofl_one B HSEG m2 m3 KI3 h OFL) as OFL3.
    assert (MID3 : kb_mid B API 8304 (bv_unsigned sp) L A mem md
                     (fun a => (False \/ fopen_writes h a) \/
                        (fopen_writes h a \/ (ps <= a < ps + 22) \/ (ms_ctx B <= a < ms_ctx B + CTX_SIZE)))
                     L1 A1 m3 md1).
    { eapply (kb_mid_tail B API IL) with (W := [(bv_unsigned sp - 64 - 112, bv_unsigned sp); (h, h + 1304); (ps, ps + 22)]);
        [ exact MID2 | exact MU3 | rewrite HSEG; exact WM3 | | | | ].
      - apply (op_present B HSEG _ _ _ MU3 WM3). intros x Hx Ho Hi. apply Ho. exact (OUTI x Hi).
      - intros x Hx Hs He. cbn [outside]. split; [lia|]. split; [|split; [| exact I]].
        + intros Hin. apply He. left. split; [exact HN0 | right; lia].
        + intros Hin. apply He. right. left. lia.
      - intros x Hx Ho. cbn [outside]. split; [lia|]. split; [|split; [lia | exact I]].
        intros Hin. destruct (block_facts B _ LAWS L1 A1 m2 md1 h 1304 (x - h) HMR1 INH1 ltac:(lia)) as (_ & _ & _ & No).
        apply No. replace (h + (x - h)) with x by lia. exact Ho.
      - intros q n i Hin Hin' Hi.
        pose proof (pl_in_blocks_of_user L A q n Hin) as INq.
        destruct (mr_blocks B _ LAWS L A mem md q n i HMR Hin Hi) as (_ & Hq1 & Hq2 & _).
        rewrite EB in INq.
        destruct (blocks_mid_disjoint B _ LAWS L1 A1 m2 md1 b1 b2 h 1304 _ _ HMR1 EB1 INq) as [D|D];
          cbn [outside]; (split; [lia|]); (split; [lia|]); (split; [lia | exact I]). }
    assert (KB3 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k ->
                    mbyte (ms_segs B) m3 (a + i) = mbyte (ms_segs B) mem (a + i)).
    { intros a k i Hin Hi.
      destruct (block_facts B _ LAWS L A mem md a k i HMR Hin Hi) as (_ & Ha1 & Ha2 & _).
      pose proof Hin as Hin2. rewrite EB in Hin2.
      destruct (blocks_mid_disjoint B _ LAWS L1 A1 m2 md1 b1 b2 h 1304 _ _ HMR1 EB1 Hin2) as [D|D];
        (rewrite (munch_mbyte (ms_segs B) _ _ _ _ MU3)
           by first [lia | cbn [outside]; (split; [lia|]); (split; [lia|]); (split; [lia | exact I])]);
        (rewrite (KEPT a k i Hin ltac:(tauto) Hi));
        (apply (munch_mbyte (ms_segs B) _ _ _ _ MU1); [lia | apply OUTW; lia]). }
    destruct HOR as [(GD & -> & PS3 & MS3) | (BD & (s1' & s2' & ->) & PS3 & FR3 & MS3)];
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
    + rewrite G8, U10, R2_10 in PS3. rewrite U2_10 in MS3.
      assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
      rewrite RP.
      apply SR_ret.
      exists L1, A1, R3, m3, md1, h.
      split; [reflexivity|].
      assert (PRES : regs_preserved regs R3).
      { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9) || (r =? 18)) regs R1 R2 R3 _ _ X1 HPRES X3).
        - intros r Hr O. unfold callee_saved in Hr.
          assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
          repeat (destruct C as [C|C]; [subst r; first [discriminate O | split; reflexivity]|]).
          subst r. split; reflexivity.
        - intros r Hr O. unfold callee_saved in Hr.
          assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
          repeat (destruct C as [C|C]; [subst r; first [discriminate O | reflexivity]|]).
          subst r. discriminate O. }
      split.
      { apply (kb_post B API); [|exact PRES].
        eapply (kb_mid_E B API); [exact MID3|].
        intros a [[F|HW]|[HW|[HW|HW]]];
          [destruct F | left; exact HW | left; exact HW | right; left; exact HW | right; right; split; [exact HN0 | exact HW]]. }
      split; [exact SO3|]. split; [exact GU3|]. split; [exact RO3|].
      split; [intros C; congruence|].
      intros _.
      split; [rewrite (getr_of_eqv _ _ 10 X3 eq_refl); reflexivity|].
      split; [exact HN0|]. split; [exact HAL16|]. split; [exact FRESH|].
      split; [exact PS3|].
      split; [exists b1, b2; split; [exact EB1 | exact EB]|].
      split; [intros a k i Hin _ Hi; exact (KB3 a k i Hin Hi)|].
      split; [exact UBK|]. split; [exact INIT|]. split; [exact RLEN|]. split; [exact RES1|].
      split; [exact MS3 | exact OFL3].
    + rewrite G8, U10, R2_10 in PS3. rewrite U2_10 in MS3. rewrite G2, SP1 in FR3.
      assert (E3_1 : getr R3 1 = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_pcap_source_open + 0xc8)%Z)) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); reflexivity).
      assert (E3_2 : getr R3 2 = sp1) by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); exact G2).
      assert (E3_4 : getr R3 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); exact G4).
      assert (E3_8 : getr R3 8 = reg_get regs 10) by (rewrite (getr_of_eqv _ _ 8 X3 eq_refl); exact G8).
      assert (E3_10 : getr R3 10 = Z_to_bv 64 h) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); exact R2_10).
      assert (SPZ3 : spZ R3 = bv_unsigned sp - 64) by (unfold spZ; rewrite E3_2; exact SP1).
      assert (CP2 : call_pre_k B (aa_MR API) 8240 L1 A1 R3 m3 md1).
      { eapply (op_pre B API) with (K := 8304) (f := 64) (regs := regs) (mem := mem) (md := md) (L := L) (A := A);
          [ exact PRE0 | exact MID3 | exact INIT | lia | lia | lia | exact SPZ3 | | rewrite E3_4; reflexivity | ].
        - rewrite SPZ3. replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring.
          rewrite Z.mod_add by lia. exact HAL.
        - rewrite E3_1. apply bv_eq. vm_compute. reflexivity. }
      pose proof MID3 as (HMR3 & _).
      pose proof HFC as FC. unfold fclose_contract in FC. rewrite HSEG in FC. unfold FCLOSE in FC.
      eapply SR_bind.
      { apply (FC L1 A1 R3 m3 md1 h b (Z.min 24 (Z.of_nat (length Fc))) Fc (sb_malloc b0 1304) eq_refl CP2 E3_10 INH1).
        - rewrite EB1. rewrite EB in INB. apply in_app_or in INB as [I|I]; apply in_or_app; [left; exact I | right; right; exact I].
        - exact MS3.
        - exact OFL3.
        - exact SO3.
        - exact GU3.
        - exact RO3.
        - exact RES1. }
      intros c4 RET2.
      destruct RET2 as (L2 & A2 & R4 & m4 & md2 & -> & POST2 & A0'' & BLK2 & KEPT2 & UBK2 & INIT2 & RLEN2 & RES2
        & OFE4 & SO4 & GU4 & RO4 & BF4).
      destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ POST2) as [MIDc2 HPRES2].
      pose proof POST2 as (HMR2 & HWF2 & HBD2 & HLE2 & HPA2 & _ & HVM2 & HFRAME2 & HBLKS2 & HSCR2).
      destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & Hmat2).
      rewrite SPZ3 in MIDc2. unfold FCLOSE_K in *.
      assert (NOWN2 : forall a, alloc_ceiling <= a -> ~ owned B L2 A2 a).
      { intros a Ha Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HMR2 Ho). lia. }
      assert (MID4 : kb_mid B API 8304 (bv_unsigned sp) L A mem md
                       (fun a => ((False \/ fopen_writes h a) \/
                          (fopen_writes h a \/ (ps <= a < ps + 22) \/ (ms_ctx B <= a < ms_ctx B + CTX_SIZE))) \/
                          fclose_writes h a) L2 A2 m4 md2).
      { eapply (op_seqXX B API); [exact MID3 | exact MIDc2 | exact UBK | exact RLEN | | lia | lia | lia | lia |].
        - intros a Ha No No2 NE1 NE2 [Hao|Hst]; [|apply No; right; exact Hst].
          apply NE1. right. right. right. exact (ax_img AX L1 A1 m3 md1 a HMR3 Ha Hao).
        - intros a Ha1 Ha2 HW. unfold fclose_writes, A_OFL_HEAD in HW. lia. }
      assert (G4_2 : reg_get R4 2 = sp1) by exact (eq_trans (HPRES2 2 ltac:(unfold callee_saved; lia)) E3_2).
      assert (G4_8 : reg_get R4 8 = reg_get regs 10)
        by exact (eq_trans (HPRES2 8 ltac:(unfold callee_saved; lia)) E3_8).
      assert (KH4 : forall a, bv_unsigned sp - 64 <= a < 2 ^ 64 ->
         mbyte rsegs m4 a = mbyte rsegs m3 a /\ (writable_at rsegs m3 a -> writable_at rsegs m4 a)).
      { intros a Ha. rewrite <- HSEG.
        destruct (HFRAME2 a ltac:(left; lia) (NOWN1 a ltac:(lia)) (NOWN2 a ltac:(lia))) as [E W].
        - unfold scratch_k. rewrite SPZ3. intros [H|H]; lia.
        - unfold fclose_writes, A_OFL_HEAD. intros [H|H]; lia.
        - split; [exact E | intros Hw; apply W; exact Hw]. }
      rewrite E3_1.
      eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of.
        eapply open_tail with (sp0 := sp) (ra0 := reg_get regs 1) (s0o := reg_get regs 8) (s1o := reg_get regs 9)
          (s2o := reg_get regs 18) (f := Z_to_bv 64 h) (sw := sw) (olen := wz 0) (vtag := wz 0) (vid := wz 0) (pad := pad).
        - rewrite G4_2. exact SP1.
        - rewrite G4_8, U10. lia.
        - rewrite G4_8, U10. apply (kp_rw_cells m3 m4 _ _ KH4); [exact PS3 | lia | unfold ps_cells; cbn; lia].
        - rewrite G4_2, SP1. apply (kp_rw_cells m3 m4 _ _ KH4); [exact FR3 | lia | cbn; lia]. }
      intros ms5 (can5 & (m5 & -> & PS5 & MU5 & WM5) & EQ5).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
      rewrite G4_8, U10 in PS5, MU5.
      assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
      rewrite RP.
      apply SR_ret.
      exists L2, A2, R5, m5, md2, h.
      split; [reflexivity|].
      assert (OUT5 : forall x, x < ps -> outside [(ps, ps + 8)] x) by (intros x Hx; cbn; split; [lia | exact I]).
      pose proof (keep_munch _ _ _ 0 ps MU5 ltac:(lia) ltac:(lia) (fun x Hx => OUT5 x ltac:(lia))) as KL5.
      assert (MID5 : kb_mid B API 8304 (bv_unsigned sp) L A mem md
                       (fun a => (((False \/ fopen_writes h a) \/
                          (fopen_writes h a \/ (ps <= a < ps + 22) \/ (ms_ctx B <= a < ms_ctx B + CTX_SIZE))) \/
                          fclose_writes h a) \/ (ps <= a < ps + 8)) L2 A2 m5 md2).
      { eapply (kb_mid_tail B API IL) with (W := [(ps, ps + 8)]);
          [ exact MID4 | exact MU5 | rewrite HSEG; exact WM5 | | | | ].
        - apply (op_present B HSEG _ _ _ MU5 WM5). intros x Hx Ho Hi.
          pose proof (in_img_low B HSEG x Hi). apply Ho. cbn. split; [lia | exact I].
        - intros x Hx Hs He. apply outside_one. lia.
        - intros x Hx _. apply outside_one. lia.
        - intros q n i Hin Hin' Hi.
          destruct (mr_blocks B _ LAWS L A mem md q n i HMR Hin Hi) as (_ & Hq1 & Hq2 & _).
          apply outside_one. lia. }
      assert (PRES : regs_preserved regs R5).
      { eapply (op_chain2 (fun r => (r =? 2) || (r =? 8) || (r =? 9) || (r =? 18)) regs R1 R2 R3 R4 R5 _ _ _ X1 HPRES X3 HPRES2 X5).
        - intros r Hr O. unfold callee_saved in Hr.
          assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
          repeat (destruct C as [C|C]; [subst r; first [discriminate O | split; [reflexivity | split; reflexivity]]|]).
          subst r. split; [reflexivity | split; reflexivity].
        - intros r Hr O. unfold callee_saved in Hr.
          assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
          repeat (destruct C as [C|C]; [subst r; first [discriminate O | reflexivity]|]).
          subst r. discriminate O. }
      split.
      { apply (kb_post B API); [|exact PRES].
        eapply (kb_mid_E B API); [exact MID5|].
        intros a [[[[F|HW]|[HW|[HW|HW]]]|HW]|HW];
          [ destruct F | left; exact HW | left; exact HW | right; left; exact HW
          | right; right; split; [exact HN0 | exact HW] | left; split; [exact HN0 | exact HW]
          | right; left; lia ]. }
      split; [apply (kp_stdio_ok m4 m5 0 ps KL5); [exact SO4 | unfold A_LIBC; lia | unfold A_OFL_LOCK; lia]|].
      split; [apply (kp_guard_ok m4 m5 0 ps KL5); [exact GU4 | unfold A_GOT_GUARD; lia | unfold A_GUARD; lia]|].
      split; [exact (ro_agree_munch _ _ _ RO4 MU5 (fun x Hx => OUT5 x ltac:(lia)))|].
      split.
      { intros _.
        split; [rewrite (getr_of_eqv _ _ 10 X5 eq_refl); reflexivity|].
        split; [exact PS5|].
        split; [apply (kp_ofl_empty m4 m5 0 ps KL5 OFE4); unfold A_OFL_HEAD; lia|].
        split.
        { destruct BLK2 as (c1 & c2 & EC1 & EC2). rewrite EC2, EB.
          symmetry. apply (op_rm_unique b1 b2 c1 c2 (h, 1304)).
          - rewrite <- EB1. exact (mr_blocks_disjoint B _ LAWS L1 A1 m3 md1 HMR3).
          - cbn. lia.
          - rewrite <- EB1. exact EC1. }
        split.
        { intros a k i Hin _ Hi.
          destruct (block_facts B _ LAWS L A mem md a k i HMR Hin Hi) as (_ & Ha1 & Ha2 & _).
          pose proof Hin as Hin2. rewrite EB in Hin2.
          assert (Hne : a <> h).
          { destruct (blocks_mid_disjoint B _ LAWS L1 A1 m2 md1 b1 b2 h 1304 _ _ HMR1 EB1 Hin2) as [D|D]; lia. }
          assert (Hin1 : In (a, k) (blocks L1 A1)).
          { rewrite EB1. apply in_app_or in Hin2 as [I|I]; apply in_or_app; [left; exact I | right; right; exact I]. }
          rewrite (munch_mbyte (ms_segs B) _ _ _ _ MU5) by (try lia; apply OUT5; lia).
          rewrite (KEPT2 a k i Hin1 Hne Hi).
          exact (KB3 a k i Hin Hi). }
        split.
        { intros q k Hin Hne. apply (UBK2 q k (UBK q k Hin)). rewrite (HPA1 q k Hin (UBK q k Hin)). exact Hne. }
        split; [lia|].
        split; [intros C; lia|].
        intros _. split; [exact HN0|]. split; [exact FRESH|]. split; [exact (INIT2 INIT)|]. split; [exact RES2|].
        apply (kp_bytes_at m4 m5 0 ps KL5); [exact BF4 | lia | lia]. }
      intros C. congruence.
Qed.

End K.
