(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AC1_realloc ECH_AStmt_C7 ECH_AKit ECH_AsKit ECH_AC7_kit ECH_AC7_rd ECH_AC7_rd2 ECH_AC14_bio2buf_seg ECH_AC14_ladder_seg ECH_AStmt_C14.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition mb_static (R R' : membio) : Prop :=
  mb_buf R' = mb_buf R /\ mb_len R' = mb_len R /\ mb_bb R' = mb_bb R /\ mb_bm R' = mb_bm R /\ mb_rp R' = mb_rp R
  /\ mb_id R' = mb_id R /\ mb_bbid R' = mb_bbid R /\ mb_bmid R' = mb_bmid R /\ mb_rpid R' = mb_rpid R.
Lemma mb_static_refl : forall R, mb_static R R.
Proof. intros R. repeat split; reflexivity. Qed.
Lemma mb_static_read : forall R R' n, mb_static R R' -> mb_static R (mb_after_read R' n).
Proof. intros R R' n S. exact S. Qed.
Lemma mb_static_blocks : forall a R R', mb_static R R' -> blocks_MEMBIO a R' = blocks_MEMBIO a R.
Proof. intros a R R' (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9). unfold blocks_MEMBIO. congruence. Qed.
Lemma mb_static_foot : forall a R R', mb_static R R' -> MEMBIO_foot a R' = MEMBIO_foot a R.
Proof. intros a R R' (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9). unfold MEMBIO_foot. congruence. Qed.
Lemma mb_static_below : forall a R R' lo, mb_static R R' -> MEMBIO_below a R lo -> MEMBIO_below a R' lo.
Proof. intros a R R' lo (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9) B. unfold MEMBIO_below in *. rewrite S3, S4, S5. exact B. Qed.
Lemma mb_static_apart : forall a R R', mb_static R R' -> MEMBIO_apart a R -> MEMBIO_apart a R'.
Proof. intros a R R' (S1 & S2 & S3 & S4 & S5 & _) AP. unfold MEMBIO_apart in *. rewrite S3, S4, S5. exact AP. Qed.
Lemma mb_static_sep : forall a R R', mb_static R R' -> MEMBIO_sep a R -> MEMBIO_sep a R'.
Proof.
  intros a R R' ST SE. destruct SE as (AP & E1 & E2 & E3 & E4). split; [exact (mb_static_apart a R R' ST AP)|].
  destruct ST as (S1 & S2 & S3 & S4 & S5 & _). rewrite S1, S2, S3, S4, S5. exact (conj E1 (conj E2 (conj E3 E4))).
Qed.
Lemma mb_static_shad : forall m a R R', mb_static R R' -> MEMBIO_shad m a R -> MEMBIO_shad m a R'.
Proof. intros m a R R' (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9) B. unfold MEMBIO_shad in *. rewrite S3, S4, S5. exact B. Qed.
Lemma mb_static_pay : forall m R R', mb_static R R' -> PAYLOAD_shad m R -> PAYLOAD_shad m R'.
Proof. intros m R R' (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9) B. unfold PAYLOAD_shad in *. rewrite S1, S2. exact B. Qed.
Lemma mb_after_read_pos : forall R n, mb_pos (mb_after_read R n) = mb_pos R + n.
Proof. intros R n. reflexivity. Qed.
Lemma mb_after_read_len : forall R n, mb_len (mb_after_read R n) = mb_len R.
Proof. intros R n. reflexivity. Qed.
Lemma firstn_app_skipn : forall (l : list byte) a b, firstn a l ++ firstn b (skipn a l) = firstn (a + b) l.
Proof.
  intros l a b. revert l. induction a as [|a IH]; intros l; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity| f_equal; apply IH].
Qed.

Definition LAD_STACK : Z := Z.max BIOREADEX_STACK (Z.max BIOEOF_STACK CREALLOC_STACK).
(* [comment removed for export] *)
Definition lad_cm (k : Z) : Z := 256 * k * (k + 3).
Definition lad_cf (k : Z) : Z := 256 * k * (k + 1).

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HX.

  (* [comment removed for export] *)
  Variables (esp : word) (S1 : Z) (gp : word) (F : bvmap 5 word) (fc : bv 32) (mb lo B : Z) (R : membio) (ds : list byte)
            (LB Lh : list block) (m0 : mem) (mo0 : Model) (ff : Z) (s3v : word) (rra : Z) (CHw : list (Z * Z)) (AL0 : Z)
            (LFx : list fframe) (fpx : Z).
  Let RBP : Z := ff + 2256.
  Let XW : list (Z * Z) := (RBP, RBP + 8) :: (S1 + 184, S1 + 192) :: MEMBIO_foot mb R.
  (* [comment removed for export] *)
  Let CHrp : list (Z * Z) := (bv_unsigned esp, rra) :: CHw.
  Hypothesis MBB : MEMBIO_below mb R lo.
  Hypothesis MBS : MEMBIO_sep mb R.
  Hypothesis DSL : zlength ds = mb_len R.
  Hypothesis SUBLB : forall b, In b LB -> In b Lh.
  Hypothesis PAYL : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB.
  Hypothesis BUDB : lb_bytes Lh + 512 * 65 <= as_LIVE_MAX H.
  Hypothesis BUDC : Z.of_nat (length Lh) + 2 <= as_LIVE_CNT_MAX H.
  Hypothesis BUDA : as_Cm H (lad_cm 32) + as_Cf H (lad_cf 32) <= AL0.
  Hypothesis SPB : bv_unsigned esp <= B.
  Hypothesis CEIL : aceil <= lo.
  Hypothesis S1R : bv_unsigned esp - 464 <= S1 <= bv_unsigned esp - 448.
  Hypothesis S1A : S1 mod 32 = 0.
  Hypothesis LO : lo <= S1 - LAD_STACK.
  Hypothesis FFR : as_FSB H + AFS_HDR <= ff /\ ff + 4096 <= as_FSB H + AFS_SIZE /\ ff mod 32 = 0.
  Hypothesis FSB : afsb_ok H.
  Hypothesis CHB : forall fp ra, In (fp, ra) CHw -> bv_unsigned esp + 16 <= fp.
  Hypothesis PFR : pf_ok (as_TR H) PF_crealloc R_rp_CRYPTO_realloc CHrp.
  (* [comment removed for export] *)
  Hypothesis FFL : In (6, ff, fpx) LFx.

  (* [comment removed for export] *)
  Definition LAD (k : Z) (m : mem) (s : as_St H) (p : bptr) (A : Z) (R' : membio) : Prop :=
       as_RHEAP H s ((p, A, 512 * (k + 1)) :: Lh) m
    /\ MEMBIO H LB m mb R' /\ mb_static R R' /\ mb_pos R' = 512 * k /\ 512 * k < mb_len R
    /\ bytes_at asegs m (mb_buf R) ds
    /\ rw_cells asegs m A [CB (Z.to_nat (512 * k)) (firstn (Z.to_nat (512 * k)) ds)]
    /\ (exists junk, rw_cells asegs m (A + 512 * k) [CB 512 junk])
    /\ (exists rb, rw_cells asegs m RBP [C8 (wz rb)])
    /\ (exists errv, rw_cells asegs m (errno_addr (Z_to_bv 64 ATP)) [C4 errv])
    /\ METH_mem m /\ IMPL_mem m /\ GOT_mem m
    /\ mem_inv asegs m /\ stk asegs m lo S1 /\ as_rauxv_ok H m B
    /\ xpres H Lh S1 XW m0 m
    (* [comment removed for export] *)
    /\ ACONST m /\ as_RFS H LFx m /\ addressable m A (512 * (k + 1)) /\ MEMBIO_shad m mb R' /\ PAYLOAD_shad m R
    /\ rw_cells asegs m (sh RBP) [C1 (b8 0)]
    /\ as_chain H m (bv_unsigned esp) CHrp
    /\ as_AL H s + as_Cm H (lad_cm k) + as_Cf H (lad_cf k) >= AL0
    /\ rw_cells asegs m (S1 + 168) [C8 (wz ARP_FILE)]
    /\ (exists v, rw_cells asegs m (S1 + 184) [C8 v]).

  (* [comment removed for export] *)
  Definition lad_entry (k : Z) (m : mem) (A : Z) (s4v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state :=
    MS (mkR (Z_to_bv 64 ARP_R3) (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) t0 t1 t2 esp (Z_to_bv 64 S1) (Z_to_bv 64 mb) (Z_to_bv 64 (A + 512 * k)) (Z_to_bv 64 512) (Z_to_bv 64 RBP) a4 a5 a6 a7
            (Z_to_bv 64 512) s3v (Z_to_bv 64 A) (Z_to_bv 64 (- (512 * k))) (Z_to_bv 64 mb) (Z_to_bv 64 (A + 512 * k)) (Z_to_bv 64 (32 - k))
            (Z_to_bv 64 RBP) s4v (Z_to_bv 64 (512 * k)) t3 t4 t5 t6)
       F (Z_to_bv 64 P_BIO_read_ex) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  Definition lad_doneK (Q : config -> Prop) : Prop :=
    forall (k n : Z) (m : mem) (msF : machine_state) (mo : Model) (s : as_St H) (p : bptr) (A : Z) (R' : membio) (junk : list byte)
           (s4v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      0 <= k <= 31 -> n = mb_len R - 512 * k -> 1 <= n <= 512 ->
      as_VIS H s msF = MS (mkR (Z_to_bv 64 ALD_RD) (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) t0 t1 t2 esp (Z_to_bv 64 S1) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 512) s3v (Z_to_bv 64 A) (Z_to_bv 64 (- (512 * k))) (Z_to_bv 64 mb) (Z_to_bv 64 (A + 512 * k)) (Z_to_bv 64 (32 - k))
                              (Z_to_bv 64 RBP) s4v (Z_to_bv 64 (512 * k)) t3 t4 t5 t6)
                         F (ret_pc (Z_to_bv 64 ALD_RD)) fc None m (seg_rom asegs) ->
      as_RHEAP H s ((p, A, 512 * (k + 1)) :: Lh) m -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
      MEMBIO H LB m mb R' -> mb_static R R' -> mb_pos R' = mb_len R ->
      bytes_at asegs m (mb_buf R) ds -> bytes_at asegs m A ds ->
      rw_cells asegs m A [CB (Z.to_nat (mb_len R)) ds; CB (Z.to_nat (512 * (k + 1) - mb_len R)) junk] ->
      rw_cells asegs m RBP [C8 (wz n)] -> (exists errv, rw_cells asegs m (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
      METH_mem m -> IMPL_mem m -> GOT_mem m -> mem_inv asegs m -> stk asegs m lo S1 -> as_rauxv_ok H m B ->
      xpres H Lh S1 XW m0 m ->
      ACONST m -> as_RFS H LFx m -> addressable m A (512 * (k + 1)) -> MEMBIO_shad m mb R' -> PAYLOAD_shad m R -> rw_cells asegs m (sh RBP) [C1 (b8 0)] ->
      as_chain H m (bv_unsigned esp) CHrp -> as_AL H s + as_Cm H (lad_cm 32) + as_Cf H (lad_cf 32) >= AL0 ->
      rw_cells asegs m (S1 + 168) [C8 (wz ARP_FILE)] -> rw_cells asegs m (S1 + 184) [C8 (wz A)] ->
      as_SR H Q (mkCfg msF mo).

  (* [comment removed for export] *)
  Definition lad_capK (Q : config -> Prop) : Prop :=
    forall (m : mem) (msF : machine_state) (mo : Model) (s : as_St H) (p : bptr) (A rv : Z) (R' : membio)
           (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5v s7v s10v s11v t3 t4 t5 t6 : word),
      as_VIS H s msF = MS (mkR (Z_to_bv 64 ALD_RC) (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) t0 t1 t2 esp (Z_to_bv 64 S1) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 512) s3v (Z_to_bv 64 A) s5v (Z_to_bv 64 mb) s7v (Z_to_bv 64 0) (Z_to_bv 64 RBP) s10v s11v t3 t4 t5 t6)
                         F (ret_pc (Z_to_bv 64 ALD_RC)) fc None m (seg_rom asegs) ->
      as_RHEAP H s ((p, A, 512 * 33) :: Lh) m -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
      MEMBIO H LB m mb R' -> mb_static R R' -> mb_pos R' = 512 * 32 -> 512 * 32 < mb_len R ->
      bytes_at asegs m (mb_buf R) ds -> (exists junk, rw_cells asegs m A [CB (Z.to_nat (512 * 33)) junk]) -> (exists rb, rw_cells asegs m RBP [C8 (wz rb)]) -> (exists errv, rw_cells asegs m (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
      METH_mem m -> IMPL_mem m -> GOT_mem m -> mem_inv asegs m -> stk asegs m lo S1 -> as_rauxv_ok H m B ->
      xpres H Lh S1 XW m0 m ->
      ACONST m -> as_RFS H LFx m -> addressable m A (512 * 33) -> MEMBIO_shad m mb R' -> PAYLOAD_shad m R -> rw_cells asegs m (sh RBP) [C1 (b8 0)] ->
      as_chain H m (bv_unsigned esp) CHrp -> as_AL H s + as_Cm H (lad_cm 32) + as_Cf H (lad_cf 32) >= AL0 ->
      rw_cells asegs m (S1 + 168) [C8 (wz ARP_FILE)] -> rw_cells asegs m (S1 + 184) [C8 (wz A)] ->
      as_SR H Q (mkCfg msF mo).

  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma lad_head_facts : forall s p A n m,
    as_RHEAP H s ((p, A, n) :: Lh) m ->
    ablock_range H A n /\ ~ In p (map blk_id Lh)
    /\ (forall b, In b Lh -> A + n + 16 <= blk_addr b \/ blk_addr b + blk_size b + 16 <= A)
    /\ (forall b, In b Lh -> ablock_range H (blk_addr b) (blk_size b))
    /\ shvis m A (A + n).
  Proof.
    intros s p A n m HP.
    pose proof (ah_blocks H HH _ _ _ _ HP (or_introl eq_refl)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof (ah_nodup H HH _ _ _ HP) as ND. cbn [map blk_id fst snd] in ND.
    assert (NI : ~ In p (map blk_id Lh)) by (inversion ND; assumption).
    split; [exact BR|]. split; [exact NI|]. split; [| split].
    - intros b Hb. pose proof (ah_disj H HH _ _ _ (p, A, n) b HP (or_introl eq_refl) (or_intror Hb)) as D.
      cbn [blk_addr blk_size blk_id fst snd] in D. apply D. intros E. apply NI. rewrite E. apply in_map. exact Hb.
    - intros b Hb. exact (ah_blocks H HH _ _ _ _ HP (or_intror Hb)).
    - exact (ah_blk_shvis H HH _ _ _ _ _ _ HP (or_introl eq_refl)).
  Qed.
  Local Ltac unf_stk_in K := unfold LAD_STACK, BIOREADEX_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, BIOCTRL_STACK, MEMCTRL_STACK, MEMREAD_STACK,
      CREALLOC_STACK, AREALLOC_STACK, AINTRIN_STACK, FR_BIO_set_data, FR_bio_read_intern, FR_bread_conv, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl,
      FR_BIO_eof, FR_CRYPTO_realloc in K.
  Local Ltac unf_stk := unfold LAD_STACK, BIOREADEX_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, BIOCTRL_STACK, MEMCTRL_STACK, MEMREAD_STACK,
      CREALLOC_STACK, AREALLOC_STACK, AINTRIN_STACK, FR_BIO_set_data, FR_bio_read_intern, FR_bread_conv, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl,
      FR_BIO_eof, FR_CRYPTO_realloc.

  (* [comment removed for export] *)
  Lemma lad_geo : forall s p A n m, as_RHEAP H s ((p, A, n) :: Lh) m ->
    0x7fff7f800000 <= aceil /\ aceil <= lo /\ lo + 100 <= S1 /\ S1 + 416 <= bv_unsigned esp /\ bv_unsigned esp < 2^64
    /\ AIMG_TOP <= as_FSB H /\ as_FSB H + AFS_HDR <= ff /\ ff + 4096 <= as_FSB H + AFS_SIZE /\ as_FSB H + AFS_SIZE <= aceil /\ aapp (as_FSB H) AFS_SIZE
    /\ 0 < A /\ AIMG_TOP <= A /\ A + n <= aceil /\ aapp A n /\ (A + n + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= A - 16) /\ aceil <= 0x7fffff800000.
  Proof.
    intros s p A n m HP. acb. pose proof (aword_range esp) as ER. unf_stk_in LO.
    destruct (lad_head_facts _ _ _ _ _ HP) as ((B1 & B2 & B3 & B4 & B5 & B6 & B7) & _).
    destruct FSB as (F1 & F2 & F3 & F4). destruct FFR as (G1 & G2 & G3).
    repeat split; try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lad_read : forall k m msF mo s p A R' (s4v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Q : config -> Prop),
    0 <= k <= 31 -> LAD k m s p A R' -> rw_cells asegs m (S1 + 184) [C8 (wz A)] -> as_VIS H s msF = lad_entry k m A s4v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 -> as_AKREL H s (mkCfg msF mo) ->
    (forall m2 msF2 mo2 (R2 : membio) (n : Z) (junk' : list byte) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
       n = Z.min 512 (mb_len R - 512 * k) -> R2 = mb_after_read R' n ->
       as_VIS H s msF2 = MS (mkR (Z_to_bv 64 ALD_R1) (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) u0 u1 u2 esp (Z_to_bv 64 S1)
                                  (Z_to_bv 64 (mem_ctrl_rv R2 BIO_CTRL_EOF)) b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 512) s3v (Z_to_bv 64 A) (Z_to_bv 64 (- (512 * k))) (Z_to_bv 64 mb) (Z_to_bv 64 (A + 512 * k)) (Z_to_bv 64 (32 - k))
                                  (Z_to_bv 64 RBP) s4v (Z_to_bv 64 (512 * k)) u3 u4 u5 u6)
                             F (ret_pc (Z_to_bv 64 ALD_R1)) fc None m2 (seg_rom asegs) ->
       as_AKREL H s (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
       as_RHEAP H s ((p, A, 512 * (k + 1)) :: Lh) m2 -> MEMBIO H LB m2 mb R2 ->
       bytes_at asegs m2 (mb_buf R) ds -> rw_cells asegs m2 A [CB (Z.to_nat (512 * k)) (firstn (Z.to_nat (512 * k)) ds)] ->
       rw_cells asegs m2 (A + 512 * k) [CB (Z.to_nat n) (mb_take R' ds n); CB (Z.to_nat 512 - Z.to_nat n) junk'] ->
       rw_cells asegs m2 RBP [C8 (wz n)] -> (exists errv, rw_cells asegs m2 (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
       METH_mem m2 -> IMPL_mem m2 -> GOT_mem m2 -> mem_inv asegs m2 -> stk asegs m2 lo S1 -> as_rauxv_ok H m2 B ->
       xpres H Lh S1 XW m0 m2 ->
       ACONST m2 -> as_RFS H LFx m2 -> addressable m2 A (512 * (k + 1)) -> MEMBIO_shad m2 mb R2 -> PAYLOAD_shad m2 R -> rw_cells asegs m2 (sh RBP) [C1 (b8 0)] ->
       as_chain H m2 (bv_unsigned esp) CHrp -> as_AL H s + as_Cm H (lad_cm k) + as_Cf H (lad_cf k) >= AL0 ->
       rw_cells asegs m2 (S1 + 168) [C8 (wz ARP_FILE)] -> rw_cells asegs m2 (S1 + 184) [C8 (wz A)] ->
       as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros k m msF mo s p A R' s4v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 Q KR INV SA VIS KREL KONT.
    destruct INV as (HP & MBO & MST & POS & KL & DS & PRE & [junk JK] & [rb RB] & [errv ERR] & ME & IM & GM & MI & ST & AUX & XP
                     & AC & RF & AD & MSH & PAY & SHB & CHN & ALB & SF & _).
    pose proof (lad_geo _ _ _ _ _ HP) as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
    unfold AIMG_TOP, AFS_HDR, AFS_SIZE in G5, G6, G7, G8, G9, G11, G14.
    assert (RBPE : RBP = ff + 2256) by reflexivity.
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
    assert (LO0 : 0 <= lo) by lia. pose proof LO as LOS. unf_stk_in LOS.
    destruct (lad_head_facts _ _ _ _ _ HP) as (BR & NIP & DISJ & BLK & SV).
    pose proof MST as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
    pose proof MBO as MB0. destruct MB0 as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _).
    rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I1. rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I2. rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I3. rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I4.
    pose proof (DISJ _ (SUBLB _ I1)) as D1. pose proof (DISJ _ (SUBLB _ I2)) as D2. pose proof (DISJ _ (SUBLB _ I3)) as D3. pose proof (DISJ _ (SUBLB _ I4)) as D4.
    pose proof (BLK _ (SUBLB _ I1)) as E1. pose proof (BLK _ (SUBLB _ I2)) as E2. pose proof (BLK _ (SUBLB _ I3)) as E3. pose proof (BLK _ (SUBLB _ I4)) as E4.
    cbn [blk_addr blk_size fst snd] in D1, D2, D3, D4, E1, E2, E3, E4.
    destruct E1 as (_ & _ & _ & E1a & E1b & E1f & E1c). destruct E2 as (_ & _ & _ & E2a & E2b & E2f & E2c).
    destruct E3 as (_ & _ & _ & E3a & E3b & E3f & E3c). destruct E4 as (_ & _ & _ & E4a & E4b & E4f & E4c).
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    assert (L1 : 1 <= mb_len R) by lia. destruct (PAYL L1) as [pD PIN].
    pose proof (DISJ _ (SUBLB _ PIN)) as DP. pose proof (BLK _ (SUBLB _ PIN)) as (_ & _ & _ & EPa & EPb & EPf & EPc). cbn [blk_addr blk_size fst snd] in DP, EPa, EPb, EPf, EPc.
    unfold zlength in DSL.
    assert (PREL : length (firstn (Z.to_nat (512 * k)) ds) = Z.to_nat (512 * k)) by (rewrite length_firstn; lia).
    pose proof PAY as (PYa & PYv & PYi).
    (* [comment removed for export] *)
    assert (OSH : OUT_shad m (A + 512 * k) 512).
    { split; [| split; [| split]].
      - eapply addressable_accessible; [exact AD| lia| lia| pose proof (aapp_bounds _ _ G13 ltac:(lia)) as (_ & _ & K3 & _); lia].
      - eapply shvis_sub; [exact SV| lia| lia| lia| lia| lia].
      - eapply aapp_in_app_mem; [exact G13| lia| lia].
      - eapply aconst_ok_aapp; [exact G13| lia| lia]. }
    assert (RSH : RB_shad m RBP).
    { split; [| split].
      - eapply acc8_of_C1; [exact SHB| cbv delta [RBP]; lia| cbv delta [RBP]; destruct FFR as (_ & _ & M32); clear - M32; Z.div_mod_to_equations; lia|].
        cbv delta [RBP]. pose proof (aapp_bounds _ _ G9 ltac:(unfold AFS_SIZE; lia)) as (_ & _ & K3 & _). unfold AFS_SIZE in *. lia.
      - eapply aapp_in_app_mem; [exact G9| cbv delta [RBP]; lia| cbv delta [RBP]; lia].
      - eapply aconst_ok_aapp; [exact G9| cbv delta [RBP]; lia| cbv delta [RBP]; lia]. }
    assert (MO1 : memrd_out mb R' (A + 512 * k) 512 lo S1).
    { unfold memrd_out. rewrite (mb_static_blocks mb R R' MST), Q1, Q2. unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      split; [left; clear - G12 G1 KR; lia|]. split; [clear - G10 KR; lia|]. split; [clear - G12 G15 KR; lia|].
      split; [apply Forall_cons; [cbn; clear - D1 KR; lia|]; apply Forall_cons; [cbn; clear - D2 KR; lia|];
             apply Forall_cons; [cbn; clear - D3 KR; lia|]; apply Forall_cons; [cbn; clear - D4 KR; lia|]; apply Forall_nil|].
      split; [clear - DP KR; lia| unfold A_mem_buf_method, O_METH_BREAD; clear - G11 KR; unfold AIMG_TOP in *; lia]. }
    assert (MO2 : memrd_out mb R' RBP 8 lo S1).
    { unfold memrd_out. cbv delta [RBP]. rewrite (mb_static_blocks mb R R' MST), Q1, Q2. unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      unfold AFS_HDR, AFS_SIZE in *.
      split; [left; clear - G7 G8 G1; lia|]. split; [clear - G5 G6; unfold AIMG_TOP in *; lia|]. split; [clear - G7 G8 G15; lia|].
      cbn [blk_addr blk_size fst snd] in E1f, E2f, E3f, E4f.
      split; [apply Forall_cons; [cbn; clear - E1f G6 G7; lia|]; apply Forall_cons; [cbn; clear - E2f G6 G7; lia|];
             apply Forall_cons; [cbn; clear - E3f G6 G7; lia|]; apply Forall_cons; [cbn; clear - E4f G6 G7; lia|]; apply Forall_nil|].
      split; [clear - EPf G6 G7; lia| unfold A_mem_buf_method, O_METH_BREAD; clear - G5 G6; lia]. }
    pose proof (abioreadex_mem_spec H HH) as RD. unfold bioreadex_mem_stmt, readintern_mem_stmt_at in RD.
    unfold lad_entry in VIS.
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| |].
    { eapply RD with (lo := lo) (LB := LB) (a := mb) (out := A + 512 * k) (outl := 512) (rbp := RBP) (rbv := rb) (R := R') (ds := ds) (junk := junk); clear RD;
        try reflexivity.
      all: try first [exact MBO| exact ME| exact JK| exact RB| exact MI| exact CEIL| exact AC| exact OSH| exact RSH].
      all: lazymatch goal with
           | |- 0 < 512 < _ => clear; lia
           | |- MEMBIO_below _ _ _ => eapply mb_static_below; [exact MST| exact MBB]
           | |- MEMBIO_sep _ _ => eapply mb_static_sep; [exact MST| exact MBS]
           | |- bytes_at _ _ _ _ => rewrite Q1; exact DS
           | |- Z.of_nat (length ds) = _ => rewrite Q2; exact DSL
           | |- memrd_out _ _ _ 512 _ _ => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); exact MO1
           | |- memrd_out _ _ _ 8 _ _ => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); exact MO2
           | |- _ + 8 <= _ \/ _ => cbv delta [RBP]; clear - G6 G7 G12 G14 KR; destruct G14; [right; lia| left; lia]
           | |- MEMBIO_shad _ _ _ => exact MSH
           | |- PAYLOAD_shad _ _ => eapply mb_static_pay; [exact MST| exact PAY]
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); exact ST
           | |- lo <= _ => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); unf_stk; clear - LOS; lia
           | |- _ mod 2 = 0 => unfold ARP_R3; rewrite unsigned_lit by (clear; lia); reflexivity
           | |- _ mod 8 = 0 => cbv delta [RBP]; destruct FFR as (_ & _ & M32); clear - M32; Z.div_mod_to_equations; lia
           end. }
    intros msF1 mo1 KREL1 MP1 PO. cbn beta in PO. unfold memrd_post in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & junk1 & VIS1 & MU1 & WM1 & MI1 & AC1 & ST1 & MBO1 & DS1 & OUT1 & RBc1).
    rewrite (unsigned_lit S1) in MU1, ST1 by (clear - G0 G1 G2 G3 G4; lia).
    rewrite (mb_static_foot mb R R' MST) in MU1. unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in MU1.
    cbn [mb_buf mb_after_read mb_advance] in DS1. rewrite Q1 in DS1.
    unfold mb_rdn, mb_avail in *. rewrite Q2, POS in *.
    set (n := Z.min 512 (mb_len R - 512 * k)) in *.
    assert (NR : 1 <= n <= 512) by (subst n; lia).
    assert (TKL : length (mb_take R' ds n) = Z.to_nat n).
    { unfold mb_take. rewrite length_firstn, length_skipn, POS. clear - NR KL KR DSL. lia. }
    rewrite TKL in OUT1.
    replace (rd_ok n) with 1 in VIS1 by (unfold rd_ok; replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    (* [comment removed for export] *)
    assert (CW : Forall (aclient_write_ok H ((p, A, 512 * (k + 1)) :: Lh))
                   [(lo, S1); (A + 512 * k, A + 512 * k + 512); (RBP, RBP + 8); (mb, mb + 128); (mb_bm R, mb_bm R + 32)]).
    { apply Forall_cons; [left; cbn; lia|].
      apply Forall_cons; [right; right; left; exists (p, A, 512 * (k + 1)); split; [left; reflexivity| cbn; lia]|].
      apply Forall_cons; [right; right; right; right; left; cbn; cbv delta [RBP]; lia|].
      apply Forall_cons; [right; right; left; exists (mb_id R, mb, 128); split; [right; exact (SUBLB _ I1)| cbn; lia]|].
      apply Forall_cons; [right; right; left; exists (mb_bmid R, mb_bm R, 32); split; [right; exact (SUBLB _ I3)| cbn; lia]| apply Forall_nil]. }
    assert (NSH : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, S1); (A + 512 * k, A + 512 * k + 512); (RBP, RBP + 8); (mb, mb + 128); (mb_bm R, mb_bm R + 32)]).
    { assert (T : forall X n lo' hi', aapp X n -> X <= lo' -> hi' <= X + n -> hi' <= ASHADOW_BASE \/ AHI_LO <= lo').
      { intros X n0 lo' hi' AP L1' L2'. pose proof (aapp_not_shadowland _ _ AP) as NS. clear - NS L1' L2'. unfold ALOWSH_LO, AHI_LO in *. rewrite ASHADOW_BASE_val. lia. }
      apply Forall_cons; [cbn; right; clear - G0 G1; unfold AHI_LO; lia|].
      apply Forall_cons; [cbn; eapply T; [exact G13| clear - KR; lia| clear - KR; lia]|].
      apply Forall_cons; [cbn; eapply T; [exact G9| cbv delta [RBP]; clear - G6 G7; lia| cbv delta [RBP]; clear - G6 G7; lia]|].
      apply Forall_cons; [cbn; eapply T; [exact E1c| clear; lia| clear; lia]|].
      apply Forall_cons; [cbn; eapply T; [exact E3c| clear; lia| clear; lia]| apply Forall_nil]. }
    assert (NSH' : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, S1); (A + 512 * k, A + 512 * k + 512); (RBP, RBP + 8); (mb, mb + 128); (mb_bm R, mb_bm R + 32)]).
    { assert (T : forall X n lo' hi', aapp X n -> X <= lo' -> hi' <= X + n -> hi' <= ALOWSH_LO \/ AHI_LO <= lo').
      { intros X n0 lo' hi' AP L1' L2'. pose proof (aapp_not_shadowland _ _ AP) as NS. clear - NS L1' L2'. lia. }
      apply Forall_cons; [cbn; right; clear - G0 G1; unfold AHI_LO; lia|].
      apply Forall_cons; [cbn; eapply T; [exact G13| clear - KR; lia| clear - KR; lia]|].
      apply Forall_cons; [cbn; eapply T; [exact G9| cbv delta [RBP]; clear - G6 G7; lia| cbv delta [RBP]; clear - G6 G7; lia]|].
      apply Forall_cons; [cbn; eapply T; [exact E1c| clear; lia| clear; lia]|].
      apply Forall_cons; [cbn; eapply T; [exact E3c| clear; lia| clear; lia]| apply Forall_nil]. }
    (* [comment removed for export] *)
    assert (HP1 : as_RHEAP H s ((p, A, 512 * (k + 1)) :: Lh) m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AW : Forall (afs_write_ok H LFx) [(lo, S1); (A + 512 * k, A + 512 * k + 512); (RBP, RBP + 8); (mb, mb + 128); (mb_bm R, mb_bm R + 32)]).
    { pose proof E1a as Y1. pose proof E1f as Y2. pose proof E3a as Y3. pose proof E3f as Y4. unfold AIMG_TOP, AFS_SIZE in Y1, Y2, Y3, Y4.
      unfold afs_write_ok, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE.
      apply Forall_cons; [left; cbn; clear - G0 G1 G8; lia|].
      apply Forall_cons; [left; cbn; clear - G11 G14 KR; lia|].
      apply Forall_cons; [right; exists (6, ff, fpx); split; [exact FFL| cbv delta [RBP]; unfold fsz; cbn; clear; lia]|].
      apply Forall_cons; [left; cbn; clear - Y1 Y2; lia|].
      apply Forall_cons; [left; cbn; clear - Y3 Y4; lia| apply Forall_nil]. }
    assert (RF1 : as_RFS H LFx m1) by (eapply (ah_RFS_frame H HH); [exact RF| exact MU1| exact WM1| exact AW]).
    assert (PRE1 : rw_cells asegs m1 A [CB (Z.to_nat (512 * k)) (firstn (Z.to_nat (512 * k)) ds)]).
    { eapply rw_cells_transport; [exact PRE| exact MU1| exact WM1|]. cbv delta [RBP]. clear - G1 G2 G6 G7 G12 G14 KR D1 D3. cbn -[Z.add Z.mul Z.sub Z.opp Z.to_nat Z.of_nat]. lia. }
    assert (IMG : forall A0 cs, rw_cells asegs m A0 cs -> A0 + Z.of_nat (cells_size cs) <= AIMG_TOP -> 0 <= A0 -> rw_cells asegs m1 A0 cs).
    { intros A0 cs RC HI H0. eapply rw_cells_transport; [exact RC| exact MU1| exact WM1|].
      cbv delta [RBP]. unfold AIMG_TOP in HI, E1a, E3a. clear - HI H0 G0 G1 G2 G5 G6 G11 E1a E3a KR. cbn -[Z.add Z.mul Z.sub Z.opp]. lia. }
    assert (ERR1 : rw_cells asegs m1 (errno_addr (Z_to_bv 64 ATP)) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbv delta [RBP].
      unfold AIMG_TOP in E1a, E3a. clear - ERNG G0 G1 G2 G5 G6 G11 E1a E3a KR. cbn -[Z.add Z.mul Z.sub Z.opp errno_addr]. lia. }
    assert (ME1 : METH_mem m1) by (unfold METH_mem in *; apply IMG; [exact ME| unfold A_mem_buf_method, O_METH_BREAD, AIMG_TOP; cbn; lia| unfold A_mem_buf_method, O_METH_BREAD; lia]).
    assert (IM1 : IMPL_mem m1).
    { unfold IMPL_mem in *. destruct IM as (J1 & J2 & J3).
      split; [| split]; (apply IMG; [eassumption| unfold A_malloc_impl, A_realloc_impl, A_free_impl, AIMG_TOP; cbn; lia| unfold A_malloc_impl, A_realloc_impl, A_free_impl; lia]). }
    assert (GM1 : GOT_mem m1) by (unfold GOT_mem in *; apply IMG; [exact GM| unfold A_got_CRYPTO_malloc, AIMG_TOP; cbn; lia| unfold A_got_CRYPTO_malloc; lia]).
    assert (XP1 : xpres H Lh S1 XW m0 m1).
    { eapply xpres_trans; [exact XP|].
      eapply (xpres_of_munch_fresh H HH s _ m m m1); [exact HP| lia| exact MU1| exact WM1|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; lia|].
      apply Forall_cons; [right; right; intros a Ha; cbn in Ha; unfold XW; cbn [rin_ivs fst snd]; left; lia|].
      apply Forall_cons; [right; right; intros a Ha; cbn in Ha; unfold XW, MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE; cbn [rin_ivs fst snd]; right; right; left; lia|].
      apply Forall_cons; [right; right; intros a Ha; cbn in Ha; unfold XW, MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE; cbn [rin_ivs fst snd]; right; right; right; left; lia| apply Forall_nil]. }
    assert (AD1 : addressable m1 A (512 * (k + 1))) by (eapply addressable_across2; [exact AD| exact G13| exact MU1| exact WM1| exact NSH]).
    assert (MSH1 : MEMBIO_shad m1 mb (mb_after_read R' n)).
    { destruct MSH as (X1 & X2 & X3 & X4). unfold MEMBIO_shad. cbn [mb_bb mb_bm mb_rp mb_after_read mb_advance]. rewrite Q3, Q4, Q5 in *.
      split; [| split; [| split]]; (eapply addressable_across2; [eassumption| eassumption| exact MU1| exact WM1| exact NSH]). }
    assert (PAY1 : PAYLOAD_shad m1 R).
    { split; [| split; [| exact PYi]].
      - eapply accessible_across; [exact PYa| exact MU1| exact NSH'].
      - pose proof (aapp_bounds _ _ EPc ltac:(clear - L1; lia)) as (_ & _ & K3 & K4 & _).
        eapply shvis_across2; [exact PYv| exact MU1| exact WM1| clear - K4; lia| clear - K3 L1; lia| exact NSH]. }
    assert (SHB1 : rw_cells asegs m1 (sh RBP) [C1 (b8 0)]).
    { eapply rw_cells_transport; [exact SHB| exact MU1| exact WM1|]. cbn [cells_size csize Nat.add length disjoint_from].
      pose proof (sh_aapp_range _ _ G9 ltac:(clear; lia)) as (W1 & W2 & W3).
      assert (SR : sh (as_FSB H) <= sh (ff + 2256) /\ sh (ff + 2256) + 1 <= sh (as_FSB H) + nsh 11571200).
      { unfold sh, nsh. clear - G6 G7. Z.div_mod_to_equations. lia. }
      pose proof (aapp_not_shadowland _ _ G13) as N1. pose proof (aapp_not_shadowland _ _ G9) as N2.
      pose proof (aapp_not_shadowland _ _ E1c) as N3. pose proof (aapp_not_shadowland _ _ E3c) as N4.
      assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
      cbv delta [RBP]. unfold ALOWSH_LO, AHI_LO, AIMG_TOP in *.
      clear - SR W1 W2 W3 G0 G1 G2 G5 G6 G7 KR N1 N2 N3 N4 S0. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. repeat split; lia. }
    assert (CHN1 : as_chain H m1 (bv_unsigned esp) CHrp).
    { eapply (achain_below H HH m m1 _ _ _ (S1 + 16)); [exact CHN| | exact MU1|].
      - intros fp' ra' [E|Hin]; [injection E as <- <-; lia| pose proof (CHB _ _ Hin); lia].
      - cbv delta [RBP] in *. clear - G1 G2 G7 G8 G12 E1b E3b KR. repeat (apply Forall_cons; [left; cbn; lia|]). apply Forall_nil. }
    assert (SF1 : rw_cells asegs m1 (S1 + 168) [C8 (wz ARP_FILE)]).
    { eapply rw_cells_transport; [exact SF| exact MU1| exact WM1|]. cbv delta [RBP]. clear - G1 G2 G7 G8 G12 E1b E3b KR. cbn -[Z.add Z.mul Z.sub Z.opp]. lia. }
    assert (SA1 : rw_cells asegs m1 (S1 + 184) [C8 (wz A)]).
    { eapply rw_cells_transport; [exact SA| exact MU1| exact WM1|]. cbv delta [RBP]. clear - G1 G2 G7 G8 G12 E1b E3b KR. cbn -[Z.add Z.mul Z.sub Z.opp]. lia. }
    clear MU1 WM1 HP AUX PRE ERR ME IM GM MI ST XP MBO JK RB DS AC AD MSH PAY SHB CHN CW NSH NSH' IMG AW RF.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 ARP_R3)) with (Z_to_bv 64 ARP_R3) in VIS1 by (symmetry; apply ret_pc_even; [unfold ARP_R3; lia| reflexivity]).
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply ald_seg1; [reflexivity| exact MI1]|]. intros msF2 mo2 KREL2 MP2 VIS2. cbn beta in VIS2.
    (* [comment removed for export] *)
    pose proof (mb_static_read R R' n MST) as MST1.
    pose proof (abioeof_mem_spec H) as EF. unfold bioeof_mem_stmt in EF.
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| |].
    { eapply EF with (lo := lo) (LB := LB) (a := mb) (R := mb_after_read R' n); clear EF; try reflexivity.
      all: try first [exact MBO1| exact ME1| exact MI1| exact CEIL| exact AC1| exact MSH1].
      all: lazymatch goal with
           | |- MEMBIO_below _ _ _ => eapply mb_static_below; [exact MST1| exact MBB]
           | |- MEMBIO_sep _ _ => eapply mb_static_sep; [exact MST1| exact MBS]
           | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact ST1
           | |- lo <= _ => rewrite unsigned_lit by lia; unf_stk; clear - LOS; lia
           | |- _ mod 2 = 0 => unfold ALD_R1; rewrite unsigned_lit by lia; reflexivity
           end. }
    intros msF3 mo3 KREL3 MP3 PO. cbn beta in PO. unfold memctrl_post in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & VIS3 & MU2 & WM2 & MI2 & AC2 & ST2 & MBO2).
    rewrite (unsigned_lit S1) in MU2, ST2 by lia.
    assert (NSH2 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, S1)]) by (apply Forall_cons; [cbn; right; unfold AHI_LO; lia| apply Forall_nil]).
    assert (CW2 : Forall (aclient_write_ok H ((p, A, 512 * (k + 1)) :: Lh)) [(lo, S1)]) by (apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
    assert (AW2 : Forall (afs_write_ok H LFx) [(lo, S1)]) by (apply Forall_cons; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE; clear - G0 G1 G8; lia| apply Forall_nil]).
    (* [comment removed for export] *)
    eapply (KONT m2 msF3 mo3 (mb_after_read R' n) n junk1); clear KONT.
    - reflexivity.
    - reflexivity.
    - exact VIS3.
    - exact KREL3.
    - eapply (ah_mpres_trans H HH); [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]| exact MP3].
    - eapply (ah_RHEAP_frame H HH); [exact HP1| exact MU2| exact WM2| exact CW2].
    - exact MBO2.
    - eapply bytes_at_transport; [exact DS1| exact MU2|]. rewrite DSL. clear - EPb CEIL. cbn -[Z.add Z.mul Z.sub Z.opp]. lia.
    - eapply rw_cells_transport; [exact PRE1| exact MU2| exact WM2|]. clear - G12 CEIL KR; cbn -[Z.add Z.mul Z.sub Z.opp Z.to_nat Z.of_nat]; lia.
    - eapply rw_cells_transport; [exact OUT1| exact MU2| exact WM2|]. clear - G12 CEIL KR NR; cbn -[Z.add Z.mul Z.sub Z.opp]. lia.
    - eapply rw_cells_transport; [exact RBc1| exact MU2| exact WM2|]. cbv delta [RBP] in *. clear - G7 G8 G1; cbn -[Z.add Z.mul Z.sub Z.opp]; lia.
    - exists errv. eapply rw_cells_transport; [exact ERR1| exact MU2| exact WM2|]. clear - ERNG CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp errno_addr]; lia.
    - unfold METH_mem in *; eapply rw_cells_transport; [exact ME1| exact MU2| exact WM2| unfold A_mem_buf_method, O_METH_BREAD; clear - CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp]; lia].
    - unfold IMPL_mem in *. destruct IM1 as (J1 & J2 & J3).
      split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU2| exact WM2| unfold A_malloc_impl, A_realloc_impl, A_free_impl; clear - CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp]; lia]).
    - unfold GOT_mem in *; eapply rw_cells_transport; [exact GM1| exact MU2| exact WM2| unfold A_got_CRYPTO_malloc; clear - CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp]; lia].
    - exact MI2.
    - exact ST2.
    - eapply (ah_rauxv_frame H HH); [exact AUX1| exact MU2| exact WM2| exact CW2].
    - eapply xpres_trans; [exact XP1|]. eapply (xpres_of_munch_fresh H HH s _ m1 m1 m2); [exact HP1| lia| exact MU2| exact WM2|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil].
    - exact AC2.
    - eapply (ah_RFS_frame H HH); [exact RF1| exact MU2| exact WM2| exact AW2].
    - eapply addressable_across2; [exact AD1| exact G13| exact MU2| exact WM2| exact NSH2].
    - destruct MSH1 as (X1 & X2 & X3 & X4). unfold MEMBIO_shad in *. cbn [mb_bb mb_bm mb_rp mb_after_read mb_advance] in *. rewrite ?Q3, ?Q4, ?Q5 in *.
      split; [| split; [| split]]; (eapply addressable_across2; [eassumption| eassumption| exact MU2| exact WM2| exact NSH2]).
    - destruct PAY1 as (Y1 & Y2 & Y3). split; [| split; [| exact Y3]].
      + eapply accessible_across; [exact Y1| exact MU2|]. apply Forall_cons; [cbn; right; unfold AHI_LO; lia| apply Forall_nil].
      + pose proof (aapp_bounds _ _ EPc ltac:(clear - L1; lia)) as (_ & _ & K3 & K4 & _).
        eapply shvis_across2; [exact Y2| exact MU2| exact WM2| clear - K4; lia| clear - K3 L1; lia| exact NSH2].
    - eapply rw_cells_transport; [exact SHB1| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add length disjoint_from].
      pose proof (sh_aapp_range _ _ G9 ltac:(clear; lia)) as (W1 & W2 & W3).
      assert (SR : sh (as_FSB H) <= sh (ff + 2256) /\ sh (ff + 2256) + 1 <= sh (as_FSB H) + nsh 11571200).
      { unfold sh, nsh. clear - G6 G7. Z.div_mod_to_equations. lia. }
      cbv delta [RBP]. unfold AHI_LO in *. clear - SR W1 W2 W3 G0 G1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. split; [| exact I]. lia.
    - eapply (achain_below H HH m1 m2 _ _ _ (S1 + 16)); [exact CHN1| | exact MU2|].
      + intros fp' ra' [E|Hin]; [injection E as <- <-; lia| pose proof (CHB _ _ Hin); lia].
      + apply Forall_cons; [left; cbn; lia| apply Forall_nil].
    - exact ALB.
    - eapply rw_cells_transport; [exact SF1| exact MU2| exact WM2|]. clear - G2; cbn -[Z.add Z.mul Z.sub Z.opp]; lia.
    - eapply rw_cells_transport; [exact SA1| exact MU2| exact WM2|]. clear - G2; cbn -[Z.add Z.mul Z.sub Z.opp]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lad_done : forall k m2 msF mo s p A R' (n : Z) (junk' : list byte) (s4v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (Q : config -> Prop),
    0 <= k <= 31 -> n = mb_len R - 512 * k -> 1 <= n <= 512 ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 ALD_R1) (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) u0 u1 u2 esp (Z_to_bv 64 S1)
                             (Z_to_bv 64 (mem_ctrl_rv (mb_after_read R' n) BIO_CTRL_EOF)) b1 b2 b3 b4 b5 b6 b7
                             (Z_to_bv 64 512) s3v (Z_to_bv 64 A) (Z_to_bv 64 (- (512 * k))) (Z_to_bv 64 mb) (Z_to_bv 64 (A + 512 * k)) (Z_to_bv 64 (32 - k))
                             (Z_to_bv 64 RBP) s4v (Z_to_bv 64 (512 * k)) u3 u4 u5 u6)
                        F (ret_pc (Z_to_bv 64 ALD_R1)) fc None m2 (seg_rom asegs) ->
    as_RHEAP H s ((p, A, 512 * (k + 1)) :: Lh) m2 -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    MEMBIO H LB m2 mb (mb_after_read R' n) -> mb_static R R' -> mb_pos R' = 512 * k ->
    bytes_at asegs m2 (mb_buf R) ds -> rw_cells asegs m2 A [CB (Z.to_nat (512 * k)) (firstn (Z.to_nat (512 * k)) ds)] ->
    rw_cells asegs m2 (A + 512 * k) [CB (Z.to_nat n) (mb_take R' ds n); CB (Z.to_nat 512 - Z.to_nat n) junk'] ->
    rw_cells asegs m2 RBP [C8 (wz n)] -> (exists errv, rw_cells asegs m2 (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    METH_mem m2 -> IMPL_mem m2 -> GOT_mem m2 -> mem_inv asegs m2 -> stk asegs m2 lo S1 -> as_rauxv_ok H m2 B ->
    xpres H Lh S1 XW m0 m2 ->
    ACONST m2 -> as_RFS H LFx m2 -> addressable m2 A (512 * (k + 1)) -> MEMBIO_shad m2 mb (mb_after_read R' n) -> PAYLOAD_shad m2 R -> rw_cells asegs m2 (sh RBP) [C1 (b8 0)] ->
    as_chain H m2 (bv_unsigned esp) CHrp -> as_AL H s + as_Cm H (lad_cm k) + as_Cf H (lad_cf k) >= AL0 ->
    rw_cells asegs m2 (S1 + 168) [C8 (wz ARP_FILE)] -> rw_cells asegs m2 (S1 + 184) [C8 (wz A)] ->
    lad_doneK Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros k m2 msF mo s p A R' n junk' s4v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Q KR NEQ NR VIS HP KREL MP MBO MST POS DS PRE OUT RBc [errv ERR] ME IM GM MI ST AUX XP
           AC RF AD MSH PAY SHB CHN ALB SF SA KD.
    pose proof (lad_geo _ _ _ _ _ HP) as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
    unfold AIMG_TOP, AFS_HDR, AFS_SIZE in G5, G6, G7, G8, G9, G11, G14.
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
    pose proof LO as LOS. unf_stk_in LOS.
    destruct (lad_head_facts _ _ _ _ _ HP) as (BR & NIP & DISJ & BLK & SV).
    pose proof MST as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
    pose proof (mb_static_read R R' n MST) as MST1.
    pose proof MBO as MB0. destruct MB0 as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _).
    cbn [mb_id mb_bbid mb_bmid mb_rpid mb_bb mb_bm mb_rp mb_after_read mb_advance] in I1, I2, I3, I4.
    rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I1. rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I3.
    pose proof (BLK _ (SUBLB _ I1)) as (_ & _ & _ & E1a & E1b & E1f & E1c). pose proof (BLK _ (SUBLB _ I3)) as (_ & _ & _ & E3a & E3b & E3f & E3c).
    cbn [blk_addr blk_size fst snd] in E1a, E1b, E1f, E1c, E3a, E3b, E3f, E3c.
    assert (L1 : 1 <= mb_len R) by lia. destruct (PAYL L1) as [pD PIN].
    pose proof (BLK _ (SUBLB _ PIN)) as (_ & _ & _ & EPa & EPb & EPf & EPc). cbn [blk_addr blk_size fst snd] in EPa, EPb, EPf, EPc.
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    unfold zlength in DSL.
    assert (PREL : length (firstn (Z.to_nat (512 * k)) ds) = Z.to_nat (512 * k)) by (rewrite length_firstn; clear - KR NEQ NR DSL; lia).
    assert (RV : mem_ctrl_rv (mb_after_read R' n) BIO_CTRL_EOF = 1).
    { unfold mem_ctrl_rv, mb_avail. cbn [mb_len mb_pos mb_after_read mb_advance]. rewrite Q2, POS.
      replace (mb_len R - (512 * k + n) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    rewrite RV in VIS.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 ALD_R1)) with (Z_to_bv 64 ALD_R1) in VIS by (symmetry; apply ret_pc_even; [unfold ALD_R1; lia| reflexivity]).
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply ald_seg2_eof; [reflexivity| clear; lia| exact MI]|]. intros msF3 mo3 KREL3 MP3 VIS3. cbn beta in VIS3.
    (* [comment removed for export] *)
    pose proof (abioeof_mem_spec H) as EF. unfold bioeof_mem_stmt in EF.
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| |].
    { eapply EF with (lo := lo) (LB := LB) (a := mb) (R := mb_after_read R' n); clear EF; try reflexivity.
      all: try first [exact MBO| exact ME| exact MI| exact CEIL| exact AC| exact MSH].
      all: lazymatch goal with
           | |- MEMBIO_below _ _ _ => eapply mb_static_below; [exact MST1| exact MBB]
           | |- MEMBIO_sep _ _ => eapply mb_static_sep; [exact MST1| exact MBS]
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); exact ST
           | |- lo <= _ => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); unf_stk; clear - LOS; lia
           | |- _ mod 2 = 0 => unfold ALD_RD; rewrite unsigned_lit by (clear; lia); reflexivity
           end. }
    intros msF4 mo4 KREL4 MP4 PO. cbn beta in PO. unfold memctrl_post in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & VIS4 & MU3 & WM3 & MI3 & AC3 & ST3 & MBO3).
    rewrite (unsigned_lit S1) in MU3, ST3 by (clear - G0 G1 G2 G3 G4; lia). rewrite RV in VIS4.
    assert (NSH3 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, S1)]) by (apply Forall_cons; [cbn; right; clear - G0 G1; unfold AHI_LO; lia| apply Forall_nil]).
    assert (CW3 : Forall (aclient_write_ok H ((p, A, 512 * (k + 1)) :: Lh)) [(lo, S1)]) by (apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
    assert (AW3 : Forall (afs_write_ok H LFx) [(lo, S1)]) by (apply Forall_cons; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE; clear - G0 G1 G8; lia| apply Forall_nil]).
    (* [comment removed for export] *)
    apply (rw_cells_transport asegs _ m2 m3 _ _ OUT) in MU3 as OUT3; [| exact WM3| clear - G12 CEIL KR NR; cbn -[Z.add Z.mul Z.sub Z.opp]; lia].
    apply (rw_cells_transport asegs _ m2 m3 _ _ PRE) in MU3 as PRE3; [| exact WM3| clear - G12 CEIL KR; cbn -[Z.add Z.mul Z.sub Z.opp Z.to_nat Z.of_nat]; lia].
    assert (W3 : rw_cells asegs m3 A ([CB (Z.to_nat (512 * k)) (firstn (Z.to_nat (512 * k)) ds)] ++ [CB (Z.to_nat n) (mb_take R' ds n); CB (Z.to_nat 512 - Z.to_nat n) junk'])).
    { apply (proj2 (rw_cells_app asegs m3 A _ _)). split; [exact PRE3|]. cbn [cells_size csize Nat.add].
      replace (A + Z.of_nat (Z.to_nat (512 * k) + 0)) with (A + 512 * k) by (clear - KR; lia). exact OUT3. }
    cbn [app] in W3.
    apply (proj1 (rw_cells_app asegs m3 _ [CB (Z.to_nat (512 * k)) (firstn (Z.to_nat (512 * k)) ds); CB (Z.to_nat n) (mb_take R' ds n)] [CB (Z.to_nat 512 - Z.to_nat n) junk'])) in W3.
    destruct W3 as [W12 JK3]. cbn [cells_size csize Nat.add] in JK3.
    apply (proj1 (rw_cells_app asegs m3 _ [CB (Z.to_nat (512 * k)) (firstn (Z.to_nat (512 * k)) ds)] [CB (Z.to_nat n) (mb_take R' ds n)])) in W12.
    destruct W12 as [P3 D3]. cbn [cells_size csize Nat.add] in D3. rewrite Nat.add_0_r in D3.
    pose proof (rw_cells_CB_join asegs m3 A _ _ _ _ P3 D3) as ALLW.
    unfold mb_take in ALLW. rewrite POS, firstn_app_skipn in ALLW.
    replace (Z.to_nat (512 * k) + Z.to_nat n)%nat with (length ds) in ALLW by (clear - KR NR NEQ DSL; lia).
    rewrite firstn_all in ALLW. replace (length ds) with (Z.to_nat (mb_len R)) in ALLW by (clear - DSL; lia).
    assert (ALL : bytes_at asegs m3 A ds).
    { pose proof (rw_cells_bytes_at asegs m3 A _ ALLW) as J. cbn [cells_bytes cbytes app] in J. rewrite app_nil_r in J. exact J. }
    assert (RWALL : rw_cells asegs m3 A [CB (Z.to_nat (mb_len R)) ds; CB (Z.to_nat (512 * (k + 1) - mb_len R)) junk']).
    { apply (proj2 (rw_cells_app asegs m3 A [CB (Z.to_nat (mb_len R)) ds] [CB (Z.to_nat (512 * (k + 1) - mb_len R)) junk'])).
      split; [exact ALLW|]. cbn [cells_size csize Nat.add].
      replace (A + Z.of_nat (Z.to_nat (mb_len R) + 0)) with (A + Z.of_nat (Z.to_nat (512 * k) + (Z.to_nat n + 0))) by (clear - NEQ NR KR; lia).
      replace (Z.to_nat (512 * (k + 1) - mb_len R)) with (Z.to_nat 512 - Z.to_nat n)%nat by (clear - NEQ NR KR; lia). exact JK3. }
    unfold lad_doneK in KD.
    eapply (KD k n m3 msF4 mo4 s p A (mb_after_read R' n) junk'); clear KD.
    all: try first [exact KR| exact NEQ| exact NR| exact VIS4| exact KREL4| exact MBO3| exact MST1| exact ALL| exact RWALL| exact MI3| exact ST3| exact AC3
                    | eapply (ah_RFS_frame H HH); [exact RF| exact MU3| exact WM3| exact AW3]].
    - eapply (ah_RHEAP_frame H HH); [exact HP| exact MU3| exact WM3| exact CW3].
    - eapply (ah_mpres_trans H HH); [eapply (ah_mpres_trans H HH); [exact MP| exact MP3]| exact MP4].
    - cbn [mb_pos mb_after_read mb_advance]. rewrite POS. clear - NEQ; lia.
    - eapply bytes_at_transport; [exact DS| exact MU3|]. rewrite DSL. clear - EPb CEIL; cbn -[Z.add Z.mul Z.sub Z.opp]; lia.
    - eapply rw_cells_transport; [exact RBc| exact MU3| exact WM3|]. cbv delta [RBP]. clear - G6 G7 G8 G1; cbn -[Z.add Z.mul Z.sub Z.opp]; lia.
    - exists errv. eapply rw_cells_transport; [exact ERR| exact MU3| exact WM3|]. clear - ERNG CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp errno_addr]; lia.
    - unfold METH_mem in *; eapply rw_cells_transport; [exact ME| exact MU3| exact WM3| unfold A_mem_buf_method, O_METH_BREAD; clear - CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp]; lia].
    - unfold IMPL_mem in *. destruct IM as (J1 & J2 & J3).
      split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU3| exact WM3| unfold A_malloc_impl, A_realloc_impl, A_free_impl; clear - CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp]; lia]).
    - unfold GOT_mem in *; eapply rw_cells_transport; [exact GM| exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; clear - CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp]; lia].
    - eapply (ah_rauxv_frame H HH); [exact AUX| exact MU3| exact WM3| exact CW3].
    - eapply xpres_trans; [exact XP|]. eapply (xpres_of_munch_fresh H HH s _ m2 m2 m3); [exact HP| lia| exact MU3| exact WM3|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil].
    - eapply addressable_across2; [exact AD| exact G13| exact MU3| exact WM3| exact NSH3].
    - unfold MEMBIO_shad in MSH |- *. cbn [mb_bb mb_bm mb_rp mb_after_read mb_advance] in MSH |- *. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      destruct MSH as (X1 & X2 & X3 & X4).
      pose proof (BLK _ (SUBLB _ I2)) as (_ & _ & _ & _ & _ & _ & E2c). pose proof (BLK _ (SUBLB _ I4)) as (_ & _ & _ & _ & _ & _ & E4c).
      cbn [blk_addr blk_size fst snd] in E2c, E4c. rewrite ?Q3, ?Q4, ?Q5 in X2. rewrite ?Q3, ?Q4, ?Q5 in X3. rewrite ?Q3, ?Q4, ?Q5 in X4.
      rewrite ?Q3, ?Q4, ?Q5 in E2c. rewrite ?Q3, ?Q4, ?Q5 in E4c. rewrite ?Q3, ?Q4, ?Q5.
      split; [| split; [| split]]; (eapply addressable_across2; [eassumption| eassumption| exact MU3| exact WM3| exact NSH3]).
    - destruct PAY as (Y1 & Y2 & Y3). split; [| split; [| exact Y3]].
      + eapply accessible_across; [exact Y1| exact MU3|]. apply Forall_cons; [cbn; right; clear - G0 G1; unfold AHI_LO; lia| apply Forall_nil].
      + pose proof (aapp_bounds _ _ EPc ltac:(clear - L1; lia)) as (_ & _ & K3 & K4 & _).
        eapply shvis_across2; [exact Y2| exact MU3| exact WM3| clear - K4; lia| clear - K3 L1; lia| exact NSH3].
    - eapply rw_cells_transport; [exact SHB| exact MU3| exact WM3|]. cbn [cells_size csize Nat.add length disjoint_from].
      pose proof (sh_aapp_range _ _ G9 ltac:(clear; lia)) as (W1 & W2 & W3).
      assert (SR : sh (as_FSB H) <= sh (ff + 2256) /\ sh (ff + 2256) + 1 <= sh (as_FSB H) + nsh 11571200).
      { unfold sh, nsh. clear - G6 G7. Z.div_mod_to_equations. lia. }
      cbv delta [RBP]. unfold AHI_LO in *. clear - SR W1 W2 W3 G0 G1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. split; [| exact I]. lia.
    - eapply (achain_below H HH m2 m3 _ _ _ (S1 + 16)); [exact CHN| | exact MU3|].
      + intros fp' ra' [E|Hin]; [injection E as <- <-; lia| pose proof (CHB _ _ Hin); lia].
      + apply Forall_cons; [left; cbn; lia| apply Forall_nil].
    - pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & _).
      assert (M1 : as_Cm H (lad_cm k) <= as_Cm H (lad_cm 32)) by (apply CMM; unfold lad_cm; clear - KR; nia).
      assert (M2 : as_Cf H (lad_cf k) <= as_Cf H (lad_cf 32)) by (apply CFM; unfold lad_cf; clear - KR; nia).
      clear - ALB M1 M2. lia.
    - eapply rw_cells_transport; [exact SF| exact MU3| exact WM3|]. clear - G2; cbn -[Z.add Z.mul Z.sub Z.opp]; lia.
    - eapply rw_cells_transport; [exact SA| exact MU3| exact WM3|]. clear - G2; cbn -[Z.add Z.mul Z.sub Z.opp]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lad_chain_xpres : forall LBx SP m m' cur CH,
    as_chain H m cur CH -> xpres H LBx SP [] m m' -> (forall fp ra, In (fp, ra) CH -> SP + 16 <= fp) -> as_chain H m' cur CH.
  Proof.
    intros LBx SP m m' cur CH C XP HS. eapply (ah_chain_ext H HH); [exact C|].
    intros fp ra a IN Ha. pose proof (HS _ _ IN). pose proof (ah_chain_range H HH _ _ _ _ _ C IN) as (R1 & R2 & R3). acb.
    apply XP; [lia|]. split; [left; lia|]. intros K. exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma lad_MEMBIO_xpres : forall SP m m' Rm, MEMBIO H LB m mb Rm -> xpres H Lh SP [] m m' -> MEMBIO H LB m' mb Rm.
  Proof.
    intros SP m m' Rm MB XP. destruct MB as (X1 & X2 & X3 & X4 & I1 & I2 & I3 & I4 & REST).
    split; [| split; [| split; [| split; [| exact (conj I1 (conj I2 (conj I3 (conj I4 REST))))]]]].
    all: eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP); [eassumption| | apply Forall_nil].
    all: right; right; left; cbn [cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ].
    - exists (mb_id Rm, mb, BIO_SIZE). split; [exact (SUBLB _ I1)| cbn [blk_addr blk_size fst snd]; unfold BIO_SIZE; lia].
    - exists (mb_bbid Rm, mb_bb Rm, BIOBUFMEM_SIZE). split; [exact (SUBLB _ I2)| cbn [blk_addr blk_size fst snd]; unfold BIOBUFMEM_SIZE; lia].
    - exists (mb_bmid Rm, mb_bm Rm, BUFMEM_SIZE). split; [exact (SUBLB _ I3)| cbn [blk_addr blk_size fst snd]; unfold BUFMEM_SIZE; lia].
    - exists (mb_rpid Rm, mb_rp Rm, BUFMEM_SIZE). split; [exact (SUBLB _ I4)| cbn [blk_addr blk_size fst snd]; unfold BUFMEM_SIZE; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma lad_grow : forall k m2 msF mo s p A R' (n : Z) (junk' : list byte) (s4v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (Q : config -> Prop),
    0 <= k <= 31 -> n = 512 -> 512 * k + 512 < mb_len R ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 ALD_R1) (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) u0 u1 u2 esp (Z_to_bv 64 S1)
                             (Z_to_bv 64 (mem_ctrl_rv (mb_after_read R' n) BIO_CTRL_EOF)) b1 b2 b3 b4 b5 b6 b7
                             (Z_to_bv 64 512) s3v (Z_to_bv 64 A) (Z_to_bv 64 (- (512 * k))) (Z_to_bv 64 mb) (Z_to_bv 64 (A + 512 * k)) (Z_to_bv 64 (32 - k))
                             (Z_to_bv 64 RBP) s4v (Z_to_bv 64 (512 * k)) u3 u4 u5 u6)
                        F (ret_pc (Z_to_bv 64 ALD_R1)) fc None m2 (seg_rom asegs) ->
    as_RHEAP H s ((p, A, 512 * (k + 1)) :: Lh) m2 -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    MEMBIO H LB m2 mb (mb_after_read R' n) -> mb_static R R' -> mb_pos R' = 512 * k ->
    bytes_at asegs m2 (mb_buf R) ds -> rw_cells asegs m2 A [CB (Z.to_nat (512 * k)) (firstn (Z.to_nat (512 * k)) ds)] ->
    rw_cells asegs m2 (A + 512 * k) [CB (Z.to_nat n) (mb_take R' ds n); CB (Z.to_nat 512 - Z.to_nat n) junk'] ->
    rw_cells asegs m2 RBP [C8 (wz n)] -> (exists errv, rw_cells asegs m2 (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    METH_mem m2 -> IMPL_mem m2 -> GOT_mem m2 -> mem_inv asegs m2 -> stk asegs m2 lo S1 -> as_rauxv_ok H m2 B ->
    xpres H Lh S1 XW m0 m2 ->
    ACONST m2 -> as_RFS H LFx m2 -> addressable m2 A (512 * (k + 1)) -> MEMBIO_shad m2 mb (mb_after_read R' n) -> PAYLOAD_shad m2 R -> rw_cells asegs m2 (sh RBP) [C1 (b8 0)] ->
    as_chain H m2 (bv_unsigned esp) CHrp -> as_AL H s + as_Cm H (lad_cm k) + as_Cf H (lad_cf k) >= AL0 ->
    rw_cells asegs m2 (S1 + 168) [C8 (wz ARP_FILE)] -> rw_cells asegs m2 (S1 + 184) [C8 (wz A)] ->
    (forall m4 msF4 mo4 s4 (p' : bptr) (A' : Z) (v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 : word),
       LAD (k + 1) m4 s4 p' A' (mb_after_read R' n) ->
       as_VIS H s4 msF4 = MS (mkR (Z_to_bv 64 ALD_R3) (Z_to_bv 64 S1) gp (Z_to_bv 64 ATP) v0 v1 v2 esp (Z_to_bv 64 S1) (Z_to_bv 64 0) c1 c2 c3 c4 c5 c6 c7
                                 (Z_to_bv 64 512) s3v (Z_to_bv 64 A') (Z_to_bv 64 (- (512 * k + 512))) (Z_to_bv 64 mb) (Z_to_bv 64 (A' + 512 * k + 512)) (Z_to_bv 64 (32 - k))
                                 (Z_to_bv 64 RBP) (Z_to_bv 64 A) (Z_to_bv 64 (512 * k + 512)) v3 v4 v5 v6)
                             F (ret_pc (Z_to_bv 64 ALD_R3)) fc None m4 (seg_rom asegs) ->
       as_AKREL H s4 (mkCfg msF4 mo4) -> as_MPRES H mo0 mo4 ->
       as_SR H Q (mkCfg msF4 mo4)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros k m2 msF mo s p A R' n junk' s4v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Q KR NEQ KL VIS HP KREL MP MBO MST POS DS PRE OUT RBc [errv ERR] ME IM GM MI ST AUX XP
           AC RF AD MSH PAY SHB CHN ALB SF SA KONT.
    subst n.
    pose proof (lad_geo _ _ _ _ _ HP) as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
    unfold AIMG_TOP, AFS_HDR, AFS_SIZE in G5, G6, G7, G8, G9, G11, G14.
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
    pose proof LO as LOS. unf_stk_in LOS.
    destruct (lad_head_facts _ _ _ _ _ HP) as (BR & NIP & DISJ & BLK & SV).
    pose proof MST as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
    pose proof (mb_static_read R R' 512 MST) as MST1.
    pose proof MBO as MB0. destruct MB0 as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _).
    cbn [mb_id mb_bbid mb_bmid mb_rpid mb_bb mb_bm mb_rp mb_after_read mb_advance] in I1, I2, I3, I4.
    rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I1. rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I2.
    rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I3. rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I4.
    pose proof (BLK _ (SUBLB _ I1)) as (_ & _ & _ & E1a & E1b & E1f & E1c). pose proof (BLK _ (SUBLB _ I2)) as (_ & _ & _ & E2a & E2b & E2f & E2c).
    pose proof (BLK _ (SUBLB _ I3)) as (_ & _ & _ & E3a & E3b & E3f & E3c). pose proof (BLK _ (SUBLB _ I4)) as (_ & _ & _ & E4a & E4b & E4f & E4c).
    cbn [blk_addr blk_size fst snd] in E1a, E1b, E1f, E1c, E2a, E2b, E2f, E2c, E3a, E3b, E3f, E3c, E4a, E4b, E4f, E4c.
    assert (L1 : 1 <= mb_len R) by (clear - KR KL; lia). destruct (PAYL L1) as [pD PIN].
    pose proof (BLK _ (SUBLB _ PIN)) as (_ & _ & _ & EPa & EPb & EPf & EPc). cbn [blk_addr blk_size fst snd] in EPa, EPb, EPf, EPc.
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    unfold zlength in DSL.
    assert (SUBLh : forall b, In b Lh -> In b ((p, A, 512 * (k + 1)) :: Lh)) by (intros b Hb; right; exact Hb).
    (* [comment removed for export] *)
    pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & SAM & SAF).
    assert (XM : as_Cm H (lad_cm k) + as_Cm H ((512 * k + 1024) * 1) <= as_Cm H (lad_cm (k + 1))).
    { replace (lad_cm (k + 1)) with (lad_cm k + (512 * k + 1024) * 1) by (unfold lad_cm; clear - KR; nia).
      apply SAM; [unfold lad_cm; clear - KR; nia| clear - KR; lia]. }
    assert (XF : as_Cf H (lad_cf k) + as_Cf H (512 * (k + 1)) <= as_Cf H (lad_cf (k + 1))).
    { replace (lad_cf (k + 1)) with (lad_cf k + 512 * (k + 1)) by (unfold lad_cf; clear - KR; nia).
      apply SAF; [unfold lad_cf; clear - KR; nia| clear - KR; lia]. }
    assert (YM : as_Cm H (lad_cm (k + 1)) <= as_Cm H (lad_cm 32)) by (apply CMM; unfold lad_cm; clear - KR; nia).
    assert (YF : as_Cf H (lad_cf (k + 1)) <= as_Cf H (lad_cf 32)) by (apply CFM; unfold lad_cf; clear - KR; nia).
    assert (ALLOW : as_Cm H ((512 * k + 1024) * 1) + as_Cf H (512 * (k + 1)) <= as_AL H s) by (clear - ALB BUDA XM XF YM YF; lia).
    clear CM0 CMM CF0 CFM SAM SAF YM YF.
    (* [comment removed for export] *)
    assert (RV : mem_ctrl_rv (mb_after_read R' 512) BIO_CTRL_EOF = 0).
    { unfold mem_ctrl_rv, mb_avail. cbn [mb_len mb_pos mb_after_read mb_advance]. rewrite Q2, POS.
      replace (mb_len R - (512 * k + 512) =? 0) with false by (symmetry; apply Z.eqb_neq; clear - KL; lia). reflexivity. }
    rewrite RV in VIS.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs m2 _ [CB (Z.to_nat 512) (mb_take R' ds 512)] [CB (Z.to_nat 512 - Z.to_nat 512) junk'])) in OUT.
    destruct OUT as [DATA _].
    replace (A + 512 * k) with (A + Z.of_nat (Z.to_nat (512 * k))) in DATA by (clear - KR; lia).
    pose proof (rw_cells_CB_join asegs m2 A _ _ _ _ PRE DATA) as OBS.
    unfold mb_take in OBS. rewrite POS, firstn_app_skipn in OBS.
    replace (Z.to_nat (512 * k) + Z.to_nat 512)%nat with (Z.to_nat (512 * (k + 1))) in OBS by (clear - KR; lia).
    assert (OBSL : length (firstn (Z.to_nat (512 * (k + 1))) ds) = Z.to_nat (512 * (k + 1))) by (rewrite length_firstn; clear - KR KL DSL; lia).
    clear PRE DATA.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 ALD_R1)) with (Z_to_bv 64 ALD_R1) in VIS by (symmetry; apply ret_pc_even; [unfold ALD_R1; lia| reflexivity]).
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply ald_seg2_grow with (K := 512 * k) (A := A);
      [clear - KR; lia| clear - KR; lia| cbv delta [RBP]; clear - G5 G6; lia| cbv delta [RBP]; clear - G7 G8 G15; lia| clear - G0 G1 G2; lia| clear - G3 G4; lia
      | exact RBc| exact SF| exact SA| exact MI]|].
    intros msF3 mo3 KREL3 MP3 VIS3. cbn beta in VIS3.
    (* [comment removed for export] *)
    pose proof (acrealloc_spec H HX) as RA. unfold crealloc_stmt, crealloc_stmt_gen in RA.
    eapply (ah_seq H HH).
    { eapply RA with (lo := lo) (B := B) (LB := (p, A, 512 * (k + 1)) :: Lh) (s := s) (p := p) (A := A) (old := 512 * (k + 1)) (num := 512 * k + 1024) (size := 1)
                     (obs := firstn (Z.to_nat (512 * (k + 1))) ds) (errv := errv) (CH := CHrp); clear RA.
      all: try first [exact VIS3| exact HP| exact KREL3| exact OBS| exact AUX| exact CEIL| exact MI| exact AC| exact CHN| exact AD| exact IM| exact GM| exact ERR| exact ALLOW].
      all: lazymatch goal with
           | |- 1 <= _ <= AREALLOC_MAX => unfold AREALLOC_MAX; clear - KR; lia
           | |- _ <= AREALLOC_MAX => unfold AREALLOC_MAX; clear - KR; lia
           | |- In _ _ => left; reflexivity
           | |- zlength _ = _ => unfold zlength; rewrite OBSL; clear - KR; lia
           | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_cons; cbn [blk_size snd]; clear - BUDB KR; lia
           | |- Z.of_nat (length _) + _ <= _ => cbn [length]; clear - BUDC; lia
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); clear - SPB S1R; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); exact ST
           | |- lo <= _ => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); unf_stk; clear - LOS; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); clear - S1A; Z.div_mod_to_equations; lia
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [E|Hin]; rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia);
                                              [injection E as <- <-; clear - G3; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' G3; lia]
           | |- pf_ok _ _ _ _ => unfold ALD_R2; rewrite unsigned_lit by (clear; lia); exact PFR
           | |- if _ then _ else _ => exact eq_refl
           | |- @eq _ _ _ => reflexivity
           | |- ?G => idtac "LEFT:" G
           end. }
    clear RA. intros [msF4 mo4] PO. unfold crealloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & errv3 & A' & junk3 & p' & s3 &
                    VIS4 & KREL4 & MP4 & MI3 & AC3 & ST3 & ERR3 & AUX3 & XP3 & BR3 & HP3 & NEW3 & AD3 & IM3 & GM3 & AL3).
    rewrite (proj1 (ah_lb_remove H HH)) in XP3, HP3 by exact NIP.
    rewrite (unsigned_lit S1) in ST3, XP3 by (clear - G0 G1 G2 G3 G4; lia).
    assert (ALB3 : as_AL H s3 + as_Cm H (lad_cm (k + 1)) + as_Cf H (lad_cf (k + 1)) >= AL0) by (clear - ALB AL3 XM XF; lia).
    clear AL3 XM XF ALLOW.
    replace ((512 * k + 1024) * 1) with (512 * (k + 1 + 1)) in BR3, HP3, NEW3, AD3 by (clear - KR; lia).
    rewrite Z.min_l in NEW3 by (clear - KR; lia). rewrite firstn_firstn, Nat.min_id in NEW3.
    replace (512 * (k + 1 + 1) - 512 * (k + 1)) with 512 in NEW3 by (clear - KR; lia).
    apply (proj1 (rw_cells_app asegs m3 _ [CB (Z.to_nat (512 * (k + 1))) (firstn (Z.to_nat (512 * (k + 1))) ds)] [CB (Z.to_nat 512) junk3])) in NEW3.
    destruct NEW3 as [PRE3 JK3]. cbn [cells_size csize Nat.add] in JK3.
    replace (A' + Z.of_nat (Z.to_nat (512 * (k + 1)) + 0)) with (A' + 512 * (k + 1)) in JK3 by (clear - KR; lia).
    pose proof BR3 as (N1 & N2 & N3 & N4 & N5 & N6 & N7). unfold AIMG_TOP, AFS_SIZE in N4, N6.
    replace (ret_pc (Z_to_bv 64 ALD_R2)) with (Z_to_bv 64 ALD_R2) in VIS4 by (symmetry; apply ret_pc_even; [unfold ALD_R2; lia| reflexivity]).
    (* [comment removed for export] *)
    assert (MBO3 : MEMBIO H LB m3 mb (mb_after_read R' 512)) by (eapply lad_MEMBIO_xpres; [exact MBO| exact XP3]).
    assert (DS3 : bytes_at asegs m3 (mb_buf R) ds).
    { eapply (xpres_bytes_at' H); [exact XP3| exact DS| | apply Forall_nil].
      right; right; left. exists (pD, mb_buf R, mb_len R). split; [exact (SUBLB _ PIN)| cbn [blk_addr blk_size fst snd]; rewrite DSL; clear; lia]. }
    assert (RBc3 : rw_cells asegs m3 RBP [C8 (wz 512)]).
    { eapply (xpres_rw_cells' H); [exact XP3| exact RBc| | apply Forall_nil].
      right; right; right; right; left. cbv delta [RBP]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unfold AFS_SIZE. clear - G6 G7; lia. }
    assert (SHB3 : rw_cells asegs m3 (sh RBP) [C1 (b8 0)]).
    { eapply (xpres_rw_cells' H); [exact XP3| exact SHB| | apply Forall_nil].
      right; right; right; right; right; left. cbv delta [RBP]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      unfold AFS_SIZE. unfold sh. clear - G6 G7. Z.div_mod_to_equations. lia. }
    assert (ME3 : METH_mem m3).
    { unfold METH_mem in *. eapply (xpres_rw_cells' H); [exact XP3| exact ME| | apply Forall_nil].
      right; left. unfold aimg_client, A_mem_buf_method, O_METH_BREAD. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length]. intros a Ha. clear - Ha. lia. }
    assert (MSH3 : MEMBIO_shad m3 mb (mb_after_read R' 512)).
    { destruct MSH as (X1 & X2 & X3 & X4). unfold MEMBIO_shad in *. cbn [mb_bb mb_bm mb_rp mb_after_read mb_advance] in *. rewrite ?Q3, ?Q4, ?Q5 in *.
      unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
      split; [| split; [| split]].
      - eapply (ashobj_addressable_xpres H HH s _ Lh m2 m3 S1 []); [exact HP| exact SUBLh| clear - G1 G2; lia| left; exists (mb_id R, mb, 128); split; [exact (SUBLB _ I1)| cbn; clear; lia]
                                                | unfold AAPP_HI; clear - E1b G15; lia| exact X1| exact XP3| apply Forall_nil].
      - eapply (ashobj_addressable_xpres H HH s _ Lh m2 m3 S1 []); [exact HP| exact SUBLh| clear - G1 G2; lia| left; exists (mb_bbid R, mb_bb R, 16); split; [exact (SUBLB _ I2)| cbn; clear; lia]
                                                | unfold AAPP_HI; clear - E2b G15; lia| exact X2| exact XP3| apply Forall_nil].
      - eapply (ashobj_addressable_xpres H HH s _ Lh m2 m3 S1 []); [exact HP| exact SUBLh| clear - G1 G2; lia| left; exists (mb_bmid R, mb_bm R, 32); split; [exact (SUBLB _ I3)| cbn; clear; lia]
                                                | unfold AAPP_HI; clear - E3b G15; lia| exact X3| exact XP3| apply Forall_nil].
      - eapply (ashobj_addressable_xpres H HH s _ Lh m2 m3 S1 []); [exact HP| exact SUBLh| clear - G1 G2; lia| left; exists (mb_rpid R, mb_rp R, 32); split; [exact (SUBLB _ I4)| cbn; clear; lia]
                                                | unfold AAPP_HI; clear - E4b G15; lia| exact X4| exact XP3| apply Forall_nil]. }
    assert (PAY3 : PAYLOAD_shad m3 R).
    { destruct PAY as (Y1 & Y2 & Y3). split; [| split; [| exact Y3]].
      - eapply (ashobj_accessible_xpres_sub H HH s _ Lh m2 m3 S1 []); [exact HP| exact SUBLh| clear - G1 G2; lia| | exact Y1| exact XP3| apply Forall_nil].
        left. exists (pD, mb_buf R, mb_len R). split; [exact (SUBLB _ PIN)| cbn; clear; lia].
      - exact (ah_blk_shvis H HH _ _ _ _ _ _ HP3 (or_intror (SUBLB _ PIN))). }
    assert (CHN3 : as_chain H m3 (bv_unsigned esp) CHrp).
    { eapply lad_chain_xpres; [exact CHN| exact XP3|].
      intros fp' ra' [E|Hin]; [injection E as <- <-; clear - G3; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' G3; lia]. }
    assert (RF3 : as_RFS H LFx m3) by (eapply (RFS_via_xpres H HH); [exact RF| exact XP3| apply Forall_nil]).
    assert (XPm3 : xpres H Lh S1 XW m0 m3) by (eapply xpres_trans; [exact XP| apply (xpres_nil_X H); exact XP3]).
    assert (SF3 : rw_cells asegs m3 (S1 + 168) [C8 (wz ARP_FILE)]) by (eapply (xpres_rw_cells' H); [exact XP3| exact SF| left; lia| apply Forall_nil]).
    assert (SA3 : rw_cells asegs m3 (S1 + 184) [C8 (wz A)]) by (eapply (xpres_rw_cells' H); [exact XP3| exact SA| left; lia| apply Forall_nil]).
    clear XP3 MBO DS RBc SHB ME IM GM AUX ST MI XP ERR MSH PAY CHN AC AD VIS VIS3 KREL KREL3 RF.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply ald_seg3 with (K := 512 * k) (A' := A');
      [reflexivity| clear - N1 N5 G15 KR; lia| clear - KR; lia| clear - N5 G15 KR; lia| exact MI3]|].
    intros msF5 mo5 KREL5 MP5 VIS5. cbn beta in VIS5.
    (* [comment removed for export] *)
    pose proof (abioeof_mem_spec H) as EF. unfold bioeof_mem_stmt in EF.
    eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5| |].
    { eapply EF with (lo := lo) (LB := LB) (a := mb) (R := mb_after_read R' 512); clear EF; try reflexivity.
      all: try first [exact MBO3| exact ME3| exact MI3| exact CEIL| exact AC3| exact MSH3].
      all: lazymatch goal with
           | |- MEMBIO_below _ _ _ => eapply mb_static_below; [exact MST1| exact MBB]
           | |- MEMBIO_sep _ _ => eapply mb_static_sep; [exact MST1| exact MBS]
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); exact ST3
           | |- lo <= _ => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); unf_stk; clear - LOS; lia
           | |- _ mod 2 = 0 => unfold ALD_R3; rewrite unsigned_lit by (clear; lia); reflexivity
           end. }
    intros msF6 mo6 KREL6 MP6 PO. cbn beta in PO. unfold memctrl_post in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & VIS6 & MU4 & WM4 & MI4 & AC4 & ST4 & MBO4).
    rewrite (unsigned_lit S1) in MU4, ST4 by (clear - G0 G1 G2 G3 G4; lia). rewrite RV in VIS6.
    destruct (lad_head_facts _ _ _ _ _ HP3) as (_ & NIP3 & DISJ3 & _ & _).
    assert (NSH4 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, S1)]) by (apply Forall_cons; [cbn; right; clear - G0 G1; unfold AHI_LO; lia| apply Forall_nil]).
    assert (CW4 : Forall (aclient_write_ok H ((p', A', 512 * (k + 1 + 1)) :: Lh)) [(lo, S1)]) by (apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
    assert (AW4 : Forall (afs_write_ok H LFx) [(lo, S1)]) by (apply Forall_cons; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE; clear - G0 G1 G8; lia| apply Forall_nil]).
    eapply (KONT m4 msF6 mo6 s3 p' A'); clear KONT; [| exact VIS6| exact KREL6
      | eapply (ah_mpres_trans H HH); [| exact MP6]; eapply (ah_mpres_trans H HH); [| exact MP5]; eapply (ah_mpres_trans H HH); [| exact MP4];
        eapply (ah_mpres_trans H HH); [exact MP| exact MP3]].
    unfold LAD.
    split; [eapply (ah_RHEAP_frame H HH); [exact HP3| exact MU4| exact WM4| exact CW4]|].
    split; [exact MBO4|]. split; [exact MST1|].
    split; [cbn [mb_pos mb_after_read mb_advance]; rewrite POS; clear; lia|].
    split; [clear - KL; lia|].
    split; [eapply bytes_at_transport; [exact DS3| exact MU4|]; rewrite DSL; clear - EPb CEIL; cbn -[Z.add Z.mul Z.sub Z.opp]; lia|].
    split; [eapply rw_cells_transport; [exact PRE3| exact MU4| exact WM4|]; clear - N5 CEIL KR; cbn -[Z.add Z.mul Z.sub Z.opp Z.to_nat Z.of_nat]; lia|].
    split; [exists junk3; eapply rw_cells_transport; [exact JK3| exact MU4| exact WM4| clear - N5 CEIL KR; cbn -[Z.add Z.mul Z.sub Z.opp Z.to_nat Z.of_nat]; lia]|].
    split; [exists 512; eapply rw_cells_transport; [exact RBc3| exact MU4| exact WM4| cbv delta [RBP]; clear - G6 G7 G8 G1; cbn -[Z.add Z.mul Z.sub Z.opp]; lia]|].
    split; [exists errv3; eapply rw_cells_transport; [exact ERR3| exact MU4| exact WM4| clear - ERNG CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp errno_addr]; lia]|].
    split; [unfold METH_mem in *; eapply rw_cells_transport; [exact ME3| exact MU4| exact WM4| unfold A_mem_buf_method, O_METH_BREAD; clear - CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp]; lia]|].
    split. { unfold IMPL_mem in *. destruct IM3 as (J1 & J2 & J3).
             split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU4| exact WM4| unfold A_malloc_impl, A_realloc_impl, A_free_impl; clear - CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp]; lia]). }
    split; [unfold GOT_mem in *; eapply rw_cells_transport; [exact GM3| exact MU4| exact WM4| unfold A_got_CRYPTO_malloc; clear - CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp]; lia]|].
    split; [exact MI4|]. split; [exact ST4|].
    split; [eapply (ah_rauxv_frame H HH); [exact AUX3| exact MU4| exact WM4| exact CW4]|].
    split. { eapply xpres_trans; [exact XPm3|]. eapply (xpres_of_munch_fresh H HH s3 _ m3 m3 m4); [exact HP3| lia| exact MU4| exact WM4|].
             apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    split; [exact AC4|].
    split; [eapply (ah_RFS_frame H HH); [exact RF3| exact MU4| exact WM4| exact AW4]|].
    split; [eapply addressable_across2; [exact AD3| exact N7| exact MU4| exact WM4| exact NSH4]|].
    split. { destruct MSH3 as (X1 & X2 & X3 & X4). unfold MEMBIO_shad in *. cbn [mb_bb mb_bm mb_rp mb_after_read mb_advance] in *. rewrite ?Q3, ?Q4, ?Q5 in *.
             split; [| split; [| split]]; (eapply addressable_across2; [eassumption| eassumption| exact MU4| exact WM4| exact NSH4]). }
    split. { destruct PAY3 as (Y1 & Y2 & Y3). split; [| split; [| exact Y3]].
             - eapply accessible_across; [exact Y1| exact MU4|]. apply Forall_cons; [cbn; right; clear - G0 G1; unfold AHI_LO; lia| apply Forall_nil].
             - pose proof (aapp_bounds _ _ EPc ltac:(clear - L1; lia)) as (_ & _ & K3 & K4 & _).
               eapply shvis_across2; [exact Y2| exact MU4| exact WM4| clear - K4; lia| clear - K3 L1; lia| exact NSH4]. }
    split. { eapply rw_cells_transport; [exact SHB3| exact MU4| exact WM4|]. cbn [cells_size csize Nat.add length disjoint_from].
             pose proof (sh_aapp_range _ _ G9 ltac:(clear; lia)) as (W1 & W2 & W3).
             assert (SR : sh (as_FSB H) <= sh (ff + 2256) /\ sh (ff + 2256) + 1 <= sh (as_FSB H) + nsh 11571200).
             { unfold sh, nsh. clear - G6 G7. Z.div_mod_to_equations. lia. }
             cbv delta [RBP]. unfold AHI_LO in *. clear - SR W1 W2 W3 G0 G1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. split; [| exact I]. lia. }
    split. { eapply (achain_below H HH m3 m4 _ _ _ (S1 + 16)); [exact CHN3| | exact MU4|].
             - intros fp' ra' [E|Hin]; [injection E as <- <-; lia| pose proof (CHB _ _ Hin); lia].
             - apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    split; [exact ALB3|].
    split; [eapply rw_cells_transport; [exact SF3| exact MU4| exact WM4|]; clear - G2; cbn -[Z.add Z.mul Z.sub Z.opp]; lia|].
    exists (wz A); eapply rw_cells_transport; [exact SA3| exact MU4| exact WM4|]; clear - G2; cbn -[Z.add Z.mul Z.sub Z.opp]; lia.
  Qed.

  Lemma lad_slot184 : forall k m m' s p A R' (v' : word),
    0 <= k -> LAD k m s p A R' -> munch [(S1 + 184, S1 + 192)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    rw_cells asegs m' (S1 + 184) [C8 v'] -> LAD k m' s p A R'.
  Proof.
    intros k m m' s p A R' v' K0 INV MU WM MI' SA'.
    destruct INV as (HP & MBO & MST & POS & KL & DS & PRE & [junk JK] & [rb RB] & [errv ERR] & ME & IM & GM & MI & ST & AUX & XP
                     & AC & RF & AD & MSH & PAY & SHB & CHN & ALB & SF & _).
    pose proof (lad_geo _ _ _ _ _ HP) as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
    unfold AIMG_TOP, AFS_HDR, AFS_SIZE in G5, G6, G7, G8, G9, G11, G14.
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
    destruct (lad_head_facts _ _ _ _ _ HP) as (BR & NIP & DISJ & BLK & SV).
    pose proof MST as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
    pose proof MBO as MB0. destruct MB0 as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _).
    cbn [mb_id mb_bbid mb_bmid mb_rpid mb_bb mb_bm mb_rp] in I1, I2, I3, I4.
    rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I1. rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I2.
    rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I3. rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I4.
    pose proof (BLK _ (SUBLB _ I1)) as (_ & _ & _ & E1a & E1b & E1f & E1c). pose proof (BLK _ (SUBLB _ I2)) as (_ & _ & _ & E2a & E2b & E2f & E2c).
    pose proof (BLK _ (SUBLB _ I3)) as (_ & _ & _ & E3a & E3b & E3f & E3c). pose proof (BLK _ (SUBLB _ I4)) as (_ & _ & _ & E4a & E4b & E4f & E4c).
    cbn [blk_addr blk_size fst snd] in E1a, E1b, E1f, E1c, E2a, E2b, E2f, E2c, E3a, E3b, E3f, E3c, E4a, E4b, E4f, E4c.
    assert (L1 : 1 <= mb_len R) by (clear - K0 KL; lia). destruct (PAYL L1) as [pD PIN].
    pose proof (BLK _ (SUBLB _ PIN)) as (_ & _ & _ & EPa & EPb & EPf & EPc). cbn [blk_addr blk_size fst snd] in EPa, EPb, EPf, EPc.
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    unfold zlength in DSL.
    assert (NSH : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(S1 + 184, S1 + 192)]) by (apply Forall_cons; [cbn; right; clear - G0 G1 G2; unfold AHI_LO; lia| apply Forall_nil]).
    assert (CW : Forall (aclient_write_ok H ((p, A, 512 * (k + 1)) :: Lh)) [(S1 + 184, S1 + 192)]) by (apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
    assert (AW : Forall (afs_write_ok H LFx) [(S1 + 184, S1 + 192)]) by (apply Forall_cons; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE; clear - G0 G1 G2 G8; lia| apply Forall_nil]).
    assert (XPs : xpres H Lh (S1 + 192) [] m m').
    { eapply (xpres_of_munch_fresh H HH s _ m m m'); [exact HP| lia| exact MU| exact WM|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    unfold LAD.
    split; [eapply (ah_RHEAP_frame H HH); [exact HP| exact MU| exact WM| exact CW]|].
    split; [eapply lad_MEMBIO_xpres; [exact MBO| exact XPs]|]. split; [exact MST|].
    split; [exact POS|]. split; [exact KL|].
    split; [eapply bytes_at_transport; [exact DS| exact MU|]; rewrite DSL; clear - EPb CEIL G2; cbn -[Z.add Z.mul Z.sub Z.opp]; lia|].
    split; [eapply rw_cells_transport; [exact PRE| exact MU| exact WM|]; clear - G12 G1 G2 K0; cbn -[Z.add Z.mul Z.sub Z.opp Z.to_nat Z.of_nat]; lia|].
    split; [exists junk; eapply rw_cells_transport; [exact JK| exact MU| exact WM| clear - G12 G1 G2 K0; cbn -[Z.add Z.mul Z.sub Z.opp Z.to_nat Z.of_nat]; lia]|].
    split; [exists rb; eapply rw_cells_transport; [exact RB| exact MU| exact WM| cbv delta [RBP]; clear - G6 G7 G8 G1 G2; cbn -[Z.add Z.mul Z.sub Z.opp]; lia]|].
    split; [exists errv; eapply rw_cells_transport; [exact ERR| exact MU| exact WM| clear - ERNG G0 G1 G2; cbn -[Z.add Z.mul Z.sub Z.opp errno_addr]; lia]|].
    split; [unfold METH_mem in *; eapply rw_cells_transport; [exact ME| exact MU| exact WM| unfold A_mem_buf_method, O_METH_BREAD; clear - G0 G1 G2; cbn -[Z.add Z.mul Z.sub Z.opp]; lia]|].
    split. { unfold IMPL_mem in *. destruct IM as (J1 & J2 & J3).
             split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| unfold A_malloc_impl, A_realloc_impl, A_free_impl; clear - G0 G1 G2; cbn -[Z.add Z.mul Z.sub Z.opp]; lia]). }
    split; [unfold GOT_mem in *; eapply rw_cells_transport; [exact GM| exact MU| exact WM| unfold A_got_CRYPTO_malloc; clear - G0 G1 G2; cbn -[Z.add Z.mul Z.sub Z.opp]; lia]|].
    split; [exact MI'|].
    split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]; cbn -[Z.add Z.mul Z.sub Z.opp]; lia|].
    split; [eapply (ah_rauxv_frame H HH); [exact AUX| exact MU| exact WM| exact CW]|].
    split. { eapply xpres_trans; [exact XP|]. eapply (xpres_of_munch_fresh H HH s _ m m m'); [exact HP| lia| exact MU| exact WM|].
             apply Forall_cons; [right; right; intros a Ha; cbv delta [XW]; cbn; right; left; cbn in Ha; lia| apply Forall_nil]. }
    split; [eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| lia]|].
    split; [eapply (ah_RFS_frame H HH); [exact RF| exact MU| exact WM| exact AW]|].
    split; [eapply addressable_across2; [exact AD| exact G13| exact MU| exact WM| exact NSH]|].
    split. { destruct MSH as (X1 & X2 & X3 & X4). unfold MEMBIO_shad in *. rewrite ?Q3, ?Q4, ?Q5 in *.
             split; [| split; [| split]]; (eapply addressable_across2; [eassumption| eassumption| exact MU| exact WM| exact NSH]). }
    split. { destruct PAY as (Y1 & Y2 & Y3). split; [| split; [| exact Y3]].
             - eapply accessible_across; [exact Y1| exact MU|]. apply Forall_cons; [cbn; right; clear - G0 G1 G2; unfold AHI_LO; lia| apply Forall_nil].
             - pose proof (aapp_bounds _ _ EPc ltac:(clear - L1; lia)) as (_ & _ & K3 & K4 & _).
               eapply shvis_across2; [exact Y2| exact MU| exact WM| clear - K4; lia| clear - K3 L1; lia| exact NSH]. }
    split. { eapply rw_cells_transport; [exact SHB| exact MU| exact WM|]. cbn [cells_size csize Nat.add length disjoint_from].
             pose proof (sh_aapp_range _ _ G9 ltac:(clear; lia)) as (W1 & W2 & W3).
             assert (SR : sh (as_FSB H) <= sh (ff + 2256) /\ sh (ff + 2256) + 1 <= sh (as_FSB H) + nsh 11571200).
             { unfold sh, nsh. clear - G6 G7. Z.div_mod_to_equations. lia. }
             cbv delta [RBP]. unfold AHI_LO in *. clear - SR W1 W2 W3 G0 G1 G2. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. split; [| exact I]. lia. }
    split. { eapply (achain_below H HH m m' _ _ _ (bv_unsigned esp)); [exact CHN| | exact MU|].
             - intros fp' ra' [E|Hin]; [injection E as <- <-; lia| pose proof (CHB _ _ Hin); lia].
             - apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    split; [exact ALB|].
    split; [eapply rw_cells_transport; [exact SF| exact MU| exact WM|]; cbn -[Z.add Z.mul Z.sub Z.opp]; lia|].
    exists v'; exact SA'.
  Qed.

  (* [comment removed for export] *)
  Lemma lad_loop : forall (fuel : nat) (k : Z) m msF mo s p A R' (s4v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Q : config -> Prop),
    Z.of_nat fuel = 32 - k -> 0 <= k <= 31 ->
    LAD k m s p A R' -> rw_cells asegs m (S1 + 184) [C8 (wz A)] -> as_VIS H s msF = lad_entry k m A s4v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    lad_doneK Q -> lad_capK Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    induction fuel as [|fuel IH]; intros k m msF mo s p A R' s4v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 Q FUEL KR INV SA VIS KREL MP KD KC; [exfalso; clear - FUEL KR; lia|].
    pose proof INV as (HP0 & _ & MST & POS & KL & _).
    eapply lad_read; [exact KR| exact INV| exact SA| exact VIS| exact KREL|].
    intros m2 msF2 mo2 R2 n junk' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 NEQ R2EQ VIS2 KREL2 MP2 HP MBO DS PRE OUT RBc ERR ME IM GM MI ST AUX XP AC RF AD MSH PAY SHB CHN ALB SF2 SA2.
    subst R2.
    destruct (Z_le_gt_dec (mb_len R) (512 * k + 512)) as [LAST|MORE].
    - (* [comment removed for export] *)
      assert (NE : n = mb_len R - 512 * k) by (rewrite NEQ; clear - LAST KL; lia).
      eapply lad_done; try eassumption; [clear - LAST KL NE; lia| eapply (ah_mpres_trans H HH); [exact MP| exact MP2]].
    - (* [comment removed for export] *)
      assert (NE : n = 512) by (rewrite NEQ; clear - MORE; lia). clear NEQ. subst n.
      eapply lad_grow; try eassumption; [reflexivity| clear - MORE; lia| eapply (ah_mpres_trans H HH); [exact MP| exact MP2]|].
      intros m4 msF4 mo4 s4 p' A' v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 INV4 VIS4 KREL4 MP4.
      replace (ret_pc (Z_to_bv 64 ALD_R3)) with (Z_to_bv 64 ALD_R3) in VIS4 by (symmetry; apply ret_pc_even; [unfold ALD_R3; lia| reflexivity]).
      pose proof INV4 as (HPs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [vs SAs]).
      assert (SG : 0 <= S1 /\ S1 + 192 < 2^64) by (pose proof (lad_geo _ _ _ _ _ HPs) as (G0 & G1 & G2 & G3 & G4 & _); clear - G0 G1 G2 G3 G4; lia).
      destruct (Z.eq_dec k 31) as [CAP|NCAP].
      + (* [comment removed for export] *)
        rewrite CAP in VIS4. change (32 - 31) with 1 in VIS4.
        eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply ald_seg4_cap; [reflexivity| exact (proj1 SG)| exact (proj2 SG)| exact SAs| exact MIs]|]. intros msF5 mo5 KREL5 MP5 PO5. cbn beta in PO5.
        destruct PO5 as (m4x & VIS5 & MUs & WMs & MIx & SAx).
        pose proof (lad_slot184 (k + 1) _ _ _ _ _ _ _ ltac:(clear - KR; lia) INV4 MUs WMs MIx SAx) as INV4x.
        clear INV4 VIS4 HPs MIs SAs MUs WMs. clear m4. rename m4x into m4. rename INV4x into INV4.
        pose proof INV4 as (HP4 & MBO4 & MST4 & POS4 & KL4 & DS4 & PRE4 & [junk4 JK4] & RB4 & ERR4 & ME4 & IM4 & GM4 & MI4 & ST4 & AUX4 & XP4
                           & AC4 & RF4 & AD4 & MSH4 & PAY4 & SHB4 & CHN4 & ALB4 & SF4 & [vq SA4q]).
      pose proof (lad_geo _ _ _ _ _ HP4) as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
      unfold AIMG_TOP, AFS_HDR, AFS_SIZE in G5, G6, G7, G8, G9, G11, G14.
      assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
      pose proof LO as LOS. unf_stk_in LOS.
      pose proof MST as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
        pose proof (abioeof_mem_spec H) as EF. unfold bioeof_mem_stmt in EF.
        eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5| |].
        { eapply EF with (lo := lo) (LB := LB) (a := mb) (R := mb_after_read R' 512); clear EF; try reflexivity.
          all: try first [exact MBO4| exact ME4| exact MI4| exact CEIL| exact AC4| exact MSH4].
          all: lazymatch goal with
               | |- MEMBIO_below _ _ _ => eapply mb_static_below; [exact MST4| exact MBB]
               | |- MEMBIO_sep _ _ => eapply mb_static_sep; [exact MST4| exact MBS]
               | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); exact ST4
               | |- lo <= _ => rewrite unsigned_lit by (clear - G0 G1 G2 G3 G4; lia); unf_stk; clear - LOS; lia
               | |- _ mod 2 = 0 => unfold ALD_RC; rewrite unsigned_lit by (clear; lia); reflexivity
               end. }
        intros msF6 mo6 KREL6 MP6 PO. cbn beta in PO. unfold memctrl_post in PO.
        destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m5 & VIS6 & MU5 & WM5 & MI5 & AC5 & ST5 & MBO5).
        rewrite (unsigned_lit S1) in MU5, ST5 by (clear - G0 G1 G2 G3 G4; lia).
        pose proof MBO4 as MB0. destruct MB0 as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _).
        cbn [mb_id mb_bbid mb_bmid mb_rpid mb_bb mb_bm mb_rp mb_buf mb_len mb_after_read mb_advance] in I1, I2, I3, I4.
        rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I1. rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I2.
        rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I3. rewrite ?Q3, ?Q4, ?Q5, ?Q6, ?Q7, ?Q8, ?Q9 in I4.
        destruct (lad_head_facts _ _ _ _ _ HP4) as (BR4 & NIP4 & DISJ4 & BLK4 & _).
        pose proof (BLK4 _ (SUBLB _ I1)) as (_ & _ & _ & E1a & E1b & E1f & E1c). pose proof (BLK4 _ (SUBLB _ I2)) as (_ & _ & _ & E2a & E2b & E2f & E2c).
        pose proof (BLK4 _ (SUBLB _ I3)) as (_ & _ & _ & E3a & E3b & E3f & E3c). pose proof (BLK4 _ (SUBLB _ I4)) as (_ & _ & _ & E4a & E4b & E4f & E4c).
        cbn [blk_addr blk_size fst snd] in E1a, E1b, E1f, E1c, E2a, E2b, E2f, E2c, E3a, E3b, E3f, E3c, E4a, E4b, E4f, E4c.
        assert (L1 : 1 <= mb_len R) by (clear - KL KR; lia). destruct (PAYL L1) as [pD PIN].
        pose proof (BLK4 _ (SUBLB _ PIN)) as (_ & _ & _ & EPa & EPb & EPf & EPc). cbn [blk_addr blk_size fst snd] in EPa, EPb, EPf, EPc.
        unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *. unfold zlength in DSL.
        assert (NSH5 : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, S1)]) by (apply Forall_cons; [cbn; right; clear - G0 G1; unfold AHI_LO; lia| apply Forall_nil]).
        unfold lad_capK in KC. rewrite CAP in HP4, KL4, POS4, PRE4, JK4, AD4, G12, G13. change (512 * (31 + 1 + 1)) with (512 * 33) in HP4, AD4, G12, G13.
        assert (CW5 : Forall (aclient_write_ok H ((p', A', 512 * 33) :: Lh)) [(lo, S1)]) by (apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
        assert (AW5 : Forall (afs_write_ok H LFx) [(lo, S1)]) by (apply Forall_cons; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE; clear - G0 G1 G8; lia| apply Forall_nil]).
        (* [comment removed for export] *)
        replace (A' + 512 * (31 + 1)) with (A' + Z.of_nat (Z.to_nat (512 * (31 + 1)))) in JK4 by (clear; lia).
        pose proof (rw_cells_CB_join asegs m4 A' _ _ _ _ PRE4 JK4) as WH4. change (Z.to_nat (512 * (31 + 1)) + 512)%nat with (Z.to_nat (512 * 33)) in WH4.
        eapply (KC m5 msF6 mo6 s4 p' A' _ (mb_after_read R' 512)); clear KC KD IH.
        all: try first [exact VIS6| exact KREL6| exact MBO5| exact MST4| exact MI5| exact ST5| exact AC5].
        * eapply (ah_RHEAP_frame H HH); [exact HP4| exact MU5| exact WM5| exact CW5].
        * eapply (ah_mpres_trans H HH); [| exact MP6]. eapply (ah_mpres_trans H HH); [exact MP4| exact MP5].
        * cbn [mb_pos mb_after_read mb_advance]. rewrite POS, CAP. reflexivity.
        * clear - KL4; lia.
        * eapply bytes_at_transport; [exact DS4| exact MU5|]. rewrite DSL. clear - EPb CEIL; cbn -[Z.add Z.mul Z.sub Z.opp]; lia.
        * exists (firstn (Z.to_nat (512 * (31 + 1))) ds ++ junk4). eapply rw_cells_transport; [exact WH4| exact MU5| exact WM5|]. clear - G12 CEIL; cbn -[Z.add Z.mul Z.sub Z.opp]; lia.
        * destruct RB4 as [rb RB]. exists rb. eapply rw_cells_transport; [exact RB| exact MU5| exact WM5| cbv delta [RBP]; clear - G6 G7 G8 G1; cbn -[Z.add Z.mul Z.sub Z.opp]; lia].
        * destruct ERR4 as [errv ERR5]. exists errv. eapply rw_cells_transport; [exact ERR5| exact MU5| exact WM5| clear - ERNG CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp errno_addr]; lia].
        * unfold METH_mem in *; eapply rw_cells_transport; [exact ME4| exact MU5| exact WM5| unfold A_mem_buf_method, O_METH_BREAD; clear - CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp]; lia].
        * unfold IMPL_mem in *. destruct IM4 as (J1 & J2 & J3).
          split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU5| exact WM5| unfold A_malloc_impl, A_realloc_impl, A_free_impl; clear - CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp]; lia]).
        * unfold GOT_mem in *; eapply rw_cells_transport; [exact GM4| exact MU5| exact WM5| unfold A_got_CRYPTO_malloc; clear - CEIL G0; cbn -[Z.add Z.mul Z.sub Z.opp]; lia].
        * eapply (ah_rauxv_frame H HH); [exact AUX4| exact MU5| exact WM5| exact CW5].
        * eapply xpres_trans; [exact XP4|]. eapply (xpres_of_munch_fresh H HH s4 _ m4 m4 m5); [exact HP4| lia| exact MU5| exact WM5|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil].
        * eapply (ah_RFS_frame H HH); [exact RF4| exact MU5| exact WM5| exact AW5].
        * eapply addressable_across2; [exact AD4| exact G13| exact MU5| exact WM5| exact NSH5].
        * destruct MSH4 as (X1 & X2 & X3 & X4). unfold MEMBIO_shad in *. cbn [mb_bb mb_bm mb_rp mb_after_read mb_advance] in *. rewrite ?Q3, ?Q4, ?Q5 in *.
          split; [| split; [| split]]; (eapply addressable_across2; [eassumption| eassumption| exact MU5| exact WM5| exact NSH5]).
        * destruct PAY4 as (Y1 & Y2 & Y3). split; [| split; [| exact Y3]].
          -- eapply accessible_across; [exact Y1| exact MU5|]. apply Forall_cons; [cbn; right; clear - G0 G1; unfold AHI_LO; lia| apply Forall_nil].
          -- pose proof (aapp_bounds _ _ EPc ltac:(clear - L1; lia)) as (_ & _ & K3 & K4 & _).
             eapply shvis_across2; [exact Y2| exact MU5| exact WM5| clear - K4; lia| clear - K3 L1; lia| exact NSH5].
        * eapply rw_cells_transport; [exact SHB4| exact MU5| exact WM5|]. cbn [cells_size csize Nat.add length disjoint_from].
          pose proof (sh_aapp_range _ _ G9 ltac:(clear; lia)) as (W1 & W2 & W3).
             assert (SR : sh (as_FSB H) <= sh (ff + 2256) /\ sh (ff + 2256) + 1 <= sh (as_FSB H) + nsh 11571200).
             { unfold sh, nsh. clear - G6 G7. Z.div_mod_to_equations. lia. }
          cbv delta [RBP]. unfold AHI_LO in *. clear - SR W1 W2 W3 G0 G1. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. split; [| exact I]. lia.
        * eapply (achain_below H HH m4 m5 _ _ _ (S1 + 16)); [exact CHN4| | exact MU5|].
          -- intros fp' ra' [E|Hin]; [injection E as <- <-; lia| pose proof (CHB _ _ Hin); lia].
          -- apply Forall_cons; [left; cbn; lia| apply Forall_nil].
        * rewrite CAP in ALB4. exact ALB4.
        * eapply rw_cells_transport; [exact SF4| exact MU5| exact WM5|]; clear - G2; cbn -[Z.add Z.mul Z.sub Z.opp]; lia.
        * eapply rw_cells_transport; [exact SAx| exact MU5| exact WM5|]; clear - G2; cbn -[Z.add Z.mul Z.sub Z.opp]; lia.
      + (* [comment removed for export] *)
        eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply ald_seg4 with (c := 32 - k); [reflexivity| clear - KR NCAP; lia| exact (proj1 SG)| exact (proj2 SG)| exact SAs| exact MIs]|].
        intros msF5 mo5 KREL5 MP5 PO5. cbn beta in PO5. destruct PO5 as (m5 & VIS5 & MU5 & WM5 & MI5 & SA5).
        replace (32 - k - 1) with (32 - (k + 1)) in VIS5 by (clear; lia).
        replace (A' + 512 * k + 512) with (A' + 512 * (k + 1)) in VIS5 by (clear; lia).
        replace (512 * k + 512) with (512 * (k + 1)) in VIS5 by (clear; lia).
        eapply (IH (k + 1)); [clear - FUEL; lia| clear - KR NCAP; lia| exact (lad_slot184 (k + 1) _ _ _ _ _ _ _ ltac:(clear - KR; lia) INV4 MU5 WM5 MI5 SA5)| exact SA5| exact VIS5| exact KREL5| eapply (ah_mpres_trans H HH); [exact MP4| exact MP5]| exact KD| exact KC].
  Qed.
End W.
