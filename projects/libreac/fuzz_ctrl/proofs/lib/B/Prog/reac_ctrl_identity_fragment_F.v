(* The footprint twin of the B proof of reac_ctrl_identity_fragment (0x859e4): the same run as an ExecF.evtF
   under a footprint RNG (reac_ctrl_identity_fragment_contract_F of reac_ctrl_identity_fragment_c.v), by the
   script of that proof over StepF's step. Every access of the run is closed from one rng premise: the image
   [IMG_LO, IMG_HI) (instruction fetches and the absolute cells), the stack window [S - 4672, S) of this frame and
   of its callees' frames with the 8-aligned WORD span of its shadow bytes, and, per buffer, the buffer bytes and
   the 8-aligned WORD cover of its shadow bytes.
   This file assumes nothing beyond its three callee contracts; they stay Section hypotheses of the theorem, as
   they are in the plain proof. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcFrag RcFragLib
  RcParseLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFPLib memcmp_c bcmp_wrap_c
  asan_memcpy_c asan_memcpy_cF reac_ctrl_record_cksum_verify_c reac_ctrl_identity_fragment_c.
(* Last: StepF's step (evtF goals) must shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Lemma fa_le1_zxb : forall b : byte, le1 (zxb b) = [b].
Proof. exact le1_zxb. Qed.

Local Ltac mem_after_store_opt ::=
  try rewrite fa_le1_zxb;
  try rewrite rf_le1_0;
  try rewrite rf_le1_1;
  norm_lit_store_bytes;
  try rewrite rf_le1_0;
  try rewrite rf_le1_1;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Lemma fa_beq : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma fa_ltu : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma fa_land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma fa_rw_bytes : forall m A cs bs, rw_cells rsegs m A cs -> cells_bytes cs = bs -> bytes_at rsegs m A bs.
Proof. intros m A cs bs [[_ H] _] E. subst. exact H. Qed.

Lemma fa_app4 : forall m A B C D a b c d,
  bytes_at rsegs m A a -> bytes_at rsegs m B b -> bytes_at rsegs m C c -> bytes_at rsegs m D d ->
  B = A + Z.of_nat (length a) -> C = B + Z.of_nat (length b) -> D = C + Z.of_nat (length c) ->
  bytes_at rsegs m A (a ++ b ++ c ++ d).
Proof.
  intros m A B C D a b c d HA HB HC HD -> -> ->.
  apply (proj2 (bytes_at_app rsegs m _ _ _)). split; [exact HA|].
  apply (proj2 (bytes_at_app rsegs m _ _ _)). split; [exact HB|].
  apply (proj2 (bytes_at_app rsegs m _ _ _)). split; [exact HC | exact HD].
Qed.

Lemma fa_mcmp : forall n l r, (n <= length l)%nat -> (n <= length r)%nat ->
  exists v, memcmp_model l r n = Some v /\ -255 <= v <= 255 /\
    (v = 0 <-> forall i, (i < n)%nat -> bv_unsigned (nth i l (Z_to_bv 8 0)) = bv_unsigned (nth i r (Z_to_bv 8 0))).
Proof.
  induction n as [|n IH]; intros l r Hl Hr.
  - exists 0. split; [reflexivity|]. split; [lia|]. split; [intros _ i Hi; lia | reflexivity].
  - destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
    cbn [memcmp_model]. pose proof (byte_range a) as Ra. pose proof (byte_range b) as Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r ltac:(cbn in Hl; lia) ltac:(cbn in Hr; lia)) as (v & Hv & Rv & Iv).
      exists v. split; [exact Hv|]. split; [exact Rv|]. rewrite Iv. split.
      * intros Hall i Hi. destruct i as [|i]; [exact E|]. cbn [nth]. apply Hall. lia.
      * intros Hall i Hi. apply (Hall (S i)). lia.
    + exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|]. split; [lia|].
      split; [intros; lia|]. intros Hall. specialize (Hall 0%nat ltac:(lia)). cbn [nth] in Hall. lia.
Qed.

Lemma fa_store_ok : forall m a n (j : nat), wr_at rsegs m a n -> Z.of_nat j <= n -> store_ok rsegs m (wa a) j = true.
Proof.
  intros m a n j H Hj. replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  apply (wr_at_store_ok rsegs m a n 0 j H); lia.
Qed.

Lemma fa_rw_of : forall m A bs, bytes_at rsegs m A bs -> wr_at rsegs m A (Z.of_nat (length bs)) ->
  rw_cells rsegs m A [CB (length bs) bs].
Proof.
  intros m A bs HB HW. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma fa_clear_app : forall P X : list byte, (7 <= length P)%nat -> fg_clear (P ++ X) = fg_clear P ++ X.
Proof.
  intros P X HP. unfold fg_clear. rewrite firstn_app, skipn_app.
  replace (6 - length P)%nat with 0%nat by lia. replace (7 - length P)%nat with 0%nat by lia.
  cbn [firstn skipn]. rewrite app_nil_r, !app_assoc. reflexivity.
Qed.

Lemma fa_clear_join : forall st g, length st = 72%nat -> 1 <= fg_n g -> fg_T st g <= 64 ->
  fg_clear (fg_join st g) =
  firstn 6 st ++ [Z_to_bv 8 0] ++ bsl st 7 (1 + fg_lf st) ++ fg_body g ++ skipn (Z.to_nat (8 + fg_T st g)) st.
Proof.
  intros st g HL Hn HT.
  pose proof (byte_range (nth (Z.to_nat 7) st (Z_to_bv 8 0))) as R.
  change (bv_unsigned (nth (Z.to_nat 7) st (Z_to_bv 8 0))) with (fg_lf st) in R.
  unfold fg_join. rewrite fa_clear_app by (rewrite length_firstn; unfold fg_T in HT; lia).
  unfold fg_clear. rewrite firstn_firstn, skipn_firstn_comm.
  replace (Nat.min 6 (Z.to_nat (8 + fg_lf st))) with 6%nat by lia.
  unfold bsl. replace (Z.to_nat (8 + fg_lf st) - 7)%nat with (Z.to_nat (1 + fg_lf st)) by lia.
  change (Z.to_nat 7) with 7%nat. rewrite !app_assoc. reflexivity.
Qed.

(* UBSan pointer-overflow tests compare against 2^64 - c (the literal -c). *)
Lemma u_ltu_negr : forall x y, 0 <= x -> -2^64 < y < 0 -> x < 2^64 + y ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof.
  intros x y Hx Hy Hxy. unfold bv_ltu. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  apply Z.ltb_lt. change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma u_ltu_negl : forall x y, 0 <= x -> -2^64 < y < 0 -> x <= 2^64 + y ->
  bv_ltu (Z_to_bv 64 y) (Z_to_bv 64 x) = false.
Proof.
  intros x y Hx Hy Hxy. unfold bv_ltu. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  apply Z.ltb_ge. change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma u_eqb_negc : forall x y, 0 <= x -> -2^64 < y < 0 -> x < 2^64 + y ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy Hxy. unfold bv_eqb. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  apply Z.eqb_neq. change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma u_eqb_m1 : bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0) = false.
Proof. unfold bv_eqb. rewrite !unsigned_lit_wrap. reflexivity. Qed.

(* An unsigned test that is not taken, with both sides as literals or zero-extended bytes. *)
Ltac ltf := match goal with |- context [bv_ltu ?X ?Y] =>
  let H := fresh "LT" in
  assert (H : bv_ltu X Y = false)
    by (unfold bv_ltu, zxb; rewrite ?unsigned_lit_wrap; apply Z.ltb_ge;
        change (2^64) with 18446744073709551616 in *; Z.div_mod_to_equations; lia);
  rewrite H; clear H; cbv iota end.

Ltac bnz0 := rewrite (rc_eqb64 0 0) by lia; change (0 =? 0) with true; cbn [negb]; cbv iota.

Lemma fa_app_out : forall a, app_mem a -> in_shadow a -> False.
Proof. unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. lia. Qed.

Lemma fa_addr_out : forall m p n x, addressable m p n -> in_shadow x -> ~ (p <= x < p + n).
Proof.
  intros m p n x (_ & _ & _ & HA) Hx Hr. destruct (HA (x - p) ltac:(lia)) as [A _].
  replace (p + (x - p)) with x in A by lia. exact (fa_app_out x A Hx).
Qed.

Lemma fa_stk_out : forall lo hi x, HIGHMEM_BEG <= lo -> hi <= APPMEM_END -> in_shadow x -> ~ (lo <= x < hi).
Proof. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. intros. lia. Qed.

Lemma fa_so5 : forall m f pa pp pn lo hi,
  addressable m f 72 -> addressable m pa 2 -> addressable m pp 8 -> addressable m pn 8 ->
  HIGHMEM_BEG <= lo -> hi <= APPMEM_END ->
  forall x, in_shadow x -> outside [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (lo, hi)] x.
Proof.
  intros m f pa pp pn lo hi Af Aa Ap An Hlo Hhi x Hx. cbn [outside].
  split; [exact (fa_addr_out _ _ _ x Af Hx)|]. split; [exact (fa_addr_out _ _ _ x Aa Hx)|].
  split; [exact (fa_addr_out _ _ _ x Ap Hx)|]. split; [exact (fa_addr_out _ _ _ x An Hx)|].
  split; [exact (fa_stk_out lo hi x Hlo Hhi Hx) | exact I].
Qed.

Lemma fa_ro5 : forall f pa pp pn lo hi, HIGHMEM_BEG <= lo ->
  dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)] ->
  forall x, RT_LO <= x < RT_HI -> outside [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (lo, hi)] x.
Proof.
  intros f pa pp pn lo hi Hlo D x Hx. cbn [dj_from] in D. cbn [outside].
  destruct D as (D1 & D2 & D3 & D4 & _). unfold RT_LO, RT_HI, HIGHMEM_BEG in *.
  split; [clear D2 D3 D4; lia|]. split; [clear D1 D3 D4; lia|]. split; [clear D1 D2 D4; lia|].
  split; [clear D1 D2 D3; lia|]. split; [lia | exact I].
Qed.

Lemma fa_addr_sub : forall mm p n p' n', addressable mm p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  addressable mm p' n'.
Proof.
  intros mm p n p' n' (H0 & Hn & He & HA) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HA. lia.
Qed.

Lemma fa_addr_app : forall mm p n i, addressable mm p n -> 0 <= i < n -> app_mem (p + i).
Proof. intros mm p n i (_ & _ & _ & HA) Hi. exact (proj1 (HA i Hi)). Qed.

Lemma fa_app_mid : forall a b x, app_mem a -> app_mem b -> a <= x <= b -> b - a <= 100 -> app_mem x.
Proof. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia. Qed.

(* Model lemmas (identical to the plain proof): the frame/record predicates as conjunctions. *)
Lemma fr_iff : forall len g, fg_fr len g = true <->
  50 <= len /\ bat g 16 = 205 /\ bat g 17 = 234 /\ bat g 18 = 4 /\ (bat g 19 = 1 \/ bat g 19 = 2) /\
  bat g 22 = 0 /\ bat g 23 = 2 /\ bat g 24 = 0 /\ bat g 25 = 254 /\ 1 <= fg_n g /\ fg_n g <= 22 /\
  blocksum (skipn 18 g) = 0.
Proof. intros len g. unfold fg_fr. rewrite !andb_true_iff, !orb_true_iff, !Z.eqb_eq, !Z.leb_le. tauto. Qed.

Lemma close_iff : forall st g, fg_close st g = true <->
  14 <= fg_T st g /\ bat (fg_join st g) 8 = 240 /\ bat (fg_join st g) 9 = 65 /\ bat (fg_join st g) 11 = 0 /\
  bat (fg_join st g) 12 = 0 /\ bat (fg_join st g) 13 = 18 /\ bat (fg_join st g) 14 = 18 /\
  bat (fg_join st g) 15 = 5 /\ bat (fg_join st g) 16 = 0 /\ bat (fg_join st g) (7 + fg_T st g) = 247 /\
  recsum (bsl (fg_join st g) 15 (fg_T st g - 8)) = 0.
Proof. intros st g. unfold fg_close. rewrite !andb_true_iff, !Z.eqb_eq, !Z.leb_le. tauto. Qed.

Lemma keep_iff : forall st g, fg_keep st g = true <-> fg_hf st <> 0 /\ fg_src_eq st g = true /\ fg_T st g <= 64.
Proof. intros st g. unfold fg_keep. rewrite !andb_true_iff, negb_true_iff, Z.eqb_neq, Z.leb_le. tauto. Qed.

Ltac fz := rewrite ?length_le8, ?length_le2; cbn [cells_size csize Nat.add length inside]; lia.

Definition hide (P : Prop) : Prop := P.
Lemma hide_i : forall P : Prop, P -> hide P. Proof. intros P H. exact H. Qed.
Ltac fzu D := let H := fresh "DU" in pose proof D as H; unfold hide in H; fz.

(* The _F forms of the two callee contracts this proof uses.  __asan_memcpy's is a Theorem Labs lane's shared statement
   asan_memcpy_contract_F (lib/B/Prog/asan_memcpy_cF.v), which a Theorem Labs lane proves (asan_memcpy_holds_F in
   asan_memcpyF.v).  The bcmp wrapper's footprint contract is published in lib/B/Prog/bcmp_wrap_c.v and comes
   from that file, through the hypothesis BCMPw; its shadow covers have the [y / 8 * 8] form of shw below.
   This proof uses both only through the Section hypotheses MCPY and BCMPw. *)

(* The 8-aligned WORD cover of the shadow bytes of [p, p + n), written at a shadow offset sh that the run reads
   from the runtime cell; at sh = ASAN_K it is the cover the contract states, since shadow_addr a = a / 8 + ASAN_K. *)
Definition shw (RNG : footprint) (sh p n : Z) : Prop :=
  rng RNG ((p / 8 + sh) / 8 * 8) (((p + n - 1) / 8 + sh) / 8 * 8 + 8 - (p / 8 + sh) / 8 * 8).

(* A sub-range of a buffer keeps the word cover of its shadow bytes. *)
Lemma shw_sub : forall (RNG : footprint) sh p n p' n',
  p <= p' -> 0 < n' -> p' + n' <= p + n -> shw RNG sh p n -> shw RNG sh p' n'.
Proof.
  intros RNG sh p n p' n' H1 H2 H3 H. unfold shw in H |- *.
  apply (rng_sub' RNG _ _ _ _ H). Z.div_mod_to_equations; lia.
Qed.

(* The shadow bytes of a sub-range lie inside that word cover, one byte per 8 bytes of the range. *)
Lemma shw_bytes : forall (RNG : footprint) sh p n p' n',
  p <= p' -> 0 < n' -> p' + n' <= p + n -> shw RNG sh p n ->
  rng RNG (p' / 8 + sh) ((p' + n' - 1) / 8 - p' / 8 + 1).
Proof.
  intros RNG sh p n p' n' H1 H2 H3 H. unfold shw in H.
  apply (rng_sub' RNG _ _ _ _ H). Z.div_mod_to_equations; lia.
Qed.
(* The same, in the byte form a callee contract states it (shadow_addr of the last byte minus of the first). *)
Lemma shw_bytes' : forall (RNG : footprint) sh p n p' n',
  p <= p' -> 0 < n' -> p' + n' <= p + n -> shw RNG sh p n ->
  rng RNG (p' / 8 + sh) ((p' + n' - 1) / 8 + sh - (p' / 8 + sh) + 1).
Proof.
  intros RNG sh p n p' n' H1 H2 H3 H. unfold shw in H.
  apply (rng_sub' RNG _ _ _ _ H). Z.div_mod_to_equations; lia.
Qed.


Section P.
Hypothesis MCPY : asan_memcpy_contract_F.
Hypothesis BCMPw : bcmp_wrap_contract_F.
Hypothesis CKV : reac_ctrl_record_cksum_verify_contract_F.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Ff : bvmap 5 word) (fc : bv 32)
  (mE : word -> option byte) (f fr len pa pp pn S off : Z) (st g : list byte) (RNG : footprint).
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rfr : 0 <= fr < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis Rpa : 0 <= pa < 2^64.
Hypothesis Rpp : 0 <= pp < 2^64.
Hypothesis Rpn : 0 <= pn < 2^64.
Hypothesis RS : 0x10007fff8000 <= S - 4672 /\ S <= 0x800000000000.
Hypothesis Hg : length g = 50%nat.
Hypothesis Hst : length st = 72%nat.
Hypothesis HCE : asan_cells mE.
Hypothesis HSW : shadow_rw mE.
Hypothesis HRT : asan_rt rsegs mE GOT_CELL_K CELL_K off [(S - 4672, S)].
Hypothesis HGOT : f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
  bytes_at rsegs mE REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mE REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs mE GOT_CF (le8 (wa CF)) /\ bytes_at rsegs mE (CF + 254) [Z_to_bv 8 1] /\
  bytes_at rsegs mE (CF + 255) [Z_to_bv 8 1].

Local Notation CL := (fg_class f fr pa pp pn len st g).
Local Notation FRc j :=
  [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Notation FRj :=
  [C8 (Z_to_bv 64 (18446744073709551615 - (f + 8))); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4;
   C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Notation Jc := (le8 (Z_to_bv 64 (18446744073709551615 - (f + 8)))).

Definition Qf : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_ret CL))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             Ff (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch (fg_fp 4672 f pa pp pn S CL) mE m' /\ wmono rsegs mE m' /\ mem_inv rsegs m' /\
    stk rsegs m' (S - 4672) S /\ fg_mem f pa pp pn st g CL m' /\ asan_cells m' /\ shadow_rw m'.

Definition NZ : Prop := f <> 0 /\ fr <> 0 /\ pa <> 0 /\ pp <> 0 /\ pn <> 0.
Definition DJA : Prop :=
  (f + 72 <= fr \/ fr + 50 <= f) /\ (f + 72 <= S - 4672 \/ S <= f) /\ (fr + 50 <= S - 4672 \/ S <= fr).
Definition DJB : Prop :=
  (f + 72 <= pa \/ pa + 2 <= f) /\ (f + 72 <= pp \/ pp + 8 <= f) /\ (f + 72 <= pn \/ pn + 8 <= f) /\
  (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
  (pa + 2 <= S - 4672 \/ S <= pa) /\ (pp + 8 <= S - 4672 \/ S <= pp) /\ (pn + 8 <= S - 4672 \/ S <= pn).
Definition OUT : Prop :=
  wr_at rsegs mE pa 2 /\ wr_at rsegs mE pp 8 /\ wr_at rsegs mE pn 8 /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0.

Definition W5 : list (Z * Z) := [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (S - 4672, S)].

Definition ASF : Prop :=
  addressable mE f 72 /\ addressable mE pa 2 /\ addressable mE pp 8 /\ addressable mE pn 8 /\ app_mem (f + 78) /\
  dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)].
Definition SRF : Prop :=
  asan_shadow_rd rsegs mE off f 72 W5 /\ asan_addressable rsegs mE off f 72 /\
  asan_shadow_rd rsegs mE off pa 2 W5 /\ asan_addressable rsegs mE off pa 2 /\
  asan_shadow_rd rsegs mE off pp 8 W5 /\ asan_addressable rsegs mE off pp 8 /\ asan_rt3 rsegs mE off pp 8 /\
  asan_shadow_rd rsegs mE off pn 8 W5 /\ asan_addressable rsegs mE off pn 8 /\ asan_rt3 rsegs mE off pn 8.
Definition ASG : Prop :=
  addressable mE fr 50 /\ asan_shadow_rd rsegs mE off fr 50 W5 /\ asan_addressable rsegs mE off fr 50.
Hypothesis HAF : NZ -> ASF /\ SRF.
Hypothesis HAG : NZ -> 50 <= len -> ASG.

(* The footprint of this run, region by region: the image (every fetch and every absolute cell), the stack
   window of this frame and of the callees' frames below it, and each buffer with the 8-aligned WORD cover of
   its shadow bytes.  RGF and RGG hold under the same guards as ASF and ASG. *)
Definition RGF : Prop :=
  rng RNG f 72 /\ shw RNG off f 72 /\
  rng RNG pa 2 /\ shw RNG off pa 2 /\
  rng RNG pp 8 /\ shw RNG off pp 8 /\
  rng RNG pn 8 /\ shw RNG off pn 8.
Definition RGG : Prop :=
  rng RNG fr 50 /\ shw RNG off fr 50.
(* The run reads the shadow offset from the runtime cell; on this image it is ASAN_K, so the covers above are
   the covers over shadow_addr that the contract states, and the callees' contracts speak of shadow_addr. *)
Hypothesis Hoff : off = ASAN_K.
(* Route 1 one level down (the bcmp wrapper's footprint contract) weakens a byte-wise footprint to a union
   of rng ranges, so that contract takes a footprint that is decided byte by byte (lib/Lib/RngBytes.v). *)
Hypothesis RBY : rng_bytes RNG.
Hypothesis RIMG : rng RNG IMG_LO (IMG_HI - IMG_LO).
Hypothesis RSTK : rng RNG (S - 4672) 4672.
Hypothesis RSTKS : shw RNG off (S - 4672) 4672.
Hypothesis RBF : NZ -> RGF.
Hypothesis RBG : NZ -> 50 <= len -> RGG.

(* Under the non-zero guard: the buffer ranges, their shadow word covers, and the byte range of each buffer's
   shadow bytes (what the single-byte shadow checks of this function read). *)
Ltac rngf NZh :=
  let H := fresh "RGFh" in
  pose proof (RBF NZh) as H; unfold RGF in H;
  destruct H as (RGf & RGfs & RGa & RGas & RGp & RGps & RGn & RGns);
  pose proof (shw_bytes RNG off f 72 f 72 ltac:(lia) ltac:(lia) ltac:(lia) RGfs) as RGfb;
  pose proof (shw_bytes RNG off pa 2 pa 2 ltac:(lia) ltac:(lia) ltac:(lia) RGas) as RGab;
  pose proof (shw_bytes RNG off pp 8 pp 8 ltac:(lia) ltac:(lia) ltac:(lia) RGps) as RGpb;
  pose proof (shw_bytes RNG off pn 8 pn 8 ltac:(lia) ltac:(lia) ltac:(lia) RGns) as RGnb.
Ltac rngg NZh L50 :=
  let H := fresh "RGGh" in
  pose proof (RBG NZh L50) as H; unfold RGG in H;
  destruct H as (RGr & RGrs);
  pose proof (shw_bytes RNG off fr 50 fr 50 ltac:(lia) ltac:(lia) ltac:(lia) RGrs) as RGrb.

Lemma dj_of : all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (fr, fr + 50); (S - 4672, S)] ->
  DJA /\ DJB.
Proof.
  intros H. cbn [all_dj dj_from] in H.
  destruct H as ((Dfa & Dfp & Dfn & Dff & DfS & _) & (Dap & Dan & Daf & DaS & _) & (Dpn & Dpf & DpS & _) &
                 (Dnf & DnS & _) & (DrS & _) & _).
  split; [exact (conj Dff (conj DfS DrS))|].
  exact (conj Dfa (conj Dfp (conj Dfn (conj Dap (conj Dan (conj Dpn (conj DaS (conj DpS DnS)))))))).
Qed.

Lemma cl_nz : CL <> FgRefuse -> NZ.
Proof. intros H. unfold NZ. repeat split; intros E; apply H; apply rf_class_refuse; tauto. Qed.

Lemma cl_nn : NZ -> CL =
  if negb (fg_fr len g) then FgNone
  else if bat g 19 =? 1 then FgFirst
  else if negb (fg_keep st g) then FgDrop
  else if negb (fg_close st g) then FgJoin
  else FgClose.
Proof. intros (H1 & H2 & H3 & H4 & H5). apply rf_class_nn; assumption. Qed.

Lemma cl_k : NZ -> fg_fr len g = true -> bat g 19 <> 1 ->
  CL = if negb (fg_keep st g) then FgDrop else if fg_close st g then FgClose else FgJoin.
Proof.
  intros NZh FRT B19. rewrite (cl_nn NZh), FRT, (proj2 (Z.eqb_neq _ _) B19). cbn [negb].
  destruct (fg_keep st g), (fg_close st g); reflexivity.
Qed.

(* The runtime's cells and the shadow survive a run that writes only inside the window, or inside W5. *)
Lemma rt0 : forall mc, munch [(S - 4672, S)] mE mc -> wmono rsegs mE mc -> asan_cells mc /\ shadow_rw mc.
Proof.
  intros mc MU WM. split.
  - apply (fl_asan_cells _ mE mc HCE MU). intros x Hx. cbn [outside]. unfold RT_LO, RT_HI in Hx.
    split; [lia | exact I].
  - apply (fl_shadow_rw _ mE mc HSW MU WM). intros x Hx. cbn [outside]. split; [|exact I].
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hx. lia.
Qed.

Lemma so5 : NZ -> forall x, in_shadow x -> outside W5 x.
Proof.
  intros NZh. destruct (HAF NZh) as ((Af & Aa & Ap & An & _) & _).
  apply (fa_so5 mE f pa pp pn); try assumption; unfold HIGHMEM_BEG, APPMEM_END; lia.
Qed.

Lemma ro5 : NZ -> forall x, RT_LO <= x < RT_HI -> outside W5 x.
Proof.
  intros NZh. destruct (HAF NZh) as ((_ & _ & _ & _ & _ & DJ) & _).
  apply (fa_ro5 f pa pp pn (S - 4672) S); [unfold HIGHMEM_BEG; lia | exact DJ].
Qed.

Lemma rtW : forall W' mc, NZ -> munch W' mE mc -> sub_fp W' W5 -> wmono rsegs mE mc -> asan_cells mc /\ shadow_rw mc.
Proof.
  intros W' mc NZh MU Hs WM. split.
  - apply (fl_asan_cells W' mE mc HCE MU). intros x Hx. apply Hs. exact (ro5 NZh x Hx).
  - apply (fl_shadow_rw W' mE mc HSW MU WM). intros x Hx. apply Hs. exact (so5 NZh x Hx).
Qed.

Lemma rt_post : forall c m, c = CL -> munch (fg_fp 4672 f pa pp pn S c) mE m -> wmono rsegs mE m ->
  asan_cells m /\ shadow_rw m.
Proof.
  intros c m Hc MU WM.
  destruct c; cbn [fg_fp] in MU; try exact (rt0 m MU WM);
    (eapply (rtW _ m); [apply cl_nz; rewrite <- Hc; discriminate | exact MU
                      | unfold sub_fp, W5; cbn [outside]; intros; tauto | exact WM]).
Qed.

Lemma fa_fr_c8 : forall (mm : word -> option byte) (A : Z) v rest,
  rw_cells rsegs mm A (C8 v :: rest) -> rw_cells rsegs mm A (CB 8 (le8 v) :: rest).
Proof.
  intros mm A v rest [[Hwf Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf] in Hwf |- *. split; [rewrite length_le8; reflexivity | exact (proj2 Hwf)].
  - cbn [cells_bytes cbytes] in Hb |- *. exact Hb.
  - cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.

Lemma fa_sowf : NZ -> forall x, in_shadow x -> outside [(f, f + 72); (S - 4672, S)] x.
Proof. intros NZh x Hx. pose proof (so5 NZh x Hx) as H. unfold W5 in H. cbn [outside] in H |- *. tauto. Qed.
Lemma fa_rowf : NZ -> forall x, RT_LO <= x < RT_HI -> outside [(f, f + 72); (S - 4672, S)] x.
Proof. intros NZh x Hx. pose proof (ro5 NZh x Hx) as H. unfold W5 in H. cbn [outside] in H |- *. tauto. Qed.

(* A shadow byte read of the j-th byte (X = a + j) of an addressable range at the current memory m. *)
Lemma fa_rd1 : forall (m : word -> option byte) (W' : list (Z * Z)) (a n j X : Z),
  asan_shadow_rd rsegs mE off a n W5 -> asan_addressable rsegs mE off a n ->
  munch W' mE m -> sub_fp W' W5 -> 0 <= j < n -> X = a + j ->
  exists k : byte, ov_read_bytes rsegs m (wa (X / 8 + off)) 1 = Some [k]
    /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros m W' a n j X SR AD MU SUB Hj ->.
  pose proof (asan_shadow_rd_munch rsegs mE m off a n W5 W' SR MU SUB) as SR'.
  pose proof (asan_addressable_munch rsegs mE m off a n W5 W' AD SR MU SUB) as AD'.
  destruct (asan_shadow_read rsegs m off a n W5 j SR' Hj) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [exact (AD' j k Hj BK) | apply rc_byte_signed].
Qed.

Lemma fa_rdb : forall (m : word -> option byte) (W' : list (Z * Z)) (a n j X : Z),
  asan_shadow_rd rsegs mE off a n W5 -> asan_addressable rsegs mE off a n ->
  munch W' mE m -> sub_fp W' W5 -> 0 <= j < n -> X = a + j ->
  exists k : byte, ov_read_bytes rsegs m (wa (X / 8 + off)) 1 = Some [k]
    /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128
    /\ 0 <= X / 8 + off < 2^64.
Proof.
  intros m W' a n j X SR AD MU SUB Hj ->.
  pose proof (asan_shadow_rd_munch rsegs mE m off a n W5 W' SR MU SUB) as SR'.
  pose proof (asan_addressable_munch rsegs mE m off a n W5 W' AD SR MU SUB) as AD'.
  destruct (asan_shadow_read rsegs m off a n W5 j SR' Hj) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [exact (AD' j k Hj BK)|]. split; [apply rc_byte_signed|].
  destruct BK as (Hlo & Hhi & _). unfold asan_shadow in Hlo, Hhi. cbn [length] in Hhi. lia.
Qed.

Lemma fa_rd2 : forall (m : word -> option byte) (W' : list (Z * Z)) (a n j X : Z),
  asan_shadow_rd rsegs mE off a n W5 -> asan_addressable rsegs mE off a n ->
  munch W' mE m -> sub_fp W' W5 -> 0 <= j -> j + 2 <= n -> X = a + j -> X mod 8 + 2 <= 8 ->
  exists k : byte, ov_read_bytes rsegs m (wa (X / 8 + off)) 1 = Some [k]
    /\ (bv_signed k = 0 \/ X mod 8 + 1 < bv_signed k) /\ -128 <= bv_signed k < 128
    /\ 0 <= X / 8 + off < 2^64.
Proof.
  intros m W' a n j X SR AD MU SUB Hj Hjn -> Hm.
  pose proof (asan_shadow_rd_munch rsegs mE m off a n W5 W' SR MU SUB) as SR'.
  pose proof (asan_addressable_munch rsegs mE m off a n W5 W' AD SR MU SUB) as AD'.
  destruct (asan_shadow_read rsegs m off a n W5 j SR' ltac:(lia)) as (k & RK & BK).
  pose proof (asan_check_lt rsegs m off a n j 2 k AD' Hj ltac:(lia) Hjn ltac:(lia) BK) as OK.
  exists k. split; [exact RK|]. split; [destruct OK as [E|E]; [left; exact E | right; lia]|].
  split; [apply rc_byte_signed|].
  destruct BK as (Hlo & Hhi & _). unfold asan_shadow in Hlo, Hhi. cbn [length] in Hhi. lia.
Qed.

Lemma fa_rd8 : forall (m : word -> option byte) (W' : list (Z * Z)) (a n j X : Z),
  asan_shadow_rd rsegs mE off a n W5 -> asan_addressable rsegs mE off a n -> asan_rt3 rsegs mE off a n ->
  munch W' mE m -> sub_fp W' W5 -> 0 <= j -> j + 8 <= n -> X = a + j -> X mod 8 = 0 ->
  exists k : byte, ov_read_bytes rsegs m (wa (X / 8 + off)) 1 = Some [k] /\ bv_unsigned k = 0
    /\ 0 <= X / 8 + off < 2^64.
Proof.
  intros m W' a n j X SR AD R3 MU SUB Hj Hjn -> Hm.
  pose proof (asan_shadow_rd_munch rsegs mE m off a n W5 W' SR MU SUB) as SR'.
  pose proof (asan_addressable_munch rsegs mE m off a n W5 W' AD SR MU SUB) as AD'.
  pose proof (asan_rt3_munch rsegs mE m off a n W5 W' R3 SR MU SUB) as R3'.
  destruct (asan_shadow_read rsegs m off a n W5 j SR' ltac:(lia)) as (k & RK & BK).
  pose proof (asan_check_8 rsegs m off a n j k AD' R3' Hj Hjn Hm BK) as K0.
  exists k. split; [exact RK|]. split; [exact (rc_signed0_unsigned0 k K0)|].
  destruct BK as (Hlo & Hhi & _). unfold asan_shadow in Hlo, Hhi. cbn [length] in Hhi. lia.
Qed.

Lemma fa_rd1m : forall (m : word -> option byte) (a n j X : Z) (W : list (Z * Z)),
  asan_shadow_rd rsegs m off a n W -> asan_addressable rsegs m off a n -> 0 <= j < n -> X = a + j ->
  exists k : byte, ov_read_bytes rsegs m (wa (X / 8 + off)) 1 = Some [k]
    /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros m a n j X W SR AD Hj ->.
  destruct (asan_shadow_read rsegs m off a n W j SR Hj) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [exact (AD j k Hj BK) | apply rc_byte_signed].
Qed.

Lemma fa_sr_sub : forall (m : word -> option byte) (off' a n k n' : Z) (W : list (Z * Z)),
  asan_shadow_rd rsegs m off' a n W -> 0 <= k -> 0 <= n' -> k + n' <= n ->
  asan_shadow_rd rsegs m off' (a + k) n' W.
Proof.
  intros m off' a n k n' W SR Hk Hn' Hkn i Hi.
  replace (a + k + i) with (a + (k + i)) by lia. apply SR. lia.
Qed.

Lemma fa_ad_sub : forall (m : word -> option byte) (off' a n k n' : Z),
  asan_addressable rsegs m off' a n -> 0 <= k -> 0 <= n' -> k + n' <= n ->
  asan_addressable rsegs m off' (a + k) n'.
Proof.
  intros m off' a n k n' AD Hk Hn' Hkn i ki Hi HB.
  replace (a + k + i) with (a + (k + i)) in HB by lia.
  replace (a + k + i) with (a + (k + i)) by lia. apply (AD (k + i) ki); [lia | exact HB].
Qed.

Ltac fa_sub := unfold sub_fp, W5; intro; cbn [outside]; tauto.

Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.
Ltac steps_to P :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 P) _ _ _ _) => idtac
  | _ => step; steps_to P
  end.

Ltac chk1 X r SH :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  step; rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
  step; step; clear RK; step;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
  lazymatch goal with
  | |- evtF ?segs ?RN ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RN Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7; step;
          rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
          replace (X mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia);
          bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac chk1p X r SH :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in let HB := fresh "HB" in
  destruct SH as (k & RK & OK & KR & HB);
  step; clear RK; step;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
  lazymatch goal with
  | |- evtF ?segs ?RN ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RN Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7; step;
          rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
          replace (X mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia);
          bjoin G r ]
      | intros ?; simp_regs; clear OK KR HB ]
  end.

Ltac chk_if X r k OK :=
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
  lazymatch goal with
  | |- evtF ?segs ?RN ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RN Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7; step;
          rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
          replace (X mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia);
          bjoin G r ]
      | intros ?; simp_regs ]
  end.

Ltac chk_if2 X r k OK :=
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
  lazymatch goal with
  | |- evtF ?segs ?RN ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RN Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7;
          step; rewrite ?(unsigned_lit (X mod 8)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
          step;
          rewrite (rc_lts_signed (X mod 8 + 1) (bv_signed k)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
          replace (X mod 8 + 1 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia);
          bjoin G r ]
      | intros ?; simp_regs ]
  end.

(* +0x238 .. the epilogue (0x85c1c). *)
Lemma L_epi : forall c j (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                         x28 x29 x30 x31 : word) m,
  c = CL -> x10 = Z_to_bv 64 (fg_ret c) ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch (fg_fp 4672 f pa pp pn S c) mE m -> wmono rsegs mE m ->
  mem_inv rsegs m -> fg_mem f pa pp pn st g c m ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
             x24 x25 x26 x27 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85c1c) fc None m (seg_rom rsegs)).
Proof.
  intros c j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m
    Hc Hx FR ST MU WM MI FM.
  destruct (rt_post c m Hc MU WM) as [AC SR].
  subst c x10.
  pose proof (stk_release rsegs m _ _ _ ST FR ltac:(lia)) as ST'.
  cbn [cells_size csize Nat.add] in ST'. replace (S + -112 + Z.of_nat 112) with S in ST' by lia. clear ST.
  do 15 step.
  try replace (S + -112 + 112) with S by lia.
  apply evtF_done. unfold Qf.
  do 14 eexists. exists m. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact FM|].
  split; [exact AC | exact SR].
Qed.

Lemma L_ret0 : forall c j (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                          x28 x29 x30 x31 : word) m,
  c = CL -> fg_ret c = 0 ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch (fg_fp 4672 f pa pp pn S c) mE m -> wmono rsegs mE m ->
  mem_inv rsegs m -> fg_mem f pa pp pn st g c m ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
             x24 x25 x26 x27 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85c18) fc None m (seg_rom rsegs)).
Proof.
  intros c j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m
    Hc Hr FR ST MU WM MI FM.
  step.
  eapply L_epi; [exact Hc | | exact FR | exact ST | exact MU | exact WM | exact MI | exact FM].
  rewrite Hr. reflexivity.
Qed.

Lemma L_none : forall j (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                        x28 x29 x30 x31 : word) m,
  NZ -> fg_fr len g = false ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
             x24 x25 x26 x27 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85c18) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m
    NZh HF FR ST MU WM MI.
  eapply (L_ret0 FgNone); [ | reflexivity | exact FR | exact ST | exact MU | exact WM | exact MI | exact I].
  rewrite (cl_nn NZh), HF. reflexivity.
Qed.

Ltac rfail := eapply (L_epi FgRefuse);
  [ symmetry; apply rf_class_refuse; tauto | reflexivity
  | eassumption | eassumption | solve [cbn [fg_fp]; eassumption]
  | eassumption | eassumption | exact I ].

Ltac nfail := eapply L_none;
  [ eassumption
  | let EF := fresh "EF" in destruct (fg_fr len g) eqn:EF; [exfalso; apply fr_iff in EF; lia | reflexivity]
  | eassumption | eassumption | eassumption | eassumption | eassumption ].

Ltac gld i :=
  let R := fresh "RDG" in
  match goal with HG : bytes_at _ _ fr g |- _ => pose proof (rd_byte rsegs _ fr g i HG ltac:(rewrite Hg; lia)) as R end;
  step; clear R.

Ltac gchk i z c :=
  rewrite (rf_beq (nth i g (Z_to_bv 8 0)) c) by lia;
  change (bv_unsigned (nth i g (Z_to_bv 8 0))) with (bat g z);
  let B := fresh "B" in destruct (Z.eqb_spec (bat g z) c) as [B|B]; cbn [negb]; cbv iota; [|nfail].

Ltac ubn c := step; step; rewrite (u_ltu_negl (fr + 18) c) by lia; cbv iota.

Ltac gshk Psrli i r :=
  steps_to Psrli;
  match goal with SRg : asan_shadow_rd rsegs mE off fr 50 W5, ADg : asan_addressable rsegs mE off fr 50,
    MU : munch [(S - 4672, S)] mE ?mm |- _ =>
      chk1 (fr + i) r (fa_rd1 mm [(S - 4672, S)] fr 50 i (fr + i) SRg ADg MU ltac:(fa_sub) ltac:(lia) eq_refl)
  end.

(* 0x85bd4 .. 0x85c10: the block-sum loop over fr + 18 .. fr + 50, each load shadow-checked. *)
Lemma loopB : forall (Q : machine_state -> Prop)
  (r1 r5 r6 r7 r11 s7v r28 r29 r30 r31 : word)
  (m : word -> option byte) (A : Z) (bs : list byte) (c : nat) (W : list (Z * Z)),
  bytes_at rsegs m A bs -> (c <= length bs)%nat -> 0 < A -> A + Z.of_nat c <= 2 ^ 64 ->
  asan_shadow_rd rsegs m off A (Z.of_nat c) W -> asan_addressable rsegs m off A (Z.of_nat c) ->
  rng RNG A (Z.of_nat c) -> rng RNG (A / 8 + off) ((A + Z.of_nat c - 1) / 8 - A / 8 + 1) ->
  (forall y0 y3 y5 y6 y7 : word, evtF rsegs RNG Q
     (MS (mkR r1 (Z_to_bv 64 (S + -112)) gp tp r5 r6 r7 (Z_to_bv 64 f) (Z_to_bv 64 pn) y0 r11
              (Z_to_bv 64 (psum bs c)) y3 (Z_to_bv 64 (A + Z.of_nat c)) y5 y6 y7 (Z_to_bv 64 pp) (Z_to_bv 64 pa)
              (Z_to_bv 64 fr) s5 (Z_to_bv 64 (fr + 18)) s7v s8 (Z_to_bv 64 off) s10 s11 r28 r29 r30 r31)
         Ff (Z_to_bv 64 0x85c10) fc None m (seg_rom rsegs))) ->
  forall n i (a0v a2v a3v a4v a5v a6v a7v : word), (i + n = c)%nat -> (0 < n)%nat ->
  a0v = Z_to_bv 64 (A + Z.of_nat i) -> a4v = Z_to_bv 64 (A + Z.of_nat i) ->
  a2v = Z_to_bv 64 (psum bs i) -> bv_unsigned a3v = Z.of_nat n ->
  evtF rsegs RNG Q
    (MS (mkR r1 (Z_to_bv 64 (S + -112)) gp tp r5 r6 r7 (Z_to_bv 64 f) (Z_to_bv 64 pn) a0v r11 a2v a3v a4v a5v a6v a7v
             (Z_to_bv 64 pp) (Z_to_bv 64 pa) (Z_to_bv 64 fr) s5 (Z_to_bv 64 (fr + 18)) s7v s8 (Z_to_bv 64 off)
             s10 s11 r28 r29 r30 r31)
        Ff (Z_to_bv 64 0x85bd4) fc None m (seg_rom rsegs)).
Proof.
  intros Q r1 r5 r6 r7 r11 s7v r28 r29 r30 r31 m A bs c W HB Hc HA HAc SR AD RDAT RSH HK.
  induction n as [|n IH]; intros i a0v a2v a3v a4v a5v a6v a7v Hin Hn E0 E4 E2 H3; [lia|].
  subst a0v a4v a2v.
  pose proof (rd_byte rsegs m A bs i HB ltac:(lia)) as RD.
  pose proof (psum_range bs i) as PR.
  step. rewrite (rc_beq0_false (A + Z.of_nat i)) by lia. cbv iota.
  chk1 (A + Z.of_nat i) (Z_to_bv 5 16)
    (fa_rd1m m A (Z.of_nat c) (Z.of_nat i) (A + Z.of_nat i) W SR AD ltac:(lia) eq_refl).
  step. step. step. step.
  rewrite psum_S_zxb.
  step. step.
  rewrite (rc_eqb0 (bv_unsigned a3v + -1)) by lia.
  destruct n as [|n].
  - replace (bv_unsigned a3v + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
    step.
    replace (A + Z.of_nat i + 1) with (A + Z.of_nat c) by lia.
    replace (Datatypes.S i) with c by lia. apply HK.
  - replace (bv_unsigned a3v + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
    apply (IH (Datatypes.S i)); first [lia | f_equal; lia | rewrite unsigned_lit by lia; lia].
Qed.

(* 0x85c60 .. 0x85cc0: the first-record path (two copies, store n and 1, return 0). *)
Lemma L_first : forall c j (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
  c = CL -> c = FgFirst -> 1 <= fg_n g <= 22 -> DJA ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  rw_cells rsegs m f [CB 72 st] -> bytes_at rsegs m fr g ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 pp) (Z_to_bv 64 pa) (Z_to_bv 64 fr) s5 (Z_to_bv 64 (fr + 18)) (zxb (nth 26 g (Z_to_bv 8 0)))
             s8 (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85c60) fc None m (seg_rom rsegs)).
Proof.
  intros c j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
    Hc HcF Hn DJAh FR ST MU WM MI HS HG.
  assert (NZh : NZ) by (apply cl_nz; rewrite <- Hc, HcF; discriminate).
  assert (FRT : fg_fr len g = true).
  { destruct (fg_fr len g) eqn:E; [reflexivity|].
    assert (HN : CL = FgNone) by (rewrite (cl_nn NZh), E; reflexivity).
    rewrite Hc in HcF. rewrite HN in HcF. discriminate HcF. }
  pose proof (proj1 (proj1 (fr_iff len g) FRT)) as Hlen50.
  destruct (HAF NZh) as ((Af & Aa & Ap & An & Happ & DJrt) & SRf & ADf & _).
  destruct (HAG NZh Hlen50) as (Ag & SRg & ADg).
  rngf NZh. rngg NZh Hlen50.
  pose proof (rt_addressable_bound mE f 72 Af) as (Hf0 & _ & Hf2).
  pose proof (rt_addressable_bound mE fr 50 Ag) as (Hr0 & _ & Hr2).
  destruct DJAh as (Dff & DfS & DrS).
  destruct (rf_rw_parts rsegs m f 72 st HS) as (HSb & HSw & HSl). clear HS.
  rewrite <- Hst in HSw.
  pose proof (rf_rw_sub rsegs m f st 0 6 HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as P0.
  pose proof (rf_rw_sub rsegs m f st 6 2 HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as P6.
  pose proof (rf_rw_sub rsegs m f st 8 (fg_n g) HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as P8.
  pose proof (rf_bytes_skip rsegs m f st (8 + fg_n g) HSb ltac:(rewrite Hst; lia)) as PR.
  clear HSb.
  rewrite Z.add_0_r in P0. change (Z.to_nat 6) with 6%nat in P0. change (Z.to_nat 2) with 2%nat in P6.
  pose proof (rf_bytes_bsl rsegs m fr g 6 6 HG ltac:(lia) ltac:(lia) ltac:(rewrite Hg; lia)) as GS.
  pose proof (rf_bytes_bsl rsegs m fr g 27 (fg_n g) HG ltac:(lia) ltac:(lia) ltac:(rewrite Hg; lia)) as GB.
  clear HG.
  apply (munch_weaken [(S - 4672, S)] [(f, f + 72); (S - 4672, S)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m f 72 Af MU (fa_sowf NZh)) as ADfm.
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m fr 50 Ag MU (fa_sowf NZh)) as ADgm.
  pose proof (rtW [(f, f + 72); (S - 4672, S)] m NZh MU ltac:(fa_sub) WM) as (ACm & SRm).
  (* the shared statement, with its shadow word spans (sh_word_rng of rng_asan.v) written out *)
  pose proof MCPY as HM. unfold asan_memcpy_contract_F, sh_word_rng, sh_al8_lo, sh_al8_hi in HM. cbv zeta in HM.
  step. step. step. step.
  assert (U0 : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 (fr + 6)) = fr + 6) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  assert (U3 : bv_unsigned (Z_to_bv 64 (S + -112)) = S + -112) by (apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HM with (src := bsl g 6 6) (junk := bsl st 0 6) (lo := S - 4672).
    - rewrite U1. exact GS.
    - rewrite U2. apply rf_bsl_length; rewrite ?Hg; lia.
    - rewrite U0, U2. exact P0.
    - rewrite U0, U1, U2. destruct Dff as [H|H]; [right; right; lia | right; left; lia].
    - rewrite U2. lia.
    - rewrite U1, U2. apply (fa_addr_sub m fr 50); [exact ADgm | lia | lia | lia].
    - rewrite U0, U2. apply (fa_addr_sub m f 72); [exact ADfm | lia | lia | lia].
    - rewrite U1, U2. unfold end_in_app. right. replace (fr + 6 + 6) with (fr + 12) by lia.
      apply (fa_addr_app m fr 50 12); [exact ADgm | lia].
    - rewrite U0, U2. unfold end_in_app. right. apply (fa_addr_app m f 72 6); [exact ADfm | lia].
    - rewrite U0, U1, U2. right. split;
        [replace (fr + 6 + 7) with (fr + 13) by lia; apply (fa_addr_app m fr 50 13); [exact ADgm | lia]
        | apply (fa_addr_app m f 72 7); [exact ADfm | lia]].
    - rewrite U0, U2. cbn [dj_from] in DJrt. destruct DJrt as [[H|H] _]; [right; lia | left; lia].
    - rewrite U0, U2, U3. unfold ASAN_MEMCPY_K. destruct DfS as [H|H]; [left; lia | right; lia].
    - rewrite U1, U2, U3. unfold ASAN_MEMCPY_K. destruct DrS as [H|H]; [left; lia | right; lia].
    - rewrite U3. exact ST.
    - rewrite U3. unfold ASAN_MEMCPY_K. lia.
    - unfold HIGHMEM_BEG. lia.
    - rewrite U3. unfold APPMEM_END. lia.
    - exact ACm.
    - exact SRm.
    - exact MI.
    - exact RBY.
    - exact RIMG.
    - rewrite U3. unfold ASAN_MEMCPY_K. apply (rng_sub' RNG (S - 4672) 4672); [exact RSTK | lia].
    - rewrite U0, U2. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - rewrite U1, U2. apply (rng_sub' RNG fr 50); [exact RGr | lia].
    - rewrite U0, U2. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off f 72 f 6 ltac:(lia) ltac:(lia) ltac:(lia) RGfs).
    - rewrite U1, U2. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off fr 50 (fr + 6) 6 ltac:(lia) ltac:(lia) ltac:(lia) RGrs).
    - rewrite U3. unfold ASAN_MEMCPY_K. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off (S - 4672) 4672 (S + -112 - 2224) 2224 ltac:(lia) ltac:(lia) ltac:(lia) RSTKS). }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                  & E & MU2 & WM2 & MI2 & ST2 & RW2 & BD2 & AC2 & SR2).
  subst ms'. clear BD2.
  rewrite U0, U2 in RW2. rewrite U0, U2, U3 in MU2. rewrite U3 in ST2.
  assert (SUB1 : sub_fp [(f, f + 6); (S + -112 - 2224, S + -112)] [(f, f + 72); (S - 4672, S)])
    by (intros x; cbn [outside]; intros (H1 & H2 & _); split; [lia | split; [lia | exact I]]).
  pose proof (munch_trans [(f, f + 72); (S - 4672, S)] mE m m2 MU (munch_weaken _ _ m m2 SUB1 MU2)) as MU3.
  pose proof (wmono_trans rsegs mE m m2 WM WM2) as WM3.
  pose proof (rw_cells_transport rsegs [(f, f + 6); (S + -112 - 2224, S + -112)] m m2 (f + 6) [CB 2 (bsl st 6 2)]
                P6 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as P6'.
  pose proof (rw_cells_transport rsegs [(f, f + 6); (S + -112 - 2224, S + -112)] m m2 (f + 8)
                [CB (Z.to_nat (fg_n g)) (bsl st 8 (fg_n g))] P8 MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as P8'.
  pose proof (bytes_at_transport rsegs [(f, f + 6); (S + -112 - 2224, S + -112)] m m2 (f + (8 + fg_n g))
                (skipn (Z.to_nat (8 + fg_n g)) st) PR MU2
                ltac:(cbn [disjoint_from]; rewrite length_skipn, Hst; repeat split; try exact I; lia)) as PR'.
  pose proof (bytes_at_transport rsegs [(f, f + 6); (S + -112 - 2224, S + -112)] m m2 (fr + 27) (bsl g 27 (fg_n g))
                GB MU2 ltac:(cbn [disjoint_from]; rewrite (rf_bsl_length g 27 (fg_n g)) by (rewrite ?Hg; lia);
                             repeat split; try exact I; lia)) as GB'.
  pose proof (rw_cells_transport rsegs [(f, f + 6); (S + -112 - 2224, S + -112)] m m2 (S + -112) (FRc j) FR MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FR2.
  replace (Z.of_nat (length st)) with 72 in HSw by (rewrite Hst; reflexivity).
  pose proof (wr_at_transport rsegs m m2 f 72 HSw WM2) as WRm2.
  replace (ret_pc (Z_to_bv 64 0x85c70)) with (Z_to_bv 64 0x85c70)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m2 f 72 Af MU3 (fa_sowf NZh)) as ADfm2.
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m2 fr 50 Ag MU3 (fa_sowf NZh)) as ADgm2.
  step. step. rewrite (u_ltu_negl (fr + 18) (-10)) by lia. cbv iota.
  step. step. step. step.
  assert (U4 : bv_unsigned (zxb (nth 26 g (Z_to_bv 8 0))) = fg_n g) by (exact (rf_zxb_u _)).
  assert (U5 : bv_unsigned (Z_to_bv 64 (f + 8)) = f + 8) by (apply unsigned_lit; lia).
  assert (U6 : bv_unsigned (Z_to_bv 64 (fr + 27)) = fr + 27) by (apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HM with (src := bsl g 27 (fg_n g)) (junk := bsl st 8 (fg_n g)) (lo := S - 4672).
    - rewrite U6. exact GB'.
    - rewrite U4. apply rf_bsl_length; rewrite ?Hg; lia.
    - rewrite U5, U4. exact P8'.
    - rewrite U5, U6, U4. destruct Dff as [H|H]; [right; right; lia | right; left; lia].
    - rewrite U4. lia.
    - rewrite U6, U4. apply (fa_addr_sub m2 fr 50); [exact ADgm2 | lia | lia | lia].
    - rewrite U5, U4. apply (fa_addr_sub m2 f 72); [exact ADfm2 | lia | lia | lia].
    - rewrite U6, U4. unfold end_in_app. right. replace (fr + 27 + fg_n g) with (fr + (27 + fg_n g)) by lia.
      apply (fa_addr_app m2 fr 50 (27 + fg_n g)); [exact ADgm2 | lia].
    - rewrite U5, U4. unfold end_in_app. right. replace (f + 8 + fg_n g) with (f + (8 + fg_n g)) by lia.
      apply (fa_addr_app m2 f 72 (8 + fg_n g)); [exact ADfm2 | lia].
    - rewrite U5, U6, U4. right. split;
        [replace (fr + 27 + 7) with (fr + 34) by lia; apply (fa_addr_app m2 fr 50 34); [exact ADgm2 | lia]
        | replace (f + 8 + 7) with (f + 15) by lia; apply (fa_addr_app m2 f 72 15); [exact ADfm2 | lia]].
    - rewrite U5, U4. cbn [dj_from] in DJrt. destruct DJrt as [[H|H] _]; [right; lia | left; lia].
    - rewrite U5, U4, U3. unfold ASAN_MEMCPY_K. destruct DfS as [H|H]; [left; lia | right; lia].
    - rewrite U6, U4, U3. unfold ASAN_MEMCPY_K. destruct DrS as [H|H]; [left; lia | right; lia].
    - rewrite U3. exact ST2.
    - rewrite U3. unfold ASAN_MEMCPY_K. lia.
    - unfold HIGHMEM_BEG. lia.
    - rewrite U3. unfold APPMEM_END. lia.
    - exact AC2.
    - exact SR2.
    - exact MI2.
    - exact RBY.
    - exact RIMG.
    - rewrite U3. unfold ASAN_MEMCPY_K. apply (rng_sub' RNG (S - 4672) 4672); [exact RSTK | lia].
    - rewrite U5, U4. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - rewrite U6, U4. apply (rng_sub' RNG fr 50); [exact RGr | lia].
    - rewrite U5, U4. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off f 72 (f + 8) (fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) RGfs).
    - rewrite U6, U4. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off fr 50 (fr + 27) (fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) RGrs).
    - rewrite U3. unfold ASAN_MEMCPY_K. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off (S - 4672) 4672 (S + -112 - 2224) 2224 ltac:(lia) ltac:(lia) ltac:(lia) RSTKS). }
  intros ms'' PO2.
  destruct PO2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m3
                  & E2 & MU4 & WM4 & MI4 & ST4 & RW4 & BD4 & AC4 & SR4).
  subst ms''. clear BD4.
  rewrite U5, U4 in RW4. rewrite U5, U4, U3 in MU4. rewrite U3 in ST4.
  replace (ret_pc (Z_to_bv 64 0x85c88)) with (Z_to_bv 64 0x85c88)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (SUB2 : sub_fp [(f + 8, f + 8 + fg_n g); (S + -112 - 2224, S + -112)] [(f, f + 72); (S - 4672, S)])
    by (intros x; cbn [outside]; intros (H1 & H2 & _); split; [lia | split; [lia | exact I]]).
  pose proof (munch_trans [(f, f + 72); (S - 4672, S)] mE m2 m3 MU3 (munch_weaken _ _ m2 m3 SUB2 MU4)) as MU5.
  pose proof (wmono_trans rsegs mE m2 m3 WM3 WM4) as WMm3.
  pose proof (wr_at_transport rsegs m2 m3 f 72 WRm2 WM4) as WRm3.
  pose proof (proj1 (rf_rw_parts rsegs m2 f 6 (bsl g 6 6) RW2)) as B0m2.
  pose proof (bytes_at_transport rsegs [(f + 8, f + 8 + fg_n g); (S + -112 - 2224, S + -112)] m2 m3 f (bsl g 6 6)
                B0m2 MU4 ltac:(cbn [disjoint_from]; rewrite rf_bsl_length by (rewrite ?Hg; lia);
                               repeat split; try exact I; lia)) as B0.
  pose proof (proj1 (rf_rw_parts rsegs m3 (f + 8) (Z.to_nat (fg_n g)) (bsl g 27 (fg_n g)) RW4)) as B8.
  pose proof (bytes_at_transport rsegs [(f + 8, f + 8 + fg_n g); (S + -112 - 2224, S + -112)] m2 m3 (f + (8 + fg_n g))
                (skipn (Z.to_nat (8 + fg_n g)) st) PR' MU4
                ltac:(cbn [disjoint_from]; rewrite length_skipn, Hst; repeat split; try exact I; lia)) as BR.
  pose proof (rw_cells_transport rsegs [(f + 8, f + 8 + fg_n g); (S + -112 - 2224, S + -112)] m2 m3 (S + -112) (FRc j)
                FR2 MU4 WM4 ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FR3.
  clear RW4 PR' RW2 P6 P6' P8 P8' PR GS GB GB' B0m2 WRm2 MU MU2 MU3 MU4 WM WM2 WM3 WM4 MI MI2 ST ST2
    ADfm ADgm ADfm2 ADgm2 ACm SRm AC2 SR2 FR FR2.
  step.
  chk1 (f + 7) (Z_to_bv 5 12)
    (fa_rd1 m3 [(f, f + 72); (S - 4672, S)] f 72 7 (f + 7) SRf ADf MU5 ltac:(fa_sub) ltac:(lia) eq_refl).
  pose proof (wr_at_store_ok rsegs m3 f 72 7 1%nat WRm3 ltac:(lia) ltac:(lia)) as SO7.
  step.
  change (Z_to_bv 64 (f + 7)) with (wa (f + 7)).
  pose proof (bytes_at_write_same rsegs m3 (f + 7) [nth 26 g (Z_to_bv 8 0)] ltac:(lia)
                ltac:(cbn [length]; lia)) as B7n.
  pose proof (bytes_at_write_other rsegs m3 (f + 7) [nth 26 g (Z_to_bv 8 0)] f (bsl g 6 6) B0 ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(rewrite rf_bsl_length by (rewrite ?Hg; lia); lia)) as B0a.
  pose proof (bytes_at_write_other rsegs m3 (f + 7) [nth 26 g (Z_to_bv 8 0)] (f + 8) (bsl g 27 (fg_n g)) B8
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as B8a.
  pose proof (bytes_at_write_other rsegs m3 (f + 7) [nth 26 g (Z_to_bv 8 0)] (f + (8 + fg_n g))
                (skipn (Z.to_nat (8 + fg_n g)) st) BR ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia))
    as BRa.
  pose proof (rw_cells_frame rsegs m3 (S + -112) (FRc j) (f + 7) [nth 26 g (Z_to_bv 8 0)] FR3 ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(cbn [cells_size csize Nat.add length]; lia)) as FR3a.
  pose proof (mem_inv_store rsegs m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)] MI4 ltac:(cbn [length]; exact SO7)) as MI4a.
  pose proof (stk_write rsegs m3 (S - 4672) (S + -112) (f + 7) [nth 26 g (Z_to_bv 8 0)] ST4 ltac:(lia)
                ltac:(cbn [length]; lia)) as ST4a.
  apply (munch_write [(f, f + 72); (S - 4672, S)] mE m3 (f + 7) [nth 26 g (Z_to_bv 8 0)]) in MU5;
    [| lia | cbn [length]; lia | cbn [inside length]; lia].
  apply (wmono_write rsegs mE m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)]) in WMm3.
  pose proof (wr_at_transport rsegs m3 (write_to_mem m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)]) f 72 WRm3
                (wmono_write rsegs m3 m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)] (wmono_refl rsegs m3))) as WRm4.
  set (m4 := write_to_mem m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)]) in *. clearbody m4.
  step.
  chk1 (f + 6) (Z_to_bv 5 11)
    (fa_rd1 m4 [(f, f + 72); (S - 4672, S)] f 72 6 (f + 6) SRf ADf MU5 ltac:(fa_sub) ltac:(lia) eq_refl).
  step. step.
  pose proof (wr_at_store_ok rsegs m4 f 72 6 1%nat WRm4 ltac:(lia) ltac:(lia)) as SO6.
  step.
  change (Z_to_bv 64 (f + 6)) with (wa (f + 6)).
  pose proof (bytes_at_write_same rsegs m4 (f + 6) [Z_to_bv 8 1] ltac:(lia) ltac:(cbn [length]; lia)) as B6_1.
  pose proof (bytes_at_write_other rsegs m4 (f + 6) [Z_to_bv 8 1] f (bsl g 6 6) B0a ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(rewrite rf_bsl_length by (rewrite ?Hg; lia); lia)) as B0b.
  pose proof (bytes_at_write_other rsegs m4 (f + 6) [Z_to_bv 8 1] (f + 7) [nth 26 g (Z_to_bv 8 0)] B7n ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as B7nb.
  pose proof (bytes_at_write_other rsegs m4 (f + 6) [Z_to_bv 8 1] (f + 8) (bsl g 27 (fg_n g)) B8a ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as B8b.
  pose proof (bytes_at_write_other rsegs m4 (f + 6) [Z_to_bv 8 1] (f + (8 + fg_n g))
                (skipn (Z.to_nat (8 + fg_n g)) st) BRa ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia))
    as BRb.
  pose proof (rw_cells_frame rsegs m4 (S + -112) (FRc j) (f + 6) [Z_to_bv 8 1] FR3a ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(cbn [cells_size csize Nat.add length]; lia)) as FR3b.
  pose proof (mem_inv_store rsegs m4 (wa (f + 6)) [Z_to_bv 8 1] MI4a ltac:(cbn [length]; exact SO6)) as MI4b.
  pose proof (stk_write rsegs m4 (S - 4672) (S + -112) (f + 6) [Z_to_bv 8 1] ST4a ltac:(lia)
                ltac:(cbn [length]; lia)) as ST4b.
  apply (munch_write [(f, f + 72); (S - 4672, S)] mE m4 (f + 6) [Z_to_bv 8 1]) in MU5;
    [| lia | cbn [length]; lia | cbn [inside length]; lia].
  apply (wmono_write rsegs mE m4 (wa (f + 6)) [Z_to_bv 8 1]) in WMm3.
  set (m5 := write_to_mem m4 (wa (f + 6)) [Z_to_bv 8 1]) in *. clearbody m5.
  step.
  eapply (L_epi FgFirst); [ rewrite <- HcF; exact Hc | reflexivity | exact FR3b | exact ST4b | exact MU5
    | exact WMm3 | exact MI4b | ].
  cbn [fg_mem]. unfold fg_first, fg_body.
  apply (rf_app rsegs m5 f (bsl g 6 6) (f + 6)
    ([Z_to_bv 8 1; nth 26 g (Z_to_bv 8 0)] ++ bsl g 27 (fg_n g) ++ skipn (Z.to_nat (8 + fg_n g)) st));
    [ exact B0b | | rewrite rf_bsl_length by (rewrite ?Hg; lia); reflexivity ].
  apply (rf_app rsegs m5 (f + 6) [Z_to_bv 8 1] (f + 7)
    ([nth 26 g (Z_to_bv 8 0)] ++ bsl g 27 (fg_n g) ++ skipn (Z.to_nat (8 + fg_n g)) st));
    [ exact B6_1 | | cbn [length]; lia ].
  apply (rf_app rsegs m5 (f + 7) [nth 26 g (Z_to_bv 8 0)] (f + 8)
    (bsl g 27 (fg_n g) ++ skipn (Z.to_nat (8 + fg_n g)) st));
    [ exact B7nb | | cbn [length]; lia ].
  apply (rf_app rsegs m5 (f + 8) (bsl g 27 (fg_n g)) (f + (8 + fg_n g)) (skipn (Z.to_nat (8 + fg_n g)) st));
    [ exact B8b | exact BRb | rewrite rf_bsl_length by (rewrite ?Hg; lia); lia ].
Qed.

(* 0x85d18 .. 0x85d28: the drop path (store 0 at f + 6, return 0). *)
Lemma L_drop : forall c j (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26
                        x28 x29 x30 x31 : word) m,
  c = CL -> c = FgDrop -> (f + 72 <= S - 4672 \/ S <= f) ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(f, f + 72); (S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  rw_cells rsegs m f [CB 72 st] ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             x21 x22 x23 (Z_to_bv 64 (f + 6)) x25 x26 (Z_to_bv 64 ((f + 6) / 8 + off)) x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85d18) fc None m (seg_rom rsegs)).
Proof.
  intros c j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 m
    Hc HcD DfS FR ST MU WM MI HS.
  assert (NZh : NZ) by (apply cl_nz; rewrite <- Hc, HcD; discriminate).
  destruct (HAF NZh) as ((Af & _) & SRf & ADf & _).
  rngf NZh.
  pose proof (rt_addressable_bound mE f 72 Af) as (Hf0 & _ & Hf2).
  chk1p (f + 6) (Z_to_bv 5 11)
    (fa_rdb m [(f, f + 72); (S - 4672, S)] f 72 6 (f + 6) SRf ADf MU ltac:(fa_sub) ltac:(lia) eq_refl).
  step. step. step.
  eapply (L_epi FgDrop); [ rewrite <- HcD; exact Hc | reflexivity | exact FR | exact ST | exact MU | exact WM
    | exact MI | ].
  cbn [fg_mem]. eapply fa_rw_bytes; [exact HS|]. cbn [cells_bytes cbytes]. rewrite ?app_nil_r. reflexivity.
Qed.

Ltac ubs c := step; step; rewrite (u_ltu_negl (f + 8) c) by lia; cbv iota.

(* 0x85ed0 .. 0x85f80: the close path (byte 17 checked, pa/pp/pn each checked and stored, return 1). *)
Lemma L_close : forall c (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x27 x28 x29 x30 x31 : word) m,
  c = CL -> c = FgClose -> 14 <= fg_T st g <= 64 -> length (fg_join st g) = 72%nat -> DJB ->
  rw_cells rsegs m (S + -112) (FRc Jc) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(f, f + 72); (S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  bytes_at rsegs m f (fg_clear (fg_join st g)) -> OUT ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 pp) (Z_to_bv 64 pa) x20 (Z_to_bv 64 (f + 8)) x22 x23 x24 (Z_to_bv 64 off)
             (Z_to_bv 64 (fg_T st g)) x27 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85ed0) fc None m (seg_rom rsegs)).
Proof.
  intros c x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x27 x28 x29 x30 x31 m
    Hc HcC HT LJ DJBh FR ST MU WM MI CJ OUTh.
  pose proof OUTh as (WA & WP & WN & Ma & Mp & Mn). clear OUTh.
  assert (NZh : NZ) by (apply cl_nz; rewrite <- Hc, HcC; discriminate).
  destruct (HAF NZh) as ((Af & Aa & Ap & An & Happ & DJrt) &
                         SRf & ADf & SRa & ADa & SRp & ADp & R3p & SRn & ADn & R3n).
  rngf NZh.
  clear Happ DJrt.
  pose proof (rt_addressable_bound mE f 72 Af) as (Hf0 & _ & Hf2).
  pose proof (rt_addressable_bound mE pa 2 Aa) as (Hpa0 & _ & Hpa2).
  pose proof (rt_addressable_bound mE pp 8 Ap) as (Hpp0 & _ & Hpp2).
  pose proof (rt_addressable_bound mE pn 8 An) as (Hpn0 & _ & Hpn2).
  clear Af Aa Ap An.
  destruct DJBh as (Dfa & Dfp & Dfn & Dap & Dan & Dpn & DaS & DpS & DnS).
  apply hide_i in Dfa; apply hide_i in Dfp; apply hide_i in Dfn; apply hide_i in Dap; apply hide_i in Dan;
    apply hide_i in Dpn; apply hide_i in DaS; apply hide_i in DpS; apply hide_i in DnS.
  assert (Hpa8 : pa mod 8 + 2 <= 8) by (pose proof (Z.mod_pos_bound pa 8 ltac:(lia)); Z.div_mod_to_equations; lia).
  apply (wr_at_transport rsegs mE m) in WA; [|exact WM].
  apply (wr_at_transport rsegs mE m) in WP; [|exact WM].
  apply (wr_at_transport rsegs mE m) in WN; [|exact WM].
  pose proof (rf_clear_length _ LJ) as LCJ.
  pose proof (bytes_at_bound rsegs m f _ CJ) as BF. rewrite LCJ in BF.
  pose proof (rf_rd1 rsegs m f _ 17 CJ ltac:(lia) ltac:(rewrite LCJ; lia)) as R17.
  change (Z.to_nat 17) with 17%nat in R17. rewrite (rf_clear_nth _ 17 _ LJ ltac:(lia)) in R17.
  pose proof (rf_rd1 rsegs m f _ 18 CJ ltac:(lia) ltac:(rewrite LCJ; lia)) as R18.
  change (Z.to_nat 18) with 18%nat in R18. rewrite (rf_clear_nth _ 18 _ LJ ltac:(lia)) in R18.
  apply (munch_weaken [(f, f + 72); (S - 4672, S)] W5) in MU;
    [|unfold sub_fp, W5; cbn [outside]; intros; tauto].
  ubs (-10).
  step.
  chk1 (f + 17) (Z_to_bv 5 12) (fa_rd1 m W5 f 72 17 (f + 17) SRf ADf MU ltac:(fa_sub) ltac:(lia) eq_refl).
  ubs (-11).
  (* pa is 2-aligned *)
  step. step. rewrite ?(unsigned_lit pa) by lia. rewrite fa_land1, Ma.
  change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
  step.
  destruct (fa_rd1 m W5 f 72 18 (f + 18) SRf ADf MU ltac:(fa_sub) ltac:(lia) eq_refl) as (k18 & RK18 & OK18 & KR18).
  step. rewrite ?(unsigned_lit (f + 18)) by lia. rewrite rc_shr3.
  step. step. clear RK18. step. clear R17. step.
  chk_if (f + 18) (Z_to_bv 5 13) k18 OK18.
  destruct (fa_rd2 m W5 pa 2 0 pa SRa ADa MU ltac:(fa_sub) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (kpa & RKpa & OKpa & KRpa & HBpa).
  step. rewrite ?(unsigned_lit pa) by lia. rewrite rc_shr3.
  step. step. clear RKpa. step. clear R18. step.
  chk_if2 pa (Z_to_bv 5 13) kpa OKpa.
  step. step. step.
  pose proof (fa_store_ok m pa 2 2 WA ltac:(lia)) as SA.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?b) _) =>
    assert (EA : b = le2 (Z_to_bv 64 (fg_addr st g))) end.
  { rewrite rc_le2_pack. unfold fg_addr, bat. change (Z.to_nat 17) with 17%nat. change (Z.to_nat 18) with 18%nat.
    rewrite Z.mul_comm. symmetry. apply rc_le2_pair. }
  rewrite EA.
  change (Z_to_bv 64 pa) with (wa pa).
  pose proof (munch_write W5 mE m pa (le2 (Z_to_bv 64 (fg_addr st g))) MU ltac:(lia)
                ltac:(rewrite length_le2; lia) ltac:(unfold W5; cbn [inside]; rewrite length_le2; lia)) as MU1.
  step. rewrite (u_ltu_negl (f + 8) (-12)) by lia. cbv iota.
  (* pp is 8-aligned *)
  step. step. rewrite ?(unsigned_lit pp) by lia. rewrite rc_land7, Mp.
  change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
  (* pp 8-byte check at the post-pa-store memory *)
  pose proof (asan_shadow_rd_munch rsegs mE _ off pp 8 W5 W5 SRp MU1 ltac:(fa_sub)) as SRp1.
  pose proof (asan_addressable_munch rsegs mE _ off pp 8 W5 W5 ADp SRp MU1 ltac:(fa_sub)) as ADp1.
  pose proof (asan_rt3_munch rsegs mE _ off pp 8 W5 W5 R3p SRp MU1 ltac:(fa_sub)) as R3p1.
  destruct (asan_shadow_read rsegs _ off pp 8 W5 0 SRp1 ltac:(lia)) as (kpp & RKpp & BKpp).
  pose proof (asan_check_8 rsegs _ off pp 8 0 kpp ADp1 R3p1 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Mp) BKpp) as K0pp.
  pose proof (rc_signed0_unsigned0 kpp K0pp) as K0ppu.
  rewrite Z.add_0_r in RKpp.
  step. rewrite ?(unsigned_lit pp) by lia. rewrite rc_shr3.
  step. step.
  replace (zxb kpp) with (Z_to_bv 64 0) by (unfold zxb; rewrite K0ppu; reflexivity).
  step.
  change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
  step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (fa_store_ok mm pp 8 8 (wr_at_write rsegs _ pp 8 _ _ WP) ltac:(lia)) as SP end.
  step.
  change (Z_to_bv 64 pp) with (wa pp). rewrite ?(unsigned_lit (f + 19)) by lia.
  pose proof (munch_write W5 mE _ pp (le8 (Z_to_bv 64 (f + 19))) MU1 ltac:(lia)
                ltac:(rewrite length_le8; lia) ltac:(unfold W5; cbn [inside]; rewrite length_le8; lia)) as MU2.
  (* pn is 8-aligned *)
  step. rewrite ?(unsigned_lit pn) by lia. rewrite rc_land7, Mn.
  change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
  (* pn 8-byte check at the post-pp-store memory *)
  pose proof (asan_shadow_rd_munch rsegs mE _ off pn 8 W5 W5 SRn MU2 ltac:(fa_sub)) as SRn2.
  pose proof (asan_addressable_munch rsegs mE _ off pn 8 W5 W5 ADn SRn MU2 ltac:(fa_sub)) as ADn2.
  pose proof (asan_rt3_munch rsegs mE _ off pn 8 W5 W5 R3n SRn MU2 ltac:(fa_sub)) as R3n2.
  destruct (asan_shadow_read rsegs _ off pn 8 W5 0 SRn2 ltac:(lia)) as (kpn & RKpn & BKpn).
  pose proof (asan_check_8 rsegs _ off pn 8 0 kpn ADn2 R3n2 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Mn) BKpn) as K0pn.
  pose proof (rc_signed0_unsigned0 kpn K0pn) as K0pnu.
  rewrite Z.add_0_r in RKpn.
  step. rewrite ?(unsigned_lit pn) by lia. rewrite rc_shr3. step. step.
  replace (zxb kpn) with (Z_to_bv 64 0) by (unfold zxb; rewrite K0pnu; reflexivity).
  step.
  change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (fa_store_ok mm pn 8 8 (wr_at_write rsegs _ pn 8 _ _ (wr_at_write rsegs _ pn 8 _ _ WN)) ltac:(lia))
      as SN end.
  step.
  change (Z_to_bv 64 pn) with (wa pn). rewrite ?(unsigned_lit (fg_T st g - 13)) by lia.
  step. step.
  eapply (L_epi FgClose); [ rewrite <- HcC; exact Hc | reflexivity | | | | | | ].
  - apply rw_cells_frame; [apply rw_cells_frame; [apply rw_cells_frame; [exact FR | fz | fz | fzu DaS]
        | fz | fz | fzu DpS] | fz | fz | fzu DnS].
  - apply stk_write; [apply stk_write; [apply stk_write; [exact ST | fz | fz] | fz | fz] | fz | fz].
  - change (fg_fp 4672 f pa pp pn S FgClose)
      with [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (S - 4672, S)].
    apply munch_write; [apply munch_write; [apply munch_write; [exact MU | fz | fz | fz] | fz | fz | fz]
      | fz | fz | fz].
  - apply wmono_write, wmono_write, wmono_write, WM.
  - apply mem_inv_store; [apply mem_inv_store; [apply mem_inv_store; [exact MI | rewrite length_le2; exact SA]
        | rewrite length_le8; exact SP] | rewrite length_le8; exact SN].
  - cbn [fg_mem]. split; [|split; [|split]].
    + apply bytes_at_write_other; [apply bytes_at_write_other; [apply bytes_at_write_other; [exact CJ | fz | fz | fzu Dfa]
          | fz | fz | fzu Dfp] | fz | fz | fzu Dfn].
    + apply bytes_at_write_other; [apply bytes_at_write_other; [apply bytes_at_write_same; fz | fz | fz | fzu Dap]
        | fz | fz | fzu Dan].
    + apply bytes_at_write_other; [apply bytes_at_write_same; fz | fz | fz | fzu Dpn].
    + apply bytes_at_write_same; fz.
Qed.

Ltac jfail := eapply (L_ret0 FgJoin);
  [ symmetry; match goal with H : CL = _ |- _ => rewrite H end;
    let EC := fresh "EC" in destruct (fg_close st g) eqn:EC; [exfalso; apply close_iff in EC; lia | reflexivity]
  | reflexivity | eassumption | eassumption | match goal with H : munch _ mE _ |- _ => exact H end
  | eassumption | eassumption
  | match goal with H : bytes_at _ _ f (fg_clear _) |- _ => exact H end ].

Ltac jld i :=
  let R := fresh "RDJ" in
  match goal with CJ : bytes_at _ _ f (fg_clear _), LJ : length (fg_join st g) = _ |- _ =>
    pose proof (rd_byte rsegs _ f _ i CJ ltac:(rewrite rf_clear_length by exact LJ; lia)) as R;
    rewrite (rf_clear_nth _ i _ LJ ltac:(lia)) in R
  end;
  step; clear R.

Ltac jbyte i z c :=
  rewrite (rf_beq (nth i (fg_join st g) (Z_to_bv 8 0)) c) by lia;
  change (bv_unsigned (nth i (fg_join st g) (Z_to_bv 8 0))) with (bat (fg_join st g) z);
  let B := fresh "B" in destruct (Z.eqb_spec (bat (fg_join st g) z) c) as [B|B]; cbn [negb]; cbv iota; [|jfail].

Ltac jchk Psrli i r :=
  steps_to Psrli;
  match goal with
  | SRf : asan_shadow_rd rsegs mE off f 72 W5, ADf : asan_addressable rsegs mE off f 72,
    MU : munch [(f, f + 72); (S - 4672, S)] mE ?mm |- _ =>
      chk1 (f + i) r (fa_rd1 mm [(f, f + 72); (S - 4672, S)] f 72 i (f + i) SRf ADf MU ltac:(fa_sub) ltac:(lia) eq_refl)
  end.

(* 0x85d64 ..: the close checks on the joined record, the record checksum call. *)
Lemma L_tail : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
  CL = (if fg_close st g then FgClose else FgJoin) -> 1 <= fg_n g <= 22 -> fg_T st g <= 64 -> DJB ->
  (f + 72 <= S - 4672 \/ S <= f) -> 0 < f -> OUT ->
  rw_cells rsegs m (S + -112) (FRc Jc) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(f, f + 72); (S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  bytes_at rsegs m f (fg_clear (fg_join st g)) ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) (Z_to_bv 64 14) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 pp) (Z_to_bv 64 pa) (Z_to_bv 64 fr) (Z_to_bv 64 (f + 8)) (Z_to_bv 64 (fr + 18))
             (zxb (nth 26 g (Z_to_bv 8 0))) (Z_to_bv 64 (f + 6)) (Z_to_bv 64 off) (Z_to_bv 64 (fg_T st g))
             (Z_to_bv 64 ((f + 6) / 8 + off)) x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85d64) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
    HCL Hn HT DJBh DfS Hf0 OUTh FR ST MU WM MI CJ.
  assert (NZh : NZ) by (apply cl_nz; rewrite HCL; destruct (fg_close st g); discriminate).
  destruct (HAF NZh) as ((Af & _) & SRf & ADf & _).
  rngf NZh.
  pose proof (rt_addressable_bound mE f 72 Af) as (Hfa0 & _ & Hf2).
  pose proof (rf_fg_join_length st g Hst Hg Hn HT) as LJ.
  pose proof (rf_clear_length _ LJ) as LCJ.
  pose proof (bytes_at_bound rsegs m f _ CJ) as BF. rewrite LCJ in BF.
  assert (T0 : 0 <= fg_T st g).
  { unfold fg_T, fg_lf, bat. pose proof (byte_range (nth (Z.to_nat 7) st (Z_to_bv 8 0))). lia. }
  step.
  rewrite (fa_ltu (fg_T st g) 14) by lia.
  destruct (Z.ltb_spec (fg_T st g) 14) as [T14|T14]; cbv iota; [jfail|].
  jchk 0x85d68 8 (Z_to_bv 5 11). jld 8%nat. step. step. jbyte 8%nat 8 240.
  step. step. rewrite (u_eqb_negc (f + 8) (-1)) by lia. cbv iota.
  jchk 0x85d90 9 (Z_to_bv 5 12). jld 9%nat. step. step. jbyte 9%nat 9 65.
  ubs (-4).
  jchk 0x85db8 11 (Z_to_bv 5 12). jld 11%nat. step. jbyte 11%nat 11 0.
  ubs (-5).
  jchk 0x85ddc 12 (Z_to_bv 5 12). jld 12%nat. step. jbyte 12%nat 12 0.
  ubs (-6).
  jchk 0x85e00 13 (Z_to_bv 5 12). jld 13%nat. step. step. jbyte 13%nat 13 18.
  ubs (-7).
  jchk 0x85e28 14 (Z_to_bv 5 12). jld 14%nat. step. step. jbyte 14%nat 14 18.
  ubs (-8).
  jchk 0x85e50 15 (Z_to_bv 5 12). jld 15%nat. step. step. jbyte 15%nat 15 5.
  ubs (-9).
  jchk 0x85e78 16 (Z_to_bv 5 13). jld 16%nat. step. jbyte 16%nat 16 0.
  step. step.
  assert (LTt : bv_ltu (Z_to_bv 64 (18446744073709551615 - (f + 8))) (Z_to_bv 64 (fg_T st g + -1)) = false).
  { unfold bv_ltu. rewrite !unsigned_lit_wrap. apply Z.ltb_ge.
    change (2 ^ 64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia. }
  step. rewrite LTt. cbv iota. clear LTt.
  step.
  replace (f + 8 + (fg_T st g + -1)) with (f + (7 + fg_T st g)) by lia.
  chk1 (f + (7 + fg_T st g)) (Z_to_bv 5 13)
    (fa_rd1 m [(f, f + 72); (S - 4672, S)] f 72 (7 + fg_T st g) (f + (7 + fg_T st g)) SRf ADf MU ltac:(fa_sub)
       ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m f (fg_clear (fg_join st g)) (Z.to_nat (7 + fg_T st g)) CJ ltac:(rewrite LCJ; lia)) as RDJ.
  rewrite (rf_clear_nth _ (Z.to_nat (7 + fg_T st g)) _ LJ ltac:(lia)) in RDJ.
  rewrite (Z2Nat.id (7 + fg_T st g)) in RDJ by lia.
  step. clear RDJ. step. step.
  rewrite (rf_beq (nth (Z.to_nat (7 + fg_T st g)) (fg_join st g) (Z_to_bv 8 0)) 247) by lia.
  change (bv_unsigned (nth (Z.to_nat (7 + fg_T st g)) (fg_join st g) (Z_to_bv 8 0)))
    with (bat (fg_join st g) (7 + fg_T st g)).
  destruct (Z.eqb_spec (bat (fg_join st g) (7 + fg_T st g)) 247) as [B7|B7]; cbn [negb]; cbv iota; [|jfail].
  step. step. rewrite (u_eqb_negc (f + 8) (-7)) by lia. cbv iota.
  pose proof (rf_bytes_bsl rsegs m f (fg_clear (fg_join st g)) 15 (fg_T st g - 8) CJ ltac:(lia) ltac:(lia)
                ltac:(rewrite LCJ; lia)) as HBr.
  assert (EBs : bsl (fg_clear (fg_join st g)) 15 (fg_T st g - 8) = bsl (fg_join st g) 15 (fg_T st g - 8)).
  { unfold bsl. change (Z.to_nat 15) with 15%nat. rewrite (rf_clear_skipn _ 15 LJ ltac:(lia)). reflexivity. }
  rewrite EBs in HBr.
  pose proof (rtW [(f, f + 72); (S - 4672, S)] m NZh MU ltac:(fa_sub) WM) as (ACm & SRm).
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m f 72 Af MU (fa_sowf NZh)) as ADfm.
  pose proof CKV as HCV. unfold reac_ctrl_record_cksum_verify_contract_F in HCV.
  step. step.
  eapply evtF_cut.
  { eapply HCV with (bs := bsl (fg_join st g) 15 (fg_T st g - 8)).
    - rewrite unsigned_lit by lia. rewrite rf_bsl_length by (rewrite ?LJ; lia). first [reflexivity | f_equal; lia].
    - right. rewrite !unsigned_lit by lia. split; [lia|]. split; [lia|]. split; [exact HBr|].
      unfold REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME; destruct DfS as [H|H]; [left; lia | right; lia].
    - rewrite (unsigned_lit (S + -112)) by lia. exact ST.
    - rewrite (unsigned_lit (S + -112)) by lia. unfold REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME. lia.
    - intros _; exact ACm.
    - intros _; exact SRm.
    - intros _. rewrite !unsigned_lit by lia. apply (fa_addr_sub m f 72); [exact ADfm | lia | lia | lia].
    - intros _ x Hx. rewrite (unsigned_lit (S + -112)) by lia. cbn [outside]. split; [|exact I].
      unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
        REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME in *. lia.
    - rewrite (unsigned_lit (S + -112)) by lia. unfold REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME.
      apply (rng_sub' RNG (S - 4672) 4672); [exact RSTK | lia].
    - unfold GOT_CELL_K. apply (rng_sub' RNG IMG_LO (IMG_HI - IMG_LO)); [exact RIMG | unfold IMG_LO, IMG_HI; lia].
    - unfold CELL_K. apply (rng_sub' RNG IMG_LO (IMG_HI - IMG_LO)); [exact RIMG | unfold IMG_LO, IMG_HI; lia].
    - intros _. rewrite !unsigned_lit by lia. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - intros _. rewrite !unsigned_lit by lia. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_bytes' RNG off f 72 (f + 15) (fg_T st g - 8) ltac:(lia) ltac:(lia) ltac:(lia) RGfs). }
  intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & MU' & WM' & MImp & ST').
  subst ms'.
  rewrite (unsigned_lit (S + -112)) in MU', ST' by lia.
  unfold REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME in MU', ST'.
  assert (SUBc : sub_fp [(S + -112 - 16, S + -112)] [(f, f + 72); (S - 4672, S)])
    by (intros xx; cbn [outside]; intros (H1 & H2 & _); split; [lia | exact I]).
  pose proof (munch_trans [(f, f + 72); (S - 4672, S)] mE m m' MU (munch_weaken _ _ m m' SUBc MU')) as MUc.
  pose proof (wmono_trans rsegs mE m m' WM WM') as WMc.
  pose proof (rw_cells_transport rsegs [(S + -112 - 16, S + -112)] m m' (S + -112) (FRc Jc) FR MU' WM'
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FRc2.
  pose proof (bytes_at_transport rsegs [(S + -112 - 16, S + -112)] m m' f (fg_clear (fg_join st g)) CJ MU'
                ltac:(cbn [disjoint_from]; rewrite LCJ; destruct DfS as [H|H]; repeat split; try exact I; lia)) as CJc.
  pose proof (MImp MI) as MIc.
  clear FR ST MU WM MI CJ MU' WM' MImp.
  replace (ret_pc (Z_to_bv 64 0x85ecc)) with (Z_to_bv 64 0x85ecc)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (Z.eqb_spec (recsum (bsl (fg_join st g) 15 (fg_T st g - 8))) 0) as [RS0|RS0]; cbv iota.
  2:{ step. rewrite u_eqb_m1. cbn [negb]. cbv iota. jfail. }
  step. rewrite (rc_eq0w (Z_to_bv 64 0)) by reflexivity. cbn [negb]. cbv iota.
  assert (EC : fg_close st g = true) by (apply close_iff; repeat split; first [assumption | lia]).
  eapply (L_close FgClose); [ rewrite HCL, EC; reflexivity | reflexivity | lia | exact LJ | exact DJBh | exact FRc2
    | exact ST' | exact MUc | exact WMc | exact MIc | exact CJc | exact OUTh ].
Qed.

(* 0x85d2c ..: the join path (append the body at f + 8 + lf, clear byte 6, fall to the close checks). *)
Lemma L_join : forall j (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word) m,
  CL = (if fg_close st g then FgClose else FgJoin) -> 1 <= fg_n g <= 22 -> fg_T st g <= 64 -> DJA -> DJB -> OUT ->
  0 < f ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(f, f + 72); (S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  bytes_at rsegs m f st -> wr_at rsegs m f (Z.of_nat (length st)) -> bytes_at rsegs m fr g ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) (zxb (nth 7 st (Z_to_bv 8 0)))
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 pp) (Z_to_bv 64 pa) (Z_to_bv 64 fr) x21
             (Z_to_bv 64 (fr + 18)) (zxb (nth 26 g (Z_to_bv 8 0))) (Z_to_bv 64 (f + 6)) (Z_to_bv 64 off)
             (Z_to_bv 64 (fg_T st g)) (Z_to_bv 64 ((f + 6) / 8 + off)) x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85d2c) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 m
    HCL Hn HT DJAh DJBh OUTh Hf0 FR ST MU WM MI HSb HSw HG.
  assert (NZh : NZ) by (apply cl_nz; rewrite HCL; destruct (fg_close st g); discriminate).
  assert (FRT : fg_fr len g = true).
  { destruct (fg_fr len g) eqn:E; [reflexivity|].
    assert (HN : CL = FgNone) by (rewrite (cl_nn NZh), E; reflexivity).
    rewrite HN in HCL. destruct (fg_close st g); discriminate HCL. }
  pose proof (proj1 (proj1 (fr_iff len g) FRT)) as Hlen50.
  destruct (HAF NZh) as ((Af & Aa & Ap & An & Happ & DJrt) & SRf & ADf & _).
  destruct (HAG NZh Hlen50) as (Ag & SRg & ADg).
  rngf NZh. rngg NZh Hlen50.
  destruct DJAh as (Dff & DfS & DrS).
  pose proof (rt_addressable_bound mE f 72 Af) as (Hfa0 & _ & Hf2).
  pose proof (rt_addressable_bound mE fr 50 Ag) as (Hr0 & _ & Hr2).
  pose proof (bytes_at_bound rsegs m fr g HG) as BG. rewrite Hg in BG.
  pose proof (bytes_at_bound rsegs m f st HSb) as BF. rewrite Hst in BF.
  pose proof (byte_range (nth 7 st (Z_to_bv 8 0))) as R7.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st) in R7.
  assert (TT : fg_T st g = fg_lf st + fg_n g) by reflexivity.
  pose proof (rf_rw_sub rsegs m f st 6 1 HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as P6.
  pose proof (rf_rw_sub rsegs m f st (8 + fg_lf st) (fg_n g) HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia))
    as P8.
  replace (f + (8 + fg_lf st)) with (f + 8 + fg_lf st) in P8 by lia.
  pose proof (rf_bytes_first rsegs m f st 6 HSb) as B0.
  pose proof (rf_bytes_bsl rsegs m f st 7 (1 + fg_lf st) HSb ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as B7.
  pose proof (rf_bytes_skip rsegs m f st (8 + fg_T st g) HSb ltac:(rewrite Hst; lia)) as BR.
  pose proof (rf_bytes_bsl rsegs m fr g 27 (fg_n g) HG ltac:(lia) ltac:(lia) ltac:(rewrite Hg; lia)) as GB.
  assert (LGB : length (bsl g 27 (fg_n g)) = Z.to_nat (fg_n g)) by (apply rf_bsl_length; rewrite ?Hg; lia).
  assert (LB7 : length (bsl st 7 (1 + fg_lf st)) = Z.to_nat (1 + fg_lf st))
    by (apply rf_bsl_length; rewrite ?Hst; lia).
  assert (LB0 : length (firstn 6 st) = 6%nat) by (rewrite length_firstn; lia).
  change (Z.to_nat 1) with 1%nat in P6.
  (* the shared statement, with its shadow word spans (sh_word_rng of rng_asan.v) written out *)
  pose proof MCPY as HM. unfold asan_memcpy_contract_F, sh_word_rng, sh_al8_lo, sh_al8_hi in HM. cbv zeta in HM.
  step. step.
  try rewrite (unsigned_lit (f + 8)) by lia. rewrite (zb_lxor_ones (f + 8)) by lia.
  step. step.
  assert (LTo : bv_ltu (Z_to_bv 64 (18446744073709551615 - (f + 8))) (zxb (nth 7 st (Z_to_bv 8 0))) = false).
  { unfold bv_ltu. rewrite rf_zxb_u, unsigned_lit_wrap.
    change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st).
    apply Z.ltb_ge. change (2 ^ 64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia. }
  rewrite LTo. cbv iota. clear LTo.
  step. step. rewrite (u_ltu_negl (fr + 18) (-10)) by lia. cbv iota.
  step. step. step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m0 end.
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m0 f 72 Af MU (fa_sowf NZh)) as ADfm.
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m0 fr 50 Ag MU (fa_sowf NZh)) as ADgm.
  pose proof (rtW [(f, f + 72); (S - 4672, S)] m0 NZh MU ltac:(fa_sub) WM) as (ACm & SRm).
  pose proof (fa_addr_app m0 f 72 0 ADfm ltac:(lia)) as APPf0. rewrite Z.add_0_r in APPf0.
  pose proof (rf_bytes_skip rsegs m0 f st (8 + fg_T st g) HSb ltac:(rewrite Hst; lia)) as BR.
  rewrite ?rf_zxb_u.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st).
  assert (U0 : bv_unsigned (Z_to_bv 64 (f + 8 + fg_lf st)) = f + 8 + fg_lf st) by (apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 (fr + 27)) = fr + 27) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (zxb (nth 26 g (Z_to_bv 8 0))) = fg_n g) by (exact (rf_zxb_u _)).
  assert (U3 : bv_unsigned (Z_to_bv 64 (S + -112)) = S + -112) by (apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HM with (src := bsl g 27 (fg_n g)) (junk := bsl st (8 + fg_lf st) (fg_n g)) (lo := S - 4672).
    - rewrite U1. exact GB.
    - rewrite U2. exact LGB.
    - rewrite U0, U2. exact P8.
    - rewrite U0, U1, U2. destruct Dff as [H|H]; [right; right; lia | right; left; lia].
    - rewrite U2. lia.
    - rewrite U1, U2. apply (fa_addr_sub m0 fr 50); [exact ADgm | lia | lia | lia].
    - rewrite U0, U2. apply (fa_addr_sub m0 f 72); [exact ADfm | lia | lia | lia].
    - rewrite U1, U2. unfold end_in_app. right. replace (fr + 27 + fg_n g) with (fr + (27 + fg_n g)) by lia.
      apply (fa_addr_app m0 fr 50 (27 + fg_n g)); [exact ADgm | lia].
    - rewrite U0, U2. unfold end_in_app. right.
      apply (fa_app_mid f (f + 78) (f + 8 + fg_lf st + fg_n g)); [exact APPf0 | exact Happ | lia | lia].
    - rewrite U0, U1, U2. right. split;
        [replace (fr + 27 + 7) with (fr + 34) by lia; apply (fa_addr_app m0 fr 50 34); [exact ADgm | lia]
        | apply (fa_app_mid f (f + 78) (f + 8 + fg_lf st + 7)); [exact APPf0 | exact Happ | lia | lia]].
    - rewrite U0, U2. cbn [dj_from] in DJrt. destruct DJrt as [[H|H] _]; [right; lia | left; lia].
    - rewrite U0, U2, U3. unfold ASAN_MEMCPY_K. destruct DfS as [H|H]; [left; lia | right; lia].
    - rewrite U1, U2, U3. unfold ASAN_MEMCPY_K. destruct DrS as [H|H]; [left; lia | right; lia].
    - rewrite U3. exact ST.
    - rewrite U3. unfold ASAN_MEMCPY_K. lia.
    - unfold HIGHMEM_BEG. lia.
    - rewrite U3. unfold APPMEM_END. lia.
    - exact ACm.
    - exact SRm.
    - exact MI.
    - exact RBY.
    - exact RIMG.
    - rewrite U3. unfold ASAN_MEMCPY_K. apply (rng_sub' RNG (S - 4672) 4672); [exact RSTK | lia].
    - rewrite U0, U2. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - rewrite U1, U2. apply (rng_sub' RNG fr 50); [exact RGr | lia].
    - rewrite U0, U2. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off f 72 (f + 8 + fg_lf st) (fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) RGfs).
    - rewrite U1, U2. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off fr 50 (fr + 27) (fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) RGrs).
    - rewrite U3. unfold ASAN_MEMCPY_K. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off (S - 4672) 4672 (S + -112 - 2224) 2224 ltac:(lia) ltac:(lia) ltac:(lia) RSTKS). }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                  & E & MU2 & WM2 & MI2 & ST2 & RW2 & BD2 & AC2 & SR2).
  subst ms'. clear BD2.
  rewrite U0, U2 in RW2. rewrite U0, U2, U3 in MU2. rewrite U3 in ST2.
  try (replace (ret_pc (Z_to_bv 64 0x85d54)) with (Z_to_bv 64 0x85d54)
    by (symmetry; apply ret_pc_even; [lia | reflexivity])).
  assert (SUB1 : sub_fp [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -112 - 2224, S + -112)]
                        [(f, f + 72); (S - 4672, S)])
    by (intros x; cbn [outside]; intros (H1 & H2 & _); split; [lia | split; [lia | exact I]]).
  pose proof (munch_trans [(f, f + 72); (S - 4672, S)] mE m0 m2 MU (munch_weaken _ _ m0 m2 SUB1 MU2)) as MU3.
  pose proof (wmono_trans rsegs mE m0 m2 WM WM2) as WM3.
  replace (Z.of_nat (length st)) with 72 in HSw by (rewrite Hst; reflexivity).
  pose proof (wr_at_transport rsegs m0 m2 f 72 HSw WM2) as WRm2.
  pose proof (bytes_at_transport rsegs [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -112 - 2224, S + -112)]
                m0 m2 f (firstn 6 st) B0 MU2
                ltac:(cbn [disjoint_from]; rewrite LB0; repeat split; try exact I; lia)) as B0m2.
  pose proof (bytes_at_transport rsegs [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -112 - 2224, S + -112)]
                m0 m2 (f + 7) (bsl st 7 (1 + fg_lf st)) B7 MU2
                ltac:(cbn [disjoint_from]; rewrite LB7, Z2Nat.id by lia; repeat split; try exact I; lia)) as B7m2.
  pose proof (bytes_at_transport rsegs [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -112 - 2224, S + -112)]
                m0 m2 (f + (8 + fg_T st g)) (skipn (Z.to_nat (8 + fg_T st g)) st) BR MU2
                ltac:(cbn [disjoint_from]; rewrite length_skipn, Hst; repeat split; try exact I; lia)) as BRm2.
  pose proof (rw_cells_transport rsegs [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -112 - 2224, S + -112)]
                m0 m2 (S + -112) FRj FR MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FR2.
  pose proof (proj1 (rf_rw_parts rsegs m2 (f + 8 + fg_lf st) (Z.to_nat (fg_n g)) (bsl g 27 (fg_n g)) RW2)) as BB.
  destruct (fa_rdb m2 [(f, f + 72); (S - 4672, S)] f 72 6 (f + 6) SRf ADf MU3 ltac:(fa_sub) ltac:(lia) eq_refl)
    as (k6 & RK6 & OK6 & KR6 & HB6).
  step. clear RK6. step.
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k6)) by lia.
  lazymatch goal with
  | |- evtF ?segs ?RN ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      enough (G : forall rr : word, evtF segs RN Q (MS (bvmap_set (Z_to_bv 5 11) rr R) F B fc rv mm ro));
      [ destruct (Z.eqb_spec (bv_signed k6) 0) as [K6|K6]; cbn [negb];
        [ bjoin G (Z_to_bv 5 11)
        | step; rewrite ?(unsigned_lit (f + 6)) by lia; rewrite rc_land7; step;
          rewrite (rc_lts_signed ((f + 6) mod 8) (bv_signed k6)) by (pose proof (Z.mod_pos_bound (f + 6) 8 ltac:(lia)); lia);
          replace ((f + 6) mod 8 <? bv_signed k6) with true by (symmetry; apply Z.ltb_lt; destruct OK6; lia);
          bjoin G (Z_to_bv 5 11) ]
      | intros ?; simp_regs; clear OK6 KR6 HB6 ]
  end.
  step.
  pose proof (wr_at_store_ok rsegs m2 f 72 6 1%nat WRm2 ltac:(lia) ltac:(lia)) as SO6.
  step.
  change (Z_to_bv 64 (f + 6)) with (wa (f + 6)).
  pose proof (bytes_at_write_same rsegs m2 (f + 6) [Z_to_bv 8 0] ltac:(lia) ltac:(cbn [length]; lia)) as B6.
  pose proof (bytes_at_write_other rsegs m2 (f + 6) [Z_to_bv 8 0] f (firstn 6 st) B0m2 ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(rewrite LB0; cbn [length]; lia)) as B0m3.
  pose proof (bytes_at_write_other rsegs m2 (f + 6) [Z_to_bv 8 0] (f + 7) (bsl st 7 (1 + fg_lf st)) B7m2
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as B7m3.
  pose proof (bytes_at_write_other rsegs m2 (f + 6) [Z_to_bv 8 0] (f + 8 + fg_lf st) (bsl g 27 (fg_n g)) BB
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as BBm3.
  pose proof (bytes_at_write_other rsegs m2 (f + 6) [Z_to_bv 8 0] (f + (8 + fg_T st g))
                (skipn (Z.to_nat (8 + fg_T st g)) st) BRm2 ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia))
    as BRm3.
  replace (f + 8 + fg_lf st) with (f + (8 + fg_lf st)) in BBm3 by lia.
  assert (CJ : bytes_at rsegs (write_to_mem m2 (wa (f + 6)) [Z_to_bv 8 0]) f (fg_clear (fg_join st g))).
  { rewrite fa_clear_join by (first [exact Hst | lia]).
    apply (rf_app _ _ f _ (f + 6)); [exact B0m3 | | rewrite LB0; lia].
    apply (rf_app _ _ (f + 6) _ (f + 7)); [exact B6 | | cbn [length]; lia].
    apply (rf_app _ _ (f + 7) _ (f + (8 + fg_lf st))); [exact B7m3 | | rewrite LB7, Z2Nat.id by lia; lia].
    apply (rf_app _ _ (f + (8 + fg_lf st)) _ (f + (8 + fg_T st g)));
      [exact BBm3 | exact BRm3 | unfold fg_body; rewrite LGB, Z2Nat.id by lia; lia]. }
  pose proof (munch_write [(f, f + 72); (S - 4672, S)] mE m2 (f + 6) [Z_to_bv 8 0] MU3 ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(unfold W5; cbn [inside length]; lia)) as MU4.
  pose proof (wmono_write rsegs mE m2 (wa (f + 6)) [Z_to_bv 8 0] WM3) as WM4.
  pose proof (mem_inv_store rsegs m2 (wa (f + 6)) [Z_to_bv 8 0] MI2 ltac:(cbn [length]; exact SO6)) as MI3.
  pose proof (stk_write rsegs m2 (S - 4672) (S + -112) (f + 6) [Z_to_bv 8 0] ST2 ltac:(lia)
                ltac:(cbn [length]; lia)) as ST3.
  pose proof (rw_cells_frame rsegs m2 (S + -112) FRj (f + 6) [Z_to_bv 8 0] FR2 ltac:(lia) ltac:(cbn [length]; lia)
                ltac:(cbn [cells_size csize Nat.add length]; lia)) as FR3.
  apply fa_fr_c8 in FR3.
  eapply L_tail; [ exact HCL | exact Hn | exact HT | exact DJBh | exact DfS | exact Hf0 | exact OUTh | exact FR3
    | exact ST3 | exact MU4 | exact WM4 | exact MI3 | exact CJ ].
Qed.

(* 0x85cc4 ..: the second-record path (keep/drop/join/close dispatch). *)
Lemma L_second : forall j (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
  NZ -> fg_fr len g = true -> bat g 19 <> 1 -> DJA -> DJB -> OUT ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  rw_cells rsegs m f [CB 72 st] -> bytes_at rsegs m fr g ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 pp) (Z_to_bv 64 pa) (Z_to_bv 64 fr) s5 (Z_to_bv 64 (fr + 18)) (zxb (nth 26 g (Z_to_bv 8 0)))
             s8 (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85cc4) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
    NZh FRT B19 DJAh DJBh OUTh FR ST MU WM MI HS HG.
  pose proof DJAh as (Dff & DfS & DrS).
  assert (Hf0 : 0 < f) by (destruct NZh as (Nf & _); lia).
  pose proof (proj1 (fr_iff len g) FRT) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hn1 & Hn2 & _).
  pose proof (cl_k NZh FRT B19) as HCL0.
  destruct (HAF NZh) as ((Af & Aa & Ap & An & Happ & DJrt) & SRf & ADf & _).
  destruct (HAG NZh (proj1 (proj1 (fr_iff len g) FRT))) as (Ag & SRg & ADg).
  rngf NZh. rngg NZh (proj1 (proj1 (fr_iff len g) FRT)).
  pose proof (rt_addressable_bound mE f 72 Af) as (Hfa0 & _ & Hf2).
  pose proof (rt_addressable_bound mE fr 50 Ag) as (Hr0 & _ & Hr2).
  pose proof (bytes_at_bound rsegs m fr g HG) as BG. rewrite Hg in BG.
  pose proof (rw_cells_bound rsegs m f _ HS) as BF. cbn [cells_size csize Nat.add] in BF.
  destruct (rf_rw_parts rsegs m f 72 st HS) as (HSb & HSw & _). clear HS.
  pose proof MU as MU0.
  apply (munch_weaken [(S - 4672, S)] [(f, f + 72); (S - 4672, S)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  pose proof (byte_range (nth 7 st (Z_to_bv 8 0))) as RL.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st) in RL.
  pose proof (byte_range (nth 26 g (Z_to_bv 8 0))) as RN.
  change (bv_unsigned (nth 26 g (Z_to_bv 8 0))) with (fg_n g) in RN.
  step.
  chk1 (f + 6) (Z_to_bv 5 11)
    (fa_rd1 m [(f, f + 72); (S - 4672, S)] f 72 6 (f + 6) SRf ADf MU ltac:(fa_sub) ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m f st 6 HSb ltac:(lia)) as R6.
  step. step. clear R6.
  rewrite (rf_beq (nth 6 st (Z_to_bv 8 0)) 0) by lia.
  change (bv_unsigned (nth 6 st (Z_to_bv 8 0))) with (fg_hf st).
  destruct (Z.eqb_spec (fg_hf st) 0) as [H6|H6]; cbv iota.
  { eapply (L_drop FgDrop);
      [ rewrite HCL0; destruct (fg_keep st g) eqn:EK;
          [exfalso; apply keep_iff in EK; destruct EK as (EK & _ & _); lia | reflexivity]
      | reflexivity | exact DfS | exact FR | exact ST | exact MU | exact WM | exact MI
      | rewrite <- Hst; apply fa_rw_of; [exact HSb | rewrite Hst; exact HSw] ]. }
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m f 72 Af MU (fa_sowf NZh)) as ADfm.
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m fr 50 Ag MU (fa_sowf NZh)) as ADgm.
  pose proof (rtW [(f, f + 72); (S - 4672, S)] m NZh MU ltac:(fa_sub) WM) as (ACm & SRm).
  pose proof (rf_bytes_skip rsegs m fr g 6 HG ltac:(rewrite Hg; lia)) as G6.
  change (Z.to_nat 6) with 6%nat in G6.
  destruct (fa_mcmp 6 st (skipn 6 g) ltac:(lia) ltac:(rewrite length_skipn, Hg; lia)) as (v & Hv & Rv & Iv).
  pose proof (HGOT (proj1 NZh) (proj1 (proj2 NZh)) (proj1 (proj2 (proj2 NZh)))
               (proj1 (proj2 (proj2 (proj2 NZh)))) (proj2 (proj2 (proj2 (proj2 NZh))))) as HGm.
  destruct HGm as (HRB0 & HRM0 & HGC0 & HCF10 & HCF20).
  pose proof (bytes_at_transport rsegs [(S - 4672, S)] mE m REAL_BCMP (le8 (wa BCMP)) HRB0 MU0
                ltac:(cbn [disjoint_from]; rewrite length_le8; unfold REAL_BCMP, HIGHMEM_BEG in *; lia)) as HRBm.
  pose proof (bytes_at_transport rsegs [(S - 4672, S)] mE m REAL_MEMCMP (le8 (wa MEMCMP)) HRM0 MU0
                ltac:(cbn [disjoint_from]; rewrite length_le8; unfold REAL_MEMCMP, HIGHMEM_BEG in *; lia)) as HRMm.
  pose proof (bytes_at_transport rsegs [(S - 4672, S)] mE m GOT_CF (le8 (wa CF)) HGC0 MU0
                ltac:(cbn [disjoint_from]; rewrite length_le8; unfold GOT_CF, HIGHMEM_BEG in *; lia)) as HGCm.
  pose proof (bytes_at_transport rsegs [(S - 4672, S)] mE m (CF + 254) [Z_to_bv 8 1] HCF10 MU0
                ltac:(cbn [disjoint_from length]; unfold CF, HIGHMEM_BEG in *; lia)) as HCF1m.
  pose proof (bytes_at_transport rsegs [(S - 4672, S)] mE m (CF + 255) [Z_to_bv 8 1] HCF20 MU0
                ltac:(cbn [disjoint_from length]; unfold CF, HIGHMEM_BEG in *; lia)) as HCF2m.
  pose proof BCMPw as HBc. unfold bcmp_wrap_contract_F in HBc. cbv zeta in HBc.
  step. step. step. step.
  assert (UF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (U6 : bv_unsigned (Z_to_bv 64 (fr + 6)) = fr + 6) by (apply unsigned_lit; lia).
  assert (U6' : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  assert (U3 : bv_unsigned (Z_to_bv 64 (S + -112)) = S + -112) by (apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HBc with (ls := st) (rs := skipn 6 g) (v := v) (lo := S - 4672).
    - rewrite UF. exact HSb.
    - rewrite U6. exact G6.
    - rewrite U6'. exact Hv.
    - exact MI.
    - rewrite U6'. lia.
    - rewrite UF, U6'. apply (fa_addr_sub m f 72); [exact ADfm | lia | lia | lia].
    - rewrite U6, U6'. apply (fa_addr_sub m fr 50); [exact ADgm | lia | lia | lia].
    - rewrite UF, U6'. unfold end_in_app. right. apply (fa_addr_app m f 72 6); [exact ADfm | lia].
    - rewrite U6, U6'. unfold end_in_app. right. replace (fr + 6 + 6) with (fr + 12) by lia.
      apply (fa_addr_app m fr 50 12); [exact ADgm | lia].
    - rewrite UF, U6'. right. apply (fa_addr_app m f 72 7); [exact ADfm | lia].
    - rewrite U6, U6'. right. replace (fr + 6 + 7) with (fr + 13) by lia.
      apply (fa_addr_app m fr 50 13); [exact ADgm | lia].
    - rewrite UF, U6', U3. unfold BCMP_WRAP_K. destruct DfS as [H|H]; [left; lia | right; lia].
    - rewrite U6, U6', U3. unfold BCMP_WRAP_K. destruct DrS as [H|H]; [left; lia | right; lia].
    - rewrite U3. exact ST.
    - rewrite U3. unfold BCMP_WRAP_K. lia.
    - unfold HIGHMEM_BEG. lia.
    - rewrite U3. unfold APPMEM_END. lia.
    - exact ACm.
    - exact SRm.
    - exact HRBm.
    - exact HRMm.
    - exact HGCm.
    - exact HCF1m.
    - exact HCF2m.
    - exact RBY.
    - exact RIMG.
    - rewrite U3. unfold BCMP_WRAP_K. apply (rng_sub' RNG (S - 4672) 4672); [exact RSTK | lia].
    - rewrite UF, U6'. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - rewrite UF, U6'. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off f 72 f 6 ltac:(lia) ltac:(lia) ltac:(lia) RGfs).
    - rewrite U6, U6'. apply (rng_sub' RNG fr 50); [exact RGr | lia].
    - rewrite U6, U6'. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off fr 50 (fr + 6) 6 ltac:(lia) ltac:(lia) ltac:(lia) RGrs). }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m2
                  & E & MU2 & WM2 & MI2 & ST2 & AC2 & SR2 & BL & BR).
  subst ms'. rewrite U3 in MU2, ST2.
  try (replace (ret_pc (Z_to_bv 64 0x85cf0)) with (Z_to_bv 64 0x85cf0)
    by (symmetry; apply ret_pc_even; [lia | reflexivity])).
  assert (SUBb : sub_fp [(S + -112 - 4560, S + -112)] [(f, f + 72); (S - 4672, S)])
    by (intros x; cbn [outside]; intros (H1 & H2 & _); split; [lia | exact I]).
  pose proof (munch_trans [(f, f + 72); (S - 4672, S)] mE m m2 MU (munch_weaken _ _ m m2 SUBb MU2)) as MU3.
  pose proof (wmono_trans rsegs mE m m2 WM WM2) as WM3.
  pose proof (bytes_at_transport rsegs [(S + -112 - 4560, S + -112)] m m2 f st HSb MU2
                ltac:(cbn [disjoint_from]; rewrite Hst; destruct DfS as [H|H]; repeat split; try exact I; lia)) as HSbm2.
  pose proof (bytes_at_transport rsegs [(S + -112 - 4560, S + -112)] m m2 fr g HG MU2
                ltac:(cbn [disjoint_from]; rewrite Hg; destruct DrS as [H|H]; repeat split; try exact I; lia)) as HGm2.
  replace (Z.of_nat (length st)) with 72 in HSw by (rewrite Hst; reflexivity).
  pose proof (wr_at_transport rsegs m m2 f 72 HSw WM2) as WRm2.
  pose proof (rw_cells_transport rsegs [(S + -112 - 4560, S + -112)] m m2 (S + -112) (FRc j) FR MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FR2.
  step.
  rewrite (rf_eqb_s v) by lia.
  destruct (Z.eqb_spec v 0) as [V0|V0]; cbn [negb]; cbv iota.
  2:{ eapply (L_drop FgDrop);
        [ rewrite HCL0; destruct (fg_keep st g) eqn:EK;
            [exfalso; apply keep_iff in EK; destruct EK as (_ & ES & _); apply V0, Iv;
             exact (proj1 (rf_src_eq st g) ES) | reflexivity]
        | reflexivity | exact DfS | exact FR2 | exact ST2 | exact MU3 | exact WM3 | exact MI2
        | rewrite <- Hst; apply fa_rw_of; [exact HSbm2 | rewrite Hst; exact WRm2] ]. }
  pose proof (rd_byte rsegs m2 f st 7 HSbm2 ltac:(lia)) as R7.
  step.
  chk1 (f + 7) (Z_to_bv 5 12)
    (fa_rd1 m2 [(f, f + 72); (S - 4672, S)] f 72 7 (f + 7) SRf ADf MU3 ltac:(fa_sub) ltac:(lia) eq_refl).
  step. clear R7. step. step. step.
  rewrite ?rf_zxb_u.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st).
  change (bv_unsigned (nth 26 g (Z_to_bv 8 0))) with (fg_n g).
  rewrite (fa_ltu (fg_lf st + fg_n g) 65) by lia.
  change (fg_lf st + fg_n g) with (fg_T st g).
  destruct (Z.ltb_spec (fg_T st g) 65) as [T65|T65]; cbv iota.
  - eapply L_join;
      [ | exact (conj Hn1 Hn2) | lia | split; [exact Dff | split; [exact DfS | exact DrS]] | exact DJBh
      | exact OUTh | exact Hf0 | exact FR2 | exact ST2 | exact MU3 | exact WM3 | exact MI2 | exact HSbm2
      | rewrite Hst; exact WRm2 | exact HGm2 ].
    rewrite HCL0. replace (fg_keep st g) with true;
      [reflexivity | symmetry; apply keep_iff; split;
        [exact H6 | split; [exact (proj2 (rf_src_eq st g) (proj1 Iv V0)) | lia]]].
  - eapply (L_drop FgDrop);
      [ rewrite HCL0; destruct (fg_keep st g) eqn:EK;
          [exfalso; apply keep_iff in EK; destruct EK as (_ & _ & ET); lia | reflexivity]
      | reflexivity | exact DfS | exact FR2 | exact ST2 | exact MU3 | exact WM3 | exact MI2
      | rewrite <- Hst; apply fa_rw_of; [exact HSbm2 | rewrite Hst; exact WRm2] ].
Qed.

(* 0x85a48 .. 0x85c14: the frame checks, the block-sum loop, the first/second dispatch. *)
Lemma L_chk : forall j (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
  NZ -> (50 <= len -> bytes_at rsegs mE fr g) -> rw_cells rsegs mE f [CB 72 st] -> OUT -> DJA -> DJB ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) x10 x11 (Z_to_bv 64 len)
             x13 x14 x15 x16 x17 (Z_to_bv 64 pp) (Z_to_bv 64 pa) (Z_to_bv 64 fr) s5 s6 s7 s8 s9 s10 s11
             x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85a48) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
    NZh HF HS0 OUTh DJAh DJBh FR ST MU WM MI.
  destruct (HAF NZh)
    as ((Af & Aa & Ap & An & Happ & DJrt) & SRf & ADf & SRa & ADa & SRp & ADp & R3p & SRn & ADn & R3n).
  pose proof (asan_rt_munch rsegs mE m _ _ off _ _ HRT MU ltac:(unfold sub_fp; intros xx Hxx; exact Hxx)) as HRTm.
  rngf NZh.
  step. step.
  rewrite (fa_ltu len 50) by lia.
  destruct (Z.ltb_spec len 50) as [L50|L50]; cbv iota; [nfail|].
  destruct (HAG NZh L50) as (Ag & SRg & ADg).
  rngg NZh L50.
  pose proof (bytes_at_transport rsegs [(S - 4672, S)] mE m fr g (HF L50) MU
                ltac:(cbn [disjoint_from]; rewrite Hg; destruct DJAh as (_ & _ & DrS); lia)) as HG.
  pose proof (rw_cells_transport rsegs [(S - 4672, S)] mE m f _ HS0 MU WM
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; destruct DJAh as (_ & DfS & _); lia)) as HS.
  clear HF HS0.
  pose proof (bytes_at_bound rsegs m fr g HG) as BG. rewrite Hg in BG.
  step. step. rewrite (u_ltu_negl fr (-19)) by lia. cbv iota.
  step. step. rewrite (u_ltu_negr fr (-16)) by lia. cbn [negb]. cbv iota.
  pose proof (asan_rt_got_read rsegs m _ _ off _ HRTm) as RG.
  pose proof (asan_rt_cell_read rsegs m _ _ off _ HRTm) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  (* the unfolded copy of the image range, for the two 8-byte loads at the literal addresses of those cells *)
  pose proof RIMG as RIMGu. unfold IMG_LO, IMG_HI in RIMGu.
  step. step. step. clear RG RC.
  gshk 0x85a70 16 (Z_to_bv 5 12). gld 16%nat. step. step. gchk 16%nat 16 205.
  step. step. rewrite (u_ltu_negl fr (-18)) by lia. cbv iota.
  gshk 0x85a98 17 (Z_to_bv 5 12). gld 17%nat. step. step. gchk 17%nat 17 234.
  gshk 0x85ab8 18 (Z_to_bv 5 11). gld 18%nat. step. step. gchk 18%nat 18 4.
  step. step. rewrite (u_eqb_negc (fr + 18) (-1)) by lia. cbv iota.
  gshk 0x85ae0 19 (Z_to_bv 5 12). gld 19%nat. step. step. step.
  rewrite rf_b1. change (bv_unsigned (nth 19 g (Z_to_bv 8 0))) with (bat g 19).
  destruct ((bat g 19 =? 1) || (bat g 19 =? 2)) eqn:E19; cbn [negb]; cbv iota.
  2:{ apply orb_false_iff in E19. destruct E19 as [E19a E19b]. apply Z.eqb_neq in E19a, E19b. nfail. }
  apply orb_true_iff in E19. rewrite !Z.eqb_eq in E19.
  ubn (-5). gshk 0x85b0c 22 (Z_to_bv 5 13). gld 22%nat. step. gchk 22%nat 22 0.
  ubn (-6). gshk 0x85b30 23 (Z_to_bv 5 13). gld 23%nat. step. step. gchk 23%nat 23 2.
  ubn (-7). gshk 0x85b58 24 (Z_to_bv 5 13). gld 24%nat. step. gchk 24%nat 24 0.
  ubn (-8). gshk 0x85b7c 25 (Z_to_bv 5 13). gld 25%nat. step. step. gchk 25%nat 25 254.
  ubn (-9). gshk 0x85ba4 26 (Z_to_bv 5 13). gld 26%nat. step. step. step.
  rewrite rf_n. change (bv_unsigned (nth 26 g (Z_to_bv 8 0))) with (fg_n g).
  destruct ((1 <=? fg_n g) && (fg_n g <=? 22)) eqn:EN; cbn [negb]; cbv iota.
  2:{ apply andb_false_iff in EN. destruct EN as [EN|EN]; apply Z.leb_gt in EN; nfail. }
  apply andb_true_iff in EN. destruct EN as [EN1 EN2]. apply Z.leb_le in EN1, EN2.
  pose proof (rf_bytes_skip rsegs m fr g 18 HG ltac:(rewrite Hg; lia)) as HBk.
  change (Z.to_nat 18) with 18%nat in HBk.
  pose proof (asan_shadow_rd_munch rsegs mE m off fr 50 W5 _ SRg MU ltac:(fa_sub)) as SRgm.
  pose proof (asan_addressable_munch rsegs mE m off fr 50 W5 _ ADg SRg MU ltac:(fa_sub)) as ADgm.
  pose proof (fa_sr_sub m off fr 50 18 (Z.of_nat 32) W5 SRgm ltac:(lia) ltac:(lia) ltac:(lia)) as SRk.
  pose proof (fa_ad_sub m off fr 50 18 (Z.of_nat 32) ADgm ltac:(lia) ltac:(lia) ltac:(lia)) as ADk.
  do 4 step.
  eapply (loopB Qf) with (A := fr + 18) (bs := skipn 18 g) (c := 32%nat) (W := W5) (n := 32%nat) (i := 0%nat);
    [ exact HBk | rewrite length_skipn, Hg; lia | lia | lia | exact SRk | exact ADk
    | apply (rng_sub' RNG fr 50); [exact RGr | lia]
    | exact (shw_bytes RNG off fr 50 (fr + 18) (Z.of_nat 32) ltac:(lia) ltac:(lia) ltac:(lia) RGrs)
    | | lia | lia
    | f_equal; lia | f_equal; lia | reflexivity | rewrite unsigned_lit by lia; reflexivity ].
  intros y0 y3 y5 y6 y7.
  remember (psum (skipn 18 g) 32) as ps eqn:Eps.
  assert (PB : 0 <= ps <= 255 * 32) by (rewrite Eps; pose proof (psum_range (skipn 18 g) 32); lia).
  step. step.
  rewrite rf_land255 by lia.
  replace (ps mod 256) with (blocksum (skipn 18 g)) by (unfold blocksum; rewrite Eps; reflexivity).
  clear Eps.
  destruct (Z.eqb_spec (blocksum (skipn 18 g)) 0) as [BS|BS]; cbv iota; [|nfail].
  assert (FRT : fg_fr len g = true) by (apply fr_iff; repeat split; first [assumption | lia]).
  step. step.
  rewrite (rf_beq (nth 19 g (Z_to_bv 8 0)) 1) by lia.
  change (bv_unsigned (nth 19 g (Z_to_bv 8 0))) with (bat g 19).
  destruct (Z.eqb_spec (bat g 19) 1) as [G1|G1]; cbn [negb]; cbv iota.
  - eapply (L_first FgFirst);
      [ rewrite (cl_nn NZh), FRT, (proj2 (Z.eqb_eq _ _) G1); reflexivity | reflexivity
      | split; [exact EN1 | exact EN2] | exact DJAh | exact FR | exact ST | exact MU | exact WM | exact MI
      | exact HS | exact HG ].
  - eapply L_second;
      [ exact NZh | exact FRT | exact G1 | exact DJAh | exact DJBh | exact OUTh | exact FR | exact ST | exact MU
      | exact WM | exact MI | exact HS | exact HG ].
Qed.

(* 0x859e4 .. 0x85a44: prologue and the argument checks. *)
Lemma L_top : forall (sp0 t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) junk,
  sp0 = Z_to_bv 64 S ->
  rw_cells rsegs mE (S + -112) [CB 112 junk] -> stk rsegs mE (S - 4672) (S + -112) -> mem_inv rsegs mE ->
  (NZ -> 50 <= len -> bytes_at rsegs mE fr g) ->
  (NZ -> rw_cells rsegs mE f [CB 72 st] /\ OUT /\ DJA /\ DJB) ->
  evtF rsegs RNG Qf
    (MS (mkR ra sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 pa)
             (Z_to_bv 64 pp) (Z_to_bv 64 pn) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ff (Z_to_bv 64 0x859e4) fc None mE (seg_rom rsegs)).
Proof.
  intros sp0 t0 t1 t2 a6 a7 t3 t4 t5 t6 junk -> FR ST MI HFg HO.
  pose proof (munch_refl [(S - 4672, S)] mE) as MU.
  pose proof (wmono_refl rsegs mE) as WM.
  do 14 step.
  step. step. step.
  rewrite (fa_beq f 0) by lia. destruct (Z.eqb_spec f 0) as [Z0|Z0]; cbv iota; [rfail|].
  step. step.
  rewrite (fa_beq fr 0) by lia. destruct (Z.eqb_spec fr 0) as [Z1|Z1]; cbv iota; [rfail|].
  step. step.
  rewrite (fa_beq pa 0) by lia. destruct (Z.eqb_spec pa 0) as [Z2|Z2]; cbv iota; [rfail|].
  step. step.
  rewrite (fa_beq pp 0) by lia. destruct (Z.eqb_spec pp 0) as [Z3|Z3]; cbv iota; [rfail|].
  step. step.
  rewrite (fa_beq pn 0) by lia. destruct (Z.eqb_spec pn 0) as [Z4|Z4]; cbv iota; [rfail|].
  assert (NZh : NZ) by (unfold NZ; tauto).
  destruct (HO NZh) as (HS0 & OUTh & DJAh & DJBh).
  eapply L_chk; [ exact NZh | exact (HFg NZh) | exact HS0 | exact OUTh | exact DJAh | exact DJBh
                | exact FR | exact ST | exact MU | exact WM | exact MI ].
Qed.

End P.

(* The form this file's run proof is written against: the owner's premises with RNG bound last and the guarded
   rng premises of a buffer conjoined.  The owner's text follows from it at the end of this file. *)
Definition fragment_contract_F_conj : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f fr len pa pp pn : Z) (st g : list byte)
         (RNG : footprint),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 fr -> a2 = Z_to_bv 64 len ->
    a3 = Z_to_bv 64 pa -> a4 = Z_to_bv 64 pp -> a5 = Z_to_bv 64 pn ->
    0 <= f < 2^64 -> 0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length g = 50%nat -> length st = 72%nat ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m fr g) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (fr, fr + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m fr 50) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    (* the footprint *)
    rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    sh_word_rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len ->
       rng RNG fr 50 /\
       rng RNG (shadow_addr fr / 8 * 8) (shadow_addr (fr + 50 - 1) / 8 * 8 + 8 - shadow_addr fr / 8 * 8)) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rng RNG f 72 /\
       rng RNG (shadow_addr f / 8 * 8) (shadow_addr (f + 72 - 1) / 8 * 8 + 8 - shadow_addr f / 8 * 8) /\
       rng RNG pa 2 /\
       rng RNG (shadow_addr pa / 8 * 8) (shadow_addr (pa + 2 - 1) / 8 * 8 + 8 - shadow_addr pa / 8 * 8) /\
       rng RNG pp 8 /\
       rng RNG (shadow_addr pp / 8 * 8) (shadow_addr (pp + 8 - 1) / 8 * 8 + 8 - shadow_addr pp / 8 * 8) /\
       rng RNG pn 8 /\
       rng RNG (shadow_addr pn / 8 * 8) (shadow_addr (pn + 8 - 1) / 8 * 8 + 8 - shadow_addr pn / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_ret (fg_class f fr pa pp pn len st g)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp) (fg_class f fr pa pp pn len st g))
           m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) /\
         fg_mem f pa pp pn st g (fg_class f fr pa pp pn len st g) m' /\
         asan_cells m' /\ shadow_rw m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_FRAGMENT) fc None m (seg_rom rsegs)).

Theorem reac_ctrl_identity_fragment_holds_F_conj :
  asan_memcpy_contract_F -> bcmp_wrap_contract_F -> reac_ctrl_record_cksum_verify_contract_F ->
  fragment_contract_F_conj.
Proof.
  intros MCPY BCMPw CKV. unfold fragment_contract_F_conj.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m f fr len pa pp pn st g RNG Ea0 Ea1 Ea2 Ea3 Ea4 Ea5 Hf Hfr Hlen Hpa Hpp Hpn Hspmod STk Hg Hst
    HFrec HOrec MI HCE HSW Hlo Hhi HAGc HAFc HB1c HB2c HB3c HB4c HB5c RBYc RIMGc RSTKc RWSc RGGc RGFc.
  subst a0 a1 a2 a3 a4 a5.
  unfold REAC_CTRL_IDENTITY_FRAGMENT_K, REAC_CTRL_IDENTITY_FRAGMENT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  (* the window's shadow word span, in the cover form shw (at off = ASAN_K) that the run's proof names *)
  assert (RSTKSc : shw RNG ASAN_K (bv_unsigned sp - 4672) 4672)
    by (destruct RWSc as [E|H]; [discriminate E | exact H]).
  assert (Esp : sp = Z_to_bv 64 (bv_unsigned sp)) by (apply bv_eq; rewrite unsigned_lit by lia; reflexivity).
  carve_frame 112%nat STk.
  rewrite Esp.
  eapply evtF_mono.
  - eapply (L_top MCPY BCMPw CKV ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f fr len pa pp pn
                  (bv_unsigned sp) ASAN_K st g RNG);
      [ exact Hf | exact Hfr | exact Hlen | exact Hpa | exact Hpp | exact Hpn
      | split; [unfold HIGHMEM_BEG in Hlo; exact Hlo | unfold APPMEM_END in Hhi; exact Hhi]
      | exact Hg | exact Hst | exact HCE | exact HSW
      | apply rt_asan_rt; [exact HCE | intros x Hx; cbn [outside]; split; [|exact I];
          clear -Hx Hlo; unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia]
      | intros _ _ _ _ _; exact (conj HB1c (conj HB2c (conj HB3c (conj HB4c HB5c))))
      | intros NZh; unfold NZ in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          pose proof (HAFc N1 N2 N3 N4 N5) as ASFh;
          destruct ASFh as (Af & Apa & App & Apn & Happ & Hdj);
          pose proof (fa_so5 m f pa pp pn (bv_unsigned sp - 4672) (bv_unsigned sp) Af Apa App Apn Hlo Hhi) as SO;
          split; [exact (conj Af (conj Apa (conj App (conj Apn (conj Happ Hdj)))))|];
          unfold SRF, W5;
          split; [apply rt_shadow_rd; [exact Af | exact SO] |];
          split; [apply rt_addressable; exact Af |];
          split; [apply rt_shadow_rd; [exact Apa | exact SO] |];
          split; [apply rt_addressable; exact Apa |];
          split; [apply rt_shadow_rd; [exact App | exact SO] |];
          split; [apply rt_addressable; exact App |];
          split; [apply rt_rt3; exact App |];
          split; [apply rt_shadow_rd; [exact Apn | exact SO] |];
          split; [apply rt_addressable; exact Apn |];
          apply rt_rt3; exact Apn
      | intros NZh L50; unfold NZ in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          pose proof (HAGc N1 N2 N3 N4 N5 L50) as Afr;
          pose proof (HAFc N1 N2 N3 N4 N5) as (Af & Apa & App & Apn & _);
          pose proof (fa_so5 m f pa pp pn (bv_unsigned sp - 4672) (bv_unsigned sp) Af Apa App Apn Hlo Hhi) as SO;
          unfold ASG, W5; split; [exact Afr | split; [apply rt_shadow_rd; [exact Afr | exact SO]
                                                      | apply rt_addressable; exact Afr]]
      | reflexivity | exact RBYc | exact RIMGc | exact RSTKc | exact RSTKSc
      | intros NZh; unfold NZ in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          unfold RGF; exact (RGFc N1 N2 N3 N4 N5)
      | intros NZh L50; unfold NZ in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          unfold RGG; exact (RGGc N1 N2 N3 N4 N5 L50)
      | reflexivity | exact FR | exact STk | exact MI
      | intros NZh L50; unfold NZ in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          exact (HFrec N1 N2 N3 N4 N5 L50)
      | intros NZh; unfold NZ in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          destruct (HOrec N1 N2 N3 N4 N5) as (HS & M2 & M8 & M8' & W2 & W8 & W8' & DJ);
          cbn [all_dj dj_from] in DJ;
          split; [exact HS|]; split; [unfold OUT; clear -M2 M8 M8' W2 W8 W8'; tauto|];
          clear -DJ; unfold DJA, DJB; repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; assumption ].
  - intros ms' HQ. unfold Qf in HQ. rewrite !(unsigned_lit (bv_unsigned sp)) by lia. exact HQ.
Qed.


(* The owner's text (reac_ctrl_identity_fragment_contract_F of reac_ctrl_identity_fragment_c.v) from the form
   above: the same premises, with RNG bound first and one guarded rng premise per buffer and per shadow cover.
   The shadow covers differ only in how the last byte of a buffer is written (p + n - 1 against the literal). *)
Theorem reac_ctrl_identity_fragment_holds_F :
  asan_memcpy_contract_F -> bcmp_wrap_contract_F -> reac_ctrl_record_cksum_verify_contract_F ->
  reac_ctrl_identity_fragment_contract_F.
Proof.
  intros MCPY BCMPw CKV.
  pose proof (reac_ctrl_identity_fragment_holds_F_conj MCPY BCMPw CKV) as HC.
  unfold fragment_contract_F_conj in HC. unfold reac_ctrl_identity_fragment_contract_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m f fr len pa pp pn st g Ea0 Ea1 Ea2 Ea3 Ea4 Ea5 Hf Hfr Hlen Hpa Hpp Hpn Hspmod STk Hg Hst
    HFrec HOrec MI HCE HSW Hlo Hhi HAGc HAFc HB1c HB2c HB3c HB4c HB5c RBYc RIMGc RSTKc RWSc
    RGfr RGfrs RGf RGfs RGpa RGpas RGpp RGpps RGpn RGpns.
  apply (HC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            F fc m f fr len pa pp pn st g RNG); try assumption.
  - intros N1 N2 N3 N4 N5 L50.
    split; [exact (RGfr N1 N2 N3 N4 N5 L50)|].
    replace (fr + 50 - 1) with (fr + 49) by lia. exact (RGfrs N1 N2 N3 N4 N5 L50).
  - intros N1 N2 N3 N4 N5.
    split; [exact (RGf N1 N2 N3 N4 N5)|].
    split; [replace (f + 72 - 1) with (f + 71) by lia; exact (RGfs N1 N2 N3 N4 N5)|].
    split; [exact (RGpa N1 N2 N3 N4 N5)|].
    split; [replace (pa + 2 - 1) with (pa + 1) by lia; exact (RGpas N1 N2 N3 N4 N5)|].
    split; [exact (RGpp N1 N2 N3 N4 N5)|].
    split; [replace (pp + 8 - 1) with (pp + 7) by lia; exact (RGpps N1 N2 N3 N4 N5)|].
    split; [exact (RGpn N1 N2 N3 N4 N5)|].
    replace (pn + 8 - 1) with (pn + 7) by lia. exact (RGpns N1 N2 N3 N4 N5).
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Route (C), the CALLEE case (a Theorem Labs lane 09:58Z): reac_ctrl_identity_fragment_holds_F_on, this run
   against its three callees' NARROWED contracts, for the narrowed statement reac_ctrl_identity_fragment_contract_F_on
   of reac_ctrl_identity_fragment_c.v. Everything above stays as it is: Section P's run takes the universal
   shadow_rw premise, which the _on statement does not give. Section P_on is Section P's script, step for step, with
   every name of the Section suffixed _on (a scripted copy) and these changes only:
     - the callee hypotheses are the _on forms: asan_memcpy_contract_F_on, bcmp_wrap_contract_F_on and
       reac_ctrl_record_cksum_verify_contract_F_on;
     - the shadow premise HSW is shadow_rw_on R mE, R = reac_ctrl_identity_fragment_shadow_R;
     - rt0_on / rtW_on / rt_post_on give, in place of shadow_rw, the transport of every shadow region present at mE
       (B.ShadowRwOnK.fl_shadow_rw_on across the run's munch: the run stores no shadow byte), and Qf_on's post is
       that transport (the _on post form);
     - at each call, the callee's region is cut out of R by ShadowRwOn.shadow_rw_on_mono and carried to the call's
       memory by that transport: rin_first_on, rin_bcmp_on and rin_join_on show that each callee region is one arm
       of R under the guards of its path. reac_ctrl_record_cksum_verify's _on contract has no shadow premise, so its
       bullet is gone;
     - the bcmp wrapper's _on contract writes its two shadow covers as 8 * (y / 8), so those two bullets rewrite
       Z.mul_comm 8 before the old cover lemma.
   The two closing theorems follow the old ones: fragment_contract_F_conj_on, then the owner's text. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOnK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_memcpy_cF_on bcmp_wrap_c_on.

Section P_on.
Hypothesis MCPY : asan_memcpy_contract_F_on.
Hypothesis BCMPw : bcmp_wrap_contract_F_on.
Hypothesis CKV : reac_ctrl_record_cksum_verify_contract_F_on.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Ff : bvmap 5 word) (fc : bv 32)
  (mE : word -> option byte) (f fr len pa pp pn S off : Z) (st g : list byte) (RNG : footprint).
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rfr : 0 <= fr < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis Rpa : 0 <= pa < 2^64.
Hypothesis Rpp : 0 <= pp < 2^64.
Hypothesis Rpn : 0 <= pn < 2^64.
Hypothesis RS : 0x10007fff8000 <= S - 4672 /\ S <= 0x800000000000.
Hypothesis Hg : length g = 50%nat.
Hypothesis Hst : length st = 72%nat.
Hypothesis HCE : asan_cells mE.
Hypothesis HSW : B.ShadowRwOn.shadow_rw_on (reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g) mE.
Hypothesis HRT : asan_rt rsegs mE GOT_CELL_K CELL_K off [(S - 4672, S)].
Hypothesis HGOT : f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
  bytes_at rsegs mE REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mE REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs mE GOT_CF (le8 (wa CF)) /\ bytes_at rsegs mE (CF + 254) [Z_to_bv 8 1] /\
  bytes_at rsegs mE (CF + 255) [Z_to_bv 8 1].

Local Notation CL := (fg_class f fr pa pp pn len st g).
Local Notation FRc j :=
  [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Notation FRj :=
  [C8 (Z_to_bv 64 (18446744073709551615 - (f + 8))); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4;
   C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Notation Jc := (le8 (Z_to_bv 64 (18446744073709551615 - (f + 8)))).

Definition Qf_on : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_ret CL))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             Ff (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch (fg_fp 4672 f pa pp pn S CL) mE m' /\ wmono rsegs mE m' /\ mem_inv rsegs m' /\
    stk rsegs m' (S - 4672) S /\ fg_mem f pa pp pn st g CL m' /\ asan_cells m' /\
    (forall P : Z -> Prop, B.ShadowRwOn.shadow_rw_on P mE -> B.ShadowRwOn.shadow_rw_on P m').

Definition NZ_on : Prop := f <> 0 /\ fr <> 0 /\ pa <> 0 /\ pp <> 0 /\ pn <> 0.
Definition DJA_on : Prop :=
  (f + 72 <= fr \/ fr + 50 <= f) /\ (f + 72 <= S - 4672 \/ S <= f) /\ (fr + 50 <= S - 4672 \/ S <= fr).
Definition DJB_on : Prop :=
  (f + 72 <= pa \/ pa + 2 <= f) /\ (f + 72 <= pp \/ pp + 8 <= f) /\ (f + 72 <= pn \/ pn + 8 <= f) /\
  (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
  (pa + 2 <= S - 4672 \/ S <= pa) /\ (pp + 8 <= S - 4672 \/ S <= pp) /\ (pn + 8 <= S - 4672 \/ S <= pn).
Definition OUT_on : Prop :=
  wr_at rsegs mE pa 2 /\ wr_at rsegs mE pp 8 /\ wr_at rsegs mE pn 8 /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0.

Definition W5_on : list (Z * Z) := [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (S - 4672, S)].

Definition ASF_on : Prop :=
  addressable mE f 72 /\ addressable mE pa 2 /\ addressable mE pp 8 /\ addressable mE pn 8 /\ app_mem (f + 78) /\
  dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)].
Definition SRF_on : Prop :=
  asan_shadow_rd rsegs mE off f 72 W5_on /\ asan_addressable rsegs mE off f 72 /\
  asan_shadow_rd rsegs mE off pa 2 W5_on /\ asan_addressable rsegs mE off pa 2 /\
  asan_shadow_rd rsegs mE off pp 8 W5_on /\ asan_addressable rsegs mE off pp 8 /\ asan_rt3 rsegs mE off pp 8 /\
  asan_shadow_rd rsegs mE off pn 8 W5_on /\ asan_addressable rsegs mE off pn 8 /\ asan_rt3 rsegs mE off pn 8.
Definition ASG_on : Prop :=
  addressable mE fr 50 /\ asan_shadow_rd rsegs mE off fr 50 W5_on /\ asan_addressable rsegs mE off fr 50.
Hypothesis HAF : NZ_on -> ASF_on /\ SRF_on.
Hypothesis HAG : NZ_on -> 50 <= len -> ASG_on.

(* The footprint of this run, region by region: the image (every fetch and every absolute cell), the stack
   window of this frame and of the callees' frames below it, and each buffer with the 8-aligned WORD cover of
   its shadow bytes.  RGF_on and RGG_on hold under the same guards as ASF_on and ASG_on. *)
Definition RGF_on : Prop :=
  rng RNG f 72 /\ shw RNG off f 72 /\
  rng RNG pa 2 /\ shw RNG off pa 2 /\
  rng RNG pp 8 /\ shw RNG off pp 8 /\
  rng RNG pn 8 /\ shw RNG off pn 8.
Definition RGG_on : Prop :=
  rng RNG fr 50 /\ shw RNG off fr 50.
(* The run reads the shadow offset from the runtime cell; on this image it is ASAN_K, so the covers above are
   the covers over shadow_addr that the contract states, and the callees' contracts speak of shadow_addr. *)
Hypothesis Hoff : off = ASAN_K.
(* Route 1 one level down (the bcmp wrapper's footprint contract) weakens a byte-wise footprint to a union
   of rng ranges, so that contract takes a footprint that is decided byte by byte (lib/Lib/RngBytes.v). *)
Hypothesis RBY : rng_bytes RNG.
Hypothesis RIMG : rng RNG IMG_LO (IMG_HI - IMG_LO).
Hypothesis RSTK : rng RNG (S - 4672) 4672.
Hypothesis RSTKS : shw RNG off (S - 4672) 4672.
Hypothesis RBF : NZ_on -> RGF_on.
Hypothesis RBG : NZ_on -> 50 <= len -> RGG_on.

(* Under the non-zero guard: the buffer ranges, their shadow word covers, and the byte range of each buffer's
   shadow bytes (what the single-byte shadow checks of this function read). *)
Ltac rngf_on NZh :=
  let H := fresh "RGFh" in
  pose proof (RBF NZh) as H; unfold RGF_on in H;
  destruct H as (RGf & RGfs & RGa & RGas & RGp & RGps & RGn & RGns);
  pose proof (shw_bytes RNG off f 72 f 72 ltac:(lia) ltac:(lia) ltac:(lia) RGfs) as RGfb;
  pose proof (shw_bytes RNG off pa 2 pa 2 ltac:(lia) ltac:(lia) ltac:(lia) RGas) as RGab;
  pose proof (shw_bytes RNG off pp 8 pp 8 ltac:(lia) ltac:(lia) ltac:(lia) RGps) as RGpb;
  pose proof (shw_bytes RNG off pn 8 pn 8 ltac:(lia) ltac:(lia) ltac:(lia) RGns) as RGnb.
Ltac rngg_on NZh L50 :=
  let H := fresh "RGGh" in
  pose proof (RBG NZh L50) as H; unfold RGG_on in H;
  destruct H as (RGr & RGrs);
  pose proof (shw_bytes RNG off fr 50 fr 50 ltac:(lia) ltac:(lia) ltac:(lia) RGrs) as RGrb.

Lemma dj_of_on : all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (fr, fr + 50); (S - 4672, S)] ->
  DJA_on /\ DJB_on.
Proof.
  intros H. cbn [all_dj dj_from] in H.
  destruct H as ((Dfa & Dfp & Dfn & Dff & DfS & _) & (Dap & Dan & Daf & DaS & _) & (Dpn & Dpf & DpS & _) &
                 (Dnf & DnS & _) & (DrS & _) & _).
  split; [exact (conj Dff (conj DfS DrS))|].
  exact (conj Dfa (conj Dfp (conj Dfn (conj Dap (conj Dan (conj Dpn (conj DaS (conj DpS DnS)))))))).
Qed.

Lemma cl_nz_on : CL <> FgRefuse -> NZ_on.
Proof. intros H. unfold NZ_on. repeat split; intros E; apply H; apply rf_class_refuse; tauto. Qed.

Lemma cl_nn_on : NZ_on -> CL =
  if negb (fg_fr len g) then FgNone
  else if bat g 19 =? 1 then FgFirst
  else if negb (fg_keep st g) then FgDrop
  else if negb (fg_close st g) then FgJoin
  else FgClose.
Proof. intros (H1 & H2 & H3 & H4 & H5). apply rf_class_nn; assumption. Qed.

Lemma cl_k_on : NZ_on -> fg_fr len g = true -> bat g 19 <> 1 ->
  CL = if negb (fg_keep st g) then FgDrop else if fg_close st g then FgClose else FgJoin.
Proof.
  intros NZh FRT B19. rewrite (cl_nn_on NZh), FRT, (proj2 (Z.eqb_neq _ _) B19). cbn [negb].
  destruct (fg_keep st g), (fg_close st g); reflexivity.
Qed.

(* The callees' shadow regions inside this run's region R (reac_ctrl_identity_fragment_shadow_R), one lemma per arm
   of R: the two __asan_memcpy copies of the first-record path, the bcmp wrapper of the second-record path, and the
   __asan_memcpy copy of the join path. Each is R's arm under that path's guards. *)
Lemma rin_first_on : NZ_on -> fg_fr len g = true -> bat g 19 = 1 ->
  forall (a0 a1 a2 : word),
  (bv_unsigned a0 = f /\ bv_unsigned a1 = fr + 6 /\ bv_unsigned a2 = 6) \/
  (bv_unsigned a0 = f + 8 /\ bv_unsigned a1 = fr + 27 /\ bv_unsigned a2 = fg_n g) ->
  forall a, B.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R a0 a1 a2 a -> reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g a.
Proof.
  intros (N1 & N2 & N3 & N4 & N5) FRT B19 a0 a1 a2 Hv a Ha.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. change (bv_modulus 64) with (2^64) in R0, R1, R2.
  unfold reac_ctrl_identity_fragment_shadow_R, B.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R in *.
  refine (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj FRT (or_introl (conj B19 _)))))))).
  destruct Hv as [(E0 & E1 & E2) | (E0 & E1 & E2)]; rewrite E0, E1, E2 in Ha; [left | right];
    rewrite !unsigned_lit by lia; exact Ha.
Qed.

Lemma rin_bcmp_on : NZ_on -> fg_fr len g = true -> bat g 19 <> 1 -> fg_hf st <> 0 ->
  forall a, B.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R f (fr + 6) 6 a -> reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g a.
Proof.
  intros (N1 & N2 & N3 & N4 & N5) FRT B19 H6 a Ha. unfold reac_ctrl_identity_fragment_shadow_R.
  exact (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj FRT (or_intror (conj B19 (conj H6 (or_introl Ha)))))))))).
Qed.

Lemma rin_join_on : NZ_on -> fg_fr len g = true -> bat g 19 <> 1 -> fg_hf st <> 0 -> fg_keep st g = true ->
  forall (a0 a1 a2 : word),
  bv_unsigned a0 = f + 8 + fg_lf st -> bv_unsigned a1 = fr + 27 -> bv_unsigned a2 = fg_n g ->
  forall a, B.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R a0 a1 a2 a -> reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g a.
Proof.
  intros (N1 & N2 & N3 & N4 & N5) FRT B19 H6 EK a0 a1 a2 E0 E1 E2 a Ha.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. change (bv_modulus 64) with (2^64) in R0, R1, R2.
  unfold reac_ctrl_identity_fragment_shadow_R, B.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R in *.
  refine (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj FRT
            (or_intror (conj B19 (conj H6 (or_intror (conj EK _))))))))))).
  rewrite E0, E1, E2 in Ha. rewrite !unsigned_lit by lia. exact Ha.
Qed.

(* The runtime's cells survive a run that writes only inside the window, or inside W5_on, and so does every shadow
   region present at mE (B.ShadowRwOnK.fl_shadow_rw_on: the run writes no shadow byte). *)
Lemma rt0_on : forall mc, munch [(S - 4672, S)] mE mc -> wmono rsegs mE mc ->
  asan_cells mc /\ (forall P : Z -> Prop, B.ShadowRwOn.shadow_rw_on P mE -> B.ShadowRwOn.shadow_rw_on P mc).
Proof.
  intros mc MU WM. split.
  - apply (fl_asan_cells _ mE mc HCE MU). intros x Hx. cbn [outside]. unfold RT_LO, RT_HI in Hx.
    split; [lia | exact I].
  - intros P HP. apply (B.ShadowRwOnK.fl_shadow_rw_on P _ mE mc HP MU WM). intros x Hx. cbn [outside]. split; [|exact I].
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hx. lia.
Qed.

Lemma so5_on : NZ_on -> forall x, in_shadow x -> outside W5_on x.
Proof.
  intros NZh. destruct (HAF NZh) as ((Af & Aa & Ap & An & _) & _).
  apply (fa_so5 mE f pa pp pn); try assumption; unfold HIGHMEM_BEG, APPMEM_END; lia.
Qed.

Lemma ro5_on : NZ_on -> forall x, RT_LO <= x < RT_HI -> outside W5_on x.
Proof.
  intros NZh. destruct (HAF NZh) as ((_ & _ & _ & _ & _ & DJ) & _).
  apply (fa_ro5 f pa pp pn (S - 4672) S); [unfold HIGHMEM_BEG; lia | exact DJ].
Qed.

Lemma rtW_on : forall W' mc, NZ_on -> munch W' mE mc -> sub_fp W' W5_on -> wmono rsegs mE mc ->
  asan_cells mc /\ (forall P : Z -> Prop, B.ShadowRwOn.shadow_rw_on P mE -> B.ShadowRwOn.shadow_rw_on P mc).
Proof.
  intros W' mc NZh MU Hs WM. split.
  - apply (fl_asan_cells W' mE mc HCE MU). intros x Hx. apply Hs. exact (ro5_on NZh x Hx).
  - intros P HP. apply (B.ShadowRwOnK.fl_shadow_rw_on P W' mE mc HP MU WM). intros x Hx. apply Hs.
    exact (so5_on NZh x Hx).
Qed.

Lemma rt_post_on : forall c m, c = CL -> munch (fg_fp 4672 f pa pp pn S c) mE m -> wmono rsegs mE m ->
  asan_cells m /\ (forall P : Z -> Prop, B.ShadowRwOn.shadow_rw_on P mE -> B.ShadowRwOn.shadow_rw_on P m).
Proof.
  intros c m Hc MU WM.
  destruct c; cbn [fg_fp] in MU; try exact (rt0_on m MU WM);
    (eapply (rtW_on _ m); [apply cl_nz_on; rewrite <- Hc; discriminate | exact MU
                      | unfold sub_fp, W5_on; cbn [outside]; intros; tauto | exact WM]).
Qed.

Lemma fa_fr_c8_on : forall (mm : word -> option byte) (A : Z) v rest,
  rw_cells rsegs mm A (C8 v :: rest) -> rw_cells rsegs mm A (CB 8 (le8 v) :: rest).
Proof.
  intros mm A v rest [[Hwf Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf] in Hwf |- *. split; [rewrite length_le8; reflexivity | exact (proj2 Hwf)].
  - cbn [cells_bytes cbytes] in Hb |- *. exact Hb.
  - cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.

Lemma fa_sowf_on : NZ_on -> forall x, in_shadow x -> outside [(f, f + 72); (S - 4672, S)] x.
Proof. intros NZh x Hx. pose proof (so5_on NZh x Hx) as H. unfold W5_on in H. cbn [outside] in H |- *. tauto. Qed.
Lemma fa_rowf_on : NZ_on -> forall x, RT_LO <= x < RT_HI -> outside [(f, f + 72); (S - 4672, S)] x.
Proof. intros NZh x Hx. pose proof (ro5_on NZh x Hx) as H. unfold W5_on in H. cbn [outside] in H |- *. tauto. Qed.

(* A shadow byte read of the j-th byte (X = a + j) of an addressable range at the current memory m. *)
Lemma fa_rd1_on : forall (m : word -> option byte) (W' : list (Z * Z)) (a n j X : Z),
  asan_shadow_rd rsegs mE off a n W5_on -> asan_addressable rsegs mE off a n ->
  munch W' mE m -> sub_fp W' W5_on -> 0 <= j < n -> X = a + j ->
  exists k : byte, ov_read_bytes rsegs m (wa (X / 8 + off)) 1 = Some [k]
    /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros m W' a n j X SR AD MU SUB Hj ->.
  pose proof (asan_shadow_rd_munch rsegs mE m off a n W5_on W' SR MU SUB) as SR'.
  pose proof (asan_addressable_munch rsegs mE m off a n W5_on W' AD SR MU SUB) as AD'.
  destruct (asan_shadow_read rsegs m off a n W5_on j SR' Hj) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [exact (AD' j k Hj BK) | apply rc_byte_signed].
Qed.

Lemma fa_rdb_on : forall (m : word -> option byte) (W' : list (Z * Z)) (a n j X : Z),
  asan_shadow_rd rsegs mE off a n W5_on -> asan_addressable rsegs mE off a n ->
  munch W' mE m -> sub_fp W' W5_on -> 0 <= j < n -> X = a + j ->
  exists k : byte, ov_read_bytes rsegs m (wa (X / 8 + off)) 1 = Some [k]
    /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128
    /\ 0 <= X / 8 + off < 2^64.
Proof.
  intros m W' a n j X SR AD MU SUB Hj ->.
  pose proof (asan_shadow_rd_munch rsegs mE m off a n W5_on W' SR MU SUB) as SR'.
  pose proof (asan_addressable_munch rsegs mE m off a n W5_on W' AD SR MU SUB) as AD'.
  destruct (asan_shadow_read rsegs m off a n W5_on j SR' Hj) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [exact (AD' j k Hj BK)|]. split; [apply rc_byte_signed|].
  destruct BK as (Hlo & Hhi & _). unfold asan_shadow in Hlo, Hhi. cbn [length] in Hhi. lia.
Qed.

Lemma fa_rd2_on : forall (m : word -> option byte) (W' : list (Z * Z)) (a n j X : Z),
  asan_shadow_rd rsegs mE off a n W5_on -> asan_addressable rsegs mE off a n ->
  munch W' mE m -> sub_fp W' W5_on -> 0 <= j -> j + 2 <= n -> X = a + j -> X mod 8 + 2 <= 8 ->
  exists k : byte, ov_read_bytes rsegs m (wa (X / 8 + off)) 1 = Some [k]
    /\ (bv_signed k = 0 \/ X mod 8 + 1 < bv_signed k) /\ -128 <= bv_signed k < 128
    /\ 0 <= X / 8 + off < 2^64.
Proof.
  intros m W' a n j X SR AD MU SUB Hj Hjn -> Hm.
  pose proof (asan_shadow_rd_munch rsegs mE m off a n W5_on W' SR MU SUB) as SR'.
  pose proof (asan_addressable_munch rsegs mE m off a n W5_on W' AD SR MU SUB) as AD'.
  destruct (asan_shadow_read rsegs m off a n W5_on j SR' ltac:(lia)) as (k & RK & BK).
  pose proof (asan_check_lt rsegs m off a n j 2 k AD' Hj ltac:(lia) Hjn ltac:(lia) BK) as OK.
  exists k. split; [exact RK|]. split; [destruct OK as [E|E]; [left; exact E | right; lia]|].
  split; [apply rc_byte_signed|].
  destruct BK as (Hlo & Hhi & _). unfold asan_shadow in Hlo, Hhi. cbn [length] in Hhi. lia.
Qed.

Lemma fa_rd8_on : forall (m : word -> option byte) (W' : list (Z * Z)) (a n j X : Z),
  asan_shadow_rd rsegs mE off a n W5_on -> asan_addressable rsegs mE off a n -> asan_rt3 rsegs mE off a n ->
  munch W' mE m -> sub_fp W' W5_on -> 0 <= j -> j + 8 <= n -> X = a + j -> X mod 8 = 0 ->
  exists k : byte, ov_read_bytes rsegs m (wa (X / 8 + off)) 1 = Some [k] /\ bv_unsigned k = 0
    /\ 0 <= X / 8 + off < 2^64.
Proof.
  intros m W' a n j X SR AD R3 MU SUB Hj Hjn -> Hm.
  pose proof (asan_shadow_rd_munch rsegs mE m off a n W5_on W' SR MU SUB) as SR'.
  pose proof (asan_addressable_munch rsegs mE m off a n W5_on W' AD SR MU SUB) as AD'.
  pose proof (asan_rt3_munch rsegs mE m off a n W5_on W' R3 SR MU SUB) as R3'.
  destruct (asan_shadow_read rsegs m off a n W5_on j SR' ltac:(lia)) as (k & RK & BK).
  pose proof (asan_check_8 rsegs m off a n j k AD' R3' Hj Hjn Hm BK) as K0.
  exists k. split; [exact RK|]. split; [exact (rc_signed0_unsigned0 k K0)|].
  destruct BK as (Hlo & Hhi & _). unfold asan_shadow in Hlo, Hhi. cbn [length] in Hhi. lia.
Qed.

Lemma fa_rd1m_on : forall (m : word -> option byte) (a n j X : Z) (W : list (Z * Z)),
  asan_shadow_rd rsegs m off a n W -> asan_addressable rsegs m off a n -> 0 <= j < n -> X = a + j ->
  exists k : byte, ov_read_bytes rsegs m (wa (X / 8 + off)) 1 = Some [k]
    /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros m a n j X W SR AD Hj ->.
  destruct (asan_shadow_read rsegs m off a n W j SR Hj) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [exact (AD j k Hj BK) | apply rc_byte_signed].
Qed.

Lemma fa_sr_sub_on : forall (m : word -> option byte) (off' a n k n' : Z) (W : list (Z * Z)),
  asan_shadow_rd rsegs m off' a n W -> 0 <= k -> 0 <= n' -> k + n' <= n ->
  asan_shadow_rd rsegs m off' (a + k) n' W.
Proof.
  intros m off' a n k n' W SR Hk Hn' Hkn i Hi.
  replace (a + k + i) with (a + (k + i)) by lia. apply SR. lia.
Qed.

Lemma fa_ad_sub_on : forall (m : word -> option byte) (off' a n k n' : Z),
  asan_addressable rsegs m off' a n -> 0 <= k -> 0 <= n' -> k + n' <= n ->
  asan_addressable rsegs m off' (a + k) n'.
Proof.
  intros m off' a n k n' AD Hk Hn' Hkn i ki Hi HB.
  replace (a + k + i) with (a + (k + i)) in HB by lia.
  replace (a + k + i) with (a + (k + i)) by lia. apply (AD (k + i) ki); [lia | exact HB].
Qed.

Ltac fa_sub_on := unfold sub_fp, W5_on; intro; cbn [outside]; tauto.

Ltac bjoin_on G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.
Ltac steps_to_on P :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 P) _ _ _ _) => idtac
  | _ => step; steps_to_on P
  end.

Ltac chk1_on X r SH :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  step; rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
  step; step; clear RK; step;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
  lazymatch goal with
  | |- evtF ?segs ?RN ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RN Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin_on G r
        | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7; step;
          rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
          replace (X mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia);
          bjoin_on G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac chk1p_on X r SH :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in let HB := fresh "HB" in
  destruct SH as (k & RK & OK & KR & HB);
  step; clear RK; step;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
  lazymatch goal with
  | |- evtF ?segs ?RN ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RN Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin_on G r
        | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7; step;
          rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
          replace (X mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia);
          bjoin_on G r ]
      | intros ?; simp_regs; clear OK KR HB ]
  end.

Ltac chk_if_on X r k OK :=
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
  lazymatch goal with
  | |- evtF ?segs ?RN ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RN Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin_on G r
        | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7; step;
          rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
          replace (X mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia);
          bjoin_on G r ]
      | intros ?; simp_regs ]
  end.

Ltac chk_if2_on X r k OK :=
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
  lazymatch goal with
  | |- evtF ?segs ?RN ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RN Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin_on G r
        | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7;
          step; rewrite ?(unsigned_lit (X mod 8)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
          step;
          rewrite (rc_lts_signed (X mod 8 + 1) (bv_signed k)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
          replace (X mod 8 + 1 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia);
          bjoin_on G r ]
      | intros ?; simp_regs ]
  end.

(* +0x238 .. the epilogue (0x85c1c). *)
Lemma L_epi_on : forall c j (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                         x28 x29 x30 x31 : word) m,
  c = CL -> x10 = Z_to_bv 64 (fg_ret c) ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch (fg_fp 4672 f pa pp pn S c) mE m -> wmono rsegs mE m ->
  mem_inv rsegs m -> fg_mem f pa pp pn st g c m ->
  evtF rsegs RNG Qf_on
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
             x24 x25 x26 x27 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85c1c) fc None m (seg_rom rsegs)).
Proof.
  intros c j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m
    Hc Hx FR ST MU WM MI FM.
  destruct (rt_post_on c m Hc MU WM) as [AC SR].
  subst c x10.
  pose proof (stk_release rsegs m _ _ _ ST FR ltac:(lia)) as ST'.
  cbn [cells_size csize Nat.add] in ST'. replace (S + -112 + Z.of_nat 112) with S in ST' by lia. clear ST.
  do 15 step.
  try replace (S + -112 + 112) with S by lia.
  apply evtF_done. unfold Qf_on.
  do 14 eexists. exists m. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact FM|].
  split; [exact AC | exact SR].
Qed.

Lemma L_ret0_on : forall c j (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                          x28 x29 x30 x31 : word) m,
  c = CL -> fg_ret c = 0 ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch (fg_fp 4672 f pa pp pn S c) mE m -> wmono rsegs mE m ->
  mem_inv rsegs m -> fg_mem f pa pp pn st g c m ->
  evtF rsegs RNG Qf_on
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
             x24 x25 x26 x27 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85c18) fc None m (seg_rom rsegs)).
Proof.
  intros c j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m
    Hc Hr FR ST MU WM MI FM.
  step.
  eapply L_epi_on; [exact Hc | | exact FR | exact ST | exact MU | exact WM | exact MI | exact FM].
  rewrite Hr. reflexivity.
Qed.

Lemma L_none_on : forall j (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                        x28 x29 x30 x31 : word) m,
  NZ_on -> fg_fr len g = false ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  evtF rsegs RNG Qf_on
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
             x24 x25 x26 x27 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85c18) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m
    NZh HF FR ST MU WM MI.
  eapply (L_ret0_on FgNone); [ | reflexivity | exact FR | exact ST | exact MU | exact WM | exact MI | exact I].
  rewrite (cl_nn_on NZh), HF. reflexivity.
Qed.

Ltac rfail_on := eapply (L_epi_on FgRefuse);
  [ symmetry; apply rf_class_refuse; tauto | reflexivity
  | eassumption | eassumption | solve [cbn [fg_fp]; eassumption]
  | eassumption | eassumption | exact I ].

Ltac nfail_on := eapply L_none_on;
  [ eassumption
  | let EF := fresh "EF" in destruct (fg_fr len g) eqn:EF; [exfalso; apply fr_iff in EF; lia | reflexivity]
  | eassumption | eassumption | eassumption | eassumption | eassumption ].

Ltac gld_on i :=
  let R := fresh "RDG" in
  match goal with HG : bytes_at _ _ fr g |- _ => pose proof (rd_byte rsegs _ fr g i HG ltac:(rewrite Hg; lia)) as R end;
  step; clear R.

Ltac gchk_on i z c :=
  rewrite (rf_beq (nth i g (Z_to_bv 8 0)) c) by lia;
  change (bv_unsigned (nth i g (Z_to_bv 8 0))) with (bat g z);
  let B := fresh "B" in destruct (Z.eqb_spec (bat g z) c) as [B|B]; cbn [negb]; cbv iota; [|nfail_on].

Ltac ubn_on c := step; step; rewrite (u_ltu_negl (fr + 18) c) by lia; cbv iota.

Ltac gshk_on Psrli i r :=
  steps_to_on Psrli;
  match goal with SRg : asan_shadow_rd rsegs mE off fr 50 W5_on, ADg : asan_addressable rsegs mE off fr 50,
    MU : munch [(S - 4672, S)] mE ?mm |- _ =>
      chk1_on (fr + i) r (fa_rd1_on mm [(S - 4672, S)] fr 50 i (fr + i) SRg ADg MU ltac:(fa_sub_on) ltac:(lia) eq_refl)
  end.

(* 0x85bd4 .. 0x85c10: the block-sum loop over fr + 18 .. fr + 50, each load shadow-checked. *)
Lemma loopB_on : forall (Q : machine_state -> Prop)
  (r1 r5 r6 r7 r11 s7v r28 r29 r30 r31 : word)
  (m : word -> option byte) (A : Z) (bs : list byte) (c : nat) (W : list (Z * Z)),
  bytes_at rsegs m A bs -> (c <= length bs)%nat -> 0 < A -> A + Z.of_nat c <= 2 ^ 64 ->
  asan_shadow_rd rsegs m off A (Z.of_nat c) W -> asan_addressable rsegs m off A (Z.of_nat c) ->
  rng RNG A (Z.of_nat c) -> rng RNG (A / 8 + off) ((A + Z.of_nat c - 1) / 8 - A / 8 + 1) ->
  (forall y0 y3 y5 y6 y7 : word, evtF rsegs RNG Q
     (MS (mkR r1 (Z_to_bv 64 (S + -112)) gp tp r5 r6 r7 (Z_to_bv 64 f) (Z_to_bv 64 pn) y0 r11
              (Z_to_bv 64 (psum bs c)) y3 (Z_to_bv 64 (A + Z.of_nat c)) y5 y6 y7 (Z_to_bv 64 pp) (Z_to_bv 64 pa)
              (Z_to_bv 64 fr) s5 (Z_to_bv 64 (fr + 18)) s7v s8 (Z_to_bv 64 off) s10 s11 r28 r29 r30 r31)
         Ff (Z_to_bv 64 0x85c10) fc None m (seg_rom rsegs))) ->
  forall n i (a0v a2v a3v a4v a5v a6v a7v : word), (i + n = c)%nat -> (0 < n)%nat ->
  a0v = Z_to_bv 64 (A + Z.of_nat i) -> a4v = Z_to_bv 64 (A + Z.of_nat i) ->
  a2v = Z_to_bv 64 (psum bs i) -> bv_unsigned a3v = Z.of_nat n ->
  evtF rsegs RNG Q
    (MS (mkR r1 (Z_to_bv 64 (S + -112)) gp tp r5 r6 r7 (Z_to_bv 64 f) (Z_to_bv 64 pn) a0v r11 a2v a3v a4v a5v a6v a7v
             (Z_to_bv 64 pp) (Z_to_bv 64 pa) (Z_to_bv 64 fr) s5 (Z_to_bv 64 (fr + 18)) s7v s8 (Z_to_bv 64 off)
             s10 s11 r28 r29 r30 r31)
        Ff (Z_to_bv 64 0x85bd4) fc None m (seg_rom rsegs)).
Proof.
  intros Q r1 r5 r6 r7 r11 s7v r28 r29 r30 r31 m A bs c W HB Hc HA HAc SR AD RDAT RSH HK.
  induction n as [|n IH]; intros i a0v a2v a3v a4v a5v a6v a7v Hin Hn E0 E4 E2 H3; [lia|].
  subst a0v a4v a2v.
  pose proof (rd_byte rsegs m A bs i HB ltac:(lia)) as RD.
  pose proof (psum_range bs i) as PR.
  step. rewrite (rc_beq0_false (A + Z.of_nat i)) by lia. cbv iota.
  chk1_on (A + Z.of_nat i) (Z_to_bv 5 16)
    (fa_rd1m_on m A (Z.of_nat c) (Z.of_nat i) (A + Z.of_nat i) W SR AD ltac:(lia) eq_refl).
  step. step. step. step.
  rewrite psum_S_zxb.
  step. step.
  rewrite (rc_eqb0 (bv_unsigned a3v + -1)) by lia.
  destruct n as [|n].
  - replace (bv_unsigned a3v + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
    step.
    replace (A + Z.of_nat i + 1) with (A + Z.of_nat c) by lia.
    replace (Datatypes.S i) with c by lia. apply HK.
  - replace (bv_unsigned a3v + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
    apply (IH (Datatypes.S i)); first [lia | f_equal; lia | rewrite unsigned_lit by lia; lia].
Qed.

(* 0x85c60 .. 0x85cc0: the first-record path (two copies, store n and 1, return 0). *)
Lemma L_first_on : forall c j (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
  c = CL -> c = FgFirst -> 1 <= fg_n g <= 22 -> DJA_on ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  rw_cells rsegs m f [CB 72 st] -> bytes_at rsegs m fr g ->
  evtF rsegs RNG Qf_on
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 pp) (Z_to_bv 64 pa) (Z_to_bv 64 fr) s5 (Z_to_bv 64 (fr + 18)) (zxb (nth 26 g (Z_to_bv 8 0)))
             s8 (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85c60) fc None m (seg_rom rsegs)).
Proof.
  intros c j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
    Hc HcF Hn DJAh FR ST MU WM MI HS HG.
  assert (NZh : NZ_on) by (apply cl_nz_on; rewrite <- Hc, HcF; discriminate).
  assert (FRT : fg_fr len g = true).
  { destruct (fg_fr len g) eqn:E; [reflexivity|].
    assert (HN : CL = FgNone) by (rewrite (cl_nn_on NZh), E; reflexivity).
    rewrite Hc in HcF. rewrite HN in HcF. discriminate HcF. }
  pose proof (proj1 (proj1 (fr_iff len g) FRT)) as Hlen50.
  (* the first-record path: bat g 19 = 1, so both copies' regions are in R's first arm *)
  assert (B19 : bat g 19 = 1).
  { destruct (Z.eq_dec (bat g 19) 1) as [G1|G1]; [exact G1|].
    pose proof (cl_k_on NZh FRT G1) as EK. rewrite <- Hc, HcF in EK.
    destruct (fg_keep st g), (fg_close st g); discriminate EK. }
  destruct (HAF NZh) as ((Af & Aa & Ap & An & Happ & DJrt) & SRf & ADf & _).
  destruct (HAG NZh Hlen50) as (Ag & SRg & ADg).
  rngf_on NZh. rngg_on NZh Hlen50.
  pose proof (rt_addressable_bound mE f 72 Af) as (Hf0 & _ & Hf2).
  pose proof (rt_addressable_bound mE fr 50 Ag) as (Hr0 & _ & Hr2).
  destruct DJAh as (Dff & DfS & DrS).
  destruct (rf_rw_parts rsegs m f 72 st HS) as (HSb & HSw & HSl). clear HS.
  rewrite <- Hst in HSw.
  pose proof (rf_rw_sub rsegs m f st 0 6 HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as P0.
  pose proof (rf_rw_sub rsegs m f st 6 2 HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as P6.
  pose proof (rf_rw_sub rsegs m f st 8 (fg_n g) HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as P8.
  pose proof (rf_bytes_skip rsegs m f st (8 + fg_n g) HSb ltac:(rewrite Hst; lia)) as PR.
  clear HSb.
  rewrite Z.add_0_r in P0. change (Z.to_nat 6) with 6%nat in P0. change (Z.to_nat 2) with 2%nat in P6.
  pose proof (rf_bytes_bsl rsegs m fr g 6 6 HG ltac:(lia) ltac:(lia) ltac:(rewrite Hg; lia)) as GS.
  pose proof (rf_bytes_bsl rsegs m fr g 27 (fg_n g) HG ltac:(lia) ltac:(lia) ltac:(rewrite Hg; lia)) as GB.
  clear HG.
  apply (munch_weaken [(S - 4672, S)] [(f, f + 72); (S - 4672, S)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m f 72 Af MU (fa_sowf_on NZh)) as ADfm.
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m fr 50 Ag MU (fa_sowf_on NZh)) as ADgm.
  pose proof (rtW_on [(f, f + 72); (S - 4672, S)] m NZh MU ltac:(fa_sub_on) WM) as (ACm & SRm).
  (* the shared statement, with its shadow word spans (sh_word_rng of rng_asan.v) written out *)
  pose proof MCPY as HM. unfold asan_memcpy_contract_F_on, sh_word_rng, sh_al8_lo, sh_al8_hi in HM. cbv zeta in HM.
  step. step. step. step.
  assert (U0 : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 (fr + 6)) = fr + 6) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  assert (U3 : bv_unsigned (Z_to_bv 64 (S + -112)) = S + -112) by (apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HM with (src := bsl g 6 6) (junk := bsl st 0 6) (lo := S - 4672).
    - rewrite U1. exact GS.
    - rewrite U2. apply rf_bsl_length; rewrite ?Hg; lia.
    - rewrite U0, U2. exact P0.
    - rewrite U0, U1, U2. destruct Dff as [H|H]; [right; right; lia | right; left; lia].
    - rewrite U2. lia.
    - rewrite U1, U2. apply (fa_addr_sub m fr 50); [exact ADgm | lia | lia | lia].
    - rewrite U0, U2. apply (fa_addr_sub m f 72); [exact ADfm | lia | lia | lia].
    - rewrite U1, U2. unfold end_in_app. right. replace (fr + 6 + 6) with (fr + 12) by lia.
      apply (fa_addr_app m fr 50 12); [exact ADgm | lia].
    - rewrite U0, U2. unfold end_in_app. right. apply (fa_addr_app m f 72 6); [exact ADfm | lia].
    - rewrite U0, U1, U2. right. split;
        [replace (fr + 6 + 7) with (fr + 13) by lia; apply (fa_addr_app m fr 50 13); [exact ADgm | lia]
        | apply (fa_addr_app m f 72 7); [exact ADfm | lia]].
    - rewrite U0, U2. cbn [dj_from] in DJrt. destruct DJrt as [[H|H] _]; [right; lia | left; lia].
    - rewrite U0, U2, U3. unfold ASAN_MEMCPY_K. destruct DfS as [H|H]; [left; lia | right; lia].
    - rewrite U1, U2, U3. unfold ASAN_MEMCPY_K. destruct DrS as [H|H]; [left; lia | right; lia].
    - rewrite U3. exact ST.
    - rewrite U3. unfold ASAN_MEMCPY_K. lia.
    - unfold HIGHMEM_BEG. lia.
    - rewrite U3. unfold APPMEM_END. lia.
    - exact ACm.
    - apply (B.ShadowRwOn.shadow_rw_on_mono (reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g));
        [|exact (SRm _ HSW)].
      intros a Ha. exact (rin_first_on NZh FRT B19 _ _ _ (or_introl (conj U0 (conj U1 U2))) a Ha).
    - exact MI.
    - exact RBY.
    - exact RIMG.
    - rewrite U3. unfold ASAN_MEMCPY_K. apply (rng_sub' RNG (S - 4672) 4672); [exact RSTK | lia].
    - rewrite U0, U2. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - rewrite U1, U2. apply (rng_sub' RNG fr 50); [exact RGr | lia].
    - rewrite U0, U2. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off f 72 f 6 ltac:(lia) ltac:(lia) ltac:(lia) RGfs).
    - rewrite U1, U2. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off fr 50 (fr + 6) 6 ltac:(lia) ltac:(lia) ltac:(lia) RGrs).
    - rewrite U3. unfold ASAN_MEMCPY_K. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off (S - 4672) 4672 (S + -112 - 2224) 2224 ltac:(lia) ltac:(lia) ltac:(lia) RSTKS). }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                  & E & MU2 & WM2 & MI2 & ST2 & RW2 & BD2 & AC2 & SR2).
  subst ms'. clear BD2.
  rewrite U0, U2 in RW2. rewrite U0, U2, U3 in MU2. rewrite U3 in ST2.
  assert (SUB1 : sub_fp [(f, f + 6); (S + -112 - 2224, S + -112)] [(f, f + 72); (S - 4672, S)])
    by (intros x; cbn [outside]; intros (H1 & H2 & _); split; [lia | split; [lia | exact I]]).
  pose proof (munch_trans [(f, f + 72); (S - 4672, S)] mE m m2 MU (munch_weaken _ _ m m2 SUB1 MU2)) as MU3.
  pose proof (wmono_trans rsegs mE m m2 WM WM2) as WM3.
  pose proof (rw_cells_transport rsegs [(f, f + 6); (S + -112 - 2224, S + -112)] m m2 (f + 6) [CB 2 (bsl st 6 2)]
                P6 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as P6'.
  pose proof (rw_cells_transport rsegs [(f, f + 6); (S + -112 - 2224, S + -112)] m m2 (f + 8)
                [CB (Z.to_nat (fg_n g)) (bsl st 8 (fg_n g))] P8 MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as P8'.
  pose proof (bytes_at_transport rsegs [(f, f + 6); (S + -112 - 2224, S + -112)] m m2 (f + (8 + fg_n g))
                (skipn (Z.to_nat (8 + fg_n g)) st) PR MU2
                ltac:(cbn [disjoint_from]; rewrite length_skipn, Hst; repeat split; try exact I; lia)) as PR'.
  pose proof (bytes_at_transport rsegs [(f, f + 6); (S + -112 - 2224, S + -112)] m m2 (fr + 27) (bsl g 27 (fg_n g))
                GB MU2 ltac:(cbn [disjoint_from]; rewrite (rf_bsl_length g 27 (fg_n g)) by (rewrite ?Hg; lia);
                             repeat split; try exact I; lia)) as GB'.
  pose proof (rw_cells_transport rsegs [(f, f + 6); (S + -112 - 2224, S + -112)] m m2 (S + -112) (FRc j) FR MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FR2.
  replace (Z.of_nat (length st)) with 72 in HSw by (rewrite Hst; reflexivity).
  pose proof (wr_at_transport rsegs m m2 f 72 HSw WM2) as WRm2.
  replace (ret_pc (Z_to_bv 64 0x85c70)) with (Z_to_bv 64 0x85c70)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m2 f 72 Af MU3 (fa_sowf_on NZh)) as ADfm2.
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m2 fr 50 Ag MU3 (fa_sowf_on NZh)) as ADgm2.
  step. step. rewrite (u_ltu_negl (fr + 18) (-10)) by lia. cbv iota.
  step. step. step. step.
  assert (U4 : bv_unsigned (zxb (nth 26 g (Z_to_bv 8 0))) = fg_n g) by (exact (rf_zxb_u _)).
  assert (U5 : bv_unsigned (Z_to_bv 64 (f + 8)) = f + 8) by (apply unsigned_lit; lia).
  assert (U6 : bv_unsigned (Z_to_bv 64 (fr + 27)) = fr + 27) by (apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HM with (src := bsl g 27 (fg_n g)) (junk := bsl st 8 (fg_n g)) (lo := S - 4672).
    - rewrite U6. exact GB'.
    - rewrite U4. apply rf_bsl_length; rewrite ?Hg; lia.
    - rewrite U5, U4. exact P8'.
    - rewrite U5, U6, U4. destruct Dff as [H|H]; [right; right; lia | right; left; lia].
    - rewrite U4. lia.
    - rewrite U6, U4. apply (fa_addr_sub m2 fr 50); [exact ADgm2 | lia | lia | lia].
    - rewrite U5, U4. apply (fa_addr_sub m2 f 72); [exact ADfm2 | lia | lia | lia].
    - rewrite U6, U4. unfold end_in_app. right. replace (fr + 27 + fg_n g) with (fr + (27 + fg_n g)) by lia.
      apply (fa_addr_app m2 fr 50 (27 + fg_n g)); [exact ADgm2 | lia].
    - rewrite U5, U4. unfold end_in_app. right. replace (f + 8 + fg_n g) with (f + (8 + fg_n g)) by lia.
      apply (fa_addr_app m2 f 72 (8 + fg_n g)); [exact ADfm2 | lia].
    - rewrite U5, U6, U4. right. split;
        [replace (fr + 27 + 7) with (fr + 34) by lia; apply (fa_addr_app m2 fr 50 34); [exact ADgm2 | lia]
        | replace (f + 8 + 7) with (f + 15) by lia; apply (fa_addr_app m2 f 72 15); [exact ADfm2 | lia]].
    - rewrite U5, U4. cbn [dj_from] in DJrt. destruct DJrt as [[H|H] _]; [right; lia | left; lia].
    - rewrite U5, U4, U3. unfold ASAN_MEMCPY_K. destruct DfS as [H|H]; [left; lia | right; lia].
    - rewrite U6, U4, U3. unfold ASAN_MEMCPY_K. destruct DrS as [H|H]; [left; lia | right; lia].
    - rewrite U3. exact ST2.
    - rewrite U3. unfold ASAN_MEMCPY_K. lia.
    - unfold HIGHMEM_BEG. lia.
    - rewrite U3. unfold APPMEM_END. lia.
    - exact AC2.
    - apply (B.ShadowRwOn.shadow_rw_on_mono (reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g));
        [|exact (SR2 _ (SRm _ HSW))].
      intros a Ha. exact (rin_first_on NZh FRT B19 _ _ _ (or_intror (conj U5 (conj U6 U4))) a Ha).
    - exact MI2.
    - exact RBY.
    - exact RIMG.
    - rewrite U3. unfold ASAN_MEMCPY_K. apply (rng_sub' RNG (S - 4672) 4672); [exact RSTK | lia].
    - rewrite U5, U4. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - rewrite U6, U4. apply (rng_sub' RNG fr 50); [exact RGr | lia].
    - rewrite U5, U4. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off f 72 (f + 8) (fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) RGfs).
    - rewrite U6, U4. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off fr 50 (fr + 27) (fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) RGrs).
    - rewrite U3. unfold ASAN_MEMCPY_K. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off (S - 4672) 4672 (S + -112 - 2224) 2224 ltac:(lia) ltac:(lia) ltac:(lia) RSTKS). }
  intros ms'' PO2.
  destruct PO2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m3
                  & E2 & MU4 & WM4 & MI4 & ST4 & RW4 & BD4 & AC4 & SR4).
  subst ms''. clear BD4.
  rewrite U5, U4 in RW4. rewrite U5, U4, U3 in MU4. rewrite U3 in ST4.
  replace (ret_pc (Z_to_bv 64 0x85c88)) with (Z_to_bv 64 0x85c88)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (SUB2 : sub_fp [(f + 8, f + 8 + fg_n g); (S + -112 - 2224, S + -112)] [(f, f + 72); (S - 4672, S)])
    by (intros x; cbn [outside]; intros (H1 & H2 & _); split; [lia | split; [lia | exact I]]).
  pose proof (munch_trans [(f, f + 72); (S - 4672, S)] mE m2 m3 MU3 (munch_weaken _ _ m2 m3 SUB2 MU4)) as MU5.
  pose proof (wmono_trans rsegs mE m2 m3 WM3 WM4) as WMm3.
  pose proof (wr_at_transport rsegs m2 m3 f 72 WRm2 WM4) as WRm3.
  pose proof (proj1 (rf_rw_parts rsegs m2 f 6 (bsl g 6 6) RW2)) as B0m2.
  pose proof (bytes_at_transport rsegs [(f + 8, f + 8 + fg_n g); (S + -112 - 2224, S + -112)] m2 m3 f (bsl g 6 6)
                B0m2 MU4 ltac:(cbn [disjoint_from]; rewrite rf_bsl_length by (rewrite ?Hg; lia);
                               repeat split; try exact I; lia)) as B0.
  pose proof (proj1 (rf_rw_parts rsegs m3 (f + 8) (Z.to_nat (fg_n g)) (bsl g 27 (fg_n g)) RW4)) as B8.
  pose proof (bytes_at_transport rsegs [(f + 8, f + 8 + fg_n g); (S + -112 - 2224, S + -112)] m2 m3 (f + (8 + fg_n g))
                (skipn (Z.to_nat (8 + fg_n g)) st) PR' MU4
                ltac:(cbn [disjoint_from]; rewrite length_skipn, Hst; repeat split; try exact I; lia)) as BR.
  pose proof (rw_cells_transport rsegs [(f + 8, f + 8 + fg_n g); (S + -112 - 2224, S + -112)] m2 m3 (S + -112) (FRc j)
                FR2 MU4 WM4 ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FR3.
  clear RW4 PR' RW2 P6 P6' P8 P8' PR GS GB GB' B0m2 WRm2 MU MU2 MU3 MU4 WM WM2 WM3 WM4 MI MI2 ST ST2
    ADfm ADgm ADfm2 ADgm2 ACm SRm AC2 SR2 FR FR2.
  step.
  chk1_on (f + 7) (Z_to_bv 5 12)
    (fa_rd1_on m3 [(f, f + 72); (S - 4672, S)] f 72 7 (f + 7) SRf ADf MU5 ltac:(fa_sub_on) ltac:(lia) eq_refl).
  pose proof (wr_at_store_ok rsegs m3 f 72 7 1%nat WRm3 ltac:(lia) ltac:(lia)) as SO7.
  step.
  change (Z_to_bv 64 (f + 7)) with (wa (f + 7)).
  pose proof (bytes_at_write_same rsegs m3 (f + 7) [nth 26 g (Z_to_bv 8 0)] ltac:(lia)
                ltac:(cbn [length]; lia)) as B7n.
  pose proof (bytes_at_write_other rsegs m3 (f + 7) [nth 26 g (Z_to_bv 8 0)] f (bsl g 6 6) B0 ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(rewrite rf_bsl_length by (rewrite ?Hg; lia); lia)) as B0a.
  pose proof (bytes_at_write_other rsegs m3 (f + 7) [nth 26 g (Z_to_bv 8 0)] (f + 8) (bsl g 27 (fg_n g)) B8
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as B8a.
  pose proof (bytes_at_write_other rsegs m3 (f + 7) [nth 26 g (Z_to_bv 8 0)] (f + (8 + fg_n g))
                (skipn (Z.to_nat (8 + fg_n g)) st) BR ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia))
    as BRa.
  pose proof (rw_cells_frame rsegs m3 (S + -112) (FRc j) (f + 7) [nth 26 g (Z_to_bv 8 0)] FR3 ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(cbn [cells_size csize Nat.add length]; lia)) as FR3a.
  pose proof (mem_inv_store rsegs m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)] MI4 ltac:(cbn [length]; exact SO7)) as MI4a.
  pose proof (stk_write rsegs m3 (S - 4672) (S + -112) (f + 7) [nth 26 g (Z_to_bv 8 0)] ST4 ltac:(lia)
                ltac:(cbn [length]; lia)) as ST4a.
  apply (munch_write [(f, f + 72); (S - 4672, S)] mE m3 (f + 7) [nth 26 g (Z_to_bv 8 0)]) in MU5;
    [| lia | cbn [length]; lia | cbn [inside length]; lia].
  apply (wmono_write rsegs mE m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)]) in WMm3.
  pose proof (wr_at_transport rsegs m3 (write_to_mem m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)]) f 72 WRm3
                (wmono_write rsegs m3 m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)] (wmono_refl rsegs m3))) as WRm4.
  set (m4 := write_to_mem m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)]) in *. clearbody m4.
  step.
  chk1_on (f + 6) (Z_to_bv 5 11)
    (fa_rd1_on m4 [(f, f + 72); (S - 4672, S)] f 72 6 (f + 6) SRf ADf MU5 ltac:(fa_sub_on) ltac:(lia) eq_refl).
  step. step.
  pose proof (wr_at_store_ok rsegs m4 f 72 6 1%nat WRm4 ltac:(lia) ltac:(lia)) as SO6.
  step.
  change (Z_to_bv 64 (f + 6)) with (wa (f + 6)).
  pose proof (bytes_at_write_same rsegs m4 (f + 6) [Z_to_bv 8 1] ltac:(lia) ltac:(cbn [length]; lia)) as B6_1.
  pose proof (bytes_at_write_other rsegs m4 (f + 6) [Z_to_bv 8 1] f (bsl g 6 6) B0a ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(rewrite rf_bsl_length by (rewrite ?Hg; lia); lia)) as B0b.
  pose proof (bytes_at_write_other rsegs m4 (f + 6) [Z_to_bv 8 1] (f + 7) [nth 26 g (Z_to_bv 8 0)] B7n ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as B7nb.
  pose proof (bytes_at_write_other rsegs m4 (f + 6) [Z_to_bv 8 1] (f + 8) (bsl g 27 (fg_n g)) B8a ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as B8b.
  pose proof (bytes_at_write_other rsegs m4 (f + 6) [Z_to_bv 8 1] (f + (8 + fg_n g))
                (skipn (Z.to_nat (8 + fg_n g)) st) BRa ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia))
    as BRb.
  pose proof (rw_cells_frame rsegs m4 (S + -112) (FRc j) (f + 6) [Z_to_bv 8 1] FR3a ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(cbn [cells_size csize Nat.add length]; lia)) as FR3b.
  pose proof (mem_inv_store rsegs m4 (wa (f + 6)) [Z_to_bv 8 1] MI4a ltac:(cbn [length]; exact SO6)) as MI4b.
  pose proof (stk_write rsegs m4 (S - 4672) (S + -112) (f + 6) [Z_to_bv 8 1] ST4a ltac:(lia)
                ltac:(cbn [length]; lia)) as ST4b.
  apply (munch_write [(f, f + 72); (S - 4672, S)] mE m4 (f + 6) [Z_to_bv 8 1]) in MU5;
    [| lia | cbn [length]; lia | cbn [inside length]; lia].
  apply (wmono_write rsegs mE m4 (wa (f + 6)) [Z_to_bv 8 1]) in WMm3.
  set (m5 := write_to_mem m4 (wa (f + 6)) [Z_to_bv 8 1]) in *. clearbody m5.
  step.
  eapply (L_epi_on FgFirst); [ rewrite <- HcF; exact Hc | reflexivity | exact FR3b | exact ST4b | exact MU5
    | exact WMm3 | exact MI4b | ].
  cbn [fg_mem]. unfold fg_first, fg_body.
  apply (rf_app rsegs m5 f (bsl g 6 6) (f + 6)
    ([Z_to_bv 8 1; nth 26 g (Z_to_bv 8 0)] ++ bsl g 27 (fg_n g) ++ skipn (Z.to_nat (8 + fg_n g)) st));
    [ exact B0b | | rewrite rf_bsl_length by (rewrite ?Hg; lia); reflexivity ].
  apply (rf_app rsegs m5 (f + 6) [Z_to_bv 8 1] (f + 7)
    ([nth 26 g (Z_to_bv 8 0)] ++ bsl g 27 (fg_n g) ++ skipn (Z.to_nat (8 + fg_n g)) st));
    [ exact B6_1 | | cbn [length]; lia ].
  apply (rf_app rsegs m5 (f + 7) [nth 26 g (Z_to_bv 8 0)] (f + 8)
    (bsl g 27 (fg_n g) ++ skipn (Z.to_nat (8 + fg_n g)) st));
    [ exact B7nb | | cbn [length]; lia ].
  apply (rf_app rsegs m5 (f + 8) (bsl g 27 (fg_n g)) (f + (8 + fg_n g)) (skipn (Z.to_nat (8 + fg_n g)) st));
    [ exact B8b | exact BRb | rewrite rf_bsl_length by (rewrite ?Hg; lia); lia ].
Qed.

(* 0x85d18 .. 0x85d28: the drop path (store 0 at f + 6, return 0). *)
Lemma L_drop_on : forall c j (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26
                        x28 x29 x30 x31 : word) m,
  c = CL -> c = FgDrop -> (f + 72 <= S - 4672 \/ S <= f) ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(f, f + 72); (S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  rw_cells rsegs m f [CB 72 st] ->
  evtF rsegs RNG Qf_on
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             x21 x22 x23 (Z_to_bv 64 (f + 6)) x25 x26 (Z_to_bv 64 ((f + 6) / 8 + off)) x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85d18) fc None m (seg_rom rsegs)).
Proof.
  intros c j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 m
    Hc HcD DfS FR ST MU WM MI HS.
  assert (NZh : NZ_on) by (apply cl_nz_on; rewrite <- Hc, HcD; discriminate).
  destruct (HAF NZh) as ((Af & _) & SRf & ADf & _).
  rngf_on NZh.
  pose proof (rt_addressable_bound mE f 72 Af) as (Hf0 & _ & Hf2).
  chk1p_on (f + 6) (Z_to_bv 5 11)
    (fa_rdb_on m [(f, f + 72); (S - 4672, S)] f 72 6 (f + 6) SRf ADf MU ltac:(fa_sub_on) ltac:(lia) eq_refl).
  step. step. step.
  eapply (L_epi_on FgDrop); [ rewrite <- HcD; exact Hc | reflexivity | exact FR | exact ST | exact MU | exact WM
    | exact MI | ].
  cbn [fg_mem]. eapply fa_rw_bytes; [exact HS|]. cbn [cells_bytes cbytes]. rewrite ?app_nil_r. reflexivity.
Qed.

Ltac ubs_on c := step; step; rewrite (u_ltu_negl (f + 8) c) by lia; cbv iota.

(* 0x85ed0 .. 0x85f80: the close path (byte 17 checked, pa/pp/pn each checked and stored, return 1). *)
Lemma L_close_on : forall c (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x27 x28 x29 x30 x31 : word) m,
  c = CL -> c = FgClose -> 14 <= fg_T st g <= 64 -> length (fg_join st g) = 72%nat -> DJB_on ->
  rw_cells rsegs m (S + -112) (FRc Jc) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(f, f + 72); (S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  bytes_at rsegs m f (fg_clear (fg_join st g)) -> OUT_on ->
  evtF rsegs RNG Qf_on
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 pp) (Z_to_bv 64 pa) x20 (Z_to_bv 64 (f + 8)) x22 x23 x24 (Z_to_bv 64 off)
             (Z_to_bv 64 (fg_T st g)) x27 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85ed0) fc None m (seg_rom rsegs)).
Proof.
  intros c x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x27 x28 x29 x30 x31 m
    Hc HcC HT LJ DJBh FR ST MU WM MI CJ OUTh.
  pose proof OUTh as (WA & WP & WN & Ma & Mp & Mn). clear OUTh.
  assert (NZh : NZ_on) by (apply cl_nz_on; rewrite <- Hc, HcC; discriminate).
  destruct (HAF NZh) as ((Af & Aa & Ap & An & Happ & DJrt) &
                         SRf & ADf & SRa & ADa & SRp & ADp & R3p & SRn & ADn & R3n).
  rngf_on NZh.
  clear Happ DJrt.
  pose proof (rt_addressable_bound mE f 72 Af) as (Hf0 & _ & Hf2).
  pose proof (rt_addressable_bound mE pa 2 Aa) as (Hpa0 & _ & Hpa2).
  pose proof (rt_addressable_bound mE pp 8 Ap) as (Hpp0 & _ & Hpp2).
  pose proof (rt_addressable_bound mE pn 8 An) as (Hpn0 & _ & Hpn2).
  clear Af Aa Ap An.
  destruct DJBh as (Dfa & Dfp & Dfn & Dap & Dan & Dpn & DaS & DpS & DnS).
  apply hide_i in Dfa; apply hide_i in Dfp; apply hide_i in Dfn; apply hide_i in Dap; apply hide_i in Dan;
    apply hide_i in Dpn; apply hide_i in DaS; apply hide_i in DpS; apply hide_i in DnS.
  assert (Hpa8 : pa mod 8 + 2 <= 8) by (pose proof (Z.mod_pos_bound pa 8 ltac:(lia)); Z.div_mod_to_equations; lia).
  apply (wr_at_transport rsegs mE m) in WA; [|exact WM].
  apply (wr_at_transport rsegs mE m) in WP; [|exact WM].
  apply (wr_at_transport rsegs mE m) in WN; [|exact WM].
  pose proof (rf_clear_length _ LJ) as LCJ.
  pose proof (bytes_at_bound rsegs m f _ CJ) as BF. rewrite LCJ in BF.
  pose proof (rf_rd1 rsegs m f _ 17 CJ ltac:(lia) ltac:(rewrite LCJ; lia)) as R17.
  change (Z.to_nat 17) with 17%nat in R17. rewrite (rf_clear_nth _ 17 _ LJ ltac:(lia)) in R17.
  pose proof (rf_rd1 rsegs m f _ 18 CJ ltac:(lia) ltac:(rewrite LCJ; lia)) as R18.
  change (Z.to_nat 18) with 18%nat in R18. rewrite (rf_clear_nth _ 18 _ LJ ltac:(lia)) in R18.
  apply (munch_weaken [(f, f + 72); (S - 4672, S)] W5_on) in MU;
    [|unfold sub_fp, W5_on; cbn [outside]; intros; tauto].
  ubs_on (-10).
  step.
  chk1_on (f + 17) (Z_to_bv 5 12) (fa_rd1_on m W5_on f 72 17 (f + 17) SRf ADf MU ltac:(fa_sub_on) ltac:(lia) eq_refl).
  ubs_on (-11).
  (* pa is 2-aligned *)
  step. step. rewrite ?(unsigned_lit pa) by lia. rewrite fa_land1, Ma.
  change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
  step.
  destruct (fa_rd1_on m W5_on f 72 18 (f + 18) SRf ADf MU ltac:(fa_sub_on) ltac:(lia) eq_refl) as (k18 & RK18 & OK18 & KR18).
  step. rewrite ?(unsigned_lit (f + 18)) by lia. rewrite rc_shr3.
  step. step. clear RK18. step. clear R17. step.
  chk_if_on (f + 18) (Z_to_bv 5 13) k18 OK18.
  destruct (fa_rd2_on m W5_on pa 2 0 pa SRa ADa MU ltac:(fa_sub_on) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (kpa & RKpa & OKpa & KRpa & HBpa).
  step. rewrite ?(unsigned_lit pa) by lia. rewrite rc_shr3.
  step. step. clear RKpa. step. clear R18. step.
  chk_if2_on pa (Z_to_bv 5 13) kpa OKpa.
  step. step. step.
  pose proof (fa_store_ok m pa 2 2 WA ltac:(lia)) as SA.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?b) _) =>
    assert (EA : b = le2 (Z_to_bv 64 (fg_addr st g))) end.
  { rewrite rc_le2_pack. unfold fg_addr, bat. change (Z.to_nat 17) with 17%nat. change (Z.to_nat 18) with 18%nat.
    rewrite Z.mul_comm. symmetry. apply rc_le2_pair. }
  rewrite EA.
  change (Z_to_bv 64 pa) with (wa pa).
  pose proof (munch_write W5_on mE m pa (le2 (Z_to_bv 64 (fg_addr st g))) MU ltac:(lia)
                ltac:(rewrite length_le2; lia) ltac:(unfold W5_on; cbn [inside]; rewrite length_le2; lia)) as MU1.
  step. rewrite (u_ltu_negl (f + 8) (-12)) by lia. cbv iota.
  (* pp is 8-aligned *)
  step. step. rewrite ?(unsigned_lit pp) by lia. rewrite rc_land7, Mp.
  change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
  (* pp 8-byte check at the post-pa-store memory *)
  pose proof (asan_shadow_rd_munch rsegs mE _ off pp 8 W5_on W5_on SRp MU1 ltac:(fa_sub_on)) as SRp1.
  pose proof (asan_addressable_munch rsegs mE _ off pp 8 W5_on W5_on ADp SRp MU1 ltac:(fa_sub_on)) as ADp1.
  pose proof (asan_rt3_munch rsegs mE _ off pp 8 W5_on W5_on R3p SRp MU1 ltac:(fa_sub_on)) as R3p1.
  destruct (asan_shadow_read rsegs _ off pp 8 W5_on 0 SRp1 ltac:(lia)) as (kpp & RKpp & BKpp).
  pose proof (asan_check_8 rsegs _ off pp 8 0 kpp ADp1 R3p1 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Mp) BKpp) as K0pp.
  pose proof (rc_signed0_unsigned0 kpp K0pp) as K0ppu.
  rewrite Z.add_0_r in RKpp.
  step. rewrite ?(unsigned_lit pp) by lia. rewrite rc_shr3.
  step. step.
  replace (zxb kpp) with (Z_to_bv 64 0) by (unfold zxb; rewrite K0ppu; reflexivity).
  step.
  change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
  step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (fa_store_ok mm pp 8 8 (wr_at_write rsegs _ pp 8 _ _ WP) ltac:(lia)) as SP end.
  step.
  change (Z_to_bv 64 pp) with (wa pp). rewrite ?(unsigned_lit (f + 19)) by lia.
  pose proof (munch_write W5_on mE _ pp (le8 (Z_to_bv 64 (f + 19))) MU1 ltac:(lia)
                ltac:(rewrite length_le8; lia) ltac:(unfold W5_on; cbn [inside]; rewrite length_le8; lia)) as MU2.
  (* pn is 8-aligned *)
  step. rewrite ?(unsigned_lit pn) by lia. rewrite rc_land7, Mn.
  change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
  (* pn 8-byte check at the post-pp-store memory *)
  pose proof (asan_shadow_rd_munch rsegs mE _ off pn 8 W5_on W5_on SRn MU2 ltac:(fa_sub_on)) as SRn2.
  pose proof (asan_addressable_munch rsegs mE _ off pn 8 W5_on W5_on ADn SRn MU2 ltac:(fa_sub_on)) as ADn2.
  pose proof (asan_rt3_munch rsegs mE _ off pn 8 W5_on W5_on R3n SRn MU2 ltac:(fa_sub_on)) as R3n2.
  destruct (asan_shadow_read rsegs _ off pn 8 W5_on 0 SRn2 ltac:(lia)) as (kpn & RKpn & BKpn).
  pose proof (asan_check_8 rsegs _ off pn 8 0 kpn ADn2 R3n2 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Mn) BKpn) as K0pn.
  pose proof (rc_signed0_unsigned0 kpn K0pn) as K0pnu.
  rewrite Z.add_0_r in RKpn.
  step. rewrite ?(unsigned_lit pn) by lia. rewrite rc_shr3. step. step.
  replace (zxb kpn) with (Z_to_bv 64 0) by (unfold zxb; rewrite K0pnu; reflexivity).
  step.
  change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (fa_store_ok mm pn 8 8 (wr_at_write rsegs _ pn 8 _ _ (wr_at_write rsegs _ pn 8 _ _ WN)) ltac:(lia))
      as SN end.
  step.
  change (Z_to_bv 64 pn) with (wa pn). rewrite ?(unsigned_lit (fg_T st g - 13)) by lia.
  step. step.
  eapply (L_epi_on FgClose); [ rewrite <- HcC; exact Hc | reflexivity | | | | | | ].
  - apply rw_cells_frame; [apply rw_cells_frame; [apply rw_cells_frame; [exact FR | fz | fz | fzu DaS]
        | fz | fz | fzu DpS] | fz | fz | fzu DnS].
  - apply stk_write; [apply stk_write; [apply stk_write; [exact ST | fz | fz] | fz | fz] | fz | fz].
  - change (fg_fp 4672 f pa pp pn S FgClose)
      with [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (S - 4672, S)].
    apply munch_write; [apply munch_write; [apply munch_write; [exact MU | fz | fz | fz] | fz | fz | fz]
      | fz | fz | fz].
  - apply wmono_write, wmono_write, wmono_write, WM.
  - apply mem_inv_store; [apply mem_inv_store; [apply mem_inv_store; [exact MI | rewrite length_le2; exact SA]
        | rewrite length_le8; exact SP] | rewrite length_le8; exact SN].
  - cbn [fg_mem]. split; [|split; [|split]].
    + apply bytes_at_write_other; [apply bytes_at_write_other; [apply bytes_at_write_other; [exact CJ | fz | fz | fzu Dfa]
          | fz | fz | fzu Dfp] | fz | fz | fzu Dfn].
    + apply bytes_at_write_other; [apply bytes_at_write_other; [apply bytes_at_write_same; fz | fz | fz | fzu Dap]
        | fz | fz | fzu Dan].
    + apply bytes_at_write_other; [apply bytes_at_write_same; fz | fz | fz | fzu Dpn].
    + apply bytes_at_write_same; fz.
Qed.

Ltac jfail_on := eapply (L_ret0_on FgJoin);
  [ symmetry; match goal with H : CL = _ |- _ => rewrite H end;
    let EC := fresh "EC" in destruct (fg_close st g) eqn:EC; [exfalso; apply close_iff in EC; lia | reflexivity]
  | reflexivity | eassumption | eassumption | match goal with H : munch _ mE _ |- _ => exact H end
  | eassumption | eassumption
  | match goal with H : bytes_at _ _ f (fg_clear _) |- _ => exact H end ].

Ltac jld_on i :=
  let R := fresh "RDJ" in
  match goal with CJ : bytes_at _ _ f (fg_clear _), LJ : length (fg_join st g) = _ |- _ =>
    pose proof (rd_byte rsegs _ f _ i CJ ltac:(rewrite rf_clear_length by exact LJ; lia)) as R;
    rewrite (rf_clear_nth _ i _ LJ ltac:(lia)) in R
  end;
  step; clear R.

Ltac jbyte_on i z c :=
  rewrite (rf_beq (nth i (fg_join st g) (Z_to_bv 8 0)) c) by lia;
  change (bv_unsigned (nth i (fg_join st g) (Z_to_bv 8 0))) with (bat (fg_join st g) z);
  let B := fresh "B" in destruct (Z.eqb_spec (bat (fg_join st g) z) c) as [B|B]; cbn [negb]; cbv iota; [|jfail_on].

Ltac jchk_on Psrli i r :=
  steps_to_on Psrli;
  match goal with
  | SRf : asan_shadow_rd rsegs mE off f 72 W5_on, ADf : asan_addressable rsegs mE off f 72,
    MU : munch [(f, f + 72); (S - 4672, S)] mE ?mm |- _ =>
      chk1_on (f + i) r (fa_rd1_on mm [(f, f + 72); (S - 4672, S)] f 72 i (f + i) SRf ADf MU ltac:(fa_sub_on) ltac:(lia) eq_refl)
  end.

(* 0x85d64 ..: the close checks on the joined record, the record checksum call. *)
Lemma L_tail_on : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
  CL = (if fg_close st g then FgClose else FgJoin) -> 1 <= fg_n g <= 22 -> fg_T st g <= 64 -> DJB_on ->
  (f + 72 <= S - 4672 \/ S <= f) -> 0 < f -> OUT_on ->
  rw_cells rsegs m (S + -112) (FRc Jc) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(f, f + 72); (S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  bytes_at rsegs m f (fg_clear (fg_join st g)) ->
  evtF rsegs RNG Qf_on
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) (Z_to_bv 64 14) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 pp) (Z_to_bv 64 pa) (Z_to_bv 64 fr) (Z_to_bv 64 (f + 8)) (Z_to_bv 64 (fr + 18))
             (zxb (nth 26 g (Z_to_bv 8 0))) (Z_to_bv 64 (f + 6)) (Z_to_bv 64 off) (Z_to_bv 64 (fg_T st g))
             (Z_to_bv 64 ((f + 6) / 8 + off)) x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85d64) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
    HCL Hn HT DJBh DfS Hf0 OUTh FR ST MU WM MI CJ.
  assert (NZh : NZ_on) by (apply cl_nz_on; rewrite HCL; destruct (fg_close st g); discriminate).
  destruct (HAF NZh) as ((Af & _) & SRf & ADf & _).
  rngf_on NZh.
  pose proof (rt_addressable_bound mE f 72 Af) as (Hfa0 & _ & Hf2).
  pose proof (rf_fg_join_length st g Hst Hg Hn HT) as LJ.
  pose proof (rf_clear_length _ LJ) as LCJ.
  pose proof (bytes_at_bound rsegs m f _ CJ) as BF. rewrite LCJ in BF.
  assert (T0 : 0 <= fg_T st g).
  { unfold fg_T, fg_lf, bat. pose proof (byte_range (nth (Z.to_nat 7) st (Z_to_bv 8 0))). lia. }
  step.
  rewrite (fa_ltu (fg_T st g) 14) by lia.
  destruct (Z.ltb_spec (fg_T st g) 14) as [T14|T14]; cbv iota; [jfail_on|].
  jchk_on 0x85d68 8 (Z_to_bv 5 11). jld_on 8%nat. step. step. jbyte_on 8%nat 8 240.
  step. step. rewrite (u_eqb_negc (f + 8) (-1)) by lia. cbv iota.
  jchk_on 0x85d90 9 (Z_to_bv 5 12). jld_on 9%nat. step. step. jbyte_on 9%nat 9 65.
  ubs_on (-4).
  jchk_on 0x85db8 11 (Z_to_bv 5 12). jld_on 11%nat. step. jbyte_on 11%nat 11 0.
  ubs_on (-5).
  jchk_on 0x85ddc 12 (Z_to_bv 5 12). jld_on 12%nat. step. jbyte_on 12%nat 12 0.
  ubs_on (-6).
  jchk_on 0x85e00 13 (Z_to_bv 5 12). jld_on 13%nat. step. step. jbyte_on 13%nat 13 18.
  ubs_on (-7).
  jchk_on 0x85e28 14 (Z_to_bv 5 12). jld_on 14%nat. step. step. jbyte_on 14%nat 14 18.
  ubs_on (-8).
  jchk_on 0x85e50 15 (Z_to_bv 5 12). jld_on 15%nat. step. step. jbyte_on 15%nat 15 5.
  ubs_on (-9).
  jchk_on 0x85e78 16 (Z_to_bv 5 13). jld_on 16%nat. step. jbyte_on 16%nat 16 0.
  step. step.
  assert (LTt : bv_ltu (Z_to_bv 64 (18446744073709551615 - (f + 8))) (Z_to_bv 64 (fg_T st g + -1)) = false).
  { unfold bv_ltu. rewrite !unsigned_lit_wrap. apply Z.ltb_ge.
    change (2 ^ 64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia. }
  step. rewrite LTt. cbv iota. clear LTt.
  step.
  replace (f + 8 + (fg_T st g + -1)) with (f + (7 + fg_T st g)) by lia.
  chk1_on (f + (7 + fg_T st g)) (Z_to_bv 5 13)
    (fa_rd1_on m [(f, f + 72); (S - 4672, S)] f 72 (7 + fg_T st g) (f + (7 + fg_T st g)) SRf ADf MU ltac:(fa_sub_on)
       ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m f (fg_clear (fg_join st g)) (Z.to_nat (7 + fg_T st g)) CJ ltac:(rewrite LCJ; lia)) as RDJ.
  rewrite (rf_clear_nth _ (Z.to_nat (7 + fg_T st g)) _ LJ ltac:(lia)) in RDJ.
  rewrite (Z2Nat.id (7 + fg_T st g)) in RDJ by lia.
  step. clear RDJ. step. step.
  rewrite (rf_beq (nth (Z.to_nat (7 + fg_T st g)) (fg_join st g) (Z_to_bv 8 0)) 247) by lia.
  change (bv_unsigned (nth (Z.to_nat (7 + fg_T st g)) (fg_join st g) (Z_to_bv 8 0)))
    with (bat (fg_join st g) (7 + fg_T st g)).
  destruct (Z.eqb_spec (bat (fg_join st g) (7 + fg_T st g)) 247) as [B7|B7]; cbn [negb]; cbv iota; [|jfail_on].
  step. step. rewrite (u_eqb_negc (f + 8) (-7)) by lia. cbv iota.
  pose proof (rf_bytes_bsl rsegs m f (fg_clear (fg_join st g)) 15 (fg_T st g - 8) CJ ltac:(lia) ltac:(lia)
                ltac:(rewrite LCJ; lia)) as HBr.
  assert (EBs : bsl (fg_clear (fg_join st g)) 15 (fg_T st g - 8) = bsl (fg_join st g) 15 (fg_T st g - 8)).
  { unfold bsl. change (Z.to_nat 15) with 15%nat. rewrite (rf_clear_skipn _ 15 LJ ltac:(lia)). reflexivity. }
  rewrite EBs in HBr.
  pose proof (rtW_on [(f, f + 72); (S - 4672, S)] m NZh MU ltac:(fa_sub_on) WM) as (ACm & SRm).
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m f 72 Af MU (fa_sowf_on NZh)) as ADfm.
  pose proof CKV as HCV. unfold reac_ctrl_record_cksum_verify_contract_F_on in HCV.
  step. step.
  eapply evtF_cut.
  { eapply HCV with (bs := bsl (fg_join st g) 15 (fg_T st g - 8)).
    - rewrite unsigned_lit by lia. rewrite rf_bsl_length by (rewrite ?LJ; lia). first [reflexivity | f_equal; lia].
    - right. rewrite !unsigned_lit by lia. split; [lia|]. split; [lia|]. split; [exact HBr|].
      unfold REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME; destruct DfS as [H|H]; [left; lia | right; lia].
    - rewrite (unsigned_lit (S + -112)) by lia. exact ST.
    - rewrite (unsigned_lit (S + -112)) by lia. unfold REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME. lia.
    - intros _; exact ACm.
    - intros _. rewrite !unsigned_lit by lia. apply (fa_addr_sub m f 72); [exact ADfm | lia | lia | lia].
    - intros _ x Hx. rewrite (unsigned_lit (S + -112)) by lia. cbn [outside]. split; [|exact I].
      unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
        REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME in *. lia.
    - rewrite (unsigned_lit (S + -112)) by lia. unfold REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME.
      apply (rng_sub' RNG (S - 4672) 4672); [exact RSTK | lia].
    - unfold GOT_CELL_K. apply (rng_sub' RNG IMG_LO (IMG_HI - IMG_LO)); [exact RIMG | unfold IMG_LO, IMG_HI; lia].
    - unfold CELL_K. apply (rng_sub' RNG IMG_LO (IMG_HI - IMG_LO)); [exact RIMG | unfold IMG_LO, IMG_HI; lia].
    - intros _. rewrite !unsigned_lit by lia. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - intros _. rewrite !unsigned_lit by lia. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_bytes' RNG off f 72 (f + 15) (fg_T st g - 8) ltac:(lia) ltac:(lia) ltac:(lia) RGfs). }
  intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & MU' & WM' & MImp & ST').
  subst ms'.
  rewrite (unsigned_lit (S + -112)) in MU', ST' by lia.
  unfold REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME in MU', ST'.
  assert (SUBc : sub_fp [(S + -112 - 16, S + -112)] [(f, f + 72); (S - 4672, S)])
    by (intros xx; cbn [outside]; intros (H1 & H2 & _); split; [lia | exact I]).
  pose proof (munch_trans [(f, f + 72); (S - 4672, S)] mE m m' MU (munch_weaken _ _ m m' SUBc MU')) as MUc.
  pose proof (wmono_trans rsegs mE m m' WM WM') as WMc.
  pose proof (rw_cells_transport rsegs [(S + -112 - 16, S + -112)] m m' (S + -112) (FRc Jc) FR MU' WM'
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FRc2.
  pose proof (bytes_at_transport rsegs [(S + -112 - 16, S + -112)] m m' f (fg_clear (fg_join st g)) CJ MU'
                ltac:(cbn [disjoint_from]; rewrite LCJ; destruct DfS as [H|H]; repeat split; try exact I; lia)) as CJc.
  pose proof (MImp MI) as MIc.
  clear FR ST MU WM MI CJ MU' WM' MImp.
  replace (ret_pc (Z_to_bv 64 0x85ecc)) with (Z_to_bv 64 0x85ecc)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (Z.eqb_spec (recsum (bsl (fg_join st g) 15 (fg_T st g - 8))) 0) as [RS0|RS0]; cbv iota.
  2:{ step. rewrite u_eqb_m1. cbn [negb]. cbv iota. jfail_on. }
  step. rewrite (rc_eq0w (Z_to_bv 64 0)) by reflexivity. cbn [negb]. cbv iota.
  assert (EC : fg_close st g = true) by (apply close_iff; repeat split; first [assumption | lia]).
  eapply (L_close_on FgClose); [ rewrite HCL, EC; reflexivity | reflexivity | lia | exact LJ | exact DJBh | exact FRc2
    | exact ST' | exact MUc | exact WMc | exact MIc | exact CJc | exact OUTh ].
Qed.

(* 0x85d2c ..: the join path (append the body at f + 8 + lf, clear byte 6, fall to the close checks). *)
Lemma L_join_on : forall j (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word) m,
  CL = (if fg_close st g then FgClose else FgJoin) -> 1 <= fg_n g <= 22 -> fg_T st g <= 64 -> DJA_on -> DJB_on -> OUT_on ->
  0 < f ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(f, f + 72); (S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  bytes_at rsegs m f st -> wr_at rsegs m f (Z.of_nat (length st)) -> bytes_at rsegs m fr g ->
  evtF rsegs RNG Qf_on
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) (zxb (nth 7 st (Z_to_bv 8 0)))
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 pp) (Z_to_bv 64 pa) (Z_to_bv 64 fr) x21
             (Z_to_bv 64 (fr + 18)) (zxb (nth 26 g (Z_to_bv 8 0))) (Z_to_bv 64 (f + 6)) (Z_to_bv 64 off)
             (Z_to_bv 64 (fg_T st g)) (Z_to_bv 64 ((f + 6) / 8 + off)) x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85d2c) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 m
    HCL Hn HT DJAh DJBh OUTh Hf0 FR ST MU WM MI HSb HSw HG.
  assert (NZh : NZ_on) by (apply cl_nz_on; rewrite HCL; destruct (fg_close st g); discriminate).
  assert (FRT : fg_fr len g = true).
  { destruct (fg_fr len g) eqn:E; [reflexivity|].
    assert (HN : CL = FgNone) by (rewrite (cl_nn_on NZh), E; reflexivity).
    rewrite HN in HCL. destruct (fg_close st g); discriminate HCL. }
  pose proof (proj1 (proj1 (fr_iff len g) FRT)) as Hlen50.
  (* the join path: bat g 19 <> 1 and fg_keep st g = true (so fg_hf st <> 0), R's last arm *)
  assert (B19o : bat g 19 <> 1).
  { intros G1. assert (EF : CL = FgFirst) by (rewrite (cl_nn_on NZh), FRT, (proj2 (Z.eqb_eq _ _) G1); reflexivity).
    rewrite EF in HCL. destruct (fg_close st g); discriminate HCL. }
  assert (EKo : fg_keep st g = true).
  { pose proof (cl_k_on NZh FRT B19o) as E. rewrite E in HCL.
    destruct (fg_keep st g); [reflexivity|]. cbn [negb] in HCL. destruct (fg_close st g); discriminate HCL. }
  pose proof (proj1 (proj1 (keep_iff st g) EKo)) as H6o.
  destruct (HAF NZh) as ((Af & Aa & Ap & An & Happ & DJrt) & SRf & ADf & _).
  destruct (HAG NZh Hlen50) as (Ag & SRg & ADg).
  rngf_on NZh. rngg_on NZh Hlen50.
  destruct DJAh as (Dff & DfS & DrS).
  pose proof (rt_addressable_bound mE f 72 Af) as (Hfa0 & _ & Hf2).
  pose proof (rt_addressable_bound mE fr 50 Ag) as (Hr0 & _ & Hr2).
  pose proof (bytes_at_bound rsegs m fr g HG) as BG. rewrite Hg in BG.
  pose proof (bytes_at_bound rsegs m f st HSb) as BF. rewrite Hst in BF.
  pose proof (byte_range (nth 7 st (Z_to_bv 8 0))) as R7.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st) in R7.
  assert (TT : fg_T st g = fg_lf st + fg_n g) by reflexivity.
  pose proof (rf_rw_sub rsegs m f st 6 1 HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as P6.
  pose proof (rf_rw_sub rsegs m f st (8 + fg_lf st) (fg_n g) HSb HSw ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia))
    as P8.
  replace (f + (8 + fg_lf st)) with (f + 8 + fg_lf st) in P8 by lia.
  pose proof (rf_bytes_first rsegs m f st 6 HSb) as B0.
  pose proof (rf_bytes_bsl rsegs m f st 7 (1 + fg_lf st) HSb ltac:(lia) ltac:(lia) ltac:(rewrite Hst; lia)) as B7.
  pose proof (rf_bytes_skip rsegs m f st (8 + fg_T st g) HSb ltac:(rewrite Hst; lia)) as BR.
  pose proof (rf_bytes_bsl rsegs m fr g 27 (fg_n g) HG ltac:(lia) ltac:(lia) ltac:(rewrite Hg; lia)) as GB.
  assert (LGB : length (bsl g 27 (fg_n g)) = Z.to_nat (fg_n g)) by (apply rf_bsl_length; rewrite ?Hg; lia).
  assert (LB7 : length (bsl st 7 (1 + fg_lf st)) = Z.to_nat (1 + fg_lf st))
    by (apply rf_bsl_length; rewrite ?Hst; lia).
  assert (LB0 : length (firstn 6 st) = 6%nat) by (rewrite length_firstn; lia).
  change (Z.to_nat 1) with 1%nat in P6.
  (* the shared statement, with its shadow word spans (sh_word_rng of rng_asan.v) written out *)
  pose proof MCPY as HM. unfold asan_memcpy_contract_F_on, sh_word_rng, sh_al8_lo, sh_al8_hi in HM. cbv zeta in HM.
  step. step.
  try rewrite (unsigned_lit (f + 8)) by lia. rewrite (zb_lxor_ones (f + 8)) by lia.
  step. step.
  assert (LTo : bv_ltu (Z_to_bv 64 (18446744073709551615 - (f + 8))) (zxb (nth 7 st (Z_to_bv 8 0))) = false).
  { unfold bv_ltu. rewrite rf_zxb_u, unsigned_lit_wrap.
    change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st).
    apply Z.ltb_ge. change (2 ^ 64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia. }
  rewrite LTo. cbv iota. clear LTo.
  step. step. rewrite (u_ltu_negl (fr + 18) (-10)) by lia. cbv iota.
  step. step. step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m0 end.
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m0 f 72 Af MU (fa_sowf_on NZh)) as ADfm.
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m0 fr 50 Ag MU (fa_sowf_on NZh)) as ADgm.
  pose proof (rtW_on [(f, f + 72); (S - 4672, S)] m0 NZh MU ltac:(fa_sub_on) WM) as (ACm & SRm).
  pose proof (fa_addr_app m0 f 72 0 ADfm ltac:(lia)) as APPf0. rewrite Z.add_0_r in APPf0.
  pose proof (rf_bytes_skip rsegs m0 f st (8 + fg_T st g) HSb ltac:(rewrite Hst; lia)) as BR.
  rewrite ?rf_zxb_u.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st).
  assert (U0 : bv_unsigned (Z_to_bv 64 (f + 8 + fg_lf st)) = f + 8 + fg_lf st) by (apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 (fr + 27)) = fr + 27) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (zxb (nth 26 g (Z_to_bv 8 0))) = fg_n g) by (exact (rf_zxb_u _)).
  assert (U3 : bv_unsigned (Z_to_bv 64 (S + -112)) = S + -112) by (apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HM with (src := bsl g 27 (fg_n g)) (junk := bsl st (8 + fg_lf st) (fg_n g)) (lo := S - 4672).
    - rewrite U1. exact GB.
    - rewrite U2. exact LGB.
    - rewrite U0, U2. exact P8.
    - rewrite U0, U1, U2. destruct Dff as [H|H]; [right; right; lia | right; left; lia].
    - rewrite U2. lia.
    - rewrite U1, U2. apply (fa_addr_sub m0 fr 50); [exact ADgm | lia | lia | lia].
    - rewrite U0, U2. apply (fa_addr_sub m0 f 72); [exact ADfm | lia | lia | lia].
    - rewrite U1, U2. unfold end_in_app. right. replace (fr + 27 + fg_n g) with (fr + (27 + fg_n g)) by lia.
      apply (fa_addr_app m0 fr 50 (27 + fg_n g)); [exact ADgm | lia].
    - rewrite U0, U2. unfold end_in_app. right.
      apply (fa_app_mid f (f + 78) (f + 8 + fg_lf st + fg_n g)); [exact APPf0 | exact Happ | lia | lia].
    - rewrite U0, U1, U2. right. split;
        [replace (fr + 27 + 7) with (fr + 34) by lia; apply (fa_addr_app m0 fr 50 34); [exact ADgm | lia]
        | apply (fa_app_mid f (f + 78) (f + 8 + fg_lf st + 7)); [exact APPf0 | exact Happ | lia | lia]].
    - rewrite U0, U2. cbn [dj_from] in DJrt. destruct DJrt as [[H|H] _]; [right; lia | left; lia].
    - rewrite U0, U2, U3. unfold ASAN_MEMCPY_K. destruct DfS as [H|H]; [left; lia | right; lia].
    - rewrite U1, U2, U3. unfold ASAN_MEMCPY_K. destruct DrS as [H|H]; [left; lia | right; lia].
    - rewrite U3. exact ST.
    - rewrite U3. unfold ASAN_MEMCPY_K. lia.
    - unfold HIGHMEM_BEG. lia.
    - rewrite U3. unfold APPMEM_END. lia.
    - exact ACm.
    - apply (B.ShadowRwOn.shadow_rw_on_mono (reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g));
        [|exact (SRm _ HSW)].
      intros a Ha. exact (rin_join_on NZh FRT B19o H6o EKo _ _ _ U0 U1 U2 a Ha).
    - exact MI.
    - exact RBY.
    - exact RIMG.
    - rewrite U3. unfold ASAN_MEMCPY_K. apply (rng_sub' RNG (S - 4672) 4672); [exact RSTK | lia].
    - rewrite U0, U2. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - rewrite U1, U2. apply (rng_sub' RNG fr 50); [exact RGr | lia].
    - rewrite U0, U2. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off f 72 (f + 8 + fg_lf st) (fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) RGfs).
    - rewrite U1, U2. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off fr 50 (fr + 27) (fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) RGrs).
    - rewrite U3. unfold ASAN_MEMCPY_K. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off (S - 4672) 4672 (S + -112 - 2224) 2224 ltac:(lia) ltac:(lia) ltac:(lia) RSTKS). }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                  & E & MU2 & WM2 & MI2 & ST2 & RW2 & BD2 & AC2 & SR2).
  subst ms'. clear BD2.
  rewrite U0, U2 in RW2. rewrite U0, U2, U3 in MU2. rewrite U3 in ST2.
  try (replace (ret_pc (Z_to_bv 64 0x85d54)) with (Z_to_bv 64 0x85d54)
    by (symmetry; apply ret_pc_even; [lia | reflexivity])).
  assert (SUB1 : sub_fp [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -112 - 2224, S + -112)]
                        [(f, f + 72); (S - 4672, S)])
    by (intros x; cbn [outside]; intros (H1 & H2 & _); split; [lia | split; [lia | exact I]]).
  pose proof (munch_trans [(f, f + 72); (S - 4672, S)] mE m0 m2 MU (munch_weaken _ _ m0 m2 SUB1 MU2)) as MU3.
  pose proof (wmono_trans rsegs mE m0 m2 WM WM2) as WM3.
  replace (Z.of_nat (length st)) with 72 in HSw by (rewrite Hst; reflexivity).
  pose proof (wr_at_transport rsegs m0 m2 f 72 HSw WM2) as WRm2.
  pose proof (bytes_at_transport rsegs [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -112 - 2224, S + -112)]
                m0 m2 f (firstn 6 st) B0 MU2
                ltac:(cbn [disjoint_from]; rewrite LB0; repeat split; try exact I; lia)) as B0m2.
  pose proof (bytes_at_transport rsegs [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -112 - 2224, S + -112)]
                m0 m2 (f + 7) (bsl st 7 (1 + fg_lf st)) B7 MU2
                ltac:(cbn [disjoint_from]; rewrite LB7, Z2Nat.id by lia; repeat split; try exact I; lia)) as B7m2.
  pose proof (bytes_at_transport rsegs [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -112 - 2224, S + -112)]
                m0 m2 (f + (8 + fg_T st g)) (skipn (Z.to_nat (8 + fg_T st g)) st) BR MU2
                ltac:(cbn [disjoint_from]; rewrite length_skipn, Hst; repeat split; try exact I; lia)) as BRm2.
  pose proof (rw_cells_transport rsegs [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -112 - 2224, S + -112)]
                m0 m2 (S + -112) FRj FR MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FR2.
  pose proof (proj1 (rf_rw_parts rsegs m2 (f + 8 + fg_lf st) (Z.to_nat (fg_n g)) (bsl g 27 (fg_n g)) RW2)) as BB.
  destruct (fa_rdb_on m2 [(f, f + 72); (S - 4672, S)] f 72 6 (f + 6) SRf ADf MU3 ltac:(fa_sub_on) ltac:(lia) eq_refl)
    as (k6 & RK6 & OK6 & KR6 & HB6).
  step. clear RK6. step.
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k6)) by lia.
  lazymatch goal with
  | |- evtF ?segs ?RN ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      enough (G : forall rr : word, evtF segs RN Q (MS (bvmap_set (Z_to_bv 5 11) rr R) F B fc rv mm ro));
      [ destruct (Z.eqb_spec (bv_signed k6) 0) as [K6|K6]; cbn [negb];
        [ bjoin_on G (Z_to_bv 5 11)
        | step; rewrite ?(unsigned_lit (f + 6)) by lia; rewrite rc_land7; step;
          rewrite (rc_lts_signed ((f + 6) mod 8) (bv_signed k6)) by (pose proof (Z.mod_pos_bound (f + 6) 8 ltac:(lia)); lia);
          replace ((f + 6) mod 8 <? bv_signed k6) with true by (symmetry; apply Z.ltb_lt; destruct OK6; lia);
          bjoin_on G (Z_to_bv 5 11) ]
      | intros ?; simp_regs; clear OK6 KR6 HB6 ]
  end.
  step.
  pose proof (wr_at_store_ok rsegs m2 f 72 6 1%nat WRm2 ltac:(lia) ltac:(lia)) as SO6.
  step.
  change (Z_to_bv 64 (f + 6)) with (wa (f + 6)).
  pose proof (bytes_at_write_same rsegs m2 (f + 6) [Z_to_bv 8 0] ltac:(lia) ltac:(cbn [length]; lia)) as B6.
  pose proof (bytes_at_write_other rsegs m2 (f + 6) [Z_to_bv 8 0] f (firstn 6 st) B0m2 ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(rewrite LB0; cbn [length]; lia)) as B0m3.
  pose proof (bytes_at_write_other rsegs m2 (f + 6) [Z_to_bv 8 0] (f + 7) (bsl st 7 (1 + fg_lf st)) B7m2
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as B7m3.
  pose proof (bytes_at_write_other rsegs m2 (f + 6) [Z_to_bv 8 0] (f + 8 + fg_lf st) (bsl g 27 (fg_n g)) BB
                ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as BBm3.
  pose proof (bytes_at_write_other rsegs m2 (f + 6) [Z_to_bv 8 0] (f + (8 + fg_T st g))
                (skipn (Z.to_nat (8 + fg_T st g)) st) BRm2 ltac:(lia) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia))
    as BRm3.
  replace (f + 8 + fg_lf st) with (f + (8 + fg_lf st)) in BBm3 by lia.
  assert (CJ : bytes_at rsegs (write_to_mem m2 (wa (f + 6)) [Z_to_bv 8 0]) f (fg_clear (fg_join st g))).
  { rewrite fa_clear_join by (first [exact Hst | lia]).
    apply (rf_app _ _ f _ (f + 6)); [exact B0m3 | | rewrite LB0; lia].
    apply (rf_app _ _ (f + 6) _ (f + 7)); [exact B6 | | cbn [length]; lia].
    apply (rf_app _ _ (f + 7) _ (f + (8 + fg_lf st))); [exact B7m3 | | rewrite LB7, Z2Nat.id by lia; lia].
    apply (rf_app _ _ (f + (8 + fg_lf st)) _ (f + (8 + fg_T st g)));
      [exact BBm3 | exact BRm3 | unfold fg_body; rewrite LGB, Z2Nat.id by lia; lia]. }
  pose proof (munch_write [(f, f + 72); (S - 4672, S)] mE m2 (f + 6) [Z_to_bv 8 0] MU3 ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(unfold W5_on; cbn [inside length]; lia)) as MU4.
  pose proof (wmono_write rsegs mE m2 (wa (f + 6)) [Z_to_bv 8 0] WM3) as WM4.
  pose proof (mem_inv_store rsegs m2 (wa (f + 6)) [Z_to_bv 8 0] MI2 ltac:(cbn [length]; exact SO6)) as MI3.
  pose proof (stk_write rsegs m2 (S - 4672) (S + -112) (f + 6) [Z_to_bv 8 0] ST2 ltac:(lia)
                ltac:(cbn [length]; lia)) as ST3.
  pose proof (rw_cells_frame rsegs m2 (S + -112) FRj (f + 6) [Z_to_bv 8 0] FR2 ltac:(lia) ltac:(cbn [length]; lia)
                ltac:(cbn [cells_size csize Nat.add length]; lia)) as FR3.
  apply fa_fr_c8_on in FR3.
  eapply L_tail_on; [ exact HCL | exact Hn | exact HT | exact DJBh | exact DfS | exact Hf0 | exact OUTh | exact FR3
    | exact ST3 | exact MU4 | exact WM4 | exact MI3 | exact CJ ].
Qed.

(* 0x85cc4 ..: the second-record path (keep/drop/join/close dispatch). *)
Lemma L_second_on : forall j (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
  NZ_on -> fg_fr len g = true -> bat g 19 <> 1 -> DJA_on -> DJB_on -> OUT_on ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  rw_cells rsegs m f [CB 72 st] -> bytes_at rsegs m fr g ->
  evtF rsegs RNG Qf_on
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 pp) (Z_to_bv 64 pa) (Z_to_bv 64 fr) s5 (Z_to_bv 64 (fr + 18)) (zxb (nth 26 g (Z_to_bv 8 0)))
             s8 (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85cc4) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
    NZh FRT B19 DJAh DJBh OUTh FR ST MU WM MI HS HG.
  pose proof DJAh as (Dff & DfS & DrS).
  assert (Hf0 : 0 < f) by (destruct NZh as (Nf & _); lia).
  pose proof (proj1 (fr_iff len g) FRT) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hn1 & Hn2 & _).
  pose proof (cl_k_on NZh FRT B19) as HCL0.
  destruct (HAF NZh) as ((Af & Aa & Ap & An & Happ & DJrt) & SRf & ADf & _).
  destruct (HAG NZh (proj1 (proj1 (fr_iff len g) FRT))) as (Ag & SRg & ADg).
  rngf_on NZh. rngg_on NZh (proj1 (proj1 (fr_iff len g) FRT)).
  pose proof (rt_addressable_bound mE f 72 Af) as (Hfa0 & _ & Hf2).
  pose proof (rt_addressable_bound mE fr 50 Ag) as (Hr0 & _ & Hr2).
  pose proof (bytes_at_bound rsegs m fr g HG) as BG. rewrite Hg in BG.
  pose proof (rw_cells_bound rsegs m f _ HS) as BF. cbn [cells_size csize Nat.add] in BF.
  destruct (rf_rw_parts rsegs m f 72 st HS) as (HSb & HSw & _). clear HS.
  pose proof MU as MU0.
  apply (munch_weaken [(S - 4672, S)] [(f, f + 72); (S - 4672, S)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  pose proof (byte_range (nth 7 st (Z_to_bv 8 0))) as RL.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st) in RL.
  pose proof (byte_range (nth 26 g (Z_to_bv 8 0))) as RN.
  change (bv_unsigned (nth 26 g (Z_to_bv 8 0))) with (fg_n g) in RN.
  step.
  chk1_on (f + 6) (Z_to_bv 5 11)
    (fa_rd1_on m [(f, f + 72); (S - 4672, S)] f 72 6 (f + 6) SRf ADf MU ltac:(fa_sub_on) ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m f st 6 HSb ltac:(lia)) as R6.
  step. step. clear R6.
  rewrite (rf_beq (nth 6 st (Z_to_bv 8 0)) 0) by lia.
  change (bv_unsigned (nth 6 st (Z_to_bv 8 0))) with (fg_hf st).
  destruct (Z.eqb_spec (fg_hf st) 0) as [H6|H6]; cbv iota.
  { eapply (L_drop_on FgDrop);
      [ rewrite HCL0; destruct (fg_keep st g) eqn:EK;
          [exfalso; apply keep_iff in EK; destruct EK as (EK & _ & _); lia | reflexivity]
      | reflexivity | exact DfS | exact FR | exact ST | exact MU | exact WM | exact MI
      | rewrite <- Hst; apply fa_rw_of; [exact HSb | rewrite Hst; exact HSw] ]. }
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m f 72 Af MU (fa_sowf_on NZh)) as ADfm.
  pose proof (fl_addressable [(f, f + 72); (S - 4672, S)] mE m fr 50 Ag MU (fa_sowf_on NZh)) as ADgm.
  pose proof (rtW_on [(f, f + 72); (S - 4672, S)] m NZh MU ltac:(fa_sub_on) WM) as (ACm & SRm).
  pose proof (rf_bytes_skip rsegs m fr g 6 HG ltac:(rewrite Hg; lia)) as G6.
  change (Z.to_nat 6) with 6%nat in G6.
  destruct (fa_mcmp 6 st (skipn 6 g) ltac:(lia) ltac:(rewrite length_skipn, Hg; lia)) as (v & Hv & Rv & Iv).
  pose proof (HGOT (proj1 NZh) (proj1 (proj2 NZh)) (proj1 (proj2 (proj2 NZh)))
               (proj1 (proj2 (proj2 (proj2 NZh)))) (proj2 (proj2 (proj2 (proj2 NZh))))) as HGm.
  destruct HGm as (HRB0 & HRM0 & HGC0 & HCF10 & HCF20).
  pose proof (bytes_at_transport rsegs [(S - 4672, S)] mE m REAL_BCMP (le8 (wa BCMP)) HRB0 MU0
                ltac:(cbn [disjoint_from]; rewrite length_le8; unfold REAL_BCMP, HIGHMEM_BEG in *; lia)) as HRBm.
  pose proof (bytes_at_transport rsegs [(S - 4672, S)] mE m REAL_MEMCMP (le8 (wa MEMCMP)) HRM0 MU0
                ltac:(cbn [disjoint_from]; rewrite length_le8; unfold REAL_MEMCMP, HIGHMEM_BEG in *; lia)) as HRMm.
  pose proof (bytes_at_transport rsegs [(S - 4672, S)] mE m GOT_CF (le8 (wa CF)) HGC0 MU0
                ltac:(cbn [disjoint_from]; rewrite length_le8; unfold GOT_CF, HIGHMEM_BEG in *; lia)) as HGCm.
  pose proof (bytes_at_transport rsegs [(S - 4672, S)] mE m (CF + 254) [Z_to_bv 8 1] HCF10 MU0
                ltac:(cbn [disjoint_from length]; unfold CF, HIGHMEM_BEG in *; lia)) as HCF1m.
  pose proof (bytes_at_transport rsegs [(S - 4672, S)] mE m (CF + 255) [Z_to_bv 8 1] HCF20 MU0
                ltac:(cbn [disjoint_from length]; unfold CF, HIGHMEM_BEG in *; lia)) as HCF2m.
  pose proof BCMPw as HBc. unfold bcmp_wrap_contract_F_on in HBc. cbv zeta in HBc.
  step. step. step. step.
  assert (UF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (U6 : bv_unsigned (Z_to_bv 64 (fr + 6)) = fr + 6) by (apply unsigned_lit; lia).
  assert (U6' : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  assert (U3 : bv_unsigned (Z_to_bv 64 (S + -112)) = S + -112) by (apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HBc with (ls := st) (rs := skipn 6 g) (v := v) (lo := S - 4672).
    - rewrite UF. exact HSb.
    - rewrite U6. exact G6.
    - rewrite U6'. exact Hv.
    - exact MI.
    - rewrite U6'. lia.
    - rewrite UF, U6'. apply (fa_addr_sub m f 72); [exact ADfm | lia | lia | lia].
    - rewrite U6, U6'. apply (fa_addr_sub m fr 50); [exact ADgm | lia | lia | lia].
    - rewrite UF, U6'. unfold end_in_app. right. apply (fa_addr_app m f 72 6); [exact ADfm | lia].
    - rewrite U6, U6'. unfold end_in_app. right. replace (fr + 6 + 6) with (fr + 12) by lia.
      apply (fa_addr_app m fr 50 12); [exact ADgm | lia].
    - rewrite UF, U6'. right. apply (fa_addr_app m f 72 7); [exact ADfm | lia].
    - rewrite U6, U6'. right. replace (fr + 6 + 7) with (fr + 13) by lia.
      apply (fa_addr_app m fr 50 13); [exact ADgm | lia].
    - rewrite UF, U6', U3. unfold BCMP_WRAP_K. destruct DfS as [H|H]; [left; lia | right; lia].
    - rewrite U6, U6', U3. unfold BCMP_WRAP_K. destruct DrS as [H|H]; [left; lia | right; lia].
    - rewrite U3. exact ST.
    - rewrite U3. unfold BCMP_WRAP_K. lia.
    - unfold HIGHMEM_BEG. lia.
    - rewrite U3. unfold APPMEM_END. lia.
    - exact ACm.
    - rewrite UF, U6, U6'.
      apply (B.ShadowRwOn.shadow_rw_on_mono (reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g));
        [exact (rin_bcmp_on NZh FRT B19 H6) | exact (SRm _ HSW)].
    - exact HRBm.
    - exact HRMm.
    - exact HGCm.
    - exact HCF1m.
    - exact HCF2m.
    - exact RBY.
    - exact RIMG.
    - rewrite U3. unfold BCMP_WRAP_K. apply (rng_sub' RNG (S - 4672) 4672); [exact RSTK | lia].
    - rewrite UF, U6'. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - rewrite UF, U6'. right. unfold shadow_addr. rewrite <- Hoff. rewrite !(Z.mul_comm 8).
      exact (shw_sub RNG off f 72 f 6 ltac:(lia) ltac:(lia) ltac:(lia) RGfs).
    - rewrite U6, U6'. apply (rng_sub' RNG fr 50); [exact RGr | lia].
    - rewrite U6, U6'. right. unfold shadow_addr. rewrite <- Hoff. rewrite !(Z.mul_comm 8).
      exact (shw_sub RNG off fr 50 (fr + 6) 6 ltac:(lia) ltac:(lia) ltac:(lia) RGrs). }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m2
                  & E & MU2 & WM2 & MI2 & ST2 & AC2 & SR2 & BL & BR).
  subst ms'. rewrite U3 in MU2, ST2.
  try (replace (ret_pc (Z_to_bv 64 0x85cf0)) with (Z_to_bv 64 0x85cf0)
    by (symmetry; apply ret_pc_even; [lia | reflexivity])).
  assert (SUBb : sub_fp [(S + -112 - 4560, S + -112)] [(f, f + 72); (S - 4672, S)])
    by (intros x; cbn [outside]; intros (H1 & H2 & _); split; [lia | exact I]).
  pose proof (munch_trans [(f, f + 72); (S - 4672, S)] mE m m2 MU (munch_weaken _ _ m m2 SUBb MU2)) as MU3.
  pose proof (wmono_trans rsegs mE m m2 WM WM2) as WM3.
  pose proof (bytes_at_transport rsegs [(S + -112 - 4560, S + -112)] m m2 f st HSb MU2
                ltac:(cbn [disjoint_from]; rewrite Hst; destruct DfS as [H|H]; repeat split; try exact I; lia)) as HSbm2.
  pose proof (bytes_at_transport rsegs [(S + -112 - 4560, S + -112)] m m2 fr g HG MU2
                ltac:(cbn [disjoint_from]; rewrite Hg; destruct DrS as [H|H]; repeat split; try exact I; lia)) as HGm2.
  replace (Z.of_nat (length st)) with 72 in HSw by (rewrite Hst; reflexivity).
  pose proof (wr_at_transport rsegs m m2 f 72 HSw WM2) as WRm2.
  pose proof (rw_cells_transport rsegs [(S + -112 - 4560, S + -112)] m m2 (S + -112) (FRc j) FR MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FR2.
  step.
  rewrite (rf_eqb_s v) by lia.
  destruct (Z.eqb_spec v 0) as [V0|V0]; cbn [negb]; cbv iota.
  2:{ eapply (L_drop_on FgDrop);
        [ rewrite HCL0; destruct (fg_keep st g) eqn:EK;
            [exfalso; apply keep_iff in EK; destruct EK as (_ & ES & _); apply V0, Iv;
             exact (proj1 (rf_src_eq st g) ES) | reflexivity]
        | reflexivity | exact DfS | exact FR2 | exact ST2 | exact MU3 | exact WM3 | exact MI2
        | rewrite <- Hst; apply fa_rw_of; [exact HSbm2 | rewrite Hst; exact WRm2] ]. }
  pose proof (rd_byte rsegs m2 f st 7 HSbm2 ltac:(lia)) as R7.
  step.
  chk1_on (f + 7) (Z_to_bv 5 12)
    (fa_rd1_on m2 [(f, f + 72); (S - 4672, S)] f 72 7 (f + 7) SRf ADf MU3 ltac:(fa_sub_on) ltac:(lia) eq_refl).
  step. clear R7. step. step. step.
  rewrite ?rf_zxb_u.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st).
  change (bv_unsigned (nth 26 g (Z_to_bv 8 0))) with (fg_n g).
  rewrite (fa_ltu (fg_lf st + fg_n g) 65) by lia.
  change (fg_lf st + fg_n g) with (fg_T st g).
  destruct (Z.ltb_spec (fg_T st g) 65) as [T65|T65]; cbv iota.
  - eapply L_join_on;
      [ | exact (conj Hn1 Hn2) | lia | split; [exact Dff | split; [exact DfS | exact DrS]] | exact DJBh
      | exact OUTh | exact Hf0 | exact FR2 | exact ST2 | exact MU3 | exact WM3 | exact MI2 | exact HSbm2
      | rewrite Hst; exact WRm2 | exact HGm2 ].
    rewrite HCL0. replace (fg_keep st g) with true;
      [reflexivity | symmetry; apply keep_iff; split;
        [exact H6 | split; [exact (proj2 (rf_src_eq st g) (proj1 Iv V0)) | lia]]].
  - eapply (L_drop_on FgDrop);
      [ rewrite HCL0; destruct (fg_keep st g) eqn:EK;
          [exfalso; apply keep_iff in EK; destruct EK as (_ & _ & ET); lia | reflexivity]
      | reflexivity | exact DfS | exact FR2 | exact ST2 | exact MU3 | exact WM3 | exact MI2
      | rewrite <- Hst; apply fa_rw_of; [exact HSbm2 | rewrite Hst; exact WRm2] ].
Qed.

(* 0x85a48 .. 0x85c14: the frame checks, the block-sum loop, the first/second dispatch. *)
Lemma L_chk_on : forall j (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
  NZ_on -> (50 <= len -> bytes_at rsegs mE fr g) -> rw_cells rsegs mE f [CB 72 st] -> OUT_on -> DJA_on -> DJB_on ->
  rw_cells rsegs m (S + -112) (FRc j) -> stk rsegs m (S - 4672) (S + -112) ->
  munch [(S - 4672, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  evtF rsegs RNG Qf_on
    (MS (mkR x1 (Z_to_bv 64 (S + -112)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) x10 x11 (Z_to_bv 64 len)
             x13 x14 x15 x16 x17 (Z_to_bv 64 pp) (Z_to_bv 64 pa) (Z_to_bv 64 fr) s5 s6 s7 s8 s9 s10 s11
             x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85a48) fc None m (seg_rom rsegs)).
Proof.
  intros j x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
    NZh HF HS0 OUTh DJAh DJBh FR ST MU WM MI.
  destruct (HAF NZh)
    as ((Af & Aa & Ap & An & Happ & DJrt) & SRf & ADf & SRa & ADa & SRp & ADp & R3p & SRn & ADn & R3n).
  pose proof (asan_rt_munch rsegs mE m _ _ off _ _ HRT MU ltac:(unfold sub_fp; intros xx Hxx; exact Hxx)) as HRTm.
  rngf_on NZh.
  step. step.
  rewrite (fa_ltu len 50) by lia.
  destruct (Z.ltb_spec len 50) as [L50|L50]; cbv iota; [nfail_on|].
  destruct (HAG NZh L50) as (Ag & SRg & ADg).
  rngg_on NZh L50.
  pose proof (bytes_at_transport rsegs [(S - 4672, S)] mE m fr g (HF L50) MU
                ltac:(cbn [disjoint_from]; rewrite Hg; destruct DJAh as (_ & _ & DrS); lia)) as HG.
  pose proof (rw_cells_transport rsegs [(S - 4672, S)] mE m f _ HS0 MU WM
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; destruct DJAh as (_ & DfS & _); lia)) as HS.
  clear HF HS0.
  pose proof (bytes_at_bound rsegs m fr g HG) as BG. rewrite Hg in BG.
  step. step. rewrite (u_ltu_negl fr (-19)) by lia. cbv iota.
  step. step. rewrite (u_ltu_negr fr (-16)) by lia. cbn [negb]. cbv iota.
  pose proof (asan_rt_got_read rsegs m _ _ off _ HRTm) as RG.
  pose proof (asan_rt_cell_read rsegs m _ _ off _ HRTm) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  (* the unfolded copy of the image range, for the two 8-byte loads at the literal addresses of those cells *)
  pose proof RIMG as RIMGu. unfold IMG_LO, IMG_HI in RIMGu.
  step. step. step. clear RG RC.
  gshk_on 0x85a70 16 (Z_to_bv 5 12). gld_on 16%nat. step. step. gchk_on 16%nat 16 205.
  step. step. rewrite (u_ltu_negl fr (-18)) by lia. cbv iota.
  gshk_on 0x85a98 17 (Z_to_bv 5 12). gld_on 17%nat. step. step. gchk_on 17%nat 17 234.
  gshk_on 0x85ab8 18 (Z_to_bv 5 11). gld_on 18%nat. step. step. gchk_on 18%nat 18 4.
  step. step. rewrite (u_eqb_negc (fr + 18) (-1)) by lia. cbv iota.
  gshk_on 0x85ae0 19 (Z_to_bv 5 12). gld_on 19%nat. step. step. step.
  rewrite rf_b1. change (bv_unsigned (nth 19 g (Z_to_bv 8 0))) with (bat g 19).
  destruct ((bat g 19 =? 1) || (bat g 19 =? 2)) eqn:E19; cbn [negb]; cbv iota.
  2:{ apply orb_false_iff in E19. destruct E19 as [E19a E19b]. apply Z.eqb_neq in E19a, E19b. nfail_on. }
  apply orb_true_iff in E19. rewrite !Z.eqb_eq in E19.
  ubn_on (-5). gshk_on 0x85b0c 22 (Z_to_bv 5 13). gld_on 22%nat. step. gchk_on 22%nat 22 0.
  ubn_on (-6). gshk_on 0x85b30 23 (Z_to_bv 5 13). gld_on 23%nat. step. step. gchk_on 23%nat 23 2.
  ubn_on (-7). gshk_on 0x85b58 24 (Z_to_bv 5 13). gld_on 24%nat. step. gchk_on 24%nat 24 0.
  ubn_on (-8). gshk_on 0x85b7c 25 (Z_to_bv 5 13). gld_on 25%nat. step. step. gchk_on 25%nat 25 254.
  ubn_on (-9). gshk_on 0x85ba4 26 (Z_to_bv 5 13). gld_on 26%nat. step. step. step.
  rewrite rf_n. change (bv_unsigned (nth 26 g (Z_to_bv 8 0))) with (fg_n g).
  destruct ((1 <=? fg_n g) && (fg_n g <=? 22)) eqn:EN; cbn [negb]; cbv iota.
  2:{ apply andb_false_iff in EN. destruct EN as [EN|EN]; apply Z.leb_gt in EN; nfail_on. }
  apply andb_true_iff in EN. destruct EN as [EN1 EN2]. apply Z.leb_le in EN1, EN2.
  pose proof (rf_bytes_skip rsegs m fr g 18 HG ltac:(rewrite Hg; lia)) as HBk.
  change (Z.to_nat 18) with 18%nat in HBk.
  pose proof (asan_shadow_rd_munch rsegs mE m off fr 50 W5_on _ SRg MU ltac:(fa_sub_on)) as SRgm.
  pose proof (asan_addressable_munch rsegs mE m off fr 50 W5_on _ ADg SRg MU ltac:(fa_sub_on)) as ADgm.
  pose proof (fa_sr_sub_on m off fr 50 18 (Z.of_nat 32) W5_on SRgm ltac:(lia) ltac:(lia) ltac:(lia)) as SRk.
  pose proof (fa_ad_sub_on m off fr 50 18 (Z.of_nat 32) ADgm ltac:(lia) ltac:(lia) ltac:(lia)) as ADk.
  do 4 step.
  eapply (loopB_on Qf_on) with (A := fr + 18) (bs := skipn 18 g) (c := 32%nat) (W := W5_on) (n := 32%nat) (i := 0%nat);
    [ exact HBk | rewrite length_skipn, Hg; lia | lia | lia | exact SRk | exact ADk
    | apply (rng_sub' RNG fr 50); [exact RGr | lia]
    | exact (shw_bytes RNG off fr 50 (fr + 18) (Z.of_nat 32) ltac:(lia) ltac:(lia) ltac:(lia) RGrs)
    | | lia | lia
    | f_equal; lia | f_equal; lia | reflexivity | rewrite unsigned_lit by lia; reflexivity ].
  intros y0 y3 y5 y6 y7.
  remember (psum (skipn 18 g) 32) as ps eqn:Eps.
  assert (PB : 0 <= ps <= 255 * 32) by (rewrite Eps; pose proof (psum_range (skipn 18 g) 32); lia).
  step. step.
  rewrite rf_land255 by lia.
  replace (ps mod 256) with (blocksum (skipn 18 g)) by (unfold blocksum; rewrite Eps; reflexivity).
  clear Eps.
  destruct (Z.eqb_spec (blocksum (skipn 18 g)) 0) as [BS|BS]; cbv iota; [|nfail_on].
  assert (FRT : fg_fr len g = true) by (apply fr_iff; repeat split; first [assumption | lia]).
  step. step.
  rewrite (rf_beq (nth 19 g (Z_to_bv 8 0)) 1) by lia.
  change (bv_unsigned (nth 19 g (Z_to_bv 8 0))) with (bat g 19).
  destruct (Z.eqb_spec (bat g 19) 1) as [G1|G1]; cbn [negb]; cbv iota.
  - eapply (L_first_on FgFirst);
      [ rewrite (cl_nn_on NZh), FRT, (proj2 (Z.eqb_eq _ _) G1); reflexivity | reflexivity
      | split; [exact EN1 | exact EN2] | exact DJAh | exact FR | exact ST | exact MU | exact WM | exact MI
      | exact HS | exact HG ].
  - eapply L_second_on;
      [ exact NZh | exact FRT | exact G1 | exact DJAh | exact DJBh | exact OUTh | exact FR | exact ST | exact MU
      | exact WM | exact MI | exact HS | exact HG ].
Qed.

(* 0x859e4 .. 0x85a44: prologue and the argument checks. *)
Lemma L_top_on : forall (sp0 t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) junk,
  sp0 = Z_to_bv 64 S ->
  rw_cells rsegs mE (S + -112) [CB 112 junk] -> stk rsegs mE (S - 4672) (S + -112) -> mem_inv rsegs mE ->
  (NZ_on -> 50 <= len -> bytes_at rsegs mE fr g) ->
  (NZ_on -> rw_cells rsegs mE f [CB 72 st] /\ OUT_on /\ DJA_on /\ DJB_on) ->
  evtF rsegs RNG Qf_on
    (MS (mkR ra sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 pa)
             (Z_to_bv 64 pp) (Z_to_bv 64 pn) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ff (Z_to_bv 64 0x859e4) fc None mE (seg_rom rsegs)).
Proof.
  intros sp0 t0 t1 t2 a6 a7 t3 t4 t5 t6 junk -> FR ST MI HFg HO.
  pose proof (munch_refl [(S - 4672, S)] mE) as MU.
  pose proof (wmono_refl rsegs mE) as WM.
  do 14 step.
  step. step. step.
  rewrite (fa_beq f 0) by lia. destruct (Z.eqb_spec f 0) as [Z0|Z0]; cbv iota; [rfail_on|].
  step. step.
  rewrite (fa_beq fr 0) by lia. destruct (Z.eqb_spec fr 0) as [Z1|Z1]; cbv iota; [rfail_on|].
  step. step.
  rewrite (fa_beq pa 0) by lia. destruct (Z.eqb_spec pa 0) as [Z2|Z2]; cbv iota; [rfail_on|].
  step. step.
  rewrite (fa_beq pp 0) by lia. destruct (Z.eqb_spec pp 0) as [Z3|Z3]; cbv iota; [rfail_on|].
  step. step.
  rewrite (fa_beq pn 0) by lia. destruct (Z.eqb_spec pn 0) as [Z4|Z4]; cbv iota; [rfail_on|].
  assert (NZh : NZ_on) by (unfold NZ_on; tauto).
  destruct (HO NZh) as (HS0 & OUTh & DJAh & DJBh).
  eapply L_chk_on; [ exact NZh | exact (HFg NZh) | exact HS0 | exact OUTh | exact DJAh | exact DJBh
                | exact FR | exact ST | exact MU | exact WM | exact MI ].
Qed.

End P_on.

(* The form the run proof above is written against, as fragment_contract_F_conj: the owner's premises with RNG bound
   last and the guarded rng premises of a buffer conjoined; the _on shadow premise and post. *)
Definition fragment_contract_F_conj_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f fr len pa pp pn : Z) (st g : list byte)
         (RNG : footprint),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 fr -> a2 = Z_to_bv 64 len ->
    a3 = Z_to_bv 64 pa -> a4 = Z_to_bv 64 pp -> a5 = Z_to_bv 64 pn ->
    0 <= f < 2^64 -> 0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) ->
    length g = 50%nat -> length st = 72%nat ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> bytes_at rsegs m fr g) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rw_cells rsegs m f [CB 72 st] /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       wr_at rsegs m pa 2 /\ wr_at rsegs m pp 8 /\ wr_at rsegs m pn 8 /\
       all_dj [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (fr, fr + 50);
               (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K, bv_unsigned sp)]) ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m -> B.ShadowRwOn.shadow_rw_on (reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g) m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m fr 50) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    (* the footprint *)
    rng_bytes RNG ->
    rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    sh_word_rng RNG (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) REAC_CTRL_IDENTITY_FRAGMENT_K ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len ->
       rng RNG fr 50 /\
       rng RNG (shadow_addr fr / 8 * 8) (shadow_addr (fr + 50 - 1) / 8 * 8 + 8 - shadow_addr fr / 8 * 8)) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       rng RNG f 72 /\
       rng RNG (shadow_addr f / 8 * 8) (shadow_addr (f + 72 - 1) / 8 * 8 + 8 - shadow_addr f / 8 * 8) /\
       rng RNG pa 2 /\
       rng RNG (shadow_addr pa / 8 * 8) (shadow_addr (pa + 2 - 1) / 8 * 8 + 8 - shadow_addr pa / 8 * 8) /\
       rng RNG pp 8 /\
       rng RNG (shadow_addr pp / 8 * 8) (shadow_addr (pp + 8 - 1) / 8 * 8 + 8 - shadow_addr pp / 8 * 8) /\
       rng RNG pn 8 /\
       rng RNG (shadow_addr pn / 8 * 8) (shadow_addr (pn + 8 - 1) / 8 * 8 + 8 - shadow_addr pn / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_ret (fg_class f fr pa pp pn len st g)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K f pa pp pn (bv_unsigned sp) (fg_class f fr pa pp pn len st g))
           m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (bv_unsigned sp) /\
         fg_mem f pa pp pn st g (fg_class f fr pa pp pn len st g) m' /\
         asan_cells m' /\ (forall P : Z -> Prop, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_FRAGMENT) fc None m (seg_rom rsegs)).

Theorem reac_ctrl_identity_fragment_holds_F_conj_on :
  asan_memcpy_contract_F_on -> bcmp_wrap_contract_F_on -> reac_ctrl_record_cksum_verify_contract_F_on ->
  fragment_contract_F_conj_on.
Proof.
  intros MCPY BCMPw CKV. unfold fragment_contract_F_conj_on.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m f fr len pa pp pn st g RNG Ea0 Ea1 Ea2 Ea3 Ea4 Ea5 Hf Hfr Hlen Hpa Hpp Hpn Hspmod STk Hg Hst
    HFrec HOrec MI HCE HSW Hlo Hhi HAGc HAFc HB1c HB2c HB3c HB4c HB5c RBYc RIMGc RSTKc RWSc RGGc RGFc.
  subst a0 a1 a2 a3 a4 a5.
  unfold REAC_CTRL_IDENTITY_FRAGMENT_K, REAC_CTRL_IDENTITY_FRAGMENT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  (* the window's shadow word span, in the cover form shw (at off = ASAN_K) that the run's proof names *)
  assert (RSTKSc : shw RNG ASAN_K (bv_unsigned sp - 4672) 4672)
    by (destruct RWSc as [E|H]; [discriminate E | exact H]).
  assert (Esp : sp = Z_to_bv 64 (bv_unsigned sp)) by (apply bv_eq; rewrite unsigned_lit by lia; reflexivity).
  carve_frame 112%nat STk.
  rewrite Esp.
  eapply evtF_mono.
  - eapply (L_top_on MCPY BCMPw CKV ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f fr len pa pp pn
                  (bv_unsigned sp) ASAN_K st g RNG);
      [ exact Hf | exact Hfr | exact Hlen | exact Hpa | exact Hpp | exact Hpn
      | split; [unfold HIGHMEM_BEG in Hlo; exact Hlo | unfold APPMEM_END in Hhi; exact Hhi]
      | exact Hg | exact Hst | exact HCE | exact HSW
      | apply rt_asan_rt; [exact HCE | intros x Hx; cbn [outside]; split; [|exact I];
          clear -Hx Hlo; unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia]
      | intros _ _ _ _ _; exact (conj HB1c (conj HB2c (conj HB3c (conj HB4c HB5c))))
      | intros NZh; unfold NZ_on in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          pose proof (HAFc N1 N2 N3 N4 N5) as ASFh;
          destruct ASFh as (Af & Apa & App & Apn & Happ & Hdj);
          pose proof (fa_so5 m f pa pp pn (bv_unsigned sp - 4672) (bv_unsigned sp) Af Apa App Apn Hlo Hhi) as SO;
          split; [exact (conj Af (conj Apa (conj App (conj Apn (conj Happ Hdj)))))|];
          unfold SRF_on, W5_on;
          split; [apply rt_shadow_rd; [exact Af | exact SO] |];
          split; [apply rt_addressable; exact Af |];
          split; [apply rt_shadow_rd; [exact Apa | exact SO] |];
          split; [apply rt_addressable; exact Apa |];
          split; [apply rt_shadow_rd; [exact App | exact SO] |];
          split; [apply rt_addressable; exact App |];
          split; [apply rt_rt3; exact App |];
          split; [apply rt_shadow_rd; [exact Apn | exact SO] |];
          split; [apply rt_addressable; exact Apn |];
          apply rt_rt3; exact Apn
      | intros NZh L50; unfold NZ_on in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          pose proof (HAGc N1 N2 N3 N4 N5 L50) as Afr;
          pose proof (HAFc N1 N2 N3 N4 N5) as (Af & Apa & App & Apn & _);
          pose proof (fa_so5 m f pa pp pn (bv_unsigned sp - 4672) (bv_unsigned sp) Af Apa App Apn Hlo Hhi) as SO;
          unfold ASG_on, W5_on; split; [exact Afr | split; [apply rt_shadow_rd; [exact Afr | exact SO]
                                                      | apply rt_addressable; exact Afr]]
      | reflexivity | exact RBYc | exact RIMGc | exact RSTKc | exact RSTKSc
      | intros NZh; unfold NZ_on in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          unfold RGF_on; exact (RGFc N1 N2 N3 N4 N5)
      | intros NZh L50; unfold NZ_on in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          unfold RGG_on; exact (RGGc N1 N2 N3 N4 N5 L50)
      | reflexivity | exact FR | exact STk | exact MI
      | intros NZh L50; unfold NZ_on in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          exact (HFrec N1 N2 N3 N4 N5 L50)
      | intros NZh; unfold NZ_on in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          destruct (HOrec N1 N2 N3 N4 N5) as (HS & M2 & M8 & M8' & W2 & W8 & W8' & DJ);
          cbn [all_dj dj_from] in DJ;
          split; [exact HS|]; split; [unfold OUT_on; clear -M2 M8 M8' W2 W8 W8'; tauto|];
          clear -DJ; unfold DJA_on, DJB_on; repeat split; try tauto; lia ].
  - intros ms' HQ. unfold Qf_on in HQ. rewrite !(unsigned_lit (bv_unsigned sp)) by lia. exact HQ.
Qed.

(* The owner's text (reac_ctrl_identity_fragment_contract_F_on of reac_ctrl_identity_fragment_c.v) from the form above,
   by reac_ctrl_identity_fragment_holds_F's script. *)
Theorem reac_ctrl_identity_fragment_holds_F_on :
  asan_memcpy_contract_F_on -> bcmp_wrap_contract_F_on -> reac_ctrl_record_cksum_verify_contract_F_on ->
  reac_ctrl_identity_fragment_contract_F_on.
Proof.
  intros MCPY BCMPw CKV.
  pose proof (reac_ctrl_identity_fragment_holds_F_conj_on MCPY BCMPw CKV) as HC.
  unfold fragment_contract_F_conj_on in HC. unfold reac_ctrl_identity_fragment_contract_F_on.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m f fr len pa pp pn st g Ea0 Ea1 Ea2 Ea3 Ea4 Ea5 Hf Hfr Hlen Hpa Hpp Hpn Hspmod STk Hg Hst
    HFrec HOrec MI HCE HSW Hlo Hhi HAGc HAFc HB1c HB2c HB3c HB4c HB5c RBYc RIMGc RSTKc RWSc
    RGfr RGfrs RGf RGfs RGpa RGpas RGpp RGpps RGpn RGpns.
  apply (HC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            F fc m f fr len pa pp pn st g RNG); try assumption.
  - intros N1 N2 N3 N4 N5 L50.
    split; [exact (RGfr N1 N2 N3 N4 N5 L50)|].
    replace (fr + 50 - 1) with (fr + 49) by lia. exact (RGfrs N1 N2 N3 N4 N5 L50).
  - intros N1 N2 N3 N4 N5.
    split; [exact (RGf N1 N2 N3 N4 N5)|].
    split; [replace (f + 72 - 1) with (f + 71) by lia; exact (RGfs N1 N2 N3 N4 N5)|].
    split; [exact (RGpa N1 N2 N3 N4 N5)|].
    split; [replace (pa + 2 - 1) with (pa + 1) by lia; exact (RGpas N1 N2 N3 N4 N5)|].
    split; [exact (RGpp N1 N2 N3 N4 N5)|].
    split; [replace (pp + 8 - 1) with (pp + 7) by lia; exact (RGpps N1 N2 N3 N4 N5)|].
    split; [exact (RGpn N1 N2 N3 N4 N5)|].
    replace (pn + 8 - 1) with (pn + 7) by lia. exact (RGpns N1 N2 N3 N4 N5).
Qed.
