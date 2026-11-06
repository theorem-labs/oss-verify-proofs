(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/C_reac_ctrl_classify_box_frameLib.v, with its module paths and module names changed; 1693 of its 1755 lines of code are new or changed and 927 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcFrag RcFragLib
  RcParseLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFPLib memcmp_c bcmp_wrap_c
  asan_memcpy_c asan_memcpy_cF reac_ctrl_identity_fragment_c asan_memcpy_c_on asan_memcpy_cF_on bcmp_wrap_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnK.
(* Last: StepF's step (evtF goals) must shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* The two narrowed callee proofs, for the closed corollary at the end of this file.  Loaded without Import: their
   notations and tactics must not shadow the ones this proof's script is written against. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpyF_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_on.
Import ListNotations.
Open Scope Z_scope.

(* Route (C) (a Theorem Labs lane 09:20Z; form of record 09:38Z, amended 09:58Z and 10:33Z): the proof of
   reac_ctrl_identity_fragment_contract_F_on (reac_ctrl_identity_fragment_c.v), from the narrowed footprint callee
   contracts asan_memcpy_contract_F_on (a Theorem Labs lane, asan_memcpy_cF_on.v) and bcmp_wrap_contract_F_on (a Theorem Labs lane,
   bcmp_wrap_c_on.v), as Section hypotheses, in the form image B's lib/B/Prog/reac_ctrl_identity_fragment_F.v (Section P) takes the old contracts in; image A's old proof reac_ctrl_identity_fragment_F.v is not in this delivery.  It is the script
   of reac_ctrl_identity_fragment_F.v (whose theorems stay there with their own proofs: they take the old callee
   contracts, which do not give the narrowed ones), with the changes of reac_ctrl_identity_fragment_on.v: HSW narrowed
   to reac_ctrl_identity_fragment_shadow_R, the forall-P post in Qf / rt0 / rtW / rt_post (ShadowRwOnK.fl_shadow_rw_on),
   each callee's shadow premise from HSW narrowed to the callee's R (R_first, R_bcmp, R_join), and
   mem_after_store_opt redefined Local.  The closed corollary at the end instantiates the two hypotheses with
   a Theorem Labs lane's asan_memcpy_holds_F_on (asan_memcpyF_on.v) and a Theorem Labs lane's bcmp_wrap_holds_F_on (bcmp_wrap_on.v).
   The old file's header follows. *)
(* The footprint twin of the A proof of reac_ctrl_identity_fragment (0x84f68): the same run as an ExecF.evtF
   under a footprint RNG (reac_ctrl_identity_fragment_contract_F of reac_ctrl_identity_fragment_c.v), by the
   script of that proof over StepF's step.  Every access of the run is closed from one rng premise: the image
   [IMG_LO, IMG_HI) (instruction fetches and the absolute cells), the stack window [S - 4656, S) of this frame and
   of its callees' frames with the 8-aligned WORD span of its shadow bytes, and, per buffer, the buffer bytes and
   the 8-aligned WORD cover of its shadow bytes.
   This file holds no Axiom, Parameter or admit; the two callee contracts stay Section hypotheses of the
   theorem, as they are in the plain proof. *)
(* reac_ctrl_identity_fragment in the asan image (0x84f68): the plain proof (lib/Prog/reac_ctrl_identity_fragment.v)
   with a 96-byte frame (ra, s0-s10), s8 = the shadow offset (read through the GOT slot 0x9fad0), a shadow check
   before each load and store of its own (each passes from the addressable-range premises, so __asan_report_* is not
   reached), the copies through __asan_memcpy (0x52028) and the compare through the bcmp wrapper (0x42970). *)

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

Lemma firstn1_skipn : forall (A : Type) (d : A) (xs : list A) (i : nat),
  (i < length xs)%nat -> firstn 1 (skipn i xs) = [nth i xs d].
Proof.
  intros A d xs. induction xs as [|x xs IH]; intros i Hi; cbn in Hi; [lia|].
  destruct i as [|i]; cbn; [reflexivity | apply IH; lia].
Qed.

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

(* The shadow is apart from application memory: the bytes of an addressable range and the window above HIGHMEM_BEG
   are outside it, and the runtime's cells are outside the ranges the contract keeps apart from them. *)
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

(* The _F forms of the two callee contracts this proof uses are their owners' shared statements, each proved for
   this image: __asan_memcpy's is a Theorem Labs lane's asan_memcpy_contract_F (lib/A/Prog/asan_memcpy_cF.v), proved as
   asan_memcpy_holds_F (asan_memcpyF.v); the bcmp wrapper's is its owner's bcmp_wrap_contract_F
   (lib/A/Prog/bcmp_wrap_c.v (an earlier version, blob 270745d3d2e, not in this delivery)), proved as bcmp_wrap_holds_F (lib/A/Prog/bcmp_wrap_F.v (not in this delivery), blob
   5840c43dcd, a working branch).  This proof uses both only through the Section hypotheses MCPY and
   BCMP; the corollary at the end of this file instantiates them.
   The bcmp wrapper's statement writes the image range as its own IMG_LO / IMG_HI (0x10000 and Contract.GT =
   0x5fe000), the same range as ImgBounds.v's IMG_LO / IMG_HI that this file's RIMG premise names. *)

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

(* A callee's region at a call, written over the literals the call site's registers carry. *)
Lemma mcpy_R_lit : forall (a0 a1 a2 : word) (d s n a : Z), asan_memcpy_shadow_R a0 a1 a2 a ->
  bv_unsigned a0 = d -> bv_unsigned a1 = s -> bv_unsigned a2 = n ->
  0 <= d < 2^64 -> 0 <= s < 2^64 -> 0 <= n < 2^64 ->
  asan_memcpy_shadow_R (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a.
Proof.
  intros a0 a1 a2 d s n a H E0 E1 E2 R0 R1 R2. unfold asan_memcpy_shadow_R in *.
  rewrite !unsigned_lit by lia. rewrite E0, E1, E2 in H. exact H.
Qed.

Section P.
Hypothesis MCPY : asan_memcpy_contract_F_on.
Hypothesis BCMP : bcmp_wrap_contract_F_on.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Ff : bvmap 5 word) (fc : bv 32)
  (mE : word -> option byte) (f fr len pa pp pn S off : Z) (st g : list byte) (RNG : footprint).
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rfr : 0 <= fr < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis Rpa : 0 <= pa < 2^64.
Hypothesis Rpp : 0 <= pp < 2^64.
Hypothesis Rpn : 0 <= pn < 2^64.
(* The window [S - K, S) in AppMem above HIGHMEM_BEG (K = 4656). *)
Hypothesis RS : 0x10007fff8000 <= S - 4656 /\ S <= 0x800000000000.
Hypothesis Hg : length g = 50%nat.
Hypothesis Hst : length st = 72%nat.
Hypothesis HCE : asan_cells mE.
Hypothesis HSW : A.ShadowRwOn.shadow_rw_on (reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g) mE.
Hypothesis HRT : asan_rt rsegs mE GOT_CELL_K CELL_K off [(S - 4656, S)].

Local Notation CL := (fg_class f fr pa pp pn len st g).
Local Notation FRc := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition W5 : list (Z * Z) := [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (S - 4656, S)].

Definition Qf : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_ret CL))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             Ff (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch (fg_fp 4656 f pa pp pn S CL) mE m' /\ wmono rsegs mE m' /\ mem_inv rsegs m' /\
    stk rsegs m' (S - 4656) S /\ fg_mem f pa pp pn st g CL m' /\ asan_cells m' /\
    (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P mE -> A.ShadowRwOn.shadow_rw_on P m').

Definition NZ : Prop := f <> 0 /\ fr <> 0 /\ pa <> 0 /\ pp <> 0 /\ pn <> 0.
Definition DJA : Prop :=
  (f + 72 <= fr \/ fr + 50 <= f) /\ (f + 72 <= S - 4656 \/ S <= f) /\ (fr + 50 <= S - 4656 \/ S <= fr).
Definition DJB : Prop :=
  (f + 72 <= pa \/ pa + 2 <= f) /\ (f + 72 <= pp \/ pp + 8 <= f) /\ (f + 72 <= pn \/ pn + 8 <= f) /\
  (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
  (pa + 2 <= S - 4656 \/ S <= pa) /\ (pp + 8 <= S - 4656 \/ S <= pp) /\ (pn + 8 <= S - 4656 \/ S <= pn).
Definition OUT : Prop :=
  wr_at rsegs mE pa 2 /\ wr_at rsegs mE pp 8 /\ wr_at rsegs mE pn 8 /\ pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0.

(* The asan premises at the entry memory: the 72 bytes at f and the outputs addressable (and their shadow bytes read
   with the offset off), f + 78 in AppMem, the outputs apart from the runtime's cells; the 50 bytes at fr. *)
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
(* The bcmp wrapper's runtime cells (as the contract supplies them), at the entry memory; all in low rodata. *)
Hypothesis HB1 : bytes_at rsegs mE REAL_BCMP (le8 (wa bcmp_wrap_c.BCMP)).
Hypothesis HB2 : bytes_at rsegs mE REAL_MEMCMP (le8 (wa MEMCMP)).
Hypothesis HB3 : bytes_at rsegs mE GOT_CF (le8 (wa CF)).
Hypothesis HB4 : bytes_at rsegs mE (CF + 254) [Z_to_bv 8 1].
Hypothesis HB5 : bytes_at rsegs mE (CF + 255) [Z_to_bv 8 1].
(* Those cells are low rodata (below the application window). *)
Hypothesis HBlo : REAL_BCMP + 8 <= S - 4656 /\ REAL_MEMCMP + 8 <= S - 4656 /\ GOT_CF + 8 <= S - 4656 /\
                  CF + 256 <= S - 4656 /\ 0 <= REAL_BCMP /\ 0 <= REAL_MEMCMP /\ 0 <= GOT_CF /\ 0 <= CF.
(* The footprint of this run, region by region: the image (every fetch and every absolute cell, including the
   runtime's GOT_CELL_K and CELL_K), the stack window of this frame and of the callees' frames below it with the
   8-aligned WORD span of its shadow bytes (which holds the shadow of the frame of __asan_memcpy that its contract
   takes), and each buffer with the 8-aligned WORD cover of its shadow bytes.  RGF and RGG hold under the same
   guards as ASF and ASG. *)
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
(* Route 1 one level down (the callees' footprint contracts) weakens a byte-wise footprint to a union of rng
   ranges, so both contracts take a footprint that is decided byte by byte (lib/Lib/RngBytes.v). *)
Hypothesis RBY : rng_bytes RNG.
Hypothesis RIMG : rng RNG IMG_LO (IMG_HI - IMG_LO).
Hypothesis RSTK : rng RNG (S - 4656) 4656.
Hypothesis RSTKS : shw RNG off (S - 4656) 4656.
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

Lemma cl_nz : CL <> FgRefuse -> NZ.
Proof. intros H. unfold NZ. repeat split; intros E; apply H; apply rf_class_refuse; tauto. Qed.

(* The runtime's cells and the shadow survive a run that writes only inside the window, or inside W5: every shadow
   region present at mE is present at mc. *)
Lemma rt0 : forall mc, munch [(S - 4656, S)] mE mc -> wmono rsegs mE mc ->
  asan_cells mc /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P mE -> A.ShadowRwOn.shadow_rw_on P mc).
Proof.
  intros mc MU WM. split.
  - apply (fl_asan_cells _ mE mc HCE MU). intros x Hx. cbn [outside]. unfold RT_LO, RT_HI in Hx.
    split; [lia | exact I].
  - intros P HP. apply (A.ShadowRwOnK.fl_shadow_rw_on P _ mE mc HP MU WM). intros x Hx. cbn [outside].
    split; [|exact I].
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
  apply (fa_ro5 f pa pp pn (S - 4656) S); [unfold HIGHMEM_BEG; lia | exact DJ].
Qed.

Lemma rtW : forall W' mc, NZ -> munch W' mE mc -> sub_fp W' W5 -> wmono rsegs mE mc ->
  asan_cells mc /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P mE -> A.ShadowRwOn.shadow_rw_on P mc).
Proof.
  intros W' mc NZh MU Hs WM. split.
  - apply (fl_asan_cells W' mE mc HCE MU). intros x Hx. apply Hs. exact (ro5 NZh x Hx).
  - intros P HP. apply (A.ShadowRwOnK.fl_shadow_rw_on P W' mE mc HP MU WM). intros x Hx. apply Hs.
    exact (so5 NZh x Hx).
Qed.

Lemma rt_post : forall c m, c = CL -> munch (fg_fp 4656 f pa pp pn S c) mE m -> wmono rsegs mE m ->
  asan_cells m /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P mE -> A.ShadowRwOn.shadow_rw_on P m).
Proof.
  intros c m Hc MU WM.
  destruct c; cbn [fg_fp] in MU; try exact (rt0 m MU WM);
    (eapply (rtW _ m); [apply cl_nz; rewrite <- Hc; discriminate | exact MU
                      | unfold sub_fp, W5; cbn [outside]; intros; tauto | exact WM]).
Qed.

(* +0x1e8 .. +0x21c: the epilogue. *)
Lemma L_epi : forall c (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                         x28 x29 x30 x31 : word) m,
  c = CL -> x10 = Z_to_bv 64 (fg_ret c) ->
  rw_cells rsegs m (S + -96) FRc -> stk rsegs m (S - 4656) (S + -96) ->
  munch (fg_fp 4656 f pa pp pn S c) mE m -> wmono rsegs mE m ->
  mem_inv rsegs m -> fg_mem f pa pp pn st g c m ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
             x24 x25 x26 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85150) fc None m (seg_rom rsegs)).
Proof.
  intros c x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 m
    Hc Hx FR ST MU WM MI FM.
  destruct (rt_post c m Hc MU WM) as [AC SR].
  subst c x10.
  pose proof (stk_release rsegs m _ _ _ ST FR ltac:(lia)) as ST'.
  cbn [cells_size csize Nat.add] in ST'. replace (S + -96 + Z.of_nat 96) with S in ST' by lia. clear ST.
  do 14 step.
  try replace (S + -96 + 96) with S by lia.
  apply evtF_done. unfold Qf.
  do 14 eexists. exists m. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact FM|].
  split; [exact AC | exact SR].
Qed.

Lemma L_ret0 : forall c (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                          x28 x29 x30 x31 : word) m,
  c = CL -> fg_ret c = 0 ->
  rw_cells rsegs m (S + -96) FRc -> stk rsegs m (S - 4656) (S + -96) ->
  munch (fg_fp 4656 f pa pp pn S c) mE m -> wmono rsegs mE m ->
  mem_inv rsegs m -> fg_mem f pa pp pn st g c m ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
             x24 x25 x26 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x8514c) fc None m (seg_rom rsegs)).
Proof.
  intros c x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 m
    Hc Hr FR ST MU WM MI FM.
  step.
  eapply L_epi; [exact Hc | | exact FR | exact ST | exact MU | exact WM | exact MI | exact FM].
  rewrite Hr. reflexivity.
Qed.

Lemma cl_nn : NZ -> CL =
  if negb (fg_fr len g) then FgNone
  else if bat g 19 =? 1 then FgFirst
  else if negb (fg_keep st g) then FgDrop
  else if negb (fg_close st g) then FgJoin
  else FgClose.
Proof. intros (H1 & H2 & H3 & H4 & H5). apply rf_class_nn; assumption. Qed.

Lemma L_none : forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                        x28 x29 x30 x31 : word) m,
  NZ -> fg_fr len g = false ->
  rw_cells rsegs m (S + -96) FRc -> stk rsegs m (S - 4656) (S + -96) ->
  munch [(S - 4656, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
             x24 x25 x26 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x8514c) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 m
    NZh HF FR ST MU WM MI.
  eapply (L_ret0 FgNone); [ | reflexivity | exact FR | exact ST | exact MU | exact WM | exact MI | exact I].
  rewrite (cl_nn NZh), HF. reflexivity.
Qed.

(* A shadow byte read of the j-th byte (X = a + j) of an addressable range, at the current memory m reached by a
   run that writes only inside W' (a subset of W5): the shadow byte k is readable and passes the 1-byte check. *)
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

(* The same, returning also the shadow address bound, for a check that reloads a precomputed shadow address. *)
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

(* A 2-byte store check: the slow path compares X mod 8 + 1 to the shadow byte. *)
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

(* An 8-byte aligned store check: the shadow byte of an addressable aligned 8-slot is 0. *)
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

(* A 1-byte shadow read at the current memory m directly (facts already at m), for the sum loops. *)
Lemma fa_rd1m : forall (m : word -> option byte) (a n j X : Z) (W : list (Z * Z)),
  asan_shadow_rd rsegs m off a n W -> asan_addressable rsegs m off a n -> 0 <= j < n -> X = a + j ->
  exists k : byte, ov_read_bytes rsegs m (wa (X / 8 + off)) 1 = Some [k]
    /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros m a n j X W SR AD Hj ->.
  destruct (asan_shadow_read rsegs m off a n W j SR Hj) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [exact (AD j k Hj BK) | apply rc_byte_signed].
Qed.

(* Restrict addressability/shadow-readability to a sub-range. *)
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

(* Two addressable points within 100 bytes lie in the same app region, so everything between is addressable. *)
Lemma fa_app_mid : forall a b x, app_mem a -> app_mem b -> a <= x <= b -> b - a <= 100 -> app_mem x.
Proof. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia. Qed.

Lemma fa_so1 : forall x, in_shadow x -> outside [(S - 4656, S)] x.
Proof.
  intros x Hx. cbn [outside]. split; [|exact I].
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hx. pose proof RS. lia.
Qed.

(* Model lemmas (identical to the plain proof): the frame/record predicates as conjunctions. *)
Lemma fr_iff : fg_fr len g = true <->
  50 <= len /\ bat g 16 = 205 /\ bat g 17 = 234 /\ bat g 18 = 4 /\ (bat g 19 = 1 \/ bat g 19 = 2) /\
  bat g 22 = 0 /\ bat g 23 = 2 /\ bat g 24 = 0 /\ bat g 25 = 254 /\ 1 <= fg_n g /\ fg_n g <= 22 /\
  blocksum (skipn 18 g) = 0.
Proof. unfold fg_fr. rewrite !andb_true_iff, !orb_true_iff, !Z.eqb_eq, !Z.leb_le. tauto. Qed.

Local Notation JN := (fg_join st g).

Lemma close_iff : fg_close st g = true <->
  14 <= fg_T st g /\ bat JN 8 = 240 /\ bat JN 9 = 65 /\ bat JN 11 = 0 /\ bat JN 12 = 0 /\ bat JN 13 = 18 /\
  bat JN 14 = 18 /\ bat JN 15 = 5 /\ bat JN 16 = 0 /\ bat JN (7 + fg_T st g) = 247 /\
  recsum (bsl JN 15 (fg_T st g - 8)) = 0.
Proof. unfold fg_close. rewrite !andb_true_iff, !Z.eqb_eq, !Z.leb_le. tauto. Qed.

Lemma keep_iff : fg_keep st g = true <-> fg_hf st <> 0 /\ fg_src_eq st g = true /\ fg_T st g <= 64.
Proof. unfold fg_keep. rewrite !andb_true_iff, negb_true_iff, Z.eqb_neq, Z.leb_le. tauto. Qed.

Lemma cl_k : NZ -> fg_fr len g = true -> bat g 19 <> 1 ->
  CL = if negb (fg_keep st g) then FgDrop else if fg_close st g then FgClose else FgJoin.
Proof.
  intros NZh FRT B19. rewrite (cl_nn NZh), FRT, (proj2 (Z.eqb_neq _ _) B19). cbn [negb].
  destruct (fg_keep st g), (fg_close st g); reflexivity.
Qed.

(* Route (C): the path facts at each call, and each callee's region at its call inside
   reac_ctrl_identity_fragment_shadow_R. *)
Lemma cl_first_b19 : NZ -> fg_fr len g = true -> CL = FgFirst -> bat g 19 = 1.
Proof.
  intros NZh FRT HC. rewrite (cl_nn NZh), FRT in HC. revert HC.
  destruct (Z.eqb_spec (bat g 19) 1) as [B|B]; [intros _; exact B|].
  destruct (fg_keep st g), (fg_close st g); cbn [negb]; intros HC; discriminate HC.
Qed.

Lemma cl_join_keep : NZ -> fg_fr len g = true -> CL = (if fg_close st g then FgClose else FgJoin) ->
  bat g 19 <> 1 /\ fg_keep st g = true.
Proof.
  intros NZh FRT HC. rewrite (cl_nn NZh), FRT in HC. revert HC.
  destruct (Z.eqb_spec (bat g 19) 1) as [B|B]; destruct (fg_keep st g), (fg_close st g); cbn [negb];
    intros HC; first [discriminate HC | exact (conj B eq_refl)].
Qed.

Lemma R_first : NZ -> fg_fr len g = true -> bat g 19 = 1 -> forall a,
  asan_memcpy_shadow_R (Z_to_bv 64 f) (Z_to_bv 64 (fr + 6)) (Z_to_bv 64 6) a \/
  asan_memcpy_shadow_R (Z_to_bv 64 (f + 8)) (Z_to_bv 64 (fr + 27)) (Z_to_bv 64 (fg_n g)) a ->
  reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g a.
Proof.
  intros (N1 & N2 & N3 & N4 & N5) FRT B a Ha. unfold reac_ctrl_identity_fragment_shadow_R.
  exact (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj FRT (or_introl (conj B Ha)))))))).
Qed.

Lemma R_bcmp : NZ -> fg_fr len g = true -> bat g 19 <> 1 -> fg_hf st <> 0 -> forall a,
  bcmp_wrap_shadow_R f (fr + 6) 6 a -> reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g a.
Proof.
  intros (N1 & N2 & N3 & N4 & N5) FRT B H6 a Ha. unfold reac_ctrl_identity_fragment_shadow_R.
  exact (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj FRT (or_intror (conj B (conj H6 (or_introl Ha)))))))))).
Qed.

Lemma R_join : NZ -> fg_fr len g = true -> bat g 19 <> 1 -> fg_keep st g = true -> forall a,
  asan_memcpy_shadow_R (Z_to_bv 64 (f + 8 + fg_lf st)) (Z_to_bv 64 (fr + 27)) (Z_to_bv 64 (fg_n g)) a ->
  reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g a.
Proof.
  intros (N1 & N2 & N3 & N4 & N5) FRT B K a Ha. pose proof (proj1 (proj1 keep_iff K)) as H6.
  unfold reac_ctrl_identity_fragment_shadow_R.
  exact (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj FRT
           (or_intror (conj B (conj H6 (or_intror (conj K Ha))))))))))).
Qed.

Ltac fz := rewrite ?length_le8, ?length_le2; cbn [cells_size csize Nat.add length inside]; lia.

Definition hide (P : Prop) : Prop := P.
Lemma hide_i : forall P : Prop, P -> hide P. Proof. intros P H. exact H. Qed.
Ltac fzu D := let H := fresh "DU" in pose proof D as H; unfold hide in H; fz.

(* The shadow-check tactics. *)
Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.
Ltac steps_to P :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 P) _ _ _ _) => idtac
  | _ => step; steps_to P
  end.

(* A 1-byte shadow check of address X (its srli at the current pc); r is the register the slow path's andi writes,
   generalized at the join, and the __asan_report_* path is not reached. *)
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

(* A 1-byte shadow check that reloads a precomputed shadow address (no srli/add), as the byte-6 store does. *)
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

(* Handle the bnez of a 1-byte shadow check whose shadow byte k was already loaded (value loads interleaved);
   r is the slow path's andi destination, X the checked address, OK the addressability fact. *)
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

(* The same for a 2-byte store check: the slow path adds 1 before the compare. *)
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

Ltac fa_sub := unfold sub_fp, W5; intro; cbn [outside]; tauto.

Lemma fa_addr_sub : forall mm p n p' n', addressable mm p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  addressable mm p' n'.
Proof.
  intros mm p n p' n' (H0 & Hn & He & HA) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HA. lia.
Qed.

Lemma fa_addr_app : forall mm p n i, addressable mm p n -> 0 <= i < n -> app_mem (p + i).
Proof. intros mm p n i (_ & _ & _ & HA) Hi. exact (proj1 (HA i Hi)). Qed.

Lemma fa_addr_pre : forall (mm : word -> option byte) (p n n' : Z),
  addressable mm p n -> 0 <= n' -> n' <= n -> addressable mm p n'.
Proof.
  intros mm p n n' AD H0 Hn. apply (fa_addr_sub mm p n p n') in AD; [exact AD | lia | lia | lia].
Qed.

(* The frame/drop/join footprint [(f, f+72); (S-4656, S)]: shadow and the runtime's cells are outside it. *)
Lemma fa_sowf : NZ -> forall x, in_shadow x -> outside [(f, f + 72); (S - 4656, S)] x.
Proof. intros NZh x Hx. pose proof (so5 NZh x Hx) as H. unfold W5 in H. cbn [outside] in H |- *. tauto. Qed.
Lemma fa_rowf : NZ -> forall x, RT_LO <= x < RT_HI -> outside [(f, f + 72); (S - 4656, S)] x.
Proof. intros NZh x Hx. pose proof (ro5 NZh x Hx) as H. unfold W5 in H. cbn [outside] in H |- *. tauto. Qed.

(* +0x194 .. +0x1c8: the block-sum loop over fr + 18 .. fr + 50, each load shadow-checked. *)
Lemma loopB : forall (Q : machine_state -> Prop)
  (r1 r2 r3 r4 r5 r6 r7 r8 r9 r12 r17 r18 r19 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 : word)
  (m : word -> option byte) (A : Z) (bs : list byte) (c : nat) (W : list (Z * Z)),
  bytes_at rsegs m A bs -> (c <= length bs)%nat -> 0 < A -> A + Z.of_nat c <= 2 ^ 64 ->
  asan_shadow_rd rsegs m off A (Z.of_nat c) W -> asan_addressable rsegs m off A (Z.of_nat c) ->
  rng RNG A (Z.of_nat c) -> rng RNG (A / 8 + off) ((A + Z.of_nat c - 1) / 8 - A / 8 + 1) ->
  (forall y4 y5 y6 : word, evtF rsegs RNG Q
     (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 (Z_to_bv 64 (A + Z.of_nat c)) (Z_to_bv 64 (A + Z.of_nat c)) r12
              (Z_to_bv 64 (psum bs c)) y4 y5 y6 r17 r18 r19 r20 r21 r22 r23 (Z_to_bv 64 off) r25 r26 r27 r28 r29 r30 r31)
         Ff (Z_to_bv 64 0x85130) fc None m (seg_rom rsegs))) ->
  forall n i (a0 a1 x4 y5 y6 : word), (i + n = c)%nat -> (0 < n)%nat ->
  a0 = Z_to_bv 64 (A + Z.of_nat i) -> a1 = Z_to_bv 64 (A + Z.of_nat i) -> bv_unsigned x4 = Z.of_nat n ->
  evtF rsegs RNG Q
    (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 a0 a1 r12 (Z_to_bv 64 (psum bs i)) x4 y5 y6 r17 r18 r19 r20 r21 r22 r23
             (Z_to_bv 64 off) r25 r26 r27 r28 r29 r30 r31)
        Ff (Z_to_bv 64 0x85108) fc None m (seg_rom rsegs)).
Proof.
  intros Q r1 r2 r3 r4 r5 r6 r7 r8 r9 r12 r17 r18 r19 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31
    m A bs c W HB Hc HA HAc SR AD RDAT RSH HK.
  induction n as [|n IH]; intros i a0 a1 x4 y5 y6 Hin Hn E0 E1 H4; [lia|].
  subst a0 a1.
  pose proof (rd_byte rsegs m A bs i HB ltac:(lia)) as RD.
  pose proof (psum_range bs i) as PR.
  chk1 (A + Z.of_nat i) (Z_to_bv 5 16)
    (fa_rd1m m A (Z.of_nat c) (Z.of_nat i) (A + Z.of_nat i) W SR AD ltac:(lia) eq_refl).
  step. step. step. step.
  rewrite psum_S_zxb.
  step. step.
  rewrite (rc_eqb0 (bv_unsigned x4 + -1)) by lia.
  destruct n as [|n].
  - replace (bv_unsigned x4 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. cbv iota.
    replace (A + Z.of_nat i + 1) with (A + Z.of_nat c) by lia.
    replace (Datatypes.S i) with c by lia. apply HK.
  - replace (bv_unsigned x4 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. cbv iota.
    apply (IH (Datatypes.S i)); first [lia | f_equal; lia | rewrite unsigned_lit by lia; lia].
Qed.

(* +0x434 .. +0x458: the record-sum loop over the joined record (f + 15 ..), each load shadow-checked. *)
Lemma loopR : forall (Q : machine_state -> Prop)
  (r1 r2 r3 r4 r5 r6 r7 r8 r9 r16 r17 r18 r19 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31 : word)
  (m : word -> option byte) (A : Z) (bs : list byte) (c : nat) (W : list (Z * Z)),
  bytes_at rsegs m A bs -> (c <= length bs)%nat -> 0 < A -> A + Z.of_nat c <= 2 ^ 64 ->
  asan_shadow_rd rsegs m off A (Z.of_nat c) W -> asan_addressable rsegs m off A (Z.of_nat c) ->
  rng RNG A (Z.of_nat c) -> rng RNG (A / 8 + off) ((A + Z.of_nat c - 1) / 8 - A / 8 + 1) ->
  (forall y3 y4 y5 : word, evtF rsegs RNG Q
     (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 (Z_to_bv 64 (A + Z.of_nat c)) (Z_to_bv 64 (A + Z.of_nat c))
              (Z_to_bv 64 (psum bs c)) y3 y4 y5 r16 r17 r18 r19 r20 r21 r22 r23 (Z_to_bv 64 off) r25 r26 r27 r28 r29
              r30 r31)
         Ff (Z_to_bv 64 0x853c4) fc None m (seg_rom rsegs))) ->
  forall n i (a0 a1 x3 y4 y5 : word), (i + n = c)%nat -> (0 < n)%nat ->
  a0 = Z_to_bv 64 (A + Z.of_nat i) -> a1 = Z_to_bv 64 (A + Z.of_nat i) -> bv_unsigned x3 = Z.of_nat n ->
  evtF rsegs RNG Q
    (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 a0 a1 (Z_to_bv 64 (psum bs i)) x3 y4 y5 r16 r17 r18 r19 r20 r21 r22 r23
             (Z_to_bv 64 off) r25 r26 r27 r28 r29 r30 r31)
        Ff (Z_to_bv 64 0x8539c) fc None m (seg_rom rsegs)).
Proof.
  intros Q r1 r2 r3 r4 r5 r6 r7 r8 r9 r16 r17 r18 r19 r20 r21 r22 r23 r25 r26 r27 r28 r29 r30 r31
    m A bs c W HB Hc HA HAc SR AD RDAT RSH HK.
  induction n as [|n IH]; intros i a0 a1 x3 y4 y5 Hin Hn E0 E1 H3; [lia|].
  subst a0 a1.
  pose proof (rd_byte rsegs m A bs i HB ltac:(lia)) as RD.
  pose proof (psum_range bs i) as PR.
  chk1 (A + Z.of_nat i) (Z_to_bv 5 15)
    (fa_rd1m m A (Z.of_nat c) (Z.of_nat i) (A + Z.of_nat i) W SR AD ltac:(lia) eq_refl).
  step. step. step. step.
  rewrite psum_S_zxb.
  step. step.
  rewrite (rc_eqb0 (bv_unsigned x3 + -1)) by lia.
  destruct n as [|n].
  - replace (bv_unsigned x3 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. cbv iota.
    replace (A + Z.of_nat i + 1) with (A + Z.of_nat c) by lia.
    replace (Datatypes.S i) with c by lia. apply HK.
  - replace (bv_unsigned x3 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. cbv iota.
    apply (IH (Datatypes.S i)); first [lia | f_equal; lia | rewrite unsigned_lit by lia; lia].
Qed.

(* +0x2d8: the drop path (store 0 at f + 6, return 0). *)
Lemma L_drop : forall c (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25
                        x28 x29 x30 x31 : word) m,
  c = CL -> c = FgDrop -> (f + 72 <= S - 4656 \/ S <= f) ->
  rw_cells rsegs m (S + -96) FRc -> stk rsegs m (S - 4656) (S + -96) ->
  munch [(f, f + 72); (S - 4656, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  rw_cells rsegs m f [CB 72 st] ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -96)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
             (Z_to_bv 64 (f + 6)) x24 x25 (Z_to_bv 64 ((f + 6) / 8 + off)) s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85240) fc None m (seg_rom rsegs)).
Proof.
  intros c x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x28 x29 x30 x31 m
    Hc HcD DfS FR ST MU WM MI HS.
  assert (NZh : NZ) by (apply cl_nz; rewrite <- Hc, HcD; discriminate).
  destruct (HAF NZh) as ((Af & _) & SRf & ADf & _).
  pose proof (rt_addressable_bound mE f 72 Af) as (Hf0 & _ & Hf2).
  rngf NZh.
  chk1p (f + 6) (Z_to_bv 5 11)
    (fa_rdb m [(f, f + 72); (S - 4656, S)] f 72 6 (f + 6) SRf ADf MU ltac:(fa_sub) ltac:(lia) eq_refl).
  step. step. step.
  eapply (L_epi FgDrop); [ rewrite <- HcD; exact Hc | reflexivity | exact FR | exact ST | exact MU | exact WM
    | exact MI | ].
  cbn [fg_mem]. eapply fa_rw_bytes; [exact HS|]. cbn [cells_bytes cbytes]. rewrite ?app_nil_r. reflexivity.
Qed.

(* +0x228 .. +0x280: the first-record path (two copies, store 1 and n, return 0). *)
Lemma L_first : forall c (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x25 x26
                         x28 x29 x30 x31 : word) m,
  c = CL -> c = FgFirst -> 1 <= fg_n g <= 22 -> DJA ->
  rw_cells rsegs m (S + -96) FRc -> stk rsegs m (S - 4656) (S + -96) ->
  munch [(S - 4656, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  rw_cells rsegs m f [CB 72 st] -> bytes_at rsegs m fr g ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -96)) gp tp x5 x6 x7 (Z_to_bv 64 f) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             (Z_to_bv 64 fr) x21 (zxb (nth 26 g (Z_to_bv 8 0))) x23 (Z_to_bv 64 off) x25 x26 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85190) fc None m (seg_rom rsegs)).
Proof.
  intros c x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x25 x26 x28 x29 x30 x31 m
    Hc HcF Hn DJAh FR ST MU WM MI HS HG.
  assert (NZh : NZ) by (apply cl_nz; rewrite <- Hc, HcF; discriminate).
  assert (FRT : fg_fr len g = true).
  { destruct (fg_fr len g) eqn:E; [reflexivity|].
    assert (HN : CL = FgNone) by (rewrite (cl_nn NZh), E; reflexivity).
    rewrite Hc in HcF. rewrite HN in HcF. discriminate HcF. }
  pose proof (proj1 (proj1 fr_iff FRT)) as Hlen50.
  pose proof (cl_first_b19 NZh FRT ltac:(rewrite <- Hc; exact HcF)) as G19.
  destruct (HAF NZh) as ((Af & Aa & Ap & An & Happ & DJrt) & SRf & ADf & _).
  destruct (HAG NZh Hlen50) as (Ag & SRg & ADg).
  pose proof (rt_addressable_bound mE f 72 Af) as (Hf0 & _ & Hf2).
  pose proof (rt_addressable_bound mE fr 50 Ag) as (Hr0 & _ & Hr2).
  rngf NZh. rngg NZh Hlen50.
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
  apply (munch_weaken [(S - 4656, S)] [(f, f + 72); (S - 4656, S)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  pose proof (fl_addressable [(f, f + 72); (S - 4656, S)] mE m f 72 Af MU (fa_sowf NZh)) as ADfm.
  pose proof (fl_addressable [(f, f + 72); (S - 4656, S)] mE m fr 50 Ag MU (fa_sowf NZh)) as ADgm.
  pose proof (rtW [(f, f + 72); (S - 4656, S)] m NZh MU ltac:(fa_sub) WM) as (ACm & SRm).
  (* the shared statement, with its shadow word spans (sh_word_rng of asan_memcpy_cF.v) written out *)
  pose proof MCPY as HM. unfold asan_memcpy_contract_F_on, sh_word_rng, sh_al8_lo, sh_al8_hi in HM. cbv zeta in HM.
  step. step. step. step.
  assert (U0 : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 (fr + 6)) = fr + 6) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  assert (U3 : bv_unsigned (Z_to_bv 64 (S + -96)) = S + -96) by (apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HM with (src := bsl g 6 6) (junk := bsl st 0 6) (lo := S - 4656).
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
    - eapply A.ShadowRwOn.shadow_rw_on_mono; [|exact (SRm _ HSW)].
      intros a Ha. apply (R_first NZh FRT G19). left.
      exact (mcpy_R_lit _ _ _ _ _ _ a Ha U0 U1 U2 ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact MI.
    - exact RBY.
    - exact RIMG.
    - rewrite U3. unfold ASAN_MEMCPY_K. apply (rng_sub' RNG (S - 4656) 4656); [exact RSTK | lia].
    - rewrite U0, U2. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - rewrite U1, U2. apply (rng_sub' RNG fr 50); [exact RGr | lia].
    - rewrite U0, U2. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off f 72 f 6 ltac:(lia) ltac:(lia) ltac:(lia) RGfs).
    - rewrite U1, U2. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off fr 50 (fr + 6) 6 ltac:(lia) ltac:(lia) ltac:(lia) RGrs).
    - rewrite U3. unfold ASAN_MEMCPY_K. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off (S - 4656) 4656 (S + -96 - 2224) 2224 ltac:(lia) ltac:(lia) ltac:(lia) RSTKS). }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                  & E & MU2 & WM2 & MI2 & ST2 & RW2 & BD2 & AC2 & SR2).
  subst ms'. clear BD2.
  rewrite U0, U2 in RW2. rewrite U0, U2, U3 in MU2. rewrite U3 in ST2.
  assert (SUB1 : sub_fp [(f, f + 6); (S + -96 - 2224, S + -96)] [(f, f + 72); (S - 4656, S)])
    by (intros x; cbn [outside]; intros (H1 & H2 & _); split; [lia | split; [lia | exact I]]).
  pose proof (munch_trans [(f, f + 72); (S - 4656, S)] mE m m2 MU (munch_weaken _ _ m m2 SUB1 MU2)) as MU3.
  pose proof (wmono_trans rsegs mE m m2 WM WM2) as WM3.
  pose proof (rw_cells_transport rsegs [(f, f + 6); (S + -96 - 2224, S + -96)] m m2 (f + 6) [CB 2 (bsl st 6 2)]
                P6 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as P6'.
  pose proof (rw_cells_transport rsegs [(f, f + 6); (S + -96 - 2224, S + -96)] m m2 (f + 8)
                [CB (Z.to_nat (fg_n g)) (bsl st 8 (fg_n g))] P8 MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as P8'.
  pose proof (bytes_at_transport rsegs [(f, f + 6); (S + -96 - 2224, S + -96)] m m2 (f + (8 + fg_n g))
                (skipn (Z.to_nat (8 + fg_n g)) st) PR MU2
                ltac:(cbn [disjoint_from]; rewrite length_skipn, Hst; repeat split; try exact I; lia)) as PR'.
  pose proof (bytes_at_transport rsegs [(f, f + 6); (S + -96 - 2224, S + -96)] m m2 (fr + 27) (bsl g 27 (fg_n g))
                GB MU2 ltac:(cbn [disjoint_from]; rewrite (rf_bsl_length g 27 (fg_n g)) by (rewrite ?Hg; lia);
                             repeat split; try exact I; lia)) as GB'.
  pose proof (rw_cells_transport rsegs [(f, f + 6); (S + -96 - 2224, S + -96)] m m2 (S + -96) FRc FR MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FR2.
  replace (Z.of_nat (length st)) with 72 in HSw by (rewrite Hst; reflexivity).
  pose proof (wr_at_transport rsegs m m2 f 72 HSw WM2) as WRm2.
  replace (ret_pc (Z_to_bv 64 0x851a0)) with (Z_to_bv 64 0x851a0)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (fl_addressable [(f, f + 72); (S - 4656, S)] mE m2 f 72 Af MU3 (fa_sowf NZh)) as ADfm2.
  pose proof (fl_addressable [(f, f + 72); (S - 4656, S)] mE m2 fr 50 Ag MU3 (fa_sowf NZh)) as ADgm2.
  step. step. step. step.
  assert (U4 : bv_unsigned (zxb (nth 26 g (Z_to_bv 8 0))) = fg_n g) by (exact (rf_zxb_u _)).
  assert (U5 : bv_unsigned (Z_to_bv 64 (f + 8)) = f + 8) by (apply unsigned_lit; lia).
  assert (U6 : bv_unsigned (Z_to_bv 64 (fr + 27)) = fr + 27) by (apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HM with (src := bsl g 27 (fg_n g)) (junk := bsl st 8 (fg_n g)) (lo := S - 4656).
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
    - eapply A.ShadowRwOn.shadow_rw_on_mono; [|exact (SR2 _ (SRm _ HSW))].
      intros a Ha. apply (R_first NZh FRT G19). right.
      exact (mcpy_R_lit _ _ _ _ _ _ a Ha U5 U6 U4 ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact MI2.
    - exact RBY.
    - exact RIMG.
    - rewrite U3. unfold ASAN_MEMCPY_K. apply (rng_sub' RNG (S - 4656) 4656); [exact RSTK | lia].
    - rewrite U5, U4. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - rewrite U6, U4. apply (rng_sub' RNG fr 50); [exact RGr | lia].
    - rewrite U5, U4. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off f 72 (f + 8) (fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) RGfs).
    - rewrite U6, U4. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off fr 50 (fr + 27) (fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) RGrs).
    - rewrite U3. unfold ASAN_MEMCPY_K. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off (S - 4656) 4656 (S + -96 - 2224) 2224 ltac:(lia) ltac:(lia) ltac:(lia) RSTKS). }
  intros ms'' PO2.
  destruct PO2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m3
                  & E2 & MU4 & WM4 & MI4 & ST4 & RW4 & BD4 & AC4 & SR4).
  subst ms''. clear BD4.
  rewrite U5, U4 in RW4. rewrite U5, U4, U3 in MU4. rewrite U3 in ST4.
  replace (ret_pc (Z_to_bv 64 0x851b0)) with (Z_to_bv 64 0x851b0)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (SUB2 : sub_fp [(f + 8, f + 8 + fg_n g); (S + -96 - 2224, S + -96)] [(f, f + 72); (S - 4656, S)])
    by (intros x; cbn [outside]; intros (H1 & H2 & _); split; [lia | split; [lia | exact I]]).
  pose proof (munch_trans [(f, f + 72); (S - 4656, S)] mE m2 m3 MU3 (munch_weaken _ _ m2 m3 SUB2 MU4)) as MU5.
  pose proof (wmono_trans rsegs mE m2 m3 WM3 WM4) as WMm3.
  pose proof (wr_at_transport rsegs m2 m3 f 72 WRm2 WM4) as WRm3.
  pose proof (proj1 (rf_rw_parts rsegs m2 f 6 (bsl g 6 6) RW2)) as B0m2.
  pose proof (bytes_at_transport rsegs [(f + 8, f + 8 + fg_n g); (S + -96 - 2224, S + -96)] m2 m3 f (bsl g 6 6)
                B0m2 MU4 ltac:(cbn [disjoint_from]; rewrite rf_bsl_length by (rewrite ?Hg; lia);
                               repeat split; try exact I; lia)) as B0.
  pose proof (proj1 (rf_rw_parts rsegs m3 (f + 8) (Z.to_nat (fg_n g)) (bsl g 27 (fg_n g)) RW4)) as B8.
  pose proof (bytes_at_transport rsegs [(f + 8, f + 8 + fg_n g); (S + -96 - 2224, S + -96)] m2 m3 (f + (8 + fg_n g))
                (skipn (Z.to_nat (8 + fg_n g)) st) PR' MU4
                ltac:(cbn [disjoint_from]; rewrite length_skipn, Hst; repeat split; try exact I; lia)) as BR.
  pose proof (rw_cells_transport rsegs [(f + 8, f + 8 + fg_n g); (S + -96 - 2224, S + -96)] m2 m3 (S + -96) FRc
                FR2 MU4 WM4 ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FR3.
  clear RW4 PR' RW2 P6 P6' P8 P8' PR GS GB GB' B0m2 WRm2 MU MU2 MU3 MU4 WM WM2 WM3 WM4 MI MI2 ST ST2
    ADfm ADgm ADfm2 ADgm2 ACm SRm AC2 SR2 FR FR2.
  (* +0x248 .. +0x25c: store n at f + 7 (checked). *)
  step.
  chk1 (f + 7) (Z_to_bv 5 12)
    (fa_rd1 m3 [(f, f + 72); (S - 4656, S)] f 72 7 (f + 7) SRf ADf MU5 ltac:(fa_sub) ltac:(lia) eq_refl).
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
  pose proof (rw_cells_frame rsegs m3 (S + -96) FRc (f + 7) [nth 26 g (Z_to_bv 8 0)] FR3 ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(cbn [cells_size csize Nat.add length]; lia)) as FR3a.
  pose proof (mem_inv_store rsegs m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)] MI4 ltac:(cbn [length]; exact SO7)) as MI4a.
  pose proof (stk_write rsegs m3 (S - 4656) (S + -96) (f + 7) [nth 26 g (Z_to_bv 8 0)] ST4 ltac:(lia)
                ltac:(cbn [length]; lia)) as ST4a.
  apply (munch_write [(f, f + 72); (S - 4656, S)] mE m3 (f + 7) [nth 26 g (Z_to_bv 8 0)]) in MU5;
    [| lia | cbn [length]; lia | cbn [inside length]; lia].
  apply (wmono_write rsegs mE m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)]) in WMm3.
  pose proof (wr_at_transport rsegs m3 (write_to_mem m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)]) f 72 WRm3
                (wmono_write rsegs m3 m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)] (wmono_refl rsegs m3))) as WRm4.
  set (m4 := write_to_mem m3 (wa (f + 7)) [nth 26 g (Z_to_bv 8 0)]) in *. clearbody m4.
  (* +0x25c .. +0x280: store 1 at f + 6 (checked), return 0. *)
  step.
  chk1 (f + 6) (Z_to_bv 5 11)
    (fa_rd1 m4 [(f, f + 72); (S - 4656, S)] f 72 6 (f + 6) SRf ADf MU5 ltac:(fa_sub) ltac:(lia) eq_refl).
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
  pose proof (rw_cells_frame rsegs m4 (S + -96) FRc (f + 6) [Z_to_bv 8 1] FR3a ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(cbn [cells_size csize Nat.add length]; lia)) as FR3b.
  pose proof (mem_inv_store rsegs m4 (wa (f + 6)) [Z_to_bv 8 1] MI4a ltac:(cbn [length]; exact SO6)) as MI4b.
  pose proof (stk_write rsegs m4 (S - 4656) (S + -96) (f + 6) [Z_to_bv 8 1] ST4a ltac:(lia)
                ltac:(cbn [length]; lia)) as ST4b.
  apply (munch_write [(f, f + 72); (S - 4656, S)] mE m4 (f + 6) [Z_to_bv 8 1]) in MU5;
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

(* +0x4dc .. +0x55c: the close path, store the three outputs (each checked), return 1. *)
Lemma L_close : forall c (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x26 x28 x29 x30 x31 : word) m,
  c = CL -> c = FgClose -> 14 <= fg_T st g <= 64 -> length JN = 72%nat -> DJB ->
  rw_cells rsegs m (S + -96) FRc -> stk rsegs m (S - 4656) (S + -96) ->
  munch [(f, f + 72); (S - 4656, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  bytes_at rsegs m f (fg_clear JN) -> OUT ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -96)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 pp) (Z_to_bv 64 pa) x20 x21 x22 x23 (Z_to_bv 64 off) (Z_to_bv 64 (fg_T st g)) x26 s11
             x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85444) fc None m (seg_rom rsegs)).
Proof.
  intros c x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x26 x28 x29 x30 x31 m
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
  apply (munch_weaken [(f, f + 72); (S - 4656, S)] W5) in MU;
    [|unfold sub_fp, W5; cbn [outside]; intros; tauto].
  step.
  chk1 (f + 17) (Z_to_bv 5 12) (fa_rd1 m W5 f 72 17 (f + 17) SRf ADf MU ltac:(fa_sub) ltac:(lia) eq_refl).
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
  step. step.
  step. rewrite ?(unsigned_lit pp) by lia. rewrite rc_shr3.
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
  (* pp 8-byte check at the post-pa-store memory *)
  pose proof (asan_shadow_rd_munch rsegs mE _ off pp 8 W5 W5 SRp MU1 ltac:(fa_sub)) as SRp1.
  pose proof (asan_addressable_munch rsegs mE _ off pp 8 W5 W5 ADp SRp MU1 ltac:(fa_sub)) as ADp1.
  pose proof (asan_rt3_munch rsegs mE _ off pp 8 W5 W5 R3p SRp MU1 ltac:(fa_sub)) as R3p1.
  destruct (asan_shadow_read rsegs _ off pp 8 W5 0 SRp1 ltac:(lia)) as (kpp & RKpp & BKpp).
  pose proof (asan_check_8 rsegs _ off pp 8 0 kpp ADp1 R3p1 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Mp) BKpp) as K0pp.
  pose proof (rc_signed0_unsigned0 kpp K0pp) as K0ppu.
  rewrite Z.add_0_r in RKpp.
  step. step.
  replace (zxb kpp) with (Z_to_bv 64 0) by (unfold zxb; rewrite K0ppu; reflexivity).
  step.
  change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (fa_store_ok mm pp 8 8 (wr_at_write rsegs _ pp 8 _ _ WP) ltac:(lia)) as SP end.
  step.
  change (Z_to_bv 64 pp) with (wa pp). rewrite ?(unsigned_lit (f + 19)) by lia.
  pose proof (munch_write W5 mE _ pp (le8 (Z_to_bv 64 (f + 19))) MU1 ltac:(lia)
                ltac:(rewrite length_le8; lia) ltac:(unfold W5; cbn [inside]; rewrite length_le8; lia)) as MU2.
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
  - change (fg_fp 4656 f pa pp pn S FgClose)
      with [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8); (S - 4656, S)].
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
  | reflexivity | eassumption | eassumption
  | match goal with H : munch _ mE _ |- _ => exact H end | eassumption | eassumption
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
    MU : munch [(f, f + 72); (S - 4656, S)] mE ?m |- _ =>
      chk1 (f + i) r (fa_rd1 m [(f, f + 72); (S - 4656, S)] f 72 i (f + i) SRf ADf MU ltac:(fa_sub) ltac:(lia) eq_refl)
  end.

(* +0x314 .. +0x4dc: close checks on the joined record, the record-sum loop, then the close path. *)
Lemma L_tail : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x26 x28 x29 x30 x31 : word) m,
  CL = (if fg_close st g then FgClose else FgJoin) -> 1 <= fg_n g <= 22 -> fg_T st g <= 64 -> DJB ->
  (f + 72 <= S - 4656 \/ S <= f) -> 0 < f -> OUT ->
  rw_cells rsegs m (S + -96) FRc -> stk rsegs m (S - 4656) (S + -96) ->
  munch [(f, f + 72); (S - 4656, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  bytes_at rsegs m f (fg_clear JN) ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -96)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) (Z_to_bv 64 14)
             x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 pp) (Z_to_bv 64 pa) x20 (Z_to_bv 64 (f + 8)) x22 x23
             (Z_to_bv 64 off) (Z_to_bv 64 (fg_T st g)) x26 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85278) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x26 x28 x29 x30 x31 m
    HCL Hn HT DJBh DfS Hf0 OUTh FR ST MU WM MI CJ.
  assert (NZh : NZ) by (apply cl_nz; rewrite HCL; destruct (fg_close st g); discriminate).
  destruct (HAF NZh) as ((Af & _) & SRf & ADf & _).
  pose proof (rt_addressable_bound mE f 72 Af) as (Hfa0 & _ & Hf2).
  rngf NZh.
  pose proof (rf_fg_join_length st g Hst Hg Hn HT) as LJ.
  pose proof (rf_clear_length _ LJ) as LCJ.
  pose proof (bytes_at_bound rsegs m f _ CJ) as BF. rewrite LCJ in BF.
  assert (T0 : 0 <= fg_T st g).
  { unfold fg_T, fg_lf, bat. pose proof (byte_range (nth (Z.to_nat 7) st (Z_to_bv 8 0))). lia. }
  step.
  rewrite (fa_ltu (fg_T st g) 14) by lia.
  destruct (Z.ltb_spec (fg_T st g) 14) as [T14|T14]; cbv iota; [jfail|].
  jchk 0x8527c 8 (Z_to_bv 5 11). jld 8%nat. step. step. jbyte 8%nat 8 240.
  jchk 0x8529c 9 (Z_to_bv 5 12). jld 9%nat. step. step. jbyte 9%nat 9 65.
  jchk 0x852bc 11 (Z_to_bv 5 12). jld 11%nat. step. jbyte 11%nat 11 0.
  jchk 0x852d8 12 (Z_to_bv 5 12). jld 12%nat. step. jbyte 12%nat 12 0.
  jchk 0x852f4 13 (Z_to_bv 5 12). jld 13%nat. step. step. jbyte 13%nat 13 18.
  jchk 0x85314 14 (Z_to_bv 5 12). jld 14%nat. step. step. jbyte 14%nat 14 18.
  jchk 0x85334 15 (Z_to_bv 5 12). jld 15%nat. step. step. jbyte 15%nat 15 5.
  jchk 0x85354 16 (Z_to_bv 5 13). jld 16%nat. step. jbyte 16%nat 16 0.
  steps_to 0x85374.
  replace (f + 8 + fg_T st g + -1) with (f + (7 + fg_T st g)) by lia.
  chk1 (f + (7 + fg_T st g)) (Z_to_bv 5 13)
    (fa_rd1 m [(f, f + 72); (S - 4656, S)] f 72 (7 + fg_T st g) (f + (7 + fg_T st g)) SRf ADf MU ltac:(fa_sub)
       ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m f (fg_clear JN) (Z.to_nat (7 + fg_T st g)) CJ ltac:(rewrite LCJ; lia)) as RDJ.
  rewrite (rf_clear_nth _ (Z.to_nat (7 + fg_T st g)) _ LJ ltac:(lia)) in RDJ.
  rewrite (Z2Nat.id (7 + fg_T st g)) in RDJ by lia.
  step. clear RDJ. step. step.
  rewrite (rf_beq (nth (Z.to_nat (7 + fg_T st g)) (fg_join st g) (Z_to_bv 8 0)) 247) by lia.
  change (bv_unsigned (nth (Z.to_nat (7 + fg_T st g)) (fg_join st g) (Z_to_bv 8 0)))
    with (bat (fg_join st g) (7 + fg_T st g)).
  destruct (Z.eqb_spec (bat (fg_join st g) (7 + fg_T st g)) 247) as [B7|B7]; cbn [negb]; cbv iota; [|jfail].
  pose proof (asan_shadow_rd_munch rsegs mE m off f 72 W5 [(f, f + 72); (S - 4656, S)] SRf MU ltac:(fa_sub)) as SRfm.
  pose proof (asan_addressable_munch rsegs mE m off f 72 W5 [(f, f + 72); (S - 4656, S)] ADf SRf MU ltac:(fa_sub)) as ADfm.
  pose proof (fa_sr_sub m off f 72 15 (Z.of_nat (Z.to_nat (fg_T st g - 8))) W5 SRfm ltac:(lia) ltac:(lia)
                ltac:(rewrite Z2Nat.id by lia; lia)) as SRr.
  pose proof (fa_ad_sub m off f 72 15 (Z.of_nat (Z.to_nat (fg_T st g - 8))) ADfm ltac:(lia) ltac:(lia)
                ltac:(rewrite Z2Nat.id by lia; lia)) as ADr.
  pose proof (rf_bytes_skip rsegs _ f _ 15 CJ ltac:(rewrite LCJ; lia)) as HBr.
  change (Z.to_nat 15) with 15%nat in HBr. rewrite (rf_clear_skipn _ 15 LJ ltac:(lia)) in HBr.
  step. step. step.
  eapply (loopR Qf) with (A := f + 15) (bs := skipn 15 (fg_join st g)) (c := Z.to_nat (fg_T st g - 8)) (W := W5)
                         (n := Z.to_nat (fg_T st g - 8)) (i := 0%nat);
    [ exact HBr | rewrite length_skipn, LJ; lia | lia | rewrite Z2Nat.id by lia; lia | exact SRr | exact ADr
    | apply (rng_sub' RNG f 72); [exact RGf | lia]
    | exact (shw_bytes RNG off f 72 (f + 15) (Z.of_nat (Z.to_nat (fg_T st g - 8)))
               ltac:(lia) ltac:(lia) ltac:(lia) RGfs)
    | | lia | lia | f_equal; lia | f_equal; lia | rewrite unsigned_lit by lia; symmetry; apply Z2Nat.id; lia ].
  intros y3 y4 y5.
  pose proof (psum_range (skipn 15 (fg_join st g)) (Z.to_nat (fg_T st g - 8))) as PR.
  step. step. step.
  rewrite rf_land127 by lia.
  pose proof (rf_recsum_bsl (fg_join st g) 15 (fg_T st g - 8) ltac:(lia) ltac:(lia) ltac:(rewrite LJ; lia)) as ER.
  change (Z.to_nat 15) with 15%nat in ER. rewrite <- ER.
  destruct (Z.eqb_spec (recsum (bsl (fg_join st g) 15 (fg_T st g - 8))) 0) as [RS0|RS0]; cbn [negb]; cbv iota;
    [|jfail].
  assert (EC : fg_close st g = true) by (apply close_iff; repeat split; first [assumption | lia]).
  eapply (L_close FgClose); [ rewrite HCL, EC; reflexivity | reflexivity | lia | exact LJ | exact DJBh | exact FR
    | exact ST | exact MU | exact WM | exact MI | exact CJ | exact OUTh ].
Qed.

(* +0x30c .. +0x324: append the body at f + 8 + lf, clear byte 6, fall to the close checks. *)
Lemma L_join : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word) m,
  CL = (if fg_close st g then FgClose else FgJoin) -> 1 <= fg_n g <= 22 -> fg_T st g <= 64 -> DJA -> DJB -> OUT ->
  0 < f ->
  rw_cells rsegs m (S + -96) FRc -> stk rsegs m (S - 4656) (S + -96) ->
  munch [(f, f + 72); (S - 4656, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  bytes_at rsegs m f st -> wr_at rsegs m f (Z.of_nat (length st)) -> bytes_at rsegs m fr g ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -96)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn)
             (zxb (nth 7 st (Z_to_bv 8 0))) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 pp) (Z_to_bv 64 pa)
             (Z_to_bv 64 fr) x21 (zxb (nth 26 g (Z_to_bv 8 0))) (Z_to_bv 64 (f + 6)) (Z_to_bv 64 off)
             (Z_to_bv 64 (fg_T st g)) (Z_to_bv 64 ((f + 6) / 8 + off)) s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x85254) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 m
    HCL Hn HT DJAh DJBh OUTh Hf0 FR ST MU WM MI HSb HSw HG.
  assert (NZh : NZ) by (apply cl_nz; rewrite HCL; destruct (fg_close st g); discriminate).
  assert (FRT : fg_fr len g = true).
  { destruct (fg_fr len g) eqn:E; [reflexivity|].
    assert (HN : CL = FgNone) by (rewrite (cl_nn NZh), E; reflexivity).
    rewrite HN in HCL. destruct (fg_close st g); discriminate HCL. }
  pose proof (proj1 (proj1 fr_iff FRT)) as Hlen50.
  destruct (cl_join_keep NZh FRT HCL) as (G19n & KPh).
  destruct (HAF NZh) as ((Af & Aa & Ap & An & Happ & DJrt) & SRf & ADf & _).
  destruct (HAG NZh Hlen50) as (Ag & SRg & ADg).
  destruct DJAh as (Dff & DfS & DrS).
  pose proof (rt_addressable_bound mE f 72 Af) as (Hfa0 & _ & Hf2).
  pose proof (rt_addressable_bound mE fr 50 Ag) as (Hr0 & _ & Hr2).
  rngf NZh. rngg NZh Hlen50.
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
  pose proof (fl_addressable [(f, f + 72); (S - 4656, S)] mE m f 72 Af MU (fa_sowf NZh)) as ADfm.
  pose proof (fl_addressable [(f, f + 72); (S - 4656, S)] mE m fr 50 Ag MU (fa_sowf NZh)) as ADgm.
  pose proof (rtW [(f, f + 72); (S - 4656, S)] m NZh MU ltac:(fa_sub) WM) as (ACm & SRm).
  pose proof (fa_addr_app m f 72 0 ADfm ltac:(lia)) as APPf0. rewrite Z.add_0_r in APPf0.
  (* the shared statement, with its shadow word spans (sh_word_rng of asan_memcpy_cF.v) written out *)
  pose proof MCPY as HM. unfold asan_memcpy_contract_F_on, sh_word_rng, sh_al8_lo, sh_al8_hi in HM. cbv zeta in HM.
  step. step. step. step. step.
  rewrite ?rf_zxb_u.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st).
  assert (U0 : bv_unsigned (Z_to_bv 64 (f + 8 + fg_lf st)) = f + 8 + fg_lf st) by (apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 (fr + 27)) = fr + 27) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (zxb (nth 26 g (Z_to_bv 8 0))) = fg_n g) by (exact (rf_zxb_u _)).
  assert (U3 : bv_unsigned (Z_to_bv 64 (S + -96)) = S + -96) by (apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HM with (src := bsl g 27 (fg_n g)) (junk := bsl st (8 + fg_lf st) (fg_n g)) (lo := S - 4656).
    - rewrite U1. exact GB.
    - rewrite U2. exact LGB.
    - rewrite U0, U2. exact P8.
    - rewrite U0, U1, U2. destruct Dff as [H|H]; [right; right; lia | right; left; lia].
    - rewrite U2. lia.
    - rewrite U1, U2. apply (fa_addr_sub m fr 50); [exact ADgm | lia | lia | lia].
    - rewrite U0, U2. apply (fa_addr_sub m f 72); [exact ADfm | lia | lia | lia].
    - rewrite U1, U2. unfold end_in_app. right. replace (fr + 27 + fg_n g) with (fr + (27 + fg_n g)) by lia.
      apply (fa_addr_app m fr 50 (27 + fg_n g)); [exact ADgm | lia].
    - rewrite U0, U2. unfold end_in_app. right.
      apply (fa_app_mid f (f + 78) (f + 8 + fg_lf st + fg_n g)); [exact APPf0 | exact Happ | lia | lia].
    - rewrite U0, U1, U2. right. split;
        [replace (fr + 27 + 7) with (fr + 34) by lia; apply (fa_addr_app m fr 50 34); [exact ADgm | lia]
        | apply (fa_app_mid f (f + 78) (f + 8 + fg_lf st + 7)); [exact APPf0 | exact Happ | lia | lia]].
    - rewrite U0, U2. cbn [dj_from] in DJrt. destruct DJrt as [[H|H] _]; [right; lia | left; lia].
    - rewrite U0, U2, U3. unfold ASAN_MEMCPY_K. destruct DfS as [H|H]; [left; lia | right; lia].
    - rewrite U1, U2, U3. unfold ASAN_MEMCPY_K. destruct DrS as [H|H]; [left; lia | right; lia].
    - rewrite U3. exact ST.
    - rewrite U3. unfold ASAN_MEMCPY_K. lia.
    - unfold HIGHMEM_BEG. lia.
    - rewrite U3. unfold APPMEM_END. lia.
    - exact ACm.
    - eapply A.ShadowRwOn.shadow_rw_on_mono; [|exact (SRm _ HSW)].
      intros a Ha. apply (R_join NZh FRT G19n KPh).
      exact (mcpy_R_lit _ _ _ _ _ _ a Ha U0 U1 U2 ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact MI.
    - exact RBY.
    - exact RIMG.
    - rewrite U3. unfold ASAN_MEMCPY_K. apply (rng_sub' RNG (S - 4656) 4656); [exact RSTK | lia].
    - rewrite U0, U2. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - rewrite U1, U2. apply (rng_sub' RNG fr 50); [exact RGr | lia].
    - rewrite U0, U2. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off f 72 (f + 8 + fg_lf st) (fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) RGfs).
    - rewrite U1, U2. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off fr 50 (fr + 27) (fg_n g) ltac:(lia) ltac:(lia) ltac:(lia) RGrs).
    - rewrite U3. unfold ASAN_MEMCPY_K. right. unfold shadow_addr. rewrite <- Hoff.
      exact (shw_sub RNG off (S - 4656) 4656 (S + -96 - 2224) 2224 ltac:(lia) ltac:(lia) ltac:(lia) RSTKS). }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                  & E & MU2 & WM2 & MI2 & ST2 & RW2 & BD2 & AC2 & SR2).
  subst ms'. clear BD2.
  rewrite U0, U2 in RW2. rewrite U0, U2, U3 in MU2. rewrite U3 in ST2.
  replace (ret_pc (Z_to_bv 64 0x85268)) with (Z_to_bv 64 0x85268)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (SUB1 : sub_fp [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -96 - 2224, S + -96)]
                        [(f, f + 72); (S - 4656, S)])
    by (intros x; cbn [outside]; intros (H1 & H2 & _); split; [lia | split; [lia | exact I]]).
  pose proof (munch_trans [(f, f + 72); (S - 4656, S)] mE m m2 MU (munch_weaken _ _ m m2 SUB1 MU2)) as MU3.
  pose proof (wmono_trans rsegs mE m m2 WM WM2) as WM3.
  replace (Z.of_nat (length st)) with 72 in HSw by (rewrite Hst; reflexivity).
  pose proof (wr_at_transport rsegs m m2 f 72 HSw WM2) as WRm2.
  pose proof (bytes_at_transport rsegs [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -96 - 2224, S + -96)]
                m m2 f (firstn 6 st) B0 MU2
                ltac:(cbn [disjoint_from]; rewrite LB0; repeat split; try exact I; lia)) as B0m2.
  pose proof (bytes_at_transport rsegs [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -96 - 2224, S + -96)]
                m m2 (f + 7) (bsl st 7 (1 + fg_lf st)) B7 MU2
                ltac:(cbn [disjoint_from]; rewrite LB7, Z2Nat.id by lia; repeat split; try exact I; lia)) as B7m2.
  pose proof (bytes_at_transport rsegs [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -96 - 2224, S + -96)]
                m m2 (f + (8 + fg_T st g)) (skipn (Z.to_nat (8 + fg_T st g)) st) BR MU2
                ltac:(cbn [disjoint_from]; rewrite length_skipn, Hst; repeat split; try exact I; lia)) as BRm2.
  pose proof (rw_cells_transport rsegs [(f + 8 + fg_lf st, f + 8 + fg_lf st + fg_n g); (S + -96 - 2224, S + -96)]
                m m2 (S + -96) FRc FR MU2 WM2
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FR2.
  pose proof (proj1 (rf_rw_parts rsegs m2 (f + 8 + fg_lf st) (Z.to_nat (fg_n g)) (bsl g 27 (fg_n g)) RW2)) as BB.
  (* byte-6 store (shadow reloaded from s10): clear byte 6 *)
  destruct (fa_rdb m2 [(f, f + 72); (S - 4656, S)] f 72 6 (f + 6) SRf ADf MU3 ltac:(fa_sub) ltac:(lia) eq_refl)
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
  pose proof (bytes_at_write_other rsegs m2 (f + 6) [Z_to_bv 8 0] (f + 7) (bsl st 7 (1 + fg_lf st)) B7m2 ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as B7m3.
  pose proof (bytes_at_write_other rsegs m2 (f + 6) [Z_to_bv 8 0] (f + 8 + fg_lf st) (bsl g 27 (fg_n g)) BB ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(cbn [length]; lia)) as BBm3.
  pose proof (bytes_at_write_other rsegs m2 (f + 6) [Z_to_bv 8 0] (f + (8 + fg_T st g))
                (skipn (Z.to_nat (8 + fg_T st g)) st) BRm2 ltac:(lia) ltac:(cbn [length]; lia)
                ltac:(cbn [length]; lia)) as BRm3.
  replace (f + 8 + fg_lf st) with (f + (8 + fg_lf st)) in BBm3 by lia.
  assert (CJ : bytes_at rsegs (write_to_mem m2 (wa (f + 6)) [Z_to_bv 8 0]) f (fg_clear JN)).
  { rewrite fa_clear_join by (first [exact Hst | lia]).
    apply (rf_app _ _ f _ (f + 6)); [exact B0m3 | | rewrite LB0; lia].
    apply (rf_app _ _ (f + 6) _ (f + 7)); [exact B6 | | cbn [length]; lia].
    apply (rf_app _ _ (f + 7) _ (f + (8 + fg_lf st))); [exact B7m3 | | rewrite LB7, Z2Nat.id by lia; lia].
    apply (rf_app _ _ (f + (8 + fg_lf st)) _ (f + (8 + fg_T st g)));
      [exact BBm3 | exact BRm3 | unfold fg_body; rewrite LGB, Z2Nat.id by lia; lia]. }
  pose proof (munch_write [(f, f + 72); (S - 4656, S)] mE m2 (f + 6) [Z_to_bv 8 0] MU3 ltac:(lia)
                ltac:(cbn [length]; lia) ltac:(unfold W5; cbn [inside length]; lia)) as MU4.
  pose proof (wmono_write rsegs mE m2 (wa (f + 6)) [Z_to_bv 8 0] WM3) as WM4.
  pose proof (mem_inv_store rsegs m2 (wa (f + 6)) [Z_to_bv 8 0] MI2 ltac:(cbn [length]; exact SO6)) as MI3.
  pose proof (stk_write rsegs m2 (S - 4656) (S + -96) (f + 6) [Z_to_bv 8 0] ST2 ltac:(lia) ltac:(cbn [length]; lia))
    as ST3.
  pose proof (rw_cells_frame rsegs m2 (S + -96) FRc (f + 6) [Z_to_bv 8 0] FR2 ltac:(lia) ltac:(cbn [length]; lia)
                ltac:(cbn [cells_size csize Nat.add length]; unfold hide in *; lia)) as FR3.
  eapply L_tail; [ exact HCL | exact Hn | exact HT | exact DJBh | exact DfS | exact Hf0 | exact OUTh | exact FR3
    | exact ST3 | exact MU4 | exact WM4 | exact MI3 | exact CJ ].
Qed.

(* +0x2b4 .. +0x320: g[19] = 2; compare, keep (join) or drop the partial record. *)
Lemma L_second : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31 : word) m,
  NZ -> fg_fr len g = true -> bat g 19 <> 1 -> DJA -> DJB -> OUT ->
  rw_cells rsegs m (S + -96) FRc -> stk rsegs m (S - 4656) (S + -96) ->
  munch [(S - 4656, S)] mE m -> wmono rsegs mE m -> mem_inv rsegs m ->
  rw_cells rsegs m f [CB 72 st] -> bytes_at rsegs m fr g ->
  evtF rsegs RNG Qf
    (MS (mkR x1 (Z_to_bv 64 (S + -96)) gp tp x5 x6 x7 (Z_to_bv 64 f) (Z_to_bv 64 pn) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 pp) (Z_to_bv 64 pa) (Z_to_bv 64 fr) x21 (zxb (nth 26 g (Z_to_bv 8 0))) x25 (Z_to_bv 64 off)
             s9 s10 s11 x28 x29 x30 x31)
        Ff (Z_to_bv 64 0x851ec) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x25 x28 x29 x30 x31 m
    NZh FRT B19 DJAh DJBh OUTh FR ST MU WM MI HS HG.
  pose proof DJAh as (Dff & DfS & DrS).
  assert (Hf0 : 0 < f) by (destruct NZh as (Nf & _); lia).
  pose proof (proj1 fr_iff FRT) as (Hlen50 & _ & _ & _ & _ & _ & _ & _ & _ & Hn1 & Hn2 & _).
  pose proof (cl_k NZh FRT B19) as HCL0.
  destruct (HAF NZh) as ((Af & _) & SRf & ADf & _).
  destruct (HAG NZh Hlen50) as (Ag & SRg & ADg).
  pose proof (rt_addressable_bound mE f 72 Af) as (Hfa0 & _ & Hf2).
  pose proof (rt_addressable_bound mE fr 50 Ag) as (Hr0 & _ & Hr2).
  rngf NZh. rngg NZh Hlen50.
  pose proof (bytes_at_bound rsegs m fr g HG) as BG. rewrite Hg in BG.
  pose proof (rw_cells_bound rsegs m f _ HS) as BF. cbn [cells_size csize Nat.add] in BF.
  destruct (rf_rw_parts rsegs m f 72 st HS) as (HSb & HSw & _). clear HS.
  pose proof (byte_range (nth 7 st (Z_to_bv 8 0))) as RL.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st) in RL.
  pose proof (byte_range (nth 26 g (Z_to_bv 8 0))) as RN.
  change (bv_unsigned (nth 26 g (Z_to_bv 8 0))) with (fg_n g) in RN.
  (* bcmp runtime cells at m *)
  pose proof (bytes_at_transport rsegs [(S - 4656, S)] mE m REAL_BCMP (le8 (wa bcmp_wrap_c.BCMP)) HB1 MU
    ltac:(cbn [disjoint_from]; rewrite length_le8; repeat split; try exact I; lia)) as HB1m.
  pose proof (bytes_at_transport rsegs [(S - 4656, S)] mE m REAL_MEMCMP (le8 (wa MEMCMP)) HB2 MU
    ltac:(cbn [disjoint_from]; rewrite length_le8; repeat split; try exact I; lia)) as HB2m.
  pose proof (bytes_at_transport rsegs [(S - 4656, S)] mE m GOT_CF (le8 (wa CF)) HB3 MU
    ltac:(cbn [disjoint_from]; rewrite length_le8; repeat split; try exact I; lia)) as HB3m.
  pose proof (bytes_at_transport rsegs [(S - 4656, S)] mE m (CF + 254) [Z_to_bv 8 1] HB4 MU
    ltac:(cbn [disjoint_from length]; repeat split; try exact I; lia)) as HB4m.
  pose proof (bytes_at_transport rsegs [(S - 4656, S)] mE m (CF + 255) [Z_to_bv 8 1] HB5 MU
    ltac:(cbn [disjoint_from length]; repeat split; try exact I; lia)) as HB5m.
  pose proof (fl_addressable [(S - 4656, S)] mE m f 72 Af MU fa_so1) as ADfm.
  pose proof (fl_addressable [(S - 4656, S)] mE m fr 50 Ag MU fa_so1) as ADgm.
  pose proof (fa_addr_app m f 72 0 ADfm ltac:(lia)) as APPf0. rewrite Z.add_0_r in APPf0.
  apply (munch_weaken [(S - 4656, S)] [(f, f + 72); (S - 4656, S)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  pose proof (rd_byte rsegs m f st 6 HSb ltac:(lia)) as R6.
  (* 0x2b4 .. 0x2c0: shadow check f+6, then load hf *)
  step.
  chk1 (f + 6) (Z_to_bv 5 11) (fa_rd1 m [(f, f + 72); (S - 4656, S)] f 72 6 (f + 6) SRf ADf MU ltac:(fa_sub)
    ltac:(lia) eq_refl).
  step. clear R6. step.
  rewrite (rf_beq (nth 6 st (Z_to_bv 8 0)) 0) by lia.
  change (bv_unsigned (nth 6 st (Z_to_bv 8 0))) with (fg_hf st).
  destruct (Z.eqb_spec (fg_hf st) 0) as [H6|H6]; cbn [negb]; cbv iota.
  { eapply (L_drop FgDrop); [ | reflexivity | exact DfS | exact FR | exact ST | exact MU | exact WM | exact MI | ].
    - rewrite HCL0. destruct (fg_keep st g) eqn:EK; [|reflexivity]. exfalso.
      apply keep_iff in EK. destruct EK as (EK0 & _ & _). lia.
    - rewrite <- Hst. apply fa_rw_of; [exact HSb | rewrite Hst; exact HSw]. }
  destruct (fa_mcmp 6 st (skipn 6 g) ltac:(lia) ltac:(rewrite length_skipn; lia)) as (v & Hv & Rv & Iv).
  pose proof (rf_bytes_skip rsegs m fr g 6 HG ltac:(rewrite Hg; lia)) as G6.
  change (Z.to_nat 6) with 6%nat in G6.
  pose proof BCMP as HBC. unfold bcmp_wrap_contract_F_on in HBC. cbv zeta in HBC.
  step. step. step. step.
  assert (UF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (U6 : bv_unsigned (Z_to_bv 64 (fr + 6)) = fr + 6) by (apply unsigned_lit; lia).
  assert (U6' : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  assert (U3 : bv_unsigned (Z_to_bv 64 (S + -96)) = S + -96) by (apply unsigned_lit; lia).
  eapply evtF_cut.
  { eapply HBC with (ls := st) (rs := skipn 6 g) (v := v) (lo := S - 4656).
    - rewrite UF. exact HSb.
    - rewrite U6. exact G6.
    - rewrite U6'. exact Hv.
    - exact MI.
    - rewrite U6'. lia.
    - rewrite UF, U6'. apply (fa_addr_pre m f 72); [exact ADfm | lia | lia].
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
    - pose proof (rtW [(f, f + 72); (S - 4656, S)] m NZh MU ltac:(fa_sub) WM) as (ACm & _). exact ACm.
    - pose proof (rtW [(f, f + 72); (S - 4656, S)] m NZh MU ltac:(fa_sub) WM) as (_ & SRc).
      eapply A.ShadowRwOn.shadow_rw_on_mono; [|exact (SRc _ HSW)].
      intros a Ha. apply (R_bcmp NZh FRT B19 H6). rewrite UF, U6, U6' in Ha. exact Ha.
    - exact HB1m.
    - exact HB2m.
    - exact HB3m.
    - exact HB4m.
    - exact HB5m.
    - exact RBY.
    (* the image range of bcmp_wrap_c.v (its own IMG_LO / IMG_HI) is this file's, written under other names *)
    - apply (rng_sub' RNG IMG_LO (IMG_HI - IMG_LO));
        [exact RIMG | cbv [IMG_LO IMG_HI bcmp_wrap_c.IMG_LO bcmp_wrap_c.IMG_HI]; lia].
    - rewrite U3. unfold BCMP_WRAP_K. apply (rng_sub' RNG (S - 4656) 4656); [exact RSTK | lia].
    - rewrite UF, U6'. apply (rng_sub' RNG f 72); [exact RGf | lia].
    - rewrite UF, U6'. right. unfold shadow_addr. rewrite <- Hoff. rewrite !(Z.mul_comm 8).
      exact (shw_sub RNG off f 72 f 6 ltac:(lia) ltac:(lia) ltac:(lia) RGfs).
    - rewrite U6, U6'. apply (rng_sub' RNG fr 50); [exact RGr | lia].
    - rewrite U6, U6'. right. unfold shadow_addr. rewrite <- Hoff. rewrite !(Z.mul_comm 8).
      exact (shw_sub RNG off fr 50 (fr + 6) 6 ltac:(lia) ltac:(lia) ltac:(lia) RGrs). }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                  & E & MU2 & WM2 & MI2 & ST2 & AC2 & SR2 & BL2 & BR2).
  subst ms'. rewrite U3 in MU2, ST2. clear BL2 BR2.
  replace (ret_pc (Z_to_bv 64 0x85218)) with (Z_to_bv 64 0x85218)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (SUB1 : sub_fp [(S + -96 - 4560, S + -96)] [(f, f + 72); (S - 4656, S)])
    by (intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (_ & H2 & _); split; [lia | exact I]).
  pose proof (munch_trans [(f, f + 72); (S - 4656, S)] mE m m2 MU (munch_weaken _ _ m m2 SUB1 MU2)) as MU3.
  pose proof (wmono_trans rsegs mE m m2 WM WM2) as WM3.
  pose proof (bytes_at_transport rsegs [(S + -96 - 4560, S + -96)] m m2 f st HSb MU2
    ltac:(cbn [disjoint_from]; rewrite Hst; repeat split; try exact I; lia)) as HSb2.
  pose proof (wr_at_transport rsegs m m2 f (Z.of_nat 72) HSw WM2) as HSw2.
  pose proof (bytes_at_transport rsegs [(S + -96 - 4560, S + -96)] m m2 fr g HG MU2
    ltac:(cbn [disjoint_from]; rewrite Hg; repeat split; try exact I; lia)) as HG2.
  pose proof (rw_cells_transport rsegs [(S + -96 - 4560, S + -96)] m m2 (S + -96) FRc FR MU2 WM2
    ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia)) as FR2.
  assert (RW2 : rw_cells rsegs m2 f [CB 72 st])
    by (rewrite <- Hst; apply fa_rw_of; [exact HSb2 | rewrite Hst; exact HSw2]).
  step.
  rewrite (rf_eqb_s v) by lia.
  destruct (Z.eqb_spec v 0) as [V0|V0]; cbn [negb]; cbv iota.
  2:{ eapply (L_drop FgDrop); [ | reflexivity | exact DfS | exact FR2 | exact ST2 | exact MU3 | exact WM3
        | exact MI2 | exact RW2 ].
      rewrite HCL0. destruct (fg_keep st g) eqn:EK; [|reflexivity]. exfalso.
      apply keep_iff in EK. destruct EK as (_ & ES & _). apply V0, Iv. exact (proj1 (rf_src_eq st g) ES). }
  pose proof (fl_addressable [(f, f + 72); (S - 4656, S)] mE m2 f 72 Af MU3 (fa_sowf NZh)) as ADfm2.
  pose proof (rd_byte rsegs m2 f st 7 HSb2 ltac:(lia)) as R7.
  step.
  chk1 (f + 7) (Z_to_bv 5 12) (fa_rd1 m2 [(f, f + 72); (S - 4656, S)] f 72 7 (f + 7) SRf ADf MU3 ltac:(fa_sub)
    ltac:(lia) eq_refl).
  step. clear R7. step. step. step.
  rewrite (firstn1_skipn _ (Z_to_bv 8 0) st 7 ltac:(lia)).
  rewrite zext_extract_byte.
  rewrite ?rf_zxb_u.
  change (bv_unsigned (nth 7 st (Z_to_bv 8 0))) with (fg_lf st).
  change (bv_unsigned (nth 26 g (Z_to_bv 8 0))) with (fg_n g).
  rewrite (fa_ltu (fg_lf st + fg_n g) 65) by lia.
  change (fg_lf st + fg_n g) with (fg_T st g).
  destruct (Z.ltb_spec (fg_T st g) 65) as [T65|T65]; cbv iota.
  - eapply L_join; [ | exact (conj Hn1 Hn2) | lia | exact DJAh | exact DJBh | exact OUTh | exact Hf0 | exact FR2
      | exact ST2 | exact MU3 | exact WM3 | exact MI2 | exact HSb2 | rewrite Hst; exact HSw2 | exact HG2 ].
    rewrite HCL0. replace (fg_keep st g) with true; [reflexivity|]. symmetry. apply keep_iff.
    split; [exact H6|]. split; [exact (proj2 (rf_src_eq st g) (proj1 Iv V0)) | lia].
  - eapply (L_drop FgDrop); [ | reflexivity | exact DfS | exact FR2 | exact ST2 | exact MU3 | exact WM3
      | exact MI2 | exact RW2 ].
    rewrite HCL0. destruct (fg_keep st g) eqn:EK; [|reflexivity]. exfalso.
    apply keep_iff in EK. destruct EK as (_ & _ & ET). lia.
Qed.

Ltac rfail := eapply (L_epi FgRefuse);
  [ symmetry; apply rf_class_refuse; tauto | reflexivity | eassumption | eassumption
  | match goal with H : munch _ mE _ |- _ => exact H end | eassumption | eassumption | exact I ].

Ltac nfail := eapply L_none;
  [ eassumption
  | let EF := fresh "EF" in destruct (fg_fr len g) eqn:EF; [exfalso; apply fr_iff in EF; lia | reflexivity]
  | eassumption | eassumption | match goal with H : munch _ mE _ |- _ => exact H end | eassumption | eassumption ].

(* +0x0 .. +0x74: prologue (save registers), the five null checks, the len >= 50 check, load the shadow base. *)
Lemma L_top : forall (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
  stk rsegs mE (S - 4656) S -> mem_inv rsegs mE ->
  (NZ -> 50 <= len -> bytes_at rsegs mE fr g) ->
  (NZ -> rw_cells rsegs mE f [CB 72 st] /\ OUT /\ DJA /\ DJB) ->
  evtF rsegs RNG Qf
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 fr) (Z_to_bv 64 len)
             (Z_to_bv 64 pa) (Z_to_bv 64 pp) (Z_to_bv 64 pn) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ff (Z_to_bv 64 0x84f68) fc None mE (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a6 a7 t3 t4 t5 t6 ST MI HF HO.
  apply hide_i in HB1. apply hide_i in HB2. apply hide_i in HB3. apply hide_i in HB4. apply hide_i in HB5.
  pose proof (munch_refl [(S - 4656, S)] mE) as MU.
  pose proof (wmono_refl rsegs mE) as WM.
  carve_frame 96%nat ST.
  do 14 step.
  step. step. rewrite (fa_beq f 0) by lia. destruct (Z.eqb_spec f 0) as [Z0|Z0]; cbv iota; [rfail|].
  step. step. rewrite (fa_beq fr 0) by lia. destruct (Z.eqb_spec fr 0) as [Z1|Z1]; cbv iota; [rfail|].
  step. step. rewrite (fa_beq pa 0) by lia. destruct (Z.eqb_spec pa 0) as [Z2|Z2]; cbv iota; [rfail|].
  step. step. rewrite (fa_beq pp 0) by lia. destruct (Z.eqb_spec pp 0) as [Z3|Z3]; cbv iota; [rfail|].
  step. step. rewrite (fa_beq pn 0) by lia. destruct (Z.eqb_spec pn 0) as [Z4|Z4]; cbv iota; [rfail|].
  assert (NZh : NZ) by (unfold NZ; tauto).
  destruct (HO NZh) as (HS0 & OUTh & DJAh & DJBh).
  step. step. rewrite (fa_ltu len 50) by lia.
  destruct (Z.ltb_spec len 50) as [L50|L50]; cbv iota; [nfail|].
  pose proof (HF NZh L50) as HGE.
  rngf NZh. rngg NZh L50.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (asan_rt_munch rsegs mE m1 GOT_CELL_K CELL_K off [(S - 4656, S)] [(S - 4656, S)] HRT MU
                ltac:(intros x Hx; exact Hx)) as HRT1.
  pose proof (asan_rt_got_read rsegs m1 GOT_CELL_K CELL_K off [(S - 4656, S)] HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 GOT_CELL_K CELL_K off [(S - 4656, S)] HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  (* the unfolded copy of the image range, for the two 8-byte loads at the literal addresses of those cells *)
  pose proof RIMG as RIMGu. unfold IMG_LO, IMG_HI in RIMGu.
  do 3 step. clear RG RC HRT1.
  pose proof (bytes_at_transport rsegs [(S - 4656, S)] mE m1 fr g HGE MU
    ltac:(cbn [disjoint_from]; rewrite Hg; destruct DJAh as (_ & _ & DrS); repeat split; try exact I; lia)) as HGm.
  pose proof (rw_cells_transport rsegs [(S - 4656, S)] mE m1 f [CB 72 st] HS0 MU WM
    ltac:(cbn [disjoint_from cells_size csize Nat.add]; destruct DJAh as (_ & DfS & _); repeat split; try exact I; lia)) as HSm.
  destruct (HAG NZh L50) as (Ag & SRg & ADg).
  pose proof (bytes_at_bound rsegs m1 fr g HGm) as BG. rewrite Hg in BG.
  (* g[16] = 205 *)
  step. chk1 (fr + 16) (Z_to_bv 5 12) (fa_rd1 m1 [(S - 4656, S)] fr 50 16 (fr + 16) SRg ADg MU ltac:(fa_sub) ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m1 fr g 16 HGm ltac:(rewrite Hg; lia)) as RG. step. clear RG. step. step.
  rewrite (rf_beq (nth 16 g (Z_to_bv 8 0)) 205) by lia.
  change (bv_unsigned (nth 16 g (Z_to_bv 8 0))) with (bat g 16).
  destruct (Z.eqb_spec (bat g 16) 205) as [B16|B16]; cbn [negb]; cbv iota; [|nfail].
  (* g[17] = 234 *)
  step. chk1 (fr + 17) (Z_to_bv 5 12) (fa_rd1 m1 [(S - 4656, S)] fr 50 17 (fr + 17) SRg ADg MU ltac:(fa_sub) ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m1 fr g 17 HGm ltac:(rewrite Hg; lia)) as RG. step. clear RG. step. step.
  rewrite (rf_beq (nth 17 g (Z_to_bv 8 0)) 234) by lia.
  change (bv_unsigned (nth 17 g (Z_to_bv 8 0))) with (bat g 17).
  destruct (Z.eqb_spec (bat g 17) 234) as [B17|B17]; cbn [negb]; cbv iota; [|nfail].
  (* g[18] = 4 *)
  step. chk1 (fr + 18) (Z_to_bv 5 12) (fa_rd1 m1 [(S - 4656, S)] fr 50 18 (fr + 18) SRg ADg MU ltac:(fa_sub) ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m1 fr g 18 HGm ltac:(rewrite Hg; lia)) as RG. step. clear RG. step. step.
  rewrite (rf_beq (nth 18 g (Z_to_bv 8 0)) 4) by lia.
  change (bv_unsigned (nth 18 g (Z_to_bv 8 0))) with (bat g 18).
  destruct (Z.eqb_spec (bat g 18) 4) as [B18|B18]; cbn [negb]; cbv iota; [|nfail].
  (* g[19] in {1,2} *)
  step. chk1 (fr + 19) (Z_to_bv 5 13) (fa_rd1 m1 [(S - 4656, S)] fr 50 19 (fr + 19) SRg ADg MU ltac:(fa_sub) ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m1 fr g 19 HGm ltac:(rewrite Hg; lia)) as RG. step. clear RG. step. step. step.
  rewrite rf_b1. change (bv_unsigned (nth 19 g (Z_to_bv 8 0))) with (bat g 19).
  destruct ((bat g 19 =? 1) || (bat g 19 =? 2)) eqn:E19; cbn [negb]; cbv iota.
  2:{ apply orb_false_iff in E19. destruct E19 as [E19a E19b]. apply Z.eqb_neq in E19a, E19b. nfail. }
  apply orb_true_iff in E19. rewrite !Z.eqb_eq in E19.
  (* g[22] = 0 *)
  step. chk1 (fr + 22) (Z_to_bv 5 14) (fa_rd1 m1 [(S - 4656, S)] fr 50 22 (fr + 22) SRg ADg MU ltac:(fa_sub) ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m1 fr g 22 HGm ltac:(rewrite Hg; lia)) as RG. step. clear RG. step.
  rewrite (rf_beq (nth 22 g (Z_to_bv 8 0)) 0) by lia.
  change (bv_unsigned (nth 22 g (Z_to_bv 8 0))) with (bat g 22).
  destruct (Z.eqb_spec (bat g 22) 0) as [B22|B22]; cbn [negb]; cbv iota; [|nfail].
  (* g[23] = 2 *)
  step. chk1 (fr + 23) (Z_to_bv 5 14) (fa_rd1 m1 [(S - 4656, S)] fr 50 23 (fr + 23) SRg ADg MU ltac:(fa_sub) ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m1 fr g 23 HGm ltac:(rewrite Hg; lia)) as RG. step. clear RG. step. step.
  rewrite (rf_beq (nth 23 g (Z_to_bv 8 0)) 2) by lia.
  change (bv_unsigned (nth 23 g (Z_to_bv 8 0))) with (bat g 23).
  destruct (Z.eqb_spec (bat g 23) 2) as [B23|B23]; cbn [negb]; cbv iota; [|nfail].
  (* g[24] = 0 *)
  step. chk1 (fr + 24) (Z_to_bv 5 14) (fa_rd1 m1 [(S - 4656, S)] fr 50 24 (fr + 24) SRg ADg MU ltac:(fa_sub) ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m1 fr g 24 HGm ltac:(rewrite Hg; lia)) as RG. step. clear RG. step.
  rewrite (rf_beq (nth 24 g (Z_to_bv 8 0)) 0) by lia.
  change (bv_unsigned (nth 24 g (Z_to_bv 8 0))) with (bat g 24).
  destruct (Z.eqb_spec (bat g 24) 0) as [B24|B24]; cbn [negb]; cbv iota; [|nfail].
  (* g[25] = 254 *)
  step. chk1 (fr + 25) (Z_to_bv 5 14) (fa_rd1 m1 [(S - 4656, S)] fr 50 25 (fr + 25) SRg ADg MU ltac:(fa_sub) ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m1 fr g 25 HGm ltac:(rewrite Hg; lia)) as RG. step. clear RG. step. step.
  rewrite (rf_beq (nth 25 g (Z_to_bv 8 0)) 254) by lia.
  change (bv_unsigned (nth 25 g (Z_to_bv 8 0))) with (bat g 25).
  destruct (Z.eqb_spec (bat g 25) 254) as [B25|B25]; cbn [negb]; cbv iota; [|nfail].
  (* g[26] = n, 1 <= n <= 22 *)
  step. chk1 (fr + 26) (Z_to_bv 5 14) (fa_rd1 m1 [(S - 4656, S)] fr 50 26 (fr + 26) SRg ADg MU ltac:(fa_sub) ltac:(lia) eq_refl).
  pose proof (rd_byte rsegs m1 fr g 26 HGm ltac:(rewrite Hg; lia)) as RG. step. clear RG. step. step. step.
  rewrite rf_n. change (bv_unsigned (nth 26 g (Z_to_bv 8 0))) with (fg_n g).
  destruct ((1 <=? fg_n g) && (fg_n g <=? 22)) eqn:EN; cbn [negb]; cbv iota.
  2:{ apply andb_false_iff in EN. destruct EN as [EN|EN]; apply Z.leb_gt in EN; nfail. }
  apply andb_true_iff in EN. destruct EN as [EN1 EN2]. apply Z.leb_le in EN1, EN2.
  (* block-sum loop over fr + 18 .. fr + 50, each byte shadow-checked *)
  pose proof (asan_shadow_rd_munch rsegs mE m1 off fr 50 W5 [(S - 4656, S)] SRg MU ltac:(fa_sub)) as SRg1.
  pose proof (asan_addressable_munch rsegs mE m1 off fr 50 W5 [(S - 4656, S)] ADg SRg MU ltac:(fa_sub)) as ADg1.
  pose proof (fa_sr_sub m1 off fr 50 18 32 W5 SRg1 ltac:(lia) ltac:(lia) ltac:(lia)) as SRb.
  pose proof (fa_ad_sub m1 off fr 50 18 32 ADg1 ltac:(lia) ltac:(lia) ltac:(lia)) as ADb.
  pose proof (rf_bytes_skip rsegs m1 fr g 18 HGm ltac:(rewrite Hg; lia)) as HBk.
  change (Z.to_nat 18) with 18%nat in HBk.
  do 3 step.
  eapply (loopB Qf) with (A := fr + 18) (bs := skipn 18 g) (c := 32%nat) (W := W5) (n := 32%nat) (i := 0%nat);
    [ exact HBk | rewrite length_skipn, Hg; lia | lia | lia | exact SRb | exact ADb
    | apply (rng_sub' RNG fr 50); [exact RGr | lia]
    | exact (shw_bytes RNG off fr 50 (fr + 18) (Z.of_nat 32) ltac:(lia) ltac:(lia) ltac:(lia) RGrs)
    | | lia | lia | first [f_equal; lia | word_eq_tac] | first [f_equal; lia | word_eq_tac]
    | rewrite unsigned_lit by lia; reflexivity ].
  intros y4 y5 y6.
  remember (psum (skipn 18 g) 32) as ps eqn:Eps.
  assert (PB : 0 <= ps <= 255 * 32) by (rewrite Eps; pose proof (psum_range (skipn 18 g) 32); lia).
  step. step. step.
  rewrite rf_land255 by lia.
  replace (ps mod 256) with (blocksum (skipn 18 g)) by (unfold blocksum; rewrite Eps; reflexivity).
  clear Eps.
  destruct (Z.eqb_spec (blocksum (skipn 18 g)) 0) as [BS|BS]; cbv iota; [|nfail].
  assert (FRT : fg_fr len g = true) by (apply fr_iff; repeat split; first [assumption | lia]).
  unfold hide in HB1, HB2, HB3, HB4, HB5.
  (* dispatch: g[19] = 1 -> first record, else -> second *)
  step. step.
  rewrite (rf_beq (nth 19 g (Z_to_bv 8 0)) 1) by lia.
  change (bv_unsigned (nth 19 g (Z_to_bv 8 0))) with (bat g 19).
  destruct (Z.eqb_spec (bat g 19) 1) as [G1|G1]; cbn [negb]; cbv iota.
  - eapply (L_first FgFirst); [ | reflexivity | lia | exact DJAh | exact FR | exact ST | exact MU | exact WM
      | exact MI | exact HSm | exact HGm ].
    rewrite (cl_nn NZh), FRT, (proj2 (Z.eqb_eq _ _) G1). reflexivity.
  - eapply L_second; [ exact NZh | exact FRT | exact G1 | exact DJAh | exact DJBh | exact OUTh | exact FR | exact ST
      | exact MU | exact WM | exact MI | exact HSm | exact HGm ].
Qed.

End P.

(* The form this file's run proof is written against: the narrowed statement's premises with RNG bound last and the
   guarded rng premises of a buffer conjoined (fragment_contract_F_conj of reac_ctrl_identity_fragment_F.v with the
   two route (C) changes).  reac_ctrl_identity_fragment_contract_F_on follows from it below. *)
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
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_identity_fragment_shadow_R f fr len pa pp pn st g) m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_CTRL_IDENTITY_FRAGMENT_K -> bv_unsigned sp <= APPMEM_END ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 -> 50 <= len -> addressable m fr 50) ->
    (f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
       addressable m f 72 /\ addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
       app_mem (f + 78) /\ dj_from RT_LO RT_HI [(f, f + 72); (pa, pa + 2); (pp, pp + 8); (pn, pn + 8)]) ->
    bytes_at rsegs m REAL_BCMP (le8 (wa bcmp_wrap_c.BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
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
         asan_cells m' /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_FRAGMENT) fc None m (seg_rom rsegs)).

Theorem reac_ctrl_identity_fragment_holds_F_conj_on :
  asan_memcpy_contract_F_on -> bcmp_wrap_contract_F_on -> fragment_contract_F_conj_on.
Proof.
  intros MCPY BCMP. unfold fragment_contract_F_conj_on.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m f fr len pa pp pn st g RNG Ea0 Ea1 Ea2 Ea3 Ea4 Ea5 Hf Hfr Hlen Hpa Hpp Hpn Hspmod STk Hg Hst
    HFrec HOrec MI HCE HSW Hlo Hhi HAGc HAFc HB1c HB2c HB3c HB4c HB5c RBYc RIMGc RSTKc RWSc RGGc RGFc.
  subst a0 a1 a2 a3 a4 a5.
  unfold REAC_CTRL_IDENTITY_FRAGMENT_K, REAC_CTRL_IDENTITY_FRAGMENT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  (* the window's shadow word span, in the cover form shw (at off = ASAN_K) that the run's proof names *)
  assert (RSTKSc : shw RNG ASAN_K (bv_unsigned sp - 4656) 4656)
    by (destruct RWSc as [E|H]; [discriminate E | exact H]).
  assert (Esp : sp = Z_to_bv 64 (bv_unsigned sp)) by (apply bv_eq; rewrite unsigned_lit by lia; reflexivity).
  rewrite Esp.
  eapply evtF_mono.
  - eapply (L_top MCPY BCMP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f fr len pa pp pn
                  (bv_unsigned sp) ASAN_K st g RNG);
      [ exact Hf | exact Hfr | exact Hlen | exact Hpa | exact Hpp | exact Hpn
      | split; [unfold HIGHMEM_BEG in Hlo; exact Hlo | unfold APPMEM_END in Hhi; exact Hhi]
      | exact Hg | exact Hst | exact HCE | exact HSW
      | apply rt_asan_rt; [exact HCE | intros x Hx; cbn [outside]; split; [|exact I];
          clear -Hx Hlo; unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia]
      | intros NZh; unfold NZ in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          pose proof (HAFc N1 N2 N3 N4 N5) as ASFh;
          destruct ASFh as (Af & Apa & App & Apn & Happ & Hdj);
          pose proof (fa_so5 m f pa pp pn (bv_unsigned sp - 4656) (bv_unsigned sp) Af Apa App Apn Hlo Hhi) as SO;
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
          pose proof (fa_so5 m f pa pp pn (bv_unsigned sp - 4656) (bv_unsigned sp) Af Apa App Apn Hlo Hhi) as SO;
          unfold ASG, W5; split; [exact Afr | split; [apply rt_shadow_rd; [exact Afr | exact SO]
                                                      | apply rt_addressable; exact Afr]]
      | exact HB1c | exact HB2c | exact HB3c | exact HB4c | exact HB5c
      | clear -Hlo; unfold REAL_BCMP, REAL_MEMCMP, GOT_CF, CF, HIGHMEM_BEG in *; repeat split; lia
      | reflexivity | exact RBYc | exact RIMGc | exact RSTKc | exact RSTKSc
      | intros NZh; unfold NZ in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          unfold RGF; exact (RGFc N1 N2 N3 N4 N5)
      | intros NZh L50; unfold NZ in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          unfold RGG; exact (RGGc N1 N2 N3 N4 N5 L50)
      | exact STk | exact MI
      | intros NZh L50; unfold NZ in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          exact (HFrec N1 N2 N3 N4 N5 L50)
      | intros NZh; unfold NZ in NZh; destruct NZh as (N1 & N2 & N3 & N4 & N5);
          destruct (HOrec N1 N2 N3 N4 N5) as (HS & M2 & M8 & M8' & W2 & W8 & W8' & DJ);
          cbn [all_dj dj_from] in DJ;
          split; [exact HS|]; split; [unfold OUT; clear -M2 M8 M8' W2 W8 W8'; tauto|];
          clear -DJ; unfold DJA, DJB; repeat split; try tauto; lia ].
  - intros ms' HQ. unfold Qf in HQ. rewrite !(unsigned_lit (bv_unsigned sp)) by lia. exact HQ.
Qed.

(* reac_ctrl_identity_fragment_contract_F_on (reac_ctrl_identity_fragment_c.v) from the form above: the same
   premises, with RNG bound first and one guarded rng premise per buffer and per shadow cover.  The shadow covers
   differ only in how the last byte of a buffer is written (p + n - 1 against the literal). *)
Theorem reac_ctrl_identity_fragment_F_holds_on :
  asan_memcpy_contract_F_on -> bcmp_wrap_contract_F_on -> reac_ctrl_identity_fragment_contract_F_on.
Proof.
  intros MCPY BCMP.
  pose proof (reac_ctrl_identity_fragment_holds_F_conj_on MCPY BCMP) as HC.
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

(* The narrowed plain statement from the narrowed footprint one (reac_ctrl_identity_fragment_contract_of_F_on). *)
Theorem reac_ctrl_identity_fragment_holds_of_F_on :
  asan_memcpy_contract_F_on -> bcmp_wrap_contract_F_on -> reac_ctrl_identity_fragment_contract_on.
Proof.
  intros MCPY BCMP.
  exact (reac_ctrl_identity_fragment_contract_of_F_on (reac_ctrl_identity_fragment_F_holds_on MCPY BCMP)).
Qed.

(* With no hypothesis left: the narrowed footprint statement of this function at the two narrowed callee contracts
   their owners prove for this image -- a Theorem Labs lane's asan_memcpy_holds_F_on (lib/A/Prog/asan_memcpyF_on.v) and
   a Theorem Labs lane's bcmp_wrap_holds_F_on (lib/A/Prog/bcmp_wrap_on.v). *)
Corollary reac_ctrl_identity_fragment_F_holds_on_closed : reac_ctrl_identity_fragment_contract_F_on.
Proof.
  exact (reac_ctrl_identity_fragment_F_holds_on
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_on.bcmp_wrap_holds_F_on).
Qed.

(* The same, for the narrowed plain statement. *)
Corollary reac_ctrl_identity_fragment_holds_on_closed : reac_ctrl_identity_fragment_contract_on.
Proof. exact (reac_ctrl_identity_fragment_contract_of_F_on reac_ctrl_identity_fragment_F_holds_on_closed). Qed.
