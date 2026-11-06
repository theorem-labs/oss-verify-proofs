(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Rep ECH_LibState ECH_LibStateMF ECH_LibFrame ECH_Kit ECH_C1_stmt ECH_C2_stmt ECH_C3_stmt ECH_C4_stmt ECH_C4_frame ECH_C11_stmt ECH_C14_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import InitMem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ERRW : list (Z * Z) :=
  [ (A_err_string_once, A_defctx_inited); (A_tevent_once, A_tevent_once + 16);
    (A_stopped, A_stopped + 4); (A_base_once, A_base_once + 8);
    (A_load_strings_once, A_load_strings_once + 8); (A_optsdone, A_optsdone + 8);
    (A_td_tsd_used, A_td_tsd_used + 1); (A_td_cancelbuf, A_td_cancelbuf + 8);
    (A_keys + 24, A_keys + 32); (A_next_key, A_key_lock + 16);
    (A_tsd_main + 8, A_tsd_main + 16); (A_tsd_main + 24, A_tsd_main + 32) ].
(* [comment removed for export] *)
Definition ERRW_core : list (Z * Z) :=
  [ (A_err_string_once, A_defctx_inited); (A_tevent_once, A_tevent_once + 16);
    (A_load_strings_once, A_load_strings_once + 8); (A_optsdone, A_optsdone + 8);
    (A_td_tsd_used, A_td_tsd_used + 1); (A_keys + 24, A_keys + 32); (A_key_lock + 8, A_key_lock + 16);
    (A_tsd_main + 8, A_tsd_main + 16); (A_tsd_main + 24, A_tsd_main + 32) ].
(* [comment removed for export] *)
Definition MIDW_misc : list (Z * Z) :=
  [ (A_malloc_impl, A_malloc_impl + 24); (A_vdso_func, A_vdso_func + 8); (A_global_cleanup, A_global_cleanup + 1) ].
Definition relro_addr (a : Z) : Prop := RELRO_LO <= a < RELRO_HI /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8).

(* [comment removed for export] *)
Definition relro_grp (m : mem) : Prop :=
  GOT_mem m /\ GOT_echfree m /\ GOT_x509vpm m /\ METH_mem m /\ METH_b64 m /\ HPKE_tabs m /\ relro_lib m.

Local Ltac addrs := unfold A_err_string_once, A_master_once_ret, A_defctx_inited, A_tevent_once, A_stopped, A_base_once, A_base_inited, A_in_init_config_key,
  A_load_strings_once, A_optsdone, A_optsdone_lock, A_td_tsd_used, A_td_cancelbuf, A_td_tsd, A_keys, A_next_key, A_key_lock, A_tsd_main, A_destructor_key,
  A_defctx_exlock, A_defctx_exmeth_bio, A_malloc_impl, A_vdso_func, A_global_cleanup, A_mem_inited,
  A_got_CRYPTO_malloc, A_got_ossl_echext_free, A_got_ASN1_OBJECT_free, A_mem_buf_method, A_b64_method, O_METH_BREAD,
  A_hpke_kem_tab, A_hpke_kdf_tab, A_hpke_aead_tab, HPKE_KEM_ROW, HPKE_KDF_ROW, HPKE_AEAD_ROW,
  RELRO_LO, RELRO_HI, RGOT_SSP, IMG_LO, IMG_HI in *.
(* [comment removed for export] *)
Local Ltac in_ivs_tac W a :=
  apply (proj1 (in_ivs_b_spec W a)); unfold W; unfold LIBX0; addrs; cbn [in_ivs_b fst snd Z.add];
  repeat (rewrite Bool.orb_true_iff; first [left; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia | right]).
Local Ltac cellr Ha := unfold in_range in Ha; cbn [cells_size csize length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Pos.add map] in Ha.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma IMPL_agreeR : forall (R : Z -> Prop) m m', IMPL_mem m -> magree R m m' -> (forall a, A_malloc_impl <= a < A_malloc_impl + 24 -> R a) -> IMPL_mem m'.
Proof. intros R m m' I AG HR. unfold IMPL_mem in *. eapply rw_cells_agree; [exact AG| exact I|]. intros a Ha. apply HR. cellr Ha. lia. Qed.

Lemma MEMFLAG_agreeR : forall (R : Z -> Prop) m m' v, MEMFLAG m v -> magree R m m' -> R A_mem_inited -> MEMFLAG m' v.
Proof.
  intros R m m' v (fb & C & V & V01) AG HR. exists fb. split; [| split; assumption].
  eapply rw_cells_agree; [exact AG| exact C|]. intros a Ha. cellr Ha. replace a with A_mem_inited by lia. exact HR.
Qed.

Lemma VDSO_agreeR : forall (R : Z -> Prop) m m' (v : bool),
  rw_cells usegs m A_vdso_func [C8 (wz (if v then 0 else P_cgt_init))] -> magree R m m' ->
  (forall a, A_vdso_func <= a < A_vdso_func + 8 -> R a) -> rw_cells usegs m' A_vdso_func [C8 (wz (if v then 0 else P_cgt_init))].
Proof. intros R m m' v C AG HR. eapply rw_cells_agree; [exact AG| exact C|]. intros a Ha. apply HR. cellr Ha. lia. Qed.

Lemma CLEAN_agreeR : forall (R : Z -> Prop) m m', m (wa A_global_cleanup) = None -> magree R m m' -> R A_global_cleanup -> m' (wa A_global_cleanup) = None.
Proof. intros R m m' C AG HR. eapply none_agree; [exact AG| unfold A_global_cleanup; lia| exact HR| exact C]. Qed.

Lemma id_rows_agreeR : forall (R : Z -> Prop) m m' a stride ids,
  id_rows m a stride ids -> magree R m m' -> 2 <= stride -> (forall x, a <= x < a + stride * Z.of_nat (length ids) -> R x) -> id_rows m' a stride ids.
Proof.
  intros R m m' a stride ids. revert a. induction ids as [|i ids IH]; intros a H AG ST HR; [exact I|].
  cbn [id_rows] in *. destruct H as [C T]. cbn [length] in HR. split.
  - eapply rw_cells_agree; [exact AG| exact C|]. intros x Hx. apply HR. cellr Hx. lia.
  - apply IH; [exact T| exact AG| exact ST|]. intros x Hx. apply HR. lia.
Qed.

Lemma relro_grp_agreeR : forall (R : Z -> Prop) m m', relro_grp m -> magree R m m' -> (forall a, relro_addr a -> R a) -> relro_grp m'.
Proof.
  intros R m m' (G1 & G2 & G3 & M1 & M2 & (T1 & T2 & T3) & RL) AG HR.
  unfold relro_grp, GOT_mem, GOT_echfree, GOT_x509vpm, METH_mem, METH_b64, HPKE_tabs, relro_addr in *.
  assert (HR' : forall A n a, A <= a < A + n -> RELRO_LO <= A -> A + n <= RGOT_SSP \/ RGOT_SSP + 8 <= A -> A + n <= RELRO_HI -> R a)
    by (intros A n a Ha H1 H2 H3; apply HR; lia).
  repeat match goal with |- _ /\ _ => split end.
  all: try (eapply rw_cells_agree; [exact AG| eassumption|]; intros a Ha; cellr Ha; eapply HR'; [exact Ha| | |]; addrs; lia).
  - eapply id_rows_agreeR; [exact T1| exact AG| unfold HPKE_KEM_ROW; lia|]. intros a Ha. unfold HPKE_KEM_IDS, HPKE_KDF_IDS, HPKE_AEAD_IDS in Ha; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. eapply HR'; [exact Ha| | |]; addrs; lia.
  - eapply id_rows_agreeR; [exact T2| exact AG| unfold HPKE_KDF_ROW; lia|]. intros a Ha. unfold HPKE_KEM_IDS, HPKE_KDF_IDS, HPKE_AEAD_IDS in Ha; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. eapply HR'; [exact Ha| | |]; addrs; lia.
  - eapply id_rows_agreeR; [exact T3| exact AG| unfold HPKE_AEAD_ROW; lia|]. intros a Ha. unfold HPKE_KEM_IDS, HPKE_KDF_IDS, HPKE_AEAD_IDS in Ha; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. eapply HR'; [exact Ha| | |]; addrs; lia.
  - intros a Ha Hn. eapply none_agree; [exact AG| addrs; lia| apply HR; split; assumption| apply RL; assumption].
Qed.

(* [comment removed for export] *)
Lemma ERR_fresh_core_agreeR : forall (R : Z -> Prop) m m',
  ERR_fresh_core m -> magree R m m' -> (forall a, rin_ivs ERRW_core a -> R a) -> ERR_fresh_core m'.
Proof.
  intros R m m' E AG HR. unfold ERR_fresh_core in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    (eapply none_on_agree; [exact AG| eassumption| intros a Ha; apply HR; unfold in_range in Ha; in_ivs_tac ERRW_core a| addrs; lia| addrs; lia]).
Qed.

Lemma CTX_keys_agreeW : forall (R : Z -> Prop) m m', CTX_keys m -> magree R m m' -> (forall a, rin_ivs ERRW a -> R a) -> CTX_keys m'.
Proof.
  intros R m m' K AG HR. eapply CTX_keys_agree; [exact K| exact AG|]. intros a Ha. apply HR.
  destruct Ha as [Ha|[Ha|Ha]]; in_ivs_tac ERRW a.
Qed.

Lemma ERR_statics_agreeR : forall (R : Z -> Prop) m m' c,
  ERR_statics m c -> magree R m m' -> (forall a, rin_ivs ERRW a -> R a) -> ERR_statics m' c.
Proof.
  intros R m m' c E AG HR. unfold ERR_statics in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    (eapply rw_cells_agree; [exact AG| eassumption| intros a Ha; apply HR; cellr Ha; in_ivs_tac ERRW a]).
Qed.

(* [comment removed for export] *)
Definition chain_cell (c : errchain) (a : Z) : Prop :=
     blk_addr (ec_mkey c) <= a < blk_addr (ec_mkey c) + 72
  \/ blk_addr (ec_sa c) <= a < blk_addr (ec_sa c) + 32
  \/ blk_addr (ec_nodes c) <= a < blk_addr (ec_nodes c) + 128
  \/ blk_addr (ec_es c) <= a < blk_addr (ec_es c) + ERRST_SIZE.
Lemma chain_cell_block : forall LIB m c a, ERR_chain LIB m c -> chain_cell c a ->
  exists b, In b LIB /\ blk_addr b <= a < blk_addr b + blk_size b /\ rblock_range (blk_addr b) (blk_size b).
Proof.
  intros LIB m c a CH Ha. unfold ERR_chain, chain_blocks in CH.
  destruct CH as (I2 & Z2 & _ & I3 & Z3 & _ & I4 & Z4 & _ & I5 & Z5 & I6 & Z6 & RR).
  pose proof (Forall_inv RR) as R2. pose proof (Forall_inv (Forall_inv_tail RR)) as R3.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RR))) as R4. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RR)))) as R5.
  cbn beta in R2, R3, R4, R5. rewrite Z2 in R2. rewrite Z3 in R3. rewrite Z4 in R4. rewrite Z5 in R5.
  destruct Ha as [Ha|[Ha|[Ha|Ha]]].
  - exists (ec_mkey c). rewrite Z2. exact (conj I2 (conj Ha R2)).
  - exists (ec_sa c). rewrite Z3. exact (conj I3 (conj Ha R3)).
  - exists (ec_nodes c). rewrite Z4. exact (conj I4 (conj Ha R4)).
  - exists (ec_es c). rewrite Z5. exact (conj I5 (conj Ha R5)).
Qed.

Lemma ERR_chain_agreeR : forall (R : Z -> Prop) LIB m m' c,
  ERR_chain LIB m c -> magree R m m' -> (forall a, chain_cell c a -> R a) -> ERR_chain LIB m' c.
Proof.
  intros R LIB m m' c CH AG HR. pose proof CH as CH0. unfold ERR_chain, sa_cells in *.
  destruct CH as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
  repeat match goal with |- _ /\ _ => split end; try assumption.
  - eapply rw_cells_agree; [exact AG| exact K2|]. intros a Ha. apply HR. cellr Ha. unfold chain_cell, O_MKEY_ERR in *. lia.
  - eapply rw_cells_agree; [exact AG| exact K3|]. intros a Ha. apply HR. cellr Ha. unfold chain_cell in *. lia.
  - eapply rw_cells_agree; [exact AG| exact K4|]. intros a Ha. apply HR. cellr Ha. unfold chain_cell in *. lia.
Qed.

Lemma ERRX_agreeR : forall (R : Z -> Prop) m m' c E,
  ERRX m (ErrReady c) E -> magree R m m' -> (forall a, chain_cell c a -> R a) -> ERRX m' (ErrReady c) E.
Proof.
  intros R m m' c E EX AG HR. cbn [ERRX] in *. eapply ERRST_agree; [exact AG| exact EX|].
  intros a Ha. apply HR. unfold in_range, chain_cell in *. lia.
Qed.

(* [comment removed for export] *)
Lemma ERRmid_agreeR : forall (R : Z -> Prop) LB m m' cph eph E,
  ERRPH_mid LB m cph eph -> ERRX m eph E -> magree R m m' ->
  (forall a, rin_ivs ERRW_core a -> R a) ->
  (cph <> CtxFresh -> forall a, rin_ivs ERRW a -> R a) ->
  (forall c a, eph = ErrReady c -> chain_cell c a -> R a) ->
  ERRPH_mid LB m' cph eph /\ ERRX m' eph E.
Proof.
  intros R LB m m' cph eph E PM EX AG HC HW HB.
  destruct cph as [|x], eph as [|c]; cbn [ERRPH_mid ERRPH ERRX] in *.
  - split; [eapply ERR_fresh_core_agreeR; eassumption| exact EX].
  - destruct PM.
  - destruct PM as [CO KE]. split; [| exact EX]. split; [eapply ERR_fresh_core_agreeR; eassumption|].
    eapply CTX_keys_agreeW; [exact KE| exact AG| apply HW; discriminate].
  - destruct PM as [ES CH]. split; [split|].
    + eapply ERR_statics_agreeR; [exact ES| exact AG| apply HW; discriminate].
    + eapply ERR_chain_agreeR; [exact CH| exact AG| intros a Ha; eapply HB; [reflexivity| exact Ha]].
    + eapply ERRST_agree; [exact AG| exact EX|]. intros a Ha. eapply HB; [reflexivity|]. unfold in_range, chain_cell in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition midR (LB : list block) (X : list (Z * Z)) (a : Z) : Prop := c4_addr LB a /\ ~ rin_ivs X a.

Lemma magree_mid_of_xpres : forall LB Lall SP X m m',
  xpres Lall SP X m m' -> (forall b, In b LB -> In b Lall) -> magree (midR LB X) m m'.
Proof.
  intros LB Lall SP X m m' XP SUB a Ha [HC HX]. apply XP; [exact Ha|]. split; [| exact HX].
  destruct HC as [[HL|(b & Hb & Hr)]|HR].
  - apply c4_static_client. left. exact HL.
  - right; right. exists b. split; [apply SUB; exact Hb| exact Hr].
  - apply c4_static_client. right. exact HR.
Qed.

(* [comment removed for export] *)
Lemma ERRW_core_libx : forall a, rin_ivs ERRW_core a -> rin_ivs LIBX a.
Proof. intros a Ha. unfold ERRW_core in Ha. cbn [rin_ivs fst snd] in Ha. addrs. intuition (in_ivs_tac LIBX a). Qed.
Lemma ERRW_libx : forall a, rin_ivs ERRW a -> rin_ivs LIBX a.
Proof. intros a Ha. unfold ERRW in Ha. cbn [rin_ivs fst snd] in Ha. addrs. intuition (in_ivs_tac LIBX a). Qed.
Lemma MIDW_misc_libx : forall a, rin_ivs MIDW_misc a -> rin_ivs LIBX a.
Proof. intros a Ha. unfold MIDW_misc in Ha. cbn [rin_ivs fst snd] in Ha. addrs. intuition (in_ivs_tac LIBX a). Qed.

(* [comment removed for export] *)
Lemma block_cell_off_image : forall b a, rblock_range (blk_addr b) (blk_size b) -> blk_addr b <= a < blk_addr b + blk_size b ->
  a < IMG_LO \/ IMG_HI <= a.
Proof. intros b a (B1 & B2 & B3 & B4 & B5) Ha. unfold IMG_LO, IMG_HI. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma EXLOCK_relist : forall L L' m b, EXLOCK L m b -> In b L' -> EXLOCK L' m b.
Proof. intros L L' m b (I1 & Z1 & R1 & M1) HI. exact (conj HI (conj Z1 (conj R1 M1))). Qed.
Lemma CTXPH_mono : forall L L' m ph, CTXPH L m ph -> (forall b, In b L -> In b L') -> CTXPH L' m ph.
Proof.
  intros L L' m [|x] C SUB; cbn [CTXPH] in *; [exact C|]. destruct C as [CS [EX (po & pi & O1 & O2)]].
  split; [exact CS|]. split; [eapply EXLOCK_relist; [exact EX| apply SUB; exact (proj1 EX)]| exists po, pi; split; apply SUB; assumption].
Qed.
Lemma ERR_chain_relist : forall L L' m c, ERR_chain L m c -> Forall (fun b => In b L') (chain_blocks c) -> ERR_chain L' m c.
Proof.
  intros L L' m c CH HF. unfold ERR_chain, chain_blocks in *.
  destruct CH as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
  pose proof (Forall_inv HF) as J2. pose proof (Forall_inv (Forall_inv_tail HF)) as J3.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF))) as J4.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF)))) as J5.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF))))) as J6.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
Lemma ERR_chain_mono : forall L L' m c, ERR_chain L m c -> (forall b, In b L -> In b L') -> ERR_chain L' m c.
Proof.
  intros L L' m c CH SUB. eapply ERR_chain_relist; [exact CH|]. unfold chain_blocks.
  destruct CH as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
  repeat (apply Forall_cons; [apply SUB; assumption|]). apply Forall_nil.
Qed.
Lemma ERRPH_mid_mono : forall L L' m cph eph, ERRPH_mid L m cph eph -> (forall b, In b L -> In b L') -> ERRPH_mid L' m cph eph.
Proof.
  intros L L' m [|x] [|c] P SUB; cbn [ERRPH_mid ERRPH] in *; try exact P.
  destruct P as [ES CH]. split; [exact ES| eapply ERR_chain_mono; eassumption].
Qed.
Lemma LIBMID_mono : forall L L' m M, LIBMID L m M -> (forall b, In b L -> In b L') -> LIBMID L' m M.
Proof.
  intros L L' m M LM SUB. destruct LM as (IM & MF & CP & EP & EX & REST).
  split; [exact IM|]. split; [exact MF|]. split; [eapply CTXPH_mono; eassumption|]. split; [eapply ERRPH_mid_mono; eassumption|].
  split; [exact EX| exact REST].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ERRPH_mid_chain : forall LIB m cph c, ERRPH_mid LIB m cph (ErrReady c) -> ERR_chain LIB m c.
Proof. intros LIB m [|x] c P; cbn [ERRPH_mid ERRPH] in P; [destruct P| exact (proj2 P)]. Qed.

(* [comment removed for export] *)
Lemma LIBMID_agree_mf : forall LIB m m' M f',
  LIBMID LIB m M -> magree (fun a => c4_addr LIB a /\ ~ (A_mem_inited <= a < A_mem_inited + 1)) m m' -> MEMFLAG m' f' ->
  LIBMID LIB m' (mkMID f' (mid_ctx M) (mid_err M) (mid_E M) (mid_vdso M)).
Proof.
  intros LIB m m' M f' LM AG MF'.
  destruct LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL).
  assert (STAT : forall a, rin_ivs LIBX a -> ~ (A_mem_inited <= a < A_mem_inited + 1) -> c4_addr LIB a /\ ~ (A_mem_inited <= a < A_mem_inited + 1))
    by (intros a Ha Hn; split; [left; left; exact Ha| exact Hn]).
  assert (BLK : forall b a, In b LIB -> rblock_range (blk_addr b) (blk_size b) -> blk_addr b <= a < blk_addr b + blk_size b ->
                 c4_addr LIB a /\ ~ (A_mem_inited <= a < A_mem_inited + 1)).
  { intros b a Hb RB Ha. split; [left; right; exists b; split; [exact Hb| exact Ha]|].
    pose proof (block_cell_off_image b a RB Ha). addrs. lia. }
  unfold LIBMID. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso].
  split. { eapply IMPL_agreeR; [exact IM| exact AG|]. intros a Ha. apply STAT; [apply MIDW_misc_libx; in_ivs_tac MIDW_misc a| addrs; lia]. }
  split; [exact MF'|].
  split. { eapply CTXPH_frame_mf; [exact CP|]. eapply magree_mono; [exact AG|]. intros a [HL Hn]. split; [left; exact HL| exact Hn]. }
  assert (ER : ERRPH_mid LIB m' (mid_ctx M) (mid_err M) /\ ERRX m' (mid_err M) (mid_E M)).
  { eapply ERRmid_agreeR; [exact EPm| exact EX| exact AG| | |].
    - intros a Ha. apply STAT; [apply ERRW_core_libx; exact Ha|]. unfold ERRW_core in Ha. cbn [rin_ivs fst snd] in Ha. addrs. lia.
    - intros _ a Ha. apply STAT; [apply ERRW_libx; exact Ha|]. unfold ERRW in Ha. cbn [rin_ivs fst snd] in Ha. addrs. lia.
    - intros c a Hc Ha. rewrite Hc in EPm. pose proof (ERRPH_mid_chain _ _ _ _ EPm) as CH.
      destruct (chain_cell_block _ _ _ _ CH Ha) as (b & Hb & Hr & RB). eapply BLK; eassumption. }
  destruct ER as [ER1 ER2]. split; [exact ER1|]. split; [exact ER2|].
  split. { eapply VDSO_agreeR; [exact VD| exact AG|]. intros a Ha. apply STAT; [apply MIDW_misc_libx; in_ivs_tac MIDW_misc a| addrs; lia]. }
  split. { eapply CLEAN_agreeR; [exact CL| exact AG|]. apply STAT; [apply MIDW_misc_libx; in_ivs_tac MIDW_misc A_global_cleanup| addrs; lia]. }
  split; [exact FIT|].
  assert (RG : relro_grp m') by (eapply relro_grp_agreeR; [exact (conj G1 (conj G2 (conj G3 (conj M1 (conj M2 (conj HT RL))))))| exact AG|];
    intros a [Ha Hn]; split; [right; split; assumption| addrs; lia]).
  exact RG.
Qed.

(* [comment removed for export] *)
Lemma LIBMID_agree_vdso : forall LIB m m' M,
  LIBMID LIB m M -> magree (fun a => c4_addr LIB a /\ ~ (A_vdso_func <= a < A_vdso_func + 8)) m m' ->
  rw_cells usegs m' A_vdso_func [C8 (wz 0)] ->
  LIBMID LIB m' (mkMID (mid_flag M) (mid_ctx M) (mid_err M) (mid_E M) true).
Proof.
  intros LIB m m' M LM AG VD'.
  destruct LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL).
  assert (STAT : forall a, rin_ivs LIBX a -> ~ (A_vdso_func <= a < A_vdso_func + 8) -> c4_addr LIB a /\ ~ (A_vdso_func <= a < A_vdso_func + 8))
    by (intros a Ha Hn; split; [left; left; exact Ha| exact Hn]).
  assert (BLK : forall b a, In b LIB -> rblock_range (blk_addr b) (blk_size b) -> blk_addr b <= a < blk_addr b + blk_size b ->
                 c4_addr LIB a /\ ~ (A_vdso_func <= a < A_vdso_func + 8)).
  { intros b a Hb RB Ha. split; [left; right; exists b; split; [exact Hb| exact Ha]|].
    pose proof (block_cell_off_image b a RB Ha). addrs. lia. }
  unfold LIBMID. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso].
  split. { eapply IMPL_agreeR; [exact IM| exact AG|]. intros a Ha. apply STAT; [apply MIDW_misc_libx; in_ivs_tac MIDW_misc a| addrs; lia]. }
  split. { eapply MEMFLAG_agreeR; [exact MF| exact AG|]. apply STAT; [in_ivs_tac LIBX A_mem_inited| addrs; lia]. }
  split. { eapply CTXPH_frame_mv; [exact CP|]. eapply magree_mono; [exact AG|]. intros a (HL & Hm & Hv). split; [left; exact HL| exact Hv]. }
  assert (ER : ERRPH_mid LIB m' (mid_ctx M) (mid_err M) /\ ERRX m' (mid_err M) (mid_E M)).
  { eapply ERRmid_agreeR; [exact EPm| exact EX| exact AG| | |].
    - intros a Ha. apply STAT; [apply ERRW_core_libx; exact Ha|]. unfold ERRW_core in Ha. cbn [rin_ivs fst snd] in Ha. addrs. lia.
    - intros _ a Ha. apply STAT; [apply ERRW_libx; exact Ha|]. unfold ERRW in Ha. cbn [rin_ivs fst snd] in Ha. addrs. lia.
    - intros c a Hc Ha. rewrite Hc in EPm. pose proof (ERRPH_mid_chain _ _ _ _ EPm) as CH.
      destruct (chain_cell_block _ _ _ _ CH Ha) as (b & Hb & Hr & RB). eapply BLK; eassumption. }
  destruct ER as [ER1 ER2]. split; [exact ER1|]. split; [exact ER2|].
  split; [exact VD'|].
  split. { eapply CLEAN_agreeR; [exact CL| exact AG|]. apply STAT; [apply MIDW_misc_libx; in_ivs_tac MIDW_misc A_global_cleanup| addrs; lia]. }
  split; [exact FIT|].
  assert (RG : relro_grp m') by (eapply relro_grp_agreeR; [exact (conj G1 (conj G2 (conj G3 (conj M1 (conj M2 (conj HT RL))))))| exact AG|];
    intros a [Ha Hn]; split; [right; split; assumption| addrs; lia]).
  exact RG.
Qed.

Lemma LIBMID_agree : forall LIB m m' M, LIBMID LIB m M -> magree (c4_addr LIB) m m' -> LIBMID LIB m' M.
Proof.
  intros LIB m m' M LM AG. pose proof LM as (_ & MF & _).
  pose proof (LIBMID_agree_mf LIB m m' M (mid_flag M) LM ltac:(eapply magree_mono; [exact AG| intros a [Ha _]; exact Ha])
                ltac:(eapply MEMFLAG_agreeR; [exact MF| exact AG| left; left; in_ivs_tac LIBX A_mem_inited])) as K.
  destruct M; exact K.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma LIBMID_xpres0 : forall LIB Lall SP m m' M,
  LIBMID LIB m M -> xpres Lall SP [] m m' -> (forall b, In b LIB -> In b Lall) -> LIBMID LIB m' M.
Proof.
  intros LIB Lall SP m m' M LM XP SUB. eapply LIBMID_agree; [exact LM|].
  eapply magree_mono; [eapply magree_mid_of_xpres; [exact XP| exact SUB]|]. intros a Ha. split; [exact Ha| intros K; exact K].
Qed.

(* [comment removed for export] *)
Lemma LIBMID_mf : forall LIB Lall SP m m' M,
  LIBMID LIB m M -> xpres Lall SP memflag_foot m m' -> (forall b, In b LIB -> In b Lall) -> MEMFLAG m' 1 ->
  LIBMID LIB m' (mkMID 1 (mid_ctx M) (mid_err M) (mid_E M) (mid_vdso M)).
Proof.
  intros LIB Lall SP m m' M LM XP SUB MF'. eapply LIBMID_agree_mf; [exact LM| | exact MF'].
  eapply magree_mono; [eapply magree_mid_of_xpres; [exact XP| exact SUB]|].
  intros a [Ha Hn]. split; [exact Ha|]. unfold memflag_foot. cbn [rin_ivs fst snd]. lia.
Qed.

(* [comment removed for export] *)
Lemma LIBMID_stageA : forall LIB Lall Lnew LA SP m m' f E v x,
  LIBMID LIB m (mkMID f CtxFresh ErrFresh E v) ->
  xpres Lall SP (memflag_foot ++ CTX_X) m m' -> (forall b, In b LIB -> In b Lall) ->
  CTXPH Lnew m' (CtxReady x) -> ctxph_delta CtxFresh LA x -> CTX_keys m' -> MEMFLAG m' 1 ->
  LIBMID (LA ++ LIB) m' (mkMID 1 (CtxReady x) ErrFresh E v).
Proof.
  intros LIB Lall Lnew LA SP m m' f E v x LM XP SUB CP D KE MF'.
  destruct LM as (IM & MF & _ & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL). cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ERRPH_mid ERRX] in *.
  pose proof (magree_mid_of_xpres _ _ _ _ _ _ XP SUB) as AG.
  assert (STAT : forall a, rin_ivs LIBX a -> ~ (A_mem_inited <= a < A_mem_inited + 1) -> ~ rin_ivs CTX_X a -> midR LIB (memflag_foot ++ CTX_X) a).
  { intros a Ha Hn Hc. split; [left; left; exact Ha|]. intros K. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (Hc K)].
    unfold memflag_foot in K. cbn [rin_ivs fst snd] in K. lia. }
  assert (NCTX : forall a, rin_ivs ERRW_core a \/ rin_ivs MIDW_misc a \/ relro_addr a -> ~ rin_ivs CTX_X a /\ ~ (A_mem_inited <= a < A_mem_inited + 1)).
  { intros a Ha. unfold ERRW_core, MIDW_misc, relro_addr, CTX_X in *. cbn [rin_ivs fst snd] in *. addrs. lia. }
  cbn [ctxph_delta] in D. destruct D as (_ & _ & _ & XIN & (po & pi & OIN & IIN)).
  cbn [CTXPH] in CP. destruct CP as [CS EXL]. destruct EXL as [(_ & Z1 & R1 & MU1) _].
  unfold LIBMID. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ERRPH_mid ERRPH CTXPH ERRX].
  split. { eapply IMPL_agreeR; [exact IM| exact AG|]. intros a Ha.
           assert (Hm : rin_ivs MIDW_misc a) by (in_ivs_tac MIDW_misc a). destruct (NCTX a ltac:(right; left; exact Hm)) as [N1 N2].
           apply STAT; [apply MIDW_misc_libx; exact Hm| exact N2| exact N1]. }
  split; [exact MF'|].
  split. { split; [exact CS|]. split; [| exists po, pi; split; apply in_or_app; left; assumption].
           split; [apply in_or_app; left; exact XIN|]. split; [exact Z1|]. split; [exact R1| exact MU1]. }
  split. { split; [| exact KE]. eapply ERR_fresh_core_agreeR; [exact EPm| exact AG|].
           intros a Ha. destruct (NCTX a ltac:(left; exact Ha)) as [N1 N2]. apply STAT; [apply ERRW_core_libx; exact Ha| exact N2| exact N1]. }
  split; [exact EX|].
  split. { eapply VDSO_agreeR; [exact VD| exact AG|]. intros a Ha.
           assert (Hm : rin_ivs MIDW_misc a) by (in_ivs_tac MIDW_misc a). destruct (NCTX a ltac:(right; left; exact Hm)) as [N1 N2].
           apply STAT; [apply MIDW_misc_libx; exact Hm| exact N2| exact N1]. }
  split. { eapply CLEAN_agreeR; [exact CL| exact AG|].
           assert (Hm : rin_ivs MIDW_misc A_global_cleanup) by (in_ivs_tac MIDW_misc A_global_cleanup).
           destruct (NCTX A_global_cleanup ltac:(right; left; exact Hm)) as [N1 N2].
           apply STAT; [apply MIDW_misc_libx; exact Hm| exact N2| exact N1]. }
  split; [exact FIT|].
  assert (RG : relro_grp m').
  { eapply relro_grp_agreeR; [exact (conj G1 (conj G2 (conj G3 (conj M1 (conj M2 (conj HT RL))))))| exact AG|].
    intros a Ha. destruct (NCTX a ltac:(right; right; exact Ha)) as [N1 N2]. destruct Ha as [Ha Hn].
    split; [right; split; assumption|]. intros K. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (N1 K)].
    unfold memflag_foot in K. cbn [rin_ivs fst snd] in K. lia. }
  exact RG.
Qed.

(* [comment removed for export] *)
Lemma LIBMID_newmembuf : forall LIB Lall Lnew LA SP m m' M x,
  LIBMID LIB m M ->
  xpres Lall SP (memflag_foot ++ ctxph_foot (mid_ctx M)) m m' -> (forall b, In b LIB -> In b Lall) ->
  CTXPH Lnew m' (CtxReady x) -> ctxph_delta (mid_ctx M) LA x -> (mid_ctx M = CtxFresh -> CTX_keys m') -> MEMFLAG m' 1 ->
  LIBMID (LA ++ LIB) m' (mkMID 1 (CtxReady x) (mid_err M) (mid_E M) (mid_vdso M)).
Proof.
  intros LIB Lall Lnew LA SP m m' M x LM XP SUB CP D KE MF'.
  destruct M as [f [|b] eph E v]; cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ctxph_foot ctxph_delta] in *.
  - assert (EF : eph = ErrFresh) by (destruct eph as [|c]; [reflexivity| destruct LM as (_ & _ & _ & F & _); destruct F]).
    subst eph. eapply LIBMID_stageA; [exact LM| exact XP| exact SUB| exact CP| exact D| exact (KE eq_refl)| exact MF'].
  - destruct D as [-> ->]. cbn [app]. rewrite app_nil_r in XP.
    exact (LIBMID_mf LIB Lall SP m m' (mkMID f (CtxReady b) eph E v) LM XP SUB MF').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mid_newlib_ok_trans : forall M0 M1 M2 L1 L2,
  mid_step M0 M1 -> mid_newlib_ok M0 M1 L1 -> mid_step M1 M2 -> mid_newlib_ok M1 M2 L2 -> mid_newlib_ok M0 M2 (L2 ++ L1).
Proof.
  intros [f0 c0 e0 E0 v0] [f1 c1 e1 E1 v1] [f2 c2 e2 E2 v2] L1 L2 S1 N1 S2 N2.
  unfold mid_step, mid_newlib_ok in *. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *.
  destruct S1 as (_ & SC1 & SE1 & _). destruct S2 as (_ & SC2 & SE2 & _).
  destruct N1 as (LA1 & LE1 & P1 & C1 & R1). destruct N2 as (LA2 & LE2 & P2 & C2 & R2).
  exists (LA2 ++ LA1), (LE2 ++ LE1). split.
  { transitivity ((LA2 ++ LE2) ++ (LA1 ++ LE1)); [apply Permutation_app; assumption|].
    rewrite <- !app_assoc. apply Permutation_app_head. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  split.
  - destruct c1 as [|b1].
    + (* [comment removed for export] *)
      destruct c0 as [|b0]; [| discriminate (SC1 b0 eq_refl)]. cbn in C1. subst LA1. rewrite app_nil_r. exact C2.
    + subst LA2. cbn [app]. rewrite (SC2 b1 eq_refl). destruct c0 as [|b0]; [exact C1|].
      cbn [ctxph_delta] in C1. destruct C1 as [_ ->]. reflexivity.
  - destruct e1 as [|d1].
    + destruct e0 as [|d0]; [| discriminate (SE1 d0 eq_refl)]. cbn in R1. subst LE1. rewrite app_nil_r. exact R2.
    + subst LE2. cbn [app]. rewrite (SE2 d1 eq_refl). destruct e0 as [|d0]; [exact R1|].
      cbn [errph_delta] in R1. destruct R1 as [_ ->]. reflexivity.
Qed.
Lemma CTXPH_recontent : forall L L' m m' x, CTXPH L m (CtxReady x) -> CTXPH L' m' (CtxReady x) -> CTXPH L m' (CtxReady x).
Proof.
  intros L L' m m' x [_ [[I1 [Z1 [R1 _]]] EXO]] [CS' [[_ [_ [_ MU']]] _]]. cbn [CTXPH].
  split; [exact CS'|]. split; [exact (conj I1 (conj Z1 (conj R1 MU')))| exact EXO].
Qed.
Lemma ERRPH_mono : forall L L' m eph, ERRPH L m eph -> (forall b, In b L -> In b L') -> ERRPH L' m eph.
Proof. intros L L' m [|c] P SUB; cbn [ERRPH] in *; [exact P|]. destruct P as [ES CH]. split; [exact ES| eapply ERR_chain_mono; eassumption]. Qed.
Lemma blocks_ERRST_cleared : blocks_ERRST errst_cleared = [].
Proof. reflexivity. Qed.
Lemma blocks_ERRST_zero : blocks_ERRST errst_zero = [].
Proof. reflexivity. Qed.

Lemma LIBMID_errcall : forall LIB Lall Lnew LE SP m m' M x c E',
  LIBMID LIB m M -> mid_ctx M = CtxReady x ->
  xpres Lall SP (ERR_X ++ errph_foot (mid_err M)) m m' -> (forall b, In b LIB -> In b Lall) ->
  CTXPH Lnew m' (CtxReady x) -> ERRPH Lnew m' (ErrReady c) -> errph_delta (mid_err M) LE c ->
  ERRST (blocks_ERRST E') m' (blk_addr (ec_es c)) E' -> errst_fits E' -> MEMFLAG m' 1 ->      (* [comment removed for export] *)
  LIBMID (LE ++ LIB) m' (mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M)).
Proof.
  intros LIB Lall Lnew LE SP m m' M x c E' LM CX XP SUB CP' EP' D EX' FIT' MF'.
  destruct M as [f cph eph E v]. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in CX, XP, D. subst cph.
  destruct LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL).
  cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ERRPH_mid] in IM, MF, CP, EPm, EX, VD.
  pose proof (magree_mid_of_xpres _ _ _ _ _ _ XP SUB) as AG.
  (* [comment removed for export] *)
  assert (NERR : forall a, rin_ivs MIDW_misc a \/ relro_addr a -> ~ rin_ivs (ERR_X ++ errph_foot eph) a).
  { intros a Ha K. apply rin_ivs_app in K. destruct K as [K|K].
    - unfold MIDW_misc, relro_addr, ERR_X in *. cbn [rin_ivs fst snd] in *. addrs. lia.
    - destruct eph as [|c0]; cbn [errph_foot rin_ivs fst snd] in K; [exact K|].
      cbn [ERRPH] in EPm. destruct EPm as [_ CH].
      destruct (chain_cell_block LIB m c0 a CH ltac:(unfold chain_cell; right; right; right; unfold ERRST_SIZE in K |- *; lia)) as (b & _ & Hr & RB).
      pose proof (block_cell_off_image b a RB Hr). unfold MIDW_misc, relro_addr in Ha. cbn [rin_ivs fst snd] in Ha. addrs. lia. }
  assert (STAT : forall a, rin_ivs MIDW_misc a -> midR LIB (ERR_X ++ errph_foot eph) a).
  { intros a Ha. split; [left; left; apply MIDW_misc_libx; exact Ha| apply NERR; left; exact Ha]. }
  unfold LIBMID. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ERRPH_mid ERRX].
  split. { eapply IMPL_agreeR; [exact IM| exact AG|]. intros a Ha. apply STAT. in_ivs_tac MIDW_misc a. }
  split; [exact MF'|].
  split; [eapply CTXPH_recontent; [eapply CTXPH_mono; [exact CP| intros b Hb; apply in_or_app; right; exact Hb]| exact CP']|].
  split. { cbn [ERRPH] in EP' |- *. destruct EP' as [ES' CH']. split; [exact ES'|]. eapply ERR_chain_relist; [exact CH'|].
           destruct eph as [|c0]; cbn [errph_delta] in D.
           - destruct D as (_ & _ & _ & HF). eapply Forall_impl; [| exact HF]. intros b Hb. apply in_or_app. left. exact Hb.
           - destruct D as [-> ->]. cbn [app ERRPH] in EPm |- *. destruct EPm as [_ CH].
             unfold ERR_chain, chain_blocks in CH |- *. destruct CH as (I2 & _ & _ & I3 & _ & _ & I4 & _ & _ & I5 & _ & I6 & _ & _).
             repeat (apply Forall_cons; [assumption|]). apply Forall_nil. }
  split; [exact EX'|].
  split. { eapply VDSO_agreeR; [exact VD| exact AG|]. intros a Ha. apply STAT. in_ivs_tac MIDW_misc a. }
  split. { eapply CLEAN_agreeR; [exact CL| exact AG|]. apply STAT. in_ivs_tac MIDW_misc A_global_cleanup. }
  split; [exact FIT'|].
  assert (RG : relro_grp m').
  { eapply relro_grp_agreeR; [exact (conj G1 (conj G2 (conj G3 (conj M1 (conj M2 (conj HT RL))))))| exact AG|].
    intros a Ha. split; [right; exact Ha| apply NERR; right; exact Ha]. }
  exact RG.
Qed.


(* [comment removed for export] *)
Lemma LIBMID_errcall_mf : forall LIB Lall Lnew LE SP m m' M x c E',
  LIBMID LIB m M -> mid_ctx M = CtxReady x ->
  xpres Lall SP (ERR_X ++ memflag_foot ++ errph_foot (mid_err M)) m m' -> (forall b, In b LIB -> In b Lall) ->
  CTXPH Lnew m' (CtxReady x) -> ERRPH Lnew m' (ErrReady c) -> errph_delta (mid_err M) LE c ->
  ERRST (blocks_ERRST E') m' (blk_addr (ec_es c)) E' -> errst_fits E' -> MEMFLAG m' 1 ->
  LIBMID (LE ++ LIB) m' (mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M)).
Proof.
  intros LIB Lall Lnew LE SP m m' M x c E' LM CX XP SUB CP' EP' D EX' FIT' MF'.
  destruct M as [f cph eph E v]. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in CX, XP, D. subst cph.
  destruct LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL).
  cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ERRPH_mid] in IM, MF, CP, EPm, EX, VD.
  pose proof (magree_mid_of_xpres _ _ _ _ _ _ XP SUB) as AG.
  assert (NERR : forall a, rin_ivs MIDW_misc a \/ relro_addr a -> ~ rin_ivs (ERR_X ++ memflag_foot ++ errph_foot eph) a).
  { intros a Ha K. apply rin_ivs_app in K. destruct K as [K|K]; [| apply rin_ivs_app in K; destruct K as [K|K]].
    - unfold MIDW_misc, relro_addr, ERR_X in *. cbn [rin_ivs fst snd] in *. addrs. lia.
    - unfold MIDW_misc, relro_addr, memflag_foot in *. cbn [rin_ivs fst snd] in *. addrs. lia.
    - destruct eph as [|c0]; cbn [errph_foot rin_ivs fst snd] in K; [exact K|].
      cbn [ERRPH] in EPm. destruct EPm as [_ CH].
      destruct (chain_cell_block LIB m c0 a CH ltac:(unfold chain_cell; right; right; right; unfold ERRST_SIZE in K |- *; lia)) as (b & _ & Hr & RB).
      pose proof (block_cell_off_image b a RB Hr). unfold MIDW_misc, relro_addr in Ha. cbn [rin_ivs fst snd] in Ha. addrs. lia. }
  assert (STAT : forall a, rin_ivs MIDW_misc a -> midR LIB (ERR_X ++ memflag_foot ++ errph_foot eph) a).
  { intros a Ha. split; [left; left; apply MIDW_misc_libx; exact Ha| apply NERR; left; exact Ha]. }
  unfold LIBMID. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ERRPH_mid ERRX].
  split. { eapply IMPL_agreeR; [exact IM| exact AG|]. intros a Ha. apply STAT. in_ivs_tac MIDW_misc a. }
  split; [exact MF'|].
  split; [eapply CTXPH_recontent; [eapply CTXPH_mono; [exact CP| intros b Hb; apply in_or_app; right; exact Hb]| exact CP']|].
  split. { cbn [ERRPH] in EP' |- *. destruct EP' as [ES' CH']. split; [exact ES'|]. eapply ERR_chain_relist; [exact CH'|].
           destruct eph as [|c0]; cbn [errph_delta] in D.
           - destruct D as (_ & _ & _ & HF). eapply Forall_impl; [| exact HF]. intros b Hb. apply in_or_app. left. exact Hb.
           - destruct D as [-> ->]. cbn [app ERRPH] in EPm |- *. destruct EPm as [_ CH].
             unfold ERR_chain, chain_blocks in CH |- *. destruct CH as (I2 & _ & _ & I3 & _ & _ & I4 & _ & _ & I5 & _ & I6 & _ & _).
             repeat (apply Forall_cons; [assumption|]). apply Forall_nil. }
  split; [exact EX'|].
  split. { eapply VDSO_agreeR; [exact VD| exact AG|]. intros a Ha. apply STAT. in_ivs_tac MIDW_misc a. }
  split. { eapply CLEAN_agreeR; [exact CL| exact AG|]. apply STAT. in_ivs_tac MIDW_misc A_global_cleanup. }
  split; [exact FIT'|].
  assert (RG : relro_grp m').
  { eapply relro_grp_agreeR; [exact (conj G1 (conj G2 (conj G3 (conj M1 (conj M2 (conj HT RL))))))| exact AG|].
    intros a Ha. split; [right; exact Ha| apply NERR; right; exact Ha]. }
  exact RG.
Qed.

(* [comment removed for export] *)
Lemma libx_in_image : forall a, rin_ivs LIBX a -> IMG_LO <= a < IMG_HI.
Proof. intros a HX. unfold LIBX, LIBX0 in HX. cbn [rin_ivs fst snd] in HX. addrs. lia. Qed.
Lemma LIBMID_mf_X : forall LIB Lall SP X m m' M,
  LIBMID LIB m M -> xpres Lall SP (memflag_foot ++ X) m m' -> (forall b, In b LIB -> In b Lall) -> MEMFLAG m' 1 ->
  (forall a, rin_ivs X a -> a < IMG_LO \/ IMG_HI <= a) ->
  (forall a b, rin_ivs X a -> In b LIB -> ~ (blk_addr b <= a < blk_addr b + blk_size b)) ->
  LIBMID LIB m' (mkMID 1 (mid_ctx M) (mid_err M) (mid_E M) (mid_vdso M)).
Proof.
  intros LIB Lall SP X m m' M LM XP SUB MF' OFF OUT. eapply LIBMID_agree_mf; [exact LM| | exact MF'].
  eapply magree_mono; [eapply magree_mid_of_xpres; [exact XP| exact SUB]|].
  intros a [Ha Hn]. split; [exact Ha|]. intros K. apply rin_ivs_app in K. destruct K as [K|K].
  - apply Hn. unfold memflag_foot in K. cbn [rin_ivs fst snd] in K. lia.
  - destruct Ha as [[HL|(b & Hb & Hr)]|HR].
    + pose proof (libx_in_image a HL). pose proof (OFF a K). lia.
    + exact (OUT a b K Hb Hr).
    + pose proof (OFF a K). unfold RELRO_LO, RELRO_HI, IMG_LO, IMG_HI in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma errst_fits_clear : forall n line, Forall (fun s => lb_bytes (blocks_slot s) <= ERRDEBUG_BYTES /\ lb_big (blocks_slot s) = 0) (repeat (slot_clear line) n).
Proof. intros n line. induction n as [|n IH]; [apply Forall_nil|]. cbn [repeat]. apply Forall_cons; [| exact IH]. cbn. unfold ERRDEBUG_BYTES. lia. Qed.
Lemma errst_fits_zero : errst_fits errst_zero.
Proof. exact (errst_fits_clear 16 0). Qed.
Lemma errst_fits_cleared : errst_fits errst_cleared.
Proof. exact (errst_fits_clear 16 (2^32 - 1)). Qed.
Lemma errst_fits_canonical : forall E, errst_canonical E -> errst_fits E.
Proof. intros E [-> | ->]; [exact errst_fits_zero| exact errst_fits_cleared]. Qed.
Lemma Forall_firstn_es : forall (P : errslot -> Prop) ss i, Forall P ss -> Forall P (firstn i ss).
Proof.
  intros P ss. induction ss as [|y ss IH]; intros [|i] F; cbn; [apply Forall_nil| apply Forall_nil| apply Forall_nil|].
  inversion F; subst. apply Forall_cons; [assumption| apply IH; assumption].
Qed.
Lemma Forall_skipn_es : forall (P : errslot -> Prop) ss j, Forall P ss -> Forall P (skipn j ss).
Proof.
  intros P ss. induction ss as [|y ss IH]; intros [|j] F; cbn; [apply Forall_nil| apply Forall_nil| exact F|].
  inversion F; subst. apply IH. assumption.
Qed.
Lemma Forall_slot_upd : forall (P : errslot -> Prop) ss i x, Forall P ss -> P x -> Forall P (slot_upd ss i x).
Proof.
  intros P ss i x F Px. unfold slot_upd. apply Forall_app. split; [apply Forall_firstn_es; exact F|].
  apply Forall_cons; [exact Px| apply Forall_skipn_es; exact F].
Qed.
Lemma Forall_slot_at : forall (P : errslot -> Prop) E i, Forall P (es_slots E) -> P (slot_clear 0) -> P (slot_at E i).
Proof.
  intros P E i F P0. unfold slot_at. generalize (Z.to_nat i) as n. intros n.
  revert F. revert n. generalize (es_slots E) as ss. induction ss as [|y ss IH]; intros [|n] F; cbn; [exact P0| exact P0| |];
    inversion F; subst; [assumption| apply IH; assumption].
Qed.
Lemma errst_fits_raise : forall E A1 p1 n1 line A2 p2 n2 lib reason,
  errst_fits E -> raise_sizes A1 n1 A2 n2 -> errst_fits (errst_raise E A1 p1 n1 line A2 p2 n2 lib reason).
Proof.
  intros E A1 p1 n1 line A2 p2 n2 lib reason FE (_ & _ & P1 & P2 & SUM). unfold errst_raise, errst_seterr, errst_debug, errst_new, errst_fits.
  cbn [es_slots es_top es_bottom].
  set (E1 := mkERRST (slot_upd (es_slots E) (Z.to_nat (err_next (es_top E))) (slot_clear (2 ^ 32 - 1))) (err_next (es_top E))
                     (if err_next (es_top E) =? es_bottom E then err_next (es_bottom E) else es_bottom E)).
  assert (F1 : errst_fits E1).
  { unfold errst_fits, E1. cbn [es_slots]. apply Forall_slot_upd; [exact FE|]. cbn. unfold ERRDEBUG_BYTES. lia. }
  set (x2 := mkSLOT (sl_flags (slot_at E1 (err_next (es_top E)))) (sl_buffer (slot_at E1 (err_next (es_top E)))) A1 (Some (p1, n1)) line A2 (Some (p2, n2))).
  assert (P2x : lb_bytes (blocks_slot x2) <= ERRDEBUG_BYTES /\ lb_big (blocks_slot x2) = 0).
  { unfold x2. cbn [blocks_slot sl_file sl_file_o sl_func sl_func_o blocks_of app lb_bytes lb_big fold_right blk_size snd fst].
    unfold big1, BIGB, ERRDEBUG_BYTES in *. destruct (2028 <? n1) eqn:B1; destruct (2028 <? n2) eqn:B2;
      rewrite ?Z.ltb_lt, ?Z.ltb_ge in B1, B2; lia. }
  set (E2 := mkERRST (slot_upd (es_slots E1) (Z.to_nat (es_top E1)) x2) (es_top E1) (es_bottom E1)).
  assert (F2 : errst_fits E2).
  { unfold errst_fits, E2. cbn [es_slots]. apply Forall_slot_upd; [exact F1| exact P2x]. }
  change (Forall (fun s => lb_bytes (blocks_slot s) <= ERRDEBUG_BYTES /\ lb_big (blocks_slot s) = 0)
            (slot_upd (es_slots E2) (Z.to_nat (es_top E2))
               (mkSLOT (sl_flags (slot_at E2 (es_top E2))) (ERR_PACK lib reason) (sl_file (slot_at E2 (es_top E2))) (sl_file_o (slot_at E2 (es_top E2)))
                       (sl_line (slot_at E2 (es_top E2))) (sl_func (slot_at E2 (es_top E2))) (sl_func_o (slot_at E2 (es_top E2)))))).
  apply Forall_slot_upd; [exact F2|].
  pose proof (Forall_slot_at _ E2 (es_top E2) F2 ltac:(cbn; unfold ERRDEBUG_BYTES; lia)) as Q.
  cbn [blocks_slot sl_file sl_file_o sl_func sl_func_o] in Q |- *. exact Q.
Qed.
Lemma errst_fits_bounds : forall E, length (es_slots E) = 16%nat -> errst_fits E ->
  Z.of_nat (length (blocks_ERRST E)) <= ERRSTR_CNT /\ lb_bytes (blocks_ERRST E) <= ERRSTR_BYTES /\ lb_big (blocks_ERRST E) = 0.
Proof.
  intros E LEN FE. unfold blocks_ERRST, ERRSTR_CNT, ERRSTR_BYTES. unfold errst_fits in FE.
  assert (GEN : forall ss, Forall (fun s => lb_bytes (blocks_slot s) <= ERRDEBUG_BYTES /\ lb_big (blocks_slot s) = 0) ss ->
            Z.of_nat (length (concat (map blocks_slot ss))) <= 2 * Z.of_nat (length ss)
            /\ lb_bytes (concat (map blocks_slot ss)) <= ERRDEBUG_BYTES * Z.of_nat (length ss)
            /\ lb_big (concat (map blocks_slot ss)) = 0).
  { intros ss F. induction F as [|y ss [PB PG] F IH]; [cbn; lia|]. cbn [map concat length].
    rewrite length_app, lb_bytes_app, lb_big_app.
    assert (L2 : (length (blocks_slot y) <= 2)%nat).
    { unfold blocks_slot. rewrite length_app. destruct (sl_file_o y) as [[? ?]|]; destruct (sl_func_o y) as [[? ?]|]; cbn; lia. }
    destruct IH as (IH1 & IH2 & IH3). unfold ERRDEBUG_BYTES in *. lia. }
  destruct (GEN _ FE) as (G1 & G2 & G3). rewrite LEN in G1, G2. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G1, G2. unfold ERRDEBUG_BYTES in G2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_cells_of_none : forall m A cs,
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m (wa a) = None) ->
  cells_wf cs -> rw_bytes_b usegs A (cells_bytes cs) = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 ->
  rw_cells usegs m A cs.
Proof.
  intros m A cs HN WF HB HA HL. pose proof (cells_bytes_length cs WF) as LEN.
  apply (rw_cells_recast usegs m A [CB (length (cells_bytes cs)) (cells_bytes cs)]).
  - apply none_on_rw_cells; [intros a Ha; apply HN; rewrite LEN in Ha; exact Ha| exact HB| exact HA| rewrite LEN; exact HL].
  - exact WF.
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity.
  - cbn [cells_size csize]. rewrite LEN. lia.
Qed.
Local Ltac img_chunk NONE :=
  apply rw_cells_of_none;
  [ intros a Ha; apply NONE; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul Pos.add] in Ha; revert Ha; addrs; intros Ha;
    first [ in_ivs_tac LIBX0 a | lia | split; lia ]
  | cbn; repeat split; try reflexivity; try exact I
  | vm_compute; reflexivity
  | addrs; lia
  | addrs; cbn; lia ].

Lemma relro_grp_of_image : forall m, relro_lib m -> relro_grp m.
Proof.
  intros m RL. assert (NONE : forall a, RELRO_LO <= a < RELRO_HI /\ ~ (RGOT_SSP <= a < RGOT_SSP + 8) -> m (wa a) = None) by (intros a [Ha Hn]; exact (RL a Ha Hn)).
  unfold relro_grp, GOT_mem, GOT_echfree, GOT_x509vpm, METH_mem, METH_b64, HPKE_tabs, id_rows, HPKE_KEM_IDS, HPKE_KDF_IDS, HPKE_AEAD_IDS.
  repeat match goal with |- _ /\ _ => split end; try exact RL; try exact I; img_chunk NONE.
Qed.

Lemma LIBMID_fresh : forall LIB m, LIBST Fresh LIB m -> relro_lib m -> LIB = [] /\ LIBMID [] m (mkMID 0 CtxFresh ErrFresh errst_zero false).
Proof.
  intros LIB m [-> PR] RL. split; [reflexivity|]. unfold lib_pristine in PR.
  assert (NONE : forall a, rin_ivs LIBX0 a -> m (wa a) = None) by exact PR.
  assert (NON : forall A n, (forall a, A <= a < A + n -> rin_ivs LIBX0 a) -> none_on m A n) by (intros A n K a Ha; apply NONE; apply K; exact Ha).
  unfold LIBMID. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso CTXPH ERRPH_mid ERRX].
  split; [unfold IMPL_mem; img_chunk NONE|].
  split. { exists (b8 0). split; [img_chunk NONE| split; [reflexivity| left; reflexivity]]. }
  split. { unfold CTX_fresh. repeat match goal with |- _ /\ _ => split end; (apply NON; intros a Ha; revert Ha; addrs; intros Ha; in_ivs_tac LIBX0 a). }
  split. { unfold ERR_fresh_core. repeat match goal with |- _ /\ _ => split end; (apply NON; intros a Ha; revert Ha; addrs; intros Ha; in_ivs_tac LIBX0 a). }
  split; [reflexivity|].
  split; [img_chunk NONE|].
  split; [apply NONE; in_ivs_tac LIBX0 A_global_cleanup|].
  split; [exact errst_fits_zero|].
  exact (relro_grp_of_image m RL).
Qed.

Lemma ERRST_canon_relist : forall L L' m a E, errst_canonical E -> ERRST L m a E -> ERRST L' m a E.
Proof.
  intros L L' m a E CE ER. unfold ERRST in *.
  destruct ER as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & OWN).
  destruct K2 as [K2a K2b]. destruct K3 as [K3a K3b].
  repeat match goal with |- _ /\ _ => split end; try assumption.
  clear OWN. destruct CE as [-> | ->]; cbn [es_slots errst_zero errst_cleared repeat];
    repeat (apply Forall_cons; [cbn [sl_file sl_file_o sl_func sl_func_o sl_flags sl_buffer sl_line slot_clear ofield]; repeat split; try reflexivity; lia|]); apply Forall_nil.
Qed.
Lemma blocks_ERRST_canonical : forall E, errst_canonical E -> blocks_ERRST E = [].
Proof. intros E [-> | ->]; reflexivity. Qed.

Lemma LIBMID_inited : forall LIB m i, LIBST (Inited i) LIB m -> relro_lib m ->
  exists E, errst_canonical E /\ lib_fits LIB /\ LIBMID LIB m (mkMID 1 (CtxReady (li_ctx i)) (ErrReady (li_chain i)) E (li_vdso_done i)).
Proof.
  intros LIB m i ((IM & VD & MFb & CS & ES & CL) & (CB & CH & (E & ER & CE)) & SZ) RL.
  exists E. split; [exact CE|]. split; [exact SZ|]. unfold LIBMID. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso CTXPH ERRPH_mid ERRPH ERRX].
  split; [exact IM|]. split; [exists (b8 1); split; [exact MFb| split; [reflexivity| right; reflexivity]]|].
  split; [split; [exact CS| exact CB]|]. split; [split; [exact ES| exact CH]|].
  split; [eapply ERRST_canon_relist; [exact CE| exact ER]|].
  split; [exact VD|]. split; [exact CL|]. split; [exact (errst_fits_canonical E CE)|]. exact (relro_grp_of_image m RL).
Qed.

Lemma LIBST_of_mid : forall LIB m x c E v, LIBMID LIB m (mkMID 1 (CtxReady x) (ErrReady c) E v) -> errst_canonical E -> lib_fits LIB ->
  LIBST (Inited (mkLI x c v)) LIB m.
Proof.
  intros LIB m x c E v LM CE SZ. destruct LM as (IM & MF & CP & EP & EX & VD & CL & _).
  cbn [mid_flag mid_ctx mid_err mid_E mid_vdso CTXPH ERRPH_mid ERRPH ERRX] in *.
  destruct CP as [CS CB]. destruct EP as [ES CH]. destruct MF as (fb & MFb & V1 & _).
  assert (FB : fb = b8 1) by (rewrite (byte_eq_of_unsigned fb 1 V1); reflexivity). subst fb.
  split.
  - unfold lib_statics_inited. cbn [li_ctx li_chain li_vdso_done]. exact (conj IM (conj VD (conj MFb (conj CS (conj ES CL))))).
  - split; [| exact SZ]. unfold lib_blocks_inited. cbn [li_ctx li_chain li_vdso_done]. split; [exact CB|]. split; [exact CH|].
    exists E. split; [eapply ERRST_canon_relist; [exact CE| exact EX]| exact CE].
Qed.
End HCW.
