(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Export NodesCfg.          (* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanLayout.      (* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr FP ZBridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlDecode YajlParser
     YajlFactsBuf YajlFactsLex YajlFactsDecode YajlFactsParse.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages ExecA LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AYajlRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition amem (X n : Z) : Prop := 0x603000 <= X /\ (X + n <= 0x7fff7000 \/ 0x10007fff8000 <= X).   (* [comment removed for export] *)
Lemma amem_intro : forall X n, AsanLayout.app_mem X n -> 0x603000 <= X -> amem X n.
Proof. intros X n H HX. unfold amem. unfold AsanLayout.app_mem, AsanLayout.kLowAppEnd, AsanLayout.kLowShadowMapBeg, AsanSizeClass.kHighMemBeg, AsanSizeClass.kShadowBase, AsanSizeClass.kHighMemEnd, AsanSizeClass.kPageSize in H. cbn in H. pose proof AsanLayout.alloc_ceiling_le_high_end as CE. unfold AsanSizeClass.kHighMemEnd in CE. cbn in CE. lia. Qed.
Lemma amem_mono : forall X n n', amem X n -> n' <= n -> amem X n'.
Proof. intros X n n' H Hle. unfold amem in *. lia. Qed.
Lemma amem_sub : forall X n X' n', amem X n -> X <= X' -> X' + n' <= X + n -> 0 <= n' -> amem X' n'.
Proof. intros X n X' n' H H1 H2 H3. unfold amem in *. lia. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AY_WRAP_STACK : Z := AMALLOC_STACK.                (* [comment removed for export] *)
Definition AY_ICP_STACK : Z := AICP_STACK.                     (* [comment removed for export] *)
Definition AY_CB_STACK : Z := 16.
Definition AY_BUF_SMALL_STACK : Z := 16.                       (* [comment removed for export] *)
Definition AY_BUF_ALLOC_STACK : Z := 32 + AMALLOC_STACK.
Definition AY_BUF_FREE_STACK : Z := 32 + AMALLOC_STACK.
Definition AY_BUF_APPEND_STACK : Z := 128 + AMALLOC_STACK.
Definition AY_LEX_ALLOC_STACK : Z := 64 + AY_BUF_ALLOC_STACK.
Definition AY_LEX_REALLOC_STACK : Z := 32 + AY_BUF_SMALL_STACK.
Definition AY_LEX_FREE_STACK : Z := 32 + AY_BUF_FREE_STACK.
Definition AY_LEX_LEX_STACK : Z := 208 + AY_BUF_APPEND_STACK.
Definition AY_DECODE_STACK : Z := 272 + AY_BUF_APPEND_STACK.    (* [comment removed for export] *)
Definition AY_RESET_STACK : Z := 32 + AY_LEX_REALLOC_STACK.
Definition AY_DO_PARSE_STACK : Z := 368 + AY_DECODE_STACK.     (* [comment removed for export] *)
Definition AY_PARSE_STACK : Z := 16 + AY_DO_PARSE_STACK.
Definition AY_ALLOC_STACK : Z := 208 + AY_LEX_ALLOC_STACK.      (* [comment removed for export] *)
Definition AY_FREE_STACK : Z := 32 + AY_LEX_FREE_STACK.
Definition AY_FUZZ_STACK : Z := 112 + AY_PARSE_STACK.         (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record ay_params := mkAYP {
  y_APS : Type;                                                        (* [comment removed for export] *)
  y_AHK : y_APS -> list ablock -> list fblock -> mem -> Model -> Prop; (* [comment removed for export] *)
  y_SO : y_APS -> StdioBase.stdout_st;                                 (* [comment removed for export] *)
  y_aS : y_APS -> word -> Prop; y_aN : y_APS -> nat; y_aEB : y_APS -> Z;   (* [comment removed for export] *)
  y_uanchor : mem -> Z -> word -> word -> Prop;                        (* [comment removed for export] *)
  y_ayR : y_APS -> Model -> y_APS -> Model -> Prop;                     (* [comment removed for export] *)
  y_aflag : Z -> Z -> Z;                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  y_acredit : y_APS -> Z; y_acharge : Z -> Z; y_arefund : Z -> Z;                (* [comment removed for export] *)
  y_phi_buf : ybuf -> Z; y_phi_hand : yhandle -> Z -> Z; y_phi_new : Z -> Z; y_cost : Z -> Z;
  y_free_cost : Z                                                      (* [comment removed for export] *) }.

(* [comment removed for export] *)
Lemma ybv_swrap32_eq : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. intros z. reflexivity. Qed.
Lemma ysx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, ybv_swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.
Lemma yzx32_small : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Section AYajl.
Variable Y : ay_params.
Let APS : Type := y_APS Y.
Let AHK : APS -> list ablock -> list fblock -> mem -> Model -> Prop := y_AHK Y.
Let SO : APS -> StdioBase.stdout_st := y_SO Y.
Let aS : APS -> word -> Prop := y_aS Y.
Let aN : APS -> nat := y_aN Y.
Let aEB : APS -> Z := y_aEB Y.
Let uanchor : mem -> Z -> word -> word -> Prop := y_uanchor Y.
Let ayR : APS -> Model -> APS -> Model -> Prop := y_ayR Y.
Let aflag : Z -> Z -> Z := y_aflag Y.
Let acredit : APS -> Z := y_acredit Y.
Let acharge : Z -> Z := y_acharge Y.
Let yphi_buf : ybuf -> Z := y_phi_buf Y.
Let yphi_hand : yhandle -> Z -> Z := y_phi_hand Y.
Let yphi_new : Z -> Z := y_phi_new Y.
Let ycost : Z -> Z := y_cost Y.
Let yfree_cost : Z := y_free_cost Y.
Let arefund : Z -> Z := y_arefund Y.

#[local] Notation usp sp := (bv_unsigned sp).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AYST (s : APS) (LB : list ablock) (LF : list fblock) (m : mem) (mo : Model) : Prop :=
  AHK s LB LF m mo
  /\ rw_cells asegs m AY_CALLBACKS (callbacks_cells ayc)
  /\ rw_cells asegs m AY_BUF_ALLOC_ERROR (buf_alloc_error_cells ayc)
  /\ rw_cells asegs m AY_NOOP_ALLOCS anoop_allocs_cells
  /\ ay_statics m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ay_static (a : Z) : Prop := (0xa8f60 <= a < 0xa9040) \/ (0x5e01d0 <= a < 0x5e01f0).

(* [comment removed for export] *)
Fixpoint yin_ivs (X : list (Z * Z)) (a : Z) : Prop :=
  match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ yin_ivs X' a end.
Definition ay_client_addr (REST : list ablock) (LF : list fblock) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ in_ablock REST a \/ in_fframe LF a \/ ay_static a.
Definition ay_pres (REST : list ablock) (LF : list fblock) (SP : Z) (X : list (Z * Z)) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> ay_client_addr REST LF SP a -> ~ yin_ivs X a ->
    m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

Lemma ay_pres_refl : forall REST LF SP X m, ay_pres REST LF SP X m m.
Proof. intros REST LF SP X m a _ _ _. auto. Qed.
Lemma ay_pres_trans : forall REST LF SP X m1 m2 m3,
  ay_pres REST LF SP X m1 m2 -> ay_pres REST LF SP X m2 m3 -> ay_pres REST LF SP X m1 m3.
Proof.
  intros REST LF SP X m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
  split; [congruence| auto].
Qed.
Lemma ay_pres_weaken : forall REST REST' LF LF' SP SP' X X' m m',
  ay_pres REST LF SP X m m' -> SP <= SP' -> (forall b, In b REST' -> In b REST) -> (forall f, In f LF' -> In f LF) ->
  (forall a, yin_ivs X a -> yin_ivs X' a) -> ay_pres REST' LF' SP' X' m m'.
Proof.
  intros REST REST' LF LF' SP SP' X X' m m' H HS HL HF HX a Ha Hc Hx. apply H; [exact Ha| |intros Hx'; apply Hx, HX, Hx'].
  destruct Hc as [Hc|[(b & Hb & Hr)|[(f & Hf & Hr)|Hc]]]; [left; lia| right; left| right; right; left| right; right; right; exact Hc].
  - exists b. split; [apply HL; exact Hb| exact Hr].
  - exists f. split; [apply HF; exact Hf| exact Hr].
Qed.

(* [comment removed for export] *)
Definition ay_acc (LB : list ablock) (LF : list fblock) (x : acc) : Prop :=
  let a := bv_unsigned (fst x) in let k := Z.of_nat (snd x) in
  (alloc_ceiling <= a /\ a + k <= 2^47)
  \/ (AY_IMG_LO <= a /\ a + k <= AY_IMG_HI)
  \/ (exists b, In b LB /\ ab_addr b <= a /\ a + k <= ab_addr b + ab_size b)
  \/ (exists b, In b LB /\ oshw_lo (ab_addr b) <= a /\ a + k <= oshw_hi (ab_addr b) (ab_size b))
  \/ (exists f, In f LF /\ snd f <= a /\ a + k <= snd f + ff_bytes (fst f))
  \/ (exists f, In f LF /\ oshw_lo (snd f) <= a /\ a + k <= oshw_lo (snd f) + Z.shiftl 8 (fst f))
  \/ (exists f, In f LF /\ a = aflag (fst f) (snd f) /\ k = 1)
  \/ (oshw_lo AY_IMG_LO <= a /\ a + k <= oshw_hi AY_IMG_LO (AY_IMG_HI - AY_IMG_LO)).

(* [comment removed for export] *)
Definition ay_write_ok (LB : list ablock) (LF : list fblock) (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ (exists b, In b LB /\ ab_addr b <= fst iv /\ snd iv <= ab_addr b + ab_size b)
  \/ (exists f, In f LF /\ snd f <= fst iv /\ snd iv <= snd f + ff_bytes (fst f))
  \/ (exists f, In f LF /\ oshw_lo (snd f) <= fst iv /\ snd iv <= oshw_lo (snd f) + Z.shiftl 8 (fst f))
  \/ (0x5e01d0 <= fst iv /\ snd iv <= 0x5e01d4).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ayframe_pre (m : mem) (sp tp : word) (fc : bv 32) (lo budget : Z) : Prop :=
  stk asegs m lo (usp sp) /\ alloc_ceiling <= lo /\ lo <= usp sp - budget /\ usp sp < 2^47 /\ usp sp mod 16 = 0
  /\ mem_inv asegs m /\ tp = wz (c_tp ACONSTS) /\ frm0 fc.
Definition ayframe_post (m m' : mem) (sp : word) (fc' : bv 32) (lo : Z) (REST : list ablock) (LF : list fblock) (X : list (Z * Z)) : Prop :=
  mem_inv asegs m' /\ stk asegs m' lo (usp sp) /\ frm0 fc' /\ True /\ ay_pres REST LF (usp sp) X m m'.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nbig (LB : list ablock) : Z := Z.of_nat (length (List.filter (fun b => 64512 <? ab_size b) LB)).
Definition AY_NBIG_REST : Z := 7900.

(* [comment removed for export] *)
Definition mh_same (mh mh' : mhand) : Prop :=
  mh_addr mh' = mh_addr mh /\ mh_lexer mh' = mh_lexer mh
  /\ mb_addr (mh_lexbuf mh') = mb_addr (mh_lexbuf mh) /\ mb_addr (mh_decbuf mh') = mb_addr (mh_decbuf mh)
  /\ mh_ctx mh' = mh_ctx mh.
Definition mb_same (mb mb' : mbuf) : Prop := mb_addr mb' = mb_addr mb.

(* [comment removed for export] *)
Definition ayaf_ok (REST : list ablock) (m : mem) (AF : Z) : Prop :=
  exists b, In b REST /\ ab_addr b <= AF /\ AF + 32 <= ab_addr b + 8 * (ab_size b / 8) /\ AF mod 8 = 0
            /\ oshadow m (ab_addr b) (ab_size b) /\ oshw_hi 0 (2^47) <= ab_addr b.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ysrc_range (REST : list ablock) (LF : list fblock) (S n : Z) : Prop :=
  (exists bt, In bt REST /\ ab_addr bt <= S /\ S + n <= ab_addr bt + ab_size bt)
  \/ (0x10000 <= S /\ S + n <= 0x31000)
  \/ (exists f, In f LF /\ snd f <= S /\ S + n <= snd f + ff_bytes (fst f))
  \/ n = 0.
(* [comment removed for export] *)
Definition ysrc_shadow (m : mem) (S n : Z) : Prop :=
  n = 0 \/ exists A sz, oshadow m A sz /\ A <= S /\ S + n <= A + sz.
(* [comment removed for export] *)
Definition ysrc_win (REST : list ablock) (LF : list fblock) (SP : Z) (m : mem) (S n : Z) : Prop :=
  0 < n -> forall s' LBx m' mo', AHK s' (LBx ++ REST) LF m' mo' -> ay_pres REST LF SP [] m m' ->
    exists ws, shadow_window asegs m' A_SB S n ws /\ range_clean A_SB S n ws
          /\ pol (acc_ok (m_vm_lazy mo') (aS s')) (shw_lo A_SB S) (shw_hi A_SB S n).

#[warnings="-notation-for-abbreviation"] Notation buf_rep := (buf_rep asegs).
#[warnings="-notation-for-abbreviation"] Notation buf_struct := (buf_struct asegs).
#[warnings="-notation-for-abbreviation"] Notation buf_data := (buf_data asegs).
#[warnings="-notation-for-abbreviation"] Notation lexer_rep := (lexer_rep asegs).
#[warnings="-notation-for-abbreviation"] Notation lexer_struct := (lexer_struct asegs).
#[warnings="-notation-for-abbreviation"] Notation hand_rep := (hand_rep asegs ayc).
#[warnings="-notation-for-abbreviation"] Notation hand_struct := (hand_struct asegs ayc).
#[warnings="-notation-for-abbreviation"] Notation bs_rep := (bs_rep asegs).
#[warnings="-notation-for-abbreviation"] Notation ctx_rep := (ctx_rep asegs).
#[warnings="-notation-for-abbreviation"] Notation text_at := (text_at asegs).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AHK_y_kip_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo ->
    m_halted mo = None /\ minvA mo /\ LI (aS s) (aN s) (aEB s) mo
    /\ (forall x, ay_acc LB LF x -> acc_ok (m_vm_lazy mo) (aS s) x)
    /\ (forall mo', magree mo mo' -> LI (aS s) (aN s) (aEB s) mo' -> AHK s LB LF m mo' /\ ayR s mo s mo').
(* [comment removed for export] *)
Definition AHK_y_mem_inv_stmt : Prop := forall s LB LF m mo, AHK s LB LF m mo -> mem_inv asegs m.
Definition AHK_y_perm_stmt : Prop :=
  forall s LB LB' LF LF' m mo, AHK s LB LF m mo -> Permutation LB LB' -> Permutation LF LF' -> AHK s LB' LF' m mo.
Definition AHK_y_blocks_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo ->
    (forall b, In b LB -> ablock_range ACONSTS (ab_addr b) (ab_size b))
    /\ (forall b1 b2, In b1 LB -> In b2 LB -> ab_addr b1 <> ab_addr b2 ->
          ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1)
    /\ List.NoDup (map ab_addr LB).
(* [comment removed for export] *)
Definition AHK_y_frame_stmt : Prop :=
  forall s LB LF m m' mo W,
    AHK s LB LF m mo -> munch W m m' -> wmono asegs m m' -> Forall (ay_write_ok LB LF) W -> AHK s LB LF m' mo.
(* [comment removed for export] *)
Definition AHK_y_statics_stmt : Prop := forall s LB LF m mo, AHK s LB LF m mo -> ay_statics m.
(* [comment removed for export] *)
Definition AHK_y_block_shadow_stmt : Prop :=
  forall s LB LF m mo b, AHK s LB LF m mo -> In b LB -> 0 < ab_size b ->
    oshadow m (ab_addr b) (ab_size b) /\ amem (ab_addr b) (ab_size b).
(* [comment removed for export] *)
Definition AHK_y_small_high_stmt : Prop :=
  forall s LB LF m mo b, AHK s LB LF m mo -> In b LB -> 0 < ab_size b <= 64512 -> oshw_hi 0 (2^47) <= ab_addr b.
(* [comment removed for export] *)
Definition AHK_y_layout_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo ->
    (forall f, In f LF -> amem (snd f) (ff_bytes (fst f)) /\ snd f + ff_bytes (fst f) <= alloc_ceiling /\ snd f mod ff_bytes (fst f) = 0 /\ 0 <= fst f <= 1
                          /\ amem (aflag (fst f) (snd f)) 1 /\ aflag (fst f) (snd f) + 1 <= alloc_ceiling)
    /\ (forall f b, In f LF -> In b LB ->
          (ab_addr b + ab_size b <= snd f \/ snd f + ff_bytes (fst f) <= ab_addr b)
          /\ (ab_addr b + ab_size b <= aflag (fst f) (snd f) \/ aflag (fst f) (snd f) + 1 <= ab_addr b))
    /\ (forall f1 f2, In f1 LF -> In f2 LF -> snd f1 <> snd f2 ->
          snd f1 + ff_bytes (fst f1) <= snd f2 \/ snd f2 + ff_bytes (fst f2) <= snd f1).
(* [comment removed for export] *)
Definition AHK_y_aflsep_stmt : Prop :=
  forall s LB LF m mo f1 f2, AHK s LB LF m mo -> In f1 LF -> In f2 LF -> snd f1 <> snd f2 ->
    aflag (fst f1) (snd f1) + 1 <= snd f2 \/ snd f2 + ff_bytes (fst f2) <= aflag (fst f1) (snd f1).
(* [comment removed for export] *)
Definition AHK_y_fnodup_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo -> List.NoDup (map snd LF).
(* [comment removed for export] *)
Definition AHK_y_flag_cell_stmt : Prop :=
  forall s LB LF m mo f, AHK s LB LF m mo -> In f LF ->
    (exists fl, rw_cells asegs m (aflag (fst f) (snd f)) [C1 fl])
    /\ (aflag (fst f) (snd f) + 1 <= snd f \/ snd f + ff_bytes (fst f) <= aflag (fst f) (snd f)).
(* [comment removed for export] *)
Definition AHK_y_globals_shadow_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo -> oshadow m AY_CALLBACKS 88 /\ oshadow m AY_NOOP_ALLOCS 32 /\ oshadow m AY_BUF_ALLOC_ERROR 32
    /\ oshadow m 0x215e0 256 /\ oshadow m 0x21560 4 /\ oshadow m 0x21580 5 /\ oshadow m 0x215a0 4.
(* [comment removed for export] *)
Definition ff_live_class (LF : list fblock) (N : Z) : nat := length (filter (fun f => Z.eqb (fst f) N) LF).
Definition astack_malloc_stmt (N : Z) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (lo : Z) (K : TSet),
  K [] -> AHK s LB LF m mo -> (ff_live_class LF N < 2)%nat ->
  stk asegs m lo (usp sp) -> alloc_ceiling <= lo -> lo <= usp sp - AMALLOC_STACK -> usp sp <= 2^47 -> usp sp mod 16 = 0 ->
  mem_inv asegs m -> tp = wz (c_tp ACONSTS) -> frm0 fc ->
  forall RR : Z, RR <= acredit s ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
          (m' : mem) (mo' : Model) (s' : APS) (ff : Z) (junk : list byte),
     stk asegs m' lo (usp sp) -> ay_pres LB LF (usp sp) [] m m' -> wmono asegs m m' -> mem_inv asegs m' -> frm0 fc' -> SO s' = SO s ->
     0 < ff -> ff mod ff_bytes N = 0 -> amem ff (ff_bytes N) -> ff + ff_bytes N <= alloc_ceiling ->
     (forall f, In f LF -> snd f + ff_bytes (fst f) <= ff \/ ff + ff_bytes N <= snd f) ->
     rw_cells asegs m' ff [CB (Z.to_nat (ff_bytes N - 8)) junk; C8 (wz (aflag N ff))] ->
     rw_cells asegs m' (oshw_lo ff) [CB (Z.to_nat (Z.shiftl 8 N)) (repeat (Z_to_bv 8 0) (Z.to_nat (Z.shiftl 8 N)))] ->
     (exists fl, rw_cells asegs m' (aflag N ff) [C1 fl]) ->
     AHK s' LB ((N, ff) :: LF) m' mo' -> ayR s mo s' mo' -> RR <= acredit s' ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz ff) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                             F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (wz ENTRY) fc None m (seg_rom asegs)) mo) K.
Fixpoint ff_remove (N ff : Z) (LF : list fblock) : list fblock :=
  match LF with [] => [] | f :: r => if (Z.eqb (fst f) N && Z.eqb (snd f) ff)%bool then r else f :: ff_remove N ff r end.
(* [comment removed for export] *)
Definition AHK_y_fake_release_stmt : Prop :=
  forall s LB LF m m' mo N ff, AHK s LB LF m mo -> In (N, ff) LF ->
    munch [(aflag N ff, aflag N ff + 1)] m m' -> wmono asegs m m' ->
    rw_cells asegs m' (aflag N ff) [C1 (Z_to_bv 8 0)] -> AHK s LB (ff_remove N ff LF) m' mo.
(* [comment removed for export] *)
Definition ayR_refl_stmt : Prop := forall s mo, ayR s mo s mo.
Definition ayR_trans_stmt : Prop := forall s1 mo1 s2 mo2 s3 mo3, ayR s1 mo1 s2 mo2 -> ayR s2 mo2 s3 mo3 -> ayR s1 mo1 s3 mo3.
(* [comment removed for export] *)
Definition AHK_y_ayR_stmt : Prop :=
  forall s LB LF m mo s' LB' LF' m' mo', AHK s LB LF m mo -> AHK s' LB' LF' m' mo' -> ayR s mo s' mo'.
(* [comment removed for export] *)
Definition yacct_nonneg_stmt : Prop :=
  (forall n, 0 <= acharge n) /\ (forall b, 0 <= yphi_buf b) /\ (forall h L, 0 <= yphi_hand h L) /\ (forall L, 0 <= yphi_new L).
(* [comment removed for export] *)
Definition yacct_free_stmt : Prop := 0 <= yfree_cost.
Definition yacct_new_stmt : Prop := forall L, 0 <= L -> yphi_new L <= ycost L.
Definition yacct_hand_mono_stmt : Prop := forall h L L', 0 <= L' <= L -> yphi_hand h L' <= yphi_hand h L.
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aywrap_malloc_stmt : Prop :=
  forall (n : Z) (LB : list ablock) (LF : list fblock) (lo RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s LB LF m mo ->
  a1 = wz n ->
  0 < n <= 2^27 ->
  acharge n + RR <= acredit s -> 0 <= RR ->
  nbig LB <= 8000 ->
  ayframe_pre m sp tp fc lo AY_WRAP_STACK ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (A : Z),
     ayframe_post m m' sp fc' lo LB LF [] -> SO s' = SO s -> ayR s mo s' mo' -> RR <= acredit s' ->
     a0' = wz A /\ ablock_range ACONSTS A n /\ amem A n /\ (n <= 64512 -> oshw_hi 0 (2^47) <= A) /\ oshadow m' A n
                 /\ (exists junk, rw_cells asegs m' A [CB (Z.to_nat n) junk])
                 /\ AYST s' (mkABlock A n :: LB) LF m' mo'  ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_MALLOC_W) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)
Definition aywrap_free_stmt : Prop :=
  forall (A n : Z) (LB : list ablock) (LF : list fblock) (lo RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s LB LF m mo ->
  In (mkABlock A n) LB ->
  a1 = wz A ->
  yfree_cost + RR <= acredit s -> 0 <= RR ->
  nbig LB <= 8000 ->
  ayframe_pre m sp tp fc lo AY_WRAP_STACK ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) ,
     ayframe_post m m' sp fc' lo (ab_remove A LB) LF [] -> SO s' = SO s -> ayR s mo s' mo' -> RR <= acredit s' ->
     AYST s' (ab_remove A LB) LF m' mo'  ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_FREE_W) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)
Definition aywrap_free_null_stmt : Prop :=
  forall (u : unit) (LB : list ablock) (LF : list fblock) (lo RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s LB LF m mo ->
  a1 = wz 0 ->
  0 + RR <= acredit s -> 0 <= RR ->
  nbig LB <= 8000 ->
  ayframe_pre m sp tp fc lo AY_WRAP_STACK ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) ,
     ayframe_post m m' sp fc' lo LB LF [] -> SO s' = SO s -> ayR s mo s' mo' -> RR <= acredit s' ->
     AYST s' LB LF m' mo'  ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_FREE_W) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)
Definition aywrap_realloc_stmt : Prop :=
  forall (A sz n : Z) (old : list byte) (LB : list ablock) (LF : list fblock) (lo RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s LB LF m mo ->
  In (mkABlock A sz) LB ->
  bytes_at asegs m A old ->
  Z.of_nat (length old) = sz ->
  a1 = wz A ->
  a2 = wz n ->
  0 < n <= 2^27 ->
  acharge n + yfree_cost + RR <= acredit s -> 0 <= RR ->
  nbig LB <= 8000 ->
  ayframe_pre m sp tp fc lo AY_WRAP_STACK ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (A' : Z),
     ayframe_post m m' sp fc' lo (ab_remove A LB) LF [] -> SO s' = SO s -> ayR s mo s' mo' -> RR <= acredit s' ->
     a0' = wz A' /\ ablock_range ACONSTS A' n /\ amem A' n /\ (n <= 64512 -> oshw_hi 0 (2^47) <= A') /\ oshadow m' A' n
                  /\ (exists junk, rw_cells asegs m' A' [CB (Z.to_nat (Z.min n sz)) (firstn (Z.to_nat (Z.min n sz)) old);
                                                   CB (Z.to_nat (n - Z.min n sz)) junk])
                  /\ AYST s' (mkABlock A' n :: ab_remove A LB) LF m' mo'
                  /\ arefund sz + RR <= acredit s'  ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_REALLOC_W) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)
Definition aywrap_realloc_null_stmt : Prop :=
  forall (n : Z) (LB : list ablock) (LF : list fblock) (lo RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s LB LF m mo ->
  a1 = wz 0 ->
  a2 = wz n ->
  0 < n <= 2^27 ->
  acharge n + RR <= acredit s -> 0 <= RR ->
  nbig LB <= 8000 ->
  ayframe_pre m sp tp fc lo AY_WRAP_STACK ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (A : Z),
     ayframe_post m m' sp fc' lo LB LF [] -> SO s' = SO s -> ayR s mo s' mo' -> RR <= acredit s' ->
     a0' = wz A /\ ablock_range ACONSTS A n /\ amem A n /\ (n <= 64512 -> oshw_hi 0 (2^47) <= A) /\ oshadow m' A n
                 /\ (exists junk, rw_cells asegs m' A [CB (Z.to_nat n) junk])
                 /\ AYST s' (mkABlock A n :: LB) LF m' mo'  ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_REALLOC_W) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aycb_null_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)  (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ a0' = wz 1 /\ m' = m.
Definition aycb_null_stmt : Prop :=
  forall (P : acc -> Prop) , forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv asegs m ->
  evtA asegs P (aycb_null_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc  m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_CB_NULL) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition aycb_boolean_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)  (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ a0' = wz 1 /\ m' = m.
Definition aycb_boolean_stmt : Prop :=
  forall (P : acc -> Prop) , forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv asegs m ->
  evtA asegs P (aycb_boolean_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc  m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_CB_BOOLEAN) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition aycb_string_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)  (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ a0' = wz 1 /\ m' = m.
Definition aycb_string_stmt : Prop :=
  forall (P : acc -> Prop) , forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv asegs m ->
  evtA asegs P (aycb_string_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc  m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_CB_STRING) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition aycb_number_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (l lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ a0' = wz 1 /\ ay_statics m'.
Definition aycb_number_stmt : Prop :=
  forall (P : acc -> Prop) (l lo : Z), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  mem_inv asegs m ->
  a2 = wz l ->
  0 < l < 2^32 ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 2^47 ->
  pol P lo (bv_unsigned sp) ->
  evtA asegs P (aycb_number_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc l lo m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_CB_NUMBER) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition aycb_start_map_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (CX lo : Z) (cx : yctx) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp); (CX + 4, CX + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ a0' = wz 1 /\ ctx_rep m' CX (mkCtx (cx_arrayLevel cx) (cx_objectLevel cx + 1)) /\ oshadow m' CX 8 /\ ay_statics m'.
Definition aycb_start_map_stmt : Prop :=
  forall (P : acc -> Prop) (CX lo : Z) (cx : yctx), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  ctx_rep m CX cx ->
  cx_objectLevel cx + 1 < 2^31 ->
  oshadow m CX 8 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 2^47 ->
  amem CX 8 ->
  CX + 8 <= alloc_ceiling ->
  a0 = wz CX ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  opol P CX 8 ->
  evtA asegs P (aycb_start_map_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc CX lo cx m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_CB_START_MAP) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition aycb_map_key_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (CX lo : Z) (cx : yctx) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ a0' = wz 1 /\ ctx_rep m' CX cx /\ oshadow m' CX 8 /\ ay_statics m'.
Definition aycb_map_key_stmt : Prop :=
  forall (P : acc -> Prop) (CX lo : Z) (cx : yctx), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  ctx_rep m CX cx ->
  0 < cx_objectLevel cx ->
  oshadow m CX 8 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 2^47 ->
  amem CX 8 ->
  CX + 8 <= alloc_ceiling ->
  a0 = wz CX ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  opol P CX 8 ->
  evtA asegs P (aycb_map_key_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc CX lo cx m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_CB_MAP_KEY) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition aycb_end_map_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (CX lo : Z) (cx : yctx) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp); (CX + 4, CX + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ a0' = wz 1 /\ ctx_rep m' CX (mkCtx (cx_arrayLevel cx) (cx_objectLevel cx - 1)) /\ oshadow m' CX 8 /\ ay_statics m'.
Definition aycb_end_map_stmt : Prop :=
  forall (P : acc -> Prop) (CX lo : Z) (cx : yctx), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  ctx_rep m CX cx ->
  0 < cx_objectLevel cx ->
  oshadow m CX 8 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 2^47 ->
  amem CX 8 ->
  CX + 8 <= alloc_ceiling ->
  a0 = wz CX ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  opol P CX 8 ->
  evtA asegs P (aycb_end_map_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc CX lo cx m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_CB_END_MAP) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition aycb_start_array_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (CX lo : Z) (cx : yctx) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp); (CX, CX + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ a0' = wz 1 /\ ctx_rep m' CX (mkCtx (cx_arrayLevel cx + 1) (cx_objectLevel cx)) /\ oshadow m' CX 8 /\ ay_statics m'.
Definition aycb_start_array_stmt : Prop :=
  forall (P : acc -> Prop) (CX lo : Z) (cx : yctx), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  ctx_rep m CX cx ->
  cx_arrayLevel cx + 1 < 2^31 ->
  oshadow m CX 8 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 2^47 ->
  amem CX 8 ->
  CX + 8 <= alloc_ceiling ->
  a0 = wz CX ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  opol P CX 8 ->
  evtA asegs P (aycb_start_array_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc CX lo cx m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_CB_START_ARRAY) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition aycb_end_array_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (CX lo : Z) (cx : yctx) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp); (CX, CX + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ a0' = wz 1 /\ ctx_rep m' CX (mkCtx (cx_arrayLevel cx - 1) (cx_objectLevel cx)) /\ oshadow m' CX 8 /\ ay_statics m'.
Definition aycb_end_array_stmt : Prop :=
  forall (P : acc -> Prop) (CX lo : Z) (cx : yctx), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  ctx_rep m CX cx ->
  0 < cx_arrayLevel cx ->
  oshadow m CX 8 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 2^47 ->
  amem CX 8 ->
  CX + 8 <= alloc_ceiling ->
  a0 = wz CX ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  opol P CX 8 ->
  evtA asegs P (aycb_end_array_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc CX lo cx m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_CB_END_ARRAY) fc None m (seg_rom asegs)).


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition buf_cleared (b : ybuf) : ybuf := mkBuf BS_ok (yb_len b) 0 (yb_data b) [].
Lemma ybuf_clear_leaf : forall b, yb_state b = BS_ok -> yleaf (ybuf_clear b) (buf_cleared b).
Proof. intros b Hs. unfold ybuf_clear. rewrite Hs. apply yl_ret. Qed.
Lemma ybuf_clear_leaf_inv : forall b b', yb_state b = BS_ok -> yleaf (ybuf_clear b) b' -> b' = buf_cleared b.
Proof. intros b b' Hs HL. unfold ybuf_clear in HL. rewrite Hs in HL. exact (yleaf_ret_inv _ _ HL). Qed.
(* [comment removed for export] *)
Definition lex_reset (lx : ylexer) : ylexer :=
  mkLexer 0 0 LE_ok (buf_cleared (lx_buf lx)) (lx_bufblk lx) 0 0 (lx_allowComments lx) (lx_validateUTF8 lx).
Lemma ylex_realloc_leaf : forall lx, yb_state (lx_buf lx) = BS_ok -> yleaf (ylex_realloc lx) (lex_reset lx).
Proof.
  intros lx Hs. unfold ylex_realloc. eapply yleaf_bind; [apply ybuf_clear_leaf; exact Hs|]. apply yl_ret.
Qed.
Lemma ylex_realloc_leaf_inv : forall lx lx', yb_state (lx_buf lx) = BS_ok -> yleaf (ylex_realloc lx) lx' -> lx' = lex_reset lx.
Proof.
  intros lx lx' Hs HL. unfold ylex_realloc in HL. apply yleaf_bind_inv in HL. destruct HL as (b & Hb & HR).
  apply (ybuf_clear_leaf_inv _ _ Hs) in Hb. subst b. exact (yleaf_ret_inv _ _ HR).
Qed.
Lemma lex_inv_reset : forall lx, lex_inv lx -> lex_inv (lex_reset lx).
Proof.
  intros lx (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold lex_inv, lex_reset, buf_cleared. cbn.
  rewrite H5, H6, H7. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition aybuf_err_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (B st lo : Z) (OA On : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ a0' = wz st /\ rw_cells asegs m' B [C4 (wz st)] /\ oshadow m' OA On /\ ay_statics m'.
Definition aybuf_err_stmt : Prop :=
  forall (P : acc -> Prop) (B st lo : Z) (OA On : Z), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  rw_cells asegs m B [C4 (wz st)] ->
  0 <= st < 2^31 ->
  B <> 0 ->
  B mod 4 = 0 ->
  oshadow m OA On ->
  OA <= B ->
  B + 4 <= OA + On ->
  0 <= OA ->
  OA + On <= lo ->
  oshw_hi OA On <= lo ->
  (oshw_hi OA On <= OA \/ OA + On <= oshw_lo OA) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 2^47 ->
  a0 = wz B ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  pol P B (B + 4) ->
  pol P (oshw_lo OA) (oshw_hi OA On) ->
  evtA asegs P (aybuf_err_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B st lo OA On m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_BUF_ERR) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition aybuf_len_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (B D AF lo : Z) (b : ybuf) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ a0' = wz (yb_used b) /\ buf_struct m' B b D AF /\ oshadow m' B SIZEOF_BUF /\ ay_statics m'.
Definition aybuf_len_stmt : Prop :=
  forall (P : acc -> Prop) (B D AF lo : Z) (b : ybuf), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  buf_struct m B b D AF ->
  yb_state b = BS_ok ->
  B <> 0 ->
  oshadow m B SIZEOF_BUF ->
  oshw_hi 0 (2^47) <= B ->
  B + SIZEOF_BUF <= alloc_ceiling ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 2^47 ->
  a0 = wz B ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  opol P B SIZEOF_BUF ->
  evtA asegs P (aybuf_len_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B D AF lo b m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_BUF_LEN) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition aybuf_data_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (B D AF lo : Z) (b : ybuf) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ a0' = wz D /\ buf_struct m' B b D AF /\ oshadow m' B SIZEOF_BUF /\ ay_statics m'.
Definition aybuf_data_stmt : Prop :=
  forall (P : acc -> Prop) (B D AF lo : Z) (b : ybuf), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  buf_struct m B b D AF ->
  yb_state b = BS_ok ->
  B <> 0 ->
  oshadow m B SIZEOF_BUF ->
  oshw_hi 0 (2^47) <= B ->
  B + SIZEOF_BUF <= alloc_ceiling ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 2^47 ->
  a0 = wz B ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  opol P B SIZEOF_BUF ->
  evtA asegs P (aybuf_data_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B D AF lo b m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_BUF_DATA) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition aybuf_clear_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (B D AF lo : Z) (b : ybuf) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch ([(lo, bv_unsigned sp); (B + 8, B + 12)] ++ match yb_data b with Some _ => [(D, D + 1)] | None => [] end) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ buf_struct m' B (buf_cleared b) D AF /\ buf_data m' D (buf_cleared b) /\ oshadow m' B SIZEOF_BUF /\ (yb_data b <> None -> oshadow m' D (yb_len b)) /\ ay_statics m'.
Definition aybuf_clear_stmt : Prop :=
  forall (P : acc -> Prop) (B D AF lo : Z) (b : ybuf), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  buf_struct m B b D AF ->
  buf_data m D b ->
  yb_state b = BS_ok ->
  buf_inv b ->
  B <> 0 ->
  oshadow m B SIZEOF_BUF ->
  oshw_hi 0 (2^47) <= B ->
  B + SIZEOF_BUF <= alloc_ceiling ->
  (yb_data b <> None -> oshadow m D (yb_len b) /\ amem D (yb_len b) /\ D + yb_len b <= alloc_ceiling /\ (B + SIZEOF_BUF <= D \/ D + yb_len b <= B)) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 2^47 ->
  a0 = wz B ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  opol P B SIZEOF_BUF ->
  (yb_data b <> None -> opol P D (yb_len b)) ->
  evtA asegs P (aybuf_clear_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B D AF lo b m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_BUF_CLEAR) fc None m (seg_rom asegs)).


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aybs_set_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (h : yhandle) (mh : mhand) (s s' : ystate) (rest : list ystate) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp); (mh_stack mh + h_used h - 1, mh_stack mh + h_used h)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ hand_struct m' h mh /\ bs_rep m' (mh_stack mh) (h_set_stack h (s' :: rest)) /\ oshadow m' (mh_addr mh) SIZEOF_HANDLE /\ oshadow m' (mh_stack mh) (h_stack_size h) /\ ay_statics m'.
Definition aybs_set_stmt : Prop :=
  forall (P : acc -> Prop) (h : yhandle) (mh : mhand) (s s' : ystate) (rest : list ystate) (lo : Z), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  hand_struct m h mh ->
  bs_rep m (mh_stack mh) h ->
  h_stack h = s :: rest ->
  h_stack_blk h <> None ->
  oshadow m (mh_addr mh) SIZEOF_HANDLE ->
  oshadow m (mh_stack mh) (h_stack_size h) ->
  oshw_hi 0 (2^47) <= mh_addr mh ->
  mh_addr mh + SIZEOF_HANDLE <= alloc_ceiling ->
  amem (mh_stack mh) (h_stack_size h) ->
  mh_stack mh + h_stack_size h <= alloc_ceiling ->
  (mh_addr mh + SIZEOF_HANDLE <= mh_stack mh \/ mh_stack mh + h_stack_size h <= mh_addr mh) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 2^47 ->
  a0 = wz (mh_addr mh + 48) ->
  a1 = wz (state_code s') ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  opol P (mh_addr mh) SIZEOF_HANDLE ->
  opol P (mh_stack mh) (h_stack_size h) ->
  evtA asegs P (aybs_set_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h mh s s' rest lo m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_BS_SET) fc None m (seg_rom asegs)).


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ayhexToDigit_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (VP S v lo : Z) (h0 h1 h2 h3 : Z) (v' : Z) (OA On : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp); (VP, VP + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' VP [C4 (wz v')] /\ bytes_at asegs m' S (zbytes [h0; h1; h2; h3]) /\ oshadow m' OA On /\ ay_statics m'.
Definition ayhexToDigit_stmt : Prop :=
  forall (P : acc -> Prop) (VP S v lo : Z) (h0 h1 h2 h3 : Z) (v' : Z) (OA On : Z), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  rw_cells asegs m VP [C4 (wz v)] ->
  0 <= v < 2^16 ->
  bytes_at asegs m S (zbytes [h0; h1; h2; h3]) ->
  is_vhc h0 = true ->
  is_vhc h1 = true ->
  is_vhc h2 = true ->
  is_vhc h3 = true ->
  hex_loop v [h0; h1; h2; h3] = Some v' ->
  oshadow m OA On ->
  OA <= S ->
  S + 4 <= OA + On ->
  amem OA On ->
  OA + On <= alloc_ceiling ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 2^47 ->
  bv_unsigned sp <= VP ->
  VP + 4 <= 2^47 ->
  bytes_at asegs m (A_SB + VP / 8) [Z_to_bv 8 0] ->
  a0 = wz VP ->
  a1 = wz S ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  pol P VP (VP + 4) ->
  pol P (A_SB + VP / 8) (A_SB + VP / 8 + 1) ->
  pol P S (S + 4) ->
  pol P (oshw_lo OA) (oshw_hi OA On) ->
  evtA asegs P (ayhexToDigit_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc VP S v lo h0 h1 h2 h3 v' OA On m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_HEXTODIGIT) fc None m (seg_rom asegs)).


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ayset_default_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (YAF lo : Z) (junk : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp); (YAF, YAF + 32)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' YAF (alloc_cells ayc) /\ oshadow m' YAF 32 /\ ay_statics m'.
Definition ayset_default_stmt : Prop :=
  forall (P : acc -> Prop) (YAF lo : Z) (junk : list byte), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  rw_cells asegs m YAF [CB 32 junk] ->
  oshadow m YAF 32 ->
  amem YAF 32 ->
  YAF + 32 <= alloc_ceiling ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= 2^47 ->
  a0 = wz YAF ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  opol P YAF 32 ->
  evtA asegs P (ayset_default_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc YAF lo junk m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_SET_DEFAULT) fc None m (seg_rom asegs)).


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aylex_realloc_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (L AF lo : Z) (lx : ylexer) (mbl : mbuf) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp); (L, L + 48); (mb_addr mbl, mb_addr mbl + 32)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ a0' = wz L /\ lexer_rep m' L (lex_reset lx) mbl AF /\ oshadow m' L SIZEOF_LEXER /\ oshadow m' (mb_addr mbl) SIZEOF_BUF /\ ay_statics m'.
Definition aylex_realloc_stmt : Prop :=
  forall (P : acc -> Prop) (L AF lo : Z) (lx : ylexer) (mbl : mbuf), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  lexer_rep m L lx mbl AF ->
  yb_state (lx_buf lx) = BS_ok ->
  buf_inv (lx_buf lx) ->
  yb_data (lx_buf lx) = None ->
  L <> 0 ->
  mb_addr mbl <> 0 ->
  oshadow m L SIZEOF_LEXER ->
  oshadow m (mb_addr mbl) SIZEOF_BUF ->
  oshw_hi 0 (2^47) <= L ->
  L + SIZEOF_LEXER <= alloc_ceiling ->
  oshw_hi 0 (2^47) <= mb_addr mbl ->
  mb_addr mbl + SIZEOF_BUF <= alloc_ceiling ->
  (L + SIZEOF_LEXER <= mb_addr mbl \/ mb_addr mbl + SIZEOF_BUF <= L) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - AY_LEX_REALLOC_STACK ->
  bv_unsigned sp <= 2^47 ->
  a0 = wz L ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  opol P L SIZEOF_LEXER ->
  opol P (mb_addr mbl) SIZEOF_BUF ->
  evtA asegs P (aylex_realloc_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L AF lo lx mbl m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_LEX_REALLOC) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition ayreset_parser_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (h : yhandle) (mh : mhand) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
    /\ munch [(lo, bv_unsigned sp); (mh_addr mh + 16, mh_addr mh + 24); (mh_lexer mh, mh_lexer mh + 48); (mb_addr (mh_lexbuf mh), mb_addr (mh_lexbuf mh) + 32)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ hand_struct m' h mh /\ lexer_rep m' (mh_lexer mh) (lex_reset (h_lexer h)) (mh_lexbuf mh) (mh_addr mh + 72) /\ oshadow m' (mh_addr mh) SIZEOF_HANDLE /\ oshadow m' (mh_lexer mh) SIZEOF_LEXER /\ oshadow m' (mb_addr (mh_lexbuf mh)) SIZEOF_BUF /\ ay_statics m'.
Definition ayreset_parser_stmt : Prop :=
  forall (P : acc -> Prop) (h : yhandle) (mh : mhand) (lo : Z), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ay_statics m ->
  hand_struct m h mh ->
  lexer_rep m (mh_lexer mh) (h_lexer h) (mh_lexbuf mh) (mh_addr mh + 72) ->
  yb_state (lx_buf (h_lexer h)) = BS_ok ->
  buf_inv (lx_buf (h_lexer h)) ->
  yb_data (lx_buf (h_lexer h)) = None ->
  mh_addr mh <> 0 ->
  mh_lexer mh <> 0 ->
  mb_addr (mh_lexbuf mh) <> 0 ->
  oshadow m (mh_addr mh) SIZEOF_HANDLE ->
  oshadow m (mh_lexer mh) SIZEOF_LEXER ->
  oshadow m (mb_addr (mh_lexbuf mh)) SIZEOF_BUF ->
  oshw_hi 0 (2^47) <= mh_addr mh ->
  mh_addr mh + SIZEOF_HANDLE <= alloc_ceiling ->
  oshw_hi 0 (2^47) <= mh_lexer mh ->
  mh_lexer mh + SIZEOF_LEXER <= alloc_ceiling ->
  oshw_hi 0 (2^47) <= mb_addr (mh_lexbuf mh) ->
  mb_addr (mh_lexbuf mh) + SIZEOF_BUF <= alloc_ceiling ->
  (mh_lexer mh + SIZEOF_LEXER <= mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + SIZEOF_BUF <= mh_lexer mh) ->
  (mh_addr mh + SIZEOF_HANDLE <= mh_lexer mh \/ mh_lexer mh + SIZEOF_LEXER <= mh_addr mh) ->
  (mh_addr mh + SIZEOF_HANDLE <= mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + SIZEOF_BUF <= mh_addr mh) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) ->
  alloc_ceiling <= lo ->
  lo <= bv_unsigned sp - AY_RESET_STACK ->
  bv_unsigned sp <= 2^47 ->
  a0 = wz (mh_addr mh) ->
  pol P lo (bv_unsigned sp) ->
  pol P AY_IMG_LO AY_IMG_HI ->
  opol P (mh_addr mh) SIZEOF_HANDLE ->
  opol P (mh_lexer mh) SIZEOF_LEXER ->
  opol P (mb_addr (mh_lexbuf mh)) SIZEOF_BUF ->
  evtA asegs P (ayreset_parser_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h mh lo m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_RESET) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aybuf_alloc_rpost (sp : word) (m : mem) (mo : Model) (s : APS) (LF : list fblock) (REST : list ablock) (AF lo : Z) (RR : Z)
    (a0' : word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (B0 : Z) : Prop :=
  SO s' = SO s /\ ayR s mo s' mo' /\ yphi_buf ybuf_zero + RR <= acredit s' /\ ayframe_post m m' sp fc' lo REST LF [] /\ rw_cells asegs m' AF (alloc_cells ayc)
  /\ a0' = wz B0 /\ 0 < B0 /\ oshw_hi 0 (2^47) <= B0 /\ buf_struct m' B0 ybuf_zero 0 AF /\ oshadow m' B0 SIZEOF_BUF
  /\ AYST s' (mkABlock B0 SIZEOF_BUF :: REST) LF m' mo' .
Definition aybuf_alloc_stmt : Prop :=
  forall (LF : list fblock) (REST : list ablock) (AF lo : Z) (RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s REST LF m mo ->
  rw_cells asegs m AF (alloc_cells ayc) ->
  ayaf_ok REST m AF ->
  ayframe_pre m sp tp fc lo AY_BUF_ALLOC_STACK ->
  a0 = wz AF ->
  acharge SIZEOF_BUF + yphi_buf ybuf_zero + RR <= acredit s -> 0 <= RR ->
  nbig REST <= AY_NBIG_REST + 3 ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (B0 : Z),
     aybuf_alloc_rpost sp m mo s LF REST AF lo RR a0' fc' m' mo' s' B0 ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_BUF_ALLOC) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aybuf_free_rpost (sp : word) (m : mem) (mo : Model) (s : APS) (LF : list fblock) (REST : list ablock) (mb : mbuf) (b : ybuf) (AF lo : Z) (RR : Z)
    (a0' : word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS)  : Prop :=
  SO s' = SO s /\ ayR s mo s' mo' /\ 0 + RR <= acredit s' /\ ayframe_post m m' sp fc' lo REST LF [] /\ rw_cells asegs m' AF (alloc_cells ayc) /\ AYST s' REST LF m' mo' .
Definition aybuf_free_stmt : Prop :=
  forall (LF : list fblock) (REST : list ablock) (mb : mbuf) (b : ybuf) (AF lo : Z) (RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s (abl (buf_blocks mb b) ++ REST) LF m mo ->
  buf_rep m mb b AF ->
  rw_cells asegs m AF (alloc_cells ayc) ->
  ayaf_ok REST m AF ->
  oshadow m (mb_addr mb) SIZEOF_BUF ->
  ayframe_pre m sp tp fc lo AY_BUF_FREE_STACK ->
  a0 = wz (mb_addr mb) ->
  yphi_buf b + RR <= acredit s -> 0 <= RR ->
  nbig REST <= AY_NBIG_REST + 3 ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) ,
     aybuf_free_rpost sp m mo s LF REST mb b AF lo RR a0' fc' m' mo' s'  ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_BUF_FREE) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aybuf_append_rpost (sp : word) (m : mem) (mo : Model) (s : APS) (LF : list fblock) (REST : list ablock) (mb : mbuf) (b : ybuf) (AF S : Z) (src : list Z) (lo : Z) (RR : Z)
    (a0' : word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (b' : ybuf) (mb' : mbuf) (LK : list ablock) : Prop :=
  SO s' = SO s /\ ayR s mo s' mo' /\ yphi_buf b' + RR <= acredit s' /\ ayframe_post m m' sp fc' lo REST LF [] /\ rw_cells asegs m' AF (alloc_cells ayc)
  /\ yleaf (ybuf_append b src) b' /\ buf_rep m' mb' b' AF /\ mb_same mb mb'
  /\ oshadow m' (mb_addr mb') SIZEOF_BUF /\ (yb_data b' <> None -> oshadow m' (mb_data mb') (yb_len b') /\ amem (mb_data mb') (yb_len b'))
  /\ LK = [] /\ AYST s' (abl (buf_blocks mb' b') ++ LK ++ REST) LF m' mo'
  /\ (LK <> [] -> yb_state b' <> BS_ok /\ length LK = 1%nat)
  /\ (LK <> [] -> yb_state b = BS_ok) .
Definition aybuf_append_stmt : Prop :=
  forall (LF : list fblock) (REST : list ablock) (mb : mbuf) (b : ybuf) (AF S : Z) (src : list Z) (lo : Z) (RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s (abl (buf_blocks mb b) ++ REST) LF m mo ->
  buf_rep m mb b AF ->
  buf_inv b ->
  rw_cells asegs m AF (alloc_cells ayc) ->
  ayaf_ok REST m AF ->
  oshadow m (mb_addr mb) SIZEOF_BUF ->
  (yb_data b <> None -> oshadow m (mb_data mb) (yb_len b)) ->
  bytes_at asegs m S (zbytes src) ->
  Forall (fun c => 0 <= c < 256) src ->
  (0 < zlength src -> S <> 0) ->
  S + zlength src <= 2^47 ->
  yb_used b + zlength src < 2^26 ->
  ysrc_range REST LF S (zlength src) ->
  ysrc_win REST LF (usp sp) m S (zlength src) ->
  ayframe_pre m sp tp fc lo AY_BUF_APPEND_STACK ->
  a0 = wz (mb_addr mb) ->
  a1 = wz S ->
  a2 = wz (zlength src) ->
  yphi_buf b + RR <= acredit s -> 0 <= RR ->
  nbig REST <= AY_NBIG_REST + 3 ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (b' : ybuf) (mb' : mbuf) (LK : list ablock),
     aybuf_append_rpost sp m mo s LF REST mb b AF S src lo RR a0' fc' m' mo' s' b' mb' LK ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_BUF_APPEND) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aylex_alloc_rpost (sp : word) (m : mem) (mo : Model) (s : APS) (LF : list fblock) (REST : list ablock) (AF aC v8 lo : Z) (RR : Z)
    (a0' : word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (L : Z) (mbl : mbuf) (lx : ylexer) : Prop :=
  SO s' = SO s /\ ayR s mo s' mo' /\ yphi_buf (lx_buf lx) + RR <= acredit s' /\ ayframe_post m m' sp fc' lo REST LF [] /\ rw_cells asegs m' AF (alloc_cells ayc)
  /\ a0' = wz L /\ 0 < L /\ oshw_hi 0 (2^47) <= L /\ oshw_hi 0 (2^47) <= mb_addr mbl
         /\ (exists blk, yleaf (ylex_alloc aC v8) (Some (blk, lx)))
         /\ lexer_rep m' L lx mbl AF /\ mb_data mbl = 0
         /\ oshadow m' L SIZEOF_LEXER /\ oshadow m' (mb_addr mbl) SIZEOF_BUF
         /\ AYST s' (mkABlock L SIZEOF_LEXER :: abl (buf_blocks mbl (lx_buf lx)) ++ REST) LF m' mo' .
Definition aylex_alloc_stmt : Prop :=
  forall (LF : list fblock) (REST : list ablock) (AF aC v8 lo : Z) (RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s REST LF m mo ->
  rw_cells asegs m AF (alloc_cells ayc) ->
  ayaf_ok REST m AF ->
  0 <= aC <= 1 ->
  0 <= v8 <= 1 ->
  ayframe_pre m sp tp fc lo AY_LEX_ALLOC_STACK ->
  a0 = wz AF ->
  a1 = wz aC ->
  a2 = wz v8 ->
  acharge SIZEOF_LEXER + acharge SIZEOF_BUF + yphi_buf ybuf_zero + yfree_cost + RR <= acredit s -> 0 <= RR ->
  nbig REST <= AY_NBIG_REST + 3 ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (L : Z) (mbl : mbuf) (lx : ylexer),
     aylex_alloc_rpost sp m mo s LF REST AF aC v8 lo RR a0' fc' m' mo' s' L mbl lx ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_LEX_ALLOC) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aylex_free_rpost (sp : word) (m : mem) (mo : Model) (s : APS) (LF : list fblock) (REST : list ablock) (L AF : Z) (mbl : mbuf) (lx : ylexer) (lo : Z) (RR : Z)
    (a0' : word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS)  : Prop :=
  SO s' = SO s /\ ayR s mo s' mo' /\ 0 + RR <= acredit s' /\ ayframe_post m m' sp fc' lo REST LF [] /\ rw_cells asegs m' AF (alloc_cells ayc) /\ AYST s' REST LF m' mo' .
Definition aylex_free_stmt : Prop :=
  forall (LF : list fblock) (REST : list ablock) (L AF : Z) (mbl : mbuf) (lx : ylexer) (lo : Z) (RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s (mkABlock L SIZEOF_LEXER :: abl (buf_blocks mbl (lx_buf lx)) ++ REST) LF m mo ->
  lexer_rep m L lx mbl AF ->
  rw_cells asegs m AF (alloc_cells ayc) ->
  ayaf_ok REST m AF ->
  oshadow m L SIZEOF_LEXER ->
  oshadow m (mb_addr mbl) SIZEOF_BUF ->
  ayframe_pre m sp tp fc lo AY_LEX_FREE_STACK ->
  a0 = wz L ->
  yfree_cost + yphi_buf (lx_buf lx) + RR <= acredit s -> 0 <= RR ->
  nbig REST <= AY_NBIG_REST + 3 ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) ,
     aylex_free_rpost sp m mo s LF REST L AF mbl lx lo RR a0' fc' m' mo' s'  ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_LEX_FREE) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)
Definition outref_addr (T D : Z) (ob : outref) : Z :=
  match ob with OB_null => 0 | OB_text i => T + i | OB_lexbuf i => D + i end.


(* [comment removed for export] *)
Definition aylex_lex_rpost (sp : word) (m : mem) (mo : Model) (s : APS) (LF : list fblock) (REST : list ablock) (h : yhandle) (mh : mhand) (T : Z) (txt : list Z) (off OBP OLP OT OTn : Z) (obw olw : word) (lo : Z) (RR : Z)
    (a0' : word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (lx' : ylexer) (tok : ytok) (off' : Z) (ob : outref) (n : Z) (mbl' : mbuf) (LK : list ablock) : Prop :=
  SO s' = SO s /\ ayR s mo s' mo' /\ yphi_buf (lx_buf lx') + RR <= acredit s' /\ ayframe_post m m' sp fc' lo REST LF [(OLP, OLP + 4); (OBP, OBP + 8)]
  /\ yleaf (ylex_lex (h_lexer h) txt (zlength txt) off) (lx', tok, off', ob, n)
  /\ a0' = wz (tok_code tok)
  /\ hand_struct m' (h_set_lex_off h lx' off') mh
  /\ lexer_rep m' (mh_lexer mh) lx' mbl' (mh_addr mh + 72) /\ mb_same (mh_lexbuf mh) mbl'
  /\ (yb_data (lx_buf lx') <> None -> oshadow m' (mb_data mbl') (yb_len (lx_buf lx')) /\ amem (mb_data mbl') (yb_len (lx_buf lx')))
  /\ rw_cells asegs m' OBP [C8 (wz (outref_addr T (mb_data mbl') ob))] /\ rw_cells asegs m' OLP [C4 (wz n)]
  /\ text_at m' T txt
  /\ LK = [] /\ AYST s' (mkABlock (mh_addr mh) SIZEOF_HANDLE :: mkABlock (mh_lexer mh) SIZEOF_LEXER :: abl (buf_blocks mbl' (lx_buf lx')) ++ LK ++ REST) LF m' mo'
  /\ (LK <> [] -> (tok = TK_eof \/ tok = TK_error) /\ length LK = 1%nat) .
Definition aylex_lex_stmt : Prop :=
  forall (LF : list fblock) (REST : list ablock) (h : yhandle) (mh : mhand) (T : Z) (txt : list Z) (off OBP OLP OT OTn : Z) (obw olw : word) (lo : Z) (RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s (mkABlock (mh_addr mh) SIZEOF_HANDLE :: mkABlock (mh_lexer mh) SIZEOF_LEXER :: abl (buf_blocks (mh_lexbuf mh) (lx_buf (h_lexer h))) ++ REST) LF m mo ->
  hand_struct m h mh ->
  lexer_rep m (mh_lexer mh) (h_lexer h) (mh_lexbuf mh) (mh_addr mh + 72) ->
  lex_inv (h_lexer h) ->
  h_bytesConsumed h = off ->
  0 <= off <= zlength txt ->
  zlength txt < 2^26 ->
  text_at m T txt ->
  T + zlength txt <= 2^47 ->
  ((exists bt, In bt REST /\ ab_addr bt <= T /\ T + zlength txt <= ab_addr bt + ab_size bt) \/ zlength txt = 0) ->
  (zlength txt = 0 \/ (oshadow m OT OTn /\ OT <= T /\ T + zlength txt <= OT + OTn /\ amem OT OTn /\ OT + OTn <= alloc_ceiling /\ (exists bt, In bt REST /\ ab_addr bt <= OT /\ OT + OTn <= ab_addr bt + ab_size bt))) ->
  oshadow m (mh_addr mh) SIZEOF_HANDLE ->
  oshadow m (mh_lexer mh) SIZEOF_LEXER ->
  oshadow m (mb_addr (mh_lexbuf mh)) SIZEOF_BUF ->
  rw_cells asegs m OBP [C8 obw] ->
  rw_cells asegs m OLP [C4 olw] ->
  oshadow m OBP 8 ->
  oshadow m OLP 4 ->
  (exists f, In f LF /\ snd f + 32 = OBP /\ OLP = OBP + 32 /\ fst f = 1) ->
  ayframe_pre m sp tp fc lo AY_LEX_LEX_STACK ->
  a0 = wz (mh_lexer mh) ->
  a1 = wz T ->
  a2 = wz (zlength txt) ->
  a3 = wz (mh_addr mh + 32) ->
  a4 = wz OBP ->
  a5 = wz OLP ->
  yphi_buf (lx_buf (h_lexer h)) + RR <= acredit s -> 0 <= RR ->
  nbig REST <= AY_NBIG_REST + 2 ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (lx' : ylexer) (tok : ytok) (off' : Z) (ob : outref) (n : Z) (mbl' : mbuf) (LK : list ablock),
     aylex_lex_rpost sp m mo s LF REST h mh T txt off OBP OLP OT OTn obw olw lo RR a0' fc' m' mo' s' lx' tok off' ob n mbl' LK ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_LEX_LEX) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aystring_decode_rpost (sp : word) (m : mem) (mo : Model) (s : APS) (LF : list fblock) (REST : list ablock) (mbd : mbuf) (db : ybuf) (AF S : Z) (str : list Z) (n OT OTn lo : Z) (RR : Z)
    (a0' : word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (db' : ybuf) (mbd' : mbuf) (LK : list ablock) : Prop :=
  SO s' = SO s /\ ayR s mo s' mo' /\ yphi_buf db' + RR <= acredit s' /\ ayframe_post m m' sp fc' lo REST LF [] /\ rw_cells asegs m' AF (alloc_cells ayc)
  /\ yleaf (ystring_decode db str n) db' /\ buf_rep m' mbd' db' AF /\ mb_same mbd mbd'
  /\ oshadow m' (mb_addr mbd') SIZEOF_BUF /\ (yb_data db' <> None -> oshadow m' (mb_data mbd') (yb_len db') /\ amem (mb_data mbd') (yb_len db'))
  /\ bytes_at asegs m' S (zbytes str)
  /\ LK = [] /\ AYST s' (abl (buf_blocks mbd' db') ++ LK ++ REST) LF m' mo'
  /\ (LK <> [] -> yb_state db' <> BS_ok /\ length LK = 1%nat) .
Definition aystring_decode_stmt : Prop :=
  forall (LF : list fblock) (REST : list ablock) (mbd : mbuf) (db : ybuf) (AF S : Z) (str : list Z) (n OT OTn lo : Z) (RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s (abl (buf_blocks mbd db) ++ REST) LF m mo ->
  buf_rep m mbd db AF ->
  buf_inv db ->
  yb_used db = 0 ->
  rw_cells asegs m AF (alloc_cells ayc) ->
  ayaf_ok REST m AF ->
  oshadow m (mb_addr mbd) SIZEOF_BUF ->
  (yb_data db <> None -> oshadow m (mb_data mbd) (yb_len db) /\ amem (mb_data mbd) (yb_len db)) ->
  bytes_at asegs m S (zbytes str) ->
  Forall (fun c => 0 <= c < 256) str ->
  n = zlength str ->
  n < 2^26 ->
  S <> 0 ->
  S + n < 2^47 ->
  sbody_ix str 0 n ->
  ((exists bt, In bt REST /\ ab_addr bt <= S /\ S + n <= ab_addr bt + ab_size bt) \/ n = 0) ->
  (n = 0 \/ (oshadow m OT OTn /\ OT <= S /\ S + n <= OT + OTn /\ amem OT OTn /\ OT + OTn <= alloc_ceiling /\ (exists bt, In bt REST /\ ab_addr bt <= OT /\ OT + OTn <= ab_addr bt + ab_size bt))) ->
  (ff_live_class LF 0 < 2)%nat ->
  ayframe_pre m sp tp fc lo AY_DECODE_STACK ->
  a0 = wz (mb_addr mbd) ->
  a1 = wz S ->
  a2 = wz n ->
  yphi_buf db + RR <= acredit s -> 0 <= RR ->
  nbig REST <= AY_NBIG_REST + 2 ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (db' : ybuf) (mbd' : mbuf) (LK : list ablock),
     aystring_decode_rpost sp m mo s LF REST mbd db AF S str n OT OTn lo RR a0' fc' m' mo' s' db' mbd' LK ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_STRING_DECODE) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aydo_parse_rpost (sp : word) (m : mem) (mo : Model) (s : APS) (LF : list fblock) (REST : list ablock) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z) (OT OTn lo : Z) (RR : Z)
    (a0' : word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (st : ystatus) (h' : yhandle) (cx' : yctx) (mh' : mhand) (LK : list ablock) : Prop :=
  SO s' = SO s /\ ayR s mo s' mo' /\ yphi_hand h' 0 + RR <= acredit s' /\ ayframe_post m m' sp fc' lo REST LF [(mh_ctx mh, mh_ctx mh + 8)]
  /\ yleaf (ydo_parse jf_callbacks txt (zlength txt) h cx) (st, h', cx')
  /\ a0' = wz (status_code st)
  /\ hand_rep m' h' mh' /\ mh_same mh mh' /\ ctx_rep m' (mh_ctx mh) cx' /\ text_at m' T txt
  /\ (yb_data (lx_buf (h_lexer h')) <> None -> oshadow m' (mb_data (mh_lexbuf mh')) (yb_len (lx_buf (h_lexer h'))) /\ amem (mb_data (mh_lexbuf mh')) (yb_len (lx_buf (h_lexer h'))))
  /\ (yb_data (h_decbuf h') <> None -> oshadow m' (mb_data (mh_decbuf mh')) (yb_len (h_decbuf h')) /\ amem (mb_data (mh_decbuf mh')) (yb_len (h_decbuf h')))
  /\ (h_stack_blk h' <> None -> oshadow m' (mh_stack mh') (h_stack_size h') /\ amem (mh_stack mh') (h_stack_size h'))
  /\ LK = [] /\ AYST s' (abl (yblocks mh' h') ++ LK ++ REST) LF m' mo'
  /\ (length LK <= 1)%nat .
Definition aydo_parse_stmt : Prop :=
  forall (LF : list fblock) (REST : list ablock) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z) (OT OTn lo : Z) (RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s (abl (yblocks mh h) ++ REST) LF m mo ->
  hand_rep m h mh ->
  ctx_rep m (mh_ctx mh) cx ->
  text_at m T txt ->
  T + zlength txt <= 2^47 ->
  zlength txt < 2^26 ->
  ((exists bt, In bt REST /\ ab_addr bt <= T /\ T + zlength txt <= ab_addr bt + ab_size bt) \/ zlength txt = 0) ->
  (zlength txt = 0 \/ (oshadow m OT OTn /\ OT <= T /\ T + zlength txt <= OT + OTn /\ amem OT OTn /\ OT + OTn <= alloc_ceiling /\ (exists bt, In bt REST /\ ab_addr bt <= OT /\ OT + OTn <= ab_addr bt + ab_size bt))) ->
  hinv (zlength txt) (h_set_off h 0) cx ->
  oshadow m (mh_addr mh) SIZEOF_HANDLE ->
  oshadow m (mh_lexer mh) SIZEOF_LEXER ->
  oshadow m (mb_addr (mh_lexbuf mh)) SIZEOF_BUF ->
  oshadow m (mb_addr (mh_decbuf mh)) SIZEOF_BUF ->
  (h_stack_blk h <> None -> oshadow m (mh_stack mh) (h_stack_size h)) ->
  oshadow m (mh_ctx mh) 8 ->
  (exists f, In f LF /\ snd f + 32 = mh_ctx mh /\ fst f = 1) ->
  (ff_live_class LF 1 < 2)%nat ->
  (ff_live_class LF 0 < 2)%nat ->
  ayframe_pre m sp tp fc lo AY_DO_PARSE_STACK ->
  a0 = wz (mh_addr mh) ->
  a1 = wz T ->
  a2 = wz (zlength txt) ->
  yphi_hand (h_set_off h 0) (zlength txt) + RR <= acredit s -> 0 <= RR ->
  nbig REST <= AY_NBIG_REST ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (st : ystatus) (h' : yhandle) (cx' : yctx) (mh' : mhand) (LK : list ablock),
     aydo_parse_rpost sp m mo s LF REST h mh cx T txt OT OTn lo RR a0' fc' m' mo' s' st h' cx' mh' LK ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_DO_PARSE) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)
Definition ayparse_rpost (sp : word) (m : mem) (mo : Model) (s : APS) (LF : list fblock) (REST : list ablock) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z) (OT OTn lo : Z) (RR : Z)
    (a0' : word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (st : ystatus) (h' : yhandle) (cx' : yctx) (mh' : mhand) (LK : list ablock) : Prop :=
  SO s' = SO s /\ ayR s mo s' mo' /\ yphi_hand h' 0 + RR <= acredit s' /\ ayframe_post m m' sp fc' lo REST LF [(mh_ctx mh, mh_ctx mh + 8)]
  /\ yleaf (ydo_parse jf_callbacks txt (zlength txt) h cx) (st, h', cx')
  /\ a0' = wz (status_code st)
  /\ hand_rep m' h' mh' /\ mh_same mh mh' /\ ctx_rep m' (mh_ctx mh) cx' /\ text_at m' T txt
  /\ (yb_data (lx_buf (h_lexer h')) <> None -> oshadow m' (mb_data (mh_lexbuf mh')) (yb_len (lx_buf (h_lexer h'))) /\ amem (mb_data (mh_lexbuf mh')) (yb_len (lx_buf (h_lexer h'))))
  /\ (yb_data (h_decbuf h') <> None -> oshadow m' (mb_data (mh_decbuf mh')) (yb_len (h_decbuf h')) /\ amem (mb_data (mh_decbuf mh')) (yb_len (h_decbuf h')))
  /\ (h_stack_blk h' <> None -> oshadow m' (mh_stack mh') (h_stack_size h') /\ amem (mh_stack mh') (h_stack_size h'))
  /\ LK = [] /\ AYST s' (abl (yblocks mh' h') ++ LK ++ REST) LF m' mo'
  /\ (length LK <= 1)%nat .
Definition ayparse_stmt : Prop :=
  forall (LF : list fblock) (REST : list ablock) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z) (OT OTn lo : Z) (RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s (abl (yblocks mh h) ++ REST) LF m mo ->
  hand_rep m h mh ->
  ctx_rep m (mh_ctx mh) cx ->
  text_at m T txt ->
  T + zlength txt <= 2^47 ->
  zlength txt < 2^26 ->
  ((exists bt, In bt REST /\ ab_addr bt <= T /\ T + zlength txt <= ab_addr bt + ab_size bt) \/ zlength txt = 0) ->
  (zlength txt = 0 \/ (oshadow m OT OTn /\ OT <= T /\ T + zlength txt <= OT + OTn /\ amem OT OTn /\ OT + OTn <= alloc_ceiling /\ (exists bt, In bt REST /\ ab_addr bt <= OT /\ OT + OTn <= ab_addr bt + ab_size bt))) ->
  hinv (zlength txt) (h_set_off h 0) cx ->
  oshadow m (mh_addr mh) SIZEOF_HANDLE ->
  oshadow m (mh_lexer mh) SIZEOF_LEXER ->
  oshadow m (mb_addr (mh_lexbuf mh)) SIZEOF_BUF ->
  oshadow m (mb_addr (mh_decbuf mh)) SIZEOF_BUF ->
  (h_stack_blk h <> None -> oshadow m (mh_stack mh) (h_stack_size h)) ->
  oshadow m (mh_ctx mh) 8 ->
  (exists f, In f LF /\ snd f + 32 = mh_ctx mh /\ fst f = 1) ->
  (ff_live_class LF 1 < 2)%nat ->
  (ff_live_class LF 0 < 2)%nat ->
  ayframe_pre m sp tp fc lo AY_PARSE_STACK ->
  a0 = wz (mh_addr mh) ->
  a1 = wz T ->
  a2 = wz (zlength txt) ->
  yphi_hand (h_set_off h 0) (zlength txt) + RR <= acredit s -> 0 <= RR ->
  nbig REST <= AY_NBIG_REST ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (st : ystatus) (h' : yhandle) (cx' : yctx) (mh' : mhand) (LK : list ablock),
     ayparse_rpost sp m mo s LF REST h mh cx T txt OT OTn lo RR a0' fc' m' mo' s' st h' cx' mh' LK ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_PARSE) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ayalloc_rpost (sp : word) (m : mem) (mo : Model) (s : APS) (LF : list fblock) (REST : list ablock) (CFGP CX lo L : Z) (RR : Z)
    (a0' : word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (h : yhandle) (mh : mhand) : Prop :=
  SO s' = SO s /\ ayR s mo s' mo' /\ yphi_hand h L + RR <= acredit s' /\ ayframe_post m m' sp fc' lo REST LF [] /\ rw_cells asegs m' CFGP [C4 (wz 1); C4 (wz 1)]
  /\ a0' = wz (mh_addr mh) /\ 0 < mh_addr mh /\ mh_ctx mh = CX
         /\ yleaf (yajl_alloc 1 1) (Some h) /\ hand_rep m' h mh
         /\ oshadow m' (mh_addr mh) SIZEOF_HANDLE /\ oshadow m' (mh_lexer mh) SIZEOF_LEXER
         /\ oshadow m' (mb_addr (mh_lexbuf mh)) SIZEOF_BUF /\ oshadow m' (mb_addr (mh_decbuf mh)) SIZEOF_BUF
         /\ (h_stack_blk h <> None -> oshadow m' (mh_stack mh) (h_stack_size h))
         /\ (forall b, In b (abl (yblocks mh h)) -> oshw_hi 0 (2^47) <= ab_addr b)
         /\ AYST s' (abl (yblocks mh h) ++ REST) LF m' mo' .
Definition ayalloc_stmt : Prop :=
  forall (LF : list fblock) (REST : list ablock) (CFGP CX lo L : Z) (RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s REST LF m mo ->
  rw_cells asegs m CFGP [C4 (wz 1); C4 (wz 1)] ->
  oshadow m CFGP 8 ->
  oshadow m CX 8 ->
  0 <= L ->
  amem CX 8 ->
  CFGP = CX + 32 ->
  CFGP + 8 <= alloc_ceiling ->
  (exists f, In f LF /\ snd f + 32 = CX /\ fst f = 1) ->
  (ff_live_class LF 1 < 2)%nat ->
  ayframe_pre m sp tp fc lo AY_ALLOC_STACK ->
  a0 = wz AY_CALLBACKS ->
  a1 = wz CFGP ->
  a2 = wz 0 ->
  a3 = wz CX ->
  yphi_new L + RR <= acredit s -> 0 <= RR ->
  nbig REST <= AY_NBIG_REST ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (h : yhandle) (mh : mhand),
     ayalloc_rpost sp m mo s LF REST CFGP CX lo L RR a0' fc' m' mo' s' h mh ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_ALLOC) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ayfree_rpost (sp : word) (m : mem) (mo : Model) (s : APS) (LF : list fblock) (REST : list ablock) (h : yhandle) (mh : mhand) (lo : Z) (RR : Z)
    (a0' : word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS)  : Prop :=
  SO s' = SO s /\ ayR s mo s' mo' /\ 0 + RR <= acredit s' /\ ayframe_post m m' sp fc' lo REST LF [] /\ AYST s' REST LF m' mo' .
Definition ayfree_stmt : Prop :=
  forall (LF : list fblock) (REST : list ablock) (h : yhandle) (mh : mhand) (lo : Z) (RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s (abl (yblocks mh h) ++ REST) LF m mo ->
  hand_rep m h mh ->
  oshadow m (mh_addr mh) SIZEOF_HANDLE ->
  oshadow m (mh_lexer mh) SIZEOF_LEXER ->
  oshadow m (mb_addr (mh_lexbuf mh)) SIZEOF_BUF ->
  oshadow m (mb_addr (mh_decbuf mh)) SIZEOF_BUF ->
  ayframe_pre m sp tp fc lo AY_FREE_STACK ->
  a0 = wz (mh_addr mh) ->
  yphi_hand h 0 + RR <= acredit s -> 0 <= RR ->
  nbig REST <= AY_NBIG_REST + 2 ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) ,
     ayfree_rpost sp m mo s LF REST h mh lo RR a0' fc' m' mo' s'  ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_FREE) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ayfuzz_rpost (sp : word) (m : mem) (mo : Model) (s : APS) (LF : list fblock) (REST : list ablock) (T : Z) (txt : list Z) (OT OTn lo : Z) (RR : Z)
    (a0' : word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (LK : list ablock) : Prop :=
  SO s' = SO s /\ ayR s mo s' mo' /\ 0 + RR <= acredit s' /\ ayframe_post m m' sp fc' lo REST LF [] /\ a0' = wz 0 /\ text_at m' T txt
  /\ yleaf (yLLVMFuzzerTestOneInput txt (zlength txt)) 0
  /\ LK = [] /\ AYST s' (LK ++ REST) LF m' mo' .
Definition ayfuzz_stmt : Prop :=
  forall (LF : list fblock) (REST : list ablock) (T : Z) (txt : list Z) (OT OTn lo : Z) (RR : Z) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS),
  K [] ->
  AYST s REST LF m mo ->
  text_at m T txt ->
  zlength txt < 2^26 ->
  ((exists bt, In bt REST /\ ab_addr bt <= T /\ T + zlength txt <= ab_addr bt + ab_size bt) \/ (zlength txt = 0 /\ T = AY_EMPTY)) ->
  (zlength txt = 0 \/ (oshadow m OT OTn /\ OT <= T /\ T + zlength txt <= OT + OTn /\ amem OT OTn /\ OT + OTn <= alloc_ceiling /\ (exists bt, In bt REST /\ ab_addr bt <= OT /\ OT + OTn <= ab_addr bt + ab_size bt))) ->
  (ff_live_class LF 1 = 0)%nat ->
  (ff_live_class LF 0 = 0)%nat ->
  gp = wz 0x10800 ->
  ayframe_pre m sp tp fc lo AY_FUZZ_STACK ->
  a0 = wz T ->
  a1 = wz (zlength txt) ->
  ycost (zlength txt) + RR <= acredit s -> 0 <= RR ->
  nbig REST <= AY_NBIG_REST ->
  uanchor m (usp sp) ra s0 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (LK : list ablock),
     ayfuzz_rpost sp m mo s LF REST T txt OT OTn lo RR a0' fc' m' mo' s' LK ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AY_FUZZ) fc None m (seg_rom asegs)) mo) K.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ay_pres_agree : forall REST LF SP X m m',
  ay_pres REST LF SP X m m' -> agree_on asegs (fun a => ay_client_addr REST LF SP a /\ ~ yin_ivs X a) m m'.
Proof. intros REST LF SP X m m' H a Ha [Hc Hx]. exact (H a Ha Hc Hx). Qed.
Lemma agree_ay_pres : forall REST LF SP X m m',
  agree_on asegs (fun a => ay_client_addr REST LF SP a /\ ~ yin_ivs X a) m m' -> ay_pres REST LF SP X m m'.
Proof. intros REST LF SP X m m' H a Ha Hc Hx. exact (H a Ha (conj Hc Hx)). Qed.

(* [comment removed for export] *)
Lemma ay_pres_of_munch : forall REST LF SP X W m m',
  munch W m m' -> wmono asegs m m' ->
  (forall a, 0 <= a < 2^64 -> ay_client_addr REST LF SP a -> ~ yin_ivs X a -> outside W a) ->
  ay_pres REST LF SP X m m'.
Proof.
  intros REST LF SP X W m m' MU WM HO a Ha Hc Hx. split.
  - apply MU. rewrite wa_unsigned by exact Ha. apply HO; assumption.
  - apply WM.
Qed.

(* [comment removed for export] *)
Lemma AYST_statics : forall s LB LF m mo, AYST s LB LF m mo -> ay_statics m.
Proof. intros s LB LF m mo (_ & _ & _ & _ & H). exact H. Qed.
Lemma AYST_AHK : forall s LB LF m mo, AYST s LB LF m mo -> AHK s LB LF m mo.
Proof. intros s LB LF m mo (H & _). exact H. Qed.

End AYajl.
End RC__1.
