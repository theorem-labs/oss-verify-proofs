(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 SecLazy ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C5 ECH_AStmt_C10 ECH_AStmt_C13 ECH_AStmt_C12 ECH_AStmt_C14 ECH_ALibMF ECH_ALibMid ECH_AKit ECH_AsKit
  ECH_AC1_malloc ECH_AC1_zalloc ECH_AC1_free ECH_AC1_dup ECH_AC5_small ECH_AC5_new ECH_AC5_push ECH_AC5_popfree ECH_AC10
  ECH_AC13_small ECH_AC13_ext ECH_AC13_entry ECH_AC12_addstr ECH_ARostr ECH_AC11_fail ECH_AC14_decexts_seg.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma sk_grow_le : forall c, 0 <= c -> 0 <= sk_grow c <= 2 * c /\ 5 * sk_grow c <= 8 * c.
Proof. intros c Hc. unfold sk_grow. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Definition S_ADX_FUNC : list byte := Eval vm_compute in img_cstr ADX_FUNC 64.
Definition K_ADX_FUNC : list byte := Eval vm_compute in img_slack ADX_FUNC (length S_ADX_FUNC).
Definition S_ADX_FILE : list byte := Eval vm_compute in img_cstr ADX_FILE_ECHS 64.
Definition K_ADX_FILE : list byte := Eval vm_compute in img_slack ADX_FILE_ECHS (length S_ADX_FILE).
Section RO.
  Context {HCEIL : HeapCeil}.
  Lemma R_ADX_FUNC : ROSTR ADX_FUNC S_ADX_FUNC K_ADX_FUNC.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma R_ADX_FILE : ROSTR ADX_FILE_ECHS S_ADX_FILE K_ADX_FILE.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma S_ADX_FUNC_len : Z.of_nat (length S_ADX_FUNC) = 25. Proof. reflexivity. Qed.
  Lemma S_ADX_FILE_len : Z.of_nat (length S_ADX_FILE) = 19. Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma AR_ADX_FUNC : AROSTR ADX_FUNC S_ADX_FUNC K_ADX_FUNC.
  Proof. eapply AROSTR_intro; [exact R_ADX_FUNC| unfold aglobals; cbn; tauto| vm_compute; intros X; discriminate X| vm_compute; intros X; discriminate X]. Qed.
  Lemma AR_ADX_FILE : AROSTR ADX_FILE_ECHS S_ADX_FILE K_ADX_FILE.
  Proof. eapply AROSTR_intro_hull; [exact R_ADX_FILE| unfold aglobals; cbn; do 52 right; left; reflexivity| ..];
    vm_compute; intros X; discriminate X. Qed.
End RO.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section G.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  (* [comment removed for export] *)
  Lemma amemflag_same : forall m m', MEMFLAG m 1 -> MEMFLAG m' 1 ->
    m' (wa A_mem_inited) = m (wa A_mem_inited) /\ (wview asegs m (wa A_mem_inited) <> None -> wview asegs m' (wa A_mem_inited) <> None).
  Proof.
    intros m m' (fb & [[_ (_ & _ & B1)] _] & V1 & _) (fb' & [[_ (_ & _ & B2)] (_ & _ & W2)] & V2 & _).
    cbn [cells_bytes cbytes app length cells_size csize Nat.add] in *.
    specialize (B1 0%nat ltac:(lia)). specialize (B2 0%nat ltac:(lia)). cbn [nth_error Z.of_nat] in B1, B2.
    replace (A_mem_inited + 0) with A_mem_inited in B1, B2 by lia.
    assert (ROM : seg_rom asegs (wa A_mem_inited) = Some (b8 0)) by (vm_compute; reflexivity).
    assert (E : fb = fb') by (rewrite (byte_eq_of_unsigned fb 1 V1), (byte_eq_of_unsigned fb' 1 V2); reflexivity). subst fb'.
    unfold mrd in B1, B2. split.
    - destruct (m (wa A_mem_inited)) as [x1|]; destruct (m' (wa A_mem_inited)) as [x2|].
      + injection B1 as ->. injection B2 as ->. reflexivity.
      + exfalso. rewrite ROM in B2. injection B2 as <-. vm_compute in V1. clear - V1. lia.
      + exfalso. rewrite ROM in B1. injection B1 as <-. vm_compute in V1. clear - V1. lia.
      + reflexivity.
    - intros _. specialize (W2 0 ltac:(lia)). replace (A_mem_inited + 0) with A_mem_inited in W2 by lia. exact W2.
  Qed.
  Lemma axpres_drop_memflag : forall L SP X1 X2 m m',
    MEMFLAG m 1 -> MEMFLAG m' 1 -> xpres H L SP (X1 ++ memflag_foot ++ X2) m m' -> xpres H L SP (X1 ++ X2) m m'.
  Proof.
    intros L SP X1 X2 m m' MF MF' XP a Ha [HC HX].
    destruct (Z.eq_dec a A_mem_inited) as [->|NE]; [apply amemflag_same; assumption|].
    apply XP; [exact Ha|]. split; [exact HC|]. intros K. apply rin_ivs_app in K. destruct K as [K|K]; [apply HX; apply rin_ivs_app; left; exact K|].
    apply rin_ivs_app in K. destruct K as [K|K]; [| apply HX; apply rin_ivs_app; right; exact K].
    unfold memflag_foot in K. cbn [rin_ivs fst snd] in K. lia.
  Qed.

  Hypothesis HH : asan_rt_hyps H.
  (* [comment removed for export] *)
  Lemma chain_via_xpres_off : forall LB SP X m m' cur CH,
    as_chain H m cur CH -> xpres H LB SP X m m' -> (forall fp ra, In (fp, ra) CH -> SP + 16 <= fp) ->
    Forall (fun iv : Z * Z => snd iv <= aceil \/ offchain CH (fst iv) (snd iv - fst iv)) X -> as_chain H m' cur CH.
  Proof.
    intros LB SP X m m' cur CH C XP HS FX. eapply (ah_chain_ext H HH); [exact C|].
    intros fp ra a IN Ha. pose proof (HS _ _ IN). pose proof (ah_chain_range H HH _ _ _ _ _ C IN) as (R1 & R2 & R3).
    apply XP; [acb; lia|]. split; [left; lia|].
    clear - FX Ha R1 IN. induction X as [|[l h] X IH]; [intros K; exact K|]. cbn. intros [K|K].
    - pose proof (Forall_inv FX) as F1. cbn in F1. destruct F1 as [F1|F1]; [lia|]. specialize (F1 _ _ IN). lia.
    - exact (IH (Forall_inv_tail FX) K).
  Qed.
  (* [comment removed for export] *)
  Lemma aCf0 : as_Cf H 0 = 0.
  Proof.
    pose proof (ah_costs H HH) as (_ & _ & F0 & _ & _ & SF). pose proof (F0 0 ltac:(lia)) as K1. pose proof (SF 0 0 ltac:(lia) ltac:(lia)) as K2. rewrite Z.add_0_r in K2. lia.
  Qed.
  Lemma aCm_mono : forall a b, 0 <= a <= b -> as_Cm H a <= as_Cm H b.
  Proof. intros a b Hab. exact (proj1 (proj2 (ah_costs H HH)) a b Hab). Qed.
  Lemma aCf_mono : forall a b, 0 <= a <= b -> as_Cf H a <= as_Cf H b.
  Proof. intros a b Hab. exact (proj1 (proj2 (proj2 (proj2 (ah_costs H HH)))) a b Hab). Qed.
  Lemma aCm_super : forall a b, 0 <= a -> 0 <= b -> as_Cm H a + as_Cm H b <= as_Cm H (a + b).
  Proof. intros a b Ha Hb. exact (proj1 (proj2 (proj2 (proj2 (proj2 (ah_costs H HH))))) a b Ha Hb). Qed.
  Lemma aCf_super : forall a b, 0 <= a -> 0 <= b -> as_Cf H a + as_Cf H b <= as_Cf H (a + b).
  Proof. intros a b Ha Hb. exact (proj2 (proj2 (proj2 (proj2 (proj2 (ah_costs H HH))))) a b Ha Hb). Qed.
  Lemma aCm_pos : forall a, 0 <= a -> 0 <= as_Cm H a.
  Proof. intros a Ha. exact (proj1 (ah_costs H HH) a Ha). Qed.
  Lemma aCf_pos : forall a, 0 <= a -> 0 <= as_Cf H a.
  Proof. intros a Ha. exact (proj1 (proj2 (proj2 (ah_costs H HH))) a Ha). Qed.
End G.

(* [comment removed for export] *)
Lemma errph_nonneg : forall ph, 0 <= errph_bytes ph /\ 0 <= errph_cnt ph.
Proof. intros [|c]; cbn; unfold ERRINIT_BYTES, ERRINIT_CNT; lia. Qed.
Lemma lb_bytes_perm : forall L L' : list block, Permutation L L' -> lb_bytes L = lb_bytes L'.
Proof. intros L L' P. induction P; rewrite ?lb_bytes_cons; lia. Qed.

(* [comment removed for export] *)
Definition ADX_PUSH_CM : Z := 13136.   (* [comment removed for export] *)
Definition ADX_PUSH_CF : Z := 8192.    (* [comment removed for export] *)
Definition ADX_PER_EXT : Z := 16 + ADX_PUSH_CM.
Definition xs_len (xs : option (skrep * list extrep)) : Z := match xs with None => 0 | Some (_, es) => zlength es end.
Definition xs_base (xs : option (skrep * list extrep)) : Z := match xs with None => 0 | Some _ => SK_SIZE end.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Hypothesis RAISE : araise_stmt H.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (mo : Model)
            (LIB LB : list block) (LF : list fframe) (M : libmid) (x : ctxinfo) (ee pk base len cur0 rem0 lo B : Z) (E : entrep) (bs : list byte) (pbin : bptr)
            (CH : list (Z * Z)) (j0 : list byte) (s00 : as_St H).
  Let spq : Z := bv_unsigned sp + -144.
  Hypothesis XE0 : en_exts E = 0.
  Hypothesis XO0 : en_exts_o E = None.
  Hypothesis BEL : Forall (fun b => blk_addr b + blk_size b <= lo) (blocks_ENTRY ee E).
  Hypothesis PKIN0 : pk_in base len cur0 rem0.
  Hypothesis REM1 : 1 <= rem0.
  Hypothesis REMB : rem0 <= 1499.
  Hypothesis SPK : bv_unsigned sp <= pk.
  Hypothesis PKB : pk + 24 <= B.
  Hypothesis PK8 : pk mod 8 = 0.
  Hypothesis BIN : In (pbin, base, len) LB.
  Hypothesis EIN0 : In (en_id E, ee, ENTRY_SIZE) LB.
  Hypothesis EBIN : en_id E <> pbin.
  Hypothesis OF0 : ofield LB (en_pname E) (en_pname_o E) /\ ofield LB (en_pub E) (en_pub_o E) /\ ofield LB (en_suites E) (en_suites_o E) /\ ofield LB (en_encoded E) (en_encoded_o E).
  Hypothesis BSL : zlength bs <= len.
  Hypothesis CRB : cur0 + rem0 <= base + zlength bs.
  Hypothesis LIBSUB : forall b, In b LIB -> In b LB.
  Hypothesis CX : mid_ctx M = CtxReady x.
  Hypothesis MF0 : mid_flag M = 1.
  Hypothesis IDS : forall b b', In b LIB -> In b' (blocks_ENTRY ee E) -> blk_id b <> blk_id b'.
  Hypothesis IDB : forall b, In b LIB -> blk_id b <> pbin.
  Hypothesis BY : lb_bytes (mid_errblocks M ++ LB) + errph_bytes (mid_err M) + DECEXTS_BYTES rem0 + ERRDEBUG_BYTES <= as_LIVE_MAX H.
  Hypothesis CN : Z.of_nat (length (mid_errblocks M ++ LB)) + errph_cnt (mid_err M) + (2 * rem0) / 5 + 8 <= as_LIVE_CNT_MAX H.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis BHI : B < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - DECEXTS_STACK M.
  Let LO8K : lo + 8592 <= bv_unsigned sp.
  Proof. clear - LO. unfold DECEXTS_STACK, FR_ech_decode_echconfig_exts, SKPOPFREE_STACK, EXTFREE_STACK, FR_ossl_echext_free, CFREE_STACK, AFREE_STACK, FR_sk_pop_free in LO. lia. Qed.
  Let Q5 : 5 * ((2 * rem0) / 5) <= 2 * rem0 /\ 2 * rem0 < 5 * ((2 * rem0) / 5) + 5.
  Proof. clear. pose proof (Z.div_mod (2 * rem0) 5 ltac:(lia)). pose proof (Z.mod_pos_bound (2 * rem0) 5 ltac:(lia)). lia. Qed.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis CLOSED : mid_closed_ok H M.
  Hypothesis LFB : (length LF + mid_LF M <= AFS_MAXLIVE)%nat.
  Hypothesis CHS : forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp'.
  Hypothesis PF : pf_ok (as_TR H) (PF_decexts (mid_err M)) (bv_unsigned ra) CH.
  Hypothesis OFFCH : offchain CH pk 24.
  Hypothesis CHN0 : as_chain H m0 (bv_unsigned s0) CH.
  (* [comment removed for export] *)
  Hypothesis HAL0 : DECEXTS_COST H M rem0 <= as_AL H s00.
  (* [comment removed for export] *)
  Definition ALED (s' : as_St H) (xs : option (skrep * list extrep)) (c : Z) (XB : list block) : Prop :=
    exists um uf, 0 <= um <= c + lb_bytes XB + ADX_PER_EXT * xs_len xs + xs_base xs /\ 0 <= uf <= ADX_PUSH_CF * xs_len xs
                  /\ as_AL H s' + as_Cm H um + as_Cf H uf >= as_AL H s00.

  (* [comment removed for export] *)
  Definition EW (P : Z) (xs : option (skrep * list extrep)) : entrep :=
    mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
          (en_maxname E) (en_cfgid E) P xs (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
  Lemma EW0 : EW 0 None = E.
  Proof. clear - XE0 XO0. unfold EW. destruct E; cbn in *. subst. reflexivity. Qed.
  Lemma blocks_EW : forall P xs, blocks_ENTRY ee (EW P xs) = blocks_ENTRY ee E ++ blocks_EXTS P xs.
  Proof.
    clear - XO0. intros P xs. unfold blocks_ENTRY, EW. cbn -[blocks_EXTS blocks_of app]. rewrite XO0. cbn [blocks_EXTS]. rewrite app_nil_r.
    rewrite !app_comm_cons. rewrite <- !app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition X0 : list (Z * Z) := (pk, pk + 24) :: (ee, ee + ENTRY_SIZE) :: ERR_XE ++ errph_foot (mid_err M).

  (* [comment removed for export] *)
  Definition EBof (K : skrep) (es : list extrep) : list block :=
    concat (map (fun pe => blocks_EXT (fst pe) (snd pe)) (combine (sk_elems K) es)).
  Lemma blocks_EXTS_some : forall P K es, blocks_EXTS P (Some (K, es)) = blocks_SK P K ++ EBof K es.
  Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  Definition XINV (P : Z) (xs : option (skrep * list extrep)) (c : Z) : Prop :=
    match xs with
    | None => P = 0 /\ c = 0
    | Some (K, es) => sk_comp K = 0 /\ 4 * zlength es <= c /\ (0 <= sk_cap K /\ 5 * sk_cap K <= 8 * zlength es + 20)
                      /\ 5 * zlength (EBof K es) <= 2 * c /\ lb_bytes (EBof K es) <= 12 * zlength es + c
    end.

  (* [comment removed for export] *)
  Definition dworldX (m : mem) (s' : as_St H) (errv' : word) (P : Z) (xs : option (skrep * list extrep)) (NB : list block)
             (c cur rem : Z) (XB : list block) : Prop :=
       mem_inv asegs m /\ ACONST m /\ stk asegs m lo spq /\ rw_cells asegs m spq (adx_frame j0 pk ee s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells asegs m (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m B
    /\ as_RHEAP H s' (mid_errblocks M ++ XB ++ NB ++ LB) m
    /\ LIBMID LIB m M
    /\ ENTRYobj (NB ++ LB) m ee (EW P xs) /\ ENTRY_shad m ee (EW P xs) /\ Permutation (blocks_EXTS P xs) NB /\ XINV P xs c
    /\ rw_cells asegs m pk (pk_cells cur base rem) /\ pk_in base len cur rem /\ cur0 + rem0 = cur + rem /\ 0 <= c <= rem0 - rem
    /\ bytes_at asegs m base bs /\ accessible m base len /\ accessible m pk 24 /\ stack0 m lo (bv_unsigned sp)
    /\ as_RFS H LF m
    /\ xpres H LB (bv_unsigned sp) X0 m0 m
    /\ ALED s' xs c XB.
  Definition dworld m s' errv' P xs NB cur rem : Prop := dworldX m s' errv' P xs NB (rem0 - rem) cur rem [].

  Lemma M_eq1 : mkMID 1 (mid_ctx M) (mid_err M) (mid_E M) (mid_vdso M) = M.
  Proof. clear - MF0. destruct M; cbn in *. subst. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma dworld_entry : forall m s' errv' P xs NB c cur rem XB,
    dworldX m s' errv' P xs NB c cur rem XB ->
    exists pad1 pad2 pad3 pad4, length pad1 = 6%nat /\ length pad2 = 4%nat /\ length pad3 = 6%nat /\ length pad4 = 4%nat /\
      rw_cells asegs m ee (entry_cells (EW P xs) pad1 pad2 pad3 pad4) /\ 0 < ee /\ ee + ENTRY_SIZE <= aceil /\ aapp ee ENTRY_SIZE /\ ee mod 16 = 0
      /\ 0 <= P < 2^64
      /\ 0 < pk /\ pk + 24 < 2^64 /\ 0 < base /\ base + len <= aceil /\ aapp base len /\ (pk + 24 <= base \/ base + zlength bs <= pk).
  Proof.
    intros m s' errv' P xs NB c cur rem XB (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & CB & BS & ACCB & ACCP & SK0 & RFS & XP & ALG).
    cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR.
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & HC) & EIN & O1 & O2 & O3 & O4 & XS).
    cbn [EW en_id en_exts en_exts_o] in EIN, XS.
    assert (SUBLB : forall b, In b LB -> In b (mid_errblocks M ++ XB ++ NB ++ LB)) by (intros b Hb; do 3 (apply in_or_app; right); exact Hb).
    pose proof (ah_blocks H HH _ _ _ _ HP (SUBLB _ EIN0)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
    pose proof (ah_blocks H HH _ _ _ _ HP (SUBLB _ BIN)) as (B1' & B2' & B3' & B4' & B5' & B6' & B7').
    cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7, B1', B2', B3', B4', B5', B6', B7'.
    assert (XR : 0 <= P < 2^64).
    { revert XS. unfold EXTS. destruct xs as [[K es]|]; intros XS; [| rewrite XS; lia].
      destruct XS as (XP1 & SO & _). destruct SO as (_ & _ & KIN & _). pose proof (ah_blocks H HH _ _ _ _ HP ltac:(do 2 (apply in_or_app; right); exact KIN)) as (K1 & _ & K3 & _ & K5 & _).
      cbn [blk_addr blk_size fst snd] in K1, K3, K5. unfold SK_SIZE in K3, K5. lia. }
    unfold zlength in *.
    exists pad1, pad2, pad3, pad4. unfold ENTRY_SIZE in *. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    all: clear - E2; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dworldX_blocks : forall m s' errv' P xs NB c cur rem XB,
    dworldX m s' errv' P xs NB c cur rem XB ->
    (forall b, In b (mid_errblocks M ++ XB ++ NB ++ LB) -> 0 < blk_addr b /\ AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ aapp (blk_addr b) (blk_size b)).
  Proof.
    intros m s' errv' P xs NB c cur rem XB (_ & _ & _ & _ & _ & _ & HP & _) b Hb.
    pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma dworldX_munch : forall m m1 s' errv' P xs NB c cur rem XB W q A n,
    dworldX m s' errv' P xs NB c cur rem XB -> In (q, A, n) XB ->
    munch W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo spq -> ACONST m1 ->
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= spq) \/ (A <= fst iv /\ snd iv <= A + n)) W ->
    dworldX m1 s' errv' P xs NB c cur rem XB
    /\ (forall A' cs, rw_cells asegs m A' cs -> disjoint_from W A' (Z.of_nat (cells_size cs)) -> rw_cells asegs m1 A' cs).
  Proof.
    intros m m1 s' errv' P xs NB c cur rem XB W q A n FW QIN MU WM MI1 ST1 AC1 HW.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & ACCB & ACCP & SK0 & RFS & XP0 & ALG).
    pose proof (dworldX_blocks _ _ _ _ _ _ _ _ _ _ FW) as HB. clear FW.
    unfold dworldX. cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR.
    assert (QINL : In (q, A, n) (mid_errblocks M ++ XB ++ NB ++ LB)) by (apply in_or_app; right; apply in_or_app; left; exact QIN).
    pose proof (HB _ QINL) as (Q1 & Q4 & Q5b & Q3 & Q7). cbn [blk_addr blk_size fst snd] in Q1, Q4, Q5b, Q3, Q7. unfold AIMG_TOP in Q4.
    pose proof (sh_aapp_range A n Q7 Q3) as (QS1 & QS2 & QS3). assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in QS1. unfold AHI_LO in QS3.
    pose proof (ah_nodup H HH _ _ _ HP) as ND.
    (* [comment removed for export] *)
    assert (REMX : forall b, In b (mid_errblocks M ++ XB ++ NB ++ LB) -> blk_id b <> q -> In b (as_lb_remove H q (mid_errblocks M ++ XB ++ NB ++ LB))).
    { intros b Hb NE. apply (proj2 (proj2 (proj2 (alb_remove_exact H HH _ _ _ _ ND QINL)) b)). split; [exact Hb| exact NE]. }
    assert (NBLB : forall b, In b (NB ++ LB) -> In b (as_lb_remove H q (mid_errblocks M ++ XB ++ NB ++ LB))).
    { intros b Hb. apply REMX; [do 2 (apply in_or_app; right); exact Hb|].
      intros Eq. rewrite (app_assoc (mid_errblocks M) XB) in ND. eapply (nodup_ids_app_ne (mid_errblocks M ++ XB) (NB ++ LB) (q, A, n) b ND); [apply in_or_app; right; exact QIN| exact Hb| symmetry; exact Eq]. }
    assert (XPR : forall X, xpres H (as_lb_remove H q (mid_errblocks M ++ XB ++ NB ++ LB)) (bv_unsigned sp + -144) X m m1).
    { intros X. eapply (xpres_of_munch_listed H HH); [exact HP| exact QINL| lia| exact MU| exact WM|].
      eapply Forall_impl; [| exact HW]. cbn beta. intros [u v] HK; cbn [fst snd] in HK; destruct HK as [[K1 K2]|[K1 K2]]; cbn [fst snd] in *; [left; lia| right; left; lia]. }
    assert (XPL : forall X, xpres H (NB ++ LB) (bv_unsigned sp + -144) X m m1) by (intros X; eapply (xpres_weaken H); [apply (XPR X)| lia| exact NBLB| intros a Ha; exact Ha]).
    assert (WLO : Forall (fun iv : Z * Z => snd iv <= bv_unsigned sp + -144) W).
    { eapply Forall_impl; [| exact HW]. cbn beta. intros [u v] HK; cbn [fst snd] in HK; destruct HK as [[K1 K2]|[K1 K2]]; cbn [fst snd] in *; lia. }
    assert (DJS : forall a k, bv_unsigned sp + -144 <= a -> disjoint_from W a k).
    { intros a k Ha. clear - WLO Ha. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv WLO) as K. cbn in K. split; [lia| apply IH; eapply Forall_inv_tail; exact WLO]. }
    assert (DJI : forall a k, a + k <= AIMG_TOP -> disjoint_from W a k).
    { intros a k Ha. unfold AIMG_TOP in Ha. clear - HW Ha Q4 CEIL ACEILB. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K. cbn in K. split; [lia| apply IH; eapply Forall_inv_tail; exact HW]. }
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W).
    { eapply Forall_impl; [| exact HW]. cbn beta. pose proof (aapp_not_shadowland _ _ Q7) as QNS.
      intros [u v] HK; cbn [fst snd] in HK; destruct HK as [[K1 K2]|[K1 K2]]; cbn [fst snd] in *; [right; unfold AHI_LO in *; clear - K1 CEIL ACEILB; lia| clear - K1 K2 QNS; lia]. }
    assert (SW : Forall stack0_ok W).
    { eapply Forall_impl; [| exact HW]. cbn beta. intros [u v] HK; cbn [fst snd] in HK; destruct HK as [[K1 K2]|[K1 K2]]; [apply stack0_ok_app; cbn; unfold AHI_LO; lia| eapply stack0_ok_aapp; [exact Q7| exact K1| exact K2]]. }
    assert (CW : Forall (aclient_write_ok H (mid_errblocks M ++ XB ++ NB ++ LB)) W).
    { eapply Forall_impl; [| exact HW]. cbn beta. intros [u v] HK; cbn [fst snd] in HK; destruct HK as [[K1 K2]|[K1 K2]]; [left; cbn; lia|]. right; right; left. exists (q, A, n). split; [exact QINL| cbn; lia]. }
    assert (FSW : Forall (afs_write_ok H LF) W).
    { eapply Forall_impl; [| exact HW]. cbn beta. pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4).
      pose proof (HB _ QINL) as K. pose proof (ah_blocks H HH _ _ _ _ HP QINL) as (_ & _ & _ & _ & _ & Q6 & _). cbn [blk_addr blk_size fst snd] in Q6.
      intros [u v] HK; cbn [fst snd] in HK; destruct HK as [[K1 K2]|[K1 K2]]; left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia. }
    split.
    - repeat match goal with |- _ /\ _ => split end; try assumption.
      + eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. apply DJS. lia.
      + subst tp. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. rewrite unsigned_lit by (unfold ATP; lia). apply DJI. unfold ATP, AIMG_TOP. cbn. lia.
      + eapply (ah_rauxv_frame H HH); [exact AUX| exact MU| exact WM| exact CW].
      + eapply (ah_RHEAP_frame H HH); [exact HP| exact MU| exact WM| exact CW].
      + eapply (LIBMID_xpres0 H); [exact LM| exact CX| apply XPR| |].
        * intros b Hb. apply REMX; [do 3 (apply in_or_app; right); apply LIBSUB; exact Hb|].
          intros Eq. rewrite (app_assoc (mid_errblocks M) XB) in ND. eapply (nodup_ids_app_ne (mid_errblocks M ++ XB) (NB ++ LB) (q, A, n) b ND); [apply in_or_app; right; exact QIN| apply in_or_app; right; apply LIBSUB; exact Hb| symmetry; exact Eq].
        * intros b Hb. apply REMX; [apply in_or_app; left; exact Hb|].
          intros Eq. eapply (nodup_ids_app_ne (mid_errblocks M) (XB ++ NB ++ LB) b (q, A, n) ND); [exact Hb| apply in_or_app; left; exact QIN| exact Eq].
      + eapply (ENTRYobj_frame_law H); [exact EO| intros b Hb; eapply ENTRYobj_owned_law; [exact EO| exact Hb]| apply XPL|].
        intros b Hb. pose proof (HB b ltac:(do 2 (apply in_or_app; right); eapply ENTRYobj_owned_law; [exact EO| exact Hb])) as (_ & _ & K5 & _). lia.
      + eapply (ENTRY_shad_frame_law H); [exact ESH| intros b Hb; eapply ENTRYobj_owned_law; [exact EO| exact Hb]| apply XPL|].
        intros b Hb. pose proof (HB b ltac:(do 2 (apply in_or_app; right); eapply ENTRYobj_owned_law; [exact EO| exact Hb])) as (_ & _ & K5 & _). lia.
      + eapply rw_cells_transport; [exact PK| exact MU| exact WM|]. apply DJS. clear - SPK. lia.
      + eapply (xpres_bytes_at' H); [apply XPL| exact BS| | constructor]. right; right; left. exists (pbin, base, len). split; [apply in_or_app; right; exact BIN| cbn [blk_addr blk_size fst snd]; unfold zlength in BSL; lia].
      + eapply accessible_across; [exact ACCB| exact MU| exact NSW].
      + eapply accessible_across; [exact ACCP| exact MU| exact NSW].
      + eapply stack0_transport; [exact SK0| exact MU| exact WM| exact SW].
      + eapply (ah_RFS_frame H HH); [exact RFS| exact MU| exact WM| exact FSW].
      + eapply (xpres_trans H); [exact XP0|]. eapply (xpres_weaken H); [apply (XPR X0)| lia| | intros a Ha; exact Ha].
        intros b Hb. apply REMX; [do 3 (apply in_or_app; right); exact Hb|].
        intros Eq. rewrite (app_assoc (mid_errblocks M) XB) in ND. eapply (nodup_ids_app_ne (mid_errblocks M ++ XB) (NB ++ LB) (q, A, n) b ND); [apply in_or_app; right; exact QIN| apply in_or_app; right; exact Hb| symmetry; exact Eq].
    - intros A' cs RC DJ0. eapply rw_cells_transport; [exact RC| exact MU| exact WM| exact DJ0].
  Qed.

  (* [comment removed for export] *)
  Lemma dworldX_stk : forall m m1 s' errv' P xs NB c cur rem XB W,
    dworldX m s' errv' P xs NB c cur rem XB ->
    munch W m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo spq -> ACONST m1 ->
    Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= spq) W ->
    dworldX m1 s' errv' P xs NB c cur rem XB
    /\ (forall A' cs, rw_cells asegs m A' cs -> bv_unsigned sp + -144 <= A' -> rw_cells asegs m1 A' cs)
    /\ (forall A' cs, rw_cells asegs m A' cs -> A' + Z.of_nat (cells_size cs) <= aceil -> rw_cells asegs m1 A' cs).
  Proof.
    intros m m1 s' errv' P xs NB c cur rem XB W FW MU WM MI1 ST1 AC1 HW.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & ACCB & ACCP & SK0 & RFS & XP0 & ALG).
    pose proof (dworldX_blocks _ _ _ _ _ _ _ _ _ _ FW) as HB. clear FW.
    unfold dworldX. cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR.
    assert (XPA : forall L X, (forall b, In b L -> In b (mid_errblocks M ++ XB ++ NB ++ LB)) -> xpres H L (bv_unsigned sp + -144) X m m1).
    { intros L X SUB. eapply (xpres_weaken H) with (X := X); [| apply Z.le_refl| exact SUB| intros a Ha; exact Ha].
      eapply (xpres_of_munch H _ (mid_errblocks M ++ XB ++ NB ++ LB)); [exact HH| exact HP| exact MU| exact WM|].
      eapply Forall_impl; [| exact HW]. cbn beta. intros [u v] HK. cbn [fst snd] in HK. destruct HK as [K1 K2]. left. cbn. lia. }
    assert (DJS : forall a k, bv_unsigned sp + -144 <= a -> disjoint_from W a k).
    { intros a k Ha. clear - HW Ha. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K. cbn in K. split; [lia| apply IH; eapply Forall_inv_tail; exact HW]. }
    assert (DJC : forall a k, a + k <= aceil -> disjoint_from W a k).
    { intros a k Ha. clear - HW Ha CEIL. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K. cbn in K. split; [lia| apply IH; eapply Forall_inv_tail; exact HW]. }
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W).
    { eapply Forall_impl; [| exact HW]. cbn beta. intros [u v] HK; cbn [fst snd] in HK; destruct HK as [K1 K2]; cbn [fst snd]. unfold AHI_LO; lia. }
    assert (SW : Forall stack0_ok W).
    { eapply Forall_impl; [| exact HW]. cbn beta. intros [u v] HK. cbn [fst snd] in HK. destruct HK as [K1 K2]. apply stack0_ok_app; cbn; unfold AHI_LO; lia. }
    assert (CW : Forall (aclient_write_ok H (mid_errblocks M ++ XB ++ NB ++ LB)) W).
    { eapply Forall_impl; [| exact HW]. cbn beta. intros [u v] HK. cbn [fst snd] in HK. destruct HK as [K1 K2]. left; cbn; lia. }
    assert (FSW : Forall (afs_write_ok H LF) W).
    { eapply Forall_impl; [| exact HW]. cbn beta. pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4).
      intros [u v] HK; cbn [fst snd] in HK; destruct HK as [K1 K2]; left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia. }
    split; [| split].
    - repeat match goal with |- _ /\ _ => split end; try assumption.
      + eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. apply DJS. lia.
      + subst tp. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. rewrite unsigned_lit by (unfold ATP; lia). apply DJC. unfold ATP. cbn. unfold AIMG_TOP in *. lia.
      + eapply (ah_rauxv_frame H HH); [exact AUX| exact MU| exact WM| exact CW].
      + eapply (ah_RHEAP_frame H HH); [exact HP| exact MU| exact WM| exact CW].
      + eapply (LIBMID_xpres0 H) with (LBx := mid_errblocks M ++ XB ++ NB ++ LB); [exact LM| exact CX| apply XPA; intros b Hb; exact Hb| intros b Hb; do 3 (apply in_or_app; right); apply LIBSUB; exact Hb| intros b Hb; apply in_or_app; left; exact Hb].
      + eapply (ENTRYobj_frame_law H); [exact EO| intros b Hb; eapply ENTRYobj_owned_law; [exact EO| exact Hb]| apply XPA; intros b Hb; do 2 (apply in_or_app; right); exact Hb|].
        intros b Hb. pose proof (HB b ltac:(do 2 (apply in_or_app; right); eapply ENTRYobj_owned_law; [exact EO| exact Hb])) as (_ & _ & K5 & _). lia.
      + eapply (ENTRY_shad_frame_law H); [exact ESH| intros b Hb; eapply ENTRYobj_owned_law; [exact EO| exact Hb]| apply XPA; intros b Hb; do 2 (apply in_or_app; right); exact Hb|].
        intros b Hb. pose proof (HB b ltac:(do 2 (apply in_or_app; right); eapply ENTRYobj_owned_law; [exact EO| exact Hb])) as (_ & _ & K5 & _). lia.
      + eapply rw_cells_transport; [exact PK| exact MU| exact WM|]. apply DJS. clear - SPK. lia.
      + eapply bytes_at_transport; [exact BS| exact MU|]. apply DJC. pose proof (HB _ ltac:(do 3 (apply in_or_app; right); exact BIN)) as (_ & _ & K5 & _). cbn [blk_addr blk_size fst snd] in K5. unfold zlength in BSL. lia.
      + eapply accessible_across; [exact ACCB| exact MU| exact NSW].
      + eapply accessible_across; [exact ACCP| exact MU| exact NSW].
      + eapply stack0_transport; [exact SK0| exact MU| exact WM| exact SW].
      + eapply (ah_RFS_frame H HH); [exact RFS| exact MU| exact WM| exact FSW].
      + eapply (xpres_trans H); [exact XP0|]. eapply (xpres_weaken H); [apply (XPA LB X0); intros b Hb; do 3 (apply in_or_app; right); exact Hb| lia| intros b Hb; exact Hb| intros a Ha; exact Ha].
    - intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply DJS. exact HA.
    - intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply DJC. exact HA.
  Qed.

  (* [comment removed for export] *)
  Lemma errph_foot_low : forall m s' L,
    LIBMID LIB m M -> as_RHEAP H s' L m -> (forall b, In b LIB -> In b L) ->
    Forall (fun iv : Z * Z => snd iv <= aceil) (errph_foot (mid_err M)).
  Proof.
    intros m s' L LM HP SUB. pose proof LM as (_ & _ & _ & EPm & _). rewrite CX in EPm. cbn [ERRPH_mid] in EPm.
    destruct (mid_err M) as [|c0]; cbn [errph_foot]; [constructor|]. cbn [ERRPH] in EPm. destruct EPm as [_ EC].
    pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ I5)) as (_ & _ & _ & _ & B5 & _). constructor; [cbn [fst snd]; rewrite <- Z5; exact B5| constructor].
  Qed.

  (* [comment removed for export] *)
  Lemma dworldX_chain : forall m s' errv' P xs NB c cur rem XB,
    dworldX m s' errv' P xs NB c cur rem XB -> as_chain H m (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH).
  Proof.
    intros m s' errv' P xs NB c cur rem XB FW.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & ACCB & ACCP & SK0 & RFS & XP0 & ALG).
    cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    pose proof (ah_blocks H HH _ _ _ _ HP ltac:(do 3 (apply in_or_app; right); exact EIN0)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E5.
    assert (C0 : as_chain H m (bv_unsigned s0) CH).
    { eapply (chain_via_xpres_off H HH); [exact CHN0| exact XP0| exact CHS|].
      unfold X0. constructor; [right; cbn [fst snd]; replace (pk + 24 - pk) with 24 by lia; exact OFFCH|].
      constructor; [left; cbn [fst snd]; exact E5|].
      apply Forall_app. split; [| eapply Forall_impl; [| eapply errph_foot_low; [exact LM| exact HP| intros b Hb; do 3 (apply in_or_app; right); apply LIBSUB; exact Hb]]; cbn beta; intros iv K; left; exact K].
      unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
        A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      pose proof ACEILB as AB. unfold AIMG_TOP in AB. cbn [app]. repeat (apply Forall_cons; [left; cbn; clear - AB; lia|]). apply Forall_nil. }
    eapply (ah_chain_cons H HH); [exact C0| lia| lia| exact SPA| clear - CEIL LO8K; lia| lia|].
    unfold adx_frame in FR.
    apply (proj1 (rw_cells_app asegs _ _ [C8 (wz ADX_FILE_ECHS); C8 (wz ADX_FILE_PKT); C8 (wz (ee + 56)); C8 (wz 0); C8 (wz 0);
                                            C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _)) in FR.
    destruct FR as [_ FR2]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ] in FR2.
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -144 + 128) by lia. rewrite !Z_to_bv_bv_unsigned. exact FR2.
  Qed.

  (* [comment removed for export] *)
  Lemma dworldX_alloc : forall m m' s' s'' errv' errv'' P xs NB c cur rem XB p A n,
    dworldX m s' errv' P xs NB c cur rem XB ->
    mem_inv asegs m' -> ACONST m' -> stk asegs m' lo spq ->
    rw_cells asegs m' (errno_addr tp) [C4 errv''] -> as_rauxv_ok H m' B ->
    xpres H (mid_errblocks M ++ XB ++ NB ++ LB) spq memflag_foot m m' ->
    as_RHEAP H s'' ((p, A, n) :: mid_errblocks M ++ XB ++ NB ++ LB) m' -> MEMFLAG m' 1 -> 0 <= n ->
    as_AL H s'' >= as_AL H s' - as_Cm H n ->
    dworldX m' s'' errv'' P xs NB c cur rem ((p, A, n) :: XB)
    /\ (forall b A' cs, In b (XB ++ NB ++ LB) -> rw_cells asegs m A' cs -> blk_addr b <= A' -> A' + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b ->
        rw_cells asegs m' A' cs)
    /\ (forall b A' k, In b (XB ++ NB ++ LB) -> addressable m A' k -> blk_addr b <= A' -> A' + k <= blk_addr b + blk_size b -> addressable m' A' k)
    /\ (forall b A' k, In b (XB ++ NB ++ LB) -> accessible m A' k -> blk_addr b <= A' -> A' + k <= blk_addr b + blk_size b -> 0 <= k -> accessible m' A' k).
  Proof.
    intros m m' s' s'' errv' errv'' P xs NB c cur rem XB p A n FW MI' AC' ST' ERR' AUX' XP HP' MF' N0 AL'.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & ACCB & ACCP & SK0 & RFS & XP0 & ALG).
    pose proof (dworldX_blocks _ _ _ _ _ _ _ _ _ _ FW) as HB. clear FW.
    unfold dworldX. cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. pose proof BSL as BSL'. unfold zlength in BSL'.
    pose proof LM as (_ & MF & _). rewrite MF0 in MF.
    set (Lp := mid_errblocks M ++ XB ++ NB ++ LB) in *.
    assert (SUBNL : forall b, In b (NB ++ LB) -> In b Lp) by (intros b Hb; subst Lp; do 2 (apply in_or_app; right); exact Hb).
    assert (SUBX : forall b, In b (XB ++ NB ++ LB) -> In b Lp) by (intros b Hb; subst Lp; apply in_or_app; right; exact Hb).
    assert (XPn : xpres H Lp (bv_unsigned sp + -144) [] m m').
    { eapply (axpres_drop_memflag H Lp _ [] []); [exact MF| exact MF'| cbn [app]; exact XP]. }
    assert (XPL : forall X, xpres H (NB ++ LB) (bv_unsigned sp + -144) X m m').
    { intros X. eapply (xpres_weaken H); [exact XPn| lia| exact SUBNL| intros a Ha; destruct Ha]. }
    assert (MFW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) memflag_foot).
    { unfold memflag_foot, A_mem_inited. constructor; [cbn; unfold ALOWSH_LO; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    assert (MFT : Forall (fun iv : Z * Z => snd iv <= ATLS_PRIV_LO) memflag_foot).
    { unfold memflag_foot, A_mem_inited, ATLS_PRIV_LO, ATP. constructor; [cbn; lia| constructor]. }
    assert (MF0k : Forall stack0_ok memflag_foot).
    { unfold memflag_foot, A_mem_inited. constructor; [| constructor]. unfold stack0_ok. cbn. unfold sh. rewrite ASHADOW_BASE_val. pose proof ACEILB. unfold AIMG_TOP in *. Z.div_mod_to_equations. lia. }
    split; [| split; [| split]].
    - repeat match goal with |- _ /\ _ => split end; try assumption.
      + eapply (xpres_rw_cells' H); [exact XP| exact FR| left; lia|]. unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor].
      + eapply (HHx_rheap_perm H HHx); [exact HP'|]. subst Lp. apply Permutation_middle.
      + rewrite <- M_eq1. eapply (LIBMID_mf H HH s' m LIB Lp (bv_unsigned sp + -144)); [exact HP| exact LM| exact CX| exact XP| intros b Hb; apply SUBNL; apply in_or_app; right; apply LIBSUB; exact Hb| intros b Hb; subst Lp; apply in_or_app; left; exact Hb| exact MF'].
      + eapply (ENTRYobj_frame_law H); [exact EO| intros b Hb; eapply ENTRYobj_owned_law; [exact EO| exact Hb]| apply XPL|].
        intros b Hb. pose proof (HB b (SUBNL _ ltac:(eapply ENTRYobj_owned_law; [exact EO| exact Hb]))) as (_ & _ & K5 & _). lia.
      + eapply (ENTRY_shad_frame_law H); [exact ESH| intros b Hb; eapply ENTRYobj_owned_law; [exact EO| exact Hb]| apply XPL|].
        intros b Hb. pose proof (HB b (SUBNL _ ltac:(eapply ENTRYobj_owned_law; [exact EO| exact Hb]))) as (_ & _ & K5 & _). lia.
      + eapply (xpres_rw_cells' H); [exact XP| exact PK| left; clear - SPK; lia|]. unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor].
      + eapply (xpres_bytes_at' H); [apply (XPL [])| exact BS| | constructor]. right; right; left. exists (pbin, base, len). split; [apply in_or_app; right; exact BIN| cbn [blk_addr blk_size fst snd]; lia].
      + eapply (ashobj_accessible_xpres_sub H HH) with (SP := bv_unsigned sp + -144) (X := memflag_foot); [exact HP| intros b Hb; exact Hb| clear - CEIL LO8K; lia| | exact ACCB| exact XP| exact MFW].
        left. exists (pbin, base, len). split; [apply SUBNL; apply in_or_app; right; exact BIN| cbn [blk_addr blk_size fst snd]; lia].
      + eapply (ashobj_accessible_xpres_sub H HH) with (SP := bv_unsigned sp + -144) (X := memflag_foot); [exact HP| intros b Hb; exact Hb| clear - CEIL LO8K; lia| | exact ACCP| exact XP| exact MFW].
        right; right. clear - SPK. lia.
      + eapply (stack0_xpres H); [exact XP| exact SK0| exact MF0k].
      + eapply (RFS_via_xpres H HH); [exact RFS| exact XP| exact MFT].
      + eapply (xpres_trans H); [exact XP0|]. eapply (xpres_weaken H); [exact XPn| clear - SPR; lia| intros b Hb; subst Lp; do 3 (apply in_or_app; right); exact Hb| intros a Ha; destruct Ha].
      + destruct ALG as (um & uf & U1 & U2 & U3). exists (um + n), uf. rewrite lb_bytes_cons. cbn [blk_size snd].
        pose proof (aCm_super H HH um n ltac:(lia) N0). split; [lia|]. split; [exact U2|]. lia.
    - intros b A' cs Hb RC H1 H2. eapply (xpres_rw_cells' H); [exact XP| exact RC| | unfold memflag_foot, A_mem_inited; constructor; [cbn| constructor]].
      + right; right; left. exists b. split; [apply SUBX; exact Hb| lia].
      + pose proof (HB _ (SUBX _ Hb)) as (_ & K4 & _). unfold AIMG_TOP in K4. lia.
    - intros b A' k Hb AD H1 H2. pose proof (HB _ (SUBX _ Hb)) as (K1 & K4 & K5 & K3 & K7).
      eapply (ashobj_addressable_xpres H HH) with (SP := bv_unsigned sp + -144) (X := memflag_foot); [exact HP| intros b0 Hb0; exact Hb0| clear - CEIL LO8K; lia| | | exact AD| exact XP| exact MFW].
      + left. exists b. split; [apply SUBX; exact Hb| lia].
      + pose proof (aapp_bounds _ _ K7 K3). lia.
    - intros b A' k Hb ACC H1 H2 Hk. eapply (ashobj_accessible_xpres_sub H HH) with (SP := bv_unsigned sp + -144) (X := memflag_foot); [exact HP| intros b0 Hb0; exact Hb0| clear - CEIL LO8K; lia| | exact ACC| exact XP| exact MFW].
      left. exists b. split; [apply SUBX; exact Hb| lia].
  Qed.

  (* [comment removed for export] *)
  Definition avoids (X : list (Z * Z)) (a n : Z) : Prop := Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) X.
  Definition shavoids (X : list (Z * Z)) (a n : Z) : Prop := Forall (fun iv : Z * Z => sh a + nsh n <= fst iv \/ snd iv <= sh a) X.
  Lemma avoids_sub : forall X a n a' n', avoids X a n -> a <= a' -> a' + n' <= a + n -> avoids X a' n'.
  Proof. clear. intros X a n a' n' AV H1 H2. unfold avoids in *. eapply Forall_impl; [| exact AV]. cbn beta. intros [u v] K. cbn [fst snd] in *. lia. Qed.
  Lemma avoids_app : forall X Y a n, avoids X a n -> avoids Y a n -> avoids (X ++ Y) a n.
  Proof. clear. intros X Y a n AX AY. unfold avoids. apply Forall_app. split; assumption. Qed.
  Lemma shavoids_app : forall X Y a n, shavoids X a n -> shavoids Y a n -> shavoids (X ++ Y) a n.
  Proof. clear. intros X Y a n AX AY. unfold shavoids. apply Forall_app. split; assumption. Qed.
  Lemma avoids_memflag : forall a n, AIMG_TOP <= a -> avoids memflag_foot a n.
  Proof. clear. intros a n Ha. unfold avoids, memflag_foot, A_mem_inited, AIMG_TOP in *. constructor; [cbn; lia| constructor]. Qed.
  Lemma shavoids_memflag : forall a n, aapp a n -> 0 <= n -> shavoids memflag_foot a n.
  Proof. clear. intros a n AP Hn. unfold shavoids. exact (memflag_below_sh _ _ AP Hn). Qed.

  Lemma combine_app1 {X Y} : forall (l1 : list X) (l2 : list Y) a b,
    length l1 = length l2 -> combine (l1 ++ [a]) (l2 ++ [b]) = combine l1 l2 ++ [(a, b)].
  Proof.
    clear. induction l1 as [|u l1 IH]; intros [|v l2] a b L; cbn in L |- *; try discriminate; [reflexivity|].
    rewrite IH by lia. reflexivity.
  Qed.
  Lemma EBof_push : forall K es p X d c did,
    length es = length (sk_elems K) -> EBof (sk_after_push K p d c did) (es ++ [X]) = EBof K es ++ blocks_EXT p X.
  Proof.
    clear. intros K es p X d c did L. unfold EBof, sk_after_push. cbn [sk_elems]. rewrite combine_app1 by (symmetry; exact L).
    rewrite map_app, concat_app. cbn [map concat fst snd]. rewrite app_nil_r. reflexivity.
  Qed.
  Lemma SK_foot_avoids : forall P K a n,
    (forall b, In b (blocks_SK P K) -> a + n <= blk_addr b \/ blk_addr b + blk_size b <= a) -> avoids (SK_foot P K) a n.
  Proof.
    clear. intros P K a n HB. unfold avoids, SK_foot. unfold blocks_SK in HB.
    constructor; [pose proof (HB _ ltac:(left; reflexivity)) as K1; cbn [blk_addr blk_size fst snd] in K1; cbn; lia|].
    destruct (sk_cap K =? 0); [constructor|]. constructor; [| constructor].
    pose proof (HB _ ltac:(right; left; reflexivity)) as K2. cbn [blk_addr blk_size fst snd] in K2. cbn. lia.
  Qed.
  Lemma SK_foot_rin : forall P K a, rin_ivs (SK_foot P K) a -> exists b, In b (blocks_SK P K) /\ blk_addr b <= a < blk_addr b + blk_size b.
  Proof.
    clear. intros P K a Ha. unfold SK_foot in Ha. unfold blocks_SK. cbn [rin_ivs fst snd] in Ha.
    destruct Ha as [Ha|Ha]; [exists (sk_id K, P, SK_SIZE); split; [left; reflexivity| cbn; lia]|].
    destruct (sk_cap K =? 0); cbn [rin_ivs fst snd] in Ha; [destruct Ha|]. destruct Ha as [Ha|[]].
    exists (sk_did K, sk_data K, 8 * sk_cap K). split; [right; left; reflexivity| cbn; lia].
  Qed.
  Lemma ASK_foot_rin : forall P K a, rin_ivs (ASK_foot P K) a ->
    (exists b, In b (blocks_SK P K) /\ blk_addr b <= a < blk_addr b + blk_size b) \/ (sk_cap K <> 0 /\ sh (sk_data K) <= a < sh (sk_data K) + nsh (8 * sk_cap K)).
  Proof.
    clear. intros P K a Ha. unfold ASK_foot in Ha. apply rin_ivs_app in Ha. destruct Ha as [Ha|Ha]; [left; exact (SK_foot_rin _ _ _ Ha)| right].
    destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; cbn [rin_ivs fst snd] in Ha; [destruct Ha|]. destruct Ha as [Ha|[]]. split; [exact NE| exact Ha].
  Qed.
  (* [comment removed for export] *)
  Lemma ASK_foot_app : forall P K a n,
    aapp a n -> 0 <= n -> a mod 8 = 0 -> 0 <= sk_cap K ->
    (forall b, In b (blocks_SK P K) -> aapp (blk_addr b) (blk_size b) /\ blk_addr b mod 8 = 0 /\
                                     (a + n + 16 <= blk_addr b \/ blk_addr b + blk_size b + 16 <= a)) ->
    avoids (ASK_foot P K) a n /\ shavoids (ASK_foot P K) a n.
  Proof.
    clear. intros P K a n AP Hn A8 C0 HB. unfold ASK_foot, avoids, shavoids.
    assert (H1 := HB _ ltac:(unfold blocks_SK; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H1. destruct H1 as (AP1 & M1 & D1).
    split; apply Forall_app; split.
    - apply SK_foot_avoids. intros b Hb. pose proof (HB _ Hb) as (_ & _ & D). lia.
    - destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor]. cbn [fst snd].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as (AP2 & M2 & D2).
      pose proof (app_vs_sh a n (sk_data K) (8 * sk_cap K) AP Hn AP2 ltac:(lia)). lia.
    - unfold SK_foot. constructor; [cbn [fst snd]; pose proof (sh_vs_app a n P SK_SIZE AP Hn AP1 ltac:(unfold SK_SIZE; lia)); lia|].
      destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor]. cbn [fst snd].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as (AP2 & M2 & D2).
      pose proof (sh_vs_app a n (sk_data K) (8 * sk_cap K) AP Hn AP2 ltac:(lia)). lia.
    - destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor]. cbn [fst snd].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as (AP2 & M2 & D2).
      exact (sh_disjoint_blocks a n (sk_data K) (8 * sk_cap K) A8 M2 Hn ltac:(lia) D2).
  Qed.
  (* [comment removed for export] *)
  Lemma ASK_foot_stack : forall P K a n,
    aceil <= a -> 0 <= sk_cap K -> (forall b, In b (blocks_SK P K) -> aapp (blk_addr b) (blk_size b)) -> avoids (ASK_foot P K) a n.
  Proof.
    clear. intros P K a n Ha C0 HB. unfold ASK_foot, avoids. apply Forall_app. split.
    - apply SK_foot_avoids. intros b Hb. pose proof (HB _ Hb) as APb.
      assert (H1 := HB _ ltac:(unfold blocks_SK; left; reflexivity)). cbn [blk_addr blk_size] in H1.
      destruct b as [[q A0] n0]. cbn [blk_addr blk_size fst snd] in *. unfold blocks_SK in Hb.
      destruct Hb as [Hb|Hb]; [injection Hb as <- <- <-; pose proof (aapp_below_aceil _ _ APb); lia|].
      destruct (sk_cap K =? 0); [destruct Hb|]. destruct Hb as [Hb|[]]. injection Hb as <- <- <-. pose proof (aapp_below_aceil _ _ APb). lia.
    - destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor]. cbn [fst snd].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2.
      acb. pose proof (sh_aapp_range _ _ H2 ltac:(lia)) as (S1 & S2 & S3). unfold AHI_LO in S3. right. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ASK_foot_stack_sh : forall P K a n,
    aceil <= a -> 0 <= n -> a + n <= AAPP_HI -> 0 <= sk_cap K ->
    (forall b, In b (blocks_SK P K) -> aapp (blk_addr b) (blk_size b) /\ blk_addr b mod 8 = 0 /\ 0 <= blk_size b) -> shavoids (ASK_foot P K) a n.
  Proof.
    clear. intros P K a n Ha Hn Htop C0 HB. unfold ASK_foot, shavoids. acb. apply Forall_app. split.
    - unfold SK_foot. assert (H1 := HB _ ltac:(unfold blocks_SK; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H1. destruct H1 as (AP1 & M1 & _).
      constructor; [cbn [fst snd]; exact (aapp_disjoint_sh P SK_SIZE a n AP1 ltac:(lia) Htop Hn)|].
      destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor]. cbn [fst snd].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as (AP2 & M2 & _).
      exact (aapp_disjoint_sh (sk_data K) (8 * sk_cap K) a n AP2 ltac:(lia) Htop Hn).
    - destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor]. cbn [fst snd].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as (AP2 & M2 & _).
      right. pose proof (aapp_below_aceil _ _ AP2). unfold sh, nsh. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma perm_split_disjoint : forall s L L1 L2 m b1 b2,
    as_RHEAP H s L m -> Permutation L (L1 ++ L2) -> In b1 L1 -> In b2 L2 ->
    blk_addr b1 + blk_size b1 + 16 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 + 16 <= blk_addr b1.
  Proof.
    intros s L L1 L2 m b1 b2 HP PL H1 H2.
    pose proof (Permutation_NoDup (Permutation_map blk_id PL) (ah_nodup H HH _ _ _ HP)) as ND.
    eapply (ah_disj H HH); [exact HP| | | exact (nodup_ids_app_ne _ _ _ _ ND H1 H2)].
    - eapply Permutation_in; [apply Permutation_sym; exact PL| apply in_or_app; left; exact H1].
    - eapply Permutation_in; [apply Permutation_sym; exact PL| apply in_or_app; right; exact H2].
  Qed.
  (* [comment removed for export] *)
  Lemma skpush_perm : forall K K' P p d c did (Lmid XB EB LB0 LB' NB : list block),
    K' = sk_after_push K p d c did -> skpush_lb K K' (Lmid ++ XB ++ NB ++ LB0) LB' ->
    Permutation (blocks_SK P K ++ EB) NB -> 0 <= sk_num K ->
    Permutation LB' (blocks_SK P K' ++ (Lmid ++ XB ++ EB ++ LB0))
    /\ (sk_cap K' = sk_cap K \/ (sk_cap K = 0 /\ sk_cap K' = 4) \/ (sk_cap K' = sk_grow (sk_cap K) /\ sk_num K = sk_cap K /\ 4 <= sk_cap K)).
  Proof.
    clear. intros K K' P p d c did Lmid XB EB LB0 LB' NB KEQ PLB PB NN.
    assert (IDK : sk_id K' = sk_id K) by (rewrite KEQ; reflexivity).
    assert (PR : Permutation (Lmid ++ XB ++ NB ++ LB0) (NB ++ (Lmid ++ XB ++ LB0))).
    { rewrite (app_assoc Lmid XB). etransitivity; [apply Permutation_app_swap_app|]. rewrite <- app_assoc. apply Permutation_refl. }
    destruct PLB as [(N1 & C1 & D1 & I1 & ->)|[(C0 & C4 & ->)|(C4 & NC & CG & PG)]].
    - split; [| left; exact C1].
      assert (BK : blocks_SK P K' = blocks_SK P K) by (unfold blocks_SK; rewrite IDK, C1, D1, I1; reflexivity). rewrite BK.
      etransitivity; [exact PR|]. etransitivity; [apply Permutation_app_tail; apply Permutation_sym; exact PB|].
      rewrite <- !app_assoc. apply Permutation_app_head. rewrite !(app_assoc Lmid XB). apply Permutation_app_swap_app.
    - split; [| right; left; split; [exact C0| exact C4]].
      assert (BK : blocks_SK P K = [(sk_id K, P, SK_SIZE)]) by (unfold blocks_SK; rewrite C0; reflexivity).
      assert (BK' : blocks_SK P K' = [(sk_id K, P, SK_SIZE); (sk_did K', sk_data K', 32)]) by (unfold blocks_SK; rewrite IDK, C4; reflexivity).
      rewrite BK in PB. rewrite BK'. cbn [app] in PB |- *.
      etransitivity; [apply perm_skip; exact PR|]. etransitivity; [apply perm_skip; apply Permutation_app_tail; apply Permutation_sym; exact PB|]. cbn [app].
      etransitivity; [apply perm_swap|]. apply perm_skip. apply perm_skip.
      rewrite !(app_assoc Lmid XB). apply Permutation_app_swap_app.
    - split; [| right; right; split; [exact CG| split; [exact NC| exact C4]]].
      assert (CNZ : (sk_cap K =? 0) = false) by (apply Z.eqb_neq; lia).
      assert (GP : 1 <= sk_grow (sk_cap K)) by (unfold sk_grow; apply Z.div_le_lower_bound; lia).
      assert (CNZ' : (sk_cap K' =? 0) = false) by (apply Z.eqb_neq; lia).
      assert (BK : blocks_SK P K = [(sk_id K, P, SK_SIZE); (sk_did K, sk_data K, 8 * sk_cap K)]) by (unfold blocks_SK; rewrite CNZ; reflexivity).
      assert (BK' : blocks_SK P K' = [(sk_id K, P, SK_SIZE); (sk_did K', sk_data K', 8 * sk_cap K')]) by (unfold blocks_SK; rewrite IDK, CNZ'; reflexivity).
      rewrite BK in PB. rewrite BK'. cbn [app] in PB |- *.
      set (D := (sk_did K, sk_data K, 8 * sk_cap K)) in *. set (D' := (sk_did K', sk_data K', 8 * sk_cap K')) in *. set (S := (sk_id K, P, SK_SIZE)) in *.
      apply (@Permutation_cons_inv _ _ _ D).
      etransitivity; [exact PG|]. etransitivity; [apply perm_skip; exact PR|].
      etransitivity; [apply perm_skip; apply Permutation_app_tail; apply Permutation_sym; exact PB|]. cbn [app].
      etransitivity; [apply perm_skip; apply perm_swap|]. etransitivity; [apply perm_swap|]. apply perm_skip.
      etransitivity; [apply perm_swap|]. apply perm_skip. apply perm_skip.
      rewrite !(app_assoc Lmid XB). apply Permutation_app_swap_app.
  Qed.
  Lemma blocks_SK_facts : forall P K, 0 <= sk_cap K ->
    lb_bytes (blocks_SK P K) <= SK_SIZE + 8 * sk_cap K /\ Z.of_nat (length (blocks_SK P K)) <= 2 /\ 1 <= Z.of_nat (length (blocks_SK P K))
    /\ (sk_cap K = 0 -> lb_bytes (blocks_SK P K) = SK_SIZE).
  Proof.
    clear. intros P K C0. unfold blocks_SK. destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE];
      rewrite ?lb_bytes_cons; cbn [blk_size snd length lb_bytes fold_right app]; unfold SK_SIZE; lia.
  Qed.
  Lemma SKobj_relist : forall L L' m a K, SKobj L m a K -> (forall b, In b (blocks_SK a K) -> In b L') -> SKobj L' m a K.
  Proof.
    clear. intros L L' m a K (HC & POS & HIN & NC & CAP & SRT & EL & DAT) KEEP. unfold SKobj.
    split; [exact HC|]. split; [exact POS|]. split; [apply KEEP; left; reflexivity|]. split; [exact NC|]. split; [exact CAP|]. split; [exact SRT|]. split; [exact EL|].
    destruct DAT as [D0|(D1 & D2 & D3 & D4 & AR & JK)]; [left; exact D0| right].
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [| split; [exact AR| exact JK]].
    apply KEEP. unfold blocks_SK. replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. left. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma EXTobj_frameX : forall L0 SP X m m' p E,
    EXTobj L0 m p E -> xpres H L0 SP X m m' -> avoids X p EXT_SIZE -> EXTobj L0 m' p E.
  Proof.
    clear. intros L0 SP X m m' p E ((pad & PL & HC) & HIN & OF) XP A1.
    split; [| split; [exact HIN| exact OF]]. exists pad. split; [exact PL|].
    eapply (xpres_rw_cells' H); [exact XP| exact HC| |].
    - right; right; left. exists (ex_id E, p, EXT_SIZE). split; [exact HIN|]. unfold ext_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold EXT_SIZE. lia.
    - unfold ext_cells. cbn [cells_size csize Nat.add]. exact A1.
  Qed.
  Lemma EXTs_frameX : forall L0 SP X m m' ps es,
    Forall2 (fun p E => EXTobj L0 m p E) ps es -> xpres H L0 SP X m m' ->
    (forall b, In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))) -> avoids X (blk_addr b) (blk_size b)) ->
    Forall2 (fun p E => EXTobj L0 m' p E) ps es.
  Proof.
    clear. intros L0 SP X m m' ps es F2. induction F2 as [|p E ps' es' HE F IH]; intros XP K; [constructor|].
    cbn [concat map combine fst snd] in K. constructor.
    - eapply EXTobj_frameX; [exact HE| exact XP|]. apply (K (ex_id E, p, EXT_SIZE)). apply in_or_app. left. left. reflexivity.
    - apply IH; [exact XP|]. intros b Hb. apply K. apply in_or_app. right. exact Hb.
  Qed.
  Lemma oshad_xpresX : forall LB2 m m' SP X P o,
    (match o with None => True | Some (id, n) => In (id, P, n) LB2 /\ avoids X P n /\ shavoids X P n end) ->
    oshad m P o -> xpres H LB2 SP X m m' -> oshad m' P o.
  Proof.
    clear. intros LB2 m m' SP X P [[id n]|] K OSH XP; [| exact I]. cbn [oshad] in *. destruct K as (IN & AV & SAV). destruct OSH as (TOP & SH & bs & CB).
    split; [exact TOP|]. split; [eapply (addressable_xpres_blkX H); [exact IN| exact TOP| exact SH| exact XP| exact SAV]|].
    exists bs. eapply (xpres_rw_cells' H); [exact XP| exact CB| |].
    - right; right; left. exists (id, P, n). split; [exact IN|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. pose proof SH as [Hn _]. lia.
    - pose proof SH as [Hn _]. eapply avoids_sub; [exact AV| lia| cbn [cells_size csize Nat.add]; lia].
  Qed.
  Lemma EXT_shad_xpresX : forall LB2 m m' SP X p E,
    In (ex_id E, p, EXT_SIZE) LB2 -> shavoids X p EXT_SIZE ->
    (match ex_val_o E with None => True | Some (id, n) => In (id, ex_val E, n) LB2 /\ avoids X (ex_val E) n /\ shavoids X (ex_val E) n end) ->
    EXT_shad m p E -> xpres H LB2 SP X m m' -> EXT_shad m' p E.
  Proof.
    clear. intros LB2 m m' SP X p E IN SAV KV (TOP & SH & OSH) XP. split; [exact TOP|]. split.
    - eapply (addressable_xpres_blkX H); [exact IN| exact TOP| exact SH| exact XP| exact SAV].
    - eapply oshad_xpresX; [exact KV| exact OSH| exact XP].
  Qed.
  Lemma EXTs_shad_xpresX : forall LB2 m m' SP X ps es,
    Forall2 (fun p E => EXT_shad m p E) ps es -> xpres H LB2 SP X m m' ->
    (forall b, In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))) -> In b LB2 /\ avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) ->
    Forall2 (fun p E => EXT_shad m' p E) ps es.
  Proof.
    clear. intros LB2 m m' SP X ps es F2. induction F2 as [|p E ps' es' HE F IH]; intros XP K; [constructor|].
    cbn [concat map combine fst snd] in K. constructor.
    - eapply EXT_shad_xpresX; [| | | exact HE| exact XP].
      + apply (proj1 (K (ex_id E, p, EXT_SIZE) ltac:(apply in_or_app; left; left; reflexivity))).
      + apply (proj2 (proj2 (K (ex_id E, p, EXT_SIZE) ltac:(apply in_or_app; left; left; reflexivity)))).
      + unfold blocks_EXT, blocks_of in K. destruct (ex_val_o E) as [[id n]|]; [| exact I].
        exact (K (id, ex_val E, n) ltac:(apply in_or_app; left; right; left; reflexivity)).
    - apply IH; [exact XP|]. intros b Hb. apply K. apply in_or_app. right. exact Hb.
  Qed.
  (* [comment removed for export] *)
  Lemma accessible_xpresX : forall s L m2 LB2 m m' SP X A n,
    as_RHEAP H s L m2 -> (forall b, In b LB2 -> In b L) -> aceil <= SP -> ashobj H LB2 SP A n -> accessible m A n -> xpres H LB2 SP X m m' ->
    Forall (fun iv : Z * Z => sh (A + n - 1) + 1 <= fst iv \/ snd iv <= sh A) X ->
    accessible m' A n.
  Proof.
    intros s L m2 LB2 m m' SP X A n HP SUB HSP OB (Q0 & Q1 & QA) XP HX.
    split; [exact Q0|]. split; [exact Q1|]. intros xa Hxa. destruct (QA xa Hxa) as (v & V1 & RD & OK).
    exists v. split; [exact V1|]. split; [| exact OK]. unfold mrd in *.
    assert (SX : ASHADOW_BASE <= sh xa < AHI_LO).
    { split; [unfold sh; Z.div_mod_to_equations; lia|].
      pose proof (sh_nsh_high xa 1 ltac:(lia) ltac:(lia) ltac:(lia)). unfold nsh in *. change ((1 + 7) / 8) with 1 in H0. lia. }
    destruct (XP (sh xa)) as [EQ _].
    { unfold AHI_LO in SX. rewrite ASHADOW_BASE_val in SX. lia. }
    { split; [eapply (ashobj_sh_client_sub H HH); eauto|].
      assert (M1 : sh A <= sh xa) by (apply sh_mono; lia). assert (M2 : sh xa <= sh (A + n - 1)) by (apply sh_mono; lia).
      clear - HX M1 M2. induction X as [|iv X IH]; [intros K; exact K|]. cbn. intros [K|K].
      - pose proof (Forall_inv HX) as K1. cbn in K1. lia.
      - exact (IH (Forall_inv_tail HX) K). }
    rewrite EQ. exact RD.
  Qed.

  (* [comment removed for export] *)
  Definition at_head (rb : Z) (k : config) : Prop :=
    exists (rax x1 a0 a1 a2 a3 a4 x6 x7 x8 x10 t0 t1 t2 t3 t4 t5 t6 : word) m s' errv' P xs NB cur rem,
      dworld m s' errv' P xs NB cur rem /\ rem <= rb /\ as_AKREL H s' k /\ as_MPRES H mo (cfg_model k)
      /\ as_VIS H s' (cfg_ms k)
          = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 (Z_to_bv 64 (-2)) (Z_to_bv 64 1) (Z_to_bv 64 2)
                    (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                    x6 x7 x8 (Z_to_bv 64 ASHB) x10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
                F (Z_to_bv 64 ADX_LOOP) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  Lemma RFS_via_xpresX : forall s L m2 LF0 LB2 SP X m m',
    as_RFS H LF0 m -> as_RHEAP H s L m2 -> xpres H LB2 SP X m m' ->
    Forall (fun iv : Z * Z => snd iv <= ATLS_PRIV_LO
                              \/ (exists b, In b L /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
                              \/ (exists b, In b L /\ sh (blk_addr b) <= fst iv /\ snd iv <= sh (blk_addr b) + nsh (blk_size b))) X ->
    as_RFS H LF0 m'.
  Proof.
    intros s L m2 LF0 LB2 SP X m m' R HP XP HX. pose proof (RFS_fsb H HH _ _ R) as (F1 & F2 & F3 & F4). acb.
    eapply (ah_RFS_ext H HH); [exact R|].
    intros a Ha Hr. apply XP; [exact Ha|]. split.
    - unfold aclient_addr. destruct Hr as [Hr|[Hr|Hr]].
      + right; right; right; right; left. exact Hr.
      + right; left. unfold aimg_client. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
      + right; right; right; right; right; left. exact Hr.
    - assert (LOa : ATLS_PRIV_LO <= a).
      { pose proof (sh_mono AIMG_TOP (as_FSB H) F1). assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
        unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP, AIMG_TOP in *. lia. }
      pose proof (sh_aapp_range _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (FS1 & FS2 & FS3). assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in FS1.
      pose proof (aapp_not_shadowland _ _ F4) as FNS.
      assert (GEN : forall iv, In iv X -> ~ (fst iv <= a < snd iv)).
      { intros iv Hiv K. pose proof (proj1 (Forall_forall _ _) HX iv Hiv) as K1. cbn beta in K1.
        destruct K1 as [K1|[(b & Hb & R1 & R2)|(b & Hb & R1 & R2)]]; [clear - K K1 LOa; lia| |].
        + pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
          pose proof (aapp_not_shadowland _ _ B7) as BNS.
          destruct Hr as [Hr|[Hr|Hr]]; [clear - K R1 R2 B6 Hr; lia| unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; clear - K R1 R2 B4 Hr; lia|].
          unfold AFS_SIZE in *. unfold ALOWSH_LO, AHI_LO, sh in *. rewrite ?ASHADOW_BASE_val in *. clear - K R1 R2 BNS Hr FNS F1 F2 B4 ACEILB. unfold AIMG_TOP in *. lia.
        + pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
          pose proof (sh_aapp_range _ _ B7 B3) as (S1 & S2 & S3). rewrite S0 in S1. pose proof (aapp_not_shadowland _ _ B7) as BNS.
          destruct Hr as [Hr|[Hr|Hr]].
          * unfold AFS_SIZE, ALOWSH_LO, AHI_LO, sh, nsh in *. rewrite ?ASHADOW_BASE_val in *. clear - K R1 R2 FNS Hr S1 S2 S3 B4 B3 ACEILB F1 F2. unfold AIMG_TOP in *. lia.
          * unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *. clear - K R1 R2 S1 Hr. lia.
          * unfold AFS_SIZE, sh, nsh in *. clear - K R1 R2 B6 B2 B3 F3 Hr. Z.div_mod_to_equations. lia. }
      clear - GEN. induction X as [|iv X IH]; [intros K; exact K|]. cbn. intros [K|K]; [exact (GEN iv (or_introl eq_refl) K)|].
      apply IH; [intros iv' Hiv'; apply GEN; right; exact Hiv'| exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma ASK_foot_stack0 : forall P K, 0 <= sk_cap K ->
    (forall b, In b (blocks_SK P K) -> aapp (blk_addr b) (blk_size b) /\ 0 <= blk_size b) -> Forall stack0_ok (ASK_foot P K).
  Proof.
    clear. intros P K C0 HB. unfold ASK_foot, SK_foot. apply Forall_app. split.
    - assert (H1 := HB _ ltac:(unfold blocks_SK; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H1. destruct H1 as [AP1 _].
      constructor; [eapply stack0_ok_aapp; [exact AP1| cbn; lia| cbn; lia]|].
      destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as [AP2 _].
      eapply stack0_ok_aapp; [exact AP2| cbn; lia| cbn; lia].
    - destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor].
      assert (H2 := HB _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)). cbn [blk_addr blk_size fst snd] in H2. destruct H2 as [AP2 N2].
      pose proof (aapp_bounds _ _ AP2 N2) as (Q1 & Q2 & Q3 & Q4 & Q5). apply stack0_ok_sh; unfold AIMG_TOP in Q1; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ASK_foot_fs : forall P K L, 0 <= sk_cap K -> (forall b, In b (blocks_SK P K) -> In b L) ->
    Forall (fun iv : Z * Z => snd iv <= ATLS_PRIV_LO
                              \/ (exists b, In b L /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
                              \/ (exists b, In b L /\ sh (blk_addr b) <= fst iv /\ snd iv <= sh (blk_addr b) + nsh (blk_size b))) (memflag_foot ++ ASK_foot P K).
  Proof.
    clear. intros P K L C0 SUB. apply Forall_app. split.
    { unfold memflag_foot, A_mem_inited, ATLS_PRIV_LO, ATP. constructor; [left; cbn; lia| constructor]. }
    unfold ASK_foot, SK_foot. apply Forall_app. split.
    - constructor; [right; left; exists (sk_id K, P, SK_SIZE); split; [apply SUB; unfold blocks_SK; left; reflexivity| cbn; lia]|].
      destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor].
      right; left. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [apply SUB; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity| cbn; lia].
    - destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE]; [constructor|]. constructor; [| constructor].
      right; right. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [apply SUB; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity| cbn; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma shavoids_acc : forall X a n, shavoids X a n -> a mod 8 = 0 -> 0 <= a ->
    Forall (fun iv : Z * Z => sh (a + n - 1) + 1 <= fst iv \/ snd iv <= sh a) X.
  Proof.
    clear. intros X a n SAV A8 A0. unfold shavoids in SAV. eapply Forall_impl; [| exact SAV]. cbn beta. intros [u v] K. cbn [fst snd] in *.
    unfold sh, nsh in *. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma blk_not_client : forall s Lall m2 L SP b1 a,
    as_RHEAP H s Lall m2 -> In b1 Lall -> (forall b, In b L -> In b Lall) -> (forall b, In b L -> blk_id b <> blk_id b1) -> aceil <= SP ->
    blk_addr b1 <= a < blk_addr b1 + blk_size b1 -> aclient_addr H L SP a -> False.
  Proof.
    intros s Lall m2 L SP b1 a HP IN1 SUB IDS1 HSP Ra C. acb.
    pose proof (ah_blocks H HH _ _ _ _ HP IN1) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof (aapp_not_shadowland _ _ B7) as BNS.
    pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4). pose proof (sh_aapp_range _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (FS1 & FS2 & FS3).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in FS1. pose proof (sh_aapp_range _ _ B7 B3) as (S1 & S2 & S3). rewrite S0 in S1.
    destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
    - clear - C Ra B5 HSP. lia.
    - unfold aimg_client, AIMG_TOP in *. clear - C Ra B4. lia.
    - destruct C as (b & Hb & Rb). pose proof (ah_disj H HH _ _ _ _ _ HP (SUB _ Hb) IN1 (IDS1 _ Hb)) as DJ. clear - DJ Ra Rb. lia.
    - destruct C as (b & Hb & Rb). pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & D3 & _ & _ & _ & D7).
      pose proof (sh_aapp_range _ _ D7 D3) as (T1 & T2 & T3). rewrite S0 in T1. clear - Rb Ra BNS T1 T2 T3. unfold ALOWSH_LO, AHI_LO in *. lia.
    - clear - C Ra B6. lia.
    - pose proof (sh_mono _ _ F2) as M6. clear - C Ra BNS FS1 FS3 M6. unfold ALOWSH_LO, AHI_LO in *. lia.
    - clear - C Ra BNS S1 S2 B3. unfold ALOWSH_LO, AHI_LO, nsh in *. lia.
  Qed.
  Lemma blksh_not_client : forall s Lall m2 L SP b1 a,
    as_RHEAP H s Lall m2 -> In b1 Lall -> (forall b, In b L -> In b Lall) -> (forall b, In b L -> blk_id b <> blk_id b1) -> aceil <= SP ->
    sh (blk_addr b1) <= a < sh (blk_addr b1) + nsh (blk_size b1) -> aclient_addr H L SP a -> False.
  Proof.
    intros s Lall m2 L SP b1 a HP IN1 SUB IDS1 HSP Ra C. acb.
    pose proof (ah_blocks H HH _ _ _ _ HP IN1) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof (aapp_not_shadowland _ _ B7) as BNS.
    pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4). pose proof (sh_aapp_range _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (FS1 & FS2 & FS3).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in FS1. pose proof (sh_aapp_range _ _ B7 B3) as (S1 & S2 & S3). rewrite S0 in S1.
    pose proof (aapp_not_shadowland _ _ F4) as FNS.
    destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
    - clear - C Ra S2 S3 HSP ACEILB. unfold AHI_LO in *. lia.
    - unfold aimg_client in *. clear - C Ra S1. lia.
    - destruct C as (b & Hb & Rb). pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & D3 & _ & _ & _ & D7).
      pose proof (aapp_not_shadowland _ _ D7) as BNSb. clear - Rb Ra BNSb S1 S2 S3. unfold ALOWSH_LO, AHI_LO in *. lia.
    - destruct C as (b & Hb & Rb). pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & D2 & D3 & _ & _ & _ & D7).
      pose proof (ah_disj H HH _ _ _ _ _ HP (SUB _ Hb) IN1 (IDS1 _ Hb)) as DJ.
      pose proof (sh_disjoint_blocks (blk_addr b) (blk_size b) (blk_addr b1) (blk_size b1) ltac:(clear - D2; Z.div_mod_to_equations; lia) ltac:(clear - B2; Z.div_mod_to_equations; lia) D3 B3 DJ) as SD.
      clear - Rb Ra SD. lia.
    - clear - C Ra FNS S1 S2 S3. unfold AFS_SIZE, ALOWSH_LO, AHI_LO in *. lia.
    - assert (E6 : sh (as_FSB H + AFS_SIZE) = sh (as_FSB H) + nsh AFS_SIZE) by (unfold sh, nsh, AFS_SIZE; clear - F3; Z.div_mod_to_equations; lia). rewrite E6 in C.
      pose proof (sh_disjoint_blocks (as_FSB H) AFS_SIZE (blk_addr b1) (blk_size b1) ltac:(clear - F3; Z.div_mod_to_equations; lia) ltac:(clear - B2; Z.div_mod_to_equations; lia) ltac:(unfold AFS_SIZE; lia) B3 ltac:(unfold AFS_SIZE in *; clear - B6; lia)) as SD2.
      clear - C Ra SD2. lia.
    - clear - C Ra S2. lia.
  Qed.

  (* [comment removed for export] *)
  Local Ltac pf_site := eapply pf_ok_call; [exact PF|]; unfold PF_decexts; intros y Hy; repeat (first [exact Hy| apply in_or_app; first [left; exact Hy| right]]).

  (* [comment removed for export] *)
  Lemma dx_push : forall m s' errv' P K es NB c cur rem X' Ao pad msF mo' (t0 t1 t2 x1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x10 t3 t4 t5 t6 : word),
    dworldX m s' errv' P (Some (K, es)) NB c cur rem (blocks_EXT Ao X') ->
    length pad = 4%nat -> rw_cells asegs m Ao (ext_cells X' pad) ->
    match ex_val_o X' with None => ex_val X' = 0 | Some (pv, n) => 0 < ex_val X' /\ 1 <= n <= ex_len X' end ->
    0 <= ex_len X' < 512 -> c + 4 + ex_len X' <= rem0 - rem ->
    EXT_shad m Ao X' ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR (Z_to_bv 64 ADX_R8) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 (Z_to_bv 64 P) (Z_to_bv 64 Ao) a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                x6 x7 x8 (Z_to_bv 64 ASHB) x10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
           F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m (seg_rom asegs) ->
    as_SR H (at_head rem) (mkCfg msF mo').
  Proof.
    intros m s' errv' P K es NB c cur rem X' Ao pad msF mo' t0 t1 t2 x1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x10 t3 t4 t5 t6 FW PL XC VO XL CLE XSH KREL MP VIS.
    pose proof (dworldX_chain _ _ _ _ _ _ _ _ _ _ FW) as CHN. pose proof (dworldX_blocks _ _ _ _ _ _ _ _ _ _ FW) as HB.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & ACCB & ACCP & SK0 & RFS & XP0 & ALG).
    clear FW. cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. pose proof BSL as BSL'. unfold zlength in BSL'.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & ESHD & EBL). rewrite MF0 in MF.
    set (XB := blocks_EXT Ao X') in *. set (Lp := mid_errblocks M ++ XB ++ NB ++ LB) in *.
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & HC) & EIN & O1 & O2 & O3 & O4 & XS).
    cbn [EW en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o] in EIN, XS, O1, O2, O3, O4, HC.
    unfold EXTS in XS. destruct XS as (PP & SO & LEN & F2).
    pose proof ESH as (ETOP & EAD & ES1 & ES2 & ES3 & ES4 & XSH0).
    cbn [EW en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o] in ES1, ES2, ES3, ES4, XSH0.
    cbn [EXTS_shad] in XSH0. destruct XSH0 as ((SKSH & PTOP & DTOP) & F2S).
    unfold XINV in XI. destruct XI as (KC & K4 & KCAP & E5 & EBY). set (EB := EBof K es) in *.
    pose proof SO as (_ & _ & KIN & KNC & KCAP2 & _ & _ & KDAT). unfold sk_num in KNC.
    (* [comment removed for export] *)
    assert (OIN : In (ex_id X', Ao, EXT_SIZE) Lp) by (subst Lp XB; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    pose proof (HB _ OIN) as (OP & O4lo & OH & _ & OAP). cbn [blk_addr blk_size fst snd] in OP, O4lo, OH, OAP. unfold EXT_SIZE in OH.
    (* [comment removed for export] *)
    pose proof (blocks_SK_facts P K ltac:(lia)) as (SKB & SKL & SKL1 & _).
    assert (NBB : lb_bytes NB = lb_bytes (blocks_SK P K) + lb_bytes EB) by (rewrite <- (lb_bytes_perm _ _ PB), lb_bytes_app; reflexivity).
    assert (NBL : length NB = (length (blocks_SK P K) + length EB)%nat) by (rewrite <- (Permutation_length PB), length_app; reflexivity).
    assert (XBB : lb_bytes XB <= EXT_SIZE + ex_len X' /\ Z.of_nat (length XB) <= 2).
    { subst XB. unfold blocks_EXT, blocks_of. destruct (ex_val_o X') as [[pv n]|]; rewrite ?lb_bytes_cons; cbn [blk_size snd length lb_bytes fold_right]; unfold EXT_SIZE; lia. }
    destruct XBB as (XBB & XBL).
    pose proof (sk_grow_le (sk_cap K) ltac:(lia)) as [GR GR5]. unfold zlength in *.
    assert (LpB : lb_bytes Lp + SKPUSH_COST K <= as_LIVE_MAX H).
    { subst Lp. rewrite !lb_bytes_app in *. unfold SKPUSH_COST. unfold DECEXTS_BYTES, ERRDEBUG_BYTES, SK_SIZE, EXT_SIZE in *.
      pose proof (errph_nonneg (mid_err M)) as [EB0 _]. clear - BY EB0 NBB SKB EBY XBB GR KCAP K4 CLE CB1 CB2 PIN REMB XL. unfold pk_in in PIN. lia. }
    assert (LpC : Z.of_nat (length Lp) + 1 <= as_LIVE_CNT_MAX H).
    { subst Lp. rewrite !length_app, !Nat2Z.inj_add in *. rewrite NBL, Nat2Z.inj_add in *.
      pose proof (errph_nonneg (mid_err M)) as [_ EC0]. clear - CN EC0 SKL E5 XBL CLE CB1 CB2 PIN XL Q5. unfold pk_in in PIN. lia. }
    (* [comment removed for export] *)
    assert (CAPM : sk_cap K <= SK_CAP_MAX) by (unfold SK_CAP_MAX; clear - KCAP K4 CLE CB2 PIN REMB XL; unfold pk_in in PIN; lia).
    assert (PCM : 0 <= SKPUSH_COST K <= ADX_PUSH_CM).
    { unfold SKPUSH_COST, ADX_PUSH_CM. pose proof (Z.div_le_mono (sk_cap K * 8) (SK_CAP_MAX * 8) 5 ltac:(lia) ltac:(clear - CAPM; lia)) as DM.
      unfold sk_grow in *. change (SK_CAP_MAX * 8 / 5) with 1638 in DM. clear - DM GR. lia. }
    destruct ALG as (um & uf & U1 & U2 & U3). cbn [xs_len xs_base] in U1, U2. unfold zlength, SK_SIZE in U1, U2.
    pose proof (aCm_super H HH um (SKPUSH_COST K) ltac:(lia) ltac:(lia)) as SCM. pose proof (aCf_super H HH uf (8 * sk_cap K) ltac:(lia) ltac:(lia)) as SCF.
    assert (UB1 : um + SKPUSH_COST K <= DECEXTS_CM rem0).
    { unfold DECEXTS_CM. unfold ADX_PER_EXT, ADX_PUSH_CM, EXT_SIZE in *. clear - U1 PCM XBB K4 CLE CB1 CB2 XL PIN. unfold pk_in in PIN. lia. }
    assert (UB2 : uf + 8 * sk_cap K <= DECEXTS_CF rem0).
    { unfold DECEXTS_CF. unfold ADX_PUSH_CF in *. clear - U2 KCAP K4 CLE CB1 CB2 XL PIN. unfold pk_in in PIN. lia. }
    pose proof (aCm_mono H HH (um + SKPUSH_COST K) (DECEXTS_CM rem0) ltac:(lia)) as MCM. pose proof (aCf_mono H HH (uf + 8 * sk_cap K) (DECEXTS_CF rem0) ltac:(lia)) as MCF.
    assert (RC0 : 0 <= RAISE_COST H (mid_err M)).
    { unfold RAISE_COST. pose proof (errph_nonneg (mid_err M)) as [EB0 _]. pose proof (aCm_pos H HH (raise_bytes (mid_err M)) ltac:(unfold raise_bytes, ERRDEBUG_BYTES; lia)).
      pose proof (aCf_pos H HH (errph_bytes (mid_err M) + ERRDEBUG_BYTES) ltac:(unfold ERRDEBUG_BYTES; lia)). lia. }
    assert (HAL : as_Cm H (SKPUSH_COST K) + as_Cf H (8 * sk_cap K) <= as_AL H s').
    { unfold DECEXTS_COST in HAL0. clear - HAL0 U3 SCM SCF MCM MCF RC0. lia. }
    (* [comment removed for export] *)
    pose proof (askpush_spec H HHx) as PS. unfold skpush_stmt in PS.
    eapply (ah_seq H HH).
    { eapply PS with (lo := lo) (B := B) (LB := Lp) (s := s') (a := P) (p := Ao) (v := 1) (K := K) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS| reflexivity| reflexivity| ..]; rewrite ?unsigned_lit by (unfold ADX_R8; lia).
      all: try first [exact HP| exact KREL| exact AUX| exact ST| exact CEIL| exact MI| exact LpB| exact LpC| exact TP| exact AC| exact CHN| exact SKSH| exact HAL].
      all: lazymatch goal with
           | |- 0 < _ < _ => clear - OP OH ACEILB; lia
           | |- SKobj _ _ _ _ => eapply SKobj_LB_mono; [exact SO| intros b Hb; subst Lp; do 2 (apply in_or_app; right); exact Hb]
           | |- sk_push_nocmp _ => left; exact KC
           | |- sk_cap _ <= SK_CAP_MAX => exact CAPM
           | |- _ <= B => clear - SPB SPR; lia
           | |- _ mod 16 = 0 => clear - SPA SPR; replace (bv_unsigned sp + -144) with (bv_unsigned sp - 9 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
           | |- _ <= _ - SKPUSH_STACK => clear - LO; unfold DECEXTS_STACK, FR_ech_decode_echconfig_exts in LO; lia
           | |- rw_cells _ _ (errno_addr _) _ => exact ERR
           | |- C1env _ _ => split; [exact MF| split; [exact IM| exact G1]]
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - SPR; lia| specialize (CHS _ _ Hin); clear - CHS; lia]
           | |- pf_ok _ _ _ _ => pf_site
           | |- ?G => idtac "PUSHPRE" G
           end. }
    clear PS. intros [ms8 mo8] PO. unfold skpush_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m8 & errv8 & s8' & LB' & K' & data' & cap' & did' &
                    VIS8 & KREL8 & MP8 & MI8 & AC8 & ST8 & ERR8 & AUX8 & KEQ & PLB & HP8 & SO8 & SKSH8 & XP8 & (v8 & (MF8 & IM8 & GM8) & VLE) & AL8).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in ST8, XP8 by lia.
    assert (V8 : v8 = 1) by (destruct MF8 as (fb8 & _ & _ & V01); lia). subst v8.
    (* [comment removed for export] *)
    subst Lp. pose proof (skpush_perm _ _ P _ _ _ _ (mid_errblocks M) XB EB LB LB' NB KEQ PLB PB ltac:(unfold sk_num, zlength; lia)) as [PL' CAPS].
    set (REST := mid_errblocks M ++ XB ++ EB ++ LB) in *.
    set (NB' := blocks_SK P K' ++ (EB ++ XB)).
    assert (IDK : sk_id K' = sk_id K) by (rewrite KEQ; reflexivity).
    assert (ELK : sk_elems K' = sk_elems K ++ [Ao]) by (rewrite KEQ; reflexivity).
    assert (CMK : sk_comp K' = sk_comp K) by (rewrite KEQ; reflexivity).
    assert (C0' : 0 <= sk_cap K') by (clear - CAPS KCAP GR; lia).
    assert (INR : forall b, In b REST -> In b LB') by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL'| apply in_or_app; right; exact Hb]).
    assert (INK : forall b, In b (blocks_SK P K') -> In b LB') by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL'| apply in_or_app; left; exact Hb]).
    assert (SUBLR : forall b, In b LB -> In b REST) by (intros b Hb; subst REST; do 3 (apply in_or_app; right); exact Hb).
    assert (SUBER : forall b, In b (EB ++ LB) -> In b REST) by (intros b Hb; subst REST; do 2 (apply in_or_app; right); exact Hb).
    assert (SUBXR : forall b, In b XB -> In b REST) by (intros b Hb; subst REST; apply in_or_app; right; apply in_or_app; left; exact Hb).
    pose proof (Permutation_NoDup (Permutation_map blk_id PL') (ah_nodup H HH _ _ _ HP8)) as ND'.
    assert (IDSK : forall b1 b2, In b1 (blocks_SK P K') -> In b2 REST -> blk_id b2 <> blk_id b1) by (intros b1 b2 H1 H2; apply not_eq_sym; exact (nodup_ids_app_ne _ _ _ _ ND' H1 H2)).
    assert (DJ : forall b1 b2, In b1 (blocks_SK P K') -> In b2 REST -> blk_addr b1 + blk_size b1 + 16 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 + 16 <= blk_addr b1)
      by (intros b1 b2 H1 H2; exact (perm_split_disjoint _ _ _ _ _ _ _ HP8 PL' H1 H2)).
    assert (HB8 : forall b, In b LB' -> 0 < blk_addr b /\ blk_addr b mod 16 = 0 /\ 0 <= blk_size b /\ AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP8 Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). repeat split; assumption. }
    assert (SKF : forall b, In b (blocks_SK P K') -> aapp (blk_addr b) (blk_size b) /\ blk_addr b mod 8 = 0 /\ 0 <= blk_size b).
    { intros b Hb. pose proof (HB8 _ (INK _ Hb)) as (_ & B2 & B3 & _ & _ & B7). split; [exact B7|]. split; [clear - B2; Z.div_mod_to_equations; lia| exact B3]. }
    (* [comment removed for export] *)
    assert (AV : forall b, In b REST -> avoids (memflag_foot ++ ASK_foot P K') (blk_addr b) (blk_size b) /\ shavoids (memflag_foot ++ ASK_foot P K') (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (HB8 _ (INR _ Hb)) as (B1 & B2 & B3 & B4 & B5 & B7).
      pose proof (ASK_foot_app P K' (blk_addr b) (blk_size b) B7 B3 ltac:(clear - B2; Z.div_mod_to_equations; lia) C0'
                    ltac:(intros b1 H1; pose proof (SKF _ H1) as (Q1 & Q2 & Q3); split; [exact Q1|]; split; [exact Q2|]; pose proof (DJ _ _ H1 Hb); lia)) as [A1 A2].
      split; [apply avoids_app; [apply avoids_memflag; exact B4| exact A1]| apply shavoids_app; [apply shavoids_memflag; [exact B7| exact B3]| exact A2]]. }
    assert (AVF : avoids (memflag_foot ++ ASK_foot P K') (bv_unsigned sp + -144) 144).
    { apply avoids_app; [apply avoids_memflag; unfold AIMG_TOP; clear - CEIL LO8K ACEILB; lia|]. apply ASK_foot_stack; [clear - CEIL LO8K; lia| exact C0'| intros b Hb; exact (proj1 (SKF _ Hb))]. }
    assert (AVP : avoids (memflag_foot ++ ASK_foot P K') pk 24).
    { apply avoids_app; [apply avoids_memflag; unfold AIMG_TOP; clear - CEIL LO8K ACEILB SPK; lia|]. apply ASK_foot_stack; [clear - CEIL LO8K SPK; lia| exact C0'| intros b Hb; exact (proj1 (SKF _ Hb))]. }
    (* [comment removed for export] *)
    assert (HP9 : as_RHEAP H s8' (mid_errblocks M ++ [] ++ NB' ++ LB) m8).
    { eapply (HHx_rheap_perm H HHx); [exact HP8|]. etransitivity; [exact PL'|]. subst NB' REST. cbn [app].
      etransitivity; [apply Permutation_app_swap_app|]. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_swap_app. }
    assert (SUBN : forall b, In b (blocks_SK P K') \/ In b EB \/ In b XB -> In b NB') by (intros b Hb; subst NB'; destruct Hb as [Hb|[Hb|Hb]]; apply in_or_app; [left| right; apply in_or_app; left| right; apply in_or_app; right]; exact Hb).
    assert (SUBN9 : forall b, In b (NB' ++ LB) -> In b LB').
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| apply INR, SUBLR; exact Hb].
      subst NB'. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply INK; exact Hb|].
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply INR, SUBER; apply in_or_app; left; exact Hb| apply INR, SUBXR; exact Hb]. }
    (* [comment removed for export] *)
    assert (FR8 : rw_cells asegs m8 (bv_unsigned sp + -144) (adx_frame j0 pk ee s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H); [exact XP8| exact FR| left; lia|]. unfold adx_frame. cbn [cells_size csize Nat.add length]. exact AVF. }
    assert (PKc8 : rw_cells asegs m8 pk (pk_cells cur base rem)).
    { eapply (xpres_rw_cells' H); [exact XP8| exact PK| left; clear - SPK; lia|]. unfold pk_cells. cbn [cells_size csize Nat.add length]. exact AVP. }
    assert (HC8 : rw_cells asegs m8 ee (entry_cells (EW P (Some (K', es ++ [X']))) pad1 pad2 pad3 pad4)).
    { eapply (xpres_rw_cells' H); [exact XP8| exact HC| |].
      - right; right; left. exists (en_id E, ee, ENTRY_SIZE). split; [apply INR, SUBLR; exact EIN0|]. unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold ENTRY_SIZE. lia.
      - eapply avoids_sub; [apply (proj1 (AV _ (SUBLR _ EIN0)))| cbn; lia|]. unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold ENTRY_SIZE. lia. }
    assert (XC8 : rw_cells asegs m8 Ao (ext_cells X' pad)).
    { eapply (xpres_rw_cells' H); [exact XP8| exact XC| |].
      - right; right; left. exists (ex_id X', Ao, EXT_SIZE). split; [apply INR, SUBXR; subst XB; left; reflexivity|]. unfold ext_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold EXT_SIZE. lia.
      - eapply avoids_sub; [apply (proj1 (AV _ (SUBXR _ ltac:(subst XB; left; reflexivity))))| cbn; lia|]. unfold ext_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold EXT_SIZE. lia. }
    assert (BS8 : bytes_at asegs m8 base bs).
    { eapply (xpres_bytes_at' H); [exact XP8| exact BS| |].
      - right; right; left. exists (pbin, base, len). split; [apply INR, SUBLR; exact BIN|]. cbn [blk_addr blk_size fst snd]. lia.
      - eapply avoids_sub; [apply (proj1 (AV _ (SUBLR _ BIN)))| cbn; lia| cbn [blk_addr blk_size fst snd]; lia]. }
    pose proof (HB8 _ (INR _ (SUBLR _ BIN))) as (PB1 & PB2 & _ & _ & _ & _). cbn [blk_addr blk_size fst snd] in PB1, PB2.
    assert (ACCB8 : accessible m8 base len).
    { eapply (accessible_xpresX s8' LB' m8 LB' m m8 (bv_unsigned sp + -144)); [exact HP8| intros b Hb; exact Hb| clear - CEIL LO8K; lia| | exact ACCB| exact XP8|].
      - left. exists (pbin, base, len). split; [apply INR, SUBLR; exact BIN| cbn [blk_addr blk_size fst snd]; lia].
      - apply shavoids_acc; [exact (proj2 (AV _ (SUBLR _ BIN)))| clear - PB2; Z.div_mod_to_equations; lia| clear - PB1; lia]. }
    assert (ACCP8 : accessible m8 pk 24).
    { eapply (accessible_xpresX s8' LB' m8 LB' m m8 (bv_unsigned sp + -144)); [exact HP8| intros b Hb; exact Hb| clear - CEIL LO8K; lia| | exact ACCP| exact XP8|].
      - right; right. clear - SPK. lia.
      - apply shavoids_acc; [| exact PK8| clear - SPK SPR; lia].
        apply shavoids_app; [| apply ASK_foot_stack_sh; [clear - CEIL LO8K SPK; lia| lia| pose proof ACCP as (_ & Q1 & _); exact Q1| exact C0'| exact SKF]].
        unfold shavoids, memflag_foot, A_mem_inited. constructor; [| constructor]. cbn [fst snd]. right. unfold sh. rewrite ASHADOW_BASE_val. clear - SPK CEIL LO8K ACEILB. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    assert (SUBLIB' : forall b, In b LIB -> In b LB') by (intros b Hb; apply INR, SUBLR, LIBSUB; exact Hb).
    assert (SPQC : aceil <= bv_unsigned sp + -144) by (clear - CEIL LO8K; lia).
    assert (NCL : forall L q, (forall b, In b L -> In b REST) -> rin_ivs (ASK_foot P K') q -> aclient_addr H L (bv_unsigned sp + -144) q -> False).
    { intros L q SUBL0 Hq C. destruct (ASK_foot_rin _ _ _ Hq) as [(b1 & H1 & R1)|[NE R1]].
      - eapply (blk_not_client s8' LB' m8 L (bv_unsigned sp + -144) b1 q); [exact HP8| apply INK; exact H1| intros b Hb; apply INR, SUBL0; exact Hb| intros b Hb; apply (IDSK _ _ H1 (SUBL0 _ Hb))| exact SPQC| exact R1| exact C].
      - eapply (blksh_not_client s8' LB' m8 L (bv_unsigned sp + -144) (sk_did K', sk_data K', 8 * sk_cap K') q); [exact HP8| | intros b Hb; apply INR, SUBL0; exact Hb| | exact SPQC| exact R1| exact C].
        + apply INK. unfold blocks_SK. rewrite (proj2 (Z.eqb_neq _ _) NE). right. left. reflexivity.
        + intros b Hb. apply (IDSK _ _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity) (SUBL0 _ Hb)). }
    assert (LM8 : LIBMID LIB m8 M).
    { rewrite <- M_eq1. eapply (LIBMID_mfX H HH s8' m8 LIB LB' (bv_unsigned sp + -144) (ASK_foot P K') m m8 M x);
        [exact HP8| exact LM| exact CX| exact XP8| exact SUBLIB'| intros b Hb; apply INR; subst REST; apply in_or_app; left; exact Hb| | | | | | exact MF8| ].
      - intros q Hq HX. pose proof (LIBX_below q HX) as QL. destruct (ASK_foot_rin _ _ _ Hq) as [(b1 & H1 & R1)|[NE R1]].
        + pose proof (HB8 _ (INK _ H1)) as (_ & _ & _ & B4 & _). clear - QL R1 B4. lia.
        + pose proof (proj1 (SKF _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity))) as AP2. cbn [blk_addr blk_size fst snd] in AP2.
          pose proof (sh_aapp_range _ _ AP2 ltac:(lia)) as (S1 & _). assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in S1. unfold AIMG_TOP in QL. clear - QL R1 S1. lia.
      - intros q Hq R. destruct (ASK_foot_rin _ _ _ Hq) as [(b1 & H1 & R1)|[NE R1]].
        + pose proof (HB8 _ (INK _ H1)) as (_ & _ & _ & B4 & _). unfold AIMG_TOP in B4. clear - R R1 B4. lia.
        + pose proof (proj1 (SKF _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity))) as AP2. cbn [blk_addr blk_size fst snd] in AP2.
          pose proof (sh_aapp_range _ _ AP2 ltac:(lia)) as (S1 & _). assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in S1. clear - R R1 S1. lia.
      - intros q Hq K0. eapply (NCL LIB q); [intros b Hb; apply SUBLR, LIBSUB; exact Hb| exact Hq| right; right; left; exact K0].
      - intros q Hq K0. eapply (NCL LIB q); [intros b Hb; apply SUBLR, LIBSUB; exact Hb| exact Hq| right; right; right; left; exact K0].
      - intros q Hq K0. eapply (NCL (mid_errblocks M) q); [intros b Hb; subst REST; apply in_or_app; left; exact Hb| exact Hq| right; right; right; left; exact K0].
      - intros q Hq K0. eapply (NCL (mid_errblocks M) q); [intros b Hb; subst REST; apply in_or_app; left; exact Hb| exact Hq| right; right; left; exact K0]. }
    assert (XP08 : xpres H LB (bv_unsigned sp) X0 m0 m8).
    { eapply (xpres_trans H); [exact XP0|].
      eapply (xpres_weaken H LB LB (bv_unsigned sp + -144) (bv_unsigned sp) [] X0); [| clear - SPR; lia| intros b Hb; exact Hb| intros q Hq; destruct Hq].
      eapply (xpres_drop_windows H LB LB' (bv_unsigned sp + -144) [] (ASK_foot P K') m m8); [| intros b Hb; apply INR, SUBLR; exact Hb| intros q Hq C; exact (NCL LB q SUBLR Hq C)].
      cbn [app]. eapply (axpres_drop_memflag H LB' _ [] (ASK_foot P K')); [exact MF| exact MF8| cbn [app]; exact XP8]. }
    (* [comment removed for export] *)
    assert (F28 : Forall2 (fun p X => EXTobj (NB' ++ LB) m8 p X) (sk_elems K) es).
    { assert (EBINb : forall b, In b EB -> exists pe, In pe (combine (sk_elems K) es) /\ In b (blocks_EXT (fst pe) (snd pe))).
      { intros b Hb. subst EB. unfold EBof in Hb. apply in_concat in Hb. destruct Hb as (l & Hl & Hb). apply in_map_iff in Hl. destruct Hl as (pe & <- & Hpe). exists pe. auto. }
      assert (BEL8 : forall b, In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine (sk_elems K) es))) -> blk_addr b + blk_size b <= bv_unsigned sp + -144).
      { intros b Hb. pose proof (HB _ ltac:(do 2 (apply in_or_app; right); apply in_or_app; left; eapply Permutation_in; [exact PB| apply in_or_app; right; exact Hb])) as (_ & _ & KB1 & _). clear - KB1 CEIL LO8K. lia. }
      assert (F2a : Forall2 (fun p X => EXTobj (EB ++ LB) m p X) (sk_elems K) es).
      { eapply (EXTs_frame H (NB ++ LB) (EB ++ LB) (EB ++ LB) (bv_unsigned sp + -144) m m); [exact F2| intros b Hb; apply in_or_app; left; exact Hb| intros b Hb; exact Hb| apply xpres_refl| exact BEL8]. }
      eapply (EXTs_frame H (EB ++ LB) (EB ++ LB) (NB' ++ LB) (bv_unsigned sp + -144) m8 m8); [| intros b Hb; apply in_or_app; left; exact Hb| | apply xpres_refl| exact BEL8].
      - eapply (EXTs_frameX (EB ++ LB) (bv_unsigned sp + -144) (memflag_foot ++ ASK_foot P K')); [exact F2a| eapply (xpres_weaken H); [exact XP8| lia| intros b Hb; apply INR, SUBER; exact Hb| intros q Hq; exact Hq]|].
        intros b Hb. apply (proj1 (AV _ (SUBER _ ltac:(apply in_or_app; left; exact Hb)))).
      - intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply SUBN; right; left; exact Hb| right; exact Hb]. }
    pose proof OF0 as (Q1 & Q2 & Q3 & Q4).
    assert (EBE : EBof K' (es ++ [X']) = EB ++ XB) by (rewrite KEQ, (EBof_push K es Ao X') by exact LEN; subst EB XB; reflexivity).
    assert (XI9 : XINV P (Some (K', es ++ [X'])) (rem0 - rem)).
    { unfold XINV. rewrite EBE, CMK. subst XB. unfold zlength in *.
      rewrite !length_app, !lb_bytes_app, !Nat2Z.inj_add. cbn [length]. revert VO XBB XBL. unfold blocks_EXT, blocks_of.
      assert (CAP9 : 0 <= sk_cap K' /\ 5 * sk_cap K' <= 8 * (Z.of_nat (length es) + 1) + 20).
      { destruct CAPS as [C1|[[C0 C4]|(CG & NC & C4)]]; [clear - C1 KCAP; lia| clear - C0 C4 KCAP; lia|].
        rewrite CG. unfold sk_num, zlength in NC. rewrite <- LEN in NC. pose proof (sk_grow_le (sk_cap K) ltac:(clear - C4; lia)) as [GR2 GR3]. clear - GR2 GR3 NC KCAP. lia. }
      destruct (ex_val_o X') as [[pv n]|]; intros VO XBB XBL;
        rewrite ?lb_bytes_cons; cbn [blk_size snd length lb_bytes fold_right]; unfold EXT_SIZE; clear - KC K4 CAP9 E5 EBY CLE XL VO; lia. }
    assert (NEWX : Forall2 (fun p X => EXTobj (NB' ++ LB) m8 p X) [Ao] [X']).
    { apply Forall2_cons; [| apply Forall2_nil].
      unfold EXTobj. split; [exists pad; split; [exact PL| exact XC8]|]. split; [apply in_or_app; left; apply SUBN; right; right; subst XB; left; reflexivity|].
      revert VO. unfold ofield. subst XB. unfold blocks_EXT, blocks_of in SUBN. destruct (ex_val_o X') as [[pv n]|]; intros VO; [| exact VO].
      split; [lia|]. split; [lia|]. apply in_or_app. left. apply SUBN. right. right. right. left. reflexivity. }
    (* [comment removed for export] *)
    assert (EAD8 : addressable m8 ee ENTRY_SIZE).
    { eapply (addressable_xpres_blkX H); [apply INR, SUBLR; exact EIN0| exact ETOP| exact EAD| exact XP8| exact (proj2 (AV _ (SUBLR _ EIN0)))]. }
    assert (OSH8 : forall Pf o, ofield LB Pf o -> oshad m Pf o -> oshad m8 Pf o).
    { intros Pf o OFo OSo. eapply oshad_xpresX; [| exact OSo| exact XP8]. destruct o as [[i1 n1]|]; [| exact I]. cbn [ofield] in OFo. destruct OFo as (_ & _ & IN1).
      split; [apply INR, SUBLR; exact IN1| exact (AV _ (SUBLR _ IN1))]. }
    assert (F2S8 : Forall2 (fun p X => EXT_shad m8 p X) (sk_elems K') (es ++ [X'])).
    { rewrite ELK. apply Forall2_app.
      - eapply EXTs_shad_xpresX; [exact F2S| exact XP8|]. intros b Hb. fold (EBof K es) in Hb. fold EB in Hb.
        split; [apply INR, SUBER; apply in_or_app; left; exact Hb| exact (AV _ (SUBER _ ltac:(apply in_or_app; left; exact Hb)))].
      - apply Forall2_cons; [| apply Forall2_nil].
        eapply EXT_shad_xpresX; [apply INR, SUBXR; subst XB; left; reflexivity| exact (proj2 (AV _ (SUBXR _ ltac:(subst XB; left; reflexivity))))| | exact XSH| exact XP8].
        subst XB. unfold blocks_EXT, blocks_of in SUBXR. destruct (ex_val_o X') as [[iv nv]|]; [| exact I].
        split; [apply INR, SUBXR; right; left; reflexivity| exact (AV _ (SUBXR _ ltac:(right; left; reflexivity)))]. }
    assert (DTOP8 : sk_cap K' <> 0 -> sk_data K' + 8 * sk_cap K' <= AAPP_HI).
    { intros NE. pose proof (SKF _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NE); right; left; reflexivity)) as (AP2 & _ & N2). cbn [blk_addr blk_size fst snd] in AP2, N2.
      pose proof (aapp_bounds _ _ AP2 N2) as (_ & _ & QT3 & _). clear - QT3. lia. }
    (* [comment removed for export] *)
    assert (FW9 : dworld m8 s8' errv8 P (Some (K', es ++ [X'])) NB' cur rem).
    { unfold dworld, dworldX. repeat match goal with |- _ /\ _ => split end; try assumption.
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => cbn [app] in HP9; exact HP9
           | |- ENTRYobj _ _ _ _ =>
               unfold ENTRYobj; cbn [EW en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o];
               split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact HC8]|];
               split; [apply in_or_app; right; exact EIN0|];
               split; [eapply ofield_LB_mono; [exact Q1| intros b Hb; apply in_or_app; right; exact Hb]|];
               split; [eapply ofield_LB_mono; [exact Q2| intros b Hb; apply in_or_app; right; exact Hb]|];
               split; [eapply ofield_LB_mono; [exact Q3| intros b Hb; apply in_or_app; right; exact Hb]|];
               split; [eapply ofield_LB_mono; [exact Q4| intros b Hb; apply in_or_app; right; exact Hb]|];
               unfold EXTS; split; [exact PP|]; split; [eapply SKobj_relist; [exact SO8| intros b Hb; apply in_or_app; left; apply SUBN; left; exact Hb]|];
               split; [rewrite ELK, !length_app; cbn [length]; rewrite LEN; reflexivity|];
               rewrite ELK; apply Forall2_app; [exact F28| exact NEWX]
           | |- ENTRY_shad _ _ _ =>
               unfold ENTRY_shad; cbn [EW en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o EXTS_shad SKX_shad];
               split; [exact ETOP|]; split; [exact EAD8|];
               split; [exact (OSH8 _ _ Q1 ES1)|]; split; [exact (OSH8 _ _ Q2 ES2)|]; split; [exact (OSH8 _ _ Q3 ES3)|]; split; [exact (OSH8 _ _ Q4 ES4)|];
               split; [split; [exact SKSH8| split; [exact PTOP| exact DTOP8]]| exact F2S8]
           | |- Permutation _ _ => unfold blocks_EXTS; fold (EBof K' (es ++ [X'])); rewrite EBE; subst NB'; apply Permutation_refl
           | |- XINV _ _ _ => exact XI9
           | |- 0 <= rem0 - _ => clear - CB1 CLE XL; lia
           | |- rem0 - _ <= rem0 - _ => clear; lia
           | |- stack0 _ _ _ => eapply (stack0_xpres H); [exact XP8| exact SK0|]; apply Forall_app; split;
                                 [unfold memflag_foot, A_mem_inited; constructor; [right; cbn [fst snd]; pose proof aceil_facts as AF; unfold sh; rewrite ASHADOW_BASE_val; clear - AF; Z.div_mod_to_equations; lia| constructor]
                                 | apply ASK_foot_stack0; [exact C0'| intros b Hb; pose proof (SKF _ Hb) as (Z1 & _ & Z3); split; [exact Z1| exact Z3]]]
           | |- as_RFS _ _ _ => eapply (RFS_via_xpresX s8' LB' m8); [exact RFS| exact HP8| exact XP8| apply ASK_foot_fs; [exact C0'| exact INK]]
           | |- ALED _ _ _ _ =>
               exists (um + SKPUSH_COST K), (uf + 8 * sk_cap K); cbn [xs_len xs_base lb_bytes fold_right]; unfold zlength, SK_SIZE; rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add;
               split; [unfold ADX_PER_EXT, ADX_PUSH_CM, EXT_SIZE in *; clear - U1 PCM XBB CLE XL CB1; lia|];
               split; [unfold ADX_PUSH_CF in *; clear - U2 KCAP CAPM; unfold SK_CAP_MAX in CAPM; lia|];
               clear - U3 AL8 SCM SCF; lia
           | |- ?G => idtac "FW9" G
           end. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply adx_seg9; [| exact FR8| clear - LO8K CEIL ACEILB; lia| exact MI8]|].
    { unfold sk_num, zlength. clear - KNC KCAP2. lia. }
    cbv beta. intros msF9 mo9 KREL9 MP9 VIS9.
    apply (ah_done H HH). unfold at_head. cbn [cfg_ms cfg_model].
    do 18 eexists. exists m8, s8', errv8, P, (Some (K', es ++ [X'])), NB', cur, rem.
    split; [exact FW9|]. split; [lia|]. split; [exact KREL9|]. split; [eapply (ah_mpres_trans H HH); [exact MP| eapply (ah_mpres_trans H HH); [exact MP8| exact MP9]]|]. exact VIS9.
  Qed.

  (* [comment removed for export] *)
  Lemma addressable_acrossW : forall W m m' A n,
    addressable m A n -> munch W m m' -> wmono asegs m m' -> 0 <= A < AAPP_HI -> A + n <= AAPP_HI ->
    Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W -> addressable m' A n.
  Proof.
    clear. intros W m m' A n AD MU WM A0 TOP HW. pose proof AD as [Hn _].
    eapply addressable_transport; [exact AD| exact MU| exact WM|].
    pose proof (sh_in_shadowland A A0) as S1.
    assert (S2 : sh A + nsh n <= AHI_LO) by (unfold sh, nsh, AHI_LO, AAPP_HI, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).
    clear - HW S1 S2. induction W as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K. cbn in K.
    split; [unfold ALOWSH_LO, AHI_LO in *; lia| exact (IH (Forall_inv_tail HW))].
  Qed.
  Lemma oshad_acrossW : forall W m m' P o,
    oshad m P o -> munch W m m' -> wmono asegs m m' ->
    (match o with None => True | Some (_, n) => 0 <= P < AAPP_HI /\ disjoint_from W P n end) ->
    Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W -> oshad m' P o.
  Proof.
    clear. intros W m m' P [[i n]|] OSH MU WM K HW; [| exact I]. cbn [oshad] in *. destruct OSH as (TOP & AD & bs & CB). destruct K as [P0 DJ].
    split; [exact TOP|]. split; [eapply addressable_acrossW; eauto|]. exists bs. eapply rw_cells_transport; [exact CB| exact MU| exact WM|].
    cbn [cells_size csize Nat.add]. pose proof AD as [Hn _]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact DJ.
  Qed.
  Lemma EXT_shad_acrossW : forall W m m' p X,
    EXT_shad m p X -> munch W m m' -> wmono asegs m m' -> 0 <= p -> disjoint_from W p EXT_SIZE ->
    (match ex_val_o X with None => True | Some (_, n) => 0 <= ex_val X < AAPP_HI /\ disjoint_from W (ex_val X) n end) ->
    Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W -> EXT_shad m' p X.
  Proof.
    clear. intros W m m' p X (TOP & AD & OSH) MU WM P0 DJp K HW. split; [exact TOP|].
    split; [eapply addressable_acrossW; eauto; unfold EXT_SIZE in TOP; lia|]. eapply oshad_acrossW; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_as_CB : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A [CB (cells_size cs) (cells_bytes cs)].
  Proof.
    clear. intros m A cs [[WF BA] W]. unfold rw_cells, cells_at. cbn [cells_bytes cbytes cells_wf cell_wf cells_size csize].
    rewrite app_nil_r, Nat.add_0_r. split; [split; [split; [apply cells_bytes_length; exact WF| exact I]| exact BA]| exact W].
  Qed.
  Lemma nodup_ids_same : forall (L : list block) b1 b2, List.NoDup (map blk_id L) -> In b1 L -> In b2 L -> blk_id b1 = blk_id b2 -> b1 = b2.
  Proof.
    clear. induction L as [|b L IH]; intros b1 b2 ND H1 H2 E; [destruct H1|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
    destruct H1 as [<-|H1], H2 as [<-|H2]; [reflexivity| | | exact (IH _ _ ND' H1 H2 E)].
    - exfalso. apply NI. rewrite E. apply in_map. exact H2.
    - exfalso. apply NI. rewrite <- E. apply in_map. exact H1.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_newsk : forall m s' errv' c cur rem X' Ao pad msF mo' (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x7 x8 : word),
    dworldX m s' errv' 0 None [] c cur rem (blocks_EXT Ao X') ->
    length pad = 4%nat -> rw_cells asegs m Ao (ext_cells X' pad) ->
    match ex_val_o X' with None => ex_val X' = 0 | Some (pv, n) => 0 < ex_val X' /\ 1 <= n <= ex_len X' end ->
    0 <= ex_len X' < 512 -> c + 4 + ex_len X' <= rem0 - rem ->
    EXT_shad m Ao X' ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR (Z_to_bv 64 ADX_R4) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) a0 a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                (Z_to_bv 64 Ao) x7 x8 (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
           F (Z_to_bv 64 P_OPENSSL_sk_new_null) fc None m (seg_rom asegs) ->
    as_SR H (at_head rem) (mkCfg msF mo').
  Proof.
    intros m s' errv' c cur rem X' Ao pad msF mo' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x7 x8 FW PL XC VO XL CLE XSH KREL MP VIS.
    pose proof (dworldX_chain _ _ _ _ _ _ _ _ _ _ FW) as CHN. pose proof (dworldX_blocks _ _ _ _ _ _ _ _ _ _ FW) as HB.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & ACCB & ACCP & SK0 & RFS & XP0 & ALG).
    cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. pose proof BSL as BSL'. unfold zlength in BSL'.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & ESHD & EBL). rewrite MF0 in MF.
    cbn [app] in HP. set (XB := blocks_EXT Ao X') in *. set (Lp := mid_errblocks M ++ XB ++ LB) in *.
    assert (OIN : In (ex_id X', Ao, EXT_SIZE) Lp) by (subst Lp XB; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    pose proof (HB _ ltac:(cbn [app]; exact OIN)) as (OP & O4lo & OH & _ & OAP). cbn [blk_addr blk_size fst snd] in OP, O4lo, OH, OAP. unfold EXT_SIZE in OH.
    assert (XBB : lb_bytes XB <= EXT_SIZE + ex_len X' /\ Z.of_nat (length XB) <= 2).
    { subst XB. unfold blocks_EXT, blocks_of. destruct (ex_val_o X') as [[pv n]|]; rewrite ?lb_bytes_cons; cbn [blk_size snd length lb_bytes fold_right]; unfold EXT_SIZE; lia. }
    destruct XBB as (XBB & XBL). unfold zlength in *.
    (* [comment removed for export] *)
    destruct ALG as (um & uf & U1 & U2 & U3). cbn [xs_len xs_base] in U1, U2.
    assert (RC0 : 0 <= RAISE_COST H (mid_err M)).
    { unfold RAISE_COST. pose proof (errph_nonneg (mid_err M)) as [EB0 _]. pose proof (aCm_pos H HH (raise_bytes (mid_err M)) ltac:(unfold raise_bytes, ERRDEBUG_BYTES; lia)).
      pose proof (aCf_pos H HH (errph_bytes (mid_err M) + ERRDEBUG_BYTES) ltac:(unfold ERRDEBUG_BYTES; lia)). lia. }
    assert (HAL : as_Cm H SK_SIZE <= as_AL H s').
    { pose proof (aCm_super H HH um SK_SIZE ltac:(lia) ltac:(unfold SK_SIZE; lia)) as SCM.
      pose proof (aCm_mono H HH (um + SK_SIZE) (DECEXTS_CM rem0) ltac:(unfold DECEXTS_CM, SK_SIZE, EXT_SIZE in *; clear - U1 XBB CLE XL CB1 CB2 PIN; unfold pk_in in PIN; lia)) as MCM.
      pose proof (aCf_mono H HH uf (DECEXTS_CF rem0) ltac:(unfold DECEXTS_CF; clear - U2 REM1; lia)) as MCF.
      unfold DECEXTS_COST in HAL0. clear - HAL0 U3 SCM MCM MCF RC0. lia. }
    (* [comment removed for export] *)
    pose proof (asknew_null_spec H HH) as SN. unfold sknew_null_stmt, sknew_stmt_gen in SN.
    eapply (ah_seq H HH).
    { eapply SN with (lo := lo) (B := B) (LB := Lp) (s := s') (c := 0) (v := 1) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH); [exact VIS| reflexivity| ..];
        rewrite ?unsigned_lit by (unfold ADX_R4; lia).
      all: try first [exact HP| exact KREL| exact AUX| exact ST| exact CEIL| exact MI| exact TP| exact AC| exact CHN| exact HAL].
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => subst Lp; rewrite !lb_bytes_app in *; unfold DECEXTS_BYTES, ERRDEBUG_BYTES, SK_SIZE, EXT_SIZE in *;
                                        pose proof (errph_nonneg (mid_err M)) as [EB0 _]; clear - BY EB0 XBB XL CLE CB1 CB2 PIN REM1; unfold pk_in in PIN; lia
           | |- Z.of_nat (length _) + _ <= _ => subst Lp; rewrite !length_app, !Nat2Z.inj_add in *; pose proof (errph_nonneg (mid_err M)) as [_ EC0]; clear - CN EC0 XBL REM1 Q5; lia
           | |- _ <= B => clear - SPB SPR; lia
           | |- _ mod 16 = 0 => clear - SPA SPR; replace (bv_unsigned sp + -144) with (bv_unsigned sp - 9 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
           | |- _ <= _ - _ => clear - LO; unfold DECEXTS_STACK, FR_ech_decode_echconfig_exts, SKPUSH_STACK, SKRESERVE_STACK, CARRAY_STACK, CREALLOC_ARRAY_STACK, CREALLOC_STACK,
                              FR_sk_new_null, FR_sk_insert, FR_sk_reserve, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, FR_CRYPTO_array, FR_CRYPTO_realloc in LO |- *; lia
           | |- rw_cells _ _ (errno_addr _) _ => exact ERR
           | |- C1env _ _ => split; [exact MF| split; [exact IM| exact G1]]
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - SPR; lia| specialize (CHS _ _ Hin); clear - CHS; lia]
           | |- pf_ok _ _ _ _ => pf_site
           | |- ?G => idtac "SNPRE" G
           end. }
    clear SN. intros [ms2 mo2] PO. unfold sknew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m2 & errv2 & Ps & id & did & s2' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & PSP & HP2 & SO2 & SKSH2 & (MF2 & IM2 & GM2) & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in ST2, XP2 by lia.
    pose proof (ah_mpres_trans H HH _ _ _ MP MP2) as MPc2.
    subst Lp. destruct (dworldX_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FW MI2 AC2 ST2 ERR2 AUX2 XP2 HP2 MF2 ltac:(unfold SK_SIZE; lia) AL2) as (FW2 & TR2 & TRa2 & TRc2).
    assert (OINX : In (ex_id X', Ao, EXT_SIZE) (XB ++ [] ++ LB)) by (apply in_or_app; left; subst XB; left; reflexivity).
    pose proof (TR2 (ex_id X', Ao, EXT_SIZE) Ao _ OINX XC ltac:(cbn; lia) ltac:(unfold ext_cells; cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]; unfold EXT_SIZE; lia)) as XC2.
    assert (XSH2 : EXT_shad m2 Ao X').
    { destruct XSH as (XT & XAD & XO). split; [exact XT|]. split; [exact (TRa2 _ _ _ OINX XAD ltac:(cbn; lia) ltac:(cbn; unfold EXT_SIZE; lia))|].
      revert XO VO. subst XB. unfold blocks_EXT, blocks_of in TR2, TRa2. destruct (ex_val_o X') as [[iv nv]|]; intros XO VO; [| exact I].
      cbn [oshad] in XO |- *. destruct XO as (T1 & A1 & bs1 & C1). split; [exact T1|]. split.
      - eapply TRa2; [apply in_or_app; left; right; left; reflexivity| exact A1| cbn; lia| cbn; lia].
      - exists bs1. eapply TR2; [apply in_or_app; left; right; left; reflexivity| exact C1| cbn; lia| cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; lia]. }
    clear TR2 TRa2 TRc2.
    pose proof (ah_blocks H HH _ _ _ _ HP2 (or_introl eq_refl)) as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH7). cbn [blk_addr blk_size fst snd] in SH1, SH2, SH3, SH4, SH5, SH6, SH7. unfold SK_SIZE in SH5.
    pose proof (ah_disj H HH _ _ _ (id, Ps, SK_SIZE) (ex_id X', Ao, EXT_SIZE) HP2 (or_introl eq_refl) (or_intror OIN)
                  (afresh_id_ne H HH _ _ _ _ _ _ (ex_id X') HP2 (in_map blk_id _ _ OIN))) as DSO. cbn [blk_addr blk_size fst snd] in DSO. unfold SK_SIZE, EXT_SIZE in DSO.
    set (SB := (id, Ps, SK_SIZE)) in *.
    assert (SKB : SK_below Ps (sk_fresh 0 id did) lo) by (split; [unfold SK_SIZE; clear - SH5 CEIL; lia| left; reflexivity]).
    assert (SKR : SK_ranges H Ps (sk_fresh 0 id did)) by (split; [exact (ah_blocks H HH _ _ _ _ HP2 (or_introl eq_refl))| cbn; intros K0; exfalso; apply K0; reflexivity]).
    assert (DJO : disjoint_from [(lo, bv_unsigned sp + -144); (Ps, Ps + SK_SIZE)] Ao (Z.of_nat (cells_size (ext_cells X' pad)))).
    { unfold ext_cells. cbn [cells_size csize Nat.add length]. unfold SK_SIZE. cbn. clear - OH CEIL DSO. lia. }
    assert (DJO16 : disjoint_from [(lo, bv_unsigned sp + -144); (Ps, Ps + SK_SIZE)] Ao EXT_SIZE) by (unfold SK_SIZE, EXT_SIZE; cbn; clear - OH CEIL DSO; lia).
    assert (WOK : Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= bv_unsigned sp + -144) \/ (Ps <= fst iv /\ snd iv <= Ps + SK_SIZE)) [(lo, bv_unsigned sp + -144); (Ps, Ps + SK_SIZE)]).
    { constructor; [left; cbn; lia|]. constructor; [| constructor]. right. cbn. lia. }
    assert (WNS : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp + -144); (Ps, Ps + SK_SIZE)]).
    { constructor; [right; cbn; unfold AHI_LO; clear - CEIL ACEILB; lia|]. constructor; [| constructor]. cbn [fst snd]. pose proof (aapp_not_shadowland _ _ SH7). unfold SK_SIZE in *. lia. }
    assert (DJV : match ex_val_o X' with None => True | Some (_, n) => 0 <= ex_val X' < AAPP_HI /\ disjoint_from [(lo, bv_unsigned sp + -144); (Ps, Ps + SK_SIZE)] (ex_val X') n end).
    { revert VO. subst XB. unfold blocks_EXT, blocks_of in OINX, HB, HP2. destruct (ex_val_o X') as [[iv nv]|]; intros VO; [| exact I].
      assert (VIN : In (iv, ex_val X', nv) (mid_errblocks M ++ ((ex_id X', Ao, EXT_SIZE) :: (iv, ex_val X', nv) :: []) ++ [] ++ LB)) by (apply in_or_app; right; apply in_or_app; left; right; left; reflexivity).
      pose proof (HB _ VIN) as (V1 & _ & V5 & V3 & _). cbn [blk_addr blk_size fst snd] in V1, V5, V3.
      pose proof (ah_disj H HH _ _ _ (id, Ps, SK_SIZE) (iv, ex_val X', nv) HP2 (or_introl eq_refl) (or_intror VIN) (afresh_id_ne H HH _ _ _ _ _ _ iv HP2 (in_map blk_id _ _ VIN))) as DV.
      cbn [blk_addr blk_size fst snd] in DV. unfold SK_SIZE in *. cbn. unfold AAPP_HI. clear - V1 V5 V3 DV CEIL ACEILB. lia. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply adx_seg5; exact MI2|]. intros msF3 mo3 KREL3 MP3 VIS3. pose proof (ah_mpres_trans H HH _ _ _ MPc2 MP3) as MPc3.
    pose proof (askset_cmp_thunks_spec H) as SC. unfold skset_cmp_thunks_stmt, skset_stmt_at in SC.
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply SC with (lo := lo) (a := Ps) (K := sk_fresh 0 id did); rewrite ?unsigned_lit by lia; try reflexivity;
                                   [unfold ADX_THUNK_CMP; lia| exact SO2| exact SKB| exact SKSH2| exact SKR| exact AC2| exact ST2| exact CEIL| clear - LO8K; lia| exact MI2]|].
    clear SC. intros msF4 mo4 KREL4 MP4 (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m4 & VIS4 & MU4 & WM4 & MI4 & AC4 & ST4 & SO4).
    pose proof (ah_mpres_trans H HH _ _ _ MPc3 MP4) as MPc4.
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in MU4, ST4 by lia.
    destruct (dworldX_munch _ _ _ _ _ _ _ _ _ _ _ _ id Ps SK_SIZE FW2 ltac:(left; reflexivity) MU4 WM4 MI4 ST4 AC4 WOK) as [FW4 TR4]. pose proof (TR4 _ _ XC2 DJO) as XC4. clear TR4 XC2.
    pose proof (EXT_shad_acrossW _ _ _ _ _ XSH2 MU4 WM4 ltac:(lia) DJO16 DJV WNS) as XSH4. clear XSH2.
    assert (SKSH4 : SK_shad m4 Ps (sk_fresh 0 id did)).
    { split; [| cbn; intros K0; exfalso; apply K0; reflexivity]. eapply addressable_acrossW; [exact (proj1 SKSH2)| exact MU4| exact WM4| pose proof (aapp_bounds _ _ SH7 ltac:(lia)); unfold SK_SIZE in *; lia| pose proof (aapp_bounds _ _ SH7 ltac:(lia)); unfold SK_SIZE in *; lia| exact WNS]. }
    clear FW2 SKSH2.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply adx_seg6; exact MI4|]. intros msF5 mo5 KREL5 MP5 VIS5. pose proof (ah_mpres_trans H HH _ _ _ MPc4 MP5) as MPc5.
    pose proof (askset_copy_thunks_spec H) as SC. unfold skset_copy_thunks_stmt, skset_stmt_at in SC.
    eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5| eapply SC with (lo := lo) (a := Ps); rewrite ?unsigned_lit by lia; try reflexivity;
                                   [unfold ADX_THUNK_COPY; lia| exact SO4| exact SKB| | | exact AC4| exact ST4| exact CEIL| clear - LO8K; lia| exact MI4]|].
    { destruct SKSH4 as [A B0]. split; [exact A| cbn; intros K0; exfalso; apply K0; reflexivity]. }
    { destruct SKR as [A B0]. split; [exact A| cbn; intros K0; exfalso; apply K0; reflexivity]. }
    clear SC. intros msF6 mo6 KREL6 MP6 (y0' & y1' & y2' & h1' & h2' & h3' & h4' & h5' & h6' & h7' & y3' & y4' & y5' & y6' & m6 & VIS6 & MU6 & WM6 & MI6 & AC6 & ST6 & SO6).
    pose proof (ah_mpres_trans H HH _ _ _ MPc5 MP6) as MPc6.
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in MU6, ST6 by lia.
    destruct (dworldX_munch _ _ _ _ _ _ _ _ _ _ _ _ id Ps SK_SIZE FW4 ltac:(left; reflexivity) MU6 WM6 MI6 ST6 AC6 WOK) as [FW6 TR6]. pose proof (TR6 _ _ XC4 DJO) as XC6. clear TR6 XC4.
    pose proof (EXT_shad_acrossW _ _ _ _ _ XSH4 MU6 WM6 ltac:(lia) DJO16 DJV WNS) as XSH6. clear XSH4.
    assert (SKSH6 : SK_shad m6 Ps (sk_fresh 0 id did)).
    { split; [| cbn; intros K0; exfalso; apply K0; reflexivity]. eapply addressable_acrossW; [exact (proj1 SKSH4)| exact MU6| exact WM6| pose proof (aapp_bounds _ _ SH7 ltac:(lia)); unfold SK_SIZE in *; lia| pose proof (aapp_bounds _ _ SH7 ltac:(lia)); unfold SK_SIZE in *; lia| exact WNS]. }
    clear FW4 SKSH4.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply adx_seg7; exact MI6|]. intros msF7 mo7 KREL7 MP7 VIS7. pose proof (ah_mpres_trans H HH _ _ _ MPc6 MP7) as MPc7.
    pose proof (askset_thunks_spec H) as SC. unfold skset_thunks_stmt, skset_stmt_at in SC.
    eapply (ahh_evt_then H HH); [exact KREL7| exact VIS7| eapply SC with (lo := lo) (a := Ps); rewrite ?unsigned_lit by lia; try reflexivity;
                                   [unfold ADX_THUNK_FREE; lia| exact SO6| exact SKB| | | exact AC6| exact ST6| exact CEIL| clear - LO8K; lia| exact MI6]|].
    { destruct SKSH6 as [A B0]. split; [exact A| cbn; intros K0; exfalso; apply K0; reflexivity]. }
    { destruct SKR as [A B0]. split; [exact A| cbn; intros K0; exfalso; apply K0; reflexivity]. }
    clear SC. intros msF8 mo8 KREL8 MP8 (y0'' & y1'' & y2'' & h1'' & h2'' & h3'' & h4'' & h5'' & h6'' & h7'' & y3'' & y4'' & y5'' & y6'' & m8 & VIS8 & MU8 & WM8 & MI8 & AC8 & ST8 & SO8).
    pose proof (ah_mpres_trans H HH _ _ _ MPc7 MP8) as MPc8.
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in MU8, ST8 by lia.
    destruct (dworldX_munch _ _ _ _ _ _ _ _ _ _ _ _ id Ps SK_SIZE FW6 ltac:(left; reflexivity) MU8 WM8 MI8 ST8 AC8 WOK) as [FW8 TR8]. pose proof (TR8 _ _ XC6 DJO) as XC8. clear TR8 XC6.
    pose proof (EXT_shad_acrossW _ _ _ _ _ XSH6 MU8 WM8 ltac:(lia) DJO16 DJV WNS) as XSH8. clear XSH6.
    assert (SKSH8 : SK_shad m8 Ps (sk_fresh 0 id did)).
    { split; [| cbn; intros K0; exfalso; apply K0; reflexivity]. eapply addressable_acrossW; [exact (proj1 SKSH6)| exact MU8| exact WM8| pose proof (aapp_bounds _ _ SH7 ltac:(lia)); unfold SK_SIZE in *; lia| pose proof (aapp_bounds _ _ SH7 ltac:(lia)); unfold SK_SIZE in *; lia| exact WNS]. }
    clear FW6 SKSH6.
    set (K3 := sk_with_thunk (sk_with_thunk (sk_with_thunk (sk_fresh 0 id did) O_SK_CMPTH ADX_THUNK_CMP) O_SK_COPYTH ADX_THUNK_COPY) O_SK_FREETH ADX_THUNK_FREE) in *.
    (* [comment removed for export] *)
    pose proof FW8 as (MI8' & AC8' & ST8' & FR8 & ERR8 & AUX8 & HP8 & LM8 & EO8 & ESH8 & _ & _ & PK8' & PIN8 & CR8 & _ & BS8 & ACCB8 & ACCP8 & SK08 & RFS8 & XP08 & ALG8).
    destruct (dworld_entry _ _ _ _ _ _ _ _ _ _ FW8) as (pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC8 & EEP & EEH & EAP & E16 & _).
    pose proof ESH8 as (ETOP & EAD8 & ES1 & ES2 & ES3 & ES4 & _). rewrite EW0 in ES1, ES2, ES3, ES4.
    assert (ACCE8 : accessible m8 (ee + 56) 8) by (eapply addressable_accessible; [exact EAD8| lia| unfold ENTRY_SIZE; lia| exact ETOP]).
    eapply (ahh_evt_then H HH); [exact KREL8| exact VIS8| eapply (adx_seg8) with (ee := ee) (P := Ps) (E := EW 0 None);
                                   [exact EC8| lia| exact ETOP| clear - PSP SH5 ACEILB; unfold AAPP_HI; lia| exact ACCE8| exact MI8]|].
    intros msF9 mo9 KREL9 MP9 (m9 & MU9 & WM9 & MI9 & EC9 & VIS9). pose proof (ah_mpres_trans H HH _ _ _ MPc8 MP9) as MPc9.
    cbn [EW en_version en_pname en_pname_o en_publen en_pub en_pub_o en_nsuites en_suites en_suites_o en_maxname en_cfgid en_exts_o en_loadtime en_forretry en_enclen en_encoded en_encoded_o en_id] in EC9.
    unfold ENTRY_SIZE in MU9.
    (* [comment removed for export] *)
    pose proof (dworldX_blocks _ _ _ _ _ _ _ _ _ _ FW8) as HB8.
    assert (EIN8 : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M ++ (SB :: XB) ++ [] ++ LB)) by (do 3 (apply in_or_app; right); exact EIN0).
    pose proof (ah_blocks H HH _ _ _ _ HP8 EIN8) as (_ & _ & _ & _ & _ & EFS & _). cbn [blk_addr blk_size fst snd] in EFS. unfold ENTRY_SIZE in EFS.
    assert (DJE : forall b, In b (mid_errblocks M ++ (SB :: XB) ++ [] ++ LB) -> blk_id b <> en_id E -> blk_addr b + blk_size b + 16 <= ee \/ ee + 104 + 16 <= blk_addr b).
    { intros b Hb NE. pose proof (ah_disj H HH _ _ _ _ _ HP8 Hb EIN8 NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ. unfold ENTRY_SIZE in DJ. exact DJ. }
    pose proof (ah_nodup H HH _ _ _ HP8) as ND8.
    assert (NEX : forall b, In b (mid_errblocks M ++ (SB :: XB)) -> blk_id b <> en_id E).
    { intros b Hb K0. rewrite (app_assoc _ _ ([] ++ LB)) in ND8. cbn [app] in ND8. exact (nodup_ids_app_ne _ _ _ _ ND8 Hb EIN0 K0). }
    assert (WE : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(ee, ee + 104)]).
    { constructor; [| constructor]. cbn [fst snd]. pose proof (aapp_not_shadowland _ _ EAP). unfold ENTRY_SIZE in *. lia. }
    assert (CWE : Forall (aclient_write_ok H (mid_errblocks M ++ (SB :: XB) ++ [] ++ LB)) [(ee, ee + 104)]).
    { constructor; [| constructor]. right; right; left. exists (en_id E, ee, ENTRY_SIZE). split; [exact EIN8| cbn; unfold ENTRY_SIZE; lia]. }
    assert (XPE : forall X, xpres H (as_lb_remove H (en_id E) (mid_errblocks M ++ (SB :: XB) ++ [] ++ LB)) (bv_unsigned sp + -144) X m8 m9).
    { intros X. eapply (xpres_of_munch_listed H HH); [exact HP8| exact EIN8| clear - CEIL LO8K; lia| exact MU9| exact WM9|]. constructor; [right; left; cbn; unfold ENTRY_SIZE; lia| constructor]. }
    assert (REME : forall b, In b (mid_errblocks M ++ (SB :: XB) ++ [] ++ LB) -> blk_id b <> en_id E -> In b (as_lb_remove H (en_id E) (mid_errblocks M ++ (SB :: XB) ++ [] ++ LB))).
    { intros b Hb NE. apply (proj2 (proj2 (proj2 (alb_remove_exact H HH _ _ _ _ ND8 EIN8)) b)). split; [exact Hb| exact NE]. }
    assert (EAD9 : addressable m9 ee ENTRY_SIZE).
    { eapply addressable_acrossW; [exact EAD8| exact MU9| exact WM9| clear - EEP EEH ACEILB; unfold AAPP_HI, ENTRY_SIZE in *; lia| exact ETOP| exact WE]. }
    pose proof OF0 as (Q1 & Q2 & Q3 & Q4).
    assert (OSx : forall Pf o, ofield LB Pf o -> oshad m8 Pf o -> oshad m9 Pf o).
    { intros Pf o OFo OSo. destruct o as [[i1 n1]|]; [| exact I]. cbn [ofield] in OFo. destruct OFo as (OP1 & ON1 & IN1).
      assert (IN1' : In (i1, Pf, n1) (mid_errblocks M ++ (SB :: XB) ++ [] ++ LB)) by (do 3 (apply in_or_app; right); exact IN1).
      pose proof (HB8 _ IN1') as (_ & _ & W5 & _). cbn [blk_addr blk_size fst snd] in W5.
      destruct (Z.eq_dec i1 (en_id E)) as [EQ|NE].
      - pose proof (nodup_ids_same _ _ _ ND8 IN1' EIN8 EQ) as EB. injection EB as En Ee. subst Pf n1.
        cbn [oshad]. split; [exact ETOP|]. split; [exact EAD9|]. eexists. unfold ENTRY_SIZE.
        match type of EC9 with rw_cells _ _ _ ?cs => replace 104 with (Z.of_nat (cells_size cs)) by reflexivity; rewrite Nat2Z.id || idtac end.
        replace (Z.to_nat (Z.of_nat _)) with (cells_size (entry_cells (mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
                      (en_maxname E) (en_cfgid E) Ps None (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E)) pad1 pad2 pad3 pad4)) by (rewrite Nat2Z.id; reflexivity).
        apply rw_cells_as_CB. exact EC9.
      - eapply oshad_acrossW; [exact OSo| exact MU9| exact WM9| | exact WE].
        pose proof (DJE _ IN1' NE) as DJ1. cbn [blk_addr blk_size fst snd] in DJ1. cbn. unfold AAPP_HI. clear - OP1 ON1 W5 ACEILB DJ1. lia. }
    assert (FW9 : dworldX m9 s2' errv2 Ps (Some (K3, [])) [SB] c cur rem XB).
    { unfold dworldX. cbv delta [spq]. repeat match goal with |- _ /\ _ => split end; try assumption.
      all: lazymatch goal with
           | |- ACONST _ => eapply ACONST_frame; [exact AC8'| exact MU9| exact WM9|]; apply Forall_cons; [eapply aconst_ok_aapp; [exact EAP| lia| unfold ENTRY_SIZE; lia]| apply Forall_nil]
           | |- stk _ _ _ _ => eapply stk_transport_disjoint; [exact ST8'| exact MU9| exact WM9| cbn; clear - EEH CEIL LO8K ACEILB; unfold ENTRY_SIZE in *; lia]
           | |- rw_cells _ _ (bv_unsigned sp + -144) _ => eapply rw_cells_transport; [exact FR8| exact MU9| exact WM9| cbn; clear - EEH CEIL LO8K; unfold ENTRY_SIZE in *; lia]
           | |- rw_cells _ _ (errno_addr _) _ => rewrite TP in ERR8 |- *; eapply rw_cells_transport; [exact ERR8| exact MU9| exact WM9|]; rewrite unsigned_lit by (unfold ATP; lia); cbn;
                                                 pose proof (aapp_bounds _ _ EAP ltac:(unfold ENTRY_SIZE; lia)) as (QQ1 & _); unfold ATP, AIMG_TOP in *; clear - QQ1; lia
           | |- as_rauxv_ok _ _ _ => eapply (ah_rauxv_frame H HH); [exact AUX8| exact MU9| exact WM9| exact CWE]
           | |- as_RHEAP _ _ _ _ =>
               eapply (HHx_rheap_perm H HHx); [eapply (ah_RHEAP_frame H HH); [exact HP8| exact MU9| exact WM9| exact CWE]|];
               cbn [app]; apply Permutation_app_head; change (SB :: XB ++ LB) with ([SB] ++ XB ++ LB); rewrite (app_assoc [SB] XB); rewrite (app_assoc XB [SB]); apply Permutation_app_tail; apply Permutation_app_comm
           | |- LIBMID _ _ _ =>
               eapply (LIBMID_xpres0 H); [exact LM8| exact CX| apply XPE| |];
               [ intros b Hb; apply REME; [do 3 (apply in_or_app; right); apply LIBSUB; exact Hb| exact (IDS _ _ Hb ltac:(left; reflexivity))]
               | intros b Hb; apply REME; [apply in_or_app; left; exact Hb| apply NEX; apply in_or_app; left; exact Hb] ]
           | |- ENTRYobj _ _ _ _ =>
               unfold ENTRYobj; cbn [EW en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o];
               split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact EC9]|];
               split; [apply in_or_app; right; exact EIN0|];
               split; [eapply ofield_LB_mono; [exact Q1| intros b Hb; apply in_or_app; right; exact Hb]|];
               split; [eapply ofield_LB_mono; [exact Q2| intros b Hb; apply in_or_app; right; exact Hb]|];
               split; [eapply ofield_LB_mono; [exact Q3| intros b Hb; apply in_or_app; right; exact Hb]|];
               split; [eapply ofield_LB_mono; [exact Q4| intros b Hb; apply in_or_app; right; exact Hb]|];
               unfold EXTS; split; [exact PSP|]; split; [| split; [reflexivity| apply Forall2_nil]];
               eapply SKobj_LB_mono; [| intros b Hb; apply in_or_app; left; exact Hb];
               eapply (SKobj_frame H _ [SB] (bv_unsigned sp + -144)); [exact SO8| intros b Hb; subst K3; rewrite !e_blocks_SK_with_thunk in Hb; unfold blocks_SK in Hb; cbn in Hb; destruct Hb as [Hb|[]]; left; exact Hb|];
               eapply (xpres_weaken H); [apply (XPE [])| lia| | intros q Hq; exact Hq];
               intros b [<-|[]]; apply REME; [apply in_or_app; right; apply in_or_app; left; left; reflexivity| apply NEX; apply in_or_app; right; left; reflexivity]
           | |- ENTRY_shad _ _ _ =>
               unfold ENTRY_shad; cbn [EW en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o EXTS_shad SKX_shad];
               split; [exact ETOP|]; split; [exact EAD9|];
               split; [exact (OSx _ _ Q1 ES1)|]; split; [exact (OSx _ _ Q2 ES2)|]; split; [exact (OSx _ _ Q3 ES3)|]; split; [exact (OSx _ _ Q4 ES4)|];
               split; [| apply Forall2_nil];
               split; [| split; [clear - SH5 ACEILB; unfold SK_SIZE, AAPP_HI; lia| subst K3; cbn; intros K0; exfalso; apply K0; reflexivity]];
               split; [| subst K3; cbn; intros K0; exfalso; apply K0; reflexivity];
               eapply addressable_acrossW; [exact (proj1 SKSH8)| exact MU9| exact WM9| clear - PSP SH5 ACEILB; unfold AAPP_HI; lia| clear - SH5 ACEILB; unfold SK_SIZE, AAPP_HI; lia| exact WE]
           | |- Permutation _ _ => unfold blocks_EXTS; subst K3; rewrite !e_blocks_SK_with_thunk, !e_sk_elems_with_thunk; unfold blocks_SK; cbn; apply Permutation_refl
           | |- XINV _ _ _ => unfold XINV, EBof; subst K3; rewrite !e_sk_elems_with_thunk; cbn -[Z.mul Z.add Z.le]; unfold zlength; cbn [length Z.of_nat]; clear - CB1; lia
           | |- rw_cells _ _ pk _ => eapply rw_cells_transport; [exact PK8'| exact MU9| exact WM9| cbn; clear - EEH CEIL LO8K SPK; unfold ENTRY_SIZE in *; lia]
           | |- bytes_at _ _ base _ =>
               eapply bytes_at_transport; [exact BS8| exact MU9|]; cbn; split; [| exact I];
               pose proof (DJE (pbin, base, len) ltac:(do 3 (apply in_or_app; right); exact BIN) ltac:(cbn; intros K0; apply EBIN; symmetry; exact K0)) as KKq; cbn [blk_addr blk_size fst snd] in KKq;
               clear - KKq BSL'; lia
           | |- accessible _ base _ => eapply accessible_across; [exact ACCB8| exact MU9| exact WE]
           | |- accessible _ pk _ => eapply accessible_across; [exact ACCP8| exact MU9| exact WE]
           | |- stack0 _ _ _ => eapply stack0_transport; [exact SK08| exact MU9| exact WM9|]; apply Forall_cons; [eapply stack0_ok_aapp; [exact EAP| lia| unfold ENTRY_SIZE; lia]| apply Forall_nil]
           | |- as_RFS _ _ _ => eapply (ah_RFS_frame H HH); [exact RFS8| exact MU9| exact WM9|]; apply Forall_cons; [| apply Forall_nil]; left; cbn [fst snd];
                                pose proof (aapp_bounds _ _ EAP ltac:(unfold ENTRY_SIZE; lia)) as (QQ1 & _); unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; clear - QQ1 EFS; lia
           | |- xpres H LB _ X0 m0 _ =>
               eapply (xpres_trans H); [exact XP08|];
               eapply (xpres_weaken H); [| apply Z.le_refl| intros b Hb; do 3 (apply in_or_app; right); exact Hb| intros q Hq; exact Hq];
               eapply (xpres_of_munch H _ (mid_errblocks M ++ (SB :: XB) ++ [] ++ LB)); [exact HH| exact HP8| exact MU9| exact WM9|];
               apply Forall_cons; [right; cbn; intros q Hq; unfold X0, ENTRY_SIZE; cbn [rin_ivs fst snd]; right; left; exact Hq| apply Forall_nil]
           | |- ALED _ _ _ _ => destruct ALG8 as (um8 & uf8 & W1 & W2 & W3); exists um8, uf8; cbn [xs_len xs_base] in W1, W2 |- *; rewrite lb_bytes_cons in W1; subst SB; cbn [blk_size snd] in W1;
                                unfold zlength, SK_SIZE in *; cbn [length Z.of_nat] in *; split; [clear - W1; lia| split; [clear - W2; lia| exact W3]]
           | |- ?G => idtac "NSK9" G
           end. }
    pose proof (proj1 (proj1 XC8)) as WF. cbn [cells_wf cell_wf ext_cells] in WF.
    eapply dx_push; [exact FW9| exact PL| | exact VO| exact XL| exact CLE| | exact KREL9| exact MPc9| exact VIS9].
    - eapply rw_cells_transport; [exact XC8| exact MU9| exact WM9|]. unfold ext_cells. cbn [cells_size csize Nat.add length]. cbn. split; [| exact I].
      pose proof (DJE (ex_id X', Ao, EXT_SIZE) ltac:(apply in_or_app; right; apply in_or_app; left; right; subst XB; left; reflexivity) (NEX _ ltac:(apply in_or_app; right; right; subst XB; left; reflexivity))) as DJ2.
      cbn [blk_addr blk_size fst snd] in DJ2. unfold EXT_SIZE in DJ2. clear - DJ2. lia.
    - eapply EXT_shad_acrossW; [exact XSH8| exact MU9| exact WM9| lia| | | exact WE].
      + cbn. split; [| exact I].
        pose proof (DJE (ex_id X', Ao, EXT_SIZE) ltac:(apply in_or_app; right; apply in_or_app; left; right; subst XB; left; reflexivity) (NEX _ ltac:(apply in_or_app; right; right; subst XB; left; reflexivity))) as DJ2.
        cbn [blk_addr blk_size fst snd] in DJ2. unfold EXT_SIZE in *. clear - DJ2. lia.
      + revert VO. pose proof DJV as DJV'. revert DJV'. subst XB. unfold blocks_EXT, blocks_of in DJE, NEX. destruct (ex_val_o X') as [[iv nv]|]; intros DJV' VO; [| exact I].
        destruct DJV' as [V0 _]. split; [exact V0|]. cbn. split; [| exact I].
        pose proof (DJE (iv, ex_val X', nv) ltac:(apply in_or_app; right; apply in_or_app; left; right; right; left; reflexivity) (NEX _ ltac:(apply in_or_app; right; right; right; left; reflexivity))) as DJ3.
        cbn [blk_addr blk_size fst snd] in DJ3. clear - DJ3. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_from_malloc : forall m s' errv' P xs NB c cur rem (val xl b0 b1 : Z) (vo : oblk) msF mo' (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x6 : word),
    dworldX m s' errv' P xs NB c cur rem (blocks_of val vo) ->
    match vo with None => val = 0 | Some (pv, n) => 0 < val /\ 1 <= n <= xl end ->
    0 <= xl < 512 -> 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= val < 2^64 -> c + 4 + xl <= rem0 - rem ->
    oshad m val vo ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR (Z_to_bv 64 ADX_R3) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 b1) (Z_to_bv 64 16) (Z_to_bv 64 ADX_FILE_ECHS) (Z_to_bv 64 217) a3 a4 a5 a6 a7
                (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                x6 (Z_to_bv 64 xl) (Z_to_bv 64 val) (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) (Z_to_bv 64 b0) t3 t4 t5 t6)
           F (Z_to_bv 64 P_CRYPTO_malloc) fc None m (seg_rom asegs) ->
    as_SR H (at_head rem) (mkCfg msF mo').
  Proof.
    intros m s' errv' P xs NB c cur rem val xl b0 b1 vo msF mo' t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x6 FW VO XL B0 B1 VR CLE VSH KREL MP VIS.
    pose proof (dworldX_chain _ _ _ _ _ _ _ _ _ _ FW) as CHN. pose proof (dworldX_blocks _ _ _ _ _ _ _ _ _ _ FW) as HB.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & ACCB & ACCP & SK0 & RFS & XP0 & ALG).
    cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. pose proof BSL as BSL'. unfold zlength in BSL'.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & ESHD & EBL). rewrite MF0 in MF.
    set (VL := blocks_of val vo) in *. set (Lp := mid_errblocks M ++ VL ++ NB ++ LB) in *.
    assert (VLB : lb_bytes VL <= xl /\ Z.of_nat (length VL) <= 1).
    { subst VL. unfold blocks_of. destruct vo as [[pv n]|]; rewrite ?lb_bytes_cons; cbn [blk_size snd length lb_bytes fold_right]; lia. }
    destruct VLB as (VLB & VLL). unfold zlength in *.
    (* [comment removed for export] *)
    assert (NBB : lb_bytes NB <= 88 + 8 * c /\ 5 * Z.of_nat (length NB) <= 2 * c + 10).
    { revert PB XI. unfold XINV. destruct xs as [[K es]|]; intros PB XI.
      - destruct XI as (KC & K4 & KCAP & E5 & EBY). rewrite blocks_EXTS_some in PB.
        pose proof (blocks_SK_facts P K ltac:(lia)) as (SKB & SKL & _ & _).
        rewrite <- (lb_bytes_perm _ _ PB), <- (Permutation_length PB), lb_bytes_app, length_app, Nat2Z.inj_add.
        unfold SK_SIZE in SKB. unfold zlength in *. clear - K4 KCAP E5 EBY SKB SKL. lia.
      - destruct XI as [_ C0]. pose proof (Permutation_nil PB) as ->. cbn. clear - C0. lia. }
    destruct NBB as (NBB & NBL).
    (* [comment removed for export] *)
    destruct ALG as (um & uf & U1 & U2 & U3).
    assert (RC0 : 0 <= RAISE_COST H (mid_err M)).
    { unfold RAISE_COST. pose proof (errph_nonneg (mid_err M)) as [EB0 _]. pose proof (aCm_pos H HH (raise_bytes (mid_err M)) ltac:(unfold raise_bytes, ERRDEBUG_BYTES; lia)).
      pose proof (aCf_pos H HH (errph_bytes (mid_err M) + ERRDEBUG_BYTES) ltac:(unfold ERRDEBUG_BYTES; lia)). lia. }
    assert (XSL : 0 <= xs_len xs /\ 4 * xs_len xs <= c /\ 0 <= xs_base xs <= SK_SIZE).
    { revert XI. unfold XINV, xs_len, xs_base. destruct xs as [[K es]|]; intros XI; [destruct XI as (_ & K4 & _); unfold zlength, SK_SIZE in *; lia| unfold SK_SIZE; lia]. }
    assert (HAL : as_Cm H 16 <= as_AL H s').
    { pose proof (aCm_super H HH um 16 ltac:(lia) ltac:(lia)) as SCM.
      pose proof (aCm_mono H HH (um + 16) (DECEXTS_CM rem0) ltac:(unfold DECEXTS_CM, ADX_PER_EXT, ADX_PUSH_CM, SK_SIZE in *; clear - U1 VLB XSL CLE XL CB1 CB2 PIN; unfold pk_in in PIN; lia)) as MCM.
      pose proof (aCf_mono H HH uf (DECEXTS_CF rem0) ltac:(unfold DECEXTS_CF, ADX_PUSH_CF in *; clear - U2 XSL CB1 CB2 PIN REM1; unfold pk_in in PIN; lia)) as MCF.
      unfold DECEXTS_COST in HAL0. clear - HAL0 U3 SCM MCM MCF RC0. lia. }
    (* [comment removed for export] *)
    pose proof (acmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
    eapply (ah_seq H HH).
    { eapply CM with (lo := lo) (B := B) (LB := Lp) (s := s') (n := 16) (v := 1) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH); [exact VIS| reflexivity| ..];
        rewrite ?unsigned_lit by (unfold ADX_R3; lia).
      all: try first [exact HP| exact KREL| exact AUX| exact ST| exact CEIL| exact MI| exact TP| exact MF| exact IM| exact G1| exact AC| exact CHN| exact HAL].
      all: lazymatch goal with
           | |- 1 <= 16 <= _ => lia
           | |- lb_bytes _ + _ <= _ => subst Lp; rewrite !lb_bytes_app in *; unfold DECEXTS_BYTES, ERRDEBUG_BYTES in *;
                                        pose proof (errph_nonneg (mid_err M)) as [EB0 _]; clear - BY EB0 VLB NBB XL CLE CB1 CB2 PIN REM1; unfold pk_in in PIN; lia
           | |- Z.of_nat (length _) + _ <= _ => subst Lp; rewrite !length_app, !Nat2Z.inj_add in *; pose proof (errph_nonneg (mid_err M)) as [_ EC0]; clear - CN EC0 VLL NBL CLE CB2 PIN XL Q5; unfold pk_in in PIN; lia
           | |- _ <= B => clear - SPB SPR; lia
           | |- _ mod 16 = 0 => clear - SPA SPR; replace (bv_unsigned sp + -144) with (bv_unsigned sp - 9 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
           | |- _ <= _ - CMALLOC_STACK => clear - LO; unfold DECEXTS_STACK, FR_ech_decode_echconfig_exts, SKPUSH_STACK, SKRESERVE_STACK, CARRAY_STACK, CREALLOC_ARRAY_STACK, CREALLOC_STACK,
                              FR_sk_insert, FR_sk_reserve, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, FR_CRYPTO_array, FR_CRYPTO_realloc in LO |- *; lia
           | |- rw_cells _ _ (errno_addr _) _ => exact ERR
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - SPR; lia| specialize (CHS _ _ Hin); clear - CHS; lia]
           | |- pf_ok _ _ _ _ => pf_site
           | |- ?G => idtac "CMPRE" G
           end. }
    clear CM. intros [ms2 mo2] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m2 & errv2 & Ao & junk & po & s2' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & OBR & HP2 & OC2 & OAD2 & MF2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in ST2, XP2 by lia.
    pose proof (ah_mpres_trans H HH _ _ _ MP MP2) as MPc2.
    subst Lp. destruct (dworldX_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FW MI2 AC2 ST2 ERR2 AUX2 XP2 HP2 MF2 ltac:(lia) AL2) as (FW2 & TR2 & TRa2 & _).
    pose proof OBR as (OP & O16 & _ & O4lo & OH & OFS & OAP). change (Z.to_nat 16) with 16%nat in OC2.
    assert (OAL8 : Ao mod 8 = 0) by (clear - O16; Z.div_mod_to_equations; lia).
    assert (VSH2 : oshad m2 val vo).
    { revert VSH VO. subst VL. unfold blocks_of in TR2, TRa2. destruct vo as [[iv nv]|]; intros VSH VO; [| exact I].
      cbn [oshad] in VSH |- *. destruct VSH as (T1 & A1 & bs1 & C1). split; [exact T1|]. split.
      - eapply TRa2; [apply in_or_app; left; left; reflexivity| exact A1| cbn; lia| cbn; lia].
      - exists bs1. eapply TR2; [apply in_or_app; left; left; reflexivity| exact C1| cbn; lia| cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; lia]. }
    clear TR2 TRa2.
    (* [comment removed for export] *)
    destruct (dworld_entry _ _ _ _ _ _ _ _ _ _ FW2) as (pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC2 & EEP & EEH & EAP & E16 & PR & _).
    pose proof FW2 as (_ & _ & _ & FR2 & _ & _ & _ & _ & _ & ESH2 & _). pose proof ESH2 as (ETOP & EAD & _).
    assert (EIN2 : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M ++ VL ++ NB ++ LB)) by (do 3 (apply in_or_app; right); exact EIN0).
    pose proof (ah_disj H HH _ _ _ (po, Ao, 16) (en_id E, ee, ENTRY_SIZE) HP2 (or_introl eq_refl) (or_intror EIN2) (afresh_id_ne H HH _ _ _ _ _ _ (en_id E) HP2 (in_map blk_id _ _ EIN2))) as DEO.
    cbn [blk_addr blk_size fst snd] in DEO. unfold ENTRY_SIZE in DEO, EEH.
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply adx_seg4 with (E := EW P xs) (oe := Ao) (val := val) (x0 := b0) (x1 := b1) (extlen := xl);
      [exact EC2| lia| exact ETOP| cbn [EW en_exts]; exact PR| exact OC2| exact OP| unfold ENTRY_SIZE; clear - DEO; lia| clear - OH CEIL LO8K; lia
      | exact (aapp_not_shadowland _ _ OAP)| eapply addressable_accessible; [exact OAD2| lia| lia| pose proof (aapp_bounds _ _ OAP ltac:(lia)); lia]
      | eapply addressable_accessible; [exact EAD| lia| unfold ENTRY_SIZE; lia| exact ETOP]
      | exact B0| exact B1| exact XL| exact VR| exact OAL8| exact FR2| clear - LO8K CEIL ACEILB; lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 (m3 & jk & a0' & a1' & MU3 & WM3 & MI3 & XC3 & CASES). cbn [EW en_exts] in CASES. pose proof (ah_mpres_trans H HH _ _ _ MPc2 MP3) as MPc3.
    assert (ST3 : stk asegs m3 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]. cbn. clear - OH CEIL. lia. }
    assert (AC3 : ACONST m3).
    { eapply ACONST_frame; [exact AC2| exact MU3| exact WM3|]. apply Forall_cons; [eapply aconst_ok_aapp; [exact OAP| lia| lia]| apply Forall_nil]. }
    destruct (dworldX_munch _ _ _ _ _ _ _ _ _ _ _ _ po Ao 16 FW2 ltac:(left; reflexivity) MU3 WM3 MI3 ST3 AC3
                ltac:(apply Forall_cons; [right; cbn; lia| apply Forall_nil])) as [FW3 _].
    pose proof (proj1 (proj1 XC3)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & _ & LJ & _).
    set (X' := mkEXT (256 * b0 + b1) xl val vo po).
    assert (XBE : (po, Ao, 16) :: VL = blocks_EXT Ao X') by (subst VL X'; reflexivity).
    assert (XCE : rw_cells asegs m3 Ao (ext_cells X' jk)) by (subst X'; unfold ext_cells; cbn [ex_type ex_len ex_val]; exact XC3).
    assert (WNS3 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(Ao, Ao + 16)]).
    { apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ OAP)| apply Forall_nil]. }
    assert (XSH3 : EXT_shad m3 Ao X').
    { subst X'. unfold EXT_shad. cbn [ex_val ex_val_o]. split; [pose proof (aapp_bounds _ _ OAP ltac:(lia)); unfold EXT_SIZE; lia|]. split.
      - eapply addressable_acrossW; [exact OAD2| exact MU3| exact WM3| pose proof (aapp_bounds _ _ OAP ltac:(lia)); lia| pose proof (aapp_bounds _ _ OAP ltac:(lia)); unfold EXT_SIZE; lia| exact WNS3].
      - eapply oshad_acrossW; [exact VSH2| exact MU3| exact WM3| | exact WNS3].
        revert VO. subst VL. unfold blocks_of in HP2, HB. destruct vo as [[iv nv]|]; intros VO; [| exact I].
        assert (VIN : In (iv, val, nv) ((po, Ao, 16) :: mid_errblocks M ++ [(iv, val, nv)] ++ NB ++ LB)) by (right; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
        pose proof (ah_blocks H HH _ _ _ _ HP2 VIN) as (V1 & _ & V3 & _ & V5 & _). cbn [blk_addr blk_size fst snd] in V1, V3, V5.
        assert (VIN' : In (iv, val, nv) (mid_errblocks M ++ [(iv, val, nv)] ++ NB ++ LB)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
        pose proof (ah_disj H HH _ _ _ (po, Ao, 16) (iv, val, nv) HP2 (or_introl eq_refl) VIN (afresh_id_ne H HH _ _ _ _ _ _ iv HP2 (in_map blk_id _ _ VIN'))) as DV.
        cbn [blk_addr blk_size fst snd] in DV. cbn. unfold AAPP_HI. clear - V1 V3 V5 DV ACEILB. lia. }
    pose proof FW3 as (_ & _ & _ & _ & _ & _ & _ & _ & EO3 & _). pose proof EO3 as (_ & _ & _ & _ & _ & _ & XS3). cbn [EW en_exts en_exts_o] in XS3.
    destruct CASES as [[P0 VIS3]|[PP VIS3]].
    - (* [comment removed for export] *)
      assert (XN : xs = None) by (destruct xs as [[K es]|]; [exfalso; unfold EXTS in XS3; destruct XS3 as [K0 _]; clear - K0 P0; lia| reflexivity]).
      subst xs. rewrite P0 in FW3. rewrite XBE in FW3.
      pose proof FW3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB3 & _). cbn [blocks_EXTS] in PB3. pose proof (Permutation_nil PB3) as NBN. rewrite NBN in FW3.
      eapply (dx_newsk _ _ _ _ _ _ X'); [exact FW3| exact LJ| exact XCE| subst X'; cbn [ex_val_o ex_val ex_len]; exact VO| subst X'; cbn [ex_len]; exact XL| subst X'; cbn [ex_len]; exact CLE
                                         | exact XSH3| exact KREL3| exact MPc3| exact VIS3].
    - (* [comment removed for export] *)
      destruct xs as [[K es]|]; [| exfalso; unfold EXTS in XS3; clear - XS3 PP; lia].
      rewrite XBE in FW3.
      eapply (dx_push _ _ _ _ _ _ _ _ _ _ X'); [exact FW3| exact LJ| exact XCE| subst X'; cbn [ex_val_o ex_val ex_len]; exact VO| subst X'; cbn [ex_len]; exact XL| subst X'; cbn [ex_len]; exact CLE
                                                  | exact XSH3| exact KREL3| exact MPc3| exact VIS3].
  Qed.

  (* [comment removed for export] *)
  Lemma dworldX_call0 : forall m m' s' s'' errv' errv'' P xs NB c cur rem XB,
    dworldX m s' errv' P xs NB c cur rem XB ->
    mem_inv asegs m' -> ACONST m' -> stk asegs m' lo spq ->
    rw_cells asegs m' (errno_addr tp) [C4 errv''] -> as_rauxv_ok H m' B ->
    xpres H (mid_errblocks M ++ XB ++ NB ++ LB) spq [] m m' ->
    as_RHEAP H s'' (mid_errblocks M ++ XB ++ NB ++ LB) m' -> as_AL H s'' >= as_AL H s' - as_Cf H 0 ->
    dworldX m' s'' errv'' P xs NB c cur rem XB.
  Proof.
    intros m m' s' s'' errv' errv'' P xs NB c cur rem XB FW MI' AC' ST' ERR' AUX' XP HP' AL'.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & ACCB & ACCP & SK0 & RFS & XP0 & ALG).
    pose proof (dworldX_blocks _ _ _ _ _ _ _ _ _ _ FW) as HB. clear FW.
    unfold dworldX. cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. pose proof BSL as BSL'. unfold zlength in BSL'.
    set (Lp := mid_errblocks M ++ XB ++ NB ++ LB) in *.
    assert (SUBNL : forall b, In b (NB ++ LB) -> In b Lp) by (intros b Hb; subst Lp; do 2 (apply in_or_app; right); exact Hb).
    assert (XPL : forall X, xpres H (NB ++ LB) (bv_unsigned sp + -144) X m m').
    { intros X. eapply (xpres_weaken H); [exact XP| lia| exact SUBNL| intros a Ha; destruct Ha]. }
    rewrite (aCf0 H HH) in AL'.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply (xpres_rw_cells' H); [exact XP| exact FR| left; lia| constructor].
    - eapply (LIBMID_xpres0 H); [exact LM| exact CX| exact XP| intros b Hb; apply SUBNL; apply in_or_app; right; apply LIBSUB; exact Hb| intros b Hb; subst Lp; apply in_or_app; left; exact Hb].
    - eapply (ENTRYobj_frame_law H); [exact EO| intros b Hb; eapply ENTRYobj_owned_law; [exact EO| exact Hb]| apply XPL|].
      intros b Hb. pose proof (HB b (SUBNL _ ltac:(eapply ENTRYobj_owned_law; [exact EO| exact Hb]))) as (_ & _ & K5 & _). lia.
    - eapply (ENTRY_shad_frame_law H); [exact ESH| intros b Hb; eapply ENTRYobj_owned_law; [exact EO| exact Hb]| apply XPL|].
      intros b Hb. pose proof (HB b (SUBNL _ ltac:(eapply ENTRYobj_owned_law; [exact EO| exact Hb]))) as (_ & _ & K5 & _). lia.
    - eapply (xpres_rw_cells' H); [exact XP| exact PK| left; clear - SPK; lia| constructor].
    - eapply (xpres_bytes_at' H); [apply (XPL [])| exact BS| | constructor]. right; right; left. exists (pbin, base, len). split; [apply in_or_app; right; exact BIN| cbn [blk_addr blk_size fst snd]; lia].
    - eapply (ashobj_accessible_xpres_sub H HH) with (SP := bv_unsigned sp + -144) (X := @nil (Z * Z)); [exact HP| intros b Hb; exact Hb| clear - CEIL LO8K; lia| | exact ACCB| exact XP| constructor].
      left. exists (pbin, base, len). split; [apply SUBNL; apply in_or_app; right; exact BIN| cbn [blk_addr blk_size fst snd]; lia].
    - eapply (ashobj_accessible_xpres_sub H HH) with (SP := bv_unsigned sp + -144) (X := @nil (Z * Z)); [exact HP| intros b Hb; exact Hb| clear - CEIL LO8K; lia| | exact ACCP| exact XP| constructor].
      right; right. clear - SPK. lia.
    - eapply (stack0_xpres H); [exact XP| exact SK0| constructor].
    - eapply (RFS_via_xpres H HH); [exact RFS| exact XP| constructor].
    - eapply (xpres_trans H); [exact XP0|]. eapply (xpres_weaken H); [exact XP| clear - SPR; lia| intros b Hb; subst Lp; do 3 (apply in_or_app; right); exact Hb| intros a Ha; destruct Ha].
    - destruct ALG as (um & uf & U1 & U2 & U3). exists um, uf. split; [exact U1|]. split; [exact U2|]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_at_sub : forall m A zs i n,
    bytes_at asegs m A zs -> 0 <= i -> 0 <= n -> i + n <= Z.of_nat (length zs) ->
    bytes_at asegs m (A + i) (firstn (Z.to_nat n) (skipn (Z.to_nat i) zs)) /\ Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) zs))) = n.
  Proof.
    clear. intros m A zs i n BS I0 N0 LE.
    rewrite <- (firstn_skipn (Z.to_nat i) zs) in BS. apply bytes_at_app in BS. destruct BS as [_ BS].
    rewrite firstn_length_le in BS by lia. rewrite Z2Nat.id in BS by lia.
    rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) zs)) in BS. apply bytes_at_app in BS. destruct BS as [BS _].
    split; [exact BS|]. rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_trip : forall m s' errv' P xs NB c rem' (cd xl b0 b1 : Z) msF mo' (t0 t1 t2 a3 a4 a5 x8 t3 t4 t5 t6 : word),
    dworldX m s' errv' P xs NB c (cd + xl) rem' [] ->
    0 <= xl < 512 -> 0 <= b0 < 256 -> 0 <= b1 < 256 -> c + 4 + xl <= rem0 - rem' -> base <= cd - 4 ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR (Z_to_bv 64 ADX_R1) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 b1) (Z_to_bv 64 0) (Z_to_bv 64 ADX_FILE_PKT) (Z_to_bv 64 518) a3 a4 a5
                (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                (Z_to_bv 64 cd) (Z_to_bv 64 xl) x8 (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) (Z_to_bv 64 b0) t3 t4 t5 t6)
           F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs) ->
    as_SR H (at_head rem') (mkCfg msF mo').
  Proof.
    intros m s' errv' P xs NB c rem' cd xl b0 b1 msF mo' t0 t1 t2 a3 a4 a5 x8 t3 t4 t5 t6 FW XL B0 B1 CLE CDB KREL MP VIS.
    pose proof (dworldX_chain _ _ _ _ _ _ _ _ _ _ FW) as CHN.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & ACCB & ACCP & SK0 & RFS & XP0 & ALG).
    cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. pose proof BSL as BSL'. unfold zlength in BSL'.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & ESHD & EBL). rewrite MF0 in MF.
    cbn [app] in HP. unfold zlength in *. unfold pk_in in PIN.
    assert (RC0 : 0 <= RAISE_COST H (mid_err M)).
    { unfold RAISE_COST. pose proof (errph_nonneg (mid_err M)) as [EB0 _]. pose proof (aCm_pos H HH (raise_bytes (mid_err M)) ltac:(unfold raise_bytes, ERRDEBUG_BYTES; lia)).
      pose proof (aCf_pos H HH (errph_bytes (mid_err M) + ERRDEBUG_BYTES) ltac:(unfold ERRDEBUG_BYTES; lia)). lia. }
    assert (HAL0' : as_Cf H 0 <= as_AL H s').
    { rewrite (aCf0 H HH). destruct ALG as (um & uf & U1 & U2 & U3). pose proof (aCm_pos H HH um ltac:(lia)). pose proof (aCf_pos H HH uf ltac:(lia)).
      pose proof (aCm_pos H HH (DECEXTS_CM rem0) ltac:(unfold DECEXTS_CM; lia)). pose proof (aCf_pos H HH (DECEXTS_CF rem0) ltac:(unfold DECEXTS_CF; lia)).
      pose proof (aCm_mono H HH um (DECEXTS_CM rem0)). pose proof (aCf_mono H HH uf (DECEXTS_CF rem0)).
      assert (XSL : 0 <= xs_len xs /\ 4 * xs_len xs <= c /\ 0 <= xs_base xs <= SK_SIZE).
      { revert XI. unfold XINV, xs_len, xs_base. destruct xs as [[K es]|]; intros XI; [destruct XI as (_ & K4 & _); unfold zlength, SK_SIZE in *; lia| unfold SK_SIZE; lia]. }
      cbn [lb_bytes fold_right] in U1. unfold DECEXTS_COST in HAL0. unfold DECEXTS_CM, DECEXTS_CF, ADX_PER_EXT, ADX_PUSH_CM, ADX_PUSH_CF, SK_SIZE in *. clear - HAL0 U1 U2 U3 XSL RC0 CB1 CB2 PIN H0 H1 H2 H3 H4 H5. lia. }
    (* [comment removed for export] *)
    pose proof (acfree_null_spec H HH) as CF. unfold cfree_null_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := mid_errblocks M ++ NB ++ LB) (s := s') (CH := (bv_unsigned sp, bv_unsigned ra) :: CH); [exact VIS| ..];
        rewrite ?unsigned_lit by (unfold ADX_R1; lia).
      all: try first [exact HP| exact KREL| exact AUX| exact ST| exact CEIL| exact MI| exact TP| exact AC| exact CHN| exact IM| exact G1| exact HAL0'].
      all: lazymatch goal with
           | |- _ <= B => clear - SPB SPR; lia
           | |- _ mod 16 = 0 => clear - SPA SPR; replace (bv_unsigned sp + -144) with (bv_unsigned sp - 9 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
           | |- _ <= _ - CFREE_STACK => clear - LO; unfold DECEXTS_STACK, FR_ech_decode_echconfig_exts, SKPOPFREE_STACK, EXTFREE_STACK, CFREE_STACK, FR_ossl_echext_free, FR_sk_pop_free in LO |- *; lia
           | |- rw_cells _ _ (errno_addr _) _ => exact ERR
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - SPR; lia| specialize (CHS _ _ Hin); clear - CHS; lia]
           | |- ?G => idtac "CFPRE" G
           end. }
    clear CF. intros [ms1 mo1] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m1 & s1' & VIS1 & KREL1 & MP1 & MI1 & AC1 & ST1 & ERR1 & AUX1 & XP1 & HP1 & IM1 & GM1 & AL1).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in ST1, XP1 by lia. pose proof (ah_mpres_trans H HH _ _ _ MP MP1) as MPc1.
    change (mid_errblocks M ++ NB ++ LB) with (mid_errblocks M ++ [] ++ NB ++ LB) in XP1, HP1.
    pose proof (dworldX_call0 _ _ _ _ _ _ _ _ _ _ _ _ _ FW MI1 AC1 ST1 ERR1 AUX1 XP1 HP1 AL1) as FW1. clear FW.
    (* [comment removed for export] *)
    pose proof FW1 as (_ & _ & _ & FRt & _). cbv delta [spq] in FRt.
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply adx_seg2; [exact XL| exact FRt| clear - LO8K CEIL ACEILB; lia| exact MI1]|]. intros msF2 mo2 KREL2 MP2 CASES. pose proof (ah_mpres_trans H HH _ _ _ MPc1 MP2) as MPc2.
    destruct CASES as [[X0e VIS2]|[X1 VIS2]].
    - (* [comment removed for export] *)
      subst xl. eapply (dx_from_malloc m1 _ _ P xs NB c (cd + 0) rem' 0 0 b0 b1 None); [cbn [blocks_of]; exact FW1| reflexivity| lia| exact B0| exact B1| lia| exact CLE| exact I| exact KREL2| exact MPc2| exact VIS2].
    - (* [comment removed for export] *)
      pose proof (dworldX_chain _ _ _ _ _ _ _ _ _ _ FW1) as CHN1.
      pose proof FW1 as (_ & AC1' & ST1' & FR1 & ERR1' & AUX1' & HP1' & LM1 & _ & _ & _ & _ & PK1 & _ & _ & _ & BS1 & ACCB1 & _ & _ & _ & _ & ALG1). cbn [app] in HP1'.
      pose proof LM1 as (IM1' & MF1 & _ & _ & _ & _ & _ & _ & G11 & _). rewrite MF0 in MF1.
      destruct (bytes_at_sub m1 base bs (cd - base) xl BS1 ltac:(clear - CDB; lia) ltac:(clear - X1; lia) ltac:(clear - PIN CB1 CLE CR BSL' CRB; lia)) as [BSX XBL].
      replace (base + (cd - base)) with cd in BSX by lia.
      set (xb := firstn (Z.to_nat xl) (skipn (Z.to_nat (cd - base)) bs)) in *.
      (* [comment removed for export] *)
      assert (NBB : lb_bytes NB <= 88 + 8 * c /\ 5 * Z.of_nat (length NB) <= 2 * c + 10).
      { revert PB XI. unfold XINV. destruct xs as [[K es]|]; intros PB XI.
        - destruct XI as (KC & K4 & KCAP & E5 & EBY). rewrite blocks_EXTS_some in PB.
          pose proof (blocks_SK_facts P K ltac:(lia)) as (SKB & SKL & _ & _).
          rewrite <- (lb_bytes_perm _ _ PB), <- (Permutation_length PB), lb_bytes_app, length_app, Nat2Z.inj_add.
          unfold SK_SIZE in SKB. unfold zlength in *. clear - K4 KCAP E5 EBY SKB SKL. lia.
        - destruct XI as [_ C0]. pose proof (Permutation_nil PB) as ->. cbn. clear - C0. lia. }
      destruct NBB as (NBB & NBL).
      assert (HAL1 : as_Cm H xl <= as_AL H s1').
      { destruct ALG1 as (um & uf & U1 & U2 & U3).
        assert (XSL : 0 <= xs_len xs /\ 4 * xs_len xs <= c /\ 0 <= xs_base xs <= SK_SIZE).
        { revert XI. unfold XINV, xs_len, xs_base. destruct xs as [[K es]|]; intros XI; [destruct XI as (_ & K4 & _); unfold zlength, SK_SIZE in *; lia| unfold SK_SIZE; lia]. }
        cbn [lb_bytes fold_right] in U1.
        pose proof (aCm_super H HH um xl ltac:(lia) ltac:(lia)) as SCM.
        pose proof (aCm_mono H HH (um + xl) (DECEXTS_CM rem0) ltac:(unfold DECEXTS_CM, ADX_PER_EXT, ADX_PUSH_CM, SK_SIZE in *; clear - U1 XSL CLE XL CB1 CB2 PIN; lia)) as MCM.
        pose proof (aCf_mono H HH uf (DECEXTS_CF rem0) ltac:(unfold DECEXTS_CF, ADX_PUSH_CF in *; clear - U2 XSL CB1 CB2 PIN REM1; lia)) as MCF.
        unfold DECEXTS_COST in HAL0. clear - HAL0 U3 SCM MCM MCF RC0. lia. }
      pose proof (acmemdup_spec H HH) as CD. unfold cmemdup_stmt in CD.
      eapply (ah_seq H HH).
      { eapply CD with (lo := lo) (B := B) (LB := mid_errblocks M ++ NB ++ LB) (s := s1') (D := cd) (bs := xb) (v := 1) (bD := (pbin, base, len)) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
          [exact VIS2| ..]; unfold zlength; rewrite ?XBL; rewrite ?unsigned_lit by (unfold ADX_R2; lia); try reflexivity.
        all: try first [exact HP1'| exact KREL2| exact AUX1'| exact ST1'| exact CEIL| exact MI1| exact TP| exact MF1| exact IM1'| exact G11| exact BSX| exact AC1'| exact CHN1| exact HAL1].
        all: lazymatch goal with
             | |- 1 <= _ <= _ => clear - X1 XL; lia
             | |- In _ _ => do 2 (apply in_or_app; right); exact BIN
             | |- blk_addr _ <= _ => cbn; clear - CDB; lia
             | |- _ + _ <= blk_addr _ + _ => cbn; clear - CDB PIN CB1 CLE CR BSL'; lia
             | |- lb_bytes _ + _ <= _ => rewrite !lb_bytes_app in *; unfold DECEXTS_BYTES, ERRDEBUG_BYTES in *;
                                          pose proof (errph_nonneg (mid_err M)) as [EB0 _]; clear - BY EB0 NBB XL CLE CB1 CB2 PIN REM1; lia
             | |- Z.of_nat (length _) + _ <= _ => rewrite !length_app, !Nat2Z.inj_add in *; pose proof (errph_nonneg (mid_err M)) as [_ EC0]; clear - CN EC0 NBL CLE CB2 PIN XL Q5; lia
             | |- _ <= B => clear - SPB SPR; lia
             | |- _ mod 16 = 0 => clear - SPA SPR; replace (bv_unsigned sp + -144) with (bv_unsigned sp - 9 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
             | |- _ <= _ - CMEMDUP_STACK => clear - LO; unfold DECEXTS_STACK, FR_ech_decode_echconfig_exts, SKPUSH_STACK, SKRESERVE_STACK, CARRAY_STACK, CREALLOC_ARRAY_STACK, CREALLOC_STACK,
                                FR_sk_insert, FR_sk_reserve, CMEMDUP_STACK, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_memdup, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, FR_CRYPTO_array, FR_CRYPTO_realloc in LO |- *; lia
             | |- rw_cells _ _ (errno_addr _) _ => exact ERR1'
             | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - SPR; lia| specialize (CHS _ _ Hin); clear - CHS; lia]
             | |- pf_ok _ _ _ _ => pf_site
             | |- accessible _ _ _ => eapply accessible_sub; [exact ACCB1| clear - CDB; lia| clear - CDB PIN CB1 CLE CR BSL'; lia| clear - XL; lia]
             | |- ?G => idtac "CDPRE" G
             end. }
      clear CD. intros [ms3 mo3] PO. unfold cmemdup_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m3 & errv3 & Av & pv & s3' &
                      VIS3 & KREL3 & MP3 & MI3 & AC3 & ST3 & ERR3 & AUX3 & XP3 & VBR & HP3 & VC3 & VAD3 & MF3 & IM3 & GM3 & AL3).
      unfold zlength in VBR, HP3, VAD3, VC3, AL3. rewrite XBL in VBR, HP3, VAD3, AL3. rewrite (unsigned_lit (bv_unsigned sp + -144)) in ST3, XP3 by lia.
      pose proof (ah_mpres_trans H HH _ _ _ MPc2 MP3) as MPc3.
      change (mid_errblocks M ++ NB ++ LB) with (mid_errblocks M ++ [] ++ NB ++ LB) in XP3, HP3.
      destruct (dworldX_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FW1 MI3 AC3 ST3 ERR3 AUX3 XP3 HP3 MF3 ltac:(clear - XL; lia) AL3) as [FW3 _].
      pose proof VBR as (VP & _ & _ & _ & VH & _ & VAP).
      (* [comment removed for export] *)
      pose proof FW3 as (_ & _ & _ & FR3 & _). cbv delta [spq] in FR3.
      eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply adx_seg3; [clear - VP VH ACEILB XL; lia| exact FR3| clear - LO8K CEIL ACEILB; lia| exact MI3]|]. intros msF4 mo4 KREL4 MP4 VIS4.
      pose proof (ah_mpres_trans H HH _ _ _ MPc3 MP4) as MPc4.
      eapply (dx_from_malloc m3 _ _ P xs NB c (cd + xl) rem' Av xl b0 b1 (Some (pv, xl))); [cbn [blocks_of]; exact FW3| cbn; clear - VP X1; lia| exact XL| exact B0| exact B1| clear - VP VH ACEILB XL; lia| exact CLE| | exact KREL4| exact MPc4| exact VIS4].
      cbn [oshad]. split; [pose proof (aapp_bounds _ _ VAP ltac:(clear - XL; lia)); lia|]. split; [exact VAD3|]. exists xb. rewrite length_XBL || idtac.
      replace (Z.to_nat xl) with (length xb) by (clear - XBL; lia). exact VC3.
  Qed.

  (* [comment removed for export] *)
  Lemma dworld_pk : forall m m1 s' errv' P xs NB c cur rem cur' rem' XB,
    dworldX m s' errv' P xs NB c cur rem XB -> munch [(pk, pk + 24)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    rw_cells asegs m1 pk (pk_cells cur' base rem') -> cur + rem = cur' + rem' -> 0 <= rem' <= rem -> base <= cur ->
    dworldX m1 s' errv' P xs NB c cur' rem' XB.
  Proof.
    intros m m1 s' errv' P xs NB c cur rem cur' rem' XB FW MU WM MI1 PK1 CR1 RR BC.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & ACCB & ACCP & SK0 & RFS & XP0 & ALG).
    pose proof (dworldX_blocks _ _ _ _ _ _ _ _ _ _ FW) as HB. clear FW.
    unfold dworldX. cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. pose proof BSL as BSL'. unfold zlength in BSL'.
    set (Lp := mid_errblocks M ++ XB ++ NB ++ LB) in *.
    assert (XPL : forall L X, (forall b, In b L -> In b Lp) -> xpres H L (pk + 24) X m m1).
    { intros L X SUBL. eapply (xpres_weaken H); [| apply Z.le_refl| exact SUBL| intros a Ha; exact Ha].
      eapply (xpres_of_munch H _ Lp); [exact HH| exact HP| exact MU| exact WM|]. apply Forall_cons; [left; cbn; clear - SPK CEIL LO8K; lia| apply Forall_nil]. }
    pose proof (HB _ ltac:(subst Lp; do 3 (apply in_or_app; right); exact BIN)) as (_ & _ & K2 & _). cbn [blk_addr blk_size fst snd] in K2. unfold pk_in in *.
    assert (WNS : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(pk, pk + 24)]).
    { apply Forall_cons; [cbn [fst snd]; right; unfold AHI_LO; clear - SPK CEIL LO8K ACEILB; lia| apply Forall_nil]. }
    assert (CW : Forall (aclient_write_ok H Lp) [(pk, pk + 24)]) by (apply Forall_cons; [left; cbn; clear - SPK CEIL LO8K; lia| apply Forall_nil]).
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4).
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply ACONST_stack_frame13; [exact AC| exact MU| exact WM| clear - SPK CEIL LO8K; lia].
    - eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. cbn. clear - SPK. lia.
    - eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. clear - SPK. lia.
    - rewrite TP in ERR |- *. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. rewrite unsigned_lit by (unfold ATP; lia). cbn. unfold ATP. clear - SPK CEIL LO8K ACEILB. lia.
    - eapply (ah_rauxv_frame H HH); [exact AUX| exact MU| exact WM| exact CW].
    - eapply (ah_RHEAP_frame H HH); [exact HP| exact MU| exact WM| exact CW].
    - eapply (LIBMID_xpres0 H); [exact LM| exact CX| apply (XPL Lp []); intros b Hb; exact Hb| intros b Hb; subst Lp; do 3 (apply in_or_app; right); apply LIBSUB; exact Hb| intros b Hb; subst Lp; apply in_or_app; left; exact Hb].
    - eapply (ENTRYobj_frame_law H); [exact EO| intros b Hb; eapply ENTRYobj_owned_law; [exact EO| exact Hb]| apply XPL; intros b Hb; subst Lp; do 2 (apply in_or_app; right); exact Hb|].
      intros b Hb. pose proof (HB b ltac:(subst Lp; do 2 (apply in_or_app; right); eapply ENTRYobj_owned_law; [exact EO| exact Hb])) as (_ & _ & K5 & _). clear - K5 SPK CEIL LO8K. lia.
    - eapply (ENTRY_shad_frame_law H); [exact ESH| intros b Hb; eapply ENTRYobj_owned_law; [exact EO| exact Hb]| apply XPL; intros b Hb; subst Lp; do 2 (apply in_or_app; right); exact Hb|].
      intros b Hb. pose proof (HB b ltac:(subst Lp; do 2 (apply in_or_app; right); eapply ENTRYobj_owned_law; [exact EO| exact Hb])) as (_ & _ & K5 & _). clear - K5 SPK CEIL LO8K. lia.
    - clear - PIN BC RR CR1. lia.
    - clear - RR. lia.
    - clear - PIN RR CR1. lia.
    - clear - CR CR1. lia.
    - clear - CB2 RR. lia.
    - eapply bytes_at_transport; [exact BS| exact MU|]. cbn. split; [| exact I]. clear - K2 SPK CEIL LO8K BSL'. lia.
    - eapply accessible_across; [exact ACCB| exact MU| exact WNS].
    - eapply accessible_across; [exact ACCP| exact MU| exact WNS].
    - eapply stack0_transport; [exact SK0| exact MU| exact WM|]. apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO; clear - SPK CEIL LO8K ACEILB; lia| apply Forall_nil].
    - eapply (ah_RFS_frame H HH); [exact RFS| exact MU| exact WM|]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. clear - F2 SPK CEIL LO8K ACEILB. lia.
    - eapply (xpres_trans H); [exact XP0|]. eapply (xpres_weaken H); [| apply Z.le_refl| intros b Hb; subst Lp; do 3 (apply in_or_app; right); exact Hb| intros a Ha; exact Ha].
      eapply (xpres_of_munch H _ Lp); [exact HH| exact HP| exact MU| exact WM|].
      apply Forall_cons; [right; cbn; intros a Ha; unfold X0; cbn [rin_ivs fst snd]; left; exact Ha| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Definition dx_exit (k : config) : Prop :=
    exists (rax x1 a0 a1 a2 a3 a4 a5 x6 x7 x8 x10 x11 t0 t1 t2 t3 t4 t5 t6 : word) m s' errv' P xs NB cur rem,
      as_AKREL H s' k /\ as_MPRES H mo (cfg_model k) /\
      (  (rem = 0 /\ dworld m s' errv' P xs NB cur rem /\
          as_VIS H s' (cfg_ms k)
            = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 (Z_to_bv 64 1) a1 a2 a3 a4 (Z_to_bv 64 (-2)) (Z_to_bv 64 1) (Z_to_bv 64 2)
                      (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                      x6 x7 x8 (Z_to_bv 64 ASHB) x10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
                 F (Z_to_bv 64 ADX_EPI) fc None m (seg_rom asegs))
      \/ (exists line c, (line = 206 \/ line = 210) /\ dworldX m s' errv' P xs NB c cur rem [] /\
          as_VIS H s' (cfg_ms k)
            = MS (mkR (Z_to_bv 64 ADX_RA1) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 2)
                      (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                      (Z_to_bv 64 line) x7 x8 (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) x11 t3 t4 t5 t6)
                 F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs))).

  (* [comment removed for export] *)
  Lemma dx_head_step : forall (rax x1 a0 a1 a2 a3 a4 x6 x7 x8 x10 t0 t1 t2 t3 t4 t5 t6 : word) m s' errv' P xs NB cur rem msF mo',
    dworld m s' errv' P xs NB cur rem -> as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 (Z_to_bv 64 (-2)) (Z_to_bv 64 1) (Z_to_bv 64 2)
                (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                x6 x7 x8 (Z_to_bv 64 ASHB) x10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
           F (Z_to_bv 64 ADX_LOOP) fc None m (seg_rom asegs) ->
    as_SR H (fun k => dx_exit k \/ at_head (rem - 4) k) (mkCfg msF mo').
  Proof.
    intros rax x1 a0 a1 a2 a3 a4 x6 x7 x8 x10 t0 t1 t2 t3 t4 t5 t6 m s' errv' P xs NB cur rem msF mo' FW KREL MP VIS.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & ACCB & ACCP & SK0 & RFS & XP0 & ALG).
    cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. pose proof BSL as BSL'. unfold zlength in BSL'.
    destruct (dworld_entry _ _ _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & _ & _ & _ & _ & _ & EEP & EEH & EAP & E16 & _ & PKP & PKH & BP & BH & BAP & PKA).
    assert (EAL8 : ee mod 8 = 0) by (clear - E16; Z.div_mod_to_equations; lia).
    pose proof PIN as PIN'. unfold pk_in in PIN'. assert (PIN2 : pk_in base (zlength bs) cur rem) by (pose proof CRB as CRBq; unfold pk_in; unfold zlength in CRBq |- *; clear - PIN' CR CRBq; lia).
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply adx_segH with (blen := zlength bs);
      [exact PK| exact BS| exact PIN2| clear - PKP; lia| pose proof ACCP as (_ & QH & _); exact QH| exact PKA| right; unfold AHI_LO; clear - SPK CEIL LO8K ACEILB; lia
      | right; clear - SPK; lia| exact ACCP| eapply accessible_sub; [exact ACCB| apply Z.le_refl| unfold zlength; clear - BSL'; lia| unfold zlength; clear; lia]
      | apply Z.le_refl| clear - EEP; lia| pose proof ESH as [ETOP _]; unfold ENTRY_SIZE in ETOP; exact ETOP| exact PK8| exact EAL8| exact BP| exact FR| clear - LO8K CEIL ACEILB; lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (a0' & a1' & a2' & a3' & a4' & a5' & s1' & s7' & s11' & m1 & cur' & rem' & MU1 & WM1 & MI1 & PK1 & CR1 & RR & CASES).
    pose proof (ah_mpres_trans H HH _ _ _ MP MP1) as MPc1.
    destruct CASES as [(R0 & -> & -> & VIS1)|[(line & LN & R1 & VIS1)|(b0 & b1 & xl & XL & CU & RM & B0 & B1 & VIS1)]].
    - (* [comment removed for export] *)
      apply (ah_done H HH). left. unfold dx_exit. cbn [cfg_ms cfg_model].
      exists rax, x1, a0, a1, a2, (Z_to_bv 64 rem), a4, a0, x6, x7, x8, x10, x10, t0, t1, t2, t3, t4, t5, t6, m, s', errv', P, xs, NB, cur, rem.
      split; [exact KREL1|]. split; [exact MPc1|]. left. split; [exact R0|]. split; [exact FW| exact VIS1].
    - (* [comment removed for export] *)
      pose proof (dworld_pk _ _ _ _ _ _ _ _ _ _ _ _ _ FW MU1 WM1 MI1 PK1 CR1 RR ltac:(clear - PIN'; lia)) as FW1.
      apply (ah_done H HH). left. unfold dx_exit. cbn [cfg_ms cfg_model].
      exists rax, s1', a0', a1', a2', a3', a4', a5', x6, s7', x8, x10, s11', t0, t1, t2, t3, t4, t5, t6, m1, s', errv', P, xs, NB, cur', rem'.
      split; [exact KREL1|]. split; [exact MPc1|]. right. exists line, (rem0 - rem). split; [exact LN|]. split; [exact FW1| exact VIS1].
    - (* [comment removed for export] *)
      pose proof (dworld_pk _ _ _ _ _ _ _ _ _ _ _ _ _ FW MU1 WM1 MI1 PK1 CR1 RR ltac:(clear - PIN'; lia)) as FW1.
      eapply (ah_mono H HH); [eapply (dx_trip m1 s' errv' P xs NB (rem0 - rem) rem' (cur + 4) xl b0 b1)|].
      + replace (cur + 4 + xl) with cur' by (clear - CU; lia). exact FW1.
      + exact XL. + exact B0. + exact B1.
      + clear - RM XL RR. lia.
      + clear - PIN'. lia.
      + exact KREL1. + exact MPc1. + exact VIS1.
      + intros k AH. right. unfold at_head in AH |- *.
        destruct AH as (rax2 & c1 & c0 & d1 & d2 & d3 & d4 & c6 & c7 & c8 & c10 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & m2 & st2 & errv2 & P2 & xs2 & NB2 & cur2 & rem2 & FW2 & RB & K2 & MP2 & MS2).
        exists rax2, c1, c0, d1, d2, d3, d4, c6, c7, c8, c10, u0, u1, u2, u3, u4, u5, u6, m2, st2, errv2, P2, xs2, NB2, cur2, rem2.
        split; [exact FW2|]. split; [clear - RB RM XL; lia|]. split; [exact K2|]. split; [exact MP2| exact MS2].
  Qed.

  (* [comment removed for export] *)
  Lemma DX_loop : forall (n : nat) (rax x1 a0 a1 a2 a3 a4 x6 x7 x8 x10 t0 t1 t2 t3 t4 t5 t6 : word) m s' errv' P xs NB cur rem msF mo',
    dworld m s' errv' P xs NB cur rem -> rem <= Z.of_nat n -> as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 (Z_to_bv 64 (-2)) (Z_to_bv 64 1) (Z_to_bv 64 2)
                (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                x6 x7 x8 (Z_to_bv 64 ASHB) x10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
           F (Z_to_bv 64 ADX_LOOP) fc None m (seg_rom asegs) ->
    as_SR H dx_exit (mkCfg msF mo').
  Proof.
    induction n as [|n IH]; intros rax x1 a0 a1 a2 a3 a4 x6 x7 x8 x10 t0 t1 t2 t3 t4 t5 t6 m s' errv' P xs NB cur rem msF mo' FW RN KREL MP VIS.
    - eapply (ah_seq H HH); [eapply dx_head_step; [exact FW| exact KREL| exact MP| exact VIS]|]. intros k [EX|AH]; [apply (ah_done H HH); exact EX|].
      exfalso. unfold at_head in AH. destruct AH as (rax2 & c1 & c0 & d1 & d2 & d3 & d4 & c6 & c7 & c8 & c10 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & m2 & st2 & errv2 & P2 & xs2 & NB2 & cur2 & rem2 & FW2 & RB & _).
      pose proof FW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PIN2 & _). unfold pk_in in PIN2. clear - PIN2 RB RN. cbn in RN. lia.
    - eapply (ah_seq H HH); [eapply dx_head_step; [exact FW| exact KREL| exact MP| exact VIS]|]. intros [ms2 mo2'] [EX|AH]; [apply (ah_done H HH); exact EX|].
      unfold at_head in AH. cbn [cfg_ms cfg_model] in AH.
      destruct AH as (rax2 & c1 & c0 & d1 & d2 & d3 & d4 & c6 & c7 & c8 & c10 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & m2 & st2 & errv2 & P2 & xs2 & NB2 & cur2 & rem2 & FW2 & RB & K2 & MP2 & MS2).
      eapply IH; [exact FW2| | exact K2| exact MP2| exact MS2]. rewrite Nat2Z.inj_succ in RN. clear - RB RN. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_ret1 : forall (rax x1 a1 a2 a3 a4 x6 x7 x8 x10 t0 t1 t2 t3 t4 t5 t6 : word) m s' errv' P xs NB cur rem msF mo',
    dworld m s' errv' P xs NB cur rem -> rem = 0 -> as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 (Z_to_bv 64 1) a1 a2 a3 a4 (Z_to_bv 64 (-2)) (Z_to_bv 64 1) (Z_to_bv 64 2)
                (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                x6 x7 x8 (Z_to_bv 64 ASHB) x10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
           F (Z_to_bv 64 ADX_EPI) fc None m (seg_rom asegs) ->
    as_SR H (decexts_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LIB LB LF M ee pk base len cur0 rem0 E bs lo B m0 mo) (mkCfg msF mo').
  Proof.
    intros rax x1 a1 a2 a3 a4 x6 x7 x8 x10 t0 t1 t2 t3 t4 t5 t6 m s' errv' P xs NB cur rem msF mo' FW R0 KREL MP VIS.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & ACCB & ACCP & SK0 & RFS & XP0 & ALG).
    cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. cbn [app] in HP.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & ESHD & EBL).
    (* [comment removed for export] *)
    destruct xs as [[K es]|]; [| exfalso; unfold XINV in XI; destruct XI as [_ C0]; clear - C0 R0 REM1; lia].
    unfold XINV in XI. destruct XI as (KC & K4 & KCAP & E5 & EBY). rewrite blocks_EXTS_some in PB.
    pose proof (blocks_SK_facts P K ltac:(lia)) as (SKB & SKL & _ & SK0').
    assert (LEN16 : length (es_slots (mid_E M)) = 16%nat).
    { destruct (mid_err M) as [|c0]; cbn [ERRX] in EX; [rewrite EX; reflexivity| exact (proj1 (proj1 EX))]. }
    pose proof (errst_fits_bounds _ LEN16 FIT) as [EC EB].
    assert (RC0 : 0 <= RAISE_COST H (mid_err M)).
    { unfold RAISE_COST. pose proof (errph_nonneg (mid_err M)) as [EB0 _]. pose proof (aCm_pos H HH (raise_bytes (mid_err M)) ltac:(unfold raise_bytes, ERRDEBUG_BYTES; lia)).
      pose proof (aCf_pos H HH (errph_bytes (mid_err M) + ERRDEBUG_BYTES) ltac:(unfold ERRDEBUG_BYTES; lia)). lia. }
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply adx_segE with (lo := lo); [exact FR| exact ST| exact CEIL| clear - LO8K; lia| exact MI]|].
    intros msF3 mo3 KREL3 MP3 [VIS3 ST3].
    apply (ah_done H HH). unfold decexts_post. cbn [cfg_ms cfg_model].
    exists t0, t1, t2, a1, a2, a3, a4, (Z_to_bv 64 (-2)), (Z_to_bv 64 1), (Z_to_bv 64 2), t3, t4, t5, t6, m, errv', s', 1, M, (Some (K, es)), P, NB, [], cur, rem, [].
    cbn [app]. unfold zlength in *. unfold pk_in in PIN.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    all: lazymatch goal with
         | |- _ = _ => first [exact VIS3| reflexivity]
         | |- as_MPRES _ _ _ => eapply (ah_mpres_trans H HH); [exact MP| exact MP3]
         | |- mid_step _ _ => unfold mid_step; split; [exact MF0|]; split; [auto|]; split; auto
         | |- mid_newlib_ok _ _ _ => unfold mid_newlib_ok; exists [], []; split; [apply Permutation_refl|]; rewrite CX; split; [reflexivity|]; destruct (mid_err M); reflexivity
         | |- Permutation _ _ => rewrite blocks_EXTS_some; exact PB
         | |- _ \/ _ => left; split; [reflexivity|]; split; [discriminate| exact R0]
         | |- 5 * _ <= _ => rewrite <- (Permutation_length PB), length_app, Nat2Z.inj_add; clear - SKL E5 R0; lia
         | |- lb_bytes _ <= _ => rewrite (lb_bytes_perm _ _ (Permutation_sym PB)), lb_bytes_app; unfold SK_SIZE in *; clear - SKB EBY KCAP K4 CB2 R0 REM1; lia
         | |- Forall _ [] => apply Forall_nil
         | |- athr_cells _ => eapply (ah_thr H HH); exact HP
         | |- as_AL _ _ >= _ => destruct ALG as (um & uf & U1 & U2 & U3); cbn [xs_len xs_base lb_bytes fold_right] in U1, U2; unfold zlength in U1, U2;
                               pose proof (aCm_mono H HH um (DECEXTS_CM rem0) ltac:(unfold DECEXTS_CM, ADX_PER_EXT, ADX_PUSH_CM, SK_SIZE in *; clear - U1 K4 CB1 CB2 R0 REM1; lia)) as MCM;
                               pose proof (aCf_mono H HH uf (DECEXTS_CF rem0) ltac:(unfold DECEXTS_CF, ADX_PUSH_CF in *; clear - U2 K4 CB1 CB2 R0 REM1; lia)) as MCF;
                               assert (RCd0 : 0 <= RAISE_COSTd H (mid_err M) (mid_err M)) by (unfold RAISE_COSTd; rewrite Z.sub_diag;
                                 pose proof (aCm_pos H HH (0 + ERRDEBUG_BYTES) ltac:(unfold ERRDEBUG_BYTES; lia)); pose proof (aCf_pos H HH (0 + ERRDEBUG_BYTES) ltac:(unfold ERRDEBUG_BYTES; lia)); lia);
                               unfold DECEXTS_SPENT; clear - U3 MCM MCF RCd0; lia
         | |- ?G => idtac "RET1" G
         end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition XR (XS : list (Z * Z)) : list (Z * Z) := XS ++ ERR_XE ++ memflag_foot ++ errph_foot (mid_err M).

  (* [comment removed for export] *)
  Lemma XR_block : forall s L m2 LF0 mX XS b,
    as_RHEAP H s L m2 -> as_RFS H LF0 mX -> Forall (fs_scratch H LF0) XS -> In b L ->
    (forall c0, mid_err M = ErrReady c0 -> In (ec_es c0) L /\ blk_id (ec_es c0) <> blk_id b /\ blk_size (ec_es c0) = ERRST_SIZE) ->
    avoids (XR XS) (blk_addr b) (blk_size b) /\ shavoids (XR XS) (blk_addr b) (blk_size b).
  Proof.
    intros s L m2 LF0 mX XS b HP RF FXS Hb HES. acb. destruct b as [[q A] n]. cbn [blk_id blk_addr blk_size fst snd] in *.
    pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in B1, B2, B3, B4, B5, B6, B7.
    pose proof (aapp_bounds _ _ B7 B3) as (Q1 & Q2 & Q3 & Q4 & _). pose proof (sh_aapp_range _ _ B7 B3) as (S1 & S2 & S3).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in S1.
    unfold XR, avoids, shavoids. split; (apply Forall_app; split; [| apply Forall_app; split; [| apply Forall_app; split]]).
    - eapply Forall_impl; [| exact FXS]. cbn beta. intros iv SC. exact (fsobj_scratch H HH LF0 A n mX iv RF (fsobj_block H HH _ _ _ LF0 _ _ _ HP Hb) ltac:(lia) B3 ltac:(lia) B7 SC).
    - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
        A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      unfold AIMG_TOP in B4. cbn [app]. clear - B4. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
    - unfold memflag_foot, A_mem_inited. unfold AIMG_TOP in B4. clear - B4. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
    - destruct (mid_err M) as [|c0]; cbn [errph_foot]; [apply Forall_nil|]. destruct (HES c0 eq_refl) as (IE & NE & SZ).
      pose proof (ah_disj H HH _ _ _ _ _ HP IE Hb NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ. rewrite SZ in DJ.
      apply Forall_cons; [cbn [fst snd]; clear - DJ; lia| apply Forall_nil].
    - eapply Forall_impl; [| exact FXS]. cbn beta. intros iv SC. exact (fsobj_scratch_sh H HH LF0 A n mX iv RF (fsobj_block H HH _ _ _ LF0 _ _ _ HP Hb) ltac:(lia) B3 ltac:(lia) SC).
    - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
        A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      cbn [app]. clear - S1. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
    - unfold memflag_foot, A_mem_inited. clear - S1. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
    - destruct (mid_err M) as [|c0]; cbn [errph_foot]; [apply Forall_nil|]. destruct (HES c0 eq_refl) as (IE & NE & SZ).
      pose proof (ah_blocks H HH _ _ _ _ HP IE) as (_ & _ & E3 & _ & _ & _ & E7). rewrite SZ in E3, E7.
      apply Forall_cons; [cbn [fst snd]; pose proof (app_vs_sh _ _ _ _ E7 E3 B7 B3); lia| apply Forall_nil].
  Qed.
  (* [comment removed for export] *)
  Lemma XR_stack : forall LF0 mX XS a n,
    as_RFS H LF0 mX -> Forall (fs_scratch H LF0) XS -> aceil <= a -> errph_below (mid_err M) aceil -> avoids (XR XS) a n.
  Proof.
    intros LF0 mX XS a n RF FXS Ha EB. unfold XR, avoids. apply Forall_app. split.
    - eapply Forall_impl; [| exact (fs_scratch_range_Forall H HH _ _ _ RF FXS)]. cbn beta. intros iv K. lia.
    - eapply (raise_foot_frame (mid_err M) a n aceil); [apply Z.le_refl| exact Ha| exact EB].
  Qed.
  Lemma XR_stack_sh : forall s L m2 LF0 mX XS a n,
    as_RHEAP H s L m2 -> as_RFS H LF0 mX -> Forall (fs_scratch H LF0) XS -> aceil <= a -> 0 <= n -> a + n <= AAPP_HI ->
    (forall c0, mid_err M = ErrReady c0 -> In (ec_es c0) L /\ blk_size (ec_es c0) = ERRST_SIZE) -> shavoids (XR XS) a n.
  Proof.
    intros s L m2 LF0 mX XS a n HP RF FXS Ha Hn Htop HES. acb. unfold XR, shavoids. pose proof (RFS_fsb H HH _ _ RF) as (F1 & F2 & F3 & F4).
    assert (SA : sh aceil <= sh a) by (apply sh_mono; lia). pose proof (sh_aapp_range _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (FS1 & FS2 & FS3).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in FS1.
    apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split]].
    - eapply Forall_impl; [| exact FXS]. cbn beta. intros iv SC. exact (fsobj_scratch_sh H HH LF0 a n mX iv RF (fsobj_high H HH LF0 a n mX RF Ha) ltac:(lia) Hn Htop SC).
    - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
        A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      cbn [app]. unfold nsh, AFS_SIZE in FS2. clear - SA FS1 FS2. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
    - unfold memflag_foot, A_mem_inited. unfold nsh, AFS_SIZE in FS2. clear - SA FS1 FS2. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
    - destruct (mid_err M) as [|c0]; cbn [errph_foot]; [apply Forall_nil|]. destruct (HES c0 eq_refl) as [IE SZ].
      pose proof (ah_blocks H HH _ _ _ _ HP IE) as (_ & _ & E3 & _ & _ & _ & E7). rewrite SZ in E3, E7.
      apply Forall_cons; [cbn [fst snd]; exact (aapp_disjoint_sh _ _ a n E7 ltac:(lia) Htop Hn)| apply Forall_nil].
  Qed.
  (* [comment removed for export] *)
  Lemma XR_stack0 : forall s L m2 LF0 mX XS,
    as_RHEAP H s L m2 -> as_RFS H LF0 mX -> Forall (fs_scratch H LF0) XS ->
    (forall c0, mid_err M = ErrReady c0 -> In (ec_es c0) L /\ blk_size (ec_es c0) = ERRST_SIZE) -> Forall stack0_ok (XR XS).
  Proof.
    intros s L m2 LF0 mX XS HP RF FXS HES. acb. unfold XR. pose proof (RFS_fsb H HH _ _ RF) as (F1 & F2 & F3 & F4).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. assert (LEA : AIMG_TOP <= aceil) by (unfold AIMG_TOP; lia). pose proof (sh_mono AIMG_TOP aceil LEA) as SM. rewrite S0 in SM.
    apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split]].
    - eapply Forall_impl; [| exact FXS]. intros iv SC. unfold stack0_ok. destruct SC as [->|(k & ff & fp & FF & EE)]; cbn [fst snd].
      + pose proof (aapp_not_shadowland _ _ F4). pose proof (sh_aapp_range _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (FS1 & _). rewrite S0 in FS1. unfold AFS_FLAGS, AFS_SIZE, ALOWSH_LO in *. lia.
      + pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
        pose proof (aapp_not_shadowland _ _ P9) as FNS. pose proof (sh_aapp_range _ _ P9 ltac:(unfold AFS_SIZE; lia)) as (FS1 & FS2 & FS3). rewrite S0 in FS1.
        pose proof (fsz_pos k ltac:(lia)).
        destruct EE as [-> |[-> | ->]]; cbn [fst snd]; unfold AFS_FLAGS, AFS_SIZE, AFS_HDR, ALOWSH_LO in *; [lia| lia|].
        right. assert (LE1 : ff + fsz k <= as_FSB H + 11571200) by (clear - P6; lia). pose proof (sh_mono _ _ LE1) as SM1. pose proof (sh_mono _ _ P8) as SM2.
        assert (E8 : sh (ff + fsz k) = sh ff + fshn k) by (unfold fshn, fsz, sh; clear - M8; Z.div_mod_to_equations; nia). rewrite <- E8. clear - SM1 SM2. lia.
    - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
        A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      cbn [app]. clear - SM. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
    - unfold memflag_foot, A_mem_inited. clear - SM. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
    - destruct (mid_err M) as [|c0]; cbn [errph_foot]; [apply Forall_nil|]. destruct (HES c0 eq_refl) as [IE SZ].
      pose proof (ah_blocks H HH _ _ _ _ HP IE) as (_ & _ & E3 & _ & _ & _ & E7). rewrite SZ in E3, E7.
      apply Forall_cons; [eapply stack0_ok_aapp; [exact E7| cbn; lia| cbn; lia]| apply Forall_nil].
  Qed.
  Lemma XR_low : forall s L m2 LF0 mX XS,
    as_RHEAP H s L m2 -> as_RFS H LF0 mX -> Forall (fs_scratch H LF0) XS ->
    (forall c0, mid_err M = ErrReady c0 -> In (ec_es c0) L /\ blk_size (ec_es c0) = ERRST_SIZE) -> Forall (fun iv : Z * Z => snd iv <= aceil) (XR XS).
  Proof.
    intros s L m2 LF0 mX XS HP RF FXS HES. acb. unfold XR.
    apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split]].
    - eapply Forall_impl; [| exact (fs_scratch_range_Forall H HH _ _ _ RF FXS)]. cbn beta. intros iv K. lia.
    - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
        A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      cbn [app]. clear - ACEILB. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
    - unfold memflag_foot, A_mem_inited. clear - ACEILB. apply Forall_cons; [cbn; lia| apply Forall_nil].
    - destruct (mid_err M) as [|c0]; cbn [errph_foot]; [apply Forall_nil|]. destruct (HES c0 eq_refl) as [IE SZ].
      pose proof (ah_blocks H HH _ _ _ _ HP IE) as (_ & _ & _ & _ & E5 & _). rewrite SZ in E5. apply Forall_cons; [cbn [fst snd]; exact E5| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma chain_at : forall X mx,
    xpres H LB (bv_unsigned sp) X m0 mx -> Forall (fun iv : Z * Z => snd iv <= aceil \/ offchain CH (fst iv) (snd iv - fst iv)) X ->
    rw_cells asegs mx spq (adx_frame j0 pk ee s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
    as_chain H mx (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH).
  Proof.
    intros X mx XP FX FR. cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (C0 : as_chain H mx (bv_unsigned s0) CH) by (eapply (chain_via_xpres_off H HH); [exact CHN0| exact XP| exact CHS| exact FX]).
    eapply (ah_chain_cons H HH); [exact C0| lia| lia| exact SPA| clear - CEIL LO8K; lia| lia|].
    unfold adx_frame in FR.
    apply (proj1 (rw_cells_app asegs _ _ [C8 (wz ADX_FILE_ECHS); C8 (wz ADX_FILE_PKT); C8 (wz (ee + 56)); C8 (wz 0); C8 (wz 0);
                                           C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _)) in FR.
    destruct FR as [_ FR2]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ] in FR2.
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -144 + 128) by lia. rewrite !Z_to_bv_bv_unsigned. exact FR2.
  Qed.
  Lemma X0XR_chain : forall s L m2 LF0 mX XS,
    as_RHEAP H s L m2 -> as_RFS H LF0 mX -> Forall (fs_scratch H LF0) XS -> In (en_id E, ee, ENTRY_SIZE) L ->
    (forall c0, mid_err M = ErrReady c0 -> In (ec_es c0) L /\ blk_size (ec_es c0) = ERRST_SIZE) ->
    Forall (fun iv : Z * Z => snd iv <= aceil \/ offchain CH (fst iv) (snd iv - fst iv)) (XS ++ X0).
  Proof.
    intros s L m2 LF0 mX XS HP RF FXS EIN HES. unfold X0.
    pose proof (ah_blocks H HH _ _ _ _ HP EIN) as (_ & _ & _ & _ & E5 & _). cbn [blk_addr blk_size fst snd] in E5.
    apply Forall_app. split; [eapply Forall_impl; [| exact (fs_scratch_range_Forall H HH _ _ _ RF FXS)]; cbn beta; intros iv K; left; lia|].
    apply Forall_cons; [right; cbn [fst snd]; replace (pk + 24 - pk) with 24 by lia; exact OFFCH|].
    apply Forall_cons; [left; cbn [fst snd]; exact E5|].
    acb. apply Forall_app. split.
    - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
        A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
      cbn [app]. clear - ACEILB. repeat (apply Forall_cons; [left; cbn; lia|]). apply Forall_nil.
    - destruct (mid_err M) as [|c0]; cbn [errph_foot]; [apply Forall_nil|]. destruct (HES c0 eq_refl) as [IE SZ].
      pose proof (ah_blocks H HH _ _ _ _ HP IE) as (_ & _ & _ & _ & E5' & _). rewrite SZ in E5'. apply Forall_cons; [left; cbn [fst snd]; exact E5'| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma oshad_entry_write : forall s L m2 m m1 Pf o Een pad1 pad2 pad3 pad4,
    as_RHEAP H s L m2 -> In (en_id E, ee, ENTRY_SIZE) L -> (forall b, In b LB -> In b L) -> ofield LB Pf o ->
    munch [(ee, ee + 104)] m m1 -> wmono asegs m m1 ->
    rw_cells asegs m1 ee (entry_cells Een pad1 pad2 pad3 pad4) -> ee + ENTRY_SIZE <= AAPP_HI -> addressable m1 ee ENTRY_SIZE ->
    oshad m Pf o -> oshad m1 Pf o.
  Proof.
    intros s L m2 m m1 Pf o Een pad1 pad2 pad3 pad4 HP EIN SUB OFo MU WM EC ETOP EAD OSo. acb.
    destruct o as [[i1 n1]|]; [| exact I]. cbn [ofield] in OFo. destruct OFo as (OP1 & ON1 & IN1).
    pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ IN1)) as (_ & _ & _ & _ & W5 & _). cbn [blk_addr blk_size fst snd] in W5.
    pose proof (ah_blocks H HH _ _ _ _ HP EIN) as (_ & _ & _ & _ & _ & _ & EAP). cbn [blk_addr blk_size fst snd] in EAP.
    assert (WE : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(ee, ee + 104)]).
    { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. pose proof (aapp_not_shadowland _ _ EAP). unfold ENTRY_SIZE in *. lia. }
    destruct (Z.eq_dec i1 (en_id E)) as [EQ|NE].
    - pose proof (nodup_ids_same _ _ _ (ah_nodup H HH _ _ _ HP) (SUB _ IN1) EIN EQ) as EB. injection EB as En Ee. subst Pf n1.
      cbn [oshad]. split; [exact ETOP|]. split; [exact EAD|]. unfold ENTRY_SIZE. exists (cells_bytes (entry_cells Een pad1 pad2 pad3 pad4)). exact (rw_cells_as_CB _ _ _ EC).
    - eapply oshad_acrossW; [exact OSo| exact MU| exact WM| | exact WE].
      pose proof (ah_disj H HH _ _ _ _ _ HP (SUB _ IN1) EIN NE) as DJ1. cbn [blk_addr blk_size fst snd] in DJ1. cbn. unfold AAPP_HI, ENTRY_SIZE in *. clear - OP1 ON1 W5 ACEILB DJ1. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma exts_cost_bytes : forall L m ps es,
    Forall2 (fun p X => EXTobj L m p X) ps es ->
    ecost_sum extrep (ext_cost H) es <= as_Cf H (lb_bytes (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))))
    /\ 0 <= lb_bytes (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))).
  Proof.
    intros L m ps es F2. induction F2 as [|p X ps' es' HE FF2 IH].
    - cbn. rewrite (aCf0 H HH). lia.
    - destruct IH as [IH1 IH2]. unfold ecost_sum in IH1 |- *. cbn [fold_right combine map concat fst snd]. rewrite lb_bytes_app.
      set (R := lb_bytes (concat (map (fun px : Z * extrep => blocks_EXT (fst px) (snd px)) (combine ps' es')))) in *.
      pose proof HE as (_ & _ & OF).
      assert (E1 : ext_cost H X <= as_Cf H (lb_bytes (blocks_EXT p X)) /\ 0 <= lb_bytes (blocks_EXT p X)).
      { unfold ext_cost, ocost, blocks_EXT, blocks_of. revert OF. unfold ofield. destruct (ex_val_o X) as [[i n]|]; intros OF; rewrite ?lb_bytes_cons; cbn [blk_size snd lb_bytes fold_right]; rewrite Z.add_0_r.
        - destruct OF as (_ & N0 & _). rewrite (Z.max_l n 0) by lia. pose proof (aCf_super H HH EXT_SIZE n ltac:(unfold EXT_SIZE; lia) N0). unfold EXT_SIZE in *. lia.
        - rewrite (aCf0 H HH). unfold EXT_SIZE. lia. }
      destruct E1 as [E1 P1]. pose proof (aCf_super H HH _ _ P1 IH2). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma es_after : forall LE m c0 E',
    LIBMID (LE ++ LIB) m (mkMID 1 (CtxReady x) (ErrReady c0) E' (mid_vdso M)) -> errph_delta (mid_err M) LE c0 ->
    forall c1, mid_err M = ErrReady c1 -> In (ec_es c1) LIB /\ blk_size (ec_es c1) = ERRST_SIZE /\ c1 = c0 /\ LE = [].
  Proof.
    intros LE m c0 E' LM DL c1 PH. rewrite PH in DL. cbn [errph_delta] in DL. destruct DL as [-> ->].
    pose proof LM as (_ & _ & _ & EPm & _). cbn [mid_ctx mid_err ERRPH_mid ERRPH app] in EPm. destruct EPm as [_ EC].
    pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _). cbn [app] in I5. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_fail_end : forall m s' errv' P xs cur rem Lf LE c0 E' pad1 pad2 pad3 pad4 XS uf msF mo'
                             (t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x5 x7 : word),
    let M' := mkMID 1 (CtxReady x) (ErrReady c0) E' (mid_vdso M) in
    mem_inv asegs m -> ACONST m -> stk asegs m lo spq -> rw_cells asegs m spq (adx_frame j0 pk ee s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
    rw_cells asegs m (errno_addr tp) [C4 errv'] -> as_rauxv_ok H m B ->
    as_RHEAP H s' Lf m -> Permutation Lf (blocks_ERRST E' ++ LE ++ LB) ->
    LIBMID (LE ++ LIB) m M' -> errph_delta (mid_err M) LE c0 ->
    length pad1 = 6%nat -> length pad2 = 4%nat -> length pad3 = 6%nat -> length pad4 = 4%nat ->
    rw_cells asegs m ee (entry_cells (EW P xs) pad1 pad2 pad3 pad4) -> ENTRY_shad m ee (EW 0 None) ->
    rw_cells asegs m pk (pk_cells cur base rem) -> pk_in base len cur rem -> cur0 + rem0 = cur + rem -> rem <= rem0 ->
    bytes_at asegs m base bs -> accessible m base len -> accessible m pk 24 -> stack0 m lo (bv_unsigned sp) ->
    Forall (fs_scratch H LF) XS -> as_RFS H LF m -> xpres H LB (bv_unsigned sp) (XS ++ X0) m0 m ->
    0 <= uf <= DECEXTS_CF rem0 -> as_AL H s' + as_Cm H (DECEXTS_CM rem0) + as_Cf H uf + RAISE_COST H (mid_err M) >= as_AL H s00 ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR (Z_to_bv 64 ADX_R10) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) x4 x5 (Z_to_bv 64 0) x7 (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr (ee + 56) 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
           F (ret_pc (Z_to_bv 64 ADX_R10)) fc None m (seg_rom asegs) ->
    as_SR H (decexts_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LIB LB LF M ee pk base len cur0 rem0 E bs lo B m0 mo) (mkCfg msF mo').
  Proof.
    intros m s' errv' P xs cur rem Lf LE c0 E' pad1 pad2 pad3 pad4 XS uf msF mo' t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x5 x7 M'
           MI AC ST FR ERR AUX HP PL LM DL L1 L2 L3 L4 EC ESH PK PIN CR RR BS ACCB ACCP SK0 FXS RFS XP0 UF HAL KREL MP VIS. subst M'.
    cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. unfold pk_in in PIN. pose proof BSL as BSL'. unfold zlength in BSL'.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & ESHD & EBL'). cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ERRPH_mid] in MF, CP, EPm, EX, VD, FIT, ESHD, EBL'.
    pose proof (es_after _ _ _ _ LM DL) as HES0.
    assert (INF : forall b, In b (blocks_ERRST E' ++ LE ++ LB) -> In b Lf) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL| exact Hb]).
    assert (SUBLF : forall b, In b LB -> In b Lf) by (intros b Hb; apply INF; do 2 (apply in_or_app; right); exact Hb).
    assert (HB : forall b, In b Lf -> 0 < blk_addr b /\ AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). repeat split; assumption. }
    assert (EIN : In (en_id E, ee, ENTRY_SIZE) Lf) by (apply SUBLF; exact EIN0).
    pose proof (ah_blocks H HH _ _ _ _ HP EIN) as (EP0 & _ & _ & _ & EH & EFS & EAP). cbn [blk_addr blk_size fst snd] in EP0, EH, EFS, EAP. unfold ENTRY_SIZE in EH, EFS.
    assert (DJE : forall b, In b Lf -> blk_id b <> en_id E -> blk_addr b + blk_size b + 16 <= ee \/ ee + 104 + 16 <= blk_addr b).
    { intros b Hb NE. pose proof (ah_disj H HH _ _ _ _ _ HP Hb EIN NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ. unfold ENTRY_SIZE in DJ. exact DJ. }
    pose proof (Permutation_NoDup (Permutation_map blk_id PL) (ah_nodup H HH _ _ _ HP)) as NDf.
    assert (NELE : forall b, In b (blocks_ERRST E' ++ LE) -> blk_id b <> en_id E).
    { intros b Hb K0. rewrite app_assoc in NDf. exact (nodup_ids_app_ne _ _ _ _ NDf Hb EIN0 K0). }
    assert (HES : forall c1, mid_err M = ErrReady c1 -> In (ec_es c1) Lf /\ blk_size (ec_es c1) = ERRST_SIZE).
    { intros c1 PH. destruct (HES0 c1 PH) as (I1 & Z1 & _). split; [apply SUBLF; apply LIBSUB; exact I1| exact Z1]. }
    pose proof ESH as (ETOP & EAD & ES1 & ES2 & ES3 & ES4 & _). cbn [EW en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o] in ES1, ES2, ES3, ES4.
    pose proof OF0 as (Q1 & Q2 & Q3 & Q4).
    assert (WE : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(ee, ee + 104)]).
    { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. pose proof (aapp_not_shadowland _ _ EAP). unfold ENTRY_SIZE in *. lia. }
    assert (CWE : Forall (aclient_write_ok H Lf) [(ee, ee + 104)]).
    { apply Forall_cons; [| apply Forall_nil]. right; right; left. exists (en_id E, ee, ENTRY_SIZE). split; [exact EIN| cbn; unfold ENTRY_SIZE; lia]. }
    assert (AL0 : 0 <= as_AL H s').
    { pose proof (aCf_mono H HH uf (DECEXTS_CF rem0) ltac:(clear - UF; lia)). unfold DECEXTS_COST in HAL0. clear - HAL0 HAL H0. lia. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply adx_segF4 with (ee := ee) (E := EW P xs);
      [exact EC| lia| exact ETOP| lia| eapply addressable_accessible; [exact EAD| lia| unfold ENTRY_SIZE; lia| exact ETOP]| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & MU1 & WM1 & MI1 & EC1 & VIS1). unfold ENTRY_SIZE in MU1. pose proof (ah_mpres_trans H HH _ _ _ MP MP1) as MPc1.
    cbn [EW en_version en_pname en_pname_o en_publen en_pub en_pub_o en_nsuites en_suites en_suites_o en_maxname en_cfgid en_exts_o en_loadtime en_forretry en_enclen en_encoded en_encoded_o en_id] in EC1.
    assert (ST1 : stk asegs m1 lo (bv_unsigned sp + -144)) by (eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| cbn; clear - EH CEIL; lia]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1|]; apply Forall_cons; [eapply aconst_ok_aapp; [exact EAP| lia| unfold ENTRY_SIZE; lia]| apply Forall_nil]).
    assert (FR1 : rw_cells asegs m1 (bv_unsigned sp + -144) (adx_frame j0 pk ee s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR| exact MU1| exact WM1| cbn; clear - EH CEIL LO8K; lia]).
    assert (ERR1 : rw_cells asegs m1 (errno_addr tp) [C4 errv']).
    { rewrite TP in ERR |- *. eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. rewrite unsigned_lit by (unfold ATP; lia). cbn. pose proof (aapp_bounds _ _ EAP ltac:(unfold ENTRY_SIZE; lia)) as (QQ1 & _). unfold ATP, AIMG_TOP in *. clear - QQ1. lia. }
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CWE]).
    assert (HP1 : as_RHEAP H s' Lf m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CWE]).
    assert (XPE : forall X, xpres H (as_lb_remove H (en_id E) Lf) (bv_unsigned sp + -144) X m m1).
    { intros X. eapply (xpres_of_munch_listed H HH); [exact HP| exact EIN| clear - CEIL LO8K; lia| exact MU1| exact WM1|]. apply Forall_cons; [right; left; cbn; unfold ENTRY_SIZE; lia| apply Forall_nil]. }
    assert (REME : forall b, In b Lf -> blk_id b <> en_id E -> In b (as_lb_remove H (en_id E) Lf)).
    { intros b Hb NE. apply (proj2 (proj2 (proj2 (alb_remove_exact H HH _ _ _ _ (ah_nodup H HH _ _ _ HP) EIN)) b)). split; [exact Hb| exact NE]. }
    assert (LM1 : LIBMID (LE ++ LIB) m1 (mkMID 1 (CtxReady x) (ErrReady c0) E' (mid_vdso M))).
    { eapply (LIBMID_xpres0 H); [exact LM| reflexivity| apply XPE| |].
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        + apply REME; [apply INF; apply in_or_app; right; apply in_or_app; left; exact Hb| apply NELE; apply in_or_app; right; exact Hb].
        + apply REME; [apply SUBLF; apply LIBSUB; exact Hb| exact (IDS _ _ Hb ltac:(left; reflexivity))].
      - cbn [mid_errblocks mid_E]. intros b Hb. apply REME; [apply INF; apply in_or_app; left; exact Hb| apply NELE; apply in_or_app; left; exact Hb]. }
    pose proof LM1 as (IM1 & _ & _ & _ & _ & _ & _ & _ & G11 & _).
    assert (PK1 : rw_cells asegs m1 pk (pk_cells cur base rem)) by (eapply rw_cells_transport; [exact PK| exact MU1| exact WM1| cbn; clear - EH CEIL LO8K SPK; lia]).
    assert (BS1 : bytes_at asegs m1 base bs).
    { eapply bytes_at_transport; [exact BS| exact MU1|]. cbn. split; [| exact I].
      pose proof (DJE (pbin, base, len) (SUBLF _ BIN) ltac:(cbn; intros K0; apply EBIN; symmetry; exact K0)) as KKq. cbn [blk_addr blk_size fst snd] in KKq. clear - KKq BSL'. lia. }
    assert (XP01 : xpres H LB (bv_unsigned sp) (XS ++ X0) m0 m1).
    { eapply (xpres_trans H); [exact XP0|]. eapply (xpres_weaken H); [| apply Z.le_refl| exact SUBLF| intros q Hq; exact Hq].
      eapply (xpres_of_munch H _ Lf); [exact HH| exact HP| exact MU1| exact WM1|].
      apply Forall_cons; [right; cbn; intros q Hq; apply rin_ivs_app; right; unfold X0, ENTRY_SIZE; cbn [rin_ivs fst snd]; right; left; exact Hq| apply Forall_nil]. }
    assert (EAD1 : addressable m1 ee ENTRY_SIZE).
    { eapply addressable_acrossW; [exact EAD| exact MU1| exact WM1| clear - EP0 EH ACEILB; unfold AAPP_HI; lia| exact ETOP| exact WE]. }
    assert (OSx : forall Pf o, ofield LB Pf o -> oshad m Pf o -> oshad m1 Pf o).
    { intros Pf o OFo OSo. eapply (oshad_entry_write s' Lf m); [exact HP| exact EIN| exact SUBLF| exact OFo| exact MU1| exact WM1| exact EC1| exact ETOP| exact EAD1| exact OSo]. }
    assert (ACCB1 : accessible m1 base len) by (eapply accessible_across; [exact ACCB| exact MU1| exact WE]).
    assert (ACCP1 : accessible m1 pk 24) by (eapply accessible_across; [exact ACCP| exact MU1| exact WE]).
    assert (SK01 : stack0 m1 lo (bv_unsigned sp)).
    { eapply stack0_transport; [exact SK0| exact MU1| exact WM1|]. apply Forall_cons; [eapply stack0_ok_aapp; [exact EAP| lia| unfold ENTRY_SIZE; lia]| apply Forall_nil]. }
    assert (RFS1 : as_RFS H LF m1).
    { eapply (ah_RFS_frame H HH); [exact RFS| exact MU1| exact WM1|]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd].
      pose proof (aapp_bounds _ _ EAP ltac:(unfold ENTRY_SIZE; lia)) as (QQ1 & _). unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *. clear - QQ1 EFS. lia. }
    clear MU1 WM1 HP FR ERR AUX PK BS XP0 EC MI ST AC ESH EAD ACCB ACCP SK0 RFS XPE.
    (* [comment removed for export] *)
    pose proof aextfree_null_spec as XF. unfold extfree_null_stmt, sknull_stmt_at in XF.
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply XF with (lo := lo); rewrite ?unsigned_lit by lia; [exact ST1| exact CEIL| unfold FR_ossl_echext_free; clear - LO8K; lia| exact MI1| exact AC1]|].
    clear XF. intros msF2 mo2 KREL2 MP2 (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m2 & VIS2 & MU2 & WM2 & MI2 & AC2 & ST2).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in MU2, ST2 by lia. pose proof (ah_mpres_trans H HH _ _ _ MPc1 MP2) as MPc2.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply adx_segF5; exact MI2|]. intros msF3 mo3 KREL3 MP3 VIS3. pose proof (ah_mpres_trans H HH _ _ _ MPc2 MP3) as MPc3.
    assert (CW2 : Forall (aclient_write_ok H Lf) [(lo, bv_unsigned sp + -144)]) by (apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
    assert (HP2 : as_RHEAP H s' Lf m2) by (eapply (ah_RHEAP_frame H HH); [exact HP1| exact MU2| exact WM2| exact CW2]).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -144) (adx_frame j0 pk ee s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2| cbn; lia]).
    assert (XP02 : xpres H LB (bv_unsigned sp) (XS ++ X0) m0 m2).
    { eapply (xpres_trans H); [exact XP01|]. eapply (xpres_weaken H); [| apply Z.le_refl| exact SUBLF| intros q Hq; exact Hq].
      eapply (xpres_of_munch H _ Lf); [exact HH| exact HP1| exact MU2| exact WM2|]. apply Forall_cons; [left; cbn; clear - SPR CEIL; lia| apply Forall_nil]. }
    pose proof (acfree_null_spec H HH) as CF. unfold cfree_null_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (LB := Lf) (s := s') (CH := (bv_unsigned sp, bv_unsigned ra) :: CH); [exact VIS3| ..]; rewrite ?unsigned_lit by (unfold ADX_R12; lia).
      all: try first [exact HP2| exact KREL3| exact ST2| exact CEIL| exact MI2| exact TP| exact AC2].
      all: lazymatch goal with
           | |- as_rauxv_ok _ _ _ => eapply (ah_rauxv_frame H HH); [exact AUX1| exact MU2| exact WM2| exact CW2]
           | |- _ <= B => clear - SPB SPR; lia
           | |- _ mod 16 = 0 => clear - SPA SPR; replace (bv_unsigned sp + -144) with (bv_unsigned sp - 9 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
           | |- _ <= _ - CFREE_STACK => clear - LO; unfold DECEXTS_STACK, FR_ech_decode_echconfig_exts, SKPOPFREE_STACK, EXTFREE_STACK, CFREE_STACK, FR_ossl_echext_free, FR_sk_pop_free in LO |- *; lia
           | |- rw_cells _ _ (errno_addr _) _ => rewrite TP in ERR1 |- *; eapply rw_cells_transport; [exact ERR1| exact MU2| exact WM2|]; rewrite unsigned_lit by (unfold ATP; lia); cbn; unfold ATP; clear - CEIL ACEILB; lia
           | |- as_chain _ _ _ _ => eapply (chain_at (XS ++ X0)); [exact XP02| eapply X0XR_chain; [exact HP2| exact RFS1| exact FXS| exact EIN| exact HES]| exact FR2]
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - SPR; lia| specialize (CHS _ _ Hin); clear - CHS; lia]
           | |- as_Cf _ 0 <= _ => rewrite (aCf0 H HH); exact AL0
           | |- IMPL_mem _ => eapply IMPL_across; [exact MU2| exact WM2| unfold A_malloc_impl; cbn; clear - CEIL ACEILB; lia| exact IM1]
           | |- GOT_mem _ => eapply GOT_across; [exact MU2| exact WM2| unfold A_got_CRYPTO_malloc; cbn; clear - CEIL ACEILB; lia| exact G11]
           | |- ?G => idtac "CF0PRE" G
           end.
      all: fail "CF0". }
    clear CF. intros [ms4 mo4] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0' & y1' & y2' & h0' & h1' & h2' & h3' & h4' & h5' & h6' & h7' & y3' & y4' & y5' & y6' & m4 & s4' & VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & XP4 & HP4 & IM4 & GM4 & AL4).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in ST4, XP4 by lia. pose proof (ah_mpres_trans H HH _ _ _ MPc3 MP4) as MPc4. rewrite (aCf0 H HH) in AL4.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply adx_segF6; exact MI4|]. intros msF5 mo5 KREL5 MP5 VIS5. pose proof (ah_mpres_trans H HH _ _ _ MPc4 MP5) as MPc5.
    assert (FR4 : rw_cells asegs m4 (bv_unsigned sp + -144) (adx_frame j0 pk ee s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by (eapply (xpres_rw_cells' H); [exact XP4| exact FR2| left; lia| apply Forall_nil]).
    eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5| eapply adx_segE with (lo := lo); [exact FR4| exact ST4| exact CEIL| clear - LO8K; lia| exact MI4]|].
    intros msF6 mo6 KREL6 MP6 [VIS6 ST6]. pose proof (ah_mpres_trans H HH _ _ _ MPc5 MP6) as MPc6.
    (* [comment removed for export] *)
    assert (MU24 : munch [(lo, bv_unsigned sp + -144)] m1 m2) by exact MU2.
    assert (XP14 : xpres H Lf (bv_unsigned sp + -144) [] m1 m4).
    { eapply (xpres_trans H); [| exact XP4]. eapply (xpres_of_munch H _ Lf); [exact HH| exact HP1| exact MU2| exact WM2|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (XPL4 : forall L X, (forall b, In b L -> In b Lf) -> xpres H L (bv_unsigned sp + -144) X m1 m4).
    { intros L X SUBL. eapply (xpres_weaken H); [exact XP14| apply Z.le_refl| exact SUBL| intros q Hq; destruct Hq]. }
    assert (LEN16 : length (es_slots E') = 16%nat) by exact (proj1 (proj1 EX)).
    pose proof (errst_fits_bounds _ LEN16 FIT) as [ECb EBb].
    apply (ah_done H HH). unfold decexts_post. cbn [cfg_ms cfg_model].
    exists y0', y1', y2', h1', h2', h3', h4', h5', h6', h7', y3', y4', y5', y6', m4, errv', s4', 0, (mkMID 1 (CtxReady x) (ErrReady c0) E' (mid_vdso M)), None, 0, [], LE, cur, rem, XS.
    cbn [app mid_errblocks mid_E mid_ctx mid_vdso]. unfold zlength in *.
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
         | |- _ = MS _ _ _ _ _ _ _ => exact VIS6
         | |- as_AKREL _ _ _ => exact KREL6
         | |- as_MPRES _ _ _ => exact MPc6
         | |- mem_inv _ _ => exact MI4
         | |- ACONST _ => exact AC4
         | |- stk _ _ _ _ => exact ST6
         | |- stack0 _ _ _ => eapply (stack0_xpres H); [apply (XPL4 Lf []); intros b Hb; exact Hb| exact SK01| apply Forall_nil]
         | |- rw_cells _ _ (errno_addr _) _ => exact ERR4
         | |- as_rauxv_ok _ _ _ => exact AUX4
         | |- as_RHEAP _ _ _ _ => eapply (HHx_rheap_perm H HHx); [exact HP4| exact PL]
         | |- LIBMID _ _ _ => eapply (LIBMID_xpres0 H); [exact LM1| reflexivity| apply (XPL4 Lf []); intros b Hb; exact Hb| | cbn [mid_errblocks mid_E]; intros b Hb; apply INF; apply in_or_app; left; exact Hb];
                              intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply INF; apply in_or_app; right; apply in_or_app; left; exact Hb| apply SUBLF; apply LIBSUB; exact Hb]
         | |- mid_step _ _ => unfold mid_step; cbn [mid_flag mid_ctx mid_err mid_vdso]; split; [reflexivity|]; split; [intros b Hb; rewrite CX in Hb; exact Hb|]; split; [| auto];
                             intros c1 Hc1; destruct (HES0 c1 Hc1) as (_ & _ & -> & _); reflexivity
         | |- mid_newlib_ok _ _ _ => unfold mid_newlib_ok; cbn [mid_ctx mid_err]; exists [], LE; split; [apply Permutation_refl|]; rewrite CX; split; [reflexivity|];
                                  destruct (mid_err M) as [|c1]; [exact DL|]; destruct (HES0 c1 eq_refl) as (_ & _ & _ & ->); reflexivity
         | |- CtxReady _ = mid_ctx _ => symmetry; exact CX
         | |- mid_vdso _ = mid_vdso _ => reflexivity
         | |- Z.of_nat (length _) <= ERRSTR_CNT => exact ECb
         | |- lb_bytes _ <= ERRSTR_BYTES => exact EBb
         | |- ENTRYobj _ _ _ _ =>
             unfold ENTRYobj; cbn [en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o];
             split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|];
                     eapply (xpres_rw_cells' H); [apply (XPL4 Lf []); intros b Hb; exact Hb| exact EC1| right; right; left; exists (en_id E, ee, ENTRY_SIZE); split; [exact EIN| unfold entry_cells; cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]; unfold ENTRY_SIZE; lia]| apply Forall_nil]|];
             split; [apply in_or_app; right; exact EIN0|];
             split; [eapply ofield_LB_mono; [exact Q1| intros b Hb; apply in_or_app; right; exact Hb]|];
             split; [eapply ofield_LB_mono; [exact Q2| intros b Hb; apply in_or_app; right; exact Hb]|];
             split; [eapply ofield_LB_mono; [exact Q3| intros b Hb; apply in_or_app; right; exact Hb]|];
             split; [eapply ofield_LB_mono; [exact Q4| intros b Hb; apply in_or_app; right; exact Hb]|]; reflexivity
         | |- ENTRY_shad _ _ _ =>
             eapply (ENTRY_shad_frame_law H _ m1 m4); [| | apply (XPL4 LB []); exact SUBLF|];
             [ unfold ENTRY_shad; cbn [en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o EXTS_shad];
               split; [exact ETOP|]; split; [exact EAD1|]; split; [exact (OSx _ _ Q1 ES1)|]; split; [exact (OSx _ _ Q2 ES2)|]; split; [exact (OSx _ _ Q3 ES3)|]; split; [exact (OSx _ _ Q4 ES4)| exact I]
             | intros b Hb; unfold blocks_ENTRY in Hb; cbn [en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o blocks_EXTS] in Hb; rewrite app_nil_r in Hb;
               destruct Hb as [<-|Hb]; [exact EIN0|];
               repeat (apply in_app_or in Hb; destruct Hb as [Hb|Hb]); first [exact (ofield_owned _ _ _ _ Q1 Hb)| exact (ofield_owned _ _ _ _ Q2 Hb)| exact (ofield_owned _ _ _ _ Q3 Hb)| exact (ofield_owned _ _ _ _ Q4 Hb)]
             | intros b Hb; pose proof (HB b (SUBLF _ ltac:(unfold blocks_ENTRY in Hb; cbn [en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o blocks_EXTS] in Hb; rewrite app_nil_r in Hb;
                                                     destruct Hb as [<-|Hb]; [exact EIN0|];
                                                     repeat (apply in_app_or in Hb; destruct Hb as [Hb|Hb]); first [exact (ofield_owned _ _ _ _ Q1 Hb)| exact (ofield_owned _ _ _ _ Q2 Hb)| exact (ofield_owned _ _ _ _ Q3 Hb)| exact (ofield_owned _ _ _ _ Q4 Hb)]))) as (_ & _ & K5 & _);
               clear - K5 CEIL LO8K; lia ]
         | |- Permutation _ _ => apply Permutation_refl
         | |- _ \/ _ => right; repeat split; reflexivity
         | |- 5 * _ <= _ => cbn [length]; clear - RR PIN; lia
         | |- pk_in _ _ _ _ => unfold pk_in; clear - PIN; lia
         | |- lb_bytes [] <= _ => cbn [lb_bytes fold_right]; unfold SK_SIZE; clear - REM1 PIN RR; lia
         | |- rw_cells _ _ pk _ => eapply (xpres_rw_cells' H); [apply (XPL4 Lf []); intros b Hb; exact Hb| exact PK1| left; clear - SPK; lia| apply Forall_nil]
         | |- bytes_at _ _ base _ => eapply (xpres_bytes_at' H); [apply (XPL4 Lf []); intros b Hb; exact Hb| exact BS1| | apply Forall_nil]; right; right; left; exists (pbin, base, len); split; [exact (SUBLF _ BIN)| cbn [blk_addr blk_size fst snd]; clear - BSL'; lia]
         | |- BUF_shad _ base _ => unfold BUF_shad; eapply (ashobj_accessible_xpres_sub H HH) with (SP := bv_unsigned sp + -144) (X := @nil (Z * Z)); [exact HP1| intros b Hb; exact Hb| clear - CEIL LO8K; lia| | exact ACCB1| apply (XPL4 Lf []); intros b Hb; exact Hb| apply Forall_nil];
                                   left; exists (pbin, base, len); split; [exact (SUBLF _ BIN)| cbn [blk_addr blk_size fst snd]; lia]
         | |- base <= _ => clear - PIN; lia
         | |- 0 <= _ => clear - PIN; lia
         | |- _ + _ <= base + len => clear - PIN; lia
         | |- cur0 + rem0 = _ => exact CR
         | |- Forall (fs_scratch _ _) _ => exact FXS
         | |- as_RFS _ _ _ => eapply (RFS_via_xpres H HH); [exact RFS1| apply (XPL4 Lf []); intros b Hb; exact Hb| apply Forall_nil]
         | |- athr_cells _ => eapply (ah_thr H HH); exact HP4
         | |- xpres H LB _ _ m0 _ => eapply (xpres_trans H); [exact XP02|]; eapply (xpres_weaken H); [exact XP4| clear - SPR; lia| exact SUBLF| intros q Hq; destruct Hq]
         | |- as_AL _ _ >= _ => assert (RCdE : RAISE_COSTd H (mid_err M) (ErrReady c0) = RAISE_COST H (mid_err M)) by (unfold RAISE_COSTd, RAISE_COST, raise_bytes; cbn [errph_bytes]; rewrite Z.sub_0_r; reflexivity);
                               unfold DECEXTS_SPENT; cbn [mid_err]; rewrite RCdE; pose proof (aCf_mono H HH uf (DECEXTS_CF rem0) ltac:(clear - UF; lia)); clear - HAL AL4 UF H0; lia
         | |- ?G => idtac "FEND" G
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma blocks_E_LB : forall b, In b (blocks_ENTRY ee E) -> In b LB.
  Proof.
    clear - OF0 EIN0 XO0 XE0. intros b Hb. pose proof OF0 as (Q1 & Q2 & Q3 & Q4). unfold blocks_ENTRY in Hb. rewrite XO0, XE0 in Hb. cbn [blocks_EXTS] in Hb. rewrite app_nil_r in Hb.
    destruct Hb as [<-|Hb]; [exact EIN0|].
    repeat (apply in_app_or in Hb; destruct Hb as [Hb|Hb]); first [exact (ofield_owned _ _ _ _ Q1 Hb)| exact (ofield_owned _ _ _ _ Q2 Hb)| exact (ofield_owned _ _ _ _ Q3 Hb)| exact (ofield_owned _ _ _ _ Q4 Hb)].
  Qed.
  Lemma blocks_EW_none : blocks_ENTRY ee (EW 0 None) = blocks_ENTRY ee E.
  Proof. rewrite blocks_EW. cbn [blocks_EXTS]. apply app_nil_r. Qed.

  (* [comment removed for export] *)
  Lemma fail_cf_bound : forall P K es c uf,
    XINV P (Some (K, es)) c -> 0 <= c <= rem0 -> 0 <= uf <= ADX_PUSH_CF * zlength es ->
    0 <= lb_bytes (EBof K es) -> uf + lb_bytes (EBof K es) + 8 * sk_cap K + 56 <= DECEXTS_CF rem0.
  Proof.
    clear. intros P K es c uf XI Hc Huf HE. cbn [XINV] in XI. destruct XI as (_ & K4 & [C0 C5] & E5 & EB). unfold ADX_PUSH_CF, DECEXTS_CF in *. unfold zlength in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_fail_tail : forall m s' errv' P xs NB c cur rem Lr LE c0 E' XS uf msF mo'
                             (t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x5 x6 x7 x8 x11 : word),
    let M' := mkMID 1 (CtxReady x) (ErrReady c0) E' (mid_vdso M) in
    mem_inv asegs m -> ACONST m -> stk asegs m lo spq -> rw_cells asegs m spq (adx_frame j0 pk ee s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
    rw_cells asegs m (errno_addr tp) [C4 errv'] -> as_rauxv_ok H m B ->
    as_RHEAP H s' Lr m -> Permutation Lr (blocks_ERRST E' ++ LE ++ NB ++ LB) ->
    LIBMID (LE ++ LIB) m M' -> errph_delta (mid_err M) LE c0 ->
    ENTRYobj (NB ++ LB) m ee (EW P xs) -> ENTRY_shad m ee (EW P xs) -> Permutation (blocks_EXTS P xs) NB -> XINV P xs c -> 0 <= c <= rem0 ->
    rw_cells asegs m pk (pk_cells cur base rem) -> pk_in base len cur rem -> cur0 + rem0 = cur + rem -> rem <= rem0 ->
    bytes_at asegs m base bs -> accessible m base len -> accessible m pk 24 -> stack0 m lo (bv_unsigned sp) ->
    Forall (fs_scratch H LF) XS -> as_RFS H LF m -> xpres H LB (bv_unsigned sp) (XS ++ X0) m0 m ->
    0 <= uf <= ADX_PUSH_CF * xs_len xs -> as_AL H s' + as_Cm H (DECEXTS_CM rem0) + as_Cf H uf + RAISE_COST H (mid_err M) >= as_AL H s00 ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR (Z_to_bv 64 ADX_RA3) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) x4 x5 x6 x7 x8 (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) x11 t3 t4 t5 t6)
           F (ret_pc (Z_to_bv 64 ADX_RA3)) fc None m (seg_rom asegs) ->
    as_SR H (decexts_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LIB LB LF M ee pk base len cur0 rem0 E bs lo B m0 mo) (mkCfg msF mo').
  Proof.
    intros m s' errv' P xs NB c cur rem Lr LE c0 E' XS uf msF mo' t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x4 x5 x6 x7 x8 x11 M'
           MI AC ST FR ERR AUX HP PL LM DL EO ESH PB XI HC PK PIN CR RR BS ACCB ACCP SK0 FXS RFS XP0 UF HAL KREL MP VIS. subst M'.
    cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. pose proof PIN as PIN'. unfold pk_in in PIN'. pose proof BSL as BSL'. unfold zlength in BSL'.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & ESHD & EBL'). cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ERRPH_mid] in MF, CP, EPm, EX, VD, FIT, ESHD, EBL'.
    pose proof (es_after _ _ _ _ LM DL) as HES0.
    assert (INF : forall b, In b (blocks_ERRST E' ++ LE ++ NB ++ LB) -> In b Lr) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL| exact Hb]).
    assert (SUBLR : forall b, In b LB -> In b Lr) by (intros b Hb; apply INF; do 3 (apply in_or_app; right); exact Hb).
    assert (SUBNR : forall b, In b (NB ++ LB) -> In b Lr) by (intros b Hb; apply INF; do 2 (apply in_or_app; right); exact Hb).
    assert (HB : forall b, In b Lr -> 0 < blk_addr b /\ AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). repeat split; assumption. }
    assert (EIN : In (en_id E, ee, ENTRY_SIZE) Lr) by (apply SUBLR; exact EIN0).
    pose proof (ah_blocks H HH _ _ _ _ HP EIN) as (EP0 & _ & _ & _ & EH & EFS & EAP). cbn [blk_addr blk_size fst snd] in EP0, EH, EFS, EAP. unfold ENTRY_SIZE in EH, EFS.
    assert (DJE : forall b, In b Lr -> blk_id b <> en_id E -> blk_addr b + blk_size b + 16 <= ee \/ ee + 104 + 16 <= blk_addr b).
    { intros b Hb NE. pose proof (ah_disj H HH _ _ _ _ _ HP Hb EIN NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ. unfold ENTRY_SIZE in DJ. exact DJ. }
    pose proof (Permutation_NoDup (Permutation_map blk_id PL) (ah_nodup H HH _ _ _ HP)) as NDr.
    assert (HES : forall c1, mid_err M = ErrReady c1 -> In (ec_es c1) Lr /\ blk_size (ec_es c1) = ERRST_SIZE).
    { intros c1 PH. destruct (HES0 c1 PH) as (I1 & Z1 & _). split; [apply SUBLR; apply LIBSUB; exact I1| exact Z1]. }
    (* [comment removed for export] *)
    assert (NBNE : forall b b', In b NB -> In b' (blocks_ERRST E' ++ LE ++ LB) -> blk_id b <> blk_id b').
    { intros b b' Hb Hb' EQ. pose proof NDr as ND1. rewrite (app_assoc (blocks_ERRST E') LE (NB ++ LB)) in ND1.
      assert (CASE : In b' (blocks_ERRST E' ++ LE) \/ In b' LB).
      { apply in_app_or in Hb'. destruct Hb' as [Hb'|Hb']; [left; apply in_or_app; left; exact Hb'|].
        apply in_app_or in Hb'. destruct Hb' as [Hb'|Hb']; [left; apply in_or_app; right; exact Hb'| right; exact Hb']. }
      destruct CASE as [Hb'2|Hb'2].
      - exact (nodup_ids_app_ne _ _ _ _ ND1 Hb'2 ltac:(apply in_or_app; left; exact Hb) (eq_sym EQ)).
      - apply nd_tail in ND1. exact (nodup_ids_app_ne _ _ _ _ ND1 Hb Hb'2 EQ). }
    pose proof ESH as (ETOP & EAD & ES1 & ES2 & ES3 & ES4 & XSH). cbn [EW en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o] in ES1, ES2, ES3, ES4, XSH.
    pose proof OF0 as (Q1 & Q2 & Q3 & Q4).
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC) & _ & O1 & O2 & O3 & O4 & XT).
    cbn [EW en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o] in XT, EC.
    assert (PR : 0 <= P < 2^64).
    { revert XT. unfold EXTS. destruct xs as [[K es]|]; intros XT; [| rewrite XT; lia].
      destruct XT as (XP1 & SO & _). destruct SO as (_ & _ & KIN & _). pose proof (HB _ (SUBNR _ KIN)) as (_ & _ & K5 & _). cbn [blk_addr blk_size fst snd] in K5. unfold SK_SIZE in K5. lia. }
    assert (ESH0 : ENTRY_shad m ee (EW 0 None)).
    { unfold ENTRY_shad. cbn [EW en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o EXTS_shad].
      split; [exact ETOP|]. split; [exact EAD|]. split; [exact ES1|]. split; [exact ES2|]. split; [exact ES3|]. split; [exact ES4| exact I]. }
    assert (WE : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp + -144)]).
    { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right. unfold AHI_LO. clear - CEIL ACEILB. lia. }
    assert (UF0 : uf <= DECEXTS_CF rem0).
    { revert XI UF. destruct xs as [[K es]|]; cbn [XINV xs_len]; intros XI UF; unfold ADX_PUSH_CF, DECEXTS_CF, zlength in *; [| lia].
      destruct XI as (_ & K4 & [C0 C5] & E5 & EB). lia. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply adx_segF2 with (ee := ee) (E := EW P xs);
      [exact EC| lia| exact ETOP| cbn [EW en_exts]; exact PR| eapply addressable_accessible; [exact EAD| lia| unfold ENTRY_SIZE; lia| exact ETOP]
      | exact FR| clear - LO8K CEIL ACEILB; lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 VIS1. cbn [EW en_exts] in VIS1. pose proof (ah_mpres_trans H HH _ _ _ MP MP1) as MPc1.
    revert XT XSH PB XI UF. unfold EXTS, EXTS_shad. destruct xs as [[K es]|]; intros XT XSH PB XI UF.
    2: { (* [comment removed for export] *)
      subst P. cbn [blocks_EXTS] in PB. pose proof (Permutation_nil PB) as NBN. subst NB. cbn [app] in PL, INF, NBNE.
      eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply askset_thunks_null_spec with (lo := lo); rewrite ?unsigned_lit by lia;
        [exact ST| exact CEIL| clear - LO8K; lia| exact MI| exact AC]|].
      intros msF2 mo2 KREL2 MP2 (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m2 & VIS2 & MU2 & WM2 & MI2 & AC2 & ST2).
      rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in MU2, ST2 by lia. pose proof (ah_mpres_trans H HH _ _ _ MPc1 MP2) as MPc2.
      assert (GE2 : GOT_echfree m2) by (eapply GOT_echfree_across; [exact MU2| exact WM2| unfold A_got_ossl_echext_free; cbn; clear - CEIL ACEILB; lia| exact G2]).
      (* [comment removed for export] *)
      eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply adx_segF3; [exact GE2| lia| exact MI2]|].
      intros msF3 mo3 KREL3 MP3 VIS3. pose proof (ah_mpres_trans H HH _ _ _ MPc2 MP3) as MPc3.
      eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply ask_pop_free_null_spec with (lo := lo); rewrite ?unsigned_lit by lia;
        [exact ST2| exact CEIL| unfold FR_sk_pop_free; clear - LO8K; lia| exact MI2| exact AC2]|].
      intros msF4 mo4 KREL4 MP4 (y0' & y1' & y2' & h1' & h2' & h3' & h4' & h5' & h6' & h7' & y3' & y4' & y5' & y6' & m4 & VIS4 & MU4 & WM4 & MI4 & AC4 & ST4).
      rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in MU4, ST4 by lia. pose proof (ah_mpres_trans H HH _ _ _ MPc3 MP4) as MPc4.
      assert (MU24 : munch [(lo, bv_unsigned sp + -144)] m m4).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU4]]; intros q Hq; cbn in Hq |- *; lia. }
      pose proof (wmono_trans asegs _ _ _ WM2 WM4) as WM24. clear MU2 WM2 MU4 WM4.
      assert (CW : Forall (aclient_write_ok H Lr) [(lo, bv_unsigned sp + -144)]) by (apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
      assert (XPs : forall L, (forall b, In b L -> In b Lr) -> xpres H L (bv_unsigned sp + -144) [] m m4).
      { intros L SUBL. eapply (xpres_weaken H); [| apply Z.le_refl| exact SUBL| intros q Hq; exact Hq].
        eapply (xpres_of_munch H _ Lr); [exact HH| exact HP| exact MU24| exact WM24|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      eapply (dx_fail_end m4 s' errv' 0 None cur rem Lr LE c0 E' pad1 pad2 pad3 pad4 XS uf msF4 mo4); try eassumption.
      all: cbv delta [spq]; lazymatch goal with
           | |- ACONST _ => exact AC4
           | |- stk _ _ _ _ => exact ST4
           | |- rw_cells _ _ (bv_unsigned sp + -144) _ => eapply rw_cells_transport; [exact FR| exact MU24| exact WM24| cbn; lia]
           | |- rw_cells _ _ (errno_addr _) _ => rewrite TP in ERR |- *; eapply rw_cells_transport; [exact ERR| exact MU24| exact WM24|]; rewrite unsigned_lit by (unfold ATP; lia); cbn; unfold ATP; clear - CEIL ACEILB; lia
           | |- as_rauxv_ok _ _ _ => eapply (ah_rauxv_frame H HH); [exact AUX| exact MU24| exact WM24| exact CW]
           | |- as_RHEAP _ _ _ _ => eapply (ah_RHEAP_frame H HH); [exact HP| exact MU24| exact WM24| exact CW]
           | |- LIBMID _ _ _ => eapply (LIBMID_xpres0 H); [exact LM| reflexivity| apply (XPs Lr); intros b Hb; exact Hb| | cbn [mid_errblocks mid_E]; intros b Hb; apply INF; apply in_or_app; left; exact Hb];
                                intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply INF; apply in_or_app; right; apply in_or_app; left; exact Hb| apply SUBLR; apply LIBSUB; exact Hb]
           | |- rw_cells _ _ ee _ => eapply rw_cells_transport; [exact EC| exact MU24| exact WM24| cbn; clear - EH CEIL; lia]
           | |- ENTRY_shad _ _ _ => eapply (ENTRY_shad_frame_law H _ m m4); [exact ESH0| intros b Hb; exact Hb| apply (XPs _); intros b Hb; rewrite blocks_EW_none in Hb; apply SUBLR; exact (blocks_E_LB _ Hb)|];
                                     intros b Hb; rewrite blocks_EW_none in Hb; pose proof (HB _ (SUBLR _ (blocks_E_LB _ Hb))) as (_ & _ & K5 & _); clear - K5 CEIL LO8K; lia
           | |- rw_cells _ _ pk _ => eapply rw_cells_transport; [exact PK| exact MU24| exact WM24| cbn; clear - SPK; lia]
           | |- pk_in _ _ _ _ => exact PIN
           | |- bytes_at _ _ base _ => eapply (xpres_bytes_at' H); [apply (XPs Lr); intros b Hb; exact Hb| exact BS| | apply Forall_nil]; right; right; left; exists (pbin, base, len); split; [exact (SUBLR _ BIN)| cbn [blk_addr blk_size fst snd]; clear - BSL'; lia]
           | |- accessible _ base _ => eapply accessible_across; [exact ACCB| exact MU24| exact WE]
           | |- accessible _ pk _ => eapply accessible_across; [exact ACCP| exact MU24| exact WE]
           | |- stack0 _ _ _ => eapply (stack0_xpres H); [apply (XPs Lr); intros b Hb; exact Hb| exact SK0| apply Forall_nil]
           | |- as_RFS _ _ _ => eapply (RFS_via_xpres H HH); [exact RFS| apply (XPs Lr); intros b Hb; exact Hb| apply Forall_nil]
           | |- xpres H LB _ _ m0 _ => eapply (xpres_trans H); [exact XP0|]; eapply (xpres_weaken H); [apply (XPs LB SUBLR)| clear - SPR; lia| intros b Hb; exact Hb| intros q Hq; destruct Hq]
           | |- 0 <= _ <= DECEXTS_CF _ => clear - UF UF0; lia
           | |- as_MPRES _ _ _ => exact MPc4
           | |- ?G => idtac "FTN" G
           end.
      all: fail "FTN". }
    (* [comment removed for export] *)
    destruct XT as (PP & SO & LEN & F2). destruct XSH as ((SKSH & T1 & T2) & F2SH). rewrite blocks_EXTS_some in PB. set (EB := EBof K es) in *.
    pose proof SO as (_ & _ & KIN & KNC & KCAP2 & _ & _ & KDAT). unfold sk_num in KNC.
    assert (KNB : In (sk_id K, P, SK_SIZE) NB) by (eapply Permutation_in; [exact PB| apply in_or_app; left; left; reflexivity]).
    assert (KIR : In (sk_id K, P, SK_SIZE) Lr) by (apply SUBNR; apply in_or_app; left; exact KNB).
    pose proof (ah_blocks H HH _ _ _ _ HP KIR) as (KB1 & KB2 & KB3 & KB4 & KB5 & KB6 & KB7). cbn [blk_addr blk_size fst snd] in KB1, KB2, KB3, KB4, KB5, KB6, KB7. unfold SK_SIZE in KB3, KB5, KB7.
    (* [comment removed for export] *)
    set (REST := blocks_ERRST E' ++ LE ++ LB) in *.
    assert (PL2 : Permutation Lr ((blocks_SK P K ++ EB) ++ REST)).
    { etransitivity; [exact PL|]. transitivity (NB ++ REST); [| apply Permutation_app_tail; apply Permutation_sym; exact PB].
      subst REST. rewrite (app_assoc (blocks_ERRST E') LE (NB ++ LB)), (app_assoc (blocks_ERRST E') LE LB). apply Permutation_app_swap_app. }
    pose proof (Permutation_NoDup (Permutation_map blk_id PL2) (ah_nodup H HH _ _ _ HP)) as ND2.
    assert (NDK : List.NoDup (map blk_id (blocks_SK P K ++ EB))) by (pose proof ND2 as NDa; rewrite map_app in NDa; apply NoDup_app_remove_r in NDa; exact NDa).
    assert (INF2 : forall b, In b ((blocks_SK P K ++ EB) ++ REST) -> In b Lr) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL2| exact Hb]).
    assert (SUBLR2 : forall b, In b LB -> In b (EB ++ REST)) by (intros b Hb; subst REST; apply in_or_app; right; do 2 (apply in_or_app; right); exact Hb).
    assert (NBE : forall b, In b (blocks_SK P K ++ EB) -> In b NB) by (intros b Hb; eapply Permutation_in; [exact PB| exact Hb]).
    assert (DBEL : sk_cap K = 0 \/ (In (sk_did K, sk_data K, 8 * sk_cap K) Lr /\ sk_data K + 8 * sk_cap K <= aceil /\ 4 <= sk_cap K /\ AIMG_TOP <= sk_data K)).
    { destruct KDAT as [[C0 _]|(C4 & _ & _ & DIN & _)]; [left; exact C0| right].
      pose proof (HB _ (SUBNR _ DIN)) as (_ & W4 & W5 & _). cbn [blk_addr blk_size fst snd] in W4, W5. split; [exact (SUBNR _ DIN)|]. split; [exact W5|]. split; [exact C4| exact W4]. }
    assert (SKB : SK_below P K lo).
    { split; [unfold SK_SIZE; clear - KB5 CEIL; lia|]. destruct DBEL as [C0|(DIN & DB & _)]; [left; exact C0| right; clear - DB CEIL; lia]. }
    assert (SKR : SK_ranges H P K).
    { split; [exact (ah_blocks H HH _ _ _ _ HP KIR)|]. intros NC. destruct DBEL as [C0|(DIN & _)]; [exfalso; exact (NC C0)|]. exact (ah_blocks H HH _ _ _ _ HP DIN). }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply (askset_thunks_spec H) with (lo := lo) (LB := NB ++ LB) (K := K); rewrite ?unsigned_lit by lia;
      [reflexivity| reflexivity| unfold ADX_THUNK_FREE; lia| exact SO| exact SKB| exact SKSH| exact SKR| exact AC| exact ST| exact CEIL| clear - LO8K; lia| exact MI]|].
    intros msF2 mo2 KREL2 MP2 (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m2 & VIS2 & MU2 & WM2 & MI2 & AC2 & ST2 & SO2).
    rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in MU2, ST2 by lia. unfold SK_SIZE in MU2. pose proof (ah_mpres_trans H HH _ _ _ MPc1 MP2) as MPc2.
    set (K3 := sk_with_thunk K O_SK_FREETH ADX_THUNK_FREE) in *.
    (* [comment removed for export] *)
    assert (REMX : forall b, In b Lr -> blk_id b <> sk_id K -> In b (as_lb_remove H (sk_id K) Lr)).
    { intros b Hb NE. apply (proj2 (proj2 (proj2 (alb_remove_exact H HH _ _ _ _ (ah_nodup H HH _ _ _ HP) KIR)) b)). split; [exact Hb| exact NE]. }
    assert (SUB2 : forall b, In b (EB ++ REST) -> In b (as_lb_remove H (sk_id K) Lr)).
    { intros b Hb. apply REMX; [apply INF2; rewrite <- app_assoc; apply in_or_app; right; exact Hb|].
      intros EQ. pose proof ND2 as NDb. rewrite <- app_assoc in NDb. exact (nodup_ids_app_ne _ _ _ _ NDb ltac:(left; reflexivity) Hb (eq_sym EQ)). }
    assert (XPh : xpres H (as_lb_remove H (sk_id K) Lr) (bv_unsigned sp + -144) [] m m2).
    { eapply (xpres_of_munch_listed H HH); [exact HP| exact KIR| clear - CEIL LO8K; lia| exact MU2| exact WM2|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; unfold SK_SIZE; lia| apply Forall_nil]. }
    assert (XPs : forall L, (forall b, In b L -> In b (EB ++ REST)) -> xpres H L (bv_unsigned sp + -144) [] m m2).
    { intros L SUBL. eapply (xpres_weaken H); [exact XPh| apply Z.le_refl| intros b Hb; apply SUB2; apply SUBL; exact Hb| intros q Hq; exact Hq]. }
    assert (CW2 : Forall (aclient_write_ok H Lr) [(lo, bv_unsigned sp + -144); (P, P + 56)]).
    { apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right; left. exists (sk_id K, P, SK_SIZE). split; [exact KIR| cbn; unfold SK_SIZE; lia]. }
    assert (WE2 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp + -144); (P, P + 56)]).
    { apply Forall_cons; [exact (Forall_inv WE)|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. pose proof (aapp_not_shadowland _ _ KB7). lia. }
    assert (HP2 : as_RHEAP H s' Lr m2) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU2| exact WM2| exact CW2]).
    assert (HP2' : as_RHEAP H s' ((blocks_SK P K ++ EB) ++ REST) m2) by (eapply (HHx_rheap_perm H HHx); [exact HP2| exact PL2]).
    assert (AUX2 : as_rauxv_ok H m2 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU2| exact WM2| exact CW2]).
    assert (ERR2 : rw_cells asegs m2 (errno_addr tp) [C4 errv']).
    { rewrite TP in ERR |- *. eapply rw_cells_transport; [exact ERR| exact MU2| exact WM2|]. rewrite unsigned_lit by (unfold ATP; lia). cbn. unfold ATP, AIMG_TOP in *. clear - CEIL ACEILB KB4. lia. }
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -144) (adx_frame j0 pk ee s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply rw_cells_transport; [exact FR| exact MU2| exact WM2|]. cbn. clear - KB5 CEIL LO8K. lia. }
    assert (GE2 : GOT_echfree m2) by (eapply GOT_echfree_across; [exact MU2| exact WM2| unfold A_got_ossl_echext_free; cbn; unfold AIMG_TOP in KB4; clear - CEIL ACEILB KB4; lia| exact G2]).
    assert (IM2 : IMPL_mem m2) by (eapply IMPL_across; [exact MU2| exact WM2| unfold A_malloc_impl; cbn; unfold AIMG_TOP in KB4; clear - CEIL ACEILB KB4; lia| exact IM]).
    assert (GM2 : GOT_mem m2) by (eapply GOT_across; [exact MU2| exact WM2| unfold A_got_CRYPTO_malloc; cbn; unfold AIMG_TOP in KB4; clear - CEIL ACEILB KB4; lia| exact G1]).
    assert (EKNE : blk_id (sk_id K, P, SK_SIZE) <> en_id E).
    { cbn [blk_id fst snd]. intros EQ. exact (NBNE _ _ KNB ltac:(subst REST; do 2 (apply in_or_app; right); exact EIN0) EQ). }
    pose proof (DJE _ KIR EKNE) as DJK. cbn [blk_addr blk_size fst snd] in DJK. unfold SK_SIZE in DJK.
    assert (EC2 : rw_cells asegs m2 ee (entry_cells (EW P (Some (K, es))) pad1 pad2 pad3 pad4)).
    { eapply rw_cells_transport; [exact EC| exact MU2| exact WM2|]. unfold entry_cells. cbn [cells_size csize Nat.add length]. cbn. clear - DJK EH CEIL LO8K. lia. }
    assert (ESH2 : ENTRY_shad m2 ee (EW 0 None)).
    { eapply (ENTRY_shad_frame_law H _ m m2); [exact ESH0| intros b Hb; exact Hb| apply (XPs _); intros b Hb; rewrite blocks_EW_none in Hb; apply SUBLR2; exact (blocks_E_LB _ Hb)|].
      intros b Hb. rewrite blocks_EW_none in Hb. pose proof (HB _ (SUBLR _ (blocks_E_LB _ Hb))) as (_ & _ & K5 & _). clear - K5 CEIL LO8K. lia. }
    assert (PBIN_NE : blk_id (pbin, base, len) <> sk_id K).
    { cbn [blk_id fst snd]. intros EQ. exact (NBNE _ _ KNB ltac:(subst REST; do 2 (apply in_or_app; right); exact BIN) (eq_sym EQ)). }
    pose proof (ah_disj H HH _ _ _ _ _ HP (SUBLR _ BIN) KIR PBIN_NE) as DJB. cbn [blk_addr blk_size fst snd] in DJB. unfold SK_SIZE in DJB.
    assert (PK2 : rw_cells asegs m2 pk (pk_cells cur base rem)) by (eapply rw_cells_transport; [exact PK| exact MU2| exact WM2| cbn; clear - SPK KB5 CEIL LO8K; lia]).
    assert (BS2 : bytes_at asegs m2 base bs).
    { eapply bytes_at_transport; [exact BS| exact MU2|]. cbn. pose proof (HB _ (SUBLR _ BIN)) as (_ & _ & Kb5 & _). cbn [blk_addr blk_size fst snd] in Kb5. clear - DJB BSL' Kb5 CEIL LO8K. lia. }
    assert (ACCB2 : accessible m2 base len) by (eapply accessible_across; [exact ACCB| exact MU2| exact WE2]).
    assert (ACCP2 : accessible m2 pk 24) by (eapply accessible_across; [exact ACCP| exact MU2| exact WE2]).
    assert (SK02 : stack0 m2 lo (bv_unsigned sp)) by (eapply (stack0_xpres H); [apply (XPs LB SUBLR2)| exact SK0| apply Forall_nil]).
    assert (RFS2 : as_RFS H LF m2) by (eapply (RFS_via_xpres H HH); [exact RFS| apply (XPs LB SUBLR2)| apply Forall_nil]).
    assert (XP02 : xpres H LB (bv_unsigned sp) (XS ++ X0) m0 m2).
    { eapply (xpres_trans H); [exact XP0|]. eapply (xpres_weaken H); [apply (XPs LB SUBLR2)| clear - SPR; lia| intros b Hb; exact Hb| intros q Hq; destruct Hq]. }
    assert (SO2' : SKobj ((blocks_SK P K ++ EB) ++ REST) m2 P K3).
    { eapply SKobj_relist; [exact SO2|]. subst K3. rewrite e_blocks_SK_with_thunk. intros b Hb. apply in_or_app; left. apply in_or_app; left. exact Hb. }
    assert (BELB : forall b, In b EB -> blk_addr b + blk_size b <= bv_unsigned sp + -144).
    { intros b Hb. pose proof (HB _ (SUBNR _ ltac:(apply in_or_app; left; apply NBE; apply in_or_app; right; exact Hb))) as (_ & _ & K5 & _). clear - K5 CEIL LO8K. lia. }
    assert (F22 : Forall2 (fun p X => EXTobj ((blocks_SK P K ++ EB) ++ REST) m2 p X) (sk_elems K) es).
    { eapply (EXTs_frame H (NB ++ LB) (EB ++ REST) _ (bv_unsigned sp + -144) m m2); [exact F2| intros b Hb; apply in_or_app; left; exact Hb| intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb| apply (XPs _); intros b Hb; exact Hb| exact BELB]. }
    assert (F2SH2 : Forall2 (fun p X => EXT_shad m2 p X) (sk_elems K) es).
    { eapply (EXTs_shad_frame H (EB ++ REST) (bv_unsigned sp + -144) m m2); [exact F2SH| intros b Hb; apply in_or_app; left; exact Hb| apply (XPs _); intros b Hb; exact Hb| exact BELB]. }
    assert (SKSH2 : SK_shad m2 P K3).
    { subst K3. unfold SK_shad. rewrite ?e_sk_cap_with_thunk, ?e_sk_data_with_thunk. destruct SKSH as [SKH SKD]. split.
      - eapply addressable_acrossW; [exact SKH| exact MU2| exact WM2| unfold AAPP_HI; clear - KB1 KB5 ACEILB; lia| exact T1| exact WE2].
      - intros NC. destruct DBEL as [C0|(DIN & DB & C4 & D4)]; [exfalso; exact (NC C0)|].
        eapply (addressable_xpres_blk H); [| exact (T2 NC)| exact (SKD NC)| exact XPh].
        apply REMX; [exact DIN|]. cbn [blk_id fst snd]. intros EQ.
        assert (NDS : List.NoDup (map blk_id (blocks_SK P K))) by (pose proof NDK as NDa; rewrite map_app in NDa; apply NoDup_app_remove_r in NDa; exact NDa).
        unfold blocks_SK in NDS. replace (sk_cap K =? 0) with false in NDS by (symmetry; apply Z.eqb_neq; exact NC).
        cbn [map blk_id fst snd] in NDS. inversion NDS as [|i1 l1 NI1 _]; subst. apply NI1. left. exact EQ. }
    assert (CH2 : as_chain H m2 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (chain_at (XS ++ X0)); [exact XP02| eapply X0XR_chain; [exact HP2| exact RFS2| exact FXS| exact EIN| exact HES]| exact FR2]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply adx_segF3; [exact GE2| lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 VIS3. pose proof (ah_mpres_trans H HH _ _ _ MPc2 MP3) as MPc3.
    pose proof (apopfree_exts_spec H HH) as PFX. unfold popfree_exts_stmt, skpopfree_stmt_gen in PFX.
    specialize (PFX (aextfree_spec H HH) (EXTobj_frame_law H) EXTobj_owned_law (GOT_echfree_frame H) (EXT_shad_frame_law H) (ext_cost_pos H HH)
                    ltac:(unfold P_ossl_echext_free; lia) ltac:(reflexivity)).
    pose proof (exts_cost_bytes _ _ _ _ F22) as [ECBq EB0q].
    assert (EB0 : 0 <= lb_bytes EB) by exact EB0q. assert (ECB : ecost_sum extrep (ext_cost H) es <= as_Cf H (lb_bytes EB)) by exact ECBq. clear ECBq EB0q.
    cbn [xs_len] in UF. assert (UFB : uf + lb_bytes EB + 8 * sk_cap K + 56 <= DECEXTS_CF rem0) by exact (fail_cf_bound _ _ _ _ _ XI HC UF EB0).
    assert (CAP0 : 0 <= 8 * sk_cap K) by (clear - KNC; lia).
    assert (N1 : 0 <= lb_bytes EB + 8 * sk_cap K) by (clear - EB0 CAP0; lia). assert (N56 : 0 <= 56) by (clear; lia).
    assert (N2 : 0 <= lb_bytes EB + 8 * sk_cap K + 56) by (clear - EB0 CAP0; lia). assert (UFp : 0 <= uf) by (clear - UF; lia).
    pose proof (aCf_super H HH _ _ EB0 CAP0) as SA1. pose proof (aCf_super H HH _ _ N1 N56) as SA2. pose proof (aCf_super H HH _ _ UFp N2) as SA3.
    assert (N3 : 0 <= uf + (lb_bytes EB + 8 * sk_cap K + 56) <= DECEXTS_CF rem0) by (clear - UF UFB EB0 CAP0; lia).
    pose proof (aCf_mono H HH _ _ N3) as SM.
    assert (ALX : ecost_sum extrep (ext_cost H) es + as_Cf H (8 * sk_cap K) + as_Cf H 56 <= as_AL H s').
    { unfold DECEXTS_COST in HAL0. pose proof (aCf_pos H HH uf ltac:(clear - UF; lia)). clear - HAL HAL0 ECB SA1 SA2 SA3 SM H0. lia. }
    eapply (ah_seq H HH).
    { eapply PFX with (a := P) (K := K3) (xs := es) (lo := lo) (B := B) (LB := (blocks_SK P K ++ EB) ++ REST) (s := s') (errv := errv') (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        subst K3; rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk, ?e_sk_free_thunk_set, ?e_sk_cap_with_thunk; [exact VIS3| reflexivity| reflexivity| ..]; rewrite ?unsigned_lit by (unfold ADX_R10; lia).
      all: try first [exact SO2'| exact LEN| exact F22| exact F2SH2| exact NDK| exact HP2'| exact KREL3| exact AUX2| exact ST2| exact CEIL| exact ERR2| exact MI2| exact TP| exact AC2| exact CH2| exact IM2| exact GM2| exact GE2| exact SKSH2].
      all: lazymatch goal with
           | |- is_sk_freefunc_thunk _ => unfold is_sk_freefunc_thunk, ADX_THUNK_FREE, P_sk_OSSL_ECHEXT_freefunc_thunk; left; reflexivity
           | |- _ <= B => clear - SPB SPR; lia
           | |- _ <= _ - SKPOPFREE_STACK _ => unfold SKPOPFREE_STACK, EXTFREE_STACK, FR_ossl_echext_free, FR_sk_pop_free, CFREE_STACK, AFREE_STACK; clear - LO8K; lia
           | |- _ mod 16 = 0 => clear - SPA SPR; replace (bv_unsigned sp + -144) with (bv_unsigned sp - 9 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
           | |- _ mod 2 = 0 => reflexivity
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - SPR; lia| specialize (CHS _ _ Hin); clear - CHS; lia]
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF|]; unfold PF_decexts, pf_raise; intros y Hy; do 5 (apply in_app_iff; right); apply in_app_iff; right; apply in_app_iff; left; exact Hy
           | |- _ <= as_AL _ _ => unfold SK_SIZE; exact ALX
           | |- ?G => idtac "PFPRE" G
           end.
      all: fail "PFPRE". }
    clear PFX. intros [ms4 mo4] PO. unfold skpopfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m4 & st4 & LB4 &
                    VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & PERM4 & HP4 & XP4 & IM4 & GM4 & GG4 & AL4).
    subst K3. rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk in PERM4. fold EB in PERM4. rewrite ?e_sk_cap_with_thunk in AL4.
    rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in ST4, XP4 by lia. pose proof (ah_mpres_trans H HH _ _ _ MPc3 MP4) as MPc4.
    assert (PL4 : Permutation LB4 REST) by (apply (Permutation_app_inv_l (blocks_SK P K ++ EB)); rewrite <- (app_assoc (blocks_SK P K) EB LB4); exact PERM4).
    assert (SUB4 : forall b, In b REST -> In b LB4) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL4| exact Hb]).
    assert (XP24 : forall L, (forall b, In b L -> In b REST) -> xpres H L (bv_unsigned sp + -144) [] m2 m4).
    { intros L SUBL. eapply (xpres_weaken H); [exact XP4| apply Z.le_refl| intros b Hb; apply SUB4; apply SUBL; exact Hb| intros q Hq; exact Hq]. }
    assert (SUBLR4 : forall b, In b LB -> In b REST) by (intros b Hb; subst REST; do 2 (apply in_or_app; right); exact Hb).
    assert (XP14 : xpres H LB (bv_unsigned sp + -144) [] m m4) by (eapply (xpres_trans H); [apply (XPs LB SUBLR2)| apply (XP24 LB SUBLR4)]).
    eapply (dx_fail_end m4 st4 errv' P (Some (K, es)) cur rem LB4 LE c0 E' pad1 pad2 pad3 pad4 XS (uf + (lb_bytes EB + 8 * sk_cap K + 56)) ms4 mo4); try eassumption.
    all: cbv delta [spq]; lazymatch goal with
         | |- Permutation _ (blocks_ERRST _ ++ _ ++ LB) => subst REST; exact PL4
         | |- LIBMID _ _ _ => eapply (LIBMID_xpres0 H); [| reflexivity| apply (XP24 REST); intros b Hb; exact Hb| | cbn [mid_errblocks mid_E]; intros b Hb; subst REST; apply in_or_app; left; exact Hb];
                               [ eapply (LIBMID_xpres0 H); [exact LM| reflexivity| apply (XPs (EB ++ REST)); intros b Hb; exact Hb| | cbn [mid_errblocks mid_E]; intros b Hb; subst REST; apply in_or_app; right; apply in_or_app; left; exact Hb];
                                 intros b Hb; subst REST; apply in_or_app; right; apply in_or_app; right; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply LIBSUB; exact Hb]
                               | intros b Hb; subst REST; apply in_or_app; right; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply LIBSUB; exact Hb] ]
         | |- rw_cells _ _ (bv_unsigned sp + -144) _ => eapply (xpres_rw_cells' H); [exact XP4| exact FR2| left; lia| apply Forall_nil]
         | |- rw_cells _ _ (errno_addr _) _ => exact ERR4
         | |- rw_cells _ _ ee _ => eapply (xpres_rw_cells' H); [apply (XP24 LB SUBLR4)| exact EC2| | apply Forall_nil]; right; right; left; exists (en_id E, ee, ENTRY_SIZE); split; [exact EIN0| unfold entry_cells; cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]; unfold ENTRY_SIZE; lia]
         | |- ENTRY_shad _ _ _ => eapply (ENTRY_shad_frame_law H _ m2 m4); [exact ESH2| intros b Hb; exact Hb| apply (XP24 _); intros b Hb; rewrite blocks_EW_none in Hb; apply SUBLR4; exact (blocks_E_LB _ Hb)|];
                                    intros b Hb; rewrite blocks_EW_none in Hb; pose proof (HB _ (SUBLR _ (blocks_E_LB _ Hb))) as (_ & _ & K5 & _); clear - K5 CEIL LO8K; lia
         | |- rw_cells _ _ pk _ => eapply (xpres_rw_cells' H); [exact XP4| exact PK2| left; clear - SPK; lia| apply Forall_nil]
         | |- pk_in _ _ _ _ => exact PIN
         | |- bytes_at _ _ base _ => eapply (xpres_bytes_at' H); [apply (XP24 LB SUBLR4)| exact BS2| | apply Forall_nil]; right; right; left; exists (pbin, base, len); split; [exact BIN| cbn [blk_addr blk_size fst snd]; clear - BSL'; lia]
         | |- accessible _ base _ => eapply (accessible_xpresX s' Lr m2 LB m2 m4 (bv_unsigned sp + -144) []); [exact HP2| exact SUBLR| clear - CEIL LO8K; lia| | exact ACCB2| apply (XP24 LB SUBLR4)| apply Forall_nil]; left; exists (pbin, base, len); split; [exact BIN| cbn [blk_addr blk_size fst snd]; lia]
         | |- accessible _ pk _ => eapply (accessible_xpresX s' Lr m2 LB m2 m4 (bv_unsigned sp + -144) []); [exact HP2| exact SUBLR| clear - CEIL LO8K; lia| right; right; clear - SPK; lia| exact ACCP2| apply (XP24 LB SUBLR4)| apply Forall_nil]
         | |- stack0 _ _ _ => eapply (stack0_xpres H); [apply (XP24 LB SUBLR4)| exact SK02| apply Forall_nil]
         | |- as_RFS _ _ _ => eapply (RFS_via_xpres H HH); [exact RFS2| apply (XP24 LB SUBLR4)| apply Forall_nil]
         | |- xpres H LB _ _ m0 _ => eapply (xpres_trans H); [exact XP02|]; eapply (xpres_weaken H); [apply (XP24 LB SUBLR4)| clear - SPR; lia| intros b Hb; exact Hb| intros q Hq; destruct Hq]
         | |- 0 <= _ <= DECEXTS_CF _ => clear - UF UFB EB0 CAP0; lia
         | |- as_AL _ _ + _ + _ + _ >= _ => clear - HAL AL4 ECB SA1 SA2 SA3; unfold SK_SIZE in AL4; lia
         | |- as_MPRES _ _ _ => exact MPc4
         | |- ?G => idtac "FT2" G
         end.
    all: fail "FT2".
  Qed.

  (* [comment removed for export] *)
  Lemma SKobj_frameX : forall L0 SP X m m' a K,
    SKobj L0 m a K -> xpres H L0 SP X m m' -> avoids X a SK_SIZE -> (sk_cap K <> 0 -> avoids X (sk_data K) (8 * sk_cap K)) -> SKobj L0 m' a K.
  Proof.
    clear. intros L0 SP X m m' a K SO XP AVH AVD.
    destruct SO as ((pad & PL & HDR) & POS & HIN & NC & CAP & SRT & EL & DAT).
    unfold SKobj. split.
    { exists pad. split; [exact PL|]. eapply (xpres_rw_cells' H); [exact XP| exact HDR| |].
      - right; right; left. exists (sk_id K, a, SK_SIZE). split; [exact HIN|]. unfold sk_hdr_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold SK_SIZE. lia.
      - unfold sk_hdr_cells. cbn [cells_size csize Nat.add]. exact AVH. }
    split; [exact POS|]. split; [exact HIN|]. split; [exact NC|]. split; [exact CAP|]. split; [exact SRT|]. split; [exact EL|].
    destruct DAT as [D0|(D1 & D2 & D3 & D4 & AR & junk & JK)]; [left; exact D0| right].
    pose proof (u64arr_bound _ _ _ _ AR) as ARB. rewrite length_map in ARB. unfold sk_num, zlength in NC.
    assert (AVD' : avoids X (sk_data K) (8 * sk_cap K)) by (apply AVD; lia).
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split.
    - eapply (xpres_u64arr H); [exact XP| exact AR|]. split.
      + right; right; left. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [exact D4|]. cbn [blk_addr blk_size fst snd]. rewrite ?length_map. lia.
      + rewrite length_map. eapply avoids_sub; [exact AVD'| lia| lia].
    - exists junk. eapply (xpres_rw_cells' H); [exact XP| exact JK| |].
      + right; right; left. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [exact D4|]. cbn [blk_addr blk_size fst snd cells_size csize]. unfold sk_num, zlength. rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
      + cbn [cells_size csize]. unfold sk_num, zlength. rewrite Nat.add_0_r, Z2Nat.id by lia. eapply avoids_sub; [exact AVD'| lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dx_stack_raise : lo <= spq - RAISE_STACK (mid_err M).
  Proof.
    cbv delta [spq]. clear - LO. unfold DECEXTS_STACK, FR_ech_decode_echconfig_exts in LO.
    pose proof (Z.le_max_l (RAISE_STACK (mid_err M)) (Z.max SKPUSH_STACK (SKPOPFREE_STACK EXTFREE_STACK))). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_fail : forall m s' errv' P xs NB c cur rem line msF mo' (t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 x5 x6 x7 t3 t4 t5 t6 : word),
    dworldX m s' errv' P xs NB c cur rem [] -> (line = 206 \/ line = 210) ->
    as_AKREL H s' (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s' msF
      = MS (mkR (Z_to_bv 64 ADX_RA1) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 2)
                (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                (Z_to_bv 64 line) x5 x6 (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (ee + 56) 3)) x7 t3 t4 t5 t6)
           F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs) ->
    as_SR H (decexts_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LIB LB LF M ee pk base len cur0 rem0 E bs lo B m0 mo) (mkCfg msF mo').
  Proof.
    intros m s' errv' P xs NB c cur rem line msF mo' t0 t1 t2 x1 a0 a1 a2 a3 a4 a5 x5 x6 x7 t3 t4 t5 t6 FW LN KREL MP VIS.
    pose proof FW as (MI & AC & ST & FR & ERR & AUX & HP & LM & EO & ESH & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & ACCB & ACCP & SK0 & RFS & XP0 & ALG).
    pose proof (dworldX_chain _ _ _ _ _ _ _ _ _ _ FW) as CH0.
    pose proof dx_stack_raise as LOR. cbv delta [spq] in *. acb. pose proof (aword_range sp) as SPR. cbn [app] in HP.
    pose proof PIN as PIN'. unfold pk_in in PIN'. pose proof BSL as BSL'. unfold zlength in BSL'.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & ESHD & EBL). rewrite MF0 in MF. rewrite CX in CP, EPm. cbn [ERRPH_mid] in EPm.
    assert (SUBL : forall b, In b LIB -> In b (NB ++ LB)) by (intros b Hb; apply in_or_app; right; apply LIBSUB; exact Hb).
    assert (SUBH : forall b, In b (NB ++ LB) -> In b (mid_errblocks M ++ NB ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (HB : forall b, In b (mid_errblocks M ++ NB ++ LB) -> 0 < blk_addr b /\ AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). repeat split; assumption. }
    (* [comment removed for export] *)
    assert (NBB : lb_bytes NB <= 88 + 8 * c /\ 5 * Z.of_nat (length NB) <= 2 * c + 10 /\ 4 * xs_len xs <= c /\ xs_base xs <= 56).
    { revert PB XI. unfold XINV. destruct xs as [[K es]|]; intros PB XI; cbn [xs_len xs_base].
      - destruct XI as (KC & K4 & [C0 C5] & E5 & EBY). rewrite blocks_EXTS_some in PB.
        pose proof (blocks_SK_facts P K C0) as (SKB & SKL & _ & _).
        rewrite <- (lb_bytes_perm _ _ PB), <- (Permutation_length PB), lb_bytes_app, length_app, Nat2Z.inj_add.
        unfold SK_SIZE in SKB |- *. unfold zlength in *. clear - K4 C0 C5 E5 EBY SKB SKL. lia.
      - destruct XI as [_ C0]. pose proof (Permutation_nil PB) as ->. cbn. unfold SK_SIZE. clear - C0. lia. }
    destruct NBB as (NBB & NBL & XL4 & XB56). unfold zlength in *.
    (* [comment removed for export] *)
    destruct ALG as (um & uf & U1 & U2 & U3). cbn [lb_bytes fold_right] in U1. rewrite Z.add_0_r in U1.
    assert (UMB : 0 <= um <= DECEXTS_CM rem0) by (unfold DECEXTS_CM, ADX_PER_EXT, ADX_PUSH_CM in *; clear - U1 XL4 XB56 CB1 CB2 PIN'; lia).
    pose proof (aCm_mono H HH _ _ UMB) as CMM.
    assert (UFB0 : 0 <= uf <= DECEXTS_CF rem0) by (unfold DECEXTS_CF, ADX_PUSH_CF in *; clear - U2 XL4 CB1 CB2 PIN'; lia).
    pose proof (aCf_mono H HH _ _ UFB0) as CFM.
    assert (HALR : RAISE_COST H (mid_err M) <= as_AL H s') by (unfold DECEXTS_COST in HAL0; clear - HAL0 U3 CMM CFM; lia).
    eapply RAISE with (lo := lo) (B := B) (LB := NB ++ LB) (s := s') (ph := mid_err M) (E := mid_E M) (x := x) (errv := errv') (LF := LF)
      (CH := (bv_unsigned sp, bv_unsigned ra) :: CH)
      (file := ADX_FILE_ECHS) (fs := S_ADX_FILE) (fsl := K_ADX_FILE) (func := ADX_FUNC) (gs := S_ADX_FUNC) (gsl := K_ADX_FUNC)
      (line := line) (lib := ADX_ERR_LIB_SSL) (reason := ADX_REASON) (ra2 := ADX_RA2) (ra3 := ADX_RA3);
      [exact VIS| ..]; try (rewrite unsigned_lit by lia).
    all: lazymatch goal with
         | |- as_RHEAP _ _ _ _ => exact HP
         | |- as_AKREL _ _ _ => exact KREL
         | |- lb_bytes _ + _ <= _ => unfold raise_bytes; rewrite !lb_bytes_app in *; unfold DECEXTS_BYTES, ERRDEBUG_BYTES in *; change (mid_errblocks M) with (blocks_ERRST (mid_E M)) in BY;
                                      pose proof (errph_nonneg (mid_err M)) as [EB0 _]; clear - BY EB0 NBB CB1 CB2 PIN' REM1; lia
         | |- Z.of_nat (length _) + _ <= _ => unfold raise_cnt; rewrite !length_app, !Nat2Z.inj_add in *; change (mid_errblocks M) with (blocks_ERRST (mid_E M)) in CN;
                                               pose proof (errph_nonneg (mid_err M)) as [_ EC0]; clear - CN EC0 NBL CB2 PIN' Q5; lia
         | |- as_rauxv_ok _ _ _ => exact AUX
         | |- _ <= B => clear - SPB SPR; lia
         | |- _ mod 16 = 0 => clear - SPA SPR; replace (bv_unsigned sp + -144) with (bv_unsigned sp - 9 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
         | |- stk _ _ _ _ => exact ST
         | |- aceil <= lo => exact CEIL
         | |- _ <= _ - RAISE_STACK _ => exact LOR
         | |- errph_sh0 _ _ _ _ => eapply (errph_sh0_sub (mid_err M) _ lo sp); [unfold errph_sh0; destruct (mid_err M); [exact SK0| exact I]
                                   | rewrite ?unsigned_lit by lia; assert (RS0 : 0 <= RAISE_STACK (mid_err M)) by (destruct (mid_err M) as [|cq]; vm_compute; discriminate);
                                      clear - LOR RS0 SPR; lia
                                    | rewrite ?unsigned_lit by lia; clear - SPA SPR; Z.div_mod_to_equations; lia]
         | |- rw_cells _ _ (errno_addr _) _ => exact ERR
         | |- mem_inv _ _ => exact MI
         | |- tp = _ => exact TP
         | |- ACONST _ => exact AC
         | |- MEMFLAG _ _ => exact MF
         | |- IMPL_mem _ => exact IM
         | |- GOT_mem _ => exact G1
         | |- arelro_lib _ => exact RL
         | |- ERRPH _ _ _ => eapply ERRPH_mono; [exact EPm| exact SUBL]
         | |- ERRX _ _ _ => exact EX
         | |- errph_below _ _ => exact EBL
         | |- errph_shad _ _ => exact ESHD
         | |- CTXPH _ _ _ => exact (CTXPH_mono _ _ SUBL _ _ CP)
         | |- as_RFS _ _ _ => exact RFS
         | |- (_ <= AFS_MAXLIVE)%nat => exact LFB
         | |- as_chain _ _ _ _ => exact CH0
         | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - SPR; lia| specialize (CHS _ _ Hin); clear - CHS; lia]
         | |- pf_ok _ (PF_errnew _) _ _ => eapply pf_ok_call; [exact PF|]; unfold PF_decexts, pf_raise, ADX_RA1; intros y Hy; do 5 (apply in_app_iff; right); apply in_app_iff; left; apply in_app_iff; left; exact Hy
         | |- pf_ok _ PF_errdebug _ _ => eapply pf_ok_call; [exact PF|]; unfold PF_decexts, pf_raise, ADX_RA2; intros y Hy; do 5 (apply in_app_iff; right); apply in_app_iff; left; apply in_app_iff; right; apply in_app_iff; left; exact Hy
         | |- pf_ok _ PF_errseterr _ _ => eapply pf_ok_call; [exact PF|]; unfold PF_decexts, pf_raise, ADX_RA3; intros y Hy; do 5 (apply in_app_iff; right); apply in_app_iff; left; apply in_app_iff; right; apply in_app_iff; right; exact Hy
         | |- errph_closed_ok _ _ => exact CLOSED
         | |- RAISE_COST _ _ <= _ => exact HALR
         | |- AROSTR ADX_FILE_ECHS _ _ => exact AR_ADX_FILE
         | |- AROSTR ADX_FUNC _ _ => exact AR_ADX_FUNC
         | |- _ <> [] => discriminate
         | |- Z.of_nat (length S_ADX_FILE) < 24 => rewrite S_ADX_FILE_len; lia
         | |- Z.of_nat (length S_ADX_FUNC) < 32 => rewrite S_ADX_FUNC_len; lia
         | |- 0 < ADX_FILE_ECHS => unfold ADX_FILE_ECHS; lia
         | |- 0 < ADX_FUNC => unfold ADX_FUNC; lia
         | |- 0 <= _ < 2 ^ 31 => clear - LN; lia
         | |- 0 < ADX_ERR_LIB_SSL < 256 => unfold ADX_ERR_LIB_SSL; lia
         | |- ADX_ERR_LIB_SSL <> 2 => unfold ADX_ERR_LIB_SSL; lia
         | |- 0 < ADX_REASON < _ => unfold ADX_REASON; lia
         | |- 0 <= ADX_RA1 < _ => unfold ADX_RA1; lia
         | |- ADX_RA1 mod 2 = 0 => reflexivity
         | |- 0 <= ADX_RA2 < _ => unfold ADX_RA2; lia
         | |- ADX_RA2 mod 2 = 0 => reflexivity
         | |- 0 <= ADX_RA3 < _ => unfold ADX_RA3; lia
         | |- ADX_RA3 mod 2 = 0 => reflexivity
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_debug) _ _ _ _) _ =>
             intros; eapply adx_glue1; [clear - LN; lia| assumption]
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_error) _ _ _ _) _ =>
             intros; eapply adx_glue2; [unfold ADX_REASON; lia| assumption]
         | |- _ => idtac
         end.
    (* [comment removed for export] *)
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 msF' m' mo'' s'' errv'' LBN c0 p1 p2 A1 A2 en1 en2 E'
           VIS' KREL' MP' MI' AC' ST' AUX' HP' MF' IM' GM' RL' ERR' DL RSZ EP' CP' EXR' LSH' XS FXS XP' RFS' AL'.
    rewrite ?unsigned_lit in ST' by lia. rewrite ?unsigned_lit in XP' by lia.
    pose proof (ah_mpres_trans H HH _ _ _ MP MP') as MPc.
    set (L' := blocks_ERRST E' ++ LBN ++ NB ++ LB) in HP'.
    assert (SUBH' : forall b, In b (NB ++ LB) -> In b L') by (intros b Hb; subst L'; do 2 (apply in_or_app; right); exact Hb).
    (* [comment removed for export] *)
    assert (LM' : LIBMID (LBN ++ LIB) m' (mkMID 1 (CtxReady x) (ErrReady c0) E' (mid_vdso M))).
    { eapply (LIBMID_errcall H HH s' m s'' LIB (NB ++ LB) (bv_unsigned sp + -144) XS LF LBN m m' M x c0 E');
        [exact HP| exact SUBL| exact LM| exact CX| exact RFS| exact FXS| exact XP'| subst L'; exact HP'| exact CP'| exact EP'| exact DL| exact EXR'
        | apply errst_fits_raise; [exact FIT| exact RSZ]| exact LSH'| exact MF']. }
    pose proof (es_after _ _ _ _ LM' DL) as HES0.
    assert (HES' : forall c1, mid_err M = ErrReady c1 -> In (ec_es c1) L' /\ blk_size (ec_es c1) = ERRST_SIZE).
    { intros c1 PH. destruct (HES0 c1 PH) as (I1 & Z1 & _). split; [apply SUBH', SUBL; exact I1| exact Z1]. }
    (* [comment removed for export] *)
    pose proof (ah_nodup H HH _ _ _ HP) as ND. apply nd_tail in ND.
    assert (NNB : forall b, In b NB -> forall l, In l LIB -> blk_id l <> blk_id b).
    { intros b Hb l Hl EQ. exact (nodup_ids_app_ne _ _ _ _ ND Hb (LIBSUB _ Hl) (eq_sym EQ)). }
    assert (NLE : forall b, In b (blocks_ENTRY ee E) -> forall l, In l LIB -> blk_id l <> blk_id b) by (intros b Hb l Hl; exact (IDS _ _ Hl Hb)).
    (* [comment removed for export] *)
    assert (AVX : forall b, In b (NB ++ LB) -> (forall l, In l LIB -> blk_id l <> blk_id b) ->
                  avoids (XR XS) (blk_addr b) (blk_size b) /\ shavoids (XR XS) (blk_addr b) (blk_size b)).
    { intros b Hb NL. eapply (XR_block s'' L' m' LF m' XS b); [exact HP'| exact RFS'| exact FXS| apply SUBH'; exact Hb|].
      intros c1 Hc1. destruct (HES0 c1 Hc1) as (I1 & Z1 & _). split; [apply SUBH', SUBL; exact I1|]. split; [apply NL; exact I1| exact Z1]. }
    assert (SPQC : aceil <= bv_unsigned sp + -144) by (clear - CEIL LO8K; lia).
    assert (AVF : avoids (XR XS) (bv_unsigned sp + -144) 144) by (eapply (XR_stack LF m' XS); [exact RFS'| exact FXS| exact SPQC| exact EBL]).
    assert (AVP : avoids (XR XS) pk 24) by (eapply (XR_stack LF m' XS); [exact RFS'| exact FXS| clear - SPK SPQC; lia| exact EBL]).
    destruct (dworld_entry _ _ _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC & EEP & _ & _ & _ & PR & PKP & PKH & BP & BH & BAP & PKA).
    pose proof EO as (_ & _ & O1 & O2 & O3 & O4 & XT). cbn [EW en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o] in O1, O2, O3, O4, XT.
    pose proof ESH as (ETOP & EAD & ES1 & ES2 & ES3 & ES4 & XSH). cbn [EW en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o] in ES1, ES2, ES3, ES4, XSH.
    pose proof OF0 as (Q1 & Q2 & Q3 & Q4).
    pose proof (AVX _ ltac:(apply in_or_app; right; exact EIN0) (NLE _ ltac:(left; reflexivity))) as [AVE SAVE]. cbn [blk_addr blk_size fst snd] in AVE, SAVE.
    pose proof (AVX _ ltac:(apply in_or_app; right; exact BIN) (fun l Hl => IDB l Hl)) as [AVB SAVB]. cbn [blk_addr blk_size fst snd] in AVB, SAVB.
    pose proof (HB _ (SUBH _ ltac:(apply in_or_app; right; exact BIN))) as (PB1 & PB2' & _). cbn [blk_addr blk_size fst snd] in PB1, PB2'.
    pose proof (ah_blocks H HH _ _ _ _ HP (SUBH _ ltac:(apply in_or_app; right; exact BIN))) as (_ & PB16 & _). cbn [blk_addr blk_size fst snd] in PB16.
    (* [comment removed for export] *)
    assert (FR' : rw_cells asegs m' (bv_unsigned sp + -144) (adx_frame j0 pk ee s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' H); [exact XP'| exact FR| left; lia|]. unfold adx_frame. cbn [cells_size csize Nat.add length]. exact AVF. }
    assert (PK' : rw_cells asegs m' pk (pk_cells cur base rem)).
    { eapply (xpres_rw_cells' H); [exact XP'| exact PK| left; clear - SPK; lia|]. unfold pk_cells. cbn [cells_size csize Nat.add length]. exact AVP. }
    assert (EC' : rw_cells asegs m' ee (entry_cells (EW P xs) pad1 pad2 pad3 pad4)).
    { eapply (xpres_rw_cells' H); [exact XP'| exact EC| |].
      - right; right; left. exists (en_id E, ee, ENTRY_SIZE). split; [apply in_or_app; right; exact EIN0|]. unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold ENTRY_SIZE. lia.
      - unfold entry_cells. cbn [cells_size csize Nat.add length]. exact AVE. }
    assert (BS' : bytes_at asegs m' base bs).
    { eapply (xpres_bytes_at' H); [exact XP'| exact BS| |].
      - right; right; left. exists (pbin, base, len). split; [apply in_or_app; right; exact BIN|]. cbn [blk_addr blk_size fst snd]. clear - BSL'; lia.
      - eapply avoids_sub; [exact AVB| lia| clear - BSL'; lia]. }
    assert (ACCB' : accessible m' base len).
    { eapply (accessible_xpresX s'' L' m' (NB ++ LB) m m' (bv_unsigned sp + -144)); [exact HP'| exact SUBH'| exact SPQC| | exact ACCB| exact XP'|].
      - left. exists (pbin, base, len). split; [apply in_or_app; right; exact BIN| cbn [blk_addr blk_size fst snd]; lia].
      - apply shavoids_acc; [exact SAVB| clear - PB16; Z.div_mod_to_equations; lia| clear - PB1; lia]. }
    assert (ACCP' : accessible m' pk 24).
    { eapply (accessible_xpresX s'' L' m' (NB ++ LB) m m' (bv_unsigned sp + -144)); [exact HP'| exact SUBH'| exact SPQC| right; right; clear - SPK; lia| exact ACCP| exact XP'|].
      apply shavoids_acc; [| exact PK8| clear - SPK SPR; lia].
      eapply (XR_stack_sh s'' L' m' LF m' XS); [exact HP'| exact RFS'| exact FXS| clear - SPK SPQC; lia| lia| pose proof ACCP as (_ & QH & _); exact QH| exact HES']. }
    assert (SK0' : stack0 m' lo (bv_unsigned sp)).
    { eapply (stack0_xpres H); [exact XP'| exact SK0|]. eapply (XR_stack0 s'' L' m' LF m' XS); [exact HP'| exact RFS'| exact FXS| exact HES']. }
    assert (XP0' : xpres H LB (bv_unsigned sp) (XS ++ X0) m0 m').
    { pose proof XP' as XPq. rewrite (app_assoc XS ERR_XE (memflag_foot ++ errph_foot (mid_err M))) in XPq.
      pose proof (axpres_drop_memflag H (NB ++ LB) (bv_unsigned sp + -144) (XS ++ ERR_XE) (errph_foot (mid_err M)) m m' MF MF' XPq) as XPd.
      eapply (xpres_trans H).
      - eapply (xpres_weaken H); [exact XP0| apply Z.le_refl| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app; right; exact Hq].
      - eapply (xpres_weaken H); [exact XPd| clear - SPR; lia| intros b Hb; apply in_or_app; right; exact Hb|].
        intros q Hq. apply rin_ivs_app in Hq. apply rin_ivs_app. destruct Hq as [Hq|Hq].
        + apply rin_ivs_app in Hq. destruct Hq as [Hq|Hq]; [left; exact Hq|]. right. unfold X0. cbn [rin_ivs fst snd]. right; right. apply rin_ivs_app. left. exact Hq.
        + right. unfold X0. cbn [rin_ivs fst snd]. right; right. apply rin_ivs_app. right. exact Hq. }
    (* [comment removed for export] *)
    assert (NBX : forall b, In b NB -> In b (NB ++ LB) /\ avoids (XR XS) (blk_addr b) (blk_size b) /\ shavoids (XR XS) (blk_addr b) (blk_size b)).
    { intros b Hb. split; [apply in_or_app; left; exact Hb|]. apply AVX; [apply in_or_app; left; exact Hb| exact (NNB _ Hb)]. }
    assert (OSH' : forall Pf o, ofield LB Pf o -> (forall b, In b (blocks_of Pf o) -> In b (blocks_ENTRY ee E)) -> oshad m Pf o -> oshad m' Pf o).
    { intros Pf o OFo INE OSo. eapply oshad_xpresX; [| exact OSo| exact XP']. destruct o as [[i1 n1]|]; [| exact I]. cbn [ofield] in OFo. destruct OFo as (_ & _ & IN1).
      pose proof (AVX (i1, Pf, n1) ltac:(apply in_or_app; right; exact IN1) (NLE _ (INE _ ltac:(left; reflexivity)))) as [A1' S1']. cbn [blk_addr blk_size fst snd] in A1', S1'.
      split; [apply in_or_app; right; exact IN1|]. split; [exact A1'| exact S1']. }
    assert (EO' : ENTRYobj (NB ++ LB) m' ee (EW P xs)).
    { unfold ENTRYobj. cbn [EW en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o].
      split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact EC']|].
      split; [apply in_or_app; right; exact EIN0|]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|].
      revert XT PB. unfold EXTS. destruct xs as [[K es]|]; intros XT PB; [| exact XT].
      destruct XT as (PP & SO & LEN & F2). rewrite blocks_EXTS_some in PB.
      assert (NBK : forall b, In b (blocks_SK P K) -> In b NB) by (intros b Hb; eapply Permutation_in; [exact PB| apply in_or_app; left; exact Hb]).
      assert (NBE : forall b, In b (EBof K es) -> In b NB) by (intros b Hb; eapply Permutation_in; [exact PB| apply in_or_app; right; exact Hb]).
      split; [exact PP|]. split; [| split; [exact LEN|]].
      - eapply SKobj_frameX; [exact SO| exact XP'| |].
        + exact (proj1 (proj2 (NBX _ (NBK _ ltac:(left; reflexivity))))).
        + intros NC. exact (proj1 (proj2 (NBX _ (NBK _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NC); right; left; reflexivity))))).
      - eapply EXTs_frameX; [exact F2| exact XP'|]. intros b Hb. exact (proj1 (proj2 (NBX _ (NBE _ Hb)))). }
    assert (ESH' : ENTRY_shad m' ee (EW P xs)).
    { unfold ENTRY_shad. cbn [EW en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o].
      split; [exact ETOP|]. split; [eapply (addressable_xpres_blkX H); [apply in_or_app; right; exact EIN0| exact ETOP| exact EAD| exact XP'| exact SAVE]|].
      split; [apply (OSH' _ _ Q1); [intros b Hb; right; apply in_or_app; left; exact Hb| exact ES1]|].
      split; [apply (OSH' _ _ Q2); [intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb| exact ES2]|].
      split; [apply (OSH' _ _ Q3); [intros b Hb; right; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb| exact ES3]|].
      split; [apply (OSH' _ _ Q4); [intros b Hb; right; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb| exact ES4]|].
      revert XSH PB XT. unfold EXTS_shad, EXTS. destruct xs as [[K es]|]; intros XSH PB XT; [| exact I].
      destruct XSH as ((SKSH & T1 & T2) & F2SH). destruct XT as (PP & SO & LEN & F2). rewrite blocks_EXTS_some in PB.
      assert (NBK : forall b, In b (blocks_SK P K) -> In b NB) by (intros b Hb; eapply Permutation_in; [exact PB| apply in_or_app; left; exact Hb]).
      assert (NBE : forall b, In b (EBof K es) -> In b NB) by (intros b Hb; eapply Permutation_in; [exact PB| apply in_or_app; right; exact Hb]).
      split.
      - split; [| split; [exact T1| exact T2]]. destruct SKSH as [SKH SKD]. split.
        + eapply (addressable_xpres_blkX H); [exact (proj1 (NBX _ (NBK _ ltac:(left; reflexivity))))| exact T1| exact SKH| exact XP'| exact (proj2 (proj2 (NBX _ (NBK _ ltac:(left; reflexivity)))))].
        + intros NC. eapply (addressable_xpres_blkX H); [| exact (T2 NC)| exact (SKD NC)| exact XP'|].
          * exact (proj1 (NBX _ (NBK _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NC); right; left; reflexivity)))).
          * exact (proj2 (proj2 (NBX _ (NBK _ ltac:(unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NC); right; left; reflexivity))))).
      - eapply EXTs_shad_xpresX; [exact F2SH| exact XP'|]. intros b Hb. exact (NBX _ (NBE _ Hb)). }
    assert (HAL' : as_AL H s'' + as_Cm H (DECEXTS_CM rem0) + as_Cf H uf + RAISE_COST H (mid_err M) >= as_AL H s00) by (clear - U3 CMM AL'; lia).
    eapply (dx_fail_tail m' s'' errv'' P xs NB c cur rem L' LBN c0 E' XS uf msF' mo'');
      [exact MI'| exact AC'| exact ST'| exact FR'| exact ERR'| exact AUX'| exact HP'| subst L'; apply Permutation_refl| exact LM'| exact DL| exact EO'| exact ESH'| exact PB| exact XI
      | clear - CB1 CB2 PIN'; lia| exact PK'| exact PIN| exact CR| clear - CB1 CB2 PIN'; lia| exact BS'| exact ACCB'| exact ACCP'| exact SK0'| exact FXS| exact RFS'| exact XP0'
      | exact U2| exact HAL'| exact KREL'| exact MPc| exact VIS'].
  Qed.

  (* [comment removed for export] *)
  Lemma dx_main : forall (rax x1 a0 a1 a2 a3 a4 x6 x7 x8 x10 t0 t1 t2 t3 t4 t5 t6 : word) m1 errv msF mo',
    mem_inv asegs m1 -> ACONST m1 -> stk asegs m1 lo spq -> rw_cells asegs m1 spq (adx_frame j0 pk ee s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
    rw_cells asegs m1 (errno_addr tp) [C4 errv] -> as_rauxv_ok H m1 B ->
    as_RHEAP H s00 (mid_errblocks M ++ LB) m1 -> LIBMID LIB m1 M -> ENTRYobj LB m1 ee E -> ENTRY_shad m1 ee E ->
    rw_cells asegs m1 pk (pk_cells cur0 base rem0) -> bytes_at asegs m1 base bs -> accessible m1 base len -> accessible m1 pk 24 -> stack0 m1 lo (bv_unsigned sp) ->
    as_RFS H LF m1 -> xpres H LB (bv_unsigned sp) X0 m0 m1 ->
    as_AKREL H s00 (mkCfg msF mo') -> as_MPRES H mo mo' ->
    as_VIS H s00 msF
      = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp x1 a0 a1 a2 a3 a4 (Z_to_bv 64 (-2)) (Z_to_bv 64 1) (Z_to_bv 64 2)
                (Z_to_bv 64 pk) (Z_to_bv 64 (pk + 16)) (Z_to_bv 64 (Z.shiftr pk 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (pk + 16) 3 + ASHB))
                x6 x7 x8 (Z_to_bv 64 ASHB) x10 (Z_to_bv 64 (ee + 56)) t3 t4 t5 t6)
           F (Z_to_bv 64 ADX_LOOP) fc None m1 (seg_rom asegs) ->
    as_SR H (decexts_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s00 LIB LB LF M ee pk base len cur0 rem0 E bs lo B m0 mo) (mkCfg msF mo').
  Proof.
    intros rax x1 a0 a1 a2 a3 a4 x6 x7 x8 x10 t0 t1 t2 t3 t4 t5 t6 m1 errv msF mo' MI AC ST FR ERR AUX HP LM EO ESH PK BS ACCB ACCP SK0 RFS XP KREL MP VIS.
    assert (FW : dworld m1 s00 errv 0 None [] cur0 rem0).
    { unfold dworld, dworldX. cbn [app]. rewrite EW0. replace (rem0 - rem0) with 0 by lia.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      all: lazymatch goal with
           | |- Permutation _ _ => apply Permutation_refl
           | |- XINV _ _ _ => unfold XINV; split; reflexivity
           | |- pk_in _ _ _ _ => exact PKIN0
           | |- _ = _ => reflexivity
           | |- ALED _ _ _ _ => exists 0, 0; cbn [xs_len xs_base lb_bytes fold_right]; unfold ADX_PER_EXT, ADX_PUSH_CF;
                                 pose proof (aCm_pos H HH 0 ltac:(lia)); rewrite (aCf0 H HH); lia
           | |- _ <= _ <= _ => lia
           | |- _ <= _ => lia
           | |- ?G => idtac "MAIN0" G
           end. }
    eapply (ah_seq H HH); [eapply (DX_loop (Z.to_nat rem0)); [exact FW| rewrite Z2Nat.id by lia; lia| exact KREL| exact MP| exact VIS]|].
    intros [ms2 mo2] EXT. unfold dx_exit in EXT. cbn [cfg_ms cfg_model] in EXT.
    destruct EXT as (rax2 & c1 & c0 & d1 & d2 & d3 & d4 & d5 & c4 & c5 & c6 & c7 & c10 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & m2 & st2 & errv2 & P2 & xs2 & NB2 & cur2 & rem2 & K2 & MP2 & CASES).
    destruct CASES as [(R0 & FW2 & MS2)|(line & cc & LN & FW2 & MS2)].
    - eapply dx_ret1; [exact FW2| exact R0| exact K2| exact MP2| exact MS2].
    - eapply dx_fail; [exact FW2| exact LN| exact K2| exact MP2| exact MS2].
  Qed.
End W.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis RAISE : araise_stmt H.
  Let HH : asan_rt_hyps H := proj1 HHx.

  Theorem adecexts_spec : decexts_stmt H.
  Proof using HHx RAISE.
    unfold decexts_stmt. intros until CH.
    intros VIS A0 A1 EO XE0 XO0 BEL ESH PK PIN REM1 REMB SPK PKB PK8 ACCP OFFCH BIN EBIN BS BSL CRB BSH LM LIBSUB CX MF0 IDS IDB HP KREL BY CN AUX SPB BHI SPA ST CEIL LO SK0 ERR MI TP AC CLOSED RFS LFB ATHR CHN0 CHS PF HAL0 RAE.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (LO8K : lo + 8592 <= bv_unsigned sp).
    { clear - LO. unfold DECEXTS_STACK, FR_ech_decode_echconfig_exts, SKPOPFREE_STACK, EXTFREE_STACK, FR_ossl_echext_free, CFREE_STACK, AFREE_STACK, FR_sk_pop_free in LO. lia. }
    assert (HB : forall b, In b (mid_errblocks M ++ LB) -> 0 < blk_addr b /\ AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). repeat split; assumption. }
    pose proof EO as (_ & EIN0 & O1 & O2 & O3 & O4 & _).
    pose proof (HB _ ltac:(apply in_or_app; right; exact EIN0)) as (EP0 & _ & EH & _). cbn [blk_addr blk_size fst snd] in EP0, EH. unfold ENTRY_SIZE in EH.
    assert (EAL8 : ee mod 8 = 0).
    { pose proof (ah_blocks H HH _ _ _ _ HP ltac:(apply in_or_app; right; exact EIN0)) as (_ & E16 & _). cbn [blk_addr blk_size fst snd] in E16. clear - E16. Z.div_mod_to_equations. lia. }
    pose proof (HB _ ltac:(apply in_or_app; right; exact BIN)) as (BP0 & _ & BH & _). cbn [blk_addr blk_size fst snd] in BP0, BH.
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. pose proof ACCP as (PKP & PKH & _). pose proof ESH as [ETOP _]. unfold ENTRY_SIZE in ETOP.
    unfold BUF_shad in BSH. pose proof BSL as BSL'. unfold zlength in BSL'.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply adx_seg1 with (lo := lo);
      [exact A0| exact A1| exact PKP| exact PKH| clear - EP0; lia| exact ETOP| exact PK8| exact EAL8| exact GSB| exact SHB0| exact ST| exact CEIL| clear - LO8K; lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & j0 & a1' & a2' & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (XPs : forall X, xpres H (mid_errblocks M ++ LB) (bv_unsigned sp) X m m1).
    { intros X. eapply (xpres_of_munch H _ (mid_errblocks M ++ LB)); [exact HH| exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; clear - CEIL LO8K SPR; lia| apply Forall_nil]. }
    assert (XPL : forall X, xpres H LB (bv_unsigned sp) X m m1).
    { intros X. eapply (xpres_weaken H); [apply XPs| apply Z.le_refl| intros b Hb; apply in_or_app; right; exact Hb| intros q Hq; exact Hq]. }
    assert (CW : Forall (aclient_write_ok H (mid_errblocks M ++ LB)) [(bv_unsigned sp + -144, bv_unsigned sp)]) by (apply Forall_cons; [left; cbn; clear - CEIL LO8K; lia| apply Forall_nil]).
    assert (WE : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(bv_unsigned sp + -144, bv_unsigned sp)]).
    { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right. unfold AHI_LO. clear - CEIL LO8K ACEILB. lia. }
    eapply (dx_main H HHx RAISE) with (j0 := j0) (m1 := m1) (errv := errv); try eassumption.
    all: lazymatch goal with
         | |- ACONST _ => eapply ACONST_frame; [exact AC| exact MU1| exact WM1|]; apply Forall_cons; [apply aconst_ok_hi; unfold AHI_LO; clear - CEIL LO8K ACEILB; lia| apply Forall_nil]
         | |- rw_cells _ _ (errno_addr _) _ => rewrite TP in ERR |- *; eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]; rewrite unsigned_lit by (unfold ATP; lia); cbn; unfold ATP; clear - CEIL LO8K ACEILB; lia
         | |- as_rauxv_ok _ _ _ => eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]
         | |- as_RHEAP _ _ _ _ => eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]
         | |- LIBMID _ _ _ => eapply (LIBMID_xpres0 H); [exact LM| exact CX| apply (XPs [])| intros b Hb; apply in_or_app; right; apply LIBSUB; exact Hb| intros b Hb; apply in_or_app; left; exact Hb]
         | |- ENTRYobj _ _ _ _ => eapply (ENTRYobj_frame_law H LB LB m m1); [exact EO| intros b Hb; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb)| apply (XPL [])|];
                                   intros b Hb; pose proof (HB _ ltac:(apply in_or_app; right; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb))) as (_ & _ & K5 & _); clear - K5 CEIL LO8K; lia
         | |- ENTRY_shad _ _ _ => eapply (ENTRY_shad_frame_law H LB m m1); [exact ESH| intros b Hb; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb)| apply (XPL [])|];
                                   intros b Hb; pose proof (HB _ ltac:(apply in_or_app; right; exact (ENTRYobj_owned_law _ _ _ _ EO _ Hb))) as (_ & _ & K5 & _); clear - K5 CEIL LO8K; lia
         | |- rw_cells _ _ _ (pk_cells _ _ _) => eapply rw_cells_transport; [exact PK| exact MU1| exact WM1| cbn; clear - SPK; lia]
         | |- bytes_at _ _ _ _ => eapply bytes_at_transport; [exact BS| exact MU1|]; cbn; clear - BH BSL' CEIL LO8K; lia
         | |- accessible _ _ 24 => eapply accessible_across; [exact ACCP| exact MU1| exact WE]
         | |- accessible _ _ _ => eapply accessible_across; [exact BSH| exact MU1| exact WE]
         | |- stack0 _ _ _ => eapply stack0_transport; [exact SK0| exact MU1| exact WM1|]; apply Forall_cons; [left; cbn [fst snd]; unfold AHI_LO; clear - CEIL LO8K ACEILB; lia| apply Forall_nil]
         | |- as_RFS _ _ _ => eapply (RFS_via_xpres H HH); [exact RFS| apply (XPL [])| apply Forall_nil]
         | |- xpres _ _ _ _ _ _ => apply XPL
         | |- as_MPRES _ _ _ => exact MP1
         | |- _ /\ _ => repeat split; assumption
         | |- ?G => idtac "WSPRE" G
         end.
    all: fail "WSPRE".
  Qed.
End WS.
