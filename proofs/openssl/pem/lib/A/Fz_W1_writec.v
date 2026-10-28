(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_M_malloc Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_new Fz_W1_sync Fz_W1_grow Fz_W1_write.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition src_blk (live : list (Z * Z)) (IN n : Z) (ex : list Z) : Prop :=
  (0xb8f190 <= IN /\ IN + n <= 0xb9f190) \/ (exists p k, In (p, k) live /\ p <= IN /\ IN + n <= p + k /\ ~ In p ex).

Lemma c4_byte1 : forall (m : mem) A fl, 0 <= fl < 2 ^ 32 -> rw_cells asegs m A [C4 (Z_to_bv 64 fl)] -> rw_cells asegs m (A + 1) [C1 (Z_to_bv 8 (fl ≫ 8))].
Proof.
  intros m A fl R H.
  assert (H4 : rw_cells asegs m A [C1 (Z_to_bv 8 fl); C1 (Z_to_bv 8 (fl ≫ 8)); C1 (Z_to_bv 8 (fl ≫ 8 ≫ 8)); C1 (Z_to_bv 8 (fl ≫ 8 ≫ 8 ≫ 8))]).
  { apply (rw_cells_recast m A _ _ H); [cbn; tauto|]. cbn [cells_bytes cbytes app]. unfold le4. rewrite unsigned_lit by lia. reflexivity. }
  exact (rw_cells_head m (A + 1) _ _ (rw_cells_skip m A [C1 (Z_to_bv 8 fl)] _ H4)).
Qed.
(* [comment removed for export] *)
Lemma bio_flags_byte1 : forall (m : mem) BI iw shw fl rrw numw padw ptrw, 0 <= fl < 2 ^ 32 ->
  rw_cells asegs m (BI + 40) (bio_w1_cells iw shw fl rrw numw padw ptrw) -> rw_cells asegs m (BI + 49) [C1 (Z_to_bv 8 (fl ≫ 8))].
Proof.
  intros m BI iw shw fl rrw numw padw ptrw R BW. unfold bio_w1_cells in BW.
  pose proof (rw_cells_head m _ _ _ (rw_cells_skip m (BI + 40) [C4 iw; C4 shw] _ BW)) as H. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  replace (BI + 49) with (BI + 40 + 8 + 1) by lia. exact (c4_byte1 m _ fl R H).
Qed.

Section CWr.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.
Hypothesis MSI : memset_icontract RT e_asan_memset.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis C_CM : crypto_malloc_env_stmt RT.
Hypothesis C_CCR : crypto_clear_realloc_env_stmt RT.

Lemma src_facts : forall (Σ : rts RT) (m : mem) IN n ex usp lo, ART RT Σ m -> src_blk (rt_live RT Σ) IN n ex -> 0 <= n -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x10007fff8000 <= lo ->
  acc asegs m IN n /\ rng_class RT Σ IN n /\ IN + n <= lo /\ 0 < IN /\ (forall i, 0 <= i < n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp (IN + i))
  /\ (forall q k, In (q, k) (rt_live RT Σ) -> In q ex -> 0 < n -> IN + n <= q \/ q + k <= IN) /\ (IN + n <= 0xb9f190 \/ 0xbc6000 <= IN).
Proof.
  intros Σ m IN n ex usp lo HA [(L & H) | (p & k & Hin & L & H & NE)] Hn LOW HLOS.
  - assert (CS : forall i, 0 <= i < n -> client_static (IN + i)) by (intros i Hi; apply client_static_intro; right; left; lia).
    split; [apply (af_acc_static RT AF Σ m IN n HA ltac:(lia)); intros i Hi; split; [exact (CS i Hi) | left; lia]|].
    split; [do 3 right; unfold SEGTOP_A; lia|]. split; [lia|]. split; [lia|]. split; [intros i Hi; apply acl_static; exact (CS i Hi)|]. split; [| left; lia].
    intros q k' Hq _ _. pose proof (af_live_range RT AF Σ m q k' HA Hq) as (_ & _ & R2). unfold SEGTOP_A in R2. destruct R2; [right | left]; lia.
  - pose proof (af_live_range RT AF Σ m p k HA Hin) as (R0 & R1 & R2).
    split; [exact (acc_sub asegs m p k IN n (proj2 (af_acc_live RT AF Σ m p k HA Hin)) L H)|].
    split; [left; exists p, k; split; [exact Hin | lia]|]. split; [lia|]. split; [lia|].
    split; [intros i Hi; apply (acl_live _ _ _ p k); [exact Hin | lia]|]. split; [| unfold SEGTOP_A in R2; clear - R2 L H; lia].
    intros q k' Hq Hex Hn'. destruct (Z.eq_dec q p) as [-> | NEQ]; [exfalso; exact (NE Hex)|].
    pose proof (live_ne_apart RT AF Σ m p k q k' HA Hin Hq ltac:(intros E; injection E; intros _ E1; exact (NEQ (eq_sym E1)))). lia.
Qed.

Definition WRF_W (BI BM R D max : Z) : list (Z * Z) := [(BI + 48, BI + 52); (BM, BM + 8); (R, R + 32); (D, D + max)].

(* [comment removed for export] *)
Definition write_fit_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl IN inl : Z) (rrw numw padw rmaxw : word) (src : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 IN -> a2 = Z_to_bv 64 inl ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 0)) ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw (Z_to_bv 64 0)) -> BM <> R ->
  In (D, max) (rt_live RT Σ) -> D <> BI -> D <> BB -> D <> BM -> D <> R ->
  0 <= off <= len -> len <= max -> len - off + inl <= max -> max < 2 ^ 31 -> 1 <= inl ->
  bytes_at asegs m IN src -> Z.of_nat (length src) = inl -> src_blk (rt_live RT Σ) IN inl [BI; BM; R; D] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 160 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_write m)))
    (ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 inl) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (WRF_W BI BM R D max) m m'
        /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB))
        /\ rw_cells asegs m' BM (bufmem_cells (len - off + inl) D max (Z_to_bv 64 0)) /\ rw_cells asegs m' R (readp_cells (len - off + inl) D 0 (Z_to_bv 64 max) (Z_to_bv 64 0)))).

Theorem write_fit_cps : write_fit_stmt.
Proof.
  pose proof (mem_buf_sync_cps RT AF GOBJ AFP MMV) as C_SY. pose proof (grow_fit_cps RT AF GOBJ AFP MSI) as C_GF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl IN inl rrw numw padw rmaxw src
    FDO MST -> -> -> -> INBI BIAL BW FLOK INBB BBAL BBC INBM BMAL BMC INR RAL RC NMR IND NDBI NDBB NDBM NDR HOFF HLEN HFIT HMAX HINL SB LSRC SRC ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 96 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -80). set (blen := len - off) in *.
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 96) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BB 16 ART0 INBB ltac:(lia)) as BBHI. pose proof (proj2 (af_acc_live RT AF Σ m BB 16 ART0 INBB)) as ACCBB.
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m R 32 ART0 INR ltac:(lia)) as RHI. pose proof (proj2 (af_acc_live RT AF Σ m R 32 ART0 INR)) as ACCR.
  pose proof (af_live_range RT AF Σ m D max ART0 IND) as (D0 & DLO' & _). assert (DLO : D + max <= lo) by (clear - DLO' LOW; lia). clear DLO'.
  pose proof (live_ne_apart RT AF Σ m BI 128 BB 16 ART0 INBI INBB ltac:(intros E; injection E; lia)) as APIB.
  pose proof (live_ne_apart RT AF Σ m BI 128 R 32 ART0 INBI INR ltac:(intros E; injection E; lia)) as APIR.
  pose proof (live_ne_apart RT AF Σ m BI 128 BM 32 ART0 INBI INBM ltac:(intros E; injection E; lia)) as APIM.
  pose proof (live_ne_apart RT AF Σ m BM 32 R 32 ART0 INBM INR ltac:(intros E; injection E; exact NMR)) as APMR.
  pose proof (live_ne_apart RT AF Σ m BB 16 BM 32 ART0 INBB INBM ltac:(intros E; injection E; lia)) as APBM.
  pose proof (live_ne_apart RT AF Σ m BB 16 R 32 ART0 INBB INR ltac:(intros E; injection E; lia)) as APBR.
  pose proof (live_ne_apart RT AF Σ m D max BI 128 ART0 IND INBI ltac:(intros E; injection E; intros _; exact NDBI)) as APDI.
  pose proof (live_ne_apart RT AF Σ m D max BB 16 ART0 IND INBB ltac:(intros E; injection E; intros _; exact NDBB)) as APDB.
  pose proof (live_ne_apart RT AF Σ m D max BM 32 ART0 IND INBM ltac:(intros E; injection E; intros _; exact NDBM)) as APDM.
  pose proof (live_ne_apart RT AF Σ m D max R 32 ART0 IND INR ltac:(intros E; injection E; intros _; exact NDR)) as APDR.
  assert (INL0 : 0 < inl) by (clear - HINL; lia).
  destruct (src_facts Σ m IN inl [BI; BM; R; D] usp lo ART0 SRC ltac:(clear - HINL; lia) LOW HLOS) as (ACCIN & CLIN & INLO & INLOW & ACLIN & APIN & INCL).
  pose proof (APIN BI 128 INBI ltac:(left; reflexivity) INL0) as APNI. pose proof (APIN BM 32 INBM ltac:(right; left; reflexivity) INL0) as APNM.
  pose proof (APIN R 32 INR ltac:(do 2 right; left; reflexivity) INL0) as APNR. pose proof (APIN D max IND ltac:(do 3 right; left; reflexivity) INL0) as APND. clear APIN.
  assert (ACLIN' : forall x, IN <= x < IN + inl -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x) by (intros x Hx; replace x with (IN + (x - IN)) by (clear; lia); apply ACLIN; clear - Hx; lia).
  assert (COP : lo + RT_STACK <= usp1 /\ usp1 + 16 <= USTACK_TOP /\ usp1 mod 16 = 0).
  { fold usp in SPA. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|]. split; [unfold USTACK_TOP in *; clear - NUM; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 5). lia. }
  pose proof (bio_flags_byte1 m BI _ _ fl rrw numw padw _ ltac:(destruct FLOK; lia) BW) as FB1.
  unfold readp_cells in RC.
  destruct (live_CB RT AF Σ m D max ART0 IND ltac:(clear - HMAX HFIT HINL HOFF; lia)) as (junk & LJ & DC).
  (* [comment removed for export] *)
  pose proof (wr_s0_walk ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R IN inl fl blen rrw numw padw
                (Z_to_bv 64 (D + off)) rmaxw (Z_to_bv 64 0)
                HLO1 HLOS SPH ST UT SHC BW FLOK FB1 ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO RC ACCR R0 RAL RHI RLO APIB APIR INLOW
                ltac:(clear - INLO HLO1 SPH; lia) ltac:(clear - HINL HFIT HMAX HOFF; lia) ltac:(clear - HOFF HFIT HMAX HINL; subst blen; lia) MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1 & BW1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 96) ART0 ltac:(clear - NUM; lia)); [| exact WM1].
    intros x Hx. apply MU1. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Hx; [apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hin; lia] | left; unfold USTACK_TOP in *; clear - Hin NUM; lia]. }
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 48 <= bv_unsigned x < BI + 52) -> m1 x = m x).
  { intros x Hx HnF. apply MU1. cbn [outside]. split; [clear - HnF; lia | split; [| exact I]]. destruct (cl_split RT AF Σ m usp 96 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Hx); clear - H; lia. }
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST1 (conj LOW COP))).
  assert (BBC1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m m1 _ _ BBC); [| exact WM1]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1; [apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia] | clear - Hx APIB; lia]. }
  assert (BMC1 : rw_cells asegs m1 BM (bufmem_cells len D max (Z_to_bv 64 0))).
  { apply (rw_cells_agree asegs m m1 _ _ BMC); [| exact WM1]. intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1; [apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia] | clear - Hx APIM; lia]. }
  assert (RC1 : rw_cells asegs m1 R (readp_cells len D off rmaxw (Z_to_bv 64 0))).
  { unfold readp_cells. fold blen. apply (rw_cells_agree asegs m m1 _ _ RC); [| exact WM1]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1; [apply (acl_live _ _ _ R 32); [exact INR | clear - Hx; lia] | clear - Hx APIR; lia]. }
  assert (DC1 : rw_cells asegs m1 D [CB (Z.to_nat max) junk]).
  { apply (rw_cells_agree asegs m m1 _ _ DC); [| exact WM1]. intros x Hx. cbv beta in Hx. cbn [cells_size csize] in Hx. rewrite Nat.add_0_r, Z2Nat.id in Hx by (clear - HMAX HFIT HINL HOFF; lia).
    apply P1; [apply (acl_live _ _ _ D max); [exact IND | clear - Hx; lia] | clear - Hx APDI; lia]. }
  (* [comment removed for export] *)
  apply (C_SY Σ PMc (Z_to_bv 64 SITE_wr_sync) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 inl) (Z_to_bv 64 BI) (Z_to_bv 64 0) (Z_to_bv 64 fl) (Z_to_bv 64 ((BI + 48) ≫ 3))
           a4 a5 a6 a7 (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 BI) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 blen)
           s9 s10 s11 t3 t4 t5 t6 F fc m1 lo BI 128 BB BM R D len max off (fl - fl mod 16) 1 (Z_to_bv 64 1) rrw numw padw rmaxw (Z_to_bv 64 0) junk
           FDO MST eq_refl eq_refl INBI ltac:(clear; lia) BIAL BW1 ltac:(clear; lia) INBB BBAL BBC1 INBM BMAL BMC1 INR RAL RC1 NMR IND NDBB NDBM NDR HOFF
           HLEN ltac:(clear - HMAX HFIT HINL HOFF; subst blen; lia) LJ DC1 ART1 MI1 CO1 ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia) T c1 Hc1').
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (v2 & rmaxw2 & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BMC2 & RC2 & _) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_wr_sync) in Hc2' by (unfold SITE_wr_sync; lia).
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 48 <= bv_unsigned x < BI + 52) -> outside (SY_W BM R D max) (bv_unsigned x) -> m2 x = m x).
  { intros x Hx HnF Ho. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) Ho). exact (P1 x Hx HnF). }
  assert (BBC2 : rw_cells asegs m2 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m1 m2 _ _ BBC1); [| exact WM2]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES2; [apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia] | unfold SY_W; cbn [outside]; clear - Hx APBM APBR APDB; lia]. }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & SHC2 & _ & _ & UT2). pose proof (proj2 (af_acc_live RT AF Σ m2 BB 16 ART2 INBB)) as ACCBB2.
  assert (CO2 : call_ok RT Σ m2 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST2 (conj LOW COP))).
  (* [comment removed for export] *)
  pose proof (wr_s1_walk sp gp y0 y1 y2 v2 h1 h2 h3 h4 h5 h6 h7 s9 s10 s11 y3 y4 y5 y6 (Z_to_bv 64 BI) F2 fc2 m2 BB BM R IN inl blen SPH UT2 SHC2 BBC2 ACCBB2 BB0 BBAL BBHI
                ltac:(clear - BBLO HLO1 SPH; lia) ltac:(clear - HOFF; subst blen; lia) ltac:(clear - HINL; lia) ltac:(clear - HFIT HMAX HOFF HINL; subst blen; lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  unfold blen in BMC2.
  apply (C_GF Σ PMc (Z_to_bv 64 SITE_wr_grow) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) y0 y1 y2 sp (Z_to_bv 64 inl) (Z_to_bv 64 BM) (Z_to_bv 64 (blen + inl)) h2 h3 h4 h5 h6 h7
           (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 blen)
           s9 s10 s11 y3 y4 y5 y6 F2 fc2 m2 lo BM D (len - off) max (blen + inl) (Z_to_bv 64 0)
           FDO MST eq_refl eq_refl eq_refl INBM BMAL BMC2 IND NDBM ltac:(clear - HOFF; lia) ltac:(clear - HINL; subst blen; lia) ltac:(clear - HFIT; subst blen; lia) HMAX ART2 MI2 CO2
           ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia) T c3 Hc3').
  clear Hc3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BMC4) & Hc4'). clear Hc4.
  destruct RS4 as (z0 & z1 & z2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & z3 & z4 & z5 & z6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_wr_grow) in Hc4' by (unfold SITE_wr_grow; lia).
  assert (P4 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 48 <= bv_unsigned x < BI + 52) -> outside (SY_W BM R D max) (bv_unsigned x) ->
               outside (GRF_W BM D max) (bv_unsigned x) -> m4 x = m x).
  { intros x Hx HnF Ho Ho'. rewrite (PRES4 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) Ho'). exact (P2 x Hx HnF Ho). }
  assert (BBC4 : rw_cells asegs m4 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m2 m4 _ _ BBC2); [| exact WM4]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES4; [apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia] | unfold GRF_W; cbn [outside]; clear - Hx APBM APDB; lia]. }
  destruct (af_client_consts RT AF Σ m4 ART4) as (_ & SHC4 & _ & _ & UT4). pose proof (proj2 (af_acc_live RT AF Σ m4 BB 16 ART4 INBB)) as ACCBB4.
  pose proof (proj2 (af_acc_live RT AF Σ m4 BM 32 ART4 INBM)) as ACCBM4.
  assert (CO4 : call_ok RT Σ m4 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST4 (conj LOW COP))).
  (* [comment removed for export] *)
  unfold bufmem_cells in BMC4.
  pose proof (wr_s2_walk sp gp z0 z1 z2 k1 k2 k3 k4 k5 k6 k7 s9 s10 s11 z3 z4 z5 z6 F4 fc4 m4 BB BM R D IN inl blen (blen + inl) (Z_to_bv 64 (blen + inl)) (Z_to_bv 64 max) (Z_to_bv 64 0)
                SPH UT4 SHC4 BBC4 ACCBB4 BB0 BBAL BBHI ltac:(clear - BBLO HLO1 SPH; lia) BMC4 ACCBM4 BM0 BMAL BMHI ltac:(clear - BMLO HLO1 SPH; lia)
                ltac:(clear - HINL HFIT HMAX HOFF; subst blen; lia) ltac:(clear - D0; lia) ltac:(clear - DLO HLO1 SPH HFIT HINL HOFF; subst blen; lia) ltac:(clear - HOFF; subst blen; lia) MI4) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5.
  (* [comment removed for export] *)
  destruct (src_facts Σ m4 IN inl [BI; BM; R; D] usp lo ART4 SRC ltac:(clear - HINL; lia) LOW HLOS) as (ACCIN4 & _).
  assert (SB4 : bytes_at asegs m4 IN src).
  { apply (bytes_at_agree asegs m m4 _ _ SB). intros x Hx. cbv beta in Hx. rewrite LSRC in Hx. apply P4; [apply ACLIN'; exact Hx | clear - Hx APNI; lia | unfold SY_W; cbn [outside]; clear - Hx APNM APNR APND; lia | unfold GRF_W; cbn [outside]; clear - Hx APNM APND; lia]. }
  apply (MCP Σ PMc (Z_to_bv 64 SITE_wr_cpy1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) z0 z1 z2 sp (Z_to_bv 64 inl) (Z_to_bv 64 (D + blen)) (Z_to_bv 64 IN) (Z_to_bv 64 inl) k3 k4 k5 k6 k7
           (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 blen)
           s9 s10 s11 z3 z4 z5 z6 F4 fc4 m4 (D + blen) IN src lo FDO MST eq_refl eq_refl ltac:(rewrite LSRC; reflexivity)
           ltac:(clear - D0 DLO HLO1 SPH HFIT HINL HOFF; subst blen; lia) ltac:(clear - INLOW INLO HLO1 SPH HINL; lia) ltac:(rewrite LSRC; clear - HINL HFIT HMAX HOFF; lia) SB4).
  { rewrite LSRC. split; [intros _; exact (conj ACCIN4 CLIN) | left; exact INLO]. }
  { rewrite LSRC. exact (live_checked_dst RT AF Σ m4 _ D max (D + blen) inl ART4 IND ltac:(clear - HOFF; subst blen; lia) ltac:(clear - HFIT; subst blen; lia) ltac:(clear - HINL; lia)). }
  { rewrite LSRC. clear - APND HOFF HFIT HINL. subst blen. lia. }
  { exact ART4. } { exact MI4. } { exact CO4. }
  { exact Hc5'. }
  clear Hc5'. intros c6 Hc6.
  destruct (ASTA_unpack RT Σ _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & _) & Hc6'). clear Hc6.
  destruct RS6 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite LSRC in PRES6. rewrite (ret_pc_even SITE_wr_cpy1) in Hc6' by (unfold SITE_wr_cpy1; lia).
  assert (P6 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 48 <= bv_unsigned x < BI + 52) -> outside (SY_W BM R D max) (bv_unsigned x) ->
               outside (GRF_W BM D max) (bv_unsigned x) -> m6 x = m x).
  { intros x Hx HnF Ho Ho'. rewrite (PRES6 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) ltac:(unfold GRF_W in Ho'; cbn [outside] in Ho'; clear - Ho' HOFF HFIT HINL; subst blen; lia)).
    exact (P4 x Hx HnF Ho Ho'). }
  assert (BBC6 : rw_cells asegs m6 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m4 m6 _ _ BBC4); [| exact WM6]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES6; [apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia] | clear - Hx APDB HOFF HFIT HINL; subst blen; lia]. }
  assert (BMC6 : rw_cells asegs m6 BM (bufmem_cells (blen + inl) D max (Z_to_bv 64 0))).
  { unfold bufmem_cells. apply (rw_cells_agree asegs m4 m6 _ _ BMC4); [| exact WM6]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES6; [apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia] | clear - Hx APDM HOFF HFIT HINL; subst blen; lia]. }
  destruct (af_client_consts RT AF Σ m6 ART6) as (_ & SHC6 & _ & _ & UT6). pose proof (proj2 (af_acc_live RT AF Σ m6 BB 16 ART6 INBB)) as ACCBB6.
  assert (CO6 : call_ok RT Σ m6 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST6 (conj LOW COP))).
  (* [comment removed for export] *)
  pose proof (wr_s3_walk sp gp w0 w1 w2 (Z_to_bv 64 (D + blen)) g1 g2 g3 g4 g5 g6 g7 s9 s10 s11 w3 w4 w5 w6 F6 fc6 m6 BB BM R IN inl blen SPH UT6 SHC6 BBC6 ACCBB6 BB0 BBAL BBHI
                ltac:(clear - BBLO HLO1 SPH; lia) ltac:(clear - BM0 BMLO HLO1 SPH; lia) ltac:(clear - R0 RLO HLO1 SPH; lia) MI6) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ _ _ c7 Hc7) as (ms7 & -> & Hc7'). clear Hc7.
  (* [comment removed for export] *)
  apply (MCP Σ PMc (Z_to_bv 64 SITE_wr_cpy2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 inl) (Z_to_bv 64 R) (Z_to_bv 64 BM) (Z_to_bv 64 32) g3 g4 g5 g6 g7
           (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 blen)
           s9 s10 s11 w3 w4 w5 w6 F6 fc6 m6 R BM (bufmem_bytes (blen + inl) D max (Z_to_bv 64 0)) lo FDO MST eq_refl eq_refl ltac:(rewrite bufmem_bytes_length; reflexivity)
           ltac:(clear - R0 RLO HLO1 SPH; lia) ltac:(clear - BM0 BMLO HLO1 SPH; lia) ltac:(rewrite bufmem_bytes_length; clear; lia) (proj2 (proj1 BMC6))).
  { rewrite bufmem_bytes_length. exact (live_checked_src RT AF Σ m6 _ lo BM 32 BM 32 ART6 INBM ltac:(clear; lia) ltac:(clear; lia) LOW). }
  { rewrite bufmem_bytes_length. exact (live_checked_dst RT AF Σ m6 _ R 32 R 32 ART6 INR ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)). }
  { rewrite bufmem_bytes_length. clear - APMR. lia. }
  { exact ART6. } { exact MI6. } { exact CO6. }
  { exact Hc7'. }
  clear Hc7'. intros c8 Hc8.
  destruct (ASTA_unpack RT Σ _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & CP8) & Hc8'). clear Hc8.
  destruct RS8 as (x0 & x1 & x2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & F8 & fc8 & ->).
  rewrite EU1 in ST8, PRES8. rewrite bufmem_bytes_length in PRES8. change (Z.of_nat 32) with 32 in PRES8. rewrite (ret_pc_even SITE_wr_cpy2) in Hc8' by (unfold SITE_wr_cpy2; lia).
  assert (P8 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> outside (WRF_W BI BM R D max) (bv_unsigned x) -> m8 x = m x).
  { intros x Hx Ho. unfold WRF_W in Ho. cbn [outside] in Ho.
    rewrite (PRES8 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) ltac:(clear - Ho; lia)).
    apply P6; [exact Hx | clear - Ho; lia | unfold SY_W; cbn [outside]; clear - Ho; lia | unfold GRF_W; cbn [outside]; clear - Ho; lia]. }
  assert (AGS : forall x : word, usp1 <= bv_unsigned x < usp -> m8 x = m1 x).
  { intros x Hx. assert (HAx : forall live frames, aclient live frames usp1 (bv_unsigned x)) by (intros; left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia).
    rewrite (PRES8 x (HAx _ _) ltac:(unfold usp1, RT_STACK in *; clear - Hx RLO HSTK; lia)).
    rewrite (PRES6 x (HAx _ _) ltac:(unfold usp1, RT_STACK in *; clear - Hx DLO HSTK HOFF HFIT HINL; subst blen; lia)).
    rewrite (PRES4 x (HAx _ _) ltac:(unfold GRF_W; cbn [outside]; unfold usp1, RT_STACK in *; clear - Hx DLO BMLO HSTK; lia)).
    apply (PRES2 x (HAx _ _)). unfold SY_W. cbn [outside]. unfold usp1, RT_STACK in *; clear - Hx DLO BMLO RLO HSTK; lia. }
  assert (FR8 : rw_cells asegs m8 usp1 (wr_frame s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree asegs m1 m8 _ _ FR1); [| exact (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM6 WM8)))].
    intros x Hx. cbv beta in Hx. unfold wr_frame in Hx. cbn [cells_size csize Nat.add] in Hx. apply AGS. unfold usp1 in *. clear - Hx. lia. }
  destruct (af_client_consts RT AF Σ m8 ART8) as (_ & _ & _ & _ & UT8).
  (* [comment removed for export] *)
  pose proof (wr_s4_walk ra sp gp x0 x1 x2 s0 s1 (Z_to_bv 64 R) e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6
                (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 blen)
                F8 fc8 m8 inl lo ltac:(clear - HLO1; lia) SPH ST8 UT8 FR8 ltac:(clear - HINL HFIT HMAX HOFF; lia) MI8) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc8' c9 Hc9.
  apply Hk. eapply ASTA_conseq; [exact Hc9|]. intros ms (q0 & q1 & q2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & q3 & q4 & q5 & q6 & m9 & -> & MU9 & WM9 & MI9 & ST9).
  fold usp in ST9. exists m9. split; [do 16 eexists; reflexivity|].
  assert (E9 : forall x : word, m9 x = m8 x) by (intros x; apply MU9; exact I).
  assert (ART9 : ART RT Σ m9) by (apply (af_frame RT AF Σ m8 m9 usp1 ART8 ltac:(unfold usp1; clear - NUM; lia)); [intros x _; apply E9 | exact WM9]).
  split; [exact (conj ART9 (conj MI9 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM8 WM9))))) ST9)))|].
  split; [intros x Hx Ho; rewrite E9; exact (P8 x Hx Ho)|].
  split.
  { apply (rw_cells_agree_nw asegs m1 m9 _ _ BW1). intros x Hx. cbv beta in Hx. unfold bio_w1_cells in Hx. cbn [cells_size csize Nat.add] in Hx. rewrite E9.
    assert (HAx : aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned x)) by (apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx; lia]).
    rewrite (PRES8 x HAx ltac:(clear - Hx APIR; lia)). rewrite (PRES6 x HAx ltac:(clear - Hx APDI HOFF HFIT HINL; subst blen; lia)).
    rewrite (PRES4 x HAx ltac:(unfold GRF_W; cbn [outside]; clear - Hx APIM APDI; lia)). apply (PRES2 x HAx). unfold SY_W. cbn [outside]. clear - Hx APIM APIR APDI. lia. }
  split.
  { apply (rw_cells_agree asegs m6 m9 _ _ BMC6); [| exact (wmono_trans asegs _ _ _ WM8 WM9)].
    intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx. rewrite E9.
    apply PRES8; [apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp); [apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia] | auto | auto | unfold usp1; clear; lia] | clear - Hx APMR; lia]. }
  replace (readp_cells (blen + inl) D 0 (Z_to_bv 64 max) (Z_to_bv 64 0)) with (bufmem_cells (blen + inl) D max (Z_to_bv 64 0)) by (unfold readp_cells, bufmem_cells; rewrite Z.sub_0_r, Z.add_0_r; reflexivity).
  apply bufmem_cells_of_bytes; [apply (bytes_at_agree asegs m8 m9 _ _ CP8); intros x _; apply E9|].
  exact (wr_at_wm m8 m9 _ _ (proj1 (af_acc_live RT AF Σ m8 R 32 ART8 INR)) WM9).
Qed.

Definition WR_SITES : list (Z * Z) := (SITE_wr_grow, e_mem_write) :: GR_SITES.
Definition WR_CALLS : list (Z * Z) := (SITE_wr_grow, e_BUF_MEM_grow_clean) :: GR_CALLS.
Definition WRG_W (BI BM R : Z) : list (Z * Z) := [(BI + 48, BI + 52); (BM, BM + 24); (R, R + 32); (G_ALLOW_CUST, G_ALLOW_CUST + 1)].
(* [comment removed for export] *)
Definition wdata_opt (live : list (Z * Z)) (BI BB BM R D len max off : Z) : Prop :=
  (D = 0 /\ max = 0 /\ len = 0 /\ off = 0) \/ (In (D, max) live /\ 1 <= max /\ D <> BI /\ D <> BB /\ D <> BM /\ D <> R).

(* [comment removed for export] *)
Definition write_re_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl IN inl : Z) (rrw numw padw rmaxw : word) (src : list byte) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 IN -> a2 = Z_to_bv 64 inl ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 0)) ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw (Z_to_bv 64 0)) -> BM <> R ->
  wdata_opt (rt_live RT Σ) BI BB BM R D len max off ->
  0 <= off <= len -> len <= max -> max < len - off + inl -> gr_n (len - off + inl) <= 0x8000000 -> 1 <= inl ->
  bytes_at asegs m IN src -> Z.of_nat (length src) = inl -> src_blk (rt_live RT Σ) IN inl [BI; BM; R; D] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 224 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_mem_write (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) WR_SITES WR_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (gr_n (len - off + inl)) <= rt_credit RT Σ -> cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_write m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 inl) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres_fp (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) (WRG_W BI BM R) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB))
           /\ rw_cells asegs m' BM (bufmem_cells (len - off + inl) q (gr_n (len - off + inl)) (Z_to_bv 64 0))
           /\ rw_cells asegs m' R (readp_cells (len - off + inl) q 0 (Z_to_bv 64 (gr_n (len - off + inl))) (Z_to_bv 64 0))) c
       /\ rt_live RT Σ' = (q, gr_n (len - off + inl)) :: live_remove D (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (gr_n (len - off + inl)) /\ 0 < q /\ q mod 16 = 0 /\ q + gr_n (len - off + inl) < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem write_re_cps : write_re_stmt.
Proof.
  pose proof (mem_buf_sync_cps RT AF GOBJ AFP MMV) as C_SY. pose proof (mem_buf_sync_same_cps RT AF GOBJ AFP) as C_SS. pose proof (grow_re_cps RT AF GOBJ AFP C_CM MSI C_CCR) as C_GR.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl IN inl rrw numw padw rmaxw src outer lb canary
    FDO MST -> -> -> -> INBI BIAL BW FLOK INBB BBAL BBC INBM BMAL BMC INR RAL RC NMR DOPT HOFF HLEN HGR HN4 HINL SB LSRC SRC ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 96 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -80). set (blen := len - off) in *. set (n := gr_n (blen + inl)) in *.
  pose proof (gr_n_gt (blen + inl) ltac:(clear - HOFF HINL; subst blen; lia)) as HNGT. fold n in HNGT.
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 96) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BB 16 ART0 INBB ltac:(lia)) as BBHI. pose proof (proj2 (af_acc_live RT AF Σ m BB 16 ART0 INBB)) as ACCBB.
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m R 32 ART0 INR ltac:(lia)) as RHI. pose proof (proj2 (af_acc_live RT AF Σ m R 32 ART0 INR)) as ACCR.
  pose proof (live_ne_apart RT AF Σ m BI 128 BB 16 ART0 INBI INBB ltac:(intros E; injection E; lia)) as APIB.
  pose proof (live_ne_apart RT AF Σ m BI 128 R 32 ART0 INBI INR ltac:(intros E; injection E; lia)) as APIR.
  pose proof (live_ne_apart RT AF Σ m BI 128 BM 32 ART0 INBI INBM ltac:(intros E; injection E; lia)) as APIM.
  pose proof (live_ne_apart RT AF Σ m BM 32 R 32 ART0 INBM INR ltac:(intros E; injection E; exact NMR)) as APMR.
  pose proof (live_ne_apart RT AF Σ m BB 16 BM 32 ART0 INBB INBM ltac:(intros E; injection E; lia)) as APBM.
  pose proof (live_ne_apart RT AF Σ m BB 16 R 32 ART0 INBB INR ltac:(intros E; injection E; lia)) as APBR.
  (* [comment removed for export] *)
  assert (DRNG : 0 <= D /\ D + max <= lo /\ D <> BI /\ D <> BB /\ D <> BM /\ D <> R
                 /\ (D + max <= BI \/ BI + 128 <= D) /\ (D + max <= BB \/ BB + 16 <= D) /\ (D + max <= BM \/ BM + 32 <= D) /\ (D + max <= R \/ R + 32 <= D)
                 /\ (D + max <= 0x10000 \/ SEGTOP_A <= D)).
  { destruct DOPT as [(-> & -> & _ & _) | (IND & HM1 & NDBI & NDBB & NDBM & NDR)]; [clear - BI0 BB0 BM0 R0 HLOS; lia|].
    pose proof (af_live_range RT AF Σ m D max ART0 IND) as (D0 & DLO' & DR2).
    pose proof (live_ne_apart RT AF Σ m D max BI 128 ART0 IND INBI ltac:(intros E; injection E; intros _; exact NDBI)).
    pose proof (live_ne_apart RT AF Σ m D max BB 16 ART0 IND INBB ltac:(intros E; injection E; intros _; exact NDBB)).
    pose proof (live_ne_apart RT AF Σ m D max BM 32 ART0 IND INBM ltac:(intros E; injection E; intros _; exact NDBM)).
    pose proof (live_ne_apart RT AF Σ m D max R 32 ART0 IND INR ltac:(intros E; injection E; intros _; exact NDR)).
    clear - D0 DLO' DR2 LOW NDBI NDBB NDBM NDR H H0 H1 H2. lia. }
  destruct DRNG as (D0 & DLO & NDBI & NDBB & NDBM & NDR & APDI & APDB & APDM & APDR & DSEG).
  assert (INL0 : 0 < inl) by (clear - HINL; lia).
  destruct (src_facts Σ m IN inl [BI; BM; R; D] usp lo ART0 SRC ltac:(clear - HINL; lia) LOW HLOS) as (ACCIN & CLIN & INLO & INLOW & ACLIN & APIN & INCL).
  pose proof (APIN BI 128 INBI ltac:(left; reflexivity) INL0) as APNI. pose proof (APIN BM 32 INBM ltac:(right; left; reflexivity) INL0) as APNM.
  pose proof (APIN R 32 INR ltac:(do 2 right; left; reflexivity) INL0) as APNR.
  assert (APND : IN + inl <= D \/ D + max <= IN).
  { destruct DOPT as [(-> & -> & _) | (IND & _)]; [clear - INLOW; lia | exact (APIN D max IND ltac:(do 3 right; left; reflexivity) INL0)]. }
  clear APIN.
  assert (ACLIN' : forall x, IN <= x < IN + inl -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x) by (intros x Hx; replace x with (IN + (x - IN)) by (clear; lia); apply ACLIN; clear - Hx; lia).
  assert (COP : lo + RT_STACK <= usp1 /\ usp1 + 16 <= USTACK_TOP /\ usp1 mod 16 = 0).
  { fold usp in SPA. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|]. split; [unfold USTACK_TOP in *; clear - NUM; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 5). lia. }
  pose proof (bio_flags_byte1 m BI _ _ fl rrw numw padw _ ltac:(destruct FLOK; lia) BW) as FB1.
  unfold readp_cells in RC.
  (* [comment removed for export] *)
  pose proof (wr_s0_walk ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R IN inl fl blen rrw numw padw
                (Z_to_bv 64 (D + off)) rmaxw (Z_to_bv 64 0)
                HLO1 HLOS SPH ST UT SHC BW FLOK FB1 ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO RC ACCR R0 RAL RHI RLO APIB APIR INLOW
                ltac:(clear - INLO HLO1 SPH; lia) ltac:(clear - HINL HGR HN4 HNGT HOFF; subst blen; lia) ltac:(clear - HOFF HLEN D0 DLO HLO1 SPH; subst blen; lia) MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1 & BW1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 96) ART0 ltac:(clear - NUM; lia)); [| exact WM1].
    intros x Hx. apply MU1. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Hx; [apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hin; lia] | left; unfold USTACK_TOP in *; clear - Hin NUM; lia]. }
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 48 <= bv_unsigned x < BI + 52) -> m1 x = m x).
  { intros x Hx HnF. apply MU1. cbn [outside]. split; [clear - HnF; lia | split; [| exact I]]. destruct (cl_split RT AF Σ m usp 96 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Hx); clear - H; lia. }
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST1 (conj LOW COP))).
  assert (BBC1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m m1 _ _ BBC); [| exact WM1]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1; [apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia] | clear - Hx APIB; lia]. }
  assert (BMC1 : rw_cells asegs m1 BM (bufmem_cells len D max (Z_to_bv 64 0))).
  { apply (rw_cells_agree asegs m m1 _ _ BMC); [| exact WM1]. intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1; [apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia] | clear - Hx APIM; lia]. }
  assert (RC1 : rw_cells asegs m1 R [C8 (Z_to_bv 64 blen); C8 (Z_to_bv 64 (D + off)); C8 rmaxw; C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m m1 _ _ RC); [| exact WM1]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1; [apply (acl_live _ _ _ R 32); [exact INR | clear - Hx; lia] | clear - Hx APIR; lia]. }
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros x Hx; cbv beta in Hx; apply P1; [apply acl_stack; exact Hx | clear - Hx BILO HLO1; lia]).
  (* [comment removed for export] *)
  assert (K : forall c2, ASTA RT Σ PMc (fun ms => exists (v rmaxw' : word) (m' : mem),
              ret_st (Z_to_bv 64 SITE_wr_sync) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) sp (Z_to_bv 64 inl) (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 BI)
                     (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 blen) s9 s10 s11 v m' ms
              /\ rt_after RT Σ usp1 lo m1 m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp1 (SY_W BM R D max) m1 m'
              /\ rw_cells asegs m' BM (bufmem_cells blen D max (Z_to_bv 64 0)) /\ rw_cells asegs m' R (readp_cells blen D 0 rmaxw' (Z_to_bv 64 0))) c2 -> realizes asegs c2 T).
  2:{ destruct DOPT as [(ED & EM & EL & EO) | (IND & HM1 & _)].
      - assert (EB : blen = 0) by (subst blen; clear - EL EO; lia). rewrite ED, EM in BMC1. rewrite EB, ED, EO, Z.add_0_r in RC1. unfold bufmem_cells in BMC1.
        apply (C_SS Σ PMc (Z_to_bv 64 SITE_wr_sync) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 inl) (Z_to_bv 64 BI) (Z_to_bv 64 0) (Z_to_bv 64 fl) (Z_to_bv 64 ((BI + 48) ≫ 3))
                 a4 a5 a6 a7 (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 BI) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 blen)
                 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo BI 128 BB BM R (fl - fl mod 16) 1 (Z_to_bv 64 1) rrw numw padw (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) rmaxw (Z_to_bv 64 0)
                 FDO MST eq_refl eq_refl INBI ltac:(clear; lia) BIAL BW1 ltac:(clear; lia) INBB BBAL BBC1 INBM BMAL BMC1 INR RAL RC1 ART1 MI1 CO1
                 ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia) T c1 Hc1').
        intros c2 Hc2. apply K. eapply ASTA_conseq; [exact Hc2|]. intros ms (v & m' & RS & AFT & PRES). rewrite EU1 in AFT, PRES. exists v, rmaxw, m'.
        split; [exact RS|]. split; [exact AFT|]. split; [exact (pres_fp_of_pres _ _ _ _ _ _ PRES)|].
        rewrite EB, ED, EM. unfold bufmem_cells, readp_cells. rewrite EL in BMC1. rewrite Z.sub_0_r, Z.add_0_r.
        pose proof (proj1 (proj2 (proj2 AFT))) as WM'.
        split; [apply (rw_cells_agree asegs m1 m' _ _ BMC1); [| exact WM'] | apply (rw_cells_agree asegs m1 m' _ _ RC1); [| exact WM']];
          intros x Hx; cbv beta in Hx; cbn [cells_size csize Nat.add] in Hx; apply PRES;
          [apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia] | apply (acl_live _ _ _ R 32); [exact INR | clear - Hx; lia]].
      - destruct (live_CB RT AF Σ m1 D max ART1 IND ltac:(clear - HM1; lia)) as (junk & LJ & DC1).
        apply (C_SY Σ PMc (Z_to_bv 64 SITE_wr_sync) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 inl) (Z_to_bv 64 BI) (Z_to_bv 64 0) (Z_to_bv 64 fl) (Z_to_bv 64 ((BI + 48) ≫ 3))
                 a4 a5 a6 a7 (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 BI) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 blen)
                 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo BI 128 BB BM R D len max off (fl - fl mod 16) 1 (Z_to_bv 64 1) rrw numw padw rmaxw (Z_to_bv 64 0) junk
                 FDO MST eq_refl eq_refl INBI ltac:(clear; lia) BIAL BW1 ltac:(clear; lia) INBB BBAL BBC1 INBM BMAL BMC1 INR RAL ltac:(unfold readp_cells; fold blen; exact RC1) NMR IND NDBB NDBM NDR HOFF
                 HLEN ltac:(clear - HM1 HGR HLEN HOFF HINL HN4 HNGT; subst blen; lia) LJ DC1 ART1 MI1 CO1 ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia) T c1 Hc1').
        intros c2 Hc2. apply K. eapply ASTA_conseq; [exact Hc2|]. intros ms (v & w & m' & RS & AFT & PRES & B1 & B2 & _). rewrite EU1 in AFT, PRES. exists v, w, m'.
        unfold blen. exact (conj RS (conj AFT (conj PRES (conj B1 B2)))). }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (v2 & rmaxw2 & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BMC2 & RC2) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite (ret_pc_even SITE_wr_sync) in Hc2' by (unfold SITE_wr_sync; lia).
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 48 <= bv_unsigned x < BI + 52) -> outside (SY_W BM R D max) (bv_unsigned x) -> m2 x = m x).
  { intros x Hx HnF Ho. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) Ho). exact (P1 x Hx HnF). }
  assert (BBC2 : rw_cells asegs m2 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m1 m2 _ _ BBC1); [| exact WM2]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES2; [apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia] | unfold SY_W; cbn [outside]; clear - Hx APBM APBR APDB; lia]. }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & SHC2 & _ & _ & UT2). pose proof (proj2 (af_acc_live RT AF Σ m2 BB 16 ART2 INBB)) as ACCBB2.
  assert (CO2 : call_ok RT Σ m2 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST2 (conj LOW COP))).
  (* [comment removed for export] *)
  pose proof (wr_s1_walk sp gp y0 y1 y2 v2 h1 h2 h3 h4 h5 h6 h7 s9 s10 s11 y3 y4 y5 y6 (Z_to_bv 64 BI) F2 fc2 m2 BB BM R IN inl blen SPH UT2 SHC2 BBC2 ACCBB2 BB0 BBAL BBHI
                ltac:(clear - BBLO HLO1 SPH; lia) ltac:(clear - HOFF; subst blen; lia) ltac:(clear - HINL; lia) ltac:(clear - HGR HN4 HNGT HOFF HINL; subst blen; lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  assert (AG02 : agree_on (fun x => usp <= x < USTACK_TOP) m m2).
  { intros x Hx. cbv beta in Hx. apply P2; [apply acl_stack; exact Hx | clear - Hx BILO HLO1; lia | unfold SY_W; cbn [outside]; clear - Hx BMLO RLO DLO HLO1; lia]. }
  assert (FRR2 : rw_cells asegs m2 (usp - 16) [C8 s0; C8 ra]).
  { assert (FR2 : rw_cells asegs m2 usp1 (wr_frame s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold wr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
      apply PRES2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | unfold SY_W; cbn [outside]; unfold usp1 in Hx; clear - Hx BMLO RLO DLO HLO1; lia]. }
    unfold wr_frame in FR2. replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m2 usp1 [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR2). }
  destruct (cl_chain_call (rt_cg RT Σ) e_mem_write e_BUF_MEM_grow_clean SITE_wr_grow m m2 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG02 FRR2 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX2 & UWC2).
  assert (CLE2 : cl_env m2 lb canary).
  { apply (cl_env_agree m1 m2 lb canary CLE1). intros x Hx. apply PRES2; [right; left; exact (cl_cell_static _ Hx) | unfold SY_W; cbn [outside]; pose proof (client_static_range _ (cl_cell_static _ Hx)); unfold SEGTOP_A in *; clear - H BMHI RHI DSEG; lia]. }
  assert (ND : forall x, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp x -> ~ (D <= x < D + max)).
  { intros x Hx. destruct DOPT as [(_ & -> & _) | (IND & _)]; [clear; lia | exact (removed_apart RT AF Σ m D max usp x ART0 IND ltac:(clear - NUM; lia) Hx)]. }
  assert (P2R : forall x : word, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 48 <= bv_unsigned x < BI + 52) ->
                ~ (BM <= bv_unsigned x < BM + 24) -> ~ (R <= bv_unsigned x < R + 32) -> m2 x = m x).
  { intros x Hx HnF HnM HnR. pose proof (aclient_mono _ _ _ (rt_live RT Σ) (rt_frames RT Σ) usp _ Hx ltac:(intros e He; exact (live_remove_sub _ _ _ He)) ltac:(auto) ltac:(clear; lia)) as Hx'.
    apply P2; [exact Hx' | exact HnF | unfold SY_W; cbn [outside]; pose proof (ND _ Hx); clear - H HnM HnR; lia]. }
  clear P2.
  apply (C_GR Σ PMc (Z_to_bv 64 SITE_wr_grow) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) y0 y1 y2 sp (Z_to_bv 64 inl) (Z_to_bv 64 BM) (Z_to_bv 64 (blen + inl)) h2 h3 h4 h5 h6 h7
           (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 blen)
           s9 s10 s11 y3 y4 y5 y6 F2 fc2 m2 lo BM D blen max (blen + inl) (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl eq_refl INBM BMAL BMC2).
  { destruct DOPT as [(ED & EM & _) | (IND & HM1 & _)]; [left; exact (conj ED EM) | right; exact (conj IND (conj HM1 NDBM))]. }
  { clear - HOFF HLEN; subst blen; lia. } { clear - HGR; subst blen; lia. } { exact HN4. } { exact ART2. } { exact MI2. } { exact CO2. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_wr_grow) by (unfold SITE_wr_grow; lia). exact CTX2. }
  { exact UWC2. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; right; exact Hx. }
  { exact Hlen. } { exact Hcr. } { exact CLE2. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ1 & q & Hc4 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4 & CLE4 & BMC4) & Hc4'). clear Hc4.
  destruct RS4 as (z0 & z1 & z2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & z3 & z4 & z5 & z6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_wr_grow) in Hc4' by (unfold SITE_wr_grow; lia). fold n in LV1, CR1, QU, BMC4.
  assert (INBB1 : In (BB, 16) (rt_live RT Σ1)) by (rewrite LV1; right; apply live_remove_keep; [exact INBB | cbn [fst]; clear - NDBB; lia]).
  assert (INBI1 : In (BI, 128) (rt_live RT Σ1)) by (rewrite LV1; right; apply live_remove_keep; [exact INBI | cbn [fst]; clear - NDBI; lia]).
  assert (INBM1 : In (BM, 32) (rt_live RT Σ1)) by (rewrite LV1; right; apply live_remove_keep; [exact INBM | cbn [fst]; clear - NDBM; lia]).
  assert (INR1 : In (R, 32) (rt_live RT Σ1)) by (rewrite LV1; right; apply live_remove_keep; [exact INR | cbn [fst]; clear - NDR; lia]).
  assert (INQ : In (q, n) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (NQ : forall x, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp x -> ~ (q <= x < q + n)).
  { intros x Hx. rewrite <- FRS1 in Hx. exact (fresh_apart RT AF Σ1 m4 q n _ usp x ART4 LV1 ltac:(rewrite SP1; clear - NUM; lia) ltac:(clear - HNGT HOFF HINL; subst blen; lia) Hx). }
  pose proof (af_live_disj RT AF Σ1 m4 q n BM 32 [] _ ART4 LV1 ltac:(apply live_remove_keep; [exact INBM | cbn [fst]; clear - NDBM; lia])) as DQM.
  pose proof (af_live_disj RT AF Σ1 m4 q n BB 16 [] _ ART4 LV1 ltac:(apply live_remove_keep; [exact INBB | cbn [fst]; clear - NDBB; lia])) as DQB.
  pose proof (af_live_disj RT AF Σ1 m4 q n R 32 [] _ ART4 LV1 ltac:(apply live_remove_keep; [exact INR | cbn [fst]; clear - NDR; lia])) as DQR.
  pose proof (af_live_disj RT AF Σ1 m4 q n BI 128 [] _ ART4 LV1 ltac:(apply live_remove_keep; [exact INBI | cbn [fst]; clear - NDBI; lia])) as DQI.
  assert (P4 : forall x : word, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 48 <= bv_unsigned x < BI + 52) ->
               ~ (BM <= bv_unsigned x < BM + 24) -> ~ (R <= bv_unsigned x < R + 32) -> bv_unsigned x <> G_ALLOW_CUST -> m4 x = m x).
  { intros x Hx HnF HnM HnR HnL. rewrite (PRES4 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) ltac:(unfold GR_W; cbn [outside]; clear - HnM HnL; lia)).
    exact (P2R x Hx HnF HnM HnR). }
  assert (BBC4 : rw_cells asegs m4 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree_nw asegs m2 m4 _ _ BBC2). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES4; [apply (acl_live _ _ _ BB 16); [apply live_remove_keep; [exact INBB | cbn [fst]; clear - NDBB; lia] | clear - Hx; lia] | unfold GR_W, G_ALLOW_CUST; cbn [outside]; clear - Hx APBM BBHI; lia]. }
  destruct (af_client_consts RT AF Σ1 m4 ART4) as (_ & SHC4 & _ & _ & UT4). pose proof (proj2 (af_acc_live RT AF Σ1 m4 BB 16 ART4 INBB1)) as ACCBB4.
  pose proof (proj2 (af_acc_live RT AF Σ1 m4 BM 32 ART4 INBM1)) as ACCBM4.
  assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
  assert (CO4 : call_ok RT Σ1 m4 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST4 (conj LOW1 COP))).
  (* [comment removed for export] *)
  unfold bufmem_cells in BMC4.
  pose proof (wr_s2_walk sp gp z0 z1 z2 k1 k2 k3 k4 k5 k6 k7 s9 s10 s11 z3 z4 z5 z6 F4 fc4 m4 BB BM R q IN inl blen (blen + inl) (Z_to_bv 64 (blen + inl)) (Z_to_bv 64 n) (Z_to_bv 64 0)
                SPH UT4 SHC4 BBC4 ACCBB4 BB0 BBAL BBHI ltac:(clear - BBLO HLO1 SPH; lia) BMC4 ACCBM4 BM0 BMAL BMHI ltac:(clear - BMLO HLO1 SPH; lia)
                ltac:(clear - HINL HGR HN4 HNGT HOFF; subst blen; lia) ltac:(clear - Q0; lia) ltac:(unfold USTACK_TOP in QU; clear - QU HNGT HINL HOFF; subst blen; lia) ltac:(clear - HOFF; subst blen; lia) MI4) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5.
  (* [comment removed for export] *)
  assert (SRC1 : src_blk (rt_live RT Σ1) IN inl [BI; BM; R; D]).
  { destruct SRC as [S0 | (p & k & Hin & L & H & NE)]; [left; exact S0 | right]. exists p, k. split; [| exact (conj L (conj H NE))].
    rewrite LV1. right. apply live_remove_keep; [exact Hin | cbn [fst]]. intros ->. apply NE. do 3 right; left; reflexivity. }
  assert (ACLR : forall x, IN <= x < IN + inl -> aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp x).
  { intros x Hx. destruct SRC as [S0 | (p & k & Hin & L & H & NE)]; [apply acl_static; apply client_static_intro; right; left; clear - S0 Hx; lia|].
    apply (acl_live _ _ _ p k); [apply live_remove_keep; [exact Hin | cbn [fst]; intros ->; apply NE; do 3 right; left; reflexivity] | clear - L H Hx; lia]. }
  destruct (src_facts Σ1 m4 IN inl [BI; BM; R; D] usp lo ART4 SRC1 ltac:(clear - HINL; lia) LOW1 HLOS) as (ACCIN4 & CLIN4 & _).
  assert (SB4 : bytes_at asegs m4 IN src).
  { apply (bytes_at_agree asegs m m4 _ _ SB). intros x Hx. cbv beta in Hx. rewrite LSRC in Hx.
    apply P4; [apply ACLR; exact Hx | clear - Hx APNI; lia | clear - Hx APNM; lia | clear - Hx APNR; lia | unfold G_ALLOW_CUST; clear - Hx INCL; lia]. }
  assert (APQ : q + blen + inl <= IN \/ IN + inl <= q + blen).
  { destruct (Z.le_gt_cases (IN + inl) q) as [|H1]; [right; clear - H HOFF; subst blen; lia|]. destruct (Z.le_gt_cases (q + n) IN) as [|H2]; [left; clear - H HNGT; lia|].
    exfalso. apply (NQ (Z.max IN q)); [apply ACLR; clear - H1 INL0; lia | clear - H1 H2 HNGT HINL HOFF; subst blen; lia]. }
  apply (MCP Σ1 PMc (Z_to_bv 64 SITE_wr_cpy1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) z0 z1 z2 sp (Z_to_bv 64 inl) (Z_to_bv 64 (q + blen)) (Z_to_bv 64 IN) (Z_to_bv 64 inl) k3 k4 k5 k6 k7
           (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 blen)
           s9 s10 s11 z3 z4 z5 z6 F4 fc4 m4 (q + blen) IN src lo FDO MST eq_refl eq_refl ltac:(rewrite LSRC; reflexivity)
           ltac:(unfold USTACK_TOP in QU; clear - Q0 QU HNGT HINL HOFF; subst blen; lia) ltac:(clear - INLOW INLO HLO1 SPH HINL; lia) ltac:(rewrite LSRC; clear - HINL HGR HN4 HNGT HOFF; lia) SB4).
  { rewrite LSRC. split; [intros _; exact (conj ACCIN4 CLIN4) | left; exact INLO]. }
  { rewrite LSRC. exact (live_checked_dst RT AF Σ1 m4 _ q n (q + blen) inl ART4 INQ ltac:(clear - HOFF; subst blen; lia) ltac:(clear - HNGT; lia) ltac:(clear - HINL; lia)). }
  { rewrite LSRC. exact APQ. }
  { exact ART4. } { exact MI4. } { exact CO4. }
  { exact Hc5'. }
  clear Hc5'. intros c6 Hc6.
  destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & _) & Hc6'). clear Hc6.
  destruct RS6 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite LSRC in PRES6. rewrite (ret_pc_even SITE_wr_cpy1) in Hc6' by (unfold SITE_wr_cpy1; lia).
  assert (P6 : forall x : word, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 48 <= bv_unsigned x < BI + 52) ->
               ~ (BM <= bv_unsigned x < BM + 24) -> ~ (R <= bv_unsigned x < R + 32) -> bv_unsigned x <> G_ALLOW_CUST -> m6 x = m x).
  { intros x Hx HnF HnM HnR HnL. rewrite (PRES6 x ltac:(rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; right; exact He | auto | unfold usp1; clear; lia]) ltac:(pose proof (NQ _ Hx); clear - H HNGT HOFF HINL; subst blen; lia)).
    exact (P4 x Hx HnF HnM HnR HnL). }
  assert (BBC6 : rw_cells asegs m6 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m4 m6 _ _ BBC4); [| exact WM6]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES6; [apply (acl_live _ _ _ BB 16); [exact INBB1 | clear - Hx; lia] | clear - Hx DQB HNGT HOFF HINL; subst blen; lia]. }
  assert (BMC6 : rw_cells asegs m6 BM (bufmem_cells (blen + inl) q n (Z_to_bv 64 0))).
  { unfold bufmem_cells. apply (rw_cells_agree asegs m4 m6 _ _ BMC4); [| exact WM6]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES6; [apply (acl_live _ _ _ BM 32); [exact INBM1 | clear - Hx; lia] | clear - Hx DQM HNGT HOFF HINL; subst blen; lia]. }
  destruct (af_client_consts RT AF Σ1 m6 ART6) as (_ & SHC6 & _ & _ & UT6). pose proof (proj2 (af_acc_live RT AF Σ1 m6 BB 16 ART6 INBB1)) as ACCBB6.
  assert (CO6 : call_ok RT Σ1 m6 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST6 (conj LOW1 COP))).
  (* [comment removed for export] *)
  pose proof (wr_s3_walk sp gp w0 w1 w2 (Z_to_bv 64 (q + blen)) g1 g2 g3 g4 g5 g6 g7 s9 s10 s11 w3 w4 w5 w6 F6 fc6 m6 BB BM R IN inl blen SPH UT6 SHC6 BBC6 ACCBB6 BB0 BBAL BBHI
                ltac:(clear - BBLO HLO1 SPH; lia) ltac:(clear - BM0 BMLO HLO1 SPH; lia) ltac:(clear - R0 RLO HLO1 SPH; lia) MI6) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ1 _ _ c7 Hc7) as (ms7 & -> & Hc7'). clear Hc7.
  (* [comment removed for export] *)
  apply (MCP Σ1 PMc (Z_to_bv 64 SITE_wr_cpy2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 inl) (Z_to_bv 64 R) (Z_to_bv 64 BM) (Z_to_bv 64 32) g3 g4 g5 g6 g7
           (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 blen)
           s9 s10 s11 w3 w4 w5 w6 F6 fc6 m6 R BM (bufmem_bytes (blen + inl) q n (Z_to_bv 64 0)) lo FDO MST eq_refl eq_refl ltac:(rewrite bufmem_bytes_length; reflexivity)
           ltac:(clear - R0 RLO HLO1 SPH; lia) ltac:(clear - BM0 BMLO HLO1 SPH; lia) ltac:(rewrite bufmem_bytes_length; clear; lia) (proj2 (proj1 BMC6))).
  { rewrite bufmem_bytes_length. exact (live_checked_src RT AF Σ1 m6 _ lo BM 32 BM 32 ART6 INBM1 ltac:(clear; lia) ltac:(clear; lia) LOW1). }
  { rewrite bufmem_bytes_length. exact (live_checked_dst RT AF Σ1 m6 _ R 32 R 32 ART6 INR1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)). }
  { rewrite bufmem_bytes_length. clear - APMR. lia. }
  { exact ART6. } { exact MI6. } { exact CO6. }
  { exact Hc7'. }
  clear Hc7'. intros c8 Hc8.
  destruct (ASTA_unpack RT Σ1 _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & CP8) & Hc8'). clear Hc8.
  destruct RS8 as (x0 & x1 & x2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & F8 & fc8 & ->).
  rewrite EU1 in ST8, PRES8. rewrite bufmem_bytes_length in PRES8. change (Z.of_nat 32) with 32 in PRES8. rewrite (ret_pc_even SITE_wr_cpy2) in Hc8' by (unfold SITE_wr_cpy2; lia).
  assert (P8 : forall x : word, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp (bv_unsigned x) -> outside (WRG_W BI BM R) (bv_unsigned x) -> m8 x = m x).
  { intros x Hx Ho. unfold WRG_W, G_ALLOW_CUST in Ho. cbn [outside] in Ho.
    rewrite (PRES8 x ltac:(rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; right; exact He | auto | unfold usp1; clear; lia]) ltac:(clear - Ho; lia)).
    apply P6; [exact Hx | clear - Ho; lia | clear - Ho; lia | clear - Ho; lia | unfold G_ALLOW_CUST; clear - Ho; lia]. }
  pose proof (af_live_range RT AF Σ1 m4 q n ART4 INQ) as (_ & QLO' & _). assert (QLO : q + n <= lo) by (clear - QLO' LOW1; lia). clear QLO'.
  assert (AGS : forall x : word, usp1 <= bv_unsigned x < usp -> m8 x = m1 x).
  { intros x Hx. assert (HAx : forall live frames, aclient live frames usp1 (bv_unsigned x)) by (intros; left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia).
    rewrite (PRES8 x (HAx _ _) ltac:(unfold usp1, RT_STACK in *; clear - Hx RLO HSTK; lia)).
    rewrite (PRES6 x (HAx _ _) ltac:(unfold usp1, RT_STACK in *; clear - Hx QLO HSTK HOFF HNGT HINL; subst blen; lia)).
    rewrite (PRES4 x (HAx _ _) ltac:(unfold GR_W, G_ALLOW_CUST; cbn [outside]; unfold usp1, RT_STACK in *; clear - Hx BMLO HSTK HLOS; lia)).
    apply (PRES2 x (HAx _ _)). unfold SY_W. cbn [outside]. unfold usp1, RT_STACK in *; clear - Hx DLO BMLO RLO HSTK; lia. }
  assert (FR8 : rw_cells asegs m8 usp1 (wr_frame s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m1 m8 _ _ FR1). intros x Hx. cbv beta in Hx. unfold wr_frame in Hx. cbn [cells_size csize Nat.add] in Hx. apply AGS. unfold usp1 in *. clear - Hx. lia. }
  destruct (af_client_consts RT AF Σ1 m8 ART8) as (_ & _ & _ & _ & UT8).
  (* [comment removed for export] *)
  pose proof (wr_s4_walk ra sp gp x0 x1 x2 s0 s1 (Z_to_bv 64 R) e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6
                (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 blen)
                F8 fc8 m8 inl lo ltac:(clear - HLO1; lia) SPH ST8 UT8 FR8 ltac:(clear - HINL HGR HN4 HNGT HOFF; lia) MI8) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc8' c9 Hc9.
  apply Hk. exists Σ1, q. split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 (conj Q0 (conj Q16 (conj QU CG1)))))))].
  eapply ASTA_conseq; [exact Hc9|]. intros ms (q0 & q1 & q2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & q3 & q4 & q5 & q6 & m9 & -> & MU9 & WM9 & MI9 & ST9).
  fold usp in ST9. exists m9. split; [do 16 eexists; reflexivity|].
  assert (E9 : forall x : word, m9 x = m8 x) by (intros x; apply MU9; exact I).
  assert (ART9 : ART RT Σ1 m9) by (apply (af_frame RT AF Σ1 m8 m9 usp1 ART8 ltac:(rewrite SP1; unfold usp1; clear - NUM; lia)); [intros x _; apply E9 | exact WM9]).
  split; [exact (conj ART9 (conj MI9 ST9))|].
  split; [intros x Hx Ho; rewrite E9; exact (P8 x Hx Ho)|].
  split.
  { apply (cl_env_agree m4 m9 _ canary CLE4). intros x Hx. pose proof (cl_cell_static _ Hx) as CSx. pose proof (client_static_range _ CSx) as Rx. rewrite E9.
    rewrite (PRES8 x ltac:(right; left; exact CSx) ltac:(unfold SEGTOP_A in Rx; clear - Rx RHI; lia)).
    apply PRES6; [right; left; exact CSx|]. pose proof (NQ _ (acl_static _ _ usp _ CSx)). clear - H HNGT HOFF HINL. subst blen. lia. }
  split.
  { apply (rw_cells_agree_nw asegs m1 m9 _ _ BW1). intros x Hx. cbv beta in Hx. unfold bio_w1_cells in Hx. cbn [cells_size csize Nat.add] in Hx. rewrite E9.
    rewrite (PRES8 x ltac:(apply (acl_live _ _ _ BI 128); [exact INBI1 | clear - Hx; lia]) ltac:(clear - Hx APIR; lia)).
    rewrite (PRES6 x ltac:(apply (acl_live _ _ _ BI 128); [exact INBI1 | clear - Hx; lia]) ltac:(clear - Hx DQI HNGT HOFF HINL; subst blen; lia)).
    rewrite (PRES4 x ltac:(apply (acl_live _ _ _ BI 128); [apply live_remove_keep; [exact INBI | cbn [fst]; clear - NDBI; lia] | clear - Hx; lia]) ltac:(unfold GR_W, G_ALLOW_CUST; cbn [outside]; clear - Hx APIM BIHI; lia)).
    apply (PRES2 x ltac:(apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx; lia])). unfold SY_W. cbn [outside]. clear - Hx APIM APIR APDI. lia. }
  split.
  { apply (rw_cells_agree asegs m6 m9 _ _ BMC6); [| exact (wmono_trans asegs _ _ _ WM8 WM9)].
    intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx. rewrite E9.
    apply PRES8; [apply (acl_live _ _ _ BM 32); [exact INBM1 | clear - Hx; lia] | clear - Hx APMR; lia]. }
  replace (readp_cells (blen + inl) q 0 (Z_to_bv 64 n) (Z_to_bv 64 0)) with (bufmem_cells (blen + inl) q n (Z_to_bv 64 0)) by (unfold readp_cells, bufmem_cells; rewrite Z.sub_0_r, Z.add_0_r; reflexivity).
  apply bufmem_cells_of_bytes; [apply (bytes_at_agree asegs m8 m9 _ _ CP8); intros x _; apply E9|].
  exact (wr_at_wm m8 m9 _ _ (proj1 (af_acc_live RT AF Σ1 m8 R 32 ART8 INR1)) WM9).
Qed.
End CWr.
