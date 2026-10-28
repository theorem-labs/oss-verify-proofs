(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib
  ECH_ALibMF ECH_Iface ECH_AStmt_C1 ECH_AC1_zalloc ECH_AC1_free ECH_AC1_malloc ECH_AC1_dup ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C7 ECH_AStmt_C13 ECH_AKit ECH_AKitSeg ECH_AsKit
  ECH_AC7_kit ECH_AC7_rd ECH_AC7_rd2 ECH_AC7_bioread ECH_ARostr ECH_ALibMid ECH_AC11_fail ECH_AC14_bio2buf_seg ECH_AC14_ladder_seg ECH_AC14_ladloop ECH_AC14_fmt_seg ECH_AC14_flat_seg ECH_AStmt_C14
  F_strspn N6_strspn ECH_AC14_b2b.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition S_B64A : list byte := Eval vm_compute in img_cstr AA_B64_ALPHABET 80.
Definition K_B64A : list byte := Eval vm_compute in img_slack AA_B64_ALPHABET (length S_B64A).
Section RO.
  Context {HCEIL : HeapCeil}.
  Lemma R_B64A : AROSTR AA_B64_ALPHABET S_B64A K_B64A.
  Proof. eapply AROSTR_intro; [apply ROSTR_of_image; vm_compute; reflexivity| unfold aglobals; cbn; tauto| vm_compute; intros X; discriminate X| vm_compute; intros X; discriminate X]. Qed.
  Lemma S_B64A_len : length S_B64A = 66%nat. Proof. reflexivity. Qed.
End RO.

(* [comment removed for export] *)
Lemma nul_split : forall (ds : list byte), exists str rest,
  ds ++ [Z_to_bv 8 0] = str ++ Z_to_bv 8 0 :: rest /\ ~ In (Z_to_bv 8 0) str /\ (length str <= length ds)%nat /\ (length str = length ds -> str = ds).
Proof.
  induction ds as [|b ds IH].
  - exists [], []. cbn. repeat split; auto.
  - destruct IH as (str & rest & E & NI & LE & EQ).
    destruct (Z.eq_dec (bv_unsigned b) 0) as [Z0|NZ].
    + assert (Hb : b = Z_to_bv 8 0) by (apply bv_eq; rewrite Z0; reflexivity).
      exists [], (ds ++ [Z_to_bv 8 0]). subst b. cbn. repeat split; [tauto| lia| intros K; exfalso; lia].
    + exists (b :: str), rest. cbn. rewrite E. repeat split.
      * intros [K|K]; [| exact (NI K)]. apply NZ. rewrite K. reflexivity.
      * lia.
      * intros K. f_equal. apply EQ. lia.
Qed.

(* [comment removed for export] *)
Section RC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  Hypothesis RAISE : araise_stmt H.
  Hypothesis SPN : strspn_icpt_stmt.
  Let HH : asan_rt_hyps H := proj1 HX.
  Let SM6 : stack_malloc_6_stmt H := proj1 (proj2 (proj2 (proj2 (proj2 HX)))).
  Let SF6 : stack_free_6_stmt H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).
  Let SSF8 : set_shadow_f8_stmt := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))))).
  Let PERM : rheap_perm H := HHx_rheap_perm H HX.

  (* [comment removed for export] *)
  Variables (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LIB LB : list block) (LF : list fframe)
            (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word) (CH : list (Z * Z)).
  Hypotheses (VIS0 : as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                         F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom asegs))
             (A0 : a0 = Z_to_bv 64 st) (A1 : a1 = Z_to_bv 64 mb)
             (SO : STOREobj LB m st S) (SE : es_entries S = 0) (SEO : es_entries_o S = None) (STL : st + STORE_SIZE <= lo) (SSH : STORE_shad m st S)
             (MBO : MEMBIO H LB m mb R) (MP0 : mb_pos R = 0) (MN0 : mb_nread R = 0) (MBB : MEMBIO_below mb R lo) (MBS : MEMBIO_sep mb R)
             (MSH : MEMBIO_shad m mb R) (PAY : PAYLOAD_shad m R)
             (DS : bytes_at asegs m (mb_buf R) ds) (DSL : zlength ds = mb_len R)
             (PAYL : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD)
             (PAYL2 : 1 <= mb_len R -> forall pD, In (pD, mb_buf R, mb_len R) LB -> pD <> es_id S)
             (NDsm : List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)))
             (LM : LIBMID LIB m M) (SUBL : forall b, In b LIB -> In b LB) (CTX : mid_ctx M = CtxReady x) (MF1 : mid_flag M = 1)
             (DJ6 : forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b')
             (HP : as_RHEAP H s (mid_errblocks M ++ LB) m) (KREL : as_AKREL H s (mkCfg msF mo))
             (BUD : lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= as_LIVE_MAX H)
             (BUDC : Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= as_LIVE_CNT_MAX H)
             (AUX : as_rauxv_ok H m B) (SPB : bv_unsigned sp <= B) (BHI : B < 2^64) (SPA : bv_unsigned sp mod 16 = 0)
             (ST : stk asegs m lo (bv_unsigned sp)) (CEIL : aceil <= lo) (LO : lo <= bv_unsigned sp - READCFG_STACK M) (ST0 : stack0 m lo (bv_unsigned sp))
             (ERR : rw_cells asegs m (errno_addr tp) [C4 errv]) (MI : mem_inv asegs m) (TP : tp = Z_to_bv 64 ATP) (AC : ACONST m)
             (MCO : mid_closed_ok H M)
             (RFS : as_RFS H LF m) (LFB : (length LF + READCFG_LF <= READCFG_MAXLIVE)%nat) (ATH : athr_cells m)
             (CHN : as_chain H m (bv_unsigned s0) CH) (CHB : forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp')
             (PF : pf_ok (as_TR H) (PF_readcfg PF9new PF9free M) (bv_unsigned ra) CH) (ALW : READCFG_COST H M <= as_AL H s)
             (RAE : bv_unsigned ra mod 2 = 0).

  (* [comment removed for export] *)
  Local Notation L0c := (L0 LB M).
  Local Notation S1c := (S1 sp).
  Local Notation KGc := (KG sp).
  Local Notation POSTc := (POST H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds).
  Local Notation XFc := (XF M st mb R).
  Local Notation SAVESc := (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Local Notation CH1c := (CH1 ra sp CH).
  Local Notation LF1c := (LF1 LF).
  Local Notation XSFc := (XSF H).
  Local Notation LEDGERc := (LEDGER H s).
  Local Notation pf_sitec := (pf_site H PF9new PF9free ra sp M CH PF).
  Local Notation rp_okKc := (rp_okK H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH).
  (* [comment removed for export] *)
  Local Notation "'RCI' f" := (f H HX RAISE PF9new PF9free ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LIB LB LF M x st mb lo B S R ds errv CH
                                 VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE)
    (at level 10, f at level 0).

  Local Ltac img_static := unfold A_malloc_impl, A_realloc_impl, A_free_impl, A_got_CRYPTO_malloc, A_mem_buf_method, O_METH_BREAD, A_mem_inited; cbn; lia.

  (* [comment removed for export] *)
  Lemma rc_facts_c :
       S = store_empty (es_id S) /\ In (es_id S, st, STORE_SIZE) L0c /\ ablock_range H st STORE_SIZE
    /\ (forall b, In b L0c -> ablock_range H (blk_addr b) (blk_size b)) /\ (forall b, In b LB -> In b L0c)
    /\ List.NoDup (map blk_id L0c) /\ 9152 <= READCFG_STACK M /\ 0 <= lo /\ MEMFLAG m 1
    /\ (forall b', In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> In b' L0c)
    /\ (forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) ->
          blk_addr b + blk_size b + 16 <= blk_addr b' \/ blk_addr b' + blk_size b' + 16 <= blk_addr b)
    /\ afsb_ok H /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
    /\ rp_s1 (bv_unsigned sp) mod 32 = 0 /\ bv_unsigned sp - 464 <= rp_s1 (bv_unsigned sp) <= bv_unsigned sp - 448 /\ bv_unsigned sp < 2^64.
  Proof. exact (RCI rc_facts). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bw_carry : forall (W : list (Z * Z)) (mA mB : mem) (sq : as_St H) (Lq : list block) (pc : bptr) (Cp nc : Z),
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= S1c) \/ (Cp <= fst iv /\ snd iv <= Cp + nc)) W ->
    munch W mA mB -> wmono asegs mA mB ->
    as_RHEAP H sq ((pc, Cp, nc) :: Lq) mA -> (forall b, In b LB -> In b Lq) ->
       as_RHEAP H sq ((pc, Cp, nc) :: Lq) mB
    /\ (as_rauxv_ok H mA B -> as_rauxv_ok H mB B)
    /\ (forall LFq, as_RFS H LFq mA -> as_RFS H LFq mB)
    /\ (forall LIBq Mq xq, LIBMID LIBq mA Mq -> mid_ctx Mq = CtxReady xq -> (forall b, In b LIBq -> In b Lq) -> (forall b, In b (mid_errblocks Mq) -> In b Lq) -> LIBMID LIBq mB Mq)
    /\ (forall A cs, rw_cells asegs mA A cs -> S1c <= A -> rw_cells asegs mB A cs)
    /\ (forall A cs, as_FSB H <= A -> A + Z.of_nat (cells_size cs) <= as_FSB H + AFS_SIZE -> rw_cells asegs mA A cs -> rw_cells asegs mB A cs)
    /\ (forall A cs, sh AIMG_TOP <= A -> A + Z.of_nat (cells_size cs) <= sh aceil -> rw_cells asegs mA A cs -> rw_cells asegs mB A cs)
    /\ (forall b A cs, In b Lq -> blk_addr b <= A -> A + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b -> rw_cells asegs mA A cs -> rw_cells asegs mB A cs)
    /\ (forall b A bs, In b Lq -> blk_addr b <= A -> A + Z.of_nat (length bs) <= blk_addr b + blk_size b -> bytes_at asegs mA A bs -> bytes_at asegs mB A bs)
    /\ (forall b A n, In b ((pc, Cp, nc) :: Lq) -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> addressable mA A n -> addressable mB A n)
    /\ (forall b A n, In b ((pc, Cp, nc) :: Lq) -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> accessible mA A n -> accessible mB A n)
    /\ (forall errvq, rw_cells asegs mA (errno_addr (Z_to_bv 64 ATP)) [C4 errvq] -> rw_cells asegs mB (errno_addr (Z_to_bv 64 ATP)) [C4 errvq])
    /\ (stack0 mA lo (bv_unsigned sp) -> stack0 mB lo (bv_unsigned sp))
    /\ (ACONST mA -> ACONST mB)
    /\ (forall cur CHq, as_chain H mA cur CHq -> (forall fpq raq, In (fpq, raq) CHq -> S1c + 16 <= fpq) -> as_chain H mB cur CHq)
    /\ (forall X m0, xpres H LB (bv_unsigned sp) X m0 mA -> xpres H LB (bv_unsigned sp) X m0 mB)
    /\ (forall R', mb_static R R' -> MEMBIO H LB mA mb R' -> MEMBIO H LB mB mb R')
    /\ (forall R', mb_static R R' -> MEMBIO H LB mA mb R' -> MEMBIO_shad mA mb R' -> MEMBIO_shad mB mb R').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM SPN.
    intros W mA mB sq Lq pc Cp nc FW0 MU WM HPq SLQ.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    assert (S0 : sh 0xc04000 = 0x80178800) by reflexivity.
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
    assert (AS1 : aceil <= S1c) by (clear - CEIL LO STK0 Q2; lia).
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
    destruct (lad_head_facts H HX Lq _ _ _ _ _ HPq) as (BRc & NIPc & DISJc & BLKq & _). pose proof BRc as (C1' & C2' & C3' & C4' & C5' & C6' & C7').
    unfold AIMG_TOP, AFS_SIZE in C4', C6'. pose proof (aapp_not_shadowland _ _ C7') as NSc. pose proof (sh_aapp_range _ _ C7' C3') as (V1 & V2 & V3). rewrite S0 in V1.
    (* [comment removed for export] *)
    assert (CW : Forall (aclient_write_ok H ((pc, Cp, nc) :: Lq)) W).
    { eapply Forall_impl; [| exact FW0]. cbn beta. intros iv [[K1 K2]|[K1 K2]]; [left; clear - K1 CEIL; lia| right; right; left; exists (pc, Cp, nc); split; [left; reflexivity| cbn; split; assumption]]. }
    (* [comment removed for export] *)
    assert (LOWq : forall A n, A + n <= aceil -> (A + n <= Cp \/ Cp + nc <= A) -> disjoint_from W A n).
    { intros A n AQ AB. apply djF. eapply Forall_impl; [| exact FW0]. cbn beta. intros iv [[K1 K2]|[K1 K2]]; [left; clear - K1 AQ CEIL; lia| clear - K1 K2 AB; lia]. }
    assert (HIGHq : forall A n, S1c <= A -> disjoint_from W A n).
    { intros A n HA. apply djF. eapply Forall_impl; [| exact FW0]. cbn beta. intros iv [[K1 K2]|[K1 K2]]; right; [clear - K2 HA; lia| clear - K2 HA C5' AS1; lia]. }
    assert (NIDq : forall b, In b Lq -> blk_id b <> pc).
    { intros b Hb E. apply NIPc. rewrite <- E. exact (in_map blk_id _ _ Hb). }
    assert (BWq : forall b A n, In b Lq -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> disjoint_from W A n).
    { intros b A n Hb HA HB N0. pose proof (ah_blocks H HH _ _ _ _ HPq (or_intror Hb)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      pose proof (DISJc _ Hb) as D. apply LOWq; [clear - D5 HB; lia| clear - D HA HB N0; lia]. }
    (* [comment removed for export] *)
    assert (SWq : forall b A n, In b ((pc, Cp, nc) :: Lq) -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> Forall (winX A n) W).
    { intros b A n Hb HA HB N0. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      eapply Forall_impl; [| exact FW0]. cbn beta. intros iv [[K1 K2]|[K1 K2]]; unfold winX.
      - right; left. unfold AHI_LO. clear - K1 CEIL ACB. lia.
      - (* [comment removed for export] *) clear - K1 K2 NSc. unfold ALOWSH_LO, AHI_LO in *. rewrite ?ASHADOW_BASE_val. lia. }
    repeat match goal with |- _ /\ _ => split end.
    - eapply (ah_RHEAP_frame H HH); [exact HPq| exact MU| exact WM| exact CW].
    - intros AUXq. eapply (ah_rauxv_frame H HH); [exact AUXq| exact MU| exact WM| exact CW].
    - intros LFq RFq. eapply (ah_RFS_frame H HH); [exact RFq| exact MU| exact WM|]. eapply Forall_impl; [| exact FW0]. cbn beta.
      intros iv [[K1 K2]|[K1 K2]]; left; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; [clear - K1 AF2 CEIL ACB; lia| clear - K1 K2 C4' C6'; lia].
    - intros LIBq Mq xq LMq CXq SLq SEq.
      assert (XPq : xpres H ((pc, Cp, nc) :: Lq) S1c W mA mB).
      { eapply (xpres_of_munch_gen H); [exact MU| exact WM|]. intros a Ha [_ HXa]. apply outside_of_not_rin. exact HXa. }
      eapply (LIBMID_xobj H HH sq mA LIBq ((pc, Cp, nc) :: Lq) S1c W [(lo, S1c)] [(pc, Cp, nc)] mA mB Mq xq).
      + exact HPq.
      + exact LMq.
      + exact CXq.
      + exact XPq.
      + intros b Hb. right. exact (SLq _ Hb).
      + intros b Hb. right. exact (SEq _ Hb).
      + intros b Hb. destruct Hb as [<-|[]]. left. reflexivity.
      + intros b b' Hb Hb'. destruct Hb' as [<-|[]]. cbn [blk_id fst snd]. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (NIDq _ (SLq _ Hb))| exact (NIDq _ (SEq _ Hb))].
      + apply Forall_cons; [left; cbn [fst snd]; exact CEIL| apply Forall_nil].
      + intros a Ha. destruct (rin_ivs_In _ _ Ha) as (iv & Hiv & Ra). pose proof (proj1 (Forall_forall _ _) FW0 iv Hiv) as K. cbn beta in K.
        destruct K as [[K1 K2]|[K1 K2]]; [right; cbn; left; clear - K1 K2 Ra; lia| left; exists (pc, Cp, nc); split; [left; reflexivity| cbn; clear - K1 K2 Ra; lia]].
    - intros A cs RC HA. eapply rw_cells_transport; [exact RC| exact MU| exact WM| exact (HIGHq _ _ HA)].
    - intros A cs HA HB RC. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply LOWq; [unfold AFS_SIZE in HB; clear - HB AF2; lia| unfold AFS_SIZE in HB; clear - HA HB C4' C6'; lia].
    - intros A cs HA HB RC. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply LOWq; [clear - HB SHC; lia|].
      unfold ALOWSH_LO, AHI_LO in NSc. unfold AIMG_TOP in HA. rewrite S0 in HA. clear - HA HB NSc V3. unfold AHI_LO in V3. lia.
    - intros b A cs Hb HA HB RC. eapply rw_cells_transport; [exact RC| exact MU| exact WM| exact (BWq b A _ Hb HA HB ltac:(clear; lia))].
    - intros b A bs Hb HA HB RC. eapply bytes_at_transport; [exact RC| exact MU| exact (BWq b A _ Hb HA HB ltac:(clear; lia))].
    - intros b A n Hb HA HB N0 AD. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      eapply addressable_acrossX; [exact AD| exact MU| exact WM| clear - D1 HA; lia| unfold AAPP_HI; clear - D5 HB ACB; lia| exact (SWq b A n Hb HA HB N0)].
    - intros b A n Hb HA HB N0 ACC. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      pose proof (sh_aapp_range _ _ D7 D3) as (U1 & U2 & U3).
      eapply accessible_transport; [exact ACC| exact MU|]. intros y Hy. apply outF. eapply Forall_impl; [| exact FW0]. cbn beta.
      assert (Y1 : AIMG_TOP <= y) by (clear - Hy HA D4; lia). assert (Y2 : y <= aceil) by (clear - Hy HB D5; lia).
      pose proof (conj (sh_mono _ _ Y1) (sh_mono _ _ Y2)) as SX. rewrite S0 in SX.
      intros iv [[K1 K2]|[K1 K2]]; [left; clear - K1 SX SHC CEIL; lia|]. unfold ALOWSH_LO, AHI_LO in NSc. clear - K1 K2 NSc SX V3. unfold AHI_LO in V3. lia.
    - intros errvq RC. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply LOWq; [clear - ERNG ACB; cbn; lia| left; clear - ERNG C4'; cbn; lia].
    - intros S00. eapply stack0_transport; [exact S00| exact MU| exact WM|]. eapply Forall_impl; [| exact FW0]. cbn beta.
      intros iv [[K1 K2]|[K1 K2]]; destruct iv as [l h]; cbn [fst snd] in K1, K2; [apply stack0_ok_app; unfold AHI_LO; clear - K1 CEIL ACB; lia| eapply (stack0_ok_aapp _ _ _ _ C7'); [exact K1| exact K2]].
    - intros ACq. eapply ACONST_frame; [exact ACq| exact MU| exact WM|]. eapply Forall_impl; [| exact FW0]. cbn beta.
      intros iv [[K1 K2]|[K1 K2]]; destruct iv as [l h]; cbn [fst snd] in K1, K2; [apply aconst_ok_hi; unfold AHI_LO; clear - K1 CEIL ACB; lia| eapply (aconst_ok_aapp _ _ _ _ C7'); [exact K1| exact K2]].
    - intros cur CHq C HS. eapply (achain_below H HH mA mB _ _ _ (S1c + 16)); [exact C| exact HS| exact MU|].
      eapply Forall_impl; [| exact FW0]. cbn beta. intros iv [[K1 K2]|[K1 K2]]; left; [clear - K2; lia| clear - K2 C5' AS1; lia].
    - intros X m0 XP. eapply xpres_trans; [exact XP|]. eapply (xpres_of_munch_gen H); [exact MU| exact WM|].
      intros a Ha [Ca HXa]. apply outside_of_not_rin. intros RW. destruct (rin_ivs_In _ _ RW) as (iv & Hiv & Ra).
      pose proof (proj1 (Forall_forall _ _) FW0 iv Hiv) as K. cbn beta in K. destruct K as [[K1 K2]|[K1 K2]].
      + exact ((RCI client_not_frame) _ _ _ _ _ HP SUB0 Ca ltac:(clear - K1 K2 Ra Q2; lia)).
      + (* [comment removed for export] *)
        pose proof (client_outside_block H HH sq ((pc, Cp, nc) :: Lq) mA (pc, Cp, nc) LB (bv_unsigned sp) a HPq (or_introl eq_refl)
                      ltac:(intros b Hb; right; exact (SLQ _ Hb)) ltac:(intros b b' Hb Hb' E; destruct Hb as [<-|[]]; exact (NIDq _ (SLQ _ Hb') (eq_sym E))) ltac:(clear - AS1 Q2; lia) Ca) as OB.
        cbn [blk_addr blk_size fst snd] in OB. clear - OB K1 K2 Ra. lia.
    - intros R' MST MB. eapply (AMEMBIO_munch H LB W mA mB); [exact MB| exact MU| exact WM|].
      apply Forall_forall. intros iv Hiv. apply Forall_forall. intros b Hb. cbn beta.
      rewrite (mb_static_blocks mb R R' MST) in Hb.
      assert (HbL : In b LB) by (destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _); unfold blocks_MEMBIO in Hb; destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption).
      pose proof (ah_blocks H HH _ _ _ _ HPq (or_intror (SLQ _ HbL))) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
      exact (djF_inv _ _ _ _ (BWq _ _ _ (SLQ _ HbL) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) D3) Hiv).
    - intros R' MST MB MSHq. destruct MSHq as (X1 & X2 & X3 & X4). pose proof MB as MBq. destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
      unfold MEMBIO_shad. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
      assert (TA : forall b A n, In b ((pc, Cp, nc) :: Lq) -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> addressable mA A n -> addressable mB A n).
      { intros b A n Hb HA HB N0 AD. pose proof (ah_blocks H HH _ _ _ _ HPq Hb) as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
        eapply addressable_acrossX; [exact AD| exact MU| exact WM| clear - D1 HA; lia| unfold AAPP_HI; clear - D5 HB ACB; lia| exact (SWq b A n Hb HA HB N0)]. }
      split; [| split; [| split]].
      + eapply (TA (mb_id R', mb, 128)); [right; apply SLQ; exact J1| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X1].
      + eapply (TA (mb_bbid R', mb_bb R', 16)); [right; apply SLQ; exact J2| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X2].
      + eapply (TA (mb_bmid R', mb_bm R', 32)); [right; apply SLQ; exact J3| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X3].
      + eapply (TA (mb_rpid R', mb_rp R', 32)); [right; apply SLQ; exact J4| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X4].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition SLOTS (m' : mem) (ff A : Z) : Prop :=
    exists (j0 : list byte) (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w192 w200 w208 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 : word),
         rw_cells asegs m' S1c [CB 16 j0]
      /\ rw_cells asegs m' (S1c + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (wz 0) (wz (ff + 80)) (wz (ff + 64)) (wz 0) (wz st) (wz (ff + 32)))
      /\ rw_cells asegs m' (S1c + 144) (arp_sg2 (wz (Z.shiftr ff 3 + ASHB + 10)) (wz ff) (wz ff) (wz ARP_FILE) (wz ASHB) (wz A) w192 w200 w208 (wz ff) w224 w232)
      /\ rw_cells asegs m' (S1c + 240) (arp_sg3 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336).
  Lemma SLOTS_carry : forall mA mB ff A, (forall A cs, rw_cells asegs mA A cs -> S1c <= A -> rw_cells asegs mB A cs) -> SLOTS mA ff A -> SLOTS mB ff A.
  Proof.
    clear. intros mA mB ff A T (j0 & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w192 & w200 & w208 & w224 & w232 & w240 & w248 & w256 & w264 & w272 & w280 & w288 & w296 & w304 & w312 & w320 & w328 & w336 & P0 & P1 & P2 & P3).
    exists j0, w16, w24, w32, w40, w48, w56, w64, w72, w80, w88, w192, w200, w208, w224, w232, w240, w248, w256, w264, w272, w280, w288, w296, w304, w312, w320, w328, w336.
    split; [exact (T _ _ P0 ltac:(lia))|]. split; [exact (T _ _ P1 ltac:(lia))|]. split; [exact (T _ _ P2 ltac:(lia))| exact (T _ _ P3 ltac:(lia))].
  Qed.

  (* [comment removed for export] *)
  Definition AFW (Lx : list block) (p : bptr) (A nA : Z) (R' : membio) (ff fp : Z) (fk1 fk2 jg e5 : list byte) (n um uf : Z) (m' : mem) (s' : as_St H) : Prop :=
       as_RHEAP H s' (Lx ++ (p, A, nA) :: L0c) m'
    /\ MEMBIO H LB m' mb R' /\ mb_static R R' /\ mb_pos R' = mb_len R /\ 1 <= mb_len R <= nA /\ nA <= 512 * 3 /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN
    /\ bytes_at asegs m' (mb_buf R) ds /\ bytes_at asegs m' A ds
    /\ (exists junk, rw_cells asegs m' A [CB (Z.to_nat (mb_len R)) ds; CB (Z.to_nat (nA - mb_len R)) junk]) /\ addressable m' A nA
    /\ SLOTS m' ff A /\ rw_cells asegs m' (S1c + 344) [CB (Z.to_nat KGc) jg] /\ rw_cells asegs m' (bv_unsigned sp + -104) SAVESc
    /\ fresh_frame H LF 6 ff fp
    /\ rw_cells asegs m' ff (arp_fframe S1c fk1 n fk2 fp)
    /\ rw_cells asegs m' (Z.shiftr ff 3 + ASHB) (arp_fshadow (poison_bytes 4 0xf1) (b8 0xf8) (poison_bytes 3 0xf2) (b8 0xf8) (b8 0xf2) (poison_bytes 256 0xf8) (poison_bytes 16 0xf2) (b8 0xf8) e5)
    /\ as_RFS H (LF1c ff fp) m'
    /\ (exists errv', rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv'])
    /\ as_rauxv_ok H m' B /\ LIBMID LIB m' M
    /\ rw_cells asegs m' st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] /\ addressable m' st STORE_SIZE
    /\ MEMBIO_shad m' mb R' /\ accessible m' (mb_buf R) (mb_len R)
    /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo S1c /\ stack0 m' lo (bv_unsigned sp)
    /\ as_chain H m' (bv_unsigned sp) CH1c
    /\ xpres H LB (bv_unsigned sp) (XSFc ff fp ++ MEMBIO_foot mb R) m m'
    /\ LEDGERc s' um uf.

  (* [comment removed for export] *)
  Lemma afw_x : forall Lx Lx' p A nA R' ff fp fk1 fk2 jg e5 n um uf um' uf' m1 s1' m2 s2' (errv2 : word),
    AFW Lx p A nA R' ff fp fk1 fk2 jg e5 n um uf m1 s1' ->
    xpres H ((p, A, nA) :: L0c) S1c [] m1 m2 ->
    as_RHEAP H s2' (Lx' ++ (p, A, nA) :: L0c) m2 -> mem_inv asegs m2 -> ACONST m2 -> stk asegs m2 lo S1c -> as_rauxv_ok H m2 B ->
    rw_cells asegs m2 (errno_addr (Z_to_bv 64 ATP)) [C4 errv2] -> LEDGERc s2' um' uf' ->
    AFW Lx' p A nA R' ff fp fk1 fk2 jg e5 n um' uf' m2 s2'.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM SPN.
    intros until errv2. intros FW XP HP2 MI2 AC2 STK2 AUX2 ERR2 LED2.
    pose proof FW as (HP1 & MBO1 & MST & POS & LR & NAR & LT & DSm1 & DSA1 & [junk1 JK1] & ADA1 & SL1 & GP1 & SV1 & FRESH & FRM1 & FSH1 & RFS1 & [errv1 ERR1] & AUX1 & LM1
                      & SC1 & SAD1 & MSH1 & PAYa1 & MI1 & AC1 & STK1 & ST01 & CHN1 & XA1 & LED1).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    assert (SHF : Z.shiftr ff 3 + ASHB = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    pose proof SBR as (_ & SB2 & _).
    assert (SQ : forall b, In b LB -> In b ((p, A, nA) :: L0c)) by (intros b Hb; right; exact (SUB0 _ Hb)).
    assert (INA : In (p, A, nA) ((p, A, nA) :: L0c)) by (left; reflexivity).
    pose proof (ah_blocks H HH _ _ _ _ HP1 ltac:(apply in_or_app; right; left; reflexivity)) as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7). cbn [blk_addr blk_size fst snd] in BA1, BA2, BA3, BA4, BA5, BA6, BA7.
    pose proof ((RCI xnil_carry) ff fp m1 m2 s1' (Lx ++ (p, A, nA) :: L0c) ((p, A, nA) :: L0c) FRESH XP HP1 ltac:(intros b Hb; apply in_or_app; right; exact Hb) SQ)
      as (TRFS & TLM & Ts & Tf & Tsh & Tb & Tby & Ta & Tacc & T0 & Tch & Txa & Tmb & Tms).
    destruct (PAYL ltac:(clear - LR; lia)) as [pD [PIN PNL]].
    unfold AFW. repeat match goal with |- _ /\ _ => split end; try assumption.
    all: lazymatch goal with
         | |- MEMBIO H LB _ mb _ => exact (Tmb R' MST MBO1)
         | |- bytes_at asegs _ (mb_buf R) ds => eapply (Tby (pD, mb_buf R, mb_len R)); [exact (SQ _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DSm1]
         | |- bytes_at asegs _ _ ds => eapply (Tby (p, A, nA)); [exact INA| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear - LR; lia| exact DSA1]
         | |- exists _, rw_cells asegs _ (errno_addr _) _ => exists errv2; exact ERR2
         | |- exists _, rw_cells asegs _ _ _ => exists junk1; eapply (Tb (p, A, nA)); [exact INA| cbn; clear; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; clear - LR; lia| exact JK1]
         | |- addressable _ st _ => exact (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE (SQ _ ltac:(pose proof SO as (_ & SINB & _); exact SINB)) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(clear - SB2; Z.div_mod_to_equations; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD1)
         | |- addressable _ _ _ => eapply (Ta (p, A, nA)); [exact INA| apply Z.le_refl| apply Z.le_refl| clear - BA2; Z.div_mod_to_equations; lia| clear - LR; lia| exact ADA1]
         | |- SLOTS _ _ _ => exact (SLOTS_carry m1 m2 ff A Ts SL1)
         | |- rw_cells asegs _ (S1c + 344) _ => exact (Ts _ _ GP1 ltac:(clear; lia))
         | |- rw_cells asegs _ (bv_unsigned sp + -104) _ => exact (Ts _ _ SV1 ltac:(clear - Q2; lia))
         | |- rw_cells asegs _ _ (arp_fframe _ _ _ _ _) => exact (Tf _ FRM1 ltac:(unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia))
         | |- rw_cells asegs _ _ (arp_fshadow _ _ _ _ _ _ _ _ _) => rewrite SHF in FSH1 |- *; exact (Tsh _ FSH1 ltac:(unfold arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia))
         | |- as_RFS H _ _ => exact (TRFS RFS1)
         | |- LIBMID LIB _ M => exact (TLM _ M x LM1 CTX ltac:(intros b Hb; exact (SQ _ (SUBL _ Hb))) ltac:(intros b Hb; right; unfold L0; apply in_or_app; left; exact Hb))
         | |- rw_cells asegs _ st _ => exact (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] (SQ _ ltac:(pose proof SO as (_ & SINB & _); exact SINB)) ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC1)
         | |- MEMBIO_shad _ mb _ => exact (Tms R' MST MBO1 MSH1)
         | |- accessible _ (mb_buf R) _ => eapply (Tacc (pD, mb_buf R, mb_len R)); [exact (SQ _ PIN)| apply Z.le_refl| apply Z.le_refl| clear - LR; lia| exact PAYa1]
         | |- stack0 _ _ _ => exact (T0 ST01)
         | |- as_chain H _ _ _ => exact (Tch _ _ CHN1 ltac:(intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]))
         | |- xpres H LB _ _ m _ => exact (Txa _ _ XA1)
         | |- _ => first [clear - LR; lia| clear - NAR; lia| clear - LT; lia| match goal with |- ?G => idtac "AFWX_LEFT" G end]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma afw_bw : forall W pc Cp nc p A nA R' ff fp fk1 fk2 jg e5 n um uf m1 s1' m2,
    AFW [(pc, Cp, nc)] p A nA R' ff fp fk1 fk2 jg e5 n um uf m1 s1' ->
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= S1c) \/ (Cp <= fst iv /\ snd iv <= Cp + nc)) W ->
    munch W m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 -> stk asegs m2 lo S1c ->
    AFW [(pc, Cp, nc)] p A nA R' ff fp fk1 fk2 jg e5 n um uf m2 s1'.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM SPN.
    intros until m2. intros FW FW0 MU WM MI2 STK2.
    pose proof FW as (HP1 & MBO1 & MST & POS & LR & NAR & LT & DSm1 & DSA1 & [junk1 JK1] & ADA1 & SL1 & GP1 & SV1 & FRESH & FRM1 & FSH1 & RFS1 & [errv1 ERR1] & AUX1 & LM1
                      & SC1 & SAD1 & MSH1 & PAYa1 & MI1 & AC1 & STK1 & ST01 & CHN1 & XA1 & LED1).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    assert (S0 : sh 0xc04000 = 0x80178800) by reflexivity.
    assert (SHF : Z.shiftr ff 3 + ASHB = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    pose proof (sh_add8 ff 512) as SY3. replace (ff + 8 * 512) with (ff + 4096) in SY3 by (clear; lia).
    pose proof (sh_mono (as_FSB H) ff ltac:(clear - FF5; lia)) as SY1. pose proof (sh_mono (ff + 4096) _ FF6) as SY2. pose proof (sh_mono _ _ AF2) as SYA.
    pose proof (sh_aapp_range _ _ AF4 ltac:(unfold AFS_SIZE; clear; lia)) as (W1 & W2 & W3). rewrite S0 in W1.
    pose proof SBR as (_ & SB2 & _). cbn [app] in HP1 |- *.
    assert (SQ : forall b, In b LB -> In b ((p, A, nA) :: L0c)) by (intros b Hb; right; exact (SUB0 _ Hb)).
    pose proof (bw_carry W m1 m2 s1' ((p, A, nA) :: L0c) pc Cp nc FW0 MU WM HP1 SQ)
      as (HP2 & TAUX & TRFS & TLM & Ts & Tf & Tsh & Tb & Tby & Ta & Tacc & Terr & T0 & Tac & Tch & Txa & Tmb & Tms).
    destruct (PAYL ltac:(clear - LR; lia)) as [pD [PIN PNL]].
    pose proof (ah_blocks H HH _ _ _ _ HP1 ltac:(right; left; reflexivity)) as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7). cbn [blk_addr blk_size fst snd] in BA1, BA2, BA3, BA4, BA5, BA6, BA7.
    unfold AFW. repeat match goal with |- _ /\ _ => split end; try assumption.
    all: lazymatch goal with
         | |- MEMBIO H LB _ mb _ => exact (Tmb R' MST MBO1)
         | |- bytes_at asegs _ (mb_buf R) ds => eapply (Tby (pD, mb_buf R, mb_len R)); [exact (SQ _ PIN)| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear; lia| exact DSm1]
         | |- bytes_at asegs _ _ ds => eapply (Tby (p, A, nA)); [left; reflexivity| cbn; clear; lia| cbn; unfold zlength in DSL; rewrite DSL; clear - LR; lia| exact DSA1]
         | |- exists _, rw_cells asegs _ (errno_addr _) _ => exists errv1; exact (Terr _ ERR1)
         | |- exists _, rw_cells asegs _ _ _ => exists junk1; eapply (Tb (p, A, nA)); [left; reflexivity| cbn; clear; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; clear - LR; lia| exact JK1]
         | |- addressable _ st _ => exact (Ta (es_id S, st, STORE_SIZE) st STORE_SIZE ltac:(right; exact (SQ _ ltac:(pose proof SO as (_ & SINB & _); exact SINB))) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STORE_SIZE; clear; lia) SAD1)
         | |- addressable _ _ _ => eapply (Ta (p, A, nA)); [right; left; reflexivity| apply Z.le_refl| apply Z.le_refl| clear - LR; lia| exact ADA1]
         | |- SLOTS _ _ _ => exact (SLOTS_carry m1 m2 ff A Ts SL1)
         | |- rw_cells asegs _ (S1c + 344) _ => exact (Ts _ _ GP1 ltac:(clear; lia))
         | |- rw_cells asegs _ (bv_unsigned sp + -104) _ => exact (Ts _ _ SV1 ltac:(clear - Q2; lia))
         | |- rw_cells asegs _ _ (arp_fframe _ _ _ _ _) => exact (Tf ff (arp_fframe S1c fk1 n fk2 fp) ltac:(clear - FF5; lia) ltac:(unfold arp_fframe; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; unfold AFS_SIZE; clear - FF6; lia) FRM1)
         | |- rw_cells asegs _ _ (arp_fshadow _ _ _ _ _ _ _ _ _) => rewrite SHF in FSH1 |- *;
              exact (Tsh (sh ff) (arp_fshadow (poison_bytes 4 0xf1) (b8 0xf8) (poison_bytes 3 0xf2) (b8 0xf8) (b8 0xf2) (poison_bytes 256 0xf8) (poison_bytes 16 0xf2) (b8 0xf8) e5)
                        ltac:(clear - SY1 W1 S0; unfold AIMG_TOP; rewrite S0; lia) ltac:(unfold arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SY2 SY3 SYA; lia) FSH1)
         | |- as_RFS H _ _ => exact (TRFS _ RFS1)
         | |- as_rauxv_ok H _ B => exact (TAUX AUX1)
         | |- LIBMID LIB _ M => exact (TLM _ M x LM1 CTX ltac:(intros b Hb; exact (SQ _ (SUBL _ Hb))) ltac:(intros b Hb; right; unfold L0; apply in_or_app; left; exact Hb))
         | |- rw_cells asegs _ st _ => exact (Tb (es_id S, st, STORE_SIZE) st [C8 (wz 0); C8 (wz 0); C8 (wz 0)] (SQ _ ltac:(pose proof SO as (_ & SINB & _); exact SINB)) ltac:(cbn; clear; lia) ltac:(cbn; unfold STORE_SIZE; clear; lia) SC1)
         | |- MEMBIO_shad _ mb _ => exact (Tms R' MST MBO1 MSH1)
         | |- accessible _ (mb_buf R) _ => eapply (Tacc (pD, mb_buf R, mb_len R)); [right; exact (SQ _ PIN)| apply Z.le_refl| apply Z.le_refl| clear - LR; lia| exact PAYa1]
         | |- ACONST _ => exact (Tac AC1)
         | |- stack0 _ _ _ => exact (T0 ST01)
         | |- as_chain H _ _ _ => exact (Tch _ _ CHN1 ltac:(intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]))
         | |- xpres H LB _ _ m _ => exact (Txa _ _ XA1)
         | |- _ => first [clear - LR; lia| clear - NAR; lia| clear - LT; lia| match goal with |- ?G => idtac "AFWBW_LEFT" G end]
         end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma SLOTS_join : forall m' ff A, SLOTS m' ff A ->
    exists (j0 : list byte) (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w192 w200 w208 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 : word),
      rw_cells asegs m' S1c ((CB 16 j0 :: arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (wz 0) (wz (ff + 80)) (wz (ff + 64)) (wz 0) (wz st) (wz (ff + 32)))
                             ++ arp_sg2 (wz (Z.shiftr ff 3 + ASHB + 10)) (wz ff) (wz ff) (wz ARP_FILE) (wz ASHB) (wz A) w192 w200 w208 (wz ff) w224 w232
                             ++ arp_sg3 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336)
      /\ rw_cells asegs m' (S1c + 144) (arp_sg2 (wz (Z.shiftr ff 3 + ASHB + 10)) (wz ff) (wz ff) (wz ARP_FILE) (wz ASHB) (wz A) w192 w200 w208 (wz ff) w224 w232).
  Proof.
    clear. intros m' ff A (j0 & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w192 & w200 & w208 & w224 & w232 & w240 & w248 & w256 & w264 & w272 & w280 & w288 & w296 & w304 & w312 & w320 & w328 & w336 & P0 & P1 & P2 & P3).
    exists j0, w16, w24, w32, w40, w48, w56, w64, w72, w80, w88, w192, w200, w208, w224, w232, w240, w248, w256, w264, w272, w280, w288, w296, w304, w312, w320, w328, w336.
    split; [| exact P2].
    change (rw_cells asegs m' S1c ([CB 16 j0] ++ (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (wz 0) (wz (ff + 80)) (wz (ff + 64)) (wz 0) (wz st) (wz (ff + 32))
                                       ++ (arp_sg2 (wz (Z.shiftr ff 3 + ASHB + 10)) (wz ff) (wz ff) (wz ARP_FILE) (wz ASHB) (wz A) w192 w200 w208 (wz ff) w224 w232
                                       ++ arp_sg3 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336)))).
    apply (proj2 (rw_cells_app asegs m' S1c _ _)). split; [exact P0|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 16) with 16.
    apply (proj2 (rw_cells_app asegs m' (S1c + 16) _ _)). split; [exact P1|]. unfold arp_sg1. cbn [cells_size csize Nat.add]. replace (S1c + 16 + Z.of_nat 128) with (S1c + 144) by lia.
    apply (proj2 (rw_cells_app asegs m' (S1c + 144) _ _)). split; [exact P2|]. unfold arp_sg2. cbn [cells_size csize Nat.add]. replace (S1c + 144 + Z.of_nat 96) with (S1c + 240) by lia.
    exact P3.
  Qed.
  Lemma LBUF_join : forall m' A L nA junk, rw_cells asegs m' A [CB (Z.to_nat L) ds; CB (Z.to_nat (nA - L)) junk] -> 0 <= L <= nA ->
    rw_cells asegs m' A [CB (Z.to_nat nA) (ds ++ junk)].
  Proof.
    clear. intros m' A L nA junk RC HL. pose proof (proj1 (rw_cells_app asegs m' A [CB (Z.to_nat L) ds] [CB (Z.to_nat (nA - L)) junk]) RC) as [R1 R2].
    cbn [cells_size csize Nat.add] in R2. rewrite Nat.add_0_r in R2.
    pose proof (rw_cells_CB_join asegs m' A _ _ _ _ R1 R2) as K. replace (Z.to_nat L + Z.to_nat (nA - L))%nat with (Z.to_nat nA) in K by lia. exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma rp_fail603 : forall p A nA R' ff fp fk1 fk2 jg e5 n um uf m' s' msF' mo'
      (u0 u1 u2 a0v a1v a2v b3 b4 b5 b6 b7 s2v s3v s4v s5v s6v s7v s8v s9v s11v u3 u4 u5 u6 : word),
    AFW [] p A nA R' ff fp fk1 fk2 jg e5 n um uf m' s' ->
    um + 2^16 + 64 <= DECODE_CUM_BYTES -> uf + nA + 2^16 + 64 <= DECODE_CUM_BYTES ->
    as_VIS H s' msF' = MS (mkR (Z_to_bv 64 AFM_R603_1) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) a0v a1v a2v b3 b4 b5 b6 b7
                              s2v s3v s4v s5v s6v s7v s8v s9v (Z_to_bv 64 ff) s11v u3 u4 u5 u6) F (Z_to_bv 64 P_ERR_new) fc None m' (seg_rom asegs) ->
    as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
    as_SR H POSTc (mkCfg msF' mo').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM SPN.
    intros until u6. intros FW UMB UFB VIS1 KREL1 MP1.
    pose proof FW as (HP1 & MBO1 & MST & POS & LR & NAR & LT & DSm1 & DSA1 & [junk1 JK1] & ADA1 & SL1 & GP1 & SV1 & FRESH & FRM1 & FSH1 & RFS1 & [errv1 ERR1] & AUX1 & LM1
                      & SC1 & SAD1 & MSH1 & PAYa1 & MI1 & AC1 & STK1 & ST01 & CHN1 & XA1 & LED1).
    cbn [app] in HP1.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof SBR as (_ & SB2 & _ & _ & SBb & _).
    destruct (SLOTS_join _ _ _ SL1) as (j0 & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w192 & w200 & w208 & w224 & w232 & w240 & w248 & w256 & w264 & w272 & w280 & w288 & w296 & w304 & w312 & w320 & w328 & w336 & SLX & _).
    pose proof (LBUF_join _ _ _ _ _ JK1 ltac:(clear - LR; lia)) as LBc1.
    unshelve eapply ((RCI rp_fail_lbuf) 603 AR_PASSED_INVALID_ARGUMENT AFM_R603_1 AFM_R603_2 AFM_ZERO3 (fun _ w => w) _ _ _ _ _ _ _ _ arp_g603a arp_g603b zero3_at_ZERO3 _ _ _
              m' msF' mo' s' p A nA (ds ++ junk1) R' ff fp n fk1 fk2 jg
              (CB 16 j0 :: arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (wz 0) (wz (ff + 80)) (wz (ff + 64)) (wz 0) (wz st) (wz (ff + 32))) (arp_sg3 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336)
              (wz (Z.shiftr ff 3 + ASHB + 10)) (wz ARP_FILE) (wz ASHB) w192 w200 w208 (wz ff) w224 w232 um uf).
    all: try first [exact VIS1| exact HP1| exact KREL1| exact MP1| exact MI1| exact AC1| exact LBc1| exact ADA1| exact MBO1| exact MSH1| exact MST| exact DSm1| exact STK1| exact ST01| exact SLX| exact GP1| exact SV1
                    | exact FRM1| exact FSH1| exact RFS1| exact ERR1| exact AUX1| exact LM1| exact SC1| exact CHN1| exact XA1| exact LED1| exact UMB| exact UFB| reflexivity].
    all: lazymatch goal with
         | |- 0 <= 603 < _ => clear; lia
         | |- 0 < AR_PASSED_INVALID_ARGUMENT < _ => unfold AR_PASSED_INVALID_ARGUMENT; clear; lia
         | |- 0 <= AFM_R603_1 < _ => unfold AFM_R603_1; clear; lia
         | |- 0 <= AFM_R603_2 < _ => unfold AFM_R603_2; clear; lia
         | |- 0 <= AFM_ZERO3 < _ => unfold AFM_ZERO3; clear; lia
         | |- _ mod 2 = 0 => reflexivity
         | |- pf_ok _ (PF_errnew _) _ _ => apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv, pf_raise; do 9 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; left; exact He
         | |- pf_ok _ PF_errdebug _ _ => apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv, pf_raise; do 9 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact He
         | |- pf_ok _ PF_errseterr _ _ => apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv, pf_raise; do 9 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact He
         | |- 0 <= _ <= 512 * 33 => clear - LR NAR; lia
         | |- cells_size (CB 16 _ :: _) = _ => unfold arp_sg1; reflexivity
         | |- cells_size (arp_sg3 _ _ _ _ _ _ _ _ _ _ _ _ _) = _ => unfold arp_sg3; reflexivity
         | |- STORE_shad _ st S => rewrite SEQ; apply (proj2 (STORE_shad_empty _ _ _)); split; [unfold AAPP_HI; clear - SBb ACB; lia| exact SAD1]
         | |- ?G => idtac "F603_LEFT" G
         end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rc_stack2_gen : forall cph eph,
       CMEMDUP_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) AREALLOC_STACK)
    /\ CMALLOC_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) AREALLOC_STACK)
    /\ CFREE_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) AREALLOC_STACK)
    /\ AINTRIN_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) AREALLOC_STACK)
    /\ ASTRSPN_STACK + 464 <= FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (Z.max (ctxph_stack cph) (errph_stack eph)) AREALLOC_STACK).
  Proof. clear. intros [|?] [|?]; repeat split; vm_compute; discriminate. Qed.
  Lemma rc_stack2 : CMEMDUP_STACK + 464 <= READCFG_STACK M /\ CMALLOC_STACK + 464 <= READCFG_STACK M /\ CFREE_STACK + 464 <= READCFG_STACK M
                    /\ AINTRIN_STACK + 464 <= READCFG_STACK M /\ ASTRSPN_STACK + 464 <= READCFG_STACK M.
  Proof. clear. unfold READCFG_STACK, mid_stack. apply rc_stack2_gen. Qed.

  (* [comment removed for export] *)
  Definition FMT_UM : Z := 512 + lad_cm 32 + 1501.
  Definition FMT_UF : Z := lad_cf 32 + 1501.

  (* [comment removed for export] *)
  Definition rp_decK0 : Prop :=
    forall (p : bptr) (A nA : Z) (R' : membio) (ff fp : Z) (fk1 fk2 jg e5 : list byte) (n um uf : Z) (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model)
           (pbin : bptr) (Bb : Z) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s5w s9w u3 u4 u5 u6 : word),
      5 <= mb_len R ->
      AFW [(pbin, Bb, mb_len R)] p A nA R' ff fp fk1 fk2 jg e5 n um uf m' s' -> um <= FMT_UM -> uf <= FMT_UF ->
      rw_cells asegs m' Bb [CB (Z.to_nat (mb_len R)) ds] -> addressable m' Bb (mb_len R) ->
      as_VIS H s' msF' = MS (mkR (Z_to_bv 64 AFM_RDUP) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 Bb) b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 A) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 ASHB) s5w (Z_to_bv 64 (mb_len R)) (Z_to_bv 64 Bb) (Z_to_bv 64 ff) s9w (Z_to_bv 64 ff)
                                  (Z_to_bv 64 0) u3 u4 u5 u6)   (* [comment removed for export] *)
                          F (Z_to_bv 64 AFM_DEC) fc None m' (seg_rom asegs) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
      as_SR H POSTc (mkCfg msF' mo').

  (* [comment removed for export] *)
  Definition rp_b64K : Prop :=
    forall (p : bptr) (A nA : Z) (R' : membio) (ff fp : Z) (fk1 fk2 jg e5 : list byte) (n um uf : Z) (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model) (k : Z)
           (rax u0 u1 u2 a0w b1 b2 b3 b4 b5 b6 b7 s2w s4w s8w s9w s11w u3 u4 u5 u6 : word),
      0 <= k <= 31 -> n = mb_len R - 512 * k -> 1 <= n <= 512 -> nA = 512 * (k + 1) -> 5 <= mb_len R ->
      AFW [] p A nA R' ff fp fk1 fk2 jg e5 n um uf m' s' -> um <= FMT_UM -> uf <= FMT_UF ->
      as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) a0w b1 b2 b3 b4 b5 b6 b7
                                  s2w (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s4w (Z_to_bv 64 (- (512 * k))) (Z_to_bv 64 (mb_len R)) (Z_to_bv 64 n) s8w s9w (Z_to_bv 64 ff)
                                  s11w u3 u4 u5 u6)   (* [comment removed for export] *)
                          F (Z_to_bv 64 AFM_B64) fc None m' (seg_rom asegs) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
      as_SR H POSTc (mkCfg msF' mo').

  (* [comment removed for export] *)
  Lemma rp_fmt : rp_decK0 -> rp_b64K -> rp_okKc.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM SPN.
    intros KDEC KB64. unfold rp_okK.
    intros k n m1 msF1 mo1 s1' p A R' junk ff fp fk1 fk2 jg j0 j1 j3 j4 e5 um uf rax u0 u1 u2 b2 b3 b4 b5 b6 b7 s4v u3 u4 u5 u6 errv1.
    intros KR NEQ NR GOK VIS1 HP1 KREL1 MP1 MI1 AC1 DSA1 JK1 AD1 MBO1 MSH1 MST POS DSm1 PAY1 STK1 ST01 SL1 GP1 SV1 FRM1 FSH1 RFS1 ERR1 AUX1 LM1 SC1 SSH1 CHN1 XA1 LED1 UMB UFB.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof rc_stack2 as (STKD & STKM & STKF & STKI & STKS).
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    assert (AS1 : aceil <= S1c) by (clear - CEIL LO STK0 Q2; lia).
    pose proof (fresh_of_RFS H HH _ _ _ _ _ RFS1) as FRESH.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    assert (SHF : Z.shiftr ff 3 + ASHB = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    pose proof SBR as (SB1 & SB2 & _ & SBa & SBb & _).
    pose proof DSL as DSL1. unfold zlength in DSL1.
    pose proof (errph_bytes_range (mid_err M)) as [EBR ECR].
    pose proof (ah_costs H HH) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd).
    rewrite SEQ in SSH1. apply (proj1 (STORE_shad_empty _ _ _)) in SSH1. destruct SSH1 as [SHhi SAD1].
    destruct (lad_head_facts H HX L0c _ _ _ _ _ HP1) as (BRA & NIPA & DISJA & _ & _). pose proof BRA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7). unfold AIMG_TOP, AFS_SIZE in BA4, BA6.
    (* [comment removed for export] *)
    destruct (arp_slots_split m1 S1c j0 j1 j3 j4 st ff (Z.shiftr ff 3 + ASHB) A SL1)
      as (w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w192 & w200 & w208 & w224 & w232 & w240 & w248 & w256 & w264 & w272 & w280 & w288 & w296 & w304 & w312 & w320 & w328 & w336 & P0 & P1 & P2 & P3).
    unfold arp_sg2L in P2.
    assert (FW1 : AFW [] p A (512 * (k + 1)) R' ff fp fk1 fk2 jg e5 n um uf m1 s1').
    { unfold AFW. cbn [app]. repeat match goal with |- _ /\ _ => split end; try assumption.
      all: lazymatch goal with
           | |- 1 <= mb_len R => clear - NEQ NR KR; lia
           | |- mb_len R <= _ => clear - NEQ NR KR; lia
           | |- mb_len R < _ => exact GOK
           | |- 512 * (_ + 1) <= _ => unfold OSSL_ECH_MAX_ECHCONFIG_LEN in GOK; clear - KR NEQ NR GOK; lia
           | |- exists _, rw_cells asegs _ (errno_addr _) _ => exists errv1; exact ERR1
           | |- exists _, rw_cells asegs _ _ _ => exists junk; exact JK1
           | |- SLOTS _ _ _ => exists j0, w16, w24, w32, w40, w48, w56, w64, w72, w80, w88, w192, w200, w208, w224, w232, w240, w248, w256, w264, w272, w280, w288, w296, w304, w312, w320, w328, w336;
                             split; [exact P0| split; [exact P1| split; [exact P2| exact P3]]]
           | |- accessible _ _ _ => destruct PAY1 as (Y1 & _); exact Y1
           | |- ?G => idtac "FW1_LEFT" G
           end. }
    destruct (Z_lt_ge_dec (mb_len R) 5) as [L5|L5].
    - (* [comment removed for export] *)
      eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply afm_seg1 with (q := S1c) (L := mb_len R) (v160 := ff);
        [clear - L5 NR NEQ KR; lia| reflexivity| clear - AS1 ACB; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| exact P2| exact MI1]|].
      intros msF2 mo2 KREL2 MP2 VIS2. cbn beta in VIS2.
      eapply rp_fail603; [exact FW1| unfold DECODE_CUM_BYTES; clear - UMB; unfold lad_cm in UMB; lia| unfold DECODE_CUM_BYTES; clear - UFB KR; unfold lad_cf in UFB; lia| exact VIS2| exact KREL2| eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]].
    - (* [comment removed for export] *)
      assert (GOK5 : 5 <= mb_len R < 1500) by (unfold OSSL_ECH_MAX_ECHCONFIG_LEN in GOK; clear - L5 GOK; lia).
      pose proof LM1 as (IM1 & MFq1 & _ & _ & _ & _ & _ & _ & GM1 & _). rewrite MF1 in MFq1.
      assert (ACC8 : accessible m1 A 8) by (eapply (addressable_accessible _ _ _ _ _ AD1); [apply Z.le_refl| clear - KR; lia| unfold AAPP_HI; clear - BA5 ACB; lia]).
      eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply afm_seg2 with (q := S1c) (A := A) (L := mb_len R) (n := n) (K := 512 * k) (ds := ds) (ff := ff);
        [clear - GOK5; lia| clear - NEQ; lia| clear - KR; lia| clear - NR; lia| exact BA1| clear - BA5 ACB NEQ NR KR; lia| clear - BA2; Z.div_mod_to_equations; lia
        | clear - AS1 ACB; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| exact DSA1| exact DSL| exact ACC8| exact P2| exact MI1]|].
      intros msF2 mo2 KREL2 MP2 [a3x VIS2]. pose proof (ah_mpres_trans H HH _ _ _ MP1 MP2) as MPc2.
      destruct (is_bin_fmt ds (mb_len R)) eqn:FMT.
      + (* [comment removed for export] *)
        pose proof (acmemdup_spec H HH) as MD. unfold cmemdup_stmt in MD.
        eapply (ah_seq H HH).
        { eapply MD with (D := A) (bs := ds) (bD := (p, A, 512 * (k + 1))) (lo := lo) (B := B) (LB := (p, A, 512 * (k + 1)) :: L0c) (s := s1') (v := 1) (errv := errv1) (CH := CH1c); clear MD.
          all: try first [exact VIS2| exact HP1| exact KREL2| exact AUX1| exact MI1| exact IM1| exact GM1| exact MFq1| exact CEIL| exact DSA1| exact AC1| exact CHN1].
          all: lazymatch goal with
               | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity| rewrite DSL; reflexivity]
               | |- 1 <= zlength ds <= _ => rewrite DSL; clear - GOK5; lia
               | |- In _ _ => left; reflexivity
               | |- blk_addr _ <= _ => apply Z.le_refl
               | |- _ + zlength ds <= blk_addr _ + blk_size _ => cbn [blk_addr blk_size fst snd]; rewrite DSL; clear - NEQ NR KR; lia
               | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_cons; cbn [blk_size snd]; pose proof BUD as BUDq; unfold mid_bytes in BUDq; rewrite CTX in BUDq; cbn [ctxph_bytes] in BUDq;
                                           unfold DECODE_BYTES, ERRSTR_BYTES in BUDq; rewrite DSL; unfold L0; clear - BUDq EBR KR GOK5; lia
               | |- Z.of_nat _ + _ <= _ => cbn [length]; pose proof BUDC as BUDq; unfold mid_cnt in BUDq; rewrite CTX in BUDq; cbn [ctxph_cnt] in BUDq; unfold DECODE_CNT, ERRSTR_CNT in BUDq; unfold L0; clear - BUDq ECR; lia
               | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
               | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact STK1
               | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKD Q2; lia
               | |- rw_cells _ _ (errno_addr _) _ => exact ERR1
               | |- Z_to_bv 64 ATP = _ => reflexivity
               | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
               | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); destruct Hin as [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]
               | |- pf_ok _ _ _ _ => unfold AFM_RDUP; rewrite unsigned_lit by (clear; lia); apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 6 (apply in_or_app; right); apply in_or_app; left; exact He
               | |- as_Cm H _ <= as_AL H _ => rewrite DSL; destruct LED1 as (L0' & L1' & L2'); pose proof (CMadd um (mb_len R) L0' ltac:(clear - GOK5; lia)) as Y1;
                     pose proof (CMmono (um + mb_len R) DECODE_CUM_BYTES ltac:(unfold lad_cm, DECODE_CUM_BYTES in *; clear - GOK5 UMB L0'; lia)) as Y2;
                     pose proof (CFmono uf DECODE_CUM_BYTES ltac:(unfold lad_cf, DECODE_CUM_BYTES in *; clear - UFB L1'; lia)) as Y3;
                     pose proof ALW as ALq; unfold READCFG_COST in ALq; pose proof ((RCI errph_cost_nonneg) (mid_err M)) as Y4; clear - L2' Y1 Y2 Y3 Y4 ALq; lia
               | |- accessible _ _ (zlength ds) => rewrite DSL; eapply (addressable_accessible _ _ _ _ _ AD1); [apply Z.le_refl| clear - NEQ NR KR; lia| unfold AAPP_HI; clear - BA5 ACB; lia]
               | |- ?G => idtac "FMT_MD_LEFT" G
               end. }
        clear MD. intros [msF3 mo3] PO. unfold cmemdup_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & errv2 & Bb & pbin & s2' & VIS3 & KREL3 & MP3 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BRB & HP2 & CELLS2 & ADB2 & MF2 & IM2 & GM2 & AL2).
        rewrite (unsigned_lit S1c) in ST2, XP2 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
        rewrite DSL in BRB, HP2, ADB2, AL2. replace (length ds) with (Z.to_nat (mb_len R)) in CELLS2 by (clear - DSL1; lia).
        pose proof BRB as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5 & Bb6 & Bb7).
        assert (XP2n : xpres H ((p, A, 512 * (k + 1)) :: L0c) S1c [] m1 m2).
        { apply (axpres_drop_memflag H _ S1c [] m1 m2); [rewrite app_nil_r; exact XP2| exact MFq1| exact MF2]. }
        assert (FW2 : AFW [(pbin, Bb, mb_len R)] p A (512 * (k + 1)) R' ff fp fk1 fk2 jg e5 n (um + mb_len R) uf m2 s2').
        { eapply (afw_x [] [(pbin, Bb, mb_len R)]); [exact FW1| exact XP2n| cbn [app]; exact HP2| exact MI2| exact AC2| exact ST2| exact AUX2| exact ERR2|].
          destruct LED1 as (L0' & L1' & L2'). split; [clear - L0' GOK5; lia| split; [exact L1'|]].
          pose proof (CMadd um (mb_len R) L0' ltac:(clear - GOK5; lia)) as Y1. clear - L2' AL2 Y1. lia. }
        (* [comment removed for export] *)
        pose proof FW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SLq & _). destruct (SLOTS_join _ _ _ SLq) as (jq & x16 & x24 & x32 & x40 & x48 & x56 & x64 & x72 & x80 & x88 & x192 & x200 & x208 & x224 & x232 & x240 & x248 & x256 & x264 & x272 & x280 & x288 & x296 & x304 & x312 & x320 & x328 & x336 & _ & P2b).
        eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply afm_seg3 with (q := S1c); [clear - Bb1 Bb5 ACB GOK5; lia| clear - AS1 ACB; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| exact P2b| exact MI2]|].
        intros msF4 mo4 KREL4 MP4 VIS4. cbn beta in VIS4.
        eapply (KDEC p A (512 * (k + 1)) R' ff fp fk1 fk2 jg e5 n (um + mb_len R) uf m2 s2' msF4 mo4 pbin Bb);
          [clear - GOK5; lia| exact FW2| unfold FMT_UM; clear - UMB GOK5; lia| unfold FMT_UF; clear - UFB; lia| exact CELLS2| exact ADB2| exact VIS4| exact KREL4
          | eapply (ah_mpres_trans H HH); [exact MPc2| eapply (ah_mpres_trans H HH); [exact MP3| exact MP4]]].
      + (* [comment removed for export] *)
        pose proof (acmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
        eapply (ah_seq H HH).
        { eapply CM with (n := mb_len R + 1) (lo := lo) (B := B) (LB := (p, A, 512 * (k + 1)) :: L0c) (s := s1') (v := 1) (errv := errv1) (CH := CH1c); clear CM.
          all: try first [exact VIS2| exact HP1| exact KREL2| exact AUX1| exact MI1| exact IM1| exact GM1| exact MFq1| exact CEIL| exact AC1| exact CHN1].
          all: lazymatch goal with
               | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
               | |- 1 <= mb_len R + 1 <= _ => clear - GOK5; lia
               | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_cons; cbn [blk_size snd]; pose proof BUD as BUDq; unfold mid_bytes in BUDq; rewrite CTX in BUDq; cbn [ctxph_bytes] in BUDq;
                                           unfold DECODE_BYTES, ERRSTR_BYTES in BUDq; unfold L0; clear - BUDq EBR KR GOK5; lia
               | |- Z.of_nat _ + _ <= _ => cbn [length]; pose proof BUDC as BUDq; unfold mid_cnt in BUDq; rewrite CTX in BUDq; cbn [ctxph_cnt] in BUDq; unfold DECODE_CNT, ERRSTR_CNT in BUDq; unfold L0; clear - BUDq ECR; lia
               | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
               | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact STK1
               | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKM Q2; lia
               | |- rw_cells _ _ (errno_addr _) _ => exact ERR1
               | |- Z_to_bv 64 ATP = _ => reflexivity
               | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
               | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); destruct Hin as [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]
               | |- pf_ok _ _ _ _ => unfold AFM_RMAL; rewrite unsigned_lit by (clear; lia); apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 7 (apply in_or_app; right); apply in_or_app; left; exact He
               | |- as_Cm H _ <= as_AL H _ => destruct LED1 as (L0' & L1' & L2'); pose proof (CMadd um (mb_len R + 1) L0' ltac:(clear - GOK5; lia)) as Y1;
                     pose proof (CMmono (um + (mb_len R + 1)) DECODE_CUM_BYTES ltac:(unfold lad_cm, DECODE_CUM_BYTES in *; clear - GOK5 UMB L0'; lia)) as Y2;
                     pose proof (CFmono uf DECODE_CUM_BYTES ltac:(unfold lad_cf, DECODE_CUM_BYTES in *; clear - UFB L1'; lia)) as Y3;
                     pose proof ALW as ALq; unfold READCFG_COST in ALq; pose proof ((RCI errph_cost_nonneg) (mid_err M)) as Y4; clear - L2' Y1 Y2 Y3 Y4 ALq; lia
               | |- ?G => idtac "FMT_CM_LEFT" G
               end. }
        clear CM. intros [msF3 mo3] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & errv2 & Cp & junk2 & pc & s2' & VIS3 & KREL3 & MP3 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BRC & HP2 & CELLS2 & ADC2 & MF2 & IM2 & GM2 & AL2).
        rewrite (unsigned_lit S1c) in ST2, XP2 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
        pose proof BRC as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5 & Bc6 & Bc7). unfold AIMG_TOP in Bc4.
        assert (XP2n : xpres H ((p, A, 512 * (k + 1)) :: L0c) S1c [] m1 m2).
        { apply (axpres_drop_memflag H _ S1c [] m1 m2); [rewrite app_nil_r; exact XP2| exact MFq1| exact MF2]. }
        assert (FW2 : AFW [(pc, Cp, mb_len R + 1)] p A (512 * (k + 1)) R' ff fp fk1 fk2 jg e5 n (um + (mb_len R + 1)) uf m2 s2').
        { eapply (afw_x [] [(pc, Cp, mb_len R + 1)]); [exact FW1| exact XP2n| cbn [app]; exact HP2| exact MI2| exact AC2| exact ST2| exact AUX2| exact ERR2|].
          destruct LED1 as (L0' & L1' & L2'). split; [clear - L0' GOK5; lia| split; [exact L1'|]].
          pose proof (CMadd um (mb_len R + 1) L0' ltac:(clear - GOK5; lia)) as Y1. clear - L2' AL2 Y1. lia. }
        destruct (lad_head_facts H HX ((p, A, 512 * (k + 1)) :: L0c) _ _ _ _ _ HP2) as (_ & NIPc & DISJc & _ & _).
        pose proof (DISJc _ (or_introl eq_refl)) as DJc. cbn [blk_addr blk_size fst snd] in DJc.
        clear XP2 XP2n FW1 VIS2 KREL2 MI1 AC1 STK1 ST01 AUX1 ERR1 LM1 SC1 SAD1 CHN1 XA1 DSA1 JK1 AD1 MBO1 MSH1 DSm1 PAY1 HP1 P0 P1 P2 P3 IM1 GM1 MFq1.
        (* [comment removed for export] *)
        pose proof FW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SLq & _). destruct (SLOTS_join _ _ _ SLq) as (jq & x16 & x24 & x32 & x40 & x48 & x56 & x64 & x72 & x80 & x88 & x192 & x200 & x208 & x224 & x232 & x240 & x248 & x256 & x264 & x272 & x280 & x288 & x296 & x304 & x312 & x320 & x328 & x336 & _ & P2d). clear SLq.
        eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply afm_seg4 with (q := S1c) (A := A); [clear - Bc1 Bc5 ACB GOK5; lia| clear - AS1 ACB; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| exact P2d| exact MI2]|].
        intros msF4 mo4 KREL4 MP4 VIS4. cbn beta in VIS4. clear P2d jq x16 x24 x32 x40 x48 x56 x64 x72 x80 x88 x192 x200 x208 x224 x232 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336.
        (* [comment removed for export] *)
        destruct (rw_cells_CB_split asegs m2 Cp _ (Z.to_nat (mb_len R)) _ CELLS2 ltac:(clear - GOK5; lia)) as [CPa CPb].
        replace (Cp + Z.of_nat (Z.to_nat (mb_len R))) with (Cp + mb_len R) in CPb by (clear - GOK5; lia).
        replace (Z.to_nat (mb_len R + 1) - Z.to_nat (mb_len R))%nat with 1%nat in CPb by (clear - GOK5; lia).
        pose proof FW2 as (HP2' & _ & _ & _ & _ & _ & _ & _ & DSA2 & _ & ADA2 & _). cbn [app] in HP2'.
        pose proof (ah_memcpy H HH) as MC. unfold asan_memcpy_stmt, amemcpy_stmt_at in MC.
        eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| |].
        { eapply MC with (src := ds) (lo := lo); clear MC.
          all: rewrite ?unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0 Bc1 Bc5 BA1 BA5 ACB GOK5 KR; lia).
          all: lazymatch goal with
               | |- bytes_at _ _ _ ds => exact DSA2
               | |- length ds = _ => clear - DSL1 GOK5; lia
               | |- rw_cells _ _ _ _ => exact CPa
               | |- _ <= lo \/ _ => left; first [clear - Bc5 CEIL; lia| clear - BA5 CEIL NEQ NR KR; lia]
               | |- _ \/ _ => clear - DJc GOK5 KR NEQ NR; lia
               | |- accessible _ _ _ => first [eapply (addressable_accessible _ _ _ _ _ ADC2); [apply Z.le_refl| clear; lia| unfold AAPP_HI; clear - Bc5 ACB; lia]
                                             | eapply (addressable_accessible _ _ _ _ _ ADA2); [apply Z.le_refl| clear - NEQ NR KR; lia| unfold AAPP_HI; clear - BA5 ACB; lia]]
               | |- shvis _ _ _ => first [eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ HP2' ltac:(left; reflexivity))| clear - Bc1; lia| apply Z.le_refl| cbn [blk_addr blk_size fst snd]; clear - GOK5; lia| clear - GOK5; lia| cbn [blk_addr blk_size fst snd]; clear - Bc1 GOK5; lia]
                                        | eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ HP2' ltac:(right; left; reflexivity))| clear - BA1; lia| apply Z.le_refl| cbn [blk_addr blk_size fst snd]; clear - NEQ NR KR; lia| clear - GOK5; lia| cbn [blk_addr blk_size fst snd]; clear - BA1 KR; lia]]
               | |- stk _ _ _ _ => exact ST2
               | |- aceil <= lo => exact CEIL
               | |- lo <= _ - AINTRIN_STACK => clear - LO STKI Q2; lia
               | |- mem_inv _ _ => exact MI2
               | |- ACONST _ => exact AC2
               | |- mb_len R <= 2 ^ 40 => clear - GOK5; lia
               | |- in_app_mem _ _ => first [eapply (aapp_in_app_mem _ _ _ _ Bc7); [apply Z.le_refl| clear; lia]| eapply (aapp_in_app_mem _ _ _ _ BA7); [apply Z.le_refl| clear - NEQ NR KR; lia]]
               | |- aconst_ok _ => eapply (aconst_ok_aapp _ _ _ _ Bc7); [apply Z.le_refl| clear; lia]
               | |- ?G => idtac "FMT_MC_LEFT" G
               end. }
        intros msF5 mo5 KREL5 MP5 (x0 & x1 & x2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & x3 & x4 & x5 & x6 & m3 & VIS5 & MU5 & WM5 & MI3 & ST3 & CP3 & DSA3 & AC3).
        repeat (rewrite unsigned_lit in MU5 by (clear - Q2 SPR CEIL LO STK0 LO0 Bc1 Bc5 BA1 BA5 ACB GOK5 KR; lia)).
        repeat (rewrite unsigned_lit in ST3 by (clear - Q2 SPR CEIL LO STK0 LO0 Bc1 Bc5 BA1 BA5 ACB GOK5 KR; lia)).
        repeat (rewrite unsigned_lit in CP3 by (clear - Q2 SPR CEIL LO STK0 LO0 Bc1 Bc5 BA1 BA5 ACB GOK5 KR; lia)).
        repeat (rewrite unsigned_lit in DSA3 by (clear - Q2 SPR CEIL LO STK0 LO0 Bc1 Bc5 BA1 BA5 ACB GOK5 KR; lia)).
        assert (FWW5 : Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= S1c) \/ (Cp <= fst iv /\ snd iv <= Cp + (mb_len R + 1))) [(Cp, Cp + mb_len R); (S1c - AINTRIN_STACK, S1c)]).
        { apply Forall_cons; [right; cbn [fst snd]; clear - GOK5; lia|]. apply Forall_cons; [left; cbn [fst snd]; clear - LO STKI Q2; lia| apply Forall_nil]. }
        assert (FW3 : AFW [(pc, Cp, mb_len R + 1)] p A (512 * (k + 1)) R' ff fp fk1 fk2 jg e5 n (um + (mb_len R + 1)) uf m3 s2') by (eapply afw_bw; [exact FW2| exact FWW5| exact MU5| exact WM5| exact MI3| exact ST3]).
        pose proof (bw_carry _ m2 m3 s2' ((p, A, 512 * (k + 1)) :: L0c) pc Cp (mb_len R + 1) FWW5 MU5 WM5 HP2' ltac:(intros b Hb; right; exact (SUB0 _ Hb))) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ta3 & _).
        pose proof (Ta3 (pc, Cp, mb_len R + 1) Cp (mb_len R + 1) (or_introl eq_refl) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(clear - GOK5; lia) ADC2) as ADC3. clear Ta3.
        assert (CPb3 : rw_cells asegs m3 (Cp + mb_len R) [CB 1 (skipn (Z.to_nat (mb_len R)) junk2)]).
        { eapply rw_cells_transport; [exact CPb| exact MU5| exact WM5|]. apply djF.
          apply Forall_cons; [right; cbn [fst snd]; clear; lia|]. apply Forall_cons; [left; cbn [fst snd cells_size csize Nat.add]; clear - Bc5 CEIL LO STKI Q2; lia| apply Forall_nil]. }
        pose proof CPb3 as [[JW _] _]. cbn in JW. destruct (skipn (Z.to_nat (mb_len R)) junk2) as [|jb [|jx jl]]; cbn in JW; try (exfalso; clear - JW; lia).
        assert (CPJ : rw_cells asegs m3 Cp [CB (Z.to_nat (mb_len R)) ds; CB 1 [jb]]).
        { apply (proj2 (rw_cells_app asegs m3 Cp [CB (Z.to_nat (mb_len R)) ds] [CB 1 [jb]])). split; [exact CP3|]. cbn [cells_size csize Nat.add].
          rewrite Nat.add_0_r, Z2Nat.id by (clear - GOK5; lia). exact CPb3. }
        clear CPa CPb CP3 CPb3 JW FW2 HP2' DSA2 ADA2 ADC2 MU5 WM5 CELLS2 VIS3 VIS4 KREL3 KREL4 MI2 AC2 ST2.
        (* [comment removed for export] *)
        pose proof FW3 as (HP3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SLq & _). cbn [app] in HP3.
        destruct (SLOTS_join _ _ _ SLq) as (jq & x16 & x24 & x32 & x40 & x48 & x56 & x64 & x72 & x80 & x88 & x192 & x200 & x208 & x224 & x232 & x240 & x248 & x256 & x264 & x272 & x280 & x288 & x296 & x304 & x312 & x320 & x328 & x336 & _ & P2c). clear SLq.
        eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5| eapply afm_seg5 with (q := S1c) (Cp := Cp) (n := n) (K := 512 * k) (L := mb_len R) (cp := ds) (jb := jb);
          [exact Bc1| clear - Bc5 ACB GOK5; lia| clear - NEQ; lia| clear - NR; lia| clear - KR; lia| clear - GOK5; lia| clear - DSL1 GOK5; lia| clear - AS1 ACB; lia
          | clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| left; clear - Bc5 AS1; lia| exact P2c| exact CPJ| eapply (addressable_accessible _ _ _ _ _ ADC3); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI; clear - Bc5 ACB; lia]| exact MI3]|].
        intros msF6 mo6 KREL6 MP6 (m4 & a2x & VIS6 & MU6 & WM6 & MI4 & CP4). clear P2c.
        assert (ST4 : stk asegs m4 lo S1c) by (eapply stk_transport_disjoint; [exact ST3| exact MU6| exact WM6| cbn [disjoint_from]; split; [right; clear - Bc5 CEIL; lia| exact I]]).
        assert (FWW6 : Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= S1c) \/ (Cp <= fst iv /\ snd iv <= Cp + (mb_len R + 1))) [(Cp + mb_len R, Cp + mb_len R + 1)]).
        { apply Forall_cons; [right; cbn [fst snd]; clear - GOK5; lia| apply Forall_nil]. }
        assert (FW4 : AFW [(pc, Cp, mb_len R + 1)] p A (512 * (k + 1)) R' ff fp fk1 fk2 jg e5 n (um + (mb_len R + 1)) uf m4 s2') by (eapply afw_bw; [exact FW3| exact FWW6| exact MU6| exact WM6| exact MI4| exact ST4]).
        pose proof (bw_carry _ m3 m4 s2' ((p, A, 512 * (k + 1)) :: L0c) pc Cp (mb_len R + 1) FWW6 MU6 WM6 HP3 ltac:(intros b Hb; right; exact (SUB0 _ Hb))) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ta4 & _).
        pose proof (Ta4 (pc, Cp, mb_len R + 1) Cp (mb_len R + 1) (or_introl eq_refl) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(clear - GOK5; lia) ADC3) as ADC4. clear Ta4.
        clear FW3 HP3 MU6 WM6 MI3 ST3 ADC3 CPJ VIS5 KREL5.
        pose proof FW4 as (HP4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AC4 & _). cbn [app] in HP4.
        destruct (HHx_canary H HX _ _ _ HP4) as (can & CG4 & CC4 & CANR).
        pose proof (proj2 (proj2 (proj1 R_B64A)) m4 MI4) as (AB4 & AN4 & _). pose proof (proj1 (proj2 R_B64A) m4 AC4) as AACC4. rewrite S_B64A_len in AACC4. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in AACC4.
        destruct (nul_split ds) as (str & rest & SPLIT & SNN & SLE & SEQ').
        assert (CSTR4 : bytes_at asegs m4 Cp (str ++ Z_to_bv 8 0 :: rest)).
        { rewrite <- SPLIT. pose proof CP4 as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY. rewrite ?app_nil_r in BY. exact BY. }
        assert (SL1' : length (str ++ Z_to_bv 8 0 :: rest) = (length ds + 1)%nat) by (rewrite <- SPLIT, length_app; cbn [length]; clear; lia).
        rewrite length_app in SL1'. cbn [length] in SL1'.
        eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| |].
        { eapply SPN with (str := str) (sslack := rest) (acc := S_B64A) (aslack := K_B64A) (lo := lo) (can := can).
          all: lazymatch goal with
               | |- bytes_at _ _ (bv_unsigned (Z_to_bv 64 AA_B64_ALPHABET)) _ => unfold AA_B64_ALPHABET; rewrite unsigned_lit by (clear; lia); exact AB4
               | |- bytes_at _ _ _ _ => rewrite unsigned_lit by (clear - Bc1 Bc5 ACB GOK5; lia); exact CSTR4
               | |- ~ In _ S_B64A => exact AN4
               | |- ~ In _ _ => exact SNN
               | |- (2 <= length S_B64A)%nat => rewrite S_B64A_len; clear; lia
               | |- accessible _ (bv_unsigned (Z_to_bv 64 AA_B64_ALPHABET)) _ => unfold AA_B64_ALPHABET in *; rewrite unsigned_lit by (clear; lia); rewrite S_B64A_len; exact AACC4
               | |- accessible _ _ _ => rewrite unsigned_lit by (clear - Bc1 Bc5 ACB GOK5; lia); eapply (addressable_accessible _ _ _ _ _ ADC4); [apply Z.le_refl| clear - SLE DSL1 GOK5; lia| unfold AAPP_HI; clear - Bc5 ACB; lia]
               | |- shvis _ (bv_unsigned (Z_to_bv 64 AA_B64_ALPHABET)) _ => unfold AA_B64_ALPHABET in *; rewrite !unsigned_lit by (clear; lia); rewrite S_B64A_len; apply ACONST_shvis; [exact AC4| unfold AIMG_LO; clear; cbn; lia| clear; cbn; lia| unfold AIMG_TOP; clear; cbn; lia]
               | |- shvis _ _ _ => rewrite !unsigned_lit by (clear - Bc1 Bc5 ACB GOK5; lia); eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ HP4 ltac:(left; reflexivity))| clear - Bc1; lia| apply Z.le_refl| cbn [blk_addr blk_size fst snd]; clear - SLE DSL1 GOK5; lia| clear; lia| cbn [blk_addr blk_size fst snd]; clear - Bc1 GOK5; lia]
               | |- in_app_mem (bv_unsigned (Z_to_bv 64 AA_B64_ALPHABET)) _ => unfold AA_B64_ALPHABET; rewrite !unsigned_lit by (clear; lia); unfold in_app_mem; left; rewrite ASHADOW_BASE_val; cbn; clear; lia
               | |- in_app_mem _ _ => rewrite !unsigned_lit by (clear - Bc1 Bc5 ACB GOK5; lia); eapply (aapp_in_app_mem _ _ _ _ Bc7); [apply Z.le_refl| clear - SLE DSL1 GOK5; lia]
               | |- Z.of_nat (length S_B64A) + 1 <= _ => rewrite S_B64A_len; clear; cbn; lia
               | |- Z.of_nat (length _) + 1 <= _ => clear - SLE DSL1 GOK5; lia
               | |- bv_unsigned (Z_to_bv 64 AA_B64_ALPHABET) + _ + _ + _ <= lo => unfold AA_B64_ALPHABET; rewrite !unsigned_lit by (clear; lia); rewrite S_B64A_len; cbn; clear - CEIL ACB; lia
               | |- bv_unsigned _ + _ + _ + _ <= lo => rewrite !unsigned_lit by (clear - Bc1 Bc5 ACB GOK5; lia); clear - SL1' DSL1 Bc5 CEIL GOK5; lia
               | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST4
               | |- aceil <= lo => exact CEIL
               | |- lo <= _ - ASTRSPN_STACK => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKS Q2; lia
               | |- _ + 8 <= 2 ^ 64 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPR Q2; lia
               | |- mem_inv _ _ => exact MI4
               | |- ACONST _ => exact AC4
               | |- rw_cells _ _ AGOT_SSP_CELL _ => exact CG4
               | |- rw_cells _ _ ACANARY_CELL _ => exact CC4
               | |- 0 <= _ < 2 ^ 64 => exact CANR
               | |- ?G => idtac "FMT_SPN_LEFT" G
               end. }
        intros msF7 mo7 KREL7 MP7 (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5' & e6 & e7 & y3 & y4 & y5 & y6 & m5 & VIS7 & MU7 & WM7 & MI5 & ST5 & AC5).
        repeat (rewrite unsigned_lit in MU7 by (clear - Q2 SPR CEIL LO STK0 LO0; lia)). repeat (rewrite unsigned_lit in ST5 by (clear - Q2 SPR CEIL LO STK0 LO0; lia)).
        assert (FWW7 : Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= S1c) \/ (Cp <= fst iv /\ snd iv <= Cp + (mb_len R + 1))) [(S1c - ASTRSPN_STACK, S1c)]).
        { apply Forall_cons; [left; cbn [fst snd]; clear - LO STKS Q2; lia| apply Forall_nil]. }
        assert (FW5 : AFW [(pc, Cp, mb_len R + 1)] p A (512 * (k + 1)) R' ff fp fk1 fk2 jg e5 n (um + (mb_len R + 1)) uf m5 s2') by (eapply afw_bw; [exact FW4| exact FWW7| exact MU7| exact WM7| exact MI5| exact ST5]).
        pose proof (bw_carry _ m4 m5 s2' ((p, A, 512 * (k + 1)) :: L0c) pc Cp (mb_len R + 1) FWW7 MU7 WM7 HP4 ltac:(intros b Hb; right; exact (SUB0 _ Hb))) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ta5 & _).
        pose proof (Ta5 (pc, Cp, mb_len R + 1) Cp (mb_len R + 1) (or_introl eq_refl) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(clear - GOK5; lia) ADC4) as ADC5. clear Ta5.
        assert (CP5 : rw_cells asegs m5 Cp [CB (Z.to_nat (mb_len R + 1)) (ds ++ [Z_to_bv 8 0])]).
        { assert (CP5' : rw_cells asegs m5 Cp [CB (Z.to_nat (mb_len R)) ds; CB 1 [Z_to_bv 8 0]]).
          { eapply rw_cells_transport; [exact CP4| exact MU7| exact WM7| cbn [disjoint_from cells_size csize Nat.add]; split; [left; clear - Bc5 CEIL LO STKS Q2 GOK5; lia| exact I]]. }
          pose proof (proj1 (rw_cells_app asegs m5 Cp [CB (Z.to_nat (mb_len R)) ds] [CB 1 [Z_to_bv 8 0]]) CP5') as [R1 R2]. cbn [cells_size csize Nat.add] in R2. rewrite Nat.add_0_r in R2.
          pose proof (rw_cells_CB_join asegs m5 Cp _ _ _ _ R1 R2) as K. replace (Z.to_nat (mb_len R) + 1)%nat with (Z.to_nat (mb_len R + 1)) in K by (clear - GOK5; lia). exact K. }
        set (span := Z.of_nat (spn str S_B64A)) in *.
        assert (SPANR : 0 <= span <= mb_len R) by (subst span; pose proof (spn_le str S_B64A) as K'; clear - K' SLE DSL1; lia).
        clear FW4 HP4 CG4 CC4 AB4 AN4 AACC4 CSTR4 MU7 WM7 MI4 ST4 CP4 ADC4 VIS6 KREL6.
        (* [comment removed for export] *)
        eapply (ahh_evt_then H HH); [exact KREL7| exact VIS7| eapply afm_seg6; exact MI5|]. intros msF8 mo8 KREL8 MP8 VIS8. cbn beta in VIS8.
        pose proof FW5 as (HP5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv5 ERR5] & AUX5 & LM5 & _ & _ & _ & _ & _ & _ & STK5 & _ & CHN5 & _ & LED5). cbn [app] in HP5.
        pose proof LM5 as (IM5 & MFq5 & _ & _ & _ & _ & _ & _ & GM5 & _).
        pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
        eapply (ah_seq H HH).
        { eapply CF with (lo := lo) (B := B) (LB := (pc, Cp, mb_len R + 1) :: (p, A, 512 * (k + 1)) :: L0c) (s := s2') (p := pc) (A := Cp) (n := mb_len R + 1) (errv := errv5) (CH := CH1c) (bs := ds ++ [Z_to_bv 8 0]); clear CF.
          all: try first [exact VIS8| exact HP5| exact KREL8| exact AUX5| exact MI5| exact CEIL| exact AC5| exact CHN5| exact CP5| exact ADC5| exact IM5| exact GM5| exact ERR5].
          all: lazymatch goal with
               | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
               | |- In _ _ => left; reflexivity
               | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
               | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact STK5
               | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKF Q2; lia
               | |- Z_to_bv 64 ATP = _ => reflexivity
               | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
               | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); destruct Hin as [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]
               | |- pf_ok _ _ _ _ => unfold AFM_RFRE; rewrite unsigned_lit by (clear; lia); apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 8 (apply in_or_app; right); apply in_or_app; left; exact He
               | |- as_Cf H _ <= as_AL H _ => destruct LED5 as (L0' & L1' & L2'); pose proof (CFadd uf (mb_len R + 1) L1' ltac:(clear - GOK5; lia)) as Y1;
                     pose proof (CMmono (um + (mb_len R + 1)) DECODE_CUM_BYTES ltac:(unfold lad_cm, DECODE_CUM_BYTES in *; clear - GOK5 UMB L0'; lia)) as Y2;
                     pose proof (CFmono (uf + (mb_len R + 1)) DECODE_CUM_BYTES ltac:(unfold lad_cf, DECODE_CUM_BYTES in *; clear - UFB L1' GOK5; lia)) as Y3;
                     pose proof ALW as ALq; unfold READCFG_COST in ALq; pose proof ((RCI errph_cost_nonneg) (mid_err M)) as Y4; clear - L2' Y1 Y2 Y3 Y4 ALq; lia
               | |- ?G => idtac "FMT_CF_LEFT" G
               end. }
        clear CF. intros [msF9 mo9] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (z0 & z1 & z2 & f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & z3 & z4 & z5 & z6 & m6 & s6' & VIS9 & KREL9 & MP9 & MI6 & AC6 & ST6 & ERR6 & AUX6 & XP6 & HP6 & IM6 & GM6 & AL6).
        rewrite (proj1 (ah_lb_remove H HH)) in XP6, HP6 by exact NIPc.
        rewrite (unsigned_lit S1c) in ST6, XP6 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
        assert (FW6 : AFW [] p A (512 * (k + 1)) R' ff fp fk1 fk2 jg e5 n (um + (mb_len R + 1)) (uf + (mb_len R + 1)) m6 s6').
        { eapply (afw_x [(pc, Cp, mb_len R + 1)] []); [exact FW5| exact XP6| cbn [app]; exact HP6| exact MI6| exact AC6| exact ST6| exact AUX6| exact ERR6|].
          destruct LED5 as (L0' & L1' & L2'). split; [exact L0'| split; [clear - L1' GOK5; lia|]].
          pose proof (CFadd uf (mb_len R + 1) L1' ltac:(clear - GOK5; lia)) as Y1. clear - L2' AL6 Y1. lia. }
        clear FW5 HP5 ERR5 AUX5 LM5 STK5 CHN5 LED5 IM5 MFq5 GM5 CP5 ADC5 XP6 HP6 MI5 ST5 AC5 VIS7 VIS8 KREL7 KREL8.
        (* [comment removed for export] *)
        eapply (ahh_evt_then H HH); [exact KREL9| exact VIS9| eapply afm_seg7 with (span := span) (L := mb_len R); [clear - SPANR GOK5; lia| clear - GOK5; lia| exact MI6]|].
        intros msF10 mo10 KREL10 MP10 VIS10. cbn beta in VIS10.
        pose proof (ah_mpres_trans H HH _ _ _ MPc2 (ah_mpres_trans H HH _ _ _ MP3 (ah_mpres_trans H HH _ _ _ MP4 (ah_mpres_trans H HH _ _ _ MP5 (ah_mpres_trans H HH _ _ _ MP6
                      (ah_mpres_trans H HH _ _ _ MP7 (ah_mpres_trans H HH _ _ _ MP8 (ah_mpres_trans H HH _ _ _ MP9 MP10)))))))) as MPc10.
        destruct (span <? mb_len R) eqn:SLt.
        * (* [comment removed for export] *)
          eapply rp_fail603; [exact FW6| unfold DECODE_CUM_BYTES; clear - UMB GOK5; unfold lad_cm in UMB; lia| unfold DECODE_CUM_BYTES; clear - UFB KR GOK5; unfold lad_cf in UFB; lia| exact VIS10| exact KREL10| exact MPc10].
        * (* [comment removed for export] *)
          eapply (KB64 p A (512 * (k + 1)) R' ff fp fk1 fk2 jg e5 n (um + (mb_len R + 1)) (uf + (mb_len R + 1)) m6 s6' msF10 mo10 k);
            [exact KR| exact NEQ| exact NR| reflexivity| clear - GOK5; lia| exact FW6| unfold FMT_UM; clear - UMB GOK5; lia| unfold FMT_UF; clear - UFB GOK5; lia| exact VIS10| exact KREL10| exact MPc10].
  Qed.
End RC.
