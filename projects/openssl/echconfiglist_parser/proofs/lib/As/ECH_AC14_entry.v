(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 AsAuxv ECH_AImg ECH_Xpres ECH_ARep ECH_ALib
  ECH_ALibMF ECH_Iface ECH_AStmt_C1 ECH_AC1_zalloc ECH_AC1_free ECH_AC1_malloc ECH_AC1_dup ECH_AC1_marr ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C5 ECH_AStmt_C7 ECH_AStmt_C10 ECH_AStmt_C13
  ECH_AStmt_C6 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AKitSeg ECH_AsKit ECH_AsKitK ECH_AC13_entry ECH_AC13_store ECH_AC7_kit ECH_AC7_rd ECH_AC7_rd2 ECH_AC7_bioread ECH_ARostr ECH_ALibMid ECH_AC11_fail
  ECH_AStmt_C12 ECH_AC12_addstr ECH_AC13 ECH_AC14_kit
  N6_memchr F_time ECH_AC10 ECH_AC13_small ECH_AC5_small ECH_AC5_new ECH_AC5_push ECH_AC14_decexts_seg ECH_AC14_fcc_seg ECH_AC14_decexts ECH_AC14_fcc
  ECH_AC14_bio2buf_seg ECH_AC14_ladder_seg ECH_AC14_ladloop ECH_AC14_fmt_seg ECH_AC14_flat_seg ECH_AC14_entry_seg ECH_AStmt_C14
  F_strspn N6_strspn ECH_AC14_b2b ECH_AC14_fmt ECH_AC14_dec ECH_AC14_pushK ECH_AC14_push.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section KCE.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Lemma fe_Cf_nonneg : forall n, 0 <= n -> 0 <= as_Cf H n.
  Proof. pose proof (ah_costs H HH) as (_ & _ & K & _). exact K. Qed.
  Lemma fe_Cf_mono : forall n n', 0 <= n <= n' -> as_Cf H n <= as_Cf H n'.
  Proof. pose proof (ah_costs H HH) as (_ & _ & _ & K & _). exact K. Qed.
  Lemma fe_Cf_super : forall a b, 0 <= a -> 0 <= b -> as_Cf H a + as_Cf H b <= as_Cf H (a + b).
  Proof. pose proof (ah_costs H HH) as (_ & _ & _ & _ & _ & K). exact K. Qed.
  Lemma fe_Cf_arg : forall x a b, x <= as_Cf H a -> a = b -> x <= as_Cf H b.
  Proof. intros x a b K E. subst b. exact K. Qed.
  Lemma fe_Cf_zero : as_Cf H 0 = 0.
  Proof. pose proof (fe_Cf_super 0 0 (Z.le_refl 0) (Z.le_refl 0)) as K. pose proof (fe_Cf_nonneg 0 (Z.le_refl 0)) as K'. rewrite Z.add_0_r in K. lia. Qed.

  Lemma fe_Forall2_In_combine : forall (A B : Type) (R : A -> B -> Prop) (l : list A) (l' : list B) (x : A) (y : B),
    Forall2 R l l' -> In (x, y) (combine l l') -> R x y.
  Proof.
    intros A B R l l' x y F Hin. induction F as [|a b l0 l0' Rab F IH]; [destruct Hin|].
    cbn in Hin. destruct Hin as [E|Hin]; [injection E as <- <-; exact Rab| exact (IH Hin)].
  Qed.
  Lemma fe_ocost_bound : forall P o, Forall (fun b => 0 <= blk_size b) (blocks_of P o) ->
    0 <= lb_bytes (blocks_of P o) /\ ocost H o <= as_Cf H (lb_bytes (blocks_of P o)).
  Proof.
    intros P [[id n]|] F; cbn [blocks_of ocost] in *.
    - pose proof (Forall_inv F) as K. cbn in K. rewrite lb_bytes_cons. cbn [blk_size snd lb_bytes fold_right]. rewrite Z.max_l by lia. split; [lia|]. apply fe_Cf_mono. lia.
    - cbn [lb_bytes fold_right]. rewrite fe_Cf_zero. lia.
  Qed.

  Lemma fe_ecost_sum_bound : forall (X : Type) (f : X -> Z) (g : Z -> X -> list block) (ps : list Z) (xs : list X),
    length xs = length ps ->
    (forall p x, In (p, x) (combine ps xs) -> 0 <= lb_bytes (g p x) /\ f x <= as_Cf H (lb_bytes (g p x))) ->
    0 <= lb_bytes (concat (map (fun pe => g (fst pe) (snd pe)) (combine ps xs)))
    /\ ecost_sum X f xs <= as_Cf H (lb_bytes (concat (map (fun pe => g (fst pe) (snd pe)) (combine ps xs)))).
  Proof.
    intros X f g ps xs. revert ps. induction xs as [|x xs IH]; intros [|p ps] LEN HF; cbn [length] in LEN; try lia.
    - cbn. rewrite fe_Cf_zero. lia.
    - cbn [combine map concat fst snd ecost_sum fold_right]. rewrite lb_bytes_app_s.
      destruct (HF p x ltac:(left; reflexivity)) as [B1 B2].
      destruct (IH ps ltac:(lia) ltac:(intros p' x' Hin; apply HF; right; exact Hin)) as [B3 B4].
      change (fold_right (fun x0 acc => f x0 + acc) 0 xs) with (ecost_sum X f xs).
      split; [lia|]. pose proof (fe_Cf_super _ _ B1 B3). lia.
  Qed.

  Lemma fe_sk_cost_bound : forall P K, Forall (fun b => 0 <= blk_size b) (blocks_SK P K) ->
    0 <= lb_bytes (blocks_SK P K) /\ as_Cf H (Z.max (8 * sk_cap K) 0) + as_Cf H SK_SIZE <= as_Cf H (lb_bytes (blocks_SK P K)).
  Proof.
    intros P K F. unfold blocks_SK in *. rewrite lb_bytes_cons. cbn [blk_size snd].
    destruct (sk_cap K =? 0) eqn:E.
    - apply Z.eqb_eq in E. rewrite E. cbn [lb_bytes fold_right Z.mul Z.max]. rewrite fe_Cf_zero. unfold SK_SIZE. rewrite Z.add_0_r. split; [lia|]. lia.
    - pose proof (Forall_inv (Forall_inv_tail F)) as K2. cbn in K2. rewrite lb_bytes_cons. cbn [blk_size snd lb_bytes fold_right].
      rewrite Z.max_l by lia. unfold SK_SIZE in *. split; [lia|]. pose proof (fe_Cf_super (8 * sk_cap K) 56 ltac:(lia) ltac:(lia)) as K3. eapply (fe_Cf_arg _ _ _ K3). lia.
  Qed.

  Lemma fe_ext_cost_bound : forall LB m p X, EXTobj LB m p X -> Forall (fun b => 0 <= blk_size b) (blocks_EXT p X) ->
    0 <= lb_bytes (blocks_EXT p X) /\ ext_cost H X <= as_Cf H (lb_bytes (blocks_EXT p X)).
  Proof.
    intros LB m p X _ F. unfold blocks_EXT, ext_cost in *. rewrite lb_bytes_cons. cbn [blk_size snd].
    destruct (fe_ocost_bound (ex_val X) (ex_val_o X) (Forall_inv_tail F)) as [B1 B2]. unfold EXT_SIZE in *.
    split; [lia|]. pose proof (fe_Cf_super 16 (lb_bytes (blocks_of (ex_val X) (ex_val_o X))) ltac:(lia) B1). lia.
  Qed.

  Lemma fe_exts_cost_bound : forall LB m P xs, EXTS LB m P xs -> Forall (fun b => 0 <= blk_size b) (blocks_EXTS P xs) ->
    0 <= lb_bytes (blocks_EXTS P xs) /\ exts_cost H xs <= as_Cf H (lb_bytes (blocks_EXTS P xs)).
  Proof.
    intros LB m P [[K es]|] EX F; cbn [blocks_EXTS exts_cost] in *.
    - destruct EX as (_ & _ & LEN & F2). apply Forall_app in F. destruct F as [FS FE].
      destruct (fe_sk_cost_bound P K FS) as [S1 S2]. rewrite lb_bytes_app_s.
      destruct (fe_ecost_sum_bound extrep (ext_cost H) blocks_EXT (sk_elems K) es LEN) as [E1 E2].
      { intros p x Hin. eapply fe_ext_cost_bound with (LB := LB) (m := m).
        - eapply (fe_Forall2_In_combine _ _ _ _ _ _ _ F2 Hin).
        - rewrite Forall_forall in FE. apply Forall_forall. intros b Hb. apply FE. apply in_concat. exists (blocks_EXT p x). split; [| exact Hb].
          apply in_map_iff. exists (p, x). split; [reflexivity| exact Hin]. }
      split; [lia|]. pose proof (fe_Cf_super _ _ S1 E1). lia.
    - cbn [lb_bytes fold_right]. pose proof (fe_Cf_nonneg 0 ltac:(lia)). lia.
  Qed.

  Lemma fe_entry_cost_bound : forall LB m p E, ENTRYobj LB m p E -> Forall (fun b => 0 <= blk_size b) (blocks_ENTRY p E) ->
    0 <= lb_bytes (blocks_ENTRY p E) /\ entry_cost H E <= as_Cf H (lb_bytes (blocks_ENTRY p E)).
  Proof.
    intros LB m p E EO F. unfold blocks_ENTRY, entry_cost in *. rewrite lb_bytes_cons. cbn [blk_size snd].
    pose proof (Forall_inv_tail F) as F'. cbn [blk_size snd] in F'.
    apply Forall_app in F'. destruct F' as [F1 F']. apply Forall_app in F'. destruct F' as [F2 F']. apply Forall_app in F'. destruct F' as [F3 F'].
    apply Forall_app in F'. destruct F' as [F4 F5].
    destruct (fe_ocost_bound _ _ F1) as [A1 A2]. destruct (fe_ocost_bound _ _ F2) as [B1 B2]. destruct (fe_ocost_bound _ _ F3) as [G1 G2]. destruct (fe_ocost_bound _ _ F4) as [D1 D2].
    destruct EO as (_ & _ & _ & _ & _ & _ & EX). destruct (fe_exts_cost_bound _ _ _ _ EX F5) as [X1 X2].
    rewrite !lb_bytes_app_s.
    set (bA := lb_bytes (blocks_of (en_pname E) (en_pname_o E))) in *. set (bB := lb_bytes (blocks_of (en_pub E) (en_pub_o E))) in *.
    set (bC := lb_bytes (blocks_of (en_suites E) (en_suites_o E))) in *. set (bD := lb_bytes (blocks_of (en_encoded E) (en_encoded_o E))) in *.
    set (bX := lb_bytes (blocks_EXTS (en_exts E) (en_exts_o E))) in *.
    unfold ENTRY_SIZE in *. split; [lia|].
    pose proof (fe_Cf_super bD bX D1 X1) as S4.
    pose proof (fe_Cf_super bC (bD + bX) G1 ltac:(lia)) as S3.
    pose proof (fe_Cf_super bB (bC + (bD + bX)) B1 ltac:(lia)) as S2.
    pose proof (fe_Cf_super bA (bB + (bC + (bD + bX))) A1 ltac:(lia)) as S1.
    pose proof (fe_Cf_super 104 (bA + (bB + (bC + (bD + bX)))) ltac:(lia) ltac:(lia)) as S0.
    lia.
  Qed.

End KCE.

(* [comment removed for export] *)
Section RC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  Hypothesis RAISE : araise_stmt H.
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

  (* [comment removed for export] *)
  Local Notation AFWc := (AFW H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B R ds CH).

  (* [comment removed for export] *)
  Variables (p : bptr) (A nA : Z) (pbin : bptr) (Bb nB : Z) (bs : list byte) (R' : membio) (bt : Z) (TB : list block).
  Variable BT : mem -> Prop.
  Variables (ff fp n : Z) (fj24 tpb fj128 fj2 jz jg e5 : list byte) (w224 : word).
  Hypotheses (NAR : 1 <= mb_len R <= nA /\ nA <= 512 * 3)                 (* [comment removed for export] *)
             (NBR : 0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN)
             (MST : mb_static R R') (POS : mb_pos R' = mb_len R)
             (BTR : 0 <= bt < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072)
             (BT_frame : forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
                 BT m1 -> xpres H L SP X m1 m2 -> (forall b, In b TB -> In b L) -> aceil <= SP ->
                 (forall b, In b TB -> avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) ->
                 mem_inv asegs m2 -> BT m2)
             (FRESH : fresh_frame H LF 6 ff fp).
  (* [comment removed for export] *)
  Hypothesis AUXV : aauxv_ok m B.
  Local Notation SH := (Z.shiftr ff 3 + ASHB).

  (* [comment removed for export] *)
  Local Notation adwkGc := (adwkG H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 w224).
  Local Notation adwkc := (adwk H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 w224).
  Local Notation drestc := (drest LB p A nA pbin Bb nB TB).
  Local Notation dffc := (dff sp fp n fj24 tpb fj128 fj2).
  Local Notation dfshc := (dfsh e5).
  Local Notation dsg2c := (dsg2 st ff w224).
  Local Notation dsg1c := (dsg1 A Bb bt).
  Local Notation "'DCT' f" := (f H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 w224) (at level 10, f at level 0).
  Local Notation "'DCJ' f" := (f H HX RAISE PF9new PF9free ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LIB LB LF M x st mb lo B S R ds errv CH
                                 VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE
                                 p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 w224 NAR NBR MST POS BTR BT_frame FRESH)
    (at level 10, f at level 0).
  Local Notation adwkG_esc := (adwkG_es H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M x st mb lo B S R ds CH CTX p A nA pbin Bb nB bs R' TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 w224).
  Local Notation adwkG_hfc := (adwkG_heap_facts H HX ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 w224).

  (* [comment removed for export] *)
  Hypothesis TIME : atime_stmt H.

  Let SS00 : set_shadow_00_stmt := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HX)))))).

  (* [comment removed for export] *)
  Local Notation KADVc := (DCT dK_adv).
  Local Notation KSKc := (DCT dK_skip).
  Local Notation KTAc := (DCT dK_tailA).
  Local Notation KTZc := (DCT dK_tailZ).
  Local Notation KTXc := (DCT dK_tailX).
  Local Notation RPESc := (DCT rp_entry_stmt).
  Local Notation dbudc := (dbud H).
  (* [comment removed for export] *)
  Local Notation adwkG_wc := (DCJ adwkG_w).
  Local Notation adwkG_xc := (DCJ adwkG_x).
  Local Notation adwkG_libXc := (DCJ adwkG_libX).
  Local Notation adwk_raisec := (DCJ adwk_raise).
  Local Notation drest_subc := (drest_sub LIB LB SUBL p A nA pbin Bb nB TB).
  Local Notation drest_idsc := (drest_ids LB p A nA pbin Bb nB TB).

  (* [comment removed for export] *)
  Lemma rc_facts_c :
       S = store_empty (es_id S) /\ In (es_id S, st, STORE_SIZE) L0c /\ ablock_range H st STORE_SIZE
    /\ (forall b, In b L0c -> ablock_range H (blk_addr b) (blk_size b)) /\ (forall b, In b LB -> In b L0c)
    /\ List.NoDup (map blk_id L0c) /\ 9152 <= READCFG_STACK M /\ 0 <= lo /\ MEMFLAG m 1
    /\ (forall b', In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> In b' L0c)
    /\ (forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) ->
          blk_addr b + blk_size b + 16 <= blk_addr b' \/ blk_addr b' + blk_size b' + 16 <= blk_addr b)
    /\ afsb_ok H /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
    /\ rp_s1 (bv_unsigned sp) mod 32 = 0 /\ bv_unsigned sp - 432 <= rp_s1 (bv_unsigned sp) <= bv_unsigned sp - 416 /\ bv_unsigned sp < 2^64.
  Proof. exact (RCI rc_facts). Qed.


  (* [comment removed for export] *)
  Definition AENT0 (pe : bptr) : entrep := mkENT 0 0 None 0 0 None 0 0 None 0 0 0 None 0 0 0 0 None pe.
  Definition AENT1 (pe : bptr) : entrep := mkENT AECH_VERSION 0 None 0 0 None 0 0 None 0 0 0 None 0 0 0 0 None pe.

  (* [comment removed for export] *)
  Lemma ade_facts : forall Lx NB S' M' LE fr1 wee fr3 tpl shb shd um uf m' s',
    adwkGc Lx NB S' M' LE fr1 wee fr3 tpl shb shd um uf m' s' ->
       aceil <= S1c /\ bv_unsigned sp - 432 <= S1c <= bv_unsigned sp - 416 /\ S1c mod 32 = 0 /\ bv_unsigned sp < 2^64
    /\ 0 < Bb /\ Bb + zlength bs <= aceil /\ In (pbin, Bb, nB) (mid_errblocks M' ++ drestc Lx NB LE) /\ zlength bs <= nB /\ nB < 1500
    /\ (forall b, In b Lx -> Bb + nB <= blk_addr b \/ blk_addr b + blk_size b <= Bb)
    /\ (forall b, In b (mid_errblocks M' ++ drestc Lx NB LE) -> blk_addr b + blk_size b <= aceil)
    /\ (forall b, In b (mid_errblocks M' ++ drestc Lx NB LE) -> ablock_range H (blk_addr b) (blk_size b))
    /\ mid_flag M' = 1 /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'
    /\ accessible m' Bb nB /\ aapp Bb nB /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
    /\ lo <= S1c - 9152 + 432 /\ 0 <= lo.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH.
    intros until s'. intros DW.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (BRS & ND & DISJ & D2 & D1).
    pose proof (drest_subc Lx NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    assert (IB2 : In (pbin, Bb, nB) (mid_errblocks M' ++ drestc Lx NB LE)) by (apply in_or_app; right; exact IB).
    pose proof (BRS _ IB2) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
    pose proof LM1 as (IM & MF & _ & _ & _ & _ & _ & _ & GM & _). pose proof STP as (F1 & _). rewrite F1 in MF.
    pose proof NBR as NBRq. unfold zlength in NBRq |- *. unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBRq.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - clear - CEIL LO STK0 Q2; lia.
    - clear - Q2; lia.
    - clear - Q2; lia.
    - clear - E5 NBRq; lia.
    - clear - NBRq; lia.
    - clear - NBRq; lia.
    - intros b Hb. pose proof (DISJ b (pbin, Bb, nB) ltac:(apply in_or_app; right; apply SLX; exact Hb) IB2 ltac:(apply (D2 b (pbin, Bb, nB) Hb); exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (drest_subc [] NB LE))))))))) as K.
      cbn [blk_addr blk_size fst snd] in K. clear - K. lia.
    - intros b Hb. pose proof (BRS _ Hb) as (_ & _ & _ & _ & K5 & _). exact K5.
    - eapply (addressable_accessible _ _ _ _ _ ADb1); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI; clear - E5 ACB; lia].
    - clear - ACB; lia.
    - clear - ACB; lia.
    - clear - LO STK0 Q2; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma alx_not_client : forall Lx NB LE M' s' m' b a,
    as_RHEAP H s' (mid_errblocks M' ++ drestc Lx NB LE) m' -> In b Lx -> blk_addr b <= a < blk_addr b + blk_size b -> aceil <= S1c ->
    aclient_addr H (mid_errblocks M' ++ drestc [] NB LE) S1c a -> False.
  Proof using HH HX.
    intros Lx NB LE M' s' m' b a HP' Hb Ha AS1 HC.
    assert (BIN' : In b (mid_errblocks M' ++ drestc Lx NB LE)) by (apply in_or_app; right; rewrite drest_app; apply in_or_app; left; exact Hb).
    pose proof (ah_nodup H HH _ _ _ HP') as ND. destruct (drest_idsc _ _ _ _ ND) as (D1 & D2 & _).
    refine (ECH_AC14_kit.blk_not_client H HX _ _ _ (mid_errblocks M' ++ drestc [] NB LE) S1c b a HP' BIN' _ _ AS1 Ha HC).
    - intros b' Hb'. apply in_app_or in Hb'. apply in_or_app. destruct Hb' as [Hb'|Hb']; [left; exact Hb'| right; rewrite drest_app; apply in_or_app; right; exact Hb'].
    - intros b' Hb'. apply in_app_or in Hb'. destruct Hb' as [Hb'|Hb'].
      + intros E. apply (D1 b' b Hb' ltac:(rewrite drest_app; apply in_or_app; left; exact Hb)). exact E.
      + intros E. apply (D2 b b' Hb Hb'). symmetry. exact E.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_efree : forall Lx NB S' M' LE fr1 wee fr3 tpl shb shd um uf m1 s1' msF1 mo1 (ee : Z) (oe : option entrep) (rax : Z)
      (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word) (Q : config -> Prop),
    adwkGc Lx NB S' M' LE fr1 wee fr3 tpl shb shd um uf m1 s1' ->
    match oe with None => ee = 0 /\ Lx = [] | Some E => ENTRYobj (drestc Lx NB LE) m1 ee E /\ ENTRY_shad m1 ee E /\ Permutation (blocks_ENTRY ee E) Lx end ->
    0 <= rax < 2^64 -> rax mod 2 = 0 -> pf_ok (as_TR H) PF_entryfree rax CH1c ->
    uf + lb_bytes Lx <= DECODE_CUM_BYTES -> um <= DECODE_CUM_BYTES ->
    as_VIS H s1' msF1 = MS (mkR (Z_to_bv 64 rax) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 ee) b1 b2 b3 b4 b5 b6 b7
                                s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                        F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m1 (seg_rom asegs) ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    (forall m2 (s2' : as_St H) msF2 mo2 (v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 : word),
       adwkGc [] NB S' M' LE fr1 wee fr3 tpl shb shd um (uf + lb_bytes Lx) m2 s2' ->
       as_VIS H s2' msF2 = MS (mkR (Z_to_bv 64 rax) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) v0 v1 v2 sp (Z_to_bv 64 S1c) c0 c1 c2 c3 c4 c5 c6 c7
                                   s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w v3 v4 v5 v6)
                           F (ret_pc (Z_to_bv 64 rax)) fc None m2 (seg_rom asegs) ->
       as_AKREL H s2' (mkCfg msF2 mo2) -> as_MPRES H mo mo2 -> as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH.
    intros until Q. intros DW OE RAXR RAXE PF0 UFB UMB VIS1 KREL1 MP1 K.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof (dec_stack M M' STP) as (_ & _ & _ & _ & STKE & _).
    assert (AS1 : aceil <= S1c) by (clear - CEIL LO STK0 Q2; lia).
    assert (CHBx : forall fp' ra', In (fp', ra') CH1c -> S1c + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    pose proof LM1 as (IM1' & MFq1 & _ & _ & _ & _ & _ & _ & GM1 & GE1 & _). pose proof STP as (MF1' & _). rewrite MF1' in MFq1.
    pose proof (ah_costs H HH) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd).
    destruct oe as [E|].
    - destruct OE as (EO & ESH & PE).
      set (Lall := mid_errblocks M' ++ drestc Lx NB LE) in *.
      assert (INall : forall b, In b (drestc Lx NB LE) -> In b Lall) by (intros b Hb; unfold Lall; apply in_or_app; right; exact Hb).
      pose proof (ah_nodup H HH _ _ _ HP1) as ND. 
      assert (NDX : List.NoDup (map blk_id Lx)).
      { unfold Lall, drest in ND. rewrite map_app in ND. apply List.NoDup_app_remove_l in ND. rewrite map_app in ND. exact (List.NoDup_app_remove_r _ _ ND). }
      assert (NDE : List.NoDup (map blk_id (blocks_ENTRY ee E))) by (eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PE| exact NDX]).
      pose proof (lb_bytes_perm _ _ PE) as LBE.
      assert (LX0 : Forall (fun b => 0 <= blk_size b) (blocks_ENTRY ee E)).
      { apply Forall_forall. intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP1 (INall _ ltac:(unfold drest; apply in_or_app; left; exact (Permutation_in _ PE Hb)))) as (_ & _ & E3 & _). exact E3. }
      destruct (fe_entry_cost_bound H HH _ _ _ _ EO LX0) as [LXN ECB]. rewrite LBE in LXN, ECB.
      pose proof (aentryfree_spec H HH) as EF. unfold entryfree_stmt, efree_stmt_at in EF.
      eapply (ah_seq H HH).
      { eapply EF with (p := ee) (x := E) (lo := lo) (B := B) (LB := Lall) (s := s1') (errv := errv1) (CH := CH1c); clear EF.
        all: try first [exact VIS1| exact HP1| exact KREL1| exact AUX1| exact MI1| exact CEIL| exact AC1| exact CHN1| exact ESH| exact NDE| exact IM1'| exact GM1| exact GE1| exact ERR1].
        all: lazymatch goal with
             | |- _ = Z_to_bv _ _ => reflexivity
             | |- Z_to_bv 64 ATP = _ => reflexivity
             | |- ENTRYobj _ _ _ _ => eapply ENTRYobj_LB_mono; [exact EO| exact INall]
             | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
             | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST1
             | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKE Q2; lia
             | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
             | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact (CHBx _ _ Hin)
             | |- pf_ok _ _ _ _ => rewrite unsigned_lit by (clear - RAXR; lia); exact PF0
             | |- entry_cost _ _ <= _ => pose proof ((RCI LEDGER_pay) s1' um uf 0 (lb_bytes Lx) LED1 ltac:(clear; lia) LXN ltac:(clear - UMB; lia) UFB) as PAYq; pose proof (CM0 0 ltac:(clear; lia)) as CMz; clear - PAYq CMz ECB; lia
             | |- bv_unsigned _ mod 2 = 0 => rewrite unsigned_lit by (clear - RAXR; lia); exact RAXE
             | |- ?G => idtac "EFREE_LEFT" G
             end. }
      clear EF. intros [msF2 mo2] PO. unfold efree_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & s2' & LB2 & VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & PL & HP2 & XP2 & IM2 & GM2 & GE2 & AL2).
      rewrite (unsigned_lit S1c) in ST2, XP2 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
      (* [comment removed for export] *)
      pose proof (nd_app _ _ ND) as [D1 NDa]. unfold drest in NDa. destruct (nd_app _ _ NDa) as [D2 _].
      assert (PL2 : Permutation LB2 (mid_errblocks M' ++ drestc [] NB LE)).
      { apply (Permutation_app_inv_l (blocks_ENTRY ee E)). transitivity Lall; [exact PL|]. unfold Lall. rewrite (drest_app LB p A nA pbin Bb nB TB Lx NB LE).
        rewrite (app_assoc (mid_errblocks M') Lx). transitivity ((Lx ++ mid_errblocks M') ++ drestc [] NB LE); [apply Permutation_app_tail; apply Permutation_app_comm|].
        rewrite <- app_assoc. apply Permutation_app_head || (apply Permutation_app; [apply Permutation_sym; exact PE| apply Permutation_refl]). }
      eapply (K m2 s2' msF2 mo2 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6); [| exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)].
      eapply ((DCJ adwkG_x) Lx [] NB S' M' LE fr1 wee fr3 tpl shb shd um uf um (uf + lb_bytes Lx) m1 s1' m2 s2' errv1);
        [exact DW| | eapply PERM; [exact HP2| exact PL2]| exact MI2| exact AC2| exact ST2| exact AUX2| exact ERR2|].
      + eapply (xpres_weaken H); [exact XP2| apply Z.le_refl| | intros q Hq; exact Hq]. intros b Hb. eapply (Permutation_in _ (Permutation_sym PL2)). exact Hb.
      + pose proof ((RCI LEDGER_step) s1' s2' um uf 0 (lb_bytes Lx) LED1 ltac:(clear; lia) LXN) as LS. rewrite Z.add_0_r in LS. apply LS. pose proof (CM0 0 ltac:(clear; lia)) as CMz. clear - AL2 ECB CMz. lia.
    - destruct OE as [-> ->].
      pose proof aentryfree_null_spec as EFN. unfold entryfree_null_stmt, sknull_stmt_at in EFN.
      eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply EFN with (lo := lo); clear EFN;
        [rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST1| exact CEIL| rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); unfold ENTRYFREE_STACK, FR_EVP_PKEY_free in STKE; clear - LO STKE Q2; lia| exact MI1| exact AC1]|].
      clear EFN. intros msF2 mo2 KREL2 MP2 PO. unfold sknull_post in PO.
      destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & VIS2 & MU2 & WM2 & MI2 & AC2 & ST2).
      rewrite (unsigned_lit S1c) in MU2, ST2 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
      assert (T12 : forall A' cs, rw_cells asegs m1 A' cs -> (A' + Z.of_nat (cells_size cs) <= lo \/ S1c <= A') -> rw_cells asegs m2 A' cs).
      { intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU2| exact WM2|]. cbn. split; [clear - HA; lia| exact I]. }
      pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
      change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
      pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AFS_SIZE in AF2.
      assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
      pose proof FF1 as [[WFf _] _]. unfold dff, arp_fframe2 in WFf. cbn in WFf.
      eapply (K m2 s1' msF2 mo2 v0 v1 v2 (Z_to_bv 64 0) c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6); [| exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)].
      cbn [lb_bytes fold_right]. rewrite Z.add_0_r.
      eapply ((DCJ adwkG_w) [] NB S' M' LE fr1 wee fr3 tpl shb shd um uf m1 s1' m2 [(lo, S1c)] fr1 wee fr3 tpl shb shd);
        [exact DW| exact MU2| exact WM2| exact MI2| exact ST2| apply Forall_cons; [left; cbn; split; apply Z.le_refl| apply Forall_nil]
        | apply T12; [exact FR1| right; clear; lia]| exact SZ1| apply T12; [exact FR2| right; clear; lia]| apply T12; [exact FR3| right; clear; lia]| exact SZ3
        | apply T12; [exact FF1| left; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - FQ6 AF2 CEIL; lia]
        | apply T12; [exact FSH1| left; unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length];
                      pose proof (sh_add8 ff 512) as SY8; replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia); pose proof (sh_mono (ff + 4096) _ FQ6) as SYU; pose proof (sh_mono _ _ AF2) as SYA;
                      unfold sh, ASHB in *; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear - SY8 SYU SYA SHC CEIL; rewrite ?ASHADOW_BASE_val in *; lia]
        | exact LSH1].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mid_step_refl_c : forall M', mid_step M M' -> mid_step M' M'.
  Proof. clear. intros M' (F1 & _). split; [exact F1|]. split; [intros b K; exact K|]. split; [intros c K; exact K| intros K; exact K]. Qed.
  Lemma mid_newlib_nil_c : forall M', mid_newlib_ok M' M' [].
  Proof.
    clear. intros M'. exists [], []. split; [apply Permutation_refl|].
    split; [destruct (mid_ctx M'); reflexivity| destruct (mid_err M'); reflexivity].
  Qed.
  Lemma M_eq1c : forall M', mid_step M M' -> mkMID 1 (mid_ctx M') (mid_err M') (mid_E M') (mid_vdso M') = M'.
  Proof. clear. intros [f c e E0 v] (F1 & _). cbn in *. subst. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma asg3_split3 : forall m A1 x0 x1 x2 n0 n1 n2 p0 p1 p2,
    rw_cells asegs m A1 (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) ->
    rw_cells asegs m A1 [C8 x0; C8 x1; C8 x2] /\ rw_cells asegs m (A1 + 24) [C8 n0; C8 n1; C8 n2] /\ rw_cells asegs m (A1 + 48) [C8 p0; C8 p1; C8 p2].
  Proof.
    clear. intros until p2. intros RC.
    change (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) with ([C8 x0; C8 x1; C8 x2] ++ [C8 n0; C8 n1; C8 n2] ++ [C8 p0; C8 p1; C8 p2]) in RC.
    apply rw_cells_app in RC. destruct RC as [R1 RC]. apply rw_cells_app in RC. destruct RC as [R2 R3].
    cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ] in R2, R3. replace (A1 + 24 + 24) with (A1 + 48) in R3 by lia.
    split; [exact R1|]. split; [exact R2| exact R3].
  Qed.
  Lemma asg3_join3 : forall m A1 x0 x1 x2 n0 n1 n2 p0 p1 p2,
    rw_cells asegs m A1 [C8 x0; C8 x1; C8 x2] -> rw_cells asegs m (A1 + 24) [C8 n0; C8 n1; C8 n2] -> rw_cells asegs m (A1 + 48) [C8 p0; C8 p1; C8 p2] ->
    rw_cells asegs m A1 (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2).
  Proof.
    clear. intros until p2. intros R1 R2 R3.
    change (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) with ([C8 x0; C8 x1; C8 x2] ++ [C8 n0; C8 n1; C8 n2] ++ [C8 p0; C8 p1; C8 p2]).
    apply rw_cells_app. split; [exact R1|]. apply rw_cells_app. cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]. split; [exact R2|].
    replace (A1 + 24 + 24) with (A1 + 48) by lia. exact R3.
  Qed.

  (* [comment removed for export] *)
  Definition upd_pub (E : entrep) (len P : Z) (o : oblk) : entrep :=
    mkENT (en_version E) (en_pname E) (en_pname_o E) len P o (en_nsuites E) (en_suites E) (en_suites_o E) (en_maxname E) (en_cfgid E)
          (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
  Definition entry_pre (E : entrep) (pad1 : list byte) : list cell := [C2 (wz (en_version E)); CB 6 pad1; C8 (wz (en_pname E))].
  Definition entry_suf (E : entrep) (pad2 pad3 pad4 : list byte) : list cell :=
    [C4 (wz (en_nsuites E)); CB 4 pad2; C8 (wz (en_suites E)); C1 (b8 (en_maxname E)); C1 (b8 (en_cfgid E)); CB 6 pad3;
     C8 (wz (en_exts E)); C8 (wz (en_loadtime E)); C8 (wz 0); C4 (wz (en_forretry E)); CB 4 pad4; C8 (wz (en_enclen E)); C8 (wz (en_encoded E))].
  Lemma entry_split_pub : forall m ee E pad1 pad2 pad3 pad4,
    rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) ->
    rw_cells asegs m ee (entry_pre E pad1) /\ rw_cells asegs m (ee + 16) [C8 (wz (en_publen E))] /\ rw_cells asegs m (ee + 24) [C8 (wz (en_pub E))]
    /\ rw_cells asegs m (ee + 32) (entry_suf E pad2 pad3 pad4).
  Proof.
    clear. intros until pad4. intros RC.
    change (entry_cells E pad1 pad2 pad3 pad4) with (entry_pre E pad1 ++ [C8 (wz (en_publen E))] ++ [C8 (wz (en_pub E))] ++ entry_suf E pad2 pad3 pad4) in RC.
    apply rw_cells_app in RC. destruct RC as [P RC]. apply rw_cells_app in RC. destruct RC as [L RC]. apply rw_cells_app in RC. destruct RC as [D RC].
    cbn [entry_pre entry_suf cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ] in L, D, RC.
    replace (ee + 16 + 8) with (ee + 24) in D by lia. replace (ee + 16 + 8 + 8) with (ee + 32) in RC by lia.
    split; [exact P|]. split; [exact L|]. split; [exact D| exact RC].
  Qed.
  Lemma entry_join_pub : forall m ee E pad1 pad2 pad3 pad4 len P o,
    rw_cells asegs m ee (entry_pre E pad1) -> rw_cells asegs m (ee + 16) [C8 (wz len)] -> rw_cells asegs m (ee + 24) [C8 (wz P)] ->
    rw_cells asegs m (ee + 32) (entry_suf E pad2 pad3 pad4) ->
    rw_cells asegs m ee (entry_cells (upd_pub E len P o) pad1 pad2 pad3 pad4).
  Proof.
    clear. intros until o. intros P1 L1 D1 S1.
    change (entry_cells (upd_pub E len P o) pad1 pad2 pad3 pad4) with (entry_pre E pad1 ++ [C8 (wz len)] ++ [C8 (wz P)] ++ entry_suf E pad2 pad3 pad4).
    apply rw_cells_app. split; [exact P1|]. apply rw_cells_app. cbn [entry_pre entry_suf cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]. split; [exact L1|].
    apply rw_cells_app. cbn [entry_pre entry_suf cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ].
    replace (ee + 16 + 8) with (ee + 24) by lia. replace (ee + 24 + 8) with (ee + 32) by lia. split; [exact D1| exact S1].
  Qed.

  (* [comment removed for export] *)
  Definition upd_pname (E : entrep) (P : Z) (o : oblk) : entrep :=
    mkENT (en_version E) P o (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E) (en_maxname E) (en_cfgid E)
          (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
  Definition entry_pre0 (E : entrep) (pad1 : list byte) : list cell := [C2 (wz (en_version E)); CB 6 pad1].
  Definition entry_suf16 (E : entrep) (pad2 pad3 pad4 : list byte) : list cell := [C8 (wz (en_publen E))] ++ [C8 (wz (en_pub E))] ++ entry_suf E pad2 pad3 pad4.
  Lemma entry_split_pname : forall m ee E pad1 pad2 pad3 pad4,
    rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) ->
    rw_cells asegs m ee (entry_pre0 E pad1) /\ rw_cells asegs m (ee + 8) [C8 (wz (en_pname E))] /\ rw_cells asegs m (ee + 16) (entry_suf16 E pad2 pad3 pad4).
  Proof.
    clear. intros until pad4. intros RC.
    change (entry_cells E pad1 pad2 pad3 pad4) with (entry_pre0 E pad1 ++ [C8 (wz (en_pname E))] ++ entry_suf16 E pad2 pad3 pad4) in RC.
    apply rw_cells_app in RC. destruct RC as [P RC]. apply rw_cells_app in RC. destruct RC as [L RC].
    cbn [entry_pre0 cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ] in L, RC. replace (ee + 8 + 8) with (ee + 16) in RC by lia.
    split; [exact P|]. split; [exact L| exact RC].
  Qed.
  Lemma entry_join_pname : forall m ee E pad1 pad2 pad3 pad4 P o,
    rw_cells asegs m ee (entry_pre0 E pad1) -> rw_cells asegs m (ee + 8) [C8 (wz P)] -> rw_cells asegs m (ee + 16) (entry_suf16 E pad2 pad3 pad4) ->
    rw_cells asegs m ee (entry_cells (upd_pname E P o) pad1 pad2 pad3 pad4).
  Proof.
    clear. intros until o. intros P1 L1 S1.
    change (entry_cells (upd_pname E P o) pad1 pad2 pad3 pad4) with (entry_pre0 E pad1 ++ [C8 (wz P)] ++ entry_suf16 E pad2 pad3 pad4).
    apply rw_cells_app. split; [exact P1|]. apply rw_cells_app. cbn [entry_pre0 cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]. split; [exact L1|].
    replace (ee + 8 + 8) with (ee + 16) by lia. exact S1.
  Qed.

  (* [comment removed for export] *)
  Lemma abytes_at_sub : forall m A zs i n,
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
  (* [comment removed for export] *)
  Lemma adwkG_xw : forall Lx Lx' NB S' M' LE fr1 wee fr3 tpl shb shd um uf um' uf' m1 s1' m2 s2' (X : list (Z * Z)) (fr1' fr3' : list cell) (errv2 : word),
    adwkGc Lx NB S' M' LE fr1 wee fr3 tpl shb shd um uf m1 s1' ->
    xpres H (mid_errblocks M' ++ drestc Lx NB LE) S1c X m1 m2 ->
    Forall (fun iv : Z * Z => (S1c + 16 <= fst iv /\ snd iv <= S1c + 144) \/ (S1c + 240 <= fst iv /\ snd iv <= S1c + 312)
                              \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) X ->      (* [comment removed for export] *)
    as_RHEAP H s2' (mid_errblocks M' ++ drestc Lx' NB LE) m2 -> mem_inv asegs m2 -> ACONST m2 -> stk asegs m2 lo S1c ->
    as_rauxv_ok H m2 B -> rw_cells asegs m2 (errno_addr (Z_to_bv 64 ATP)) [C4 errv2] -> as_RFS H (LF1c ff fp) m2 -> LEDGERc s2' um' uf' ->
    rw_cells asegs m2 (S1c + 16) fr1' -> cells_size fr1' = 128%nat -> rw_cells asegs m2 (S1c + 240) fr3' -> cells_size fr3' = 72%nat ->
    adwkGc Lx' NB S' M' LE fr1' wee fr3' tpl shb shd um' uf' m2 s2'.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH.
    intros until errv2. intros DW XP FX HP2 MI2 AC2 STK2 AUX2 ERR2 RFS2 LED2 FR1' SZ1' FR3' SZ3'.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (AS1 & Q2 & Q1 & SPR & BP & BH & IB2 & NBL & NB15 & BLX & BEL & BRS & F1 & MF & IM & GM & ACCB & APB & ACB & LOS & LO0).
    destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (_ & ND & DISJ & D2 & D1).
    pose proof (drest_subc Lx NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof (drest_subc [] NB LE) as (SLB0 & _ & SLE0 & SNB0 & STB0 & IB0 & IA0 & _ & S30 & SLL0).
    set (Lall := mid_errblocks M' ++ drestc Lx NB LE) in *.
    assert (INX : forall b, In b Lx -> In b Lall) by (intros b Hb; subst Lall; apply in_or_app; right; apply SLX; exact Hb).
    assert (IN0 : forall b, In b (drestc [] NB LE) -> In b Lall) by (intros b Hb; subst Lall; apply in_or_app; right; apply SL0; exact Hb).
    assert (HBL : forall b, In b Lx -> blk_addr b + blk_size b <= aceil) by (intros b Hb; exact (BEL b (INX _ Hb))).
    (* [comment removed for export] *)
    assert (LM2 : LIBMID (LE ++ LIB) m2 M').
    { eapply (LIBMID_xobj H HH s1' m1 (LE ++ LIB) Lall S1c X [(S1c + 16, S1c + 152); (S1c + 240, S1c + 312)] Lx m1 m2 M' x);
        [exact HP1| exact LM1| rewrite CTX1; exact CTX| exact XP| | | exact INX| | |].
      - intros b Hb. apply IN0. apply SLL0. exact Hb.
      - intros b Hb. subst Lall. apply in_or_app. left. exact Hb.
      - intros b b' Hb Hb' EQ. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        + exact (D2 _ _ Hb' (SLL0 _ Hb) (eq_sym EQ)).
        + exact (D1 _ _ Hb (SLX _ Hb') EQ).
      - apply Forall_cons; [left; cbn [fst]; clear - AS1; lia|]. apply Forall_cons; [left; cbn [fst]; clear - AS1; lia| apply Forall_nil].
      - intros a Ha. destruct (rin_ivs_In _ _ Ha) as (iv & Hiv & Ra). pose proof (proj1 (Forall_forall _ _) FX iv Hiv) as K.
        destruct K as [K|[K|(b & Hb & K1 & K2)]].
        + right. cbn. left. clear - K Ra. lia.
        + right. cbn. right; left. clear - K Ra. lia.
        + left. exists b. split; [exact Hb| clear - K1 K2 Ra; lia]. }
    (* [comment removed for export] *)
    assert (FR2' : rw_cells asegs m2 (S1c + 144) (dsg2c wee)).
    { eapply (xpres_rw_cells' H); [exact XP| exact FR2| left; clear; lia|].
      apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FX iv Hiv) as K. unfold dsg2, arp_sg2. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ].
      destruct K as [K|[K|(b & Hb & K1 & K2)]]; [clear - K; lia| clear - K; lia| pose proof (HBL b Hb); clear - H0 K1 K2 AS1; lia]. }
    eapply (adwkG_libXc Lx Lx' NB S' M' M' LE [] fr1 wee fr3 tpl shb shd um uf um' uf' m1 s1' m2 s2' X [] fr1' wee fr3' errv2);
      [exact DW| cbn [app]; exact LM2| apply mid_step_refl_c; exact STP| apply mid_newlib_nil_c| reflexivity| exact EC| exact EB
      | eapply (xpres_weaken H); [exact XP| apply Z.le_refl| intros b Hb; subst Lall; apply in_or_app; right; exact Hb| intros a Ha; apply rin_ivs_app; left; exact Ha]
      | eapply Forall_impl; [| exact FX]; cbn beta; intros iv [K|[K|K]]; [left; clear - K; lia| right; left; exact K| right; right; exact K]
      | apply Forall_nil| cbn [app]; exact HP2| exact MI2| exact AC2| exact STK2| exact AUX2| exact ERR2| exact RFS2| exact LED2
      | exact FR1'| exact SZ1'| exact FR2'| exact FR3'| exact SZ3'].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition same_blocks (E E' : entrep) : Prop :=
    en_id E' = en_id E /\ en_pname E' = en_pname E /\ en_pname_o E' = en_pname_o E /\ en_pub E' = en_pub E /\ en_pub_o E' = en_pub_o E
    /\ en_suites E' = en_suites E /\ en_suites_o E' = en_suites_o E /\ en_encoded E' = en_encoded E /\ en_encoded_o E' = en_encoded_o E
    /\ en_exts E' = en_exts E /\ en_exts_o E' = en_exts_o E.
  Lemma same_blocks_ENTRY : forall ee E E', same_blocks E E' -> blocks_ENTRY ee E' = blocks_ENTRY ee E.
  Proof. clear. intros ee E E' (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11). unfold blocks_ENTRY. rewrite Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11. reflexivity. Qed.
  Lemma eshad_same : forall m ee E E', same_blocks E E' -> ENTRY_shad m ee E -> ENTRY_shad m ee E'.
  Proof. clear. intros m ee E E' (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11) ESH. unfold ENTRY_shad in *. rewrite Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11. exact ESH. Qed.
  (* [comment removed for export] *)
  Lemma eobj_same_cells : forall LBq m1 m2 ee E E' pad1 pad2 pad3 pad4,
    ENTRYobj LBq m1 ee E -> same_blocks E E' -> en_exts_o E = None ->
    length pad1 = 6%nat -> length pad2 = 4%nat -> length pad3 = 6%nat -> length pad4 = 4%nat ->
    rw_cells asegs m2 ee (entry_cells E' pad1 pad2 pad3 pad4) -> ENTRYobj LBq m2 ee E'.
  Proof.
    clear. intros LBq m1 m2 ee E E' pad1 pad2 pad3 pad4 (_ & EIN & O1 & O2 & O3 & O4 & XT) (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11) XO L1 L2 L3 L4 EC.
    unfold ENTRYobj. rewrite Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11. rewrite XO in XT |- *. cbn [EXTS] in XT |- *.
    split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact EC]|].
    split; [exact EIN|]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4| exact XT].
  Qed.
  (* [comment removed for export] *)
  Lemma eobj_cells : forall LBq m ee E, ENTRYobj LBq m ee E ->
    exists pad1 pad2 pad3 pad4, length pad1 = 6%nat /\ length pad2 = 4%nat /\ length pad3 = 6%nat /\ length pad4 = 4%nat /\ rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4).
  Proof. clear. intros LBq m ee E ((pad1 & pad2 & pad3 & pad4 & K) & _). exists pad1, pad2, pad3, pad4. exact K. Qed.

  (* [comment removed for export] *)
  Lemma ade_subblocks : forall Lx NB S' M' LE fr1 wee fr3 tpl shb shd um uf m' s' ee E,
    adwkGc Lx NB S' M' LE fr1 wee fr3 tpl shb shd um uf m' s' -> Permutation (blocks_ENTRY ee E) Lx ->
    forall b, In b (blocks_of (en_pname E) (en_pname_o E) ++ blocks_of (en_pub E) (en_pub_o E) ++ blocks_of (en_suites E) (en_suites_o E)
                   ++ blocks_of (en_encoded E) (en_encoded_o E) ++ blocks_EXTS (en_exts E) (en_exts_o E)) ->
      In b Lx /\ In b (mid_errblocks M' ++ drestc Lx NB LE) /\ ablock_range H (blk_addr b) (blk_size b)
      /\ (blk_addr b + blk_size b + 16 <= ee \/ ee + ENTRY_SIZE + 16 <= blk_addr b).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH.
    intros until E. intros DW PE b Hb.
    destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (BRS & ND & DISJ & D2 & D1).
    pose proof (drest_subc Lx NB LE) as (_ & _ & _ & _ & _ & _ & _ & SLX & _).
    assert (INE : In b (blocks_ENTRY ee E)) by (right; exact Hb).
    assert (INX : In b Lx) by (eapply Permutation_in; [exact PE| exact INE]).
    assert (INL : In b (mid_errblocks M' ++ drestc Lx NB LE)) by (apply in_or_app; right; apply SLX; exact INX).
    assert (INH : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M' ++ drestc Lx NB LE)).
    { apply in_or_app; right; apply SLX. eapply Permutation_in; [exact PE| left; reflexivity]. }
    assert (NDX : List.NoDup (map blk_id Lx)).
    { unfold drest in ND. rewrite map_app in ND. apply List.NoDup_app_remove_l in ND. rewrite map_app in ND. exact (List.NoDup_app_remove_r _ _ ND). }
    assert (NDE : List.NoDup (map blk_id (blocks_ENTRY ee E))) by (eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PE| exact NDX]).
    assert (NE : blk_id b <> blk_id (en_id E, ee, ENTRY_SIZE)).
    { unfold blocks_ENTRY in NDE. rewrite map_cons in NDE. inversion NDE as [|xq lq NI NDq EQ]. subst. intros EQ. apply NI. rewrite <- EQ. apply in_map. exact Hb. }
    split; [exact INX|]. split; [exact INL|]. split; [exact (BRS _ INL)|].
    pose proof (DISJ _ _ INL INH NE) as K. cbn [blk_addr blk_size fst snd] in K. exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma eshad_acrossW : forall W m1 m2 ee E,
    ENTRY_shad m1 ee E -> munch W m1 m2 -> wmono asegs m1 m2 -> 0 <= ee ->
    Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W ->
    (forall b, In b (blocks_of (en_pname E) (en_pname_o E) ++ blocks_of (en_pub E) (en_pub_o E) ++ blocks_of (en_suites E) (en_suites_o E)
                    ++ blocks_of (en_encoded E) (en_encoded_o E)) -> 0 <= blk_addr b < AAPP_HI /\ disjoint_from W (blk_addr b) (blk_size b)) ->
    en_exts_o E = None ->
    ENTRY_shad m2 ee E.
  Proof.
    clear. intros W m1 m2 ee E (ETOP & EAD & O1 & O2 & O3 & O4 & XSH) MU WM EE0 FW SUB XO.
    assert (OSH : forall P o, (forall i n, o = Some (i, n) -> In (i, P, n) (blocks_of (en_pname E) (en_pname_o E) ++ blocks_of (en_pub E) (en_pub_o E) ++ blocks_of (en_suites E) (en_suites_o E)
                    ++ blocks_of (en_encoded E) (en_encoded_o E))) -> oshad m1 P o -> oshad m2 P o).
    { intros P [[i n]|] INo OS; [| exact I]. pose proof (SUB _ (INo i n eq_refl)) as [B0 DJ]. cbn [blk_addr blk_size fst snd] in B0, DJ.
      eapply (ECH_AC14_decexts.oshad_acrossW W m1 m2 P (Some (i, n))); [exact OS| exact MU| exact WM| | exact FW]. split; [| exact DJ]. exact B0. }
    unfold ENTRY_shad. split; [exact ETOP|]. split.
    - eapply (ECH_AC14_decexts.addressable_acrossW W m1 m2); [exact EAD| exact MU| exact WM| unfold AAPP_HI, ENTRY_SIZE in *; lia| exact ETOP| exact FW].
    - split; [apply OSH; [intros i n Eo; rewrite Eo; apply in_or_app; left; left; reflexivity| exact O1]|].
      split; [apply OSH; [intros i n Eo; rewrite Eo; apply in_or_app; right; apply in_or_app; left; left; reflexivity| exact O2]|].
      split; [apply OSH; [intros i n Eo; rewrite Eo; do 2 (apply in_or_app; right); apply in_or_app; left; left; reflexivity| exact O3]|].
      split; [apply OSH; [intros i n Eo; rewrite Eo; do 3 (apply in_or_app; right); left; reflexivity| exact O4]|].
      rewrite XO. exact I.
  Qed.
  Lemma in_ext5 : forall (b : block) (A B C D X : list block), In b (A ++ B ++ C ++ D) -> In b (A ++ B ++ C ++ D ++ X).
  Proof. clear. intros b A B C D X K. rewrite !in_app_iff in *. tauto. Qed.

  (* [comment removed for export] *)
  Lemma asuite_cells_eq : forall rows, asuite_cells rows = suite_cells rows.
  Proof. clear. induction rows as [|[[k d] a] rows IH]; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.
  Lemma asrows_ok : forall bsq off kem k, 0 <= kem < 2^16 -> Forall row_ok (srows bsq off kem k).
  Proof.
    clear. intros bsq off kem k KR. revert off. induction k as [|k IH]; intros off; cbn; constructor; [| apply IH].
    unfold row_ok. cbn [fst snd]. pose proof (bz_range bsq off). pose proof (bz_range bsq (Datatypes.S off)). pose proof (bz_range bsq (Datatypes.S (Datatypes.S off))). pose proof (bz_range bsq (Datatypes.S (Datatypes.S (Datatypes.S off)))). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma asg2_216 : forall m A1 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232,
    rw_cells asegs m A1 (arp_sg2 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232) -> rw_cells asegs m (A1 + 72) [C8 w216].
  Proof.
    clear. intros until w232. intros RC.
    change (arp_sg2 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232) with ([C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208] ++ [C8 w216] ++ [C8 w224; C8 w232]) in RC.
    apply rw_cells_app in RC. destruct RC as [_ RC]. apply rw_cells_app in RC. destruct RC as [RC _]. cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ] in RC. exact RC.
  Qed.
  (* [comment removed for export] *)
  Lemma nodup_hd_ne : forall (x y : block) (l : list block), List.NoDup (map blk_id (x :: l)) -> In y l -> blk_id y <> blk_id x.
  Proof. clear. intros x y l ND IN. rewrite map_cons in ND. inversion ND as [|xq lq NI NDq EQ]. subst. intros EQ. apply NI. rewrite <- EQ. apply in_map. exact IN. Qed.
  (* [comment removed for export] *)
  Lemma ade_nodup : forall Lx NB S' M' LE fr1 wee fr3 tpl shb shd um uf m' s' (Lb : list block),
    adwkGc Lx NB S' M' LE fr1 wee fr3 tpl shb shd um uf m' s' -> Permutation Lb Lx -> List.NoDup (map blk_id Lb).
  Proof using HX.
    intros until Lb. intros DW PE. destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (_ & ND & _).
    assert (NDX : List.NoDup (map blk_id Lx)).
    { unfold drest in ND. rewrite map_app in ND. apply List.NoDup_app_remove_l in ND. rewrite map_app in ND. exact (List.NoDup_app_remove_r _ _ ND). }
    eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PE| exact NDX].
  Qed.
  (* [comment removed for export] *)
  Lemma amemchr_res_range : forall A1 c k buf, 0 <= A1 -> 0 <= memchr_res A1 c k buf <= A1 + Z.of_nat (length buf) /\ (memchr_res A1 c k buf = 0 -> 0 < A1 -> find_byte c (firstn (Z.to_nat k) buf) = None).
  Proof.
    clear. intros A1 c k buf A0. unfold memchr_res. destruct (find_byte c (firstn (Z.to_nat k) buf)) as [i|] eqn:FB.
    - pose proof (find_byte_Some _ _ _ FB) as (Hi & _). rewrite length_firstn in Hi. split; [lia|]. intros E P. exfalso. lia.
    - split; [lia|]. intros _ _. reflexivity.
  Qed.
  Lemma afind_byte_None_notin : forall c l, find_byte c l = None -> 0 <= c < 256 -> ~ In (Z_to_bv 8 c) l.
  Proof.
    clear. intros c l FB CR IN. apply In_nth_error in IN. destruct IN as [j Hj].
    apply (find_byte_None _ _ FB _ _ Hj). rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8%N) with 256. rewrite Z.mod_small by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma astrnlen_full : forall ns, ~ In (Z_to_bv 8 0) ns -> strnlen ns = length ns.
  Proof.
    clear. induction ns as [|b ns IH]; intros NI; [reflexivity|]. cbn [strnlen length].
    destruct (bv_unsigned b =? 0) eqn:E.
    - exfalso. apply NI. left. apply Z.eqb_eq in E. apply bv_eq. rewrite E. reflexivity.
    - f_equal. apply IH. intros K. apply NI. right. exact K.
  Qed.
  Lemma astrndup_bytes : forall m D ns, rw_cells asegs m D [CB (length ns) ns; C1 (b8 0)] -> bytes_at asegs m D (ns ++ [Z_to_bv 8 0]).
  Proof. clear. intros m D ns [[_ BA] _]. cbn [cells_bytes cbytes app] in BA. rewrite ?app_nil_r in BA. exact BA. Qed.
  (* [comment removed for export] *)
  Lemma errph_step_le : forall M1 M2, mid_step M1 M2 -> errph_bytes (mid_err M2) <= errph_bytes (mid_err M1) /\ errph_cnt (mid_err M2) <= errph_cnt (mid_err M1).
  Proof.
    clear. intros M1 M2 (_ & _ & SE & _). pose proof (errph_bytes_range (mid_err M2)) as [B2 C2].
    destruct (mid_err M1) as [|c1] eqn:E1; [cbn [errph_bytes errph_cnt]; unfold ERRINIT_BYTES; lia|].
    rewrite (SE c1 eq_refl). lia.
  Qed.
  Lemma PF_decexts_mstep : forall M1 M2, mid_step M1 M2 -> incl (PF_decexts (mid_err M2)) (PF_decexts (mid_err M1)).
  Proof.
    clear. intros M1 M2 ST. unfold PF_decexts.
    repeat (apply incl_app_app; [apply incl_refl|]). apply incl_app_app; [apply (pf_raise_mstep _ _ _ _ _ ST)| apply incl_refl].
  Qed.
  Lemma PF_fcc_mstep : forall M1 M2, mid_step M1 M2 -> incl (PF_fcc (mid_err M2)) (PF_fcc (mid_err M1)).
  Proof.
    clear. intros M1 M2 ST. unfold PF_fcc.
    apply incl_app_app; [apply incl_refl|]. apply incl_app_app; [apply pf_shift_mono; apply (PF_suitebad_mstep _ _ ST)|].
    apply incl_app_app; [apply incl_refl|]. apply incl_app_app; [apply incl_refl|].
    apply incl_app_app; [apply (pf_raise_mstep _ _ _ _ _ ST)|]. apply incl_app_app; [apply (pf_raise_mstep _ _ _ _ _ ST)|]. apply (pf_raise_mstep _ _ _ _ _ ST).
  Qed.
  (* [comment removed for export] *)
  Lemma aCm_mulk : forall k a, 0 <= k -> 0 <= a -> k * as_Cm H a <= as_Cm H (k * a).
  Proof using HH.
    clear - HH. intros k a K0 Aa0. pose proof (ah_costs H HH) as (CM0 & _ & _ & _ & CMadd & _).
    revert K0. apply (Wf_Z.natlike_ind (fun k => k * as_Cm H a <= as_Cm H (k * a))).
    - rewrite !Z.mul_0_l. pose proof (CM0 0 ltac:(lia)). lia.
    - intros j J0 IH. rewrite !Z.mul_succ_l. pose proof (CMadd (j * a) a ltac:(nia) Aa0). lia.
  Qed.
  Lemma aCf_mulk : forall k a, 0 <= k -> 0 <= a -> k * as_Cf H a <= as_Cf H (k * a).
  Proof using HH.
    clear - HH. intros k a K0 Aa0. pose proof (ah_costs H HH) as (_ & _ & CF0 & _ & _ & CFadd).
    revert K0. apply (Wf_Z.natlike_ind (fun k => k * as_Cf H a <= as_Cf H (k * a))).
    - rewrite !Z.mul_0_l. pose proof (CF0 0 ltac:(lia)). lia.
    - intros j J0 IH. rewrite !Z.mul_succ_l. pose proof (CFadd (j * a) a ltac:(nia) Aa0). lia.
  Qed.

  Lemma aerrph_delta_bounds : forall eph LEn c, errph_delta eph LEn c ->
    Z.of_nat (length LEn) + errph_cnt (ErrReady c) <= errph_cnt eph /\ lb_bytes LEn + errph_bytes (ErrReady c) <= errph_bytes eph.
  Proof.
    clear. intros [|c0] LEn c DL; cbn [errph_delta errph_cnt errph_bytes] in *.
    - destruct DL as (Q1 & Q2 & _). lia.
    - destruct DL as [_ ->]. cbn. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma anewlib_len : forall M1 M2 LEn, mid_step M1 M2 -> mid_newlib_ok M1 M2 LEn -> mid_ctx M1 = mid_ctx M ->
       Z.of_nat (length LEn) + errph_cnt (mid_err M2) <= errph_cnt (mid_err M1) /\ lb_bytes LEn + errph_bytes (mid_err M2) <= errph_bytes (mid_err M1).
  Proof using CTX.
    clear - CTX. intros M1 M2 LEn STP2 NEW2 CTX1. destruct NEW2 as (LA & LE2 & PM & CA & CE). rewrite CTX1, CTX in CA. destruct STP2 as (_ & _ & SE2 & _).
    subst LA. cbn [app] in PM.
    destruct (mid_err M1) as [|c1] eqn:Eq1; destruct (mid_err M2) as [|c2] eqn:Eq2.
    - rewrite CE in PM. apply Permutation_sym in PM. apply Permutation_nil in PM. subst LEn. cbn. clear. lia.
    - pose proof (aerrph_delta_bounds _ _ _ CE) as [Q1 Q2]. rewrite (Permutation_length PM), (lb_bytes_perm _ _ PM). clear - Q1 Q2. lia.
    - discriminate (SE2 c1 eq_refl).
    - rewrite CE in PM. apply Permutation_sym in PM. apply Permutation_nil in PM. subst LEn. cbn. clear. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma EXTS_frameX : forall L0 SP X m m' ee E,
    ENTRYobj L0 m ee E -> xpres H L0 SP X m m' ->
    (forall b, In b (blocks_EXTS (en_exts E) (en_exts_o E)) -> avoids X (blk_addr b) (blk_size b)) ->
    EXTS L0 m' (en_exts E) (en_exts_o E).
  Proof.
    clear. intros L0 SP X m m' ee E EO XP AV. pose proof EO as (_ & _ & _ & _ & _ & _ & XT).
    revert XT AV. unfold EXTS. destruct (en_exts_o E) as [[K es]|]; intros XT AV; [| exact XT].
    destruct XT as (PP & SO & LEN & F2). rewrite ECH_AC14_kit.blocks_EXTS_some in AV.
    split; [exact PP|]. split; [| split; [exact LEN|]].
    - eapply (ECH_AC14_kit.SKobj_frameX H); [exact SO| exact XP| |].
      + exact (AV _ ltac:(apply in_or_app; left; left; reflexivity)).
      + intros NC. exact (AV _ ltac:(apply in_or_app; left; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NC); right; left; reflexivity)).
    - eapply (ECH_AC14_kit.EXTs_frameX H); [exact F2| exact XP|]. intros b Hb. exact (AV _ ltac:(apply in_or_app; right; exact Hb)).
  Qed.

  Lemma EXTS_shad_frameX : forall LB L0 SP X m m' ee E,
    ENTRY_shad m ee E -> ENTRYobj LB m ee E -> xpres H L0 SP X m m' ->
    (forall b, In b (blocks_EXTS (en_exts E) (en_exts_o E)) -> In b L0 /\ avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) ->
    EXTS_shad m' (en_exts E) (en_exts_o E).
  Proof.
    clear. intros LB L0 SP X m m' ee E ESH EO XP AV. pose proof ESH as (_ & _ & _ & _ & _ & _ & XSH). pose proof EO as (_ & _ & _ & _ & _ & _ & XT).
    revert XSH XT AV. unfold EXTS_shad, EXTS. destruct (en_exts_o E) as [[K es]|]; intros XSH XT AV; [| exact I].
    destruct XSH as ((SKSH & T1 & T2) & F2SH). destruct XT as (PP & SO & LEN & F2). rewrite ECH_AC14_kit.blocks_EXTS_some in AV.
    split.
    - split; [| split; [exact T1| exact T2]]. destruct SKSH as [SKH SKD]. split.
      + pose proof (AV _ ltac:(apply in_or_app; left; left; reflexivity)) as (I1 & _ & Y1). eapply (addressable_xpres_blkX H); [exact I1| exact T1| exact SKH| exact XP| exact Y1].
      + intros NC. pose proof (AV _ ltac:(apply in_or_app; left; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NC); right; left; reflexivity)) as (I1 & _ & Y1).
        eapply (addressable_xpres_blkX H); [exact I1| exact (T2 NC)| exact (SKD NC)| exact XP| exact Y1].
    - eapply (ECH_AC14_kit.EXTs_shad_xpresX H); [exact F2SH| exact XP|]. intros b Hb. exact (AV _ ltac:(apply in_or_app; right; exact Hb)).
  Qed.

  (* [comment removed for export] *)
  Lemma eobj_updX : forall L0 SP X m1 m2 ee E E' pad1 pad2 pad3 pad4,
    ENTRYobj L0 m1 ee E -> same_blocks E E' ->
    length pad1 = 6%nat -> length pad2 = 4%nat -> length pad3 = 6%nat -> length pad4 = 4%nat ->
    rw_cells asegs m2 ee (entry_cells E' pad1 pad2 pad3 pad4) ->
    xpres H L0 SP X m1 m2 -> (forall b, In b (blocks_EXTS (en_exts E) (en_exts_o E)) -> avoids X (blk_addr b) (blk_size b)) ->
    ENTRYobj L0 m2 ee E'.
  Proof.
    clear. intros L0 SP X m1 m2 ee E E' pad1 pad2 pad3 pad4 EO SB L1 L2 L3 L4 EC XP AV.
    pose proof (EXTS_frameX _ _ _ _ _ _ _ EO XP AV) as XT2.
    pose proof EO as (_ & EIN & O1 & O2 & O3 & O4 & _). pose proof SB as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
    unfold ENTRYobj. rewrite Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11.
    split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact EC]|].
    split; [exact EIN|]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4| exact XT2].
  Qed.

  (* [comment removed for export] *)
  Lemma eshad_updX : forall LB L0 SP X m1 m2 ee E E',
    ENTRY_shad m1 ee E -> ENTRYobj LB m1 ee E -> same_blocks E E' -> xpres H L0 SP X m1 m2 ->
    In (en_id E, ee, ENTRY_SIZE) L0 -> shavoids X ee ENTRY_SIZE ->
    (forall b, In b (blocks_of (en_pname E) (en_pname_o E) ++ blocks_of (en_pub E) (en_pub_o E) ++ blocks_of (en_suites E) (en_suites_o E)
                    ++ blocks_of (en_encoded E) (en_encoded_o E) ++ blocks_EXTS (en_exts E) (en_exts_o E)) ->
        In b L0 /\ avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) ->
    ENTRY_shad m2 ee E'.
  Proof.
    clear. intros LB L0 SP X m1 m2 ee E E' ESH EO SB XP EIN SAVE AV.
    pose proof (EXTS_shad_frameX _ _ _ _ _ _ _ _ ESH EO XP ltac:(intros b Hb; apply AV; do 4 (apply in_or_app; right); exact Hb)) as XSH2.
    pose proof ESH as (ETOP & EAD & ES1 & ES2 & ES3 & ES4 & _). pose proof EO as (_ & _ & O1 & O2 & O3 & O4 & _).
    pose proof SB as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
    assert (OSH : forall Pf o, ofield LB Pf o -> (forall b, In b (blocks_of Pf o) -> In b L0 /\ avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) ->
                  oshad m1 Pf o -> oshad m2 Pf o).
    { intros Pf o OFo INE OSo. eapply (ECH_AC14_kit.oshad_xpresX H); [| exact OSo| exact XP]. destruct o as [[i1 n1]|]; [| exact I].
      pose proof (INE (i1, Pf, n1) ltac:(left; reflexivity)) as (I1 & A1' & Y1). cbn [blk_addr blk_size fst snd] in A1', Y1. split; [exact I1|]. split; [exact A1'| exact Y1]. }
    unfold ENTRY_shad. rewrite Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11.
    split; [exact ETOP|]. split; [eapply (addressable_xpres_blkX H); [exact EIN| exact ETOP| exact EAD| exact XP| exact SAVE]|].
    split; [apply (OSH _ _ O1); [intros b Hb; apply AV; apply in_or_app; left; exact Hb| exact ES1]|].
    split; [apply (OSH _ _ O2); [intros b Hb; apply AV; apply in_or_app; right; apply in_or_app; left; exact Hb| exact ES2]|].
    split; [apply (OSH _ _ O3); [intros b Hb; apply AV; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb| exact ES3]|].
    split; [apply (OSH _ _ O4); [intros b Hb; apply AV; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb| exact ES4]| exact XSH2].
  Qed.
  (* [comment removed for export] *)
  Local Notation adwkG_timec := ((DCJ adwkG_time) AUXV).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma aCm_mul : forall k n, 0 <= k -> 0 <= n -> k * as_Cm H n <= as_Cm H (k * n).
  Proof using HX.
    clear - HX. intros k n K N. pose proof (ah_costs H (proj1 HX)) as (CM0 & _ & _ & _ & CMadd & _).
    revert k K. refine (natlike_ind _ _ _).
    - rewrite !Z.mul_0_l. pose proof (CM0 0 ltac:(apply Z.le_refl)). lia.
    - intros x X IH. pose proof (CMadd (x * n) n ltac:(clear - X N; nia) N) as AD.
      replace (Z.succ x * n) with (x * n + n) by (clear; lia). replace (Z.succ x * as_Cm H n) with (x * as_Cm H n + as_Cm H n) by (clear; lia). clear - IH AD. lia.
  Qed.
  Lemma aCf_mul : forall k n, 0 <= k -> 0 <= n -> k * as_Cf H n <= as_Cf H (k * n).
  Proof using HX.
    clear - HX. intros k n K N. pose proof (ah_costs H (proj1 HX)) as (_ & _ & CF0 & _ & _ & CFadd).
    revert k K. refine (natlike_ind _ _ _).
    - rewrite !Z.mul_0_l. pose proof (CF0 0 ltac:(apply Z.le_refl)). lia.
    - intros x X IH. pose proof (CFadd (x * n) n ltac:(clear - X N; nia) N) as AD.
      replace (Z.succ x * n) with (x * n + n) by (clear; lia). replace (Z.succ x * as_Cf H n) with (x * as_Cf H n + as_Cf H n) by (clear; lia). clear - IH AD. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fcc_cost_lump : forall Mq ns, 1 <= ns ->
    FCC_COST H Mq ns <= as_Cm H (560 + errph_bytes (mid_err Mq) + 64 * ns) + as_Cf H (568 + errph_bytes (mid_err Mq) + 64 * ns).
  Proof using HX.
    intros Mq ns NS. pose proof (ah_costs H (proj1 HX)) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd). pose proof (errph_bytes_range (mid_err Mq)) as [E0 _].
    unfold FCC_COST, ADD1HOST_COST, ADD1HOST_BYTES, RAISE_COST, RCR, raise_bytes, VPM_SIZE, XBUF_SIZE, SK_SIZE, ERRDEBUG_BYTES.
    pose proof (CMadd 136 16 ltac:(clear; lia) ltac:(clear; lia)) as QA1. pose proof (CMadd (136 + 16) 256 ltac:(clear; lia) ltac:(clear; lia)) as QA2.
    pose proof (CMadd (136 + 16 + 256) 56 ltac:(clear; lia) ltac:(clear; lia)) as QA3. pose proof (CMadd (136 + 16 + 256 + 56) 32 ltac:(clear; lia) ltac:(clear; lia)) as QA4.
    pose proof (CMadd (136 + 16 + 256 + 56 + 32) (errph_bytes (mid_err Mq) + 64) ltac:(clear; lia) ltac:(clear - E0; lia)) as QA5.
    pose proof (CMadd (136 + 16 + 256 + 56 + 32 + (errph_bytes (mid_err Mq) + 64)) (ns * 64) ltac:(clear - E0; lia) ltac:(clear - NS; lia)) as QA6.
    pose proof (aCm_mul ns 64 ltac:(clear - NS; lia) ltac:(clear; lia)) as QA7.
    pose proof (CFadd 0 0 ltac:(clear; lia) ltac:(clear; lia)) as QB0. pose proof (CF0 0 ltac:(clear; lia)) as QB00. rewrite Z.add_0_l in QB0.
    pose proof (CFadd (136 + (16 + 264 + 56 + 32)) (errph_bytes (mid_err Mq) + 64) ltac:(clear; lia) ltac:(clear - E0; lia)) as QB1.
    pose proof (CFadd (136 + (16 + 264 + 56 + 32) + (errph_bytes (mid_err Mq) + 64)) (ns * 64) ltac:(clear - E0; lia) ltac:(clear - NS; lia)) as QB2.
    pose proof (aCf_mul ns 64 ltac:(clear - NS; lia) ltac:(clear; lia)) as QB3.
    replace (560 + errph_bytes (mid_err Mq) + 64 * ns) with (136 + 16 + 256 + 56 + 32 + (errph_bytes (mid_err Mq) + 64) + ns * 64) by (clear; lia).
    replace (568 + errph_bytes (mid_err Mq) + 64 * ns) with (136 + (16 + 264 + 56 + 32) + (errph_bytes (mid_err Mq) + 64) + ns * 64) by (clear; lia).
    clear - QA1 QA2 QA3 QA4 QA5 QA6 QA7 QB0 QB00 QB1 QB2 QB3. lia.
  Qed.
  Lemma fcc_spent_lump : forall Mq Mq' ns, 1 <= ns -> errph_bytes (mid_err Mq') <= errph_bytes (mid_err Mq) ->
    FCC_SPENT H Mq Mq' ns <= as_Cm H (496 + (errph_bytes (mid_err Mq) - errph_bytes (mid_err Mq') + ERRDEBUG_BYTES) + 64 * ns)
                          + as_Cf H (504 + (errph_bytes (mid_err Mq) - errph_bytes (mid_err Mq') + ERRDEBUG_BYTES) + 64 * ns).
  Proof using HX.
    intros Mq Mq' ns NS LE. pose proof (ah_costs H (proj1 HX)) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd).
    set (d := errph_bytes (mid_err Mq) - errph_bytes (mid_err Mq') + ERRDEBUG_BYTES). assert (D0 : 0 <= d) by (subst d; unfold ERRDEBUG_BYTES; clear - LE; lia).
    unfold FCC_SPENT, ADD1HOST_COST, ADD1HOST_BYTES, RAISE_COSTd, RCR, VPM_SIZE, XBUF_SIZE, SK_SIZE. fold d. unfold ERRDEBUG_BYTES.
    pose proof (CMadd 136 16 ltac:(clear; lia) ltac:(clear; lia)) as QA1. pose proof (CMadd (136 + 16) 256 ltac:(clear; lia) ltac:(clear; lia)) as QA2.
    pose proof (CMadd (136 + 16 + 256) 56 ltac:(clear; lia) ltac:(clear; lia)) as QA3. pose proof (CMadd (136 + 16 + 256 + 56) 32 ltac:(clear; lia) ltac:(clear; lia)) as QA4.
    pose proof (CMadd (136 + 16 + 256 + 56 + 32) d ltac:(clear; lia) D0) as QA5.
    pose proof (CMadd (136 + 16 + 256 + 56 + 32 + d) (ns * 64) ltac:(clear - D0; lia) ltac:(clear - NS; lia)) as QA6.
    pose proof (aCm_mul ns 64 ltac:(clear - NS; lia) ltac:(clear; lia)) as QA7.
    pose proof (CFadd 0 0 ltac:(clear; lia) ltac:(clear; lia)) as QB0. pose proof (CF0 0 ltac:(clear; lia)) as QB00. rewrite Z.add_0_l in QB0.
    pose proof (CFadd (136 + (16 + 264 + 56 + 32)) d ltac:(clear; lia) D0) as QB1.
    pose proof (CFadd (136 + (16 + 264 + 56 + 32) + d) (ns * 64) ltac:(clear - D0; lia) ltac:(clear - NS; lia)) as QB2.
    pose proof (aCf_mul ns 64 ltac:(clear - NS; lia) ltac:(clear; lia)) as QB3.
    replace (496 + d + 64 * ns) with (136 + 16 + 256 + 56 + 32 + d + ns * 64) by (clear; lia).
    replace (504 + d + 64 * ns) with (136 + (16 + 264 + 56 + 32) + d + ns * 64) by (clear; lia).
    clear - QA1 QA2 QA3 QA4 QA5 QA6 QA7 QB0 QB00 QB1 QB2 QB3. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma de_phase8 : forall (cur rem elen : Z) (Lx NB : list block) (S' : storerep) (M' M2 : libmid) (LE2 : list block)
      (w24 w32 w48 w56 w64 w72 : word) (x0 x1 x2 n0 n1 n2 p0 p1 p2 : word) (um uf um0 uf0 : Z)
      (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model) (ee : Z) (E : entrep) (rows : list (Z * Z * Z)) (nm : list byte) (pS : bptr) (sn : Z) (pn : bptr)
      (u0 u1 u2 a1w a2w a3w a4w a5w a6w a7w s2w s4w s5w s6w s8w s9w s10w s11w u3 u4 u5 u6 : word),
    adwkGc Lx NB S' M2 LE2 (dsg1c w24 w32 (wz (cur + 4)) w48 w56 w64 w72 (wz (rem - 4)) (wz elen) (wz cur)) (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) 0 (b8 0) (poison_bytes 256 0) um uf m' s' ->
    mid_step M M' -> mid_step M' M2 ->
    ENTRYobj (drestc Lx NB LE2) m' ee E -> ENTRY_shad m' ee E -> Permutation (blocks_ENTRY ee E) Lx ->
    en_loadtime E = 0 -> en_forretry E = 0 ->
    1 <= en_nsuites E < 2^31 -> en_suites_o E = Some (pS, sn) -> rw_cells asegs m' (en_suites E) (suite_cells rows) -> zlength rows = en_nsuites E -> 6 * en_nsuites E <= sn ->
    Forall row_ok rows -> 4 * en_nsuites E <= elen ->
    en_pname_o E = Some (pn, zlength nm + 1) -> bytes_at asegs m' (en_pname E) (nm ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) nm -> 1 <= zlength nm <= 255 ->
    5 * Z.of_nat (length Lx) <= 2 * (elen + 4) -> lb_bytes Lx <= ENTRY_KEPT elen ->
    19 <= elen -> 4 + elen <= rem -> Bb + 2 <= cur -> cur + rem <= Bb + zlength bs ->
    dbudc (drestc Lx NB LE2) M2 PUSH_HB (FCC_CNT + ERRSTR_CNT) ->
    um <= um0 + 3304 * elen + (errph_bytes (mid_err M') - errph_bytes (mid_err M2)) ->
    uf <= uf0 + 2100 * elen + (errph_bytes (mid_err M') - errph_bytes (mid_err M2)) ->
    um0 + errph_bytes (mid_err M') + ENTRY_CM rem <= DECODE_CUM_BYTES -> uf0 + errph_bytes (mid_err M') + ENTRY_CF rem <= DECODE_CUM_BYTES -> nent S' <= 65 ->
    KADVc cur rem NB S' um0 uf0 (mid_err M') -> KTXc NB S' ->
    as_VIS H s' msF' = MS (mkR (Z_to_bv 64 ADE_R8) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 0) a1w a2w a3w a4w a5w a6w a7w
                                s2w (Z_to_bv 64 SH) s4w s5w s6w (Z_to_bv 64 ASHB) s8w s9w s10w s11w u3 u4 u5 u6)
                        F (Z_to_bv 64 P_time) fc None m' (seg_rom asegs) ->
    as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
    as_SR H POSTc (mkCfg msF' mo').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH AUXV TIME.
    intros until u6. intros DW STP1 STP2 EO ESH PE LT0 FRY0 NSR SUO SC RWL SO6 RWO NS4 PNO PNB NONUL NMR LXC LXB EL19 ELR BC CR DB UMQ UFQ UMB UFB NENT KADV KTX VIS1 KREL1 MP1.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (AS1 & Q2 & Q1 & SPR & BP & BH & IB2 & NBL & NB15 & BLX & BEL & BRS & F1 & MF & IM & GM & ACCB & APB & ACB & LOS & LO0).
    destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (_ & ND & DISJ & D2 & D1).
    destruct rc_facts_c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AFSB & _). pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (SHL : ASHB + AIMG_TOP / 8 <= SH) by (unfold ASHB, AIMG_TOP; rewrite Z.shiftr_div_pow2 by (clear; lia); clear - FQ1; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (SHU : SH + 512 < AHI_LO) by (rewrite SHF; unfold sh, AHI_LO; rewrite ASHADOW_BASE_val; clear - FQ2 ACB; lia).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
    pose proof (dec_stack M M2 STP) as DSK. pose proof (errph_bytes_range (mid_err M2)) as [EBR' ECR'].
    pose proof (errph_step_le _ _ STP2) as [EPH12 EPC12]. pose proof (errph_step_le _ _ STP1) as [EPH01 EPC01].
    pose proof (ah_costs H HH) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd).
    pose proof LM1 as (_ & _ & _ & _ & _ & VD1 & _ & _ & _ & _ & _ & _ & _ & _ & RL1 & _).
    assert (CHBx : forall fp' ra', In (fp', ra') CH1c -> S1c + 16 <= fp').
    { intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    (* [comment removed for export] *)
    pose proof (drest_subc Lx NB LE2) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    assert (EINx : In (en_id E, ee, ENTRY_SIZE) Lx) by (eapply Permutation_in; [exact PE| left; reflexivity]).
    assert (EIN : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M2 ++ drestc Lx NB LE2)) by (apply in_or_app; right; apply SLX; exact EINx).
    pose proof (BRS _ EIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
    pose proof (aapp_not_shadowland _ _ E7) as ENS. unfold ENTRY_SIZE in E5, E6, ENS. unfold AIMG_TOP in E4. unfold AFS_SIZE in E6.
    (* [comment removed for export] *)
    idtac "P8_TIME".
    pose proof TIME as TM. unfold atime_stmt, atime_stmt_at in TM.
    eapply (ah_seq H HH).
    { eapply TM with (lo := lo) (B := B) (LB := mid_errblocks M2 ++ drestc Lx NB LE2) (s := s') (vf := if mid_vdso M2 then 0 else P_cgt_init) (errv := errv1); clear TM.
      all: try first [exact VIS1| exact HP1| exact KREL1| exact AUX1| exact MI1| exact CEIL| exact AC1| exact ERR1| exact RL1| exact VD1].
      all: lazymatch goal with
           | |- _ = Z_to_bv _ _ => reflexivity
           | |- Z_to_bv 64 ATP = _ => reflexivity
           | |- aauxv_ok _ B => exact ((DCJ adwkG_auxv) AUXV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW)
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - SPB Q2; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact ST1
           | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); unfold ATIME_STACK; clear - LOS; lia
           | |- (_ = 0 \/ _ = P_cgt_init) => destruct (mid_vdso M2); [left| right]; reflexivity
           | |- _ mod 2 = 0 => unfold ADE_R8; rewrite unsigned_lit by (clear; lia); reflexivity
           | |- ?G => idtac "TM_LEFT" G
           end. }
    clear TM. intros [msF2 mo2] PO. unfold atime_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & tv & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m2 & VIS2 & KREL2 & MP2 & MI2 & ST2 & AC2 & ERR2 & AUX2 & AAUX2 & HP2 & MU2 & WM2 & VD2).
    rewrite (unsigned_lit S1c) in MU2, ST2 by (clear - Q2 SPR CEIL LOS LO0; lia).
    (* [comment removed for export] *)
    set (M3 := mkMID (mid_flag M2) (mid_ctx M2) (mid_err M2) (mid_E M2) true).
    pose proof (adwkG_timec Lx NB S' M2 LE2 _ _ _ _ _ _ _ _ _ _ m2 _ DW MU2 WM2 MI2 ST2 AC2 AUX2 HP2 VD2 ERR2) as DW2. fold M3 in DW2.
    assert (STP3 : mid_step M2 M3) by (subst M3; unfold mid_step; cbn [mid_flag mid_ctx mid_err mid_vdso]; split; [exact F1| split; [intros b0 Hb0; exact Hb0| split; [intros c0 Hc0; exact Hc0| intros _; reflexivity]]]).
    pose proof (mid_step_trans_ _ _ _ STP STP3) as STP03. pose proof (mid_step_trans_ _ _ _ STP2 STP3) as STP13.
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) /\ errno_addr (Z_to_bv 64 ATP) + 4 <= AIMG_TOP /\ 0 <= A_vdso_func /\ A_vdso_func + 8 <= AIMG_TOP) by (clear; unfold AIMG_TOP, A_vdso_func; vm_compute; repeat split; discriminate).
    pose proof ERNG as ERNG'. unfold errno_addr, A_vdso_func, AIMG_TOP in ERNG'. rewrite ?unsigned_lit in ERNG' by (clear; unfold ATP; lia).
    Local Ltac avlia B4 ERNG ERNG' := cbn [fst snd]; unfold errno_addr, A_vdso_func, AIMG_TOP; rewrite ?unsigned_lit by (clear; unfold ATP; lia); clear - B4 ERNG ERNG'; unfold AIMG_TOP in *; lia.
    assert (XT2 : xpres H (drestc Lx NB LE2) S1c [(A_vdso_func, A_vdso_func + 8); (errno_addr (Z_to_bv 64 ATP), errno_addr (Z_to_bv 64 ATP) + 4)]%Z m' m2).
    { eapply xpres_weaken; [eapply (xpres_of_munch H); [exact HH| exact HP1| exact MU2| exact WM2|]| apply Z.le_refl| intros b Hb; apply in_or_app; right; exact Hb| intros a Ha; exact Ha].
      apply Forall_cons; [left; cbn [fst snd]; unfold ATIME_STACK; clear - AS1 LOS CEIL; lia|].
      apply Forall_cons; [right; cbn [fst snd]; intros a Ha; cbn; left; exact Ha|].
      apply Forall_cons; [right; cbn [fst snd]; intros a Ha; cbn; right; left; exact Ha| apply Forall_nil]. }
    (* [comment removed for export] *)
    assert (SUBE : forall b, In b (blocks_ENTRY ee E) -> In b (drestc Lx NB LE2) /\ AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. assert (INX : In b Lx) by (eapply Permutation_in; [exact PE| exact Hb]). pose proof (BRS _ ltac:(apply in_or_app; right; apply SLX; exact INX)) as (_ & _ & B3 & B4 & B5 & _ & B7).
      split; [apply SLX; exact INX|]. split; [exact B4|]. split; [exact B5|]. split; [exact B3| exact B7]. }
    assert (AVT : forall b, In b (blocks_ENTRY ee E) -> avoids [(A_vdso_func, A_vdso_func + 8); (errno_addr (Z_to_bv 64 ATP), errno_addr (Z_to_bv 64 ATP) + 4)]%Z (blk_addr b) (blk_size b)
                                                   /\ shavoids [(A_vdso_func, A_vdso_func + 8); (errno_addr (Z_to_bv 64 ATP), errno_addr (Z_to_bv 64 ATP) + 4)]%Z (blk_addr b) (blk_size b)).
    { intros b Hb. destruct (SUBE b Hb) as (_ & B4 & _ & B3 & B7). pose proof (sh_mono _ _ B4) as SB4. assert (S0 : sh AIMG_TOP = 0x80172000) by reflexivity. rewrite S0 in SB4.
      unfold avoids, shavoids. split.
      - apply Forall_cons; [avlia B4 ERNG ERNG'|]. apply Forall_cons; [avlia B4 ERNG ERNG'| apply Forall_nil].
      - apply Forall_cons; [avlia SB4 ERNG ERNG'|]. apply Forall_cons; [avlia SB4 ERNG ERNG'| apply Forall_nil]. }
    assert (EO2 : ENTRYobj (drestc Lx NB LE2) m2 ee E) by (eapply (ENTRYobj_frameX H); [exact EO| exact XT2| intros b Hb; exact (proj1 (AVT b Hb))]).
    assert (ESH2 : ENTRY_shad m2 ee E) by (eapply (ENTRY_shad_frameX H); [exact ESH| exact EO| exact XT2| intros b Hb; split; [exact (proj1 (SUBE b Hb))| exact (AVT b Hb)]]).
    assert (SC2 : rw_cells asegs m2 (en_suites E) (suite_cells rows)).
    { pose proof (suite_cells_size rows) as SSZ. rewrite RWL in SSZ.
      eapply (xpres_rw_cells' H); [exact XT2| exact SC| right; right; left; exists (pS, en_suites E, sn); split; [apply (proj1 (SUBE _ ltac:(unfold blocks_ENTRY; right; rewrite SUO; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity)))| cbn; rewrite SSZ; clear - SO6 NSR; lia]|].
      destruct (SUBE (pS, en_suites E, sn) ltac:(unfold blocks_ENTRY; right; rewrite SUO; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as (_ & B4 & _). cbn [blk_addr fst snd] in B4.
      rewrite SSZ. apply Forall_cons; [avlia B4 ERNG ERNG'|]. apply Forall_cons; [avlia B4 ERNG ERNG'| apply Forall_nil]. }
    assert (PNB2 : bytes_at asegs m2 (en_pname E) (nm ++ [Z_to_bv 8 0])).
    { eapply (xpres_bytes_at' H); [exact XT2| exact PNB| right; right; left; exists (pn, en_pname E, zlength nm + 1); split; [apply (proj1 (SUBE _ ltac:(unfold blocks_ENTRY; right; rewrite PNO; apply in_or_app; left; left; reflexivity)))| cbn; rewrite length_app; cbn [length]; unfold zlength; clear; lia]|].
      destruct (SUBE (pn, en_pname E, zlength nm + 1) ltac:(unfold blocks_ENTRY; right; rewrite PNO; apply in_or_app; left; left; reflexivity)) as (_ & B4 & _). cbn [blk_addr fst snd] in B4.
      rewrite length_app. cbn [length]. apply Forall_cons; [avlia B4 ERNG ERNG'|]. apply Forall_cons; [avlia B4 ERNG ERNG'| apply Forall_nil]. }
    clear XT2 AVT.
    pose proof DW2 as (HP2' & LM2 & _ & NEW2 & CTX2 & EC2 & EB2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSb2 & _ & _ & _ & _ & _ & FR02 & FR12 & _ & FR22 & FR32 & _ & FRG2 & FRS2 & FF2 & FSH2 & _ & RFS2 & _ & _ & _ & _ & _ & STK2 & CHN2 & XA2 & LED2).
    (* [comment removed for export] *)
    idtac "P8_SEG13".
    pose proof (eobj_cells _ _ _ _ EO2) as (pad1 & pad2 & pad3 & pad4 & PL1 & PL2 & PL3 & PL4 & EC13).
    pose proof ESH2 as (ETOP2 & EAD2 & _).
    rewrite <- (Z_to_bv_bv_unsigned tv) in VIS2. pose proof (aword_range tv) as TVR.
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply ade_seg13 with (E := E) (ff := ff) (ee := ee);
      [exact SSF8| unfold dsg2 in FR22; exact FR22| unfold dfsh in FSH2; exact FSH2| exact SHL| exact SHU| clear - TVR; lia| exact EC13| clear - E4; lia| unfold ENTRY_SIZE; exact E5
      | eapply (addressable_accessible _ _ _ _ _ EAD2); [clear; lia| unfold ENTRY_SIZE; clear; lia| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia]
      | unfold ENTRY_SIZE; exact E7| exact AS1| clear - Q2 SPR; lia| exact MI2| exact AC2]|].
    intros msF3 mo3 KREL3 MP3 (z0 & z1 & z2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & z3 & z4 & z5 & z6 & m3 & VIS3 & MU3 & WM3 & MI3 & EC3 & FSH3 & AC3).
    set (Et := upd_loadtime E (bv_unsigned tv)) in EC3.
    assert (SBe : same_blocks E Et) by (subst Et; repeat split; reflexivity).
    pose proof ENS as ENS'. unfold ALOWSH_LO, AHI_LO in ENS'.
    pose proof (sh_in_shadowland ee ltac:(unfold AAPP_HI; clear - E1 E5 ACB; lia)) as SISe.
    pose proof (sh_nsh_high ee ENTRY_SIZE ltac:(clear - E1; lia) ltac:(unfold ENTRY_SIZE; clear; lia) ltac:(unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia)) as SNHe.
    unfold ALOWSH_LO, AHI_LO in SISe, SNHe.
    assert (ST3 : stk asegs m3 lo S1c) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - E5 CEIL FQ2 ACB AS1; lia]).
    assert (T23 : forall A' cs, rw_cells asegs m2 A' cs -> (A' + Z.of_nat (cells_size cs) <= ee + 64 \/ ee + 72 <= A') -> (A' + Z.of_nat (cells_size cs) <= SH + 4 \/ SH + 264 <= A') ->
                                rw_cells asegs m3 A' cs).
    { intros A' cs RC HA HB. eapply rw_cells_transport; [exact RC| exact MU3| exact WM3|]. cbn. split; [clear - HA; lia|]. clear - HB. lia. }
    assert (SHq : SH + 264 <= S1c) by (rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - FQ2 ACB AS1; lia).
    assert (SHff : ff + 4096 <= SH + 4 \/ SH + 264 <= ff).
    { pose proof (aapp_not_shadowland _ _ FB3) as NSF. rewrite SHF. unfold sh. rewrite ASHADOW_BASE_val. unfold ALOWSH_LO, AHI_LO, AFS_SIZE in NSF. clear - NSF FQ5 FQ6. lia. }
    assert (DW3 : adwkGc Lx NB S' M3 LE2 (dsg1c w24 w32 (wz (cur + 4)) w48 w56 w64 w72 (wz (rem - 4)) (wz elen) (wz cur)) (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) 0 (b8 0xf8) (poison_bytes 256 0xf8) um uf m3 s').
    { eapply (adwkG_wc Lx NB S' M3 LE2 _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) um uf m2 s' m3 [(ee + 64, ee + 72); (SH + 4, SH + 5); (SH + 8, SH + 264)]);
        [exact DW2| exact MU3| exact WM3| exact MI3| exact ST3|
        | apply T23; [exact FR12| right; clear - E5 AS1; lia| right; clear - SHq; lia]| reflexivity
        | apply T23; [exact FR22| right; clear - E5 AS1; lia| right; clear - SHq; lia]
        | apply T23; [exact FR32| right; clear - E5 AS1; lia| right; clear - SHq; lia]| reflexivity
        | apply T23; [exact FF2| unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - E6 FQ5 FQ6; lia
                    | unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SHff; lia]
        | unfold dfsh; exact FSH3| reflexivity].
      apply Forall_cons; [do 6 right; exists (en_id E, ee, ENTRY_SIZE); split; [exact EINx| cbn; unfold ENTRY_SIZE; clear; lia]|].
      apply Forall_cons; [right; right; right; right; left; cbn; split; apply Z.le_refl|]. apply Forall_cons; [do 5 right; left; cbn; split; apply Z.le_refl| apply Forall_nil]. }
    assert (XP23 : xpres H (drestc Lx NB LE2) S1c [(ee + 64, ee + 72); (SH + 4, SH + 5); (SH + 8, SH + 264)] m2 m3).
    { eapply (xpres_weaken H); [eapply (ECH_Xpres.xpres_of_munch H s' _ S1c [(ee + 64, ee + 72); (SH + 4, SH + 5); (SH + 8, SH + 264)] _ m2); [exact HH| exact HP2'| exact MU3| exact WM3|]
        | apply Z.le_refl| intros b Hb; apply in_or_app; right; exact Hb| intros a Ha; exact Ha].
      apply Forall_cons; [right; cbn [fst snd]; intros a Ha; cbn; left; exact Ha|].
      apply Forall_cons; [right; cbn [fst snd]; intros a Ha; cbn; right; left; exact Ha|].
      apply Forall_cons; [right; cbn [fst snd]; intros a Ha; cbn; right; right; left; exact Ha| apply Forall_nil]. }
    (* [comment removed for export] *)
    assert (SUBAV3 : forall b, In b (blocks_of (en_pname E) (en_pname_o E) ++ blocks_of (en_pub E) (en_pub_o E) ++ blocks_of (en_suites E) (en_suites_o E) ++ blocks_of (en_encoded E) (en_encoded_o E)
                                     ++ blocks_EXTS (en_exts E) (en_exts_o E)) ->
               In b Lx /\ avoids [(ee + 64, ee + 72); (SH + 4, SH + 5); (SH + 8, SH + 264)] (blk_addr b) (blk_size b)
               /\ shavoids [(ee + 64, ee + 72); (SH + 4, SH + 5); (SH + 8, SH + 264)] (blk_addr b) (blk_size b)).
    { intros b Hb. destruct (ade_subblocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW2 PE b Hb) as (INX & _ & BR & APT).
      pose proof BR as (B1 & _ & B3 & _ & B5 & B6 & B7). unfold ENTRY_SIZE in APT. unfold AFS_SIZE in B6.
      pose proof (aapp_not_shadowland _ _ B7) as NSb. unfold ALOWSH_LO, AHI_LO in NSb.
      split; [exact INX|]. split.
      - unfold avoids. apply Forall_cons; [cbn [fst snd]; clear - APT B3; lia|].
        apply Forall_cons; [cbn [fst snd]; rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - NSb B3 FQ1 FQ2 ACB; Z.div_mod_to_equations; lia|].
        apply Forall_cons; [cbn [fst snd]; rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - NSb B3 FQ1 FQ2 ACB; Z.div_mod_to_equations; lia| apply Forall_nil].
      - pose proof (sh_in_shadowland (blk_addr b) ltac:(clear - B1 B3 B5 ACB; unfold AAPP_HI; lia)) as SIS.
        pose proof (sh_nsh_high (blk_addr b) (blk_size b) ltac:(clear - B1; lia) B3 ltac:(clear - B1 B3 B5 ACB; unfold AAPP_HI; lia)) as SNH.
        unfold shavoids. apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; clear - SIS SNH ENS' APT; lia|].
        apply Forall_cons; [cbn [fst snd]; rewrite SHF; unfold sh, nsh; rewrite ASHADOW_BASE_val; clear - B6 B3 B1 FQ5 FQ6; Z.div_mod_to_equations; lia|].
        apply Forall_cons; [cbn [fst snd]; rewrite SHF; unfold sh, nsh; rewrite ASHADOW_BASE_val; clear - B6 B3 B1 FQ5 FQ6; Z.div_mod_to_equations; lia| apply Forall_nil]. }
    assert (EO3 : ENTRYobj (drestc Lx NB LE2) m3 ee Et).
    { eapply (eobj_updX _ S1c _ m2 m3); [exact EO2| exact SBe| exact PL1| exact PL2| exact PL3| exact PL4| exact EC3| exact XP23|].
      intros b Hb. exact (proj1 (proj2 (SUBAV3 b ltac:(do 4 (apply in_or_app; right); exact Hb)))). }
    assert (ESH3 : ENTRY_shad m3 ee Et).
    { eapply (eshad_updX (drestc Lx NB LE2) (drestc Lx NB LE2) S1c _ m2 m3); [exact ESH2| exact EO2| exact SBe| exact XP23| apply SLX; exact EINx| |].
      - unfold shavoids. apply Forall_cons; [cbn [fst snd]; clear - ENS' SISe SNHe; lia|].
        apply Forall_cons; [cbn [fst snd]; rewrite SHF; unfold sh, nsh, ENTRY_SIZE; rewrite ASHADOW_BASE_val; clear - E6 E1 FQ5 FQ6; Z.div_mod_to_equations; lia|].
        apply Forall_cons; [cbn [fst snd]; rewrite SHF; unfold sh, nsh, ENTRY_SIZE; rewrite ASHADOW_BASE_val; clear - E6 E1 FQ5 FQ6; Z.div_mod_to_equations; lia| apply Forall_nil].
      - intros b Hb. destruct (SUBAV3 b Hb) as (INX & AV & SAV). split; [apply SLX; exact INX|]. split; [exact AV| exact SAV]. }
    destruct (SUBAV3 (pS, en_suites E, sn) ltac:(rewrite SUO; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as (SINx & AVs & _).
    destruct (SUBAV3 (pn, en_pname E, zlength nm + 1) ltac:(rewrite PNO; apply in_or_app; left; left; reflexivity)) as (NINx & AVn & _).
    cbn [blk_addr blk_size fst snd] in AVs, AVn. pose proof (suite_cells_size rows) as SSZ. rewrite RWL in SSZ.
    assert (SC3 : rw_cells asegs m3 (en_suites E) (suite_cells rows)).
    { eapply (xpres_rw_cells' H); [exact XP23| exact SC2| right; right; left; exists (pS, en_suites E, sn); split; [apply SLX; exact SINx| cbn; rewrite SSZ; clear - SO6 NSR; lia]|].
      rewrite SSZ. eapply Forall_impl; [| exact AVs]. cbn beta. intros iv K. clear - K SO6 NSR. lia. }
    assert (PNB3 : bytes_at asegs m3 (en_pname E) (nm ++ [Z_to_bv 8 0])).
    { eapply (xpres_bytes_at' H); [exact XP23| exact PNB2| right; right; left; exists (pn, en_pname E, zlength nm + 1); split; [apply SLX; exact NINx| cbn; rewrite length_app; cbn [length]; unfold zlength; clear; lia]|].
      rewrite length_app. cbn [length]. eapply Forall_impl; [| exact AVn]. cbn beta. intros iv K. unfold zlength in K |- *. clear - K. lia. }
    clear T23.
    (* [comment removed for export] *)
    idtac "P8_FCC".
    pose proof DW3 as (HPd & LMd & _ & NEWd & CTXd & ECd & EBd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSbd & _ & _ & _ & _ & _ & FR0d & FR1d & _ & FR2d & FR3d & _ & _ & _ & FFd & FSHd & LSHd & RFSd & [errvd ERRd] & AUXd & MId & ACd & STd & STKd & CHNd & _ & LEDd).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BRSd & F1d & MFd & IMd & GMd & ACCBd & _).
    destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW3) as (_ & ND3 & DISJ3 & D23 & D13).
    pose proof (drest_subc [] NB LE2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SLL0).
    assert (EPH3 : mid_err M3 = mid_err M2) by reflexivity.
    assert (HES : forall c0, mid_err M3 = ErrReady c0 -> In (ec_es c0) (mid_errblocks M3 ++ drestc Lx NB LE2) /\ blk_size (ec_es c0) = ERRST_SIZE).
    { intros c0 EQ. destruct (adwkG_esc Lx NB S' M3 LE2 _ _ _ _ _ _ _ _ _ _ c0 DW3 EQ) as [I5 Z5]. split; [apply in_or_app; right; apply SL0; apply SLL; exact I5| exact Z5]. }
    (* [comment removed for export] *)
    assert (PNINd : In (pn, en_pname E, zlength nm + 1) (mid_errblocks M3 ++ drestc Lx NB LE2)) by (apply in_or_app; right; apply SLX; exact NINx).
    pose proof (HHx_slack_law H HX _ _ _ _ _ _ HPd PNINd) as WR. pose proof (ah_blocks H HH _ _ _ _ HPd PNINd) as (_ & _ & _ & P4 & _). cbn [blk_addr blk_size fst snd] in P4.
    destruct (awr_at_bytes _ _ _ WR ltac:(pose proof (Z.mod_pos_bound (- (en_pname E + (zlength nm + 1))) 8 ltac:(clear; lia)) as K; clear - K; lia) ltac:(clear - P4 NMR; unfold zlength in *; lia)) as (slack & SL & SB).
    assert (PNS : bytes_at asegs m3 (en_pname E) (nm ++ Z_to_bv 8 0 :: slack)).
    { change (nm ++ Z_to_bv 8 0 :: slack) with (nm ++ [Z_to_bv 8 0] ++ slack). rewrite app_assoc. apply bytes_at_app. split; [exact PNB3|].
      rewrite length_app. cbn [length]. replace (en_pname E + Z.of_nat (length nm + 1)) with (en_pname E + (zlength nm + 1)) by (unfold zlength; clear; lia). exact SB. }
    assert (SLK : (- (en_pname E + zlength nm + 1)) mod 8 <= zlength slack).
    { unfold zlength in SL |- *. rewrite SL. replace (en_pname E + Z.of_nat (length nm) + 1) with (en_pname E + (Z.of_nat (length nm) + 1)) by (clear; lia). apply Z.le_refl. }
    (* [comment removed for export] *)
    destruct DB as [DBb DBc].
    assert (FBY : lb_bytes (mid_errblocks M3 ++ drestc Lx NB LE2) + errph_bytes (mid_err M3) + FCC_BYTES + ERRSTR_BYTES <= as_LIVE_MAX H).
    { rewrite lb_bytes_app, EPH3. unfold FCC_BYTES, VPM_SIZE, SK_SIZE, ERRSTR_BYTES, PUSH_HB in *. clear - DBb EBd. lia. }
    assert (FBC : Z.of_nat (length (mid_errblocks M3 ++ drestc Lx NB LE2)) + errph_cnt (mid_err M3) + FCC_CNT + ERRSTR_CNT <= as_LIVE_CNT_MAX H).
    { rewrite length_app, Nat2Z.inj_add, EPH3. unfold FCC_CNT, ERRSTR_CNT in *. clear - DBc ECd. lia. }
    assert (NS1 : 1 <= en_nsuites E) by (clear - NSR; lia).
    pose proof ((RCI LEDGER_pay) s' um uf (560 + errph_bytes (mid_err M3) + 64 * en_nsuites E) (568 + errph_bytes (mid_err M3) + 64 * en_nsuites E) LEDd
                  ltac:(rewrite EPH3; clear - EBR' NS1; lia) ltac:(rewrite EPH3; clear - EBR' NS1; lia)
                  ltac:(rewrite EPH3; unfold ENTRY_CM, DECODE_CUM_BYTES in *; clear - UMQ UMB NS4 ELR EBR' NS1; lia)
                  ltac:(rewrite EPH3; unfold ENTRY_CF, DECODE_CUM_BYTES in *; clear - UFQ UFB NS4 ELR EBR' NS1; lia)) as PAYF.
    pose proof (fcc_cost_lump M3 (en_nsuites E) NS1) as FCL.
    pose proof (afcc_spec H HX RAISE strspn_icpt_ok) as FC. unfold fcc_stmt in FC.
    eapply (ah_seq H HH).
    { eapply FC with (lo := lo) (B := B) (LIB := LE2 ++ LIB) (LB := drestc Lx NB LE2) (LF := LF1c ff fp) (M := M3) (x := x) (ee := ee) (E := Et)
                     (errv := errvd) (CH := CH1c) (s := s') (rows := rows) (ps := pS) (sn := sn) (pn := pn) (ns := nm) (slack := slack); clear FC.
      all: try first [exact VIS3| exact EO3| exact ESH3| exact HPd| exact KREL3| exact AUXd| exact CEIL| exact MId| exact LMd| exact BHI| exact ACd| exact RFSd| exact ERRd| exact CHNd
                     | exact RWO| exact NONUL| exact NMR| exact FBY| exact FBC].
      all: lazymatch goal with
        | |- _ = Z_to_bv _ _ => reflexivity
        | |- Z_to_bv 64 ATP = _ => reflexivity
        | |- 1 <= en_nsuites _ < _ => subst Et; cbn; exact NSR
        | |- en_suites_o _ = _ => subst Et; cbn; exact SUO
        | |- rw_cells _ _ (en_suites _) _ => subst Et; cbn; exact SC3
        | |- zlength _ = en_nsuites _ => subst Et; cbn; exact RWL
        | |- 6 * en_nsuites _ <= _ => subst Et; cbn; exact SO6
        | |- en_pname_o _ = _ => subst Et; cbn; exact PNO
        | |- bytes_at _ _ (en_pname _) _ => subst Et; cbn; exact PNS
        | |- _ mod 8 <= zlength _ => subst Et; cbn; exact SLK
        | |- Forall _ (blocks_ENTRY _ _) => rewrite (same_blocks_ENTRY ee E Et SBe); apply Forall_forall; intros b Hb;
              pose proof (BRSd b ltac:(apply in_or_app; right; apply SLX; eapply Permutation_in; [exact PE| exact Hb])) as (_ & _ & _ & _ & Kb & _); clear - Kb CEIL; lia
        | |- forall b, In b (_ ++ LIB) -> In b _ => intros b Hb; apply SL0; apply SLL; exact Hb
        | |- mid_ctx _ = CtxReady x => rewrite CTXd; exact CTX
        | |- mid_flag _ = 1 => exact F1d
        | |- forall b b', In b _ -> In b' (blocks_ENTRY _ _) -> _ => rewrite (same_blocks_ENTRY ee E Et SBe); intros b b' Hb Hb' K; exact (D23 _ _ ltac:(eapply Permutation_in; [exact PE| exact Hb']) (SLL0 _ Hb) (eq_sym K))
        | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - SPB Q2; lia
        | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
        | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact STd
        | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); replace (FCC_STACK M3) with (FCC_STACK M2) by reflexivity; clear - LO DSK Q2; lia
        | |- stack0 _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); eapply stack0_sub; [exact STKd| clear - LOS; lia| clear - Q2 LOS; lia| clear - Q1; Z.div_mod_to_equations; lia]
        | |- mid_closed_ok _ _ => exact (errph_closed_of_step H M MCO M3 STP03)
        | |- (_ <= AFS_MAXLIVE)%nat => cbn [length LF1]; unfold mid_LF, ERRPH_LF, AFS_MAXLIVE, READCFG_LF, READCFG_MAXLIVE in *; destruct (mid_err M3); clear - LFB; lia
        | |- athr_cells _ => eapply (ah_thr H HH); exact HPd
        | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact (CHBx _ _ Hin)
        | |- pf_ok _ _ _ _ => unfold ADE_R10; rewrite unsigned_lit by (clear; lia); eapply pf_ok_incl; [| apply (PF_fcc_mstep M M3 STP03)]; apply pf_sitec; intros e He;
                              unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left; unfold PF_entry; do 7 (apply in_or_app; right); apply in_or_app; left; exact He
        | |- FCC_COST _ _ _ <= as_AL _ _ => subst Et; cbn; clear - PAYF FCL; lia
        | |- _ mod 2 = 0 => unfold ADE_R10; rewrite unsigned_lit by (clear; lia); reflexivity
        | |- ?G => idtac "FC_LEFT" G
        end. }
    clear FC. intros [msF4 mo4] PO. unfold fcc_post in PO. cbn [cfg_ms cfg_model] in PO. cbv zeta in PO.
    destruct PO as (k0 & k1 & k2 & d1 & d2 & d3 & d4r & d5 & d6 & d7 & k3 & k4 & k5 & k6 & m4 & errv4 & s4q & rv & M4 & LBN & XS
                    & VIS4 & RV & KREL4 & MP4 & MI4 & AC4 & ST4 & STK4 & ERR4 & AUX4 & HP4 & LM4 & STP4 & NEW4 & CTX4 & VD4 & EC4 & EB4 & EO4 & ESH4 & FXS4 & RFS4 & ATH4 & XP4 & AL4).
    rewrite (unsigned_lit S1c) in ST4, STK4, XP4 by (clear - Q2 SPR CEIL LOS LO0; lia).
    idtac "P8_POSTFCC".
    pose proof (errph_step_le _ _ STP4) as [EPH4 EPC4]. pose proof (anewlib_len _ _ _ STP4 NEW4 CTXd) as [LEc LEb]. rewrite EPH3 in EPH4, EPC4, LEc, LEb.
    set (dd := errph_bytes (mid_err M2) - errph_bytes (mid_err M4) + ERRDEBUG_BYTES).
    assert (DD0 : 0 <= dd) by (subst dd; unfold ERRDEBUG_BYTES; clear - EPH4; lia).
    (* [comment removed for export] *)
    assert (XP4' : xpres H (drestc Lx NB LE2) S1c ([] ++ ECH_AC14_kit.XR (mid_err M3) XS) m3 m4).
    { eapply (xpres_X_mono H); [exact XP4|]. intros a K. cbn [app]. unfold ECH_AC14_kit.XR. apply rin_ivs_app in K. apply rin_ivs_app.
      destruct K as [K|K]; [left; exact K|]. right. apply rin_ivs_app in K. apply rin_ivs_app. destruct K as [K|K]; [left; exact K|]. right. apply rin_ivs_app. right. exact K. }
    pose proof (ECH_AC14_kit.XR_low H HX (mid_err M3) s' _ m3 (LF1c ff fp) m3 XS HPd RFSd FXS4 HES) as XRL.
    assert (TS4 : forall A' cs, rw_cells asegs m3 A' cs -> S1c <= A' -> rw_cells asegs m4 A' cs).
    { intros A' cs RC Ha. eapply (xpres_rw_cells' H); [exact XP4'| exact RC| left; exact Ha|]. cbn [app].
      eapply Forall_impl; [| exact XRL]. cbn beta. intros iv K. right. clear - K Ha AS1. lia. }
    pose proof (TS4 _ _ FR1d ltac:(clear; lia)) as FR14. pose proof (TS4 _ _ FR2d ltac:(clear; lia)) as FR24. pose proof (TS4 _ _ FR3d ltac:(clear; lia)) as FR34.
    (* [comment removed for export] *)
    pose proof (fcc_spent_lump M3 M4 (en_nsuites E) NS1 ltac:(rewrite EPH3; exact EPH4)) as FSL. rewrite EPH3 in FSL. fold dd in FSL.
    assert (LED4 : LEDGERc s4q (um + (496 + dd + 64 * en_nsuites E)) (uf + (504 + dd + 64 * en_nsuites E))).
    { apply ((RCI LEDGER_step) s' s4q um uf (496 + dd + 64 * en_nsuites E) (504 + dd + 64 * en_nsuites E) LEDd ltac:(clear - DD0 NS1; lia) ltac:(clear - DD0 NS1; lia)).
      revert AL4. subst Et. cbn [en_nsuites upd_loadtime]. intros AL4. clear - AL4 FSL. lia. }
    (* [comment removed for export] *)
    assert (DW4 : adwkc Lx NB S' M4 (LBN ++ LE2) w24 w32 (wz (cur + 4)) w48 w56 w64 w72 (wz (rem - 4)) (wz elen) (wz cur) (wz ee) x0 x1 x2 n0 n1 n2 p0 p1 p2 0
                    (um + (496 + dd + 64 * en_nsuites E)) (uf + (504 + dd + 64 * en_nsuites E)) m4 s4q).
    { unfold adwk. eapply (adwkG_libXc Lx Lx NB S' M3 M4 LE2 LBN _ (wz ee) _ 0 (b8 0xf8) (poison_bytes 256 0xf8) um uf _ _ m3 s' m4 s4q [] XS _ (wz ee) _ errv4);
        [exact DW3| exact LM4| exact STP4| exact NEW4| rewrite CTX4; reflexivity| exact EC4| exact EB4| exact XP4'| apply Forall_nil| exact FXS4| | exact MI4| exact AC4| exact ST4| exact AUX4| exact ERR4| exact RFS4| exact LED4
        | exact FR14| reflexivity| exact FR24| exact FR34| reflexivity].
      eapply PERM; [exact HP4|]. apply Permutation_app_head. apply (drest_LEn LB p A nA pbin Bb nB TB). }
    assert (SUB4 : forall b, In b (LBN ++ drestc Lx NB LE2) -> In b (drestc Lx NB (LBN ++ LE2))).
    { intros b Hb. eapply Permutation_in; [apply (drest_LEn LB p A nA pbin Bb nB TB)| exact Hb]. }
    pose proof (ENTRYobj_LB_mono _ _ _ _ _ EO4 SUB4) as EO4'.
    assert (DB4 : dbud H (drestc Lx NB (LBN ++ LE2)) M4 PUSH_HB PUSH_HC).
    { unfold dbud. rewrite <- (lb_bytes_perm _ _ (drest_LEn LB p A nA pbin Bb nB TB Lx NB LE2 LBN)), <- (Permutation_length (drest_LEn LB p A nA pbin Bb nB TB Lx NB LE2 LBN)).
      rewrite (lb_bytes_app LBN), (length_app LBN), Nat2Z.inj_add. unfold PUSH_HC, FCC_CNT, ERRSTR_CNT in *. clear - DBb DBc LEc LEb. lia. }
    assert (PE4 : Permutation (blocks_ENTRY ee Et) Lx) by (rewrite (same_blocks_ENTRY ee E Et SBe); exact PE).
    idtac "P8_PUSH".
    eapply ((DCJ de_push) AUXV cur rem NB S' um0 uf0 (mid_err M') Lx M4 (LBN ++ LE2) w24 w32 w48 w56 w64 w72 (wz cur) x0 x1 x2 n0 n1 n2 p0 p1 p2 0
              (um + (496 + dd + 64 * en_nsuites E)) (uf + (504 + dd + 64 * en_nsuites E)) elen m4 s4q msF4 mo4 ee rv Et);
      [exact DW4| exact EO4'| exact ESH4| exact PE4
      | rewrite (same_blocks_ENTRY ee E Et SBe), (Permutation_length PE); exact LXC
      | rewrite (same_blocks_ENTRY ee E Et SBe), (lb_bytes_perm _ _ PE); exact LXB
      | exact EL19| exact ELR| exact BC| exact CR| exact NENT| exact RV
      | exact (mid_step_trans_ _ _ _ STP03 STP4)| clear - EPH4 EPH12; lia| exact EPH01| exact DB4
      | subst dd; unfold ENTRY_CM, PUSH_CM, ERRDEBUG_BYTES in *; clear - UMQ NS4 EL19 EPH4 EPH12; lia
      | subst dd; unfold ENTRY_CF, PUSH_CF, ERRDEBUG_BYTES in *; clear - UFQ NS4 EL19 EPH4 EPH12; lia
      | subst dd; unfold ENTRY_CM, PUSH_CM, ERRDEBUG_BYTES in *; clear - UMQ UMB NS4 EL19 ELR EPH4 EPH12 EBR'; lia
      | subst dd; unfold ENTRY_CF, PUSH_CF, ERRDEBUG_BYTES, ENTRY_KEPT in *; clear - UFQ UFB LXB NS4 EL19 ELR EPH4 EPH12 EBR'; lia
      | exact KADV| exact KTX| exact VIS4| exact KREL4
      | exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 (ah_mpres_trans H HH _ _ _ MP3 MP4)))].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma de_phase7 : forall (cur rem elen xp xl : Z) (Lx NB : list block) (S' : storerep) (M' M2 : libmid) (LE2 : list block)
      (w24 w32 w48 w56 w64 w72 : word) (x0 x1 x2 n0 n1 n2 p0 p1 p2 : word) (um uf um0 uf0 : Z)
      (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model) (ee : Z) (E : entrep) (rows : list (Z * Z * Z)) (nm : list byte) (pS : bptr) (sn : Z) (pn : bptr)
      (rax u0 u1 u2 a0w a1w a2w a3w a4w a5w a6w a7w s2w s6w s8w s9w s10w s11w u3 u4 u5 u6 : word),
    adwkGc Lx NB S' M2 LE2 (dsg1c w24 w32 (wz (cur + 4)) w48 w56 w64 w72 (wz (rem - 4)) (wz elen) (wz cur)) (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) 0 (b8 0) (poison_bytes 256 0) um uf m' s' ->
    mid_step M M' -> mid_step M' M2 ->
    ENTRYobj (drestc Lx NB LE2) m' ee E -> ENTRY_shad m' ee E -> Permutation (blocks_ENTRY ee E) Lx ->
    en_encoded_o E = None -> en_loadtime E = 0 -> en_forretry E = 0 ->
    1 <= en_nsuites E < 2^31 -> en_suites_o E = Some (pS, sn) -> rw_cells asegs m' (en_suites E) (suite_cells rows) -> zlength rows = en_nsuites E -> 6 * en_nsuites E <= sn ->
    Forall row_ok rows -> 4 * en_nsuites E <= elen ->
    en_pname_o E = Some (pn, zlength nm + 1) -> bytes_at asegs m' (en_pname E) (nm ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) nm -> 1 <= zlength nm <= 255 ->
    5 * Z.of_nat (length Lx) + 5 <= 2 * (elen + 4) -> lb_bytes Lx + (elen + 4) <= ENTRY_KEPT elen ->
    19 <= elen -> 4 + elen <= rem -> Bb + 2 <= cur -> cur + rem <= Bb + zlength bs -> cur + 23 <= xp /\ xp + xl <= cur + 4 + elen -> 0 <= xl ->
    dbudc (drestc Lx NB LE2) M2 (elen + 4 + PUSH_HB) (1 + (FCC_CNT + ERRSTR_CNT)) ->
    um <= um0 + 3 * elen + 3300 * xl + 600 + (errph_bytes (mid_err M') - errph_bytes (mid_err M2)) ->
    uf <= uf0 + 2100 * xl + 320 + (errph_bytes (mid_err M') - errph_bytes (mid_err M2)) ->
    um0 + errph_bytes (mid_err M') + ENTRY_CM rem <= DECODE_CUM_BYTES -> uf0 + errph_bytes (mid_err M') + ENTRY_CF rem <= DECODE_CUM_BYTES -> nent S' <= 65 ->
    KADVc cur rem NB S' um0 uf0 (mid_err M') -> KTAc NB S' -> KTZc NB S' -> KTXc NB S' ->
    as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) a0w a1w a2w a3w a4w a5w a6w a7w
                                s2w (Z_to_bv 64 SH) (Z_to_bv 64 xl) (Z_to_bv 64 xp) s6w (Z_to_bv 64 ASHB) s8w s9w s10w s11w u3 u4 u5 u6)
                        F (Z_to_bv 64 ADE_J3) fc None m' (seg_rom asegs) ->
    as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
    as_SR H POSTc (mkCfg msF' mo').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH AUXV TIME.
    intros until u6. intros DW STP0 STP2 EO ESH PE ENO LT0 FRY0 NSR SUO SC RWL SN6 RWO NS4 PNO NMB NONUL NMR LGC LGB E19 ELR BC CR [XP23 XPR] XL0 DB0 UMQ UFQ UMB UFB NENT KADV KTA KTZ KTX VIS1 KREL1 MP1.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (AS1 & Q2 & Q1 & SPR & BP & BH & IB2 & NBL & NB15 & BLX & BEL & BRS & F1 & MF & IM & GM & ACCB & APB & ACB & LOS & LO0).
    destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (_ & ND & DISJ & D2 & D1).
    destruct rc_facts_c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AFSB & _). pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (SHL : ASHB + AIMG_TOP / 8 <= SH) by (unfold ASHB, AIMG_TOP; rewrite Z.shiftr_div_pow2 by (clear; lia); clear - FQ1; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (SHU : SH + 512 < AHI_LO) by (rewrite SHF; unfold sh, AHI_LO; rewrite ASHADOW_BASE_val; clear - FQ2 ACB; lia).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
    pose proof (dec_stack M M2 STP) as DSK. pose proof (errph_bytes_range (mid_err M2)) as [EBR' ECR'].
    pose proof (ah_costs H HH) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd).
    (* [comment removed for export] *)
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC1) & EINr & OF1 & OF2 & OF3 & OF4 & XT).
    pose proof (drest_subc Lx NB LE2) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    assert (EINx : In (en_id E, ee, ENTRY_SIZE) Lx) by (eapply Permutation_in; [exact PE| left; reflexivity]).
    assert (EIN : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M2 ++ drestc Lx NB LE2)) by (apply in_or_app; right; apply SLX; exact EINx).
    pose proof (BRS _ EIN) as (E1 & Eb2 & Eb3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, Eb2, Eb3, E4, E5, E6, E7.
    pose proof (BLX _ EINx) as EBA. cbn [blk_addr blk_size fst snd] in EBA. pose proof (aapp_not_shadowland _ _ E7) as ENS.
    unfold ENTRY_SIZE in E5, E6, EBA, ENS. unfold AIMG_TOP in E4. unfold AFS_SIZE in E6.
    pose proof ESH as (ETOP & AD & _). unfold ENTRY_SIZE in ETOP.
    pose proof (sh_in_shadowland ee ltac:(unfold AAPP_HI; clear - E1 E5 ACB; lia)) as SISe.
    pose proof (sh_nsh_high ee ENTRY_SIZE ltac:(clear - E1; lia) ltac:(unfold ENTRY_SIZE; clear; lia) ltac:(unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia)) as SNHe.
    pose proof ENS as ENS'. unfold ALOWSH_LO, AHI_LO in SISe, SNHe, ENS'.
    assert (SUBF : forall b, In b (blocks_of (en_pname E) (en_pname_o E) ++ blocks_of (en_pub E) (en_pub_o E) ++ blocks_of (en_suites E) (en_suites_o E) ++ blocks_of (en_encoded E) (en_encoded_o E)
                                 ++ blocks_EXTS (en_exts E) (en_exts_o E)) ->
                   0 <= blk_addr b < AAPP_HI /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ (blk_addr b + blk_size b + 16 <= ee \/ ee + 104 + 16 <= blk_addr b) /\ In b Lx /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. destruct (ade_subblocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW PE b Hb) as (INX & _ & BR & APT).
      pose proof BR as (B1 & _ & B3 & _ & B5 & _ & B7). unfold ENTRY_SIZE in APT. split; [clear - B1 B3 B5 ACB; unfold AAPP_HI; lia|]. split; [exact B5|]. split; [exact B3|]. split; [exact APT|]. split; [exact INX| exact B7]. }
    assert (SINx : In (pS, en_suites E, sn) Lx /\ (en_suites E + sn + 16 <= ee \/ ee + 104 + 16 <= en_suites E) /\ en_suites E + sn <= aceil /\ 0 <= en_suites E < AAPP_HI /\ 0 <= sn).
    { destruct (SUBF (pS, en_suites E, sn) ltac:(rewrite SUO; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as (B0 & B5 & B3 & APT & INX & _).
      cbn [blk_addr blk_size fst snd] in B0, B5, B3, APT. split; [exact INX|]. split; [exact APT|]. split; [exact B5|]. split; [exact B0| exact B3]. }
    destruct SINx as (SINx & SEA & SAT & SA0 & SN0).
    assert (NINx : In (pn, en_pname E, zlength nm + 1) Lx /\ (en_pname E + (zlength nm + 1) + 16 <= ee \/ ee + 104 + 16 <= en_pname E) /\ en_pname E + (zlength nm + 1) <= aceil /\ 0 <= en_pname E < AAPP_HI).
    { destruct (SUBF (pn, en_pname E, zlength nm + 1) ltac:(rewrite PNO; apply in_or_app; left; left; reflexivity)) as (B0 & B5 & B3 & APT & INX & _).
      cbn [blk_addr blk_size fst snd] in B0, B5, B3, APT. split; [exact INX|]. split; [exact APT|]. split; [exact B5| exact B0]. }
    destruct NINx as (NINx & NEA & NAT & NA0).
    pose proof (suite_cells_size rows) as SSZ. rewrite RWL in SSZ. pose proof NMR as NMRn. unfold zlength in NMRn.
    assert (CHBx : forall fp' ra', In (fp', ra') CH1c -> S1c + 16 <= fp').
    { intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    (* [comment removed for export] *)
    assert (SUBAV : forall b lo' hi', In b (blocks_of (en_pname E) (en_pname_o E) ++ blocks_of (en_pub E) (en_pub_o E) ++ blocks_of (en_suites E) (en_suites_o E) ++ blocks_of (en_encoded E) (en_encoded_o E)
                                          ++ blocks_EXTS (en_exts E) (en_exts_o E)) -> ee <= lo' -> hi' <= ee + 104 ->
                    In b Lx /\ avoids [(lo', hi')] (blk_addr b) (blk_size b) /\ shavoids [(lo', hi')] (blk_addr b) (blk_size b)).
    { intros b lo' hi' Hb Hlo Hhi. pose proof (SUBF b Hb) as (B0 & B5 & B3 & APT & INX & B7). split; [exact INX|].
      split; [unfold avoids; apply Forall_cons; [cbn [fst snd]; clear - APT B3 Hlo Hhi; lia| apply Forall_nil]|].
      pose proof (sh_in_shadowland (blk_addr b) ltac:(clear - B0; lia)) as SIS. pose proof (sh_nsh_high (blk_addr b) (blk_size b) ltac:(clear - B0; lia) B3 ltac:(clear - B0 B5 ACB; unfold AAPP_HI; lia)) as SNH.
      unfold shavoids. apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; clear - SIS SNH ENS' Hlo Hhi; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    idtac "P7_SEG11".
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1
      | eapply ade_seg11 with (E := E) (cur := cur) (xs := xp) (xl := xl);
        [unfold dsg1 in FR1; exact FR1| exact FR2| clear - BC BP XP23; lia| exact XL0| clear - XPR ELR CR BH ACB; lia| exact EC1| exact E1| unfold ENTRY_SIZE; exact E5
        | eapply (addressable_accessible _ _ _ _ _ AD); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia]
        | exact AS1| clear - Q2 SPR; lia| exact MI1]|].
    intros msF2 mo2 KREL2 MP2 (m2 & MU2 & WM2 & MI2 & EC2 & VIS2).
    set (E2 := upd_enclen E (xp + xl - cur)) in EC2.
    assert (SBe : same_blocks E E2) by (subst E2; repeat split; reflexivity).
    assert (ST2 : stk asegs m2 lo S1c) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| cbn; clear - E5 CEIL; lia]).
    assert (T12 : forall A' cs, rw_cells asegs m' A' cs -> (A' + Z.of_nat (cells_size cs) <= ee + 88 \/ ee + 96 <= A') -> rw_cells asegs m2 A' cs).
    { intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU2| exact WM2|]. cbn. split; [clear - HA; lia| exact I]. }
    assert (DW2 : adwkGc Lx NB S' M2 LE2 (dsg1c w24 w32 (wz (cur + 4)) w48 w56 w64 w72 (wz (rem - 4)) (wz elen) (wz cur)) (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) 0 (b8 0) (poison_bytes 256 0) um uf m2 s').
    { eapply (adwkG_wc Lx NB S' M2 LE2 _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) um uf m' s' m2 [(ee + 88, ee + 96)]);
        [exact DW| exact MU2| exact WM2| exact MI2| exact ST2| apply Forall_cons; [do 6 right; exists (en_id E, ee, ENTRY_SIZE); split; [exact EINx| cbn; unfold ENTRY_SIZE; clear; lia]| apply Forall_nil]
        | apply T12; [exact FR1| right; clear - E5 AS1; lia]| exact SZ1| apply T12; [exact FR2| right; clear - E5 AS1; lia]
        | apply T12; [exact FR3| right; clear - E5 AS1; lia]| exact SZ3
        | apply T12; [exact FF1| unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - E6 FQ5 FQ6; lia]
        | apply T12; [exact FSH1| unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?LSH1; clear - ENS' SHL SHU; unfold ASHB, AHI_LO, AIMG_TOP in *; lia]
        | exact LSH1]. }
    assert (XP12 : xpres H (drestc Lx NB LE2) S1c [(ee + 88, ee + 96)] m' m2).
    { eapply (xpres_weaken H); [eapply (ECH_Xpres.xpres_of_munch H s' _ S1c [(ee + 88, ee + 96)] _ m'); [exact HH| exact HP1| exact MU2| exact WM2| apply Forall_cons; [right; cbn [fst snd]; intros a Ha; cbn; left; exact Ha| apply Forall_nil]]
        | apply Z.le_refl| intros b Hb; apply in_or_app; right; exact Hb| intros a Ha; exact Ha]. }
    assert (EO2 : ENTRYobj (drestc Lx NB LE2) m2 ee E2).
    { eapply (eobj_updX _ S1c [(ee + 88, ee + 96)] m' m2); [exact EO| exact SBe| exact L1| exact L2| exact L3| exact L4| exact EC2| exact XP12|].
      intros b Hb. exact (proj1 (proj2 (SUBAV b (ee + 88) (ee + 96) ltac:(do 4 (apply in_or_app; right); exact Hb) ltac:(clear; lia) ltac:(clear; lia)))). }
    assert (ESH2 : ENTRY_shad m2 ee E2).
    { eapply (eshad_updX (drestc Lx NB LE2) (drestc Lx NB LE2) S1c [(ee + 88, ee + 96)] m' m2); [exact ESH| exact EO| exact SBe| exact XP12| apply SLX; exact EINx| |].
      - unfold shavoids. apply Forall_cons; [cbn [fst snd]; clear - ENS' SISe SNHe; lia| apply Forall_nil].
      - intros b Hb. destruct (SUBAV b (ee + 88) (ee + 96) Hb ltac:(clear; lia) ltac:(clear; lia)) as (INX & AV & SAV). split; [apply SLX; exact INX|]. split; [exact AV| exact SAV]. }
    pose proof (T12 _ _ SC ltac:(rewrite SSZ; clear - SEA SN6 NSR; lia)) as SC2.
    pose proof (bytes_at_transport asegs _ _ _ _ _ NMB MU2 ltac:(cbn; rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - NEA NMRn; unfold zlength in *; lia)) as NMB2.
    clear T12.
    (* [comment removed for export] *)
    idtac "P7_MEMDUP".
    pose proof DW2 as (HPb & LMb & _ & _ & _ & ECb & EBb & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSbb & _ & _ & _ & _ & _ & _ & FR1b & _ & FR2b & FR3b & _ & _ & _ & _ & _ & _ & _ & [errvb ERRb] & AUXb & MIb & ACb & STb & STKb & CHNb & _ & LEDb).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW2) as (_ & _ & _ & _ & _ & _ & IB2b & _ & _ & _ & _ & _ & _ & MFb & IMb & GMb & ACCBb & _).
    pose proof CR as CRn. unfold zlength in CRn.
    destruct (abytes_at_sub m2 Bb bs (cur - Bb) (xp + xl - cur) DSbb ltac:(clear - BC; lia) ltac:(clear - XP23 XL0; lia) ltac:(clear - BC CRn XPR ELR; lia)) as [BSE ENL].
    replace (Bb + (cur - Bb)) with cur in BSE by (clear; lia).
    set (encb := firstn (Z.to_nat (xp + xl - cur)) (skipn (Z.to_nat (cur - Bb)) bs)) in BSE, ENL.
    pose proof (acmemdup_spec H HH) as CD. unfold cmemdup_stmt in CD.
    eapply (ah_seq H HH).
    { eapply CD with (lo := lo) (B := B) (LB := mid_errblocks M2 ++ drestc Lx NB LE2) (s := s') (D := cur) (bs := encb) (bD := (pbin, Bb, nB)) (v := 1) (errv := errvb) (CH := CH1c); clear CD; unfold zlength; rewrite ?ENL.
      all: try first [exact VIS2| exact HPb| exact KREL2| exact AUXb| exact MIb| exact CEIL| exact ACb| exact CHNb| exact ERRb| exact MFb| exact IMb| exact GMb| exact BSE| exact IB2b].
      all: lazymatch goal with
           | |- _ = Z_to_bv _ _ => reflexivity
           | |- Z_to_bv 64 ATP = _ => reflexivity
           | |- 1 <= _ <= 2 ^ 28 => clear - XP23 XPR XL0 E19 ELR CRn NB15 NBL BC; unfold zlength in *; lia
           | |- blk_addr _ <= _ => cbn; clear - BC; lia
           | |- _ + _ <= blk_addr _ + blk_size _ => cbn; clear - BC CRn XPR ELR NBL; unfold zlength in *; lia
           | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_app; unfold dbud, PUSH_HB in *; clear - DB0 EBb EBR' XPR XP23 XL0; lia
           | |- Z.of_nat (length _) + _ <= _ => rewrite length_app, Nat2Z.inj_add; unfold dbud, FCC_CNT, ERRSTR_CNT in *; clear - DB0 ECb ECR'; lia
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - SPB Q2; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact STb
           | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - LO DSK Q2; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact (CHBx _ _ Hin)
           | |- pf_ok _ _ _ _ => unfold ADE_R7; rewrite unsigned_lit by (clear; lia); apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left;
                                 unfold PF_entry; do 6 (apply in_or_app; right); apply in_or_app; left; exact He
           | |- as_Cm H _ <= as_AL H _ =>
               pose proof ((RCI LEDGER_pay) s' um uf (xp + xl - cur) 0 LEDb ltac:(clear - XP23 XL0; lia) ltac:(clear; lia)
                             ltac:(unfold ENTRY_CM in *; clear - UMQ UMB XP23 XPR XL0 E19 ELR EBR'; lia) ltac:(unfold ENTRY_CF in *; pose proof (errph_bytes_range (mid_err M')) as [EB0 _]; clear - UFQ UFB XP23 XPR XL0 E19 ELR EBR' EB0; lia)) as PY;
               pose proof (CF0 0 ltac:(clear; lia)) as CFz; clear - PY CFz; lia
           | |- accessible _ _ _ => eapply accessible_sub; [exact ACCBb| clear - BC; lia| clear - BC CRn XPR ELR NBL; unfold zlength in *; lia| clear - XP23 XL0; lia]
           | |- ?G => idtac "CD_LEFT" G
           end. }
    clear CD. intros [msF3 mo3] PO. unfold cmemdup_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m3 & errv3 & EA & pv & s3' & VIS3 & KREL3 & MP3 & MI3 & AC3 & ST3 & ERR3 & AUX3 & XP3 & EBRg & HP3 & ECB & ADS3 & MF3 & IM3 & GM3 & AL3).
    rewrite (unsigned_lit S1c) in ST3, XP3 by (clear - Q2 SPR CEIL LOS LO0; lia).
    unfold zlength in EBRg, HP3, ADS3, AL3. rewrite ENL in EBRg, HP3, ADS3, AL3.
    idtac "P7_POSTMD".
    pose proof EBRg as (EAP & EA16 & _ & EAI & EAT & EAF & EAA). pose proof (aapp_not_shadowland _ _ EAA) as EANS. unfold ALOWSH_LO, AHI_LO in EANS. unfold AIMG_TOP in EAI.
    assert (LED3 : LEDGERc s3' (um + (xp + xl - cur)) uf).
    { pose proof ((RCI LEDGER_step) s' s3' um uf (xp + xl - cur) 0 LEDb ltac:(clear - XP23 XL0; lia) ltac:(clear; lia)) as LS. rewrite Z.add_0_r in LS. apply LS.
      pose proof (CF0 0 ltac:(clear; lia)) as CFz. clear - AL3 CFz. lia. }
    assert (XP3' : xpres H (mid_errblocks M2 ++ drestc Lx NB LE2) S1c [] m2 m3).
    { pose proof (ECH_AC14_kit.axpres_drop_memflag H (mid_errblocks M2 ++ drestc Lx NB LE2) S1c [] [] m2 m3 MFb MF3) as K. cbn [app] in K. rewrite app_nil_r in K. apply K. exact XP3. }
    set (Lx3 := @cons block (pv, EA, xp + xl - cur) Lx).
    assert (DW3 : adwkGc Lx3 NB S' M2 LE2 (dsg1c w24 w32 (wz (cur + 4)) w48 w56 w64 w72 (wz (rem - 4)) (wz elen) (wz cur)) (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) 0 (b8 0) (poison_bytes 256 0)
                    (um + (xp + xl - cur)) uf m3 s3').
    { eapply (adwkG_xc Lx Lx3); [exact DW2| | | exact MI3| exact AC3| exact ST3| exact AUX3| exact ERR3| exact LED3].
      - eapply (xpres_weaken H); [exact XP3'| apply Z.le_refl| | intros a Ha; exact Ha].
        intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply SL0; exact Hb].
      - eapply PERM; [exact HP3|]. subst Lx3. rewrite (drest_app LB p A nA pbin Bb nB TB ((pv, EA, xp + xl - cur) :: Lx) NB LE2), (drest_app LB p A nA pbin Bb nB TB Lx NB LE2). apply Permutation_middle. }
    assert (XPd : xpres H (drestc Lx NB LE2) S1c [] m2 m3).
    { eapply (xpres_weaken H); [exact XP3'| apply Z.le_refl| intros b Hb; apply in_or_app; right; exact Hb| intros a Ha; exact Ha]. }
    pose proof (drest_subc Lx3 NB LE2) as (_ & SL03 & _ & _ & _ & _ & _ & SLX3 & _ & SLL3).
    assert (SUB3 : forall b, In b (drestc Lx NB LE2) -> In b (drestc Lx3 NB LE2)).
    { intros b Hb. subst Lx3. rewrite (drest_app LB p A nA pbin Bb nB TB ((pv, EA, xp + xl - cur) :: Lx) NB LE2). right. rewrite <- (drest_app LB p A nA pbin Bb nB TB Lx NB LE2). exact Hb. }
    assert (EO3a : ENTRYobj (drestc Lx3 NB LE2) m3 ee E2).
    { eapply ENTRYobj_LB_mono; [eapply (ENTRYobj_frameX H); [exact EO2| exact XPd| intros b Hb; apply Forall_nil]| exact SUB3]. }
    assert (ESH3a : ENTRY_shad m3 ee E2).
    { eapply (ENTRY_shad_frameX H); [exact ESH2| exact EO2| exact XPd|]. intros b Hb. split; [apply SLX; rewrite (same_blocks_ENTRY ee E E2 SBe) in Hb; eapply Permutation_in; [exact PE| exact Hb]|]. split; apply Forall_nil. }
    pose proof (xpres_rw_cells' H _ _ _ _ _ _ _ XPd EC2 ltac:(right; right; left; exists (en_id E, ee, ENTRY_SIZE); split; [apply SLX; exact EINx| unfold entry_cells; cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]; unfold ENTRY_SIZE; clear; lia]) ltac:(apply Forall_nil)) as EC3.
    pose proof (xpres_rw_cells' H _ _ _ _ _ _ _ XPd SC2 ltac:(right; right; left; exists (pS, en_suites E, sn); split; [apply SLX; exact SINx| cbn [blk_addr blk_size fst snd]; rewrite SSZ; clear - SN6; lia]) ltac:(apply Forall_nil)) as SC3.
    pose proof (xpres_bytes_at' H _ _ _ _ _ _ _ XPd NMB2 ltac:(right; right; left; exists (pn, en_pname E, zlength nm + 1); split; [apply SLX; exact NINx| cbn [blk_addr blk_size fst snd]; rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zlength; clear; lia]) ltac:(apply Forall_nil)) as NMB3.
    (* [comment removed for export] *)
    destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW3) as (BRS3 & ND3 & DISJ3 & D23 & D13).
    assert (PE3a : Permutation ((pv, EA, xp + xl - cur) :: blocks_ENTRY ee E2) Lx3) by (subst Lx3; apply perm_skip; rewrite (same_blocks_ENTRY ee E E2 SBe); exact PE).
    pose proof (ade_nodup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW3 PE3a) as ND3a.
    assert (NLX3 : In (pv, EA, xp + xl - cur) Lx3) by (subst Lx3; left; reflexivity).
    assert (ELX3 : In (en_id E, ee, ENTRY_SIZE) Lx3) by (subst Lx3; right; exact EINx).
    assert (DJE : EA + (xp + xl - cur) + 16 <= ee \/ ee + 104 + 16 <= EA).
    { pose proof (DISJ3 (pv, EA, xp + xl - cur) (en_id E, ee, ENTRY_SIZE) ltac:(apply in_or_app; right; apply SLX3; exact NLX3) ltac:(apply in_or_app; right; apply SLX3; exact ELX3)
                    ltac:(intros EQ; symmetry in EQ; exact (nodup_hd_ne _ _ _ ND3a ltac:(left; reflexivity) EQ))) as K.
      cbn [blk_addr blk_size fst snd] in K. unfold ENTRY_SIZE in K. exact K. }
    (* [comment removed for export] *)
    idtac "P7_SEG12".
    pose proof DW3 as (HPc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR1c & _ & FR2c & FR3c & _ & _ & _ & FFc & FSHc & LSHc & _ & _ & _ & MIc & _ & STc & _).
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3
      | eapply ade_seg12 with (E := E2) (s2x := Z_to_bv 64 0);
        [exact FR2c| clear - EAP EAT ACB XP23 XL0; lia| exact EC3| exact E1| unfold ENTRY_SIZE; exact E5
        | eapply (addressable_accessible _ _ _ _ _ (proj1 (proj2 ESH3a))); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia]
        | exact AS1| clear - Q2 SPR; lia| exact MIc]|].
    intros msF4 mo4 KREL4 MP4 (m4 & MU4 & WM4 & MI4 & EC4 & [[Z0 _]|[_ VIS4]]); [exfalso; clear - Z0 EAP; lia|].
    set (E3 := upd_encoded E2 EA (Some (pv, xp + xl - cur))).
    assert (ST4 : stk asegs m4 lo S1c) by (eapply stk_transport_disjoint; [exact STc| exact MU4| exact WM4| cbn; clear - E5 CEIL; lia]).
    assert (T34 : forall A' cs, rw_cells asegs m3 A' cs -> (A' + Z.of_nat (cells_size cs) <= ee + 96 \/ ee + 104 <= A') -> rw_cells asegs m4 A' cs).
    { intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU4| exact WM4|]. cbn. split; [clear - HA; lia| exact I]. }
    assert (DW4 : adwkGc Lx3 NB S' M2 LE2 (dsg1c w24 w32 (wz (cur + 4)) w48 w56 w64 w72 (wz (rem - 4)) (wz elen) (wz cur)) (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) 0 (b8 0) (poison_bytes 256 0)
                    (um + (xp + xl - cur)) uf m4 s3').
    { eapply (adwkG_wc Lx3 NB S' M2 LE2 _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) (um + (xp + xl - cur)) uf m3 s3' m4 [(ee + 96, ee + 104)]);
        [exact DW3| exact MU4| exact WM4| exact MI4| exact ST4| apply Forall_cons; [do 6 right; exists (en_id E, ee, ENTRY_SIZE); split; [exact ELX3| cbn; unfold ENTRY_SIZE; clear; lia]| apply Forall_nil]
        | apply T34; [exact FR1c| right; clear - E5 AS1; lia]| exact SZ1| apply T34; [exact FR2c| right; clear - E5 AS1; lia]
        | apply T34; [exact FR3c| right; clear - E5 AS1; lia]| exact SZ3
        | apply T34; [exact FFc| unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - E6 FQ5 FQ6; lia]
        | apply T34; [exact FSHc| unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?LSHc; clear - ENS' SHL SHU; unfold ASHB, AHI_LO, AIMG_TOP in *; lia]
        | exact LSHc]. }
    assert (XP34 : xpres H (drestc Lx3 NB LE2) S1c [(ee + 96, ee + 104)] m3 m4).
    { eapply (xpres_weaken H); [eapply (ECH_Xpres.xpres_of_munch H s3' _ S1c [(ee + 96, ee + 104)] _ m3); [exact HH| exact HPc| exact MU4| exact WM4| apply Forall_cons; [right; cbn [fst snd]; intros a Ha; cbn; left; exact Ha| apply Forall_nil]]
        | apply Z.le_refl| intros b Hb; apply in_or_app; right; exact Hb| intros a Ha; exact Ha]. }
    pose proof (T34 _ _ SC3 ltac:(rewrite SSZ; clear - SEA SN6 NSR; lia)) as SC4.
    pose proof (bytes_at_transport asegs _ _ _ _ _ NMB3 MU4 ltac:(cbn; rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - NEA NMRn; unfold zlength in *; lia)) as NMB4.
    pose proof (T34 _ _ ECB ltac:(cbn [cells_size csize]; clear - DJE ENL; lia)) as ECB4.
    idtac "P7_OBJ3".
    assert (EO4 : ENTRYobj (drestc Lx3 NB LE2) m4 ee E3).
    { pose proof EO3a as (_ & EIN3 & O13 & O23 & O33 & _ & _).
      unfold ENTRYobj. subst E3 E2. cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_enclen upd_encoded] in *.
      split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact EC4]|].
      split; [exact EIN3|]. split; [exact O13|]. split; [exact O23|]. split; [exact O33|].
      split; [cbn [ofield]; split; [exact EAP|]; split; [clear - XP23 XL0; lia| apply SLX3; exact NLX3]|].
      eapply (EXTS_frameX _ S1c [(ee + 96, ee + 104)] m3 m4 ee (upd_enclen E (xp + xl - cur))); [exact EO3a| exact XP34|].
      intros b Hb. exact (proj1 (proj2 (SUBAV b (ee + 96) (ee + 104) ltac:(do 4 (apply in_or_app; right); exact Hb) ltac:(clear; lia) ltac:(clear; lia)))). }
    assert (PE4 : Permutation (blocks_ENTRY ee E3) Lx3).
    { subst E3 E2 Lx3. unfold blocks_ENTRY in PE |- *. rewrite ENO in PE.
      cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_enclen upd_encoded blocks_of app] in PE |- *.
      eapply Permutation_trans; [| apply perm_skip; exact PE].
      rewrite !app_assoc. change (?a :: ?l ++ (pv, EA, xp + xl - cur) :: ?r) with ((a :: l) ++ (pv, EA, xp + xl - cur) :: r).
      eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. cbn [app]. rewrite <- !app_assoc. apply Permutation_refl. }
    assert (ESH4 : ENTRY_shad m4 ee E3).
    { pose proof ESH3a as (_ & AD3 & OS13 & OS23 & OS33 & _ & _).
      assert (OX : forall P o, (forall i n, o = Some (i, n) -> In (i, P, n) (blocks_of (en_pname E) (en_pname_o E) ++ blocks_of (en_pub E) (en_pub_o E) ++ blocks_of (en_suites E) (en_suites_o E) ++ blocks_of (en_encoded E) (en_encoded_o E))) ->
                   oshad m3 P o -> oshad m4 P o).
      { intros P [[iq nq]|] INo OS; [| exact I]. destruct (SUBAV _ (ee + 96) (ee + 104) (in_ext5 _ _ _ _ _ _ (INo iq nq eq_refl)) ltac:(clear; lia) ltac:(clear; lia)) as (INX & AV & SAV). cbn [blk_addr blk_size fst snd] in AV, SAV.
        eapply (ECH_AC14_kit.oshad_xpresX H); [| exact OS| exact XP34]. split; [apply SLX3; subst Lx3; right; exact INX|]. split; [exact AV| exact SAV]. }
      pose proof (EXTS_shad_frameX _ _ S1c [(ee + 96, ee + 104)] m3 m4 ee E2 ESH3a EO3a XP34
                    ltac:(intros b Hb; destruct (SUBAV b (ee + 96) (ee + 104) ltac:(do 4 (apply in_or_app; right); exact Hb) ltac:(clear; lia) ltac:(clear; lia)) as (INX & AV & SAV);
                          split; [apply SLX3; subst Lx3; right; exact INX| split; [exact AV| exact SAV]])) as XSH4.
      subst E3 E2. unfold ENTRY_shad. cbn [en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_enclen upd_encoded] in *.
      split; [unfold ENTRY_SIZE; exact ETOP|]. split.
      { eapply (addressable_xpres_blkX H); [apply SLX3; exact ELX3| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia| exact AD3| exact XP34|].
        unfold shavoids. apply Forall_cons; [cbn [fst snd]; clear - ENS' SISe SNHe; lia| apply Forall_nil]. }
      split; [apply OX; [intros iq nq Eo; rewrite Eo; apply in_or_app; left; left; reflexivity| exact OS13]|].
      split; [apply OX; [intros iq nq Eo; rewrite Eo; apply in_or_app; right; apply in_or_app; left; left; reflexivity| exact OS23]|].
      split; [apply OX; [intros iq nq Eo; rewrite Eo; do 2 (apply in_or_app; right); apply in_or_app; left; left; reflexivity| exact OS33]|].
      split; [| exact XSH4].
      cbn [oshad]. pose proof (sh_in_shadowland EA ltac:(unfold AAPP_HI; clear - EAP EAT ACB XP23 XL0; lia)) as SISa.
      pose proof (sh_nsh_high EA (xp + xl - cur) ltac:(clear - EAP; lia) ltac:(clear - XP23 XL0; lia) ltac:(unfold AAPP_HI; clear - EAT ACB XP23 XL0 EAP; lia)) as SNHa. unfold ALOWSH_LO, AHI_LO in SISa, SNHa.
      split; [unfold AAPP_HI; clear - EAT ACB XP23 XL0 EAP; lia|]. split.
      - eapply (addressable_xpres_blkX H); [apply SLX3; exact NLX3| unfold AAPP_HI; clear - EAT ACB XP23 XL0 EAP; lia| exact ADS3| exact XP34|].
        unfold shavoids. apply Forall_cons; [cbn [fst snd]; clear - ENS' SISa SNHa; lia| apply Forall_nil].
      - exists encb. replace (Z.to_nat (xp + xl - cur)) with (length encb) by (clear - ENL; lia). exact ECB4. }
    assert (DB3 : dbudc (drestc Lx3 NB LE2) M2 PUSH_HB (FCC_CNT + ERRSTR_CNT)).
    { unfold dbud in *. subst Lx3. change (drestc ((pv, EA, xp + xl - cur) :: Lx) NB LE2) with ((pv, EA, xp + xl - cur) :: drestc Lx NB LE2).
      rewrite lb_bytes_cons. cbn [length blk_size snd]. rewrite Nat2Z.inj_succ. unfold PUSH_HB, FCC_CNT, ERRSTR_CNT in *. clear - DB0 XPR XP23 XL0. lia. }
    idtac "P7_PH8".
    eapply (de_phase8 cur rem elen Lx3 NB S' M' M2 LE2 w24 w32 w48 w56 w64 w72 x0 x1 x2 n0 n1 n2 p0 p1 p2 (um + (xp + xl - cur)) uf um0 uf0 m4 s3' msF4 mo4 ee E3 rows nm pS sn pn);
      [exact DW4| exact STP0| exact STP2| exact EO4| exact ESH4| exact PE4
      | subst E3 E2; cbn; exact LT0| subst E3 E2; cbn; exact FRY0| subst E3 E2; cbn; exact NSR| subst E3 E2; cbn; exact SUO| subst E3 E2; cbn; exact SC4| subst E3 E2; cbn; exact RWL
      | subst E3 E2; cbn; exact SN6| exact RWO| subst E3 E2; cbn; exact NS4
      | subst E3 E2; cbn; exact PNO| subst E3 E2; cbn; exact NMB4| exact NONUL| exact NMR
      | subst Lx3; cbn [length]; rewrite Nat2Z.inj_succ; clear - LGC; lia| subst Lx3; rewrite lb_bytes_cons; cbn [blk_size snd]; clear - LGB XPR XP23 XL0; lia
      | exact E19| exact ELR| exact BC| exact CR| exact DB3
      | clear - UMQ XPR XP23 XL0 E19; lia| clear - UFQ XPR XP23 XL0 E19; lia
      | exact UMB| exact UFB| exact NENT| exact KADV| exact KTX| exact VIS4| exact KREL4
      | exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 (ah_mpres_trans H HH _ _ _ MP3 MP4)))].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma de_phase6 : forall (cur rem elen publen kh5 kl6 ph7 sl solo ns nl : Z) (Lx NB : list block) (S' : storerep) (M' : libmid) (LE : list block)
      (x0 x1 x2 : word) (um uf um0 uf0 : Z)
      (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model) (ee SA : Z) (pS : bptr) (E : entrep) (rows : list (Z * Z * Z)) (nm : list byte)
      (u0 u1 u2 a2w a3w a4w a5w a6w a7w u3 u4 u5 u6 : word),
    let np := cur + 9 + publen + 2 + sl + 2 in
    adwkGc Lx NB S' M' LE (dsg1c (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (rem - 4)) (wz elen) (wz cur)) (wz ee)
           (arp_sg3 x0 x1 x2 (wz np) (wz Bb) (wz nl) (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) um uf m' s' ->
    ENTRYobj (drestc Lx NB LE) m' ee E -> ENTRY_shad m' ee E -> Permutation (blocks_ENTRY ee E) Lx ->
    en_suites_o E = Some (pS, 6 * ns) -> en_suites E = SA -> en_nsuites E = ns -> en_pname_o E = None -> en_encoded_o E = None -> en_exts E = 0 -> en_exts_o E = None ->
    en_loadtime E = 0 -> en_forretry E = 0 ->
    rw_cells asegs m' SA (suite_cells rows) -> zlength rows = ns -> Forall row_ok rows -> 1 <= ns -> 4 * ns <= sl ->
    nm = firstn (Z.to_nat nl) (skipn (Z.to_nat (np - Bb)) bs) -> zlength nm = nl -> ~ In (Z_to_bv 8 0) nm -> 4 <= nl < 256 ->
    lb_bytes Lx <= ENTRY_SIZE + publen + 6 * ns -> Z.of_nat (length Lx) <= 3 ->
    Bb + 2 <= cur -> 0 <= publen -> 0 <= solo < 256 -> 2 <= sl < 2^16 -> 9 + publen + sl + nl <= elen -> 4 + elen <= rem -> cur + rem <= Bb + zlength bs ->
    0 <= kh5 < 256 -> 0 <= kl6 < 256 -> 0 <= ph7 < 256 ->
    dbudc (drestc [] NB LE) M' (ENTRY_BYTES rem) (ENTRY_CNT rem) ->
    um <= um0 + ENTRY_SIZE + publen + 6 * ns -> uf = uf0 ->
    um0 + errph_bytes (mid_err M') + ENTRY_CM rem <= DECODE_CUM_BYTES -> uf0 + errph_bytes (mid_err M') + ENTRY_CF rem <= DECODE_CUM_BYTES -> nent S' <= 65 ->
    KADVc cur rem NB S' um0 uf0 (mid_err M') -> KTAc NB S' -> KTZc NB S' -> KTXc NB S' ->
    as_VIS H s' msF' = MS (mkR (Z_to_bv 64 ADE_R5) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 (S1c + 264)) (Z_to_bv 64 (ee + 8)) a2w a3w a4w a5w a6w a7w
                                (Z_to_bv 64 ee) (Z_to_bv 64 SH) (Z_to_bv 64 (elen - 7 - publen - sl - 2)) (Z_to_bv 64 sl) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 ASHB)
                                (Z_to_bv 64 (256 * ph7)) (Z_to_bv 64 nl) (Z_to_bv 64 np) (Z_to_bv 64 431) u3 u4 u5 u6)
                        F (Z_to_bv 64 P_PACKET_strndup) fc None m' (seg_rom asegs) ->
    as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
    as_SR H POSTc (mkCfg msF' mo').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH AUXV TIME.
    intros until u6. cbv zeta. intros DW EO ESH PE SUO SUE NSE PNO ENO XE0 XO LT0 FRY0 SC RWL RWO NS1 SO4 NMD NML NONUL NLR LB1 LBN BC PLE SOLR SLR ES ELR CR R5 R6 R7 DB0 UMQ UFQ UMB UFB NENT KADV KTA KTZ KTX VIS1 KREL1 MP1.
    pose proof KTA as KTA'. unfold dK_tailA in KTA'. subst uf.
    set (np := cur + 9 + publen + 2 + sl + 2) in *.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (AS1 & Q2 & Q1 & SPR & BP & BH & IB2 & NBL & NB15 & BLX & BEL & BRS & F1 & MF & IM & GM & ACCB & APB & ACB & LOS & LO0).
    destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (_ & ND & DISJ & D2 & D1).
    destruct rc_facts_c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AFSB & _). pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (SHL : ASHB + AIMG_TOP / 8 <= SH) by (unfold ASHB, AIMG_TOP; rewrite Z.shiftr_div_pow2 by (clear; lia); clear - FQ1; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (SHU : SH + 512 < AHI_LO) by (rewrite SHF; unfold sh, AHI_LO; rewrite ASHADOW_BASE_val; clear - FQ2 ACB; lia).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
    pose proof (dec_stack M M' STP) as DSK. pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    pose proof (ah_costs H HH) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd).
    (* [comment removed for export] *)
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC1) & EINr & OF1 & OF2 & OF3 & OF4 & XT).
    pose proof (drest_subc Lx NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    assert (EINx : In (en_id E, ee, ENTRY_SIZE) Lx) by (eapply Permutation_in; [exact PE| left; reflexivity]).
    assert (EIN : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M' ++ drestc Lx NB LE)) by (apply in_or_app; right; apply SLX; exact EINx).
    pose proof (BRS _ EIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
    pose proof (BLX _ EINx) as EBA. cbn [blk_addr blk_size fst snd] in EBA. pose proof (aapp_not_shadowland _ _ E7) as ENS.
    unfold ENTRY_SIZE in E5, E6, EBA, ENS. unfold AIMG_TOP in E4. unfold AFS_SIZE in E6.
    pose proof ESH as (ETOP & AD & _). unfold ENTRY_SIZE in ETOP.
    assert (SUBF : forall b, In b (blocks_of (en_pname E) (en_pname_o E) ++ blocks_of (en_pub E) (en_pub_o E) ++ blocks_of (en_suites E) (en_suites_o E) ++ blocks_of (en_encoded E) (en_encoded_o E)) ->
                   0 <= blk_addr b < AAPP_HI /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ (blk_addr b + blk_size b + 16 <= ee \/ ee + 104 + 16 <= blk_addr b) /\ In b Lx /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. destruct (ade_subblocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW PE b (in_ext5 _ _ _ _ _ _ Hb)) as (INX & _ & BR & APT).
      pose proof BR as (B1 & _ & B3 & _ & B5 & _ & B7). unfold ENTRY_SIZE in APT. split; [clear - B1 B3 B5 ACB; unfold AAPP_HI; lia|]. split; [exact B5|]. split; [exact B3|]. split; [exact APT|]. split; [exact INX| exact B7]. }
    assert (SINx : In (pS, SA, 6 * ns) Lx /\ (SA + 6 * ns + 16 <= ee \/ ee + 104 + 16 <= SA) /\ SA + 6 * ns <= aceil /\ aapp SA (6 * ns)).
    { destruct (SUBF (pS, SA, 6 * ns) ltac:(rewrite SUO, SUE; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as (_ & B5 & _ & APT & INX & B7).
      cbn [blk_addr blk_size fst snd] in B5, APT, B7. split; [exact INX|]. split; [exact APT|]. split; [exact B5| exact B7]. }
    destruct SINx as (SINx & SEA & SAT & SAP7). pose proof (aapp_not_shadowland _ _ SAP7) as SNS.
    assert (SIN : In (pS, SA, 6 * ns) (mid_errblocks M' ++ drestc Lx NB LE)) by (apply in_or_app; right; apply SLX; exact SINx).
    pose proof (suite_cells_size rows) as SSZ. rewrite RWL in SSZ.
    assert (CHBx : forall fp' ra', In (fp', ra') CH1c -> S1c + 16 <= fp').
    { intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    assert (NPR : Bb + 11 <= np /\ np + nl <= Bb + zlength bs /\ np + nl <= cur + 4 + elen) by (subst np; clear - BC PLE SLR ES CR ELR NLR; lia).
    destruct NPR as (NP1 & NP2 & NP3).
    (* [comment removed for export] *)
    destruct (entry_split_pname _ _ _ _ _ _ _ EC1) as (EP0 & EL & ES16). pose proof OF1 as OF1'. rewrite PNO in OF1'. cbn [ofield] in OF1'. rewrite OF1' in EL.
    pose proof (asg3_split3 _ _ _ _ _ _ _ _ _ _ _ FR3) as QQ3. destruct QQ3 as [QX3 QQ4]. destruct QQ4 as [QN3 QP3].
    pose proof NP2 as NP2q. unfold zlength in NP2q.
    destruct (abytes_at_sub m' Bb bs (np - Bb) nl DSb1 ltac:(clear - NP1; lia) ltac:(clear - NLR; lia) ltac:(clear - NP2q NLR; lia)) as [BSN NML'].
    rewrite <- NMD in BSN. replace (Bb + (np - Bb)) with np in BSN by (clear; lia).
    (* [comment removed for export] *)
    idtac "P6_STRNDUP".
    pose proof (apkstrndup_spec H HH) as PS. unfold pkstrndup_stmt in PS.
    eapply (ah_seq H HH).
    { eapply PS with (lo := lo) (B := B) (LB := mid_errblocks M' ++ drestc Lx NB LE) (LF := LF1c ff fp) (s := s') (pkt := S1c + 264) (cur := np) (ms := Bb)
                     (dptr := ee + 8) (v := 1) (bs := nm) (bC := (pbin, Bb, nB)) (errv := errv1) (CH := CH1c); clear PS; rewrite ?NML.
      all: try first [exact VIS1| exact HP1| exact KREL1| exact AUX1| exact MI1| exact CEIL| exact AC1| exact CHN1| exact ERR1| exact RFS1| exact MF| exact IM| exact GM| exact BSN| exact EL| exact IB2].
      all: lazymatch goal with
           | |- _ = Z_to_bv _ _ => reflexivity
           | |- Z_to_bv 64 ATP = _ => reflexivity
           | |- rw_cells _ _ (S1c + 264) _ => unfold pk_cells; replace (S1c + 264) with (S1c + 240 + 24) by (clear; lia); exact QN3
           | |- ashobj _ _ _ (S1c + 264) _ => right; right; rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear; lia
           | |- ashobj _ _ _ _ _ => left; exists (en_id E, ee, ENTRY_SIZE); split; [exact EIN| cbn; unfold ENTRY_SIZE; clear; lia]
           | |- S1c + 264 + 24 <= B => clear - Q2 SPB; lia
           | |- 0 < _ < 2 ^ 64 => clear - NP1 NP2 BP BH ACB NLR; lia
           | |- apart _ 24 _ 8 => unfold apart; clear - E5 AS1; lia
           | |- apart _ _ _ 24 => unfold apart; clear - NP2 BH AS1 NLR; lia
           | |- apart _ _ _ 8 => unfold apart; clear - EBA NP1 NP2 NBL NLR; lia
           | |- blk_addr _ <= _ => cbn; clear - NP1; lia
           | |- _ + _ <= blk_addr _ + blk_size _ => cbn; clear - NP2 NBL; lia
           | |- _ < 2 ^ 28 => clear - NLR; lia
           | |- (S1c + 264) mod 8 = 0 => clear - Q1; Z.div_mod_to_equations; lia
           | |- (_ + _) mod 8 = 0 => clear - E2; Z.div_mod_to_equations; lia
           | |- afs_write_ok _ _ _ => left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP, AFS_SIZE in *; clear - E4 E6; lia
           | |- accessible _ (S1c + 264) _ => eapply stack0_accessible; [exact STK1| clear - LOS; lia| clear; lia| clear - Q2; lia]
           | |- accessible _ _ 8 => eapply (addressable_accessible _ _ _ _ _ AD); [clear; lia| unfold ENTRY_SIZE; clear; lia| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia]
           | |- accessible _ _ _ => eapply accessible_sub; [exact ACCB| clear - NP1; lia| clear - NP2 NBL; lia| clear - NLR; lia]
           | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_app, (drest_app LB p A nA pbin Bb nB TB Lx NB LE), lb_bytes_app; unfold dbud, ENTRY_BYTES, ENTRY_SIZE in *; clear - DB0 EB EBR' ES ELR PLE SLR SO4 LB1 NLR; lia
           | |- Z.of_nat (length _) + _ <= _ => rewrite length_app, (drest_app LB p A nA pbin Bb nB TB Lx NB LE), length_app, !Nat2Z.inj_add; unfold dbud, ENTRY_CNT in *;
                                                 pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR ES PLE SLR NLR; lia) ltac:(clear; lia)) as DP; clear - DB0 EC DP ECR' LBN; lia
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - SPB Q2; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact ST1
           | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - LO DSK Q2; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact (CHBx _ _ Hin)
           | |- pf_ok _ _ _ _ => unfold ADE_R5; rewrite unsigned_lit by (clear; lia); apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left;
                                 unfold PF_entry; do 4 (apply in_or_app; right); apply in_or_app; left; exact He
           | |- as_Cf H 0 + as_Cm H _ <= as_AL H _ =>
               pose proof ((RCI LEDGER_pay) s' um uf0 (nl + 1) 0 LED1 ltac:(clear - NLR; lia) ltac:(clear; lia)
                             ltac:(unfold ENTRY_CM, ENTRY_SIZE in *; clear - UMQ UMB ES ELR PLE SLR SO4 NLR EBR'; lia) ltac:(unfold ENTRY_CF in *; clear - UFB ELR ES PLE SLR NLR EBR'; lia)) as PY;
               pose proof (CF0 0 ltac:(clear; lia)) as CFz; clear - PY CFz; lia
           | |- ?G => idtac "PS_LEFT" G
           end. }
    clear PS. intros [msF2 mo2] PO. unfold pkstrndup_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & m2 & errv2 & s2' & D & pN &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & DBR & HP2 & RFS2 & NC2 & ADD2 & PK2 & DP2 & XP2 & MF2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit S1c) in ST2, XP2 by (clear - Q2 SPR CEIL LOS LO0; lia).
    rewrite (astrnlen_full nm NONUL) in DBR, HP2, NC2, ADD2, AL2. rewrite firstn_all in NC2. pose proof NML as NMLn. unfold zlength in NMLn. rewrite NMLn in DBR, HP2, ADD2, AL2. rewrite NML in PK2.
    pose proof (astrndup_bytes _ _ _ NC2) as NMB2. pose proof DBR as (DPOS & _ & _ & _ & DTOP & _ & DAP).
    assert (XP2' : xpres H (mid_errblocks M' ++ drestc Lx NB LE) S1c [(S1c + 264, S1c + 264 + 24); (ee + 8, ee + 8 + 8)] m' m2).
    { pose proof (ECH_AC14_kit.axpres_drop_memflag H (mid_errblocks M' ++ drestc Lx NB LE) S1c [(S1c + 264, S1c + 264 + 24); (ee + 8, ee + 8 + 8)] [] m' m2 MF MF2) as K.
      rewrite app_nil_r in K. apply K. exact XP2. }
    assert (FXW : Forall (fun iv : Z * Z => (S1c + 16 <= fst iv /\ snd iv <= S1c + 144) \/ (S1c + 240 <= fst iv /\ snd iv <= S1c + 312)
                                           \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) [(S1c + 264, S1c + 264 + 24); (ee + 8, ee + 8 + 8)]).
    { apply Forall_cons; [right; left; cbn; clear; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right. exists (en_id E, ee, ENTRY_SIZE). split; [exact EINx| cbn; unfold ENTRY_SIZE; clear; lia]. }
    (* [comment removed for export] *)
    assert (TE : forall A' cs, rw_cells asegs m' A' cs -> ee <= A' -> A' + Z.of_nat (cells_size cs) <= ee + 104 -> (A' + Z.of_nat (cells_size cs) <= ee + 8 \/ ee + 16 <= A') -> rw_cells asegs m2 A' cs).
    { intros A' cs RC Ha Hb Hc. eapply (xpres_rw_cells' H); [exact XP2'| exact RC| right; right; left; exists (en_id E, ee, ENTRY_SIZE); split; [exact EIN| cbn; unfold ENTRY_SIZE; clear - Ha Hb; lia]|].
      apply Forall_cons; [cbn; clear - Hb E5 AS1; lia|]. apply Forall_cons; [cbn; clear - Hc; lia| apply Forall_nil]. }
    assert (TS : forall A' cs, rw_cells asegs m' A' cs -> S1c <= A' -> (A' + Z.of_nat (cells_size cs) <= S1c + 264 \/ S1c + 288 <= A') -> rw_cells asegs m2 A' cs).
    { intros A' cs RC Ha Hb. eapply (xpres_rw_cells' H); [exact XP2'| exact RC| left; exact Ha|]. apply Forall_cons; [cbn; clear - Hb; lia|]. apply Forall_cons; [cbn; clear - Ha E5 AS1; lia| apply Forall_nil]. }
    pose proof (TE _ _ EP0 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; left; clear; lia)) as EP2.
    pose proof (TE _ _ ES16 ltac:(clear; lia) ltac:(unfold entry_suf16, entry_suf; cbn [cells_size csize Nat.add length app]; rewrite ?L2, ?L3, ?L4; clear; lia) ltac:(cbn; right; clear; lia)) as ES2.
    pose proof (TS _ _ QX3 ltac:(clear; lia) ltac:(cbn; left; clear; lia)) as QX2. pose proof (TS _ _ QP3 ltac:(clear; lia) ltac:(cbn; right; clear; lia)) as QP2.
    pose proof (TS _ _ FR1 ltac:(clear; lia) ltac:(unfold dsg1, arp_sg1; cbn; left; clear; lia)) as FR12.
    assert (SC2 : rw_cells asegs m2 SA (suite_cells rows)).
    { eapply (xpres_rw_cells' H); [exact XP2'| exact SC| right; right; left; exists (pS, SA, 6 * ns); split; [exact SIN| cbn; rewrite SSZ; clear; lia]|].
      rewrite SSZ. apply Forall_cons; [cbn; clear - SAT AS1; lia|]. apply Forall_cons; [cbn; clear - SEA NS1; lia| apply Forall_nil]. }
    unfold pk_cells in PK2. pose proof (asg3_join3 _ _ _ _ _ _ _ _ _ _ _ QX2 ltac:(replace (S1c + 240 + 24) with (S1c + 264) by (clear; lia); exact PK2) QP2) as FR32.
    set (En2 := upd_pname E D (Some (pN, nl + 1))). set (Lx2 := @cons block (pN, D, nl + 1) Lx).
    pose proof (entry_join_pname _ _ _ _ _ _ _ _ (Some (pN, nl + 1)) EP2 DP2 ES2) as EC2. fold En2 in EC2.
    clear TE TS.
    (* [comment removed for export] *)
    assert (LED2 : LEDGERc s2' (um + (nl + 1)) uf0).
    { pose proof ((RCI LEDGER_step) s' s2' um uf0 (nl + 1) 0 LED1 ltac:(clear - NLR; lia) ltac:(clear; lia)) as LS. rewrite Z.add_0_r in LS. apply LS.
      pose proof (CF0 0 ltac:(clear; lia)) as CFz. clear - AL2 CFz. lia. }
    assert (DW2 : adwkGc Lx2 NB S' M' LE (dsg1c (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (rem - 4)) (wz elen) (wz cur))
                    (wz ee) (arp_sg3 x0 x1 x2 (wz np) (wz Bb) (wz nl) (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) (um + (nl + 1)) uf0 m2 s2').
    { eapply (adwkG_xw Lx Lx2 NB S' M' LE _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) um uf0 (um + (nl + 1)) uf0 m' s' m2 s2' _ _ _ errv2);
        [exact DW| exact XP2'| exact FXW| eapply PERM; [exact HP2| subst Lx2; rewrite (drest_app LB p A nA pbin Bb nB TB ((pN, D, nl + 1) :: Lx) NB LE), (drest_app LB p A nA pbin Bb nB TB Lx NB LE); apply Permutation_middle]
        | exact MI2| exact AC2| exact ST2| exact AUX2| exact ERR2| exact RFS2| exact LED2| exact FR12| reflexivity| exact FR32| reflexivity]. }
    pose proof (drest_subc Lx2 NB LE) as (_ & SL02 & _ & _ & _ & IBq & _ & SLX2 & _ & SLL2).
    assert (ELX2 : In (en_id E, ee, ENTRY_SIZE) Lx2) by (right; exact EINx). assert (NLX2 : In (pN, D, nl + 1) Lx2) by (left; reflexivity). assert (SLXi2 : In (pS, SA, 6 * ns) Lx2) by (right; exact SINx).
    assert (EO2 : ENTRYobj (drestc Lx2 NB LE) m2 ee En2).
    { unfold ENTRYobj. subst En2. cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_pname].
      split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact EC2]|].
      split; [apply SLX2; exact ELX2|]. split; [cbn [ofield]; split; [exact DPOS|]; split; [clear - NLR; lia| apply SLX2; exact NLX2]|].
      split; [eapply ofield_LB_mono; [exact OF2| intros b Hb; right; exact Hb]|]. split; [eapply ofield_LB_mono; [exact OF3| intros b Hb; right; exact Hb]|].
      split; [eapply ofield_LB_mono; [exact OF4| intros b Hb; right; exact Hb]|]. rewrite XO in XT |- *. exact XT. }
    assert (PE2 : Permutation (blocks_ENTRY ee En2) Lx2).
    { unfold blocks_ENTRY in PE |- *. subst En2 Lx2. rewrite PNO in PE.
      cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_pname blocks_of app] in PE |- *.
      eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. exact PE. }
    assert (ESH2 : ENTRY_shad m2 ee En2).
    { pose proof ESH as (_ & _ & _ & OS2 & OS3 & OS4 & XSH).
      assert (OX : forall P o, (forall i n, o = Some (i, n) -> In (i, P, n) (blocks_of (en_pname E) (en_pname_o E) ++ blocks_of (en_pub E) (en_pub_o E) ++ blocks_of (en_suites E) (en_suites_o E) ++ blocks_of (en_encoded E) (en_encoded_o E))) ->
                   oshad m' P o -> oshad m2 P o).
      { intros P [[iq nq]|] INo OS; [| exact I]. destruct (SUBF _ (INo iq nq eq_refl)) as (B0 & B5 & B3 & APT & INX & B7). cbn [blk_addr blk_size fst snd] in B0, B5, B3, APT, INX, B7.
        eapply (ECH_AC14_kit.oshad_xpresX H); [| exact OS| exact XP2']. split; [apply in_or_app; right; apply SLX; exact INX|].
        pose proof (sh_in_shadowland P ltac:(clear - B0; lia)) as SIS. pose proof (aapp_not_shadowland _ _ B7) as BNS.
        pose proof (sh_nsh_high P nq ltac:(clear - B0; lia) B3 ltac:(clear - B0 B5 ACB; unfold AAPP_HI; lia)) as SNH.
        split; (apply Forall_cons; [cbn| apply Forall_cons; [cbn| apply Forall_nil]]);
          [clear - B5 AS1; lia| clear - APT B3; lia| clear - SIS SNH ACB AS1 SHC; unfold AHI_LO, ALOWSH_LO in *; lia| clear - SIS SNH ENS; unfold AHI_LO, ALOWSH_LO in *; lia]. }
      subst En2. unfold ENTRY_shad, upd_pname. cbn [en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o].
      split; [unfold ENTRY_SIZE; exact ETOP|]. split.
      { eapply (addressable_xpres_blkX H); [exact EIN| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia| exact AD| exact XP2'|].
        pose proof (sh_in_shadowland ee ltac:(unfold AAPP_HI; clear - E1 E5 ACB; lia)) as SIS.
        pose proof (sh_nsh_high ee ENTRY_SIZE ltac:(clear - E1; lia) ltac:(unfold ENTRY_SIZE; clear; lia) ltac:(unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia)) as SNH.
        pose proof (sh_aapp_range ee ENTRY_SIZE E7 ltac:(unfold ENTRY_SIZE; clear; lia)) as (W1 & W2 & W3). pose proof ENS as ENS'. unfold ALOWSH_LO, AHI_LO in SIS, SNH, W3, ENS'.
        apply Forall_cons; [cbn; clear - AS1 W2 SHC; lia|]. apply Forall_cons; [cbn; clear - ENS' SIS SNH; lia| apply Forall_nil]. }
      split.
      { cbn [oshad]. split; [clear - DTOP ACB; unfold AAPP_HI; lia|]. split; [exact ADD2|]. exists (nm ++ [b8 0]).
        eapply arw_cells_recut; [exact NC2| cbn [cells_wf cell_wf]; split; [rewrite length_app; cbn [length]; clear - NMLn NLR; lia| exact I]| cbn [cells_bytes cbytes]; rewrite !app_nil_r; reflexivity]. }
      split; [apply OX; [intros iq nq Eo; rewrite Eo; apply in_or_app; right; apply in_or_app; left; left; reflexivity| exact OS2]|].
      split; [apply OX; [intros iq nq Eo; rewrite Eo; do 2 (apply in_or_app; right); apply in_or_app; left; left; reflexivity| exact OS3]|].
      split; [apply OX; [intros iq nq Eo; rewrite Eo; do 3 (apply in_or_app; right); left; reflexivity| exact OS4]| rewrite XO; exact I]. }
    assert (LB1' : lb_bytes Lx2 <= ENTRY_SIZE + publen + 6 * ns + nl + 1) by (subst Lx2; rewrite lb_bytes_cons; cbn [blk_size snd]; clear - LB1; lia).
    assert (LBN' : Z.of_nat (length Lx2) <= 4) by (subst Lx2; cbn [length]; rewrite Nat2Z.inj_succ; clear - LBN; lia).
    assert (TAILB : dbudc (drestc Lx2 NB LE) M' (4 * ERRDEBUG_BYTES) 8 /\ um + (nl + 1) + errph_bytes (mid_err M') + 4 * ERRDEBUG_BYTES <= DECODE_CUM_BYTES
                    /\ uf0 + errph_bytes (mid_err M') + lb_bytes Lx2 + 4 * ERRDEBUG_BYTES + 8192 <= DECODE_CUM_BYTES).
    { split; [| split].
      - unfold dbud in *. rewrite (drest_app LB p A nA pbin Bb nB TB Lx2 NB LE), lb_bytes_app, length_app, Nat2Z.inj_add. unfold ENTRY_BYTES, ENTRY_CNT, ENTRY_SIZE, ERRDEBUG_BYTES in *.
        pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR ES PLE SLR NLR; lia) ltac:(clear; lia)) as DP. clear - DB0 LB1' LBN' DP ELR ES PLE SLR SO4 NLR. lia.
      - unfold ENTRY_CM, ENTRY_SIZE, ERRDEBUG_BYTES in *. clear - UMQ UMB ELR ES PLE SLR SO4 NLR. lia.
      - unfold ENTRY_CF, ENTRY_SIZE, ERRDEBUG_BYTES in *. clear - UFB LB1' ELR ES PLE SLR SO4 NLR. lia. }
    destruct TAILB as (TB1 & TB2 & TB3).
    (* [comment removed for export] *)
    pose proof DW2 as (HPc & LMc & _ & _ & _ & ECc & EBc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSbc & _ & _ & _ & _ & _ & _ & FR1c & _ & FR2c & FR3c & _ & _ & _ & FFc & FSHc & LSHc & RFSc & [errvc ERRc] & AUXc & _ & ACc & _ & STKc & CHNc & _ & LEDc).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MFc & IMc & GMc & ACCBc & _).
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2
      | eapply ade_seg9 with (q := S1c) (nm := np) (nl := nl) (rleft := elen - 7 - publen - sl - 2) (blen := nB);
        [unfold dsg1 in FR1c; exact FR1c| unfold dsg2 in FR2c; exact FR2c| exact FR3c| exact DSbc| exact BP| clear - NP1; lia| clear - NLR; lia| clear - ES; lia
        | subst np; clear - CR ELR; lia| exact BH| exact ACCBc| exact NBL| clear - ES ELR CR NBL NB15 BC PLE SLR NLR; lia| clear; lia| clear - E1; lia| unfold ENTRY_SIZE; clear - E5 ACB; lia
        | exact AS1| clear - Q2 SPR; lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 (a0' & a1' & a2' & a3' & a4' & a5' & s4' & s5' & m3 & y0 & y1 & y2 & line & MU3 & WM3 & MI3 & FR33 & CASES).
    assert (ST3 : stk asegs m3 lo S1c) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; clear; lia]).
    assert (T23 : forall A' cs, rw_cells asegs m2 A' cs -> (A' + Z.of_nat (cells_size cs) <= S1c + 240 \/ S1c + 264 <= A') -> rw_cells asegs m3 A' cs).
    { intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU3| exact WM3|]. cbn. split; [clear - HA; lia| exact I]. }
    assert (DW3 : adwkGc Lx2 NB S' M' LE (dsg1c (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (rem - 4)) (wz elen) (wz cur))
                    (wz ee) (arp_sg3 y0 y1 y2 (wz np) (wz Bb) (wz nl) (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) (um + (nl + 1)) uf0 m3 s2').
    { eapply (adwkG_wc Lx2 NB S' M' LE _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) (um + (nl + 1)) uf0 m2 s2' m3 [(S1c + 240, S1c + 264)]);
        [exact DW2| exact MU3| exact WM3| exact MI3| exact ST3| apply Forall_cons; [right; right; left; cbn; clear; lia| apply Forall_nil]
        | apply T23; [exact FR1c| left; unfold dsg1, arp_sg1; cbn; clear; lia]| exact SZ1| apply T23; [exact FR2c| left; unfold dsg2, arp_sg2; cbn; clear; lia]| exact FR33| reflexivity
        | apply T23; [exact FFc| left; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - FQ2 AS1; lia]
        | apply T23; [exact FSHc| left; unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?LSHc; rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - FQ2 ACB AS1; lia]
        | exact LSHc]. }
    pose proof (T23 _ _ EC2 ltac:(left; unfold entry_cells; cbn [cells_size csize Nat.add length]; rewrite ?L1, ?L2, ?L3, ?L4; clear - E5 AS1; lia)) as EC3.
    pose proof (T23 _ _ SC2 ltac:(left; rewrite SSZ; clear - SAT AS1; lia)) as SC3.
    pose proof MU3 as MU3'. eapply (bytes_at_transport asegs _ m2 m3) in NMB2; [| exact MU3'| cbn; rewrite length_app, Nat2Z.inj_add, NMLn; cbn [length Z.of_nat Pos.of_succ_nat]; clear - DTOP AS1 NLR; lia]. rename NMB2 into NMB3.
    assert (FWA3 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(S1c + 240, S1c + 264)]) by (apply Forall_cons; [right; cbn; unfold AHI_LO; clear - ACB AS1; lia| apply Forall_nil]).
    assert (SUBF2 : forall b, In b (blocks_of (en_pname En2) (en_pname_o En2) ++ blocks_of (en_pub En2) (en_pub_o En2) ++ blocks_of (en_suites En2) (en_suites_o En2) ++ blocks_of (en_encoded En2) (en_encoded_o En2)) ->
                   0 <= blk_addr b < AAPP_HI /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ (blk_addr b + blk_size b + 16 <= ee \/ ee + 104 + 16 <= blk_addr b) /\ In b Lx2 /\ aapp (blk_addr b) (blk_size b)).
    { intros b Hb. destruct (ade_subblocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW2 PE2 b (in_ext5 _ _ _ _ _ _ Hb)) as (INX & _ & BR & APT).
      pose proof BR as (B1 & _ & B3 & _ & B5 & _ & B7). unfold ENTRY_SIZE in APT. split; [clear - B1 B3 B5 ACB; unfold AAPP_HI; lia|]. split; [exact B5|]. split; [exact B3|]. split; [exact APT|]. split; [exact INX| exact B7]. }
    assert (ESH3 : ENTRY_shad m3 ee En2).
    { eapply (eshad_acrossW _ m2 m3 ee En2); [exact ESH2| exact MU3| exact WM3| clear - E1; lia| exact FWA3| | subst En2; exact XO].
      intros b Hb. destruct (SUBF2 b Hb) as (B0 & B5 & B3 & _). split; [exact B0| cbn; clear - B5 B3 AS1; lia]. }
    pose proof (eobj_same_cells _ _ m3 _ _ En2 _ _ _ _ EO2 ltac:(unfold same_blocks; repeat split; reflexivity) ltac:(subst En2; exact XO) L1 L2 L3 L4 EC3) as EO3.
    clear T23 MU3 MU3' WM3.
    assert (E19 : forall xl, 0 <= xl -> nl + 2 + xl <= elen - 7 - publen - sl - 2 -> 19 <= elen) by (intros xlq X0 XB; clear - X0 XB ES SO4 NS1 NLR PLE SLR; lia).
    destruct CASES as [(LN & VIS3)|(xl & RV1 & XL2 & XQ & XLB & -> & -> & -> & -> & REST)].
    { (* [comment removed for export] *)
      eapply (KTA' Lx2 M' LE (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (rem - 4)) (wz elen) (wz cur) y0 y1 y2 (wz np) (wz Bb) (wz nl) (wz (cur + 9)) (wz Bb) (wz publen) 0 (um + (nl + 1)) uf0 (b8 0) (poison_bytes 256 0) m3 s2' msF3 mo3 ee line);
        [exact DW3| exact EO3| exact ESH3| exact PE2| clear - LN; lia| exact TB1| exact TB2| exact TB3| exact VIS3| exact KREL3
        | exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 MP3))]. }
    pose proof (bz_range bs (Z.to_nat (np - Bb + nl))) as X9. pose proof (bz_range bs (Z.to_nat (np - Bb + nl + 1))) as X10.
    assert (XLR : 0 <= xl < 2^16) by (rewrite XQ; clear - X9 X10; lia).
    pose proof (E19 xl ltac:(clear - XLR; lia) XLB) as EL19.
    destruct REST as [[X0 VIS3]|[X1 VIS3]].
    - (* [comment removed for export] *)
      idtac "P6_NOEXT".
      eapply (de_phase7 cur rem elen (np + nl + 2) xl Lx2 NB S' M' M' LE (wz (ee + 24)) (wz (ee + 16)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (np + nl + 2)) (wz Bb) (wz xl) (wz np) (wz Bb) (wz nl) (wz (cur + 9)) (wz Bb) (wz publen)
                (um + (nl + 1)) uf0 um0 uf0 m3 s2' msF3 mo3 ee En2 rows nm pS (6 * ns) pN);
        [exact DW3| exact STP| apply mid_step_refl_c; exact STP| exact EO3| exact ESH3| exact PE2
        | subst En2; exact ENO| subst En2; exact LT0| subst En2; exact FRY0
        | subst En2; cbn; rewrite NSE; clear - NS1 SO4 SLR; lia| subst En2; cbn; exact SUO| subst En2; cbn; rewrite SUE; exact SC3| subst En2; cbn; rewrite NSE; exact RWL| subst En2; cbn; rewrite NSE; clear; lia
        | exact RWO| subst En2; cbn; rewrite NSE; clear - SO4 ES PLE NLR; lia
        | subst En2; cbn; rewrite NML; reflexivity| subst En2; cbn; exact NMB3| exact NONUL| rewrite NML; clear - NLR; lia
        | clear - LBN' EL19; lia| unfold ENTRY_KEPT, ENTRY_SIZE in *; clear - LB1' ES SO4 NS1 NLR PLE XLB X0; lia
        | exact EL19| exact ELR| exact BC| exact CR| subst np; clear - X0 XLB NLR PLE SLR BC SO4 NS1; lia| clear - XLR; lia
        | | rewrite Z.sub_diag, Z.add_0_r; unfold ENTRY_SIZE in UMQ; clear - UMQ X0 ES SO4 NLR PLE SLR NS1; lia| rewrite Z.sub_diag, Z.add_0_r; clear - X0; lia
        | exact UMB| exact UFB| exact NENT| exact KADV| exact KTA| exact KTZ| exact KTX| exact VIS3| exact KREL3
        | exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 MP3))].
      unfold dbud in *. rewrite (drest_app LB p A nA pbin Bb nB TB Lx2 NB LE), lb_bytes_app, length_app, Nat2Z.inj_add. unfold ENTRY_BYTES, ENTRY_CNT, ENTRY_SIZE, PUSH_HB, PUSH_HC, FCC_CNT, ERRSTR_CNT in *.
      pose proof (Z.div_le_lower_bound (2 * rem) 5 ((2 * elen) / 5) ltac:(clear; lia) ltac:(pose proof (Z.mul_div_le (2 * elen) 5 ltac:(clear; lia)); clear - ELR EL19 H0; lia)) as DP.
      pose proof (Z.div_pos (2 * elen) 5 ltac:(clear - EL19; lia) ltac:(clear; lia)) as DPq.
      clear - DB0 LB1' LBN' DP DPq ELR ES PLE SLR SO4 NLR EL19. lia.
    - (* [comment removed for export] *)
      idtac "P6_DECEXTS".
      pose proof DW3 as (HPd & LMd & _ & _ & CTXd & ECd & EBd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSbd & _ & _ & _ & _ & _ & _ & FR1d & _ & FR2d & FR3d & _ & _ & _ & FFd & FSHd & LSHd & RFSd & [errvd ERRd] & AUXd & _ & ACd & _ & STKd & CHNd & _ & LEDd).
      destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MFd & IMd & GMd & ACCBd & _).
      destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW3) as (BRS3 & ND3 & DISJ3 & D23 & D13).
      pose proof (drest_subc [] NB LE) as (_ & _ & _ & _ & _ & IB0 & _ & _ & _ & SLL0).
      pose proof (asg3_split3 _ _ _ _ _ _ _ _ _ _ _ FR3d) as QQ3. destruct QQ3 as [PKX QQ4]. destruct QQ4 as [QN33 QP33].
      assert (HES : forall c0, mid_err M' = ErrReady c0 -> In (ec_es c0) (mid_errblocks M' ++ drestc Lx2 NB LE) /\ blk_size (ec_es c0) = ERRST_SIZE).
      { intros c0 EQ. destruct (adwkG_esc Lx2 NB S' M' LE _ _ _ _ _ _ _ _ _ _ c0 DW3 EQ) as [I5 Z5]. split; [apply in_or_app; right; apply SL02; apply SLL2; exact I5| exact Z5]. }
      pose proof (adecexts_spec H HX RAISE) as DX. unfold decexts_stmt in DX.
      eapply (ah_seq H HH).
      { eapply DX with (lo := lo) (B := B) (LIB := LE ++ LIB) (LB := drestc Lx2 NB LE) (LF := LF1c ff fp) (M := M') (x := x) (ee := ee) (pk := S1c + 240) (base := Bb) (len := nB)
                       (cur := np + nl + 2) (rem := xl) (E := En2) (bs := bs) (pbin := pbin) (errv := errvd) (CH := CH1c) (s := s2'); clear DX.
        all: try first [exact VIS3| exact EO3| exact ESH3| exact HPd| exact KREL3| exact AUXd| exact CEIL| exact MI3| exact DSbd| exact LMd| exact BHI| exact IBq| exact ACd| exact NBL| exact RFSd| exact ERRd| exact CHNd| exact X1| exact ACCBd].
        all: lazymatch goal with
          | |- _ = Z_to_bv _ _ => reflexivity
          | |- Z_to_bv 64 ATP = _ => reflexivity
          | |- en_exts _ = 0 => subst En2; exact XE0
          | |- en_exts_o _ = None => subst En2; exact XO
          | |- Forall _ (blocks_ENTRY _ _) => apply Forall_forall; intros b Hb; pose proof (BRS3 b ltac:(apply in_or_app; right; apply SLX2; eapply Permutation_in; [exact PE2| exact Hb])) as (_ & _ & _ & _ & Kb & _); clear - Kb CEIL; lia
          | |- rw_cells _ _ (S1c + 240) _ => unfold pk_cells; exact PKX
          | |- pk_in _ _ _ _ => unfold pk_in; subst np; clear - NP1 NP2 XLR XLB ES ELR CR NBL PLE SLR NLR BC; lia
          | |- _ <= 1499 => subst np; clear - XLB ES ELR CR NBL NB15 BC PLE SLR NLR; lia
          | |- bv_unsigned _ <= S1c + 240 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear; lia
          | |- S1c + 240 + 24 <= B => clear - SPB Q2; lia
          | |- (S1c + 240) mod 8 = 0 => clear - Q1; Z.div_mod_to_equations; lia
          | |- accessible _ (S1c + 240) 24 => eapply stack0_accessible; [exact STKd| clear - LOS; lia| clear; lia| clear - Q2; lia]
          | |- offchain _ _ _ => intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; left; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; left; clear - CB' Q2; lia]
          | |- en_id _ <> pbin => subst En2; cbn [en_id upd_pname]; exact (D2 _ _ EINx IB0)
          | |- _ <= Bb + zlength bs => subst np; clear - NP1 XLB ES ELR CR PLE SLR NLR BC; lia
          | |- forall b, In b (_ ++ LIB) -> In b _ => intros b Hb; apply SL02; apply SLL2; exact Hb
          | |- mid_ctx _ = CtxReady x => rewrite CTXd; exact CTX
          | |- mid_flag _ = 1 => exact F1
          | |- forall b b', In b _ -> In b' (blocks_ENTRY _ _) -> _ => intros b b' Hb Hb' K; exact (D23 _ _ ltac:(eapply Permutation_in; [exact PE2| exact Hb']) (SLL0 _ Hb) (eq_sym K))
          | |- forall b, In b _ -> blk_id b <> pbin =>
              intros b Hb K; destruct (drest_idsc (mid_errblocks M') Lx2 NB LE ND3) as (_ & _ & _ & _ & D5 & _ & _);
              refine (D5 (pbin, Bb, nB) b (or_introl eq_refl) _ (eq_sym K)); right; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; exact (SUBL _ Hb)]
          | |- lb_bytes _ + _ + _ + _ <= _ => rewrite lb_bytes_app, (drest_app LB p A nA pbin Bb nB TB Lx2 NB LE), lb_bytes_app; unfold dbud, DECEXTS_BYTES, ENTRY_BYTES, ENTRY_SIZE, ERRDEBUG_BYTES in *; clear - DB0 EBd EBR' ES ELR PLE SLR SO4 LB1' NLR XLB XLR; lia
          | |- Z.of_nat (length _) + _ + _ + _ <= _ => rewrite length_app, (drest_app LB p A nA pbin Bb nB TB Lx2 NB LE), length_app, !Nat2Z.inj_add; unfold dbud, ENTRY_CNT in *;
                pose proof (Z.div_le_mono (2 * xl) (2 * rem) 5 ltac:(clear; lia) ltac:(clear - XLB ES ELR PLE SLR NLR XLR; lia)) as DM; clear - DB0 ECd DM ECR' LBN'; lia
          | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - SPB Q2; lia
          | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
          | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact ST3
          | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - LO DSK Q2; lia
          | |- stack0 _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); eapply stack0_sub; [exact STKd| clear - LOS; lia| clear - Q2 LOS; lia| clear - Q1; Z.div_mod_to_equations; lia]
          | |- mid_closed_ok _ _ => exact (errph_closed_of_step H M MCO M' STP)
          | |- (_ <= AFS_MAXLIVE)%nat => cbn [length LF1]; unfold mid_LF, ERRPH_LF, AFS_MAXLIVE, READCFG_LF, READCFG_MAXLIVE in *; destruct (mid_err M'); clear - LFB; lia
          | |- athr_cells _ => eapply (ah_thr H HH); exact HPd
          | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact (CHBx _ _ Hin)
          | |- pf_ok _ _ _ _ => unfold ADE_R6; rewrite unsigned_lit by (clear; lia); eapply pf_ok_incl; [| apply (PF_decexts_mstep M M' STP)]; apply pf_sitec; intros e He;
                                unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left; unfold PF_entry; do 5 (apply in_or_app; right); apply in_or_app; left; exact He
          | |- DECEXTS_COST _ _ _ <= as_AL _ _ =>
              pose proof ((RCI LEDGER_pay) s2' (um + (nl + 1)) uf0 (DECEXTS_CM xl + raise_bytes (mid_err M')) (DECEXTS_CF xl + (errph_bytes (mid_err M') + ERRDEBUG_BYTES)) LEDd
                            ltac:(unfold DECEXTS_CM, raise_bytes, ERRDEBUG_BYTES; clear - XLR EBR'; lia) ltac:(unfold DECEXTS_CF, ERRDEBUG_BYTES; clear - XLR EBR'; lia)
                            ltac:(unfold ENTRY_CM, ENTRY_SIZE, DECEXTS_CM, raise_bytes, ERRDEBUG_BYTES in *; subst np; clear - UMQ UMB ES ELR PLE SLR SO4 NLR XLB XLR EBR' NS1; lia)
                            ltac:(unfold ENTRY_CF, DECEXTS_CF, ERRDEBUG_BYTES in *; subst np; clear - UFB ELR ES PLE SLR NLR XLB XLR EBR'; lia)) as PY;
              unfold DECEXTS_COST, RAISE_COST;
              pose proof (CMadd (DECEXTS_CM xl) (raise_bytes (mid_err M')) ltac:(unfold DECEXTS_CM; clear - XLR; lia) ltac:(unfold raise_bytes, ERRDEBUG_BYTES; clear - EBR'; lia)) as S1q;
              pose proof (CFadd (DECEXTS_CF xl) (errph_bytes (mid_err M') + ERRDEBUG_BYTES) ltac:(unfold DECEXTS_CF; clear - XLR; lia) ltac:(unfold ERRDEBUG_BYTES; clear - EBR'; lia)) as S2q;
              clear - PY S1q S2q; lia
          | |- _ mod 2 = 0 => unfold ADE_R6; rewrite unsigned_lit by (clear; lia); reflexivity
          | |- ?G => idtac "DX_LEFT" G
          end. }
      clear DX. intros [msF4 mo4] PO. unfold decexts_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (z7 & z8 & z9 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & z10 & z11 & z12 & z13 & m4 & errv4 & s4q & rv & M2 & xs & exp & NBx & LBN2 & cur' & rem' & XS &
                      VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & STK4 & ERR4 & AUX4 & HP4 & LM4 & STP4 & NEW4 & CTX4 & VD4 & EC4 & EB4 & EO4 & ESH4 & PBX & RV & LGC & LGB & PK4 & BS4 & BSH4 & PIN4 & CR4 & FXS4 & RFS4 & ATH4 & XP4 & AL4).
      rewrite (unsigned_lit S1c) in ST4, STK4, XP4 by (clear - Q2 SPR CEIL LOS LO0; lia).
      idtac "P6_POSTDX".
      pose proof (errph_step_le _ _ STP4) as [EPH EPC]. pose proof (anewlib_len _ _ _ STP4 NEW4 CTXd) as [LEc LEb].
      set (d4 := errph_bytes (mid_err M') - errph_bytes (mid_err M2) + ERRDEBUG_BYTES).
      assert (D4 : 0 <= d4) by (subst d4; unfold ERRDEBUG_BYTES; clear - EPH; lia).
      (* [comment removed for export] *)
      assert (XP4' : xpres H (drestc Lx2 NB LE) S1c ([(S1c + 240, S1c + 240 + 24); (ee, ee + ENTRY_SIZE)] ++ ECH_AC14_kit.XR (mid_err M') XS) m3 m4).
      { eapply (xpres_X_mono H); [exact XP4|]. intros a K. unfold ECH_AC14_kit.XR. apply rin_ivs_app in K. apply rin_ivs_app.
        destruct K as [K|K]; [right; apply rin_ivs_app; left; exact K|]. cbn [rin_ivs app] in K.
        destruct K as [K|[K|K]]; [left; cbn; left; exact K| left; cbn; right; left; exact K|].
        right. apply rin_ivs_app. right. apply rin_ivs_app in K. apply rin_ivs_app. destruct K as [K|K]; [left; exact K| right; apply rin_ivs_app; right; exact K]. }
      pose proof (ECH_AC14_kit.XR_low H HX (mid_err M') s2' _ m3 (LF1c ff fp) m3 XS HPd RFSd FXS4 HES) as XRL.
      assert (TS4 : forall A' cs, rw_cells asegs m3 A' cs -> S1c <= A' -> (A' + Z.of_nat (cells_size cs) <= S1c + 240 \/ S1c + 264 <= A') -> rw_cells asegs m4 A' cs).
      { intros A' cs RC Ha Hb. eapply (xpres_rw_cells' H); [exact XP4'| exact RC| left; exact Ha|]. apply Forall_app. split.
        - apply Forall_cons; [cbn; clear - Hb; lia|]. apply Forall_cons; [cbn; unfold ENTRY_SIZE; clear - Ha E5 AS1; lia| apply Forall_nil].
        - eapply Forall_impl; [| exact XRL]. cbn beta. intros iv K. right. clear - K Ha AS1. lia. }
      pose proof (TS4 _ _ FR1d ltac:(clear; lia) ltac:(left; unfold dsg1, arp_sg1; cbn; clear; lia)) as FR14.
      pose proof (TS4 _ _ FR2d ltac:(clear; lia) ltac:(left; unfold dsg2, arp_sg2; cbn; clear; lia)) as FR24.
      pose proof (TS4 _ _ QN33 ltac:(clear; lia) ltac:(right; cbn; clear; lia)) as QN34. pose proof (TS4 _ _ QP33 ltac:(clear; lia) ltac:(right; cbn; clear; lia)) as QP34.
      unfold pk_cells in PK4. pose proof (asg3_join3 _ _ _ _ _ _ _ _ _ _ _ PK4 QN34 QP34) as FR34.
      (* [comment removed for export] *)
      assert (TB4 : forall b A' cs, In b Lx2 -> b <> (en_id E, ee, ENTRY_SIZE) -> rw_cells asegs m3 A' cs -> blk_addr b <= A' -> A' + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b -> rw_cells asegs m4 A' cs).
      { intros b A' cs Hb NEb RC Ha Hsz. assert (INL : In b (mid_errblocks M' ++ drestc Lx2 NB LE)) by (apply in_or_app; right; apply SLX2; exact Hb).
        pose proof (BRS3 _ INL) as (_ & _ & _ & _ & B5 & _).
        assert (NE : blk_id b <> blk_id (en_id E, ee, ENTRY_SIZE)).
        { intros EQ. apply NEb. pose proof (ade_nodup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW3 PE2) as NDE. unfold blocks_ENTRY in NDE.
          assert (Hb2 : In b (blocks_ENTRY ee En2)) by (eapply Permutation_in; [apply Permutation_sym; exact PE2| exact Hb]).
          destruct Hb2 as [<-|Hb2]; [reflexivity|]. exfalso. exact (nodup_hd_ne _ _ _ NDE Hb2 EQ). }
        pose proof (DISJ3 _ _ INL ltac:(apply in_or_app; right; apply SLX2; exact ELX2) NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ.
        eapply (xpres_rw_cells' H); [exact XP4'| exact RC| right; right; left; exists b; split; [apply SLX2; exact Hb| clear - Ha Hsz; lia]|]. apply Forall_app. split.
        - apply Forall_cons; [cbn; clear - Ha Hsz B5 AS1; lia|]. apply Forall_cons; [cbn; unfold ENTRY_SIZE in *; clear - Ha Hsz DJ; lia| apply Forall_nil].
        - eapply Forall_impl; [| exact (proj1 (ECH_AC14_kit.XR_block H HX (mid_err M') s2' _ m3 (LF1c ff fp) m3 XS b HPd RFSd FXS4 INL
                                                 ltac:(intros c0 EQ; destruct (HES c0 EQ) as [I5 Z5]; split; [exact I5|]; split; [| exact Z5];
                                                       destruct (adwkG_esc Lx2 NB S' M' LE _ _ _ _ _ _ _ _ _ _ c0 DW3 EQ) as [I6 _]; intros K; exact (D23 _ _ Hb (SLL2 _ I6) (eq_sym K)))))].
          cbn beta. intros iv K. clear - K Ha Hsz. lia. }
      assert (NEs : (pS, SA, 6 * ns) <> (en_id E, ee, ENTRY_SIZE)) by (intros K; injection K as K1 K2 K3; unfold ENTRY_SIZE in K3; clear - SEA K2 NS1; lia).
      pose proof (TB4 _ _ _ SLXi2 NEs SC3 ltac:(cbn; clear; lia) ltac:(cbn; rewrite SSZ; clear; lia)) as SC4.
      assert (NMB4 : bytes_at asegs m4 D (nm ++ [Z_to_bv 8 0])).
      { assert (INL : In (pN, D, nl + 1) (mid_errblocks M' ++ drestc Lx2 NB LE)) by (apply in_or_app; right; apply SLX2; exact NLX2).
        assert (NE : blk_id (pN, D, nl + 1) <> blk_id (en_id E, ee, ENTRY_SIZE)).
        { pose proof (ade_nodup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW3 PE2) as NDE. unfold blocks_ENTRY in NDE. intros EQ. symmetry in EQ.
          refine (nodup_hd_ne _ (pN, D, nl + 1) _ NDE _ (eq_sym EQ)). subst En2. cbn. left. reflexivity. }
        pose proof (DISJ3 _ _ INL ltac:(apply in_or_app; right; apply SLX2; exact ELX2) NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ.
        eapply (xpres_bytes_at' H); [exact XP4'| exact NMB3| right; right; left; exists (pN, D, nl + 1); split; [apply SLX2; exact NLX2| cbn; rewrite length_app, Nat2Z.inj_add, NMLn; cbn; clear; lia]|].
        rewrite length_app, Nat2Z.inj_add, NMLn. cbn [length Z.of_nat Pos.of_succ_nat]. apply Forall_app. split.
        - apply Forall_cons; [cbn; clear - DTOP AS1; lia|]. apply Forall_cons; [cbn; unfold ENTRY_SIZE in *; clear - DJ NLR; lia| apply Forall_nil].
        - eapply Forall_impl; [| exact (proj1 (ECH_AC14_kit.XR_block H HX (mid_err M') s2' _ m3 (LF1c ff fp) m3 XS (pN, D, nl + 1) HPd RFSd FXS4 INL
                                                 ltac:(intros c0 EQ; destruct (HES c0 EQ) as [I5 Z5]; split; [exact I5|]; split; [| exact Z5];
                                                       destruct (adwkG_esc Lx2 NB S' M' LE _ _ _ _ _ _ _ _ _ _ c0 DW3 EQ) as [I6 _]; intros K; exact (D23 _ _ NLX2 (SLL2 _ I6) (eq_sym K)))))].
          cbn beta. intros iv K. cbn [blk_addr blk_size fst snd] in K. clear - K. lia. }
      (* [comment removed for export] *)
      assert (LED4 : LEDGERc s4q (um + (nl + 1) + (DECEXTS_CM xl + d4)) (uf0 + (DECEXTS_CF xl + d4))).
      { apply ((RCI LEDGER_step) s2' s4q (um + (nl + 1)) uf0 (DECEXTS_CM xl + d4) (DECEXTS_CF xl + d4) LEDd ltac:(unfold DECEXTS_CM; clear - XLR D4; lia) ltac:(unfold DECEXTS_CF; clear - XLR D4; lia)).
        unfold DECEXTS_SPENT, RAISE_COSTd in AL4. fold d4 in AL4.
        pose proof (CMadd (DECEXTS_CM xl) d4 ltac:(unfold DECEXTS_CM; clear - XLR; lia) D4) as S1q. pose proof (CFadd (DECEXTS_CF xl) d4 ltac:(unfold DECEXTS_CF; clear - XLR; lia) D4) as S2q.
        clear - AL4 S1q S2q. lia. }
      (* [comment removed for export] *)
      assert (DW4 : adwkGc (NBx ++ Lx2) NB S' M2 (LBN2 ++ LE) (dsg1c (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (rem - 4)) (wz elen) (wz cur))
                      (wz ee) (arp_sg3 (wz cur') (wz Bb) (wz rem') (wz np) (wz Bb) (wz nl) (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0)
                      (um + (nl + 1) + (DECEXTS_CM xl + d4)) (uf0 + (DECEXTS_CF xl + d4)) m4 s4q).
      { eapply (adwkG_libXc Lx2 (NBx ++ Lx2) NB S' M' M2 LE LBN2 _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) (um + (nl + 1)) uf0 _ _ m3 s2' m4 s4q [(S1c + 240, S1c + 240 + 24); (ee, ee + ENTRY_SIZE)] XS _ (wz ee) _ errv4);
          [exact DW3| exact LM4| exact STP4| exact NEW4| rewrite CTX4; reflexivity| exact EC4| exact EB4| exact XP4'| | exact FXS4| | exact MI4| exact AC4| exact ST4| exact AUX4| exact ERR4| exact RFS4| exact LED4
          | exact FR14| reflexivity| exact FR24| exact FR34| reflexivity].
        - apply Forall_cons; [right; left; cbn; clear; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right. exists (en_id E, ee, ENTRY_SIZE). split; [exact ELX2| cbn; clear; lia].
        - eapply PERM; [exact HP4|]. apply Permutation_app_head.
          rewrite (drest_app LB p A nA pbin Bb nB TB (NBx ++ Lx2) NB (LBN2 ++ LE)), <- app_assoc, <- (drest_app LB p A nA pbin Bb nB TB Lx2 NB (LBN2 ++ LE)).
          apply Permutation_app_head. apply (drest_LEn LB p A nA pbin Bb nB TB). }
      assert (SUB4 : forall b, In b (NBx ++ LBN2 ++ drestc Lx2 NB LE) -> In b (drestc (NBx ++ Lx2) NB (LBN2 ++ LE))).
      { intros b Hb. rewrite (drest_app LB p A nA pbin Bb nB TB (NBx ++ Lx2) NB (LBN2 ++ LE)), <- app_assoc, <- (drest_app LB p A nA pbin Bb nB TB Lx2 NB (LBN2 ++ LE)).
        eapply Permutation_in; [apply Permutation_app_head; apply (drest_LEn LB p A nA pbin Bb nB TB)| exact Hb]. }
      pose proof (ENTRYobj_LB_mono _ _ _ _ _ EO4 SUB4) as EO4'. clear EO4.
      (* [comment removed for export] *)
      assert (DBX : forall hb hc, dbudc (drestc Lx2 NB LE) M' (lb_bytes NBx + hb) (Z.of_nat (length NBx) + hc) -> dbudc (drestc (NBx ++ Lx2) NB (LBN2 ++ LE)) M2 hb hc).
      { intros hb hc [Qa Qb]. unfold dbud. rewrite (drest_app LB p A nA pbin Bb nB TB (NBx ++ Lx2) NB (LBN2 ++ LE)), <- app_assoc, <- (drest_app LB p A nA pbin Bb nB TB Lx2 NB (LBN2 ++ LE)).
        rewrite <- (lb_bytes_perm _ _ (Permutation_app_head NBx (drest_LEn LB p A nA pbin Bb nB TB Lx2 NB LE LBN2))), <- (Permutation_length (Permutation_app_head NBx (drest_LEn LB p A nA pbin Bb nB TB Lx2 NB LE LBN2))).
        rewrite (lb_bytes_app NBx), (lb_bytes_app LBN2), (length_app NBx), (length_app LBN2), !Nat2Z.inj_add. clear - Qa Qb LEc LEb. lia. }
      (* [comment removed for export] *)
      eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply ade_seg10; [clear - RV; destruct RV as [(Rq & _)|(Rq & _)]; rewrite Rq; clear; lia| clear - AS1 ACB; lia| clear - Q2 SPR; lia| exact MI4]|].
      intros msF5 mo5 KREL5 MP5 [[R0 VIS5]|[R1 VIS5]].
      + (* [comment removed for export] *)
        destruct RV as [(Rq & _)|(_ & XS0 & EXP0 & NB0)]; [exfalso; clear - Rq R0; lia|]. subst xs exp NBx. cbn [app] in DW4, EO4', DBX. rewrite Z.add_0_l in DBX || idtac.
        eapply (KTA' Lx2 M2 (LBN2 ++ LE) (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (rem - 4)) (wz elen) (wz cur) (wz cur') (wz Bb) (wz rem') (wz np) (wz Bb) (wz nl) (wz (cur + 9)) (wz Bb) (wz publen) 0 _ _ (b8 0) (poison_bytes 256 0) m4 s4q msF5 mo5 ee 447);
          [exact DW4| | exact ESH4| | clear; lia| apply DBX; cbn [lb_bytes length fold_right Z.of_nat]; rewrite ?Z.add_0_l; exact TB1| | | exact VIS5| exact KREL5
          | exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 (ah_mpres_trans H HH _ _ _ MP3 (ah_mpres_trans H HH _ _ _ MP4 MP5))))].
        * first [exact EO4' | match goal with |- ?G => idtac "EO_GOAL" G end; match type of EO4' with ?T => idtac "EO4'" T end; fail "CUT_EO"].
        * first [revert PE2; subst En2; unfold blocks_ENTRY, upd_pname; cbn [en_version en_id en_pname en_pname_o en_publen en_pub en_pub_o en_nsuites en_suites en_suites_o en_maxname en_cfgid en_enclen en_encoded en_encoded_o en_exts en_exts_o en_loadtime en_forretry];
                 rewrite ?XE0, ?XO; intros PE2; exact PE2
                | match goal with |- ?G => idtac "PE_GOAL" G end; match type of PE2 with ?T => idtac "PE2" T end; fail "CUT_PE"].
        * unfold ENTRY_CM, ENTRY_SIZE, DECEXTS_CM, ERRDEBUG_BYTES in *. subst d4 np. clear - UMQ UMB ES ELR PLE SLR SO4 NLR XLB XLR NS1 EPH. lia.
        * unfold ENTRY_CF, ENTRY_SIZE, DECEXTS_CF, ERRDEBUG_BYTES in *. subst d4 np. clear - UFB LB1' ELR ES PLE SLR SO4 NLR XLB XLR EPH. lia.
      + (* [comment removed for export] *)
        idtac "P6_PH7".
        destruct RV as [(_ & XSS & RM0)|(Rq & _)]; [| exfalso; clear - Rq R1; lia]. subst rem'.
        match type of EO4' with ENTRYobj _ _ _ ?Ex => set (En4 := Ex) in EO4', ESH4 end.
        assert (PE4 : Permutation (blocks_ENTRY ee En4) (NBx ++ Lx2)).
        { subst En4. unfold blocks_ENTRY in PE2 |- *. revert PE2. subst En2. unfold upd_pname.
          cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o]. rewrite XE0, XO. cbn [blocks_EXTS]. rewrite app_nil_r. intros PE2.
          eapply Permutation_trans; [| apply Permutation_app_comm]. rewrite !app_assoc.
          lazymatch goal with |- Permutation (?a :: ?l ++ blocks_EXTS exp xs) _ => change (a :: l ++ blocks_EXTS exp xs) with ((a :: l) ++ blocks_EXTS exp xs) end.
          apply Permutation_app; [| exact PBX]. rewrite <- !app_assoc. exact PE2. }
        eapply (de_phase7 cur rem elen (np + nl + 2) xl (NBx ++ Lx2) NB S' M' M2 (LBN2 ++ LE) (wz (ee + 24)) (wz (ee + 16)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz cur') (wz Bb) (wz 0) (wz np) (wz Bb) (wz nl) (wz (cur + 9)) (wz Bb) (wz publen)
                  _ _ um0 uf0 m4 s4q msF5 mo5 ee En4 rows nm pS (6 * ns) pN);
          [exact DW4| exact STP| exact STP4| exact EO4'| exact ESH4| exact PE4
          | subst En4 En2; cbn; exact ENO| subst En4 En2; cbn; exact LT0| subst En4 En2; cbn; exact FRY0
          | subst En4 En2; cbn; rewrite NSE; clear - NS1 SO4 SLR; lia| subst En4 En2; cbn; exact SUO| subst En4 En2; cbn; rewrite SUE; exact SC4| subst En4 En2; cbn; rewrite NSE; exact RWL| subst En4 En2; cbn; rewrite NSE; clear; lia
          | exact RWO| subst En4 En2; cbn; rewrite NSE; clear - SO4 ES PLE NLR; lia
          | subst En4 En2; cbn; rewrite NML; reflexivity| subst En4 En2; cbn; exact NMB4| exact NONUL| rewrite NML; clear - NLR; lia
          | rewrite length_app, Nat2Z.inj_add; subst np; clear - LGC LBN' EL19 XLB ES SO4 NS1 NLR PLE SLR; lia
          | rewrite lb_bytes_app; unfold ENTRY_KEPT, ENTRY_SIZE, SK_SIZE in *; subst np; clear - LGB LB1' ES XLB XLR SO4 NS1 NLR PLE SLR; lia
          | exact EL19| exact ELR| exact BC| exact CR| subst np; clear - XLR XLB NLR PLE SLR BC X1 SO4 NS1; lia| clear - XLR; lia
          | | subst d4 np; unfold DECEXTS_CM, ENTRY_SIZE, ERRDEBUG_BYTES in *; clear - UMQ ES SO4 NLR PLE SLR NS1 XLR; lia| subst d4; unfold DECEXTS_CF, ERRDEBUG_BYTES; clear - XLR; lia
          | exact UMB| exact UFB| exact NENT| exact KADV| exact KTA| exact KTZ| exact KTX| exact VIS5| exact KREL5
          | exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 (ah_mpres_trans H HH _ _ _ MP3 (ah_mpres_trans H HH _ _ _ MP4 MP5))))].
        apply DBX. unfold dbud in *. rewrite (drest_app LB p A nA pbin Bb nB TB Lx2 NB LE), lb_bytes_app, length_app, Nat2Z.inj_add. unfold ENTRY_BYTES, ENTRY_CNT, ENTRY_SIZE, SK_SIZE, PUSH_HB, PUSH_HC, FCC_CNT, ERRSTR_CNT in *.
        pose proof (Z.div_le_mono (2 * xl) (2 * rem) 5 ltac:(clear; lia) ltac:(clear - XLB ES ELR PLE SLR NLR XLR; lia)) as DM.
        assert (NBL5 : 5 * Z.of_nat (length NBx) <= 2 * xl + 10) by (clear - LGC; lia).
        pose proof (Z.div_le_lower_bound (2 * rem) 5 ((2 * xl) / 5 + 2) ltac:(clear; lia) ltac:(pose proof (Z.mul_div_le (2 * xl) 5 ltac:(clear; lia)); subst np; clear - ELR XLB ES PLE SLR NLR XLR H0; lia)) as DQ.
        subst np. clear - DB0 DQ NBL5 LGB LB1' LBN' ELR ES PLE SLR SO4 NLR XLB XLR EL19. Z.div_mod_to_equations. nia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma de_phase5 : forall (cur rem elen publen kh5 kl6 ph7 pl8 sl solo ns : Z) (Lx NB : list block) (S' : storerep) (M' : libmid) (LE : list block)
      (x0 x1 x2 n0 n1 n2 : word) (um uf um0 uf0 : Z)
      (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model) (ee SA : Z) (pS : bptr) (E : entrep) (junk : list byte)
      (rax u0 u1 u2 a1w a2w a3w a4w a5w a6w a7w u3 u4 u5 u6 : word),
    adwkGc Lx NB S' M' LE (dsg1c (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (rem - 4)) (wz elen) (wz cur)) (wz ee)
           (arp_sg3 x0 x1 x2 n0 n1 n2 (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) um uf m' s' ->
    ENTRYobj (drestc Lx NB LE) m' ee E -> ENTRY_shad m' ee E -> Permutation ((pS, SA, 6 * ns) :: blocks_ENTRY ee E) Lx ->
    en_suites_o E = None -> en_pname_o E = None -> en_encoded_o E = None -> en_exts E = 0 -> en_exts_o E = None -> en_loadtime E = 0 -> en_forretry E = 0 ->
    en_nsuites E = ns -> rw_cells asegs m' SA [CB (Z.to_nat (6 * ns)) junk] -> 0 < SA -> addressable m' SA (6 * ns) ->
    lb_bytes Lx <= ENTRY_SIZE + publen + 6 * ns -> Z.of_nat (length Lx) <= 3 ->
    Bb + 2 <= cur -> 0 <= publen -> 0 <= solo < 256 -> 2 <= sl < 2^16 -> sl mod 2 = 0 -> ns = sl / 4 -> 1 <= ns ->
    7 + publen + sl <= elen -> 4 + elen <= rem -> cur + rem <= Bb + zlength bs ->
    0 <= kh5 < 256 -> 0 <= kl6 < 256 -> 0 <= ph7 < 256 -> 0 <= pl8 < 256 -> publen = 256 * ph7 + pl8 ->
    dbudc (drestc [] NB LE) M' (ENTRY_BYTES rem) (ENTRY_CNT rem) ->
    um <= um0 + ENTRY_SIZE + publen + 6 * ns -> uf = uf0 ->
    um0 + errph_bytes (mid_err M') + ENTRY_CM rem <= DECODE_CUM_BYTES -> uf0 + errph_bytes (mid_err M') + ENTRY_CF rem <= DECODE_CUM_BYTES -> nent S' <= 65 ->
    KADVc cur rem NB S' um0 uf0 (mid_err M') -> KTAc NB S' -> KTZc NB S' -> KTXc NB S' ->
    as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 SA) a1w a2w a3w a4w a5w a6w a7w
                                (Z_to_bv 64 ee) (Z_to_bv 64 SH) (Z_to_bv 64 pl8) (Z_to_bv 64 sl) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 ASHB)
                                (Z_to_bv 64 (256 * ph7)) (Z_to_bv 64 (cur + 9 + publen)) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 ns) u3 u4 u5 u6)
                        F (ret_pc (Z_to_bv 64 ADE_R3)) fc None m' (seg_rom asegs) ->
    as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
    as_SR H POSTc (mkCfg msF' mo').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH AUXV TIME.
    intros until u6. intros DW EO ESH PE SUO PNO ENO XE0 XO LT0 FRY0 NSE SC SAP ADS LB1 LBN BC PLE SOLR SLR EVN NSQ NS1 SL7 ELR CR R5 R6 R7 R8 PEQ DB0 UMQ UFQ UMB UFB NENT KADV KTA KTZ KTX VIS1 KREL1 MP1.
    pose proof KTA as KTA'. unfold dK_tailA in KTA'. subst uf.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (AS1 & Q2 & Q1 & SPR & BP & BH & IB2 & NBL & NB15 & BLX & BEL & BRS & F1 & MF & IM & GM & ACCB & APB & ACB & LOS & LO0).
    destruct (adwkG_hfc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (_ & ND & DISJ & D2 & D1).
    destruct rc_facts_c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AFSB & _). pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (SHL : ASHB + AIMG_TOP / 8 <= SH) by (unfold ASHB, AIMG_TOP; rewrite Z.shiftr_div_pow2 by (clear; lia); clear - FQ1; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (SHU : SH + 512 < AHI_LO) by (rewrite SHF; unfold sh, AHI_LO; rewrite ASHADOW_BASE_val; clear - FQ2 ACB; lia).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
    pose proof (dec_stack M M' STP) as DSK. pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    pose proof (ah_costs H HH) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd).
    (* [comment removed for export] *)
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC1) & EINr & OF1 & OF2 & OF3 & OF4 & XT).
    pose proof (drest_subc Lx NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    assert (EINx : In (en_id E, ee, ENTRY_SIZE) Lx) by (eapply Permutation_in; [exact PE| right; left; reflexivity]).
    assert (SINx : In (pS, SA, 6 * ns) Lx) by (eapply Permutation_in; [exact PE| left; reflexivity]).
    assert (EIN : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M' ++ drestc Lx NB LE)) by (apply in_or_app; right; apply SLX; exact EINx).
    assert (SIN : In (pS, SA, 6 * ns) (mid_errblocks M' ++ drestc Lx NB LE)) by (apply in_or_app; right; apply SLX; exact SINx).
    pose proof (BRS _ EIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
    pose proof (BLX _ EINx) as EBA. cbn [blk_addr blk_size fst snd] in EBA. pose proof (aapp_not_shadowland _ _ E7) as ENS.
    unfold ENTRY_SIZE in E5, E6, EBA, ENS. unfold AIMG_TOP in E4. unfold AFS_SIZE in E6.
    pose proof (BRS _ SIN) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). cbn [blk_addr blk_size fst snd] in T1, T2, T3, T4, T5, T6, T7.
    pose proof (BLX _ SINx) as SBA. cbn [blk_addr blk_size fst snd] in SBA. pose proof (aapp_not_shadowland _ _ T7) as SNS.
    unfold AIMG_TOP in T4. unfold AFS_SIZE in T6.
    pose proof ESH as (ETOP & AD & _). unfold ENTRY_SIZE in ETOP.
    assert (ES0 : en_suites E = 0) by (rewrite SUO in OF3; exact OF3).
    pose proof (ade_nodup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW PE) as NDP.
    assert (NPS : forall b, In b (blocks_ENTRY ee E) -> blk_id b <> pS) by (intros b Hb; exact (nodup_hd_ne _ _ _ NDP Hb)).
    pose proof (DISJ _ _ SIN EIN ltac:(cbn [blk_id fst snd]; intros K; exact (NPS _ ltac:(left; reflexivity) (eq_sym K)))) as SEA. cbn [blk_addr blk_size fst snd] in SEA. unfold ENTRY_SIZE in SEA.
    assert (NSR : 0 <= ns < 2^14) by (rewrite NSQ; clear - SLR; Z.div_mod_to_equations; lia).
    assert (SO4 : 4 * ns <= sl) by (rewrite NSQ; clear - SLR; Z.div_mod_to_equations; lia).
    set (src := cur + 9 + publen + 2) in *.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1
      | eapply ade_seg5 with (q := S1c) (E := E) (publen := publen) (cur := cur);
        [unfold dsg1 in FR1; exact FR1| exact R5| exact R6| exact R7| exact R8| exact PEQ| exact NSR| clear - SAP; lia| clear - T5 ACB; lia| subst src; clear - BC BP PLE; lia
        | subst src; clear - CR BH AS1 SL7 SLR ELR Q2 SPR; lia| clear - BC BP PLE; lia
        | exact EC1| exact E1| unfold ENTRY_SIZE; exact E5
        | eapply (addressable_accessible _ _ _ _ _ AD); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia]
        | exact AS1| clear - Q2 SPR; lia| exact MI1]|].
    intros msF2 mo2 KREL2 MP2 (m2 & MU2 & WM2 & MI2 & EC2 & [[ABS _]|[_ VIS2]]); [exfalso; clear - ABS SAP; lia|].
    set (E1' := upd_suites E SA (Some (pS, 6 * ns))).
    assert (EC2' : rw_cells asegs m2 ee (entry_cells E1' pad1 pad2 pad3 pad4)) by exact EC2.
    assert (ST2 : stk asegs m2 lo S1c) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| cbn; clear - E5 CEIL; lia]).
    assert (T12 : forall A' cs, rw_cells asegs m' A' cs -> (A' + Z.of_nat (cells_size cs) <= ee + 40 \/ ee + 48 <= A') -> rw_cells asegs m2 A' cs).
    { intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU2| exact WM2|]. cbn. split; [clear - HA; lia| exact I]. }
    pose proof (T12 _ _ FR1 ltac:(right; unfold dsg1, arp_sg1; cbn; clear - E5 AS1; lia)) as FR12. pose proof (T12 _ _ FR2 ltac:(right; unfold dsg2, arp_sg2; cbn; clear - E5 AS1; lia)) as FR22.
    pose proof (T12 _ _ FR3 ltac:(right; unfold arp_sg3; cbn; clear - E5 AS1; lia)) as FR32.
    pose proof (T12 _ _ SC ltac:(cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - NSR; lia); clear - SEA NS1; lia)) as SC2.
    assert (DW2 : adwkGc Lx NB S' M' LE (dsg1c (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (rem - 4)) (wz elen) (wz cur))
                    (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) um uf0 m2 s').
    { eapply (adwkG_wc Lx NB S' M' LE _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) um uf0 m' s' m2 [(ee + 40, ee + 48)]);
        [exact DW| exact MU2| exact WM2| exact MI2| exact ST2| | exact FR12| exact SZ1| exact FR22| exact FR32| exact SZ3
        | apply T12; [exact FF1| unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - E6 FQ5 FQ6; lia]
        | apply T12; [exact FSH1| unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?LSH1;
                      pose proof (sh_in_shadowland ff ltac:(unfold AAPP_HI; clear - FQ1 FQ2 ACB; lia)) as SIS; rewrite <- SHF in SIS; clear - SIS SHU ENS; lia]
        | exact LSH1].
      apply Forall_cons; [| apply Forall_nil]. do 6 right. exists (en_id E, ee, ENTRY_SIZE). split; [exact EINx| cbn; unfold ENTRY_SIZE; clear; lia]. }
    assert (FWA2 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(ee + 40, ee + 48)]).
    { apply Forall_cons; [cbn; unfold ALOWSH_LO, AHI_LO in ENS |- *; clear - ENS; lia| apply Forall_nil]. }
    assert (PE1 : Permutation (blocks_ENTRY ee E1') Lx).
    { eapply Permutation_trans; [| exact PE]. subst E1'. unfold blocks_ENTRY, upd_suites.
      cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o]. rewrite PNO, ENO, XO, SUO.
      cbn [blocks_of blocks_EXTS app]. rewrite !app_nil_r.
      change ((en_id E, ee, ENTRY_SIZE) :: blocks_of (en_pub E) (en_pub_o E) ++ [(pS, SA, 6 * ns)]) with (((en_id E, ee, ENTRY_SIZE) :: blocks_of (en_pub E) (en_pub_o E)) ++ [(pS, SA, 6 * ns)]).
      apply Permutation_sym. apply Permutation_cons_append. }
    (* [comment removed for export] *)
    assert (SUBF : forall b, In b (blocks_of (en_pname E1') (en_pname_o E1') ++ blocks_of (en_pub E1') (en_pub_o E1') ++ blocks_of (en_suites E1') (en_suites_o E1') ++ blocks_of (en_encoded E1') (en_encoded_o E1')) ->
                   0 <= blk_addr b < AAPP_HI /\ blk_addr b + blk_size b <= aceil /\ 0 <= blk_size b /\ (blk_addr b + blk_size b + 16 <= ee \/ ee + 104 + 16 <= blk_addr b) /\ In b Lx).
    { intros b Hb. destruct (ade_subblocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW2 PE1 b (in_ext5 _ _ _ _ _ _ Hb)) as (INX & _ & BR & APT).
      pose proof BR as (B1 & _ & B3 & _ & B5 & _). unfold ENTRY_SIZE in APT. split; [clear - B1 B3 B5 ACB; unfold AAPP_HI; lia|]. split; [exact B5|]. split; [exact B3|]. split; [exact APT| exact INX]. }
    assert (SUBE : forall b, In b (blocks_of (en_pname E) (en_pname_o E) ++ blocks_of (en_pub E) (en_pub_o E) ++ blocks_of (en_suites E) (en_suites_o E) ++ blocks_of (en_encoded E) (en_encoded_o E)) ->
                   In b (blocks_of (en_pname E1') (en_pname_o E1') ++ blocks_of (en_pub E1') (en_pub_o E1') ++ blocks_of (en_suites E1') (en_suites_o E1') ++ blocks_of (en_encoded E1') (en_encoded_o E1'))).
    { intros b Hb. subst E1'. unfold upd_suites. cbn [en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o]. rewrite SUO in Hb. cbn [blocks_of] in Hb |- *.
      rewrite !in_app_iff in Hb |- *. cbn [In] in Hb |- *. clear - Hb. tauto. }
    assert (ESHm2 : ENTRY_shad m2 ee E).
    { eapply (eshad_acrossW _ m' m2 ee E); [exact ESH| exact MU2| exact WM2| clear - E1; lia| exact FWA2| | exact XO].
      intros b Hb. destruct (SUBF b (SUBE b Hb)) as (B0 & B5 & B3 & APT & _). split; [exact B0| cbn; clear - APT B5 B3; lia]. }
    pose proof ESHm2 as (_ & AD2 & OS1 & OS2 & _ & OS4 & XSH2).
    assert (ADS2 : addressable m2 SA (6 * ns)).
    { eapply (ECH_AC14_decexts.addressable_acrossW _ m' m2); [exact ADS| exact MU2| exact WM2| clear - T1 T5 ACB NS1; unfold AAPP_HI; lia| clear - T5 ACB; unfold AAPP_HI; lia| exact FWA2]. }
    assert (ESH2 : ENTRY_shad m2 ee E1').
    { subst E1'. unfold ENTRY_shad, upd_suites. cbn [en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o].
      split; [unfold ENTRY_SIZE; exact ETOP|]. split; [exact AD2|]. split; [exact OS1|]. split; [exact OS2|]. split; [| split; [exact OS4| exact XSH2]].
      cbn [oshad]. split; [clear - T5 ACB; unfold AAPP_HI; lia|]. split; [exact ADS2|]. exists junk. exact SC2. }
    assert (EO2 : ENTRYobj (drestc Lx NB LE) m2 ee E1').
    { subst E1'. unfold ENTRYobj, upd_suites. cbn [en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o].
      split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact EC2]|].
      split; [exact EINr|]. split; [exact OF1|]. split; [exact OF2|]. split; [cbn [ofield]; split; [exact SAP|]; split; [clear - NS1; lia| apply SLX; exact SINx]|]. split; [exact OF4| rewrite XO in XT |- *; exact XT]. }
    clear T12 EC2' EC1.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (cur + publen)) with (Z_to_bv 64 (src - 11)) in VIS2 by (subst src; f_equal; clear; lia). fold src in VIS2.
    pose proof DW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSb2 & _).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MF2 & IM2 & GM2 & ACCB2 & _).
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2
      | eapply (ade_loop (Z.to_nat ns) 0) with (q := S1c) (E := E1') (blen := nB) (bs := bs) (Bb := Bb);
        [clear - NS1; lia| clear - NS1; lia| subst E1'; cbn [en_nsuites upd_suites]; exact NSE| exact NSR| exact SO4| clear - R5 R6; lia| clear - R8; lia| clear - R7; lia
        | replace (S1c + 216) with (S1c + 144 + 72) by (clear; lia); exact (asg2_216 _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR22)
        | replace (SA + 6 * 0) with SA by (clear; lia); replace (6 * (ns - 0)) with (6 * ns) by (clear; lia); exact SC2| exact SAP| exact T5
        | eapply (addressable_accessible _ _ _ _ _ ADS2); [apply Z.le_refl| apply Z.le_refl| clear - T5 ACB; unfold AAPP_HI; lia]| exact SNS
        | exact DSb2| exact BP| subst src; clear - BC PLE; lia| subst src; clear - CR SL7 ELR; lia| exact BH| exact ACCB2| exact NBL| clear - SBA NBL; lia
        | exact EC2| exact E1| unfold ENTRY_SIZE; exact E5
        | eapply (addressable_accessible _ _ _ _ _ AD2); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia]
        | unfold ENTRY_SIZE; clear - SEA; lia| exact AS1| clear - Q2 SPR; lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 (a2' & y0 & y1 & y2 & y3 & y4 & y5 & y6 & m3 & junk' & MU3 & WM3 & MI3 & SC3 & VIS3). cbn beta in VIS3.
    replace (SA + 6 * 0) with SA in MU3, SC3 by (clear; lia). replace (src - Bb + 4 * 0) with (src - Bb) in SC3 by (clear; lia).
    apply rw_cells_app in SC3. destruct SC3 as [SC3 _]. rewrite asuite_cells_eq in SC3.
    set (rows := srows bs (Z.to_nat (src - Bb)) (256 * kh5 + kl6) (Z.to_nat ns)) in SC3.
    assert (ROWS : zlength rows = ns /\ Forall row_ok rows) by (subst rows; split; [unfold zlength; rewrite srows_length; clear - NS1; lia| apply asrows_ok; clear - R5 R6; lia]). clearbody rows.
    pose proof (suite_cells_size rows) as SSZ. rewrite (proj1 ROWS) in SSZ.
    assert (ST3 : stk asegs m3 lo S1c) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; clear - T5 CEIL; lia]).
    assert (T23 : forall A' cs, rw_cells asegs m2 A' cs -> (A' + Z.of_nat (cells_size cs) <= SA \/ SA + 6 * ns <= A') -> rw_cells asegs m3 A' cs).
    { intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU3| exact WM3|]. cbn. split; [clear - HA; lia| exact I]. }
    pose proof DW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR12' & _ & FR22' & FR32' & _ & _ & _ & FF2 & FSH2 & LSH2 & _).
    assert (DW3 : adwkGc Lx NB S' M' LE (dsg1c (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (rem - 4)) (wz elen) (wz cur))
                    (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) um uf0 m3 s').
    { eapply (adwkG_wc Lx NB S' M' LE _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) um uf0 m2 s' m3 [(SA, SA + 6 * ns)]);
        [exact DW2| exact MU3| exact WM3| exact MI3| exact ST3| | apply T23; [exact FR12'| right; unfold dsg1, arp_sg1; cbn; clear - T5 AS1; lia]| exact SZ1
        | apply T23; [exact FR22'| right; unfold dsg2, arp_sg2; cbn; clear - T5 AS1; lia]| apply T23; [exact FR32'| right; unfold arp_sg3; cbn; clear - T5 AS1; lia]| exact SZ3
        | apply T23; [exact FF2| unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - T6 FQ5 FQ6; lia]
        | apply T23; [exact FSH2| unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?LSH2;
                      pose proof (sh_in_shadowland ff ltac:(unfold AAPP_HI; clear - FQ1 FQ2 ACB; lia)) as SIS; rewrite <- SHF in SIS; clear - SIS SHU SNS; lia]
        | exact LSH2].
      apply Forall_cons; [| apply Forall_nil]. do 6 right. exists (pS, SA, 6 * ns). split; [exact SINx| cbn; clear; lia]. }
    assert (FWA3 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(SA, SA + 6 * ns)]).
    { apply Forall_cons; [cbn; unfold ALOWSH_LO, AHI_LO in SNS |- *; clear - SNS; lia| apply Forall_nil]. }
    pose proof (T23 _ _ EC2 ltac:(unfold entry_cells; cbn [cells_size csize Nat.add length]; rewrite ?L1, ?L2, ?L3, ?L4; clear - SEA; lia)) as EC3.
    (* [comment removed for export] *)
    assert (ESH3 : ENTRY_shad m3 ee E1').
    { pose proof ESH2 as (ETOP2 & AD2' & OS12 & OS22 & OS32 & OS42 & XSH3). subst E1'. unfold ENTRY_shad, upd_suites in OS12, OS22, OS42, XSH3 |- *.
      cbn [en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o] in OS12, OS22, OS42, XSH3 |- *.
      split; [exact ETOP2|]. split.
      { eapply (ECH_AC14_decexts.addressable_acrossW _ m2 m3); [exact AD2'| exact MU3| exact WM3| clear - E1 E5 ACB; unfold AAPP_HI; lia| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia| exact FWA3]. }
      split; [rewrite PNO; exact I|]. split.
      { eapply (ECH_AC14_decexts.oshad_acrossW _ m2 m3); [exact OS22| exact MU3| exact WM3| | exact FWA3].
        destruct (en_pub_o E) as [[ip np0]|] eqn:PO; [| exact I].
        destruct (SUBF (ip, en_pub E, np0) ltac:(subst; unfold upd_suites; cbn; rewrite PNO, PO; cbn; left; reflexivity)) as (B0 & B5 & B3 & _ & INX).
        split; [exact B0|]. cbn. split; [| exact I].
        assert (NE : blk_id (ip, en_pub E, np0) <> blk_id (pS, SA, 6 * ns)).
        { cbn [blk_id fst snd]. apply (NPS (ip, en_pub E, np0)). right. apply in_or_app; right; apply in_or_app; left. rewrite PO. left; reflexivity. }
        pose proof (DISJ _ _ ltac:(apply in_or_app; right; apply SLX; exact INX) SIN NE) as K. cbn [blk_addr blk_size fst snd] in K. clear - K B3 NS1. lia. }
      split.
      { cbn [oshad]. split; [clear - T5 ACB; unfold AAPP_HI; lia|]. split.
        - eapply (ECH_AC14_decexts.addressable_acrossW _ m2 m3); [exact ADS2| exact MU3| exact WM3| clear - T1 T5 ACB NS1; unfold AAPP_HI; lia| clear - T5 ACB; unfold AAPP_HI; lia| exact FWA3].
        - exists (cells_bytes (suite_cells rows)). pose proof SC3 as [[WF3 _] _].
          eapply arw_cells_recut; [exact SC3| cbn [cells_wf cell_wf]; split; [rewrite (cells_bytes_length _ WF3); clear - SSZ NS1; lia| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity]. }
      split; [rewrite ENO; exact I| rewrite XO; exact I]. }
    pose proof (eobj_same_cells _ _ m3 _ _ E1' _ _ _ _ EO2 ltac:(unfold same_blocks; repeat split; reflexivity) ltac:(subst E1'; exact XO) L1 L2 L3 L4 EC3) as EO3.
    assert (AD3 : addressable m3 ee ENTRY_SIZE) by (destruct ESH3 as (_ & K & _); exact K).
    pose proof DW3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSb3 & _ & _ & _ & _ & _ & _ & FR13 & _ & FR23 & FR33 & _).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MF3 & IM3 & GM3 & ACCB3 & _).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3
      | eapply ade_seg7 with (q := S1c) (E := E1') (blen := nB) (r48 := elen - 7 - publen) (d1 := solo);
        [unfold dsg1 in FR13; exact FR13| unfold dsg2 in FR23; exact FR23| exact FR33| exact DSb3| exact BP| subst src; clear - BC PLE; lia| clear - SLR SL7; lia
        | subst src; clear - CR ELR; lia| exact BH| exact ACCB3| exact NBL| exact SOLR| clear - NS1; lia| clear - SAP; lia| clear - T5 ACB NS1; lia| clear - R5 R6; lia| clear - R8; lia| clear - R7; lia
        | exact EC3| exact E1| unfold ENTRY_SIZE; exact E5| unfold ENTRY_SIZE; clear - EBA NBL; lia
        | eapply (addressable_accessible _ _ _ _ _ AD3); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia]
        | unfold ENTRY_SIZE; exact ENS| exact AS1| clear - Q2 SPR; lia| exact MI3]|].
    intros msF4 mo4 KREL4 MP4 (a0' & a1' & a2'' & a3' & s4' & s9' & s10' & m4 & n0' & n1' & n2' & mx & line & MU4 & WM4 & MI4 & FR34 & EC4 & MXR & CASES).
    assert (ST4 : stk asegs m4 lo S1c) by (eapply stk_transport_disjoint; [exact ST3| exact MU4| exact WM4| cbn; clear - E5 CEIL; lia]).
    assert (T34 : forall A' cs, rw_cells asegs m3 A' cs -> (A' + Z.of_nat (cells_size cs) <= ee + 48 \/ ee + 49 <= A') -> (A' + Z.of_nat (cells_size cs) <= S1c + 264 \/ S1c + 288 <= A') -> rw_cells asegs m4 A' cs).
    { intros A' cs RC HA HB. eapply rw_cells_transport; [exact RC| exact MU4| exact WM4|]. cbn. split; [clear - HA; lia|]. split; [clear - HB; lia| exact I]. }
    assert (DW4 : adwkGc Lx NB S' M' LE (dsg1c (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (rem - 4)) (wz elen) (wz cur))
                    (wz ee) (arp_sg3 x0 x1 x2 n0' n1' n2' (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) um uf0 m4 s').
    { pose proof DW3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FF3 & FSH3 & LSH3 & _).
      eapply (adwkG_wc Lx NB S' M' LE _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) um uf0 m3 s' m4 [(ee + 48, ee + 49); (S1c + 264, S1c + 288)]);
        [exact DW3| exact MU4| exact WM4| exact MI4| exact ST4| | apply T34; [exact FR13| right; unfold dsg1, arp_sg1; cbn; clear - E5 AS1; lia| left; unfold dsg1, arp_sg1; cbn; clear; lia]| exact SZ1
        | apply T34; [exact FR23| right; unfold dsg2, arp_sg2; cbn; clear - E5 AS1; lia| left; unfold dsg2, arp_sg2; cbn; clear; lia]| exact FR34| reflexivity
        | apply T34; [exact FF3| unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - E6 FQ5 FQ6; lia| left; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - FQ2 AS1; lia]
        | apply T34; [exact FSH3| | ]; unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?LSH3;
            [pose proof (sh_in_shadowland ff ltac:(unfold AAPP_HI; clear - FQ1 FQ2 ACB; lia)) as SIS; rewrite <- SHF in SIS; clear - SIS SHU ENS; lia
            | left; rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - FQ2 ACB AS1; lia]
        | exact LSH3].
      apply Forall_cons; [do 6 right; exists (en_id E, ee, ENTRY_SIZE); split; [exact EINx| cbn; unfold ENTRY_SIZE; clear; lia]|].
      apply Forall_cons; [right; right; left; cbn; clear; lia| apply Forall_nil]. }
    assert (FWA4 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(ee + 48, ee + 49); (S1c + 264, S1c + 288)]).
    { apply Forall_cons; [cbn; unfold ALOWSH_LO, AHI_LO in ENS |- *; clear - ENS; lia|]. apply Forall_cons; [right; cbn; unfold AHI_LO; clear - ACB AS1; lia| apply Forall_nil]. }
    set (Em7 := upd_maxname E1' mx).
    assert (SB7 : same_blocks E1' Em7) by (subst Em7 E1'; unfold same_blocks, upd_maxname, upd_suites; cbn; repeat split; reflexivity).
    assert (ESH4 : ENTRY_shad m4 ee Em7).
    { apply (eshad_same m4 ee E1' Em7 SB7). eapply (eshad_acrossW _ m3 m4 ee E1'); [exact ESH3| exact MU4| exact WM4| clear - E1; lia| exact FWA4| | subst E1'; exact XO].
      intros b Hb. destruct (SUBF b Hb) as (B0 & B5 & B3 & APT & _). split; [exact B0| cbn; clear - APT B5 B3 AS1; lia]. }
    pose proof (eobj_same_cells _ _ m4 _ _ Em7 _ _ _ _ EO3 SB7 ltac:(subst E1'; exact XO) L1 L2 L3 L4 EC4) as EO4.
    assert (PE4 : Permutation (blocks_ENTRY ee Em7) Lx) by (rewrite (same_blocks_ENTRY ee E1' Em7 SB7); exact PE1).
    pose proof (T34 _ _ SC3 ltac:(rewrite SSZ; clear - SEA NS1; lia) ltac:(rewrite SSZ; clear - T5 AS1; lia)) as SC4.
    assert (TAILB : dbudc (drestc Lx NB LE) M' (4 * ERRDEBUG_BYTES) 8 /\ um + errph_bytes (mid_err M') + 4 * ERRDEBUG_BYTES <= DECODE_CUM_BYTES
                    /\ uf0 + errph_bytes (mid_err M') + lb_bytes Lx + 4 * ERRDEBUG_BYTES + 8192 <= DECODE_CUM_BYTES).
    { split; [| split].
      - unfold dbud in *. rewrite (drest_app LB p A nA pbin Bb nB TB Lx NB LE), lb_bytes_app, length_app, Nat2Z.inj_add. unfold ENTRY_BYTES, ENTRY_CNT, ENTRY_SIZE, ERRDEBUG_BYTES in *.
        pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR SL7 PLE SLR; lia) ltac:(clear; lia)) as DP. clear - DB0 LB1 LBN DP ELR SL7 PLE SLR SO4. lia.
      - unfold ENTRY_CM, ENTRY_SIZE, ERRDEBUG_BYTES in *. clear - UMQ UMB ELR SL7 PLE SLR SO4. lia.
      - unfold ENTRY_CF, ENTRY_SIZE, ERRDEBUG_BYTES in *. clear - UFB LB1 ELR SL7 PLE SLR SO4. lia. }
    destruct TAILB as (TB1 & TB2 & TB3).
    destruct CASES as [(LN & VIS4)|(nl & SO2 & NQ & SNL & MX & -> & -> & -> & -> & VIS4)].
    - (* [comment removed for export] *)
      eapply (KTA' Lx M' LE (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (rem - 4)) (wz elen) (wz cur) x0 x1 x2 n0' n1' n2' (wz (cur + 9)) (wz Bb) (wz publen) 0 um uf0 (b8 0) (poison_bytes 256 0) m4 s' msF4 mo4 ee line);
        [exact DW4| exact EO4| exact ESH4| exact PE4| clear - LN; lia| exact TB1| exact TB2| exact TB3| exact VIS4| exact KREL4
        | exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 (ah_mpres_trans H HH _ _ _ MP3 MP4)))].
    - (* [comment removed for export] *)
      idtac "P5_MEMCHR".
      pose proof DW4 as (HP4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSb4 & _ & _ & _ & _ & _ & _ & FR14 & _ & FR24 & FR34' & _ & _ & _ & FF4 & FSH4 & LSH4 & _ & _ & _ & _ & AC4 & _).
      destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW4) as (_ & _ & _ & _ & _ & _ & IB4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & ACCB4 & _).
      pose proof (bz_range bs (Z.to_nat (src - Bb + sl + 1))) as NLR. rewrite <- NQ in NLR.
      assert (NPR : Bb + 11 <= src + sl + 2 /\ src + sl + 2 + nl <= Bb + zlength bs) by (subst src; clear - BC PLE SLR SNL CR ELR; lia).
      destruct NPR as [NP1 NP2].
      pose proof CR as CRq. pose proof NP2 as NP2q. unfold zlength in CRq, NP2q.
      destruct (abytes_at_sub m4 Bb bs (src + sl + 2 - Bb) nl DSb4 ltac:(clear - NP1; lia) ltac:(clear - NLR; lia) ltac:(clear - NP2q; lia)) as [BSN NML].
      replace (Bb + (src + sl + 2 - Bb)) with (src + sl + 2) in BSN by (clear; lia).
      set (nm := firstn (Z.to_nat nl) (skipn (Z.to_nat (src + sl + 2 - Bb)) bs)) in *.
      pose proof (ah_blk_shvis H HH _ _ _ _ _ _ HP4 IB4) as SVB. cbn [blk_addr blk_size fst snd] in SVB.
      eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4
        | eapply memchr_icpt0_ok with (buf := nm) (lo := lo); rewrite ?unsigned_lit by (clear - NP1 NP2 BP BH ACB NLR Q2 SPR CEIL LOS LO0; lia);
          [exact BSN| exact NML| clear - NLR; lia| clear - NP1 BP; lia
          | eapply accessible_sub; [exact ACCB4| clear - NP1; lia| clear - NP2 NBL; lia| clear - NLR; lia]
          | eapply shvis_sub; [exact SVB| clear - BP; lia| clear - NP1; lia| clear - NP2 NBL; lia| clear - NLR; lia| clear - BP NBR; lia]
          | exact ST4| exact CEIL| unfold AINTRIN_STACK; clear - LOS; lia| exact MI4| exact AC4
          | eapply aapp_in_app_mem; [exact APB| clear - NP1; lia| clear - NP2 NBL; lia]
          | left; clear - NP2 BH CEIL; lia]|].
      intros msF5 mo5 KREL5 MP5 PO5. unfold amemchr_post in PO5.
      destruct PO5 as (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & m5 & VIS5 & MU5 & WM5 & MI5 & ST5 & BS5 & AC5).
      rewrite (unsigned_lit S1c) in MU5, ST5 by (clear - Q2 SPR CEIL LOS LO0; lia). rewrite (unsigned_lit (src + sl + 2)) in VIS5, BS5 by (clear - NP1 NP2 BP BH ACB NLR; lia).
      rewrite (unsigned_lit 0) in VIS5 by (clear; lia). rewrite (unsigned_lit nl) in VIS5 by (clear - NLR; lia). change (0 mod 256) with 0 in VIS5.
      destruct (amemchr_res_range (src + sl + 2) 0 nl nm ltac:(clear - NP1 BP; lia)) as [RR RZ]. rewrite NML in RR.
      set (mres := memchr_res (src + sl + 2) 0 nl nm) in *.
      assert (T45 : forall A' cs, rw_cells asegs m4 A' cs -> (A' + Z.of_nat (cells_size cs) <= lo \/ S1c <= A') -> rw_cells asegs m5 A' cs).
      { intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU5| exact WM5|]. cbn. unfold AINTRIN_STACK. split; [clear - HA LOS; lia| exact I]. }
      assert (DW5 : adwkGc Lx NB S' M' LE (dsg1c (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (rem - 4)) (wz elen) (wz cur))
                      (wz ee) (arp_sg3 x0 x1 x2 (wz (src + sl + 2)) (wz Bb) (wz nl) (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) um uf0 m5 s').
      { eapply (adwkG_wc Lx NB S' M' LE _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) um uf0 m4 s' m5 [(S1c - AINTRIN_STACK, S1c)]);
          [exact DW4| exact MU5| exact WM5| exact MI5| exact ST5| apply Forall_cons; [left; cbn; unfold AINTRIN_STACK; clear - LOS; lia| apply Forall_nil]
          | apply T45; [exact FR14| right; clear; lia]| exact SZ1| apply T45; [exact FR24| right; clear; lia]| apply T45; [exact FR34'| right; clear; lia]| reflexivity
          | apply T45; [exact FF4| left; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - FQ6 AF2 CEIL; lia]
          | apply T45; [exact FSH4| left; unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?LSH4;
                        pose proof (sh_add8 ff 512) as SY8; replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia); pose proof (sh_mono (ff + 4096) _ FQ6) as SYU; pose proof (sh_mono _ _ AF2) as SYA;
                        rewrite SHF; clear - SY8 SYU SYA SHC CEIL; lia]
          | exact LSH4]. }
      assert (FWA5 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(S1c - AINTRIN_STACK, S1c)]).
      { apply Forall_cons; [right; cbn; unfold AHI_LO, AINTRIN_STACK; clear - ACB CEIL LOS; lia| apply Forall_nil]. }
      assert (ESH5 : ENTRY_shad m5 ee Em7).
      { apply (eshad_same m5 ee E1' Em7 SB7). eapply (eshad_acrossW _ m4 m5 ee E1'); [apply (eshad_same m4 ee Em7 E1'); [| exact ESH4]| exact MU5| exact WM5| clear - E1; lia| exact FWA5| | subst E1'; exact XO].
        - clear - SB7. destruct SB7 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11). unfold same_blocks. rewrite Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11. repeat split; reflexivity.
        - intros b Hb. destruct (SUBF b Hb) as (B0 & B5 & B3 & APT & _). split; [exact B0| cbn; unfold AINTRIN_STACK; clear - B5 B3 CEIL LOS; lia]. }
      pose proof (T45 _ _ EC4 ltac:(left; unfold entry_cells; cbn [cells_size csize Nat.add length]; rewrite ?L1, ?L2, ?L3, ?L4; clear - E5 CEIL; lia)) as EC5.
      pose proof (eobj_same_cells _ _ m5 _ _ Em7 _ _ _ _ EO4 ltac:(unfold same_blocks; repeat split; reflexivity) ltac:(subst Em7 E1'; exact XO) L1 L2 L3 L4 EC5) as EO5.
      pose proof (T45 _ _ SC4 ltac:(left; rewrite SSZ; clear - T5 CEIL; lia)) as SC5.
      pose proof DW5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR25 & _).
      (* [comment removed for export] *)
      eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5
        | eapply ade_seg8; [unfold dsg2 in FR25; exact FR25| clear - NLR; lia| subst mres; clear - RR NP1 NP2 BH ACB BP; lia| clear - E1; lia| unfold ENTRY_SIZE; clear - E5 ACB; lia| clear - AS1 ACB; lia| clear - Q2 SPR; lia| exact MI5]|].
      intros msF6 mo6 KREL6 MP6 [[_ VIS6]|(N4 & R0 & VIS6)].
      + (* [comment removed for export] *)
        eapply (KTA' Lx M' LE (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz solo) (wz (rem - 4)) (wz elen) (wz cur) x0 x1 x2 (wz (src + sl + 2)) (wz Bb) (wz nl) (wz (cur + 9)) (wz Bb) (wz publen) 0 um uf0 (b8 0) (poison_bytes 256 0) m5 s' msF6 mo6 ee 431);
          [exact DW5| exact EO5| exact ESH5| exact PE4| clear; lia| exact TB1| exact TB2| exact TB3| exact VIS6| exact KREL6
          | exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 (ah_mpres_trans H HH _ _ _ MP3 (ah_mpres_trans H HH _ _ _ MP4 (ah_mpres_trans H HH _ _ _ MP5 MP6)))))].
      + (* [comment removed for export] *)
        eapply (de_phase6 cur rem elen publen kh5 kl6 ph7 sl solo ns nl Lx NB S' M' LE x0 x1 x2 um uf0 um0 uf0 m5 s' msF6 mo6 ee SA pS Em7 rows nm);
          [exact DW5| exact EO5| exact ESH5| exact PE4
          | subst Em7 E1'; reflexivity| subst Em7 E1'; reflexivity| subst Em7 E1'; cbn; exact NSE| subst Em7 E1'; cbn; exact PNO| subst Em7 E1'; cbn; exact ENO| subst Em7 E1'; cbn; exact XE0| subst Em7 E1'; cbn; exact XO
          | subst Em7 E1'; cbn; exact LT0| subst Em7 E1'; cbn; exact FRY0
          | exact SC5| exact (proj1 ROWS)| exact (proj2 ROWS)| exact NS1| exact SO4
          | subst nm src; reflexivity| unfold zlength; exact NML| | clear - N4 NLR; lia
          | exact LB1| exact LBN| exact BC| exact PLE| exact SOLR| exact SLR| subst src; clear - SNL; lia| exact ELR| exact CR| exact R5| exact R6| exact R7| exact DB0
          | exact UMQ| reflexivity| exact UMB| exact UFB| exact NENT| exact KADV| exact KTA| exact KTZ| exact KTX| exact VIS6| exact KREL6
          | exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 (ah_mpres_trans H HH _ _ _ MP3 (ah_mpres_trans H HH _ _ _ MP4 (ah_mpres_trans H HH _ _ _ MP5 MP6)))))].
        apply afind_byte_None_notin; [| clear; lia]. rewrite <- (firstn_all2 (n := Z.to_nat nl) nm) at 1 by (clear - NML; lia). apply RZ; [exact R0| clear - NP1 BP; lia].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma de_phase4 : forall (cur rem elen publen kh5 kl6 ph7 pl8 : Z) (Lx NB : list block) (S' : storerep) (M' : libmid) (LE : list block)
      (w48 w72 : word) (x0 x1 x2 n0 n1 n2 : word) (um uf um0 uf0 : Z)
      (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model) (ee : Z) (E : entrep)
      (rax u0 u1 u2 a1w a2w a3w a4w a5w a6w a7w s10w u3 u4 u5 u6 : word),
    adwkGc Lx NB S' M' LE (dsg1c (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) w48 (wz kl6) (wz kh5) w72 (wz (rem - 4)) (wz elen) (wz cur)) (wz ee)
           (arp_sg3 x0 x1 x2 n0 n1 n2 (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) um uf m' s' ->
    ENTRYobj (drestc Lx NB LE) m' ee E -> ENTRY_shad m' ee E -> Permutation (blocks_ENTRY ee E) Lx ->
    en_suites_o E = None -> en_pname_o E = None -> en_encoded_o E = None -> en_exts E = 0 -> en_exts_o E = None -> en_loadtime E = 0 -> en_forretry E = 0 ->
    lb_bytes Lx <= ENTRY_SIZE + publen -> Z.of_nat (length Lx) <= 2 ->
    Bb + 2 <= cur -> 0 <= publen -> 5 + publen <= elen -> 4 + elen <= rem -> cur + rem <= Bb + zlength bs ->
    0 <= kh5 < 256 -> 0 <= kl6 < 256 -> 0 <= ph7 < 256 -> 0 <= pl8 < 256 -> publen = 256 * ph7 + pl8 ->
    dbudc (drestc [] NB LE) M' (ENTRY_BYTES rem) (ENTRY_CNT rem) ->
    um <= um0 + ENTRY_SIZE + publen -> uf = uf0 ->
    um0 + errph_bytes (mid_err M') + ENTRY_CM rem <= DECODE_CUM_BYTES -> uf0 + errph_bytes (mid_err M') + ENTRY_CF rem <= DECODE_CUM_BYTES -> nent S' <= 65 ->
    KADVc cur rem NB S' um0 uf0 (mid_err M') -> KTAc NB S' -> KTZc NB S' -> KTXc NB S' ->
    as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 1) a1w a2w a3w a4w a5w a6w a7w
                                (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 SH) (Z_to_bv 64 pl8) (Z_to_bv 64 (elen - 5)) (Z_to_bv 64 (cur + 9)) (Z_to_bv 64 ASHB)
                                (Z_to_bv 64 (256 * ph7)) (Z_to_bv 64 publen) s10w (Z_to_bv 64 400) u3 u4 u5 u6)
                        F (ret_pc (Z_to_bv 64 ADE_R2)) fc None m' (seg_rom asegs) ->
    as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
    as_SR H POSTc (mkCfg msF' mo').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH AUXV TIME.
    intros until u6. intros DW EO ESH PE SUO PNO ENO XE0 XO LT0 FRY0 LB1 LBN BC PLE PL5 ELR CR R5 R6 R7 R8 PEQ DB0 UMQ UFQ UMB UFB NENT KADV KTA KTZ KTX VIS1 KREL1 MP1.
    pose proof KTA as KTA'. unfold dK_tailA in KTA'. pose proof KTZ as KTZ'. unfold dK_tailZ in KTZ'. subst uf.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (AS1 & Q2 & Q1 & SPR & BP & BH & IB2 & NBL & NB15 & BLX & BEL & BRS & F1 & MF & IM & GM & ACCB & APB & ACB & LOS & LO0).
    destruct rc_facts_c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AFSB & _). pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (SHL : ASHB + AIMG_TOP / 8 <= SH) by (unfold ASHB, AIMG_TOP; rewrite Z.shiftr_div_pow2 by (clear; lia); clear - FQ1; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (SHU : SH + 512 < AHI_LO) by (rewrite SHF; unfold sh, AHI_LO; rewrite ASHADOW_BASE_val; clear - FQ2 ACB; lia).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
    pose proof (dec_stack M M' STP) as DSK. pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    pose proof (ah_costs H HH) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd).
    (* [comment removed for export] *)
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC1) & EINr & OF1 & OF2 & OF3 & OF4 & XT).
    assert (EINx : In (en_id E, ee, ENTRY_SIZE) Lx) by (eapply Permutation_in; [exact PE| left; reflexivity]).
    pose proof (drest_subc Lx NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    assert (EIN : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M' ++ drestc Lx NB LE)) by (apply in_or_app; right; apply SLX; exact EINx).
    pose proof (BRS _ EIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
    pose proof (BLX _ EINx) as EBA. cbn [blk_addr blk_size fst snd] in EBA. pose proof (aapp_not_shadowland _ _ E7) as ENS.
    unfold ENTRY_SIZE in E5, E6, EBA, ENS. unfold AIMG_TOP in E4. unfold AFS_SIZE in E6.
    pose proof ESH as (ETOP & AD & _). unfold ENTRY_SIZE in ETOP.
    assert (ES0 : en_suites E = 0) by (rewrite SUO in OF3; exact OF3).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1
      | eapply ade_seg4 with (q := S1c) (blen := nB);
        [unfold dsg1 in FR1; exact FR1| unfold dsg2 in FR2; exact FR2| exact DSb1| clear - BC; lia| exact PLE| exact PL5| clear - CR ELR; lia| exact BP| exact BH| exact ACCB| exact NBL
        | exact R7| exact R8| exact EC1| exact E1| unfold ENTRY_SIZE; exact E5| unfold ENTRY_SIZE; clear - EBA NBL; lia
        | eapply (addressable_accessible _ _ _ _ _ AD); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia]
        | unfold ENTRY_SIZE; exact ENS| exact AS1| clear - Q2 SPR; lia| exact MI1]|].
    intros msF2 mo2 KREL2 MP2 (a0' & a1' & a2' & a3' & a4' & s2' & s5' & s9' & m2 & w48' & w72' & ns & MU2 & WM2 & MI2 & FR1' & EC2 & NSR & CASES).
    (* [comment removed for export] *)
    assert (ST2 : stk asegs m2 lo S1c) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| cbn; clear - E5 CEIL; lia]).
    assert (T12 : forall A' cs, rw_cells asegs m' A' cs ->
              (A' + Z.of_nat (cells_size cs) <= S1c + 48 \/ S1c + 56 <= A') -> (A' + Z.of_nat (cells_size cs) <= S1c + 72 \/ S1c + 80 <= A') ->
              (A' + Z.of_nat (cells_size cs) <= ee \/ ee + 104 <= A') -> rw_cells asegs m2 A' cs).
    { intros A' cs RC HA HB HE. eapply rw_cells_transport; [exact RC| exact MU2| exact WM2|]. cbn. split; [clear - HA; lia|]. split; [clear - HB; lia|]. split; [clear - HE; lia| exact I]. }
    pose proof (T12 _ _ FR3 ltac:(right; cbn; clear; lia) ltac:(right; cbn; clear; lia) ltac:(right; cbn; clear - E5 AS1; lia)) as FR3'.
    assert (DW2 : adwkGc Lx NB S' M' LE (arp_sg1 (wz AR_INTERNAL_ERROR) (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) w48' (wz kl6) (wz kh5) w72' (wz AECH_VERSION) (wz ADE_FILE) (wz A) (wz bt) (wz (rem - 4)) (wz Bb) (wz elen) (wz cur))
                    (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) um uf0 m2 s').
    { eapply (adwkG_wc Lx NB S' M' LE _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) um uf0 m' s' m2 [(S1c + 48, S1c + 56); (S1c + 72, S1c + 80); (ee + 32, ee + 36)]);
        [exact DW| exact MU2| exact WM2| exact MI2| exact ST2| | exact FR1'| reflexivity| | exact FR3'| reflexivity| | | reflexivity].
      - apply Forall_cons; [right; left; cbn; clear; lia|]. apply Forall_cons; [right; left; cbn; clear; lia|].
        apply Forall_cons; [| apply Forall_nil]. do 6 right. exists (en_id E, ee, ENTRY_SIZE). split; [exact EINx| cbn; unfold ENTRY_SIZE; clear; lia].
      - apply T12; [unfold dsg2 in FR2; exact FR2| right; cbn; clear; lia| right; cbn; clear; lia| right; cbn; clear - E5 AS1; lia].
      - apply T12; [exact FF1| | |]; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; [left; clear - FQ2 AS1; lia| left; clear - FQ2 AS1; lia| clear - E6 FQ5 FQ6; lia].
      - apply T12; [exact FSH1| | |]; unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?LSH1;
          [left; rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - FQ2 ACB AS1; lia
          | left; rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - FQ2 ACB AS1; lia
          | pose proof (sh_in_shadowland ff ltac:(unfold AAPP_HI; clear - FQ1 FQ2 ACB; lia)) as SIS; rewrite <- SHF in SIS; clear - SIS SHU ENS; lia]. }
    assert (FWA : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(S1c + 48, S1c + 56); (S1c + 72, S1c + 80); (ee + 32, ee + 36)]).
    { apply Forall_cons; [right; cbn; unfold AHI_LO; clear - ACB AS1; lia|]. apply Forall_cons; [right; cbn; unfold AHI_LO; clear - ACB AS1; lia|].
      apply Forall_cons; [cbn; unfold ALOWSH_LO, AHI_LO in ENS |- *; clear - ENS; lia| apply Forall_nil]. }
    set (En2 := upd_nsuites E ns).
    assert (SB2 : same_blocks E En2) by (subst En2; unfold same_blocks, upd_nsuites; cbn; repeat split; reflexivity).
    assert (ESH2 : ENTRY_shad m2 ee En2).
    { apply (eshad_same m2 ee E En2 SB2). eapply (eshad_acrossW _ m' m2 ee E); [exact ESH| exact MU2| exact WM2| clear - E1; lia| exact FWA| | exact XO].
      intros b Hb. destruct (ade_subblocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW PE b (in_ext5 _ _ _ _ _ _ Hb)) as (_ & _ & BR & APT).
      pose proof BR as (B1 & _ & B3 & _ & B5 & _). unfold ENTRY_SIZE in APT. split; [clear - B1 B3 B5 ACB; unfold AAPP_HI; lia| cbn; clear - APT B5 AS1 B3; lia]. }
    pose proof (eobj_same_cells _ _ m2 _ _ En2 _ _ _ _ EO SB2 XO L1 L2 L3 L4 EC2) as EO2.
    assert (PE2 : Permutation (blocks_ENTRY ee En2) Lx) by (rewrite (same_blocks_ENTRY ee E En2 SB2); exact PE).
    clear T12.
    destruct CASES as [VIS2|(sl & SEQ & SL1 & SLEV & SL7 & NSQ & -> & -> & VIS2)].
    - (* [comment removed for export] *)
      eapply (KTA' Lx M' LE (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) w48' (wz kl6) (wz kh5) w72' (wz (rem - 4)) (wz elen) (wz cur) x0 x1 x2 n0 n1 n2 (wz (cur + 9)) (wz Bb) (wz publen) 0 um uf0 (b8 0) (poison_bytes 256 0) m2 s' msF2 mo2 ee 400);
        [exact DW2| exact EO2| exact ESH2| exact PE2| clear; lia| | | | exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)].
      + unfold dbud in *. rewrite (drest_app LB p A nA pbin Bb nB TB Lx NB LE), lb_bytes_app, length_app, Nat2Z.inj_add. unfold ENTRY_BYTES, ENTRY_CNT, ENTRY_SIZE, ERRDEBUG_BYTES in *.
        pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR PL5 PLE; lia) ltac:(clear; lia)) as DP. clear - DB0 LB1 LBN DP ELR PL5 PLE. lia.
      + unfold ENTRY_CM, ENTRY_SIZE, ERRDEBUG_BYTES in *. clear - UMQ UMB ELR PL5 PLE. lia.
      + unfold ENTRY_CF, ENTRY_SIZE, ERRDEBUG_BYTES in *. clear - UFB LB1 ELR PL5 PLE. lia.
    - (* [comment removed for export] *)
      idtac "P4_MARR".
      pose proof DW2 as (HP2 & LM2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSb2 & _ & _ & _ & _ & _ & _ & FR12 & _ & FR22 & FR32 & _ & _ & _ & FF2 & FSH2 & LSH2 & RFS2 & [errv2 ERR2] & AUX2 & _ & AC2 & _ & STK2 & CHN2 & _ & LED2).
      destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MF2 & IM2 & GM2 & ACCB2 & _).
      assert (AD2 : addressable m2 ee ENTRY_SIZE) by (destruct ESH2 as (_ & K & _); exact K).
      assert (SLR : 0 <= sl < 2^16).
      { pose proof (bz_range bs (Z.to_nat (cur - Bb + (9 + publen)))) as R9. pose proof (bz_range bs (Z.to_nat (cur - Bb + (10 + publen)))) as R10. clear - SEQ R9 R10. lia. }
      assert (NSR' : 0 <= ns < 2^14) by (rewrite NSQ; clear - SLR; Z.div_mod_to_equations; lia). assert (NS0' : 0 <= ns) by (clear - NSR'; lia).
      assert (CHBx : forall fp' ra', In (fp', ra') CH1c -> S1c + 16 <= fp').
      { intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
      destruct (Z.eq_dec ns 0) as [NS0|NSP].
      + (* [comment removed for export] *)
        rewrite NS0 in VIS2.
        eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2
          | eapply acmalloc_array0_spec with (lo := lo);
            [rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact ST2| exact CEIL| rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); unfold FR_CRYPTO_array, FR_CRYPTO_malloc; clear - LOS; lia
            | exact MI2| exact AC2| exact IM2| exact GM2]|].
        intros msF3 mo3 KREL3 MP3 (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m3 & VIS3 & MU3 & WM3 & MI3 & AC3 & ST3).
        rewrite (unsigned_lit S1c) in MU3, ST3 by (clear - Q2 SPR CEIL LOS LO0; lia).
        assert (T23 : forall A' cs, rw_cells asegs m2 A' cs -> (A' + Z.of_nat (cells_size cs) <= lo \/ S1c <= A') -> rw_cells asegs m3 A' cs).
        { intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU3| exact WM3|]. cbn. split; [clear - HA; lia| exact I]. }
        pose proof FF2 as [[WFf _] _]. unfold dff, arp_fframe2 in WFf. cbn in WFf.
        assert (DW3 : adwkGc Lx NB S' M' LE (arp_sg1 (wz AR_INTERNAL_ERROR) (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz (bz bs (Z.to_nat (cur - Bb + (10 + publen))))) (wz AECH_VERSION) (wz ADE_FILE) (wz A) (wz bt) (wz (rem - 4)) (wz Bb) (wz elen) (wz cur))
                        (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) um uf0 m3 s').
        { eapply (adwkG_wc Lx NB S' M' LE _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) um uf0 m2 s' m3 [(lo, S1c)]);
            [exact DW2| exact MU3| exact WM3| exact MI3| exact ST3| apply Forall_cons; [left; cbn; split; apply Z.le_refl| apply Forall_nil]
            | apply T23; [exact FR12| right; clear; lia]| reflexivity| apply T23; [exact FR22| right; clear; lia]| apply T23; [exact FR32| right; clear; lia]| reflexivity
            | apply T23; [exact FF2| left; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - FQ6 AF2 CEIL; lia]
            | apply T23; [exact FSH2| left; unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?LSH2;
                          pose proof (sh_add8 ff 512) as SY8; replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia); pose proof (sh_mono (ff + 4096) _ FQ6) as SYU; pose proof (sh_mono _ _ AF2) as SYA;
                          rewrite SHF; clear - SY8 SYU SYA SHC CEIL; lia]
            | exact LSH2]. }
        pose proof (T23 _ _ EC2 ltac:(left; unfold entry_cells; cbn [cells_size csize Nat.add length]; rewrite ?L1, ?L2, ?L3, ?L4; clear - E5 CEIL; lia)) as EC3.
        assert (FWA3 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, S1c)]) by (apply Forall_cons; [right; cbn; unfold AHI_LO; clear - ACB CEIL; lia| apply Forall_nil]).
        assert (ESH3 : ENTRY_shad m3 ee En2).
        { eapply (eshad_acrossW _ m2 m3 ee En2); [exact ESH2| exact MU3| exact WM3| clear - E1; lia| exact FWA3| | subst En2; exact XO].
          intros b Hb. destruct (ade_subblocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW2 PE2 b (in_ext5 _ _ _ _ _ _ Hb)) as (_ & _ & BR & APT).
          pose proof BR as (B1 & _ & B3 & _ & B5 & _). split; [clear - B1 B3 B5 ACB; unfold AAPP_HI; lia| cbn; clear - B5 CEIL B3; lia]. }
        pose proof (eobj_same_cells _ _ m3 _ _ En2 _ _ _ _ EO2 ltac:(unfold same_blocks; repeat split; reflexivity) ltac:(subst En2; exact XO) L1 L2 L3 L4 EC3) as EO3.
        assert (AD3 : addressable m3 ee ENTRY_SIZE) by (destruct ESH3 as (_ & K & _); exact K).
        pose proof DW3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR13 & _ & FR23 & FR33 & _ & _ & _ & FF3 & FSH3 & LSH3 & _ & _ & _ & _ & AC3' & _ & STK3 & _).
        (* [comment removed for export] *)
        eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3
          | eapply ade_seg5 with (q := S1c) (E := En2) (publen := publen) (cur := cur);
            [exact FR13| exact R5| exact R6| exact R7| exact R8| exact PEQ| clear; lia| apply Z.le_refl| clear; lia| clear - BC BP PLE; lia
            | clear - CR BH AS1 SL7 SLR ELR Q2 SPR; lia| clear - BC BP PLE; lia
            | exact EC3| exact E1| unfold ENTRY_SIZE; exact E5
            | eapply (addressable_accessible _ _ _ _ _ AD3); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia]
            | exact AS1| clear - Q2 SPR; lia| exact MI3]|].
        intros msF4 mo4 KREL4 MP4 (m4 & MU4 & WM4 & MI4 & EC4 & [[_ VIS4]|[ABS _]]); [| exfalso; clear - ABS; lia].
        assert (ST4 : stk asegs m4 lo S1c) by (eapply stk_transport_disjoint; [exact ST3| exact MU4| exact WM4| cbn; clear - E5 CEIL; lia]).
        assert (T34 : forall A' cs, rw_cells asegs m3 A' cs -> (A' + Z.of_nat (cells_size cs) <= ee \/ ee + 104 <= A') -> rw_cells asegs m4 A' cs).
        { intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU4| exact WM4|]. cbn. split; [clear - HA; lia| exact I]. }
        assert (DW4 : adwkGc Lx NB S' M' LE (arp_sg1 (wz AR_INTERNAL_ERROR) (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz (bz bs (Z.to_nat (cur - Bb + (10 + publen))))) (wz AECH_VERSION) (wz ADE_FILE) (wz A) (wz bt) (wz (rem - 4)) (wz Bb) (wz elen) (wz cur))
                        (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) um uf0 m4 s').
        { eapply (adwkG_wc Lx NB S' M' LE _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) um uf0 m3 s' m4 [(ee + 40, ee + 48)]);
            [exact DW3| exact MU4| exact WM4| exact MI4| exact ST4| | apply T34; [exact FR13| right; cbn; clear - E5 AS1; lia]| reflexivity| apply T34; [exact FR23| right; cbn; clear - E5 AS1; lia]
            | apply T34; [exact FR33| right; cbn; clear - E5 AS1; lia]| reflexivity
            | apply T34; [exact FF3| unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - E6 FQ5 FQ6; lia]
            | apply T34; [exact FSH3| unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?LSH3;
                          pose proof (sh_in_shadowland ff ltac:(unfold AAPP_HI; clear - FQ1 FQ2 ACB; lia)) as SIS; rewrite <- SHF in SIS; clear - SIS SHU ENS; lia]
            | exact LSH3].
          apply Forall_cons; [| apply Forall_nil]. do 6 right. exists (en_id E, ee, ENTRY_SIZE). split; [exact EINx| cbn; unfold ENTRY_SIZE; clear; lia]. }
        set (En4 := upd_suites En2 0 (en_suites_o En2)).
        assert (SB4 : same_blocks En2 En4) by (subst En4 En2; unfold same_blocks, upd_suites, upd_nsuites; cbn; rewrite ES0; repeat split; reflexivity).
        assert (FWA4 : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(ee + 40, ee + 48)]).
        { apply Forall_cons; [cbn; unfold ALOWSH_LO, AHI_LO in ENS |- *; clear - ENS; lia| apply Forall_nil]. }
        assert (ESH4 : ENTRY_shad m4 ee En4).
        { apply (eshad_same m4 ee En2 En4 SB4). eapply (eshad_acrossW _ m3 m4 ee En2); [exact ESH3| exact MU4| exact WM4| clear - E1; lia| exact FWA4| | subst En2; exact XO].
          intros b Hb. destruct (ade_subblocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW3 PE2 b (in_ext5 _ _ _ _ _ _ Hb)) as (_ & _ & BR & APT).
          pose proof BR as (B1 & _ & B3 & _ & B5 & _). unfold ENTRY_SIZE in APT. split; [clear - B1 B3 B5 ACB; unfold AAPP_HI; lia| cbn; clear - APT B5 B3; lia]. }
        pose proof (eobj_same_cells _ _ m4 _ _ En4 _ _ _ _ EO3 SB4 ltac:(subst En2; exact XO) L1 L2 L3 L4 EC4) as EO4.
        assert (PE4 : Permutation (blocks_ENTRY ee En4) Lx) by (rewrite (same_blocks_ENTRY ee En2 En4 SB4); exact PE2).
        eapply (KTZ' Lx M' LE (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz (bz bs (Z.to_nat (cur - Bb + (10 + publen))))) (wz (rem - 4)) (wz elen) (wz cur) x0 x1 x2 n0 n1 n2 (wz (cur + 9)) (wz Bb) (wz publen) 0 um uf0 (b8 0) (poison_bytes 256 0) m4 s' msF4 mo4 ee);
          [exact DW4| exact EO4| exact ESH4| exact PE4| | | | exact VIS4| exact KREL4| exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 (ah_mpres_trans H HH _ _ _ MP3 MP4)))].
        * unfold dbud in *. rewrite (drest_app LB p A nA pbin Bb nB TB Lx NB LE), lb_bytes_app, length_app, Nat2Z.inj_add. unfold ENTRY_BYTES, ENTRY_CNT, ENTRY_SIZE, ERRDEBUG_BYTES in *.
          pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR PL5 PLE; lia) ltac:(clear; lia)) as DP. clear - DB0 LB1 LBN DP ELR PL5 PLE. lia.
        * unfold ENTRY_CM, ENTRY_SIZE, ERRDEBUG_BYTES in *. clear - UMQ UMB ELR PL5 PLE. lia.
        * unfold ENTRY_CF, ENTRY_SIZE, ERRDEBUG_BYTES in *. clear - UFB LB1 ELR PL5 PLE. lia.
      + (* [comment removed for export] *)
        idtac "P4_MARR1".
        pose proof (acmalloc_array_spec H HH) as CA. unfold cmalloc_array_stmt in CA.
        eapply (ah_seq H HH).
        { eapply CA with (lo := lo) (B := B) (LB := mid_errblocks M' ++ drestc Lx NB LE) (s := s') (num := ns) (size := 6) (v := 1) (errv := errv2) (CH := CH1c); clear CA.
          all: try first [exact VIS2| exact HP2| exact KREL2| exact AUX2| exact MI2| exact CEIL| exact AC2| exact CHN2| exact ERR2| exact MF2| exact IM2| exact GM2].
          all: lazymatch goal with
               | |- _ = Z_to_bv _ _ => reflexivity
               | |- Z_to_bv 64 ATP = _ => reflexivity
               | |- 0 <= 6 < 2 ^ 32 => clear; lia
               | |- 0 <= _ < 2 ^ 32 => clear - NSR'; lia
               | |- 1 <= _ <= 2 ^ 28 => clear - NSR' NSP; lia
               | |- lb_bytes _ + _ <= _ => unfold dbud in DB0; rewrite (drest_app LB p A nA pbin Bb nB TB Lx NB LE), !lb_bytes_app in *; unfold ENTRY_BYTES, ENTRY_SIZE in *; clear - DB0 EB EBR' LB1 PL5 ELR PLE SL7 NSQ SL1; Z.div_mod_to_equations; lia
               | |- Z.of_nat (length _) + _ <= _ => unfold dbud in DB0; rewrite (drest_app LB p A nA pbin Bb nB TB Lx NB LE), !length_app, !Nat2Z.inj_add in *; unfold ENTRY_CNT in *;
                                                     pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR PL5 PLE; lia) ltac:(clear; lia)) as DP; clear - DB0 EC DP ECR' LBN; lia
               | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - SPB Q2; lia
               | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact ST2
               | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - LO DSK Q2; lia
               | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
               | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact (CHBx _ _ Hin)
               | |- pf_ok _ _ _ _ => unfold ADE_R3; rewrite unsigned_lit by (clear; lia); apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left;
                                     unfold PF_entry; do 2 (apply in_or_app; right); apply in_or_app; left; exact He
               | |- as_Cm H _ <= as_AL H _ =>
                   pose proof ((RCI LEDGER_pay) s' um uf0 (ns * 6) 0 LED2 ltac:(clear - NSR'; lia) ltac:(clear; lia)
                                 ltac:(unfold ENTRY_CM, ENTRY_SIZE in *; clear - UMQ UMB ELR PL5 PLE SL7 NSQ SL1 EBR'; Z.div_mod_to_equations; lia) ltac:(unfold ENTRY_CF in *; clear - UFB ELR PL5 PLE EBR'; lia)) as PY;
                   pose proof (CF0 0 ltac:(clear; lia)) as CFz; clear - PY CFz; lia
               | |- ?G => idtac "CA_LEFT" G
               end. }
        clear CA. intros [msF3 mo3] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m3 & errv3 & SA & junk & pS & s3' & VIS3 & KREL3 & MP3 & MI3 & AC3 & ST3 & ERR3 & AUX3 & XP3 & SBR & HP3 & SC3 & ADS3 & MF3 & IM3 & GM3 & AL3).
        rewrite (unsigned_lit S1c) in ST3, XP3 by (clear - Q2 SPR CEIL LOS LO0; lia).
        pose proof SBR as (SAP & SA16 & _ & _ & SAT & _). replace (ns * 6) with (6 * ns) in SAT, HP3, SC3, ADS3, AL3 by (clear; lia).
        assert (LED3 : LEDGERc s3' (um + 6 * ns) uf0).
        { pose proof ((RCI LEDGER_step) s' s3' um uf0 (6 * ns) 0 LED2 ltac:(clear - NSR'; lia) ltac:(clear; lia)) as LS. rewrite Z.add_0_r in LS. apply LS.
          pose proof (CF0 0 ltac:(clear; lia)) as CFz. clear - AL3 CFz. lia. }
        assert (XP3' : xpres H (mid_errblocks M' ++ drestc Lx NB LE) S1c [] m2 m3).
        { pose proof (ECH_AC14_kit.axpres_drop_memflag H (mid_errblocks M' ++ drestc Lx NB LE) S1c [] [] m2 m3 MF2 MF3) as K. cbn [app] in K. rewrite app_nil_r in K. apply K. exact XP3. }
        assert (DW3 : adwkGc ((pS, SA, 6 * ns) :: Lx) NB S' M' LE (arp_sg1 (wz AR_INTERNAL_ERROR) (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) (wz (elen - 7 - publen)) (wz kl6) (wz kh5) (wz (bz bs (Z.to_nat (cur - Bb + (10 + publen))))) (wz AECH_VERSION) (wz ADE_FILE) (wz A) (wz bt) (wz (rem - 4)) (wz Bb) (wz elen) (wz cur))
                        (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) (um + 6 * ns) uf0 m3 s3').
        { eapply (adwkG_xc Lx ((pS, SA, 6 * ns) :: Lx)); [exact DW2| | | exact MI3| exact AC3| exact ST3| exact AUX3| exact ERR3| exact LED3].
          - eapply (xpres_weaken H); [exact XP3'| apply Z.le_refl| | intros a Ha; exact Ha].
            intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply SL0; exact Hb].
          - eapply PERM; [exact HP3|]. rewrite (drest_app LB p A nA pbin Bb nB TB ((pS, SA, 6 * ns) :: Lx) NB LE), (drest_app LB p A nA pbin Bb nB TB Lx NB LE). apply Permutation_middle. }
        assert (XPd : xpres H (drestc Lx NB LE) S1c [] m2 m3).
        { eapply (xpres_weaken H); [exact XP3'| apply Z.le_refl| intros b Hb; apply in_or_app; right; exact Hb| intros a Ha; exact Ha]. }
        assert (EO3 : ENTRYobj (drestc ((pS, SA, 6 * ns) :: Lx) NB LE) m3 ee En2).
        { eapply ENTRYobj_LB_mono; [eapply (ENTRYobj_frameX H); [exact EO2| exact XPd| intros b Hb; apply Forall_nil]|].
          intros b Hb. rewrite (drest_app LB p A nA pbin Bb nB TB ((pS, SA, 6 * ns) :: Lx) NB LE). right. rewrite <- (drest_app LB p A nA pbin Bb nB TB Lx NB LE). exact Hb. }
        assert (ESH3 : ENTRY_shad m3 ee En2).
        { eapply (ENTRY_shad_frameX H); [exact ESH2| exact EO2| exact XPd|]. intros b Hb. split; [apply SLX; eapply Permutation_in; [exact PE2| exact Hb]|]. split; apply Forall_nil. }
        assert (PE3 : Permutation ((pS, SA, 6 * ns) :: blocks_ENTRY ee En2) ((pS, SA, 6 * ns) :: Lx)) by (apply perm_skip; exact PE2).
        eapply (de_phase5 cur rem elen publen kh5 kl6 ph7 pl8 sl (bz bs (Z.to_nat (cur - Bb + (10 + publen)))) ns ((pS, SA, 6 * ns) :: Lx) NB S' M' LE x0 x1 x2 n0 n1 n2 (um + 6 * ns) uf0 um0 uf0 m3 s3' msF3 mo3 ee SA pS En2 junk);
          [exact DW3| exact EO3| exact ESH3| exact PE3| subst En2; exact SUO| subst En2; exact PNO| subst En2; exact ENO| subst En2; exact XE0| subst En2; exact XO| subst En2; exact LT0| subst En2; exact FRY0
          | subst En2; reflexivity| exact SC3| exact SAP| exact ADS3
          | rewrite lb_bytes_cons; cbn [blk_size snd]; clear - LB1 NSR'; lia| cbn [length]; clear - LBN; lia
          | exact BC| exact PLE| apply bz_range| clear - SLR NSQ NSP; Z.div_mod_to_equations; lia| exact SLEV| exact NSQ| clear - NSP NS0'; lia
          | exact SL7| exact ELR| exact CR| exact R5| exact R6| exact R7| exact R8| exact PEQ| exact DB0
          | clear - UMQ; lia| reflexivity| exact UMB| exact UFB| exact NENT| exact KADV| exact KTA| exact KTZ| exact KTX| exact VIS3| exact KREL3
          | exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 MP3))].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma de_phase3 : forall (cur rem elen : Z) (NB : list block) (S' : storerep) (M' : libmid) (LE : list block)
      (w24 w32 w40 w48 w56 w64 w72 : word) (x0 x1 x2 n0 n1 n2 p0 p1 p2 : word) (tpl um0 uf0 : Z)
      (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model) (ee : Z) (pe : bptr)
      (rax u0 u1 u2 a0w a1w a2w a3w a4w a7w s5w s6w s8w s10w u3 u4 u5 u6 : word),
    adwkGc [(pe, ee, ENTRY_SIZE)] NB S' M' LE (dsg1c w24 w32 w40 w48 w56 w64 w72 (wz (rem - 4)) (wz elen) (wz cur)) (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) 0 (b8 0) (poison_bytes 256 0)
           (um0 + ENTRY_SIZE) uf0 m' s' ->
    rw_cells asegs m' ee (entry_cells (AENT1 pe) (zeros 6) (zeros 4) (zeros 6) (zeros 4)) -> addressable m' ee ENTRY_SIZE ->
    Bb + 2 <= cur -> 0 <= elen -> 4 + elen <= rem -> cur + rem <= Bb + zlength bs ->
    dbudc (drestc [(pe, ee, ENTRY_SIZE)] NB LE) M' (ENTRY_BYTES rem - ENTRY_SIZE) (ENTRY_CNT rem - 1) ->
    um0 + errph_bytes (mid_err M') + ENTRY_CM rem <= DECODE_CUM_BYTES -> uf0 + errph_bytes (mid_err M') + ENTRY_CF rem <= DECODE_CUM_BYTES -> nent S' <= 65 ->
    KADVc cur rem NB S' um0 uf0 (mid_err M') -> KTAc NB S' -> KTZc NB S' -> KTXc NB S' ->
    as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) a0w a1w a2w a3w a4w (Z_to_bv 64 ASHB) (Z_to_bv 64 ee) a7w
                                (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 SH) (Z_to_bv 64 (rem - 4)) s5w s6w (Z_to_bv 64 ASHB) s8w (Z_to_bv 64 Bb) s10w (Z_to_bv 64 374) u3 u4 u5 u6)
                        F (Z_to_bv 64 ADE_J1) fc None m' (seg_rom asegs) ->
    as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
    as_SR H POSTc (mkCfg msF' mo').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH AUXV TIME.
    intros until u6. intros DW EC1 AD BC EL0 ELR CR DB UMB UFB NENT KADV KTA KTZ KTX VIS1 KREL1 MP1.
    pose proof KTA as KTA'. unfold dK_tailA in KTA'.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (AS1 & Q2 & Q1 & SPR & BP & BH & IB2 & NBL & NB15 & BLX & BEL & BRS & F1 & MF & IM & GM & ACCB & APB & ACB & LOS & LO0).
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (SHL : ASHB + AIMG_TOP / 8 <= SH) by (unfold ASHB, AIMG_TOP; rewrite Z.shiftr_div_pow2 by (clear; lia); clear - FQ1; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (SHU : SH + 512 < AHI_LO) by (rewrite SHF; unfold sh, AHI_LO; rewrite ASHADOW_BASE_val; clear - FQ2 ACB; lia).
    pose proof (dec_stack M M' STP) as DSK. pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    pose proof (ah_costs H HH) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd).
    assert (EINx : In (pe, ee, ENTRY_SIZE) [(pe, ee, ENTRY_SIZE)]) by (left; reflexivity).
    assert (EIN : In (pe, ee, ENTRY_SIZE) (mid_errblocks M' ++ drestc [(pe, ee, ENTRY_SIZE)] NB LE)).
    { apply in_or_app; right. rewrite (drest_app LB p A nA pbin Bb nB TB [(pe, ee, ENTRY_SIZE)] NB LE). left; reflexivity. }
    pose proof (BRS _ EIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
    pose proof (BLX _ EINx) as EBA. cbn [blk_addr blk_size fst snd] in EBA. pose proof (aapp_not_shadowland _ _ E7) as ENS.
    unfold ENTRY_SIZE in E5, E6, EBA, ENS. unfold AIMG_TOP in E4. unfold AFS_SIZE in E6.
    destruct DB as [DB1 DB2].
    assert (DB0 : dbudc (drestc [] NB LE) M' (ENTRY_BYTES rem) (ENTRY_CNT rem)).
    { unfold dbud in DB1, DB2 |- *. rewrite (drest_app LB p A nA pbin Bb nB TB [(pe, ee, ENTRY_SIZE)] NB LE) in DB1, DB2. rewrite lb_bytes_app in DB1. rewrite length_app, Nat2Z.inj_add in DB2.
      cbn [lb_bytes length fold_right app blk_size snd Z.of_nat Pos.of_succ_nat] in DB1, DB2. clear - DB1 DB2. unfold ENTRY_SIZE in *. lia. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1
      | eapply ade_seg3 with (q := S1c) (E := AENT1 pe) (blen := nB);
        [unfold dsg1 in FR1; exact FR1| unfold dsg2 in FR2; exact FR2| exact FR3| exact DSb1| clear - BC; lia| exact EL0| clear - CR ELR; lia| exact BP| exact BH| exact ACCB| exact NBL
        | exact EC1| reflexivity| exact E1| unfold ENTRY_SIZE; exact E5| unfold ENTRY_SIZE; clear - EBA NBL; lia
        | eapply (addressable_accessible _ _ _ _ _ AD); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia]
        | unfold ENTRY_SIZE; exact ENS| exact AS1| clear - Q2 SPR; lia| exact MI1]|].
    intros msF2 mo2 KREL2 MP2 (a0' & a1' & a2' & a3' & a4' & s4' & s5' & s6' & s8' & s9' & m2 & w24' & w32' & w40' & w56' & w64' & p0' & p1' & p2' & cf & MU2 & WM2 & MI2 & FR1' & FR3' & EC2 & CFR & CASES).
    (* [comment removed for export] *)
    assert (ST2 : stk asegs m2 lo S1c) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| cbn; clear - E5 CEIL; lia]).
    assert (T12 : forall A' cs, rw_cells asegs m' A' cs ->
              (A' + Z.of_nat (cells_size cs) <= S1c + 24 \/ S1c + 72 <= A') -> (A' + Z.of_nat (cells_size cs) <= S1c + 288 \/ S1c + 312 <= A') ->
              (A' + Z.of_nat (cells_size cs) <= ee \/ ee + 104 <= A') -> rw_cells asegs m2 A' cs).
    { intros A' cs RC HA HB HE. eapply rw_cells_transport; [exact RC| exact MU2| exact WM2|]. cbn. split; [clear - HA; lia|]. split; [clear - HB; lia|]. split; [clear - HE; lia| exact I]. }
    assert (DW2 : adwkGc [(pe, ee, ENTRY_SIZE)] NB S' M' LE (arp_sg1 (wz AR_INTERNAL_ERROR) w24' w32' w40' w48 w56' w64' w72 (wz AECH_VERSION) (wz ADE_FILE) (wz A) (wz bt) (wz (rem - 4)) (wz Bb) (wz elen) (wz cur))
                    (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 p0' p1' p2') 0 (b8 0) (poison_bytes 256 0) (um0 + ENTRY_SIZE) uf0 m2 s').
    { eapply (adwkG_wc [(pe, ee, ENTRY_SIZE)] NB S' M' LE _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) (um0 + ENTRY_SIZE) uf0 m' s' m2 [(S1c + 24, S1c + 72); (S1c + 288, S1c + 312); (ee + 49, ee + 50)]);
        [exact DW| exact MU2| exact WM2| exact MI2| exact ST2| | exact FR1'| reflexivity| | exact FR3'| reflexivity| | | reflexivity].
      - apply Forall_cons; [right; left; cbn; clear; lia|]. apply Forall_cons; [right; right; left; cbn; clear; lia|].
        apply Forall_cons; [| apply Forall_nil]. do 6 right. exists (pe, ee, ENTRY_SIZE). split; [exact EINx| cbn; unfold ENTRY_SIZE; clear; lia].
      - apply T12; [unfold dsg2 in FR2; exact FR2| right; cbn; clear; lia| left; cbn; clear; lia| right; cbn; clear - E5 AS1; lia].
      - apply T12; [exact FF1| | |]; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; [left; clear - FQ2 AS1; lia| left; clear - FQ2 AS1; lia| clear - E6 FQ5 FQ6; lia].
      - apply T12; [exact FSH1| | |]; unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?LSH1;
          [left; rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - FQ2 ACB AS1; lia
          | left; rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - FQ2 ACB AS1; lia
          | pose proof (sh_in_shadowland ff ltac:(unfold AAPP_HI; clear - FQ1 FQ2 ACB; lia)) as SIS; rewrite <- SHF in SIS; clear - SIS SHU ENS; lia]. }
    assert (AD2 : addressable m2 ee ENTRY_SIZE).
    { eapply addressable_transport; [exact AD| exact MU2| exact WM2|]. cbn. pose proof (sh_in_shadowland ee ltac:(unfold AAPP_HI; clear - E1 E5 ACB; lia)) as SIS.
      assert (ETOP : ee + ENTRY_SIZE <= AAPP_HI) by (unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia).
      pose proof (sh_nsh_high ee ENTRY_SIZE ltac:(clear - E1; lia) ltac:(unfold ENTRY_SIZE; clear; lia) ETOP) as SNH.
      pose proof (sh_aapp_range ee ENTRY_SIZE E7 ltac:(unfold ENTRY_SIZE; clear; lia)) as (W1 & W2 & W3).
      assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia). unfold ALOWSH_LO, AHI_LO in SIS, SNH, ENS, W3.
      split; [clear - AS1 W2 SHC; lia|]. split; [clear - AS1 W2 SHC; lia|]. split; [clear - ENS SIS SNH; lia| exact I]. }
    clear MU2 WM2 T12.
    assert (ESH2 : ENTRY_shad m2 ee (upd_cfgid (AENT1 pe) cf)).
    { unfold ENTRY_shad, AENT1, upd_cfgid. cbn [en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o oshad EXTS_shad].
      split; [unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia|]. split; [exact AD2|]. repeat split; exact I. }
    assert (EO2 : ENTRYobj (drestc [(pe, ee, ENTRY_SIZE)] NB LE) m2 ee (upd_cfgid (AENT1 pe) cf)).
    { unfold ENTRYobj, AENT1, upd_cfgid. cbn [en_id en_version en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o ofield EXTS].
      split; [exists (zeros 6), (zeros 4), (zeros 6), (zeros 4); split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact EC2]|].
      split; [rewrite (drest_app LB p A nA pbin Bb nB TB [(pe, ee, ENTRY_SIZE)] NB LE); left; reflexivity|]. repeat split; reflexivity. }
    assert (PE2 : Permutation (blocks_ENTRY ee (upd_cfgid (AENT1 pe) cf)) [(pe, ee, ENTRY_SIZE)]) by (unfold AENT1, upd_cfgid; cbn; apply Permutation_refl).
    destruct CASES as [VIS2|(publen & PEQ & PL5 & CF & -> & -> & -> & -> & -> & -> & -> & -> & VIS2)].
    2: pose proof (bz_range bs (Z.to_nat (cur - Bb + 7))) as R7q; pose proof (bz_range bs (Z.to_nat (cur - Bb + 8))) as R8q;
       assert (PLE : 0 <= publen) by (clear - PEQ R7q R8q; lia); assert (PLH : publen < 2^16) by (clear - PEQ R7q R8q; lia).
    - (* [comment removed for export] *)
      eapply (KTA' [(pe, ee, ENTRY_SIZE)] M' LE w24' w32' w40' w48 w56' w64' w72 (wz (rem - 4)) (wz elen) (wz cur) x0 x1 x2 n0 n1 n2 p0' p1' p2' 0 (um0 + ENTRY_SIZE) uf0 (b8 0) (poison_bytes 256 0) m2 s' msF2 mo2 ee 400);
        [exact DW2| exact EO2| exact ESH2| exact PE2| clear; lia| | | | exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)].
      + unfold dbud in *. unfold ENTRY_BYTES, ENTRY_CNT, ENTRY_SIZE, ERRDEBUG_BYTES in *.
        pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR EL0; lia) ltac:(clear; lia)) as DP. clear - DB1 DB2 DP ELR EL0. lia.
      + unfold ENTRY_CM, ENTRY_SIZE, ERRDEBUG_BYTES in *. clear - UMB ELR EL0. lia.
      + cbn [lb_bytes fold_right blk_size snd]. unfold ENTRY_CF, ENTRY_SIZE, ERRDEBUG_BYTES in *. clear - UFB ELR EL0. lia.
    - (* [comment removed for export] *)
      idtac "P3_MEMDUP".
      pose proof DW2 as (HP2 & LM2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSb2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RFS2 & [errv2 ERR2] & AUX2 & _ & AC2 & _ & STK2 & CHN2 & _ & LED2).
      destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MF2 & IM2 & GM2 & ACCB2 & _).
      pose proof CR as CRq. pose proof NBL as NBLq. unfold zlength in CRq, NBLq.
      destruct (abytes_at_sub m2 Bb bs (cur + 9 - Bb) publen DSb2 ltac:(clear - BC; lia) PLE ltac:(clear - BC CRq PL5 ELR; lia)) as [BSX XBL].
      replace (Bb + (cur + 9 - Bb)) with (cur + 9) in BSX by (clear; lia).
      set (xb := firstn (Z.to_nat publen) (skipn (Z.to_nat (cur + 9 - Bb)) bs)) in *.
      assert (XBLz : zlength xb = publen) by (unfold zlength; exact XBL).
      destruct (entry_split_pub _ _ _ _ _ _ _ EC2) as (EP1 & EL1 & ED1 & ES1). cbn [en_publen en_pub upd_cfgid AENT1] in EL1, ED1.
      pose proof (asg3_split3 _ _ _ _ _ _ _ _ _ _ _ FR3') as QQ3. destruct QQ3 as [QX3 QQ4]. destruct QQ4 as [QN3 QP3].
      assert (CHBx : forall fp' ra', In (fp', ra') CH1c -> S1c + 16 <= fp').
      { intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
      pose proof (apkmemdup_spec H HH) as PM. unfold pkmemdup_stmt in PM.
      eapply (ah_seq H HH).
      { eapply PM with (lo := lo) (B := B) (LB := mid_errblocks M' ++ drestc [(pe, ee, ENTRY_SIZE)] NB LE) (LF := LF1c ff fp) (s := s') (pkt := S1c + 288) (cur := cur + 9) (ms := Bb)
                       (dptr := ee + 24) (lptr := ee + 16) (oldlen := 0) (v := 1) (bs := xb) (bC := (pbin, Bb, nB)) (errv := errv2) (CH := CH1c); clear PM; rewrite ?XBLz.
        all: try first [exact VIS2| exact HP2| exact KREL2| exact AUX2| exact MI2| exact CEIL| exact AC2| exact CHN2| exact ERR2| exact RFS2| exact MF2| exact IM2| exact GM2| exact BSX| exact EL1| exact ED1| exact IB2].
        all: lazymatch goal with
             | |- _ = Z_to_bv _ _ => reflexivity
             | |- Z_to_bv 64 ATP = _ => reflexivity
             | |- rw_cells _ _ (S1c + 288) _ => unfold pk_cells; replace (S1c + 288) with (S1c + 240 + 48) by (clear; lia); exact QP3
             | |- ashobj _ _ _ (S1c + 288) _ => right; right; rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear; lia
             | |- ashobj _ _ _ _ _ => left; exists (pe, ee, ENTRY_SIZE); split; [exact EIN| cbn; unfold ENTRY_SIZE; clear; lia]
             | |- S1c + 288 + 24 <= B => clear - Q2 SPB; lia
             | |- cells_apart _ _ => unfold cells_apart, apart; clear; lia
             | |- apart _ 24 _ 8 => unfold apart; clear - E5 AS1; lia
             | |- apart _ _ _ 24 => unfold apart; clear - BH CR ELR PL5 AS1 NBL; lia
             | |- apart _ _ _ 8 => unfold apart; clear - EBA BC CR ELR PL5 NBL; lia
             | |- blk_addr _ <= _ => cbn; clear - BC; lia
             | |- _ + 9 + _ <= blk_addr _ + blk_size _ => cbn; clear - CR ELR PL5 NBL; lia
             | |- _ <= 2 ^ 28 => clear - PL5 ELR CR NBL NB15 BC; lia
             | |- (S1c + 288) mod 8 = 0 => clear - Q1; Z.div_mod_to_equations; lia
             | |- (_ + _) mod 8 = 0 => clear - E2; Z.div_mod_to_equations; lia
             | |- afs_write_ok _ _ _ => left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP, AFS_SIZE in *; clear - E4 E6; lia
             | |- accessible _ (S1c + 288) _ => eapply stack0_accessible; [exact STK2| clear - LOS; lia| clear; lia| clear - Q2; lia]
             | |- accessible _ _ 8 => eapply (addressable_accessible _ _ _ _ _ AD2); [clear; lia| unfold ENTRY_SIZE; clear; lia| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia]
             | |- accessible _ (_ + 9) _ => eapply accessible_sub; [exact ACCB2| clear - BC; lia| clear - CR ELR PL5 NBL; lia| exact PLE]
             | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_app; unfold dbud, ENTRY_BYTES, ENTRY_SIZE in *; clear - DB1 EB EBR' PL5 ELR EL0 PLE; lia
             | |- Z.of_nat (length _) + _ <= _ => rewrite length_app, Nat2Z.inj_add; unfold dbud, ENTRY_CNT in *;
                                                   pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - ELR EL0; lia) ltac:(clear; lia)) as DP; clear - DB2 EC DP ECR'; lia
             | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - SPB Q2; lia
             | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact ST2
             | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - LO DSK Q2; lia
             | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
             | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact (CHBx _ _ Hin)
             | |- offchain _ _ _ => intros fp' ra' Hin; left; pose proof (CHBx _ _ Hin) as CB'; clear - CB' E5 AS1; lia
             | |- pf_ok _ _ _ _ => unfold ADE_R2; rewrite unsigned_lit by (clear; lia); apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left;
                                   unfold PF_entry; apply in_or_app; right; apply in_or_app; left; exact He
             | |- as_Cf H 0 + as_Cm H _ <= as_AL H _ =>
                 pose proof ((RCI LEDGER_pay) s' (um0 + ENTRY_SIZE) uf0 publen 0 LED2 PLE ltac:(clear; lia)
                               ltac:(unfold ENTRY_CM, ENTRY_SIZE in *; clear - UMB ELR EL0 PL5 EBR'; lia) ltac:(unfold ENTRY_CF in *; clear - UFB ELR EL0 EBR'; lia)) as PY;
                 clear - PY; lia
             | |- ?G => idtac "PM_LEFT" G
             end. }
      clear PM. intros [msF3 mo3] PO. unfold pkmemdup_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m3 & errv3 & s3' & LB3 & D &
                      VIS3 & KREL3 & MP3 & MI3 & AC3 & ST3 & ERR3 & AUX3 & HP3 & RFS3 & PK3 & DP3 & LP3 & PCASE & XP3 & [v' [MF3 VV]] & IM3 & GM3).
      rewrite (unsigned_lit S1c) in ST3, XP3 by (clear - Q2 SPR CEIL LOS LO0; lia).
      rewrite XBLz in PK3, LP3, PCASE.
      replace (if publen =? 0 then 0 else publen) with publen in LP3 by (destruct (Z.eqb_spec publen 0); lia).
      assert (V1 : v' = 1) by (destruct MF3 as (fb & _ & _ & VR); clear - VR VV; lia). subst v'.
      (* [comment removed for export] *)
      assert (XP3' : xpres H (mid_errblocks M' ++ drestc [(pe, ee, ENTRY_SIZE)] NB LE) S1c [(S1c + 288, S1c + 288 + 24); (ee + 24, ee + 24 + 8); (ee + 16, ee + 16 + 8)] m2 m3).
      { pose proof (ECH_AC14_kit.axpres_drop_memflag H (mid_errblocks M' ++ drestc [(pe, ee, ENTRY_SIZE)] NB LE) S1c [(S1c + 288, S1c + 288 + 24); (ee + 24, ee + 24 + 8); (ee + 16, ee + 16 + 8)] [] m2 m3 MF2 MF3) as K.
        rewrite app_nil_r in K. apply K. exact XP3. }
      assert (FXW : Forall (fun iv : Z * Z => (S1c + 16 <= fst iv /\ snd iv <= S1c + 144) \/ (S1c + 240 <= fst iv /\ snd iv <= S1c + 312)
                                             \/ (exists b, In b [(pe, ee, ENTRY_SIZE)] /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b))
                           [(S1c + 288, S1c + 288 + 24); (ee + 24, ee + 24 + 8); (ee + 16, ee + 16 + 8)]).
      { apply Forall_cons; [right; left; cbn; clear; lia|].
        apply Forall_cons; [right; right; exists (pe, ee, ENTRY_SIZE); split; [exact EINx| cbn; unfold ENTRY_SIZE; clear; lia]|].
        apply Forall_cons; [right; right; exists (pe, ee, ENTRY_SIZE); split; [exact EINx| cbn; unfold ENTRY_SIZE; clear; lia]| apply Forall_nil]. }
      (* [comment removed for export] *)
      assert (TE : forall A' cs, rw_cells asegs m2 A' cs -> ee <= A' -> A' + Z.of_nat (cells_size cs) <= ee + 104 ->
                 (A' + Z.of_nat (cells_size cs) <= ee + 16 \/ ee + 32 <= A') -> rw_cells asegs m3 A' cs).
      { intros A' cs RC H1 H2 H3. eapply (xpres_rw_cells' H); [exact XP3'| exact RC| right; right; left; exists (pe, ee, ENTRY_SIZE); split; [exact EIN| cbn; unfold ENTRY_SIZE; clear - H1 H2; lia]|].
        apply Forall_cons; [cbn; clear - H2 E5 AS1; lia|]. apply Forall_cons; [cbn; clear - H3; lia|]. apply Forall_cons; [cbn; clear - H3; lia| apply Forall_nil]. }
      assert (TS : forall A' cs, rw_cells asegs m2 A' cs -> S1c <= A' -> (A' + Z.of_nat (cells_size cs) <= S1c + 288 \/ S1c + 312 <= A') -> rw_cells asegs m3 A' cs).
      { intros A' cs RC H1 H2. eapply (xpres_rw_cells' H); [exact XP3'| exact RC| left; exact H1|].
        apply Forall_cons; [cbn; clear - H2; lia|]. apply Forall_cons; [cbn; clear - H1 E5 AS1; lia|]. apply Forall_cons; [cbn; clear - H1 E5 AS1; lia| apply Forall_nil]. }
      pose proof (TE _ _ EP1 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; left; clear; lia)) as EP3.
      pose proof (TE _ _ ES1 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; right; clear; lia)) as ES3.
      pose proof (TS _ _ QX3 ltac:(clear; lia) ltac:(cbn; left; clear; lia)) as QX4. pose proof (TS _ _ QN3 ltac:(clear; lia) ltac:(cbn; left; clear; lia)) as QN4.
      pose proof (TS _ _ FR1' ltac:(clear; lia) ltac:(unfold arp_sg1; cbn; left; clear; lia)) as FR1''.
      unfold pk_cells in PK3. pose proof (asg3_join3 _ _ _ _ _ _ _ _ _ _ _ QX4 QN4 ltac:(replace (S1c + 240 + 48) with (S1c + 288) by (clear; lia); exact PK3)) as FR3''.
      clear TE TS.
      (* [comment removed for export] *)
      assert (LED3 : LEDGERc s3' (um0 + ENTRY_SIZE + publen) uf0).
      { pose proof ((RCI LEDGER_step) s' s3' (um0 + ENTRY_SIZE) uf0 publen 0 LED2 PLE ltac:(clear; lia)) as LS. rewrite Z.add_0_r in LS. apply LS.
        pose proof (CF0 0 ltac:(clear; lia)) as CFz. pose proof (CM0 publen PLE) as CMp.
        destruct PCASE as [(_ & _ & _ & AL3)|(_ & pD & _ & _ & _ & _ & AL3)]; clear - AL3 CFz CMp; lia. }
      idtac "P3_FIN".
      (* [comment removed for export] *)
      assert (FIN : forall Lx o, as_RHEAP H s3' (mid_errblocks M' ++ drestc Lx NB LE) m3 ->
                 Permutation ((pe, ee, ENTRY_SIZE) :: blocks_of D o) Lx -> ofield (drestc Lx NB LE) D o -> oshad m3 D o ->
                 lb_bytes Lx <= ENTRY_SIZE + publen -> Z.of_nat (length Lx) <= 2 ->
                 as_SR H POSTc (mkCfg msF3 mo3)).
      { intros Lx o HP3' PBL OFD OSH LB1 LBN.
        assert (DW3 : adwkGc Lx NB S' M' LE (arp_sg1 (wz AR_INTERNAL_ERROR) (wz (ee + 24)) (wz (ee + 16)) (wz (cur + 4)) w48 (wz (bz bs (Z.to_nat (cur - Bb + 6)))) (wz (bz bs (Z.to_nat (cur - Bb + 5)))) w72 (wz AECH_VERSION) (wz ADE_FILE) (wz A) (wz bt) (wz (rem - 4)) (wz Bb) (wz elen) (wz cur))
                        (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 (wz (cur + 9)) (wz Bb) (wz publen)) 0 (b8 0) (poison_bytes 256 0) (um0 + ENTRY_SIZE + publen) uf0 m3 s3').
        { eapply (adwkG_xw [(pe, ee, ENTRY_SIZE)] Lx NB S' M' LE _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) (um0 + ENTRY_SIZE) uf0 (um0 + ENTRY_SIZE + publen) uf0 m2 s' m3 s3' _ _ _ errv3);
            [exact DW2| exact XP3'| exact FXW| exact HP3'| exact MI3| exact AC3| exact ST3| exact AUX3| exact ERR3| exact RFS3| exact LED3| exact FR1''| reflexivity| exact FR3''| reflexivity]. }
        assert (ADE3 : addressable m3 ee ENTRY_SIZE).
        { eapply (addressable_xpres_blkX H); [exact EIN| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia| exact AD2| exact XP3'|].
          pose proof (sh_in_shadowland ee ltac:(unfold AAPP_HI; clear - E1 E5 ACB; lia)) as SIS.
          pose proof (sh_nsh_high ee ENTRY_SIZE ltac:(clear - E1; lia) ltac:(unfold ENTRY_SIZE; clear; lia) ltac:(unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia)) as SNH.
          pose proof (sh_aapp_range ee ENTRY_SIZE E7 ltac:(unfold ENTRY_SIZE; clear; lia)) as (W1 & W2 & W3).
          assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
          pose proof ENS as ENS'. unfold ALOWSH_LO, AHI_LO in SIS, SNH, W3, ENS'.
          apply Forall_cons; [cbn; clear - AS1 W2 SHC; lia|]. apply Forall_cons; [cbn; clear - ENS' SIS SNH; lia|]. apply Forall_cons; [cbn; clear - ENS' SIS SNH; lia| apply Forall_nil]. }
        set (En3 := upd_pub (upd_cfgid (AENT1 pe) cf) publen D o).
        assert (ESH3 : ENTRY_shad m3 ee En3).
        { subst En3. unfold ENTRY_shad, AENT1, upd_cfgid, upd_pub. cbn [en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o EXTS_shad].
          split; [unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia|]. split; [exact ADE3|]. split; [exact I|]. split; [exact OSH|]. repeat split; exact I. }
        assert (EO3 : ENTRYobj (drestc Lx NB LE) m3 ee En3).
        { subst En3. unfold ENTRYobj, AENT1, upd_cfgid, upd_pub. cbn [en_id en_version en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o EXTS].
          split; [exists (zeros 6), (zeros 4), (zeros 6), (zeros 4); split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact (entry_join_pub _ _ _ _ _ _ _ _ _ o EP3 LP3 DP3 ES3)]|].
          split; [apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (drest_subc Lx NB LE))))))))); eapply Permutation_in; [exact PBL| left; reflexivity]|].
          split; [reflexivity|]. split; [exact OFD|]. split; [reflexivity|]. split; reflexivity. }
        assert (PE3 : Permutation (blocks_ENTRY ee En3) Lx).
        { subst En3. cbn [blocks_ENTRY en_id en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o upd_pub upd_cfgid AENT1 blocks_EXTS app].
          destruct o as [[? ?]|]; cbn [blocks_of app] in PBL |- *; exact PBL. }
        pose proof (bz_range bs (Z.to_nat (cur - Bb + 5))) as R5. pose proof (bz_range bs (Z.to_nat (cur - Bb + 6))) as R6.
        pose proof (bz_range bs (Z.to_nat (cur - Bb + 7))) as R7. pose proof (bz_range bs (Z.to_nat (cur - Bb + 8))) as R8.
        eapply (de_phase4 cur rem elen publen (bz bs (Z.to_nat (cur - Bb + 5))) (bz bs (Z.to_nat (cur - Bb + 6))) (bz bs (Z.to_nat (cur - Bb + 7))) (bz bs (Z.to_nat (cur - Bb + 8)))
                  Lx NB S' M' LE w48 w72 x0 x1 x2 n0 n1 n2 (um0 + ENTRY_SIZE + publen) uf0 um0 uf0 m3 s3' msF3 mo3 ee En3);
          [exact DW3| exact EO3| exact ESH3| exact PE3| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
          | exact LB1| exact LBN| exact BC| exact PLE| exact PL5| exact ELR| exact CR| exact R5| exact R6| exact R7| exact R8| exact PEQ| exact DB0
          | apply Z.le_refl| reflexivity| exact UMB| exact UFB| exact NENT| exact KADV| exact KTA| exact KTZ| exact KTX| exact VIS3| exact KREL3
          | exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 MP3))]. }
      destruct PCASE as [(P0 & D0 & -> & _)|(P1 & pD & DBR & -> & DC3 & ADD3 & _)].
      + (* [comment removed for export] *)
        apply (FIN [(pe, ee, ENTRY_SIZE)] None); [exact HP3| apply Permutation_refl| exact D0| exact I| cbn [lb_bytes fold_right blk_size snd]; unfold ENTRY_SIZE; clear - PLE; lia| cbn; clear; lia].
      + (* [comment removed for export] *)
        pose proof DBR as (DPOS & _ & _ & _ & DTOP & _).
        apply (FIN [(pD, D, publen); (pe, ee, ENTRY_SIZE)] (Some (pD, publen))).
        * eapply PERM; [exact HP3|]. apply Permutation_middle.
        * apply perm_swap.
        * cbn [ofield]. split; [exact DPOS|]. split; [exact PLE|]. rewrite (drest_app LB p A nA pbin Bb nB TB [(pD, D, publen); (pe, ee, ENTRY_SIZE)] NB LE). left; reflexivity.
        * cbn [oshad]. split; [unfold AAPP_HI; clear - DTOP ACB; lia|]. split; [exact ADD3|]. exists xb. rewrite <- XBL, Nat2Z.id. exact DC3.
        * cbn [lb_bytes fold_right blk_size snd]. unfold ENTRY_SIZE. clear - PLE. lia.
        * cbn; clear; lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma de_phase2 : forall (cur rem : Z) (NB : list block) (S' : storerep) (M' : libmid) (LE : list block)
      (w24 w32 w40 w48 w56 w64 w72 w112 w128 w136 wee : word) (x0 x1 x2 n0 n1 n2 p0 p1 p2 : word) (tpl um uf um0 uf0 : Z)
      (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model) (ee : Z) (pe : bptr)
      (rax u0 u1 u2 a1w a2w a3w a4w a5w a6w a7w s5w s6w s8w s10w u3 u4 u5 u6 : word),
    adwkGc [(pe, ee, ENTRY_SIZE)] NB S' M' LE (dsg1c w24 w32 w40 w48 w56 w64 w72 w112 w128 w136) wee (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) 0 (b8 0) (poison_bytes 256 0) um uf m' s' ->
    rw_cells asegs m' ee (entry_cells (AENT0 pe) (zeros 6) (zeros 4) (zeros 6) (zeros 4)) -> addressable m' ee ENTRY_SIZE ->
    Bb + 2 <= cur -> 1 <= rem -> cur + rem <= Bb + zlength bs ->
    dbudc (drestc [(pe, ee, ENTRY_SIZE)] NB LE) M' (ENTRY_BYTES rem - ENTRY_SIZE) (ENTRY_CNT rem - 1) ->
    um = um0 + ENTRY_SIZE -> uf = uf0 ->
    um0 + errph_bytes (mid_err M') + ENTRY_CM rem <= DECODE_CUM_BYTES -> uf0 + errph_bytes (mid_err M') + ENTRY_CF rem <= DECODE_CUM_BYTES -> nent S' <= 65 ->
    KADVc cur rem NB S' um0 uf0 (mid_err M') -> KSKc cur rem NB S' um0 uf0 (mid_err M') -> KTAc NB S' -> KTZc NB S' -> KTXc NB S' ->
    as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 ee) a1w a2w a3w a4w a5w a6w a7w
                                (Z_to_bv 64 cur) (Z_to_bv 64 SH) (Z_to_bv 64 rem) s5w s6w (Z_to_bv 64 ASHB) s8w (Z_to_bv 64 Bb) s10w (Z_to_bv 64 (SH + 8)) u3 u4 u5 u6)
                        F (ret_pc (Z_to_bv 64 ADE_R1)) fc None m' (seg_rom asegs) ->
    as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
    as_SR H POSTc (mkCfg msF' mo').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH AUXV TIME.
    intros until u6. intros DW EC0 AD BC R1 CR DB UM UF UMB UFB NENT KADV KSK KTA KTZ KTX VIS1 KREL1 MP1.
    pose proof KSK as KSK'. unfold dK_skip in KSK'. pose proof KTA as KTA'. unfold dK_tailA in KTA'.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (AS1 & Q2 & Q1 & SPR & BP & BH & IB2 & NBL & NB15 & BLX & BEL & BRS & F1 & MF & IM & GM & ACCB & APB & ACB & LOS & LO0).
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (SHL : ASHB + AIMG_TOP / 8 <= SH) by (unfold ASHB, AIMG_TOP; rewrite Z.shiftr_div_pow2 by (clear; lia); clear - FQ1; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (SHU : SH + 512 < AHI_LO) by (rewrite SHF; unfold sh, AHI_LO; rewrite ASHADOW_BASE_val; clear - FQ2 ACB; lia).
    pose proof (dec_stack M M' STP) as DSK. pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    pose proof (ah_costs H HH) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd).
    assert (EINx : In (pe, ee, ENTRY_SIZE) [(pe, ee, ENTRY_SIZE)]) by (left; reflexivity).
    assert (EIN : In (pe, ee, ENTRY_SIZE) (mid_errblocks M' ++ drestc [(pe, ee, ENTRY_SIZE)] NB LE)).
    { apply in_or_app; right. rewrite (drest_app LB p A nA pbin Bb nB TB [(pe, ee, ENTRY_SIZE)] NB LE). left; reflexivity. }
    pose proof (BRS _ EIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
    pose proof (BLX _ EINx) as EBA. cbn [blk_addr blk_size fst snd] in EBA. pose proof (aapp_not_shadowland _ _ E7) as ENS.
    unfold ENTRY_SIZE in E5, E6, EBA, ENS. unfold AIMG_TOP in E4. unfold AFS_SIZE in E6.
    destruct DB as [DB1 DB2]. subst um uf.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1
      | eapply ade_seg2 with (q := S1c) (E := AENT0 pe) (blen := nB);
        [unfold dsg1 in FR1; exact FR1| unfold dsg2 in FR2; exact FR2| exact DSb1| clear - BC; lia| exact R1| exact CR| exact BP| exact BH| exact ACCB| exact NBL
        | exact EC0| exact E1| unfold ENTRY_SIZE; exact E5| unfold ENTRY_SIZE; clear - EBA NBL; lia
        | eapply (addressable_accessible _ _ _ _ _ AD); [apply Z.le_refl| apply Z.le_refl| unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia]
        | unfold ENTRY_SIZE; exact ENS| exact AS1| clear - Q2 SPR; lia| exact MI1]|].
    intros msF2 mo2 KREL2 MP2 (a0' & a1' & a2' & a3' & a4' & a5' & a6' & m2 & w112' & w128' & w136' & v & MU2 & WM2 & MI2 & FR1' & FR2' & EC2 & VR & CASES).
    (* [comment removed for export] *)
    assert (ST2 : stk asegs m2 lo S1c) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| cbn; clear - E5 CEIL; lia]).
    assert (T12 : forall A' cs, rw_cells asegs m' A' cs ->
              (A' + Z.of_nat (cells_size cs) <= S1c + 112 \/ S1c + 152 <= A') -> (A' + Z.of_nat (cells_size cs) <= ee \/ ee + 2 <= A') -> rw_cells asegs m2 A' cs).
    { intros A' cs RC HA HB. eapply rw_cells_transport; [exact RC| exact MU2| exact WM2|]. cbn. split; [clear - HA; lia|]. split; [clear - HB; lia| exact I]. }
    assert (DW2 : adwkGc [(pe, ee, ENTRY_SIZE)] NB S' M' LE (arp_sg1 (wz AR_INTERNAL_ERROR) w24 w32 w40 w48 w56 w64 w72 (wz AECH_VERSION) (wz ADE_FILE) (wz A) (wz bt) w112' (wz Bb) w128' w136')
                    (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) 0 (b8 0) (poison_bytes 256 0) (um0 + ENTRY_SIZE) uf0 m2 s').
    { eapply (adwkG_wc [(pe, ee, ENTRY_SIZE)] NB S' M' LE _ wee _ 0 (b8 0) (poison_bytes 256 0) (um0 + ENTRY_SIZE) uf0 m' s' m2 [(S1c + 112, S1c + 152); (ee, ee + 2)]);
        [exact DW| exact MU2| exact WM2| exact MI2| exact ST2| | exact FR1'| reflexivity| unfold dsg2; exact FR2'| | exact SZ3| | | reflexivity].
      - apply Forall_cons; [right; left; cbn; clear; lia|]. apply Forall_cons; [| apply Forall_nil]. do 6 right. exists (pe, ee, ENTRY_SIZE). split; [exact EINx| cbn; unfold ENTRY_SIZE; clear; lia].
      - apply T12; [exact FR3| right; cbn; clear; lia| right; cbn; clear - E5 AS1; lia].
      - apply T12; [exact FF1| | ]; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; [left; clear - FQ2 AS1; lia| clear - E6 FQ5 FQ6; lia].
      - apply T12; [exact FSH1| | ]; unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?LSH1;
          [left; rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - FQ2 ACB AS1; lia
          | pose proof (sh_in_shadowland ff ltac:(unfold AAPP_HI; clear - FQ1 FQ2 ACB; lia)) as SIS; rewrite <- SHF in SIS; clear - SIS SHU ENS; lia]. }
    assert (AD2 : addressable m2 ee ENTRY_SIZE).
    { eapply addressable_transport; [exact AD| exact MU2| exact WM2|]. cbn. pose proof (sh_in_shadowland ee ltac:(unfold AAPP_HI; clear - E1 E5 ACB; lia)) as SIS.
      assert (ETOP : ee + ENTRY_SIZE <= AAPP_HI) by (unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia).
      pose proof (sh_nsh_high ee ENTRY_SIZE ltac:(clear - E1; lia) ltac:(unfold ENTRY_SIZE; clear; lia) ETOP) as SNH.
      pose proof (sh_aapp_range ee ENTRY_SIZE E7 ltac:(unfold ENTRY_SIZE; clear; lia)) as (W1 & W2 & W3).
      assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia). unfold ALOWSH_LO, AHI_LO in SIS, SNH, ENS, W3.
      split; [clear - AS1 W2 SHC; lia|]. split; [clear - ENS SIS SNH; lia| exact I]. }
    clear MU2 WM2 T12 FR1' FR2'.
    assert (ESH2 : ENTRY_shad m2 ee (upd_version (AENT0 pe) v)).
    { unfold ENTRY_shad, AENT0, upd_version. cbn [en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o oshad EXTS_shad].
      split; [unfold AAPP_HI, ENTRY_SIZE; clear - E5 ACB; lia|]. split; [exact AD2|]. repeat split; exact I. }
    assert (EO2 : ENTRYobj (drestc [(pe, ee, ENTRY_SIZE)] NB LE) m2 ee (upd_version (AENT0 pe) v)).
    { unfold ENTRYobj, AENT0, upd_version. cbn [en_id en_version en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o en_exts en_exts_o ofield EXTS].
      split; [exists (zeros 6), (zeros 4), (zeros 6), (zeros 4); split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact EC2]|].
      split; [rewrite (drest_app LB p A nA pbin Bb nB TB [(pe, ee, ENTRY_SIZE)] NB LE); left; reflexivity|]. repeat split; reflexivity. }
    assert (PE2 : Permutation (blocks_ENTRY ee (upd_version (AENT0 pe) v)) [(pe, ee, ENTRY_SIZE)]) by (unfold AENT0, upd_version; cbn; apply Permutation_refl).
    destruct CASES as [(line & s2' & s4' & LN & VIS2)|(elen & EL0 & ELR & -> & -> & -> & VB & REST)].
    - (* [comment removed for export] *)
      eapply (KTA' [(pe, ee, ENTRY_SIZE)] M' LE w24 w32 w40 w48 w56 w64 w72 w112' w128' w136' x0 x1 x2 n0 n1 n2 p0 p1 p2 0 (um0 + ENTRY_SIZE) uf0 (b8 0) (poison_bytes 256 0) m2 s' msF2 mo2 ee line);
        [exact DW2| exact EO2| exact ESH2| exact PE2| clear - LN; lia| | | | exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)].
      + unfold dbud in *. unfold ENTRY_BYTES, ENTRY_CNT, ENTRY_SIZE, ERRDEBUG_BYTES in *.
        pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - R1; lia) ltac:(clear; lia)) as DP. clear - DB1 DB2 DP R1. lia.
      + unfold ENTRY_CM, ENTRY_SIZE, ERRDEBUG_BYTES in *. clear - UMB R1. lia.
      + cbn [lb_bytes fold_right blk_size snd]. unfold ENTRY_CF, ENTRY_SIZE, ERRDEBUG_BYTES in *. clear - UFB R1. lia.
    - destruct REST as [[NV VIS2]|[EV VIS2]].
      + (* [comment removed for export] *)
        eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply ade_skip1; [clear - E1 E5 ACB; lia| exact MI2]|].
        intros msF3 mo3 KREL3 MP3 VIS3. cbn beta in VIS3.
        eapply (ade_efree [(pe, ee, ENTRY_SIZE)] NB S' M' LE _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) (um0 + ENTRY_SIZE) uf0 m2 s' msF3 mo3 ee (Some (upd_version (AENT0 pe) v)) ADE_SK_R1);
          [exact DW2| exact (conj EO2 (conj ESH2 PE2))| unfold ADE_SK_R1; clear; lia| reflexivity
          | apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left; unfold PF_entry; do 3 (apply in_or_app; right); apply in_or_app; left; exact He
          | cbn [lb_bytes fold_right blk_size snd]; unfold ENTRY_CF, ENTRY_SIZE in *; clear - UFB R1 EBR'; lia
          | unfold ENTRY_CM, ENTRY_SIZE in *; clear - UMB R1 EBR'; lia
          | exact VIS3| exact KREL3| exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 MP3))|].
        intros m4 s4' msF4 mo4 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DW4 VIS4 KREL4 MP4. cbn [lb_bytes fold_right blk_size snd] in DW4. rewrite Z.add_0_r in DW4.
        pose proof DW4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR14 & _ & FR24 & FR34 & _ & _ & _ & FF4 & FSH4 & LSH4 & _ & _ & _ & MI4 & AC4 & ST4 & _).
        eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4
          | eapply ade_skip2 with (q := S1c); [exact SSF8| unfold dsg2 in FR24; exact FR24| unfold dfsh in FSH4; exact FSH4| exact SHL| exact SHU| exact AS1| clear - Q2 SPR; lia| exact MI4| exact AC4]|].
        intros msF5 mo5 KREL5 MP5 (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & m5 & VIS5 & MU5 & WM5 & MI5 & FSH5 & AC5).
        assert (ST5 : stk asegs m5 lo S1c) by (eapply stk_transport_disjoint; [exact ST4| exact MU5| exact WM5| cbn; rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - CEIL FQ2 ACB; lia]).
        assert (T45 : forall A' cs, rw_cells asegs m4 A' cs -> (A' + Z.of_nat (cells_size cs) <= SH + 4 \/ SH + 264 <= A') -> rw_cells asegs m5 A' cs).
        { intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU5| exact WM5|]. cbn. clear - HA. lia. }
        assert (SHq : SH + 264 <= S1c) by (rewrite SHF; unfold sh; rewrite ASHADOW_BASE_val; clear - FQ2 ACB AS1; lia).
        assert (SHff : ff + 4096 <= SH + 4 \/ SH + 264 <= ff).
        { pose proof (aapp_not_shadowland _ _ FB3) as NSF. rewrite SHF. unfold sh. rewrite ASHADOW_BASE_val. unfold ALOWSH_LO, AHI_LO, AFS_SIZE in NSF. clear - NSF FQ5 FQ6. lia. }
        assert (DW5 : adwkGc [] NB S' M' LE (arp_sg1 (wz AR_INTERNAL_ERROR) w24 w32 w40 w48 w56 w64 w72 (wz AECH_VERSION) (wz ADE_FILE) (wz A) (wz bt) (wz (rem - 4)) (wz Bb) (wz elen) (wz cur))
                        (wz ee) (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) 0 (b8 0xf8) (poison_bytes 256 0xf8) (um0 + ENTRY_SIZE) (uf0 + ENTRY_SIZE) m5 s4').
        { eapply (adwkG_wc [] NB S' M' LE _ (wz ee) _ 0 (b8 0) (poison_bytes 256 0) (um0 + ENTRY_SIZE) (uf0 + ENTRY_SIZE) m4 s4' m5 [(SH + 4, SH + 5); (SH + 8, SH + 264)]);
            [exact DW4| exact MU5| exact WM5| exact MI5| exact ST5| | apply T45; [exact FR14| right; clear - SHq; lia]| reflexivity| apply T45; [unfold dsg2 in FR24; exact FR24| right; clear - SHq; lia]
            | apply T45; [exact FR34| right; clear - SHq; lia]| exact SZ3| apply T45; [exact FF4| unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - SHff; lia]| unfold dfsh; exact FSH5| reflexivity].
          apply Forall_cons; [right; right; right; right; left; cbn; split; apply Z.le_refl|]. apply Forall_cons; [right; right; right; right; right; left; cbn; split; apply Z.le_refl| apply Forall_nil]. }
        eapply (KSK' M' LE w24 w32 w40 w48 w56 w64 w72 (wz cur) (wz ee) x0 x1 x2 n0 n1 n2 p0 p1 p2 0 (um0 + ENTRY_SIZE) (uf0 + ENTRY_SIZE) elen m5 s4' msF5 mo5);
          [unfold adwk; exact DW5| exact EL0| exact ELR| unfold ENTRY_CM, ENTRY_SIZE; clear - EL0; lia| unfold ENTRY_CF, ENTRY_SIZE; clear - EL0; lia| exact VIS5| exact KREL5
          | exact (ah_mpres_trans H HH _ _ _ MP4 MP5)].
      + (* [comment removed for export] *)
        subst v. eapply (de_phase3 cur rem elen NB S' M' LE w24 w32 w40 w48 w56 w64 w72 x0 x1 x2 n0 n1 n2 p0 p1 p2 tpl um0 uf0 m2 s' msF2 mo2 ee pe);
          [unfold dsg1; exact DW2| unfold AENT1; exact EC2| exact AD2| exact BC| exact EL0| exact ELR| exact CR| split; [exact DB1| exact DB2]| exact UMB| exact UFB| exact NENT
          | exact KADV| exact KTA| exact KTZ| exact KTX| exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rp_entry : RPESc.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH AUXV TIME.
    unfold rp_entry_stmt.
    intros cur rem NB S' M' LE w24 w32 w40 w48 w56 w64 w72 w112 w128 w136 wee x0 x1 x2 n0 n1 n2 p0 p1 p2 tpl um uf m' s' msF' mo' rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s5w s6w s8w s10w u3 u4 u5 u6.
    intros DW BC R1 CR DB UMB UFB NENT KADV KSK KTA KTZ KTX VIS1 KREL1 MP1.
    pose proof DW as DWG. rewrite adwk_G in DWG.
    pose proof DWG as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                       & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct (ade_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DWG) as (AS1 & Q2 & Q1 & SPR & BP & BH & IB2 & NBL & NB15 & BLX & BEL & BRS & F1 & MF & IM & GM & ACCB & APB & ACB & LOS & LO0).
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (SHL : ASHB + AIMG_TOP / 8 <= SH) by (unfold ASHB, AIMG_TOP; rewrite Z.shiftr_div_pow2 by (clear; lia); clear - FQ1; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (SHU : SH + 512 < AHI_LO) by (rewrite SHF; unfold sh, AHI_LO; rewrite ASHADOW_BASE_val; clear - FQ2 ACB; lia).
    pose proof (dec_stack M M' STP) as DSK. pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1
      | eapply ade_seg1 with (q := S1c) (ff := ff) (tpl := tpl) (rb := n);
        [exact SS00| unfold dsg1 in FR1; exact FR1| unfold dsg2 in FR2; exact FR2| unfold dff in FF1; exact FF1| unfold dfsh in FSH1; exact FSH1
        | exact SHL| exact SHU| unfold AIMG_TOP; clear - FQ1; lia| exact FQ2| | exact AS1| clear - Q2 SPR; lia| exact MI1| exact AC1]|].
    { (* [comment removed for export] *) eapply aapp_sub; [exact FB3| clear - FQ5; lia| unfold AFS_SIZE; clear - FQ6; lia]. }
    intros msF2 mo2 KREL2 MP2 (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & VIS2 & MU2 & WM2 & MI2 & FF2 & FSH2 & AC2). cbn beta in VIS2.
    assert (ST2 : stk asegs m2 lo S1c).
    { eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]. cbn. rewrite SHF. unfold sh. rewrite ASHADOW_BASE_val.
      clear - CEIL FQ2 ACB. lia. }
    assert (DW2 : adwkGc [] NB S' M' LE (dsg1c w24 w32 w40 w48 w56 w64 w72 w112 w128 w136) wee (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) 0 (b8 0) (poison_bytes 256 0) um uf m2 s').
    { eapply (adwkG_wc [] NB S' M' LE _ wee _ tpl (b8 0xf8) (poison_bytes 256 0xf8) um uf m' s' m2 _ _ wee _ 0 (b8 0) (poison_bytes 256 0));
        [exact DWG| exact MU2| exact WM2| exact MI2| exact ST2| | | exact SZ1| | | exact SZ3| unfold dff; exact FF2| unfold dfsh; exact FSH2| reflexivity].
      - apply Forall_cons; [right; right; right; right; left; cbn; split; apply Z.le_refl|].
        apply Forall_cons; [right; right; right; left; cbn; split; apply Z.le_refl|].
        apply Forall_cons; [right; right; right; right; right; left; cbn; split; apply Z.le_refl| apply Forall_nil].
      - eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. unfold dsg1, arp_sg1. cbn. rewrite SHF. unfold sh. rewrite ASHADOW_BASE_val.
        clear - CEIL FQ2 ACB AS1 Q2. lia.
      - eapply rw_cells_transport; [exact FR2| exact MU2| exact WM2|]. unfold dsg2, arp_sg2. cbn. rewrite SHF. unfold sh. rewrite ASHADOW_BASE_val.
        clear - CEIL FQ2 ACB AS1 Q2. lia.
      - eapply rw_cells_transport; [exact FR3| exact MU2| exact WM2|]. unfold arp_sg3. cbn. rewrite SHF. unfold sh. rewrite ASHADOW_BASE_val.
        clear - CEIL FQ2 ACB AS1 Q2. lia. }
    clear MU2 WM2 FF2 FSH2.
    pose proof DW2 as (HP2 & LM2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv2 ERR2] & AUX2 & _ & _ & _ & _ & CHN2 & _ & LED2).
    pose proof LM2 as (IM2 & MFq2 & _ & _ & _ & _ & _ & _ & GM2 & _). rewrite F1 in MFq2.
    (* [comment removed for export] *)
    pose proof (aczalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    destruct DB as [DB1 DB2].
    eapply (ah_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := mid_errblocks M' ++ drestc [] NB LE) (s := s') (num := ENTRY_SIZE) (size := 1) (v := 1) (errv := errv2) (CH := CH1c); clear CZ.
      all: try first [exact VIS2| exact HP2| exact KREL2| exact AUX2| exact MI2| exact IM2| exact GM2| exact MFq2| exact CEIL| exact AC2| exact CHN2| exact ERR2].
      all: lazymatch goal with
           | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
           | |- 1 = 1 => reflexivity
           | |- 1 <= ENTRY_SIZE * 1 <= _ => unfold ENTRY_SIZE; clear; lia
           | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_app; unfold ENTRY_BYTES, ENTRY_SIZE in *; clear - DB1 EB R1 EBR'; lia
           | |- Z.of_nat (length _) + _ <= _ => rewrite length_app, Nat2Z.inj_add; unfold ENTRY_CNT, ERRSTR_CNT in *; pose proof (Z.div_pos (2 * rem) 5 ltac:(clear - R1; lia) ltac:(clear; lia)) as DP; clear - DB2 EC DP ECR'; lia
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - SPB Q2; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); exact ST2
           | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); clear - LO DSK Q2; lia
           | |- Z_to_bv 64 ATP = _ => reflexivity
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [E|Hin]; rewrite unsigned_lit by (clear - Q2 SPR CEIL LOS LO0; lia); [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]
           | |- pf_ok _ _ _ _ => unfold ADE_R1; rewrite unsigned_lit by (clear; lia); apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left;
                                 unfold PF_entry; apply in_or_app; left; exact He
           | |- as_Cm H _ <= as_AL H _ => pose proof ((RCI LEDGER_pay) s' um uf ENTRY_SIZE 0 LED2 ltac:(unfold ENTRY_SIZE; clear; lia) ltac:(clear; lia)
                                                             ltac:(unfold ENTRY_CM, ENTRY_SIZE in *; clear - UMB R1 EBR'; lia) ltac:(unfold ENTRY_CF in *; clear - UFB R1 EBR'; lia)) as PY;
                                             pose proof (proj1 (proj2 (proj2 (ah_costs H HH))) 0 ltac:(clear; lia)) as CFz; replace (ENTRY_SIZE * 1) with ENTRY_SIZE by (clear; lia); clear - PY CFz; lia
           | |- ?G => idtac "CZ_LEFT" G
           end. }
    clear CZ. intros [msF3 mo3] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m3 & errv3 & ee & pe & s3' & VIS3 & KREL3 & MP3 & MI3 & AC3 & ST3 & ERR3 & AUX3 & XP3 & EBR & HP3 & EC0 & AD3 & MF3 & IM3 & GM3 & AL3).
    rewrite (unsigned_lit S1c) in ST3, XP3 by (clear - Q2 SPR CEIL LOS LO0; lia).
    replace (ENTRY_SIZE * 1) with ENTRY_SIZE in EBR, HP3, EC0, AD3, AL3 by (clear; lia).
    assert (LED3 : LEDGERc s3' (um + ENTRY_SIZE) uf).
    { pose proof ((RCI LEDGER_step) s' s3' um uf ENTRY_SIZE 0 LED2 ltac:(unfold ENTRY_SIZE; clear; lia) ltac:(clear; lia)) as LS. rewrite Z.add_0_r in LS. apply LS.
      pose proof (proj1 (proj2 (proj2 (ah_costs H HH))) 0 ltac:(clear; lia)) as CFz. clear - AL3 CFz. lia. }
    assert (DW3 : adwkGc [(pe, ee, ENTRY_SIZE)] NB S' M' LE (dsg1c w24 w32 w40 w48 w56 w64 w72 w112 w128 w136) wee (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) 0 (b8 0) (poison_bytes 256 0) (um + ENTRY_SIZE) uf m3 s3').
    { eapply (adwkG_xc [] [(pe, ee, ENTRY_SIZE)]); [exact DW2| | | exact MI3| exact AC3| exact ST3| exact AUX3| exact ERR3| exact LED3].
      - apply (ECH_AC14_kit.axpres_drop_memflag H _ S1c [] [] m2 m3 MFq2 MF3). cbn [app]. rewrite app_nil_r. exact XP3.
      - eapply PERM; [exact HP3|]. rewrite (drest_app LB p A nA pbin Bb nB TB [(pe, ee, ENTRY_SIZE)] NB LE). apply Permutation_middle. }
    eapply (de_phase2 cur rem NB S' M' LE w24 w32 w40 w48 w56 w64 w72 w112 w128 w136 wee x0 x1 x2 n0 n1 n2 p0 p1 p2 tpl (um + ENTRY_SIZE) uf um uf m3 s3' msF3 mo3 ee pe);
      [exact DW3| | exact AD3| exact BC| exact R1| exact CR| | reflexivity| reflexivity| exact UMB| exact UFB| exact NENT| exact KADV| exact KSK| exact KTA| exact KTZ| exact KTX| exact VIS3| exact KREL3
      | exact (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 MP3))].
    - eapply arw_cells_recut; [exact EC0| vm_compute; repeat split; reflexivity| vm_compute; reflexivity].
    - unfold dbud in *. rewrite (drest_app LB p A nA pbin Bb nB TB [(pe, ee, ENTRY_SIZE)] NB LE), lb_bytes_app, length_app, Nat2Z.inj_add.
      cbn [lb_bytes length fold_right app blk_size snd Z.of_nat Pos.of_succ_nat]. clear - DB1 DB2. unfold ENTRY_SIZE in *. lia.
  Qed.
End RC.

(* [comment removed for export] *)
Theorem aentry_shape `{HCEIL : HeapCeil} : forall H, asan_rt_hyps_x H -> araise_stmt H -> atime_stmt H -> rp_entry_shape H.
Proof.
  intros H HX RAISE TIME. unfold rp_entry_shape. intros. eapply rp_entry; eassumption.
Qed.
