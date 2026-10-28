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
  ECH_ALibMF ECH_Iface ECH_AStmt_C1 ECH_AC1_zalloc ECH_AC1_free ECH_AC1_malloc ECH_AC1_dup ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C5 ECH_AStmt_C6 ECH_AC6_acc ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9
  ECH_AStmt_C10 ECH_AStmt_C13 ECH_AKit ECH_AKitSeg ECH_AsKit ECH_AC13_entry ECH_AC13_store ECH_AC7_kit ECH_AC7_rd ECH_AC7_rd2 ECH_AC7_bioread ECH_AC7_biofreeint ECH_ARostr ECH_ALibMid ECH_AC11_fail
  ECH_AKitS ECH_AC12_addstr ECH_AC13_small ECH_AC13 ECH_AC14_kit ECH_AC14_bio2buf_seg ECH_AC14_ladder_seg ECH_AC14_ladloop ECH_AC14_fmt_seg ECH_AC14_flat_seg ECH_AC14_b64arm_seg ECH_AC14_entry_seg
  ECH_AStmt_C14 F_strspn N6_strspn ECH_AC14_b2b ECH_AC14_fmt ECH_AC14_dec ECH_AC14_b64arm AsAuxv.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition S_AFUNC_D1 : list byte := Eval vm_compute in img_cstr AFUNC_D1 64.
Definition K_AFUNC_D1 : list byte := Eval vm_compute in img_slack AFUNC_D1 (length S_AFUNC_D1).
Definition S_AFUNC_DF : list byte := Eval vm_compute in img_cstr AFUNC_DF 64.
Definition K_AFUNC_DF : list byte := Eval vm_compute in img_slack AFUNC_DF (length S_AFUNC_DF).

(* [comment removed for export] *)
Lemma pf_shift_mono14 : forall r A B, incl A B -> incl (pf_shift r A) (pf_shift r B).
Proof. intros r A B I. unfold pf_shift. apply incl_map. exact I. Qed.
Section KF.
  Context {HCEIL : HeapCeil}.
  Lemma R_AFUNC_D1 : AROSTR AFUNC_D1 S_AFUNC_D1 K_AFUNC_D1.
  Proof. eapply AROSTR_intro; [apply ROSTR_of_image; vm_compute; reflexivity| unfold aglobals; cbn; tauto| vm_compute; intros X; discriminate X| vm_compute; intros X; discriminate X]. Qed.
  Lemma R_AFUNC_DF : AROSTR AFUNC_DF S_AFUNC_DF K_AFUNC_DF.
  Proof. eapply AROSTR_intro; [apply ROSTR_of_image; vm_compute; reflexivity| unfold aglobals; cbn; tauto| vm_compute; intros X; discriminate X| vm_compute; intros X; discriminate X]. Qed.
  Lemma S_AFUNC_D1_len : Z.of_nat (length S_AFUNC_D1) = 20. Proof. reflexivity. Qed.
  Lemma S_AFUNC_DF_len : Z.of_nat (length S_AFUNC_DF) = 22. Proof. reflexivity. Qed.
  Lemma PF_errnew_mstep14 : forall M M', mid_step M M' -> incl (PF_errnew (mid_err M')) (PF_errnew (mid_err M)).
  Proof.
    intros M M' (_ & _ & SE & _). unfold PF_errnew. apply incl_app_app; [| apply incl_refl]. apply pf_shift_mono14.
    destruct (mid_err M) as [|c0] eqn:E0; destruct (mid_err M') as [|c1] eqn:E1; cbn [PF_egs]; try apply incl_refl; [apply incl_nil_l|].
    exfalso. specialize (SE _ eq_refl). discriminate SE.
  Qed.
  (* [comment removed for export] *)
  Lemma errph_delta_bounds14 : forall eph LEn c, errph_delta eph LEn c ->
    Z.of_nat (length LEn) + errph_cnt (ErrReady c) <= errph_cnt eph /\ lb_bytes LEn + errph_bytes (ErrReady c) <= errph_bytes eph.
  Proof.
    clear. intros [|c0] LEn c DL; cbn [errph_delta errph_cnt errph_bytes] in *.
    - destruct DL as (Q1 & Q2 & _). lia.
    - destruct DL as [_ ->]. cbn. lia.
  Qed.
End KF.

(* [comment removed for export] *)
Section KC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Lemma f14_Cf_nonneg : forall n, 0 <= n -> 0 <= as_Cf H n.
  Proof. pose proof (ah_costs H HH) as (_ & _ & K & _). exact K. Qed.
  Lemma f14_Cf_mono : forall n n', 0 <= n <= n' -> as_Cf H n <= as_Cf H n'.
  Proof. pose proof (ah_costs H HH) as (_ & _ & _ & K & _). exact K. Qed.
  Lemma f14_Cf_super : forall a b, 0 <= a -> 0 <= b -> as_Cf H a + as_Cf H b <= as_Cf H (a + b).
  Proof. pose proof (ah_costs H HH) as (_ & _ & _ & _ & _ & K). exact K. Qed.
  Lemma f14_Cf_arg : forall x a b, x <= as_Cf H a -> a = b -> x <= as_Cf H b.
  Proof. intros x a b K E. subst b. exact K. Qed.
  Lemma f14_Cf_zero : as_Cf H 0 = 0.
  Proof. pose proof (f14_Cf_super 0 0 (Z.le_refl 0) (Z.le_refl 0)) as K. pose proof (f14_Cf_nonneg 0 (Z.le_refl 0)) as K'. rewrite Z.add_0_r in K. lia. Qed.

  Lemma f14_Forall2_In_combine : forall (A B : Type) (R : A -> B -> Prop) (l : list A) (l' : list B) (x : A) (y : B),
    Forall2 R l l' -> In (x, y) (combine l l') -> R x y.
  Proof.
    intros A B R l l' x y F Hin. induction F as [|a b l0 l0' Rab F IH]; [destruct Hin|].
    cbn in Hin. destruct Hin as [E|Hin]; [injection E as <- <-; exact Rab| exact (IH Hin)].
  Qed.
  Lemma f14_ocost_bound : forall P o, Forall (fun b => 0 <= blk_size b) (blocks_of P o) ->
    0 <= lb_bytes (blocks_of P o) /\ ocost H o <= as_Cf H (lb_bytes (blocks_of P o)).
  Proof.
    intros P [[id n]|] F; cbn [blocks_of ocost] in *.
    - pose proof (Forall_inv F) as K. cbn in K. rewrite lb_bytes_cons. cbn [blk_size snd lb_bytes fold_right]. rewrite Z.max_l by lia. split; [lia|]. apply f14_Cf_mono. lia.
    - cbn [lb_bytes fold_right]. rewrite f14_Cf_zero. lia.
  Qed.

  Lemma f14_ecost_sum_bound : forall (X : Type) (f : X -> Z) (g : Z -> X -> list block) (ps : list Z) (xs : list X),
    length xs = length ps ->
    (forall p x, In (p, x) (combine ps xs) -> 0 <= lb_bytes (g p x) /\ f x <= as_Cf H (lb_bytes (g p x))) ->
    0 <= lb_bytes (concat (map (fun pe => g (fst pe) (snd pe)) (combine ps xs)))
    /\ ecost_sum X f xs <= as_Cf H (lb_bytes (concat (map (fun pe => g (fst pe) (snd pe)) (combine ps xs)))).
  Proof.
    intros X f g ps xs. revert ps. induction xs as [|x xs IH]; intros [|p ps] LEN HF; cbn [length] in LEN; try lia.
    - cbn. rewrite f14_Cf_zero. lia.
    - cbn [combine map concat fst snd ecost_sum fold_right]. rewrite lb_bytes_app_s.
      destruct (HF p x ltac:(left; reflexivity)) as [B1 B2].
      destruct (IH ps ltac:(lia) ltac:(intros p' x' Hin; apply HF; right; exact Hin)) as [B3 B4].
      change (fold_right (fun x0 acc => f x0 + acc) 0 xs) with (ecost_sum X f xs).
      split; [lia|]. pose proof (f14_Cf_super _ _ B1 B3). lia.
  Qed.

  Lemma f14_sk_cost_bound : forall P K, Forall (fun b => 0 <= blk_size b) (blocks_SK P K) ->
    0 <= lb_bytes (blocks_SK P K) /\ as_Cf H (Z.max (8 * sk_cap K) 0) + as_Cf H SK_SIZE <= as_Cf H (lb_bytes (blocks_SK P K)).
  Proof.
    intros P K F. unfold blocks_SK in *. rewrite lb_bytes_cons. cbn [blk_size snd].
    destruct (sk_cap K =? 0) eqn:E.
    - apply Z.eqb_eq in E. rewrite E. cbn [lb_bytes fold_right Z.mul Z.max]. rewrite f14_Cf_zero. unfold SK_SIZE. rewrite Z.add_0_r. split; [lia|]. lia.
    - pose proof (Forall_inv (Forall_inv_tail F)) as K2. cbn in K2. rewrite lb_bytes_cons. cbn [blk_size snd lb_bytes fold_right].
      rewrite Z.max_l by lia. unfold SK_SIZE in *. split; [lia|]. pose proof (f14_Cf_super (8 * sk_cap K) 56 ltac:(lia) ltac:(lia)) as K3. eapply (f14_Cf_arg _ _ _ K3). lia.
  Qed.

  Lemma f14_ext_cost_bound : forall LB m p X, EXTobj LB m p X -> Forall (fun b => 0 <= blk_size b) (blocks_EXT p X) ->
    0 <= lb_bytes (blocks_EXT p X) /\ ext_cost H X <= as_Cf H (lb_bytes (blocks_EXT p X)).
  Proof.
    intros LB m p X _ F. unfold blocks_EXT, ext_cost in *. rewrite lb_bytes_cons. cbn [blk_size snd].
    destruct (f14_ocost_bound (ex_val X) (ex_val_o X) (Forall_inv_tail F)) as [B1 B2]. unfold EXT_SIZE in *.
    split; [lia|]. pose proof (f14_Cf_super 16 (lb_bytes (blocks_of (ex_val X) (ex_val_o X))) ltac:(lia) B1). lia.
  Qed.

  Lemma f14_exts_cost_bound : forall LB m P xs, EXTS LB m P xs -> Forall (fun b => 0 <= blk_size b) (blocks_EXTS P xs) ->
    0 <= lb_bytes (blocks_EXTS P xs) /\ exts_cost H xs <= as_Cf H (lb_bytes (blocks_EXTS P xs)).
  Proof.
    intros LB m P [[K es]|] EX F; cbn [blocks_EXTS exts_cost] in *.
    - destruct EX as (_ & _ & LEN & F2). apply Forall_app in F. destruct F as [FS FE].
      destruct (f14_sk_cost_bound P K FS) as [S1 S2]. rewrite lb_bytes_app_s.
      destruct (f14_ecost_sum_bound extrep (ext_cost H) blocks_EXT (sk_elems K) es LEN) as [E1 E2].
      { intros p x Hin. eapply f14_ext_cost_bound with (LB := LB) (m := m).
        - eapply (f14_Forall2_In_combine _ _ _ _ _ _ _ F2 Hin).
        - rewrite Forall_forall in FE. apply Forall_forall. intros b Hb. apply FE. apply in_concat. exists (blocks_EXT p x). split; [| exact Hb].
          apply in_map_iff. exists (p, x). split; [reflexivity| exact Hin]. }
      split; [lia|]. pose proof (f14_Cf_super _ _ S1 E1). lia.
    - cbn [lb_bytes fold_right]. pose proof (f14_Cf_nonneg 0 ltac:(lia)). lia.
  Qed.

  Lemma f14_entry_cost_bound : forall LB m p E, ENTRYobj LB m p E -> Forall (fun b => 0 <= blk_size b) (blocks_ENTRY p E) ->
    0 <= lb_bytes (blocks_ENTRY p E) /\ entry_cost H E <= as_Cf H (lb_bytes (blocks_ENTRY p E)).
  Proof.
    intros LB m p E EO F. unfold blocks_ENTRY, entry_cost in *. rewrite lb_bytes_cons. cbn [blk_size snd].
    pose proof (Forall_inv_tail F) as F'. cbn [blk_size snd] in F'.
    apply Forall_app in F'. destruct F' as [F1 F']. apply Forall_app in F'. destruct F' as [F2 F']. apply Forall_app in F'. destruct F' as [F3 F'].
    apply Forall_app in F'. destruct F' as [F4 F5].
    destruct (f14_ocost_bound _ _ F1) as [A1 A2]. destruct (f14_ocost_bound _ _ F2) as [B1 B2]. destruct (f14_ocost_bound _ _ F3) as [G1 G2]. destruct (f14_ocost_bound _ _ F4) as [D1 D2].
    destruct EO as (_ & _ & _ & _ & _ & _ & EX). destruct (f14_exts_cost_bound _ _ _ _ EX F5) as [X1 X2].
    rewrite !lb_bytes_app_s.
    set (bA := lb_bytes (blocks_of (en_pname E) (en_pname_o E))) in *. set (bB := lb_bytes (blocks_of (en_pub E) (en_pub_o E))) in *.
    set (bC := lb_bytes (blocks_of (en_suites E) (en_suites_o E))) in *. set (bD := lb_bytes (blocks_of (en_encoded E) (en_encoded_o E))) in *.
    set (bX := lb_bytes (blocks_EXTS (en_exts E) (en_exts_o E))) in *.
    unfold ENTRY_SIZE in *. split; [lia|].
    pose proof (f14_Cf_super bD bX D1 X1) as S4.
    pose proof (f14_Cf_super bC (bD + bX) G1 ltac:(lia)) as S3.
    pose proof (f14_Cf_super bB (bC + (bD + bX)) B1 ltac:(lia)) as S2.
    pose proof (f14_Cf_super bA (bB + (bC + (bD + bX))) A1 ltac:(lia)) as S1.
    pose proof (f14_Cf_super 104 (bA + (bB + (bC + (bD + bX)))) ltac:(lia) ltac:(lia)) as S0.
    lia.
  Qed.

End KC.
(* [comment removed for export] *)
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
  Hypothesis AUXV : aauxv_ok m B.
  Local Notation SH := (Z.shiftr ff 3 + ASHB).

  (* [comment removed for export] *)
  Local Notation adwkGc := (adwkG H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5).
  Local Notation adwkc := (adwk H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5).
  Local Notation drestc := (drest LB p A nA pbin Bb nB TB).
  Local Notation dffc := (dff sp fp n fj24 tpb fj128 fj2).
  Local Notation dfshc := (dfsh e5).
  Local Notation dsg2c := (dsg2 A ff).
  Local Notation dsg1c := (dsg1 st Bb bt ff).
  Local Notation "'DCT' f" := (f H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5) (at level 10, f at level 0).
  Local Notation "'DCJ' f" := (f H HX RAISE PF9new PF9free ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LIB LB LF M x st mb lo B S R ds errv CH
                                 VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE
                                 p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5 NAR NBR MST POS BTR BT_frame FRESH)
    (at level 10, f at level 0).
  Local Notation adwkG_esc := (adwkG_es H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M x st mb lo B S R ds CH CTX p A nA pbin Bb nB bs R' TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5).
  Local Notation adwkG_hfc := (adwkG_heap_facts H HX ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5).
  Local Notation btfreec := (btfree_stmt H PF9free ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5).

  (* [comment removed for export] *)
  Hypothesis RPE : DCT rp_entry_stmt.
  Hypothesis BTFREE : btfreec.

  (* [comment removed for export] *)
  Lemma dcf_smoke : forall NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl um uf m' s',
    adwkGc [] NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m' s' -> DCT rp_errl_stmt -> True.
  Proof. intros. exact I. Qed.

  (* [comment removed for export] *)
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
  Lemma rp_postN : forall m' msF' mo' (s' : as_St H) (rv : Z) (NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (XSq : list (Z * Z))
      (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 errv' : word),
    as_VIS H s' msF' = MS (mkR ra sp gp (Z_to_bv 64 ATP) u0 u1 u2 s0 s1 (Z_to_bv 64 rv) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                       F (ret_pc ra) fc None m' (seg_rom asegs) ->
    (rv = 0 \/ rv = 1) -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' -> mem_inv asegs m' -> ACONST m' ->
    stk asegs m' lo (bv_unsigned sp) -> stack0 m' lo (bv_unsigned sp) ->
    rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv'] -> as_rauxv_ok H m' B ->
    as_RHEAP H s' (mid_errblocks M' ++ NB ++ LE ++ LB) m' -> LIBMID (LE ++ LIB) m' M' -> mid_step M M' -> mid_newlib_ok M M' LE -> mid_ctx M' = mid_ctx M ->
    Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M') <= ERRSTR_BYTES ->
    MEMBIO H LB m' mb R' -> MEMBIO_shad m' mb R' -> bytes_at asegs m' (mb_buf R) ds ->
    STOREobj (NB ++ LE ++ LB) m' st S' -> STORE_shad m' st S' -> es_id S' = es_id S -> Permutation (blocks_STORE st S') ((es_id S, st, STORE_SIZE) :: NB) ->
    List.NoDup (map blk_id (blocks_STORE st S')) -> dnb NB ->
    as_RFS H LF m' -> Forall (fs_scratch H LF) XSq ->
    xpres H LB (bv_unsigned sp) (XSq ++ XFc) m m' ->
    as_AL H s' >= as_AL H s - READCFG_COST H M ->
    as_SR H POSTc (mkCfg msF' mo').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    intros m' msF' mo' s' rv NB S' M' LE XSq u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 errv'.
    intros VIS' RV KREL' MP' MI' AC' ST' ST0' ERR' AUX' HP' LM' STEP' NEW' CTX' EC' EB' MBO' MSH' DS' SO' SSH' SID' SPM' SND' [DC DB] RFS' FXSq XP' AL'.
    apply (ah_done H HH). unfold POST, readcfg_post. cbn [cfg_ms cfg_model]. rewrite TP.
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', errv', s', rv, M', S', R', LE, NB, XSq.
    cbv zeta.
    split; [exact VIS'|]. split; [exact RV|]. split; [exact KREL'|]. split; [exact MP'|].
    split; [exact MI'|]. split; [exact AC'|]. split; [exact ST'|]. split; [exact ST0'|]. split; [exact ERR'|]. split; [exact AUX'|]. split; [exact HP'|].
    split; [exact LM'|]. split; [exact STEP'|]. split; [exact NEW'|]. split; [exact CTX'|].
    split; [exact SO'|]. split; [exact SSH'|]. split; [exact SID'|]. split; [exact SPM'|].
    split; [exact DC|]. split; [exact DB|].
    split; [exact EC'|]. split; [exact EB'|]. split; [exact SND'|].
    split; [eapply MEMBIO_mono; [exact MBO'| intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb]|].
    split; [exact MSH'|]. split; [exact (mb_static_blocks mb R R' MST)|]. split; [exact DS'|].
    split; [exact FXSq|]. split; [exact RFS'|].
    split; [exact (ah_thr H HH _ _ _ HP')|].
    split; [unfold XF in XP'; exact XP'| exact AL'].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_exitN : forall m1 msF1 mo1 (s1' : as_St H) (rv : Z) (NB : list block) (S' : storerep) (M' : libmid) (LE : list block)
      (fj1 : list byte) (slots : list cell) (XSq : list (Z * Z))
      (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s2v s3v s4v s6v s7v s9v s11v u3 u4 u5 u6 errv1 : word),
    as_VIS H s1' msF1 = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) b0 b1 b2 b3 b4 b5 b6 b7
                                s2v s3v s4v (Z_to_bv 64 rv) s6v s7v (Z_to_bv 64 ff) s9v (Z_to_bv 64 ff) s11v u3 u4 u5 u6)
                        F (Z_to_bv 64 AEXIT) fc None m1 (seg_rom asegs) ->
    (rv = 0 \/ rv = 1) -> as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 -> mem_inv asegs m1 -> ACONST m1 ->
    stk asegs m1 lo S1c -> stack0 m1 lo (bv_unsigned sp) ->
    cells_size slots = 344%nat -> rw_cells asegs m1 S1c slots -> rw_cells asegs m1 (S1c + 344) [CB (Z.to_nat KGc) jg] -> rw_cells asegs m1 (bv_unsigned sp + -104) SAVESc ->
    rw_cells asegs m1 ff (arp_fframe S1c fj1 n fj2 fp) -> as_RFS H (LF1c ff fp) m1 ->
    rw_cells asegs m1 (errno_addr (Z_to_bv 64 ATP)) [C4 errv1] -> as_rauxv_ok H m1 B ->
    as_RHEAP H s1' (mid_errblocks M' ++ NB ++ LE ++ LB) m1 -> LIBMID (LE ++ LIB) m1 M' -> mid_step M M' -> mid_newlib_ok M M' LE -> mid_ctx M' = mid_ctx M ->
    Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M') <= ERRSTR_BYTES ->
    MEMBIO H LB m1 mb R' -> MEMBIO_shad m1 mb R' -> bytes_at asegs m1 (mb_buf R) ds ->
    STOREobj (NB ++ LE ++ LB) m1 st S' -> STORE_shad m1 st S' -> es_id S' = es_id S -> Permutation (blocks_STORE st S') ((es_id S, st, STORE_SIZE) :: NB) ->
    List.NoDup (map blk_id (blocks_STORE st S')) -> dnb NB ->
    Forall (fs_scratch H LF) XSq -> (forall a, rin_ivs (XSFc ff fp) a -> rin_ivs XSq a) ->
    xpres H LB (bv_unsigned sp) (XSq ++ XFc) m m1 ->
    as_AL H s1' >= as_AL H s - READCFG_COST H M ->
    as_SR H POSTc (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    intros m1 msF1 mo1 s1' rv NB S' M' LE fj1 slots XSq rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s2v s3v s4v s6v s7v s9v s11v u3 u4 u5 u6 errv1.
    intros VIS1 RV KREL1 MP1 MI1 AC1 STK1 ST01 SLZ SL1 GP1 SV1 FRM1 RFS1 ERR1 AUX1 HP1 LM1 STEP1 NEW1 CTX1 EC1 EB1 MBO1 MSH1 DS1 SO1 SSH1 SID1 SPM1 SND1 DNB1 FSq INCq XP1 AL1.
    pose proof MST as MST1.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof (rc_stack M) as (_ & _ & _ & _ & STKA).
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    pose proof MST1 as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    set (Lall := mid_errblocks M' ++ NB ++ LE ++ LB) in *.
    assert (SLB : forall b, In b LB -> In b Lall) by (intros b Hb; unfold Lall; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
    assert (BRS : forall b, In b Lall -> ablock_range H (blk_addr b) (blk_size b)) by (intros b Hb; exact (ah_blocks H HH _ _ _ _ HP1 Hb)).
    pose proof SBR as (_ & SB2 & _ & SBa & SBb & SBf & SBc). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, STORE_SIZE, AIMG_TOP, AFS_SIZE in *.
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
    assert (S0 : sh 0xc04000 = 0x80178800) by reflexivity.
    pose proof (sh_add8 ff 512) as SH8. replace (ff + 8 * 512) with (ff + 4096) in SH8 by (clear; lia).
    pose proof (sh_mono (as_FSB H) ff ltac:(clear - FF5; lia)) as SHL. pose proof (sh_mono (ff + 4096) (as_FSB H + 11571200) FF6) as SHU.
    pose proof (sh_aapp_range _ _ FB3 ltac:(clear; lia)) as (W1 & W2 & W3). unfold nsh in W2. unfold AIMG_TOP in W1.
    pose proof (aapp_not_shadowland _ _ FB3) as NSF.
    (* [comment removed for export] *)
    set (WX := [(ff, ff + 4096); (S1c - AFS_STACK, S1c); (fp, fp + 1); (sh ff, sh ff + 512)]).
    assert (FW : Forall (fswin H) WX).
    { subst WX. unfold fswin, AFS_SIZE. apply Forall_cons; [right; left; cbn; clear - FF5 FF6; lia|]. apply Forall_cons; [left; cbn; unfold AFS_STACK; clear - CEIL LO STK0 Q2; lia|].
      apply Forall_cons; [right; left; cbn; clear - FP3 FP4 FF5; lia|]. apply Forall_cons; [| apply Forall_nil].
      right; right. cbn. clear - SHL SHU SH8. lia. }
    assert (CW : forall L, Forall (aclient_write_ok H L) WX) by (intros L; eapply Forall_impl; [intros iv; apply (fswin_cw H)| exact FW]).
    assert (S0K : Forall stack0_ok WX).
    { subst WX. apply Forall_cons; [eapply stack0_ok_aapp; [exact FB3| clear - FF5; lia| clear - FF6; lia]|].
      apply Forall_cons; [apply stack0_ok_app; unfold AHI_LO, AFS_STACK; clear - CEIL LO STK0 Q2 ACB; lia|].
      apply Forall_cons; [eapply stack0_ok_aapp; [exact FB3| clear - FP3; lia| clear - FP4 FF5; lia]|].
      apply Forall_cons; [apply stack0_ok_sh'; [clear - FF1; lia| clear; lia| clear - FF6 FB2; lia]| apply Forall_nil]. }
    (* [comment removed for export] *)
    assert (BW : forall A n, A mod 16 = 0 -> 0 <= n -> 0xc04000 <= A -> A + n <= aceil -> (A + n + 16 <= as_FSB H \/ as_FSB H + 11571200 <= A - 16) -> aapp A n ->
              Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) WX /\ Forall (winX A n) WX).
    { intros A' n' M16 N0 LA HA AP AA. pose proof (aapp_not_shadowland _ _ AA) as NSA. subst WX. unfold winX, AFS_STACK. split.
      - apply Forall_cons; [cbn; clear - AP FF5 FF6; lia|]. apply Forall_cons; [cbn; clear - HA CEIL LO STK0 Q2; lia|].
        apply Forall_cons; [cbn; clear - AP FP3 FP4 FF5; lia|]. apply Forall_cons; [| apply Forall_nil]. cbn.
        pose proof (sh_mono _ _ FB2) as SHA. unfold ALOWSH_LO, AHI_LO in *. clear - NSA SHL SHU SH8 SHA W3 FF1. unfold sh in *. rewrite ?ASHADOW_BASE_val in *. lia.
      - apply Forall_cons; [cbn; unfold ALOWSH_LO, AHI_LO in *; rewrite ?ASHADOW_BASE_val; clear - NSF FF5 FF6; lia|].
        apply Forall_cons; [cbn; right; left; unfold AHI_LO; clear - CEIL LO STK0 Q2 ACB; lia|].
        apply Forall_cons; [cbn; unfold ALOWSH_LO, AHI_LO in *; rewrite ?ASHADOW_BASE_val; clear - NSF FP3 FP4 FF5; lia|].
        apply Forall_cons; [| apply Forall_nil]. cbn. right; right. unfold sh, nsh. clear - M16 N0 AP FF5 FF6 FF64. Z.div_mod_to_equations. lia. }
    assert (BWb : forall b, In b Lall -> Forall (fun iv : Z * Z => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) WX /\ Forall (winX (blk_addr b) (blk_size b)) WX).
    { intros b Hb. pose proof (BRS b Hb) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). unfold AIMG_TOP, AFS_SIZE in E4, E6. exact (BW _ _ E2 E3 E4 E5 E6 E7). }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply aexit; [clear - FF1; lia| clear - FF2 ACB; lia| exact FRM1| exact MI1]|].
    intros msF2 mo2 KREL2 MP2 (m2 & VIS2 & MU2 & WM2 & MI2 & FRM2).
    assert (AW2 : Forall (afs_write_ok H (LF1c ff fp)) [(ff, ff + 8)]).
    { apply Forall_cons; [| apply Forall_nil]. right. exists (6, ff, fp). split; [left; reflexivity| cbn; unfold fsz; cbn; clear; lia]. }
    assert (RFS2 : as_RFS H (LF1c ff fp) m2) by (eapply (ah_RFS_frame H HH); [exact RFS1| exact MU2| exact WM2| exact AW2]).
    assert (AC2 : ACONST m2).
    { eapply ACONST_frame; [exact AC1| exact MU2| exact WM2|]. apply Forall_cons; [eapply aconst_ok_aapp; [exact FB3| cbn; clear - FF5; lia| cbn; clear - FF6; lia]| apply Forall_nil]. }
    assert (STK2 : stk asegs m2 lo S1c) by (eapply stk_transport_disjoint; [exact STK1| exact MU2| exact WM2| cbn; clear - FF6 FB2 CEIL Q2; lia]).
    (* [comment removed for export] *)
    pose proof SF6 as SF. unfold stack_free_6_stmt in SF.
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| |].
    { eapply SF with (LF := LF1c ff fp) (lo := lo) (n := ARP_FFREQ) (fp := fp); clear SF.
      - exact RFS2.
      - left; reflexivity.
      - change (Z.to_nat (fsz 6 - 40)) with 4056%nat. unfold wz in FRM2 |- *. exact FRM2.
      - reflexivity.
      - reflexivity.
      - unfold ARP_FFREQ, fsz. clear. cbn. lia.
      - rewrite unsigned_lit by (clear - Q2 LO0 CEIL STK0 LO SPR; lia). exact STK2.
      - exact CEIL.
      - rewrite unsigned_lit by (clear - Q2 LO0 CEIL STK0 LO SPR; lia). clear - LO STKA Q2. lia.
      - exact MI2.
      - exact AC2. }
    clear SF. intros msF3 mo3 KREL3 MP3 PO. unfold stack_free_post in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & VIS3 & MU3 & WM3 & MI3 & ST3 & RFS3 & SHD3 & AC3).
    rewrite (unsigned_lit S1c) in MU3, ST3 by (clear - Q2 LO0 CEIL STK0 LO SPR; lia). unfold LF1 in RFS3. rewrite lf_remove_head in RFS3. change (fshn 6) with 512 in MU3.
    (* [comment removed for export] *)
    assert (MU13 : munch WX m1 m3).
    { subst WX. eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; intros z Hz; cbn in Hz |- *; clear - Hz; lia. }
    pose proof (wmono_trans asegs _ _ _ WM2 WM3) as WM13.
    (* [comment removed for export] *)
    assert (FRW : Forall (fun iv : Z * Z => bv_unsigned sp <= fst iv \/ snd iv <= S1c) WX).
    { subst WX. unfold AFS_STACK. apply Forall_cons; [cbn; clear - FF6 FB2 CEIL LO STK0 Q2; lia|]. apply Forall_cons; [cbn; clear; lia|].
      apply Forall_cons; [cbn; clear - FP4 FF5 FF6 FB2 CEIL LO STK0 Q2; lia|]. apply Forall_cons; [| apply Forall_nil]. cbn. pose proof (sh_mono _ _ FB2) as SHA'. clear - SHU SH8 SHA' W3 CEIL LO STK0 Q2 ACB. unfold AHI_LO in W3. lia. }
    assert (T13 : forall A' cs, rw_cells asegs m1 A' cs -> S1c <= A' -> A' + Z.of_nat (cells_size cs) <= bv_unsigned sp -> rw_cells asegs m3 A' cs).
    { intros A' cs RC HA HB. eapply rw_cells_transport; [exact RC| exact MU13| exact WM13|].
      clear - FRW HA HB. induction WX as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv FRW) as K. cbn in K. split; [lia| exact (IH (Forall_inv_tail FRW))]. }
    pose proof (T13 _ _ SV1 ltac:(clear - Q2; lia) ltac:(cbn; clear; lia)) as SV3.
    pose proof (T13 _ _ SL1 ltac:(clear; lia) ltac:(rewrite SLZ; clear - Q2; lia)) as SL3.
    pose proof (T13 _ _ GP1 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold KG; change (rp_s1 (bv_unsigned sp)) with S1c; clear - Q2; lia)) as GP3.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply aepi; [clear - Q2 CEIL LO STK0 LO0; lia| exact SV3| exact MI3]|].
    intros msF4 mo4 KREL4 MP4 VIS4. cbn beta in VIS4.
    (* [comment removed for export] *)
    assert (STK3 : stk asegs m3 lo (bv_unsigned sp)).
    { assert (FR3 : rw_cells asegs m3 S1c (slots ++ [CB (Z.to_nat KGc) jg] ++ SAVESc)).
      { apply (proj2 (rw_cells_app asegs m3 S1c slots _)). split; [exact SL3|]. rewrite SLZ.
        apply (proj2 (rw_cells_app asegs m3 _ [CB (Z.to_nat KGc) jg] SAVESc)). split; [exact GP3|].
        cbn [cells_size csize Nat.add]. replace (S1c + Z.of_nat 344 + Z.of_nat (Z.to_nat KGc + 0)) with (bv_unsigned sp + -104) by (unfold KG; change (rp_s1 (bv_unsigned sp)) with S1c; clear - Q2; lia). exact SV3. }
      pose proof (stk_release asegs m3 lo _ _ ST3 FR3 ltac:(clear - CEIL LO STK0 Q2; lia)) as K.
      rewrite !cells_size_app, SLZ in K. unfold SAVES, arp_saves in K. cbn [cells_size csize Nat.add length] in K.
      replace (S1c + Z.of_nat (344 + (Z.to_nat KGc + 0 + 104))) with (bv_unsigned sp) in K by (unfold KG; change (rp_s1 (bv_unsigned sp)) with S1c; clear - Q2; lia). exact K. }
    assert (XP13q : xpres H Lall S1c WX m1 m3).
    { eapply (xpres_of_munch_gen H); [exact MU13| exact WM13|]. intros a' Ha [_ HXa]. apply ECH_AC14_b2b.outside_of_not_rin. exact HXa. }
    assert (XP13 : xpres H LB (bv_unsigned sp) (XSq ++ XFc) m1 m3).
    { eapply (xpres_of_munch_gen H); [exact MU13| exact WM13|]. intros a' Ha [HC HXa]. subst WX. cbn.
      assert (HXb : ~ rin_ivs (XSFc ff fp) a') by (intros K; apply HXa; apply rin_ivs_app; left; exact (INCq a' K)).
      unfold XSF in HXb. cbn [rin_ivs fst snd app] in HXb. change (fsz 6) with 4096 in HXb. change (fshn 6) with 512 in HXb. unfold AFS_STACK.
      split; [clear - HXb; lia|]. split; [intros K; eapply ((RCI client_not_frame) _ _ _ _ a' HP SUB0 HC); clear - K Q2 CEIL LO STK0; lia|].
      split; [clear - HXb; lia|]. split; [clear - HXb; lia| exact I]. }
    assert (AVW : forall b, In b Lall -> avoids WX (blk_addr b) (blk_size b) /\ shavoids WX (blk_addr b) (blk_size b)).
    { intros b Hb. destruct (BWb b Hb) as [K1 K2]. pose proof (BRS b Hb) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). split; [exact K1|].
      unfold shavoids. pose proof (disjoint_of_winX WX (blk_addr b) (blk_size b) ltac:(clear - E1; lia) E3 ltac:(unfold AAPP_HI; clear - E5 ACB; lia) K2) as DJ.
      apply Forall_forall. intros iv Hiv. exact (djF_inv _ _ _ _ DJ Hiv). }
    assert (STin : forall b, In b (blocks_STORE st S') -> In b Lall).
    { intros b Hb. pose proof (Permutation_in _ SPM1 Hb) as [<-|Hb']; [apply SLB; exact (proj1 (proj2 SO))| unfold Lall; apply in_or_app; right; apply in_or_app; left; exact Hb']. }
    eapply (rp_postN m3 msF4 mo4 s1' rv NB S' M' LE XSq); [exact VIS4| exact RV| exact KREL4| | exact MI3| exact AC3| exact STK3| | | | | exact LM1 || idtac| exact STEP1| exact NEW1| exact CTX1| exact EC1| exact EB1
      | | | | | | exact SID1| exact SPM1| exact SND1| exact DNB1| exact RFS3| exact FSq| eapply (xpres_trans H); [exact XP1| exact XP13]| exact AL1].
    - eapply (ah_mpres_trans H HH); [| exact MP4]. eapply (ah_mpres_trans H HH); [| exact MP3]. eapply (ah_mpres_trans H HH); [exact MP1| exact MP2].
    - eapply stack0_transport; [exact ST01| exact MU13| exact WM13| exact S0K].
    - eapply rw_cells_transport; [exact ERR1| exact MU13| exact WM13|]. subst WX. unfold AFS_STACK. cbn -[Z.add Z.mul Z.sub Z.opp errno_addr sh].
      clear - ERNG FF1 CEIL LO STK0 Q2 ACB FP1 SHL W1 S0. lia.
    - eapply (ah_rauxv_frame H HH); [exact AUX1| exact MU13| exact WM13| apply (CW LB)].
    - eapply (ah_RHEAP_frame H HH); [exact HP1| exact MU13| exact WM13| apply CW].
    - (* [comment removed for export] *)
      eapply (LIBMID_xfs0 H HH s1' m1 (LE ++ LIB) Lall S1c WX m1 m3 M' x); [exact HP1| exact LM1| rewrite CTX1; exact CTX| exact XP13q| | | exact FW].
      + intros b Hb. unfold Lall. apply in_or_app. right. apply in_or_app; right. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; exact (SUBL _ Hb)].
      + intros b Hb. unfold Lall. apply in_or_app. left. exact Hb.
    - eapply (AMEMBIO_munch H); [exact MBO1| exact MU13| exact WM13|].
      apply Forall_forall. intros iv Hiv. apply Forall_forall. intros b Hb.
      assert (HbL : In b Lall) by (apply SLB; rewrite (mb_static_blocks mb R R' MST1) in Hb; destruct MBO as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _); unfold blocks_MEMBIO in Hb; destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption).
      exact (proj1 (Forall_forall _ _) (proj1 (BWb b HbL)) iv Hiv).
    - destruct MSH1 as (X1 & X2 & X3 & X4). pose proof MBO1 as MBq. destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _). unfold MEMBIO_shad.
      assert (TADq : forall q Aq nq, In (q, Aq, nq) LB -> addressable m1 Aq nq -> addressable m3 Aq nq).
      { intros q Aq nq Hq AD. pose proof (BRS _ (SLB _ Hq)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E3, E5.
        eapply addressable_acrossX; [exact AD| exact MU13| exact WM13| clear - E1; lia| unfold AAPP_HI; clear - E5 ACB; lia| exact (proj2 (BWb _ (SLB _ Hq)))]. }
      split; [| split; [| split]]; [exact (TADq _ _ _ J1 X1)| exact (TADq _ _ _ J2 X2)| exact (TADq _ _ _ J3 X3)| exact (TADq _ _ _ J4 X4)].
    - (* [comment removed for export] *)
      pose proof MBO as MBq. destruct MBq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LENR & BUFP & BUFH & _).
      destruct (Z.eq_dec (mb_len R) 0) as [L0Z|LNZ].
      + assert (DN : ds = []) by (destruct ds; [reflexivity| unfold zlength in DSL; cbn in DSL; exfalso; clear - DSL L0Z; lia]). rewrite DN. apply bytes_at_nil.
        clear - BUFP BUFH ACB L0Z. lia.
      + destruct (PAYL ltac:(clear - LNZ LENR; lia)) as [pD [PIN _]].
        destruct (BWb _ (SLB _ PIN)) as [BWP _]. cbn [blk_addr blk_size fst snd] in BWP.
        eapply bytes_at_transport; [exact DS1| exact MU13|]. unfold zlength in DSL. rewrite DSL.
        clear - BWP. induction WX as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv BWP) as K. cbn in K. split; [lia| exact (IH (Forall_inv_tail BWP))].
    - eapply (STOREobj_frameX H (NB ++ LE ++ LB) S1c WX m1 m3); [exact SO1| | intros b Hb; exact (proj1 (AVW b (STin b Hb)))].
      eapply (xpres_weaken H); [exact XP13q| apply Z.le_refl| intros b Hb; unfold Lall; apply in_or_app; right; exact Hb| intros q Hq; exact Hq].
    - eapply (STORE_shad_frameX H (NB ++ LE ++ LB) Lall S1c WX m1 m3); [exact SSH1| exact SO1| exact XP13q|].
      intros b Hb. split; [exact (STin b Hb)| exact (AVW b (STin b Hb))].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rc_stackF : CFREE_STACK + 464 <= READCFG_STACK M /\ AFS_STACK + 464 <= READCFG_STACK M.
  Proof. clear. pose proof (rc_stack M) as (_ & _ & _ & K1 & K2). exact (conj K1 K2). Qed.

  Lemma rp_errl : DCT rp_errl_stmt.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    unfold rp_errl_stmt. intros NB S' M' LE fr1 fr3 wee v192 v200 v208 v224 v232 tpl um uf m1 s1' msF1 mo1 rv u0 u1 u2 a1w a2w b3 b4 b5 b6 b7 s4w s6w s9w u3 u4 u5 u6.
    intros DW RV DNB UFB UMB VIS1 KREL1 MP1.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof rc_stackF as [STKF STKA].
    assert (AS1 : aceil <= S1c) by (clear - CEIL LO STK0 Q2; lia).
    assert (CHBx : forall fp' ra', In (fp', ra') CH1c -> S1c + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    assert (SHF : Z.shiftr ff 3 + ASHB = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    pose proof (errph_bytes_range (mid_err M)) as [EBR ECR].
    pose proof DW as (_ & _ & STP & NEW & CTX1 & EC & EB & _). pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    (* [comment removed for export] *)
    eapply (BTFREE NB S' M' LE fr1 fr3 wee v192 v200 v208 v224 v232 tpl um uf m1 s1' msF1 mo1 AFM_ERRL_R1);
      [exact DW| unfold AFM_ERRL_R1; clear; lia| reflexivity| exact DNB
      | apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 17 (apply in_or_app; right); apply in_or_app; left; exact He
      | clear - UFB; lia| exact UMB| exact VIS1| exact KREL1| exact MP1|].
    intros m2 s2' msF2 mo2 errv2 uf2 XS2 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6.
    intros VIS2 KREL2 MP2 HP2 MI2 AC2 ST2 STK2 ERR2 AUX2 RFS2 LM2 SO2 SSH2 MBO2 MSH2 DSm2 [jb CBb2] ADb2 [ja CBa2] ADa2 FR0 FR1 FR2 FR3 FRG FRS FF2' FSH2 CHN2 FXS2 INC2 XP2 LED2 UF2.
    pose proof LM2 as (IM2 & MFq2 & _ & _ & _ & _ & _ & _ & GM2 & _).
    pose proof DW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SO1 & SSH1 & SID & SPM & SND & _).
    pose proof (ah_costs H HH) as (CM0 & CMmono & CF0 & CFmono & CMadd & CFadd).
    pose proof CBb2 as [[WFb _] _]. cbn in WFb. destruct WFb as (LB1 & LJ1 & _).
    pose proof CBa2 as [[WFa _] _]. cbn in WFa. destruct WFa as (LA1 & LJA1 & _).
    pose proof DSL as DSL1. unfold zlength in DSL1. pose proof NBR as NBRq. unfold zlength in NBRq.
    (* [comment removed for export] *)
    pose proof (rw_cells_merge asegs m2 Bb [] [CB (length bs) bs; CB (Z.to_nat nB - length bs) jb] [] ltac:(cbn [app]; exact CBb2)) as CHb. cbn [app cells_size cells_bytes csize cbytes Nat.add] in CHb. rewrite app_nil_r in CHb.
    replace (length bs + (Z.to_nat nB - length bs + 0))%nat with (Z.to_nat nB) in CHb by (clear - NBRq LB1; lia).
    pose proof (rw_cells_merge asegs m2 A [] [CB (Z.to_nat (mb_len R)) ds; CB (Z.to_nat (nA - mb_len R)) ja] [] ltac:(cbn [app]; exact CBa2)) as CHa. cbn [app cells_size cells_bytes csize cbytes Nat.add] in CHa. rewrite app_nil_r in CHa.
    replace (Z.to_nat (mb_len R) + (Z.to_nat (nA - mb_len R) + 0))%nat with (Z.to_nat nA) in CHa by (clear - NAR; lia).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply aerrl2; exact MI2|]. intros msF3 mo3 KREL3 MP3 VIS3. cbn beta in VIS3.
    assert (HP2' : as_RHEAP H s2' ((pbin, Bb, nB) :: mid_errblocks M' ++ NB ++ (p, A, nA) :: LE ++ LB) m2).
    { eapply PERM; [exact HP2|]. rewrite !(app_assoc (mid_errblocks M') NB). apply Permutation_sym. apply Permutation_middle. }
    pose proof (ah_nodup H HH _ _ _ HP2') as ND2. cbn [map] in ND2. apply List.NoDup_cons_iff in ND2. destruct ND2 as [NIB _].
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (s := s2') (p := pbin) (A := Bb) (n := nB) (errv := errv2) (CH := CH1c) (bs := bs ++ jb); clear CF.
      all: try first [exact VIS3| exact HP2'| exact KREL3| exact AUX2| exact MI2| exact CEIL| exact AC2| exact CHN2| exact CHb| exact ADb2| exact IM2| exact GM2| exact ERR2].
      all: lazymatch goal with
           | |- In _ _ => left; reflexivity
           | |- _ = Z_to_bv _ _ => reflexivity
           | |- Z_to_bv 64 ATP = _ => reflexivity
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST2
           | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKF Q2; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact (CHBx _ _ Hin)
           | |- pf_ok _ _ _ _ => unfold AERRL_R2; rewrite unsigned_lit by (clear; lia); apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 18 (apply in_or_app; right); apply in_or_app; left; exact He
           | |- as_Cf H _ <= as_AL H _ => pose proof ((RCI LEDGER_pay) s2' um uf2 0 nB LED2 ltac:(clear; lia) ltac:(clear - NBRq; lia) ltac:(clear - UMB; lia) ltac:(unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBRq; clear - UFB UF2 NBRq; lia)) as PAYq;
                                             pose proof (CM0 0 ltac:(clear; lia)) as CMz; clear - PAYq CMz; lia
           | |- ?G => idtac "ERRL_CF1_LEFT" G
           end. }
    clear CF. intros [msF4 mo4] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & s4' & VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & XP4 & HP4 & IM4 & GM4 & AL4).
    rewrite (proj1 (ah_lb_remove H HH)) in XP4, HP4 by exact NIB.
    rewrite (unsigned_lit S1c) in ST4, XP4 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    assert (LED4 : LEDGERc s4' um (uf2 + nB)).
    { pose proof ((RCI LEDGER_step) s2' s4' um uf2 0 nB LED2 ltac:(clear; lia) ltac:(clear - NBRq; lia)) as K. rewrite Z.add_0_r in K. apply K. pose proof (CM0 0 ltac:(clear; lia)) as CMz. clear - AL4 CMz. lia. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply aerrl3; exact MI4|]. intros msF5 mo5 KREL5 MP5 VIS5. cbn beta in VIS5.
    assert (HP4' : as_RHEAP H s4' ((p, A, nA) :: mid_errblocks M' ++ NB ++ LE ++ LB) m4).
    { eapply PERM; [exact HP4|]. rewrite !(app_assoc (mid_errblocks M') NB). apply Permutation_sym. apply Permutation_middle. }
    pose proof (ah_nodup H HH _ _ _ HP4') as ND4. cbn [map] in ND4. apply List.NoDup_cons_iff in ND4. destruct ND4 as [NIA _].
    assert (XP24 : xpres H ((p, A, nA) :: mid_errblocks M' ++ NB ++ LE ++ LB) S1c [] m2 m4).
    { eapply (xpres_weaken H); [exact XP4| apply Z.le_refl| | intros q Hq; exact Hq].
      intros b [<-|Hb]; [apply in_or_app; right; apply in_or_app; right; left; reflexivity|].
      apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; right; apply in_or_app; left; exact Hb|].
      apply in_or_app; right; apply in_or_app; right; right; exact Hb. }
    assert (CHa4 : rw_cells asegs m4 A [CB (Z.to_nat nA) (ds ++ ja)]).
    { eapply (xpres_rw_cells' H); [exact XP24| exact CHa| right; right; left; exists (p, A, nA); split; [left; reflexivity| cbn; clear - NAR; lia]| apply Forall_nil]. }
    assert (ADa4 : addressable m4 A nA).
    { pose proof (ah_blocks H HH _ _ _ _ HP4' ltac:(left; reflexivity)) as (_ & _ & _ & _ & E5 & _). cbn [blk_addr blk_size fst snd] in E5.
      eapply (addressable_xpres_blkX H ((p, A, nA) :: mid_errblocks M' ++ NB ++ LE ++ LB) m2 m4 S1c [] p); [left; reflexivity| unfold AAPP_HI; clear - E5 ACB; lia| exact ADa2| exact XP24| unfold shavoids; apply Forall_nil]. }
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_seq H HH).
    { eapply CF with (lo := lo) (B := B) (s := s4') (p := p) (A := A) (n := nA) (errv := errv2) (CH := CH1c) (bs := ds ++ ja); clear CF.
      all: try first [exact VIS5| exact HP4'| exact KREL5| exact AUX4| exact MI4| exact CEIL| exact AC4| exact CHa4| exact ADa4| exact IM4| exact GM4| exact ERR4].
      all: lazymatch goal with
           | |- In _ _ => left; reflexivity
           | |- _ = Z_to_bv _ _ => reflexivity
           | |- Z_to_bv 64 ATP = _ => reflexivity
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - SPB Q2; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact ST4
           | |- lo <= _ => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - LO STKF Q2; lia
           | |- _ mod 16 = 0 => rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia
           | |- as_chain _ _ _ _ => eapply (chain_via_xpres_off H HH _ S1c []); [exact CHN2| exact XP4| exact CHBx| apply Forall_nil]
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); exact (CHBx _ _ Hin)
           | |- pf_ok _ _ _ _ => unfold AERRL_R3; rewrite unsigned_lit by (clear; lia); apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 19 (apply in_or_app; right); exact He
           | |- as_Cf H _ <= as_AL H _ => pose proof ((RCI LEDGER_pay) s4' um (uf2 + nB) 0 nA LED4 ltac:(clear; lia) ltac:(clear - NAR; lia) ltac:(clear - UMB; lia) ltac:(unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBRq; clear - UFB UF2 NBRq NAR; lia)) as PAYq;
                                             pose proof (CM0 0 ltac:(clear; lia)) as CMz; clear - PAYq CMz; lia
           | |- ?G => idtac "ERRL_CF2_LEFT" G
           end. }
    clear CF. intros [msF6 mo6] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (x0 & x1 & x2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & x3 & x4 & x5 & x6 & m6 & s6' & VIS6 & KREL6 & MP6 & MI6 & AC6 & ST6 & ERR6 & AUX6 & XP6 & HP6 & IM6 & GM6 & AL6).
    rewrite (proj1 (ah_lb_remove H HH)) in XP6, HP6 by exact NIA.
    rewrite (unsigned_lit S1c) in ST6, XP6 by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    assert (LED6 : LEDGERc s6' um (uf2 + nB + nA)).
    { pose proof ((RCI LEDGER_step) s4' s6' um (uf2 + nB) 0 nA LED4 ltac:(clear; lia) ltac:(clear - NAR; lia)) as K. rewrite Z.add_0_r in K. apply K. pose proof (CM0 0 ltac:(clear; lia)) as CMz. clear - AL6 CMz. lia. }
    (* [comment removed for export] *)
    set (Lr := mid_errblocks M' ++ NB ++ LE ++ LB) in *.
    assert (XP26 : xpres H Lr S1c [] m2 m6).
    { eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XP24| apply Z.le_refl| intros b Hb; right; exact Hb| intros q Hq; exact Hq]| exact XP6]. }
    assert (SLr : forall b, In b LB -> In b Lr) by (intros b Hb; unfold Lr; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
    assert (BRS : forall b, In b Lr -> ablock_range H (blk_addr b) (blk_size b)) by (intros b Hb; exact (ah_blocks H HH _ _ _ _ HP6 Hb)).
    assert (T26s : forall A' cs, rw_cells asegs m2 A' cs -> S1c <= A' -> rw_cells asegs m6 A' cs).
    { intros A' cs RC HA. eapply (xpres_rw_cells' H); [exact XP26| exact RC| left; exact HA| apply Forall_nil]. }
    assert (T26b : forall b A' cs, In b Lr -> blk_addr b <= A' -> A' + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b -> rw_cells asegs m2 A' cs -> rw_cells asegs m6 A' cs).
    { intros b A' cs Hb HA HB RC. eapply (xpres_rw_cells' H); [exact XP26| exact RC| right; right; left; exists b; split; [exact Hb| split; [exact HA| exact HB]]| apply Forall_nil]. }
    assert (TAD : forall q Aq nq, In (q, Aq, nq) Lr -> addressable m2 Aq nq -> addressable m6 Aq nq).
    { intros q Aq nq Hb AD. pose proof (BRS _ Hb) as (_ & _ & _ & _ & E5 & _). cbn [blk_addr blk_size fst snd] in E5.
      eapply (addressable_xpres_blkX H Lr m2 m6 S1c [] q); [exact Hb| unfold AAPP_HI; clear - E5 ACB; lia| exact AD| exact XP26| unfold shavoids; apply Forall_nil]. }
    (* [comment removed for export] *)
    destruct FF2' as [lb FF2'].
    assert (FRM6 : rw_cells asegs m6 ff (arp_fframe S1c (le8 (wz tpl) ++ fj24 ++ [lb] ++ tpb ++ fj128) n fj2 fp)).
    { assert (FF6' : rw_cells asegs m6 ff (dffc tpl lb)).
      { eapply (xpres_rw_cells' H); [exact XP26| exact FF2'| right; right; right; right; left; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; unfold AFS_SIZE; clear - FF5 FF6; lia| apply Forall_nil]. }
      pose proof FF6' as [[WF _] _]. unfold dff, arp_fframe2 in WF. cbn in WF.
      unfold dff, arp_fframe2 in FF6'. unfold arp_fframe. eapply arw_cells_recut; [exact FF6'| cbn; rewrite !length_app; cbn [length]; rewrite ?length_app; clear - WF; repeat split; try tauto; lia| cbn [cells_bytes cbytes app]; rewrite <- !app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply aerrl4; exact MI6|]. intros msF7 mo7 KREL7 MP7 VIS7. cbn beta in VIS7.
    eapply (rp_exitN m6 msF7 mo7 s6' rv NB S' M' LE (le8 (wz tpl) ++ fj24 ++ [lb] ++ tpb ++ fj128) ([CB 16 jz] ++ fr1 ++ dsg2c wee v192 v200 v208 v224 v232 ++ fr3) XS2).
    all: lazymatch goal with
    | |- as_VIS _ _ _ = _ => exact VIS7
    | |- _ = 0 \/ _ = 1 => exact RV
    | |- as_AKREL _ _ _ => exact KREL7
    | |- as_MPRES _ _ _ => eapply (ah_mpres_trans H HH); [exact MP2|]; eapply (ah_mpres_trans H HH); [exact MP3|]; eapply (ah_mpres_trans H HH); [exact MP4|]; eapply (ah_mpres_trans H HH); [exact MP5|]; eapply (ah_mpres_trans H HH); [exact MP6| exact MP7]
    | |- mem_inv _ _ => exact MI6
    | |- ACONST _ => exact AC6
    | |- stk _ _ _ _ => exact ST6
    | |- stack0 _ _ _ => eapply (stack0_xpres H); [exact XP26| exact STK2| apply Forall_nil]
    | |- cells_size _ = _ => pose proof DW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SZ1 & _ & _ & SZ3 & _);
                             rewrite !cells_size_app, SZ1, SZ3; reflexivity
    | |- rw_cells asegs _ S1c _ =>
        pose proof DW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SZ1 & _ & _ & SZ3 & _);
        apply (proj2 (rw_cells_app asegs m6 S1c [CB 16 jz] _)); split; [exact (T26s _ _ FR0 ltac:(apply Z.le_refl))|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app asegs m6 _ fr1 _)); split; [exact (T26s _ _ FR1 ltac:(clear; lia))|]; rewrite SZ1;
        apply (proj2 (rw_cells_app asegs m6 _ (dsg2c wee v192 v200 v208 v224 v232) _)); split; [replace (S1c + Z.of_nat 16 + Z.of_nat 128) with (S1c + 144) by (clear; lia); exact (T26s _ _ FR2 ltac:(clear; lia))|];
        unfold dsg2, arp_sg2; cbn [cells_size csize Nat.add]; replace (S1c + Z.of_nat 16 + Z.of_nat 128 + 96) with (S1c + 240) by (clear; lia); exact (T26s _ _ FR3 ltac:(clear; lia))
    | |- rw_cells asegs _ (S1c + 344) _ => exact (T26s _ _ FRG ltac:(clear; lia))
    | |- rw_cells asegs _ (bv_unsigned sp + -104) _ => exact (T26s _ _ FRS ltac:(clear - Q2; lia))
    | |- rw_cells asegs _ _ (arp_fframe _ _ _ _ _) => exact FRM6
    | |- as_RFS _ _ _ => eapply (ECH_AKit.RFS_via_xpres H HH); [exact RFS2| exact XP26| apply Forall_nil]
    | |- rw_cells asegs _ (errno_addr _) _ => exact ERR6
    | |- as_rauxv_ok _ _ _ => exact AUX6
    | |- as_RHEAP _ _ _ _ => exact HP6
    | |- LIBMID _ _ _ => eapply (LIBMID_xpres0 H (LE ++ LIB) Lr S1c m2 m6 M' x); [exact LM2| rewrite CTX1; exact CTX| exact XP26| | intros b Hb; apply in_or_app; left; exact Hb];
                         intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; exact (SUBL _ Hb)]
    | |- mid_step _ _ => exact STP
    | |- mid_newlib_ok _ _ _ => exact NEW
    | |- mid_ctx _ = _ => exact CTX1
    | |- Z.of_nat (length (mid_errblocks _)) <= _ => exact EC
    | |- lb_bytes (mid_errblocks _) <= _ => exact EB
    | |- MEMBIO _ _ _ _ _ =>
        eapply (AMEMBIO_xpres H LB Lr S1c [] m2 m6); [exact MBO2| intros b Hb; apply SLr; destruct MBO2 as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _); unfold blocks_MEMBIO in Hb; destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption| exact XP26| apply Forall_nil]
    | |- MEMBIO_shad _ _ _ =>
        destruct MSH2 as (X1 & X2 & X3 & X4); pose proof MBO2 as MBq; destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _); unfold MEMBIO_shad;
        split; [| split; [| split]]; [exact (TAD _ _ _ (SLr _ J1) X1)| exact (TAD _ _ _ (SLr _ J2) X2)| exact (TAD _ _ _ (SLr _ J3) X3)| exact (TAD _ _ _ (SLr _ J4) X4)]
    | |- bytes_at asegs _ (mb_buf R) ds =>
        destruct (PAYL ltac:(clear - NAR; lia)) as [pD [PIN _]];
        eapply (xpres_bytes_at' H); [exact XP26| exact DSm2| right; right; left; exists (pD, mb_buf R, mb_len R); split; [exact (SLr _ PIN)| cbn; rewrite DSL1; clear; lia]| apply Forall_nil]
    | |- STOREobj _ _ _ _ => eapply (STOREobj_frameX H (NB ++ LE ++ LB) S1c [] m2 m6); [exact SO2| eapply (xpres_weaken H); [exact XP26| apply Z.le_refl| intros b Hb; apply in_or_app; right; exact Hb| intros q Hq; exact Hq]| intros b Hb; unfold avoids; apply Forall_nil]
    | |- STORE_shad _ _ _ => eapply (STORE_shad_frameX H (NB ++ LE ++ LB) Lr S1c [] m2 m6); [exact SSH2| exact SO2| exact XP26|];
                             intros b Hb; pose proof (Permutation_in _ SPM Hb) as [<-|Hb']; [split; [apply SLr; exact (proj1 (proj2 SO))| split; [unfold avoids| unfold shavoids]; apply Forall_nil]| split; [apply in_or_app; right; apply in_or_app; left; exact Hb'| split; [unfold avoids| unfold shavoids]; apply Forall_nil]]
    | |- es_id _ = _ => exact SID
    | |- Permutation _ _ => exact SPM
    | |- List.NoDup _ => exact SND
    | |- dnb _ => exact DNB
    | |- Forall (fs_scratch H LF) _ => exact FXS2
    | |- forall q, rin_ivs _ q -> rin_ivs _ q => exact INC2
    | |- xpres _ LB _ _ m _ =>
        eapply (xpres_trans H); [exact XP2|];
        intros a' Ha [Ca HXa]; apply XP26; [exact Ha|]; split; [eapply (aclient_addr_weaken H); [exact Ca| clear - Q2; lia| exact SLr]| intros []]
    | |- as_AL H _ >= _ => eapply ((RCI LEDGER_post) s6' um (uf2 + nB + nA)); [exact LED6| exact UMB| unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBRq; clear - UFB UF2 NBRq NAR; lia]
    | |- ?G => idtac "ERRL_LEFT" G
    end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rp_efree : forall Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m1 s1' msF1 mo1 (ee : Z) (oe : option entrep) (rax : Z)
      (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word) (Q : config -> Prop),
    adwkGc Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m1 s1' ->
    match oe with None => ee = 0 /\ Lx = [] | Some E => ENTRYobj (drestc Lx NB LE) m1 ee E /\ ENTRY_shad m1 ee E /\ Permutation (blocks_ENTRY ee E) Lx end ->
    0 <= rax < 2^64 -> rax mod 2 = 0 -> pf_ok (as_TR H) PF_entryfree rax CH1c ->
    uf + lb_bytes Lx <= DECODE_CUM_BYTES -> um <= DECODE_CUM_BYTES ->
    as_VIS H s1' msF1 = MS (mkR (Z_to_bv 64 rax) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 ee) b1 b2 b3 b4 b5 b6 b7
                                s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                        F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m1 (seg_rom asegs) ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    (forall m2 (s2' : as_St H) msF2 mo2 (v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 : word),
       adwkGc [] NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um (uf + lb_bytes Lx) m2 s2' ->
       as_VIS H s2' msF2 = MS (mkR (Z_to_bv 64 rax) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) v0 v1 v2 sp (Z_to_bv 64 S1c) c0 c1 c2 c3 c4 c5 c6 c7
                                   s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w v3 v4 v5 v6)
                           F (ret_pc (Z_to_bv 64 rax)) fc None m2 (seg_rom asegs) ->
       as_AKREL H s2' (mkCfg msF2 mo2) -> as_MPRES H mo mo2 -> as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
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
      destruct (f14_entry_cost_bound H HH _ _ _ _ EO LX0) as [LXN ECB]. rewrite LBE in LXN, ECB.
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
      eapply ((DCJ adwkG_x) Lx [] NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf um (uf + lb_bytes Lx) m1 s1' m2 s2' errv1);
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
      destruct FF1 as [lb1 FF1]. pose proof FF1 as [[WFf _] _]. unfold dff, arp_fframe2 in WFf. cbn in WFf.
      eapply (K m2 s1' msF2 mo2 v0 v1 v2 (Z_to_bv 64 0) c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6); [| exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)].
      cbn [lb_bytes fold_right]. rewrite Z.add_0_r.
      eapply ((DCJ adwkG_w) [] NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m1 s1' m2 [(lo, S1c)] fr1 wee v192 v200 v208 v224 v232 fr3 tpl lb1 shb shb2 shd);
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
  Lemma rc_stackT : RAISE_STACK (mid_err M) + 464 <= READCFG_STACK M /\ AFS_STACK + 464 <= READCFG_STACK M.
  Proof. clear. pose proof (rc_stack M) as (K1 & _ & _ & _ & K2). exact (conj K1 K2). Qed.

  Local Tactic Notation "pf_entry_seg" integer(k) :=
    (apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left;
     unfold PF_entry; do k (apply in_or_app; right); first [apply in_or_app; left; exact He| exact He]).

  (* [comment removed for export] *)
  Lemma rp_tailXc : forall Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl um uf m1 s1' msF1 mo1 (ee : Z) (oe : option entrep)
      (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w u3 u4 u5 u6 : word),
    adwkGc Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m1 s1' ->
    match oe with None => ee = 0 /\ Lx = [] | Some E => ENTRYobj (drestc Lx NB LE) m1 ee E /\ ENTRY_shad m1 ee E /\ Permutation (blocks_ENTRY ee E) Lx end ->
    dnb NB -> dbud H (drestc Lx NB LE) M' ERRDEBUG_BYTES 2 ->
    um + errph_bytes (mid_err M') + ERRDEBUG_BYTES <= DECODE_CUM_BYTES -> uf + errph_bytes (mid_err M') + lb_bytes Lx + ERRDEBUG_BYTES + 8192 <= DECODE_CUM_BYTES ->
    as_VIS H s1' msF1 = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) b0 b1 b2 b3 b4 b5 b6 b7
                                (Z_to_bv 64 A) (Z_to_bv 64 SH) s4w s5w s6w (Z_to_bv 64 Bb) (Z_to_bv 64 ff) (Z_to_bv 64 ee) (Z_to_bv 64 ff) (Z_to_bv 64 bt) u3 u4 u5 u6)
                        F (Z_to_bv 64 ADF_TX) fc None m1 (seg_rom asegs) ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    as_SR H POSTc (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    intros until u6. intros DW OE DNB BD UMB UFB VIS1 KREL1 MP1.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    assert (LX0 : 0 <= lb_bytes Lx).
    { pose proof DW as (HP1 & _). apply lb_bytes_nonneg_s. apply Forall_forall. intros b Hb.
      pose proof (ah_blocks H HH _ _ _ _ HP1 ltac:(apply in_or_app; right; unfold drest; apply in_or_app; left; exact Hb)) as (_ & _ & E3 & _). exact E3. }
    pose proof DW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & _).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply aft_x1; exact MI1|]. intros msF2 mo2 KREL2 MP2 VIS2. cbn beta in VIS2.
    eapply (rp_efree Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) _ (poison_bytes 256 0xf8) um uf m1 s1' msF2 mo2 ee oe ADF_TX_R0);
      [exact DW| exact OE| unfold ADF_TX_R0; clear; lia| reflexivity| pf_entry_seg 12| clear - UFB EBR'; unfold ERRDEBUG_BYTES in *; lia| clear - UMB EBR'; unfold ERRDEBUG_BYTES in *; lia
      | exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)|].
    intros m3 s3' msF3 mo3 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DW3 VIS3 KREL3 MP3.
    pose proof DW3 as (_ & _ & STP3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI3 & _).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply aft_x2; exact MI3|]. intros msF4 mo4 KREL4 MP4 VIS4. cbn beta in VIS4.
    eapply ((DCJ adwk_raise) [] NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) _ (poison_bytes 256 0xf8) um (uf + lb_bytes Lx) m3 s3' msF4 mo4 ARP_FUNC S_ARP_FUNC K_ARP_FUNC ADF_TX_R1 ADF_TX_R2 ADF_TX_R3 637 AR_INTERNAL_ERROR);
      [exact R_ARP_FUNC| discriminate| rewrite S_ARP_FUNC_len; clear; lia| unfold ARP_FUNC; clear; lia| exact DW3| exact VIS4| exact KREL4| exact (ah_mpres_trans H HH _ _ _ MP3 MP4)
      | destruct BD as [B1 B2]; unfold dbud; rewrite (drest_app LB p A nA pbin Bb nB TB Lx NB LE), lb_bytes_app, length_app, Nat2Z.inj_add in B1, B2 |- * || idtac; unfold dbud in *; split; [clear - B1 LX0; rewrite ?(drest_app LB p A nA pbin Bb nB TB Lx NB LE), ?lb_bytes_app in *; lia| clear - B2; rewrite ?(drest_app LB p A nA pbin Bb nB TB Lx NB LE), ?length_app, ?Nat2Z.inj_add in *; lia]
      | clear - UMB; lia| clear - UFB LX0; lia
      | apply pf_sitec; intros e He; apply (pf_shift_mono14 _ _ _ (PF_errnew_mstep14 M M' STP3)) in He;
        unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left; unfold PF_entry, pf_raise; do 15 (apply in_or_app; right); apply in_or_app; left; exact He
      | apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left; unfold PF_entry, pf_raise; do 15 (apply in_or_app; right); apply in_or_app; right; apply in_or_app; left; exact He
      | apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left; unfold PF_entry, pf_raise; do 15 (apply in_or_app; right); apply in_or_app; right; apply in_or_app; right; exact He
      | clear; lia| unfold AR_INTERNAL_ERROR; clear; lia
      | unfold ADF_TX_R1; clear; lia| reflexivity| unfold ADF_TX_R2; clear; lia| reflexivity| unfold ADF_TX_R3; clear; lia| reflexivity
      | apply arglue_of_arp; exact aft_x3| apply arglue_of_arp; exact aft_x4|].
    intros u0' u1' u2' c0' c1' c2' c3' c4' c5' c6' c7' u3' u4' u5' u6' msF5 m5 mo5 s5' LEn M'' c XS5 VIS5 KREL5 MP5 DW5 STEP5 ME5 DL5 FXS5 XP5.
    pose proof DW5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI5 & _).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5| eapply aft_x5; exact MI5|]. intros msF6 mo6 KREL6 MP6 VIS6. cbn beta in VIS6.
    pose proof rp_errl as RE. unfold rp_errl_stmt in RE.
    eapply (RE NB S' M'' (LEn ++ LE) fr1 fr3 wee v192 v200 v208 v224 v232 tpl (um + (errph_bytes (mid_err M') + ERRDEBUG_BYTES)) (uf + lb_bytes Lx + (errph_bytes (mid_err M') + ERRDEBUG_BYTES)) m5 s5' msF6 mo6 0);
      [exact DW5| left; reflexivity| exact DNB| clear - UFB LX0; lia| clear - UMB; lia| exact VIS6| exact KREL6| exact (ah_mpres_trans H HH _ _ _ MP5 MP6)].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_tailYn : forall NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl um uf m1 s1' msF1 mo1 (line reason : Z)
      (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s6w u3 u4 u5 u6 : word),
    adwkGc [] NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m1 s1' ->
    dnb NB -> dbud H (drestc [] NB LE) M' (2 * ERRDEBUG_BYTES) 4 -> 0 <= line < 2^31 -> 0 < reason < 2^23 ->
    um + errph_bytes (mid_err M') + 2 * ERRDEBUG_BYTES <= DECODE_CUM_BYTES -> uf + errph_bytes (mid_err M') + 2 * ERRDEBUG_BYTES + 8192 <= DECODE_CUM_BYTES ->
    as_VIS H s1' msF1 = MS (mkR (Z_to_bv 64 ADF_TY_R1) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) b0 b1 b2 b3 b4 b5 b6 b7
                                (Z_to_bv 64 A) (Z_to_bv 64 SH) (Z_to_bv 64 reason) (Z_to_bv 64 line) s6w (Z_to_bv 64 Bb) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 ff) (Z_to_bv 64 bt) u3 u4 u5 u6)
                        F (Z_to_bv 64 P_ERR_new) fc None m1 (seg_rom asegs) ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    as_SR H POSTc (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    intros until u6. intros DW DNB BD LNR REAS UMB UFB VIS1 KREL1 MP1.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    pose proof DW as (_ & _ & STP & _).
    eapply ((DCJ adwk_raise) [] NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) _ (poison_bytes 256 0xf8) um uf m1 s1' msF1 mo1 AFUNC_DF S_AFUNC_DF K_AFUNC_DF ADF_TY_R1 ADF_TY_R2 ADF_TX line reason);
      [exact R_AFUNC_DF| discriminate| rewrite S_AFUNC_DF_len; clear; lia| unfold AFUNC_DF; clear; lia| exact DW| exact VIS1| exact KREL1| exact MP1
      | destruct BD as [B1 B2]; split; [clear - B1; unfold ERRDEBUG_BYTES in *; lia| clear - B2; lia]
      | clear - UMB; unfold ERRDEBUG_BYTES in *; lia| clear - UFB; unfold ERRDEBUG_BYTES in *; lia
      | apply pf_sitec; intros e He; apply (pf_shift_mono14 _ _ _ (PF_errnew_mstep14 M M' STP)) in He;
        unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left; unfold PF_entry, pf_raise; do 14 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; left; exact He
      | apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left; unfold PF_entry, pf_raise; do 14 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact He
      | apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left; unfold PF_entry, pf_raise; do 14 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact He
      | exact LNR| exact REAS
      | unfold ADF_TY_R1; clear; lia| reflexivity| unfold ADF_TY_R2; clear; lia| reflexivity| unfold ADF_TX; clear; lia| reflexivity
      | apply aft_y2| apply aft_y3|].
    intros u0' u1' u2' c0' c1' c2' c3' c4' c5' c6' c7' u3' u4' u5' u6' msF2 m2 mo2 s2' LEn M'' c XS2 VIS2 KREL2 MP2 DW2 STEP2 ME2 DL2 FXS2 XP2.
    replace (ret_pc (Z_to_bv 64 ADF_TX)) with (Z_to_bv 64 ADF_TX : word) in VIS2 by (symmetry; apply ret_pc_even; [unfold ADF_TX; clear; lia| reflexivity]).
    pose proof (errph_delta_bounds14 _ _ _ DL2) as [DC2 DB2]. rewrite <- ME2 in DC2, DB2.
    assert (EZ : errph_bytes (mid_err M'') = 0 /\ errph_cnt (mid_err M'') = 0) by (rewrite ME2; split; reflexivity). destruct EZ as [EZ1 EZ2].
    eapply (rp_tailXc [] NB S' M'' (LEn ++ LE) fr1 wee v192 v200 v208 v224 v232 fr3 tpl _ _ m2 s2' msF2 mo2 0 None);
      [exact DW2| split; reflexivity| exact DNB| | | | exact VIS2| exact KREL2| exact MP2].
    - destruct BD as [B1 B2].
      assert (EQB : forall LEq, lb_bytes (drestc [] NB LEq) = lb_bytes LEq + lb_bytes (drestc [] NB [])).
      { intros LEq. unfold drest. cbn [app]. rewrite ?lb_bytes_app, ?lb_bytes_cons, ?lb_bytes_app. cbn [lb_bytes fold_right app]. rewrite ?lb_bytes_app. clear; lia. }
      assert (EQC : forall LEq, length (drestc [] NB LEq) = (length LEq + length (drestc [] NB []))%nat).
      { intros LEq. unfold drest. cbn [app]. rewrite ?length_app. cbn [length app]. rewrite ?length_app. cbn [length]. clear; lia. }
      unfold dbud in B1, B2 |- *. rewrite (EQB (LEn ++ LE)), lb_bytes_app. rewrite (EQB LE) in B1. rewrite (EQC (LEn ++ LE)), length_app. rewrite (EQC LE) in B2.
      rewrite ?Nat2Z.inj_add in B2 |- *. unfold ERRDEBUG_BYTES in *. split; [clear - B1 DB2; lia| clear - B2 DC2; lia].
    - cbn [lb_bytes fold_right]. clear - UMB EZ1. unfold ERRDEBUG_BYTES in *. lia.
    - cbn [lb_bytes fold_right]. clear - UFB EZ1. unfold ERRDEBUG_BYTES in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rp_tailY : forall NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl um uf m1 s1' msF1 mo1 (line reason : Z)
      (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s6w u3 u4 u5 u6 : word),
    adwkGc [] NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m1 s1' ->
    dnb NB -> dbud H (drestc [] NB LE) M' (2 * ERRDEBUG_BYTES) 4 -> 0 <= line < 2^31 -> 0 < reason < 2^23 ->
    um + errph_bytes (mid_err M') + 2 * ERRDEBUG_BYTES <= DECODE_CUM_BYTES -> uf + errph_bytes (mid_err M') + 2 * ERRDEBUG_BYTES + 8192 <= DECODE_CUM_BYTES ->
    as_VIS H s1' msF1 = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) b0 b1 b2 b3 b4 b5 b6 b7
                                (Z_to_bv 64 A) (Z_to_bv 64 SH) (Z_to_bv 64 reason) (Z_to_bv 64 line) s6w (Z_to_bv 64 Bb) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 ff) (Z_to_bv 64 bt) u3 u4 u5 u6)
                        F (Z_to_bv 64 ADF_TY) fc None m1 (seg_rom asegs) ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    as_SR H POSTc (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    intros until u6. intros DW DNB BD LNR REAS UMB UFB VIS1 KREL1 MP1.
    pose proof DW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & _).
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply aft_y1; exact MI1|]. intros msF2 mo2 KREL2 MP2 VIS2. cbn beta in VIS2.
    eapply (rp_tailYn NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl um uf m1 s1' msF2 mo2 line reason);
      [exact DW| exact DNB| exact BD| exact LNR| exact REAS| exact UMB| exact UFB| exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_tailZc : forall Lx NB S' M' LE w16 w32 w40 w48 v192 v200 v208 v224 v232 fr3 tpl (shb shb2 : byte) (shd : list byte) um uf m1 s1' msF1 mo1 (ee : Z) (E : entrep)
      (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s2w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word),
    adwkGc Lx NB S' M' LE (dsg1c w16 w32 w40 w48) (wz ee) v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m1 s1' ->
    cells_size fr3 = 104%nat ->
    ENTRYobj (drestc Lx NB LE) m1 ee E -> ENTRY_shad m1 ee E -> Permutation (blocks_ENTRY ee E) Lx ->
    dnb NB -> dbud H (drestc Lx NB LE) M' (2 * ERRDEBUG_BYTES) 4 ->
    um + errph_bytes (mid_err M') + 2 * ERRDEBUG_BYTES <= DECODE_CUM_BYTES -> uf + errph_bytes (mid_err M') + lb_bytes Lx + 2 * ERRDEBUG_BYTES + 8192 <= DECODE_CUM_BYTES ->
    as_VIS H s1' msF1 = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) b0 b1 b2 b3 b4 b5 b6 b7
                                s2w (Z_to_bv 64 SH) s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                        F (Z_to_bv 64 ADF_TZ) fc None m1 (seg_rom asegs) ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    as_SR H POSTc (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    intros until u6. intros DW SZ3 EO ESH PE DNB BD UMB UFB VIS1 KREL1 MP1.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    assert (LX0 : 0 <= lb_bytes Lx).
    { pose proof DW as (HP1 & _). apply lb_bytes_nonneg_s. apply Forall_forall. intros b Hb.
      pose proof (ah_blocks H HH _ _ _ _ HP1 ltac:(apply in_or_app; right; unfold drest; apply in_or_app; left; exact Hb)) as (_ & _ & E3 & _). exact E3. }
    pose proof DW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & _).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply aft_z1 with (q := S1c); [clear - CEIL LO STK0 Q2 LO0; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| unfold dsg2 in FR2; exact FR2| exact MI1]|].
    intros msF2 mo2 KREL2 MP2 VIS2. cbn beta in VIS2.
    eapply (rp_efree Lx NB S' M' LE _ (wz ee) v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m1 s1' msF2 mo2 ee (Some E) ADF_TZ_R1);
      [exact DW| exact (conj EO (conj ESH PE))| unfold ADF_TZ_R1; clear; lia| reflexivity| pf_entry_seg 11| clear - UFB EBR'; unfold ERRDEBUG_BYTES in *; lia| clear - UMB EBR'; unfold ERRDEBUG_BYTES in *; lia
      | exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)|].
    intros m3 s3' msF3 mo3 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DW3 VIS3 KREL3 MP3.
    pose proof DW3 as (HP3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR1 & _ & FR2' & FR3 & _ & _ & _ & FF3 & FSH3 & _ & _ & _ & _ & MI3 & AC3 & ST3 & _). destruct FF3 as [lb3 FF3].
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| |].
    { eapply aft_z2 with (q := S1c); [exact SSF8| clear - CEIL LO STK0 Q2 LO0; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| unfold AIMG_TOP; clear - FQ5 AF1; lia| clear - FQ6 AF2; lia| eapply aapp_sub; [exact FB3| clear - FQ5; lia| unfold AFS_SIZE; clear - FQ6; lia]
        | clear - CEIL LO STK0 Q2; lia| unfold dsg1 in FR1; exact FR1| unfold dsg2 in FR2'; exact FR2'| unfold dfsh in FSH3; exact FSH3| exact MI3| exact AC3]. }
    intros msF4 mo4 KREL4 MP4 (m4 & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & VIS4 & MU4 & WM4 & MI4 & FR1x & FR2x & FSHx & AC4).
    assert (ST4 : stk asegs m4 lo S1c).
    { eapply stk_transport_disjoint; [exact ST3| exact MU4| exact WM4|]. cbn. unfold sh, ASHB in *. rewrite ?Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8.
      pose proof (sh_add8 ff 512) as SY8. unfold sh in SY8. pose proof aceil_range. clear - H0 CEIL FQ6 AF2 SY8 LO STK0 Q2. rewrite ?ASHADOW_BASE_val in *. lia. }
    assert (DW4 : adwkGc [] NB S' M' LE (dsg1c w16 w32 w40 w48) (wz ee) v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um (uf + lb_bytes Lx) m4 s3').
    { eapply ((DCJ adwkG_w) [] NB S' M' LE _ (wz ee) v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um (uf + lb_bytes Lx) m3 s3' m4 _ _ (wz ee) _ _ _ _ _ fr3 tpl lb3 (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8));
        [exact DW3| exact MU4| exact WM4| exact MI4| exact ST4| | unfold dsg1; exact FR1x| reflexivity| unfold dsg2; exact FR2x| | exact SZ3| | unfold dfsh; exact FSHx| reflexivity].
      - apply Forall_cons; [right; right; right; right; left; cbn; split; apply Z.le_refl|]. apply Forall_cons; [right; right; right; right; right; left; cbn; split; apply Z.le_refl| apply Forall_nil].
      - eapply rw_cells_transport; [exact FR3| exact MU4| exact WM4|]. cbn. unfold sh, ASHB in *. rewrite ?Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 3) with 8.
        pose proof (sh_add8 ff 512) as SY8. unfold sh in SY8. pose proof aceil_range. clear - H0 CEIL FQ6 AF2 SY8 LO STK0 Q2. rewrite ?ASHADOW_BASE_val in *. lia.
      - assert (SHF : Z.shiftr ff 3 + ASHB = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
        eapply rw_cells_transport; [exact FF3| exact MU4| exact WM4|]. rewrite SHF. cbn. unfold dff, arp_fframe2. cbn [cells_size csize Nat.add length].
        assert (SB0 : ASHADOW_BASE <= sh ff) by (unfold sh; clear - FQ5 AF1; Z.div_mod_to_equations; lia).
        pose proof (sh_add8 ff 512) as SY8. replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia).
        pose proof (sh_mono (ff + 4096) _ FQ6) as SYU. pose proof (sh_aapp_range _ _ AF4 ltac:(unfold AFS_SIZE; clear; lia)) as (W1 & W2 & W3). unfold AFS_SIZE in W1, W2, W3.
        pose proof (aapp_not_shadowland _ _ AF4) as NSF. unfold ALOWSH_LO, AHI_LO, AFS_SIZE in *. change (nsh 11571200) with 1446400 in W2.
        pose proof (sh_add8 (as_FSB H) 1446400) as SF8. replace (8 * 1446400) with 11571200 in SF8 by (clear; lia).
        clear - SB0 SY8 SYU W1 W2 W3 NSF FQ5 FQ6 AF2 SF8. rewrite ?ASHADOW_BASE_val in *.
        first [lia| match goal with |- ?G => idtac "ZFF" G end; repeat match goal with K : ?T |- _ => idtac T; fail end]. }
    (* [comment removed for export] *)
    eapply (rp_tailYn NB S' M' LE _ (wz ee) v192 v200 v208 v224 v232 fr3 tpl um (uf + lb_bytes Lx) m4 s3' msF4 mo4 520 AR_INTERNAL_ERROR);
      [exact DW4| exact DNB| | clear; lia| unfold AR_INTERNAL_ERROR; clear; lia| clear - UMB; lia| clear - UFB; lia| exact VIS4| exact KREL4| exact (ah_mpres_trans H HH _ _ _ MP3 MP4)].
    destruct BD as [B1 B2]. unfold dbud in *. rewrite (drest_app LB p A nA pbin Bb nB TB Lx NB LE), lb_bytes_app in B1. rewrite (drest_app LB p A nA pbin Bb nB TB Lx NB LE), length_app, Nat2Z.inj_add in B2.
    split; [clear - B1 LX0; unfold ERRDEBUG_BYTES in *; lia| clear - B2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_tailA : forall Lx NB S' M' LE w16 w32 w40 w48 v192 v200 v208 v224 v232 fr3 tpl (shb shb2 : byte) (shd : list byte) um uf m1 s1' msF1 mo1 (ee line : Z) (E : entrep)
      (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s2w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word),
    adwkGc Lx NB S' M' LE (dsg1c w16 w32 w40 w48) (wz ee) v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m1 s1' ->
    cells_size fr3 = 104%nat ->
    ENTRYobj (drestc Lx NB LE) m1 ee E -> ENTRY_shad m1 ee E -> Permutation (blocks_ENTRY ee E) Lx -> 0 <= line < 2^31 ->
    dnb NB -> dbud H (drestc Lx NB LE) M' (4 * ERRDEBUG_BYTES) 8 ->
    um + errph_bytes (mid_err M') + 4 * ERRDEBUG_BYTES <= DECODE_CUM_BYTES -> uf + errph_bytes (mid_err M') + lb_bytes Lx + 4 * ERRDEBUG_BYTES + 8192 <= DECODE_CUM_BYTES ->
    as_VIS H s1' msF1 = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) b0 b1 b2 b3 b4 b5 b6 b7
                                s2w (Z_to_bv 64 SH) (Z_to_bv 64 line) s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                        F (Z_to_bv 64 ADF_TA) fc None m1 (seg_rom asegs) ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    as_SR H POSTc (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    intros until u6. intros DW SZ3 EO ESH PE LNR DNB BD UMB UFB VIS1 KREL1 MP1.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    assert (LX0 : 0 <= lb_bytes Lx).
    { pose proof DW as (HP1 & _). apply lb_bytes_nonneg_s. apply Forall_forall. intros b Hb.
      pose proof (ah_blocks H HH _ _ _ _ HP1 ltac:(apply in_or_app; right; unfold drest; apply in_or_app; left; exact Hb)) as (_ & _ & E3 & _). exact E3. }
    pose proof DW as (HP1 & _ & STP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RFS1 & _ & _ & MI1 & _).
    pose proof (drest_sub LIB LB SUBL p A nA pbin Bb nB TB Lx NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof (adwkG_hfc Lx NB S' M' LE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (BRS & NDL & DISJ & D2 & D1).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply aft_a1; exact MI1|]. intros msF2 mo2 KREL2 MP2 VIS2. cbn beta in VIS2.
    eapply ((DCJ adwk_raise) Lx NB S' M' LE _ (wz ee) v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m1 s1' msF2 mo2 AFUNC_D1 S_AFUNC_D1 K_AFUNC_D1 ADF_TA_R1 ADF_TA_R2 ADF_TZ line AR_ECH_DECODE_ERROR);
      [exact R_AFUNC_D1| discriminate| rewrite S_AFUNC_D1_len; clear; lia| unfold AFUNC_D1; clear; lia| exact DW| exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)
      | destruct BD as [B1 B2]; split; [clear - B1; unfold ERRDEBUG_BYTES in *; lia| clear - B2; lia]
      | clear - UMB; unfold ERRDEBUG_BYTES in *; lia| clear - UFB LX0; unfold ERRDEBUG_BYTES in *; lia
      | apply pf_sitec; intros e He; apply (pf_shift_mono14 _ _ _ (PF_errnew_mstep14 M M' STP)) in He;
        unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left; unfold PF_entry, pf_raise; do 13 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; left; exact He
      | apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left; unfold PF_entry, pf_raise; do 13 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact He
      | apply pf_sitec; intros e He; unfold PF_readcfg, PF_read_priv; do 16 (apply in_or_app; right); apply in_or_app; left; unfold PF_entry, pf_raise; do 13 (apply in_or_app; right); apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact He
      | exact LNR| unfold AR_ECH_DECODE_ERROR; clear; lia
      | unfold ADF_TA_R1; clear; lia| reflexivity| unfold ADF_TA_R2; clear; lia| reflexivity| unfold ADF_TZ; clear; lia| reflexivity
      | apply aft_a2| apply aft_a3|].
    intros u0' u1' u2' c0' c1' c2' c3' c4' c5' c6' c7' u3' u4' u5' u6' msF3 m3 mo3 s3' LEn M'' c XS3 VIS3 KREL3 MP3 DW3 STEP3 ME3 DL3 FXS3 XP3.
    replace (ret_pc (Z_to_bv 64 ADF_TZ)) with (Z_to_bv 64 ADF_TZ : word) in VIS3 by (symmetry; apply ret_pc_even; [unfold ADF_TZ; clear; lia| reflexivity]).
    pose proof (errph_delta_bounds14 _ _ _ DL3) as [DC3 DB3]. rewrite <- ME3 in DC3, DB3.
    assert (EZ : errph_bytes (mid_err M'') = 0 /\ errph_cnt (mid_err M'') = 0) by (rewrite ME3; split; reflexivity). destruct EZ as [EZ1 EZ2].
    (* [comment removed for export] *)
    assert (XAV : forall b, In b (blocks_ENTRY ee E) -> avoids (XS3 ++ ERR_XE ++ memflag_foot ++ errph_foot (mid_err M')) (blk_addr b) (blk_size b)
                                                /\ shavoids (XS3 ++ ERR_XE ++ memflag_foot ++ errph_foot (mid_err M')) (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (Permutation_in _ PE Hb) as HbX.
      eapply (ECH_AC14_kit.XR_block H HX (mid_err M') s1' (mid_errblocks M' ++ drestc Lx NB LE) m1 (LF1c ff fp) m1 XS3 b);
        [exact HP1| exact RFS1| exact FXS3| apply in_or_app; right; exact (SLX _ HbX)|].
      intros c0 EQ. destruct (adwkG_esc Lx NB S' M' LE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c0 DW EQ) as [I5 Z5].
      split; [apply in_or_app; right; apply SL0; apply SLL; exact I5| split; [| exact Z5]].
      intros EQI. exact (D2 _ _ HbX (SLL _ I5) (eq_sym EQI)). }
    assert (EO3 : ENTRYobj (drestc Lx NB (LEn ++ LE)) m3 ee E).
    { eapply ENTRYobj_LB_mono; [| intros b Hb; eapply (Permutation_in _ (drest_LEn LB p A nA pbin Bb nB TB Lx NB LE LEn)); apply in_or_app; right; exact Hb].
      eapply (ENTRYobj_frameX H); [exact EO| exact XP3| intros b Hb; exact (proj1 (XAV b Hb))]. }
    assert (ESH3 : ENTRY_shad m3 ee E).
    { eapply (ENTRY_shad_frameX H (drestc Lx NB LE) (drestc Lx NB LE)); [exact ESH| exact EO| exact XP3|]. intros b Hb. split; [exact (SLX _ (Permutation_in _ PE Hb))| exact (XAV b Hb)]. }
    eapply (rp_tailZc Lx NB S' M'' (LEn ++ LE) w16 w32 w40 w48 v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd _ _ m3 s3' msF3 mo3 ee E);
      [exact DW3| exact SZ3| exact EO3| exact ESH3| exact PE| exact DNB| | | | exact VIS3| exact KREL3| exact MP3].
    - destruct BD as [B1 B2].
      assert (EQB : forall LEq, lb_bytes (drestc Lx NB LEq) = lb_bytes LEq + lb_bytes (drestc Lx NB [])).
      { intros LEq. unfold drest. cbn [app]. rewrite ?lb_bytes_app, ?lb_bytes_cons, ?lb_bytes_app. cbn [lb_bytes fold_right app]. rewrite ?lb_bytes_app. clear; lia. }
      assert (EQC : forall LEq, length (drestc Lx NB LEq) = (length LEq + length (drestc Lx NB []))%nat).
      { intros LEq. unfold drest. cbn [app]. rewrite ?length_app. cbn [length app]. rewrite ?length_app. cbn [length]. clear; lia. }
      unfold dbud in B1, B2 |- *. rewrite (EQB (LEn ++ LE)), lb_bytes_app. rewrite (EQB LE) in B1. rewrite (EQC (LEn ++ LE)), length_app. rewrite (EQC LE) in B2.
      rewrite ?Nat2Z.inj_add in B2 |- *. unfold ERRDEBUG_BYTES in *. split; [clear - B1 DB3; lia| clear - B2 DC3; lia].
    - clear - UMB EZ1. unfold ERRDEBUG_BYTES in *. lia.
    - clear - UFB EZ1. unfold ERRDEBUG_BYTES in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rp_done : forall NB S' M' LE w16 w24 w32 w40 w48 w56 w64 w72 w96 w104 w112 w128 w136 wee v192 v200 v208 v224 v232 fr3 tpl um uf m1 s1' msF1 mo1
      (rax u0 u1 u2 a0w b1 b2 b3 b4 b5 b6 b7 s2w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word),
    adwkGc [] NB S' M' LE (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 (wz bt) (wz Bb) w96 w104 w112 (wz 0) w128 w136) wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m1 s1' ->
    dnb NB -> uf + 8192 <= DECODE_CUM_BYTES -> um <= DECODE_CUM_BYTES ->
    as_VIS H s1' msF1 = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) a0w b1 b2 b3 b4 b5 b6 b7
                                s2w (Z_to_bv 64 SH) s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                        F (Z_to_bv 64 ADF_DONE) fc None m1 (seg_rom asegs) ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    as_SR H POSTc (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    intros until u6. intros DW DNB UFB UMB VIS1 KREL1 MP1.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof DW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & _).
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply afs_done; exact MI1|]. intros msF2 mo2 KREL2 MP2 VIS2. cbn beta in VIS2.
    eapply (rp_efree [] NB S' M' LE _ wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m1 s1' msF2 mo2 0 None ADF_R_DONE);
      [exact DW| split; reflexivity| unfold ADF_R_DONE; clear; lia| reflexivity| pf_entry_seg 10| cbn [lb_bytes fold_right]; clear - UFB; lia| exact UMB
      | exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)|].
    intros m3 s3' msF3 mo3 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DW3 VIS3 KREL3 MP3.
    pose proof DW3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR1 & _ & FR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI3 & _).
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply afs_done2 with (q := S1c); [clear - CEIL LO STK0 Q2 LO0; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| exact FR1| unfold dsg2 in FR2; exact FR2| exact MI3]|].
    intros msF4 mo4 KREL4 MP4 VIS4. cbn beta in VIS4.
    pose proof rp_errl as RE. unfold rp_errl_stmt in RE.
    eapply (RE NB S' M' LE _ fr3 wee v192 v200 v208 v224 v232 tpl um (uf + lb_bytes []) m3 s3' msF4 mo4 1);
      [exact DW3| right; reflexivity| exact DNB| cbn [lb_bytes fold_right]; clear - UFB; lia| exact UMB| exact VIS4| exact KREL4| exact (ah_mpres_trans H HH _ _ _ MP3 MP4)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bud0 :
       lb_bytes TB + nB + nA + lb_bytes LB + errph_bytes (mid_err M) + ERRSTR_BYTES + DLOOP_BYTES <= as_LIVE_MAX H
    /\ Z.of_nat (length TB) + 2 + Z.of_nat (length LB) + errph_cnt (mid_err M) + ERRSTR_CNT + DLOOP_CNT <= as_LIVE_CNT_MAX H.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    assert (LBE0 : 0 <= lb_bytes (mid_errblocks M)).
    { apply lb_bytes_nonneg_s. apply Forall_forall. intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & E3 & _). exact E3. }
    pose proof BUD as BUDq. pose proof BUDC as BUCq. unfold mid_bytes in BUDq. unfold mid_cnt in BUCq. rewrite CTX in BUDq, BUCq. cbn [ctxph_bytes ctxph_cnt] in BUDq, BUCq.
    rewrite lb_bytes_app in BUDq. rewrite length_app, Nat2Z.inj_add in BUCq. destruct BTR as (_ & TL & TBY).
    unfold DECODE_BYTES, DECODE_CNT, DLOOP_BYTES, DLOOP_CNT, OSSL_ECH_MAX_ECHCONFIG_LEN in *. clear - BUDq BUCq TL TBY NAR NBR LBE0. split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dbud_now : forall Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m' s' hb hc,
    adwkGc Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m' s' ->
    lb_bytes Lx + lb_bytes NB + hb <= DLOOP_BYTES -> Z.of_nat (length Lx) + Z.of_nat (length NB) + hc <= DLOOP_CNT ->
    dbud H (drestc Lx NB LE) M' hb hc.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    intros until hc. intros DW B1 B2. destruct bud0 as [K1 K2].
    pose proof DW as (_ & _ & _ & _ & _ & _ & _ & LC & LBY & _).
    unfold dbud, drest. rewrite !lb_bytes_app, !lb_bytes_cons, !length_app. cbn [length blk_size snd]. rewrite ?lb_bytes_app, ?length_app.
    rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ, ?Nat2Z.inj_add. clear - B1 B2 K1 K2 LC LBY. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma skb_facts : forall Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m' s',
    adwkGc Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m' s' ->
    Permutation NB (SKB st S' ++ EBS S') /\ Z.of_nat (length (SKB st S')) <= 2 /\ 0 <= lb_bytes (SKB st S') <= 88 + 16 * nent S' /\ 0 <= nent S'.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    intros until s'. intros DW.
    pose proof DW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SO1 & _ & SID & SPM & _ & SKI & _).
    split.
    { rewrite blocks_STORE_split, SID in SPM. exact (Permutation_sym (Permutation_cons_inv SPM)). }
    unfold SKB, EBS, nent. destruct SO1 as (_ & _ & EN). destruct (es_entries_o S') as [[K es]|] eqn:EO.
    - destruct EN as (PP & SKO & LEN & _). pose proof SKO as (_ & _ & _ & (N1 & N2) & C20 & _ & _ & KD).
      first [destruct (SKI K es eq_refl) as [_ CAP]| destruct (SKI K es EO) as [_ CAP]]. rewrite <- LEN in CAP. unfold sk_num, zlength in N1, N2.
      unfold blocks_SK. destruct (Z.eqb_spec (sk_cap K) 0) as [C0|CN]; rewrite ?lb_bytes_cons; cbn [length blk_size snd lb_bytes fold_right app Z.add]; unfold SK_SIZE.
      + clear - N1. lia.
      + clear - CAP N1 N2 CN. lia.
    - cbn. clear. lia.
  Qed.

  Lemma nb_ledger : forall Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m' s' c,
    adwkGc Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m' s' -> dledger S' c -> c <= 1500 ->
    lb_bytes NB <= 36 * c + 88 /\ 5 * Z.of_nat (length NB) <= 2 * c + 10 /\ 0 <= c /\ 0 <= nent S' /\ 23 * nent S' <= c /\ dnb NB.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    intros until c. intros DW (L1 & L2 & L3 & L4) CLE.
    destruct (skb_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (PNB & KL & KB & N0).
    unfold dnb, DECODE_CNT, DECODE_BYTES.
    rewrite (lb_bytes_perm _ _ PNB), (Permutation_length PNB), lb_bytes_app, length_app, Nat2Z.inj_add.
    clear - L1 L2 L3 L4 KL KB N0 CLE. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Definition LOOPAT (kk : nat) : Prop :=
    forall (cur rem c : Z) (NB : list block) (S' : storerep) (M' : libmid) (LE : list block)
           (w16 w32 w40 w48 wee v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word) (tpl um uf : Z) (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model)
           (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s9w s10w s11w u3 u4 u5 u6 : word),
      32 <= zlength bs < 1500 -> 1 <= olen_of bs <= zlength bs - 2 ->
      rem <= Z.of_nat kk ->
      adwkc [] NB S' M' LE w16 w32 w40 w48 wee v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf m' s' ->
      dledger S' c -> cur = Bb + 2 + c -> c + rem = olen_of bs -> 1 <= rem ->
      um + errph_bytes (mid_err M') + ENTRY_CM rem <= DECODE_CUM_BYTES -> uf + errph_bytes (mid_err M') + ENTRY_CF rem <= DECODE_CUM_BYTES ->
      as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) b0 b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 2) (Z_to_bv 64 SH) s4w s5w s6w (Z_to_bv 64 rem) (Z_to_bv 64 cur) s9w s10w s11w u3 u4 u5 u6)
                          F (Z_to_bv 64 ADF_HEAD) fc None m' (seg_rom asegs) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
      as_SR H POSTc (mkCfg msF' mo').

  (* [comment removed for export] *)
  Lemma rp_trip_adv : forall kk (cur rem c elen : Z) NB S' M' LE (w16 w32 w40 w48 wee v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word) tpl um uf m' s' msF' mo'
      (rax u0 u1 u2 a0w b1 b2 b3 b4 b5 b6 b7 s5w s6w s8w s9w s11w u3 u4 u5 u6 : word),
    LOOPAT kk -> 32 <= zlength bs < 1500 -> 1 <= olen_of bs <= zlength bs - 2 -> rem - 4 - elen <= Z.of_nat kk ->
    adwkc [] NB S' M' LE w16 w32 w40 w48 wee v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf m' s' ->
    dledger S' (c + 4 + elen) -> cur = Bb + 2 + c -> c + rem = olen_of bs -> 0 <= elen -> 4 + elen <= rem -> 0 <= c ->
    um + errph_bytes (mid_err M') + ENTRY_CM (rem - 4 - elen) <= DECODE_CUM_BYTES -> uf + errph_bytes (mid_err M') + ENTRY_CF (rem - 4 - elen) <= DECODE_CUM_BYTES ->
    as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) a0w b1 b2 b3 b4 b5 b6 b7
                                (Z_to_bv 64 2) (Z_to_bv 64 SH) (Z_to_bv 64 (cur + 4 + elen)) s5w s6w (Z_to_bv 64 (rem - 4)) s8w s9w (Z_to_bv 64 elen) s11w u3 u4 u5 u6)
                        F (Z_to_bv 64 ADF_ADV) fc None m' (seg_rom asegs) ->
    as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
    as_SR H POSTc (mkCfg msF' mo').
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    intros until u6. intros LP TR OLEN REM DW LED CUR CR E0 ER C0 UMB UFB VIS1 KREL1 MP1.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    pose proof DW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI1 & _).
    pose proof (adwkG_hfc [] NB S' M' LE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (BRS & _).
    pose proof (drest_sub LIB LB SUBL p A nA pbin Bb nB TB [] NB LE) as (_ & _ & _ & _ & _ & IB & _).
    pose proof (BRS _ ltac:(apply in_or_app; right; exact IB)) as (BP & _ & _ & _ & BH & _). cbn [blk_addr blk_size fst snd] in BP, BH.
    pose proof NBR as NBR'. unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBR'.
    pose proof DW as DWG. rewrite adwk_G in DWG.
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1
      | eapply afs_adv with (q := S1c) (cur := cur) (rem := rem) (elen := elen);
        [exact E0| exact ER| clear - CR OLEN TR C0; lia| clear - CUR C0 BP; lia| clear - CUR CR OLEN TR BH NBR' C0 ACB; lia
        | clear - CEIL LO STK0 Q2 LO0; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| exact MI1]|].
    intros msF2 mo2 KREL2 MP2. cbn beta.
    destruct (Z.eqb_spec (rem - 4 - elen) 0) as [Z0|NZ]; intros VIS2.
    - unfold dsg1 in DWG. eapply (rp_done NB S' M' LE); [exact DWG| | | | exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)].
      + destruct (nb_ledger [] NB S' M' LE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (c + 4 + elen) DWG LED ltac:(clear - CR OLEN TR ER C0; lia)) as (_ & _ & _ & _ & _ & DNB). exact DNB.
      + rewrite Z0 in UFB. unfold ENTRY_CF in UFB. clear - UFB EBR'. lia.
      + unfold ENTRY_CM in UMB. clear - UMB EBR' ER E0. lia.
    - eapply (LP (cur + 4 + elen) (rem - 4 - elen) (c + 4 + elen) NB S' M' LE);
        [exact TR| exact OLEN| exact REM| exact DW| exact LED| clear - CUR; lia| clear - CR; lia| clear - NZ ER E0; lia| exact UMB| exact UFB
        | exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_loop : forall kk, LOOPAT kk.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    induction kk as [|kk IH]; unfold LOOPAT;
      intros cur rem c NB S' M' LE w16 w32 w40 w48 wee v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf m' s' msF' mo'
             rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s9w s10w s11w u3 u4 u5 u6 TR OLEN REM DW LED CUR CR R1 UMB UFB VIS1 KREL1 MP1.
    { exfalso. clear - REM R1. cbn in REM. lia. }
    pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    pose proof NBR as NBR'. unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBR'.
    pose proof DW as DWG. rewrite adwk_G in DWG.
    destruct (nb_ledger [] NB S' M' LE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c DWG LED ltac:(clear - CR OLEN TR R1; lia)) as (NB1 & NB2 & C0 & N0 & N23 & DNB).
    pose proof RPE as RP. unfold rp_entry_stmt in RP.
    eapply (RP cur rem NB S' M' LE); clear RP; [exact DW| clear - CUR C0; lia| exact R1| clear - CUR CR OLEN NBR'; lia| | exact UMB| exact UFB| clear - N23 CR OLEN TR R1; lia
      | | | | | | exact VIS1| exact KREL1| exact MP1].
    - (* [comment removed for export] *)
      eapply dbud_now; [exact DWG| |]; cbn [lb_bytes length fold_right Z.of_nat]; unfold ENTRY_BYTES, ENTRY_CNT, DLOOP_BYTES, DLOOP_CNT.
      + clear - NB1 CR OLEN TR R1 C0. lia.
      + clear - NB2 CR OLEN TR R1 C0. lia.
    - (* [comment removed for export] *)
      unfold dK_adv. intros NB2' NBe S2 M2 LE2 v16 v32 v40 v48 wee2 z192 z200 z208 z224 z232 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 tpl2 um2 uf2 elen m2 s2' msF2 mo2
        rax2 v0 v1 v2 a0w c1 c2 c3 c4 c5 c6 c7 t5w t6w t8w t9w t11w v3 v4 v5 v6 DW2 EL19 ER UM2 UF2 (EBS2 & NE2 & SKL2 & SKB2) NBE1 NBE2 VIS2 KREL2 MP2.
      pose proof (errph_bytes_range (mid_err M2)) as [EBR2 ECR2].
      eapply (rp_trip_adv kk cur rem c elen NB2' S2 M2 LE2); [exact IH| exact TR| exact OLEN| clear - REM EL19; lia| exact DW2| | exact CUR| exact CR| clear - EL19; lia| exact ER| exact C0
        | unfold ENTRY_CM in *; clear - UMB UM2 EBR' EBR2 ER EL19; lia| unfold ENTRY_CF in *; clear - UFB UF2 EBR' EBR2 ER EL19; lia| exact VIS2| exact KREL2| exact MP2].
      destruct LED as (L1 & L2 & L3 & L4). unfold dledger. rewrite EBS2, NE2, length_app, lb_bytes_app, Nat2Z.inj_add. unfold ENTRY_KEPT in NBE2.
      clear - L1 L2 L3 L4 NBE1 NBE2 EL19. repeat split; lia.
    - (* [comment removed for export] *)
      unfold dK_skip. intros M2 LE2 v16 v32 v40 v48 wee2 z192 z200 z208 z224 z232 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 tpl2 um2 uf2 elen m2 s2' msF2 mo2
        rax2 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 t5w t6w t8w t9w t11w v3 v4 v5 v6 DW2 EL0 ER UM2 UF2 VIS2 KREL2 MP2.
      pose proof (errph_bytes_range (mid_err M2)) as [EBR2 ECR2].
      eapply (rp_trip_adv kk cur rem c elen NB S' M2 LE2); [exact IH| exact TR| exact OLEN| clear - REM EL0; lia| exact DW2| | exact CUR| exact CR| exact EL0| exact ER| exact C0
        | unfold ENTRY_CM in *; clear - UMB UM2 EBR' EBR2 ER EL0; lia| unfold ENTRY_CF in *; clear - UFB UF2 EBR' EBR2 ER EL0; lia| exact VIS2| exact KREL2| exact MP2].
      eapply dledger_mono; [exact LED| clear - EL0; lia].
    - (* [comment removed for export] *)
      unfold dK_tailA. intros Lx M2 LE2 v16 v32 v40 v48 z192 z200 z208 z224 z232 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 tpl2 um2 uf2 shb2 shb3 shd2 m2 s2' msF2 mo2 ee line E
        rax2 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 t2w t5w t6w t7w t8w t9w t10w t11w v3 v4 v5 v6 DW2 EO ESH PE LNR BD UM2 UF2 VIS2 KREL2 MP2.
      eapply (rp_tailA Lx NB S' M2 LE2); [exact DW2| reflexivity| exact EO| exact ESH| exact PE| exact LNR| exact DNB| exact BD| exact UM2| exact UF2| exact VIS2| exact KREL2| exact MP2].
    - (* [comment removed for export] *)
      unfold dK_tailZ. intros Lx M2 LE2 v16 v32 v40 v48 z192 z200 z208 z224 z232 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 tpl2 um2 uf2 shb2 shb3 shd2 m2 s2' msF2 mo2 ee E
        rax2 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 t2w t4w t5w t6w t7w t8w t9w t10w t11w v3 v4 v5 v6 DW2 EO ESH PE BD UM2 UF2 VIS2 KREL2 MP2.
      eapply (rp_tailZc Lx NB S' M2 LE2); [exact DW2| reflexivity| exact EO| exact ESH| exact PE| exact DNB
        | destruct BD as [B1 B2]; split; [clear - B1; unfold ERRDEBUG_BYTES in *; lia| clear - B2; lia]
        | clear - UM2; unfold ERRDEBUG_BYTES in *; lia| clear - UF2; unfold ERRDEBUG_BYTES in *; lia| exact VIS2| exact KREL2| exact MP2].
    - (* [comment removed for export] *)
      unfold dK_tailX. intros Lx NB2' S2 M2 LE2 v16 v32 v40 v48 z192 z200 z208 z224 z232 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 tpl2 um2 uf2 m2 s2' msF2 mo2 ee E
        rax2 v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 t4w t5w t6w v3 v4 v5 v6 DW2 (EBS2 & NE2 & SKL2 & SKB2) EO ESH PE BD UM2 UF2 VIS2 KREL2 MP2.
      rewrite adwk_G in DW2.
      assert (DNB2 : dnb NB2').
      { destruct (skb_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW2) as (PNB & KL & KB & N0').
        destruct LED as (L1 & L2 & L3 & L4). unfold dnb, DECODE_CNT, DECODE_BYTES.
        rewrite (lb_bytes_perm _ _ PNB), (Permutation_length PNB), lb_bytes_app, length_app, Nat2Z.inj_add, EBS2. rewrite NE2 in KB.
        clear - L1 L2 L3 L4 KL KB CR OLEN TR R1. split; lia. }
      eapply (rp_tailXc Lx NB2' S2 M2 LE2 _ (wz ee) z192 z200 z208 z224 z232 _ tpl2 um2 uf2 m2 s2' msF2 mo2 ee (Some E));
        [exact DW2| split; [exact EO| split; [exact ESH| exact PE]]| exact DNB2
        | destruct BD as [B1 B2]; split; [clear - B1; unfold ERRDEBUG_BYTES in *; lia| clear - B2; lia]
        | clear - UM2; unfold ERRDEBUG_BYTES in *; lia| clear - UF2; unfold ERRDEBUG_BYTES in *; lia| exact VIS2| exact KREL2| exact MP2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rp_flat : DCT rp_flat_stmt.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH RPE BTFREE.
    unfold rp_flat_stmt.
    intros M' LE w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 wee v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf m1 s1' msF1 mo1
           rax u0 u1 u2 a0w a1w a2w b3 b4 b5 b6 b7 s5w s9w u3 u4 u5 u6 DW UMB UFB BD VIS1 KREL1 MP1.
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof (errph_bytes_range (mid_err M')) as [EBR' ECR'].
    pose proof NBR as NBR'. unfold OSSL_ECH_MAX_ECHCONFIG_LEN in NBR'.
    pose proof DW as (HP1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BS1 & _ & ADB1 & _ & _ & _ & _ & FR1 & SZ1 & FR2 & FR3 & SZ3 & _ & _ & [lbf FF1] & FSH1 & LSH1 & _ & _ & _ & MI1 & AC1 & ST1 & _).
    pose proof (adwkG_hfc [] [] S M' LE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (BRS & _).
    pose proof (drest_sub LIB LB SUBL p A nA pbin Bb nB TB [] [] LE) as (_ & _ & _ & _ & _ & IB & IA & _).
    pose proof (BRS _ ltac:(apply in_or_app; right; exact IB)) as (BP & B16 & _ & _ & BH & _). cbn [blk_addr blk_size fst snd] in BP, B16, BH.
    pose proof (BRS _ ltac:(apply in_or_app; right; exact IA)) as (AP & _ & _ & _ & AH & _). cbn [blk_addr blk_size fst snd] in AP, AH.
    pose proof (ah_blocks H HH _ _ _ _ HP ltac:(apply in_or_app; right; exact (proj1 (proj2 SO)))) as (SK1 & SK2 & SK3 & _ & SK5 & _). cbn [blk_addr blk_size fst snd] in SK1, SK2, SK3, SK5.
    assert (LED0 : dledger S 0) by (unfold dledger, EBS, nent; rewrite SEO; cbn; clear; lia).
    assert (BDY : dbud H (drestc [] [] LE) M' (2 * ERRDEBUG_BYTES) 4).
    { eapply dbud_now; [exact DW| |]; cbn; unfold ERRDEBUG_BYTES, DLOOP_BYTES, DLOOP_CNT; clear; lia. }
    assert (DNB0 : dnb []) by (unfold dnb, DECODE_CNT, DECODE_BYTES; cbn; clear; lia).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL1| exact VIS1| eapply afs_dec with (T := zlength bs) (Bb := Bb); [clear - NBR'; lia| exact BP| clear - BH ACB NBR'; lia| exact MI1]|].
    intros msF2 mo2 KREL2 MP2. cbn beta.
    destruct (andb (32 <=? zlength bs) (zlength bs <? 1500)) eqn:G; intros (a0' & a1' & VIS2).
    2: { (* [comment removed for export] *)
         eapply (rp_tailY [] S M' LE _ wee v192 v200 v208 v224 v232 _ tpl um uf m1 s1' msF2 mo2 509 AR_PASSED_NULL_PARAMETER); [exact DW| exact DNB0| exact BDY| clear; lia| unfold AR_PASSED_NULL_PARAMETER; clear; lia
           | unfold DLOOP_CM, ERRDEBUG_BYTES in *; clear - UMB; lia| unfold DLOOP_CF, ERRDEBUG_BYTES in *; clear - UFB; lia
           | exact VIS2| exact KREL2| exact (ah_mpres_trans H HH _ _ _ MP1 MP2)]. }
    apply andb_prop in G. destruct G as [G1 G2]. apply Z.leb_le in G1. apply Z.ltb_lt in G2.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2
      | eapply afs_hdr with (q := S1c) (T := zlength bs) (Bb := Bb) (A := A) (bt := bt) (st := st) (shf := SH) (bs := bs);
        [clear - G1 G2; lia| reflexivity| exact BS1| exact BP| clear - BH ACB NBR'; lia| clear - B16; Z.div_mod_to_equations; lia
        | eapply (addressable_accessible _ _ _ _ _ ADB1); [apply Z.le_refl| clear - G1 NBR'; lia| unfold AAPP_HI; clear - BH ACB; lia]
        | clear - CEIL LO STK0 Q2 LO0; lia| clear - Q2 SPR SPA; Z.div_mod_to_equations; lia| clear - AP AH ACB NAR; lia| exact (proj1 BTR)
        | clear - SK1 SK3 SK5 ACB; lia| clear - SK2; Z.div_mod_to_equations; lia
        | exact FR1| unfold dsg2 in FR2; exact FR2| exact MI1]|].
    intros msF3 mo3 KREL3 MP3. cbn beta. intros (a0'' & a1'' & a2'' & K3).
    pose proof (ah_mpres_trans H HH _ _ _ MP1 (ah_mpres_trans H HH _ _ _ MP2 MP3)) as MPc3.
    destruct K3 as [[LT VIS3]|[(Z0 & m2 & VIS3 & MU & WM & MI2 & FR1b)|([OL1 OL2] & m2 & VIS3 & MU & WM & MI2 & FR1b)]].
    - (* [comment removed for export] *)
      eapply (rp_tailY [] S M' LE _ wee v192 v200 v208 v224 v232 _ tpl um uf m1 s1' msF3 mo3 514 AR_INTERNAL_ERROR); [exact DW| exact DNB0| exact BDY| clear; lia| unfold AR_INTERNAL_ERROR; clear; lia
        | unfold DLOOP_CM, ERRDEBUG_BYTES in *; clear - UMB; lia| unfold DLOOP_CF, ERRDEBUG_BYTES in *; clear - UFB; lia
        | exact VIS3| exact KREL3| exact MPc3].
    - (* [comment removed for export] *)
      assert (T12 : forall A' cs, rw_cells asegs m1 A' cs -> (A' + Z.of_nat (cells_size cs) <= S1c + 16 \/ S1c + 144 <= A') -> rw_cells asegs m2 A' cs).
      { intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. cbn. split; [clear - HA; lia| exact I]. }
      assert (ST2 : stk asegs m2 lo S1c).
      { eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. cbn. split; [clear; lia| exact I]. }
      pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
      change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
      pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AFS_SIZE in AF2.
      assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
      assert (DW2 : adwkGc [] [] S M' LE (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 (wz bt) (wz Bb) (wz 0) (wz (ff + 80)) (wz (ff + 64)) (wz 0) (wz st) (wz (ff + 32))) wee v192 v200 v208 v224 v232
                      (arp_sg3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m2 s1').
      { eapply ((DCJ adwkG_w) [] [] S M' LE _ wee v192 v200 v208 v224 v232 _ tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m1 s1' m2 [(S1c + 16, S1c + 144)]
                 _ wee v192 v200 v208 v224 v232 _ tpl _ (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8));
          [exact DW| exact MU| exact WM| exact MI2| exact ST2| apply Forall_cons; [right; left; cbn [fst snd]; clear; lia| apply Forall_nil]
          | exact FR1b| reflexivity| apply T12; [exact FR2| right; clear; lia]| apply T12; [exact FR3| right; clear; lia]| exact SZ3
          | apply T12; [exact FF1| left; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - FQ6 AF2 CEIL LO STK0 Q2; lia]
          | apply T12; [exact FSH1| left; unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length];
                        pose proof (sh_add8 ff 512) as SY8; replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia); pose proof (sh_mono (ff + 4096) _ FQ6) as SYU; pose proof (sh_mono _ _ AF2) as SYA;
                        unfold sh, ASHB in *; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear - SY8 SYU SYA SHC CEIL LO STK0 Q2; rewrite ?ASHADOW_BASE_val in *; lia]
          | exact LSH1]. }
      eapply (rp_done [] S M' LE w16 w24 w32 w40 w48 w56 w64 w72); [exact DW2| exact DNB0| unfold DLOOP_CF in UFB; clear - UFB EBR'; lia| unfold DLOOP_CM in UMB; clear - UMB EBR'; lia
        | exact VIS3| exact KREL3| exact MPc3].
    - (* [comment removed for export] *)
      assert (T12 : forall A' cs, rw_cells asegs m1 A' cs -> (A' + Z.of_nat (cells_size cs) <= S1c + 16 \/ S1c + 144 <= A') -> rw_cells asegs m2 A' cs).
      { intros A' cs RC HA. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. cbn. split; [clear - HA; lia| exact I]. }
      assert (ST2 : stk asegs m2 lo S1c).
      { eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. cbn. split; [clear; lia| exact I]. }
      pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
      change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
      pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AFS_SIZE in AF2.
      assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
      assert (DW2 : adwkGc [] [] S M' LE (dsg1c w16 w32 w40 w48) wee v192 v200 v208 v224 v232 (arp_sg3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) tpl
                      (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m2 s1').
      { eapply ((DCJ adwkG_w) [] [] S M' LE _ wee v192 v200 v208 v224 v232 _ tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m1 s1' m2 [(S1c + 16, S1c + 144)]
                 _ wee v192 v200 v208 v224 v232 _ tpl _ (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8));
          [exact DW| exact MU| exact WM| exact MI2| exact ST2| apply Forall_cons; [right; left; cbn [fst snd]; clear; lia| apply Forall_nil]
          | unfold dsg1; exact FR1b| reflexivity| apply T12; [exact FR2| right; clear; lia]| apply T12; [exact FR3| right; clear; lia]| exact SZ3
          | apply T12; [exact FF1| left; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; clear - FQ6 AF2 CEIL LO STK0 Q2; lia]
          | apply T12; [exact FSH1| left; unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length];
                        pose proof (sh_add8 ff 512) as SY8; replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia); pose proof (sh_mono (ff + 4096) _ FQ6) as SYU; pose proof (sh_mono _ _ AF2) as SYA;
                        unfold sh, ASHB in *; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear - SY8 SYU SYA SHC CEIL LO STK0 Q2; rewrite ?ASHADOW_BASE_val in *; lia]
          | exact LSH1]. }
      rewrite <- adwk_G in DW2.
      eapply (rp_loop (Z.to_nat (olen_of bs)) (Bb + 2) (olen_of bs) 0 [] S M' LE);
        [exact (conj G1 G2)| exact (conj OL1 OL2)| rewrite Z2Nat.id by (clear - OL1; lia); apply Z.le_refl| exact DW2| exact LED0| clear; lia| clear; lia| exact OL1
        | unfold ENTRY_CM, DLOOP_CM in *; clear - UMB OL2 G2; lia| unfold ENTRY_CF, DLOOP_CF in *; clear - UFB OL2 G2; lia
        | exact VIS3| exact KREL3| exact MPc3].
  Qed.
End RC.
