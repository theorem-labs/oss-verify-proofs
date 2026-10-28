(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec Cells CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsWalk AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC6_acc ECH_AC7_kit ECH_AC8_blockA ECH_AC9_kit ECH_AC9_rdseg
  ECH_AC9_rdloop ECH_AC9_rdpro ECH_AKitS.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64 ECH_C9_rdfacts.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require ECH_C9_ctrl.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asegs_find_none_high9 : forall a n, 1 <= n -> 12599296 <= a -> find_segment asegs a n = None.
Proof.
  intros a n Hn Ha. unfold asegs, RefMemImage.Ref.loaded_segments. cbn -[Z.leb Z.add Z.of_N].
  cbn [Z.of_N seg_base seg_size RefMemImage.RefMemImage_segment_000 RefMemImage.RefMemImage_segment_001 RefMemImage.RefMemImage_segment_002 RefMemImage.RefMemImage_segment_003
       AsanUbsan.AsanUbsan_segment_000 AsanUbsan.AsanUbsan_segment_001
       AsanUbsan.AsanUbsan_segment_002 AsanUbsan.AsanUbsan_segment_003].
  destruct (Z.leb_spec 65536 a); destruct (Z.leb_spec (a + n) (65536 + 1593344)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 1658880 a); destruct (Z.leb_spec (a + n) (1658880 + 4046848)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 5705728 a); destruct (Z.leb_spec (a + n) (5705728 + 495616)); cbn [andb]; try (exfalso; lia).
  destruct (Z.leb_spec 6201344 a); destruct (Z.leb_spec (a + n) (6201344 + 6397952)); cbn [andb]; try (exfalso; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stk_transport_high : forall m m' lo hi, stk asegs m lo hi -> wmono asegs m m' -> 12599296 <= lo -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (L0 & H64 & ST) WM HI. split; [exact L0| split; [exact H64|]]. intros a Ha.
  destruct (ST a Ha) as [W (b & B)]. pose proof (WM _ W) as W'. split; [exact W'|]. unfold mrd.
  destruct (m' (wa a)) as [b'|] eqn:E; [eexists; reflexivity|]. exfalso. apply W'. unfold wview. rewrite E.
  rewrite wa_unsigned by lia. rewrite asegs_find_none_high9 by lia. reflexivity.
Qed.

Lemma le4_wz_of_bytes9 : forall bs, length bs = 4%nat -> le4 (wz (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le4, wz.
  assert (B : 0 <= bytes_le_to_Z bs < 2^64).
  { pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs) as B0. rewrite L in B.
    change (2 ^ (8 * Z.of_nat 4)) with (2^32) in B. lia. }
  rewrite unsigned_lit by lia. rewrite <- L. apply Z_to_le_bytes_of_bytes.
Qed.
(* [comment removed for export] *)
Lemma rw_cells_CB4_C4_9 : forall segs m A pre bs post,
  rw_cells segs m A (pre ++ CB 4 bs :: post) -> rw_cells segs m A (pre ++ C4 (wz (bytes_le_to_Z bs)) :: post).
Proof.
  intros segs m A pre bs post [[Hwf Hb] Hw].
  pose proof Hwf as W0. apply cells_wf_app in W0. destruct W0 as [_ [L _]]. cbn in L.
  split; [split|].
  - apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [W1 [_ W3]]. split; [exact W1|]. split; [exact I| exact W3].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le4_wz_of_bytes9 by exact L. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.


Lemma le4_cont_bytes : forall c, map bv_unsigned (le4 (wz c)) = map (fun z => z mod 256) [c; c / 256; c / 65536; c / 16777216].
Proof.
  intros c. unfold le4, wz, word_to_le_bytes. rewrite Z_to_bv_unsigned.
  cbn [Z_to_le_bytes map]. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (2^64).
  rewrite !Z.shiftr_shiftr by lia. rewrite !Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod c (2^64) ltac:(lia)) as DM. set (q := c / 2 ^ 64) in DM.
  replace (c mod 2^64) with (c + 2^64 * (- q)) by lia.
  change (2 ^ 8) with (256 ^ 1). change (2 ^ (8 + 8)) with (256 ^ 2). change (2 ^ (8 + 8 + 8)) with (256 ^ 3).
  rewrite !ECH_C9_ctrl.div256k_mod64 by lia. rewrite Z.pow_1_r. change (256 ^ 2) with 65536. change (256 ^ 3) with 16777216.
  replace ((c + 2 ^ 64 * - q) mod 256) with (c mod 256); [reflexivity|].
  replace (c + 2 ^ 64 * - q) with (c + (- 72057594037927936 * q) * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> exists w : word, le8 w = bs.
Proof.
  intros bs L. exists (le_bytes_to_word bs). unfold le8, word_to_le_bytes, le_bytes_to_word.
  rewrite Z_to_bv_unsigned. pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs) as B0. rewrite L in B.
  change (bv_wrap 64 ?x) with (x mod 2^64). rewrite Z.mod_small by (cbn in B; clear - B B0; lia). rewrite <- L. apply Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB0 : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A (CB 0 [] :: cs).
Proof.
  intros m A cs H. eapply arw_cells_recut; [exact H| |].
  - destruct H as [[WF _] _]. cbn. split; [reflexivity| exact WF].
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ardframe_of_head : forall m fb ctx ff mb a out outl j0 j80 j104 j136 j256,
  rw_cells asegs m fb (aheadslots ctx ff mb a out outl j0 j80 j104 j136 j256) ->
  exists w136 w152 w216 w224,
    rw_cells asegs m fb [CB 8 j0] /\
    rw_cells asegs m (fb + 8) (ardslots ctx ff ff 0 mb a (ff + 32) (Z_to_bv 64 out) (Z_to_bv 64 outl) w136 w152 w216 w224 (Z_to_bv 64 0) j256).
Proof.
  intros until j256. intros H. pose proof H as W. destruct W as [[WF _] _]. cbn in WF.
  assert (L80 : length j80 = 16%nat) by tauto. assert (L104 : length j104 = 8%nat) by tauto.
  assert (L136 : length j136 = 8%nat) by tauto. assert (L256 : length j256 = 16%nat) by tauto.
  destruct (le8_of_bytes (firstn 8 j80) ltac:(rewrite length_firstn; lia)) as [w136 E136].
  destruct (le8_of_bytes (skipn 8 j80) ltac:(rewrite length_skipn; lia)) as [w152 E152].
  destruct (le8_of_bytes j104 L104) as [w216 E216].
  destruct (le8_of_bytes j136 L136) as [w224 E224].
  exists w136, w152, w216, w224.
  assert (E : rw_cells asegs m fb ([CB 8 j0] ++ ardslots ctx ff ff 0 mb a (ff + 32) (Z_to_bv 64 out) (Z_to_bv 64 outl) w136 w152 w216 w224 (Z_to_bv 64 0) j256)).
  { eapply arw_cells_recut; [exact H| |].
    - cbn. tauto.
    - unfold aheadslots, ardslots. cbn [cells_bytes cbytes app].
      rewrite E136, E152, E216, E224.
      rewrite (app_assoc (firstn 8 j80) (skipn 8 j80)), (firstn_skipn 8 j80). reflexivity. }
  apply rw_cells_app in E. cbn [cells_size csize Nat.add] in E. replace (fb + Z.of_nat 8) with (fb + 8) in E by lia. exact E.
Qed.

(* [comment removed for export] *)
Lemma b64ctx_at_head : forall m ctx enc bjunk, length bjunk = 2528%nat ->
  rw_cells asegs m ctx [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 2); C4 (wz 1); C4 (wz 1); C4 (wz 0); C8 (wz enc); CB 2528 bjunk; C8 (wz 0); C8 (wz 0)] ->
     rw_cells asegs m ctx (rdhdr 0 0 0 1 enc)
  /\ rw_cells asegs m (ctx + 40) [CB 1502 (firstn 1502 bjunk)]
  /\ rw_cells asegs m (ctx + 1542) [CB 1024 (firstn 1024 (skipn 1502 bjunk))]
  /\ rw_cells asegs m (ctx + 2566) [CB 2 (skipn 2526 bjunk); C8 (wz 0); C8 (wz 0)].
Proof.
  intros m ctx enc bjunk LJ H.
  assert (E : rw_cells asegs m ctx ((rdhdr 0 0 0 1 enc ++ [CB 1502 (firstn 1502 bjunk)]) ++ [CB 1024 (firstn 1024 (skipn 1502 bjunk))]
                                   ++ [CB 2 (skipn 2526 bjunk); C8 (wz 0); C8 (wz 0)])).
  { eapply arw_cells_recut; [exact H| |].
    - cbn. rewrite !length_firstn, !length_skipn. repeat split; lia.
    - unfold rdhdr. cbn [cells_bytes cbytes app].
      rewrite <- (firstn_skipn 1502 bjunk) at 4. rewrite <- (firstn_skipn 1024 (skipn 1502 bjunk)) at 2. rewrite skipn_skipn. cbn [Nat.add].
      rewrite <- !app_assoc. reflexivity. }
  apply rw_cells_app in E. destruct E as [E1 E]. apply rw_cells_app in E. destruct E as [E2 E3].
  apply rw_cells_app in E1. destruct E1 as [E0 E1].
  revert E1 E2 E3. rewrite !cells_size_app. cbn [cells_size csize app Nat.add rdhdr]. intros E1 E2 E3.
  replace (ctx + Z.of_nat 40) with (ctx + 40) in E1 by lia.
  replace (ctx + Z.of_nat 1542) with (ctx + 1542) in E2 by lia.
  replace (ctx + Z.of_nat 1542 + Z.of_nat 1024) with (ctx + 2566) in E3 by lia.
  split; [exact E0|]. split; [exact E1|]. split; [exact E2| exact E3].
Qed.

(* [comment removed for export] *)
Lemma b64ctx_used_of_exit : forall m ctx enc bl bo c jb jt tl,
  rw_cells asegs m ctx (rdhdr bl bo 0 c enc) -> rw_cells asegs m (ctx + 40) [CB 1502 jb] -> rw_cells asegs m (ctx + 1542) [CB 1024 jt] ->
  rw_cells asegs m (ctx + 2566) [CB 2 tl; C8 (wz 0); C8 (wz 0)] ->
  let hdr := cells_bytes [C4 (wz bl); C4 (wz bo); C4 (wz 0); C4 (wz 0); C4 (wz 2); C4 (wz 1); C4 (wz c); C4 (wz 0)] in
     rw_cells asegs m ctx (b64ctx_used_cells enc hdr (jb ++ jt ++ tl) 0) /\ length hdr = 32%nat /\ length (jb ++ jt ++ tl) = 2528%nat
  /\ map bv_unsigned (firstn 4 (skipn 24 hdr)) = map (fun z => z mod 256) [c; c / 256; c / 65536; c / 16777216].
Proof.
  intros until tl. intros H0 H1 H2 H3. cbv zeta.
  pose proof H1 as W1. destruct W1 as [[WF1 _] _]. cbn in WF1. pose proof H2 as W2. destruct W2 as [[WF2 _] _]. cbn in WF2.
  pose proof H3 as W3. destruct W3 as [[WF3 _] _]. cbn in WF3.
  assert (L1 : length jb = 1502%nat) by tauto. assert (L2 : length jt = 1024%nat) by tauto. assert (L3 : length tl = 2%nat) by tauto.
  assert (E1 : rw_cells asegs m ctx (rdhdr bl bo 0 c enc ++ [CB 1502 jb])).
  { apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact H0| cbn [cells_size csize Nat.add rdhdr]; replace (ctx + Z.of_nat 40) with (ctx + 40) by lia; exact H1]. }
  assert (E2 : rw_cells asegs m ctx ((rdhdr bl bo 0 c enc ++ [CB 1502 jb]) ++ [CB 1024 jt])).
  { apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact E1| rewrite cells_size_app; cbn [cells_size csize Nat.add rdhdr app]; replace (ctx + Z.of_nat 1542) with (ctx + 1542) by lia; exact H2]. }
  assert (E : rw_cells asegs m ctx (((rdhdr bl bo 0 c enc ++ [CB 1502 jb]) ++ [CB 1024 jt]) ++ [CB 2 tl; C8 (wz 0); C8 (wz 0)])).
  { apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact E2| rewrite !cells_size_app; cbn [cells_size csize Nat.add rdhdr app]; replace (ctx + Z.of_nat 2566) with (ctx + 2566) by lia; exact H3]. }
  clear E1 E2.
  split; [| split; [reflexivity| split; [rewrite !length_app; lia|]]].
  - eapply arw_cells_recut; [exact E| |].
    + cbn. rewrite !length_app. repeat split; lia.
    + unfold rdhdr, b64ctx_used_cells. cbn [cells_bytes cbytes app]. rewrite <- !app_assoc. reflexivity.
  - generalize (le4_cont_bytes c). unfold le4, wz, word_to_le_bytes. cbn. intros E4. exact E4.
Qed.

(* [comment removed for export] *)
Lemma sub_fp_inner : forall lo hi hi' (XSc XS W Wc : list (Z * Z)),
  hi' <= hi -> Forall (covered (lo, hi) (XSc ++ W)) Wc -> sub_fp ((lo, hi') :: XS ++ Wc) ((lo, hi) :: (XSc ++ XS) ++ W).
Proof.
  intros lo hi hi' XSc XS W Wc LE FA x Hx. cbn in Hx |- *. destruct Hx as [H0 Hx]. split; [lia|].
  rewrite <- app_assoc in Hx. apply outside_app in Hx. destruct Hx as [H1 Hx]. apply outside_app in Hx. destruct Hx as [H2 H3].
  apply outside_app. split; [exact H2|].
  apply (sub_fp_covered (lo, hi) [] (XSc ++ W) Wc FA). cbn. split; [exact H0|]. apply outside_app. split; assumption.
Qed.
Lemma sub_fp_inner0 : forall lohi (XSc XS W Wc : list (Z * Z)),
  Forall (covered lohi (XSc ++ W)) Wc -> sub_fp Wc (lohi :: (XSc ++ XS) ++ W).
Proof.
  intros [lo hi] XSc XS W Wc FA x Hx. cbn in Hx. destruct Hx as [H0 Hx].
  rewrite <- app_assoc in Hx. apply outside_app in Hx. destruct Hx as [H1 Hx]. apply outside_app in Hx. destruct Hx as [H2 H3].
  apply (sub_fp_covered (lo, hi) [] (XSc ++ W) Wc FA). cbn. split; [exact H0|]. apply outside_app. split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac ubal_any :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      lazymatch R with
      | context [Z.land ?x 7] =>
          first [ match goal with H : _ mod 16 = 0 |- _ => ubal_by H end
                | match goal with H : _ mod 8 = 0 |- _ => ubal_by H end
                | idtac ]
      | context [Z.land ?x 3] =>
          first [ match goal with H : _ mod 16 = 0 |- _ => ubal_by H end
                | match goal with H : _ mod 8 = 0 |- _ => ubal_by H end
                | match goal with H : _ mod 4 = 0 |- _ => ubal_by H end
                | idtac ]
      | _ => idtac
      end
  | _ => idtac
  end.


Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HX.
  Let HSM0 : stack_malloc_0_stmt H := proj1 (proj2 (proj2 HX)).
  (* [comment removed for export] *)
  Hypothesis BRMS : bioread_mem_stmt H.
  Hypothesis GDS : biogetdata_stmt H.
  Hypothesis NXS : bionext_stmt H.
  Hypothesis CFS : bioclearflags_stmt H.
  Hypothesis TFS : biotestflags_stmt H.
  Hypothesis DUS : decupdate_stmt H.
  Hypothesis DFS : decfinal_stmt H.
  Hypothesis DIS : decinit_stmt H.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => hide H end.

  (* [comment removed for export] *)
  Definition b64rd_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (LF : list fframe) (sA : as_St H) (rv : Z) (a : Z) (R : b64frep) (nr : Z) (mb : Z) (M : membio) (txt : list byte)
      (out : Z) (data : list Z) (outl : Z) (used : nat) (rb : option (Z * Z)) (W : list (Z * Z)) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (fl rt c fl' nr' : Z) (d' : list Z) (hdr junk junk' : list byte) (XS : list (Z * Z)),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ Forall (fs_scratch H LF) XS
      /\ munch ((lo, bv_unsigned sp) :: XS ++ W) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' a (bio_cells (b64f_bio (bf_with_hdr R fl rt nr mb (bf_prev R)))) /\ 0 <= fl < 2^31 /\ 0 <= rt < 2^32
      /\ length hdr = 32%nat /\ length junk = 2528%nat /\ rw_cells asegs m' (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk 0)
      /\ map bv_unsigned (firstn 4 (skipn 24 hdr)) = map (fun z => z mod 256) [c; c / 256; c / 65536; c / 16777216]
      /\ - 2^31 <= c < 2^31 /\ (rv = 0 -> c <= 0) /\ -1 <= rv <= outl /\ zlength data <= outl
      /\ ENCCTX H LB m' (bf_enc R) d' (bf_eid R)
      /\ MEMBIO H LB m' mb (mset M (Z.of_nat used) fl' nr')
      /\ bytes_at asegs m' (mb_buf M) txt
      /\ rw_cells asegs m' out [CB (length data) (map b8 data); CB (Z.to_nat outl - length data) junk']
      /\ METH_b64 m' /\ METH_mem m'
      /\ match rb with None => True | Some (rbp, v) => rw_cells asegs m' rbp [C8 (wz v)] /\ 0 <= v <= outl end
      /\ ACONST m' /\ as_RFS H LF m' /\ arelro_lib m' /\ as_RHEAP H sA LB m'.

  (* [comment removed for export] *)
  Definition XSF (ff fp : Z) : list (Z * Z) :=
    [(as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 64); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 8)].

  (* [comment removed for export] *)
  Ltac ext1_core MU WM MUc WMc tac :=
    lazymatch type of MU with munch ?W ?ma ?mb =>
    lazymatch type of MUc with munch _ mb ?mc =>
      let T := fresh "MUx" in
      assert (T : munch W ma mc)
        by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUc];
            let xa := fresh "xa" in let Hxa := fresh "Hxa" in
            intros xa Hxa; cbn [XSF outside app fst snd] in Hxa |- *; revert xa Hxa; tac; intros; lia);
      clear MU; rename T into MU;
      let T2 := fresh "WMx" in pose proof (wmono_trans _ _ _ _ WM WMc) as T2; clear WM; rename T2 into WM
    end end.
  Tactic Notation "ext1" constr(MU) constr(WM) constr(MUc) constr(WMc) "keeping" tactic3(tac) := ext1_core MU WM MUc WMc tac.
  (* [comment removed for export] *)
  Ltac carry_stg_core STg WMc tac :=
    lazymatch type of WMc with wmono _ _ ?mx =>
    lazymatch type of STg with stk ?sg _ ?l ?h =>
      let T := fresh "STx" in
      assert (T : stk sg mx l h) by (tac; eapply stk_transport_high; [exact STg| exact WMc| lia]);
      clear STg; rename T into STg
    end end.
  Tactic Notation "carry_stg" hyp(STg) constr(WMc) "by" tactic3(tac) := carry_stg_core STg WMc tac.

  (* [comment removed for export] *)
  Definition ardhead_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (LF : list fframe) (sA : as_St H) (a : Z) (R : b64frep) (mb : Z) (M : membio) (txt junk : list byte)
      (out outl lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists mh (fb ff fp vnum : Z) (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3' s8' s9' s10' t3 t4 t5 t6 j136 j152 w216 w224 : word)
                      (j0 j20 j2 j256 jb jt : list byte),
         ms' = MS (mkR ra' (Z_to_bv 64 fb) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp)) (Z_to_bv 64 fb) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 outl) s3' (Z_to_bv 64 (bf_ctx R + 12)) (Z_to_bv 64 (Z.shiftr (bf_ctx R + 8) 3 + ASHB)) (Z_to_bv 64 (bf_ctx R + 8)) (Z_to_bv 64 (bf_ctx R + 20))
                       s8' s9' s10' (Z_to_bv 64 ASHB) t3 t4 t5 t6)
                  F (Z_to_bv 64 ARD_HEAD) fc None mh (seg_rom asegs)
      /\ bv_unsigned sp - 400 <= fb <= bv_unsigned sp - 384 /\ fb mod 16 = 0 /\ fresh_frame H LF 0 ff fp
      /\ rw_cells asegs mh (bv_unsigned sp + -104) (ardsaves s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      /\ stk asegs mh (fb + 280) (bv_unsigned sp + -104) /\ stk asegs mh lo fb
      /\ rw_cells asegs mh fb [CB 8 j0]
      /\ rw_cells asegs mh (fb + 8) (ardslots (bf_ctx R) ff ff 0 mb a (ff + 32) (Z_to_bv 64 out) (Z_to_bv 64 outl) j136 j152 w216 w224 (Z_to_bv 64 0) j256)
      /\ rw_cells asegs mh ff [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 ADESCR_b64_read); C8 (Z_to_bv 64 P_b64_read)]
      /\ rw_cells asegs mh (ff + 32) [C4 (wz vnum)] /\ rw_cells asegs mh (ff + 36) [CB 20 j20] /\ rw_cells asegs mh (ff + 56) [C8 (Z_to_bv 64 fp)]
      /\ rw_cells asegs mh (Z.shiftr ff 3 + ASHB) b64rd_shpat /\ rw_cells asegs mh fp [C1 (b8 1)]
      /\ rw_cells asegs mh (bf_ctx R) (rdhdr 0 0 0 1 (bf_enc R)) /\ rw_cells asegs mh (bf_ctx R + 40) [CB 1502 jb] /\ rw_cells asegs mh (bf_ctx R + 1542) [CB 1024 jt]
      /\ rw_cells asegs mh (bf_ctx R + 2566) [CB 2 j2; C8 (wz 0); C8 (wz 0)]
      /\ ENCCTX H LB mh (bf_enc R) [] (bf_eid R) /\ MEMBIO H LB mh mb M /\ bytes_at asegs mh (mb_buf M) txt
      /\ rw_cells asegs mh out [CB (Z.to_nat outl) junk] /\ METH_b64 mh /\ METH_mem mh /\ mem_inv asegs mh
      /\ rw_cells asegs mh a (bio_cells (mkBIO A_b64_method 1 1 (Z.land (bf_flags R) (Z.lnot 15)) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0))
      /\ ACONST mh /\ as_RFS H ((0, ff, fp) :: LF) mh /\ arelro_lib mh /\ as_RHEAP H sA LB mh
      /\ B64F_shad mh a R /\ MEMBIO_shad mh mb M /\ PAYLOAD_shad mh M /\ OUT_shad mh out outl /\ shvis mh (bf_ctx R) (bf_ctx R + B64CTX_SIZE)
      /\ munch ((lo, bv_unsigned sp) :: XSF ff fp ++ [(a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92)]) m mh /\ wmono asegs m mh.

  Lemma ard_entry :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (LF : list fframe) (sA : as_St H)
           (a mb out outl lo : Z) (R : b64frep) (M : membio) (txt junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> 0 < outl < 2^31 ->
      B64F_fresh H LB m a R -> B64F_apart a R -> bf_next R = mb -> B64F_below a R lo -> ENCCTX H LB m (bf_enc R) [] (bf_eid R) ->
      MEMBIO H LB m mb M -> mb_pos M = 0 -> MEMBIO_below mb M lo -> MEMBIO_sep mb M -> bytes_at asegs m (mb_buf M) txt -> zlength txt = mb_len M ->
      zlength txt <= outl ->
      rw_cells asegs m out [CB (Z.to_nat outl) junk] -> memrd_out mb M out outl lo (bv_unsigned sp) ->
      Forall (fun b => out + outl <= blk_addr b \/ blk_addr b + blk_size b <= out) (blocks_B64F a R) ->
      Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M)) (blocks_B64F a R) ->
      Forall (fun b => mb_buf M + mb_len M <= blk_addr b \/ blk_addr b + blk_size b <= mb_buf M) (blocks_B64F a R) ->
      METH_b64 m -> METH_mem m ->
      B64F_shad m a R -> MEMBIO_shad m mb M -> PAYLOAD_shad m M -> OUT_shad m out outl ->                                  (* [comment removed for export] *)
      shvis m (bf_ctx R) (bf_ctx R + B64CTX_SIZE) -> in_app_mem (bf_ctx R) (bf_ctx R + B64CTX_SIZE) ->                   (* [comment removed for export] *)
      ACONST m -> arelro_lib m ->
      as_RFS H LF m -> (S (length LF) < AFS_MAXLIVE)%nat -> tp = Z_to_bv 64 ATP -> as_RHEAP H sA LB m -> bv_unsigned sp mod 16 = 0 ->  (* [comment removed for export] *)
      fsobj H LF out outl -> fsobj H LF (mb_buf M) (mb_len M) ->
      afs_write_ok H LF (out, out + outl) -> aclient_write_ok H LB (out, out + outl) -> AIMG_TOP <= out ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - B64READ_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (ardhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LF sA a R mb M txt junk out outl lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_b64_read) fc None m (seg_rom asegs)).
  Proof.
    intros until junk. intros A0 A1 A2 OUTL BF BAP BNXT BEL ENC MB POS0 MBL MSEP TXT TLEN TLE OUTC MO APO APM APT METHB METHM
           BSH MBSH PAY OSH CSV CAPP AC RL RFS LFN TP RH SP16 FO FP AWO ACWO OTOP ST CEIL LO MI RAE.
    subst a0 a1 a2. pose proof LO as LO_orig. pose proof MO as MO0. pose proof BEL as BEL0. pose proof MBL as MBL0. pose proof MSEP as MSEP0.
    pose proof BSH as BSH0. pose proof MBSH as MBSH0. pose proof PAY as PAY0. pose proof OSH as OSH0.
    unfold B64READ_STACK, BIOREAD_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, DECUPDATE_STACK, DECFINAL_STACK,
      DECINIT_STACK, DECBLOCK_STACK, FR_b64_read, FR_BIO_read, FR_bio_read_intern, FR_bread_conv, FR_BIO_eof, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl, FR_EVP_DecodeUpdate,
      FR_EVP_DecodeFinal, FR_EVP_DecodeInit, FR_evp_decodeblock_int, AFS_STACK, AINTRIN_STACK, BIOACC_STACK, FR_BIO_set_data in LO.
    unfold P_b64_read. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    pose proof BF as (HB & (bjunk & LJ & BX) & BLK & NONL & RT0 & NR0).
    pose proof BLK as (J1 & J2 & J3 & RBa & RBc & RBe & BFLR & RTR & NRR & NXR & PVR).
    pose proof RBa as (AP0 & A16 & _ & ATOP & ACE & AFSa & AAPa). pose proof RBc as (CP & C16 & _ & CTOP & CCE & AFSc & CAP). pose proof RBe as (EP & E16 & _ & ETOP & ECE & AFSe & EAP).
    pose proof BEL as (ABL1 & ABL2 & ABL3). pose proof BAP as (BA1 & BA2 & BA3).
    unfold BIO_SIZE, B64CTX_SIZE, ENCCTX_SIZE in ABL1, ABL2, ABL3, BA1, BA2, BA3, ATOP, ACE, AFSa, AAPa, CTOP, CCE, AFSc, CAP, ETOP, ECE, AFSe, EAP, CSV, CAPP.
    hide AFSa; hide AFSc; hide AFSe; hide BA1; hide BA2; hide BA3.
    (* [comment removed for export] *)
    membio_open m mb M MB MBL MBSH AC.
    pose proof RB0 as RBX || idtac.
    pose proof RB1 as (_ & _ & _ & _ & _ & AFSm & _). pose proof RB2 as (_ & _ & _ & _ & _ & AFSbb & _).
    pose proof RB3 as (_ & _ & _ & _ & _ & AFSbm & _). pose proof RB4 as (_ & _ & _ & _ & _ & AFSrp & _).
    hide AFSm; hide AFSbb; hide AFSbm; hide AFSrp.
    pose proof MSEP as ((SP1 & SP2 & SP3 & SP4 & SP5 & SP6) & PS1 & PS2 & PS3 & PS4).
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in SP1, SP2, SP3, SP4, SP5, SP6, PS1, PS2, PS3, PS4.
    hide SP1; hide SP2; hide SP3; hide SP4; hide SP5; hide SP6; hide PS1; hide PS2; hide PS3; hide PS4.
    destruct MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    clear OUTF. cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in OF1, OF2, OF3, OF4.
    unfold A_mem_buf_method, O_METH_BREAD in OUTM. hide OF1; hide OF2; hide OF3; hide OF4; hide OUTR; hide OUTB; hide OUTM.
    pose proof (Forall_inv APO) as OA1. pose proof (Forall_inv (Forall_inv_tail APO)) as OA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APO))) as OA3.
    cbn [blk_addr blk_size fst snd] in OA1, OA2, OA3. unfold BIO_SIZE, B64CTX_SIZE in OA1, OA2, OA3. hide OA1; hide OA2; hide OA3.
    pose proof (Forall_inv APT) as PT1. pose proof (Forall_inv (Forall_inv_tail APT)) as PT2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APT))) as PT3.
    cbn [blk_addr blk_size fst snd] in PT1, PT2, PT3. unfold BIO_SIZE, B64CTX_SIZE in PT1, PT2, PT3. hide PT1; hide PT2; hide PT3.
    destruct PAY as (PACC & PVIS & PAPP). destruct OSH as (OACC & OVIS & OAPP & OAOK). destruct BSH as (SHba & SHc & SHe).
    pose proof (aapp_not_shadowland _ _ AAPa) as NSba. pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_not_shadowland _ _ EAP) as NSe.
    pose proof (aapp_bounds _ _ AAPa ltac:(lia)) as (_ & _ & AHIba & _). pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & AHIc & _).
    pose proof (aapp_bounds _ _ EAP ltac:(lia)) as (_ & _ & AHIe & _).
    unfold ALOWSH_LO, AHI_LO, AAPP_HI in NSba, NSc, NSe, AHIba, AHIc, AHIe. hide NSba; hide NSc; hide NSe.
    pose proof OACC as (_ & OHI & _). unfold AAPP_HI in OHI.
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    unfold bio_cells, b64f_bio, wz in HB. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in HB.
    unfold A_b64_method in HB. rewrite BNXT, RT0, NR0 in HB.
    unfold b64ctx_fresh_cells, wz in BX.
    pose proof METHB as METHB0. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in METHB. norm_addr METHB.
    pose proof NM as MT || (pose proof METHM as MT; unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in MT; norm_addr MT).
    unfold zlength in TLEN, TLE.
    (* [comment removed for export] *)
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). pose proof (aapp_not_shadowland _ _ F4) as NSfs.
    unfold AFS_SIZE, ALOWSH_LO, AHI_LO, AIMG_TOP in F1, F2, NSfs. hide NSfs.
    pose proof (ACONST_uar _ AC) as [GUA UAR]. unfold AGOT_UAR, AUAR_CELL, wz in GUA, UAR.
    clear ACCa ACCbb ACCbm ACCrp.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    carve_frame 104%nat ST. carve_frame 280%nat ST.
    unhide OUTR. go. hide OUTR.
    (* [comment removed for export] *)
    idtac. rewrite land_align32 by lia.
    remember (bv_unsigned sp + -384 - (bv_unsigned sp + -384) mod 32) as fb eqn:Hfb.
    assert (FBR : bv_unsigned sp - 400 <= fb <= bv_unsigned sp - 384 /\ fb mod 16 = 0).
    { subst fb. split; [Z.div_mod_to_equations; lia|]. rewrite <- Zminus_mod_idemp_r. Z.div_mod_to_equations. lia. }
    clear Hfb. destruct FBR as [FBR FB16].
    (* [comment removed for export] *)
    release_frame FR0 ST (bv_unsigned sp + -104).
    destruct (stk_split asegs _ lo fb _ ST ltac:(lia)) as [STc STm]. clear ST.
    destruct (stk_split asegs _ fb (fb + 280) _ STm ltac:(lia)) as [STs STg]. clear STm.
    destruct (stk_carve asegs _ fb (fb + 280) 280 STs ltac:(lia)) as [_ [jfr FRM]]. clear STs.
    replace (fb + 280 - Z.of_nat 280) with fb in FRM by lia. change (Z.of_nat 280) with 280 in FRM |- *.
    rename STc into ST.
    (* [comment removed for export] *)
    unhide OUTR. go. step. hide OUTR.
    (* [comment removed for export] *)
    assert (FWS : Forall (afs_write_ok H LF) [(lo, bv_unsigned sp)]).
    { constructor; [| constructor]. left. cbn [fst snd]. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE. clear - F2 CEIL ACEILB SPR LO; split; lia. }
    assert (CWS : Forall (aclient_write_ok H LB) [(lo, bv_unsigned sp)]) by (constructor; [left; cbn [fst snd]; lia| constructor]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (RFS1 : as_RFS H LF mx) by (eapply (ah_RFS_frame H HH); [exact RFS| exact MU0| exact WM| exact FWS]);
      assert (AC1 : ACONST mx) by (eapply ACONST_stack_frame7; [exact AC| exact MU0| exact WM| exact CEIL]);
      assert (RH1 : as_RHEAP H sA LB mx) by (eapply (ah_RHEAP_frame H HH); [exact RH| exact MU0| exact WM| exact CWS]);
      assert (RL1 : arelro_lib mx) by (eapply arelro_across; [exact RL| exact MU0| constructor; [cbn [fst]; pose proof aceil_range; lia| constructor]])
    end.
    pose proof (ah_thr H HH _ _ _ RH1) as THR1.
    pose proof HSM0 as SM. unfold stack_malloc_0_stmt, stack_malloc_stmt, AFS_MALLOC_0, AFS_STACK in SM.
    eapply evt_cut.
    { eapply SM with (lo := lo) (LF := LF); clear SM; rewrite ?unsigned_lit by lia;
        [exact RFS1| clear - LFN; lia| exact ST| exact CEIL| lia| assumption| exact TP| exact AC1| exact THR1]. }
    clear SM. unfold stack_malloc_post.
    intros ms' PO. change (fsz 0) with 64 in PO. change (fshn 0) with 8 in PO. unfold AFS_STACK, AFS_FLAGS in PO.
    change (Z.to_nat (64 - 40)) with 24%nat in PO. change (Z.to_nat 8) with 8%nat in PO.
    rewrite ?unsigned_lit in PO by lia.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & ff & fp & jk1 & jk2
                    & -> & MUc & WMc & MI2 & ST2 & RFS2 & FFR & SHD & FPC & AC2).
    lazymatch type of MUc with munch _ ?mx _ => tryif is_var mx then (try rename m1 into m1_pre; rename mx into m1) else set (m1 := mx) in * end.
    replace (ret_pc (Z_to_bv 64 ARD_RA_SM)) with (Z_to_bv 64 ARD_RA_SM) by (symmetry; apply ret_pc_even; [unfold ARD_RA_SM; lia| reflexivity]).
    (* [comment removed for export] *)
    pose proof (fresh_of_RFS H HH _ _ _ _ _ RFS2) as FRESH.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 0) with 64 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    pose proof (proj1 FRESH) as AFR.
    pose proof (SHAD_rw_cells _ _ _ SHD) as SHC. change (poison_bytes 8 0) with [b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0; b8 0] in SHC. cbn [length] in SHC. clear SHD.
    assert (APff : aapp ff 64) by (clear - FB3 FF5 FF6; eapply aapp_sub; [exact FB3| lia| unfold AFS_SIZE; lia]).
    assert (APfp : aapp fp 1) by (clear - FB3 FP3 FP4; eapply aapp_sub; [exact FB3| lia| unfold AFS_SIZE; lia]).
    assert (SHF : ASHADOW_BASE <= Z.shiftr ff 3 + ASHB /\ Z.shiftr ff 3 + ASHB + 8 <= AHI_LO).
    { unfold ASHB. rewrite <- ASHADOW_BASE_val, (sh_shiftr ff) by lia. clear - APff FF1. pose proof (sh_aapp_range ff 64 APff ltac:(lia)) as (Q1 & Q2 & Q3).
      change (nsh 64) with 8 in Q2. split; [unfold sh; Z.div_mod_to_equations; lia| lia]. }
    pose proof SHF as [SHF1 SHF2]. unfold ASHB in SHF1, SHF2. rewrite ASHADOW_BASE_val in SHF1. unfold AHI_LO in SHF2.
    rewrite <- (sh_shiftr ff) in SHC, MUc by lia. rewrite ASHADOW_BASE_val in SHC, MUc.
    pose proof (aapp_not_shadowland _ _ APff) as NSff. pose proof (aapp_not_shadowland _ _ APfp) as NSfp. unfold ALOWSH_LO, AHI_LO in NSff, NSfp.
    (* [comment removed for export] *)
    pose proof (fsobj_windows H HH LF out outl 0 ff fp _ RFS1 FO FRESH ltac:(clear - OUTP; lia) ltac:(clear - OUTL; lia) ltac:(clear - OHI; unfold AAPP_HI; lia)) as (OW1 & OW2 & OW3 & OW4).
    pose proof (fsobj_windows H HH LF (mb_buf M) (mb_len M) 0 ff fp _ RFS1 FP FRESH ltac:(clear - BUFP; lia) ltac:(clear - LENR; lia) ltac:(clear - BUFH; acb; unfold AAPP_HI; lia)) as (PW1 & PW2 & PW3 & PW4).
    change (fsz 0) with 64 in OW1, PW1. change (fshn 0) with 8 in OW2, PW2. unfold AFS_FLAGS in OW4, PW4.
    rewrite <- (sh_shiftr ff) in OW2, PW2 by lia. rewrite ASHADOW_BASE_val in OW2, PW2.
    hide OW1; hide OW2; hide OW3; hide OW4; hide PW1; hide PW2; hide PW3; hide PW4.
    (* [comment removed for export] *)
    carry1k MUc WMc FR by (clear - FR MUc WMc FBR SPR LO CEIL ACEILB FB2 FF6 FP2 FP4 SHF2).
    carry1k MUc WMc FRM by (clear - FRM MUc WMc FBR SPR LO CEIL ACEILB FB2 FF6 FP2 FP4 SHF2).
    carry1k MUc WMc STg by (clear - STg MUc WMc FBR SPR LO CEIL ACEILB FB2 FF6 FP2 FP4 SHF2).
    carry1k MUc WMc HB by (clear - HB MUc WMc FBR SPR LO ABL1 AFSa NSba FF5 FF6 FP3 FP4 SHF1 SHF2; unhide AFSa; unhide NSba; unfold AFS_SIZE in AFSa).
    carry1k MUc WMc BX by (clear - BX LJ MUc WMc FBR SPR LO ABL2 AFSc NSc FF5 FF6 FP3 FP4 SHF1 SHF2; unhide AFSc; unhide NSc; unfold AFS_SIZE in AFSc).
    (* [comment removed for export] *)
    assert (MU1 : munch ((lo, fb + 280) :: XSF ff fp ++ [(a, a + 128); (bf_ctx R, bf_ctx R + 2584)]) m1 m2)
      by (eapply munch_weaken; [| exact MUc]; intros xa Hxa; cbn [XSF outside app fst snd] in Hxa |- *; clear - xa Hxa FBR LO SPR LO0; lia).
    assert (MUA : munch ((lo, bv_unsigned sp) :: XSF ff fp ++ [(a, a + 128); (bf_ctx R, bf_ctx R + 2584)]) m m2)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MU0]| eapply munch_weaken; [| exact MUc]];
          intros xa Hxa; cbn [XSF outside app fst snd] in Hxa |- *; clear - xa Hxa FBR LO SPR LO0; lia).
    pose proof WMc as WM1. pose proof (wmono_trans _ _ _ _ WM WMc) as WMA. clear MUc WMc MI MU0 WM.
    pose proof (munch_refl [(lo, fb + 280); (ff, ff + 64); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 8); (a, a + 128); (bf_ctx R, bf_ctx R + 2584)] m2) as MU2.
    pose proof (wmono_refl asegs m2) as WM2.
    assert (FXf : Forall (fs_scratch H LF) (XSF ff fp)).
    { pose proof (fs_scratch_of_fresh H _ _ _ _ FRESH) as FS4. change (fsz 0) with 64 in FS4. change (fshn 0) with 8 in FS4. unfold AFS_FLAGS in FS4.
      rewrite <- (sh_shiftr ff) in FS4 by lia. rewrite ASHADOW_BASE_val in FS4. exact FS4. }
    assert (AW2 : Forall appwin [(a, a + 128); (bf_ctx R, bf_ctx R + 2584)]).
    { unhide NSba. unhide NSc. unfold appwin, AHI_LO. rewrite ASHADOW_BASE_val.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [clear - NSba| clear - NSc]; lia. }
    assert (AW3 : Forall appwin [(a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92)]).
    { unhide NSba. unhide NSc. unhide NSe. unfold appwin, AHI_LO. rewrite ASHADOW_BASE_val.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [clear - NSba| clear - NSc| clear - NSe]; lia. }
    hide NSba. hide NSc. hide NSe.
    assert (Fa : fsobj H LF a 128) by (apply fsobj_outside; unhide AFSa; clear - AFSa; unfold AFS_SIZE in *; lia).
    assert (Fc : fsobj H LF (bf_ctx R) 2584) by (apply fsobj_outside; unhide AFSc; clear - AFSc; unfold AFS_SIZE in *; lia).
    assert (Fe : fsobj H LF (bf_enc R) 92) by (apply fsobj_outside; unhide AFSe; clear - AFSe; unfold AFS_SIZE in *; lia).
    assert (BOK : bio_ok (mkBIO A_b64_method 1 1 (bf_flags R) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0)).
    { unfold bio_ok; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite].
      unfold A_b64_method. clear - BFLR CP CCE AP ACE ACEILB PVR BL1 LO SPR. lia. }
    clear ST. rename ST2 into ST.
    (* [comment removed for export] *)
    apply (arw_cells_recut _ _ _ [C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0)]) in SHC; [| cbn; repeat split; exact I| reflexivity].
    rewrite <- (Z_to_bv_bv_unsigned sp). eapply evt_cut.
    { eapply apro_b; try exact FRM; try exact FFR; try exact SHC; try exact ST; try exact CEIL; try exact MI2.
      all: clear - OUTP OB OUTL FF1 FF2 FF5 FF6 F1 F2 LO0 FBR SPR LO CEIL ACEILB NSff SHF1 SHF2; unfold ASHB, ALOWSH_LO, AHI_LO; rewrite ?ASHADOW_BASE_val; lia. }
    cbv beta. intros ms3 (m3 & -> & MUc & WMc & MI3 & ST3 & FRM3 & FFR3 & SHC3). clear FRM FFR SHC MI2 ST. rename ST3 into ST. rename MI3 into MI.
    unfold ASHB in MUc, SHC3.
    carry1k MUc WMc HB by (clear - HB MUc WMc ABL1 FBR LO SPR AFSa NSba FF5 FF6 SHF1 SHF2; unhide AFSa; unhide NSba; unfold AFS_SIZE in AFSa).
    carry1k MUc WMc BX by (clear - BX LJ MUc WMc ABL2 FBR LO SPR AFSc NSc FF5 FF6 SHF1 SHF2; unhide AFSc; unhide NSc; unfold AFS_SIZE in AFSc).
    carry1k MUc WMc FR by (clear - FR MUc WMc FBR LO SPR CEIL ACEILB FF2 SHF2).
    carry1k MUc WMc FPC by (clear - FPC MUc WMc FBR LO SPR CEIL FP2 FF2 NSfp SHF1 SHF2).
    carry_stg STg WMc by (clear - STg WMc CEIL ACEILB LO FBR).
    ext1 MUA WMA MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU1 WM1 MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU2 WM2 MUc WMc keeping (clear - FBR LO SPR LO0).
    clear MUc WMc.
    (* [comment removed for export] *)
    assert (ACX : ACONST m3).
    { clear - AC2 MU2 WM2 CEIL ACEILB LO FBR LO0 FB3 APfp APff FF1 AAPa CAP HCEIL.
      eapply ACONST_frame; [exact AC2| exact MU2| exact WM2|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
      - eapply aconst_ok_aapp; [exact APff| cbn; lia| cbn; lia].
      - apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; change (12599296 / 8) with 1574912;
          rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia.
      - eapply aconst_ok_aapp; [exact AAPa| cbn; lia| cbn; lia].
      - eapply aconst_ok_aapp; [exact CAP| cbn; lia| cbn; lia]. }
    assert (SHaX : addressable m3 a 128).
    { eapply (addressable_across3 H HH); [exact SHba| exact RFS| exact Fa| clear - AP0; lia| clear - AHIba; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW2]. }
    pose proof GDS as G. unfold biogetdata_stmt, bioacc_stmt_at in G.
    eapply evt_cut.
    { eapply G with (lo := lo) (a := a) (x := ff) (B := mkBIO A_b64_method 1 1 (bf_flags R) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0); clear G.
      all: lazymatch goal with
           | |- rw_cells _ _ _ (bio_cells _) => unfold bio_cells, wz, A_b64_method; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; exact HB
           | |- bio_ok _ => exact BOK
           | |- addressable _ _ _ => exact SHaX
           | |- BIO_ranges _ _ => exact RBa
           | |- ACONST _ => exact ACX
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - FBR SPR LO LO0; lia); exact ST
           | |- mem_inv _ _ => exact MI
           | |- aceil <= _ => exact CEIL
           | |- _ mod 2 = 0 => unfold ARD_RA_GD; rewrite unsigned_lit by (clear; lia); reflexivity
           | |- _ <= bv_unsigned _ - _ => unfold BIOACC_STACK, FR_BIO_set_data; rewrite unsigned_lit by (clear - FBR SPR LO LO0; lia); clear - LO FBR; lia
           | |- _ => try reflexivity
           end.
      all: try (unfold BIO_SIZE; clear - ABL1; lia).
      all: try (clear - FF1 FF2 ACEILB; lia). }
    clear G HB ACX SHaX. unfold bioacc_post, BIO_SIZE. cbn [bio_ptr].
    intros ms4 PO. destruct PO as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m4 & -> & MUc & WMc & MI4 & ACX & ST4 & HB).
    rewrite unsigned_lit in MUc, ST4 by (clear - FBR SPR LO LO0; lia). clear MI ST. rename MI4 into MI. rename ST4 into ST.
    carry1k MUc WMc FRM3 by (clear - FRM3 MUc WMc ABL1 LO FBR SPR).
    carry1k MUc WMc FFR3 by (clear - FFR3 MUc WMc FF2 CEIL AFSa FF5 FF6; unhide AFSa; unfold AFS_SIZE in AFSa).
    carry1k MUc WMc SHC3 by (clear - SHC3 MUc WMc SHF1 SHF2 ACEILB CEIL NSba; unhide NSba).
    carry1k MUc WMc FPC by (clear - FPC MUc WMc FP2 FF2 CEIL AFSa FP3 FP4; unhide AFSa; unfold AFS_SIZE in AFSa).
    carry1k MUc WMc BX by (clear - BX LJ MUc WMc ABL2 BA1; unhide BA1).
    carry1k MUc WMc FR by (clear - FR MUc WMc ABL1 LO FBR SPR).
    carry_stg STg WMc by (clear - STg WMc CEIL ACEILB LO FBR).
    ext1 MUA WMA MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU1 WM1 MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU2 WM2 MUc WMc keeping (clear - FBR LO SPR LO0).
    clear MUc WMc.
    replace (ret_pc (Z_to_bv 64 ARD_RA_GD)) with (Z_to_bv 64 ARD_RA_GD) by (symmetry; apply ret_pc_even; [unfold ARD_RA_GD; lia| reflexivity]).
    unfold bio_cells, wz, A_b64_method in HB; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in HB.
    (* [comment removed for export] *)
    eapply evt_cut; [apply apro_c with (ff := ff)|]. cbv beta. intros ms5 ->.
    (* [comment removed for export] *)
    assert (SHaX : addressable m4 a 128).
    { eapply (addressable_across3 H HH); [exact SHba| exact RFS| exact Fa| clear - AP0; lia| clear - AHIba; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW2]. }
    pose proof NXS as G. unfold bionext_stmt in G.
    eapply evt_cut.
    { eapply G with (lo := lo) (a := a) (x := bv_unsigned w3) (B := mkBIO A_b64_method 1 1 (bf_flags R) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0); clear G.
      all: lazymatch goal with
           | |- rw_cells _ _ _ (bio_cells _) => unfold bio_cells, wz, A_b64_method; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; exact HB
           | |- bio_ok _ => exact BOK
           | |- addressable _ _ _ => exact SHaX
           | |- BIO_ranges _ _ => exact RBa
           | |- ACONST _ => exact ACX
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - FBR SPR LO LO0; lia); exact ST
           | |- mem_inv _ _ => exact MI
           | |- aceil <= _ => exact CEIL
           | |- _ mod 2 = 0 => unfold ARD_RA_NX; rewrite unsigned_lit by (clear; lia); reflexivity
           | |- _ <= bv_unsigned _ - _ => unfold BIOACC_STACK, FR_BIO_set_data; rewrite unsigned_lit by (clear - FBR SPR LO LO0; lia); clear - LO FBR; lia
           | |- 0 < _ => exact AP0
           | |- ?w = Z_to_bv 64 (bv_unsigned ?w) => symmetry; apply Z_to_bv_bv_unsigned
           | |- 0 <= bv_unsigned ?w < _ => pose proof (aword_range w); lia
           | |- _ => try reflexivity
           end.
      all: try (unfold BIO_SIZE; clear - ABL1; lia).
      all: match goal with |- ?G => idtac "NX-LEFT:" G end. }
    clear G HB ACX SHaX. unfold bioacc_post, BIO_SIZE. cbn [bio_next].
    intros ms6 PO. destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m6 & -> & MUc & WMc & MI6 & ACX & ST6 & HB).
    rewrite unsigned_lit in MUc, ST6 by (clear - FBR SPR LO LO0; lia). clear MI ST. rename MI6 into MI. rename ST6 into ST.
    carry1k MUc WMc FRM3 by (clear - FRM3 MUc WMc ABL1 LO FBR SPR).
    carry1k MUc WMc FFR3 by (clear - FFR3 MUc WMc FF2 CEIL AFSa FF5 FF6; unhide AFSa; unfold AFS_SIZE in AFSa).
    carry1k MUc WMc SHC3 by (clear - SHC3 MUc WMc SHF1 SHF2 ACEILB CEIL NSba; unhide NSba).
    carry1k MUc WMc FPC by (clear - FPC MUc WMc FP2 FF2 CEIL AFSa FP3 FP4; unhide AFSa; unfold AFS_SIZE in AFSa).
    carry1k MUc WMc BX by (clear - BX LJ MUc WMc ABL2 BA1; unhide BA1).
    carry1k MUc WMc FR by (clear - FR MUc WMc ABL1 LO FBR SPR).
    carry_stg STg WMc by (clear - STg WMc CEIL ACEILB LO FBR).
    ext1 MUA WMA MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU1 WM1 MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU2 WM2 MUc WMc keeping (clear - FBR LO SPR LO0).
    clear MUc WMc.
    replace (ret_pc (Z_to_bv 64 ARD_RA_NX)) with (Z_to_bv 64 ARD_RA_NX) by (symmetry; apply ret_pc_even; [unfold ARD_RA_NX; lia| reflexivity]).
    unfold bio_cells, wz, A_b64_method in HB; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in HB.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply apro_d; [clear - CP CCE ACEILB; lia| clear - AP BL1 LO SPR; lia| exact FRM3| exact ST| exact CEIL| clear - LO FBR; lia| clear - LO0 LO FBR; lia
                     | clear - FBR; lia| clear - SPR; lia| exact MI]. }
    cbv beta. intros ms7 (m7 & -> & MUc & WMc & MI7 & ST7 & FRM7). clear FRM3 MI ST. rename MI7 into MI. rename ST7 into ST.
    assert (ACX7 : ACONST m7) by (eapply ACONST_stack_frame7; [exact ACX| exact MUc| exact WMc| clear - CEIL LO FBR; lia]). clear ACX. rename ACX7 into ACX.
    carry1k MUc WMc HB by (clear - HB MUc WMc ABL1 LO FBR SPR).
    carry1k MUc WMc FFR3 by (clear - FFR3 MUc WMc FF2 CEIL LO FBR).
    carry1k MUc WMc SHC3 by (clear - SHC3 MUc WMc SHF2 ACEILB CEIL LO FBR).
    carry1k MUc WMc FPC by (clear - FPC MUc WMc FP2 FF2 CEIL LO FBR).
    carry1k MUc WMc BX by (clear - BX LJ MUc WMc ABL2 LO FBR).
    carry1k MUc WMc FR by (clear - FR MUc WMc FBR SPR).
    carry_stg STg WMc by (clear - STg WMc CEIL ACEILB LO FBR).
    ext1 MUA WMA MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU1 WM1 MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU2 WM2 MUc WMc keeping (clear - FBR LO SPR LO0).
    clear MUc WMc.
    (* [comment removed for export] *)
    assert (SHaX : addressable m7 a 128).
    { eapply (addressable_across3 H HH); [exact SHba| exact RFS| exact Fa| clear - AP0; lia| clear - AHIba; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW2]. }
    pose proof CFS as G. unfold bioclearflags_stmt, bioacc_stmt_at in G.
    eapply evt_cut.
    { eapply G with (lo := lo) (a := a) (x := 15) (B := mkBIO A_b64_method 1 1 (bf_flags R) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0); clear G.
      all: lazymatch goal with
           | |- rw_cells _ _ _ (bio_cells _) => unfold bio_cells, wz, A_b64_method; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; exact HB
           | |- bio_ok _ => exact BOK
           | |- addressable _ _ _ => exact SHaX
           | |- BIO_ranges _ _ => exact RBa
           | |- ACONST _ => exact ACX
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - FBR SPR LO LO0; lia); exact ST
           | |- mem_inv _ _ => exact MI
           | |- aceil <= _ => exact CEIL
           | |- _ mod 2 = 0 => unfold ARD_RA_CF; rewrite unsigned_lit by (clear; lia); reflexivity
           | |- _ <= bv_unsigned _ - _ => unfold BIOACC_STACK, FR_BIO_set_data; rewrite unsigned_lit by (clear - FBR SPR LO LO0; lia); clear - LO FBR; lia
           | |- _ => try reflexivity
           end.
      all: try (unfold BIO_SIZE; clear - ABL1; lia).
      all: match goal with |- ?G => idtac "CF-LEFT:" G end. }
    clear G HB ACX SHaX. unfold bioacc_post, BIO_SIZE, bio_with_flags. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite].
    intros ms8 PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m8 & -> & MUc & WMc & MI8 & ACX & ST8 & HB).
    rewrite unsigned_lit in MUc, ST8 by (clear - FBR SPR LO LO0; lia). clear MI ST. rename MI8 into MI. rename ST8 into ST.
    carry1k MUc WMc FRM7 by (clear - FRM7 MUc WMc ABL1 LO FBR SPR).
    carry1k MUc WMc FFR3 by (clear - FFR3 MUc WMc FF2 CEIL AFSa FF5 FF6; unhide AFSa; unfold AFS_SIZE in AFSa).
    carry1k MUc WMc SHC3 by (clear - SHC3 MUc WMc SHF1 SHF2 ACEILB CEIL NSba; unhide NSba).
    carry1k MUc WMc FPC by (clear - FPC MUc WMc FP2 FF2 CEIL AFSa FP3 FP4; unhide AFSa; unfold AFS_SIZE in AFSa).
    carry1k MUc WMc BX by (clear - BX LJ MUc WMc ABL2 BA1; unhide BA1).
    carry1k MUc WMc FR by (clear - FR MUc WMc ABL1 LO FBR SPR).
    carry_stg STg WMc by (clear - STg WMc CEIL ACEILB LO FBR).
    ext1 MUA WMA MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU1 WM1 MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU2 WM2 MUc WMc keeping (clear - FBR LO SPR LO0).
    clear MUc WMc.
    replace (ret_pc (Z_to_bv 64 ARD_RA_CF)) with (Z_to_bv 64 ARD_RA_CF) by (symmetry; apply ret_pc_even; [unfold ARD_RA_CF; lia| reflexivity]).
    (* [comment removed for export] *)
    assert (SHcX : addressable m8 (bf_ctx R) 2584).
    { eapply (addressable_across3 H HH); [exact SHc| exact RFS| exact Fc| clear - CP; lia| clear - AHIc; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW2]. }
    assert (ACC8 : accessible m8 (bf_ctx R) B64CTX_SIZE) by (eapply addressable_accessible; [exact SHcX| lia| unfold B64CTX_SIZE; lia| clear - AHIc; unfold AAPP_HI; lia]).
    clear SHcX.
    eapply evt_cut.
    { eapply apro_e with (enc := bf_enc R); [exact CP| exact C16| exact ABL2| exact CAP| exact ACC8| clear - EP ECE ACEILB; lia| exact FRM7| exact BX| exact ST| exact CEIL
                     | clear - LO FBR; lia| clear - LO0 LO FBR; lia| clear - FBR; lia| clear - SPR; lia| exact MI]. }
    cbv beta. intros ms9 (m9 & -> & MUc & WMc & MI9 & ST9 & FRM9 & CTX9). clear FRM7 BX ACC8 MI ST. rename MI9 into MI. rename ST9 into ST.
    assert (APc20 : aapp (bf_ctx R) 20) by (clear - CAP; eapply aapp_sub; [exact CAP| lia| lia]).
    assert (ACX9 : ACONST m9) by (eapply ACONST_stack_obj6; [exact ACX| exact MUc| exact WMc| clear - CEIL LO FBR; lia| exact APc20| clear - CCE ACEILB; lia]). clear ACX. rename ACX9 into ACX.
    carry1k MUc WMc HB by (clear - HB MUc WMc ABL1 LO FBR SPR BA1; unhide BA1).
    carry1k MUc WMc FFR3 by (clear - FFR3 MUc WMc FF2 CEIL LO FBR AFSc FF5 FF6; unhide AFSc; unfold AFS_SIZE in AFSc).
    carry1k MUc WMc SHC3 by (clear - SHC3 MUc WMc SHF1 SHF2 ACEILB CEIL LO FBR NSc; unhide NSc).
    carry1k MUc WMc FPC by (clear - FPC MUc WMc FP2 FF2 CEIL LO FBR AFSc FP3 FP4; unhide AFSc; unfold AFS_SIZE in AFSc).
    carry1k MUc WMc FR by (clear - FR MUc WMc FBR SPR ABL2 LO).
    carry_stg STg WMc by (clear - STg WMc CEIL ACEILB LO FBR).
    ext1 MUA WMA MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU1 WM1 MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU2 WM2 MUc WMc keeping (clear - FBR LO SPR LO0).
    clear MUc WMc.
    (* [comment removed for export] *)
    assert (ENC8 : ENCCTX H LB m9 (bf_enc R) [] (bf_eid R)).
    { eapply ENCCTX_transport; [exact MUA| exact WMA| | exact ENC].
      unhide AFSe. unhide NSe. unhide BA2. unhide BA3. clear - ABL3 LO SPR AFSe FF5 FF6 FP3 FP4 SHF1 SHF2 NSe BA2 BA3. cbn. unfold AFS_SIZE in AFSe. lia. }
    pose proof (ENCCTX_CB92 H _ _ _ _ _ ENC8) as ((old & EC8) & _ & _ & _).
    assert (SHeX : addressable m9 (bf_enc R) 92).
    { eapply (addressable_across3 H HH); [exact SHe| exact RFS| exact Fe| clear - EP; lia| clear - AHIe; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW2]. }
    assert (ACC9 : accessible m9 (bf_enc R) ENCCTX_SIZE) by (eapply addressable_accessible; [exact SHeX| lia| unfold ENCCTX_SIZE; lia| clear - AHIe; unfold AAPP_HI; lia]).
    clear SHeX.
    pose proof DIS as G. unfold decinit_stmt in G.
    eapply evt_cut.
    { eapply G with (lo := lo) (a := bf_enc R) (LB := LB) (p := bf_eid R); clear G.
      all: lazymatch goal with
           | |- rw_cells _ _ _ [CB 92 _] => exact EC8
           | |- In _ _ => exact J3
           | |- ablock_range _ _ _ => exact RBe
           | |- accessible _ _ _ => exact ACC9
           | |- ACONST _ => exact ACX
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - FBR SPR LO LO0; lia); exact ST
           | |- mem_inv _ _ => exact MI
           | |- aceil <= _ => exact CEIL
           | |- _ mod 2 = 0 => unfold ARD_RA_DI1; rewrite unsigned_lit by (clear; lia); reflexivity
           | |- _ <= bv_unsigned _ - _ => unfold DECINIT_STACK, FR_EVP_DecodeInit; rewrite unsigned_lit by (clear - FBR SPR LO LO0; lia); clear - LO FBR; lia
           | |- _ => try reflexivity
           end.
      all: try (unfold ENCCTX_SIZE; clear - ABL3; lia).
      all: match goal with |- ?G => idtac "DI-LEFT:" G end. }
    clear G EC8 ACX ACC9 ENC8. unfold c8_post, ENCCTX_foot, ENCCTX_SIZE.
    intros ms10 PO. destruct PO as (v0 & v1' & v2' & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3' & v4' & v5' & v6' & m10 & -> & -> & MUc & WMc & MI10 & ACX & ST10 & ENC10 & _).
    rewrite unsigned_lit in MUc, ST10 by (clear - FBR SPR LO LO0; lia). clear MI ST. rename MI10 into MI. rename ST10 into ST.
    carry1k MUc WMc HB by (clear - HB MUc WMc ABL1 LO FBR SPR BA2; unhide BA2).
    carry1k MUc WMc FRM9 by (clear - FRM9 MUc WMc ABL3 LO FBR SPR).
    carry1k MUc WMc CTX9 by (clear - CTX9 LJ MUc WMc ABL2 BA3; unhide BA3).
    carry1k MUc WMc FFR3 by (clear - FFR3 MUc WMc FF2 CEIL AFSe FF5 FF6; unhide AFSe; unfold AFS_SIZE in AFSe).
    carry1k MUc WMc SHC3 by (clear - SHC3 MUc WMc SHF1 SHF2 ACEILB CEIL NSe; unhide NSe).
    carry1k MUc WMc FPC by (clear - FPC MUc WMc FP2 FF2 CEIL AFSe FP3 FP4; unhide AFSe; unfold AFS_SIZE in AFSe).
    carry1k MUc WMc FR by (clear - FR MUc WMc ABL3 LO FBR SPR).
    carry_stg STg WMc by (clear - STg WMc CEIL ACEILB LO FBR).
    (* [comment removed for export] *)
    assert (MUA' : munch ((lo, bv_unsigned sp) :: XSF ff fp ++ [(a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92)]) m m10).
    { eapply munch_trans; [eapply munch_weaken; [| exact MUA]| eapply munch_weaken; [| exact MUc]];
        intros xa Hxa; cbn [XSF outside app fst snd] in Hxa |- *; clear - xa Hxa FBR LO SPR LO0; lia. }
    assert (MU1' : munch ((lo, fb + 280) :: XSF ff fp ++ [(a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92)]) m1 m10).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MUc]];
        intros xa Hxa; cbn [XSF outside app fst snd] in Hxa |- *; clear - xa Hxa FBR LO SPR LO0; lia. }
    assert (MU2' : munch [(lo, fb + 280); (ff, ff + 64); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 8); (a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92)] m2 m10).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MUc]];
        intros xa Hxa; cbn [XSF outside app fst snd] in Hxa |- *; clear - xa Hxa FBR LO SPR LO0; lia. }
    pose proof (wmono_trans _ _ _ _ WMA WMc) as WMA'. pose proof (wmono_trans _ _ _ _ WM1 WMc) as WM1'. pose proof (wmono_trans _ _ _ _ WM2 WMc) as WM2'.
    clear MUA MU1 MU2 WMA WM1 WM2 MUc WMc. rename MUA' into MUA. rename MU1' into MU1. rename MU2' into MU2. rename WMA' into WMA. rename WM1' into WM1. rename WM2' into WM2.
    replace (ret_pc (Z_to_bv 64 ARD_RA_DI1)) with (Z_to_bv 64 ARD_RA_DI1) by (symmetry; apply ret_pc_even; [unfold ARD_RA_DI1; lia| reflexivity]).
    (* [comment removed for export] *)
    assert (SHcX : addressable m10 (bf_ctx R) 2584).
    { eapply (addressable_across3 H HH); [exact SHc| exact RFS| exact Fc| clear - CP; lia| clear - AHIc; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW3]. }
    assert (ACC10 : accessible m10 (bf_ctx R) B64CTX_SIZE) by (eapply addressable_accessible; [exact SHcX| lia| unfold B64CTX_SIZE; lia| clear - AHIc; unfold AAPP_HI; lia]).
    clear SHcX.
    eapply evt_cut.
    { eapply apro_f with (enc := bf_enc R) (ff := ff) (mb := mb) (a := a); [exact OUTL| clear - FF1; lia| exact FF2| exact CP| exact C16| exact ABL2| exact CAP| exact ACC10| clear - EP ECE ACEILB; lia| exact FRM9| exact CTX9
                     | exact ST| exact CEIL| clear - LO FBR; lia| clear - LO0 LO FBR; lia| clear - FBR; lia| clear - SPR; lia| exact MI]. }
    cbv beta. intros msh (mh & j0 & j80 & j104 & j136 & j256 & -> & MUc & WMc & MIh & STh & FRMh & CTXh). clear FRM9 CTX9 ACC10 MI ST. rename MIh into MI. rename STh into ST.
    assert (ACXh : ACONST mh) by (eapply ACONST_stack_frame7; [exact ACX| exact MUc| exact WMc| clear - CEIL LO FBR; lia]). clear ACX. rename ACXh into ACX.
    carry1k MUc WMc HB by (clear - HB MUc WMc ABL1 LO FBR SPR).
    carry1k MUc WMc FFR3 by (clear - FFR3 MUc WMc FF2 CEIL LO FBR).
    carry1k MUc WMc SHC3 by (clear - SHC3 MUc WMc SHF2 ACEILB CEIL LO FBR).
    carry1k MUc WMc FPC by (clear - FPC MUc WMc FP2 FF2 CEIL LO FBR).
    carry1k MUc WMc FR by (clear - FR MUc WMc FBR SPR).
    carry_stg STg WMc by (clear - STg WMc CEIL ACEILB LO FBR).
    assert (ENCh : ENCCTX H LB mh (bf_enc R) [] (bf_eid R)) by (eapply ENCCTX_transport; [exact MUc| exact WMc| cbn; clear - ABL3 LO FBR; lia| exact ENC10]). clear ENC10.
    ext1 MUA WMA MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU1 WM1 MUc WMc keeping (clear - FBR LO SPR LO0). ext1 MU2 WM2 MUc WMc keeping (clear - FBR LO SPR LO0).
    clear MUc WMc.
    (* [comment removed for export] *)
    pose proof (ardframe_of_head _ _ _ _ _ _ _ _ _ _ _ _ _ FRMh) as (w136 & w152 & w216 & w224 & FR24 & SLOTS). clear FRMh.
    destruct (b64ctx_at_head _ _ _ _ LJ CTXh) as (HDh & BUFh & TMPh & TAILh). clear CTXh.
    (* [comment removed for export] *)
    destruct (proj1 (rw_cells_app asegs mh ff [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 ADESCR_b64_read); C8 (Z_to_bv 64 P_b64_read)]
                                  [C8 (Z_to_bv 64 fb); CB 24 jk2; C8 (Z_to_bv 64 fp)]) FFR3) as [FH1 FH2]. clear FFR3.
    cbn [cells_size csize Nat.add] in FH2. replace (ff + Z.of_nat 24) with (ff + 24) in FH2 by lia.
    destruct (proj1 (rw_cells_app asegs mh (ff + 24) [C8 (Z_to_bv 64 fb)] [CB 24 jk2; C8 (Z_to_bv 64 fp)]) FH2) as [FH3 FH4]. clear FH2.
    cbn [cells_size csize Nat.add] in FH4. replace (ff + 24 + Z.of_nat 8) with (ff + 32) in FH4 by lia.
    destruct (proj1 (rw_cells_app asegs mh (ff + 32) [CB 24 jk2] [C8 (Z_to_bv 64 fp)]) FH4) as [FH5 FH6]. clear FH4.
    cbn [cells_size csize Nat.add] in FH6. replace (ff + 32 + Z.of_nat 24) with (ff + 56) in FH6 by lia.
    destruct (rw_cells_CB_split asegs _ _ 24 4 jk2 FH5 ltac:(lia)) as [NUM J20]. clear FH5.
    change (24 - 4)%nat with 20%nat in J20. replace (ff + 32 + Z.of_nat 4) with (ff + 36) in J20 by lia.
    apply (rw_cells_CB4_C4_9 asegs mh (ff + 32) [] (firstn 4 jk2) []) in NUM. cbn [app] in NUM.
    (* [comment removed for export] *)
    pose proof (Forall_inv APM) as APM1. pose proof (Forall_inv APM1) as DJ_a_mb. pose proof (Forall_inv (Forall_inv_tail APM1)) as DJ_a_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM1))) as DJ_a_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM1)))) as DJ_a_rp.
    cbn [blk_addr blk_size fst snd] in DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp. clear APM1.
    pose proof (Forall_inv (Forall_inv_tail APM)) as APM2. pose proof (Forall_inv APM2) as DJ_c_mb. pose proof (Forall_inv (Forall_inv_tail APM2)) as DJ_c_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM2))) as DJ_c_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM2)))) as DJ_c_rp.
    cbn [blk_addr blk_size fst snd] in DJ_c_mb, DJ_c_bb, DJ_c_bm, DJ_c_rp. clear APM2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM))) as APM3. pose proof (Forall_inv APM3) as DJ_e_mb. pose proof (Forall_inv (Forall_inv_tail APM3)) as DJ_e_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM3))) as DJ_e_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM3)))) as DJ_e_rp.
    cbn [blk_addr blk_size fst snd] in DJ_e_mb, DJ_e_bb, DJ_e_bm, DJ_e_rp. clear APM3.
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, ENCCTX_SIZE in DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp, DJ_c_mb, DJ_c_bb, DJ_c_bm, DJ_c_rp, DJ_e_mb, DJ_e_bb, DJ_e_bm, DJ_e_rp.
    unfold ALOWSH_LO, AHI_LO in NSa, NSbb, NSbm, NSrp.
    assert (MBh : MEMBIO H LB mh mb M).
    { eapply MEMBIO_transport; [exact MUA| exact WMA| | | | | exact MB]; unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; cbn [XSF app].
      - unhide AFSm. clear - BL1 LO SPR AFSm NSa SHF1 SHF2 FF5 FF6 FP3 FP4 DJ_a_mb DJ_c_mb DJ_e_mb. unfold AFS_SIZE in AFSm. cbn. lia.
      - unhide AFSbb. clear - BL2 LO SPR AFSbb NSbb SHF1 SHF2 FF5 FF6 FP3 FP4 DJ_a_bb DJ_c_bb DJ_e_bb. unfold AFS_SIZE in AFSbb. cbn. lia.
      - unhide AFSbm. clear - BL3 LO SPR AFSbm NSbm SHF1 SHF2 FF5 FF6 FP3 FP4 DJ_a_bm DJ_c_bm DJ_e_bm. unfold AFS_SIZE in AFSbm. cbn. lia.
      - unhide AFSrp. clear - BL4 LO SPR AFSrp NSrp SHF1 SHF2 FF5 FF6 FP3 FP4 DJ_a_rp DJ_c_rp DJ_e_rp. unfold AFS_SIZE in AFSrp. cbn. lia. }
    (* [comment removed for export] *)
    assert (TXTh : bytes_at asegs mh (mb_buf M) txt).
    { eapply bytes_at_transport; [exact TXT| exact MU1|]. cbn [disjoint_from length app XSF fst snd].
      unhide PW1; unhide PW3; unhide PW4; unhide PT1; unhide PT2; unhide PT3.
      pose proof PAPP as PAPP'. unfold in_app_mem, AHI_LO, AAPP_HI in PAPP'. rewrite ASHADOW_BASE_val in PAPP'.
      repeat lazymatch goal with |- _ /\ _ => split end; try exact I;
        [ clear - TLEN BUFH CEIL LO FBR; lia | clear - TLEN PW4; lia | clear - TLEN PW3; lia | clear - TLEN PW1; lia
        | clear - TLEN PAPP' SHF1 SHF2 LENR; lia | clear - TLEN PT1; lia | clear - TLEN PT2; lia | clear - TLEN PT3; lia ]. }
    clear TXT. rename TXTh into TXT.
    assert (OUTCh : rw_cells asegs mh out [CB (Z.to_nat outl) junk]).
    { eapply rw_cells_transport; [exact OUTC| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize length app Nat.add XSF fst snd].
      rewrite Nat.add_0_r, Z2Nat.id by (clear - OUTL; lia).
      unhide OUTR; unhide OW1; unhide OW3; unhide OW4; unhide OA1; unhide OA2; unhide OA3.
      pose proof OAPP as OAPP'. unfold in_app_mem, AHI_LO, AAPP_HI in OAPP'. rewrite ASHADOW_BASE_val in OAPP'.
      repeat lazymatch goal with |- _ /\ _ => split end; try exact I;
        [ clear - OUTR FBR; lia | clear - OW4; lia | clear - OW3; lia | clear - OW1; lia
        | clear - OAPP' SHF1 SHF2 OUTL; lia | clear - OA1; lia | clear - OA2; lia | clear - OA3; lia ]. }
    clear OUTC. rename OUTCh into OUTC.
    assert (METHBh : METH_b64 mh).
    { unfold METH_b64 in METHB0 |- *. eapply rw_cells_transport; [exact METHB0| exact MUA| exact WMA|].
      unfold A_b64_method, O_METH_BREAD. clear - CEIL ACEILB FB1 FP3 FF5 SHF1 ATOP CTOP ETOP LO FBR SPR. cbn. lia. }
    assert (METHMh : METH_mem mh).
    { unfold METH_mem in METHM |- *. eapply rw_cells_transport; [exact METHM| exact MUA| exact WMA|].
      unfold A_mem_buf_method, O_METH_BREAD. clear - CEIL ACEILB FB1 FP3 FF5 SHF1 ATOP CTOP ETOP LO FBR SPR. cbn. lia. }
    (* [comment removed for export] *)
    assert (RFSh : as_RFS H ((0, ff, fp) :: LF) mh).
    { eapply (ah_RFS_frame H HH); [exact RFS2| exact MU2| exact WM2|].
      unhide AFSa; unhide AFSc; unhide AFSe; unhide NSfs. clear - CEIL ACEILB FB2 LO FBR AFSa AFSc AFSe ATOP CTOP ETOP NSfs SHF1 SHF2.
      unfold afs_write_ok, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - left. lia.
      - right. exists (0, ff, fp). split; [left; reflexivity|]. cbn. change (fsz 0) with 64. lia.
      - left. lia.
      - left. lia.
      - left. lia.
      - left. lia. }
    assert (RHh : as_RHEAP H sA LB mh).
    { eapply (ah_RHEAP_frame H HH); [exact RH1| exact MU1| exact WM1|].
      apply Forall_cons; [left; cbn [fst]; clear - CEIL; lia|]. apply (proj2 (Forall_app _ _ _)). split; [apply (fs_scratch_write_ok_Forall H LF); exact FXf|].
      repeat apply Forall_cons; try apply Forall_nil; right; right; left.
      - exists (bf_id R, a, 128). split; [exact J1| cbn; lia].
      - exists (bf_cid R, bf_ctx R, B64CTX_SIZE). split; [exact J2| cbn; unfold B64CTX_SIZE; lia].
      - exists (bf_eid R, bf_enc R, 92). split; [exact J3| cbn; lia]. }
    assert (RLh : arelro_lib mh).
    { eapply arelro_across; [exact RL| exact MUA|]. clear - CEIL ACEILB FB1 FP3 FF5 SHF1 ATOP CTOP ETOP. cbn [XSF app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
    (* [comment removed for export] *)
    assert (Fm : fsobj H LF mb 128) by (apply fsobj_outside; unhide AFSm; clear - AFSm; unfold AFS_SIZE in *; lia).
    assert (Fbb : fsobj H LF (mb_bb M) 16) by (apply fsobj_outside; unhide AFSbb; clear - AFSbb; unfold AFS_SIZE in *; lia).
    assert (Fbm : fsobj H LF (mb_bm M) 32) by (apply fsobj_outside; unhide AFSbm; clear - AFSbm; unfold AFS_SIZE in *; lia).
    assert (Frp : fsobj H LF (mb_rp M) 32) by (apply fsobj_outside; unhide AFSrp; clear - AFSrp; unfold AFS_SIZE in *; lia).
    assert (BSHh : B64F_shad mh a R).
    { unfold B64F_shad, BIO_SIZE, B64CTX_SIZE. split; [| split].
      - eapply (addressable_across3 H HH); [exact SHba| exact RFS| exact Fa| clear - AP0; lia| clear - AHIba; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW3].
      - eapply (addressable_across3 H HH); [exact SHc| exact RFS| exact Fc| clear - CP; lia| clear - AHIc; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW3].
      - eapply (addressable_across3 H HH); [exact SHe| exact RFS| exact Fe| clear - EP; lia| clear - AHIe; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW3]. }
    assert (MBSHh : MEMBIO_shad mh mb M).
    { unfold MEMBIO_shad, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. split; [| split; [| split]].
      - eapply (addressable_across3 H HH); [exact SHa| exact RFS| exact Fm| clear - AP; lia| clear - AHIa; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW3].
      - eapply (addressable_across3 H HH); [exact SHbb| exact RFS| exact Fbb| clear - BBP; lia| clear - AHIbb; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW3].
      - eapply (addressable_across3 H HH); [exact SHbm| exact RFS| exact Fbm| clear - BMP; lia| clear - AHIbm; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW3].
      - eapply (addressable_across3 H HH); [exact SHrp| exact RFS| exact Frp| clear - RPP; lia| clear - AHIrp; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW3]. }
    assert (PAYh : PAYLOAD_shad mh M).
    { pose proof PACC as (Q0 & Q1 & _). split; [| split; [| exact PAPP]].
      - eapply (accessible_across3 H HH); [exact PACC| exact RFS| exact FP| clear - LENR; lia| exact MUA| exact CEIL| exact FXf| exact AW3].
      - eapply (shvis_across3 H HH); [exact PVIS| exact RFS| exact FP| clear - Q0; lia| clear - LENR; lia| clear - Q1; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW3]. }
    assert (OSHh : OUT_shad mh out outl).
    { pose proof OACC as (Q0 & Q1 & _). split; [| split; [| split; [exact OAPP| exact OAOK]]].
      - eapply (accessible_across3 H HH); [exact OACC| exact RFS| exact FO| clear - OUTL; lia| exact MUA| exact CEIL| exact FXf| exact AW3].
      - eapply (shvis_across3 H HH); [exact OVIS| exact RFS| exact FO| clear - Q0; lia| clear - OUTL; lia| clear - Q1; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW3]. }
    assert (CSVh : shvis mh (bf_ctx R) (bf_ctx R + B64CTX_SIZE)).
    { unfold B64CTX_SIZE. eapply (shvis_across3 H HH); [exact CSV| exact RFS| exact Fc| clear - CP; lia| clear; lia| clear - AHIc; unfold AAPP_HI; lia| exact MUA| exact WMA| exact CEIL| exact FXf| exact AW3]. }
    (* [comment removed for export] *)
    apply evt_done. unfold ardhead_post. rewrite !(unsigned_lit (bv_unsigned sp)) by (clear - SPR; lia).
    eexists mh, fb, ff, fp. do 31 eexists.
    split; [reflexivity|].
    split; [exact FBR|]. split; [exact FB16|]. split; [exact FRESH|].
    split; [unfold ardsaves; exact FR|].
    split; [exact STg|]. split; [exact ST|].
    split; [exact FR24|]. split; [exact SLOTS|].
    split; [exact FH1|]. split; [exact NUM|]. split; [exact J20|]. split; [exact FH6|].
    split; [unfold ASHB; exact SHC3|]. split; [exact FPC|].
    split; [exact HDh|]. split; [exact BUFh|]. split; [exact TMPh|]. split; [exact TAILh|].
    split; [exact ENCh|]. split; [exact MBh|]. split; [exact TXT|].
    split; [exact OUTC|].
    split; [exact METHBh|]. split; [exact METHMh|].
    split; [exact MI|].
    split; [unfold bio_cells, wz, A_b64_method; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; exact HB|].
    split; [exact ACX|]. split; [exact RFSh|]. split; [exact RLh|]. split; [exact RHh|].
    split; [exact BSHh|]. split; [exact MBSHh|]. split; [exact PAYh|]. split; [exact OSHh|]. split; [exact CSVh|].
    split; [exact MUA| exact WMA].
  Qed.


  (* [comment removed for export] *)
  Lemma b64read_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (LF : list fframe) (sA : as_St H)
           (a mb out outl lo : Z) (R : b64frep) (M : membio) (txt junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> 0 < outl < 2^31 ->
      B64F_fresh H LB m a R -> B64F_apart a R -> bf_next R = mb -> B64F_below a R lo -> ENCCTX H LB m (bf_enc R) [] (bf_eid R) ->
      MEMBIO H LB m mb M -> mb_pos M = 0 -> MEMBIO_below mb M lo -> MEMBIO_sep mb M -> bytes_at asegs m (mb_buf M) txt -> zlength txt = mb_len M ->
      zlength txt <= outl ->
      rw_cells asegs m out [CB (Z.to_nat outl) junk] -> memrd_out mb M out outl lo (bv_unsigned sp) ->
      Forall (fun b => out + outl <= blk_addr b \/ blk_addr b + blk_size b <= out) (blocks_B64F a R) ->
      Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M)) (blocks_B64F a R) ->
      Forall (fun b => mb_buf M + mb_len M <= blk_addr b \/ blk_addr b + blk_size b <= mb_buf M) (blocks_B64F a R) ->
      METH_b64 m -> METH_mem m ->
      B64F_shad m a R -> MEMBIO_shad m mb M -> PAYLOAD_shad m M -> OUT_shad m out outl ->
      shvis m (bf_ctx R) (bf_ctx R + B64CTX_SIZE) -> in_app_mem (bf_ctx R) (bf_ctx R + B64CTX_SIZE) ->
      ACONST m -> arelro_lib m ->
      as_RFS H LF m -> (S (length LF) < AFS_MAXLIVE)%nat -> tp = Z_to_bv 64 ATP -> as_RHEAP H sA LB m -> bv_unsigned sp mod 16 = 0 ->
      fsobj H LF out outl -> fsobj H LF (mb_buf M) (mb_len M) ->
      afs_write_ok H LF (out, out + outl) -> aclient_write_ok H LB (out, out + outl) -> AIMG_TOP <= out ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - B64READ_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (b64rd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LF sA (br_rv (b64_read_spec (map bv_unsigned txt) outl)) a R (bf_nread R) mb M txt
                   out (br_out (b64_read_spec (map bv_unsigned txt) outl)) outl (br_used (b64_read_spec (map bv_unsigned txt) outl)) None
                   ((out, out + outl) :: B64F_foot a R ++ MEMBIO_foot mb M) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_b64_read) fc None m (seg_rom asegs)).
  Proof.
    intros until junk. intros A0 A1 A2 OUTL BF BAP BNXT BEL ENC MB POS0 MBL MSEP TXT TLEN TLE OUTC MO APO APM APT METHB METHM
           BSH MBSH PAY OSH CSV CAPP AC RL RFS LFN TP RH SP16 FO FP AWO ACWO OTOP ST CEIL LO MI RAE.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply ard_entry; [exact A0| exact A1| exact A2| exact OUTL| exact BF| exact BAP| exact BNXT| exact BEL| exact ENC| exact MB| exact POS0| exact MBL| exact MSEP
                       | exact TXT| exact TLEN| exact TLE| exact OUTC| exact MO| exact APO| exact APM| exact APT| exact METHB| exact METHM| exact BSH| exact MBSH| exact PAY
                       | exact OSH| exact CSV| exact CAPP| exact AC| exact RL| exact RFS| exact LFN| exact TP| exact RH| exact SP16| exact FO| exact FP| exact AWO| exact ACWO
                       | exact OTOP| exact ST| exact CEIL| exact LO| exact MI| exact RAE]. }
    cbv beta. clear TXT OUTC METHB METHM ST MI. intros msh HP. unfold ardhead_post in HP.
    destruct HP as (mh & fb & ff & fp & vnum & ra' & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s3' & q8 & q9 & q10 & u3 & u4 & u5 & u6
                    & j136 & j152 & w216 & w224 & j0 & j20 & j2 & j256 & jb & jt
                    & -> & FBR & FB16 & FRESH & FRs & STg & ST & FR24 & SLOTS & FH1 & NUM & J20 & FH6 & SHC & FPC & HD & BUF & TMP & TAIL
                    & ENCh & MBh & TXT & OUTC & METHBh & METHMh & MI & HB & ACh & RFSh & RLh & RHh & BSHh & MBSHh & PAYh & OSHh & CSVh & MUA & WMA).
    pose proof (aword_range sp) as SPR. pose proof aceil_range as ACR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof BF as (_ & (bjunk & LJ & _) & BLK & NONL & RT0 & NR0).
    pose proof BLK as (J1 & J2 & J3 & RBa & RBc & RBe & FLR & RTR & NRR & NXR & PVR).
    pose proof RBa as (AP0 & A16 & _ & ATOP & ACE & AFSa & AAPa). pose proof RBc as (CP & C16 & _ & CTOP & CCE & AFSc & CAP). pose proof RBe as (EP & E16 & _ & ETOP & ECE & AFSe & EAP).
    pose proof BEL as (ABL1 & ABL2 & ABL3). pose proof BAP as (BA1 & BA2 & BA3).
    unfold BIO_SIZE, B64CTX_SIZE, ENCCTX_SIZE in ABL1, ABL2, ABL3, BA1, BA2, BA3, ATOP, ACE, AFSa, AAPa, CTOP, CCE, AFSc, CAP, ETOP, ECE, AFSe, EAP.
    pose proof MB as MBc. destruct MBc as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & POSR & LENR & BUFP & BUFH & MFL & RDO & AEOF & NUMR & NRD & NRD2 & MNX & MPV).
    pose proof RB1 as (AP & AAL & _ & AH & MCE & AFSm & AAP). pose proof RB3 as (BMP & BMAL & _ & BMH & BMCE & AFSbm & BMAP).
    pose proof MBL as (BL1 & BL2 & BL3 & BL4). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in BL1, BL2, BL3, BL4, MCE, AFSm, AAP, BMCE, AFSbm, BMAP.
    unfold AFS_SIZE in AFSa, AFSc, AFSe, AFSm, AFSbm.
    pose proof RB2 as (BBP & _ & _ & BBH & BBCE & AFSbb & BBAP). pose proof RB4 as (RPP & _ & _ & RPH & RPCE & AFSrp & RPAP).
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, AFS_SIZE in BBCE, AFSbb, BBAP, RPCE, AFSrp, RPAP.
    pose proof (aapp_not_shadowland _ _ BBAP) as NSbb. pose proof (aapp_not_shadowland _ _ RPAP) as NSrp. unfold ALOWSH_LO, AHI_LO in NSbb, NSrp.
    pose proof MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof (b64_flags_facts (bf_flags R) FLR ltac:(unfold BIO_FLAGS_BASE64_NO_NL in NONL; exact NONL)) as [FL1 FL2].
    pose proof (Forall_inv APO) as OA1. pose proof (Forall_inv (Forall_inv_tail APO)) as OA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APO))) as OA3.
    cbn [blk_addr blk_size fst snd] in OA1, OA2, OA3. unfold BIO_SIZE, B64CTX_SIZE in OA1, OA2, OA3.
    pose proof (Forall_inv APM) as APM1. pose proof (Forall_inv APM1) as DJ_a_mb. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM1))) as DJ_a_bm. clear APM1.
    pose proof (Forall_inv (Forall_inv_tail APM)) as APM2. pose proof (Forall_inv APM2) as DJ_c_mb. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM2))) as DJ_c_bm. clear APM2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM))) as APM3. pose proof (Forall_inv APM3) as DJ_e_mb. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM3))) as DJ_e_bm. clear APM3.
    cbn [blk_addr blk_size fst snd] in DJ_a_mb, DJ_a_bm, DJ_c_mb, DJ_c_bm, DJ_e_mb, DJ_e_bm.
    pose proof (Forall_inv APM) as APM1'. pose proof (Forall_inv (Forall_inv_tail APM1')) as DJ_a_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM1')))) as DJ_a_rp. clear APM1'.
    cbn [blk_addr blk_size fst snd] in DJ_a_bb, DJ_a_rp. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in DJ_a_bb, DJ_a_rp.
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in DJ_a_mb, DJ_a_bm, DJ_c_mb, DJ_c_bm, DJ_e_mb, DJ_e_bm.
    pose proof (Forall_inv APT) as PT1. cbn [blk_addr blk_size fst snd] in PT1. unfold BIO_SIZE in PT1.
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. cbn [blk_addr blk_size fst snd] in OF1, OF3.
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in OF1, OF3. unfold A_mem_buf_method, O_METH_BREAD in OUTM.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FF1 & FF2 & FF64 & FF8 & FP1 & FP2 & FP3 & FP4 & FF5 & FF6 & FB1 & FB2 & FB3).
    change (fsz 0) with 64 in FF2, FF6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FF1, FF2, FP1, FP2, FP3, FP4, FF5, FF6, FB1, FB2.
    assert (APff : aapp ff 64) by (clear - FB3 FF5 FF6; eapply aapp_sub; [exact FB3| lia| unfold AFS_SIZE; lia]).
    assert (APfp : aapp fp 1) by (clear - FB3 FP3 FP4; eapply aapp_sub; [exact FB3| lia| unfold AFS_SIZE; lia]).
    assert (SHF : ASHADOW_BASE <= Z.shiftr ff 3 + ASHB /\ Z.shiftr ff 3 + ASHB + 8 <= AHI_LO).
    { unfold ASHB. rewrite <- ASHADOW_BASE_val, (sh_shiftr ff) by lia. clear - APff FF1. pose proof (sh_aapp_range ff 64 APff ltac:(lia)) as (Q1 & Q2 & Q3).
      change (nsh 64) with 8 in Q2. split; [unfold sh; Z.div_mod_to_equations; lia| lia]. }
    pose proof SHF as [SHF1 SHF2]. unfold ASHB in SHF1, SHF2. rewrite ASHADOW_BASE_val in SHF1. unfold AHI_LO in SHF2.
    pose proof (aapp_not_shadowland _ _ APff) as NSff. pose proof (aapp_not_shadowland _ _ APfp) as NSfp. unfold ALOWSH_LO, AHI_LO in NSff, NSfp.
    pose proof (aapp_not_shadowland _ _ AAPa) as NSba. pose proof (aapp_not_shadowland _ _ AAP) as NSa. pose proof (aapp_not_shadowland _ _ BMAP) as NSbm.
    unfold ALOWSH_LO, AHI_LO in NSba, NSa, NSbm.
    pose proof (aapp_not_shadowland _ _ CAP) as NSc. pose proof (aapp_not_shadowland _ _ EAP) as NSe. unfold ALOWSH_LO, AHI_LO in NSc, NSe.
    pose proof (aapp_bounds _ _ AAPa ltac:(clear; lia)) as (_ & _ & AHIba & _). pose proof (aapp_bounds _ _ CAP ltac:(clear; lia)) as (_ & _ & AHIc & _).
    pose proof (aapp_bounds _ _ AAP ltac:(clear; lia)) as (_ & _ & AHIa & _). pose proof (aapp_bounds _ _ BMAP ltac:(clear; lia)) as (_ & _ & AHIbm & _).
    unfold AAPP_HI in AHIba, AHIc, AHIa, AHIbm.
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). pose proof (aapp_not_shadowland _ _ F4) as NSfs. unfold AFS_SIZE, ALOWSH_LO, AHI_LO, AIMG_TOP in F1, F2, NSfs.
    pose proof (fsobj_windows H HH LF out outl 0 ff fp _ RFS FO FRESH ltac:(clear - OUTP; lia) ltac:(clear - OUTL; lia) ltac:(destruct OSH as ((_ & OHI & _) & _); clear - OHI; lia)) as (OW1 & OW2 & OW3 & OW4).
    pose proof (fsobj_windows H HH LF (mb_buf M) (mb_len M) 0 ff fp _ RFS FP FRESH ltac:(clear - BUFP; lia) ltac:(clear - LENR; lia) ltac:(clear - BUFH ACR; unfold AAPP_HI; lia)) as (PW1 & PW2 & PW3 & PW4).
    change (fsz 0) with 64 in OW1, PW1. change (fshn 0) with 8 in OW2, PW2. unfold AFS_FLAGS in OW4, PW4.
    unfold zlength in TLEN, TLE.
    assert (LOS : lo <= fb - Z.max BIOREAD_STACK (Z.max DECUPDATE_STACK (Z.max DECFINAL_STACK (Z.max DECINIT_STACK AINTRIN_STACK)))).
    { revert LO FBR. unfold B64READ_STACK, BIOREAD_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, DECUPDATE_STACK, DECFINAL_STACK,
        DECINIT_STACK, DECBLOCK_STACK, FR_b64_read, FR_BIO_read, FR_bio_read_intern, FR_bread_conv, FR_BIO_eof, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl, FR_EVP_DecodeUpdate,
        FR_EVP_DecodeFinal, FR_EVP_DecodeInit, FR_evp_decodeblock_int, AFS_STACK, AINTRIN_STACK, BIOACC_STACK, FR_BIO_set_data. clear. intros; lia. }
    assert (LO16 : lo + 4096 <= fb) by (revert LOS; unfold AINTRIN_STACK; clear; intros; lia).
    assert (BOK0 : bio_ok (mkBIO A_b64_method 1 1 (Z.land (bf_flags R) (Z.lnot 15)) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0)).
    { unfold bio_ok; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite].
      unfold A_b64_method. clear - FL1 CP CCE AP MCE ACR PVR. lia. }
    unfold ASHB in SHC. rewrite <- ASHADOW_BASE_val in SHC. rewrite (sh_shiftr ff) in SHC by (clear - FF1; lia).
    (* [comment removed for export] *)
    eapply evt_cut.
    { match goal with |- evt _ _ ?ms =>
        replace ms with (HEADMS (bv_unsigned sp) fb gp tp F fc R ra' u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 outl) s3' (Z_to_bv 64 (bf_ctx R + 12)) q8 q9 q10 u3 u4 u5 u6 mh)
          by (unfold HEADMS; reflexivity) end.
      eapply (@rd_loop HCEIL H HH BRMS TFS DUS DFS DIS (bv_unsigned sp) fb gp tp F fc j136 j152 j256 mh sA LB LF ff fp a mb lo out outl R M txt
                BAP BEL RBa RBc RBe FLR J3 MBL MSEP (conj RB1 (conj RB2 (conj RB3 RB4))) LENR (eq_sym (eq_sym TLEN)) APM APT OUTF OUTB OUTM APO OUTR OUTP OUTH OTOP OUTL CEIL LOS
                ltac:(clear - FBR; lia) ltac:(clear - SPR; lia) FB16 TP METHMh
                _ HB BOK0 FL2 (proj1 FRESH) (proj1 (proj2 FRESH)) LFN SHC BSHh MBSHh PAYh OSHh CSVh CAPP
                (fsobj_mono H _ _ _ _ FO) (fsobj_mono H _ _ _ _ FP) PW1 OW1 AWO ACWO J2 (conj I1 I3) RFSh
                (S (S (length txt))) 0%nat [] [] mh (mb_flags M) (mb_nread M) 1 vnum [] w216 w224 jb jt junk).
      - clear; cbn; lia.
      - clear; lia.
      - unfold zlength; cbn; clear - OUTL; lia.
      - left; reflexivity.
      - clear; lia.
      - unfold HINV. split. { unfold zlength; cbn [length Z.of_nat]; rewrite Z.add_0_r, Z.sub_0_r; exact SLOTS. }
        split; [exact HD|]. split; [exact BUF|]. split; [exact TMP|]. split; [exact ENCh|].
        split. { change (Z.of_nat 0) with 0. rewrite <- POS0. rewrite mset_self. exact MBh. }
        split; [exact TXT|]. split. { cbn [length map]. rewrite Nat.sub_0_r. apply rw_cells_CB0. exact OUTC. }
        split; [exact NUM|].
        split; [exact (B64TAB_of_mem_inv _ MI)|]. split; [exact MI|]. split; [exact ST|].
        split; [exact ACh|]. split; [exact RFSh|]. split; [exact RLh|]. split; [exact RHh|].
        split; [apply Forall_nil|]. split; [apply munch_refl| apply wmono_refl].
      all: match goal with |- ?G => idtac "LOOP-ARG:" G end. }
    cbv beta. intros msx EX. unfold EXITQ in EX.
    destruct EX as (mx & rcf & c' & fl' & nr' & bl' & bo' & vnum' & d' & XS & w104' & w128' & w216' & w224' & jb' & jt' & jo'
                    & ra2 & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & x3 & x4 & x5 & x6
                    & -> & RV & RCF & CLE & CR & ZLE & USED & FLR' & SLOTSx & HDx & BUFx & TMPx & ENCx & MBx & TXTx & OUTx & NUMx & TABx & MIx & STx & ACx
                    & RFSx & RLx & RHx & FXx & MUx & WMx).
    replace (b64r_loop (S (S (length txt))) (skipn 0 (map bv_unsigned txt)) [] (zlength (@nil Z)) (outl - zlength (@nil Z)) [] 0)
      with (b64_read_spec (map bv_unsigned txt) outl) in *
      by (unfold b64_read_spec, zlength; rewrite length_map; cbn [skipn length Z.of_nat]; rewrite Z.sub_0_r; reflexivity).
    set (res := b64_read_spec (map bv_unsigned txt) outl) in *. clearbody res.
    assert (ZNN : 0 <= zlength (br_out res)) by (unfold zlength; clear; lia).
    unfold ECH_AC9_rdloop.FP, ECH_AC9_rdloop.WL' in MUx.
    assert (INff : In (0, ff, fp) ((0, ff, fp) :: LF)) by (left; reflexivity).
    assert (Fab : fsobj H ((0, ff, fp) :: LF) a 128) by (apply fsobj_outside; clear - AFSa; unfold AFS_SIZE; lia).
    assert (Fcb : fsobj H ((0, ff, fp) :: LF) (bf_ctx R) 2584) by (apply fsobj_outside; clear - AFSc; unfold AFS_SIZE; lia).
    assert (Fmb : fsobj H ((0, ff, fp) :: LF) mb 128) by (apply fsobj_outside; clear - AFSm; unfold AFS_SIZE; lia).
    pose proof OSH as (_ & _ & OAPP & _). pose proof OAPP as OAPP'. unfold in_app_mem, AHI_LO, AAPP_HI in OAPP'. rewrite ASHADOW_BASE_val in OAPP'.
    pose proof PAY as (_ & _ & PAPP). pose proof PAPP as PAPP'. unfold in_app_mem, AHI_LO, AAPP_HI in PAPP'. rewrite ASHADOW_BASE_val in PAPP'.
    (* [comment removed for export] *)
    assert (FRsx : rw_cells asegs mx (bv_unsigned sp + -104) (ardsaves s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply rw_cells_transport; [exact FRs| exact MUx| exact WMx|]. cbn [disjoint_from cells_size csize length app Nat.add ardsaves Z.of_nat Pos.of_succ_nat Pos.succ fst snd].
      split; [clear - FBR; lia|]. apply disjoint_from_app. split; [eapply (dj_scratch_hi H HH); [exact RFSh| exact FXx| clear - CEIL LO16 FBR; lia]|].
      cbn [disjoint_from fst snd]. clear - OUTR SPR FBR ABL2 ABL3 BL1 BL3 FF2 CEIL LO16. lia. }
    assert (STgx : stk asegs mx (fb + 280) (bv_unsigned sp + -104)) by (eapply stk_transport_high; [exact STg| exact WMx| clear - CEIL ACR LO16; lia]).
    assert (ST24x : stk asegs mx fb (fb + 8)).
    { pose proof (stk_of_rw_cells _ _ _ _ FR24) as S24. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in S24.
      match type of S24 with stk _ _ _ ?h => replace h with (fb + 8) in S24 by (clear; lia) end.
      eapply stk_transport_high; [exact S24| exact WMx| clear - CEIL ACR LO16; lia]. }
    assert (FH1x : rw_cells asegs mx ff [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 ADESCR_b64_read); C8 (Z_to_bv 64 P_b64_read)]).
    { eapply rw_cells_transport; [exact FH1| exact MUx| exact WMx|]. cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd].
      split; [clear - FF2 CEIL LO16; lia|]. apply disjoint_from_app. split; [eapply (dj_scratch_live H HH); [exact RFSh| exact INff| exact FXx| clear; lia| change (fsz 0) with 64; clear; lia]|].
      cbn [disjoint_from fst snd]. clear - OW1 AFSc AFSe AFSm AFSbm FF5 FF6. lia. }
    assert (FH6x : rw_cells asegs mx (ff + 56) [C8 (Z_to_bv 64 fp)]).
    { eapply rw_cells_transport; [exact FH6| exact MUx| exact WMx|]. cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd].
      split; [clear - FF2 CEIL LO16; lia|]. apply disjoint_from_app. split; [eapply (dj_scratch_live H HH); [exact RFSh| exact INff| exact FXx| clear; lia| change (fsz 0) with 64; clear; lia]|].
      cbn [disjoint_from fst snd]. clear - OW1 AFSc AFSe AFSm AFSbm FF5 FF6. lia. }
    assert (FPCx : rw_cells asegs mx fp [C1 (b8 1)]).
    { eapply rw_cells_transport; [exact FPC| exact MUx| exact WMx|]. cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd].
      split; [clear - FP2 FF2 CEIL LO16; lia|]. apply disjoint_from_app. split; [eapply (dj_scratch_live_flag H HH); [exact RFSh| exact INff| exact FXx]|].
      cbn [disjoint_from fst snd]. clear - OW3 AFSc AFSe AFSm AFSbm FP2 FP3 FP4. lia. }
    assert (TAILx : rw_cells asegs mx (bf_ctx R + 2566) [CB 2 j2; C8 (wz 0); C8 (wz 0)]).
    { eapply rw_cells_transport; [exact TAIL| exact MUx| exact WMx|]. cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd].
      split; [clear - ABL2; lia|]. apply disjoint_from_app. split.
      - eapply disjoint_from_Forall; [exact FXx|]. intros iv Hiv.
        pose proof (fsobj_scratch H HH _ _ _ _ iv RFSh Fcb ltac:(clear - CP; lia) ltac:(clear; lia) ltac:(clear - AHIc; unfold AAPP_HI; lia) CAP Hiv) as D. cbn [fst snd] in D |- *. clear - D. lia.
      - cbn [disjoint_from fst snd]. clear - OA2 BA3 DJ_c_mb DJ_c_bm AFSc FF5 FF6. lia. }
    assert (HBx : rw_cells asegs mx a (bio_cells (mkBIO A_b64_method 1 1 (Z.land (bf_flags R) (Z.lnot 15)) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0))).
    { eapply rw_cells_transport; [exact HB| exact MUx| exact WMx|].
      cbn [disjoint_from cells_size csize length app Nat.add bio_cells Z.of_nat Pos.of_succ_nat Pos.succ fst snd
           bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite].
      split; [clear - ABL1; lia|]. apply disjoint_from_app. split.
      - eapply disjoint_from_Forall; [exact FXx|]. intros iv Hiv.
        pose proof (fsobj_scratch H HH _ _ _ _ iv RFSh Fab ltac:(clear - AP0; lia) ltac:(clear; lia) ltac:(clear - AHIba; unfold AAPP_HI; lia) AAPa Hiv) as D. cbn [fst snd] in D |- *. clear - D. lia.
      - cbn [disjoint_from fst snd]. clear - OA1 BA1 BA2 DJ_a_mb DJ_a_bm AFSa FF5 FF6. lia. }
    (* [comment removed for export] *)
    assert (AWL : Forall appwin [(out, out + outl); (bf_ctx R, bf_ctx R + 2566); (bf_enc R, bf_enc R + 92); (mb, mb + 128); (mb_bm M, mb_bm M + 32); (ff + 32, ff + 36)]).
    { unfold appwin, AHI_LO. rewrite ASHADOW_BASE_val. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        [ clear - OAPP'| clear - NSc| clear - NSe| clear - NSa| clear - NSbm| clear - NSff]; lia. }
    pose proof BSHh as (SHah & _ & _). pose proof MBSHh as (SHmh & _ & _ & _). unfold BIO_SIZE in SHah, SHmh.
    assert (ADDa : addressable mx a 128).
    { eapply (addressable_across3 H HH); [exact SHah| exact RFSh| exact Fab| clear - AP0; lia| clear - AHIba; unfold AAPP_HI; lia| exact MUx| exact WMx| exact CEIL| exact FXx| exact AWL]. }
    assert (ACCa : accessible mx a BIO_SIZE).
    { unfold BIO_SIZE. eapply addressable_accessible; [exact ADDa| clear; lia| clear; lia| clear - AHIba; unfold AAPP_HI; lia]. }
    assert (ADDm : addressable mx mb 128).
    { eapply (addressable_across3 H HH); [exact SHmh| exact RFSh| exact Fmb| clear - AP; lia| clear - AHIa; unfold AAPP_HI; lia| exact MUx| exact WMx| exact CEIL| exact FXx| exact AWL]. }
    assert (ACCm : accessible mx mb BIO_SIZE).
    { unfold BIO_SIZE. eapply addressable_accessible; [exact ADDm| clear; lia| clear; lia| clear - AHIa; unfold AAPP_HI; lia]. }
    assert (SHPx : rw_cells asegs mx (Z.shiftr ff 3 + ASHB) b64rd_shpat).
    { unfold ASHB. rewrite <- ASHADOW_BASE_val, (sh_shiftr ff) by (clear - FF1; lia).
      eapply (shpat_across3 H HH); [exact SHC| exact RFSh| exact INff| exact MUx| exact WMx| exact CEIL| exact FXx| exact AWL]. }
    pose proof MBx as (NCx & _).
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply aexit with (B := mkBIO A_b64_method 1 1 (Z.land (bf_flags R) (Z.lnot 15)) 0 0 (bf_ctx R) mb (bf_prev R) 1 0 0)
                        (M := mset M (Z.of_nat (br_used res)) fl' nr') (lo := lo) (vret := zlength (br_out res)) (ff := ff) (fp := fp);
        cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite membio_bio mset
             mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp];
      [ clear - ZLE ZNN OUTL; unfold zlength in *; lia
      | exact RCF
      | clear - FF1 F1; lia
      | clear - FF2 F2; lia
      | unfold ALOWSH_LO, AHI_LO; exact NSff
      | unfold ASHB; rewrite ASHADOW_BASE_val; exact SHF1
      | unfold ASHB, AHI_LO; exact SHF2
      | clear - FP1 F1; lia
      | clear - FP2 FF1; lia
      | unfold AIMG_TOP; clear - FP1 F1; lia
      | unfold ALOWSH_LO, AHI_LO; exact NSfp
      | exact AP0
      | unfold BIO_SIZE; exact ABL1
      | exact AAPa
      | exact ACCa
      | exact BOK0
      | reflexivity
      | exact AP
      | unfold BIO_SIZE; exact BL1
      | exact AAP
      | exact ACCm
      | exact FLR'
      | unfold BIO_SIZE; exact DJ_a_mb
      | exact ACx
      | unfold BIO_SIZE; clear - AFSa FF5 FF6 FP3 FP4; lia
      | unfold BIO_SIZE; clear - AFSm FF5 FF6 FP3 FP4; lia
      | exact SLOTSx
      | exact FRsx
      | exact HBx
      | exact NCx
      | exact FH1x
      | exact FH6x
      | exact SHPx
      | exact FPCx
      | exact STx
      | exact CEIL
      | clear - LO16; lia
      | clear - LO16 LO0; lia
      | clear - FBR; lia
      | clear - SPR; lia
      | exact MIx
      | exact RAE
      | exact A16
      | exact AAL ]. }
    cbv beta. intros ms3 (m1 & g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & -> & MU1 & WM1 & MI1 & ST1 & SL1 & SV1 & BC1 & NC1 & FHr & FTr & SHr & FPr).
    (* [comment removed for export] *)
    assert (SH8 : Z.shiftr ff 3 = ff / 8) by (rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity).
    unfold ASHB in MU1.
    (* [comment removed for export] *)
    assert (TAIL1 : rw_cells asegs m1 (bf_ctx R + 2566) [CB 2 j2; C8 (wz 0); C8 (wz 0)]).
    { eapply rw_cells_transport; [exact TAILx| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd map]. clear - ABL2 LO16 BA1 NSc SHF1 SHF2 AFSc FF5 FF6 FP3 FP4. lia. }
    assert (HD1 : rw_cells asegs m1 (bf_ctx R) (rdhdr bl' bo' 0 c' (bf_enc R))).
    { eapply rw_cells_transport; [exact HDx| exact MU1| exact WM1|]. unfold rdhdr. cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd map]. clear - ABL2 LO16 BA1 NSc SHF1 SHF2 AFSc FF5 FF6 FP3 FP4. lia. }
    assert (BUF1 : rw_cells asegs m1 (bf_ctx R + 40) [CB 1502 jb']).
    { eapply rw_cells_transport; [exact BUFx| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd map]. clear - ABL2 LO16 BA1 NSc SHF1 SHF2 AFSc FF5 FF6 FP3 FP4. lia. }
    assert (TMP1 : rw_cells asegs m1 (bf_ctx R + 1542) [CB 1024 jt']).
    { eapply rw_cells_transport; [exact TMPx| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd map]. clear - ABL2 LO16 BA1 NSc SHF1 SHF2 AFSc FF5 FF6 FP3 FP4. lia. }
    assert (ENC1 : ENCCTX H LB m1 (bf_enc R) d' (bf_eid R)).
    { eapply (ENCCTX_transport H); [exact MU1| exact WM1| | exact ENCx]. cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd map]. clear - ABL3 LO16 BA2 NSe SHF1 SHF2 AFSe FF5 FF6 FP3 FP4. lia. }
    assert (MB1 : MEMBIO H LB m1 mb (mset M (Z.of_nat (br_used res)) fl' nr')).
    { eapply (MEMBIO_transport H); [exact MU1| exact WM1| | | | | exact MBx]; cbn [mb_bb mb_bm mb_rp mset]; unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd map].
      - clear - BL1 LO16 DJ_a_mb NSa SHF1 SHF2 AFSm FF5 FF6 FP3 FP4. lia.
      - clear - BL2 LO16 DJ_a_bb NSbb SHF1 SHF2 AFSbb FF5 FF6 FP3 FP4. lia.
      - clear - BL3 LO16 DJ_a_bm NSbm SHF1 SHF2 AFSbm FF5 FF6 FP3 FP4. lia.
      - clear - BL4 LO16 DJ_a_rp NSrp SHF1 SHF2 AFSrp FF5 FF6 FP3 FP4. lia. }
    assert (TXT1 : bytes_at asegs m1 (mb_buf M) txt).
    { eapply bytes_at_transport; [exact TXTx| exact MU1|]. cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd map]. unfold zlength in TLEN. clear - BUFH CEIL LO16 TLEN PT1 SPR PAPP' SHF1 SHF2 PW1 PW3. lia. }
    assert (OUT1 : rw_cells asegs m1 out [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl - length (br_out res)) jo']).
    { eapply rw_cells_transport; [exact OUTx| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd map]. rewrite ?length_map. unfold zlength in ZLE. clear - OUTR OA1 ZLE OUTL SPR LO16 OAPP' SHF1 SHF2 OW1 OW3 FBR. lia. }
    assert (METHBx : METH_b64 mx).
    { unfold METH_b64 in METHBh |- *. eapply rw_cells_transport; [exact METHBh| exact MUx| exact WMx|].
      cbn [cells_size csize Nat.add length]. split; [unfold A_b64_method, O_METH_BREAD; cbn; clear - CEIL ACR; lia|]. apply disjoint_from_app. split.
      + eapply (dj_scratch_img H HH); [exact RFSh| exact FXx| unfold A_b64_method, O_METH_BREAD, AIMG_TOP; cbn; clear; lia].
      + unfold A_b64_method, O_METH_BREAD. cbn. unfold AIMG_TOP in *. clear - OTOP CTOP ETOP AH BMH FF1 F1. lia. }
    assert (METHMx : METH_mem mx).
    { unfold METH_mem in METHMh |- *. eapply rw_cells_transport; [exact METHMh| exact MUx| exact WMx|].
      cbn [cells_size csize Nat.add length]. split; [unfold A_mem_buf_method, O_METH_BREAD; cbn; clear - CEIL ACR; lia|]. apply disjoint_from_app. split.
      + eapply (dj_scratch_img H HH); [exact RFSh| exact FXx| unfold A_mem_buf_method, O_METH_BREAD, AIMG_TOP; cbn; clear; lia].
      + unfold A_mem_buf_method, O_METH_BREAD. cbn. unfold AIMG_TOP in *. clear - OTOP CTOP ETOP AH BMH FF1 F1. lia. }
    assert (METHB1 : METH_b64 m1).
    { unfold METH_b64 in METHBx |- *. eapply rw_cells_transport; [exact METHBx| exact MU1| exact WM1|]. unfold A_b64_method, O_METH_BREAD. cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd map]. unfold AIMG_TOP in *. clear - CEIL ACR ATOP SPR LO16 SHF1 SH8 FF1 FP1 F1. lia. }
    assert (METHM1 : METH_mem m1).
    { unfold METH_mem in METHMx |- *. eapply rw_cells_transport; [exact METHMx| exact MU1| exact WM1|]. unfold A_mem_buf_method, O_METH_BREAD. cbn [disjoint_from cells_size csize length app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd map]. unfold AIMG_TOP in *. clear - CEIL ACR ATOP SPR LO16 SHF1 SH8 FF1 FP1 F1. lia. }
    destruct (b64ctx_used_of_exit _ _ _ _ _ _ _ _ _ HD1 BUF1 TMP1 TAIL1) as (USED1 & LH1 & LJ1 & CONT1).
    (* [comment removed for export] *)
    assert (ST24 : stk asegs m1 fb (fb + 8)) by (eapply stk_transport_high; [exact ST24x| exact WM1| clear - CEIL ACR LO16; lia]).
    assert (STg1 : stk asegs m1 (fb + 280) (bv_unsigned sp + -104)) by (eapply stk_transport_high; [exact STgx| exact WM1| clear - CEIL ACR LO16; lia]).
    pose proof (stk_of_rw_cells _ _ _ _ SL1) as STsl. cbn [cells_size csize Nat.add ardslots length app Z.of_nat Pos.of_succ_nat Pos.succ] in STsl.
    pose proof (stk_of_rw_cells _ _ _ _ SV1) as STsv. cbn [cells_size csize Nat.add ardsaves length app Z.of_nat Pos.of_succ_nat Pos.succ] in STsv.
    assert (STa : stk asegs m1 lo (fb + 8)) by (eapply stk_merge; [exact ST1| exact ST24| clear - LO16 LO0; lia]).
    assert (STb : stk asegs m1 lo (fb + 280)).
    { eapply stk_merge; [exact STa| | clear - LO16 LO0; lia]. match type of STsl with stk _ _ _ ?h => replace h with (fb + 280) in STsl by (clear; lia) end. exact STsl. }
    assert (STc : stk asegs m1 lo (bv_unsigned sp + -104)) by (eapply stk_merge; [exact STb| exact STg1| clear - LO16 LO0 FBR; lia]).
    assert (STf : stk asegs m1 lo (bv_unsigned sp)).
    { eapply stk_merge; [exact STc| | clear - LO16 LO0 FBR SPR; lia]. match type of STsv with stk _ _ _ ?h => replace h with (bv_unsigned sp) in STsv by (clear; lia) end. exact STsv. }
    (* [comment removed for export] *)
    assert (MUf : munch ((lo, bv_unsigned sp) :: (XSF ff fp ++ XS) ++ (out, out + outl) :: B64F_foot a R ++ MEMBIO_foot mb M) m m1).
    { clear - MUA MUx MU1 LO16 FBR SPR LO0.
      lazymatch goal with |- munch ?T _ _ => eapply (munch_join _ _ T m mx m1); [eapply (munch_join _ _ T m mh mx); [exact MUA| exact MUx| |]| exact MU1| apply sub_fp_refl|] end.
      - apply sub_fp_callee; [lia|]. unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE. cbn [app].
        repeat apply Forall_cons; try apply Forall_nil; unfold covered; cbn [fst snd]; right;
          repeat first [apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl].
      - apply sub_fp_inner; [lia|]. unfold XSF, B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE. cbn [app].
        repeat apply Forall_cons; try apply Forall_nil; unfold covered; cbn [fst snd]; right;
          repeat first [apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl].
      - apply sub_fp_inner0. unfold XSF, B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE. cbn [app].
        repeat apply Forall_cons; try apply Forall_nil; unfold covered; cbn [fst snd];
          first [left; lia | right; repeat first [apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl]].
      }
    pose proof (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WMA WMx) WM1) as WMf.
    (* [comment removed for export] *)
    assert (ACf : ACONST m1).
    { clear - ACx MU1 WM1 CEIL ACR LO16 LO0 FB3 APfp APff FF1 FP1 F1 AAPa SHF1 SH8 HCEIL.
      eapply ACONST_frame; [exact ACx| exact MU1| exact WM1|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
      - eapply aconst_ok_aapp; [exact AAPa| cbn; lia| cbn; lia].
      - apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; change (12599296 / 8) with 1574912; rewrite SH8; Z.div_mod_to_equations; lia.
      - eapply aconst_ok_aapp; [exact APff| cbn; lia| cbn; lia].
      - eapply aconst_ok_aapp; [exact APfp| cbn; lia| cbn; lia]. }
    assert (RFSf : as_RFS H LF m1).
    { rewrite <- (lf_remove_head 0 ff fp LF).
      eapply (ah_release H HH); [exact RFSx| left; reflexivity| exact MU1| exact WM1| |].
      - clear - AFSa ATOP NSfs SHF1 SHF2 SH8 FB1 FB2 FP3 FP4 FF5 FF6 F1 F2 ACR CEIL LO16 LO0.
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold afs_write_ok, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AIMG_TOP in *; cbn [fst snd] in *.
        + left. left. lia.
        + left. left. lia.
        + left. left. lia.
        + left. right. exists (0, ff, fp). split; [left; reflexivity|]. cbn. change (fsz 0) with 64. lia.
        + right. split; reflexivity.
      - destruct FPr as [[_ (B0 & B1 & B2)] _]. specialize (B2 0%nat ltac:(cbn; lia)). cbn in B2. rewrite Z.add_0_r in B2. exact B2. }
    assert (RLf : arelro_lib m1).
    { eapply arelro_across; [exact RLx| exact MU1|]. clear - CEIL ACR FB1 FP1 FF1 F1 SHF1 SH8 ATOP LO16 LO0. unfold AIMG_TOP in *.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
    assert (RHf : as_RHEAP H sA LB m1).
    { eapply (ah_RHEAP_frame H HH); [exact RHx| exact MU1| exact WM1|].
      clear - CEIL LO16 LO0 J1 FF5 FF6 FF8 FP3 FP4 SHF1 SHF2 SH8 F1 F2 F3.
      repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd].
      - left. lia.
      - right; right; left. exists (bf_id R, a, 128). split; [exact J1| cbn; lia].
      - right; right; right; right; right; left. unfold sh, AFS_SIZE, AFS_HDR, AFS_FLAGS in *. rewrite ?ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
      - right; right; right; right; left. unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *. lia.
      - right; right; right; right; left. unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *. lia. }
    (* [comment removed for export] *)
    apply evt_done. unfold b64rd_post.
    exists g0, g1, g2, h1, h2, h3, h4, h5, h6, h7, g3, g4, g5, g6, m1, (Z.lor (Z.land (bf_flags R) (Z.lnot 15)) (fl' mod 16)), 0, c', fl', nr', d'. eexists. eexists. exists jo', (XSF ff fp ++ XS).
    split. { rewrite <- RV. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    split. { apply Forall_app_scratch; [| exact (fs_scratch_mono_Forall H _ _ _ FXx)].
             pose proof (fs_scratch_of_fresh H _ _ _ _ FRESH) as FS4. change (fsz 0) with 64 in FS4. change (fshn 0) with 8 in FS4. unfold AFS_FLAGS in FS4.
             rewrite <- (sh_shiftr ff) in FS4 by (clear - FF1 F1; lia). rewrite ASHADOW_BASE_val in FS4. exact FS4. }
    split; [exact MUf|]. split; [exact WMf|]. split; [exact MI1|]. split; [exact STf|].
    split. { rewrite NR0. unfold b64f_bio, bf_with_hdr in *.
             cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite membio_bio mset
                  mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc] in BC1 |- *.
             exact BC1. }
    split. { apply lor_lt_pow2; [exact FL1|]. pose proof (Z.mod_pos_bound fl' 16 ltac:(lia)) as Q. clear - Q. lia. }
    split; [clear; lia|].
    split; [exact LH1|]. split; [exact LJ1|]. split; [exact USED1|]. split; [exact CONT1|].
    split; [exact CR|].
    split. { intros E. rewrite RV in E. destruct (Z.eqb_spec (zlength (br_out res)) 0) as [E0|E0]; clear - E CLE E0 ZNN RCF; lia. }
    split. { rewrite RV. destruct (zlength (br_out res) =? 0); clear - RCF ZLE ZNN OUTL; lia. }
    split; [exact ZLE|].
    split; [exact ENC1|]. split; [exact MB1|]. split; [exact TXT1|]. split; [exact OUT1|]. split; [exact METHB1|]. split; [exact METHM1|].
    split; [exact I|]. split; [exact ACf|]. split; [exact RFSf|]. split; [exact RLf| exact RHf].
  Qed.
End S.
