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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep
     ECH_LibState ECH_LibStateMF ECH_LibFrame ECH_LibMid ECH_C0_stmt ECH_C1_stmt ECH_C1_malloc ECH_C1_dup ECH_C1_free ECH_C2_stmt ECH_C3_stmt ECH_C4_stmt ECH_C4_rep ECH_C4_frame ECH_C4_frame2
     ECH_C4_egs ECH_C4_raise ECH_Rostr ECH_C5_stmt ECH_C5_small ECH_C5_new ECH_C5_push ECH_C5_popfree ECH_C10_stmt
     ECH_C13_stmt ECH_C13_ext ECH_C13_small ECH_C13_entry ECH_C14_stmt ECH_KitSeg ECH_C14_fcc_seg ECH_C14_fcc ECH_C14_decexts_seg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Lemma sk_grow_le : forall c, 0 <= c -> 0 <= sk_grow c <= 2 * c /\ 5 * sk_grow c <= 8 * c.
Proof.
  intros c Hc. unfold sk_grow. split; [split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]|].
  rewrite (Z.mul_comm c 8). apply Z.mul_div_le. lia.
Qed.

(* [comment removed for export] *)
Definition S_DX_FUNC : list byte := Eval vm_compute in img_cstr DX_FUNC 64.
Definition K_DX_FUNC : list byte := Eval vm_compute in img_slack DX_FUNC (length S_DX_FUNC).
Section RO.
  Context {HCEIL : HeapCeil}.
  Lemma R_DX_FUNC : ROSTR DX_FUNC S_DX_FUNC K_DX_FUNC.
  Proof. apply ROSTR_of_image; vm_compute; reflexivity. Qed.
  Lemma S_DX_FUNC_len : Z.of_nat (length S_DX_FUNC) = 25. Proof. reflexivity. Qed.
  Lemma DX_FILE_ECHS_eq : DX_FILE_ECHS = A_ECHS_FILE. Proof. reflexivity. Qed.
End RO.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis EGS : egs_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let HRE : realloc_sr_stmt H := proj1 (proj2 HX).
  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).
  Let STATICS : statics_of_RHEAP H := proj1 (proj2 (proj2 (proj2 (proj2 HX)))).

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (mo : Model)
            (LIB LB : list block) (M : libmid) (x : ctxinfo) (ee pk base len cur0 rem0 lo B : Z) (E : entrep) (bs : list byte) (pbin : bptr)
            (j0 : list byte).
  Let spq : Z := bv_unsigned sp + -144.
  Hypothesis XE0 : en_exts E = 0.
  Hypothesis XO0 : en_exts_o E = None.
  Hypothesis BEL : Forall (fun b => blk_addr b + blk_size b <= lo) (blocks_ENTRY ee E).
  Hypothesis PKIN0 : pk_in base len cur0 rem0.
  Hypothesis REM1 : 1 <= rem0.
  Hypothesis REMB : rem0 <= 1499.
  Hypothesis SPK : bv_unsigned sp <= pk.
  Hypothesis PKB : pk + 24 <= B.
  Hypothesis BIN : In (pbin, base, len) LB.
  Hypothesis EIN0 : In (en_id E, ee, ENTRY_SIZE) LB.
  Hypothesis EBIN : en_id E <> pbin.
  Hypothesis OF0 : ofield LB (en_pname E) (en_pname_o E) /\ ofield LB (en_pub E) (en_pub_o E) /\ ofield LB (en_suites E) (en_suites_o E) /\ ofield LB (en_encoded E) (en_encoded_o E).
  Hypothesis BSL : zlength bs <= len.
  Hypothesis CRB : cur0 + rem0 <= base + zlength bs.   (* [comment removed for export] *)
  Hypothesis LIBSUB : forall b, In b LIB -> In b LB.
  Hypothesis CX : mid_ctx M = CtxReady x.
  Hypothesis MF0 : mid_flag M = 1.
  Hypothesis IDS : forall b b', In b LIB -> In b' (blocks_ENTRY ee E) -> blk_id b <> blk_id b'.
  Hypothesis IDB : forall b, In b LIB -> blk_id b <> pbin.
  Hypothesis BY : lb_bytes (mid_errblocks M ++ LB) + errph_bytes (mid_err M) + DECEXTS_BYTES rem0 + ERRDEBUG_BYTES <= hs_LIVE_MAX H.
  Hypothesis CN : Z.of_nat (length (mid_errblocks M ++ LB)) + errph_cnt (mid_err M) + (2 * rem0) / 5 + 8 <= hs_LIVE_CNT_MAX H.
  Hypothesis BG : lb_big (mid_errblocks M ++ LB) + errph_big (mid_err M) + 2 <= hs_LIVE_BIG_MAX H.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis BHI : B < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : hceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - DECEXTS_STACK M.
  Let LO8K : lo + 8592 <= bv_unsigned sp.
  Proof. clear - LO. unfold DECEXTS_STACK, FR_ech_decode_echconfig_exts in LO. change RREALLOC_STACK with 8256 in LO. lia. Qed.
  Let Q5 : 5 * ((2 * rem0) / 5) <= 2 * rem0 /\ 2 * rem0 < 5 * ((2 * rem0) / 5) + 5.
  Proof. clear. pose proof (Z.div_mod (2 * rem0) 5 ltac:(lia)). pose proof (Z.mod_pos_bound (2 * rem0) 5 ltac:(lia)). lia. Qed.
  Hypothesis TP : tp = Z_to_bv 64 RATP.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.

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
  Definition X0 : list (Z * Z) := (pk, pk + 24) :: (ee, ee + ENTRY_SIZE) :: ERR_X ++ errph_foot (mid_err M).

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
                      /\ 5 * zlength (EBof K es) <= 2 * c /\ lb_bytes (EBof K es) <= 12 * zlength es + c /\ lb_big (EBof K es) = 0
    end.

  (* [comment removed for export] *)
  Definition dworldX (m : mem) (mo' : Model) (s' : PState) (errv' : word) (P : Z) (xs : option (skrep * list extrep)) (NB : list block)
             (c cur rem : Z) (XB : list block) : Prop :=
       mem_inv rsegs m /\ stk rsegs m lo spq /\ rw_cells rsegs m spq (dx_frame j0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells rsegs m (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m B
    /\ hs_KREL H s' mo' /\ hs_MPRES H mo mo'
    /\ hs_RHEAP H s' (mid_errblocks M ++ XB ++ NB ++ LB) m
    /\ LIBMID LIB m M
    /\ ENTRYobj (NB ++ LB) m ee (EW P xs) /\ Permutation (blocks_EXTS P xs) NB /\ XINV P xs c
    /\ rw_cells rsegs m pk (pk_cells cur base rem) /\ pk_in base len cur rem /\ cur0 + rem0 = cur + rem /\ 0 <= c <= rem0 - rem
    /\ bytes_at rsegs m base bs
    /\ xpres LB (bv_unsigned sp) X0 m0 m.
  Definition dworld m mo' s' errv' P xs NB cur rem : Prop := dworldX m mo' s' errv' P xs NB (rem0 - rem) cur rem [].

  Lemma M_eq1 : mkMID 1 (mid_ctx M) (mid_err M) (mid_E M) (mid_vdso M) = M.
  Proof. clear - MF0. destruct M; cbn in *. subst. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma nb_not_client : forall s' L0 L1 L2 (SP : Z) X m b a,
    hs_RHEAP H s' (L0 ++ L1 ++ L2) m -> lo <= SP -> In b L1 -> blk_addr b <= a < blk_addr b + blk_size b ->
    xclient L2 SP X a -> False.
  Proof.
    intros s' L0 L1 L2 SP X m b a HP HSP Hb Ha [HC _].
    assert (BIN' : In b (L0 ++ L1 ++ L2)) by (apply in_or_app; right; apply in_or_app; left; exact Hb).
    pose proof (HH_blocks_below H HH _ _ _ HP _ BIN') as BH. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP BIN') as BR.
    destruct HC as [HC|[[HC _]|(b' & Hb' & Hr')]].
    - clear - HC BH Ha CEIL HSP. lia.
    - pose proof (block_cell_off_image _ _ BR Ha) as K. unfold IMG_LO, IMG_HI in K. clear - K HC. lia.
    - pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND.
      destruct (nd_app _ _ ND) as [_ ND1].
      assert (NE : blk_id b <> blk_id b') by (exact (nodup_ids_app_ne _ _ _ _ ND1 Hb Hb')).
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP BIN' ltac:(do 2 (apply in_or_app; right); exact Hb') NE) as DJ.
      unfold in_block in *. clear - DJ Ha Hr'. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dworld_entry : forall m mo' s' errv' P xs NB c cur rem XB,
    dworldX m mo' s' errv' P xs NB c cur rem XB ->
    exists pad1 pad2 pad3 pad4, length pad1 = 6%nat /\ length pad2 = 4%nat /\ length pad3 = 6%nat /\ length pad4 = 4%nat /\
      rw_cells rsegs m ee (entry_cells (EW P xs) pad1 pad2 pad3 pad4) /\ 0 < ee /\ ee + ENTRY_SIZE <= hceil
      /\ 0 <= P < 2^64
      /\ 0 < pk /\ pk + 24 < 2^64 /\ 0 < base /\ base + len <= hceil /\ (pk + 24 <= base \/ base + zlength bs <= pk).
  Proof.
    intros m mo' s' errv' P xs NB c cur rem XB (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & EO & PB & XI & PK & PIN & CR & CB & BS & XP).
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & HC) & EIN & O1 & O2 & O3 & O4 & XS).
    cbn [EW en_id en_exts en_exts_o] in EIN, XS.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (SUBLB : forall b, In b LB -> In b (mid_errblocks M ++ XB ++ NB ++ LB)) by (intros b Hb; do 3 (apply in_or_app; right); exact Hb).
    pose proof (HB _ (SUBLB _ EIN0)) as K1. pose proof (HB _ (SUBLB _ BIN)) as K2.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBLB _ EIN0)) as (EP0 & _).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBLB _ BIN)) as (BP0 & _).
    cbn [blk_addr blk_size fst snd] in K1, K2, EP0, BP0.
    assert (XR : 0 <= P < 2^64).
    { revert XS. unfold EXTS. destruct xs as [[K es]|]; intros XS; [| rewrite XS; lia].
      destruct XS as (XP1 & SO & _). destruct SO as (_ & _ & KIN & _). pose proof (HB _ ltac:(do 2 (apply in_or_app; right); exact KIN)) as K5. cbn [blk_addr blk_size fst snd] in K5. unfold SK_SIZE in K5. lia. }
    unfold zlength in *.
    exists pad1, pad2, pad3, pad4. unfold ENTRY_SIZE in *. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dworldX_munch : forall m m1 mo' s' errv' P xs NB c cur rem XB W,
    dworldX m mo' s' errv' P xs NB c cur rem XB -> munch W m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo spq ->
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= spq) \/ (exists b, In b XB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
    dworldX m1 mo' s' errv' P xs NB c cur rem XB
    /\ (forall A cs, rw_cells rsegs m A cs -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m1 A cs).
  Proof.
    intros m m1 mo' s' errv' P xs NB c cur rem XB W
      (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & EO & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & XP0) MU WM MI1 ST1 FW.
    unfold dworldX. cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (XBH : forall b, In b XB -> blk_addr b + blk_size b <= hceil) by (intros b Hb; apply HB; apply in_or_app; right; apply in_or_app; left; exact Hb).
    assert (XBO : forall b, In b XB -> blk_addr b + blk_size b <= 0x10000 \/ 0x311000 <= blk_addr b).
    { intros b Hb. exact (proj2 (proj2 (proj2 (proj2 (HH_RHEAP_block_range H HH _ _ _ _ HP ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)))))). }
    assert (XPL : xpres (NB ++ LB) (bv_unsigned sp + -144) [] m m1).
    { eapply xpres_of_munch_gen; [exact MU| exact WM|]. intros a Ha XC. clear MU WM. induction W as [|[u v] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as K1. cbn in K1. split; [| apply IH; eapply Forall_inv_tail; eassumption].
      destruct K1 as [[K1 K2]|(b & Hb & K1 & K2)].
      - destruct XC as [HC _]. destruct HC as [HC|[[HC _]|(b' & Hb' & Hr')]]; [clear - HC K2; lia| clear - HC K1 CEIL HCEILB; lia|].
        pose proof (HB _ ltac:(do 2 (apply in_or_app; right); exact Hb')) as BH'. clear - BH' Hr' K1 CEIL. lia.
      - intros R. eapply (nb_not_client s' (mid_errblocks M) XB (NB ++ LB) (bv_unsigned sp + -144) []); [exact HP| clear - LO8K; lia| exact Hb| | exact XC]. clear - R K1 K2. lia. }
    assert (WLO : Forall (fun iv : Z * Z => snd iv <= bv_unsigned sp + -144) W).
    { eapply Forall_impl; [| exact FW]. cbn beta. intros [u v] [[K1 K2]|(b & Hb & K1 & K2)]; cbn in *; [lia|]. pose proof (XBH _ Hb) as BH. clear - BH K2 CEIL LO8K. lia. }
    assert (WIMG : Forall (fun iv : Z * Z => snd iv <= 0x10000 \/ 0x311000 <= fst iv) W).
    { eapply Forall_impl; [| exact FW]. cbn beta. intros [u v] [[K1 K2]|(b & Hb & K1 & K2)]; cbn in *; [clear - K1 CEIL HCEILB; lia|]. pose proof (XBO _ Hb) as BO. clear - BO K1 K2. lia. }
    assert (DJS : forall a n, bv_unsigned sp + -144 <= a -> disjoint_from W a n).
    { intros a n Ha. clear - WLO Ha. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv WLO) as K. cbn in K. split; [lia| apply IH; eapply Forall_inv_tail; exact WLO]. }
    assert (DJI : forall a n, 0x10000 <= a -> a + n <= 0x311000 -> disjoint_from W a n).
    { intros a n H1 H2. clear - WIMG H1 H2. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv WIMG) as K. cbn in K. split; [lia| apply IH; eapply Forall_inv_tail; exact WIMG]. }
    pose proof (HB _ ltac:(do 3 (apply in_or_app; right); exact BIN)) as K2. cbn [blk_addr blk_size fst snd] in K2.
    pose proof (rw_cells_bound _ _ _ _ PK) as PKB0. pose proof (bytes_at_bound _ _ _ _ BS) as BSB. unfold zlength in *.
    split.
    - repeat match goal with |- _ /\ _ => split end; try assumption.
      + eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. apply DJS. lia.
      + subst tp. rewrite errno_RATP in *. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. apply DJI; unfold RERRNO; cbn; lia.
      + eapply (HH_rauxv_frame H HH); [exact AUX| exact MU| exact WM|]. apply Forall_forall. intros [u v] Hin.
        pose proof (proj1 (Forall_forall _ _) WLO _ Hin) as K1. pose proof (proj1 (Forall_forall _ _) WIMG _ Hin) as K3. cbn in K1, K3 |- *. unfold RAUXV_CELL. clear - K1 K3 SPB LO8K. lia.
      + eapply (HH_RHEAP_frame H HH); [exact HP| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. cbn beta. intros [u v] [[K1 K3]|(b & Hb & K1 & K3)]; [left; cbn in *; lia|].
        right; right. exists b. split; [apply in_or_app; right; apply in_or_app; left; exact Hb|]. cbn [fst snd] in K1, K3 |- *. clear - K1 K3. lia.
      + eapply LIBMID_xpres0; [exact LM| exact XPL|]. intros b Hb. apply in_or_app; right. apply LIBSUB. exact Hb.
      + eapply ENTRYobj_frameX; [exact EO| exact XPL| intros b Hb; apply avoids_nil].
      + eapply rw_cells_transport; [exact PK| exact MU| exact WM|]. apply DJS. clear - SPK. lia.
      + eapply (xpres_bytes_at _ _ _ _ _ _ _ XPL); [exact BS|]. split; [| apply Forall_nil]. right; right. exists (pbin, base, len). split; [apply in_or_app; right; exact BIN| cbn; lia].
      + eapply xpres_trans; [exact XP0|]. eapply xpres_of_munch_gen; [exact MU| exact WM|]. intros a Ha XC. clear MU WM WLO WIMG DJS DJI. induction W as [|[u v] W IH]; [exact I|]. cbn.
        pose proof (Forall_inv FW) as K1. cbn in K1. split; [| apply IH; eapply Forall_inv_tail; eassumption].
        destruct K1 as [[K1 K3]|(b & Hb & K1 & K3)].
        * destruct XC as [HC _]. destruct HC as [HC|[[HC _]|(b' & Hb' & Hr')]]; [clear - HC K3 SPR; lia| clear - HC K1 CEIL HCEILB; lia|].
          pose proof (HB _ ltac:(do 3 (apply in_or_app; right); exact Hb')) as BH'. clear - BH' Hr' K1 CEIL. lia.
        * intros R. rewrite (app_assoc XB NB) in HP. eapply (nb_not_client s' (mid_errblocks M) (XB ++ NB) LB (bv_unsigned sp) X0); [exact HP| clear - LO8K; lia| apply in_or_app; left; exact Hb| | exact XC]. clear - R K1 K3. lia.
    - intros A cs RC DJ0. eapply rw_cells_transport; [exact RC| exact MU| exact WM| exact DJ0].
  Qed.
  Lemma dworldX_stk : forall m m1 mo' s' errv' P xs NB c cur rem XB W,
    dworldX m mo' s' errv' P xs NB c cur rem XB -> munch W m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo spq ->
    Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= spq) W ->
    dworldX m1 mo' s' errv' P xs NB c cur rem XB
    /\ (forall A cs, rw_cells rsegs m A cs -> A + Z.of_nat (cells_size cs) <= hceil -> rw_cells rsegs m1 A cs).
  Proof.
    intros m m1 mo' s' errv' P xs NB c cur rem XB W FW MU WM MI1 ST1 HW.
    destruct (dworldX_munch _ _ _ _ _ _ _ _ _ _ _ _ _ FW MU WM MI1 ST1 ltac:(eapply Forall_impl; [| exact HW]; cbn beta; intros iv K; left; exact K)) as [FW1 TR].
    split; [exact FW1|]. intros A cs RC BND. apply TR; [exact RC|]. clear - HW BND CEIL.
    induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K. cbn in K. split; [lia| apply IH; eapply Forall_inv_tail; exact HW].
  Qed.

  (* [comment removed for export] *)
  Lemma dworldX_alloc : forall m m' mo' mo'' s' s'' errv' errv'' P xs NB c cur rem XB p A n,
    dworldX m mo' s' errv' P xs NB c cur rem XB ->
    hs_KREL H s'' mo'' -> hs_MPRES H mo' mo'' -> mem_inv rsegs m' -> stk rsegs m' lo spq ->
    rw_cells rsegs m' (errno_addr tp) [C4 errv''] -> hs_rauxv_ok H m' B ->
    xpres (mid_errblocks M ++ XB ++ NB ++ LB) spq memflag_foot m m' ->
    hs_RHEAP H s'' ((p, A, n) :: mid_errblocks M ++ XB ++ NB ++ LB) m' -> MEMFLAG m' 1 ->
    dworldX m' mo'' s'' errv'' P xs NB c cur rem ((p, A, n) :: XB)
    /\ (forall b A' cs, In b (XB ++ NB ++ LB) -> rw_cells rsegs m A' cs -> blk_addr b <= A' -> A' + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b ->
        rw_cells rsegs m' A' cs).
  Proof.
    intros m m' mo' mo'' s' s'' errv' errv'' P xs NB c cur rem XB p A n
      (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & EO & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & XP0) KREL' MP' MI' ST' ERR' AUX' XP HP' MF'.
    unfold dworldX. cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR. pose proof BSL as BSL'. unfold zlength in BSL'.
    pose proof LM as (_ & MF & _). rewrite MF0 in MF.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (AVM : forall b, In b (mid_errblocks M ++ XB ++ NB ++ LB) -> avoids memflag_foot (blk_addr b) (blk_size b)).
    { intros b Hb. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP Hb) as (_ & _ & _ & _ & OFF). unfold avoids, memflag_foot, A_mem_inited. constructor; [cbn; clear - OFF; lia| constructor]. }
    assert (SUBNL : forall b, In b (NB ++ LB) -> In b (mid_errblocks M ++ XB ++ NB ++ LB)) by (intros b Hb; do 2 (apply in_or_app; right); exact Hb).
    assert (XPL : xpres (NB ++ LB) (bv_unsigned sp + -144) memflag_foot m m') by (eapply xpres_weaken; [exact XP| lia| exact SUBNL| auto]).
    assert (AVF : avoids memflag_foot (bv_unsigned sp + -144) 144) by (unfold avoids, memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]).
    assert (AVP : avoids memflag_foot pk 24) by (unfold avoids, memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]).
    split.
    - repeat match goal with |- _ /\ _ => split end; try assumption.
      + eapply xpres_rw_cells'; [exact XP| exact FR| left; lia|]. unfold dx_frame. cbn [cells_size csize Nat.add length]. exact AVF.
      + eapply (mpres_trans H HH); [exact MP| exact MP'].
      + eapply PERM; [exact HP'|]. apply Permutation_middle.
      + rewrite <- M_eq1. eapply (LIBMID_mf LIB _ (bv_unsigned sp + -144)); [exact LM| exact XP| intros b Hb; apply SUBNL; apply in_or_app; right; apply LIBSUB; exact Hb| exact MF'].
      + eapply ENTRYobj_frameX; [exact EO| exact XPL|]. intros b Hb. apply AVM. apply SUBNL. eapply ENTRYobj_owned_law; [exact EO| exact Hb].
      + eapply xpres_rw_cells'; [exact XP| exact PK| left; clear - SPK; lia|]. unfold pk_cells. cbn [cells_size csize Nat.add length]. exact AVP.
      + eapply (xpres_bytes_at _ _ _ _ _ _ _ XPL); [exact BS|]. split.
        * right; right. exists (pbin, base, len). split; [apply in_or_app; right; exact BIN| cbn; lia].
        * eapply avoids_sub; [apply AVM; do 3 (apply in_or_app; right); exact BIN| cbn; lia| cbn; lia].
      + eapply xpres_trans; [exact XP0|].
        apply (xpres_weaken LB LB (bv_unsigned sp + -144) (bv_unsigned sp) ([] ++ []) X0); [| clear - SPR; lia| auto| intros a Ha; destruct Ha].
        eapply xpres_drop_memflag; [exact MF| exact MF'|]. cbn [app]. eapply xpres_weaken; [exact XP| lia| intros b Hb; do 3 (apply in_or_app; right); exact Hb| auto].
    - intros b A' cs Hb RC H1 H2. eapply xpres_rw_cells'; [exact XP| exact RC| |].
      + right; right. exists b. split; [apply in_or_app; right; exact Hb| lia].
      + eapply avoids_sub; [apply AVM; apply in_or_app; right; exact Hb| exact H1| exact H2].
  Qed.

  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  Lemma perm_split_disjoint : forall s L L1 L2 m b1 b2,
    hs_RHEAP H s L m -> Permutation L (L1 ++ L2) -> In b1 L1 -> In b2 L2 ->
    blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
  Proof.
    intros s L L1 L2 m b1 b2 HP PL H1 H2.
    pose proof (Permutation_NoDup (Permutation_map blk_id PL) (HH_RHEAP_blocks_nodup H HH _ _ _ HP)) as ND.
    eapply (HH_RHEAP_blocks_disjoint H HH); [exact HP| | | exact (nodup_ids_app_ne _ _ _ _ ND H1 H2)].
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

  (* [comment removed for export] *)
  Definition at_head (rb : Z) (k : config) : Prop :=
    exists (rax a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 w3 w7 w8 w9 w10 w11 : word) m mo' s' errv' P xs NB cur rem,
      dworld m mo' s' errv' P xs NB cur rem /\ rem <= rb /\ cfg_model k = mo'
      /\ cfg_ms k = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pk) w3
                          (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 1) w7 w8 w9 w10 w11 t3 t4 t5 t6)
                     F (Z_to_bv 64 DX_HEAD) fc None m (seg_rom rsegs).


  Lemma blocks_SK_facts : forall P K, 0 <= sk_cap K ->
    lb_bytes (blocks_SK P K) <= SK_SIZE + 8 * sk_cap K /\ Z.of_nat (length (blocks_SK P K)) <= 2 /\ 1 <= Z.of_nat (length (blocks_SK P K)) /\ lb_big (blocks_SK P K) <= 1
    /\ (sk_cap K = 0 -> lb_bytes (blocks_SK P K) = SK_SIZE /\ lb_big (blocks_SK P K) = 0).
  Proof.
    clear. intros P K C0. unfold blocks_SK. destruct (Z.eqb_spec (sk_cap K) 0) as [E0|NE];
      rewrite ?lb_bytes_cons, ?lb_big_cons; cbn [blk_size snd length lb_bytes lb_big fold_right app];
      rewrite (big1_small SK_SIZE) by (unfold SK_SIZE, BIGB; lia).
    - unfold SK_SIZE. lia.
    - pose proof (big1_range (8 * sk_cap K)). unfold SK_SIZE. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_push : forall m mo' s' errv' P K es NB c cur rem X' Ao pad (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w7 w8 w9 w10 w11 : word),
    dworldX m mo' s' errv' P (Some (K, es)) NB c cur rem (blocks_EXT Ao X') ->
    length pad = 4%nat -> rw_cells rsegs m Ao (ext_cells X' pad) ->
    match ex_val_o X' with None => ex_val X' = 0 | Some (pv, n) => 0 < ex_val X' /\ 1 <= n <= ex_len X' end ->
    0 <= ex_len X' < 512 -> c + 4 + ex_len X' <= rem0 - rem ->
    hs_SR H (at_head rem)
      (mkCfg (MS (mkR (Z_to_bv 64 DX_R8) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) (Z_to_bv 64 P) (Z_to_bv 64 Ao) a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 pk) (Z_to_bv 64 Ao) (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 1) w7 w8 w9 w10 w11 t3 t4 t5 t6)
                  F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros m mo' s' errv' P K es NB c cur rem X' Ao pad t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w7 w8 w9 w10 w11 FW PL XC VO XL CLE.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & EO & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & XP0).
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL). rewrite MF0 in MF.
    set (XB := blocks_EXT Ao X') in *. set (Lp := mid_errblocks M ++ XB ++ NB ++ LB) in *.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & HC) & EIN & O1 & O2 & O3 & O4 & XS).
    cbn [EW en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o] in EIN, XS, O1, O2, O3, O4, HC.
    unfold EXTS in XS. destruct XS as (PP & SO & LEN & F2).
    unfold XINV in XI. destruct XI as (KC & K4 & KCAP & E5 & EBY & EBG). set (EB := EBof K es) in *.
    pose proof SO as (_ & _ & KIN & KNC & KCAP2 & _ & _ & KDAT). unfold sk_num in KNC.
    (* [comment removed for export] *)
    assert (OIN : In (ex_id X', Ao, EXT_SIZE) Lp) by (subst Lp XB; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    pose proof (HB _ OIN) as OH. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP OIN) as (OP & _ & _ & _ & OOFF). cbn [blk_addr blk_size fst snd] in OH, OP, OOFF. unfold EXT_SIZE in OH, OOFF.
    (* [comment removed for export] *)
    pose proof (blocks_SK_facts P K ltac:(lia)) as (SKB & SKL & SKL1 & SKG & _).
    assert (NBB : lb_bytes NB = lb_bytes (blocks_SK P K) + lb_bytes EB) by (rewrite <- (lb_bytes_perm _ _ PB), lb_bytes_app; reflexivity).
    assert (NBL : length NB = (length (blocks_SK P K) + length EB)%nat) by (rewrite <- (Permutation_length PB), length_app; reflexivity).
    assert (NBG : lb_big NB = lb_big (blocks_SK P K) + lb_big EB) by (rewrite <- (lb_big_perm _ _ PB), lb_big_app; reflexivity).
    assert (XBB : lb_bytes XB <= EXT_SIZE + ex_len X' /\ Z.of_nat (length XB) <= 2 /\ lb_big XB = 0).
    { subst XB. unfold blocks_EXT, blocks_of. destruct (ex_val_o X') as [[pv n]|]; rewrite ?lb_bytes_cons, ?lb_big_cons; cbn [blk_size snd length lb_bytes lb_big fold_right];
        rewrite (big1_small EXT_SIZE) by (unfold EXT_SIZE, BIGB; lia); [rewrite (big1_small n) by (unfold BIGB; lia)|]; unfold EXT_SIZE; lia. }
    destruct XBB as (XBB & XBL & XBG).
    pose proof (sk_grow_le (sk_cap K) ltac:(lia)) as [GR GR5]. unfold zlength in *.
    assert (LpB : lb_bytes Lp + SKPUSH_COST K <= hs_LIVE_MAX H).
    { subst Lp. rewrite !lb_bytes_app in *. unfold SKPUSH_COST. unfold DECEXTS_BYTES, ERRDEBUG_BYTES, SK_SIZE, EXT_SIZE in *.
      pose proof (errph_nonneg (mid_err M)) as (EB0 & _). clear - BY EB0 NBB SKB EBY XBB GR KCAP K4 CLE CB1 CB2 PIN REMB XL. unfold pk_in in PIN. lia. }
    assert (LpC : Z.of_nat (length Lp) + 1 <= hs_LIVE_CNT_MAX H).
    { subst Lp. rewrite !length_app, !Nat2Z.inj_add in *. rewrite NBL, Nat2Z.inj_add in *.
      pose proof (errph_nonneg (mid_err M)) as (_ & EC0 & _). clear - CN EC0 SKL E5 XBL CLE CB1 CB2 PIN XL Q5. unfold pk_in in PIN. lia. }
    assert (LpG : lb_big Lp + big1 (8 * sk_grow (sk_cap K)) <= hs_LIVE_BIG_MAX H).
    { subst Lp. rewrite !lb_big_app in *. pose proof (big1_range (8 * sk_grow (sk_cap K))). pose proof (errph_nonneg (mid_err M)) as (_ & _ & EG0).
      clear - BG EG0 NBG SKG EBG XBG H0. lia. }
    (* [comment removed for export] *)
    pose proof (skpush_spec H HH HRE) as PS. unfold skpush_stmt in PS.
    eapply (sr_seq H HH).
    { eapply PS with (lo := lo) (B := B) (LB := Lp) (s := s') (a := P) (p := Ao) (v := 1) (K := K); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP| exact KREL| exact AUX| exact ST| exact CEIL| exact MI| exact LpB| exact LpC| exact LpG| exact TP].
      all: lazymatch goal with
           | |- 0 < _ < _ => clear - OP OH HCEILB; lia
           | |- SKobj _ _ _ _ => eapply SKobj_LB_mono; [exact SO| intros b Hb; subst Lp; do 2 (apply in_or_app; right); exact Hb]
           | |- sk_push_nocmp _ => left; exact KC
           | |- sk_cap _ <= SK_CAP_MAX => unfold SK_CAP_MAX; clear - KCAP K4 CLE CB2 PIN REMB XL; unfold pk_in in PIN; lia
           | |- _ <= B => clear - SPB SPR; lia
           | |- _ <= _ - SKPUSH_STACK =>
               unfold SKPUSH_STACK, SKRESERVE_STACK, CARRAY_STACK, CREALLOC_ARRAY_STACK, CREALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_realloc, RREALLOC_STACK,
                 FR_sk_insert, FR_sk_reserve, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; clear - LO8K; lia
           | |- rw_cells _ _ (errno_addr _) _ => exact ERR
           | |- C1env _ _ => split; [exact MF| split; [exact IM| exact G1]]
           | |- ?G => idtac "PUSHPRE" G
           end. }
    clear PS. intros [ms8 mo8] PO. unfold skpush_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m8 & errv8 & s8' & LB' & K' & data' & cap' & did' &
                    -> & KREL8 & MP8 & MI8 & ST8 & ERR8 & AUX8 & KEQ & PLB & HP8 & SO8 & XP8 & (v8 & (MF8 & IM8 & GM8) & VLE)).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in ST8, XP8 by lia.
    assert (V8 : v8 = 1) by (destruct MF8 as (fb8 & _ & _ & V01); lia). subst v8.
    (* [comment removed for export] *)
    subst Lp. pose proof (skpush_perm _ _ P _ _ _ _ (mid_errblocks M) XB EB LB LB' NB KEQ PLB PB ltac:(unfold sk_num, zlength; lia)) as [PL' CAPS].
    set (REST := mid_errblocks M ++ XB ++ EB ++ LB) in *.
    set (NB' := blocks_SK P K' ++ (EB ++ XB)).
    assert (IDK : sk_id K' = sk_id K) by (rewrite KEQ; reflexivity).
    assert (ELK : sk_elems K' = sk_elems K ++ [Ao]) by (rewrite KEQ; reflexivity).
    assert (CMK : sk_comp K' = sk_comp K) by (rewrite KEQ; reflexivity).
    assert (INR : forall b, In b REST -> In b LB') by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL'| apply in_or_app; right; exact Hb]).
    assert (INK : forall b, In b (blocks_SK P K') -> In b LB') by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL'| apply in_or_app; left; exact Hb]).
    assert (SUBLR : forall b, In b LB -> In b REST) by (intros b Hb; subst REST; do 3 (apply in_or_app; right); exact Hb).
    assert (SUBER : forall b, In b (EB ++ LB) -> In b REST) by (intros b Hb; subst REST; do 2 (apply in_or_app; right); exact Hb).
    assert (SUBXR : forall b, In b XB -> In b REST) by (intros b Hb; subst REST; apply in_or_app; right; apply in_or_app; left; exact Hb).
    assert (HB8 := HH_blocks_below H HH _ _ _ HP8).
    assert (DJ : forall b1 b2, In b1 (blocks_SK P K') -> In b2 REST -> blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1)
      by (intros b1 b2 H1 H2; exact (perm_split_disjoint _ _ _ _ _ _ _ HP8 PL' H1 H2)).
    assert (AV : forall b, In b REST -> avoids (memflag_foot ++ SK_foot P K') (blk_addr b) (blk_size b)).
    { intros b Hb. unfold avoids. apply Forall_app. split.
      - pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP8 (INR _ Hb)) as (_ & _ & _ & _ & OFF). unfold memflag_foot, A_mem_inited. constructor; [cbn; clear - OFF; lia| constructor].
      - apply SK_foot_avoids. intros b1 H1. pose proof (DJ _ _ H1 Hb). lia. }
    assert (KBL : forall b, In b (blocks_SK P K') -> blk_addr b + blk_size b <= hceil) by (intros b Hb; exact (HB8 _ (INK _ Hb))).
    assert (AVF : avoids (memflag_foot ++ SK_foot P K') (bv_unsigned sp + -144) 144).
    { unfold avoids. apply Forall_app. split; [unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]|].
      apply SK_foot_avoids. intros b1 H1. pose proof (KBL _ H1) as KB1. clear - KB1 CEIL LO8K. lia. }
    assert (AVP : avoids (memflag_foot ++ SK_foot P K') pk 24).
    { unfold avoids. apply Forall_app. split; [unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]|].
      apply SK_foot_avoids. intros b1 H1. pose proof (KBL _ H1) as KB1. clear - KB1 CEIL LO8K SPK. lia. }
    (* [comment removed for export] *)
    assert (HP9 : hs_RHEAP H s8' (mid_errblocks M ++ [] ++ NB' ++ LB) m8).
    { eapply PERM; [exact HP8|]. etransitivity; [exact PL'|]. subst NB' REST. cbn [app].
      etransitivity; [apply Permutation_app_swap_app|]. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_swap_app. }
    assert (SUBN : forall b, In b (blocks_SK P K') \/ In b EB \/ In b XB -> In b NB') by (intros b Hb; subst NB'; destruct Hb as [Hb|[Hb|Hb]]; apply in_or_app; [left| right; apply in_or_app; left| right; apply in_or_app; right]; exact Hb).
    (* [comment removed for export] *)
    assert (FR8 : rw_cells rsegs m8 (bv_unsigned sp + -144) (dx_frame j0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply xpres_rw_cells'; [exact XP8| exact FR| left; lia|]. unfold dx_frame. cbn [cells_size csize Nat.add length]. exact AVF. }
    assert (PK8 : rw_cells rsegs m8 pk (pk_cells cur base rem)).
    { eapply xpres_rw_cells'; [exact XP8| exact PK| left; clear - SPK; lia|]. unfold pk_cells. cbn [cells_size csize Nat.add length]. exact AVP. }
    assert (HC8 : rw_cells rsegs m8 ee (entry_cells (EW P (Some (K', es ++ [X']))) pad1 pad2 pad3 pad4)).
    { eapply xpres_rw_cells'; [exact XP8| exact HC| |].
      - right; right. exists (en_id E, ee, ENTRY_SIZE). split; [apply INR, SUBLR; exact EIN0|]. unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold ENTRY_SIZE. lia.
      - eapply avoids_sub; [apply AV; apply SUBLR; exact EIN0| cbn; lia|]. unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold ENTRY_SIZE. lia. }
    assert (XC8 : rw_cells rsegs m8 Ao (ext_cells X' pad)).
    { eapply xpres_rw_cells'; [exact XP8| exact XC| |].
      - right; right. exists (ex_id X', Ao, EXT_SIZE). split; [apply INR, SUBXR; subst XB; left; reflexivity|]. unfold ext_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold EXT_SIZE. lia.
      - eapply avoids_sub; [apply AV; apply SUBXR; subst XB; left; reflexivity| cbn; lia|]. unfold ext_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold EXT_SIZE. lia. }
    assert (BS8 : bytes_at rsegs m8 base bs).
    { eapply xpres_bytes_at; [exact XP8| exact BS|]. split.
      - right; right. exists (pbin, base, len). split; [apply INR, SUBLR; exact BIN|]. cbn [blk_addr blk_size fst snd]. pose proof BSL as BSLq; unfold zlength in BSLq |- *. lia.
      - eapply avoids_sub; [apply AV; apply SUBLR; exact BIN| cbn; lia| cbn [blk_addr blk_size fst snd]; pose proof BSL as BSLq; unfold zlength in BSLq |- *; lia]. }
    assert (F28 : Forall2 (fun p X => EXTobj (NB' ++ LB) m8 p X) (sk_elems K) es).
    { assert (F2a : Forall2 (fun p X => EXTobj (EB ++ LB) m p X) (sk_elems K) es).
      { eapply (EXTs_frame (NB ++ LB) (EB ++ LB) (EB ++ LB) (bv_unsigned sp + -144) m m); [exact F2| intros b Hb; apply in_or_app; left; exact Hb| auto| apply xpres_refl|].
        intros b Hb. pose proof (HB _ ltac:(do 2 (apply in_or_app; right); apply in_or_app; left; eapply Permutation_in; [exact PB| apply in_or_app; right; exact Hb])) as KB1. clear - KB1 CEIL LO8K. lia. }
      eapply (EXTs_frame (EB ++ LB) (EB ++ LB) (NB' ++ LB) (bv_unsigned sp + -144) m8 m8); [| intros b Hb; apply in_or_app; left; exact Hb| | apply xpres_refl|].
      - eapply (EXTs_frameX (EB ++ LB) (bv_unsigned sp + -144) (memflag_foot ++ SK_foot P K')); [exact F2a| eapply xpres_weaken; [exact XP8| lia| intros b Hb; apply INR, SUBER; exact Hb| auto]|].
        intros b Hb. apply AV. apply SUBER. apply in_or_app. left. exact Hb.
      - intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply SUBN; right; left; exact Hb| right; exact Hb].
      - intros b Hb. pose proof (HB8 _ (INR _ (SUBER _ ltac:(apply in_or_app; left; exact Hb)))) as KB1. clear - KB1 CEIL LO8K. lia. }
    assert (LM8 : LIBMID LIB m8 M).
    { rewrite <- M_eq1. apply (LIBMID_mf_X LIB LB' (bv_unsigned sp + -144) (SK_foot P K') m m8 M); [exact LM| exact XP8| intros b Hb; apply INR, SUBLR, LIBSUB; exact Hb| exact MF8| |].
      - intros a Ha. destruct (SK_foot_rin _ _ _ Ha) as (b1 & H1 & R1).
        pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP8 (INK _ H1)) as BR. exact (block_cell_off_image _ _ BR R1).
      - intros a b Ha Hb K0. destruct (SK_foot_rin _ _ _ Ha) as (b1 & H1 & R1). pose proof (DJ _ _ H1 (SUBLR _ (LIBSUB _ Hb))) as DJ1. clear - DJ1 R1 K0. lia. }
    assert (XP08 : xpres LB (bv_unsigned sp) X0 m0 m8).
    { eapply xpres_trans; [exact XP0|].
      apply (xpres_weaken LB LB (bv_unsigned sp) (bv_unsigned sp) [] X0); [| lia| auto| intros a Ha; destruct Ha].
      eapply (xpres_shrink LB' LB (bv_unsigned sp + -144) (bv_unsigned sp) [] (SK_foot P K')); [| clear - SPR; lia| intros b Hb; apply INR, SUBLR; exact Hb|].
      - eapply (xpres_drop_memflag _ _ [] (SK_foot P K')); [exact MF| exact MF8| cbn [app]; exact XP8].
      - intros a Ha XCa. destruct (SK_foot_rin _ _ _ Ha) as (b1 & H1 & R1).
        eapply (nb_not_client s8' (mid_errblocks M) NB' LB (bv_unsigned sp)); [cbn [app] in HP9; exact HP9| clear - LO8K; lia| apply SUBN; left; exact H1| exact R1| exact XCa]. }
    (* [comment removed for export] *)
    pose proof OF0 as (Q1 & Q2 & Q3 & Q4).
    assert (EBE : EBof K' (es ++ [X']) = EB ++ XB) by (rewrite KEQ, (EBof_push K es Ao X') by exact LEN; subst EB XB; reflexivity).
    assert (XI9 : XINV P (Some (K', es ++ [X'])) (rem0 - rem)).
    { unfold XINV. rewrite EBE, CMK. subst XB. unfold zlength in *.
      rewrite !length_app, !lb_bytes_app, !lb_big_app, !Nat2Z.inj_add. cbn [length]. revert VO XBB XBL XBG. unfold blocks_EXT, blocks_of.
      assert (CAP9 : 0 <= sk_cap K' /\ 5 * sk_cap K' <= 8 * (Z.of_nat (length es) + 1) + 20).
      { destruct CAPS as [C1|[[C0 C4]|(CG & NC & C4)]]; [clear - C1 KCAP; lia| clear - C0 C4 KCAP; lia|].
        rewrite CG. unfold sk_num, zlength in NC. rewrite <- LEN in NC. pose proof (sk_grow_le (sk_cap K) ltac:(clear - C4; lia)) as [GR2 GR3]. clear - GR2 GR3 NC KCAP. lia. }
      destruct (ex_val_o X') as [[pv n]|]; intros VO XBB XBL XBG;
        rewrite ?lb_bytes_cons, ?lb_big_cons; cbn [blk_size snd length lb_bytes lb_big fold_right]; rewrite (big1_small EXT_SIZE) by (unfold EXT_SIZE, BIGB; lia);
        [rewrite (big1_small n) by (unfold BIGB; lia)|]; unfold EXT_SIZE; clear - KC K4 CAP9 E5 EBY EBG CLE XL VO; lia. }
    assert (NEWX : Forall2 (fun p X => EXTobj (NB' ++ LB) m8 p X) [Ao] [X']).
    { apply Forall2_cons; [| apply Forall2_nil].
      unfold EXTobj. split; [exists pad; split; [exact PL| exact XC8]|]. split; [apply in_or_app; left; apply SUBN; right; right; subst XB; left; reflexivity|].
      revert VO. unfold ofield. subst XB. unfold blocks_EXT, blocks_of in SUBN. destruct (ex_val_o X') as [[pv n]|]; intros VO; [| exact VO].
      split; [lia|]. split; [lia|]. apply in_or_app. left. apply SUBN. right. right. right. left. reflexivity. }
    assert (FW9 : dworld m8 mo8 s8' errv8 P (Some (K', es ++ [X'])) NB' cur rem).
    { unfold dworld, dworldX. repeat match goal with |- _ /\ _ => split end; try assumption.
      all: lazymatch goal with
           | |- hs_MPRES _ _ _ => eapply (mpres_trans H HH); [exact MP| exact MP8]
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
           | |- Permutation _ _ => unfold blocks_EXTS; fold (EBof K' (es ++ [X'])); rewrite EBE; subst NB'; apply Permutation_refl
           | |- XINV _ _ _ => exact XI9
           | |- 0 <= rem0 - _ => clear - CB1 CLE XL; lia
           | |- rem0 - _ <= rem0 - _ => clear; lia
           | |- ?G => idtac "FW9" G
           end. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL8| eapply dx_seg9; [| exact MI8]|].
    { unfold sk_num, zlength. clear - KNC KCAP2. lia. }
    cbv beta. intros ms9 ->.
    apply (sr_done H HH). unfold at_head. cbn [cfg_ms cfg_model].
    do 22 eexists. exists m8, mo8, s8', errv8, P, (Some (K', es ++ [X'])), NB', cur, rem.
    split; [exact FW9|]. split; [lia|]. split; [reflexivity|]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_newsk : forall m mo' s' errv' c cur rem X' Ao pad (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w7 w8 w9 w10 w11 : word),
    dworldX m mo' s' errv' 0 None [] c cur rem (blocks_EXT Ao X') ->
    length pad = 4%nat -> rw_cells rsegs m Ao (ext_cells X' pad) ->
    match ex_val_o X' with None => ex_val X' = 0 | Some (pv, n) => 0 < ex_val X' /\ 1 <= n <= ex_len X' end ->
    0 <= ex_len X' < 512 -> c + 4 + ex_len X' <= rem0 - rem ->
    hs_SR H (at_head rem)
      (mkCfg (MS (mkR (Z_to_bv 64 DX_R4) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 pk) (Z_to_bv 64 Ao) (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 1) w7 w8 w9 w10 w11 t3 t4 t5 t6)
                  F (Z_to_bv 64 P_OPENSSL_sk_new_null) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros m mo' s' errv' c cur rem X' Ao pad t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w7 w8 w9 w10 w11 FW PL XC VO XL CLE.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & EO & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & XP0).
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL). rewrite MF0 in MF.
    cbn [app] in HP. set (XB := blocks_EXT Ao X') in *. set (Lp := mid_errblocks M ++ XB ++ LB) in *.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (OIN : In (ex_id X', Ao, EXT_SIZE) Lp) by (subst Lp XB; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    pose proof (HB _ OIN) as OH. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP OIN) as (OP & _). cbn [blk_addr blk_size fst snd] in OH, OP. unfold EXT_SIZE in OH.
    assert (XBB : lb_bytes XB <= EXT_SIZE + ex_len X' /\ Z.of_nat (length XB) <= 2 /\ lb_big XB = 0).
    { subst XB. unfold blocks_EXT, blocks_of. destruct (ex_val_o X') as [[pv n]|]; rewrite ?lb_bytes_cons, ?lb_big_cons; cbn [blk_size snd length lb_bytes lb_big fold_right];
        rewrite (big1_small EXT_SIZE) by (unfold EXT_SIZE, BIGB; lia); [rewrite (big1_small n) by (unfold BIGB; lia)|]; unfold EXT_SIZE; lia. }
    destruct XBB as (XBB & XBL & XBG). unfold zlength in *.
    (* [comment removed for export] *)
    pose proof (sknew_null_spec H HH) as SN. unfold sknew_null_stmt, sknew_stmt_gen in SN.
    eapply (sr_seq H HH).
    { eapply SN with (lo := lo) (B := B) (LB := Lp) (s := s') (c := 0) (v := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP| exact KREL| exact AUX| exact ST| exact CEIL| exact MI| exact TP].
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => subst Lp; rewrite !lb_bytes_app in *; unfold DECEXTS_BYTES, ERRDEBUG_BYTES, SK_SIZE, EXT_SIZE in *;
                                        pose proof (errph_nonneg (mid_err M)) as (EB0 & _); clear - BY EB0 XBB XL CLE CB1 CB2 PIN REM1; unfold pk_in in PIN; lia
           | |- Z.of_nat (length _) + _ <= _ => subst Lp; rewrite !length_app, !Nat2Z.inj_add in *; pose proof (errph_nonneg (mid_err M)) as (_ & EC0 & _); clear - CN EC0 XBL REM1 Q5; lia
           | |- lb_big _ <= _ => subst Lp; rewrite !lb_big_app in *; pose proof (errph_nonneg (mid_err M)) as (_ & _ & EG0); clear - BG EG0 XBG; lia
           | |- _ <= B => clear - SPB SPR; lia
           | |- _ <= _ - _ => unfold FR_sk_new_null, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; clear - LO8K; lia
           | |- rw_cells _ _ (errno_addr _) _ => exact ERR
           | |- C1env _ _ => split; [exact MF| split; [exact IM| exact G1]]
           | |- ?G => idtac "SNPRE" G
           end. }
    clear SN. intros [ms2 mo2] PO. unfold sknew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m2 & errv2 & Ps & id & did & s2' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & PSP & HP2 & SO2 & (MF2 & IM2 & GM2)).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in ST2, XP2 by lia.
    subst Lp. destruct (dworldX_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FW KREL2 MP2 MI2 ST2 ERR2 AUX2 XP2 HP2 MF2) as [FW2 TR2].
    pose proof (TR2 (ex_id X', Ao, EXT_SIZE) Ao _ ltac:(apply in_or_app; left; subst XB; left; reflexivity) XC ltac:(cbn; lia)
                  ltac:(unfold ext_cells; cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]; unfold EXT_SIZE; lia)) as XC2.
    clear TR2.
    pose proof (HH_blocks_below H HH _ _ _ HP2 (id, Ps, SK_SIZE) ltac:(left; reflexivity)) as SH. cbn [blk_addr blk_size fst snd] in SH. unfold SK_SIZE in SH.
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp + -144) Ao 16 HP2
                  ltac:(right; right; exists (ex_id X', Ao, EXT_SIZE); split; [exact OIN| cbn; unfold EXT_SIZE; lia]) ltac:(clear - CEIL LO8K; lia) ltac:(lia)) as DSO.
    unfold SK_SIZE in DSO.
    set (SB := (id, Ps, SK_SIZE)) in *.
    assert (SKB : SK_below Ps (sk_fresh 0 id did) lo) by (split; [unfold SK_SIZE; clear - SH CEIL; lia| left; reflexivity]).
    assert (DJO : disjoint_from [(lo, bv_unsigned sp + -144); (Ps, Ps + SK_SIZE)] Ao (Z.of_nat (cells_size (ext_cells X' pad)))).
    { unfold ext_cells. cbn [cells_size csize Nat.add length]. unfold SK_SIZE. cbn. clear - OH CEIL DSO. lia. }
    assert (WOK : Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= bv_unsigned sp + -144) \/ (exists b, In b (SB :: XB) /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b))
                    [(lo, bv_unsigned sp + -144); (Ps, Ps + SK_SIZE)]).
    { constructor; [left; cbn; lia|]. constructor; [| constructor]. right. exists SB. split; [left; reflexivity| subst SB; cbn; lia]. }
    (* [comment removed for export] *)
    pose proof FW2 as (_ & _ & FR2 & _).
    eapply (sr_evt_krel H HH); [exact KREL2| eapply dx_seg5; [exact FR2| clear - LO8K CEIL HCEILB; lia| exact MI2]|]. cbv beta. intros ms3 ->.
    pose proof skset_cmp_thunks_spec as SC. unfold skset_cmp_thunks_stmt, skset_stmt_at in SC.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply SC with (lo := lo) (a := Ps) (K := sk_fresh 0 id did); rewrite ?unsigned_lit by lia; try reflexivity;
                                 [unfold DX_THUNK_CMP; lia| exact SO2| exact SKB| exact ST2| clear - LO8K; lia| exact MI2]|].
    clear SC. cbv beta. intros ms4 (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & SO4).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in MU4, ST4 by lia.
    destruct (dworldX_munch _ _ _ _ _ _ _ _ _ _ _ _ _ FW2 MU4 WM4 MI4 ST4 WOK) as [FW4 TR4]. pose proof (TR4 _ _ XC2 DJO) as XC4. clear TR4 FW2 XC2.
    (* [comment removed for export] *)
    pose proof FW4 as (_ & _ & FR4 & _).
    eapply (sr_evt_krel H HH); [exact KREL2| eapply dx_seg6; [exact FR4| clear - LO8K CEIL HCEILB; lia| exact MI4]|]. cbv beta. intros ms5 ->.
    pose proof skset_copy_thunks_spec as SC. unfold skset_copy_thunks_stmt, skset_stmt_at in SC.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply SC with (lo := lo) (a := Ps); rewrite ?unsigned_lit by lia; try reflexivity;
                                 [unfold DX_THUNK_COPY; lia| exact SO4| exact SKB| exact ST4| clear - LO8K; lia| exact MI4]|].
    clear SC. cbv beta. intros ms6 (y0' & y1' & y2' & h1' & h2' & h3' & h4' & h5' & h6' & h7' & y3' & y4' & y5' & y6' & m6 & -> & MU6 & WM6 & MI6 & ST6 & SO6).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in MU6, ST6 by lia.
    destruct (dworldX_munch _ _ _ _ _ _ _ _ _ _ _ _ _ FW4 MU6 WM6 MI6 ST6 WOK) as [FW6 TR6]. pose proof (TR6 _ _ XC4 DJO) as XC6. clear TR6 FW4 XC4.
    (* [comment removed for export] *)
    pose proof FW6 as (_ & _ & FR6 & _).
    eapply (sr_evt_krel H HH); [exact KREL2| eapply dx_seg7; [exact FR6| clear - LO8K CEIL HCEILB; lia| exact MI6]|]. cbv beta. intros ms7 ->.
    pose proof skset_thunks_spec as SC. unfold skset_thunks_stmt, skset_stmt_at in SC.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply SC with (lo := lo) (a := Ps); rewrite ?unsigned_lit by lia; try reflexivity;
                                 [unfold DX_THUNK_FREE; lia| exact SO6| exact SKB| exact ST6| clear - LO8K; lia| exact MI6]|].
    clear SC. cbv beta. intros ms8 (y0'' & y1'' & y2'' & h1'' & h2'' & h3'' & h4'' & h5'' & h6'' & h7'' & y3'' & y4'' & y5'' & y6'' & m8 & -> & MU8 & WM8 & MI8 & ST8 & SO8).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in MU8, ST8 by lia.
    destruct (dworldX_munch _ _ _ _ _ _ _ _ _ _ _ _ _ FW6 MU8 WM8 MI8 ST8 WOK) as [FW8 TR8]. pose proof (TR8 _ _ XC6 DJO) as XC8. clear TR8 FW6 XC6.
    set (K3 := sk_with_thunk (sk_with_thunk (sk_with_thunk (sk_fresh 0 id did) O_SK_CMPTH DX_THUNK_CMP) O_SK_COPYTH DX_THUNK_COPY) O_SK_FREETH DX_THUNK_FREE) in *.
    (* [comment removed for export] *)
    pose proof FW8 as (MI8' & ST8' & FR8 & ERR8 & AUX8 & KREL8 & MP8 & HP8 & LM8 & EO8 & _ & _ & PK8 & PIN8 & CR8 & _ & BS8 & XP08).
    destruct (dworld_entry _ _ _ _ _ _ _ _ _ _ _ FW8) as (pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC8 & EEP & EEH & _).
    eapply (sr_evt_krel H HH); [exact KREL8| eapply (dx_seg8) with (ee := ee) (P := Ps) (A := Ao) (E := EW 0 None);
                                 [exact EC8| exact EEP| clear - EEH HCEILB; lia| clear - PSP SH HCEILB; lia| exact MI8]|].
    cbv beta. intros ms9 (m9 & MU9 & WM9 & MI9 & EC9 & ->). cbn [EW en_version en_pname en_pname_o en_publen en_pub en_pub_o en_nsuites en_suites en_suites_o en_maxname en_cfgid en_exts_o en_loadtime en_forretry en_enclen en_encoded en_encoded_o en_id] in EC9.
    unfold ENTRY_SIZE in MU9.
    (* [comment removed for export] *)
    assert (HB8 := HH_blocks_below H HH _ _ _ HP8).
    assert (EIN8 : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M ++ (SB :: XB) ++ [] ++ LB)) by (do 3 (apply in_or_app; right); exact EIN0).
    pose proof (HB8 _ EIN8) as EH. cbn [blk_addr blk_size fst snd] in EH. unfold ENTRY_SIZE in EH.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP8 EIN8) as (_ & _ & _ & _ & EOFF). cbn [blk_addr blk_size fst snd] in EOFF. unfold ENTRY_SIZE in EOFF.
    assert (DJE : forall b, In b (mid_errblocks M ++ (SB :: XB) ++ [] ++ LB) -> blk_id b <> en_id E -> blk_addr b + blk_size b <= ee \/ ee + 104 <= blk_addr b).
    { intros b Hb NE. pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP8 Hb EIN8 NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ. unfold ENTRY_SIZE in DJ. exact DJ. }
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP8) as ND8.
    assert (NEX : forall b, In b (mid_errblocks M ++ (SB :: XB)) -> blk_id b <> en_id E).
    { intros b Hb K0. rewrite (app_assoc _ _ ([] ++ LB)) in ND8. cbn [app] in ND8. exact (nodup_ids_app_ne _ _ _ _ ND8 Hb EIN0 K0). }
    assert (FW9 : dworldX m9 mo2 s2' errv2 Ps (Some (K3, [])) [SB] c cur rem XB).
    { unfold dworldX. cbv delta [spq]. repeat match goal with |- _ /\ _ => split end; try assumption.
      all: lazymatch goal with
           | |- stk _ _ _ _ => eapply stk_transport_disjoint; [exact ST8'| exact MU9| exact WM9| cbn; clear - EH CEIL; lia]
           | |- rw_cells _ _ (bv_unsigned sp + -144) _ => eapply rw_cells_transport; [exact FR8| exact MU9| exact WM9| cbn; clear - EH CEIL LO8K; lia]
           | |- rw_cells _ _ (errno_addr _) _ => rewrite TP in *; rewrite errno_RATP in *; eapply rw_cells_transport; [exact ERR8| exact MU9| exact WM9| unfold RERRNO; cbn; clear - EOFF; lia]
           | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX8| exact MU9| exact WM9|]; unfold RAUXV_CELL; apply Forall_cons; [cbn; clear - EH EOFF CEIL LO8K SPB; lia| apply Forall_nil]
           | |- hs_RHEAP _ _ _ _ =>
               eapply PERM; [eapply (HH_RHEAP_frame H HH); [exact HP8| exact MU9| exact WM9|]; apply Forall_cons; [right; right; exists (en_id E, ee, ENTRY_SIZE); split; [exact EIN8| cbn; unfold ENTRY_SIZE; lia]| apply Forall_nil]|];
               cbn [app]; apply Permutation_app_head; change (SB :: XB ++ LB) with ([SB] ++ XB ++ LB); rewrite (app_assoc [SB] XB); rewrite (app_assoc XB [SB]); apply Permutation_app_tail; apply Permutation_app_comm
           | |- LIBMID _ _ _ =>
               eapply (LIBMID_xpres0 LIB LIB (bv_unsigned sp + -144)); [exact LM8| | auto];
               eapply xpres_of_munch_gen; [exact MU9| exact WM9|]; intros a Ha [HC _]; cbn; split; [| exact I];
               destruct HC as [HC|[[HC _]|(b' & Hb' & Hr')]]; [clear - HC EH CEIL LO8K; lia| clear - HC EOFF; lia|];
               pose proof (DJE b' ltac:(do 3 (apply in_or_app; right); apply LIBSUB; exact Hb') (IDS _ _ Hb' ltac:(left; reflexivity))) as DJ; clear - DJ Hr'; lia
           | |- ENTRYobj _ _ _ _ =>
               unfold ENTRYobj; cbn [EW en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o];
               pose proof OF0 as (Q1 & Q2 & Q3 & Q4);
               split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4| exact EC9]|];
               split; [apply in_or_app; right; exact EIN0|];
               split; [eapply ofield_LB_mono; [exact Q1| intros b Hb; apply in_or_app; right; exact Hb]|];
               split; [eapply ofield_LB_mono; [exact Q2| intros b Hb; apply in_or_app; right; exact Hb]|];
               split; [eapply ofield_LB_mono; [exact Q3| intros b Hb; apply in_or_app; right; exact Hb]|];
               split; [eapply ofield_LB_mono; [exact Q4| intros b Hb; apply in_or_app; right; exact Hb]|];
               unfold EXTS; split; [exact PSP|]; split; [| split; [reflexivity| apply Forall2_nil]];
               eapply SKobj_LB_mono; [| intros b Hb; apply in_or_app; left; exact Hb];
               eapply (SKobj_frame _ [SB] (bv_unsigned sp + -144)); [exact SO8| intros b Hb; subst K3; rewrite !e_blocks_SK_with_thunk in Hb; unfold blocks_SK in Hb; cbn in Hb; destruct Hb as [Hb|[]]; left; exact Hb|];
               eapply xpres_of_munch_gen; [exact MU9| exact WM9|]; intros a Ha [HC _]; cbn; split; [| exact I];
               destruct HC as [HC|[[HC _]|(b' & Hb' & Hr')]]; [clear - HC EH CEIL LO8K; lia| clear - HC EOFF; lia|];
               destruct Hb' as [<-|[]]; pose proof (DJE SB ltac:(apply in_or_app; right; left; reflexivity) (NEX SB ltac:(apply in_or_app; right; left; reflexivity))) as DJ; clear - DJ Hr'; lia
           | |- Permutation _ _ => unfold blocks_EXTS; subst K3; rewrite !e_blocks_SK_with_thunk, !e_sk_elems_with_thunk; unfold blocks_SK; cbn; apply Permutation_refl
           | |- XINV _ _ _ => unfold XINV, EBof; subst K3; rewrite !e_sk_elems_with_thunk; cbn -[Z.mul Z.add Z.le]; unfold zlength; cbn [length Z.of_nat]; clear - CB1; lia
           | |- rw_cells _ _ pk _ => eapply rw_cells_transport; [exact PK8| exact MU9| exact WM9| cbn; clear - EH CEIL LO8K SPK; lia]
           | |- bytes_at _ _ base _ =>
               eapply bytes_at_transport; [exact BS8| exact MU9|]; cbn; split; [| exact I];
               pose proof (DJE (pbin, base, len) ltac:(do 3 (apply in_or_app; right); exact BIN) ltac:(cbn; intros K0; apply EBIN; symmetry; exact K0)) as KKq; cbn [blk_addr blk_size fst snd] in KKq;
               pose proof BSL as BSLq; unfold zlength in BSLq |- *; clear - KKq BSLq; lia
           | |- xpres LB _ X0 m0 _ =>
               eapply xpres_trans; [exact XP08|]; eapply xpres_of_munch; [exact MU9| exact WM9| | intros b Hb; apply HB8; do 3 (apply in_or_app; right); exact Hb];
               apply Forall_cons; [right; cbn; intros a Ha; unfold X0, ENTRY_SIZE; cbn [rin_ivs fst snd]; right; left; exact Ha| apply Forall_nil]
           | |- ?G => idtac "NSK9" G
           end. }
    pose proof (proj1 (proj1 XC8)) as WF. cbn [cells_wf cell_wf ext_cells] in WF.
    eapply dx_push; [exact FW9| exact PL| | exact VO| exact XL| exact CLE].
    eapply rw_cells_transport; [exact XC8| exact MU9| exact WM9|]. unfold ext_cells. cbn [cells_size csize Nat.add length]. cbn. split; [| exact I].
    exact (DJE (ex_id X', Ao, EXT_SIZE) ltac:(apply in_or_app; right; apply in_or_app; left; right; subst XB; left; reflexivity) (NEX _ ltac:(apply in_or_app; right; right; subst XB; left; reflexivity))).
  Qed.

  (* [comment removed for export] *)
  Lemma dx_from_malloc : forall m mo' s' errv' P xs NB c cur rem (val xl b0 b1 : Z) (vo : oblk) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w3 w9 : word),
    dworldX m mo' s' errv' P xs NB c cur rem (blocks_of val vo) ->
    match vo with None => val = 0 | Some (pv, n) => 0 < val /\ 1 <= n <= xl end ->
    0 <= xl < 512 -> 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= val < 2^64 -> c + 4 + xl <= rem0 - rem ->
    hs_SR H (at_head rem)
      (mkCfg (MS (mkR (Z_to_bv 64 DX_R3) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) (Z_to_bv 64 16) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 217) a3 a4 a5 a6 a7
                        (Z_to_bv 64 pk) w3 (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 1) (Z_to_bv 64 b1) (Z_to_bv 64 b0) w9 (Z_to_bv 64 val) (Z_to_bv 64 xl) t3 t4 t5 t6)
                  F (Z_to_bv 64 P_CRYPTO_malloc) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros m mo' s' errv' P xs NB c cur rem val xl b0 b1 vo t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w3 w9 FW VO XL B0 B1 VR CLE.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & EO & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & XP0).
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL). rewrite MF0 in MF.
    set (VL := blocks_of val vo) in *. set (Lp := mid_errblocks M ++ VL ++ NB ++ LB) in *.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (VLB : lb_bytes VL <= xl /\ Z.of_nat (length VL) <= 1 /\ lb_big VL = 0).
    { subst VL. unfold blocks_of. destruct vo as [[pv n]|]; rewrite ?lb_bytes_cons, ?lb_big_cons; cbn [blk_size snd length lb_bytes lb_big fold_right];
        [rewrite (big1_small n) by (unfold BIGB; lia)|]; lia. }
    destruct VLB as (VLB & VLL & VLG). unfold zlength in *.
    (* [comment removed for export] *)
    assert (NBB : lb_bytes NB <= 88 + 8 * c /\ 5 * Z.of_nat (length NB) <= 2 * c + 10 /\ lb_big NB <= 1).
    { revert PB XI. unfold XINV. destruct xs as [[K es]|]; intros PB XI.
      - destruct XI as (KC & K4 & KCAP & E5 & EBY & EBG). rewrite blocks_EXTS_some in PB.
        pose proof (blocks_SK_facts P K ltac:(lia)) as (SKB & SKL & _ & SKG & _).
        rewrite <- (lb_bytes_perm _ _ PB), <- (Permutation_length PB), <- (lb_big_perm _ _ PB), lb_bytes_app, length_app, lb_big_app, Nat2Z.inj_add.
        unfold SK_SIZE in SKB. unfold zlength in *. clear - K4 KCAP E5 EBY EBG SKB SKL SKG. lia.
      - destruct XI as [_ C0]. pose proof (Permutation_nil PB) as ->. cbn. clear - C0. lia. }
    destruct NBB as (NBB & NBL & NBG).
    (* [comment removed for export] *)
    pose proof (cmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
    eapply (sr_seq H HH).
    { eapply CM with (lo := lo) (B := B) (LB := Lp) (s := s') (n := 16) (v := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP| exact KREL| exact AUX| exact ST| exact CEIL| exact MI| exact TP| exact MF| exact IM| exact G1].
      all: lazymatch goal with
           | |- 1 <= 16 < _ => lia
           | |- lb_bytes _ + _ <= _ => subst Lp; rewrite !lb_bytes_app in *; unfold DECEXTS_BYTES, ERRDEBUG_BYTES in *;
                                        pose proof (errph_nonneg (mid_err M)) as (EB0 & _); clear - BY EB0 VLB NBB XL CLE CB1 CB2 PIN REM1; unfold pk_in in PIN; lia
           | |- Z.of_nat (length _) + _ <= _ => subst Lp; rewrite !length_app, !Nat2Z.inj_add in *; pose proof (errph_nonneg (mid_err M)) as (_ & EC0 & _); clear - CN EC0 VLL NBL CLE CB2 PIN XL Q5; unfold pk_in in PIN; lia
           | |- lb_big _ + _ <= _ => subst Lp; rewrite !lb_big_app in *; rewrite (big1_small 16) by (unfold BIGB; lia); pose proof (errph_nonneg (mid_err M)) as (_ & _ & EG0); clear - BG EG0 VLG NBG; lia
           | |- _ <= B => clear - SPB SPR; lia
           | |- _ <= _ - CMALLOC_STACK => unfold CMALLOC_STACK, FR_CRYPTO_malloc, RMALLOC_STACK; clear - LO8K; lia
           | |- rw_cells _ _ (errno_addr _) _ => exact ERR
           | |- ?G => idtac "CMPRE" G
           end. }
    clear CM. intros [ms2 mo2] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m2 & errv2 & Ao & junk & po & s2' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & OBR & HP2 & OC2 & MF2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in ST2, XP2 by lia.
    subst Lp. destruct (dworldX_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FW KREL2 MP2 MI2 ST2 ERR2 AUX2 XP2 HP2 MF2) as [FW2 _].
    pose proof OBR as (OP & _ & _ & OH & OOFF). change (Z.to_nat 16) with 16%nat in OC2.
    (* [comment removed for export] *)
    destruct (dworld_entry _ _ _ _ _ _ _ _ _ _ _ FW2) as (pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC2 & EEP & EEH & PR & _).
    assert (EIN2 : In (en_id E, ee, ENTRY_SIZE) (mid_errblocks M ++ VL ++ NB ++ LB)) by (do 3 (apply in_or_app; right); exact EIN0).
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp + -144) ee ENTRY_SIZE HP2
                  ltac:(right; right; exists (en_id E, ee, ENTRY_SIZE); split; [exact EIN2| cbn; lia]) ltac:(clear - CEIL LO8K; lia) ltac:(unfold ENTRY_SIZE; lia)) as DEO.
    unfold ENTRY_SIZE in DEO, EEH.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply dx_seg4 with (E := EW P xs) (A := Ao) (val := val) (b0 := b0) (b1 := b1) (extlen := xl);
      [exact EC2| exact EEP| unfold ENTRY_SIZE; clear - EEH HCEILB; lia| cbn [EW en_exts]; exact PR| exact OC2| exact OP| clear - OH HCEILB; lia| unfold ENTRY_SIZE; clear - DEO; lia
      | exact B0| exact B1| exact XL| exact VR| exact MI2]|].
    cbv beta. intros ms3 (m3 & jk & MU3 & WM3 & MI3 & XC3 & CASES). cbn [EW en_exts] in CASES.
    assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]. cbn. clear - OH CEIL. lia. }
    destruct (dworldX_munch _ _ _ _ _ _ _ _ _ _ _ _ _ FW2 MU3 WM3 MI3 ST3
                ltac:(apply Forall_cons; [right; exists (po, Ao, 16); split; [left; reflexivity| cbn; lia]| apply Forall_nil])) as [FW3 _].
    pose proof (proj1 (proj1 XC3)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & _ & LJ & _).
    set (X' := mkEXT (256 * b0 + b1) xl val vo po).
    assert (XBE : (po, Ao, 16) :: VL = blocks_EXT Ao X') by (subst VL X'; reflexivity).
    assert (XCE : rw_cells rsegs m3 Ao (ext_cells X' jk)) by (subst X'; unfold ext_cells; cbn [ex_type ex_len ex_val]; exact XC3).
    pose proof FW3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EO3 & _). pose proof EO3 as (_ & _ & _ & _ & _ & _ & XS3). cbn [EW en_exts en_exts_o] in XS3.
    destruct CASES as [[P0 ->]|[PP ->]].
    - (* [comment removed for export] *)
      assert (XN : xs = None) by (destruct xs as [[K es]|]; [exfalso; unfold EXTS in XS3; destruct XS3 as [K0 _]; clear - K0 P0; lia| reflexivity]).
      subst xs. rewrite P0 in FW3. rewrite XBE in FW3.
      pose proof FW3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB3 & _). cbn [blocks_EXTS] in PB3. pose proof (Permutation_nil PB3) as NBN. rewrite NBN in FW3.
      eapply (dx_newsk _ _ _ _ _ _ _ X'); [exact FW3| exact LJ| exact XCE| subst X'; cbn [ex_val_o ex_val ex_len]; exact VO| subst X'; cbn [ex_len]; exact XL| subst X'; cbn [ex_len]; exact CLE].
    - (* [comment removed for export] *)
      destruct xs as [[K es]|]; [| exfalso; unfold EXTS in XS3; clear - XS3 PP; lia].
      rewrite XBE in FW3.
      eapply (dx_push _ _ _ _ _ _ _ _ _ _ _ X'); [exact FW3| exact LJ| exact XCE| subst X'; cbn [ex_val_o ex_val ex_len]; exact VO| subst X'; cbn [ex_len]; exact XL| subst X'; cbn [ex_len]; exact CLE].
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_at_sub : forall m A zs i n,
    bytes_at rsegs m A zs -> 0 <= i -> 0 <= n -> i + n <= Z.of_nat (length zs) ->
    bytes_at rsegs m (A + i) (firstn (Z.to_nat n) (skipn (Z.to_nat i) zs)) /\ Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) zs))) = n.
  Proof.
    clear. intros m A zs i n BS I0 N0 LE.
    rewrite <- (firstn_skipn (Z.to_nat i) zs) in BS. apply bytes_at_app in BS. destruct BS as [_ BS].
    rewrite firstn_length_le in BS by lia. rewrite Z2Nat.id in BS by lia.
    rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) zs)) in BS. apply bytes_at_app in BS. destruct BS as [BS _].
    split; [exact BS|]. rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_trip : forall m mo' s' errv' P xs NB c rem' (cd xl b0 b1 : Z) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    dworldX m mo' s' errv' P xs NB c (cd + xl) rem' [] ->
    0 <= xl < 512 -> 0 <= b0 < 256 -> 0 <= b1 < 256 -> c + 4 + xl <= rem0 - rem' -> base <= cd - 4 ->
    hs_SR H (at_head rem')
      (mkCfg (MS (mkR (Z_to_bv 64 DX_R1) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) (Z_to_bv 64 0) (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 518) a3 a4 a5 a6 a7
                        (Z_to_bv 64 pk) (Z_to_bv 64 cd) (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 1) (Z_to_bv 64 b1) (Z_to_bv 64 b0)
                        (Z_to_bv 64 SSL_R_BAD_ECHCONFIG_EXTENSION) (Z_to_bv 64 206) (Z_to_bv 64 xl) t3 t4 t5 t6)
                  F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros m mo' s' errv' P xs NB c rem' cd xl b0 b1 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 FW XL B0 B1 CLE CDB.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & EO & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & XP0).
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL). rewrite MF0 in MF.
    cbn [app] in HP. assert (HB := HH_blocks_below H HH _ _ _ HP). unfold zlength in *. unfold pk_in in PIN.
    (* [comment removed for export] *)
    pose proof cfree_null_evt_spec as CF. unfold cfree_null_evt_stmt in CF.
    eapply (sr_evt_krel H HH); [exact KREL| eapply CF with (lo := lo); rewrite ?unsigned_lit by lia; [exact ST| exact CEIL| clear - LO8K; lia| exact MI| exact IM| exact G1]|].
    clear CF. cbv beta. intros ms1 (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & _ & _).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in MU1, ST1 by lia.
    destruct (dworldX_stk _ _ _ _ _ _ _ _ _ _ _ _ _ FW MU1 WM1 MI1 ST1 ltac:(apply Forall_cons; [cbn; lia| apply Forall_nil])) as [FW1 _]. clear FW MU1 WM1.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply dx_seg2; try exact (Z_to_bv 64 0); [exact XL| exact MI1]|]. cbv beta. intros ms2 [[X0e ->]|[X1 ->]].
    - (* [comment removed for export] *)
      subst xl. eapply (dx_from_malloc m1 _ _ _ P xs NB c (cd + 0) rem' 0 0 b0 b1 None); [cbn [blocks_of]; exact FW1| reflexivity| lia| exact B0| exact B1| lia| exact CLE].
    - (* [comment removed for export] *)
      pose proof FW1 as (_ & ST1' & FR1 & ERR1 & AUX1 & _ & _ & HP1 & LM1 & _ & _ & _ & PK1 & _ & _ & _ & BS1 & _). cbn [app] in HP1.
      pose proof LM1 as (IM1 & MF1 & _ & _ & _ & _ & _ & _ & G11 & _). rewrite MF0 in MF1.
      destruct (bytes_at_sub m1 base bs (cd - base) xl BS1 ltac:(clear - CDB; lia) ltac:(clear - X1; lia) ltac:(clear - PIN CB1 CLE CR BSL CRB; lia)) as [BSX XBL].
      replace (base + (cd - base)) with cd in BSX by lia.
      set (xb := firstn (Z.to_nat xl) (skipn (Z.to_nat (cd - base)) bs)) in *.
      (* [comment removed for export] *)
      assert (NBB : lb_bytes NB <= 88 + 8 * c /\ 5 * Z.of_nat (length NB) <= 2 * c + 10 /\ lb_big NB <= 1).
      { revert PB XI. unfold XINV. destruct xs as [[K es]|]; intros PB XI.
        - destruct XI as (KC & K4 & KCAP & E5 & EBY & EBG). rewrite blocks_EXTS_some in PB.
          pose proof (blocks_SK_facts P K ltac:(lia)) as (SKB & SKL & _ & SKG & _).
          rewrite <- (lb_bytes_perm _ _ PB), <- (Permutation_length PB), <- (lb_big_perm _ _ PB), lb_bytes_app, length_app, lb_big_app, Nat2Z.inj_add.
          unfold SK_SIZE in SKB. unfold zlength in *. clear - K4 KCAP E5 EBY EBG SKB SKL SKG. lia.
        - destruct XI as [_ C0]. pose proof (Permutation_nil PB) as ->. cbn. clear - C0. lia. }
      destruct NBB as (NBB & NBL & NBG).
      pose proof (cmemdup_spec H HH) as CD. unfold cmemdup_stmt in CD.
      eapply (sr_seq H HH).
      { eapply CD with (lo := lo) (B := B) (LB := mid_errblocks M ++ NB ++ LB) (s := s') (D := cd) (bs := xb) (v := 1); unfold zlength; rewrite ?XBL; rewrite ?unsigned_lit by lia; try reflexivity.
        all: try first [exact HP1| exact KREL| exact AUX1| exact ST1'| exact CEIL| exact MI1| exact TP| exact MF1| exact IM1| exact G11| exact BSX].
        all: lazymatch goal with
             | |- 1 <= _ < _ => clear - X1 XL; lia
             | |- xclient_range _ _ _ _ _ =>
                 split; [right; right; exists (pbin, base, len); split; [do 2 (apply in_or_app; right); exact BIN| cbn; clear - CDB PIN CB1 CLE CR; lia]|];
                 pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP1 ltac:(do 2 (apply in_or_app; right); exact BIN)) as (_ & _ & _ & _ & OFF); cbn [blk_addr blk_size fst snd] in OFF;
                 unfold memflag_foot, A_mem_inited; apply Forall_cons; [cbn; clear - OFF CDB PIN CB1 CLE CR; lia| apply Forall_nil]
             | |- lb_bytes _ + _ <= _ => rewrite !lb_bytes_app in *; unfold DECEXTS_BYTES, ERRDEBUG_BYTES in *;
                                          pose proof (errph_nonneg (mid_err M)) as (EB0 & _); clear - BY EB0 NBB XL CLE CB1 CB2 PIN REM1; lia
             | |- Z.of_nat (length _) + _ <= _ => rewrite !length_app, !Nat2Z.inj_add in *; pose proof (errph_nonneg (mid_err M)) as (_ & EC0 & _); clear - CN EC0 NBL CLE CB2 PIN XL Q5; lia
             | |- lb_big _ + big1 ?n <= _ => rewrite !lb_big_app in *; rewrite (big1_small n) by (unfold BIGB; clear - XL; lia); pose proof (errph_nonneg (mid_err M)) as (_ & _ & EG0); clear - BG EG0 NBG; lia
             | |- _ <= B => clear - SPB SPR; lia
             | |- _ <= _ - CMEMDUP_STACK => unfold CMEMDUP_STACK, CMALLOC_STACK, FR_CRYPTO_memdup, FR_CRYPTO_malloc, RMALLOC_STACK; clear - LO8K; lia
             | |- rw_cells _ _ (errno_addr _) _ => exact ERR1
             | |- ?G => idtac "CDPRE" G
             end. }
      clear CD. intros [ms3 mo3] PO. unfold cmemdup_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m3 & errv3 & Av & pv & s3' &
                      -> & KREL3 & MP3 & MI3 & ST3 & ERR3 & AUX3 & XP3 & VBR & HP3 & VC3 & MF3 & IM3 & GM3).
      unfold zlength in VBR, HP3. rewrite XBL in VBR, HP3. rewrite (unsigned_lit (bv_unsigned sp + -144)) in ST3, XP3 by lia.
      change (mid_errblocks M ++ NB ++ LB) with (mid_errblocks M ++ [] ++ NB ++ LB) in XP3, HP3.
      destruct (dworldX_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FW1 KREL3 MP3 MI3 ST3 ERR3 AUX3 XP3 HP3 MF3) as [FW3 _].
      pose proof VBR as (VP & _ & _ & VH & _).
      (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL3| eapply dx_seg3; try exact (Z_to_bv 64 0); [clear - VP VH HCEILB XL; lia| exact MI3]|]. cbv beta. intros ms4 ->.
      eapply (dx_from_malloc m3 _ _ _ P xs NB c (cd + xl) rem' Av xl b0 b1 (Some (pv, xl))); [cbn [blocks_of]; exact FW3| cbn; clear - VP X1; lia| exact XL| exact B0| exact B1| clear - VP VH HCEILB XL; lia| exact CLE].
  Qed.

  (* [comment removed for export] *)
  Lemma dworld_pk : forall m m1 mo' s' errv' P xs NB c cur rem cur' rem' XB,
    dworldX m mo' s' errv' P xs NB c cur rem XB -> munch [(pk, pk + 24)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
    rw_cells rsegs m1 pk (pk_cells cur' base rem') -> cur + rem = cur' + rem' -> 0 <= rem' <= rem -> base <= cur ->
    dworldX m1 mo' s' errv' P xs NB c cur' rem' XB.
  Proof.
    intros m m1 mo' s' errv' P xs NB c cur rem cur' rem' XB
      (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & EO & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & XP0) MU WM MI1 PK1 CR1 RR BC.
    unfold dworldX. cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (XPL : forall L, (forall b, In b L -> In b (mid_errblocks M ++ XB ++ NB ++ LB)) -> xpres L (pk + 24) [] m m1).
    { intros L SUBL. eapply xpres_of_munch_gen; [exact MU| exact WM|]. intros a Ha [HC _]. cbn. split; [| exact I].
      destruct HC as [HC|[[HC _]|(b' & Hb' & Hr')]]; [clear - HC; lia| clear - HC SPK CEIL LO8K HCEILB; lia|].
      pose proof (HB _ (SUBL _ Hb')) as BH'. clear - BH' Hr' SPK CEIL LO8K. lia. }
    pose proof (HB _ ltac:(do 3 (apply in_or_app; right); exact BIN)) as K2. cbn [blk_addr blk_size fst snd] in K2. unfold pk_in in *.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. cbn. clear - SPK. lia.
    - eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. clear - SPK. lia.
    - subst tp. rewrite errno_RATP in *. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. unfold RERRNO. cbn. clear - SPK CEIL LO8K HCEILB. lia.
    - eapply (HH_rauxv_frame H HH); [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; clear - SPK PKB CEIL LO8K HCEILB; lia| apply Forall_nil].
    - eapply (HH_RHEAP_frame H HH); [exact HP| exact MU| exact WM|]. apply Forall_cons; [left; cbn; clear - SPK CEIL LO8K; lia| apply Forall_nil].
    - eapply LIBMID_xpres0; [exact LM| apply (XPL LB); intros b Hb; do 3 (apply in_or_app; right); exact Hb| exact LIBSUB].
    - eapply ENTRYobj_frameX; [exact EO| apply XPL; intros b Hb; do 2 (apply in_or_app; right); exact Hb| intros b Hb; apply avoids_nil].
    - clear - PIN BC RR CR1. lia.
    - clear - RR. lia.
    - clear - PIN RR CR1. lia.
    - clear - CR CR1. lia.
    - clear - CB2 RR. lia.
    - eapply bytes_at_transport; [exact BS| exact MU|]. cbn. split; [| exact I]. pose proof BSL as BSL'. unfold zlength in BSL'. clear - K2 SPK CEIL LO8K BSL'. lia.
    - eapply xpres_trans; [exact XP0|]. eapply xpres_of_munch; [exact MU| exact WM| | intros b Hb; apply HB; do 3 (apply in_or_app; right); exact Hb].
      apply Forall_cons; [right; cbn; intros a Ha; unfold X0; cbn [rin_ivs fst snd]; left; exact Ha| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Definition dx_exit (k : config) : Prop :=
    exists (rax a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 w3 w7 w8 w9 w10 w11 : word) m mo' s' errv' P xs NB cur rem,
      cfg_model k = mo' /\
      (  (rem = 0 /\ dworld m mo' s' errv' P xs NB cur rem /\
          cfg_ms k = MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pk) w3
                           (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 1) w7 w8 w9 w10 w11 t3 t4 t5 t6)
                      F (Z_to_bv 64 DX_EPI) fc None m (seg_rom rsegs))
      \/ (exists line c, (line = 206 \/ line = 210) /\ dworldX m mo' s' errv' P xs NB c cur rem [] /\
          cfg_ms k = MS (mkR (Z_to_bv 64 DX_RA1) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pk) (Z_to_bv 64 0)
                           (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 1) w7 w8 (Z_to_bv 64 SSL_R_BAD_ECHCONFIG_EXTENSION) (Z_to_bv 64 line) w11 t3 t4 t5 t6)
                      F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom rsegs))).

  (* [comment removed for export] *)
  Lemma dx_head_step : forall (rax a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 w3 w7 w8 w9 w10 w11 : word) m mo' s' errv' P xs NB cur rem,
    dworld m mo' s' errv' P xs NB cur rem ->
    hs_SR H (fun k => dx_exit k \/ at_head (rem - 4) k)
      (mkCfg (MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pk) w3
                        (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 1) w7 w8 w9 w10 w11 t3 t4 t5 t6)
                  F (Z_to_bv 64 DX_HEAD) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros rax a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 w3 w7 w8 w9 w10 w11 m mo' s' errv' P xs NB cur rem FW.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & EO & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & XP0).
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    destruct (dworld_entry _ _ _ _ _ _ _ _ _ _ _ FW) as (pad1 & pad2 & pad3 & pad4 & _ & _ & _ & _ & _ & _ & _ & _ & PKP & PKH & BP & BH & PKA).
    pose proof PIN as PIN'. unfold pk_in in PIN'. assert (PIN2 : pk_in base (zlength bs) cur rem) by (pose proof CRB as CRBq; unfold pk_in; unfold zlength in CRBq |- *; clear - PIN' CR CRBq; lia).
    eapply (sr_evt_krel H HH); [exact KREL| eapply dx_segH; [exact PK| exact BS| exact PIN2| exact PKP| exact PKH| exact PKA| exact MI]|].
    cbv beta. intros ms1 (a0' & a1' & a2' & a3' & s7' & s8' & s11' & m1 & cur' & rem' & MU1 & WM1 & MI1 & PK1 & CR1 & RR & CASES).
    destruct CASES as [(R0 & -> & -> & ->)|[(line & LN & R1 & ->)|(b0 & b1 & xl & XL & CU & RM & B0 & B1 & ->)]].
    - (* [comment removed for export] *)
      apply (sr_done H HH). left. unfold dx_exit. cbn [cfg_ms cfg_model].
      exists rax, a0, a1, a2, a3, a4, a5, a6, a7, t0, t1, t2, t3, t4, t5, t6, w3, w7, w8, w9, w10, w11, m, mo', s', errv', P, xs, NB, cur, rem.
      split; [reflexivity|]. left. split; [exact R0|]. split; [exact FW| reflexivity].
    - (* [comment removed for export] *)
      pose proof (dworld_pk _ _ _ _ _ _ _ _ _ _ _ _ _ _ FW MU1 WM1 MI1 PK1 CR1 RR ltac:(clear - PIN'; lia)) as FW1.
      apply (sr_done H HH). left. unfold dx_exit. cbn [cfg_ms cfg_model].
      exists rax, a0', a1', a2', a3', a4, a5, a6, a7, t0, t1, t2, t3, t4, t5, t6, w3, s7', s8', w9, w10, s11', m1, mo', s', errv', P, xs, NB, cur', rem'.
      split; [reflexivity|]. right. exists line, (rem0 - rem). split; [exact LN|]. split; [exact FW1| reflexivity].
    - (* [comment removed for export] *)
      pose proof (dworld_pk _ _ _ _ _ _ _ _ _ _ _ _ _ _ FW MU1 WM1 MI1 PK1 CR1 RR ltac:(clear - PIN'; lia)) as FW1.
      eapply (sr_mono H HH); [eapply (dx_trip m1 mo' s' errv' P xs NB (rem0 - rem) rem' (cur + 4) xl b0 b1)|].
      + replace (cur + 4 + xl) with cur' by (clear - CU; lia). exact FW1.
      + exact XL. + exact B0. + exact B1.
      + clear - RM XL RR. lia.
      + clear - PIN'. lia.
      + intros k AH. right. unfold at_head in AH |- *.
        destruct AH as (rax2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & v3 & v7 & v8 & v9 & v10 & v11 & m2 & mo2 & st2 & errv2 & P2 & xs2 & NB2 & cur2 & rem2 & FW2 & RB & MO & MS2).
        exists rax2, c0, c1, c2, c3, c4, c5, c6, c7, u0, u1, u2, u3, u4, u5, u6, v3, v7, v8, v9, v10, v11, m2, mo2, st2, errv2, P2, xs2, NB2, cur2, rem2.
        split; [exact FW2|]. split; [clear - RB RM XL; lia|]. split; [exact MO| exact MS2].
  Qed.

  (* [comment removed for export] *)
  Lemma DX_loop : forall (n : nat) (rax a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 w3 w7 w8 w9 w10 w11 : word) m mo' s' errv' P xs NB cur rem,
    dworld m mo' s' errv' P xs NB cur rem -> rem <= Z.of_nat n ->
    hs_SR H dx_exit
      (mkCfg (MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pk) w3
                        (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 1) w7 w8 w9 w10 w11 t3 t4 t5 t6)
                  F (Z_to_bv 64 DX_HEAD) fc None m (seg_rom rsegs)) mo').
  Proof.
    induction n as [|n IH]; intros rax a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 w3 w7 w8 w9 w10 w11 m mo' s' errv' P xs NB cur rem FW RN.
    - eapply (sr_seq H HH); [eapply dx_head_step; exact FW|]. intros k [EX|AH]; [apply (sr_done H HH); exact EX|].
      exfalso. unfold at_head in AH. destruct AH as (rax2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & v3 & v7 & v8 & v9 & v10 & v11 & m2 & mo2 & st2 & errv2 & P2 & xs2 & NB2 & cur2 & rem2 & FW2 & RB & _).
      pose proof FW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PIN2 & _). unfold pk_in in PIN2. clear - PIN2 RB RN. cbn in RN. lia.
    - eapply (sr_seq H HH); [eapply dx_head_step; exact FW|]. intros [ms2 mo2'] [EX|AH]; [apply (sr_done H HH); exact EX|].
      unfold at_head in AH. cbn [cfg_ms cfg_model] in AH.
      destruct AH as (rax2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & v3 & v7 & v8 & v9 & v10 & v11 & m2 & mo2 & st2 & errv2 & P2 & xs2 & NB2 & cur2 & rem2 & FW2 & RB & -> & ->).
      eapply IH; [exact FW2|]. rewrite Nat2Z.inj_succ in RN. clear - RB RN. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_ret1 : forall (rax a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 w3 w7 w8 w9 w10 w11 : word) m mo' s' errv' P xs NB cur rem s_,
    dworld m mo' s' errv' P xs NB cur rem -> rem = 0 ->
    hs_SR H (decexts_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s_ LIB LB M ee pk base len cur0 rem0 E bs lo B m0 mo)
      (mkCfg (MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pk) w3
                        (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 1) w7 w8 w9 w10 w11 t3 t4 t5 t6)
                  F (Z_to_bv 64 DX_EPI) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros rax a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 w3 w7 w8 w9 w10 w11 m mo' s' errv' P xs NB cur rem s_ FW R0.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & EO & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & XP0).
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR. cbn [app] in HP.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL).
    (* [comment removed for export] *)
    destruct xs as [[K es]|]; [| exfalso; unfold XINV in XI; destruct XI as [_ C0]; clear - C0 R0 REM1; lia].
    unfold XINV in XI. destruct XI as (KC & K4 & KCAP & E5 & EBY & EBG). rewrite blocks_EXTS_some in PB.
    pose proof (blocks_SK_facts P K ltac:(lia)) as (SKB & SKL & _ & SKG & SK0).
    assert (LEN16 : length (es_slots (mid_E M)) = 16%nat).
    { destruct (mid_err M) as [|c0]; cbn [ERRX] in EX; [rewrite EX; reflexivity| exact (proj1 EX)]. }
    pose proof (errst_fits_bounds _ LEN16 FIT) as (EC & EB & EG).
    eapply (sr_evt_krel H HH); [exact KREL| eapply dx_segE with (lo := lo); [exact FR| exact ST| exact CEIL| clear - LO8K; lia| exact MI]|].
    cbv beta. intros ms3 [-> ST3].
    apply (sr_done H HH). unfold decexts_post. cbn [cfg_ms cfg_model].
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m, errv', s', 1, M, (Some (K, es)), P, NB, [], cur, rem.
    cbn [app]. unfold zlength in *. unfold pk_in in PIN.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    all: lazymatch goal with
         | |- _ = _ => reflexivity
         | |- mid_step _ _ => unfold mid_step; split; [exact MF0|]; split; [auto|]; split; auto
         | |- mid_newlib_ok _ _ _ => unfold mid_newlib_ok; exists [], []; split; [apply Permutation_refl|]; rewrite CX; split; [reflexivity|]; destruct (mid_err M); reflexivity
         | |- Permutation _ _ => rewrite blocks_EXTS_some; exact PB
         | |- _ \/ _ => left; split; [reflexivity|]; split; [discriminate| exact R0]
         | |- 5 * _ <= _ => rewrite <- (Permutation_length PB), length_app, Nat2Z.inj_add; clear - SKL E5 R0; lia
         | |- lb_bytes _ <= _ => rewrite <- (lb_bytes_perm _ _ PB), lb_bytes_app; unfold SK_SIZE in *; clear - SKB EBY KCAP K4 CB2 R0 REM1; lia
         | |- lb_big _ <= _ =>
             rewrite <- (lb_big_perm _ _ PB), lb_big_app, EBG; unfold blocks_SK; destruct (Z.eqb_spec (sk_cap K) 0) as [C0|CN0];
             rewrite ?lb_big_cons; cbn [blk_size snd lb_big fold_right]; rewrite (big1_small SK_SIZE) by (unfold SK_SIZE, BIGB; lia);
             [pose proof (Z.div_pos rem0 600 ltac:(lia) ltac:(lia)); lia|];
             unfold big1; destruct (Z.ltb_spec BIGB (8 * sk_cap K)) as [BG1|BG0];
             [apply Z.div_le_lower_bound; [lia|]; unfold BIGB in BG1; clear - BG1 KCAP K4 CB2 R0; lia| pose proof (Z.div_pos rem0 600 ltac:(lia) ltac:(lia)); lia]
         | |- ?G => idtac "RET1" G
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_fail_end : forall m mo' s' errv' P xs cur rem Lf LE c E' pad1 pad2 pad3 pad4 s_
                             (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w4 w5 w6 w7 w8 w9 w11 : word),
    let M' := mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M) in
    mem_inv rsegs m -> stk rsegs m lo spq -> rw_cells rsegs m spq (dx_frame j0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
    rw_cells rsegs m (errno_addr tp) [C4 errv'] -> hs_rauxv_ok H m B -> hs_KREL H s' mo' -> hs_MPRES H mo mo' ->
    hs_RHEAP H s' Lf m -> Permutation Lf (blocks_ERRST E' ++ LE ++ LB) ->
    LIBMID (LE ++ LIB) m M' -> errph_delta (mid_err M) LE c ->
    length pad1 = 6%nat -> length pad2 = 4%nat -> length pad3 = 6%nat -> length pad4 = 4%nat ->
    rw_cells rsegs m ee (entry_cells (EW P xs) pad1 pad2 pad3 pad4) ->
    rw_cells rsegs m pk (pk_cells cur base rem) -> pk_in base len cur rem -> cur0 + rem0 = cur + rem -> rem <= rem0 ->
    bytes_at rsegs m base bs -> xpres LB (bv_unsigned sp) X0 m0 m ->
    hs_SR H (decexts_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s_ LIB LB M ee pk base len cur0 rem0 E bs lo B m0 mo)
      (mkCfg (MS (mkR (Z_to_bv 64 DX_R10) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) a0 a1 a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 pk) (Z_to_bv 64 0) w4 w5 w6 w7 w8 w9 (Z_to_bv 64 0) w11 t3 t4 t5 t6)
                  F (ret_pc (Z_to_bv 64 DX_R10)) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros m mo' s' errv' P xs cur rem Lf LE c E' pad1 pad2 pad3 pad4 s_ t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w4 w5 w6 w7 w8 w9 w11 M'
           MI ST FR ERR AUX KREL MP HP PL LM DL L1 L2 L3 L4 EC PK PIN CR RR BS XP0. subst M'.
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR. unfold pk_in in PIN.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL). cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ERRPH_mid] in MF, CP, EPm, EX, VD, FIT.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (INF : forall b, In b (blocks_ERRST E' ++ LE ++ LB) -> In b Lf) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL| exact Hb]).
    assert (EIN : In (en_id E, ee, ENTRY_SIZE) Lf) by (apply INF; do 2 (apply in_or_app; right); exact EIN0).
    pose proof (HB _ EIN) as EH. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP EIN) as (EP0 & _ & _ & _ & EOFF). cbn [blk_addr blk_size fst snd] in EH, EP0, EOFF. unfold ENTRY_SIZE in EH, EOFF.
    assert (DJE : forall b, In b Lf -> blk_id b <> en_id E -> blk_addr b + blk_size b <= ee \/ ee + 104 <= blk_addr b).
    { intros b Hb NE. pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP Hb EIN NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ. unfold ENTRY_SIZE in DJ. exact DJ. }
    pose proof (Permutation_NoDup (Permutation_map blk_id PL) (HH_RHEAP_blocks_nodup H HH _ _ _ HP)) as NDf.
    assert (NELE : forall b, In b (blocks_ERRST E' ++ LE) -> blk_id b <> en_id E).
    { intros b Hb K0. rewrite app_assoc in NDf. exact (nodup_ids_app_ne _ _ _ _ NDf Hb EIN0 K0). }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply dx_segF4 with (ee := ee) (E := EW P xs); [exact EC| exact EP0| unfold ENTRY_SIZE; clear - EH HCEILB; lia| exact MI]|].
    cbv beta. intros ms1 (m1 & MU1 & WM1 & MI1 & EC1 & ->). unfold ENTRY_SIZE in MU1.
    cbn [EW en_version en_pname en_pname_o en_publen en_pub en_pub_o en_nsuites en_suites en_suites_o en_maxname en_cfgid en_exts_o en_loadtime en_forretry en_enclen en_encoded en_encoded_o en_id] in EC1.
    assert (ST1 : stk rsegs m1 lo (bv_unsigned sp + -144)) by (eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| cbn; clear - EH CEIL; lia]).
    assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp + -144) (dx_frame j0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR| exact MU1| exact WM1| cbn; clear - EH CEIL LO8K; lia]).
    assert (ERR1 : rw_cells rsegs m1 (errno_addr tp) [C4 errv']) by (rewrite TP in *; rewrite errno_RATP in *; eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| unfold RERRNO; cbn; clear - EOFF; lia]).
    assert (AUX1 : hs_rauxv_ok H m1 B) by (eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL; apply Forall_cons; [cbn; clear - EH EOFF CEIL LO8K SPB; lia| apply Forall_nil]).
    assert (HP1 : hs_RHEAP H s' Lf m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [| apply Forall_nil]. right; right. exists (en_id E, ee, ENTRY_SIZE). split; [exact EIN| cbn; unfold ENTRY_SIZE; lia]. }
    assert (LM1 : LIBMID (LE ++ LIB) m1 (mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M))).
    { eapply (LIBMID_xpres0 _ (LE ++ LIB) (bv_unsigned sp + -144)); [exact LM| | auto].
      eapply xpres_of_munch_gen; [exact MU1| exact WM1|]. intros a Ha [HC _]. cbn. split; [| exact I].
      destruct HC as [HC|[[HC _]|(b' & Hb' & Hr')]]; [clear - HC EH CEIL LO8K; lia| clear - HC EOFF; lia|].
      apply in_app_or in Hb'. destruct Hb' as [Hb'|Hb'].
      - pose proof (DJE b' (INF _ ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb')) (NELE _ ltac:(apply in_or_app; right; exact Hb'))) as DJ. clear - DJ Hr'. lia.
      - pose proof (DJE b' (INF _ ltac:(do 2 (apply in_or_app; right); apply LIBSUB; exact Hb')) (IDS _ _ Hb' ltac:(left; reflexivity))) as DJ. clear - DJ Hr'. lia. }
    assert (PK1 : rw_cells rsegs m1 pk (pk_cells cur base rem)) by (eapply rw_cells_transport; [exact PK| exact MU1| exact WM1| cbn; clear - EH CEIL LO8K SPK; lia]).
    assert (BS1 : bytes_at rsegs m1 base bs).
    { eapply bytes_at_transport; [exact BS| exact MU1|]. cbn. split; [| exact I]. pose proof BSL as BSL'. unfold zlength in BSL'.
      pose proof (DJE (pbin, base, len) (INF _ ltac:(do 2 (apply in_or_app; right); exact BIN)) ltac:(cbn; intros K0; apply EBIN; symmetry; exact K0)) as KKq. cbn [blk_addr blk_size fst snd] in KKq. clear - KKq BSL'. lia. }
    assert (XP01 : xpres LB (bv_unsigned sp) X0 m0 m1).
    { eapply xpres_trans; [exact XP0|]. eapply xpres_of_munch; [exact MU1| exact WM1| | intros b Hb; apply HB; apply INF; do 2 (apply in_or_app; right); exact Hb].
      apply Forall_cons; [right; cbn; intros a Ha; unfold X0, ENTRY_SIZE; cbn [rin_ivs fst snd]; right; left; exact Ha| apply Forall_nil]. }
    pose proof (IMPL_across _ _ _ MU1 WM1 ltac:(unfold A_malloc_impl; cbn; clear - EOFF; lia) IM) as IM1.
    pose proof (GOT_across _ _ _ MU1 WM1 ltac:(unfold A_got_CRYPTO_malloc; cbn; clear - EOFF; lia) G1) as GM1.
    clear MU1 WM1 HP LM FR ERR AUX PK BS XP0 EC MI ST.
    (* [comment removed for export] *)
    pose proof extfree_null_spec as XF. unfold extfree_null_stmt, nullret_stmt_at in XF.
    eapply (sr_evt_krel H HH); [exact KREL| eapply XF with (lo := lo); rewrite ?unsigned_lit by lia; [exact ST1| clear - LO8K; lia| exact MI1| unfold DX_R11; rewrite unsigned_lit by lia; reflexivity]|].
    clear XF. cbv beta. intros ms2 (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in MU2, ST2 by lia.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply dx_segF5; exact MI2|]. cbv beta. intros ms3 ->.
    pose proof cfree_null_evt_spec as CF. unfold cfree_null_evt_stmt in CF.
    eapply (sr_evt_krel H HH); [exact KREL| eapply CF with (lo := lo); rewrite ?unsigned_lit by lia; [exact ST2| exact CEIL| clear - LO8K; lia| exact MI2| |]|].
    { eapply IMPL_across; [exact MU2| exact WM2| unfold A_malloc_impl; cbn; clear - CEIL HCEILB; lia| exact IM1]. }
    { eapply GOT_across; [exact MU2| exact WM2| unfold A_got_CRYPTO_malloc; cbn; clear - CEIL HCEILB; lia| exact GM1]. }
    clear CF. cbv beta. intros ms4 (y0' & y1' & y2' & h1' & h2' & h3' & h4' & h5' & h6' & h7' & y3' & y4' & y5' & y6' & m4 & -> & MU4 & WM4 & MI4 & ST4 & _ & _).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in MU4, ST4 by lia.
    assert (MU24 : munch [(lo, bv_unsigned sp + -144)] m1 m4).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU4]]; intros q Hq; cbn in Hq |- *; lia. }
    pose proof (wmono_trans rsegs _ _ _ WM2 WM4) as WM24. clear MU2 WM2 MU4 WM4.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply dx_segF6; exact MI4|]. cbv beta. intros ms5 ->.
    assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -144) (dx_frame j0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR1| exact MU24| exact WM24| cbn; lia]).
    eapply (sr_evt_krel H HH); [exact KREL| eapply dx_segE with (lo := lo); [exact FR4| exact ST4| exact CEIL| clear - LO8K; lia| exact MI4]|].
    cbv beta. intros ms6 [-> ST6].
    (* [comment removed for export] *)
    assert (HB1 := HH_blocks_below H HH _ _ _ HP1).
    assert (LEN16 : length (es_slots E') = 16%nat) by exact (proj1 EX).
    pose proof (errst_fits_bounds _ LEN16 FIT) as (ECb & EBb & EGb).
    apply (sr_done H HH). unfold decexts_post. cbn [cfg_ms cfg_model].
    exists y0', y1', y2', h1', h2', h3', h4', h5', h6', h7', y3', y4', y5', y6', m4, errv', s', 0, (mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M)), None, 0, [], LE, cur, rem.
    cbn [app mid_errblocks mid_E mid_ctx mid_vdso]. unfold zlength in *.
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
         | |- MS _ _ _ _ _ _ _ = _ => reflexivity
         | |- hs_KREL _ _ _ => exact KREL
         | |- hs_MPRES _ _ _ => exact MP
         | |- mem_inv _ _ => exact MI4
         | |- stk _ _ _ _ => exact ST6
         | |- rw_cells _ _ (errno_addr _) _ => rewrite TP in *; rewrite errno_RATP in *; eapply rw_cells_transport; [exact ERR1| exact MU24| exact WM24| unfold RERRNO; cbn; clear - CEIL HCEILB; lia]
         | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX1| exact MU24| exact WM24|]; unfold RAUXV_CELL; apply Forall_cons; [cbn; clear - CEIL HCEILB LO8K SPB; lia| apply Forall_nil]
         | |- hs_RHEAP _ _ _ _ => eapply PERM; [| exact PL]; eapply (HH_RHEAP_frame H HH); [exact HP1| exact MU24| exact WM24|]; apply Forall_cons; [left; cbn; lia| apply Forall_nil]
         | |- LIBMID _ _ _ => eapply (LIBMID_xpres0 _ Lf (bv_unsigned sp + -144)); [exact LM1| | intros b Hb; apply INF; apply in_or_app; right; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply LIBSUB; exact Hb]];
                              eapply xpres_of_munch; [exact MU24| exact WM24| apply Forall_cons; [left; cbn; lia| apply Forall_nil]| exact HB1]
         | |- mid_step _ _ => unfold mid_step; cbn [mid_flag mid_ctx mid_err mid_vdso]; split; [reflexivity|]; split; [intros b Hb; rewrite CX in Hb; exact Hb|]; split; [| auto];
                             intros c0 Hc0; rewrite Hc0 in DL; cbn [errph_delta] in DL; destruct DL as [-> _]; reflexivity
         | |- mid_newlib_ok _ _ _ => unfold mid_newlib_ok; cbn [mid_ctx mid_err]; exists [], LE; split; [apply Permutation_refl|]; rewrite CX; split; [reflexivity|];
                                  destruct (mid_err M) as [|c0]; [exact DL|]; cbn [errph_delta] in DL; destruct DL as [_ ->]; reflexivity
         | |- CtxReady _ = mid_ctx _ => symmetry; exact CX
         | |- mid_vdso _ = mid_vdso _ => reflexivity
         | |- Z.of_nat (length (mid_errblocks _)) <= _ => exact ECb
         | |- lb_bytes (mid_errblocks _) <= _ => exact EBb
         | |- lb_big (mid_errblocks _) = 0 => exact EGb
         | |- ENTRYobj _ _ _ _ =>
             pose proof OF0 as (Q1 & Q2 & Q3 & Q4); unfold ENTRYobj; cbn [en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o];
             split; [exists pad1, pad2, pad3, pad4; split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|];
                     eapply rw_cells_transport; [exact EC1| exact MU24| exact WM24| cbn; clear - EH CEIL LO8K; lia]|];
             split; [apply in_or_app; right; exact EIN0|];
             split; [eapply ofield_LB_mono; [exact Q1| intros b Hb; apply in_or_app; right; exact Hb]|];
             split; [eapply ofield_LB_mono; [exact Q2| intros b Hb; apply in_or_app; right; exact Hb]|];
             split; [eapply ofield_LB_mono; [exact Q3| intros b Hb; apply in_or_app; right; exact Hb]|];
             split; [eapply ofield_LB_mono; [exact Q4| intros b Hb; apply in_or_app; right; exact Hb]|]; reflexivity
         | |- Permutation _ _ => apply Permutation_refl
         | |- _ \/ _ => right; repeat split; reflexivity
         | |- 5 * _ <= _ => cbn [length]; rewrite Nat2Z.inj_0; clear - RR; lia
         | |- pk_in _ _ _ _ => unfold pk_in; clear - PIN; lia
         | |- lb_bytes [] <= _ => cbn [lb_bytes fold_right]; unfold SK_SIZE; clear - REM1; lia
         | |- lb_big [] <= _ => cbn [lb_big fold_right]; apply Z.div_pos; clear - REM1; lia
         | |- rw_cells _ _ pk _ => eapply rw_cells_transport; [exact PK1| exact MU24| exact WM24| cbn; clear - SPK; lia]
         | |- bytes_at _ _ base _ => eapply bytes_at_transport; [exact BS1| exact MU24|]; cbn; split; [| exact I]; pose proof (HB1 _ (INF _ ltac:(do 2 (apply in_or_app; right); exact BIN))) as K2; cbn [blk_addr blk_size fst snd] in K2; pose proof BSL as BSL'; unfold zlength in BSL'; clear - K2 CEIL BSL'; lia
         | |- base <= _ => clear - PIN; lia
         | |- 0 <= _ => clear - PIN; lia
         | |- _ + _ <= base + len => clear - PIN; lia
         | |- cur0 + rem0 = _ => exact CR
         | |- xpres LB _ _ m0 _ => eapply xpres_trans; [exact XP01|]; eapply xpres_of_munch; [exact MU24| exact WM24| apply Forall_cons; [left; cbn; clear - SPR CEIL; lia| apply Forall_nil]| intros b Hb; apply HB1; apply INF; do 2 (apply in_or_app; right); exact Hb]
         | |- ?G => idtac "FEND" G
         end.
  Qed.

  Lemma xclient_mono : forall L L' (SP : Z) X a, (forall b, In b L -> In b L') -> xclient L SP X a -> xclient L' SP X a.
  Proof.
    clear. intros L L' SP X a SUB [HC HX]. split; [| exact HX].
    destruct HC as [HC|[HC|(b & Hb & Hr)]]; [left; exact HC| right; left; exact HC| right; right; exists b; split; [apply SUB; exact Hb| exact Hr]].
  Qed.

  (* [comment removed for export] *)
  Lemma dx_fail_tail : forall m mo' s' errv' P xs NB cur rem Lr LE c E' line s_
                              (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w7 w8 w11 : word),
    let M' := mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M) in
    mem_inv rsegs m -> stk rsegs m lo spq -> rw_cells rsegs m spq (dx_frame j0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
    rw_cells rsegs m (errno_addr tp) [C4 errv'] -> hs_rauxv_ok H m B -> hs_KREL H s' mo' -> hs_MPRES H mo mo' ->
    hs_RHEAP H s' Lr m -> Permutation Lr (blocks_ERRST E' ++ LE ++ NB ++ LB) ->
    LIBMID (LE ++ LIB) m M' -> errph_delta (mid_err M) LE c ->
    ENTRYobj (NB ++ LB) m ee (EW P xs) -> Permutation (blocks_EXTS P xs) NB ->
    rw_cells rsegs m pk (pk_cells cur base rem) -> pk_in base len cur rem -> cur0 + rem0 = cur + rem -> rem <= rem0 ->
    bytes_at rsegs m base bs -> xpres LB (bv_unsigned sp) X0 m0 m ->
    hs_SR H (decexts_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s_ LIB LB M ee pk base len cur0 rem0 E bs lo B m0 mo)
      (mkCfg (MS (mkR (Z_to_bv 64 DX_RA3) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) a0 a1 a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 pk) (Z_to_bv 64 0) (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 1) w7 w8
                        (Z_to_bv 64 SSL_R_BAD_ECHCONFIG_EXTENSION) (Z_to_bv 64 line) w11 t3 t4 t5 t6)
                  F (ret_pc (Z_to_bv 64 DX_RA3)) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros m mo' s' errv' P xs NB cur rem Lr LE c E' line s_ t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w7 w8 w11 M'
           MI ST FR ERR AUX KREL MP HP PL LM DL EO PB PK PIN CR RR BS XP0. subst M'.
    cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL). cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ERRPH_mid] in MF, CP, EPm, EX, VD, FIT.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (INF : forall b, In b (blocks_ERRST E' ++ LE ++ NB ++ LB) -> In b Lr) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL| exact Hb]).
    assert (SUBLR : forall b, In b LB -> In b Lr) by (intros b Hb; apply INF; do 3 (apply in_or_app; right); exact Hb).
    assert (SUBNR : forall b, In b (NB ++ LB) -> In b Lr) by (intros b Hb; apply INF; do 2 (apply in_or_app; right); exact Hb).
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC) & EIN & O1 & O2 & O3 & O4 & XS).
    cbn [EW en_id en_exts en_exts_o en_pname en_pname_o en_pub en_pub_o en_suites en_suites_o en_encoded en_encoded_o] in EIN, XS, EC.
    pose proof (HB _ (SUBLR _ EIN0)) as EH. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBLR _ EIN0)) as (EP0 & _ & _ & _ & EOFF). cbn [blk_addr blk_size fst snd] in EH, EP0, EOFF. unfold ENTRY_SIZE in EH, EOFF.
    assert (PR : 0 <= P < 2^64).
    { revert XS. unfold EXTS. destruct xs as [[K es]|]; intros XS; [| rewrite XS; lia].
      destruct XS as (XP1 & SO & _). destruct SO as (_ & _ & KIN & _). pose proof (HB _ (SUBNR _ KIN)) as K5. cbn [blk_addr blk_size fst snd] in K5. unfold SK_SIZE in K5. lia. }
    unfold GOT_echfree in G2.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply dx_segF2 with (ee := ee) (E := EW P xs); [exact EC| exact EP0| unfold ENTRY_SIZE; clear - EH HCEILB; lia| cbn [EW en_exts]; exact PR| exact MI]|].
    cbv beta. intros ms1 ->. cbn [EW en_exts].
    revert XS PB. unfold EXTS. destruct xs as [[K es]|]; intros XS PB.
    2: { (* [comment removed for export] *)
      rewrite XS. cbn [blocks_EXTS] in PB. pose proof (Permutation_nil PB) as NBN. subst NB. cbn [app] in PL, INF.
      pose proof skset_thunks_null_spec as SN. unfold skset_thunks_null_stmt, sknull_stmt_at in SN.
      eapply (sr_evt_krel H HH); [exact KREL| eapply SN with (lo := lo); rewrite ?unsigned_lit by lia; [exact ST| clear - LO8K; lia| exact MI]|].
      clear SN. cbv beta. intros ms2 (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
      rewrite (unsigned_lit (bv_unsigned sp + -144)) in MU2, ST2 by lia.
      (* [comment removed for export] *)
      eapply (sr_evt_krel H HH); [exact KREL| eapply dx_segF3; [unfold GOT_echfree; eapply rw_cells_transport; [exact G2| exact MU2| exact WM2| unfold A_got_ossl_echext_free; cbn; clear - CEIL HCEILB; lia]| lia| exact MI2]|].
      cbv beta. intros ms3 ->.
      pose proof sk_pop_free_null_spec as SN. unfold sk_pop_free_null_stmt, sknull_stmt_at in SN.
      eapply (sr_evt_krel H HH); [exact KREL| eapply SN with (lo := lo); rewrite ?unsigned_lit by lia; [exact ST2| clear - LO8K; lia| exact MI2]|].
      clear SN. cbv beta. intros ms4 (y0' & y1' & y2' & h1' & h2' & h3' & h4' & h5' & h6' & h7' & y3' & y4' & y5' & y6' & m4 & -> & MU4 & WM4 & MI4 & ST4).
      rewrite (unsigned_lit (bv_unsigned sp + -144)) in MU4, ST4 by lia.
      assert (MU24 : munch [(lo, bv_unsigned sp + -144)] m m4).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU4]]; intros q Hq; cbn in Hq |- *; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM2 WM4) as WM24. clear MU2 WM2 MU4 WM4.
      assert (XPs : forall L, (forall b, In b L -> In b Lr) -> xpres L (bv_unsigned sp + -144) [] m m4).
      { intros L SUBL. eapply xpres_of_munch; [exact MU24| exact WM24| apply Forall_cons; [left; cbn; lia| apply Forall_nil]| intros b Hb; apply HB; apply SUBL; exact Hb]. }
      eapply (dx_fail_end m4 mo' s' errv' P None cur rem Lr LE c E' pad1 pad2 pad3 pad4); try eassumption.
      all: cbv delta [spq]; lazymatch goal with
           | |- stk _ _ _ _ => exact ST4
           | |- rw_cells _ _ (bv_unsigned sp + -144) _ => eapply rw_cells_transport; [exact FR| exact MU24| exact WM24| cbn; lia]
           | |- rw_cells _ _ (errno_addr _) _ => rewrite TP in *; rewrite errno_RATP in *; eapply rw_cells_transport; [exact ERR| exact MU24| exact WM24| unfold RERRNO; cbn; clear - CEIL HCEILB; lia]
           | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX| exact MU24| exact WM24|]; unfold RAUXV_CELL; apply Forall_cons; [cbn; clear - CEIL HCEILB LO8K SPB; lia| apply Forall_nil]
           | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU24| exact WM24|]; apply Forall_cons; [left; cbn; lia| apply Forall_nil]
           | |- LIBMID _ _ _ => eapply (LIBMID_xpres0 _ Lr (bv_unsigned sp + -144)); [exact LM| apply XPs; auto|]; intros b Hb; apply INF; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; right; apply in_or_app; left; exact Hb| do 2 (apply in_or_app; right); apply LIBSUB; exact Hb]
           | |- rw_cells _ _ ee _ => eapply rw_cells_transport; [exact EC| exact MU24| exact WM24| cbn; clear - EH CEIL; lia]
           | |- rw_cells _ _ pk _ => eapply rw_cells_transport; [exact PK| exact MU24| exact WM24| cbn; clear - SPK; lia]
           | |- bytes_at _ _ base _ => eapply (xpres_bytes_at _ _ _ _ _ _ _ (XPs LB SUBLR)); [exact BS|]; split; [| apply Forall_nil]; right; right; exists (pbin, base, len); split; [exact BIN| cbn; pose proof BSL as BSLq; unfold zlength in BSLq |- *; lia]
           | |- xpres LB _ X0 m0 _ => eapply xpres_trans; [exact XP0|]; eapply xpres_weaken; [apply (XPs LB SUBLR)| clear - SPR; lia| auto| intros q Hq; destruct Hq]
           | |- ?G => idtac "FTN" G
           end. }
    (* [comment removed for export] *)
    destruct XS as (PP & SO & LEN & F2). rewrite blocks_EXTS_some in PB. set (EB := EBof K es) in *.
    pose proof SO as (_ & _ & KIN & KNC & KCAP2 & _ & _ & KDAT). unfold sk_num in KNC.
    (* [comment removed for export] *)
    set (REST := blocks_ERRST E' ++ LE ++ LB) in *.
    assert (PL2 : Permutation Lr ((blocks_SK P K ++ EB) ++ REST)).
    { etransitivity; [exact PL|]. transitivity (NB ++ REST); [| apply Permutation_app_tail; apply Permutation_sym; exact PB].
      subst REST. rewrite (app_assoc (blocks_ERRST E') LE (NB ++ LB)), (app_assoc (blocks_ERRST E') LE LB). apply Permutation_app_swap_app. }
    assert (HP2 : hs_RHEAP H s' ([] ++ blocks_SK P K ++ (EB ++ REST)) m) by (eapply PERM; [exact HP|]; cbn [app]; rewrite app_assoc; exact PL2).
    pose proof (Permutation_NoDup (Permutation_map blk_id PL2) (HH_RHEAP_blocks_nodup H HH _ _ _ HP)) as ND2.
    assert (SH : P + SK_SIZE <= hceil) by (pose proof (HB _ (SUBNR _ KIN)) as K5; cbn [blk_addr blk_size fst snd] in K5; exact K5).
    assert (SKB : SK_below P K lo).
    { split; [clear - SH CEIL; lia|]. destruct KDAT as [[C0 _]|(_ & _ & _ & DIN & _)]; [left; exact C0| right].
      pose proof (HB _ (SUBNR _ DIN)) as K6. cbn [blk_addr blk_size fst snd] in K6. clear - K6 CEIL. lia. }
    (* [comment removed for export] *)
    pose proof skset_thunks_spec as SC. unfold skset_thunks_stmt, skset_stmt_at in SC.
    eapply (sr_evt_krel H HH); [exact KREL| eapply SC with (lo := lo) (a := P) (K := K); rewrite ?unsigned_lit by lia; try reflexivity;
                                [unfold DX_THUNK_FREE; lia| exact SO| exact SKB| exact ST| clear - LO8K; lia| exact MI]|].
    clear SC. cbv beta. intros ms2 (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & SO2).
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in MU2, ST2 by lia. unfold SK_SIZE in MU2.
    set (K3 := sk_with_thunk K O_SK_FREETH DX_THUNK_FREE) in *.
    (* [comment removed for export] *)
    assert (SUB2 : forall b, In b (EB ++ REST) -> In b Lr) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL2| rewrite <- app_assoc; apply in_or_app; right; exact Hb]).
    assert (SUBLR2 : forall b, In b LB -> In b (EB ++ REST)) by (intros b Hb; subst REST; apply in_or_app; right; do 2 (apply in_or_app; right); exact Hb).
    assert (XPs : forall L, (forall b, In b L -> In b (EB ++ REST)) -> xpres L (bv_unsigned sp + -144) [] m m2).
    { intros L SUBL. eapply xpres_of_munch_gen; [exact MU2| exact WM2|]. intros a Ha XC. pose proof (xclient_mono _ _ _ _ _ SUBL XC) as XC2. cbn. split; [| split; [| exact I]].
      - destruct XC2 as [HC _]. destruct HC as [HC|[[HC _]|(b' & Hb' & Hr')]]; [clear - HC; lia| clear - HC CEIL HCEILB; lia|].
        pose proof (HB _ (SUB2 _ Hb')) as BH'. clear - BH' Hr' CEIL. lia.
      - intros R. eapply (nb_not_client s' [] (blocks_SK P K) (EB ++ REST) (bv_unsigned sp + -144) []); [exact HP2| clear - LO8K; lia| left; reflexivity| cbn [blk_addr blk_size fst snd]; unfold SK_SIZE; exact R| exact XC2]. }
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBNR _ KIN)) as (_ & _ & _ & _ & POFF). cbn [blk_addr blk_size fst snd] in POFF. unfold SK_SIZE in POFF, SH.
    assert (DJI : forall q n, 0x10000 <= q -> q + n <= 0x311000 -> disjoint_from [(lo, bv_unsigned sp + -144); (P, P + 56)] q n).
    { intros q n Q1 Q2. cbn. split; [clear - Q1 Q2 CEIL HCEILB; lia| split; [clear - Q1 Q2 POFF; lia| exact I]]. }
    assert (GE2 : GOT_echfree m2) by (unfold GOT_echfree; eapply rw_cells_transport; [exact G2| exact MU2| exact WM2| apply DJI; unfold A_got_ossl_echext_free; cbn; lia]).
    assert (HP2' : hs_RHEAP H s' ((blocks_SK P K ++ EB) ++ REST) m2).
    { eapply PERM; [eapply (HH_RHEAP_frame H HH); [exact HP2| exact MU2| exact WM2|]| cbn [app]; rewrite app_assoc; apply Permutation_refl].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right. exists (sk_id K, P, SK_SIZE). split; [cbn [app]; apply in_or_app; left; left; reflexivity| cbn; unfold SK_SIZE; lia]. }
    assert (F22 : Forall2 (fun p X => EXTobj ((blocks_SK P K ++ EB) ++ REST) m2 p X) (sk_elems K) es).
    { eapply (EXTs_frame (NB ++ LB) (EB ++ REST) _ (bv_unsigned sp + -144) m m2); [exact F2| intros b Hb; apply in_or_app; left; exact Hb| intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb| apply XPs; auto|].
      intros b Hb. pose proof (HB _ (SUB2 _ ltac:(apply in_or_app; left; exact Hb))) as BH. clear - BH CEIL LO8K. lia. }
    assert (NDK : List.NoDup (map blk_id (blocks_SK P K ++ EB))) by (pose proof ND2 as NDa; rewrite map_app in NDa; apply NoDup_app_remove_r in NDa; exact NDa).
    pose proof (IMPL_across _ _ _ MU2 WM2 ltac:(apply DJI; unfold A_malloc_impl; cbn; lia) IM) as IM2.
    pose proof (GOT_across _ _ _ MU2 WM2 ltac:(apply DJI; unfold A_got_CRYPTO_malloc; cbn; lia) G1) as GM2.
    assert (ERR2 : rw_cells rsegs m2 (errno_addr tp) [C4 errv']) by (rewrite TP in *; rewrite errno_RATP in *; eapply rw_cells_transport; [exact ERR| exact MU2| exact WM2| apply DJI; unfold RERRNO; cbn; lia]).
    assert (AUX2 : hs_rauxv_ok H m2 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU2| exact WM2|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; clear - CEIL HCEILB LO8K SPB; lia|]. apply Forall_cons; [cbn; clear - SH POFF CEIL LO8K SPB; lia| apply Forall_nil]. }
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -144) (dx_frame j0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply rw_cells_transport; [exact FR| exact MU2| exact WM2|]. cbn. split; [lia| split; [clear - SH CEIL LO8K; lia| exact I]]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply dx_segF3; [exact GE2| lia| exact MI2]|]. cbv beta. intros ms3 ->.
    pose proof (popfree_exts_spec H HH) as PF. unfold popfree_exts_stmt, skpopfree_stmt_gen in PF.
    specialize (PF (extfree_spec H HH) EXTobj_frame_law EXTobj_owned_law GOT_echfree_frame ltac:(unfold P_ossl_echext_free; lia) ltac:(reflexivity)).
    eapply (sr_seq H HH).
    { eapply PF with (a := P) (K := K3) (xs := es) (lo := lo) (B := B) (LB := (blocks_SK P K ++ EB) ++ REST) (s := s') (errv := errv');
        subst K3; rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk, ?e_sk_free_thunk_set, ?unsigned_lit by lia; try reflexivity.
      all: try first [exact LEN| exact F22| exact NDK| exact HP2'| exact KREL| exact AUX2| exact ST2| exact CEIL| exact ERR2| exact MI2| exact IM2| exact GM2| exact GE2| exact TP].
      all: lazymatch goal with
           | |- SKobj _ _ _ _ => eapply SKobj_LB_mono; [exact SO2| intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [eapply Permutation_in; [exact PL2| apply SUBNR; apply in_or_app; left; exact Hb]| apply in_or_app; right; subst REST; do 2 (apply in_or_app; right); exact Hb]]
           | |- is_sk_freefunc_thunk _ => unfold is_sk_freefunc_thunk; left; reflexivity
           | |- _ <= B => clear - SPB SPR; lia
           | |- _ <= _ - SKPOPFREE_STACK _ => unfold SKPOPFREE_STACK, EXTFREE_STACK, FR_ossl_echext_free, FR_sk_pop_free, CFREE_STACK, RFREE_STACK; clear - LO8K; lia
           | |- _ mod 2 = 0 => unfold DX_R10; rewrite unsigned_lit by lia; reflexivity
           | |- ?G => idtac "PFPRE" G
           end. }
    clear PF. intros [ms4 mo4] PO. unfold skpopfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0' & c1' & c2' & c3' & c4' & c5' & c6' & c7' & v3 & v4 & v5 & v6 & m4 & st4 & LB4 &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & PERM4 & HP4 & XP4 & IM4 & GM4 & GG4).
    subst K3. rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk in PERM4. fold EB in PERM4.
    rewrite (unsigned_lit (bv_unsigned sp + -144)) in ST4, XP4 by lia.
    assert (PL4 : Permutation LB4 REST) by (apply (Permutation_app_inv_l (blocks_SK P K ++ EB)); rewrite <- (app_assoc (blocks_SK P K) EB LB4); exact PERM4).
    assert (SUB4 : forall b, In b REST -> In b LB4) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL4| exact Hb]).
    eapply (dx_fail_end m4 mo4 st4 errv' P (Some (K, es)) cur rem LB4 LE c E' pad1 pad2 pad3 pad4); try eassumption.
    all: cbv delta [spq]; lazymatch goal with
         | |- hs_MPRES _ _ _ => eapply (mpres_trans H HH); [exact MP| exact MP4]
         | |- Permutation _ (blocks_ERRST _ ++ _ ++ LB) => subst REST; exact PL4
         | |- LIBMID _ ?m _ => eapply (LIBMID_xpres0 _ _ (bv_unsigned sp + -144) _ m); [| exact XP4| intros b Hb; apply SUB4; subst REST; apply in_or_app; right; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply LIBSUB; exact Hb]];
                              eapply (LIBMID_xpres0 _ (EB ++ REST) (bv_unsigned sp + -144)); [exact LM| apply XPs; auto| intros b Hb; subst REST; apply in_or_app; right; apply in_or_app; right; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply LIBSUB; exact Hb]]
         | |- rw_cells _ _ (bv_unsigned sp + -144) _ => eapply xpres_rw_cells'; [exact XP4| exact FR2| left; lia| apply Forall_nil]
         | |- rw_cells _ _ ee _ => eapply xpres_rw_cells'; [exact XP4| eapply (xpres_rw_cells' _ _ _ _ _ _ _ (XPs LB SUBLR2)); [exact EC| right; right; exists (en_id E, ee, ENTRY_SIZE); split; [exact EIN0| unfold entry_cells; cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]; unfold ENTRY_SIZE; lia]| apply Forall_nil]| | apply Forall_nil];
                                   right; right; exists (en_id E, ee, ENTRY_SIZE); split; [apply SUB4; subst REST; do 2 (apply in_or_app; right); exact EIN0| unfold entry_cells; cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]; unfold ENTRY_SIZE; lia]
         | |- rw_cells _ _ pk _ => eapply xpres_rw_cells'; [exact XP4| eapply rw_cells_transport; [exact PK| exact MU2| exact WM2| cbn; split; [clear - SPK; lia| split; [clear - SH SPK CEIL LO8K; lia| exact I]]]| left; clear - SPK; lia| apply Forall_nil]
         | |- bytes_at _ _ base _ => eapply (xpres_bytes_at _ _ _ _ _ _ _ XP4); [eapply (xpres_bytes_at _ _ _ _ _ _ _ (XPs LB SUBLR2)); [exact BS| split; [| apply Forall_nil]; right; right; exists (pbin, base, len); split; [exact BIN| cbn; pose proof BSL as BSLq; unfold zlength in BSLq |- *; lia]]|];
                                    split; [| apply Forall_nil]; right; right; exists (pbin, base, len); split; [apply SUB4; subst REST; do 2 (apply in_or_app; right); exact BIN| cbn; pose proof BSL as BSLq; unfold zlength in BSLq |- *; lia]
         | |- xpres LB _ X0 m0 _ => eapply xpres_trans; [exact XP0|]; eapply xpres_trans; [eapply xpres_weaken; [apply (XPs LB SUBLR2)| clear - SPR; lia| auto| intros q Hq; destruct Hq]|];
                                   eapply xpres_weaken; [exact XP4| clear - SPR; lia| intros b Hb; apply SUB4; subst REST; do 2 (apply in_or_app; right); exact Hb| intros q Hq; destruct Hq]
         | |- ?G => idtac "FT2" G
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_stack_raise : lo <= spq - RAISE_STACK (mid_err M).
  Proof.
    cbv delta [spq]. clear - LO.
    unfold DECEXTS_STACK, FR_ech_decode_echconfig_exts in LO. change RREALLOC_STACK with 8256 in LO.
    destruct (mid_err M) as [|c0] eqn:E0.
    - change (RAISE_STACK ErrFresh) with 9360. change (errph_stack ErrFresh) with 9328 in LO. lia.
    - change (RAISE_STACK (ErrReady c0)) with 8304. change (errph_stack (ErrReady c0)) with 144 in LO. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_fail : forall m mo' s' errv' P xs NB c cur rem line s_ (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w7 w8 w11 : word),
    dworldX m mo' s' errv' P xs NB c cur rem [] -> (line = 206 \/ line = 210) ->
    hs_SR H (decexts_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s_ LIB LB M ee pk base len cur0 rem0 E bs lo B m0 mo)
      (mkCfg (MS (mkR (Z_to_bv 64 DX_RA1) (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pk) (Z_to_bv 64 0)
                        (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 1) w7 w8 (Z_to_bv 64 SSL_R_BAD_ECHCONFIG_EXTENSION) (Z_to_bv 64 line) w11 t3 t4 t5 t6)
                  F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom rsegs)) mo').
  Proof.
    intros m mo' s' errv' P xs NB c cur rem line s_ t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w7 w8 w11 FW LN.
    pose proof FW as (MI & ST & FR & ERR & AUX & KREL & MP & HP & LM & EO & PB & XI & PK & PIN & CR & [CB1 CB2] & BS & XP0).
    pose proof dx_stack_raise as LOR. cbv delta [spq] in *. hcb. pose proof (word_range sp) as SPR. cbn [app] in HP.
    pose proof LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL). rewrite MF0 in MF. rewrite CX in CP, EPm. cbn [ERRPH_mid] in EPm.
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (SUBL : forall b, In b LIB -> In b (NB ++ LB)) by (intros b Hb; apply in_or_app; right; apply LIBSUB; exact Hb).
    assert (SUBH : forall b, In b (NB ++ LB) -> In b (mid_errblocks M ++ NB ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    (* [comment removed for export] *)
    assert (NBB : lb_bytes NB <= 88 + 8 * c /\ 5 * Z.of_nat (length NB) <= 2 * c + 10 /\ lb_big NB <= 1).
    { revert PB XI. unfold XINV. destruct xs as [[K es]|]; intros PB XI.
      - destruct XI as (KC & K4 & KCAP & E5 & EBY & EBG). rewrite blocks_EXTS_some in PB.
        pose proof (blocks_SK_facts P K ltac:(lia)) as (SKB & SKL & _ & SKG & _).
        rewrite <- (lb_bytes_perm _ _ PB), <- (Permutation_length PB), <- (lb_big_perm _ _ PB), lb_bytes_app, length_app, lb_big_app, Nat2Z.inj_add.
        unfold SK_SIZE in SKB. unfold zlength in *. clear - K4 KCAP E5 EBY EBG SKB SKL SKG. lia.
      - destruct XI as [_ C0]. pose proof (Permutation_nil PB) as ->. cbn. clear - C0. lia. }
    destruct NBB as (NBB & NBL & NBG). unfold zlength in *. unfold pk_in in PIN.
    (* [comment removed for export] *)
    assert (ESA : forall c0 b', mid_err M = ErrReady c0 -> In b' (NB ++ LB) -> (forall b, In b LIB -> blk_id b <> blk_id b') ->
                   blk_addr b' + blk_size b' <= blk_addr (ec_es c0) \/ blk_addr (ec_es c0) + ERRST_SIZE <= blk_addr b').
    { intros c0 b' PH Hb' NE. rewrite PH in EPm. cbn [ERRPH] in EPm. destruct EPm as [_ CH]. pose proof CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP (SUBH _ (SUBL _ I5)) (SUBH _ Hb') (NE _ I5)) as DJ. rewrite Z5 in DJ. clear - DJ. lia. }
    assert (ESH : forall c0, mid_err M = ErrReady c0 -> blk_addr (ec_es c0) + ERRST_SIZE <= hceil).
    { intros c0 PH. rewrite PH in EPm. cbn [ERRPH] in EPm. destruct EPm as [_ CH]. pose proof CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
      pose proof (HB _ (SUBH _ (SUBL _ I5))) as K5. rewrite Z5 in K5. exact K5. }
    eapply (raise_spec H HX EGS) with (lo := lo) (B := B) (LB := NB ++ LB) (s := s') (ph := mid_err M) (E := mid_E M) (x := x) (errv := errv')
      (file := DX_FILE_ECHS) (fs := S_ECHS_FILE) (fsl := K_ECHS_FILE) (func := DX_FUNC) (gs := S_DX_FUNC) (gsl := K_DX_FUNC)
      (line := line) (lib := DX_ERR_LIB_SSL) (reason := SSL_R_BAD_ECHCONFIG_EXTENSION) (ra2 := DX_RA2) (ra3 := DX_RA3);
      try (rewrite unsigned_lit by lia); try eassumption.
    all: lazymatch goal with
         | |- hs_RHEAP _ _ _ _ => exact HP
         | |- lb_bytes _ + _ <= _ => unfold raise_bytes; rewrite !lb_bytes_app in *; unfold DECEXTS_BYTES, ERRDEBUG_BYTES in *; change (mid_errblocks M) with (blocks_ERRST (mid_E M)) in BY;
                                      pose proof (errph_nonneg (mid_err M)) as (EB0 & _); clear - BY EB0 NBB CB1 CB2 PIN REM1; lia
         | |- Z.of_nat (length _) + _ <= _ => unfold raise_cnt; rewrite !length_app, !Nat2Z.inj_add in *; change (mid_errblocks M) with (blocks_ERRST (mid_E M)) in CN;
                                               pose proof (errph_nonneg (mid_err M)) as (_ & EC0 & _); clear - CN EC0 NBL CB2 PIN Q5; lia
         | |- lb_big _ + _ <= _ => rewrite !lb_big_app in *; change (mid_errblocks M) with (blocks_ERRST (mid_E M)) in BG; pose proof (errph_nonneg (mid_err M)) as (_ & _ & EG0); clear - BG EG0 NBG; lia
         | |- _ <= B => clear - SPB SPR; lia
         | |- _ mod 16 = 0 => clear - SPA SPR; replace (bv_unsigned sp + -144) with (bv_unsigned sp - 9 * 16) by lia; rewrite Zminus_mod, SPA, Z_mod_mult; reflexivity
         | |- _ <= _ - RAISE_STACK _ => exact LOR
         | |- ERRPH _ _ _ => destruct (mid_err M) as [|c0]; cbn [ERRPH] in EPm |- *; [exact EPm| destruct EPm as [ES CH]; split; [exact ES| eapply ERR_chain_mono; [exact CH| exact SUBL]]]
         | |- errph_below _ _ =>
             destruct (mid_err M) as [|c0]; [exact I|]; cbn [errph_below]; cbn [ERRPH] in EPm; destruct EPm as [_ CH];
             pose proof CH as (I2 & _ & _ & I3 & _ & _ & I4 & _ & _ & I5 & _ & I6 & _);
             pose proof (HB _ (SUBH _ (SUBL _ I2))) as K2; pose proof (HB _ (SUBH _ (SUBL _ I3))) as K3; pose proof (HB _ (SUBH _ (SUBL _ I4))) as K4; pose proof (HB _ (SUBH _ (SUBL _ I5))) as K5;
             pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBH _ (SUBL _ I2))) as (P2 & _); pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBH _ (SUBL _ I3))) as (P3 & _);
             pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBH _ (SUBL _ I4))) as (P4 & _); pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBH _ (SUBL _ I5))) as (P5 & _);
             pose proof CH as (_ & Z2 & _ & _ & Z3 & _ & _ & Z4 & _ & _ & Z5 & _); rewrite Z2 in K2; rewrite Z3 in K3; rewrite Z4 in K4; rewrite Z5 in K5;
             unfold chain_below; clear - K2 K3 K4 K5 P2 P3 P4 P5 CEIL; lia
         | |- CTXPH _ _ _ => eapply CTXPH_mono; [exact CP| exact SUBL]
         | |- ROSTR DX_FILE_ECHS _ _ => exact R_ECHS_FILE
         | |- ROSTR DX_FUNC _ _ => exact R_DX_FUNC
         | |- _ <> [] => discriminate
         | |- Z.of_nat (length S_ECHS_FILE) < 24 => rewrite S_ECHS_FILE_len; lia
         | |- Z.of_nat (length S_DX_FUNC) < 32 => rewrite S_DX_FUNC_len; lia
         | |- 0 < DX_FILE_ECHS => unfold DX_FILE_ECHS; lia
         | |- 0 < DX_FUNC => unfold DX_FUNC; lia
         | |- 0 <= _ < 2^31 => clear - LN; lia
         | |- 0 < DX_ERR_LIB_SSL < 256 => unfold DX_ERR_LIB_SSL; lia
         | |- DX_ERR_LIB_SSL <> 2 => unfold DX_ERR_LIB_SSL; lia
         | |- 0 < SSL_R_BAD_ECHCONFIG_EXTENSION < _ => unfold SSL_R_BAD_ECHCONFIG_EXTENSION; lia
         | |- 0 <= DX_RA1 < _ => unfold DX_RA1; lia
         | |- DX_RA1 mod 2 = 0 => reflexivity
         | |- 0 <= DX_RA2 < _ => unfold DX_RA2; lia
         | |- DX_RA2 mod 2 = 0 => reflexivity
         | |- 0 <= DX_RA3 < _ => unfold DX_RA3; lia
         | |- DX_RA3 mod 2 = 0 => reflexivity
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_debug) _ _ _ _) _ =>
             intros; eapply dx_glue1; [clear - LN; lia| assumption]
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_error) _ _ _ _) _ =>
             intros; eapply dx_glue2; [unfold SSL_R_BAD_ECHCONFIG_EXTENSION; lia| assumption]
         | |- _ => idtac
         end.
    (* [comment removed for export] *)
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m' mo'' s'' errv'' LE c0 p1 p2 A1 A2 n1 n2 E'
           KREL' MP' MI' ST' AUX' HP' MF' IM' GM' RL' ERR' DL RSZ EP' CP' EST' XP'.
    rewrite ?unsigned_lit in ST' by lia. rewrite ?unsigned_lit in XP' by lia.
    pose proof (xpres_drop_memflag _ _ _ _ _ _ MF MF' XP') as XPd. fold (EF (mid_err M)) in XPd.
    assert (XPL : xpres LB (bv_unsigned sp + -144) (EF (mid_err M)) m m') by (eapply xpres_weaken; [exact XPd| lia| intros b Hb; apply in_or_app; right; exact Hb| auto]).
    (* [comment removed for export] *)
    assert (AVB : forall b', In b' (NB ++ LB) -> (forall b, In b LIB -> blk_id b <> blk_id b') -> avoids (EF (mid_err M)) (blk_addr b') (blk_size b')).
    { intros b' Hb' NE. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUBH _ Hb')) as (_ & _ & _ & _ & OFF).
      apply avoids_EF; [unfold IMG_LO, IMG_HI; exact OFF|]. intros c1 Hc1. exact (ESA c1 b' Hc1 Hb' NE). }
    assert (AVF : avoids (EF (mid_err M)) (bv_unsigned sp + -144) 144).
    { apply avoids_EF; [unfold IMG_LO, IMG_HI; clear - CEIL LO8K HCEILB; lia|]. intros c1 Hc1. pose proof (ESH c1 Hc1) as EH1. clear - EH1 CEIL LO8K. lia. }
    assert (AVP : avoids (EF (mid_err M)) pk 24).
    { apply avoids_EF; [unfold IMG_LO, IMG_HI; clear - CEIL LO8K HCEILB SPK; lia|]. intros c1 Hc1. pose proof (ESH c1 Hc1) as EH1. clear - EH1 CEIL LO8K SPK. lia. }
    (* [comment removed for export] *)
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND.
    assert (NNB : forall b' b, In b' NB -> In b LIB -> blk_id b <> blk_id b').
    { intros b' b Hb' Hb. destruct (nd_app _ _ ND) as [_ ND1]. apply not_eq_sym. exact (nodup_ids_app_ne _ _ _ _ ND1 Hb' (LIBSUB _ Hb)). }
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC) & _).
    eapply (dx_fail_tail m' mo'' s'' errv'' P xs NB cur rem (blocks_ERRST E' ++ LE ++ NB ++ LB) LE c0 E' line); try eassumption.
    all: cbv delta [spq]; lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned sp + -144) _ => eapply xpres_rw_cells'; [exact XPd| exact FR| left; lia| unfold dx_frame; cbn [cells_size csize Nat.add length]; exact AVF]
         | |- hs_MPRES _ _ _ => eapply (mpres_trans H HH); [exact MP| exact MP']
         | |- Permutation _ _ => apply Permutation_refl
         | |- LIBMID _ _ _ =>
             eapply (LIBMID_errcall LIB (NB ++ LB) (LE ++ NB ++ LB) LE); [exact LM| exact CX| exact XPd| exact SUBL| exact CP'| exact EP'| exact DL| exact EST'| apply errst_fits_raise; [exact FIT| exact RSZ]| exact MF']
         | |- ENTRYobj _ _ _ _ =>
             eapply (ENTRYobj_frameX (NB ++ LB) (bv_unsigned sp + -144) (EF (mid_err M))); [exact EO| exact XPd|];
             intros b Hb; rewrite blocks_EW in Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb];
             [ apply AVB; [eapply (ENTRYobj_owned_law _ _ _ _ EO); rewrite blocks_EW; apply in_or_app; left; exact Hb| intros bq Hbq; exact (IDS _ _ Hbq Hb)]
             | apply AVB; [apply in_or_app; left; eapply Permutation_in; [exact PB| exact Hb]| intros bq Hbq; apply (NNB b bq); [eapply Permutation_in; [exact PB| exact Hb]| exact Hbq]] ]
         | |- rw_cells _ _ pk _ => eapply xpres_rw_cells'; [exact XPd| exact PK| left; clear - SPK; lia| unfold pk_cells; cbn [cells_size csize Nat.add length]; exact AVP]
         | |- pk_in _ _ _ _ => unfold pk_in; clear - PIN; lia
         | |- _ <= rem0 => clear - CB1 CB2; lia
         | |- bytes_at _ _ base _ =>
             eapply xpres_bytes_at; [exact XPL| exact BS|]; split;
             [ right; right; exists (pbin, base, len); split; [exact BIN| cbn; pose proof BSL as BSLq; unfold zlength in BSLq |- *; lia]
             | eapply avoids_sub; [apply (AVB (pbin, base, len)); [apply in_or_app; right; exact BIN| intros bq Hbq; cbn; exact (IDB _ Hbq)]| cbn; lia| cbn; pose proof BSL as BSLq; unfold zlength in BSLq |- *; lia] ]
         | |- xpres LB _ X0 m0 _ => eapply xpres_trans; [exact XP0|]; eapply xpres_weaken; [exact XPL| clear - SPR; lia| auto|]; intros q Hq; unfold X0; unfold EF in Hq; cbn [rin_ivs fst snd]; right; right; exact Hq
         | |- ?G => idtac "RSK" G
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_main : forall (rax a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 w3 w7 w8 w9 w10 w11 : word) m1 s_ errv,
    mem_inv rsegs m1 -> stk rsegs m1 lo spq -> rw_cells rsegs m1 spq (dx_frame j0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
    rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> hs_rauxv_ok H m1 B -> hs_KREL H s_ mo ->
    hs_RHEAP H s_ (mid_errblocks M ++ LB) m1 -> LIBMID LIB m1 M -> ENTRYobj LB m1 ee E ->
    rw_cells rsegs m1 pk (pk_cells cur0 base rem0) -> bytes_at rsegs m1 base bs -> xpres LB (bv_unsigned sp) X0 m0 m1 ->
    hs_SR H (decexts_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s_ LIB LB M ee pk base len cur0 rem0 E bs lo B m0 mo)
      (mkCfg (MS (mkR rax (Z_to_bv 64 spq) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 pk) w3
                        (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 1) w7 w8 w9 w10 w11 t3 t4 t5 t6)
                  F (Z_to_bv 64 DX_HEAD) fc None m1 (seg_rom rsegs)) mo).
  Proof.
    intros rax a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 w3 w7 w8 w9 w10 w11 m1 s_ errv MI ST FR ERR AUX KREL HP LM EO PK BS XP.
    assert (FW : dworld m1 mo s_ errv 0 None [] cur0 rem0).
    { unfold dworld, dworldX. cbn [app]. rewrite EW0. replace (rem0 - rem0) with 0 by lia.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      all: lazymatch goal with
           | |- hs_MPRES _ _ _ => apply (mpres_refl H HH)
           | |- Permutation _ _ => apply Permutation_refl
           | |- XINV _ _ _ => unfold XINV; split; reflexivity
           | |- pk_in _ _ _ _ => exact PKIN0
           | |- _ = _ => reflexivity
           | |- _ <= _ <= _ => lia
           | |- _ <= _ => lia
           | |- ?G => idtac "MAIN0" G
           end. }
    eapply (sr_seq H HH); [eapply (DX_loop (Z.to_nat rem0)); [exact FW| rewrite Z2Nat.id by lia; lia]|].
    intros [ms2 mo2] EXT. unfold dx_exit in EXT. cbn [cfg_ms cfg_model] in EXT.
    destruct EXT as (rax2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u0 & u1 & u2 & u3 & u4 & u5 & u6 & v3 & v7 & v8 & v9 & v10 & v11 & m2 & mo2' & st2 & errv2 & P2 & xs2 & NB2 & cur2 & rem2 & <- & CASES).
    destruct CASES as [(R0 & FW2 & ->)|(line & cc & LN & FW2 & ->)].
    - eapply dx_ret1; [exact FW2| exact R0].
    - eapply dx_fail; [exact FW2| exact LN].
  Qed.
End W.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WS.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis EGS : egs_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.

  Theorem decexts_spec : decexts_stmt H.
  Proof using HX EGS.
    unfold decexts_stmt. intros until errv.
    intros A0 A1 EO XE0 XO0 BEL PK PIN REM1 REMB SPK PKB BIN EBIN BS BSL CRB LM LIBSUB CX MF0 IDS IDB HP KREL BY CN BG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (LO8K : lo + 8592 <= bv_unsigned sp) by (clear - LO; unfold DECEXTS_STACK, FR_ech_decode_echconfig_exts in LO; change RREALLOC_STACK with 8256 in LO; lia).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof EO as (_ & EIN0 & O1 & O2 & O3 & O4 & _).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply dx_seg1 with (lo := lo); [exact A0| exact A1| exact ST| exact CEIL| clear - LO8K; lia| exact MI]|].
    cbv beta. intros ms1 (m1 & j0 & a0' & a1' & a2' & a3' & a4' & a5' & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (XP1 : forall X, xpres LB (bv_unsigned sp) X m m1).
    { intros X. eapply xpres_of_munch; [exact MU1| exact WM1| | intros b Hb; apply HB; apply in_or_app; right; exact Hb]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    pose proof (rw_cells_bound _ _ _ _ PK) as PKR.
    eapply (dx_main H HX EGS) with (j0 := j0); try eassumption.
    all: lazymatch goal with
         | |- rw_cells _ _ (errno_addr _) _ => rewrite TP in *; rewrite errno_RATP in *; eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| unfold RERRNO; cbn; clear - CEIL LO8K HCEILB; lia]
         | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL; apply Forall_cons; [cbn; clear - CEIL LO8K HCEILB SPB; lia| apply Forall_nil]
         | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]; apply Forall_cons; [left; cbn; clear - CEIL LO8K; lia| apply Forall_nil]
         | |- LIBMID _ _ _ => eapply LIBMID_xpres0; [exact LM| apply (XP1 [])| exact LIBSUB]
         | |- ENTRYobj _ _ _ _ => eapply ENTRYobj_frameX; [exact EO| apply (XP1 [])| intros b Hb; apply avoids_nil]
         | |- rw_cells _ _ _ (pk_cells _ _ _) => eapply rw_cells_transport; [exact PK| exact MU1| exact WM1| cbn; clear - SPK; lia]
         | |- bytes_at _ _ _ _ => eapply bytes_at_transport; [exact BS| exact MU1|]; cbn; split; [| exact I]; pose proof (HB _ ltac:(apply in_or_app; right; exact BIN)) as K2; cbn [blk_addr blk_size fst snd] in K2; unfold zlength in BSL; clear - K2 CEIL LO8K BSL; lia
         | |- xpres _ _ _ _ _ => apply XP1
         | |- _ /\ _ => repeat split; assumption
         | |- ?G => idtac "WSPRE" G
         end.
  Qed.
End WS.
