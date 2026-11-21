(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Frame Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun InflateInvApi InflateInvLoop InflateInvCall InflateRc InflateCall HarnessKit HarnessFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.FMQ6 Require Import CallocLib6 CallocTail6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 Callee6 CalleeKits6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 Callee6i Itab6 UpdWin6
     Infl6 Infl6B Infl6C IfSpec6 IfFast6 InffastOk IRep6 IInit6 ITok6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import ZlibStmtBase ExSmallIface FlLibStmt FlLibIface.
Import InflLv Infl6A.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation RSX := Src_zlib_example_flush_fuzzer_repro.M.loaded_segments.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Lemma ret_ok_ra : forall ra, ra_ok ra -> ret_ok (Z_to_bv 64 ra).
Proof. intros ra [H1 H2]. apply ret_ok_even. change (Z_to_bv 64 ra) with (zw ra). rewrite u_zw_small by lia. exact H2. Qed.

Lemma holds_cells : forall m a zs, 0 <= a -> a + zlength zs <= 2 ^ 64 ->
  holds RSX m a zs -> cells s6_segs m a 1 1 (zlength zs) (fun i => nth (Z.to_nat i) zs 0).
Proof.
  intros m a zs Ha Hl H i Hi. unfold holds in H. unfold cell.
  pose proof (rdn_sub s6_segs (Z.to_nat i) (length zs) (Z_to_bv 64 a) m _ 1 H ltac:(unfold zlength in Hi; lia)) as R.
  replace (zw (a + 1 * i)) with (Z_to_bv 64 a + nat_to_word (Z.to_nat i))%bv.
  2:{ change (Z_to_bv 64 a) with (zw a). rewrite <- zw_add_nat. f_equal. lia. }
  rewrite R. f_equal. rewrite skipn_map, firstn_map.
  rewrite (skipn_nth zs (Z.to_nat i) 0) by (unfold zlength in Hi; lia). reflexivity.
Qed.

Lemma cells_holds : forall m a zs, 0 <= a -> a + zlength zs <= 2 ^ 64 ->
  cells s6_segs m a 1 1 (zlength zs) (fun i => nth (Z.to_nat i) zs 0) -> holds RSX m a zs.
Proof.
  intros m a zs Ha. unfold holds, cells, cell. unfold s6_segs. change (zw) with (Z_to_bv 64). revert a Ha.
  induction zs as [|z zs IH]; intros a Ha Hl H; [reflexivity|].
  cbn [length rdn map]. unfold zlength in *. cbn [length] in Hl, H.
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.mul_0_r, Z.add_0_r in H0. cbn [rdn Z_to_le_bytes Z.to_nat nth] in H0.
  destruct (match m (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSX (Z_to_bv 64 a) end) as [b|]; [| discriminate].
  injection H0 as <-.
  specialize (IH (a + 1) ltac:(lia) ltac:(lia)).
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  2:{ change (Z_to_bv 64 (a + 1)) with (zw (a + Z.of_nat 1)). rewrite zw_add_nat. reflexivity. }
  rewrite IH; [reflexivity|].
  intros i Hi. specialize (H (i + 1) ltac:(lia)). replace (a + 1 + 1 * i) with (a + 1 * (i + 1)) by lia.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in H by lia. cbn [nth] in H. exact H.
Qed.

Lemma arr_get_of_list : forall l i, 0 <= i < zlength l -> arr_get (arr_of_list l) i = nth (Z.to_nat i) l 0.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  unfold arr_inb. rewrite arr_len_make.
  replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
  replace (i <? 0 + zlength l) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (i <? zlength l) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma nth_arr_slice0 : forall (a : arr) k i, 0 <= i < k -> nth (Z.to_nat i) (arr_slice a 0 k) 0 = arr_get a i.
Proof.
  intros a k i Hi. unfold arr_slice.
  replace (Z.to_nat k) with (Z.to_nat i + S (Z.to_nat (k - i - 1)))%nat by lia.
  generalize (Z.to_nat (k - i - 1)); intros n.
  assert (G : forall m st j, nth m (arr_slice_nat a st (m + S j)) 0 = arr_get a (st + Z.of_nat m)).
  { intros m. induction m as [|m IH]; intros st j; cbn [arr_slice_nat nth Nat.add]; [f_equal; lia|].
    rewrite IH. f_equal. lia. }
  rewrite G. f_equal. lia.
Qed.

Lemma uw_core_blk : forall s src e k, is_window_blk (uw_core s src e k) = is_window_blk s.
Proof.
  intros s src e k. unfold uw_core.
  destruct (is_wsize _ <=? k); [| destruct (negb _)]; [| | destruct (_ =? _); destruct (_ <? _)]; destruct (is_wsize s =? 0); destruct s; reflexivity.
Qed.
Lemma leave_tail_blk : forall fl s ic r, is_window_blk (fst (leave_tail fl s ic r)) = is_window_blk s.
Proof. intros fl s ic r. unfold leave_tail. destruct (_ && _); destruct s; reflexivity. Qed.

Lemma inflate_p_blk : forall ans s zc fl, UI s -> zcall_ok zc -> is_window_blk s <> None ->
  snd (inflate_p ivar_ref ans s zc fl) = None /\ is_window_blk (fst (fst (inflate_p ivar_ref ans s zc fl))) <> None.
Proof.
  intros ans s zc fl U ZC Hb.
  destruct (inflateStateCheck s) eqn:Hc.
  { unfold inflate_p. rewrite Hc. cbn. split; [reflexivity | exact Hb]. }
  rewrite (inflate_p_W1M ivar_ref ans s zc fl Hc).
  pose proof (ui_entry s zc U ZC) as PI.
  pose proof (inf_loop_exit ivar_ref fl _ _ (arr_len (is_window s)) (zs_total_out (zc_strm zc)) (zcall_NI zc ZC) (zcall_NO zc ZC) _ PI) as X.
  cbv zeta in X. destruct (inf_loop ivar_ref fl (W1M s (icall_of_zcall zc))) as [stop [s' c' r']]. cbn [fst snd w_s w_c w_r] in X |- *.
  destruct X as (LR & _). apply LRNGq_iff in LR. destruct LR as (_ & _ & _ & WI & _). unfold WINV in WI. cbn [w_s] in WI.
  destruct WI as (WL & _ & WNiff & _).
  assert (Hb' : is_window_blk s' <> None).
  { intros E. apply Hb. destruct U as ((SR & _ & WS) & _). destruct (is_window_blk s) as [b|]; [| reflexivity].
    exfalso. destruct WS as [L _]. pose proof (proj2 WNiff E) as Z0. rewrite Z0 in L.
    assert (Hwb : 8 <= is_wbits s <= 15) by (destruct SR as (_ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
    assert (0 < 2 ^ is_wbits s) by (apply Z.pow_pos_nonneg; lia). lia. }
  destruct stop as [|rc]; cbn [fst snd]; [| split; [reflexivity | exact Hb']].
  unfold inf_leave_p. cbn [w_s w_c w_r RESTORE].
  destruct (leave_need fl _ _ r'); cbn [fst snd].
  - destruct (is_window_blk (iset_bits (iset_hold s' (ir_hold r')) (ir_bits r'))) as [b|] eqn:EB; cbn [fst snd].
    + split; [reflexivity|]. rewrite leave_tail_blk, uw_core_blk, EB. discriminate.
    + exfalso. apply Hb'. destruct s'; exact EB.
  - split; [reflexivity|]. rewrite leave_tail_blk. destruct s'; exact Hb'.
Qed.

Lemma inflate_p_blk_none : forall ans s zc fl, UI s -> zcall_ok zc -> is_window_blk s = None ->
  snd (inflate_p ivar_ref ans s zc fl) = None -> is_window_blk (fst (fst (inflate_p ivar_ref ans s zc fl))) = None.
Proof.
  intros ans s zc fl U ZC Hb HA.
  destruct (inflateStateCheck s) eqn:Hc.
  { unfold inflate_p in *. rewrite Hc in *. cbn. exact Hb. }
  rewrite (inflate_p_W1M ivar_ref ans s zc fl Hc) in HA |- *.
  pose proof (ui_entry s zc U ZC) as PI.
  pose proof (inf_loop_exit ivar_ref fl _ _ (arr_len (is_window s)) (zs_total_out (zc_strm zc)) (zcall_NI zc ZC) (zcall_NO zc ZC) _ PI) as X.
  cbv zeta in X. destruct (inf_loop ivar_ref fl (W1M s (icall_of_zcall zc))) as [stop [s' c' r']]. cbn [fst snd w_s w_c w_r] in X, HA |- *.
  destruct X as (LR & _). apply LRNGq_iff in LR. destruct LR as (_ & _ & _ & WI & _). unfold WINV in WI. cbn [w_s] in WI.
  destruct WI as (WL & _ & WNiff & _).
  assert (Hb' : is_window_blk s' = None).
  { apply (proj1 WNiff). destruct U as ((SR & _ & WS) & _). rewrite Hb in WS. destruct WS as [L _]. exact L. }
  destruct stop as [|rc]; cbn [fst snd]; [| exact Hb'].
  unfold inf_leave_p in *. cbn [w_s w_c w_r RESTORE] in HA |- *.
  destruct (leave_need fl _ _ r'); cbn [fst snd] in HA |- *.
  - assert (EB : is_window_blk (iset_bits (iset_hold s' (ir_hold r')) (ir_bits r')) = None) by (destruct s'; exact Hb').
    rewrite EB in HA |- *. destruct ans as [[b g]|]; cbn [fst snd] in HA |- *; exfalso; discriminate HA.
  - rewrite leave_tail_blk. destruct s'; exact Hb'.
Qed.

Lemma inflate_p_asked : forall ans s zc fl sx cx rx sz,
  inflateStateCheck s = false ->
  inf_loop ivar_ref fl (W1M s (icall_of_zcall zc)) = (SLeave, mkW sx cx rx) ->
  is_wbits sx = 15 ->
  snd (inflate_p ivar_ref ans s zc fl) = Some sz -> sz = 32768.
Proof.
  intros ans s zc fl sx cx rx sz Hchk EQL Hwb H.
  rewrite (inflate_p_W1M ivar_ref ans s zc fl Hchk), EQL in H. unfold inf_leave_p in H. rewrite RESTORE_eq in H. cbn [w_s w_c w_r] in H.
  pose proof (sR_fields sx rx) as (_ & _ & _ & _ & _ & Y6 & _).
  destruct (leave_need fl (sR sx rx) (cR cx rx) rx); [| cbn [fst snd] in H; discriminate H].
  destruct (is_window_blk (sR sx rx)); [cbn [fst snd] in H; discriminate H|].
  assert (E : sz = mul32 (shl32 1 (is_wbits (sR sx rx))) 1) by (destruct ans as [[b g]|]; cbn [fst snd] in H; congruence).
  rewrite E, Y6, Hwb. reflexivity.
Qed.

Definition cvW (R0 : bvmap 5 word) (sp : Z) (q : iptrs) (inp outp : Z) (zc : ZCall) (f : Z) (WB WN : Z) : icv :=
  ICV sp R0 (ip_strm q) (ip_p q) inp outp WB (zlength (zc_input zc)) (zc_avail_out zc) WN f (zs_total_out (zc_strm zc)) FL_ZCALLOC FL_ZCFREE 0.

Definition TWF (R0 RW : bvmap 5 word) (q : iptrs) (inp outp : Z) (s : inflate_state) (zc : ZCall) (f : Z) (M : word -> option byte) : Prop :=
  exists (sp : Z) (sx : inflate_state) (cx : icall) (rx : iregs),
    let v := cvW R0 sp q inp outp zc f 0 0 in
    getr R0 2 = zw sp
    /\ inflateStateCheck s = false
    /\ inf_loop ivar_ref f (W1M s (icall_of_zcall zc)) = (SLeave, mkW sx cx rx)
    /\ leave_need f (sR sx rx) (cR cx rx) rx = true /\ is_window_blk sx = None
    /\ LX v (mkW sx cx rx) /\ SRNGq sx /\ RINV (zlength (zc_input zc)) (zc_avail_out zc) rx /\ CINV (zlength (zc_input zc)) (zc_avail_out zc) cx /\ is_wsize sx = 0
    /\ UI s /\ zcall_ok zc /\ LXS s /\ - 1 <= zs_msg (zc_strm zc) <= 27
    /\ ip_w q = 0 /\ is_window_blk s = None /\ arr_len (is_window s) = 0
    /\ ictx v /\ IRANGES q
    /\ WSTR v rx RW /\ getr RW 3 = getr R0 3 /\ getr RW 4 = getr R0 4
    /\ LMEMC v (mkW (sL (sR sx rx) (cR cx rx) rx) (cL v (sR sx rx) (cR cx rx) rx) rx) M
    /\ UWC sp rx (cv_S v) M   (* 1.4: the s0 slot holds inflate's S (x8) *)
    /\ mapped M (sp - INF_FRAME - INF_SCRATCH) (INF_FRAME + INF_SCRATCH) /\ mapped M (ip_strm q) 112 /\ mapped M (ip_p q) 7176
    /\ mapped M outp (zc_avail_out zc).

Section INF.
  Variables (regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (s : inflate_state) (zc : ZCall) (f : Z).
  Variables (sp ra inp outp zcl fa ff : Z).
  Local Abbreviation p := (ip_p q). Local Abbreviation strm := (ip_strm q). Local Abbreviation WB := (ip_w q).
  Local Abbreviation input := (zc_input zc). Local Abbreviation n := (zlength (zc_input zc)). Local Abbreviation NO := (zc_avail_out zc).

  Hypothesis G10 : getr regs 10 = zw strm.
  Hypothesis G11 : getr regs 11 = zw f.
  Hypothesis G2 : getr regs 2 = zw sp.
  Hypothesis G1 : getr regs 1 = zw ra.
  Hypothesis RA : ra_ok ra.
  Hypothesis SP16 : sp mod 16 = 0.
  Hypothesis HZC : zcl + FL_FRA <= sp.
  Hypothesis SP47 : sp <= 2 ^ 47.
  Hypothesis HTOP : FL_IMG_TOP <= zcl.
  Hypothesis BOK : blocks_ok mem zcl (iblocks q).
  Hypothesis IC : img_clear mem.
  Hypothesis STRM0 : 0 < strm.
  Hypothesis STRM47 : strm + 112 <= 2 ^ 47.
  Hypothesis STRM8 : strm mod 8 = 0.
  Hypothesis INP0 : 0 < inp.
  Hypothesis OUTP0 : 0 < outp.
  Hypothesis SOKf : store_ok RSX mem (Z_to_bv 64 (sp - FL_FRA)) (Z.to_nat FL_FRA) = true.
  Hypothesis SOKz : store_ok RSX mem (Z_to_bv 64 strm) 112%nat = true.
  Hypothesis SOKo : store_ok RSX mem (Z_to_bv 64 outp) (Z.to_nat NO) = true.
  Hypothesis AP : all_apart ((sp - FL_FRA, FL_FRA) :: (strm, 112) :: (outp, NO) :: (inp, n) :: iblocks q).
  Hypothesis IMG : forall a k, In (a, k) [(sp - FL_FRA, FL_FRA); (strm, 112); (outp, NO); (inp, n)] -> a + k <= FL_RO_LO \/ FL_IMG_TOP <= a.
  Hypothesis BI : inp + n < 2 ^ 63.
  Hypothesis BO : outp + NO < 2 ^ 63.
  Hypothesis NO31 : NO < 2 ^ 31.
  Hypothesis N31 : n < 2 ^ 31.
  Hypothesis IR : FL_IREP mem q s.
  Hypothesis WIFF : WB = 0 <-> is_window_blk s = None.
  Hypothesis HLD : holds RSX mem inp input.
  Hypothesis ZS : izs_cells FL_MSGA mem strm inp n outp NO (zc_strm zc) p fa ff.
  Hypothesis FA : fa = FL_ZCALLOC.
  Hypothesis FF : ff = FL_ZCFREE.
  Hypothesis SAFE : FL_ISAFE s zc f.

  Definition cvF : icv :=
    ICV sp regs strm p inp outp WB n NO (arr_len (is_window s)) f (zs_total_out (zc_strm zc)) fa ff 0.

  Lemma consts : FL_ZCALLOC = 0x19ff8 /\ FL_ZCFREE = 0x1a008 /\ FL_FRA = 1024 /\ FL_IMG_TOP = 0x5c000 /\ FL_RO_LO = 0x10000
                 /\ FL_ISTATE_N = 7176 /\ FL_WIN_N = 32768 /\ FL_IFR = 416 /\ FL_ZWD = 272.
  Proof. repeat split. Qed.

  Lemma st_facts : 0 < p /\ p mod 16 = 0 /\ p + 7176 <= zcl /\ (p + 7176 <= 0x10000 \/ 0x5c000 <= p)
    /\ store_ok RSX mem (Z_to_bv 64 p) (Z.to_nat 7176) = true
    /\ (WB <> 0 -> 0 < WB /\ WB mod 16 = 0 /\ WB + 32768 <= zcl /\ (WB + 32768 <= 0x10000 \/ 0x5c000 <= WB)
                   /\ store_ok RSX mem (Z_to_bv 64 WB) (Z.to_nat 32768) = true).
  Proof.
    pose proof BOK as B. unfold blocks_ok, iblocks in B. apply Forall_cons_iff in B as [BS BW]. cbn [fst snd] in BS.
    unfold blk_okz, FL_ISTATE_N, FL_WIN_N, FL_IMG_TOP in BS, BW. destruct BS as (A16 & P1 & PZ & PIM & SOP).
    repeat (split; [assumption|]). intros HWB.
    destruct (Z.eqb_spec WB 0) as [E|E]; [exfalso; exact (HWB E)|].
    apply Forall_inv in BW. cbn [fst snd] in BW. destruct BW as (W16 & W1 & WZ & WIM & SOW). repeat split; assumption.
  Qed.

  Lemma ap_facts : sep (sp - 1024) 1024 strm 112 /\ sep (sp - 1024) 1024 outp NO /\ sep (sp - 1024) 1024 inp n /\ sep (sp - 1024) 1024 p 7176
    /\ sep strm 112 outp NO /\ sep strm 112 inp n /\ sep strm 112 p 7176
    /\ sep outp NO inp n /\ sep outp NO p 7176 /\ sep inp n p 7176
    /\ (WB <> 0 -> sep (sp - 1024) 1024 WB 32768 /\ sep strm 112 WB 32768 /\ sep outp NO WB 32768 /\ sep inp n WB 32768 /\ sep p 7176 WB 32768).
  Proof.
    pose proof AP as A. unfold iblocks, FL_FRA, FL_ISTATE_N, FL_WIN_N in A.
    destruct (Z.eqb_spec WB 0) as [E|E]; cbn [all_apart apart_from_all app] in A; unfold ExSmallIface.apart, sep in *.
    - destruct A as ((A1 & A2 & A3 & A4 & _) & (A5 & A6 & A7 & _) & (A8 & A9 & _) & (A10 & _) & _).
      repeat match goal with |- _ /\ _ => split end; try assumption. intros X. exfalso. exact (X E).
    - destruct A as ((A1 & A2 & A3 & A4 & A4' & _) & (A5 & A6 & A7 & A7' & _) & (A8 & A9 & A9' & _) & (A10 & A10' & _) & (A11 & _) & _).
      repeat match goal with |- _ /\ _ => split end; try assumption. intros _. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  Lemma maps : mapped mem (sp - 416) 416 /\ mapped mem strm 112 /\ mapped mem p 7176 /\ (0 < NO -> mapped mem outp NO)
    /\ (WB <> 0 -> mapped mem WB 32768).
  Proof.
    pose proof st_facts as (P1 & P16 & PZ & PIM & SOP & W). pose proof RA as [RAB _]. pose proof (zlength_nonneg input) as N0.
    assert (KTOP : FL_IMG_TOP = 0x5c000) by reflexivity. assert (KRO : FL_RO_LO = 0x10000) by reflexivity.
    assert (KFRA : FL_FRA = 1024) by reflexivity. rewrite KTOP in HTOP. rewrite KFRA in HZC, SOKf.
    destruct SAFE as (_ & ZC & _). pose proof (zcall_NO zc ZC) as HNO.
    split; [| split; [| split; [| split]]].
    - intros x Hx. apply (mapped_of_store_ok6 mem (sp - 1024) 1024); [lia| lia| lia| lia | exact SOKf | lia].
    - intros x Hx. apply (mapped_of_store_ok6 mem strm 112); [lia| lia| lia| | exact SOKz | exact Hx].
      specialize (IMG strm 112 ltac:(right; left; reflexivity)). rewrite KTOP, KRO in IMG. exact IMG.
    - intros x Hx. apply (mapped_of_store_ok6 mem p 7176); [lia| lia| lia| exact PIM| exact SOP | exact Hx].
    - intros HNO' x Hx. apply (mapped_of_store_ok6 mem outp NO); [lia| lia| lia| | exact SOKo | exact Hx].
      specialize (IMG outp NO ltac:(right; right; left; reflexivity)). rewrite KTOP, KRO in IMG. exact IMG.
    - intros HWB x Hx. destruct (W HWB) as (W1 & W16 & WZ & WIM & SOW).
      apply (mapped_of_store_ok6 mem WB 32768); [lia| lia| lia| exact WIM| exact SOW | exact Hx].
  Qed.

  Lemma wn_facts : (WB = 0 -> arr_len (is_window s) = 0) /\ (WB <> 0 -> arr_len (is_window s) = 32768).
  Proof.
    destruct IR as ((SC & L1 & L2 & L3 & WC & WI & WL) & MR & RG). destruct SAFE as (U & _).
    split; [| exact WL].
    intros E. destruct U as ((SR & _ & WS) & _). rewrite (proj1 WIFF E) in WS. exact (proj1 WS).
  Qed.

  Lemma ictx_cvF : ictx cvF.
  Proof.
    pose proof st_facts as (P1 & P16 & PZ & PIM & SOP & W). pose proof RA as [RAB RA2]. pose proof (zlength_nonneg input) as N0.
    pose proof ap_facts as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & AW).
    pose proof wn_facts as [WN0 WN1].
    pose proof consts as (KA & KF & KFRA & KTOP & KRO & KIS & KWN & KIFR & KZWD).
    destruct SAFE as (U & ZC & LX4 & MSG & Hf). pose proof (zcall_NO zc ZC) as HNO. destruct ZC as (_ & _ & _ & _ & Zto & _).
    rewrite KTOP in HTOP. rewrite KFRA in HZC.
    pose proof (IMG strm 112 ltac:(right; left; reflexivity)) as IMGz.
    pose proof (IMG outp NO ltac:(right; right; left; reflexivity)) as IMGo.
    pose proof (IMG inp n ltac:(right; right; right; left; reflexivity)) as IMGi. rewrite KTOP, KRO in IMGz, IMGo, IMGi.
    pose proof (ret_ok_ra ra RA) as RET. change (Z_to_bv 64 ra) with (zw ra) in RET. rewrite <- G1 in RET.
    assert (Hfa : 0 <= fa < 2 ^ 64 /\ 0 <= ff < 2 ^ 64) by (rewrite FA, FF, KA, KF; clear; lia).
    assert (HW : (arr_len (is_window s) = 0 /\ WB = 0)
                 \/ (arr_len (is_window s) = 32768 /\ 0 < WB /\ WB mod 16 = 0 /\ WB + 32768 <= zcl /\ (WB + 32768 <= 65536 \/ 376832 <= WB)
                     /\ sep (sp - 1024) 1024 WB 32768 /\ sep strm 112 WB 32768 /\ sep outp NO WB 32768 /\ sep inp n WB 32768 /\ sep p 7176 WB 32768)).
    { destruct (Z.eq_dec WB 0) as [E|E]; [left; split; [exact (WN0 E) | exact E] | right].
      destruct (W E) as (W1 & W16 & WZ & WIM & SOW). destruct (AW E) as (B1 & B2 & B3 & B4 & B5).
      split; [exact (WN1 E)|]. repeat match goal with |- _ /\ _ => split end; assumption. }
    clear BOK AP IR WIFF HLD ZS IMG SOP SOKf SOKz SOKo IC W AW WN0 WN1 U LX4.
    unfold cvF. remember (arr_len (is_window s)) as WN eqn:EWN. clear EWN.
    Local Ltac wcase HW t0 t1 := destruct HW as [(EWN & EWB) | (EWN & W1 & W16 & WZ & WIM & B1 & B2 & B3 & B4 & B5)]; [rewrite ?EWN, ?EWB; t0 | rewrite ?EWN; t1].
    constructor; cbn [cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq];
      unfold offimg, IMG6_TOP, INF_FRAME, INF_SCRATCH, sep; unfold sep in *;
      [ exact RET
      | clear - HZC HTOP SP47 SP16; lia
      | clear - STRM0 STRM47 STRM8; lia
      | clear - P1 PZ HZC SP47 P16; lia
      | clear - INP0 BI N0 N31; lia
      | clear - OUTP0 BO HNO NO31; lia
      | wcase HW ltac:(clear; lia) ltac:(split; [clear - W1; lia|]; split; [clear - WZ HZC SP47; lia|]; right; split; [reflexivity|]; split; [exact W1 | exact W16])
      | exact Hf
      | exact Zto
      | clear - Hfa; lia
      | exact I
      | exact IMGz
      | exact PIM
      | intros _; exact IMGi
      | intros _; exact IMGo
      | wcase HW ltac:(clear; lia) ltac:(exact WIM)
      | clear - A1; lia
      | clear - A4; lia
      | intros _; clear - A3; lia
      | intros _; clear - A2; lia
      | wcase HW ltac:(clear - HZC HTOP; lia) ltac:(clear - B1; lia)
      | clear - A7; lia
      | clear - A6; lia
      | clear - A5; lia
      | wcase HW ltac:(clear - STRM0; lia) ltac:(clear - B2; lia)
      | intros _; clear - A10; lia
      | intros _; clear - A9; lia
      | wcase HW ltac:(clear - P1; lia) ltac:(clear - B5; lia)
      | clear - A8; lia
      | intros _; wcase HW ltac:(clear - INP0; lia) ltac:(clear - B4; lia)
      | intros _; wcase HW ltac:(clear - OUTP0; lia) ltac:(clear - B3; lia)
      | exact SP47
      | clear - PZ HZC; lia ].
  Qed.
  Lemma CMEM_entry : CMEM cvF s (icall_of_zcall zc) mem.
  Proof.
    pose proof st_facts as (P1 & P16 & PZ & PIM & SOP & W). pose proof (zlength_nonneg input) as N0.
    pose proof wn_facts as [WN0 WN1]. pose proof maps as (MF & MZ & MP & MO & MW).
    destruct SAFE as (U & ZC & LX4 & MSG & Hf). pose proof (zcall_NO zc ZC) as HNO.
    destruct IR as ((SC & L1 & L2 & L3 & WC & WI & WL) & MR & RG).
    destruct ZS as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C96). unfold cell8, cell4 in *.
    constructor; cbn [cvF cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq
                      icall_of_zcall ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg].
    - intros x Hx. unfold ROD6_LO, ROD6_HI in Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply IC. unfold FL_RO_LO, FL_RO_HI. exact Hx.
    - exact SC.
    - exact L1.
    - exact L2.
    - exact L3.
    - intros HWN. assert (E : WB <> 0) by (intros E; apply HWN; exact (WN0 E)). exact (WC E).
    - intros i Hi. rewrite arr_get_of_list by exact Hi. exact (holds_cells mem inp input ltac:(clear - INP0; lia) ltac:(clear - BI; lia) HLD i Hi).
    - intros i Hi. exfalso. clear - Hi. lia.
    - unfold izs6. cbn [cvF cv_ZP cv_S cv_I0 cv_P0 cv_fa cv_ff cv_opq icall_of_zcall ic_next_in ic_avail_in ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_msg].
      rewrite !Z.add_0_r. unfold FL_MSGA in C48. unfold cell.
      repeat match goal with |- _ /\ _ => split end; assumption.
    - unfold INF_FRAME, INF_SCRATCH. replace (sp - 224 - 192) with (sp - 416) by lia. exact MF.
    - exact MZ.
    - exact MP.
    - destruct (Z.eq_dec NO 0) as [E|E]; [intros x Hx; exfalso; clear - Hx E; lia | apply MO; clear - E HNO; lia].
    - intros HWN. assert (E : WB <> 0) by (intros E; apply HWN; exact (WN0 E)). rewrite (WN1 E). exact (MW E).
  Qed.

  Local Notation CALL6 thm := (thm cvF ictx_cvF memcpy_run6_ok ROM6 ROM6_of_rod6 adler32_run6_ok itable_run6_ok
                                   inflate_fast_spec6_holds FFOK FASTOK GFOB FFRAME CLPINV).

  Lemma frame_of_call : forall (M' : word -> option byte) (put' : Z),
    0 <= put' <= NO ->
    (forall x, mem x <> None -> M' x <> None) ->
    (forall x : word,
        ~ (sp - INF_FRAME - INF_SCRATCH <= bv_unsigned x < sp) -> ~ (p <= bv_unsigned x < p + 7176) ->
        ~ (strm <= bv_unsigned x < strm + 112) -> ~ (outp <= bv_unsigned x < outp + put') ->
        ~ (arr_len (is_window s) <> 0 /\ WB <= bv_unsigned x < WB + arr_len (is_window s)) ->
        M' x = mem x) ->
    frame_mod mem M' ((Z_to_bv 64 (sp - FL_IFR), FL_IFR) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, put') :: wz (iblocks q)).
  Proof.
    intros M' put' Hput Hg HE. pose proof st_facts as (P1 & P16 & PZ & PIM & SOP & W). pose proof wn_facts as [WN0 WN1].
    destruct SAFE as (U & ZC & _). pose proof (zcall_NO zc ZC) as HNO. pose proof (zlength_nonneg input) as N0.
    pose proof consts as (KA & KF & KFRA & KTOP & KRO & KIS & KWN & KIFR & KZWD). rewrite KTOP in HTOP. rewrite KFRA in HZC.
    split; [| exact Hg].
    intros a Hout. apply HE; unfold INF_FRAME, INF_SCRATCH; unfold iblocks, FL_IFR, FL_ISTATE_N, FL_WIN_N in Hout;
      cbn [outside wz map fst snd app] in Hout; unfold in_rng in Hout; change (Z_to_bv 64) with zw in Hout;
      pose proof (u64_range a) as Ha.
    - destruct Hout as [H1 _]. rewrite u_zw_small in H1 by (clear - HZC HTOP SP47; lia). clear - H1. lia.
    - destruct Hout as (_ & _ & _ & H4 & _). rewrite u_zw_small in H4 by (clear - P1 PZ HZC SP47; lia). clear - H4. lia.
    - destruct Hout as (_ & H2 & _). rewrite u_zw_small in H2 by (clear - STRM0 STRM47; lia). clear - H2. lia.
    - destruct Hout as (_ & _ & H3 & _). rewrite u_zw_small in H3 by (clear - OUTP0 BO HNO; lia). clear - H3. lia.
    - destruct (Z.eqb_spec WB 0) as [E|E].
      + rewrite (WN0 E). clear. lia.
      + cbn [outside map fst snd] in Hout. destruct Hout as (_ & _ & _ & _ & H5 & _). destruct (W E) as (W1 & _ & WZ & _).
        unfold in_rng in H5. change (Z_to_bv 64) with zw in H5.
        rewrite u_zw_small in H5 by (clear - W1 WZ HZC SP47; lia). rewrite (WN1 E). clear - H5. lia.
  Qed.

  Lemma post_of_CMEM : forall ans (M' : word -> option byte) (cf : icall),
    snd (inflate_p ivar_ref ans s zc f) = None ->
    let s' := fst (fst (inflate_p ivar_ref ans s zc f)) in
    CMEM cvF s' cf M' -> LXS s' -> CCUR cvF cf -> 0 <= ic_next_out cf <= NO ->
    FL_IREP M' q s'
    /\ izs_cells FL_MSGA M' strm (inp + ic_next_in cf) (n - ic_next_in cf) (outp + ic_next_out cf) (NO - ic_next_out cf) (zstrm_of_icall cf) p fa ff
    /\ holds RSX M' outp (arr_slice (ic_outbuf cf) 0 (ic_next_out cf))
    /\ (WB = 0 <-> is_window_blk s' = None).
  Proof.
    intros ans M' cf HA. cbv zeta. intros HM' HXS HCC Hput.
    pose proof st_facts as (P1 & P16 & PZ & PIM & SOP & W). pose proof wn_facts as [WN0 WN1].
    destruct SAFE as (U & ZC & LX4 & MSG & Hf).
    destruct IR as ((SC & L1 & L2 & L3 & WC & WI & WL) & MR & RG).
    pose proof (inflate_p_post ivar_ref ans s zc f U ZC) as PP.
    destruct (inflate_p ivar_ref ans s zc f) as [[s' z'] asked] eqn:EP. cbn [fst snd] in HA, HM', HXS, PP |- *.
    destruct PP as [U' _].
    assert (BLK : (WB = 0 <-> is_window_blk s' = None)).
    { destruct (Z.eq_dec WB 0) as [E|E].
      - pose proof (inflate_p_blk_none ans s zc f U ZC (proj1 WIFF E)) as X. rewrite EP in X. cbn [fst snd] in X.
        split; [intros _; exact (X HA) | intros _; exact E].
      - assert (Hb : is_window_blk s <> None) by (intros X; exact (E (proj2 WIFF X))).
        pose proof (inflate_p_blk ans s zc f U ZC Hb) as X. rewrite EP in X. cbn [fst snd] in X. destruct X as [_ X].
        split; [intros X0; exfalso; exact (E X0) | intros X0; exfalso; exact (X X0)]. }
    assert (WL' : WB <> 0 -> arr_len (is_window s') = 32768).
    { intros E. destruct U' as ((SR' & _ & WS') & _). destruct HXS as (_ & Hwb' & _).
      destruct (is_window_blk s') as [b|] eqn:EB; [| exfalso; exact (E (proj2 BLK eq_refl))].
      destruct WS' as [L' _]. rewrite L', Hwb'. reflexivity. }
    destruct HM' as [Rod' Sc' Lens' Work' Codes' Win' In' Out' Zs' _ _ _ _ _].
    cbn [cvF cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq] in *.
    split; [| split; [| split; [| exact BLK]]].
    -
      split; [| split; [| exact RG]].
      + split; [exact Sc'|]. split; [exact Lens'|]. split; [exact Work'|]. split; [exact Codes'|].
        split; [| split; [exact BLK | exact WL']].
        intros E. rewrite (WL' E). rewrite <- (WN1 E). apply Win'. rewrite (WN1 E). clear; lia.
      + destruct U' as ((SR' & _) & _). destruct SR' as (Smode' & _). exact Smode'.
    -
      unfold izs6 in Zs'. cbn [cv_ZP cv_S cv_I0 cv_P0 cv_fa cv_ff cv_opq] in Zs'.
      destruct Zs' as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
      unfold CCUR in HCC. cbn [cvF cv_NI cv_NO] in HCC. destruct HCC as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      unfold izs_cells, cell8, cell4, FL_MSGA. cbn [zstrm_of_icall zs_total_in zs_total_out zs_adler zs_msg]. unfold cell in *.
      rewrite Z.add_0_r in Z0.
      replace (n - ic_next_in cf) with (ic_avail_in cf) by (clear - Q3; lia).
      replace (NO - ic_next_out cf) with (ic_avail_out cf) by (clear - Q6; lia).
      repeat match goal with |- _ /\ _ => split end; assumption.
    -
      pose proof (arr_slice_length (ic_outbuf cf) 0 (ic_next_out cf)) as Hl.
      apply cells_holds; [clear - OUTP0; lia | rewrite Hl; clear - BO Hput; lia |].
      rewrite Hl. replace (Z.max 0 (ic_next_out cf)) with (ic_next_out cf) by (clear - Hput; lia).
      eapply cells_extf; [exact Out'|]. intros i Hi. cbn beta. symmetry. apply nth_arr_slice0. exact Hi.
  Qed.

  Theorem inflate_fl_R : forall ans,
    snd (inflate_p ivar_ref ans s zc f) = None ->
    let s' := fst (fst (inflate_p ivar_ref ans s zc f)) in let r := snd (fst (inflate_p ivar_ref ans s zc f)) in
    exists (regs' : bvmap 5 word) (mem' : word -> option byte) (nout : Z),
      0 <= nout <= NO
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - FL_IFR), FL_IFR) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, nout) :: wz (iblocks q))
      /\ msteps RSX (mkst regs (Z_to_bv 64 FL_A_INFLATE) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
      /\ getr regs' 10 = Z_to_bv 64 (zr_rc r) /\ getr regs' 2 = Z_to_bv 64 sp /\ rkeep regs regs' FL_KEEP
      /\ (~ RR (zr_rc r) ->
          nout = zlength (zr_output r) /\ 0 <= zr_consumed r <= n
          /\ FL_IREP mem' q s'
          /\ izs_cells FL_MSGA mem' strm (inp + zr_consumed r) (n - zr_consumed r) (outp + nout) (NO - nout) (zr_strm r) p fa ff
          /\ holds RSX mem' outp (zr_output r)
          /\ (WB = 0 <-> is_window_blk s' = None)).
  Proof.
    intros ans HA. cbv zeta.
    destruct SAFE as (U & ZC & LX4 & MSG & Hf) eqn:ESAFE. clear ESAFE.
    pose proof consts as (KA & KF & _).
    assert (HFA : 0 < cv_fa cvF) by (cbn; rewrite FA, KA; clear; lia).
    assert (HFF : 0 < cv_ff cvF) by (cbn; rewrite FF, KF; clear; lia).
    assert (HXS : LXS s) by exact LX4.
    pose proof (CALL6 inflate_call6 s zc mem ans eq_refl eq_refl eq_refl eq_refl U ZC HXS MSG HFA HFF CMEM_entry G2 G10 G11 HA) as X.
    cbv zeta in X. cbn [cvF cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq] in X.
    destruct X as (R' & M' & put' & RUN & A10 & A2 & Hkeep & A3 & A4 & Hput & Hg & HE & POST).
    exists R', M', put'.
    split; [exact Hput|].
    split; [exact (frame_of_call M' put' Hput Hg HE)|].
    split; [rewrite G1 in RUN; exact RUN|].
    split; [exact A10|]. split; [exact A2|].
    split.
    { intros rg Hrg. unfold FL_KEEP in Hrg. cbn [In] in Hrg.
      destruct Hrg as [<-|[<-|Hrg]]; [exact A3 | exact A4 |]. apply Hkeep. cbn [In]. clear - Hrg. tauto. }
    intros NRR. destruct (POST NRR) as (cf & Ezf & Eput & HM' & HXS' & MSG' & HCC).
    pose proof (post_of_CMEM ans M' cf HA HM' HXS' HCC ltac:(rewrite Eput; exact Hput)) as (IR' & ZS' & HLD' & BLK').
    rewrite Ezf. cbn [zret_of_icall zr_consumed zr_output zr_strm zr_rc]. rewrite Eput.
    unfold CCUR in HCC. cbn [cvF cv_NI cv_NO] in HCC. destruct HCC as (Q1 & Q2 & Q3 & _).
    split; [rewrite arr_slice_length; clear - Hput; lia|].
    split; [clear - Q1 Q2 Q3; lia|].
    rewrite Eput in ZS', HLD'.
    split; [exact IR'|]. split; [exact ZS'|]. split; [exact HLD' | exact BLK'].
  Qed.
  Lemma cvF_cvW : WB = 0 -> arr_len (is_window s) = 0 -> cvF = cvW regs sp q inp outp zc f 0 0.
  Proof. intros E1 E2. unfold cvF, cvW. rewrite FA, FF, E1, E2. reflexivity. Qed.

  Theorem inflate_fl_W : forall ans sz,
    snd (inflate_p ivar_ref ans s zc f) = Some sz ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte) (nout : Z),
      0 <= nout <= NO
      /\ frame_mod mem mem' ((Z_to_bv 64 (sp - FL_IFR), FL_IFR) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, nout) :: wz (iblocks q))
      /\ (sz = FL_WIN_N /\ WB = 0 /\
          msteps RSX (mkst regs (Z_to_bv 64 FL_A_INFLATE) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 FL_A_ZW) mem' (seg_rom RSX))
          /\ getr regs' 13 = Z_to_bv 64 fa /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 FL_WIN_N /\ getr regs' 12 = Z_to_bv 64 1
          /\ getr regs' 2 = Z_to_bv 64 (sp - FL_ZWD) /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
          /\ TWF regs regs' q inp outp s zc f mem').
  Proof.
    intros ans sz HA.
    destruct SAFE as (U & ZC & LX4 & MSG & Hf) eqn:ESAFE. clear ESAFE.
    pose proof consts as (KA & KF & KFRA & KTOP & KRO & KIS & KWN & KIFR & KZWD).
    assert (HFA : 0 < cv_fa cvF) by (cbn; rewrite FA, KA; clear; lia).
    assert (HFF : 0 < cv_ff cvF) by (cbn; rewrite FF, KF; clear; lia).
    assert (HXS : LXS s) by exact LX4.
    assert (HA' : snd (inflate_p ivar_ref ans s zc (cv_flush cvF)) <> None) by (cbn; rewrite HA; discriminate).
    pose proof (CALL6 inflate_callW6 s zc mem ans eq_refl eq_refl eq_refl eq_refl U ZC HXS MSG HFA HFF CMEM_entry G2 G10 G11 HA') as X.
    cbn [cv_flush cvF] in X.
    destruct X as (R' & M' & sx & cx & rx & EQL & LN & EWB & EWN & PI & HX & (SR & RIv & CIv & Hws0) & RUN & WS & Hg & HE).
    cbn [cvF cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq] in EWN, HE.
    pose proof wn_facts as [WN0 WN1].
    assert (EWB0 : WB = 0) by (destruct (Z.eq_dec WB 0) as [E|E]; [exact E | exfalso; pose proof (WN1 E) as X; rewrite EWN in X; discriminate X]).
    pose proof RIv as RIx. unfold RINV in RIx. cbn [cvF cv_NI cv_NO] in RIx. destruct RIx as (Rnx & Rhv0 & Rnh & Rpt0 & Rlf0 & Rpl & _).
    assert (Hput : 0 <= ir_put rx <= NO) by (clear - Rpt0 Rlf0 Rpl; lia).
    exists R', M', (ir_put rx).
    split; [exact Hput|].
    split.
    { apply (frame_of_call M' (ir_put rx) Hput Hg). intros x N1 N2 N3 N4 N5. apply HE; assumption. }
    pose proof HX as HXx. unfold LX in HXx. cbn [w_s w_c w_r] in HXx. destruct HXx as (Xwrap & Xwbits & _).
    assert (Hchk : inflateStateCheck s = false).
    { destruct U as ((SRs & _) & _). unfold SRNGq in SRs. destruct SRs as (Smode & _). destruct LX4 as (_ & _ & Llv & _).
      unfold inflateStateCheck. unfold live_mode, HEAD, MEM, SYNC, FLAGS, HCRC in *. apply Bool.orb_false_intro; apply Z.ltb_ge; clear - Smode Llv; lia. }
    split; [exact (inflate_p_asked ans s zc f sx cx rx sz Hchk EQL Xwbits HA)|].
    split; [exact EWB0|].
    split; [exact RUN|].
    destruct WS as (W13 & W10 & W11 & W12 & W2 & W8 & W9 & W18 & W19 & W20 & W24 & W25 & W3 & W4 & HM' & F8 & F16 & F24 & F32 & F40 & F48).
    cbn [cvF cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq] in W13, W10, W11, W12, W2, W8, W9, W18, W19, W20, W24, W25, W3, W4, F8, F16, F24, F32, F40, F48.
    unfold INF_FRAME in W2, F8, F16, F24, F32, F40, F48.
    split; [exact W13|]. split; [exact W10|]. split; [rewrite KWN; exact W11|]. split; [exact W12|].
    split; [rewrite KZWD; replace (sp - 272) with (sp - 224 - 48) by (clear; lia); exact W2|].
    split; [exact W3|]. split; [exact W4|].
    pose proof (cvF_cvW EWB0 EWN) as EV.
    exists sp, sx, cx, rx. cbv zeta. rewrite <- EV.
    split; [exact G2|]. split; [exact Hchk|]. split; [exact EQL|]. split; [exact LN|]. split; [exact EWB|].
    split; [exact HX|]. split; [exact SR|]. split; [exact RIv|]. split; [exact CIv|]. split; [exact Hws0|].
    split; [exact U|]. split; [exact ZC|]. split; [exact LX4|]. split; [exact MSG|].
    split; [exact EWB0|]. split; [exact (proj1 WIFF EWB0)|]. split; [exact EWN|].
    split; [exact ictx_cvF|]. split; [destruct IR as (_ & _ & RG); exact RG|].
    split.
    { unfold WSTR. cbn [cvF cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq]. unfold INF_FRAME.
      repeat match goal with |- _ /\ _ => split end; assumption. }
    split; [exact W3|]. split; [exact W4|].
    split; [exact (LMEMC_of _ _ _ HM')|].
    split; [unfold UWC, INF_FRAME; repeat match goal with |- _ /\ _ => split end; assumption|].
    pose proof (lm_map_f _ _ _ HM') as Mf. pose proof (lm_map_Z _ _ _ HM') as Mz. pose proof (lm_map_S _ _ _ HM') as Ms. pose proof (lm_map_P _ _ _ HM') as Mp.
    cbn [cvF cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq] in Mf, Mz, Ms, Mp.
    split; [exact Mf|]. split; [exact Mz|]. split; [exact Ms | exact Mp].
  Qed.
End INF.

Theorem twf_local : forall (R0 RW : bvmap 5 word) q inp outp s zc f (M M' : word -> option byte),
      let sp := bv_unsigned (getr R0 2) in
      (forall a, (sp - FL_ZWD <= bv_unsigned a < sp \/ ip_p q <= bv_unsigned a < ip_p q + FL_ISTATE_N \/
                  ip_strm q <= bv_unsigned a < ip_strm q + 112 \/ outp <= bv_unsigned a < outp + zc_avail_out zc \/
                  inp <= bv_unsigned a < inp + zlength (zc_input zc)) -> M' a = M a) ->
      (forall a, sp - FL_FRA <= bv_unsigned a < sp - FL_ZWD -> M' a <> None) ->
      TWF R0 RW q inp outp s zc f M -> TWF R0 RW q inp outp s zc f M'.
Proof.
  intros R0 RW q inp outp s zc f M M'. cbv zeta. intros HE HB HT.
  destruct HT as (sp & sx & cx & rx & T). cbv zeta in T.
  destruct T as (Gsp & Hchk & EQL & LN & EWB & HX & SR & RIv & CIv & Hws0 & U & ZC & HXS & MSG & HW0 & Hblk & Hwl & C & RG & WR & W3 & W4 & HMC & HUW & Mf & Mz & Ms & Mp).
  exists sp, sx, cx, rx. cbv zeta.
  rewrite Gsp in HE, HB. rewrite u_zw_small in HE by (pose proof (ic_sp _ C) as Csp; cbn [cvW cv_sp] in Csp; unfold IMG6_TOP, INF_FRAME, INF_SCRATCH in Csp; clear - Csp; lia).
  rewrite u_zw_small in HB by (pose proof (ic_sp _ C) as Csp; cbn [cvW cv_sp] in Csp; unfold IMG6_TOP, INF_FRAME, INF_SCRATCH in Csp; clear - Csp; lia).
  pose proof (ic_sp _ C) as Csp. pose proof (ic_S _ C) as CS. pose proof (ic_ZP _ C) as CZP. pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0.
  cbn [cvW cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq] in Csp, CS, CZP, CI0, CP0.
  unfold IMG6_TOP, INF_FRAME, INF_SCRATCH, FL_ZWD, FL_FRA, FL_ISTATE_N in *.
  pose proof RIv as RIx. unfold RINV in RIx. destruct RIx as (Rnx & Rhv0 & Rnh & Rpt0 & Rlf0 & Rpl & _).
  assert (HEz : forall z, (sp - 272 <= z < sp) \/ (ip_p q <= z < ip_p q + 7176) \/ (ip_strm q <= z < ip_strm q + 112)
                          \/ (outp <= z < outp + zc_avail_out zc) \/ (inp <= z < inp + zlength (zc_input zc)) ->
                          0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = M (Z_to_bv 64 z)).
  { intros z Hz Bz. apply HE. change (Z_to_bv 64 z) with (zw z). rewrite u_zw_small by exact Bz. exact Hz. }
  repeat (split; [assumption|]).
  split; [| split; [| split; [| split; [| split]]]].
  -
    unfold LMEMC in *. cbn [cvW cv_sp cv_R0 cv_ZP cv_S cv_I0 cv_P0 cv_WB cv_NI cv_NO cv_WN cv_flush cv_TOT0 cv_fa cv_ff cv_opq w_s w_c w_r] in HMC |- *.
    unfold INF_FRAME in *.
    destruct HMC as (Lsc & Llens & Lwork & Lcodes & Lwin & Lin & Lout & Lzs & Lfr & Loutc).
    split; [apply (is6_scalars_local M M' _ _ _ Lsc); [clear - CS; lia | clear - CS; lia | intros z Hz; apply HEz; clear - Hz CS; lia]|].
    split; [apply (cells_local M M' _ _ _ _ _ Llens); [cbn; clear; lia | clear - CS; lia | clear - CS; lia | intros z Hz; apply HEz; clear - Hz CS; lia]|].
    split; [apply (cells_local M M' _ _ _ _ _ Lwork); [cbn; clear; lia | clear - CS; lia | clear - CS; lia | intros z Hz; apply HEz; clear - Hz CS; lia]|].
    split; [apply (cells_local M M' _ _ _ _ _ Lcodes); [cbn; clear; lia | clear - CS; lia | clear - CS; lia | intros z Hz; apply HEz; clear - Hz CS; lia]|].
    split; [intros X; exfalso; apply X; reflexivity|].
    split; [apply (cells_local M M' _ _ _ _ _ Lin); [cbn; clear; lia | clear - CI0; lia | clear - CI0; lia | intros z Hz; apply HEz; clear - Hz CI0; lia]|].
    split; [apply (cells_local M M' _ _ _ _ _ Lout); [cbn; clear; lia | clear - CP0; lia | clear - CP0 Rpt0 Rpl Rlf0; lia | intros z Hz; apply HEz; clear - Hz CP0 Rpt0 Rpl Rlf0; lia]|].
    split; [apply (izs6_local _ _ M M' Lzs); cbn [cvW cv_ZP]; [clear - CZP; lia | clear - CZP; lia | intros z Hz; apply HEz; clear - Hz CZP; lia]|].
    split; [apply (iframe6_local _ M M' Lfr); cbn [cvW cv_sp]; [clear - Csp; lia | clear - Csp; lia | intros z Hz; apply HEz; clear - Hz Csp; lia]|].
    apply (cell_local M M' _ _ _ Loutc); [clear - Csp; lia | cbn; clear - Csp; lia | intros z Hz; apply HEz; cbn in Hz; clear - Hz Csp; lia].
  -
    unfold UWC, INF_FRAME in *. destruct HUW as (U1 & U2 & U3 & U4 & U5 & U6).
    repeat match goal with |- _ /\ _ => split end;
      lazymatch goal with |- cell _ _ ?a _ _ =>
        match goal with CC : cell _ M a _ _ |- _ => apply (cell_local M M' _ _ _ CC); [clear - Csp; lia | cbn; clear - Csp; lia | intros z Hz; apply HEz; cbn in Hz; clear - Hz Csp; lia] end
      end.
  - intros x Hx. pose proof (u64_range x) as Bx.
    destruct (Z_lt_le_dec (bv_unsigned x) (sp - 272)) as [LT|GE].
    + apply HB. clear - Hx LT. lia.
    + rewrite (HE x) by (left; clear - Hx GE; lia). exact (Mf x Hx).
  - intros x Hx. rewrite (HE x) by (right; right; left; exact Hx). exact (Mz x Hx).
  - intros x Hx. rewrite (HE x) by (right; left; exact Hx). exact (Ms x Hx).
  - intros x Hx. rewrite (HE x) by (right; right; right; left; exact Hx). exact (Mp x Hx).
Qed.
End FXG.
