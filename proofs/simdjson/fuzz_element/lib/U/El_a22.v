(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr Bytes FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjLeaves SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_tables Sj_stage2_iface Atp_defs Atp_h_defs El_defs Atp_kitu El_throw_site El_acc_3c9d4 El_acc_3cb20 El_acc_3cbfc El_acc_3ccd8.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition EL_CJTAB : Z := 0x141a8.
Definition CJT_TAB : list Z := [169024; 169584; 169284; 169380; 169176; 169680; 169712; 169476].
Definition cjt (i : Z) : Z := nth (Z.to_nat i) CJT_TAB 0.
Definition CJT_WORDS : list word := map (Z_to_bv 64) CJT_TAB.

Lemma cjt_image : ro_bytes_b usegs EL_CJTAB (u32s CJT_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cjt_at : forall m, mem_inv usegs m -> bytes_at usegs m EL_CJTAB (u32s CJT_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold EL_CJTAB; lia | rewrite u32s_length; unfold EL_CJTAB, CJT_WORDS; rewrite length_map; cbn; lia |].
  apply ro_bytes_b_sound. exact cjt_image.
Qed.
Lemma cjt_read : forall (m : word -> option byte) i a, mem_inv usegs m -> 0 <= i < 8 -> a = wa (EL_CJTAB + 4 * i) ->
  ov_read_bytes usegs m a 4 = Some (le4 (Z_to_bv 64 (cjt i))).
Proof.
  intros m i a MI Hi ->. eapply (u32ro_read m EL_CJTAB CJT_WORDS i); [apply cjt_at; exact MI| | lia | reflexivity].
  unfold CJT_WORDS, cjt. rewrite nth_error_map. rewrite (nth_error_nth' CJT_TAB 0); [reflexivity|].
  change (length CJT_TAB) with 8%nat. lia.
Qed.
Definition cast_entry (sel : Z) : Z :=
  if sel =? 0 then 0x3d5e8 else if sel =? 1 then 0x3d818 else if sel =? 2 then 0x3d6ec else if sel =? 3 then 0x3d74c
  else if sel =? 4 then 0x3d680 else if sel =? 5 then 0x3d878 else if sel =? 6 then 0x3d898 else 0x3d7ac.
Lemma cjt_entry : forall sel, 0 <= sel < 8 -> EL_CJTAB + cjt sel = cast_entry sel /\ 0 <= cjt sel < 2^31.
Proof.
  intros sel H.
  assert (F : forallb (fun i => (EL_CJTAB + cjt i =? cast_entry i) && (0 <=? cjt i) && (cjt i <? 2 ^ 31)) (map Z.of_nat (seq 0 8)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. specialize (F sel ltac:(apply in_map_iff; exists (Z.to_nat sel); split; [lia|]; apply in_seq; lia)).
  apply andb_true_iff in F. destruct F as [F F3]. apply andb_true_iff in F. destruct F as [F1 F2].
  apply Z.eqb_eq in F1. apply Z.leb_le in F2. apply Z.ltb_lt in F3. lia.
Qed.

Definition cast_site (sel : Z) : Z :=
  if sel =? 0 then 0x3d644 else if sel =? 1 then 0x3d840 else if sel =? 2 then 0x3d714 else if sel =? 3 then 0x3d774
  else if sel =? 4 then 0x3d6a8 else if sel =? 5 then 0x3ef04 else if sel =? 6 then 0x3d8d8 else 0x3d7dc.

Definition cast_ok (sel w v : Z) : bool :=
  if sel =? 0 then (w =? tword t_false 0) || (w =? tword t_true 0)
  else if sel =? 1 then (w =? tword t_dbl 0) || (w =? tword t_u64 0) || (w =? tword t_i64 0)
  else if sel =? 2 then (w =? tword t_u64 0) || ((w =? tword t_i64 0) && (v <? 2^63))
  else if sel =? 3 then (w =? tword t_i64 0) || ((w =? tword t_u64 0) && (v <? 2^63))
  else if (sel =? 4) || (sel =? 5) then ttype w =? t_str
  else if sel =? 6 then ttype w =? t_arr
  else ttype w =? t_obj.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Lemma cast_ok_throws : forall E sel, aenv_ok E -> 0 <= sel < 8 -> cast_ok sel (ae_T E 1) (ae_T E 2) = negb (el_throws 22 sel (ttype (ae_T E 1)) (ae_T E 2)).
Proof.
  intros E sel OK SEL. pose proof (el_root_elem E OK) as [EL NR].
  pose proof (el_elem_cases E _ _ _ OK EL) as CS. cbv zeta in CS.
  unfold cast_ok, el_throws, t_false, t_true, t_dbl, t_u64, t_i64, t_str, t_arr, t_obj. change (22 =? 22) with true. cbn [negb].
  assert (SPLIT : forall w : Z,
    (w = tword 116 0 \/ w = tword 102 0 \/ w = tword 110 0 \/ w = tword 108 0 \/ w = tword 117 0 \/ w = tword 100 0
     \/ (exists o, w = tword 34 o /\ 0 <= o < 2^56) \/ (exists e cv, 0 <= e + 1 < 2^32 /\ 0 <= cv <= CNT_MAX /\ (w = cword 91 (e + 1) cv \/ w = cword 123 (e + 1) cv))) ->
    forall v, 0 <= sel < 8 ->
    (if sel =? 0 then (w =? tword 102 0) || (w =? tword 116 0)
     else if sel =? 1 then (w =? tword 100 0) || (w =? tword 117 0) || (w =? tword 108 0)
     else if sel =? 2 then (w =? tword 117 0) || (w =? tword 108 0) && (v <? 2 ^ 63)
     else if sel =? 3 then (w =? tword 108 0) || (w =? tword 117 0) && (v <? 2 ^ 63)
     else if (sel =? 4) || (sel =? 5) then ttype w =? 34 else if sel =? 6 then ttype w =? 91 else ttype w =? 123)
    = negb (if sel =? 0 then negb ((ttype w =? 116) || (ttype w =? 102))
            else if sel =? 1 then negb ((ttype w =? 100) || (ttype w =? 117) || (ttype w =? 108))
            else if sel =? 2 then (ttype w =? 108) && (2 ^ 63 <=? v) || negb ((ttype w =? 117) || (ttype w =? 108))
            else if sel =? 3 then (ttype w =? 117) && (2 ^ 63 <=? v) || negb ((ttype w =? 108) || (ttype w =? 117))
            else if (sel =? 4) || (sel =? 5) then negb (ttype w =? 34) else if sel =? 6 then negb (ttype w =? 91) else negb (ttype w =? 123))).
  { intros w HW v Hs.
    assert (EQT : forall t t', (tword t 0 =? tword t' 0) = (t =? t')).
    { intros t t'. destruct (Z.eqb_spec t t') as [->|NE]; [apply Z.eqb_refl| apply (proj2 (Z.eqb_neq _ _)); unfold tword; lia]. }
    assert (W : exists c, ttype w = c /\ ((w = tword c 0 /\ (c = 116 \/ c = 102 \/ c = 110 \/ c = 108 \/ c = 117 \/ c = 100))
                                       \/ ((c = 34 \/ c = 91 \/ c = 123) /\ forall t, 0 <= t < 256 -> t <> c -> (w =? tword t 0) = false))).
    { unfold CNT_MAX in HW.
      destruct HW as [-> |[-> |[-> |[-> |[-> |[-> |[(o & -> & Ho)|(e & cv & He & Hcv & [-> | ->])]]]]]]];
        try (eexists; split; [apply ttype_tword; lia| left; split; [reflexivity| lia]]).
      - exists 34. split; [apply ttype_tword; lia| right; split; [lia|]]. intros t Ht NE. apply (proj2 (Z.eqb_neq _ _)). unfold tword. lia.
      - exists 91. split; [apply ttype_cword; unfold CNT_MAX; lia| right; split; [lia|]]. intros t Ht NE. apply (proj2 (Z.eqb_neq _ _)). unfold cword, tword. lia.
      - exists 123. split; [apply ttype_cword; unfold CNT_MAX; lia| right; split; [lia|]]. intros t Ht NE. apply (proj2 (Z.eqb_neq _ _)). unfold cword, tword. lia. }
    destruct W as (c & TC & [[-> HC]|[HC NEQ]]).
    - rewrite !EQT, !(ttype_tword c 0) by lia.
      destruct (v <? 2^63) eqn:K1; destruct (2^63 <=? v) eqn:K2;
        first [apply Z.ltb_lt in K1 | apply Z.ltb_ge in K1]; first [apply Z.leb_le in K2 | apply Z.leb_gt in K2]; try lia;
        destruct HC as [-> |[-> |[-> |[-> |[-> | ->]]]]];
        assert (CASES : sel = 0 \/ sel = 1 \/ sel = 2 \/ sel = 3 \/ sel = 4 \/ sel = 5 \/ sel = 6 \/ sel = 7) by lia;
        destruct CASES as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; reflexivity.
    - rewrite TC. rewrite !NEQ by lia.
      destruct HC as [-> |[-> | ->]];
        assert (CASES : sel = 0 \/ sel = 1 \/ sel = 2 \/ sel = 3 \/ sel = 4 \/ sel = 5 \/ sel = 6 \/ sel = 7) by lia;
        destruct CASES as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; reflexivity. }
  apply SPLIT; [| exact SEL].
  destruct CS as [[_ [H|[H|H]]]|[[_ [H|[H|H]]]|[(_ & _ & o & H & Ho)|(e & cv & He & Hj & Hcv & [H|H])]]]; unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_arr, t_obj in H.
  - left; exact H. - right; left; exact H. - right; right; left; exact H.
  - do 3 right; left; exact H. - do 4 right; left; exact H. - do 5 right; left; exact H.
  - do 6 right; left. exists o. auto.
  - do 7 right. exists e, cv. split; [lia|]. split; [exact Hcv|]. left; exact H.
  - do 7 right. exists e, cv. split; [lia|]. split; [exact Hcv|]. right; exact H.
Qed.

Section A22.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Definition cast_post (sel : Z) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' =>
      (exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
         ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc' None m' (seg_rom usegs)
         /\ munch [(q - 96, q)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q /\ frm0 fc')
      \/ (exists (x1 t0 t1 t2 xs0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
         ms' = MS (mkR x1 (Z_to_bv 64 (q - 16 - cast_D sel)) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (Z_to_bv 64 (cast_site sel)) fc' None m' (seg_rom usegs)
         /\ rw_cells usegs m' (q + -16) [C8 s0; C8 ra]
         /\ munch [(q - 96, q)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (q + -16)
         /\ cast_XP sel m' (q + -16) /\ frm0 fc'
         /\ (sel = 2 \/ sel = 3 -> bv_unsigned xs0 < 64)).

  Ltac fin_ret := apply evt_done; left; do 15 eexists; do 3 eexists; split; [atp_st_eq_goal|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption| eassumption].
  Ltac fin_site := apply evt_done; right; unfold cast_D, cast_site, cast_XP, xp_none; cbn [Z.eqb Pos.eqb]; do 17 eexists; do 3 eexists; split; [atp_st_eq_goal|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [first [exact I | eassumption]|]; split; [eassumption|]; intros HS; first [exfalso; lia | rewrite unsigned_lit by lia; lia].

  Lemma cast_reget : forall s m mX node lo hi,
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m ->
    munch [(lo, hi)] m mX -> wmono usegs m mX -> alloc_ceiling <= lo -> hi <= node -> hi <= ae_DOC E ->
    AINV E mX /\ el_root E mX node /\ RHEAP s (ae_LB E) mX.
  Proof.
    intros s m mX node lo hi AI RT HP MU WM L1 L2 L3. split; [| split].
    - eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
      + intros a Ha. pose proof (blocks_below _ _ _ a HP Ha). cbn [outside]. lia.
      + intros a Ha. cbn [outside]. lia.
    - unfold el_root in *. eapply rw_cells_transport; [exact RT| exact MU| exact WM| cbn; lia].
    - eapply LH_frame; [exact HP| exact MU| exact WM|]. constructor; [apply W_ok_stack; lia| constructor].
  Qed.

  Lemma cast_word_small : forall (w : word) k, bv_unsigned w < k -> exists e, w = Z_to_bv 64 e /\ 0 <= e < k.
  Proof.
    intros w k H. exists (bv_unsigned w). split; [symmetry; apply Z_to_bv_bv_unsigned|].
    pose proof (bv_unsigned_in_range 64 w). lia.
  Qed.

  Ltac s5_wk := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_lia
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let b := eval vm_compute in ((pc =? 0x3ee74) || (pc =? 0x3e064) || (pc =? 0x3ef04))%bool in lazymatch b with false => idtac end;
        astep; repeat (match goal with H : ?x mod 8 = 0 |- context [Z.land ?x 7] => rewrite (land7_mod8 x ltac:(lia) H) end)
    end).
  Ltac s5_tixc := lazymatch goal with |- evt _ _ (MS _ ?F _ ?fc _ ?mx _) =>
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx (ae_DOC E) (ae_TAPE E) _ _ [C8 (Z_to_bv 64 (ae_SBUF E))]);
    [eassumption| lia| lia| lia| lia| assumption| lia| lia| reflexivity| lia| reflexivity|]; intros ? ? ? ?; try rewrite Z.mul_1_r end.
  Ltac s5_tb_at TAPEB MU WM TIR := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let TB := fresh "TB" in
    assert (TB : bytes_at usegs mx (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))))
      by (eapply bytes_at_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact TAPEB|]; rewrite u64s_length, length_map; intros a Ha; cbn [outside]; lia);
    let R1 := fresh "RDT" in let R2 := fresh "RDT" in let R3 := fresh "RDB" in
    pose proof (tape_read mx (ae_TAPE E) (ae_tws E) 1 TB ltac:(lia)) as R1;
    pose proof (tape_read mx (ae_TAPE E) (ae_tws E) 2 TB ltac:(lia)) as R2;
    pose proof (tape_read_type mx (ae_TAPE E) (ae_tws E) 1 TB ltac:(lia) TIR) as R3;
    rewrite Z.mul_1_r in R1, R3 end.

  Lemma cast_sel5 : forall (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m m1 : mem) (q node : Z) (j1 j2 j3 j4 : list byte),
    bytes_at usegs m (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))) ->
    rw_cells usegs m1 (ae_DOC E) [C8 (Z_to_bv 64 (ae_TAPE E)); C8 (Z_to_bv 64 (ae_SBUF E))] ->
    rw_cells usegs m1 node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 1)] ->
    mem_inv usegs m1 -> frm0 fc ->
    ae_lo E <= q - 96 -> q <= ae_B E -> q mod 16 = 0 -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E -> node mod 8 = 0 ->
    0 < ae_TAPE E /\ ae_TAPE E + 8 * ae_n E <= alloc_ceiling ->
    0 < ae_SBUF E /\ ae_SBUF E + ae_sn E <= alloc_ceiling ->
    ae_TAPE E mod 8 = 0 -> ae_DOC E mod 8 = 0 -> ae_DOC E + 24 <= ae_B E -> alloc_ceiling <= ae_lo E -> ae_B E < 2 ^ 63 ->
    2 < ae_n E < 2 ^ 32 -> 0 <= ae_T E 1 < 2 ^ 64 -> 0 <= ttype (ae_T E 1) < 256 ->
    munch [(q - 96, q)] m m1 -> wmono usegs m m1 -> stk usegs m1 (ae_lo E) (q + -48) ->
    rw_cells usegs m1 (q + -48) [CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; C8 s0; C8 ra] ->
    evt usegs (cast_post 5 ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (ae_lo E) m)
      (MS (mkR ra (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 node) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3d878) fc None m1 (seg_rom usegs)).
  Proof.
    intros until j4. intros TAPEB DOCC1 ROOT MI FRM LOQ QB Q16 N0 N1 QDOC N8 TR SR T8 D8 DB CEIL B63 NR TIR TTR MU WM ST FR.
    pose proof alloc_ceiling_range as CEIL_RANGE__.
    s5_wk. release_frame FR ST q.
    step. carve_frame 16%nat ST. apply (rw_cells_split_CB usegs _ _ [] 16 _ [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    hstep. hstep. s5_tb_at TAPEB MU WM TIR. s5_wk. s5_tixc. s5_wk.
    if_cases K1; zify_cond K1; [s5_wk; fin_site|].
    assert (LV : 0 <= Z.land (ae_T E 1) 72057594037927935 < 2 ^ 56) by (change 72057594037927935 with (Z.ones 56); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    s5_wk. s5_tixc. s5_wk.
    release_frame FR ST q. fin_ret.
  Qed.

  Ltac s4_wk := repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_lia
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let b := eval vm_compute in ((pc =? 254052) || (pc =? 248276) || (pc =? 248828) || (pc =? 248608) || (pc =? 249048) || (pc =? 257652) || (pc =? 251460) || (pc =? 251968) || (pc =? 251668) || (pc =? 251764) || (pc =? 251560) || (pc =? 257796) || (pc =? 252120) || (pc =? 251868))%bool in lazymatch b with false => idtac end;
        astep; repeat (match goal with H : ?x mod 8 = 0 |- context [Z.land ?x 7] => rewrite (land7_mod8 x ltac:(lia) H) end)
    end).
  Lemma cast_sel4 : forall (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m m1 : mem) (s : PState) (q node : Z) (j0 j1 j2 j3 : list byte),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m ->
    munch [(q - 96, q)] m m1 -> wmono usegs m m1 -> mem_inv usegs m1 -> frm0 fc ->
    stk usegs m1 (ae_lo E) (q + -48) ->
    rw_cells usegs m1 (q + -48) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; C8 s0; C8 ra] ->
    ae_lo E <= q - 96 -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E -> node mod 8 = 0 ->
    evt usegs (cast_post 4 ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (ae_lo E) m)
      (MS (mkR ra (Z_to_bv 64 (q + -48)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 node) s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3d680) fc None m1 (seg_rom usegs)).
  Proof.
    intros until j3. intros AI RT HP MU WM MI FRM ST FR LOQ QN NB QD N8.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB] [D8 T8]].
    unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    apply (rw_cells_merge usegs _ _ [_] [_; _; _] _) in FR. cbn [cells_size csize Nat.add app] in FR.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [FR0 FR]. cbn [cells_size csize Nat.add] in FR.
    replace (q + -48 + Z.of_nat 8) with (q + -40) in FR by lia.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [SL FR]. cbn [cells_size csize Nat.add] in FR.
    replace (q + -40 + Z.of_nat 24) with (q + -16) in FR by lia.
    s4_wk.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (cast_reget s m mx node (q - 96) q AI RT HP MU WM ltac:(lia) ltac:(lia) ltac:(lia)) as (AI1 & RT1 & HP1) end.
    eapply evt_cut; [eapply (acc_3c9d4_spec E OK); [exact AI1| exact RT1| exact HP1| exact MI| exact FRM| exact ST| first [eassumption | lia] ..]|].
    clear AI1 RT1 HP1 AI RT HP.
    intros ms' PO. hnf in PO.
    destruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & RES).
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) => rewrite (ret_pc_even x) by lia end.
    clear MI FRM ST. transport_after_call usegs m1 m2 MU2 WM2. clear MU2 WM2. rename ST2 into ST, MI2 into MI, FC2 into FRM.
    destruct RES as (k1 & k2 & err & RS & ER & _).
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in RS. destruct RS as [RS0 RS]. cbn [cells_size csize Nat.add] in RS.
    replace (q + -40 + Z.of_nat 16) with (q + -24) in RS by lia.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in RS. destruct RS as [RS1 RS2]. cbn [cells_size csize Nat.add] in RS2.
    replace (q + -24 + Z.of_nat 4) with (q + -20) in RS2 by lia.
    s4_wk. if_cases K1; zify_cond K1.
    - s4_wk.
      release_frame FR0 ST (q + -40). release_frame RS0 ST (q + -24). release_frame RS1 ST (q + -20).
      release_frame RS2 ST (q + -16). release_frame FR ST q.
      fin_ret.
    - s4_wk. pose proof RS1 as XE.
      release_frame FR0 ST (q + -40). release_frame RS0 ST (q + -24). release_frame RS1 ST (q + -20).
      release_frame RS2 ST (q + -16).
      apply evt_done; right; unfold cast_D, cast_site, cast_XP, xp_err; cbn [Z.eqb Pos.eqb].
      do 17 eexists; do 3 eexists. split; [atp_st_eq_goal|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [exists err; split; [lia|]; replace (q + -16 - 8) with (q + -24) by lia; exact XE|].
      split; [eassumption|]. intros HS. exfalso. lia.
  Qed.

  Lemma cast_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node lo SELA sel : Z) (jsel : list byte),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv usegs m -> frm0 fc ->
    stk usegs m lo q -> ae_lo E = lo -> lo <= q - 96 -> q <= ae_B E -> q mod 16 = 0 -> q <= node -> node + 16 <= ae_B E ->
    rw_cells usegs m SELA [CB 4 jsel; C4 (Z_to_bv 64 sel)] -> 0 <= sel < 8 -> q <= SELA -> SELA + 8 <= ae_B E -> q <= ae_DOC E -> node mod 8 = 0 ->
    evt usegs (cast_post sel ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (SELA + 4)) (Z_to_bv 64 node) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_CAST) fc None m (seg_rom usegs)).
  Proof.
    intros until jsel. intros AI ROOT HEAP MI FRM ST LOLO LOQ QB Q16 N0 N1 XSEL SEL SA0 SA1 QDOC N8.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB] [D8 T8]].
    assert (LO0 : 0 <= ae_lo E) by (unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    pose proof (el_root_elem E OK) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof AI as AI0. pose proof ROOT as ROOT0. pose proof HEAP as HEAP0. hide AI0. hide ROOT0. hide HEAP0.
    destruct AI as (TAPEB & SBUFB & PTRB & DOCC). unfold el_root in ROOT. unfold EL_CAST.
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    subst lo.
    pose proof (munch_refl [(q - 96, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.

    Ltac wk := repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_lia
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let b := eval vm_compute in ((pc =? 254052) || (pc =? 248276) || (pc =? 248828) || (pc =? 248608) || (pc =? 249048) || (pc =? 257652) || (pc =? 251460) || (pc =? 251968) || (pc =? 251668) || (pc =? 251764) || (pc =? 251560) || (pc =? 257796) || (pc =? 252120) || (pc =? 251868))%bool in lazymatch b with false => idtac end;
          astep; repeat (match goal with H : ?x mod 8 = 0 |- context [Z.land ?x 7] => rewrite (land7_mod8 x ltac:(lia) H) end)
      end).
    Ltac tixc := lazymatch goal with |- evt _ _ (MS _ ?F _ ?fc _ ?mx _) =>
      eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx (ae_DOC E) (ae_TAPE E) _ _ [C8 (Z_to_bv 64 (ae_SBUF E))]);
      [eassumption| lia| lia| lia| lia| assumption| lia| lia| reflexivity| lia| reflexivity|]; intros ? ? ? ?; try rewrite Z.mul_1_r end.
    Ltac do_ret FR ST q := wk; release_frame FR ST q; fin_ret.
    Ltac site FR ST q := apply (proj1 (rw_cells_app _ _ _ [_; _; _; _] _)) in FR; destruct FR as [FR0 FR]; cbn [cells_size csize Nat.add] in FR;
      replace (q + -48 + Z.of_nat 32) with (q + -16) in FR by lia; release_frame FR0 ST (q + -16); fin_site.
    Ltac retfix := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) => rewrite (ret_pc_even x) by lia end.
    Ltac callq SPEC AI0 ROOT0 HEAP0 MU WM FRM ST MI := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        unhide AI0; unhide ROOT0; unhide HEAP0;
        let AI1 := fresh "AI1" in let RT1 := fresh "RT1" in let HP1 := fresh "HP1" in
        lazymatch type of HEAP0 with RHEAP ?s0 _ ?m0 =>
        lazymatch type of ROOT0 with el_root _ _ ?nd =>
        lazymatch type of MU with munch [(?l0, ?h0)] _ _ =>
        destruct (cast_reget s0 m0 mx nd l0 h0 AI0 ROOT0 HEAP0 MU WM ltac:(lia) ltac:(lia) ltac:(lia)) as (AI1 & RT1 & HP1) end end end;
        eapply evt_cut; [eapply (SPEC E OK); [exact AI1| exact RT1| exact HP1| exact MI| exact FRM| exact ST| first [eassumption | lia] ..]|];
        clear AI1 RT1 HP1 AI0 ROOT0 HEAP0;
        let ms' := fresh "ms'" in let PO := fresh "PO" in intros ms' PO; hnf in PO;
        let m2 := fresh "m" in let MU2 := fresh "MU" in let WM2 := fresh "WM" in let MI2 := fresh "MI" in let ST2 := fresh "ST" in let FC2 := fresh "FRM" in
        destruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & RES);
        retfix; clear MI FRM ST; transport_after_call usegs mx m2 MU2 WM2; clear MU2 WM2; rename ST2 into ST, MI2 into MI, FC2 into FRM end.
    Ltac tb_at TAPEB MU WM TIR := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let TB := fresh "TB" in
      assert (TB : bytes_at usegs mx (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))))
        by (unhide TAPEB; eapply bytes_at_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact TAPEB|]; rewrite u64s_length, length_map; intros a Ha; cbn [outside]; lia);
      let R1 := fresh "RDT" in let R2 := fresh "RDT" in let R3 := fresh "RDB" in
      pose proof (tape_read mx (ae_TAPE E) (ae_tws E) 1 TB ltac:(lia)) as R1;
      pose proof (tape_read mx (ae_TAPE E) (ae_tws E) 2 TB ltac:(lia)) as R2;
      pose proof (tape_read_type mx (ae_TAPE E) (ae_tws E) 1 TB ltac:(lia) TIR) as R3;
      rewrite Z.mul_1_r in R1, R3 end.

    hide TAPEB. clear SBUFB PTRB.
    step. carve_frame 48%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 48 junk [] [8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    hstep. hstep. hstep. hstep.

    rewrite (a_sx32_small sel) by lia.
    step. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|]. clear KB.
    astep. astep. astep. astep. astep.
    pose proof (cjt_entry sel SEL) as [CJE CJR].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (cjt_read mx sel (wa (Z.shiftl sel 2 + EL_CJTAB)) ltac:(assumption) SEL ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RJ end.
    unfold EL_CJTAB in RJ.
    astep. astep. step.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) => replace x with (cast_entry sel) by (unfold EL_CJTAB in CJE; lia) end.
    clear RJ CJE CJR.
    tb_at TAPEB MU WM TIR.
    lazymatch goal with H : rw_cells usegs _ (ae_DOC E) _ |- _ => rename H into DOCC1 end.
    Ltac arm_entry v pc := replace (cast_entry v) with pc by reflexivity; rewrite (ret_pc_even pc) by lia.
    assert (CASES : sel = 0 \/ sel = 1 \/ sel = 2 \/ sel = 3 \/ sel = 4 \/ sel = 5 \/ sel = 6 \/ sel = 7) by lia.
    destruct CASES as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]].

    -
      arm_entry 0 0x3d5e8. wk. tixc.
      wk. if_cases K1; zify_cond K1; [do_ret FR ST q|].
      wk. tixc.
      wk. if_cases K2; zify_cond K2; [do_ret FR ST q|].
      wk. site FR ST q.
    -
      arm_entry 1 0x3d818. wk. callq acc_3ccd8_spec AI0 ROOT0 HEAP0 MU WM FRM ST MI.
      destruct RES as [A0R A0E]. destruct (cast_word_small ya0 64 A0R) as (e1 & -> & E1). clear A0R. rewrite unsigned_lit in A0E by lia.
      wk. if_cases K1; zify_cond K1; [do_ret FR ST q|].
      wk. site FR ST q.
    -
      arm_entry 2 0x3d6ec. wk. callq acc_3cbfc_spec AI0 ROOT0 HEAP0 MU WM FRM ST MI. 
      destruct RES as [A1R A1E]. destruct (cast_word_small ya1 64 A1R) as (e1 & -> & E1). clear A1R. rewrite unsigned_lit in A1E by lia.
      wk. if_cases K1; zify_cond K1; [do_ret FR ST q|].
      wk. site FR ST q.
    -
      arm_entry 3 0x3d74c. wk. callq acc_3cb20_spec AI0 ROOT0 HEAP0 MU WM FRM ST MI. 
      destruct RES as [A1R A1E]. destruct (cast_word_small ya1 64 A1R) as (e1 & -> & E1). clear A1R. rewrite unsigned_lit in A1E by lia.
      wk. if_cases K1; zify_cond K1; [do_ret FR ST q|].
      wk. site FR ST q.
    - arm_entry 4 0x3d680. unhide AI0. unhide ROOT0. unhide HEAP0. eapply cast_sel4; eassumption.
    - arm_entry 5 0x3d878. eapply cast_sel5; eassumption.
    -
      arm_entry 6 0x3d898. wk. tixc. wk. if_cases K1; zify_cond K1; [wk; site FR ST q|].
      do_ret FR ST q.
    -
      arm_entry 7 0x3d7ac. wk. tixc. wk. if_cases K1; zify_cond K1; [do_ret FR ST q|].
      wk. site FR ST q.
  Qed.
End A22.
End WithCeiling0.
