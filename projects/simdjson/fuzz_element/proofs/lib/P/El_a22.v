(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr Bytes FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjLeaves SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit Sj_stage2_defs Sj_tables Sj_stage2_iface Atp_defs Atp_h_defs El_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition EL_CJTAB : Z := 0x14128.
Definition CJT_TAB : list Z := [163828; 164224; 164016; 164080; 163936; 164332; 164412; 164144].
Definition cjt (i : Z) : Z := nth (Z.to_nat i) CJT_TAB 0.
Definition CJT_WORDS : list word := map (Z_to_bv 64) CJT_TAB.

Lemma cjt_image : ro_bytes_b psegs EL_CJTAB (u32s CJT_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cjt_at : forall m, mem_inv psegs m -> bytes_at psegs m EL_CJTAB (u32s CJT_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold EL_CJTAB; lia | rewrite u32s_length; unfold EL_CJTAB, CJT_WORDS; rewrite length_map; cbn; lia |].
  apply ro_bytes_b_sound. exact cjt_image.
Qed.
Lemma cjt_read : forall (m : word -> option byte) i a, mem_inv psegs m -> 0 <= i < 8 -> a = wa (EL_CJTAB + 4 * i) ->
  ov_read_bytes psegs m a 4 = Some (le4 (Z_to_bv 64 (cjt i))).
Proof.
  intros m i a MI Hi ->. eapply (u32ro_read m EL_CJTAB CJT_WORDS i); [apply cjt_at; exact MI| | lia | reflexivity].
  unfold CJT_WORDS, cjt. rewrite nth_error_map. rewrite (nth_error_nth' CJT_TAB 0); [reflexivity|].
  change (length CJT_TAB) with 8%nat. lia.
Qed.
Definition cast_entry (sel : Z) : Z :=
  if sel =? 0 then 0x3c11c else if sel =? 1 then 0x3c2a8 else if sel =? 2 then 0x3c1d8 else if sel =? 3 then 0x3c218
  else if sel =? 4 then 0x3c188 else if sel =? 5 then 0x3c314 else if sel =? 6 then 0x3c364 else 0x3c258.
Lemma cjt_entry : forall sel, 0 <= sel < 8 -> EL_CJTAB + cjt sel = cast_entry sel /\ 0 <= cjt sel < 2^31.
Proof.
  intros sel H.
  assert (F : forallb (fun i => (EL_CJTAB + cjt i =? cast_entry i) && (0 <=? cjt i) && (cjt i <? 2 ^ 31)) (map Z.of_nat (seq 0 8)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. specialize (F sel ltac:(apply in_map_iff; exists (Z.to_nat sel); split; [lia|]; apply in_seq; lia)).
  apply andb_true_iff in F. destruct F as [F F3]. apply andb_true_iff in F. destruct F as [F1 F2].
  apply Z.eqb_eq in F1. apply Z.leb_le in F2. apply Z.ltb_lt in F3. lia.
Qed.

Definition cast_site (sel : Z) : Z :=
  if sel =? 0 then 0x3c15c else if sel =? 1 then 0x3c2e4 else if sel =? 2 then 0x3c398 else if sel =? 3 then 0x3c3c8
  else if sel =? 4 then 0x3c1a8 else if sel =? 5 then 0x3c334 else if sel =? 6 then 0x3c3f4 else 0x3c278.

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

  Definition cast_post (sel : Z) (ra : word) (q : Z) (gp s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' =>
      (exists a0 a1 a2 m',
         ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom psegs)
         /\ munch [(q - 16, q)] m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo q)
      \/ (exists a0 a1 a2 xs0 m',
         ms' = MS (mkR ra (Z_to_bv 64 (q + -16)) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (cast_site sel)) fc None m' (seg_rom psegs)
         /\ rw_cells psegs m' (q + -16) [C8 s0; C8 ra]
         /\ munch [(q - 16, q)] m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo (q + -16)
         /\ (sel = 2 \/ sel = 3 -> xs0 = Z_to_bv 64 17 \/ xs0 = Z_to_bv 64 18)).

  Ltac fin_ret := apply evt_done; left; do 4 eexists; split; [cbv delta [mkR]; reflexivity|]; repeat (split; [eassumption|]); eassumption.
  Ltac fin_site := apply evt_done; right; do 5 eexists; split; [cbv delta [mkR]; reflexivity|]; repeat (split; [eassumption|]); intros HS; first [left; reflexivity | right; reflexivity | exfalso; lia].

  Lemma cast_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node lo SELA sel : Z) (jsel : list byte),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv psegs m ->
    stk psegs m lo q -> ae_lo E <= lo -> lo <= q - 16 -> q <= ae_B E -> q mod 16 = 0 -> q <= node -> node + 16 <= ae_B E ->
    rw_cells psegs m SELA [CB 4 jsel; C4 (Z_to_bv 64 sel)] -> 0 <= sel < 8 -> q <= SELA -> SELA + 8 <= ae_B E -> q <= ae_DOC E ->
    evt psegs (cast_post sel ra q gp s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (SELA + 4)) (Z_to_bv 64 node) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_CAST) fc None m (seg_rom psegs)).
  Proof.
    intros until jsel. intros AI ROOT HEAP MI ST LOLO LOQ QB Q16 N0 N1 XSEL SEL SA0 SA1 QDOC.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB]].
    assert (LO0 : 0 <= ae_lo E) by (unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__); lia).
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    pose proof (el_root_elem E OK) as [EL NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    destruct AI as (TAPEB & SBUFB & PTRB & DOCC). unfold el_root in ROOT. unfold EL_CAST.
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia).
    pose proof (munch_refl [(q - 16, q)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.

    hide TAPEB. clear SBUFB PTRB.
    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB psegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    hstep. hstep.
    unhide TAPEB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (TB : bytes_at psegs mx (ae_TAPE E) (u64s (map (Z_to_bv 64) (ae_tws E))))
        by (eapply bytes_at_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact TAPEB|]; rewrite u64s_length, length_map; intros a Ha; cbn [outside]; lia) end.
    clear TAPEB.

    zstep. rewrite (a_sx32_small sel) by lia.
    step. zstep. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|]. clear KB.

    zstep. step. zstep. zstep.
    pose proof (cjt_entry sel SEL) as [CJE CJR].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (cjt_read mx sel (wa (Z.shiftl sel 2 + 82216)) ltac:(assumption) SEL ltac:(unfold wa, EL_CJTAB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RJ end.
    zstep. zstep. rewrite (a_swrap32_small (cjt sel)) by lia.
    replace (cjt sel + 82216) with (cast_entry sel) by (unfold EL_CJTAB in CJE; lia).

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (tape_read mx (ae_TAPE E) (ae_tws E) 1 TB ltac:(lia)) as RDT1;
      pose proof (tape_read mx (ae_TAPE E) (ae_tws E) 2 TB ltac:(lia)) as RDT2;
      pose proof (tape_read_type mx (ae_TAPE E) (ae_tws E) 1 TB ltac:(lia) TIR) as RDB end.
    rewrite Z.mul_1_r in RDT1, RDB. replace (ae_TAPE E + 8 * 2) with (ae_TAPE E + 8 + 8) in RDT2 by lia.
    Ltac do_ret FR ST q := step; step; step; release_frame FR ST q; step; fin_ret.
    Ltac arm_entry v pc := replace (cast_entry v) with pc by reflexivity; zstep.
    assert (CASES : sel = 0 \/ sel = 1 \/ sel = 2 \/ sel = 3 \/ sel = 4 \/ sel = 5 \/ sel = 6 \/ sel = 7) by lia.
    destruct CASES as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]].
    -
      arm_entry 0 0x3c11c. step. step. step. astep. astep. astep. astep. astep.
      zstep. if_cases K1; zify_cond K1; [do_ret FR ST q|].

      astep. astep. zstep. if_cases K2; zify_cond K2; [do_ret FR ST q|].

      astep. astep. astep. astep. unfold cast_site. cbn [Z.eqb]. fin_site.
    -
      arm_entry 1 0x3c2a8. step. step. step. astep. astep. astep. astep. astep.
      zstep. if_cases K1; zify_cond K1; [do_ret FR ST q|].
      astep. astep. zstep. if_cases K2; zify_cond K2; [do_ret FR ST q|].
      astep. astep. zstep. if_cases K3; zify_cond K3; [do_ret FR ST q|].
      unfold cast_site. cbn [Z.eqb]. fin_site.
    -
      arm_entry 2 0x3c1d8. step. step. step. astep. astep. astep. astep. astep.
      zstep. if_cases K1; zify_cond K1; [do_ret FR ST q|].

      astep. astep. zstep. if_cases K2; zify_cond K2.
      + astep. unfold cast_site. cbn [Z.eqb]. fin_site.
      +
        astep. zstep. if_cases K3; zify_cond K3; [do_ret FR ST q|].
        astep. step. unfold cast_site. cbn [Z.eqb]. fin_site.
    -
      arm_entry 3 0x3c218. step. step. step. astep. astep. astep. astep. astep.
      zstep. if_cases K1; zify_cond K1; [do_ret FR ST q|].
      astep. astep. zstep. if_cases K2; zify_cond K2.
      + astep. unfold cast_site. cbn [Z.eqb]. fin_site.
      + astep. zstep. if_cases K3; zify_cond K3; [do_ret FR ST q|].
        astep. step. unfold cast_site. cbn [Z.eqb]. fin_site.
    -
      arm_entry 4 0x3c188. step. step. step. astep. astep. astep. astep.
      zstep. if_cases K1; zify_cond K1; [do_ret FR ST q|].
      unfold cast_site. cbn [Z.eqb]. fin_site.
    -
      arm_entry 5 0x3c314. step. step. step. astep. astep. astep. astep.
      zstep. if_cases K1; zify_cond K1; [do_ret FR ST q|].
      unfold cast_site. cbn [Z.eqb]. fin_site.
    -
      arm_entry 6 0x3c364. step. step. step. astep. astep. astep. astep.
      zstep. if_cases K1; zify_cond K1; [unfold cast_site; cbn [Z.eqb]; fin_site|].
      do_ret FR ST q.
    -
      arm_entry 7 0x3c258. step. step. step. astep. astep. astep. astep.
      zstep. if_cases K1; zify_cond K1; [do_ret FR ST q|].
      unfold cast_site. cbn [Z.eqb]. fin_site.
  Qed.
End A22.
End WithCeiling0.
