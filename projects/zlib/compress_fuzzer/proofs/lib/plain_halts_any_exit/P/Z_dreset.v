(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Zlib_iface Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_adler32 F_memset Z_dinit_kit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz Deflate RefDeflateInitLib FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation wz := (Z_to_bv 64).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Definition Z_DRESETKEEP : Z := 0x16bd8.
Definition Z_DRESET : Z := 0x16730.
Definition Z_DRESET_STACK : Z := 64.

Lemma state_check_cases : forall d, deflateStateCheck d = false ->
  let st := ds_status d in st = 42 \/ st = 57 \/ st = 69 \/ st = 73 \/ st = 91 \/ st = 103 \/ st = 113 \/ st = 666.
Proof.
  intros d H. unfold deflateStateCheck in H. apply negb_false_iff in H. cbv zeta.
  unfold INIT_STATE, GZIP_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE, BUSY_STATE, FINISH_STATE in H.
  repeat (apply orb_true_iff in H; destruct H as [H|H]); apply Z.eqb_eq in H; lia.
Qed.

Definition zs_raw (As ni ai ti no ao to : Z) (p1 p2 : list byte) (msg opq dt : word) (p3 : list byte) (adl resv : word) : list cell :=
  zs_pub ni ai ti no ao to p1 p2 ++ [C8 msg; C8 (wz As); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 opq; C4 dt; CB 4 p3; C8 adl; C8 resv].

Ltac merge44 H k :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let rest := eval cbv beta iota delta [skipn] in (skipn k cs) in
    lazymatch rest with C4 ?a :: C4 ?b :: ?post =>
      let H' := fresh in pose proof (cells_merge44 m A pre a b post H) as H'; cbn [app] in H'; clear H; rename H' into H end end.
Ltac split8 H k :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let rest := eval cbv beta iota delta [skipn] in (skipn k cs) in
    lazymatch rest with C8 (Z_to_bv 64 0) :: ?post =>
      let H' := fresh in pose proof (cells_split8_0 m A pre post H) as H'; cbn [app] in H'; clear H; rename H' into H end end.

(* 1.4: deflateResetKeep also resets part of the match state after _tr_init (block_start := strstart read as an
   unsigned word, match_length := prev_length := 2, match_available := lookahead := 0, matches := 0 when level <> 0)
   and clears gzhead. lm_init (deflateReset) overwrites every one of those fields, so LM (RK1 s) = LM (tr_init (RK0 s)). *)
Definition rk1_fields (x : deflate_state) : deflate_state :=
  set_prev_length (set_lookahead (set_match_available (set_match_length (set_block_start x (ds_strstart x mod 2 ^ 32)) 2) 0) 0) 2.
Definition RK1 (s : deflate_state) : deflate_state := rk1_fields (tr_init (RK0 s)).

Lemma LM_rk1_fields : forall x, LM (rk1_fields x) = LM x.
Proof. intros x. destruct x. reflexivity. Qed.

Lemma LM_RK1 : forall s, LM (RK1 s) = LM (tr_init (RK0 s)).
Proof. intros s. apply LM_rk1_fields. Qed.

Lemma tr_init_matches : forall x, ds_matches (tr_init x) = 0.
Proof. intros x. reflexivity. Qed.

Section RESET.
  Hypothesis HTRI : tr_init_stmt.

  Definition dresetkeep_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : dlay) (s : deflate_state) (ni ai no ao : Z) (p1 p2 : list byte) (opq : word) (p3 : list byte) (resv : word) (lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ a0 = wz 0
      /\ rw_cells psegs m' (dl_S L) (zs_raw (dl_As L) ni ai 0 no ao 0 p1 p2 (wz 0) opq (wz 2) p3 (wz 1) resv)
      /\ DST m' L (RK1 s).

  Lemma deflateResetKeep_spec : forall (L : dlay) (s : deflate_state)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (msg opq dt : word) (p3 : list byte) (adl resv : word) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DSTi m L s ->
    rw_cells psegs m (dl_S L) (zs_raw (dl_As L) ni ai ti no ao to p1 p2 msg opq dt p3 adl resv) ->
    deflateStateCheck s = false -> 0 <= ds_wrap s <= 1 ->
    ds_matches s = 0 -> ds_gzhead s = 0 ->
    stk psegs m lo (bv_unsigned sp) -> dlay_below L lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 ->
    mem_inv psegs m ->
    a0 = wz (dl_S L) ->
    evt psegs (dresetkeep_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s ni ai no ao p1 p2 opq p3 resv lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_DRESETKEEP) fc None m (seg_rom psegs)).
  Proof.
    intros until m. intros ST ZS CHK WR HM0 HGZ STK BEL LOSP MI ->.
    open_DST ST. open_A GA. unfold zs_raw, zs_pub in ZS. cbn [app] in ZS.
    lay_open LAY. below_open BEL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (EUS : bv_unsigned (wz (dl_S L)) = dl_S L) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz (dl_As L)) = dl_As L) by (apply unsigned_lit; lia).
    assert (EUb : bv_unsigned (wz (dl_Ab L)) = dl_Ab L) by (apply unsigned_lit; lia).
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212)] m) as MUf.
    unfold Z_DRESETKEEP.
    zstep. zstep. if_false. zstep. zstep. if_false. zstep. zstep. if_false.
    carve_frame 32%nat STK.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false. zstep. zstep. if_false. (* 1.4: + sd s2,0(sp) *)
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (evt_cut psegs (fun ms' => exists a3' a4' : word,
        ms' = MS (mkR ra (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz (dl_As L)) s1 (wz (dl_S L)) (wz (-2)) (sx32 (wz (ds_status s)))
                      a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x16c38) fc None mm (seg_rom psegs))) end.
    { pose proof (state_check_cases s CHK) as CS. cbv zeta in CS.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let bs := eval vm_compute in (option.default [] (image_bytes psegs 0x106e0 8)) in
        assert (MASK : ro_cells psegs mm 0x106e0 [CB (length bs) bs])
          by (apply ro_cells_image; [assumption| vm_compute; reflexivity| lia| cbn; lia]) end.
      cbn [length] in MASK.
      destruct CS as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E.
      - zstep. zstep. if_true. zstep. zstep. if_false. zstep. zstep. if_true. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_true. zstep. zstep. if_true. apply evt_done. do 2 eexists. reflexivity. }
    intros ms' (a3' & a4' & ->).
    zs. zs. zs. zs. zs. zs. zs. zs. zs.
    zstep. if_cases K; zify_cond K; rewrite ?signed_wz in K by lia; [|exfalso; lia]. clear K.
    zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; lia|]. clear K.
    zs. zs. zs. zs.
    zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; lia|]. clear K.
    zs. zs. zs.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [eapply adler32_null_spec with (adler := 0) (len := 0); [lia| lia| lia| eassumption] | post_call segs mm] end.
   
    (* 1.4: j; li s2,0; lw a1,level; sd adler; li a0,-2; sd zero,gzhead; sw last_flush; bnez a1 (level 6: taken); mv a0,s0 *)
    zs. zs. zs. zs. zs. zs. zs.
    (* every level (compress2's deflateInit takes 0..9). level <> 0: bnez taken, s2 stays 0;
       level = 0: lui; add; lw s2 = matches, which is 0 here (HM0). Both paths meet after mv a0,s0. *)
    eapply (evt_cut psegs (fun ms' => ms' = _)).
    { zstep. if_cases K.
      - zs. apply evt_done. reflexivity.
      - tr_groups MUf WM. open_D GD. rewrite HM0 in GD.
        zs. zs. zs. zs. apply evt_done. reflexivity. }
    intros ms' ->.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (ST1 : DSTi mm L (RK0 s)) end.
    { tr_groups MUf WM.
      constructor; [ | exact GB | exact GC | exact GD | exact Glt | exact Gdt | exact Gbt | exact Gblc | exact Gheap | exact Gdep
                   | exact Gwin | exact Gprev | exact Ghead | exact Gpend | close_lens LENS | exact LAY ].
      do 5 eexists. unfold dsA_cells, RK0. dsred.
        replace (ds_wrap s =? 2) with false by (symmetry; apply Z.eqb_neq; lia). unfold INIT_STATE.
        rewrite HGZ.
        close_cells GA. }
    clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf.
    zstep.
    call (HTRI L (RK0 s)).
    1:{ exact ST1. } 1:{ eassumption. } 1:{ reflexivity. }
    clear ST1.
    (* 1.4: after _tr_init: matches := s2 (0), block_start := strstart, match_length := 2, match_available := 0,
       lookahead := 0, prev_length := 2 (RK1), then the epilogue with ld s2 *)
    remember (tr_init (RK0 s)) as Y eqn:EY.
    open_DST POST. open_A GA. open_D GD.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968)] mm) as MUk;
      pose proof (wmono_refl psegs mm) as WMk end.
    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
    zs. zs. zs. zs. zs. zs. zs.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold dresetkeep_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [lazymatch goal with H : mem_inv psegs ?mm |- mem_inv psegs ?mm => exact H end|].
    split; [exact STK|]. split; [reflexivity|].
    split; [unfold zs_raw, zs_pub; cbn [app]; exact ZS|].
    tr_groups MUk WMk.
    unfold RK1. rewrite <- EY.
    constructor.
    -
      abstract (do 5 eexists; unfold dsA_cells, rk1_fields; dsred; close_cells GA;
        unfold zx32; f_equal; rewrite unsigned_lit_wrap; apply Z.mod_mod_divide; exists 4294967296; reflexivity).
    - abstract (exact GB).
    - abstract (exact GC).
    -
      abstract (do 5 eexists; unfold dsD_cells, rk1_fields; dsred; close_cells GD; rewrite EY, tr_init_matches; reflexivity).
    - abstract (exact Glt).
    - abstract (exact Gdt).
    - abstract (exact Gbt).
    - abstract (exact Gblc).
    - abstract (exact Gheap).
    - abstract (exact Gdep).
    - abstract (exact Gwin).
    - abstract (exact Gprev).
    - abstract (exact Ghead).
    - abstract (exact Gpend).
    - lazymatch goal with H : dlens Y |- _ => abstract (close_lens H) end.
    - exact LAY.
  Qed.

  Definition dreset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : dlay) (s : deflate_state) (ni ai no ao : Z) (p1 p2 : list byte) (opq : word) (p3 : list byte) (resv : word) (lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968); (dl_Ah L, dl_Ah L + 65536)] m m'
      /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ a0 = wz 0
      /\ rw_cells psegs m' (dl_S L) (zs_raw (dl_As L) ni ai 0 no ao 0 p1 p2 (wz 0) opq (wz 2) p3 (wz 1) resv)
      /\ DST m' L (LM (tr_init (RK0 s))).

End RESET.
