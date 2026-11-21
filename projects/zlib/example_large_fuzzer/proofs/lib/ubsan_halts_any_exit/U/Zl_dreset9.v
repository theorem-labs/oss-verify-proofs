(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import InitMem Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Zlib_iface Z_dview Z_drep Z_dkit Z_trees_iface Z_adler32 F_memset Z_dinit_kit Z_ukit Z_dreset.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz Deflate RefDeflateInitLib FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation wz := (Z_to_bv 64).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Definition Z_DRESETKEEP : Z := 0x16e4c.
Definition Z_DRESET : Z := 0x168c4.
Definition Z_DRESET_STACK : Z := 192.
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
Lemma land7_of_mod8 : forall a, a mod 8 = 0 -> Z.land a 7 = 0.
Proof. intros a H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. exact H. Qed.
Ltac al8m X := rewrite (land7_of_mod8 X) by (Z.div_mod_to_equations; lia).
Lemma config9_relro : forall m, relro_clean m ->
  rw_cells usegs m 0x2c2e8 [C2 (wz 32); C2 (wz 258); C2 (wz 258); C2 (wz 4096); C8 (wz 0x1a07c)].
Proof.
  intros m RC. unfold relro_clean, RELRO_LO, RELRO_HI in RC.
  pose (cs := [C2 (wz 32); C2 (wz 258); C2 (wz 258); C2 (wz 4096); C8 (wz 0x1a07c)]).
  apply (InitMem.rw_cells_recast usegs m 0x2c2e8 [CB 16 (cells_bytes cs)] cs).
  - apply (InitMem.rw_cells_image0 usegs m 0x2c2e8 (cells_bytes cs)).
    + intros a Ha. apply RC. change (Z.of_nat (length (cells_bytes cs))) with 16 in Ha. lia.
    + vm_compute. reflexivity.
    + lia.
    + change (Z.of_nat (length (cells_bytes cs))) with 16. lia.
  - cbn. repeat split; exact I.
  - vm_compute. reflexivity.
  - reflexivity.
Qed.
Section RESET.
  Hypothesis HTRI : tr_init_stmt.
  Definition dresetkeep_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : dlay) (s : deflate_state) (ni ai no ao : Z) (p1 p2 : list byte) (opq : word) (p3 : list byte) (resv : word) (lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ a0 = wz 0
      /\ rw_cells usegs m' (dl_S L) (zs_raw (dl_As L) ni ai 0 no ao 0 p1 p2 (wz 0) opq (wz 2) p3 (wz 1) resv)
      /\ DST m' L (RK1 s).
  Lemma deflateResetKeep_spec : forall (L : dlay) (s : deflate_state)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (msg opq dt : word) (p3 : list byte) (adl resv : word) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DSTi m L s ->
    rw_cells usegs m (dl_S L) (zs_raw (dl_As L) ni ai ti no ao to p1 p2 msg opq dt p3 adl resv) ->
    deflateStateCheck s = false -> 0 <= ds_wrap s <= 1 ->
    ds_level s = 9 -> ds_gzhead s = 0 ->
    stk usegs m lo (bv_unsigned sp) -> dlay_below L lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 160 ->
    mem_inv usegs m ->
    a0 = wz (dl_S L) ->
    evt usegs (dresetkeep_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s ni ai no ao p1 p2 opq p3 resv lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_DRESETKEEP) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros ST ZS CHK WR HLV HGZ STK BEL LOSP MI ->.
    open_DST ST. open_A GA. unfold zs_raw, zs_pub in ZS. cbn [app] in ZS.
    lay_open LAY. below_open BEL.
    pose proof (lo_S _ LAY) as (_ & ALS & _). pose proof (lo_s _ LAY) as (_ & ALs & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (EUS : bv_unsigned (wz (dl_S L)) = dl_S L) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz (dl_As L)) = dl_As L) by (apply unsigned_lit; lia).
    assert (EUb : bv_unsigned (wz (dl_Ab L)) = dl_Ab L) by (apply unsigned_lit; lia).
    assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212)] m) as MUf.
    unfold Z_DRESETKEEP.
    carve_frame 32%nat STK.
    zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. if_false. zstep. al8m (dl_S L). zstep. if_false.
    zstep. zstep. if_false. zstep. zstep. if_false.
    zstep. zstep. if_false. zstep. al8m (dl_As L). zstep. if_false.
    zstep. zstep. if_false.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (evt_cut usegs (fun ms' => exists a3' a4' : word,
        ms' = MS (mkR ra (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz (dl_As L)) s1 (wz (dl_S L)) (wz (-2)) (sx32 (wz (ds_status s)))
                      a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x16ebc) fc None mm (seg_rom usegs))) end.
    { pose proof (state_check_cases s CHK) as CS. cbv zeta in CS.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let bs := eval vm_compute in (option.default [] (image_bytes usegs 0x10700 8)) in
        assert (MASK : ro_cells usegs mm 0x10700 [CB (length bs) bs])
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
    zs.
    zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; lia|]. clear K.
    zs. zs. zs. zs.
    zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; lia|]. clear K.
    zs. zs. zstep.
    remember (wz (bv_unsigned sp + -32)) as spw eqn:Espw.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [eapply (adler32_null_spec lo) with (adler := 0) (len := 0); [lia| lia| lia| eassumption| rewrite E32; exact STK| rewrite E32; unfold ADLER32_FRAME; lia] | post_call segs mm] end.
    lazymatch goal with H : stk usegs _ lo (bv_unsigned spw) |- _ => rewrite E32 in H; rename H into STK' end.
    subst spw.
    zs. zs. zs. zs. zs. zs. zs.
    rewrite HLV. zstep. if_true.
    zs.
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
    remember (tr_init (RK0 s)) as Y eqn:EY.
    open_DST POST. open_A GA. open_D GD.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968)] mm) as MUk;
      pose proof (wmono_refl usegs mm) as WMk end.
    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
    zs. zs. zs. zs. zs. zs. zs.
    release_frame FR STK' (bv_unsigned sp).
    apply evt_done. unfold dresetkeep_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [lazymatch goal with H : mem_inv usegs ?mm |- mem_inv usegs ?mm => exact H end|].
    split; [exact STK'|]. split; [reflexivity|].
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
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968); (dl_Ah L, dl_Ah L + 65536)] m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ a0 = wz 0
      /\ rw_cells usegs m' (dl_S L) (zs_raw (dl_As L) ni ai 0 no ao 0 p1 p2 (wz 0) opq (wz 2) p3 (wz 1) resv)
      /\ DST m' L (LM (tr_init (RK0 s))).
  Lemma deflateReset9_spec : forall (L : dlay) (s : deflate_state)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (msg opq dt : word) (p3 : list byte) (adl resv : word) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DSTi m L s ->
    rw_cells usegs m (dl_S L) (zs_raw (dl_As L) ni ai ti no ao to p1 p2 msg opq dt p3 adl resv) ->
    relro_clean m ->
    deflateStateCheck s = false -> 0 <= ds_wrap s <= 1 ->
    ds_level s = 9 -> ds_w_size s = 32768 -> ds_hash_size s = 32768 -> ds_gzhead s = 0 ->
    stk usegs m lo (bv_unsigned sp) -> dlay_below L lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_DRESET_STACK ->
    mem_inv usegs m ->
    a0 = wz (dl_S L) ->
    evt usegs (dreset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s ni ai no ao p1 p2 opq p3 resv lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_DRESET) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros ST ZS RC CHK WR HLV HW HH HGZ STK BEL LOSP MI ->.
    pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'.
    pose proof (lo_S _ LAY) as (_ & ALS & _). pose proof (lo_s _ LAY) as (_ & ALs & _). pose proof (lo_h _ LAY) as (_ & ALh & _).
    unfold Z_DRESET_STACK in LOSP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (EUS : bv_unsigned (wz (dl_S L)) = dl_S L) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz (dl_As L)) = dl_As L) by (apply unsigned_lit; lia).
    assert (EUh : bv_unsigned (wz (dl_Ah L)) = dl_Ah L) by (apply unsigned_lit; lia).
    assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968); (dl_Ah L, dl_Ah L + 65536)] m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf.
    unfold Z_DRESET.
    carve_frame 32%nat STK.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. (* 1.4 UBSan: + sd s2,0(sp) *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (ST0 : DSTi mm L s) by
      (apply (DSTi_agree m mm); [exact ST| eapply ag_blocks_munch; [exact LAY| exact MUf| exact WM| | | | |]; cbn [disjoint_from]; slia]) end.
    clear MUf ST.
    call (deflateResetKeep_spec L s ni ai ti no ao to p1 p2 msg opq dt p3 adl resv lo).
    1:{ exact ST0. } 1:{ exact ZS. } 1:{ exact CHK. } 1:{ exact WR. } 1:{ exact HLV. } 1:{ exact HGZ. } 1:{ rewrite E32. exact STK. }
    1:{ rewrite E32. unfold dlay_below in *. lia. } 1:{ rewrite E32. lia. } 1:{ exact MI. } 1:{ reflexivity. }
    subst x2. rewrite E32 in PC. rename PC into STK. rename PC1 into ZS. unfold zs_raw, zs_pub in ZS. cbn [app] in ZS. clear ST0.
    remember (RK1 s) as X eqn:EX.
    assert (EWX : ds_w_size X = 32768) by (subst X; exact HW).
    assert (EHX : ds_hash_size X = 32768) by (subst X; exact HH).
    assert (ELX : ds_level X = 9) by (subst X; exact HLV).
    open_DST POST. open_A GA. open_D GD. rewrite EWX, EHX, ELX in GA.
    unfold dhead, u16arr in Ghead.
    pose proof (av16_zlength (ds_head X) 32768 ltac:(lia)) as LH.
    destruct (u8arr_split3 _ (dl_Ah L) _ (Z.to_nat 65534) 2 Ghead ltac:(lia)) as (H1 & H2 & _). clear Ghead.
    replace (dl_Ah L + Z.of_nat (Z.to_nat 65534)) with (dl_Ah L + 65534) in H2 by lia.
    apply rw_cells_of_u8arr in H1. rewrite length_firstn, Nat.min_l in H1 by lia.
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ah L, dl_Ah L + 65536)] x14) as MUf.
    pose proof (wmono_refl usegs x14) as WMf.
    zstep. if_true.
    zstep. if_false. zstep. al8m (dl_S L). zstep. if_false.
    zs. zstep. if_false. zstep. al8m (dl_As L). zstep. if_false.
    zs. zs. zs. zs. zs. zs. zs. zs. zs.
    gF. do 3 zstep. gX. zstep. if_false.
    zstep. rewrite (land1_mod2 (dl_Ah L + 65534)) by (Z.div_mod_to_equations; lia). zstep. if_false.
    zs. zs. zs. zs. (* 1.4 UBSan: mv s2,a0; lui; addw; add s1 = s + 5928 *)
    zs.
    zs. zs. zs.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [eapply memset_callZ with (D := dl_Ah L) (C := 0) (N := 65534); [exact H1| eassumption| lia| lia| lia| lia] | post_call segs mm] end.
    lazymatch type of POST with rw_cells _ ?mm _ _ => rename mm into mhd end.
    pose proof (dhead_LM_cleared mhd L X EHX LENS POST H2) as Ghead.
    clear POST H2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968)] mhd) as MUg.
    pose proof (wmono_refl usegs mhd) as WMg.
    (* 1.4 UBSan lm_init: lw a0,level; li a1,10; sw zero,0(s1) clears matches (5928); sw zero,32(s1) clears slid (5960, a
       junk cell); bgeu; then sll / auipc / add / not / bltu; mv a0,s2; add a1,a2,a1 *)
    zs. zs. zs. zs. zstep. if_false.
    zs. zs. zs. zs. zstep. if_false.
    zs. zs.
    (* 1.4 UBSan: sw zero,4(s1) clears insert (5932) before the config reads, so RC' / CFG name the memory after it *)
    zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RC' : relro_clean mm) end.
    { eapply relro_clean_munch; [exact RC| exact MU|]. unfold RELRO_LO, RELRO_HI. cbn [disjoint_from].
      destruct (lo_s L LAY) as (_ & _ & _ & Ds). destruct (lo_h L LAY) as (_ & _ & _ & Dh). lia. }
    pose proof (config9_relro _ RC') as CFG.
    (* the four config lhu *)
    zs. zs. zs. zs.
    rewrite !zx16_small by lia.
    zs.
    zs. zs. zs. zs. zs. zs. zs. zs. zs.
    merge44 GA 31%nat.
    zs.
    split8 GA 31%nat.
    zs. zs. zs. zs. zs. zs. (* 1.4 UBSan: + ld s2 *)
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold dreset_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [lazymatch goal with H : mem_inv usegs ?mm |- mem_inv usegs ?mm => exact H end|].
    split; [exact STK|]. split; [reflexivity|].
    split; [unfold zs_raw, zs_pub; cbn [app]; exact ZS|].
    rewrite <- LM_RK1, <- EX. tr_groups MUf WMf. tr_groups MUg WMg.
    constructor.
    - abstract (do 5 eexists; unfold dsA_cells, LM, clear_hash; dsred; rewrite ELX;
      change (cfg_lazy 9) with 258; change (cfg_good 9) with 32; change (cfg_nice 9) with 258; change (cfg_chain 9) with 4096; unfold MIN_MATCH;
      close_cells GA).
    - abstract (exact GB).
    - abstract (exact GC).
    - assert (EMX : ds_matches X = 0) by (rewrite EX; reflexivity).
      abstract (do 5 eexists; unfold dsD_cells, LM, clear_hash; dsred; close_cells GD; rewrite EMX; reflexivity).
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
    - destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
      abstract (constructor; unfold LM, clear_hash; dsred; rewrite ?arr_len_fill, ?arr_len_set; [exact l1|exact l2|exact l3|exact l4|exact l5|exact l6|exact l7|exact l8|exact l9|exact l10|exact l11|exact l12|exact l13]).
    - exact LAY.
  Qed.
End RESET.
