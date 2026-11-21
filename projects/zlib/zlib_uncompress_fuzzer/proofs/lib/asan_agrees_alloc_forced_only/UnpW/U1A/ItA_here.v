(* reloc-zl14c *)
(* [U14] inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import ItA_base ItA_ldefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP SPA S F PB top : Z) (m1 : amem).
  Variables (ty : codetype) (lf wf cf : Z -> Z) (lo codes nx bits : Z).
  Hypothesis CX : itb_ctx RNG SP SPA S F PB top m1.
  Hypothesis C : itc ty lf lo codes nx bits cf wf.

  Notation LP := (S + 168 + 2 * lo).
  Notation cntAr := (cntA lf lo codes).
  Notation mx := (mxA lf lo codes).
  Notation mn := (mnA lf lo codes).
  Notation rt := (rootA lf lo codes bits).
  Notation work1Ar := (work1A lf lo codes wf).
  Notation w1 := (arr_get (work1A lf lo codes wf)).
  Notation X := (itm_ctx ty (lensA lf) lo nx rt mx).
  Notation MST := (mst SP SPA S F PB LP gp tp FR fc rt mx).
  Notation MINV := (fun m st => minv SPA S F PB m1 m ty rt nx bits lf w1 st).

  (* [comment removed for export] *)
  Definition tr_opw (st : ItSt) : Z :=
    let w := tr_w st in
    if w + 1 <? it_match ty then 0
    else if it_match ty <=? w then it_extra ty (t_work st) (w - it_match ty) else 96.
  Lemma tr_op_opw : forall st, tr_op X st = (if (tr_w st + 1 <? it_match ty) then 0 else if (it_match ty <=? tr_w st) then wrap8 (tr_opw st) else 96).
  Proof.
    intros st. unfold tr_op, tr_ov, tr_opw. cbn [x_ty itm_ctx]. cbv zeta.
    destruct (tr_w st + 1 <? it_match ty); [reflexivity|]. destruct (it_match ty <=? tr_w st); reflexivity.
  Qed.

  Lemma tr_op_wrap8 : forall st, tr_op X st = wrap8 (tr_opw st).
  Proof.
    intros st. rewrite tr_op_opw. unfold tr_opw. cbv zeta.
    destruct (tr_w st + 1 <? it_match ty); [reflexivity|]. destruct (it_match ty <=? tr_w st); reflexivity.
  Qed.

  Definition here_post (st : ItSt) (m : amem) (x16 x17 x25 x29 : word) : machine_state -> Prop :=
    fun ms' => exists (q6 q7 q10 q11 q16 q17 : word),
      ms' = MST st (Z_to_bv 64 (tr_opw st)) q6 q7 q10 q11 q16 q17 x25 (Z_to_bv 64 (tr_val X st)) x29 0x95f94 m.

  Lemma work1_range : forall j, 0 <= j < 288 -> 0 <= w1 j < 65536.
  Proof.
    intros j Hj. pose proof C as C'. open_itc C'. unfold work1A. rewrite itm_work_eq.
    apply (sort_k_work_range (lensA lf) lo codes (offsA lf lo codes) (workA wf) 288); [|exact Hj].
    intros i Hi. rewrite workA_get. apply Hwf. exact Hi.
  Qed.

  Lemma it_here : forall (st : ItSt) (m : amem) (v0 v96 v104 v112 : word) (of : Z -> Z)
      (x1 x6 x7 x10 x11 x16 x17 x25 x28 : word),
    MINV m st v0 v96 v104 v112 of -> spure work1Ar rt nx st ->
    0 <= t_sym st < 288 -> 0 <= tr_w st < 65536 ->
    (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
    (* [P14] 1.4's CODES base / extra are NULL, so here's extra / base arm must be unreachable for
       CODES: the caller passes w < 20 (U1A/ItA_safe20, from codes <= 19) *)
    (ty = CODES -> tr_w st < 20) ->
    (* [U14] 1.4 keeps match in t4 across here (0x95ef4 bgeu a0,t4; 1.3.1 loaded it from frame slot 72) *)
    evtF asegs RNG (here_post st m x16 x17 x25 (Z_to_bv 64 (it_match ty)))
      (MST st x1 x6 x7 x10 x11 x16 x17 x25 x28 (Z_to_bv 64 (it_match ty)) 0x95f08 m).
  Proof using All.
    intros until x28. intros INV HU Hsym Hw Hwm Hw20. open_ctx CX. unfold minv in INV. open_inv INV. open_spure HU. unfold mst, bst.
    pose proof C as C'. open_itc C'.
    assert (MT : 0 <= it_match ty <= 257) by (clear; destruct ty; cbn; lia).
    unfold tr_w in Hw, Hwm, Hw20. rewrite WK in Hw, Hwm, Hw20. box Hwm. box Hw20. clear HtyC HtyD LOWR DROPR.
    zs. zs. setreg 10 (Z_to_bv 64 (2 * t_sym st)) ltac:(rewrite zext32_x2 by lia; reflexivity).
    zs. do 4 zs.
    pose proof (f16arr_read asegs m (S + 808) 288 _ (t_sym st) _ WORK ltac:(lia) eq_refl) as RD.
    zs. rewrite (zx16_small (w1 (t_sym st))) by lia. clear RD.
    zs. zs. zbr0 K1. (* [U14] 1.4 compares with t4 directly: one load fewer than 1.3.1's ld a1,72(s1) *)
    - (* [comment removed for export] *)
      zs. zbr0 K2.
      + (* [comment removed for export] *)
        unbox Hwm. specialize (Hwm ltac:(lia)).
        zs. setreg 11 (Z_to_bv 64 (w1 (t_sym st) - it_match ty)) ltac:(rewrite swrap32_small by lia; f_equal; lia).
        zs. zs. setreg 10 (Z_to_bv 64 (2 * (w1 (t_sym st) - it_match ty))) ltac:(rewrite zext32_x2 by lia; reflexivity).
        zs. zs.
        pose proof (it_tabsh_mu _ m1 m SHT MU DJT) as (TSH1 & TSH2 & TSH3 & TSH4).
        destruct (ty_cases ty S) as [(ET & ECT & EM & EEX & EBS & ENE & EL & ED) | [(ET & ECT & EM & EEX & EBS & ENE & EL & ED) | (ET & ECT & EM & EEX & EBS & ENE & EL & ED)]];
          rewrite ?EEX, ?EBS, ?EM in *; rewrite ENE in Hwm.
        * (* [P14] a worker 2026-11-11: CODES. 1.4 stores NULL base / extra, and this arm (w >= 20) is unreachable:
             the caller's bound gives w < 20 (1.3.1 read work[w - 20] here) *)
          unbox Hw20. specialize (Hw20 ET). exfalso. lia.
        * (* [comment removed for export] *)
          pose proof (lext_range (w1 (t_sym st) - 257) ltac:(lia)) as XR. pose proof (lbase_range (w1 (t_sym st) - 257) ltac:(lia)) as BR.
          destruct (tab62_check m 149312 2147469544 (w1 (t_sym st) - 257) TSH2 eq_refl ltac:(lia) eq_refl ltac:(lia)) as (b1 & RD1 & CK1).
          zs. zs. zs. rewrite sxb_sval. clear RD1.
          ck_branchJ 5 0x95f6c CK1. (* [U14] the slow path reuses t0 at 1.4 (1.3.1: a7) *)
          zs. zs. setreg 11 (Z_to_bv 64 (2 * (w1 (t_sym st) - 257))) ltac:(rewrite Z.mod_small by lia; rewrite shl1_2x; reflexivity).
          zs. zs.
          destruct (tab62_check m 149216 2147469532 (w1 (t_sym st) - 257) TSH1 eq_refl ltac:(lia) eq_refl ltac:(lia)) as (b2 & RD2 & CK2).
          zs. zs. zs. rewrite sxb_sval. clear RD2.
          pose proof (lext_read m (w1 (t_sym st) - 257) _ MI ltac:(lia) eq_refl) as RDX.
          zs. rewrite (zx16_small (arr_get lext_a (w1 (t_sym st) - 257))) by lia. clear RDX.
          ck_branchJ 10 0x95f90 CK2.
          pose proof (lbase_read m (w1 (t_sym st) - 257) _ MI ltac:(lia) eq_refl) as RDB.
          zs. rewrite (zx16_small (arr_get lbase_a (w1 (t_sym st) - 257))) by lia. clear RDB.
          apply evtF_done. unfold here_post. do 6 eexists.
          unfold tr_opw, tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. cbv zeta. rewrite WK, ET. cbn [it_match it_extra it_base].
          destruct (Z.ltb_spec (w1 (t_sym st) + 1) 257); [lia|].
          destruct (Z.leb_spec 257 (w1 (t_sym st))); [|lia]. cbn [snd]. reflexivity.
        * (* [comment removed for export] *)
          pose proof (dext_range (w1 (t_sym st) - 0) ltac:(lia)) as XR. pose proof (dbase_range (w1 (t_sym st) - 0) ltac:(lia)) as BR.
          pose proof (tab64_check m 149504 2147469568 (w1 (t_sym st) - 0) TSH4 eq_refl ltac:(lia) eq_refl ltac:(lia)) as RD1.
          zs. zs. zs. zs. clear RD1.
          zs. zs. setreg 11 (Z_to_bv 64 (2 * (w1 (t_sym st) - 0))) ltac:(rewrite Z.mod_small by lia; rewrite shl1_2x; reflexivity).
          zs. zs.
          pose proof (tab64_check m 149408 2147469556 (w1 (t_sym st) - 0) TSH3 eq_refl ltac:(lia) eq_refl ltac:(lia)) as RD2.
          zs. zs. zs. clear RD2.
          pose proof (dext_read m (w1 (t_sym st) - 0) _ MI ltac:(lia) eq_refl) as RDX.
          zs. rewrite (zx16_small (arr_get dext_a (w1 (t_sym st) - 0))) by lia. clear RDX.
          zs.
          pose proof (dbase_read m (w1 (t_sym st) - 0) _ MI ltac:(lia) eq_refl) as RDB.
          zs. rewrite (zx16_small (arr_get dbase_a (w1 (t_sym st) - 0))) by lia. clear RDB.
          apply evtF_done. unfold here_post. do 6 eexists.
          unfold tr_opw, tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. cbv zeta. rewrite WK, ET. cbn [it_match it_extra it_base].
          destruct (Z.ltb_spec (w1 (t_sym st) + 1) 0); [lia|].
          destruct (Z.leb_spec 0 (w1 (t_sym st))); [|lia]. cbn [snd]. reflexivity.
      + (* [comment removed for export] *)
        zs. zs. zs.
        apply evtF_done. unfold here_post. do 6 eexists.
        unfold tr_opw, tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. cbv zeta. rewrite WK.
        destruct (Z.ltb_spec (w1 (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (w1 (t_sym st))); [lia|]. cbn [snd]. reflexivity.
    - (* [comment removed for export] *)
      zs. zs.
      apply evtF_done. unfold here_post. do 6 eexists.
      unfold tr_opw, tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. cbv zeta. rewrite WK.
      destruct (Z.ltb_spec (w1 (t_sym st) + 1) (it_match ty)); [|lia]. cbn [snd]. reflexivity.
  Qed.
End P.
End CANSEC1.
