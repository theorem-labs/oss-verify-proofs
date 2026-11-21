(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure UbFit2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import ItB_base ItB_ldefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Notation ST := (bst SP SPA S F PB LP (cty ty) gp tp FR fc).
  Notation cntAr := (cntA lf lo codes).
  Notation cA := (arr_get (cntA lf lo codes)).
  Notation mx := (mxA lf lo codes).
  Notation mn := (mnA lf lo codes).
  Notation rt := (rootA lf lo codes bits).
  Notation w1 := (arr_get (work1A lf lo codes wf)).
  Notation SHPB := (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880)).
  Notation MST := (mst SP SPA S F PB LP (cty ty) gp tp FR fc rt mx).
  Notation MINV := (fun m st => minv SPA S F PB m1 m ty rt nx bits lf w1 st).

  Definition head_post (st : ItSt) (v0 v8 v16 v128 v136 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => exists (m : amem) (q5 q6 q7 q11 q16 q29 q30 q31 v56 : word),
      ms' = MST st q5 q6 q7 q11 q16 q29 q30 q31 0x97180 m /\ MINV m st v0 v8 v16 v56 v128 v136 of.

  Notation st0 := (itm_st0 mn nx rt cntAr (tblA cf) (work1A lf lo codes wf)).

  Definition switch_post (v0 v8 v16 v128 v136 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => (head_post st0 v0 v8 v16 v128 v136 of ms' /\ it_not_enough ty (itm_used rt) = false)
      \/ (ret_pre SP SPA S F PB LP (cty ty) gp tp FR fc m1 1 lf w1 cf (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ms'
          /\ it_not_enough ty (itm_used rt) = true).

  Lemma it_init : forall (m : amem) (v0 v8 v16 v24 v32 v40 v56 v80 v88 v96 v104 v112 v128 v136 : word) (of : Z -> Z)
      (x1 x5 x6 x7 x10 x11 x16 x17 x25 x28 x29 x30 x31 : word),
    1 <= mx ->
    (* [U14B] A2 2026-11-12: the 1.4 combined frame (see minv in ItB_ldefs): extra in slot 16, base in 48, the flag XFL in
       56, the free spill v56 in 64 *)
    itb_inv SPA S F PB m1 m v0 v8 (Z_to_bv 64 (EXA ty S)) v24 v32 v40 (Z_to_bv 64 (BSA ty S)) (Z_to_bv 64 (XFL ty)) v56 (Z_to_bv 64 (it_match ty))
            v80 v88 v96 v104 v112 (Z_to_bv 64 (S + 160)) v128 v136 (Z_to_bv 64 F)
            cA of lf w1 cf (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ->
    evtF bsegs RNG (switch_post v0 v8 v16 v128 v136 of)
      (ST x1 x5 x6 x7 x10 x11 (Z_to_bv 64 mn) SHPB (Z_to_bv 64 rt) (Z_to_bv 64 mx) x16 x17 x25 x28 x29 x30 x31 0x970b8 m).
  Proof using All.
    intros until x31. intros Hmx INV. pose proof INV as INV0. open_ctx CX. open_inv INV. unfold bst.
    pose proof C as C'. open_itc C'.
    pose proof (rt_facts lf lo codes bits Hmx) as (RT & RT2 & RT3).
    pose proof (pow2_le15 rt ltac:(lia)) as PRT.
    pose proof (ne_pow ty rt RT) as NEP.
    zs. zs. ubg. zs. zs. zs. ubg. zs. zs. zs. zs. zs. zs.
    zs. zs. ubg.
    zs. zs. zs.
    apply (fun H => f32arr_ext bsegs _ _ _ _ (arr_get (tblA cf)) H (fun j _ => eq_sym (tblA_get cf j))) in CDS.
    Local Ltac init_tail RT PRT NEP ET :=
      zs; ubg; zs; zs; zs;
      zs; setreg 11 (Z_to_bv 64 (2 ^ rootA lf lo codes bits)) ltac:(rewrite sllw_1 by lia; reflexivity);
      zs; zs; zs; zs; zs; zs;
      zs; setreg 11 (Z_to_bv 64 (2 ^ rootA lf lo codes bits - 1)) ltac:(rewrite swrap32_small by lia; f_equal; lia);
      zs; zs; zs; zs; zs; zs.
    Local Ltac init_close ECT :=
      apply evtF_done; left; split;
      [ unfold head_post; eexists; do 9 eexists; split;
        [ unfold mst, bst; rewrite ECT; cbn [t_next t_sym t_len t_drop t_huff itm_st0]; rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r; reflexivity
        | unfold minv; cbn [t_curr t_low t_used t_count t_tbl t_sym itm_st0]; rewrite itm_used_pow2 by lia; change (lowS 4294967295) with (-1);
          lazymatch goal with FRM : rw_cells _ _ _ _ |- _ => replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) in FRM by (apply bv_eq; reflexivity) end;
          unfold itb_inv, itb_W, frm19; do 10 (split; [eassumption|]); eassumption ]
      | ].
    destruct (ty_cases ty S) as [(ET & ECT & EM & EEX & EBS & ENE & EL & ED) | [(ET & ECT & EM & EEX & EBS & ENE & EL & ED) | (ET & ECT & EM & EEX & EBS & ENE & EL & ED)]];
      rewrite ECT.
    -
      zs. zs. zs.
      init_tail RT PRT NEP ET. init_close ECT; rewrite NEP, ET; reflexivity.
    -
      zs. zs. zs. zbr K9.
      +
        apply evtF_done. right. split; [| rewrite NEP, ET; destruct (Z.leb_spec rt 9); [lia | reflexivity]].
        unfold ret_pre. eexists. do 16 eexists. do 19 eexists. exists cA, of. split; [unfold bst; rewrite ECT; reflexivity |].
        unfold itb_inv, itb_W, frm19. do 10 (split; [eassumption|]). eassumption.
      + zs. zs.
        init_tail RT PRT NEP ET. init_close ECT; rewrite NEP, ET; destruct (Z.leb_spec rt 9); [reflexivity | lia].
    -
      zs. zs. zs. zs. zs. zbr K9.
      + apply evtF_done. right. split; [| rewrite NEP, ET; destruct (Z.leb_spec rt 9); [lia | reflexivity]].
        unfold ret_pre. eexists. do 16 eexists. do 19 eexists. exists cA, of. split; [unfold bst; rewrite ECT; reflexivity |].
        unfold itb_inv, itb_W, frm19. do 10 (split; [eassumption|]). eassumption.
      + init_tail RT PRT NEP ET. init_close ECT; rewrite NEP, ET; destruct (Z.leb_spec rt 9); [reflexivity | lia].
  Qed.
  Lemma it_switch : forall (m : amem) (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v128 v136 : word) (of : Z -> Z)
      (x1 x5 x6 x7 x10 x11 x16 x17 x25 x28 x29 x30 x31 : word),
    1 <= mx ->
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 (Z_to_bv 64 (S + 160)) v128 v136 (Z_to_bv 64 F)
            cA of lf w1 cf (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ->
    evtF bsegs RNG (switch_post v0 v8 v16 v128 v136 of)
      (ST x1 x5 x6 x7 x10 x11 (Z_to_bv 64 mn) SHPB (Z_to_bv 64 rt) (Z_to_bv 64 mx) x16 x17 x25 x28 x29 x30 x31 0x9702c m).
  Proof using All.
    intros until x31. intros Hmx INV. open_ctx CX. open_inv INV. unfold bst.
    destruct (ty_cases ty S) as [(ET & ECT & EM & EEX & EBS & ENE & EL & ED) | [(ET & ECT & EM & EEX & EBS & ENE & EL & ED) | (ET & ECT & EM & EEX & EBS & ENE & EL & ED)]].
    (* [U14B] A2 2026-11-12: zlib 1.4's switch(type) in the combined image: DISTS first (0x97040 beq s7,2 -> 0x97090), then
       the flag := 1 (0x9704c), LENS (0x97050 beq s7,1 -> 0x97070), default (0x97054 bnez s7), and CODES in line: null
       base / flag / extra and match = 20 (0x97058 .. 0x9706c). *)
    - (* CODES *)
      zs. zs. zbr K. zs. zs. zs. zs. zbr K1. zs. zbr K2. do 6 zs.
      eapply (it_init _ v0 v8 v16); [exact Hmx|].
      rewrite EBS, EEX, EM. replace (XFL ty) with 0 by (rewrite ET; reflexivity).
      unfold itb_inv, itb_W, frm19. do 10 (split; [try eassumption|]); try eassumption.
    - (* LENS *)
      zs. zs. zbr K. zs. zs. zs. zs. zbr K1. do 10 zs.
      eapply (it_init _ v0 v8 v16); [exact Hmx|].
      rewrite EBS, EEX, EM. replace (XFL ty) with 1 by (rewrite ET; reflexivity).
      unfold itb_inv, itb_W, frm19. do 10 (split; [try eassumption|]); try eassumption.
    - (* DISTS *)
      zs. zs. zbr K. do 10 zs.
      eapply (it_init _ v0 v8 v16); [exact Hmx|].
      rewrite EBS, EEX, EM. replace (XFL ty) with 1 by (rewrite ET; reflexivity).
      unfold itb_inv, itb_W, frm19. do 10 (split; [try eassumption|]); try eassumption.
  Qed.
End P.
End CANSEC1.
