(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure ItA_base ItA_ldefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
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
  Notation ST := (bst SP SPA S F PB LP gp tp FR fc).
  Notation cntAr := (cntA lf lo codes).
  Notation cA := (arr_get (cntA lf lo codes)).
  Notation mx := (mxA lf lo codes).
  Notation mn := (mnA lf lo codes).
  Notation rt := (rootA lf lo codes bits).
  Notation w1 := (arr_get (work1A lf lo codes wf)).
  Notation SHPB := (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880)).
  Notation MST := (mst SP SPA S F PB LP gp tp FR fc rt mx).
  Notation MINV := (fun m st => minv SPA S F PB m1 m ty rt nx bits lf w1 st).

  (* rewritten for zlib 1.4's switch(type) / table init (0x9607c .. 0x96184, unc14.dis).  1.4
     checks root > 9 before it stores anything, stores null base / extra for CODES, sets match in t4 (stored to frame slot
     72 by init), keeps the constant 1 in s9 (1.3.1: t3), and enters the loop head with match still in t4. *)
  Definition head_post (st : ItSt) (v0 v96 v104 v112 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => exists (m : amem) (q1 q6 q7 q10 q11 q16 q17 q25 q28 : word),
      ms' = MST st q1 q6 q7 q10 q11 q16 q17 q25 q28 (Z_to_bv 64 (it_match ty)) 0x961b4 m /\ MINV m st v0 v96 v104 v112 of.

  Lemma it_reenter : forall (st : ItSt) (m : amem) (v0 v64 v80 v96 v104 v112 : word) (of : Z -> Z)
      (x1 x10 x11 x16 x17 x28 : word),
    1 <= t_curr st <= 15 -> (t_low st = 4294967295 \/ 0 <= t_low st < 32768) ->
    itb_inv SPA S F PB m1 m v0 (Z_to_bv 64 (isD ty)) (Z_to_bv 64 (isL ty)) (Z_to_bv 64 (Z.shiftr (S + 160) 3 + 2147450880))
            (Z_to_bv 64 (t_used st)) (Z_to_bv 64 (EXA ty S)) (Z_to_bv 64 (BSA ty S)) (Z_to_bv 64 (2 ^ rt - 1))
            v64 (Z_to_bv 64 (it_match ty)) v80 (Z_to_bv 64 (S + 160))
            v96 v104 v112 (arr_get (t_count st)) of lf w1 (arr_get (t_tbl st))
            (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ->
    evtF asegs RNG (head_post st v0 v96 v104 v112 of)
      (MST st x1 (Z_to_bv 64 (t_curr st)) (Z_to_bv 64 (lowS (t_low st))) x10 x11 x16 x17 (Z_to_bv 64 1) x28 (Z_to_bv 64 (it_match ty)) 0x961a4 m).
  Proof using All.
    intros until x28. intros HC HL INV. open_ctx CX. open_inv INV. unfold mst, bst.
    pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PC.
    zs. setreg 10 (Z_to_bv 64 (2 ^ t_curr st)) ltac:(rewrite sllw_1 by lia; reflexivity).
    zs. zs. rewrite (sextw_lowS (t_low st) HL).
    zs.
    apply evtF_done. unfold head_post. eexists. do 9 eexists. split; [reflexivity|]. unfold minv. close_inv.
  Qed.

  Notation st0 := (itm_st0 mn nx rt cntAr (tblA cf) (work1A lf lo codes wf)).

  Lemma it_init : forall (m : amem) (v0 v24 v32 v56 v64 v72 v80 v96 v104 v112 : word) (of : Z -> Z)
      (x1 x5 x6 x7 x10 x16 x17 x24 x25 x28 x29 x30 x31 : word),
    1 <= mx ->
    itb_inv SPA S F PB m1 m v0 (Z_to_bv 64 (isD ty)) (Z_to_bv 64 (isL ty)) v24 v32 (Z_to_bv 64 (EXA ty S)) (Z_to_bv 64 (BSA ty S)) v56
            v64 v72 v80 (Z_to_bv 64 (S + 160))
            v96 v104 v112 cA of lf w1 cf (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ->
    (* match in t4, stated as an equation so a caller with a literal match (after its ty case split) can supply it *)
    x29 = Z_to_bv 64 (it_match ty) ->
    evtF asegs RNG (head_post st0 v0 v96 v104 v112 of)
      (ST x1 x5 x6 x7 x10 (Z_to_bv 64 (S + 160)) SHPB (Z_to_bv 64 rt) (Z_to_bv 64 mx) (Z_to_bv 64 mn) x16 x17 x24 x25 x28
          x29 x30 x31 0x96160 m).
  Proof using All.
    intros until x31. intros Hmx INV HM. subst x29. open_ctx CX. open_inv INV. unfold bst.
    pose proof C as C'. open_itc C'.
    pose proof (rt_facts lf lo codes bits Hmx) as (RT & RT2 & RT3).
    pose proof (pow2_le15 rt ltac:(lia)) as PRT.
    zs. zs. zs. zs. zs.     (* srl / add / sd 24 / lbu / bnez: the table-pointer shadow *)
    zs. zs. zs. zs.         (* sym, drop, huff, the constant 1 *)
    zs.                     (* next = *table *)
    zs. setreg 10 (Z_to_bv 64 (2 ^ rt)) ltac:(rewrite sllw_1 by lia; reflexivity).
    zs. zs. setreg 10 (Z_to_bv 64 (2 ^ rt - 1)) ltac:(rewrite swrap32_small by lia; f_equal; lia).
    zs. zs. zs. zs.         (* sd 56 / curr / low / sd t4,72 *)
    apply (fun H => f32arr_ext asegs _ _ _ _ (arr_get (tblA cf)) H (fun j _ => eq_sym (tblA_get cf j))) in CDS.
    eapply (it_reenter st0); cbn [t_curr t_low t_used t_count t_tbl itm_st0].
    - lia.
    - left. reflexivity.
    - rewrite itm_used_pow2 by lia. unfold itb_inv, itb_W, frm15. do 10 (split; [eassumption|]). eassumption.
  Qed.

  Definition switch_post (v0 v96 v104 v112 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => (head_post st0 v0 v96 v104 v112 of ms' /\ it_not_enough ty (itm_used rt) = false)
      \/ (ret_pre SP SPA S F PB LP gp tp FR fc m1 1 lf w1 cf (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ms'
          /\ it_not_enough ty (itm_used rt) = true).

  Lemma it_switch : forall (m : amem) (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v96 v104 v112 : word) (of : Z -> Z)
      (x1 x5 x6 x7 x10 x11 x16 x17 x25 x28 x29 x30 x31 : word),
    1 <= mx ->
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 (Z_to_bv 64 (S + 160))
            v96 v104 v112 cA of lf w1 cf (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ->
    evtF asegs RNG (switch_post v0 v96 v104 v112 of)
      (ST x1 x5 x6 x7 x10 x11 SHPB (Z_to_bv 64 rt) (Z_to_bv 64 mx) (Z_to_bv 64 mn) x16 x17 (Z_to_bv 64 (cty ty)) x25 x28 x29 x30 x31 0x960ac m).
  Proof using All.
    intros until x31. intros Hmx INV. pose proof INV as INV0. open_ctx CX. open_inv INV. unfold bst.
    pose proof (rt_facts lf lo codes bits Hmx) as (RT & RT2 & RT3).
    pose proof (ne_pow ty rt RT) as NEP.
    destruct (ty_cases ty S) as [(ET & ECT & EM & EEX & EBS & ENE & EL & ED) | [(ET & ECT & EM & EEX & EBS & ENE & EL & ED) | (ET & ECT & EM & EEX & EBS & ENE & EL & ED)]];
      rewrite ECT.
    - (* CODES *)
      zrunb [0x96160].
      eapply evtF_mono; [eapply (it_init _ v0); [exact Hmx| | rewrite EM; reflexivity] | intros ms' HP; left; split; [exact HP | rewrite NEP, ET; first [reflexivity | destruct (Z.leb_spec rt 9); [reflexivity | lia]]]].
      rewrite ?ED, ?EL, ?EBS, ?EEX, ?EM. unfold itb_inv, itb_W, frm15. do 10 (split; [eassumption|]). eassumption.
    - (* LENS: root > 9 returns 1 before any store *)
      zrunb [0x960e0]. zs. zbr0 K9.
      + apply evtF_done. right. split; [| rewrite NEP, ET; destruct (Z.leb_spec rt 9); [lia | reflexivity]].
        unfold ret_pre. exists m. do 17 eexists. do 15 eexists. exists cA, of. split; [reflexivity | exact INV0].
      + zrunb [0x96160].
        eapply evtF_mono; [eapply (it_init _ v0); [exact Hmx| | rewrite EM; reflexivity] | intros ms' HP; left; split; [exact HP | rewrite NEP, ET; first [reflexivity | destruct (Z.leb_spec rt 9); [reflexivity | lia]]]].
        rewrite ?ED, ?EL, ?EBS, ?EEX, ?EM. unfold itb_inv, itb_W, frm15. do 10 (split; [eassumption|]). eassumption.
    - (* DISTS: root > 9 returns 1 before any store *)
      zrunb [0x96118]. zs. zbr0 K9.
      + apply evtF_done. right. split; [| rewrite NEP, ET; destruct (Z.leb_spec rt 9); [lia | reflexivity]].
        unfold ret_pre. exists m. do 17 eexists. do 15 eexists. exists cA, of. split; [reflexivity | exact INV0].
      + zrunb [0x96160].
        eapply evtF_mono; [eapply (it_init _ v0); [exact Hmx| | rewrite EM; reflexivity] | intros ms' HP; left; split; [exact HP | rewrite NEP, ET; first [reflexivity | destruct (Z.leb_spec rt 9); [reflexivity | lia]]]].
        rewrite ?ED, ?EL, ?EBS, ?EEX, ?EM. unfold itb_inv, itb_W, frm15. do 10 (split; [eassumption|]). eassumption.
  Qed.
End P.
End CANSEC1.
