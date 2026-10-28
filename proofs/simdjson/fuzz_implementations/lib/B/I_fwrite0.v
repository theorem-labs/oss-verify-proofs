(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small R_m2s R_thread I_consts RT_iface I_readw2 I_memcpyw D_kit FX_Layout FX_Stdio_iface Imp_xifaceA X_ixdefs X_ixdefs2 F_fwrite0A.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.

Lemma fwrite_walkA0 : forall (sp sa len errp : Z) (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk bsegs m lo sp -> 0x7fff7f800000 <= lo -> lo + 2304 <= sp -> sp <= 2^47 ->
  0 <= sa < 2^64 -> 0 <= len < 2^64 -> 0 <= errp < 2^64 ->
  rw_cells bsegs m 0x181d90 [C8 (Z_to_bv 64 0x168e70)] -> rw_cells bsegs m 0x18a658 [C1 (Z_to_bv 8 1)] -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (m' : mem) junk,
      ms' = MS (mkR (Z_to_bv 64 0x722cc) (Z_to_bv 64 (sp + -2128)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 len)
                    (Z_to_bv 64 sa) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 errp) (Z_to_bv 64 0x168e70) a5 a6 a7
                    (Z_to_bv 64 sa) (Z_to_bv 64 errp) (Z_to_bv 64 0) (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x168e70) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 2144, sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (sp + -2128) [CB 2072 junk]
      /\ rw_cells bsegs m' (sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ stk bsegs m' lo (sp + -2128))
    (entry_st ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sa) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 errp)
       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fwrite m).
Proof.
  intros until lo. intros ST LO0 LO UT Hsa Hlen Herr RF AI MI.
  unfold entry_st, e_fwrite. pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(sp - 2144, sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  carve_frame 56%nat ST. rename FR into FRt.
  carve_frame 2072%nat ST. rename FR into FRb.
  zhide.
  do 16 step.
  carve_frame 16%nat ST. rename FR into FRa.
  step. step. change (Z_to_le_bytes 8 467628) with (le8 (Z_to_bv 64 467628)). mem_after_store.
  step.
  do 6 step. if_false.
  do 4 step.
  release_frame FRa ST (sp + -2128).
  do 8 step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact FRb|]. split; [exact FRt| exact ST].
Qed.

Lemma fwrite_walkB0 : forall (sp sa len errp : Z) (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) junk,
  stk bsegs m lo (sp + -2128) -> 0x7fff7f800000 <= lo -> lo + 2304 <= sp -> sp <= 2^47 ->
  rw_cells bsegs m (sp + -2128) [CB 2072 junk] ->
  rw_cells bsegs m (sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom bsegs))
                 /\ stk bsegs m lo sp)
    (MS (mkR (Z_to_bv 64 0x722cc) (Z_to_bv 64 (sp + -2128)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 len)
             (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 sa) (Z_to_bv 64 errp) (Z_to_bv 64 0) (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x722cc) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST LO0 LO UT FRb FRt MI.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step. if_false.
  step. if_true.
  release_frame FRb ST (sp + -56).
  do 10 step.
  release_frame FRt ST sp.
  apply evt_done. split; [| exact ST]. do 14 eexists. reflexivity.
Qed.

Lemma ifw_finish : forall sp0 (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) (fc : bv 32) (m m1 m2 : mem) (Fp S lo FW : Z) (flags mode' : word) (WP wfn bufp bufsize fd lbf : Z) (tail junk : list byte),
  sp = Z_to_bv 64 usp ->
  stk bsegs m2 lo (usp + -2128) -> 0x7fff7f800000 <= lo -> lo + 2304 <= usp -> usp <= 2^47 ->
  munch [(usp - 2144, usp)] m m1 -> wmono bsegs m m1 ->
  munch [(lo, usp + -2128); (Fp, Fp + FW)] m1 m2 -> wmono bsegs m1 m2 -> FW <= 232 -> Fp + 232 <= lo ->
  rw_cells bsegs m1 (usp + -2128) [CB 2072 junk] -> rw_cells bsegs m1 (usp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv bsegs m2 ->
  rw_cells bsegs m2 Fp (file_cells flags (bufp + bufsize) WP bufp wfn bufp bufsize fd mode' lbf tail) ->
  (Fp = RSTDOUT \/ Fp = RSTDERR) -> sp0 - STACK_WIN <= lo -> ixit2 sp0 m ->
  evt bsegs (ifwrite0_post (ixit2 sp0) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags WP wfn bufp bufsize fd lbf tail lo m)
    (MS (mkR (Z_to_bv 64 0x722cc) (Z_to_bv 64 (usp + -2128)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 1)
             (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 S) (Z_to_bv 64 Fp) (Z_to_bv 64 0) (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x722cc) fc None m2 (seg_rom bsegs)).
Proof.
  intros until junk. intros ESP ST2 LO0 LO UT MU1 WM1 MU2 WM2 FWL FPL FRb FRt MI2 FC2 FPC XL IX.
  assert (FRb2 : rw_cells bsegs m2 (usp + -2128) [CB 2072 junk]).
  { apply (rw_cells_agree bsegs _ _ _ _ FRb); [| exact WM2]. apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [cells_size csize Nat.add length] in Hx. cbn [outside]. lia. }
  assert (FRt2 : rw_cells bsegs m2 (usp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree bsegs _ _ _ _ FRt); [| exact WM2]. apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [cells_size csize Nat.add length] in Hx. cbn [outside]. lia. }
  eapply evt_mono; [exact (fwrite_walkB0 usp S 1 Fp ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo junk
                              ST2 LO0 LO UT FRb2 FRt2 MI2)|].
  intros ms' ((v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & ->) & ST3). rewrite <- ESP.
  assert (MU : munch [(lo, usp); (Fp, Fp + 232)] m m2).
  { apply (munch_trans _ m m1 m2); [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros; lia. }
  unfold ifwrite0_post. exists v0, v1, v2, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, mode', m2.
  assert (EU : bv_unsigned sp = usp) by (rewrite ESP; apply unsigned_lit; lia).
  rewrite EU. split; [reflexivity|]. split; [exact MU|]. split; [exact (wmono_trans _ _ _ _ WM1 WM2)|]. split; [exact MI2|]. split; [exact ST3|].
  split; [exact FC2|].
  apply (IX2_frame sp0 _ lo usp m m2 IX MU (wmono_trans _ _ _ _ WM1 WM2) XL).
  intros x Hx. unfold XWI, XTPLOC in Hx. cbn [outside] in Hx |- *. destruct FPC as [-> | ->]; lia.
Qed.

Theorem ifwrite0_ok : forall sp0, ifwrite0_stmt (ixit2 sp0) (sp0 - STACK_WIN).
Proof.
  intros sp0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Fp S flags mode wend wpos wbase wfn bufp bufsize fd lbf tail lo
         FC WCASE LBF -> -> -> -> FPC B0 BS0 BSP BLO Fp0 FPB SR ST LOD GLO XL SPH [IXm XCm] MI.
  pose proof XCm as ((SPW & SPT) & RF & IC & GM & AB & AS). pose proof IC as (G2 & G1 & RM & SHC & RI).
  assert (AI : rw_cells bsegs m 0x18a658 [C1 (Z_to_bv 8 1)]) by (destruct IXm as (AI & _); exact AI).
  unfold g_REAL_fwrite, e_musl_fwrite, ICPT_DEPTH, STACK_WIN, GLOBALS_TOP in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  pose proof (stk_top_le m lo usp ST ltac:(lia) MI) as UT.
  pose proof (rw_cells_top_le m Fp _ FC MI ltac:(cbn; lia)) as FT. cbn [cells_size csize Nat.add file_cells length] in FT.

  eapply evt_cut.
  { eapply (fwrite_walkA0 usp S 1 Fp); first [ exact ST | exact RF | exact AI | exact MI | lia ]. }
  intros ms1 PO. destruct PO as (m1 & junk & -> & MU1 & WM1 & MI1 & FRb & FRt & ST1).
  assert (FC1 : rw_cells bsegs m1 Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail)).
  { apply (rw_cells_agree bsegs _ _ _ _ FC); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1). intros x Hx.
    cbn [cells_size csize Nat.add file_cells length] in Hx. cbn [outside]. lia. }
  assert (IC1 : icells m1).
  { split; [| split; [| split; [| split]]];
      (eapply ro_cells_agree; [eassumption|]; apply (agree_of_munch _ _ _ _ MU1); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; lia). }
  clear G2 G1 RM SHC RI RF AI.

  assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; lia).
  destruct WCASE as [[-> FL8] | (-> & -> & WPR)].
  - eapply evt_cut.
    { eapply (fwrite0_idle_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 Fp S flags mode wpos wbase wfn bufp bufsize fd lbf tail lo);
        first [ exact FC1 | exact FL8 | exact LBF | reflexivity | exact FPC | exact IC1 | exact MI1
              | rewrite ?EU1; first [ exact ST1 | unfold FWRITE0_DEPTH, kHighShadowEnd, GLOBALS_TOP; lia ] ]. }
    intros ms2 PO. unfold fwrite0_idle_post in PO. rewrite EU1 in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2).
    cbn [Z.eqb]. rewrite (ret_pc_even 0x722cc) by lia. eapply (ifw_finish sp0); try eassumption; unfold kHighShadowEnd; try lia; first [reflexivity | split; assumption].
  - cbn [Z.eqb]. replace (bufp + bufsize =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    eapply evt_cut.
    { eapply (fwrite0_active_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 Fp S flags wpos wfn bufp bufsize fd mode lbf tail lo);
        first [ exact FC1 | exact LBF | reflexivity | exact FPC | exact IC1 | exact MI1
              | rewrite ?EU1; first [ exact ST1 | unfold FWRITE0_DEPTH, kHighShadowEnd, GLOBALS_TOP; lia ] ]. }
    intros ms2 PO. unfold fwrite0_post in PO. rewrite EU1 in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2).
    rewrite (ret_pc_even 0x722cc) by lia. eapply (ifw_finish sp0); try eassumption; unfold kHighShadowEnd; try lia; first [reflexivity | split; assumption].
Qed.
