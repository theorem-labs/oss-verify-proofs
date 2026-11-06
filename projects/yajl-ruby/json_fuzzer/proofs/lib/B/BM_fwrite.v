(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac ITree Nodes Decode SysStep SFModel MonadX SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages ITreeA NodesA SysStepA MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BM_monadx BM_syscalls BM_stdio_lib BX_file BM_stdio_write.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation GLOBALS_TOP := 0x603000%Z (only parsing).



(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition towrite_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (flags mode : word) (wend wpos wbase writefn buf bufsize fd lbf : Z) (tail : list byte) (P : acc -> Prop),
    (forall a k, bv_unsigned a0 <= a -> a + Z.of_nat k <= bv_unsigned a0 + 232 -> P (Z_to_bv 64 a, k)) ->
    rw_cells bsegs m (bv_unsigned a0) (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
    mem_inv bsegs m ->
    evtA bsegs P (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom bsegs)
                 /\ munch [(bv_unsigned a0, bv_unsigned a0 + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
                 /\ rw_cells bsegs m' (bv_unsigned a0) (file_cells flags (buf + bufsize) buf buf writefn buf bufsize fd mode' lbf tail))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x98a28) fc None m (seg_rom bsegs)).

End RC__1.
Ltac if_lit :=
  lazymatch goal with
  | |- evtA _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Theorem towrite_proof : towrite_stmt.
Proof.
  unfold towrite_stmt. intros until P. intros PFILE FC NOWR B0 BHI BS0 MI.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size file_cells csize Nat.add] in FB.
  set (Fp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold file_cells in FC.
  assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
  { unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
    rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
  do 5 zs. rewrite FL8. zs. zs. if_lit.
  do 10 zs.
  apply evtA_done. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold file_cells. match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | let t := type of H in idtac "FC:" t; fail] end.
Qed.

(* [comment removed for export] *)
Definition fwx_nofit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp S l wfn lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 wfn) t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 wfn) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma fwx_nofit : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z) (P : acc -> Prop),
  (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, Fp <= a -> a + Z.of_nat k <= Fp + 232 -> P (Z_to_bv 64 a, k)) ->
  rw_cells bsegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
  (0 < wend < 2^64) -> (0 <= wpos <= wend) -> (wend - wpos < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
  mem_inv bsegs m ->
  (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  evtA bsegs P (fwx_nofit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp S l wfn lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x98838) fc None m (seg_rom bsegs)).
Proof.
  intros until P. intros PSTK PFILE FC -> -> -> WEND WPOS L SR WFN WFE ST LO LO0 MI SEPF.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  unfold file_cells in FC.
  carve_frame 64%nat ST.
  do 13 step.
  if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
  do 3 step.
  if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
  do 13 step.
  rewrite (ret_pc_even wfn) by (first [lia | exact WFE]).
  release_frame FR ST (bv_unsigned sp).
  unfold fwx_nofit_post. sys_finish.
Qed.



(* [comment removed for export] *)
Definition FWRITE_DEPTH : Z := 240.

Section Fwrite.
  Context {St : Type}.

  Definition fwrite_diag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ stderr_wfile0 m'
      /\ ssp_cells m' canary
      /\ st' = st.

  (* [comment removed for export] *)
  Definition fwrite_diag_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word) (s : list Z) (P : acc -> Prop),
      (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
      (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
      (forall a k, bv_unsigned a0 <= a -> a + Z.of_nat k <= bv_unsigned a0 + zlength s -> P (Z_to_bv 64 a, k)) ->
      (forall a, P (Z_to_bv 64 a, 0%nat)) ->
      towrite_stmt ->
      stderr_wfile0 m ->
      bytes_at bsegs m (bv_unsigned a0) (zb s) -> Forall (fun c => 0 <= c < 256) s -> 0 < zlength s < 2^31 ->
      a1 = Z_to_bv 64 (zlength s) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 RSTDERR ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 0x800000000000) (* [comment removed for export] *) ->
      (bv_unsigned a0 + zlength s <= lo \/ (bv_unsigned sp <= bv_unsigned a0 /\ bv_unsigned a0 + zlength s <= 0x800000000000)) ->
      (bv_unsigned a0 + zlength s <= RSTDERR \/ RSTDERR + 232 <= bv_unsigned a0) ->
      ssp_cells m canary -> mem_inv bsegs m ->
      implMA bsegs P (stderr_fwrite s : M St unit) st
            (fwrite_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x98970) fc None m (seg_rom bsegs)).
End Fwrite.

Lemma bv_eqb_refl' : forall (x : word), bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.



(* [comment removed for export] *)
Lemma implMA_post_evt'' : forall {St A} P (c : M St A) s Q Q' ms,
  implMA bsegs P c s Q ms -> (forall a s' ms', Q a s' ms' -> evtA bsegs P (Q' a s') ms') ->
  implMA bsegs P c s Q' ms.
Proof.
  intros St A P c s Q Q' ms H HQ. unfold implMA in *. eapply implA_extend_epost; [exact H|].
  intros [a s'] ms' H'; cbn in *. apply HQ; exact H'.
Qed.

Section WithTowrite.
  Hypothesis TW : towrite_stmt.

  (* [comment removed for export] *)
  Lemma fwx_nofit0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (Fp : Z) (flags : word) (wpos wbase wfn bufp fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z) (P : acc -> Prop),
    (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
    (forall a k, Fp <= a -> a + Z.of_nat k <= Fp + 232 -> P (Z_to_bv 64 a, k)) ->
    rw_cells bsegs m Fp (file_cells flags 0 wpos wbase wfn bufp 0 fd mode lbf tail) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
    (0 < bufp < 2^63) -> (0 < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
    stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
    mem_inv bsegs m ->
    (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
    evtA bsegs P (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' (Z_to_bv 64 wfn) t2' s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (Z_to_bv 64 wfn) fc None m' (seg_rom bsegs)
                 /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
                 /\ stk bsegs m' lo (bv_unsigned sp)
                 /\ rw_cells bsegs m' Fp (file_cells flags bufp bufp bufp wfn bufp 0 fd mode' lbf tail))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x98838) fc None m (seg_rom bsegs)).
  Proof.
    intros until P. intros PSTK PFILE FC FL8 -> -> -> BUFP L SR WFN WFE ST LO LO0 MI Fp0 SEPF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size file_cells csize Nat.add length] in BF.
    unfold file_cells in FC.
    carve_frame 64%nat ST.
    do 13 step.
    if_lit.
    step. step.
    eapply evtA_cut.
    { eapply (TW _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (buf := bufp) (bufsize := 0);
        [ intros a k H1 H2; rewrite unsigned_lit in H1, H2 by (clear - BF Fp0; lia); apply PFILE; lia
        | rewrite unsigned_lit by (clear - BF Fp0; lia); exact FC | exact FL8 | lia | lia | lia | exact MI ]. }
    cbv beta. intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode' & m1 & -> & MU1 & WM1 & MI1 & FC1).
    rewrite unsigned_lit in MU1, FC1 by lia.
    change (ret_pc (Z_to_bv 64 0x988f4)) with (ret_pc (Z_to_bv 64 0x988f4)).
    rewrite (ret_pc_even 0x988f4) by (cbn; lia).
    transport_after_call bsegs m0 m1 MU1 WM1.
    unfold file_cells in FC1.
    step. if_lit.
    do 5 step.
    if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?land_W64, ?Z.mod_small in Hr by lia. clear - Hr L. lia. }
    do 13 step.
    rewrite (ret_pc_even wfn) by (first [lia | exact WFE]).
    release_frame FR ST (bv_unsigned sp).
    apply evtA_done. do 12 eexists. exists m1.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST|].
    unfold file_cells. rewrite ?Z.add_0_r in FC1. exact FC1.
  Qed.
End WithTowrite.

Lemma zb_length' : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.

Lemma land8_of_land40 : forall f, Z.land f 40 = 0 -> Z.land f 8 = 0.
Proof.
  intros f H. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec i 3) as [->|NE].
  - pose proof (f_equal (fun z => Z.testbit z 3) H) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
    change (Z.testbit 8 3) with true. change (Z.testbit 40 3) with true in T. exact T.
  - change 8 with (2^3). rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 3 i); [lia|]. apply Bool.andb_false_r.
Qed.

Theorem fwrite_diag_proof {St : Type} : @fwrite_diag_stmt St.
Proof.
  unfold fwrite_diag_stmt. intros until P. intros PSTK PIMG PSRC PNUL TW W0 SRC BYT LS -> -> -> ST LO GLO SPHI SEPS1 SEPS2 SSP MI.
  destruct W0 as (flags & mode & e & wend & tail & FC & FL40 & WEND & HE).
  pose proof (land8_of_land40 _ FL40) as FL8.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length' in BS.
  assert (LSB : length (zb s) = length s) by apply zb_length'.
  set (S := bv_unsigned a0) in *.
  assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
  unfold FWRITE_DEPTH in *. unfold zlength in *.
  destruct SSP as [GOT GUARD]. idtac. unfold got_ssp, ssp_guard in GOT, GUARD.
  unfold stderr_fwrite. unfold zlength.
  replace (0 <? Z.of_nat (length s)) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  unfold file_cells in FC.
  rewrite EA0.
  apply implMA_from_evtA.
  carve_frame 64%nat ST.
  do 8 step. do 3 step. step. step. step. if_lit.
  step. step. step.
  rewrite (unsigned_lit (Z.of_nat (length s))) by (clear - LS; lia). rewrite Z.mul_1_l.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO; lia).
  (* [comment removed for export] *)
  eapply (evtA_cut bsegs P (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode1 : word) (m1 : mem),
      ms' = MS (mkR (Z_to_bv 64 0x989f8) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' (Z_to_bv 64 F_STDIO_WRITE) t2'
                    (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (length s)))
                    (Z_to_bv 64 RSTDERR) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length s))) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 RSTDERR) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 F_STDIO_WRITE) fc None m1 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp + -64); (RSTDERR, RSTDERR + 232)] m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1
      /\ stk bsegs m1 lo (bv_unsigned sp + -64)
      /\ rw_cells bsegs m1 RSTDERR (file_cells flags 0x601c58 0x601c58 0x601c58 F_STDIO_WRITE 0x601c58 0 2 mode1 0xffffffff tail))).
  { destruct WEND as [-> | [-> ->]].
    - eapply evtA_mono.
      { eapply (fwx_nofit0 TW) with (lo := lo) (Fp := 0xa9c68); [ intros a k H1 H2; rewrite ?ESP in H2; apply PSTK; lia | intros a k H1 H2; apply PIMG; lia
          | exact FC | exact FL8 | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
          [rewrite ESP; exact ST | exact MI]. }
      cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FC1).
      rewrite ESP in MU1, ST1.
      do 12 eexists. exists m1. split; [reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. exact FC1.
    - eapply evtA_mono.
      { eapply fwx_nofit with (lo := lo) (Fp := 0xa9c68); [ intros a k H1 H2; rewrite ?ESP in H2; apply PSTK; lia | intros a k H1 H2; apply PIMG; lia
          | exact FC | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
          [rewrite ESP; exact ST | exact MI]. }
      cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
      rewrite ESP in MU1, ST1.
      do 11 eexists. exists mode, m1. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia. }
      split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
      eapply (rw_cells_transport bsegs _ m0 m1); [exact FC | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FC1).
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0. fold S in RA0.
  assert (SRC1 : bytes_at bsegs m1 S (to_bytes s)).
  { eapply (bytes_at_transport bsegs _ m0 m1); [exact SRC | exact MU1 | cbn; rewrite ?LSB; unfold to_bytes; rewrite ?length_map; clear - SEPS1 SEPS2 LO GLO; lia]. }
  assert (GOT1 : rw_cells bsegs m1 680488 [C8 (Z_to_bv 64 6296976)]).
  { eapply (rw_cells_transport bsegs _ m0 m1); [exact GOT | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  assert (GUARD1 : rw_cells bsegs m1 6296976 [C8 canary]).
  { eapply (rw_cells_transport bsegs _ m0 m1); [exact GUARD | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
  assert (FC1' : rw_cells bsegs m1 RSTDERR (file_cells flags 0x601c58 (0x601c58 + zlength (@nil Z)) 0x601c58 F_STDIO_WRITE 0x601c58 0 2 mode1 0xffffffff tail)).
  { unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r. exact FC1. }
  clear FC1 GOT GUARD SRC.
  apply evtA_done.
  eapply implMA_post_evt''.
  { eapply (stdio_write_spec (St:=St)) with (lo := lo) (S := S) (canary := canary) (buf := []) (fd := 2) (P := P) (Fp := 0xa9c68) (B := 0x601c58) (bufsize := 0) (s := s);
      [ intros a k H1 H2; rewrite ?ESP in H2; apply PSTK; lia | exact PIMG | intros a k H1 H2; apply PIMG; lia | intros a k H1 H2; apply PIMG; lia
      | intros a k H1 H2; destruct k; [apply PNUL | apply PSRC; unfold zlength in *; lia]
      | exact FC1'
      | apply bytes_at_nil; clear; lia
      | exact SRC1
      | reflexivity | reflexivity | reflexivity
      | right; reflexivity
      | rewrite ESP; exact ST1 | rewrite ESP; unfold STDIO_WRITE_DEPTH; clear - LO; lia | exact GLO | rewrite ESP; clear - SPHI; lia
      | split; [exact GOT1 | exact GUARD1] | exact MI1
      | try (rewrite ?ESP; unfold got_ssp, ssp_guard, zlength in *; cbn [length Z.of_nat] in *; clear - LO GLO RA0 BS LS SEPS1 SEPS2 SPHI; lia) .. ]. }
  cbv beta. intros [] st2 ms2 PO2.
  destruct PO2 as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
  rewrite ESP in MU2, ST2. unfold STDIO_WRITE_DEPTH in MU2.
  rewrite (ret_pc_even 0x989f8) by (cbn; lia).
  assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply (rw_cells_transport bsegs _ m1 m2); [| exact MU2 | exact WM2 | cbn; clear - LO GLO RSP; lia].
    eapply (rw_cells_transport bsegs _ m0 m1); [exact FR | exact MU1 | exact WM1 | cbn; clear - LO GLO RSP; lia]. }
  clear FR. unfold file_cells in FC2.
  (* [comment removed for export] *)
  step. step. unfold zlength. rewrite (bv_eqb_refl' (Z_to_bv 64 (Z.of_nat (length s)))). cbv iota.
  do 4 step.
  do 9 step.
  release_frame FR2 ST2 (bv_unsigned sp).
  replace (v_sltiu (Z_to_bv 64 (Z.of_nat (length s))) 1) with (Z_to_bv 64 0 : word)
    by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1; destruct (Z.ltb_spec (Z.of_nat (length s)) 1); [exfalso; lia| reflexivity]).
  match goal with |- context [Z_to_bv 64 (Z.land ?x 1)] =>
    replace (Z_to_bv 64 (Z.land x 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity) end.
  apply evtA_done. unfold fwrite_diag_post.
  do 14 eexists. exists m2.
  split; [reflexivity|].
  split. { apply (munch_trans _ m m0 m2); [| apply (munch_trans _ m0 m1 m2)].
           - eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
           - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
           - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia. }
  split. { eapply wmono_trans; [exact WM | eapply wmono_trans; [exact WM1 | exact WM2]]. }
  split; [exact MI2|]. split; [exact ST2|].
  split.
  { exists flags, mode1, 0x601c58, 0x601c58, tail. split; [| split; [exact FL40 | split; [right; split; reflexivity | clear; lia]]].
    unfold file_cells. rewrite ?Z.add_0_r in FC2. exact FC2. }
  split; [exact SSP2 | reflexivity].
Qed.
End RC__2.
