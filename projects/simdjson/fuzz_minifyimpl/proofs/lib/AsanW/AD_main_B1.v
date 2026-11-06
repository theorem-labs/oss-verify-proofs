(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree Keeps FmtFp F_fmt_fp_lib Printf_fmts Printf_pieces.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AU_kit AU_iface AHarnessU_iface F_syscalls StdioFiles Stdio_kit Stdio_kit2 Stdio_iface F_printf_iface MonadF Strnlen_iface I_printf_formats I_read I_memcpy ADriver_iface AD_kit AD_ctx AD_diag AD_main_A.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Set Keyed Unification.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac fix_ret := match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  lazymatch n with Zpos _ => idtac end; replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Notation wz := (Z_to_bv 64).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 ATP).


(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {XP : ExitParams}.
Definition AS_OOM : Z := 0x15007.    Definition s_oom : list Z := (str "cli: out of memory"%string ++ [10])%list.
Definition AS_SHORT : Z := 0x21df3.  Definition s_short : list Z := (str "cli: input shorter than header"%string ++ [10])%list.
Definition AS_OVER : Z := 0x163be.   Definition s_over : list Z := (str "cli: config_len overruns input"%string ++ [10])%list.
Lemma s_oom_ro : ro_bytes_b asegs AS_OOM (zb s_oom) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_short_ro : ro_bytes_b asegs AS_SHORT (zb s_short) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_over_ro : ro_bytes_b asegs AS_OVER (zb s_over) = true. Proof. vm_compute. reflexivity. Qed.
Lemma str_range : forall s, Forall (fun c => 0 <= c < 256) (str s).
Proof.
  intros s. unfold str. induction (list_ascii_of_string s) as [|a l IH]; cbn; constructor; [| exact IH].
  pose proof (Ascii.N_ascii_bounded a). lia.
Qed.

(* [comment removed for export] *)
Lemma implMA_loop_S : forall {X R} RNG fuel (body : X -> @Monad.M APS (X + R)) x s (Q : R -> APS -> footprint -> machine_state -> Prop) ms,
  implMA RNG (body x) s (fun r s' RNG' ms' => match r with
                                        | inl x' => implMA RNG' (mloop fuel body x') s' Q ms'
                                        | inr v => evtF asegs RNG' (Q v s' RNG') ms'
                                        end) ms ->
  implMA RNG (mloop (S fuel) body x) s Q ms.
Proof.
  intros X R RNG fuel body x s Q ms H. cbn [mloop]. eapply implMA_bind; [exact H|].
  cbv beta. intros [x'|v] s' RNG' ms' H'; [exact H'| apply implMA_ret; exact H'].
Qed.
(* [comment removed for export] *)
Lemma implMA_mret_bind : forall {A B} RNG (a : A) (f : A -> @Monad.M APS B) s Q ms,
  implMA RNG (f a) s Q ms -> implMA RNG (mbind (mret a) f) s Q ms.
Proof. intros A B RNG a f s Q ms H. exact H. Qed.

(* [comment removed for export] *)
Section B.
  (* [comment removed for export] *)
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Variables (usp TID : Z) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) (RSTK : region) (canary : word) (L : alayout).
  Hypothesis RSTK_lo : r_lo RSTK <= ALO usp.
  Hypothesis RSTK_hi : usp + -112 <= r_hi RSTK.
  Hypothesis RSTK_rlo : ATOP <= r_rlo RSTK.
  Hypothesis USP16 : usp mod 16 = 0.
  Hypothesis USPLO : ATOP + 8388608 <= usp.
  Hypothesis USPHI : usp + 24 <= 2^47.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.
  Hypothesis URI_CI : forall iv, In iv uri_img_ranges -> In iv CI.
  Hypothesis CI_WF : forall iv, In iv CI -> 0 <= fst iv.
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis SPG : usp = al_sp0 L.
  Hypothesis BOT : ATOP + 4096 <= ALO usp.
  (* [comment removed for export] *)
  Hypothesis XSLO : xp_SLO <= ALO usp.
  Hypothesis XSHI : usp <= xp_SHI.
  Hypothesis HUXL : HUX L.
  Hypothesis SPTOP : In [AFREE_PC] (al_U L).        (* [comment removed for export] *)
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis FUZZ : fuzz_oneU_stmt AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.
  Variables (argv : list (list byte)) (P0 P1 : Z) (slack0 slack1 : list byte) (RA0 RA1 : region).
  Hypothesis VARGV : valid_argv argv.
  Notation argc := (Z.of_nat (length argv)).
  Notation arg0 := (map bv_unsigned (nth 0 argv [])).
  Notation arg1 := (map bv_unsigned (nth 1 argv [])).
  (* [comment removed for export] *)
  Variable J8 : list byte.
  Notation ABASE' := (ABASE usp TID S0 S1 S2 S3 S4 S5 S6 S7 J8 RSTK canary).
  Notation AMFRAME' := (AMFRAME usp S0 S1 S2 S3 S4 S5 S6 S7 J8).
  Notation LO := (ALO usp).
  Notation RNGS' := (RNGS rng_fs usp RSTK L argv P0 P1 slack0 slack1 RA0 RA1).
  Notation AARGV' := (AARGV usp argv P0 P1 slack0 slack1 RA0 RA1).
  Let WOKo := WOK_outside usp USP16 USPLO USPHI.
  Let geoA' := geoA usp USP16 USPLO USPHI.
  (* [comment removed for export] *)
  Hypothesis UM_e48 : In [AMALLOC_PC; 0xb0a0c] (al_U L).
  Hypothesis UM_e9c : In [AMALLOC_PC; 0xb0a60] (al_U L).
  Hypothesis UF_ec0 : In [AFREE_PC; 0xb0a84] (al_U L).
  Hypothesis UF_ff0 : In [AFREE_PC; 0xb0bb4] (al_U L).
  Hypothesis UM_14c : In [AMALLOC_PC; 0xb0cec] (al_U L).
  Hypothesis UF_1a0 : In [AFREE_PC; 0xb0d80] (al_U L).
  Hypothesis UM0 : In [AMALLOC_PC] (al_U L).
  Hypothesis UF0 : In [AFREE_PC] (al_U L).
  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  (* [comment removed for export] *)

  Notation ioS := (ioA AAllocAsan).

  (* [comment removed for export] *)
  Definition BUF (mm : amem) (s : APS) (RNG : footprint) (bufp : AsanCtrl.aptr) (A cap : Z) (DATA junk : list byte) : Prop :=
    AHEAP AI L RNG (aps_m s) [HB bufp A cap] mm /\ aps_so0 s /\ aps_ok L s /\ A = aptr_addr_M s bufp
    /\ rw_cells asegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
    /\ (65536 <= cap <= MAX_INPUT /\ exists k, 0 <= k /\ cap = 2 ^ k) /\ Z.of_nat (length DATA) <= cap /\ ablock_range A cap
    /\ rng RNG A cap /\ rng RNG (shad A) (shlen (cap + 7)).

  (* [comment removed for export] *)
  Definition STAGE (mm : amem) (sj : list byte) : Prop := rw_cells asegs mm ASTAGE [CB ASTAGE_LEN sj].

  (* [comment removed for export] *)
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 ASTAGE) x23 t3 t4 t5 t6 F fc mm).

  (* [comment removed for export] *)
  Definition RDINV (fd : Z) (st : rd_st) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : amem)
           (A : Z) (DATA junk : list byte) (sj : list byte) (pc : Z),
      ms = RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (zlength (rd_content st)) fd (rd_cap st) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm
      /\ ((pc = 0xb0a40 /\ x9 = Z_to_bv 64 A) \/ (pc = 0xb0a20 /\ rd_content st = []))
      /\ rd_content st = map bv_unsigned DATA
      /\ BUF mm s RNG (rd_buf st) A (rd_cap st) DATA junk /\ STAGE mm sj
      /\ ABASE' stdout_init mm /\ AARGV' mm /\ RNGS' RNG /\ frm0 fc.

  (* [comment removed for export] *)
  Definition RDBRK (fd : Z) (bufp : AsanCtrl.aptr) (content : list Z) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : amem)
           (A cap : Z) (DATA junk : list byte),
      ms = RST 0xb0aac x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA
      /\ BUF mm s RNG bufp A cap DATA junk
      /\ ABASE' stdout_init mm /\ AARGV' mm /\ RNGS' RNG /\ frm0 fc.

  Definition POSTBODY (fd : Z) (r : rd_st + rd_result) (s : APS) (RNG : footprint) (ms : machine_state) : Prop :=
    match r with
    | inl st' => RDINV fd st' s RNG ms
    | inr RdExit => aat_exit AI 2 s RNG ms
    | inr (RdDone b c) => RDBRK fd b c s RNG ms
    end.

  (* [comment removed for export] *)
  Definition rd_read_part (fd : Z) (path : list Z) (st1 : rd_st (ptr:=AsanCtrl.aptr)) : @Monad.M APS (rd_st + rd_result (ptr:=AsanCtrl.aptr)) :=
    let len := zlength (rd_content st1) in
    let want0 := rd_cap st1 - len in
    let cnt := if 65536 <? want0 then 65536 else want0 in
    a <- msys (NRead fd ASTAGE cnt) (dec_read ASTAGE cnt) ;;
    match a with
    | RdErr _ => io_diag ioS (DReadError path) ;;; mret (inr RdExit)
    | RdData bs =>
        if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
        else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
    end.

  Definition rd_grow_part (st : rd_st) : @Monad.M APS (option rd_st) :=
    if zlength (rd_content st) =? rd_cap st then
      if MAX_INPUT <=? rd_cap st then io_diag ioS DTooBig ;;; mret None
      else
        nb <- amalloc_M (rd_cap st * 2) ;;
        match nb with
        | None => io_diag ioS DOom ;;; mret None
        | Some nb' => afree_M (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
        end
    else mret (Some st).

  Lemma read_loop_body_eq : forall fd path st,
    read_loop_body ioS amalloc_M afree_M ASTAGE fd path st
    = (g <- rd_grow_part st ;; match g with None => mret (inr RdExit) | Some st1 =>
         let want0 := rd_cap st1 - zlength (rd_content st) in
         let cnt := if 65536 <? want0 then 65536 else want0 in
         a <- msys (NRead fd ASTAGE cnt) (dec_read ASTAGE cnt) ;;
         match a with
         | RdErr _ => io_diag ioS (DReadError path) ;;; mret (inr RdExit)
         | RdData bs =>
             if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
             else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
         end end).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma afprintf_exit : forall (d : diag_msg) {R} (K : @Monad.M APS R) (Q : R -> APS -> footprint -> machine_state -> Prop) (s : APS) (LB : list ablock) RNG
      x1 t0 t1 t2 x9 (a1v a2v : word) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : amem),
    adiag_args RNG d mm a1v a2v LO (usp + -128) ->
    ABASE' stdout_init mm -> AHEAP AI L RNG (aps_m s) LB mm -> aps_so0 s -> frm0 fc -> RNGS' RNG ->
    (forall b, In b LB -> exists q A n, b = HB q A n) -> aps_ok L s ->       (* [comment removed for export] *)
    (forall ms', aat_exit AI 2 s RNG ms' -> implMA RNG K s Q ms') ->
    implMA RNG (s_diag d ;;; K) s Q
      (GST 0xb0c18 x1 t0 t1 t2 x9 (Z_to_bv 64 RSTDERR) a1v a2v x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros DA BA AH SO FRM RG HBO RK HK.
    pose proof geoA' as (G1 & G2 & G3 & G4 & G5). unfold KHIGH in *.
    pose proof BA as (ST & MI & FR & AS & SE & GU & TR & HI & ROD & RCS & RCB & RSG & ERR & SOF).
    pose proof RG as (RGstk & RGtop & RGimg & RGimsh & RGfs & RRS & RRF & RRB & RG0 & _ & _ & _ & RGX).
    destruct (drv_got_of_aheap AI _ _ _ _ _ AH) as (_ & _ & _ & GSSP).
    apply implMA_from_evtF. zstep. apply evtF_done.
    eapply implMA_bind.
    { apply implMA_of_implAM.
      eapply (afprintf_diag_proof HSTRN RNG RSTK d) with (lo := LO); rewrite ?unsigned_lit by lia;
        first [ apply stderr_wfile0_wfile; exact SE | reflexivity | exact DA | exact ST | exact MI | exact RCS | exact ROD | exact RGimg | exact RG0 | exact RRS | exact RRF
              | split; [exact GSSP| exact GU] | exact (ASHENV _ _ _ _ _ AH) | exact FRM | idtac ].
      all: first [ unfold AFPRINTF_DEPTH; lia | unfold KHIGH; lia | eapply rng_sub'; [exact RGstk| lia] ]. }
    cbv beta. intros [] st' RNG' ms' [-> PO].
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MU2 & WM2 & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ->).
    rewrite ?unsigned_lit in MU2, ST2 by lia. fix_ret.
    assert (HW2 : Forall (WOK usp) [(LO, usp + -128); (RSTDERR, RSTDERR + 232)]) by (constructor; [left; cbn; lia| constructor; [right; right; left; cbn; split; reflexivity| constructor]]).
    assert (AH2 : AHEAP AI L RNG (aps_m s) LB m2).
    { eapply (AI_frame AI); [exact AH| exact MU2| exact WM2|].
      pose proof (AI_layout AI _ _ _ _ _ AH) as (Y1 & Y2 & Y3 & Y4 & _).
      constructor; [| constructor; [| constructor]]; cbn [fst snd].
      + left. left. lia.
      + left. right; left. exists (RSTDERR, RSTDERR + 232)%Z. split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia]. }
    destruct (after_diag AI usp TID S0 S1 S2 S3 S4 S5 S6 S7 RSTK canary USP16 USPLO USPHI _ _ _ _ _ _ _ _ _ _ _ _ BA HW2 MU2 WM2 AH2 AH) as (FR2 & AS2 & SOF2 & HI2 & RCL2 & TX2).   (* [comment removed for export] *)
    apply implMA_from_evtF.
    (* [comment removed for export] *)
    zstep.
    eapply evtF_mono; [| intros ms'' H; exact (HK ms'' H)].
    eapply (aexit2_tail AI usp TID RSTK RSTK_lo RSTK_hi RSTK_rlo USP16 USPLO USPHI canary XSLO XSHI) with (L := L) (LB := LB);
      first [exact ST2 | exact AS2 | exact MI2 | exact HT | exact RGimg | exact RGimsh | exact RG0
            | exact (proj1 HI2) | exact (exit_tableA_of_inv0 _ _ _ HI2 (proj2 SO)) | exact HBO | exact RK | exact FRM2 | exact RCL2 | exact RRS | exact HUXL | exact RGtop | exact RGX | exact SPTOP
            | idtac].
    - exact AH2.
    - rewrite (proj1 SO). exact SOF2.
    - apply stderr_wfile_file. exact SEW.
    - exact (proj2 SSP2).
    - eapply rng_sub'; [exact RGstk| lia].
    - exact TX2.                                           (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
(* [comment removed for export] *)
End B.
End CANSEC1.
