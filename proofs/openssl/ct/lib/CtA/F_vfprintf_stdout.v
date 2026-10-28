(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import SFModel Arr SysStep FP ITree Nodes Decode. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_mlib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import FX_lib F_memset F_memcpy F_fwritex F_pop_arg F_printf_iface F_printf_core F_towrite F_pkit R_m2s I_consts F_achk.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_pieces.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Printf_stdio_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import PrintfModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
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
Local Ltac zidle_begin_rw sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call ctasegs m mm MU WM end end.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Ltac tslia ::= first [ exact I | clear_big; first [ tlia | split; [ tlia | exact I ] ] ].
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= clear_big; lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM ctasegs c s Q ms) | _ => idtac end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdoutSinkProofs.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Let SINK := SINK_stdout (St:=St) get_so.

  Lemma stdout_sink_frame : sink_frame_stmt RSTDOUT RSTDOUT_BUF 1024 SINK.
  Proof using get_so.
    unfold sink_frame_stmt. intros W m m' st (ACT & flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN) MU WM D1 D2.
    split; [exact ACT|]. exists flags, mode, tail, bufbytes.
    split; [|split; [exact FL | split; [| split; [exact PFX | exact LEN]]]].
    - eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
  Qed.


  Lemma stdout_sink_flags : sink_flags_stmt RSTDOUT SINK.
  Proof using get_so.
    unfold sink_flags_stmt. intros m st (ACT & flags & mode & tail & bufbytes & FC & FL & _).
    exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
    rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
    rewrite <- land_mod_low by lia. eapply land_sub_mask; [|exact FL]. reflexivity.
  Qed.

End StdoutSinkProofs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stdout.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.
  Hypothesis FWX : fwritex_stdout_stmt.
  Hypothesis RIP : rip_stmt.

  Let OUT := OUT_stdout get_so set_so.
  Let SINK := SINK_stdout (St:=St) get_so.

  Definition vfprintf_stdout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom ctasegs)
      /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk ctasegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ ssp_cells m' canary.

  Definition vfprintf_stdout_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      let q := bv_unsigned sp in
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
      stdout_file m (get_so st) ->
      bytes_at ctasegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 m lo q (q - VF_FRAME) slots args ->
      printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
      stk ctasegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
      ssp_cells m canary -> mem_inv ctasegs m -> frm0 fc ->
      (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
      (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      (* [comment removed for export] *)
      (kHighShadowEnd + 8 <= lo) -> ictx m -> (forall p n, lo <= p -> p + n <= q -> chkr m p n) ->
      chkr m A (zlength fmt) -> rod_chk m -> chkr m RSTDOUT_BUF 1024 ->
      Monad.implM ctasegs (stdout_towrite get_so set_so ;;; outsk OUT ps (mret tt)) st
        (vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x526dec) fc None m (seg_rom ctasegs)).

  Theorem vfprintf_stdout_proof : vfprintf_stdout_stmt.
  Proof using FWX GS SS RIP.
    unfold vfprintf_stdout_stmt. intros until canary. cbv zeta.
    intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI HSH IC STKC FMTC ROD CHBUF.
    unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
    pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU1.
    destruct SF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & PFX & BLEN & INACT). unfold file_cells in FC.
    pose proof (rw_CB_length _ _ _ _ BUF) as LBB.
    (* [comment removed for export] *)
    unfold stdout_towrite, upd_so. apply implM_upd_l.
    apply (printf_model_outs ctasegs OUT (OUTFP_stdout (St:=St)) fmt args ps r (fun _ => mret tt) _ _ _ PP).
    ienter.
    carve_frame 368%nat ST.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB ctasegs _ _ [] 368 junk [] [8; 8; 248; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    zidle_begin_rw sp 368%Z MUz WMz.
    do 12 zs. do 14 zs.
    zidle_end MUz WMz.
    (* [comment removed for export] *)
    pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
    eapply evt_cut.
    { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
        [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
    cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
    rewrite !unsigned_lit in MUc, STc by lia.
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call ctasegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    fix_ret.
    clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    (* [comment removed for export] *)
    zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit. zs. zs. zs.
    destruct (so_active (get_so st)) eqn:ACT.
    - (* [comment removed for export] *)
      if_lit. cbv beta iota in FC.
      zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app ctasegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      ileave.
      pose proof (printf_core_proof RIP St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                    (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
      unfold printf_core_stmt in PC2.
      assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
      { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      eapply implM_bind.
      { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
          clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
        all: try lia. all: try exact I.
        - unfold SINK, SINK_stdout. rewrite GS, ACT. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode, tail, bufbytes.
          split; [unfold file_cells; exact FC|]. split; [exact FL'|]. split; [exact BUF|]. split; [exact PFX | exact BLEN].
        - exact BY.
        - exact HF.
        - reflexivity.
        - replace (VA + 8 * 0) with VA by lia. exact APC.
        - exact VAA.
        - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1 | exact HSH | unfold SHADOW_LO; lia].
        - rewrite FPC. apply Forall_nil.
        - exact STc.
        - split; [exact SSP1 | exact SSP2].
        - assumption.
        - ictx_tr IC MU WM.
        - intros p n Hp1 Hp2. apply (chkr_munch _ m _ p n (STKC p n Hp1 ltac:(lia)) MU).
          intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia.
        - chkr_tr FMTC MU.
        - destruct ROD as (R1 & R2 & R3). split; [chkr_tr R1 MU | split; [chkr_tr R2 MU | chkr_tr R3 MU]].
        - chkr_tr CHBUF MU. }
      cbv beta. intros r' st' ms' P. clear PC2 MU1.
      unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
      destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
      unfold SR in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call ctasegs mm m3 MUc WMc; clear MUc WMc end.
      apply implM_ret. fix_ret.
      destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
      clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
      (* [comment removed for export] *)
      zs. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
      zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
      do 9 zs.
      (* [comment removed for export] *)
      replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
        by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
      change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
      rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
      (* [comment removed for export] *)
      lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
        assert (FALL : rw_cells ctasegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app ctasegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
        | clear AP FR ] end.
      cbn [app] in FALL.
      release_frame FALL ST3 (bv_unsigned sp).
      apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
      split; [exact ST3|].
      split.
      { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
        rewrite ACT3. split; [unfold file_cells; exact FC3|].
        split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
        rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
        pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
        unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
        split; [apply Z.lor_nonneg; lia|].
        apply (lor_lt_pow2 _ _ 64); lia. }
      split; [exact SSP1 | exact SSP2].
    - (* [comment removed for export] *)
      if_lit. cbv beta iota in FC. zs. zs. zs.
      pose proof towrite_proof as TW. unfold towrite_stmt in TW.
      eapply evt_cut.
      { eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
        rewrite unsigned_lit; [apply flags_noerr_nowr; exact FL72|].
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      cbv beta. intros ms' P. clear TW.
      destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
      rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call ctasegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
      fix_ret.
      zs. if_lit. zs. zs. zs. zs. zs. zs.
      apply (proj1 (rw_cells_app ctasegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
      replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
      ileave.
      pose proof (printf_core_proof RIP St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
                    (stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
      unfold printf_core_stmt in PC2.
      assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
      { rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
        unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
      eapply implM_bind.
      { eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
          clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
        all: try lia. all: try exact I.
        - unfold SINK, SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [reflexivity|].
          exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, bufbytes.
          change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
          split; [exact FCt|]. split; [exact FL'|]. split; [exact BUF|]. split; [reflexivity | lia].
        - exact BY.
        - exact HF.
        - reflexivity.
        - replace (VA + 8 * 0) with VA by lia. exact APC.
        - exact VAA.
        - cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1 | exact HSH | unfold SHADOW_LO; lia].
        - rewrite FPC. apply Forall_nil.
        - exact STc.
        - split; [exact SSP1 | exact SSP2].
        - assumption.
        - ictx_tr IC MU WM.
        - intros p n Hp1 Hp2. apply (chkr_munch _ m _ p n (STKC p n Hp1 ltac:(lia)) MU).
          intros ?x ?Hx; cbn [outside]; unfold SHADOW_LO, SHADOW_HI, kHighShadowEnd in *; lia.
        - chkr_tr FMTC MU.
        - destruct ROD as (R1 & R2 & R3). split; [chkr_tr R1 MU | split; [chkr_tr R2 MU | chkr_tr R3 MU]].
        - chkr_tr CHBUF MU. }
      cbv beta. intros r' st' ms' P. clear PC2 MU1.
      unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
      destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
      unfold SR in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mm _ => transport_after_call ctasegs mm m3 MUc WMc; clear MUc WMc end.
      apply implM_ret. fix_ret.
      destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
      clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
      (* [comment removed for export] *)
      zs. zs. zs. if_lit.
      zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
      zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
      do 9 zs.
      (* [comment removed for export] *)
      replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
        by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
      change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
      rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
      (* [comment removed for export] *)
      lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
        assert (FALL : rw_cells ctasegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
        [ apply (proj2 (rw_cells_app ctasegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
        | clear AP FR ] end.
      cbn [app] in FALL.
      release_frame FALL ST3 (bv_unsigned sp).
      apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
      split; [exact ST3|].
      split.
      { exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
        rewrite ACT3. split; [unfold file_cells; exact FC3|].
        split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
        rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
        pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
        unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
        pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
        split; [apply Z.lor_nonneg; lia|].
        apply (lor_lt_pow2 _ _ 64); lia. }
      split; [exact SSP1 | exact SSP2].
  Qed.
End Stdout.
