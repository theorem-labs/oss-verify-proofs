(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SBase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZGo11 SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.

Module S_ClDefs.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* THE LIST FORM: a register fact of a statement is "the meaning of the layout's list" (`rholds`), over the
   values that the statement binds (`qargs`, `qvalv`). *)
Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Notation qargs := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs (only parsing).
Notation qvalv := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (only parsing).
(* TWO OPENERS (they only unfold, split and name): every list-form hypothesis, and a list-form goal *)
Ltac gb_open :=
  repeat match goal with
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd nth
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_cl OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_cld
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_ll_head OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_ll_kx OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_ll_kd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_ll_body OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_fl_head OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_fl_k
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tl_head OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tl_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tl_dn
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_llt OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_llfill OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_llsetup
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tbody OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tbody_jb] in H;
             icx_cbn; destr_conj H
         end;
  zgetl_nil.
Ltac gb_split :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd nth
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_cl OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_cld
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_ll_head OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_ll_kx OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_ll_kd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_ll_body OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_fl_head OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_fl_k
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tl_head OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tl_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tl_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_llt OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_llfill OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_llsetup
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tbody OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tbody_jb];
  icx_cbn; split_conj.
(* A CLOSER: a list-form goal at a state whose list-form facts are in hand, up to the kit's linear arithmetic *)
Ltac gb_relist := gb_open; gb_split; cbv beta iota delta [zget_l alookup]; zkept.
Notation L_CL_HEAD := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_HEAD (only parsing).
Notation L_CL_DONE := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_DONE (only parsing).

Definition s_regs_cl (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  s_fix cx Rb l /\ s_vars cx st Rb l /\
  rholds (qvalv cx (Some st) [t_shave st]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_cl.

Definition clhead_stmt {RCa1 : RunCtx}  : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = CODELENS -> sinv cx st lf cf ->
    s_regs_cl cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_HEAD (zupd Rb l) M MD) T.

Definition s_regs_cld (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  s_fix cx Rb l /\ s_vars cx st Rb l /\
  rholds (qvalv cx (Some st) [t_nlen st; t_nlen st + t_ndist st]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_cld.

Definition cldone_stmt {RCa1 : RunCtx}  : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = CODELENS -> t_nlen st + t_ndist st <= t_shave st -> sinv cx st lf cf ->
    s_regs_cld cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_DONE (zupd Rb l) M MD) T.
End S_ClDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Inftrees InftreesCoverage ItCovIface InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ItBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_Type S_LenF.

Module S_TableL.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import S_ClDefs.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_DistL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Notation L_TAB_LOOP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_TAB_LOOP (only parsing).
Notation L_TAB_BODY := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_TAB_BODY (only parsing).
Notation L_LL_BODY := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LL_BODY (only parsing).
Notation L_LL_HEAD := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LL_HEAD (only parsing).
Notation L_LL_FILL0 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LL_FILL0 (only parsing).
Notation L_LL_FLOOP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LL_FLOOP (only parsing).
Notation L_LL_FEND := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LL_FEND (only parsing).
Notation A_ORDER := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.A_GB_ORDER (only parsing).

Notation KS_LL := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_gb_ll (only parsing).
Notation KS_TB := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_gb_tb (only parsing).
Notation KS_LF := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_gb_lf (only parsing).
Ltac keptc_close ::= cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF]; split_conj; try exact I; zreg.
Ltac keptc_chain HK ::= cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF] in HK |- *; zkeys; destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].

Lemma zext32_shift31 : forall x, 0 <= x < 4294967296 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) (31 mod 64) = 2 * x.
Proof.
  intros x Hx. change (31 mod 64) with 31. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia_std.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia_std).
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia_std. lia_std.
Qed.
Lemma shiftl_1m : forall x, Z.shiftl x (1 mod 64) = 2 * x.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia_std. change (2 ^ (1 mod 64)) with 2. lia_std. Qed.
Lemma land7_range : forall h, 0 <= Z.land h 7 < 8.
Proof. intros. apply land_7. Qed.
Lemma drop3_bound : forall H B, 0 <= H < 2 ^ B -> 3 <= B -> 0 <= H / 2 ^ 3 < 2 ^ (B - 3).
Proof. intros H B HH HB. apply hold_shr_bound; lia_std. Qed.

Lemma land_m32 : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia_std. apply Z.mod_small. exact Hx. Qed.

Lemma order_f_lt : forall i, 0 <= i < 19 -> 0 <= order_f i < 65536.
Proof. intros i Hi. pose proof (order_f_range i Hi). lia_std. Qed.

Ltac zside1 := first [reflexivity | exact I | zlia].
Ltac tstoreP fd HP HPres :=
  let pc := zpc in
  fd pc ltac:(fun F E D =>
    lazymatch type of D with
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply zu_sb; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply zu_sh; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply zu_sw; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply zu_sd; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    end);
  lazymatch goal with
  | |- realizes _ (zcfg _ _ _ (wbytes ?M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
      (let HP' := fresh in pose proof (HPres M _ a v HP ltac:(zside1) ltac:(zside1)) as HP'; clear HP; rename HP' into HP);
      zmem_post_arr; zmem_post
  end.
Ltac tstore_arrP2 fd Ha i HP HPres :=
  lazymatch type of Ha with
  | mem_arr ?k ?segs ?M ?base ?n ?f =>
      let pc := zpc in
      fd pc ltac:(fun F E D =>
        lazymatch type of D with
        | decode_any _ = Some (Store SZ1 _ _ _, _) =>
            eapply zu_sb; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        | decode_any _ = Some (Store SZ2 _ _ _, _) =>
            eapply zu_sh; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        | decode_any _ = Some (Store SZ4 _ _ _, _) =>
            eapply zu_sw; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        end);
      lazymatch goal with
      | |- realizes _ (zcfg _ _ _ (wbytes M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
          apply (mem_arr_upd segs k M base n f a i v) in Ha; [| zlia | zlia];
          (let kn := eval cbv in (Z.to_nat k) in change (Z.to_nat k) with kn in Ha);
          (let HP' := fresh in pose proof (HPres M _ a v HP ltac:(zside1) ltac:(zside1)) as HP'; clear HP; rename HP' into HP);
          repeat match goal with
          | H : mem_arr ?k' segs M ?base' ?n' ?f' |- _ =>
              first [ apply (mem_arr_frame segs k' M base' n' f' a (Z_to_le_bytes kk v)) in H; [|unfold zdisj; zlen_norm; zlia]
                    | clear H ]
          end;
          zmem_post
      end
  end.
Ltac keptc_trans :=
  repeat match goal with H : keptc _ _ _ _ |- _ => cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF] in H; destr_conj H end;
  cbv [keptc KS_D1 KS_D2 KS_X KS_L1 KS_L2 KS_LL KS_TB KS_LF]; zkeys; split_conj; try exact I;
  rewrite ?zget_zupd in *; cbv [zget_l] in *; cbn [alookup Pos.eqb] in *;
  first [ assumption | reflexivity
        | etransitivity; [eassumption|]; first [assumption | reflexivity | symmetry; assumption] ].

Lemma lenlens_loop {RCa1 : RunCtx}  : forall (N : nat) (P : Z -> mem -> Prop) Rb l M MD T
    (p q n ncode j ci B H : Z) (fin lf : Z -> Z),
  m_halted MD = None ->
  rholds (qargs [p; A_ORDER + 2 * j; ncode - j; j + 1; ncode; B; H; n - ci; q + ci]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_ll_head ->
  ncode - j <= Z.of_nat N -> 0 <= j -> j < ncode -> ncode <= 19 ->
  0 <= ci -> ci <= n -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) -> ZSEP (p + 7176 <= ROM_LO_ALL \/ ROMHI_S <= p) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M A_ORDER 19 order_f ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf -> (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) ->
  (forall i, 0 <= i < j -> lf (order_f i) <= 7) ->
  P j M ->
  (forall M' jo (a v : Z), P jo M' -> a = p + 156 -> 0 <= v < 4294967296 -> P v (wbytes M' (w64 a) (Z_to_le_bytes 4 v))) ->
  (forall M' jo (a v : Z), P jo M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' M' (j' B' H' : Z) (lf' : Z -> Z),
     rholds (qargs [B'; H'; q + n]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_ll_kx ->
     j <= j' -> j' < ncode -> 0 <= B' -> B' < 3 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * n ->
     B' + 3 * (j' - j) = 8 * (n - ci) + B ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' A_ORDER 19 order_f ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) ->
     (forall i, 0 <= i < j' -> lf' (order_f i) <= 7) -> P j' M' ->
     keptc Rb l R' KS_LL ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD (zupd R' []) M' MD) T) ->
  (forall R' M' (ci' B' H' : Z) (lf' : Z -> Z),
     rholds (qargs [B'; H'; n - ci'; q + ci'; ncode; p]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_ll_kd ->
     ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' + 3 * (ncode - j) = 8 * (n - ci) + B ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' A_ORDER 19 order_f ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) ->
     (forall i, 0 <= i < ncode -> lf' (order_f i) <= 7) -> P ncode M' ->
     keptc Rb l R' KS_LL ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_FILL0 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_HEAD (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T p q n ncode j ci B H fin lf Hh RH
    HN Hj0 Hj1 Hnc Hc0 Hc1 HB0 HB1 HH0 HH1 HBc Hq1 Hn26 Hq2 Hp1 Hp2 SPQ SPR Wp Hin Rfin Hord Hlens Rlf Hlf7 HP HPa HPb KX KD; [lia|].
  gb_open.
  zkeysb. unfold L_LL_HEAD, L_LL_FILL0, L_LEAVE_LD, A_ORDER in *. pose proof two64_eq as TW64.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  zto_branch Rfd.
  assert (BODY : forall RJ (cib Hb Bb : Z),
    rholds (qargs [p; A_ORDER + 2 * j; ncode - j; j + 1; ncode; Bb; Hb; n - cib; q + cib]) RJ [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_ll_body ->
    ci <= cib -> cib <= n -> 3 <= Bb -> Bb <= 40 -> 0 <= Hb -> Hb < 2 ^ Bb -> Bb <= 8 * cib ->
    8 * (n - cib) + Bb = 8 * (n - ci) + B ->
    keptc Rb l RJ KS_LL ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_BODY (zupd RJ []) M MD) T).
  { intros RJ cib Hb Bb RJH X1 X2 X3 X4 X5 X6 X7 X8 HK.
    gb_open. unfold L_LL_BODY, A_ORDER in *. zkeys.
    pose proof (pow2_48 Bb ltac:(lia)) as HPBb.
    pose proof (land7_range Hb) as Hv.
    pose proof (order_f_range j ltac:(lia)) as Ho. pose proof (order_f_lt j ltac:(lia)) as Ho2.
    zuntil Rfd (idtac; tstoreP Rfd HP HPa).
    zuntil_h Rfd (first [ zhint srli_small | zhint shiftl_1m ])
      (idtac; tstore_arrP2 Rfd Hlens (order_f j) HP HPb).
    zto_branch Rfd.
    pose proof (drop3_bound Hb Bb ltac:(lia) ltac:(lia)) as Hd3.
    assert (Rlf1 : forall i, 0 <= i < 320 -> 0 <= zfupd lf (order_f j) (Z.land Hb 7) i < 65536).
    { intros i Hi. unfold zfupd. destruct (Z.eqb_spec i (order_f j)); [lia | apply Rlf; lia]. }
    assert (Hlf7' : forall i, 0 <= i < j + 1 -> zfupd lf (order_f j) (Z.land Hb 7) (order_f i) <= 7).
    { intros i Hi. unfold zfupd. destruct (Z.eqb_spec (order_f i) (order_f j)); [lia|]. apply Hlf7.
      destruct (Z.eq_dec i j); [subst; congruence | lia]. }
    destruct (Z.eq_dec (ncode - j) 1) as [Hlast | Hmore].
    - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KD Rx Mx cib (Bb - 3) (Hb / 2 ^ 3) (zfupd lf (order_f j) (Z.land Hb 7))) end);
        [ gb_split | .. ]; try zreg; try assumption; try lia.
      + intros i Hi. apply Hlf7'. lia.
      + replace ncode with (j + 1) by lia. exact HP.
      + keptc_trans.
    - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (IH P Rx lx Mx MD T p q n ncode (j + 1) cib (Bb - 3) (Hb / 2 ^ 3) fin (zfupd lf (order_f j) (Z.land Hb 7)) Hh) end);
        [ gb_split | .. ]; try zreg; try assumption; try lia.
      + intros R' M' j' B' H' lf'. intros. eapply (KX R' M' j' B' H' lf'); try eassumption; try lia.
        keptc_trans.
      + intros R' M' ci' B' H' lf'. intros. eapply (KD R' M' ci' B' H' lf'); try eassumption; try lia.
        keptc_trans. }
  destruct (Z_lt_dec 2 B) as [HB3 | HB3].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (BODY Rx ci H B) end);
      [ gb_split | .. ]; try zreg; try lia. keptc_close.
  - zto_branch Rfd.
    destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
    + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KX Rx Mx j B H lf) end);
        [ gb_split | .. ]; try zreg; try assumption; try lia. keptc_close.
    + pose proof (Rfin ci ltac:(lia)) as Rb1.
      pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hpl0 Hpl1].
      pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
      zuntil_h Rfd (first [ zhint shl_byte | zhint lor8_small ])
        (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (BODY Rx (ci + 1) (fin ci * 2 ^ B + H) (B + 8)) end);
        [ gb_split | .. ]; try zreg; try lia.
      keptc_close.
Qed.

Lemma fill_loop {RCa1 : RunCtx}  : forall (N : nat) (P : Z -> mem -> Prop) Rb l M MD T (p j jo : Z) (lf : Z -> Z),
  m_halted MD = None ->
  rholds (qargs [p; A_ORDER + 2 * j; j + 1]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_fl_head ->
  19 - j <= Z.of_nat N -> 0 <= j -> j < 19 ->
  0 < p -> p + 7176 <= 140737488355328 -> ZSEP (p + 7176 <= ROM_LO_ALL \/ ROMHI_S <= p) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M A_ORDER 19 order_f ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf -> (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) ->
  (forall i, 0 <= i < j -> lf (order_f i) <= 7) ->
  P jo M ->
  (forall M' jo' (a v : Z), P jo' M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo' (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' M' (lf' : Z -> Z),
     rholds (qargs []) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_fl_k ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' A_ORDER 19 order_f ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) ->
     (forall i, 0 <= i < 19 -> lf' (order_f i) <= 7) -> P jo M' ->
     keptc Rb l R' KS_LF ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_FEND (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_FLOOP (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T p j jo lf Hh RH HN Hj0 Hj1 Hp1 Hp2 SPR Wp Hord Hlens Rlf Hlf7 HP HPb K; [lia|].
  gb_open.
  zkeysb. unfold L_LL_FLOOP, L_LL_FEND, A_ORDER in *. pose proof two64_eq as TW64.
  pose proof (order_f_range j ltac:(lia)) as Ho. pose proof (order_f_lt j ltac:(lia)) as Ho2.
  assert (Rord : forall i, 0 <= i < 19 -> 0 <= order_f i < 65536) by (intros; apply order_f_lt; lia).
  zuntil_h Rfd (first [ zhint land_m32 | zhint shiftl_1m ])
    (idtac; tstore_arrP2 Rfd Hlens (order_f j) HP HPb).
  zto_branch Rfd.
  assert (Rlf1 : forall i, 0 <= i < 320 -> 0 <= zfupd lf (order_f j) 0 i < 65536).
  { intros i Hi. unfold zfupd. destruct (Z.eqb_spec i (order_f j)); [lia | apply Rlf; lia]. }
  assert (Hlf7' : forall i, 0 <= i < j + 1 -> zfupd lf (order_f j) 0 (order_f i) <= 7).
  { intros i Hi. unfold zfupd. destruct (Z.eqb_spec (order_f i) (order_f j)); [lia|]. apply Hlf7.
    destruct (Z.eq_dec i j); [subst; congruence | lia]. }
  destruct (Z.eq_dec j 18) as [Hlast | Hmore].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd lf (order_f j) 0)) end);
      [ gb_split | .. ]; try zreg; try assumption.
    + intros i Hi. apply Hlf7'. lia.
    + keptc_close.
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T p (j + 1) jo (zfupd lf (order_f j) 0) Hh) end);
      [ gb_split | .. ]; try zreg; try assumption; try lia.
Qed.

Lemma table_loop {RCa1 : RunCtx}  : forall (k : nat) Rb l M MD T (q n cinj holdj j : Z) (fin : Z -> Z),
  m_halted MD = None -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  14 - 8 * Z.of_nat k <= j < 22 - 8 * Z.of_nat k -> (1 <= k <= 2)%nat -> 0 <= j ->
  0 <= cinj <= n -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 ->
  rholds (qargs [j; q + cinj; n - cinj; holdj]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tl_head ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin ->
  (forall R' hold' j',
     rholds (qargs [q + n; hold'; j']) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tl_lv ->
     j' = j + 8 * (n - cinj) -> 0 <= hold' < 2 ^ j' -> n - cinj < Z.of_nat k ->
     keptc Rb l R' KS_TB ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD (zupd R' []) M MD) T) ->
  (forall R' hold' j',
     rholds (qargs [q + cinj + Z.of_nat k; n - cinj - Z.of_nat k; hold'; j']) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tl_dn ->
     j' = j + 8 * Z.of_nat k -> 0 <= hold' < 2 ^ j' -> Z.of_nat k <= n - cinj ->
     keptc Rb l R' KS_TB ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TAB_BODY (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TAB_LOOP (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros Rb l M MD T q n cinj holdj j fin Hh Hfin Hj Hk Hj0 Hc Hhj Hjc Hq1 Hn26 Hq2 RH Hin KLV KDN; [lia|].
  gb_open.
  zkeys. unfold L_TAB_LOOP, L_TAB_BODY, L_LEAVE_LD in *. pose proof two64_eq as TW64.
  assert (Hj40 : 2 ^ j <= 2 ^ 21) by (apply Z.pow_le_mono_r; lia). change (2 ^ 21) with 2097152 in Hj40.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj j) end);
      [ gb_split | .. ]; try zreg; try lia.
    all: first [ keptc_close | replace (j + 8 * (n - cinj)) with j by lia; lia ].
  - pose proof (Hfin cinj ltac:(lia)) as Hb0.
    pose proof (pullbyte_bound holdj j (fin cinj) ltac:(lia) Hhj Hb0) as Hpb.
    zto_branch_h Rfd (first [ zhint shl_byte ]).
    destruct k as [|k'].
    + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KDN R' (fin cinj * 2 ^ j + holdj) (j + 8)) end);
        [ gb_split | .. ]; try zreg; try lia.
      keptc_close.
    + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') _ _) _ =>
        eapply (IH R' l' M MD T q n (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) fin Hh Hfin) end);
        [ lia | lia | lia | lia | lia | lia | lia | lia | lia | (gb_split; zreg) .. | exact Hin | | ].
      * intros R' hold' j'. intros. eapply KLV; try eassumption; try lia. all: gb_relist.
      * intros R' hold' j'. intros. eapply KDN; try eassumption; try lia. all: gb_relist.
Qed.
End S_TableL.

Module S_Table.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ItCovIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ItBridge.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_DistL S_TableL S_ClDefs.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Notation L_TAB_SKIP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_TAB_SKIP (only parsing).
Notation L_LL_SETUP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LL_SETUP (only parsing).
Notation L_LL_FILL := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LL_FILL (only parsing).
Notation L_LL_TABLE := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LL_TABLE (only parsing).
Notation L_LL_RET := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LL_RET (only parsing).
Notation L_TBLERR := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_TBLERR (only parsing).
Notation L_BAD_TAB := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_BAD_TAB (only parsing).

Lemma mem_u64_eqv {RCa1 : RunCtx}  : forall M a v v', v = v' -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v'.
Proof. intros M a v v' <- H. exact H. Qed.
Lemma mem_u64_mod {RCa1 : RunCtx}  : forall M a v, mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a (v mod 18446744073709551616).
Proof. intros M a v H. unfold mem_u64 in *. change 18446744073709551616 with two64. rewrite Z_to_le_bytes_mod by lia_std. exact H. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma land31_mod : forall h, 0 <= h -> Z.land h 31 = h mod 32.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma bits_54_59 : forall h, 0 <= h < 18446744073709551616 ->
  Z.shiftr (Z.shiftl h 54 mod 18446744073709551616) 59 = (h / 32) mod 32.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 54) with 18014398509481984. change (2 ^ 59) with 576460752303423488. nia.
Qed.
Lemma bits_50_60 : forall h, 0 <= h < 18446744073709551616 ->
  Z.shiftr (Z.shiftl h 50 mod 18446744073709551616) 60 = (h / 1024) mod 16.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 50) with 1125899906842624. change (2 ^ 60) with 1152921504606846976. nia.
Qed.
Lemma mod_range : forall a m, 0 < m -> 0 <= a mod m < m.
Proof. intros. apply Z.mod_pos_bound. assumption. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma it_fail_shape : forall ty lens lens_ofs codes tbl table bits work,
  let r := inflate_table ty lens lens_ofs codes tbl table bits work in
  it_ret r <> 0 -> it_table r = table /\ it_bits r = bits.
Proof. intros. apply inflate_table_fail_shape. assumption. Qed.

Lemma order_covers : forall (lf : Z -> Z) b,
  (forall j, 0 <= j < 19 -> lf (order_f j) <= b) -> forall i, 0 <= i < 19 -> lf i <= b.
Proof.
  intros lf b H i Hi.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/
              i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18) by lia_std.
  decompose [or] C; subst;
    [ change (lf 0) with (lf (order_f 3))
    | change (lf 1) with (lf (order_f 17))
    | change (lf 2) with (lf (order_f 15))
    | change (lf 3) with (lf (order_f 13))
    | change (lf 4) with (lf (order_f 11))
    | change (lf 5) with (lf (order_f 9))
    | change (lf 6) with (lf (order_f 7))
    | change (lf 7) with (lf (order_f 5))
    | change (lf 8) with (lf (order_f 4))
    | change (lf 9) with (lf (order_f 6))
    | change (lf 10) with (lf (order_f 8))
    | change (lf 11) with (lf (order_f 10))
    | change (lf 12) with (lf (order_f 12))
    | change (lf 13) with (lf (order_f 14))
    | change (lf 14) with (lf (order_f 16))
    | change (lf 15) with (lf (order_f 18))
    | change (lf 16) with (lf (order_f 0))
    | change (lf 17) with (lf (order_f 1))
    | change (lf 18) with (lf (order_f 2)) ];
    apply H; lia_std.
Qed.

Lemma le_cell2_range : forall bs i, 0 <= le_cell 2 bs i < 65536.
Proof.
  intros bs i. unfold le_cell.
  set (l := firstn (Z.to_nat 2) (skipn (Z.to_nat (2 * i)) bs)).
  pose proof (bytes_le_to_Z_bound l) as R. pose proof (bytes_le_to_Z_nonneg l) as R0.
  assert (L : (length l <= 2)%nat) by (subst l; rewrite length_firstn; cbn; lia_std).
  assert (P : 2 ^ (8 * Z.of_nat (length l)) <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia_std).
  change (2 ^ 16) with 65536 in P. lia_std.
Qed.
Lemma work_arr {RCa1 : RunCtx}  : forall M p, mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> 0 <= p -> p + 7176 <= two64 ->
  exists wf, mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 wf /\ (forall i, 0 <= i < 288 -> 0 <= wf i < 65536).
Proof.
  intros M p W Hp1 Hp2.
  destruct (mem_wr_readable (run_segments R_segs rc_inp rc_sp rc_mb) wr_rd_R M (p + 808) 576 ltac:(eapply mem_wr_sub; [exact W | lia_std | lia_std]) ltac:(lia_std)) as [bs [A B]].
  exists (le_cell 2 bs). split.
  - apply (mem_arr_of_bytes (run_segments R_segs rc_inp rc_sp rc_mb) 2 M (p + 808) 288 bs A); try lia_std.
  - intros i _. apply le_cell2_range.
Qed.

Lemma rom_it_tabs {RCa1 : RunCtx}  : forall M, rom_ok M ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M LBASE_ADDR 31 (arr_get lbase_a) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M LEXT_ADDR 31 (arr_get lext_a) /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M DBASE_ADDR 32 (arr_get dbase_a) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M DEXT_ADDR 32 (arr_get dext_a).
Proof.
  intros M H. cbv [LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR]. split_conj.
  - eapply mem_arr_ext; [apply rom_lbase_arr; exact H | intros; apply lbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_lext_arr; exact H | intros; apply lext_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dbase_arr; exact H | intros; apply dbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dext_arr; exact H | intros; apply dext_f_model; assumption].
Qed.

Definition st_sh (st : ist) (j : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) j (t_nx st) (t_whave st) (t_wnext st).
Definition st_ll (st : ist) (ci H B j : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) ci (t_cout st) H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) j (t_nx st) (t_whave st) (t_wnext st).
Definition st_ct (st : ist) (m rv lb nx sh : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) rv
      (t_length st) (t_offset st) (t_extra st) (CDyn 0) (CDyn 0) lb (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) sh nx (t_whave st) (t_wnext st).
Definition st_lt (st : ist) (lb nx : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (CDyn 0) (CDyn 0) lb (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) nx (t_whave st) (t_wnext st).
Definition st_tb (st : ist) (m ci H B ncode nlen ndist sh : Z) : ist :=
  IST m (t_last st) (t_flags st) ci (t_cout st) H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      ncode nlen ndist sh (t_nx st) (t_whave st) (t_wnext st).

Ltac ist_cbn := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in *.

Lemma sinv_ll : forall cx st lf cf ci H B j lf',
  sinv cx st lf cf -> t_mode st = LENLENS ->
  t_cin st <= ci -> ci <= c_n cx -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  0 <= j -> j <= 19 ->
  (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j -> lf' (order_f i) <= 7) ->
  sinv cx (st_ll st ci H B j) lf' cf /\ meas cx (st_ll st ci H B j) <= meas cx st.
Proof.
  intros cx st lf cf ci H B j lf' (R & W & P & Mo) Hm H1 H2 H3 H4 H5 H6 H7 H8 Hj0 Hj1 Rlf' Hlf'.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_ll, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. cbv [N_LENS N_CODES] in R. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (LENLENS = HEAD \/ LENLENS = BAD) /\ cout = 0) by mode_get Mo.
  assert (ML : LENLENS = LENLENS -> 4 <= ncode /\ ncode <= 19 /\ shave <= 19 /\ 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\
            (forall j0, 0 <= j0 < shave -> lf (arr_get order_a j0) <= 7)) by mode_get Mo.
  specialize (ML eq_refl). dand ML as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear Mo.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 H1 H8. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [intros _; split_conj; try assumption; intros j0 Hj; rewrite <- order_f_model by lia_std; apply Hlf'; exact Hj |].
    split_conj; mode_vacuous.
  - clear - H8. lia_std.
Qed.

Lemma sinv_ll_ct : forall cx st lf cf cf' lb nx,
  sinv cx st lf cf -> t_mode st = LENLENS ->
  1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= N_CODES -> tab_ok CODES (rdc cf' (CDyn 0)) lb nx = true ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_ct st CODELENS 0 lb nx 0) lf cf' /\ meas cx (st_ct st CODELENS 0 lb nx 0) < meas cx st.
Proof.
  intros cx st lf cf cf' lb nx (R & W & P & Mo) Hm Hlb1 Hlb2 Hnx1 Hnx2 TOK Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb0 db ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_ct, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (LENLENS = HEAD \/ LENLENS = BAD) /\ cout = 0) by mode_get Mo.
  assert (ML : LENLENS = LENLENS -> 4 <= ncode /\ ncode <= 19 /\ shave <= 19 /\ 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\
            (forall j0, 0 <= j0 < shave -> lf (arr_get order_a j0) <= 7)) by mode_get Mo.
  specialize (ML eq_refl). dand ML as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [mode_vacuous |].
    split; [intros _; split_conj; try lia_std; unfold ctable_live; cbn; cbv [N_CODES]; split_conj; try reflexivity; try lia_std; exact TOK |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_ll_bad : forall cx st lf cf cf' rv,
  sinv cx st lf cf -> t_mode st = LENLENS -> 0 <= rv < 18446744073709551616 ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_ct st BAD rv 7 0 (t_shave st)) lf cf' /\ meas cx (st_ct st BAD rv 7 0 (t_shave st)) < meas cx st.
Proof.
  intros cx st lf cf cf' rv (R & W & P & Mo) Hm Hrv Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb0 db ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_ct, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (LENLENS = HEAD \/ LENLENS = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_tb : forall cx st lf cf ci H1 B1 ncode nlen ndist,
  sinv cx st lf cf -> t_mode st = TABLE ->
  t_cin st <= ci -> ci <= c_n cx -> 14 <= B1 -> B1 <= 40 -> 0 <= H1 -> H1 < 2 ^ B1 -> B1 <= 8 * ci ->
  8 * (c_n cx - ci) + B1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  4 <= ncode -> ncode <= 19 -> 257 <= nlen -> nlen <= 286 -> 1 <= ndist -> ndist <= 30 ->
  sinv cx (st_tb st LENLENS ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist 0) lf cf /\
  meas cx (st_tb st LENLENS ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist 0) < meas cx st.
Proof.
  intros cx st lf cf ci H1 B1 ncode nlen ndist (R & W & P & Mo) Hm H1c H2 H3 H4 H5 H6 H7 H8 N1 N2 N3 N4 N5 N6.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode0 nlen0 ndist0 shave nx whave wnext].
  unfold sinv, st_tb, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (TABLE = HEAD \/ TABLE = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  pose proof (hold_shr_bound H1 B1 14 ltac:(lia_std) ltac:(lia_std)) as Hs.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 H1c H8. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [intros _; split_conj; try lia_std; intros j0 Hj0; exfalso; lia_std |].
    split_conj; mode_vacuous.
  - clear - H8 H3. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.
Lemma sinv_tb_bad : forall cx st lf cf ci H1 B1 ncode nlen ndist,
  sinv cx st lf cf -> t_mode st = TABLE ->
  t_cin st <= ci -> ci <= c_n cx -> 14 <= B1 -> B1 <= 40 -> 0 <= H1 -> H1 < 2 ^ B1 -> B1 <= 8 * ci ->
  8 * (c_n cx - ci) + B1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  0 <= ncode -> ncode < 4294967296 -> 0 <= nlen -> nlen < 4294967296 -> 0 <= ndist -> ndist < 4294967296 ->
  sinv cx (bad_of (st_tb st TABLE ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist (t_shave st))) lf cf /\
  meas cx (bad_of (st_tb st TABLE ci (H1 / 2 ^ 14) (B1 - 14) ncode nlen ndist (t_shave st))) < meas cx st.
Proof.
  intros cx st lf cf ci H1 B1 ncode nlen ndist (R & W & P & Mo) Hm H1c H2 H3 H4 H5 H6 H7 H8 N1 N2 N3 N4 N5 N6.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode0 nlen0 ndist0 shave nx whave wnext].
  unfold sinv, st_tb, bad_of, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (TABLE = HEAD \/ TABLE = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  pose proof (hold_shr_bound H1 B1 14 ltac:(lia_std) ltac:(lia_std)) as Hs.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf. unfold RNG. icx_cbn. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 H1c H8. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj; mode_vacuous.
  - clear - H8 H3. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Local Ltac st_cell_tac Hp1 Hp2 :=
  lazymatch goal with
  | |- mem_u32 _ (wbytes _ (w64 ?a) _) ?a _ => apply mem_u32_stored; clear - Hp1 Hp2; lia_std
  | |- mem_u64 _ (wbytes _ (w64 ?a) _) ?a _ => apply mem_u64_stored; clear - Hp1 Hp2; lia_std
  | |- mem_u32 _ (wbytes _ _ _) _ _ => apply mem_u32_frame; [st_cell_tac Hp1 Hp2 | clear - Hp1 Hp2; unfold zdisj; rewrite length_Z_to_le_bytes'; cbn; lia_std]
  | |- mem_u64 _ (wbytes _ _ _) _ _ => apply mem_u64_frame; [st_cell_tac Hp1 Hp2 | clear - Hp1 Hp2; unfold zdisj; rewrite length_Z_to_le_bytes'; cbn; lia_std]
  | |- _ => assumption
  end.
Local Ltac st_rest_set_tac :=
  intros cx st M v H Hp1 Hp2; destruct cx, st; unfold st_rest, st_sh, st_ct, st_lt, st_tb in *; icx_cbn;
  pose proof two64_eq as TW64;
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17);
  repeat split; st_cell_tac Hp1 Hp2.
Lemma st_rest_set140 {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_sh st v) (wbytes M (w64 (c_p cx + 156)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
Definition PL {RCa1 : RunCtx}  (cx : ictx) (fin : Z -> Z) (M0 : mem) (st : ist) (cf : Z -> Z) (j : Z) (M : mem) : Prop :=
  s_std cx fin M /\ st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_sh st j) M /\ s_ret cx st M /\ s_out cx st M /\
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf /\ mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx).

Lemma PL_store140 {RCa1 : RunCtx}  : forall cx fin M0 st cf jo M a v,
  ctx_ok ROMHI_S cx -> PL cx fin M0 st cf jo M -> a = c_p cx + 156 -> 0 <= v < 4294967296 ->
  PL cx fin M0 st cf v (wbytes M (w64 a) (Z_to_le_bytes 4 v)).
Proof.
  intros cx fin M0 st cf jo M a v CX H -> Hv.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  dand H as (STD & [Hmode SREST] & RET & OUT & HC & HP0). open_std STD. unfold PL. icx_cbn. cbv [N_LENS N_CODES] in *.
  cbv [ROMHI_S] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (st_rest_set140 _ _ _ v SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1. clear SREST.
  unfold st_sh in SR1, Hmode |- *. cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1, Hmode |- *.
  zmem_transport M (p + 156) (Z_to_le_bytes 4 v).
  split_conj; try assumption; try close_std; try exact HAG; try exact I. split; assumption.
Qed.

Lemma PL_store_lens {RCa1 : RunCtx}  : forall cx fin M0 st cf jo M a v,
  ctx_ok ROMHI_S cx -> PL cx fin M0 st cf jo M -> c_p cx + 168 <= a -> a + 2 <= c_p cx + 808 ->
  PL cx fin M0 st cf jo (wbytes M (w64 a) (Z_to_le_bytes 2 v)).
Proof.
  intros cx fin M0 st cf jo M a v CX H Ha1 Ha2.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  dand H as (STD & SAT & RET & OUT & HC & HP0). open_std STD. unfold PL. icx_cbn. cbv [N_LENS N_CODES] in *.
  cbv [ROMHI_S] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zmem_transport M a (Z_to_le_bytes 2 v).
  split_conj; try assumption; try close_std; try exact HAG; try exact I.
Qed.

Lemma PL_intro {RCa1 : RunCtx}  : forall cx fin M0 st lf cf M,
  k_mem cx fin M0 st lf cf M -> PL cx fin M0 st cf (t_shave st) M /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf.
Proof.
  intros cx fin M0 st lf cf M H. open_kmem H. split; [| exact Hlens]. unfold PL. destruct st. split_conj; assumption.
Qed.
Lemma PL_kmem {RCa1 : RunCtx}  : forall cx fin M0 st lf cf j M,
  PL cx fin M0 st cf j M -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> k_mem cx fin M0 (st_sh st j) lf cf M.
Proof.
  intros cx fin M0 st lf cf j M (A & B & C & C2 & D & E) HL. unfold k_mem. destruct st. split_conj; assumption.
Qed.

Section TABLE_CODE.
Context {RCa1 : RunCtx}.
Hypothesis ITABLE : itable_spec_s.
Hypothesis CLHEAD : clhead_stmt.

Definition s_regs_llt (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  rholds (qvalv cx (Some st) []) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_llt /\ s_vars cx st Rb l.

Lemma ll_table_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENLENS -> t_shave st = 19 -> sinv cx st lf cf ->
  s_regs_llt cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_TABLE (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hsh SI RG KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). rewrite Hsh in ML. dand ML as (_ & _ & _ & Hnl1 & Hnl2 & Hnd1 & Hnd2 & Hlf7). clear MODE_.
  assert (L7 : forall i, 0 <= i < 19 -> lf i <= 7).
  { apply order_covers. intros j0 Hj0. rewrite order_f_model by exact Hj0. apply Hlf7. exact Hj0. }
  clear Hlf7.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode shave. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  match goal with H : forall i, _ -> 0 <= cf i < 4294967296 |- _ => rename H into Rcf end.
  unfold s_regs_llt, s_vars in RG. icx_cbn. destr_conj RG.
  gb_open.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof FRM as FSL. unfold i_frame in FSL. icx_cbn. cbv [JTAB_ADDR] in FSL. destr_conj FSL.
  prune_rng.
  zkeysb. unfold L_LL_TABLE, L_LL_RET, L_TBLERR, L_CL_HEAD, L_RELOAD_A1, L_ITABLE in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  unfold st_rest in SREST. icx_cbn. cbv [cp_addr o_codes] in SREST. icx_cbn. destr_conj SREST.
  unfold itable_spec_s, itable_spec_at in ITABLE.
  (let rlab := eval cbv in L_LL_RET in
   let fr := eval cbv in (- FR_INF) in
   pose proof (fun Rx lx Mx wf => ITABLE Rx lx Mx MD T CODES p 0 19 0 7 (p + 136) (u + fr) rlab zc lf cf wf Hh) as ITC).
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    lazymatch goal with H120 : mem_u32 _ Mx (p + 136) 7, H144 : mem_u64 _ Mx (p + 160) (p + 1384) |- _ =>
      rename H120 into C120n; rename H144 into C144n end;
    destruct (work_arr Mx p Wp ltac:(lia) ltac:(rewrite TW64; lia)) as (wf & Hwork & Rwf);
    dand (rom_it_tabs Mx ROM) as (RT1 & RT2 & RT3 & RT4);
    eapply (ITC Rx lx Mx wf) end).
  all: first [ lazymatch goal with
       | |- zget_l _ _ _ = _ => cbv [cty o_lens o_next o_work o_lenbits]; zreg
       | |- Z.land _ _ = _ => reflexivity
       | |- _ \/ _ => left; cbv [o_lenbits]; reflexivity
       | |- ZSEP _ => unfold ZSEP; pose proof (sep_p_rom _ _ SEP) as D; cbn [c_p] in D; cbv [STATE_SIZE ROM_LO_ALL DEXT_ADDR] in D |- *; clear - D; lia
       | |- _ mod 16 = 0 => first [ exact (proj1 (proj2 AL)) | apply mod0_add; [lia | exact (proj1 AL) | reflexivity] ]
       | |- mem_wr _ _ _ _ => first [ assumption | cbv [FR_IT]; eapply mem_wr_sub; [exact Wstk | lia | lia] ]
       | |- mem_arr _ _ _ _ _ _ => assumption
       | |- mem_u64 _ _ _ _ => first [ assumption | eapply mem_u64_eqv; [| exact C144n]; cbv [o_codes]; lia ]
       | |- mem_u32 _ _ _ _ => assumption
       | |- forall i : Z, _ -> _ <= _ < _ => assumption
       | |- _ = CODES -> _ => intros _; split; [lia | split; [reflexivity | intros s Hs; replace (0 + s) with s by lia; apply L7; lia]]
       | |- _ = DISTS -> _ => intros X; discriminate X
       | |- forall s : Z, _ -> _ <= 15 => intros s Hs; replace (0 + s) with s by lia; pose proof (L7 s Hs); lia
       | |- forall R' M', _ => idtac
       | |- _ => cbv [FRA STATE_SIZE N_LENS N_CODES FR_IT DEXT_ADDR]; cbn [it_room]; first [assumption | lia]
       end | idtac ].
  intros R' M' cf' wf' Hrv Hret3 Hcf' Hwf' Rcf' Rwf' HP Hlens' Hcodes' Hwork' Hnext' Hbits' KE.
  pose proof (tab_ok_of_itable CODES lf cf wf cf' 0 19 0 7) as BR0.
  pose proof (it_fail_shape CODES (arr_init N_LENS lf) 0 19 (arr_init N_CODES cf) 0 7 (arr_init N_WORK wf)) as FS0.
  set (r := inflate_table CODES (arr_init N_LENS lf) 0 19 (arr_init N_CODES cf) 0 7 (arr_init N_WORK wf)) in *.
  clearbody r. cbv zeta in BR0, FS0.
  assert (BR : it_ret r = 0 ->
     tab_ok CODES (rdc cf' (CDyn 0)) (it_bits r) (it_table r - 0) = true /\ 1 <= it_bits r <= 15 /\
     0 + 2 ^ it_bits r <= it_table r <= 0 + it_room CODES /\ (forall i, 0 <= i < N_CODES -> ~ (0 <= i < it_table r) -> cf' i = cf i)).
  { intros Hrz. apply BR0; cbv [N_LENS N_CODES]; cbn [it_room]; try assumption; try lia.
    - intros s Hs. replace (0 + s) with s by lia. pose proof (L7 s Hs). lia.
    - intros _. split; [lia | split; [reflexivity | intros s Hs; replace (0 + s) with s by lia; apply L7; lia]]. }
  assert (FS : it_ret r <> 0 -> it_table r = 0 /\ it_bits r = 7) by (intros Hnz; exact (FS0 Hnz)).
  clear BR0 FS0.
  unfold kept_eq in KE. zkeys. destr_conj KE. zimps.
  clear Hwork RT1 RT2 RT3 RT4 C120n C144n Hcodes.
  unfold it_fp in HP. cbv [o_next o_work o_codes N_WORK N_CODES FR_IT] in HP. zreattachL HP.
  match goal with HS : s_ret _ _ ?Mx |- realizes _ (zcfg _ _ _ ?Mx _) _ => clear HS end.
  cbv [N_CODES] in Rcf', BR. cbn [it_room] in BR. cbv [o_next o_codes] in Hnext'.
  destruct (Z.eq_dec (it_ret r) 0) as [Hr0 | Hnz].
  -
    dand (BR Hr0) as (TOK & Hb15 & Htab & Hout). clear BR FS.
    rewrite Hr0 in Hrv. rewrite Z.sub_0_r in TOK.
    pose proof (sinv_ll_ct _ _ lf cf cf' (it_bits r) (it_table r) SI0 eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv [N_CODES]; lia) TOK ltac:(cbv [N_CODES]; exact Rcf')) as [SI1 ME1].
    zuntil Rfd (idtac;
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (CLHEAD (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (st_ct (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist 19 nx whave wnext)
                       CODELENS 0 (it_bits r) (it_table r) 0)
                lf cf' CX0 Hh Hfin eq_refl SI1) end).
    + unfold s_regs_cl, s_fix, s_vars, st_ct; gb_split; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    + unfold k_mem, st_at, st_rest, s_ret, st_ct; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [CODELENS]; assumption | exact HAG | exact I | eapply mem_u64_eqv; [| eassumption]; lia ].
    + eapply KALL_mono; [| exact KA0]. clear - ME1. lia.
  -
    destruct (FS Hnz) as [Ht0 Hb7]. clear BR FS.
    assert (Hrm : exists rm, it_ret r mod 18446744073709551616 = rm /\ rm <> 0 /\ 0 <= rm < 18446744073709551616).
    { exists (it_ret r mod 18446744073709551616). split; [reflexivity|].
      destruct Hret3 as [E | [E | E]]; [exfalso; exact (Hnz E) | rewrite E | rewrite E]; clear;
        [ change (1 mod 18446744073709551616) with 1 | change ((-1) mod 18446744073709551616) with 18446744073709551615 ]; lia_std. }
    dand Hrm as (rm & Hrm & Hrm0 & Hrm1).
    (* A RUN THAT ENDS AT A FACT: the stop tactic needs the fact "a cell of the current memory holds the callee's
       result": it stands only after the store of that result has been taken, and the stop tactic takes no step:
       it re-says the stored value in its reduced form for the load that follows *)
    zuntil Rfd (idtac; lazymatch goal with HS : mem_u64 _ ?Mx _ (it_ret r) |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      apply mem_u64_mod in HS; rewrite Hrm in HS end).
    pose proof (sinv_ll_bad _ _ lf cf cf' rm SI0 eq_refl (conj (proj1 Hrm1) (proj2 Hrm1)) ltac:(cbv [N_CODES]; exact Rcf')) as [SI1 ME1].
    ist_cbn. rewrite Ht0 in Hnext'. rewrite Hb7 in Hbits'.
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KRA1 Rx Mx _ lf cf' SI1 ME1) end).
    + unfold s_regs_reload, st_ct; icx_cbn; zkeys; split_conj; try zreg; try (intros C; discriminate C).
    + unfold k_mem, st_at, st_rest, s_ret, st_ct; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [BAD]; assumption | exact HAG | exact I | eapply mem_u64_eqv; [| eassumption]; lia ].
Qed.

Lemma ll_fill_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENLENS -> t_ncode st <= t_shave st -> sinv cx st lf cf ->
  s_regs_llt cx st Rb l -> rholds (qargs [t_shave st]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_llfill -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_FILL (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hsh SI RG La5 KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  destruct (PL_intro _ _ _ _ _ _ _ KM) as [HP HlensX]. open_kmem KM. open_std STD. clear SAT SRET SOUT HlensX.
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). dand ML as (Hnc1 & Hnc2 & Hsh19 & _ & _ & _ & _ & Hlf7). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  unfold s_regs_llt, s_vars in RG. icx_cbn. destr_conj RG.
  gb_open.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (rom_order_arr _ ROM) as Hord.
  prune_rng.
  zkeysb. unfold L_LL_FILL, L_LL_TABLE, L_LL_FLOOP, L_LL_FEND, A_ORDER in *. pose proof two64_eq as TW64.
  zto_branch Rfd.
  destruct (Z_lt_dec 18 shave) as [H19 | H18].
  - zuntil Rfd (idtac;
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (ll_table_s _ fin MD T M0 Rx lx Mx
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI0) end).
    + unfold s_regs_llt, s_vars; gb_split; icx_cbn; zkeys; split_conj; zreg.
    + apply (PL_kmem _ _ _ _ lf cf shave) in HP; [exact HP | exact Hlens].
    + exact KA0.
  - zuntil_h Rfd (first [ zhint shiftl_1m ]) (idtac;
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (fill_loop 19 (fun (_ : Z) Mq => PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                 (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf shave Mq)
                Rx lx Mx MD T p shave shave lf Hh) end);
      [ gb_split | .. ]; try zreg; try assumption; try lia.
    + unfold ZSEP. exact (sep_p_rom _ _ SEP).
    + intros i Hi. rewrite order_f_model by lia. apply Hlf7. lia.
    + intros M' jo' a v HP' Ha1 Ha2. eapply PL_store_lens; [exact CX0 | exact HP' | cbn; lia | cbn; lia].
    +
      intros R' M' lf' Ha2 Wp' Hord' Hlens' Rlf' Hlf7' HP' HKC. gb_open. cbv [keptc KS_LF] in HKC. destr_conj HKC. zimps. zkeys. unfold L_LL_FEND in *.
      clear Hlens Hord Hin Wp Wstk Wob Ww ROM FRM CST HK Hcodes HP.
      pose proof (fun M' jo a v => PL_store140 (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                    (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    cf jo M' a v CX0) as HPa.
      clear Hord'.
      zuntil0 Rfd (idtac; tstoreP Rfd HP' HPa).
      pose proof (sinv_ll _ _ lf cf cin hold bits 19 lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) Rlf' Hlf7') as [SI1 ME1].
      zuntil0 Rfd (idtac;
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (ll_table_s _ fin MD T M0 Rx lx Mx
                  (st_ll (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cin hold bits 19)
                  lf' cf CX0 Hh Hfin eq_refl eq_refl SI1) end).
      * unfold s_regs_llt, s_vars, st_ll; gb_split; icx_cbn; zkeys; split_conj; try zreg; keptc_trans.
      * apply (PL_kmem _ _ _ _ lf' cf 19) in HP'; [exact HP' | exact Hlens'].
      * eapply KALL_mono; [| exact KA0]. exact ME1.
Qed.

Lemma ll_setup_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENLENS -> t_shave st < t_ncode st -> sinv cx st lf cf ->
  s_fix cx Rb l -> s_vars cx st Rb l ->
  rholds (qvalv cx (Some st) [t_shave st; t_ncode st]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_llsetup ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LL_SETUP (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hsh SI FX VR RH KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0. open_K K.
  destruct (PL_intro _ _ _ _ _ _ _ KM) as [HP HlensX]. open_kmem KM. open_std STD. clear SAT SRET SOUT HlensX.
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). dand ML as (Hnc1 & Hnc2 & Hsh19 & _ & _ & _ & _ & Hlf7). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  unfold s_fix in FX. unfold s_vars in VR. icx_cbn. destr_conj FX. destr_conj VR.
  gb_open.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof (rom_order_arr _ ROM) as Hord.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  prune_rng.
  zkeysb. unfold L_LL_SETUP, L_LL_HEAD, L_LL_FILL0, L_LL_FILL, L_LEAVE_LD, A_ORDER in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  pose proof (fun M' jo a v => PL_store140 (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                cf jo M' a v CX0) as HPa.
  pose proof (fun M' jo a v => PL_store_lens (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                cf jo M' a v CX0) as HPb.
  cbn [c_p] in HPa, HPb.
  zuntil_h Rfd (first [ zhint_by zext32_shift ltac:(zlia) | zhint zext32_shift31 ]) (idtac;
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (lenlens_loop 19 (fun jo Mq => PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
               (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf jo Mq)
              Rx lx Mx MD T p q n ncode shave cin bits hold fin lf Hh) end);
    [ gb_split | .. ]; try zreg; try assumption; try lia.
  - unfold ZSEP. exact (sep_p_q _ _ SEP).
  - unfold ZSEP. exact (sep_p_rom _ _ SEP).
  - intros i Hi. rewrite order_f_model by lia. apply Hlf7. lia.
  -
    intros R' M' j' B' H' lf' RKH X1 X2 X3 X4 X5 X6 X7 X8 Wp' Hin' Hord' Hlens' Rlf' Hlf7' HP' HKC.
    gb_open.
    cbv [keptc KS_LL] in HKC. destr_conj HKC. zimps. zkeys.
    pose proof (sinv_ll _ _ lf cf n H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) Rlf' ltac:(exact Hlf7')) as [SI1 ME1].
    pose proof (PL_kmem _ _ _ _ lf' cf j' _ HP' Hlens') as KM'. dand KM' as (STD' & SAT' & SRET' & SOUT' & HL' & HC' & HP0').
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KLL Rx Mx (st_ll (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) n H' B' j') lf' cf SI1) end.
    + unfold s_regs_leave_ld, st_ll; icx_cbn; zkeys; split_conj; try zreg; try assumption.
      all: try (match goal with G : zget _ _ = 0 |- _ => rewrite G end; lia).
    + exact STD'.
    + exact SAT'.
    + exact SRET'.
    + exact SOUT'.
    + exact HL'.
    + exact HC'.
    + exact HP0'.
  -
    intros R' M' ci' B' H' lf' RKH X1 X2 X3 X4 X5 X6 X7 X8 Wp' Hin' Hord' Hlens' Rlf' Hlf7' HP' HKC.
    gb_open.
    cbv [keptc KS_LL] in HKC. destr_conj HKC. zimps. zkeys. unfold L_LL_FILL0, L_LL_FILL in *.
    pose proof (sinv_ll _ _ lf cf ci' H' B' ncode lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) Rlf' ltac:(exact Hlf7')) as [SI1 ME1].
    zuntil Rfd (idtac;
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (ll_fill_s _ fin MD T M0 Rx lx Mx
                (st_ll (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' ncode)
                lf' cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI1) end).
    + unfold s_regs_llt, s_vars, st_ll; gb_split; icx_cbn; zkeys; split_conj; try zreg; try assumption.
    + gb_split; unfold st_ll; cbn [t_shave]; zreg.
    + apply (PL_kmem _ _ _ _ lf' cf ncode) in HP'; [exact HP' | exact Hlens'].
    + eapply KALL_mono; [| exact KA0]. exact ME1.
Qed.

Theorem arm_LENLENS_s0 : arm_stmt L_LENLENS LENLENS.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof KM as KM0. open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by mode_get MODE_.
  specialize (ML Hm). dand ML as (Hnc1 & Hnc2 & Hsh19 & _). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof RE as RE0. unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  assert (C128 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 144) ncode) by (unfold st_rest in SREST; icx_cbn; destr_conj SREST; assumption).
  assert (C140 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 156) shave) by (unfold st_rest in SREST; icx_cbn; destr_conj SREST; assumption).
  clear SREST Hmode STD SRET SOUT Hlens Hcodes HP0.
  zkeysb. unfold L_LENLENS, L_LL_SETUP, L_LL_FILL in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  zto_branch Rfd.
  destruct (Z_lt_dec shave ncode) as [Hlt | Hge].
  - zuntil Rfd (idtac;
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (ll_setup_s _ fin MD T M0 Rx lx Mx
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI) end);
      [ unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg
      | unfold s_vars; icx_cbn; zkeys; split_conj; zreg
      | (gb_split; icx_cbn; zkeys; zreg) .. | exact KM0 | exact K ].
  - zuntil Rfd (idtac;
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (ll_fill_s _ fin MD T M0 Rx lx Mx
                (IST LENLENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI) end);
      [ unfold s_regs_llt, s_vars; gb_split; icx_cbn; zkeys; split_conj; zreg
      | gb_split; icx_cbn; zkeys; zreg | exact KM0 | exact K ].
Qed.

Ltac zval k :=
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?l) _ _) _ =>
    let o := eval cbn [alookup Pos.eqb] in (alookup l k) in
    lazymatch o with Some ?v => v end
  end.

Lemma table_body : forall cx fin MD T M0 Rb l M st lf cf (cin1 hold1 bits1 : Z),
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = TABLE -> sinv cx st lf cf ->
  s_fix cx Rb l ->
  rholds (qvalv cx (Some st) [c_n cx - cin1; hold1; bits1; c_q cx + cin1]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tbody ->
  t_cin st <= cin1 -> cin1 <= c_n cx -> 14 <= bits1 -> bits1 <= 40 -> 0 <= hold1 -> hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
  8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_TAB_BODY (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf cin1 hold1 bits1 CX Hh Hfin Hm SI FX RH
         Hc1 Hc2 Hb1 Hb2 Hh1 Hh2 Hbc HW KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0. open_K K.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  unfold s_fix in FX. icx_cbn. destr_conj FX.
  gb_open.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  prune_rng.
  pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh64.
  zkeysb. unfold L_TAB_BODY, L_LL_SETUP, L_BAD_TAB, L_BADMSG_S11 in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (mod_range hold1 32 ltac:(lia)) as R1. pose proof (mod_range (hold1 / 32) 32 ltac:(lia)) as R2.
  pose proof (mod_range (hold1 / 1024) 16 ltac:(lia)) as R3.
  pose proof (hold_shr_bound hold1 bits1 14 ltac:(lia) ltac:(lia)) as R4.
  unfold st_rest in SREST. icx_cbn. cbv [cp_addr o_codes] in SREST. icx_cbn. destr_conj SREST.
  zto_branch_h Rfd (first [ zhint land31_mod | zhint bits_54_59 | zhint bits_50_60 | zhint srli_small ]).
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (JB : forall RJ,
    rholds (qvalv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
              (Some (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext))
              [n - cin1; q + cin1; hold1 / 2 ^ 14; bits1 - 14]) RJ [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gb_tbody_jb ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_BAD_TAB (zupd RJ []) Mc MD) T) end.
  { intros RJ. intros. gb_open. unfold L_BAD_TAB. zkeys.
    pose proof (sinv_tb_bad _ _ lf cf cin1 hold1 bits1 ((hold1 / 1024) mod 16 + 4) (hold1 mod 32 + 257) ((hold1 / 32) mod 32 + 1)
                  SI0 eq_refl Hc1 Hc2 Hb1 Hb2 Hh1 Hh2 Hbc HW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI1 ME1].
    ist_cbn.
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KB11 Rx Mx _ lf cf SI1 ME1) end).
    - unfold s_regs_disp, s_fix, s_vars, st_tb; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - zreg.
    - unfold k_mem, st_at, st_rest, st_tb, s_ret; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [cbv [TABLE]; assumption | exact HAG | exact I]. }
  destruct (Z_lt_dec 29 (hold1 mod 32)) as [Hn1 | Hn1].
  { zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => apply (JB Rx) end); gb_split; zreg. }
  zto_branch Rfd.
  destruct (Z_lt_dec ((hold1 / 32) mod 32) 30) as [Hn2 | Hn2].
  2: { zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => apply (JB Rx) end); gb_split; zreg. }
  clear JB.
  pose proof (sinv_tb _ _ lf cf cin1 hold1 bits1 ((hold1 / 1024) mod 16 + 4) (hold1 mod 32 + 257) ((hold1 / 32) mod 32 + 1)
                SI0 eq_refl Hc1 Hc2 Hb1 Hb2 Hh1 Hh2 Hbc HW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI1 ME1].
  zuntil Rfd (idtac;
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (ll_setup_s _ fin MD T M0 Rx lx Mx
              (st_tb (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                     LENLENS cin1 (hold1 / 2 ^ 14) (bits1 - 14) ((hold1 / 1024) mod 16 + 4) (hold1 mod 32 + 257) ((hold1 / 32) mod 32 + 1) 0)
              lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI1) end).
  - unfold s_fix, st_tb; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - unfold s_vars, st_tb; icx_cbn; zkeys; split_conj; zreg.
  - gb_split; unfold st_tb; icx_cbn; zkeys; zreg.
  - unfold k_mem, st_at, st_rest, st_tb, s_ret; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
    all: first [cbv [LENLENS]; assumption | exact HAG | exact I].
  - eapply KALL_mono; [| exact KA0]. clear - ME1. lia.
Qed.

Theorem arm_TABLE_s0 : arm_stmt L_TABLE TABLE.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof KM as KM0. pose proof K as KA0. open_K K. open_kmem KM. open_std STD.
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof (proj1 CX) as CXl. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof RE as RE0. unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  clear SAT SRET SOUT Hlens Hcodes ROM Wstk Wp Wob Ww FRM CST HK.
  prune_rng.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  zkeysb. unfold L_TABLE, L_TAB_LOOP, L_TAB_BODY, L_TAB_SKIP, L_LEAVE_LD in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  zto_branch Rfd.
  destruct (Z_lt_dec 13 bits) as [Hb14 | Hb14].
  - zuntil Rfd (idtac;
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (table_body _ fin MD T M0 Rx lx Mx
                (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf cin hold bits CX0 Hh Hfin eq_refl SI) end);
      [ unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg
      | (gb_split; icx_cbn; zkeys; first [zreg | lia]) .. | exact KM0 | exact KA0 ].
  - assert (Hkk : exists k : nat, 14 - 8 * Z.of_nat k <= bits < 22 - 8 * Z.of_nat k /\ (1 <= k <= 2)%nat).
    { destruct (Z_lt_dec bits 6); [exists 2%nat | exists 1%nat]; cbn; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (table_loop k Rx lx Mx MD T q n cin hold bits fin Hh Hfin Hk1 Hk2) end);
      [ lia | lia | lia | lia | lia | lia | lia | (gb_split; zreg) .. | exact Hin | | ].
    +
      intros R' hold' j' RKH Hj' Hh' Hkn HKC. gb_open. cbv [keptc KS_TB] in HKC. destr_conj HKC. zimps. zkeys.
      pose proof (sinv_pull _ _ lf cf n hold' j' SI ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 _].
      dand KM0 as (STD' & SAT' & SRET' & SOUT' & HL' & HC' & HP0').
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KLL Rx Mx (st_pull (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) n hold' j') lf cf SI1) end;
        [ unfold s_regs_leave_ld, st_pull; icx_cbn; zkeys; split_conj; try zreg; try assumption;
          match goal with G : zget R' _ = 0 |- _ => rewrite G end; lia
        | exact STD' | exact SAT' | exact SRET' | exact SOUT' | exact HL' | exact HC' | exact HP0' ].
    +
      intros R' hold' j' RKH Hj' Hh' Hkn HKC. gb_open. cbv [keptc KS_TB] in HKC. destr_conj HKC. zimps. zkeys.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (table_body _ fin MD T M0 Rx [] Mx
                  (IST TABLE last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  lf cf (cin + Z.of_nat k) hold' j' CX0 Hh Hfin eq_refl SI) end;
        [ unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; try zreg; assumption
        | (gb_split; icx_cbn; zkeys; first [zreg | assumption | lia]) .. | exact KM0 | exact KA0 ].
Qed.
End TABLE_CODE.

End S_Table.

Module S_CodelensT.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ItCovIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ItBridge.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_DistL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_LenL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF S_ClDefs.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* the text's own labels: moved to the layout; the old names stand as parse-only notations of its fields *)
Notation L_LENS_RET := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LENS_RET (only parsing).
Notation L_DTAB := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_DTAB (only parsing).
Notation L_DISTS_RET := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_DISTS_RET (only parsing).
Notation L_CL_OK := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_OK (only parsing).
(* this label is defined in both halves of the text under one name: its layout field is the front half's row *)
Notation L_TBLERR := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_TBLERR (only parsing).

Lemma mem_u64_eqv {RCa1 : RunCtx}  : forall M a v v', v = v' -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v'.
Proof. intros M a v v' <- H. exact H. Qed.
Lemma mem_u64_mod {RCa1 : RunCtx}  : forall M a v, mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a (v mod 18446744073709551616).
Proof. intros M a v H. unfold mem_u64 in *. change 18446744073709551616 with two64. rewrite Z_to_le_bytes_mod by lia_std. exact H. Qed.

Lemma le_cell2_range : forall bs i, 0 <= le_cell 2 bs i < 65536.
Proof.
  intros bs i. unfold le_cell.
  set (l := firstn (Z.to_nat 2) (skipn (Z.to_nat (2 * i)) bs)).
  pose proof (bytes_le_to_Z_bound l) as R. pose proof (bytes_le_to_Z_nonneg l) as R0.
  assert (L : (length l <= 2)%nat) by (subst l; rewrite length_firstn; cbn; lia_std).
  assert (P : 2 ^ (8 * Z.of_nat (length l)) <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia_std).
  change (2 ^ 16) with 65536 in P. lia_std.
Qed.
Lemma work_arr {RCa1 : RunCtx}  : forall M p, mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> 0 <= p -> p + 7176 <= two64 ->
  exists wf, mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 808) 288 wf /\ (forall i, 0 <= i < 288 -> 0 <= wf i < 65536).
Proof.
  intros M p W Hp1 Hp2.
  destruct (mem_wr_readable (run_segments R_segs rc_inp rc_sp rc_mb) wr_rd_R M (p + 808) 576 ltac:(eapply mem_wr_sub; [exact W | lia_std | lia_std]) ltac:(lia_std)) as [bs [A B]].
  exists (le_cell 2 bs). split.
  - apply (mem_arr_of_bytes (run_segments R_segs rc_inp rc_sp rc_mb) 2 M (p + 808) 288 bs A); try lia_std.
  - intros i _. apply le_cell2_range.
Qed.

Lemma rom_it_tabs {RCa1 : RunCtx}  : forall M, rom_ok M ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M LBASE_ADDR 31 (arr_get lbase_a) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M LEXT_ADDR 31 (arr_get lext_a) /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M DBASE_ADDR 32 (arr_get dbase_a) /\ mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M DEXT_ADDR 32 (arr_get dext_a).
Proof.
  intros M H. cbv [LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR]. split_conj.
  - eapply mem_arr_ext; [apply rom_lbase_arr; exact H | intros; apply lbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_lext_arr; exact H | intros; apply lext_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dbase_arr; exact H | intros; apply dbase_f_model; assumption].
  - eapply mem_arr_ext; [apply rom_dext_arr; exact H | intros; apply dext_f_model; assumption].
Qed.


Ltac ist_cbn := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in *.

Lemma rng_dc : forall cx st lf cf, sinv cx st lf cf -> match t_dc st with CDyn o => 0 <= o /\ o <= N_CODES | _ => True end.
Proof. intros cx st lf cf (R & _). unfold RNG in R. destr_conj R. assumption. Qed.

Lemma pow2_pos : forall b, 0 <= b -> 0 < 2 ^ b.
Proof. intros b Hb. apply Z.pow_pos_nonneg; lia_std. Qed.

Definition st_tab (st : ist) (m rv lb : Z) (dc : codeptr) (db nx : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) rv
      (t_length st) (t_offset st) (t_extra st) (CDyn 0) dc lb db
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) nx (t_whave st) (t_wnext st).

Lemma sinv_cl_bad : forall cx st lf cf cf' rv lb dc db nx,
  sinv cx st lf cf -> t_mode st = CODELENS -> 0 <= rv < 18446744073709551616 ->
  0 <= lb < 4294967296 -> 0 <= db < 4294967296 ->
  match dc with CDyn o => 0 <= o /\ o <= N_CODES | _ => True end -> 0 <= nx -> nx <= N_CODES ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_tab st BAD rv lb dc db nx) lf cf' /\ meas cx (st_tab st BAD rv lb dc db nx) < meas cx st.
Proof.
  intros cx st lf cf cf' rv lb dc db nx (R & W & P & Mo) Hm Hrv Hlb Hdb Hdc Hnx1 Hnx2 Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc0 lb0 db0 ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_tab, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  assert (Mf : flags = -1 -> (CODELENS = HEAD \/ CODELENS = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split; [unfold PROG in P; icx_cbn; prog_transfer P |]]] |].
  - clear W P Mf. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear W P. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_cl_len_ : forall cx st lf cf cf' lb o2 db nx,
  sinv cx st lf cf -> t_mode st = CODELENS ->
  1 <= lb -> lb <= 15 -> 1 <= db -> db <= 15 -> 0 <= o2 -> o2 <= nx -> nx <= N_CODES ->
  tab_ok LENS (rdc cf' (CDyn 0)) lb o2 = true -> tab_ok DISTS (rdc cf' (CDyn o2)) db (nx - o2) = true ->
  (forall i, 0 <= i < N_CODES -> 0 <= cf' i < 4294967296) ->
  sinv cx (st_tab st LEN_ 0 lb (CDyn o2) db nx) lf cf' /\ meas cx (st_tab st LEN_ 0 lb (CDyn o2) db nx) < meas cx st.
Proof.
  intros cx st lf cf cf' lb o2 db nx (R & W & P & Mo) Hm Hlb1 Hlb2 Hdb1 Hdb2 Ho1 Ho2 Hnx TL TD Rcf.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc0 lb0 db0 ncode nlen ndist shave nx0 whave wnext].
  unfold sinv, st_tab, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. destr_conj R.
  assert (Mf : flags = -1 -> (CODELENS = HEAD \/ CODELENS = BAD) /\ cout = 0) by mode_get Mo. clear Mo.
  cbv [N_CODES] in *.
  split; [split; [| split; [exact W | split; [unfold PROG in P; icx_cbn; prog_transfer P |]]] |].
  - clear W P Mf TL TD. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear W P. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [mode_vacuous |].
    split; [mode_vacuous |].
    split; [intros _; unfold tables_live; cbn [t_lc t_dc t_lb t_db t_nx]; cbv [N_CODES]; split_conj; try reflexivity; try assumption; lia_std |].
    split_conj; mode_vacuous.
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Section CLT.
Context {RCa1 : RunCtx}.
Hypothesis ITABLE : itable_spec_s.
Hypothesis IFAST : ifast_spec_s.

Lemma lenu_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LEN_ -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEN_ (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof (sinv_len_ cx st lf cf SI Hmd) as [SI1 ME1].
  open_kmem KM. destruct SAT as [Hmode SREST].
  dand RG as (FIX & VARS & G27).
  pose proof CX as CX0. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold s_fix, s_vars in FIX, VARS. icx_cbn. destr_conj FIX. destr_conj VARS.
  open_std STD. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold st_le in SI1, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1, ME1.
  zkeysb. unfold L_LEN_, L_LEN in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  clear Hmode.
  zuntil Rfd (idtac;
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (len_s IFAST _ fin MD T M0 Rx lx Mx
              (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI1) end).
  - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [LEN]; assumption | exact SREST | exact SRET | exact SOUT | exact HAG | exact I].
  - eapply KALL_mono; [| exact K]. clear - ME1. lia.
Qed.

Local Ltac itable_pre SEP AL Wstk LF15 :=
  first [ lazymatch goal with
       | |- zget_l _ _ _ = _ => cbv [cty o_lens o_next o_work o_lenbits o_distbits]; zreg
       | |- Z.land _ _ = _ => reflexivity
       | |- _ \/ _ => first [ left; cbv [o_lenbits]; reflexivity | right; cbv [o_distbits]; reflexivity ]
       | |- ZSEP _ => unfold ZSEP; pose proof (sep_p_rom _ _ SEP) as D; cbn [c_p] in D; cbv [STATE_SIZE ROM_LO_ALL DEXT_ADDR ROMHI_S] in D |- *; clear - D; lia
       | |- _ mod 16 = 0 => first [ exact (proj1 (proj2 AL)) | apply mod0_add; [lia | exact (proj1 AL) | reflexivity] ]
       | |- mem_wr _ _ _ _ => first [ assumption | cbv [FR_IT]; eapply mem_wr_sub; [exact Wstk | lia | lia] ]
       | |- mem_arr _ _ _ _ _ _ => assumption
       | |- mem_u64 _ _ _ _ => first [ assumption | eapply mem_u64_eqv; [| eassumption]; cbv [o_codes]; lia ]
       | |- mem_u32 _ _ _ _ => assumption
       | |- forall i : Z, _ -> _ <= _ < _ => assumption
       | |- _ = CODES -> _ => intros X; discriminate X
       | |- _ = DISTS -> _ => first [ intros X; discriminate X | intros _; lia ]
       | |- forall s : Z, _ -> _ <= 15 => intros s Hs; first [ replace (0 + s) with s by lia | idtac ]; apply LF15; lia
       | |- forall R' M', _ => idtac
       | |- _ => cbv [FRA STATE_SIZE N_LENS N_CODES FR_IT ENOUGH_LENS ENOUGH_DISTS DEXT_ADDR]; cbn [it_room]; cbv [ENOUGH_LENS ENOUGH_DISTS]; first [assumption | lia]
       end | idtac ].

Theorem cldone_s : cldone_stmt.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm Hhave SI RG KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (MC : t_mode st = CODELENS -> 257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            t_shave st <= t_nlen st + t_ndist st /\ (forall i, 0 <= i < t_shave st -> lf i <= 15) /\ ctable_live st cf) by mode_get MODE_.
  specialize (MC Hm). dand MC as (Hnl1 & Hnl2 & Hnd1 & Hnd2 & Hsh & Hlf15 & _). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  assert (LF15 : forall i, 0 <= i < nlen + ndist -> lf i <= 15) by (intros i Hi; apply Hlf15; lia). clear Hlf15 Hsh Hhave.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  match goal with H : forall i, _ -> 0 <= cf i < 4294967296 |- _ => rename H into Rcf end.
  pose proof (rng_dc _ _ _ _ SI0) as Hdc. cbn [t_dc] in Hdc. cbv [N_CODES] in Hdc.
  unfold s_regs_cld, s_fix, s_vars in RG. icx_cbn. destr_conj RG. gb_open.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  (* the frame's slots are opened ALL (the hand text took eight of them through a helper lemma that named their
     distances) *)
  pose proof FRM as FS. unfold i_frame in FS. icx_cbn. cbv [JTAB_ADDR] in FS. destr_conj FS.
  unfold st_rest in SREST. icx_cbn.
  dand SREST as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
  pose proof SRET as SRET'. unfold s_ret in SRET'. icx_cbn. clear SRET.
  assert (Rdb : 0 <= db < 4294967296) by lia. pose proof (Rlf 256 ltac:(lia)) as R256.
  prune_rng.
  zkeysb. unfold L_CL_DONE, L_LENS_RET, L_DTAB, L_DISTS_RET, L_TBLERR, L_CL_OK, L_BADMSG_S10, L_RELOAD_A1, L_ITABLE, L_LEN_ in *.
  cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zto_branch Rfd.
  destruct (Z.eq_dec (lf 256) 0) as [Hz | Hnz].
  {
    pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
    cbn [t_mode] in MB. change (rank CODELENS) with 20 in MB.
    zuntil Rfd (idtac;
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KB10 Rx Mx (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf
                (sinv_bad_of _ _ _ _ SI0)) end).
    - clear - MB. lia.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - first [ zreg | lazymatch goal with |- 0 <= ?x < _ => eassert (EA2 : x = _) by zreg; rewrite EA2 end; lia ].
    - unfold k_mem, st_at, st_rest, s_ret, s_out; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std.
      all: first [exact HAG | unfold s_out in SOUT; icx_cbn; exact SOUT | exact I]. }
  pose proof ITABLE as ITABLE1. unfold itable_spec_s, itable_spec_at in ITABLE1.
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    lazymatch goal with H120 : mem_u32 _ Mx (p + 136) 9, H144 : mem_u64 _ Mx (p + 160) (p + 1384) |- _ =>
      rename H120 into C120n; rename H144 into C144n end;
    destruct (work_arr Mx p Wp ltac:(lia) ltac:(rewrite TW64; lia)) as (wf & Hwork & Rwf);
    dand (rom_it_tabs Mx ROM) as (RT1 & RT2 & RT3 & RT4);
    (let RETPC := eval cbv in L_LENS_RET in
     let fr := eval cbv in (- FR_INF) in
     eapply (ITABLE1 Rx lx Mx MD T LENS p 0 nlen 0 9 (p + 136) (u + fr) RETPC zc lf cf wf Hh)) end).
  all: itable_pre SEP AL Wstk LF15.
  clear ITABLE1.
  intros R' M' cf' wf' Hrv Hret3 Hcf' Hwf' Rcf' Rwf' HP Hlens' Hcodes' Hwork' Hnext' Hbits' KE.
  set (r := inflate_table _ _ _ _ _ _ _ _) in *.
  assert (BR : it_ret r = 0 ->
     tab_ok LENS (rdc cf' (CDyn 0)) (it_bits r) (it_table r - 0) = true /\ 1 <= it_bits r <= 15 /\
     0 + 2 ^ it_bits r <= it_table r <= 0 + it_room LENS /\ (forall i, 0 <= i < N_CODES -> ~ (0 <= i < it_table r) -> cf' i = cf i)).
  { intros Hr0. apply (tab_ok_of_itable LENS lf cf wf cf' 0 nlen 0 9); cbv [N_LENS N_CODES]; cbn [it_room]; cbv [ENOUGH_LENS]; try assumption; try lia.
    - intros s Hs. replace (0 + s) with s by lia. apply LF15. lia.
    - intros X; discriminate X.
    - intros X; discriminate X. }
  assert (FS1 : it_ret r <> 0 -> it_table r = 0 /\ it_bits r = 9).
  { intros Hne. exact (inflate_table_fail_shape LENS (arr_init N_LENS lf) 0 nlen (arr_init N_CODES cf) 0 9 (arr_init N_WORK wf) Hne). }
  clearbody r.
  unfold kept_eq in KE. zkeys. destr_conj KE. zimps.
  clear Hwork RT1 RT2 RT3 RT4 C120n C144n Hcodes Hlens.
  unfold it_fp in HP. cbv [o_next o_work o_codes o_lenbits N_WORK N_CODES FR_IT] in HP. zreattachL HP.
  cbv [o_lens o_codes o_work o_next o_lenbits N_LENS N_CODES N_WORK] in Hlens', Hcodes', Hwork', Hnext', Hbits'.
  cbv [N_CODES] in Rcf', BR. cbv [N_WORK] in Rwf'. cbn [it_room] in BR. cbv [ENOUGH_LENS] in BR.
  destruct (Z.eq_dec (it_ret r) 0) as [Hr0 | Hnz1].
  2: {
    destruct (FS1 Hnz1) as [Ht0 Hb9]. clear BR FS1.
    assert (Hrm : exists rm, it_ret r mod 18446744073709551616 = rm /\ rm <> 0 /\ 0 <= rm < 18446744073709551616).
    { exists (it_ret r mod 18446744073709551616). split; [reflexivity|].
      destruct Hret3 as [E | [E | E]]; [exfalso; exact (Hnz1 E) | rewrite E | rewrite E];
        [ rewrite Z.mod_small by lia_std; lia_std
        | replace ((-1) mod 18446744073709551616) with 18446744073709551615 by reflexivity; lia_std ]. }
    dand Hrm as (rm & Hrm & Hrm0 & Hrm1).
    zuntil Rfd (idtac; lazymatch goal with HS : mem_u64 _ ?Mx _ (it_ret r) |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      apply mem_u64_mod in HS; rewrite Hrm in HS end).
    pose proof (sinv_cl_bad _ _ lf cf cf' rm (it_bits r) dc db (it_table r) SI0 eq_refl (conj (proj1 Hrm1) (proj2 Hrm1))
                  ltac:(lia) ltac:(lia) Hdc ltac:(lia) ltac:(cbv [N_CODES]; lia) ltac:(cbv [N_CODES]; exact Rcf')) as [SI1 ME1].
    unfold st_tab in SI1, ME1. ist_cbn.
    rewrite Ht0 in *. rewrite Hb9 in *.
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KRA1 Rx Mx _ lf cf' SI1 ME1) end).
    + unfold s_regs_reload; icx_cbn; zkeys; split_conj; try zreg. all: intros C; discriminate C.
    + unfold k_mem, st_at, st_rest, s_ret, s_out; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [BAD]; assumption | exact HAG | unfold s_out in SOUT; icx_cbn; exact SOUT | exact I | eapply mem_u64_eqv; [| eassumption]; lia ]. }
  dand (BR Hr0) as (TOK1 & Hb15 & Htab1 & Hout1). clear BR FS1.
  rewrite Hr0 in Hrv. rewrite Z.sub_0_r in TOK1.
  pose proof (pow2_pos (it_bits r) ltac:(lia)) as Hpw1.
  pose proof ITABLE as ITABLE2. unfold itable_spec_s, itable_spec_at in ITABLE2.
  zuntil_h Rfd (first [ zhint S_TableL.shiftl_1m ])
    (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      lazymatch goal with H124 : mem_u32 _ Mx (p + 140) 6, H112 : mem_u64 _ Mx (p + 128) _ |- _ =>
        rename H124 into C124n; rename H112 into C112n end;
      dand (rom_it_tabs Mx ROM) as (RT1 & RT2 & RT3 & RT4);
      (let RETPC := eval cbv in L_DISTS_RET in
       let fr := eval cbv in (- FR_INF) in
       eapply (ITABLE2 Rx lx Mx MD T DISTS p nlen ndist (it_table r) 6 (p + 140) (u + fr) RETPC zc lf cf' wf' Hh)) end).
  all: itable_pre SEP AL Wstk LF15.
  clear ITABLE2.
  intros R'' M'' cf'' wf'' Hrv2 Hret32 Hcf'' Hwf'' Rcf'' Rwf'' HP2 Hlens'' Hcodes'' Hwork'' Hnext'' Hbits'' KE2.
  set (r2 := inflate_table _ _ _ _ _ _ _ _) in *.
  assert (BR2 : it_ret r2 = 0 ->
     tab_ok DISTS (rdc cf'' (CDyn (it_table r))) (it_bits r2) (it_table r2 - it_table r) = true /\ 1 <= it_bits r2 <= 15 /\
     it_table r + 2 ^ it_bits r2 <= it_table r2 <= it_table r + it_room DISTS /\
     (forall i, 0 <= i < N_CODES -> ~ (it_table r <= i < it_table r2) -> cf'' i = cf' i)).
  { intros Hr0'. apply (tab_ok_of_itable DISTS lf cf' wf' cf'' nlen ndist (it_table r) 6); cbv [N_LENS N_CODES]; cbn [it_room]; cbv [ENOUGH_DISTS]; try assumption; try lia.
    - intros s Hs. apply LF15. lia.
    - intros X; discriminate X. }
  assert (FS2 : it_ret r2 <> 0 -> it_table r2 = it_table r /\ it_bits r2 = 6).
  { intros Hne. exact (inflate_table_fail_shape DISTS (arr_init N_LENS lf) nlen ndist (arr_init N_CODES cf') (it_table r) 6 (arr_init N_WORK wf') Hne). }
  clearbody r2.
  unfold kept_eq in KE2. zkeys. destr_conj KE2. zimps.
  clear RT1 RT2 RT3 RT4 C124n Hcodes' Hlens' Hwork' Hnext'.
  unfold it_fp in HP2. cbv [o_next o_work o_codes o_distbits N_WORK N_CODES FR_IT] in HP2. zreattachL HP2.
  cbv [o_lens o_codes o_work o_next o_distbits N_LENS N_CODES N_WORK] in Hlens'', Hcodes'', Hwork'', Hnext'', Hbits''.
  cbv [N_CODES] in Rcf'', BR2. cbn [it_room] in BR2. cbv [ENOUGH_DISTS] in BR2.
  zto_branch Rfd.
  destruct (Z.eq_dec (it_ret r2) 0) as [Hr20 | Hnz2].
  -
    dand (BR2 Hr20) as (TOK2 & Hb25 & Htab2 & Hout2). clear BR2 FS2.
    rewrite Hr20 in *.
    pose proof (pow2_pos (it_bits r2) ltac:(lia)) as Hpw2.
    assert (TOK1' : tab_ok LENS (rdc cf'' (CDyn 0)) (it_bits r) (it_table r) = true).
    { eapply tab_ok_ext_rd; [| exact TOK1]. intros i Hi. unfold rdc. apply Hout2; cbv [N_CODES]; lia. }
    pose proof (sinv_cl_len_ _ _ lf cf cf'' (it_bits r) (it_table r) (it_bits r2) (it_table r2) SI0 eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbv [N_CODES]; lia)
                  TOK1' TOK2 ltac:(cbv [N_CODES]; exact Rcf'')) as [SI1 ME1].
    unfold st_tab in SI1, ME1. ist_cbn.
    zuntil Rfd (idtac;
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (lenu_s (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (IST LEN_ last flags cin cout hold bits out 0 length offset extra (CDyn 0) (CDyn (it_table r)) (it_bits r) (it_bits r2)
                     ncode nlen ndist shave (it_table r2) whave wnext)
                lf cf'' CX0 Hh Hfin eq_refl SI1) end).
    + unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    + unfold k_mem, st_at, st_rest, s_ret, s_out; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [LEN_]; assumption | exact HAG | unfold s_out in SOUT; icx_cbn; exact SOUT | exact I | eapply mem_u64_eqv; [| eassumption]; lia ].
    + eapply KALL_mono; [| exact KA0]. clear - ME1. lia.
  -
    destruct (FS2 Hnz2) as [Ht2 Hb6]. clear BR2 FS2.
    assert (Hrm : exists rm, it_ret r2 mod 18446744073709551616 = rm /\ rm <> 0 /\ 0 <= rm < 18446744073709551616).
    { exists (it_ret r2 mod 18446744073709551616). split; [reflexivity|].
      destruct Hret32 as [E | [E | E]]; [exfalso; exact (Hnz2 E) | rewrite E | rewrite E];
        [ rewrite Z.mod_small by lia_std; lia_std
        | replace ((-1) mod 18446744073709551616) with 18446744073709551615 by reflexivity; lia_std ]. }
    dand Hrm as (rm & Hrm & Hrm0 & Hrm1).
    lazymatch goal with HS : mem_u64 _ ?Mx _ (it_ret r2) |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      apply mem_u64_mod in HS; rewrite Hrm in HS end.
    pose proof (sinv_cl_bad _ _ lf cf cf'' rm (it_bits r) (CDyn (it_table r)) (it_bits r2) (it_table r2) SI0 eq_refl (conj (proj1 Hrm1) (proj2 Hrm1))
                  ltac:(lia) ltac:(lia) ltac:(cbv [N_CODES]; lia) ltac:(lia) ltac:(cbv [N_CODES]; lia) ltac:(cbv [N_CODES]; exact Rcf'')) as [SI1 ME1].
    unfold st_tab in SI1, ME1. ist_cbn.
    rewrite Ht2 in *. rewrite Hb6 in *.
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KRA1 Rx Mx _ lf cf'' SI1 ME1) end).
    + unfold s_regs_reload; icx_cbn; zkeys; split_conj; try zreg. all: intros C; discriminate C.
    + unfold k_mem, st_at, st_rest, s_ret, s_out; icx_cbn; cbv [N_LENS N_CODES cp_addr o_codes]; icx_cbn. split_conj; try assumption; try close_std.
      all: first [ cbv [BAD]; assumption | exact HAG | unfold s_out in SOUT; icx_cbn; exact SOUT | exact I | eapply mem_u64_eqv; [| eassumption]; lia ].
Qed.

End CLT.
End S_CodelensT.

Module S_CodelensL.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_DistL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* the text's own labels: moved to the layout; the old names stand as parse-only notations of its fields *)
Notation L_CL_LOOP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_LOOP (only parsing).
Notation L_CL_DLOOP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_DLOOP (only parsing).
Notation L_CL_RES := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_RES (only parsing).
Notation L_CL_P17 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_P17 (only parsing).
Notation L_CL_X17 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_X17 (only parsing).
Notation L_CL_P16 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_P16 (only parsing).
Notation L_CL_X16 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_X16 (only parsing).
Notation L_CL_P18 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_P18 (only parsing).
Notation L_CL_X18 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_X18 (only parsing).
Notation L_CL_CHK := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_CHK (only parsing).
Notation L_CL_FILL := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_FILL (only parsing).
Notation L_CL_FILLX := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_FILLX (only parsing).
Notation L_CL_NEXT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CL_NEXT (only parsing).
Notation L_LVX_CL := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LVX_CL (only parsing).
Notation L_LEAVE_A7 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LEAVE_A7 (only parsing).
Notation L_BADREP0 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_BADREP0 (only parsing).
Notation L_BADREP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_BADREP (only parsing).
(* the meaning words of the list form *)
Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Notation fholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds (only parsing).
Notation qargs := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs (only parsing).

Lemma ctab_bits : forall cf lb nx i,
  tab_ok CODES (rdc cf (CDyn 0)) lb nx = true -> 0 <= i < 2 ^ lb -> 1 <= code_bits (cf i) <= lb /\ 2 ^ lb <= nx.
Proof.
  intros cf lb nx i T Hi. pose proof (tab_root_entry CODES (rdc cf (CDyn 0)) lb nx i T Hi) as (X & _ & Y & _).
  unfold rdc in X. rewrite Z.add_0_l in X. split; [exact X | exact Y].
Qed.
Lemma zext32_shift31 : forall x, 0 <= x < 4294967296 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) (31 mod 64) = 2 * x.
Proof.
  intros x Hx. change (31 mod 64) with 31. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma land3_range : forall x, 0 <= Z.land x 3 < 4.
Proof. intros. apply land_ones_range with (k := 2). lia_std. Qed.
Lemma land7_range' : forall x, 0 <= Z.land x 7 < 8.
Proof. intros. apply land_ones_range with (k := 3). lia_std. Qed.
Lemma land127_range : forall x, 0 <= Z.land x 127 < 128.
Proof. intros. apply land_ones_range with (k := 7). lia_std. Qed.

(* the four keep lists: moved to the layout; the old names stand as parse-only notations of its fields *)
Notation KS_CP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_gbb_cp (only parsing).
Notation KS_CD := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_gbb_cd (only parsing).
Notation KS_CF := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_gbb_cf (only parsing).
Notation KS_CX := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_gbb_cx (only parsing).
Ltac keptc_closeC := cbv [keptc KS_CP KS_CD KS_CF KS_CX]; split_conj; try exact I; zreg.
Ltac keptc_chainC HK := cbv [keptc KS_CP KS_CD KS_CF KS_CX] in HK |- *; destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].

(* OPENERS OF THE LIST FORM (they only unfold, split and name). `gbb_open H`: a list-form hypothesis: the meaning
   over the layout's list is unfolded, the conjunction split and its parts named. `split_lists`: the same for a
   goal of that form (any other goal is left as it is). *)
Ltac gbb_unfold_in H :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_pull OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_pull_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_pull_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_dec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_dec_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_dec_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_stub OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_stub_dn OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_gbb_stub
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_fill OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_fill_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_res OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_res_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_res_bad
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_res_nx OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_chk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_x16
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_x1718
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_xd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_xa
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_bad OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_res OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_stub_k OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_gbb_jt] in H.
Ltac gbb_open H :=
  gbb_unfold_in H;
  repeat match type of H with context [zget_l ?RJ [] ?KJ] => change (zget_l RJ [] KJ) with (zget RJ KJ) in H end;
  destr_conj H.
Ltac open_lists :=
  repeat match goal with
         | HJ : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ |- _ => gbb_open HJ
         | HJ : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds _ _ _ _ _ |- _ => gbb_open HJ
         end.
Ltac gbb_split_goal :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_pull OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_pull_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_pull_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_dec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_dec_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_dec_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_stub OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_stub_dn OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_gbb_stub
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_fill OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_fill_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_res OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_res_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_res_bad
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_res_nx OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_chk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_x16
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_x1718
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_xd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_xa
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_bad OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_res OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_stub_k OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_gbb_jt];
  repeat match goal with |- context [zget_l ?RJ [] ?KJ] => change (zget_l RJ [] KJ) with (zget RJ KJ) end;
  split_conj.
Ltac split_lists :=
  lazymatch goal with
  | |- OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ => gbb_split_goal
  | |- OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds _ _ _ _ _ => gbb_split_goal
  | |- _ => idtac
  end.

Lemma cl_pull {RCa1 : RunCtx}  : forall (N : nat) (pc pcx : Z) Rb l M MD T (q n need c0 b0 ci B H : Z) (fin : Z -> Z),
  ((pc = L_CL_P17 /\ pcx = L_CL_X17) \/ (pc = L_CL_P16 /\ pcx = L_CL_X16) \/ (pc = L_CL_P18 /\ pcx = L_CL_X18)) ->
  m_halted MD = None ->
  (* the list's values: the input left; the next input address; the bit count; the bits needed; the hold *)
  rholds (qargs [n - ci; q + ci; B; need; H]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_pull ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < need -> need <= 22 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  (forall R' (H' : Z),
     rholds (qargs [H'; q + n; b0 + 8 * (n - c0)]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_pull_lv ->
     0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) < need -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_CP ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_A7 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     rholds (qargs [n - ci'; q + ci'; B'; H']) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_pull_dn ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> need <= B' -> B' <= 29 ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_CP ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pcx (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros pc pcx Rb l M MD T q n need c0 b0 ci B H fin Hpc Hh LR
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt Hneed HH1 HH2 HBc Hq1 Hn26 Hq2 Hin Rfin KX KD; [lia|].
  gbb_open LR.
  zkeys. unfold L_CL_P17, L_CL_X17, L_CL_P16, L_CL_X16, L_CL_P18, L_CL_X18, L_LEAVE_A7 in *. pose proof two64_eq as TW64.
  pose proof (pow2_48 B ltac:(lia)) as HPB. pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct Hpc as [[-> ->] | [[-> ->] | [-> ->]]]; (
    lazymatch goal with |- realizes _ (zcfg _ ?PC _ _ _) _ =>
    destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz];
    [ zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end); split_lists; try zreg; try lia;
      [ replace (b0 + 8 * (n - c0)) with B by lia; lia | keptc_closeC ]
    | pose proof (Rfin ci ltac:(lia)) as Rb1;
      pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]; rewrite pow2_add8 in Hp1 by lia;
      assert (HH' : 0 <= H + fin ci * 2 ^ B < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia);
      zto_branch_h Rfd (first [ zhint shl_byte ]);
      destruct (Z_lt_dec (B + 8) need) as [Hmore | Hdone];
      [ zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ PC (zupd ?Rx ?lx) ?Mx ?MDx) ?Tx =>
          eapply (IH _ _ Rx lx Mx MDx Tx q n need c0 b0 (ci + 1) (B + 8) (H + fin ci * 2 ^ B) fin) end);
        [ first [left; split; reflexivity | right; left; split; reflexivity | right; right; split; reflexivity] | ..];
        split_lists; try zreg; try lia; try eassumption;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? HK; eapply KD; try eassumption; try lia; keptc_chainC HK
      | zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) (H + fin ci * 2 ^ B)) end);
        split_lists; try zreg; try lia; keptc_closeC ] ] end).
Qed.

Lemma cl_decode {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (u p q n lb lm nx c0 b0 ci B H : Z) (fin cf : Z -> Z),
  m_halted MD = None ->
  (* a frame list that binds no value; its base: the stream's address *)
  fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs []) M u OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_gbb_jt ->
  (* the list's values: the stream's address; the state's address; the root mask; the next input address; the
     input left; the bit count; the hold *)
  rholds (qargs [u; p; lm; q + ci; n - ci; B; H]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_dec ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < code_bits (cf (Z.land lm H)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= 1444 -> tab_ok CODES (rdc cf (CDyn 0)) lb nx = true ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 ->
  p + 8200 <= u -> u + 208 <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 cf ->
  (forall R' (H' : Z),
     rholds (qargs [H']) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_dec_lv ->
     0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 22 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_CD ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_CL (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     rholds (qargs [q + ci'; n - ci'; B'; H'; code_bits (cf (Z.land lm H')); Z.land lm H']) R' []
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_dec_dn ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> code_bits (cf (Z.land lm H')) <= B' -> B' <= 22 ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_CD ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_RES (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_DLOOP (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T u p q n lb lm nx c0 b0 ci B H fin cf Hh HJT LR
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hdm Hlb1 Hlb2 Hnx1 Hnx2 TOK Hq1 Hn26 Hq2 Hp1 Hp2 Hu1 Hu2 Hin Rfin Hcodes KX KD; [lia|].
  gbb_open LR. pose proof HJT as HJTo. gbb_open HJTo.
  zkeys. unfold L_CL_DLOOP, L_CL_RES, L_LVX_CL in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (ctab_bits cf lb nx (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits0 Hpow].
  assert (HB14 : B <= 14) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end); split_lists; try zreg; try lia.
    all: first [replace (b0 + 8 * (n - c0)) with B by lia; lia | keptc_closeC]. }
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1']. rewrite pow2_add8 in Hp1' by lia.
  assert (HH' : 0 <= fin ci * 2 ^ B + H < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia).
  pose proof (land_mask_l (fin ci * 2 ^ B + H) lb ltac:(lia)) as Ri1. rewrite <- Hdm in Ri1.
  pose proof (ctab_bits cf lb nx (Z.land lm (fin ci * 2 ^ B + H)) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits1 _].
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  zuntil_h Rfd (first [ zhint shl_byte | zhint shiftl_2 ]) (idtac; tld4_bits Hcodes (Z.land lm (fin ci * 2 ^ B + H))).
  zto_branch Rfd.
  set (H' := fin ci * 2 ^ B + H) in *. clearbody H'. clear Hp0 Hp1'.
  destruct (Z_lt_dec (B + 8) (code_bits (cf (Z.land lm H')))) as [Hmore | Hdone].
  - zuntil Rfd (idtac;
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T u p q n lb lm nx c0 b0 (ci + 1) (B + 8) H' fin cf Hh HJT) end);
      split_lists; try zreg; try lia; try eassumption.
    intros R' ci' B' H'' GR X1 X2 X3 X4 X5 X6 X7 X8 HK.
    eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chainC HK.
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) H') end);
      split_lists; try zreg; try lia.
    all: keptc_closeC.
Qed.

Lemma stub_CL {RCa1 : RunCtx}  : forall Rb l M MD T (q n c0 b0 u rv : Z),
  m_halted MD = None ->
  (* the list's values: the input left; the next input address; the bit count; the stream's address *)
  rholds (qargs [n - c0; q + c0; b0; u]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_stub ->
  0 <= n - c0 -> n - c0 < 4294967296 ->
  (* the frame list's value: the return value so far; its base: the stream's address *)
  fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs [rv]) M u OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_gbb_stub ->
  (* the list's values: the bit count; the input's end; the return value so far *)
  (forall R', rholds (qargs [b0 + 8 * (n - c0); q + n; rv]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_stub_k ->
     keptc Rb l R' KS_CX -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_CL (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T q n c0 b0 u rv Hh LR H1 H2 Hrv K.
  gbb_open LR. gbb_open Hrv.
  zkeys. unfold L_LVX_CL, L_LEAVE in *.
  zuntil_h Rfd (first [ zhint shiftl_3 | zhint_by zext32_shift ltac:(zlia) ])
    (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end); split_lists; try zreg. keptc_closeC.
Qed.

Ltac zside1c := first [reflexivity | exact I | zlia].
Ltac tstore_arrPc fd Ha i HP HPres :=
  lazymatch type of Ha with
  | mem_arr ?k ?segs ?M ?base ?n ?f =>
      let pc := zpc in
      fd pc ltac:(fun F E D =>
        lazymatch type of D with
        | decode_any _ = Some (Store SZ1 _ _ _, _) =>
            eapply zu_sb; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        | decode_any _ = Some (Store SZ2 _ _ _, _) =>
            eapply zu_sh; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        | decode_any _ = Some (Store SZ4 _ _ _, _) =>
            eapply zu_sw; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        end);
      lazymatch goal with
      | |- realizes _ (zcfg _ _ _ (wbytes M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
          apply (mem_arr_upd segs k M base n f a i v) in Ha; [| zlia | zlia];
          (let kn := eval cbv in (Z.to_nat k) in change (Z.to_nat k) with kn in Ha);
          (let HP' := fresh in pose proof (HPres M a v HP ltac:(zside1c) ltac:(zside1c)) as HP'; clear HP; rename HP' into HP);
          repeat match goal with
          | H : mem_arr ?k' segs M ?base' ?n' ?f' |- _ =>
              first [ apply (mem_arr_frame segs k' M base' n' f' a (Z_to_le_bytes kk v)) in H; [|unfold zdisj; zlen_norm; zlia]
                    | clear H ]
          end;
          zmem_post
      end
  end.
Ltac tstorePc fd HP HPres :=
  let pc := zpc in
  fd pc ltac:(fun F E D =>
    lazymatch type of D with
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply zu_sh; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply zu_sw; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply zu_sd; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
    end);
  lazymatch goal with
  | |- realizes _ (zcfg _ _ _ (wbytes ?M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
      (let HP' := fresh in pose proof (HPres M a v HP ltac:(zside1c) ltac:(zside1c)) as HP'; clear HP; rename HP' into HP);
      zmem_post_arr; zmem_post
  end.

Lemma cl_fill {RCa1 : RunCtx}  : forall (N : nat) (P : mem -> Prop) Rb l M MD T (u p q n j je len : Z) (fin cf lf : Z -> Z),
  m_halted MD = None ->
  (* the list's values: the index; the end index; the length to store; the state's address *)
  rholds (qargs [j; je; len; p]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_fill ->
  je - j <= Z.of_nat N -> 0 <= j -> j < je -> je <= 320 -> 0 <= len -> len < 65536 ->
  0 < p -> p + 7176 <= 140737488355328 -> 1 <= q -> 0 <= n -> q + n <= 140737488355328 -> p + 8200 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 cf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  P M ->
  (forall M' (a v : Z), P M' -> p + 168 <= a -> a + 2 <= p + 808 -> P (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' M' (lf' : Z -> Z),
     rholds (qargs [je]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_fill_dn ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> P M' ->
     (forall i, 0 <= i < 320 -> j <= i < je -> lf' i = len) ->
     (forall i, 0 <= i < 320 -> ~ (j <= i < je) -> lf' i = lf i) ->
     keptc Rb l R' KS_CF ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_FILLX (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_FILL (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T u p q n j je len fin cf lf Hh LR
    HN Hj0 Hj1 Hje Hl0 Hl1 Hp1 Hp2 Hq1 Hn0 Hq2 Hu1 Hu2 SPQ Wp Hin Hcodes Hlens HP HPb KD; [lia|].
  gbb_open LR.
  zkeys. unfold L_CL_FILL, L_CL_FILLX in *. pose proof two64_eq as TW64.
  zuntil_h Rfd (first [ zhint zext32_shift31 ]) (idtac; tstore_arrPc Rfd Hlens j HP HPb).
  destruct (Z.eq_dec (j + 1) je) as [Hlast | Hmore].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KD Rx Mx (zfupd lf j len)) end);
      split_lists; try zreg; try eassumption.
    all: first [ intros i Hi Hij; unfold zfupd; destruct (Z.eqb_spec i j); first [reflexivity | lia] | keptc_closeC ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T u p q n (j + 1) je len fin cf _ Hh) end);
      split_lists; try zreg; try lia; try eassumption.
    intros R' M' lf' G14 W' Hin' Hcodes' Hlens' HP' Hin_ Hout_ HK.
    eapply (KD R' M' lf'); try eassumption.
    all: first [ intros i Hi Hij;
                 first [ destruct (Z.eq_dec i j) as [-> | Hne];
                         [ rewrite Hout_ by lia; unfold zfupd; rewrite Z.eqb_refl; reflexivity | apply Hin_; lia ]
                       | rewrite Hout_ by lia; unfold zfupd; destruct (Z.eqb_spec i j); [lia | reflexivity] ]
               | keptc_chainC HK ].
Qed.
End S_CodelensL.

Module S_Codelens.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_MatchL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_DistL S_TableL S_Table S_ClDefs S_CodelensL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* the keep list: moved to the layout; the old name stands as a parse-only notation of its field *)
Notation KS_CR := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_gbb_cr (only parsing).
Ltac keptc_closeR := cbv [keptc KS_CR KS_CP KS_CD KS_CF KS_CX]; split_conj; try exact I; zreg.
Ltac kopen HK := open_lists; cbv [keptc KS_CR KS_CP KS_CD KS_CF KS_CX] in HK; destr_conj HK; zimps.
Ltac keptc_transC :=
  repeat match goal with H : keptc _ _ _ _ |- _ => cbv [keptc KS_CR KS_CP KS_CD KS_CF KS_CX] in H; destr_conj H end;
  cbv [keptc KS_CR KS_CP KS_CD KS_CF KS_CX]; split_conj; try exact I;
  rewrite ?zget_zupd in *; cbv [zget_l] in *; cbn [alookup Pos.eqb] in *;
  first [ assumption | reflexivity
        | etransitivity; [eassumption|]; first [assumption | reflexivity | symmetry; assumption] ].
Ltac kgoal := split_lists; first [ zreg | assumption | OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ITac.zarith_goal; lia | etransitivity; [eassumption | solve [lia | symmetry; assumption]] | keptc_transC ].

(* A HINT LEMMA (new): a right shift of a value below the word size by an amount below the word's bit count *)
Lemma srl_u64 : forall h k, 0 <= h < 18446744073709551616 -> 0 <= k <= 63 ->
  Z.shiftr (h mod 18446744073709551616) (k mod 64) = h / 2 ^ k.
Proof.
  intros h k Hh Hk. rewrite (Z.mod_small k 64) by lia. rewrite (Z.mod_small h) by lia.
  apply Z.shiftr_div_pow2. lia.
Qed.

Lemma cl_res {RCa1 : RunCtx}  : forall (P : Z -> mem -> Prop) Rb l M MD T (u p q n nlen nd lb lm nx c0 b0 j ci B H : Z) (fin cf lf : Z -> Z),
  m_halted MD = None ->
  (* the list's values: the stream's address; the state's address; the count of length codes; the count of all
     codes; the root mask; the index; the next input address; the input left; the bit count; the bit count at
     the entry; the hold; the entry's bit length; the entry's index *)
  rholds (qargs [u; p; nlen; nd; lm; j; q + ci; n - ci; B; b0; H; code_bits (cf (Z.land lm H)); Z.land lm H]) Rb l
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_res ->
  0 <= j -> j < nd -> nd <= 316 -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  code_bits (cf (Z.land lm H)) <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= 1444 -> tab_ok CODES (rdc cf (CDyn 0)) lb nx = true ->
  (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) -> (forall i, 0 <= i < j -> lf i <= 15) ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 -> p + 8200 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 cf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  P j M ->
  (forall M' (a v : Z), P j M' -> a = p + 156 -> 0 <= v < 4294967296 -> P v (wbytes M' (w64 a) (Z_to_le_bytes 4 v))) ->
  (forall M' (jo a v : Z), P jo M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' (ci' B' H' : Z),
     rholds (qargs [H'; n - ci'; q + ci'; B'; b0]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_res_lv ->
     ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ci) + B ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_A7 (zupd R' []) M MD) T) ->
  (forall (pc : Z) R' (ci' B' H' : Z),
     (pc = L_BADREP0 \/ pc = L_BADREP) ->
     rholds (qargs [H'; n - ci'; q + ci'; B']) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_res_bad ->
     ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ci) + B ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd R' []) M MD) T) ->
  (forall R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     rholds (qargs [j'; H'; n - ci'; q + ci'; B']) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_res_nx ->
     j < j' -> j' <= nd -> ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' + 1 <= 8 * (n - ci) + B ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_NEXT (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_RES (zupd Rb l) M MD) T.
Proof.
  intros P Rb l M MD T u p q n nlen nd lb lm nx c0 b0 j ci B H fin cf lf Hh
    LR
    Hj0 Hj1 Hnd Hc0 Hc1 Hc2 Hb0 HB Hbe HB40 HH1 HH2 HBc Hdm Hlb1 Hlb2 Hnx1 Hnx2 TOK Rlf Hlf15
    Hq1 Hn0 Hn26 Hq2 Hp1 Hp2 Hpu Hu2 SPQ Wp Hin Rfin Hcodes Hlens HP HPa HPb KX KB KN.
  gbb_open LR.
  zkeys. unfold L_CL_RES, L_CL_NEXT, L_LEAVE_A7, L_BADREP0, L_BADREP, L_CL_P17, L_CL_X17, L_CL_P16, L_CL_X16, L_CL_P18, L_CL_X18,
    L_CL_CHK, L_CL_FILL, L_CL_FILLX in *.
  pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (ctab_bits cf lb nx (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits0 Hpow].
  set (e := cf (Z.land lm H)) in *.
  pose proof (code_bits_range e) as Rbe. pose proof (code_val_range e) as Rve.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  zuntil_h Rfd (first [ zhint shiftl_2 ]) (idtac; tld4_val Hcodes (Z.land lm H)).
  fold e.
  zto_branch Rfd.
  (* the two error places' continuations, each bound to its label outside the run calls *)
  pose proof (KB L_BADREP) as KBR. pose proof (KB L_BADREP0) as KBR0.
  assert (CHK : forall RC (ci' B' H' copy len : Z),
    (* the list's values: the repeat count; the length to repeat; the hold; the bit count; the input left; the
       next input address; the index; the count of all codes; the state's address *)
    rholds (qargs [copy; len; H'; B'; n - ci'; q + ci'; j; nd; p]) RC [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_chk ->
    3 <= copy -> copy <= 138 -> 0 <= len -> len <= 15 ->
    ci <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
    8 * (n - ci') + B' + 1 <= 8 * (n - ci) + B ->
    keptc Rb l RC KS_CR ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_CHK (zupd RC []) M MD) T).
  { intros RC ci' B' H' copy len GR Hcp1 Hcp2 Hln1 Hln2 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 HK.
    open_lists.
    zkeys. unfold L_CL_CHK.
    zto_branch Rfd.
    destruct (Z_lt_dec nd (copy + j)) as [Hover | Hfit].
    - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KBR Rx ci' B' H') end);
        try (right; reflexivity). all: kgoal.
    - pose proof (fun M1 a1 v1 => HPb M1 j a1 v1) as HPbj.
      pose proof (fun RJ LJ MJ => cl_fill (Z.to_nat 138) (P j) RJ LJ MJ MD T u p q n j (copy + j) len fin cf lf Hh) as FILLJ.
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (FILLJ Rx lx Mx) end);
        split_lists; try zreg; try lia; try eassumption.
      intros R' M' lf' G14' Wp' Hin' Hcodes' Hlens' HP' Hfill Hkeep HK'. unfold L_CL_FILLX. zimps. kopen HK'. zkeys.
      zuntil0 Rfd (idtac; tstorePc Rfd HP' HPa).
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KN Rx Mx (copy + j) ci' B' H' lf') end); try eassumption.
      all: first [ intros i Hi;
                   first [ destruct (Z_lt_dec i j) as [Hl|Hr]; [rewrite Hkeep by lia; apply Rlf; lia |];
                           destruct (Z_lt_dec i (copy + j)) as [Hm|Hx]; [rewrite Hfill by lia; lia | rewrite Hkeep by lia; apply Rlf; lia]
                         | destruct (Z_lt_dec i j) as [Hl|Hr]; [rewrite Hkeep by lia; apply Hlf15; lia | rewrite Hfill by lia; lia] ]
                 | kgoal ]. }
  destruct (Z_lt_dec 15 (code_val e)) as [Hrep | Hlit].
  2: {
    pose proof (hold_shr_bound H B (code_bits e) ltac:(lia) ltac:(lia)) as HH'.
    pose proof (fun M1 a1 v1 => HPb M1 (j + 1) a1 v1) as HPb1.
    zuntil_h Rfd (first [ zhint srl_u64 ]) (idtac; tstorePc Rfd HP HPa).
    zuntil_h Rfd (first [ zhint zext32_shift31 ]) (idtac; tstore_arrPc Rfd Hlens j HP HPb1).
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KN Rx Mx (j + 1) ci (B - code_bits e) (H / 2 ^ code_bits e) (zfupd lf j (code_val e))) end);
      try eassumption.
    all: first [ intros i Hi; unfold zfupd; destruct (Z.eqb_spec i j); [lia | first [apply Rlf; lia | apply Hlf15; lia]]
               | kgoal ]. }
  zto_branch Rfd.
  destruct (Z.eq_dec (code_val e) 16) as [E16 | N16].
  -
    zto_branch Rfd.
    assert (X16 : forall RX (ci' B' H' : Z),
      (* the list's values: the input left; the next input address; the bit count; the hold; the entry's bit
         length; the index; the state's address; the count of all codes *)
      rholds (qargs [n - ci'; q + ci'; B'; H'; code_bits e; j; p; nd]) RX [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_x16 ->
      ci <= ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> code_bits e + 2 <= B' -> B' <= 40 ->
      0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
      keptc Rb l RX KS_CR ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_X16 (zupd RX []) M MD) T).
    { intros RX ci' B' H' GR Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 HK. kopen HK. zkeys.
      pose proof (pow2_48 B' ltac:(lia)) as HPB'.
      unfold L_CL_X16.
      pose proof (hold_shr_bound H' B' (code_bits e) ltac:(lia) ltac:(lia)) as HS2.
      pose proof (pow2_48 (B' - code_bits e) ltac:(lia)) as HPd.
      zto_branch_h Rfd (first [ zhint srl_u64 ]).
      set (H2 := H' / 2 ^ code_bits e) in *.
      destruct (Z.eq_dec j 0) as [Hj | Hj].
      +
        pose proof (pow2_le (B' - code_bits e) B' ltac:(lia)) as HP2.
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KBR0 Rx ci' (B' - code_bits e) H2) end);
          try (left; reflexivity). all: kgoal.
      + pose proof (Rlf (j - 1) ltac:(lia)) as Rlj. pose proof (Hlf15 (j - 1) ltac:(lia)) as Hlj.
        pose proof (land3_range H2) as Hcp.
        pose proof (hold_shr_bound H2 (B' - code_bits e) 2 ltac:(lia) ltac:(lia)) as HS3.
        pose proof (pow2_le (B' - code_bits e - 2) (B' - code_bits e) ltac:(lia)) as HP3.
        pose proof (fun RJ => CHK RJ ci' (B' - code_bits e - 2) (H2 / 2 ^ 2) (Z.land H2 3 + 3) (lf (j - 1))) as CHK2.
        zuntil_h Rfd (first [ zhint zext32_shift31 | zhint srli_small ])
          (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
            eapply (CHK2 Rx) end).
        all: kgoal. }
    (* the pull loop at this place, bound to its two labels outside the run call *)
    pose proof (fun RJ LJ MJ => cl_pull (S (Z.to_nat (n - ci))) L_CL_P16 L_CL_X16 RJ LJ MJ MD T q n (code_bits e + 2) c0 b0 ci B H fin
                  ltac:(right; left; split; reflexivity) Hh) as PULL16.
    destruct (Z_lt_dec B (code_bits e + 2)) as [Hneed | Hhave].
    + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (PULL16 Rx lx Mx) end);
        split_lists; try zreg; try lia; try eassumption.
      * intros R' H' GR X1 X2 X3 X4 HK. zimps. kopen HK.
        eapply (KX R' n (b0 + 8 * (n - c0)) H'). all: kgoal.
      * intros R' ci' B' H' GR X1 X2 X3 X4 X5 X6 X7 X8 HK. zimps. kopen HK.
        eapply (X16 R' ci' B' H'). all: kgoal.
    + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (X16 Rx ci B H) end). all: kgoal.
  - zto_branch Rfd.
    assert (X1718 : forall (pcx k base : Z) RX (ci' B' H' : Z),
      ((pcx = L_CL_X17 /\ k = 3 /\ base = 3) \/ (pcx = L_CL_X18 /\ k = 7 /\ base = 11)) ->
      (* the list's values: as in the asserted statement before this one *)
      rholds (qargs [n - ci'; q + ci'; B'; H'; code_bits e; j; p; nd]) RX [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_x1718 ->
      ci <= ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> code_bits e + k <= B' -> B' <= 40 ->
      0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
      keptc Rb l RX KS_CR ->
      realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pcx (zupd RX []) M MD) T).
    { intros pcx k base RX ci' B' H' Hpcx GR Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 HK. kopen HK. zkeys.
      pose proof (pow2_48 B' ltac:(lia)) as HPB'.
      destruct Hpcx as [(-> & -> & ->) | (-> & -> & ->)].
      - unfold L_CL_X17.
        pose proof (hold_shr_bound H' B' (code_bits e) ltac:(lia) ltac:(lia)) as HS2.
        pose proof (pow2_48 (B' - code_bits e) ltac:(lia)) as HPd.
        pose proof (land7_range' (H' / 2 ^ code_bits e)) as Hcp.
        pose proof (hold_shr_bound (H' / 2 ^ code_bits e) (B' - code_bits e) 3 ltac:(lia) ltac:(lia)) as HS3.
        pose proof (pow2_le (B' - code_bits e - 3) (B' - code_bits e) ltac:(lia)) as HP3.
        pose proof (fun RJ => CHK RJ ci' (B' - code_bits e - 3) (H' / 2 ^ code_bits e / 2 ^ 3)
                                  (Z.land (H' / 2 ^ code_bits e) 7 + 3) 0) as CHK3.
        zuntil_h Rfd (first [ zhint srl_u64 | zhint srli_small ])
          (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (CHK3 Rx) end).
        all: kgoal.
      - unfold L_CL_X18.
        pose proof (hold_shr_bound H' B' (code_bits e) ltac:(lia) ltac:(lia)) as HS2.
        pose proof (pow2_48 (B' - code_bits e) ltac:(lia)) as HPd.
        pose proof (land127_range (H' / 2 ^ code_bits e)) as Hcp.
        pose proof (hold_shr_bound (H' / 2 ^ code_bits e) (B' - code_bits e) 7 ltac:(lia) ltac:(lia)) as HS3.
        pose proof (pow2_le (B' - code_bits e - 7) (B' - code_bits e) ltac:(lia)) as HP3.
        pose proof (fun RJ => CHK RJ ci' (B' - code_bits e - 7) (H' / 2 ^ code_bits e / 2 ^ 7)
                                  (Z.land (H' / 2 ^ code_bits e) 127 + 11) 0) as CHK7.
        zuntil_h Rfd (first [ zhint srl_u64 | zhint srli_small ])
          (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (CHK7 Rx) end).
        all: kgoal. }
    (* the two join points of the asserted statement and the pull loop at its two places, each bound to its
       labels outside the run calls *)
    pose proof (X1718 L_CL_X17 3 3) as X17. pose proof (X1718 L_CL_X18 7 11) as X18.
    pose proof (fun RJ LJ MJ => cl_pull (S (Z.to_nat (n - ci))) L_CL_P17 L_CL_X17 RJ LJ MJ MD T q n (code_bits e + 3) c0 b0 ci B H fin
                  ltac:(left; split; reflexivity) Hh) as PULL17.
    pose proof (fun RJ LJ MJ => cl_pull (S (Z.to_nat (n - ci))) L_CL_P18 L_CL_X18 RJ LJ MJ MD T q n (code_bits e + 7) c0 b0 ci B H fin
                  ltac:(right; right; split; reflexivity) Hh) as PULL18.
    destruct (Z.eq_dec (code_val e) 17) as [E17 | N17].
    +
      zto_branch Rfd.
      destruct (Z_lt_dec B (code_bits e + 3)) as [Hneed | Hhave].
      * zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (PULL17 Rx lx Mx) end);
          split_lists; try zreg; try lia; try eassumption.
        -- intros R' H' GR X1 X2 X3 X4 HK. zimps. kopen HK.
           eapply (KX R' n (b0 + 8 * (n - c0)) H'). all: kgoal.
        -- intros R' ci' B' H' GR X1 X2 X3 X4 X5 X6 X7 X8 HK. zimps. kopen HK.
           eapply (X1718 L_CL_X17 3 3 R' ci' B' H'); try (left; split_conj; reflexivity). all: kgoal.
      * zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (X17 Rx ci B H) end);
          try (left; split_conj; reflexivity). all: kgoal.
    +
      zto_branch Rfd.
      destruct (Z_lt_dec B (code_bits e + 7)) as [Hneed | Hhave].
      * zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (PULL18 Rx lx Mx) end);
          split_lists; try zreg; try lia; try eassumption.
        -- intros R' H' GR X1 X2 X3 X4 HK. zimps. kopen HK.
           eapply (KX R' n (b0 + 8 * (n - c0)) H'). all: kgoal.
        -- intros R' ci' B' H' GR X1 X2 X3 X4 X5 X6 X7 X8 HK. zimps. kopen HK.
           eapply (X1718 L_CL_X18 7 11 R' ci' B' H'); try (right; split_conj; reflexivity). all: kgoal.
      * zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (X18 Rx ci B H) end);
          try (right; split_conj; reflexivity). all: kgoal.
Qed.

Lemma cl_loop {RCa1 : RunCtx}  : forall (N : nat) (P : Z -> mem -> Prop) Rb l M MD T (u p q n nlen nd lb lm nx ce Be j ci B H : Z) (fin cf lf : Z -> Z),
  m_halted MD = None ->
  (* a frame list that binds no value; its base: the stream's address *)
  (forall (jo : Z) M', P jo M' -> fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs []) M' u OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_gbb_jt) ->
  (* the list's values: the stream's address; the state's address; the count of length codes; the count of all
     codes; the root mask; the index; the next input address; the input left; the bit count; the hold *)
  rholds (qargs [u; p; nlen; nd; lm; j; q + ci; n - ci; B; H]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop ->
  nd - j <= Z.of_nat N -> 0 <= j -> j < nd -> nd <= 316 ->
  ce <= ci -> ci <= n -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci -> 8 * (n - ci) + B <= 8 * (n - ce) + Be ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 0 <= nx -> nx <= 1444 -> tab_ok CODES (rdc cf (CDyn 0)) lb nx = true ->
  (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) -> (forall i, 0 <= i < j -> lf i <= 15) ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= 140737488355328 -> 0 < p -> p + 7176 <= 140737488355328 -> p + 8200 <= u -> u + 208 <= 140737488355328 ->
  ZSEP (p + 7176 <= q \/ q + n <= p) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) 1444 cf -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) 320 lf ->
  P j M ->
  (forall M' (jo a v : Z), P jo M' -> a = p + 156 -> 0 <= v < 4294967296 -> P v (wbytes M' (w64 a) (Z_to_le_bytes 4 v))) ->
  (forall M' (jo a v : Z), P jo M' -> p + 168 <= a -> a + 2 <= p + 808 -> P jo (wbytes M' (w64 a) (Z_to_le_bytes 2 v))) ->
  (forall R' M' (j' ci0 B0 H' : Z) (lf' : Z -> Z),
     rholds (qargs [H'; n - ci0; q + ci0; B0]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_xd ->
     ce <= ci0 -> ci0 <= n -> 0 <= B0 -> B0 + 8 * (n - ci0) <= 40 -> 0 <= H' -> H' < 2 ^ (B0 + 8 * (n - ci0)) ->
     B0 + 8 * (n - ci0) <= 8 * n -> B0 + 8 * (n - ci0) <= 8 * (n - ce) + Be ->
     j <= j' -> j' < nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_CL (zupd R' []) M' MD) T) ->
  (forall R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     rholds (qargs [H'; n - ci'; q + ci'; B']) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_xa ->
     ce <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ce) + Be -> j <= j' -> j' < nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_A7 (zupd R' []) M' MD) T) ->
  (forall (pc : Z) R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     (pc = L_BADREP0 \/ pc = L_BADREP) ->
     rholds (qargs [H'; n - ci'; q + ci'; B']) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_bad ->
     ce <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ce) + Be -> j <= j' -> j' < nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd R' []) M' MD) T) ->
  (forall R' M' (j' ci' B' H' : Z) (lf' : Z -> Z),
     rholds (qargs [H'; n - ci'; q + ci'; B'; j']) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_dn ->
     ce <= ci' -> ci' <= n -> 0 <= B' -> B' <= 40 -> 0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     8 * (n - ci') + B' <= 8 * (n - ce) + Be -> nd <= j' -> j' <= nd ->
     (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j' -> lf' i <= 15) ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
     mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' -> P j' M' ->
     keptc Rb l R' KS_CR ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_DONE (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_LOOP (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T u p q n nlen nd lb lm nx ce Be j ci B H fin cf lf Hh HJT
    LR
    HN Hj0 Hj1 Hnd Hce Hc2 HB0 HB40 HH1 HH2 HBc HW Hdm Hlb1 Hlb2 Hnx1 Hnx2 TOK Rlf Hlf15
    Hq1 Hn0 Hn26 Hq2 Hp1 Hp2 Hpu Hu2 SPQ Wp Hin Rfin Hcodes Hlens HP HPa HPb KXD KXA KBD KDN; [lia|].
  gbb_open LR. pose proof (HJT j M HP) as HJM.
  zkeys. unfold L_CL_LOOP, L_CL_DLOOP, L_CL_RES, L_CL_NEXT, L_CL_DONE, L_LVX_CL, L_LEAVE_A7, L_BADREP0, L_BADREP in *.
  pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPlb. pose proof (pow2_48 B ltac:(lia)) as HPB.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (ctab_bits cf lb nx (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as [Hbits0 Hpow].
  assert (RES : forall RR (ci1 B1 H1 : Z),
    (* the list's values: the stream's address; the state's address; the count of length codes; the count of all
       codes; the root mask; the index; the next input address; the input left; the bit count; the bit count at
       the code's start; the hold; the entry's bit length; the entry's index; the input left and the input
       address at the code's start *)
    rholds (qargs [u; p; nlen; nd; lm; j; q + ci1; n - ci1; B1; B; H1; code_bits (cf (Z.land lm H1)); Z.land lm H1;
                   n - ci; q + ci]) RR [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_gbb_loop_res ->
    ci <= ci1 -> ci1 <= n -> B1 = B + 8 * (ci1 - ci) -> code_bits (cf (Z.land lm H1)) <= B1 -> B1 <= 40 ->
    0 <= H1 -> H1 < 2 ^ B1 -> B1 <= 8 * ci1 ->
    keptc Rb l RR KS_CR ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CL_RES (zupd RR []) M MD) T).
  { intros RR ci1 B1 H1. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
    eapply (cl_res P RR [] M MD T u p q n nlen nd lb lm nx ci B j ci1 B1 H1 fin cf lf Hh);
      split_lists; try (cbv [zget_l alookup]; eassumption); try eassumption; try lia.
    - intros M1 a1 v1 X1 X2 X3. exact (HPa M1 j a1 v1 X1 X2 X3).
    -
      intros R' ci' B' H'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
      eapply (KXA R' M j ci' B' H' lf). all: kgoal.
    -
      intros pc R' ci' B' H' Hpc. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
      eapply (KBD pc R' M j ci' B' H' lf Hpc). all: kgoal.
    -
      intros R' M' j' ci' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. unfold L_CL_NEXT. zkeys.
      pose proof (pow2_48 B' ltac:(lia)) as HPB'.
      zto_branch Rfd.
      destruct (Z_lt_dec j' nd) as [Hlt | Hge].
      + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (IH P Rx lx Mx MD T u p q n nlen nd lb lm nx ce Be j' ci' B' H' fin cf lf' Hh HJT) end);
          split_lists; try zreg; try lia; try eassumption.
        * intros RR9 MM9 jj9 cc9 BB9 HQ9 ll9. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
          eapply (KXD RR9 MM9 jj9 cc9 BB9 HQ9 ll9). all: kgoal.
        * intros RR9 MM9 jj9 cc9 BB9 HQ9 ll9. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
          eapply (KXA RR9 MM9 jj9 cc9 BB9 HQ9 ll9). all: kgoal.
        * intros pc RR9 MM9 jj9 cc9 BB9 HQ9 ll9 Hpc. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
          eapply (KBD pc RR9 MM9 jj9 cc9 BB9 HQ9 ll9 Hpc). all: kgoal.
        * intros RR9 MM9 jj9 cc9 BB9 HQ9 ll9. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
          eapply (KDN RR9 MM9 jj9 cc9 BB9 HQ9 ll9). all: kgoal.
      + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KDN Rx Mx j' ci' B' H' lf') end). all: kgoal. }
  zuntil_h Rfd (first [ zhint shiftl_2 ]) (idtac; tld4_bits Hcodes (Z.land lm H)).
  destruct (Z_lt_dec B (code_bits (cf (Z.land lm H)))) as [Hdec | Hres].
  -
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (cl_decode (S (Z.to_nat (n - ci))) Rx lx Mx MD T u p q n lb lm nx ci B ci B H fin cf Hh HJM) end);
      split_lists; try zreg; try lia; try eassumption.
    + intros R' H'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
      eapply (KXD R' M j ci B H' lf). all: kgoal.
    + intros R' ci' B' H'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end.
      eapply (RES R' ci' B' H'). all: kgoal.
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (RES Rx ci B H) end). all: kgoal.
Qed.

Definition st_cl (st : ist) (ci H B j : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) ci (t_cout st) H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) j (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_cl : forall cx st lf cf ci H B j lf',
  sinv cx st lf cf -> t_mode st = CODELENS ->
  t_cin st <= ci -> ci <= c_n cx -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  0 <= j -> j <= t_nlen st + t_ndist st ->
  (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j -> lf' i <= 15) ->
  sinv cx (st_cl st ci H B j) lf' cf /\ meas cx (st_cl st ci H B j) <= meas cx st.
Proof.
  intros cx st lf cf ci H B j lf' (R & W & P & Mo) Hm H1 H2 H3 H4 H5 H6 H7 H8 Hj0 Hj1 Rlf' Hlf'.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_cl, meas, Wm in *. icx_cbn. subst mode.
  unfold RNG in R. icx_cbn. cbv [N_LENS N_CODES] in R. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mf : flags = -1 -> (CODELENS = HEAD \/ CODELENS = BAD) /\ cout = 0) by mode_get Mo.
  assert (MC : CODELENS = CODELENS -> 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\ shave <= nlen + ndist /\
            (forall i, 0 <= i < shave -> lf i <= 15) /\
            ctable_live (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  specialize (MC eq_refl). dand MC as (A1 & A2 & A3 & A4 & _ & _ & CT). clear Mo.
  unfold ctable_live in CT. cbn [t_lc t_lb t_nx] in CT.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 P3 Mf CT. unfold RNG. icx_cbn. cbv [N_LENS N_CODES]. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 H1 H8. unfold PROG, Wm. icx_cbn. split; [lia_std | split; [lia_std |]].
    destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split; [mode_vacuous |].
    split; [intros _; split_conj; try assumption; unfold ctable_live; cbn [t_lc t_lb t_nx]; exact CT |].
    split_conj; mode_vacuous.
  - clear - H8. lia_std.
Qed.

Section CL.
Context {RCa1 : RunCtx}.
Hypothesis CLDONE : cldone_stmt.

Theorem clhead_s : clhead_stmt.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RG KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0. pose proof KM as KM0.
  open_K K. open_kmem KM. pose proof STD as STD0. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & MODE_).
  assert (MC : t_mode st = CODELENS -> 257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            t_shave st <= t_nlen st + t_ndist st /\ (forall i, 0 <= i < t_shave st -> lf i <= 15) /\ ctable_live st cf) by mode_get MODE_.
  specialize (MC Hm). dand MC as (Hnl1 & Hnl2 & Hnd1 & Hnd2 & Hsh & Hlf15 & CT). clear MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  ist_cbn. subst mode. icx_cbn.
  unfold ctable_live in CT. cbn [t_lc t_lb t_nx] in CT. dand CT as (Hlc & Hlb & Hnx0 & Hnx1 & TOK). cbv [N_CODES] in Hnx1.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  unfold s_regs_cl, s_fix, s_vars in RG. icx_cbn. destr_conj RG. gb_open.
  cbv [N_LENS N_CODES] in Hlens, Hcodes.
  pose proof SREST as SR'. unfold st_rest in SR'. icx_cbn.
  dand SR' as (_ & _ & _ & _ & _ & _ & _ & C104 & _ & C120 & _ & _ & C132 & C136 & C140 & _).
  subst lc. cbv [cp_addr o_codes] in C104. icx_cbn.
  assert (Hshv : 0 <= shave) by (pose proof (Hlf15 0); lia).
  pose proof (PL_intro _ _ _ _ _ _ _ KM0) as [HP _]. cbn [t_shave] in HP.
  clear Ww CST HK Hmode SREST SRET SOUT.
  prune_rng.
  zkeysb. unfold L_CL_HEAD, L_CL_DONE, L_CL_LOOP, L_LVX_CL, L_LEAVE_A7, L_BADREP0, L_BADREP, L_BADMSG_S11, L_LEAVE, L_LEAVE_LD in *.
  cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  zto_branch Rfd.
  destruct (Z_lt_dec shave (nlen + ndist)) as [Hgo | Hdone0].
  2: {
    zuntil Rfd (idtac;
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (CLDONE (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI0) end).
    - unfold s_regs_cld, s_fix, s_vars; gb_split; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - exact KM0.
    - exact KA0. }
  assert (KMX : forall M' (ci' H' B' j' : Z) (lf' : Z -> Z),
    PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
       (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) cf j' M' ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf' ->
    k_mem (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
      (st_cl (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' j') lf' cf M').
  { intros M' ci' H' B' j' lf' HP' HL'. unfold st_cl. ist_cbn.
    pose proof (PL_kmem _ _ _ _ lf' _ _ _ HP' HL') as X. unfold st_sh in X. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in X.
    unfold k_mem in X |- *. dand X as (X1 & X2 & X3 & X3b & X4 & X5 & X6). split_conj; try assumption. }
  (* the frame list's facts are among the frame's slots; a list with no slot means the trivial proposition (HI) *)
  assert (HJT : forall (jo : Z) (Mq : mem),
    PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
       (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) cf jo Mq ->
    fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs []) Mq u OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_gbb_jt).
  { intros jo Mq HPq. pose proof I as HI. destruct HPq as (STDq & _). unfold s_std in STDq.
    destruct STDq as (_ & _ & _ & _ & _ & FRMq & _).
    pose proof FRMq as FSq. unfold i_frame in FSq. icx_cbn. cbv [JTAB_ADDR] in FSq. destr_conj FSq.
    split_lists; assumption. }
  zuntil_h Rfd (first [ zhint mask_not_sllw ]) (idtac;
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (cl_loop (S (Z.to_nat (nlen + ndist - shave)))
              (PL (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
                  (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) cf)
              Rx lx Mx MD T u p q n nlen (nlen + ndist) lb (2 ^ lb - 1) nx cin bits shave cin bits hold fin cf lf Hh HJT) end);
    split_lists; try zreg; try lia; try eassumption; try reflexivity.
  - unfold ZSEP. pose proof (sep_p_q _ _ SEP) as D. cbn [c_p c_q c_n] in D. cbv [STATE_SIZE] in D. exact D.
  - intros M' jo a v HPj Ha Hv. apply (PL_store140 _ _ _ _ _ _ _ _ _ CX0 HPj); [icx_cbn; exact Ha | exact Hv].
  - intros M' jo a v HPj Ha1 Ha2. apply (PL_store_lens _ _ _ _ _ _ _ _ _ CX0 HPj); icx_cbn; lia.
  -
    intros R' M' j' ci0 B0 H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. zkeys.
    match goal with HP' : PL _ _ _ _ _ j' M' |- _ =>
      dand HP' as (STD' & SAT' & SRET' & SOUT' & HC' & HAG'); unfold s_ret in SRET'; unfold st_sh in SAT'; icx_cbn end.
    eapply (stub_CL R' [] M' MD T q n ci0 B0 u ret Hh); split_lists; try (cbv [zget_l alookup]; eassumption); try lia.
    intros R9 ER HK9. kopen HK9.
    pose proof (sinv_cl _ _ lf cf n H' (B0 + 8 * (n - ci0)) j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KL Rx Mx _ ret lf' cf SI1) end.
    + unfold s_regs_leave, st_cl; icx_cbn; zkeys; split_conj; kgoal.
    + exact STD'.
    + unfold st_cl; ist_cbn. exact SAT'.
    + unfold st_cl, s_out in *; ist_cbn. exact SOUT'.
    + assumption.
    + exact HC'.
    + exact HAG'.
  -
    intros R' M' j' ci' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. unfold L_LEAVE_A7. zkeys.
    match goal with HP' : PL _ _ _ _ _ j' M' |- _ =>
      dand HP' as (STD' & SAT' & SRET' & SOUT' & HC' & HAG'); unfold st_sh in SAT'; icx_cbn end.
    pose proof (sinv_cl _ _ lf cf ci' H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KLL Rx Mx _ lf' cf SI1) end).
    + unfold s_regs_leave_ld, st_cl; icx_cbn; zkeys; split_conj; kgoal.
    + exact STD'.
    + unfold st_cl; ist_cbn. exact SAT'.
    + unfold st_cl, s_ret in *; ist_cbn. exact SRET'.
    + unfold st_cl, s_out in *; ist_cbn. exact SOUT'.
    + assumption.
    + exact HC'.
    + exact HAG'.
  -
    intros pc R' M' j' ci' B' H' lf' Hpc. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. unfold L_BADREP0, L_BADREP in Hpc. zkeys.
    pose proof (sinv_cl _ _ lf cf ci' H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (st_cl (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' j')) as MB.
    unfold st_cl in MB, SI1, ME1 |- *. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in MB, SI1, ME1 |- *. change (rank CODELENS) with 20 in MB.
    destruct Hpc as [-> | ->];
      (zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
         eapply (KB11 Rx Mx (IST CODELENS last flags ci' cout H' B' out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist j' nx whave wnext) lf' cf
                   (sinv_bad_of _ _ _ _ SI1)) end);
       [ clear - MB ME1; lia
       | unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; kgoal
       | first [ zreg | lazymatch goal with |- 0 <= ?x < _ => eassert (EA2 : x = _) by zreg; rewrite EA2 end; lia ]
       | apply KMX; assumption ]).
  -
    intros R' M' j' ci' B' H' lf'. intros. match goal with HK : keptc _ _ _ _ |- _ => kopen HK end. zkeys.
    assert (Ej : j' = nlen + ndist) by lia.
    pose proof (sinv_cl _ _ lf cf ci' H' B' j' lf' SI0 eq_refl ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(assumption) ltac:(assumption)) as [SI1 ME1].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (CLDONE (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx [] Mx
                (st_cl (IST CODELENS last flags cin cout hold bits out ret length offset extra (CDyn 0) dc lb db ncode nlen ndist shave nx whave wnext) ci' H' B' j')
                lf' cf CX0 Hh Hfin eq_refl ltac:(cbn; lia) SI1) end.
    + unfold s_regs_cld, s_fix, s_vars, st_cl; gb_split; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; kgoal.
    + apply KMX; assumption.
    + eapply KALL_mono; [| exact KA0]. clear - ME1. unfold st_cl in ME1. exact ME1.
Qed.

Theorem arm_CODELENS_s0 : arm_stmt L_CODELENS CODELENS.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof KM as KM0. open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof CX as CX0. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode] in Hm. subst mode.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  unfold st_rest in SREST. icx_cbn. dand SREST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C140 & _).
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & Mo). unfold RNG in RNG_. icx_cbn. destr_conj RNG_.
  assert (MC : CODELENS = CODELENS -> 257 <= nlen /\ nlen <= 286 /\ 1 <= ndist /\ ndist <= 30 /\ shave <= nlen + ndist /\
            (forall i, 0 <= i < shave -> lf i <= 15) /\
            ctable_live (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  specialize (MC eq_refl). dand MC as (MC1 & MC2 & MC3 & MC4 & MC5 & _). clear Mo.
  zkeysb. unfold L_CODELENS, L_CL_HEAD in *. pose proof two64_eq as TW64.
  zuntil Rfd (idtac;
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (clhead_s (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 Rx lx Mx
              (IST CODELENS last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI) end).
  - unfold s_regs_cl, s_fix, s_vars; gb_split; icx_cbn; zkeys; split_conj; zreg.
  - exact KM0.
  - exact K.
Qed.

End CL.
End S_Codelens.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import SBase. Import S_ClDefs. Import S_Table. Import S_CodelensT. Import S_Codelens.
Import ListNotations.
Open Scope Z_scope.

Theorem arm_TABLE_s {RCa1 : RunCtx}  : itable_spec_s -> ifast_spec_s -> arm_stmt L_TABLE TABLE.
Proof. intros IT IFA. exact (arm_TABLE_s0 IT (clhead_s (cldone_s IT IFA))). Qed.

Theorem arm_LENLENS_s {RCa1 : RunCtx}  : itable_spec_s -> ifast_spec_s -> arm_stmt L_LENLENS LENLENS.
Proof. intros IT IFA. exact (arm_LENLENS_s0 IT (clhead_s (cldone_s IT IFA))). Qed.

Theorem arm_CODELENS_s {RCa1 : RunCtx}  : itable_spec_s -> ifast_spec_s -> arm_stmt L_CODELENS CODELENS.
Proof. intros IT IFA. exact (arm_CODELENS_s0 (cldone_s IT IFA)). Qed.
