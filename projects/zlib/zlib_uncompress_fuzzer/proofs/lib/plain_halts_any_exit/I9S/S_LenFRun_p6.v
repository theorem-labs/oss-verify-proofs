(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SBase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZGo11 SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout S_LenFB_p15.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenFB_p15.

Module S_LenL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import S_MatchL S_DistL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* moved to the layout: 4 labels of this module (each stays as a parse-only notation with its old name) *)
Local Notation L_LLOOP1 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LLOOP1 (only parsing).
Local Notation L_L40 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_L40 (only parsing).
Local Notation L_LLOOP2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LLOOP2 (only parsing).
Local Notation L_L700 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_L700 (only parsing).

(* HINT LEMMAS (new in the run form). Each is an equation `machine form = nicer form`; a run's hint names the
   lemma. The first is the equation that a value replacement of the hand text proved in place; the second is
   the front's shift lemma with every variable bound by its left side; the third is the front's mask lemma
   with its right side in the form the hand text names. *)
Lemma div_pow2_add_comm : forall a k v, a / 2 ^ k + v = v + a / 2 ^ k.
Proof. intros a k v. apply Z.add_comm. Qed.
Lemma srl_hold_u : forall hold k, 0 <= hold < 9223372036854775808 -> 0 <= k <= 63 ->
  Z.shiftr (hold mod 18446744073709551616) (k mod 64) = hold / 2 ^ k.
Proof. intros hold k Hh Hk. apply (srl_hold hold 63 k); [ exact Hh | lia | exact Hk ]. Qed.
Lemma mask_not_sllw_m : forall k, 0 <= k <= 30 ->
  Z.lxor (bv_swrap 32 (Z.shiftl (-1) (k mod 32))) (-1) = 2 ^ k + -1.
Proof. intros k Hk. rewrite mask_not_sllw by exact Hk. reflexivity. Qed.
(* a bound that the third hint's condition reads: stated as a fact before a run *)
Lemma hold_lt_63 : forall h b, 0 <= b <= 63 -> h < 2 ^ b -> h < 9223372036854775808.
Proof.
  intros h b Hb Hh. assert (2 ^ b <= 2 ^ 63) by (apply pow2_le; lia).
  change (2 ^ 63) with 9223372036854775808 in *. lia.
Qed.

(* SPEED ONLY: before the kit's re-attach word after a call, the open facts of the old memory that lie INSIDE a
   range of the callee's footprint (the kit would drop each after a long failing search) are dropped at once,
   by a comparison of the written distances (no solver call). A fact it does not drop goes to the kit's word. *)
Ltac fp_in_lit AA WW FP :=
  lazymatch FP with
  | (?RA, ?RN) :: ?REST =>
      first [ lazymatch zbase_off AA with
              | (?B1, ?O1) =>
                  lazymatch zbase_off RA with
                  | (?B2, ?O2) =>
                      constr_eq B1 B2;
                      let INS := eval cbv in (andb (Z.leb O2 O1) (Z.leb (O1 + WW) (O2 + RN))) in
                      lazymatch INS with true => idtac end
                  end
              end
            | fp_in_lit AA WW REST ]
  end.
Ltac drop_in_fp HPX :=
  lazymatch type of HPX with
  | mpostL _ ?MO _ ?FP =>
      repeat match goal with
      | HF : mem_u64 _ MO ?AA _ |- _ => fp_in_lit AA 8 FP; clear HF
      | HF : mem_u32 _ MO ?AA _ |- _ => fp_in_lit AA 4 FP; clear HF
      end
  end.

(* the state's relation is closed again from its open facts after a run that wrote a field: a field's fact is
   taken as it stands, or with its value brought to the wanted form by the kit's arithmetic *)
Ltac st_reclose :=
  unfold st_rest; icx_cbn; split_conj;
  first [ assumption
        | lazymatch goal with |- mem_u32 ?sg ?mm ?aa ?e2 =>
            match goal with HX : mem_u32 sg mm aa ?e1 |- _ => replace e2 with e1 by lia; exact HX end end
        | lazymatch goal with |- mem_u64 ?sg ?mm ?aa ?e2 =>
            match goal with HX : mem_u64 sg mm aa ?e1 |- _ => replace e2 with e1 by lia; exact HX end end ].

(* THE LIST FORM's OPENERS AND CLOSERS OF THIS HALF (they unfold, split and name; no value of an image stands in
   them: the lists stand in the layout). `rh_open` opens "each register of the layout's list holds its value" in
   a hypothesis; `rh_close` proves it for the state of the goal; `rk_open` / `rk_close` do the same for "each
   register of the layout's keep list holds what it held at the start"; `rk_chain` carries a keep fact of a
   later start state back to the first one. *)
Ltac lenb_lists_cbv_in HH :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval
       fst snd nth
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l1_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l1_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l2_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l2_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenb_e1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenb_e2
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_e OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_j28 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_kx1
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_j40 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_j700
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l778 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_lx34 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_j60
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_jra] in HH;
  cbn [c_u c_p c_q c_n c_ob c_osz c_w c_K c_cin0
       t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in HH;
  cbv [JTAB_ADDR] in HH.
Ltac lenb_lists_cbv :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval
       fst snd nth
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l1_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l1_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l2_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l2_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenb_e1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenb_e2
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_e OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_j28 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_kx1
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_j40 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_j700
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l778 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_lx34 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_j60
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_jra];
  cbn [c_u c_p c_q c_n c_ob c_osz c_w c_K c_cin0
       t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext];
  cbv [JTAB_ADDR].
Ltac lenb_keys_cbv_in HH :=
  cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
       kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in HH.
Ltac lenb_keys_cbv :=
  cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
       kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6].
Ltac rh_open HH := lenb_lists_cbv_in HH; lenb_keys_cbv_in HH; destr_conj HH.
Ltac rh_close := lenb_lists_cbv; split_conj; zreg.
Ltac rk_open HH := lenb_lists_cbv_in HH; lenb_keys_cbv_in HH; destr_conj HH.
Ltac rk_close := lenb_lists_cbv; split_conj; zreg.
Ltac rk_chain HK :=
  lenb_lists_cbv_in HK; lenb_keys_cbv_in HK; lenb_lists_cbv; lenb_keys_cbv; destr_conj HK; split_conj;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].

(* THE LIST FORM of the hand statement: the registers of the head and of the two continuations stand in the
   layout's lists; the statement binds their values in order (the head's list: the table's base; the root mask;
   the input left; the next input address; the bit count; the hold; the root entry's bit count; the root
   entry's address; the input left, the bit count and the next input address at the arm's entry) *)
Lemma l_loop1 {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n la na lb lm c0 b0 ci B H : Z) (fin rdL : Z -> Z),
  m_halted MD = None ->
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs [la; lm; n - ci; q + ci; B; H; code_bits (rdL (Z.land lm H)); la + 4 * Z.land lm H; n - c0; b0; q + c0])
    Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l1 ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < code_bits (rdL (Z.land lm H)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 2 ^ lb <= na -> tab_ok LENS rdL lb na = true ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 <= la -> la + 4 * na <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M la na rdL ->
  (forall R' (H' : Z),
     OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs [H']) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l1_lv ->
     0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenb_e1 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L1 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs [q + ci'; n - ci'; B'; H'; code_bits (rdL (Z.land lm H')); la + 4 * Z.land lm H'])
       R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l1_dn ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> B' <= 22 -> code_bits (rdL (Z.land lm H')) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenb_e1 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_L40 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LLOOP1 (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n la na lb lm c0 b0 ci B H fin rdL Hh HRG
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hdm Hdb1 Hdb2 Hnd TOK Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  rh_open HRG.
  zkeys. unfold L_LLOOP1, L_L40, L_LVX_L1 in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPdb.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (tab_root_entry LENS rdL lb na (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as (Hbits0 & _ & _ & _).
  assert (HB14 : B <= 14) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { (* no input left: ONE RUN to the leave's continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end).
    all: try rh_close. all: try lia.
    replace (b0 + 8 * (n - c0)) with B by lia. lia. }
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  (* the hold after the pulled byte, in the form the run leaves it; its facts stand before the run *)
  assert (HH' : 0 <= fin ci * 2 ^ B + H < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia).
  pose proof (land_mask_l (fin ci * 2 ^ B + H) lb ltac:(lia)) as Ri1. rewrite <- Hdm in Ri1.
  pose proof (tab_root_entry LENS rdL lb na (Z.land lm (fin ci * 2 ^ B + H)) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as (Hbits1 & _ & _ & _).
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  (* ONE RUN through the loop's body to its exit test, with TWO VALUE HINTS (the pulled byte, shifted; the
     table index, scaled) *)
  zto_branch_hq Rfd (first [ zhint shl_byte | zhint shiftl_2 ]).
  destruct (Z_lt_dec (B + 8) (code_bits (rdL (Z.land lm (fin ci * 2 ^ B + H))))) as [Hmore | Hdone].
  - (* THE BACK EDGE: ONE RUN back to the loop's head, where the induction hypothesis applies *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n la na lb lm c0 b0 (ci + 1) (B + 8) (fin ci * 2 ^ B + H) fin rdL Hh) end).
    all: try rh_close. all: try lia. all: try eassumption.
    intros R' ci' B' H'' HR2 X1 X2 X3 X4 X5 X6 X7 X8 HK.
    eapply (KD R' ci' B' H''); try assumption; try lia. all: rk_chain HK.
  - (* enough bits: ONE RUN to the body's continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) (fin ci * 2 ^ B + H)) end).
    all: try rh_close. all: try lia.
Qed.


(* THE LIST FORM of the hand statement (the head's list: the second-level mask; the root bits; the sub-table's
   first index; the table's base; the input left, the bit count and the next input address at the root entry;
   the input left; the next input address; the bit count; the hold; the second-level entry's address; the
   second-level entry's bit count) *)
Lemma l_loop2 {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n la na lb lo v m2 c1 b1 ci B H : Z) (fin rdL : Z -> Z),
  m_halted MD = None ->
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs [m2; lb; v; la; n - c1; b1; q + c1; n - ci; q + ci; B; H;
                                                     la + 4 * (v + Z.land H m2 / 2 ^ lb); code_bits (rdL (v + Z.land H m2 / 2 ^ lb))])
    Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l2 ->
  n - ci < Z.of_nat N -> 0 <= c1 -> c1 <= ci -> ci <= n -> 0 <= b1 -> B = b1 + 8 * (ci - c1) ->
  B < lb + code_bits (rdL (v + Z.land H m2 / 2 ^ lb)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  m2 = 2 ^ (lb + lo) - 1 -> 1 <= lb -> lb <= 15 -> 1 <= lo -> lo <= 15 - lb -> 0 <= v -> v + 2 ^ lo <= na -> na <= 65536 ->
  (forall j, 0 <= j < 2 ^ lo -> is_linkop (code_op (rdL (v + j))) = false /\ term_ok LENS (15 - lb) (rdL (v + j)) = true) ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 <= la -> la + 4 * na <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M la na rdL ->
  (forall R' (H' : Z),
     OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs [H']) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l2_lv ->
     0 <= H' -> H' < 2 ^ (b1 + 8 * (n - c1)) -> b1 + 8 * (n - c1) <= 29 -> b1 + 8 * (n - c1) <= 8 * n ->
     OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenb_e2 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L2 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs [q + ci'; n - ci'; B'; H';
                                                        la + 4 * (v + Z.land H' m2 / 2 ^ lb); code_bits (rdL (v + Z.land H' m2 / 2 ^ lb))])
       R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l2_dn ->
     ci < ci' -> ci' <= n -> B' = b1 + 8 * (ci' - c1) -> B' <= 37 -> lb + code_bits (rdL (v + Z.land H' m2 / 2 ^ lb)) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenb_e2 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_L700 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LLOOP2 (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n la na lb lo v m2 c1 b1 ci B H fin rdL Hh HRG
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hm2 Hdb1 Hdb2 Hlo1 Hlo2 Hv1 Hv2 Hnd SUB
    Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  rh_open HRG.
  zkeys. unfold L_LLOOP2, L_L700, L_LVX_L2 in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPdb. pose proof (pow2_15 lo ltac:(lia)) as HPlo.
  assert (HPm : 1 <= 2 ^ (lb + lo) <= 32768) by (apply pow2_15; lia).
  assert (JR : forall Hx, 0 <= Z.land Hx m2 / 2 ^ lb < 2 ^ lo).
  { intros Hx. pose proof (land_mask_r Hx (lb + lo) ltac:(lia)) as A. rewrite <- Hm2 in A.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
  pose proof (JR H) as Rj0.
  destruct (SUB _ Rj0) as [_ TM0]. apply term_ok_LENS in TM0 as [Hbits0 _].
  assert (HB29 : B <= 29) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { (* no input left: ONE RUN to the leave's continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end).
    all: try rh_close. all: try lia.
    replace (b1 + 8 * (n - c1)) with B by lia. lia. }
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  (* the hold after the pulled byte, in the form the run leaves it; its facts stand before the run *)
  assert (HH' : 0 <= fin ci * 2 ^ B + H < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia).
  pose proof (land_mask_r (fin ci * 2 ^ B + H) (lb + lo) ltac:(lia)) as Rm. rewrite <- Hm2 in Rm.
  pose proof (JR (fin ci * 2 ^ B + H)) as Rj1.
  destruct (SUB _ Rj1) as [_ TM1]. apply term_ok_LENS in TM1 as [Hbits1 _].
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  (* ONE RUN through the loop's body to its exit test, with FOUR VALUE HINTS (the pulled byte, shifted; the
     second-level index; the index with its base; the index, scaled) *)
  zto_branch_hq Rfd (first [ zhint shl_byte | zhint srlw_small | zhint div_pow2_add_comm | zhint zext32_shift30 ]).
  destruct (Z_lt_dec (B + 8) (lb + code_bits (rdL (v + Z.land (fin ci * 2 ^ B + H) m2 / 2 ^ lb)))) as [Hmore | Hdone].
  - (* THE BACK EDGE: ONE RUN back to the loop's head, where the induction hypothesis applies *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n la na lb lo v m2 c1 b1 (ci + 1) (B + 8) (fin ci * 2 ^ B + H) fin rdL Hh) end).
    all: try rh_close. all: try lia. all: try eassumption.
    intros R' ci' B' H'' HR2 X1 X2 X3 X4 X5 X6 X7 X8 HK.
    eapply (KD R' ci' B' H''); try assumption; try lia. all: rk_chain HK.
  - (* enough bits: ONE RUN to the body's continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) (fin ci * 2 ^ B + H)) end).
    all: try rh_close. all: try lia.
Qed.


Definition st_le (st : ist) (m len ex : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      len (t_offset st) ex (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_len_set : forall cx st lf cf m len,
  sinv cx st lf cf -> t_mode st = LEN -> (m = LEN \/ m = LIT \/ m = TYPE) -> 0 <= len -> len < 4294967296 ->
  sinv cx (st_le st m len (t_extra st)) lf cf.
Proof.
  intros cx st lf cf m len SI Hm Hm' Hl1 Hl2.
  dand SI as (RN0 & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN = HEAD \/ LEN = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in RN0. icx_cbn. destr_conj RN0.
  split; [| split; [exact W | split; [prog_transfer P|]]].
  - clear W P Mf Mlive. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear - Hm'; unfold reach; destruct Hm' as [-> | [-> | ->]]; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | destruct Hm' as [-> | [-> | ->]]; mode_vacuous ].
Qed.

Lemma sinv_to_lenext : forall cx st lf cf len ex,
  sinv cx st lf cf -> t_mode st = LEN -> 1 <= len -> len <= 32768 -> 0 <= ex -> ex <= 15 ->
  sinv cx (st_le st LENEXT len ex) lf cf /\ meas cx (st_le st LENEXT len ex) < meas cx st.
Proof.
  intros cx st lf cf len ex SI Hm Hl1 Hl2 He1 He2.
  dand SI as (RN0 & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN = HEAD \/ LEN = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in RN0. icx_cbn. destr_conj RN0.
  split; [split; [| split; [exact W | split; [prog_transfer P|]]] |].
  - clear W P Mf Mlive. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | intros _; clear - Hl1 Hl2 He1 He2; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_to_dist : forall cx st lf cf len,
  sinv cx st lf cf -> t_mode st = LENEXT -> 1 <= len -> len < 65536 ->
  sinv cx (st_le st DIST len (t_extra st)) lf cf /\ meas cx (st_le st DIST len (t_extra st)) < meas cx st.
Proof.
  intros cx st lf cf len SI Hm Hl1 Hl2.
  dand SI as (RN0 & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LENEXT = HEAD \/ LENEXT = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LENEXT -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LENEXT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in RN0. icx_cbn. destr_conj RN0.
  split; [split; [| split; [exact W | split; [prog_transfer P|]]] |].
  - clear W P Mf Mlive. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | intros _; clear - Hl1 Hl2; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma st_rest_le {RCa1 : RunCtx}  : forall cx st M m len ex,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st len (t_offset st) ex) M -> st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_le st m len ex) M.
Proof. intros cx st M m len ex H. destruct cx, st. exact H. Qed.
End S_LenL.

Module S_LenX.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import S_MatchL S_Match S_DistL S_DistX S_Dist S_LenL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* moved to the layout: 3 labels of this module (each stays as a parse-only notation with its old name) *)
Local Notation L_LX34 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LX34 (only parsing).
Local Notation L_L770 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_L770 (only parsing).
Local Notation L_L778 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_L778 (only parsing).

Ltac kcbv_in H := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in H.
Ltac jfin :=
  lazymatch goal with
  | |- zget _ _ = _ => zreg
  | |- zget_l _ _ _ = _ => zreg
  | |- OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ => rh_close
  | |- x_regs _ _ _ _ _ _ _ _ _ _ _ _ => close_xregs
  | |- keptc _ _ _ _ => keptc_close
  | |- realizes _ _ _ => idtac
  | |- forall _, _ => try assumption
  | |- _ \/ _ => assumption
  | |- mem_arr _ _ _ _ _ _ => assumption
  | |- tab_ok _ _ _ _ = true => assumption
  | |- m_halted _ = _ => assumption
  | |- _ => first [assumption | lia]
  end.
Ltac st_cbn_in H := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in H.

(* THE LIST FORM of the hand statement: its two register facts beside the dispatch map stand in a list of the
   layout (bound value: the length) *)
Theorem len_to_dist {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf (m len : Z),
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENEXT -> sinv cx st lf cf -> 1 <= len -> len < 65536 ->
  s_regs_d10 cx st Rb l ->
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv cx (Some st) [len]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_l778 ->
  s_std cx fin M -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 8) m -> st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st len (t_offset st) (t_extra st)) M ->
  s_ret cx st M -> s_out cx st M -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_L778 (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf m len CX Hh Hfin Hmd SI Hl1 Hl2 RG HRX STD Hm SREST SRET SOUT Hlens Hcodes HP0 K.
  rh_open HRX.
  pose proof (sinv_to_dist cx st lf cf len SI Hmd Hl1 Hl2) as [SI1 ME1].
  pose proof (st_rest_le cx st M DIST len (t_extra st) SREST) as SR1. clear SREST.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode. unfold st_le in SI1, ME1, SR1. st_cbn_in SI1. st_cbn_in ME1. st_cbn_in SR1.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_std STD. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  zkeysb. unfold L_L778, L_DIST in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  (* ONE RUN to the next arm's entry *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (dist_s _ fin MD T M0 Rx lx Mx
              (IST DIST last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI1) end).
  - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [DIST]; assumption | exact SR1 | exact SRET | exact SOUT | exact I | exact HAG].
  - eapply KALL_mono; [| exact K]. clear - ME1. lia.
Qed.

Theorem len_70 {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENEXT -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l ->
  s_std cx fin M -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 8) LENEXT -> st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M ->
  s_ret cx st M -> s_out cx st M -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_L770 (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG STD Hm SREST SRET SOUT Hlens Hcodes HP0 K.
  assert (HLE : t_extra st <= 15 /\ 1 <= t_length st /\ t_length st <= 32768).
  { dand SI as (_ & _ & _ & Mo). clear - Mo Hmd. unfold MODE in Mo.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    match goal with H : t_mode st = LENEXT -> _ |- _ => exact (H Hmd) end. }
  dand HLE as (HX15 & HL1 & HL32).
  pose proof CX as CX0. pose proof RG as RG0. pose proof STD as STD0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_std STD. icx_cbn.
  zkeysb. unfold L_L770, L_L778 in *. cbv [JTAB_ADDR] in *.
  pose proof SREST as C92. unfold st_rest in C92. icx_cbn. dand C92 as (_ & _ & _ & _ & C92 & _).
  (* the frame's slots are opened ALL *)
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn. destr_conj FR.
  pose proof (proj1 SI) as RN0. unfold RNG in RN0. icx_cbn. dand RN0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [RL1 RL2] & _).
  (* ONE RUN to the join point of the two ways into the next arm *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (len_to_dist _ fin MD T M0 Rx lx Mx
              (IST LENEXT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf LENEXT length CX0 Hh Hfin eq_refl SI) end).
  - lia.
  - lia.
  - split; [| split]; [unfold s_fix | unfold s_vars | ]; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - rh_close.
  - exact STD0.
  - exact Hm.
  - unfold st_w3; icx_cbn. exact SREST.
  - exact SRET.
  - first [ exact SOUT | exact I ].
  - exact Hlens.
  - exact Hcodes.
  - exact HP0.
  - exact K.
Qed.

(* THE LIST FORM of the hand statement: its one register fact beside the dispatch map stands in a list of the
   layout (bound value: the count of extra bits) *)
Theorem lenext_s {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENEXT -> sinv cx st lf cf -> t_extra st <> 0 ->
  s_regs_d10 cx st Rb l ->
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv cx (Some st) [t_extra st]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_lx34 ->
  s_std cx fin M -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 8) LENEXT -> st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M ->
  s_ret cx st M -> s_out cx st M -> mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LX34 (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI Hx1 RG HRX STD Hm SREST SRET SOUT Hlens Hcodes HP0 K.
  rh_open HRX.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  assert (HLE : extra <= 15 /\ 1 <= length /\ length <= 32768)
    by (clear - MODE_; unfold MODE in MODE_; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
        match goal with H : LENEXT = LENEXT -> _ |- _ => exact (H eq_refl) end).
  dand HLE as (HX15 & HL1 & HL32). clear MODE_.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_std STD. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  prune_rng.
  zkeysb. unfold L_LX34, L_L778, L_LXLOOP, L_LX60, L_LVX_EXT in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KD10 KD00 KSM KRA1 KRL KB11 KB10 KBA3 KLL KRT.
  (* the frame's slots are opened ALL *)
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn. destr_conj FR.
  destruct (mem_wr_u32_exists_R M (p + 7164) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (vb & Hback & Rvb).
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  (* THE JOIN AFTER THE EXTRA BITS ARE IN HAND: the front's register map of the extra-bits module, and the
     join's own five registers as a list of the layout (bound values: the next input address; the input left;
     the bit count; the hold; the count of extra bits) *)
  assert (J60 : forall R' (ci H B : Z),
    x_regs u p q n ob osz K0 cin cout bits out R' ->
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs [q + ci; n - ci; B; H; extra]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_j60 ->
    cin <= ci -> ci <= n -> extra <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci -> B = bits + 8 * (ci - cin) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LX60 (zupd R' []) M MD) T).
  { intros R' ci H B XR HRJ Hc1 Hc2 HxB HB40 HH1 HH2 HBc HB.
    unfold L_LX60. open_xregs XR. rh_open HRJ. zgetl_nil. clear KL.
    repeat match goal with H : forall i : Z, _ |- _ => lazymatch H with Hfin => fail | _ => clear H end end.
    pose proof (pow2_15 extra ltac:(lia)) as HPx.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    pose proof (land_mask_r H extra ltac:(lia)) as Rbx.
    pose proof (hold_shr_bound H B extra ltac:(lia) ltac:(lia)) as HH'.
    pose proof (hold_lt_63 H B ltac:(lia) HH2) as HH63.
    pose proof (sinv_pull _ _ lf cf ci (H / 2 ^ extra) (B - extra) SI0 ltac:(cbn; lia) ltac:(cbn; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 ME1].
    unfold st_pull in SI1, ME1. st_cbn_in SI1. st_cbn_in ME1.
    (* the state's facts are opened before the run (the run writes one of them) *)
    unfold st_rest in SREST. icx_cbn.
    dand SREST as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
    (* ONE RUN to the join point of the two ways into the next arm, with TWO VALUE HINTS (the mask of the extra
       bits; the hold shifted down) *)
    zuntil_h Rfd (first [ zhint mask_not_sllw | zhint srl_hold_u ])
      (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (len_to_dist _ fin MD T M0 Rx lx Mx
                  (IST LENEXT last flags ci cout (H / 2 ^ extra) (B - extra) out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  lf cf LENEXT (length + Z.land H (2 ^ extra - 1)) CX0 Hh Hfin eq_refl SI1) end).
    - lia.
    - lia.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - rh_close.
    - close_std.
    - icx_cbn. exact Hm.
    - unfold st_w3; icx_cbn. st_reclose.
    - exact SRET.
    - first [ exact SOUT | exact I ].
    - exact Hlens.
    - exact Hcodes.
    - exact HAG.
    - eapply KALL_mono; [| exact K]. clear - ME1. lia. }
  destruct (Z_lt_dec bits extra) as [Hneed | Hhave].
  - (* not enough bits: ONE RUN to the loop that pulls input *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (x_loop (S (Z.to_nat (n - cin))) L_LXLOOP L_LX60 Rx lx Mx MD T q n extra cin bits cin bits hold fin) end).
    1: left; split; reflexivity.
    all: try (split_lists3; zreg).
    all: jfin.
    + intros R' H' HL HH1 HH2 HB14 HBn KP. keptc_open KP. open_lists3. zgetl_nil. zimps.
      eapply (stub_L1 L_LVX_EXT R' [] M MD T q n cin bits u ret); [right; reflexivity | exact Hh | split_lists3; zreg | lia | lia | exact SRET |].
      intros R9 RH9 KP9. keptc_open KP9. open_lists3. zgetl_nil. zimps.
      pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
      unfold st_pull in SI1. st_cbn_in SI1.
      unfold KLEAVE, L_LEAVE in KL.
      eapply (KL R9 M _ ret lf cf SI1).
      * unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
      * close_std.
      * split; [exact Hm | exact SREST].
      * first [ exact SOUT | exact I ].
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    + intros R' ci' B' H' HL X1 X2 X3 X4 X5 X6 X7 X8 KP. keptc_open KP. open_lists3. zgetl_nil. zimps.
      eapply (J60 R' ci' H' B'). all: jfin.
  - (* enough bits: ONE RUN to the join point *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J60 Rx cin hold bits) end). all: jfin.
Qed.

Theorem arm_LENEXT {RCa1 : RunCtx}  : arm_stmt L_LENEXT LENEXT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof SREST as SR0. unfold st_rest in SR0. dand SR0 as (_ & _ & _ & _ & _ & _ & C100 & _).
  dand RG as (FIX & VARS & G27). pose proof FIX as FIX0. unfold s_fix in FIX. destr_conj FIX.
  pose proof SI as SI'. dand SI' as (R & _ & _ & Mo).
  assert (HX : t_extra st <= 15 /\ 1 <= t_length st /\ t_length st <= 32768).
  { clear - Mo Hmd. unfold MODE in Mo. repeat match goal with H : _ /\ _ |- _ => destruct H end.
    match goal with H : t_mode st = LENEXT -> _ |- _ => exact (H Hmd) end. }
  assert (HX0 : 0 <= t_extra st) by (unfold RNG in R; destr_conj R; assumption). clear R Mo.
  zkeysb. unfold L_LENEXT, L_LX34, L_L770 in *.
  (* ONE RUN to the test of the extra bits' count *)
  zto_branch_q Rfd.
  destruct (Z.eq_dec (t_extra st) 0) as [Hx0 | Hx1].
  - (* no extra bits: ONE RUN to the short way *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (len_70 cx fin MD T M0 Rx lx M st lf cf CX Hh Hfin Hmd SI) end).
    + split; [exact FIX0 | split; [exact VARS | zreg]].
    + exact STD.
    + rewrite <- Hmd. exact Hmode.
    + exact SREST.
    + exact SRET.
    + first [ exact SOUT | exact I ].
    + exact Hlens.
    + exact Hcodes.
    + exact HP0.
    + exact K.
  - (* extra bits: ONE RUN to the way that pulls them *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (lenext_s cx fin MD T M0 Rx lx M st lf cf CX Hh Hfin Hmd SI Hx1) end).
    + split; [exact FIX0 | split; [exact VARS | zreg]].
    + rh_close.
    + exact STD.
    + rewrite <- Hmd. exact Hmode.
    + exact SREST.
    + exact SRET.
    + first [ exact SOUT | exact I ].
    + exact Hlens.
    + exact Hcodes.
    + exact HP0.
    + exact K.
Qed.
End S_LenX.

Module S_Len.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import S_MatchL S_Match S_DistL S_DistX S_Dist S_LenL S_LenX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* moved to the layout: 2 labels of this module, the first back module's four and two of the second's: each
   stays as a parse-only notation with its old name *)
Local Notation L_L770 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_L770 (only parsing).
Local Notation L_LX34 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LX34 (only parsing).
Local Notation L_LSLOW := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LSLOW (only parsing).
Local Notation L_L28 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_L28 (only parsing).
Local Notation L_LLOOP1 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LLOOP1 (only parsing).
Local Notation L_L40 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_L40 (only parsing).
Local Notation L_LLOOP2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LLOOP2 (only parsing).
Local Notation L_L700 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_L700 (only parsing).

(* moved to the layout: the hand text's register-map definition of this module is a list of the layout, read
   with the context record and the model state; its opener and closer are the list form's (`rh_open`,
   `rh_close`) *)
Ltac jfin ::=
  lazymatch goal with
  | |- zget _ _ = _ => zreg
  | |- zget_l _ _ _ = _ => zreg
  | |- OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ => rh_close
  | |- keptc _ _ _ _ => keptc_close
  | |- realizes _ _ _ => idtac
  | |- forall _, _ => try assumption
  | |- _ \/ _ => assumption
  | |- mem_arr _ _ _ _ _ _ => assumption
  | |- tab_ok _ _ _ _ = true => assumption
  | |- m_halted _ = _ => assumption
  | |- s_std _ _ _ => close_std
  | |- st_rest _ _ _ _ => assumption
  | |- s_ret _ _ _ => assumption
  | |- s_out _ _ _ => first [ assumption | exact I ]
  | |- framed _ _ => assumption
  | |- mem_u32 _ _ _ _ => assumption
  | |- mem_u64 _ _ _ _ => assumption
  | |- mem_wr _ _ _ _ => assumption
  | |- _ => first [assumption | lia]
  end.
Ltac mode_getr Mo := clear - Mo; unfold MODE in Mo; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
  first [ assumption | match goal with H : ?x = ?x -> _ |- _ => exact (H eq_refl) end ].
Lemma land_mask_l' : forall x k, 0 <= k -> 0 <= Z.land (2 ^ k + -1) x < 2 ^ k.
Proof. intros x k Hk. replace (2 ^ k + -1) with (2 ^ k - 1) by lia. apply land_mask_l. exact Hk. Qed.

Theorem len_slow_s {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LEN -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LSLOW (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  pose proof KM as KM0. open_kmem KM. open_std STD.
  assert (TLV : tables_live cx st cf).
  { assert (ML : codes_liveP (t_mode st) -> tables_live cx st cf) by mode_get MODE_.
    apply ML. rewrite Hmd. unfold codes_liveP. cbv [LEN_ LEN LIT]. lia. }
  dand (live_tabs cx st lf cf M CX RNG_ TLV ROM Hcodes) as (na & nd & TB). clear TLV MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold tabsP in TB. icx_cbn. idtac.
  dand TB as (HtL & HtD & TOKL & TOKD & Cla1 & Cla2 & Cda1 & Cda2 & Cna & Cnd & ALla & ALda & Slaob & Slap & Sdaob & Sdap & Slap2 & Sdap2 & _).
  clear HtD TOKD Cda1 Cda2 Cnd ALda Sdaob Sdap Sdap2.
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) lc) as la eqn:Ela.
  remember (rdc cf lc) as rdL eqn:ErdL. clear ErdL.
  prune_rng.
  zkeysb. unfold L_LSLOW, L_L28, L_LLOOP1, L_L40, L_LLOOP2, L_L700, L_LVX_L1, L_LVX_L2, L_L770, L_LX34 in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD10 KD00 KSM KRA1 KRL KB11 KB10 KRT.
  (* the frame's slots are opened ALL *)
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn. destr_conj FR.
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  pose proof (tab_ok_root _ _ _ _ TOKL) as (Hlb1 & Hna1 & _).
  pose proof (pow2_15 lb ltac:(lia)) as HPlb.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn. dand SR0 as (_ & _ & _ & _ & _ & _ & _ & C104 & _ & C120 & _).
  rewrite <- Ela in C104. clear Ela.
  (* THE JOIN AFTER A TABLE ENTRY IS READ, in the list form: the module's register map and the join's own list
     (bound values: the entry's operation field, value field and bit count; the bits already taken; the bit
     count; the hold; the next input address; the input left) *)
  assert (J28 : forall R' M' (ci B Hd e lbv : Z),
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
      (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (Some (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) [])
      R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_e ->
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
      (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (Some (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext))
         [code_op e; code_val e; code_bits e; lbv; B; Hd; q + ci; n - ci])
      R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_j28 ->
    1 <= code_bits e ->
    ((code_op e = 0 /\ code_val e < 256)
     \/ (16 <= code_op e < 32 /\ 3 <= code_val e /\ code_val e + Z.shiftl 1 (code_op e - 16) - 1 <= 258 /\ code_op e <= 21)
     \/ (Z.land (code_op e) 64 <> 0 /\ Z.land (code_op e) 16 = 0)) ->
    0 <= lbv -> lbv <= 15 ->
    cin <= ci -> ci <= n -> code_bits e <= B -> B <= 40 -> 0 <= Hd -> Hd < 2 ^ B -> B <= 8 * ci ->
    8 * (n - ci) + B <= 8 * (n - cin) + bits ->
    s_std (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 8) LEN ->
    st_rest (run_segments R_segs rc_inp rc_sp rc_mb) (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_ret (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_out (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
    mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p 7176 ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X [(u - 1024, 1024); (u, 112); (p, 7176); (ob, osz)]) M' ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_L28 (zupd R' []) M' MD) T).
  { intros R' M' ci B Hd e lbv ER HRJ Hbe CLS Hlv1 Hlv2 Hc1 Hc2 HbB HB40 HH1 HH2 HBc HWm
           STD' Hm' SR' RET' OUT' HL' HC' Wp' HAG'.
    cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_L28]. rh_open ER. rh_open HRJ. zgetl_nil.
    clear KL KLL. clear Slaob Slap Slap2.
    repeat match goal with Hd : forall i : Z, _ |- _ => lazymatch Hd with Hfin => fail | _ => clear Hd end end.
    repeat match goal with Hd : context [M] |- _ => clear Hd end.
    rename STD' into STD. rename Hm' into Hmode. rename SR' into SREST. rename RET' into SRET. rename OUT' into SOUT.
    rename HL' into Hlens. rename HC' into Hcodes. rename HAG' into HAG.
    pose proof STD as STD2. open_std STD2. icx_cbn. zkeys.
    pose proof (code_op_range e) as Rop. pose proof (code_val_range e) as Rval. pose proof (code_bits_range e) as Rbi.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    pose proof (hold_shr_bound Hd B (code_bits e) ltac:(lia) ltac:(lia)) as HH'.
    pose proof (hold_lt_63 Hd B ltac:(lia) HH2) as HH63.
    pose proof (sinv_pull _ _ lf cf ci (Hd / 2 ^ code_bits e) (B - code_bits e) SI0 ltac:(cbn; lia) ltac:(cbn; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 ME1].
    unfold st_pull in SI1, ME1. st_cbn_in SI1. st_cbn_in ME1.
    unfold KDISP, L_DISP in KD. unfold KBADMSG_A3, L_BADMSG_A3 in KBA3. zkeys.
    (* the state's facts are opened before the runs (the runs write some of them) *)
    unfold st_rest in SREST. icx_cbn.
    dand SREST as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
    (* ONE RUN to the test of the entry's kind, with ONE VALUE HINT (the hold shifted down) *)
    zto_branch_hq Rfd (first [ zhint srl_hold_u ]).
    destruct CLS as [[Hop0 Hv256] | [(Hop16 & Hv3 & Hv258 & Hop21) | [H64 H16]]].
    - (* a literal: ONE RUN to the dispatch *)
      pose proof (sinv_len_set _ _ lf cf LIT (code_val e) SI1 eq_refl ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
      unfold st_le in SI2. st_cbn_in SI2.
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KD Rx Mx (IST LIT last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                             lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI2) end).
      + clear - ME1. unfold meas, Wm in *. icx_cbn. change (rank LIT) with 13 in *. change (rank LEN) with 18 in *. lia.
      + unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
      + unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
        all: first [cbv [LIT]; assumption | exact SRET | exact SOUT | exact I | exact HAG | st_reclose].
    - (* a length base: ONE RUN to the test of its extra bits' count *)
      pose proof (op_base_tests (code_op e) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
      rewrite shiftl_1_pow in Hv258 by lia. pose proof (pow2_15 (code_op e - 16) ltac:(lia)) as HPx.
      pose proof (sinv_to_lenext _ _ lf cf (code_val e) (code_op e - 16) SI1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI2 ME2].
      unfold st_le in SI2, ME2. st_cbn_in SI2. st_cbn_in ME2.
      zto_branch_q Rfd.
      destruct (Z.eq_dec (code_op e - 16) 0) as [Hx0 | Hx1].
      + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (len_70 _ fin MD T M0 Rx lx Mx
                    (IST LENEXT last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset (code_op e - 16)
                         lc dc lb db ncode nlen ndist shave nx whave wnext)
                    lf cf CX0 Hh Hfin eq_refl SI2) end).
        * unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
        * close_std.
        * icx_cbn. cbv [LENEXT]. assumption.
        * icx_cbn. st_reclose.
        * exact SRET.
        * first [ exact SOUT | exact I ].
        * exact Hlens.
        * exact Hcodes.
        * exact HAG.
        * eapply KALL_mono; [| exact K]. clear - ME1 ME2. lia.
      + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (lenext_s _ fin MD T M0 Rx lx Mx
                    (IST LENEXT last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset (code_op e - 16)
                         lc dc lb db ncode nlen ndist shave nx whave wnext)
                    lf cf CX0 Hh Hfin eq_refl SI2) end).
        * icx_cbn. exact Hx1.
        * unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
        * rh_close.
        * close_std.
        * icx_cbn. cbv [LENEXT]. assumption.
        * icx_cbn. st_reclose.
        * exact SRET.
        * first [ exact SOUT | exact I ].
        * exact Hlens.
        * exact Hcodes.
        * exact HAG.
        * eapply KALL_mono; [| exact K]. clear - ME1 ME2. lia.
    - (* the block's end or a code that is not valid: ONE RUN to the test that tells them *)
      assert (Tnz : code_op e <> 0) by (intros E; rewrite E in H64; apply H64; reflexivity).
      pose proof (land_range_r (code_op e) 64 ltac:(lia)) as R64. pose proof (land_range_r (code_op e) 32 ltac:(lia)) as R32.
      pose proof (sinv_len_set _ _ lf cf LEN (code_val e) SI1 eq_refl ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
      unfold st_le in SI2. st_cbn_in SI2.
      zto_branch_q Rfd.
      destruct (Z.eq_dec (Z.land (code_op e) 32) 0) as [H32 | H32].
      + (* not valid: ONE RUN to the error place *)
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
          eapply (KBA3 Rx Mx (IST LEN last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                                lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf) end).
        (* the premises in their order: the invariant; the measure; the fixed map; the place's own register
           facts (their count is the layout's: each is closed by the register word); the message address's
           range; the memory relation *)
        1: (apply sinv_bad_of; exact SI2).
        1: (pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                        (IST LEN last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                             lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB;
            cbn [t_mode] in MB; change (rank LEN) with 18 in MB; clear - MB ME1; unfold meas, Wm in *; icx_cbn; lia).
        1: (unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg).
        all: try zreg.
        all: try (lazymatch goal with |- 0 <= ?x < _ => replace x with OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.A_lenb_badmsg by (symmetry; zreg) end;
                  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.A_lenb_badmsg]; rewrite TW64; lia).
        unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
        all: first [exact SRET | exact SOUT | exact I | exact HAG | st_reclose].
      + (* the block's end: ONE RUN to the dispatch *)
        pose proof (sinv_len_set _ _ lf cf TYPE (code_val e) SI1 eq_refl ltac:(right; right; reflexivity) ltac:(lia) ltac:(lia)) as SI3.
        unfold st_le in SI3. st_cbn_in SI3.
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
          eapply (KD Rx Mx (IST TYPE last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                               lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI3) end).
        * clear - HWm Hbe. unfold meas, Wm. icx_cbn. change (rank TYPE) with 24. change (rank LEN) with 18. lia.
        * unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
        * unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
          all: first [cbv [TYPE]; assumption | exact SRET | exact SOUT | exact I | exact HAG | st_reclose]. }
  (* the root entry's facts stand before the run *)
  pose proof (land_mask_l' hold lb ltac:(lia)) as Ri0.
  pose proof (tab_root_entry LENS rdL lb na (Z.land (2 ^ lb + -1) hold) TOKL Ri0) as (Hbits0 & _ & _ & _).
  (* ONE RUN from the arm's entry to the test of the bits in hand, with TWO VALUE HINTS (the root mask; the
     table index, scaled) *)
  zto_branch_hq Rfd (first [ zhint mask_not_sllw_m | zhint shiftl_2 ]).
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => rename Mx into M1 end.
  match goal with Hb : mem_u32 _ M1 (p + 7164) 0 |- _ => rename Hb into Hback0 end.
  (* THE LEAVE OF THE ROOT LOOP, in the list form (bound value: the hold) *)
  assert (KX1 : forall R' (H' : Z),
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
      (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (Some (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) [H'])
      R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_kx1 ->
    0 <= H' -> H' < 2 ^ (bits + 8 * (n - cin)) -> bits + 8 * (n - cin) <= 14 -> bits + 8 * (n - cin) <= 8 * n ->
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
      (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (Some (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) [])
      R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_e ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L1 (zupd R' []) M1 MD) T).
  { intros R' H' HRK HH1 HH2 HB14 HBn ER. rh_open ER. rh_open HRK. zgetl_nil.
    clear J28 KBA3 KLL KD.
    eapply (stub_L1 L_LVX_L1 R' [] M1 MD T q n cin bits u ret); [left; reflexivity | exact Hh | split_lists3; zreg | lia | lia | exact SRET |].
    intros R9 RH9 KP. keptc_open KP. open_lists3. zgetl_nil. zimps.
    pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
    unfold st_pull in SI1. st_cbn_in SI1.
    unfold KLEAVE, L_LEAVE in KL.
    eapply (KL R9 M1 _ ret lf cf SI1).
    - unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
- first [ exact SOUT | exact I ].
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  (* THE JOIN AT A ROOT ENTRY, in the list form (bound values: the table's base; the root mask; the next input
     address; the input left; the bit count; the hold; the root entry's address; the root entry's bit count) *)
  assert (J40 : forall R' (ci B Hd : Z),
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
      (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (Some (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) [])
      R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_e ->
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
      (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (Some (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext))
         [la; 2 ^ lb + -1; q + ci; n - ci; B; Hd; la + 4 * Z.land (2 ^ lb + -1) Hd; code_bits (rdL (Z.land (2 ^ lb + -1) Hd))])
      R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_j40 ->
    cin <= ci -> ci <= n -> B = bits + 8 * (ci - cin) -> code_bits (rdL (Z.land (2 ^ lb + -1) Hd)) <= B -> B <= 40 ->
    0 <= Hd -> Hd < 2 ^ B -> B <= 8 * ci ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_L40 (zupd R' []) M1 MD) T).
  { intros R' ci B Hd ER HRJ Hc1 Hc2 HB HbB HB40 HH1 HH2 HBc.
    cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_L40]. rh_open ER. rh_open HRJ. zgetl_nil.
    clear KX1 KL KD KBA3.
    set (i := Z.land (2 ^ lb + -1) Hd) in *.
    pose proof (land_mask_l' Hd lb ltac:(lia)) as Ri. fold i in Ri.
    pose proof (code_op_range (rdL i)) as Rop. pose proof (code_val_range (rdL i)) as Rval.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    (* (speed only) no run of this block takes a store: the separation facts are hidden from the kit's
       arithmetic; the entry's case fact is taken after the first run *)
    (* ONE RUN to the test of the entry's kind *)
    zto_branch_q Rfd.
    pose proof (tab_root_entry LENS rdL lb na i TOKL Ri) as (Hbits & _ & _ & CASES).
    destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
    - (* a root entry that ends the code: ONE RUN to the join point *)
      apply term_ok_LENS in TM as [Hb1 CLS].
      apply is_linkop_false in NL.
      assert (Hterm : code_op (rdL i) = 0 \/ 16 <= code_op (rdL i)).
      { destruct CLS as [(A & _) | [(A & _) | (A64 & _)]]; [lia | lia |].
        pose proof (land_range_r (code_op (rdL i)) 64 ltac:(lia)).
        destruct (Z.eq_dec (code_op (rdL i)) 0) as [E|E]; [left; exact E|]. right.
        destruct (Z_lt_dec (code_op (rdL i)) 16); [|lia]. exfalso. apply NL. lia. }
      destruct Hterm as [E | E];
        [ assert (Hbr : (code_op (rdL i) + -1) mod 18446744073709551616 = 18446744073709551615) by (rewrite E; reflexivity)
        | idtac ];
        (zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J28 Rx Mx ci B Hd (rdL i) 0) end));
        jfin.
    - (* a link to a second-level table: ONE RUN to the test of the bits in hand *)
      rewrite L2 in *.
      pose proof (op_link_tests (code_op (rdL i)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
      assert (HPm : 1 <= 2 ^ (lb + code_op (rdL i)) <= 32768) by (apply pow2_15; lia).
      pose proof (pow2_15 (code_op (rdL i)) ltac:(lia)) as HPlo.
      set (v := code_val (rdL i)) in *. set (lo := code_op (rdL i)) in *.
      (* the second-level mask in the form the run leaves it; its facts stand before the run *)
      assert (JR : forall Hx, 0 <= Z.land Hx (2 ^ (lb + lo) + -1) / 2 ^ lb < 2 ^ lo).
      { intros Hx. pose proof (land_mask_r Hx (lb + lo) ltac:(lia)) as A. replace (2 ^ (lb + lo) - 1) with (2 ^ (lb + lo) + -1) in A by lia.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
      pose proof (land_mask_r Hd (lb + lo) ltac:(lia)) as Rm. replace (2 ^ (lb + lo) - 1) with (2 ^ (lb + lo) + -1) in Rm by lia.
      pose proof (JR Hd) as Rj.
      destruct (SUB _ Rj) as [NL2 TM2]. pose proof TM2 as TM2'.
      (* (speed only) the second-level entry's case fact is taken after the run *)
      (* with FOUR VALUE HINTS (the second-level mask; the second-level index; the index with its base; the
         index, scaled) *)
      zto_branch_hq Rfd (first [ zhint mask_not_sllw_m | zhint srlw_small | zhint div_pow2_add_comm | zhint zext32_shift30 ]).
      apply term_ok_LENS in TM2 as [Hbits2 CLS2].
      set (m2 := 2 ^ (lb + lo) + -1) in *.
      (* THE JOIN AT A SECOND-LEVEL ENTRY, in the list form (bound values: the table's base; the root bits; the
         sub-table's first index; the input left, the bit count and the next input address at the root entry;
         the next input address; the input left; the bit count; the hold; the second-level entry's address; the
         second-level entry's bit count) *)
      assert (J700 : forall R2 (ci2 B2 H2 : Z),
        OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
          (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
             (Some (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) [])
          R2 [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_e ->
        OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
          (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
             (Some (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext))
             [la; lb; v; n - ci; B; q + ci; q + ci2; n - ci2; B2; H2;
              la + 4 * (v + Z.land H2 m2 / 2 ^ lb); code_bits (rdL (v + Z.land H2 m2 / 2 ^ lb))])
          R2 [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_j700 ->
        ci <= ci2 -> ci2 <= n -> B2 = bits + 8 * (ci2 - cin) -> lb + code_bits (rdL (v + Z.land H2 m2 / 2 ^ lb)) <= B2 -> B2 <= 40 ->
        0 <= H2 -> H2 < 2 ^ B2 -> B2 <= 8 * ci2 ->
        realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_L700 (zupd R2 []) M1 MD) T).
      { intros R2 ci2 B2 H2 ER2 HRJ2 Hd1 Hd2 HB2 HbB2 HB2' HH21 HH22 HBc2.
        cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_L700]. rh_open ER2. rh_open HRJ2. zgetl_nil.
        clear KLL CLS2 TM2' NL2 Hbits2 Rj Rm.
        pose proof (JR H2) as Rj2.
        set (j2 := Z.land H2 m2 / 2 ^ lb) in *.
        assert (HPB2 : 1 <= 2 ^ B2 <= 2 ^ 40) by (split; [pose proof (pow2_pos B2 ltac:(lia)); lia | apply pow2_le; lia]).
        pose proof (code_bits_range (rdL (v + j2))) as Rb2.
        pose proof (hold_shr_bound H2 B2 lb ltac:(lia) ltac:(lia)) as HH2'.
        pose proof (hold_lt_63 H2 B2 ltac:(lia) HH22) as HH263.
        destruct (SUB _ Rj2) as [NL3 TM3]. apply term_ok_LENS in TM3 as [Hbits3 CLS3].
        (* ONE RUN to the join point, with ONE VALUE HINT (the hold shifted down) *)
        zuntil_h Rfd (first [ zhint srl_hold_u ])
          (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
            eapply (J28 Rx Mx ci2 (B2 - lb) (H2 / 2 ^ lb) (rdL (v + j2)) lb) end).
        all: jfin. }
      (* (speed only) the case fact is hidden from the kit's arithmetic for the two runs below *)
      destruct (Z_lt_dec B (lb + code_bits (rdL (v + Z.land Hd m2 / 2 ^ lb)))) as [Hneed | Hok].
      + (* not enough bits: ONE RUN to the second-level loop *)
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (l_loop2 (S (Z.to_nat (n - ci))) Rx lx Mx MD T q n la na lb lo v m2 ci B ci B Hd fin rdL Hh) end).
        all: try rh_close.
        all: jfin.
        * intros R5 H' HR HH1' HH2' HB29 HBn KP. rh_open HR. zgetl_nil. rk_open KP. zimps.
          clear J700 J28 SUB JR.
          eapply (stub_L2 R5 [] M1 MD T q n ci B Hh); [zreg | zreg | zreg | lia | lia |].
          intros R9 RH9 KP9. keptc_open KP9. open_lists3. zgetl_nil. zimps.
          pose proof (sinv_pull _ _ lf cf n H' (B + 8 * (n - ci)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1' HH2' HBn ltac:(cbn; lia)) as [SI1 _].
          unfold st_pull in SI1. st_cbn_in SI1.
          unfold KLEAVE_LD, L_LEAVE_LD in KLL. zkeys.
          eapply (KLL R9 M1 _ lf cf SI1).
          -- unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
          -- close_std.
          -- split; [exact Hmode | exact SREST].
          -- exact SRET.
          -- first [ exact SOUT | exact I ].
          -- exact Hlens.
          -- exact Hcodes.
          -- exact HAG.
        * intros R5 ci' B' H' HR X1 X2 X3 X4 X5 X6 X7 X8 KP. rh_open HR. zgetl_nil. rk_open KP. zimps.
          eapply (J700 R5 ci' B' H'). all: jfin.
      + (* enough bits: ONE RUN to the join point *)
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J700 Rx ci B Hd) end). all: jfin. }
  clear KBA3 KLL KD J28.
  (* (speed only) the two runs below take no store *)
  destruct (Z_lt_dec bits (code_bits (rdL (Z.land (2 ^ lb + -1) hold)))) as [Hneed | Hok].
  - (* not enough bits: ONE RUN to the root loop *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (l_loop1 (S (Z.to_nat (n - cin))) Rx lx Mx MD T q n la na lb (2 ^ lb + -1) cin bits cin bits hold fin rdL Hh) end).
    all: try rh_close.
    all: jfin.
    + intros R' H' HR HH1' HH2' HB14 HBn KP. rh_open HR. zgetl_nil. rk_open KP. zimps.
      eapply (KX1 R' H'). all: jfin.
    + intros R' ci' B' H' HR X1 X2 X3 X4 X5 X6 X7 X8 KP. rh_open HR. zgetl_nil. rk_open KP. zimps.
      eapply (J40 R' ci' B' H'). all: jfin.
  - (* enough bits: ONE RUN to the join point *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J40 Rx cin bits hold) end). all: jfin.
Qed.
End S_Len.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import S_MatchL. Import S_Match. Import S_DistL. Import S_DistX. Import S_Dist. Import S_LenL. Import S_LenX. Import S_Len.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* moved to the layout: the tail's label, and one label of the third back module that the tail unfolds: each
   stays as a parse-only notation with its old name *)
Local Notation L_FRET := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_FRET (only parsing).
Local Notation L_LSLOW := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LSLOW (only parsing).

Ltac st_cbn := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext].

Definition st_fast (st : ist) (m ci co H B : Z) : ist :=
  IST m (t_last st) (t_flags st) ci co H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_after_fast : forall cx st lf cf m ci co H B,
  sinv cx st lf cf -> t_mode st = LEN ->
  0 <= ci -> ci <= c_n cx -> t_cout st <= co -> co <= c_osz cx ->
  0 <= B -> B <= 7 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B + (c_osz cx - co) < 8 * (c_n cx - t_cin st) + t_bits st + (c_osz cx - t_cout st) ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  (m = LEN \/ m = TYPE \/ m = BAD) ->
  sinv cx (st_fast st m ci co H B) lf cf /\ meas cx (st_fast st m ci co H B) < meas cx st.
Proof.
  intros cx st lf cf m ci co H B SI Hm Hci1 Hci2 Hco1 Hco2 HB1 HB2 HH1 HH2 HBc HW HI Hm'.
  dand SI as (RN0 & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_fast, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN = HEAD \/ LEN = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in RN0. icx_cbn. destr_conj RN0.
  dand P as (P1 & P2 & P3). unfold PROG, Wm in P1, P2, P3 |- *. icx_cbn.
  split; [split; [| split; [exact W | split]] |].
  - clear W Mf Mlive P1 P2 P3. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - clear W Mf Mlive Hm'. split; [lia_std | split; [lia_std |]].
    first [ exact P3 | destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std] ].
  - unfold MODE. icx_cbn.
    split; [clear - Hm'; unfold reach; destruct Hm' as [-> | [-> | ->]]; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros HL; destruct Hm' as [-> | [-> | ->]];
              [ apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
              | exfalso; clear - HL; unfold codes_liveP in HL; modes_cbv; lia_std
              | exfalso; clear - HL; unfold codes_liveP in HL; modes_cbv; lia_std ]
          | destruct Hm' as [-> | [-> | ->]]; mode_vacuous ].
  - clear - HW Hm'. pose proof (rank_range m) as RR. change (rank LEN) with 18. lia_std.
Qed.

Lemma win_arr {RCa1 : RunCtx}  : forall M w, 0 < w \/ w = 0 -> w + 32768 <= two64 -> (w <> 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M w 32768) ->
  exists fw, (w <> 0 -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M w 32768 fw) /\ (forall i, 0 <= i < 32768 -> 0 <= fw i < 256).
Proof.
  intros M w Hw Hw2 Ww. destruct (Z.eq_dec w 0) as [E|NE].
  - exists (fun _ => 0). split; [intros C; contradiction | intros; lia_std].
  - destruct (out_arr M w 32768 (Ww NE) ltac:(lia_std) ltac:(lia_std) Hw2) as (fw & A & B).
    exists fw. split; [intros _; exact A | exact B].
Qed.

Section LenF.
Context {RCa1 : RunCtx}.
Hypothesis IFAST : ifast_spec_s.

Theorem len_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LEN -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEN (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_).
  pose proof KM as KM0. pose proof RG as RG0. open_kmem KM. open_std STD.
  assert (TLV : tables_live cx st cf).
  { assert (ML : codes_liveP (t_mode st) -> tables_live cx st cf) by mode_get MODE_.
    apply ML. rewrite Hmd. unfold codes_liveP. cbv [LEN_ LEN LIT]. lia. }
  dand (live_tabs cx st lf cf M CX RNG_ TLV ROM Hcodes) as (na & nd & TB). clear TLV MODE_ PROG_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold tabsP in TB. icx_cbn. idtac.
  dand TB as (HtL & HtD & TOKL & TOKD & Cla1 & Cla2 & Cda1 & Cda2 & Cna & Cnd & ALla & ALda & Slaob & Slap & Sdaob & Sdap & Slap2 & Sdap2 & _).
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) lc) as la eqn:Ela.
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) dc) as da eqn:Eda.
  remember (rdc cf lc) as rdL eqn:ErdL. remember (rdc cf dc) as rdD eqn:ErdD. clear ErdL ErdD.
  pose proof (tab_ok_root _ _ _ _ TOKL) as (Hlb1 & Hna1 & _). pose proof (tab_ok_root _ _ _ _ TOKD) as (Hdb1 & Hnd1 & _).
  pose proof (pow2_15 lb ltac:(lia)) as HPlb. pose proof (pow2_15 db ltac:(lia)) as HPdb.
  prune_rng.
  zkeysb. unfold L_LEN, L_LSLOW, L_FRET, L_RELOAD, L_IFAST in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  (* THE THREE TESTS OF THE FAST WAY: one run to each open test; where a test fails, ONE RUN to the slow way *)
  zto_branch_q Rfd.
  destruct (Z_lt_dec (n - cin) 6) as [Hh6 | Hh6].
  { zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (len_slow_s _ fin MD T M0 Rx lx M
                (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI0) end); [| exact KM0 | exact K].
    unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg. }
  zto_branch_q Rfd.
  destruct (Z_lt_dec (osz - cout) 258) as [Hl258 | Hl258].
  { zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (len_slow_s _ fin MD T M0 Rx lx M
                (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI0) end); [| exact KM0 | exact K].
    unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg. }
  zto_branch_q Rfd.
  destruct (Z_lt_dec 7 bits) as [Hb8 | Hb8].
  { zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (len_slow_s _ fin MD T M0 Rx lx M
                (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI0) end); [| exact KM0 | exact K].
    unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg. }
  clear KM0 RG0.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KD10 KD00 KSM KB11 KB10 KBA3 KL KLL KRT.
  (* the frame's slots are opened ALL *)
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn. destr_conj FR.
  pose proof SOUT as S80. unfold s_out in S80. icx_cbn.
  pose proof CST as CS. unfold i_cst in CS. icx_cbn. dand CS as (S64u & _ & _ & _ & _ & _ & C60 & C72 & C7144).
  (* the state's facts are opened before the run *)
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn.
  dand SR0 as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
  rewrite <- Ela in C104. rewrite <- Eda in C112. clear SREST.
  pose proof WIN_ as WIN'. unfold WIN in WIN'. icx_cbn. cbv [WIN_SIZE] in WIN'. destruct WIN' as [WIN0 WIN1].
  unfold ifast_spec_s, ifast_spec_at in IFAST.
  (* ONE RUN to the fast decoder's call. Its specification wants the output's and the window's bytes as
     arrays of the memory at the call: the handed-in tactic takes them there, behind a test that the
     specification applies at all. The frame's extent, the return place and the read-only bound are handed
     to the specification as the VALUES of their names (computed, not written): the callee's footprint then
     stands in written distances, as the kit's re-attach word after the call needs it *)
  zuntil Rfd (idtac; assert_succeeds (eapply IFAST);
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      destruct (out_arr Mx ob osz Wob ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fo & HOB & Rfo);
      destruct (win_arr Mx w ltac:(lia) ltac:(rewrite TW64; lia) ltac:(intros Hw; pose proof Ww as X; rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw) in X; cbv [WIN_SIZE] in X; exact X)) as (fw & Hwin & Rfw);
      let NF := eval cbv in (- FR_INF) in
      let RP := eval cbv in L_FRET in
      let RH := eval cbv in ROMHI_S in
      eapply (IFAST Rx lx Mx MD T u p q n ob osz w whave wnext cin cout hold bits out lb db la na da nd (u + NF) RP RH zc rdL rdD fin fo fw Hh) end).
  all: first [ lazymatch goal with
       | |- zget_l _ _ _ = _ => zreg
       | |- Z.land _ _ = _ => reflexivity
       | |- ZSEP _ => first [ assumption | exact (sep_ob_u _ _ SEP) | exact (sep_p_ob _ _ SEP) | exact (sep_p_q _ _ SEP) | exact (sep_ob_q _ _ SEP)
                            | exact (sep_w_p _ _ SEP) | exact (sep_w_q _ _ SEP) | exact (sep_w_ob _ _ SEP) ]
       | |- tab_ok _ _ _ _ = true => assumption
       | |- _ mod _ = _ => cbv [FR_INF]; first [ assumption | exact (proj1 AL) | exact (proj1 (proj2 AL))
                                 | pose proof (proj1 AL) as ALu; clear - ALu; cbn in ALu; Z.to_euclidean_division_equations; lia ]
       | |- _ \/ _ => destruct (Z.eq_dec w 0) as [Ew|Nw]; [left; exact Ew | right; split; [lia | split; [cbv [WIN_SIZE ]; lia | exact (proj2 (proj2 AL))]]]
       | |- _ -> mem_wr _ _ _ _ => intros Hw; pose proof Ww as X; rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw) in X; cbv [WIN_SIZE] in X |- *; exact X
       | |- _ -> mem_arr _ _ _ _ _ _ => exact Hwin
       | |- _ -> _ /\ _ => first [exact WIN0 | cbv [WIN_SIZE]; exact WIN1]
       | |- mem_wr _ _ _ _ => first [assumption | exact Wstk]
       | |- mem_arr _ _ _ _ _ _ => assumption
       | |- mem_u64 _ _ _ _ => assumption
       | |- mem_u32 _ _ _ _ => first [assumption | exact C60 | cbv [LEN]; assumption]
       | |- forall i : Z, _ => first [exact Hfin | exact Rfo | exact Rfw]
       | |- forall R' M', _ => idtac
       | |- _ => cbv [FRA STATE_SIZE WIN_SIZE FR_IF FR_INF ROMHI_S L_FRET]; first [assumption | lia]
       end
       ].
  intros R' M' cin' cout' hold' bits' mode' fo' Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hho1 Hho2 Hb3 HWlt HIle Hm' HP E8 E16 E32 E40 P80 P88 P8 HOB' Rfo' KE.
  unfold kept_eq in KE. zkeys. destr_conj KE. zimps.
  clear Hmode HOB Hwin C60 C72 C7144 S64u HtL HtD.
  repeat match goal with
         | H : mem_u64 _ ?Mo _ _ |- _ => lazymatch Mo with M' => fail | _ => lazymatch type of H with
             | mem_u64 _ _ (u) _ => clear H | mem_u64 _ _ (u + 24) _ => clear H | mem_u64 _ _ (p + 96) _ => clear H end end
         | H : mem_u32 _ ?Mo _ _ |- _ => lazymatch Mo with M' => fail | _ => lazymatch type of H with
             | mem_u32 _ _ (u + 8) _ => clear H | mem_u32 _ _ (u + 32) _ => clear H | mem_u32 _ _ (p + 104) _ => clear H end end
         end.
  (* (speed only) the old memory's open facts inside the callee's footprint are dropped before the kit's
     re-attach word *)
  unfold if_fp in HP. cbv [FR_IF] in HP. drop_in_fp HP. zreattachL HP.
  assert (Hmv : 0 <= mode' < 2147483648) by (clear - Hm'; cbv [LEN TYPE BAD] in Hm'; lia).
  (* ONE RUN from the fast decoder's return to the test of the mode it left *)
  zto_branch_q Rfd.
unfold KRELOAD in KRL. unfold KRELOAD_A1 in KRA1. zkeys.
  assert (JRA : forall R9 M9 (m9 : Z),
    (m9 = LEN \/ m9 = TYPE \/ m9 = BAD) -> m9 = mode' \/ (m9 = TYPE /\ mode' = TYPE) ->
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
      (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (Some (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext))
         [q + cin'; n - cin'; ob + cout'; osz - cout'; hold'; bits'])
      R9 [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenb_jra ->
    s_std (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M9 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M9 (p + 8) m9 ->
    st_rest (run_segments R_segs rc_inp rc_sp rc_mb) (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M9 ->
    s_ret (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M9 ->
    s_out (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M9 ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M9 (p + 168) 320 lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M9 (p + 1384) 1444 cf ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X [(u - 1024, 1024); (u, 112); (p, 7176); (ob, osz)]) M9 ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LENB_RELOAD_J (zupd R9 []) M9 MD) T).
  { intros R9 M9 m9 Hm9 _ HRJ STD9 Hmo9 SR9 RET9 OUT9 HL9 HC9 HAG9.
    rh_open HRJ. zgetl_nil.
    pose proof (sinv_after_fast _ _ lf cf m9 cin' cout' hold' bits' SI0 eq_refl Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hho1 Hho2 Hb3
                  ltac:(cbn; lia) ltac:(cbn; lia) Hm9) as [SI9 ME9].
    unfold st_fast in SI9, ME9. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI9, ME9.
first [ eapply (KRL R9 M9 _ lf cf SI9 ME9) | eapply (KRA1 R9 M9 _ lf cf SI9 ME9) ].
    - unfold s_regs_reload; icx_cbn; zkeys; split_conj; try assumption; first [intros C; discriminate C | intros _; assumption].
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption. all: exact SR9. }
  destruct (Z.eq_dec mode' TYPE) as [HmT | HmT]; cbv [TYPE] in HmT.
  - (* ONE RUN to the reload's join point *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (JRA Rx Mx mode' Hm' ltac:(left; reflexivity)) end).
    all: try rh_close.
    all: try zreg.
    all: first [close_std | assumption | unfold st_rest; icx_cbn; split_conj; first [assumption | subst la; assumption | subst da; assumption]].
  - (* ONE RUN to the reload's join point *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (JRA Rx Mx mode' Hm' ltac:(left; reflexivity)) end).
    all: try rh_close.
    all: try zreg.
    all: first [close_std | assumption | unfold st_rest; icx_cbn; split_conj; first [assumption | subst la; assumption | subst da; assumption]].
Qed.

Theorem arm_LEN : arm_stmt L_LEN LEN.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply len_s; try eassumption.
Qed.

Lemma sinv_len_ : forall cx st lf cf,
  sinv cx st lf cf -> t_mode st = LEN_ ->
  sinv cx (st_le st LEN (t_length st) (t_extra st)) lf cf /\ meas cx (st_le st LEN (t_length st) (t_extra st)) < meas cx st.
Proof.
  intros cx st lf cf SI Hm.
  dand SI as (RN0 & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN_ = HEAD \/ LEN_ = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN_ -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN_ last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  split; [split; [exact RN0 | split; [exact W | split; [prog_transfer P|]]] |].
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Theorem arm_LEN_ : arm_stmt L_LEN_ LEN_.
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
  (* ONE RUN to the next arm's entry *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (len_s _ fin MD T M0 Rx lx Mx
              (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI1) end).
  - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [LEN]; assumption | exact SREST | exact SRET | exact SOUT | exact I | exact HAG].
  - eapply KALL_mono; [| exact K]. clear - ME1. lia.
Qed.
End LenF.
