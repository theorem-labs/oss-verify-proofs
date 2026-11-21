(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require S9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SBase S_ZB S_GroupB.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame Hoare AllocSim.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require MstepsGrows.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_Entry S_ZA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZStep ZMem ZTac ZPrune ZSysLite ZCall ZCallL ZArr ZRd IGlue IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZGo11 SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.

Module S_ZC.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Frame OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Hoare OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.AllocSim.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9LibStmt.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZStep OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZPrune OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZSysLite OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZRd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IGlue OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.MstepsGrows.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations. Open Scope bv_scope. Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

(* THE MODULE's OWN LABEL IS A FIELD OF THE IMAGE's LAYOUT TEXT; here it has its short name only *)
Local Notation L_EPI_S := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_EPI_S (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation rkeeps := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps (only parsing).
Local Notation qval := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval (only parsing).

(* BY-FORM READERS OF THE CONTRACT's STATEMENT. The contract's statement says its register and memory facts in
   its own words; each reader below takes its register, its address and its value FROM THE FACT OR THE GOAL IT
   WORKS ON and writes none of them. A fact of the reader's form that it cannot read FAILS the reader. *)

(* a key that is said through its register is made a numeral *)
Ltac zkey_lit :=
  repeat match goal with
         | |- context [bv_key ?RG] => let KV := eval cbv in (bv_key RG) in change (bv_key RG) with KV
         end.

(* a difference is said as a sum (the form in which the walk's steps say an address) *)
Ltac znorm_sub_in HH :=
  repeat match type of HH with
         | context [?AA - ?BB] => let NB := eval cbv in (- BB) in replace (AA - BB) with (AA + NB) in HH by lia
         end.

(* every fact "this register holds this word" of the start state becomes a fact of the walk's register tree;
   GK is the lemma that reads a register of the start state *)
Ltac iface_regs RB GK :=
  repeat match goal with
         | HG : getr _ ?RR = Z_to_bv 64 ?ZZ |- _ =>
             let KV := eval cbv in (bv_key RR) in
             let LG := fresh "LG" in
             first [ assert (LG : zget_l RB [] KV = ZZ)
                       by (refine (eq_trans (GK RR eq_refl) _); rewrite HG;
                           change (Z_to_bv 64 ZZ) with (w64 ZZ); rewrite w64_unsigned, mod_small_u64 by lia; reflexivity)
                   | fail 3 "READER: a register fact of the contract is not read" ];
             clear HG; znorm_sub_in LG
         | HG : getr _ ?RR = ?WW |- _ =>
             is_var WW;
             let KV := eval cbv in (bv_key RR) in
             let LG := fresh "LG" in
             first [ assert (LG : zget_l RB [] KV = bv_unsigned WW)
                       by (refine (eq_trans (GK RR eq_refl) _); rewrite HG; reflexivity)
                   | fail 3 "READER: a register fact of the contract (a word) is not read" ];
             clear HG
         end.

(* every fact "this register's value is this" of the start state becomes a fact of the walk's register tree *)
Ltac iface_vals RB GK :=
  repeat match goal with
         | EH : bv_unsigned (getr _ ?RR) = ?VV |- _ =>
             let KV := eval cbv in (bv_key RR) in
             let LG := fresh "LG" in
             first [ assert (LG : zget_l RB [] KV = VV) by (refine (eq_trans (GK RR eq_refl) _); exact EH)
                   | fail 3 "READER: a register value of the token is not read" ];
             clear EH
         end.

(* every fact "these bytes stand at this address" becomes a cell fact of the walk *)
Ltac iface_mem :=
  repeat match goal with
         | HR : rdn _ ?MM (Z_to_bv 64 ?AA) 8 = Some (Z_to_le_bytes 8 ?VV) |- _ =>
             first [ change (mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) MM AA VV) in HR
                   | fail 3 "READER: a cell fact of the contract is not read" ];
             znorm_sub_in HR
         | HR : rdn _ ?MM (Z_to_bv 64 ?AA) 8 = Some (word_to_le_bytes 8 ?WW) |- _ =>
             first [ change (mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) MM AA (bv_unsigned WW)) in HR
                   | fail 3 "READER: a cell fact of the contract (a word) is not read" ];
             znorm_sub_in HR
         | HR : rdn _ ?MM (Z_to_bv 64 ?AA) 4 = Some (Z_to_le_bytes 4 ?VV) |- _ =>
             first [ change (mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) MM AA VV) in HR
                   | fail 3 "READER: a half-cell fact of the contract is not read" ];
             znorm_sub_in HR
         end.

(* every fact "this region may be stored to" becomes a writable-region fact of the walk *)
Ltac iface_store :=
  repeat match goal with
         | HS : store_ok _ ?MM (Z_to_bv 64 ?AA) (Z.to_nat ?NN) = true |- _ =>
             let WR := fresh "WR" in
             first [ (pose proof (mem_wr_of_store_ok _ _ _ _ HS) as WR; rewrite Z2Nat.id in WR by lia;
                      change (mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) MM AA NN) in WR)
                   | fail 3 "READER: a store fact of the contract is not read" ];
             znorm_sub_in WR; clear HS
         | HS : store_ok _ _ ?WW (Z.to_nat _) = true |- _ =>
             is_var WW; rewrite <- (Z_to_bv_bv_unsigned 64 WW) in HS
         end.

(* a goal "this register of the end state holds this word": the register and the word are the goal's own.
   The end state is the walk's tree with its update list (the first form) or a tree whose facts are in hand
   (the second form). GK reads a register of the start state. *)
Ltac zd_iface GK :=
  lazymatch goal with
  | |- getr (zden (zupd ?RB ?LC)) ?RG = ?WW =>
      eapply eq_trans; [ exact (getr_zupd RB LC RG eq_refl) | ];
      lazymatch WW with
      | Z_to_bv 64 ?ZZ => change (Z_to_bv 64 ZZ) with (w64 ZZ); apply (f_equal w64)
      | getr _ ?RR => eapply eq_trans; [ | exact (w64_of_word WW) ]; apply (f_equal w64);
                      eapply eq_trans; [ | exact (GK RR eq_refl) ]
      | _ => eapply eq_trans; [ | exact (w64_of_word WW) ]; apply (f_equal w64)
      end;
      zkey_lit; zreg
  | |- getr (zden ?RX) ?RG = ?WW =>
      eapply eq_trans; [ exact (getr_zkey RX RG eq_refl) | ];
      lazymatch WW with
      | Z_to_bv 64 ?ZZ => change (Z_to_bv 64 ZZ) with (w64 ZZ); apply (f_equal w64)
      | getr _ ?RR => eapply eq_trans; [ | exact (w64_of_word WW) ]; apply (f_equal w64);
                      eapply eq_trans; [ | exact (GK RR eq_refl) ]
      | _ => eapply eq_trans; [ | exact (w64_of_word WW) ]; apply (f_equal w64)
      end;
      zkey_lit; first [ assumption | zreg ]
  end.

(* the same for a goal over a list of registers that the contract names *)
Ltac zd_iface_all GK :=
  first [ zd_iface GK
        | (let RR := fresh "rr" in let HR := fresh "Hr" in
           intros RR HR; unfold S_ENTRY in HR; cbn [app] in HR;
           repeat (destruct HR as [<- | HR]; [ zd_iface GK | ]); destruct HR) ].

Section ZC.
Context {RCa1 : RunCtx}.

Lemma zsetreg_lemma : forall segs pc Rb k (e v : Z) rest M MD T, v = e ->
  realizes segs (zcfg segs pc (zupd Rb ((k, v) :: rest)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb ((k, e) :: rest)) M MD) T.
Proof. intros. subst. assumption. Qed.
Ltac zsetreg v tac := eapply (zsetreg_lemma _ _ _ _ _ v); [tac|].

End ZC.


Definition MD0 : Model := mkModel [] (mkVmMaps [] [] (Z_to_bv 64 0) (Z_to_bv 64 0) 0) IEof [] None None None.
Lemma MD0_halted : m_halted MD0 = None.
Proof. reflexivity. Qed.

(* the application of the epilogue's statement, handed to the runs below; and the opener of its two lists *)
Local Ltac to_epi EPI := idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?LC) _ _) _ => apply (EPI LC) end.
Local Ltac epi_lists :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_epi OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_top_epi];
  split_conj.

(* THE CALLER's TAIL AFTER THE LIBRARY's LAST CALL, UNDER THE CONTRACT's OWN WORDS. The start state's facts are
   read from the contract's hypotheses; the result set says the contract's own conclusion about the end state's
   registers; the walk is runs; the one join point (the epilogue) has its label, its register map and its keep
   list in the layout. No register, no distance of the frame and no label value is written here. *)
Theorem zc_s {RCa1 : RunCtx}  : zc_stmt_S9.
Proof.
  unfold zc_stmt_S9.
  intros regs mem u. intros.
  cbv [S9_IMG_TOP] in *. pose proof two64_eq as TW64.
  set (Rb := zlift regs).
  assert (Gk : forall r : reg, bv_eqb r 0%bv = false -> zget_l Rb [] (bv_key r) = bv_unsigned (getr regs r)).
  { intros r Hr. cbv [zget_l alookup]. subst Rb. rewrite zget_zlift, (getr_reg_get regs r Hr). reflexivity. }
  (* the result set: the end place, the one cell the tail clears, and the contract's own register conclusion *)
  lazymatch goal with
  | |- exists rr mm, _ /\ _ /\ @?IF rr =>
      set (Q := fun (MDx : Model) (c : config) => exists lc M',
        c = zcfg (run_segments R_segs rc_inp rc_sp rc_mb) S9_HARN_RA (zupd Rb lc) M' MDx
        /\ mpost (run_segments R_segs rc_inp rc_sp rc_mb) mem M' (u + 56) (u + 64) 0 0
        /\ IF (zden (zupd Rb lc)))
  end.
  assert (HR : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) S9_ZC (zupd Rb []) mem MD0) (Q MD0)).
  { (* the start state's facts, read from the contract's hypotheses; over the empty update list they are said
       in the tree form *)
    iface_regs Rb Gk. iface_store. iface_mem. zgetl_nil.
    (* from here the walk speaks of the register tree and of the model as of any tree and any model that is not
       halted (as the walk lemmas of the other texts do) *)
    generalize MD0_halted. generalize MD0. intros MD Hh. clearbody Rb.
    (* the first word of the region that may be stored to holds some value *)
    lazymatch goal with
    | WR : mem_wr _ mem ?BA _ |- _ =>
        destruct (mem_wr_u64_exists_R mem BA ltac:(eapply mem_wr_sub; [exact WR | lia | lia])) as (s16 & H16 & Rs16)
    end.
    zkeys. unfold S9_HARN_RA, S9_RA2, S9_ZC in *.
    pose proof (mpost_refl (run_segments R_segs rc_inp rc_sp rc_mb) mem (u + 56) (u + 64) 0 0 : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) mem X (u + 56) (u + 64) 0 0) mem) as HAG.
    pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) mem (u + 56) (u + 64) 0 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HST.
    (* ONE RUN to the first test of the return code *)
    zto_branch Rfd.
    (* THE EPILOGUE: value number 0 of the list is the stream's address (the stack pointer holds it); the
       layout's keep list holds what it held at the start *)
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
    assert (EPI : forall lc,
       rholds (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs [u]) Rb lc OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_epi ->
       rkeeps (zupd Rb lc) Rb [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_top_epi ->
       realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_EPI_S (zupd Rb lc) Mc MD) (Q MD)) end.
    { intros lc REL RKL.
      cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_epi] in REL. destr_conj REL.
      cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_top_epi] in RKL. destr_conj RKL.
      repeat match goal with HK : zget (zupd Rb lc) _ = _ |- _ => rewrite zget_zupd in HK end.
      zkeys. unfold L_EPI_S.
      (* ONE RUN to the caller's return place; there the contract's conclusion is read off the registers *)
      zgo Rfd S9_HARN_RA.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?LC) ?MX _) _ => apply rz_now; subst Q; cbv beta; exists LC, MX end.
      split; [reflexivity|]. split; [exact HAG|].
      split_conj; zd_iface_all Gk. }
    (* THE CASE TREE: each run takes the test that the case split above it decided; each leaf is one run to the
       epilogue *)
    destruct (Z.eq_dec s16 1) as [E1|N1].
    { zuntil Rfd (to_epi EPI); epi_lists; zreg. }
    zto_branch Rfd.
    destruct (Z.eq_dec s16 2) as [E2|N2].
    { zuntil Rfd (to_epi EPI); epi_lists; zreg. }
    zto_branch Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ((_, ?EV) :: _)) _ _) _ => destruct (Z.eq_dec (EV mod 18446744073709551616) 0) as [Ez|Ez] end;
      zuntil Rfd (to_epi EPI); epi_lists; zreg. }
  (* the contract's conclusion from the result set *)
  dand HR as (ms' & RUN & HQ). subst Q. cbv beta in HQ. cbn [cfg_ms cfg_model zcfg] in RUN, HQ.
  dand HQ as (lc & M' & E & HP & IFQ).
  unfold zcfg in E. injection E as E1. subst ms'.
  exists (zden (zupd Rb lc)), M'.
  split; [| split; [| exact IFQ]].
  - unfold zst in RUN. cbn [zupd] in RUN. subst Rb. rewrite zden_zlift in RUN. exact RUN.
  - replace 8 with (u + 64 - (u + 56)) by lia.
    apply (frame_mod_of_mpost (run_segments R_segs rc_inp rc_sp rc_mb)); [lia | lia | exact HP |].
    pose proof (msteps_mem_grows (run_segments R_segs rc_inp rc_sp rc_mb) _ _ RUN) as G. unfold zst in G. cbn [ms_mem] in G. exact G.
Qed.

End S_ZC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_Type S_Check.

Module S_Head.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Check.S_HeadA.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* THE MODULE's FOUR OWN LABELS ARE FIELDS OF THE IMAGE's LAYOUT TEXT; here they have their short names only *)
Local Notation L_HEAD_LOOP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_HEAD_LOOP (only parsing).
Local Notation L_HEAD_BODY := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_HEAD_BODY (only parsing).
Local Notation L_HEAD_WERR := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_HEAD_WERR (only parsing).
Local Notation L_HEAD_FIN := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_HEAD_FIN (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation rkeeps := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps (only parsing).
Local Notation qval := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval (only parsing).

(* OPENERS OF THE LIST FORM (they only unfold, split and name): every list-form hypothesis: the meaning over
   the layout's lists is unfolded, the conjunction split and its parts named; the same for a goal *)
Ltac open_lists :=
  repeat match goal with
         | HH : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_body OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_werr
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_fin OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_loop
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_dn] in HH;
             unfold hd_st in HH; icx_cbn; destr_conj HH
         | HH : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_top_head_loop] in HH; destr_conj HH
         end.
Ltac split_lists :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_body OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_werr
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_fin OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_loop
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_top_head_loop];
  unfold hd_st; icx_cbn; split_conj.

(* a register that holds a numeral is inside the word's range *)
Ltac zrange_lit :=
  lazymatch goal with
  | |- 0 <= ?XX < _ => let EA := fresh "EA" in eassert (EA : XX = _) by zreg; rewrite EA; clear EA
  end; lia.

Definition fp_head (u p : Z) : list (Z * Z) := [(p + 8, 4); (p + 28, 20); (u + 48, 8); (u + 96, 8)].

Section WITH_ADLER_NULL.
Context {RCa1 : RunCtx}.
Hypothesis ADLN : adler32_null_spec_s.

Lemma head_main : forall cx fin MD T M0 Rb l M st lf cf (cin1 hold1 bits1 : Z),
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = HEAD -> sinv cx st lf cf ->
  s_regs_arm cx (hd_st st (t_mode st) (t_flags st) cin1 hold1 bits1) Rb l ->
  rholds (qval cx (Some (hd_st st (t_mode st) (t_flags st) cin1 hold1 bits1)) 0) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_body ->
  t_cin st <= cin1 <= c_n cx -> 16 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
  8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_HEAD_BODY (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf cin1 hold1 bits1 CX Hh Hfin Hm SI REA REH Hc1 Hb1 Hh1 Hbc1 HW1 KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof KM as KM0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags t_cin t_cout t_hold t_bits t_out] in *. subst mode. icx_cbn.
  (* the place's register facts: the base text's arm map and the layout's list, at the state that the statement
     binds *)
  unfold s_regs_arm, s_fix, s_vars, hd_st in REA. icx_cbn. destr_conj REA. open_lists.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh64.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & _ & H48 & H56 & _).
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  (* the frame's slots are opened ALL *)
  destr_conj FRM'.
  pose proof (rom_mod31_u64 M ROM) as H31.
  pose proof SREST as SR'. unfold st_rest in SR'. icx_cbn. dand SR' as (_ & H24 & _).
  clear ROM Wob Ww FRM CST HK Hmode SREST SRET SOUT Hlens Hcodes Hin.
  zkeysb. unfold L_HEAD_BODY, L_HEAD_WERR, L_HEAD_FIN, L_BADMSG_S11 in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_head u p) ltac:(unfold fp_head; ranges_ok_tac)) as HSTh.
  assert (HAGh : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (fp_head u p)) M) by (apply mpostL_refl).
  unfold fp_head in HSTh, HAGh.
  assert (EXIT : forall (ra1 : bool) RX Mq m' flags' hold' bits',
    sinv (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                m' flags' cin1 hold' bits') lf cf ->
    meas (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                m' flags' cin1 hold' bits') <
    meas (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ->
    s_regs_reload (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
         (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                m' flags' cin1 hold' bits') RX (negb ra1) true ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 8) m' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 28) flags' ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M Mq [(p + 8, 4); (p + 28, 20); (u + 48, 8); (u + 96, 8)] ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) (if ra1 then L_RELOAD_RA else L_RELOAD_A1) (zupd RX []) Mq MD) T).
  { intros ra1 RX Mq m' flags' hold' bits' SI1 MB1 RRL Hm8 Hf24 HPq.
    clear HST HAG Wstk Wp HSTh HAGh H48 H56 H31 H24.
    repeat match goal with HH : mem_u64 _ _ (u + _) _ |- _ => clear HH end.
    open_kmem KM0. open_std STD. destruct SAT as [Hmode SREST]. clear Hmode.
    unfold st_rest in SREST. icx_cbn.
    dand SREST as (H12 & _ & H64 & H68 & H92 & H96 & H100 & H104 & H112 & H120 & H124 & H128 & H132 & H136 & H140 & H144).
    fp_frame_from HP0.
    cbv [N_LENS N_CODES] in Hlens, Hcodes.
    zreattachL HPq.
    destruct ra1;
      [ change (if true then L_RELOAD_RA else L_RELOAD_A1) with L_RELOAD_RA;
        eapply (KRRA RX Mq (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                              m' flags' cin1 hold' bits') lf cf SI1 MB1)
      | change (if false then L_RELOAD_RA else L_RELOAD_A1) with L_RELOAD_A1;
        eapply (KRA1 RX Mq (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                              m' flags' cin1 hold' bits') lf cf SI1 MB1) ].
    1,3: exact RRL.
    all: unfold k_mem; split_conj;
      [ close_std
      | unfold st_at, st_rest, hd_st; icx_cbn; split_conj; assumption
      | unfold s_ret, hd_st in *; icx_cbn; assumption | first [ exact I | (unfold s_out, hd_st in *; icx_cbn; assumption) ]
      | assumption | assumption | exact HAG ]. }
  (* the exit's two entries, each under a name of its own (the runs below name them) *)
  pose proof (EXIT false) as EXIT_A1. pose proof (EXIT true) as EXIT_RA.
  (* ONE RUN to the first open test; the test is taken each way *)
  zto_branch Rfd.
  clear H31 H48.
  zbranch_split Rfd.
  2: { (* the test fails: ONE RUN to the error place *)
    pose proof (sinv_hd _ _ lf cf BAD flags cin1 hold1 bits1 SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(intros _; right; reflexivity)
                  ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  BAD flags cin1 hold1 bits1 ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MB1.
    clear HSTh HAGh H56 H24 EXIT. repeat match goal with HH : mem_u64 _ _ (u + _) _ |- _ => clear HH end.
    open_kmem KM0. destruct SAT as [Hmode SREST].
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ =>
      eapply (KB11 RX MX (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                                  HEAD flags cin1 hold1 bits1) lf cf SI1 MB1) end).
    - unfold s_regs_disp, s_fix, s_vars, hd_st; icx_cbn; zkeys; split_conj; zreg.
    - zrange_lit.
    - unfold k_mem, hd_st; icx_cbn; split_conj;
        [ exact STD | split; [exact Hmode | exact SREST] | exact SRET | exact SOUT | exact Hlens | exact Hcodes | exact HP0 ]. }
  (* ONE RUN to the test of the method; the test is taken each way *)
  zto_branch Rfd.
  zbranch_split Rfd.
  { (* another method: ONE RUN to the exit *)
    clear H56.
    pose proof (sinv_hd _ _ lf cf BAD flags cin1 hold1 bits1 SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(intros _; right; reflexivity)
                  ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  BAD flags cin1 hold1 bits1 ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MB1.
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ => apply (EXIT_A1 RX MX BAD flags hold1 bits1 SI1 MB1) end);
      first [ exact HAGh | assumption
            | (unfold s_regs_reload, hd_st; cbn [negb]; icx_cbn; zkeys; split_conj; first [zreg | intros; discriminate | intros _; zreg]) ]. }
  (* ONE RUN to the first test of the window size *)
  zto_branch Rfd.
  pose proof (shiftr_lt_pow2 hold1 bits1 4 ltac:(lia) Hh1) as Hsh4.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (WERR : forall RW,
    rholds (qval (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
              (Some (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                           HEAD flags cin1 hold1 bits1))
              (Z.shiftr hold1 4)) RW [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_werr ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_HEAD_WERR (zupd RW []) Mc MD) T) end.
  { intros RW RHW. open_lists. zgetl_nil. unfold L_HEAD_WERR. zkeys. clear H56.
    pose proof (sinv_hd _ _ lf cf BAD flags cin1 (Z.shiftr hold1 4) (bits1 - 4) SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity)
                  ltac:(intros _; right; reflexivity)
                  ltac:(cbn; lia) ltac:(lia) ltac:(exact Hsh4) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  BAD flags cin1 (Z.shiftr hold1 4) (bits1 - 4) ltac:(left; cbn; lia)) as MB1.
    (* ONE RUN to the exit *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ => apply (EXIT_A1 RX MX BAD flags (Z.shiftr hold1 4) (bits1 - 4) SI1 MB1) end);
      first [ exact HAGh | assumption
            | (unfold s_regs_reload, hd_st; cbn [negb]; icx_cbn; zkeys; split_conj; first [zreg | intros; discriminate | intros _; zreg]) ]. }
  (* the test of the window size is taken each way *)
  zbranch_split Rfd.
  { (* the size is too large: the error place is reached at once; the shifted hold is said in its plain form *)
    zuntil0 Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RW _ _) _ => apply (WERR RW) end);
      split_lists; rewrite ?(Z.mod_small hold1) by lia; zreg. }
  (* ONE RUN to the second test of the window size; it is taken each way *)
  zto_branch Rfd.
  zbranch_split Rfd.
  2: { zuntil0 Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RW _ _) _ => apply (WERR RW) end);
         split_lists; rewrite ?(Z.mod_small hold1) by lia; zreg. }
  clear WERR Hsh4.
  (* ONE RUN to the checksum callee's call *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RR ?LC) ?MX _) _ =>
    eapply (ADLN RR LC MX MD T _ Hh) end); [zreg | zreg | zreg | reflexivity |].
  intros R2 E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
  zimps. zkeys.
  (* ONE RUN to the test of the header's top bit *)
  zto_branch Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (FIN : forall RF m', (m' = DICTID \/ m' = TYPE) ->
    rholds (qval (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
              (Some (hd_st (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                           HEAD flags cin1 hold1 bits1))
              m') RF [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_fin ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_HEAD_FIN (zupd RF []) Mc MD) T) end.
  { intros RF m' Hm' RHF. open_lists. zgetl_nil. unfold L_HEAD_FIN. zkeys.
    assert (Rm' : 0 <= m' < 4294967296) by (destruct Hm' as [-> | ->]; cbv [DICTID TYPE]; lia).
    pose proof (sinv_hd _ _ lf cf m' 0 cin1 0 0 SI0 eq_refl ltac:(destruct Hm' as [-> | ->]; (first [solve [zkeep_section; tauto] | tauto])) ltac:(right; reflexivity)
                  ltac:(intros E; discriminate E)
                  ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  m' 0 cin1 0 0 ltac:(left; cbn; lia)) as MB1.
    (* ONE RUN to the exit. LOCAL FIRST-OF-CONTINUATIONS STOP: the run ends at the first of the exit's two places
       that it reaches *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX ?MX _) _ =>
                  first [ apply (EXIT_RA RX MX m' 0 0 0 SI1 MB1) | apply (EXIT_A1 RX MX m' 0 0 0 SI1 MB1) ] end);
      first [ exact HAGh | assumption
            | (unfold s_regs_reload, hd_st; cbn [negb]; icx_cbn; zkeys; split_conj; first [zreg | intros; discriminate | intros _; zreg]) ]. }
  (* the test of the header's top bit is taken each way *)
  zbranch_split Rfd.
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RF _ _) _ => apply (FIN RF TYPE) end); [right; reflexivity | split_lists; zreg].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RF _ _) _ => apply (FIN RF DICTID) end); [left; reflexivity | split_lists; zreg].
Qed.


Lemma head_loop : forall (k : nat) cx fin MD T Rb l M (st0 : ist) (cinj holdj j : Z),
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_S cx ->
  16 - 8 * Z.of_nat k <= j < 24 - 8 * Z.of_nat k -> (1 <= k <= 2)%nat -> 0 <= j ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  rholds (qval cx (Some (hd_st st0 (t_mode st0) (t_flags st0) cinj holdj j)) 0) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_loop ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_q cx) (c_n cx) fin ->
  (forall R' hold' j',
     rholds (qval cx (Some (hd_st st0 (t_mode st0) (t_flags st0) (c_n cx) hold' j')) 0) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_lv ->
     j' = j + 8 * (c_n cx - cinj) -> 0 <= hold' < 2 ^ j' -> c_n cx - cinj < Z.of_nat k ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_top_head_loop ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD (zupd R' []) M MD) T) ->
  (forall R' hold' j',
     rholds (qval cx (Some (hd_st st0 (t_mode st0) (t_flags st0) (cinj + Z.of_nat k) hold' j')) 0) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_head_dn ->
     j' = j + 8 * Z.of_nat k -> 0 <= hold' < 2 ^ j' -> Z.of_nat k <= c_n cx - cinj ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_top_head_loop ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_HEAD_BODY (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_HEAD_LOOP (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M st0 cinj holdj j Hh Hfin CXl Hj Hk Hj0 Hc Hhj Hjc RHL Hin KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S] in CXl; destr_conj CXl.
  open_lists.
  zkeysb. unfold L_HEAD_LOOP, L_HEAD_BODY, L_LEAVE_LD in *. pose proof two64_eq as TW64.
  assert (Hj24 : 2 ^ j <= 2 ^ 23) by (apply Z.pow_le_mono_r; lia). change (2 ^ 23) with 8388608 in Hj24.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  - (* no input left: ONE RUN to the leave *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ => apply (KLV RX holdj j) end);
      [ split_lists | | | | split_lists ]; try zreg; try lia.
    all: replace (j + 8 * (n - cinj)) with j by lia; lia.
  - pose proof (Hfin cinj ltac:(lia)) as Hb0.
    pose proof (pullbyte_bound holdj j (fin cinj) ltac:(lia) Hhj Hb0) as Hpb.
    (* ONE RUN through the loop's body to its exit test; then the pulled byte's shift is said as a product *)
    zto_branch Rfd.
    rewrite ?(Z.mod_small j) by lia; rewrite ?Z.shiftl_mul_pow2 by lia.
    destruct k as [|k'].
    + (* the last round: ONE RUN to the body's continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ => apply (KDN RX (fin cinj * 2 ^ j + holdj) (j + 8)) end);
        [ split_lists | | | | split_lists ]; try zreg; try lia.
    + (* THE BACK EDGE: ONE RUN back to the loop's head, where the induction hypothesis applies *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RX ?LX) _ _) _ =>
        eapply (IH (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T RX LX M st0 (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) Hh Hfin) end);
        [ unfold ctx_lin; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S]; split_conj; assumption || lia
        | lia | lia | lia | icx_cbn; lia | lia | icx_cbn; lia
        | split_lists; zreg | exact Hin | | ].
      * (* the inner leave gives the outer leave: the same place, the model values re-said *)
        intros R' hold' j' RH' Ej' Hb' Hlt' KP'. icx_cbn. eapply (KLV R' hold' j').
        -- first [ exact RH'
                 | (open_lists; zgetl_nil; split_lists; cbv beta iota delta [zget_l alookup];
                    first [ assumption | (etransitivity; [ eassumption | lia ]) ]) ].
        -- lia.
        -- assumption.
        -- lia.
        -- first [ exact KP' | (open_lists; split_lists; zkept) ].
      * intros R' hold' j' RH' Ej' Hb' Hle' KP'. icx_cbn. eapply (KDN R' hold' j').
        -- first [ exact RH'
                 | (open_lists; zgetl_nil; split_lists; cbv beta iota delta [zget_l alookup];
                    first [ assumption | (etransitivity; [ eassumption | lia ]) ]) ].
        -- lia.
        -- assumption.
        -- lia.
        -- first [ exact KP' | (open_lists; split_lists; zkept) ].
Qed.

Lemma head_body : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = HEAD -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_HEAD (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof KM as KM0. pose proof K as KA0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof (proj1 CX) as CXl. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags] in Hm. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & H16 & _).
  clear ROM Wob Ww FRM CST HK Hmode SREST SRET SOUT Hlens Hcodes.
  zkeysb. unfold L_HEAD, L_HEAD_LOOP, L_HEAD_BODY, L_LEAVE_LD in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  (* ONE RUN to the test of the bit count *)
  zto_branch Rfd.
  destruct (Z_lt_dec 15 bits) as [Hb16 | Hb16].
  - (* enough bits in hand: ONE RUN to the body *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RX ?LX) ?MX _) _ =>
      eapply (head_main (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 RX LX MX
                (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf cin hold bits CX0 Hh Hfin eq_refl SI0) end);
      [ unfold s_regs_arm, s_fix, s_vars, hd_st; icx_cbn; zkeys; split_conj; zreg
      | split_lists; zreg
      | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
  - (* not enough bits: ONE RUN to the loop's head *)
    assert (Hkk : exists k : nat, 16 - 8 * Z.of_nat k <= bits < 24 - 8 * Z.of_nat k /\ (1 <= k <= 2)%nat).
    { exists (Z.to_nat (2 - bits / 8)).
      rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RX ?LX) ?MX _) _ =>
      eapply (head_loop k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T RX LX MX
                (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                cin hold bits Hh Hfin CXl Hk1 Hk2) end);
      [ lia | icx_cbn; lia | lia | lia | split_lists; zreg | exact Hin | | ].
    + (* the loop's leave: the leave place's statement applies as it stands *)
      intros R' hold' j' RH' Ej' Hb' Hlt' KP'. icx_cbn. open_lists. zgetl_nil. zimps. zkeys. unfold L_LEAVE_LD in *.
      pose proof (sinv_hd _ _ lf cf HEAD flags n hold' j' SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(intros _; left; reflexivity)
                    ltac:(cbn; lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia)) as SI1.
      clear H16. open_kmem KM0. destruct SAT as [Hmode SREST].
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KLL Rx Mx _ lf cf SI1) end.
      * unfold s_regs_leave_ld, hd_st; icx_cbn; zkeys; split_conj; try zreg; zkept.
      * exact STD.
      * unfold hd_st; split; [exact Hmode | exact SREST].
      * exact SRET.
      * exact SOUT.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    + (* the loop's body continuation: the main lemma applies as it stands *)
      intros R' hold' j' RH' Ej' Hb' Hle' KP'. icx_cbn. open_lists. zgetl_nil. zimps. zkeys. unfold L_HEAD_BODY in *.
      eapply (head_main (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' [] M
                (IST HEAD last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf (cin + Z.of_nat k) hold' j' CX0 Hh Hfin eq_refl SI0);
        [ unfold s_regs_arm, s_fix, s_vars, hd_st; icx_cbn; zkeys; split_conj; cbv beta iota delta [zget_l alookup]; first [zkept | lia]
        | split_lists; zkeys; cbv beta iota delta [zget_l alookup]; first [zkept | lia]
        | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
Qed.

Theorem arm_HEAD_s : arm_stmt L_HEAD HEAD.
Proof. intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K. eapply head_body; eassumption. Qed.

End WITH_ADLER_NULL.
End S_Head.

Module S_HeadB.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Check.S_HeadA.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* THE MODULE's TWO OWN LABELS ARE FIELDS OF THE IMAGE's LAYOUT TEXT; here they have their short names only *)
Local Notation L_DICTID_LOOP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_DICTID_LOOP (only parsing).
Local Notation L_DICTID_BODY := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_DICTID_BODY (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation rkeeps := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps (only parsing).
Local Notation qval := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval (only parsing).

(* OPENERS OF THE LIST FORM (they only unfold, split and name) *)
Ltac open_lists :=
  repeat match goal with
         | HH : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_dictid_body OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_dictid_loop
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_dictid_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_dictid_dn] in HH;
             unfold hd_st in HH; icx_cbn; destr_conj HH
         | HH : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_top_dictid_loop] in HH; destr_conj HH
         end.
Ltac split_lists :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_dictid_body OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_dictid_loop
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_dictid_lv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_dictid_dn
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_top_dictid_loop];
  unfold hd_st; icx_cbn; split_conj.

Section WITH_ADLER_NULL.
Context {RCa1 : RunCtx}.
Hypothesis ADLN : adler32_null_spec_s.

Lemma dictid_loop : forall (k : nat) cx fin MD T Rb l M (st0 : ist) (cinj holdj j : Z),
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_S cx ->
  32 - 8 * Z.of_nat k <= j < 40 - 8 * Z.of_nat k -> (1 <= k <= 4)%nat -> 0 <= j ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  rholds (qval cx (Some (hd_st st0 (t_mode st0) (t_flags st0) cinj holdj j)) 0) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_dictid_loop ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_q cx) (c_n cx) fin ->
  (forall R' hold' j',
     rholds (qval cx (Some (hd_st st0 (t_mode st0) (t_flags st0) (c_n cx) hold' j')) 0) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_dictid_lv ->
     j' = j + 8 * (c_n cx - cinj) -> 0 <= hold' < 2 ^ j' -> c_n cx - cinj < Z.of_nat k ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_top_dictid_loop ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD (zupd R' []) M MD) T) ->
  (forall R' hold' j',
     rholds (qval cx (Some (hd_st st0 (t_mode st0) (t_flags st0) (cinj + Z.of_nat k) hold' j')) 0) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_dictid_dn ->
     j' = j + 8 * Z.of_nat k -> 0 <= hold' < 2 ^ j' -> Z.of_nat k <= c_n cx - cinj ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_top_dictid_loop ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DICTID_BODY (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DICTID_LOOP (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M st0 cinj holdj j Hh Hfin CXl Hj Hk Hj0 Hc Hhj Hjc RHL Hin KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S] in CXl; destr_conj CXl.
  open_lists.
  zkeysb. unfold L_DICTID_LOOP, L_DICTID_BODY, L_LEAVE_LD in *. pose proof two64_eq as TW64.
  assert (Hj40 : 2 ^ j <= 2 ^ 39) by (apply Z.pow_le_mono_r; lia). change (2 ^ 39) with 549755813888 in Hj40.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  - (* no input left: ONE RUN to the leave *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ => apply (KLV RX holdj j) end);
      [ split_lists | | | | split_lists ]; try zreg; try lia.
    all: replace (j + 8 * (n - cinj)) with j by lia; lia.
  - pose proof (Hfin cinj ltac:(lia)) as Hb0.
    pose proof (pullbyte_bound holdj j (fin cinj) ltac:(lia) Hhj Hb0) as Hpb.
    (* ONE RUN through the loop's body to its exit test; then the pulled byte's shift is said as a product *)
    zto_branch Rfd.
    rewrite ?(Z.mod_small j) by lia; rewrite ?Z.shiftl_mul_pow2 by lia.
    destruct k as [|k'].
    + (* the last round: ONE RUN to the body's continuation *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ => apply (KDN RX (fin cinj * 2 ^ j + holdj) (j + 8)) end);
        [ split_lists | | | | split_lists ]; try zreg; try lia.
    + (* THE BACK EDGE: ONE RUN back to the loop's head, where the induction hypothesis applies *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RX ?LX) _ _) _ =>
        eapply (IH (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T RX LX M st0 (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) Hh Hfin) end);
        [ unfold ctx_lin; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S]; split_conj; assumption || lia
        | lia | lia | lia | icx_cbn; lia | lia | icx_cbn; lia
        | split_lists; zreg | exact Hin | | ].
      * (* the inner leave gives the outer leave: the same place, the model values re-said *)
        intros R' hold' j' RH' Ej' Hb' Hlt' KP'. icx_cbn. eapply (KLV R' hold' j').
        -- first [ exact RH'
                 | (open_lists; zgetl_nil; split_lists; cbv beta iota delta [zget_l alookup];
                    first [ assumption | (etransitivity; [ eassumption | lia ]) ]) ].
        -- lia.
        -- assumption.
        -- lia.
        -- first [ exact KP' | (open_lists; split_lists; zkept) ].
      * intros R' hold' j' RH' Ej' Hb' Hle' KP'. icx_cbn. eapply (KDN R' hold' j').
        -- first [ exact RH'
                 | (open_lists; zgetl_nil; split_lists; cbv beta iota delta [zget_l alookup];
                    first [ assumption | (etransitivity; [ eassumption | lia ]) ]) ].
        -- lia.
        -- assumption.
        -- lia.
        -- first [ exact KP' | (open_lists; split_lists; zkept) ].
Qed.

Lemma dictid_body : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DICTID -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DICTID (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof K as KA0.
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof (proj1 CX) as CXl. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags] in Hm, Hfl. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_. pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  zkeysb. unfold L_DICTID, L_DICTID_LOOP, L_DICTID_BODY, L_LEAVE_LD, L_DICT in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  (* ONE RUN to the test of the bit count *)
  zto_branch Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (BODY : forall RJ cin1 hold1 bits1,
    s_fix (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) RJ [] ->
    s_vars (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (hd_st (IST DICTID last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
             DICTID flags cin1 hold1 bits1) RJ [] ->
    rholds (qval (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
              (Some (hd_st (IST DICTID last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                           DICTID flags cin1 hold1 bits1)) 0) RJ [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_top_dictid_body ->
    cin <= cin1 <= n -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (n - cin1) + bits1 = 8 * (n - cin) + bits ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DICTID_BODY (zupd RJ []) Mc MD) T) end.
  { intros RJ cin1 hold1 bits1 RJF RJV RJH. intros.
    unfold s_fix in RJF. unfold s_vars, hd_st in RJV. icx_cbn. destr_conj RJF. destr_conj RJV. open_lists. zgetl_nil.
    unfold L_DICTID_BODY. zkeys.
    pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh1.
    pose proof (sinv_hd _ _ lf cf DICT flags cin1 0 0 SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(cbn; intros E; exfalso; exact (Hfl E))
                  ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as SI1.
    pose proof (meas_hd (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                  (IST DICTID last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                  DICT flags cin1 0 0 ltac:(left; cbn; lia)) as MB1.
    (* ONE RUN to the next arm's body *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RX ?LX) ?MX _) _ =>
      eapply (dict_body ADLN (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 RX LX MX
                (hd_st (IST DICTID last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) DICT flags cin1 0 0)
                lf cf CX0 Hh Hfin eq_refl SI1) end);
      [ (unfold hd_st; icx_cbn; zkeys; zreg) ..
      | unfold k_mem, hd_st; icx_cbn; split_conj;
        [ close_std | split; [assumption | exact SREST] | exact SRET | first [ exact I | exact SOUT ] | exact Hlens | exact Hcodes | exact HAG ]
      | eapply KALL_mono; [| exact KA0]; lia ]. }
  destruct (Z_lt_dec 31 bits) as [Hb32 | Hb32].
  - (* enough bits in hand: ONE RUN to the body *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RX _ _) _ => apply (BODY RX cin hold bits) end);
      first [ solve [unfold s_fix; icx_cbn; zkeys; split_conj; zreg]
            | solve [unfold s_vars, hd_st; icx_cbn; zkeys; split_conj; zreg]
            | solve [split_lists; zreg]
            | lia ].
  - (* not enough bits: ONE RUN to the loop's head *)
    assert (Hkk : exists k : nat, 32 - 8 * Z.of_nat k <= bits < 40 - 8 * Z.of_nat k /\ (1 <= k <= 4)%nat).
    { exists (Z.to_nat (4 - bits / 8)).
      rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RX ?LX) ?MX _) _ =>
      eapply (dictid_loop k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T RX LX MX
                (IST DICTID last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                cin hold bits Hh Hfin CXl Hk1 Hk2) end);
      [ lia | icx_cbn; lia | lia | lia | split_lists; zreg | exact Hin | | ].
    + (* the loop's leave: the leave place's statement applies as it stands *)
      intros R' hold' j' RH' Ej' Hb' Hlt' KP'. icx_cbn. open_lists. zgetl_nil. zimps. zkeys. unfold L_LEAVE_LD in *.
      pose proof (sinv_hd _ _ lf cf DICTID flags n hold' j' SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto])) ltac:(left; reflexivity) ltac:(cbn; intros E; exfalso; exact (Hfl E))
                    ltac:(cbn; lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia)) as SI1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KLL Rx Mx _ lf cf SI1) end.
      * unfold s_regs_leave_ld, hd_st; icx_cbn; zkeys; split_conj; try zreg; zkept.
      * close_std.
      * unfold hd_st; split; [exact Hmode | exact SREST].
      * exact SRET.
      * first [ exact I | exact SOUT ].
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    + (* the loop's body continuation: the body's statement applies as it stands *)
      intros R' hold' j' RH' Ej' Hb' Hle' KP'. icx_cbn. open_lists. zgetl_nil. zimps. zkeys. unfold L_DICTID_BODY in *.
      apply (BODY R' (cin + Z.of_nat k) hold' j');
        [ unfold s_fix; icx_cbn; zkeys; split_conj; cbv beta iota delta [zget_l alookup]
        | unfold s_vars, hd_st; icx_cbn; zkeys; split_conj; cbv beta iota delta [zget_l alookup]
        | split_lists; zkeys; cbv beta iota delta [zget_l alookup]
        | .. ]; try zkept; try lia.
Qed.

Theorem arm_DICTID_s : arm_stmt L_DICTID DICTID.
Proof. intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K. eapply dictid_body; eassumption. Qed.

End WITH_ADLER_NULL.
End S_HeadB.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_Stored S_LenF.

Module S_Top.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Frame OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Hoare OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.AllocSim.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9LibStmt.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.MstepsGrows.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry.S_Loop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_Ret OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAw.S_Uw OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_LeaveA OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_Leave OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_Inflate OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAw.S_U2A OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_U2B OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_U2C OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA S_ZC OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZB.S_Tok OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZB S_Head OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Check.S_HeadA S_HeadB OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Type OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Stored OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Stored.S_StoredA OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_LenX OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_Dist OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_DistX OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_LenF.S_Match OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Check.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Lemma zl_get : forall regs (r : reg), bv_eqb r 0%bv = false ->
  zget_l (zlift regs) [] (bv_key r) = bv_unsigned (getr regs r).
Proof. intros regs r Hr. cbv [zget_l alookup]. rewrite zget_zlift, (getr_reg_get regs r Hr). reflexivity. Qed.

Lemma zl_get_lit : forall regs (r : reg) k z, bv_eqb r 0%bv = false -> bv_key r = k ->
  getr regs r = Z_to_bv 64 z -> 0 <= z < two64 -> zget_l (zlift regs) [] k = z.
Proof.
  intros regs r k z Hr <- H Hz. rewrite (zl_get regs r Hr), H.
  change (Z_to_bv 64 z) with (w64 z). rewrite w64_unsigned, mod_small_u64 by exact Hz. reflexivity.
Qed.

(* a register of a tree, as a word (the tree's name is no name of the base text) *)
Lemma zd_get : forall RT (r : reg) k v, bv_eqb r 0%bv = false -> bv_key r = k -> zget RT k = v ->
  getr (zden RT) r = w64 v.
Proof. intros RT r k v Hr <- <-. apply getr_zkey. exact Hr. Qed.
Lemma zd_get_u : forall RT (r : reg) k v, bv_eqb r 0%bv = false -> bv_key r = k -> zget RT k = v -> 0 <= v < two64 ->
  bv_unsigned (getr (zden RT) r) = v.
Proof. intros RT r k v Hr Hk Hv Rv. rewrite (zd_get RT r k v Hr Hk Hv), w64_unsigned. apply mod_small_u64. exact Rv. Qed.

(* a register of the start state holds a word's value (every register: the tree is the lift of the start
   state) *)
Lemma zl_range : forall regs (r : reg), 0 <= zget_l (zlift regs) [] (bv_key r) < two64.
Proof. intros regs r. cbv [zget_l alookup]. rewrite zget_zlift, two64_eq. apply u64_range. Qed.

(* MORE BY-FORM READERS (see the first module): they write no register, no distance and no label *)

(* the range of the start state's value under a key: the key's register is found by trying each register of
   the instruction set (the numerals 5, 31 and 1 below, and the 0 at its calls: the width of a register's
   number, the last register, the step, the first register) *)
Ltac zl_range_try RG NN :=
  first [ exact (zl_range RG (Z_to_bv 5 NN))
        | lazymatch eval cbv in (NN <? 31) with
          | true => let MM := eval cbv in (NN + 1) in zl_range_try RG MM
          end ].

(* witnesses taken one by one from a list *)
Ltac ex_list LL := lazymatch LL with | ?XX :: ?TT => exists XX; ex_list TT | nil => idtac end.

(* a lemma applied to the elements of a list, one by one *)
Ltac app_list FF LL :=
  lazymatch LL with
  | ?XX :: ?TT => let F2 := open_constr:(FF XX) in app_list F2 TT
  | nil => FF
  end.

(* the range fact of the start state's value of each register of a list *)
Ltac pose_ranges RB RG LL :=
  lazymatch LL with
  | ?RR :: ?TT => pose proof (zl_range RG RR : 0 <= zget_l RB [] (bv_key RR) < two64); pose_ranges RB RG TT
  | nil => idtac
  end.

(* a goal "the registers of a list hold these values" over the end state's tree, element by element: each
   element's register is the goal's own; its value is the fact in hand about that register; an element with
   no fact in hand is the value that the goal binds *)
Ltac sregs_vals :=
  repeat (apply (f_equal2 cons);
          [ first [ (lazymatch goal with
                     | |- bv_unsigned (getr (zden ?RX) ?RG) = _ =>
                         etransitivity;
                         [ apply (zd_get_u RX RG _ _ eq_refl eq_refl); [ eassumption | first [ assumption | lia_std ] ]
                         | reflexivity ]
                     end)
                  | reflexivity ]
          | ]);
  reflexivity.

(* a goal "the registers of a list hold what they held in the start state" *)
Ltac sregs_kept GK :=
  unfold sregs, S_ENTRY5, S_ENTRY; cbn [map app];
  repeat (apply (f_equal2 cons); [ apply (f_equal bv_unsigned); zd_iface GK | ]); reflexivity.

(* a goal "the registers of a list hold the values that the token names" *)
Ltac sregs_tok :=
  match goal with
  | EsE : ?SE = _ |- sregs _ _ = ?SE => rewrite EsE
  end;
  unfold sregs, S_ENTRY5, S_ENTRY; cbn [map app]; sregs_vals.

(* the contract's layout facts and the token, opened ALL (never by the place of a part) *)
Ltac open_layout_all :=
  lazymatch goal with LAY : lib_layout_S9 _ _ _ _ _ _ |- _ => unfold lib_layout_S9 in LAY; destr_conj LAY end.
(* the fourth value that the token's register list is applied to; the list's own form says how many values
   follow it *)
Ltac tok_cin_of TT :=
  lazymatch TT with
  | tok_regs _ _ _ ?CIN => CIN
  | ?FF _ => tok_cin_of FF
  end.
Ltac open_token_all :=
  lazymatch goal with
  | TOK : zwtok_S9 _ _ _ _ _ _ _ _ |- _ =>
      unfold zwtok_S9 in TOK;
      repeat (lazymatch type of TOK with exists _, _ => destruct TOK as [? TOK] end);
      unfold tok_pure in TOK; destr_conj TOK
  end;
  (* the token's values get the names by which the proofs below speak of them: each is found by the place it
     has in a fact (never by its place in the token) *)
  lazymatch goal with
  | TM : tok_mem _ ?ST ?RV ?LF ?CF _ |- _ => rename ST into st; rename RV into rv; rename LF into lf; rename CF into cf
  end;
  match goal with
  | EW : _ = ?TT |- _ =>
      lazymatch TT with context [tok_regs] => let CIN := tok_cin_of TT in rename CIN into cin0 end
  end;
  lazymatch goal with | HC : ?COUT < t_cout _ |- _ => rename COUT into cout0 end;
  lazymatch goal with | SI : sinv (?FF ?WW ?RR) _ _ _ |- _ => rename WW into W0 end.

Lemma hold_u64 : forall hold bits, 0 <= bits -> bits <= 40 -> 0 <= hold -> hold < 2 ^ bits -> 0 <= hold < two64.
Proof.
  intros hold bits B0 B1 H0 H1. pose proof (Z.pow_le_mono_r 2 bits 40 ltac:(lia_std) B1) as P.
  change (2 ^ 40) with 1099511627776 in P. rewrite two64_eq. split; [exact H0|]. change (2 ^ 64) with 18446744073709551616. lia_std.
Qed.

(* the walk's footprint gives the contract's write set (the footprint's ranges do not wrap: said by the
   footprint's own range word, with no number of an image) *)
Lemma frame_mod_WA {RCa1 : RunCtx}  : forall mem mem' u p,
  ranges_lt (fp_u2 u p 0) ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem mem' (fp_u2 u p 0) -> mem_grows mem mem' -> frame_mod mem mem' (WA_S9 u p).
Proof.
  intros mem mem' u p HRL HP HG.
  eapply frame_mod_weaken; [| eapply (frame_mod_of_mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem mem' (fp_u2 u p 0)); [exact HRL | exact HP | exact HG]].
  intros a Ho. unfold WA_S9 in Ho. cbn [outside wranges fp_u2 Z.eqb] in *.
  destr_conj Ho. repeat split; try assumption.
  all: (unfold in_rng; lia_std).
Qed.
Lemma frame_mod_WAw {RCa1 : RunCtx}  : forall mem mem' u p (ww : word),
  ranges_lt (fp_u2 u p (bv_unsigned ww)) -> bv_unsigned ww <> 0 ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem mem' (fp_u2 u p (bv_unsigned ww)) -> mem_grows mem mem' -> frame_mod mem mem' (WA_S9 u p ++ [(ww, S9_WIN_N)]).
Proof.
  intros mem mem' u p ww HRL Hw0 HP HG.
  eapply frame_mod_weaken; [| eapply (frame_mod_of_mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem mem' (fp_u2 u p (bv_unsigned ww))); [exact HRL | exact HP | exact HG]].
  intros a Ho. unfold WA_S9 in Ho. cbn [outside wranges fp_u2 app] in *.
  destr_conj Ho. rewrite (proj2 (Z.eqb_neq _ 0) Hw0).
  repeat split; try assumption. rewrite Z_to_bv_bv_unsigned. assumption.
Qed.

Section CONTRACT.
Context {RCa1 : RunCtx}.
Hypothesis A_TABLE : arm_stmt L_TABLE TABLE.
Hypothesis A_LENLENS : arm_stmt L_LENLENS LENLENS.
Hypothesis A_CODELENS : arm_stmt L_CODELENS CODELENS.

Let A_HEAD : arm_stmt L_HEAD HEAD := arm_HEAD_s adler32_null_ok.
Let A_DICTID : arm_stmt L_DICTID DICTID := arm_DICTID_s adler32_null_ok.
Let A_DICT : arm_stmt L_DICT DICT := arm_DICT_s adler32_null_ok.
Let A_TYPE : arm_stmt L_TYPE TYPE := arm_TYPE_s.
Let A_TYPEDO : arm_stmt L_TYPEDO TYPEDO := arm_TYPEDO_s.
Let A_STORED : arm_stmt L_STORED STORED := arm_STORED_s memcpy_ok.
Let A_COPY_ : arm_stmt L_COPY_ COPY_ := arm_COPY__s memcpy_ok.
Let A_COPY : arm_stmt L_COPY COPY := arm_COPY_s memcpy_ok.
Let A_LEN_ : arm_stmt L_LEN_ LEN_ := arm_LEN_ ifast_ok.
Let A_LEN : arm_stmt L_LEN LEN := arm_LEN ifast_ok.
Let A_LENEXT : arm_stmt L_LENEXT LENEXT := arm_LENEXT.
Let A_DIST : arm_stmt L_DIST DIST := arm_DIST.
Let A_DISTEXT : arm_stmt L_DISTEXT DISTEXT := arm_DISTEXT.
Let A_MATCH : arm_stmt L_MATCH MATCH := arm_MATCH.
Let A_LIT : arm_stmt L_LIT LIT := arm_LIT.
Let A_CHECK : arm_stmt_ob L_CHECK CHECK := arm_CHECK_s adler32_ok.
Let A_LENGTH : arm_stmt L_LENGTH LENGTH := arm_LENGTH_s.


Theorem za_s : za_stmt_S9 zwtok_S9.
Proof.
  unfold za_stmt_S9. intros regs mem u pw qw n zc. intros.
  (* the contract's layout facts, opened all *)
  open_layout_all.
  cbv [S9_FRA S9_INFL_N S9_BUF S9_BUF_N S9_RO_LO S9_RO_HI S9_IMG_TOP S9_ZWD] in *. pose proof two64_eq as TW64.
  set (Rb := zlift regs).
  (* the start state's facts, read from the contract's hypotheses *)
  iface_regs Rb (zl_get regs). iface_store. iface_mem.
  set (p := bv_unsigned pw) in *. set (q := bv_unsigned qw) in *.
  assert (Ep : bv_unsigned pw = p) by reflexivity. assert (Eq : bv_unsigned qw = q) by reflexivity. clearbody p q.
  pose proof (u64_range pw) as Rp. pose proof (u64_range qw) as Rq. rewrite Ep in Rp. rewrite Eq in Rq.
  pose proof (rom_ok_of_hyp mem ltac:(assumption)) as ROM.
  destruct (mem_arr_of_readable (run_segments R_segs rc_inp rc_sp rc_mb) mem q n ltac:(lia_std) ltac:(lia_std) ltac:(lia_std) ltac:(eassumption)) as (fin & Hin & Hfin).
  (* the result set: each end place with the contract's own conclusion about it *)
  lazymatch goal with
  | |- exists rr mm pp, _ /\ _ /\ ((_ /\ @?AA rr mm) \/ (_ /\ @?BB rr mm)) =>
      set (Q := fun c : config => exists (RT : tree Z) (M' : word -> option byte),
        (c = zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE2 (zupd RT []) M' MD0 /\ AA (zden RT) M' /\
         mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem M' (fp_u2 u p 0))
        \/
        (c = zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZW (zupd RT []) M' MD0 /\ BB (zden RT) M' /\
         mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem M' (fp_u2 u p 0)))
  end.
  assert (HR : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZA (zupd Rb []) mem MD0) Q).
  { eapply za_cps with (u := u) (p := p) (q := q) (n := n) (fin := fin) (MD := MD0) (T := Q) (zc := zc).
    (* the register premises first: a register the contract speaks of holds its word; any other holds the
       value it holds (that value is the lemma's entry value) *)
    all: try (lazymatch goal with |- zget_l _ _ _ = _ => first [ eassumption | reflexivity ] end).
    all: try (lazymatch goal with |- 0 <= zget_l _ _ _ < two64 => zl_range_try regs 0 end).
    all: try first [ exact MD0_halted | assumption | exact memcpy_ok | exact adler32_ok
                   | (unfold ZSEP; cbv [STATE_SIZE ROM_LO_ALL ROMHI_S BUF]; lia_std)
                   | (cbv [FRA STATE_SIZE DATA_LO DATA_LEN]; lia_std) ].
    - (* the first end place: the contract's conclusion from the continuation's premises *)
      intros RT M'. intros. apply rz_now. subst Q. cbv beta. exists RT, M'. left.
      split; [reflexivity|]. split; [| assumption].
      split.
      + unfold end_regs_S9. split_conj; first [ zd_iface (zl_get regs) | sregs_kept (zl_get regs) ].
      + unfold end_cells_S9. split_conj; assumption.
    - (* the second end place: the registers the contract names, and the token *)
      intros RT M' cin0 cout0 W0 ra st rv lf cf. cbv zeta. intros Hra Hcin0 Hcout0 SI Hcc Hmd. intros.
      apply rz_now. subst Q. cbv beta. exists RT, M'. right.
      split; [reflexivity|]. split; [| assumption].
      split_conj; [> zd_iface (zl_get regs) .. | ].
      (* the token: the entry list's registers with their start values; the values of the callee's registers
         from the facts in hand *)
      unfold zwtok_S9.
      let LS := eval cbv [map S_ENTRY5 S_ENTRY app] in (map (fun r : reg => zget_l Rb [] (bv_key r)) S_ENTRY5) in ex_list LS.
      exists cin0, cout0, W0, ra, rv. repeat (lazymatch goal with |- @ex Z _ => eexists end). exists st, lf, cf.
      split; [| split; [| split]].
      + unfold sregs, S_ENTRY5, S_ENTRY. cbn [map app].
        repeat (apply (f_equal2 cons);
                [ lazymatch goal with |- bv_unsigned (getr ?RG ?RR) = _ => symmetry; exact (zl_get RG RR eq_refl) end | ]);
          reflexivity.
      + unfold sregs, S_ALL, tok_regs. cbn [map].
        pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _). unfold RNG, cxc in RNG_. icx_cbn.
        destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
        icx_cbn. destr_conj RNG_.
        pose proof (hold_u64 hold bits ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Rhold.
        cbv [BUF FRA STATE_SIZE] in *.
        sregs_vals.
      + unfold tok_pure.
        let LR := eval cbv [S_ENTRY5 S_ENTRY app] in S_ENTRY5 in pose_ranges Rb regs LR.
        split_conj; try assumption; try (icx_cbn; assumption); try (cbv [FRA STATE_SIZE]; lia_std);
          try (lazymatch goal with
               | |- context [bv_unsigned ?WW] =>
                   let HU := fresh "HU" in pose proof (u64_range WW) as HU; rewrite <- TW64 in HU; lia_std
               end).
      + unfold tok_mem, cxw. icx_cbn. clear ROM Hin.
        lazymatch goal with STD : s_std _ _ _ |- _ => open_std STD end.
        split_conj; first [ assumption | (match goal with HH : _ |- _ => exact HH end) ]. }
  (* the contract's conclusion from the result set *)
  dand HR as (ms' & RUN & HQ). subst Q. cbv beta in HQ. cbn [cfg_ms cfg_model zcfg] in RUN, HQ.
  unfold zst in RUN. cbn [zupd] in RUN. subst Rb. rewrite zden_zlift in RUN.
  pose proof (msteps_mem_grows (run_segments R_segs rc_inp rc_sp rc_mb) _ _ RUN) as G. cbn [ms_mem] in G.
  destruct HQ as (RT & M' & [(E & AQ & HP) | (E & BQ & HP)]);
    unfold zcfg, zst in E; injection E as E1; subst ms'; cbn [ms_mem] in G; cbn [zupd].
  - exists (zden RT), M', T_ZE2. split; [exact RUN | split].
    + apply frame_mod_WA; try assumption; unfold fp_u2; cbn [ranges_lt]; cbv [STATE_SIZE BUF] in *; lia_std.
    + left. split; [reflexivity | exact AQ].
  - exists (zden RT), M', T_ZW. split; [exact RUN | split].
    + apply frame_mod_WA; try assumption; unfold fp_u2; cbn [ranges_lt]; cbv [STATE_SIZE BUF] in *; lia_std.
    + right. split; [reflexivity | exact BQ].
Qed.


Theorem zb_s : zb_stmt_S9 zwtok_S9.
Proof.
  unfold zb_stmt_S9. intros regs mem u pw qw ww n zc sE sW. intros.
  (* the contract's layout facts and the token, opened all *)
  open_layout_all.
  cbv [S9_FRA S9_INFL_N S9_BUF S9_BUF_N S9_RO_LO S9_RO_HI S9_IMG_TOP S9_WIN_N S9_ZWD] in *. pose proof two64_eq as TW64.
  open_token_all.
  set (Rb := zlift regs).
  (* the start state's facts, read from the contract's hypotheses and from the token's list *)
  iface_regs Rb (zl_get regs). iface_store. iface_mem.
  lazymatch goal with
  | HsW : sregs regs S_ALL = sW, EsW : sW = ?TT |- _ =>
      lazymatch TT with context [tok_regs] => idtac end;
      rewrite EsW in HsW; unfold sregs, S_ALL, tok_regs in HsW; cbn [map] in HsW; injection HsW; clear HsW; intros
  end.
  iface_vals Rb (zl_get regs).
  set (p := bv_unsigned pw) in *. set (q := bv_unsigned qw) in *. set (w := bv_unsigned ww) in *.
  assert (Ep : bv_unsigned pw = p) by reflexivity. assert (Eq : bv_unsigned qw = q) by reflexivity. assert (Ew : bv_unsigned ww = w) by reflexivity.
  clearbody p q w.
  pose proof (u64_range pw) as Rp. pose proof (u64_range qw) as Rq. pose proof (u64_range ww) as Rw.
  rewrite Ep in Rp. rewrite Eq in Rq. rewrite Ew in Rw.
  pose proof (rom_ok_of_hyp mem ltac:(assumption)) as ROM.
  destruct (mem_arr_of_readable (run_segments R_segs rc_inp rc_sp rc_mb) mem q n ltac:(lia_std) ltac:(lia_std) ltac:(lia_std) ltac:(eassumption)) as (fin & Hin & Hfin).
  (* the callee's return place is one of the two call places *)
  lazymatch goal with
  | Hra : ?RAV = _ \/ ?RAV = _ |- _ =>
      assert (Hsite : exists site : bool, RAV = ra_site site)
        by (destruct Hra as [Era | Era]; rewrite Era; [exists true | exists false]; reflexivity);
      destruct Hsite as (site & Esite); subst RAV
  end.
  (* the result set: the end place with the contract's own conclusion about it *)
  lazymatch goal with
  | |- exists rr mm, _ /\ _ /\ @?AA rr mm =>
      set (Q := fun c : config => exists (RT : tree Z) (M' : word -> option byte),
        c = zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE1 (zupd RT []) M' MD0 /\ AA (zden RT) M' /\
        mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem M' (fp_u2 u p w))
  end.
  assert (HR : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZB (zupd Rb []) mem MD0) Q).
  { (* the lemma's entry values are the token's list, element by element *)
    lazymatch goal with
    | EsE : sE = ?LS |- _ =>
        let T1 := app_list open_constr:(zb_cps u p q n _ _) LS in
        eapply (T1 fin MD0 Q zc) with (w := w) (site := site) (cin0 := cin0) (cout0 := cout0) (W0 := W0) (rv := rv) (st := st) (lf := lf) (cf := cf)
    end.
    all: try (lazymatch goal with |- zget_l _ _ _ = _ => first [ eassumption | reflexivity ] end).
    all: try (lazymatch goal with |- 0 <= zget_l _ _ _ < two64 => zl_range_try regs 0 end).
    all: try first [ exact MD0_halted | assumption | exact memcpy_ok | exact adler32_ok
                   | (intros _; assumption)
                   | (unfold wok, ZSEP; cbv [WIN_SIZE STATE_SIZE BUF ROM_LO_ALL ROMHI_S]; split_conj; lia_std)
                   | (unfold ZSEP; cbv [STATE_SIZE ROM_LO_ALL ROMHI_S BUF]; lia_std)
                   | (cbv [FRA STATE_SIZE DATA_LO DATA_LEN]; lia_std) ].
    - (* the end place without a window: the window's address is not zero *)
      intros RT M'. intros. exfalso. lia_std.
    - (* the end place: the contract's conclusion from the continuation's premises *)
      intros RT M'. intros. apply rz_now. subst Q. cbv beta. exists RT, M'.
      split; [reflexivity|]. split; [| assumption].
      split.
      + unfold end_regs_S9. split_conj; first [ zd_iface (zl_get regs) | sregs_tok ].
      + unfold end_cells_S9. split_conj; assumption. }
  (* the contract's conclusion from the result set *)
  dand HR as (ms' & RUN & HQ). subst Q. cbv beta in HQ. cbn [cfg_ms cfg_model zcfg] in RUN, HQ.
  unfold zst in RUN. cbn [zupd] in RUN. subst Rb. rewrite zden_zlift in RUN.
  pose proof (msteps_mem_grows (run_segments R_segs rc_inp rc_sp rc_mb) _ _ RUN) as G. cbn [ms_mem] in G.
  dand HQ as (RT & M' & E & AQ & HP).
  unfold zcfg, zst in E; injection E as E1; subst ms'; cbn [ms_mem] in G; cbn [zupd].
  exists (zden RT), M'. split; [exact RUN | split; [| exact AQ]].
  apply frame_mod_WAw; rewrite ?Ew; try assumption;
    first [ lia | (unfold fp_u2; cbn [ranges_lt]; cbv [STATE_SIZE BUF WIN_SIZE] in *; lia_std) ].
Qed.

Theorem zb0_s : zb0_stmt_S9 zwtok_S9.
Proof.
  unfold zb0_stmt_S9. intros regs mem u pw qw n zc sE sW. intros.
  (* the contract's layout facts and the token, opened all *)
  open_layout_all.
  cbv [S9_FRA S9_INFL_N S9_BUF S9_BUF_N S9_RO_LO S9_RO_HI S9_IMG_TOP S9_WIN_N S9_ZWD] in *. pose proof two64_eq as TW64.
  open_token_all.
  set (Rb := zlift regs).
  (* the start state's facts, read from the contract's hypotheses and from the token's list *)
  iface_regs Rb (zl_get regs). iface_store. iface_mem.
  lazymatch goal with
  | HsW : sregs regs S_ALL = sW, EsW : sW = ?TT |- _ =>
      lazymatch TT with context [tok_regs] => idtac end;
      rewrite EsW in HsW; unfold sregs, S_ALL, tok_regs in HsW; cbn [map] in HsW; injection HsW; clear HsW; intros
  end.
  iface_vals Rb (zl_get regs).
  set (p := bv_unsigned pw) in *. set (q := bv_unsigned qw) in *.
  assert (Ep : bv_unsigned pw = p) by reflexivity. assert (Eq : bv_unsigned qw = q) by reflexivity.
  clearbody p q.
  pose proof (u64_range pw) as Rp. pose proof (u64_range qw) as Rq. rewrite Ep in Rp. rewrite Eq in Rq.
  pose proof (rom_ok_of_hyp mem ltac:(assumption)) as ROM.
  destruct (mem_arr_of_readable (run_segments R_segs rc_inp rc_sp rc_mb) mem q n ltac:(lia_std) ltac:(lia_std) ltac:(lia_std) ltac:(eassumption)) as (fin & Hin & Hfin).
  (* the callee's return place is one of the two call places *)
  lazymatch goal with
  | Hra : ?RAV = _ \/ ?RAV = _ |- _ =>
      assert (Hsite : exists site : bool, RAV = ra_site site)
        by (destruct Hra as [Era | Era]; rewrite Era; [exists true | exists false]; reflexivity);
      destruct Hsite as (site & Esite); subst RAV
  end.
  (* the result set: the end place with the contract's own conclusion about it *)
  lazymatch goal with
  | |- exists rr mm, _ /\ _ /\ @?AA rr mm =>
      set (Q := fun c : config => exists (RT : tree Z) (M' : word -> option byte),
        c = zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE2 (zupd RT []) M' MD0 /\ AA (zden RT) M' /\
        mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem M' (fp_u2 u p 0))
  end.
  assert (HR : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZB (zupd Rb []) mem MD0) Q).
  { (* the lemma's entry values are the token's list, element by element; there is no window *)
    lazymatch goal with
    | EsE : sE = ?LS |- _ =>
        let T1 := app_list open_constr:(zb_cps u p q n _ _) LS in
        eapply (T1 fin MD0 Q zc) with (w := 0) (site := site) (cin0 := cin0) (cout0 := cout0) (W0 := W0) (rv := rv) (st := st) (lf := lf) (cf := cf)
    end.
    all: try (lazymatch goal with |- zget_l _ _ _ = _ => first [ eassumption | reflexivity ] end).
    all: try (lazymatch goal with |- 0 <= zget_l _ _ _ < two64 => zl_range_try regs 0 end).
    all: try first [ exact MD0_halted | assumption | exact memcpy_ok | exact adler32_ok
                   | (intros CC; exfalso; exact (CC eq_refl))
                   | (apply wok0; cbv [DATA_LO DATA_LEN]; lia_std)
                   | (unfold ZSEP; cbv [STATE_SIZE ROM_LO_ALL ROMHI_S BUF]; lia_std)
                   | (cbv [FRA STATE_SIZE DATA_LO DATA_LEN]; lia_std) ].
    - (* the end place: the contract's conclusion from the continuation's premises *)
      intros RT M'. intros. apply rz_now. subst Q. cbv beta. exists RT, M'.
      split; [reflexivity|]. split; [| assumption].
      split.
      + unfold end_regs_S9. split_conj; first [ zd_iface (zl_get regs) | sregs_tok ].
      + unfold end_cells_S9. split_conj; assumption.
    - (* the end place with a window: there is none *)
      intros RT M'. intros. exfalso. match goal with HC : 0 <> 0 |- _ => exact (HC eq_refl) end. }
  (* the contract's conclusion from the result set *)
  dand HR as (ms' & RUN & HQ). subst Q. cbv beta in HQ. cbn [cfg_ms cfg_model zcfg] in RUN, HQ.
  unfold zst in RUN. cbn [zupd] in RUN. subst Rb. rewrite zden_zlift in RUN.
  pose proof (msteps_mem_grows (run_segments R_segs rc_inp rc_sp rc_mb) _ _ RUN) as G. cbn [ms_mem] in G.
  dand HQ as (RT & M' & E & AQ & HP).
  unfold zcfg, zst in E; injection E as E1; subst ms'; cbn [ms_mem] in G; cbn [zupd].
  exists (zden RT), M'. split; [exact RUN | split; [| exact AQ]].
  apply frame_mod_WA; try assumption; unfold fp_u2; cbn [ranges_lt]; cbv [STATE_SIZE BUF] in *; lia_std.
Qed.

Definition contract_S9 : zlib_u2_contract_S9 :=
  ZU2C_S9 zwtok_S9 zw_local za_s zb_s zb0_s zc_s.

End CONTRACT.
End S_Top.

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import S9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import SBase. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZB. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZB.S_Tok. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import S_GroupB. Import S_Top.

Definition zlib_contract_S9 {RCa1 : RunCtx}  : zlib_u2_contract_S9 :=
  contract_S9 (arm_TABLE_s itable_ok ifast_ok) (arm_LENLENS_s itable_ok ifast_ok) (arm_CODELENS_s itable_ok ifast_ok).
