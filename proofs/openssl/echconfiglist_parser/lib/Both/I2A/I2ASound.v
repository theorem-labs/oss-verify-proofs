(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_Xpres AsStack0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxHandoff2 FxCellFrame FxRoFrame FxGeom FxGeomA I2Canon I2Mach I2Image I2Run I2RunA I2Sound.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv I2ANodeLib I2ANodeMem I2AShadow I2AArgs I2ANodeAux I2ANodeKit
  I2ANodeM I2ANodeF I2ANodeR I2ANodeSig.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Lemma inl_In : forall x l, inl x l = true -> In x l.
Proof.
  intros x l H. unfold inl in H. apply existsb_exists in H as (y & Hy & E). apply Uint63.eqb_spec in E. subst. exact Hy.
Qed.
Lemma forallb_In : forall {T} (f : T -> bool) l x, forallb f l = true -> In x l -> f x = true.
Proof. intros T f l x H Hin. rewrite forallb_forall in H. exact (H x Hin). Qed.

Section Sound.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable IMX : fimage.
  Variable A : i2aconsts.
  Variable code : itrie finstr.
  Local Abbreviation K := (ka_K A).
  Local Abbreviation IM := (im_ro IMX).
  Local Abbreviation RO := (ro_of (ka_K A)).
  Hypothesis HK : KA_ok A = true.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis HIMX : image_ok asegs IMX.
  Hypothesis HWRX : image_wr_ok IMX.
  Hypothesis Hcode : code_ok asegs code.
  Hypothesis HROC : ro_const A.
  Hypothesis HSH0 : forall m, ACONST m -> mem_inv asegs m -> sh0_facts A m.
  Hypothesis Hpfc : Forall (fun e : int * list int => trace_ok (as_TR H) (to_Z (fst e)) (map to_Z (snd e))) (ka_pfc A).
  (* [comment removed for export] *)
  Hypothesis NFSM : anode_fsmalloc_sig H IMX A.
  Hypothesis NFSF : anode_fsfree_sig H IMX A code.
  Hypothesis NSET : anode_memset_sig H IMX A.
  Hypothesis NCPY : anode_memcpy_sig H IMX A.
  Hypothesis NLEN : anode_strlen_sig H IMX A.
  Hypothesis NMAL : anode_memalign_sig H IMX A.
  Let HH : asan_rt_hyps H := proj1 HHx.

  Lemma Hnw : im_nowr IM.
  Proof. intros a sg Hf. exact (im_ro_find_seg IMX a sg Hf). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cells0x_runA : forall bp k F F' r cnt pn ci,
    fx_run IM code RO bp k F = (F', r, cnt) -> cells0x (f_mem F) pn ci -> cells0x (f_mem F') pn ci.
  Proof. intros. eapply fx_run_cellx; eassumption. Qed.

  Lemma ptr_arg_ne0 : forall M v n t off, ptr_arg M v n = Some (t, off) -> t <> 0%uint63.
  Proof.
    intros M [t [top o]] n t' off Hp. unfold ptr_arg in Hp.
    destruct ((top =? 0) && negb (t =? 0))%uint63 eqn:E; [|discriminate].
    destruct (iget t M) as [rg|]; [|discriminate].
    match type of Hp with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
    injection Hp as <- <-. rewrite andb_true_iff, negb_true_iff in E. destruct E as [_ E].
    intros E'. subst. rewrite Uint63.eqb_refl in E. discriminate.
  Qed.

  Lemma cells0x_write_byte : forall M t off s M' pn ci,
    write_byte M t off s = Some M' -> t <> 0%uint63 -> cells0x M pn ci -> cells0x M' pn ci.
  Proof.
    intros M t off s M' pn ci Hw Ht Hc. unfold write_byte in Hw. destruct (iget t M) as [rg|]; [|discriminate].
    cbv zeta in Hw.
    match type of Hw with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
    injection Hw as <-. apply cells0x_iset_other; assumption.
  Qed.

  Lemma cells0x_fill_bytes : forall fuel M t off c M' pn ci,
    fill_bytes fuel M t off c = Some M' -> t <> 0%uint63 -> cells0x M pn ci -> cells0x M' pn ci.
  Proof.
    induction fuel as [|fuel IH]; intros M t off c M' pn ci Hf Ht Hc; cbn [fill_bytes] in Hf.
    - injection Hf as <-. exact Hc.
    - destruct (write_byte M t off (SK c)) as [M1|] eqn:Hw; [|discriminate].
      eapply IH; [exact Hf | exact Ht | eapply cells0x_write_byte; eassumption].
  Qed.

  Lemma cells0x_copy_bytes : forall fuel M td od ts os M' pn ci,
    copy_bytes IM fuel M td od ts os = Some M' -> td <> 0%uint63 -> cells0x M pn ci -> cells0x M' pn ci.
  Proof.
    induction fuel as [|fuel IH]; intros M td od ts os M' pn ci Hf Ht Hc; cbn [copy_bytes] in Hf.
    - injection Hf as <-. exact Hc.
    - destruct (byte_at IM M ts os) as [b|v j|]; try discriminate.
      + destruct (write_byte M td od (SK b)) as [M1|] eqn:Hw; [|discriminate].
        eapply IH; [exact Hf | exact Ht | eapply cells0x_write_byte; eassumption].
      + destruct (write_byte M td od (SV v j)) as [M1|] eqn:Hw; [|discriminate].
        eapply IH; [exact Hf | exact Ht | eapply cells0x_write_byte; eassumption].
  Qed.

  Lemma cells0x_write_cell : forall M t off v M' pn ci,
    write_cell M t off v = Some M' -> t <> 0%uint63 -> cells0x M pn ci -> cells0x M' pn ci.
  Proof.
    intros M t off v M' pn ci Hw Ht Hc. unfold write_cell in Hw. destruct (iget t M) as [rg|]; [|discriminate].
    cbv zeta in Hw.
    match type of Hw with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
    injection Hw as <-. apply cells0x_iset_other; assumption.
  Qed.

  Lemma a_n_ne0 : forall stack st off l, call_okn K stack st = Some (off, l) -> a_n st <> 0%uint63.
  Proof.
    intros stack st off l Hc E. destruct (call_okn_inv A stack st off l Hc) as (_ & _ & _ & _ & _ & _ & H2).
    rewrite E in H2. change (to_Z 0%uint63) with 0 in H2. slia.
  Qed.
  Lemma a_n_ne0_1 : forall stack st off l, call_okn K stack st = Some (off, l) -> (a_n st + 1)%uint63 <> 0%uint63.
  Proof.
    intros stack st off l Hc E. destruct (call_okn_inv A stack st off l Hc) as (_ & _ & _ & _ & _ & H59 & H2).
    apply (f_equal to_Z) in E. rewrite Uint63.add_spec in E. change (to_Z 0%uint63) with 0 in E. change (to_Z 1%uint63) with 1 in E.
    change (to_Z two59) with (2 ^ 59) in H59. rewrite Z.mod_small in E; [slia|]. change wB with (2 ^ 63). slia.
  Qed.
  Lemma a_n_ne0_2 : forall stack st off l, call_okn K stack st = Some (off, l) -> (a_n st + 2)%uint63 <> 0%uint63.
  Proof.
    intros stack st off l Hc E. destruct (call_okn_inv A stack st off l Hc) as (_ & _ & _ & _ & _ & H59 & H2).
    apply (f_equal to_Z) in E. rewrite Uint63.add_spec in E. change (to_Z 0%uint63) with 0 in E. change (to_Z 2%uint63) with 2 in E.
    change (to_Z two59) with (2 ^ 59) in H59. rewrite Z.mod_small in E; [slia|]. change wB with (2 ^ 63). slia.
  Qed.

  (* [comment removed for export] *)
  Lemma ne0_of_errno2 : forall te off tb M M1 M2,
    drop_stack off (iremove (tb + 1)%uint63 (iremove tb M)) = Some M1 -> set_errno K te M1 = Some M2 ->
    tb <> 0%uint63 /\ (tb + 1)%uint63 <> 0%uint63.
  Proof.
    intros te off tb M M1 M2 HM1 HM2.
    destruct (drop_stack_inv _ _ _ HM1) as (rg1 & _ & ->). destruct (set_errno_inv _ _ _ _ HM2) as (rg0 & pe & H0 & _ & _ & _).
    rewrite iget_iset in H0. change ((0 =? 1)%uint63) with false in H0. cbv iota in H0.
    rewrite iget_iremove in H0. destruct (0 =? tb + 1)%uint63 eqn:E1; [discriminate|].
    rewrite iget_iremove in H0. destruct (0 =? tb)%uint63 eqn:E0; [discriminate|].
    split; intros E; rewrite E, Uint63.eqb_refl in *; discriminate.
  Qed.
  (* [comment removed for export] *)
  Lemma cells0x_anode_at : forall st st' pn ci,
    anode_at IM A st = Some st' -> cells0x (f_mem (a_F st)) pn ci -> cells0x (f_mem (a_F st')) pn ci.
  Proof.
    intros st st' pn ci Hn Hc. unfold anode_at in Hn.
    destruct (f_pc (a_F st) =? 0)%uint63; [discriminate|].
    destruct (inl (f_pc (a_F st)) (ka_malloc A)).
    { unfold anode_malloc in Hn. destruct (call_okn K (c_mstack K) st) as [[off l]|] eqn:Hco; [|discriminate].
      destruct (conc63 (FxState.rget (a_F st) 10)) as [n|]; [|discriminate].
      destruct (pop_cost 0 n 0 (a_cs st)) as [cs|]; [|discriminate].
      match type of Hn with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
      destruct (drop_stack off (f_mem (a_F st))) as [M1|] eqn:HM1; [|discriminate].
      destruct (set_errno K (a_n st + 16)%uint63 (iset (a_n st + 1)%uint63 (sh_region false (a_n st) n) (iset (a_n st) (blk_region n 4 iempty) M1))) as [M2|] eqn:HM2; [|discriminate].
      injection Hn as <-. cbn [a_F f_mem mkc].
      eapply cells0x_set_errno; [exact HM2|]. apply cells0x_iset_other; [exact (a_n_ne0_1 _ _ _ _ Hco)|].
      apply cells0x_iset_other; [exact (a_n_ne0 _ _ _ _ Hco)|].
      eapply cells0x_drop_stack; [exact HM1 | exact Hc]. }
    destruct (inl (f_pc (a_F st)) (ka_free A)).
    { destruct (conc63 (FxState.rget (a_F st) 10)).
      - unfold anode_free_null in Hn. destruct (call_okn K (c_mstack K) st) as [[off l]|] eqn:Hco; [|discriminate].
        destruct (conc63 (FxState.rget (a_F st) 10)) as [z|]; [|discriminate].
        destruct (pop_cost 1 0 0 (a_cs st)) as [cs|]; [|discriminate].
        match type of Hn with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
        destruct (drop_stack off (f_mem (a_F st))) as [M1|] eqn:HM1; [|discriminate].
        destruct (set_errno K (a_n st + 15)%uint63 M1) as [M2|] eqn:HM2; [|discriminate].
        injection Hn as <-. cbn [a_F f_mem mkc].
        eapply cells0x_set_errno; [exact HM2|]. eapply cells0x_drop_stack; [exact HM1 | exact Hc].
      - unfold anode_free in Hn. destruct (call_okn K (c_mstack K) st) as [[off l]|] eqn:Hco; [|discriminate].
        destruct (base_tag (FxState.rget (a_F st) 10)) as [tb|]; [|discriminate].
        destruct (bsize_of tb (a_blk st)) as [n|]; [|discriminate].
        destruct (iget tb (f_mem (a_F st))); [|discriminate]. destruct (iget (tb + 1)%uint63 (f_mem (a_F st))); [|discriminate].
        destruct (pop_cost 1 n 0 (a_cs st)) as [cs|]; [|discriminate].
        match type of Hn with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
        destruct (drop_stack off (iremove (tb + 1)%uint63 (iremove tb (f_mem (a_F st))))) as [M1|] eqn:HM1; [|discriminate].
        destruct (set_errno K (a_n st + 15)%uint63 M1) as [M2|] eqn:HM2; [|discriminate].
        injection Hn as <-. cbn [a_F f_mem mkc].
        destruct (ne0_of_errno2 _ _ _ _ _ _ HM1 HM2) as [Htb0 Htb1].
        eapply cells0x_set_errno; [exact HM2|]. eapply cells0x_drop_stack; [exact HM1|].
        apply cells0x_iremove_other; [exact Htb1|]. apply cells0x_iremove_other; [exact Htb0 | exact Hc]. }
    destruct (inl (f_pc (a_F st)) (ka_realloc A)).
    { unfold anode_realloc in Hn. destruct (call_okn K (c_mstack K) st) as [[off l]|] eqn:Hco; [|discriminate].
      destruct (base_tag (FxState.rget (a_F st) 10)) as [tb|]; [|discriminate].
      destruct (conc63 (FxState.rget (a_F st) 11)) as [n'|]; [|discriminate].
      destruct (bsize_of tb (a_blk st)) as [n|]; [|discriminate]. destruct (iget tb (f_mem (a_F st))) as [rgb|]; [|discriminate].
      destruct (iget (tb + 1)%uint63 (f_mem (a_F st))); [|discriminate].
      destruct (pop_cost 2 n n' (a_cs st)) as [cs|]; [|discriminate].
      match type of Hn with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
      cbv zeta in Hn.
      match type of Hn with context [drop_stack off ?M] => destruct (drop_stack off M) as [M1|] eqn:HM1; [|discriminate] end.
      destruct (set_errno K (a_n st + 16)%uint63 M1) as [M2|] eqn:HM2; [|discriminate].
      injection Hn as <-. cbn [a_F f_mem mkc].
      destruct (drop_stack_inv _ _ _ HM1) as (rg1 & _ & EM1). destruct (set_errno_inv _ _ _ _ HM2) as (rg0 & pe & H0 & _ & _ & _).
      assert (Htb01 : tb <> 0%uint63 /\ (tb + 1)%uint63 <> 0%uint63).
      { rewrite EM1 in H0. rewrite !iget_iset in H0. change ((0 =? 1)%uint63) with false in H0. cbv iota in H0.
        rewrite (eqb_neq_false 0%uint63 (a_n st + 1)%uint63) in H0 by (intros E; apply (a_n_ne0_1 _ _ _ _ Hco); symmetry; exact E).
        rewrite (eqb_neq_false 0%uint63 (a_n st)) in H0 by (intros E; apply (a_n_ne0 _ _ _ _ Hco); symmetry; exact E).
        rewrite iget_iremove in H0. destruct (0 =? tb + 1)%uint63 eqn:E1; [discriminate|].
        rewrite iget_iremove in H0. destruct (0 =? tb)%uint63 eqn:E0; [discriminate|].
        split; intros E; rewrite E, Uint63.eqb_refl in *; discriminate. }
      destruct Htb01 as [Htb0 Htb1].
      eapply cells0x_set_errno; [exact HM2|]. eapply cells0x_drop_stack; [exact HM1|].
      apply cells0x_iset_other; [exact (a_n_ne0_1 _ _ _ _ Hco)|].
      apply cells0x_iset_other; [exact (a_n_ne0 _ _ _ _ Hco)|].
      apply cells0x_iremove_other; [exact Htb1|]. apply cells0x_iremove_other; [exact Htb0 | exact Hc]. }
    destruct (f_pc (a_F st) =? ka_memalign A)%uint63.
    { unfold anode_memalign in Hn. destruct (call_okn K (c_mstack K) st) as [[off l]|] eqn:Hco; [|discriminate].
      destruct (ptr_arg (f_mem (a_F st)) (FxState.rget (a_F st) 10) 8) as [[tm offm]|] eqn:Hpa; [|discriminate].
      destruct (conc63 (FxState.rget (a_F st) 11)) as [al|]; [|discriminate].
      destruct (conc63 (FxState.rget (a_F st) 12)) as [n|]; [|discriminate].
      destruct (log2_al al) as [lg|]; [|discriminate]. destruct (pop_cost 3 al n (a_cs st)) as [cs|]; [|discriminate].
      match type of Hn with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
      destruct (drop_stack off (f_mem (a_F st))) as [M1|] eqn:HM1; [|discriminate].
      destruct (write_cell M1 tm offm (FV (a_n st) w_zero)) as [M1'|] eqn:HW; [|discriminate].
      destruct (set_errno K (a_n st + 16)%uint63 (iset (a_n st + 1)%uint63 (sh_region false (a_n st) n) (iset (a_n st) (blk_region n lg iempty) M1'))) as [M2|] eqn:HM2; [|discriminate].
      injection Hn as <-. cbn [a_F f_mem mkc].
      eapply cells0x_set_errno; [exact HM2|]. apply cells0x_iset_other; [exact (a_n_ne0_1 _ _ _ _ Hco)|].
      apply cells0x_iset_other; [exact (a_n_ne0 _ _ _ _ Hco)|].
      eapply cells0x_write_cell; [exact HW | exact (ptr_arg_ne0 _ _ _ _ _ Hpa) |].
      eapply cells0x_drop_stack; [exact HM1 | exact Hc]. }
    destruct (f_pc (a_F st) =? ka_memset A)%uint63.
    { unfold anode_memset in Hn. destruct (call_okn K (ka_istack A) st) as [[off l]|] eqn:Hco; [|discriminate].
      destruct (conc63 (FxState.rget (a_F st) 11)) as [c|]; [|discriminate]. destruct (conc63 (FxState.rget (a_F st) 12)) as [n|]; [|discriminate].
      match type of Hn with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
      destruct (ptr_arg (f_mem (a_F st)) (FxState.rget (a_F st) 10) n) as [[t o]|] eqn:Hpa; [|discriminate].
      destruct (range_okb IM A st false t o n); [|discriminate].
      destruct (drop_stack off (f_mem (a_F st))) as [M1|] eqn:HM1; [|discriminate].
      destruct (fill_bytes (Z.to_nat (to_Z n)) M1 t o (c land 255)%uint63) as [M2|] eqn:HF; [|discriminate].
      injection Hn as <-. cbn [a_F f_mem mk].
      eapply cells0x_fill_bytes; [exact HF | exact (ptr_arg_ne0 _ _ _ _ _ Hpa) |]. eapply cells0x_drop_stack; [exact HM1 | exact Hc]. }
    assert (CPY : forall stx, anode_memcpy IM A st = Some stx -> cells0x (f_mem (a_F stx)) pn ci).
    { intros stx Hm. unfold anode_memcpy in Hm. destruct (call_okn K (ka_istack A) st) as [[off l]|] eqn:Hco; [|discriminate].
      destruct (conc63 (FxState.rget (a_F st) 12)) as [n|]; [|discriminate].
      destruct (n <=? 65536)%uint63; [|discriminate].
      destruct (ptr_arg (f_mem (a_F st)) (FxState.rget (a_F st) 10) n) as [[td od]|] eqn:Hpa; [|discriminate].
      destruct (src_arg (f_mem (a_F st)) (FxState.rget (a_F st) 11) n) as [[ts os]|]; [|discriminate].
      match type of Hm with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
      destruct (drop_stack off (f_mem (a_F st))) as [M1|] eqn:HM1; [|discriminate].
      destruct (copy_bytes IM (Z.to_nat (to_Z n)) M1 td od ts os) as [M2|] eqn:HF; [|discriminate].
      injection Hm as <-. cbn [a_F f_mem mk].
      eapply cells0x_copy_bytes; [exact HF | exact (ptr_arg_ne0 _ _ _ _ _ Hpa) |]. eapply cells0x_drop_stack; [exact HM1 | exact Hc]. }
    destruct (inl (f_pc (a_F st)) (ka_memcpy A)); [exact (CPY _ Hn)|].
    destruct (f_pc (a_F st) =? ka_memmove A)%uint63; [exact (CPY _ Hn)|].
    destruct (f_pc (a_F st) =? ka_strlen A)%uint63.
    { unfold anode_strlen in Hn. destruct (call_okn K (ka_istack A) st) as [[off l]|] eqn:Hco; [|discriminate].
      destruct (src_arg (f_mem (a_F st)) (FxState.rget (a_F st) 10) 1) as [[t o]|]; [|discriminate].
      destruct (scan_strlen IM 4096 (f_mem (a_F st)) t o 0) as [len|]; [|discriminate].
      destruct (src_arg (f_mem (a_F st)) (FxState.rget (a_F st) 10) (strlen_span o len)) as [x_|]; [|discriminate].
      destruct (range_okb IM A st true t o (len + 1)%uint63); [|discriminate].
      destruct (drop_stack off (f_mem (a_F st))) as [M1|] eqn:HM1; [|discriminate].
      injection Hn as <-. cbn [a_F f_mem mk]. eapply cells0x_drop_stack; [exact HM1 | exact Hc]. }
    destruct (fsm_class (f_pc (a_F st)) (ka_fsm A)) as [k|]; [|discriminate].
    unfold anode_fsmalloc in Hn. destruct (call_okn K (ka_fstack A) st) as [[off l]|] eqn:Hco; [|discriminate].
    match type of Hn with (if ?b then _ else _) = _ => destruct b; [|discriminate] end.
    cbv zeta in Hn.
    match type of Hn with context [drop_stack off ?M] => destruct (drop_stack off M) as [M2|] eqn:HM1; [|discriminate] end.
    injection Hn as <-. cbn [a_F f_mem mk].
    eapply cells0x_drop_stack; [exact HM1|].
    apply cells0x_iset_other; [exact (a_n_ne0_1 _ _ _ _ Hco)|].
    apply cells0x_iset_other; [exact (a_n_ne0_2 _ _ _ _ Hco)|].
    apply cells0x_iset_other; [exact (a_n_ne0 _ _ _ _ Hco) | exact Hc].
  Qed.

  Lemma cells0x_anode_fsfree : forall st st' pn ci,
    anode_fsfree code st = Some st' -> cells0x (f_mem (a_F st)) pn ci -> cells0x (f_mem (a_F st')) pn ci.
  Proof.
    intros st st' pn ci Hn Hc. unfold anode_fsfree in Hn.
    destruct (iget (f_pc (a_F st)) code) as [ins|]; [|discriminate]. destruct ins; try discriminate.
    destruct (fv_alu (f_mem (a_F st)) ALU_ADD (FxState.rget (a_F st) rs1) (FV 0 imm)) as [[ft [top o]]|]; [|discriminate].
    destruct (conc63 (FxState.rget (a_F st) rs2)) as [z|]; [|discriminate].
    match type of Hn with (if ?b then _ else _) = _ => destruct b eqn:Hg; [|discriminate] end.
    injection Hn as <-. cbn [a_F f_mem mk].
    rewrite !andb_true_iff in Hg. destruct Hg as [[[[[[_ _] _] _] H3] _] _]. apply Uint63.leb_spec in H3. change (to_Z 3%uint63) with 3 in H3.
    pose proof (i63_range ft) as Hft.
    assert (E2 : to_Z (ft - 2)%uint63 = to_Z ft - 2) by (rewrite Uint63.sub_spec; change (to_Z 2%uint63) with 2; apply Z.mod_small; change wB with (2^63); slia).
    assert (E21 : to_Z (ft - 2 + 1)%uint63 = to_Z ft - 1) by (rewrite Uint63.add_spec, E2; change (to_Z 1%uint63) with 1; rewrite Z.mod_small; [slia|]; change wB with (2^63); slia).
    assert (E22 : to_Z (ft - 2 + 2)%uint63 = to_Z ft) by (rewrite Uint63.add_spec, E2; change (to_Z 2%uint63) with 2; rewrite Z.mod_small; [slia|]; change wB with (2^63); slia).
    apply cells0x_iremove_other; [intros E; apply (f_equal to_Z) in E; rewrite E22 in E; change (to_Z 0%uint63) with 0 in E; slia|].
    apply cells0x_iremove_other; [intros E; apply (f_equal to_Z) in E; rewrite E21 in E; change (to_Z 0%uint63) with 0 in E; slia|].
    apply cells0x_iremove_other; [intros E; apply (f_equal to_Z) in E; rewrite E2 in E; change (to_Z 0%uint63) with 0 in E; slia| exact Hc].
  Qed.

  (* [comment removed for export] *)
  Lemma i2a_run_step : forall fuel st,
    i2a_run IM A code (S fuel) st =
    match fx_run IM code RO no_bp 40 (a_F st) with
    | (F', r, _) =>
        let st' := awith_F st F' in
        match r with
        | SStuck c =>
            if (c =? 1)%uint63 then abindn 10 st' (anode_at IM A st') (i2a_run IM A code fuel)
            else if (c =? 2)%uint63 then (if is_final K code F' then ADone st' else ARej 2 st')
            else if (c =? 5)%uint63 then abindn 11 st' (anode_fsfree code st') (i2a_run IM A code fuel)
            else ARej (100 + c)%uint63 st'
        | SEcall => ARej 3 st'
        | SBreak => ARej 4 st'
        | SFuel => ARej 5 st'
        end
    end.
  Proof. intros. reflexivity. Qed.

  Lemma i2a_run_0 : forall st, i2a_run IM A code 0 st = ARej 90 st.
  Proof. intros. reflexivity. Qed.

  Lemma cells0x_i2a_run : forall fuel st st' pn ci,
    i2a_run IM A code fuel st = ADone st' -> cells0x (f_mem (a_F st)) pn ci -> cells0x (f_mem (a_F st')) pn ci.
  Proof.
    induction fuel as [|fuel IH]; intros st st' pn ci Hr Hc; [rewrite i2a_run_0 in Hr; discriminate|].
    rewrite i2a_run_step in Hr.
    destruct (fx_run IM code RO no_bp 40 (a_F st)) as [[F' r] cnt] eqn:Hrun. cbv zeta in Hr.
    pose proof (cells0x_runA _ _ _ _ _ _ pn ci Hrun Hc) as Hc'.
    destruct r as [| | |c]; try discriminate.
    destruct (c =? 1)%uint63.
    - unfold abindn in Hr. destruct (anode_at IM A (awith_F st F')) as [st''|] eqn:Hn; [|discriminate].
      apply (IH st'' st' pn ci Hr). exact (cells0x_anode_at _ _ pn ci Hn Hc').
    - destruct (c =? 2)%uint63.
      + destruct (is_final K code F'); [|discriminate]. injection Hr as <-. exact Hc'.
      + destruct (c =? 5)%uint63; [|discriminate].
        unfold abindn in Hr. destruct (anode_fsfree code (awith_F st F')) as [st''|] eqn:Hn; [|discriminate].
        apply (IH st'' st' pn ci Hr). exact (cells0x_anode_fsfree _ _ pn ci Hn Hc').
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma K_pcs : forall pc,
       (inl pc (ka_malloc A) = true -> to_Z pc = AMALLOC_STUB)
    /\ (inl pc (ka_free A) = true -> to_Z pc = AFREE_STUB)
    /\ (inl pc (ka_realloc A) = true -> to_Z pc = AREALLOC_STUB).
  Proof.
    intros pc. destruct (HK_parts A HK) as (_ & _ & Hp & _). unfold K_pcs_ok in Hp. rewrite !andb_true_iff in Hp.
    destruct Hp as [[[[[[[[[[Hm Hf] Hr] _] _] _] _] _] _] _] _].
    split; [| split]; intros Hi; apply inl_In in Hi.
    - pose proof (forallb_In _ _ _ Hm Hi) as E. apply Z.eqb_eq in E. exact E.
    - pose proof (forallb_In _ _ _ Hf Hi) as E. apply Z.eqb_eq in E. exact E.
    - pose proof (forallb_In _ _ _ Hr Hi) as E. apply Z.eqb_eq in E. exact E.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem i2a_run_sound : forall fuel Q st st' rho msF mo,
    i2a_run IM A code fuel st = ADone st' ->
    cells0_in A (f_mem (a_F st')) ->
    I2RA H IMX A Q st rho msF mo ->
    as_SR H (fun c' => exists rho', I2RA H IMX A Q st' rho' (cfg_ms c') (cfg_model c') /\ is_final K code (a_F st') = true)
            (mkCfg msF mo).
  Proof.
    induction fuel as [|fuel IH]; intros Q st st' rho msF mo Hr Hc0 HI; [rewrite i2a_run_0 in Hr; discriminate|].
    rewrite i2a_run_step in Hr.
    destruct (fx_run IM code RO no_bp 40 (a_F st)) as [[F' r] cnt] eqn:Hrun. cbv zeta in Hr.
    (* [comment removed for export] *)
    assert (Hc0' : cells0_in A (f_mem F')).
    { destruct r as [| | |c]; try discriminate.
      destruct (c =? 1)%uint63.
      - unfold abindn in Hr. destruct (anode_at IM A (awith_F st F')) as [st''|] eqn:Hn; [|discriminate].
        apply (cells0_in_of K (f_mem F') (f_mem (a_F st'))); [|exact Hc0].
        intros pn ci Hc. apply (cells0x_i2a_run _ _ _ pn ci Hr). exact (cells0x_anode_at _ _ pn ci Hn Hc).
      - destruct (c =? 2)%uint63.
        + destruct (is_final K code F'); [|discriminate]. injection Hr as <-. exact Hc0.
        + destruct (c =? 5)%uint63; [|discriminate].
          unfold abindn in Hr. destruct (anode_fsfree code (awith_F st F')) as [st''|] eqn:Hn; [|discriminate].
          apply (cells0_in_of K (f_mem F') (f_mem (a_F st'))); [|exact Hc0].
          intros pn ci Hc. apply (cells0x_i2a_run _ _ _ pn ci Hr). exact (cells0x_anode_fsfree _ _ pn ci Hn Hc). }
    eapply (ah_seq H HH).
    { exact (seg_sound H IMX A code Hcode HK HHx Hnw Q st rho msF mo F' r cnt Hrun HI Hc0'). }
    intros [ms1 mo1] HI1. cbn [cfg_ms cfg_model] in HI1.
    destruct r as [| | |c]; try discriminate.
    destruct (c =? 1)%uint63.
    - (* [comment removed for export] *)
      unfold abindn in Hr. destruct (anode_at IM A (awith_F st F')) as [st''|] eqn:Hn; [|discriminate].
      assert (Hnode : as_SR H (fun c' => exists rho', I2RA H IMX A Q st'' rho' (cfg_ms c') (cfg_model c')) (mkCfg ms1 mo1)).
      { unfold anode_at in Hn. cbn [a_F awith_F] in Hn.
        destruct (K_pcs (f_pc F')) as (Pm & Pf & Pr).
        destruct (f_pc F' =? 0)%uint63 eqn:E0; [discriminate|].
        destruct (inl (f_pc F') (ka_malloc A)) eqn:Em.
        { exact (anode_malloc_sound H IMX A HK HHx HIMX HWRX HSH0 Hpfc HROC Q (awith_F st F') st'' rho ms1 mo1 Hn (Pm eq_refl) Hc0' HI1). }
        destruct (inl (f_pc F') (ka_free A)) eqn:Ef.
        { destruct (conc63 (FxState.rget F' 10)).
          - exact (anode_free_null_sound H IMX A HK HHx HIMX HWRX HSH0 HROC Q (awith_F st F') st'' rho ms1 mo1 Hn (Pf eq_refl) Hc0' HI1).
          - exact (anode_free_sound H IMX A HK HHx HIMX HWRX HSH0 Hpfc HROC Q (awith_F st F') st'' rho ms1 mo1 Hn (Pf eq_refl) Hc0' HI1). }
        destruct (inl (f_pc F') (ka_realloc A)) eqn:Er.
        { exact (anode_realloc_sound H IMX A HK HHx HIMX HWRX HSH0 Hpfc HROC Q (awith_F st F') st'' rho ms1 mo1 Hn (Pr eq_refl) Hc0' HI1). }
        destruct (f_pc F' =? ka_memalign A)%uint63 eqn:Ea.
        { apply Uint63.eqb_spec in Ea. exact (NMAL Q (awith_F st F') st'' rho ms1 mo1 Hn Ea Hc0' HI1). }
        destruct (f_pc F' =? ka_memset A)%uint63 eqn:Es.
        { apply Uint63.eqb_spec in Es. exact (NSET Q (awith_F st F') st'' rho ms1 mo1 Hn Es Hc0' HI1). }
        destruct (inl (f_pc F') (ka_memcpy A)) eqn:Ec.
        { exact (NCPY Q (awith_F st F') st'' rho ms1 mo1 Hn (or_introl Ec) Hc0' HI1). }
        destruct (f_pc F' =? ka_memmove A)%uint63 eqn:Ev.
        { apply Uint63.eqb_spec in Ev. exact (NCPY Q (awith_F st F') st'' rho ms1 mo1 Hn (or_intror Ev) Hc0' HI1). }
        destruct (f_pc F' =? ka_strlen A)%uint63 eqn:El.
        { apply Uint63.eqb_spec in El. exact (NLEN Q (awith_F st F') st'' rho ms1 mo1 Hn El Hc0' HI1). }
        destruct (fsm_class (f_pc F') (ka_fsm A)) as [k|] eqn:Ek; [|discriminate].
        exact (NFSM Q (awith_F st F') st'' rho ms1 mo1 k Hn Ek Hc0' HI1). }
      eapply (ah_seq H HH); [exact Hnode|].
      intros [ms2 mo2] [rho2 HI2]. cbn [cfg_ms cfg_model] in HI2.
      exact (IH Q st'' st' rho2 ms2 mo2 Hr Hc0 HI2).
    - destruct (c =? 2)%uint63.
      + destruct (is_final K code F') eqn:Hfin; [|discriminate].
        injection Hr as <-. apply (ah_done H HH). exists rho. split; [exact HI1 | exact Hfin].
      + destruct (c =? 5)%uint63; [|discriminate].
        unfold abindn in Hr. destruct (anode_fsfree code (awith_F st F')) as [st''|] eqn:Hn; [|discriminate].
        eapply (ah_seq H HH); [exact (NFSF Q (awith_F st F') st'' rho ms1 mo1 Hn Hc0' HI1)|].
        intros [ms2 mo2] [rho2 HI2]. cbn [cfg_ms cfg_model] in HI2.
        exact (IH Q st'' st' rho2 ms2 mo2 Hr Hc0 HI2).
  Qed.
End Sound.
