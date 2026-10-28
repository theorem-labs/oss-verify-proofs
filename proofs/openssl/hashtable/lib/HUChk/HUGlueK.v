(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb PropExec H0Lim HUTargetPre HUWorldK HUReadBase HUTargetFull HUHandoff HUInitPcs HUFiPre HUFiFx HUFiTail.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require ConeCfg.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxKind FxMem FxExec FxRel FxHandoff FxDrive.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CxPlan CxPlanSound CxGlue HUPlanImage HUAtable H0Sinv.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrMain BrInfer.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import Spec ClaVerdict HTSpec HUCheckG HUSel HUTgtGlue.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HUChk Require Import HUBrGlue2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ehash_of (K : AX2.kentry) : AX2.expr :=
  match K with
  | AX2.KRange (AX2.EAlu ALU_ADD (AX2.EMd M_MUL (AX2.ELit (-1)) (AX2.EVar 11)) h) _ _ => h
  | _ => AX2.ELit 0
  end.

Section GlueK.
Variable HASHF0 : AX2.kentry.
Hypothesis HASHF0_shape : HASHF0 = AX2.KRange (AX2.EAlu ALU_ADD (AX2.EMd M_MUL (AX2.ELit (-1)) (AX2.EVar 11)) (ehash_of HASHF0)) 0 0.
Hypothesis HASHF0_closed : CAP.expr_vars_lt 0 (ehash_of HASHF0) = true.

Definition XBc (content : list byte) (b : nat) : list byte :=
  if Nat.eqb b 3 then skipn (Z.to_nat (6 + hdr_cfglen content)) content else [].

Definition E0c (content : list byte) : AX2.env := AX2.Env (fun _ => Z_to_bv 64 0) (XBc content).

Definition XVXc (content : list byte) (CS : CAP.acs) (x : nat) : word :=
  let nx := CAP.nxt CS in let t := tin_of content in
  if Nat.eqb x 9 then Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0)))
  else if Nat.eqb x 11 then AX2.edenot (E0c content) (ehash_of HASHF0)
  else if Nat.eqb x (nx - 3) then Z_to_bv 64 (t_calls t)
  else if Nat.eqb x (nx - 2) then Z_to_bv 64 (t_n t / 4096)
  else if Nat.eqb x (nx - 1) then Z_to_bv 64 (t_n t mod 4096)
  else Z_to_bv 64 0.

(* [comment removed for export] *)
Definition var_tag_whole (VT : vtab) (x : nat) (t : int) : bool :=
  var_is_tag VT x t
  || match vt_get VT x with
     | Some (VVal (FV t' w)) => (t' =? t)%uint63 && is_plain t' && (wZ w =? 0)
     | _ => false
     end.

Lemma var_tag_whole_sound rho xv xb VT x t : var_tag_whole VT x t = true -> AX2.ev (env_of rho xv xb VT) x = rho t.
Proof.
  unfold var_tag_whole. intros H. apply orb_prop in H as [H|H]; [exact (var_is_tag_sound rho xv xb VT x t H)|].
  rewrite ev_env_of. destruct (vt_get VT x) as [[[t' w]| |]|]; try discriminate.
  apply andb_prop in H as [H Hw]. apply andb_prop in H as [Ht Hp]. apply Uint63.eqb_spec in Ht. subst t'.
  apply Z.eqb_eq in Hw. cbn [vden].
  rewrite (fk_dv_plain rho (FV t w) (is_plain_lt60 _ Hp)). cbn [vtag vw].
  apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, Hw, Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Definition XCHKg (CS : CAP.acs) (bd : bdata) : bool :=
  let nx := CAP.nxt CS in let VT := bd_vt bd in
  Nat.leb 16 nx
  && var_is_tag VT 4 113 && var_is_tag VT 8 111 && var_tag_whole VT (nx - 4) 121
  && var_is_ext VT 9 && var_is_ext VT 11 && var_is_ext VT (nx - 3) && var_is_ext VT (nx - 2) && var_is_ext VT (nx - 1).

Lemma XBc_12 content : XBc content 1%nat = [] /\ XBc content 2%nat = [].
Proof. split; reflexivity. Qed.
Lemma XBc_3 content : XBc content 3%nat = skipn (Z.to_nat (6 + hdr_cfglen content)) content.
Proof. reflexivity. Qed.
Lemma XVXc_9 content CS : XVXc content CS 9%nat = Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0))).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma tin_cl content : t_cl (tin_of content) = hdr_cfglen content.
Proof.
  unfold tin_of, hdr_cfglen, hdr_cfg, hdr_b0, hdr_b1, config_len, cfg_word, byte_at. cbn [t_cl].
  rewrite Z2Nat.id; [reflexivity|]. apply Z.mod_pos_bound. lia.
Qed.
Lemma tin_n content : 0 <= hdr_paylen content -> t_n (tin_of content) = hdr_paylen content.
Proof.
  intros Hp. unfold tin_of. cbn [t_n]. unfold ht_payload_len, hdr_paylen in *.
  pose proof (tin_cl content) as Hc. unfold tin_of in Hc. cbn [t_cl] in Hc.
  change HDR_MIN with 6%nat. lia.
Qed.

(* [comment removed for export] *)
Lemma heok_g sp0 k buf can content VM R M envc mb B sec tdz err :
  tgt_entry_full sp0 k buf can content VM R M ->
  forall CS bd (rho' : int -> word), XCHKg CS bd = true ->
    (forall t, to_Z t < 200 -> rho' t = fi_rho sp0 can R mb B sec tdz err t) ->
    tin_ok k (tin_of content)
    /\ eokx (CAP.nxt CS - 3) (CAP.nxt CS - 4) (CAP.nxt CS - 2) (CAP.nxt CS - 1) HASHF0 (tin_of content)
            (env_of rho' (XV envc (XVXc content) CS) (XBc content) (bd_vt bd)).
Proof.
  intros TF CS bd rho' Hx Hag.
  destruct (handoff_teqs sp0 k buf can content VM R M mb B sec tdz err (Z_to_bv 64 0) (Z_to_bv 64 0) TF)
    as (E111 & _ & E113 & _ & _ & _ & Hc & Hp & Hlen & Hcap & _ & _ & _).
  pose proof (tin_cl content) as Tcl. pose proof (tin_n content Hp) as Tn.
  destruct (te_len _ _ _ _ _ _ (tf_entry _ _ _ _ _ _ _ _ TF)) as [_ HL26].
  set (t := tin_of content) in *. set (E := env_of rho' (XV envc (XVXc content) CS) (XBc content) (bd_vt bd)).
  unfold XCHKg in Hx. cbv zeta in Hx.
  apply andb_prop in Hx as [Hx Xr]. apply andb_prop in Hx as [Hx Xq]. apply andb_prop in Hx as [Hx Xk].
  apply andb_prop in Hx as [Hx X11]. apply andb_prop in Hx as [Hx X9]. apply andb_prop in Hx as [Hx Xs5].
  apply andb_prop in Hx as [Hx X8]. apply andb_prop in Hx as [Hnx X4]. apply Nat.leb_le in Hnx.
  set (nx := CAP.nxt CS) in *.
  (* [comment removed for export] *)
  assert (Hb2 : 0 <= t_b2 t <= 255).
  { unfold t, tin_of. cbn [t_b2]. unfold byte_at. pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as Hr.
    change (bv_modulus 8) with 256 in Hr. lia. }
  (* [comment removed for export] *)
  assert (Htin : tin_ok k t).
  { unfold tin_ok. rewrite Tcl, Tn. split; [exact Hp|]. split; [lia|]. split; [exact Hb2|].
    destruct TF as [_ _ (mb' & bw' & B' & brkv & mas & tid' & sec' & _ & [(-> & HL & _) | (Hk & HL & _)])].
    - unfold Llo, Lhi. cbn. lia.
    - unfold Llo, Lhi, capk in *. destruct (Z.eqb_spec k 0) as [->|Hk0]; [lia|]. lia. }
  split; [exact Htin|].
  (* [comment removed for export] *)
  assert (Eext : forall x, var_is_ext (bd_vt bd) x = true -> x <> 2%nat -> AX2.ev E x = XVXc content CS x).
  { intros x Hxe Hx2. unfold E. rewrite (var_is_ext_sound rho' _ _ _ x Hxe). unfold XV.
    destruct (Nat.eqb_spec x 2); [contradiction | reflexivity]. }
  assert (Hlit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z).
  { intros z Hz. apply Z_to_bv_small. unfold bv_modulus. exact Hz. }
  assert (Hb0 : 0 <= hdr_b0 content <= 255 /\ 0 <= hdr_b1 content <= 255).
  { unfold hdr_b0, hdr_b1. pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as H0.
    pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as H1. change (bv_modulus 8) with 256 in *. lia. }
  assert (Es5 : bv_unsigned (AX2.ev E (nx - 4)%nat)
                = if hdr_b1 content <? 128 then hdr_b1 content else hdr_b1 content - 256 + 2 ^ 64).
  { unfold E. rewrite (var_tag_whole_sound rho' _ _ _ (nx - 4)%nat 121%uint63 Xs5), (Hag 121%uint63 ltac:(cbv; reflexivity)).
    unfold fi_rho. change 121%uint63 with (T_REG 21). rewrite rho_reg by lia.
    assert (Hs5 : getr R (Z_to_bv 5 21) = Z_to_bv 64 (if hdr_b1 content <? 128 then hdr_b1 content else hdr_b1 content - 256 + 2 ^ 64))
      by exact (te_s5 _ _ _ _ _ _ (tf_entry _ _ _ _ _ _ _ _ TF)).
    rewrite Hs5.
    apply Hlit. destruct (hdr_b1 content <? 128) eqn:Eb; [apply Z.ltb_lt in Eb | apply Z.ltb_ge in Eb]; lia. }
  unfold eokx. unfold CXS.uE. cbn [AX2.edenot].
  repeat split.
  - (* [comment removed for export] *)
    unfold E. rewrite (var_is_tag_sound rho' _ _ _ 4%nat 113%uint63 X4), (Hag 113%uint63 ltac:(cbv; reflexivity)).
    unfold fi_rho. rewrite E113. symmetry. exact Tn.
  - unfold E. rewrite (var_is_tag_sound rho' _ _ _ 8%nat 111%uint63 X8), (Hag 111%uint63 ltac:(cbv; reflexivity)).
    unfold fi_rho. rewrite E111. symmetry. exact Tcl.
  - rewrite (Eext 9%nat X9 ltac:(lia)). unfold XVXc. cbn [Nat.eqb]. rewrite Hlit; [reflexivity|].
    unfold t, tin_of, byte_at in Hb2. cbn [t_b2] in Hb2. lia.
  - (* [comment removed for export] *)
    rewrite (Eext (nx - 3)%nat Xk ltac:(lia)). unfold XVXc. fold nx. fold t.
    destruct (Nat.eqb_spec (nx - 3) 9); [lia|]. destruct (Nat.eqb_spec (nx - 3) 11); [lia|].
    rewrite Nat.eqb_refl. apply Hlit. unfold t_calls. pose proof (Z.mod_pos_bound (t_b2 t) 4 ltac:(lia)).
    destruct (t_cl t =? 0); lia.
  - (* [comment removed for export] *)
    intros Hle. rewrite Es5 in Hle. unfold t, tin_of. cbn [t_cnt]. apply Z.leb_gt.
    unfold cfg_word, byte_at. fold (hdr_b0 content) (hdr_b1 content).
    destruct (hdr_b1 content <? 128) eqn:Eb; [apply Z.ltb_lt in Eb | apply Z.ltb_ge in Eb]; lia.
  - intros Hcnt. rewrite Es5. unfold t, tin_of in Hcnt. cbn [t_cnt] in Hcnt. apply Z.leb_gt in Hcnt.
    unfold cfg_word, byte_at in Hcnt. fold (hdr_b0 content) (hdr_b1 content) in Hcnt.
    destruct (hdr_b1 content <? 128) eqn:Eb; [apply Z.ltb_lt in Eb | apply Z.ltb_ge in Eb]; lia.
  - rewrite (Eext (nx - 2)%nat Xq ltac:(lia)). unfold XVXc. fold nx. fold t.
    destruct (Nat.eqb_spec (nx - 2) 9); [lia|]. destruct (Nat.eqb_spec (nx - 2) 11); [lia|].
    destruct (Nat.eqb_spec (nx - 2) (nx - 3)); [lia|]. rewrite Nat.eqb_refl. apply Hlit.
    rewrite Tn. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
  - rewrite (Eext (nx - 1)%nat Xr ltac:(lia)). unfold XVXc. fold nx. fold t.
    destruct (Nat.eqb_spec (nx - 1) 9); [lia|]. destruct (Nat.eqb_spec (nx - 1) 11); [lia|].
    destruct (Nat.eqb_spec (nx - 1) (nx - 3)); [lia|]. destruct (Nat.eqb_spec (nx - 1) (nx - 2)); [lia|].
    rewrite Nat.eqb_refl. apply Hlit. pose proof (Z.mod_pos_bound (t_n t) 4096 ltac:(lia)). lia.
  - (* [comment removed for export] *)
    rewrite HASHF0_shape. cbn [pure_holds AX2.edenot].
    assert (Eh : AX2.edenot E (ehash_of HASHF0) = AX2.ev E 11%nat).
    { rewrite (Eext 11%nat X11 ltac:(lia)). unfold XVXc. cbn [Nat.eqb].
      apply (CXS.edenot_agree' 0 E (E0c content) _); [|exact HASHF0_closed].
      split; [intros n0 Hn0; lia | reflexivity]. }
    rewrite AX2S.u_add64, AX2S.u_mul64, Eh.
    assert (Hm1 : bv_unsigned (Z_to_bv 64 (-1)) = 2 ^ 64 - 1) by reflexivity. rewrite Hm1.
    pose proof (bv_unsigned_in_range _ (AX2.ev E 11%nat)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    set (h := bv_unsigned (AX2.ev E 11%nat)) in *.
    rewrite Z.add_mod_idemp_l by lia. replace ((2 ^ 64 - 1) * h + h) with (h * 2 ^ 64) by lia.
    rewrite Z.mod_mul by lia. lia.
Qed.

(* [comment removed for export] *)
Definition XRNGf (x : nat) (lo hi : Z) : bool := false.
Definition XCHKf (k : Z) (CS : CAP.acs) (bd : bdata) (F : fstate) (L : fledger) : bool := XCHKg CS bd.
Definition PHIf (CS : CAP.acs) (E : AX2.env) : Prop := True.

Section Assembly.
Variable CSL : Z -> list CAP.acs.                                     (* [comment removed for export] *)
Variable EOKc : Z -> list byte -> CAP.acs -> AX2.env -> Prop.         (* [comment removed for export] *)
Hypothesis FAM : forall (sp0 : word) (k : Z) (content : list byte) (envc : Z) (fs0 : Fs.Fs),
  valid_sp sp0 -> 0 <= envc /\ bv_unsigned sp0 + 192 + 8 * envc < 2 ^ 47 - 32 ->
  forall CS, In CS (CSL k) -> forall (PHIb : AX2.env -> Prop) E R' FULL model,
    CXS.cs_ok HSEGS H0T LIM (SINVg PHIb sp0 (bv_unsigned sp0 + 192 + 8 * envc))
              (argHt (bv_unsigned sp0 + 192 + 8 * envc)) (bv_unsigned sp0) fs0 E CS R' FULL model ->
    EOKc k content CS E ->
    realizes_cfg ConeCfg.CFG HSEGS (mkCfg (mkst R' (Z_to_bv 64 (CAP.pc CS)) FULL (PropExec.seg_rom HSEGS)) model) (t_target_ht content fs0).
(* [comment removed for export] *)
Hypothesis HEOKc : forall k content CS E, In CS (CSL k) -> tin_ok k (tin_of content) ->
  eokx (CAP.nxt CS - 3) (CAP.nxt CS - 4) (CAP.nxt CS - 2) (CAP.nxt CS - 1) HASHF0 (tin_of content) E -> EOKc k content CS E.
(* [comment removed for export] *)
Hypothesis CHK : forall k, In k KS -> forallb (leaf_chk k (TB_std k) (CSL k) XRNGf (XCHKf k)) (tree_leaves (the_tree k FUEL)) = true.

Theorem h0_leaf_tail_k : leaf_tail_stmt t_target_ht.
Proof.
  apply (h0br_leaf_tail_std t_target_ht CSL PHIf (fun content k envc CS E => EOKc k content CS E) XVXc XBc XRNGf XCHKf CHK
           XBc_12 XBc_3 XVXc_9).
  - intros content CS x lo hi Hf. discriminate Hf.
  - intros sp0 k buf can content VM R M envc fs0 Hsp TF Henv CS HCS E R' FULL model HC HE.
    exact (FAM sp0 k content envc fs0 Hsp Henv CS HCS (PHIf CS) E R' FULL model HC HE).
  - intros; exact I.
  - intros sp0 k buf can content VM R M envc mb bw B sec tdz err TF HR CS bd F L rho' HCS Hx Hag Eteq.
    destruct (heok_g sp0 k buf can content VM R M envc mb B sec tdz err TF CS bd rho' Hx Hag) as [Htin He].
    exact (HEOKc k content CS _ HCS Htin He).
Qed.
End Assembly.
End GlueK.
