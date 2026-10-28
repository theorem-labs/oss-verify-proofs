(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApParse ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface ApWalkTac ApErrKit ApErrKit2 W_err_new W_err_set_debug W_err_set_error.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition ASN1_GET_OBJECT : Z := 0xfd87c.
(* [comment removed for export] *)
Definition GETOBJ_STACK : Z := 48 + ERR_SET_ERROR_STACK.
(* [comment removed for export] *)
Definition A_ASN1_LIB_C : Z := 0x2bfe6.
Definition A_ASN1_GET_OBJECT : Z := 0x13213.

(* [comment removed for export] *)
Definition go_eff (g : go_res) : @AM bptr unit :=
  match go_err g with
  | None => aret tt
  | Some GeHdr => err_raise RS_hdr_too_long
  | Some GeTooLong => err_raise RS_too_long
  | Some GeTooSmall => aunr
  end.

(* [comment removed for export] *)
Definition go_cells_ok (sp PP PL PT PC : Z) : Prop :=
  sp <= PP /\ sp <= PL /\ sp <= PT /\ sp <= PC
  /\ PP mod 8 = 0 /\ PL mod 8 = 0 /\ PT mod 4 = 0 /\ PC mod 4 = 0
  /\ (PP + 8 <= PL \/ PL + 8 <= PP) /\ (PP + 8 <= PT \/ PT + 4 <= PP) /\ (PP + 8 <= PC \/ PC + 4 <= PP)
  /\ (PL + 8 <= PT \/ PT + 4 <= PL) /\ (PL + 8 <= PC \/ PC + 4 <= PL) /\ (PT + 4 <= PC \/ PC + 4 <= PT).

(* [comment removed for export] *)
Definition getobj_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (s : PState) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (canary : word) (m : mem) (K : list block)
    (D PP PL PT PC : Z) (g : go_res) (r : unit * ap_st bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word) (jl j2 j3 : list byte),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ ap_pre s' (snd r) m' OW' LB E bo sp lo B errv' canary 0
    /\ lx_pres LB (bv_unsigned sp) ([(PP, PP + 8); (PL, PL + 8); (PT, PT + 4); (PC, PC + 4)] ++ LIBW_AP) m m'
    /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
    /\ blocks_kept K (snd r) OW' m m'
    /\ rw_cells ctusegs m' PP [C8 (wz (D + go_p g))]
    /\ match go_err g with
       | None => a0 = wz (go_ret g)
                 /\ rw_cells ctusegs m' PL [C8 (wz (go_len g))] /\ rw_cells ctusegs m' PT [C4 (wz (go_tag g))] /\ rw_cells ctusegs m' PC [C4 (wz (go_cls g))]
       | Some GeTooLong => a0 = wz (Z.lor (go_ret g) 128)
                 /\ rw_cells ctusegs m' PL [C8 (wz (go_len g))] /\ rw_cells ctusegs m' PT [C4 (wz (go_tag g))] /\ rw_cells ctusegs m' PC [C4 (wz (go_cls g))]
       | Some _ => a0 = wz 128
                 /\ rw_cells ctusegs m' PL [CB 8 jl] /\ rw_cells ctusegs m' PT [CB 4 j2] /\ rw_cells ctusegs m' PC [CB 4 j3]
       end.

(* [comment removed for export] *)
Definition ASN1_get_object_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block)
         (D : Z) (d : list Z) (op omax PP PL PT PC : Z) (jl j2 j3 : list byte),
    ap_pre s st m OW LB E bo sp lo B errv canary GETOBJ_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_ok m LB D d -> 0 <= op -> 0 < omax -> op + omax <= zlength d ->
    go_cells_ok (bv_unsigned sp) PP PL PT PC -> PP + 8 <= B -> PL + 8 <= B -> PT + 4 <= B -> PC + 4 <= B ->
    rw_cells ctusegs m PP [C8 (wz (D + op))] -> rw_cells ctusegs m PL [CB 8 jl] -> rw_cells ctusegs m PT [CB 4 j2] -> rw_cells ctusegs m PC [CB 4 j3] ->
    a0 = wz PP -> a1 = wz PL -> a2 = wz PT -> a3 = wz PC -> a4 = wz omax ->
    implM ctusegs (interp (ap_embed (go_eff (get_object d op omax) st))) s
          (getobj_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E bo lo B canary m K D PP PL PT PC (get_object d op omax))
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz ASN1_GET_OBJECT) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Lemma land_pow2_cases : forall x k, 0 <= k -> Z.land x (2 ^ k) = 0 \/ Z.land x (2 ^ k) = 2 ^ k.
Proof.
  intros x k Hk. destruct (Z.testbit x k) eqn:T.
  - right. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec k n); [subst; rewrite T; reflexivity|apply andb_false_r].
  - left. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec k n); [subst; rewrite T; reflexivity|apply andb_false_r].
Qed.

Lemma land_32_cases : forall x, Z.land x 32 = 0 \/ Z.land x 32 = 32.
Proof. intros x. change 32 with (2 ^ 5). apply land_pow2_cases. lia. Qed.

Lemma land_192_cases : forall x, Z.land x 192 = 0 \/ Z.land x 192 = 64 \/ Z.land x 192 = 128 \/ Z.land x 192 = 192.
Proof.
  intros x. change 192 with (Z.lor (2 ^ 6) (2 ^ 7)). rewrite Z.land_lor_distr_r.
  destruct (land_pow2_cases x 6 ltac:(lia)) as [A|A]; destruct (land_pow2_cases x 7 ltac:(lia)) as [B|B]; rewrite A, B; cbn; tauto.
Qed.

Lemma go_ret_cases : forall d op omax, let g := get_object d op omax in
  go_ret g = 0 \/ go_ret g = 1 \/ go_ret g = 32 \/ go_ret g = 33.
Proof.
  intros d op omax. cbn zeta. rewrite get_object_eq.
  destruct (omax <=? 0); [cbn; tauto|]. destruct (go_hdr d op omax) as [[[tag p1] max1]|]; [|cbn; tauto].
  destruct (get_length d p1 max1) as [[[inf len] p2]|]; [|cbn; tauto].
  pose proof (land_32_cases (znth d op)) as C. unfold V_ASN1_CONSTRUCTED.
  destruct (inf && _) eqn:E; [cbn; tauto|].
  destruct (omax - (p2 - op) <? len); cbn [go_ret]; destruct C as [C|C]; rewrite C; destruct inf; cbn; tauto.
Qed.

Lemma go_cls_cases : forall d op omax, let g := get_object d op omax in
  go_cls g = 0 \/ go_cls g = 64 \/ go_cls g = 128 \/ go_cls g = 192.
Proof.
  intros d op omax. cbn zeta. rewrite get_object_eq.
  destruct (omax <=? 0); [cbn; tauto|]. destruct (go_hdr d op omax) as [[[tag p1] max1]|]; [|cbn; tauto].
  destruct (get_length d p1 max1) as [[[inf len] p2]|]; [|cbn; tauto].
  destruct (inf && _) eqn:E; [cbn; tauto|].
  destruct (omax - (p2 - op) <? len); cbn [go_cls]; apply land_192_cases.
Qed.

(* [comment removed for export] *)
Lemma tag_loop_len : forall fuel d len p max len' p' max',
  0 <= len <= INT_MAX / 128 -> tag_loop fuel d len p max = Some (len', p', max') -> 0 <= len' <= INT_MAX / 128.
Proof.
  induction fuel as [|f IH]; intros d len p max len' p' max' Hl H; cbn -[Z.shiftl Z.lor Z.land Z.ltb Z.div Z.eqb Z.sub INT_MAX] in H; [discriminate|].
  destruct (Z.land (znth d p) 128 =? 0); [inversion H; subst; exact Hl|].
  destruct (max - 1 =? 0); [discriminate|]. destruct (Z.ltb_spec (INT_MAX / 128) (Z.lor (Z.shiftl len 7) (Z.land (znth d p) 127))) as [C|C]; [discriminate|].
  eapply IH; [|exact H]. split; [|exact C]. apply Z.lor_nonneg. split; [apply Z.shiftl_nonneg; lia|apply Z.land_nonneg; right; lia].
Qed.

Lemma lor_le_add : forall a b, 0 <= a -> 0 <= b -> Z.lor a b <= a + b.
Proof. intros a b Ha Hb. pose proof (Z.add_lor_land a b). pose proof (Z.land_nonneg a b). lia. Qed.

Lemma go_tag_range : forall d op omax, let g := get_object d op omax in 0 <= go_tag g <= INT_MAX.
Proof.
  intros d op omax. cbn zeta. rewrite get_object_eq. unfold INT_MAX.
  destruct (omax <=? 0); [cbn; lia|]. destruct (go_hdr d op omax) as [[[tag p1] max1]|] eqn:EH; [|cbn; lia].
  assert (T : 0 <= tag <= 2147483647).
  { unfold go_hdr in EH. destruct (Z.land (znth d op) 31 =? 31).
    - destruct (omax - 1 =? 0); [discriminate|]. destruct (tag_loop _ d 0 (op + 1) (omax - 1)) as [[[len q] mx]|] eqn:ET; [|discriminate].
      assert (L0 : 0 <= 0 <= INT_MAX / 128) by (unfold INT_MAX; cbn; lia).
      pose proof (tag_loop_len _ _ _ _ _ _ _ _ L0 ET) as L. unfold INT_MAX in L. cbn in L.
      destruct (mx - 1 =? 0); [discriminate|]. inversion EH; subst.
      assert (B1 : 0 <= Z.land (znth d q) 127 <= 127).
      { split; [apply Z.land_nonneg; right; lia|]. set (v := znth d q). change 127 with (Z.ones 7) at 1. rewrite Z.land_ones by lia. change (2 ^ 7) with 128. pose proof (Z.mod_pos_bound v 128). lia. }
      assert (S1 : 0 <= Z.shiftl len 7 <= 16777215 * 128) by (rewrite Z.shiftl_mul_pow2 by lia; cbn; lia).
      split; [apply Z.lor_nonneg; lia|]. pose proof (lor_le_add (Z.shiftl len 7) (Z.land (znth d q) 127) ltac:(lia) ltac:(lia)). lia.
    - destruct (omax - 1 =? 0); [discriminate|]. inversion EH; subst.
      split; [apply Z.land_nonneg; right; lia|]. set (v := znth d op). change 31 with (Z.ones 5) at 1. rewrite Z.land_ones by lia. change (2 ^ 5) with 32. pose proof (Z.mod_pos_bound v 32). lia. }
  destruct (get_length d p1 max1) as [[[inf len] p2]|]; [|cbn; lia].
  destruct (inf && _); [cbn; lia|]. destruct (omax - (p2 - op) <? len); cbn [go_tag]; exact T.
Qed.
End WithCeiling0.
