(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV CtrPre GlueA FrameV CtrFrame CtrNoDelta CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require RtCells. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_annot. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_annot. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require KnownA.
Unset Nia Cache. Unset Nra Cache.

Ltac zl := unfold two64, two63, bv_modulus in *; change (2 ^ Z.of_N 64) with 18446744073709551616 in *; lia.

Notation al8_spec := CallA.al8_spec (only parsing).
Notation mod64_mod8 := CallA.mod64_mod8 (only parsing).
Notation al8_sv_sound := CallA.al8_sv_sound (only parsing).

Lemma mid_hi_sound : forall E fs k mid h, facts_hold E fs -> mid_hi fs k mid = Some h ->
  bv_unsigned (ev E k) mod 8 = 0 -> bv_unsigned (ev E k) < 2 ^ 62 ->
  bv_unsigned (ev E k) <= bv_unsigned (den E mid)
  /\ (bv_unsigned (den E mid) - bv_unsigned (ev E k)) mod 8 = 0
  /\ bv_unsigned (den E h) = (bv_unsigned (den E mid) - bv_unsigned (ev E k)) / 8.
Proof.
  intros E fs k mid h HF H K8 K62. unfold mid_hi in H.
  destruct mid as [|n o|op a xs| | | | | | | |]; try discriminate H.
  2:{
      destruct op; try discriminate H. destruct a as [|k' z| | | | | | | | |]; try discriminate H.
      destruct (PrimInt63.eqb k' k && weqb z wzero && div8x fs xs && KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) && nowrap_kb fs k SYMCAPw) eqn:C; [|discriminate H].
      injection H as <-.
      apply andb_prop in C as [C NWK]. apply andb_prop in C as [C XS]. apply andb_prop in C as [C D8]. apply andb_prop in C as [EK EZ].
      apply Uint63.eqb_correct in EK. subst k'. apply weqb_eq in EZ. subst z.
      pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF XS) as X8. replace (bv_unsigned (den E (VL SYMCAPw))) with 65536 in X8 by (vm_compute; reflexivity).
      destruct (ValP.nowrap_kb_sound E _ HF k _ NWK) as [RK8 _]. replace (w2Zs SYMCAPw) with 65536 in RK8 by (vm_compute; reflexivity).
      pose proof (CallA.div8x_holds E fs xs HF D8) as X0.
      pose proof (bv_unsigned_in_range 64 (den E xs)) as RX. unfold bv_modulus in RX. change (2 ^ Z.of_N 64) with (2 ^ 64) in RX.
      pose proof (bv_unsigned_in_range 64 (ev E k)) as RK0. unfold bv_modulus in RK0. change (2 ^ Z.of_N 64) with (2 ^ 64) in RK0.
      rewrite CallA.den_add_vp0. unfold two64 in *. rewrite Z.mod_small by lia.
      replace (bv_unsigned (ev E k) + bv_unsigned (den E xs) - bv_unsigned (ev E k)) with (bv_unsigned (den E xs)) by lia.
      split; [lia|]. split; [exact X0|]. rewrite (CallA.twin_len_den E xs) by lia. clear - X0. Z.div_mod_to_equations. lia. }
  pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. unfold bv_modulus in RK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RK.
  destruct (PrimInt63.eqb n k) eqn:NK.
  - apply Uint63.eqb_correct in NK. subst n. destruct (al8 o) eqn:A8; [|discriminate H]. injection H as <-.
    destruct (al8_spec o A8) as (T & ZS & M). pose proof (int_range (wl o)) as RO. rewrite two63_eq in RO.
    assert (DM : bv_unsigned (den E (VP k o)) = bv_unsigned (ev E k) + to_Z (wl o)).
    { rewrite (ValP.den_VP E k o), ZS. unfold two64. apply Z.mod_small. lia. }
    rewrite DM. split; [lia|]. replace (bv_unsigned (ev E k) + to_Z (wl o) - bv_unsigned (ev E k)) with (to_Z (wl o)) by lia.
    split; [exact M|]. rewrite HeapCtr.den_wlit. unfold ALib.Mem.wa. rewrite lsr_spec. change (to_Z 3%uint63) with 3. change (2 ^ 3) with 8.
    apply Z_to_bv_small. clear - RO. unfold two64, two63, bv_modulus in *. change (2 ^ Z.of_N 64) with 18446744073709551616. Z.div_mod_to_equations. lia.
  - destruct (find_lb_to fs n k) as [o2|] eqn:LB; [|discriminate H].
    destruct (al8 o && al8 o2 && PrimInt63.leb 3%uint63 (find_align fs n) && nowrap_kb fs n o && nowrap_kb fs k o2) eqn:C; [|discriminate H].
    injection H as <-.
    apply andb_prop in C as [C NW2]. apply andb_prop in C as [C NWo]. apply andb_prop in C as [C AL]. apply andb_prop in C as [A8 A82].
    destruct (al8_spec o A8) as (T & ZS & M). destruct (al8_spec o2 A82) as (T2 & ZS2 & M2).
    destruct (ValP.nowrap_kb_sound E _ HF n o NWo) as [RA DA]. destruct (ValP.nowrap_kb_sound E _ HF k o2 NW2) as [R2 D2].
    pose proof (CallA.find_lb_to_holds E fs n k o2 HF LB) as L. rewrite D2 in L.
    pose proof (ValP.find_align_le E fs HF n 3%uint63 AL) as AN. change (2 ^ to_Z 3%uint63) with 8 in AN.
    rewrite ZS in RA, DA. rewrite ZS2 in L, R2.
    pose proof (int_range (wl o)) as RO. pose proof (int_range (wl o2)) as RO2. unfold two64 in *.
    rewrite DA. split; [lia|]. split.
    + rewrite Zminus_mod, Z.add_mod, AN, M, K8 by lia. reflexivity.
    + unfold vec_hi. cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, bv_sub_unsigned.
      replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
      replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      change (bv_add (ev E n) (wbv o)) with (den E (VP n o)). rewrite DA.
      change (bv_add (ev E k) (wbv wzero)) with (den E (VP k wzero)). rewrite (HeapCtr.den_VPz E k).
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      rewrite Z.mod_small by lia. reflexivity.
Qed.

Definition annot_rsh (h' : sv) : region := Region 0%uint63 h' false BGZero IMap.empty.
Definition annot_post (st1 : sstate) (r sh : int) (h' : sv) : sstate :=
  let st2 := setregs (clobber st1) (IMap.add sh (annot_rsh h') (IMap.remove sh (s_regs st1))) in
  setpc (setr (snd (fresh st2)) X10 (VP (fst (fresh st2)) wzero)) r.
Lemma annotate_apply_shape : forall st sts, annotate_apply st = Some sts ->
  exists r hargs wnl st1 k sh rsh len om h',
    acall_pre ANNOT_ROOM None st = Some (r, hargs, wnl, st1)
    /\ getr st X10 = VP k wzero
    /\ IMap.find sh (s_regs st) = Some rsh /\ CtrA.win_lookup wnl sh = Some (len, K_TWIN)
    /\ mid_hi (s_facts st) k (getr st X13) = Some h'
    /\ mid_hi (s_facts st) k om = Some (rg_hi rsh)
    /\ PrimInt63.eqb sh 0%uint63 = false
    /\ PrimInt63.leb 3%uint63 (find_align (s_facts st) k) = true
    /\ block_of_twin (s_facts st) sh = Some k
    /\ twin_small (s_facts st) len = true
    /\ rg_w rsh = false /\ rg_lo rsh = 0%uint63 /\ rg_cells rsh = IMap.Leaf /\ rg_bg rsh = BGZero
    /\ KnownT.KnownT.known_eq_t (s_facts st) (getr st X12) om = true
    /\ KnownT.KnownT.known_leu_t (s_facts st) (getr st X13) (getr st X11) = true
    /\ KnownT.KnownT.known_leu_t (s_facts st) (getr st X12) (getr st X11) = true
    /\ al8_sv (s_facts st) (getr st X11) = true
    /\ annot_end_ok (s_facts st) k len (getr st X11) = true
    /\ no_views_on (s_facts st) (s_regs st) k sh = true
    /\ annot_tails_ok st wnl k sh = true
    /\ annot_others_ok st wnl k sh len = true
    /\ sts = [annot_post st1 r sh h'].
Proof.
  intros st sts H. unfold annotate_apply in H.
  destruct (acall_pre ANNOT_ROOM None st) as [[[[r hargs] wnl] st1]|] eqn:PRE; [|discriminate].
  destruct (getr st X10) as [|k zb| | | | | | | | |] eqn:X10E; try discriminate.
  destruct (find_twin (s_facts st) k) as [sh|] eqn:FT; [|discriminate].
  destruct (IMap.find sh (s_regs st)) as [rsh|] eqn:Frs; [|discriminate].
  destruct (CtrA.win_lookup wnl sh) as [[len kd]|] eqn:WL; [|discriminate].
  destruct (hi_mid k (rg_hi rsh)) as [om|] eqn:HM; [|discriminate].
  destruct (mid_hi (s_facts st) k (getr st X13)) as [h'|] eqn:MH; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end.
  apply andb_prop in C as [C OTHERS]. apply andb_prop in C as [C TAILS]. apply andb_prop in C as [C NV]. apply andb_prop in C as [C ENDIN]. apply andb_prop in C as [C AL8].
  apply andb_prop in C as [C OLE]. apply andb_prop in C as [C NLE]. apply andb_prop in C as [C KEQ]. apply andb_prop in C as [C REV].
  apply andb_prop in C as [C CB]. apply andb_prop in C as [C LO0]. apply andb_prop in C as [C RO]. apply andb_prop in C as [C TSM].
  apply andb_prop in C as [C BT]. apply andb_prop in C as [C AL]. apply andb_prop in C as [C SHNZ].
  apply andb_prop in C as [ZB KD].
  apply weqb_eq in ZB. subst zb. apply weqb_eq in KD. subst kd. apply negb_true_iff in SHNZ. apply negb_true_iff in RO.
  apply Uint63.eqb_correct in LO0.
  destruct (block_of_twin (s_facts st) sh) as [kb|] eqn:BTE; [|discriminate BT]. apply Uint63.eqb_correct in BT. subst kb.
  destruct (mid_hi (s_facts st) k om) as [hO|] eqn:MHO; [|discriminate REV]. apply sv_eqb_eq in REV. subst hO.
  assert (CB' : rg_cells rsh = IMap.Leaf /\ rg_bg rsh = BGZero).
  { destruct (rg_cells rsh); [| discriminate CB]. destruct (rg_bg rsh); try discriminate CB. split; reflexivity. }
  exists r, hargs, wnl, st1, k, sh, rsh, len, om, h'.
  repeat (split; [first [reflexivity | assumption | exact (proj1 CB') | exact (proj2 CB')]|]).
  unfold annot_post, annot_rsh. cbv zeta in H |- *.
  destruct (fresh (setregs (clobber st1) (IMap.add sh (Region 0%uint63 h' false BGZero IMap.empty) (IMap.remove sh (s_regs st1))))) as [v st3] eqn:F.
  injection H as <-. reflexivity.
Qed.

Lemma blk_win_pos_inv : forall st wnl x, blk_win_pos st wnl x = true ->
  exists n, CtrA.win_lookup wnl x = Some (n, CtrLib.K_BLOCK) /\ KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) n = true.
Proof.
  intros st wnl x H. unfold blk_win_pos in H. destruct (CtrA.win_lookup wnl x) as [[n kd]|]; [|discriminate H].
  apply andb_prop in H as [KD P]. apply weqb_eq in KD. subst kd. exists n. split; [reflexivity| exact P].
Qed.
Lemma blk_reg_w_inv : forall st x, blk_reg_w st x = true ->
  exists r, IMap.find x (s_regs st) = Some r /\ rg_w r = true /\ rg_lo r = 0%uint63 /\ KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (rg_hi r) = true.
Proof.
  intros st x H. unfold blk_reg_w in H. destruct (IMap.find x (s_regs st)) as [r|]; [|discriminate H].
  apply andb_prop in H as [H P]. apply andb_prop in H as [W L0]. apply Uint63.eqb_correct in L0. exists r. auto.
Qed.
Lemma existsb_eqb_In : forall (x : int) l, existsb (PrimInt63.eqb x) l = true -> In x l.
Proof. intros x l H. apply existsb_exists in H as (y & Hy & Q). apply Uint63.eqb_correct in Q. subst y. exact Hy. Qed.
Lemma annot_others_inv : forall st wnl k sh len k0 len0 kd0,
  annot_others_ok st wnl k sh len = true -> In (k0, len0, kd0) wnl -> k0 <> sh ->
  (kd0 <> K_TWIN /\ wt kd0 = false /\ to_Z (wl kd0) <= 8)
  \/ (kd0 = K_TWIN
      /\ ((exists l0 wlen, len = VL wlen /\ len0 = VL l0 /\ l0 <> wlen)
          \/ exists k2, block_of_twin (s_facts st) k0 = Some k2 /\ k2 <> k /\ PrimInt63.leb 3%uint63 (find_align (s_facts st) k2) = true
               /\ ((In k (carg_vecs st) /\ In k2 (carg_vecs st))
                   \/ (In k (carg_vecs st) /\ blk_win_pos st wnl k2 = true)
                   \/ (blk_win_pos st wnl k = true /\ In k2 (carg_vecs st))
                   \/ (blk_reg_w st k = true /\ blk_reg_w st k2 = true)))).
Proof.
  intros st wnl k sh len k0 len0 kd0 H Hin NS. unfold annot_others_ok in H. cbv zeta in H.
  pose proof (proj1 (forallb_forall _ _) H _ Hin) as C. cbv beta iota in C. unfold annot_other_ok in C.
  replace (PrimInt63.eqb k0 sh) with false in C by (symmetry; apply Uint63.eqb_false_spec; exact NS).
  destruct (weqb kd0 K_TWIN) eqn:KD.
  - apply weqb_eq in KD. subst kd0. right. split; [reflexivity|].
    apply orb_prop in C as [C|C].
    + left. destruct len0 as [l0| | | | | | | | | |]; try discriminate C. destruct len as [wlen| | | | | | | | | |]; try discriminate C.
      exists l0, wlen. split; [reflexivity|]. split; [reflexivity|]. intros ->.
      rewrite (proj2 (weqb_ok _ _) eq_refl) in C. discriminate C.
    + right. destruct (block_of_twin (s_facts st) k0) as [k2|]; [|discriminate C]. exists k2. split; [reflexivity|].
      apply andb_prop in C as [C EV]. apply andb_prop in C as [NE AL]. apply negb_true_iff in NE. apply Uint63.eqb_false_spec in NE.
      split; [exact NE|]. split; [exact AL|].
      apply orb_prop in EV as [EV|EV]; [apply orb_prop in EV as [EV|EV]; [apply orb_prop in EV as [EV|EV]|]|]; apply andb_prop in EV as [E1 E2].
      * left. split; [exact (existsb_eqb_In _ _ E1)| exact (existsb_eqb_In _ _ E2)].
      * right; left. split; [exact (existsb_eqb_In _ _ E1)| exact E2].
      * right; right; left. split; [exact E1| exact (existsb_eqb_In _ _ E2)].
      * right; right; right. split; assumption.
  - left. cbn [orb] in C. apply andb_prop in C as [T L]. apply negb_true_iff in T. apply Uint63.leb_spec in L. change (to_Z 8%uint63) with 8 in L.
    split; [intros ->; rewrite (proj2 (weqb_ok _ _) eq_refl) in KD; discriminate KD|]. split; assumption.
Qed.

Section Annot.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.cov1 HEAP_ID args z.

Hypothesis Cw_vec_unowned : forall md ca LB ws m i a, cw_holds Cw md ca LB ws m -> In i (VECS md) -> nth_error ca i = Some a -> bv_unsigned a <> 0 ->
  forall w, In w ws -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned a.

Hypothesis Cw_vecs_distinct : forall md ca LB ws m i j a b, cw_holds Cw md ca LB ws m -> In i (VECS md) -> In j (VECS md) -> i <> j ->
  nth_error ca i = Some a -> nth_error ca j = Some b -> bv_unsigned a <> 0 -> bv_unsigned b <> 0 -> bv_unsigned a <> bv_unsigned b.

Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.

Lemma KT9 : w2Z K_TWIN = 9. Proof. reflexivity. Qed.

Section POST.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok asegs OPS E st ms mo.
Variables (wnl : list (int * sv * w64)) (nn : nat) (rest : list sv) (LB : blocks) (aw : word).
Hypothesis NW : CtrA.nonstack_windows nn rest = Some wnl.
Hypothesis WF : windows_wf (wins_of E nn rest) LB (ATOP + 4096).
Variable WW : wit.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis TI : ties WW (wins_of E nn rest).

Variables (k sh : int) (rsh : region) (tlen : sv) (om h' : sv).
Hypothesis Frs : IMap.find sh (s_regs st) = Some rsh.
Hypothesis WLt : CtrA.win_lookup wnl sh = Some (tlen, K_TWIN).
Hypothesis MHN : mid_hi (s_facts st) k (getr st X13) = Some h'.
Hypothesis MHO : mid_hi (s_facts st) k om = Some (rg_hi rsh).
Hypothesis SHNZ : PrimInt63.eqb sh 0%uint63 = false.
Hypothesis ALK : PrimInt63.leb 3%uint63 (find_align (s_facts st) k) = true.
Hypothesis BT : block_of_twin (s_facts st) sh = Some k.
Hypothesis WMAX : bv_unsigned (den E tlen) <= 8064.
Hypothesis KEQ : KnownT.KnownT.known_eq_t (s_facts st) (getr st X12) om = true.
Hypothesis NLE : KnownT.KnownT.known_leu_t (s_facts st) (getr st X13) (getr st X11) = true.
Hypothesis OLE : KnownT.KnownT.known_leu_t (s_facts st) (getr st X12) (getr st X11) = true.
Hypothesis AL8E : al8_sv (s_facts st) (getr st X11) = true.
Hypothesis ENDIN : annot_end_ok (s_facts st) k tlen (getr st X11) = true.
Hypothesis X10E : getr st X10 = VP k wzero.
Hypothesis LO0 : rg_lo rsh = 0%uint63.
Hypothesis CELLS : rg_cells rsh = IMap.Leaf.
Hypothesis BG : rg_bg rsh = BGZero.

Let m : amem := ms_mem ms.
Let K : Z := bv_unsigned (ev E k).
Let WL : Z := bv_unsigned (den E tlen).
Let HF : facts_hold E (s_facts st) := so_facts _ _ _ _ _ _ HS.
Let HWw : aw_holds_w AI ACCT UNIV WW aw LB m mo := proj1 AR.

Lemma twin_data : exists p n,
  In (HB p K n) (w_T WW) /\ bv_unsigned (ev E sh) = shad K /\ WL = shlen (n + 7) /\ 1 <= n <= 64512 /\ K mod 16 = 0
  /\ ablk K (K + n) /\ K + n <= ATOP /\ In (shad K, shlen (n + 7)) LB /\ In (Win (shad K) (shlen (n + 7)) K_TWINz) (wins_of E nn rest).
Proof.
  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl sh tlen K_TWIN NW (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as (_ & _ & _ & INW).
  rewrite KT9 in INW. pose proof TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV).
  unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as ESA ESL.
  destruct (twin_T_facts AI ACCT UNIV WW aw LB m mo b HWw HbT) as (HbL & _ & _ & HTW & (p & EB) & NB & A16 & UB & _).
  pose proof HWw as (AH & _).
  destruct (heap_block_facts AI _ _ _ _ _ b AH HbL ltac:(exists p; rewrite EB; reflexivity)) as (_ & (BK & _ & HI & _) & _).
  pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  fold WL in ESL.
  pose proof (CallA.block_of_twin_sound E _ sh k HF BT) as LINK. fold K in LINK.
  pose proof (ValP.find_align_le E _ HF k 3%uint63 ALK) as K8. change (2 ^ to_Z 3%uint63) with 8 in K8. fold K in K8.
  pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. fold K in RK. unfold bv_modulus in RK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RK.
  rewrite Z.mod_small in LINK by (clear - RK; Z.div_mod_to_equations; lia).
  assert (EK : K = ab_addr b).
  { rewrite LINK in ESA. unfold shad, ASHOFF in ESA. rewrite Z.shiftr_div_pow2 in ESA by lia. change (2 ^ 3) with 8 in ESA.
    clear - ESA K8 A16 BK. Z.div_mod_to_equations. lia. }
  assert (NPR : ab_size b <= 64512).
  { unfold shlen in ESL. rewrite Z.shiftr_div_pow2 in ESL by lia. change (2 ^ 3) with 8 in ESL. clear - ESL WMAX NB. unfold WL in ESL. Z.div_mod_to_equations. lia. }
  exists p, (ab_size b). rewrite EK.
  split; [rewrite <- EB; exact HbT|]. split; [rewrite <- EK, LINK; unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; lia|].
  split; [exact ESL|]. split; [lia|]. split; [exact A16|]. split; [unfold ablk, AIMG_HI, KLS; exact BK|]. split; [exact HI|].
  split; [exact HTW|]. fold WL in INW. rewrite ESA, ESL in INW. exact INW.
Qed.

Let Oz : Z := bv_unsigned (den E (getr st X12)).
Let Nz : Z := bv_unsigned (den E (getr st X13)).
Let Ez : Z := bv_unsigned (den E (getr st X11)).

Lemma mids : K mod 8 = 0 /\ K < 2 ^ 47
  /\ K <= Oz <= Ez /\ K <= Nz <= Ez /\ Ez <= K + 8 * WL
  /\ (Oz - K) mod 8 = 0 /\ (Nz - K) mod 8 = 0 /\ Ez mod 8 = 0
  /\ hiZ E rsh = (Oz - K) / 8 /\ bv_unsigned (den E h') = (Nz - K) / 8.
Proof.
  destruct twin_data as (p & n & _ & _ & _ & NB & A16 & BK & HI & _). pose proof atop_range as ATR.
  assert (K8 : K mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
  assert (K47 : K < 2 ^ 47) by lia.
  destruct (mid_hi_sound E _ k om (rg_hi rsh) HF MHO K8 ltac:(fold K; lia)) as (O1 & O2 & O3).
  destruct (mid_hi_sound E _ k (getr st X13) h' HF MHN K8 ltac:(fold K; lia)) as (N1 & N2 & N3).
  pose proof (KnownA.KnownA.known_eq_sound E _ _ _ HF KEQ) as EO. rewrite <- EO in O1, O2, O3. fold K Oz in O1, O2, O3. fold K Nz in N1, N2, N3.
  pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF NLE) as NE. pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF OLE) as OE. fold Nz Ez in NE. fold Oz Ez in OE.
  pose proof (al8_sv_sound E _ _ HF AL8E) as E8. fold Ez in E8.
  pose proof (CallA.annot_end_ok_sound E _ k tlen _ HF ENDIN K8 E8 WMAX K47) as EI. fold K Ez WL in EI.
  repeat (split; [first [assumption | lia]|]). exact N3.
Qed.

Lemma old_zero : forall g, 0 <= g < hiZ E rsh -> rb asegs m (shad K + g) = Some (Z_to_bv 8 0).
Proof.
  intros g Hg. pose proof (so_reg _ _ _ _ _ _ HS sh rsh Frs) as RO0. destruct twin_data as (p & n & _ & ESH & _).
  pose proof (ro_bg _ _ _ _ _ _ RO0 g) as BGc. unfold bg_byte in BGc. rewrite BG, ESH in BGc. apply BGc.
  - intros _. unfold loZ. rewrite LO0. change (keyZ 0%uint63) with 0. lia.
  - intros X. rewrite SHNZ in X. discriminate X.
  - intros g0 gr _ F. rewrite CELLS in F. discriminate F.
Qed.

Variables (r : int) (st1 : sstate).
Hypothesis CP : call_pre st = Some r.
Hypothesis FS : forget_stack_below_sp_g st = Some st1.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis RO : rg_w rsh = false.
Hypothesis NV : no_views_on (s_facts st) (s_regs st) k sh = true.
Hypothesis TAILS : annot_tails_ok st wnl k sh = true.
Hypothesis OTHERS : annot_others_ok st wnl k sh tlen = true.
Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m.
Hypothesis AWden : aw = den E A.
Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Let lo : Z := CtrPre.sp_lo E st.
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis Hksp : okey offs = Some ksp.
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Hypothesis K16 : keyZ ksp mod 16 = 0.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis LOB : ATOP + 4096 <= lo.
Hypothesis LOS : lo <= sp.
Hypothesis SP47 : sp < 2 ^ 47.
Variables (R' : bvmap 5 word) (m' : amem) (mo' : Model).
Hypothesis KEPT : forall rg, In rg CtrFrame.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg.
Hypothesis MINV' : ALib.Mem.mem_inv asegs m'.
Hypothesis STK' : stk asegs m' lo sp.
Hypothesis MU : munch [(lo, sp); (shad K, shad K + WL)] m m'.
Hypothesis WM : wmono asegs m m'.

Hypothesis ZERO : forall g, 0 <= g < bv_unsigned (den E h') -> rb asegs m' (shad K + g) = Some (Z_to_bv 8 0).
Hypothesis AC' : ACCT aw (w_L WW) (w_RNG WW) (w_st WW) (w_LBa WW) mo'.
Hypothesis OTH : OTHER mo mo'.
Hypothesis MINVo : op_minv OPS mo'.

Let TWv : iv := (shad K, WL).
Let AWH : aw_holds_asan AI ACCT UNIV aw LB m mo := aw_real_holds AI ACCT UNIV _ _ _ _ _ AR.

Lemma twin_geo : 0x800bde00 <= shad K /\ shad K + WL <= shad ATOP /\ 1 <= WL /\ In TWv LB
  /\ In (Win (shad K) WL K_TWINz) (wins_of E nn rest).
Proof.
  destruct twin_data as (p & n & _ & _ & EWL & NB & _ & BK & HI & INL & INW). rewrite <- EWL in INL, INW.
  destruct (shadow_tight _ _ BK HI ltac:(lia)) as [S1 S2]. rewrite <- EWL in S2.
  assert (W1 : 1 <= WL). { rewrite EWL. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - NB. Z.div_mod_to_equations. lia. }
  auto.
Qed.
Lemma shad_atop_lt : shad ATOP < ATOP /\ shad ATOP <= 0x10007fff8000.
Proof. pose proof atop_range as ATR. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; Z.div_mod_to_equations; lia. Qed.

Lemma raw_out : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < sp) -> ~ (shad K <= a < shad K + WL) -> m' (ALib.Mem.wa a) = m (ALib.Mem.wa a).
Proof.
  intros a Ha N1 N2. apply MU. cbn [ALib.Frame.outside]. unfold ALib.Mem.wa. rewrite Z_to_bv_small by (clear - Ha; zl).
  split; [exact N1|]. split; [exact N2| exact I].
Qed.
Lemma raw_view : forall a, m' (ALib.Mem.wa a) = m (ALib.Mem.wa a) -> rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true).
Proof.
  intros a EQ. split; [unfold rb; unfold ALib.Mem.wa in EQ; rewrite EQ; reflexivity|].
  intros Wb. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in Wb. rewrite (wview_ext1 m' m _ EQ). exact Wb.
Qed.

Lemma twin_mapped' : forall i, 0 <= i < WL -> m' (ALib.Mem.wa (shad K + i)) <> None.
Proof.
  intros i Hi. destruct twin_geo as (S1 & S2 & _ & INL & _). pose proof shad_atop_lt as [SAL SAH]. pose proof atop_range as ATR.
  destruct (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB m mo TWv (shad K + i) AWH INL ltac:(unfold in_iv, TWv; cbn [fst snd]; lia)) as [MP SEG].
  pose proof (WM (ALib.Mem.wa (shad K + i))) as W0. unfold wview in W0. unfold ALib.Mem.wa in *.
  destruct (m (Z_to_bv 64 (shad K + i))) as [b0|] eqn:Q; [| contradiction].
  specialize (W0 ltac:(discriminate)).
  destruct (m' (Z_to_bv 64 (shad K + i))) as [b1|]; [discriminate|]. exfalso. apply W0.
  rewrite Z_to_bv_small by (clear - S1 S2 Hi SAL ATR; zl). rewrite SEG. reflexivity.
Qed.

Definition Wm : wit := mkWit (w_L WW) (w_RNG WW) (w_st WW) (w_LBa WW) (w_T WW) (w_FA WW) m' (w_zc WW).
Lemma WORLD' : aw_realW AI ACCT UNIV aw LB m' mo' Wm.
Proof.
  destruct twin_data as (p & n & HbT & _ & EWL & NB & _).
  assert (AR1 : aw_realW AI ACCT UNIV aw LB m' mo (set_ms WW m')).
  { apply (aw_real_twin_write AI IMGX IMGX_aci ACCT UNIV AI_fake aw LB m mo WW p K n m' lo sp AR HbT (is_primary_le n ltac:(lia)) LOB LOS ltac:(lia)).
    - rewrite <- EWL. exact MU.
    - exact WM.
    - rewrite <- EWL. exact twin_mapped'. }
  destruct (aw_realW_AHEAP AI ACCT UNIV _ _ _ _ _ AR1) as (AH1 & _).
  exact (aw_real_nodelta AI ACCT UNIV AI_fake aw aw LB m' mo (set_ms WW m') (w_RNG WW) (w_st WW) m' mo' AR1 AH1 AC'
           (fun _ _ _ _ _ => eq_refl) (fun _ _ _ _ _ _ _ => eq_refl)).
Qed.
Lemma TIES' : ties Wm (wins_of E nn rest).
Proof. apply (ties_ext WW Wm); [reflexivity| intros b; reflexivity| reflexivity| exact TI| intros b _ V; exact V| intros P; exact P]. Qed.

Let Fv : Z -> word := CtrFree.cfvF R'.
Let Gv : Z -> Z -> byte := fun _ _ => Z_to_bv 8 0.
Notation E' := (CtrFrame.E' E st Fv Gv).
Let FOK : fresh_ok st = true := proj1 (HeapCtr.call_pre_inv st r CP).

Lemma twin_in_heap_ws : forall a, shad K <= a < shad K + WL -> in_ws (heap_ws (wins_of E nn rest)) a.
Proof.
  intros a Ha. destruct twin_geo as (_ & _ & _ & _ & INW). unfold in_ws, heap_ws. apply in_ivs_In. exists (shad K, WL).
  split; [| unfold in_iv; cbn [fst snd]; lia].
  apply in_map_iff. exists (Win (shad K) WL K_TWINz). split; [reflexivity|]. apply filter_In. split; [exact INW| reflexivity].
Qed.
Lemma user_below : forall a, in_user LB a -> 0 <= a < ATOP.
Proof.
  intros a U. pose proof atop_range as ATR. destruct (LB_band AI ACCT UNIV AI_fake WW aw LB m mo a HWw U) as [B|[B|B]]; unfold AIMG_HI, KLS in *; lia.
Qed.

Lemma DECN : decode (map (den E') hargs) = Some (w2Z md, den E A, wins_of E nn rest, map (den E) (skipn (3 * nn) rest)).
Proof. exact (CtrFrame.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln). Qed.
Lemma HOLDN : op_holds OPS HEAP_ID (map (den E') hargs) m' mo'.
Proof.
  rewrite OPS_holds1. exists (w2Z md), aw, (wins_of E nn rest), (map (den E) (skipn (3 * nn) rest)), LB, Wm.
  split; [rewrite AWden; exact DECN|]. split; [exact (proj1 WORLD')|]. split; [exact WF|]. split; [| exact TIES'].
  apply (cw_frame Cw _ _ _ _ m m' HC). intros a Ha U NWS. symmetry. pose proof (user_below a U) as UB. pose proof atop_range as ATR.
  apply (raw_out a); [unfold two64 in Ha; lia| lia|]. intros X. exact (NWS (twin_in_heap_ws a X)).
Qed.

Definition LBk : blocks := remove iv_eq_dec TWv LB.
Lemma LBk_In : forall v, In v LBk <-> (In v LB /\ v <> TWv).
Proof. intros v. unfold LBk. split; [intros H; apply in_remove in H; exact H| intros [H N]; apply in_in_remove; assumption]. Qed.
Lemma LBk_sub : forall v, In v LBk -> In v LB.
Proof. intros v H. exact (proj1 (proj1 (LBk_In v) H)). Qed.
Lemma LBk_apart : forall a, in_user LBk a -> ~ (shad K <= a < shad K + WL).
Proof.
  intros a U X. apply in_ivs_In in U as (v & Hv & Hin). apply LBk_In in Hv as [Hv NE]. destruct twin_geo as (_ & _ & _ & INL & _).
  destruct v as [Av nv]. destruct (Z.eq_dec Av (shad K)) as [->|NA].
  - apply NE. unfold TWv. f_equal. exact (LB_same_addr AI ACCT UNIV AI_fake WW aw LB m mo _ _ _ HWw Hv INL).
  - apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB m mo (Av, nv) TWv a AWH Hv INL); [cbn [fst TWv]; exact NA| exact Hin|].
    unfold in_iv, TWv. cbn [fst snd]. lia.
Qed.
Lemma out_low : forall a, 0 <= a < 0x800bde00 -> m' (ALib.Mem.wa a) = m (ALib.Mem.wa a).
Proof. intros a Ha. destruct twin_geo as (S1 & _). pose proof atop_range as ATR. apply raw_out; lia. Qed.
Lemma SBVa : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LBk a ->
  rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true).
Proof.
  intros a Ha ST. apply raw_view. destruct twin_geo as (S1 & S2 & _). pose proof shad_atop_lt as [SAL SAH]. pose proof atop_range as ATR.
  destruct ST as [ST|[(iv0 & Hi & RRa)|U]].
  - fold sp in ST. apply raw_out; [exact Ha| lia| lia].
  - pose proof (AI_aci_img AI iv0 Hi) as HIa. pose proof (AI_aci_lo AI iv0 Hi) as LOa. unfold AIMG_HI in HIa. apply out_low. lia.
  - assert (UL : in_user LB a).
    { apply in_ivs_In in U as (v & Hv & Hin). apply in_ivs_In. exists v. split; [exact (LBk_sub v Hv)| exact Hin]. }
    pose proof (user_below a UL) as UB. apply raw_out; [exact Ha| lia| exact (LBk_apart a U)].
Qed.
Lemma shad_mono_facts : forall a', 0 <= a' < 2 ^ 47 -> (a' < AIMG_HI -> shad a' < 0x800bde00) /\ (ATOP <= a' -> shad ATOP <= shad a') /\ 0 <= shad a' < 0x10007fff8000.
Proof.
  intros a' Ha. pose proof atop_range as ATR. unfold shad, ASHOFF, AIMG_HI. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  repeat split; intros; Z.div_mod_to_equations; lia.
Qed.
Lemma SBOa : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E') (op_args o))) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
  destruct twin_geo as (S1 & S2 & _). pose proof shad_atop_lt as [SAL SAH]. pose proof atop_range as ATR.
  assert (ACI : forall x, in_ranges (aci AI) x -> 0 <= x < AIMG_HI).
  { intros x (iv0 & Hi & RRa). pose proof (AI_aci_img AI iv0 Hi). pose proof (AI_aci_lo AI iv0 Hi). lia. }
  change (Z_to_bv 64 a) with (ALib.Mem.wa a).
  destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
  - pose proof (ACI a INA) as B. unfold AIMG_HI in B. apply out_low. lia.
  - pose proof (ACI a' INA) as B. destruct (shad_mono_facts a' ltac:(unfold AIMG_HI in B; lia)) as (F1 & _ & F3). apply out_low. specialize (F1 (proj2 B)). lia.
  - destruct (shad_mono_facts a' ltac:(lia)) as (_ & F2 & F3). specialize (F2 (proj1 STK)). apply raw_out; [unfold two64 in Ha; lia| lia| lia].
Qed.
Lemma WBMa : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
  wb asegs m a = true -> wb asegs m' a = true.
Proof. intros a _ _ Wb. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in Wb. exact (WM _ Wb). Qed.
Lemma SBTa : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
  rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true).
Proof.
  intros a Ha SC _. apply raw_view. destruct twin_geo as (S1 & S2 & _). pose proof shad_atop_lt as [SAL SAH]. pose proof atop_range as ATR.
  destruct (sh_cov_band a SC) as [B|B]; [apply out_low; lia| apply raw_out; [exact Ha| lia| lia]].
Qed.

Lemma link_den : forall k0 k2, block_of_twin (s_facts st) k0 = Some k2 -> bv_unsigned (ev E k0) = bv_unsigned (ev E k2) / 8 + 0x7fff8000.
Proof.
  intros k0 k2 B2. rewrite (CallA.block_of_twin_sound E _ k0 k2 HF B2). apply Z.mod_small.
  pose proof (bv_unsigned_in_range 64 (ev E k2)) as R2. unfold bv_modulus in R2. change (2 ^ Z.of_N 64) with (2 ^ 64) in R2. clear - R2. Z.div_mod_to_equations. lia.
Qed.
Lemma K_facts : K mod 8 = 0 /\ 6483968 <= K < 2 ^ 47 /\ k <> 0%uint63.
Proof.
  destruct twin_data as (p & n & _ & _ & _ & NB & A16 & BK & HI & _). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  split; [clear - A16; Z.div_mod_to_equations; lia|]. split; [lia|]. intros ->. unfold K in BK.
  rewrite (so_zero _ _ _ _ _ _ HS) in BK. rewrite Z_to_bv_unsigned in BK. change (bv_wrap 64 0) with 0 in BK. lia.
Qed.

Lemma other_block_ne : forall k2, k2 <> k ->
  ((In k (carg_vecs st) /\ In k2 (carg_vecs st)) \/ (In k (carg_vecs st) /\ blk_win_pos st wnl k2 = true)
   \/ (blk_win_pos st wnl k = true /\ In k2 (carg_vecs st)) \/ (blk_reg_w st k = true /\ blk_reg_w st k2 = true)) ->
  bv_unsigned (ev E k2) <> K.
Proof.
  intros k2 NE EV. destruct K_facts as (K8 & KB & KNZ).
  assert (WINB : forall x n, CtrA.win_lookup wnl x = Some (n, CtrLib.K_BLOCK) -> KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) n = true ->
            exists w, In w (wins_of E nn rest) /\ w_kind w = K_BLOCK /\ 0 < w_len w /\ w_lo w = bv_unsigned (ev E x)).
  { intros x n WLx P. destruct (HeapCtrB.nonstack_windows_In E nn rest wnl x n CtrLib.K_BLOCK NW (HeapCtrB.win_lookup_In _ _ _ _ WLx)) as (_ & _ & _ & INx).
    pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF P) as P0. replace (bv_unsigned (den E (VL wzero))) with 0 in P0 by (vm_compute; reflexivity).
    eexists. split; [exact INx|]. cbn [w_kind w_len w_lo]. auto. }
  assert (Hf' : find_op HEAP_ID (s_ops st) = Some (VL md :: A :: VL nw :: rest)) by (rewrite <- Eh; exact Hf).
  destruct EV as [[CV1 CV2]|[[CV BW]|[[BW CV]|[RW1 RW2]]]].
  - destruct (Z.eq_dec (bv_unsigned (ev E k2)) 0) as [Z0|NZ0]; [lia|].
    destruct (CallA.carg_vecs_spec st md A nw rest k Hf' CV1) as (i & Hi & NEi). destruct (CallA.carg_vecs_spec st md A nw rest k2 Hf' CV2) as (j & Hj & NEj).
    rewrite <- Nn in NEi, NEj.
    assert (IJ : i <> j) by (intros ->; rewrite NEi in NEj; injection NEj as X; exact (NE (eq_sym X))).
    pose proof (Cw_vecs_distinct _ _ _ _ _ i j (den E (VP k wzero)) (den E (VP k2 wzero)) HC Hi Hj IJ (map_nth_error (den E) _ _ NEi) (map_nth_error (den E) _ _ NEj)) as X.
    rewrite !HeapCtr.den_VPz in X. fold K in X. intros EQ. apply X; [lia| exact NZ0| symmetry; exact EQ].
  - destruct (blk_win_pos_inv _ _ _ BW) as (n2 & WL2 & P2). destruct (WINB k2 n2 WL2 P2) as (w & Hw & KW & PW & LOW).
    pose proof (CtrFree.cvu_of Cw Cw_vec_unowned E st m LB nn md A nw rest Hf' Nn HC k CV ltac:(fold K; lia) w Hw KW PW) as X. fold K in X. lia.
  - destruct (blk_win_pos_inv _ _ _ BW) as (n1 & WL1 & P1). destruct (WINB k n1 WL1 P1) as (w & Hw & KW & PW & LOW). fold K in LOW.
    destruct (Z.eq_dec (bv_unsigned (ev E k2)) 0) as [Z0|NZ0]; [lia|].
    pose proof (CtrFree.cvu_of Cw Cw_vec_unowned E st m LB nn md A nw rest Hf' Nn HC k2 CV NZ0 w Hw KW PW) as X. lia.
  - destruct (blk_reg_w_inv _ _ RW1) as (r1 & F1 & W1 & L1 & P1). destruct (blk_reg_w_inv _ _ RW2) as (r2 & F2 & W2 & L2 & P2).
    destruct (Uint63.eqb k2 0%uint63) eqn:Q2.
    { apply Uint63.eqb_correct in Q2. subst k2. rewrite (so_zero _ _ _ _ _ _ HS), Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. lia. }
    intros EQ.
    pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF P1) as H1. pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF P2) as H2.
    replace (bv_unsigned (den E (VL wzero))) with 0 in H1, H2 by (vm_compute; reflexivity). fold (hiZ E r1) in H1. fold (hiZ E r2) in H2.
    assert (LZ : forall r0, rg_lo r0 = 0%uint63 -> loZ r0 = 0) by (intros r0 L; unfold loZ; rewrite L; reflexivity).
    apply (so_disj _ _ _ _ _ _ HS k r1 k2 r2 F1 F2 (fun X => NE (eq_sym X)) ltac:(apply Uint63.eqb_false_spec; exact KNZ) Q2 (or_introl W1) K).
    fold K. rewrite EQ, (LZ r1 L1), (LZ r2 L2). lia.
Qed.

Definition KEEPa (k0 : int) : Prop := k0 <> sh.
Lemma others_apart : forall k0 len kd a, KEEPa k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> ~ (shad K <= a < shad K + WL).
Proof.
  intros k0 len kd a KP WL0 Ha X. pose proof (HeapCtrB.win_lookup_In _ _ _ _ WL0) as Hin.
  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k0 len kd NW Hin) as (_ & _ & KD & INW0).
  destruct twin_geo as (S1 & S2 & W1 & INL & INWT). destruct twin_data as (p & n & HbT & ESH & EWL & NB & A16 & BK & HI & _).
  pose proof TI as (_ & T2 & _ & T4 & T5 & _ & _ & _ & _ & GA & _). pose proof HWw as (AH & _).
  set (w0 := Win (bv_unsigned (ev E k0)) (bv_unsigned (den E len)) (w2Z kd)) in *. set (wT := Win (shad K) WL K_TWINz) in *.
  assert (IN0 : in_iv (w_iv w0) a) by (unfold in_iv, w_iv, w0; cbn [w_lo w_len fst snd]; lia).
  assert (INT : in_iv (w_iv wT) a) by (unfold in_iv, w_iv, wT; cbn [w_lo w_len fst snd]; lia).
  destruct (twin_T_facts AI ACCT UNIV WW aw LB m mo _ HWw HbT) as (HbL & _). cbn [ab_addr ab_size] in *.

  assert (HULL : forall b' n', (In b' (w_T WW) \/ visf WW b') -> b' <> HB p K n -> n' <= ab_size b' + 7 ->
            shad (ab_addr b') <= a < shad (ab_addr b') + shlen n' -> False).
  { intros b' n' HB' NEb LEn Hb'a. destruct (LB_shadow_hull AI ACCT UNIV AI_fake WW aw LB m mo b' HWw HB') as (H1 & H2 & H3 & H4).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB p K n) b' AH HbL H1 (fun Q => NEb (eq_sym Q))) as D. cbn [ab_addr ab_size] in D.
    assert (SL : shlen n' <= shlen (ab_size b' + 7)).
    { unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. apply Z.div_le_mono; lia. }
    apply (gran_disj K n (ab_addr b') (ab_size b') a); [unfold ablk, AIMG_HI in BK; lia| exact H2| lia| lia| exact D| clear - A16; Z.div_mod_to_equations; lia| exact H4| rewrite <- EWL; exact X| lia]. }
  destruct (annot_others_inv st wnl k sh tlen k0 len kd OTHERS Hin KP) as [(NKT & WTk & LEk)|(-> & EV)].
  -
    assert (KZ : w2Z kd = to_Z (wl kd)) by (unfold w2Z; rewrite WTk; lia). pose proof (int_range (wl kd)) as RK0.
    assert (CASES : w2Z kd = K_BLOCK \/ (K_SUB <= w2Z kd < K_GHOST) \/ w2Z kd = K_FRAMEz \/ w2Z kd = K_FTWINz) by (unfold K_BLOCK, K_SUB, K_GHOST, K_FRAMEz, K_FTWINz; lia).
    destruct CASES as [C1|[C2|[C7|C8]]].
    + exact (GA wT w0 INWT INW0 ltac:(cbn; unfold K_GHOST, K_TWINz; lia) C1 a INT IN0).
    + exact (Cw_sub_ghost _ _ _ _ _ w0 wT a HC INW0 INWT C2 ltac:(cbn; unfold K_GHOST, K_TWINz; lia) IN0 INT).
    + destruct (T4 w0 INW0 C7) as (b' & Vb' & EIV). unfold w_iv, user_iv, w0 in EIV. cbn [w_lo w_len] in EIV. injection EIV as EA EL.
      destruct (LB_user_facts AI ACCT UNIV AI_fake WW aw LB m mo b' HWw (proj1 Vb')) as (_ & B1 & _). pose proof (usz_le b') as UL.
      pose proof shad_atop_lt as [SAL SAH]. pose proof atop_range as ATR. lia.
    + destruct (T5 w0 INW0 C8) as (b' & Vb' & EIV). unfold w_iv, fsh_iv, w0 in EIV. cbn [w_lo w_len] in EIV. injection EIV as EA EL.
      apply (HULL b' (ab_size b') (or_intror Vb')); [intros ->; exact (heap_not_fake (HB p K n) ltac:(exists p; reflexivity) (proj2 Vb'))| lia| lia].
  -
    rewrite KT9 in *. destruct (T2 w0 INW0 eq_refl) as (b0 & Hb0 & EIV). unfold w_iv, twin_iv, w0 in EIV. cbn [w_lo w_len] in EIV. injection EIV as EA EL.
    apply (HULL b0 (ab_size b0 + 7) (or_introl Hb0)); [| lia| lia].
    intros ->. cbn [ab_addr ab_size] in EA, EL.
    destruct EV as [(l0 & wlen & ELEN & -> & NEl)|(k2 & B2 & NE2 & AL2 & EV2)].
    + apply NEl. apply w2Z_inj. cbn [den] in EL. rewrite wbv_unsigned in EL. rewrite EL, <- EWL. unfold WL. rewrite ELEN. cbn [den]. rewrite wbv_unsigned. reflexivity.
    + pose proof (other_block_ne k2 NE2 EV2) as NEK. pose proof (link_den k0 k2 B2) as LK.
      pose proof (ValP.find_align_le E _ HF k2 3%uint63 AL2) as A8. change (2 ^ to_Z 3%uint63) with 8 in A8.
      destruct K_facts as (K8 & _). rewrite EA in LK. unfold shad, ASHOFF in LK. rewrite Z.shiftr_div_pow2 in LK by lia. change (2 ^ 3) with 8 in LK.
      clear - LK A8 K8 NEK. Z.div_mod_to_equations. lia.
Qed.
Lemma WINKa : forall k0 len kd, KEEPa k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LBk a.
Proof.
  intros k0 len kd KP WL0 a Ha. pose proof (others_apart k0 len kd a KP WL0 Ha) as AP0.
  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k0 len kd NW (HeapCtrB.win_lookup_In _ _ _ _ WL0)) as (_ & _ & KD & INW).
  assert (NT : forall b, In b LB -> in_iv b a -> In b LBk).
  { intros b Hb Hin. apply LBk_In. split; [exact Hb|]. intros ->. unfold in_iv, TWv in Hin. cbn [fst snd] in Hin. exact (AP0 Hin). }
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
  - exfalso. exact (KD KS0).
  - apply in_ivs_In. eexists. split; [apply (NT _ B); unfold in_iv; cbn [fst snd]; lia| unfold in_iv; cbn [fst snd]; lia].
  - apply in_ivs_In. exists b. assert (Hin : in_iv b a) by (apply SUB; unfold in_iv; cbn [fst snd]; lia). split; [exact (NT b Hb Hin)| exact Hin].
Qed.
Lemma VKEEPa : forall k0 rg hs n sh' len, IMap.find k0 (s_regs st) = Some rg -> zero_view rg = Some hs -> KEEPa k0 ->
  block_of_twin (s_facts st) k0 = Some n -> CallV.view_parent (s_facts st) (s_regs st) n sh' ->
  CtrA.win_lookup wnl sh' = Some (len, K_TWIN) -> KEEPa sh'.
Proof.
  intros k0 rg hs n sh' len Fk ZV NKs BT0 VPAR WL0. intros ->. unfold no_views_on in NV.
  pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) NV k0 rg Fk) as C. cbv beta in C.
  replace (PrimInt63.eqb k0 sh) with false in C by (symmetry; apply Uint63.eqb_false_spec; exact NKs).
  rewrite ZV, BT0 in C. destruct VPAR as [(kb & o1 & UB & TW)|(rshp & Frshp & HNp)];
      [rewrite UB, TW, Uint63.eqb_refl in C; cbn in C; discriminate C| rewrite Frshp, HNp in C; cbn [negb] in C; rewrite !Bool.andb_false_r in C; discriminate C].
Qed.
Lemma TKEEPa : forall k0 rg sh' kb n len, IMap.find k0 (s_regs st) = Some rg -> KEEPa k0 -> CtrA.win_lookup wnl sh' = Some (len, K_TWIN) ->
  block_of_twin (s_facts st) sh' = Some kb -> CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK) ->
  size_tail_ok (s_facts st) n = true -> tail_named (tail_rhs sh' n) k0 (s_facts st) = true -> KEEPa sh'.
Proof.
  intros k0 rg sh' kb n len Fk NKs WL0 BT0 WLk ST TN. intros ->. rewrite BT in BT0. injection BT0 as <-.
  unfold annot_tails_ok in TAILS. rewrite WLk in TAILS.
  pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) TAILS k0 rg Fk) as C. cbv beta in C. rewrite TN in C. discriminate C.
Qed.
Lemma KEEP_dela : forall k0, ~ In k0 [sh] -> KEEPa k0.
Proof. intros k0 H ->. apply H. left. reflexivity. Qed.

Let H' : Z := bv_unsigned (den E h').
Lemma H'_le : 0 <= H' <= WL.
Proof.
  destruct mids as (_ & _ & _ & (N1 & N2) & EI & _ & N8 & _ & _ & EH). fold H' in EH. rewrite EH. clear - N1 N2 EI. Z.div_mod_to_equations. lia.
Qed.
Lemma h'_den : bv_unsigned (den E' h') = bv_unsigned (den E h').
Proof.
  pose proof (CtrFrame.reg_below st FOK X13) as B13. pose proof (CtrFrame.reg_below st FOK X10) as B10. rewrite X10E in B10. cbn [sv_vars_below] in B10.
  assert (BEL : sv_vars_below (s_next st) h' = true -> bv_unsigned (den E' h') = bv_unsigned (den E h')) by (intros B; rewrite (CtrFrame.den_E' E st Fv Gv h' B); reflexivity).
  pose proof MHN as MH. unfold mid_hi in MH. destruct (getr st X13) as [|n o|op a xs| | | | | | | |]; try discriminate MH; cbn [sv_vars_below] in B13.
  - apply BEL. destruct (PrimInt63.eqb n k); [destruct (al8 o); [injection MH as <-; reflexivity| discriminate MH]|].
    destruct (find_lb_to (s_facts st) n k); [|discriminate MH].
    match type of MH with (if ?c then _ else _) = _ => destruct c; [|discriminate MH] end. injection MH as <-.
    unfold vec_hi. cbn [sv_vars_below]. rewrite B13, B10. reflexivity.
  - destruct op; try discriminate MH. destruct a as [|k' z| | | | | | | | |]; try discriminate MH.
    match type of MH with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate MH] end. injection MH as <-.
    apply andb_prop in C as [C _]. apply andb_prop in C as [_ XS].
    apply andb_prop in B13 as [_ BX].
    pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF XS) as X8. replace (bv_unsigned (den E (VL SYMCAPw))) with 65536 in X8 by (vm_compute; reflexivity).
    rewrite (CallA.twin_len_den E' xs) by (rewrite (CtrFrame.den_E' E st Fv Gv xs BX); lia). rewrite (CallA.twin_len_den E xs) by lia.
    rewrite (CtrFrame.den_E' E st Fv Gv xs BX). reflexivity.
Qed.
Lemma sh_E' : bv_unsigned (ev E' sh) = shad K /\ hiZ E' (annot_rsh h') = H' /\ loZ (annot_rsh h') = 0.
Proof.
  destruct (CtrFrame.reg_E' OPS E st ms mo HS FOK Fv Gv sh rsh Frs) as (Ek & _). destruct twin_data as (p & n & _ & ESH & _).
  split; [rewrite Ek; exact ESH|]. split; [| reflexivity]. unfold hiZ, annot_rsh. cbn [rg_hi]. exact h'_den.
Qed.
Definition newRa : list (int * region) := [(sh, annot_rsh h')].
Definition NEWSETa (a : Z) : Prop := shad K <= a < shad K + H'.
Lemma newRa_ok : forall k0 rg, In (k0, rg) newRa -> region_ok asegs (s_priv st) E' m' k0 rg.
Proof.
  intros k0 rg [X|[]]. injection X as <- <-. destruct sh_E' as (ESH & EHI & ELO). pose proof H'_le as HL.
  destruct twin_geo as (S1 & S2 & _ & INL & _). pose proof shad_atop_lt as [SAL SAH].
  constructor.
  - apply IMap.bst_empty.
  - intros _. rewrite ESH, EHI, ELO. unfold two64. lia.
  - intros _ a Ha. rewrite ESH, EHI, ELO in Ha. split; [| split; [intros X; discriminate X|]].
    + replace a with (shad K + (a - shad K)) by lia. rewrite (ZERO (a - shad K)) by (fold H'; lia). discriminate.
    + exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB m mo TWv a AWH INL ltac:(unfold in_iv, TWv; cbn [fst snd]; lia))).
  - intros g gr F. unfold annot_rsh in F. cbn [rg_cells] in F. rewrite IMap.find_empty in F. discriminate F.
  - intros g gr c i F. unfold annot_rsh in F. cbn [rg_cells] in F. rewrite IMap.find_empty in F. discriminate F.
  - intros o H1 _ _. unfold bg_byte, annot_rsh. cbn [rg_bg]. specialize (H1 SHNZ). rewrite EHI, ELO in H1. rewrite ESH. apply ZERO. fold H'. lia.
Qed.
Lemma newRa_range : forall k0 rg a, In (k0, rg) newRa -> bv_unsigned (ev E' k0) + loZ rg <= a < bv_unsigned (ev E' k0) + hiZ E' rg -> NEWSETa a.
Proof. intros k0 rg a [X|[]] Ha. injection X as <- <-. destruct sh_E' as (ESH & EHI & ELO). rewrite ESH, EHI, ELO in Ha. unfold NEWSETa. lia. Qed.
Lemma newRa_low : forall a, NEWSETa a -> AIMG_HI <= a < ATOP + 4096 /\ ~ in_user LBk a.
Proof.
  intros a Ha. unfold NEWSETa in Ha. pose proof H'_le as HL. destruct twin_geo as (S1 & S2 & _). pose proof shad_atop_lt as [SAL SAH]. unfold AIMG_HI.
  split; [lia|]. intros U. apply (LBk_apart a U). lia.
Qed.
Lemma newRa_nosh : forall a, NEWSETa a -> ~ (0x7fff8000 <= a < 0x800bde00).
Proof. intros a Ha. unfold NEWSETa in Ha. destruct twin_geo as (S1 & _). lia. Qed.
Lemma newRa_nostk : forall a, NEWSETa a -> ~ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Proof.
  intros a Ha (a' & Ra & ->). unfold NEWSETa in Ha. pose proof H'_le as HL. destruct twin_geo as (_ & S2 & _).
  destruct (shad_mono_facts a' ltac:(pose proof atop_range; lia)) as (_ & F2 & _). specialize (F2 (proj1 Ra)). lia.
Qed.
Lemma newRa_disj : forall k1 r1 k2 r2 a, In (k1, r1) newRa -> In (k2, r2) newRa -> k1 <> k2 -> (rg_w r1 = true \/ rg_w r2 = true) ->
  ~ (bv_unsigned (ev E' k1) + loZ r1 <= a < bv_unsigned (ev E' k1) + hiZ E' r1 /\ bv_unsigned (ev E' k2) + loZ r2 <= a < bv_unsigned (ev E' k2) + hiZ E' r2).
Proof. intros k1 r1 k2 r2 a [X1|[]] [X2|[]] NE. injection X1 as <- _. injection X2 as <- _. contradiction. Qed.
Lemma newRa_nodup : List.NoDup (map fst newRa).
Proof. cbn. constructor; [intros []| constructor]. Qed.
Lemma newRa_nz : forall k0 rg, In (k0, rg) newRa -> PrimInt63.eqb k0 0%uint63 = false.
Proof. intros k0 rg [X|[]]. injection X as <- _. exact SHNZ. Qed.

Definition RgA : IMap.t region := CtrFrame.RgPg st ks rss ksp newRa [sh].
Lemma annot_shape : annot_post st1 r sh h'
  = SS r (rf_set (s_rf (clobber st1)) X10 (VP (addn (s_next st) 15) wzero)) (s_ff st) (s_resv st) RgA (s_facts st)
       (set_op HEAP_ID hargs (s_ops st)) (s_priv st) (PrimInt63.add (addn (s_next st) 15) 1%uint63).
Proof.
  assert (G : forall (S : sstate) R0 nx1 v, setpc (setr (set_next (setregs S R0) nx1) X10 v) r
              = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) R0 (s_facts S) (s_ops S) (s_priv S) nx1) by (intros [] ? ? ?; reflexivity).
  unfold annot_post. cbv zeta. unfold fresh. cbn [fst snd]. rewrite G.
  destruct (clobber_fields st1) as (_ & FF & RV & _ & FS0' & OP & PV & NXc).
  destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (XE : s_next (setregs (clobber st1) (IMap.add sh (annot_rsh h') (IMap.remove sh (s_regs st1)))) = addn (s_next st) 15).
  { assert (SN : forall (S : sstate) R0, s_next (setregs S R0) = s_next S) by (intros [] ?; reflexivity).
    rewrite SN, NXc, NX1. symmetry. destruct (CtrFrame.NX st FOK) as (_ & _ & B). pose proof (int_range (s_next st)) as RRn. rewrite two63_eq in RRn.
    apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]. }
  rewrite XE, FF, RV, FS0', OP, PV, FF1, RV1, FS1, OP1, PV1. rewrite (CtrNoDelta.set_op_same HEAP_ID hargs (s_ops st) Hf).
  rewrite (CtrFrame.st1_regs st st1 FS ks offs rss ksp SPR Hksp). reflexivity.
Qed.

Theorem annot_post_ok : st_ok asegs OPS E' (annot_post st1 r sh h') (CtrFrame.ms' ms r R' m') mo'.
Proof.
  rewrite annot_shape.
  apply (CtrFrame.frame_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo' KEPT (fun x i Hx => CtrFree.cfvF_clob R' x i Hx) aw LB LBk AWH MINV' SBVa SBOa WBMa SBTa
           ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPa WINKa VKEEPa TKEEPa
           K16 LOSP STK' FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln OTH newRa [sh] newRa_nodup
           newRa_nz KEEP_dela NEWSETa newRa_ok newRa_range newRa_low newRa_nosh newRa_nostk newRa_disj
           hargs (w2Z md) (den E A) (wins_of E nn rest) (map (den E) (skipn (3 * nn) rest)) DECN HOLDN).
  -   intros a Ha. unfold NEWSETa in Ha. pose proof H'_le as HL. apply twin_in_heap_ws. lia.
  -   intros a _ _ NWS. left. exact NWS.
  -   intros a _ X. exact X.
  - exact (so_facts _ _ _ _ _ _ (CtrFrame.HS' OPS E st ms mo HS FOK Fv Gv)).
  - rewrite HeapCtr.den_VPz. rewrite (CtrFrame.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). reflexivity.
  - exact MINVo.
Qed.
End POST.

Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).

Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Definition acct_leaf_silent (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa mo'.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent mo aw L st LBa).

Lemma rw_cells_of_rb : forall (m : amem) A cs,
  cells_wf cs -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  (forall i, (i < length (cells_bytes cs))%nat -> rb asegs m (A + Z.of_nat i) = nth_error (cells_bytes cs) i) ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> wb asegs m (A + i) = true) ->
  ALib.Step.rw_cells asegs m A cs.
Proof.
  intros m A cs WF HA HB HR HW. pose proof (cells_bytes_length cs WF) as L. split.
  - split; [exact WF|]. split; [exact HA|]. split; [rewrite L; exact HB|].
    intros i Hi. rewrite <- (GlueA.rb_mrdA asegs). exact (HR i Hi).
  - split; [exact HA|]. split; [exact HB|]. intros i Hi. apply (GlueA.wb_wviewA asegs). exact (HW i Hi).
Qed.
Lemma mapped_chunk : forall (m : amem) n A,
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> wb asegs m (A + i) = true /\ rb asegs m (A + i) <> None) ->
  exists j, ALib.Step.rw_cells asegs m A [CB n j].
Proof.
  intros m n. induction n as [|n IH]; intros A HA HB H.
  - exists []. apply rw_cells_of_rb; [cbn; auto| exact HA| cbn; lia| intros i Hi; cbn in Hi; lia| intros i Hi; cbn in Hi; lia].
  - destruct (H 0 ltac:(lia)) as [_ R0]. rewrite Z.add_0_r in R0. destruct (rb asegs m A) as [b|] eqn:Eb; [|congruence].
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as [j Hj].
    { intros i Hi. replace (A + 1 + i) with (A + (i + 1)) by lia. apply H. lia. }
    exists (b :: j). destruct Hj as [[WF (_ & _ & BY)] _]. cbn [cells_wf cell_wf cells_bytes cbytes app] in WF, BY. rewrite app_nil_r in BY.
    apply rw_cells_of_rb.
    + pose proof (proj1 WF) as WL. simpl in WL. simpl. split; [|exact I]. f_equal. exact WL.
    + exact HA.
    + cbn [cells_size csize Nat.add]. lia.
    + cbn [cells_bytes cbytes app]. rewrite app_nil_r. intros i Hi. destruct i as [|i]; cbn [nth_error].
      * rewrite Z.add_0_r. exact Eb.
      * rewrite (GlueA.rb_mrdA asegs). replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply BY. cbn [length] in Hi. lia.
    + cbn [cells_size csize Nat.add]. intros i Hi. apply H. lia.
Qed.

Lemma shad_off : forall K X, 0 <= K <= X -> K mod 8 = 0 -> (X - K) mod 8 = 0 -> shad X = shad K + (X - K) / 8.
Proof. intros K X R K8 X8. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. Qed.
Lemma shlen_div : forall s, 0 <= s -> shlen s = s / 8.
Proof. intros s S0. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Definition annot_Q (R F : bvmap 5 word) (fc : bv 32) (lo sp K WL H' : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) t0 t1 t2 (AP.getr R 8) (AP.getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
                  (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
                  (AP.getr R 26) (AP.getr R 27) t3 t4 t5 t6) F (MState.ret_pc (AP.getr R 1)) fc None m' (seg_rom asegs)
    /\ munch [(lo, sp); (shad K, shad K + WL)] m m' /\ wmono asegs m m' /\ ALib.Mem.mem_inv asegs m' /\ stk asegs m' lo sp
    /\ (forall g, 0 <= g < H' -> rb asegs m' (shad K + g) = Some (Z_to_bv 8 0)).

Theorem annotate_sound : forall pc, to_Z pc = F_annot.F_annot.AANNOT -> contract_sound asegs OPS MP PB (annotate_c pc).
Proof.
  intros pc Hpc st sts Hspc Happ Kt E ms mo HS HMP HPB HK. cbn [c_apply c_pc annotate_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = F_annot.F_annot.AANNOT) by (rewrite Hspc; exact Hpc).
  destruct (annotate_apply_shape st sts Happ) as (r & hargs & wnl & st1 & k & sh & rsh & tlen & om & h' & PRE & X10E & Frs & WLt & MHN & MHO & SHNZ & ALK & BT
      & TSM & RO & LO0 & CELLS & BG & KEQ & NLE & OLE & AL8E & ENDIN & NV & TAILS & OTHERS & ESTS).
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ANNOT_ROOM None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct WOF as (E1 & E2 & E3 & E4).
  set (R := ms_regs ms) in *. set (sp := bv_unsigned (AP.getr R 2)) in *. set (m := ms_mem ms) in *. set (lo := CtrPre.sp_lo E st) in *.
  pose proof atop_range as ATR. pose proof (so_facts _ _ _ _ _ _ HS) as HFs.
  pose proof (CallA.twin_small_sound E _ _ HFs TSM) as WMAX.
  destruct (twin_data E st ms mo HS wnl nn rest LB aw NW W ARW TI k sh tlen WLt ALK BT WMAX) as (p & n & HbT & ESH & EWL & NB & A16 & BK & HI & INL & INW).
  destruct (mids E st ms mo HS wnl nn rest LB aw NW W ARW TI k sh rsh tlen om h' WLt MHN MHO ALK BT WMAX KEQ NLE OLE AL8E ENDIN)
    as (K8 & K47 & (O1 & O2) & (N1 & N2) & EI & O8 & N8 & E8 & EH & EH').
  set (K := bv_unsigned (ev E k)) in *. set (WL := bv_unsigned (den E tlen)) in *.
  set (Oz := bv_unsigned (den E (getr st X12))) in *. set (Nz := bv_unsigned (den E (getr st X13))) in *. set (Ez := bv_unsigned (den E (getr st X11))) in *.
  set (H' := bv_unsigned (den E h')) in *.
  assert (KB : 6483968 <= K) by (unfold ablk, AIMG_HI, KLS in BK; lia).

  assert (REGV : forall x, AP.getr R (reg_of_r5 x) = Z_to_bv 64 (bv_unsigned (den E (getr st x)))).
  { intros x. unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS x). symmetry. apply Z_to_bv_bv_unsigned. }
  assert (Ha0 : AP.getr R 10 = Z_to_bv 64 K) by (rewrite <- HeapCtr.reg_of_X10, REGV, X10E, HeapCtr.den_VPz; reflexivity).
  assert (Ha1 : AP.getr R 11 = Z_to_bv 64 Ez) by (rewrite <- HeapCtr.reg_of_X11, REGV; reflexivity).
  assert (Ha2 : AP.getr R 12 = Z_to_bv 64 Oz) by (rewrite <- HeapCtr.reg_of_X12, REGV; reflexivity).
  assert (Ha3 : AP.getr R 13 = Z_to_bv 64 Nz).
  { assert (RX : reg_of_r5 X13 = 13%bv) by (apply bv_eq; reflexivity). rewrite <- RX, REGV. reflexivity. }

  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. pose proof (AI_relro AI _ _ _ _ _ AH) as RELRO.
  destruct RT as (_ & GOT6 & _ & REALM & SHB & _ & _ & LAY & CANP & _ & _ & _ & CF120 & _ & _ & _ & _ & _ & _ & _ & _ & DCO & VERB).
  assert (GMS : ALib.Step.rw_cells asegs m 0xd1538 [C8 (Z_to_bv 64 0xd3428)])
    by (apply (AFake_arep.AFake_arep.relro_word m 0xd1538 0xd3428 RELRO); [unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
  assert (GVB : ALib.Step.rw_cells asegs m 0xd1568 [C8 (Z_to_bv 64 0x169558)])
    by (apply (AFake_arep.AFake_arep.relro_word m 0xd1568 0x169558 RELRO); [unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
  assert (PC : F_apoison.F_apoison.poison_cells m) by (unfold F_apoison.F_apoison.poison_cells; repeat (split; [assumption|]); assumption).
  assert (ANC : F_annot.F_annot.annot_cells m) by (unfold F_annot.F_annot.annot_cells; repeat (split; [assumption|]); assumption).

  pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW) as AWH.
  destruct (shadow_tight _ _ BK HI ltac:(lia)) as [S1 S2]. rewrite <- EWL in S2, INL.
  assert (SAL : shad ATOP < ATOP /\ shad ATOP <= 0x10007fff8000).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; Z.div_mod_to_equations; lia. }
  assert (CHUNK : forall a len, shad K <= a -> 0 <= len -> a + len <= shad K + WL -> exists junk, ALib.Step.rw_cells asegs m a [CB (Z.to_nat len) junk]).
  { intros a len A1 L0 A2. apply mapped_chunk; [lia| rewrite Z2Nat.id by lia; lia|]. intros i Hi. rewrite Z2Nat.id in Hi by lia.
    destruct (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB m mo (shad K, WL) (a + i) AWH INL ltac:(unfold in_iv; cbn [fst snd]; lia)) as [MP0 SEG].
    split.
    - apply (GlueA.wb_wviewA asegs). unfold wview, GlueA.AMem.wa. destruct (m (Z_to_bv 64 (a + i))); [discriminate| contradiction].
    - unfold rb. destruct (m (Z_to_bv 64 (a + i))); [discriminate| contradiction]. }
  destruct (twin_T_facts AI ACCT UNIV W aw LB m mo _ (proj1 ARW) HbT) as (HbL & _). rewrite E4 in HbL.
  destruct (AI_block AI _ _ _ _ _ p K n AH HbL) as (_ & _ & _ & RNGT & _). rewrite <- EWL in RNGT.
  set (H := hiZ E rsh) in *.
  pose proof (old_zero E st ms mo HS wnl nn rest LB aw NW W ARW TI k sh rsh tlen Frs WLt SHNZ ALK BT WMAX LO0 CELLS BG) as OLDZ. fold K H m in OLDZ.
  assert (SHO : shad Oz = shad K + H) by (rewrite EH; apply shad_off; lia).
  assert (SHN : shad Nz = shad K + H') by (rewrite EH'; apply shad_off; lia).
  assert (HLE : 0 <= H <= WL /\ 0 <= H' <= WL) by (rewrite EH, EH'; clear - O1 O2 N1 N2 EI; split; Z.div_mod_to_equations; lia).
  change (to_Z ANNOT_ROOM) with 4096 in LOR. fold sp in LOR, ST, SPT, SP16, RSTK. fold lo in LOR, ST, BOT, LO, RSTK.
  assert (OUTV : forall (m' : amem) a0 len0, shad K <= a0 -> a0 + len0 <= shad K + WL ->
             munch [(sp - F_annot.F_annot.ANNOT_STACK, sp); (a0, a0 + len0)] m m' -> munch [(lo, sp); (shad K, shad K + WL)] m m').
  { intros m' a0 len0 A1 A2 MU. eapply munch_weaken; [| exact MU]. intros x OUT. cbn [ALib.Frame.outside] in *. unfold F_annot.F_annot.ANNOT_STACK. lia. }
  assert (KEEPZ : forall (m' : amem) g, 0 <= g < H -> m' (ALib.Mem.wa (shad K + g)) = m (ALib.Mem.wa (shad K + g)) -> rb asegs m' (shad K + g) = Some (Z_to_bv 8 0)).
  { intros m' g Hg EQ. rewrite <- (OLDZ g Hg). unfold rb. unfold ALib.Mem.wa in EQ. rewrite EQ. reflexivity. }
  assert (OUTS : forall x, shad K <= x < shad K + WL -> ~ (sp - F_annot.F_annot.ANNOT_STACK <= x < sp)) by (intros x Hx; unfold F_annot.F_annot.ANNOT_STACK; lia).
  assert (UW : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (ALib.Mem.wa x) = x) by (intros x Hx; unfold ALib.Mem.wa; apply Z_to_bv_small; clear - Hx; zl).
  assert (BLKE : Ez <= 2 ^ 47 /\ ((AIMG_HI <= K /\ K + 8 * WL <= KLS) \/ (0x10007fff8000 <= K /\ K + 8 * WL <= ATOP))).
  { pose proof ATOP_al16 as AT16. assert (WLE : WL = (n + 7) / 8) by (rewrite EWL; apply shlen_div; lia).
    unfold ablk, AIMG_HI, KLS in *. clear - WLE BK HI A16 AT16 NB EI ATR. split; [| destruct BK as [BK|BK]; [left| right]]; Z.div_mod_to_equations; lia. }
  destruct BLKE as [E47 BLK8].
  assert (EV : evtF asegs RNG (annot_Q R (ms_fregs ms) (ms_fcsr ms) lo sp K WL H' m)
                 (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                          (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                          (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                          (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                     (ms_fregs ms) (Z_to_bv 64 F_annot.F_annot.AANNOT) (ms_fcsr ms) None m (seg_rom asegs))).
  { assert (O8' : Oz mod 8 = 0) by (clear - O8 K8; Z.div_mod_to_equations; lia).
    assert (N8' : Nz mod 8 = 0) by (clear - N8 K8; Z.div_mod_to_equations; lia).
    assert (CAP : Ez - K <= 2 ^ 40) by (unfold WL in *; lia).
    assert (XOUT : forall g, 0 <= g < WL -> bv_unsigned (ALib.Mem.wa (shad K + g)) = shad K + g) by (intros g Hg; apply UW; lia).
    assert (G1 : ATOP <= lo) by lia.
    assert (G2 : lo <= bv_unsigned (AP.getr R 2) - F_annot.F_annot.ANNOT_STACK) by (unfold F_annot.F_annot.ANNOT_STACK; fold sp; lia).
    destruct (Z_lt_le_dec Nz Oz) as [LT|GE]; [| destruct (Z_lt_le_dec Oz Nz) as [GT|LE2]].
    -
      assert (LENE : shlen (Oz - Nz) = H - H') by (rewrite shlen_div by lia; rewrite EH, EH'; clear - N1 LT O8 N8; Z.div_mod_to_equations; lia).
      destruct (CHUNK (shad Nz) (shlen (Oz - Nz)) ltac:(lia) ltac:(lia) ltac:(lia)) as [junk BODY].
      eapply evtF_mono.
      + pose proof (F_annot.F_annot_g.annot_shrink_gspec RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                 (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                 (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                 (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                 (ms_fregs ms) (ms_fcsr ms) m K Ez Oz Nz lo junk MI ST G1 G2 PC ANC Ha0 Ha1 Ha2 Ha3 K8 E8 O8' N8') as X0.
        assert (G3 : 0 <= K <= Nz) by lia. assert (G4 : ablk Nz Oz) by (unfold ablk; lia). assert (G5 : Oz <= 2 ^ 47) by lia.
        apply (X0 G3 LT O2 CAP G4 G5 BODY (ACCT_rng_aimg _ _ _ _ _ _ AC) RSTK). eapply rng_sub'; [exact RNGT| lia].
      + intros ms' (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV & STK & _).
        exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'. split; [exact EMS|]. fold sp in MU, STK.
        split; [apply (OUTV m' (shad Nz) (shlen (Oz - Nz))); [lia| lia| exact MU]|]. split; [exact WM|]. split; [exact MINV|]. split; [exact STK|].
        intros g Hg. apply KEEPZ; [lia|]. apply MU. cbn [ALib.Frame.outside]. rewrite XOUT by lia. split; [apply OUTS; lia|]. split; [lia| exact I].
    -
      assert (LENE : shlen (Nz - Oz) = H' - H) by (rewrite shlen_div by lia; rewrite EH, EH'; clear - O1 GT O8 N8; Z.div_mod_to_equations; lia).
      destruct (CHUNK (shad Oz) (shlen (Nz - Oz)) ltac:(lia) ltac:(lia) ltac:(lia)) as [junk BODY].
      eapply evtF_mono.
      + pose proof (F_annot.F_annot_g.annot_grow_gspec RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                 (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                 (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                 (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                 (ms_fregs ms) (ms_fcsr ms) m K Ez Oz Nz lo junk MI ST G1 G2 PC ANC Ha0 Ha1 Ha2 Ha3 K8 E8 O8' N8') as X0.
        assert (G3 : 0 <= K <= Oz) by lia. assert (G4 : ablk Oz Nz) by (unfold ablk; lia). assert (G5 : Nz <= 2 ^ 47) by lia.
        apply (X0 G3 GT N2 CAP G4 G5 BODY (ACCT_rng_aimg _ _ _ _ _ _ AC) RSTK). eapply rng_sub'; [exact RNGT| lia].
      + intros ms' (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV & STK & CELL).
        exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'. split; [exact EMS|]. fold sp in MU, STK.
        split; [apply (OUTV m' (shad Oz) (shlen (Nz - Oz))); [lia| lia| exact MU]|]. split; [exact WM|]. split; [exact MINV|]. split; [exact STK|].
        intros g Hg. destruct (Z_lt_le_dec g H) as [GL|GH].
        * apply KEEPZ; [lia|]. apply MU. cbn [ALib.Frame.outside]. rewrite XOUT by lia. split; [apply OUTS; lia|]. split; [lia| exact I].
        * destruct CELL as [[_ (_ & _ & BY)] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
          specialize (BY (Z.to_nat (g - H)) ltac:(rewrite repeat_length; lia)). rewrite Z2Nat.id in BY by lia. rewrite nth_error_repeat in BY by lia.
          rewrite (GlueA.rb_mrdA asegs). replace (shad K + g) with (shad Oz + (g - H)) by lia. exact BY.
    -
      assert (EQ : Nz = Oz) by lia. rewrite EQ in Ha3. assert (HH : H' = H) by (rewrite EH, EH', EQ; reflexivity).
      eapply evtF_mono.
      + assert (G3 : 0 <= K <= Oz) by lia.
        exact (F_annot.F_annot_g.annot_same_gspec RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                 (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                 (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                 (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                 (ms_fregs ms) (ms_fcsr ms) m K Ez Oz lo MI ST G1 G2 GOT6 ANC Ha0 Ha1 Ha2 Ha3 G3 O2 CAP E47 (ACCT_rng_aimg _ _ _ _ _ _ AC) RSTK).
      + intros ms' (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV & STK).
        exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'. split; [exact EMS|]. fold sp in MU, STK.
        split. { eapply munch_weaken; [| exact MU]. intros x OUT. cbn [ALib.Frame.outside] in *. unfold F_annot.F_annot.ANNOT_STACK. lia. }
        split; [exact WM|]. split; [exact MINV|]. split; [exact STK|].
        intros g Hg. apply KEEPZ; [lia|]. apply MU. cbn [ALib.Frame.outside]. rewrite XOUT by lia. split; [apply OUTS; lia| exact I]. }
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ annot_Q R (ms_fregs ms) (ms_fcsr ms) lo sp K WL H' m ms') _ _ moc mo Kt).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV'' & STK' & ZERO).
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WTr & LT0 & ER).
    assert (EMS' : ms' = CtrFrame.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.ms'. f_equal. fold R. rewrite RA. apply MState.ret_pc_even.
      - lia.
      - pose proof (HeapCtr.call_pre_even st r CP) as EV0.
        pose proof (ValP.land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV0 in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
    apply (HK _ ltac:(rewrite ESTS; left; reflexivity) (CtrFrame.E' E st (CtrFree.cfvF R') (fun _ _ => Z_to_bv 8 0)) ms' mo' (CtrFrame.EXT E st _ _) HMP').
    rewrite EMS'.
    assert (KEPT : forall rg, In rg CtrFrame.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg).
    { intros rg Hrg. unfold CtrFrame.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg. }
    rewrite <- E1, <- E2, <- E3, <- E4 in ACP.
    assert (LOS : lo <= sp) by lia.
    exact (annot_post_ok E st ms mo HS wnl nn rest LB aw NW WF W ARW TI k sh rsh tlen om h' Frs WLt MHN MHO SHNZ ALK BT WMAX KEQ NLE OLE AL8E ENDIN X10E
             r st1 CP FS AJ NV TAILS OTHERS hargs md A nw Hf Hc Eh Tnw Nn Ln HC AWden ks offs rss ksp SPR Hksp SPE K16 LOSP FLOOR BOT LOS SPT
             R' m' mo' KEPT MINV'' STK' MU WM ZERO ACP OTH HMI').
Qed.
End Annot.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Unset Nia Cache. Unset Nra Cache.

Ltac zl := unfold two64, two63, bv_modulus in *; change (2 ^ Z.of_N 64) with 18446744073709551616 in *; lia.

Notation al8_spec := CallA.TwinB.al8_spec (only parsing).
Notation mod64_mod8 := CallA.TwinB.mod64_mod8 (only parsing).
Notation al8_sv_sound := CallA.TwinB.al8_sv_sound (only parsing).

Lemma mid_hi_sound : forall E fs k mid h, facts_hold E fs -> mid_hi fs k mid = Some h ->
  bv_unsigned (ev E k) mod 8 = 0 -> bv_unsigned (ev E k) < 2 ^ 62 ->
  bv_unsigned (ev E k) <= bv_unsigned (den E mid)
  /\ (bv_unsigned (den E mid) - bv_unsigned (ev E k)) mod 8 = 0
  /\ bv_unsigned (den E h) = (bv_unsigned (den E mid) - bv_unsigned (ev E k)) / 8.
Proof.
  intros E fs k mid h HF H K8 K62. unfold mid_hi in H.
  destruct mid as [|n o|op a xs| | | | | | | |]; try discriminate H.
  2:{
      destruct op; try discriminate H. destruct a as [|k' z| | | | | | | | |]; try discriminate H.
      destruct (PrimInt63.eqb k' k && weqb z wzero && div8x fs xs && KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) && nowrap_kb fs k SYMCAPw) eqn:C; [|discriminate H].
      injection H as <-.
      apply andb_prop in C as [C NWK]. apply andb_prop in C as [C XS]. apply andb_prop in C as [C D8]. apply andb_prop in C as [EK EZ].
      apply Uint63.eqb_correct in EK. subst k'. apply weqb_eq in EZ. subst z.
      pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF XS) as X8. replace (bv_unsigned (den E (VL SYMCAPw))) with 65536 in X8 by (vm_compute; reflexivity).
      destruct (ValP.nowrap_kb_sound E _ HF k _ NWK) as [RK8 _]. replace (w2Zs SYMCAPw) with 65536 in RK8 by (vm_compute; reflexivity).
      pose proof (CallA.TwinB.div8x_holds E fs xs HF D8) as X0.
      pose proof (bv_unsigned_in_range 64 (den E xs)) as RX. unfold bv_modulus in RX. change (2 ^ Z.of_N 64) with (2 ^ 64) in RX.
      pose proof (bv_unsigned_in_range 64 (ev E k)) as RK0. unfold bv_modulus in RK0. change (2 ^ Z.of_N 64) with (2 ^ 64) in RK0.
      rewrite CallA.TwinB.den_add_vp0. unfold two64 in *. rewrite Z.mod_small by lia.
      replace (bv_unsigned (ev E k) + bv_unsigned (den E xs) - bv_unsigned (ev E k)) with (bv_unsigned (den E xs)) by lia.
      split; [lia|]. split; [exact X0|]. rewrite (CallA.TwinB.twin_len_den E xs) by lia. clear - X0. Z.div_mod_to_equations. lia. }
  pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. unfold bv_modulus in RK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RK.
  destruct (PrimInt63.eqb n k) eqn:NK.
  - apply Uint63.eqb_correct in NK. subst n. destruct (al8 o) eqn:A8; [|discriminate H]. injection H as <-.
    destruct (al8_spec o A8) as (T & ZS & M). pose proof (int_range (wl o)) as RO. rewrite two63_eq in RO.
    assert (DM : bv_unsigned (den E (VP k o)) = bv_unsigned (ev E k) + to_Z (wl o)).
    { rewrite (ValP.den_VP E k o), ZS. unfold two64. apply Z.mod_small. lia. }
    rewrite DM. split; [lia|]. replace (bv_unsigned (ev E k) + to_Z (wl o) - bv_unsigned (ev E k)) with (to_Z (wl o)) by lia.
    split; [exact M|]. rewrite HeapCtr.TwinB.den_wlit. unfold ALib.Mem.wa. rewrite lsr_spec. change (to_Z 3%uint63) with 3. change (2 ^ 3) with 8.
    apply Z_to_bv_small. clear - RO. unfold two64, two63, bv_modulus in *. change (2 ^ Z.of_N 64) with 18446744073709551616. Z.div_mod_to_equations. lia.
  - destruct (find_lb_to fs n k) as [o2|] eqn:LB; [|discriminate H].
    destruct (al8 o && al8 o2 && PrimInt63.leb 3%uint63 (find_align fs n) && nowrap_kb fs n o && nowrap_kb fs k o2) eqn:C; [|discriminate H].
    injection H as <-.
    apply andb_prop in C as [C NW2]. apply andb_prop in C as [C NWo]. apply andb_prop in C as [C AL]. apply andb_prop in C as [A8 A82].
    destruct (al8_spec o A8) as (T & ZS & M). destruct (al8_spec o2 A82) as (T2 & ZS2 & M2).
    destruct (ValP.nowrap_kb_sound E _ HF n o NWo) as [RA DA]. destruct (ValP.nowrap_kb_sound E _ HF k o2 NW2) as [R2 D2].
    pose proof (CallA.TwinB.find_lb_to_holds E fs n k o2 HF LB) as L. rewrite D2 in L.
    pose proof (ValP.find_align_le E fs HF n 3%uint63 AL) as AN. change (2 ^ to_Z 3%uint63) with 8 in AN.
    rewrite ZS in RA, DA. rewrite ZS2 in L, R2.
    pose proof (int_range (wl o)) as RO. pose proof (int_range (wl o2)) as RO2. unfold two64 in *.
    rewrite DA. split; [lia|]. split.
    + rewrite Zminus_mod, Z.add_mod, AN, M, K8 by lia. reflexivity.
    + unfold vec_hi. cbn [den]. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, bv_sub_unsigned.
      replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
      replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      change (bv_add (ev E n) (wbv o)) with (den E (VP n o)). rewrite DA.
      change (bv_add (ev E k) (wbv wzero)) with (den E (VP k wzero)). rewrite (HeapCtr.TwinB.den_VPz E k).
      unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      rewrite Z.mod_small by lia. reflexivity.
Qed.

Definition annot_rsh (h' : sv) : region := Region 0%uint63 h' false BGZero IMap.empty.
Definition annot_post (st1 : sstate) (r sh : int) (h' : sv) : sstate :=
  let st2 := setregs (clobber st1) (IMap.add sh (annot_rsh h') (IMap.remove sh (s_regs st1))) in
  setpc (setr (snd (fresh st2)) X10 (VP (fst (fresh st2)) wzero)) r.
Lemma annotate_apply_shape : forall st sts, annotate_apply st = Some sts ->
  exists r hargs wnl st1 k sh rsh len om h',
    acall_pre ANNOT_ROOM None st = Some (r, hargs, wnl, st1)
    /\ getr st X10 = VP k wzero
    /\ IMap.find sh (s_regs st) = Some rsh /\ CtrA.win_lookup wnl sh = Some (len, K_TWIN)
    /\ mid_hi (s_facts st) k (getr st X13) = Some h'
    /\ mid_hi (s_facts st) k om = Some (rg_hi rsh)
    /\ PrimInt63.eqb sh 0%uint63 = false
    /\ PrimInt63.leb 3%uint63 (find_align (s_facts st) k) = true
    /\ block_of_twin (s_facts st) sh = Some k
    /\ twin_small (s_facts st) len = true
    /\ rg_w rsh = false /\ rg_lo rsh = 0%uint63 /\ rg_cells rsh = IMap.Leaf /\ rg_bg rsh = BGZero
    /\ KnownT.KnownT.known_eq_t (s_facts st) (getr st X12) om = true
    /\ KnownT.KnownT.known_leu_t (s_facts st) (getr st X13) (getr st X11) = true
    /\ KnownT.KnownT.known_leu_t (s_facts st) (getr st X12) (getr st X11) = true
    /\ al8_sv (s_facts st) (getr st X11) = true
    /\ annot_end_ok (s_facts st) k len (getr st X11) = true
    /\ no_views_on (s_facts st) (s_regs st) k sh = true
    /\ annot_tails_ok st wnl k sh = true
    /\ annot_others_ok st wnl k sh len = true
    /\ sts = [annot_post st1 r sh h'].
Proof.
  intros st sts H. unfold annotate_apply in H.
  destruct (acall_pre ANNOT_ROOM None st) as [[[[r hargs] wnl] st1]|] eqn:PRE; [|discriminate].
  destruct (getr st X10) as [|k zb| | | | | | | | |] eqn:X10E; try discriminate.
  destruct (find_twin (s_facts st) k) as [sh|] eqn:FT; [|discriminate].
  destruct (IMap.find sh (s_regs st)) as [rsh|] eqn:Frs; [|discriminate].
  destruct (CtrA.win_lookup wnl sh) as [[len kd]|] eqn:WL; [|discriminate].
  destruct (hi_mid k (rg_hi rsh)) as [om|] eqn:HM; [|discriminate].
  destruct (mid_hi (s_facts st) k (getr st X13)) as [h'|] eqn:MH; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end.
  apply andb_prop in C as [C OTHERS]. apply andb_prop in C as [C TAILS]. apply andb_prop in C as [C NV]. apply andb_prop in C as [C ENDIN]. apply andb_prop in C as [C AL8].
  apply andb_prop in C as [C OLE]. apply andb_prop in C as [C NLE]. apply andb_prop in C as [C KEQ]. apply andb_prop in C as [C REV].
  apply andb_prop in C as [C CB]. apply andb_prop in C as [C LO0]. apply andb_prop in C as [C RO]. apply andb_prop in C as [C TSM].
  apply andb_prop in C as [C BT]. apply andb_prop in C as [C AL]. apply andb_prop in C as [C SHNZ].
  apply andb_prop in C as [ZB KD].
  apply weqb_eq in ZB. subst zb. apply weqb_eq in KD. subst kd. apply negb_true_iff in SHNZ. apply negb_true_iff in RO.
  apply Uint63.eqb_correct in LO0.
  destruct (block_of_twin (s_facts st) sh) as [kb|] eqn:BTE; [|discriminate BT]. apply Uint63.eqb_correct in BT. subst kb.
  destruct (mid_hi (s_facts st) k om) as [hO|] eqn:MHO; [|discriminate REV]. apply sv_eqb_eq in REV. subst hO.
  assert (CB' : rg_cells rsh = IMap.Leaf /\ rg_bg rsh = BGZero).
  { destruct (rg_cells rsh); [| discriminate CB]. destruct (rg_bg rsh); try discriminate CB. split; reflexivity. }
  exists r, hargs, wnl, st1, k, sh, rsh, len, om, h'.
  repeat (split; [first [reflexivity | assumption | exact (proj1 CB') | exact (proj2 CB')]|]).
  unfold annot_post, annot_rsh. cbv zeta in H |- *.
  destruct (fresh (setregs (clobber st1) (IMap.add sh (Region 0%uint63 h' false BGZero IMap.empty) (IMap.remove sh (s_regs st1))))) as [v st3] eqn:F.
  injection H as <-. reflexivity.
Qed.

Lemma blk_win_pos_inv : forall st wnl x, blk_win_pos st wnl x = true ->
  exists n, CtrA.win_lookup wnl x = Some (n, CtrLib.K_BLOCK) /\ KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) n = true.
Proof.
  intros st wnl x H. unfold blk_win_pos in H. destruct (CtrA.win_lookup wnl x) as [[n kd]|]; [|discriminate H].
  apply andb_prop in H as [KD P]. apply weqb_eq in KD. subst kd. exists n. split; [reflexivity| exact P].
Qed.
Lemma blk_reg_w_inv : forall st x, blk_reg_w st x = true ->
  exists r, IMap.find x (s_regs st) = Some r /\ rg_w r = true /\ rg_lo r = 0%uint63 /\ KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (rg_hi r) = true.
Proof.
  intros st x H. unfold blk_reg_w in H. destruct (IMap.find x (s_regs st)) as [r|]; [|discriminate H].
  apply andb_prop in H as [H P]. apply andb_prop in H as [W L0]. apply Uint63.eqb_correct in L0. exists r. auto.
Qed.
Lemma existsb_eqb_In : forall (x : int) l, existsb (PrimInt63.eqb x) l = true -> In x l.
Proof. intros x l H. apply existsb_exists in H as (y & Hy & Q). apply Uint63.eqb_correct in Q. subst y. exact Hy. Qed.
Lemma annot_others_inv : forall st wnl k sh len k0 len0 kd0,
  annot_others_ok st wnl k sh len = true -> In (k0, len0, kd0) wnl -> k0 <> sh ->
  (kd0 <> K_TWIN /\ wt kd0 = false /\ to_Z (wl kd0) <= 8)
  \/ (kd0 = K_TWIN
      /\ ((exists l0 wlen, len = VL wlen /\ len0 = VL l0 /\ l0 <> wlen)
          \/ exists k2, block_of_twin (s_facts st) k0 = Some k2 /\ k2 <> k /\ PrimInt63.leb 3%uint63 (find_align (s_facts st) k2) = true
               /\ ((In k (carg_vecs st) /\ In k2 (carg_vecs st))
                   \/ (In k (carg_vecs st) /\ blk_win_pos st wnl k2 = true)
                   \/ (blk_win_pos st wnl k = true /\ In k2 (carg_vecs st))
                   \/ (blk_reg_w st k = true /\ blk_reg_w st k2 = true)))).
Proof.
  intros st wnl k sh len k0 len0 kd0 H Hin NS. unfold annot_others_ok in H. cbv zeta in H.
  pose proof (proj1 (forallb_forall _ _) H _ Hin) as C. cbv beta iota in C. unfold annot_other_ok in C.
  replace (PrimInt63.eqb k0 sh) with false in C by (symmetry; apply Uint63.eqb_false_spec; exact NS).
  destruct (weqb kd0 K_TWIN) eqn:KD.
  - apply weqb_eq in KD. subst kd0. right. split; [reflexivity|].
    apply orb_prop in C as [C|C].
    + left. destruct len0 as [l0| | | | | | | | | |]; try discriminate C. destruct len as [wlen| | | | | | | | | |]; try discriminate C.
      exists l0, wlen. split; [reflexivity|]. split; [reflexivity|]. intros ->.
      rewrite (proj2 (weqb_ok _ _) eq_refl) in C. discriminate C.
    + right. destruct (block_of_twin (s_facts st) k0) as [k2|]; [|discriminate C]. exists k2. split; [reflexivity|].
      apply andb_prop in C as [C EV]. apply andb_prop in C as [NE AL]. apply negb_true_iff in NE. apply Uint63.eqb_false_spec in NE.
      split; [exact NE|]. split; [exact AL|].
      apply orb_prop in EV as [EV|EV]; [apply orb_prop in EV as [EV|EV]; [apply orb_prop in EV as [EV|EV]|]|]; apply andb_prop in EV as [E1 E2].
      * left. split; [exact (existsb_eqb_In _ _ E1)| exact (existsb_eqb_In _ _ E2)].
      * right; left. split; [exact (existsb_eqb_In _ _ E1)| exact E2].
      * right; right; left. split; [exact E1| exact (existsb_eqb_In _ _ E2)].
      * right; right; right. split; assumption.
  - left. cbn [orb] in C. apply andb_prop in C as [T L]. apply negb_true_iff in T. apply Uint63.leb_spec in L. change (to_Z 8%uint63) with 8 in L.
    split; [intros ->; rewrite (proj2 (weqb_ok _ _) eq_refl) in KD; discriminate KD|]. split; assumption.
Qed.

Section Annot.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.TwinB.cov1 HEAP_ID args z.

Hypothesis Cw_vec_unowned : forall md ca LB ws m i a, cw_holds Cw md ca LB ws m -> In i (VECS md) -> nth_error ca i = Some a -> bv_unsigned a <> 0 ->
  forall w, In w ws -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned a.

Hypothesis Cw_vecs_distinct : forall md ca LB ws m i j a b, cw_holds Cw md ca LB ws m -> In i (VECS md) -> In j (VECS md) -> i <> j ->
  nth_error ca i = Some a -> nth_error ca j = Some b -> bv_unsigned a <> 0 -> bv_unsigned b <> 0 -> bv_unsigned a <> bv_unsigned b.

Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.

Lemma KT9 : w2Z K_TWIN = 9. Proof. reflexivity. Qed.

Section POST.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok bsegs OPS E st ms mo.
Variables (wnl : list (int * sv * w64)) (nn : nat) (rest : list sv) (LB : blocks) (aw : word).
Hypothesis NW : CtrA.nonstack_windows nn rest = Some wnl.
Hypothesis WF : windows_wf (wins_of E nn rest) LB (ATOP + 4096).
Variable WW : wit.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis TI : ties WW (wins_of E nn rest).

Variables (k sh : int) (rsh : region) (tlen : sv) (om h' : sv).
Hypothesis Frs : IMap.find sh (s_regs st) = Some rsh.
Hypothesis WLt : CtrA.win_lookup wnl sh = Some (tlen, K_TWIN).
Hypothesis MHN : mid_hi (s_facts st) k (getr st X13) = Some h'.
Hypothesis MHO : mid_hi (s_facts st) k om = Some (rg_hi rsh).
Hypothesis SHNZ : PrimInt63.eqb sh 0%uint63 = false.
Hypothesis ALK : PrimInt63.leb 3%uint63 (find_align (s_facts st) k) = true.
Hypothesis BT : block_of_twin (s_facts st) sh = Some k.
Hypothesis WMAX : bv_unsigned (den E tlen) <= 8064.
Hypothesis KEQ : KnownT.KnownT.known_eq_t (s_facts st) (getr st X12) om = true.
Hypothesis NLE : KnownT.KnownT.known_leu_t (s_facts st) (getr st X13) (getr st X11) = true.
Hypothesis OLE : KnownT.KnownT.known_leu_t (s_facts st) (getr st X12) (getr st X11) = true.
Hypothesis AL8E : al8_sv (s_facts st) (getr st X11) = true.
Hypothesis ENDIN : annot_end_ok (s_facts st) k tlen (getr st X11) = true.
Hypothesis X10E : getr st X10 = VP k wzero.
Hypothesis LO0 : rg_lo rsh = 0%uint63.
Hypothesis CELLS : rg_cells rsh = IMap.Leaf.
Hypothesis BG : rg_bg rsh = BGZero.

Let m : amem := ms_mem ms.
Let K : Z := bv_unsigned (ev E k).
Let WL : Z := bv_unsigned (den E tlen).
Let HF : facts_hold E (s_facts st) := so_facts _ _ _ _ _ _ HS.
Let HWw : aw_holds_w AI ACCT UNIV WW aw LB m mo := proj1 AR.

Lemma twin_data : exists p n,
  In (HB p K n) (w_T WW) /\ bv_unsigned (ev E sh) = shad K /\ WL = shlen (n + 7) /\ 1 <= n <= 64512 /\ K mod 16 = 0
  /\ ablk K (K + n) /\ K + n <= ATOP /\ In (shad K, shlen (n + 7)) LB /\ In (Win (shad K) (shlen (n + 7)) K_TWINz) (wins_of E nn rest).
Proof.
  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl sh tlen K_TWIN NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as (_ & _ & _ & INW).
  rewrite KT9 in INW. pose proof TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV).
  unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as ESA ESL.
  destruct (twin_T_facts AI ACCT UNIV WW aw LB m mo b HWw HbT) as (HbL & _ & _ & HTW & (p & EB) & NB & A16 & UB & _).
  pose proof HWw as (AH & _).
  destruct (heap_block_facts AI _ _ _ _ _ b AH HbL ltac:(exists p; rewrite EB; reflexivity)) as (_ & (BK & _ & HI & _) & _).
  pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  fold WL in ESL.
  pose proof (CallA.TwinB.block_of_twin_sound E _ sh k HF BT) as LINK. fold K in LINK.
  pose proof (ValP.find_align_le E _ HF k 3%uint63 ALK) as K8. change (2 ^ to_Z 3%uint63) with 8 in K8. fold K in K8.
  pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. fold K in RK. unfold bv_modulus in RK. change (2 ^ Z.of_N 64) with (2 ^ 64) in RK.
  rewrite Z.mod_small in LINK by (clear - RK; Z.div_mod_to_equations; lia).
  assert (EK : K = ab_addr b).
  { rewrite LINK in ESA. unfold shad, ASHOFF in ESA. rewrite Z.shiftr_div_pow2 in ESA by lia. change (2 ^ 3) with 8 in ESA.
    clear - ESA K8 A16 BK. Z.div_mod_to_equations. lia. }
  assert (NPR : ab_size b <= 64512).
  { unfold shlen in ESL. rewrite Z.shiftr_div_pow2 in ESL by lia. change (2 ^ 3) with 8 in ESL. clear - ESL WMAX NB. unfold WL in ESL. Z.div_mod_to_equations. lia. }
  exists p, (ab_size b). rewrite EK.
  split; [rewrite <- EB; exact HbT|]. split; [rewrite <- EK, LINK; unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; lia|].
  split; [exact ESL|]. split; [lia|]. split; [exact A16|]. split; [unfold ablk, AIMG_HI, KLS; exact BK|]. split; [exact HI|].
  split; [exact HTW|]. fold WL in INW. rewrite ESA, ESL in INW. exact INW.
Qed.

Let Oz : Z := bv_unsigned (den E (getr st X12)).
Let Nz : Z := bv_unsigned (den E (getr st X13)).
Let Ez : Z := bv_unsigned (den E (getr st X11)).

Lemma mids : K mod 8 = 0 /\ K < 2 ^ 47
  /\ K <= Oz <= Ez /\ K <= Nz <= Ez /\ Ez <= K + 8 * WL
  /\ (Oz - K) mod 8 = 0 /\ (Nz - K) mod 8 = 0 /\ Ez mod 8 = 0
  /\ hiZ E rsh = (Oz - K) / 8 /\ bv_unsigned (den E h') = (Nz - K) / 8.
Proof.
  destruct twin_data as (p & n & _ & _ & _ & NB & A16 & BK & HI & _). pose proof atop_range as ATR.
  assert (K8 : K mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
  assert (K47 : K < 2 ^ 47) by lia.
  destruct (mid_hi_sound E _ k om (rg_hi rsh) HF MHO K8 ltac:(fold K; lia)) as (O1 & O2 & O3).
  destruct (mid_hi_sound E _ k (getr st X13) h' HF MHN K8 ltac:(fold K; lia)) as (N1 & N2 & N3).
  pose proof (KnownA.TwinB.KnownA.known_eq_sound E _ _ _ HF KEQ) as EO. rewrite <- EO in O1, O2, O3. fold K Oz in O1, O2, O3. fold K Nz in N1, N2, N3.
  pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF NLE) as NE. pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF OLE) as OE. fold Nz Ez in NE. fold Oz Ez in OE.
  pose proof (al8_sv_sound E _ _ HF AL8E) as E8. fold Ez in E8.
  pose proof (CallA.TwinB.annot_end_ok_sound E _ k tlen _ HF ENDIN K8 E8 WMAX K47) as EI. fold K Ez WL in EI.
  repeat (split; [first [assumption | lia]|]). exact N3.
Qed.

Lemma old_zero : forall g, 0 <= g < hiZ E rsh -> rb bsegs m (shad K + g) = Some (Z_to_bv 8 0).
Proof.
  intros g Hg. pose proof (so_reg _ _ _ _ _ _ HS sh rsh Frs) as RO0. destruct twin_data as (p & n & _ & ESH & _).
  pose proof (ro_bg _ _ _ _ _ _ RO0 g) as BGc. unfold bg_byte in BGc. rewrite BG, ESH in BGc. apply BGc.
  - intros _. unfold loZ. rewrite LO0. change (keyZ 0%uint63) with 0. lia.
  - intros X. rewrite SHNZ in X. discriminate X.
  - intros g0 gr _ F. rewrite CELLS in F. discriminate F.
Qed.

Variables (r : int) (st1 : sstate).
Hypothesis CP : call_pre st = Some r.
Hypothesis FS : forget_stack_below_sp_g st = Some st1.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis RO : rg_w rsh = false.
Hypothesis NV : no_views_on (s_facts st) (s_regs st) k sh = true.
Hypothesis TAILS : annot_tails_ok st wnl k sh = true.
Hypothesis OTHERS : annot_others_ok st wnl k sh tlen = true.
Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m.
Hypothesis AWden : aw = den E A.
Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Let lo : Z := CtrPre.TwinB.sp_lo E st.
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis Hksp : okey offs = Some ksp.
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Hypothesis K16 : keyZ ksp mod 16 = 0.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis LOB : ATOP + 4096 <= lo.
Hypothesis LOS : lo <= sp.
Hypothesis SP47 : sp < 2 ^ 47.
Variables (R' : bvmap 5 word) (m' : amem) (mo' : Model).
Hypothesis KEPT : forall rg, In rg CtrFrame.TwinB.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg.
Hypothesis MINV' : ALib.Mem.mem_inv bsegs m'.
Hypothesis STK' : stk bsegs m' lo sp.
Hypothesis MU : munch [(lo, sp); (shad K, shad K + WL)] m m'.
Hypothesis WM : wmono bsegs m m'.

Hypothesis ZERO : forall g, 0 <= g < bv_unsigned (den E h') -> rb bsegs m' (shad K + g) = Some (Z_to_bv 8 0).
Hypothesis AC' : ACCT aw (w_L WW) (w_RNG WW) (w_st WW) (w_LBa WW) mo'.
Hypothesis OTH : OTHER mo mo'.
Hypothesis MINVo : op_minv OPS mo'.

Let TWv : iv := (shad K, WL).
Let AWH : aw_holds_asan AI ACCT UNIV aw LB m mo := aw_real_holds AI ACCT UNIV _ _ _ _ _ AR.

Lemma twin_geo : 0x800be200 <= shad K /\ shad K + WL <= shad ATOP /\ 1 <= WL /\ In TWv LB
  /\ In (Win (shad K) WL K_TWINz) (wins_of E nn rest).
Proof.
  destruct twin_data as (p & n & _ & _ & EWL & NB & _ & BK & HI & INL & INW). rewrite <- EWL in INL, INW.
  destruct (shadow_tight _ _ BK HI ltac:(lia)) as [S1 S2]. rewrite <- EWL in S2.
  assert (W1 : 1 <= WL). { rewrite EWL. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - NB. Z.div_mod_to_equations. lia. }
  auto.
Qed.
Lemma shad_atop_lt : shad ATOP < ATOP /\ shad ATOP <= 0x10007fff8000.
Proof. pose proof atop_range as ATR. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; Z.div_mod_to_equations; lia. Qed.

Lemma raw_out : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < sp) -> ~ (shad K <= a < shad K + WL) -> m' (ALib.Mem.wa a) = m (ALib.Mem.wa a).
Proof.
  intros a Ha N1 N2. apply MU. cbn [ALib.Frame.outside]. unfold ALib.Mem.wa. rewrite Z_to_bv_small by (clear - Ha; zl).
  split; [exact N1|]. split; [exact N2| exact I].
Qed.
Lemma raw_view : forall a, m' (ALib.Mem.wa a) = m (ALib.Mem.wa a) -> rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true).
Proof.
  intros a EQ. split; [unfold rb; unfold ALib.Mem.wa in EQ; rewrite EQ; reflexivity|].
  intros Wb. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in Wb. rewrite (wview_ext1 m' m _ EQ). exact Wb.
Qed.

Lemma twin_mapped' : forall i, 0 <= i < WL -> m' (ALib.Mem.wa (shad K + i)) <> None.
Proof.
  intros i Hi. destruct twin_geo as (S1 & S2 & _ & INL & _). pose proof shad_atop_lt as [SAL SAH]. pose proof atop_range as ATR.
  destruct (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB m mo TWv (shad K + i) AWH INL ltac:(unfold in_iv, TWv; cbn [fst snd]; lia)) as [MP SEG].
  pose proof (WM (ALib.Mem.wa (shad K + i))) as W0. unfold wview in W0. unfold ALib.Mem.wa in *.
  destruct (m (Z_to_bv 64 (shad K + i))) as [b0|] eqn:Q; [| contradiction].
  specialize (W0 ltac:(discriminate)).
  destruct (m' (Z_to_bv 64 (shad K + i))) as [b1|]; [discriminate|]. exfalso. apply W0.
  rewrite Z_to_bv_small by (clear - S1 S2 Hi SAL ATR; zl). rewrite SEG. reflexivity.
Qed.

Definition Wm : wit := mkWit (w_L WW) (w_RNG WW) (w_st WW) (w_LBa WW) (w_T WW) (w_FA WW) m' (w_zc WW).
Lemma WORLD' : aw_realW AI ACCT UNIV aw LB m' mo' Wm.
Proof.
  destruct twin_data as (p & n & HbT & _ & EWL & NB & _).
  assert (AR1 : aw_realW AI ACCT UNIV aw LB m' mo (set_ms WW m')).
  { apply (aw_real_twin_write AI IMGX IMGX_aci ACCT UNIV AI_fake aw LB m mo WW p K n m' lo sp AR HbT (is_primary_le n ltac:(lia)) LOB LOS ltac:(lia)).
    - rewrite <- EWL. exact MU.
    - exact WM.
    - rewrite <- EWL. exact twin_mapped'. }
  destruct (aw_realW_AHEAP AI ACCT UNIV _ _ _ _ _ AR1) as (AH1 & _).
  exact (aw_real_nodelta AI ACCT UNIV AI_fake aw aw LB m' mo (set_ms WW m') (w_RNG WW) (w_st WW) m' mo' AR1 AH1 AC'
           (fun _ _ _ _ _ => eq_refl) (fun _ _ _ _ _ _ _ => eq_refl)).
Qed.
Lemma TIES' : ties Wm (wins_of E nn rest).
Proof. apply (ties_ext WW Wm); [reflexivity| intros b; reflexivity| reflexivity| exact TI| intros b _ V; exact V| intros P; exact P]. Qed.

Let Fv : Z -> word := CtrFree.TwinB.cfvF R'.
Let Gv : Z -> Z -> byte := fun _ _ => Z_to_bv 8 0.
Notation E' := (CtrFrame.TwinB.E' E st Fv Gv).
Let FOK : fresh_ok st = true := proj1 (HeapCtr.TwinB.call_pre_inv st r CP).

Lemma twin_in_heap_ws : forall a, shad K <= a < shad K + WL -> in_ws (heap_ws (wins_of E nn rest)) a.
Proof.
  intros a Ha. destruct twin_geo as (_ & _ & _ & _ & INW). unfold in_ws, heap_ws. apply in_ivs_In. exists (shad K, WL).
  split; [| unfold in_iv; cbn [fst snd]; lia].
  apply in_map_iff. exists (Win (shad K) WL K_TWINz). split; [reflexivity|]. apply filter_In. split; [exact INW| reflexivity].
Qed.
Lemma user_below : forall a, in_user LB a -> 0 <= a < ATOP.
Proof.
  intros a U. pose proof atop_range as ATR. destruct (LB_band AI ACCT UNIV AI_fake WW aw LB m mo a HWw U) as [B|[B|B]]; unfold AIMG_HI, KLS in *; lia.
Qed.

Lemma DECN : decode (map (den E') hargs) = Some (w2Z md, den E A, wins_of E nn rest, map (den E) (skipn (3 * nn) rest)).
Proof. exact (CtrFrame.TwinB.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln). Qed.
Lemma HOLDN : op_holds OPS HEAP_ID (map (den E') hargs) m' mo'.
Proof.
  rewrite OPS_holds1. exists (w2Z md), aw, (wins_of E nn rest), (map (den E) (skipn (3 * nn) rest)), LB, Wm.
  split; [rewrite AWden; exact DECN|]. split; [exact (proj1 WORLD')|]. split; [exact WF|]. split; [| exact TIES'].
  apply (cw_frame Cw _ _ _ _ m m' HC). intros a Ha U NWS. symmetry. pose proof (user_below a U) as UB. pose proof atop_range as ATR.
  apply (raw_out a); [unfold two64 in Ha; lia| lia|]. intros X. exact (NWS (twin_in_heap_ws a X)).
Qed.

Definition LBk : blocks := remove iv_eq_dec TWv LB.
Lemma LBk_In : forall v, In v LBk <-> (In v LB /\ v <> TWv).
Proof. intros v. unfold LBk. split; [intros H; apply in_remove in H; exact H| intros [H N]; apply in_in_remove; assumption]. Qed.
Lemma LBk_sub : forall v, In v LBk -> In v LB.
Proof. intros v H. exact (proj1 (proj1 (LBk_In v) H)). Qed.
Lemma LBk_apart : forall a, in_user LBk a -> ~ (shad K <= a < shad K + WL).
Proof.
  intros a U X. apply in_ivs_In in U as (v & Hv & Hin). apply LBk_In in Hv as [Hv NE]. destruct twin_geo as (_ & _ & _ & INL & _).
  destruct v as [Av nv]. destruct (Z.eq_dec Av (shad K)) as [->|NA].
  - apply NE. unfold TWv. f_equal. exact (LB_same_addr AI ACCT UNIV AI_fake WW aw LB m mo _ _ _ HWw Hv INL).
  - apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB m mo (Av, nv) TWv a AWH Hv INL); [cbn [fst TWv]; exact NA| exact Hin|].
    unfold in_iv, TWv. cbn [fst snd]. lia.
Qed.
Lemma out_low : forall a, 0 <= a < 0x800be200 -> m' (ALib.Mem.wa a) = m (ALib.Mem.wa a).
Proof. intros a Ha. destruct twin_geo as (S1 & _). pose proof atop_range as ATR. apply raw_out; lia. Qed.
Lemma SBVa : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LBk a ->
  rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true).
Proof.
  intros a Ha ST. apply raw_view. destruct twin_geo as (S1 & S2 & _). pose proof shad_atop_lt as [SAL SAH]. pose proof atop_range as ATR.
  destruct ST as [ST|[(iv0 & Hi & RRa)|U]].
  - fold sp in ST. apply raw_out; [exact Ha| lia| lia].
  - pose proof (AI_aci_img AI iv0 Hi) as HIa. pose proof (AI_aci_lo AI iv0 Hi) as LOa. unfold AIMG_HI in HIa. apply out_low. lia.
  - assert (UL : in_user LB a).
    { apply in_ivs_In in U as (v & Hv & Hin). apply in_ivs_In. exists v. split; [exact (LBk_sub v Hv)| exact Hin]. }
    pose proof (user_below a UL) as UB. apply raw_out; [exact Ha| lia| exact (LBk_apart a U)].
Qed.
Lemma shad_mono_facts : forall a', 0 <= a' < 2 ^ 47 -> (a' < AIMG_HI -> shad a' < 0x800be200) /\ (ATOP <= a' -> shad ATOP <= shad a') /\ 0 <= shad a' < 0x10007fff8000.
Proof.
  intros a' Ha. pose proof atop_range as ATR. unfold shad, ASHOFF, AIMG_HI. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  repeat split; intros; Z.div_mod_to_equations; lia.
Qed.
Lemma SBOa : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E') (op_args o))) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
  destruct twin_geo as (S1 & S2 & _). pose proof shad_atop_lt as [SAL SAH]. pose proof atop_range as ATR.
  assert (ACI : forall x, in_ranges (aci AI) x -> 0 <= x < AIMG_HI).
  { intros x (iv0 & Hi & RRa). pose proof (AI_aci_img AI iv0 Hi). pose proof (AI_aci_lo AI iv0 Hi). lia. }
  change (Z_to_bv 64 a) with (ALib.Mem.wa a).
  destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
  - pose proof (ACI a INA) as B. unfold AIMG_HI in B. apply out_low. lia.
  - pose proof (ACI a' INA) as B. destruct (shad_mono_facts a' ltac:(unfold AIMG_HI in B; lia)) as (F1 & _ & F3). apply out_low. specialize (F1 (proj2 B)). lia.
  - destruct (shad_mono_facts a' ltac:(lia)) as (_ & F2 & F3). specialize (F2 (proj1 STK)). apply raw_out; [unfold two64 in Ha; lia| lia| lia].
Qed.
Lemma WBMa : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
  wb bsegs m a = true -> wb bsegs m' a = true.
Proof. intros a _ _ Wb. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in Wb. exact (WM _ Wb). Qed.
Lemma SBTa : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
  rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true).
Proof.
  intros a Ha SC _. apply raw_view. destruct twin_geo as (S1 & S2 & _). pose proof shad_atop_lt as [SAL SAH]. pose proof atop_range as ATR.
  destruct (sh_cov_band a SC) as [B|B]; [apply out_low; lia| apply raw_out; [exact Ha| lia| lia]].
Qed.

Lemma link_den : forall k0 k2, block_of_twin (s_facts st) k0 = Some k2 -> bv_unsigned (ev E k0) = bv_unsigned (ev E k2) / 8 + 0x7fff8000.
Proof.
  intros k0 k2 B2. rewrite (CallA.TwinB.block_of_twin_sound E _ k0 k2 HF B2). apply Z.mod_small.
  pose proof (bv_unsigned_in_range 64 (ev E k2)) as R2. unfold bv_modulus in R2. change (2 ^ Z.of_N 64) with (2 ^ 64) in R2. clear - R2. Z.div_mod_to_equations. lia.
Qed.
Lemma K_facts : K mod 8 = 0 /\ 6492160 <= K < 2 ^ 47 /\ k <> 0%uint63.
Proof.
  destruct twin_data as (p & n & _ & _ & _ & NB & A16 & BK & HI & _). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  split; [clear - A16; Z.div_mod_to_equations; lia|]. split; [lia|]. intros ->. unfold K in BK.
  rewrite (so_zero _ _ _ _ _ _ HS) in BK. rewrite Z_to_bv_unsigned in BK. change (bv_wrap 64 0) with 0 in BK. lia.
Qed.

Lemma other_block_ne : forall k2, k2 <> k ->
  ((In k (carg_vecs st) /\ In k2 (carg_vecs st)) \/ (In k (carg_vecs st) /\ blk_win_pos st wnl k2 = true)
   \/ (blk_win_pos st wnl k = true /\ In k2 (carg_vecs st)) \/ (blk_reg_w st k = true /\ blk_reg_w st k2 = true)) ->
  bv_unsigned (ev E k2) <> K.
Proof.
  intros k2 NE EV. destruct K_facts as (K8 & KB & KNZ).
  assert (WINB : forall x n, CtrA.win_lookup wnl x = Some (n, CtrLib.K_BLOCK) -> KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) n = true ->
            exists w, In w (wins_of E nn rest) /\ w_kind w = K_BLOCK /\ 0 < w_len w /\ w_lo w = bv_unsigned (ev E x)).
  { intros x n WLx P. destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl x n CtrLib.K_BLOCK NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLx)) as (_ & _ & _ & INx).
    pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF P) as P0. replace (bv_unsigned (den E (VL wzero))) with 0 in P0 by (vm_compute; reflexivity).
    eexists. split; [exact INx|]. cbn [w_kind w_len w_lo]. auto. }
  assert (Hf' : find_op HEAP_ID (s_ops st) = Some (VL md :: A :: VL nw :: rest)) by (rewrite <- Eh; exact Hf).
  destruct EV as [[CV1 CV2]|[[CV BW]|[[BW CV]|[RW1 RW2]]]].
  - destruct (Z.eq_dec (bv_unsigned (ev E k2)) 0) as [Z0|NZ0]; [lia|].
    destruct (CallA.TwinB.carg_vecs_spec st md A nw rest k Hf' CV1) as (i & Hi & NEi). destruct (CallA.TwinB.carg_vecs_spec st md A nw rest k2 Hf' CV2) as (j & Hj & NEj).
    rewrite <- Nn in NEi, NEj.
    assert (IJ : i <> j) by (intros ->; rewrite NEi in NEj; injection NEj as X; exact (NE (eq_sym X))).
    pose proof (Cw_vecs_distinct _ _ _ _ _ i j (den E (VP k wzero)) (den E (VP k2 wzero)) HC Hi Hj IJ (map_nth_error (den E) _ _ NEi) (map_nth_error (den E) _ _ NEj)) as X.
    rewrite !HeapCtr.TwinB.den_VPz in X. fold K in X. intros EQ. apply X; [lia| exact NZ0| symmetry; exact EQ].
  - destruct (blk_win_pos_inv _ _ _ BW) as (n2 & WL2 & P2). destruct (WINB k2 n2 WL2 P2) as (w & Hw & KW & PW & LOW).
    pose proof (CtrFree.TwinB.cvu_of Cw Cw_vec_unowned E st m LB nn md A nw rest Hf' Nn HC k CV ltac:(fold K; lia) w Hw KW PW) as X. fold K in X. lia.
  - destruct (blk_win_pos_inv _ _ _ BW) as (n1 & WL1 & P1). destruct (WINB k n1 WL1 P1) as (w & Hw & KW & PW & LOW). fold K in LOW.
    destruct (Z.eq_dec (bv_unsigned (ev E k2)) 0) as [Z0|NZ0]; [lia|].
    pose proof (CtrFree.TwinB.cvu_of Cw Cw_vec_unowned E st m LB nn md A nw rest Hf' Nn HC k2 CV NZ0 w Hw KW PW) as X. lia.
  - destruct (blk_reg_w_inv _ _ RW1) as (r1 & F1 & W1 & L1 & P1). destruct (blk_reg_w_inv _ _ RW2) as (r2 & F2 & W2 & L2 & P2).
    destruct (Uint63.eqb k2 0%uint63) eqn:Q2.
    { apply Uint63.eqb_correct in Q2. subst k2. rewrite (so_zero _ _ _ _ _ _ HS), Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. lia. }
    intros EQ.
    pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF P1) as H1. pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF P2) as H2.
    replace (bv_unsigned (den E (VL wzero))) with 0 in H1, H2 by (vm_compute; reflexivity). fold (hiZ E r1) in H1. fold (hiZ E r2) in H2.
    assert (LZ : forall r0, rg_lo r0 = 0%uint63 -> loZ r0 = 0) by (intros r0 L; unfold loZ; rewrite L; reflexivity).
    apply (so_disj _ _ _ _ _ _ HS k r1 k2 r2 F1 F2 (fun X => NE (eq_sym X)) ltac:(apply Uint63.eqb_false_spec; exact KNZ) Q2 (or_introl W1) K).
    fold K. rewrite EQ, (LZ r1 L1), (LZ r2 L2). lia.
Qed.

Definition KEEPa (k0 : int) : Prop := k0 <> sh.
Lemma others_apart : forall k0 len kd a, KEEPa k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> ~ (shad K <= a < shad K + WL).
Proof.
  intros k0 len kd a KP WL0 Ha X. pose proof (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL0) as Hin.
  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k0 len kd NW Hin) as (_ & _ & KD & INW0).
  destruct twin_geo as (S1 & S2 & W1 & INL & INWT). destruct twin_data as (p & n & HbT & ESH & EWL & NB & A16 & BK & HI & _).
  pose proof TI as (_ & T2 & _ & T4 & T5 & _ & _ & _ & _ & GA & _). pose proof HWw as (AH & _).
  set (w0 := Win (bv_unsigned (ev E k0)) (bv_unsigned (den E len)) (w2Z kd)) in *. set (wT := Win (shad K) WL K_TWINz) in *.
  assert (IN0 : in_iv (w_iv w0) a) by (unfold in_iv, w_iv, w0; cbn [w_lo w_len fst snd]; lia).
  assert (INT : in_iv (w_iv wT) a) by (unfold in_iv, w_iv, wT; cbn [w_lo w_len fst snd]; lia).
  destruct (twin_T_facts AI ACCT UNIV WW aw LB m mo _ HWw HbT) as (HbL & _). cbn [ab_addr ab_size] in *.

  assert (HULL : forall b' n', (In b' (w_T WW) \/ visf WW b') -> b' <> HB p K n -> n' <= ab_size b' + 7 ->
            shad (ab_addr b') <= a < shad (ab_addr b') + shlen n' -> False).
  { intros b' n' HB' NEb LEn Hb'a. destruct (LB_shadow_hull AI ACCT UNIV AI_fake WW aw LB m mo b' HWw HB') as (H1 & H2 & H3 & H4).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB p K n) b' AH HbL H1 (fun Q => NEb (eq_sym Q))) as D. cbn [ab_addr ab_size] in D.
    assert (SL : shlen n' <= shlen (ab_size b' + 7)).
    { unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. apply Z.div_le_mono; lia. }
    apply (gran_disj K n (ab_addr b') (ab_size b') a); [unfold ablk, AIMG_HI in BK; lia| exact H2| lia| lia| exact D| clear - A16; Z.div_mod_to_equations; lia| exact H4| rewrite <- EWL; exact X| lia]. }
  destruct (annot_others_inv st wnl k sh tlen k0 len kd OTHERS Hin KP) as [(NKT & WTk & LEk)|(-> & EV)].
  -
    assert (KZ : w2Z kd = to_Z (wl kd)) by (unfold w2Z; rewrite WTk; lia). pose proof (int_range (wl kd)) as RK0.
    assert (CASES : w2Z kd = K_BLOCK \/ (K_SUB <= w2Z kd < K_GHOST) \/ w2Z kd = K_FRAMEz \/ w2Z kd = K_FTWINz) by (unfold K_BLOCK, K_SUB, K_GHOST, K_FRAMEz, K_FTWINz; lia).
    destruct CASES as [C1|[C2|[C7|C8]]].
    + exact (GA wT w0 INWT INW0 ltac:(cbn; unfold K_GHOST, K_TWINz; lia) C1 a INT IN0).
    + exact (Cw_sub_ghost _ _ _ _ _ w0 wT a HC INW0 INWT C2 ltac:(cbn; unfold K_GHOST, K_TWINz; lia) IN0 INT).
    + destruct (T4 w0 INW0 C7) as (b' & Vb' & EIV). unfold w_iv, user_iv, w0 in EIV. cbn [w_lo w_len] in EIV. injection EIV as EA EL.
      destruct (LB_user_facts AI ACCT UNIV AI_fake WW aw LB m mo b' HWw (proj1 Vb')) as (_ & B1 & _). pose proof (usz_le b') as UL.
      pose proof shad_atop_lt as [SAL SAH]. pose proof atop_range as ATR. lia.
    + destruct (T5 w0 INW0 C8) as (b' & Vb' & EIV). unfold w_iv, fsh_iv, w0 in EIV. cbn [w_lo w_len] in EIV. injection EIV as EA EL.
      apply (HULL b' (ab_size b') (or_intror Vb')); [intros ->; exact (heap_not_fake (HB p K n) ltac:(exists p; reflexivity) (proj2 Vb'))| lia| lia].
  -
    rewrite KT9 in *. destruct (T2 w0 INW0 eq_refl) as (b0 & Hb0 & EIV). unfold w_iv, twin_iv, w0 in EIV. cbn [w_lo w_len] in EIV. injection EIV as EA EL.
    apply (HULL b0 (ab_size b0 + 7) (or_introl Hb0)); [| lia| lia].
    intros ->. cbn [ab_addr ab_size] in EA, EL.
    destruct EV as [(l0 & wlen & ELEN & -> & NEl)|(k2 & B2 & NE2 & AL2 & EV2)].
    + apply NEl. apply w2Z_inj. cbn [den] in EL. rewrite wbv_unsigned in EL. rewrite EL, <- EWL. unfold WL. rewrite ELEN. cbn [den]. rewrite wbv_unsigned. reflexivity.
    + pose proof (other_block_ne k2 NE2 EV2) as NEK. pose proof (link_den k0 k2 B2) as LK.
      pose proof (ValP.find_align_le E _ HF k2 3%uint63 AL2) as A8. change (2 ^ to_Z 3%uint63) with 8 in A8.
      destruct K_facts as (K8 & _). rewrite EA in LK. unfold shad, ASHOFF in LK. rewrite Z.shiftr_div_pow2 in LK by lia. change (2 ^ 3) with 8 in LK.
      clear - LK A8 K8 NEK. Z.div_mod_to_equations. lia.
Qed.
Lemma WINKa : forall k0 len kd, KEEPa k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LBk a.
Proof.
  intros k0 len kd KP WL0 a Ha. pose proof (others_apart k0 len kd a KP WL0 Ha) as AP0.
  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k0 len kd NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL0)) as (_ & _ & KD & INW).
  assert (NT : forall b, In b LB -> in_iv b a -> In b LBk).
  { intros b Hb Hin. apply LBk_In. split; [exact Hb|]. intros ->. unfold in_iv, TWv in Hin. cbn [fst snd] in Hin. exact (AP0 Hin). }
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
  - exfalso. exact (KD KS0).
  - apply in_ivs_In. eexists. split; [apply (NT _ B); unfold in_iv; cbn [fst snd]; lia| unfold in_iv; cbn [fst snd]; lia].
  - apply in_ivs_In. exists b. assert (Hin : in_iv b a) by (apply SUB; unfold in_iv; cbn [fst snd]; lia). split; [exact (NT b Hb Hin)| exact Hin].
Qed.
Lemma VKEEPa : forall k0 rg hs n sh' len, IMap.find k0 (s_regs st) = Some rg -> zero_view rg = Some hs -> KEEPa k0 ->
  block_of_twin (s_facts st) k0 = Some n -> CallV.TwinB.view_parent (s_facts st) (s_regs st) n sh' ->
  CtrA.win_lookup wnl sh' = Some (len, K_TWIN) -> KEEPa sh'.
Proof.
  intros k0 rg hs n sh' len Fk ZV NKs BT0 VPAR WL0. intros ->. unfold no_views_on in NV.
  pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) NV k0 rg Fk) as C. cbv beta in C.
  replace (PrimInt63.eqb k0 sh) with false in C by (symmetry; apply Uint63.eqb_false_spec; exact NKs).
  rewrite ZV, BT0 in C. destruct VPAR as [(kb & o1 & UB & TW)|(rshp & Frshp & HNp)];
      [rewrite UB, TW, Uint63.eqb_refl in C; cbn in C; discriminate C| rewrite Frshp, HNp in C; cbn [negb] in C; rewrite !Bool.andb_false_r in C; discriminate C].
Qed.
Lemma TKEEPa : forall k0 rg sh' kb n len, IMap.find k0 (s_regs st) = Some rg -> KEEPa k0 -> CtrA.win_lookup wnl sh' = Some (len, K_TWIN) ->
  block_of_twin (s_facts st) sh' = Some kb -> CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK) ->
  size_tail_ok (s_facts st) n = true -> tail_named (tail_rhs sh' n) k0 (s_facts st) = true -> KEEPa sh'.
Proof.
  intros k0 rg sh' kb n len Fk NKs WL0 BT0 WLk ST TN. intros ->. rewrite BT in BT0. injection BT0 as <-.
  unfold annot_tails_ok in TAILS. rewrite WLk in TAILS.
  pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) TAILS k0 rg Fk) as C. cbv beta in C. rewrite TN in C. discriminate C.
Qed.
Lemma KEEP_dela : forall k0, ~ In k0 [sh] -> KEEPa k0.
Proof. intros k0 H ->. apply H. left. reflexivity. Qed.

Let H' : Z := bv_unsigned (den E h').
Lemma H'_le : 0 <= H' <= WL.
Proof.
  destruct mids as (_ & _ & _ & (N1 & N2) & EI & _ & N8 & _ & _ & EH). fold H' in EH. rewrite EH. clear - N1 N2 EI. Z.div_mod_to_equations. lia.
Qed.
Lemma h'_den : bv_unsigned (den E' h') = bv_unsigned (den E h').
Proof.
  pose proof (CtrFrame.TwinB.reg_below st FOK X13) as B13. pose proof (CtrFrame.TwinB.reg_below st FOK X10) as B10. rewrite X10E in B10. cbn [sv_vars_below] in B10.
  assert (BEL : sv_vars_below (s_next st) h' = true -> bv_unsigned (den E' h') = bv_unsigned (den E h')) by (intros B; rewrite (CtrFrame.TwinB.den_E' E st Fv Gv h' B); reflexivity).
  pose proof MHN as MH. unfold mid_hi in MH. destruct (getr st X13) as [|n o|op a xs| | | | | | | |]; try discriminate MH; cbn [sv_vars_below] in B13.
  - apply BEL. destruct (PrimInt63.eqb n k); [destruct (al8 o); [injection MH as <-; reflexivity| discriminate MH]|].
    destruct (find_lb_to (s_facts st) n k); [|discriminate MH].
    match type of MH with (if ?c then _ else _) = _ => destruct c; [|discriminate MH] end. injection MH as <-.
    unfold vec_hi. cbn [sv_vars_below]. rewrite B13, B10. reflexivity.
  - destruct op; try discriminate MH. destruct a as [|k' z| | | | | | | | |]; try discriminate MH.
    match type of MH with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate MH] end. injection MH as <-.
    apply andb_prop in C as [C _]. apply andb_prop in C as [_ XS].
    apply andb_prop in B13 as [_ BX].
    pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF XS) as X8. replace (bv_unsigned (den E (VL SYMCAPw))) with 65536 in X8 by (vm_compute; reflexivity).
    rewrite (CallA.TwinB.twin_len_den E' xs) by (rewrite (CtrFrame.TwinB.den_E' E st Fv Gv xs BX); lia). rewrite (CallA.TwinB.twin_len_den E xs) by lia.
    rewrite (CtrFrame.TwinB.den_E' E st Fv Gv xs BX). reflexivity.
Qed.
Lemma sh_E' : bv_unsigned (ev E' sh) = shad K /\ hiZ E' (annot_rsh h') = H' /\ loZ (annot_rsh h') = 0.
Proof.
  destruct (CtrFrame.TwinB.reg_E' OPS E st ms mo HS FOK Fv Gv sh rsh Frs) as (Ek & _). destruct twin_data as (p & n & _ & ESH & _).
  split; [rewrite Ek; exact ESH|]. split; [| reflexivity]. unfold hiZ, annot_rsh. cbn [rg_hi]. exact h'_den.
Qed.
Definition newRa : list (int * region) := [(sh, annot_rsh h')].
Definition NEWSETa (a : Z) : Prop := shad K <= a < shad K + H'.
Lemma newRa_ok : forall k0 rg, In (k0, rg) newRa -> region_ok bsegs (s_priv st) E' m' k0 rg.
Proof.
  intros k0 rg [X|[]]. injection X as <- <-. destruct sh_E' as (ESH & EHI & ELO). pose proof H'_le as HL.
  destruct twin_geo as (S1 & S2 & _ & INL & _). pose proof shad_atop_lt as [SAL SAH].
  constructor.
  - apply IMap.bst_empty.
  - intros _. rewrite ESH, EHI, ELO. unfold two64. lia.
  - intros _ a Ha. rewrite ESH, EHI, ELO in Ha. split; [| split; [intros X; discriminate X|]].
    + replace a with (shad K + (a - shad K)) by lia. rewrite (ZERO (a - shad K)) by (fold H'; lia). discriminate.
    + exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB m mo TWv a AWH INL ltac:(unfold in_iv, TWv; cbn [fst snd]; lia))).
  - intros g gr F. unfold annot_rsh in F. cbn [rg_cells] in F. rewrite IMap.find_empty in F. discriminate F.
  - intros g gr c i F. unfold annot_rsh in F. cbn [rg_cells] in F. rewrite IMap.find_empty in F. discriminate F.
  - intros o H1 _ _. unfold bg_byte, annot_rsh. cbn [rg_bg]. specialize (H1 SHNZ). rewrite EHI, ELO in H1. rewrite ESH. apply ZERO. fold H'. lia.
Qed.
Lemma newRa_range : forall k0 rg a, In (k0, rg) newRa -> bv_unsigned (ev E' k0) + loZ rg <= a < bv_unsigned (ev E' k0) + hiZ E' rg -> NEWSETa a.
Proof. intros k0 rg a [X|[]] Ha. injection X as <- <-. destruct sh_E' as (ESH & EHI & ELO). rewrite ESH, EHI, ELO in Ha. unfold NEWSETa. lia. Qed.
Lemma newRa_low : forall a, NEWSETa a -> AIMG_HI <= a < ATOP + 4096 /\ ~ in_user LBk a.
Proof.
  intros a Ha. unfold NEWSETa in Ha. pose proof H'_le as HL. destruct twin_geo as (S1 & S2 & _). pose proof shad_atop_lt as [SAL SAH]. unfold AIMG_HI.
  split; [lia|]. intros U. apply (LBk_apart a U). lia.
Qed.
Lemma newRa_nosh : forall a, NEWSETa a -> ~ (0x7fff8000 <= a < 0x800be200).
Proof. intros a Ha. unfold NEWSETa in Ha. destruct twin_geo as (S1 & _). lia. Qed.
Lemma newRa_nostk : forall a, NEWSETa a -> ~ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Proof.
  intros a Ha (a' & Ra & ->). unfold NEWSETa in Ha. pose proof H'_le as HL. destruct twin_geo as (_ & S2 & _).
  destruct (shad_mono_facts a' ltac:(pose proof atop_range; lia)) as (_ & F2 & _). specialize (F2 (proj1 Ra)). lia.
Qed.
Lemma newRa_disj : forall k1 r1 k2 r2 a, In (k1, r1) newRa -> In (k2, r2) newRa -> k1 <> k2 -> (rg_w r1 = true \/ rg_w r2 = true) ->
  ~ (bv_unsigned (ev E' k1) + loZ r1 <= a < bv_unsigned (ev E' k1) + hiZ E' r1 /\ bv_unsigned (ev E' k2) + loZ r2 <= a < bv_unsigned (ev E' k2) + hiZ E' r2).
Proof. intros k1 r1 k2 r2 a [X1|[]] [X2|[]] NE. injection X1 as <- _. injection X2 as <- _. contradiction. Qed.
Lemma newRa_nodup : List.NoDup (map fst newRa).
Proof. cbn. constructor; [intros []| constructor]. Qed.
Lemma newRa_nz : forall k0 rg, In (k0, rg) newRa -> PrimInt63.eqb k0 0%uint63 = false.
Proof. intros k0 rg [X|[]]. injection X as <- _. exact SHNZ. Qed.

Definition RgA : IMap.t region := CtrFrame.TwinB.RgPg st ks rss ksp newRa [sh].
Lemma annot_shape : annot_post st1 r sh h'
  = SS r (rf_set (s_rf (clobber st1)) X10 (VP (addn (s_next st) 15) wzero)) (s_ff st) (s_resv st) RgA (s_facts st)
       (set_op HEAP_ID hargs (s_ops st)) (s_priv st) (PrimInt63.add (addn (s_next st) 15) 1%uint63).
Proof.
  assert (G : forall (S : sstate) R0 nx1 v, setpc (setr (set_next (setregs S R0) nx1) X10 v) r
              = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) R0 (s_facts S) (s_ops S) (s_priv S) nx1) by (intros [] ? ? ?; reflexivity).
  unfold annot_post. cbv zeta. unfold fresh. cbn [fst snd]. rewrite G.
  destruct (clobber_fields st1) as (_ & FF & RV & _ & FS0' & OP & PV & NXc).
  destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (XE : s_next (setregs (clobber st1) (IMap.add sh (annot_rsh h') (IMap.remove sh (s_regs st1)))) = addn (s_next st) 15).
  { assert (SN : forall (S : sstate) R0, s_next (setregs S R0) = s_next S) by (intros [] ?; reflexivity).
    rewrite SN, NXc, NX1. symmetry. destruct (CtrFrame.TwinB.NX st FOK) as (_ & _ & B). pose proof (int_range (s_next st)) as RRn. rewrite two63_eq in RRn.
    apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]. }
  rewrite XE, FF, RV, FS0', OP, PV, FF1, RV1, FS1, OP1, PV1. rewrite (CtrNoDelta.TwinB.set_op_same HEAP_ID hargs (s_ops st) Hf).
  rewrite (CtrFrame.TwinB.st1_regs st st1 FS ks offs rss ksp SPR Hksp). reflexivity.
Qed.

Theorem annot_post_ok : st_ok bsegs OPS E' (annot_post st1 r sh h') (CtrFrame.TwinB.ms' ms r R' m') mo'.
Proof.
  rewrite annot_shape.
  apply (CtrFrame.TwinB.frame_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo' KEPT (fun x i Hx => CtrFree.TwinB.cfvF_clob R' x i Hx) aw LB LBk AWH MINV' SBVa SBOa WBMa SBTa
           ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPa WINKa VKEEPa TKEEPa
           K16 LOSP STK' FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln OTH newRa [sh] newRa_nodup
           newRa_nz KEEP_dela NEWSETa newRa_ok newRa_range newRa_low newRa_nosh newRa_nostk newRa_disj
           hargs (w2Z md) (den E A) (wins_of E nn rest) (map (den E) (skipn (3 * nn) rest)) DECN HOLDN).
  -   intros a Ha. unfold NEWSETa in Ha. pose proof H'_le as HL. apply twin_in_heap_ws. lia.
  -   intros a _ _ NWS. left. exact NWS.
  -   intros a _ X. exact X.
  - exact (so_facts _ _ _ _ _ _ (CtrFrame.TwinB.HS' OPS E st ms mo HS FOK Fv Gv)).
  - rewrite HeapCtr.TwinB.den_VPz. rewrite (CtrFrame.TwinB.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). reflexivity.
  - exact MINVo.
Qed.
End POST.

Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).

Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Definition acct_leaf_silent (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa mo'.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent mo aw L st LBa).

Lemma rw_cells_of_rb : forall (m : amem) A cs,
  cells_wf cs -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  (forall i, (i < length (cells_bytes cs))%nat -> rb bsegs m (A + Z.of_nat i) = nth_error (cells_bytes cs) i) ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> wb bsegs m (A + i) = true) ->
  ALib.Step.rw_cells bsegs m A cs.
Proof.
  intros m A cs WF HA HB HR HW. pose proof (cells_bytes_length cs WF) as L. split.
  - split; [exact WF|]. split; [exact HA|]. split; [rewrite L; exact HB|].
    intros i Hi. rewrite <- (GlueA.TwinB.rb_mrdA bsegs). exact (HR i Hi).
  - split; [exact HA|]. split; [exact HB|]. intros i Hi. apply (GlueA.TwinB.wb_wviewA bsegs). exact (HW i Hi).
Qed.
Lemma mapped_chunk : forall (m : amem) n A,
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> wb bsegs m (A + i) = true /\ rb bsegs m (A + i) <> None) ->
  exists j, ALib.Step.rw_cells bsegs m A [CB n j].
Proof.
  intros m n. induction n as [|n IH]; intros A HA HB H.
  - exists []. apply rw_cells_of_rb; [cbn; auto| exact HA| cbn; lia| intros i Hi; cbn in Hi; lia| intros i Hi; cbn in Hi; lia].
  - destruct (H 0 ltac:(lia)) as [_ R0]. rewrite Z.add_0_r in R0. destruct (rb bsegs m A) as [b|] eqn:Eb; [|congruence].
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as [j Hj].
    { intros i Hi. replace (A + 1 + i) with (A + (i + 1)) by lia. apply H. lia. }
    exists (b :: j). destruct Hj as [[WF (_ & _ & BY)] _]. cbn [cells_wf cell_wf cells_bytes cbytes app] in WF, BY. rewrite app_nil_r in BY.
    apply rw_cells_of_rb.
    + pose proof (proj1 WF) as WL. simpl in WL. simpl. split; [|exact I]. f_equal. exact WL.
    + exact HA.
    + cbn [cells_size csize Nat.add]. lia.
    + cbn [cells_bytes cbytes app]. rewrite app_nil_r. intros i Hi. destruct i as [|i]; cbn [nth_error].
      * rewrite Z.add_0_r. exact Eb.
      * rewrite (GlueA.TwinB.rb_mrdA bsegs). replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply BY. cbn [length] in Hi. lia.
    + cbn [cells_size csize Nat.add]. intros i Hi. apply H. lia.
Qed.

Lemma shad_off : forall K X, 0 <= K <= X -> K mod 8 = 0 -> (X - K) mod 8 = 0 -> shad X = shad K + (X - K) / 8.
Proof. intros K X R K8 X8. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. Qed.
Lemma shlen_div : forall s, 0 <= s -> shlen s = s / 8.
Proof. intros s S0. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Definition annot_Q (R F : bvmap 5 word) (fc : bv 32) (lo sp K WL H' : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) t0 t1 t2 (AP.getr R 8) (AP.getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
                  (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
                  (AP.getr R 26) (AP.getr R 27) t3 t4 t5 t6) F (MState.ret_pc (AP.getr R 1)) fc None m' (seg_rom bsegs)
    /\ munch [(lo, sp); (shad K, shad K + WL)] m m' /\ wmono bsegs m m' /\ ALib.Mem.mem_inv bsegs m' /\ stk bsegs m' lo sp
    /\ (forall g, 0 <= g < H' -> rb bsegs m' (shad K + g) = Some (Z_to_bv 8 0)).

Theorem annotate_sound : forall pc, to_Z pc = F_annot.TwinB.F_annot.AANNOT -> contract_sound bsegs OPS MP PB (annotate_c pc).
Proof.
  intros pc Hpc st sts Hspc Happ Kt E ms mo HS HMP HPB HK. cbn [c_apply c_pc annotate_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = F_annot.TwinB.F_annot.AANNOT) by (rewrite Hspc; exact Hpc).
  destruct (annotate_apply_shape st sts Happ) as (r & hargs & wnl & st1 & k & sh & rsh & tlen & om & h' & PRE & X10E & Frs & WLt & MHN & MHO & SHNZ & ALK & BT
      & TSM & RO & LO0 & CELLS & BG & KEQ & NLE & OLE & AL8E & ENDIN & NV & TAILS & OTHERS & ESTS).
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ANNOT_ROOM None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct WOF as (E1 & E2 & E3 & E4).
  set (R := ms_regs ms) in *. set (sp := bv_unsigned (AP.getr R 2)) in *. set (m := ms_mem ms) in *. set (lo := CtrPre.TwinB.sp_lo E st) in *.
  pose proof atop_range as ATR. pose proof (so_facts _ _ _ _ _ _ HS) as HFs.
  pose proof (CallA.TwinB.twin_small_sound E _ _ HFs TSM) as WMAX.
  destruct (twin_data E st ms mo HS wnl nn rest LB aw NW W ARW TI k sh tlen WLt ALK BT WMAX) as (p & n & HbT & ESH & EWL & NB & A16 & BK & HI & INL & INW).
  destruct (mids E st ms mo HS wnl nn rest LB aw NW W ARW TI k sh rsh tlen om h' WLt MHN MHO ALK BT WMAX KEQ NLE OLE AL8E ENDIN)
    as (K8 & K47 & (O1 & O2) & (N1 & N2) & EI & O8 & N8 & E8 & EH & EH').
  set (K := bv_unsigned (ev E k)) in *. set (WL := bv_unsigned (den E tlen)) in *.
  set (Oz := bv_unsigned (den E (getr st X12))) in *. set (Nz := bv_unsigned (den E (getr st X13))) in *. set (Ez := bv_unsigned (den E (getr st X11))) in *.
  set (H' := bv_unsigned (den E h')) in *.
  assert (KB : 6492160 <= K) by (unfold ablk, AIMG_HI, KLS in BK; lia).

  assert (REGV : forall x, AP.getr R (reg_of_r5 x) = Z_to_bv 64 (bv_unsigned (den E (getr st x)))).
  { intros x. unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS x). symmetry. apply Z_to_bv_bv_unsigned. }
  assert (Ha0 : AP.getr R 10 = Z_to_bv 64 K) by (rewrite <- HeapCtr.TwinB.reg_of_X10, REGV, X10E, HeapCtr.TwinB.den_VPz; reflexivity).
  assert (Ha1 : AP.getr R 11 = Z_to_bv 64 Ez) by (rewrite <- HeapCtr.TwinB.reg_of_X11, REGV; reflexivity).
  assert (Ha2 : AP.getr R 12 = Z_to_bv 64 Oz) by (rewrite <- HeapCtr.TwinB.reg_of_X12, REGV; reflexivity).
  assert (Ha3 : AP.getr R 13 = Z_to_bv 64 Nz).
  { assert (RX : reg_of_r5 X13 = 13%bv) by (apply bv_eq; reflexivity). rewrite <- RX, REGV. reflexivity. }

  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT. pose proof (AI_relro AI _ _ _ _ _ AH) as RELRO.
  destruct RT as (_ & GOT6 & _ & REALM & SHB & _ & _ & LAY & CANP & _ & _ & _ & CF120 & _ & _ & _ & _ & _ & _ & _ & _ & DCO & VERB).
  assert (GMS : ALib.Step.rw_cells bsegs m 0xd3650 [C8 (Z_to_bv 64 0xd5540)])
    by (apply (AFake_arep.TwinB.AFake_arep.relro_word m 0xd3650 0xd5540 RELRO); [unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
  assert (GVB : ALib.Step.rw_cells bsegs m 0xd3680 [C8 (Z_to_bv 64 0x16b718)])
    by (apply (AFake_arep.TwinB.AFake_arep.relro_word m 0xd3680 0x16b718 RELRO); [unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
  assert (PC : F_apoison.TwinB.F_apoison.poison_cells m) by (unfold F_apoison.TwinB.F_apoison.poison_cells; repeat (split; [assumption|]); assumption).
  assert (ANC : F_annot.TwinB.F_annot.annot_cells m) by (unfold F_annot.TwinB.F_annot.annot_cells; repeat (split; [assumption|]); assumption).

  pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW) as AWH.
  destruct (shadow_tight _ _ BK HI ltac:(lia)) as [S1 S2]. rewrite <- EWL in S2, INL.
  assert (SAL : shad ATOP < ATOP /\ shad ATOP <= 0x10007fff8000).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; Z.div_mod_to_equations; lia. }
  assert (CHUNK : forall a len, shad K <= a -> 0 <= len -> a + len <= shad K + WL -> exists junk, ALib.Step.rw_cells bsegs m a [CB (Z.to_nat len) junk]).
  { intros a len A1 L0 A2. apply mapped_chunk; [lia| rewrite Z2Nat.id by lia; lia|]. intros i Hi. rewrite Z2Nat.id in Hi by lia.
    destruct (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB m mo (shad K, WL) (a + i) AWH INL ltac:(unfold in_iv; cbn [fst snd]; lia)) as [MP0 SEG].
    split.
    - apply (GlueA.TwinB.wb_wviewA bsegs). unfold wview, GlueA.TwinB.AMem.wa. destruct (m (Z_to_bv 64 (a + i))); [discriminate| contradiction].
    - unfold rb. destruct (m (Z_to_bv 64 (a + i))); [discriminate| contradiction]. }
  destruct (twin_T_facts AI ACCT UNIV W aw LB m mo _ (proj1 ARW) HbT) as (HbL & _). rewrite E4 in HbL.
  destruct (AI_block AI _ _ _ _ _ p K n AH HbL) as (_ & _ & _ & RNGT & _). rewrite <- EWL in RNGT.
  set (H := hiZ E rsh) in *.
  pose proof (old_zero E st ms mo HS wnl nn rest LB aw NW W ARW TI k sh rsh tlen Frs WLt SHNZ ALK BT WMAX LO0 CELLS BG) as OLDZ. fold K H m in OLDZ.
  assert (SHO : shad Oz = shad K + H) by (rewrite EH; apply shad_off; lia).
  assert (SHN : shad Nz = shad K + H') by (rewrite EH'; apply shad_off; lia).
  assert (HLE : 0 <= H <= WL /\ 0 <= H' <= WL) by (rewrite EH, EH'; clear - O1 O2 N1 N2 EI; split; Z.div_mod_to_equations; lia).
  change (to_Z ANNOT_ROOM) with 4096 in LOR. fold sp in LOR, ST, SPT, SP16, RSTK. fold lo in LOR, ST, BOT, LO, RSTK.
  assert (OUTV : forall (m' : amem) a0 len0, shad K <= a0 -> a0 + len0 <= shad K + WL ->
             munch [(sp - F_annot.TwinB.F_annot.ANNOT_STACK, sp); (a0, a0 + len0)] m m' -> munch [(lo, sp); (shad K, shad K + WL)] m m').
  { intros m' a0 len0 A1 A2 MU. eapply munch_weaken; [| exact MU]. intros x OUT. cbn [ALib.Frame.outside] in *. unfold F_annot.TwinB.F_annot.ANNOT_STACK. lia. }
  assert (KEEPZ : forall (m' : amem) g, 0 <= g < H -> m' (ALib.Mem.wa (shad K + g)) = m (ALib.Mem.wa (shad K + g)) -> rb bsegs m' (shad K + g) = Some (Z_to_bv 8 0)).
  { intros m' g Hg EQ. rewrite <- (OLDZ g Hg). unfold rb. unfold ALib.Mem.wa in EQ. rewrite EQ. reflexivity. }
  assert (OUTS : forall x, shad K <= x < shad K + WL -> ~ (sp - F_annot.TwinB.F_annot.ANNOT_STACK <= x < sp)) by (intros x Hx; unfold F_annot.TwinB.F_annot.ANNOT_STACK; lia).
  assert (UW : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (ALib.Mem.wa x) = x) by (intros x Hx; unfold ALib.Mem.wa; apply Z_to_bv_small; clear - Hx; zl).
  assert (BLKE : Ez <= 2 ^ 47 /\ ((AIMG_HI <= K /\ K + 8 * WL <= KLS) \/ (0x10007fff8000 <= K /\ K + 8 * WL <= ATOP))).
  { pose proof ATOP_al16 as AT16. assert (WLE : WL = (n + 7) / 8) by (rewrite EWL; apply shlen_div; lia).
    unfold ablk, AIMG_HI, KLS in *. clear - WLE BK HI A16 AT16 NB EI ATR. split; [| destruct BK as [BK|BK]; [left| right]]; Z.div_mod_to_equations; lia. }
  destruct BLKE as [E47 BLK8].
  assert (EV : evtF bsegs RNG (annot_Q R (ms_fregs ms) (ms_fcsr ms) lo sp K WL H' m)
                 (MS (mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                          (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                          (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                          (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                     (ms_fregs ms) (Z_to_bv 64 F_annot.TwinB.F_annot.AANNOT) (ms_fcsr ms) None m (seg_rom bsegs))).
  { assert (O8' : Oz mod 8 = 0) by (clear - O8 K8; Z.div_mod_to_equations; lia).
    assert (N8' : Nz mod 8 = 0) by (clear - N8 K8; Z.div_mod_to_equations; lia).
    assert (CAP : Ez - K <= 2 ^ 40) by (unfold WL in *; lia).
    assert (XOUT : forall g, 0 <= g < WL -> bv_unsigned (ALib.Mem.wa (shad K + g)) = shad K + g) by (intros g Hg; apply UW; lia).
    assert (G1 : ATOP <= lo) by lia.
    assert (G2 : lo <= bv_unsigned (AP.getr R 2) - F_annot.TwinB.F_annot.ANNOT_STACK) by (unfold F_annot.TwinB.F_annot.ANNOT_STACK; fold sp; lia).
    destruct (Z_lt_le_dec Nz Oz) as [LT|GE]; [| destruct (Z_lt_le_dec Oz Nz) as [GT|LE2]].
    -
      assert (LENE : shlen (Oz - Nz) = H - H') by (rewrite shlen_div by lia; rewrite EH, EH'; clear - N1 LT O8 N8; Z.div_mod_to_equations; lia).
      destruct (CHUNK (shad Nz) (shlen (Oz - Nz)) ltac:(lia) ltac:(lia) ltac:(lia)) as [junk BODY].
      eapply evtF_mono.
      + pose proof (F_annot.TwinB.F_annot_g.annot_shrink_gspec RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                 (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                 (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                 (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                 (ms_fregs ms) (ms_fcsr ms) m K Ez Oz Nz lo junk MI ST G1 G2 PC ANC Ha0 Ha1 Ha2 Ha3 K8 E8 O8' N8') as X0.
        assert (G3 : 0 <= K <= Nz) by lia. assert (G4 : ablk Nz Oz) by (unfold ablk; lia). assert (G5 : Oz <= 2 ^ 47) by lia.
        apply (X0 G3 LT O2 CAP G4 G5 BODY (ACCT_rng_aimg _ _ _ _ _ _ AC) RSTK). eapply rng_sub'; [exact RNGT| lia].
      + intros ms' (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV & STK & _).
        exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'. split; [exact EMS|]. fold sp in MU, STK.
        split; [apply (OUTV m' (shad Nz) (shlen (Oz - Nz))); [lia| lia| exact MU]|]. split; [exact WM|]. split; [exact MINV|]. split; [exact STK|].
        intros g Hg. apply KEEPZ; [lia|]. apply MU. cbn [ALib.Frame.outside]. rewrite XOUT by lia. split; [apply OUTS; lia|]. split; [lia| exact I].
    -
      assert (LENE : shlen (Nz - Oz) = H' - H) by (rewrite shlen_div by lia; rewrite EH, EH'; clear - O1 GT O8 N8; Z.div_mod_to_equations; lia).
      destruct (CHUNK (shad Oz) (shlen (Nz - Oz)) ltac:(lia) ltac:(lia) ltac:(lia)) as [junk BODY].
      eapply evtF_mono.
      + pose proof (F_annot.TwinB.F_annot_g.annot_grow_gspec RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                 (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                 (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                 (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                 (ms_fregs ms) (ms_fcsr ms) m K Ez Oz Nz lo junk MI ST G1 G2 PC ANC Ha0 Ha1 Ha2 Ha3 K8 E8 O8' N8') as X0.
        assert (G3 : 0 <= K <= Oz) by lia. assert (G4 : ablk Oz Nz) by (unfold ablk; lia). assert (G5 : Nz <= 2 ^ 47) by lia.
        apply (X0 G3 GT N2 CAP G4 G5 BODY (ACCT_rng_aimg _ _ _ _ _ _ AC) RSTK). eapply rng_sub'; [exact RNGT| lia].
      + intros ms' (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV & STK & CELL).
        exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'. split; [exact EMS|]. fold sp in MU, STK.
        split; [apply (OUTV m' (shad Oz) (shlen (Nz - Oz))); [lia| lia| exact MU]|]. split; [exact WM|]. split; [exact MINV|]. split; [exact STK|].
        intros g Hg. destruct (Z_lt_le_dec g H) as [GL|GH].
        * apply KEEPZ; [lia|]. apply MU. cbn [ALib.Frame.outside]. rewrite XOUT by lia. split; [apply OUTS; lia|]. split; [lia| exact I].
        * destruct CELL as [[_ (_ & _ & BY)] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
          specialize (BY (Z.to_nat (g - H)) ltac:(rewrite repeat_length; lia)). rewrite Z2Nat.id in BY by lia. rewrite nth_error_repeat in BY by lia.
          rewrite (GlueA.TwinB.rb_mrdA bsegs). replace (shad K + g) with (shad Oz + (g - H)) by lia. exact BY.
    -
      assert (EQ : Nz = Oz) by lia. rewrite EQ in Ha3. assert (HH : H' = H) by (rewrite EH, EH', EQ; reflexivity).
      eapply evtF_mono.
      + assert (G3 : 0 <= K <= Oz) by lia.
        exact (F_annot.TwinB.F_annot_g.annot_same_gspec RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                 (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                 (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                 (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                 (ms_fregs ms) (ms_fcsr ms) m K Ez Oz lo MI ST G1 G2 GOT6 ANC Ha0 Ha1 Ha2 Ha3 G3 O2 CAP E47 (ACCT_rng_aimg _ _ _ _ _ _ AC) RSTK).
      + intros ms' (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV & STK).
        exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'. split; [exact EMS|]. fold sp in MU, STK.
        split. { eapply munch_weaken; [| exact MU]. intros x OUT. cbn [ALib.Frame.outside] in *. unfold F_annot.TwinB.F_annot.ANNOT_STACK. lia. }
        split; [exact WM|]. split; [exact MINV|]. split; [exact STK|].
        intros g Hg. apply KEEPZ; [lia|]. apply MU. cbn [ALib.Frame.outside]. rewrite XOUT by lia. split; [apply OUTS; lia| exact I]. }
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ annot_Q R (ms_fregs ms) (ms_fcsr ms) lo sp K WL H' m ms') _ _ moc mo Kt).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV'' & STK' & ZERO).
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WTr & LT0 & ER).
    assert (EMS' : ms' = CtrFrame.TwinB.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.TwinB.ms'. f_equal. fold R. rewrite RA. apply MState.ret_pc_even.
      - lia.
      - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EV0.
        pose proof (ValP.land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV0 in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
    apply (HK _ ltac:(rewrite ESTS; left; reflexivity) (CtrFrame.TwinB.E' E st (CtrFree.TwinB.cfvF R') (fun _ _ => Z_to_bv 8 0)) ms' mo' (CtrFrame.TwinB.EXT E st _ _) HMP').
    rewrite EMS'.
    assert (KEPT : forall rg, In rg CtrFrame.TwinB.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg).
    { intros rg Hrg. unfold CtrFrame.TwinB.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg. }
    rewrite <- E1, <- E2, <- E3, <- E4 in ACP.
    assert (LOS : lo <= sp) by lia.
    exact (annot_post_ok E st ms mo HS wnl nn rest LB aw NW WF W ARW TI k sh rsh tlen om h' Frs WLt MHN MHO SHNZ ALK BT WMAX KEQ NLE OLE AL8E ENDIN X10E
             r st1 CP FS AJ NV TAILS OTHERS hargs md A nw Hf Hc Eh Tnw Nn Ln HC AWden ks offs rss ksp SPR Hksp SPE K16 LOSP FLOOR BOT LOS SPT
             R' m' mo' KEPT MINV'' STK' MU WM ZERO ACP OTH HMI').
Qed.
End Annot.
End TwinB.
