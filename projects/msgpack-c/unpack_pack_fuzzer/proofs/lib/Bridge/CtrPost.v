(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto AMalloc_iface AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aaligned_iseg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV CtrPre GlueA.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require KnownA.
Unset Nia Cache. Unset Nra Cache.

Definition alloc_stB_g (TWR : region) (XN : r5) (st st1 : sstate) (r : int) (h3 : list sv) (cred : sv) : sstate :=
  let n := getr st XN in
  let st2 := clobber st1 in
  let k := s_next st2 in
  let sh := PrimInt63.add k 1%uint63 in
  let st4 := set_next (set_next st2 (PrimInt63.add k 1%uint63)) (PrimInt63.add sh 1%uint63) in
  let R' := IMap.add sh TWR (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty) (s_regs st4)) in
  let st5 := set_ops (setregs st4 R') (set_op HEAP_ID h3 (s_ops st4)) in
  let st6 := addfact (addfact (addfact (addfact st5 (cred_fact (s_facts st) n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
               (FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw))) in
  setpc (setr st6 X10 (VP k wzero)) r.
Definition alloc_stB (XN : r5) (st st1 : sstate) (r : int) (h3 : list sv) (cred : sv) : sstate :=
  alloc_stB_g (twin_region (getr st XN)) XN st st1 r h3 cred.

Definition amalloc_stB : sstate -> sstate -> int -> list sv -> sv -> sstate := alloc_stB X10.

Definition alloc_stBb (XN : r5) (st st1 : sstate) (r : int) (h3 : list sv) (cred : sv) : sstate :=
  let n := getr st XN in
  let st2 := clobber st1 in
  let k := s_next st2 in
  let sh := PrimInt63.add k 1%uint63 in
  let s2 := PrimInt63.add sh 1%uint63 in
  let st4b := set_next (set_next (set_next st2 (PrimInt63.add k 1%uint63)) (PrimInt63.add sh 1%uint63)) (PrimInt63.add s2 1%uint63) in
  let Rb := IMap.add s2 (tail_region n) (IMap.add sh (twin_main n) (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty) (s_regs st4b))) in
  let st5b := set_ops (setregs st4b Rb) (set_op HEAP_ID h3 (s_ops st4b)) in
  let st6b := addfact (addfact (addfact (addfact (addfact (addfact st5b (cred_fact (s_facts st) n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
               (FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw)))) (tail_fact s2 sh n)) (FULt (VL wzero) n) in
  setpc (setr st6b X10 (VP k wzero)) r.

Lemma amalloc_apply_shape : forall UNIV PCz st sts, amalloc_apply UNIV PCz st = Some sts ->
  exists r hargs cred st1 h1 h2 h3 stN,
    call_pre st = Some r /\ find_op HEAP_ID (s_ops st) = Some hargs /\ heap_A hargs = Some cred
    /\ forget_stack_below_sp_g st = Some st1
    /\ heap_set_A hargs (cred_post (s_facts st) (getr st X10) cred) = Some h1
    /\ heap_add_window h1 (VP (s_next (clobber st1)) wzero) (getr st X10) (VL CtrLib.K_BLOCK) = Some h2
    /\ heap_add_window h2 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X10)) (VL K_TWIN) = Some h3
    /\ null_post hargs cred (clobber st1) r = Some stN
    /\ (   (size_shape_ok (s_facts st) (getr st X10) = true /\ sts = [stN; amalloc_stB st st1 r h3 cred])
        \/ (size_shape_ok (s_facts st) (getr st X10) = false /\ sts = [stN; alloc_stBb X10 st st1 r h3 cred])).
Proof.
  intros UNIV PCz st sts H. unfold amalloc_apply in H.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |] eqn:TP; try discriminate.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:FO; [|discriminate].
  destruct (heap_A hargs) as [cred|] eqn:HA; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  destruct (forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate].
  destruct (null_post hargs cred (clobber st1) r) as [stN|] eqn:NP; [|discriminate].
  unfold fresh in H. cbv zeta in H. cbn [fst snd s_next set_next] in H.
  destruct (heap_set_A hargs (cred_post (s_facts st) (getr st X10) cred)) as [h1|] eqn:H1; [|discriminate].
  destruct (heap_add_window h1 (VP (s_next (clobber st1)) wzero) (getr st X10) (VL CtrLib.K_BLOCK)) as [h2|] eqn:H2; [|discriminate].
  destruct (heap_add_window h2 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X10)) (VL K_TWIN)) as [h3|] eqn:H3; [|discriminate].
  injection H as <-.
  exists r, hargs, cred, st1, h1, h2, h3, stN. repeat (split; [reflexivity || assumption|]).
  destruct (size_shape_ok (s_facts st) (f10 (s_rf st))) eqn:SSH; [left; split; [exact SSH| reflexivity]| right; split; [exact SSH| reflexivity]].
Qed.

Lemma aaligned_apply_shape : forall UNIV PCz st sts, aaligned_apply UNIV PCz st = Some sts ->
  exists r hargs cred st1 h1 h2 h3 stN,
    call_pre st = Some r /\ find_op HEAP_ID (s_ops st) = Some hargs /\ heap_A hargs = Some cred
    /\ forget_stack_below_sp_g st = Some st1
    /\ heap_set_A hargs (cred_post (s_facts st) (getr st X11) cred) = Some h1
    /\ heap_add_window h1 (VP (s_next (clobber st1)) wzero) (getr st X11) (VL CtrLib.K_BLOCK) = Some h2
    /\ heap_add_window h2 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X11)) (VL K_TWIN) = Some h3
    /\ null_post hargs cred (clobber st1) r = Some stN
    /\ sts = [stN; alloc_stB X11 st st1 r h3 cred].
Proof.
  intros UNIV PCz st sts H. unfold aaligned_apply in H.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |] eqn:TP; try discriminate.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:FO; [|discriminate].
  destruct (getr st X10) as [al| | | | | | | | | |] eqn:X10E; try discriminate.
  destruct (heap_A hargs) as [cred|] eqn:HA; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  destruct (forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate].
  destruct (null_post hargs cred (clobber st1) r) as [stN|] eqn:NP; [|discriminate].
  unfold fresh in H. cbv zeta in H. cbn [fst snd s_next set_next] in H.
  destruct (heap_set_A hargs (cred_post (s_facts st) (getr st X11) cred)) as [h1|] eqn:H1; [|discriminate].
  destruct (heap_add_window h1 (VP (s_next (clobber st1)) wzero) (getr st X11) (VL CtrLib.K_BLOCK)) as [h2|] eqn:H2; [|discriminate].
  destruct (heap_add_window h2 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X11)) (VL K_TWIN)) as [h3|] eqn:H3; [|discriminate].
  injection H as <-.
  exists r, hargs, cred, st1, h1, h2, h3, stN. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Lemma add_window_facts : forall E md A nw rest n lo len kd,
  wt nw = false -> n = Z.to_nat (to_Z (wl nw)) -> (3 * n <= length rest)%nat -> to_Z (wl nw) + 1 < two63 ->
  let rest1 := firstn (3 * n) rest ++ [lo; len; kd] ++ skipn (3 * n) rest in
  let nw1 := wadd nw wone in
  heap_add_window (VL md :: A :: VL nw :: rest) lo len kd = Some (VL md :: A :: VL nw1 :: rest1)
  /\ wt nw1 = false /\ S n = Z.to_nat (to_Z (wl nw1)) /\ (3 * S n <= length rest1)%nat
  /\ wins_of E (S n) rest1 = wins_of E n rest ++ [Win (bv_unsigned (den E lo)) (bv_unsigned (den E len)) (bv_unsigned (den E kd))]
  /\ skipn (3 * S n) rest1 = skipn (3 * n) rest.
Proof.
  intros E md A nw rest n lo len kd T N L B. cbv zeta.
  destruct (wadd_one_small nw T B) as [T' E'].
  assert (HN : heap_nwin (VL md :: A :: VL nw :: rest) = Some n).
  { unfold heap_nwin. rewrite T, <- N. destruct (Nat.leb_spec (3 * n) (length rest)); [reflexivity| lia]. }
  split; [exact (heap_add_window_eq md A nw rest n lo len kd HN)|]. split; [exact T'|].
  split; [rewrite E', N; pose proof (Uint63.to_Z_bounded (wl nw)); lia|].
  split. { rewrite app_length, firstn_length_le by lia. cbn [length app]. rewrite skipn_length. lia. }
  split.
  - cbn [app]. rewrite (wins_of_app1 E n (firstn (3 * n) rest) lo len kd (skipn (3 * n) rest)); [| rewrite firstn_length_le; lia].
    rewrite <- (app_nil_r (firstn (3 * n) rest)) at 1. rewrite (wins_of_firstn E n rest []) by lia. reflexivity.
  - replace (3 * S n)%nat with (3 * n + 3)%nat by lia. rewrite skipn_app, firstn_length_le by lia.
    rewrite skipn_all2; [| rewrite firstn_length_le; lia]. replace (3 * n + 3 - 3 * n)%nat with 3%nat by lia. reflexivity.
Qed.

Lemma stB_shape_gen : forall (S : sstate) (k sh nx1 nx2 : int) (RGk RGs : region) (h : list sv) (f0 f1 f2 f3 : fact) (v : sv) (r : int),
  setpc (setr (addfact (addfact (addfact (addfact
          (set_ops (setregs (set_next (set_next S nx1) nx2) (IMap.add sh RGs (IMap.add k RGk (s_regs (set_next (set_next S nx1) nx2)))))
                   (set_op HEAP_ID h (s_ops (set_next (set_next S nx1) nx2))))
          f0) f1) f2) f3) X10 v) r
  = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (IMap.add sh RGs (IMap.add k RGk (s_regs S)))
       (f3 :: f2 :: f1 :: f0 :: s_facts S) (set_op HEAP_ID h (s_ops S)) (s_priv S) nx2.
Proof. intros. destruct S. reflexivity. Qed.
Lemma stBb_shape_gen : forall (S : sstate) (k sh s2 nx1 nx2 nx3 : int) (RGk RGs RGt : region) (h : list sv) (f0 f1 f2 f3 f4 f5 : fact) (v : sv) (r : int),
  setpc (setr (addfact (addfact (addfact (addfact (addfact (addfact
          (set_ops (setregs (set_next (set_next (set_next S nx1) nx2) nx3)
                            (IMap.add s2 RGt (IMap.add sh RGs (IMap.add k RGk (s_regs (set_next (set_next (set_next S nx1) nx2) nx3))))))
                   (set_op HEAP_ID h (s_ops (set_next (set_next (set_next S nx1) nx2) nx3))))
          f0) f1) f2) f3) f4) f5) X10 v) r
  = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (IMap.add s2 RGt (IMap.add sh RGs (IMap.add k RGk (s_regs S))))
       (f5 :: f4 :: f3 :: f2 :: f1 :: f0 :: s_facts S) (set_op HEAP_ID h (s_ops S)) (s_priv S) nx3.
Proof. intros. destruct S. reflexivity. Qed.

Section Post.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.

Hypothesis IMGSH_aci : forall v a, In v SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.cov1 HEAP_ID args z.
Hypothesis Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds Cw md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.

Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.

Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.

Section POST.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok asegs OPS E st ms mo.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Definition E' : env := env_above E (s_next st) Fv Gv.

Lemma EXT : env_ext (s_next st) E E'.
Proof. apply env_above_ext. Qed.

Lemma NX : st_vars_below (s_next st) st = true /\ 0 < to_Z (s_next st) /\ to_Z (s_next st) + 256 <= 2 ^ 62.
Proof. apply HeapCtr.fresh_ok_inv. exact FOK. Qed.

Lemma SVB_parts :
  rf_allb (sv_vars_below (s_next st)) (s_rf st) = true /\ rf_allb (sv_vars_below (s_next st)) (s_ff st) = true
  /\ resv_vars_below (s_next st) (s_resv st) = true
  /\ IMap.forallb (fun k r => PrimInt63.ltb k (s_next st) && region_vars_below (s_next st) r) (s_regs st) = true
  /\ forallb (fact_vars_below (s_next st)) (s_facts st) = true
  /\ forallb (fun o => forallb (sv_vars_below (s_next st)) (op_args o)) (s_ops st) = true.
Proof.
  destruct NX as (SVB & _). unfold st_vars_below in SVB.
  apply andb_prop in SVB as [SVB H6]. apply andb_prop in SVB as [SVB H5]. apply andb_prop in SVB as [SVB H4'].
  apply andb_prop in SVB as [SVB H3]. apply andb_prop in SVB as [H1 H2]. repeat split; assumption.
Qed.

Lemma HS' : st_ok asegs OPS E' st ms mo.
Proof. destruct NX as (SVB & POS & _). exact (st_ok_reval asegs OPS (s_next st) E E' EXT st ms mo POS SVB HS). Qed.

Lemma den_E' : forall v, sv_vars_below (s_next st) v = true -> den E' v = den E v.
Proof. intros v Hv. exact (den_reval (s_next st) E E' EXT v Hv). Qed.

Lemma ev_E'_below : forall k, to_Z k < to_Z (s_next st) -> ev E' k = ev E k.
Proof. intros k Hk. unfold E'. apply ev_below. exact Hk. Qed.

Lemma ev_E'_fresh : forall i, (i <= 200)%nat -> ev E' (addn (s_next st) i) = Fv (Z.of_nat i).
Proof.
  intros i Hi. destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  assert (EA : to_Z (addn (s_next st) i) = to_Z (s_next st) + Z.of_nat i) by (apply addn_Z; rewrite wB_two63, two63_eq; lia).
  unfold E'. rewrite ev_above by (rewrite EA; lia). rewrite EA. f_equal. lia.
Qed.

Lemma reg_E' : forall k rg, IMap.find k (s_regs st) = Some rg ->
  ev E' k = ev E k /\ hiZ E' rg = hiZ E rg /\ PrimInt63.ltb k (s_next st) = true /\ region_vars_below (s_next st) rg = true.
Proof.
  intros k rg Hk. destruct SVB_parts as (_ & _ & _ & HR & _). exact (regs_reval_find (s_next st) E E' EXT _ k rg (so_bst _ _ _ _ _ _ HS) HR Hk).
Qed.

Variables (r : int) (st1 : sstate).
Hypothesis CP : call_pre st = Some r.
Hypothesis FS : forget_stack_below_sp_g st = Some st1.
Variables (R' : bvmap 5 word) (m' : amem) (mo' : Model).
Definition kept_regsA : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Hypothesis KEPT : forall rg, In rg kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg.
Hypothesis HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Definition ms' : machine_state := MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None m' (seg_rom asegs).

Lemma st1_fields : s_pc st1 = s_pc st /\ s_rf st1 = s_rf st /\ s_ff st1 = s_ff st /\ s_resv st1 = s_resv st /\ s_facts st1 = s_facts st
  /\ s_ops st1 = s_ops st /\ s_priv st1 = s_priv st /\ s_next st1 = s_next st.
Proof.
  unfold forget_stack_below_sp_g in FS. destruct (sp_region st) as [[[k0 off0] r0]|]; [|discriminate].
  destruct (okey off0); [|discriminate]. injection FS as <-. repeat split; reflexivity.
Qed.

Lemma rget_core_getrA : forall R F pc fc rv x, rget (Core R F pc fc rv) (reg_of_r5 x) = AP.getr R (reg_of_r5 x).
Proof. intros. reflexivity. Qed.
Lemma reg_of_X0 : reg_of_r5 X0 = 0%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma getr_x0A : forall R, AP.getr R (reg_of_r5 X0) = Z_to_bv 64 0.
Proof. intros R. rewrite reg_of_X0. unfold AP.getr. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma kept_or_clobberedA : forall x, x <> X0 -> x <> X10 -> clob_pos x = None -> In (reg_of_r5 x) kept_regsA.
Proof.
  intros x N0 N10 H. destruct x; try discriminate H; try congruence;
  unfold kept_regsA; cbn [In];
  repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] | |- False => fail end.
Qed.

Lemma post_regs : forall v, den E' v = AP.getr R' 10%bv ->
  forall x, rget (Core R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None) (reg_of_r5 x)
            = den E' (rf_get (rf_set (s_rf (clobber st1)) X10 v) x).
Proof.
  intros v Hv x. rewrite rget_core_getrA. destruct st1_fields as (_ & RF1 & _ & _ & _ & _ & _ & NX1).
  destruct (r5_eqb x X10) eqn:Q10.
  { apply r5_eqb_spec in Q10. subst x. rewrite rf_get_set_same. symmetry. rewrite <- HeapCtr.reg_of_X10 in Hv. exact Hv. }
  assert (N10 : x <> X10) by (intros ->; rewrite StepB.r5_eqb_refl in Q10; discriminate).
  rewrite rf_get_set_other by (intros Q; apply N10; symmetry; exact Q).
  change (rf_get (s_rf (clobber st1)) x) with (getr (clobber st1) x). rewrite getr_clobber, NX1.
  destruct (clob_pos x) as [i|] eqn:CPx.
  - rewrite <- (HF x i CPx). cbn [den]. rewrite ev_E'_fresh; [| destruct x; cbn in CPx; try discriminate; injection CPx as <-; lia].
    apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, w2Z_wzero, Z.add_0_r. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
  - destruct (r5_eqb x X0) eqn:Q0.
    + apply r5_eqb_spec in Q0. subst x. rewrite getr_x0A. unfold getr. rewrite RF1.
      rewrite (so_x0 _ _ _ _ _ _ HS'). rewrite den_VL. reflexivity.
    + assert (N0 : x <> X0) by (intros ->; rewrite StepB.r5_eqb_refl in Q0; discriminate).
      rewrite (KEPT _ (kept_or_clobberedA x N0 N10 CPx)).
      rewrite (GlueA.getr_RA asegs OPS E st ms mo HS x). unfold getr. rewrite RF1.
      symmetry. apply den_E'. destruct SVB_parts as (SVB & _). exact (rf_allb_get _ _ _ SVB x).
Qed.

Variables (aw : word) (LB : blocks) (L : alayout) (RNG RNG' : footprint) (sta sta' : astate) (LBa : list ablock) (p : aptr) (Ablk N : Z).

Variable WW : wit.
Hypothesis WOF : wit_of WW L RNG sta LBa.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis AH' : AHEAP AI L RNG' sta' (HB p Ablk N :: LBa) m'.
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis PRES : aheap_pres (aci AI) LBa sp (ms_mem ms) m'.
Hypothesis TWP : twins_pres LBa (ms_mem ms) m'.
Hypothesis PATN : ablock_shadow m' Ablk N.
Hypothesis MINV' : ALib.Mem.mem_inv asegs m'.

Definition stableA (a : Z) : Prop := (sp <= a < 2 ^ 47) \/ in_ranges (aci AI) a \/ in_user LB a.

Lemma stable_byte : forall a, 0 <= a < 2 ^ 64 -> stableA a ->
  m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a) /\ rb asegs m' a = rb asegs (ms_mem ms) a
  /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true).
Proof.
  intros a Ha ST.
  assert (EQ : m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)).
  { destruct WOF as (E1 & E2 & E3 & E4). pose proof AR as [HWw EMw]. pose proof HWw as (_ & HT & _).
    destruct (LB_classify AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo HWw) as (KU & KT).
    apply (aw_real_stable AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo WW RNG' sta' (HB p Ablk N :: LBa) m' LBa LB sp LBa TWP ltac:(intros b Hb _ _; rewrite <- E4; exact Hb) AR).
    - rewrite E1. exact AH'.
    - exact PRES.
    - intros v Hv UB P. destruct (KU v Hv UB P) as (b & Vb & ->). exists b. split; [rewrite <- E4; exact (proj1 Vb)| reflexivity].
    - intros v Hv NUB. destruct (KT v Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
      + left. exists b. destruct (HT b Hb) as [HbL HH]. split; [exact HbL|]. split; [right; rewrite <- E4; exact HbL|]. split; [exact HH| reflexivity].
      + right. exists b. split; [exact (proj1 (proj1 Vb))|]. split; [rewrite <- E4; exact (proj1 (proj1 Vb))|]. split; [exact (proj2 Vb)| reflexivity].
    - exact Ha.
    - exact ST. }
  split; [exact EQ|]. split.
  - unfold rb. unfold ALib.Mem.wa in EQ. rewrite EQ. reflexivity.
  - intros W. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in W.
    rewrite (wview_ext1 m' (ms_mem ms) _ EQ). exact W.
Qed.

Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis Hksp : okey offs = Some ksp.
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Variables (wnl : list (int * sv * w64)) (n : nat) (rest : list sv).
Hypothesis NW : CtrA.nonstack_windows n rest = Some wnl.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis WF : windows_wf (wins_of E n rest) LB (ATOP + 4096).

Hypothesis WLOF : forall wlo, stack_wlo st = Some wlo -> ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo)).
Hypothesis FLOOR0 : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis LOSP0 : loZ rss <= keyZ ksp.

Lemma SP_den : bv_unsigned (den E (getr st X2)) = sp.
Proof. unfold sp. rewrite <- HeapCtr.reg_of_X2, (GlueA.getr_RA asegs OPS E st ms mo HS X2). reflexivity. Qed.

Notation is_sliver k0 rg := (sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k0 rg).
Lemma old_stable : forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> k0 <> 0%uint63 -> k0 <> ks -> is_sliver k0 rg = false ->
  forall a, bv_unsigned (ev E k0) + loZ rg <= a < bv_unsigned (ev E k0) + hiZ E rg -> (sp <= a < 2 ^ 47) \/ in_user LB a \/ sh_cov a.
Proof.
  intros k0 rg Hk K0 KS NSL a Ha. pose proof atop_range as ATR.
  assert (INWIN : forall k1 len kd, CtrA.win_lookup wnl k1 = Some (len, kd) ->
            bv_unsigned (ev E k1) <= a < bv_unsigned (ev E k1) + bv_unsigned (den E len) -> in_user LB a).
  { intros k1 len kd WL Hin.
    destruct (HeapCtrB.nonstack_windows_In E n rest wnl k1 len kd NW (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
    pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
    + exfalso. exact (KD KS0).
    + apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
    + apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }
  destruct (CallA.aregion_just_sound asegs OPS E st ms mo wnl ks offs rss k0 rg HS SPR AJ Hk K0) as [[EQK _]|(_ & [(len & kd & WL & LZ & HZ)|[(ABOVE & TOP)|[VJ|SL]]])];
    [| | | | congruence].
  - contradiction.
  - right. left. rewrite LZ in Ha. apply (INWIN k0 len kd WL). lia.
  - left. rewrite SP_den in ABOVE. lia.
  - destruct (CallV.view_just_sound asegs OPS E st ms mo wnl ks offs rss k0 rg HS SPR Hk K0 VJ) as [(_ & blo & bhi & SHA & TOP & FLR)|[(hs0 & n0 & sh' & len & ZV & BT & VPAR & WL & LO & HI)|[(_ & v & Hv & LO & HI)|(sh' & kbt & nt & len & WL & _ & _ & _ & _ & _ & LO & HI)]]].
    + right. right. left. destruct (SHA a Ha) as (a' & Ha' & ->). exists a'.
      assert (FL : ATOP + 4096 <= blo).
      { destruct FLR as [(wlo & SW & ->)|[(rs0 & Frs & ->)|GE]].
        - exact (WLOF wlo SW).
        - destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). rewrite Hrs in Frs. injection Frs as <-. exact FLOOR0.
        - rewrite SP_den in GE. rewrite SPE in GE. lia. }
      split; [lia|]. unfold CallV.shz, shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
    + right. left. apply (INWIN sh' len K_TWIN WL). lia.
    + right. right. right. exists v. split; [exact (IMGSH_SHLIT v Hv)| lia].
    + right. left. apply (INWIN sh' len K_TWIN WL). lia.
Qed.

Lemma sh_cov_pres : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a).
Proof.
  intros a Ha [(a' & R & ->)|(v & Hv & R)].
  - exact (proj1 (PRES (shad a') Ha ltac:(right; right; right; exists a'; split; [left; exact R| reflexivity]))).
  - destruct (IMGSH_aci v a Hv R) as (a' & INA & ->).
    exact (proj1 (PRES (shad a') Ha ltac:(right; right; right; exists a'; split; [right; left; exact INA| reflexivity]))).
Qed.

Hypothesis STKlo' : stk asegs m' (CtrPre.sp_lo E st) sp.
Lemma SP_bottom : CtrPre.sp_lo E st <= bv_unsigned (ev E ks) + loZ rss <= sp.
Proof. split; [exact (CtrPre.sp_lo_le OPS E st ms mo ks offs rss HS SPR)| rewrite SPE; lia]. Qed.

Lemma old_region_ok : forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> k0 <> 0%uint63 -> k0 <> ks ->
  region_ok asegs (s_priv st) E' m' k0 rg.
Proof.
  intros k0 rg Hk K0 KS. pose proof (so_reg _ _ _ _ _ _ HS' k0 rg Hk) as RO. destruct (reg_E' k0 rg Hk) as (Ek & Eh & _).
  assert (KZ : PrimInt63.eqb k0 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  destruct (is_sliver k0 rg) eqn:SL.
  {
    exact (CtrPre.sliver_region_ok OPS E E' st ms mo m' ks offs rss k0 rg sp HS SPR Hk K0 KS SL Ek Eh (proj2 SP_bottom) STKlo'). }
  apply (MemP.region_ok_frame asegs (s_priv st) E' (ms_mem ms) m' k0 rg (so_zero _ _ _ _ _ _ HS') RO).
  intros a Ha R _. rewrite Ek, Eh in R.
  destruct (old_stable k0 rg Hk K0 KS SL a (R KZ)) as [X|[X|X]].
  - destruct (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(left; exact X)) as (E1 & _). unfold ALib.Mem.wa in E1. exact E1.
  - destruct (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; right; exact X)) as (E1 & _). unfold ALib.Mem.wa in E1. exact E1.
  - pose proof (sh_cov_pres a ltac:(unfold two64 in Ha; lia) X) as E1. unfold ALib.Mem.wa in E1. exact E1.
Qed.

Hypothesis K16 : keyZ ksp mod 16 = 0.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Lemma STK' : stk asegs m' (bv_unsigned (ev E ks) + loZ rss) sp.
Proof. exact (CtrPre.stk_sp_region E st m' ks offs rss sp SPR SP_bottom STKlo'). Qed.
Definition forget_rs : region := region_forget_below rss ksp.

Lemma st1_regs : s_regs st1 = IMap.add ks forget_rs (s_regs st).
Proof.
  unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. reflexivity.
Qed.

Lemma rs_top : bv_unsigned (ev E ks) + hiZ E rss <= 2 ^ 47.
Proof.
  destruct (CallA.sp_region_inv st ks offs rss SPR) as (HX2 & Hrs & KZ & HW & HBG).
  assert (K0 : ks <> 0%uint63) by (apply Uint63.eqb_false_spec; exact KZ).
  destruct (CallA.aregion_just_sound asegs OPS E st ms mo wnl ks offs rss ks rss HS SPR AJ Hrs K0) as [[_ TOP]|[NE _]]; [exact TOP| contradiction].
Qed.

Lemma rs_ok : region_ok asegs (s_priv st) E' m' ks forget_rs.
Proof.
  destruct (CallA.sp_region_inv st ks offs rss SPR) as (HX2 & Hrs & KZ & HW & HBG).
  pose proof (so_reg _ _ _ _ _ _ HS' ks rss Hrs) as RO. destruct (reg_E' ks rss Hrs) as (Ek & Eh & _). pose proof rs_top as TOP.
  destruct (ro_range _ _ _ _ _ _ RO KZ) as [RLO RHI]. rewrite Ek in RLO. rewrite Ek, Eh in RHI.
  apply (CallA.region_forget_below_ok asegs (s_priv st) E' (ms_mem ms) m' ks rss ksp (so_zero _ _ _ _ _ _ HS') RO KZ HBG K16).
  - intros a Ha. rewrite Ek, Eh in Ha.
    destruct (stable_byte a ltac:(unfold two64 in *; lia) ltac:(left; rewrite SPE; lia)) as (_ & E2 & W2). split; assumption.
  - intros a Ha. rewrite Ek in Ha. destruct STK' as (_ & _ & ST). destruct (ST a ltac:(rewrite SPE; lia)) as [W [b Hb]].
    split; [rewrite (GlueA.rb_mrdA asegs), Hb; discriminate|]. apply (GlueA.wb_wviewA asegs). exact W.
Qed.

Variable aw' : word.
Hypothesis AC' : ACCT aw' L RNG' sta' (HB p Ablk N :: LBa) mo'.
Definition LB' : blocks := (shad Ablk, shlen (N + 7)) :: (Ablk, N) :: LB.

Lemma NEWB : 1 <= N <= AREQMAX /\ ablock_range Ablk N /\ ALib.Mem.wr_at asegs m' Ablk N.
Proof.
  destruct (heap_block_facts AI L RNG' sta' _ m' (HB p Ablk N) AH' ltac:(left; reflexivity) ltac:(exists p; reflexivity)) as (A1 & A2 & A3).
  cbn [ab_addr ab_size] in *. auto.
Qed.

Definition Wm : wit := mkWit (w_L WW) RNG' sta' (HB p Ablk N :: w_LBa WW) (HB p Ablk N :: w_T WW) (w_FA WW) m' (w_zc WW).

Lemma WORLD' : aw_holds_w AI ACCT UNIV Wm aw' LB' m' mo'
  /\ (forall g, 0 <= g -> 8 * g < N -> m' (ALib.Mem.wa (shad Ablk + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? N then 0 else N - 8 * g)))
  /\ user_band Ablk /\ (forall a, in_iv (Ablk, N) a -> ~ in_user LB a) /\ ~ In (shad Ablk, shlen (N + 7)) ((Ablk, N) :: LB)
  /\ (forall a, in_iv (shad Ablk, shlen (N + 7)) a -> ~ in_user LB a).
Proof.
  destruct WOF as (E1 & E2 & E3 & E4).
  destruct (aw_real_malloc AI ACCT UNIV AI_fake aw aw' LB (ms_mem ms) mo WW RNG' sta' p Ablk N m' mo' sp AR
              ltac:(rewrite E1, E4; exact AH') ltac:(rewrite E1, E4; exact AC') ltac:(rewrite E4; exact PRES) ltac:(rewrite E4; exact TWP) PATN) as (AR' & VB & NT & UB & DJ & DJT).
  destruct AR' as [HW1 _].
  destruct (twin_out_w AI ACCT UNIV AI_fake _ aw' _ m' mo' (HB p Ablk N) HW1 VB ltac:(exists p; reflexivity) NT) as (AWH' & NIN & PAT).
  split; [exact AWH'|]. split; [exact PAT|]. split; [exact UB|]. split; [exact DJ|]. split; [exact NIN| exact DJT].
Qed.
Lemma WORLD'_asan : aw_holds_asan AI ACCT UNIV aw' LB' m' mo'.
Proof. exists Wm. exact (proj1 WORLD'). Qed.

Definition kB : int := addn (s_next st) 15.
Definition kS : int := addn (s_next st) 16.
Variable XN : r5.
Definition nsv : sv := getr st XN.
Hypothesis NDEN : bv_unsigned (den E nsv) = N.
Hypothesis F15 : Fv 15 = Z_to_bv 64 Ablk.
Hypothesis F16 : Fv 16 = Z_to_bv 64 (shad Ablk).
Hypothesis GJ : forall o, 0 <= o < N -> rb asegs m' (Ablk + o) = Some (Gv 15 o).

Variable TWR : region.
Hypothesis TWSH : (TWR = twin_region nsv /\ match nsv with VL _ => True | _ => N mod 8 = 0 end) \/ TWR = twin_main nsv.

Lemma nsv_below : sv_vars_below (s_next st) nsv = true.
Proof. destruct SVB_parts as (SVB & _). exact (rf_allb_get _ _ _ SVB XN). Qed.

Lemma kB_Z : to_Z kB = to_Z (s_next st) + 15.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold kB. rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma kS_Z : to_Z kS = to_Z (s_next st) + 16.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold kS. rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma ev_kB : bv_unsigned (ev E' kB) = Ablk.
Proof.
  unfold kB. rewrite ev_E'_fresh by lia. change (Z.of_nat 15) with 15. rewrite F15. destruct NEWB as (N1 & (BK & _ & TOP & _) & _).
  pose proof atop_range. unfold ablk, AIMG_HI, KLS in BK. apply Z_to_bv_small. unfold bv_modulus, two64. lia.
Qed.
Lemma ev_kS : bv_unsigned (ev E' kS) = shad Ablk.
Proof.
  unfold kS. rewrite ev_E'_fresh by lia. change (Z.of_nat 16) with 16. rewrite F16. destruct NEWB as (N1 & BR & _).
  destruct (twin_band _ _ BR N1) as (T1 & T2 & T3 & _). apply Z_to_bv_small. unfold bv_modulus, two64. lia.
Qed.
Lemma kB_nz : PrimInt63.eqb kB 0%uint63 = false.
Proof. apply Uint63.eqb_false_spec. intros X. pose proof kB_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia. Qed.
Lemma kS_nz : PrimInt63.eqb kS 0%uint63 = false.
Proof. apply Uint63.eqb_false_spec. intros X. pose proof kS_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia. Qed.

Definition blk_region : region := Region 0%uint63 nsv true BGUnk IMap.empty.

Lemma blk_region_ok : region_ok asegs (s_priv st) E' m' kB blk_region.
Proof.
  destruct NEWB as (N1 & BR & WR). pose proof WORLD'_asan as AWH'.
  assert (EH : hiZ E' blk_region = N) by (unfold hiZ, blk_region; cbn [rg_hi]; rewrite (den_E' nsv nsv_below); exact NDEN).
  assert (EL : loZ blk_region = 0) by reflexivity.
  destruct BR as (BK & _ & TOP & _). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  constructor; rewrite ?ev_kB, ?EH, ?EL.
  - apply IMap.bst_empty.
  - intros _. unfold two64. lia.
  - intros _ a Ha.
    destruct (aw_user_ok_asan AI ACCT UNIV AI_fake aw' LB' m' mo' (Ablk, N) a AWH' ltac:(right; left; reflexivity) ltac:(unfold in_iv; cbn [fst snd]; lia)) as [MP SEG].
    split; [| split; [| exact SEG]].
    + unfold rb. destruct (m' (Z_to_bv 64 a)); [discriminate| contradiction].
    + intros _. apply (GlueA.wb_wviewA asegs). destruct WR as (_ & _ & W). replace a with (Ablk + (a - Ablk)) by lia. apply W. lia.
  - intros g gr Hg. cbn [blk_region rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
  - intros g gr c i Hg. cbn [blk_region rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
  - intros o H1 _ _. specialize (H1 kB_nz). unfold bg_byte. cbn [blk_region rg_bg]. unfold E'. rewrite eg_above by (rewrite kB_Z; lia).
    rewrite kB_Z. replace (to_Z (s_next st) + 15 - to_Z (s_next st)) with 15 by lia. apply GJ. lia.
Qed.

Lemma twin_region_okA : region_ok asegs (s_priv st) E' m' kS TWR.
Proof.
  destruct NEWB as (N1 & BR & WR). destruct WORLD' as (_ & PAT & _). pose proof WORLD'_asan as AWH'. destruct (twin_band _ _ BR N1) as (T1 & T2 & T3 & _).
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (den_E' nsv nsv_below); exact NDEN).
  destruct TWSH as [[-> SHAPE]| ->].
  2:{
      apply (CallA.twin_main_ok asegs (s_priv st) E' m' kS nsv kS_nz); rewrite ?DN, ?ev_kS.
      - clear - N1. lia.
      - unfold shlen in T2. rewrite Z.shiftr_div_pow2 in T2 by lia. change (2 ^ 3) with 8 in T2. unfold two64. clear - T1 T2 N1. Z.div_mod_to_equations. lia.
      - intros g G. assert (G0 : 0 <= g) by lia. assert (G1 : 8 * g < N) by (clear - G; Z.div_mod_to_equations; lia). split.
        + pose proof (PAT g G0 G1) as P1. unfold rb. unfold ALib.Mem.wa in P1. rewrite P1.
          replace (8 * g + 8 <=? N) with true by (symmetry; apply Z.leb_le; clear - G; Z.div_mod_to_equations; lia). reflexivity.
        + apply (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw' LB' m' mo' _ (shad Ablk + g) AWH' ltac:(left; reflexivity)
                         ltac:(unfold in_iv; cbn [fst snd]; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - G; Z.div_mod_to_equations; lia))). }
  apply (CallA.twin_region_ok asegs (s_priv st) E' m' kS nsv kS_nz); rewrite ?DN, ?ev_kS.
  - lia.
  - unfold AREQMAX in N1. lia.
  - assert (X : match nsv with VL _ => True | _ => bv_unsigned (den E' nsv) mod 8 = 0 end) by (destruct nsv; try exact I; rewrite DN; exact SHAPE). rewrite DN in X. exact X.
  - unfold shlen in T2. rewrite Z.shiftr_div_pow2 in T2 by lia. change (2 ^ 3) with 8 in T2. unfold two64. lia.
  - intros g G0 G1. split.
    + pose proof (PAT g G0 G1) as P1. unfold rb. unfold ALib.Mem.wa in P1. rewrite P1. reflexivity.
    + apply (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw' LB' m' mo' _ (shad Ablk + g) AWH' ltac:(left; reflexivity)
                     ltac:(unfold in_iv; cbn [fst snd]; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - G0 G1; Z.div_mod_to_equations; lia))).
Qed.

Lemma TWR_geo : loZ TWR = 0 /\ 0 <= hiZ E' TWR <= (N + 7) / 8 /\ rg_w TWR = false.
Proof.
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (den_E' nsv nsv_below); exact NDEN).
  destruct NEWB as (NN & _). unfold AREQMAX in NN.
  destruct TWSH as [[-> _]| ->].
  - destruct (CallA.twin_region_fields nsv) as (LO & WR & _). split; [unfold loZ; rewrite LO; reflexivity|]. split; [| exact WR].
    unfold hiZ. rewrite CallA.twin_region_hi, (CallA.twin_len_den E' nsv) by (rewrite DN; lia). rewrite DN. clear - NN. split; [Z.div_mod_to_equations; lia| lia].
  - split; [reflexivity|]. split; [| reflexivity]. unfold hiZ, twin_main. cbn [rg_hi]. rewrite CallA.sz_last_den by (rewrite DN; clear - NN; lia). rewrite DN. clear - NN. Z.div_mod_to_equations. lia.
Qed.
Definition RgP : IMap.t region := IMap.add kS TWR (IMap.add kB blk_region (IMap.add ks forget_rs (s_regs st))).

Lemma old_key_lt : forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> to_Z k0 < to_Z (s_next st).
Proof. intros k0 rg H. destruct (reg_E' k0 rg H) as (_ & _ & LT & _). apply Uint63.ltb_spec in LT. exact LT. Qed.

Lemma RgP_bst : IMap.bst RgP.
Proof. unfold RgP. repeat apply IMap.bst_add. exact (so_bst _ _ _ _ _ _ HS). Qed.

Lemma RgP_find : forall k0 rg, IMap.find k0 RgP = Some rg ->
  (k0 = kS /\ rg = TWR) \/ (k0 = kB /\ rg = blk_region) \/ (k0 = ks /\ rg = forget_rs)
  \/ (k0 <> kS /\ k0 <> kB /\ k0 <> ks /\ IMap.find k0 (s_regs st) = Some rg).
Proof.
  intros k0 rg H. unfold RgP in H. pose proof (so_bst _ _ _ _ _ _ HS) as B0.
  destruct (Uint63.eqb kS k0) eqn:Q1.
  { apply Uint63.eqb_correct in Q1. subst k0. rewrite IMap.find_add_same in H by (repeat apply IMap.bst_add; exact B0). injection H as <-. left. auto. }
  rewrite IMap.find_add_other_eqb in H by (repeat apply IMap.bst_add; exact B0 || exact Q1).
  destruct (Uint63.eqb kB k0) eqn:Q2.
  { apply Uint63.eqb_correct in Q2. subst k0. rewrite IMap.find_add_same in H by (repeat apply IMap.bst_add; exact B0). injection H as <-. right; left. auto. }
  rewrite IMap.find_add_other_eqb in H by (repeat apply IMap.bst_add; exact B0 || exact Q2).
  destruct (Uint63.eqb ks k0) eqn:Q3.
  { apply Uint63.eqb_correct in Q3. subst k0. rewrite IMap.find_add_same in H by exact B0. injection H as <-. right; right; left. auto. }
  rewrite IMap.find_add_other_eqb in H by (exact B0 || exact Q3).
  right; right; right. apply Uint63.eqb_false_spec in Q1, Q2, Q3. repeat split; auto.
Qed.

Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.

Lemma rs_fields : loZ forget_rs = loZ rss /\ (forall E0, hiZ E0 forget_rs = hiZ E0 rss) /\ rg_w forget_rs = rg_w rss.
Proof. repeat split; reflexivity. Qed.

Lemma RgP_range : forall k0 rg a, IMap.find k0 RgP = Some rg -> PrimInt63.eqb k0 0%uint63 = false ->
  bv_unsigned (ev E' k0) + loZ rg <= a < bv_unsigned (ev E' k0) + hiZ E' rg ->
  (k0 = kS /\ in_iv (shad Ablk, shlen (N + 7)) a) \/ (k0 = kB /\ in_iv (Ablk, N) a)
  \/ (k0 = ks /\ ATOP + 4096 <= a < 2 ^ 47) \/ (k0 <> kS /\ k0 <> kB /\ k0 <> ks /\ ((ATOP + 4096 <= a < 2 ^ 47) \/ in_user LB a \/ sh_cov a)).
Proof.
  intros k0 rg a H KZ Ha. destruct (RgP_find k0 rg H) as [[-> ->]|[[-> ->]|[[-> ->]|(N1 & N2 & N3 & F)]]].
  - left. split; [reflexivity|]. rewrite ev_kS in Ha. destruct TWR_geo as (L0 & H0 & _). rewrite L0 in Ha.
    unfold in_iv, shlen. cbn [fst snd]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
  - right; left. split; [reflexivity|]. rewrite ev_kB in Ha. unfold hiZ, loZ, blk_region in Ha. cbn [rg_hi rg_lo] in Ha.
    rewrite (den_E' nsv nsv_below), NDEN in Ha. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0 in Ha. unfold in_iv. cbn [fst snd]. lia.
  - right; right; left. split; [reflexivity|]. destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _).
    destruct (reg_E' ks rss Hrs) as (Ek & Eh & _). destruct rs_fields as (L1 & H1 & _). rewrite L1, (H1 E'), Ek, Eh in Ha. pose proof rs_top. lia.
  - right; right; right. repeat (split; [assumption|]). destruct (reg_E' k0 rg F) as (Ek & Eh & _). rewrite Ek, Eh in Ha.
    assert (K0' : k0 <> 0%uint63) by (intros ->; discriminate KZ).
    destruct (is_sliver k0 rg) eqn:SL.
    + left. destruct (CtrPre.sp_lo_of_sliver OPS E st ms mo ks offs rss k0 rg HS SPR F K0' N3 SL) as (_ & L0 & EH & _ & _ & wlo & SW & EKW).
      pose proof (WLOF wlo SW) as CE. pose proof rs_top as RT. pose proof (CallA.sliver_neg st ks offs rss k0 rg SPR SL) as NEG.
      pose proof (bv_unsigned_in_range 64 (den E (rg_hi rss))) as RH. fold (hiZ E rss) in RH. rewrite L0 in Ha. lia.
    + destruct (old_stable k0 rg F K0' N3 SL a Ha) as [X|[X|X]]; [left; pose proof SPE; lia| right; left; exact X| right; right; exact X].
Qed.

Lemma sp_floor : ATOP + 4096 <= sp.
Proof. rewrite SPE. lia. Qed.

Lemma RgP_old : forall k0 rg, IMap.find k0 RgP = Some rg -> k0 <> kS -> k0 <> kB ->
  exists rg0, IMap.find k0 (s_regs st) = Some rg0 /\ loZ rg = loZ rg0 /\ (forall E0, hiZ E0 rg = hiZ E0 rg0) /\ rg_w rg = rg_w rg0.
Proof.
  intros k0 rg H N1 N2. destruct (RgP_find k0 rg H) as [[-> _]|[[-> _]|[[-> ->]|(_ & _ & _ & F)]]]; try contradiction.
  - destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). exists rss. split; [exact Hrs|]. repeat split; reflexivity.
  - exists rg. auto.
Qed.

Lemma RgP_disjoint : regions_disjoint E' RgP.
Proof.
  intros k1 rg1 k2 rg2 H1 H2 NE Z1 Z2 WR a [A1 A2].
  destruct NEWB as (NN & BR & _). destruct (twin_band _ _ BR NN) as (T1 & T2 & T3 & _). destruct WORLD' as (_ & _ & UB & DJ & _ & DJT).
  pose proof atop_range as ATR. pose proof sp_floor as SPF. destruct BR as (BK & _ & TOP & _). unfold ablk, AIMG_HI, KLS in BK.
  pose proof (RgP_range k1 rg1 a H1 Z1 A1) as C1. pose proof (RgP_range k2 rg2 a H2 Z2 A2) as C2.
  assert (TW_B : in_iv (shad Ablk, shlen (N + 7)) a -> in_iv (Ablk, N) a -> False) by (unfold in_iv; cbn [fst snd]; unfold user_band in UB; lia).
  assert (TW_S : in_iv (shad Ablk, shlen (N + 7)) a -> ATOP + 4096 <= a -> False) by (unfold in_iv; cbn [fst snd]; lia).
  assert (B_S : in_iv (Ablk, N) a -> ATOP + 4096 <= a -> False) by (unfold in_iv; cbn [fst snd]; lia).

  assert (SHB : sh_cov a -> (0x7fffa000 <= a < 0x800bdca8) \/ (shad ATOP <= a < 0x10007fff8000)) by exact (sh_cov_band a).
  destruct (shadow_tight Ablk N ltac:(unfold ablk, AIMG_HI, KLS; exact BK) TOP ltac:(lia)) as [TT1 TT2].
  assert (TW_C : in_iv (shad Ablk, shlen (N + 7)) a -> sh_cov a -> False) by (intros X Y; apply SHB in Y; unfold in_iv in X; cbn [fst snd] in X; lia).
  assert (B_C : in_iv (Ablk, N) a -> sh_cov a -> False).
  { intros X Y. apply SHB in Y. unfold in_iv in X. cbn [fst snd] in X.
    assert (SHA : 0x7fff8000 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia). lia. }

  destruct C1 as [[E1 I1]|[[E1 I1]|C1]]; destruct C2 as [[E2 I2]|[[E2 I2]|C2]]; subst; try contradiction; try (exfalso; eauto; fail).
  - destruct C2 as [[_ I2]|(_ & _ & _ & [I2|[I2|I2]])]; [exact (TW_S I1 (proj1 I2))| exact (TW_S I1 ltac:(lia))| exact (DJT a I1 I2)| exact (TW_C I1 I2)].
  - destruct C2 as [[_ I2]|(_ & _ & _ & [I2|[I2|I2]])]; [exact (B_S I1 (proj1 I2))| exact (B_S I1 ltac:(lia))| exact (DJ a I1 I2)| exact (B_C I1 I2)].
  - destruct C1 as [[_ I1]|(_ & _ & _ & [I1|[I1|I1]])]; [exact (TW_S I2 (proj1 I1))| exact (TW_S I2 ltac:(lia))| exact (DJT a I2 I1)| exact (TW_C I2 I1)].
  - destruct C1 as [[_ I1]|(_ & _ & _ & [I1|[I1|I1]])]; [exact (B_S I2 (proj1 I1))| exact (B_S I2 ltac:(lia))| exact (DJ a I2 I1)| exact (B_C I2 I1)].
  -
    assert (N1S : k1 <> kS) by (destruct C1 as [[-> _]|(X & _)]; [| exact X]; intros X; pose proof kS_Z; destruct (CallA.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite X in *; lia).
    assert (N1B : k1 <> kB) by (destruct C1 as [[-> _]|(_ & X & _)]; [| exact X]; intros X; pose proof kB_Z; destruct (CallA.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite X in *; lia).
    assert (N2S : k2 <> kS) by (destruct C2 as [[-> _]|(X & _)]; [| exact X]; intros X; pose proof kS_Z; destruct (CallA.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite X in *; lia).
    assert (N2B : k2 <> kB) by (destruct C2 as [[-> _]|(_ & X & _)]; [| exact X]; intros X; pose proof kB_Z; destruct (CallA.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite X in *; lia).
    destruct (RgP_old k1 rg1 H1 N1S N1B) as (q1 & F1 & L1 & HH1 & W1). destruct (RgP_old k2 rg2 H2 N2S N2B) as (q2 & F2 & L2 & HH2 & W2).
    rewrite L1, (HH1 E') in A1. rewrite L2, (HH2 E') in A2. rewrite W1, W2 in WR.
    exact (so_disj _ _ _ _ _ _ HS' k1 q1 k2 q2 F1 F2 NE Z1 Z2 WR a (conj A1 A2)).
Qed.

Lemma RgP_in_based : forall a, in_based E' RgP a ->
  in_iv (shad Ablk, shlen (N + 7)) a \/ in_iv (Ablk, N) a \/ in_based E' (s_regs st) a.
Proof.
  intros a (k0 & rg & H & KZ & R).
  destruct (Uint63.eqb k0 kS) eqn:QS; [apply Uint63.eqb_correct in QS; subst k0|].
  { destruct (RgP_range kS rg a H KZ R) as [[_ I]|[[X _]|[[X _]|(X & _)]]]; [left; exact I| | |];
      exfalso; [pose proof kS_Z; pose proof kB_Z; rewrite X in *; lia | pose proof kS_Z; destruct (CallA.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite <- X in *; lia | congruence]. }
  destruct (Uint63.eqb k0 kB) eqn:QB; [apply Uint63.eqb_correct in QB; subst k0|].
  { destruct (RgP_range kB rg a H KZ R) as [[X _]|[[_ I]|[[X _]|(_ & X & _)]]]; [| right; left; exact I | |];
      exfalso; [pose proof kS_Z; pose proof kB_Z; rewrite X in *; lia | pose proof kB_Z; destruct (CallA.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite <- X in *; lia | congruence]. }
  apply Uint63.eqb_false_spec in QS, QB. destruct (RgP_old k0 rg H QS QB) as (q & F & L1 & HH1 & _).
  right; right. exists k0, q. rewrite <- L1, <- (HH1 E'). auto.
Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : n = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * n <= length rest)%nat.
Hypothesis AWden : aw = den E A.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * n) rest)) LB (wins_of E n rest) (ms_mem ms).
Hypothesis TI : ties WW (wins_of E n rest).
Hypothesis PRS : In prist_win (wins_of E n rest) -> aprist sta'.

Lemma DEC : decode (map (den E) hargs) = Some (w2Z md, den E A, wins_of E n rest, map (den E) (skipn (3 * n) rest)).
Proof. rewrite Eh. exact (decode_hargs E md A nw rest n Tnw Nn Ln). Qed.

Lemma AWH : aw_holds_asan AI ACCT UNIV aw LB (ms_mem ms) mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.

Lemma win_off_image : forall a, in_ws (wins_of E n rest) a -> find_segment asegs a 1 = None.
Proof.
  intros a X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
  pose proof atop_range as ATR.
  pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SUBb)]]]).
  - apply ref_find_segment_none; [lia|]. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. lia.
  - exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ a AWH B Hin)).
  - exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo b a AWH Hb (SUBb a Hin))).
Qed.

Lemma pub_image_client : forall a seg, 0 <= a < two64 -> find_segment asegs a 1 = Some seg -> ~ in_priv (s_priv st) a -> in_ranges (aci AI) a.
Proof.
  intros a seg Ha SEG NP.
  destruct (in_ivs_b IMGX a) eqn:IX.
  - apply in_ivs_b_spec in IX. apply in_ivs_In in IX as (v & Hv & Hin). unfold in_iv in Hin.
    destruct (IMGX_aci v Hv) as (N0 & [(rg & Hr & R1 & R2)|[(rg & Hr & R1 & R2)|(S1 & S2)]]).
    + exists rg. split; [exact Hr|]. lia.
    +   exfalso. pose proof (AI_aci_lo AI rg Hr) as LO.
      rewrite (ref_find_segment_none a 1 ltac:(lia) ltac:(right; unfold ASHOFF in *; lia)) in SEG. discriminate.
    + exfalso. pose proof atop_range as ATR0.
      rewrite (ref_find_segment_none a 1 ltac:(lia) ltac:(right; unfold ASHOFF in *; lia)) in SEG. discriminate.
  - exfalso. assert (NIX : ~ in_ivs IMGX a) by (rewrite <- in_ivs_b_spec; congruence).
    assert (NW0 : ~ in_ws (wins_of E n rest) a) by (intros X; rewrite (win_off_image a X) in SEG; discriminate).
    destruct (ops_apart_find asegs OPS E (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a (so_apart _ _ _ _ _ _ HS) Hf) as [_ IP].
    { rewrite OPS_fp1. apply (proj2 (fp_spec IMGX _ _ _ _ _ a DEC)). auto. }
    apply NP. apply IP. exists seg. exact SEG.
Qed.

Lemma r0_ok : forall r0, IMap.find 0%uint63 (s_regs st) = Some r0 -> region_ok asegs (s_priv st) E' m' 0%uint63 r0.
Proof.
  intros r0 H0. pose proof (so_reg _ _ _ _ _ _ HS' _ _ H0) as RO.
  apply (MemP.region_ok_frame asegs (s_priv st) E' (ms_mem ms) m' _ r0 (so_zero _ _ _ _ _ _ HS') RO).
  intros a Ha _ R. destruct (R eq_refl) as [[seg SEG] NP].
  destruct (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact (pub_image_client a seg Ha SEG NP))) as (E1 & _).
  unfold ALib.Mem.wa in E1. exact E1.
Qed.

Lemma ks_nz : ks <> 0%uint63.
Proof. destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & _ & KZ & _). apply Uint63.eqb_false_spec. exact KZ. Qed.

Lemma all_regions_ok : forall k0 rg, IMap.find k0 RgP = Some rg -> region_ok asegs (s_priv st) E' m' k0 rg.
Proof.
  intros k0 rg H. destruct (RgP_find k0 rg H) as [[-> ->]|[[-> ->]|[[-> ->]|(N1 & N2 & N3 & F)]]].
  - exact twin_region_okA.
  - exact blk_region_ok.
  - exact rs_ok.
  - destruct (Uint63.eqb k0 0%uint63) eqn:Q0.
    + apply Uint63.eqb_correct in Q0. subst k0. exact (r0_ok rg F).
    + apply Uint63.eqb_false_spec in Q0. exact (old_region_ok k0 rg F Q0 N3).
Qed.

Lemma RgP_pub : abs_cells_public (s_priv st) RgP.
Proof.
  intros r0 g gr c H0 Hg Hcc i Hi.
  destruct (RgP_find _ _ H0) as [[X _]|[[X _]|[[X _]|(_ & _ & _ & F)]]].
  - exfalso. pose proof kS_Z as KZ. rewrite <- X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia.
  - exfalso. pose proof kB_Z as KZ. rewrite <- X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia.
  - exfalso. exact (ks_nz (eq_sym X)).
  - exact (so_pub _ _ _ _ _ _ HS r0 g gr c F Hg Hcc i Hi).
Qed.

Hypothesis N255 : (n <= 255)%nat.
Variable pd : bool.
Definition cred' : sv := if pd then A else sv_alu ALU_SUB A nsv.
Definition CHG : Z := if pd then 0 else N.
Definition restB : list sv := firstn (3 * n) rest ++ [VP kB wzero; nsv; VL CtrLib.K_BLOCK] ++ skipn (3 * n) rest.
Definition nwB : w64 := wadd nw wone.
Definition restT : list sv := firstn (3 * S n) restB ++ [VP kS wzero; twin_len nsv; VL K_TWIN] ++ skipn (3 * S n) restB.
Definition nwT : w64 := wadd nwB wone.
Definition h3 : list sv := VL md :: cred' :: VL nwT :: restT.

Lemma nw_small : to_Z (wl nw) + 2 < two63.
Proof. pose proof (Uint63.to_Z_bounded (wl nw)) as B. unfold two63. rewrite Nn in N255. lia. Qed.

Lemma h3_shape :
  heap_set_A hargs cred' = Some (VL md :: cred' :: VL nw :: rest)
  /\ heap_add_window (VL md :: cred' :: VL nw :: rest) (VP kB wzero) nsv (VL CtrLib.K_BLOCK) = Some (VL md :: cred' :: VL nwB :: restB)
  /\ heap_add_window (VL md :: cred' :: VL nwB :: restB) (VP kS wzero) (twin_len nsv) (VL K_TWIN) = Some h3.
Proof.
  pose proof nw_small as NS.
  destruct (add_window_facts E' md cred' nw rest n (VP kB wzero) nsv (VL CtrLib.K_BLOCK) Tnw Nn Ln ltac:(lia)) as (A1 & T1 & N1 & L1 & _).
  fold restB nwB in A1, T1, N1, L1.
  destruct (add_window_facts E' md cred' nwB restB (S n) (VP kS wzero) (twin_len nsv) (VL K_TWIN) T1 N1 L1
              ltac:(destruct (wadd_one_small nw Tnw ltac:(lia)) as [_ X]; fold nwB in X; lia)) as (A2 & _).
  split; [rewrite Eh; reflexivity|]. split; [exact A1| exact A2].
Qed.

Lemma rest_below : forallb (sv_vars_below (s_next st)) rest = true.
Proof.
  destruct SVB_parts as (_ & _ & _ & _ & _ & SO). pose proof (proj1 (forallb_forall _ _) SO _ (find_op_In _ _ _ Hf)) as X.
  cbn [op_args] in X. rewrite Eh in X. cbn [forallb] in X. apply andb_prop in X as [_ X]. apply andb_prop in X as [_ X]. apply andb_prop in X as [_ X]. exact X.
Qed.
Lemma A_below : sv_vars_below (s_next st) A = true.
Proof.
  destruct SVB_parts as (_ & _ & _ & _ & _ & SO). pose proof (proj1 (forallb_forall _ _) SO _ (find_op_In _ _ _ Hf)) as X.
  cbn [op_args] in X. rewrite Eh in X. cbn [forallb] in X. apply andb_prop in X as [_ X]. apply andb_prop in X as [X _]. exact X.
Qed.

Lemma wins_of_E' : forall m0 l, forallb (sv_vars_below (s_next st)) l = true -> wins_of E' m0 l = wins_of E m0 l.
Proof.
  induction m0 as [|m0 IH]; intros l AV; [reflexivity|]. destruct l as [|x [|y [|z l']]]; try reflexivity. cbn [forallb] in AV.
  apply andb_prop in AV as [A1 AV]. apply andb_prop in AV as [A2 AV]. apply andb_prop in AV as [A3 AV].
  rewrite !wins_of_cons, (IH l' AV), !den_E' by assumption. reflexivity.
Qed.
Lemma map_den_E' : forall l, forallb (sv_vars_below (s_next st)) l = true -> map (den E') l = map (den E) l.
Proof.
  induction l as [|x l IH]; intros AV; [reflexivity|]. cbn [forallb] in AV. apply andb_prop in AV as [A1 AV].
  cbn [map]. rewrite (den_E' x A1), (IH AV). reflexivity.
Qed.
Lemma forallb_skipn : forall {T} (f : T -> bool) j l, forallb f l = true -> forallb f (skipn j l) = true.
Proof.
  intros T f j. induction j as [|j IH]; intros l H; [exact H|]. destruct l as [|x l]; [reflexivity|]. cbn [skipn]. cbn [forallb] in H.
  apply andb_prop in H as [_ H]. exact (IH l H).
Qed.

Definition WB : window := Win Ablk N K_BLOCK.
Definition WT : window := Win (shad Ablk) (shlen (N + 7)) K_TWINz.

Lemma DEC3 : decode (map (den E') h3)
  = Some (w2Z md, Z_to_bv 64 (bv_unsigned aw - CHG), (wins_of E n rest ++ [WB]) ++ [WT], map (den E) (skipn (3 * n) rest)).
Proof.
  pose proof nw_small as NS. destruct NEWB as (NN & _).
  destruct (add_window_facts E' md cred' nw rest n (VP kB wzero) nsv (VL CtrLib.K_BLOCK) Tnw Nn Ln ltac:(lia)) as (_ & T1 & N1 & L1 & W1 & S1).
  fold restB nwB in T1, N1, L1, W1, S1.
  destruct (add_window_facts E' md cred' nwB restB (S n) (VP kS wzero) (twin_len nsv) (VL K_TWIN) T1 N1 L1
              ltac:(destruct (wadd_one_small nw Tnw ltac:(lia)) as [_ X]; fold nwB in X; lia)) as (_ & T2 & N2 & L2 & W2 & S2).
  fold restT nwT in T2, N2, L2, W2, S2.
  unfold h3. rewrite (decode_hargs E' md cred' nwT restT (S (S n)) T2 N2 L2). rewrite W2, W1, S2, S1.
  rewrite (wins_of_E' n rest rest_below), (map_den_E' _ (forallb_skipn _ (3 * n) rest rest_below)).
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (den_E' nsv nsv_below); exact NDEN).
  assert (C1 : den E' cred' = Z_to_bv 64 (bv_unsigned aw - CHG)).
  { unfold cred', CHG. destruct pd.
    - rewrite (den_E' A A_below), Z.sub_0_r, AWden. symmetry. apply Z_to_bv_bv_unsigned.
    - rewrite den_sv_alu. rewrite (den_E' A A_below). unfold alu64, alu. apply bv_eq.
      rewrite bv_sub_unsigned, Z_to_bv_unsigned, DN, AWden. reflexivity. }
  assert (C2 : Win (bv_unsigned (den E' (VP kB wzero))) (bv_unsigned (den E' nsv)) (bv_unsigned (den E' (VL CtrLib.K_BLOCK))) = WB).
  { unfold WB. rewrite HeapCtr.den_VPz, ev_kB, DN. reflexivity. }
  assert (C3 : Win (bv_unsigned (den E' (VP kS wzero))) (bv_unsigned (den E' (twin_len nsv))) (bv_unsigned (den E' (VL K_TWIN))) = WT).
  { unfold WT. rewrite HeapCtr.den_VPz, ev_kS. rewrite (CallA.twin_len_den E' nsv) by (rewrite DN; unfold AREQMAX in NN; lia).
    rewrite DN. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite C1, C2, C3. reflexivity.
Qed.

Hypothesis AW'E : aw' = Z_to_bv 64 (bv_unsigned aw - CHG).

Lemma windows_wf_mono : forall ws L1 L2 c, windows_wf ws L1 c -> (forall b, In b L1 -> In b L2) -> windows_wf ws L2 c.
Proof.
  intros ws L1 L2 c WF0 SUB. apply Forall_forall. intros w Hw.
  pose proof (proj1 (Forall_forall _ _) WF0 w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SB)]]]).
  - split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. left; auto.
  - split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. right; left; auto.
  - split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. right; right. split; [exact K|]. exists b. auto.
Qed.

Lemma HOLDS3 : op_holds OPS HEAP_ID (map (den E') h3) m' mo'.
Proof.
  rewrite OPS_holds1. destruct WORLD' as (AWH' & PAT & UB & DJ & NIN & DJT). destruct NEWB as (NN & BR & _).
  destruct (twin_band _ _ BR NN) as (T1 & T2 & T3 & _). assert (BK16 : 0 <= N /\ Ablk mod 8 = 0) by (destruct BR as (_ & X0 & _ & X16); split; [exact X0| clear - X16; Z.div_mod_to_equations; lia]).
  destruct BR as (BK & _ & TOP & _). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  assert (TWFRESH : forall a, in_iv (shad Ablk, shlen (N + 7)) a -> ~ in_user ((Ablk, N) :: LB) a).
  { intros a Ha U. apply in_ivs_cons in U as [U|U]; [| exact (DJT a Ha U)].
    unfold in_iv in Ha, U. cbn [fst snd] in Ha, U. unfold user_band in UB. lia. }
  exists (w2Z md), aw', ((wins_of E n rest ++ [WB]) ++ [WT]), (map (den E) (skipn (3 * n) rest)), LB', Wm.
  split; [rewrite AW'E; exact DEC3|]. split; [exact AWH'|]. split; [| split].
  -
    apply Forall_app. split; [apply Forall_app; split|].
    + apply (windows_wf_mono _ LB LB' _ WF). intros b Hb. right; right. exact Hb.
    + constructor; [|constructor]. unfold window_wf, WB, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; left. split; [reflexivity|]. right; left. reflexivity.
    + constructor; [|constructor]. unfold window_wf, WT, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; right. split; [unfold K_SUB, K_TWINz; lia|]. exists (shad Ablk, shlen (N + 7)). split; [left; reflexivity|]. intros a Ha. exact Ha.
  -
    assert (HC1 : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * n) rest)) LB (wins_of E n rest) m').
    { apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U _.
      destruct (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; right; exact U)) as (E1 & _). unfold ALib.Mem.wa in E1. symmetry. exact E1. }
    pose proof (cw_grow Cw _ _ _ _ m' Ablk N HC1 DJ) as HC2.
    apply (Cw_ghost_grow _ _ _ _ m' Ablk N (shlen (N + 7)) HC2); [apply in_or_app; right; left; reflexivity| lia| destruct BK16 as [_ X]; exact X|].
    exact TWFRESH.
  -
    apply (ties_grow_heap WW (wins_of E n rest) (w_L WW) RNG' sta' m' (HB p Ablk N) TI ltac:(exists p; reflexivity)); [cbn [ab_size]; lia| | exact PRS].
    cbn [ab_addr ab_size]. fold WB WT.
    assert (GA0 : ghost_apart (wins_of E n rest)) by (destruct TI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
    assert (WF1 : windows_wf (wins_of E n rest ++ [WB]) ((Ablk, N) :: LB) (ATOP + 4096)).
    { apply Forall_app. split; [apply (windows_wf_mono _ LB _ _ WF); intros b Hb; right; exact Hb|].
      constructor; [|constructor]. unfold window_wf, WB, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; left. split; [reflexivity|]. left. reflexivity. }
    apply (ghost_apart_new_ghosts (wins_of E n rest ++ [WB]) _ ((Ablk, N) :: LB) (ATOP + 4096) WF1).
    + exact (ghost_apart_new_block _ LB (ATOP + 4096) Ablk N WF GA0 DJ).
    + intros w Hw. apply in_app_or in Hw as [Hw|[<-|[]]]; [left; exact Hw| right]. split; [unfold WT; cbn [w_kind]; unfold K_TWINz, K_BLOCK; lia|].
      intros _ a Ha. unfold WT, w_iv in Ha. cbn [w_lo w_len] in Ha. exact (TWFRESH a Ha).
Qed.

Hypothesis OTH : OTHER mo mo'.

Definition ops' : list opinst := set_op HEAP_ID h3 (s_ops st).

Lemma hargs_below : forallb (sv_vars_below (s_next st)) hargs = true.
Proof.
  destruct SVB_parts as (_ & _ & _ & _ & _ & SO). exact (proj1 (forallb_forall _ _) SO _ (find_op_In _ _ _ Hf)).
Qed.
Lemma DEC' : decode (map (den E') hargs) = Some (w2Z md, den E A, wins_of E n rest, map (den E) (skipn (3 * n) rest)).
Proof. rewrite (map_den_E' hargs hargs_below). exact DEC. Qed.

Lemma in_ws_app : forall ws1 ws2 a, in_ws (ws1 ++ ws2) a <-> in_ws ws1 a \/ in_ws ws2 a.
Proof. intros. unfold in_ws. rewrite map_app. apply in_ivs_app. Qed.

Lemma OPS_HOLD' : ops_hold OPS E' ops' m' mo'.
Proof.
  apply (ops_hold_set_op OPS E' E' (s_ops st) HEAP_ID hargs h3 (ms_mem ms) m' mo mo' Hf Hc (so_ops _ _ _ _ _ _ HS')); [| exact HOLDS3].
  intros o Ho NI H. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
  apply (OPS_mo_other _ _ _ mo mo' NI OTH). apply (OPS_frame_other _ _ (ms_mem ms) m' mo NI H).
  - intros a Ha FP. destruct (OPS_fp_other _ _ a NI FP) as [R|[(a' & R & ->)|(a' & R & ->)]].
    + destruct (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact R)) as (E1 & _). unfold ALib.Mem.wa in E1. symmetry. exact E1.
    + pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [right; left; exact R| reflexivity]))) as E1.
      unfold ALib.Mem.wa in E1. symmetry. exact E1.
    + pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact R| reflexivity]))) as E1.
      unfold ALib.Mem.wa in E1. symmetry. exact E1.
  - intros a Ha C W. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in W.
    refine (proj2 (PRES a ltac:(unfold two64 in Ha; lia) _) W).
    destruct C as [C|[(a' & C & ->)|(a' & C & ->)]]; [right; left; exact C| |]; right; right; right; exists a'; (split; [| reflexivity]); [right; left; exact C| left; exact C].
Qed.

Lemma aci_low : forall a, in_ranges (aci AI) a -> a < AIMG_HI.
Proof. intros a (iv0 & Hi & R). pose proof (AI_aci_img AI iv0 Hi). lia. Qed.

Lemma APART_g : forall RG : IMap.t region,
  (forall a, in_based E' RG a -> in_iv (shad Ablk, shlen (N + 7)) a \/ in_iv (Ablk, N) a \/ in_based E' (s_regs st) a) ->
  ops_apart asegs OPS E' ops' RG (s_priv st).
Proof.
  intros RG RGB.
  destruct NEWB as (NN & BR & _). destruct (twin_band _ _ BR NN) as (T1 & T2 & T3 & _). destruct BR as (BK & _ & TOP & _).
  unfold ablk, AIMG_HI, KLS in BK.
  apply (ops_apart_set_op asegs OPS E' E' (s_ops st) HEAP_ID hargs h3 (s_regs st) RG (s_priv st) Hf Hc (so_apart _ _ _ _ _ _ HS')).
  - intros o a Ho NI OLD FP. destruct (OLD FP) as [NB IP]. split; [| exact IP].
    intros IB. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    pose proof atop_range as ATR. pose proof ATOP_al16 as AT16.
    assert (LOW : a < 6483968 \/ 0x7fff8000 <= a < 0x800bde00 \/ shad ATOP <= a < 0x10007fff8000).
    { destruct (OPS_fp_other _ _ a NI FP) as [R|[(a' & R & ->)|(a' & R & ->)]]; [left; pose proof (aci_low a R) as X; unfold AIMG_HI in X; exact X| |].
      - right. left. apply CtrPre.shad_img_band. split; [destruct R as (iv0 & Hi & R); pose proof (AI_aci_lo AI iv0 Hi); lia| exact (aci_low a' R)].
      - right. right. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - R ATR. Z.div_mod_to_equations. lia. }
    assert (SHA : 0x800bde00 <= shad Ablk) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).

    assert (SHT : shad Ablk + shlen (N + 7) <= shad ATOP).
    { destruct NEWB as (_ & (_ & N0 & _ & A16) & _). unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      clear - TOP N0 A16 AT16. Z.div_mod_to_equations. lia. }
    assert (SHATOP : 0x7fff8000 + 0x7fff7f800000 / 8 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - ATR; Z.div_mod_to_equations; lia).
    destruct (RGB a IB) as [I|[I|I]]; [unfold in_iv in I; cbn [fst snd] in I; lia| unfold in_iv in I; cbn [fst snd] in I; lia| exact (NB I)].
  - intros a FP. rewrite OPS_fp1 in FP. apply (proj1 (fp_spec IMGX _ _ _ _ _ a DEC3)) in FP as (Ha & NIX & NWS).
    assert (NW0 : ~ in_ws (wins_of E n rest) a) by (intros X; apply NWS; apply in_ws_app; left; apply in_ws_app; left; exact X).
    destruct (ops_apart_find asegs OPS E' (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a (so_apart _ _ _ _ _ _ HS') Hf) as [NB IP].
    { rewrite OPS_fp1. apply (proj2 (fp_spec IMGX _ _ _ _ _ a DEC')). auto. }
    split; [| exact IP]. intros IB. destruct (RGB a IB) as [I|[I|I]]; [| | exact (NB I)]; apply NWS; apply in_ws_app.
    + right. unfold in_ws. apply in_ivs_In. exists (w_iv WT). split; [left; reflexivity| exact I].
    + left. apply in_ws_app. right. unfold in_ws. apply in_ivs_In. exists (w_iv WB). split; [left; reflexivity| exact I].
Qed.

Lemma APART' : ops_apart asegs OPS E' ops' RgP (s_priv st).
Proof. exact (APART_g RgP RgP_in_based). Qed.

Lemma ops'_cases : In (OpI HEAP_ID h3) ops' /\ forall o, In o (s_ops st) -> o = OpI HEAP_ID hargs \/ In o ops'.
Proof.
  destruct (find_op_unique HEAP_ID (s_ops st) hargs Hf Hc) as (l1 & l2 & E0 & F1 & F2). unfold ops'. rewrite E0, (set_op_split HEAP_ID h3 l1 l2 hargs F1).
  split; [apply in_app_iff; right; left; reflexivity|].
  intros o Ho. apply in_app_iff in Ho as [Ho|[Ho|Ho]]; [right; apply in_app_iff; left; exact Ho| left; symmetry; exact Ho| right; apply in_app_iff; right; right; exact Ho].
Qed.

Lemma COVER_g : forall RG : IMap.t region,
  (forall a, in_based E' RG a -> in_iv (shad Ablk, shlen (N + 7)) a \/ in_iv (Ablk, N) a \/ in_based E' (s_regs st) a) ->
  forall a, fx_acc asegs E' RG a -> op_cov OPS (insts E' ops') a.
Proof.
  intros RG RGB a [IB|IMG]; [| left; exact (OPS_cov0_img a IMG)].
  destruct ops'_cases as [INH OTHERS].
  assert (NEWCOV0 : in_ws (heap_ws ((wins_of E n rest ++ [WB]) ++ [WT])) a \/ sh_cov a -> op_cov OPS (insts E' ops') a).
  { intros X. right. apply Exists_exists. exists (HEAP_ID, map (den E') h3). split.
    - unfold insts. apply in_map_iff. exists (OpI HEAP_ID h3). split; [reflexivity| exact INH].
    - cbn [fst snd]. apply OPS_cov1. split; [reflexivity|]. eexists _, _, _, _. split; [exact DEC3| exact X]. }
  assert (NEWCOV : in_ws (heap_ws ((wins_of E n rest ++ [WB]) ++ [WT])) a -> op_cov OPS (insts E' ops') a) by (intros X; exact (NEWCOV0 (or_introl X))).
  assert (HWS : forall w, In w [WB; WT] -> in_iv (w_iv w) a -> in_ws (heap_ws ((wins_of E n rest ++ [WB]) ++ [WT])) a).
  { intros w Hw I. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv w). split; [| exact I]. apply in_map. apply filter_In. split.
    - destruct Hw as [<-|[<-|[]]]; [apply in_or_app; left; apply in_or_app; right; left; reflexivity| apply in_or_app; right; left; reflexivity].
    - destruct Hw as [<-|[<-|[]]]; reflexivity. }
  destruct (RGB a IB) as [I|[I|I]].
  - apply NEWCOV. apply (HWS WT); [right; left; reflexivity| exact I].
  - apply NEWCOV. apply (HWS WB); [left; reflexivity| exact I].
  - destruct (so_cover _ _ _ _ _ _ HS' a (or_introl I)) as [C0|C1]; [left; exact C0|].
    apply Exists_exists in C1 as (oi & Hoi & CV). unfold insts in Hoi. apply in_map_iff in Hoi as (o & <- & Ho). cbn [fst snd] in CV.
    destruct (OTHERS o Ho) as [->|INo].
    + cbn [op_id op_args] in CV. apply OPS_cov1 in CV as (_ & md0 & aw0 & ws0 & ca0 & D0 & X). rewrite DEC' in D0. injection D0 as <- <- <- <-.
      destruct X as [X|X]; [| exact (NEWCOV0 (or_intror X))].
      apply NEWCOV. unfold in_ws, heap_ws in *. apply in_ivs_In in X as (v & Hv & Hin). apply in_ivs_In. exists v. split; [| exact Hin].
      apply in_map_iff in Hv as (w & <- & Hw). apply in_map. apply filter_In in Hw as [Hw K]. apply filter_In. split; [| exact K].
      apply in_or_app. left. apply in_or_app. left. exact Hw.
    + right. apply Exists_exists. exists (op_id o, map (den E') (op_args o)). split; [| exact CV].
      unfold insts. apply in_map_iff. exists o. split; [reflexivity| exact INo].
Qed.

Lemma COVER' : forall a, fx_acc asegs E' RgP a -> op_cov OPS (insts E' ops') a.
Proof. exact (COVER_g RgP RgP_in_based). Qed.

Definition f_range : fact := FRange kB BLK_LO BLK_HI.
Definition f_align : fact := FAlign kB 4%uint63.
Definition f_link : fact := FEq (VP kS wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP kB wzero) (VL (wlit 3%uint63))) (VL SBw)).

Definition f_cred : fact := cred_fact (s_facts st) nsv A.
Hypothesis CREDF : fact_holds E f_cred.
Lemma CREDF' : fact_holds E' f_cred.
Proof.
  revert CREDF. unfold f_cred, cred_fact. destruct (prim_decided (s_facts st) nsv); cbn [fact_holds].
  - rewrite (den_E' A A_below). cbn [den]. intros X; exact X.
  - rewrite (den_E' nsv nsv_below), (den_E' A A_below). intros X; exact X.
Qed.

Lemma FACTS' : facts_hold E' (f_link :: f_align :: f_range :: f_cred :: s_facts st).
Proof.
  destruct NEWB as (NN & BR & _). destruct BR as (BK & _ & TOP & AL). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  constructor; [| constructor; [| constructor; [| constructor; [exact CREDF'| exact (so_facts _ _ _ _ _ _ HS')]]]].
  - cbn [fact_holds f_link]. rewrite HeapCtr.den_VPz.
    change (den E' (VAlu ALU_ADD (VAlu ALU_SRL (VP kB wzero) (VL (wlit 3%uint63))) (VL SBw)))
      with (alu64 ALU_ADD (alu64 ALU_SRL (den E' (VP kB wzero)) (wbv (wlit 3%uint63))) (wbv SBw)).
    rewrite HeapCtr.den_VPz. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned, ev_kS, ev_kB.
    replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
    replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
    change (Z.land 3 63) with 3.
    replace (bv_unsigned (wbv SBw)) with 0x7fff8000 by (vm_compute; reflexivity).
    unfold shad, ASHOFF, bv_wrap, bv_modulus. rewrite Z.mod_small; [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    change (2 ^ Z.of_N 64) with (2 ^ 64). clear - BK TOP ATR NN. Z.div_mod_to_equations. lia.
  - cbn [fact_holds f_align]. rewrite ev_kB. change (2 ^ to_Z 4%uint63) with 16. exact AL.
  - cbn [fact_holds f_range]. rewrite ev_kB. replace (w2Z BLK_LO) with 0x62f000 by (vm_compute; reflexivity).
    replace (w2Z BLK_HI) with (2 ^ 47 - 1) by (vm_compute; reflexivity). lia.
Qed.

Hypothesis A0' : AP.getr R' 10%bv = Z_to_bv 64 Ablk.
Hypothesis MINVo : op_minv OPS mo'.

Lemma kB_next : s_next (clobber st1) = kB.
Proof.
  destruct (clobber_fields st1) as (_ & _ & _ & _ & _ & _ & _ & NXc). destruct st1_fields as (_ & _ & _ & _ & _ & _ & _ & NX1).
  rewrite NXc, NX1. symmetry. destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma kS_next : PrimInt63.add kB 1%uint63 = kS.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  apply Uint63.to_Z_inj. rewrite add_Z by (rewrite kB_Z; change (to_Z 1%uint63) with 1; rewrite wB_two63, two63_eq; lia).
  rewrite kB_Z, kS_Z. change (to_Z 1%uint63) with 1. lia.
Qed.

Lemma stB_shape : alloc_stB_g TWR XN st st1 r h3 A
  = SS r (rf_set (s_rf (clobber st1)) X10 (VP kB wzero)) (s_ff st) (s_resv st) RgP
       (f_link :: f_align :: f_range :: f_cred :: s_facts st) ops' (s_priv st) (PrimInt63.add kS 1%uint63).
Proof.
  unfold alloc_stB_g. cbv zeta. rewrite kB_next, kS_next. fold nsv. rewrite stB_shape_gen.
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & _). destruct st1_fields as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & _).
  rewrite FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1, st1_regs. reflexivity.
Qed.

Theorem post_B : st_ok asegs OPS E' (alloc_stB_g TWR XN st st1 r h3 A) ms' mo'.
Proof.
  rewrite stB_shape.
  assert (DKB : den E' (VP kB wzero) = AP.getr R' 10%bv).
  { rewrite HeapCtr.den_VPz, A0'. apply bv_eq. rewrite ev_kB. destruct NEWB as (NN & (BK & _ & TOP & _) & _). pose proof atop_range.
    unfold ablk, AIMG_HI, KLS in BK. symmetry. apply Z_to_bv_small. unfold bv_modulus, two64. lia. }
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next ms' ms_pc_val ms_regs ms_fregs ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending MS].
  - reflexivity.
  - rewrite rf_get_set_other by discriminate. change (rf_get (s_rf (clobber st1)) X0) with (getr (clobber st1) X0). rewrite getr_clobber. cbn [clob_pos].
    destruct st1_fields as (_ & RF1 & _). unfold getr. rewrite RF1. exact (so_x0 _ _ _ _ _ _ HS).
  - exact (post_regs (VP kB wzero) DKB).
  - exact (so_fregs _ _ _ _ _ _ HS').
  - reflexivity.
  - rewrite (HeapCtr.call_pre_resv st r CP). reflexivity.
  - exact (so_fcsr _ _ _ _ _ _ HS).
  - reflexivity.
  - exact (so_zero _ _ _ _ _ _ HS').
  - exact RgP_bst.
  - exact all_regions_ok.
  - exact RgP_disjoint.
  - exact RgP_pub.
  - exact FACTS'.
  - exact OPS_HOLD'.
  - exact APART'.
  - exact MINVo.
  - exact COVER'.
  - intros a b H seg Hs. pose proof (MINV' a b H) as X. unfold ALib.Mem.ro_addr in X. rewrite Hs in X.
    destruct (seg_writable seg); [reflexivity| discriminate X].
Qed.

Definition kS2 : int := addn (s_next st) 17.
Lemma kS2_Z : to_Z kS2 = to_Z (s_next st) + 17.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold kS2. rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma kS2_next : PrimInt63.add kS 1%uint63 = kS2.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  apply Uint63.to_Z_inj. rewrite add_Z by (rewrite kS_Z; change (to_Z 1%uint63) with 1; rewrite wB_two63, two63_eq; lia).
  rewrite kS_Z, kS2_Z. change (to_Z 1%uint63) with 1. lia.
Qed.
Lemma kS2_nz : PrimInt63.eqb kS2 0%uint63 = false.
Proof. apply Uint63.eqb_false_spec. intros X. pose proof kS2_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia. Qed.
Definition RgPb : IMap.t region := IMap.add kS2 (tail_region nsv) RgP.
Definition f_tail : fact := tail_fact kS2 kS nsv.
Definition f_sign : fact := FULt (VL wzero) nsv.

Lemma stBb_shape : TWR = twin_main nsv -> alloc_stBb XN st st1 r h3 A
  = SS r (rf_set (s_rf (clobber st1)) X10 (VP kB wzero)) (s_ff st) (s_resv st) RgPb
       (f_sign :: f_tail :: f_link :: f_align :: f_range :: f_cred :: s_facts st) ops' (s_priv st) (PrimInt63.add kS2 1%uint63).
Proof.
  intros TM. unfold alloc_stBb. cbv zeta. rewrite kB_next, kS_next, kS2_next. fold nsv. rewrite stBb_shape_gen.
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & _). destruct st1_fields as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & _).
  rewrite FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1, st1_regs. unfold RgPb, RgP. rewrite TM. reflexivity.
Qed.

Section PAIR.
Hypothesis TM : TWR = twin_main nsv.
Hypothesis F17 : Fv 17 = Z_to_bv 64 (shad Ablk + (N - 1) / 8).

Lemma tail_geo : 0 <= (N - 1) / 8 /\ (N - 1) / 8 + 1 <= (N + 7) / 8 /\ shad Ablk + (N + 7) / 8 <= 0x10007fff8000.
Proof.
  destruct NEWB as (NN & BR & _). destruct (twin_band _ _ BR NN) as (T1 & T2 & _). unfold shlen in T2. rewrite Z.shiftr_div_pow2 in T2 by lia. change (2 ^ 3) with 8 in T2.
  split; [clear - NN; Z.div_mod_to_equations; lia|]. split; [clear - NN; Z.div_mod_to_equations; lia| exact T2].
Qed.
Lemma ev_kS2 : bv_unsigned (ev E' kS2) = shad Ablk + (N - 1) / 8.
Proof.
  unfold kS2. rewrite ev_E'_fresh by lia. change (Z.of_nat 17) with 17. rewrite F17. destruct NEWB as (N1 & BR & _).
  destruct (twin_band _ _ BR N1) as (T1 & _). destruct tail_geo as (G0 & G1 & G2). apply Z_to_bv_small. unfold bv_modulus, two64. lia.
Qed.
Lemma tail_range : forall a, bv_unsigned (ev E' kS2) + loZ (tail_region nsv) <= a < bv_unsigned (ev E' kS2) + hiZ E' (tail_region nsv) ->
  a = shad Ablk + (N - 1) / 8 /\ in_iv (shad Ablk, shlen (N + 7)) a.
Proof.
  intros a Ha. destruct (CallA.tail_region_fields nsv) as (LO & HI & _). rewrite ev_kS2 in Ha.
  assert (LZ : loZ (tail_region nsv) = 0) by (unfold loZ; rewrite LO; reflexivity).
  assert (HZ : hiZ E' (tail_region nsv) = 1) by (unfold hiZ; rewrite HI; cbn [den]; rewrite wbv_unsigned; reflexivity).
  rewrite LZ, HZ in Ha. destruct tail_geo as (G0 & G1 & _). split; [lia|]. unfold in_iv, shlen. cbn [fst snd]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
Qed.
Lemma tail_region_okA : region_ok asegs (s_priv st) E' m' kS2 (tail_region nsv).
Proof.
  destruct NEWB as (N1 & BR & WR). destruct WORLD' as (_ & PAT & _). pose proof WORLD'_asan as AWH'. destruct tail_geo as (G0 & G1 & G2).
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (den_E' nsv nsv_below); exact NDEN).
  apply (CallA.tail_region_ok asegs (s_priv st) E' m' kS2 nsv kS2_nz); rewrite ?DN, ?ev_kS2.
  - unfold two64. lia.
  - pose proof (PAT ((N - 1) / 8) G0 ltac:(clear - N1; Z.div_mod_to_equations; lia)) as P1. unfold rb. unfold ALib.Mem.wa in P1. rewrite P1.
    do 2 f_equal. destruct (Z.leb_spec (8 * ((N - 1) / 8) + 8) N) as [FL|PT]; [clear - N1 FL| clear - N1 PT]; Z.div_mod_to_equations; lia.
  - apply (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw' LB' m' mo' _ (shad Ablk + (N - 1) / 8) AWH' ltac:(left; reflexivity)
                   ltac:(unfold in_iv; cbn [fst snd]; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; lia))).
Qed.
Lemma RgPb_find : forall k0 rg, IMap.find k0 RgPb = Some rg -> (k0 = kS2 /\ rg = tail_region nsv) \/ (k0 <> kS2 /\ IMap.find k0 RgP = Some rg).
Proof.
  intros k0 rg H. unfold RgPb in H. destruct (Uint63.eqb kS2 k0) eqn:Q.
  - apply Uint63.eqb_correct in Q. subst k0. rewrite IMap.find_add_same in H by exact RgP_bst. injection H as <-. left. auto.
  - rewrite IMap.find_add_other_eqb in H by (exact RgP_bst || exact Q). right. apply Uint63.eqb_false_spec in Q. split; [congruence| exact H].
Qed.
Lemma RgPb_in_based : forall a, in_based E' RgPb a ->
  in_iv (shad Ablk, shlen (N + 7)) a \/ in_iv (Ablk, N) a \/ in_based E' (s_regs st) a.
Proof.
  intros a (k0 & rg & H & KZ & R). destruct (RgPb_find k0 rg H) as [[-> ->]|[_ F]].
  - left. exact (proj2 (tail_range a R)).
  - apply RgP_in_based. exists k0, rg. auto.
Qed.

Lemma twin_iv_apart : forall k0 rg a, IMap.find k0 RgP = Some rg -> PrimInt63.eqb k0 0%uint63 = false -> k0 <> kS ->
  bv_unsigned (ev E' k0) + loZ rg <= a < bv_unsigned (ev E' k0) + hiZ E' rg -> in_iv (shad Ablk, shlen (N + 7)) a -> False.
Proof.
  intros k0 rg a H KZ NK Ha I.
  destruct NEWB as (NN & BR & _). destruct (twin_band _ _ BR NN) as (T1 & T2 & T3 & _). destruct WORLD' as (_ & _ & UB & DJ & _ & DJT).
  pose proof atop_range as ATR. pose proof sp_floor as SPF. destruct BR as (BK & _ & TOP & _). unfold ablk, AIMG_HI, KLS in BK.
  assert (TW_B : in_iv (Ablk, N) a -> False) by (unfold in_iv in *; cbn [fst snd] in *; unfold user_band in UB; lia).
  assert (TW_S : ATOP + 4096 <= a -> False) by (unfold in_iv in I; cbn [fst snd] in I; lia).
  assert (SHB : sh_cov a -> (0x7fffa000 <= a < 0x800bdca8) \/ (shad ATOP <= a < 0x10007fff8000)) by exact (sh_cov_band a).
  destruct (shadow_tight Ablk N ltac:(unfold ablk, AIMG_HI, KLS; exact BK) TOP ltac:(lia)) as [TT1 TT2].
  assert (TW_C : sh_cov a -> False) by (intros Y; apply SHB in Y; unfold in_iv in I; cbn [fst snd] in I; lia).
  destruct (RgP_range k0 rg a H KZ Ha) as [[E1 _]|[[_ I2]|[[_ I2]|(_ & _ & _ & [I2|[I2|I2]])]]].
  - contradiction.
  - exact (TW_B I2).
  - exact (TW_S (proj1 I2)).
  - exact (TW_S (proj1 I2)).
  - exact (DJT a I I2).
  - exact (TW_C I2).
Qed.
Lemma FACTSb : facts_hold E' (f_sign :: f_tail :: f_link :: f_align :: f_range :: f_cred :: s_facts st).
Proof.
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (den_E' nsv nsv_below); exact NDEN). destruct tail_geo as (G0 & G1 & G2).
  constructor; [| constructor; [| exact FACTS']].
  - cbn [fact_holds f_sign]. rewrite DN. cbn [den]. rewrite wbv_unsigned, wzero_ok. destruct NEWB as (NN & _). clear - NN. lia.
  - unfold f_tail, tail_fact. cbn [fact_holds]. rewrite HeapCtr.den_VPz. apply bv_eq. destruct NEWB as (NN & _).
    rewrite (CallA.tail_rhs_den E' kS nsv) by (rewrite ?ev_kS, DN; clear - NN G0 G1 G2; lia). rewrite ev_kS2, ev_kS, DN. reflexivity.
Qed.

Theorem post_Bb : st_ok asegs OPS E' (alloc_stBb XN st st1 r h3 A) ms' mo'.
Proof.
  pose proof post_B as PB. rewrite stB_shape in PB. rewrite (stBb_shape TM).
  destruct PB as [Qpc Qx0 Qregs Qfregs Qsvc Qresv Qfcsr Qrom Qz Qbst Qreg Qdisj Qpub Qfacts Qops Qapart Qmf Qcov Qminv].
  cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in *.
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - unfold RgPb. apply IMap.bst_add. exact RgP_bst.
  - intros k0 rg H. destruct (RgPb_find k0 rg H) as [[-> ->]|[_ F]]; [exact tail_region_okA| exact (Qreg k0 rg F)].
  - intros k1 rg1 k2 rg2 H1 H2 NE Z1 Z2 WR a [A1 A2]. destruct TWR_geo as (_ & _ & TWW).
    destruct (CallA.tail_region_fields nsv) as (_ & _ & TLW & _).
    destruct (RgPb_find k1 rg1 H1) as [[-> ->]|[N1 F1]]; destruct (RgPb_find k2 rg2 H2) as [[-> ->]|[N2 F2]].
    + contradiction.
    + destruct (tail_range a A1) as [_ I]. destruct (Uint63.eqb k2 kS) eqn:QS.
      * apply Uint63.eqb_correct in QS. subst k2. destruct (RgP_find kS rg2 F2) as [[_ ->]|[[X _]|[[X _]|(X & _)]]];
          [destruct WR as [W|W]; congruence | | |]; exfalso; pose proof kS_Z; pose proof kB_Z;
          [rewrite X in *; lia | destruct (CallA.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite <- X in *; lia | congruence].
      * apply Uint63.eqb_false_spec in QS. exact (twin_iv_apart k2 rg2 a F2 Z2 QS A2 I).
    + destruct (tail_range a A2) as [_ I]. destruct (Uint63.eqb k1 kS) eqn:QS.
      * apply Uint63.eqb_correct in QS. subst k1. destruct (RgP_find kS rg1 F1) as [[_ ->]|[[X _]|[[X _]|(X & _)]]];
          [destruct WR as [W|W]; congruence | | |]; exfalso; pose proof kS_Z; pose proof kB_Z;
          [rewrite X in *; lia | destruct (CallA.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite <- X in *; lia | congruence].
      * apply Uint63.eqb_false_spec in QS. exact (twin_iv_apart k1 rg1 a F1 Z1 QS A1 I).
    + exact (Qdisj k1 rg1 k2 rg2 F1 F2 NE Z1 Z2 WR a (conj A1 A2)).
  - intros r0 g gr c H0 Hg Hcc i Hi. destruct (RgPb_find _ _ H0) as [[X _]|[_ F]].
    + exfalso. pose proof kS2_Z as KZ. rewrite <- X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia.
    + exact (Qpub r0 g gr c F Hg Hcc i Hi).
  - exact FACTSb.
  - exact (APART_g RgPb RgPb_in_based).
  - exact (COVER_g RgPb RgPb_in_based).
Qed.
End PAIR.

Theorem post_all : st_ok asegs OPS E' (alloc_stB_g TWR XN st st1 r h3 A) ms' mo'
  /\ (TWR = twin_main nsv -> Fv 17 = Z_to_bv 64 (shad Ablk + (N - 1) / 8) -> st_ok asegs OPS E' (alloc_stBb XN st st1 r h3 A) ms' mo').
Proof. split; [exact post_B| exact post_Bb]. Qed.
Lemma FEQ_holds : N mod 8 = 0 -> fact_holds E' (FEq (sz_and7 nsv) (VL wzero)).
Proof.
  intros Z8. cbn [fact_holds]. apply bv_eq. rewrite CallA.sz_and7_den, (den_E' nsv nsv_below), NDEN, Z8. cbn [den]. rewrite wbv_unsigned, wzero_ok. reflexivity.
Qed.

End POST.

Definition cfvA (R' : bvmap 5 word) (A S : word) (i : Z) : word :=
  nth (Z.to_nat i)
      [AP.getr R' 1%bv; AP.getr R' 5%bv; AP.getr R' 6%bv; AP.getr R' 7%bv;
       AP.getr R' 11%bv; AP.getr R' 12%bv; AP.getr R' 13%bv; AP.getr R' 14%bv;
       AP.getr R' 15%bv; AP.getr R' 16%bv; AP.getr R' 17%bv;
       AP.getr R' 28%bv; AP.getr R' 29%bv; AP.getr R' 30%bv; AP.getr R' 31%bv; A; S] (Z_to_bv 64 0).
Lemma cfvA_clob : forall R' A S x i, clob_pos x = Some i -> cfvA R' A S (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Proof. intros R' A S x i H. destruct x; cbn in H; try discriminate; injection H as <-; cbn; f_equal; apply bv_eq; reflexivity. Qed.

Definition cfvT (R' : bvmap 5 word) (A S T : word) (i : Z) : word :=
  nth (Z.to_nat i)
      [AP.getr R' 1%bv; AP.getr R' 5%bv; AP.getr R' 6%bv; AP.getr R' 7%bv;
       AP.getr R' 11%bv; AP.getr R' 12%bv; AP.getr R' 13%bv; AP.getr R' 14%bv;
       AP.getr R' 15%bv; AP.getr R' 16%bv; AP.getr R' 17%bv;
       AP.getr R' 28%bv; AP.getr R' 29%bv; AP.getr R' 30%bv; AP.getr R' 31%bv; A; S; T] (Z_to_bv 64 0).
Lemma cfvT_clob : forall R' A S T x i, clob_pos x = Some i -> cfvT R' A S T (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Proof. intros R' A S T x i H. destruct x; cbn in H; try discriminate; injection H as <-; cbn; f_equal; apply bv_eq; reflexivity. Qed.

Lemma amalloc_post_okA : forall st sts E ms mo (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (n : Z)
    rr RNG' msP mo',
  st_ok asegs OPS E st ms mo -> amalloc_apply UNIV AMALLOC_PC st = Some sts ->
  CtrPre.acall_facts AI ACCT UNIV Cw X10 E st ms mo L RNG sta LBa aw n ->
  let R := ms_regs ms in
  amalloc_post2 (aci AI) (AHEAP AI) L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa n (CtrPre.sp_lo E st) (ms_mem ms) rr RNG' msP ->
  (forall Aaddr, match snd rr with
                 | Some p => ACCT (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X10) then 0 else n))) L RNG' (fst rr) (HB p Aaddr n :: LBa) mo'
                 | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst rr) LBa mo'
                 end) ->
  (CtrPre.prist_in E st -> aprist (fst rr)) ->
  op_minv OPS mo' -> OTHER mo mo' ->
  exists stB E1, In stB (tl sts) /\ env_ext (s_next st) E E1 /\ st_ok asegs OPS E1 stB msP mo'.
Proof.
  intros st sts E ms mo L RNG sta LBa aw n rr RNG' msP mo' HS Happ CF R HQ ACP PRSX MINVo OTH.
  destruct CF as (LB & r & hargs & st1 & ks & offs & rss & ksp & wnl & nn & md & A & nw & rest
                  & CP & FS & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255 & NW & AJ & WF & HC & AWden & (W & WOF & AR & TI) & NDEN & SHAPE).
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (PRS0 : In prist_win (wins_of E nn rest) -> aprist (fst rr)).
  { intros IP. apply PRSX. exists hargs, md, A, nw, rest. rewrite <- Nn. auto. }

  destruct HQ as (FPLE & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV' & STK' & PRES & TWP & POSTB).
  destruct (snd rr) as [p|] eqn:SR; [| contradiction].
  destruct POSTB as (Ablk & junk & EA0 & BRN & AH' & RW & _ & _ & _ & PATN).
  specialize (ACP Ablk). cbv beta iota in ACP.
  set (R' := mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) t0 t1 t2 (AP.getr R 8) (AP.getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) t3 t4 t5 t6) in *.
  set (Fv := cfvT R' (Z_to_bv 64 Ablk) (Z_to_bv 64 (shad Ablk)) (Z_to_bv 64 (shad Ablk + (n - 1) / 8))).
  set (Gv := fun (_ : Z) (o : Z) => match m' (ALib.Mem.wa (Ablk + o)) with Some b => b | None => Z_to_bv 8 0 end).

  destruct (amalloc_apply_shape UNIV AMALLOC_PC st sts Happ) as (r2 & hargs2 & cred2 & st12 & h1 & h2 & h3x & stN & CP2 & Hf2 & HA2 & FS2 & S1 & S2 & S3 & NPOST & SHP).
  rewrite CP in CP2. injection CP2 as <-. rewrite Hf in Hf2. injection Hf2 as <-. rewrite FS in FS2. injection FS2 as <-.
  rewrite Eh, heap_A_eq in HA2. injection HA2 as <-.
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.reg_of_X1, (GlueA.getr_RA asegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.den_wlit. }
  assert (EMS' : msP = ms' ms r R' m').
  { rewrite EMS. unfold ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  rewrite EMS'.

  destruct (h3_shape E st ms Fv Gv ksp nn rest X10 hargs md A nw Hc Eh Tnw Nn Ln N255 (prim_decided (s_facts st) (getr st X10))) as (Q1 & Q2 & Q3).
  assert (KBE : s_next (clobber st1) = kB st) by (eapply kB_next; eassumption).
  assert (KSE : PrimInt63.add (kB st) 1%uint63 = kS st) by (eapply kS_next; eassumption).
  unfold cred', nsv in Q1, Q2, Q3.
  unfold cred_post in S1. assert (E1 : h1 = VL md :: (if prim_decided (s_facts st) (getr st X10) then A else sv_alu ALU_SUB A (getr st X10)) :: VL nw :: rest) by congruence. subst h1.
  rewrite KBE in S2. assert (E2 : h2 = VL md :: (if prim_decided (s_facts st) (getr st X10) then A else sv_alu ALU_SUB A (getr st X10)) :: VL (nwB nw) :: restB st nn rest X10) by congruence. subst h2.
  rewrite KBE, KSE in S3. assert (E3 : h3x = h3 st nn rest X10 md A nw (prim_decided (s_facts st) (getr st X10))) by congruence. subst h3x.
  destruct (NEWB m' L RNG' (fst rr) LBa p Ablk n AH') as (NN & BRN' & WRN).
  assert (AWH' : aw_holds_asan AI ACCT UNIV (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X10) then 0 else n))) (LB' LB Ablk n) m' mo').
  { eapply (WORLD'_asan ms mo m'); eassumption. }
  assert (ALL : forall TWR, (TWR = twin_region (getr st X10) /\ match getr st X10 with VL _ => True | _ => n mod 8 = 0 end) \/ TWR = twin_main (getr st X10) ->
            st_ok asegs OPS (E' E st Fv Gv) (alloc_stB_g TWR X10 st st1 r (h3 st nn rest X10 md A nw (prim_decided (s_facts st) (getr st X10))) A) (ms' ms r R' m') mo'
            /\ (TWR = twin_main (getr st X10) -> Fv 17 = Z_to_bv 64 (shad Ablk + (n - 1) / 8) ->
                st_ok asegs OPS (E' E st Fv Gv) (alloc_stBb X10 st st1 r (h3 st nn rest X10 md A nw (prim_decided (s_facts st) (getr st X10))) A) (ms' ms r R' m') mo')).
  { intros TWR TWSH.
  apply (post_all E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo') with (aw := aw) (LB := LB) (L := L) (RNG := RNG) (RNG' := RNG') (sta := sta)
       (sta' := fst rr) (LBa := LBa) (WW := W) (p := p) (Ablk := Ablk) (N := n) (XN := X10) (ks := ks) (offs := offs) (rss := rss) (ksp := ksp) (wnl := wnl)
       (aw' := Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X10) then 0 else n))) (hargs := hargs) (pd := prim_decided (s_facts st) (getr st X10)); try assumption.
  -   intros rg Hrg. unfold kept_regsA in Hrg. cbn [In] in Hrg.
    repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
  -   intros x i Hx. exact (cfvT_clob R' _ _ _ x i Hx).
  -   intros wlo SW. exact (CallV.wlo_floor E st hargs nn md A nw rest LB (ATOP + 4096) wlo Hf Eh Tnw Nn Ln WF SW).
  -   reflexivity.
  -   reflexivity.
  -   intros o Ho. unfold Gv, rb.
    destruct (aw_user_ok_asan AI ACCT UNIV AI_fake _ _ m' mo' (Ablk, n) (Ablk + o) AWH' ltac:(right; left; reflexivity) ltac:(unfold in_iv; cbn [fst snd]; lia)) as [MP _].
    unfold ALib.Mem.wa. destruct (m' (Z_to_bv 64 (Ablk + o))); [reflexivity| contradiction].
  -   reflexivity.
  -
    destruct (CtrPre.amalloc_apply_inv UNIV st _ Happ) as (r9 & tp9 & hargs9 & cred9 & st19 & _ & _ & FO9 & HA9 & _ & _ & _ & _ & _ & _ & _ & _ & NC9 & _).
    rewrite Hf in FO9. injection FO9 as <-. rewrite Eh, heap_A_eq in HA9. injection HA9 as <-.
    pose proof (so_facts _ _ _ _ _ _ HS) as HF9. unfold f_cred, cred_fact, cred_pre, nsv in *. apply andb_prop in NC9 as [NX9 NC9].
    destruct (prim_decided (s_facts st) (getr st X10)); cbn [fact_holds].
    + exact (KnownA.KnownA.known_leu_sound E _ _ _ HF9 NX9).
    + cbn [orb] in NC9. exact (KnownA.KnownA.known_leu_sound E _ _ _ HF9 NC9). }

  pose proof (so_facts _ _ _ _ _ _ HS) as HFx.
  assert (SHSEM : size_shape_ok (s_facts st) (getr st X10) = true -> match getr st X10 with VL _ => True | _ => n mod 8 = 0 end).
  { intros SS. pose proof (CallA.size_shape_sound E _ (getr st X10) HFx SS) as X. rewrite NDEN in X. exact X. }
  assert (Z8SEM : n mod 8 = 0 -> match getr st X10 with VL _ => True | _ => n mod 8 = 0 end) by (intros Z8; destruct (getr st X10); try exact I; exact Z8).
  destruct SHP as [[SS ->]|(SS & ->)].
  - exists (amalloc_stB st st1 r (h3 st nn rest X10 md A nw (prim_decided (s_facts st) (getr st X10))) A), (E' E st Fv Gv).
    split; [left; reflexivity|]. split; [apply EXT|]. exact (proj1 (ALL _ (or_introl (conj eq_refl (SHSEM SS))))).
  -
    exists (alloc_stBb X10 st st1 r (h3 st nn rest X10 md A nw (prim_decided (s_facts st) (getr st X10))) A), (E' E st Fv Gv).
    split; [left; reflexivity|]. split; [apply EXT|]. exact (proj2 (ALL _ (or_intror eq_refl)) eq_refl eq_refl).
Qed.

Lemma aaligned_post_okA : forall st sts E ms mo (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (n : Z)
    rr RNG' msP mo',
  st_ok asegs OPS E st ms mo -> aaligned_apply UNIV F_aaligned_iseg.AALIGNED_PC st = Some sts ->
  CtrPre.acall_facts AI ACCT UNIV Cw X11 E st ms mo L RNG sta LBa aw n ->
  let R := ms_regs ms in
  amalloc_post2 (aci AI) (AHEAP AI) L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa n (CtrPre.sp_lo E st) (ms_mem ms) rr RNG' msP ->
  (forall Aaddr, match snd rr with
                 | Some p => ACCT (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) L RNG' (fst rr) (HB p Aaddr n :: LBa) mo'
                 | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst rr) LBa mo'
                 end) ->
  ~ CtrPre.prist_in E st ->
  op_minv OPS mo' -> OTHER mo mo' ->
  exists stN stB E1, sts = [stN; stB] /\ env_ext (s_next st) E E1 /\ st_ok asegs OPS E1 stB msP mo'.
Proof.
  intros st sts E ms mo L RNG sta LBa aw n rr RNG' msP mo' HS Happ CF R HQ ACP PRSX MINVo OTH.
  destruct CF as (LB & r & hargs & st1 & ks & offs & rss & ksp & wnl & nn & md & A & nw & rest
                  & CP & FS & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255 & NW & AJ & WF & HC & AWden & (W & WOF & AR & TI) & NDEN & SHAPE).
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (PRS0 : In prist_win (wins_of E nn rest) -> aprist (fst rr)).
  { intros IP. exfalso. apply PRSX. exists hargs, md, A, nw, rest. rewrite <- Nn. auto. }

  destruct HQ as (FPLE & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV' & STK' & PRES & TWP & POSTB).
  destruct (snd rr) as [p|] eqn:SR; [| contradiction].
  destruct POSTB as (Ablk & junk & EA0 & BRN & AH' & RW & _ & _ & _ & PATN).
  specialize (ACP Ablk). cbv beta iota in ACP.
  set (R' := mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) t0 t1 t2 (AP.getr R 8) (AP.getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) t3 t4 t5 t6) in *.
  set (Fv := cfvA R' (Z_to_bv 64 Ablk) (Z_to_bv 64 (shad Ablk))).
  set (Gv := fun (_ : Z) (o : Z) => match m' (ALib.Mem.wa (Ablk + o)) with Some b => b | None => Z_to_bv 8 0 end).

  destruct (aaligned_apply_shape UNIV F_aaligned_iseg.AALIGNED_PC st sts Happ) as (r2 & hargs2 & cred2 & st12 & h1 & h2 & h3x & stN & CP2 & Hf2 & HA2 & FS2 & S1 & S2 & S3 & NPOST & ->).
  rewrite CP in CP2. injection CP2 as <-. rewrite Hf in Hf2. injection Hf2 as <-. rewrite FS in FS2. injection FS2 as <-.
  rewrite Eh, heap_A_eq in HA2. injection HA2 as <-.
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.reg_of_X1, (GlueA.getr_RA asegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.den_wlit. }
  assert (EMS' : msP = ms' ms r R' m').
  { rewrite EMS. unfold ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  exists stN. eexists. exists (E' E st Fv Gv). split; [reflexivity|]. split; [apply EXT|]. rewrite EMS'.

  destruct (h3_shape E st ms Fv Gv ksp nn rest X11 hargs md A nw Hc Eh Tnw Nn Ln N255 (prim_decided (s_facts st) (getr st X11))) as (Q1 & Q2 & Q3).
  assert (KBE : s_next (clobber st1) = kB st) by (eapply kB_next; eassumption).
  assert (KSE : PrimInt63.add (kB st) 1%uint63 = kS st) by (eapply kS_next; eassumption).
  unfold cred', nsv in Q1, Q2, Q3.
  unfold cred_post in S1. assert (E1 : h1 = VL md :: (if prim_decided (s_facts st) (getr st X11) then A else sv_alu ALU_SUB A (getr st X11)) :: VL nw :: rest) by congruence. subst h1.
  rewrite KBE in S2. assert (E2 : h2 = VL md :: (if prim_decided (s_facts st) (getr st X11) then A else sv_alu ALU_SUB A (getr st X11)) :: VL (nwB nw) :: restB st nn rest X11) by congruence. subst h2.
  rewrite KBE, KSE in S3. assert (E3 : h3x = h3 st nn rest X11 md A nw (prim_decided (s_facts st) (getr st X11))) by congruence. subst h3x.
  destruct (NEWB m' L RNG' (fst rr) LBa p Ablk n AH') as (NN & BRN' & WRN).
  assert (AWH' : aw_holds_asan AI ACCT UNIV (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) (LB' LB Ablk n) m' mo').
  { eapply (WORLD'_asan ms mo m'); eassumption. }
  assert (TWSH : (twin_region (getr st X11) = twin_region (nsv st X11) /\ match nsv st X11 with VL _ => True | _ => n mod 8 = 0 end) \/ twin_region (getr st X11) = twin_main (nsv st X11)).
  { left. split; [reflexivity|]. destruct (SHAPE eq_refl) as [wl0 EW]. unfold nsv. rewrite EW. exact I. }
  change (alloc_stB X11 st st1 r (h3 st nn rest X11 md A nw (prim_decided (s_facts st) (getr st X11))) A)
    with (alloc_stB_g (twin_region (getr st X11)) X11 st st1 r (h3 st nn rest X11 md A nw (prim_decided (s_facts st) (getr st X11))) A).
  apply (post_B E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo') with (aw := aw) (LB := LB) (L := L) (RNG := RNG) (RNG' := RNG') (sta := sta)
       (sta' := fst rr) (LBa := LBa) (WW := W) (p := p) (Ablk := Ablk) (N := n) (XN := X11) (ks := ks) (offs := offs) (rss := rss) (ksp := ksp) (wnl := wnl)
       (aw' := Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) (hargs := hargs) (pd := prim_decided (s_facts st) (getr st X11))
       (TWR := twin_region (getr st X11)); try assumption.
  -   intros rg Hrg. unfold kept_regsA in Hrg. cbn [In] in Hrg.
    repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
  -   intros x i Hx. exact (cfvA_clob R' _ _ x i Hx).
  -   intros wlo SW. exact (CallV.wlo_floor E st hargs nn md A nw rest LB (ATOP + 4096) wlo Hf Eh Tnw Nn Ln WF SW).
  -   reflexivity.
  -   reflexivity.
  -   intros o Ho. unfold Gv, rb.
    destruct (aw_user_ok_asan AI ACCT UNIV AI_fake _ _ m' mo' (Ablk, n) (Ablk + o) AWH' ltac:(right; left; reflexivity) ltac:(unfold in_iv; cbn [fst snd]; lia)) as [MP _].
    unfold ALib.Mem.wa. destruct (m' (Z_to_bv 64 (Ablk + o))); [reflexivity| contradiction].
  -   reflexivity.
  -
    destruct (CtrPre.aaligned_apply_inv UNIV st _ Happ) as (r9 & tp9 & hargs9 & cred9 & st19 & al9 & _ & _ & FO9 & HA9 & _ & _ & _ & _ & _ & _ & _ & _ & _ & NC9 & _).
    rewrite Hf in FO9. injection FO9 as <-. rewrite Eh, heap_A_eq in HA9. injection HA9 as <-.
    pose proof (so_facts _ _ _ _ _ _ HS) as HF9. unfold f_cred, cred_fact, cred_pre, nsv in *. apply andb_prop in NC9 as [NX9 NC9].
    destruct (prim_decided (s_facts st) (getr st X11)); cbn [fact_holds].
    + exact (KnownA.KnownA.known_leu_sound E _ _ _ HF9 NX9).
    + cbn [orb] in NC9. exact (KnownA.KnownA.known_leu_sound E _ _ _ HF9 NC9).
Qed.

End Post.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Unset Nia Cache. Unset Nra Cache.

Definition alloc_stB_g (TWR : region) (XN : r5) (st st1 : sstate) (r : int) (h3 : list sv) (cred : sv) : sstate :=
  let n := getr st XN in
  let st2 := clobber st1 in
  let k := s_next st2 in
  let sh := PrimInt63.add k 1%uint63 in
  let st4 := set_next (set_next st2 (PrimInt63.add k 1%uint63)) (PrimInt63.add sh 1%uint63) in
  let R' := IMap.add sh TWR (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty) (s_regs st4)) in
  let st5 := set_ops (setregs st4 R') (set_op HEAP_ID h3 (s_ops st4)) in
  let st6 := addfact (addfact (addfact (addfact st5 (cred_fact (s_facts st) n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
               (FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw))) in
  setpc (setr st6 X10 (VP k wzero)) r.
Definition alloc_stB (XN : r5) (st st1 : sstate) (r : int) (h3 : list sv) (cred : sv) : sstate :=
  alloc_stB_g (twin_region (getr st XN)) XN st st1 r h3 cred.

Definition amalloc_stB : sstate -> sstate -> int -> list sv -> sv -> sstate := alloc_stB X10.

Definition alloc_stBb (XN : r5) (st st1 : sstate) (r : int) (h3 : list sv) (cred : sv) : sstate :=
  let n := getr st XN in
  let st2 := clobber st1 in
  let k := s_next st2 in
  let sh := PrimInt63.add k 1%uint63 in
  let s2 := PrimInt63.add sh 1%uint63 in
  let st4b := set_next (set_next (set_next st2 (PrimInt63.add k 1%uint63)) (PrimInt63.add sh 1%uint63)) (PrimInt63.add s2 1%uint63) in
  let Rb := IMap.add s2 (tail_region n) (IMap.add sh (twin_main n) (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty) (s_regs st4b))) in
  let st5b := set_ops (setregs st4b Rb) (set_op HEAP_ID h3 (s_ops st4b)) in
  let st6b := addfact (addfact (addfact (addfact (addfact (addfact st5b (cred_fact (s_facts st) n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
               (FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw)))) (tail_fact s2 sh n)) (FULt (VL wzero) n) in
  setpc (setr st6b X10 (VP k wzero)) r.

Lemma amalloc_apply_shape : forall UNIV PCz st sts, amalloc_apply UNIV PCz st = Some sts ->
  exists r hargs cred st1 h1 h2 h3 stN,
    call_pre st = Some r /\ find_op HEAP_ID (s_ops st) = Some hargs /\ heap_A hargs = Some cred
    /\ forget_stack_below_sp_g st = Some st1
    /\ heap_set_A hargs (cred_post (s_facts st) (getr st X10) cred) = Some h1
    /\ heap_add_window h1 (VP (s_next (clobber st1)) wzero) (getr st X10) (VL CtrLib.K_BLOCK) = Some h2
    /\ heap_add_window h2 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X10)) (VL K_TWIN) = Some h3
    /\ null_post hargs cred (clobber st1) r = Some stN
    /\ (   (size_shape_ok (s_facts st) (getr st X10) = true /\ sts = [stN; amalloc_stB st st1 r h3 cred])
        \/ (size_shape_ok (s_facts st) (getr st X10) = false /\ sts = [stN; alloc_stBb X10 st st1 r h3 cred])).
Proof.
  intros UNIV PCz st sts H. unfold amalloc_apply in H.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |] eqn:TP; try discriminate.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:FO; [|discriminate].
  destruct (heap_A hargs) as [cred|] eqn:HA; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  destruct (forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate].
  destruct (null_post hargs cred (clobber st1) r) as [stN|] eqn:NP; [|discriminate].
  unfold fresh in H. cbv zeta in H. cbn [fst snd s_next set_next] in H.
  destruct (heap_set_A hargs (cred_post (s_facts st) (getr st X10) cred)) as [h1|] eqn:H1; [|discriminate].
  destruct (heap_add_window h1 (VP (s_next (clobber st1)) wzero) (getr st X10) (VL CtrLib.K_BLOCK)) as [h2|] eqn:H2; [|discriminate].
  destruct (heap_add_window h2 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X10)) (VL K_TWIN)) as [h3|] eqn:H3; [|discriminate].
  injection H as <-.
  exists r, hargs, cred, st1, h1, h2, h3, stN. repeat (split; [reflexivity || assumption|]).
  destruct (size_shape_ok (s_facts st) (f10 (s_rf st))) eqn:SSH; [left; split; [exact SSH| reflexivity]| right; split; [exact SSH| reflexivity]].
Qed.

Lemma aaligned_apply_shape : forall UNIV PCz st sts, aaligned_apply UNIV PCz st = Some sts ->
  exists r hargs cred st1 h1 h2 h3 stN,
    call_pre st = Some r /\ find_op HEAP_ID (s_ops st) = Some hargs /\ heap_A hargs = Some cred
    /\ forget_stack_below_sp_g st = Some st1
    /\ heap_set_A hargs (cred_post (s_facts st) (getr st X11) cred) = Some h1
    /\ heap_add_window h1 (VP (s_next (clobber st1)) wzero) (getr st X11) (VL CtrLib.K_BLOCK) = Some h2
    /\ heap_add_window h2 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X11)) (VL K_TWIN) = Some h3
    /\ null_post hargs cred (clobber st1) r = Some stN
    /\ sts = [stN; alloc_stB X11 st st1 r h3 cred].
Proof.
  intros UNIV PCz st sts H. unfold aaligned_apply in H.
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |] eqn:TP; try discriminate.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:FO; [|discriminate].
  destruct (getr st X10) as [al| | | | | | | | | |] eqn:X10E; try discriminate.
  destruct (heap_A hargs) as [cred|] eqn:HA; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  destruct (forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate].
  destruct (null_post hargs cred (clobber st1) r) as [stN|] eqn:NP; [|discriminate].
  unfold fresh in H. cbv zeta in H. cbn [fst snd s_next set_next] in H.
  destruct (heap_set_A hargs (cred_post (s_facts st) (getr st X11) cred)) as [h1|] eqn:H1; [|discriminate].
  destruct (heap_add_window h1 (VP (s_next (clobber st1)) wzero) (getr st X11) (VL CtrLib.K_BLOCK)) as [h2|] eqn:H2; [|discriminate].
  destruct (heap_add_window h2 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X11)) (VL K_TWIN)) as [h3|] eqn:H3; [|discriminate].
  injection H as <-.
  exists r, hargs, cred, st1, h1, h2, h3, stN. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Lemma add_window_facts : forall E md A nw rest n lo len kd,
  wt nw = false -> n = Z.to_nat (to_Z (wl nw)) -> (3 * n <= length rest)%nat -> to_Z (wl nw) + 1 < two63 ->
  let rest1 := firstn (3 * n) rest ++ [lo; len; kd] ++ skipn (3 * n) rest in
  let nw1 := wadd nw wone in
  heap_add_window (VL md :: A :: VL nw :: rest) lo len kd = Some (VL md :: A :: VL nw1 :: rest1)
  /\ wt nw1 = false /\ S n = Z.to_nat (to_Z (wl nw1)) /\ (3 * S n <= length rest1)%nat
  /\ wins_of E (S n) rest1 = wins_of E n rest ++ [Win (bv_unsigned (den E lo)) (bv_unsigned (den E len)) (bv_unsigned (den E kd))]
  /\ skipn (3 * S n) rest1 = skipn (3 * n) rest.
Proof.
  intros E md A nw rest n lo len kd T N L B. cbv zeta.
  destruct (wadd_one_small nw T B) as [T' E'].
  assert (HN : heap_nwin (VL md :: A :: VL nw :: rest) = Some n).
  { unfold heap_nwin. rewrite T, <- N. destruct (Nat.leb_spec (3 * n) (length rest)); [reflexivity| lia]. }
  split; [exact (heap_add_window_eq md A nw rest n lo len kd HN)|]. split; [exact T'|].
  split; [rewrite E', N; pose proof (Uint63.to_Z_bounded (wl nw)); lia|].
  split. { rewrite app_length, firstn_length_le by lia. cbn [length app]. rewrite skipn_length. lia. }
  split.
  - cbn [app]. rewrite (wins_of_app1 E n (firstn (3 * n) rest) lo len kd (skipn (3 * n) rest)); [| rewrite firstn_length_le; lia].
    rewrite <- (app_nil_r (firstn (3 * n) rest)) at 1. rewrite (wins_of_firstn E n rest []) by lia. reflexivity.
  - replace (3 * S n)%nat with (3 * n + 3)%nat by lia. rewrite skipn_app, firstn_length_le by lia.
    rewrite skipn_all2; [| rewrite firstn_length_le; lia]. replace (3 * n + 3 - 3 * n)%nat with 3%nat by lia. reflexivity.
Qed.

Lemma stB_shape_gen : forall (S : sstate) (k sh nx1 nx2 : int) (RGk RGs : region) (h : list sv) (f0 f1 f2 f3 : fact) (v : sv) (r : int),
  setpc (setr (addfact (addfact (addfact (addfact
          (set_ops (setregs (set_next (set_next S nx1) nx2) (IMap.add sh RGs (IMap.add k RGk (s_regs (set_next (set_next S nx1) nx2)))))
                   (set_op HEAP_ID h (s_ops (set_next (set_next S nx1) nx2))))
          f0) f1) f2) f3) X10 v) r
  = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (IMap.add sh RGs (IMap.add k RGk (s_regs S)))
       (f3 :: f2 :: f1 :: f0 :: s_facts S) (set_op HEAP_ID h (s_ops S)) (s_priv S) nx2.
Proof. intros. destruct S. reflexivity. Qed.
Lemma stBb_shape_gen : forall (S : sstate) (k sh s2 nx1 nx2 nx3 : int) (RGk RGs RGt : region) (h : list sv) (f0 f1 f2 f3 f4 f5 : fact) (v : sv) (r : int),
  setpc (setr (addfact (addfact (addfact (addfact (addfact (addfact
          (set_ops (setregs (set_next (set_next (set_next S nx1) nx2) nx3)
                            (IMap.add s2 RGt (IMap.add sh RGs (IMap.add k RGk (s_regs (set_next (set_next (set_next S nx1) nx2) nx3))))))
                   (set_op HEAP_ID h (s_ops (set_next (set_next (set_next S nx1) nx2) nx3))))
          f0) f1) f2) f3) f4) f5) X10 v) r
  = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (IMap.add s2 RGt (IMap.add sh RGs (IMap.add k RGk (s_regs S))))
       (f5 :: f4 :: f3 :: f2 :: f1 :: f0 :: s_facts S) (set_op HEAP_ID h (s_ops S)) (s_priv S) nx3.
Proof. intros. destruct S. reflexivity. Qed.

Section Post.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.

Hypothesis IMGSH_aci : forall v a, In v SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.TwinB.cov1 HEAP_ID args z.
Hypothesis Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds Cw md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.

Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.

Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.

Section POST.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok bsegs OPS E st ms mo.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Definition E' : env := env_above E (s_next st) Fv Gv.

Lemma EXT : env_ext (s_next st) E E'.
Proof. apply env_above_ext. Qed.

Lemma NX : st_vars_below (s_next st) st = true /\ 0 < to_Z (s_next st) /\ to_Z (s_next st) + 256 <= 2 ^ 62.
Proof. apply HeapCtr.TwinB.fresh_ok_inv. exact FOK. Qed.

Lemma SVB_parts :
  rf_allb (sv_vars_below (s_next st)) (s_rf st) = true /\ rf_allb (sv_vars_below (s_next st)) (s_ff st) = true
  /\ resv_vars_below (s_next st) (s_resv st) = true
  /\ IMap.forallb (fun k r => PrimInt63.ltb k (s_next st) && region_vars_below (s_next st) r) (s_regs st) = true
  /\ forallb (fact_vars_below (s_next st)) (s_facts st) = true
  /\ forallb (fun o => forallb (sv_vars_below (s_next st)) (op_args o)) (s_ops st) = true.
Proof.
  destruct NX as (SVB & _). unfold st_vars_below in SVB.
  apply andb_prop in SVB as [SVB H6]. apply andb_prop in SVB as [SVB H5]. apply andb_prop in SVB as [SVB H4'].
  apply andb_prop in SVB as [SVB H3]. apply andb_prop in SVB as [H1 H2]. repeat split; assumption.
Qed.

Lemma HS' : st_ok bsegs OPS E' st ms mo.
Proof. destruct NX as (SVB & POS & _). exact (st_ok_reval bsegs OPS (s_next st) E E' EXT st ms mo POS SVB HS). Qed.

Lemma den_E' : forall v, sv_vars_below (s_next st) v = true -> den E' v = den E v.
Proof. intros v Hv. exact (den_reval (s_next st) E E' EXT v Hv). Qed.

Lemma ev_E'_below : forall k, to_Z k < to_Z (s_next st) -> ev E' k = ev E k.
Proof. intros k Hk. unfold E'. apply ev_below. exact Hk. Qed.

Lemma ev_E'_fresh : forall i, (i <= 200)%nat -> ev E' (addn (s_next st) i) = Fv (Z.of_nat i).
Proof.
  intros i Hi. destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  assert (EA : to_Z (addn (s_next st) i) = to_Z (s_next st) + Z.of_nat i) by (apply addn_Z; rewrite wB_two63, two63_eq; lia).
  unfold E'. rewrite ev_above by (rewrite EA; lia). rewrite EA. f_equal. lia.
Qed.

Lemma reg_E' : forall k rg, IMap.find k (s_regs st) = Some rg ->
  ev E' k = ev E k /\ hiZ E' rg = hiZ E rg /\ PrimInt63.ltb k (s_next st) = true /\ region_vars_below (s_next st) rg = true.
Proof.
  intros k rg Hk. destruct SVB_parts as (_ & _ & _ & HR & _). exact (regs_reval_find (s_next st) E E' EXT _ k rg (so_bst _ _ _ _ _ _ HS) HR Hk).
Qed.

Variables (r : int) (st1 : sstate).
Hypothesis CP : call_pre st = Some r.
Hypothesis FS : forget_stack_below_sp_g st = Some st1.
Variables (R' : bvmap 5 word) (m' : amem) (mo' : Model).
Definition kept_regsA : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Hypothesis KEPT : forall rg, In rg kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg.
Hypothesis HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Definition ms' : machine_state := MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None m' (seg_rom bsegs).

Lemma st1_fields : s_pc st1 = s_pc st /\ s_rf st1 = s_rf st /\ s_ff st1 = s_ff st /\ s_resv st1 = s_resv st /\ s_facts st1 = s_facts st
  /\ s_ops st1 = s_ops st /\ s_priv st1 = s_priv st /\ s_next st1 = s_next st.
Proof.
  unfold forget_stack_below_sp_g in FS. destruct (sp_region st) as [[[k0 off0] r0]|]; [|discriminate].
  destruct (okey off0); [|discriminate]. injection FS as <-. repeat split; reflexivity.
Qed.

Lemma rget_core_getrA : forall R F pc fc rv x, rget (Core R F pc fc rv) (reg_of_r5 x) = AP.getr R (reg_of_r5 x).
Proof. intros. reflexivity. Qed.
Lemma reg_of_X0 : reg_of_r5 X0 = 0%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma getr_x0A : forall R, AP.getr R (reg_of_r5 X0) = Z_to_bv 64 0.
Proof. intros R. rewrite reg_of_X0. unfold AP.getr. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma kept_or_clobberedA : forall x, x <> X0 -> x <> X10 -> clob_pos x = None -> In (reg_of_r5 x) kept_regsA.
Proof.
  intros x N0 N10 H. destruct x; try discriminate H; try congruence;
  unfold kept_regsA; cbn [In];
  repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] | |- False => fail end.
Qed.

Lemma post_regs : forall v, den E' v = AP.getr R' 10%bv ->
  forall x, rget (Core R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None) (reg_of_r5 x)
            = den E' (rf_get (rf_set (s_rf (clobber st1)) X10 v) x).
Proof.
  intros v Hv x. rewrite rget_core_getrA. destruct st1_fields as (_ & RF1 & _ & _ & _ & _ & _ & NX1).
  destruct (r5_eqb x X10) eqn:Q10.
  { apply r5_eqb_spec in Q10. subst x. rewrite rf_get_set_same. symmetry. rewrite <- HeapCtr.TwinB.reg_of_X10 in Hv. exact Hv. }
  assert (N10 : x <> X10) by (intros ->; rewrite StepB.r5_eqb_refl in Q10; discriminate).
  rewrite rf_get_set_other by (intros Q; apply N10; symmetry; exact Q).
  change (rf_get (s_rf (clobber st1)) x) with (getr (clobber st1) x). rewrite getr_clobber, NX1.
  destruct (clob_pos x) as [i|] eqn:CPx.
  - rewrite <- (HF x i CPx). cbn [den]. rewrite ev_E'_fresh; [| destruct x; cbn in CPx; try discriminate; injection CPx as <-; lia].
    apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, w2Z_wzero, Z.add_0_r. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
  - destruct (r5_eqb x X0) eqn:Q0.
    + apply r5_eqb_spec in Q0. subst x. rewrite getr_x0A. unfold getr. rewrite RF1.
      rewrite (so_x0 _ _ _ _ _ _ HS'). rewrite den_VL. reflexivity.
    + assert (N0 : x <> X0) by (intros ->; rewrite StepB.r5_eqb_refl in Q0; discriminate).
      rewrite (KEPT _ (kept_or_clobberedA x N0 N10 CPx)).
      rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS x). unfold getr. rewrite RF1.
      symmetry. apply den_E'. destruct SVB_parts as (SVB & _). exact (rf_allb_get _ _ _ SVB x).
Qed.

Variables (aw : word) (LB : blocks) (L : alayout) (RNG RNG' : footprint) (sta sta' : astate) (LBa : list ablock) (p : aptr) (Ablk N : Z).

Variable WW : wit.
Hypothesis WOF : wit_of WW L RNG sta LBa.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis AH' : AHEAP AI L RNG' sta' (HB p Ablk N :: LBa) m'.
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis PRES : aheap_pres (aci AI) LBa sp (ms_mem ms) m'.
Hypothesis TWP : twins_pres LBa (ms_mem ms) m'.
Hypothesis PATN : ablock_shadow m' Ablk N.
Hypothesis MINV' : ALib.Mem.mem_inv bsegs m'.

Definition stableA (a : Z) : Prop := (sp <= a < 2 ^ 47) \/ in_ranges (aci AI) a \/ in_user LB a.

Lemma stable_byte : forall a, 0 <= a < 2 ^ 64 -> stableA a ->
  m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a) /\ rb bsegs m' a = rb bsegs (ms_mem ms) a
  /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true).
Proof.
  intros a Ha ST.
  assert (EQ : m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)).
  { destruct WOF as (E1 & E2 & E3 & E4). pose proof AR as [HWw EMw]. pose proof HWw as (_ & HT & _).
    destruct (LB_classify AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo HWw) as (KU & KT).
    apply (aw_real_stable AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo WW RNG' sta' (HB p Ablk N :: LBa) m' LBa LB sp LBa TWP ltac:(intros b Hb _ _; rewrite <- E4; exact Hb) AR).
    - rewrite E1. exact AH'.
    - exact PRES.
    - intros v Hv UB P. destruct (KU v Hv UB P) as (b & Vb & ->). exists b. split; [rewrite <- E4; exact (proj1 Vb)| reflexivity].
    - intros v Hv NUB. destruct (KT v Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
      + left. exists b. destruct (HT b Hb) as [HbL HH]. split; [exact HbL|]. split; [right; rewrite <- E4; exact HbL|]. split; [exact HH| reflexivity].
      + right. exists b. split; [exact (proj1 (proj1 Vb))|]. split; [rewrite <- E4; exact (proj1 (proj1 Vb))|]. split; [exact (proj2 Vb)| reflexivity].
    - exact Ha.
    - exact ST. }
  split; [exact EQ|]. split.
  - unfold rb. unfold ALib.Mem.wa in EQ. rewrite EQ. reflexivity.
  - intros W. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in W.
    rewrite (wview_ext1 m' (ms_mem ms) _ EQ). exact W.
Qed.

Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis Hksp : okey offs = Some ksp.
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Variables (wnl : list (int * sv * w64)) (n : nat) (rest : list sv).
Hypothesis NW : CtrA.nonstack_windows n rest = Some wnl.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis WF : windows_wf (wins_of E n rest) LB (ATOP + 4096).

Hypothesis WLOF : forall wlo, stack_wlo st = Some wlo -> ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo)).
Hypothesis FLOOR0 : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis LOSP0 : loZ rss <= keyZ ksp.

Lemma SP_den : bv_unsigned (den E (getr st X2)) = sp.
Proof. unfold sp. rewrite <- HeapCtr.TwinB.reg_of_X2, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X2). reflexivity. Qed.

Notation is_sliver k0 rg := (sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k0 rg).
Lemma old_stable : forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> k0 <> 0%uint63 -> k0 <> ks -> is_sliver k0 rg = false ->
  forall a, bv_unsigned (ev E k0) + loZ rg <= a < bv_unsigned (ev E k0) + hiZ E rg -> (sp <= a < 2 ^ 47) \/ in_user LB a \/ sh_cov a.
Proof.
  intros k0 rg Hk K0 KS NSL a Ha. pose proof atop_range as ATR.
  assert (INWIN : forall k1 len kd, CtrA.win_lookup wnl k1 = Some (len, kd) ->
            bv_unsigned (ev E k1) <= a < bv_unsigned (ev E k1) + bv_unsigned (den E len) -> in_user LB a).
  { intros k1 len kd WL Hin.
    destruct (HeapCtrB.TwinB.nonstack_windows_In E n rest wnl k1 len kd NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
    pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
    + exfalso. exact (KD KS0).
    + apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
    + apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }
  destruct (CallA.TwinB.aregion_just_sound bsegs OPS E st ms mo wnl ks offs rss k0 rg HS SPR AJ Hk K0) as [[EQK _]|(_ & [(len & kd & WL & LZ & HZ)|[(ABOVE & TOP)|[VJ|SL]]])];
    [| | | | congruence].
  - contradiction.
  - right. left. rewrite LZ in Ha. apply (INWIN k0 len kd WL). lia.
  - left. rewrite SP_den in ABOVE. lia.
  - destruct (CallV.TwinB.view_just_sound bsegs OPS E st ms mo wnl ks offs rss k0 rg HS SPR Hk K0 VJ) as [(_ & blo & bhi & SHA & TOP & FLR)|[(hs0 & n0 & sh' & len & ZV & BT & VPAR & WL & LO & HI)|[(_ & v & Hv & LO & HI)|(sh' & kbt & nt & len & WL & _ & _ & _ & _ & _ & LO & HI)]]].
    + right. right. left. destruct (SHA a Ha) as (a' & Ha' & ->). exists a'.
      assert (FL : ATOP + 4096 <= blo).
      { destruct FLR as [(wlo & SW & ->)|[(rs0 & Frs & ->)|GE]].
        - exact (WLOF wlo SW).
        - destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). rewrite Hrs in Frs. injection Frs as <-. exact FLOOR0.
        - rewrite SP_den in GE. rewrite SPE in GE. lia. }
      split; [lia|]. unfold CallV.TwinB.shz, shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
    + right. left. apply (INWIN sh' len K_TWIN WL). lia.
    + right. right. right. exists v. split; [exact (IMGSH_SHLIT v Hv)| lia].
    + right. left. apply (INWIN sh' len K_TWIN WL). lia.
Qed.

Lemma sh_cov_pres : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a).
Proof.
  intros a Ha [(a' & R & ->)|(v & Hv & R)].
  - exact (proj1 (PRES (shad a') Ha ltac:(right; right; right; exists a'; split; [left; exact R| reflexivity]))).
  - destruct (IMGSH_aci v a Hv R) as (a' & INA & ->).
    exact (proj1 (PRES (shad a') Ha ltac:(right; right; right; exists a'; split; [right; left; exact INA| reflexivity]))).
Qed.

Hypothesis STKlo' : stk bsegs m' (CtrPre.TwinB.sp_lo E st) sp.
Lemma SP_bottom : CtrPre.TwinB.sp_lo E st <= bv_unsigned (ev E ks) + loZ rss <= sp.
Proof. split; [exact (CtrPre.TwinB.sp_lo_le OPS E st ms mo ks offs rss HS SPR)| rewrite SPE; lia]. Qed.

Lemma old_region_ok : forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> k0 <> 0%uint63 -> k0 <> ks ->
  region_ok bsegs (s_priv st) E' m' k0 rg.
Proof.
  intros k0 rg Hk K0 KS. pose proof (so_reg _ _ _ _ _ _ HS' k0 rg Hk) as RO. destruct (reg_E' k0 rg Hk) as (Ek & Eh & _).
  assert (KZ : PrimInt63.eqb k0 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  destruct (is_sliver k0 rg) eqn:SL.
  {
    exact (CtrPre.TwinB.sliver_region_ok OPS E E' st ms mo m' ks offs rss k0 rg sp HS SPR Hk K0 KS SL Ek Eh (proj2 SP_bottom) STKlo'). }
  apply (MemP.region_ok_frame bsegs (s_priv st) E' (ms_mem ms) m' k0 rg (so_zero _ _ _ _ _ _ HS') RO).
  intros a Ha R _. rewrite Ek, Eh in R.
  destruct (old_stable k0 rg Hk K0 KS SL a (R KZ)) as [X|[X|X]].
  - destruct (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(left; exact X)) as (E1 & _). unfold ALib.Mem.wa in E1. exact E1.
  - destruct (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; right; exact X)) as (E1 & _). unfold ALib.Mem.wa in E1. exact E1.
  - pose proof (sh_cov_pres a ltac:(unfold two64 in Ha; lia) X) as E1. unfold ALib.Mem.wa in E1. exact E1.
Qed.

Hypothesis K16 : keyZ ksp mod 16 = 0.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Lemma STK' : stk bsegs m' (bv_unsigned (ev E ks) + loZ rss) sp.
Proof. exact (CtrPre.TwinB.stk_sp_region E st m' ks offs rss sp SPR SP_bottom STKlo'). Qed.
Definition forget_rs : region := region_forget_below rss ksp.

Lemma st1_regs : s_regs st1 = IMap.add ks forget_rs (s_regs st).
Proof.
  unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. reflexivity.
Qed.

Lemma rs_top : bv_unsigned (ev E ks) + hiZ E rss <= 2 ^ 47.
Proof.
  destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (HX2 & Hrs & KZ & HW & HBG).
  assert (K0 : ks <> 0%uint63) by (apply Uint63.eqb_false_spec; exact KZ).
  destruct (CallA.TwinB.aregion_just_sound bsegs OPS E st ms mo wnl ks offs rss ks rss HS SPR AJ Hrs K0) as [[_ TOP]|[NE _]]; [exact TOP| contradiction].
Qed.

Lemma rs_ok : region_ok bsegs (s_priv st) E' m' ks forget_rs.
Proof.
  destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (HX2 & Hrs & KZ & HW & HBG).
  pose proof (so_reg _ _ _ _ _ _ HS' ks rss Hrs) as RO. destruct (reg_E' ks rss Hrs) as (Ek & Eh & _). pose proof rs_top as TOP.
  destruct (ro_range _ _ _ _ _ _ RO KZ) as [RLO RHI]. rewrite Ek in RLO. rewrite Ek, Eh in RHI.
  apply (CallA.TwinB.region_forget_below_ok bsegs (s_priv st) E' (ms_mem ms) m' ks rss ksp (so_zero _ _ _ _ _ _ HS') RO KZ HBG K16).
  - intros a Ha. rewrite Ek, Eh in Ha.
    destruct (stable_byte a ltac:(unfold two64 in *; lia) ltac:(left; rewrite SPE; lia)) as (_ & E2 & W2). split; assumption.
  - intros a Ha. rewrite Ek in Ha. destruct STK' as (_ & _ & ST). destruct (ST a ltac:(rewrite SPE; lia)) as [W [b Hb]].
    split; [rewrite (GlueA.TwinB.rb_mrdA bsegs), Hb; discriminate|]. apply (GlueA.TwinB.wb_wviewA bsegs). exact W.
Qed.

Variable aw' : word.
Hypothesis AC' : ACCT aw' L RNG' sta' (HB p Ablk N :: LBa) mo'.
Definition LB' : blocks := (shad Ablk, shlen (N + 7)) :: (Ablk, N) :: LB.

Lemma NEWB : 1 <= N <= AREQMAX /\ ablock_range Ablk N /\ ALib.Mem.wr_at bsegs m' Ablk N.
Proof.
  destruct (heap_block_facts AI L RNG' sta' _ m' (HB p Ablk N) AH' ltac:(left; reflexivity) ltac:(exists p; reflexivity)) as (A1 & A2 & A3).
  cbn [ab_addr ab_size] in *. auto.
Qed.

Definition Wm : wit := mkWit (w_L WW) RNG' sta' (HB p Ablk N :: w_LBa WW) (HB p Ablk N :: w_T WW) (w_FA WW) m' (w_zc WW).

Lemma WORLD' : aw_holds_w AI ACCT UNIV Wm aw' LB' m' mo'
  /\ (forall g, 0 <= g -> 8 * g < N -> m' (ALib.Mem.wa (shad Ablk + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? N then 0 else N - 8 * g)))
  /\ user_band Ablk /\ (forall a, in_iv (Ablk, N) a -> ~ in_user LB a) /\ ~ In (shad Ablk, shlen (N + 7)) ((Ablk, N) :: LB)
  /\ (forall a, in_iv (shad Ablk, shlen (N + 7)) a -> ~ in_user LB a).
Proof.
  destruct WOF as (E1 & E2 & E3 & E4).
  destruct (aw_real_malloc AI ACCT UNIV AI_fake aw aw' LB (ms_mem ms) mo WW RNG' sta' p Ablk N m' mo' sp AR
              ltac:(rewrite E1, E4; exact AH') ltac:(rewrite E1, E4; exact AC') ltac:(rewrite E4; exact PRES) ltac:(rewrite E4; exact TWP) PATN) as (AR' & VB & NT & UB & DJ & DJT).
  destruct AR' as [HW1 _].
  destruct (twin_out_w AI ACCT UNIV AI_fake _ aw' _ m' mo' (HB p Ablk N) HW1 VB ltac:(exists p; reflexivity) NT) as (AWH' & NIN & PAT).
  split; [exact AWH'|]. split; [exact PAT|]. split; [exact UB|]. split; [exact DJ|]. split; [exact NIN| exact DJT].
Qed.
Lemma WORLD'_asan : aw_holds_asan AI ACCT UNIV aw' LB' m' mo'.
Proof. exists Wm. exact (proj1 WORLD'). Qed.

Definition kB : int := addn (s_next st) 15.
Definition kS : int := addn (s_next st) 16.
Variable XN : r5.
Definition nsv : sv := getr st XN.
Hypothesis NDEN : bv_unsigned (den E nsv) = N.
Hypothesis F15 : Fv 15 = Z_to_bv 64 Ablk.
Hypothesis F16 : Fv 16 = Z_to_bv 64 (shad Ablk).
Hypothesis GJ : forall o, 0 <= o < N -> rb bsegs m' (Ablk + o) = Some (Gv 15 o).

Variable TWR : region.
Hypothesis TWSH : (TWR = twin_region nsv /\ match nsv with VL _ => True | _ => N mod 8 = 0 end) \/ TWR = twin_main nsv.

Lemma nsv_below : sv_vars_below (s_next st) nsv = true.
Proof. destruct SVB_parts as (SVB & _). exact (rf_allb_get _ _ _ SVB XN). Qed.

Lemma kB_Z : to_Z kB = to_Z (s_next st) + 15.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold kB. rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma kS_Z : to_Z kS = to_Z (s_next st) + 16.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold kS. rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma ev_kB : bv_unsigned (ev E' kB) = Ablk.
Proof.
  unfold kB. rewrite ev_E'_fresh by lia. change (Z.of_nat 15) with 15. rewrite F15. destruct NEWB as (N1 & (BK & _ & TOP & _) & _).
  pose proof atop_range. unfold ablk, AIMG_HI, KLS in BK. apply Z_to_bv_small. unfold bv_modulus, two64. lia.
Qed.
Lemma ev_kS : bv_unsigned (ev E' kS) = shad Ablk.
Proof.
  unfold kS. rewrite ev_E'_fresh by lia. change (Z.of_nat 16) with 16. rewrite F16. destruct NEWB as (N1 & BR & _).
  destruct (twin_band _ _ BR N1) as (T1 & T2 & T3 & _). apply Z_to_bv_small. unfold bv_modulus, two64. lia.
Qed.
Lemma kB_nz : PrimInt63.eqb kB 0%uint63 = false.
Proof. apply Uint63.eqb_false_spec. intros X. pose proof kB_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia. Qed.
Lemma kS_nz : PrimInt63.eqb kS 0%uint63 = false.
Proof. apply Uint63.eqb_false_spec. intros X. pose proof kS_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia. Qed.

Definition blk_region : region := Region 0%uint63 nsv true BGUnk IMap.empty.

Lemma blk_region_ok : region_ok bsegs (s_priv st) E' m' kB blk_region.
Proof.
  destruct NEWB as (N1 & BR & WR). pose proof WORLD'_asan as AWH'.
  assert (EH : hiZ E' blk_region = N) by (unfold hiZ, blk_region; cbn [rg_hi]; rewrite (den_E' nsv nsv_below); exact NDEN).
  assert (EL : loZ blk_region = 0) by reflexivity.
  destruct BR as (BK & _ & TOP & _). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  constructor; rewrite ?ev_kB, ?EH, ?EL.
  - apply IMap.bst_empty.
  - intros _. unfold two64. lia.
  - intros _ a Ha.
    destruct (aw_user_ok_asan AI ACCT UNIV AI_fake aw' LB' m' mo' (Ablk, N) a AWH' ltac:(right; left; reflexivity) ltac:(unfold in_iv; cbn [fst snd]; lia)) as [MP SEG].
    split; [| split; [| exact SEG]].
    + unfold rb. destruct (m' (Z_to_bv 64 a)); [discriminate| contradiction].
    + intros _. apply (GlueA.TwinB.wb_wviewA bsegs). destruct WR as (_ & _ & W). replace a with (Ablk + (a - Ablk)) by lia. apply W. lia.
  - intros g gr Hg. cbn [blk_region rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
  - intros g gr c i Hg. cbn [blk_region rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
  - intros o H1 _ _. specialize (H1 kB_nz). unfold bg_byte. cbn [blk_region rg_bg]. unfold E'. rewrite eg_above by (rewrite kB_Z; lia).
    rewrite kB_Z. replace (to_Z (s_next st) + 15 - to_Z (s_next st)) with 15 by lia. apply GJ. lia.
Qed.

Lemma twin_region_okA : region_ok bsegs (s_priv st) E' m' kS TWR.
Proof.
  destruct NEWB as (N1 & BR & WR). destruct WORLD' as (_ & PAT & _). pose proof WORLD'_asan as AWH'. destruct (twin_band _ _ BR N1) as (T1 & T2 & T3 & _).
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (den_E' nsv nsv_below); exact NDEN).
  destruct TWSH as [[-> SHAPE]| ->].
  2:{
      apply (CallA.TwinB.twin_main_ok bsegs (s_priv st) E' m' kS nsv kS_nz); rewrite ?DN, ?ev_kS.
      - clear - N1. lia.
      - unfold shlen in T2. rewrite Z.shiftr_div_pow2 in T2 by lia. change (2 ^ 3) with 8 in T2. unfold two64. clear - T1 T2 N1. Z.div_mod_to_equations. lia.
      - intros g G. assert (G0 : 0 <= g) by lia. assert (G1 : 8 * g < N) by (clear - G; Z.div_mod_to_equations; lia). split.
        + pose proof (PAT g G0 G1) as P1. unfold rb. unfold ALib.Mem.wa in P1. rewrite P1.
          replace (8 * g + 8 <=? N) with true by (symmetry; apply Z.leb_le; clear - G; Z.div_mod_to_equations; lia). reflexivity.
        + apply (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw' LB' m' mo' _ (shad Ablk + g) AWH' ltac:(left; reflexivity)
                         ltac:(unfold in_iv; cbn [fst snd]; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - G; Z.div_mod_to_equations; lia))). }
  apply (CallA.TwinB.twin_region_ok bsegs (s_priv st) E' m' kS nsv kS_nz); rewrite ?DN, ?ev_kS.
  - lia.
  - unfold AREQMAX in N1. lia.
  - assert (X : match nsv with VL _ => True | _ => bv_unsigned (den E' nsv) mod 8 = 0 end) by (destruct nsv; try exact I; rewrite DN; exact SHAPE). rewrite DN in X. exact X.
  - unfold shlen in T2. rewrite Z.shiftr_div_pow2 in T2 by lia. change (2 ^ 3) with 8 in T2. unfold two64. lia.
  - intros g G0 G1. split.
    + pose proof (PAT g G0 G1) as P1. unfold rb. unfold ALib.Mem.wa in P1. rewrite P1. reflexivity.
    + apply (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw' LB' m' mo' _ (shad Ablk + g) AWH' ltac:(left; reflexivity)
                     ltac:(unfold in_iv; cbn [fst snd]; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - G0 G1; Z.div_mod_to_equations; lia))).
Qed.

Lemma TWR_geo : loZ TWR = 0 /\ 0 <= hiZ E' TWR <= (N + 7) / 8 /\ rg_w TWR = false.
Proof.
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (den_E' nsv nsv_below); exact NDEN).
  destruct NEWB as (NN & _). unfold AREQMAX in NN.
  destruct TWSH as [[-> _]| ->].
  - destruct (CallA.TwinB.twin_region_fields nsv) as (LO & WR & _). split; [unfold loZ; rewrite LO; reflexivity|]. split; [| exact WR].
    unfold hiZ. rewrite CallA.TwinB.twin_region_hi, (CallA.TwinB.twin_len_den E' nsv) by (rewrite DN; lia). rewrite DN. clear - NN. split; [Z.div_mod_to_equations; lia| lia].
  - split; [reflexivity|]. split; [| reflexivity]. unfold hiZ, twin_main. cbn [rg_hi]. rewrite CallA.TwinB.sz_last_den by (rewrite DN; clear - NN; lia). rewrite DN. clear - NN. Z.div_mod_to_equations. lia.
Qed.
Definition RgP : IMap.t region := IMap.add kS TWR (IMap.add kB blk_region (IMap.add ks forget_rs (s_regs st))).

Lemma old_key_lt : forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> to_Z k0 < to_Z (s_next st).
Proof. intros k0 rg H. destruct (reg_E' k0 rg H) as (_ & _ & LT & _). apply Uint63.ltb_spec in LT. exact LT. Qed.

Lemma RgP_bst : IMap.bst RgP.
Proof. unfold RgP. repeat apply IMap.bst_add. exact (so_bst _ _ _ _ _ _ HS). Qed.

Lemma RgP_find : forall k0 rg, IMap.find k0 RgP = Some rg ->
  (k0 = kS /\ rg = TWR) \/ (k0 = kB /\ rg = blk_region) \/ (k0 = ks /\ rg = forget_rs)
  \/ (k0 <> kS /\ k0 <> kB /\ k0 <> ks /\ IMap.find k0 (s_regs st) = Some rg).
Proof.
  intros k0 rg H. unfold RgP in H. pose proof (so_bst _ _ _ _ _ _ HS) as B0.
  destruct (Uint63.eqb kS k0) eqn:Q1.
  { apply Uint63.eqb_correct in Q1. subst k0. rewrite IMap.find_add_same in H by (repeat apply IMap.bst_add; exact B0). injection H as <-. left. auto. }
  rewrite IMap.find_add_other_eqb in H by (repeat apply IMap.bst_add; exact B0 || exact Q1).
  destruct (Uint63.eqb kB k0) eqn:Q2.
  { apply Uint63.eqb_correct in Q2. subst k0. rewrite IMap.find_add_same in H by (repeat apply IMap.bst_add; exact B0). injection H as <-. right; left. auto. }
  rewrite IMap.find_add_other_eqb in H by (repeat apply IMap.bst_add; exact B0 || exact Q2).
  destruct (Uint63.eqb ks k0) eqn:Q3.
  { apply Uint63.eqb_correct in Q3. subst k0. rewrite IMap.find_add_same in H by exact B0. injection H as <-. right; right; left. auto. }
  rewrite IMap.find_add_other_eqb in H by (exact B0 || exact Q3).
  right; right; right. apply Uint63.eqb_false_spec in Q1, Q2, Q3. repeat split; auto.
Qed.

Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.

Lemma rs_fields : loZ forget_rs = loZ rss /\ (forall E0, hiZ E0 forget_rs = hiZ E0 rss) /\ rg_w forget_rs = rg_w rss.
Proof. repeat split; reflexivity. Qed.

Lemma RgP_range : forall k0 rg a, IMap.find k0 RgP = Some rg -> PrimInt63.eqb k0 0%uint63 = false ->
  bv_unsigned (ev E' k0) + loZ rg <= a < bv_unsigned (ev E' k0) + hiZ E' rg ->
  (k0 = kS /\ in_iv (shad Ablk, shlen (N + 7)) a) \/ (k0 = kB /\ in_iv (Ablk, N) a)
  \/ (k0 = ks /\ ATOP + 4096 <= a < 2 ^ 47) \/ (k0 <> kS /\ k0 <> kB /\ k0 <> ks /\ ((ATOP + 4096 <= a < 2 ^ 47) \/ in_user LB a \/ sh_cov a)).
Proof.
  intros k0 rg a H KZ Ha. destruct (RgP_find k0 rg H) as [[-> ->]|[[-> ->]|[[-> ->]|(N1 & N2 & N3 & F)]]].
  - left. split; [reflexivity|]. rewrite ev_kS in Ha. destruct TWR_geo as (L0 & H0 & _). rewrite L0 in Ha.
    unfold in_iv, shlen. cbn [fst snd]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
  - right; left. split; [reflexivity|]. rewrite ev_kB in Ha. unfold hiZ, loZ, blk_region in Ha. cbn [rg_hi rg_lo] in Ha.
    rewrite (den_E' nsv nsv_below), NDEN in Ha. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0 in Ha. unfold in_iv. cbn [fst snd]. lia.
  - right; right; left. split; [reflexivity|]. destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _).
    destruct (reg_E' ks rss Hrs) as (Ek & Eh & _). destruct rs_fields as (L1 & H1 & _). rewrite L1, (H1 E'), Ek, Eh in Ha. pose proof rs_top. lia.
  - right; right; right. repeat (split; [assumption|]). destruct (reg_E' k0 rg F) as (Ek & Eh & _). rewrite Ek, Eh in Ha.
    assert (K0' : k0 <> 0%uint63) by (intros ->; discriminate KZ).
    destruct (is_sliver k0 rg) eqn:SL.
    + left. destruct (CtrPre.TwinB.sp_lo_of_sliver OPS E st ms mo ks offs rss k0 rg HS SPR F K0' N3 SL) as (_ & L0 & EH & _ & _ & wlo & SW & EKW).
      pose proof (WLOF wlo SW) as CE. pose proof rs_top as RT. pose proof (CallA.TwinB.sliver_neg st ks offs rss k0 rg SPR SL) as NEG.
      pose proof (bv_unsigned_in_range 64 (den E (rg_hi rss))) as RH. fold (hiZ E rss) in RH. rewrite L0 in Ha. lia.
    + destruct (old_stable k0 rg F K0' N3 SL a Ha) as [X|[X|X]]; [left; pose proof SPE; lia| right; left; exact X| right; right; exact X].
Qed.

Lemma sp_floor : ATOP + 4096 <= sp.
Proof. rewrite SPE. lia. Qed.

Lemma RgP_old : forall k0 rg, IMap.find k0 RgP = Some rg -> k0 <> kS -> k0 <> kB ->
  exists rg0, IMap.find k0 (s_regs st) = Some rg0 /\ loZ rg = loZ rg0 /\ (forall E0, hiZ E0 rg = hiZ E0 rg0) /\ rg_w rg = rg_w rg0.
Proof.
  intros k0 rg H N1 N2. destruct (RgP_find k0 rg H) as [[-> _]|[[-> _]|[[-> ->]|(_ & _ & _ & F)]]]; try contradiction.
  - destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). exists rss. split; [exact Hrs|]. repeat split; reflexivity.
  - exists rg. auto.
Qed.

Lemma RgP_disjoint : regions_disjoint E' RgP.
Proof.
  intros k1 rg1 k2 rg2 H1 H2 NE Z1 Z2 WR a [A1 A2].
  destruct NEWB as (NN & BR & _). destruct (twin_band _ _ BR NN) as (T1 & T2 & T3 & _). destruct WORLD' as (_ & _ & UB & DJ & _ & DJT).
  pose proof atop_range as ATR. pose proof sp_floor as SPF. destruct BR as (BK & _ & TOP & _). unfold ablk, AIMG_HI, KLS in BK.
  pose proof (RgP_range k1 rg1 a H1 Z1 A1) as C1. pose proof (RgP_range k2 rg2 a H2 Z2 A2) as C2.
  assert (TW_B : in_iv (shad Ablk, shlen (N + 7)) a -> in_iv (Ablk, N) a -> False) by (unfold in_iv; cbn [fst snd]; unfold user_band in UB; lia).
  assert (TW_S : in_iv (shad Ablk, shlen (N + 7)) a -> ATOP + 4096 <= a -> False) by (unfold in_iv; cbn [fst snd]; lia).
  assert (B_S : in_iv (Ablk, N) a -> ATOP + 4096 <= a -> False) by (unfold in_iv; cbn [fst snd]; lia).

  assert (SHB : sh_cov a -> (0x7fffa000 <= a < 0x800be0e0) \/ (shad ATOP <= a < 0x10007fff8000)) by exact (sh_cov_band a).
  destruct (shadow_tight Ablk N ltac:(unfold ablk, AIMG_HI, KLS; exact BK) TOP ltac:(lia)) as [TT1 TT2].
  assert (TW_C : in_iv (shad Ablk, shlen (N + 7)) a -> sh_cov a -> False) by (intros X Y; apply SHB in Y; unfold in_iv in X; cbn [fst snd] in X; lia).
  assert (B_C : in_iv (Ablk, N) a -> sh_cov a -> False).
  { intros X Y. apply SHB in Y. unfold in_iv in X. cbn [fst snd] in X.
    assert (SHA : 0x7fff8000 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia). lia. }

  destruct C1 as [[E1 I1]|[[E1 I1]|C1]]; destruct C2 as [[E2 I2]|[[E2 I2]|C2]]; subst; try contradiction; try (exfalso; eauto; fail).
  - destruct C2 as [[_ I2]|(_ & _ & _ & [I2|[I2|I2]])]; [exact (TW_S I1 (proj1 I2))| exact (TW_S I1 ltac:(lia))| exact (DJT a I1 I2)| exact (TW_C I1 I2)].
  - destruct C2 as [[_ I2]|(_ & _ & _ & [I2|[I2|I2]])]; [exact (B_S I1 (proj1 I2))| exact (B_S I1 ltac:(lia))| exact (DJ a I1 I2)| exact (B_C I1 I2)].
  - destruct C1 as [[_ I1]|(_ & _ & _ & [I1|[I1|I1]])]; [exact (TW_S I2 (proj1 I1))| exact (TW_S I2 ltac:(lia))| exact (DJT a I2 I1)| exact (TW_C I2 I1)].
  - destruct C1 as [[_ I1]|(_ & _ & _ & [I1|[I1|I1]])]; [exact (B_S I2 (proj1 I1))| exact (B_S I2 ltac:(lia))| exact (DJ a I2 I1)| exact (B_C I2 I1)].
  -
    assert (N1S : k1 <> kS) by (destruct C1 as [[-> _]|(X & _)]; [| exact X]; intros X; pose proof kS_Z; destruct (CallA.TwinB.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite X in *; lia).
    assert (N1B : k1 <> kB) by (destruct C1 as [[-> _]|(_ & X & _)]; [| exact X]; intros X; pose proof kB_Z; destruct (CallA.TwinB.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite X in *; lia).
    assert (N2S : k2 <> kS) by (destruct C2 as [[-> _]|(X & _)]; [| exact X]; intros X; pose proof kS_Z; destruct (CallA.TwinB.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite X in *; lia).
    assert (N2B : k2 <> kB) by (destruct C2 as [[-> _]|(_ & X & _)]; [| exact X]; intros X; pose proof kB_Z; destruct (CallA.TwinB.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite X in *; lia).
    destruct (RgP_old k1 rg1 H1 N1S N1B) as (q1 & F1 & L1 & HH1 & W1). destruct (RgP_old k2 rg2 H2 N2S N2B) as (q2 & F2 & L2 & HH2 & W2).
    rewrite L1, (HH1 E') in A1. rewrite L2, (HH2 E') in A2. rewrite W1, W2 in WR.
    exact (so_disj _ _ _ _ _ _ HS' k1 q1 k2 q2 F1 F2 NE Z1 Z2 WR a (conj A1 A2)).
Qed.

Lemma RgP_in_based : forall a, in_based E' RgP a ->
  in_iv (shad Ablk, shlen (N + 7)) a \/ in_iv (Ablk, N) a \/ in_based E' (s_regs st) a.
Proof.
  intros a (k0 & rg & H & KZ & R).
  destruct (Uint63.eqb k0 kS) eqn:QS; [apply Uint63.eqb_correct in QS; subst k0|].
  { destruct (RgP_range kS rg a H KZ R) as [[_ I]|[[X _]|[[X _]|(X & _)]]]; [left; exact I| | |];
      exfalso; [pose proof kS_Z; pose proof kB_Z; rewrite X in *; lia | pose proof kS_Z; destruct (CallA.TwinB.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite <- X in *; lia | congruence]. }
  destruct (Uint63.eqb k0 kB) eqn:QB; [apply Uint63.eqb_correct in QB; subst k0|].
  { destruct (RgP_range kB rg a H KZ R) as [[X _]|[[_ I]|[[X _]|(_ & X & _)]]]; [| right; left; exact I | |];
      exfalso; [pose proof kS_Z; pose proof kB_Z; rewrite X in *; lia | pose proof kB_Z; destruct (CallA.TwinB.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite <- X in *; lia | congruence]. }
  apply Uint63.eqb_false_spec in QS, QB. destruct (RgP_old k0 rg H QS QB) as (q & F & L1 & HH1 & _).
  right; right. exists k0, q. rewrite <- L1, <- (HH1 E'). auto.
Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : n = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * n <= length rest)%nat.
Hypothesis AWden : aw = den E A.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * n) rest)) LB (wins_of E n rest) (ms_mem ms).
Hypothesis TI : ties WW (wins_of E n rest).
Hypothesis PRS : In prist_win (wins_of E n rest) -> aprist sta'.

Lemma DEC : decode (map (den E) hargs) = Some (w2Z md, den E A, wins_of E n rest, map (den E) (skipn (3 * n) rest)).
Proof. rewrite Eh. exact (decode_hargs E md A nw rest n Tnw Nn Ln). Qed.

Lemma AWH : aw_holds_asan AI ACCT UNIV aw LB (ms_mem ms) mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.

Lemma win_off_image : forall a, in_ws (wins_of E n rest) a -> find_segment bsegs a 1 = None.
Proof.
  intros a X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
  pose proof atop_range as ATR.
  pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SUBb)]]]).
  - apply ref_find_segment_none; [lia|]. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. lia.
  - exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ a AWH B Hin)).
  - exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo b a AWH Hb (SUBb a Hin))).
Qed.

Lemma pub_image_client : forall a seg, 0 <= a < two64 -> find_segment bsegs a 1 = Some seg -> ~ in_priv (s_priv st) a -> in_ranges (aci AI) a.
Proof.
  intros a seg Ha SEG NP.
  destruct (in_ivs_b IMGX a) eqn:IX.
  - apply in_ivs_b_spec in IX. apply in_ivs_In in IX as (v & Hv & Hin). unfold in_iv in Hin.
    destruct (IMGX_aci v Hv) as (N0 & [(rg & Hr & R1 & R2)|[(rg & Hr & R1 & R2)|(S1 & S2)]]).
    + exists rg. split; [exact Hr|]. lia.
    +   exfalso. pose proof (AI_aci_lo AI rg Hr) as LO.
      rewrite (ref_find_segment_none a 1 ltac:(lia) ltac:(right; unfold ASHOFF in *; lia)) in SEG. discriminate.
    + exfalso. pose proof atop_range as ATR0.
      rewrite (ref_find_segment_none a 1 ltac:(lia) ltac:(right; unfold ASHOFF in *; lia)) in SEG. discriminate.
  - exfalso. assert (NIX : ~ in_ivs IMGX a) by (rewrite <- in_ivs_b_spec; congruence).
    assert (NW0 : ~ in_ws (wins_of E n rest) a) by (intros X; rewrite (win_off_image a X) in SEG; discriminate).
    destruct (ops_apart_find bsegs OPS E (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a (so_apart _ _ _ _ _ _ HS) Hf) as [_ IP].
    { rewrite OPS_fp1. apply (proj2 (fp_spec IMGX _ _ _ _ _ a DEC)). auto. }
    apply NP. apply IP. exists seg. exact SEG.
Qed.

Lemma r0_ok : forall r0, IMap.find 0%uint63 (s_regs st) = Some r0 -> region_ok bsegs (s_priv st) E' m' 0%uint63 r0.
Proof.
  intros r0 H0. pose proof (so_reg _ _ _ _ _ _ HS' _ _ H0) as RO.
  apply (MemP.region_ok_frame bsegs (s_priv st) E' (ms_mem ms) m' _ r0 (so_zero _ _ _ _ _ _ HS') RO).
  intros a Ha _ R. destruct (R eq_refl) as [[seg SEG] NP].
  destruct (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact (pub_image_client a seg Ha SEG NP))) as (E1 & _).
  unfold ALib.Mem.wa in E1. exact E1.
Qed.

Lemma ks_nz : ks <> 0%uint63.
Proof. destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & _ & KZ & _). apply Uint63.eqb_false_spec. exact KZ. Qed.

Lemma all_regions_ok : forall k0 rg, IMap.find k0 RgP = Some rg -> region_ok bsegs (s_priv st) E' m' k0 rg.
Proof.
  intros k0 rg H. destruct (RgP_find k0 rg H) as [[-> ->]|[[-> ->]|[[-> ->]|(N1 & N2 & N3 & F)]]].
  - exact twin_region_okA.
  - exact blk_region_ok.
  - exact rs_ok.
  - destruct (Uint63.eqb k0 0%uint63) eqn:Q0.
    + apply Uint63.eqb_correct in Q0. subst k0. exact (r0_ok rg F).
    + apply Uint63.eqb_false_spec in Q0. exact (old_region_ok k0 rg F Q0 N3).
Qed.

Lemma RgP_pub : abs_cells_public (s_priv st) RgP.
Proof.
  intros r0 g gr c H0 Hg Hcc i Hi.
  destruct (RgP_find _ _ H0) as [[X _]|[[X _]|[[X _]|(_ & _ & _ & F)]]].
  - exfalso. pose proof kS_Z as KZ. rewrite <- X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia.
  - exfalso. pose proof kB_Z as KZ. rewrite <- X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia.
  - exfalso. exact (ks_nz (eq_sym X)).
  - exact (so_pub _ _ _ _ _ _ HS r0 g gr c F Hg Hcc i Hi).
Qed.

Hypothesis N255 : (n <= 255)%nat.
Variable pd : bool.
Definition cred' : sv := if pd then A else sv_alu ALU_SUB A nsv.
Definition CHG : Z := if pd then 0 else N.
Definition restB : list sv := firstn (3 * n) rest ++ [VP kB wzero; nsv; VL CtrLib.K_BLOCK] ++ skipn (3 * n) rest.
Definition nwB : w64 := wadd nw wone.
Definition restT : list sv := firstn (3 * S n) restB ++ [VP kS wzero; twin_len nsv; VL K_TWIN] ++ skipn (3 * S n) restB.
Definition nwT : w64 := wadd nwB wone.
Definition h3 : list sv := VL md :: cred' :: VL nwT :: restT.

Lemma nw_small : to_Z (wl nw) + 2 < two63.
Proof. pose proof (Uint63.to_Z_bounded (wl nw)) as B. unfold two63. rewrite Nn in N255. lia. Qed.

Lemma h3_shape :
  heap_set_A hargs cred' = Some (VL md :: cred' :: VL nw :: rest)
  /\ heap_add_window (VL md :: cred' :: VL nw :: rest) (VP kB wzero) nsv (VL CtrLib.K_BLOCK) = Some (VL md :: cred' :: VL nwB :: restB)
  /\ heap_add_window (VL md :: cred' :: VL nwB :: restB) (VP kS wzero) (twin_len nsv) (VL K_TWIN) = Some h3.
Proof.
  pose proof nw_small as NS.
  destruct (add_window_facts E' md cred' nw rest n (VP kB wzero) nsv (VL CtrLib.K_BLOCK) Tnw Nn Ln ltac:(lia)) as (A1 & T1 & N1 & L1 & _).
  fold restB nwB in A1, T1, N1, L1.
  destruct (add_window_facts E' md cred' nwB restB (S n) (VP kS wzero) (twin_len nsv) (VL K_TWIN) T1 N1 L1
              ltac:(destruct (wadd_one_small nw Tnw ltac:(lia)) as [_ X]; fold nwB in X; lia)) as (A2 & _).
  split; [rewrite Eh; reflexivity|]. split; [exact A1| exact A2].
Qed.

Lemma rest_below : forallb (sv_vars_below (s_next st)) rest = true.
Proof.
  destruct SVB_parts as (_ & _ & _ & _ & _ & SO). pose proof (proj1 (forallb_forall _ _) SO _ (find_op_In _ _ _ Hf)) as X.
  cbn [op_args] in X. rewrite Eh in X. cbn [forallb] in X. apply andb_prop in X as [_ X]. apply andb_prop in X as [_ X]. apply andb_prop in X as [_ X]. exact X.
Qed.
Lemma A_below : sv_vars_below (s_next st) A = true.
Proof.
  destruct SVB_parts as (_ & _ & _ & _ & _ & SO). pose proof (proj1 (forallb_forall _ _) SO _ (find_op_In _ _ _ Hf)) as X.
  cbn [op_args] in X. rewrite Eh in X. cbn [forallb] in X. apply andb_prop in X as [_ X]. apply andb_prop in X as [X _]. exact X.
Qed.

Lemma wins_of_E' : forall m0 l, forallb (sv_vars_below (s_next st)) l = true -> wins_of E' m0 l = wins_of E m0 l.
Proof.
  induction m0 as [|m0 IH]; intros l AV; [reflexivity|]. destruct l as [|x [|y [|z l']]]; try reflexivity. cbn [forallb] in AV.
  apply andb_prop in AV as [A1 AV]. apply andb_prop in AV as [A2 AV]. apply andb_prop in AV as [A3 AV].
  rewrite !wins_of_cons, (IH l' AV), !den_E' by assumption. reflexivity.
Qed.
Lemma map_den_E' : forall l, forallb (sv_vars_below (s_next st)) l = true -> map (den E') l = map (den E) l.
Proof.
  induction l as [|x l IH]; intros AV; [reflexivity|]. cbn [forallb] in AV. apply andb_prop in AV as [A1 AV].
  cbn [map]. rewrite (den_E' x A1), (IH AV). reflexivity.
Qed.
Lemma forallb_skipn : forall {T} (f : T -> bool) j l, forallb f l = true -> forallb f (skipn j l) = true.
Proof.
  intros T f j. induction j as [|j IH]; intros l H; [exact H|]. destruct l as [|x l]; [reflexivity|]. cbn [skipn]. cbn [forallb] in H.
  apply andb_prop in H as [_ H]. exact (IH l H).
Qed.

Definition WB : window := Win Ablk N K_BLOCK.
Definition WT : window := Win (shad Ablk) (shlen (N + 7)) K_TWINz.

Lemma DEC3 : decode (map (den E') h3)
  = Some (w2Z md, Z_to_bv 64 (bv_unsigned aw - CHG), (wins_of E n rest ++ [WB]) ++ [WT], map (den E) (skipn (3 * n) rest)).
Proof.
  pose proof nw_small as NS. destruct NEWB as (NN & _).
  destruct (add_window_facts E' md cred' nw rest n (VP kB wzero) nsv (VL CtrLib.K_BLOCK) Tnw Nn Ln ltac:(lia)) as (_ & T1 & N1 & L1 & W1 & S1).
  fold restB nwB in T1, N1, L1, W1, S1.
  destruct (add_window_facts E' md cred' nwB restB (S n) (VP kS wzero) (twin_len nsv) (VL K_TWIN) T1 N1 L1
              ltac:(destruct (wadd_one_small nw Tnw ltac:(lia)) as [_ X]; fold nwB in X; lia)) as (_ & T2 & N2 & L2 & W2 & S2).
  fold restT nwT in T2, N2, L2, W2, S2.
  unfold h3. rewrite (decode_hargs E' md cred' nwT restT (S (S n)) T2 N2 L2). rewrite W2, W1, S2, S1.
  rewrite (wins_of_E' n rest rest_below), (map_den_E' _ (forallb_skipn _ (3 * n) rest rest_below)).
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (den_E' nsv nsv_below); exact NDEN).
  assert (C1 : den E' cred' = Z_to_bv 64 (bv_unsigned aw - CHG)).
  { unfold cred', CHG. destruct pd.
    - rewrite (den_E' A A_below), Z.sub_0_r, AWden. symmetry. apply Z_to_bv_bv_unsigned.
    - rewrite den_sv_alu. rewrite (den_E' A A_below). unfold alu64, alu. apply bv_eq.
      rewrite bv_sub_unsigned, Z_to_bv_unsigned, DN, AWden. reflexivity. }
  assert (C2 : Win (bv_unsigned (den E' (VP kB wzero))) (bv_unsigned (den E' nsv)) (bv_unsigned (den E' (VL CtrLib.K_BLOCK))) = WB).
  { unfold WB. rewrite HeapCtr.TwinB.den_VPz, ev_kB, DN. reflexivity. }
  assert (C3 : Win (bv_unsigned (den E' (VP kS wzero))) (bv_unsigned (den E' (twin_len nsv))) (bv_unsigned (den E' (VL K_TWIN))) = WT).
  { unfold WT. rewrite HeapCtr.TwinB.den_VPz, ev_kS. rewrite (CallA.TwinB.twin_len_den E' nsv) by (rewrite DN; unfold AREQMAX in NN; lia).
    rewrite DN. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite C1, C2, C3. reflexivity.
Qed.

Hypothesis AW'E : aw' = Z_to_bv 64 (bv_unsigned aw - CHG).

Lemma windows_wf_mono : forall ws L1 L2 c, windows_wf ws L1 c -> (forall b, In b L1 -> In b L2) -> windows_wf ws L2 c.
Proof.
  intros ws L1 L2 c WF0 SUB. apply Forall_forall. intros w Hw.
  pose proof (proj1 (Forall_forall _ _) WF0 w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SB)]]]).
  - split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. left; auto.
  - split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. right; left; auto.
  - split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. right; right. split; [exact K|]. exists b. auto.
Qed.

Lemma HOLDS3 : op_holds OPS HEAP_ID (map (den E') h3) m' mo'.
Proof.
  rewrite OPS_holds1. destruct WORLD' as (AWH' & PAT & UB & DJ & NIN & DJT). destruct NEWB as (NN & BR & _).
  destruct (twin_band _ _ BR NN) as (T1 & T2 & T3 & _). assert (BK16 : 0 <= N /\ Ablk mod 8 = 0) by (destruct BR as (_ & X0 & _ & X16); split; [exact X0| clear - X16; Z.div_mod_to_equations; lia]).
  destruct BR as (BK & _ & TOP & _). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  assert (TWFRESH : forall a, in_iv (shad Ablk, shlen (N + 7)) a -> ~ in_user ((Ablk, N) :: LB) a).
  { intros a Ha U. apply in_ivs_cons in U as [U|U]; [| exact (DJT a Ha U)].
    unfold in_iv in Ha, U. cbn [fst snd] in Ha, U. unfold user_band in UB. lia. }
  exists (w2Z md), aw', ((wins_of E n rest ++ [WB]) ++ [WT]), (map (den E) (skipn (3 * n) rest)), LB', Wm.
  split; [rewrite AW'E; exact DEC3|]. split; [exact AWH'|]. split; [| split].
  -
    apply Forall_app. split; [apply Forall_app; split|].
    + apply (windows_wf_mono _ LB LB' _ WF). intros b Hb. right; right. exact Hb.
    + constructor; [|constructor]. unfold window_wf, WB, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; left. split; [reflexivity|]. right; left. reflexivity.
    + constructor; [|constructor]. unfold window_wf, WT, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; right. split; [unfold K_SUB, K_TWINz; lia|]. exists (shad Ablk, shlen (N + 7)). split; [left; reflexivity|]. intros a Ha. exact Ha.
  -
    assert (HC1 : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * n) rest)) LB (wins_of E n rest) m').
    { apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U _.
      destruct (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; right; exact U)) as (E1 & _). unfold ALib.Mem.wa in E1. symmetry. exact E1. }
    pose proof (cw_grow Cw _ _ _ _ m' Ablk N HC1 DJ) as HC2.
    apply (Cw_ghost_grow _ _ _ _ m' Ablk N (shlen (N + 7)) HC2); [apply in_or_app; right; left; reflexivity| lia| destruct BK16 as [_ X]; exact X|].
    exact TWFRESH.
  -
    apply (ties_grow_heap WW (wins_of E n rest) (w_L WW) RNG' sta' m' (HB p Ablk N) TI ltac:(exists p; reflexivity)); [cbn [ab_size]; lia| | exact PRS].
    cbn [ab_addr ab_size]. fold WB WT.
    assert (GA0 : ghost_apart (wins_of E n rest)) by (destruct TI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
    assert (WF1 : windows_wf (wins_of E n rest ++ [WB]) ((Ablk, N) :: LB) (ATOP + 4096)).
    { apply Forall_app. split; [apply (windows_wf_mono _ LB _ _ WF); intros b Hb; right; exact Hb|].
      constructor; [|constructor]. unfold window_wf, WB, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; left. split; [reflexivity|]. left. reflexivity. }
    apply (ghost_apart_new_ghosts (wins_of E n rest ++ [WB]) _ ((Ablk, N) :: LB) (ATOP + 4096) WF1).
    + exact (ghost_apart_new_block _ LB (ATOP + 4096) Ablk N WF GA0 DJ).
    + intros w Hw. apply in_app_or in Hw as [Hw|[<-|[]]]; [left; exact Hw| right]. split; [unfold WT; cbn [w_kind]; unfold K_TWINz, K_BLOCK; lia|].
      intros _ a Ha. unfold WT, w_iv in Ha. cbn [w_lo w_len] in Ha. exact (TWFRESH a Ha).
Qed.

Hypothesis OTH : OTHER mo mo'.

Definition ops' : list opinst := set_op HEAP_ID h3 (s_ops st).

Lemma hargs_below : forallb (sv_vars_below (s_next st)) hargs = true.
Proof.
  destruct SVB_parts as (_ & _ & _ & _ & _ & SO). exact (proj1 (forallb_forall _ _) SO _ (find_op_In _ _ _ Hf)).
Qed.
Lemma DEC' : decode (map (den E') hargs) = Some (w2Z md, den E A, wins_of E n rest, map (den E) (skipn (3 * n) rest)).
Proof. rewrite (map_den_E' hargs hargs_below). exact DEC. Qed.

Lemma in_ws_app : forall ws1 ws2 a, in_ws (ws1 ++ ws2) a <-> in_ws ws1 a \/ in_ws ws2 a.
Proof. intros. unfold in_ws. rewrite map_app. apply in_ivs_app. Qed.

Lemma OPS_HOLD' : ops_hold OPS E' ops' m' mo'.
Proof.
  apply (ops_hold_set_op OPS E' E' (s_ops st) HEAP_ID hargs h3 (ms_mem ms) m' mo mo' Hf Hc (so_ops _ _ _ _ _ _ HS')); [| exact HOLDS3].
  intros o Ho NI H. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
  apply (OPS_mo_other _ _ _ mo mo' NI OTH). apply (OPS_frame_other _ _ (ms_mem ms) m' mo NI H).
  - intros a Ha FP. destruct (OPS_fp_other _ _ a NI FP) as [R|[(a' & R & ->)|(a' & R & ->)]].
    + destruct (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact R)) as (E1 & _). unfold ALib.Mem.wa in E1. symmetry. exact E1.
    + pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [right; left; exact R| reflexivity]))) as E1.
      unfold ALib.Mem.wa in E1. symmetry. exact E1.
    + pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact R| reflexivity]))) as E1.
      unfold ALib.Mem.wa in E1. symmetry. exact E1.
  - intros a Ha C W. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in W.
    refine (proj2 (PRES a ltac:(unfold two64 in Ha; lia) _) W).
    destruct C as [C|[(a' & C & ->)|(a' & C & ->)]]; [right; left; exact C| |]; right; right; right; exists a'; (split; [| reflexivity]); [right; left; exact C| left; exact C].
Qed.

Lemma aci_low : forall a, in_ranges (aci AI) a -> a < AIMG_HI.
Proof. intros a (iv0 & Hi & R). pose proof (AI_aci_img AI iv0 Hi). lia. Qed.

Lemma APART_g : forall RG : IMap.t region,
  (forall a, in_based E' RG a -> in_iv (shad Ablk, shlen (N + 7)) a \/ in_iv (Ablk, N) a \/ in_based E' (s_regs st) a) ->
  ops_apart bsegs OPS E' ops' RG (s_priv st).
Proof.
  intros RG RGB.
  destruct NEWB as (NN & BR & _). destruct (twin_band _ _ BR NN) as (T1 & T2 & T3 & _). destruct BR as (BK & _ & TOP & _).
  unfold ablk, AIMG_HI, KLS in BK.
  apply (ops_apart_set_op bsegs OPS E' E' (s_ops st) HEAP_ID hargs h3 (s_regs st) RG (s_priv st) Hf Hc (so_apart _ _ _ _ _ _ HS')).
  - intros o a Ho NI OLD FP. destruct (OLD FP) as [NB IP]. split; [| exact IP].
    intros IB. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    pose proof atop_range as ATR. pose proof ATOP_al16 as AT16.
    assert (LOW : a < 6492160 \/ 0x7fff8000 <= a < 0x800be200 \/ shad ATOP <= a < 0x10007fff8000).
    { destruct (OPS_fp_other _ _ a NI FP) as [R|[(a' & R & ->)|(a' & R & ->)]]; [left; pose proof (aci_low a R) as X; unfold AIMG_HI in X; exact X| |].
      - right. left. apply CtrPre.TwinB.shad_img_band. split; [destruct R as (iv0 & Hi & R); pose proof (AI_aci_lo AI iv0 Hi); lia| exact (aci_low a' R)].
      - right. right. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - R ATR. Z.div_mod_to_equations. lia. }
    assert (SHA : 0x800be200 <= shad Ablk) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).

    assert (SHT : shad Ablk + shlen (N + 7) <= shad ATOP).
    { destruct NEWB as (_ & (_ & N0 & _ & A16) & _). unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      clear - TOP N0 A16 AT16. Z.div_mod_to_equations. lia. }
    assert (SHATOP : 0x7fff8000 + 0x7fff7f800000 / 8 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - ATR; Z.div_mod_to_equations; lia).
    destruct (RGB a IB) as [I|[I|I]]; [unfold in_iv in I; cbn [fst snd] in I; lia| unfold in_iv in I; cbn [fst snd] in I; lia| exact (NB I)].
  - intros a FP. rewrite OPS_fp1 in FP. apply (proj1 (fp_spec IMGX _ _ _ _ _ a DEC3)) in FP as (Ha & NIX & NWS).
    assert (NW0 : ~ in_ws (wins_of E n rest) a) by (intros X; apply NWS; apply in_ws_app; left; apply in_ws_app; left; exact X).
    destruct (ops_apart_find bsegs OPS E' (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a (so_apart _ _ _ _ _ _ HS') Hf) as [NB IP].
    { rewrite OPS_fp1. apply (proj2 (fp_spec IMGX _ _ _ _ _ a DEC')). auto. }
    split; [| exact IP]. intros IB. destruct (RGB a IB) as [I|[I|I]]; [| | exact (NB I)]; apply NWS; apply in_ws_app.
    + right. unfold in_ws. apply in_ivs_In. exists (w_iv WT). split; [left; reflexivity| exact I].
    + left. apply in_ws_app. right. unfold in_ws. apply in_ivs_In. exists (w_iv WB). split; [left; reflexivity| exact I].
Qed.

Lemma APART' : ops_apart bsegs OPS E' ops' RgP (s_priv st).
Proof. exact (APART_g RgP RgP_in_based). Qed.

Lemma ops'_cases : In (OpI HEAP_ID h3) ops' /\ forall o, In o (s_ops st) -> o = OpI HEAP_ID hargs \/ In o ops'.
Proof.
  destruct (find_op_unique HEAP_ID (s_ops st) hargs Hf Hc) as (l1 & l2 & E0 & F1 & F2). unfold ops'. rewrite E0, (set_op_split HEAP_ID h3 l1 l2 hargs F1).
  split; [apply in_app_iff; right; left; reflexivity|].
  intros o Ho. apply in_app_iff in Ho as [Ho|[Ho|Ho]]; [right; apply in_app_iff; left; exact Ho| left; symmetry; exact Ho| right; apply in_app_iff; right; right; exact Ho].
Qed.

Lemma COVER_g : forall RG : IMap.t region,
  (forall a, in_based E' RG a -> in_iv (shad Ablk, shlen (N + 7)) a \/ in_iv (Ablk, N) a \/ in_based E' (s_regs st) a) ->
  forall a, fx_acc bsegs E' RG a -> op_cov OPS (insts E' ops') a.
Proof.
  intros RG RGB a [IB|IMG]; [| left; exact (OPS_cov0_img a IMG)].
  destruct ops'_cases as [INH OTHERS].
  assert (NEWCOV0 : in_ws (heap_ws ((wins_of E n rest ++ [WB]) ++ [WT])) a \/ sh_cov a -> op_cov OPS (insts E' ops') a).
  { intros X. right. apply Exists_exists. exists (HEAP_ID, map (den E') h3). split.
    - unfold insts. apply in_map_iff. exists (OpI HEAP_ID h3). split; [reflexivity| exact INH].
    - cbn [fst snd]. apply OPS_cov1. split; [reflexivity|]. eexists _, _, _, _. split; [exact DEC3| exact X]. }
  assert (NEWCOV : in_ws (heap_ws ((wins_of E n rest ++ [WB]) ++ [WT])) a -> op_cov OPS (insts E' ops') a) by (intros X; exact (NEWCOV0 (or_introl X))).
  assert (HWS : forall w, In w [WB; WT] -> in_iv (w_iv w) a -> in_ws (heap_ws ((wins_of E n rest ++ [WB]) ++ [WT])) a).
  { intros w Hw I. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv w). split; [| exact I]. apply in_map. apply filter_In. split.
    - destruct Hw as [<-|[<-|[]]]; [apply in_or_app; left; apply in_or_app; right; left; reflexivity| apply in_or_app; right; left; reflexivity].
    - destruct Hw as [<-|[<-|[]]]; reflexivity. }
  destruct (RGB a IB) as [I|[I|I]].
  - apply NEWCOV. apply (HWS WT); [right; left; reflexivity| exact I].
  - apply NEWCOV. apply (HWS WB); [left; reflexivity| exact I].
  - destruct (so_cover _ _ _ _ _ _ HS' a (or_introl I)) as [C0|C1]; [left; exact C0|].
    apply Exists_exists in C1 as (oi & Hoi & CV). unfold insts in Hoi. apply in_map_iff in Hoi as (o & <- & Ho). cbn [fst snd] in CV.
    destruct (OTHERS o Ho) as [->|INo].
    + cbn [op_id op_args] in CV. apply OPS_cov1 in CV as (_ & md0 & aw0 & ws0 & ca0 & D0 & X). rewrite DEC' in D0. injection D0 as <- <- <- <-.
      destruct X as [X|X]; [| exact (NEWCOV0 (or_intror X))].
      apply NEWCOV. unfold in_ws, heap_ws in *. apply in_ivs_In in X as (v & Hv & Hin). apply in_ivs_In. exists v. split; [| exact Hin].
      apply in_map_iff in Hv as (w & <- & Hw). apply in_map. apply filter_In in Hw as [Hw K]. apply filter_In. split; [| exact K].
      apply in_or_app. left. apply in_or_app. left. exact Hw.
    + right. apply Exists_exists. exists (op_id o, map (den E') (op_args o)). split; [| exact CV].
      unfold insts. apply in_map_iff. exists o. split; [reflexivity| exact INo].
Qed.

Lemma COVER' : forall a, fx_acc bsegs E' RgP a -> op_cov OPS (insts E' ops') a.
Proof. exact (COVER_g RgP RgP_in_based). Qed.

Definition f_range : fact := FRange kB BLK_LO BLK_HI.
Definition f_align : fact := FAlign kB 4%uint63.
Definition f_link : fact := FEq (VP kS wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP kB wzero) (VL (wlit 3%uint63))) (VL SBw)).

Definition f_cred : fact := cred_fact (s_facts st) nsv A.
Hypothesis CREDF : fact_holds E f_cred.
Lemma CREDF' : fact_holds E' f_cred.
Proof.
  revert CREDF. unfold f_cred, cred_fact. destruct (prim_decided (s_facts st) nsv); cbn [fact_holds].
  - rewrite (den_E' A A_below). cbn [den]. intros X; exact X.
  - rewrite (den_E' nsv nsv_below), (den_E' A A_below). intros X; exact X.
Qed.

Lemma FACTS' : facts_hold E' (f_link :: f_align :: f_range :: f_cred :: s_facts st).
Proof.
  destruct NEWB as (NN & BR & _). destruct BR as (BK & _ & TOP & AL). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  constructor; [| constructor; [| constructor; [| constructor; [exact CREDF'| exact (so_facts _ _ _ _ _ _ HS')]]]].
  - cbn [fact_holds f_link]. rewrite HeapCtr.TwinB.den_VPz.
    change (den E' (VAlu ALU_ADD (VAlu ALU_SRL (VP kB wzero) (VL (wlit 3%uint63))) (VL SBw)))
      with (alu64 ALU_ADD (alu64 ALU_SRL (den E' (VP kB wzero)) (wbv (wlit 3%uint63))) (wbv SBw)).
    rewrite HeapCtr.TwinB.den_VPz. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, bv_shiftr_unsigned, bv_and_unsigned, ev_kS, ev_kB.
    replace (bv_unsigned (wbv (wlit 3%uint63))) with 3 by (vm_compute; reflexivity).
    replace (bv_unsigned (Z_to_bv 64 63)) with 63 by (vm_compute; reflexivity).
    change (Z.land 3 63) with 3.
    replace (bv_unsigned (wbv SBw)) with 0x7fff8000 by (vm_compute; reflexivity).
    unfold shad, ASHOFF, bv_wrap, bv_modulus. rewrite Z.mod_small; [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    change (2 ^ Z.of_N 64) with (2 ^ 64). clear - BK TOP ATR NN. Z.div_mod_to_equations. lia.
  - cbn [fact_holds f_align]. rewrite ev_kB. change (2 ^ to_Z 4%uint63) with 16. exact AL.
  - cbn [fact_holds f_range]. rewrite ev_kB. replace (w2Z BLK_LO) with 0x631000 by (vm_compute; reflexivity).
    replace (w2Z BLK_HI) with (2 ^ 47 - 1) by (vm_compute; reflexivity). lia.
Qed.

Hypothesis A0' : AP.getr R' 10%bv = Z_to_bv 64 Ablk.
Hypothesis MINVo : op_minv OPS mo'.

Lemma kB_next : s_next (clobber st1) = kB.
Proof.
  destruct (clobber_fields st1) as (_ & _ & _ & _ & _ & _ & _ & NXc). destruct st1_fields as (_ & _ & _ & _ & _ & _ & _ & NX1).
  rewrite NXc, NX1. symmetry. destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma kS_next : PrimInt63.add kB 1%uint63 = kS.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  apply Uint63.to_Z_inj. rewrite add_Z by (rewrite kB_Z; change (to_Z 1%uint63) with 1; rewrite wB_two63, two63_eq; lia).
  rewrite kB_Z, kS_Z. change (to_Z 1%uint63) with 1. lia.
Qed.

Lemma stB_shape : alloc_stB_g TWR XN st st1 r h3 A
  = SS r (rf_set (s_rf (clobber st1)) X10 (VP kB wzero)) (s_ff st) (s_resv st) RgP
       (f_link :: f_align :: f_range :: f_cred :: s_facts st) ops' (s_priv st) (PrimInt63.add kS 1%uint63).
Proof.
  unfold alloc_stB_g. cbv zeta. rewrite kB_next, kS_next. fold nsv. rewrite stB_shape_gen.
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & _). destruct st1_fields as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & _).
  rewrite FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1, st1_regs. reflexivity.
Qed.

Theorem post_B : st_ok bsegs OPS E' (alloc_stB_g TWR XN st st1 r h3 A) ms' mo'.
Proof.
  rewrite stB_shape.
  assert (DKB : den E' (VP kB wzero) = AP.getr R' 10%bv).
  { rewrite HeapCtr.TwinB.den_VPz, A0'. apply bv_eq. rewrite ev_kB. destruct NEWB as (NN & (BK & _ & TOP & _) & _). pose proof atop_range.
    unfold ablk, AIMG_HI, KLS in BK. symmetry. apply Z_to_bv_small. unfold bv_modulus, two64. lia. }
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next ms' ms_pc_val ms_regs ms_fregs ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending MS].
  - reflexivity.
  - rewrite rf_get_set_other by discriminate. change (rf_get (s_rf (clobber st1)) X0) with (getr (clobber st1) X0). rewrite getr_clobber. cbn [clob_pos].
    destruct st1_fields as (_ & RF1 & _). unfold getr. rewrite RF1. exact (so_x0 _ _ _ _ _ _ HS).
  - exact (post_regs (VP kB wzero) DKB).
  - exact (so_fregs _ _ _ _ _ _ HS').
  - reflexivity.
  - rewrite (HeapCtr.TwinB.call_pre_resv st r CP). reflexivity.
  - exact (so_fcsr _ _ _ _ _ _ HS).
  - reflexivity.
  - exact (so_zero _ _ _ _ _ _ HS').
  - exact RgP_bst.
  - exact all_regions_ok.
  - exact RgP_disjoint.
  - exact RgP_pub.
  - exact FACTS'.
  - exact OPS_HOLD'.
  - exact APART'.
  - exact MINVo.
  - exact COVER'.
  - intros a b H seg Hs. pose proof (MINV' a b H) as X. unfold ALib.Mem.ro_addr in X. rewrite Hs in X.
    destruct (seg_writable seg); [reflexivity| discriminate X].
Qed.

Definition kS2 : int := addn (s_next st) 17.
Lemma kS2_Z : to_Z kS2 = to_Z (s_next st) + 17.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold kS2. rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma kS2_next : PrimInt63.add kS 1%uint63 = kS2.
Proof.
  destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  apply Uint63.to_Z_inj. rewrite add_Z by (rewrite kS_Z; change (to_Z 1%uint63) with 1; rewrite wB_two63, two63_eq; lia).
  rewrite kS_Z, kS2_Z. change (to_Z 1%uint63) with 1. lia.
Qed.
Lemma kS2_nz : PrimInt63.eqb kS2 0%uint63 = false.
Proof. apply Uint63.eqb_false_spec. intros X. pose proof kS2_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia. Qed.
Definition RgPb : IMap.t region := IMap.add kS2 (tail_region nsv) RgP.
Definition f_tail : fact := tail_fact kS2 kS nsv.
Definition f_sign : fact := FULt (VL wzero) nsv.

Lemma stBb_shape : TWR = twin_main nsv -> alloc_stBb XN st st1 r h3 A
  = SS r (rf_set (s_rf (clobber st1)) X10 (VP kB wzero)) (s_ff st) (s_resv st) RgPb
       (f_sign :: f_tail :: f_link :: f_align :: f_range :: f_cred :: s_facts st) ops' (s_priv st) (PrimInt63.add kS2 1%uint63).
Proof.
  intros TM. unfold alloc_stBb. cbv zeta. rewrite kB_next, kS_next, kS2_next. fold nsv. rewrite stBb_shape_gen.
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & _). destruct st1_fields as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & _).
  rewrite FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1, st1_regs. unfold RgPb, RgP. rewrite TM. reflexivity.
Qed.

Section PAIR.
Hypothesis TM : TWR = twin_main nsv.
Hypothesis F17 : Fv 17 = Z_to_bv 64 (shad Ablk + (N - 1) / 8).

Lemma tail_geo : 0 <= (N - 1) / 8 /\ (N - 1) / 8 + 1 <= (N + 7) / 8 /\ shad Ablk + (N + 7) / 8 <= 0x10007fff8000.
Proof.
  destruct NEWB as (NN & BR & _). destruct (twin_band _ _ BR NN) as (T1 & T2 & _). unfold shlen in T2. rewrite Z.shiftr_div_pow2 in T2 by lia. change (2 ^ 3) with 8 in T2.
  split; [clear - NN; Z.div_mod_to_equations; lia|]. split; [clear - NN; Z.div_mod_to_equations; lia| exact T2].
Qed.
Lemma ev_kS2 : bv_unsigned (ev E' kS2) = shad Ablk + (N - 1) / 8.
Proof.
  unfold kS2. rewrite ev_E'_fresh by lia. change (Z.of_nat 17) with 17. rewrite F17. destruct NEWB as (N1 & BR & _).
  destruct (twin_band _ _ BR N1) as (T1 & _). destruct tail_geo as (G0 & G1 & G2). apply Z_to_bv_small. unfold bv_modulus, two64. lia.
Qed.
Lemma tail_range : forall a, bv_unsigned (ev E' kS2) + loZ (tail_region nsv) <= a < bv_unsigned (ev E' kS2) + hiZ E' (tail_region nsv) ->
  a = shad Ablk + (N - 1) / 8 /\ in_iv (shad Ablk, shlen (N + 7)) a.
Proof.
  intros a Ha. destruct (CallA.TwinB.tail_region_fields nsv) as (LO & HI & _). rewrite ev_kS2 in Ha.
  assert (LZ : loZ (tail_region nsv) = 0) by (unfold loZ; rewrite LO; reflexivity).
  assert (HZ : hiZ E' (tail_region nsv) = 1) by (unfold hiZ; rewrite HI; cbn [den]; rewrite wbv_unsigned; reflexivity).
  rewrite LZ, HZ in Ha. destruct tail_geo as (G0 & G1 & _). split; [lia|]. unfold in_iv, shlen. cbn [fst snd]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
Qed.
Lemma tail_region_okA : region_ok bsegs (s_priv st) E' m' kS2 (tail_region nsv).
Proof.
  destruct NEWB as (N1 & BR & WR). destruct WORLD' as (_ & PAT & _). pose proof WORLD'_asan as AWH'. destruct tail_geo as (G0 & G1 & G2).
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (den_E' nsv nsv_below); exact NDEN).
  apply (CallA.TwinB.tail_region_ok bsegs (s_priv st) E' m' kS2 nsv kS2_nz); rewrite ?DN, ?ev_kS2.
  - unfold two64. lia.
  - pose proof (PAT ((N - 1) / 8) G0 ltac:(clear - N1; Z.div_mod_to_equations; lia)) as P1. unfold rb. unfold ALib.Mem.wa in P1. rewrite P1.
    do 2 f_equal. destruct (Z.leb_spec (8 * ((N - 1) / 8) + 8) N) as [FL|PT]; [clear - N1 FL| clear - N1 PT]; Z.div_mod_to_equations; lia.
  - apply (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw' LB' m' mo' _ (shad Ablk + (N - 1) / 8) AWH' ltac:(left; reflexivity)
                   ltac:(unfold in_iv; cbn [fst snd]; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; lia))).
Qed.
Lemma RgPb_find : forall k0 rg, IMap.find k0 RgPb = Some rg -> (k0 = kS2 /\ rg = tail_region nsv) \/ (k0 <> kS2 /\ IMap.find k0 RgP = Some rg).
Proof.
  intros k0 rg H. unfold RgPb in H. destruct (Uint63.eqb kS2 k0) eqn:Q.
  - apply Uint63.eqb_correct in Q. subst k0. rewrite IMap.find_add_same in H by exact RgP_bst. injection H as <-. left. auto.
  - rewrite IMap.find_add_other_eqb in H by (exact RgP_bst || exact Q). right. apply Uint63.eqb_false_spec in Q. split; [congruence| exact H].
Qed.
Lemma RgPb_in_based : forall a, in_based E' RgPb a ->
  in_iv (shad Ablk, shlen (N + 7)) a \/ in_iv (Ablk, N) a \/ in_based E' (s_regs st) a.
Proof.
  intros a (k0 & rg & H & KZ & R). destruct (RgPb_find k0 rg H) as [[-> ->]|[_ F]].
  - left. exact (proj2 (tail_range a R)).
  - apply RgP_in_based. exists k0, rg. auto.
Qed.

Lemma twin_iv_apart : forall k0 rg a, IMap.find k0 RgP = Some rg -> PrimInt63.eqb k0 0%uint63 = false -> k0 <> kS ->
  bv_unsigned (ev E' k0) + loZ rg <= a < bv_unsigned (ev E' k0) + hiZ E' rg -> in_iv (shad Ablk, shlen (N + 7)) a -> False.
Proof.
  intros k0 rg a H KZ NK Ha I.
  destruct NEWB as (NN & BR & _). destruct (twin_band _ _ BR NN) as (T1 & T2 & T3 & _). destruct WORLD' as (_ & _ & UB & DJ & _ & DJT).
  pose proof atop_range as ATR. pose proof sp_floor as SPF. destruct BR as (BK & _ & TOP & _). unfold ablk, AIMG_HI, KLS in BK.
  assert (TW_B : in_iv (Ablk, N) a -> False) by (unfold in_iv in *; cbn [fst snd] in *; unfold user_band in UB; lia).
  assert (TW_S : ATOP + 4096 <= a -> False) by (unfold in_iv in I; cbn [fst snd] in I; lia).
  assert (SHB : sh_cov a -> (0x7fffa000 <= a < 0x800be0e0) \/ (shad ATOP <= a < 0x10007fff8000)) by exact (sh_cov_band a).
  destruct (shadow_tight Ablk N ltac:(unfold ablk, AIMG_HI, KLS; exact BK) TOP ltac:(lia)) as [TT1 TT2].
  assert (TW_C : sh_cov a -> False) by (intros Y; apply SHB in Y; unfold in_iv in I; cbn [fst snd] in I; lia).
  destruct (RgP_range k0 rg a H KZ Ha) as [[E1 _]|[[_ I2]|[[_ I2]|(_ & _ & _ & [I2|[I2|I2]])]]].
  - contradiction.
  - exact (TW_B I2).
  - exact (TW_S (proj1 I2)).
  - exact (TW_S (proj1 I2)).
  - exact (DJT a I I2).
  - exact (TW_C I2).
Qed.
Lemma FACTSb : facts_hold E' (f_sign :: f_tail :: f_link :: f_align :: f_range :: f_cred :: s_facts st).
Proof.
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (den_E' nsv nsv_below); exact NDEN). destruct tail_geo as (G0 & G1 & G2).
  constructor; [| constructor; [| exact FACTS']].
  - cbn [fact_holds f_sign]. rewrite DN. cbn [den]. rewrite wbv_unsigned, wzero_ok. destruct NEWB as (NN & _). clear - NN. lia.
  - unfold f_tail, tail_fact. cbn [fact_holds]. rewrite HeapCtr.TwinB.den_VPz. apply bv_eq. destruct NEWB as (NN & _).
    rewrite (CallA.TwinB.tail_rhs_den E' kS nsv) by (rewrite ?ev_kS, DN; clear - NN G0 G1 G2; lia). rewrite ev_kS2, ev_kS, DN. reflexivity.
Qed.

Theorem post_Bb : st_ok bsegs OPS E' (alloc_stBb XN st st1 r h3 A) ms' mo'.
Proof.
  pose proof post_B as PB. rewrite stB_shape in PB. rewrite (stBb_shape TM).
  destruct PB as [Qpc Qx0 Qregs Qfregs Qsvc Qresv Qfcsr Qrom Qz Qbst Qreg Qdisj Qpub Qfacts Qops Qapart Qmf Qcov Qminv].
  cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in *.
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - unfold RgPb. apply IMap.bst_add. exact RgP_bst.
  - intros k0 rg H. destruct (RgPb_find k0 rg H) as [[-> ->]|[_ F]]; [exact tail_region_okA| exact (Qreg k0 rg F)].
  - intros k1 rg1 k2 rg2 H1 H2 NE Z1 Z2 WR a [A1 A2]. destruct TWR_geo as (_ & _ & TWW).
    destruct (CallA.TwinB.tail_region_fields nsv) as (_ & _ & TLW & _).
    destruct (RgPb_find k1 rg1 H1) as [[-> ->]|[N1 F1]]; destruct (RgPb_find k2 rg2 H2) as [[-> ->]|[N2 F2]].
    + contradiction.
    + destruct (tail_range a A1) as [_ I]. destruct (Uint63.eqb k2 kS) eqn:QS.
      * apply Uint63.eqb_correct in QS. subst k2. destruct (RgP_find kS rg2 F2) as [[_ ->]|[[X _]|[[X _]|(X & _)]]];
          [destruct WR as [W|W]; congruence | | |]; exfalso; pose proof kS_Z; pose proof kB_Z;
          [rewrite X in *; lia | destruct (CallA.TwinB.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite <- X in *; lia | congruence].
      * apply Uint63.eqb_false_spec in QS. exact (twin_iv_apart k2 rg2 a F2 Z2 QS A2 I).
    + destruct (tail_range a A2) as [_ I]. destruct (Uint63.eqb k1 kS) eqn:QS.
      * apply Uint63.eqb_correct in QS. subst k1. destruct (RgP_find kS rg1 F1) as [[_ ->]|[[X _]|[[X _]|(X & _)]]];
          [destruct WR as [W|W]; congruence | | |]; exfalso; pose proof kS_Z; pose proof kB_Z;
          [rewrite X in *; lia | destruct (CallA.TwinB.sp_region_inv st _ offs rss SPR) as (_ & Hrs & _); pose proof (old_key_lt _ _ Hrs); rewrite <- X in *; lia | congruence].
      * apply Uint63.eqb_false_spec in QS. exact (twin_iv_apart k1 rg1 a F1 Z1 QS A1 I).
    + exact (Qdisj k1 rg1 k2 rg2 F1 F2 NE Z1 Z2 WR a (conj A1 A2)).
  - intros r0 g gr c H0 Hg Hcc i Hi. destruct (RgPb_find _ _ H0) as [[X _]|[_ F]].
    + exfalso. pose proof kS2_Z as KZ. rewrite <- X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NX as (_ & P & _). lia.
    + exact (Qpub r0 g gr c F Hg Hcc i Hi).
  - exact FACTSb.
  - exact (APART_g RgPb RgPb_in_based).
  - exact (COVER_g RgPb RgPb_in_based).
Qed.
End PAIR.

Theorem post_all : st_ok bsegs OPS E' (alloc_stB_g TWR XN st st1 r h3 A) ms' mo'
  /\ (TWR = twin_main nsv -> Fv 17 = Z_to_bv 64 (shad Ablk + (N - 1) / 8) -> st_ok bsegs OPS E' (alloc_stBb XN st st1 r h3 A) ms' mo').
Proof. split; [exact post_B| exact post_Bb]. Qed.
Lemma FEQ_holds : N mod 8 = 0 -> fact_holds E' (FEq (sz_and7 nsv) (VL wzero)).
Proof.
  intros Z8. cbn [fact_holds]. apply bv_eq. rewrite CallA.TwinB.sz_and7_den, (den_E' nsv nsv_below), NDEN, Z8. cbn [den]. rewrite wbv_unsigned, wzero_ok. reflexivity.
Qed.

End POST.

Definition cfvA (R' : bvmap 5 word) (A S : word) (i : Z) : word :=
  nth (Z.to_nat i)
      [AP.getr R' 1%bv; AP.getr R' 5%bv; AP.getr R' 6%bv; AP.getr R' 7%bv;
       AP.getr R' 11%bv; AP.getr R' 12%bv; AP.getr R' 13%bv; AP.getr R' 14%bv;
       AP.getr R' 15%bv; AP.getr R' 16%bv; AP.getr R' 17%bv;
       AP.getr R' 28%bv; AP.getr R' 29%bv; AP.getr R' 30%bv; AP.getr R' 31%bv; A; S] (Z_to_bv 64 0).
Lemma cfvA_clob : forall R' A S x i, clob_pos x = Some i -> cfvA R' A S (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Proof. intros R' A S x i H. destruct x; cbn in H; try discriminate; injection H as <-; cbn; f_equal; apply bv_eq; reflexivity. Qed.

Definition cfvT (R' : bvmap 5 word) (A S T : word) (i : Z) : word :=
  nth (Z.to_nat i)
      [AP.getr R' 1%bv; AP.getr R' 5%bv; AP.getr R' 6%bv; AP.getr R' 7%bv;
       AP.getr R' 11%bv; AP.getr R' 12%bv; AP.getr R' 13%bv; AP.getr R' 14%bv;
       AP.getr R' 15%bv; AP.getr R' 16%bv; AP.getr R' 17%bv;
       AP.getr R' 28%bv; AP.getr R' 29%bv; AP.getr R' 30%bv; AP.getr R' 31%bv; A; S; T] (Z_to_bv 64 0).
Lemma cfvT_clob : forall R' A S T x i, clob_pos x = Some i -> cfvT R' A S T (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Proof. intros R' A S T x i H. destruct x; cbn in H; try discriminate; injection H as <-; cbn; f_equal; apply bv_eq; reflexivity. Qed.

Lemma amalloc_post_okA : forall st sts E ms mo (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (n : Z)
    rr RNG' msP mo',
  st_ok bsegs OPS E st ms mo -> amalloc_apply UNIV AMALLOC_PC st = Some sts ->
  CtrPre.TwinB.acall_facts AI ACCT UNIV Cw X10 E st ms mo L RNG sta LBa aw n ->
  let R := ms_regs ms in
  amalloc_post2 (aci AI) (AHEAP AI) L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa n (CtrPre.TwinB.sp_lo E st) (ms_mem ms) rr RNG' msP ->
  (forall Aaddr, match snd rr with
                 | Some p => ACCT (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X10) then 0 else n))) L RNG' (fst rr) (HB p Aaddr n :: LBa) mo'
                 | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst rr) LBa mo'
                 end) ->
  (CtrPre.TwinB.prist_in E st -> aprist (fst rr)) ->
  op_minv OPS mo' -> OTHER mo mo' ->
  exists stB E1, In stB (tl sts) /\ env_ext (s_next st) E E1 /\ st_ok bsegs OPS E1 stB msP mo'.
Proof.
  intros st sts E ms mo L RNG sta LBa aw n rr RNG' msP mo' HS Happ CF R HQ ACP PRSX MINVo OTH.
  destruct CF as (LB & r & hargs & st1 & ks & offs & rss & ksp & wnl & nn & md & A & nw & rest
                  & CP & FS & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255 & NW & AJ & WF & HC & AWden & (W & WOF & AR & TI) & NDEN & SHAPE).
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (PRS0 : In prist_win (wins_of E nn rest) -> aprist (fst rr)).
  { intros IP. apply PRSX. exists hargs, md, A, nw, rest. rewrite <- Nn. auto. }

  destruct HQ as (FPLE & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV' & STK' & PRES & TWP & POSTB).
  destruct (snd rr) as [p|] eqn:SR; [| contradiction].
  destruct POSTB as (Ablk & junk & EA0 & BRN & AH' & RW & _ & _ & _ & PATN).
  specialize (ACP Ablk). cbv beta iota in ACP.
  set (R' := mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) t0 t1 t2 (AP.getr R 8) (AP.getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) t3 t4 t5 t6) in *.
  set (Fv := cfvT R' (Z_to_bv 64 Ablk) (Z_to_bv 64 (shad Ablk)) (Z_to_bv 64 (shad Ablk + (n - 1) / 8))).
  set (Gv := fun (_ : Z) (o : Z) => match m' (ALib.Mem.wa (Ablk + o)) with Some b => b | None => Z_to_bv 8 0 end).

  destruct (amalloc_apply_shape UNIV AMALLOC_PC st sts Happ) as (r2 & hargs2 & cred2 & st12 & h1 & h2 & h3x & stN & CP2 & Hf2 & HA2 & FS2 & S1 & S2 & S3 & NPOST & SHP).
  rewrite CP in CP2. injection CP2 as <-. rewrite Hf in Hf2. injection Hf2 as <-. rewrite FS in FS2. injection FS2 as <-.
  rewrite Eh, heap_A_eq in HA2. injection HA2 as <-.
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.TwinB.den_wlit. }
  assert (EMS' : msP = ms' ms r R' m').
  { rewrite EMS. unfold ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  rewrite EMS'.

  destruct (h3_shape E st ms Fv Gv ksp nn rest X10 hargs md A nw Hc Eh Tnw Nn Ln N255 (prim_decided (s_facts st) (getr st X10))) as (Q1 & Q2 & Q3).
  assert (KBE : s_next (clobber st1) = kB st) by (eapply kB_next; eassumption).
  assert (KSE : PrimInt63.add (kB st) 1%uint63 = kS st) by (eapply kS_next; eassumption).
  unfold cred', nsv in Q1, Q2, Q3.
  unfold cred_post in S1. assert (E1 : h1 = VL md :: (if prim_decided (s_facts st) (getr st X10) then A else sv_alu ALU_SUB A (getr st X10)) :: VL nw :: rest) by congruence. subst h1.
  rewrite KBE in S2. assert (E2 : h2 = VL md :: (if prim_decided (s_facts st) (getr st X10) then A else sv_alu ALU_SUB A (getr st X10)) :: VL (nwB nw) :: restB st nn rest X10) by congruence. subst h2.
  rewrite KBE, KSE in S3. assert (E3 : h3x = h3 st nn rest X10 md A nw (prim_decided (s_facts st) (getr st X10))) by congruence. subst h3x.
  destruct (NEWB m' L RNG' (fst rr) LBa p Ablk n AH') as (NN & BRN' & WRN).
  assert (AWH' : aw_holds_asan AI ACCT UNIV (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X10) then 0 else n))) (LB' LB Ablk n) m' mo').
  { eapply (WORLD'_asan ms mo m'); eassumption. }
  assert (ALL : forall TWR, (TWR = twin_region (getr st X10) /\ match getr st X10 with VL _ => True | _ => n mod 8 = 0 end) \/ TWR = twin_main (getr st X10) ->
            st_ok bsegs OPS (E' E st Fv Gv) (alloc_stB_g TWR X10 st st1 r (h3 st nn rest X10 md A nw (prim_decided (s_facts st) (getr st X10))) A) (ms' ms r R' m') mo'
            /\ (TWR = twin_main (getr st X10) -> Fv 17 = Z_to_bv 64 (shad Ablk + (n - 1) / 8) ->
                st_ok bsegs OPS (E' E st Fv Gv) (alloc_stBb X10 st st1 r (h3 st nn rest X10 md A nw (prim_decided (s_facts st) (getr st X10))) A) (ms' ms r R' m') mo')).
  { intros TWR TWSH.
  apply (post_all E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo') with (aw := aw) (LB := LB) (L := L) (RNG := RNG) (RNG' := RNG') (sta := sta)
       (sta' := fst rr) (LBa := LBa) (WW := W) (p := p) (Ablk := Ablk) (N := n) (XN := X10) (ks := ks) (offs := offs) (rss := rss) (ksp := ksp) (wnl := wnl)
       (aw' := Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X10) then 0 else n))) (hargs := hargs) (pd := prim_decided (s_facts st) (getr st X10)); try assumption.
  -   intros rg Hrg. unfold kept_regsA in Hrg. cbn [In] in Hrg.
    repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
  -   intros x i Hx. exact (cfvT_clob R' _ _ _ x i Hx).
  -   intros wlo SW. exact (CallV.TwinB.wlo_floor E st hargs nn md A nw rest LB (ATOP + 4096) wlo Hf Eh Tnw Nn Ln WF SW).
  -   reflexivity.
  -   reflexivity.
  -   intros o Ho. unfold Gv, rb.
    destruct (aw_user_ok_asan AI ACCT UNIV AI_fake _ _ m' mo' (Ablk, n) (Ablk + o) AWH' ltac:(right; left; reflexivity) ltac:(unfold in_iv; cbn [fst snd]; lia)) as [MP _].
    unfold ALib.Mem.wa. destruct (m' (Z_to_bv 64 (Ablk + o))); [reflexivity| contradiction].
  -   reflexivity.
  -
    destruct (CtrPre.TwinB.amalloc_apply_inv UNIV st _ Happ) as (r9 & tp9 & hargs9 & cred9 & st19 & _ & _ & FO9 & HA9 & _ & _ & _ & _ & _ & _ & _ & _ & NC9 & _).
    rewrite Hf in FO9. injection FO9 as <-. rewrite Eh, heap_A_eq in HA9. injection HA9 as <-.
    pose proof (so_facts _ _ _ _ _ _ HS) as HF9. unfold f_cred, cred_fact, cred_pre, nsv in *. apply andb_prop in NC9 as [NX9 NC9].
    destruct (prim_decided (s_facts st) (getr st X10)); cbn [fact_holds].
    + exact (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF9 NX9).
    + cbn [orb] in NC9. exact (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF9 NC9). }

  pose proof (so_facts _ _ _ _ _ _ HS) as HFx.
  assert (SHSEM : size_shape_ok (s_facts st) (getr st X10) = true -> match getr st X10 with VL _ => True | _ => n mod 8 = 0 end).
  { intros SS. pose proof (CallA.TwinB.size_shape_sound E _ (getr st X10) HFx SS) as X. rewrite NDEN in X. exact X. }
  assert (Z8SEM : n mod 8 = 0 -> match getr st X10 with VL _ => True | _ => n mod 8 = 0 end) by (intros Z8; destruct (getr st X10); try exact I; exact Z8).
  destruct SHP as [[SS ->]|(SS & ->)].
  - exists (amalloc_stB st st1 r (h3 st nn rest X10 md A nw (prim_decided (s_facts st) (getr st X10))) A), (E' E st Fv Gv).
    split; [left; reflexivity|]. split; [apply EXT|]. exact (proj1 (ALL _ (or_introl (conj eq_refl (SHSEM SS))))).
  -
    exists (alloc_stBb X10 st st1 r (h3 st nn rest X10 md A nw (prim_decided (s_facts st) (getr st X10))) A), (E' E st Fv Gv).
    split; [left; reflexivity|]. split; [apply EXT|]. exact (proj2 (ALL _ (or_intror eq_refl)) eq_refl eq_refl).
Qed.

Lemma aaligned_post_okA : forall st sts E ms mo (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) (n : Z)
    rr RNG' msP mo',
  st_ok bsegs OPS E st ms mo -> aaligned_apply UNIV F_aaligned_iseg.TwinB.AALIGNED_PC st = Some sts ->
  CtrPre.TwinB.acall_facts AI ACCT UNIV Cw X11 E st ms mo L RNG sta LBa aw n ->
  let R := ms_regs ms in
  amalloc_post2 (aci AI) (AHEAP AI) L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa n (CtrPre.TwinB.sp_lo E st) (ms_mem ms) rr RNG' msP ->
  (forall Aaddr, match snd rr with
                 | Some p => ACCT (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) L RNG' (fst rr) (HB p Aaddr n :: LBa) mo'
                 | None => ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' (fst rr) LBa mo'
                 end) ->
  ~ CtrPre.TwinB.prist_in E st ->
  op_minv OPS mo' -> OTHER mo mo' ->
  exists stN stB E1, sts = [stN; stB] /\ env_ext (s_next st) E E1 /\ st_ok bsegs OPS E1 stB msP mo'.
Proof.
  intros st sts E ms mo L RNG sta LBa aw n rr RNG' msP mo' HS Happ CF R HQ ACP PRSX MINVo OTH.
  destruct CF as (LB & r & hargs & st1 & ks & offs & rss & ksp & wnl & nn & md & A & nw & rest
                  & CP & FS & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255 & NW & AJ & WF & HC & AWden & (W & WOF & AR & TI) & NDEN & SHAPE).
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (PRS0 : In prist_win (wins_of E nn rest) -> aprist (fst rr)).
  { intros IP. exfalso. apply PRSX. exists hargs, md, A, nw, rest. rewrite <- Nn. auto. }

  destruct HQ as (FPLE & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV' & STK' & PRES & TWP & POSTB).
  destruct (snd rr) as [p|] eqn:SR; [| contradiction].
  destruct POSTB as (Ablk & junk & EA0 & BRN & AH' & RW & _ & _ & _ & PATN).
  specialize (ACP Ablk). cbv beta iota in ACP.
  set (R' := mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) t0 t1 t2 (AP.getr R 8) (AP.getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) t3 t4 t5 t6) in *.
  set (Fv := cfvA R' (Z_to_bv 64 Ablk) (Z_to_bv 64 (shad Ablk))).
  set (Gv := fun (_ : Z) (o : Z) => match m' (ALib.Mem.wa (Ablk + o)) with Some b => b | None => Z_to_bv 8 0 end).

  destruct (aaligned_apply_shape UNIV F_aaligned_iseg.TwinB.AALIGNED_PC st sts Happ) as (r2 & hargs2 & cred2 & st12 & h1 & h2 & h3x & stN & CP2 & Hf2 & HA2 & FS2 & S1 & S2 & S3 & NPOST & ->).
  rewrite CP in CP2. injection CP2 as <-. rewrite Hf in Hf2. injection Hf2 as <-. rewrite FS in FS2. injection FS2 as <-.
  rewrite Eh, heap_A_eq in HA2. injection HA2 as <-.
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.TwinB.den_wlit. }
  assert (EMS' : msP = ms' ms r R' m').
  { rewrite EMS. unfold ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  exists stN. eexists. exists (E' E st Fv Gv). split; [reflexivity|]. split; [apply EXT|]. rewrite EMS'.

  destruct (h3_shape E st ms Fv Gv ksp nn rest X11 hargs md A nw Hc Eh Tnw Nn Ln N255 (prim_decided (s_facts st) (getr st X11))) as (Q1 & Q2 & Q3).
  assert (KBE : s_next (clobber st1) = kB st) by (eapply kB_next; eassumption).
  assert (KSE : PrimInt63.add (kB st) 1%uint63 = kS st) by (eapply kS_next; eassumption).
  unfold cred', nsv in Q1, Q2, Q3.
  unfold cred_post in S1. assert (E1 : h1 = VL md :: (if prim_decided (s_facts st) (getr st X11) then A else sv_alu ALU_SUB A (getr st X11)) :: VL nw :: rest) by congruence. subst h1.
  rewrite KBE in S2. assert (E2 : h2 = VL md :: (if prim_decided (s_facts st) (getr st X11) then A else sv_alu ALU_SUB A (getr st X11)) :: VL (nwB nw) :: restB st nn rest X11) by congruence. subst h2.
  rewrite KBE, KSE in S3. assert (E3 : h3x = h3 st nn rest X11 md A nw (prim_decided (s_facts st) (getr st X11))) by congruence. subst h3x.
  destruct (NEWB m' L RNG' (fst rr) LBa p Ablk n AH') as (NN & BRN' & WRN).
  assert (AWH' : aw_holds_asan AI ACCT UNIV (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) (LB' LB Ablk n) m' mo').
  { eapply (WORLD'_asan ms mo m'); eassumption. }
  assert (TWSH : (twin_region (getr st X11) = twin_region (nsv st X11) /\ match nsv st X11 with VL _ => True | _ => n mod 8 = 0 end) \/ twin_region (getr st X11) = twin_main (nsv st X11)).
  { left. split; [reflexivity|]. destruct (SHAPE eq_refl) as [wl0 EW]. unfold nsv. rewrite EW. exact I. }
  change (alloc_stB X11 st st1 r (h3 st nn rest X11 md A nw (prim_decided (s_facts st) (getr st X11))) A)
    with (alloc_stB_g (twin_region (getr st X11)) X11 st st1 r (h3 st nn rest X11 md A nw (prim_decided (s_facts st) (getr st X11))) A).
  apply (post_B E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo') with (aw := aw) (LB := LB) (L := L) (RNG := RNG) (RNG' := RNG') (sta := sta)
       (sta' := fst rr) (LBa := LBa) (WW := W) (p := p) (Ablk := Ablk) (N := n) (XN := X11) (ks := ks) (offs := offs) (rss := rss) (ksp := ksp) (wnl := wnl)
       (aw' := Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) (hargs := hargs) (pd := prim_decided (s_facts st) (getr st X11))
       (TWR := twin_region (getr st X11)); try assumption.
  -   intros rg Hrg. unfold kept_regsA in Hrg. cbn [In] in Hrg.
    repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
  -   intros x i Hx. exact (cfvA_clob R' _ _ x i Hx).
  -   intros wlo SW. exact (CallV.TwinB.wlo_floor E st hargs nn md A nw rest LB (ATOP + 4096) wlo Hf Eh Tnw Nn Ln WF SW).
  -   reflexivity.
  -   reflexivity.
  -   intros o Ho. unfold Gv, rb.
    destruct (aw_user_ok_asan AI ACCT UNIV AI_fake _ _ m' mo' (Ablk, n) (Ablk + o) AWH' ltac:(right; left; reflexivity) ltac:(unfold in_iv; cbn [fst snd]; lia)) as [MP _].
    unfold ALib.Mem.wa. destruct (m' (Z_to_bv 64 (Ablk + o))); [reflexivity| contradiction].
  -   reflexivity.
  -
    destruct (CtrPre.TwinB.aaligned_apply_inv UNIV st _ Happ) as (r9 & tp9 & hargs9 & cred9 & st19 & al9 & _ & _ & FO9 & HA9 & _ & _ & _ & _ & _ & _ & _ & _ & _ & NC9 & _).
    rewrite Hf in FO9. injection FO9 as <-. rewrite Eh, heap_A_eq in HA9. injection HA9 as <-.
    pose proof (so_facts _ _ _ _ _ _ HS) as HF9. unfold f_cred, cred_fact, cred_pre, nsv in *. apply andb_prop in NC9 as [NX9 NC9].
    destruct (prim_decided (s_facts st) (getr st X11)); cbn [fact_holds].
    + exact (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF9 NX9).
    + cbn [orb] in NC9. exact (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF9 NC9).
Qed.

End Post.
End TwinB.
