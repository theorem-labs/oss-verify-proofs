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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto AMalloc_iface AMalloc_iface2 ARealloc_x.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AInstanceU2F.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV CtrPre GlueA FrameV CtrFrame CtrPost CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require KnownA.
Unset Nia Cache. Unset Nra Cache.

Definition arealloc_stB (st st1 : sstate) (r : int) (h5 : list sv) (kf sh : int) (cred : sv) : sstate :=
  let n := getr st X11 in
  let st2 := clobber st1 in
  let k := s_next st2 in
  let sh' := PrimInt63.add k 1%uint63 in
  let st4 := set_next (set_next st2 (PrimInt63.add k 1%uint63)) (PrimInt63.add sh' 1%uint63) in
  let R' := IMap.add sh' (twin_region n) (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty) (IMap.remove sh (IMap.remove kf (s_regs st4)))) in
  let st5 := set_ops (setregs st4 R') (set_op HEAP_ID h5 (s_ops st4)) in
  let st6 := addfact (addfact (addfact (addfact st5 (cred_fact (s_facts st) n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
               (FEq (VP sh' wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw))) in
  let st7 := addfacts st6 (and7_facts n) in
  setpc (setr st7 X10 (VP k wzero)) r.

Lemma arealloc_apply_shape : forall UNIV PCz st sts, arealloc_apply UNIV PCz st = Some sts ->
  exists r hargs wnl st1 kf sh cred h1 h2 h3 h4 h5 stN,
    acall_pre AREALLOC_ROOM (Some (UNIV, PCz)) st = Some (r, hargs, wnl, st1) /\ getr st X10 = VP kf wzero
    /\ find_twin (s_facts st) kf = Some sh /\ heap_A hargs = Some cred
    /\ afree_ok st wnl kf sh = true /\ no_views_on (s_facts st) (s_regs st) kf sh = true /\ twin_canon st wnl kf sh = true
    /\ KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (getr st X11) = true /\ reqmax_ok (s_facts st) (getr st X11) = true
    /\ size_shape_ok (s_facts st) (getr st X11) = true /\ cred_pre (s_facts st) (getr st X11) cred = true
    /\ prist_absent (s_facts st) hargs = true
    /\ heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK = Some h1 /\ heap_del_window_k h1 (VP sh wzero) K_TWIN = Some h2
    /\ heap_set_A h2 (cred_post (s_facts st) (getr st X11) cred) = Some h3
    /\ heap_add_window h3 (VP (s_next (clobber st1)) wzero) (getr st X11) (VL CtrLib.K_BLOCK) = Some h4
    /\ heap_add_window h4 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X11)) (VL K_TWIN) = Some h5
    /\ null_post hargs cred (clobber st1) r = Some stN
    /\ sts = [stN; arealloc_stB st st1 r h5 kf sh cred].
Proof.
  intros UNIV PCz st sts H. unfold arealloc_apply in H.
  destruct (acall_pre AREALLOC_ROOM (Some (UNIV, PCz)) st) as [[[[r hargs] wnl] st1]|] eqn:PRE; [|discriminate].
  destruct (getr st X10) as [|kf off| | | | | | | | |] eqn:X10E; try discriminate.
  destruct (find_twin (s_facts st) kf) as [sh|] eqn:FT; [|discriminate].
  destruct (heap_A hargs) as [cred|] eqn:HA; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  apply andb_prop in CK as [CK PRA]. apply andb_prop in CK as [CK NC]. apply andb_prop in CK as [CK SS]. apply andb_prop in CK as [CK N1]. apply andb_prop in CK as [CK N0].
  apply andb_prop in CK as [CK NV]. apply andb_prop in CK as [CK TC]. apply andb_prop in CK as [OFF FOK]. apply weqb_eq in OFF. subst off.
  destruct (null_post hargs cred (clobber st1) r) as [stN|] eqn:NP; [|discriminate].
  destruct (heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK) as [h1|] eqn:H1; [|discriminate].
  destruct (heap_del_window_k h1 (VP sh wzero) K_TWIN) as [h2|] eqn:H2; [|discriminate].
  unfold fresh in H. cbv zeta in H. cbn [fst snd s_next set_next] in H.
  destruct (heap_set_A h2 (cred_post (s_facts st) (getr st X11) cred)) as [h3|] eqn:H3; [|discriminate].
  destruct (heap_add_window h3 (VP (s_next (clobber st1)) wzero) (getr st X11) (VL CtrLib.K_BLOCK)) as [h4|] eqn:H4; [|discriminate].
  destruct (heap_add_window h4 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X11)) (VL K_TWIN)) as [h5|] eqn:H5; [|discriminate].
  injection H as <-.
  exists r, hargs, wnl, st1, kf, sh, cred, h1, h2, h3, h4, h5, stN. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Section Realloc.
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
Hypothesis Cw_ghost_free : forall md ca LB ws m b n ws', cw_holds Cw md ca LB ws m -> In (Win b n K_TWINz) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n K_TWINz) -> cw_holds Cw md ca (remove iv_eq_dec (b, n) LB) ws' m.

Hypothesis Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds Cw md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.

Hypothesis Cw_vec_unowned : forall md ca LB ws m i a, cw_holds Cw md ca LB ws m -> In i (VECS md) -> nth_error ca i = Some a -> bv_unsigned a <> 0 ->
  forall w, In w ws -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned a.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.

Lemma afree_ok_k_inv : forall (kdB kdT : w64) E st ms mo wnl kf sh, st_ok asegs OPS E st ms mo -> afree_ok_k kdB kdT st wnl kf sh = true ->
  exists rf lenf lent,
  IMap.find kf (s_regs st) = Some rf /\ CtrA.win_lookup wnl kf = Some (lenf, kdB) /\ CtrA.win_lookup wnl sh = Some (lent, kdT)
  /\ block_of_twin (s_facts st) sh = Some kf /\ rg_lo rf = 0%uint63
  /\ 0 < hiZ E rf /\ hiZ E rf <= bv_unsigned (den E lenf)
  /\ forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
       (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
       \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len)
             /\ 0 < hiZ E r0 /\ rg_w r0 = true /\ (kd = kdB \/ hiZ E rf = bv_unsigned (den E lenf))).
Proof.
  intros kdB kdT E st ms mo wnl kf sh HS FOKk.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF. unfold afree_ok_k in FOKk. cbv zeta in FOKk.
  destruct (IMap.find kf (s_regs st)) as [rf|] eqn:Frf; [|discriminate].
  destruct (CtrA.win_lookup wnl kf) as [[lenf kdf]|] eqn:WLf; [|discriminate].
  destruct (CtrA.win_lookup wnl sh) as [[lent kdt]|] eqn:WLt; [|discriminate].
  destruct (block_of_twin (s_facts st) sh) as [kb|] eqn:BT; [|discriminate].
  do 6 (apply andb_prop in FOKk as [FOKk ?]).
  rename H into ALL, H0 into LEQ, H1 into POS, H2 into LO0, H3 into KBE, H4 into KDT.
  apply weqb_eq in FOKk. subst kdf. apply weqb_eq in KDT. subst kdt. apply Uint63.eqb_correct in KBE. subst kb. apply Uint63.eqb_correct in LO0.
  pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF POS) as POS'. cbn [den] in POS'. rewrite wbv_unsigned, wzero_ok in POS'.
  pose proof (KnownA.KnownA.known_leu_q_sound E _ _ _ HF LEQ) as LEQ'.
  exists rf, lenf, lent. repeat (split; [reflexivity || assumption|]).
  intros k len kd Hin NKf NKs. pose proof (proj1 (forallb_forall _ _) ALL _ Hin) as X. cbv beta iota in X.
  apply Uint63.eqb_false_spec in NKf, NKs. rewrite NKf, NKs in X. cbn [orb] in X.
  destruct (weqb kd K_TWIN) eqn:KT.
  - left. split; [reflexivity|]. destruct (block_of_twin (s_facts st) k) as [kb|]; [|discriminate]. exists kb. split; [reflexivity|].
    apply negb_true_iff in X. apply Uint63.eqb_false_spec in X. exact X.
  - right. split; [reflexivity|].
    destruct (IMap.find k (s_regs st)) as [r0|] eqn:Fr0; [|discriminate]. exists r0. split; [reflexivity|].
    apply andb_prop in X as [X KB]. apply andb_prop in X as [X W]. apply andb_prop in X as [X P0]. apply andb_prop in X as [L0 LE0]. apply Uint63.eqb_correct in L0.
    pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF P0) as P0'. cbn [den] in P0'. rewrite wbv_unsigned, wzero_ok in P0'.
    split; [exact L0|]. split; [exact (KnownA.KnownA.known_leu_q_sound E _ _ _ HF LE0)|]. split; [exact P0'|]. split; [exact W|].
    apply orb_prop in KB as [KB|FULL]; [left; apply weqb_eq; exact KB| right].
    pose proof (KnownA.KnownA.known_eq_sound E _ _ _ HF FULL) as EQ. unfold hiZ. rewrite EQ. reflexivity.
Qed.

Section REALLOCD.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok asegs OPS E st ms mo.
Variables (wnl : list (int * sv * w64)) (nn : nat) (rest : list sv) (LB : blocks) (aw : word)
          (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock).
Hypothesis NW : CtrA.nonstack_windows nn rest = Some wnl.
Hypothesis AN : CtrA.windows_anchored (s_regs st) wnl = true.
Hypothesis WF : windows_wf (wins_of E nn rest) LB (ATOP + 4096).

Variable WW : wit.
Hypothesis WOF : wit_of WW L RNG sta LBa.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis TI : ties WW (wins_of E nn rest).
Hypothesis NOPR : ~ In prist_win (wins_of E nn rest).

Hypothesis CVU : forall kb, In kb (carg_vecs st) -> bv_unsigned (ev E kb) <> 0 -> forall w, In w (wins_of E nn rest) -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned (ev E kb).
Variables (kf sh : int).
Hypothesis FT : find_twin (s_facts st) kf = Some sh.
Hypothesis FOKk : afree_ok st wnl kf sh = true.
Hypothesis NV : no_views_on (s_facts st) (s_regs st) kf sh = true.
Hypothesis TCAN : twin_canon st wnl kf sh = true.

Lemma afree_ok_inv : exists rf lenf lent,
  IMap.find kf (s_regs st) = Some rf /\ CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK) /\ CtrA.win_lookup wnl sh = Some (lent, K_TWIN)
  /\ block_of_twin (s_facts st) sh = Some kf /\ rg_lo rf = 0%uint63
  /\ 0 < hiZ E rf /\ hiZ E rf <= bv_unsigned (den E lenf)
  /\ forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
       (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
       \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len)
             /\ 0 < hiZ E r0 /\ rg_w r0 = true /\ (kd = CtrLib.K_BLOCK \/ hiZ E rf = bv_unsigned (den E lenf))).
Proof. exact (afree_ok_k_inv CtrLib.K_BLOCK K_TWIN E st ms mo wnl kf sh HS FOKk). Qed.

Variables (rf : region) (lenf lent : sv).
Hypothesis Frf : IMap.find kf (s_regs st) = Some rf.
Hypothesis WLf : CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK).
Hypothesis WLt : CtrA.win_lookup wnl sh = Some (lent, K_TWIN).
Hypothesis BTs : block_of_twin (s_facts st) sh = Some kf.
Hypothesis LO0 : rg_lo rf = 0%uint63.
Hypothesis POSf : 0 < hiZ E rf.
Hypothesis LEf : hiZ E rf <= bv_unsigned (den E lenf).
Hypothesis OTHERS : forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
  \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len)
        /\ 0 < hiZ E r0 /\ rg_w r0 = true /\ (kd = CtrLib.K_BLOCK \/ hiZ E rf = bv_unsigned (den E lenf))).

Let Af : Z := bv_unsigned (ev E kf).
Let nf : Z := bv_unsigned (den E lenf).

Lemma AWHf : aw_holds_asan AI ACCT UNIV aw LB (ms_mem ms) mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.

Lemma KB1 : w2Z CtrLib.K_BLOCK = 1. Proof. reflexivity. Qed.
Lemma KT9 : w2Z K_TWIN = 9. Proof. reflexivity. Qed.

Lemma entry_window : forall k len kd, In (k, len, kd) wnl ->
  k <> 0%uint63 /\ In (Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z kd)) (wins_of E nn rest)
  /\ exists b, In b LB /\ (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a)
       /\ (kd = CtrLib.K_BLOCK -> b = (bv_unsigned (ev E k), bv_unsigned (den E len))).
Proof.
  intros k len kd Hin. destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k len kd NW Hin) as (K0 & _ & KD & INW).
  split; [exact K0|]. split; [exact INW|].
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
  - exfalso. exact (KD KS0).
  - eexists. split; [exact B|]. split; [intros a Ha; exact Ha| reflexivity].
  - exists b. split; [exact Hb|]. split; [exact SUB|]. intros ->. rewrite KB1 in KS2. unfold K_SUB in KS2. lia.
Qed.

Lemma blockLB : In (Af, nf) LB.
Proof.
  destruct (entry_window kf lenf CtrLib.K_BLOCK (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as (_ & _ & b & Hb & _ & EQ). rewrite (EQ eq_refl) in Hb. exact Hb.
Qed.

Lemma nf_small : 0 <= Af /\ 1 <= nf /\ Af + nf < 2 ^ 48.
Proof.
  destruct (aw_blocks_ok_asan AI IMGX IMGX_aci ACCT UNIV AI_fake aw LB (ms_mem ms) mo (Af, nf) AWHf blockLB) as (B1 & B2 & B3 & _). cbn [fst snd] in *.
  unfold aw_ceiling_asan in B3. pose proof atop_range. unfold hiZ in *. fold nf in LEf. lia.
Qed.

Lemma twin_sh : exists rs, IMap.find sh (s_regs st) = Some rs /\ is_twin_region rs lenf = true /\ len_is_twin (s_facts st) lent lenf = true
  /\ bv_unsigned (ev E sh) = shad Af /\ bv_unsigned (den E lent) = shlen (nf + 7).
Proof.

  destruct (CallA.twin_canon_inv st wnl kf sh TCAN) as (rs & n0 & kdn & lent0 & kdt & FR & WLn & WLt0 & TR & _ & LEN & _).
  rewrite WLf in WLn. injection WLn as <- <-. rewrite WLt in WLt0. injection WLt0 as <- <-.
  exists rs. split; [exact FR|]. split; [exact TR|]. split; [exact LEN|].
  destruct nf_small as (A0 & N1 & SM).
  split.
  - rewrite (CallA.block_of_twin_sound E _ sh kf (so_facts _ _ _ _ _ _ HS) BTs). fold Af. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. clear - A0 SM N1. Z.div_mod_to_equations. lia.
  - rewrite (CallA.len_is_twin_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) LEN) by (fold nf; lia). fold nf. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma owner : user_band Af /\ In (shad Af, shlen (nf + 7)) LB /\ (exists p, In (HB p Af nf) LBa /\ In (HB p Af nf) (w_T WW))
  /\ 1 <= nf <= AREQMAX /\ Af mod 16 = 0.
Proof.
  destruct twin_sh as (rs & _ & _ & _ & ESH & ELT).
  destruct (entry_window sh lent K_TWIN (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as (_ & INW & _). rewrite ESH, ELT, KT9 in INW.

  destruct TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as ESA ESL.
  destruct AR as [HWw EMw]. destruct WOF as (_ & _ & _ & ELB).
  destruct (twin_owner_w AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b Af nf HWw HbT blockLB ESA) as (EA & EN & NR).
  destruct (twin_T_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b HWw HbT) as (HbL & _ & _ & HTW & (p & EB) & _ & AL & UB & _).
  unfold twin_iv in HTW. rewrite <- EA, <- EN in HTW. rewrite <- EA in AL, UB. rewrite <- EN in NR. rewrite <- EA, <- EN in EB.
  split; [exact UB|]. split; [exact HTW|]. split; [| split; [exact NR| exact AL]].
  exists p. rewrite <- EB. split; [rewrite <- ELB; exact HbL| exact HbT].
Qed.

Lemma freed_pattern : ablock_shadow (ms_mem ms) Af nf.
Proof.
  destruct twin_sh as (rs & Frs & TRs & _ & ESH & _). destruct owner as (UBf & HTf & (p0 & HPL & HPT) & NRf & ALf).
  assert (SS : size_shape_ok (s_facts st) lenf = true).
  { destruct (CallA.twin_canon_inv st wnl kf sh TCAN) as (rs0 & n0 & kdn & lent0 & kdt & _ & WLn & _ & _ & SS0 & _). rewrite WLf in WLn. injection WLn as <- <-. exact SS0. }
  pose proof (so_reg _ _ _ _ _ _ HS sh rs Frs) as RO.
  destruct (entry_window sh lent K_TWIN (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as (SH0 & _).
  assert (SHNZ : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact SH0).
  pose proof (CallA.size_shape_sound E _ lenf (so_facts _ _ _ _ _ _ HS) SS) as SHAPE.
  pose proof (CallA.is_twin_region_sound asegs (s_priv st) E (ms_mem ms) sh rs lenf RO SHNZ TRs) as PATR. fold nf in PATR. rewrite ESH in PATR.
  intros g G0 G1.
  assert (P1 : rb asegs (ms_mem ms) (shad Af + g) = Some (Z_to_bv 8 (if 8 * g + 8 <=? nf then 0 else nf - 8 * g))).
  { apply PATR; [unfold AREQMAX in NRf; lia| | exact G0| exact G1]. destruct lenf; try exact I; exact SHAPE. }

  destruct AR as [HWw _]. pose proof HWw as (_ & _ & _ & _ & _ & _ & _ & MAP & _).
  assert (MP : ms_mem ms (ALib.Mem.wa (shad Af + g)) <> None).
  { apply MAP. apply in_ivs_In. exists (twin_iv (HB p0 Af nf)). split; [apply in_map; exact HPT|].
    unfold in_iv, twin_iv. cbn [fst snd ab_addr ab_size]. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear -G0 G1. Z.div_mod_to_equations. lia. }
  unfold rb in P1. unfold ALib.Mem.wa in *. destruct (ms_mem ms (Z_to_bv 64 (shad Af + g))) as [y|]; [exact P1| contradiction].
Qed.

Lemma region_first_byte : forall k r0, IMap.find k (s_regs st) = Some r0 -> rg_lo r0 = 0%uint63 -> 0 < hiZ E r0 ->
  bv_unsigned (ev E k) + loZ r0 <= bv_unsigned (ev E k) < bv_unsigned (ev E k) + hiZ E r0.
Proof. intros k r0 _ L0 P. unfold loZ. rewrite L0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. lia. Qed.

Lemma kept_block_w : forall k len kd r0 b, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  IMap.find k (s_regs st) = Some r0 -> rg_lo r0 = 0%uint63 -> hiZ E r0 <= bv_unsigned (den E len) -> 0 < hiZ E r0 -> rg_w r0 = true ->
  (kd = CtrLib.K_BLOCK \/ hiZ E rf = nf) ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
  b <> (Af, nf) /\ b <> (shad Af, shlen (nf + 7)).
Proof.
  intros k len kd r0 b Hin NKf NKs Fr0 L0 LE0 P0 W0 CASE Hb SUB.
  destruct (entry_window k len kd Hin) as (K0 & _ & b1 & Hb1 & SUB1 & EQ1).
  destruct (entry_window kf lenf CtrLib.K_BLOCK (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as (Kf0 & _).
  destruct (entry_window sh lent K_TWIN (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as (Ks0 & _).
  assert (ZK : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  assert (ZF : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kf0).
  assert (ZS : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ks0).
  assert (A0IN : in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) (bv_unsigned (ev E k))) by (unfold in_iv; cbn [fst snd]; lia).
  pose proof (SUB _ A0IN) as INB. pose proof (region_first_byte k r0 Fr0 L0 P0) as RK.
  split; intros ->.
  -
    unfold in_iv in INB. cbn [fst snd] in INB.
    assert (INF : bv_unsigned (ev E kf) + loZ rf <= bv_unsigned (ev E k) < bv_unsigned (ev E kf) + hiZ E rf).
    { unfold loZ. rewrite LO0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. fold Af. destruct CASE as [->|FULL]; [| lia].

      pose proof (EQ1 eq_refl) as E1. subst b1.
      destruct (Z.eq_dec (bv_unsigned (ev E k)) Af) as [EA|NA]; [lia| exfalso].
      apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ (Af, nf) (bv_unsigned (ev E k)) AWHf Hb1 blockLB); [cbn [fst]; exact NA| exact A0IN|].
      unfold in_iv. cbn [fst snd]. lia. }
    exact (so_disj _ _ _ _ _ _ HS k r0 kf rf Fr0 Frf NKf ZK ZF (or_introl W0) _ (conj RK INF)).
  -
    destruct twin_sh as (rs & Frs & TRs & _ & ESH & _). unfold in_iv in INB. cbn [fst snd] in INB.
    unfold is_twin_region in TRs. cbv zeta in TRs. do 4 (apply andb_prop in TRs as [TRs ?]).
    apply Uint63.eqb_correct in TRs. match goal with X : sv_eqb (rg_hi rs) _ = true |- _ => apply sv_eqb_eq in X; rewrite CallA.twin_region_hi in X; rename X into HIs end.
    destruct nf_small as (A0 & N1 & SM).
    assert (INS : bv_unsigned (ev E sh) + loZ rs <= bv_unsigned (ev E k) < bv_unsigned (ev E sh) + hiZ E rs).
    { unfold loZ, hiZ. rewrite TRs, HIs, (CallA.twin_len_den E lenf) by (fold nf; lia). fold nf. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0, ESH.
      unfold shlen in INB. rewrite Z.shiftr_div_pow2 in INB by lia. change (2 ^ 3) with 8 in INB. lia. }
    exact (so_disj _ _ _ _ _ _ HS k r0 sh rs Fr0 Frs NKs ZK ZS (or_introl W0) _ (conj RK INS)).
Qed.

Lemma kept_block : forall k len kd b, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
  b <> (Af, nf) /\ b <> (shad Af, shlen (nf + 7)).
Proof.
  intros k len kd b Hin NKf NKs Hb SUB.
  destruct (OTHERS k len kd Hin NKf NKs) as [[KT (kb & BTk & NKB)]|(KT & r0 & Fr0 & L0 & LE0 & P0 & W0 & CASE)].
  2:{ exact (kept_block_w k len kd r0 b Hin NKf NKs Fr0 L0 LE0 P0 W0 CASE Hb SUB). }

  destruct (CallA.twin_canon_inv st wnl kf sh TCAN) as (? & ? & ? & ? & ? & _ & _ & _ & _ & _ & _ & TAP & _).
  destruct (CallA.twins_apart_inv _ _ _ _ _ _ k len kd TAP Hin KT NKs) as [OLD|EVA].
  2:{ destruct (CallV.twin_ev_cases E _ _ _ _ _ _ _ (so_facts _ _ _ _ _ _ HS) EVA) as (kb2 & BT2 & LW & AL & EVD).
      rewrite BTk in BT2. injection BT2 as <-.
      pose proof (GTwinSub.GTwinSub.mod8_of_align E _ kb (so_facts _ _ _ _ _ _ HS) AL) as K8.

      destruct (entry_window k len kd Hin) as (_ & INWk & _). apply weqb_eq in KT. subst kd. rewrite KT9 in INWk.
      destruct TI as (_ & T2 & _). destruct (T2 _ INWk eq_refl) as (b2 & Hb2T & EIV). unfold w_iv in EIV. cbn [w_lo w_len] in EIV.
      pose proof AR as [HWw _].
      destruct (twin_T_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b2 HWw Hb2T) as (_ & _ & _ & _ & _ & NR2 & AL2 & UB2 & NUB2).
      assert (EB : b = twin_iv b2).
      { apply (twin_container AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b2 b HWw Hb2T Hb). rewrite <- EIV. exact SUB. }
      unfold twin_iv in EIV. injection EIV as ESA ESL.
      destruct owner as (UBf & HTf & _ & NRf & ALf).
      subst b. unfold twin_iv. split.
      - intros X. apply (f_equal fst) in X. cbn [fst] in X. apply NUB2. rewrite X. exact UBf.
      - intros X. injection X as XA XL.

        destruct nf_small as (A0 & N1 & SM).
        pose proof (CallA.block_of_twin_sound E _ k kb (so_facts _ _ _ _ _ _ HS) BTk) as LK.
        pose proof (bv_unsigned_in_range 64 (ev E kb)) as RKB. change (bv_modulus 64) with (2 ^ 64) in RKB.
        rewrite Z.mod_small in LK by (clear - RKB; Z.div_mod_to_equations; lia).
        assert (EKB : bv_unsigned (ev E kb) = Af).
        { rewrite ESA, XA in LK. unfold shad, ASHOFF in LK. rewrite Z.shiftr_div_pow2 in LK by lia. change (2 ^ 3) with 8 in LK.
          clear - LK K8 ALf. Z.div_mod_to_equations. lia. }
        destruct EVD as [CVk|(ks & lens & kds & rsub & Hins & NXs & NKBs & NKTs & Frsub & RWs & L0s & HPOS & XLO & XHI)].
        {
          destruct (HeapCtrB.nonstack_windows_In E nn rest wnl kf lenf CtrLib.K_BLOCK NW (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as (_ & _ & _ & INk).
          assert (AFNZ : Af <> 0).
          { destruct owner as (_ & _ & (p0 & HP0 & _) & _). pose proof AR as [(AH0 & _) _]. destruct WOF as (_ & _ & _ & E4w). rewrite E4w in AH0.
            destruct (heap_block_facts AI _ _ _ _ _ (HB p0 Af nf) AH0 HP0 ltac:(exists p0; reflexivity)) as (_ & (BK0 & _) & _). unfold ablk, AIMG_HI, KLS in BK0. cbn [ab_addr ab_size] in BK0. lia. }
          apply (CVU kb CVk ltac:(rewrite EKB; exact AFNZ) _ INk); [reflexivity| cbn [w_len]; fold nf; lia| cbn [w_lo]; fold Af; symmetry; exact EKB]. }
        assert (XIN : Af <= bv_unsigned (ev E ks) < Af + nf).
        { rewrite ESL, XL in XHI. rewrite EKB in XLO, XHI. unfold shlen in XHI. rewrite Z.shiftr_div_pow2 in XHI by lia. change (2 ^ 3) with 8 in XHI.
          clear - XLO XHI N1. Z.div_mod_to_equations. lia. }
        destruct (entry_window ks lens kds Hins) as (Ks0 & _).
        destruct (entry_window kf lenf CtrLib.K_BLOCK (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as (Kf0 & _).
        assert (ZKs : PrimInt63.eqb ks 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ks0).
        assert (ZF : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kf0).
        assert (NSs : ks <> sh).
        { intros ->. destruct twin_sh as (rs & Frs & TRs & _). rewrite Frsub in Frs. injection Frs as <-.
          unfold is_twin_region in TRs. cbv zeta in TRs. do 2 (apply andb_prop in TRs as [TRs ?]). apply andb_prop in TRs as [_ RO].
          rewrite RWs in RO. discriminate RO. }
        destruct (OTHERS ks lens kds Hins NXs NSs) as [[KTs _]|(_ & r0s & Fr0s & _ & _ & _ & _ & CASEs)]; [rewrite NKTs in KTs; discriminate KTs|].
        destruct CASEs as [KB|FULL]; [exact (NKBs KB)|].
        pose proof (region_first_byte ks rsub Frsub L0s HPOS) as RKs.
        assert (INF : bv_unsigned (ev E kf) + loZ rf <= bv_unsigned (ev E ks) < bv_unsigned (ev E kf) + hiZ E rf).
        { unfold loZ. rewrite LO0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. fold Af. rewrite FULL. fold nf. lia. }
        exact (so_disj _ _ _ _ _ _ HS ks rsub kf rf Frsub Frf NXs ZKs ZF (or_introl RWs) _ (conj RKs INF)). }
  destruct (CallA.twin_arm_old_inv _ _ _ _ _ OLD) as (kb' & rk & n2 & BT2 & FRk & WL2 & LEN2 & _).
  rewrite BTk in BT2. injection BT2 as <-.
  pose proof (HeapCtrB.win_lookup_In _ _ _ _ WL2) as IN2.
  assert (NKBs : kb <> sh). { intros ->. rewrite WLt in WL2. apply (f_equal (fun o => match o with Some (_, kd0) => w2Z kd0 | None => 0 end)) in WL2. vm_compute in WL2. discriminate WL2. }
  destruct (entry_window kb n2 CtrLib.K_BLOCK IN2) as (Kb0 & _ & b2 & Hb2 & SUB2 & EQ2). pose proof (EQ2 eq_refl) as E2. subst b2.
  set (A2 := bv_unsigned (ev E kb)) in *. set (N2 := bv_unsigned (den E n2)) in *.

  destruct (OTHERS kb n2 CtrLib.K_BLOCK IN2 NKB NKBs) as [[X _]|(_ & r2 & Fr2 & L2 & LE2 & P2 & W2 & CASE2)]; [discriminate X|].
  destruct (kept_block_w kb n2 CtrLib.K_BLOCK r2 (A2, N2) IN2 NKB NKBs Fr2 L2 LE2 P2 W2 CASE2 Hb2 ltac:(intros a Ha; exact Ha)) as [NEB _].
  destruct (aw_blocks_ok_asan AI IMGX IMGX_aci ACCT UNIV AI_fake aw LB (ms_mem ms) mo (A2, N2) AWHf Hb2) as (B1 & B2 & B3 & _). cbn [fst snd] in B1, B2, B3.
  unfold aw_ceiling_asan in B3. pose proof atop_range as ATR.
  assert (N2pos : 1 <= N2) by (unfold hiZ in *; fold N2 in LE2; lia).
  assert (EK : bv_unsigned (ev E k) = shad A2).
  { rewrite (CallA.block_of_twin_sound E _ k kb (so_facts _ _ _ _ _ _ HS) BTk). fold A2. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. clear - B1 B3 N2pos ATR. Z.div_mod_to_equations. lia. }
  assert (EL : bv_unsigned (den E len) = shlen (N2 + 7)).
  { rewrite (CallA.len_is_twin_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) LEN2) by (fold N2; lia). fold N2. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite EK, EL in SUB.

  destruct (entry_window k len kd Hin) as (_ & INWk & _). rewrite EK, EL in INWk. apply weqb_eq in KT. subst kd. rewrite KT9 in INWk.
  destruct TI as (_ & T2 & _). destruct (T2 _ INWk eq_refl) as (b2 & Hb2T & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as ESA ESL.
  pose proof AR as [HWw _].
  destruct (twin_owner_w AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b2 A2 N2 HWw Hb2T Hb2 ESA) as (EA2 & EN2 & NR2).
  destruct (twin_T_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b2 HWw Hb2T) as (_ & _ & _ & _ & _ & _ & AL2 & UB2 & NUB2).
  rewrite <- EA2 in AL2, NUB2.

  assert (EB : b = (shad A2, shlen (N2 + 7))).
  { rewrite EA2, EN2. apply (twin_container AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b2 b HWw Hb2T Hb). unfold twin_iv. rewrite <- EA2, <- EN2. exact SUB. }
  destruct owner as (UBf & HTf & _ & NRf & ALf).
  subst b. split.
  - intros X. apply (f_equal fst) in X. cbn [fst] in X. apply NUB2. rewrite X. exact UBf.
  - intros X. apply (f_equal fst) in X. cbn [fst] in X. apply NEB.
    assert (EA : A2 = Af) by (unfold shad in X; rewrite !Z.shiftr_div_pow2 in X by lia; change (2 ^ 3) with 8 in X; clear - X AL2 ALf; Z.div_mod_to_equations; lia).
    rewrite EA in *. f_equal. exact (LB_same_addr AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo Af N2 nf HWw Hb2 blockLB).
Qed.

Variables (p q : aptr) (UBk N : Z) (RNG' : footprint) (sta' : astate) (m' : amem) (mo' : Model) (aw' : word).
Hypothesis HP : In (HB p Af nf) LBa.
Hypothesis AH' : AHEAP AI L RNG' sta' (HB q UBk N :: lb_remove p LBa) m'.
Hypothesis AC' : ACCT aw' L RNG' sta' (HB q UBk N :: lb_remove p LBa) mo'.
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis PRES : aheap_pres (aci AI) (lb_remove p LBa) sp (ms_mem ms) m'.
Hypothesis TWP : twins_pres (lb_remove p LBa) (ms_mem ms) m'.
Hypothesis PATN : ablock_shadow m' UBk N.
Definition LBk : blocks := LB_free LB Af nf.
Definition LBr : blocks := (shad UBk, shlen (N + 7)) :: (UBk, N) :: LBk.
Definition Tr : list ablock := List.filter (fun x => if ablock_eq_dec x (HB p Af nf) then false else true) (w_T WW).

Definition Wr : wit := mkWit (w_L WW) RNG' sta' (HB q UBk N :: lb_remove p (w_LBa WW)) (HB q UBk N :: Tr) (w_FA WW) m' (w_zc WW).

Lemma NEWBr : 1 <= N <= AREQMAX /\ ablock_range UBk N /\ ALib.Mem.wr_at asegs m' UBk N.
Proof.
  destruct (heap_block_facts AI L RNG' sta' _ m' (HB q UBk N) AH' ltac:(left; reflexivity) ltac:(exists q; reflexivity)) as (A1 & A2 & A3).
  cbn [ab_addr ab_size] in *. auto.
Qed.

Lemma WORLDr : aw_holds_w AI ACCT UNIV Wr aw' LBr m' mo'
  /\ (forall g, 0 <= g -> 8 * g < N -> m' (ALib.Mem.wa (shad UBk + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? N then 0 else N - 8 * g)))
  /\ user_band UBk /\ (forall a, in_iv (UBk, N) a -> ~ in_user LBk a) /\ ~ In (shad UBk, shlen (N + 7)) ((UBk, N) :: LBk)
  /\ (forall a, in_iv (shad UBk, shlen (N + 7)) a -> ~ in_user LBk a).
Proof.
  destruct WOF as (E1 & E2 & E3 & E4).
  destruct (aw_real_realloc AI ACCT UNIV AI_fake aw aw' LB (ms_mem ms) mo WW RNG' sta' p Af nf q UBk N m' mo' sp AR
              ltac:(rewrite E4; exact HP) ltac:(rewrite E1, E4; exact AH') ltac:(rewrite E1, E4; exact AC') ltac:(rewrite E4; exact PRES) ltac:(rewrite E4; exact TWP) PATN)
    as (AR' & VB & NT & UB & DJ & DJT).
  destruct AR' as [HW1 _].
  destruct (twin_out_w AI ACCT UNIV AI_fake _ aw' _ m' mo' (HB q UBk N) HW1 VB ltac:(exists q; reflexivity) NT) as (AWH' & NIN & PAT).
  split; [exact AWH'|]. split; [exact PAT|]. split; [exact UB|]. split; [exact DJ|]. split; [exact NIN| exact DJT].
Qed.
Lemma WORLDr_asan : aw_holds_asan AI ACCT UNIV aw' LBr m' mo'.
Proof. exists Wr. exact (proj1 WORLDr). Qed.

Lemma SBr : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LBk a -> m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a).
Proof.
  intros a Ha ST. destruct WOF as (E1 & E2 & E3 & E4). pose proof AR as [HWw EMw]. pose proof HWw as (AH & HTw & _ & HFAw & _).
  assert (HPw : In (HB p Af nf) (w_LBa WW)) by (rewrite E4; exact HP).
  pose proof (LB_free_char AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo p Af nf HWw HPw) as CHAR. cbv zeta in CHAR.
  assert (RM : forall b, In b (lb_remove p (w_LBa WW)) -> In b (w_LBa WW)) by (intros b Hb; exact (proj1 (proj1 (lb_remove_In AI _ _ _ _ _ p Af nf b AH HPw) Hb))).
  apply (aw_real_stable AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo WW RNG' sta' (HB q UBk N :: lb_remove p LBa) m' (lb_remove p LBa) LBk sp (lb_remove p LBa) TWP);
    [| exact AR| rewrite E1; exact AH'| exact PRES| | | exact Ha| exact ST].
  {
    intros b HbO _ HvK. rewrite <- E4. apply (lb_remove_In AI _ _ _ _ _ p Af nf b AH HPw). split; [exact HbO|]. intros ->.
    unfold LBk in HvK. apply LB_free_In in HvK as (_ & _ & NE). apply NE. reflexivity. }
  - intros v Hv UB P. apply CHAR in Hv as [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
    + exists b. split; [rewrite <- E4; exact Hb| reflexivity].
    + exfalso. apply filter_In in Hb as [Hb _]. destruct (LB_twin_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b HWw Hb) as (T1 & T2 & T3).
      unfold user_band in UB. cbn [fst twin_iv] in UB. lia.
    + exfalso. destruct (LB_fsh_facts AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b HWw (conj (conj (RM b Hb) NF) HF)) as (T1 & T2 & T3 & _).
      unfold user_band in UB. cbn [fst fsh_iv] in UB. lia.
  - intros v Hv NUB. apply CHAR in Hv as [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
    + exfalso. destruct (LB_user_facts AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b HWw (conj (RM b Hb) NF)) as (UP & B1 & B2 & _).
      apply NUB. unfold user_band. cbn [fst user_iv]. pose proof (usz_le b). lia.
    + left. exists b. apply filter_In in Hb as [Hb NE]. destruct (HTw b Hb) as [HbL HH].
      split; [exact HbL|]. split; [| split; [exact HH| reflexivity]].
      right. rewrite <- E4. apply (lb_remove_In AI _ _ _ _ _ p Af nf b AH HPw). split; [exact HbL|].
      destruct (ablock_eq_dec b (HB p Af nf)); [discriminate NE| assumption].
    + right. exists b. split; [exact (RM b Hb)|]. split; [rewrite <- E4; exact Hb|]. split; [exact HF| reflexivity].
Qed.
Lemma SBVr : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LBk a ->
  rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true).
Proof. exact (CtrFrame.SBV_of_raw (CtrFrame.stableA AI ms LBk) (ms_mem ms) m' SBr). Qed.
Lemma WBMr : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
  wb asegs (ms_mem ms) a = true -> wb asegs m' a = true.
Proof. exact (CtrFrame.WBM_of_pres AI _ _ _ _ PRES). Qed.

Definition KEEPf (k0 : int) : Prop := k0 <> kf /\ k0 <> sh.

Lemma WINKf : forall k0 len kd, KEEPf k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LBk a.
Proof.
  intros k0 len kd [NKf NKs] WL a Ha. pose proof (HeapCtrB.win_lookup_In _ _ _ _ WL) as Hin.
  destruct (entry_window k0 len kd Hin) as (_ & _ & b & Hb & SUB & _).
  destruct (kept_block k0 len kd b Hin NKf NKs Hb SUB) as [N1 N2].
  apply in_ivs_In. exists b. split; [apply LB_free_In; auto|]. apply SUB. unfold in_iv. cbn [fst snd]. lia.
Qed.

Lemma VKEEPf : forall k0 rg hs n sh' len, IMap.find k0 (s_regs st) = Some rg -> zero_view rg = Some hs -> KEEPf k0 ->
  block_of_twin (s_facts st) k0 = Some n -> CallV.view_parent (s_facts st) (s_regs st) n sh' ->
  CtrA.win_lookup wnl sh' = Some (len, K_TWIN) -> KEEPf sh'.
Proof.
  intros k0 rg hs n sh' len Fk ZV [NKf NKs] BT VPAR WL. split.
  - intros ->. rewrite WLf in WL. assert (X : CtrLib.K_BLOCK = K_TWIN) by congruence. vm_compute in X. discriminate X.
  - intros ->. unfold no_views_on in NV.
    pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) NV k0 rg Fk) as C. cbv beta in C.
    replace (PrimInt63.eqb k0 sh) with false in C by (symmetry; apply Uint63.eqb_false_spec; exact NKs).
    rewrite ZV, BT in C. destruct VPAR as [(kb & o1 & UB & TW)|(rshp & Frshp & HNp)];
      [rewrite UB, TW, Uint63.eqb_refl in C; cbn in C; discriminate C| rewrite Frshp, HNp in C; cbn [negb] in C; rewrite !Bool.andb_false_r in C; discriminate C].
Qed.

Lemma TKEEPf : forall k0 rg sh' kb n len, IMap.find k0 (s_regs st) = Some rg -> KEEPf k0 -> CtrA.win_lookup wnl sh' = Some (len, K_TWIN) ->
  block_of_twin (s_facts st) sh' = Some kb -> CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK) ->
  size_tail_ok (s_facts st) n = true -> tail_named (tail_rhs sh' n) k0 (s_facts st) = true -> KEEPf sh'.
Proof.
  intros k0 rg sh' kb n len Fk [NKf NKs] WL BT WLk ST TN. split.
  - intros ->. rewrite WLf in WL. assert (X : CtrLib.K_BLOCK = K_TWIN) by congruence. vm_compute in X. discriminate X.
  - intros ->. rewrite BTs in BT. injection BT as <-. rewrite WLf in WLk. injection WLk as <-.
    destruct (CallA.twin_canon_inv st wnl kf sh TCAN) as (rs0 & n0 & kdn & lent0 & kdt & _ & WLn & _ & _ & _ & _ & _ & NTA). rewrite WLf in WLn. injection WLn as <- <-.
    exact (CallA.no_tail_at_sound _ _ _ _ k0 rg (so_bst _ _ _ _ _ _ HS) NTA Fk TN).
Qed.
Lemma SBTf : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
  rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true).
Proof.
  intros a Ha SC _. apply (FrameV.frame_v_of_raw asegs).
  destruct SC as [(a' & R & ->)|(v & Hv & R)].
  - exact (proj1 (PRES (shad a') Ha ltac:(right; right; right; exists a'; split; [left; exact R| reflexivity]))).
  - destruct (IMGSH_aci v a Hv R) as (a' & INA & ->).
    exact (proj1 (PRES (shad a') Ha ltac:(right; right; right; exists a'; split; [right; left; exact INA| reflexivity]))).
Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Notation E' := (CtrFrame.E' E st Fv Gv).
Lemma SBOf : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E') (op_args o))) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a).
Proof.
  intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI. destruct (OPS_fp_other _ _ a NI FP) as [R|[(a' & R & ->)|(a' & R & ->)]].
  - pose proof (SBr a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact R)) as E1. unfold ALib.Mem.wa in E1. exact E1.
  - pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [right; left; exact R| reflexivity]))) as E1.
    unfold ALib.Mem.wa in E1. exact E1.
  - pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact R| reflexivity]))) as E1.
    unfold ALib.Mem.wa in E1. exact E1.
Qed.

Variables (h1 h2 : list sv).
Hypothesis H1 : heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK = Some h1.
Hypothesis H2 : heap_del_window_k h1 (VP sh wzero) K_TWIN = Some h2.

Definition WBf : window := Win Af nf K_BLOCK.
Definition WTf : window := Win (shad Af) (shlen (nf + 7)) K_TWINz.

Lemma forallb_sub : forall {T} (f : T -> bool) l l', (forall x, In x l' -> In x l) -> forallb f l = true -> forallb f l' = true.
Proof. intros T f l l' SUB H. apply forallb_forall. intros x Hx. exact (proj1 (forallb_forall _ _) H x (SUB x Hx)). Qed.

Lemma forallb_skipn : forall {T} (f : T -> bool) j l, forallb f l = true -> forallb f (skipn j l) = true.
Proof.
  intros T f j. induction j as [|j IH]; intros l H; [exact H|]. destruct l as [|x l]; [reflexivity|]. cbn [skipn]. cbn [forallb] in H.
  apply andb_prop in H as [_ H]. exact (IH l H).
Qed.

Lemma anchors_perm : forall (l l' : list (int * sv * w64)), Permutation l l' -> Permutation (HeapCtrB.anchors l) (HeapCtrB.anchors l').
Proof. intros l l' P. unfold HeapCtrB.anchors. apply Permutation_map. exact P. Qed.

Lemma DEL2 : exists l1 l2 m1 m2 nw2 rest2,
  h2 = VL md :: A :: VL nw2 :: rest2 /\ wt nw2 = false /\ pred (pred nn) = Z.to_nat (to_Z (wl nw2)) /\ (3 * pred (pred nn) <= length rest2)%nat
  /\ wins_of E (pred (pred nn)) rest2 = m1 ++ m2 /\ skipn (3 * pred (pred nn)) rest2 = skipn (3 * nn) rest
  /\ (forall x, In x rest2 -> In x rest) /\ (2 <= nn)%nat
  /\ wins_of E nn rest = l1 ++ WBf :: l2 /\ l1 ++ l2 = m1 ++ WTf :: m2
  /\ ~ In WBf (l1 ++ l2) /\ ~ In WTf (m1 ++ m2).
Proof.
  pose proof (HeapCtrB.windows_anchored_nodup_anchors _ _ AN) as NDA.
  rewrite Eh in H1.
  destruct (CtrFree.heap_del_window_k_facts E md A nw rest nn kf CtrLib.K_BLOCK h1 wnl eq_refl Tnw Nn Ln NW H1)
    as (ws1 & l1 & len1 & l2 & wl1 & EH1 & I1 & W1 & W1' & T1 & N1 & L1 & SK1 & NW1 & S1 & S2 & S3 & M1 & PM1).
  destruct (HeapCtrB.windows_anchored_nodup _ _ kf len1 CtrLib.K_BLOCK lenf CtrLib.K_BLOCK AN I1 (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as [-> _].
  rewrite EH1 in H2.
  destruct (CtrFree.heap_del_window_k_facts E md A (wsub nw wone) (ws1 ++ skipn (3 * nn) rest) (pred nn) sh K_TWIN h2 wl1 eq_refl T1 N1 L1 NW1 H2)
    as (ws2 & m1 & len2 & m2 & wl2 & EH2 & I2 & W2 & W2' & T2 & N2 & L2 & SK2 & NW2 & R1 & R2 & R3 & M2 & PM2).
  destruct (HeapCtrB.windows_anchored_nodup _ _ sh len2 K_TWIN lent K_TWIN AN (S1 _ I2) (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as [-> _].
  destruct twin_sh as (rs & _ & _ & _ & ESH & ELT). destruct owner as (UBf & HTf & _ & NRf & ALf).

  assert (ND1 : List.NoDup (kf :: HeapCtrB.anchors wl1)) by (exact (Permutation_NoDup (anchors_perm _ _ PM1) NDA)).
  apply List.NoDup_cons_iff in ND1 as [NKF1 ND1'].
  assert (ND2 : List.NoDup (sh :: HeapCtrB.anchors wl2)) by (exact (Permutation_NoDup (anchors_perm _ _ PM2) ND1')).
  apply List.NoDup_cons_iff in ND2 as [NSH2 _].
  assert (ANCH : forall (l : list (int * sv * w64)) k len kd, In (k, len, kd) l -> In k (HeapCtrB.anchors l)).
  { intros l k len kd H. unfold HeapCtrB.anchors. apply in_map_iff. exists (k, len, kd). auto. }
  exists l1, l2, m1, m2, (wsub (wsub nw wone) wone), (ws2 ++ skipn (3 * pred nn) (ws1 ++ skipn (3 * nn) rest)).
  split; [exact EH2|]. split; [exact T2|]. split; [exact N2|]. split; [exact L2|]. split; [exact W2'|]. split; [rewrite SK2, SK1; reflexivity|].
  split; [intros x Hx; apply S3; apply R3; exact Hx|]. split; [lia|].
  split. { rewrite W1. unfold WBf. fold Af nf. rewrite KB1. reflexivity. }
  split. { rewrite <- W1', W2. unfold WTf. rewrite ESH, ELT, KT9. reflexivity. }
  split.
  - intros X. rewrite <- W1' in X.
    destruct (HeapCtrB.wins_cover E (pred nn) _ wl1 WBf NW1 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_BLOCK, K_STACK in KS; lia|].
    unfold WBf in EW. injection EW as E1 E2 E3.
    assert (NKf : k <> kf) by (intros ->; exact (NKF1 (ANCH _ _ _ _ Ik))).
    assert (NKs : k <> sh).
    { intros ->. destruct (HeapCtrB.windows_anchored_nodup _ _ sh len kd lent K_TWIN AN (S1 _ Ik) (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as [_ ->]. rewrite KT9 in E3. unfold K_BLOCK in E3. lia. }
    destruct (kept_block k len kd (Af, nf) (S1 _ Ik) NKf NKs blockLB ltac:(rewrite <- E1, <- E2; intros a Ha; exact Ha)) as [NE _]. exact (NE eq_refl).
  - intros X. rewrite <- W2' in X.
    destruct (HeapCtrB.wins_cover E (pred (pred nn)) _ wl2 WTf NW2 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_TWINz, K_STACK in KS; lia|].
    unfold WTf in EW. injection EW as E1 E2 E3.
    assert (NKs : k <> sh) by (intros ->; exact (NSH2 (ANCH _ _ _ _ Ik))).
    assert (NKf : k <> kf) by (intros ->; exact (NKF1 (ANCH _ _ _ _ (R1 _ Ik)))).
    destruct (kept_block k len kd _ (S1 _ (R1 _ Ik)) NKf NKs HTf ltac:(rewrite <- E1, <- E2; intros a Ha; exact Ha)) as [_ NE]. exact (NE eq_refl).
Qed.

Definition kB : int := addn (s_next st) 15.
Definition kS : int := addn (s_next st) 16.
Definition nsv : sv := getr st X11.
Hypothesis NDEN : bv_unsigned (den E nsv) = N.
Hypothesis F15 : Fv 15 = Z_to_bv 64 UBk.
Hypothesis F16 : Fv 16 = Z_to_bv 64 (shad UBk).
Hypothesis GJ : forall o, 0 <= o < N -> rb asegs m' (UBk + o) = Some (Gv 15 o).
Hypothesis SHAPE : size_shape_ok (s_facts st) nsv = true.

Lemma NXr : st_vars_below (s_next st) st = true /\ 0 < to_Z (s_next st) /\ to_Z (s_next st) + 256 <= 2 ^ 62.
Proof. exact (HeapCtr.fresh_ok_inv st FOK). Qed.
Lemma nsv_below : sv_vars_below (s_next st) nsv = true.
Proof.
  destruct NXr as (SVB & _). unfold st_vars_below in SVB.
  apply andb_prop in SVB as [SVB _]. apply andb_prop in SVB as [SVB _]. apply andb_prop in SVB as [SVB _].
  apply andb_prop in SVB as [SVB _]. apply andb_prop in SVB as [H1' _]. exact (rf_allb_get _ _ _ H1' X11).
Qed.
Lemma kB_Z : to_Z kB = to_Z (s_next st) + 15.
Proof.
  destruct NXr as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold kB. rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma kS_Z : to_Z kS = to_Z (s_next st) + 16.
Proof.
  destruct NXr as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold kS. rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma ev_kB : bv_unsigned (ev E' kB) = UBk.
Proof.
  unfold kB. rewrite (CtrFrame.ev_E'_fresh E st FOK Fv Gv 15) by lia. change (Z.of_nat 15) with 15. rewrite F15. destruct NEWBr as (N1 & (BK & _ & TOP & _) & _).
  pose proof atop_range. unfold ablk, AIMG_HI, KLS in BK. apply Z_to_bv_small. unfold bv_modulus, two64. lia.
Qed.
Lemma ev_kS : bv_unsigned (ev E' kS) = shad UBk.
Proof.
  unfold kS. rewrite (CtrFrame.ev_E'_fresh E st FOK Fv Gv 16) by lia. change (Z.of_nat 16) with 16. rewrite F16. destruct NEWBr as (N1 & BR & _).
  destruct (twin_band _ _ BR N1) as (T1 & T2 & T3 & _). apply Z_to_bv_small. unfold bv_modulus, two64. lia.
Qed.
Lemma kB_nz : PrimInt63.eqb kB 0%uint63 = false.
Proof. apply Uint63.eqb_false_spec. intros X. pose proof kB_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NXr as (_ & P & _). lia. Qed.
Lemma kS_nz : PrimInt63.eqb kS 0%uint63 = false.
Proof. apply Uint63.eqb_false_spec. intros X. pose proof kS_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NXr as (_ & P & _). lia. Qed.

Definition blk_region : region := Region 0%uint63 nsv true BGUnk IMap.empty.

Lemma blk_region_ok : region_ok asegs (s_priv st) E' m' kB blk_region.
Proof.
  destruct NEWBr as (N1 & BR & WR). pose proof WORLDr_asan as AWH'.
  assert (EH : hiZ E' blk_region = N) by (unfold hiZ, blk_region; cbn [rg_hi]; rewrite (CtrFrame.den_E' E st Fv Gv nsv nsv_below); exact NDEN).
  assert (EL : loZ blk_region = 0) by reflexivity.
  destruct BR as (BK & _ & TOP & _). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  constructor; rewrite ?ev_kB, ?EH, ?EL.
  - apply IMap.bst_empty.
  - intros _. unfold two64. lia.
  - intros _ a Ha.
    destruct (aw_user_ok_asan AI ACCT UNIV AI_fake aw' LBr m' mo' (UBk, N) a AWH' ltac:(right; left; reflexivity) ltac:(unfold in_iv; cbn [fst snd]; lia)) as [MP SEG].
    split; [| split; [| exact SEG]].
    + unfold rb. destruct (m' (Z_to_bv 64 a)); [discriminate| contradiction].
    + intros _. apply (GlueA.wb_wviewA asegs). destruct WR as (_ & _ & W). replace a with (UBk + (a - UBk)) by lia. apply W. lia.
  - intros g gr Hg. cbn [blk_region rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
  - intros g gr c i Hg. cbn [blk_region rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
  - intros o H1' _ _. specialize (H1' kB_nz). unfold bg_byte. cbn [blk_region rg_bg]. unfold CtrFrame.E'. rewrite eg_above by (rewrite kB_Z; lia).
    rewrite kB_Z. replace (to_Z (s_next st) + 15 - to_Z (s_next st)) with 15 by lia. apply GJ. lia.
Qed.

Lemma twin_region_okA : region_ok asegs (s_priv st) E' m' kS (twin_region nsv).
Proof.
  destruct NEWBr as (N1 & BR & WR). destruct WORLDr as (_ & PAT & _). pose proof WORLDr_asan as AWH'. destruct (twin_band _ _ BR N1) as (T1 & T2 & T3 & _).
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (CtrFrame.den_E' E st Fv Gv nsv nsv_below); exact NDEN).
  apply (CallA.twin_region_ok asegs (s_priv st) E' m' kS nsv kS_nz); rewrite ?DN, ?ev_kS.
  - lia.
  - unfold AREQMAX in N1. lia.
  - pose proof (CallA.size_shape_sound E' _ nsv (so_facts _ _ _ _ _ _ (CtrFrame.HS' OPS E st ms mo HS FOK Fv Gv)) SHAPE) as X. rewrite DN in X. exact X.
  - unfold shlen in T2. rewrite Z.shiftr_div_pow2 in T2 by lia. change (2 ^ 3) with 8 in T2. unfold two64. lia.
  - intros g G0 G1. split.
    + pose proof (PAT g G0 G1) as P1. unfold rb. unfold ALib.Mem.wa in P1. rewrite P1. reflexivity.
    + apply (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw' LBr m' mo' _ (shad UBk + g) AWH' ltac:(left; reflexivity)
                     ltac:(unfold in_iv; cbn [fst snd]; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - G0 G1; Z.div_mod_to_equations; lia))).
Qed.

Hypothesis N255 : (nn <= 255)%nat.
Hypothesis AWden : aw = den E A.
Variable pd : bool.
Hypothesis AW'E : aw' = Z_to_bv 64 (bv_unsigned aw - (if pd then 0 else N)).
Definition cred' : sv := if pd then A else sv_alu ALU_SUB A nsv.
Variables (h3 h4 h5 : list sv).
Hypothesis H3 : heap_set_A h2 cred' = Some h3.
Hypothesis H4 : heap_add_window h3 (VP kB wzero) nsv (VL CtrLib.K_BLOCK) = Some h4.
Hypothesis H5 : heap_add_window h4 (VP kS wzero) (twin_len nsv) (VL K_TWIN) = Some h5.
Definition WB : window := Win UBk N K_BLOCK.
Definition WT : window := Win (shad UBk) (shlen (N + 7)) K_TWINz.

Lemma rest_below : forallb (sv_vars_below (s_next st)) rest = true.
Proof. exact (CtrFrame.rest_below st FOK rest hargs md A nw Hf Eh). Qed.

Lemma DEC5 : forall (m1 m2 : list window) nw2 rest2,
  h2 = VL md :: A :: VL nw2 :: rest2 -> wt nw2 = false -> pred (pred nn) = Z.to_nat (to_Z (wl nw2)) -> (3 * pred (pred nn) <= length rest2)%nat ->
  wins_of E (pred (pred nn)) rest2 = m1 ++ m2 -> skipn (3 * pred (pred nn)) rest2 = skipn (3 * nn) rest ->
  (forall x, In x rest2 -> In x rest) -> (2 <= nn)%nat ->
  decode (map (den E') h5) = Some (w2Z md, aw', ((m1 ++ m2) ++ [WB]) ++ [WT], map (den E) (skipn (3 * nn) rest)).
Proof.
  intros m1 m2 nw2 rest2 EH2 T2 N2 L2 W2 SK2 SUB NN2. destruct NEWBr as (NN & _).
  assert (NS : to_Z (wl nw2) + 2 < two63) by (pose proof (Uint63.to_Z_bounded (wl nw2)) as B; unfold two63; lia).
  rewrite EH2 in H3. cbn in H3. injection H3 as <-.
  destruct (CtrPost.add_window_facts E' md cred' nw2 rest2 (pred (pred nn)) (VP kB wzero) nsv (VL CtrLib.K_BLOCK) T2 N2 L2 ltac:(lia)) as (A1 & T1 & N1 & L1 & W1 & S1).
  cbv zeta in A1, T1, N1, L1, W1, S1. assert (X4 : Some h4 = _) by (rewrite <- H4; exact A1). apply Some_inj in X4. subst h4.
  destruct (CtrPost.add_window_facts E' md cred' (wadd nw2 wone) _ (S (pred (pred nn))) (VP kS wzero) (twin_len nsv) (VL K_TWIN) T1 N1 L1
              ltac:(destruct (wadd_one_small nw2 T2 ltac:(lia)) as [_ X]; lia)) as (A2 & T2' & N2' & L2' & W2' & S2').
  cbv zeta in A2, T2', N2', L2', W2', S2'. assert (X5 : Some h5 = _) by (rewrite <- H5; exact A2). apply Some_inj in X5. subst h5.
  rewrite (decode_hargs E' md cred' _ _ (S (S (pred (pred nn)))) T2' N2' L2'). rewrite W2', W1, S2', S1, SK2.
  assert (RB2 : forallb (sv_vars_below (s_next st)) rest2 = true) by (apply (forallb_sub _ rest); [exact SUB| exact rest_below]).
  rewrite (CtrFrame.wins_of_E' E st Fv Gv _ _ RB2), W2, (CtrFrame.map_den_E' E st Fv Gv _ (forallb_skipn _ (3 * nn) rest rest_below)).
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (CtrFrame.den_E' E st Fv Gv nsv nsv_below); exact NDEN).
  assert (C1 : den E' cred' = aw').
  { unfold cred'. destruct pd.
    - rewrite (CtrFrame.den_E' E st Fv Gv A (CtrFrame.A_below st FOK rest hargs md A nw Hf Eh)), AW'E, Z.sub_0_r, AWden. symmetry. apply Z_to_bv_bv_unsigned.
    - rewrite den_sv_alu. rewrite (CtrFrame.den_E' E st Fv Gv A (CtrFrame.A_below st FOK rest hargs md A nw Hf Eh)). unfold alu64, alu. apply bv_eq.
      rewrite bv_sub_unsigned, AW'E, Z_to_bv_unsigned, DN, AWden. reflexivity. }
  assert (C2 : Win (bv_unsigned (den E' (VP kB wzero))) (bv_unsigned (den E' nsv)) (bv_unsigned (den E' (VL CtrLib.K_BLOCK))) = WB).
  { unfold WB. rewrite HeapCtr.den_VPz, ev_kB, DN. reflexivity. }
  assert (C3 : Win (bv_unsigned (den E' (VP kS wzero))) (bv_unsigned (den E' (twin_len nsv))) (bv_unsigned (den E' (VL K_TWIN))) = WT).
  { unfold WT. rewrite HeapCtr.den_VPz, ev_kS. rewrite (CallA.twin_len_den E' nsv) by (rewrite DN; unfold AREQMAX in NN; lia).
    rewrite DN. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite C1, C2, C3. reflexivity.
Qed.

Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) (ms_mem ms).

Lemma freed_off_image : forall a, in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a -> find_segment asegs a 1 = None /\ a < ATOP.
Proof.
  intros a Ha. destruct owner as (UBf & HTf & _). pose proof atop_range as ATR. pose proof AR as [HWw _].
  assert (IU : in_user LB a).
  { unfold in_user. apply in_ivs_In. destruct Ha as [Ha|Ha]; [exists (Af, nf); split; [exact blockLB| exact Ha]| exists (shad Af, shlen (nf + 7)); split; [exact HTf| exact Ha]]. }
  split.
  - destruct Ha as [Ha|Ha]; [exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ a AWHf blockLB Ha))
                            | exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ a AWHf HTf Ha))].
  - destruct (LB_band AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo a HWw IU) as [B|[B|B]]; unfold AIMG_HI, KLS in *; lia.
Qed.

Lemma HOLDNr : forall l1 l2 m1 m2,
  decode (map (den E') h5) = Some (w2Z md, aw', ((m1 ++ m2) ++ [WB]) ++ [WT], map (den E) (skipn (3 * nn) rest)) ->
  wins_of E nn rest = l1 ++ WBf :: l2 -> l1 ++ l2 = m1 ++ WTf :: m2 -> ~ In WBf (l1 ++ l2) -> ~ In WTf (m1 ++ m2) ->
  op_holds OPS HEAP_ID (map (den E') h5) m' mo'.
Proof.
  intros l1 l2 m1 m2 D W1 W2 NB NT. rewrite OPS_holds1. destruct owner as (UBf & HTf & _ & NRf & ALf).
  destruct WORLDr as (AWH' & PAT & UBn & DJ & NIN & DJT). destruct NEWBr as (NN & BR & _).
  destruct (twin_band _ _ BR NN) as (TB1 & TB2 & TB3 & _). assert (BK8 : UBk mod 8 = 0) by (destruct BR as (_ & _ & _ & X16); clear - X16; Z.div_mod_to_equations; lia).
  destruct BR as (BK & _ & TOP & _). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  assert (TWFRESH : forall a, in_iv (shad UBk, shlen (N + 7)) a -> ~ in_user ((UBk, N) :: LBk) a).
  { intros a Ha U. apply in_ivs_cons in U as [U|U]; [| exact (DJT a Ha U)].
    unfold in_iv in Ha, U. cbn [fst snd] in Ha, U. unfold user_band in UBn. lia. }
  assert (IN1 : forall w, In w (l1 ++ l2) <-> In w (wins_of E nn rest) /\ w <> WBf).
  { intros w. rewrite W1. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NB H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  assert (IN2 : forall w, In w (m1 ++ m2) <-> In w (l1 ++ l2) /\ w <> WTf).
  { intros w. rewrite W2. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NT H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  assert (WFK : windows_wf (m1 ++ m2) LBk (ATOP + 4096)).
  {
      apply Forall_forall. intros w Hw. apply IN2 in Hw as [Hw NWT]. apply IN1 in Hw as [Hw NWB].
      pose proof (proj1 (Forall_forall _ _) WF w Hw) as (X1 & X2 & X3 & KD). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
      destruct (HeapCtrB.wins_cover E nn rest wnl w NW Hw) as [KS|(k & len & kd & Ik & EW)].
      { left. destruct KD as [[_ C]|[[K _]|[K _]]]; [split; [exact KS| exact C]| rewrite KS in K; unfold K_BLOCK, K_STACK in K; lia| rewrite KS in K; unfold K_SUB, K_STACK in K; lia]. }
      assert (NKf : k <> kf).
      { intros ->. destruct (HeapCtrB.windows_anchored_nodup _ _ kf len kd lenf CtrLib.K_BLOCK AN Ik (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as [-> ->].
        apply NWB. rewrite EW. unfold WBf. rewrite KB1. reflexivity. }
      assert (NKs : k <> sh).
      { intros ->. destruct (HeapCtrB.windows_anchored_nodup _ _ sh len kd lent K_TWIN AN Ik (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as [-> ->].
        destruct twin_sh as (rs & _ & _ & _ & ESH & ELT). apply NWT. rewrite EW. unfold WTf. rewrite ESH, ELT, KT9. reflexivity. }
      destruct KD as [[K C]|[[K B]|[K (b & Hb & SUB)]]].
      * left. auto.
      * right; left. split; [exact K|]. apply LB_free_In. split; [exact B|].
        apply (kept_block k len kd (w_iv w) Ik NKf NKs B). rewrite EW. unfold w_iv. cbn [w_lo w_len]. intros a Ha. exact Ha.
      * right; right. split; [exact K|]. exists b. split; [| exact SUB]. apply LB_free_In. split; [exact Hb|].
        apply (kept_block k len kd b Ik NKf NKs Hb). rewrite EW in SUB. unfold w_iv in SUB. cbn [w_lo w_len] in SUB. exact SUB.
  }
  exists (w2Z md), aw', (((m1 ++ m2) ++ [WB]) ++ [WT]), (map (den E) (skipn (3 * nn) rest)), LBr, Wr.
  split; [exact D|]. split; [exact AWH'|]. split; [| split].
  -
    apply Forall_app. split; [apply Forall_app; split|].
    + apply (CtrPost.windows_wf_mono _ LBk LBr _ WFK). intros b Hb; right; right; exact Hb.
    + constructor; [|constructor]. unfold window_wf, WB, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; left. split; [reflexivity|]. right; left. reflexivity.
    + constructor; [|constructor]. unfold window_wf, WT, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; right. split; [unfold K_SUB, K_TWINz; lia|]. exists (shad UBk, shlen (N + 7)). split; [left; reflexivity|]. intros a Ha. exact Ha.
  -
    assert (HC1 : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m').
    { apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U NH.
      apply in_ivs_In in U as (b & Hb & Hin).
      assert (INWIN : forall w, In w (wins_of E nn rest) -> w_kind w <> K_STACK -> in_iv (w_iv w) a -> False).
      { intros w Hw NK Hwa. apply NH. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv w). split; [| exact Hwa]. apply in_map. apply filter_In. split; [exact Hw|].
        destruct (Z.eqb_spec (w_kind w) K_STACK); [contradiction| reflexivity]. }
      destruct (iv_eq_dec b (Af, nf)) as [->|N1].
      { exfalso. apply (INWIN WBf); [rewrite W1; apply in_or_app; right; left; reflexivity| cbn; unfold K_BLOCK, K_STACK; lia| exact Hin]. }
      destruct (iv_eq_dec b (shad Af, shlen (nf + 7))) as [->|N2].
      { exfalso. apply (INWIN WTf); [| cbn; unfold K_TWINz, K_STACK; lia| exact Hin].
        assert (X : In WTf (l1 ++ l2)) by (rewrite W2; apply in_or_app; right; left; reflexivity). apply IN1 in X as [X _]. exact X. }
      symmetry. unfold ALib.Mem.wa in *. apply (SBr a ltac:(unfold two64 in Ha; lia)). right; right. apply in_ivs_In. exists b. split; [apply LB_free_In; auto| exact Hin]. }
    assert (INB : In WBf (wins_of E nn rest)) by (rewrite W1; apply in_or_app; right; left; reflexivity).
    pose proof (cw_free Cw _ _ _ _ m' Af nf (l1 ++ l2) HC1 INB IN1) as HC2.
    assert (INT : In WTf (l1 ++ l2)) by (rewrite W2; apply in_or_app; right; left; reflexivity).
    pose proof (Cw_ghost_free _ _ _ _ m' (shad Af) (shlen (nf + 7)) (m1 ++ m2) HC2 INT IN2) as HC3.
    pose proof (cw_grow Cw _ _ _ _ m' UBk N HC3 DJ) as HC4.
    apply (Cw_ghost_grow _ _ _ _ m' UBk N (shlen (N + 7)) HC4); [apply in_or_app; right; left; reflexivity| lia| exact BK8|].
    exact TWFRESH.
  -
    pose proof AR as [HWw _]. pose proof HWw as (AHw & HTw & _). destruct WOF as (_ & _ & _ & E4).
    destruct owner as (_ & _ & (p' & HP' & HPT) & _).
    assert (EP : HB p' Af nf = HB p Af nf).
    { apply (shadow_iv_inj AI AI_fake _ _ _ _ _ (HB p' Af nf) (HB p Af nf) AHw (proj1 (HTw _ HPT)) ltac:(rewrite E4; exact HP)). reflexivity. }
    rewrite EP in HPT.
    pose proof (ties_free AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo (wins_of E nn rest) (l1 ++ l2) (m1 ++ m2) p Af nf RNG' sta' m' HWw TI HPT IN1 IN2
                  ltac:(intros IP; exfalso; exact (NOPR IP))) as TF.
    apply (ties_grow_heap _ (m1 ++ m2) (w_L WW) RNG' sta' m' (HB q UBk N) TF ltac:(exists q; reflexivity)); [cbn [ab_size]; lia| |
      intros IP; exfalso; apply NOPR; apply IN2 in IP as [IP _]; apply IN1 in IP as [IP _]; exact IP].
    cbn [ab_addr ab_size]. fold WB WT.
    assert (GA0 : ghost_apart (m1 ++ m2)) by (destruct TF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
    assert (WF1 : windows_wf ((m1 ++ m2) ++ [WB]) ((UBk, N) :: LBk) (ATOP + 4096)).
    { apply Forall_app. split; [apply (CtrPost.windows_wf_mono _ LBk _ _ WFK); intros b Hb; right; exact Hb|].
      constructor; [|constructor]. unfold window_wf, WB, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; left. split; [reflexivity|]. left. reflexivity. }
    apply (ghost_apart_new_ghosts ((m1 ++ m2) ++ [WB]) _ ((UBk, N) :: LBk) (ATOP + 4096) WF1).
    + exact (ghost_apart_new_block _ LBk (ATOP + 4096) UBk N WFK GA0 DJ).
    + intros w Hw. apply in_app_or in Hw as [Hw|[<-|[]]]; [left; exact Hw| right]. split; [unfold WT; cbn [w_kind]; unfold K_TWINz, K_BLOCK; lia|].
      intros _ a Ha. unfold WT, w_iv in Ha. cbn [w_lo w_len] in Ha. exact (TWFRESH a Ha).
Qed.

Variables (r : int) (st1 : sstate) (R' : bvmap 5 word).
Hypothesis CP : call_pre st = Some r.
Hypothesis FS : forget_stack_below_sp_g st = Some st1.
Hypothesis KEPT : forall rg, In rg CtrFrame.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg.
Hypothesis HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Hypothesis A0' : AP.getr R' 10%bv = Z_to_bv 64 UBk.
Hypothesis MINV' : ALib.Mem.mem_inv asegs m'.
Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis Hksp : okey offs = Some ksp.
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis K16 : keyZ ksp mod 16 = 0.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis STK' : stk asegs m' (CtrPre.sp_lo E st) sp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis OTH : OTHER mo mo'.
Hypothesis MINVo : op_minv OPS mo'.

Definition newRr : list (int * region) := [(kB, blk_region); (kS, twin_region nsv)].
Definition RgR : IMap.t region := CtrFrame.RgPg st ks rss ksp newRr [kf; sh].
Definition NEWSETr (a : Z) : Prop := in_iv (UBk, N) a \/ in_iv (shad UBk, shlen (N + 7)) a.

Lemma KEEP_delr : forall k0, ~ In k0 [kf; sh] -> KEEPf k0.
Proof. intros k0 H. split; intros ->; apply H; [left| right; left]; reflexivity. Qed.
Lemma newR_nodup : List.NoDup (map fst newRr).
Proof.
  cbn [map fst newRr]. constructor; [| constructor; [intros []| constructor]]. intros [X|[]].
  pose proof kB_Z as KB. pose proof kS_Z as KS. rewrite X in KS. lia.
Qed.
Lemma newR_fresh : forall k rg, In (k, rg) newRr -> PrimInt63.eqb k 0%uint63 = false.
Proof. intros k rg [X|[X|[]]]; injection X as <- _; [exact kB_nz| exact kS_nz]. Qed.
Lemma newR_ok : forall k rg, In (k, rg) newRr -> region_ok asegs (s_priv st) E' m' k rg.
Proof. intros k rg [X|[X|[]]]; injection X as <- <-; [exact blk_region_ok| exact twin_region_okA]. Qed.
Lemma twin_hi : hiZ E' (twin_region nsv) = shlen (N + 7) /\ loZ (twin_region nsv) = 0.
Proof.
  destruct NEWBr as (NN & _).
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (CtrFrame.den_E' E st Fv Gv nsv nsv_below); exact NDEN).
  assert (HI : rg_hi (twin_region nsv) = twin_len nsv /\ rg_lo (twin_region nsv) = 0%uint63).
  { split; [exact (CallA.twin_region_hi nsv)| exact (proj1 (CallA.twin_region_fields nsv))]. }
  destruct HI as [HI LO]. unfold hiZ, loZ. rewrite HI, LO. split; [| reflexivity].
  rewrite (CallA.twin_len_den E' nsv) by (rewrite DN; unfold AREQMAX in NN; lia). rewrite DN. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma newR_range : forall k rg a, In (k, rg) newRr ->
  bv_unsigned (ev E' k) + loZ rg <= a < bv_unsigned (ev E' k) + hiZ E' rg -> NEWSETr a.
Proof.
  intros k rg a [X|[X|[]]] Ha; injection X as <- <-.
  - left. rewrite ev_kB in Ha. unfold in_iv. cbn [fst snd]. unfold hiZ, loZ, blk_region in Ha. cbn [rg_hi rg_lo] in Ha.
    rewrite (CtrFrame.den_E' E st Fv Gv nsv nsv_below), NDEN in Ha. change (keyZ 0%uint63) with 0 in Ha. lia.
  - right. rewrite ev_kS in Ha. destruct twin_hi as [HI LO]. rewrite HI, LO in Ha. unfold in_iv. cbn [fst snd]. lia.
Qed.
Lemma new_band : forall a, NEWSETr a ->
  ((AIMG_HI <= a < 0x7fff7000 \/ 0x10007fff8000 <= a < ATOP) /\ in_iv (UBk, N) a) \/ ((0x800bde00 <= a < shad ATOP) /\ in_iv (shad UBk, shlen (N + 7)) a).
Proof.
  intros a Ha. destruct NEWBr as (NN & (BK & _ & HI & _) & _). destruct (shadow_tight UBk N BK HI ltac:(lia)) as [T1 T2].
  unfold ablk, AIMG_HI, KLS in BK. unfold AIMG_HI. destruct Ha as [Ha|Ha]; [left| right]; (split; [| exact Ha]); unfold in_iv in Ha; cbn [fst snd] in Ha; lia.
Qed.
Lemma newR_low : forall a, NEWSETr a -> AIMG_HI <= a < ATOP + 4096 /\ ~ in_user LBk a.
Proof.
  intros a Ha. destruct WORLDr as (_ & _ & _ & DJ & _ & DJT). pose proof atop_range as ATR.
  assert (SHA : shad ATOP < ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  destruct (new_band a Ha) as [[B I]|[B I]]; (split; [unfold AIMG_HI in *; lia|]); [exact (DJ a I)| exact (DJT a I)].
Qed.
Lemma newR_nosh : forall a, NEWSETr a -> ~ (0x7fff8000 <= a < 0x800bde00).
Proof. intros a Ha X. destruct (new_band a Ha) as [[B _]|[B _]]; unfold AIMG_HI in *; lia. Qed.
Lemma newR_nostk : forall a, NEWSETr a -> ~ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Proof.
  intros a Ha (a' & R & ->). pose proof atop_range as ATR.
  assert (M : shad ATOP <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  destruct (new_band _ Ha) as [[B _]|[B _]]; unfold AIMG_HI in *; [| lia].
  assert (SHA : 0x7fff7000 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia). lia.
Qed.
Lemma newR_disj : forall k1 r1 k2 r2 a, In (k1, r1) newRr -> In (k2, r2) newRr -> k1 <> k2 -> (rg_w r1 = true \/ rg_w r2 = true) ->
  ~ (bv_unsigned (ev E' k1) + loZ r1 <= a < bv_unsigned (ev E' k1) + hiZ E' r1 /\
     bv_unsigned (ev E' k2) + loZ r2 <= a < bv_unsigned (ev E' k2) + hiZ E' r2).
Proof.
  intros k1 r1 k2 r2 a I1 I2 NE _ [A1 A2].
  pose proof (newR_range k1 r1 a I1 A1) as S1. pose proof (newR_range k2 r2 a I2 A2) as S2.
  assert (BLK : forall k rg, In (k, rg) newRr -> bv_unsigned (ev E' k) + loZ rg <= a < bv_unsigned (ev E' k) + hiZ E' rg -> (k = kB /\ in_iv (UBk, N) a) \/ (k = kS /\ in_iv (shad UBk, shlen (N + 7)) a)).
  { intros k rg [X|[X|[]]] Ha; injection X as <- <-.
    - left. split; [reflexivity|]. rewrite ev_kB in Ha. unfold in_iv. cbn [fst snd]. unfold hiZ, loZ, blk_region in Ha. cbn [rg_hi rg_lo] in Ha.
      rewrite (CtrFrame.den_E' E st Fv Gv nsv nsv_below), NDEN in Ha. change (keyZ 0%uint63) with 0 in Ha. lia.
    - right. split; [reflexivity|]. rewrite ev_kS in Ha. destruct twin_hi as [HI LO]. rewrite HI, LO in Ha. unfold in_iv. cbn [fst snd]. lia. }
  destruct NEWBr as (NN & (BK & _ & HI & _) & _). destruct (shadow_tight UBk N BK HI ltac:(lia)) as [T1 T2]. pose proof atop_range as ATR.
  assert (SHA : shad ATOP <= 0x10007fff8000) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  unfold ablk, AIMG_HI, KLS in BK.
  destruct (BLK k1 r1 I1 A1) as [[-> X1]|[-> X1]]; destruct (BLK k2 r2 I2 A2) as [[-> X2]|[-> X2]]; try (exfalso; exact (NE eq_refl));
    unfold in_iv in X1, X2; cbn [fst snd] in X1, X2; lia.
Qed.

Lemma freed_band : forall a, in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a ->
  (a < 0x7fff7000 \/ 0x10007fff8000 <= a) \/ (0x800bde00 <= a < shad ATOP).
Proof.
  intros a Ha. pose proof AR as [(AH & _) EM]. destruct WOF as (E1 & E2 & E3 & E4). rewrite E4 in AH.
  destruct (heap_block_facts AI _ _ _ _ _ (HB p Af nf) AH HP ltac:(exists p; reflexivity)) as (NP & (BK & _ & HI & _) & _). cbn [ab_addr ab_size] in NP, BK, HI.
  destruct (shadow_tight Af nf BK HI ltac:(lia)) as [T1 T2]. unfold ablk, AIMG_HI, KLS in BK. unfold in_iv in Ha. cbn [fst snd] in Ha.
  destruct Ha as [Ha|Ha]; [left| right]; lia.
Qed.

Lemma freed_unbased_r : forall a, in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a -> ~ NEWSETr a -> ~ in_based E' RgR a.
Proof.
  intros a Ha NNEW (k0 & rg & Fk & KZ & RA). destruct (freed_off_image a Ha) as [_ LOW]. destruct owner as (_ & HTf & _).
  assert (SPF : ATOP + 4096 <= sp) by (rewrite SPE; lia).
  destruct (CtrFrame.RgPg_range OPS E st ms mo HS FOK Fv Gv LB LBk ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf LOSP FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln newRr [kf; sh]
              newR_nodup KEEP_delr NEWSETr newR_range k0 rg a Fk KZ RA) as [[_ X]|[_ [[_ X]|[_ [X|[X|X]]]]]].
  - exact (NNEW X).
  - lia.
  - fold sp in X. lia.
  - exact (freed_apart AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo WW Af nf a AR blockLB HTf Ha X).
  - pose proof atop_range as ATR.
    assert (SHA : 0x7fff8000 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
    destruct (sh_cov_band a X) as [C|C]; destruct (freed_band a Ha) as [B|B]; lia.
Qed.

Definition f_range : fact := FRange kB BLK_LO BLK_HI.
Definition f_align : fact := FAlign kB 4%uint63.
Definition f_link : fact := FEq (VP kS wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP kB wzero) (VL (wlit 3%uint63))) (VL SBw)).

Definition f_cred : fact := cred_fact (s_facts st) nsv A.
Hypothesis CREDF : fact_holds E f_cred.
Lemma CREDF' : fact_holds E' f_cred.
Proof.
  revert CREDF. unfold f_cred, cred_fact. destruct (prim_decided (s_facts st) nsv); cbn [fact_holds].
  - rewrite (CtrFrame.den_E' E st Fv Gv A (CtrFrame.A_below st FOK rest hargs md A nw Hf Eh)). cbn [den]. intros X; exact X.
  - rewrite (CtrFrame.den_E' E st Fv Gv nsv nsv_below), (CtrFrame.den_E' E st Fv Gv A (CtrFrame.A_below st FOK rest hargs md A nw Hf Eh)). intros X; exact X.
Qed.

Lemma FACTSr4 : facts_hold E' (f_link :: f_align :: f_range :: f_cred :: s_facts st).
Proof.
  destruct NEWBr as (NN & BR & _). destruct BR as (BK & _ & TOP & AL). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  constructor; [| constructor; [| constructor; [| constructor; [exact CREDF'| exact (so_facts _ _ _ _ _ _ (CtrFrame.HS' OPS E st ms mo HS FOK Fv Gv))]]]].
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

Definition fx_r : list fact := and7_facts nsv.
Lemma and7_hold : Forall (fact_holds E') fx_r.
Proof.
  unfold fx_r, and7_facts. pose proof (CallA.size_shape_sound E (s_facts st) nsv (so_facts _ _ _ _ _ _ HS) SHAPE) as M8.
  pose proof (CtrFrame.den_E' E st Fv Gv nsv nsv_below) as DEN.
  revert M8 DEN. generalize nsv. intros n M8 DEN.
  destruct n; [constructor| | | | | | | | | |];
    (constructor; [| constructor]); hnf in M8; cbn [fact_holds]; apply bv_eq;
    rewrite CallA.and7_den_raw, DEN, M8; cbn [den]; rewrite wbv_unsigned, wzero_ok; reflexivity.
Qed.
Lemma FACTSr : facts_hold E' (fx_r ++ f_link :: f_align :: f_range :: f_cred :: s_facts st).
Proof.
  pose proof and7_hold as A7. pose proof FACTSr4 as F4. unfold facts_hold in *.
  revert A7. generalize fx_r. intros l A7.
  induction l as [|f l IH]; [exact F4|]. cbn [app]. constructor; [exact (Forall_inv A7)| exact (IH (Forall_inv_tail A7))].
Qed.

Lemma st1_fields_r : s_pc st1 = s_pc st /\ s_rf st1 = s_rf st /\ s_ff st1 = s_ff st /\ s_resv st1 = s_resv st /\ s_facts st1 = s_facts st
  /\ s_ops st1 = s_ops st /\ s_priv st1 = s_priv st /\ s_next st1 = s_next st /\ s_regs st1 = IMap.add ks (region_forget_below rss ksp) (s_regs st).
Proof. unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. repeat split; reflexivity. Qed.
Lemma kB_next : s_next (clobber st1) = kB.
Proof.
  destruct (clobber_fields st1) as (_ & _ & _ & _ & _ & _ & _ & NXc). destruct st1_fields_r as (_ & _ & _ & _ & _ & _ & _ & NX1 & _).
  rewrite NXc, NX1. symmetry. destruct NXr as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma kS_next : PrimInt63.add kB 1%uint63 = kS.
Proof.
  destruct NXr as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  apply Uint63.to_Z_inj. rewrite add_Z by (rewrite kB_Z; change (to_Z 1%uint63) with 1; rewrite wB_two63, two63_eq; lia).
  rewrite kB_Z, kS_Z. change (to_Z 1%uint63) with 1. lia.
Qed.
Lemma stR_shape_gen : forall (S : sstate) (nx1 nx2 : int) (RT : IMap.t region -> IMap.t region) (h : list sv) (f0 f1 f2 f3 : fact) (l : list fact) (v : sv) (r0 : int),
  setpc (setr (addfacts (addfact (addfact (addfact (addfact
          (set_ops (setregs (set_next (set_next S nx1) nx2) (RT (s_regs (set_next (set_next S nx1) nx2))))
                   (set_op HEAP_ID h (s_ops (set_next (set_next S nx1) nx2))))
          f0) f1) f2) f3) l) X10 v) r0
  = SS r0 (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (RT (s_regs S)) (l ++ f3 :: f2 :: f1 :: f0 :: s_facts S) (set_op HEAP_ID h (s_ops S)) (s_priv S) nx2.
Proof. intros. destruct S. reflexivity. Qed.
Lemma stR_shape : arealloc_stB st st1 r h5 kf sh A
  = SS r (rf_set (s_rf (clobber st1)) X10 (VP kB wzero)) (s_ff st) (s_resv st) RgR
       (fx_r ++ f_link :: f_align :: f_range :: f_cred :: s_facts st) (set_op HEAP_ID h5 (s_ops st)) (s_priv st) (PrimInt63.add kS 1%uint63).
Proof.
  unfold arealloc_stB. cbv zeta. rewrite kB_next, kS_next. fold nsv. unfold fx_r.
  rewrite (stR_shape_gen (clobber st1) _ _ (fun R0 => IMap.add kS (twin_region nsv) (IMap.add kB (Region 0%uint63 nsv true BGUnk IMap.empty) (IMap.remove sh (IMap.remove kf R0))))).
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & _). destruct st1_fields_r as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & _ & R1).
  rewrite FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1, R1. reflexivity.
Qed.

Lemma NEWSETr_dec : forall a, NEWSETr a \/ ~ NEWSETr a.
Proof. intros a. unfold NEWSETr, in_iv. cbn [fst snd]. lia. Qed.

Theorem realloc_post : st_ok asegs OPS E' (arealloc_stB st st1 r h5 kf sh A) (CtrFrame.ms' ms r R' m') mo'.
Proof.
  rewrite stR_shape. destruct DEL2 as (l1 & l2 & m1 & m2 & nw2 & rest2 & EH2 & T2 & N2 & L2 & W2m & SK2 & SUB & NN2 & W1 & W2 & NB & NT).
  pose proof (DEC5 m1 m2 nw2 rest2 EH2 T2 N2 L2 W2m SK2 SUB NN2) as D.
  pose proof (HOLDNr l1 l2 m1 m2 D W1 W2 NB NT) as HOLDN.
  set (ws5 := ((m1 ++ m2) ++ [WB]) ++ [WT]) in *.
  assert (INWS : forall a, in_ws (wins_of E nn rest) a -> in_ws (m1 ++ m2) a \/ in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a).
  { intros a X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    rewrite W1 in Hw. apply in_app_or in Hw as [Hw|[<-|Hw]]; [| right; left; exact Hin|].
    - assert (X : In w (l1 ++ l2)) by (apply in_or_app; left; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [| right; right; exact Hin|];
        left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]).
    - assert (X : In w (l1 ++ l2)) by (apply in_or_app; right; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [| right; right; exact Hin|];
        left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]). }
  assert (HW5 : forall w a, In w ws5 -> w_kind w <> K_STACK -> in_iv (w_iv w) a -> in_ws (heap_ws ws5) a).
  { intros w a Hw NK Hin. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [exact Hw|].
    destruct (Z.eqb_spec (w_kind w) K_STACK); [contradiction| reflexivity]. }
  assert (NEWIN : forall a, NEWSETr a -> in_ws (heap_ws ws5) a).
  { intros a [Ha|Ha].
    - apply (HW5 WB a); [unfold ws5; apply in_or_app; left; apply in_or_app; right; left; reflexivity| cbn; unfold K_BLOCK, K_STACK; lia| exact Ha].
    - apply (HW5 WT a); [unfold ws5; apply in_or_app; right; left; reflexivity| cbn; unfold K_TWINz, K_STACK; lia| exact Ha]. }
  assert (DKB : den E' (VP kB wzero) = AP.getr R' 10%bv).
  { rewrite HeapCtr.den_VPz, A0'. apply bv_eq. rewrite ev_kB. destruct NEWBr as (NN & (BK & _ & TOP & _) & _). pose proof atop_range.
    unfold ablk, AIMG_HI, KLS in BK. symmetry. apply Z_to_bv_small. unfold bv_modulus, two64. lia. }
  apply (CtrFrame.frame_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo' KEPT HF aw LB LBk AWHf MINV' SBVr SBOf WBMr SBTf ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf
           K16 LOSP STK' FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln OTH newRr [kf; sh] newR_nodup
           newR_fresh KEEP_delr NEWSETr newR_ok newR_range newR_low newR_nosh newR_nostk newR_disj
           h5 (w2Z md) aw' ws5 (map (den E) (skipn (3 * nn) rest)) D HOLDN).
  - exact NEWIN.
  -   intros a Ha NIX NWS. destruct (GLib.UG.in_ws_dec (wins_of E nn rest) a) as [IW|NIW]; [| left; exact NIW].
    right. destruct (INWS a IW) as [X|FR].
    + exfalso. apply NWS. unfold ws5. apply CtrPost.in_ws_app. left. apply CtrPost.in_ws_app. left. exact X.
    + split; [exact (proj1 (freed_off_image a FR))|]. apply (freed_unbased_r a FR). intros NS. apply NWS. exact (CtrFrame.in_heap_ws _ _ (NEWIN a NS)).
  -   intros a IB X. pose proof (CtrFrame.in_heap_ws _ _ X) as IW. destruct (INWS a IW) as [Y|FR].
    + unfold in_ws, heap_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw). apply filter_In in Hw as [Hw KW].
      assert (NFR : forall w0, w0 = WBf \/ w0 = WTf -> in_iv (w_iv w0) a -> ~ NEWSETr a -> False).
      { intros w0 [-> | ->] Hw0 NS; [exact (freed_unbased_r a (or_introl Hw0) NS IB)| exact (freed_unbased_r a (or_intror Hw0) NS IB)]. }
      destruct (NEWSETr_dec a) as [NS|NNS]; [exact (proj1 (in_ivs_In _ _) (NEWIN a NS)) || (apply in_ivs_In; exact (proj1 (in_ivs_In _ _) (NEWIN a NS)))|].
      apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [| exact KW].
      unfold ws5. apply in_or_app. left. apply in_or_app. left.
      rewrite W1 in Hw. apply in_app_or in Hw as [Hw|[<-|Hw]]; [| exfalso; exact (NFR WBf (or_introl eq_refl) Hin NNS)|].
      * assert (X : In w (l1 ++ l2)) by (apply in_or_app; left; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; auto| exfalso; exact (NFR WTf (or_intror eq_refl) Hin NNS)| apply in_or_app; auto].
      * assert (X : In w (l1 ++ l2)) by (apply in_or_app; right; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; auto| exfalso; exact (NFR WTf (or_intror eq_refl) Hin NNS)| apply in_or_app; auto].
    + destruct (NEWSETr_dec a) as [NS|NNS]; [exact (NEWIN a NS)| exfalso; exact (freed_unbased_r a FR NNS IB)].
  - exact FACTSr.
  - exact DKB.
  - exact MINVo.
Qed.

End REALLOCD.

Lemma arealloc_block : forall E st ms mo r hargs wnl L RNG sta LBa aw kf sh cred,
  st_ok asegs OPS E st ms mo -> CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  find_twin (s_facts st) kf = Some sh -> afree_ok st wnl kf sh = true -> twin_canon st wnl kf sh = true -> getr st X10 = VP kf wzero -> heap_A hargs = Some cred ->
  KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (getr st X11) = true -> reqmax_ok (s_facts st) (getr st X11) = true ->
  cred_pre (s_facts st) (getr st X11) cred = true ->
  exists p lenf, CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK)
    /\ In (HB p (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf))) LBa
    /\ AP.getr (ms_regs ms) 10%bv = Z_to_bv 64 (bv_unsigned (ev E kf))
    /\ AP.getr (ms_regs ms) 11%bv = Z_to_bv 64 (bv_unsigned (den E (getr st X11)))
    /\ 1 <= bv_unsigned (den E (getr st X11)) <= AREQMAX
    /\ (1048576 <= bv_unsigned aw /\ (prim_decided (s_facts st) (getr st X11) = true \/ bv_unsigned (den E (getr st X11)) <= bv_unsigned aw))
    /\ ablock_shadow (ms_mem ms) (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf)).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kf sh cred HS CF FT FOKk TCAN X10E HA N0 N1 NC.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & AR & TI)).
  destruct (afree_ok_inv E st ms mo HS wnl kf sh FOKk) as (rf & lenf & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  destruct (owner E st ms mo HS wnl nn rest LB aw L RNG sta LBa NW WF W WOF AR TI kf sh TCAN rf lenf lent WLf WLt BTs POSf LEf) as (_ & _ & (p & HP & _) & _).
  pose proof (freed_pattern E st ms mo HS wnl nn rest LB aw L RNG sta LBa NW WF W WOF AR TI kf sh TCAN rf lenf lent WLf WLt BTs POSf LEf OTHERS) as FPAT.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  pose proof (KnownA.KnownA.known_ltu_sound E _ _ _ HF N0) as L0. pose proof (CallA.reqmax_ok_sound E _ _ HF N1) as L1.
  cbn [den] in L0. rewrite wbv_unsigned in L0. rewrite wzero_ok in L0.
  replace 0xFFF00000 with AREQMAX in L1 by reflexivity.
  rewrite Eh, heap_A_eq in HA. injection HA as <-.
  assert (L2 : 1048576 <= bv_unsigned aw /\ (prim_decided (s_facts st) (getr st X11) = true \/ bv_unsigned (den E (getr st X11)) <= bv_unsigned aw)).
  { unfold cred_pre in NC. apply andb_prop in NC as [NCX NC]. rewrite AWden.
    pose proof (KnownA.KnownA.known_leu_sound E _ _ _ HF NCX) as LX. replace (bv_unsigned (den E (VL C_EXHw))) with 1048576 in LX by (vm_compute; reflexivity).
    split; [exact LX|]. apply orb_prop in NC as [NC|NC]; [left; exact NC| right; exact (KnownA.KnownA.known_leu_sound E _ _ _ HF NC)]. }
  exists p, lenf. split; [exact WLf|]. split; [exact HP|].
  split; [rewrite <- HeapCtr.reg_of_X10, (GlueA.getr_RA asegs OPS E st ms mo HS X10), X10E, HeapCtr.den_VPz; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite <- HeapCtr.reg_of_X11, (GlueA.getr_RA asegs OPS E st ms mo HS X11); symmetry; apply Z_to_bv_bv_unsigned|].
  split; [lia|]. split; [exact L2| exact FPAT].
Qed.

Lemma arealloc_post_okA : forall st sts E ms mo r hargs wnl st1 kf sh cred h1 h2 h3 h4 h5 stN
    (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) p lenf n rr RNG' msP mo',
  st_ok asegs OPS E st ms mo ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  find_twin (s_facts st) kf = Some sh -> afree_ok st wnl kf sh = true -> no_views_on (s_facts st) (s_regs st) kf sh = true ->
  twin_canon st wnl kf sh = true ->
  heap_A hargs = Some cred -> size_shape_ok (s_facts st) (getr st X11) = true -> cred_pre (s_facts st) (getr st X11) cred = true ->
  prist_absent (s_facts st) hargs = true ->
  heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK = Some h1 -> heap_del_window_k h1 (VP sh wzero) K_TWIN = Some h2 ->
  heap_set_A h2 (cred_post (s_facts st) (getr st X11) cred) = Some h3 ->
  heap_add_window h3 (VP (s_next (clobber st1)) wzero) (getr st X11) (VL CtrLib.K_BLOCK) = Some h4 ->
  heap_add_window h4 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X11)) (VL K_TWIN) = Some h5 ->
  sts = [stN; arealloc_stB st st1 r h5 kf sh cred] ->
  CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK) ->
  In (HB p (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf))) LBa ->
  n = bv_unsigned (den E (getr st X11)) ->
  let R := ms_regs ms in
  AInstanceU2F.arealloc_post2 (aci AI) (AHEAP AI) L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa p (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf)) n
     (CtrPre.sp_lo E st) (ms_mem ms) rr RNG' msP ->
  (forall UB, match snd rr with
              | Some q => ACCT (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) L RNG' (fst rr) (HB q UB n :: lb_remove p LBa) mo'
              | None => True
              end) ->
  op_minv OPS mo' -> OTHER mo mo' ->
  exists stB E1, sts = [stN; stB] /\ env_ext (s_next st) E E1 /\ st_ok asegs OPS E1 stB msP mo'.
Proof.
  intros st sts E ms mo r hargs wnl st1 kf sh cred h1 h2 h3 h4 h5 stN L RNG sta LBa aw p lenf n rr RNG' msP mo'
         HS CP FS CF FT FOKk NV TCAN HA SHAPE NCP PRA H1 H2 H3 H4 H5 -> WLf0 HP En R HQ ACP MINVo OTH.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & AR & TI)).
  destruct (afree_ok_inv E st ms mo HS wnl kf sh FOKk) as (rf & lenf' & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  rewrite WLf0 in WLf. injection WLf as <-. pose proof WLf0 as WLf.
  assert (NOPR : ~ In prist_win (wins_of E nn rest)).
  { intros IP. apply (CtrPre.prist_absent_not_in E st hargs (so_facts _ _ _ _ _ _ HS) Hf PRA). exists hargs, md, A, nw, rest. rewrite <- Nn. auto. }
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  destruct HQ as (FPLE & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV' & STK' & PRES & TWP & POSTB).
  destruct (snd rr) as [q|] eqn:SR; [| contradiction].
  destruct POSTB as (UB & srcb & junk & EA0 & BRN & AH' & _ & _ & _ & _ & _ & PATN).
  specialize (ACP UB). cbv beta iota in ACP.
  rewrite Eh, heap_A_eq in HA. injection HA as <-.
  set (R' := mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) t0 t1 t2 (AP.getr R 8) (AP.getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) t3 t4 t5 t6) in *.
  set (Fv := CtrPost.cfvA R' (Z_to_bv 64 UB) (Z_to_bv 64 (shad UB))).
  set (Gv := fun (_ : Z) (o : Z) => match m' (ALib.Mem.wa (UB + o)) with Some b => b | None => Z_to_bv 8 0 end).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.reg_of_X1, (GlueA.getr_RA asegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.den_wlit. }
  assert (EMS' : msP = CtrFrame.ms' ms r R' m').
  { rewrite EMS. unfold CtrFrame.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  eexists. exists (CtrFrame.E' E st Fv Gv). split; [reflexivity|]. split; [apply CtrFrame.EXT|]. rewrite EMS'.
  assert (KBE : s_next (clobber st1) = kB st) by (eapply kB_next; eassumption).
  assert (KSE : PrimInt63.add (kB st) 1%uint63 = kS st) by (eapply kS_next; eassumption).
  rewrite KBE in H4. rewrite KBE, KSE in H5.
  assert (WORLD : aw_holds_asan AI ACCT UNIV (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) (LBr E LB kf lenf UB n) m' mo').
  { exact (WORLDr_asan E ms mo LB aw L RNG sta LBa W WOF AR kf lenf p q UB n RNG' (fst rr) m' mo' (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) HP AH' ACP PRES TWP PATN). }
  eapply (realloc_post E st ms mo HS wnl nn rest LB aw L RNG sta LBa NW AN WF W WOF AR TI NOPR
            (CtrFree.cvu_of Cw Cw_vec_unowned E st (ms_mem ms) LB nn md A nw rest ltac:(rewrite <- Eh; exact Hf) Nn HC) kf sh NV TCAN rf lenf lent Frf WLf WLt BTs LO0 POSf LEf OTHERS
            p q UB n RNG' (fst rr) m' mo' (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) HP AH' ACP PRES TWP PATN hargs md A nw Hf Eh Tnw Nn Ln FOK Fv Gv h1 h2 H1 H2)
    with (pd := prim_decided (s_facts st) (getr st X11)) (ks := ks) (offs := offs) (rss := rss) (ksp := ksp) (R' := R') (h3 := h3) (h4 := h4); try eassumption; try reflexivity.
  -   unfold nsv. symmetry. exact En.
  -   intros o Ho. unfold Gv, rb.
    destruct (aw_user_ok_asan AI ACCT UNIV AI_fake _ _ m' mo' (UB, n) (UB + o) WORLD ltac:(right; left; reflexivity) ltac:(unfold in_iv; cbn [fst snd]; lia)) as [MP _].
    unfold ALib.Mem.wa. destruct (m' (Z_to_bv 64 (UB + o))); [reflexivity| contradiction].
  -   intros rg Hrg. unfold CtrFrame.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
  -   intros x i Hx. exact (CtrPost.cfvA_clob R' _ _ x i Hx).
  -
    pose proof (so_facts _ _ _ _ _ _ HS) as HF9. unfold f_cred, cred_fact, cred_pre, nsv in *.
    try (rewrite Eh, heap_A_eq in HA; injection HA as <-). apply andb_prop in NCP as [NX9 NC9].
    destruct (prim_decided (s_facts st) (getr st X11)); cbn [fact_holds].
    + exact (KnownA.KnownA.known_leu_sound E _ _ _ HF9 NX9).
    + cbn [orb] in NC9. exact (KnownA.KnownA.known_leu_sound E _ _ _ HF9 NC9).
Qed.

End Realloc.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB ARealloc_x.TwinB.
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

Definition arealloc_stB (st st1 : sstate) (r : int) (h5 : list sv) (kf sh : int) (cred : sv) : sstate :=
  let n := getr st X11 in
  let st2 := clobber st1 in
  let k := s_next st2 in
  let sh' := PrimInt63.add k 1%uint63 in
  let st4 := set_next (set_next st2 (PrimInt63.add k 1%uint63)) (PrimInt63.add sh' 1%uint63) in
  let R' := IMap.add sh' (twin_region n) (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty) (IMap.remove sh (IMap.remove kf (s_regs st4)))) in
  let st5 := set_ops (setregs st4 R') (set_op HEAP_ID h5 (s_ops st4)) in
  let st6 := addfact (addfact (addfact (addfact st5 (cred_fact (s_facts st) n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
               (FEq (VP sh' wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw))) in
  let st7 := addfacts st6 (and7_facts n) in
  setpc (setr st7 X10 (VP k wzero)) r.

Lemma arealloc_apply_shape : forall UNIV PCz st sts, arealloc_apply UNIV PCz st = Some sts ->
  exists r hargs wnl st1 kf sh cred h1 h2 h3 h4 h5 stN,
    acall_pre AREALLOC_ROOM (Some (UNIV, PCz)) st = Some (r, hargs, wnl, st1) /\ getr st X10 = VP kf wzero
    /\ find_twin (s_facts st) kf = Some sh /\ heap_A hargs = Some cred
    /\ afree_ok st wnl kf sh = true /\ no_views_on (s_facts st) (s_regs st) kf sh = true /\ twin_canon st wnl kf sh = true
    /\ KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (getr st X11) = true /\ reqmax_ok (s_facts st) (getr st X11) = true
    /\ size_shape_ok (s_facts st) (getr st X11) = true /\ cred_pre (s_facts st) (getr st X11) cred = true
    /\ prist_absent (s_facts st) hargs = true
    /\ heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK = Some h1 /\ heap_del_window_k h1 (VP sh wzero) K_TWIN = Some h2
    /\ heap_set_A h2 (cred_post (s_facts st) (getr st X11) cred) = Some h3
    /\ heap_add_window h3 (VP (s_next (clobber st1)) wzero) (getr st X11) (VL CtrLib.K_BLOCK) = Some h4
    /\ heap_add_window h4 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X11)) (VL K_TWIN) = Some h5
    /\ null_post hargs cred (clobber st1) r = Some stN
    /\ sts = [stN; arealloc_stB st st1 r h5 kf sh cred].
Proof.
  intros UNIV PCz st sts H. unfold arealloc_apply in H.
  destruct (acall_pre AREALLOC_ROOM (Some (UNIV, PCz)) st) as [[[[r hargs] wnl] st1]|] eqn:PRE; [|discriminate].
  destruct (getr st X10) as [|kf off| | | | | | | | |] eqn:X10E; try discriminate.
  destruct (find_twin (s_facts st) kf) as [sh|] eqn:FT; [|discriminate].
  destruct (heap_A hargs) as [cred|] eqn:HA; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate] end.
  apply andb_prop in CK as [CK PRA]. apply andb_prop in CK as [CK NC]. apply andb_prop in CK as [CK SS]. apply andb_prop in CK as [CK N1]. apply andb_prop in CK as [CK N0].
  apply andb_prop in CK as [CK NV]. apply andb_prop in CK as [CK TC]. apply andb_prop in CK as [OFF FOK]. apply weqb_eq in OFF. subst off.
  destruct (null_post hargs cred (clobber st1) r) as [stN|] eqn:NP; [|discriminate].
  destruct (heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK) as [h1|] eqn:H1; [|discriminate].
  destruct (heap_del_window_k h1 (VP sh wzero) K_TWIN) as [h2|] eqn:H2; [|discriminate].
  unfold fresh in H. cbv zeta in H. cbn [fst snd s_next set_next] in H.
  destruct (heap_set_A h2 (cred_post (s_facts st) (getr st X11) cred)) as [h3|] eqn:H3; [|discriminate].
  destruct (heap_add_window h3 (VP (s_next (clobber st1)) wzero) (getr st X11) (VL CtrLib.K_BLOCK)) as [h4|] eqn:H4; [|discriminate].
  destruct (heap_add_window h4 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X11)) (VL K_TWIN)) as [h5|] eqn:H5; [|discriminate].
  injection H as <-.
  exists r, hargs, wnl, st1, kf, sh, cred, h1, h2, h3, h4, h5, stN. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Section Realloc.
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
Hypothesis Cw_ghost_free : forall md ca LB ws m b n ws', cw_holds Cw md ca LB ws m -> In (Win b n K_TWINz) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n K_TWINz) -> cw_holds Cw md ca (remove iv_eq_dec (b, n) LB) ws' m.

Hypothesis Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds Cw md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.

Hypothesis Cw_vec_unowned : forall md ca LB ws m i a, cw_holds Cw md ca LB ws m -> In i (VECS md) -> nth_error ca i = Some a -> bv_unsigned a <> 0 ->
  forall w, In w ws -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned a.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.

Lemma afree_ok_k_inv : forall (kdB kdT : w64) E st ms mo wnl kf sh, st_ok bsegs OPS E st ms mo -> afree_ok_k kdB kdT st wnl kf sh = true ->
  exists rf lenf lent,
  IMap.find kf (s_regs st) = Some rf /\ CtrA.win_lookup wnl kf = Some (lenf, kdB) /\ CtrA.win_lookup wnl sh = Some (lent, kdT)
  /\ block_of_twin (s_facts st) sh = Some kf /\ rg_lo rf = 0%uint63
  /\ 0 < hiZ E rf /\ hiZ E rf <= bv_unsigned (den E lenf)
  /\ forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
       (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
       \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len)
             /\ 0 < hiZ E r0 /\ rg_w r0 = true /\ (kd = kdB \/ hiZ E rf = bv_unsigned (den E lenf))).
Proof.
  intros kdB kdT E st ms mo wnl kf sh HS FOKk.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF. unfold afree_ok_k in FOKk. cbv zeta in FOKk.
  destruct (IMap.find kf (s_regs st)) as [rf|] eqn:Frf; [|discriminate].
  destruct (CtrA.win_lookup wnl kf) as [[lenf kdf]|] eqn:WLf; [|discriminate].
  destruct (CtrA.win_lookup wnl sh) as [[lent kdt]|] eqn:WLt; [|discriminate].
  destruct (block_of_twin (s_facts st) sh) as [kb|] eqn:BT; [|discriminate].
  do 6 (apply andb_prop in FOKk as [FOKk ?]).
  rename H into ALL, H0 into LEQ, H1 into POS, H2 into LO0, H3 into KBE, H4 into KDT.
  apply weqb_eq in FOKk. subst kdf. apply weqb_eq in KDT. subst kdt. apply Uint63.eqb_correct in KBE. subst kb. apply Uint63.eqb_correct in LO0.
  pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF POS) as POS'. cbn [den] in POS'. rewrite wbv_unsigned, wzero_ok in POS'.
  pose proof (KnownA.TwinB.KnownA.known_leu_q_sound E _ _ _ HF LEQ) as LEQ'.
  exists rf, lenf, lent. repeat (split; [reflexivity || assumption|]).
  intros k len kd Hin NKf NKs. pose proof (proj1 (forallb_forall _ _) ALL _ Hin) as X. cbv beta iota in X.
  apply Uint63.eqb_false_spec in NKf, NKs. rewrite NKf, NKs in X. cbn [orb] in X.
  destruct (weqb kd K_TWIN) eqn:KT.
  - left. split; [reflexivity|]. destruct (block_of_twin (s_facts st) k) as [kb|]; [|discriminate]. exists kb. split; [reflexivity|].
    apply negb_true_iff in X. apply Uint63.eqb_false_spec in X. exact X.
  - right. split; [reflexivity|].
    destruct (IMap.find k (s_regs st)) as [r0|] eqn:Fr0; [|discriminate]. exists r0. split; [reflexivity|].
    apply andb_prop in X as [X KB]. apply andb_prop in X as [X W]. apply andb_prop in X as [X P0]. apply andb_prop in X as [L0 LE0]. apply Uint63.eqb_correct in L0.
    pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF P0) as P0'. cbn [den] in P0'. rewrite wbv_unsigned, wzero_ok in P0'.
    split; [exact L0|]. split; [exact (KnownA.TwinB.KnownA.known_leu_q_sound E _ _ _ HF LE0)|]. split; [exact P0'|]. split; [exact W|].
    apply orb_prop in KB as [KB|FULL]; [left; apply weqb_eq; exact KB| right].
    pose proof (KnownA.TwinB.KnownA.known_eq_sound E _ _ _ HF FULL) as EQ. unfold hiZ. rewrite EQ. reflexivity.
Qed.

Section REALLOCD.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok bsegs OPS E st ms mo.
Variables (wnl : list (int * sv * w64)) (nn : nat) (rest : list sv) (LB : blocks) (aw : word)
          (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock).
Hypothesis NW : CtrA.nonstack_windows nn rest = Some wnl.
Hypothesis AN : CtrA.windows_anchored (s_regs st) wnl = true.
Hypothesis WF : windows_wf (wins_of E nn rest) LB (ATOP + 4096).

Variable WW : wit.
Hypothesis WOF : wit_of WW L RNG sta LBa.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis TI : ties WW (wins_of E nn rest).
Hypothesis NOPR : ~ In prist_win (wins_of E nn rest).

Hypothesis CVU : forall kb, In kb (carg_vecs st) -> bv_unsigned (ev E kb) <> 0 -> forall w, In w (wins_of E nn rest) -> w_kind w = K_BLOCK -> 0 < w_len w -> w_lo w <> bv_unsigned (ev E kb).
Variables (kf sh : int).
Hypothesis FT : find_twin (s_facts st) kf = Some sh.
Hypothesis FOKk : afree_ok st wnl kf sh = true.
Hypothesis NV : no_views_on (s_facts st) (s_regs st) kf sh = true.
Hypothesis TCAN : twin_canon st wnl kf sh = true.

Lemma afree_ok_inv : exists rf lenf lent,
  IMap.find kf (s_regs st) = Some rf /\ CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK) /\ CtrA.win_lookup wnl sh = Some (lent, K_TWIN)
  /\ block_of_twin (s_facts st) sh = Some kf /\ rg_lo rf = 0%uint63
  /\ 0 < hiZ E rf /\ hiZ E rf <= bv_unsigned (den E lenf)
  /\ forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
       (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
       \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len)
             /\ 0 < hiZ E r0 /\ rg_w r0 = true /\ (kd = CtrLib.K_BLOCK \/ hiZ E rf = bv_unsigned (den E lenf))).
Proof. exact (afree_ok_k_inv CtrLib.K_BLOCK K_TWIN E st ms mo wnl kf sh HS FOKk). Qed.

Variables (rf : region) (lenf lent : sv).
Hypothesis Frf : IMap.find kf (s_regs st) = Some rf.
Hypothesis WLf : CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK).
Hypothesis WLt : CtrA.win_lookup wnl sh = Some (lent, K_TWIN).
Hypothesis BTs : block_of_twin (s_facts st) sh = Some kf.
Hypothesis LO0 : rg_lo rf = 0%uint63.
Hypothesis POSf : 0 < hiZ E rf.
Hypothesis LEf : hiZ E rf <= bv_unsigned (den E lenf).
Hypothesis OTHERS : forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
  \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len)
        /\ 0 < hiZ E r0 /\ rg_w r0 = true /\ (kd = CtrLib.K_BLOCK \/ hiZ E rf = bv_unsigned (den E lenf))).

Let Af : Z := bv_unsigned (ev E kf).
Let nf : Z := bv_unsigned (den E lenf).

Lemma AWHf : aw_holds_asan AI ACCT UNIV aw LB (ms_mem ms) mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.

Lemma KB1 : w2Z CtrLib.K_BLOCK = 1. Proof. reflexivity. Qed.
Lemma KT9 : w2Z K_TWIN = 9. Proof. reflexivity. Qed.

Lemma entry_window : forall k len kd, In (k, len, kd) wnl ->
  k <> 0%uint63 /\ In (Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z kd)) (wins_of E nn rest)
  /\ exists b, In b LB /\ (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a)
       /\ (kd = CtrLib.K_BLOCK -> b = (bv_unsigned (ev E k), bv_unsigned (den E len))).
Proof.
  intros k len kd Hin. destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k len kd NW Hin) as (K0 & _ & KD & INW).
  split; [exact K0|]. split; [exact INW|].
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
  - exfalso. exact (KD KS0).
  - eexists. split; [exact B|]. split; [intros a Ha; exact Ha| reflexivity].
  - exists b. split; [exact Hb|]. split; [exact SUB|]. intros ->. rewrite KB1 in KS2. unfold K_SUB in KS2. lia.
Qed.

Lemma blockLB : In (Af, nf) LB.
Proof.
  destruct (entry_window kf lenf CtrLib.K_BLOCK (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as (_ & _ & b & Hb & _ & EQ). rewrite (EQ eq_refl) in Hb. exact Hb.
Qed.

Lemma nf_small : 0 <= Af /\ 1 <= nf /\ Af + nf < 2 ^ 48.
Proof.
  destruct (aw_blocks_ok_asan AI IMGX IMGX_aci ACCT UNIV AI_fake aw LB (ms_mem ms) mo (Af, nf) AWHf blockLB) as (B1 & B2 & B3 & _). cbn [fst snd] in *.
  unfold aw_ceiling_asan in B3. pose proof atop_range. unfold hiZ in *. fold nf in LEf. lia.
Qed.

Lemma twin_sh : exists rs, IMap.find sh (s_regs st) = Some rs /\ is_twin_region rs lenf = true /\ len_is_twin (s_facts st) lent lenf = true
  /\ bv_unsigned (ev E sh) = shad Af /\ bv_unsigned (den E lent) = shlen (nf + 7).
Proof.

  destruct (CallA.TwinB.twin_canon_inv st wnl kf sh TCAN) as (rs & n0 & kdn & lent0 & kdt & FR & WLn & WLt0 & TR & _ & LEN & _).
  rewrite WLf in WLn. injection WLn as <- <-. rewrite WLt in WLt0. injection WLt0 as <- <-.
  exists rs. split; [exact FR|]. split; [exact TR|]. split; [exact LEN|].
  destruct nf_small as (A0 & N1 & SM).
  split.
  - rewrite (CallA.TwinB.block_of_twin_sound E _ sh kf (so_facts _ _ _ _ _ _ HS) BTs). fold Af. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. clear - A0 SM N1. Z.div_mod_to_equations. lia.
  - rewrite (CallA.TwinB.len_is_twin_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) LEN) by (fold nf; lia). fold nf. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma owner : user_band Af /\ In (shad Af, shlen (nf + 7)) LB /\ (exists p, In (HB p Af nf) LBa /\ In (HB p Af nf) (w_T WW))
  /\ 1 <= nf <= AREQMAX /\ Af mod 16 = 0.
Proof.
  destruct twin_sh as (rs & _ & _ & _ & ESH & ELT).
  destruct (entry_window sh lent K_TWIN (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as (_ & INW & _). rewrite ESH, ELT, KT9 in INW.

  destruct TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as ESA ESL.
  destruct AR as [HWw EMw]. destruct WOF as (_ & _ & _ & ELB).
  destruct (twin_owner_w AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b Af nf HWw HbT blockLB ESA) as (EA & EN & NR).
  destruct (twin_T_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b HWw HbT) as (HbL & _ & _ & HTW & (p & EB) & _ & AL & UB & _).
  unfold twin_iv in HTW. rewrite <- EA, <- EN in HTW. rewrite <- EA in AL, UB. rewrite <- EN in NR. rewrite <- EA, <- EN in EB.
  split; [exact UB|]. split; [exact HTW|]. split; [| split; [exact NR| exact AL]].
  exists p. rewrite <- EB. split; [rewrite <- ELB; exact HbL| exact HbT].
Qed.

Lemma freed_pattern : ablock_shadow (ms_mem ms) Af nf.
Proof.
  destruct twin_sh as (rs & Frs & TRs & _ & ESH & _). destruct owner as (UBf & HTf & (p0 & HPL & HPT) & NRf & ALf).
  assert (SS : size_shape_ok (s_facts st) lenf = true).
  { destruct (CallA.TwinB.twin_canon_inv st wnl kf sh TCAN) as (rs0 & n0 & kdn & lent0 & kdt & _ & WLn & _ & _ & SS0 & _). rewrite WLf in WLn. injection WLn as <- <-. exact SS0. }
  pose proof (so_reg _ _ _ _ _ _ HS sh rs Frs) as RO.
  destruct (entry_window sh lent K_TWIN (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as (SH0 & _).
  assert (SHNZ : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact SH0).
  pose proof (CallA.TwinB.size_shape_sound E _ lenf (so_facts _ _ _ _ _ _ HS) SS) as SHAPE.
  pose proof (CallA.TwinB.is_twin_region_sound bsegs (s_priv st) E (ms_mem ms) sh rs lenf RO SHNZ TRs) as PATR. fold nf in PATR. rewrite ESH in PATR.
  intros g G0 G1.
  assert (P1 : rb bsegs (ms_mem ms) (shad Af + g) = Some (Z_to_bv 8 (if 8 * g + 8 <=? nf then 0 else nf - 8 * g))).
  { apply PATR; [unfold AREQMAX in NRf; lia| | exact G0| exact G1]. destruct lenf; try exact I; exact SHAPE. }

  destruct AR as [HWw _]. pose proof HWw as (_ & _ & _ & _ & _ & _ & _ & MAP & _).
  assert (MP : ms_mem ms (ALib.Mem.wa (shad Af + g)) <> None).
  { apply MAP. apply in_ivs_In. exists (twin_iv (HB p0 Af nf)). split; [apply in_map; exact HPT|].
    unfold in_iv, twin_iv. cbn [fst snd ab_addr ab_size]. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear -G0 G1. Z.div_mod_to_equations. lia. }
  unfold rb in P1. unfold ALib.Mem.wa in *. destruct (ms_mem ms (Z_to_bv 64 (shad Af + g))) as [y|]; [exact P1| contradiction].
Qed.

Lemma region_first_byte : forall k r0, IMap.find k (s_regs st) = Some r0 -> rg_lo r0 = 0%uint63 -> 0 < hiZ E r0 ->
  bv_unsigned (ev E k) + loZ r0 <= bv_unsigned (ev E k) < bv_unsigned (ev E k) + hiZ E r0.
Proof. intros k r0 _ L0 P. unfold loZ. rewrite L0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. lia. Qed.

Lemma kept_block_w : forall k len kd r0 b, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  IMap.find k (s_regs st) = Some r0 -> rg_lo r0 = 0%uint63 -> hiZ E r0 <= bv_unsigned (den E len) -> 0 < hiZ E r0 -> rg_w r0 = true ->
  (kd = CtrLib.K_BLOCK \/ hiZ E rf = nf) ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
  b <> (Af, nf) /\ b <> (shad Af, shlen (nf + 7)).
Proof.
  intros k len kd r0 b Hin NKf NKs Fr0 L0 LE0 P0 W0 CASE Hb SUB.
  destruct (entry_window k len kd Hin) as (K0 & _ & b1 & Hb1 & SUB1 & EQ1).
  destruct (entry_window kf lenf CtrLib.K_BLOCK (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as (Kf0 & _).
  destruct (entry_window sh lent K_TWIN (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as (Ks0 & _).
  assert (ZK : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  assert (ZF : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kf0).
  assert (ZS : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ks0).
  assert (A0IN : in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) (bv_unsigned (ev E k))) by (unfold in_iv; cbn [fst snd]; lia).
  pose proof (SUB _ A0IN) as INB. pose proof (region_first_byte k r0 Fr0 L0 P0) as RK.
  split; intros ->.
  -
    unfold in_iv in INB. cbn [fst snd] in INB.
    assert (INF : bv_unsigned (ev E kf) + loZ rf <= bv_unsigned (ev E k) < bv_unsigned (ev E kf) + hiZ E rf).
    { unfold loZ. rewrite LO0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. fold Af. destruct CASE as [->|FULL]; [| lia].

      pose proof (EQ1 eq_refl) as E1. subst b1.
      destruct (Z.eq_dec (bv_unsigned (ev E k)) Af) as [EA|NA]; [lia| exfalso].
      apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ (Af, nf) (bv_unsigned (ev E k)) AWHf Hb1 blockLB); [cbn [fst]; exact NA| exact A0IN|].
      unfold in_iv. cbn [fst snd]. lia. }
    exact (so_disj _ _ _ _ _ _ HS k r0 kf rf Fr0 Frf NKf ZK ZF (or_introl W0) _ (conj RK INF)).
  -
    destruct twin_sh as (rs & Frs & TRs & _ & ESH & _). unfold in_iv in INB. cbn [fst snd] in INB.
    unfold is_twin_region in TRs. cbv zeta in TRs. do 4 (apply andb_prop in TRs as [TRs ?]).
    apply Uint63.eqb_correct in TRs. match goal with X : sv_eqb (rg_hi rs) _ = true |- _ => apply sv_eqb_eq in X; rewrite CallA.TwinB.twin_region_hi in X; rename X into HIs end.
    destruct nf_small as (A0 & N1 & SM).
    assert (INS : bv_unsigned (ev E sh) + loZ rs <= bv_unsigned (ev E k) < bv_unsigned (ev E sh) + hiZ E rs).
    { unfold loZ, hiZ. rewrite TRs, HIs, (CallA.TwinB.twin_len_den E lenf) by (fold nf; lia). fold nf. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0, ESH.
      unfold shlen in INB. rewrite Z.shiftr_div_pow2 in INB by lia. change (2 ^ 3) with 8 in INB. lia. }
    exact (so_disj _ _ _ _ _ _ HS k r0 sh rs Fr0 Frs NKs ZK ZS (or_introl W0) _ (conj RK INS)).
Qed.

Lemma kept_block : forall k len kd b, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
  b <> (Af, nf) /\ b <> (shad Af, shlen (nf + 7)).
Proof.
  intros k len kd b Hin NKf NKs Hb SUB.
  destruct (OTHERS k len kd Hin NKf NKs) as [[KT (kb & BTk & NKB)]|(KT & r0 & Fr0 & L0 & LE0 & P0 & W0 & CASE)].
  2:{ exact (kept_block_w k len kd r0 b Hin NKf NKs Fr0 L0 LE0 P0 W0 CASE Hb SUB). }

  destruct (CallA.TwinB.twin_canon_inv st wnl kf sh TCAN) as (? & ? & ? & ? & ? & _ & _ & _ & _ & _ & _ & TAP & _).
  destruct (CallA.TwinB.twins_apart_inv _ _ _ _ _ _ k len kd TAP Hin KT NKs) as [OLD|EVA].
  2:{ destruct (CallV.TwinB.twin_ev_cases E _ _ _ _ _ _ _ (so_facts _ _ _ _ _ _ HS) EVA) as (kb2 & BT2 & LW & AL & EVD).
      rewrite BTk in BT2. injection BT2 as <-.
      pose proof (GTwinSub.GTwinSub.mod8_of_align E _ kb (so_facts _ _ _ _ _ _ HS) AL) as K8.

      destruct (entry_window k len kd Hin) as (_ & INWk & _). apply weqb_eq in KT. subst kd. rewrite KT9 in INWk.
      destruct TI as (_ & T2 & _). destruct (T2 _ INWk eq_refl) as (b2 & Hb2T & EIV). unfold w_iv in EIV. cbn [w_lo w_len] in EIV.
      pose proof AR as [HWw _].
      destruct (twin_T_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b2 HWw Hb2T) as (_ & _ & _ & _ & _ & NR2 & AL2 & UB2 & NUB2).
      assert (EB : b = twin_iv b2).
      { apply (twin_container AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b2 b HWw Hb2T Hb). rewrite <- EIV. exact SUB. }
      unfold twin_iv in EIV. injection EIV as ESA ESL.
      destruct owner as (UBf & HTf & _ & NRf & ALf).
      subst b. unfold twin_iv. split.
      - intros X. apply (f_equal fst) in X. cbn [fst] in X. apply NUB2. rewrite X. exact UBf.
      - intros X. injection X as XA XL.

        destruct nf_small as (A0 & N1 & SM).
        pose proof (CallA.TwinB.block_of_twin_sound E _ k kb (so_facts _ _ _ _ _ _ HS) BTk) as LK.
        pose proof (bv_unsigned_in_range 64 (ev E kb)) as RKB. change (bv_modulus 64) with (2 ^ 64) in RKB.
        rewrite Z.mod_small in LK by (clear - RKB; Z.div_mod_to_equations; lia).
        assert (EKB : bv_unsigned (ev E kb) = Af).
        { rewrite ESA, XA in LK. unfold shad, ASHOFF in LK. rewrite Z.shiftr_div_pow2 in LK by lia. change (2 ^ 3) with 8 in LK.
          clear - LK K8 ALf. Z.div_mod_to_equations. lia. }
        destruct EVD as [CVk|(ks & lens & kds & rsub & Hins & NXs & NKBs & NKTs & Frsub & RWs & L0s & HPOS & XLO & XHI)].
        {
          destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl kf lenf CtrLib.K_BLOCK NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as (_ & _ & _ & INk).
          assert (AFNZ : Af <> 0).
          { destruct owner as (_ & _ & (p0 & HP0 & _) & _). pose proof AR as [(AH0 & _) _]. destruct WOF as (_ & _ & _ & E4w). rewrite E4w in AH0.
            destruct (heap_block_facts AI _ _ _ _ _ (HB p0 Af nf) AH0 HP0 ltac:(exists p0; reflexivity)) as (_ & (BK0 & _) & _). unfold ablk, AIMG_HI, KLS in BK0. cbn [ab_addr ab_size] in BK0. lia. }
          apply (CVU kb CVk ltac:(rewrite EKB; exact AFNZ) _ INk); [reflexivity| cbn [w_len]; fold nf; lia| cbn [w_lo]; fold Af; symmetry; exact EKB]. }
        assert (XIN : Af <= bv_unsigned (ev E ks) < Af + nf).
        { rewrite ESL, XL in XHI. rewrite EKB in XLO, XHI. unfold shlen in XHI. rewrite Z.shiftr_div_pow2 in XHI by lia. change (2 ^ 3) with 8 in XHI.
          clear - XLO XHI N1. Z.div_mod_to_equations. lia. }
        destruct (entry_window ks lens kds Hins) as (Ks0 & _).
        destruct (entry_window kf lenf CtrLib.K_BLOCK (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as (Kf0 & _).
        assert (ZKs : PrimInt63.eqb ks 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ks0).
        assert (ZF : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kf0).
        assert (NSs : ks <> sh).
        { intros ->. destruct twin_sh as (rs & Frs & TRs & _). rewrite Frsub in Frs. injection Frs as <-.
          unfold is_twin_region in TRs. cbv zeta in TRs. do 2 (apply andb_prop in TRs as [TRs ?]). apply andb_prop in TRs as [_ RO].
          rewrite RWs in RO. discriminate RO. }
        destruct (OTHERS ks lens kds Hins NXs NSs) as [[KTs _]|(_ & r0s & Fr0s & _ & _ & _ & _ & CASEs)]; [rewrite NKTs in KTs; discriminate KTs|].
        destruct CASEs as [KB|FULL]; [exact (NKBs KB)|].
        pose proof (region_first_byte ks rsub Frsub L0s HPOS) as RKs.
        assert (INF : bv_unsigned (ev E kf) + loZ rf <= bv_unsigned (ev E ks) < bv_unsigned (ev E kf) + hiZ E rf).
        { unfold loZ. rewrite LO0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. fold Af. rewrite FULL. fold nf. lia. }
        exact (so_disj _ _ _ _ _ _ HS ks rsub kf rf Frsub Frf NXs ZKs ZF (or_introl RWs) _ (conj RKs INF)). }
  destruct (CallA.TwinB.twin_arm_old_inv _ _ _ _ _ OLD) as (kb' & rk & n2 & BT2 & FRk & WL2 & LEN2 & _).
  rewrite BTk in BT2. injection BT2 as <-.
  pose proof (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL2) as IN2.
  assert (NKBs : kb <> sh). { intros ->. rewrite WLt in WL2. apply (f_equal (fun o => match o with Some (_, kd0) => w2Z kd0 | None => 0 end)) in WL2. vm_compute in WL2. discriminate WL2. }
  destruct (entry_window kb n2 CtrLib.K_BLOCK IN2) as (Kb0 & _ & b2 & Hb2 & SUB2 & EQ2). pose proof (EQ2 eq_refl) as E2. subst b2.
  set (A2 := bv_unsigned (ev E kb)) in *. set (N2 := bv_unsigned (den E n2)) in *.

  destruct (OTHERS kb n2 CtrLib.K_BLOCK IN2 NKB NKBs) as [[X _]|(_ & r2 & Fr2 & L2 & LE2 & P2 & W2 & CASE2)]; [discriminate X|].
  destruct (kept_block_w kb n2 CtrLib.K_BLOCK r2 (A2, N2) IN2 NKB NKBs Fr2 L2 LE2 P2 W2 CASE2 Hb2 ltac:(intros a Ha; exact Ha)) as [NEB _].
  destruct (aw_blocks_ok_asan AI IMGX IMGX_aci ACCT UNIV AI_fake aw LB (ms_mem ms) mo (A2, N2) AWHf Hb2) as (B1 & B2 & B3 & _). cbn [fst snd] in B1, B2, B3.
  unfold aw_ceiling_asan in B3. pose proof atop_range as ATR.
  assert (N2pos : 1 <= N2) by (unfold hiZ in *; fold N2 in LE2; lia).
  assert (EK : bv_unsigned (ev E k) = shad A2).
  { rewrite (CallA.TwinB.block_of_twin_sound E _ k kb (so_facts _ _ _ _ _ _ HS) BTk). fold A2. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. clear - B1 B3 N2pos ATR. Z.div_mod_to_equations. lia. }
  assert (EL : bv_unsigned (den E len) = shlen (N2 + 7)).
  { rewrite (CallA.TwinB.len_is_twin_sound E _ _ _ (so_facts _ _ _ _ _ _ HS) LEN2) by (fold N2; lia). fold N2. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite EK, EL in SUB.

  destruct (entry_window k len kd Hin) as (_ & INWk & _). rewrite EK, EL in INWk. apply weqb_eq in KT. subst kd. rewrite KT9 in INWk.
  destruct TI as (_ & T2 & _). destruct (T2 _ INWk eq_refl) as (b2 & Hb2T & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as ESA ESL.
  pose proof AR as [HWw _].
  destruct (twin_owner_w AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b2 A2 N2 HWw Hb2T Hb2 ESA) as (EA2 & EN2 & NR2).
  destruct (twin_T_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b2 HWw Hb2T) as (_ & _ & _ & _ & _ & _ & AL2 & UB2 & NUB2).
  rewrite <- EA2 in AL2, NUB2.

  assert (EB : b = (shad A2, shlen (N2 + 7))).
  { rewrite EA2, EN2. apply (twin_container AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b2 b HWw Hb2T Hb). unfold twin_iv. rewrite <- EA2, <- EN2. exact SUB. }
  destruct owner as (UBf & HTf & _ & NRf & ALf).
  subst b. split.
  - intros X. apply (f_equal fst) in X. cbn [fst] in X. apply NUB2. rewrite X. exact UBf.
  - intros X. apply (f_equal fst) in X. cbn [fst] in X. apply NEB.
    assert (EA : A2 = Af) by (unfold shad in X; rewrite !Z.shiftr_div_pow2 in X by lia; change (2 ^ 3) with 8 in X; clear - X AL2 ALf; Z.div_mod_to_equations; lia).
    rewrite EA in *. f_equal. exact (LB_same_addr AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo Af N2 nf HWw Hb2 blockLB).
Qed.

Variables (p q : aptr) (UBk N : Z) (RNG' : footprint) (sta' : astate) (m' : amem) (mo' : Model) (aw' : word).
Hypothesis HP : In (HB p Af nf) LBa.
Hypothesis AH' : AHEAP AI L RNG' sta' (HB q UBk N :: lb_remove p LBa) m'.
Hypothesis AC' : ACCT aw' L RNG' sta' (HB q UBk N :: lb_remove p LBa) mo'.
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis PRES : aheap_pres (aci AI) (lb_remove p LBa) sp (ms_mem ms) m'.
Hypothesis TWP : twins_pres (lb_remove p LBa) (ms_mem ms) m'.
Hypothesis PATN : ablock_shadow m' UBk N.
Definition LBk : blocks := LB_free LB Af nf.
Definition LBr : blocks := (shad UBk, shlen (N + 7)) :: (UBk, N) :: LBk.
Definition Tr : list ablock := List.filter (fun x => if ablock_eq_dec x (HB p Af nf) then false else true) (w_T WW).

Definition Wr : wit := mkWit (w_L WW) RNG' sta' (HB q UBk N :: lb_remove p (w_LBa WW)) (HB q UBk N :: Tr) (w_FA WW) m' (w_zc WW).

Lemma NEWBr : 1 <= N <= AREQMAX /\ ablock_range UBk N /\ ALib.Mem.wr_at bsegs m' UBk N.
Proof.
  destruct (heap_block_facts AI L RNG' sta' _ m' (HB q UBk N) AH' ltac:(left; reflexivity) ltac:(exists q; reflexivity)) as (A1 & A2 & A3).
  cbn [ab_addr ab_size] in *. auto.
Qed.

Lemma WORLDr : aw_holds_w AI ACCT UNIV Wr aw' LBr m' mo'
  /\ (forall g, 0 <= g -> 8 * g < N -> m' (ALib.Mem.wa (shad UBk + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? N then 0 else N - 8 * g)))
  /\ user_band UBk /\ (forall a, in_iv (UBk, N) a -> ~ in_user LBk a) /\ ~ In (shad UBk, shlen (N + 7)) ((UBk, N) :: LBk)
  /\ (forall a, in_iv (shad UBk, shlen (N + 7)) a -> ~ in_user LBk a).
Proof.
  destruct WOF as (E1 & E2 & E3 & E4).
  destruct (aw_real_realloc AI ACCT UNIV AI_fake aw aw' LB (ms_mem ms) mo WW RNG' sta' p Af nf q UBk N m' mo' sp AR
              ltac:(rewrite E4; exact HP) ltac:(rewrite E1, E4; exact AH') ltac:(rewrite E1, E4; exact AC') ltac:(rewrite E4; exact PRES) ltac:(rewrite E4; exact TWP) PATN)
    as (AR' & VB & NT & UB & DJ & DJT).
  destruct AR' as [HW1 _].
  destruct (twin_out_w AI ACCT UNIV AI_fake _ aw' _ m' mo' (HB q UBk N) HW1 VB ltac:(exists q; reflexivity) NT) as (AWH' & NIN & PAT).
  split; [exact AWH'|]. split; [exact PAT|]. split; [exact UB|]. split; [exact DJ|]. split; [exact NIN| exact DJT].
Qed.
Lemma WORLDr_asan : aw_holds_asan AI ACCT UNIV aw' LBr m' mo'.
Proof. exists Wr. exact (proj1 WORLDr). Qed.

Lemma SBr : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LBk a -> m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a).
Proof.
  intros a Ha ST. destruct WOF as (E1 & E2 & E3 & E4). pose proof AR as [HWw EMw]. pose proof HWw as (AH & HTw & _ & HFAw & _).
  assert (HPw : In (HB p Af nf) (w_LBa WW)) by (rewrite E4; exact HP).
  pose proof (LB_free_char AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo p Af nf HWw HPw) as CHAR. cbv zeta in CHAR.
  assert (RM : forall b, In b (lb_remove p (w_LBa WW)) -> In b (w_LBa WW)) by (intros b Hb; exact (proj1 (proj1 (lb_remove_In AI _ _ _ _ _ p Af nf b AH HPw) Hb))).
  apply (aw_real_stable AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo WW RNG' sta' (HB q UBk N :: lb_remove p LBa) m' (lb_remove p LBa) LBk sp (lb_remove p LBa) TWP);
    [| exact AR| rewrite E1; exact AH'| exact PRES| | | exact Ha| exact ST].
  {
    intros b HbO _ HvK. rewrite <- E4. apply (lb_remove_In AI _ _ _ _ _ p Af nf b AH HPw). split; [exact HbO|]. intros ->.
    unfold LBk in HvK. apply LB_free_In in HvK as (_ & _ & NE). apply NE. reflexivity. }
  - intros v Hv UB P. apply CHAR in Hv as [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
    + exists b. split; [rewrite <- E4; exact Hb| reflexivity].
    + exfalso. apply filter_In in Hb as [Hb _]. destruct (LB_twin_facts AI ACCT UNIV WW aw LB (ms_mem ms) mo b HWw Hb) as (T1 & T2 & T3).
      unfold user_band in UB. cbn [fst twin_iv] in UB. lia.
    + exfalso. destruct (LB_fsh_facts AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b HWw (conj (conj (RM b Hb) NF) HF)) as (T1 & T2 & T3 & _).
      unfold user_band in UB. cbn [fst fsh_iv] in UB. lia.
  - intros v Hv NUB. apply CHAR in Hv as [(b & [Hb NF] & ->)|[(b & Hb & ->)|(b & [[Hb NF] HF] & ->)]].
    + exfalso. destruct (LB_user_facts AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo b HWw (conj (RM b Hb) NF)) as (UP & B1 & B2 & _).
      apply NUB. unfold user_band. cbn [fst user_iv]. pose proof (usz_le b). lia.
    + left. exists b. apply filter_In in Hb as [Hb NE]. destruct (HTw b Hb) as [HbL HH].
      split; [exact HbL|]. split; [| split; [exact HH| reflexivity]].
      right. rewrite <- E4. apply (lb_remove_In AI _ _ _ _ _ p Af nf b AH HPw). split; [exact HbL|].
      destruct (ablock_eq_dec b (HB p Af nf)); [discriminate NE| assumption].
    + right. exists b. split; [exact (RM b Hb)|]. split; [rewrite <- E4; exact Hb|]. split; [exact HF| reflexivity].
Qed.
Lemma SBVr : forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LBk a ->
  rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true).
Proof. exact (CtrFrame.TwinB.SBV_of_raw (CtrFrame.TwinB.stableA AI ms LBk) (ms_mem ms) m' SBr). Qed.
Lemma WBMr : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
  wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true.
Proof. exact (CtrFrame.TwinB.WBM_of_pres AI _ _ _ _ PRES). Qed.

Definition KEEPf (k0 : int) : Prop := k0 <> kf /\ k0 <> sh.

Lemma WINKf : forall k0 len kd, KEEPf k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LBk a.
Proof.
  intros k0 len kd [NKf NKs] WL a Ha. pose proof (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL) as Hin.
  destruct (entry_window k0 len kd Hin) as (_ & _ & b & Hb & SUB & _).
  destruct (kept_block k0 len kd b Hin NKf NKs Hb SUB) as [N1 N2].
  apply in_ivs_In. exists b. split; [apply LB_free_In; auto|]. apply SUB. unfold in_iv. cbn [fst snd]. lia.
Qed.

Lemma VKEEPf : forall k0 rg hs n sh' len, IMap.find k0 (s_regs st) = Some rg -> zero_view rg = Some hs -> KEEPf k0 ->
  block_of_twin (s_facts st) k0 = Some n -> CallV.TwinB.view_parent (s_facts st) (s_regs st) n sh' ->
  CtrA.win_lookup wnl sh' = Some (len, K_TWIN) -> KEEPf sh'.
Proof.
  intros k0 rg hs n sh' len Fk ZV [NKf NKs] BT VPAR WL. split.
  - intros ->. rewrite WLf in WL. assert (X : CtrLib.K_BLOCK = K_TWIN) by congruence. vm_compute in X. discriminate X.
  - intros ->. unfold no_views_on in NV.
    pose proof (proj1 (IMap.forallb_spec _ _ (so_bst _ _ _ _ _ _ HS)) NV k0 rg Fk) as C. cbv beta in C.
    replace (PrimInt63.eqb k0 sh) with false in C by (symmetry; apply Uint63.eqb_false_spec; exact NKs).
    rewrite ZV, BT in C. destruct VPAR as [(kb & o1 & UB & TW)|(rshp & Frshp & HNp)];
      [rewrite UB, TW, Uint63.eqb_refl in C; cbn in C; discriminate C| rewrite Frshp, HNp in C; cbn [negb] in C; rewrite !Bool.andb_false_r in C; discriminate C].
Qed.

Lemma TKEEPf : forall k0 rg sh' kb n len, IMap.find k0 (s_regs st) = Some rg -> KEEPf k0 -> CtrA.win_lookup wnl sh' = Some (len, K_TWIN) ->
  block_of_twin (s_facts st) sh' = Some kb -> CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK) ->
  size_tail_ok (s_facts st) n = true -> tail_named (tail_rhs sh' n) k0 (s_facts st) = true -> KEEPf sh'.
Proof.
  intros k0 rg sh' kb n len Fk [NKf NKs] WL BT WLk ST TN. split.
  - intros ->. rewrite WLf in WL. assert (X : CtrLib.K_BLOCK = K_TWIN) by congruence. vm_compute in X. discriminate X.
  - intros ->. rewrite BTs in BT. injection BT as <-. rewrite WLf in WLk. injection WLk as <-.
    destruct (CallA.TwinB.twin_canon_inv st wnl kf sh TCAN) as (rs0 & n0 & kdn & lent0 & kdt & _ & WLn & _ & _ & _ & _ & _ & NTA). rewrite WLf in WLn. injection WLn as <- <-.
    exact (CallA.TwinB.no_tail_at_sound _ _ _ _ k0 rg (so_bst _ _ _ _ _ _ HS) NTA Fk TN).
Qed.
Lemma SBTf : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
  rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true).
Proof.
  intros a Ha SC _. apply (FrameV.TwinB.frame_v_of_raw bsegs).
  destruct SC as [(a' & R & ->)|(v & Hv & R)].
  - exact (proj1 (PRES (shad a') Ha ltac:(right; right; right; exists a'; split; [left; exact R| reflexivity]))).
  - destruct (IMGSH_aci v a Hv R) as (a' & INA & ->).
    exact (proj1 (PRES (shad a') Ha ltac:(right; right; right; exists a'; split; [right; left; exact INA| reflexivity]))).
Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Notation E' := (CtrFrame.TwinB.E' E st Fv Gv).
Lemma SBOf : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E') (op_args o))) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a).
Proof.
  intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI. destruct (OPS_fp_other _ _ a NI FP) as [R|[(a' & R & ->)|(a' & R & ->)]].
  - pose proof (SBr a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact R)) as E1. unfold ALib.Mem.wa in E1. exact E1.
  - pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [right; left; exact R| reflexivity]))) as E1.
    unfold ALib.Mem.wa in E1. exact E1.
  - pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact R| reflexivity]))) as E1.
    unfold ALib.Mem.wa in E1. exact E1.
Qed.

Variables (h1 h2 : list sv).
Hypothesis H1 : heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK = Some h1.
Hypothesis H2 : heap_del_window_k h1 (VP sh wzero) K_TWIN = Some h2.

Definition WBf : window := Win Af nf K_BLOCK.
Definition WTf : window := Win (shad Af) (shlen (nf + 7)) K_TWINz.

Lemma forallb_sub : forall {T} (f : T -> bool) l l', (forall x, In x l' -> In x l) -> forallb f l = true -> forallb f l' = true.
Proof. intros T f l l' SUB H. apply forallb_forall. intros x Hx. exact (proj1 (forallb_forall _ _) H x (SUB x Hx)). Qed.

Lemma forallb_skipn : forall {T} (f : T -> bool) j l, forallb f l = true -> forallb f (skipn j l) = true.
Proof.
  intros T f j. induction j as [|j IH]; intros l H; [exact H|]. destruct l as [|x l]; [reflexivity|]. cbn [skipn]. cbn [forallb] in H.
  apply andb_prop in H as [_ H]. exact (IH l H).
Qed.

Lemma anchors_perm : forall (l l' : list (int * sv * w64)), Permutation l l' -> Permutation (HeapCtrB.TwinB.anchors l) (HeapCtrB.TwinB.anchors l').
Proof. intros l l' P. unfold HeapCtrB.TwinB.anchors. apply Permutation_map. exact P. Qed.

Lemma DEL2 : exists l1 l2 m1 m2 nw2 rest2,
  h2 = VL md :: A :: VL nw2 :: rest2 /\ wt nw2 = false /\ pred (pred nn) = Z.to_nat (to_Z (wl nw2)) /\ (3 * pred (pred nn) <= length rest2)%nat
  /\ wins_of E (pred (pred nn)) rest2 = m1 ++ m2 /\ skipn (3 * pred (pred nn)) rest2 = skipn (3 * nn) rest
  /\ (forall x, In x rest2 -> In x rest) /\ (2 <= nn)%nat
  /\ wins_of E nn rest = l1 ++ WBf :: l2 /\ l1 ++ l2 = m1 ++ WTf :: m2
  /\ ~ In WBf (l1 ++ l2) /\ ~ In WTf (m1 ++ m2).
Proof.
  pose proof (HeapCtrB.TwinB.windows_anchored_nodup_anchors _ _ AN) as NDA.
  rewrite Eh in H1.
  destruct (CtrFree.TwinB.heap_del_window_k_facts E md A nw rest nn kf CtrLib.K_BLOCK h1 wnl eq_refl Tnw Nn Ln NW H1)
    as (ws1 & l1 & len1 & l2 & wl1 & EH1 & I1 & W1 & W1' & T1 & N1 & L1 & SK1 & NW1 & S1 & S2 & S3 & M1 & PM1).
  destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ kf len1 CtrLib.K_BLOCK lenf CtrLib.K_BLOCK AN I1 (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as [-> _].
  rewrite EH1 in H2.
  destruct (CtrFree.TwinB.heap_del_window_k_facts E md A (wsub nw wone) (ws1 ++ skipn (3 * nn) rest) (pred nn) sh K_TWIN h2 wl1 eq_refl T1 N1 L1 NW1 H2)
    as (ws2 & m1 & len2 & m2 & wl2 & EH2 & I2 & W2 & W2' & T2 & N2 & L2 & SK2 & NW2 & R1 & R2 & R3 & M2 & PM2).
  destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ sh len2 K_TWIN lent K_TWIN AN (S1 _ I2) (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as [-> _].
  destruct twin_sh as (rs & _ & _ & _ & ESH & ELT). destruct owner as (UBf & HTf & _ & NRf & ALf).

  assert (ND1 : List.NoDup (kf :: HeapCtrB.TwinB.anchors wl1)) by (exact (Permutation_NoDup (anchors_perm _ _ PM1) NDA)).
  apply List.NoDup_cons_iff in ND1 as [NKF1 ND1'].
  assert (ND2 : List.NoDup (sh :: HeapCtrB.TwinB.anchors wl2)) by (exact (Permutation_NoDup (anchors_perm _ _ PM2) ND1')).
  apply List.NoDup_cons_iff in ND2 as [NSH2 _].
  assert (ANCH : forall (l : list (int * sv * w64)) k len kd, In (k, len, kd) l -> In k (HeapCtrB.TwinB.anchors l)).
  { intros l k len kd H. unfold HeapCtrB.TwinB.anchors. apply in_map_iff. exists (k, len, kd). auto. }
  exists l1, l2, m1, m2, (wsub (wsub nw wone) wone), (ws2 ++ skipn (3 * pred nn) (ws1 ++ skipn (3 * nn) rest)).
  split; [exact EH2|]. split; [exact T2|]. split; [exact N2|]. split; [exact L2|]. split; [exact W2'|]. split; [rewrite SK2, SK1; reflexivity|].
  split; [intros x Hx; apply S3; apply R3; exact Hx|]. split; [lia|].
  split. { rewrite W1. unfold WBf. fold Af nf. rewrite KB1. reflexivity. }
  split. { rewrite <- W1', W2. unfold WTf. rewrite ESH, ELT, KT9. reflexivity. }
  split.
  - intros X. rewrite <- W1' in X.
    destruct (HeapCtrB.TwinB.wins_cover E (pred nn) _ wl1 WBf NW1 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_BLOCK, K_STACK in KS; lia|].
    unfold WBf in EW. injection EW as E1 E2 E3.
    assert (NKf : k <> kf) by (intros ->; exact (NKF1 (ANCH _ _ _ _ Ik))).
    assert (NKs : k <> sh).
    { intros ->. destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ sh len kd lent K_TWIN AN (S1 _ Ik) (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as [_ ->]. rewrite KT9 in E3. unfold K_BLOCK in E3. lia. }
    destruct (kept_block k len kd (Af, nf) (S1 _ Ik) NKf NKs blockLB ltac:(rewrite <- E1, <- E2; intros a Ha; exact Ha)) as [NE _]. exact (NE eq_refl).
  - intros X. rewrite <- W2' in X.
    destruct (HeapCtrB.TwinB.wins_cover E (pred (pred nn)) _ wl2 WTf NW2 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_TWINz, K_STACK in KS; lia|].
    unfold WTf in EW. injection EW as E1 E2 E3.
    assert (NKs : k <> sh) by (intros ->; exact (NSH2 (ANCH _ _ _ _ Ik))).
    assert (NKf : k <> kf) by (intros ->; exact (NKF1 (ANCH _ _ _ _ (R1 _ Ik)))).
    destruct (kept_block k len kd _ (S1 _ (R1 _ Ik)) NKf NKs HTf ltac:(rewrite <- E1, <- E2; intros a Ha; exact Ha)) as [_ NE]. exact (NE eq_refl).
Qed.

Definition kB : int := addn (s_next st) 15.
Definition kS : int := addn (s_next st) 16.
Definition nsv : sv := getr st X11.
Hypothesis NDEN : bv_unsigned (den E nsv) = N.
Hypothesis F15 : Fv 15 = Z_to_bv 64 UBk.
Hypothesis F16 : Fv 16 = Z_to_bv 64 (shad UBk).
Hypothesis GJ : forall o, 0 <= o < N -> rb bsegs m' (UBk + o) = Some (Gv 15 o).
Hypothesis SHAPE : size_shape_ok (s_facts st) nsv = true.

Lemma NXr : st_vars_below (s_next st) st = true /\ 0 < to_Z (s_next st) /\ to_Z (s_next st) + 256 <= 2 ^ 62.
Proof. exact (HeapCtr.TwinB.fresh_ok_inv st FOK). Qed.
Lemma nsv_below : sv_vars_below (s_next st) nsv = true.
Proof.
  destruct NXr as (SVB & _). unfold st_vars_below in SVB.
  apply andb_prop in SVB as [SVB _]. apply andb_prop in SVB as [SVB _]. apply andb_prop in SVB as [SVB _].
  apply andb_prop in SVB as [SVB _]. apply andb_prop in SVB as [H1' _]. exact (rf_allb_get _ _ _ H1' X11).
Qed.
Lemma kB_Z : to_Z kB = to_Z (s_next st) + 15.
Proof.
  destruct NXr as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold kB. rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma kS_Z : to_Z kS = to_Z (s_next st) + 16.
Proof.
  destruct NXr as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  unfold kS. rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma ev_kB : bv_unsigned (ev E' kB) = UBk.
Proof.
  unfold kB. rewrite (CtrFrame.TwinB.ev_E'_fresh E st FOK Fv Gv 15) by lia. change (Z.of_nat 15) with 15. rewrite F15. destruct NEWBr as (N1 & (BK & _ & TOP & _) & _).
  pose proof atop_range. unfold ablk, AIMG_HI, KLS in BK. apply Z_to_bv_small. unfold bv_modulus, two64. lia.
Qed.
Lemma ev_kS : bv_unsigned (ev E' kS) = shad UBk.
Proof.
  unfold kS. rewrite (CtrFrame.TwinB.ev_E'_fresh E st FOK Fv Gv 16) by lia. change (Z.of_nat 16) with 16. rewrite F16. destruct NEWBr as (N1 & BR & _).
  destruct (twin_band _ _ BR N1) as (T1 & T2 & T3 & _). apply Z_to_bv_small. unfold bv_modulus, two64. lia.
Qed.
Lemma kB_nz : PrimInt63.eqb kB 0%uint63 = false.
Proof. apply Uint63.eqb_false_spec. intros X. pose proof kB_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NXr as (_ & P & _). lia. Qed.
Lemma kS_nz : PrimInt63.eqb kS 0%uint63 = false.
Proof. apply Uint63.eqb_false_spec. intros X. pose proof kS_Z as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ. destruct NXr as (_ & P & _). lia. Qed.

Definition blk_region : region := Region 0%uint63 nsv true BGUnk IMap.empty.

Lemma blk_region_ok : region_ok bsegs (s_priv st) E' m' kB blk_region.
Proof.
  destruct NEWBr as (N1 & BR & WR). pose proof WORLDr_asan as AWH'.
  assert (EH : hiZ E' blk_region = N) by (unfold hiZ, blk_region; cbn [rg_hi]; rewrite (CtrFrame.TwinB.den_E' E st Fv Gv nsv nsv_below); exact NDEN).
  assert (EL : loZ blk_region = 0) by reflexivity.
  destruct BR as (BK & _ & TOP & _). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  constructor; rewrite ?ev_kB, ?EH, ?EL.
  - apply IMap.bst_empty.
  - intros _. unfold two64. lia.
  - intros _ a Ha.
    destruct (aw_user_ok_asan AI ACCT UNIV AI_fake aw' LBr m' mo' (UBk, N) a AWH' ltac:(right; left; reflexivity) ltac:(unfold in_iv; cbn [fst snd]; lia)) as [MP SEG].
    split; [| split; [| exact SEG]].
    + unfold rb. destruct (m' (Z_to_bv 64 a)); [discriminate| contradiction].
    + intros _. apply (GlueA.TwinB.wb_wviewA bsegs). destruct WR as (_ & _ & W). replace a with (UBk + (a - UBk)) by lia. apply W. lia.
  - intros g gr Hg. cbn [blk_region rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
  - intros g gr c i Hg. cbn [blk_region rg_cells] in Hg. rewrite IMap.find_empty in Hg. discriminate Hg.
  - intros o H1' _ _. specialize (H1' kB_nz). unfold bg_byte. cbn [blk_region rg_bg]. unfold CtrFrame.TwinB.E'. rewrite eg_above by (rewrite kB_Z; lia).
    rewrite kB_Z. replace (to_Z (s_next st) + 15 - to_Z (s_next st)) with 15 by lia. apply GJ. lia.
Qed.

Lemma twin_region_okA : region_ok bsegs (s_priv st) E' m' kS (twin_region nsv).
Proof.
  destruct NEWBr as (N1 & BR & WR). destruct WORLDr as (_ & PAT & _). pose proof WORLDr_asan as AWH'. destruct (twin_band _ _ BR N1) as (T1 & T2 & T3 & _).
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (CtrFrame.TwinB.den_E' E st Fv Gv nsv nsv_below); exact NDEN).
  apply (CallA.TwinB.twin_region_ok bsegs (s_priv st) E' m' kS nsv kS_nz); rewrite ?DN, ?ev_kS.
  - lia.
  - unfold AREQMAX in N1. lia.
  - pose proof (CallA.TwinB.size_shape_sound E' _ nsv (so_facts _ _ _ _ _ _ (CtrFrame.TwinB.HS' OPS E st ms mo HS FOK Fv Gv)) SHAPE) as X. rewrite DN in X. exact X.
  - unfold shlen in T2. rewrite Z.shiftr_div_pow2 in T2 by lia. change (2 ^ 3) with 8 in T2. unfold two64. lia.
  - intros g G0 G1. split.
    + pose proof (PAT g G0 G1) as P1. unfold rb. unfold ALib.Mem.wa in P1. rewrite P1. reflexivity.
    + apply (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw' LBr m' mo' _ (shad UBk + g) AWH' ltac:(left; reflexivity)
                     ltac:(unfold in_iv; cbn [fst snd]; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; clear - G0 G1; Z.div_mod_to_equations; lia))).
Qed.

Hypothesis N255 : (nn <= 255)%nat.
Hypothesis AWden : aw = den E A.
Variable pd : bool.
Hypothesis AW'E : aw' = Z_to_bv 64 (bv_unsigned aw - (if pd then 0 else N)).
Definition cred' : sv := if pd then A else sv_alu ALU_SUB A nsv.
Variables (h3 h4 h5 : list sv).
Hypothesis H3 : heap_set_A h2 cred' = Some h3.
Hypothesis H4 : heap_add_window h3 (VP kB wzero) nsv (VL CtrLib.K_BLOCK) = Some h4.
Hypothesis H5 : heap_add_window h4 (VP kS wzero) (twin_len nsv) (VL K_TWIN) = Some h5.
Definition WB : window := Win UBk N K_BLOCK.
Definition WT : window := Win (shad UBk) (shlen (N + 7)) K_TWINz.

Lemma rest_below : forallb (sv_vars_below (s_next st)) rest = true.
Proof. exact (CtrFrame.TwinB.rest_below st FOK rest hargs md A nw Hf Eh). Qed.

Lemma DEC5 : forall (m1 m2 : list window) nw2 rest2,
  h2 = VL md :: A :: VL nw2 :: rest2 -> wt nw2 = false -> pred (pred nn) = Z.to_nat (to_Z (wl nw2)) -> (3 * pred (pred nn) <= length rest2)%nat ->
  wins_of E (pred (pred nn)) rest2 = m1 ++ m2 -> skipn (3 * pred (pred nn)) rest2 = skipn (3 * nn) rest ->
  (forall x, In x rest2 -> In x rest) -> (2 <= nn)%nat ->
  decode (map (den E') h5) = Some (w2Z md, aw', ((m1 ++ m2) ++ [WB]) ++ [WT], map (den E) (skipn (3 * nn) rest)).
Proof.
  intros m1 m2 nw2 rest2 EH2 T2 N2 L2 W2 SK2 SUB NN2. destruct NEWBr as (NN & _).
  assert (NS : to_Z (wl nw2) + 2 < two63) by (pose proof (Uint63.to_Z_bounded (wl nw2)) as B; unfold two63; lia).
  rewrite EH2 in H3. cbn in H3. injection H3 as <-.
  destruct (CtrPost.TwinB.add_window_facts E' md cred' nw2 rest2 (pred (pred nn)) (VP kB wzero) nsv (VL CtrLib.K_BLOCK) T2 N2 L2 ltac:(lia)) as (A1 & T1 & N1 & L1 & W1 & S1).
  cbv zeta in A1, T1, N1, L1, W1, S1. assert (X4 : Some h4 = _) by (rewrite <- H4; exact A1). apply Some_inj in X4. subst h4.
  destruct (CtrPost.TwinB.add_window_facts E' md cred' (wadd nw2 wone) _ (S (pred (pred nn))) (VP kS wzero) (twin_len nsv) (VL K_TWIN) T1 N1 L1
              ltac:(destruct (wadd_one_small nw2 T2 ltac:(lia)) as [_ X]; lia)) as (A2 & T2' & N2' & L2' & W2' & S2').
  cbv zeta in A2, T2', N2', L2', W2', S2'. assert (X5 : Some h5 = _) by (rewrite <- H5; exact A2). apply Some_inj in X5. subst h5.
  rewrite (decode_hargs E' md cred' _ _ (S (S (pred (pred nn)))) T2' N2' L2'). rewrite W2', W1, S2', S1, SK2.
  assert (RB2 : forallb (sv_vars_below (s_next st)) rest2 = true) by (apply (forallb_sub _ rest); [exact SUB| exact rest_below]).
  rewrite (CtrFrame.TwinB.wins_of_E' E st Fv Gv _ _ RB2), W2, (CtrFrame.TwinB.map_den_E' E st Fv Gv _ (forallb_skipn _ (3 * nn) rest rest_below)).
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (CtrFrame.TwinB.den_E' E st Fv Gv nsv nsv_below); exact NDEN).
  assert (C1 : den E' cred' = aw').
  { unfold cred'. destruct pd.
    - rewrite (CtrFrame.TwinB.den_E' E st Fv Gv A (CtrFrame.TwinB.A_below st FOK rest hargs md A nw Hf Eh)), AW'E, Z.sub_0_r, AWden. symmetry. apply Z_to_bv_bv_unsigned.
    - rewrite den_sv_alu. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv A (CtrFrame.TwinB.A_below st FOK rest hargs md A nw Hf Eh)). unfold alu64, alu. apply bv_eq.
      rewrite bv_sub_unsigned, AW'E, Z_to_bv_unsigned, DN, AWden. reflexivity. }
  assert (C2 : Win (bv_unsigned (den E' (VP kB wzero))) (bv_unsigned (den E' nsv)) (bv_unsigned (den E' (VL CtrLib.K_BLOCK))) = WB).
  { unfold WB. rewrite HeapCtr.TwinB.den_VPz, ev_kB, DN. reflexivity. }
  assert (C3 : Win (bv_unsigned (den E' (VP kS wzero))) (bv_unsigned (den E' (twin_len nsv))) (bv_unsigned (den E' (VL K_TWIN))) = WT).
  { unfold WT. rewrite HeapCtr.TwinB.den_VPz, ev_kS. rewrite (CallA.TwinB.twin_len_den E' nsv) by (rewrite DN; unfold AREQMAX in NN; lia).
    rewrite DN. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite C1, C2, C3. reflexivity.
Qed.

Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) (ms_mem ms).

Lemma freed_off_image : forall a, in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a -> find_segment bsegs a 1 = None /\ a < ATOP.
Proof.
  intros a Ha. destruct owner as (UBf & HTf & _). pose proof atop_range as ATR. pose proof AR as [HWw _].
  assert (IU : in_user LB a).
  { unfold in_user. apply in_ivs_In. destruct Ha as [Ha|Ha]; [exists (Af, nf); split; [exact blockLB| exact Ha]| exists (shad Af, shlen (nf + 7)); split; [exact HTf| exact Ha]]. }
  split.
  - destruct Ha as [Ha|Ha]; [exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ a AWHf blockLB Ha))
                            | exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ a AWHf HTf Ha))].
  - destruct (LB_band AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo a HWw IU) as [B|[B|B]]; unfold AIMG_HI, KLS in *; lia.
Qed.

Lemma HOLDNr : forall l1 l2 m1 m2,
  decode (map (den E') h5) = Some (w2Z md, aw', ((m1 ++ m2) ++ [WB]) ++ [WT], map (den E) (skipn (3 * nn) rest)) ->
  wins_of E nn rest = l1 ++ WBf :: l2 -> l1 ++ l2 = m1 ++ WTf :: m2 -> ~ In WBf (l1 ++ l2) -> ~ In WTf (m1 ++ m2) ->
  op_holds OPS HEAP_ID (map (den E') h5) m' mo'.
Proof.
  intros l1 l2 m1 m2 D W1 W2 NB NT. rewrite OPS_holds1. destruct owner as (UBf & HTf & _ & NRf & ALf).
  destruct WORLDr as (AWH' & PAT & UBn & DJ & NIN & DJT). destruct NEWBr as (NN & BR & _).
  destruct (twin_band _ _ BR NN) as (TB1 & TB2 & TB3 & _). assert (BK8 : UBk mod 8 = 0) by (destruct BR as (_ & _ & _ & X16); clear - X16; Z.div_mod_to_equations; lia).
  destruct BR as (BK & _ & TOP & _). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  assert (TWFRESH : forall a, in_iv (shad UBk, shlen (N + 7)) a -> ~ in_user ((UBk, N) :: LBk) a).
  { intros a Ha U. apply in_ivs_cons in U as [U|U]; [| exact (DJT a Ha U)].
    unfold in_iv in Ha, U. cbn [fst snd] in Ha, U. unfold user_band in UBn. lia. }
  assert (IN1 : forall w, In w (l1 ++ l2) <-> In w (wins_of E nn rest) /\ w <> WBf).
  { intros w. rewrite W1. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NB H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  assert (IN2 : forall w, In w (m1 ++ m2) <-> In w (l1 ++ l2) /\ w <> WTf).
  { intros w. rewrite W2. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NT H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  assert (WFK : windows_wf (m1 ++ m2) LBk (ATOP + 4096)).
  {
      apply Forall_forall. intros w Hw. apply IN2 in Hw as [Hw NWT]. apply IN1 in Hw as [Hw NWB].
      pose proof (proj1 (Forall_forall _ _) WF w Hw) as (X1 & X2 & X3 & KD). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
      destruct (HeapCtrB.TwinB.wins_cover E nn rest wnl w NW Hw) as [KS|(k & len & kd & Ik & EW)].
      { left. destruct KD as [[_ C]|[[K _]|[K _]]]; [split; [exact KS| exact C]| rewrite KS in K; unfold K_BLOCK, K_STACK in K; lia| rewrite KS in K; unfold K_SUB, K_STACK in K; lia]. }
      assert (NKf : k <> kf).
      { intros ->. destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ kf len kd lenf CtrLib.K_BLOCK AN Ik (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as [-> ->].
        apply NWB. rewrite EW. unfold WBf. rewrite KB1. reflexivity. }
      assert (NKs : k <> sh).
      { intros ->. destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ sh len kd lent K_TWIN AN Ik (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as [-> ->].
        destruct twin_sh as (rs & _ & _ & _ & ESH & ELT). apply NWT. rewrite EW. unfold WTf. rewrite ESH, ELT, KT9. reflexivity. }
      destruct KD as [[K C]|[[K B]|[K (b & Hb & SUB)]]].
      * left. auto.
      * right; left. split; [exact K|]. apply LB_free_In. split; [exact B|].
        apply (kept_block k len kd (w_iv w) Ik NKf NKs B). rewrite EW. unfold w_iv. cbn [w_lo w_len]. intros a Ha. exact Ha.
      * right; right. split; [exact K|]. exists b. split; [| exact SUB]. apply LB_free_In. split; [exact Hb|].
        apply (kept_block k len kd b Ik NKf NKs Hb). rewrite EW in SUB. unfold w_iv in SUB. cbn [w_lo w_len] in SUB. exact SUB.
  }
  exists (w2Z md), aw', (((m1 ++ m2) ++ [WB]) ++ [WT]), (map (den E) (skipn (3 * nn) rest)), LBr, Wr.
  split; [exact D|]. split; [exact AWH'|]. split; [| split].
  -
    apply Forall_app. split; [apply Forall_app; split|].
    + apply (CtrPost.TwinB.windows_wf_mono _ LBk LBr _ WFK). intros b Hb; right; right; exact Hb.
    + constructor; [|constructor]. unfold window_wf, WB, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; left. split; [reflexivity|]. right; left. reflexivity.
    + constructor; [|constructor]. unfold window_wf, WT, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; right. split; [unfold K_SUB, K_TWINz; lia|]. exists (shad UBk, shlen (N + 7)). split; [left; reflexivity|]. intros a Ha. exact Ha.
  -
    assert (HC1 : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m').
    { apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U NH.
      apply in_ivs_In in U as (b & Hb & Hin).
      assert (INWIN : forall w, In w (wins_of E nn rest) -> w_kind w <> K_STACK -> in_iv (w_iv w) a -> False).
      { intros w Hw NK Hwa. apply NH. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv w). split; [| exact Hwa]. apply in_map. apply filter_In. split; [exact Hw|].
        destruct (Z.eqb_spec (w_kind w) K_STACK); [contradiction| reflexivity]. }
      destruct (iv_eq_dec b (Af, nf)) as [->|N1].
      { exfalso. apply (INWIN WBf); [rewrite W1; apply in_or_app; right; left; reflexivity| cbn; unfold K_BLOCK, K_STACK; lia| exact Hin]. }
      destruct (iv_eq_dec b (shad Af, shlen (nf + 7))) as [->|N2].
      { exfalso. apply (INWIN WTf); [| cbn; unfold K_TWINz, K_STACK; lia| exact Hin].
        assert (X : In WTf (l1 ++ l2)) by (rewrite W2; apply in_or_app; right; left; reflexivity). apply IN1 in X as [X _]. exact X. }
      symmetry. unfold ALib.Mem.wa in *. apply (SBr a ltac:(unfold two64 in Ha; lia)). right; right. apply in_ivs_In. exists b. split; [apply LB_free_In; auto| exact Hin]. }
    assert (INB : In WBf (wins_of E nn rest)) by (rewrite W1; apply in_or_app; right; left; reflexivity).
    pose proof (cw_free Cw _ _ _ _ m' Af nf (l1 ++ l2) HC1 INB IN1) as HC2.
    assert (INT : In WTf (l1 ++ l2)) by (rewrite W2; apply in_or_app; right; left; reflexivity).
    pose proof (Cw_ghost_free _ _ _ _ m' (shad Af) (shlen (nf + 7)) (m1 ++ m2) HC2 INT IN2) as HC3.
    pose proof (cw_grow Cw _ _ _ _ m' UBk N HC3 DJ) as HC4.
    apply (Cw_ghost_grow _ _ _ _ m' UBk N (shlen (N + 7)) HC4); [apply in_or_app; right; left; reflexivity| lia| exact BK8|].
    exact TWFRESH.
  -
    pose proof AR as [HWw _]. pose proof HWw as (AHw & HTw & _). destruct WOF as (_ & _ & _ & E4).
    destruct owner as (_ & _ & (p' & HP' & HPT) & _).
    assert (EP : HB p' Af nf = HB p Af nf).
    { apply (shadow_iv_inj AI AI_fake _ _ _ _ _ (HB p' Af nf) (HB p Af nf) AHw (proj1 (HTw _ HPT)) ltac:(rewrite E4; exact HP)). reflexivity. }
    rewrite EP in HPT.
    pose proof (ties_free AI ACCT UNIV AI_fake WW aw LB (ms_mem ms) mo (wins_of E nn rest) (l1 ++ l2) (m1 ++ m2) p Af nf RNG' sta' m' HWw TI HPT IN1 IN2
                  ltac:(intros IP; exfalso; exact (NOPR IP))) as TF.
    apply (ties_grow_heap _ (m1 ++ m2) (w_L WW) RNG' sta' m' (HB q UBk N) TF ltac:(exists q; reflexivity)); [cbn [ab_size]; lia| |
      intros IP; exfalso; apply NOPR; apply IN2 in IP as [IP _]; apply IN1 in IP as [IP _]; exact IP].
    cbn [ab_addr ab_size]. fold WB WT.
    assert (GA0 : ghost_apart (m1 ++ m2)) by (destruct TF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
    assert (WF1 : windows_wf ((m1 ++ m2) ++ [WB]) ((UBk, N) :: LBk) (ATOP + 4096)).
    { apply Forall_app. split; [apply (CtrPost.TwinB.windows_wf_mono _ LBk _ _ WFK); intros b Hb; right; exact Hb|].
      constructor; [|constructor]. unfold window_wf, WB, w_iv. cbn [w_lo w_len w_kind]. split; [lia|]. split; [lia|]. split; [unfold two64; lia|].
      right; left. split; [reflexivity|]. left. reflexivity. }
    apply (ghost_apart_new_ghosts ((m1 ++ m2) ++ [WB]) _ ((UBk, N) :: LBk) (ATOP + 4096) WF1).
    + exact (ghost_apart_new_block _ LBk (ATOP + 4096) UBk N WFK GA0 DJ).
    + intros w Hw. apply in_app_or in Hw as [Hw|[<-|[]]]; [left; exact Hw| right]. split; [unfold WT; cbn [w_kind]; unfold K_TWINz, K_BLOCK; lia|].
      intros _ a Ha. unfold WT, w_iv in Ha. cbn [w_lo w_len] in Ha. exact (TWFRESH a Ha).
Qed.

Variables (r : int) (st1 : sstate) (R' : bvmap 5 word).
Hypothesis CP : call_pre st = Some r.
Hypothesis FS : forget_stack_below_sp_g st = Some st1.
Hypothesis KEPT : forall rg, In rg CtrFrame.TwinB.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg.
Hypothesis HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Hypothesis A0' : AP.getr R' 10%bv = Z_to_bv 64 UBk.
Hypothesis MINV' : ALib.Mem.mem_inv bsegs m'.
Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis Hksp : okey offs = Some ksp.
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis K16 : keyZ ksp mod 16 = 0.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis STK' : stk bsegs m' (CtrPre.TwinB.sp_lo E st) sp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis OTH : OTHER mo mo'.
Hypothesis MINVo : op_minv OPS mo'.

Definition newRr : list (int * region) := [(kB, blk_region); (kS, twin_region nsv)].
Definition RgR : IMap.t region := CtrFrame.TwinB.RgPg st ks rss ksp newRr [kf; sh].
Definition NEWSETr (a : Z) : Prop := in_iv (UBk, N) a \/ in_iv (shad UBk, shlen (N + 7)) a.

Lemma KEEP_delr : forall k0, ~ In k0 [kf; sh] -> KEEPf k0.
Proof. intros k0 H. split; intros ->; apply H; [left| right; left]; reflexivity. Qed.
Lemma newR_nodup : List.NoDup (map fst newRr).
Proof.
  cbn [map fst newRr]. constructor; [| constructor; [intros []| constructor]]. intros [X|[]].
  pose proof kB_Z as KB. pose proof kS_Z as KS. rewrite X in KS. lia.
Qed.
Lemma newR_fresh : forall k rg, In (k, rg) newRr -> PrimInt63.eqb k 0%uint63 = false.
Proof. intros k rg [X|[X|[]]]; injection X as <- _; [exact kB_nz| exact kS_nz]. Qed.
Lemma newR_ok : forall k rg, In (k, rg) newRr -> region_ok bsegs (s_priv st) E' m' k rg.
Proof. intros k rg [X|[X|[]]]; injection X as <- <-; [exact blk_region_ok| exact twin_region_okA]. Qed.
Lemma twin_hi : hiZ E' (twin_region nsv) = shlen (N + 7) /\ loZ (twin_region nsv) = 0.
Proof.
  destruct NEWBr as (NN & _).
  assert (DN : bv_unsigned (den E' nsv) = N) by (rewrite (CtrFrame.TwinB.den_E' E st Fv Gv nsv nsv_below); exact NDEN).
  assert (HI : rg_hi (twin_region nsv) = twin_len nsv /\ rg_lo (twin_region nsv) = 0%uint63).
  { split; [exact (CallA.TwinB.twin_region_hi nsv)| exact (proj1 (CallA.TwinB.twin_region_fields nsv))]. }
  destruct HI as [HI LO]. unfold hiZ, loZ. rewrite HI, LO. split; [| reflexivity].
  rewrite (CallA.TwinB.twin_len_den E' nsv) by (rewrite DN; unfold AREQMAX in NN; lia). rewrite DN. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma newR_range : forall k rg a, In (k, rg) newRr ->
  bv_unsigned (ev E' k) + loZ rg <= a < bv_unsigned (ev E' k) + hiZ E' rg -> NEWSETr a.
Proof.
  intros k rg a [X|[X|[]]] Ha; injection X as <- <-.
  - left. rewrite ev_kB in Ha. unfold in_iv. cbn [fst snd]. unfold hiZ, loZ, blk_region in Ha. cbn [rg_hi rg_lo] in Ha.
    rewrite (CtrFrame.TwinB.den_E' E st Fv Gv nsv nsv_below), NDEN in Ha. change (keyZ 0%uint63) with 0 in Ha. lia.
  - right. rewrite ev_kS in Ha. destruct twin_hi as [HI LO]. rewrite HI, LO in Ha. unfold in_iv. cbn [fst snd]. lia.
Qed.
Lemma new_band : forall a, NEWSETr a ->
  ((AIMG_HI <= a < 0x7fff7000 \/ 0x10007fff8000 <= a < ATOP) /\ in_iv (UBk, N) a) \/ ((0x800be200 <= a < shad ATOP) /\ in_iv (shad UBk, shlen (N + 7)) a).
Proof.
  intros a Ha. destruct NEWBr as (NN & (BK & _ & HI & _) & _). destruct (shadow_tight UBk N BK HI ltac:(lia)) as [T1 T2].
  unfold ablk, AIMG_HI, KLS in BK. unfold AIMG_HI. destruct Ha as [Ha|Ha]; [left| right]; (split; [| exact Ha]); unfold in_iv in Ha; cbn [fst snd] in Ha; lia.
Qed.
Lemma newR_low : forall a, NEWSETr a -> AIMG_HI <= a < ATOP + 4096 /\ ~ in_user LBk a.
Proof.
  intros a Ha. destruct WORLDr as (_ & _ & _ & DJ & _ & DJT). pose proof atop_range as ATR.
  assert (SHA : shad ATOP < ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  destruct (new_band a Ha) as [[B I]|[B I]]; (split; [unfold AIMG_HI in *; lia|]); [exact (DJ a I)| exact (DJT a I)].
Qed.
Lemma newR_nosh : forall a, NEWSETr a -> ~ (0x7fff8000 <= a < 0x800be200).
Proof. intros a Ha X. destruct (new_band a Ha) as [[B _]|[B _]]; unfold AIMG_HI in *; lia. Qed.
Lemma newR_nostk : forall a, NEWSETr a -> ~ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Proof.
  intros a Ha (a' & R & ->). pose proof atop_range as ATR.
  assert (M : shad ATOP <= shad a' < 0x10007fff8000) by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  destruct (new_band _ Ha) as [[B _]|[B _]]; unfold AIMG_HI in *; [| lia].
  assert (SHA : 0x7fff7000 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia). lia.
Qed.
Lemma newR_disj : forall k1 r1 k2 r2 a, In (k1, r1) newRr -> In (k2, r2) newRr -> k1 <> k2 -> (rg_w r1 = true \/ rg_w r2 = true) ->
  ~ (bv_unsigned (ev E' k1) + loZ r1 <= a < bv_unsigned (ev E' k1) + hiZ E' r1 /\
     bv_unsigned (ev E' k2) + loZ r2 <= a < bv_unsigned (ev E' k2) + hiZ E' r2).
Proof.
  intros k1 r1 k2 r2 a I1 I2 NE _ [A1 A2].
  pose proof (newR_range k1 r1 a I1 A1) as S1. pose proof (newR_range k2 r2 a I2 A2) as S2.
  assert (BLK : forall k rg, In (k, rg) newRr -> bv_unsigned (ev E' k) + loZ rg <= a < bv_unsigned (ev E' k) + hiZ E' rg -> (k = kB /\ in_iv (UBk, N) a) \/ (k = kS /\ in_iv (shad UBk, shlen (N + 7)) a)).
  { intros k rg [X|[X|[]]] Ha; injection X as <- <-.
    - left. split; [reflexivity|]. rewrite ev_kB in Ha. unfold in_iv. cbn [fst snd]. unfold hiZ, loZ, blk_region in Ha. cbn [rg_hi rg_lo] in Ha.
      rewrite (CtrFrame.TwinB.den_E' E st Fv Gv nsv nsv_below), NDEN in Ha. change (keyZ 0%uint63) with 0 in Ha. lia.
    - right. split; [reflexivity|]. rewrite ev_kS in Ha. destruct twin_hi as [HI LO]. rewrite HI, LO in Ha. unfold in_iv. cbn [fst snd]. lia. }
  destruct NEWBr as (NN & (BK & _ & HI & _) & _). destruct (shadow_tight UBk N BK HI ltac:(lia)) as [T1 T2]. pose proof atop_range as ATR.
  assert (SHA : shad ATOP <= 0x10007fff8000) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  unfold ablk, AIMG_HI, KLS in BK.
  destruct (BLK k1 r1 I1 A1) as [[-> X1]|[-> X1]]; destruct (BLK k2 r2 I2 A2) as [[-> X2]|[-> X2]]; try (exfalso; exact (NE eq_refl));
    unfold in_iv in X1, X2; cbn [fst snd] in X1, X2; lia.
Qed.

Lemma freed_band : forall a, in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a ->
  (a < 0x7fff7000 \/ 0x10007fff8000 <= a) \/ (0x800be200 <= a < shad ATOP).
Proof.
  intros a Ha. pose proof AR as [(AH & _) EM]. destruct WOF as (E1 & E2 & E3 & E4). rewrite E4 in AH.
  destruct (heap_block_facts AI _ _ _ _ _ (HB p Af nf) AH HP ltac:(exists p; reflexivity)) as (NP & (BK & _ & HI & _) & _). cbn [ab_addr ab_size] in NP, BK, HI.
  destruct (shadow_tight Af nf BK HI ltac:(lia)) as [T1 T2]. unfold ablk, AIMG_HI, KLS in BK. unfold in_iv in Ha. cbn [fst snd] in Ha.
  destruct Ha as [Ha|Ha]; [left| right]; lia.
Qed.

Lemma freed_unbased_r : forall a, in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a -> ~ NEWSETr a -> ~ in_based E' RgR a.
Proof.
  intros a Ha NNEW (k0 & rg & Fk & KZ & RA). destruct (freed_off_image a Ha) as [_ LOW]. destruct owner as (_ & HTf & _).
  assert (SPF : ATOP + 4096 <= sp) by (rewrite SPE; lia).
  destruct (CtrFrame.TwinB.RgPg_range OPS E st ms mo HS FOK Fv Gv LB LBk ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf LOSP FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln newRr [kf; sh]
              newR_nodup KEEP_delr NEWSETr newR_range k0 rg a Fk KZ RA) as [[_ X]|[_ [[_ X]|[_ [X|[X|X]]]]]].
  - exact (NNEW X).
  - lia.
  - fold sp in X. lia.
  - exact (freed_apart AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo WW Af nf a AR blockLB HTf Ha X).
  - pose proof atop_range as ATR.
    assert (SHA : 0x7fff8000 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
    destruct (sh_cov_band a X) as [C|C]; destruct (freed_band a Ha) as [B|B]; lia.
Qed.

Definition f_range : fact := FRange kB BLK_LO BLK_HI.
Definition f_align : fact := FAlign kB 4%uint63.
Definition f_link : fact := FEq (VP kS wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP kB wzero) (VL (wlit 3%uint63))) (VL SBw)).

Definition f_cred : fact := cred_fact (s_facts st) nsv A.
Hypothesis CREDF : fact_holds E f_cred.
Lemma CREDF' : fact_holds E' f_cred.
Proof.
  revert CREDF. unfold f_cred, cred_fact. destruct (prim_decided (s_facts st) nsv); cbn [fact_holds].
  - rewrite (CtrFrame.TwinB.den_E' E st Fv Gv A (CtrFrame.TwinB.A_below st FOK rest hargs md A nw Hf Eh)). cbn [den]. intros X; exact X.
  - rewrite (CtrFrame.TwinB.den_E' E st Fv Gv nsv nsv_below), (CtrFrame.TwinB.den_E' E st Fv Gv A (CtrFrame.TwinB.A_below st FOK rest hargs md A nw Hf Eh)). intros X; exact X.
Qed.

Lemma FACTSr4 : facts_hold E' (f_link :: f_align :: f_range :: f_cred :: s_facts st).
Proof.
  destruct NEWBr as (NN & BR & _). destruct BR as (BK & _ & TOP & AL). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
  constructor; [| constructor; [| constructor; [| constructor; [exact CREDF'| exact (so_facts _ _ _ _ _ _ (CtrFrame.TwinB.HS' OPS E st ms mo HS FOK Fv Gv))]]]].
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

Definition fx_r : list fact := and7_facts nsv.
Lemma and7_hold : Forall (fact_holds E') fx_r.
Proof.
  unfold fx_r, and7_facts. pose proof (CallA.TwinB.size_shape_sound E (s_facts st) nsv (so_facts _ _ _ _ _ _ HS) SHAPE) as M8.
  pose proof (CtrFrame.TwinB.den_E' E st Fv Gv nsv nsv_below) as DEN.
  revert M8 DEN. generalize nsv. intros n M8 DEN.
  destruct n; [constructor| | | | | | | | | |];
    (constructor; [| constructor]); hnf in M8; cbn [fact_holds]; apply bv_eq;
    rewrite CallA.TwinB.and7_den_raw, DEN, M8; cbn [den]; rewrite wbv_unsigned, wzero_ok; reflexivity.
Qed.
Lemma FACTSr : facts_hold E' (fx_r ++ f_link :: f_align :: f_range :: f_cred :: s_facts st).
Proof.
  pose proof and7_hold as A7. pose proof FACTSr4 as F4. unfold facts_hold in *.
  revert A7. generalize fx_r. intros l A7.
  induction l as [|f l IH]; [exact F4|]. cbn [app]. constructor; [exact (Forall_inv A7)| exact (IH (Forall_inv_tail A7))].
Qed.

Lemma st1_fields_r : s_pc st1 = s_pc st /\ s_rf st1 = s_rf st /\ s_ff st1 = s_ff st /\ s_resv st1 = s_resv st /\ s_facts st1 = s_facts st
  /\ s_ops st1 = s_ops st /\ s_priv st1 = s_priv st /\ s_next st1 = s_next st /\ s_regs st1 = IMap.add ks (region_forget_below rss ksp) (s_regs st).
Proof. unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. repeat split; reflexivity. Qed.
Lemma kB_next : s_next (clobber st1) = kB.
Proof.
  destruct (clobber_fields st1) as (_ & _ & _ & _ & _ & _ & _ & NXc). destruct st1_fields_r as (_ & _ & _ & _ & _ & _ & _ & NX1 & _).
  rewrite NXc, NX1. symmetry. destruct NXr as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma kS_next : PrimInt63.add kB 1%uint63 = kS.
Proof.
  destruct NXr as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  apply Uint63.to_Z_inj. rewrite add_Z by (rewrite kB_Z; change (to_Z 1%uint63) with 1; rewrite wB_two63, two63_eq; lia).
  rewrite kB_Z, kS_Z. change (to_Z 1%uint63) with 1. lia.
Qed.
Lemma stR_shape_gen : forall (S : sstate) (nx1 nx2 : int) (RT : IMap.t region -> IMap.t region) (h : list sv) (f0 f1 f2 f3 : fact) (l : list fact) (v : sv) (r0 : int),
  setpc (setr (addfacts (addfact (addfact (addfact (addfact
          (set_ops (setregs (set_next (set_next S nx1) nx2) (RT (s_regs (set_next (set_next S nx1) nx2))))
                   (set_op HEAP_ID h (s_ops (set_next (set_next S nx1) nx2))))
          f0) f1) f2) f3) l) X10 v) r0
  = SS r0 (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (RT (s_regs S)) (l ++ f3 :: f2 :: f1 :: f0 :: s_facts S) (set_op HEAP_ID h (s_ops S)) (s_priv S) nx2.
Proof. intros. destruct S. reflexivity. Qed.
Lemma stR_shape : arealloc_stB st st1 r h5 kf sh A
  = SS r (rf_set (s_rf (clobber st1)) X10 (VP kB wzero)) (s_ff st) (s_resv st) RgR
       (fx_r ++ f_link :: f_align :: f_range :: f_cred :: s_facts st) (set_op HEAP_ID h5 (s_ops st)) (s_priv st) (PrimInt63.add kS 1%uint63).
Proof.
  unfold arealloc_stB. cbv zeta. rewrite kB_next, kS_next. fold nsv. unfold fx_r.
  rewrite (stR_shape_gen (clobber st1) _ _ (fun R0 => IMap.add kS (twin_region nsv) (IMap.add kB (Region 0%uint63 nsv true BGUnk IMap.empty) (IMap.remove sh (IMap.remove kf R0))))).
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & _). destruct st1_fields_r as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & _ & R1).
  rewrite FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1, R1. reflexivity.
Qed.

Lemma NEWSETr_dec : forall a, NEWSETr a \/ ~ NEWSETr a.
Proof. intros a. unfold NEWSETr, in_iv. cbn [fst snd]. lia. Qed.

Theorem realloc_post : st_ok bsegs OPS E' (arealloc_stB st st1 r h5 kf sh A) (CtrFrame.TwinB.ms' ms r R' m') mo'.
Proof.
  rewrite stR_shape. destruct DEL2 as (l1 & l2 & m1 & m2 & nw2 & rest2 & EH2 & T2 & N2 & L2 & W2m & SK2 & SUB & NN2 & W1 & W2 & NB & NT).
  pose proof (DEC5 m1 m2 nw2 rest2 EH2 T2 N2 L2 W2m SK2 SUB NN2) as D.
  pose proof (HOLDNr l1 l2 m1 m2 D W1 W2 NB NT) as HOLDN.
  set (ws5 := ((m1 ++ m2) ++ [WB]) ++ [WT]) in *.
  assert (INWS : forall a, in_ws (wins_of E nn rest) a -> in_ws (m1 ++ m2) a \/ in_iv (Af, nf) a \/ in_iv (shad Af, shlen (nf + 7)) a).
  { intros a X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    rewrite W1 in Hw. apply in_app_or in Hw as [Hw|[<-|Hw]]; [| right; left; exact Hin|].
    - assert (X : In w (l1 ++ l2)) by (apply in_or_app; left; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [| right; right; exact Hin|];
        left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]).
    - assert (X : In w (l1 ++ l2)) by (apply in_or_app; right; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [| right; right; exact Hin|];
        left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]). }
  assert (HW5 : forall w a, In w ws5 -> w_kind w <> K_STACK -> in_iv (w_iv w) a -> in_ws (heap_ws ws5) a).
  { intros w a Hw NK Hin. unfold in_ws, heap_ws. apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [exact Hw|].
    destruct (Z.eqb_spec (w_kind w) K_STACK); [contradiction| reflexivity]. }
  assert (NEWIN : forall a, NEWSETr a -> in_ws (heap_ws ws5) a).
  { intros a [Ha|Ha].
    - apply (HW5 WB a); [unfold ws5; apply in_or_app; left; apply in_or_app; right; left; reflexivity| cbn; unfold K_BLOCK, K_STACK; lia| exact Ha].
    - apply (HW5 WT a); [unfold ws5; apply in_or_app; right; left; reflexivity| cbn; unfold K_TWINz, K_STACK; lia| exact Ha]. }
  assert (DKB : den E' (VP kB wzero) = AP.getr R' 10%bv).
  { rewrite HeapCtr.TwinB.den_VPz, A0'. apply bv_eq. rewrite ev_kB. destruct NEWBr as (NN & (BK & _ & TOP & _) & _). pose proof atop_range.
    unfold ablk, AIMG_HI, KLS in BK. symmetry. apply Z_to_bv_small. unfold bv_modulus, two64. lia. }
  apply (CtrFrame.TwinB.frame_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo' KEPT HF aw LB LBk AWHf MINV' SBVr SBOf WBMr SBTf ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf
           K16 LOSP STK' FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln OTH newRr [kf; sh] newR_nodup
           newR_fresh KEEP_delr NEWSETr newR_ok newR_range newR_low newR_nosh newR_nostk newR_disj
           h5 (w2Z md) aw' ws5 (map (den E) (skipn (3 * nn) rest)) D HOLDN).
  - exact NEWIN.
  -   intros a Ha NIX NWS. destruct (GLib.UG.in_ws_dec (wins_of E nn rest) a) as [IW|NIW]; [| left; exact NIW].
    right. destruct (INWS a IW) as [X|FR].
    + exfalso. apply NWS. unfold ws5. apply CtrPost.TwinB.in_ws_app. left. apply CtrPost.TwinB.in_ws_app. left. exact X.
    + split; [exact (proj1 (freed_off_image a FR))|]. apply (freed_unbased_r a FR). intros NS. apply NWS. exact (CtrFrame.TwinB.in_heap_ws _ _ (NEWIN a NS)).
  -   intros a IB X. pose proof (CtrFrame.TwinB.in_heap_ws _ _ X) as IW. destruct (INWS a IW) as [Y|FR].
    + unfold in_ws, heap_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw). apply filter_In in Hw as [Hw KW].
      assert (NFR : forall w0, w0 = WBf \/ w0 = WTf -> in_iv (w_iv w0) a -> ~ NEWSETr a -> False).
      { intros w0 [-> | ->] Hw0 NS; [exact (freed_unbased_r a (or_introl Hw0) NS IB)| exact (freed_unbased_r a (or_intror Hw0) NS IB)]. }
      destruct (NEWSETr_dec a) as [NS|NNS]; [exact (proj1 (in_ivs_In _ _) (NEWIN a NS)) || (apply in_ivs_In; exact (proj1 (in_ivs_In _ _) (NEWIN a NS)))|].
      apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [| exact KW].
      unfold ws5. apply in_or_app. left. apply in_or_app. left.
      rewrite W1 in Hw. apply in_app_or in Hw as [Hw|[<-|Hw]]; [| exfalso; exact (NFR WBf (or_introl eq_refl) Hin NNS)|].
      * assert (X : In w (l1 ++ l2)) by (apply in_or_app; left; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; auto| exfalso; exact (NFR WTf (or_intror eq_refl) Hin NNS)| apply in_or_app; auto].
      * assert (X : In w (l1 ++ l2)) by (apply in_or_app; right; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; auto| exfalso; exact (NFR WTf (or_intror eq_refl) Hin NNS)| apply in_or_app; auto].
    + destruct (NEWSETr_dec a) as [NS|NNS]; [exact (NEWIN a NS)| exfalso; exact (freed_unbased_r a FR NNS IB)].
  - exact FACTSr.
  - exact DKB.
  - exact MINVo.
Qed.

End REALLOCD.

Lemma arealloc_block : forall E st ms mo r hargs wnl L RNG sta LBa aw kf sh cred,
  st_ok bsegs OPS E st ms mo -> CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  find_twin (s_facts st) kf = Some sh -> afree_ok st wnl kf sh = true -> twin_canon st wnl kf sh = true -> getr st X10 = VP kf wzero -> heap_A hargs = Some cred ->
  KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (getr st X11) = true -> reqmax_ok (s_facts st) (getr st X11) = true ->
  cred_pre (s_facts st) (getr st X11) cred = true ->
  exists p lenf, CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK)
    /\ In (HB p (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf))) LBa
    /\ AP.getr (ms_regs ms) 10%bv = Z_to_bv 64 (bv_unsigned (ev E kf))
    /\ AP.getr (ms_regs ms) 11%bv = Z_to_bv 64 (bv_unsigned (den E (getr st X11)))
    /\ 1 <= bv_unsigned (den E (getr st X11)) <= AREQMAX
    /\ (1048576 <= bv_unsigned aw /\ (prim_decided (s_facts st) (getr st X11) = true \/ bv_unsigned (den E (getr st X11)) <= bv_unsigned aw))
    /\ ablock_shadow (ms_mem ms) (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf)).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kf sh cred HS CF FT FOKk TCAN X10E HA N0 N1 NC.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & AR & TI)).
  destruct (afree_ok_inv E st ms mo HS wnl kf sh FOKk) as (rf & lenf & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  destruct (owner E st ms mo HS wnl nn rest LB aw L RNG sta LBa NW WF W WOF AR TI kf sh TCAN rf lenf lent WLf WLt BTs POSf LEf) as (_ & _ & (p & HP & _) & _).
  pose proof (freed_pattern E st ms mo HS wnl nn rest LB aw L RNG sta LBa NW WF W WOF AR TI kf sh TCAN rf lenf lent WLf WLt BTs POSf LEf OTHERS) as FPAT.
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  pose proof (KnownA.TwinB.KnownA.known_ltu_sound E _ _ _ HF N0) as L0. pose proof (CallA.TwinB.reqmax_ok_sound E _ _ HF N1) as L1.
  cbn [den] in L0. rewrite wbv_unsigned in L0. rewrite wzero_ok in L0.
  replace 0xFFF00000 with AREQMAX in L1 by reflexivity.
  rewrite Eh, heap_A_eq in HA. injection HA as <-.
  assert (L2 : 1048576 <= bv_unsigned aw /\ (prim_decided (s_facts st) (getr st X11) = true \/ bv_unsigned (den E (getr st X11)) <= bv_unsigned aw)).
  { unfold cred_pre in NC. apply andb_prop in NC as [NCX NC]. rewrite AWden.
    pose proof (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF NCX) as LX. replace (bv_unsigned (den E (VL C_EXHw))) with 1048576 in LX by (vm_compute; reflexivity).
    split; [exact LX|]. apply orb_prop in NC as [NC|NC]; [left; exact NC| right; exact (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF NC)]. }
  exists p, lenf. split; [exact WLf|]. split; [exact HP|].
  split; [rewrite <- HeapCtr.TwinB.reg_of_X10, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), X10E, HeapCtr.TwinB.den_VPz; symmetry; apply Z_to_bv_bv_unsigned|].
  split; [rewrite <- HeapCtr.TwinB.reg_of_X11, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X11); symmetry; apply Z_to_bv_bv_unsigned|].
  split; [lia|]. split; [exact L2| exact FPAT].
Qed.

Lemma arealloc_post_okA : forall st sts E ms mo r hargs wnl st1 kf sh cred h1 h2 h3 h4 h5 stN
    (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) p lenf n rr RNG' msP mo',
  st_ok bsegs OPS E st ms mo ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  find_twin (s_facts st) kf = Some sh -> afree_ok st wnl kf sh = true -> no_views_on (s_facts st) (s_regs st) kf sh = true ->
  twin_canon st wnl kf sh = true ->
  heap_A hargs = Some cred -> size_shape_ok (s_facts st) (getr st X11) = true -> cred_pre (s_facts st) (getr st X11) cred = true ->
  prist_absent (s_facts st) hargs = true ->
  heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK = Some h1 -> heap_del_window_k h1 (VP sh wzero) K_TWIN = Some h2 ->
  heap_set_A h2 (cred_post (s_facts st) (getr st X11) cred) = Some h3 ->
  heap_add_window h3 (VP (s_next (clobber st1)) wzero) (getr st X11) (VL CtrLib.K_BLOCK) = Some h4 ->
  heap_add_window h4 (VP (PrimInt63.add (s_next (clobber st1)) 1%uint63) wzero) (twin_len (getr st X11)) (VL K_TWIN) = Some h5 ->
  sts = [stN; arealloc_stB st st1 r h5 kf sh cred] ->
  CtrA.win_lookup wnl kf = Some (lenf, CtrLib.K_BLOCK) ->
  In (HB p (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf))) LBa ->
  n = bv_unsigned (den E (getr st X11)) ->
  let R := ms_regs ms in
  AInstanceU2F.TwinB.arealloc_post2 (aci AI) (AHEAP AI) L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa p (bv_unsigned (ev E kf)) (bv_unsigned (den E lenf)) n
     (CtrPre.TwinB.sp_lo E st) (ms_mem ms) rr RNG' msP ->
  (forall UB, match snd rr with
              | Some q => ACCT (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) L RNG' (fst rr) (HB q UB n :: lb_remove p LBa) mo'
              | None => True
              end) ->
  op_minv OPS mo' -> OTHER mo mo' ->
  exists stB E1, sts = [stN; stB] /\ env_ext (s_next st) E E1 /\ st_ok bsegs OPS E1 stB msP mo'.
Proof.
  intros st sts E ms mo r hargs wnl st1 kf sh cred h1 h2 h3 h4 h5 stN L RNG sta LBa aw p lenf n rr RNG' msP mo'
         HS CP FS CF FT FOKk NV TCAN HA SHAPE NCP PRA H1 H2 H3 H4 H5 -> WLf0 HP En R HQ ACP MINVo OTH.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & AR & TI)).
  destruct (afree_ok_inv E st ms mo HS wnl kf sh FOKk) as (rf & lenf' & lent & Frf & WLf & WLt & BTs & LO0 & POSf & LEf & OTHERS).
  rewrite WLf0 in WLf. injection WLf as <-. pose proof WLf0 as WLf.
  assert (NOPR : ~ In prist_win (wins_of E nn rest)).
  { intros IP. apply (CtrPre.TwinB.prist_absent_not_in E st hargs (so_facts _ _ _ _ _ _ HS) Hf PRA). exists hargs, md, A, nw, rest. rewrite <- Nn. auto. }
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  destruct HQ as (FPLE & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV' & STK' & PRES & TWP & POSTB).
  destruct (snd rr) as [q|] eqn:SR; [| contradiction].
  destruct POSTB as (UB & srcb & junk & EA0 & BRN & AH' & _ & _ & _ & _ & _ & PATN).
  specialize (ACP UB). cbv beta iota in ACP.
  rewrite Eh, heap_A_eq in HA. injection HA as <-.
  set (R' := mkR (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) t0 t1 t2 (AP.getr R 8) (AP.getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) t3 t4 t5 t6) in *.
  set (Fv := CtrPost.TwinB.cfvA R' (Z_to_bv 64 UB) (Z_to_bv 64 (shad UB))).
  set (Gv := fun (_ : Z) (o : Z) => match m' (ALib.Mem.wa (UB + o)) with Some b => b | None => Z_to_bv 8 0 end).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.TwinB.den_wlit. }
  assert (EMS' : msP = CtrFrame.TwinB.ms' ms r R' m').
  { rewrite EMS. unfold CtrFrame.TwinB.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  eexists. exists (CtrFrame.TwinB.E' E st Fv Gv). split; [reflexivity|]. split; [apply CtrFrame.TwinB.EXT|]. rewrite EMS'.
  assert (KBE : s_next (clobber st1) = kB st) by (eapply kB_next; eassumption).
  assert (KSE : PrimInt63.add (kB st) 1%uint63 = kS st) by (eapply kS_next; eassumption).
  rewrite KBE in H4. rewrite KBE, KSE in H5.
  assert (WORLD : aw_holds_asan AI ACCT UNIV (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) (LBr E LB kf lenf UB n) m' mo').
  { exact (WORLDr_asan E ms mo LB aw L RNG sta LBa W WOF AR kf lenf p q UB n RNG' (fst rr) m' mo' (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) HP AH' ACP PRES TWP PATN). }
  eapply (realloc_post E st ms mo HS wnl nn rest LB aw L RNG sta LBa NW AN WF W WOF AR TI NOPR
            (CtrFree.TwinB.cvu_of Cw Cw_vec_unowned E st (ms_mem ms) LB nn md A nw rest ltac:(rewrite <- Eh; exact Hf) Nn HC) kf sh NV TCAN rf lenf lent Frf WLf WLt BTs LO0 POSf LEf OTHERS
            p q UB n RNG' (fst rr) m' mo' (Z_to_bv 64 (bv_unsigned aw - (if prim_decided (s_facts st) (getr st X11) then 0 else n))) HP AH' ACP PRES TWP PATN hargs md A nw Hf Eh Tnw Nn Ln FOK Fv Gv h1 h2 H1 H2)
    with (pd := prim_decided (s_facts st) (getr st X11)) (ks := ks) (offs := offs) (rss := rss) (ksp := ksp) (R' := R') (h3 := h3) (h4 := h4); try eassumption; try reflexivity.
  -   unfold nsv. symmetry. exact En.
  -   intros o Ho. unfold Gv, rb.
    destruct (aw_user_ok_asan AI ACCT UNIV AI_fake _ _ m' mo' (UB, n) (UB + o) WORLD ltac:(right; left; reflexivity) ltac:(unfold in_iv; cbn [fst snd]; lia)) as [MP _].
    unfold ALib.Mem.wa. destruct (m' (Z_to_bv 64 (UB + o))); [reflexivity| contradiction].
  -   intros rg Hrg. unfold CtrFrame.TwinB.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
  -   intros x i Hx. exact (CtrPost.TwinB.cfvA_clob R' _ _ x i Hx).
  -
    pose proof (so_facts _ _ _ _ _ _ HS) as HF9. unfold f_cred, cred_fact, cred_pre, nsv in *.
    try (rewrite Eh, heap_A_eq in HA; injection HA as <-). apply andb_prop in NCP as [NX9 NC9].
    destruct (prim_decided (s_facts st) (getr st X11)); cbn [fact_holds].
    + exact (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF9 NX9).
    + cbn [orb] in NC9. exact (KnownA.TwinB.KnownA.known_leu_sound E _ _ _ HF9 NC9).
Qed.

End Realloc.
End TwinB.
