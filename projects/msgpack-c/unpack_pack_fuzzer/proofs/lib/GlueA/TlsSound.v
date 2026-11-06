(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_tlsga. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_tlsP AInstanceU AInstanceUT AInstanceU2 AInstanceU2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require ExhFirst.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase StepSoundMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV GlueA CtrPre FrameV CtrFrame CtrFree CtrNoDelta FakeLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepM CtrFX ActrA.
Local Notation AIu2 := (AInstanceU2.AIu2 ExhFirst.exh_first).
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module TP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_tlsP.

Definition TLSW : w64 := wlit 6345856%uint63.

Definition tls_postA {rc : runConstT} (AI : AMallocIface2) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TP.ATLSADDR) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (MState.ret_pc ra) fc None m' (seg_rom asegs)
    /\ AM.mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ munch [(bv_unsigned sp - TP.TLSGA_STACK, bv_unsigned sp)] m m' /\ wmono asegs m m'
    /\ aheap_pres (aci AI) LB (bv_unsigned sp) m m'
    /\ AHEAP AI L RNG st LB m'.

Definition tls_walk_stmt {rc : runConstT} (AI : AMallocIface2) (entry : Z) : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo A : Z),
  AHEAP AI L RNG st LB m ->
  AM.mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - TP.TLSGA_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> bv_unsigned sp <= A ->
  AS.ro_cells asegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG A 16 ->
  evtF asegs RNG (tls_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Lemma aheap_windows_hargs : forall st h wl, ActrA.aheap_windows st = Some (h, wl) -> find_op HEAP_ID (s_ops st) = Some h.
Proof.
  intros st h wl H. unfold ActrA.aheap_windows in H.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|]; [|discriminate H].
  destruct (CtrA.count_op HEAP_ID (s_ops st)) as [|[|?]]; try discriminate H.
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|]; [|discriminate H].
  destruct (heap_nwin hargs) as [n|]; [|discriminate H].
  destruct hargs as [|? [|? [|? rest]]]; try discriminate H.
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate H] end.
  destruct (CtrA.nonstack_windows n rest) as [wl0|]; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate H] end.
  injection H as <- _. reflexivity.
Qed.

Lemma acall_pre_bridgeB : forall room st r hargs st1,
  ActrB.acall_pre ActrA.ATPi room st = Some (r, hargs) -> ActrA.forget_stack_below_sp_g st = Some st1 ->
  exists wl, ActrA.acall_pre room None st = Some (r, hargs, wl, st1).
Proof.
  intros room st r hargs st1 H FS. unfold ActrB.acall_pre in H. unfold ActrA.acall_pre.
  destruct (call_pre st) as [r0|]; [|discriminate H].
  destruct (getr st X4) as [tp| | | | | | | | | |]; try discriminate H.
  destruct (find_op HEAP_ID (s_ops st)) as [h0|] eqn:FO; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  injection H as <- <-.
  repeat match type of CK with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CK as [CK X] end.
  unfold ActrA.twins_intact in Q. destruct (ActrA.aheap_windows st) as [[h wl]|] eqn:AW; [|discriminate Q].
  pose proof (aheap_windows_hargs st h wl AW) as FH. rewrite FO in FH. injection FH as <-.
  exists wl. unfold ActrB.stack_room_g in Q2. rewrite CK, Q2, Q1, Q0. cbn [andb]. rewrite FS. reflexivity.
Qed.

Lemma tls_apply_shape : forall TLSADDR st sts, ActrB.tls_get_addr_apply asegs ActrA.ATPi TLSADDR st = Some sts ->
  exists r hargs k off rg o0 o8 offs st1,
       ActrB.acall_pre ActrA.ATPi 4096%uint63 st = Some (r, hargs)
    /\ getr st X10 = VP k off /\ IMap.find k (s_regs st) = Some rg /\ okey off = Some o0 /\ okey (wadd off (wlit 8%uint63)) = Some o8
    /\ can_read asegs (s_facts st) (s_priv st) k rg o0 8%uint63 = true /\ can_read asegs (s_facts st) (s_priv st) k rg o8 8%uint63 = true
    /\ region_load asegs k rg o0 8%uint63 false = Some (VL wone) /\ region_load asegs k rg o8 8%uint63 false = Some (VL wzero)
    /\ getr st X2 = VP k offs /\ wlts off offs = false
    /\ ActrA.forget_stack_below_sp_g st = Some st1
    /\ sts = [setpc (setr (clobber st1) X10 (VL TLSADDR)) r].
Proof.
  intros TLSADDR st sts H. unfold ActrB.tls_get_addr_apply in H.
  destruct (ActrB.acall_pre ActrA.ATPi 4096%uint63 st) as [[r hargs]|] eqn:PRE; [|discriminate H].
  destruct (getr st X10) as [|k off| | | | | | | | |] eqn:HX10; try discriminate H.
  destruct (IMap.find k (s_regs st)) as [rg|] eqn:FR; [|discriminate H].
  destruct (okey off) as [o0|] eqn:K0; [|discriminate H].
  destruct (okey (wadd off (wlit 8%uint63))) as [o8|] eqn:K8; [|discriminate H].
  destruct (can_read asegs (s_facts st) (s_priv st) k rg o0 8%uint63 && can_read asegs (s_facts st) (s_priv st) k rg o8 8%uint63)%bool eqn:CR;
    cbn [negb] in H; [|discriminate H]. apply andb_prop in CR as [CR0 CR8].
  destruct (region_load asegs k rg o0 8%uint63 false) as [[m| | | | | | | | | |]|] eqn:RL0; try discriminate H.
  destruct (region_load asegs k rg o8 8%uint63 false) as [[o| | | | | | | | | |]|] eqn:RL8; try discriminate H.
  destruct (getr st X2) as [|ks offs| | | | | | | | |] eqn:HX2; cbn zeta in H;
    try (rewrite Bool.andb_false_r in H; discriminate H).
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  apply andb_prop in CK as [CK AB]. apply andb_prop in CK as [M1 O0]. apply andb_prop in AB as [KS WL]. apply negb_true_iff in WL.
  apply Uint63.eqb_correct in KS. subst ks.
  assert (EM : m = wone) by (apply weqb_ok; exact M1). assert (EO : o = wzero) by (apply weqb_ok; exact O0). subst m o.
  unfold ActrB.forget_stack_below_sp_g in H. destruct (ActrA.forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate H].
  injection H as <-.
  exists r, hargs, k, off, rg, o0, o8, offs, st1. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Section MemLemmas.
Variable segs : list Segment.
Lemma ov_read_bytes_inv : forall m A n bs, ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs ->
  0 <= A -> A + Z.of_nat n <= two64 ->
  length bs = n /\ forall i, 0 <= i < Z.of_nat n -> rb segs m (A + i) = nth_error bs (Z.to_nat i).
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A bs H HA HAn.
  - cbn in H. injection H as <-. split; [reflexivity | intros i Hi; lia].
  - cbn [ov_read_bytes] in H. rewrite <- rb_unfold in H.
    destruct (rb segs m A) as [b|] eqn:Hb; [|discriminate H].
    rewrite Z_to_bv_succ in H.
    destruct (ov_read_bytes segs m (Z_to_bv 64 (A + 1)) n) as [bs'|] eqn:Hr; [|discriminate H]. injection H as <-.
    destruct (IH (A + 1) bs' Hr ltac:(lia) ltac:(lia)) as [Hlen Hbs]. split; [cbn; lia|].
    intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Z.add_0_r. cbn. exact Hb.
    + replace (A + i) with (A + 1 + (i - 1)) by lia. rewrite Hbs by lia.
      replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma stored_is_loaded : forall (w : int) (x : word) bs, (to_Z w = 1 \/ to_Z w = 8) -> length bs = Z.to_nat (to_Z w) ->
  x = ext_word false 0 (to_Z w) (le_bytes_to_word bs) -> store_bytes w x = bs.
Proof.
  intros w x bs Hw Len ->.
  pose proof (MemFX.MemFX.Z_to_le_bytes_to_Z bs) as RT. pose proof (bytes_le_to_Z_bound bs) as BD.
  destruct Hw as [W1|W8].
  - assert (w = 1%uint63) by (apply Uint63.to_Z_inj; rewrite W1; reflexivity). subst w. change (to_Z 1%uint63) with 1 in *.
    change (Z.to_nat 1) with 1%nat in Len. destruct bs as [|b [|? ?]]; try discriminate Len. clear RT BD.
    rewrite <- (bytes_val_ext_word false 1 [b] eq_refl ltac:(lia)). unfold store_bytes, bytes_val.
    change (Z.to_nat (to_Z 1%uint63)) with 1%nat. cbn [Z_to_le_bytes]. f_equal.
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
    assert (EB : bytes_le_to_Z [b] = bv_unsigned b) by (rewrite bytes_le_to_Z_cons; cbn; lia).
    rewrite EB, (ext_Z_small_id false 1 (bv_unsigned b)); [| lia| unfold two64; lia| change (2 ^ (8 * 1 - 0)) with 256; lia].
    apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite (bv_wrap_small 64 (bv_unsigned b)) by (rewrite bv_modulus_64; unfold W64.two64; lia).
    apply bv_wrap_small. unfold bv_modulus. cbn. lia.
  - assert (w = 8%uint63) by (apply Uint63.to_Z_inj; rewrite W8; reflexivity). subst w. change (to_Z 8%uint63) with 8 in *.
    rewrite <- store_bytes_64. rewrite <- RT at 2. rewrite Len. change (Z.to_nat 8) with 8%nat. f_equal.
    rewrite Len in BD. change (8 * Z.of_nat (Z.to_nat 8)) with 64 in BD.
    rewrite ext_word_id64. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact BD.
Qed.

End MemLemmas.

Lemma w2Zs_wadd_small : forall a b, - two63 <= w2Zs a + w2Z b < two63 -> w2Zs (wadd a b) = w2Zs a + w2Z b.
Proof.
  intros a b H. rewrite (w2Zs_eq (wadd a b)), w2Z_wt, wadd_ok.
  rewrite (w2Zs_eq a), (w2Z_wt a) in H |- *.
  pose proof (w2Z_range a) as Ra. pose proof (w2Z_range b) as Rb. unfold two63, two64 in *.
  destruct (Z.leb_spec 9223372036854775808 (w2Z a));
  destruct (Z_lt_le_dec (w2Z a + w2Z b) 18446744073709551616);
  try (rewrite (Z.mod_small (w2Z a + w2Z b)) by lia; destruct (Z.leb_spec 9223372036854775808 (w2Z a + w2Z b)); lia);
  try (replace (w2Z a + w2Z b) with ((w2Z a + w2Z b - 18446744073709551616) + 1 * 18446744073709551616) by lia;
       rewrite Z.mod_add, Z.mod_small by lia;
       destruct (Z.leb_spec 9223372036854775808 (w2Z a + w2Z b - 18446744073709551616)); lia).
Qed.

Section Blk.
Context {rc : runConstT}.
Variable OPS : optable.

Lemma load8_bytes : forall E st ms mo k rg key v, st_ok asegs OPS E st ms mo ->
  IMap.find k (s_regs st) = Some rg -> can_read asegs (s_facts st) (s_priv st) k rg key 8%uint63 = true ->
  region_load asegs k rg key 8%uint63 false = Some v ->
  AM.bytes_at asegs (ms_mem ms) (addrZ E k key) (AM.le8 (den E v))
  /\ (PrimInt63.eqb k 0%uint63 = false -> loZ rg <= keyZ key /\ keyZ key + 8 <= hiZ E rg).
Proof.
  intros E st ms mo k rg key v HS FR CR RL.
  pose proof (so_reg _ _ _ _ _ _ HS _ _ FR) as RO.
  destruct (MemP.can_read_sound asegs (s_priv st) E (ms_mem ms) (s_facts st) k rg key 8%uint63
              (so_facts _ _ _ _ _ _ HS) (so_zero _ _ _ _ _ _ HS) RO ltac:(right; right; right; reflexivity) CR) as (LO & HI & _ & INR & _).
  change (to_Z 8%uint63) with 8 in HI, INR.
  destruct (MemP.region_load_sound asegs (s_priv st) E (ms_mem ms) (s_facts st) k rg key 8%uint63 false v
              (so_facts _ _ _ _ _ _ HS) (so_zero _ _ _ _ _ _ HS) RO ltac:(right; right; right; reflexivity) CR RL) as (bs & LEN & OV & DEN).
  change (Z.to_nat (to_Z 8%uint63)) with 8%nat in LEN, OV.
  destruct (ov_read_bytes_inv asegs (ms_mem ms) _ 8 bs OV LO ltac:(change (Z.of_nat 8) with 8; exact HI)) as [_ RB].
  assert (EBS : bs = AM.le8 (den E v)).
  { rewrite <- (stored_is_loaded 8%uint63 (den E v) bs ltac:(right; reflexivity) LEN).
    - rewrite <- StepM.store_bytes_64. apply AS.store_bytes_8'.
    - rewrite DEN. apply StepM.bytes_val_ext_word; [exact LEN| change (to_Z 8%uint63) with 8; lia]. }
  split.
  - rewrite <- EBS. split; [exact LO|]. split; [rewrite LEN; unfold two64 in HI; lia|]. intros i Hi. rewrite LEN in Hi.
    change (AM.mrd asegs (ms_mem ms) (AM.wa (addrZ E k key + Z.of_nat i))) with (rb asegs (ms_mem ms) (addrZ E k key + Z.of_nat i)).
    rewrite (RB (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
  - intros KZ. pose proof (INR KZ 0 ltac:(lia)) as I0. pose proof (INR KZ 7 ltac:(lia)) as I7. lia.
Qed.

Lemma arg_block : forall E st ms mo k rg off o0 o8, st_ok asegs OPS E st ms mo ->
  IMap.find k (s_regs st) = Some rg -> PrimInt63.eqb k 0%uint63 = false ->
  okey off = Some o0 -> okey (wadd off (wlit 8%uint63)) = Some o8 ->
  can_read asegs (s_facts st) (s_priv st) k rg o0 8%uint63 = true -> can_read asegs (s_facts st) (s_priv st) k rg o8 8%uint63 = true ->
  region_load asegs k rg o0 8%uint63 false = Some (VL wone) -> region_load asegs k rg o8 8%uint63 false = Some (VL wzero) ->
  let A := addrZ E k o0 in
  AS.ro_cells asegs (ms_mem ms) A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)]
  /\ den E (VP k off) = Z_to_bv 64 A /\ 0 <= A /\ A + 16 <= bv_unsigned (ev E k) + hiZ E rg /\ keyZ o0 = w2Zs off.
Proof.
  intros E st ms mo k rg off o0 o8 HS FR KZ K0 K8 CR0 CR8 RL0 RL8 A.
  destruct (load8_bytes E st ms mo k rg o0 _ HS FR CR0 RL0) as [B0 IN0]. destruct (load8_bytes E st ms mo k rg o8 _ HS FR CR8 RL8) as [B8 IN8].
  specialize (IN0 KZ). specialize (IN8 KZ).
  destruct (okey_sound _ _ K0) as [E0 R0]. destruct (okey_sound _ _ K8) as [E8 R8].
  assert (E80 : keyZ o8 = keyZ o0 + 8).
  { rewrite E8, E0. rewrite w2Zs_wadd_small; [rewrite wlit_ok; reflexivity|]. rewrite wlit_ok. change (to_Z 8%uint63) with 8.
    rewrite <- E0. unfold two63 in *. lia. }
  assert (A8 : addrZ E k o8 = A + 8) by (unfold A, addrZ; lia).
  pose proof (AM.bytes_at_bound asegs _ _ _ B0) as BB0. rewrite AM.length_le8 in BB0.
  split; [| split; [| split; [lia| split; [unfold A, addrZ; lia| exact E0]]]].
  - split; [cbn; auto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (proj2 (AM.bytes_at_app asegs _ _ _ _)).
    rewrite AM.length_le8. change (Z.of_nat 8) with 8. rewrite <- A8.
    replace (Z_to_bv 64 1) with (den E (VL wone)) by (cbn [den]; apply bv_eq; reflexivity).
    replace (Z_to_bv 64 0) with (den E (VL wzero)) by (cbn [den]; apply bv_eq; reflexivity).
    split; [exact B0| exact B8].
  - apply bv_eq. rewrite den_VP, <- E0. rewrite Z_to_bv_unsigned. unfold A, addrZ in *. rewrite Z.mod_small by (unfold two64; lia).
    symmetry. apply bv_wrap_small. rewrite bv_modulus_64. unfold W64.two64. lia.
Qed.
End Blk.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Hypothesis IMGSH_aci : forall v a, In v Op.SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.cov1 HEAP_ID args z.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Variable ENTRY : Z.
Hypothesis WALK : tls_walk_stmt AI ENTRY.
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Definition acct_leaf_silent (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa mo'.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent mo aw L st LBa).

Theorem tls_get_addr_sound : forall pc, to_Z pc = ENTRY -> contract_sound asegs OPS MP PB (ActrB.tls_get_addr_c asegs pc ActrA.ATPi TLSW).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc ActrB.tls_get_addr_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = ENTRY) by (rewrite Hspc; exact Hpc).
  destruct (tls_apply_shape TLSW st sts Happ) as (r & hargs & k & off & rg & o0 & o8 & offs & st1 & PREB & HX10 & FR & K0 & K8 & CR0 & CR8 & RL0 & RL8 & HX2 & WL & FS0 & ESTS).
  destruct (acall_pre_bridgeB 4096%uint63 st r hargs st1 PREB FS0) as [wnl PRE].
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng 4096%uint63 None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  set (R := ms_regs ms) in *. set (spw := AP.getr R 2) in *. set (sp := bv_unsigned spw) in *.
  pose proof atop_range as ATR.
  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs' & rss & ksp & nn & md & Aa & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (Wt & WOF & ARW & TI)).
  destruct (CallA.sp_region_inv st ks offs' rss SPR) as (HX2' & Hrs & KSZ & _).
  rewrite HX2 in HX2'. injection HX2' as <- <-. rewrite FR in Hrs. injection Hrs as <-.

  destruct (arg_block OPS E st ms mo k rg off o0 o8 HS FR KSZ K0 K8 CR0 CR8 RL0 RL8) as (BLK & DA & A0 & AHI & EK0).
  set (A := addrZ E k o0) in *.
  assert (KN0 : k <> 0%uint63) by (intros ->; discriminate KSZ).
  assert (TOPk : bv_unsigned (ev E k) + hiZ E rg <= 2 ^ 47).
  { destruct (CallA.aregion_just_sound asegs OPS E st ms mo wnl k offs rg k rg HS SPR AJ FR KN0) as [[_ T]|[NE _]]; [exact T| exfalso; apply NE; reflexivity]. }
  assert (SPA : sp <= A).
  { destruct (okey_sound _ _ Hksp) as [Eksp _]. rewrite wlts_w2Zs in WL. apply Z.ltb_ge in WL.
    unfold sp, spw. fold R in SPE. rewrite SPE. unfold A, addrZ. rewrite EK0, Eksp. lia. }
  assert (GA0 : AP.getr R 10 = Z_to_bv 64 A).
  { unfold R. rewrite <- HeapCtr.reg_of_X10, (GlueA.getr_RA asegs OPS E st ms mo HS X10), HX10. exact DA. }
  change (to_Z 4096%uint63) with 4096 in LOR.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  assert (RNGA : rng RNG A 16) by (eapply rng_sub'; [exact (ACCT_rng _ _ _ _ _ _ AC)| fold sp in LOR, BOT; lia]).
  pose proof (WALK L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa (CtrPre.sp_lo E st) A AH MI ST BOT
                ltac:(unfold TP.TLSGA_STACK; fold spw; fold sp; fold spw in LOR; fold sp in LOR; lia) TP GA0 SPA BLK RSTK RNGA) as EV.
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ tls_postA AI L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa (CtrPre.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV'' & STK' & MU & WM & PRES & AH').
    fold spw in PRES, STK'. fold sp in PRES, STK'.
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    set (m := ms_mem ms) in *.
    set (Fv := CtrFree.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
    destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
    assert (EMS' : ms' = CtrFrame.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.ms'. f_equal. fold R. rewrite RA. apply MState.ret_pc_even.
      - lia.
      - pose proof (HeapCtr.call_pre_even st r CP) as EV0.
        pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV0 in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
    destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0' & OP & PV & NXc).
    destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
    assert (SHAPE : sts = [SS r (rf_set (s_rf (clobber st1)) X10 (VL TLSW)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st)
                              (s_ops st) (s_priv st) (s_next (clobber st1))]).
    { rewrite ESTS. apply (f_equal (fun x : sstate => [x])).
      assert (G : forall (S : sstate) v, setpc (setr S X10 v) r
                  = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (s_regs S) (s_facts S) (s_ops S) (s_priv S) (s_next S)) by (intros [] ?; reflexivity).
      rewrite G, FF, RV, RG, FS0', OP, PV, FF1, RV1, FS1, OP1, PV1. reflexivity. }
    apply (HK _ ltac:(rewrite SHAPE; left; reflexivity) (CtrFrame.E' E st Fv Gv) ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
    rewrite EMS'.
    assert (RAWV : forall a, m' (AM.wa a) = m (AM.wa a) -> rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true)).
    { intros a EQ. split; [unfold rb; unfold AM.wa in EQ; rewrite EQ; reflexivity|].
      intros Wb. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in Wb. rewrite (wview_ext1 m' m _ EQ). exact Wb. }
    assert (TWP : twins_pres LBa m m').
    { apply (Op.twins_pres_band AI L RNG sta LBa m m' AH). intros a Ha.
      assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SA in Ha. unfold ASHOFF in Ha.
      assert (RA0 : 0 <= a < 2 ^ 64) by (clear - Ha ATR; Z.div_mod_to_equations; lia).
      apply (MU (AM.wa a)). unfold AM.wa. rewrite Z_to_bv_small by (unfold bv_modulus; exact RA0).
      cbn [outside]. split; [| exact I]. unfold TP.TLSGA_STACK. fold sp in LOR, BOT. intros [Q1 Q2]. fold spw in Q1, Q2. fold sp in Q1, Q2. clear - Ha ATR LOR BOT Q1 Q2. Z.div_mod_to_equations. lia. }
    assert (STB : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LB0 a ->
              m' (AM.wa a) = m (AM.wa a)).
    { intros LB0 (W0 & (E1 & E2 & E3 & E4) & ARW0) a Ha ST0. pose proof ARW0 as [HW0 _]. pose proof HW0 as (_ & HT0 & _).
      destruct (LB_classify AI ACCT UNIV AI_fake W0 aw LB0 m mo HW0) as (KU & KT).
      apply (aw_real_stable AI ACCT UNIV AI_fake aw LB0 m mo W0 RNG sta LBa m' LBa LB0 sp LBa TWP ltac:(intros b0 Hb0 _ _; rewrite <- E4; exact Hb0) ARW0).
      - rewrite E1. exact AH'.
      - exact PRES.
      - intros v Hv UB P. destruct (KU v Hv UB P) as (b & Vb & ->). exists b. split; [rewrite <- E4; exact (proj1 Vb)| reflexivity].
      - intros v Hv NUB. destruct (KT v Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
        + left. exists b. destruct (HT0 b Hb) as [HbL HH0]. split; [exact HbL|]. split; [rewrite <- E4; exact HbL|]. split; [exact HH0| reflexivity].
        + right. exists b. split; [exact (proj1 (proj1 Vb))|]. split; [rewrite <- E4; exact (proj1 (proj1 Vb))|]. split; [exact (proj2 Vb)| reflexivity].
      - exact Ha.
      - exact ST0. }
    apply (CtrNoDelta.nodelta_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
             OPS_cov0_img E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG sta _ _ HS CP FS CF).
    --
      intros rg0 Hrg. unfold CtrFrame.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
    -- intros x i Hx. exact (CtrFree.cfvF_clob R' x i Hx).
    --   cbn [den]. apply bv_eq. reflexivity.
    -- exact MINV''.
    -- exact STK'.
    --   intros LB0 AR0 a Ha STa. apply RAWV. exact (STB LB0 AR0 a Ha STa).
    --   intros LB0 AR0 a Ha IU. apply (STB LB0 AR0 a Ha). right; right. exact IU.
    --
      intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
      destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STKZ & ->)]].
      + pose proof (proj1 (PRES a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact INA))) as E0. unfold AM.wa in E0. exact E0.
      + pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [right; left; exact INA| reflexivity]))) as E0.
        unfold AM.wa in E0. exact E0.
      +
        pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact STKZ| reflexivity]))) as E0.
        unfold AM.wa in E0. exact E0.
    --   exact (CtrFrame.WBM_of_pres AI LBa sp m m' PRES).
    --
      intros a Ha SC IB. apply RAWV.
      assert (CA : aclient_addr (aci AI) LBa sp a).
      { destruct SC as [(a' & RRa & ->)|(vv & Hv & RRa)].
        - right; right; right. exists a'. split; [left; exact RRa| reflexivity].
        - destruct (IMGSH_aci vv a Hv RRa) as (a' & INA & ->). right; right; right. exists a'. split; [right; left; exact INA| reflexivity]. }
      exact (proj1 (PRES a Ha CA)).
    -- exact AH'.
    -- exact ACP.
    --
      intros b x Hb FK Hx. pose proof (Op.blk_band AI AI_fake L RNG sta LBa m b x AH Hb Hx) as BB.
      exact (proj1 (PRES x ltac:(unfold AIMG_HI, KLS in BB; lia) ltac:(right; right; left; exists b; split; [exact Hb| exact Hx]))).
    -- exact TWP.
    -- exact OTH.
    -- exact HMI'.
    -- exact (fun P => P).
Qed.
End Sound.

Section Inst.
Context {rc : runConstT}.
Lemma AIu_tls_walk : tls_walk_stmt AIu2 F_tlsga.F_tlsga.ATLSGA_ICPT.
Proof.
  unfold tls_walk_stmt. intros until A. intros AH MI ST BOT LO TPE A0 ABV BLK RSTK RA.
  exact (AInstanceU2F.AHU2_tlsga L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           FR fc m st LB lo A AH MI ST BOT LO TPE A0 ABV BLK RSTK RA).
Qed.
End Inst.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import ActrB.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepM CtrFX ActrA.
Local Notation AIu2 := (AInstanceU2.TwinB.AIu2 ExhFirst.TwinB.exh_first).
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module TP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_tlsP.TwinB.

Definition TLSW : w64 := wlit 6354496%uint63.

Definition tls_postA {rc : runConstT} (AI : AMallocIface2) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TP.ATLSADDR) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (MState.ret_pc ra) fc None m' (seg_rom bsegs)
    /\ AM.mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ munch [(bv_unsigned sp - TP.TLSGA_STACK, bv_unsigned sp)] m m' /\ wmono bsegs m m'
    /\ aheap_pres (aci AI) LB (bv_unsigned sp) m m'
    /\ AHEAP AI L RNG st LB m'.

Definition tls_walk_stmt {rc : runConstT} (AI : AMallocIface2) (entry : Z) : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo A : Z),
  AHEAP AI L RNG st LB m ->
  AM.mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - TP.TLSGA_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> bv_unsigned sp <= A ->
  AS.ro_cells bsegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG A 16 ->
  evtF bsegs RNG (tls_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 entry) fc None m (seg_rom bsegs)).

Lemma aheap_windows_hargs : forall st h wl, ActrA.aheap_windows st = Some (h, wl) -> find_op HEAP_ID (s_ops st) = Some h.
Proof.
  intros st h wl H. unfold ActrA.aheap_windows in H.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|]; [|discriminate H].
  destruct (CtrA.count_op HEAP_ID (s_ops st)) as [|[|?]]; try discriminate H.
  destruct (IMap.find STACK_ID (s_regs st)) as [r1|]; [|discriminate H].
  destruct (heap_nwin hargs) as [n|]; [|discriminate H].
  destruct hargs as [|? [|? [|? rest]]]; try discriminate H.
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate H] end.
  destruct (CtrA.nonstack_windows n rest) as [wl0|]; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate H] end.
  injection H as <- _. reflexivity.
Qed.

Lemma acall_pre_bridgeB : forall room st r hargs st1,
  ActrB.TwinB.ActrB.acall_pre ActrA.ATPi room st = Some (r, hargs) -> ActrA.forget_stack_below_sp_g st = Some st1 ->
  exists wl, ActrA.acall_pre room None st = Some (r, hargs, wl, st1).
Proof.
  intros room st r hargs st1 H FS. unfold ActrB.TwinB.ActrB.acall_pre in H. unfold ActrA.acall_pre.
  destruct (call_pre st) as [r0|]; [|discriminate H].
  destruct (getr st X4) as [tp| | | | | | | | | |]; try discriminate H.
  destruct (find_op HEAP_ID (s_ops st)) as [h0|] eqn:FO; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  injection H as <- <-.
  repeat match type of CK with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CK as [CK X] end.
  unfold ActrA.twins_intact in Q. destruct (ActrA.aheap_windows st) as [[h wl]|] eqn:AW; [|discriminate Q].
  pose proof (aheap_windows_hargs st h wl AW) as FH. rewrite FO in FH. injection FH as <-.
  exists wl. unfold ActrB.TwinB.ActrB.stack_room_g in Q2. rewrite CK, Q2, Q1, Q0. cbn [andb]. rewrite FS. reflexivity.
Qed.

Lemma tls_apply_shape : forall TLSADDR st sts, ActrB.TwinB.ActrB.tls_get_addr_apply bsegs ActrA.ATPi TLSADDR st = Some sts ->
  exists r hargs k off rg o0 o8 offs st1,
       ActrB.TwinB.ActrB.acall_pre ActrA.ATPi 4096%uint63 st = Some (r, hargs)
    /\ getr st X10 = VP k off /\ IMap.find k (s_regs st) = Some rg /\ okey off = Some o0 /\ okey (wadd off (wlit 8%uint63)) = Some o8
    /\ can_read bsegs (s_facts st) (s_priv st) k rg o0 8%uint63 = true /\ can_read bsegs (s_facts st) (s_priv st) k rg o8 8%uint63 = true
    /\ region_load bsegs k rg o0 8%uint63 false = Some (VL wone) /\ region_load bsegs k rg o8 8%uint63 false = Some (VL wzero)
    /\ getr st X2 = VP k offs /\ wlts off offs = false
    /\ ActrA.forget_stack_below_sp_g st = Some st1
    /\ sts = [setpc (setr (clobber st1) X10 (VL TLSADDR)) r].
Proof.
  intros TLSADDR st sts H. unfold ActrB.TwinB.ActrB.tls_get_addr_apply in H.
  destruct (ActrB.TwinB.ActrB.acall_pre ActrA.ATPi 4096%uint63 st) as [[r hargs]|] eqn:PRE; [|discriminate H].
  destruct (getr st X10) as [|k off| | | | | | | | |] eqn:HX10; try discriminate H.
  destruct (IMap.find k (s_regs st)) as [rg|] eqn:FR; [|discriminate H].
  destruct (okey off) as [o0|] eqn:K0; [|discriminate H].
  destruct (okey (wadd off (wlit 8%uint63))) as [o8|] eqn:K8; [|discriminate H].
  destruct (can_read bsegs (s_facts st) (s_priv st) k rg o0 8%uint63 && can_read bsegs (s_facts st) (s_priv st) k rg o8 8%uint63)%bool eqn:CR;
    cbn [negb] in H; [|discriminate H]. apply andb_prop in CR as [CR0 CR8].
  destruct (region_load bsegs k rg o0 8%uint63 false) as [[m| | | | | | | | | |]|] eqn:RL0; try discriminate H.
  destruct (region_load bsegs k rg o8 8%uint63 false) as [[o| | | | | | | | | |]|] eqn:RL8; try discriminate H.
  destruct (getr st X2) as [|ks offs| | | | | | | | |] eqn:HX2; cbn zeta in H;
    try (rewrite Bool.andb_false_r in H; discriminate H).
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:CK; [|discriminate H] end.
  apply andb_prop in CK as [CK AB]. apply andb_prop in CK as [M1 O0]. apply andb_prop in AB as [KS WL]. apply negb_true_iff in WL.
  apply Uint63.eqb_correct in KS. subst ks.
  assert (EM : m = wone) by (apply weqb_ok; exact M1). assert (EO : o = wzero) by (apply weqb_ok; exact O0). subst m o.
  unfold ActrB.TwinB.ActrB.forget_stack_below_sp_g in H. destruct (ActrA.forget_stack_below_sp_g st) as [st1|] eqn:FS; [|discriminate H].
  injection H as <-.
  exists r, hargs, k, off, rg, o0, o8, offs, st1. repeat (split; [reflexivity || assumption|]). reflexivity.
Qed.

Section MemLemmas.
Variable segs : list Segment.
Lemma ov_read_bytes_inv : forall m A n bs, ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs ->
  0 <= A -> A + Z.of_nat n <= two64 ->
  length bs = n /\ forall i, 0 <= i < Z.of_nat n -> rb segs m (A + i) = nth_error bs (Z.to_nat i).
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A bs H HA HAn.
  - cbn in H. injection H as <-. split; [reflexivity | intros i Hi; lia].
  - cbn [ov_read_bytes] in H. rewrite <- rb_unfold in H.
    destruct (rb segs m A) as [b|] eqn:Hb; [|discriminate H].
    rewrite Z_to_bv_succ in H.
    destruct (ov_read_bytes segs m (Z_to_bv 64 (A + 1)) n) as [bs'|] eqn:Hr; [|discriminate H]. injection H as <-.
    destruct (IH (A + 1) bs' Hr ltac:(lia) ltac:(lia)) as [Hlen Hbs]. split; [cbn; lia|].
    intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Z.add_0_r. cbn. exact Hb.
    + replace (A + i) with (A + 1 + (i - 1)) by lia. rewrite Hbs by lia.
      replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma stored_is_loaded : forall (w : int) (x : word) bs, (to_Z w = 1 \/ to_Z w = 8) -> length bs = Z.to_nat (to_Z w) ->
  x = ext_word false 0 (to_Z w) (le_bytes_to_word bs) -> store_bytes w x = bs.
Proof.
  intros w x bs Hw Len ->.
  pose proof (MemFX.MemFX.Z_to_le_bytes_to_Z bs) as RT. pose proof (bytes_le_to_Z_bound bs) as BD.
  destruct Hw as [W1|W8].
  - assert (w = 1%uint63) by (apply Uint63.to_Z_inj; rewrite W1; reflexivity). subst w. change (to_Z 1%uint63) with 1 in *.
    change (Z.to_nat 1) with 1%nat in Len. destruct bs as [|b [|? ?]]; try discriminate Len. clear RT BD.
    rewrite <- (bytes_val_ext_word false 1 [b] eq_refl ltac:(lia)). unfold store_bytes, bytes_val.
    change (Z.to_nat (to_Z 1%uint63)) with 1%nat. cbn [Z_to_le_bytes]. f_equal.
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
    assert (EB : bytes_le_to_Z [b] = bv_unsigned b) by (rewrite bytes_le_to_Z_cons; cbn; lia).
    rewrite EB, (ext_Z_small_id false 1 (bv_unsigned b)); [| lia| unfold two64; lia| change (2 ^ (8 * 1 - 0)) with 256; lia].
    apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite (bv_wrap_small 64 (bv_unsigned b)) by (rewrite bv_modulus_64; unfold W64.two64; lia).
    apply bv_wrap_small. unfold bv_modulus. cbn. lia.
  - assert (w = 8%uint63) by (apply Uint63.to_Z_inj; rewrite W8; reflexivity). subst w. change (to_Z 8%uint63) with 8 in *.
    rewrite <- store_bytes_64. rewrite <- RT at 2. rewrite Len. change (Z.to_nat 8) with 8%nat. f_equal.
    rewrite Len in BD. change (8 * Z.of_nat (Z.to_nat 8)) with 64 in BD.
    rewrite ext_word_id64. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact BD.
Qed.

End MemLemmas.

Lemma w2Zs_wadd_small : forall a b, - two63 <= w2Zs a + w2Z b < two63 -> w2Zs (wadd a b) = w2Zs a + w2Z b.
Proof.
  intros a b H. rewrite (w2Zs_eq (wadd a b)), w2Z_wt, wadd_ok.
  rewrite (w2Zs_eq a), (w2Z_wt a) in H |- *.
  pose proof (w2Z_range a) as Ra. pose proof (w2Z_range b) as Rb. unfold two63, two64 in *.
  destruct (Z.leb_spec 9223372036854775808 (w2Z a));
  destruct (Z_lt_le_dec (w2Z a + w2Z b) 18446744073709551616);
  try (rewrite (Z.mod_small (w2Z a + w2Z b)) by lia; destruct (Z.leb_spec 9223372036854775808 (w2Z a + w2Z b)); lia);
  try (replace (w2Z a + w2Z b) with ((w2Z a + w2Z b - 18446744073709551616) + 1 * 18446744073709551616) by lia;
       rewrite Z.mod_add, Z.mod_small by lia;
       destruct (Z.leb_spec 9223372036854775808 (w2Z a + w2Z b - 18446744073709551616)); lia).
Qed.

Section Blk.
Context {rc : runConstT}.
Variable OPS : optable.

Lemma load8_bytes : forall E st ms mo k rg key v, st_ok bsegs OPS E st ms mo ->
  IMap.find k (s_regs st) = Some rg -> can_read bsegs (s_facts st) (s_priv st) k rg key 8%uint63 = true ->
  region_load bsegs k rg key 8%uint63 false = Some v ->
  AM.bytes_at bsegs (ms_mem ms) (addrZ E k key) (AM.le8 (den E v))
  /\ (PrimInt63.eqb k 0%uint63 = false -> loZ rg <= keyZ key /\ keyZ key + 8 <= hiZ E rg).
Proof.
  intros E st ms mo k rg key v HS FR CR RL.
  pose proof (so_reg _ _ _ _ _ _ HS _ _ FR) as RO.
  destruct (MemP.can_read_sound bsegs (s_priv st) E (ms_mem ms) (s_facts st) k rg key 8%uint63
              (so_facts _ _ _ _ _ _ HS) (so_zero _ _ _ _ _ _ HS) RO ltac:(right; right; right; reflexivity) CR) as (LO & HI & _ & INR & _).
  change (to_Z 8%uint63) with 8 in HI, INR.
  destruct (MemP.region_load_sound bsegs (s_priv st) E (ms_mem ms) (s_facts st) k rg key 8%uint63 false v
              (so_facts _ _ _ _ _ _ HS) (so_zero _ _ _ _ _ _ HS) RO ltac:(right; right; right; reflexivity) CR RL) as (bs & LEN & OV & DEN).
  change (Z.to_nat (to_Z 8%uint63)) with 8%nat in LEN, OV.
  destruct (ov_read_bytes_inv bsegs (ms_mem ms) _ 8 bs OV LO ltac:(change (Z.of_nat 8) with 8; exact HI)) as [_ RB].
  assert (EBS : bs = AM.le8 (den E v)).
  { rewrite <- (stored_is_loaded 8%uint63 (den E v) bs ltac:(right; reflexivity) LEN).
    - rewrite <- StepM.store_bytes_64. apply AS.store_bytes_8'.
    - rewrite DEN. apply StepM.bytes_val_ext_word; [exact LEN| change (to_Z 8%uint63) with 8; lia]. }
  split.
  - rewrite <- EBS. split; [exact LO|]. split; [rewrite LEN; unfold two64 in HI; lia|]. intros i Hi. rewrite LEN in Hi.
    change (AM.mrd bsegs (ms_mem ms) (AM.wa (addrZ E k key + Z.of_nat i))) with (rb bsegs (ms_mem ms) (addrZ E k key + Z.of_nat i)).
    rewrite (RB (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
  - intros KZ. pose proof (INR KZ 0 ltac:(lia)) as I0. pose proof (INR KZ 7 ltac:(lia)) as I7. lia.
Qed.

Lemma arg_block : forall E st ms mo k rg off o0 o8, st_ok bsegs OPS E st ms mo ->
  IMap.find k (s_regs st) = Some rg -> PrimInt63.eqb k 0%uint63 = false ->
  okey off = Some o0 -> okey (wadd off (wlit 8%uint63)) = Some o8 ->
  can_read bsegs (s_facts st) (s_priv st) k rg o0 8%uint63 = true -> can_read bsegs (s_facts st) (s_priv st) k rg o8 8%uint63 = true ->
  region_load bsegs k rg o0 8%uint63 false = Some (VL wone) -> region_load bsegs k rg o8 8%uint63 false = Some (VL wzero) ->
  let A := addrZ E k o0 in
  AS.ro_cells bsegs (ms_mem ms) A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)]
  /\ den E (VP k off) = Z_to_bv 64 A /\ 0 <= A /\ A + 16 <= bv_unsigned (ev E k) + hiZ E rg /\ keyZ o0 = w2Zs off.
Proof.
  intros E st ms mo k rg off o0 o8 HS FR KZ K0 K8 CR0 CR8 RL0 RL8 A.
  destruct (load8_bytes E st ms mo k rg o0 _ HS FR CR0 RL0) as [B0 IN0]. destruct (load8_bytes E st ms mo k rg o8 _ HS FR CR8 RL8) as [B8 IN8].
  specialize (IN0 KZ). specialize (IN8 KZ).
  destruct (okey_sound _ _ K0) as [E0 R0]. destruct (okey_sound _ _ K8) as [E8 R8].
  assert (E80 : keyZ o8 = keyZ o0 + 8).
  { rewrite E8, E0. rewrite w2Zs_wadd_small; [rewrite wlit_ok; reflexivity|]. rewrite wlit_ok. change (to_Z 8%uint63) with 8.
    rewrite <- E0. unfold two63 in *. lia. }
  assert (A8 : addrZ E k o8 = A + 8) by (unfold A, addrZ; lia).
  pose proof (AM.bytes_at_bound bsegs _ _ _ B0) as BB0. rewrite AM.length_le8 in BB0.
  split; [| split; [| split; [lia| split; [unfold A, addrZ; lia| exact E0]]]].
  - split; [cbn; auto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (proj2 (AM.bytes_at_app bsegs _ _ _ _)).
    rewrite AM.length_le8. change (Z.of_nat 8) with 8. rewrite <- A8.
    replace (Z_to_bv 64 1) with (den E (VL wone)) by (cbn [den]; apply bv_eq; reflexivity).
    replace (Z_to_bv 64 0) with (den E (VL wzero)) by (cbn [den]; apply bv_eq; reflexivity).
    split; [exact B0| exact B8].
  - apply bv_eq. rewrite den_VP, <- E0. rewrite Z_to_bv_unsigned. unfold A, addrZ in *. rewrite Z.mod_small by (unfold two64; lia).
    symmetry. apply bv_wrap_small. rewrite bv_modulus_64. unfold W64.two64. lia.
Qed.
End Blk.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Hypothesis IMGSH_aci : forall v a, In v Op.TwinB.SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.TwinB.cov1 HEAP_ID args z.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Variable ENTRY : Z.
Hypothesis WALK : tls_walk_stmt AI ENTRY.
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Definition acct_leaf_silent (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ op_minv OPS mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa mo'.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent mo aw L st LBa).

Theorem tls_get_addr_sound : forall pc, to_Z pc = ENTRY -> contract_sound bsegs OPS MP PB (ActrB.TwinB.ActrB.tls_get_addr_c bsegs pc ActrA.ATPi TLSW).
Proof.
  intros pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc ActrB.TwinB.ActrB.tls_get_addr_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = ENTRY) by (rewrite Hspc; exact Hpc).
  destruct (tls_apply_shape TLSW st sts Happ) as (r & hargs & k & off & rg & o0 & o8 & offs & st1 & PREB & HX10 & FR & K0 & K8 & CR0 & CR8 & RL0 & RL8 & HX2 & WL & FS0 & ESTS).
  destruct (acall_pre_bridgeB 4096%uint63 st r hargs st1 PREB FS0) as [wnl PRE].
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng 4096%uint63 None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  set (R := ms_regs ms) in *. set (spw := AP.getr R 2) in *. set (sp := bv_unsigned spw) in *.
  pose proof atop_range as ATR.
  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs' & rss & ksp & nn & md & Aa & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (Wt & WOF & ARW & TI)).
  destruct (CallA.TwinB.sp_region_inv st ks offs' rss SPR) as (HX2' & Hrs & KSZ & _).
  rewrite HX2 in HX2'. injection HX2' as <- <-. rewrite FR in Hrs. injection Hrs as <-.

  destruct (arg_block OPS E st ms mo k rg off o0 o8 HS FR KSZ K0 K8 CR0 CR8 RL0 RL8) as (BLK & DA & A0 & AHI & EK0).
  set (A := addrZ E k o0) in *.
  assert (KN0 : k <> 0%uint63) by (intros ->; discriminate KSZ).
  assert (TOPk : bv_unsigned (ev E k) + hiZ E rg <= 2 ^ 47).
  { destruct (CallA.TwinB.aregion_just_sound bsegs OPS E st ms mo wnl k offs rg k rg HS SPR AJ FR KN0) as [[_ T]|[NE _]]; [exact T| exfalso; apply NE; reflexivity]. }
  assert (SPA : sp <= A).
  { destruct (okey_sound _ _ Hksp) as [Eksp _]. rewrite wlts_w2Zs in WL. apply Z.ltb_ge in WL.
    unfold sp, spw. fold R in SPE. rewrite SPE. unfold A, addrZ. rewrite EK0, Eksp. lia. }
  assert (GA0 : AP.getr R 10 = Z_to_bv 64 A).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X10, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), HX10. exact DA. }
  change (to_Z 4096%uint63) with 4096 in LOR.
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  assert (RNGA : rng RNG A 16) by (eapply rng_sub'; [exact (ACCT_rng _ _ _ _ _ _ AC)| fold sp in LOR, BOT; lia]).
  pose proof (WALK L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (AP.getr R 10) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31)
                (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) sta LBa (CtrPre.TwinB.sp_lo E st) A AH MI ST BOT
                ltac:(unfold TP.TLSGA_STACK; fold spw; fold sp; fold spw in LOR; fold sp in LOR; lia) TP GA0 SPA BLK RSTK RNGA) as EV.
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ tls_postA AI L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
               (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) sta LBa (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV'' & STK' & MU & WM & PRES & AH').
    fold spw in PRES, STK'. fold sp in PRES, STK'.
    match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
    set (m := ms_mem ms) in *.
    set (Fv := CtrFree.TwinB.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
    destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
    assert (EMS' : ms' = CtrFrame.TwinB.ms' ms r R' m').
    { rewrite EMS. unfold CtrFrame.TwinB.ms'. f_equal. fold R. rewrite RA. apply MState.ret_pc_even.
      - lia.
      - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EV0.
        pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
        change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV0 in LM. change (to_Z 0%uint63) with 0 in LM.
        change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
    destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0' & OP & PV & NXc).
    destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
    assert (SHAPE : sts = [SS r (rf_set (s_rf (clobber st1)) X10 (VL TLSW)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st)
                              (s_ops st) (s_priv st) (s_next (clobber st1))]).
    { rewrite ESTS. apply (f_equal (fun x : sstate => [x])).
      assert (G : forall (S : sstate) v, setpc (setr S X10 v) r
                  = SS r (rf_set (s_rf S) X10 v) (s_ff S) (s_resv S) (s_regs S) (s_facts S) (s_ops S) (s_priv S) (s_next S)) by (intros [] ?; reflexivity).
      rewrite G, FF, RV, RG, FS0', OP, PV, FF1, RV1, FS1, OP1, PV1. reflexivity. }
    apply (HK _ ltac:(rewrite SHAPE; left; reflexivity) (CtrFrame.TwinB.E' E st Fv Gv) ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
    rewrite EMS'.
    assert (RAWV : forall a, m' (AM.wa a) = m (AM.wa a) -> rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true)).
    { intros a EQ. split; [unfold rb; unfold AM.wa in EQ; rewrite EQ; reflexivity|].
      intros Wb. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in Wb. rewrite (wview_ext1 m' m _ EQ). exact Wb. }
    assert (TWP : twins_pres LBa m m').
    { apply (Op.TwinB.twins_pres_band AI L RNG sta LBa m m' AH). intros a Ha.
      assert (SA : shad ATOP = ASHOFF + ATOP / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SA in Ha. unfold ASHOFF in Ha.
      assert (RA0 : 0 <= a < 2 ^ 64) by (clear - Ha ATR; Z.div_mod_to_equations; lia).
      apply (MU (AM.wa a)). unfold AM.wa. rewrite Z_to_bv_small by (unfold bv_modulus; exact RA0).
      cbn [outside]. split; [| exact I]. unfold TP.TLSGA_STACK. fold sp in LOR, BOT. intros [Q1 Q2]. fold spw in Q1, Q2. fold sp in Q1, Q2. clear - Ha ATR LOR BOT Q1 Q2. Z.div_mod_to_equations. lia. }
    assert (STB : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LB0 a ->
              m' (AM.wa a) = m (AM.wa a)).
    { intros LB0 (W0 & (E1 & E2 & E3 & E4) & ARW0) a Ha ST0. pose proof ARW0 as [HW0 _]. pose proof HW0 as (_ & HT0 & _).
      destruct (LB_classify AI ACCT UNIV AI_fake W0 aw LB0 m mo HW0) as (KU & KT).
      apply (aw_real_stable AI ACCT UNIV AI_fake aw LB0 m mo W0 RNG sta LBa m' LBa LB0 sp LBa TWP ltac:(intros b0 Hb0 _ _; rewrite <- E4; exact Hb0) ARW0).
      - rewrite E1. exact AH'.
      - exact PRES.
      - intros v Hv UB P. destruct (KU v Hv UB P) as (b & Vb & ->). exists b. split; [rewrite <- E4; exact (proj1 Vb)| reflexivity].
      - intros v Hv NUB. destruct (KT v Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
        + left. exists b. destruct (HT0 b Hb) as [HbL HH0]. split; [exact HbL|]. split; [rewrite <- E4; exact HbL|]. split; [exact HH0| reflexivity].
        + right. exists b. split; [exact (proj1 (proj1 Vb))|]. split; [rewrite <- E4; exact (proj1 (proj1 Vb))|]. split; [exact (proj2 Vb)| reflexivity].
      - exact Ha.
      - exact ST0. }
    apply (CtrNoDelta.TwinB.nodelta_st_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
             OPS_cov0_img E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG sta _ _ HS CP FS CF).
    --
      intros rg0 Hrg. unfold CtrFrame.TwinB.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
    -- intros x i Hx. exact (CtrFree.TwinB.cfvF_clob R' x i Hx).
    --   cbn [den]. apply bv_eq. reflexivity.
    -- exact MINV''.
    -- exact STK'.
    --   intros LB0 AR0 a Ha STa. apply RAWV. exact (STB LB0 AR0 a Ha STa).
    --   intros LB0 AR0 a Ha IU. apply (STB LB0 AR0 a Ha). right; right. exact IU.
    --
      intros o a Ho NI Ha FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
      destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STKZ & ->)]].
      + pose proof (proj1 (PRES a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact INA))) as E0. unfold AM.wa in E0. exact E0.
      + pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [right; left; exact INA| reflexivity]))) as E0.
        unfold AM.wa in E0. exact E0.
      +
        pose proof (proj1 (PRES (shad a') ltac:(unfold two64 in Ha; lia) ltac:(right; right; right; exists a'; split; [left; exact STKZ| reflexivity]))) as E0.
        unfold AM.wa in E0. exact E0.
    --   exact (CtrFrame.TwinB.WBM_of_pres AI LBa sp m m' PRES).
    --
      intros a Ha SC IB. apply RAWV.
      assert (CA : aclient_addr (aci AI) LBa sp a).
      { destruct SC as [(a' & RRa & ->)|(vv & Hv & RRa)].
        - right; right; right. exists a'. split; [left; exact RRa| reflexivity].
        - destruct (IMGSH_aci vv a Hv RRa) as (a' & INA & ->). right; right; right. exists a'. split; [right; left; exact INA| reflexivity]. }
      exact (proj1 (PRES a Ha CA)).
    -- exact AH'.
    -- exact ACP.
    --
      intros b x Hb FK Hx. pose proof (Op.TwinB.blk_band AI AI_fake L RNG sta LBa m b x AH Hb Hx) as BB.
      exact (proj1 (PRES x ltac:(unfold AIMG_HI, KLS in BB; lia) ltac:(right; right; left; exists b; split; [exact Hb| exact Hx]))).
    -- exact TWP.
    -- exact OTH.
    -- exact HMI'.
    -- exact (fun P => P).
Qed.
End Sound.

Section Inst.
Context {rc : runConstT}.
Lemma AIu_tls_walk : tls_walk_stmt AIu2 F_tlsga.TwinB.F_tlsga.ATLSGA_ICPT.
Proof.
  unfold tls_walk_stmt. intros until A. intros AH MI ST BOT LO TPE A0 ABV BLK RSTK RA.
  exact (AInstanceU2F.TwinB.AHU2_tlsga L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           FR fc m st LB lo A AH MI ST BOT LO TPE A0 ABV BLK RSTK RA).
Qed.
End Inst.
End TwinB.
