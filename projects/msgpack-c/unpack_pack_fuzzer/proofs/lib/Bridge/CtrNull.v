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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CtrPre GlueA CtrFrame CtrNoDelta.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import StepSoundMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Lemma errno_havoc_inv : forall st2 stE, errno_havoc st2 = Some stE ->
  exists r0, IMap.find 0%uint63 (s_regs st2) = Some r0 /\ in_priv_b (s_priv st2) AERRNOi 4%uint63 = false
    /\ stE = SS (s_pc st2) (s_rf st2) (s_ff st2) (resv_after_store (s_facts st2) (s_resv st2) (VL (wlit AERRNOi)))
                (IMap.add 0%uint63 (Mem.region_store r0 AERRNOi 4%uint63 (VP (s_next st2) wzero)) (s_regs st2))
                (s_facts st2) (s_ops st2) (s_priv st2) (PrimInt63.add (s_next st2) 1%uint63).
Proof.
  intros st2 stE H. unfold errno_havoc in H. destruct (IMap.find 0%uint63 (s_regs st2)) as [r0|]; [|discriminate].
  destruct (in_priv_b (s_priv st2) AERRNOi 4%uint63) eqn:Q; [discriminate|].
  unfold fresh, set_next in H. cbn [fst snd s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in H. injection H as <-.
  exists r0. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma null_post_inv : forall hargs cred st2 r stN, null_post hargs cred st2 r = Some stN ->
  exists stE hN, errno_havoc (setr st2 X10 (VL wzero)) = Some stE /\ heap_set_A hargs (sv_alu ALU_SUB cred (VL C_EXHw)) = Some hN
    /\ stN = setpc (set_ops stE (set_op HEAP_ID hN (s_ops stE))) r.
Proof.
  intros hargs cred st2 r stN H. unfold null_post in H.
  destruct (errno_havoc (setr st2 X10 (VL wzero))) as [stE|]; [| discriminate H].
  destruct (heap_set_A hargs (sv_alu ALU_SUB cred (VL C_EXHw))) as [hN|]; [| discriminate H].
  exists stE, hN. split; [reflexivity|]. split; [reflexivity|]. injection H as <-. reflexivity.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> ALib.Mem.le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold ALib.Mem.le4, le_bytes_to_word.
  pose proof (AP.bytes_le_to_Z_bound bs) as HR. pose proof (AP.bytes_le_to_Z_nonneg bs) as H0. rewrite HL in HR.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z in HR.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia). rewrite <- HL. apply Shadow.Z_to_le_bytes_to_Z.
Qed.
Section ErrnoCells.
Context {rc : runConstT}.

Lemma ties_ext_p : forall W W' ws, w_T W' = w_T W -> (forall b, visf W' b <-> visf W b) -> w_zc W' = w_zc W -> ties W ws ->
  (forall b, is_heap b -> vis W' b -> vis W b) -> (In prist_win ws -> aprist (w_st W')) -> ties W' ws.
Proof.
  intros W W' ws ET EV EZ (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) HV PS. unfold ties. rewrite ET, EZ.
  split; [exact T1|]. split; [exact T2|]. split; [intros b Hb; apply T3; apply EV; exact Hb|].
  split; [intros w Hw K; destruct (T4 w Hw K) as (b & Vb & E); exists b; split; [apply EV; exact Vb| exact E]|].
  split; [intros w Hw K; destruct (T5 w Hw K) as (b & Vb & E); exists b; split; [apply EV; exact Vb| exact E]|].
  split; [exact T6| split; [exact T7| split; [exact T8|]]].
  split; [intros b Vb HH CC; exact (C24 b (HV b HH Vb) HH CC)| split; [exact GA| exact PS]].
Qed.

Lemma rw_cells_of_rb0 : forall (m : amem) A cs,
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
Lemma errno_cells : forall m : amem, exists e0 : word, ALib.Step.rw_cells asegs m AERRNO [C4 e0].
Proof.
  intros m.
  assert (AW : Mem.abs_writable asegs AERRNO 4 = true) by (vm_compute; reflexivity).
  assert (EA : 0 <= AERRNO) by (unfold AERRNO, ATP; lia).
  destruct (MemP.abs_writable_sound asegs AERRNO 4 EA ltac:(lia) AW) as [AR BY].
  destruct (MemP.abs_readable_sound asegs AERRNO 4 ltac:(lia) AR) as [_ RD].
  assert (B : forall i, 0 <= i < 4 -> exists b, rb asegs m (AERRNO + i) = Some b).
  { intros i Hi. rewrite (GlueA.rb_mrdA asegs). unfold ALib.Mem.mrd. destruct (m (ALib.Mem.wa (AERRNO + i))) as [b|]; [exists b; reflexivity|].
    destruct (RD i Hi) as (b & rest & MR). exists b. unfold seg_rom, ALib.Mem.wa. rewrite MR. reflexivity. }
  destruct (B 0 ltac:(lia)) as [b0 H0]. destruct (B 1 ltac:(lia)) as [b1 H1]. destruct (B 2 ltac:(lia)) as [b2 H2]. destruct (B 3 ltac:(lia)) as [b3 H3].
  exists (le_bytes_to_word [b0; b1; b2; b3]). apply rw_cells_of_rb0.
  - split; exact I.
  - exact EA.
  - cbn [cells_size csize Nat.add]. unfold AERRNO, ATP. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite (le4_of_bytes [b0; b1; b2; b3] eq_refl).
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|i]]]]; [rewrite Z.add_0_r; exact H0| exact H1| exact H2| exact H3| lia].
  - cbn [cells_size csize Nat.add]. intros i Hi. exact (proj1 (BY i Hi) m).
Qed.
End ErrnoCells.

Section Null.
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
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.

Definition acallN (E : env) (st : sstate) (ms : machine_state) (mo : Model) (r : int) (hargs : list sv) (wnl : list (int * sv * w64))
    (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) : Prop :=
  exists (LB : blocks) (ks : int) (offs : w64) (rss : region) (ksp : int) (nn : nat) (md : w64) (A : sv) (nw : w64) (rest : list sv),
    sp_region st = Some (ks, offs, rss) /\ okey offs = Some ksp
    /\ bv_unsigned (AP.getr (ms_regs ms) 2%bv) = bv_unsigned (ev E ks) + keyZ ksp
    /\ keyZ ksp mod 16 = 0 /\ loZ rss <= keyZ ksp /\ ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss
    /\ find_op HEAP_ID (s_ops st) = Some hargs /\ CtrA.count_op HEAP_ID (s_ops st) = 1%nat
    /\ hargs = VL md :: A :: VL nw :: rest /\ wt nw = false /\ nn = Z.to_nat (to_Z (wl nw)) /\ (3 * nn <= length rest)%nat /\ (nn <= 255)%nat
    /\ CtrA.nonstack_windows nn rest = Some wnl /\ aregions_justified st wnl = true
    /\ windows_wf (wins_of E nn rest) LB (ATOP + 4096)
    /\ cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) (ms_mem ms)
    /\ aw = den E A
    /\ exists W, wit_of W L RNG sta LBa /\ aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W /\ ties W (wins_of E nn rest).
Lemma acallN_of_G : forall E st ms mo r hargs wnl L RNG sta LBa aw,
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> acallN E st ms mo r hargs wnl L RNG sta LBa aw.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13
     & H14 & _ & H16 & _ & H18 & H19 & H20 & H21).
  exists LB, ks, offs, rss, ksp, nn, md, A, nw, rest. repeat (split; [assumption|]). assumption.
Qed.
Lemma acallN_of_facts : forall XN E st ms mo L RNG sta LBa aw n,
  CtrPre.acall_facts AI ACCT UNIV Cw XN E st ms mo L RNG sta LBa aw n ->
  exists r hargs wnl st1, call_pre st = Some r /\ forget_stack_below_sp_g st = Some st1 /\ acallN E st ms mo r hargs wnl L RNG sta LBa aw.
Proof.
  intros XN E st ms mo L RNG sta LBa aw n (LB & r & hargs & st1 & ks & offs & rss & ksp & wnl & nn & md & A & nw & rest & CP & FS & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9
     & H10 & H11 & H12 & H13 & H14 & H16 & H18 & H19 & H20 & H21 & _).
  exists r, hargs, wnl, st1. split; [exact CP|]. split; [exact FS|].
  exists LB, ks, offs, rss, ksp, nn, md, A, nw, rest. repeat (split; [assumption|]). assumption.
Qed.

Theorem nodelta_cred_st_ok : forall E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' (v : sv) (nx' : int) (credN : sv) (hN : list sv) (aw' : word),
  st_ok asegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  acallN E st ms mo r hargs wnl L RNG sta LBa aw ->

  heap_set_A hargs credN = Some hN -> den (CtrFrame.E' E st Fv Gv) credN = aw' ->

  (forall rg, In rg CtrFrame.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg) ->
  (forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x)) ->
  den (CtrFrame.E' E st Fv Gv) v = AP.getr R' 10%bv ->

  ALib.Mem.mem_inv asegs m' ->
  stk asegs m' (CtrPre.sp_lo E st) (bv_unsigned (AP.getr (ms_regs ms) 2%bv)) ->

  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LB a ->
     rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true)) ->
  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB a ->
     m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)) ->
  (forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
     Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den (CtrFrame.E' E st Fv Gv)) (op_args o))) ->
     m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
     wb asegs (ms_mem ms) a = true -> wb asegs m' a = true) ->

  (forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
     rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true)) ->

  AHEAP AI L RNG' sta' LBa m' -> ACCT aw' L RNG' sta' LBa mo' ->
  (forall b x, In b LBa -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (ALib.Mem.wa x) = ms_mem ms (ALib.Mem.wa x)) ->
  twins_pres LBa (ms_mem ms) m' ->
  OTHER mo mo' -> op_minv OPS mo' ->
  (CtrPre.prist_in E st -> aprist sta -> aprist sta') ->
  st_ok asegs OPS (CtrFrame.E' E st Fv Gv)
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (set_op HEAP_ID hN (s_ops st)) (s_priv st) nx')
    (CtrFrame.ms' ms r R' m') mo'.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' v nx' credN hN aw' HS CP FS CF HSA DCN KEPT HF DV MINV' STK' SBVall SBUall SBO WBM SBT AH' AC' KEEPW TWP OTH MINVo PSN.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AJ & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & _).
  pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW) as AWH.
  assert (AR : aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa) by (exists W; split; [exact WOF| exact ARW]).
  pose proof (SBVall LB AR) as SBV. pose proof (SBUall LB AR) as SBU.
  set (W' := mkWit (w_L W) RNG' sta' (w_LBa W) (w_T W) (w_FA W) m' (w_zc W)).
  assert (AR' : aw_realW AI ACCT UNIV aw' LB m' mo' W').
  { destruct WOF as (E1 & E2 & E3 & E4). pose proof ARW as [(_ & _ & _ & HFA & _) _].
    apply (aw_real_nodelta AI ACCT UNIV AI_fake aw aw' LB (ms_mem ms) mo W RNG' sta' m' mo' ARW); [rewrite E1, E4; exact AH'| rewrite E1, E4; exact AC'| | rewrite E4; exact TWP].
    intros b x Hb FK Hx. apply (KEEPW b x); [rewrite <- E4; exact Hb| exact FK| exact Hx]. }
  assert (TI' : ties W' (wins_of E nn rest)).
  { apply (ties_ext_p W W'); [reflexivity| intros b; reflexivity| reflexivity| exact TI| intros b _ V; exact V|]. intros IP. subst W'. cbn [w_st].
    destruct WOF as (_ & _ & E3 & _). apply PSN; [| rewrite <- E3; exact (ties_prist W _ TI IP)]. exists hargs, md, A, nw, rest. split; [exact Hf|]. split; [exact Eh|]. rewrite <- Nn. exact IP. }
  pose proof STK' as STK2.

  assert (WINK : forall k0 len kd, True -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
            forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LB a).
  { intros k0 len kd _ WL a Ha.
    destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k0 len kd NW (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
    pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
    - exfalso. exact (KD KS0).
    - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
    - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }

  assert (EhN : hN = VL md :: credN :: VL nw :: rest) by (rewrite Eh in HSA; cbn [heap_set_A] in HSA; injection HSA as <-; reflexivity).
  assert (DECN : decode (map (den (CtrFrame.E' E st Fv Gv)) hN) = Some (w2Z md, aw', wins_of E nn rest, map (den E) (skipn (3 * nn) rest))).
  { pose proof (CtrFrame.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln) as D0. rewrite Eh in D0.
    rewrite (decode_hargs (CtrFrame.E' E st Fv Gv) md A nw rest nn Tnw Nn Ln) in D0.
    assert (DW : wins_of (CtrFrame.E' E st Fv Gv) nn rest = wins_of E nn rest) by congruence.
    assert (DR : map (den (CtrFrame.E' E st Fv Gv)) (skipn (3 * nn) rest) = map (den E) (skipn (3 * nn) rest)) by congruence.
    rewrite EhN, (decode_hargs (CtrFrame.E' E st Fv Gv) md credN nw rest nn Tnw Nn Ln), DW, DR, DCN. reflexivity. }
  assert (HOLDN : op_holds OPS HEAP_ID (map (den (CtrFrame.E' E st Fv Gv)) hN) m' mo').
  { rewrite OPS_holds1. exists (w2Z md), aw', (wins_of E nn rest), (map (den E) (skipn (3 * nn) rest)), LB, W'.
    split; [exact DECN|]. split; [exact (proj1 AR')|]. split; [exact WF|]. split; [| exact TI'].
    apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U _. symmetry. unfold ALib.Mem.wa in SBU.
    apply (SBU a ltac:(unfold two64 in Ha; lia)). exact U. }
  replace (s_regs st1) with (CtrFrame.RgPg st ks rss ksp [] []).
  2:{ unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. reflexivity. }
  apply (CtrFrame.frame_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo' KEPT HF aw LB LB AWH MINV' SBV SBO WBM SBT ks offs rss ksp SPR SPE wnl nn rest AJ WF (fun _ => True) WINK ltac:(intros; exact I) ltac:(intros; exact I)
           K16 LOSP STK2 FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln OTH [] [] (NoDup_nil _)
           ltac:(intros k1 r1 X; destruct X) ltac:(intros k0 _; exact I) (fun _ => False) ltac:(intros k1 r1 X; destruct X) ltac:(intros k1 r1 a1 X; destruct X)
           ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros k1 r1 k2 r2 a1 X; destruct X)
           hN (w2Z md) aw' (wins_of E nn rest) (map (den E) (skipn (3 * nn) rest)) DECN HOLDN).
  - intros a X. destruct X.
  - intros a Ha NIX NWS. left. exact NWS.
  - intros a _ X. exact X.
  - exact (so_facts _ _ _ _ _ _ (CtrFrame.HS' OPS E st ms mo HS FOK Fv Gv)).
  - exact DV.
  - exact MINVo.
Qed.

Lemma nodelta_heap_holds : forall E st ms mo r hargs wnl L RNG sta LBa aw Fv Gv m' mo' RNG' sta' (credN : sv) (hN : list sv) (aw' : word),
  st_ok asegs OPS E st ms mo -> call_pre st = Some r ->
  acallN E st ms mo r hargs wnl L RNG sta LBa aw ->
  heap_set_A hargs credN = Some hN -> den (CtrFrame.E' E st Fv Gv) credN = aw' ->
  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB a ->
     m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)) ->
  AHEAP AI L RNG' sta' LBa m' -> ACCT aw' L RNG' sta' LBa mo' ->
  (forall b x, In b LBa -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (ALib.Mem.wa x) = ms_mem ms (ALib.Mem.wa x)) ->
  twins_pres LBa (ms_mem ms) m' ->
  (CtrPre.prist_in E st -> aprist sta -> aprist sta') ->
  find_op HEAP_ID (s_ops st) = Some hargs /\ CtrA.count_op HEAP_ID (s_ops st) = 1%nat
  /\ op_holds OPS HEAP_ID (map (den (CtrFrame.E' E st Fv Gv)) hN) m' mo'.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw Fv Gv m' mo' RNG' sta' credN hN aw' HS CP CF HSA DCN SBUall AH' AC' KEEPW TWP PSN.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AJ & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & _).
  assert (AR : aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa) by (exists W; split; [exact WOF| exact ARW]).
  pose proof (SBUall LB AR) as SBU.
  set (W' := mkWit (w_L W) RNG' sta' (w_LBa W) (w_T W) (w_FA W) m' (w_zc W)).
  assert (AR' : aw_realW AI ACCT UNIV aw' LB m' mo' W').
  { destruct WOF as (E1 & E2 & E3 & E4). pose proof ARW as [(_ & _ & _ & HFA & _) _].
    apply (aw_real_nodelta AI ACCT UNIV AI_fake aw aw' LB (ms_mem ms) mo W RNG' sta' m' mo' ARW); [rewrite E1, E4; exact AH'| rewrite E1, E4; exact AC'| | rewrite E4; exact TWP].
    intros b x Hb FK Hx. apply (KEEPW b x); [rewrite <- E4; exact Hb| exact FK| exact Hx]. }
  assert (TI' : ties W' (wins_of E nn rest)).
  { apply (ties_ext_p W W'); [reflexivity| intros b; reflexivity| reflexivity| exact TI| intros b _ V; exact V|]. intros IP. subst W'. cbn [w_st].
    destruct WOF as (_ & _ & E3 & _). apply PSN; [| rewrite <- E3; exact (ties_prist W _ TI IP)]. exists hargs, md, A, nw, rest. split; [exact Hf|]. split; [exact Eh|]. rewrite <- Nn. exact IP. }
  assert (EhN : hN = VL md :: credN :: VL nw :: rest) by (rewrite Eh in HSA; cbn [heap_set_A] in HSA; injection HSA as <-; reflexivity).
  assert (DECN : decode (map (den (CtrFrame.E' E st Fv Gv)) hN) = Some (w2Z md, aw', wins_of E nn rest, map (den E) (skipn (3 * nn) rest))).
  { pose proof (CtrFrame.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln) as D0. rewrite Eh in D0.
    rewrite (decode_hargs (CtrFrame.E' E st Fv Gv) md A nw rest nn Tnw Nn Ln) in D0.
    assert (DW : wins_of (CtrFrame.E' E st Fv Gv) nn rest = wins_of E nn rest) by congruence.
    assert (DR : map (den (CtrFrame.E' E st Fv Gv)) (skipn (3 * nn) rest) = map (den E) (skipn (3 * nn) rest)) by congruence.
    rewrite EhN, (decode_hargs (CtrFrame.E' E st Fv Gv) md credN nw rest nn Tnw Nn Ln), DW, DR, DCN. reflexivity. }
  split; [exact Hf|]. split; [exact Hc|].
  rewrite OPS_holds1. exists (w2Z md), aw', (wins_of E nn rest), (map (den E) (skipn (3 * nn) rest)), LB, W'.
  split; [exact DECN|]. split; [exact (proj1 AR')|]. split; [exact WF|]. split; [| exact TI'].
  apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U _. symmetry. unfold ALib.Mem.wa in SBU.
  apply (SBU a ltac:(unfold two64 in Ha; lia)). exact U.
Qed.

Lemma errno_seg : forall a, AERRNO <= a < AERRNO + 4 -> exists seg, find_segment asegs a 1 = Some seg.
Proof.
  intros a Ha. rewrite AImg.a_find_segment_1 by (unfold AERRNO, ATP in Ha; lia). unfold AERRNO, ATP in Ha.
  replace (0x10000 <=? a) with true by (symmetry; apply Z.leb_le; lia). replace (a + 1 <=? 0x3b000) with false by (symmetry; apply Z.leb_gt; lia).
  replace (0x3b000 <=? a) with true by (symmetry; apply Z.leb_le; lia). replace (a + 1 <=? 0xcd000) with false by (symmetry; apply Z.leb_gt; lia).
  replace (0xcd000 <=? a) with true by (symmetry; apply Z.leb_le; lia). replace (a + 1 <=? 0xd3000) with false by (symmetry; apply Z.leb_gt; lia).
  replace (0xd3000 <=? a) with true by (symmetry; apply Z.leb_le; lia). replace (a + 1 <=? 0x62f000) with true by (symmetry; apply Z.leb_le; lia).
  cbn [andb]. eexists. reflexivity.
Qed.

Definition in_errno (x : Z) : Prop := AERRNO <= x < AERRNO + 4.
Definition in_errno_b (x : Z) : bool := (AERRNO <=? x) && (x <? AERRNO + 4).
Lemma in_errno_b_spec : forall x, in_errno_b x = true <-> in_errno x.
Proof. intros x. unfold in_errno_b, in_errno. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Definition mem_old_errno (m m' : amem) : amem := fun x => if in_errno_b (bv_unsigned x) then m x else m' x.

Lemma moe_in : forall m m' x, in_errno (bv_unsigned x) -> mem_old_errno m m' x = m x.
Proof. intros m m' x H. unfold mem_old_errno. rewrite (proj2 (in_errno_b_spec _) H). reflexivity. Qed.
Lemma moe_out : forall m m' x, ~ in_errno (bv_unsigned x) -> mem_old_errno m m' x = m' x.
Proof. intros m m' x H. unfold mem_old_errno. destruct (in_errno_b (bv_unsigned x)) eqn:Q; [exfalso; exact (H (proj1 (in_errno_b_spec _) Q))| reflexivity]. Qed.

Hypothesis AERRNO_client : forall LB SP, aclient_range (aci AI) LB SP AERRNO 4.

Theorem nodelta_errno_st_ok : forall E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' (v : sv)
    (credN : sv) (hN : list sv) (aw' : word) (e0 e' : word) (stE : sstate),
  st_ok asegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  acallN E st ms mo r hargs wnl L RNG sta LBa aw ->
  heap_set_A hargs credN = Some hN -> den (CtrFrame.E' E st Fv Gv) credN = aw' ->
  errno_havoc (setr (clobber st1) X10 v) = Some stE ->
  (forall rg, In rg CtrFrame.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg) ->
  (forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x)) ->
  den (CtrFrame.E' E st Fv Gv) v = AP.getr R' 10%bv ->
  Fv 15 = e' ->
  ALib.Step.rw_cells asegs (ms_mem ms) AERRNO [C4 e0] -> ALib.Step.rw_cells asegs m' AERRNO [C4 e'] ->
  ALib.Mem.mem_inv asegs m' ->
  stk asegs m' (CtrPre.sp_lo E st) (bv_unsigned (AP.getr (ms_regs ms) 2%bv)) -> ATOP + 4096 <= CtrPre.sp_lo E st ->

  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LB a -> ~ in_errno a ->
     rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true)) ->
  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB a ->
     m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)) ->
  (forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 -> ~ in_errno a ->
     Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den (CtrFrame.E' E st Fv Gv)) (op_args o))) ->
     m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
     wb asegs (ms_mem ms) a = true -> wb asegs m' a = true) ->
  (forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
     rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true)) ->
  AHEAP AI L RNG' sta' LBa m' -> ACCT aw' L RNG' sta' LBa mo' ->
  (forall b x, In b LBa -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (ALib.Mem.wa x) = ms_mem ms (ALib.Mem.wa x)) ->
  twins_pres LBa (ms_mem ms) m' ->
  OTHER mo mo' -> op_minv OPS mo' ->
  (CtrPre.prist_in E st -> aprist sta -> aprist sta') ->
  st_ok asegs OPS (CtrFrame.E' E st Fv Gv) (setpc (set_ops stE (set_op HEAP_ID hN (s_ops stE))) r) (CtrFrame.ms' ms r R' m') mo'.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' v credN hN aw' e0 e' stE
         HS CP FS CF HSA DCN HAV KEPT HF DV FV15 ERR0 ERR' MINV' STK' BOT SBVe SBU SBOe WBM SBT AH' AC' KEEPW TWP OTH MINVo PSN.
  set (Mv := mem_old_errno (ms_mem ms) m').
  set (E1 := CtrFrame.E' E st Fv Gv) in *.
  assert (ERNG : 0 <= AERRNO /\ AERRNO + 4 <= AIMG_HI /\ AIMG_HI < 2 ^ 47) by (unfold AERRNO, ATP, AIMG_HI; lia).
  assert (MvI : forall a, 0 <= a < 2 ^ 64 -> in_errno a -> Mv (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)).
  { intros a Ha IE. apply moe_in. unfold ALib.Mem.wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia). exact IE. }
  assert (MvO : forall a, 0 <= a < 2 ^ 64 -> ~ in_errno a -> Mv (ALib.Mem.wa a) = m' (ALib.Mem.wa a)).
  { intros a Ha IE. apply moe_out. unfold ALib.Mem.wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia). exact IE. }

  assert (RBi : forall a, 0 <= a < 2 ^ 64 -> in_errno a -> rb asegs Mv a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs Mv a = true)).
  { intros a Ha IE. unfold rb, wb, wview. change (Z_to_bv 64 a) with (ALib.Mem.wa a). rewrite (MvI a Ha IE). split; [reflexivity| exact (fun H => H)]. }
  assert (RBo : forall a, 0 <= a < 2 ^ 64 -> ~ in_errno a -> rb asegs Mv a = rb asegs m' a /\ (wb asegs m' a = true -> wb asegs Mv a = true)).
  { intros a Ha IE. unfold rb, wb, wview. change (Z_to_bv 64 a) with (ALib.Mem.wa a). rewrite (MvO a Ha IE). split; [reflexivity| exact (fun H => H)]. }
  assert (DEC_E : forall a, in_errno a \/ ~ in_errno a) by (intros a; unfold in_errno; lia).

  assert (SBVv : forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LB a ->
            rb asegs Mv a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs Mv a = true)).
  { intros LB AR a Ha SA. destruct (DEC_E a) as [IE|NE]; [exact (RBi a Ha IE)|].
    destruct (RBo a Ha NE) as [R1 W1]. destruct (SBVe LB AR a Ha SA NE) as [R2 W2]. split; [rewrite R1; exact R2| intros W; exact (W1 (W2 W))]. }
  assert (SBUv : forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB a ->
            Mv (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)).
  { intros LB AR a Ha IU. destruct (DEC_E a) as [IE|NE]; [exact (MvI a Ha IE)| rewrite (MvO a Ha NE); exact (SBU LB AR a Ha IU)]. }
  assert (SBOv : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
            Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E1) (op_args o))) -> Mv (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
  { intros o a Ho NI Ha FP. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold two64 in Ha; lia). change (Z_to_bv 64 a) with (ALib.Mem.wa a).
    destruct (DEC_E a) as [IE|NE]; [exact (MvI a Ha' IE)| rewrite (MvO a Ha' NE); exact (SBOe o a Ho NI Ha NE FP)]. }
  assert (WBMv : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
            wb asegs (ms_mem ms) a = true -> wb asegs Mv a = true).
  { intros a Ha C W. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold two64 in Ha; lia).
    destruct (DEC_E a) as [IE|NE]; [exact (proj2 (RBi a Ha' IE) W)| exact (proj2 (RBo a Ha' NE) (WBM a Ha C W))]. }
  assert (SBTv : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
            rb asegs Mv a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs Mv a = true)).
  { intros a Ha SC IB. destruct (DEC_E a) as [IE|NE]; [exact (RBi a Ha IE)|].
    destruct (RBo a Ha NE) as [R1 W1]. destruct (SBT a Ha SC IB) as [R2 W2]. split; [rewrite R1; exact R2| intros W; exact (W1 (W2 W))]. }
  assert (KEEPWv : forall b x, In b LBa -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> Mv (ALib.Mem.wa x) = ms_mem ms (ALib.Mem.wa x)).
  { intros b x Hb FK Hx. destruct (AI_block_bounds AI _ _ _ _ _ b AH' Hb) as (B1 & B2 & B3). assert (Hx' : 0 <= x < 2 ^ 64) by (atop_facts; lia).
    rewrite (MvO x Hx') by (unfold in_errno; lia). exact (KEEPW b x Hb FK Hx). }
  assert (TWPv : twins_pres LBa (ms_mem ms) Mv).
  { intros p A n Hin PR i Hi. destruct (AI_block_bounds AI _ _ _ _ _ (HB p A n) AH' Hin) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
    assert (SH : AIMG_HI <= shad A + i < 2 ^ 64).
    { unfold shad, ASHOFF. unfold shlen in Hi. rewrite Z.shiftr_div_pow2 in Hi by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8 in *. atop_facts. unfold AIMG_HI in *.
      assert (0 <= A / 8 <= A) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). assert ((n + 7) / 8 <= n + 7) by (apply Z.div_le_upper_bound; lia). lia. }
    rewrite (MvO (shad A + i)) by (unfold in_errno; lia). exact (TWP p A n Hin PR i Hi). }
  assert (MINVv : ALib.Mem.mem_inv asegs Mv).
  { intros a b H. unfold Mv, mem_old_errno in H. destruct (in_errno_b (bv_unsigned a)); [| exact (MINV' a b H)].
    unfold ALib.Mem.ro_addr. destruct (find_segment asegs (bv_unsigned a) 1) as [seg|] eqn:FSG; [| reflexivity].
    rewrite (so_minv _ _ _ _ _ _ HS a b H seg FSG). reflexivity. }
  assert (STKv : stk asegs Mv (CtrPre.sp_lo E st) (bv_unsigned (AP.getr (ms_regs ms) 2%bv))).
  { destruct STK' as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha.
    assert (Ha' : 0 <= a < 2 ^ 64) by lia. assert (NE : ~ in_errno a) by (unfold in_errno; atop_facts; unfold AIMG_HI in *; lia).
    destruct (S3 a Ha) as [W1 R1]. unfold wview, ALib.Mem.mrd in *. rewrite (MvO a Ha' NE). split; [exact W1| exact R1]. }
  assert (AHv : AHEAP AI L RNG' sta' LBa Mv).
  { apply (AI_frame AI L RNG' sta' LBa m' Mv [(AERRNO, AERRNO + 4)] AH').
    - intros x [OUT _]. apply moe_out. exact OUT.
    - intros x WV. destruct (DEC_E (bv_unsigned x)) as [IE|NE]; [| unfold Mv; unfold wview in *; rewrite (moe_out _ _ x NE); exact WV].
      destruct ERR0 as [_ (_ & _ & WR)]. pose proof (WR (bv_unsigned x - AERRNO) ltac:(unfold in_errno in IE; cbn [cells_size csize Nat.add]; lia)) as WX.
      replace (ALib.Mem.wa (AERRNO + (bv_unsigned x - AERRNO))) with x in WX by (unfold ALib.Mem.wa; replace (AERRNO + (bv_unsigned x - AERRNO)) with (bv_unsigned x) by lia; rewrite Z_to_bv_bv_unsigned; reflexivity).
      unfold Mv; unfold wview in *. rewrite (moe_in _ _ x IE). exact WX.
    - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (AERRNO + 4 - AERRNO) with 4 by lia. exact (AERRNO_client LBa (ATOP + 4096)). }

  set (nxE := PrimInt63.add (s_next (clobber st1)) 1%uint63).
  pose proof (nodelta_cred_st_ok E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' Mv mo' RNG' sta' v nxE credN hN aw'
                HS CP FS CF HSA DCN KEPT HF DV MINVv STKv SBVv SBUv SBOv WBMv SBTv AHv AC' KEEPWv TWPv OTH MINVo PSN) as HS1.
  fold E1 in HS1.

  destruct (errno_havoc_inv _ _ HAV) as (r0 & F0 & NPV & EQE).
  destruct (clobber_fields st1) as (Cpc & Cff & Crv & CR & Cfs & Cos & Cpv & Cnx).
  destruct (CtrFrame.st1_fields st st1 FS) as (Spc & Srf & Sff & Srv & Sfs & Sos & Spv & Snx).
  cbn [setr s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in F0, NPV, EQE.
  rewrite CR in F0. rewrite Cpv, Spv in NPV.
  pose proof (HeapCtr.call_pre_resv st r CP) as RV0.
  set (stA := SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (set_op HEAP_ID hN (s_ops st)) (s_priv st) nxE) in HS1.
  assert (CW : can_write asegs (s_facts stA) (s_priv stA) 0%uint63 r0 AERRNOi 4%uint63 = true).
  { unfold can_write. cbn [stA s_priv s_facts]. rewrite NPV.
    replace (Mem.abs_writable asegs (to_Z AERRNOi) (to_Z 4%uint63)) with true by (vm_compute; reflexivity). reflexivity. }
  assert (RVOK : resv_ok E1 (resv_after_store (s_facts st) (s_resv st) (VL (wlit AERRNOi))) None) by (rewrite RV0; reflexivity).
  destruct (StepM.store_sound asegs OPS E1 stA (CtrFrame.ms' ms r R' Mv) mo' (VL (wlit AERRNOi)) 0%uint63 (wlit AERRNOi) r0 AERRNOi 4%uint63
              (VP (s_next (clobber st1)) wzero) _ None HS1 ltac:(right; right; left; reflexivity) eq_refl F0 eq_refl CW RVOK) as [_ HS2].
  cbn [stA s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in HS2.

  assert (FOK : fresh_ok st = true) by (destruct (HeapCtr.call_pre_inv st r CP) as (X & _); exact X).
  assert (EVe : den E1 (VP (s_next (clobber st1)) wzero) = e').
  { rewrite HeapCtr.den_VPz. rewrite Cnx, Snx.
    destruct (HeapCtr.fresh_ok_inv st FOK) as (_ & _ & B). pose proof (int_range (s_next st)) as RI. rewrite two63_eq in RI.
    replace (PrimInt63.add (s_next st) 15%uint63) with (addn (s_next st) 15) by (apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]).
    unfold E1. rewrite (CtrFrame.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). exact FV15. }
  assert (EVa : den E1 (VL (wlit AERRNOi)) = Z_to_bv 64 AERRNO) by reflexivity.
  rewrite EVe, EVa in HS2.
  set (Mvv := write_to_mem Mv (Z_to_bv 64 AERRNO) (store_bytes 4%uint63 e')) in *.

  assert (IN4 : forall i, 0 <= i < 4 -> Mvv (Z_to_bv 64 (AERRNO + i)) = nth_error (ALib.Mem.le4 e') (Z.to_nat i)).
  { intros i Hi. subst Mvv. apply write_to_mem_in; [lia| change (length (store_bytes 4%uint63 e')) with (length (ALib.Mem.le4 e')); rewrite ALib.Mem.length_le4; unfold two64; lia
                                                  | change (length (store_bytes 4%uint63 e')) with (length (ALib.Mem.le4 e')); rewrite ALib.Mem.length_le4; lia]. }
  assert (OUT4 : forall a, 0 <= a < two64 -> ~ in_errno a -> Mvv (Z_to_bv 64 a) = Mv (Z_to_bv 64 a)).
  { intros a Ha NE. subst Mvv. apply write_to_mem_frame; [lia| change (length (store_bytes 4%uint63 e')) with (length (ALib.Mem.le4 e')); rewrite ALib.Mem.length_le4; unfold two64; lia| exact Ha
                                                         | change (length (store_bytes 4%uint63 e')) with (length (ALib.Mem.le4 e')); rewrite ALib.Mem.length_le4; exact NE]. }
  assert (RBeq : forall a, 0 <= a < two64 -> rb asegs m' a = rb asegs Mvv a).
  { intros a Ha. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold two64 in Ha; lia). destruct (DEC_E a) as [IE|NE].
    - unfold rb at 2. replace a with (AERRNO + (a - AERRNO)) at 2 by lia. rewrite (IN4 (a - AERRNO)) by (unfold in_errno in IE; lia).
      rewrite (GlueA.rb_mrdA asegs). destruct ERR' as [[_ (_ & _ & BY)] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
      pose proof (BY (Z.to_nat (a - AERRNO)) ltac:(rewrite ALib.Mem.length_le4; unfold in_errno in IE; lia)) as B1.
      rewrite Z2Nat.id in B1 by (unfold in_errno in IE; lia). replace (AERRNO + (a - AERRNO)) with a in B1 by lia. rewrite B1.
      destruct (nth_error (ALib.Mem.le4 e') (Z.to_nat (a - AERRNO))) eqn:X; [reflexivity|].
      exfalso. apply nth_error_None in X. rewrite ALib.Mem.length_le4 in X. unfold in_errno in IE. lia.
    - unfold rb. rewrite (OUT4 a Ha NE). change (Z_to_bv 64 a) with (ALib.Mem.wa a). rewrite (MvO a Ha' NE). reflexivity. }
  assert (WBle : forall a, 0 <= a < two64 -> wb asegs Mvv a = true -> wb asegs m' a = true).
  { intros a Ha W. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold two64 in Ha; lia). destruct (DEC_E a) as [IE|NE].
    - apply (GlueA.wb_wviewA asegs). destruct ERR' as [_ (_ & _ & WR)].
      pose proof (WR (a - AERRNO) ltac:(unfold in_errno in IE; cbn [cells_size csize Nat.add]; lia)) as WX.
      replace (AERRNO + (a - AERRNO)) with a in WX by lia. exact WX.
    - unfold wb, wview in *. rewrite (OUT4 a Ha NE) in W. change (Z_to_bv 64 a) with (ALib.Mem.wa a) in *. rewrite (MvO a Ha' NE) in W. exact W. }
  destruct (nodelta_heap_holds E st ms mo r hargs wnl L RNG sta LBa aw Fv Gv m' mo' RNG' sta' credN hN aw' HS CP CF HSA DCN SBU AH' AC' KEEPW TWP PSN)
    as (Hf & Hc & HOLDN).
  fold E1 in HOLDN.
  assert (OPSH : ops_hold OPS E1 (set_op HEAP_ID hN (s_ops st)) m' mo').
  { apply (ops_hold_set_op OPS E1 E1 (s_ops st) HEAP_ID hargs hN (ms_mem ms) m' mo mo' Hf Hc (so_ops _ _ _ _ _ _ (CtrFrame.HS' OPS E st ms mo HS FOK Fv Gv))); [| exact HOLDN].
    intros o Ho NI H. pose proof NI as NI0. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    apply (OPS_mo_other _ _ _ mo mo' NI OTH). apply (OPS_frame_other _ _ (ms_mem ms) m' mo NI H); [| exact WBM].
    intros a Ha FP. destruct (DEC_E a) as [IE|NE]; [| symmetry; exact (SBOe o a Ho NI0 Ha NE FP)].
    exfalso. pose proof (so_apart _ _ _ _ _ _ (CtrFrame.HS' OPS E st ms mo HS FOK Fv Gv)) as AP. unfold ops_apart in AP.
    destruct (proj1 (Forall_forall _ _) AP o Ho a FP) as [_ IP].
    apply (in_priv_b_false (s_priv st) AERRNOi 4%uint63 a NPV); [vm_compute; reflexivity| exact IE| exact (IP (errno_seg a IE))]. }
  assert (MINVfx : forall x b, m' x = Some b -> forall seg, find_segment asegs (bv_unsigned x) 1 = Some seg -> seg_writable seg = true).
  { intros x b Hx seg FSG. pose proof (MINV' x b Hx) as RO. unfold ALib.Mem.ro_addr in RO. rewrite FSG in RO. destruct (seg_writable seg); [reflexivity| discriminate RO]. }

  rewrite EQE. unfold setpc, set_ops. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  rewrite Cff, Sff, Cfs, Sfs, Crv, Srv, CR, Cos, Sos, Cpv, Spv.
  exact (MemFX.MemFX.st_ok_view_ext asegs OPS E1 _ R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None Mvv m' (seg_rom asegs) mo' HS2 RBeq WBle OPSH MINVfx).
Qed.

Hypothesis IMGSH_aci : forall v a, In v SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.

Theorem pres_e_st_ok : forall E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' (v : sv)
    (credN : sv) (hN : list sv) (aw' : word) (e0 e' : word) (stE : sstate),
  st_ok asegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  acallN E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) ->
  heap_set_A hargs credN = Some hN -> den (CtrFrame.E' E st Fv Gv) credN = aw' ->
  errno_havoc (setr (clobber st1) X10 v) = Some stE ->
  (forall rg, In rg CtrFrame.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg) ->
  (forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x)) ->
  den (CtrFrame.E' E st Fv Gv) v = AP.getr R' 10%bv ->
  Fv 15 = e' ->
  ALib.Step.rw_cells asegs (ms_mem ms) AERRNO [C4 e0] -> ALib.Step.rw_cells asegs m' AERRNO [C4 e'] ->
  ALib.Mem.mem_inv asegs m' ->
  stk asegs m' (CtrPre.sp_lo E st) (bv_unsigned (AP.getr (ms_regs ms) 2%bv)) -> ATOP + 4096 <= CtrPre.sp_lo E st ->
  aheap_pres_e (aci AI) LBa (bv_unsigned (AP.getr (ms_regs ms) 2%bv)) (ms_mem ms) m' ->
  twins_pres LBa (ms_mem ms) m' ->
  AHEAP AI L RNG' sta' LBa m' -> ACCT aw' L RNG' sta' LBa mo' ->
  OTHER mo mo' -> op_minv OPS mo' ->
  (CtrPre.prist_in E st -> aprist sta -> aprist sta') ->
  st_ok asegs OPS (CtrFrame.E' E st Fv Gv) (setpc (set_ops stE (set_op HEAP_ID hN (s_ops stE))) r) (CtrFrame.ms' ms r R' m') mo'.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' v credN hN aw' e0 e' stE
         HS CP FS CF AH HSA DCN HAV KEPT HF DV FV15 ERR0 ERR' MINV' STK' BOT PRESe TWP AH' AC' OTH MINVo PSN.
  set (m := ms_mem ms) in *. set (sp := bv_unsigned (AP.getr (ms_regs ms) 2%bv)) in *.
  set (Mv := mem_old_errno m m').
  assert (ERNG : 0 <= AERRNO /\ AERRNO + 4 <= AIMG_HI /\ AIMG_HI < 2 ^ 47) by (unfold AERRNO, ATP, AIMG_HI; lia).
  assert (MvI : forall a, 0 <= a < 2 ^ 64 -> in_errno a -> Mv (ALib.Mem.wa a) = m (ALib.Mem.wa a)).
  { intros a Ha IE. apply moe_in. unfold ALib.Mem.wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia). exact IE. }
  assert (MvO : forall a, 0 <= a < 2 ^ 64 -> ~ in_errno a -> Mv (ALib.Mem.wa a) = m' (ALib.Mem.wa a)).
  { intros a Ha IE. apply moe_out. unfold ALib.Mem.wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia). exact IE. }
  assert (DEC_E : forall a, in_errno a \/ ~ in_errno a) by (intros a; unfold in_errno; lia).

  assert (PRESv : aheap_pres (aci AI) LBa sp m Mv).
  { intros a Ha CA. destruct (DEC_E a) as [IE|NE].
    - rewrite (MvI a Ha IE). split; [reflexivity|]. unfold wview. rewrite (MvI a Ha IE). exact (fun H => H).
    - destruct (PRESe a Ha CA NE) as [P1 P2]. rewrite (MvO a Ha NE). split; [exact P1|]. unfold wview in *. rewrite (MvO a Ha NE). exact P2. }
  assert (TWPv : twins_pres LBa m Mv).
  { intros p A n Hin PR i Hi. destruct (AI_block_bounds AI _ _ _ _ _ (HB p A n) AH' Hin) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
    assert (SH : AIMG_HI <= shad A + i < 2 ^ 64).
    { unfold shad, ASHOFF. unfold shlen in Hi. rewrite Z.shiftr_div_pow2 in Hi by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8 in *. atop_facts. unfold AIMG_HI in *.
      assert (0 <= A / 8 <= A) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). assert ((n + 7) / 8 <= n + 7) by (apply Z.div_le_upper_bound; lia). lia. }
    rewrite (MvO (shad A + i)) by (unfold in_errno; lia). exact (TWP p A n Hin PR i Hi). }
  assert (AHv : AHEAP AI L RNG' sta' LBa Mv).
  { apply (AI_frame AI L RNG' sta' LBa m' Mv [(AERRNO, AERRNO + 4)] AH').
    - intros x [OUT _]. apply moe_out. exact OUT.
    - intros x WV. destruct (DEC_E (bv_unsigned x)) as [IE|NE]; [| unfold Mv; unfold wview in *; rewrite (moe_out _ _ x NE); exact WV].
      destruct ERR0 as [_ (_ & _ & WR)]. pose proof (WR (bv_unsigned x - AERRNO) ltac:(unfold in_errno in IE; cbn [cells_size csize Nat.add]; lia)) as WX.
      replace (ALib.Mem.wa (AERRNO + (bv_unsigned x - AERRNO))) with x in WX by (unfold ALib.Mem.wa; replace (AERRNO + (bv_unsigned x - AERRNO)) with (bv_unsigned x) by lia; rewrite Z_to_bv_bv_unsigned; reflexivity).
      unfold Mv; unfold wview in *. rewrite (moe_in _ _ x IE). exact WX.
    - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (AERRNO + 4 - AERRNO) with 4 by lia. exact (AERRNO_client LBa (ATOP + 4096)). }

  assert (STBx : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.stableA AI ms LB0 a -> ~ in_errno a ->
            m' (ALib.Mem.wa a) = m (ALib.Mem.wa a)).
  { intros LB0 (W0 & (E1 & E2 & E3 & E4) & ARW0) a Ha ST0 NE. pose proof ARW0 as [HW0 _]. pose proof HW0 as (_ & HT0 & _).
    destruct (LB_classify AI ACCT UNIV AI_fake W0 aw LB0 m mo HW0) as (KU & KT).
    rewrite <- (MvO a Ha NE).
    apply (aw_real_stable AI ACCT UNIV AI_fake aw LB0 m mo W0 RNG' sta' LBa Mv LBa LB0 sp LBa TWPv ltac:(intros b0 Hb0 _ _; rewrite <- E4; exact Hb0) ARW0).
    - rewrite E1. exact AHv.
    - exact PRESv.
    - intros v0 Hv UB P. destruct (KU v0 Hv UB P) as (b & Vb & ->). exists b. split; [rewrite <- E4; exact (proj1 Vb)| reflexivity].
    - intros v0 Hv NUB. destruct (KT v0 Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
      + left. exists b. destruct (HT0 b Hb) as [HbL HH0]. split; [exact HbL|]. split; [rewrite <- E4; exact HbL|]. split; [exact HH0| reflexivity].
      + right. exists b. split; [exact (proj1 (proj1 Vb))|]. split; [rewrite <- E4; exact (proj1 (proj1 Vb))|]. split; [exact (proj2 Vb)| reflexivity].
    - exact Ha.
    - exact ST0. }
  assert (RAWV : forall a, m' (ALib.Mem.wa a) = m (ALib.Mem.wa a) -> rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true)).
  { intros a EQ. split; [unfold rb; unfold ALib.Mem.wa in EQ; rewrite EQ; reflexivity|].
    intros Wb. apply (GlueA.wb_wviewA asegs). apply (GlueA.wb_wviewA asegs) in Wb. rewrite (wview_ext1 m' m _ EQ). exact Wb. }
  assert (CLX : forall a, 0 <= a < 2 ^ 64 -> aclient_addr (aci AI) LBa sp a -> ~ in_errno a ->
            rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true)).
  { intros a Ha CA NE. apply RAWV. exact (proj1 (PRESe a Ha CA NE)). }
  apply (nodelta_errno_st_ok E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' v credN hN aw' e0 e' stE
           HS CP FS CF HSA DCN HAV KEPT HF DV FV15 ERR0 ERR' MINV' STK' BOT).
  -   intros LB0 AR0 a Ha STB NE. apply RAWV. exact (STBx LB0 AR0 a Ha STB NE).
  -   intros LB0 AR0 a Ha IU. destruct (DEC_E a) as [IE|NE]; [| apply (STBx LB0 AR0 a Ha); [right; right; exact IU| exact NE]].
    exfalso. destruct AR0 as (W0 & (E1 & E2 & E3 & E4) & ARW0). pose proof ARW0 as [HW0 _].
    apply in_ivs_In in IU as (v0 & Hv & Hin).
    pose proof (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB0 m mo v0 a (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW0) Hv Hin) as [_ BAND].
    destruct (errno_seg a IE) as [seg SG]. rewrite SG in BAND. discriminate BAND.
  -
    intros o a Ho NI Ha NE FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    assert (CA : aclient_addr (aci AI) LBa sp a).
    { destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
      - right; left; exact INA.
      - right; right; right. exists a'. split; [right; left; exact INA| reflexivity].
      - right; right; right. exists a'. split; [left; exact STK| reflexivity]. }
    pose proof (proj1 (PRESe a ltac:(unfold two64 in Ha; lia) CA NE)) as E0. unfold ALib.Mem.wa in E0. exact E0.
  -
    intros a Ha CC Wb. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold two64 in Ha; lia).
    destruct (DEC_E a) as [IE|NE].
    + apply (GlueA.wb_wviewA asegs). destruct ERR' as [_ (_ & _ & WR)].
      pose proof (WR (a - AERRNO) ltac:(unfold in_errno in IE; cbn [cells_size csize Nat.add]; lia)) as WX.
      replace (AERRNO + (a - AERRNO)) with a in WX by lia. exact WX.
    + apply (CLX a Ha'); [| exact NE| exact Wb].
      destruct CC as [CC|[(a' & CC & ->)|(a' & CC & ->)]]; [right; left; exact CC| |]; right; right; right; exists a'; (split; [| reflexivity]); [right; left; exact CC| left; exact CC].
  -
    intros a Ha SC IB. assert (NE : ~ in_errno a).
    { unfold in_errno. destruct SC as [(a' & RRa & ->)|(vv & Hv & RRa)].
      - unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. atop_facts. unfold AIMG_HI in *. Z.div_mod_to_equations. lia.
      - destruct (IMGSH_aci vv a Hv RRa) as (a' & INA & ->). destruct INA as (iv0 & Hi0 & Hin0). pose proof (AI_aci_lo AI iv0 Hi0) as LO0.
        unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold AIMG_HI in *. Z.div_mod_to_equations. lia. }
    apply (CLX a Ha); [| exact NE].
    destruct SC as [(a' & RRa & ->)|(vv & Hv & RRa)].
    + right; right; right. exists a'. split; [left; exact RRa| reflexivity].
    + destruct (IMGSH_aci vv a Hv RRa) as (a' & INA & ->). right; right; right. exists a'. split; [right; left; exact INA| reflexivity].
  - exact AH'.
  - exact AC'.
  -
    intros b x Hb FK Hx. pose proof (Op.blk_band AI AI_fake L RNG sta LBa m b x AH Hb Hx) as BB.
    refine (proj1 (PRESe x ltac:(unfold AIMG_HI, KLS in BB; lia) ltac:(right; right; left; exists b; split; [exact Hb| exact Hx]) _)).
    unfold in_errno. unfold AIMG_HI, KLS in *. lia.
  - exact TWP.
  - exact OTH.
  - exact MINVo.
  - exact PSN.
Qed.

Definition cfvE (R' : bvmap 5 word) (e : word) (i : Z) : word :=
  nth (Z.to_nat i)
      [AP.getr R' 1%bv; AP.getr R' 5%bv; AP.getr R' 6%bv; AP.getr R' 7%bv;
       AP.getr R' 11%bv; AP.getr R' 12%bv; AP.getr R' 13%bv; AP.getr R' 14%bv;
       AP.getr R' 15%bv; AP.getr R' 16%bv; AP.getr R' 17%bv;
       AP.getr R' 28%bv; AP.getr R' 29%bv; AP.getr R' 30%bv; AP.getr R' 31%bv; e] (Z_to_bv 64 0).
Lemma cfvE_clob : forall R' e x i, clob_pos x = Some i -> cfvE R' e (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Proof. intros R' e x i H. destruct x; cbn in H; try discriminate; injection H as <-; cbn; f_equal; apply bv_eq; reflexivity. Qed.

Theorem anull_post_ok : forall st E ms mo L RNG sta LBa aw r hargs wnl st1 cred stN sta' RNG' msP mo',
  st_ok asegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  acallN E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) ->
  heap_A hargs = Some cred ->
  null_post hargs cred (clobber st1) r = Some stN ->
  ATOP + 4096 <= CtrPre.sp_lo E st ->
  let R := ms_regs ms in
  amalloc_null_post2 (aci AI) (AHEAP AI) L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) LBa (CtrPre.sp_lo E st) (ms_mem ms) sta' RNG' msP ->
  ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' sta' LBa mo' ->
  (CtrPre.prist_in E st -> aprist sta -> aprist sta') -> op_minv OPS mo' -> OTHER mo mo' ->
  exists E1, env_ext (s_next st) E E1 /\ st_ok asegs OPS E1 stN msP mo'.
Proof.
  intros st E ms mo L RNG sta LBa aw r hargs wnl st1 cred stN sta' RNG' msP mo' HS CP FS CF AH HA NPOST BOT R HQ ACP PSN MINVo OTH.
  destruct (errno_cells (ms_mem ms)) as [e0 ERR0].
  destruct HQ as (FPLE & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV' & STK' & PRESe & TWP & AH' & ERR').
  match type of EMS with msP = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (Fv := cfvE R' (Z_to_bv 64 12)). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.reg_of_X1, (GlueA.getr_RA asegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.den_wlit. }
  assert (EMS' : msP = CtrFrame.ms' ms r R' m').
  { rewrite EMS. unfold CtrFrame.ms'. f_equal. rewrite RAEQ. apply MState.ret_pc_even.
    - pose proof (int_range r) as RRr. rewrite two63_eq in RRr. lia.
    - pose proof (HeapCtr.call_pre_even st r CP) as EV0.
      pose proof (ValP.land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV0 in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }

  destruct (null_post_inv hargs cred (clobber st1) r stN NPOST) as (stE & hN & HAV & HSA & ->).
  exists (CtrFrame.E' E st Fv Gv). split; [exact (CtrFrame.EXT E st Fv Gv)|].
  rewrite EMS'.
  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AJ & WF & HC & AWden & WIT).
  assert (EC : cred = A) by (rewrite Eh in HA; cbn [heap_A] in HA; congruence).
  apply (pres_e_st_ok E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' (VL wzero) (sv_alu ALU_SUB cred (VL C_EXHw)) hN
           (Z_to_bv 64 (bv_unsigned aw - 1048576)) e0 (Z_to_bv 64 12) stE HS CP FS CF AH HSA); try assumption.
  -
    rewrite den_sv_alu, EC. rewrite (CtrFrame.den_E' E st Fv Gv A (CtrFrame.A_below st FOK rest hargs md A nw Hf Eh)). unfold alu64, alu. apply bv_eq.
    rewrite bv_sub_unsigned, Z_to_bv_unsigned, AWden. reflexivity.
  - intros rg Hrg. unfold CtrFrame.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
  - intros x i Hx. exact (cfvE_clob R' _ x i Hx).
  - reflexivity.
  - reflexivity.
Qed.

End Null.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem.

Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Lemma errno_havoc_inv : forall st2 stE, errno_havoc st2 = Some stE ->
  exists r0, IMap.find 0%uint63 (s_regs st2) = Some r0 /\ in_priv_b (s_priv st2) AERRNOi 4%uint63 = false
    /\ stE = SS (s_pc st2) (s_rf st2) (s_ff st2) (resv_after_store (s_facts st2) (s_resv st2) (VL (wlit AERRNOi)))
                (IMap.add 0%uint63 (Mem.region_store r0 AERRNOi 4%uint63 (VP (s_next st2) wzero)) (s_regs st2))
                (s_facts st2) (s_ops st2) (s_priv st2) (PrimInt63.add (s_next st2) 1%uint63).
Proof.
  intros st2 stE H. unfold errno_havoc in H. destruct (IMap.find 0%uint63 (s_regs st2)) as [r0|]; [|discriminate].
  destruct (in_priv_b (s_priv st2) AERRNOi 4%uint63) eqn:Q; [discriminate|].
  unfold fresh, set_next in H. cbn [fst snd s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in H. injection H as <-.
  exists r0. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma null_post_inv : forall hargs cred st2 r stN, null_post hargs cred st2 r = Some stN ->
  exists stE hN, errno_havoc (setr st2 X10 (VL wzero)) = Some stE /\ heap_set_A hargs (sv_alu ALU_SUB cred (VL C_EXHw)) = Some hN
    /\ stN = setpc (set_ops stE (set_op HEAP_ID hN (s_ops stE))) r.
Proof.
  intros hargs cred st2 r stN H. unfold null_post in H.
  destruct (errno_havoc (setr st2 X10 (VL wzero))) as [stE|]; [| discriminate H].
  destruct (heap_set_A hargs (sv_alu ALU_SUB cred (VL C_EXHw))) as [hN|]; [| discriminate H].
  exists stE, hN. split; [reflexivity|]. split; [reflexivity|]. injection H as <-. reflexivity.
Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> ALib.Mem.le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold ALib.Mem.le4, le_bytes_to_word.
  pose proof (AP.bytes_le_to_Z_bound bs) as HR. pose proof (AP.bytes_le_to_Z_nonneg bs) as H0. rewrite HL in HR.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z in HR.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia). rewrite <- HL. apply Shadow.Z_to_le_bytes_to_Z.
Qed.
Section ErrnoCells.
Context {rc : runConstT}.

Lemma ties_ext_p : forall W W' ws, w_T W' = w_T W -> (forall b, visf W' b <-> visf W b) -> w_zc W' = w_zc W -> ties W ws ->
  (forall b, is_heap b -> vis W' b -> vis W b) -> (In prist_win ws -> aprist (w_st W')) -> ties W' ws.
Proof.
  intros W W' ws ET EV EZ (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & C24 & GA & PR) HV PS. unfold ties. rewrite ET, EZ.
  split; [exact T1|]. split; [exact T2|]. split; [intros b Hb; apply T3; apply EV; exact Hb|].
  split; [intros w Hw K; destruct (T4 w Hw K) as (b & Vb & E); exists b; split; [apply EV; exact Vb| exact E]|].
  split; [intros w Hw K; destruct (T5 w Hw K) as (b & Vb & E); exists b; split; [apply EV; exact Vb| exact E]|].
  split; [exact T6| split; [exact T7| split; [exact T8|]]].
  split; [intros b Vb HH CC; exact (C24 b (HV b HH Vb) HH CC)| split; [exact GA| exact PS]].
Qed.

Lemma rw_cells_of_rb0 : forall (m : amem) A cs,
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
Lemma errno_cells : forall m : amem, exists e0 : word, ALib.Step.rw_cells bsegs m AERRNO [C4 e0].
Proof.
  intros m.
  assert (AW : Mem.abs_writable bsegs AERRNO 4 = true) by (vm_compute; reflexivity).
  assert (EA : 0 <= AERRNO) by (unfold AERRNO, ATP; lia).
  destruct (MemP.abs_writable_sound bsegs AERRNO 4 EA ltac:(lia) AW) as [AR BY].
  destruct (MemP.abs_readable_sound bsegs AERRNO 4 ltac:(lia) AR) as [_ RD].
  assert (B : forall i, 0 <= i < 4 -> exists b, rb bsegs m (AERRNO + i) = Some b).
  { intros i Hi. rewrite (GlueA.TwinB.rb_mrdA bsegs). unfold ALib.Mem.mrd. destruct (m (ALib.Mem.wa (AERRNO + i))) as [b|]; [exists b; reflexivity|].
    destruct (RD i Hi) as (b & rest & MR). exists b. unfold seg_rom, ALib.Mem.wa. rewrite MR. reflexivity. }
  destruct (B 0 ltac:(lia)) as [b0 H0]. destruct (B 1 ltac:(lia)) as [b1 H1]. destruct (B 2 ltac:(lia)) as [b2 H2]. destruct (B 3 ltac:(lia)) as [b3 H3].
  exists (le_bytes_to_word [b0; b1; b2; b3]). apply rw_cells_of_rb0.
  - split; exact I.
  - exact EA.
  - cbn [cells_size csize Nat.add]. unfold AERRNO, ATP. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite (le4_of_bytes [b0; b1; b2; b3] eq_refl).
    intros i Hi. cbn [length] in Hi.
    destruct i as [|[|[|[|i]]]]; [rewrite Z.add_0_r; exact H0| exact H1| exact H2| exact H3| lia].
  - cbn [cells_size csize Nat.add]. intros i Hi. exact (proj1 (BY i Hi) m).
Qed.
End ErrnoCells.

Section Null.
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
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.

Definition acallN (E : env) (st : sstate) (ms : machine_state) (mo : Model) (r : int) (hargs : list sv) (wnl : list (int * sv * w64))
    (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) : Prop :=
  exists (LB : blocks) (ks : int) (offs : w64) (rss : region) (ksp : int) (nn : nat) (md : w64) (A : sv) (nw : w64) (rest : list sv),
    sp_region st = Some (ks, offs, rss) /\ okey offs = Some ksp
    /\ bv_unsigned (AP.getr (ms_regs ms) 2%bv) = bv_unsigned (ev E ks) + keyZ ksp
    /\ keyZ ksp mod 16 = 0 /\ loZ rss <= keyZ ksp /\ ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss
    /\ find_op HEAP_ID (s_ops st) = Some hargs /\ CtrA.count_op HEAP_ID (s_ops st) = 1%nat
    /\ hargs = VL md :: A :: VL nw :: rest /\ wt nw = false /\ nn = Z.to_nat (to_Z (wl nw)) /\ (3 * nn <= length rest)%nat /\ (nn <= 255)%nat
    /\ CtrA.nonstack_windows nn rest = Some wnl /\ aregions_justified st wnl = true
    /\ windows_wf (wins_of E nn rest) LB (ATOP + 4096)
    /\ cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) (ms_mem ms)
    /\ aw = den E A
    /\ exists W, wit_of W L RNG sta LBa /\ aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo W /\ ties W (wins_of E nn rest).
Lemma acallN_of_G : forall E st ms mo r hargs wnl L RNG sta LBa aw,
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> acallN E st ms mo r hargs wnl L RNG sta LBa aw.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13
     & H14 & _ & H16 & _ & H18 & H19 & H20 & H21).
  exists LB, ks, offs, rss, ksp, nn, md, A, nw, rest. repeat (split; [assumption|]). assumption.
Qed.
Lemma acallN_of_facts : forall XN E st ms mo L RNG sta LBa aw n,
  CtrPre.TwinB.acall_facts AI ACCT UNIV Cw XN E st ms mo L RNG sta LBa aw n ->
  exists r hargs wnl st1, call_pre st = Some r /\ forget_stack_below_sp_g st = Some st1 /\ acallN E st ms mo r hargs wnl L RNG sta LBa aw.
Proof.
  intros XN E st ms mo L RNG sta LBa aw n (LB & r & hargs & st1 & ks & offs & rss & ksp & wnl & nn & md & A & nw & rest & CP & FS & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9
     & H10 & H11 & H12 & H13 & H14 & H16 & H18 & H19 & H20 & H21 & _).
  exists r, hargs, wnl, st1. split; [exact CP|]. split; [exact FS|].
  exists LB, ks, offs, rss, ksp, nn, md, A, nw, rest. repeat (split; [assumption|]). assumption.
Qed.

Theorem nodelta_cred_st_ok : forall E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' (v : sv) (nx' : int) (credN : sv) (hN : list sv) (aw' : word),
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  acallN E st ms mo r hargs wnl L RNG sta LBa aw ->

  heap_set_A hargs credN = Some hN -> den (CtrFrame.TwinB.E' E st Fv Gv) credN = aw' ->

  (forall rg, In rg CtrFrame.TwinB.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg) ->
  (forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x)) ->
  den (CtrFrame.TwinB.E' E st Fv Gv) v = AP.getr R' 10%bv ->

  ALib.Mem.mem_inv bsegs m' ->
  stk bsegs m' (CtrPre.TwinB.sp_lo E st) (bv_unsigned (AP.getr (ms_regs ms) 2%bv)) ->

  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LB a ->
     rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true)) ->
  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB a ->
     m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)) ->
  (forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
     Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den (CtrFrame.TwinB.E' E st Fv Gv)) (op_args o))) ->
     m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
     wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true) ->

  (forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
     rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true)) ->

  AHEAP AI L RNG' sta' LBa m' -> ACCT aw' L RNG' sta' LBa mo' ->
  (forall b x, In b LBa -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (ALib.Mem.wa x) = ms_mem ms (ALib.Mem.wa x)) ->
  twins_pres LBa (ms_mem ms) m' ->
  OTHER mo mo' -> op_minv OPS mo' ->
  (CtrPre.TwinB.prist_in E st -> aprist sta -> aprist sta') ->
  st_ok bsegs OPS (CtrFrame.TwinB.E' E st Fv Gv)
    (SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (set_op HEAP_ID hN (s_ops st)) (s_priv st) nx')
    (CtrFrame.TwinB.ms' ms r R' m') mo'.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' v nx' credN hN aw' HS CP FS CF HSA DCN KEPT HF DV MINV' STK' SBVall SBUall SBO WBM SBT AH' AC' KEEPW TWP OTH MINVo PSN.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AJ & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & _).
  pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW) as AWH.
  assert (AR : aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa) by (exists W; split; [exact WOF| exact ARW]).
  pose proof (SBVall LB AR) as SBV. pose proof (SBUall LB AR) as SBU.
  set (W' := mkWit (w_L W) RNG' sta' (w_LBa W) (w_T W) (w_FA W) m' (w_zc W)).
  assert (AR' : aw_realW AI ACCT UNIV aw' LB m' mo' W').
  { destruct WOF as (E1 & E2 & E3 & E4). pose proof ARW as [(_ & _ & _ & HFA & _) _].
    apply (aw_real_nodelta AI ACCT UNIV AI_fake aw aw' LB (ms_mem ms) mo W RNG' sta' m' mo' ARW); [rewrite E1, E4; exact AH'| rewrite E1, E4; exact AC'| | rewrite E4; exact TWP].
    intros b x Hb FK Hx. apply (KEEPW b x); [rewrite <- E4; exact Hb| exact FK| exact Hx]. }
  assert (TI' : ties W' (wins_of E nn rest)).
  { apply (ties_ext_p W W'); [reflexivity| intros b; reflexivity| reflexivity| exact TI| intros b _ V; exact V|]. intros IP. subst W'. cbn [w_st].
    destruct WOF as (_ & _ & E3 & _). apply PSN; [| rewrite <- E3; exact (ties_prist W _ TI IP)]. exists hargs, md, A, nw, rest. split; [exact Hf|]. split; [exact Eh|]. rewrite <- Nn. exact IP. }
  pose proof STK' as STK2.

  assert (WINK : forall k0 len kd, True -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
            forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LB a).
  { intros k0 len kd _ WL a Ha.
    destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k0 len kd NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
    pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
    - exfalso. exact (KD KS0).
    - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
    - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia. }

  assert (EhN : hN = VL md :: credN :: VL nw :: rest) by (rewrite Eh in HSA; cbn [heap_set_A] in HSA; injection HSA as <-; reflexivity).
  assert (DECN : decode (map (den (CtrFrame.TwinB.E' E st Fv Gv)) hN) = Some (w2Z md, aw', wins_of E nn rest, map (den E) (skipn (3 * nn) rest))).
  { pose proof (CtrFrame.TwinB.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln) as D0. rewrite Eh in D0.
    rewrite (decode_hargs (CtrFrame.TwinB.E' E st Fv Gv) md A nw rest nn Tnw Nn Ln) in D0.
    assert (DW : wins_of (CtrFrame.TwinB.E' E st Fv Gv) nn rest = wins_of E nn rest) by congruence.
    assert (DR : map (den (CtrFrame.TwinB.E' E st Fv Gv)) (skipn (3 * nn) rest) = map (den E) (skipn (3 * nn) rest)) by congruence.
    rewrite EhN, (decode_hargs (CtrFrame.TwinB.E' E st Fv Gv) md credN nw rest nn Tnw Nn Ln), DW, DR, DCN. reflexivity. }
  assert (HOLDN : op_holds OPS HEAP_ID (map (den (CtrFrame.TwinB.E' E st Fv Gv)) hN) m' mo').
  { rewrite OPS_holds1. exists (w2Z md), aw', (wins_of E nn rest), (map (den E) (skipn (3 * nn) rest)), LB, W'.
    split; [exact DECN|]. split; [exact (proj1 AR')|]. split; [exact WF|]. split; [| exact TI'].
    apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U _. symmetry. unfold ALib.Mem.wa in SBU.
    apply (SBU a ltac:(unfold two64 in Ha; lia)). exact U. }
  replace (s_regs st1) with (CtrFrame.TwinB.RgPg st ks rss ksp [] []).
  2:{ unfold forget_stack_below_sp_g in FS. rewrite SPR, Hksp in FS. injection FS as <-. reflexivity. }
  apply (CtrFrame.TwinB.frame_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv r st1 CP FS R' m' mo' KEPT HF aw LB LB AWH MINV' SBV SBO WBM SBT ks offs rss ksp SPR SPE wnl nn rest AJ WF (fun _ => True) WINK ltac:(intros; exact I) ltac:(intros; exact I)
           K16 LOSP STK2 FLOOR hargs md A nw Hf Hc Eh Tnw Nn Ln OTH [] [] (NoDup_nil _)
           ltac:(intros k1 r1 X; destruct X) ltac:(intros k0 _; exact I) (fun _ => False) ltac:(intros k1 r1 X; destruct X) ltac:(intros k1 r1 a1 X; destruct X)
           ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros k1 r1 k2 r2 a1 X; destruct X)
           hN (w2Z md) aw' (wins_of E nn rest) (map (den E) (skipn (3 * nn) rest)) DECN HOLDN).
  - intros a X. destruct X.
  - intros a Ha NIX NWS. left. exact NWS.
  - intros a _ X. exact X.
  - exact (so_facts _ _ _ _ _ _ (CtrFrame.TwinB.HS' OPS E st ms mo HS FOK Fv Gv)).
  - exact DV.
  - exact MINVo.
Qed.

Lemma nodelta_heap_holds : forall E st ms mo r hargs wnl L RNG sta LBa aw Fv Gv m' mo' RNG' sta' (credN : sv) (hN : list sv) (aw' : word),
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r ->
  acallN E st ms mo r hargs wnl L RNG sta LBa aw ->
  heap_set_A hargs credN = Some hN -> den (CtrFrame.TwinB.E' E st Fv Gv) credN = aw' ->
  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB a ->
     m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)) ->
  AHEAP AI L RNG' sta' LBa m' -> ACCT aw' L RNG' sta' LBa mo' ->
  (forall b x, In b LBa -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (ALib.Mem.wa x) = ms_mem ms (ALib.Mem.wa x)) ->
  twins_pres LBa (ms_mem ms) m' ->
  (CtrPre.TwinB.prist_in E st -> aprist sta -> aprist sta') ->
  find_op HEAP_ID (s_ops st) = Some hargs /\ CtrA.count_op HEAP_ID (s_ops st) = 1%nat
  /\ op_holds OPS HEAP_ID (map (den (CtrFrame.TwinB.E' E st Fv Gv)) hN) m' mo'.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw Fv Gv m' mo' RNG' sta' credN hN aw' HS CP CF HSA DCN SBUall AH' AC' KEEPW TWP PSN.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AJ & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & _).
  assert (AR : aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa) by (exists W; split; [exact WOF| exact ARW]).
  pose proof (SBUall LB AR) as SBU.
  set (W' := mkWit (w_L W) RNG' sta' (w_LBa W) (w_T W) (w_FA W) m' (w_zc W)).
  assert (AR' : aw_realW AI ACCT UNIV aw' LB m' mo' W').
  { destruct WOF as (E1 & E2 & E3 & E4). pose proof ARW as [(_ & _ & _ & HFA & _) _].
    apply (aw_real_nodelta AI ACCT UNIV AI_fake aw aw' LB (ms_mem ms) mo W RNG' sta' m' mo' ARW); [rewrite E1, E4; exact AH'| rewrite E1, E4; exact AC'| | rewrite E4; exact TWP].
    intros b x Hb FK Hx. apply (KEEPW b x); [rewrite <- E4; exact Hb| exact FK| exact Hx]. }
  assert (TI' : ties W' (wins_of E nn rest)).
  { apply (ties_ext_p W W'); [reflexivity| intros b; reflexivity| reflexivity| exact TI| intros b _ V; exact V|]. intros IP. subst W'. cbn [w_st].
    destruct WOF as (_ & _ & E3 & _). apply PSN; [| rewrite <- E3; exact (ties_prist W _ TI IP)]. exists hargs, md, A, nw, rest. split; [exact Hf|]. split; [exact Eh|]. rewrite <- Nn. exact IP. }
  assert (EhN : hN = VL md :: credN :: VL nw :: rest) by (rewrite Eh in HSA; cbn [heap_set_A] in HSA; injection HSA as <-; reflexivity).
  assert (DECN : decode (map (den (CtrFrame.TwinB.E' E st Fv Gv)) hN) = Some (w2Z md, aw', wins_of E nn rest, map (den E) (skipn (3 * nn) rest))).
  { pose proof (CtrFrame.TwinB.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln) as D0. rewrite Eh in D0.
    rewrite (decode_hargs (CtrFrame.TwinB.E' E st Fv Gv) md A nw rest nn Tnw Nn Ln) in D0.
    assert (DW : wins_of (CtrFrame.TwinB.E' E st Fv Gv) nn rest = wins_of E nn rest) by congruence.
    assert (DR : map (den (CtrFrame.TwinB.E' E st Fv Gv)) (skipn (3 * nn) rest) = map (den E) (skipn (3 * nn) rest)) by congruence.
    rewrite EhN, (decode_hargs (CtrFrame.TwinB.E' E st Fv Gv) md credN nw rest nn Tnw Nn Ln), DW, DR, DCN. reflexivity. }
  split; [exact Hf|]. split; [exact Hc|].
  rewrite OPS_holds1. exists (w2Z md), aw', (wins_of E nn rest), (map (den E) (skipn (3 * nn) rest)), LB, W'.
  split; [exact DECN|]. split; [exact (proj1 AR')|]. split; [exact WF|]. split; [| exact TI'].
  apply (cw_frame Cw _ _ _ _ (ms_mem ms) m' HC). intros a Ha U _. symmetry. unfold ALib.Mem.wa in SBU.
  apply (SBU a ltac:(unfold two64 in Ha; lia)). exact U.
Qed.

Lemma errno_seg : forall a, AERRNO <= a < AERRNO + 4 -> exists seg, find_segment bsegs a 1 = Some seg.
Proof.
  intros a Ha. rewrite BImg.a_find_segment_1 by (unfold AERRNO, ATP in Ha; lia). unfold AERRNO, ATP in Ha.
  replace (0x10000 <=? a) with true by (symmetry; apply Z.leb_le; lia). replace (a + 1 <=? 0x3c000) with false by (symmetry; apply Z.leb_gt; lia).
  replace (0x3c000 <=? a) with true by (symmetry; apply Z.leb_le; lia). replace (a + 1 <=? 0xcf000) with false by (symmetry; apply Z.leb_gt; lia).
  replace (0xcf000 <=? a) with true by (symmetry; apply Z.leb_le; lia). replace (a + 1 <=? 0xd5000) with false by (symmetry; apply Z.leb_gt; lia).
  replace (0xd5000 <=? a) with true by (symmetry; apply Z.leb_le; lia). replace (a + 1 <=? 0x631000) with true by (symmetry; apply Z.leb_le; lia).
  cbn [andb]. eexists. reflexivity.
Qed.

Definition in_errno (x : Z) : Prop := AERRNO <= x < AERRNO + 4.
Definition in_errno_b (x : Z) : bool := (AERRNO <=? x) && (x <? AERRNO + 4).
Lemma in_errno_b_spec : forall x, in_errno_b x = true <-> in_errno x.
Proof. intros x. unfold in_errno_b, in_errno. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Definition mem_old_errno (m m' : amem) : amem := fun x => if in_errno_b (bv_unsigned x) then m x else m' x.

Lemma moe_in : forall m m' x, in_errno (bv_unsigned x) -> mem_old_errno m m' x = m x.
Proof. intros m m' x H. unfold mem_old_errno. rewrite (proj2 (in_errno_b_spec _) H). reflexivity. Qed.
Lemma moe_out : forall m m' x, ~ in_errno (bv_unsigned x) -> mem_old_errno m m' x = m' x.
Proof. intros m m' x H. unfold mem_old_errno. destruct (in_errno_b (bv_unsigned x)) eqn:Q; [exfalso; exact (H (proj1 (in_errno_b_spec _) Q))| reflexivity]. Qed.

Hypothesis AERRNO_client : forall LB SP, aclient_range (aci AI) LB SP AERRNO 4.

Theorem nodelta_errno_st_ok : forall E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' (v : sv)
    (credN : sv) (hN : list sv) (aw' : word) (e0 e' : word) (stE : sstate),
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  acallN E st ms mo r hargs wnl L RNG sta LBa aw ->
  heap_set_A hargs credN = Some hN -> den (CtrFrame.TwinB.E' E st Fv Gv) credN = aw' ->
  errno_havoc (setr (clobber st1) X10 v) = Some stE ->
  (forall rg, In rg CtrFrame.TwinB.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg) ->
  (forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x)) ->
  den (CtrFrame.TwinB.E' E st Fv Gv) v = AP.getr R' 10%bv ->
  Fv 15 = e' ->
  ALib.Step.rw_cells bsegs (ms_mem ms) AERRNO [C4 e0] -> ALib.Step.rw_cells bsegs m' AERRNO [C4 e'] ->
  ALib.Mem.mem_inv bsegs m' ->
  stk bsegs m' (CtrPre.TwinB.sp_lo E st) (bv_unsigned (AP.getr (ms_regs ms) 2%bv)) -> ATOP + 4096 <= CtrPre.TwinB.sp_lo E st ->

  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LB a -> ~ in_errno a ->
     rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true)) ->
  (forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB a ->
     m' (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)) ->
  (forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 -> ~ in_errno a ->
     Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den (CtrFrame.TwinB.E' E st Fv Gv)) (op_args o))) ->
     m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
     wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true) ->
  (forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
     rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true)) ->
  AHEAP AI L RNG' sta' LBa m' -> ACCT aw' L RNG' sta' LBa mo' ->
  (forall b x, In b LBa -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> m' (ALib.Mem.wa x) = ms_mem ms (ALib.Mem.wa x)) ->
  twins_pres LBa (ms_mem ms) m' ->
  OTHER mo mo' -> op_minv OPS mo' ->
  (CtrPre.TwinB.prist_in E st -> aprist sta -> aprist sta') ->
  st_ok bsegs OPS (CtrFrame.TwinB.E' E st Fv Gv) (setpc (set_ops stE (set_op HEAP_ID hN (s_ops stE))) r) (CtrFrame.TwinB.ms' ms r R' m') mo'.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' v credN hN aw' e0 e' stE
         HS CP FS CF HSA DCN HAV KEPT HF DV FV15 ERR0 ERR' MINV' STK' BOT SBVe SBU SBOe WBM SBT AH' AC' KEEPW TWP OTH MINVo PSN.
  set (Mv := mem_old_errno (ms_mem ms) m').
  set (E1 := CtrFrame.TwinB.E' E st Fv Gv) in *.
  assert (ERNG : 0 <= AERRNO /\ AERRNO + 4 <= AIMG_HI /\ AIMG_HI < 2 ^ 47) by (unfold AERRNO, ATP, AIMG_HI; lia).
  assert (MvI : forall a, 0 <= a < 2 ^ 64 -> in_errno a -> Mv (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)).
  { intros a Ha IE. apply moe_in. unfold ALib.Mem.wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia). exact IE. }
  assert (MvO : forall a, 0 <= a < 2 ^ 64 -> ~ in_errno a -> Mv (ALib.Mem.wa a) = m' (ALib.Mem.wa a)).
  { intros a Ha IE. apply moe_out. unfold ALib.Mem.wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia). exact IE. }

  assert (RBi : forall a, 0 <= a < 2 ^ 64 -> in_errno a -> rb bsegs Mv a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs Mv a = true)).
  { intros a Ha IE. unfold rb, wb, wview. change (Z_to_bv 64 a) with (ALib.Mem.wa a). rewrite (MvI a Ha IE). split; [reflexivity| exact (fun H => H)]. }
  assert (RBo : forall a, 0 <= a < 2 ^ 64 -> ~ in_errno a -> rb bsegs Mv a = rb bsegs m' a /\ (wb bsegs m' a = true -> wb bsegs Mv a = true)).
  { intros a Ha IE. unfold rb, wb, wview. change (Z_to_bv 64 a) with (ALib.Mem.wa a). rewrite (MvO a Ha IE). split; [reflexivity| exact (fun H => H)]. }
  assert (DEC_E : forall a, in_errno a \/ ~ in_errno a) by (intros a; unfold in_errno; lia).

  assert (SBVv : forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LB a ->
            rb bsegs Mv a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs Mv a = true)).
  { intros LB AR a Ha SA. destruct (DEC_E a) as [IE|NE]; [exact (RBi a Ha IE)|].
    destruct (RBo a Ha NE) as [R1 W1]. destruct (SBVe LB AR a Ha SA NE) as [R2 W2]. split; [rewrite R1; exact R2| intros W; exact (W1 (W2 W))]. }
  assert (SBUv : forall LB, aw_real AI ACCT UNIV aw LB (ms_mem ms) mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> in_user LB a ->
            Mv (ALib.Mem.wa a) = ms_mem ms (ALib.Mem.wa a)).
  { intros LB AR a Ha IU. destruct (DEC_E a) as [IE|NE]; [exact (MvI a Ha IE)| rewrite (MvO a Ha NE); exact (SBU LB AR a Ha IU)]. }
  assert (SBOv : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
            Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E1) (op_args o))) -> Mv (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
  { intros o a Ho NI Ha FP. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold two64 in Ha; lia). change (Z_to_bv 64 a) with (ALib.Mem.wa a).
    destruct (DEC_E a) as [IE|NE]; [exact (MvI a Ha' IE)| rewrite (MvO a Ha' NE); exact (SBOe o a Ho NI Ha NE FP)]. }
  assert (WBMv : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
            wb bsegs (ms_mem ms) a = true -> wb bsegs Mv a = true).
  { intros a Ha C W. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold two64 in Ha; lia).
    destruct (DEC_E a) as [IE|NE]; [exact (proj2 (RBi a Ha' IE) W)| exact (proj2 (RBo a Ha' NE) (WBM a Ha C W))]. }
  assert (SBTv : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
            rb bsegs Mv a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs Mv a = true)).
  { intros a Ha SC IB. destruct (DEC_E a) as [IE|NE]; [exact (RBi a Ha IE)|].
    destruct (RBo a Ha NE) as [R1 W1]. destruct (SBT a Ha SC IB) as [R2 W2]. split; [rewrite R1; exact R2| intros W; exact (W1 (W2 W))]. }
  assert (KEEPWv : forall b x, In b LBa -> is_fake b -> ab_addr b <= x < ab_addr b + ab_size b -> Mv (ALib.Mem.wa x) = ms_mem ms (ALib.Mem.wa x)).
  { intros b x Hb FK Hx. destruct (AI_block_bounds AI _ _ _ _ _ b AH' Hb) as (B1 & B2 & B3). assert (Hx' : 0 <= x < 2 ^ 64) by (atop_facts; lia).
    rewrite (MvO x Hx') by (unfold in_errno; lia). exact (KEEPW b x Hb FK Hx). }
  assert (TWPv : twins_pres LBa (ms_mem ms) Mv).
  { intros p A n Hin PR i Hi. destruct (AI_block_bounds AI _ _ _ _ _ (HB p A n) AH' Hin) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
    assert (SH : AIMG_HI <= shad A + i < 2 ^ 64).
    { unfold shad, ASHOFF. unfold shlen in Hi. rewrite Z.shiftr_div_pow2 in Hi by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8 in *. atop_facts. unfold AIMG_HI in *.
      assert (0 <= A / 8 <= A) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). assert ((n + 7) / 8 <= n + 7) by (apply Z.div_le_upper_bound; lia). lia. }
    rewrite (MvO (shad A + i)) by (unfold in_errno; lia). exact (TWP p A n Hin PR i Hi). }
  assert (MINVv : ALib.Mem.mem_inv bsegs Mv).
  { intros a b H. unfold Mv, mem_old_errno in H. destruct (in_errno_b (bv_unsigned a)); [| exact (MINV' a b H)].
    unfold ALib.Mem.ro_addr. destruct (find_segment bsegs (bv_unsigned a) 1) as [seg|] eqn:FSG; [| reflexivity].
    rewrite (so_minv _ _ _ _ _ _ HS a b H seg FSG). reflexivity. }
  assert (STKv : stk bsegs Mv (CtrPre.TwinB.sp_lo E st) (bv_unsigned (AP.getr (ms_regs ms) 2%bv))).
  { destruct STK' as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha.
    assert (Ha' : 0 <= a < 2 ^ 64) by lia. assert (NE : ~ in_errno a) by (unfold in_errno; atop_facts; unfold AIMG_HI in *; lia).
    destruct (S3 a Ha) as [W1 R1]. unfold wview, ALib.Mem.mrd in *. rewrite (MvO a Ha' NE). split; [exact W1| exact R1]. }
  assert (AHv : AHEAP AI L RNG' sta' LBa Mv).
  { apply (AI_frame AI L RNG' sta' LBa m' Mv [(AERRNO, AERRNO + 4)] AH').
    - intros x [OUT _]. apply moe_out. exact OUT.
    - intros x WV. destruct (DEC_E (bv_unsigned x)) as [IE|NE]; [| unfold Mv; unfold wview in *; rewrite (moe_out _ _ x NE); exact WV].
      destruct ERR0 as [_ (_ & _ & WR)]. pose proof (WR (bv_unsigned x - AERRNO) ltac:(unfold in_errno in IE; cbn [cells_size csize Nat.add]; lia)) as WX.
      replace (ALib.Mem.wa (AERRNO + (bv_unsigned x - AERRNO))) with x in WX by (unfold ALib.Mem.wa; replace (AERRNO + (bv_unsigned x - AERRNO)) with (bv_unsigned x) by lia; rewrite Z_to_bv_bv_unsigned; reflexivity).
      unfold Mv; unfold wview in *. rewrite (moe_in _ _ x IE). exact WX.
    - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (AERRNO + 4 - AERRNO) with 4 by lia. exact (AERRNO_client LBa (ATOP + 4096)). }

  set (nxE := PrimInt63.add (s_next (clobber st1)) 1%uint63).
  pose proof (nodelta_cred_st_ok E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' Mv mo' RNG' sta' v nxE credN hN aw'
                HS CP FS CF HSA DCN KEPT HF DV MINVv STKv SBVv SBUv SBOv WBMv SBTv AHv AC' KEEPWv TWPv OTH MINVo PSN) as HS1.
  fold E1 in HS1.

  destruct (errno_havoc_inv _ _ HAV) as (r0 & F0 & NPV & EQE).
  destruct (clobber_fields st1) as (Cpc & Cff & Crv & CR & Cfs & Cos & Cpv & Cnx).
  destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (Spc & Srf & Sff & Srv & Sfs & Sos & Spv & Snx).
  cbn [setr s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in F0, NPV, EQE.
  rewrite CR in F0. rewrite Cpv, Spv in NPV.
  pose proof (HeapCtr.TwinB.call_pre_resv st r CP) as RV0.
  set (stA := SS r (rf_set (s_rf (clobber st1)) X10 v) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (set_op HEAP_ID hN (s_ops st)) (s_priv st) nxE) in HS1.
  assert (CW : can_write bsegs (s_facts stA) (s_priv stA) 0%uint63 r0 AERRNOi 4%uint63 = true).
  { unfold can_write. cbn [stA s_priv s_facts]. rewrite NPV.
    replace (Mem.abs_writable bsegs (to_Z AERRNOi) (to_Z 4%uint63)) with true by (vm_compute; reflexivity). reflexivity. }
  assert (RVOK : resv_ok E1 (resv_after_store (s_facts st) (s_resv st) (VL (wlit AERRNOi))) None) by (rewrite RV0; reflexivity).
  destruct (StepM.store_sound bsegs OPS E1 stA (CtrFrame.TwinB.ms' ms r R' Mv) mo' (VL (wlit AERRNOi)) 0%uint63 (wlit AERRNOi) r0 AERRNOi 4%uint63
              (VP (s_next (clobber st1)) wzero) _ None HS1 ltac:(right; right; left; reflexivity) eq_refl F0 eq_refl CW RVOK) as [_ HS2].
  cbn [stA s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in HS2.

  assert (FOK : fresh_ok st = true) by (destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (X & _); exact X).
  assert (EVe : den E1 (VP (s_next (clobber st1)) wzero) = e').
  { rewrite HeapCtr.TwinB.den_VPz. rewrite Cnx, Snx.
    destruct (HeapCtr.TwinB.fresh_ok_inv st FOK) as (_ & _ & B). pose proof (int_range (s_next st)) as RI. rewrite two63_eq in RI.
    replace (PrimInt63.add (s_next st) 15%uint63) with (addn (s_next st) 15) by (apply addn_lit; [reflexivity| rewrite wB_two63, two63_eq; lia]).
    unfold E1. rewrite (CtrFrame.TwinB.ev_E'_fresh E st FOK Fv Gv 15 ltac:(lia)). exact FV15. }
  assert (EVa : den E1 (VL (wlit AERRNOi)) = Z_to_bv 64 AERRNO) by reflexivity.
  rewrite EVe, EVa in HS2.
  set (Mvv := write_to_mem Mv (Z_to_bv 64 AERRNO) (store_bytes 4%uint63 e')) in *.

  assert (IN4 : forall i, 0 <= i < 4 -> Mvv (Z_to_bv 64 (AERRNO + i)) = nth_error (ALib.Mem.le4 e') (Z.to_nat i)).
  { intros i Hi. subst Mvv. apply write_to_mem_in; [lia| change (length (store_bytes 4%uint63 e')) with (length (ALib.Mem.le4 e')); rewrite ALib.Mem.length_le4; unfold two64; lia
                                                  | change (length (store_bytes 4%uint63 e')) with (length (ALib.Mem.le4 e')); rewrite ALib.Mem.length_le4; lia]. }
  assert (OUT4 : forall a, 0 <= a < two64 -> ~ in_errno a -> Mvv (Z_to_bv 64 a) = Mv (Z_to_bv 64 a)).
  { intros a Ha NE. subst Mvv. apply write_to_mem_frame; [lia| change (length (store_bytes 4%uint63 e')) with (length (ALib.Mem.le4 e')); rewrite ALib.Mem.length_le4; unfold two64; lia| exact Ha
                                                         | change (length (store_bytes 4%uint63 e')) with (length (ALib.Mem.le4 e')); rewrite ALib.Mem.length_le4; exact NE]. }
  assert (RBeq : forall a, 0 <= a < two64 -> rb bsegs m' a = rb bsegs Mvv a).
  { intros a Ha. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold two64 in Ha; lia). destruct (DEC_E a) as [IE|NE].
    - unfold rb at 2. replace a with (AERRNO + (a - AERRNO)) at 2 by lia. rewrite (IN4 (a - AERRNO)) by (unfold in_errno in IE; lia).
      rewrite (GlueA.TwinB.rb_mrdA bsegs). destruct ERR' as [[_ (_ & _ & BY)] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
      pose proof (BY (Z.to_nat (a - AERRNO)) ltac:(rewrite ALib.Mem.length_le4; unfold in_errno in IE; lia)) as B1.
      rewrite Z2Nat.id in B1 by (unfold in_errno in IE; lia). replace (AERRNO + (a - AERRNO)) with a in B1 by lia. rewrite B1.
      destruct (nth_error (ALib.Mem.le4 e') (Z.to_nat (a - AERRNO))) eqn:X; [reflexivity|].
      exfalso. apply nth_error_None in X. rewrite ALib.Mem.length_le4 in X. unfold in_errno in IE. lia.
    - unfold rb. rewrite (OUT4 a Ha NE). change (Z_to_bv 64 a) with (ALib.Mem.wa a). rewrite (MvO a Ha' NE). reflexivity. }
  assert (WBle : forall a, 0 <= a < two64 -> wb bsegs Mvv a = true -> wb bsegs m' a = true).
  { intros a Ha W. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold two64 in Ha; lia). destruct (DEC_E a) as [IE|NE].
    - apply (GlueA.TwinB.wb_wviewA bsegs). destruct ERR' as [_ (_ & _ & WR)].
      pose proof (WR (a - AERRNO) ltac:(unfold in_errno in IE; cbn [cells_size csize Nat.add]; lia)) as WX.
      replace (AERRNO + (a - AERRNO)) with a in WX by lia. exact WX.
    - unfold wb, wview in *. rewrite (OUT4 a Ha NE) in W. change (Z_to_bv 64 a) with (ALib.Mem.wa a) in *. rewrite (MvO a Ha' NE) in W. exact W. }
  destruct (nodelta_heap_holds E st ms mo r hargs wnl L RNG sta LBa aw Fv Gv m' mo' RNG' sta' credN hN aw' HS CP CF HSA DCN SBU AH' AC' KEEPW TWP PSN)
    as (Hf & Hc & HOLDN).
  fold E1 in HOLDN.
  assert (OPSH : ops_hold OPS E1 (set_op HEAP_ID hN (s_ops st)) m' mo').
  { apply (ops_hold_set_op OPS E1 E1 (s_ops st) HEAP_ID hargs hN (ms_mem ms) m' mo mo' Hf Hc (so_ops _ _ _ _ _ _ (CtrFrame.TwinB.HS' OPS E st ms mo HS FOK Fv Gv))); [| exact HOLDN].
    intros o Ho NI H. pose proof NI as NI0. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    apply (OPS_mo_other _ _ _ mo mo' NI OTH). apply (OPS_frame_other _ _ (ms_mem ms) m' mo NI H); [| exact WBM].
    intros a Ha FP. destruct (DEC_E a) as [IE|NE]; [| symmetry; exact (SBOe o a Ho NI0 Ha NE FP)].
    exfalso. pose proof (so_apart _ _ _ _ _ _ (CtrFrame.TwinB.HS' OPS E st ms mo HS FOK Fv Gv)) as AP. unfold ops_apart in AP.
    destruct (proj1 (Forall_forall _ _) AP o Ho a FP) as [_ IP].
    apply (in_priv_b_false (s_priv st) AERRNOi 4%uint63 a NPV); [vm_compute; reflexivity| exact IE| exact (IP (errno_seg a IE))]. }
  assert (MINVfx : forall x b, m' x = Some b -> forall seg, find_segment bsegs (bv_unsigned x) 1 = Some seg -> seg_writable seg = true).
  { intros x b Hx seg FSG. pose proof (MINV' x b Hx) as RO. unfold ALib.Mem.ro_addr in RO. rewrite FSG in RO. destruct (seg_writable seg); [reflexivity| discriminate RO]. }

  rewrite EQE. unfold setpc, set_ops. cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  rewrite Cff, Sff, Cfs, Sfs, Crv, Srv, CR, Cos, Sos, Cpv, Spv.
  exact (MemFX.MemFX.st_ok_view_ext bsegs OPS E1 _ R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None Mvv m' (seg_rom bsegs) mo' HS2 RBeq WBle OPSH MINVfx).
Qed.

Hypothesis IMGSH_aci : forall v a, In v SHLIT -> fst v <= a < snd v -> exists a', in_ranges (aci AI) a' /\ a = shad a'.

Theorem pres_e_st_ok : forall E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' (v : sv)
    (credN : sv) (hN : list sv) (aw' : word) (e0 e' : word) (stE : sstate),
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  acallN E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) ->
  heap_set_A hargs credN = Some hN -> den (CtrFrame.TwinB.E' E st Fv Gv) credN = aw' ->
  errno_havoc (setr (clobber st1) X10 v) = Some stE ->
  (forall rg, In rg CtrFrame.TwinB.kept_regsA -> AP.getr R' rg = AP.getr (ms_regs ms) rg) ->
  (forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = AP.getr R' (reg_of_r5 x)) ->
  den (CtrFrame.TwinB.E' E st Fv Gv) v = AP.getr R' 10%bv ->
  Fv 15 = e' ->
  ALib.Step.rw_cells bsegs (ms_mem ms) AERRNO [C4 e0] -> ALib.Step.rw_cells bsegs m' AERRNO [C4 e'] ->
  ALib.Mem.mem_inv bsegs m' ->
  stk bsegs m' (CtrPre.TwinB.sp_lo E st) (bv_unsigned (AP.getr (ms_regs ms) 2%bv)) -> ATOP + 4096 <= CtrPre.TwinB.sp_lo E st ->
  aheap_pres_e (aci AI) LBa (bv_unsigned (AP.getr (ms_regs ms) 2%bv)) (ms_mem ms) m' ->
  twins_pres LBa (ms_mem ms) m' ->
  AHEAP AI L RNG' sta' LBa m' -> ACCT aw' L RNG' sta' LBa mo' ->
  OTHER mo mo' -> op_minv OPS mo' ->
  (CtrPre.TwinB.prist_in E st -> aprist sta -> aprist sta') ->
  st_ok bsegs OPS (CtrFrame.TwinB.E' E st Fv Gv) (setpc (set_ops stE (set_op HEAP_ID hN (s_ops stE))) r) (CtrFrame.TwinB.ms' ms r R' m') mo'.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' v credN hN aw' e0 e' stE
         HS CP FS CF AH HSA DCN HAV KEPT HF DV FV15 ERR0 ERR' MINV' STK' BOT PRESe TWP AH' AC' OTH MINVo PSN.
  set (m := ms_mem ms) in *. set (sp := bv_unsigned (AP.getr (ms_regs ms) 2%bv)) in *.
  set (Mv := mem_old_errno m m').
  assert (ERNG : 0 <= AERRNO /\ AERRNO + 4 <= AIMG_HI /\ AIMG_HI < 2 ^ 47) by (unfold AERRNO, ATP, AIMG_HI; lia).
  assert (MvI : forall a, 0 <= a < 2 ^ 64 -> in_errno a -> Mv (ALib.Mem.wa a) = m (ALib.Mem.wa a)).
  { intros a Ha IE. apply moe_in. unfold ALib.Mem.wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia). exact IE. }
  assert (MvO : forall a, 0 <= a < 2 ^ 64 -> ~ in_errno a -> Mv (ALib.Mem.wa a) = m' (ALib.Mem.wa a)).
  { intros a Ha IE. apply moe_out. unfold ALib.Mem.wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold W64.two64; lia). exact IE. }
  assert (DEC_E : forall a, in_errno a \/ ~ in_errno a) by (intros a; unfold in_errno; lia).

  assert (PRESv : aheap_pres (aci AI) LBa sp m Mv).
  { intros a Ha CA. destruct (DEC_E a) as [IE|NE].
    - rewrite (MvI a Ha IE). split; [reflexivity|]. unfold wview. rewrite (MvI a Ha IE). exact (fun H => H).
    - destruct (PRESe a Ha CA NE) as [P1 P2]. rewrite (MvO a Ha NE). split; [exact P1|]. unfold wview in *. rewrite (MvO a Ha NE). exact P2. }
  assert (TWPv : twins_pres LBa m Mv).
  { intros p A n Hin PR i Hi. destruct (AI_block_bounds AI _ _ _ _ _ (HB p A n) AH' Hin) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
    assert (SH : AIMG_HI <= shad A + i < 2 ^ 64).
    { unfold shad, ASHOFF. unfold shlen in Hi. rewrite Z.shiftr_div_pow2 in Hi by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8 in *. atop_facts. unfold AIMG_HI in *.
      assert (0 <= A / 8 <= A) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). assert ((n + 7) / 8 <= n + 7) by (apply Z.div_le_upper_bound; lia). lia. }
    rewrite (MvO (shad A + i)) by (unfold in_errno; lia). exact (TWP p A n Hin PR i Hi). }
  assert (AHv : AHEAP AI L RNG' sta' LBa Mv).
  { apply (AI_frame AI L RNG' sta' LBa m' Mv [(AERRNO, AERRNO + 4)] AH').
    - intros x [OUT _]. apply moe_out. exact OUT.
    - intros x WV. destruct (DEC_E (bv_unsigned x)) as [IE|NE]; [| unfold Mv; unfold wview in *; rewrite (moe_out _ _ x NE); exact WV].
      destruct ERR0 as [_ (_ & _ & WR)]. pose proof (WR (bv_unsigned x - AERRNO) ltac:(unfold in_errno in IE; cbn [cells_size csize Nat.add]; lia)) as WX.
      replace (ALib.Mem.wa (AERRNO + (bv_unsigned x - AERRNO))) with x in WX by (unfold ALib.Mem.wa; replace (AERRNO + (bv_unsigned x - AERRNO)) with (bv_unsigned x) by lia; rewrite Z_to_bv_bv_unsigned; reflexivity).
      unfold Mv; unfold wview in *. rewrite (moe_in _ _ x IE). exact WX.
    - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (AERRNO + 4 - AERRNO) with 4 by lia. exact (AERRNO_client LBa (ATOP + 4096)). }

  assert (STBx : forall LB0, aw_real AI ACCT UNIV aw LB0 m mo L RNG sta LBa -> forall a, 0 <= a < 2 ^ 64 -> CtrFrame.TwinB.stableA AI ms LB0 a -> ~ in_errno a ->
            m' (ALib.Mem.wa a) = m (ALib.Mem.wa a)).
  { intros LB0 (W0 & (E1 & E2 & E3 & E4) & ARW0) a Ha ST0 NE. pose proof ARW0 as [HW0 _]. pose proof HW0 as (_ & HT0 & _).
    destruct (LB_classify AI ACCT UNIV AI_fake W0 aw LB0 m mo HW0) as (KU & KT).
    rewrite <- (MvO a Ha NE).
    apply (aw_real_stable AI ACCT UNIV AI_fake aw LB0 m mo W0 RNG' sta' LBa Mv LBa LB0 sp LBa TWPv ltac:(intros b0 Hb0 _ _; rewrite <- E4; exact Hb0) ARW0).
    - rewrite E1. exact AHv.
    - exact PRESv.
    - intros v0 Hv UB P. destruct (KU v0 Hv UB P) as (b & Vb & ->). exists b. split; [rewrite <- E4; exact (proj1 Vb)| reflexivity].
    - intros v0 Hv NUB. destruct (KT v0 Hv NUB) as [(b & Hb & ->)|(b & Vb & ->)].
      + left. exists b. destruct (HT0 b Hb) as [HbL HH0]. split; [exact HbL|]. split; [rewrite <- E4; exact HbL|]. split; [exact HH0| reflexivity].
      + right. exists b. split; [exact (proj1 (proj1 Vb))|]. split; [rewrite <- E4; exact (proj1 (proj1 Vb))|]. split; [exact (proj2 Vb)| reflexivity].
    - exact Ha.
    - exact ST0. }
  assert (RAWV : forall a, m' (ALib.Mem.wa a) = m (ALib.Mem.wa a) -> rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true)).
  { intros a EQ. split; [unfold rb; unfold ALib.Mem.wa in EQ; rewrite EQ; reflexivity|].
    intros Wb. apply (GlueA.TwinB.wb_wviewA bsegs). apply (GlueA.TwinB.wb_wviewA bsegs) in Wb. rewrite (wview_ext1 m' m _ EQ). exact Wb. }
  assert (CLX : forall a, 0 <= a < 2 ^ 64 -> aclient_addr (aci AI) LBa sp a -> ~ in_errno a ->
            rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true)).
  { intros a Ha CA NE. apply RAWV. exact (proj1 (PRESe a Ha CA NE)). }
  apply (nodelta_errno_st_ok E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' v credN hN aw' e0 e' stE
           HS CP FS CF HSA DCN HAV KEPT HF DV FV15 ERR0 ERR' MINV' STK' BOT).
  -   intros LB0 AR0 a Ha STB NE. apply RAWV. exact (STBx LB0 AR0 a Ha STB NE).
  -   intros LB0 AR0 a Ha IU. destruct (DEC_E a) as [IE|NE]; [| apply (STBx LB0 AR0 a Ha); [right; right; exact IU| exact NE]].
    exfalso. destruct AR0 as (W0 & (E1 & E2 & E3 & E4) & ARW0). pose proof ARW0 as [HW0 _].
    apply in_ivs_In in IU as (v0 & Hv & Hin).
    pose proof (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB0 m mo v0 a (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW0) Hv Hin) as [_ BAND].
    destruct (errno_seg a IE) as [seg SG]. rewrite SG in BAND. discriminate BAND.
  -
    intros o a Ho NI Ha NE FP. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    assert (CA : aclient_addr (aci AI) LBa sp a).
    { destruct (OPS_fp_other _ _ a NI FP) as [INA|[(a' & INA & ->)|(a' & STK & ->)]].
      - right; left; exact INA.
      - right; right; right. exists a'. split; [right; left; exact INA| reflexivity].
      - right; right; right. exists a'. split; [left; exact STK| reflexivity]. }
    pose proof (proj1 (PRESe a ltac:(unfold two64 in Ha; lia) CA NE)) as E0. unfold ALib.Mem.wa in E0. exact E0.
  -
    intros a Ha CC Wb. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold two64 in Ha; lia).
    destruct (DEC_E a) as [IE|NE].
    + apply (GlueA.TwinB.wb_wviewA bsegs). destruct ERR' as [_ (_ & _ & WR)].
      pose proof (WR (a - AERRNO) ltac:(unfold in_errno in IE; cbn [cells_size csize Nat.add]; lia)) as WX.
      replace (AERRNO + (a - AERRNO)) with a in WX by lia. exact WX.
    + apply (CLX a Ha'); [| exact NE| exact Wb].
      destruct CC as [CC|[(a' & CC & ->)|(a' & CC & ->)]]; [right; left; exact CC| |]; right; right; right; exists a'; (split; [| reflexivity]); [right; left; exact CC| left; exact CC].
  -
    intros a Ha SC IB. assert (NE : ~ in_errno a).
    { unfold in_errno. destruct SC as [(a' & RRa & ->)|(vv & Hv & RRa)].
      - unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. atop_facts. unfold AIMG_HI in *. Z.div_mod_to_equations. lia.
      - destruct (IMGSH_aci vv a Hv RRa) as (a' & INA & ->). destruct INA as (iv0 & Hi0 & Hin0). pose proof (AI_aci_lo AI iv0 Hi0) as LO0.
        unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold AIMG_HI in *. Z.div_mod_to_equations. lia. }
    apply (CLX a Ha); [| exact NE].
    destruct SC as [(a' & RRa & ->)|(vv & Hv & RRa)].
    + right; right; right. exists a'. split; [left; exact RRa| reflexivity].
    + destruct (IMGSH_aci vv a Hv RRa) as (a' & INA & ->). right; right; right. exists a'. split; [right; left; exact INA| reflexivity].
  - exact AH'.
  - exact AC'.
  -
    intros b x Hb FK Hx. pose proof (Op.TwinB.blk_band AI AI_fake L RNG sta LBa m b x AH Hb Hx) as BB.
    refine (proj1 (PRESe x ltac:(unfold AIMG_HI, KLS in BB; lia) ltac:(right; right; left; exists b; split; [exact Hb| exact Hx]) _)).
    unfold in_errno. unfold AIMG_HI, KLS in *. lia.
  - exact TWP.
  - exact OTH.
  - exact MINVo.
  - exact PSN.
Qed.

Definition cfvE (R' : bvmap 5 word) (e : word) (i : Z) : word :=
  nth (Z.to_nat i)
      [AP.getr R' 1%bv; AP.getr R' 5%bv; AP.getr R' 6%bv; AP.getr R' 7%bv;
       AP.getr R' 11%bv; AP.getr R' 12%bv; AP.getr R' 13%bv; AP.getr R' 14%bv;
       AP.getr R' 15%bv; AP.getr R' 16%bv; AP.getr R' 17%bv;
       AP.getr R' 28%bv; AP.getr R' 29%bv; AP.getr R' 30%bv; AP.getr R' 31%bv; e] (Z_to_bv 64 0).
Lemma cfvE_clob : forall R' e x i, clob_pos x = Some i -> cfvE R' e (Z.of_nat i) = AP.getr R' (reg_of_r5 x).
Proof. intros R' e x i H. destruct x; cbn in H; try discriminate; injection H as <-; cbn; f_equal; apply bv_eq; reflexivity. Qed.

Theorem anull_post_ok : forall st E ms mo L RNG sta LBa aw r hargs wnl st1 cred stN sta' RNG' msP mo',
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  acallN E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) ->
  heap_A hargs = Some cred ->
  null_post hargs cred (clobber st1) r = Some stN ->
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st ->
  let R := ms_regs ms in
  amalloc_null_post2 (aci AI) (AHEAP AI) L RNG (AP.getr R 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R 8) (AP.getr R 9)
     (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
     (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) LBa (CtrPre.TwinB.sp_lo E st) (ms_mem ms) sta' RNG' msP ->
  ACCT (Z_to_bv 64 (bv_unsigned aw - 1048576)) L RNG' sta' LBa mo' ->
  (CtrPre.TwinB.prist_in E st -> aprist sta -> aprist sta') -> op_minv OPS mo' -> OTHER mo mo' ->
  exists E1, env_ext (s_next st) E E1 /\ st_ok bsegs OPS E1 stN msP mo'.
Proof.
  intros st E ms mo L RNG sta LBa aw r hargs wnl st1 cred stN sta' RNG' msP mo' HS CP FS CF AH HA NPOST BOT R HQ ACP PSN MINVo OTH.
  destruct (errno_cells (ms_mem ms)) as [e0 ERR0].
  destruct HQ as (FPLE & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MINV' & STK' & PRESe & TWP & AH' & ERR').
  match type of EMS with msP = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (Fv := cfvE R' (Z_to_bv 64 12)). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0).
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.TwinB.den_wlit. }
  assert (EMS' : msP = CtrFrame.TwinB.ms' ms r R' m').
  { rewrite EMS. unfold CtrFrame.TwinB.ms'. f_equal. rewrite RAEQ. apply MState.ret_pc_even.
    - pose proof (int_range r) as RRr. rewrite two63_eq in RRr. lia.
    - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EV0.
      pose proof (ValP.land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV0 in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }

  destruct (null_post_inv hargs cred (clobber st1) r stN NPOST) as (stE & hN & HAV & HSA & ->).
  exists (CtrFrame.TwinB.E' E st Fv Gv). split; [exact (CtrFrame.TwinB.EXT E st Fv Gv)|].
  rewrite EMS'.
  pose proof CF as CF0.
  destruct CF0 as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AJ & WF & HC & AWden & WIT).
  assert (EC : cred = A) by (rewrite Eh in HA; cbn [heap_A] in HA; congruence).
  apply (pres_e_st_ok E st ms mo r hargs wnl L RNG sta LBa aw st1 Fv Gv R' m' mo' RNG' sta' (VL wzero) (sv_alu ALU_SUB cred (VL C_EXHw)) hN
           (Z_to_bv 64 (bv_unsigned aw - 1048576)) e0 (Z_to_bv 64 12) stE HS CP FS CF AH HSA); try assumption.
  -
    rewrite den_sv_alu, EC. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv A (CtrFrame.TwinB.A_below st FOK rest hargs md A nw Hf Eh)). unfold alu64, alu. apply bv_eq.
    rewrite bv_sub_unsigned, Z_to_bv_unsigned, AWden. reflexivity.
  - intros rg Hrg. unfold CtrFrame.TwinB.kept_regsA in Hrg. cbn [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]). destruct Hrg.
  - intros x i Hx. exact (cfvE_clob R' _ x i Hx).
  - reflexivity.
  - reflexivity.
Qed.

End Null.
End TwinB.
