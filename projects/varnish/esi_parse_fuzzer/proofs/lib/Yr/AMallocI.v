(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AIcpm9j ARtStmts AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@CFL; @CFU; @CGPS; @CINI; @CMCS; @CPS; @FR0; @Tctx; @Tini; @Tkey; @Tthr; @Ttsd]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aobjL H := let A := fresh "A" H in pose proof (proj1 H) as A; aobj_lin1 A.
Ltac aobj_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => exact (proj1 H) end
  | match goal with K : aobjK _ _ |- _ => exact (aobjK_e _ _ K) end
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_sub _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_sub _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | apply aobj_hi; kun; lia ].
Ltac pz_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_pz_in _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | unfold pz_in, kLowShadowMapBeg, kHighMemBeg; kun; lia ].

Notation wz z := (Z_to_bv 64 z) (only parsing).
Definition TP : Z := 0x5e83d8.
Definition malloc_icpt_entry : Z := 0x58b4c.
Definition alloc_entry : Z := 0x3719c.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition malloc_pro_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (n tsd ctx thr top bot lo : Z) (Q : machine_state -> Prop),
    let fp := bv_unsigned sp in
    mem_inv rsegs m -> stk rsegs m lo fp -> lo <= fp - 2128 - 224 -> alloc_ceiling <= lo ->
    tp = wz TP -> fp mod 16 = 0 -> fp <= 2^47 -> a0 = wz n -> 0 <= n < 2^64 ->
    4096 <= bv_unsigned ra -> bv_unsigned ra <> 0x58c14 -> bv_unsigned s0 <= fp -> 0 <= top < 2^64 -> 0 <= bot < 2^64 ->
    thread_cells m tp tsd ctx thr ->
    ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)] ->                                              (* [comment removed for export] *)
    ro_cells rsegs m 0xa9170 [C8 (wz 0x144e60)] -> ro_cells rsegs m 0x144e60 [C8 (wz 4096)] ->   (* [comment removed for export] *)
    ro_cells rsegs m 0xb60bc [C4 (wz 30)] ->                                                     (* [comment removed for export] *)
    ro_cells rsegs m 0xa9180 [C8 (wz 0x146ee8)] -> ro_cells rsegs m (0x146ee8 + 34) [C1 (Z_to_bv 8 1)] ->  (* [comment removed for export] *)
    rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)] -> ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
    (thr + 4096 <= lo \/ fp + 2^16 <= thr) ->
    (forall (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (pad jb1 jrest : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (fp + -2128) [C8 (wz (fp + -2128 + 16))] ->
        (if unwind_depth2 top bot fp
         then rw_cells rsegs m' (fp + -2128 + 8) [C4 (wz 2)] /\ rw_cells rsegs m' (fp + -2128 + 16) [C8 (wz 0x58c14); C8 ra]
         else rw_cells rsegs m' (fp + -2128 + 8) [C4 (wz 1)] /\ rw_cells rsegs m' (fp + -2128 + 16) [C8 (wz 0x58c14); CB 8 jb1]) ->
        rw_cells rsegs m' (fp + -2128 + 12) [C4 (wz 0)] ->
        rw_cells rsegs m' (fp + -2128 + 32) [CB 2024 jrest] ->
        rw_cells rsegs m' (fp + -2128 + 2056) [C8 (wz fp)] ->
        rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' (fp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells rsegs m' (fp + -2144) [C8 sp; C8 (wz 0x58c80)] ->
        munch [(fp - 2128 - 224, fp); (thr + off_th_unwinding, thr + off_th_unwinding + 1)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (fp - 2144) ->
        evt rsegs Q (MS (mkR (wz 0x3716c) (wz (fp + -2144)) gp tp t0' t1' t2' sp (wz n)
                         (wz 0xb1d58) (wz n) (wz 8) (wz (fp + -2128)) (wz 1) (wz 1) a6' a7'
                         (wz 0x58c14) (wz 1) (wz (fp + -2128)) (wz (fp + -81)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz alloc_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz malloc_icpt_entry) fc None m (seg_rom rsegs)).

End CEIL.

(* [comment removed for export] *)
Lemma rwc_rebytes : forall m A cs cs', cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  rw_cells rsegs m A cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' WF' E [[WF B] W]. split; [split; [exact WF'|]|].
  - rewrite E. exact B.
  - rewrite <- (cells_bytes_length cs' WF'), E, (cells_bytes_length cs WF). exact W.
Qed.
Lemma rwc_tl : forall m A c cs, rw_cells rsegs m A (c :: cs) -> rw_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs [[[WF1 WF2] BA] (W0 & W1 & W2)].
  cbn [cells_bytes] in BA. apply bytes_at_app in BA. destruct BA as [BA1 BA2].
  rewrite (cbytes_length c WF1) in BA2. cbn [cells_size] in W1, W2.
  split; [split; [exact WF2| exact BA2]|].
  split; [lia|]. split; [rewrite Nat2Z.inj_add in W1; lia|].
  intros i Hi. replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply W2.
  rewrite Nat2Z.inj_add. lia.
Qed.
Lemma rwc_ro : forall m A cs, rw_cells rsegs m A cs -> ro_cells rsegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.
Lemma land_ones64_l' : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma obj_split_80 : forall m A (w : word) junk (t : word), length junk = 2040%nat ->
  rw_cells rsegs m A [C8 w; C8 (Z_to_bv 64 0); CB 2040 junk; C8 t] ->
  rw_cells rsegs m A [C8 w; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 2040 junk; C8 t].
Proof.
  intros m A w junk t L H. eapply rwc_rebytes; [| | exact H].
  - cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; exact L.
  - cbn [cells_bytes cbytes app]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma obj_split_80h : forall m A (w : word) junk, length junk = 2040%nat ->
  rw_cells rsegs m A [C8 w; C8 (Z_to_bv 64 0); CB 2040 junk] ->
  rw_cells rsegs m A [C8 w; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 2040 junk].
Proof.
  intros m A w junk L H. eapply rwc_rebytes; [| | exact H].
  - cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; exact L.
  - cbn [cells_bytes cbytes app]. reflexivity.
Qed.
Lemma obj_join_8 : forall m A B cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 -> B = (A + Z.of_nat (cells_size cs1))%Z -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] R1] [[W2 B2] R2] ->. split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply bytes_at_app. rewrite (cells_bytes_length cs1 W1). tauto.
  - rewrite cells_size_app, Nat2Z.inj_add. destruct R1 as (R10 & R11 & R12), R2 as (R20 & R21 & R22).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))); [apply R12; lia|].
    replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply R22. lia.
Qed.
Ltac obj_join TOP OBJ :=
  lazymatch type of OBJ with rw_cells _ ?mj ?A ?cs1 => lazymatch type of TOP with rw_cells _ _ ?B ?cs2 =>
    let J := fresh "FRJ" in
    pose proof (obj_join_8 mj A B cs1 cs2 OBJ TOP ltac:(cbn [cells_size csize Nat.add]; repeat match goal with H : _ |- _ => clear H end; lia)) as J;
    cbn [app] in J; clear TOP OBJ; rename J into OBJ end end.

Lemma rwc_hd : forall m A c cs, rw_cells rsegs m A (c :: cs) -> rw_cells rsegs m A [c].
Proof.
  intros m A c cs [[[WF1 WF2] BA] (W0 & W1 & W2)].
  cbn [cells_bytes] in BA. apply bytes_at_app in BA. destruct BA as [BA1 BA2].
  cbn [cells_size] in W1, W2.
  split; [split; [exact (conj WF1 I)|]|].
  - cbn [cells_bytes]. rewrite app_nil_r. exact BA1.
  - cbn [cells_size]. rewrite Nat.add_0_r. split; [lia|]. split; [rewrite Nat2Z.inj_add in W1; lia|].
    intros i Hi. apply W2. rewrite Nat2Z.inj_add. lia.
Qed.
Lemma rwc_CB_split : forall m A n1 n2 j rest, length j = (n1 + n2)%nat ->
  rw_cells rsegs m A (CB (n1 + n2) j :: rest) -> rw_cells rsegs m A (CB n1 (firstn n1 j) :: CB n2 (skipn n1 j) :: rest).
Proof.
  intros m A n1 n2 j rest L H. eapply rwc_rebytes; [| | exact H].
  - destruct H as [[[_ WF] _] _]. cbn. rewrite firstn_length, skipn_length. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. exact WF.
  - cbn [cells_bytes cbytes]. rewrite app_assoc, firstn_skipn. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac kung := cbv delta [kHighMemBeg kDepotNodesBlock kStackStoreBlockBytes kShadowOffset kStackStoreBlockFrames kMaxSize
                        kAsanHeapLeftRedzoneMagic kMaxPrimaryUser kMallocFillByte kAllocBegMagic CHUNK_ALLOCATED].
Ltac eqrefl := lazymatch goal with |- _ = _ => reflexivity end.
Ltac sides1c := first [ eassumption | eqrefl | lia ].
(* [comment removed for export] *)
Ltac sidesc := lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sidesc
  | |- thread_cells _ _ _ _ _ => unfold thread_cells; sidesc
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- bytes_at _ _ _ _ => eassumption
  | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
  | |- _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
  | |- _ = _ => eqrefl
  | |- ?g /\ ?h => tryif has_evar g then (split; sidesc) else tryif has_evar h then (split; sidesc) else first [eassumption | split; sidesc]
  | |- ?g => tryif has_evar g then idtac else sides1c end.
Ltac sides1 ::= first [ eassumption | eqrefl | lia | kung; lia
                      | rewrite ?unsigned_lit by lia; first [eassumption | eqrefl | lia] | modtac ].
Ltac sides ::= lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sides
  | |- thread_cells _ _ _ _ _ => unfold thread_cells; sides
  | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
  | |- _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
  | |- _ /\ _ => first [eassumption | split; sides]
  | |- _ => sides1 end.
Tactic Notation "callx" uconstr(SPEC) "cleaning" tactic(CLEAN) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [eapply SPEC | ]; [> try sidesc .. | idtac]; [> try sides .. | CLEAN; post_call_z segs m ]
  end.
Tactic Notation "callx" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [eapply SPEC | ]; [> try sidesc .. | idtac]; [> try sides .. | post_call_z segs m ]
  end.

Section Pro.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Hypothesis UNW : unwind_stmt.

  #[using="UNW"] Theorem malloc_pro_ok : malloc_pro_stmt.
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. unfold malloc_pro_stmt. intros until Q. cbv zeta.
    intros MI ST LOLE CEIL TPE FPA FPH A0 NR RA0 RANE VLE TOPR BOTR THC CINI CGPS CPS CMCS CFL CFU TTB TDT TUNW TDJ K.
    pose proof alloc_ceiling_val as CV.
    pose proof THC as THC'.
    (first [ dand13 THC as Tini Tkey Ttsd Tctx Tthr Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct THC as (Tini & Tkey & Ttsd & Tctx & Tthr & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]).
    unfold malloc_icpt_entry, alloc_entry, kHighMemBeg, off_th_unwinding in *. unfold TP in TPE. subst tp a0.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    rewrite unsigned_lit in Ttsd, Btp by lia. change (6194136 - 88) with 6194048 in Ttsd. lit_addrs.
    pose proof (munch_refl [(bv_unsigned sp - 2128 - 224, bv_unsigned sp); (thr + 3168, thr + 3168 + 1)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    carve_frame 64%nat ST.
    carve_frame 8%nat ST.       (* [comment removed for export] *)
    carve_frame 2056%nat ST.    (* [comment removed for export] *)
    do 13 amz.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 9 amz. if_false. do 4 amz.
    release_frame FR2 ST (bv_unsigned sp + -2128).
    amz. if_false. (* [comment removed for export] *)
    (* [comment removed for export] *)
    amz. amz. amz. amz. amz.
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with H : rw_cells rsegs mc (bv_unsigned sp + -2128) [C8 ?w; C8 _; CB 2040 ?j] |- _ =>
        apply (obj_split_80h mc (bv_unsigned sp + -2128) w j) in H; [| destruct H as [[WF _] _]; cbn in WF; tauto] end end.
    amz. amz. amz. amz. amz. (* [comment removed for export] *)
    amz. amz. if_true. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. amz. amz. (* [comment removed for export] *)
    amz. amz. amz. amz. amz. (* [comment removed for export] *)
    rewrite (land_ones64_l' (bv_unsigned sp)) by lia.
    amz. (* [comment removed for export] *)
    amz. if_true. (* [comment removed for export] *)
    amz. amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
    pose proof FR as SAV2. do 6 apply rwc_tl in SAV2. apply rwc_ro in SAV2.
    cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.add] in SAV2 || idtac.
    lazymatch type of SAV2 with ro_cells _ _ ?a _ => replace a with (bv_unsigned sp - 16) in SAV2 by lia end.
    replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in FR1 by lia.
    obj_join FR0 FR1. rename FR1 into FR0.
    (* [comment removed for export] *)
    pose proof FR0 as OBJ.
    pose proof (rwc_hd _ _ _ _ OBJ) as O0.
    apply rwc_tl in OBJ. apply rwc_tl in OBJ. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in OBJ.
    pose proof (rwc_hd _ _ _ _ OBJ) as O12. apply rwc_tl in OBJ. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in OBJ.
    lazymatch type of OBJ with rw_cells _ _ _ (CB 2040 ?j :: _) =>
      apply (rwc_CB_split _ _ 16 2024 j) in OBJ; [| destruct OBJ as [[[WFj _] _] _]; exact WFj] end.
    apply rwc_tl in OBJ. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in OBJ.
    pose proof (rwc_hd _ _ _ _ OBJ) as O32. clear OBJ.
    replace (bv_unsigned sp + -2128 + 8 + 4) with (bv_unsigned sp + -2116) in O12 by lia.
    replace (bv_unsigned sp + -2128 + 8 + 4 + 4 + 16) with (bv_unsigned sp + -2096) in O32 by lia.
    callx UNW cleaning (unfold off_th_unwinding in *).
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    match goal with H : context [unwind_depth2 _ _ _] |- _ => rename H into DEP end.
    (* [comment removed for export] *)
    destruct (unwind_depth2 top bot (bv_unsigned sp)) eqn:DD; destruct DEP as [D8 D16].
    (* [comment removed for export] *)
    all: do 4 amz. (* [comment removed for export] *)
    all: carve_frame 16%nat ST.
    all: do 3 amz. (* [comment removed for export] *)
    all: do 8 amz. (* [comment removed for export] *)
    all: lazymatch type of O12 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -2128 + 12) in O12 by (cbn; lia) end.
    all: lazymatch type of O32 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -2128 + 32) in O32 by (cbn; lia) end.
    all: match goal with H : munch _ ?m0 _ |- _ => is_var m0; rename H into MUf; match goal with W : wmono rsegs m0 _ |- _ => rename W into WMf end end.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => match goal with H : mem_inv rsegs mc |- _ => rename H into MIf end end.
    all: eapply K; try eassumption.
    all: split; [assumption| eassumption].
    Unshelve. all: try exact [].
  Qed.
End Pro.

(* [comment removed for export] *)
Definition malloc_epi_entry : Z := 0x3716c.
Definition malloc_epi_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fp lo r : Z)
         (s0w w0 w8 w12 w2056 s5v s4v s3v s2v s1v s0v ra0 : word) (cs16 : list cell) (j32 pad : list byte)
         (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (fp - 2144) -> lo <= fp - 2144 -> 0 <= fp - 2144 -> fp <= 2^47 ->
    sp = wz (fp + -2144) -> a0 = wz r -> 0 < r < 2^64 ->
    rw_cells rsegs m (fp + -2144) [C8 s0w; C8 (wz 0x58c80)] ->
    rw_cells rsegs m (fp + -2128) [C8 w0] -> rw_cells rsegs m (fp + -2120) [C4 w8] -> rw_cells rsegs m (fp + -2116) [C4 w12] ->
    rw_cells rsegs m (fp + -2112) cs16 -> cells_size cs16 = 16%nat -> rw_cells rsegs m (fp + -2096) [CB 2024 j32] ->
    rw_cells rsegs m (fp + -72) [C8 w2056] ->
    rw_cells rsegs m (fp + -64) [CB 8 pad; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    (stk rsegs m lo fp ->
        evt rsegs Q (MS (mkR ra0 (wz fp) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra0) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz malloc_epi_entry) fc None m (seg_rom rsegs)).

Theorem malloc_epi_ok : malloc_epi_stmt.
Proof.
  unfold malloc_epi_stmt. intros until Q. intros MI ST LOLE F0 F1 SP A0 RR AMF O0 O8 O12 O16 S16 O32 O2056 SAV K.
  unfold malloc_epi_entry in *. subst sp a0.
  pose proof (munch_refl [(fp - 2144, fp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  do 10 amz. (* [comment removed for export] *)
  release_frame AMF ST (fp + -2128).
  release_frame O0 ST (fp + -2120).
  release_frame O8 ST (fp + -2116).
  release_frame O12 ST (fp + -2112).
  eapply stk_release in O16; [| exact ST| lia]. clear ST. rename O16 into ST. rewrite S16 in ST.
  lazymatch type of ST with stk _ _ _ ?h => replace h with (fp + -2096) in ST by (cbn; lia) end.
  release_frame O32 ST (fp + -72).
  release_frame O2056 ST (fp + -64).
  release_frame SAV ST fp.
  apply K. exact ST.
Qed.
