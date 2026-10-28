(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mpi_addsub.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MpiClient () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Logic.iff"; "Stdlib.Lists.List.In"; "Stdlib.Lists.List.flat_map"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "set_nth"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "MC.local_ok"; "structs_apart"; "limbs_apart"; "MC.w_blk_ok"; "MC.ex_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "MC.cstate"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "MC.w_ok"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "Corelib.Init.Datatypes.false"; "MC.set_sg"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.MPI_MAX_LIMBS"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.binop_keep"].


(* [comment removed for export] *)
Fixpoint set_nth {A} (i : nat) (l : list A) (x : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: t, O => x :: t
  | h :: t, S k => h :: set_nth k t x
  end.

Lemma nth_error_set_nth_eq {A} : forall i (l : list A) x y, nth_error l i = Some y -> nth_error (set_nth i l x) i = Some x.
Proof. induction i; intros [|h t] x y H; cbn in *; try discriminate; [reflexivity| eauto]. Qed.
Lemma nth_error_set_nth_neq {A} : forall i j (l : list A) x, i <> j -> nth_error (set_nth i l x) j = nth_error l j.
Proof.
  induction i; intros j [|h t] x NE; cbn; [reflexivity| | reflexivity|].
  - destruct j; [congruence| reflexivity].
  - destruct j; [reflexivity|]. cbn. apply IHi. congruence.
Qed.
Lemma In_set_nth {A} : forall i (l : list A) x y, In y (set_nth i l x) -> y = x \/ In y l.
Proof.
  induction i; intros [|h t] x y H; cbn in *; try tauto.
  - destruct H as [<-|H]; [left; reflexivity| right; right; exact H].
  - destruct H as [<-|H]; [right; left; reflexivity|]. destruct (IHi _ _ _ H); [left | right; right]; assumption.
Qed.
Lemma Forall_set_nth {A} (P : A -> Prop) : forall i (l : list A) x y,
  nth_error l i = Some y -> P x -> (forall j z, nth_error l j = Some z -> j <> i -> P z) -> Forall P (set_nth i l x).
Proof.
  induction i; intros [|h t] x y Hy Px Pz; cbn in *; try discriminate.
  - constructor; [exact Px|]. apply Forall_forall. intros z Hz. destruct (In_nth_error _ _ Hz) as [j Hj]. exact (Pz (S j) z Hj ltac:(discriminate)).
  - constructor; [exact (Pz O h eq_refl ltac:(discriminate))|].
    eapply IHi; [exact Hy| exact Px|]. intros j z Hj NE. exact (Pz (S j) z Hj ltac:(congruence)).
Qed.

Definition blk_eq_dec2 (x y : blk) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* [comment removed for export] *)
Definition structs_apart (ls : list mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pi,$0.Pj,$0.Pdi,$1.Pdj,$1.P,(2.(3.$1.)(4.$1.O1.R4.)(5.$1.R2.))P,(2.(3.$1.)(4.$1.O1.R4.)(5.$1.R2.))P,(6.(2.$0.R6.R5.))(7.(8.(9.(:.R5.)+10.)(:.R4.))(8.(9.(:.R4.)+10.)(:.R5.)))")
(* [comment removed for export] *).
Definition limbs_apart (ls : list mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pi,$0.Pj,$0.Pdi,$1.Pdj,$1.P,(2.(3.$1.)(4.$1.O1.R4.)(5.$1.R2.))P,(2.(3.$1.)(4.$1.O1.R4.)(5.$1.R2.))P,(6.(2.$0.R6.R5.))P,(2.$;.(<.R5.)$=.)P,(2.$;.(<.R5.)$=.)(6.(2.$>.(?.R7.)(?.R6.)))")
(* [comment removed for export] *).

Lemma flat_map_blk_in : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pls,(10.$1.)Pb,$11.(12.(13.$11.R1.(14.$1.$11.$15.R2.))(16.$1.Ld,$1.(17.(13.$1.R1.R3.)(17.(2.$;.(<.R1.)$=.)(2.$11.R2.(18.$>.$>.(?.R1.)(19.+4.(1:.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros ls b. rewrite in_flat_map. split.
  - intros (d & Hd & Hb). exists d. unfold mpd_blk in Hb. destruct (md_own d) eqn:O; try (destruct Hb; fail).
    destruct Hb as [<-|[]]. auto.
  - intros (d & Hd & O & ->). exists d. split; [exact Hd|]. unfold mpd_blk. rewrite O. left. reflexivity.
Qed.

Lemma mpd_blk_heap : forall d b, In b (mpd_blk d) -> md_own d = LHeap /\ b = (md_p d, 4 * md_n d).
Proof. intros d b Hb. unfold mpd_blk in Hb. destruct (md_own d); try (destruct Hb; fail). destruct Hb as [<-|[]]. auto. Qed.
Lemma mpd_blk_in : forall d, md_own d = LHeap -> In (md_p d, 4 * md_n d) (mpd_blk d).
Proof. intros d O. unfold mpd_blk. rewrite O. left. reflexivity. Qed.

Lemma set_nth_cases {A} : forall i (ls : list A) (d d' : A) j x, nth_error ls i = Some d ->
  nth_error (set_nth i ls d') j = Some x -> (j = i /\ x = d') \/ (j <> i /\ nth_error ls j = Some x).
Proof.
  intros i ls d d' j x Hi Hj. destruct (Nat.eq_dec j i) as [->|NE].
  - rewrite (nth_error_set_nth_eq i ls d' d Hi) in Hj. injection Hj as <-. left. auto.
  - rewrite (nth_error_set_nth_neq i j ls d' ltac:(congruence)) in Hj. right. auto.
Qed.
Lemma set_nth_blk : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pi,$0.Pls,(10.$1.)Pd,$1.Pd',$1.Pb,$11.P,(2.(3.$1.)(4.$1.R4.R5.)(5.$1.R3.))(12.(13.$11.R2.(14.$1.$11.$15.(1;.$1.R6.R5.R3.)))(7.(13.$11.R2.(15.R3.))(16.$0.Lj,$0.(16.$1.Ldj,$1.(17.(2.(3.$1.)(4.$1.R7.R2.)(5.$1.R1.))(17.(6.(2.$0.R2.R8.))(13.$11.R4.(15.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros i ls d d' b Hi. rewrite in_flat_map. split.
  - intros (x & Hx & Hb). destruct (In_nth_error _ _ Hx) as [j Hj]. destruct (set_nth_cases _ _ _ _ _ _ Hi Hj) as [[-> ->]|[NE Hj']]; [left; exact Hb|].
    right. exists j, x. auto.
  - intros [Hb|(j & dj & Hj & NE & Hb)].
    + exists d'. split; [eapply nth_error_In; exact (nth_error_set_nth_eq i ls d' d Hi)| exact Hb].
    + exists dj. split; [eapply nth_error_In; rewrite (nth_error_set_nth_neq i j ls d' ltac:(congruence)); exact Hj| exact Hb].
Qed.
Lemma In_set_nth_inv {A} : forall i (ls : list A) d d' x, nth_error ls i = Some d -> In x (set_nth i ls d') ->
  x = d' \/ (exists j, nth_error ls j = Some x /\ j <> i).
Proof.
  intros i ls d d' x Hi Hx. destruct (In_nth_error _ _ Hx) as [j Hj]. destruct (set_nth_cases _ _ _ _ _ _ Hi Hj) as [[-> ->]|[NE Hj']]; [left; reflexivity| right; exists j; auto].
Qed.

(* [comment removed for export] *)
Lemma munch_focus : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "PW,(10.$1<.)Pm,P,(1=.&40.)(3.(1=.&8.))Pm',P,(1=.&40.)(3.(1=.&8.))PA,$>.Pn,$>.P,(1>.R5.R4.R3.)P,Px,$>.P,(17.(8.R4.R1.)(1?.R1.(9.R4.R3.)))(20.R8.R2.)(1>.(21.(22.$>.$>.)(18.$>.$>.=R4.)(21.(22.$>.$>.)(18.$>.$>.(9.R4.R3.)(23.+2.+40.))(24.(22.$>.$>.))))R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' A n MU HO x Hx. apply MU. cbn in Hx. destruct Hx as (H1 & H2 & _). apply HO.
  pose proof (bv_unsigned_in_range 64 x). unfold bv_modulus in H. lia.
Qed.
Lemma disjoint_focus : forall A n a k, A <= a -> a + k <= A + n -> disjoint_from [(0, A); (A + n, 2^64)] a k.
Proof. intros. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma mpd_at_munch_pw : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Psegs,(10.$25.)Pm,P,(1=.&40.)(3.(1=.&8.))Pm',P,(1=.&40.)(3.(1=.&8.))PLB,(10.$11.)Pd,$1.PW,(10.$1<.)P,(26.R6.R5.R3.R2.)P,(1>.R2.R6.R5.)P,(27.R8.R7.R6.)P,(28.R9.R8.)P,(28.R:.R8.)P,Px,$>.P,(17.(8.(:.R8.)R1.)(1?.R1.(9.(:.R8.)+10.)))(20.R8.R2.)P,P,(2.$;.(<.R8.)$=.)Px,$>.P,(17.(8.(?.R:.)R1.)(1?.R1.(9.(?.R:.)(19.+4.(1:.R:.)))))(20.R:.R2.)(26.R=.R;.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros segs m m' LB d W [(HR & HAL & HPOS & HL & HN & HO) HS] MU WM MI MI' D1 D2. split; [| exact HS].
  split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
  - eapply rw_cells_transport; [exact HR| apply (munch_focus _ _ _ (md_addr d) 16 MU); exact D1| exact WM| apply disjoint_focus; cbn; lia].
  - destruct (md_own d); [exact HO| |].
    + destruct HO as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      eapply u32arr_transport; [exact H4| apply (munch_focus _ _ _ (md_p d) (4 * md_n d) MU); exact (D2 eq_refl)| exact WM|]. rewrite HL. apply disjoint_focus; lia.
    + destruct HO as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [| exact H5].
      eapply bytes_at_static; [exact MI| exact MI'| exact H4|]. rewrite u32s_length. intros i Hi. apply H5. lia.
Qed.

Lemma outside_of_bounds : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "PW,(10.$1<.)Plo',$>.Phi',$>.Pa,$>.P,(29.(22.$>.$>.)Lw,(22.$>.$>.)(17.(8.R4.(2:.$>.$>.R1.))(8.(2;.$>.$>.R1.)R3.))R4.)P,(7.(1?.R2.R4.)(8.R3.R2.))(20.R6.R3.)")
(* [comment removed for export] *).
Proof.
  induction W as [|[u v] W IH]; cbn; intros lo' hi' a HW Ha; [exact I|].
  inversion HW as [|x l Hx HW']; subst. cbn in Hx. split; [lia| eapply IH; [exact HW'| exact Ha]].
Qed.

Section MC.
  Variable segs : list Segment.
  Variable L : heap_layout.
  Variable HI : heap_iface segs L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP segs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis ROIMG : forall a, 0 <= a < 2^64 -> ro_addr segs (wa a) = true -> hl_img_lo L <= a < hl_img_hi L.

  (* [comment removed for export] *)
  Variables (h0 : HST segs L HI) (LB : list blk) (mo0 : Model) (m0 : mem) (SP lo SPc : Z) (dW0 : mpd) (es : list mpd).
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis LOC : lo <= SPc.
  Hypothesis CSP : SPc <= SP.
  Hypothesis SPT : SP <= heap_top segs L HI h0.
  Hypothesis SPB : SP < 2^64.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis W0NS : md_own dW0 <> LStatic.
  Hypothesis W0WR : mpd_writable L LB SP (heap_top segs L HI h0) dW0.
  Hypothesis W0AS : md_addr dW0 + 16 <= lo \/ SP <= md_addr dW0.
  Hypothesis W0A8 : md_addr dW0 mod 8 = 0.
  Hypothesis W0BLK : md_own dW0 = LHeap -> In (md_p dW0, 4 * md_n dW0) LB /\ 1 <= md_n dW0.
  (* [comment removed for export] *)
  Hypothesis ESF : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "(29.$1.Le,$1.(17.(2<.VL,VLB,Vlo,(:.R1.)+10.)(17.P,(2.$;.(<.R1.)$=.)(13.(22.$>.$>.)(18.$>.$>.(?.R2.)(19.+4.(1:.R2.)))VLB,)(17.(7.(8.(9.(:.R1.)+10.)Vlo,)(8.VSP,(:.R1.)))(17.P,(2.$;.(<.VdW0,)$=.)(7.(8.(9.(:.R2.)+10.)(?.VdW0,))(8.(9.(?.VdW0,)(19.+4.(1:.VdW0,)))(:.R2.)))(17.(7.(6.(2.$;.(<.VdW0,)$=.))(7.(2.$;.(<.R1.)$2=.)(7.(8.(9.(?.VdW0,)(19.+4.(1:.VdW0,)))(?.R1.))(8.(9.(?.R1.)(19.+4.(1:.R1.)))(?.VdW0,)))))(17.(7.(8.(9.(:.VdW0,)+10.)(:.R1.))(8.(9.(:.R1.)+10.)(:.VdW0,)))P,(6.(2.$;.(<.R1.)$2=.))(7.(8.(9.(:.VdW0,)+10.)(?.R2.))(8.(9.(?.R2.)(19.+4.(1:.R2.)))(:.VdW0,)))))))))Ves,)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Set Default Proof Using "HLS DIMG HND IMGC SW ROIMG ACL LOC CSP SPT SPB DHI W0NS W0WR W0AS W0A8 W0BLK ESF".

  Definition local_ok (mq : mem) (LBq : list blk) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "(17.(26.Vsegs,O3.O2.O1.)(17.(6.(2.$;.(<.O1.)$2>.))(17.(8.VSPc,(:.O1.))(17.(8.(9.(:.O1.)+10.)VSP,)(2.$>.(2?.(:.O1.)+8.)=)))))")
(* [comment removed for export] *).

  Definition w_blk_ok (LBq : list blk) (ls : list mpd) (EX : list blk) (dW : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "(17.(2.$>.(:.O1.)(:.VdW0,))(17.(6.(2.$;.(<.O1.)$2>.))(17.(17.(2.(1=.&40.)(30.O1.)(30.VdW0,))(8.(1:.VdW0,)(1:.O1.)))(17.P,(2.$;.(<.O1.)$=.)(17.(6.(13.(22.$>.$>.)(18.$>.$>.(?.O1.)(19.+4.(1:.O1.)))(14.$1.$11.$15.O3.)))(17.(6.(13.(22.$>.$>.)(18.$>.$>.(?.O1.)(19.+4.(1:.O1.)))O2.))(7.(13.(22.$>.$>.)(18.$>.$>.(?.O1.)(19.+4.(1:.O1.)))(15.VdW0,))(6.(13.(22.$>.$>.)(18.$>.$>.(?.O1.)(19.+4.(1:.O1.)))VLB,)))))Pb,$11.P,(13.$11.R1.(15.VdW0,))P,(13.$11.R2.O4.)(7.(2.(10.$11.)(15.O1.)(15.VdW0,))(7.(13.$11.R3.(14.$1.$11.$15.O3.))(13.$11.R3.O2.)))))))")
(* [comment removed for export] *).

  Definition ex_ok (LBq : list blk) (ls : list mpd) (B : blk) : Prop :=
    In B LBq /\ (In B LB -> In B (mpd_blk dW0)) /\ ~ In B (flat_map mpd_blk ls) /\ 0 < snd B.

  Definition cstate (mq : mem) (moq : Model) (hq : HST segs L HI) (LBq : list blk)
      (ls : list mpd) (dW : mpd) (EX : list blk) (CS CX : list (Z * list cell)) : Prop := ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "(17.(31.Vsegs,VL,VHI,O7.O6.O9.O8.)(17.(2.$>.(32.Vsegs,VL,VHI,O7.)(32.Vsegs,VL,VHI,Vh0,))(17.(33.Vmo0,O8.)(17.(29.$1.(34.O9.O6.)O5.)(17.(35.O5.)(17.(36.O5.)(17.(26.Vsegs,O9.O6.O4.)(17.(37.O6.O5.O3.O4.)(17.(29.$11.(38.O6.O5.)O3.)(17.Pb,$11.P,(13.$11.R1.VLB,)P,(6.(13.$11.R2.(15.VdW0,)))(13.$11.R3.O6.)(17.Pb,$11.P,(13.$11.R1.O6.)(7.(13.$11.R2.VLB,)(7.(13.$11.R2.(14.$1.$11.$15.O5.))(7.(13.$11.R2.(15.O4.))(13.$11.R2.O3.))))(17.Pb,$11.P,(13.$11.R1.(14.$1.$11.$15.O5.))P,(13.$11.R2.VLB,)(13.$11.R3.(15.VdW0,))(17.(29.$1.Le,$1.(26.Vsegs,O9.O6.R1.)Ves,)(17.(39.Vsegs,VL,VLB,VSP,(3:.VdW0,)Vm0,O9.)(17.(3;.Vsegs,VL,O9.)(17.(28.Vsegs,O9.)(17.(3<.Vsegs,O9.Vlo,VSPc,)(17.(29.(22.$>.(10.$3=.))Lac,(22.$>.(10.$3=.))(3>.Vsegs,O9.(2:.$>.(10.$3=.)R1.)(2;.$>.(10.$3=.)R1.))O2.)(17.(29.(22.$>.(10.$3=.))Lac,(22.$>.(10.$3=.))(17.(8.VSPc,(2:.$>.(10.$3=.)R1.))(17.(8.(9.(2:.$>.(10.$3=.)R1.)(3?.(40.(2;.$>.(10.$3=.)R1.))))VSP,)Pd,$1.P,(13.$1.R1.O5.)(7.(8.(9.(2:.$>.(10.$3=.)R3.)(3?.(40.(2;.$>.(10.$3=.)R3.))))(:.R2.))(8.(9.(:.R2.)+10.)(2:.$>.(10.$3=.)R3.)))))O2.)(17.(29.(22.$>.(10.$3=.))Lac,(22.$>.(10.$3=.))(3>.Vsegs,O9.(2:.$>.(10.$3=.)R1.)(2;.$>.(10.$3=.)R1.))O1.)(29.(22.$>.(10.$3=.))Lac,(22.$>.(10.$3=.))(16.$11.LB,$11.(17.(13.$11.R1.O3.)(17.(8.(2:.$>.$>.R1.)(2:.$>.(10.$3=.)R2.))(8.(9.(2:.$>.(10.$3=.)R2.)(3?.(40.(2;.$>.(10.$3=.)R2.))))(9.(2:.$>.$>.R1.)(2;.$>.$>.R1.))))))O1.)))))))))))))))))))))")
(* [comment removed for export] *).

  Ltac dest_cs H :=
    destruct H as (HH & HTc & MF & LOK & SA & LA & MW & WOK & EXOK & SUB & COV & FRS & EXT & PX & SOK & MI & ST & CH & CHS & CXH & CXS).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma local_blk_facts : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pd,$1.P,(31.Vsegs,VL,VHI,R3.R2.R5.R4.)P,(26.Vsegs,R6.R3.R2.)P,(2.$;.(<.R3.)$=.)(17.(13.(22.$>.$>.)(18.$>.$>.(?.R4.)(19.+4.(1:.R4.)))R5.)(17.(8.+1.(1:.R4.))(17.(1?.=(?.R4.))(17.(8.(9.(?.R4.)(19.+4.(1:.R4.)))(43.VL,))(7.(8.(9.(?.R4.)(19.+4.(1:.R4.)))(44.VL,))(8.(45.VL,)(?.R4.)))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq d HH [MA _] O. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [BR _].
    exact (mpdr_blk_facts segs L mq LBq d MA O BR).
  Qed.

  Lemma blocks_disjoint : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)PB1,$>.Pk1,$>.PB2,$>.Pk2,$>.P,(31.Vsegs,VL,VHI,R6.R5.R8.R7.)P,(13.(22.$>.$>.)(18.$>.$>.R5.R4.)R6.)P,(13.(22.$>.$>.)(18.$>.$>.R4.R3.)R7.)P,(6.(2.$>.R7.R5.))P,(1?.=R7.)P,(1?.=R6.)(7.(8.(9.R:.R9.)R8.)(8.(9.R8.R7.)R:.))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq B1 k1 B2 k2 HH I1 I2 NE P1 P2. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [_ BA].
    destruct (blocks_apart_neq _ _ _ BA I1 I2 ltac:(intros E; injection E as E1 E2; exact (NE E1)) P1 P2) as [Q|Q]; cbn in Q; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma blocks_eq_or : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pb1,$11.Pb2,$11.P,(31.Vsegs,VL,VHI,R4.R3.R6.R5.)P,(13.$11.R3.R4.)P,(13.$11.R3.R5.)(7.(2.$11.R5.R4.)(6.(2.$>.(2:.$>.$>.R5.)(2:.$>.$>.R4.))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq [B1 k1] [B2 k2] HH I1 I2. destruct (blk_eq_dec2 (B1, k1) (B2, k2)) as [E|NE]; [left; exact E| right]. cbn.
    intros E. exact (nodup_fst_neq _ _ _ _ _ (HND _ _ _ _ HH) I2 I1 NE E).
  Qed.

  (* [comment removed for export] *)
  Lemma mpd_limbs_low : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pd,$1.P,(31.Vsegs,VL,VHI,R3.R2.R5.R4.)P,(26.Vsegs,R6.R3.R2.)P,(6.(2.$;.(<.R3.)$2=.))(17.(1?.=(?.R4.))(8.(9.(?.R4.)(19.+4.(1:.R4.)))(43.VL,)))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq d HH MA NN. destruct (md_own d) eqn:O; [exfalso; exact (NN eq_refl)| |].
    - destruct (local_blk_facts _ _ _ _ _ HH MA O) as (_ & _ & P0 & P4 & _). auto.
    - destruct MA as [(_ & _ & _ & HL & HN & HO) _]. rewrite O in HO. destruct HO as (N1 & _ & P0 & (B0 & BL & _) & RO).
      split; [exact P0|]. rewrite u32s_length in BL.
      pose proof (ROIMG (md_p d + (4 * md_n d - 1)) ltac:(lia) ltac:(apply RO; lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma client_apart_fresh : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)PA,$>.Pn,$>.PB,$>.Pk,$>.P,(31.Vsegs,VL,VHI,R6.R5.R8.R7.)P,Pb,$11.P,(13.$11.R1.VLB,)P,(6.(13.$11.R2.(15.VdW0,)))(13.$11.R3.R9.)P,(2<.VL,VLB,Vlo,R6.R5.)P,(1?.=R6.)P,(13.(22.$>.$>.)(18.$>.$>.R6.R5.)R9.)P,P,(13.(22.$>.$>.)(18.$>.$>.R7.R6.)VLB,)(13.(22.$>.$>.)(18.$>.$>.R8.R7.)(15.VdW0,))P,(1?.=R7.)P,(7.(8.(9.R;.R:.)Vlo,)(8.VSP,R;.))P,P,(2.$;.(<.VdW0,)$=.)(7.(8.(9.R=.R<.)(?.VdW0,))(8.(9.(?.VdW0,)(19.+4.(1:.VdW0,)))R=.))(7.(8.(9.R=.R<.)R;.)(8.(9.R;.R:.)R=.))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq A n B k HH SUB CR Hn IN NIN Hk AS AW.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [BR BA].
    pose proof (proj1 (Forall_forall _ _) BR _ IN) as (B0 & _ & _ & B4 & B5). cbn in B0, B4, B5.
    destruct (Z_lt_le_dec A (B + k)) as [H1|H1]; [| right; lia].
    destruct (Z_lt_le_dec B (A + n)) as [H2|H2]; [| left; lia].
    exfalso. set (a := Z.max A B).
    assert (HX : A <= a < A + n) by (subst a; split; [apply Z.le_max_l| apply Z.max_lub_lt; lia]).
    assert (HY : B <= a < B + k) by (subst a; split; [apply Z.le_max_r| apply Z.max_lub_lt; lia]).
    destruct (CR a HX) as [C|[[C _]|(b & Hb & R)]]; [lia| pose proof DIMG; lia|].
    destruct b as [B' k']. cbn in R.
    assert (NW : ~ In (B', k') (mpd_blk dW0)).
    { intros HW. destruct (mpd_blk_heap _ _ HW) as [O E]. injection E as -> ->. pose proof (AW O). lia. }
    pose proof (SUB _ Hb NW) as Hbq.
    assert (NE : (B', k') <> (B, k)) by (intros E; rewrite E in Hb; rewrite E in NW; exact (NW (NIN Hb))).
    pose proof (proj1 (Forall_forall _ _) BR _ Hbq) as (_ & _ & K2 & _). cbn in K2.
    destruct (Z.eq_dec k' 0) as [->|NZ]; [lia|].
    destruct (blocks_apart_neq _ _ _ BA Hbq IN NE ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mpd_at_heap_presx' : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pm,P,(1=.&40.)(3.(1=.&8.))Pm',P,(1=.&40.)(3.(1=.&8.))PLB0,(10.$11.)PLBp,(10.$11.)PLB',(10.$11.)PSP0,$>.PXI,(10.$1<.)Pd,$1.P,(26.Vsegs,R8.R6.R1.)P,(39.Vsegs,VL,R6.R4.R3.R9.R8.)P,(28.Vsegs,R:.)P,(28.Vsegs,R:.)P,(2<.VL,R9.R7.(:.R5.)+10.)P,P,(2.$;.(<.R6.)$=.)(2<.VL,R;.R9.(?.R7.)(19.+4.(1:.R7.)))P,(46.R8.(:.R7.)+10.)P,P,(2.$;.(<.R8.)$=.)(46.R:.(?.R9.)(19.+4.(1:.R9.)))P,Pb,$11.P,(13.$11.R1.(15.R:.))(13.$11.R2.R>.)(26.Vsegs,R10.R=.R:.)")
(* [comment removed for export] *).
  Proof.
    intros m m' LB0 LBp LB' SP0 XI d [HA HS] HP MI MI' CR CRL D1 D2 HBL. split; [| exact HS].
    destruct HA as (HR & HAL & HPOS & HL & HN & HO).
    split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
    - eapply heap_presx_rw_cells; [exact HP| exact HR| exact CR| exact D1].
    - destruct (md_own d) eqn:EO; [exact HO| |].
      + destruct HO as (H1 & H2 & H3 & [H4 H5]). split; [exact H1|]. split; [apply HBL; unfold mpd_blk; rewrite EO; left; reflexivity|]. split; [exact H3|].
        assert (E4 : Z.of_nat (length (u32s (md_limbs d))) = 4 * md_n d) by (rewrite u32s_length; lia).
        split; [eapply heap_presx_bytes_at; [exact HP| exact H4| rewrite E4; exact (CRL eq_refl)| rewrite E4; exact (D2 eq_refl)]|].
        eapply heap_presx_wr_at; [exact HP| exact H5| rewrite HL; exact (CRL eq_refl)| rewrite HL; exact (D2 eq_refl)].
      + destruct HO as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [| exact H5].
        eapply static_limbs_any_mem; [exact MI| exact MI'| exact H4|]. rewrite u32s_length. intros i Hi. apply H5. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mpd_at_relb : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pm,P,(1=.&40.)(3.(1=.&8.))PLB1,(10.$11.)PLB2,(10.$11.)Pd,$1.P,(26.Vsegs,R4.R3.R1.)P,Pb,$11.P,(13.$11.R1.(15.R3.))(13.$11.R2.R5.)(26.Vsegs,R6.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros m LB1 LB2 d [(HR & HAL & HPOS & HL & HN & HO) HS] HB. split; [| exact HS]. repeat (split; [assumption|]).
    destruct (md_own d) eqn:O; [exact HO| | exact HO]. destruct HO as (N1 & IN & PAL & U32). split; [exact N1|]. split; [| auto].
    apply HB. unfold mpd_blk. rewrite O. left. reflexivity.
  Qed.

  Lemma statics_ok_heap_pres_ : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "PLBp,(10.$11.)PSPp,$>.Pm,P,(1=.&40.)(3.(1=.&8.))Pm',P,(1=.&40.)(3.(1=.&8.))P,(3;.Vsegs,VL,R2.)P,(47.Vsegs,VL,R5.R4.R3.R2.)(3;.Vsegs,VL,R3.)")
(* [comment removed for export] *).
  Proof.
    intros LBp SPp m m' (H0' & H1 & HP) PR. split; [exact H0'|]. split; [exact H1|]. intros a Ha HE.
    destruct (PR a ltac:(lia) ltac:(right; left; split; [exact Ha| intros HS; exact (HE (SW _ HS))])) as [E _].
    rewrite E. exact (HP a Ha HE).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cs_local_facts : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pi,$0.Pd,$1.P,(48.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(2.(3.$1.)(4.$1.R8.R3.)(5.$1.R2.))(17.(26.Vsegs,R=.R:.R3.)(17.(6.(2.$;.(<.R3.)$2>.))(17.(49.VL,R:.VSPc,(32.Vsegs,VL,VHI,R;.)R3.)(17.P,(6.(2.$;.(<.R3.)$2=.))(7.(8.(9.(?.R4.)(19.+4.(1:.R4.)))Vlo,)(8.VSPc,(?.R4.)))(17.(2<.VL,R:.Vlo,(:.R3.)+10.)(17.P,(2.$;.(<.R3.)$=.)(2<.VL,R;.Vlo,(?.R4.)(19.+4.(1:.R4.)))(17.P,(2.$;.(<.R3.)$=.)(17.(1?.=(?.R4.))(17.(8.(9.(?.R4.)(19.+4.(1:.R4.)))(43.VL,))(17.(13.(22.$>.$>.)(18.$>.$>.(?.R4.)(19.+4.(1:.R4.)))R;.)(17.(8.+1.(1:.R4.))P,(13.(22.$>.$>.)(18.$>.$>.(?.R4.)(19.+4.(1:.R4.)))VLB,)(13.(22.$>.$>.)(18.$>.$>.(?.R5.)(19.+4.(1:.R5.)))(15.VdW0,))))))(17.(8.VSPc,(:.R3.))(17.(8.(9.(:.R3.)+10.)VSP,)(2.$>.(2?.(:.R3.)+8.)=))))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX i d CST Hi. dest_cs CST.
    pose proof (proj1 (Forall_forall _ _) LOK d (nth_error_In _ _ Hi)) as (MD & NS & D1 & D2 & D8).
    assert (HF : md_own d = LHeap -> 0 < md_p d /\ md_p d + 4 * md_n d <= alloc_ceiling /\ In (md_p d, 4 * md_n d) LBq /\ 1 <= md_n d /\ (In (md_p d, 4 * md_n d) LB -> In (md_p d, 4 * md_n d) (mpd_blk dW0))).
    { intros O. destruct (local_blk_facts _ _ _ _ _ HH MD O) as (IN & N1 & P0 & P4 & _). repeat (split; [auto|]).
      apply FRS. apply in_flat_map. exists d. split; [eapply nth_error_In; exact Hi| apply mpd_blk_in; exact O]. }
    split; [exact MD|]. split; [exact NS|].
    split. { split; [| split]. - intros a Ha. left. rewrite HTc. lia. - intros a Ha Hd. exfalso. pose proof DIMG. lia. - intros O. destruct (HF O) as (P0 & P4 & _). lia. }
    split. { intros NN. destruct (mpd_limbs_low _ _ _ _ _ HH MD NN). lia. }
    split. { apply client_range_stack. lia. }
    split. { intros O. destruct (HF O) as (_ & _ & IN & _). eapply client_range_blk; [exact IN| lia| lia]. }
    split; [exact HF|]. auto.
  Qed.

  Lemma cs_w_facts : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))P,(48.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(17.(26.Vsegs,R:.R7.R5.)(17.(6.(2.$;.(<.R5.)$2>.))(17.(2.$>.(:.R5.)(:.VdW0,))(17.(49.VL,R7.VSPc,(32.Vsegs,VL,VHI,R8.)R5.)(17.P,(6.(2.$;.(<.R5.)$2=.))(7.(8.(9.(?.R6.)(19.+4.(1:.R6.)))Vlo,)(8.VSPc,(?.R6.)))(17.(2<.VL,R7.Vlo,(:.R5.)+10.)(17.P,(2.$;.(<.R5.)$=.)(2<.VL,R8.Vlo,(?.R6.)(19.+4.(1:.R6.)))(17.P,(2.$;.(<.R5.)$=.)(17.(1?.=(?.R6.))(17.(8.(9.(?.R6.)(19.+4.(1:.R6.)))(43.VL,))(17.(13.(22.$>.$>.)(18.$>.$>.(?.R6.)(19.+4.(1:.R6.)))R8.)(8.+1.(1:.R6.)))))(17.(7.(8.(9.(:.R5.)+10.)Vlo,)(8.VSP,(:.R5.)))(2.$>.(2?.(:.R5.)+8.)=))))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX CST. dest_cs CST.
    destruct WOK as (EA & NS & EP & WB & WK). destruct W0WR as (WW1 & WW2 & WW3).
    assert (HF : md_own dW = LHeap -> 0 < md_p dW /\ md_p dW + 4 * md_n dW <= alloc_ceiling /\ In (md_p dW, 4 * md_n dW) LBq /\ 1 <= md_n dW).
    { intros O. destruct (local_blk_facts _ _ _ _ _ HH MW O) as (IN & N1 & P0 & P4 & _). auto. }
    split; [exact MW|]. split; [exact NS|]. split; [exact EA|].
    split.
    { split; [| split].
      - rewrite EA. intros a Ha. destruct (WW1 a Ha) as [C|[C|([B k] & Hb & R)]]; [left; rewrite HTc; lia| right; left; exact C| right; right].
        exists (B, k). split; [| exact R]. apply SUB; [exact Hb|]. intros HW. destruct (mpd_blk_heap _ _ HW) as [O E]. injection E as -> ->. cbn in R.
        pose proof (WW3 O). lia.
      - rewrite EA. exact WW2.
      - intros O. destruct (HF O) as (P0 & P4 & _). rewrite EA. destruct W0AS; [| lia].
        (* [comment removed for export] *)
        destruct (WB O) as (_ & _ & [OLD|NEW]).
        + destruct (mpd_blk_heap _ _ OLD) as [O0 E]. injection E as E1 E2. rewrite E1, E2. apply WW3. exact O0.
        + eapply (client_apart_fresh mq moq hq LBq (md_addr dW0) 16); [exact HH| exact SUB| | lia| exact (proj1 (proj2 (proj2 (HF O))))| intros C; exfalso; exact (NEW C)| lia| exact W0AS| exact WW3].
          intros a Ha. destruct (WW1 a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
    split. { intros NN. destruct (mpd_limbs_low _ _ _ _ _ HH MW NN). lia. }
    split.
    { rewrite EA. intros a Ha. destruct (WW1 a Ha) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right].
      exists (B, k). split; [| exact R]. apply SUB; [exact Hb|]. intros HW. destruct (mpd_blk_heap _ _ HW) as [O E]. injection E as -> ->. cbn in R.
      pose proof (WW3 O). lia. }
    split. { intros O. destruct (HF O) as (_ & _ & IN & _). eapply client_range_blk; [exact IN| lia| lia]. }
    split; [exact HF|]. rewrite EA. auto.
  Qed.

  Lemma cs_ext_facts : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pe,$1.P,(48.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(13.$1.R2.Ves,)(17.(26.Vsegs,R<.R9.R3.)(17.(2<.VL,R9.Vlo,(:.R3.)+10.)(17.P,(2.$;.(<.R3.)$=.)(2<.VL,R:.Vlo,(?.R4.)(19.+4.(1:.R4.)))(17.P,(6.(2.$;.(<.R3.)$2=.))(7.(8.(9.(?.R4.)(19.+4.(1:.R4.)))Vlo,)(8.VSPc,(?.R4.)))(17.P,(2.$;.(<.R3.)$=.)(17.(1?.=(?.R4.))(17.(13.(22.$>.$>.)(18.$>.$>.(?.R4.)(19.+4.(1:.R4.)))R:.)(17.(13.(22.$>.$>.)(18.$>.$>.(?.R4.)(19.+4.(1:.R4.)))VLB,)(8.+1.(1:.R4.)))))(7.(8.(9.(:.R3.)+10.)Vlo,)(8.VSP,(:.R3.))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX e CST He. dest_cs CST.
    pose proof (proj1 (Forall_forall _ _) EXT e He) as ME. pose proof (proj1 (Forall_forall _ _) ESF e He) as (CRE & INE & ASE & AWS & AWL & AWA & AWE).
    assert (INQ : md_own e = LHeap -> In (md_p e, 4 * md_n e) LBq).
    { intros O. apply SUB; [exact (INE O)|]. intros HW. destruct (mpd_blk_heap _ _ HW) as [O0 E].
      destruct AWL as [C|[C|C]]; [exact (C O0)| congruence|]. injection E as E1 E2.
      destruct (local_blk_facts _ _ _ _ _ HH ME O) as (_ & N1 & _). lia. }
    split; [exact ME|].
    split. { intros a Ha. destruct (CRE a Ha) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right].
             exists (B, k). split; [| exact R]. apply SUB; [exact Hb|]. intros HW. destruct (mpd_blk_heap _ _ HW) as [O E]. injection E as -> ->. cbn in R.
             pose proof (AWS O). lia. }
    split. { intros O. eapply client_range_blk; [exact (INQ O)| lia| lia]. }
    split. { intros NN. destruct (mpd_limbs_low _ _ _ _ _ HH ME NN). lia. }
    split; [| exact ASE]. intros O. destruct (local_blk_facts _ _ _ _ _ HH ME O) as (IN & N1 & P0 & _). auto.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma cs_opnd_sep_ll : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pi,$0.Pj,$0.Pdi,$1.Pdj,$1.P,(48.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(2.(3.$1.)(4.$1.R:.R5.)(5.$1.R3.))P,(2.(3.$1.)(4.$1.R;.R5.)(5.$1.R3.))(17.(4:.R5.R4.)(4;.R5.R4.Vlo,VSPc,))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX i j di dj CST Hi Hj.
    destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST Hi) as (MI_ & NSI & _ & LI & _ & _ & HFI & AI1 & AI2 & _).
    destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST Hj) as (MJ & NSJ & _ & LJ & _ & _ & HFJ & AJ1 & AJ2 & _).
    pose proof CST as CST'. dest_cs CST.
    destruct (Nat.eq_dec i j) as [<-|NE].
    - rewrite Hi in Hj. injection Hj as <-. split; [left; reflexivity|].
      split; [| split; [| split; [left; reflexivity| split; [right; lia|]]]].
      + intros NN. destruct (mpd_limbs_low _ _ _ _ _ HH MI_ NN). lia.
      + intros O. destruct (HFI O). lia.
      + intros NN. destruct (mpd_limbs_low _ _ _ _ _ HH MI_ NN). lia.
    - pose proof (SA _ _ _ _ Hi Hj NE) as AP.
      split; [right; exact AP|].
      split; [| split; [| split; [| split; [right; lia|]]]].
      + intros NN. destruct (mpd_limbs_low _ _ _ _ _ HH MJ NN). lia.
      + intros O. destruct (HFI O). lia.
      + destruct (md_own di) eqn:OI; [right; left; discriminate| | exfalso; exact (NSI eq_refl)].
        destruct (md_own dj) eqn:OJ; [right; right; left; reflexivity| | exfalso; exact (NSJ eq_refl)].
        right; right; right. destruct (HFI eq_refl) as (P0 & P4 & INI & NI1 & _). destruct (HFJ eq_refl) as (Q0 & Q4 & INJ & NJ1 & _).
        exact (blocks_disjoint _ _ _ _ _ _ _ _ HH INI INJ (LA _ _ _ _ Hi Hj NE OI OJ) ltac:(lia) ltac:(lia)).
      + intros NN. destruct (mpd_limbs_low _ _ _ _ _ HH MJ NN). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_opnd_sep_le : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pi,$0.Pdi,$1.Pe,$1.P,(48.R<.R;.R:.R9.R8.R7.R6.R5.R4.)P,(2.(3.$1.)(4.$1.R9.R4.)(5.$1.R3.))P,(13.$1.R3.Ves,)(17.(4:.R5.R4.)(4;.R5.R4.Vlo,VSPc,))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX i di e CST Hi He.
    destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST Hi) as (MI_ & NSI & _ & LI & _ & _ & HFI & AI1 & AI2 & _).
    destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST He) as (ME & CRE' & _ & LE & HFE & ASE).
    pose proof (proj1 (Forall_forall _ _) ESF e He) as (CRE & INE & _ & AWS & AWL & AWA & AWE).
    pose proof CST as CST'. dest_cs CST.
    split; [right; lia|].
    split; [| split; [| split; [| split; [lia|]]]].
    - intros NN. destruct (mpd_limbs_low _ _ _ _ _ HH ME NN). lia.
    - intros O. destruct (HFI O) as (P0 & P4 & IN & N1 & NIN).
      eapply (client_apart_fresh mq moq hq LBq (md_addr e) 16); [exact HH| exact SUB| exact CRE| lia| exact IN| exact NIN| lia| exact ASE| exact AWS].
    - destruct (md_own di) eqn:OI; [right; left; discriminate| | exfalso; exact (NSI eq_refl)].
      destruct (HFI eq_refl) as (P0 & P4 & INI & NI1 & NIN).
      destruct (md_own e) eqn:OE; [right; right; left; reflexivity| |]; right; right; right.
      + destruct (HFE eq_refl) as (Q0 & INQ & INL & NE1).
        assert (NE : md_p di <> md_p e).
        { intros E. destruct (blocks_eq_or _ _ _ _ _ _ HH INI INQ) as [Q|Q]; [| exact (Q E)].
          rewrite Q in NIN. destruct (mpd_blk_heap _ _ (NIN INL)) as [O0 E0]. injection E0 as E1 E2.
          destruct AWL as [C|[C|C]]; [exact (C O0)| congruence| lia]. }
        exact (blocks_disjoint _ _ _ _ _ _ _ _ HH INI INQ NE ltac:(lia) ltac:(lia)).
      + destruct ME as [(_ & _ & _ & HL & HN & HO) _]. rewrite OE in HO. destruct HO as (EN1 & _ & EP0 & (B0 & BL & _) & RO).
        rewrite u32s_length in BL.
        pose proof (ROIMG (md_p e) ltac:(lia) ltac:(replace (md_p e) with (md_p e + 0) by lia; apply RO; lia)).
        pose proof (ROIMG (md_p e + (4 * md_n e - 1)) ltac:(lia) ltac:(apply RO; lia)).
        destruct (local_blk_facts _ _ _ _ _ HH MI_ OI) as (_ & _ & _ & _ & IMG). lia.
    - exact LE.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_opnd_sep_lw : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pi,$0.Pdi,$1.P,(48.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(2.(3.$1.)(4.$1.R8.R3.)(5.$1.R2.))(17.(4:.R3.R8.)(4;.R3.R8.Vlo,VSPc,))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX i di CST Hi.
    destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST Hi) as (MI_ & NSI & _ & LI & _ & _ & HFI & AI1 & AI2 & _).
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (MWf & NSW & EA & _ & LW & _ & _ & HFW & ASW & _).
    pose proof CST as CST'. dest_cs CST. destruct WOK as (_ & _ & _ & WB & WK). destruct W0WR as (WW1 & WW2 & WW3).
    split; [right; lia|].
    split; [| split; [| split; [| split; [lia| exact LW]]]].
    - intros NN. destruct (mpd_limbs_low _ _ _ _ _ HH MW NN). lia.
    - intros O. destruct (HFI O) as (P0 & P4 & IN & N1 & NIN). rewrite EA.
      eapply (client_apart_fresh mq moq hq LBq (md_addr dW0) 16); [exact HH| exact SUB| | lia| exact IN| exact NIN| lia| exact W0AS| exact WW3].
      intros a Ha. destruct (WW1 a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
    - destruct (md_own di) eqn:OI; [right; left; discriminate| | exfalso; exact (NSI eq_refl)].
      destruct (md_own dW) eqn:OW; [right; right; left; reflexivity| | exfalso; exact (NSW eq_refl)].
      right; right; right. destruct (HFI eq_refl) as (P0 & P4 & INI & NI1 & NIN). destruct (HFW eq_refl) as (Q0 & Q4 & INW & NW1).
      destruct (WB eq_refl) as (WNL & _ & _).
      assert (NE : md_p di <> md_p dW).
      { intros E. apply WNL. apply in_flat_map. exists di. split; [eapply nth_error_In; exact Hi|].
        destruct (blocks_eq_or _ _ _ _ _ _ HH INI INW) as [Q|Q]; [| exfalso; exact (Q E)]. rewrite <- Q. apply mpd_blk_in. exact OI. }
      exact (blocks_disjoint _ _ _ _ _ _ _ _ HH INI INW NE ltac:(lia) ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma cs_opnd_sep_wl : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pj,$0.Pdj,$1.P,(48.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(2.(3.$1.)(4.$1.R8.R3.)(5.$1.R2.))(17.(4:.R8.R3.)(4;.R8.R3.Vlo,VSPc,))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX j dj CST Hj.
    destruct (cs_opnd_sep_lw _ _ _ _ _ _ _ _ _ _ _ CST Hj) as [SEP (O1 & O2 & O3 & O4 & O5)].
    destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST Hj) as (MJ & NSJ & _ & LJ & _ & _ & HFJ & AJ1 & AJ2 & _).
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (MWf & NSW & EA & _ & LW & _ & _ & HFW & ASW & _).
    split. { destruct SEP as [E|[E|E]]; [left; symmetry; exact E| right; right; exact E| right; left; exact E]. }
    split; [| split; [| split; [| split; [right; lia| exact LJ]]]].
    - intros NN. destruct (md_own dj) eqn:OJ; [exfalso; exact (NN eq_refl)| exact (O2 eq_refl)| exfalso; exact (NSJ eq_refl)].
    - intros O. exact (O1 ltac:(rewrite O; discriminate)).
    - destruct O3 as [E|[E|[E|E]]].
      + left. symmetry. exact E.
      + right; right; left. destruct (md_own dj) eqn:OJ; [reflexivity| exfalso; exact (E eq_refl)| exfalso; exact (NSJ eq_refl)].
      + right; left. rewrite E. discriminate.
      + right; right; right. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_opnd_sep_we : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pe,$1.P,(48.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(13.$1.R2.Ves,)(17.(4:.R7.R3.)(4;.R7.R3.Vlo,VSPc,))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX e CST He.
    destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST He) as (ME & CRE' & _ & LE & HFE & ASE).
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (MWf & NSW & EA & _ & LW & _ & _ & HFW & ASW & _).
    pose proof (proj1 (Forall_forall _ _) ESF e He) as (CRE & INE & _ & AWS & AWL & AWA & AWE).
    pose proof CST as CST'. dest_cs CST. destruct WOK as (_ & _ & _ & WB & WK).
    split; [right; rewrite EA; lia|].
    split; [| split; [| split; [| split; [exact ASE || lia| exact LE]]]].
    - intros NN. rewrite EA. exact (AWE NN).
    - intros O. destruct (WB O) as (_ & _ & [OLD|NEW]).
      + destruct (mpd_blk_heap _ _ OLD) as [O0 E]. injection E as E1 E2. rewrite E1, E2. apply AWS. exact O0.
      + destruct (HFW O) as (P0 & P4 & INW & NW1).
        eapply (client_apart_fresh mq moq hq LBq (md_addr e) 16); [exact HH| exact SUB| exact CRE| lia| exact INW| intros C; exfalso; exact (NEW C)| lia| exact ASE| exact AWS].
    - destruct (md_own dW) eqn:OW; [right; left; discriminate| | exfalso; exact (NSW eq_refl)].
      destruct (md_own e) eqn:OE; [right; right; left; reflexivity| |]; right; right; right.
      + destruct (HFE eq_refl) as (Q0 & INQ & INL & NE1). destruct (HFW eq_refl) as (P0 & P4 & INW & NW1).
        assert (NE : md_p dW <> md_p e).
        { intros E. destruct (blocks_eq_or _ _ _ _ _ _ HH INW INQ) as [Q|Q]; [| exact (Q E)].
          destruct (WB eq_refl) as (_ & _ & [OLD|NEW]); [| apply NEW; rewrite Q; exact INL].
          destruct (mpd_blk_heap _ _ OLD) as [O0 E0]. injection E0 as E1 E2.
          destruct AWL as [C|[C|C]]; [exact (C O0)| congruence| ]. injection Q as Q1 Q2. lia. }
        exact (blocks_disjoint _ _ _ _ _ _ _ _ HH INW INQ NE ltac:(lia) ltac:(lia)).
      + destruct ME as [(_ & _ & _ & HL & HN & HO) _]. rewrite OE in HO. destruct HO as (EN1 & _ & EP0 & (B0 & BL & _) & RO).
        rewrite u32s_length in BL.
        pose proof (ROIMG (md_p e) ltac:(lia) ltac:(replace (md_p e) with (md_p e + 0) by lia; apply RO; lia)).
        pose proof (ROIMG (md_p e + (4 * md_n e - 1)) ltac:(lia) ltac:(apply RO; lia)).
        destruct (local_blk_facts _ _ _ _ _ HH MW OW) as (_ & _ & _ & _ & IMG). lia.
  Qed.
  Lemma cs_opnd_sep_ww : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))P,(48.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(17.(4:.R5.R5.)(4;.R5.R5.Vlo,VSPc,))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX CST.
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (MWf & NSW & EA & (_ & _ & WR3) & LW & _ & _ & HFW & ASW & _).
    pose proof CST as CST'. dest_cs CST.
    split; [left; reflexivity|].
    split; [| split; [| split; [left; reflexivity| split; [clear -ASW CSP; lia| exact LW]]]].
    - intros NN. destruct (md_own dW) eqn:O; [exfalso; exact (NN eq_refl)| exact (WR3 eq_refl)| exfalso; exact (NSW eq_refl)].
    - exact WR3.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cs_ivs_local : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))PdX,$1.Pi,$0.P,(48.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(2.(3.$1.)(4.$1.R8.R2.)(5.$1.R3.))(17.Pj,$0.Pdj,$1.P,(2.(3.$1.)(4.$1.R;.R2.)(5.$1.R1.))P,(6.(2.$0.R6.R3.))(17.(46.(3:.R8.)(:.R3.)+10.)P,(2.$;.(<.R3.)$=.)(46.(3:.R9.)(?.R4.)(19.+4.(1:.R4.))))(17.(46.(3:.R4.)(:.R8.)+10.)(17.P,(2.$;.(<.R8.)$=.)(46.(3:.R5.)(?.R9.)(19.+4.(1:.R9.)))(17.Pe,$1.P,(13.$1.R1.Ves,)(17.(46.(3:.R6.)(:.R2.)+10.)P,(2.$;.(<.R2.)$=.)(46.(3:.R7.)(?.R3.)(19.+4.(1:.R3.))))(17.PB,$11.P,(13.$11.R1.R8.)(46.(3:.R6.)(2:.$>.$>.R2.)(2;.$>.$>.R2.))(17.Pa,$>.Pk,$>.P,(8.VSPc,R2.)P,(7.(8.(9.R3.R2.)(:.R7.))(8.(9.(:.R7.)+10.)R3.))(46.(3:.R8.)R4.R3.)Pa,$>.P,(17.(8.=R1.)(1?.R1.(23.+2.+40.)))P,(4<.VL,VLB,VSP,R2.)P,(20.(3:.VdW0,)R3.)(17.(4<.VL,R>.VSPc,R4.)(20.(3:.R8.)R4.))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX dX i CST Hi.
    destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST Hi) as (MX & NSX & _ & LX & _ & _ & HFX & X1 & X2 & _).
    pose proof CST as CST'. dest_cs CST. destruct WOK as (EA & NSW & EP & WB & WK). destruct W0WR as (WW1 & WW2 & WW3).
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [BR BA].
    (* [comment removed for export] *)
    assert (XF : md_own dX = LHeap -> In (md_p dX, 4 * md_n dX) LBq /\ 1 <= md_n dX /\ 0 < md_p dX /\ md_p dX + 4 * md_n dX <= alloc_ceiling
              /\ (In (md_p dX, 4 * md_n dX) LB -> In (md_p dX, 4 * md_n dX) (mpd_blk dW0)) /\ In (md_p dX, 4 * md_n dX) (flat_map mpd_blk ls)).
    { intros O. destruct (HFX O) as (P0 & P4 & IN & N1 & NIN). split; [exact IN|]. split; [exact N1|]. split; [exact P0|]. split; [exact P4|]. split; [exact NIN|].
      apply in_flat_map. exists dX. split; [eapply nth_error_In; exact Hi| apply mpd_blk_in; exact O]. }
    (* [comment removed for export] *)
    assert (IVS : forall a k, (a + k <= md_addr dX \/ md_addr dX + 16 <= a) ->
              (md_own dX = LHeap -> a + k <= md_p dX \/ md_p dX + 4 * md_n dX <= a) -> disjoint_from (mpd_ivs dX) a k).
    { intros a k H1 H2. unfold mpd_ivs. cbn. split; [exact H1|]. destruct (md_own dX) eqn:O; cbn; [exact I| split; [exact (H2 eq_refl)| exact I]| exfalso; exact (NSX eq_refl)]. }
    split.
    { intros j dj Hj NE. destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST' Hj) as (MJ & NSJ & _ & LJ & _ & _ & HFJ & J1 & J2 & _).
      split.
      - apply IVS; [pose proof (SA _ _ _ _ Hi Hj NE); lia| intros O; destruct (XF O); lia].
      - intros OJ. destruct (HFJ OJ) as (Q0 & Q4 & INJ & NJ1 & _). apply IVS; [lia|]. intros O. destruct (XF O) as (INX & NX1 & _).
        pose proof (blocks_disjoint _ _ _ _ _ _ _ _ HH INX INJ (LA _ _ _ _ Hi Hj NE O OJ) ltac:(lia) ltac:(lia)); lia. }
    split.
    { apply IVS; [rewrite EA; destruct W0AS; lia|]. intros O. destruct (XF O) as (INX & NX1 & PX0 & PX4 & NIN & _). rewrite EA.
      eapply (client_apart_fresh mq moq hq LBq (md_addr dW0) 16); [exact HH| exact SUB| | lia| exact INX| exact NIN| lia| exact W0AS| exact WW3].
      intros a Ha. destruct (WW1 a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
    split.
    { intros OW. destruct (local_blk_facts _ _ _ _ _ HH MW OW) as (INW & NW1 & PW0 & PW4 & _). apply IVS; [lia|].
      intros O. destruct (XF O) as (INX & NX1 & _ & _ & _ & INF). destruct (WB OW) as (WNL & _ & _).
      assert (NE : md_p dX <> md_p dW).
      { intros E. apply WNL. destruct (blocks_eq_or _ _ _ _ _ _ HH INX INW) as [Q|Q]; [rewrite <- Q; exact INF| exfalso; exact (Q E)]. }
      pose proof (blocks_disjoint _ _ _ _ _ _ _ _ HH INX INW NE ltac:(lia) ltac:(lia)); lia. }
    split.
    { intros e He. destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST' He) as (ME & _ & _ & LE & HFE & ASE).
      pose proof (proj1 (Forall_forall _ _) ESF e He) as (CRE & INE & _ & AWS & AWL & AWA & AWE).
      split.
      - apply IVS; [lia|]. intros O. destruct (XF O) as (INX & NX1 & PX0 & PX4 & NIN & _).
        eapply (client_apart_fresh mq moq hq LBq (md_addr e) 16); [exact HH| exact SUB| exact CRE| lia| exact INX| exact NIN| lia| exact ASE| exact AWS].
      - intros OE. destruct (HFE OE) as (Q0 & INQ & INL & N1). destruct (local_blk_facts _ _ _ _ _ HH ME OE) as (_ & _ & _ & Q4 & _). apply IVS; [lia|].
        intros O. destruct (XF O) as (INX & NX1 & _ & _ & NIN & _).
        assert (NE : md_p dX <> md_p e).
        { intros E. destruct (blocks_eq_or _ _ _ _ _ _ HH INX INQ) as [Q|Q]; [| exact (Q E)].
          rewrite Q in NIN. destruct (mpd_blk_heap _ _ (NIN INL)) as [O0 E0]. injection E0 as E1 E2.
          destruct AWL as [C|[C|C]]; [exact (C O0)| congruence| lia]. }
        pose proof (blocks_disjoint _ _ _ _ _ _ _ _ HH INX INQ NE ltac:(lia) ltac:(lia)); lia. }
    split.
    { intros [B k] HB. pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & NLB & NLOC & KP). cbn in KP |- *.
      pose proof (proj1 (Forall_forall _ _) BR _ INB) as (B0 & _ & _ & B4 & _). cbn in B0, B4.
      apply IVS; [lia|]. intros O. destruct (XF O) as (INX & NX1 & _ & _ & _ & INF).
      assert (NE : md_p dX <> B).
      { intros E. apply NLOC. destruct (blocks_eq_or _ _ _ _ _ _ HH INX INB) as [Q|Q]; [rewrite <- Q; exact INF| exfalso; exact (Q E)]. }
      pose proof (blocks_disjoint _ _ _ _ _ _ _ _ HH INX INB NE ltac:(lia) KP); lia. }
    split.
    { intros a k Ha AP. apply IVS; [exact AP|]. intros O. destruct (XF O). lia. }
    intros a Ha Hc Ho. split.
    - destruct Hc as [C|[C|(b & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists b; split; [apply SUB; [exact Hb|]| exact R]].
      intros HW. destruct (mpd_blk_heap _ _ HW) as [O0 E]. subst b. unfold mpd_ivs in Ho. rewrite O0 in Ho. cbn in Ho, R. lia.
    - unfold mpd_ivs. cbn. split.
      + destruct Hc as [C|[[C _]|([B k] & Hb & R)]]; [lia| pose proof DIMG; lia|]. cbn in R.
        assert (Hbq : In (B, k) LBq).
        { apply SUB; [exact Hb|]. intros HW. destruct (mpd_blk_heap _ _ HW) as [O0 E]. injection E as -> ->. unfold mpd_ivs in Ho. rewrite O0 in Ho. cbn in Ho. lia. }
        pose proof (proj1 (Forall_forall _ _) BR _ Hbq) as (_ & _ & _ & B4 & _). cbn in B4. lia.
      + destruct (md_own dX) eqn:O; cbn; [exact I| | exfalso; exact (NSX eq_refl)]. split; [| exact I].
        destruct (XF eq_refl) as (IN & N1 & P0 & P4 & NIN & _). destruct (local_blk_facts _ _ _ _ _ HH MX O) as (_ & _ & _ & _ & P5).
        destruct Hc as [C|[[C _]|([B k] & Hb & R)]]; [lia| pose proof DIMG; lia|]. cbn in R.
        assert (Hbq : In (B, k) LBq).
        { apply SUB; [exact Hb|]. intros HW. destruct (mpd_blk_heap _ _ HW) as [O0 E]. injection E as -> ->. unfold mpd_ivs in Ho. rewrite O0 in Ho. cbn in Ho. lia. }
        assert (NE : (B, k) <> (md_p dX, 4 * md_n dX)).
        { intros E; rewrite E in Hb. destruct (mpd_blk_heap _ _ (NIN Hb)) as [O0 E0]. injection E0 as E1 E2.
          unfold mpd_ivs in Ho. rewrite O0 in Ho. cbn in Ho. injection E as E3 E4. lia. }
        pose proof (proj1 (Forall_forall _ _) BR _ Hbq) as (_ & _ & K2 & _). cbn in K2.
        destruct (Z.eq_dec k 0) as [->|NZ]; [lia|].
        destruct (blocks_apart_neq _ _ _ BA Hbq IN NE ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia.
  Qed.
  Lemma cs_ivs_w : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))P,(48.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(17.Pj,$0.Pdj,$1.P,(2.(3.$1.)(4.$1.R8.R2.)(5.$1.R1.))(17.(46.(3:.R8.)(:.R2.)+10.)P,(2.$;.(<.R2.)$=.)(46.(3:.R9.)(?.R3.)(19.+4.(1:.R3.))))(17.Pe,$1.P,(13.$1.R1.Ves,)(17.(46.(3:.R7.)(:.R2.)+10.)P,(2.$;.(<.R2.)$=.)(46.(3:.R8.)(?.R3.)(19.+4.(1:.R3.))))(17.PB,$11.P,(13.$11.R1.R5.)(46.(3:.R7.)(2:.$>.$>.R2.)(2;.$>.$>.R2.))(17.Pa,$>.Pk,$>.P,(8.VSPc,R2.)P,(8.(9.R3.R2.)VSP,)(46.(3:.R9.)R4.R3.)Pa,$>.P,(17.(8.=R1.)(1?.R1.(23.+2.+40.)))P,(4<.VL,VLB,VSP,R2.)P,(20.(3:.VdW0,)R3.)(17.(4<.VL,R;.VSPc,R4.)(20.(3:.R9.)R4.))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX CST.
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (MWf & NSW & EA & (WR1 & WR2 & WR3) & LW & _ & _ & HFW & ASW & _).
    pose proof CST as CST'. dest_cs CST. destruct WOK as (_ & _ & EP & WB & WK). destruct W0WR as (WW1 & WW2 & WW3).
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [BR BA].
    assert (IVS : forall a k, (a + k <= md_addr dW \/ md_addr dW + 16 <= a) ->
              (md_own dW = LHeap -> a + k <= md_p dW \/ md_p dW + 4 * md_n dW <= a) -> disjoint_from (mpd_ivs dW) a k).
    { intros a k H1 H2. unfold mpd_ivs. cbn. split; [exact H1|]. destruct (md_own dW) eqn:O; cbn; [exact I| split; [exact (H2 eq_refl)| exact I]| exfalso; exact (NSW eq_refl)]. }
    split.
    { intros j dj Hj. destruct (cs_opnd_sep_lw _ _ _ _ _ _ _ _ _ _ _ CST' Hj) as [SEP (O1 & O2 & O3 & O4 & O5)].
      destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST' Hj) as (MJ & NSJ & _ & LJ & _ & _ & HFJ & J1 & J2 & _).
      split.
      - apply IVS; [rewrite EA; destruct W0AS; lia| intros O; destruct (HFW O); lia].
      - intros OJ. destruct (HFJ OJ) as (Q0 & Q4 & INJ & NJ1 & _). apply IVS; [rewrite EA; destruct W0AS; lia|].
        intros OW. destruct O3 as [E|[E|[E|E]]]; [| exfalso; exact (E OJ)| congruence| lia].
        exfalso. subst dj. lia. }
    split.
    { intros e He. destruct (cs_opnd_sep_we _ _ _ _ _ _ _ _ _ _ CST' He) as [SEP (O1 & O2 & O3 & O4 & O5)].
      destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST' He) as (ME & _ & _ & LE & HFE & ASE).
      pose proof (proj1 (Forall_forall _ _) ESF e He) as (CRE & INE & _ & AWS & AWL & AWA & AWE).
      split.
      - apply IVS; [rewrite EA; lia| exact O2].
      - intros OE. apply IVS; [pose proof (O1 ltac:(rewrite OE; discriminate)); lia|].
        intros OW. destruct O3 as [E|[E|[E|E]]]; [| exfalso; exact (E OW)| congruence| lia].
        exfalso. subst e. rewrite EA in AWA. lia. }
    split.
    { intros [B k] HB. pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & NLB & NLOC & KP). cbn in KP |- *.
      pose proof (proj1 (Forall_forall _ _) BR _ INB) as (B0 & _ & _ & B4 & _). cbn in B0, B4.
      apply IVS.
      - rewrite EA. destruct W0AS as [C|C]; [| lia].
        enough (md_addr dW0 + 16 <= B \/ B + k <= md_addr dW0) by lia.
        eapply (client_apart_fresh mq moq hq LBq (md_addr dW0) 16); [exact HH| exact SUB| | lia| exact INB| exact NLB| exact KP| exact W0AS| exact WW3].
        intros a Ha. destruct (WW1 a Ha) as [X|[X|X]]; [left; lia| right; left; exact X| right; right; exact X].
      - intros O. destruct (HFW O) as (P0 & P4 & INW & NW1). destruct (WB O) as (_ & WNE & _).
        assert (NE : md_p dW <> B).
        { intros E. apply WNE. destruct (blocks_eq_or _ _ _ _ _ _ HH INW INB) as [Q|Q]; [rewrite Q; exact HB| exfalso; exact (Q E)]. }
        pose proof (blocks_disjoint _ _ _ _ _ _ _ _ HH INW INB NE ltac:(lia) KP). lia. }
    split.
    { intros a k Ha Hk. apply IVS; [rewrite EA; destruct W0AS; lia| intros O; destruct (HFW O); lia]. }
    intros a Ha Hc Ho. unfold mpd_ivs in Ho. rewrite <- EA in Ho. cbn in Ho. destruct Ho as [Ho1 Ho2]. split.
    - destruct Hc as [C|[C|(b & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists b; split; [apply SUB; [exact Hb|]| exact R]].
      intros HW. destruct (mpd_blk_heap _ _ HW) as [O0 E]. subst b. rewrite O0 in Ho2. cbn in Ho2, R. lia.
    - unfold mpd_ivs. cbn. split; [exact Ho1|].
      destruct (md_own dW) eqn:O; cbn; [exact I| | exfalso; exact (NSW eq_refl)]. split; [| exact I].
      destruct (HFW eq_refl) as (P0 & P4 & INW & NW1). destruct (local_blk_facts _ _ _ _ _ HH MW O) as (_ & _ & _ & _ & P5).
      destruct (WB eq_refl) as (_ & _ & [OLD|NEW]).
      + destruct (mpd_blk_heap _ _ OLD) as [O0 E]. injection E as E1 E2. rewrite O0 in Ho2. cbn in Ho2. rewrite E1, E2. lia.
      + destruct Hc as [C|[[C _]|([B k] & Hb & R)]]; [lia| pose proof DIMG; lia|]. cbn in R.
        assert (Hbq : In (B, k) LBq).
        { apply SUB; [exact Hb|]. intros HW. destruct (mpd_blk_heap _ _ HW) as [O0 E]. injection E as -> ->. rewrite O0 in Ho2. cbn in Ho2. lia. }
        assert (NE : (B, k) <> (md_p dW, 4 * md_n dW)) by (intros E; rewrite E in Hb; exact (NEW Hb)).
        pose proof (proj1 (Forall_forall _ _) BR _ Hbq) as (_ & _ & K2 & _). cbn in K2.
        destruct (Z.eq_dec k 0) as [->|NZ]; [lia|].
        destruct (blocks_apart_neq _ _ _ BA Hbq INW NE ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cs_binop_l : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pi,$0.PdX,$1.Pm2,P,(1=.&40.)(3.(1=.&8.))Pmo2,$41.Ph2,(42.Vsegs,VL,VHI,)PLB2,(10.$11.)PdX',$1.P,(48.R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(2.(3.$1.)(4.$1.R=.R8.)(5.$1.R7.))P,(31.Vsegs,VL,VHI,R5.R4.R7.R6.)P,(2.$>.(32.Vsegs,VL,VHI,R6.)(32.Vsegs,VL,VHI,R11.))P,(33.R13.R8.)P,(26.Vsegs,R:.R7.R6.)P,(4=.R13.R<.R8.R7.)P,(39.Vsegs,VL,R14.VSPc,(3:.R=.)R17.R<.)P,(3;.Vsegs,VL,R=.)P,(28.Vsegs,R>.)P,(3<.Vsegs,R?.Vlo,VSPc,)P,Pb,$11.P,(13.$11.R1.(15.R=.))(7.(13.$11.R2.(15.R13.))(6.(13.$11.R2.R1:.)))(48.R11.R10.R?.R>.(1;.$1.R13.R18.R=.)R17.R16.R15.R14.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX i dX m2 mo2 h2 LB2 dX' CST Hi HH2 HT2 MF2 MA2 OUT PX2 SOK2 MI2 ST2 FRESH.
    destruct (cs_ivs_local _ _ _ _ _ _ _ _ _ _ _ CST Hi) as (IVL & IVW1 & IVW2 & IVE & IVX & IVC & IVP).
    destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST Hi) as (MX & NSX & _ & LX & CRX & CRXL & HFX & X1 & X2 & XA8).
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (MWf & NSW & EA & _ & LW & CRW & CRWL & HFW & ASW & WA8).
    pose proof CST as CST'. dest_cs CST. destruct WOK as (_ & _ & EP & WB & WK).
    pose proof OUT as (EAX & NS & K1 & K2 & K3).
    pose proof (nth_error_In _ _ Hi) as INX.
    pose proof (HND _ _ _ _ HH) as NDq. pose proof (HND _ _ _ _ HH2) as ND2.
    assert (XB : forall b, In b (mpd_blk dX) -> In b (flat_map mpd_blk ls)) by (intros b Hb; apply in_flat_map; exists dX; split; [exact INX| exact Hb]).
    (* [comment removed for export] *)
    assert (KEEPJ : forall j dj, nth_error ls j = Some dj -> j <> i -> forall b, In b (mpd_blk dj) -> In b LB2).
    { intros j dj Hj NE b Hb. destruct (mpd_blk_heap _ _ Hb) as [OJ ->].
      pose proof (proj1 (Forall_forall _ _) LOK dj (nth_error_In _ _ Hj)) as (MJ & _).
      apply K2; [exact (proj1 (local_blk_facts _ _ _ _ _ HH MJ OJ))|].
      intros HX. destruct (mpd_blk_heap _ _ HX) as [OX E]. injection E as E1 E2. exact (LA _ _ _ _ Hj Hi NE OJ OX E1). }
    assert (KEEPW : forall b, In b (mpd_blk dW) -> In b LB2).
    { intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [OW ->]. apply K2; [exact (proj1 (local_blk_facts _ _ _ _ _ HH MW OW))|].
      intros HX. apply (proj1 (WB OW)). exact (XB _ HX). }
    assert (KEEPE : forall B, In B EX -> In B LB2).
    { intros B HB. pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & NLB & NLOC & KP). apply K2; [exact INB|].
      intros HX. apply NLOC. exact (XB _ HX). }
    assert (SUB2 : forall b, In b LB -> ~ In b (mpd_blk dW0) -> In b LB2).
    { intros b Hb NW. apply K2; [exact (SUB b Hb NW)|]. intros C. exact (NW (FRS _ (XB _ C) Hb)). }
    (* [comment removed for export] *)
    assert (NEWX : forall b, In b (mpd_blk dX') -> ~ In b LBq ->
              (forall j dj, nth_error ls j = Some dj -> j <> i -> ~ In b (mpd_blk dj)) /\ ~ In b (mpd_blk dW) /\ ~ In b EX
              /\ (In b LB -> In b (mpd_blk dW0))).
    { intros b Hb NQ.
      split. { intros j dj Hj NE Hbj. destruct (mpd_blk_heap _ _ Hbj) as [OJ ->].
               pose proof (proj1 (Forall_forall _ _) LOK dj (nth_error_In _ _ Hj)) as (MJ & _). exact (NQ (proj1 (local_blk_facts _ _ _ _ _ HH MJ OJ))). }
      split. { intros HbW. destruct (mpd_blk_heap _ _ HbW) as [OW ->]. exact (NQ (proj1 (local_blk_facts _ _ _ _ _ HH MW OW))). }
      split. { intros HB. pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & _). exact (NQ INB). }
      intros HL. destruct (in_dec blk_eq_dec2 b (mpd_blk dW0)) as [Y|N]; [exact Y|]. exfalso. exact (NQ (SUB _ HL N)). }
    split; [exact HH2|]. split; [rewrite HT2; exact HTc|]. split; [eapply mo_frame_trans; [exact MF| exact MF2]|].
    split.
    { (* [comment removed for export] *)
      eapply Forall_set_nth; [exact Hi| |].
      - split; [exact MA2|]. split; [exact NS|]. rewrite EAX. auto.
      - intros j dj Hj NE. pose proof (proj1 (Forall_forall _ _) LOK dj (nth_error_In _ _ Hj)) as (MJ & NSJ & J1 & J2 & JA8).
        split; [| auto]. destruct (IVL _ _ Hj ltac:(congruence)) as [D1 D2].
        eapply mpd_at_heap_presx'; [exact MJ| exact PX2| exact MI| exact MI2| apply client_range_stack; lia| | exact D1| exact D2| exact (KEEPJ _ _ Hj NE)].
        intros O. eapply client_range_blk; [exact (proj1 (local_blk_facts _ _ _ _ _ HH MJ O))| lia| lia]. }
    split.
    { (* [comment removed for export] *)
      intros a b da db Ha Hb NE.
      destruct (set_nth_cases _ _ _ _ _ _ Hi Ha) as [[-> ->]|[NA Ha']]; destruct (set_nth_cases _ _ _ _ _ _ Hi Hb) as [[-> ->]|[NB Hb']]; [congruence| | |].
      - rewrite EAX. exact (SA _ _ _ _ Hi Hb' ltac:(congruence)).
      - rewrite EAX. exact (SA _ _ _ _ Ha' Hi ltac:(congruence)).
      - exact (SA _ _ _ _ Ha' Hb' NE). }
    split.
    { (* [comment removed for export] *)
      assert (NEWAP : forall j dj, nth_error ls j = Some dj -> j <> i -> md_own dX' = LHeap -> md_own dj = LHeap -> md_p dX' <> md_p dj).
      { intros j dj Hj NE OX' OJ E.
        pose proof (proj1 (Forall_forall _ _) LOK dj (nth_error_In _ _ Hj)) as (MJ & _).
        destruct (local_blk_facts _ _ _ _ _ HH MJ OJ) as (INJ & NJ1 & _).
        destruct (local_blk_facts _ _ _ _ _ HH2 MA2 OX') as (INX' & NX1 & _).
        pose proof (KEEPJ _ _ Hj NE _ (mpd_blk_in _ OJ)) as INJ2.
        destruct (FRESH _ (mpd_blk_in _ OX')) as [OLD|NEW].
        - destruct (mpd_blk_heap _ _ OLD) as [OX EE]. injection EE as P1 P2. apply (LA _ _ _ _ Hi Hj ltac:(congruence) OX OJ). congruence.
        - destruct (blk_eq_dec2 (md_p dX', 4 * md_n dX') (md_p dj, 4 * md_n dj)) as [Q|Q]; [apply NEW; rewrite Q; exact INJ|].
          exact (nodup_fst_neq _ _ _ _ _ ND2 INJ2 INX' Q E). }
      intros a b da db Ha Hb NE Oa Ob.
      destruct (set_nth_cases _ _ _ _ _ _ Hi Ha) as [[-> ->]|[NA Ha']]; destruct (set_nth_cases _ _ _ _ _ _ Hi Hb) as [[-> ->]|[NB Hb']]; [congruence| | |].
      - exact (NEWAP _ _ Hb' ltac:(congruence) Oa Ob).
      - intros E. exact (NEWAP _ _ Ha' ltac:(congruence) Ob Oa (eq_sym E)).
      - exact (LA _ _ _ _ Ha' Hb' NE Oa Ob). }
    split.
    { (* [comment removed for export] *)
      destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST') as (_ & _ & _ & (WR1 & _ & _) & _).
      eapply mpd_at_heap_presx'; [exact MW| exact PX2| exact MI| exact MI2| | | exact IVW1| exact IVW2| exact KEEPW].
      - intros a Ha. destruct (WR1 a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
      - intros O. eapply client_range_blk; [exact (proj1 (local_blk_facts _ _ _ _ _ HH MW O))| lia| lia]. }
    split.
    { (* [comment removed for export] *)
      split; [exact EA|]. split; [exact NSW|]. split; [exact EP|]. split.
      - intros OW. destruct (WB OW) as (WNL & WNE & WOR). split; [| split; [exact WNE| exact WOR]].
        intros HIn. apply (proj1 (set_nth_blk _ _ _ _ _ Hi)) in HIn. destruct HIn as [HbX'|(j & dj & Hj & NE & Hbj)].
        + destruct (FRESH _ HbX') as [OLD|NEW]; [apply WNL; exact (XB _ OLD)|].
          exact (NEW (proj1 (local_blk_facts _ _ _ _ _ HH MW OW))).
        + apply WNL. apply in_flat_map. exists dj. split; [eapply nth_error_In; exact Hj| exact Hbj].
      - intros b Hb0 Hb2. destruct (K1 b Hb2) as [Hbq|HbX'].
        + destruct (WK b Hb0 Hbq) as [E|[Hl|He]]; [left; exact E| right; left| right; right; exact He].
          apply in_flat_map in Hl. destruct Hl as (x & Hx & Hbx). destruct (In_nth_error _ _ Hx) as [j Hj].
          destruct (Nat.eq_dec j i) as [->|NE].
          * rewrite Hi in Hj. injection Hj as ->. apply (proj2 (set_nth_blk _ _ _ _ _ Hi)). left. rewrite (K3 b Hbx Hb2). exact Hbx.
          * apply (proj2 (set_nth_blk _ _ _ _ _ Hi)). right. exists j, x. auto.
        + right; left. apply (proj2 (set_nth_blk _ _ _ _ _ Hi)). left. exact HbX'. }
    split.
    { (* [comment removed for export] *)
      apply Forall_forall. intros B HB. pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & NLB & NLOC & KP).
      split; [exact (KEEPE _ HB)|]. split; [exact NLB|]. split; [| exact KP].
      intros HIn. apply (proj1 (set_nth_blk _ _ _ _ _ Hi)) in HIn. destruct HIn as [HbX'|(j & dj & Hj & NE & Hbj)].
      - destruct (FRESH _ HbX') as [OLD|NEW]; [apply NLOC; exact (XB _ OLD)| exact (NEW INB)].
      - apply NLOC. apply in_flat_map. exists dj. split; [eapply nth_error_In; exact Hj| exact Hbj]. }
    split; [exact SUB2|].
    split.
    { (* [comment removed for export] *)
      intros b Hb. destruct (K1 b Hb) as [Hq|Hn].
      - destruct (COV b Hq) as [Hl|[Hf|[Hw|He]]]; [left; exact Hl| right; left| right; right; left; exact Hw| right; right; right; exact He].
        apply in_flat_map in Hf. destruct Hf as (d & Hd & Hbd). destruct (In_nth_error _ _ Hd) as [j Hj].
        destruct (Nat.eq_dec j i) as [->|NE].
        + rewrite Hi in Hj. injection Hj as ->. apply (proj2 (set_nth_blk _ _ _ _ _ Hi)). left. rewrite (K3 b Hbd Hb). exact Hbd.
        + apply (proj2 (set_nth_blk _ _ _ _ _ Hi)). right. exists j, d. auto.
      - right; left. apply (proj2 (set_nth_blk _ _ _ _ _ Hi)). left. exact Hn. }
    split.
    { (* [comment removed for export] *)
      intros b Hb HL. apply (proj1 (set_nth_blk _ _ _ _ _ Hi)) in Hb. destruct Hb as [HbX'|(j & dj & Hj & NE & Hbj)].
      - destruct (FRESH _ HbX') as [OLD|NEW]; [exact (FRS _ (XB _ OLD) HL)|].
        exact (proj2 (proj2 (proj2 (NEWX _ HbX' NEW))) HL).
      - apply FRS; [| exact HL]. apply in_flat_map. exists dj. split; [eapply nth_error_In; exact Hj| exact Hbj]. }
    split.
    { (* [comment removed for export] *)
      apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) EXT e He) as ME.
      destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST' He) as (_ & CRE & CREL & _ & HFE & ASE).
      destruct (IVE _ He) as [D1 D2].
      eapply mpd_at_heap_presx'; [exact ME| exact PX2| exact MI| exact MI2| | | exact D1| exact D2|].
      { intros a Ha. destruct (CRE a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
      { intros O. destruct (HFE O) as (_ & INQ & _). eapply client_range_blk; [exact INQ| lia| lia]. }
      intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [OE ->]. destruct (HFE OE) as (_ & INQ & INL & _).
      apply K2; [exact INQ|]. intros HX. pose proof (FRS _ (XB _ HX) INL) as HW0.
      destruct (mpd_blk_heap _ _ HW0) as [O0 E0]. injection E0 as E1 E2.
      pose proof (proj1 (Forall_forall _ _) ESF e He) as (_ & _ & _ & _ & AWL & _).
      destruct (HFE OE) as (_ & _ & _ & NE1). destruct AWL as [C|[C|C]]; [exact (C O0)| congruence| lia]. }
    split.
    { (* [comment removed for export] *)
      eapply heap_presx_trans; [exact PX|]. intros a Ha Hc Ho. destruct (IVP a Ha Hc Ho) as [C1 O1]. exact (PX2 a Ha C1 O1). }
    split; [exact SOK2|]. split; [exact MI2|]. split; [exact ST2|].
    split.
    { (* [comment removed for export] *)
      apply Forall_forall. intros [a cs] Hac. pose proof (proj1 (Forall_forall _ _) CH _ Hac) as R. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as (B1 & B2 & B3). cbn in R, B1, B2, B3 |- *.
      eapply heap_presx_rw_cells; [exact PX2| exact R| apply client_range_stack; lia|].
      apply IVC; [exact B1| exact (B3 dX INX)]. }
    split.
    { apply Forall_forall. intros ac Hac. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as (B1 & B2 & B3).
      split; [exact B1|]. split; [exact B2|]. intros d Hd. destruct (In_set_nth_inv _ _ _ _ _ Hi Hd) as [->|(j & Hj & NE)]; [rewrite EAX; exact (B3 dX INX)| exact (B3 d (nth_error_In _ _ Hj))]. }
    split.
    { (* [comment removed for export] *)
      apply Forall_forall. intros [a cs] Hac. pose proof (proj1 (Forall_forall _ _) CXH _ Hac) as R. pose proof (proj1 (Forall_forall _ _) CXS _ Hac) as (B & HB & B1 & B2). cbn in R, B1, B2 |- *.
      pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & NLB & NLOC & KP).
      destruct (heap_blocks _ _ HI _ _ _ _ HH) as [BR _]. pose proof (proj1 (Forall_forall _ _) BR _ INB) as (B0 & _ & _ & B4 & _).
      eapply heap_presx_rw_cells; [exact PX2| exact R| |].
      - destruct B as [B0' k']. cbn in B1, B2 |- *. eapply client_range_blk; [exact INB| lia| lia].
      - eapply disjoint_from_sub; [exact (IVX _ HB)| lia| lia]. }
    apply Forall_forall. intros ac Hac. exact (proj1 (Forall_forall _ _) CXS _ Hac).
  Qed.

  (* [comment removed for export] *)
  Lemma cs_binop_w : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pm2,P,(1=.&40.)(3.(1=.&8.))Pmo2,$41.Ph2,(42.Vsegs,VL,VHI,)PLB2,(10.$11.)PdW',$1.P,(48.R>.R=.R<.R;.R:.R9.R8.R7.R6.)P,(31.Vsegs,VL,VHI,R4.R3.R6.R5.)P,(2.$>.(32.Vsegs,VL,VHI,R5.)(32.Vsegs,VL,VHI,R>.))P,(33.R10.R7.)P,(26.Vsegs,R9.R6.R5.)P,(4=.R10.R>.R7.R6.)P,(39.Vsegs,VL,R11.VSPc,(3:.R?.)R14.R;.)P,(3;.Vsegs,VL,R<.)P,(28.Vsegs,R=.)P,(3<.Vsegs,R>.Vlo,VSPc,)P,Pb,$11.P,(13.$11.R1.(15.R<.))(7.(13.$11.R2.(15.R15.))(6.(13.$11.R2.R17.)))P,(2.(1=.&40.)(30.R<.)(30.R14.))P,(8.(1:.R15.)(1:.R=.))(48.R12.R11.R10.R?.R17.R>.R15.R14.R13.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX m2 mo2 h2 LB2 dW' CST HH2 HT2 MF2 MA2 OUT PX2 SOK2 MI2 ST2 FRESH PAD NLE.
    destruct (cs_ivs_w _ _ _ _ _ _ _ _ _ CST) as (IVL & IVE & IVX & IVC & IVP).
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (MWf & NSW & EA & _ & LW & CRW & CRWL & HFW & ASW & WA8).
    pose proof CST as CST'. dest_cs CST. destruct WOK as (_ & _ & [EP EN] & WB & WK).
    pose proof OUT as (EAX & NS & K1 & K2 & K3).
    pose proof (HND _ _ _ _ HH) as NDq. pose proof (HND _ _ _ _ HH2) as ND2.
    (* [comment removed for export] *)
    assert (WNL : forall b, In b (mpd_blk dW) -> ~ In b (flat_map mpd_blk ls)).
    { intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [OW ->]. exact (proj1 (WB OW)). }
    assert (WNE : forall b, In b (mpd_blk dW) -> ~ In b EX).
    { intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [OW ->]. exact (proj1 (proj2 (WB OW))). }
    assert (WLB : forall b, In b (mpd_blk dW) -> In b LB -> In b (mpd_blk dW0)).
    { intros b Hb HL. destruct (mpd_blk_heap _ _ Hb) as [OW ->]. destruct (proj2 (proj2 (WB OW))) as [Y|N]; [exact Y| exfalso; exact (N HL)]. }
    assert (KEEPJ : forall j dj, nth_error ls j = Some dj -> forall b, In b (mpd_blk dj) -> In b LB2).
    { intros j dj Hj b Hb. destruct (mpd_blk_heap _ _ Hb) as [OJ ->].
      pose proof (proj1 (Forall_forall _ _) LOK dj (nth_error_In _ _ Hj)) as (MJ & _).
      apply K2; [exact (proj1 (local_blk_facts _ _ _ _ _ HH MJ OJ))|].
      intros HW. apply (WNL _ HW). apply in_flat_map. exists dj. split; [eapply nth_error_In; exact Hj| apply mpd_blk_in; exact OJ]. }
    assert (KEEPE : forall B, In B EX -> In B LB2).
    { intros B HB. pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & _). apply K2; [exact INB|]. intros HW. exact (WNE _ HW HB). }
    assert (SUB2 : forall b, In b LB -> ~ In b (mpd_blk dW0) -> In b LB2).
    { intros b Hb NW. apply K2; [exact (SUB b Hb NW)|]. intros HW. exact (NW (WLB _ HW Hb)). }
    split; [exact HH2|]. split; [rewrite HT2; exact HTc|]. split; [eapply mo_frame_trans; [exact MF| exact MF2]|].
    split.
    { (* [comment removed for export] *)
      apply Forall_forall. intros dj Hdj. destruct (In_nth_error _ _ Hdj) as [j Hj].
      pose proof (proj1 (Forall_forall _ _) LOK dj Hdj) as (MJ & NSJ & J1 & J2 & JA8).
      split; [| auto]. destruct (IVL _ _ Hj) as [D1 D2].
      eapply mpd_at_heap_presx'; [exact MJ| exact PX2| exact MI| exact MI2| apply client_range_stack; lia| | exact D1| exact D2| exact (KEEPJ _ _ Hj)].
      intros O. eapply client_range_blk; [exact (proj1 (local_blk_facts _ _ _ _ _ HH MJ O))| lia| lia]. }
    split; [exact SA|]. split; [exact LA|].
    split; [exact MA2|].
    split.
    { (* [comment removed for export] *)
      split; [rewrite EAX; exact EA|]. split; [exact NS|]. split; [split; [rewrite PAD; exact EP| lia]|]. split.
      - intros OW'. pose proof (mpd_blk_in _ OW') as HbW'.
        destruct (FRESH _ HbW') as [OLD|NEW].
        + split; [exact (WNL _ OLD)|]. split; [exact (WNE _ OLD)|].
          destruct (in_dec blk_eq_dec2 (md_p dW', 4 * md_n dW') LB) as [HL|HNL]; [left; exact (WLB _ OLD HL)| right; exact HNL].
        + split.
          { intros Hl. apply in_flat_map in Hl. destruct Hl as (x & Hx & Hbx). destruct (mpd_blk_heap _ _ Hbx) as [OX E].
            pose proof (proj1 (Forall_forall _ _) LOK x Hx) as (MX & _). apply NEW. rewrite E. exact (proj1 (local_blk_facts _ _ _ _ _ HH MX OX)). }
          split. { intros HE. pose proof (proj1 (Forall_forall _ _) EXOK _ HE) as (INB & _). exact (NEW INB). }
          destruct (in_dec blk_eq_dec2 (md_p dW', 4 * md_n dW') (mpd_blk dW0)) as [Y|N]; [left; exact Y| right].
          intros HL. exact (NEW (SUB _ HL N)).
      - intros b Hb0 Hb2. destruct (K1 b Hb2) as [Hbq|HbW'].
        + destruct (WK b Hb0 Hbq) as [E|[Hl|He]]; [| right; left; exact Hl| right; right; exact He].
          left. rewrite <- E. apply (K3 b); [rewrite E; exact Hb0| exact Hb2].
        + left. destruct (mpd_blk_heap _ _ HbW') as [OW' ->]. destruct (mpd_blk_heap _ _ Hb0) as [O0 E0].
          unfold mpd_blk. rewrite OW', O0. rewrite E0. reflexivity. }
    split.
    { (* [comment removed for export] *)
      apply Forall_forall. intros B HB. pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & NLB & NLOC & KP).
      split; [exact (KEEPE _ HB)|]. split; [exact NLB|]. split; [exact NLOC| exact KP]. }
    split; [exact SUB2|].
    split.
    { (* [comment removed for export] *)
      intros b Hb. destruct (K1 b Hb) as [Hq|Hn]; [| right; right; left; exact Hn].
      destruct (COV b Hq) as [Hl|[Hf|[Hw|He]]]; [left; exact Hl| right; left; exact Hf| | right; right; right; exact He].
      right; right; left. rewrite (K3 b Hw Hb). exact Hw. }
    split; [exact FRS|].
    split.
    { (* [comment removed for export] *)
      apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) EXT e He) as ME.
      destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST' He) as (_ & CRE & CREL & _ & HFE & ASE).
      destruct (IVE _ He) as [D1 D2].
      eapply mpd_at_heap_presx'; [exact ME| exact PX2| exact MI| exact MI2| | | exact D1| exact D2|].
      { intros a Ha. destruct (CRE a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
      { intros O. destruct (HFE O) as (_ & INQ & _). eapply client_range_blk; [exact INQ| lia| lia]. }
      intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [OE ->]. destruct (HFE OE) as (_ & INQ & INL & NE1).
      apply K2; [exact INQ|]. intros HW. pose proof (WLB _ HW INL) as HW0.
      destruct (mpd_blk_heap _ _ HW0) as [O0 E0]. injection E0 as E1 E2.
      pose proof (proj1 (Forall_forall _ _) ESF e He) as (_ & _ & _ & _ & AWL & _).
      destruct AWL as [C|[C|C]]; [exact (C O0)| congruence| lia]. }
    split.
    { eapply heap_presx_trans; [exact PX|]. intros a Ha Hc Ho. destruct (IVP a Ha Hc Ho) as [C1 O1]. exact (PX2 a Ha C1 O1). }
    split; [exact SOK2|]. split; [exact MI2|]. split; [exact ST2|].
    split.
    { apply Forall_forall. intros [a cs] Hac. pose proof (proj1 (Forall_forall _ _) CH _ Hac) as R. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as (B1 & B2 & B3). cbn in R, B1, B2, B3 |- *.
      eapply heap_presx_rw_cells; [exact PX2| exact R| apply client_range_stack; lia|]. apply IVC; [exact B1| exact B2]. }
    split; [exact CHS|].
    split.
    { apply Forall_forall. intros [a cs] Hac. pose proof (proj1 (Forall_forall _ _) CXH _ Hac) as R. pose proof (proj1 (Forall_forall _ _) CXS _ Hac) as (B & HB & B1 & B2). cbn in R, B1, B2 |- *.
      pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & NLB & NLOC & KP).
      pose proof (IVX _ HB) as D. destruct B as [B0' k']. cbn in B1, B2, D, KP |- *.
      eapply heap_presx_rw_cells; [exact PX2| exact R| eapply client_range_blk; [exact INB| lia| lia]| eapply disjoint_from_sub; [exact D| lia| lia]]. }
    exact CXS.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition w_ok (ls : list mpd) (li : option nat) (wl ex : bool) (dW : mpd) (EX : list blk) (w : ivl) : Prop := ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "(7.(17.(8.Vlo,(2:.$>.$>.O1.))(8.(2;.$>.$>.O1.)VSPc,))(7.(16.$0.Li,$0.(16.$1.Ld,$1.(17.(2.(3.$0.)O6.(5.$0.R2.))(17.(2.(3.$1.)(4.$1.O7.R2.)(5.$1.R1.))(17.(2.$;.(<.R1.)$=.)(17.(8.(?.R1.)(2:.$>.$>.O1.))(8.(2;.$>.$>.O1.)(9.(?.R1.)(19.+4.(1:.R1.))))))))))(7.(17.(2.$4>.O5.$4?.)(17.(2.$;.(<.O3.)$=.)(17.(8.(?.O3.)(2:.$>.$>.O1.))(8.(2;.$>.$>.O1.)(9.(?.O3.)(19.+4.(1:.O3.)))))))(17.(2.$4>.O4.$4?.)(16.$11.LB,$11.(17.(13.$11.R1.O2.)(17.(8.(2:.$>.$>.R1.)(2:.$>.$>.O1.))(8.(2;.$>.$>.O1.)(9.(2:.$>.$>.R1.)(2;.$>.$>.R1.))))))))))")
(* [comment removed for export] *).

  Lemma w_inside : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pls,(10.$1.)Pli,(3.$0.)Pwl,$4>.Pex,$4>.PdW,$1.PEX,(10.$11.)PW,(10.$1<.)Pa,$>.P,(29.$1<.(50.R8.R7.R6.R5.R4.R3.)R2.)P,(6.(20.R3.R2.))(7.(17.(8.Vlo,R3.)(1?.R3.VSPc,))(7.(16.$0.Li,$0.(16.$1.Ld,$1.(17.(2.(3.$0.)R;.(5.$0.R2.))(17.(2.(3.$1.)(4.$1.R<.R2.)(5.$1.R1.))(17.(2.$;.(<.R1.)$=.)(17.(8.(?.R1.)R5.)(1?.R5.(9.(?.R1.)(19.+4.(1:.R1.))))))))))(7.(17.(2.$4>.R8.$4?.)(17.(2.$;.(<.R6.)$=.)(17.(8.(?.R6.)R3.)(1?.R3.(9.(?.R6.)(19.+4.(1:.R6.)))))))(17.(2.$4>.R7.$4?.)(16.$11.LB,$11.(17.(13.$11.R1.R6.)(17.(8.(2:.$>.$>.R1.)R4.)(1?.R4.(9.(2:.$>.$>.R1.)(2;.$>.$>.R1.))))))))))")
(* [comment removed for export] *).
  Proof.
    intros ls li wl ex dW EX W a WOK. induction W as [|[u v] W IH]; cbn; intros NO; [exfalso; exact (NO I)|].
    inversion WOK as [|x l Hx WOK']; subst.
    destruct (Z_le_gt_dec u a) as [C1|C1]; [destruct (Z_lt_le_dec a v) as [C2|C2]|].
    - destruct Hx as [[A1 A2]|[(i & d & H1 & H2 & H3 & H4 & H5)|[(H1 & H2 & H3 & H4)|(H0 & B & H1 & H2 & H3)]]]; cbn [fst snd] in *;
        [left; lia| right; left; exists i, d; repeat split; try assumption; lia| right; right; left; repeat split; try assumption; lia| right; right; right; split; [exact H0| exists B; repeat split; try assumption; lia]].
    - apply (IH WOK'). intros O. apply NO. split; [lia| exact O].
    - apply (IH WOK'). intros O. apply NO. split; [lia| exact O].
  Qed.

  Lemma cs_munch : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pli,(3.$0.)Pwl,$4>.Pex,$4>.PW,(10.$1<.)Pm2,P,(1=.&40.)(3.(1=.&8.))Pls',(10.$1.)PdW',$1.PCX',(10.(22.$>.(10.$3=.)))P,(48.R11.R10.R?.R>.R=.R<.R;.R:.R9.)P,(1>.R6.R12.R5.)P,(27.Vsegs,R13.R6.)P,(28.Vsegs,R7.)P,(3<.Vsegs,R8.Vlo,VSPc,)P,(29.$1<.(50.R12.R=.R<.R;.R11.R10.)R:.)P,(2.$0.(51.$1.R9.)(51.$1.R13.))P,Pj,$0.Pd,$1.Pd',$1.P,(2.(3.$1.)(4.$1.R17.R3.)(5.$1.R2.))P,(2.(3.$1.)(4.$1.R>.R4.)(5.$1.R2.))(17.(2.$>.(:.R3.)(:.R4.))(17.(2.$>.(52.R3.)(52.R4.))(17.(2.$>.(1:.R3.)(1:.R4.))(17.(2.$>.(?.R3.)(?.R4.))(17.(2.(1=.&40.)(30.R3.)(30.R4.))(17.(2.$;.(<.R3.)(<.R4.))(17.P,(6.(17.(2.(3.$0.)R14.(5.$0.R5.))(2.$;.(<.R4.)$=.)))(2.$1.R4.R5.)P,(2.(3.$0.)R14.(5.$0.R5.))P,(2.$;.(<.R5.)$=.)(17.(53.Vsegs,R12.(?.R6.)(54.R5.))(2.$>.(3?.(51.(1=.&40.)(54.R5.)))(1:.R6.))))))))))P,(17.(2.$>.(:.R:.)(:.R14.))(17.(2.$>.(52.R:.)(52.R14.))(17.(2.$>.(1:.R:.)(1:.R14.))(17.(2.$>.(?.R:.)(?.R14.))(17.(2.(1=.&40.)(30.R:.)(30.R14.))(17.(2.$;.(<.R:.)(<.R14.))(17.P,(6.(17.(2.$4>.R?.$4?.)(2.$;.(<.R14.)$=.)))(2.$1.R;.R15.)P,(2.$4>.R?.$4?.)P,(2.$;.(<.R15.)$=.)(17.(53.Vsegs,R>.(?.R16.)(54.R<.))(2.$>.(3?.(51.(1=.&40.)(54.R<.)))(1:.R16.))))))))))P,P,(2.$4>.R?.$55.)(2.(10.(22.$>.(10.$3=.)))R;.R13.)P,P,(2.$4>.R10.$4?.)(17.(29.(22.$>.(10.$3=.))Lac,(22.$>.(10.$3=.))(3>.Vsegs,R10.(2:.$>.(10.$3=.)R1.)(2;.$>.(10.$3=.)R1.))R<.)(29.(22.$>.(10.$3=.))Lac,(22.$>.(10.$3=.))(16.$11.LB,$11.(17.(13.$11.R1.R18.)(17.(8.(2:.$>.$>.R1.)(2:.$>.(10.$3=.)R2.))(8.(9.(2:.$>.(10.$3=.)R2.)(3?.(40.(2;.$>.(10.$3=.)R2.))))(9.(2:.$>.$>.R1.)(2;.$>.$>.R1.))))))R<.))(48.R?.R1;.R1:.R19.R>.R=.R16.R15.R<.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX li wl ex W m2 ls' dW' CX' CST MU WM MI2 ST2 WOK' LEN REL RELW CXF CXT.
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (MWf & NSW & EA & _ & LW & CRW & CRWL & HFW & ASW & WA8).
    pose proof CST as CST'. dest_cs CST. destruct WOK as (_ & _ & EPN & WB & WK).
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [BR BA].
    assert (LOCF : forall i d, nth_error ls i = Some d -> local_ok mq LBq d) by (intros i d Hd; exact (proj1 (Forall_forall _ _) LOK d (nth_error_In _ _ Hd))).
    (* [comment removed for export] *)
    assert (WIN : forall a, ~ outside W a ->
              (lo <= a < SPc)
              \/ (exists i d, li = Some i /\ nth_error ls i = Some d /\ md_own d = LHeap /\ md_p d <= a < md_p d + 4 * md_n d /\ In (md_p d, 4 * md_n d) LBq)
              \/ (wl = true /\ md_own dW = LHeap /\ md_p dW <= a < md_p dW + 4 * md_n dW /\ In (md_p dW, 4 * md_n dW) LBq)
              \/ (ex = true /\ exists B, In B EX /\ fst B <= a < fst B + snd B /\ In B LBq)).
    { intros a NO. destruct (w_inside _ _ _ _ _ _ _ _ WOK' NO) as [H|[(i & d & H1 & H2 & H3 & H4)|[(H1 & H2 & H3)|(H1 & B & H2 & H3)]]]; [left; exact H| right; left| right; right; left| right; right; right].
      - exists i, d. repeat (split; [assumption|]). exact (proj1 (local_blk_facts _ _ _ _ _ HH (proj1 (LOCF _ _ H2)) H3)).
      - repeat (split; [assumption|]). exact (proj1 (local_blk_facts _ _ _ _ _ HH MW H2)).
      - split; [exact H1|]. exists B. repeat (split; [assumption|]). exact (proj1 (proj1 (Forall_forall _ _) EXOK _ H2)). }
    (* [comment removed for export] *)
    assert (BLO : forall B k a, In (B, k) LBq -> B <= a < B + k -> a < alloc_ceiling).
    { intros B k a IN Ha. pose proof (proj1 (Forall_forall _ _) BR _ IN) as (_ & _ & _ & B4 & _). cbn in B4. lia. }
    assert (OUTS : forall a, SPc <= a -> outside W a).
    { intros a Ha. destruct (outside_dec W a) as [Y|NO]; [exact Y|]. exfalso.
      destruct (WIN a NO) as [H|[(i & d & _ & _ & _ & H4 & IN)|[(_ & _ & H3 & IN)|(_ & [B k] & _ & H3 & IN)]]]; [lia| | |];
        [pose proof (BLO _ _ _ IN H4)| pose proof (BLO _ _ _ IN H3)| cbn in H3; pose proof (BLO _ _ _ IN H3)]; lia. }
    assert (OUTD : forall a, a < lo -> alloc_ceiling <= a -> outside W a).
    { intros a Ha Hc. destruct (outside_dec W a) as [Y|NO]; [exact Y|]. exfalso.
      destruct (WIN a NO) as [H|[(i & d & _ & _ & _ & H4 & IN)|[(_ & _ & H3 & IN)|(_ & [B k] & _ & H3 & IN)]]]; [lia| | |];
        [pose proof (BLO _ _ _ IN H4)| pose proof (BLO _ _ _ IN H3)| cbn in H3; pose proof (BLO _ _ _ IN H3)]; lia. }
    assert (OUTBLK : forall B k a, In (B, k) LBq -> 0 < k -> B <= a < B + k ->
              (forall i d, li = Some i -> nth_error ls i = Some d -> md_own d = LHeap -> (md_p d, 4 * md_n d) <> (B, k)) ->
              (wl = true -> md_own dW = LHeap -> (md_p dW, 4 * md_n dW) <> (B, k)) ->
              (ex = true -> ~ In (B, k) EX) ->
              outside W a).
    { intros B k a IN Hk Ha N1 N2 N3. destruct (outside_dec W a) as [Y|NO]; [exact Y|]. exfalso.
      pose proof (BLO _ _ _ IN Ha) as AL.
      assert (DISJ : forall B' k', In (B', k') LBq -> (B', k') <> (B, k) -> 0 < k' -> B' <= a < B' + k' -> False).
      { intros B' k' IN' NE Hk' Ha'. destruct (blocks_apart_neq _ _ _ BA IN' IN NE ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia. }
      destruct (WIN a NO) as [H|[(i & d & H1 & H2 & H3 & H4 & IN')|[(H1 & H2 & H3 & IN')|(H1 & [B' k'] & H2 & H3 & IN')]]]; [lia| | |].
      - exact (DISJ _ _ IN' (N1 _ _ H1 H2 H3) ltac:(lia) H4).
      - exact (DISJ _ _ IN' (N2 H1 H2) ltac:(lia) H3).
      - cbn in H3. destruct (blk_eq_dec2 (B', k') (B, k)) as [E|NE]; [apply (N3 H1); rewrite <- E; exact H2|]. exact (DISJ _ _ IN' NE ltac:(lia) H3). }
    (* [comment removed for export] *)
    assert (PAIR : forall j d', nth_error ls' j = Some d' -> exists d, nth_error ls j = Some d).
    { intros j d' Hj'. destruct (nth_error ls j) as [d|] eqn:Hj; [exists d; reflexivity|].
      exfalso. apply nth_error_None in Hj. rewrite <- LEN in Hj. apply (proj2 (nth_error_None _ _)) in Hj. congruence. }
    assert (PAIR' : forall j d, nth_error ls j = Some d -> exists d', nth_error ls' j = Some d').
    { intros j d Hj. destruct (nth_error ls' j) as [d'|] eqn:Hj'; [exists d'; reflexivity|].
      exfalso. apply nth_error_None in Hj'. rewrite LEN in Hj'. apply (proj2 (nth_error_None _ _)) in Hj'. congruence. }
    assert (FLD : forall j d', nth_error ls' j = Some d' -> exists d, nth_error ls j = Some d /\ md_addr d' = md_addr d /\ md_own d' = md_own d /\ md_p d' = md_p d /\ md_n d' = md_n d).
    { intros j d' Hj'. destruct (PAIR _ _ Hj') as [d Hj]. exists d. destruct (REL _ _ _ Hj Hj') as (E1 & E2 & E3 & E4 & E5 & E6 & _). auto 10. }
    assert (BLK : forall b, In b (flat_map mpd_blk ls') <-> In b (flat_map mpd_blk ls)).
    { intros b. rewrite !flat_map_blk_in. split; intros (d & Hd & O & ->).
      - destruct (In_nth_error _ _ Hd) as [j Hj']. destruct (FLD _ _ Hj') as (d0 & Hj & E1 & EO & EP & EN).
        exists d0. split; [eapply nth_error_In; exact Hj|]. rewrite <- EO, EP, EN. auto.
      - destruct (In_nth_error _ _ Hd) as [j Hj]. destruct (PAIR' _ _ Hj) as [d' Hj']. destruct (FLD _ _ Hj') as (d0 & Hj0 & E1 & EO & EP & EN).
        rewrite Hj in Hj0. injection Hj0 as <-. exists d'. split; [eapply nth_error_In; exact Hj'|]. rewrite EO, EP, EN. auto. }
    destruct RELW as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WSAME & WNEW).
    assert (BLKW : mpd_blk dW' = mpd_blk dW) by (unfold mpd_blk; rewrite WE6, WE4, WE3; reflexivity).
    (* [comment removed for export] *)
    assert (OSTR_L : forall j d a, nth_error ls j = Some d -> md_addr d <= a < md_addr d + 16 -> outside W a).
    { intros j d a Hj Ha. destruct (LOCF _ _ Hj) as (_ & _ & A1 & _). apply OUTS. lia. }
    assert (OSTR_W : forall a, md_addr dW <= a < md_addr dW + 16 -> outside W a).
    { intros a Ha. destruct ASW as [C|C]; [| apply OUTS; lia].
      destruct (outside_dec W a) as [Y|NO]; [exact Y|]. exfalso.
      destruct (WIN a NO) as [H|[(i & d & H1 & H2 & H3 & H4 & IN')|[(H1 & H2 & H3 & IN')|(H1 & [B' k'] & H2 & H3 & IN')]]]; [lia| | |].
      - destruct (cs_opnd_sep_lw _ _ _ _ _ _ _ _ _ _ _ CST' H2) as [_ (_ & O2 & _)]. pose proof (O2 H3). lia.
      - destruct (HFW H2) as (_ & _ & _ & _). destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST') as (_ & _ & _ & (_ & _ & WR3) & _). pose proof (WR3 H2). lia.
      - cbn in H3. destruct (cs_ivs_w _ _ _ _ _ _ _ _ _ CST') as (_ & _ & IVX & _). pose proof (IVX _ H2) as D. unfold mpd_ivs in D. cbn in D. destruct D as [D _]. lia. }
    (* [comment removed for export] *)
    assert (E_BLK : forall e, In e es -> md_own e = LHeap -> In (md_p e, 4 * md_n e) LB /\ In (md_p e, 4 * md_n e) LBq /\ ~ In (md_p e, 4 * md_n e) (mpd_blk dW0) /\ 1 <= md_n e).
    { intros e He OE. destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST' He) as (_ & _ & _ & _ & HFE & _). destruct (HFE OE) as (_ & INQ & INL & NE1).
      split; [exact INL|]. split; [exact INQ|]. split; [| exact NE1]. intros HW0. destruct (mpd_blk_heap _ _ HW0) as [O0 E0]. injection E0 as E1 E2.
      pose proof (proj1 (Forall_forall _ _) ESF e He) as (_ & _ & _ & _ & AWL & _). destruct AWL as [C|[C|C]]; [exact (C O0)| congruence| lia]. }
    assert (LI_NE : forall i d b, li = Some i -> nth_error ls i = Some d -> md_own d = LHeap -> In b LB -> ~ In b (mpd_blk dW0) -> (md_p d, 4 * md_n d) <> b).
    { intros i d b Hli Hd Od Hb NW E. subst b. apply NW. apply FRS; [| exact Hb]. apply in_flat_map. exists d. split; [eapply nth_error_In; exact Hd| apply mpd_blk_in; exact Od]. }
    assert (W_NE : forall b, In b LB -> ~ In b (mpd_blk dW0) -> md_own dW = LHeap -> (md_p dW, 4 * md_n dW) <> b).
    { intros b Hb NW OW E. subst b. destruct (proj2 (proj2 (WB OW))) as [Y|N]; [exact (NW Y)| exact (N Hb)]. }
    assert (EX_NE : forall b, In b LB -> ~ In b (mpd_blk dW0) -> ~ In b EX).
    { intros b Hb NW HE. pose proof (proj1 (Forall_forall _ _) EXOK _ HE) as (_ & NLB & _). exact (NW (NLB Hb)). }
    assert (OUT_LB : forall B k a, In (B, k) LB -> ~ In (B, k) (mpd_blk dW0) -> B <= a < B + k -> outside W a).
    { intros B k a Hb NW Ha. pose proof (SUB _ Hb NW) as Hbq. pose proof (proj1 (Forall_forall _ _) BR _ Hbq) as (_ & _ & K2 & _). cbn in K2.
      eapply OUTBLK; [exact Hbq| lia| exact Ha| intros i d Hli Hd Od; exact (LI_NE _ _ _ Hli Hd Od Hb NW)| intros _ OW; exact (W_NE _ Hb NW OW)| intros _; exact (EX_NE _ Hb NW)]. }
    (* [comment removed for export] *)
    assert (OUTIMG : forall a, hl_img_lo L <= a < hl_img_hi L -> outside W a).
    { intros a Ha. destruct (outside_dec W a) as [Y|NO]; [exact Y|]. exfalso.
      destruct (WIN a NO) as [H|[(i & d & H1 & H2 & H3 & H4 & IN')|[(H1 & H2 & H3 & IN')|(H1 & [B' k'] & H2 & H3 & IN')]]]; [lia| | |];
        [pose proof (proj1 (Forall_forall _ _) BR _ IN') as (_ & _ & _ & _ & B5)| pose proof (proj1 (Forall_forall _ _) BR _ IN') as (_ & _ & _ & _ & B5)| pose proof (proj1 (Forall_forall _ _) BR _ IN') as (_ & _ & _ & _ & B5)]; cbn in B5; cbn in H3; lia. }
    assert (OSTR_E : forall e a, In e es -> md_addr e <= a < md_addr e + 16 -> outside W a).
    { intros e a He Ha. destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST' He) as (ME & CRE & _ & _ & HFE & ASE).
      destruct ASE as [C|C]; [| apply OUTS; lia].
      destruct (CRE a Ha) as [X|[[X _]|([B k] & Hb & R)]]; [lia| apply OUTIMG; pose proof DIMG; lia|]. cbn in R.
      (* [comment removed for export] *)
      pose proof (proj1 (Forall_forall _ _) ESF e He) as (CRE0 & _ & _ & AWS & _).
      destruct (CRE0 a Ha) as [X|[[X _]|([B0 k0] & Hb0 & R0)]]; [lia| apply OUTIMG; pose proof DIMG; lia|]. cbn in R0.
      eapply OUT_LB; [exact Hb0| | exact R0]. intros HW0. destruct (mpd_blk_heap _ _ HW0) as [O0 E0]. injection E0 as E1 E2. pose proof (AWS O0). lia. }
    assert (OLIMB_E : forall e a, In e es -> md_own e <> LNull -> md_p e <= a < md_p e + 4 * md_n e -> outside W a).
    { intros e a He NN Ha. destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST' He) as (ME & _).
      destruct (md_own e) eqn:OE; [exfalso; exact (NN eq_refl)| |].
      - destruct (E_BLK _ He OE) as (INL & INQ & NW0 & NE1). eapply OUT_LB; [exact INL| exact NW0| exact Ha].
      - apply OUTIMG. destruct ME as [(_ & _ & _ & HL & HN & HO) _]. rewrite OE in HO. destruct HO as (EN1 & _ & EP0 & (B0 & BL & _) & RO).
        rewrite u32s_length in BL.
        pose proof (ROIMG (md_p e) ltac:(lia) ltac:(replace (md_p e) with (md_p e + 0) by lia; apply RO; lia)).
        pose proof (ROIMG (md_p e + (4 * md_n e - 1)) ltac:(lia) ltac:(apply RO; lia)). lia. }
    (* [comment removed for export] *)
    assert (OLIMB_L : forall j d a, nth_error ls j = Some d -> md_own d = LHeap -> ~ (li = Some j) -> md_p d <= a < md_p d + 4 * md_n d -> outside W a).
    { intros j d a Hj Od NJ Ha. destruct (local_blk_facts _ _ _ _ _ HH (proj1 (LOCF _ _ Hj)) Od) as (IN & N1 & _).
      eapply OUTBLK; [exact IN| lia| exact Ha| | |].
      - intros i di Hli Hdi Odi E. injection E as E1 E2. assert (i <> j) by congruence. exact (LA _ _ _ _ Hdi Hj H Odi Od E1).
      - intros _ OW E. apply (proj1 (WB OW)). rewrite E. apply in_flat_map. exists d. split; [eapply nth_error_In; exact Hj| apply mpd_blk_in; exact Od].
      - intros _ HE. pose proof (proj1 (Forall_forall _ _) EXOK _ HE) as (_ & _ & NLOC & _). apply NLOC. apply in_flat_map. exists d. split; [eapply nth_error_In; exact Hj| apply mpd_blk_in; exact Od]. }
    assert (OLIMB_W : forall a, md_own dW = LHeap -> wl <> true -> md_p dW <= a < md_p dW + 4 * md_n dW -> outside W a).
    { intros a OW NWL Ha. destruct (HFW OW) as (_ & _ & IN & N1).
      eapply OUTBLK; [exact IN| lia| exact Ha| | intros C; exfalso; exact (NWL C)|].
      - intros i di Hli Hdi Odi E. apply (proj1 (WB OW)). rewrite <- E. apply in_flat_map. exists di. split; [eapply nth_error_In; exact Hdi| apply mpd_blk_in; exact Odi].
      - intros _ HE. exact (proj1 (proj2 (WB OW)) HE). }
    assert (OEX : forall B a, In B EX -> ex <> true -> fst B <= a < fst B + snd B -> outside W a).
    { intros [B k] a HE NEX Ha. pose proof (proj1 (Forall_forall _ _) EXOK _ HE) as (INB & NLB & NLOC & KP). cbn in Ha, KP.
      eapply OUTBLK; [exact INB| exact KP| exact Ha| | | intros C; exfalso; exact (NEX C)].
      - intros i di Hli Hdi Odi E. apply NLOC. rewrite <- E. apply in_flat_map. exists di. split; [eapply nth_error_In; exact Hdi| apply mpd_blk_in; exact Odi].
      - intros _ OW E. apply (proj1 (proj2 (WB OW))). rewrite E. exact HE. }
    (* [comment removed for export] *)
    split.
    { apply (HEAP_munch segs L HI hq LBq mq m2 moq lo W HH ACL MU WM). intros a Ha NO.
      destruct (WIN a NO) as [H|[(i & d & H1 & H2 & H3 & H4 & IN')|[(H1 & H2 & H3 & IN')|(H1 & [B' k'] & H2 & H3 & IN')]]].
      - left. rewrite HTc. lia.
      - right; right. exists (md_p d, 4 * md_n d). split; [exact IN'| cbn; lia].
      - right; right. exists (md_p dW, 4 * md_n dW). split; [exact IN'| cbn; lia].
      - right; right. exists (B', k'). split; [exact IN'| exact H3]. }
    split; [exact HTc|]. split; [exact MF|].
    split.
    { (* [comment removed for export] *)
      apply Forall_forall. intros d' Hd'. destruct (In_nth_error _ _ Hd') as [j Hj']. destruct (PAIR _ _ Hj') as [d Hj].
      pose proof (LOCF _ _ Hj) as (MD & NS & A1 & A2 & A8).
      destruct (REL _ _ _ Hj Hj') as (E1 & E2 & E3 & E4 & E5 & E6 & SAME & NEWL).
      split; [| rewrite E6, E1; auto].
      destruct MD as [(HR & HAL & HPOS & HL & HN & HO) HS]. split; [| rewrite E2; exact HS].
      rewrite E1, E2, E3, E4, E5, E6.
      split. { eapply rw_cells_transport; [exact HR| apply (munch_focus _ _ _ (md_addr d) 16 MU); intros x Hx; eapply OSTR_L; [exact Hj| lia]| exact WM| apply disjoint_focus; cbn; lia]. }
      split; [exact HAL|]. split; [exact HPOS|].
      destruct (md_own d) eqn:O.
      - destruct HO as [P0 N0]. rewrite (SAME ltac:(intros [_ E]; congruence)). auto.
      - destruct HO as (N1 & IN & PAL & U32).
        assert (li = Some j \/ li <> Some j) as [E|NE] by (destruct li as [i|]; [destruct (Nat.eq_dec i j); [left; congruence| right; congruence]| right; discriminate]).
        + destruct (NEWL E eq_refl) as [U' L']. split; [exact L'|]. split; [exact HN|]. split; [exact N1|]. split; [exact IN|]. split; [exact PAL| exact U'].
        + rewrite (SAME ltac:(intros [E _]; exact (NE E))). split; [exact HL|]. split; [exact HN|]. split; [exact N1|]. split; [exact IN|]. split; [exact PAL|].
          eapply u32arr_transport; [exact U32| apply (munch_focus _ _ _ (md_p d) (4 * md_n d) MU); intros x Hx; eapply OLIMB_L; [exact Hj| exact O| exact NE| exact Hx]| exact WM|].
          rewrite HL. apply disjoint_focus; lia.
      - exfalso. exact (NS eq_refl). }
    split.
    { intros x y dx dy Hx Hy NE. destruct (FLD _ _ Hx) as (dx0 & Hx0 & EAx & _). destruct (FLD _ _ Hy) as (dy0 & Hy0 & EAy & _).
      rewrite EAx, EAy. exact (SA _ _ _ _ Hx0 Hy0 NE). }
    split.
    { intros x y dx dy Hx Hy NE Ox Oy. destruct (FLD _ _ Hx) as (dx0 & Hx0 & _ & EOx & EPx & _). destruct (FLD _ _ Hy) as (dy0 & Hy0 & _ & EOy & EPy & _).
      rewrite EPx, EPy. apply (LA _ _ _ _ Hx0 Hy0 NE); congruence. }
    split.
    { (* [comment removed for export] *)
      destruct MW as [(HR & HAL & HPOS & HL & HN & HO) HS]. split; [| rewrite WE2; exact HS].
      rewrite WE1, WE2, WE3, WE4, WE5, WE6.
      split. { eapply rw_cells_transport; [exact HR| apply (munch_focus _ _ _ (md_addr dW) 16 MU); intros x Hx; apply OSTR_W; lia| exact WM| apply disjoint_focus; cbn; lia]. }
      split; [exact HAL|]. split; [exact HPOS|].
      destruct (md_own dW) eqn:O.
      - destruct HO as [P0 N0]. rewrite (WSAME ltac:(intros [_ E]; congruence)). auto.
      - destruct HO as (N1 & IN & PAL & U32).
        destruct (Bool.bool_dec wl true) as [E|NE].
        + destruct (WNEW E eq_refl) as [U' L']. split; [exact L'|]. split; [exact HN|]. split; [exact N1|]. split; [exact IN|]. split; [exact PAL| exact U'].
        + rewrite (WSAME ltac:(intros [E _]; exact (NE E))). split; [exact HL|]. split; [exact HN|]. split; [exact N1|]. split; [exact IN|]. split; [exact PAL|].
          eapply u32arr_transport; [exact U32| apply (munch_focus _ _ _ (md_p dW) (4 * md_n dW) MU); intros x Hx; eapply OLIMB_W; [reflexivity| exact NE| exact Hx]| exact WM|].
          rewrite HL. apply disjoint_focus; lia.
      - exfalso. exact (NSW eq_refl). }
    split.
    { (* [comment removed for export] *)
      split; [rewrite WE1; exact EA|]. split; [rewrite WE6; exact NSW|]. split; [rewrite WE5, WE3; exact EPN|]. rewrite WE6, WE4, WE3, BLKW.
      split; [intros OW; destruct (WB OW) as (X1 & X2 & X3); split; [intros C; apply X1; apply (proj1 (BLK _)); exact C| split; [exact X2| exact X3]]|].
      intros b Hb0 Hbq. destruct (WK b Hb0 Hbq) as [X|[X|X]]; [left; exact X| right; left; apply (proj2 (BLK _)); exact X| right; right; exact X]. }
    split.
    { apply Forall_forall. intros B HB. pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & NLB & NLOC & KP).
      split; [exact INB|]. split; [exact NLB|]. split; [intros C; apply NLOC; apply (proj1 (BLK _)); exact C| exact KP]. }
    split; [exact SUB|].
    split. { intros b Hb. rewrite BLKW. destruct (COV b Hb) as [X|[X|[X|X]]]; [left; exact X| right; left; apply (proj2 (BLK _)); exact X| right; right; left; exact X| right; right; right; exact X]. }
    split; [intros b Hb; apply FRS; apply (proj1 (BLK b)); exact Hb|].
    split.
    { (* [comment removed for export] *)
      apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) EXT e He) as ME.
      eapply mpd_at_munch_pw; [exact ME| exact MU| exact WM| exact MI| exact MI2| intros x Hx; exact (OSTR_E _ _ He Hx)|].
      intros OE x Hx. eapply OLIMB_E; [exact He| rewrite OE; discriminate| exact Hx]. }
    split.
    { eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. destruct Hc as [C|[[C _]|([B k] & Hb & R)]]; [apply OUTS; lia| apply OUTIMG; pose proof DIMG; lia|]. cbn in R.
      eapply OUT_LB; [exact Hb| | exact R]. intros HW0. destruct (mpd_blk_heap _ _ HW0) as [O0 E0]. injection E0 as E1 E2.
      unfold mpd_ivs in Ho. rewrite O0 in Ho. cbn in Ho. lia. }
    split. { eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha NW. apply OUTIMG. pose proof DIMG. lia. }
    split; [exact MI2|]. split; [exact ST2|].
    split.
    { apply Forall_forall. intros [a cs] Hac. pose proof (proj1 (Forall_forall _ _) CH _ Hac) as R. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as (B1 & B2 & B3). cbn in R, B1, B2, B3 |- *.
      eapply rw_cells_transport; [exact R| apply (munch_focus _ _ _ a (Z.of_nat (cells_size cs)) MU); intros x Hx; apply OUTS; lia| exact WM| apply disjoint_focus; lia]. }
    split.
    { apply Forall_forall. intros ac Hac. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as (B1 & B2 & B3).
      split; [exact B1|]. split; [exact B2|]. intros d' Hd'. destruct (In_nth_error _ _ Hd') as [j Hj']. destruct (FLD _ _ Hj') as (d & Hj & E1 & _).
      rewrite E1. apply B3. eapply nth_error_In. exact Hj. }
    destruct ex.
    - exact (CXT eq_refl).
    - rewrite (CXF eq_refl). split; [| exact CXS].
      apply Forall_forall. intros [a cs] Hac. pose proof (proj1 (Forall_forall _ _) CXH _ Hac) as R. pose proof (proj1 (Forall_forall _ _) CXS _ Hac) as (B & HB & B1 & B2). cbn in R, B1, B2 |- *.
      eapply rw_cells_transport; [exact R| apply (munch_focus _ _ _ a (Z.of_nat (cells_size cs)) MU); intros x Hx; eapply (OEX B); [exact HB| discriminate| lia]| exact WM| apply disjoint_focus; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition set_sg (d : mpd) (sg' : Z) : mpd := mkMPD (md_addr d) sg' (md_n d) (md_p d) (md_limbs d) (md_pad d) (md_own d).

  Lemma cs_hi_write : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pflo,$>.Pfhi,$>.PWlo,(10.(22.$>.$>.))Pm2,P,(1=.&40.)(3.(1=.&8.))Pls',(10.$1.)PCS',(10.(22.$>.(10.$3=.)))P,(48.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(1>.(21.(22.$>.$>.)(18.$>.$>.R7.R6.)R5.)R10.R4.)P,(27.Vsegs,R11.R5.)P,(28.Vsegs,R6.)P,(3<.Vsegs,R7.Vlo,VSPc,)P,(8.VSPc,R;.)P,(8.R;.VSP,)P,(29.(22.$>.$>.)Lw,(22.$>.$>.)(17.(8.Vlo,(2:.$>.$>.R1.))(8.(2;.$>.$>.R1.)VSPc,))R;.)P,(2.$0.(51.$1.R:.)(51.$1.R13.))P,Pj,$0.Pd,$1.Pd',$1.P,(2.(3.$1.)(4.$1.R17.R3.)(5.$1.R2.))P,(2.(3.$1.)(4.$1.R?.R4.)(5.$1.R2.))(7.(17.(7.(8.R13.(:.R4.))(8.(9.(:.R4.)+10.)R14.))(2.$1.R3.R4.))(16.$>.Lsg',$>.(17.(2.$1.R4.(56.R5.R1.))(17.(7.(2.$>.R1.+1.)(2.$>.R1.-1.))(3>.Vsegs,R12.(:.R5.)(57.(?.R5.)(58.&40.R1.)(1:.R5.)(30.R5.)))))))P,(29.(22.$>.(10.$3=.))Lac,(22.$>.(10.$3=.))(3>.Vsegs,R>.(2:.$>.(10.$3=.)R1.)(2;.$>.(10.$3=.)R1.))R;.)P,(29.(22.$>.(10.$3=.))Lac,(22.$>.(10.$3=.))(17.(8.VSPc,(2:.$>.(10.$3=.)R1.))(17.(8.(9.(2:.$>.(10.$3=.)R1.)(3?.(40.(2;.$>.(10.$3=.)R1.))))VSP,)Pd,$1.P,(13.$1.R1.R?.)(7.(8.(9.(2:.$>.(10.$3=.)R3.)(3?.(40.(2;.$>.(10.$3=.)R3.))))(:.R2.))(8.(9.(:.R2.)+10.)(2:.$>.(10.$3=.)R3.)))))R<.)(48.R?.R1:.R19.R18.R>.R16.R15.R=.R13.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX flo fhi Wlo m2 ls' CS' CST MU WM MI2 ST2 F1 F2 WLO LEN REL CH' CHS'.
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (MWf & NSW & EA & _ & LW & CRW & CRWL & HFW & ASW & WA8).
    pose proof CST as CST'. dest_cs CST.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [BR BA].
    assert (LOCF : forall i d, nth_error ls i = Some d -> local_ok mq LBq d) by (intros i d Hd; exact (proj1 (Forall_forall _ _) LOK d (nth_error_In _ _ Hd))).
    assert (OLO : forall a, a < lo -> outside ((flo, fhi) :: Wlo) a).
    { intros a Ha. cbn. split; [lia|]. eapply outside_of_bounds; [exact WLO| left; exact Ha]. }
    assert (OHI : forall a, SP <= a -> outside ((flo, fhi) :: Wlo) a).
    { intros a Ha. cbn. split; [lia|]. eapply outside_of_bounds; [exact WLO| right; lia]. }
    assert (OMID : forall a, SPc <= a -> (a < flo \/ fhi <= a) -> outside ((flo, fhi) :: Wlo) a).
    { intros a Ha Hb. cbn. split; [lia|]. eapply outside_of_bounds; [exact WLO| right; exact Ha]. }
    assert (BLO : forall B k a, In (B, k) LBq -> B <= a < B + k -> a < alloc_ceiling).
    { intros B k a IN Ha. pose proof (proj1 (Forall_forall _ _) BR _ IN) as (_ & _ & _ & B4 & _). cbn in B4. lia. }
    (* [comment removed for export] *)
    assert (PAIR : forall j d', nth_error ls' j = Some d' -> exists d, nth_error ls j = Some d).
    { intros j d' Hj'. destruct (nth_error ls j) as [d|] eqn:Hj; [exists d; reflexivity|].
      exfalso. apply nth_error_None in Hj. rewrite <- LEN in Hj. apply (proj2 (nth_error_None _ _)) in Hj. congruence. }
    assert (PAIR' : forall j d, nth_error ls j = Some d -> exists d', nth_error ls' j = Some d').
    { intros j d Hj. destruct (nth_error ls' j) as [d'|] eqn:Hj'; [exists d'; reflexivity|].
      exfalso. apply nth_error_None in Hj'. rewrite LEN in Hj'. apply (proj2 (nth_error_None _ _)) in Hj'. congruence. }
    assert (FLD : forall j d', nth_error ls' j = Some d' -> exists d, nth_error ls j = Some d /\ md_addr d' = md_addr d /\ md_own d' = md_own d /\ md_p d' = md_p d /\ md_n d' = md_n d).
    { intros j d' Hj'. destruct (PAIR _ _ Hj') as [d Hj]. exists d. destruct (REL _ _ _ Hj Hj') as [[_ ->]|(sg' & -> & _)]; cbn; auto 10. }
    assert (BLK : forall b, In b (flat_map mpd_blk ls') <-> In b (flat_map mpd_blk ls)).
    { intros b. rewrite !flat_map_blk_in. split; intros (d & Hd & O & ->).
      - destruct (In_nth_error _ _ Hd) as [j Hj']. destruct (FLD _ _ Hj') as (d0 & Hj & E1 & EO & EP & EN).
        exists d0. split; [eapply nth_error_In; exact Hj|]. rewrite <- EO, EP, EN. auto.
      - destruct (In_nth_error _ _ Hd) as [j Hj]. destruct (PAIR' _ _ Hj) as [d' Hj']. destruct (FLD _ _ Hj') as (d0 & Hj0 & E1 & EO & EP & EN).
        rewrite Hj in Hj0. injection Hj0 as <-. exists d'. split; [eapply nth_error_In; exact Hj'|]. rewrite EO, EP, EN. auto. }
    split. { apply (HEAP_munch segs L HI hq LBq mq m2 moq lo _ HH ACL MU WM). intros a Ha NO. left. rewrite HTc.
             destruct (Z_lt_le_dec a lo) as [C|C]; [exfalso; exact (NO (OLO a C))|]. destruct (Z_lt_le_dec a SP) as [C2|C2]; [lia| exfalso; exact (NO (OHI a C2))]. }
    split; [exact HTc|]. split; [exact MF|].
    split.
    { apply Forall_forall. intros d' Hd'. destruct (In_nth_error _ _ Hd') as [j Hj']. destruct (PAIR _ _ Hj') as [d Hj].
      pose proof (LOCF _ _ Hj) as (MD & NS & A1 & A2 & A8).
      destruct (REL _ _ _ Hj Hj') as [[AP ->]|(sg' & -> & SG & STR)].
      - split; [| auto]. eapply mpd_at_munch_pw; [exact MD| exact MU| exact WM| exact MI| exact MI2| intros x Hx; apply OMID; lia|].
        intros O x Hx. destruct (local_blk_facts _ _ _ _ _ HH MD O) as (_ & _ & P0 & P4 & _). apply OLO. lia.
      - split; [| cbn; auto]. split; [| cbn; exact SG].
        destruct MD as [(HR & HAL & HPOS & HL & HN & HO) _]. cbn. split; [exact STR|]. split; [exact HAL|]. split; [exact HPOS|]. split; [exact HL|]. split; [exact HN|].
        destruct (md_own d) eqn:O; [exact HO| | exfalso; exact (NS eq_refl)].
        destruct HO as (N1 & IN & PAL & U32). split; [exact N1|]. split; [exact IN|]. split; [exact PAL|].
        destruct (local_blk_facts _ _ _ _ _ HH (proj1 (LOCF _ _ Hj)) O) as (_ & _ & P0 & P4 & _).
        eapply u32arr_transport; [exact U32| apply (munch_focus _ _ _ (md_p d) (4 * md_n d) MU); intros x Hx; apply OLO; lia| exact WM| rewrite HL; apply disjoint_focus; lia]. }
    split.
    { intros x y dx dy Hx Hy NE. destruct (FLD _ _ Hx) as (dx0 & Hx0 & EAx & _). destruct (FLD _ _ Hy) as (dy0 & Hy0 & EAy & _).
      rewrite EAx, EAy. exact (SA _ _ _ _ Hx0 Hy0 NE). }
    split.
    { intros x y dx dy Hx Hy NE Ox Oy. destruct (FLD _ _ Hx) as (dx0 & Hx0 & _ & EOx & EPx & _). destruct (FLD _ _ Hy) as (dy0 & Hy0 & _ & EOy & EPy & _).
      rewrite EPx, EPy. apply (LA _ _ _ _ Hx0 Hy0 NE); congruence. }
    split.
    { eapply mpd_at_munch_pw; [exact MW| exact MU| exact WM| exact MI| exact MI2| intros x Hx; destruct ASW as [C|C]; [apply OLO; lia| apply OHI; lia]|].
      intros O x Hx. destruct (HFW O) as (P0 & P4 & _). apply OLO. lia. }
    split.
    { destruct WOK as (X1 & X2 & X3 & WB & WK). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
      split; [intros OW; destruct (WB OW) as (Y1 & Y2 & Y3); split; [intros C; apply Y1; apply (proj1 (BLK _)); exact C| split; [exact Y2| exact Y3]]|].
      intros b Hb0 Hbq. destruct (WK b Hb0 Hbq) as [X|[X|X]]; [left; exact X| right; left; apply (proj2 (BLK _)); exact X| right; right; exact X]. }
    split.
    { apply Forall_forall. intros B HB. pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & NLB & NLOC & KP).
      split; [exact INB|]. split; [exact NLB|]. split; [intros C; apply NLOC; apply (proj1 (BLK _)); exact C| exact KP]. }
    split; [exact SUB|].
    split. { intros b Hb. destruct (COV b Hb) as [X|[X|[X|X]]]; [left; exact X| right; left; apply (proj2 (BLK _)); exact X| right; right; left; exact X| right; right; right; exact X]. }
    split; [intros b Hb; apply FRS; apply (proj1 (BLK b)); exact Hb|].
    split.
    { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) EXT e He) as ME.
      destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST' He) as (_ & _ & _ & LE & _ & ASE).
      eapply mpd_at_munch_pw; [exact ME| exact MU| exact WM| exact MI| exact MI2| intros x Hx; destruct ASE as [C|C]; [apply OLO; lia| apply OHI; lia]|].
      intros O x Hx. destruct (mpd_limbs_low _ _ _ _ _ HH ME ltac:(rewrite O; discriminate)). apply OLO. lia. }
    split.
    { eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. destruct Hc as [C|[[C _]|([B k] & Hb & R)]]; [apply OHI; lia| apply OLO; pose proof DIMG; lia|]. cbn in R.
      apply OLO. assert (Hbq : In (B, k) LBq).
      { apply SUB; [exact Hb|]. intros HW. destruct (mpd_blk_heap _ _ HW) as [O0 E]. injection E as -> ->. unfold mpd_ivs in Ho. rewrite O0 in Ho. cbn in Ho. lia. }
      pose proof (BLO _ _ _ Hbq R). lia. }
    split. { eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha NW. apply OLO. pose proof DIMG. lia. }
    split; [exact MI2|]. split; [exact ST2|].
    split; [exact CH'|]. split; [exact CHS'|].
    split.
    { apply Forall_forall. intros [a cs] Hac. pose proof (proj1 (Forall_forall _ _) CXH _ Hac) as R. pose proof (proj1 (Forall_forall _ _) CXS _ Hac) as (B & HB & B1 & B2). cbn in R, B1, B2 |- *.
      pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & _ & _ & KP). destruct B as [B0 k0]. cbn in B1, B2, KP.
      pose proof (proj1 (Forall_forall _ _) BR _ INB) as (_ & _ & _ & B4 & _). cbn in B4.
      eapply rw_cells_transport; [exact R| apply (munch_focus _ _ _ a (Z.of_nat (cells_size cs)) MU); intros x Hx; apply OLO; lia| exact WM| apply disjoint_focus; lia]. }
    exact CXS.
  Qed.


  (* [comment removed for export] *)
  Lemma cs_sign_w : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pm2,P,(1=.&40.)(3.(1=.&8.))Psg',$>.P,(48.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(1>.(21.(22.$>.$>.)(18.$>.$>.(:.R7.)(9.(:.R7.)+10.))(24.(22.$>.$>.)))R<.R3.)P,(27.Vsegs,R=.R4.)P,(28.Vsegs,R5.)P,(3>.Vsegs,R6.(:.R:.)(57.(?.R:.)(58.&40.R5.)(1:.R:.)(30.R:.)))P,(7.(2.$>.R6.+1.)(2.$>.R6.-1.))(48.R8.R10.R?.R>.R=.(56.R<.R7.)R;.R:.R9.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX m2 sg' CST MU WM MI2 STR SG.
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (MWf & NSW & EA & (WR1 & WR2 & WR3) & LW & CRW & CRWL & HFW & ASW & WA8).
    destruct (cs_ivs_w _ _ _ _ _ _ _ _ _ CST) as (IVL & IVE & IVX & IVC & IVP).
    pose proof CST as CST'. dest_cs CST.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [BR BA].
    assert (IVS1 : forall a k, disjoint_from (mpd_ivs dW) a k -> disjoint_from [(md_addr dW, md_addr dW + 16)] a k).
    { intros a k D. unfold mpd_ivs in D. cbn in D |- *. split; [exact (proj1 D)| exact I]. }
    split.
    { apply (HEAP_munch segs L HI hq LBq mq m2 moq lo _ HH ACL MU WM). intros a Ha NO. cbn in NO.
      assert (R : md_addr dW <= a < md_addr dW + 16) by lia.
      destruct (WR1 a R) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
    split; [exact HTc|]. split; [exact MF|].
    split.
    { apply Forall_forall. intros dj Hdj. destruct (In_nth_error _ _ Hdj) as [j Hj].
      pose proof (proj1 (Forall_forall _ _) LOK dj Hdj) as (MJ & NSJ & J1 & J2 & JA8). split; [| auto].
      destruct (IVL _ _ Hj) as [D1 D2].
      eapply mpd_at_munch; [exact MJ| exact NSJ| exact MU| exact WM| exact (IVS1 _ _ D1)| intros O; exact (IVS1 _ _ (D2 O))]. }
    split; [exact SA|]. split; [exact LA|].
    split.
    { split; [| cbn; exact SG].
      destruct MW as [(HR & HAL & HPOS & HL & HN & HO) _]. cbn. split; [exact STR|]. split; [exact HAL|]. split; [exact HPOS|]. split; [exact HL|]. split; [exact HN|].
      destruct (md_own dW) eqn:O; [exact HO| | exfalso; exact (NSW eq_refl)].
      destruct HO as (N1 & IN & PAL & U32). split; [exact N1|]. split; [exact IN|]. split; [exact PAL|].
      eapply u32arr_transport; [exact U32| exact MU| exact WM|]. rewrite HL. cbn. pose proof (WR3 eq_refl). lia. }
    split; [exact WOK|]. split; [exact EXOK|]. split; [exact SUB|]. split; [exact COV|]. split; [exact FRS|].
    split.
    { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) EXT e He) as ME.
      destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST' He) as (_ & _ & _ & _ & HFE & _).
      pose proof (proj1 (Forall_forall _ _) ESF e He) as (_ & _ & _ & _ & _ & AWA & AWE). rewrite <- EA in AWA, AWE.
      eapply mpd_at_munch_pw; [exact ME| exact MU| exact WM| exact MI| exact MI2| intros x Hx; cbn; split; [lia| exact I]|].
      intros O x Hx. pose proof (AWE ltac:(rewrite O; discriminate)). cbn. split; [lia| exact I]. }
    split.
    { eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. unfold mpd_ivs in Ho. cbn in Ho |- *. rewrite EA. split; [lia| exact I]. }
    split. { eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha NW. cbn. split; [| exact I]. intros R. exact (NW (WR2 a R Ha)). }
    split; [exact MI2|]. split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| cbn; lia]|].
    split.
    { apply Forall_forall. intros [a cs] Hac. pose proof (proj1 (Forall_forall _ _) CH _ Hac) as R. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as (B1 & B2 & B3). cbn in R, B1, B2, B3 |- *.
      eapply rw_cells_transport; [exact R| exact MU| exact WM| exact (IVS1 _ _ (IVC _ _ B1 B2))]. }
    split; [exact CHS|].
    split.
    { apply Forall_forall. intros [a cs] Hac. pose proof (proj1 (Forall_forall _ _) CXH _ Hac) as R. pose proof (proj1 (Forall_forall _ _) CXS _ Hac) as (B & HB & B1 & B2). cbn in R, B1, B2 |- *.
      pose proof (IVX _ HB) as D. destruct B as [B0 k0]. cbn in B1, B2, D.
      eapply rw_cells_transport; [exact R| exact MU| exact WM| apply IVS1; eapply disjoint_from_sub; [exact D| lia| lia]]. }
    exact CXS.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cs_calloc_attach : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pi,$0.Pd,$1.Pm2,P,(1=.&40.)(3.(1=.&8.))Pmo2,$41.Ph2,(42.Vsegs,VL,VHI,)PA,$>.Pn,$>.Pm3,P,(1=.&40.)(3.(1=.&8.))Psg',$>.Ppad',(1=.&40.)P,(48.R13.R12.R11.R10.R?.R>.R=.R<.R;.)P,(2.(3.$1.)(4.$1.R10.R;.)(5.$1.R:.))P,(2.$;.(<.R;.)$2=.)P,(31.Vsegs,VL,VHI,R9.(21.(22.$>.$>.)(18.$>.$>.R8.(19.+4.R7.))R13.)R;.R:.)P,(2.$>.(32.Vsegs,VL,VHI,R:.)(32.Vsegs,VL,VHI,R15.))P,(33.R17.R<.)P,(47.Vsegs,VL,R16.VSPc,R19.R>.)P,(28.Vsegs,R?.)P,(3<.Vsegs,R10.Vlo,VSPc,)P,(59.VL,R>.(19.+4.R=.))P,(3>.Vsegs,R12.R?.(21.$3=.(5:.(5;.(19.+4.R>.))(5<.(1=.&8.)(58.&8.=)(5;.(19.+4.R>.))))(24.$3=.)))P,(17.(8.+1.R?.)(8.R?.$5=.))P,(1>.(21.(22.$>.$>.)(18.$>.$>.(:.R15.)(9.(:.R15.)+10.))(24.(22.$>.$>.)))R14.R?.)P,(27.Vsegs,R15.R10.)P,(28.Vsegs,R11.)P,(3>.Vsegs,R12.(:.R18.)(57.R14.(58.&40.R11.)R13.R10.))P,(7.(2.$>.R12.+1.)(2.$>.R12.-1.))(48.R14.R18.R17.(21.(22.$>.$>.)(18.$>.$>.R16.(19.+4.R15.))R21.)(1;.$1.R1;.R20.(5>.(:.R1:.)R13.R15.R16.(5<.(1=.&40.)(58.&40.=)(5;.R15.))R12.$=.))R1?.R1>.R1=.R1<.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX i d m2 mo2 h2 A n m3 sg' pad' CST Hi ON HH2 HT2 MF2 PR MI2 ST2 BRA ZCH NR MU WM MI3 STR SG.
    destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST Hi) as (MD & NS & _ & _ & _ & _ & _ & A1 & A2 & A8).
    pose proof CST as CST'. dest_cs CST.
    pose proof (HND _ _ _ _ HH2) as ND2. pose proof BRA as (BA0 & BA16 & _ & BA4 & BA5).
    assert (ANEW : ~ In (A, 4 * n) LBq).
    { intros C. inversion ND2 as [|x l NI ND']; subst. apply NI. apply in_map_iff. exists (A, 4 * n). auto. }
    assert (DJ : md_addr d + 16 <= A \/ A + 4 * n <= md_addr d) by lia.
    eapply (cs_binop_l mq moq hq LBq ls dW EX CS CX i d m3 mo2 h2 ((A, 4 * n) :: LBq)); [exact CST'| exact Hi| | exact HT2| exact MF2| | | | | exact MI3| |].
    - apply (HEAP_munch segs L HI h2 _ m2 m3 mo2 lo _ HH2 ACL MU WM). intros a Ha NO. cbn in NO. left. rewrite HT2, HTc. lia.
    - split; [| cbn; exact SG]. cbn.
      split; [exact STR|]. pose proof MD as [(_ & HAL & HPOS & _) _]. split; [exact HAL|]. split; [exact HPOS|].
      split; [rewrite repeat_length; lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [exact BA16|].
      eapply u32arr_of_cells; [| symmetry; apply u32s_repeat0].
      replace (4 * Z.to_nat n)%nat with (Z.to_nat (4 * n)) by lia.
      eapply rw_cells_transport; [exact ZCH| exact MU| exact WM| cbn; lia].
    - split; [reflexivity|]. split; [cbn; discriminate|]. unfold mpd_blk. rewrite ON. cbn.
      split; [intros b [<-|Hb]; [right; left; reflexivity| left; exact Hb]|].
      split; [intros b Hb _; right; exact Hb|]. intros b [].
    - unfold mpd_ivs. rewrite ON. eapply heap_presx_trans; [apply heap_presx_of_pres; exact PR|].
      eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. exact Ho.
    - eapply statics_ok_munch; [eapply statics_ok_heap_pres_; [exact SOK| exact PR]| exact MU|]. intros a Ha NW. cbn. pose proof DIMG. lia.
    - eapply stk_transport_disjoint; [exact ST2| exact MU| exact WM| cbn; lia].
    - unfold mpd_blk. cbn. intros b [<-|[]]. right. exact ANEW.
  Qed.

  (* [comment removed for export] *)
  Lemma set_nth_same_id {A} : forall i (ls : list A) d, nth_error ls i = Some d -> set_nth i ls d = ls.
  Proof.
    induction i as [|i IH]; intros [|x ls] d H; cbn in H |- *; try discriminate H; [injection H as ->; reflexivity| f_equal; apply IH; exact H].
  Qed.

  (* [comment removed for export] *)
  Lemma cs_heap_nop : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pi,$0.Pd,$1.Pm2,P,(1=.&40.)(3.(1=.&8.))Pmo2,$41.Ph2,(42.Vsegs,VL,VHI,)P,(48.R>.R=.R<.R;.R:.R9.R8.R7.R6.)P,(2.(3.$1.)(4.$1.R;.R6.)(5.$1.R5.))P,(31.Vsegs,VL,VHI,R3.R=.R5.R4.)P,(2.$>.(32.Vsegs,VL,VHI,R4.)(32.Vsegs,VL,VHI,R?.))P,(33.R11.R6.)P,(47.Vsegs,VL,R10.VSPc,R13.R8.)P,(28.Vsegs,R9.)P,(3<.Vsegs,R:.Vlo,VSPc,)(48.R;.R:.R9.R13.R12.R11.R10.R?.R>.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX i d m2 mo2 h2 CST Hi HH2 HT2 MF2 PR MI2 ST2.
    destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST Hi) as (MD & NS & _ & LD & CRD & CRDL & HFD & A1 & A2 & A8).
    pose proof CST as CST'. dest_cs CST.
    rewrite <- (set_nth_same_id i ls d Hi).
    eapply (cs_binop_l mq moq hq LBq ls dW EX CS CX i d m2 mo2 h2 LBq d); [exact CST'| exact Hi| exact HH2| exact HT2| exact MF2| | | | | exact MI2| exact ST2|].
    - eapply (mpd_at_heap_presx' mq m2 LBq LBq LBq SPc []); [exact MD| apply heap_presx_of_pres; exact PR| exact MI| exact MI2| | | cbn; exact I| intros _; cbn; exact I|].
      + intros a Ha. left. lia.
      + intros O. destruct (HFD O) as (_ & _ & IN & _). eapply client_range_blk; [exact IN| lia| lia].
      + intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [O ->]. destruct (HFD O) as (_ & _ & IN & _). exact IN.
    - apply mpd_out_refl. exact NS.
    - eapply heap_presx_of_pres_sub; [exact PR| intros b Hb; exact Hb| lia| lia] || (apply heap_presx_of_pres; exact PR).
    - eapply statics_ok_heap_pres_; [exact SOK| exact PR].
    - intros b Hb. left. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_release : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pi,$0.Pd,$1.Pm2,P,(1=.&40.)(3.(1=.&8.))Pmo2,$41.Ph2,(42.Vsegs,VL,VHI,)Pm3,P,(1=.&40.)(3.(1=.&8.))Ppad',(1=.&40.)P,(48.R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(2.(3.$1.)(4.$1.R=.R8.)(5.$1.R7.))P,(2.$;.(<.R8.)$=.)P,(31.Vsegs,VL,VHI,R6.(5?.(?.R9.)R10.)R8.R7.)P,(2.$>.(32.Vsegs,VL,VHI,R7.)(32.Vsegs,VL,VHI,R12.))P,(33.R14.R9.)P,(39.Vsegs,VL,(5?.(?.R<.)R13.)VSPc,(21.(22.$>.$>.)(18.$>.$>.(?.R<.)(9.(?.R<.)(19.+4.(1:.R<.))))(24.(22.$>.$>.)))R16.R;.)P,(3;.Vsegs,VL,R<.)P,(28.Vsegs,R=.)P,(3<.Vsegs,R>.Vlo,VSPc,)P,(1>.(21.(22.$>.$>.)(18.$>.$>.(:.R10.)(9.(:.R10.)+10.))(24.(22.$>.$>.)))R?.R<.)P,(27.Vsegs,R10.R=.)P,(28.Vsegs,R>.)P,(3>.Vsegs,R?.(:.R13.)(57.=(58.&40.+1.)=R>.))(48.R10.R12.R11.(5?.(?.R14.)R1;.)(1;.$1.R15.R1:.(5>.(:.R14.)+1.==(24.(1=.&40.))R?.$2=.))R19.R18.R17.R16.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX i d m2 mo2 h2 m3 pad' CST Hi OD HH2 HT2 MF2 PX2 SOK2 MI2 ST2 MU WM MI3 STR.
    destruct (cs_local_facts _ _ _ _ _ _ _ _ _ _ _ CST Hi) as (MD & NS & _ & _ & _ & _ & HFD & A1 & A2 & A8).
    destruct (HFD OD) as (PD0 & PD4 & IND & ND1 & _).
    pose proof CST as CST'. dest_cs CST.
    pose proof (HND _ _ _ _ HH) as NDq.
    set (LB2 := lb_remove (md_p d) LBq) in *.
    assert (NINf : forall k, ~ In (md_p d, k) LB2) by (intros k; subst LB2; apply lb_remove_notin; exact NDq).
    assert (KEEP : forall b, In b LBq -> b <> (md_p d, 4 * md_n d) -> In b LB2).
    { intros [B k] Hb NE. subst LB2. apply In_lb_remove_keep; [exact Hb|]. exact (nodup_fst_neq _ _ _ _ _ NDq IND Hb NE). }
    eapply (cs_binop_l mq moq hq LBq ls dW EX CS CX i d m3 mo2 h2 LB2); [exact CST'| exact Hi| | exact HT2| exact MF2| | | | | exact MI3| |].
    - apply (HEAP_munch segs L HI h2 _ m2 m3 mo2 lo _ HH2 ACL MU WM). intros a Ha NO. cbn in NO. left. rewrite HT2, HTc. lia.
    - split; [| cbn; left; reflexivity]. cbn.
      pose proof MD as [(_ & HAL & HPOS & _) _]. split; [exact STR|]. split; [exact HAL|]. split; [exact HPOS|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|]. split; reflexivity.
    - split; [reflexivity|]. split; [cbn; discriminate|]. unfold mpd_blk. rewrite OD. cbn.
      split; [intros b Hb; left; subst LB2; eapply In_lb_remove; exact Hb|].
      split; [intros b Hb NB; apply KEEP; [exact Hb| intros ->; apply NB; left; reflexivity]|].
      intros b [<-|[]] Hb2. exfalso. exact (NINf _ Hb2).
    - unfold mpd_ivs. rewrite OD. eapply heap_presx_trans.
      + intros a Ha Hc Ho. cbn in Ho. apply PX2; [exact Ha| | cbn; split; [exact (proj1 (proj2 Ho))| exact I]].
        destruct Hc as [C|[C|([B k] & Hb & R)]]; [left; exact C| right; left; exact C| right; right]. cbn in R.
        exists (B, k). split; [| exact R]. apply KEEP; [exact Hb|]. intros E. injection E as -> ->. lia.
      + eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn in Ho |- *. split; [exact (proj1 Ho)| exact I].
    - eapply statics_ok_munch; [exact SOK2| exact MU|]. intros a Ha NW. cbn. pose proof DIMG. lia.
    - eapply stk_transport_disjoint; [exact ST2| exact MU| exact WM| cbn; lia].
    - cbn. intros b [].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cs_ex_alloc : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))Pm2,P,(1=.&40.)(3.(1=.&8.))Pmo2,$41.Ph2,(42.Vsegs,VL,VHI,)PA,$>.Pk,$>.Pcs,(10.$3=.)P,(48.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(31.Vsegs,VL,VHI,R5.(21.(22.$>.$>.)(18.$>.$>.R4.R3.)R=.)R7.R6.)P,(2.$>.(32.Vsegs,VL,VHI,R6.)(32.Vsegs,VL,VHI,R?.))P,(33.R11.R8.)P,(47.Vsegs,VL,R10.VSPc,R13.R:.)P,(28.Vsegs,R;.)P,(3<.Vsegs,R<.Vlo,VSPc,)P,(1?.=R9.)P,(3>.Vsegs,R>.R;.R9.)P,(8.(3?.(40.R:.))R;.)(48.R10.R?.R>.(21.(22.$>.$>.)(18.$>.$>.R=.R<.)R16.)R15.R14.(21.(22.$>.$>.)(18.$>.$>.R=.R<.)R13.)R12.(21.(22.$>.(10.$3=.))(18.$>.(10.$3=.)R=.R;.)R11.))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX CS CX m2 mo2 h2 A k cs CST HH2 HT2 MF2 PR MI2 ST2 KP ACH SZ.
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (MWf & NSW & EA & (WR1 & WR2 & WR3) & LW & CRW & CRWL & HFW & ASW & WA8).
    destruct (cs_ivs_w _ _ _ _ _ _ _ _ _ CST) as (_ & _ & _ & _ & IVP).
    pose proof CST as CST'. dest_cs CST. destruct WOK as (X1 & X2 & X3 & WB & WK).
    pose proof (HND _ _ _ _ HH2) as ND2.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [BR BA].
    assert (ANEW : ~ In (A, k) LBq).
    { intros C. inversion ND2 as [|x l NI ND']; subst. apply NI. apply in_map_iff. exists (A, k). auto. }
    assert (PX2 : heap_presx segs L LBq SPc [] mq m2) by (apply heap_presx_of_pres; exact PR).
    assert (TR : forall d, mpd_at segs mq LBq d -> client_range L LBq SPc (md_addr d) 16 -> mpd_at segs m2 ((A, k) :: LBq) d).
    { intros d MD CR. eapply mpd_at_heap_presx'; [exact MD| exact PX2| exact MI| exact MI2| exact CR| | cbn; exact I| intros; exact I|].
      - intros O. eapply client_range_blk; [exact (proj1 (local_blk_facts _ _ _ _ _ HH MD O))| lia| lia].
      - intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [O ->]. right. exact (proj1 (local_blk_facts _ _ _ _ _ HH MD O)). }
    split; [exact HH2|]. split; [rewrite HT2; exact HTc|]. split; [eapply mo_frame_trans; [exact MF| exact MF2]|].
    split.
    { apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) LOK d Hd) as (MD & NS & A1 & A2 & A8). split; [| auto].
      apply TR; [exact MD| apply client_range_stack; lia]. }
    split; [exact SA|]. split; [exact LA|].
    split. { apply TR; [exact MW|]. intros a Ha. destruct (WR1 a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
    split.
    { split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split.
      - intros OW. destruct (WB OW) as (Y1 & Y2 & Y3). split; [exact Y1|]. split; [| exact Y3].
        intros [E|HE]; [| exact (Y2 HE)]. apply ANEW. rewrite E. exact (proj1 (local_blk_facts _ _ _ _ _ HH MW OW)).
      - intros b Hb0 [<-|Hbq]; [right; right; left; reflexivity|].
        destruct (WK b Hb0 Hbq) as [X|[X|X]]; [left; exact X| right; left; exact X| right; right; right; exact X]. }
    split.
    { constructor.
      - split; [left; reflexivity|]. split.
        { intros HL. destruct (in_dec blk_eq_dec2 (A, k) (mpd_blk dW0)) as [Y|N]; [exact Y|]. exfalso. exact (ANEW (SUB _ HL N)). }
        split; [| exact KP]. intros Hl. apply in_flat_map in Hl. destruct Hl as (x & Hx & Hbx). destruct (mpd_blk_heap _ _ Hbx) as [OX E].
        pose proof (proj1 (Forall_forall _ _) LOK x Hx) as (MX & _). apply ANEW. rewrite E. exact (proj1 (local_blk_facts _ _ _ _ _ HH MX OX)).
      - apply Forall_forall. intros B HB. pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & NLB & NLOC & KPB).
        split; [right; exact INB|]. split; [exact NLB|]. split; [exact NLOC| exact KPB]. }
    split; [intros b Hb NW; right; exact (SUB b Hb NW)|].
    split.
    { intros b [<-|Hb]; [right; right; right; left; reflexivity|].
      destruct (COV b Hb) as [X|[X|[X|X]]]; [left; exact X| right; left; exact X| right; right; left; exact X| right; right; right; right; exact X]. }
    split; [exact FRS|].
    split.
    { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) EXT e He) as ME.
      destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST' He) as (_ & CRE & _ & _ & _ & ASE).
      apply TR; [exact ME|]. intros a Ha. destruct (CRE a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
    split.
    { eapply heap_presx_trans; [exact PX|]. intros a Ha Hc Ho. destruct (IVP a Ha Hc Ho) as [C1 _]. exact (PR a Ha C1). }
    split; [eapply statics_ok_heap_pres_; [exact SOK| exact PR]|]. split; [exact MI2|]. split; [exact ST2|].
    split.
    { apply Forall_forall. intros [a cs'] Hac. pose proof (proj1 (Forall_forall _ _) CH _ Hac) as R. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as (B1 & B2 & B3). cbn in R, B1, B2, B3 |- *.
      eapply heap_presx_rw_cells; [exact PX2| exact R| apply client_range_stack; lia| cbn; exact I]. }
    split; [exact CHS|].
    split.
    { constructor; [exact ACH|].
      apply Forall_forall. intros [a cs'] Hac. pose proof (proj1 (Forall_forall _ _) CXH _ Hac) as R. pose proof (proj1 (Forall_forall _ _) CXS _ Hac) as (B & HB & B1 & B2). cbn in R, B1, B2 |- *.
      pose proof (proj1 (Forall_forall _ _) EXOK _ HB) as (INB & _). destruct B as [B0 k0]. cbn in B1, B2.
      eapply heap_presx_rw_cells; [exact PX2| exact R| eapply client_range_blk; [exact INB| lia| lia]| cbn; exact I]. }
    constructor; [exists (A, k); split; [left; reflexivity| cbn; lia]|].
    apply Forall_forall. intros ac Hac. pose proof (proj1 (Forall_forall _ _) CXS _ Hac) as (B & HB & B1 & B2). exists B. split; [right; exact HB| auto].
  Qed.

  Lemma cs_ex_free : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PEX,(10.$11.)PEX',(10.(22.$>.$>.))PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))PCX',(10.(22.$>.(10.$3=.)))Pm2,P,(1=.&40.)(3.(1=.&8.))Pmo2,$41.Ph2,(42.Vsegs,VL,VHI,)PA,$>.Pk,$>.P,(48.R10.R?.R>.R=.R<.R;.R:.R8.R7.)P,(2.(10.$11.)R;.(21.(22.$>.$>.)(18.$>.$>.R3.R2.)R:.))P,(6.(13.(22.$>.$>.)(18.$>.$>.R4.R3.)R;.))P,(31.Vsegs,VL,VHI,R6.(5?.R5.R10.)R8.R7.)P,(2.$>.(32.Vsegs,VL,VHI,R7.)(32.Vsegs,VL,VHI,R12.))P,(33.R14.R9.)P,(39.Vsegs,VL,(5?.R8.R13.)VSPc,(21.(22.$>.$>.)(18.$>.$>.R8.(9.R8.R7.))(24.(22.$>.$>.)))R16.R;.)P,(3;.Vsegs,VL,R<.)P,(28.Vsegs,R=.)P,(3<.Vsegs,R>.Vlo,VSPc,)P,(29.(22.$>.(10.$3=.))Lac,(22.$>.(10.$3=.))(13.(22.$>.(10.$3=.))R1.R12.)R10.)P,(29.(22.$>.(10.$3=.))Lac,(22.$>.(10.$3=.))(16.(22.$>.$>.)LB,(22.$>.$>.)(17.(13.(22.$>.$>.)R1.R16.)(17.(8.(2:.$>.$>.R1.)(2:.$>.(10.$3=.)R2.))(8.(9.(2:.$>.(10.$3=.)R2.)(3?.(40.(2;.$>.(10.$3=.)R2.))))(9.(2:.$>.$>.R1.)(2;.$>.$>.R1.))))))R11.)(48.R11.R10.R?.(5?.R>.R19.)R18.R17.R15.R14.R12.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW EX EX' CS CX CX' m2 mo2 h2 A k CST HEX NIN' HH2 HT2 MF2 PX2 SOK2 MI2 ST2 CXI CXS'.
    destruct (cs_w_facts _ _ _ _ _ _ _ _ _ CST) as (MWf & NSW & EA & (WR1 & WR2 & WR3) & LW & CRW & CRWL & HFW & ASW & WA8).
    destruct (cs_ivs_w _ _ _ _ _ _ _ _ _ CST) as (_ & _ & IVX & _ & IVP).
    pose proof CST as CST'. dest_cs CST. destruct WOK as (X1 & X2 & X3 & WB & WK).
    pose proof (HND _ _ _ _ HH) as NDq.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [BR BA].
    assert (HEA : In (A, k) EX) by (rewrite HEX; left; reflexivity).
    pose proof (proj1 (Forall_forall _ _) EXOK _ HEA) as (INA & NLA & NLOCA & KP). cbn in KP.
    pose proof (proj1 (Forall_forall _ _) BR _ INA) as (A0 & _ & _ & A4 & A5). cbn in A0, A4, A5.
    set (LB2 := lb_remove A LBq) in *.
    assert (NINf : forall j, ~ In (A, j) LB2) by (intros j; subst LB2; apply lb_remove_notin; exact NDq).
    assert (KEEP : forall b, In b LBq -> b <> (A, k) -> In b LB2).
    { intros [B j] Hb NE. subst LB2. apply In_lb_remove_keep; [exact Hb|]. exact (nodup_fst_neq _ _ _ _ _ NDq INA Hb NE). }
    assert (BACK : forall b, In b LB2 -> In b LBq /\ b <> (A, k)).
    { intros b Hb. split; [subst LB2; eapply In_lb_remove; exact Hb|]. intros ->. exact (NINf _ Hb). }
    assert (DISJ : forall B j, In (B, j) LBq -> (B, j) <> (A, k) -> 0 < j -> B + j <= A \/ A + k <= B).
    { intros B j Hb NE Hj. destruct (blocks_apart_neq _ _ _ BA Hb INA NE ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia. }
    (* [comment removed for export] *)
    assert (TR : forall d, mpd_at segs mq LBq d -> client_range L LBq SPc (md_addr d) 16 ->
              (md_addr d + 16 <= A \/ A + k <= md_addr d) -> (md_own d = LHeap -> (md_p d, 4 * md_n d) <> (A, k)) -> mpd_at segs m2 LB2 d).
    { intros d MD CR DS NB.
      assert (LK : md_own d = LHeap -> In (md_p d, 4 * md_n d) LB2 /\ (md_p d + 4 * md_n d <= A \/ A + k <= md_p d)).
      { intros O. destruct (local_blk_facts _ _ _ _ _ HH MD O) as (IN & N1 & _). split; [exact (KEEP _ IN (NB O))| exact (DISJ _ _ IN (NB O) ltac:(lia))]. }
      eapply mpd_at_heap_presx'; [exact MD| exact PX2| exact MI| exact MI2| | | cbn; split; [lia| exact I]| intros O; cbn; split; [pose proof (proj2 (LK O)); lia| exact I]|].
      - intros a Ha. destruct (CR a Ha) as [C|[C|([B j] & Hb & R)]]; [left; exact C| right; left; exact C| right; right]. cbn in R.
        exists (B, j). split; [| exact R]. apply KEEP; [exact Hb|]. intros E. injection E as -> ->. lia.
      - intros O. eapply client_range_blk; [exact (proj1 (LK O))| lia| lia].
      - intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [O ->]. exact (proj1 (LK O)). }
    split; [exact HH2|]. split; [rewrite HT2; exact HTc|]. split; [eapply mo_frame_trans; [exact MF| exact MF2]|].
    split.
    { apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) LOK d Hd) as (MD & NS & A1 & A2 & A8). split; [| auto].
      apply TR; [exact MD| apply client_range_stack; lia| lia|]. intros O E. apply NLOCA. rewrite <- E. apply in_flat_map. exists d. split; [exact Hd| apply mpd_blk_in; exact O]. }
    split; [exact SA|]. split; [exact LA|].
    split.
    { pose proof (IVX _ HEA) as D. unfold mpd_ivs in D. cbn in D.
      apply TR; [exact MW| | pose proof (proj1 D); lia|].
      - intros a Ha. destruct (WR1 a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
      - intros OW E. apply (proj1 (proj2 (WB OW))). rewrite E. exact HEA. }
    split.
    { split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split.
      - intros OW. destruct (WB OW) as (Y1 & Y2 & Y3). split; [exact Y1|]. split; [| exact Y3]. intros HE. apply Y2. rewrite HEX. right. exact HE.
      - intros b Hb0 Hb2. destruct (BACK b Hb2) as [Hbq NE]. destruct (WK b Hb0 Hbq) as [X|[X|X]]; [left; exact X| right; left; exact X| right; right].
        rewrite HEX in X. destruct X as [E|X]; [exfalso; exact (NE (eq_sym E))| exact X]. }
    split.
    { apply Forall_forall. intros B HB. assert (HB' : In B EX) by (rewrite HEX; right; exact HB).
      pose proof (proj1 (Forall_forall _ _) EXOK _ HB') as (INB & NLB & NLOC & KPB).
      split; [apply KEEP; [exact INB| intros ->; exact (NIN' HB)]|]. split; [exact NLB|]. split; [exact NLOC| exact KPB]. }
    split. { intros b Hb NW. apply KEEP; [exact (SUB b Hb NW)|]. intros ->. exact (NW (NLA Hb)). }
    split.
    { intros b Hb2. destruct (BACK b Hb2) as [Hbq NE]. destruct (COV b Hbq) as [X|[X|[X|X]]]; [left; exact X| right; left; exact X| right; right; left; exact X| right; right; right].
      rewrite HEX in X. destruct X as [E|X]; [exfalso; exact (NE (eq_sym E))| exact X]. }
    split; [exact FRS|].
    split.
    { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) EXT e He) as ME.
      destruct (cs_ext_facts _ _ _ _ _ _ _ _ _ _ CST' He) as (_ & CRE & _ & _ & HFE & ASE).
      pose proof (proj1 (Forall_forall _ _) ESF e He) as (CRE0 & _ & _ & AWS & AWL & _).
      apply TR; [exact ME| | |].
      - intros a Ha. destruct (CRE a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
      - eapply (client_apart_fresh mq moq hq LBq (md_addr e) 16); [exact HH| exact SUB| exact CRE0| lia| exact INA| exact NLA| exact KP| exact ASE| exact AWS].
      - intros OE E. destruct (HFE OE) as (_ & INQ & INL & NE1). rewrite E in INL. destruct (mpd_blk_heap _ _ (NLA INL)) as [O0 E0]. injection E0 as E1 E2.
        injection E as E3 E4. destruct AWL as [C|[C|C]]; [exact (C O0)| congruence| lia]. }
    split.
    { eapply heap_presx_trans; [exact PX|]. intros a Ha Hc Ho. destruct (IVP a Ha Hc Ho) as [C1 _].
      assert (NA : ~ (A <= a < A + k)).
      { intros R. destruct C1 as [C|[[C _]|([B j] & Hb & Rb)]]; [lia| pose proof DIMG; lia|]. cbn in Rb.
        destruct (blk_eq_dec2 (B, j) (A, k)) as [E|NE].
        - injection E as -> ->. destruct Hc as [C|[[C _]|([B' j'] & Hb' & Rb')]]; [lia| pose proof DIMG; lia|]. cbn in Rb'.
          assert (NW' : ~ In (B', j') (mpd_blk dW0)).
          { intros HW0. destruct (mpd_blk_heap _ _ HW0) as [O0 E0]. injection E0 as -> ->. unfold mpd_ivs in Ho. rewrite O0 in Ho. cbn in Ho. lia. }
          pose proof (SUB _ Hb' NW') as Hbq'.
          assert (NE' : (B', j') <> (A, k)) by (intros E'; rewrite E' in Hb', NW'; exact (NW' (NLA Hb'))).
          pose proof (proj1 (Forall_forall _ _) BR _ Hbq') as (_ & _ & K2 & _). cbn in K2.
          destruct (Z.eq_dec j' 0) as [->|NZ]; [lia|]. pose proof (DISJ _ _ Hbq' NE' ltac:(lia)). lia.
        - pose proof (proj1 (Forall_forall _ _) BR _ Hb) as (_ & _ & K2 & _). cbn in K2.
          destruct (Z.eq_dec j 0) as [->|NZ]; [lia|]. pose proof (DISJ _ _ Hb NE ltac:(lia)). lia. }
      apply PX2; [exact Ha| | cbn; split; [exact NA| exact I]].
      destruct C1 as [C|[C|([B j] & Hb & Rb)]]; [left; exact C| right; left; exact C| right; right]. cbn in Rb.
      exists (B, j). split; [| exact Rb]. apply KEEP; [exact Hb|]. intros E. injection E as -> ->. exact (NA Rb). }
    split; [exact SOK2|]. split; [exact MI2|]. split; [exact ST2|].
    split.
    { apply Forall_forall. intros [a cs'] Hac. pose proof (proj1 (Forall_forall _ _) CH _ Hac) as R. pose proof (proj1 (Forall_forall _ _) CHS _ Hac) as (B1 & B2 & B3). cbn in R, B1, B2, B3 |- *.
      eapply heap_presx_rw_cells; [exact PX2| exact R| apply client_range_stack; lia| cbn; lia]. }
    split; [exact CHS|].
    split.
    { apply Forall_forall. intros [a cs'] Hac. pose proof (proj1 (Forall_forall _ _) CXI _ Hac) as HIN. pose proof (proj1 (Forall_forall _ _) CXH _ HIN) as R.
      pose proof (proj1 (Forall_forall _ _) CXS' _ Hac) as (B & HB & B1 & B2). cbn in R, B1, B2 |- *.
      assert (HB' : In B EX) by (rewrite HEX; right; exact HB).
      pose proof (proj1 (Forall_forall _ _) EXOK _ HB') as (INB & _ & _ & KPB). destruct B as [B0 k0]. cbn in B1, B2, KPB.
      assert (NE : (B0, k0) <> (A, k)) by (intros E; rewrite E in HB; exact (NIN' HB)).
      pose proof (DISJ _ _ INB NE KPB).
      eapply heap_presx_rw_cells; [exact PX2| exact R| eapply client_range_blk; [apply KEEP; [exact INB| exact NE]| lia| lia]| cbn; lia]. }
    exact CXS'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cs_init : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pm1,P,(1=.&40.)(3.(1=.&8.))Pls,(10.$1.)PCS,(10.(22.$>.(10.$3=.)))P,(31.Vsegs,VL,VHI,Vh0,VLB,Vm0,Vmo0,)P,(3;.Vsegs,VL,Vm0,)P,(28.Vsegs,Vm0,)P,(26.Vsegs,Vm0,VLB,VdW0,)P,(29.$1.Le,$1.(26.Vsegs,Vm0,VLB,R1.)Ves,)P,(1>.(21.(22.$>.$>.)(18.$>.$>.Vlo,VSP,)(24.(22.$>.$>.)))Vm0,R8.)P,(27.Vsegs,Vm0,R9.)P,(28.Vsegs,R:.)P,(3<.Vsegs,R;.Vlo,VSPc,)P,(29.$1.Ld,$1.(17.(3>.Vsegs,R=.(:.R1.)(57.=(58.&40.+1.)=(30.R1.)))(17.(2.$;.(<.R1.)$2=.)(17.(2.$>.(?.R1.)=)(17.(2.$>.(1:.R1.)=)(17.(2.(10.(1=.&40.))(54.R1.)(24.(1=.&40.)))(17.(2.$>.(52.R1.)+1.)(17.(8.VSPc,(:.R1.))(17.(8.(9.(:.R1.)+10.)VSP,)(2.$>.(2?.(:.R1.)+8.)=)))))))))R;.)P,(35.R<.)P,(29.(22.$>.(10.$3=.))Lac,(22.$>.(10.$3=.))(3>.Vsegs,R?.(2:.$>.(10.$3=.)R1.)(2;.$>.(10.$3=.)R1.))R<.)P,(29.(22.$>.(10.$3=.))Lac,(22.$>.(10.$3=.))(17.(8.VSPc,(2:.$>.(10.$3=.)R1.))(17.(8.(9.(2:.$>.(10.$3=.)R1.)(3?.(40.(2;.$>.(10.$3=.)R1.))))VSP,)Pd,$1.P,(13.$1.R1.R10.)(7.(8.(9.(2:.$>.(10.$3=.)R3.)(3?.(40.(2;.$>.(10.$3=.)R3.))))(:.R2.))(8.(9.(:.R2.)+10.)(2:.$>.(10.$3=.)R3.)))))R=.)(48.R10.Vmo0,Vh0,VLB,R?.VdW0,(24.$11.)R>.(24.(22.$>.(10.$3=.))))")
(* [comment removed for export] *).
  Proof.
    intros m1 ls CS HH SOK MI MW0 EXT MU WM MI1 ST1 LOC0 SA CH CHS.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [BR BA]. pose proof alloc_ceiling_pos as ACP. destruct W0WR as (WW1 & WW2 & WW3).
    assert (NOBLK : forall b, ~ In b (flat_map mpd_blk ls)).
    { intros b Hb. apply in_flat_map in Hb. destruct Hb as (d & Hd & Hb). pose proof (proj1 (Forall_forall _ _) LOC0 d Hd) as (_ & O & _). unfold mpd_blk in Hb. rewrite O in Hb. exact Hb. }
    assert (OLO : forall a, a < lo -> outside [(lo, SP)] a) by (intros a Ha; cbn; split; [lia| exact I]).
    split. { apply (HEAP_munch segs L HI h0 _ m0 m1 mo0 lo _ HH ACL MU WM). intros a Ha NO. cbn in NO. left. lia. }
    split; [reflexivity|]. split; [apply mo_frame_refl|].
    split.
    { apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) LOC0 d Hd) as (R & O & P0 & N0 & L0 & S1 & A1 & A2 & A8).
      split; [| rewrite O; split; [discriminate| auto]].
      split; [| rewrite S1; left; reflexivity].
      split; [rewrite P0, S1, N0; exact R|]. split; [exact A8|]. split; [lia|]. split; [rewrite L0, N0; reflexivity|]. split; [rewrite N0; unfold MPI_MAX_LIMBS; lia|].
      rewrite O. auto. }
    split; [exact SA|].
    split. { intros a b da db Ha Hb NE Oa. pose proof (proj1 (Forall_forall _ _) LOC0 da (nth_error_In _ _ Ha)) as (_ & O & _). congruence. }
    split.
    { eapply mpd_at_munch_pw; [exact MW0| exact MU| exact WM| exact MI| exact MI1| intros x Hx; cbn; split; [destruct W0AS as [C|C]; lia| exact I]|].
      intros O x Hx. destruct (local_blk_facts _ _ _ _ _ HH MW0 O) as (_ & _ & P0 & P4 & _). apply OLO. lia. }
    split.
    { split; [reflexivity|]. split; [exact W0NS|]. split; [split; [reflexivity| lia]|]. split.
      - intros O. split; [exact (NOBLK _)|]. split; [intros []|]. left. apply mpd_blk_in. exact O.
      - intros b Hb _. left. reflexivity. }
    split; [constructor|].
    split; [intros b Hb _; exact Hb|]. split; [intros b Hb; left; exact Hb|]. split; [intros b Hb; destruct (NOBLK b Hb)|].
    split.
    { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) EXT e He) as ME.
      pose proof (proj1 (Forall_forall _ _) ESF e He) as (CRE & INE & ASE & _).
      eapply mpd_at_munch_pw; [exact ME| exact MU| exact WM| exact MI| exact MI1| intros x Hx; cbn; split; [lia| exact I]|].
      intros O x Hx. destruct (local_blk_facts _ _ _ _ _ HH ME O) as (_ & _ & P0 & P4 & _). apply OLO. lia. }
    split.
    { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn. split; [| exact I].
      destruct Hc as [C|[[C _]|([B k] & Hb & R)]]; [lia| pose proof DIMG; lia|]. cbn in R.
      pose proof (proj1 (Forall_forall _ _) BR _ Hb) as (_ & _ & _ & B4 & _). cbn in B4. lia. }
    split. { eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha NW. cbn. pose proof DIMG. lia. }
    split; [exact MI1|]. split; [exact ST1|]. split; [exact CH|]. split; [exact CHS|]. split; constructor.
  Qed.

  (* [comment removed for export] *)
  Lemma cs_final : ltac2:(CDefT.buildp (gd_tbl_MpiClient ()) "Pmq,P,(1=.&40.)(3.(1=.&8.))Pmoq,$41.Phq,(42.Vsegs,VL,VHI,)PLBq,(10.$11.)Pls,(10.$1.)PdW,$1.PCS,(10.(22.$>.(10.$3=.)))PCX,(10.(22.$>.(10.$3=.)))P,(48.R8.R7.R6.R5.R4.R3.(24.$11.)R2.R1.)P,(29.$1.Ld,$1.(2.$;.(<.R1.)$2=.)R5.)(17.(31.Vsegs,VL,VHI,R8.R7.R:.R9.)(17.(2.$>.(32.Vsegs,VL,VHI,R8.)(32.Vsegs,VL,VHI,Vh0,))(17.(33.Vmo0,R9.)(17.(26.Vsegs,R:.R7.R5.)(17.(4=.VLB,VdW0,R7.R5.)(17.(60.VLB,VdW0,R5.)(17.(39.Vsegs,VL,VLB,VSP,(3:.VdW0,)Vm0,R:.)(17.(3;.Vsegs,VL,R:.)(17.(28.Vsegs,R:.)(17.(3<.Vsegs,R:.Vlo,VSPc,)(29.(22.$>.(10.$3=.))Lac,(22.$>.(10.$3=.))(3>.Vsegs,R;.(2:.$>.(10.$3=.)R1.)(2;.$>.(10.$3=.)R1.))R4.)))))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq ls dW CS CX CST NUL. dest_cs CST. destruct WOK as (X1 & X2 & [X3 X4] & WB & WK).
    assert (NOBLK : forall b, ~ In b (flat_map mpd_blk ls)).
    { intros b Hb. apply in_flat_map in Hb. destruct Hb as (d & Hd & Hb). pose proof (proj1 (Forall_forall _ _) NUL d Hd) as O. cbn in O. unfold mpd_blk in Hb. rewrite O in Hb. exact Hb. }
    split; [exact HH|]. split; [exact HTc|]. split; [exact MF|]. split; [exact MW|].
    split.
    { split; [exact X1|]. split; [exact X2|]. split.
      - intros b Hb. destruct (COV b Hb) as [X|[X|[X|[]]]]; [left; exact X| destruct (NOBLK _ X)| right; exact X].
      - split; [exact SUB|]. intros b Hb0 Hbq. destruct (WK b Hb0 Hbq) as [X|[X|[]]]; [exact X| destruct (NOBLK _ X)]. }
    split.
    { split; [exact X1|]. split; [exact X3|]. split; [| exact X4].
      intros b Hb. destruct (mpd_blk_heap _ _ Hb) as [O ->]. destruct (proj2 (proj2 (WB O))) as [Y|N]; [left; exact Y| right; exact N]. }
    split; [exact PX|]. split; [exact SOK|]. split; [exact MI|]. split; [exact ST| exact CH].
  Qed.
End MC.
