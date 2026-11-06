(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_tables MallocInv_steps.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


Section Tail.
  Context {R : Type}.
  Variables (A : astate) (s s2 : mstate).
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i nn : Z).
  Variables (S Mb p0 e OFF Pp RSV OFU CODE : Z).
  Hypothesis HW : WF A.
  Hypothesis HR : Rep A (ms_mem s).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi : nth_error slots (Z.to_nat i) = Some STaken.
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hi32 : i < 32.
  Hypothesis ES : S = mt_stride mt.
  Hypothesis EMb : Mb = mt_mem mt.
  Hypothesis Ep0 : p0 = Mb + 16 + i * S.
  Hypothesis Ee : e = p0 + S - 4.
  Hypothesis EPp : Pp = p0 + 16 * OFF.
  Hypothesis ERSV : RSV = e - nn - Pp.
  Hypothesis EOFU : OFU = (Pp - Mb - 16) / 16.
  Hypothesis ECODE : CODE = Z.min RSV 5.
  Hypothesis HS16 : 16 <= S.
  Hypothesis Hnn : 0 <= nn.
  Hypothesis HOFF : 0 <= OFF <= 255.
  Hypothesis HRSV : 0 <= RSV < 2^20.
  Hypothesis HSnn : S - nn < 2^20.
  Hypothesis HOFU : 0 <= OFU < 2^20.
  Hypothesis Hheap : 0x1000 <= Mb /\ Mb + 16 + mt_cnt mt * S <= alloc_ceiling /\
                     (Mb + 16 + mt_cnt mt * S <= IMG_LO \/ IMG_HI <= Mb).
  Hypothesis HiS : 0 <= i * S /\ i * S + S <= mt_cnt mt * S.
  Hypothesis Hspan : forall x, p0 - 4 <= x < e + 1 -> dom A x.
  Hypothesis Hclear : forall f, has A f -> f_a f + f_n f <= Mb + 16 + i * S - 3 \/ Mb + 16 + i * S + S - 4 <= f_a f.
  (* [comment removed for export] *)
  Hypothesis HRb : Rep A (ms_mem s2).
  Hypothesis HWINb : WIN s2.
  Hypothesis Hvmb : ms_vm s2 = ms_vm s.
  Hypothesis Hlob : ms_lo s2 = ms_lo s.
  Hypothesis Hhib : ms_hi s2 = ms_hi s.
  Hypothesis HROb : rodata_clear (ms_mem s2).
  Hypothesis Hfrb : forall a : word, bv_unsigned a < p0 - 3 \/ e <= bv_unsigned a -> ms_mem s2 a = ms_mem s a.
  Hypothesis Hpayb : forall a : word, Pp <= bv_unsigned a < Pp + nn -> ms_mem s2 a = ms_mem s a.
  Hypothesis Hhdrb : OFF <> 0 -> mbyte (ms_mem s2) (p0 - 3) = Some 224 /\ mbyte (ms_mem s2) (p0 - 2) = Some (OFF mod 256) /\
                     mbyte (ms_mem s2) (p0 - 1) = Some (OFF / 256) /\ mbyte (ms_mem s2) (Pp - 4) = Some 0.
  Hypothesis Hbi : mbyte (ms_mem s2) (Pp - 3) = Some i.
  Hypothesis Hbo0 : mbyte (ms_mem s2) (Pp - 2) = Some (OFU mod 256).
  Hypothesis Hbo1 : mbyte (ms_mem s2) (Pp - 1) = Some ((OFU / 256) mod 256).
  Hypothesis Hbz : RSV <> 0 -> mbyte (ms_mem s2) (Pp + nn) = Some 0.
  Hypothesis Hbf : 5 <= RSV -> mbyte (ms_mem s2) (e - 5) = Some 0 /\
                   forall kk, 0 <= kk < 4 -> mbyte (ms_mem s2) (e - 4 + kk) = Some (byte_of RSV kk).

  Let L' := lupd (a_live A) (p0 + 16 * OFF) (Some nn).

  Lemma L'_spec : forall q k, L' q = Some k <->
    (exists off, SLive OFF nn = SLive off k /\ q = slot_start mt i + 16 * off) \/
    (a_live A q = Some k /\ forall off n, STaken = SLive off n -> q <> slot_start mt i + 16 * off).
  Proof using ECODE EMb EOFU EPp ERSV ES Ee Ep0 HOFF HOFU HRSV HS16 HSnn HW Hbf Hbi Hbo0 Hbo1 Hbz Hclear Hfrb Hhdrb Hheap Hi Hi0 HiS Hma Hnn Hpayb Hr Hspan. pu_keep (ECODE, EMb, EOFU, EPp, ERSV, ES, Ee, Ep0, HOFF, HOFU, HRSV, HS16, HSnn, HW, Hbf, Hbi, Hbo0, Hbo1, Hbz, Hclear, Hfrb, Hhdrb, Hheap, Hi, Hi0, HiS, Hma, Hnn, Hpayb, Hr, Hspan).
    intros q k. unfold L', lupd.
    assert (Ess : slot_start mt i = p0) by (unfold slot_start, slot_start_g; subst; reflexivity).
    rewrite Ess.
    destruct (Z.eq_dec q (p0 + 16 * OFF)) as [-> | Hne].
    - split.
      + intros E. injection E as <-. left. exists OFF. auto.
      + intros [(off & E & Eq) | (Hl & _)].
        * injection E as <- <-. reflexivity.
        * exfalso. apply (proj1 (wf_live_map A HW _ _)) in Hl.
          destruct Hl as (x & mtx & aibx & slx & j & off & Hx & Hrx & Hj0 & Hj & Eq).
          destruct (live_in_span_unique A x mtx aibx slx j off k ma mt aib slots i STaken HW Hx Hrx Hj0 Hj Hma Hr Hi0 Hi
                      ltac:(intros ch E; discriminate)) as [-> Eji].
          { rewrite <- Eq, Ess. destruct (stride_16 mt) as [q' Hq']. subst. unfold slot_end, slot_end_g.
            assert (16 * OFF <= mt_stride mt - 16) by llia. llia. }
          subst j. rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-. rewrite Hi in Hj. discriminate.
    - split.
      + intros Hl. right. split; [exact Hl | intros off n E; discriminate].
      + intros [(off & E & Eq) | (Hl & _)]; [| exact Hl].
        injection E as <- <-. exfalso. apply Hne. exact Eq.
  Qed.

  Lemma enframe_tail : forall (k : word -> M R) P,
    (forall s',
      WF (slot_set A ma i (SLive OFF nn) L') ->
      Rep (slot_set A ma i (SLive OFF nn) L') (ms_mem s') ->
      WIN s' -> ms_vm s' = ms_vm s -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
      rodata_clear (ms_mem s') ->
      (forall a : word, bv_unsigned a < p0 - 3 \/ e <= bv_unsigned a -> ms_mem s' a = ms_mem s a) ->
      (forall a : word, Pp <= bv_unsigned a < Pp + nn -> ms_mem s' a = ms_mem s a) ->
      tsafe (k (Z_to_bv 64 (p0 + 16 * OFF)) s') P) ->
    tsafe ((y <- (c <- m_lbu (Z_to_bv 64 (Pp - 3)) ;;
                  m_sb (Z_to_bv 64 (Pp - 3)) (v_or (v_slli (Z_to_bv 64 CODE) 5) (v_andi c 31)) ;;
                  mret (Z_to_bv 64 Pp)) ;; k y) s2) P.
  Proof using ECODE EMb EOFU EPp ERSV ES Ee Ep0 HOFF HOFU HR HROb HRSV HRb HS16 HSnn HW HWINb Hbf Hbi Hbo0 Hbo1 Hbz Hclear Hfrb Hhdrb Hheap Hhib Hi Hi0 Hi32 HiS Hlob Hma Hnn Hpayb Hr Hspan Hvmb MLok. pu_keep (ECODE, EMb, EOFU, EPp, ERSV, ES, Ee, Ep0, HOFF, HOFU, HR, HROb, HRSV, HRb, HS16, HSnn, HW, HWINb, Hbf, Hbi, Hbo0, Hbo1, Hbz, Hclear, Hfrb, Hhdrb, Hheap, Hhib, Hi, Hi0, Hi32, HiS, Hlob, Hma, Hnn, Hpayb, Hr, Hspan, Hvmb, MLok).
    intros k P HK.
    assert (HCODE : 0 <= CODE <= 5) by (subst CODE; llia).
    assert (HPp : p0 <= Pp /\ Pp + nn <= e) by (subst; llia).
    reassoc.
    eapply ts_lbu_mbyte; [exact HWINb | exact Hbi | ceil; subst; llia |].
    reassoc.
    rewrite v_andi_Z by llia. change 31 with (Z.ones 5). rewrite Z.land_ones by llia. change (2^5) with 32.
    rewrite (Z.mod_small i 32) by llia.
    rewrite v_slli_Z by llia. change (2^5) with 32.
    rewrite v_or_Z by llia. rewrite Z.lor_comm. change 32 with (2^5) at 1. rewrite lor_low_high by llia. change (2^5) with 32.
    eapply (ts_st_clear A HW); [exact HRb | exact HWINb | llia | intros j Hj; apply Hspan; llia
      | intros f Hf; destruct (Hclear f Hf); cbn [Z.of_nat]; llia |].
    intros HRf. cbn [ms_mem ms_vm upd].
    set (mf := wbytes (ms_mem s2) (Z_to_bv 64 (Pp - 3)) (word_to_le_bytes 1 (Z_to_bv 64 (i + CODE * 32)))) in *.
    apply ts_bind_ret.
    assert (Hmfout : forall x, 0 <= x < 2^64 -> x <> Pp - 3 -> mbyte mf x = mbyte (ms_mem s2) x).
    { intros x Hx Hne. unfold mf. apply mbyte_store_out; cbn [Z.of_nat]; llia. }
    assert (Hmfi : mbyte mf (Pp - 3) = Some (i + 32 * CODE)).
    { unfold mf. replace (Pp - 3) with (Pp - 3 + 0) at 2 by llia. rewrite mbyte_store_in by (cbn [Z.of_nat]; llia).
      rewrite byte_of_0, uZ by llia. rewrite Z.mod_small by llia. f_equal. llia. }
    assert (Hmffr : forall a : word, bv_unsigned a < p0 - 3 \/ e <= bv_unsigned a -> mf a = ms_mem s a).
    { intros a Ha. unfold mf. pose proof (u64_range a). rewrite wbytes_other_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat]; llia).
      apply Hfrb. exact Ha. }
    assert (Hmfpay : forall a : word, Pp <= bv_unsigned a < Pp + nn -> mf a = ms_mem s a).
    { intros a Ha. unfold mf. pose proof (u64_range a). rewrite wbytes_other_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat]; llia).
      apply Hpayb. exact Ha. }
    assert (HWF' : WF (slot_set A ma i (SLive OFF nn) L')).
    { apply (WF_slot_set A HW ma mt aib slots i STaken); try assumption.
      - left; reflexivity.
      - right. exists OFF, nn. reflexivity.
      - intros off n E. injection E as <- <-. rewrite <- ES. subst. llia.
      - exact L'_spec. }
    replace (Z_to_bv 64 Pp) with (Z_to_bv 64 (p0 + 16 * OFF)) by (rewrite EPp; reflexivity).
    apply (HK (upd s2 mf (ms_vm s2))); cbn [ms_mem ms_vm ms_lo ms_hi upd].
    - exact HWF'.
    - apply (Rep_slot_set A ma mt aib slots i (SLive OFF nn) Hma Hr Hi0) with (L := L'); [exact HRf |].
      + (* [comment removed for export] *)
        intros f x b Hin [Hx ->].
        unfold slot_fields, slot_fields_g, slot_start_g, slot_end_g in Hin.
        rewrite <- ES, <- EMb in Hin.
        replace (Mb + 16 + i * S) with p0 in Hin by llia.
        replace (p0 + S - 4) with e in Hin by llia.
        replace (p0 + 16 * OFF) with Pp in Hin by llia.
        replace (e - Pp - nn) with RSV in Hin by llia.
        replace ((Pp - Mb - 16) / 16) with OFU in Hin by llia.
        rewrite <- ECODE in Hin.
        assert (Rm0 : forall y, 0 <= y < 2^64 -> (y < p0 - 3 \/ e <= y) -> forall v, mbyte (ms_mem s) y = Some v -> mbyte mf y = Some v).
        { intros y Hy Hout v Hv. rewrite <- Hv. apply mbyte_ext.
          apply Hmffr. rewrite uZ by llia. exact Hout. }
        pose proof (rep_facts A (ms_mem s) HR) as RF.
        assert (Hz4 : mbyte (ms_mem s) (p0 - 4) = Some 0).
        { apply RF. exists (FCT (p0 - 4) 1 0). split; [| split; [cbn; llia | cbn [f_a f_v]; rewrite Z.sub_diag, byte_of_0; reflexivity]].
          right; right; right. exists ma, mt, aib, slots. split; [exact Hma | split; [exact Hr|]]. right.
          exists (Z.to_nat i), STaken. split; [exact Hi|]. rewrite Z2Nat.id by llia.
          unfold slot_fields, slot_fields_g, slot_start_g. cbn. left. rewrite Ep0, EMb, ES. reflexivity. }
        assert (Hze : mbyte (ms_mem s) e = Some 0).
        { apply RF. exists (FCT e 1 0). split; [| split; [cbn; llia | cbn [f_a f_v]; rewrite Z.sub_diag, byte_of_0; reflexivity]].
          right; right; right. exists ma, mt, aib, slots. split; [exact Hma | split; [exact Hr|]]. right.
          exists (Z.to_nat i), STaken. split; [exact Hi|]. rewrite Z2Nat.id by llia.
          unfold slot_fields, slot_fields_g, slot_end_g. cbn. right; left. rewrite Ee, Ep0, EMb, ES. reflexivity. }
        apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
        { destruct Hin as [<- | [<- | []]]; cbn [f_a f_n f_v] in Hx |- *.
          - replace x with (p0 - 4) by llia. rewrite Z.sub_diag, byte_of_0. apply (Rm0 (p0 - 4)); [llia | llia | exact Hz4].
          - replace x with e by llia. rewrite Z.sub_diag, byte_of_0. apply (Rm0 e); [llia | llia | exact Hze]. }
        repeat (apply in_app_iff in Hin; destruct Hin as [Hin | Hin]).
        * destruct (OFF =? 0) eqn:EO; [destruct Hin|]. apply Z.eqb_neq in EO.
          destruct (Hhdrb EO) as (B1 & B2 & B3 & B4).
          assert (HPp16 : p0 + 16 <= Pp) by (subst; llia).
          destruct Hin as [<- | [<- | [<- | []]]]; cbn [f_a f_n f_v] in Hx |- *.
          -- replace x with (p0 - 3) by llia. rewrite Hmfout by llia. rewrite Z.sub_diag, byte_of_0. exact B1.
          -- rewrite Hmfout by llia. destruct (Z.eq_dec x (p0 - 2)) as [-> | Hne].
             ++ replace (p0 - 2 - (p0 - 2)) with 0 by llia. rewrite byte_of_0. exact B2.
             ++ replace x with (p0 - 1) by llia. replace (p0 - 1 - (p0 - 2)) with 1 by llia. rewrite byte_of_1.
                rewrite (Z.mod_small (OFF / 256)) by (split; [apply Z.div_pos; llia | apply Z.div_lt_upper_bound; llia]). exact B3.
          -- replace x with (Pp - 4) by llia. rewrite Hmfout by llia. rewrite Z.sub_diag, byte_of_0. exact B4.
        * destruct Hin as [<- | [<- | []]]; cbn [f_a f_n f_v] in Hx |- *.
          -- replace x with (Pp - 3) by llia. rewrite Z.sub_diag, byte_of_0. rewrite Hmfi. f_equal.
             rewrite Z.mod_small by llia. llia.
          -- rewrite Hmfout by llia. destruct (Z.eq_dec x (Pp - 2)) as [-> | Hne].
             ++ replace (Pp - 2 - (Pp - 2)) with 0 by llia. rewrite byte_of_0. exact Hbo0.
             ++ replace x with (Pp - 1) by llia. replace (Pp - 1 - (Pp - 2)) with 1 by llia. rewrite byte_of_1. exact Hbo1.
        * destruct (RSV <? 5) eqn:ER; [destruct Hin|]. apply Z.ltb_ge in ER.
          destruct (Hbf ER) as [Bz5 Bk].
          destruct Hin as [<- | [<- | []]]; cbn [f_a f_n f_v] in Hx |- *.
          -- rewrite Hmfout by llia. replace x with (e - 4 + (x - (e - 4))) at 1 by llia. apply Bk. llia.
          -- replace x with (e - 5) by llia. rewrite Hmfout by llia. rewrite Z.sub_diag, byte_of_0. exact Bz5.
        * destruct (RSV =? 0) eqn:ER; [destruct Hin|]. apply Z.eqb_neq in ER.
          destruct Hin as [<- | []]; cbn [f_a f_n f_v] in Hx |- *.
          replace x with (Pp + nn) by llia. rewrite Hmfout by llia. replace (Pp + nn - (e - RSV)) with 0 by llia. rewrite byte_of_0. apply Hbz. exact ER.
    - apply WIN_upd. exact HWINb.
    - exact Hvmb.
    - exact Hlob.
    - exact Hhib.
    - unfold mf. apply rodata_clear_wbytes; [exact HROb | llia | rewrite ?length_N_to_le_bytes; cbn [Z.of_nat]; llia | rewrite ?length_N_to_le_bytes; cbn [Z.of_nat]; llia].
    - exact Hmffr.
    - exact Hmfpay.
  Qed.
End Tail.

End WithLayout.
