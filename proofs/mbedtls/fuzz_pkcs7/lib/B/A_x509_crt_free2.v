(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepCrt CrtFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_crt_free.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_mpi_read_binary_stmt A_platform_zeroize A_asn1_free_named_data_list_shallow A_asn1_sequence_free A_mpi_stmtA A_mpi_zeroize_and_free A_crt_stmts A_crt_free_stmt2 A_x509_crt_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Definition zchk_new : list Z := [0xaa08c; 0xaa090].
Lemma zchk_land7 x : Z.land x 7 = x mod 8. Proof. apply (Z.land_ones x 3); lia. Qed.
Local Ltac zchk_clear :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | (_ < _)%Z => fail | (_ <= _)%Z => fail | (_ > _)%Z => fail | (_ >= _)%Z => fail
      | (_ <= _ < _)%Z => fail | (_ < _ < _)%Z => fail | (_ <= _ <= _)%Z => fail | (_ < _ <= _)%Z => fail
      | @eq Z _ _ => fail | ~ (@eq Z _ _) => fail
      | _ => match type of T with Prop => clear H end
      end
  end.
Local Ltac zlia := zchk_clear; lia.
Local Ltac zchk_base :=
  first [ reflexivity
        | apply Z.ltb_lt; zlia | apply Z.ltb_ge; zlia | apply Z.leb_le; zlia | apply Z.leb_gt; zlia
        | apply Z.eqb_eq; zlia | apply Z.eqb_neq; zlia ].
Local Ltac zchk_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); zchk_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); zchk_rec
  | _ => zchk_base
  end.
Local Ltac zchk_solve :=
  rewrite ?zchk_land7;
  first [ reflexivity
        | unfold_cond; fold_lit_ux;
          repeat match goal with
                 | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by zlia
                 end;
          zchk_rec ].
Local Ltac zchk_if :=
  lazymatch goal with
  | |- _ (MS _ _ (if ?c then Z_to_bv 64 0xaa210 else _) _ _ _ _) =>
      replace c with false; [cbv_concl_iota | symmetry; zchk_solve]
  end.
Local Ltac zabsorb :=
  lazymatch goal with
  | |- _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch eval vm_compute in (List.existsb (Z.eqb pc) zchk_new) with true => step; zsimp end
  end.
Local Ltac zpre := repeat (first [ zchk_if | zabsorb ]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.
Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis HFREE : arl_free R = A_WRAP_FREE_CF.
  Hypothesis NEEDF : 0 <= arl_need_free R.
  Hypothesis NEEDA : 0 <= arl_need_amem R.
  Hypothesis NEEDM : 0 <= arl_need_malloc R.
  Hypothesis PZ : platform_zeroize_stmtA asegs R HIA A_PLATFORM_ZEROIZE.
  Hypothesis SHALLOW : asn1_free_named_data_list_shallow_stmtA asegs R HIA A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW.
  Hypothesis SEQFREE : asn1_sequence_free_stmtA asegs R HIA A_ASN1_SEQUENCE_FREE.
  Hypothesis ZFREE : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Variable PK : pk_class asegs.
  Variables (PHIpk : Z -> Z) (FFRpk : Z -> Z -> Z) (STKpk : Z).
  Hypothesis STKpk0 : 0 <= STKpk.
  Hypothesis PHIpk0 : forall k, 0 <= k -> 0 <= PHIpk k.
  Hypothesis FFRpk0 : forall k d, 0 <= k -> 0 <= d -> 0 <= FFRpk k d.
  Hypothesis PHIpk_mono : forall k k', 0 <= k <= k' -> PHIpk k <= PHIpk k'.
  Hypothesis FFRpk_mono : forall k k' d, 0 <= k <= k' -> FFRpk k d <= FFRpk k' d.
  Hypothesis PKFREE : pk_free_stmtA asegs R HIA PK PHIpk FFRpk STKpk A_PK_FREE.

  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2613344972.2200000?S1R5NEEDF5NEEDM". (* [comment removed for export] *)
  Let NRT : arl_need_free R <= arl_need_rt R /\ arl_need_amem R <= arl_need_rt R /\ 0 <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma blocks_apart_app : forall (L1 L2 : list blk) b1 b2,
    blocks_apart (L1 ++ L2) -> In b1 L1 -> In b2 L2 -> fst b1 + snd b1 <= fst b2 \/ fst b2 + snd b2 <= fst b1.
  Proof.
    induction L1 as [|[x y] L1 IH]; cbn; intros L2 b1 b2 H H1 H2; [destruct H1|].
    destruct H as [Hx H]. destruct H1 as [<-|H1].
    - cbn. destruct b2 as [B k]. cbn. apply Hx. apply in_app_iff. right. exact H2.
    - eapply IH; eauto.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L62420035243.28L64969942440.27L6899624530.27 00000800>00BS2FB1n1HS2FB1nS2FB". (* [comment removed for export] *)
  #[using="Type"] Lemma fdata_sub : forall LF' b, In b (fdata LF') -> exists fb, In fb LF' /\ fst fb <= fst b /\ fst b + snd b <= fst fb + snd fb.
  Proof.
    induction LF' as [|[FB n] r IH]; intros b Hb; [destruct Hb|].
    cbn [fdata] in Hb. destruct Hb as [E|[E|Hb]].
    - exists (FB, n). split; [left; reflexivity|]. subst b. cbn [fst snd]. split; [lia|]. pose proof (Z.le_min_r 24 n). lia.
    - exists (FB, n). split; [left; reflexivity|]. subst b. cbn [fst snd]. lia.
    - ddestruct (IH b Hb) as (fb & H1 & H2). exists fb. split; [right; exact H1| exact H2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Section Body.
    Variables (h : HST asegs R HIA) (LBo LB LF : list blk).
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
              (A : Z) (f : crt_own) (j : crt_junk) (lo d : Z).
    Hypothesis HH : HM asegs R HIA h (LBo ++ LB) LF m.
    Hypothesis HK0 : HK asegs R HIA h mo.
    Hypothesis OWN : crt_own_ok asegs PK m (LBo ++ LB) A f j.
    Hypothesis HAL : A mod 8 = 0.
    Hypothesis HA : 0 < A.
    Hypothesis AB : A + 744 <= 2 ^ 64.
    Hypothesis SUB : forall b, In b (crt_blocks f) -> In b LBo.
    Hypothesis NDO : List.NoDup (map fst (LBo ++ LB)).
    Hypothesis RAWSMALL : co_rawlen f < 2 ^ 40.
    Hypothesis CW : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) A 744.
    Hypothesis DS : A + 744 <= lo \/ bv_unsigned sp <= A.
    Hypothesis LOS : arl_stklo R <= lo.
    Hypothesis SLO : lo <= bv_unsigned sp - STKcf R STKpk.
    Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
    Hypothesis SPTOP : bv_unsigned sp <= htop asegs R HIA h.
    Hypothesis TP : tp = Z_to_bv 64 (arl_tp R).
    Hypothesis SPR : 0 <= bv_unsigned sp < 2 ^ 64.
    Hypothesis UWO : uw_obj R A 744 d.
    Hypothesis BUD : havol asegs R HIA h + PHIcf PHIpk (Z.of_nat (length (crt_blocks f))) <= AVOL_MAX.
    Hypothesis BUDF : hfr asegs R HIA h + FFRcf FFRpk (Z.of_nat (length (crt_blocks f))) d <= FR_MAX.

    Let ND : List.NoDup (map fst (crt_blocks f)).
    Proof. ddestruct OWN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N). exact N. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L29280787994.7400000:S2sp1A1d1H". (* [comment removed for export] *)
    Let D0 : 0 <= d. Proof. destruct UWO as [[_ H]|H]; lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L15756354262.4L18821501791.9L22069022898.5L29604608213.000000>00W00h00iS1R2lo3LOS3ALOS1B1k2B'2j'2FB1n2H12H22APS1R4DIMG1B1k4BimgS". (* [comment removed for export] *)
    #[using="R HIA DIMG h LB LF m lo HH CW LOS"] Lemma obj_apart : forall B k, In (B, k) LBo -> 0 < k -> B + k <= A \/ A + 744 <= B.
    Proof.
      intros B k HB Hk. destruct (hm_apart asegs R HIA h _ _ _ HH) as [BR BA]. rewrite Forall_forall in BR.
      ddestruct (BR (B, k) ltac:(apply in_app_iff; left; apply in_app_iff; left; exact HB)) as (B0 & _ & Bce & Bimg). cbn [fst snd] in B0, Bce, Bimg.
      pose proof (art_lo asegs R HIA) as ALO.
      eapply (client_wrange_apart L (LB ++ fdata LF) lo (htop asegs R HIA h) A 744 B k CW); [clear; lia| exact Hk| clear - ALO LOS; lia| exact Bce| clear - Bimg DIMG; lia|].
      intros B' j' Hb'. rewrite <- app_assoc in BA. apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb'].
      - exact (blocks_apart_app LBo (LB ++ LF) (B, k) (B', j') BA HB ltac:(apply in_app_iff; left; exact Hb')).
      - destruct (fdata_sub LF _ Hb') as ([FB n] & HF & H1 & H2). cbn [fst snd] in H1, H2.
        pose proof (blocks_apart_app LBo (LB ++ LF) (B, k) (FB, n) BA HB ltac:(apply in_app_iff; right; exact HF)) as AP. cbn [fst snd] in AP.
        clear - AP H1 H2. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Definition cinv (P : list blk) (Lc : list blk) (mc : mem) (moc : Model) (hc : HST asegs R HIA) : Prop :=
      HM asegs R HIA hc (Lc ++ LB) LF mc /\ HK asegs R HIA hc moc /\ mo_frame mo moc
      /\ htop asegs R HIA hc = htop asegs R HIA h /\ hstkhi asegs R HIA hc = hstkhi asegs R HIA h /\ hflag asegs R HIA hc = hflag asegs R HIA h
      /\ (forall x, hcs asegs R HIA h x -> hcs asegs R HIA hc x)
      /\ havol asegs R HIA hc <= havol asegs R HIA h + PHIcf PHIpk (Z.of_nat (length (crt_blocks f)))
      /\ hfr asegs R HIA hc <= hfr asegs R HIA h + FFRpk (Z.of_nat (length (crt_blocks f))) d + fr_charge d * Z.of_nat (length P)
      /\ (forall b, In b Lc -> In b LBo) /\ List.NoDup (map fst (Lc ++ LB))
      /\ (forall b, In b LBo -> ~ In (fst b) (map fst P) -> In b Lc)
      /\ (forall b, In b Lc -> In (fst b) (map fst P) -> fst b = co_rawp f /\ co_rawp f <> 0 /\ co_ob f <> Z_to_bv 64 1)
      /\ presW asegs R HIA h (Lc ++ LB) LF (bv_unsigned sp) (arl_stklo R) [(A, A + 744)] m mc
      /\ (exists jp : word, rw_cells asegs mc (bv_unsigned sp + -48) [C8 jp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      /\ rw_cells asegs mc A (crt_cells (pk0 f) j)
      /\ aobj asegs AL (hcs asegs R HIA h) mc A 744
      /\ mem_inv asegs mc /\ stk asegs mc lo (bv_unsigned sp + -48).

    (* [comment removed for export] *)

    #[using="PK LBo LB m A j OWN ND"] Lemma seg_nodup P S Rr : crt_blocks f = P ++ S ++ Rr -> List.NoDup (map fst S).
    Proof.
      intros E. pose proof ND as N. rewrite E, !map_app in N.
      apply NoDup_app_inv_r in N. apply NoDup_app_inv_l in N. exact N.
    Qed.

    #[using="PK LBo LB m A j OWN ND"] Lemma seg_nodup_nodes P ns nodes Rr : crt_blocks f = P ++ map (fun a => (a, ns)) nodes ++ Rr -> List.NoDup nodes.
    Proof. intros E. pose proof (seg_nodup _ _ _ E) as N. rewrite map_fst_map_pair in N. exact N. Qed.

    #[using="PK OWN SUB ND"] Lemma cinv_seg_in P S Rr Lc mc moc hc :
      cinv P Lc mc moc hc -> crt_blocks f = P ++ S ++ Rr -> forall b, In b S -> In b Lc.
    Proof.
      intros CI E b Hb. ddestruct CI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KEEP & _).
      apply KEEP; [apply SUB; rewrite E; apply in_or_app; right; apply in_or_app; left; exact Hb|].
      pose proof ND as N. rewrite E, !map_app in N.
      apply (NoDup_app_notin_l _ _ (fst b) N). apply in_or_app. left. apply in_map. exact Hb.
    Qed.

    #[using="UWO D0"] Lemma cinv_skip P S Lc mc moc hc : cinv P Lc mc moc hc ->
      (forall b, In b Lc -> In (fst b) (map fst S) -> fst b = co_rawp f /\ co_rawp f <> 0 /\ co_ob f <> Z_to_bv 64 1) ->
      cinv (P ++ S) Lc mc moc hc.
    Proof.
      intros CI HS. ddestruct CI as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8v & C9 & C10 & C11 & KEEP & REL & Crest).
      refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8v (conj _ (conj C10 (conj C11 (conj _ (conj _ Crest))))))))))))).
      - rewrite app_length, Nat2Z.inj_add. unfold fr_charge in *. clear - C9 D0. nia.
      - intros b Hb Hn. apply KEEP; [exact Hb|]. intros C. apply Hn. rewrite map_app. apply in_or_app. left. exact C.
      - intros b Hb Hin. rewrite map_app in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (REL b Hb Hin)| exact (HS b Hb Hin)].
    Qed.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L19652553279.1000000LS1R3HIA1h2sp1A2lo2DS1a2Ha2Hs". (* [comment removed for export] *)
    #[using="HIA h lo CW DS"] Lemma obj_client_range : forall LBx, (forall b, In b LB -> In b LBx) -> client_range L (LBx ++ fdata LF) (bv_unsigned sp + -48) A 744.
    Proof.
      intros LBx HI a Ha. destruct (CW a Ha) as [Hs|[Hd|(b & Hb & Hr)]].
      - left. clear - Hs Ha DS. lia.
      - right; left. exact Hd.
      - right; right. exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply HI, Hb| right; exact Hb].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L59308579027.100L59308693969.97 L59310827749.105L59314873579.103L64068264283.96 L64068264283.97 00000]01G02902b03403FS1R2sp1A2HA3SPR3buf3len1a3Hd14Bimg2G12G21H2H0S1R2sp1A2HA3SPR3buf3len2SP3HSP1a2Hs3Bce2G2S2sp1A2HA3SPR3buf3len1a2b'2Hr2G12G22FB1n2H12H23APFS2sp1A2HA3SPR3buf3len1a1B1k2Hr2G12G22NE1HS2sp1A3buf3len1a1HS2sp1A3buf3len1a1H". (* [comment removed for export] *)
    #[using="DIMG sp A HA SPR"] Lemma presA_drop_freed Lall mc (hc : HST asegs R HIA) buf len m' SP TOP :
      HM asegs R HIA hc Lall LF mc -> In (buf, len) Lall -> List.NoDup (map fst Lall) -> alloc_ceiling <= SP ->
      presA asegs R (lb_remove buf Lall) LF SP (arl_stklo R) TOP [(buf, buf + len)] mc m' ->
      presA asegs R (lb_remove buf Lall) LF SP (arl_stklo R) TOP [] mc m'.
    Proof.
      intros HHc HIN NDL HSP [P S]. split; [| exact S].
      intros a Ha Hc _. apply P; [exact Ha| exact Hc|]. cbn [outside]. split; [|exact I].
      destruct (hm_apart asegs R HIA hc _ _ _ HHc) as [BR AP]. rewrite Forall_forall in BR.
      destruct (BR _ ltac:(apply in_app_iff; left; exact HIN)) as (_ & _ & Bce & Bimg). cbn [fst snd] in Bce, Bimg.
      destruct (Z.lt_ge_cases a buf) as [|G1]; [lia|]. destruct (Z.lt_ge_cases a (buf + len)) as [G2|]; [|lia]. exfalso.
      destruct Hc as [Hs|[[Hd1 Hd2]|(b' & Hb' & Hr)]]; [lia| destruct DIMG; lia|].
      apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb'].
      - destruct b' as [B k]. cbn [fst snd] in Hr.
        assert (NE : buf <> B) by (intros E; exact (lb_remove_fst_neq _ _ _ NDL Hb' (eq_sym E))).
        assert (AP' : blocks_apart Lall) by (clear - AP; induction Lall as [|[x y] l IH]; cbn in *; [exact I|]; destruct AP as [A1 A2]; split; [intros B0 k0 H0; apply A1; apply in_app_iff; left; exact H0| apply IH; exact A2]).
        pose proof (blocks_apart_in2 _ _ _ _ _ AP' HIN (In_lb_remove _ _ _ Hb') NE). lia.
      - destruct (fdata_sub LF _ Hb') as ([FB n] & HF & H1 & H2).
        pose proof (blocks_apart_app Lall LF (buf, len) (FB, n) AP HIN HF) as APF. cbn [fst snd] in APF, H1, H2. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L15897747528.8 L2780121756.1  L40281191306.3 L42671303539.9 L48263424353.12L49631015752.1 L62018535662.1 00000K00O00X01701b01f01iS1R5STKpk3NRT2sp2lo3LOS3SLOS2spS1R3HIA1hS1R3HIA5PHIpk1h1f2hc2h'3HVc3HV'S1R3HIA5FFRpk1h1f1d1P5nodes2hc2h'4HFRc4HFR'S2spS1R". (* [comment removed for export] *)
    #[using="NEEDF NEEDM PK STKpk NRT OWN SUB CW DS LOS SLO ND"] Lemma cinv_after_chain P ns nodes Rr Lc mc moc hc m' mo' (h' : HST asegs R HIA) :
      cinv P Lc mc moc hc -> crt_blocks f = P ++ map (fun a => (a, ns)) nodes ++ Rr ->
      HM asegs R HIA h' (lb_remove_all nodes (Lc ++ LB)) LF m' -> HK asegs R HIA h' mo' -> mo_frame moc mo' ->
      htop asegs R HIA h' = htop asegs R HIA hc -> hstkhi asegs R HIA h' = hstkhi asegs R HIA hc -> hflag asegs R HIA h' = hflag asegs R HIA hc ->
      (forall x, hcs asegs R HIA hc x -> hcs asegs R HIA h' x) ->
      havol asegs R HIA h' <= havol asegs R HIA hc -> hfr asegs R HIA h' <= hfr asegs R HIA hc + fr_charge d * Z.of_nat (length nodes) ->
      presA asegs R (lb_remove_all nodes (Lc ++ LB)) LF (bv_unsigned sp + -48) (arl_stklo R) (hstkhi asegs R HIA hc) [] mc m' ->
      mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp + -48) ->
      cinv (P ++ map (fun a => (a, ns)) nodes) (lb_remove_all nodes Lc) m' mo' h'.
    Proof.
      intros CI E HH' HK' MF' HT' HS' HF' HCS' HV' HFR' HP MI' ST'.
      pose proof (seg_nodup_nodes _ _ _ _ E) as NDn.
      assert (HINn : forall x, In x nodes -> In x (map fst Lc)).
      { intros x Hx. replace x with (fst (x, ns)) by reflexivity. apply in_map.
        eapply (cinv_seg_in _ _ _ _ _ _ _ CI E). apply in_map_iff. exists x. auto. }
      rewrite (lb_remove_all_app_l nodes Lc LB NDn HINn) in HH', HP.
      ddestruct CI as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & SUBLc & NDL & KEEPc & RELc & HPXc & [jp FR] & CELLS & OBJc & MIc & STc).
      assert (NDL' : List.NoDup (map fst (lb_remove_all nodes Lc ++ LB))).
      { rewrite <- (lb_remove_all_app_l nodes Lc LB NDn HINn). clear - NDL. generalize (Lc ++ LB) NDL. clear. intros l NDL. revert l NDL.
        induction nodes as [|a r IH]; cbn; intros l NDL; [exact NDL|]. apply IH. apply nodup_fst_lb_remove. exact NDL. }
      assert (NDLc : List.NoDup (map fst Lc)) by (rewrite map_app in NDL; apply NoDup_app_inv_l in NDL; exact NDL).
      assert (SUBL' : forall b, In b (lb_remove_all nodes Lc ++ LB) -> In b (Lc ++ LB)).
      { apply lb_sub_app. intros b Hb. eapply In_lb_remove_all; exact Hb. }
      pose proof (art_lo asegs R HIA) as ALO. pose proof (hcs_ok asegs R HIA h) as CSOK.
      split; [exact HH'|]. split; [exact HK'|]. split; [eapply mo_frame_trans; eassumption|].
      split; [congruence|]. split; [congruence|]. split; [congruence|].
      split; [intros x Hx; apply HCS', HCSc, Hx|].
      split; [clear - HV' HVc; lia|].
      split; [rewrite app_length, map_length, Nat2Z.inj_add; clear - HFR' HFRc; lia|].
      split; [intros b Hb; apply SUBLc; eapply In_lb_remove_all; exact Hb|]. split; [exact NDL'|].
      split.
      { intros b Hb Hn. apply In_lb_remove_all_keep.
        - apply KEEPc; [exact Hb|]. intros C. apply Hn. rewrite map_app. apply in_or_app. left. exact C.
        - intros C. apply Hn. rewrite map_app. apply in_or_app. right. rewrite map_fst_map_pair. exact C. }
      split.
      { intros b Hb Hin. rewrite map_app in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
        - apply RELc; [eapply In_lb_remove_all; exact Hb| exact Hin].
        - exfalso. rewrite map_fst_map_pair in Hin. exact (lb_remove_all_fst_notin _ _ _ NDLc Hb Hin). }
      split.
      { eapply presW_call; [eapply (presW_sub_blocks_fn asegs R HIA); [exact HPXc| exact SUBL']| exact HP| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| rewrite HSc; clear; lia| intros x _; exact I]. }
      split; [exists jp; eapply presA_rw_cells; [exact HP| exact FR| apply client_range_stack; cbn; clear; lia| exact I]|].
      split; [eapply presA_rw_cells; [exact HP| exact CELLS| replace (Z.of_nat (cells_size (crt_cells (pk0 f) j))) with 744 by reflexivity; apply obj_client_range; intros b Hb; apply in_app_iff; right; exact Hb| exact I]|].
      split; [eapply presA_aobj0; [exact CSOK| exact HP| exact OBJc| intros x Hx; rewrite HSc; eapply hcs_below_top; exact Hx| right; split; [apply obj_client_range; intros b Hb; apply in_app_iff; right; exact Hb| unfold STKcf in SLO; clear - LOS SLO STKpk0 NRT; lia]]|].
      split; [exact MI'| exact ST'].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Notation POST := (x509_crt_free_postA2 asegs R HIA (PHIcf PHIpk) (FFRcf FFRpk)
                              h LBo LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A f lo d m mo).
    Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).

    (* [comment removed for export] *)
    Definition from (pc : Z) (P : list blk) : Prop :=
      forall Lc mc moc hc (x1 x5 x6 x7 : word) x10 x11 x12 x13 x14 x15 x16 x17 s3v x28 x29 x30 x31,
        cinv P Lc mc moc hc ->
        aevtS asegs POST
          (mkCfg (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 (al_sb AL)) s3v s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 pc) fc None mc (seg_rom asegs)) moc).

    #[using="Type"] Lemma cinv_remodel P Lc mc moc hc mo' : cinv P Lc mc moc hc -> HK asegs R HIA hc mo' -> mo_frame moc mo' -> cinv P Lc mc mo' hc.
    Proof.
      intros CI HK' MF'. ddestruct CI as (C1 & C2 & C3 & Crest). split; [exact C1|]. split; [exact HK'|]. split; [eapply mo_frame_trans; [exact C3| exact MF']| exact Crest].
    Qed.

    (* [comment removed for export] *)
    Ltac goto Lm :=
      let K := fresh "K" in let mo1 := fresh "mo" in let HK1 := fresh "HKg" in let MF1 := fresh "MFg" in
      pose proof Lm as K; unfold from in K;
      intros mo1 [HK1 MF1]; eapply K; clear K; eapply cinv_remodel; [| exact HK1| exact MF1].

    Ltac cinv_open CI :=
      destruct CI as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & SUBLc & NDc & KEEPc & RELc & HPXc & [jp FR] & CELLS & OBJc & MIc & STc);
      unfold crt_cells in CELLS;
      cbn [pk0 co_ob co_rawlen co_rawp co_issuer_next co_issuer co_subject_next co_subject co_pkinfo co_pkctx co_pkowned
           co_san_next co_san co_akid_next co_akid co_pol_next co_pol co_eku_next co_eku co_sigopts] in CELLS.

    Ltac facts :=
      pose proof (hcs_ok asegs R HIA h) as CSOK; pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_val R) as ACV;
      pose proof (hm_top asegs R HIA h _ _ _ HH) as HTOP; pose proof (hcs_stack asegs R HIA h) as SCS0;
      pose proof IMG as IMG'; unfold asan_img_ok in IMG'; unfold STKcf in SLO;
      assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by
        (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STKpk0 NRT SPTOP HTOP; lia]);
      lazymatch goal with HHc : HM _ _ _ ?hc _ _ ?mc |- _ => pose proof (hm_wlow asegs R HIA hc _ _ mc HHc) as WLc end.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0120@C17025492443.147C31740276271.148D16049893661.149D60109446735.149K13100251734.147K30199128561.147K6518702880.147 L11741095640.143L13093679425.2  L14791142800.11 L23086053406.1  L26924648792.143L27911231108.143L28132161751.5  L28814037385.143L29604608213.0  L30212436884.3  L34423640368.7  L35653441506.11 L43654564952.143L49788159649.0  L51709111996.142L52460656417.4  L53056398486.2  L5348938364.127 L54695856470.8  L59499841752.143L60098763854.3  L6514053445.2   L66151427842.16 L7510805464.143 L861591149.2    L881835912.0    O17025492443.147O37383812214.147O49587672251.147P6518702880.147 Q10224802669.129Q14790846236.129Q15647878503.143Q15766564435.148Q16191576493.128Q16203753099.129Q18361895783.143Q20409902095.129Q32659924583.143Q33913700356.143Q36856420847.148Q37703787028.148Q37703787028.149Q38248387216.148Q38248387216.149Q3834260612.143 Q39935065476.143Q43879899724.148Q43879899724.149Q44652743143.143Q48217684537.148Q50840533351.148Q51223049447.143Q64119853238.148Q64119853238.149Q6445967924.128 Q66534486788.143Q9321803270.128 Q9838812676.143 00000100400500L00j01@01A01Q01R02902:02J02l03>03W03X03Y04004P04`04a05105=05D05Z06506E06O06P06k07;07A07B07C07D07E07F07a08J08[09109>09K09\09i0::0:S0:T0:a0:n0;<0;J0;c0<<0<M0<^0<o0=<0=M0=^0=k0>80>E0>^0>k0?DFS1AFS1R5STKpk2sp1A1f2lo3LOSS1R5STKpk3NRT2sp1A1f2lo2DS3SLOS1R5STKpk2sp1A1f2lo2DSFS1R5STKpk2sp1A1fFS1R5STKpk3NRT2sp2lo3LOS3SLO3SPR3ALO3ACVFS1R5STKpk2sp1A1fS1R5STKpk3NRT2sp1A1f2lo2HA3SLO3SPRS1R3HIA1h2sp5SPTOPS1R5STKpk2sp1A1f2HA2AB2KESFS1R5STKpk3NRT2sp2lo3SLOS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPS1R5STKpk2sp1A1fSS1R5STKpk2sp1A1fS2sp1A2lo2DSS2sp2loS1R5STKpk2sp1A1f2HA2ABS1R3HIA5FFRpk1h1f1d2hc4HFRcS1R5STKpk2sp1A1fS1R2lo3LOSFS2sp2r04SP161q1r1H2H02q02H4S1R5STKpk2sp1A1fS1d2D0SFFFFS1R5STKpk2sp1A1f3HAL2HA3SPRS1R5STKpk3NRT2sp1f2lo3LOS3SLO3SPR3ALO3ACVS1R5STKpk2sp1f2loS1R5STKpk1f2lo3LOS3ALOS1R5STKpk1A1fS1R5STKpk1A1fS1R5STKpk2sp1f2loS1R5STKpk1A1fS1R5STKpk2sp1f2loS1R5STKpk3NRT2sp1f2lo3SLOFS1R5STKpk1A1fS1R5STKpk1A1fS1R5STKpk1f2loS1R5STKpk1f2loS1R5STKpk3NRT2sp1f2lo3SLOS1R5STKpk3NRT2sp1f2lo3SLOS1R5STKpk2sp1f2loS1R5STKpk2sp1f2loS1R5STKpk2sp1f2loS1R5STKpk1A1fS1R5STKpk2sp1f2loS1R5STKpk2sp1f2loS1R5STKpk1A1fS1R5STKpk1A1fS1R5STKpk1A1fS1R5STKpk3NRT2sp1f2lo3SLOS1R5STKpk1A1fS1R5STKpk3NRT2sp1f2lo3SLO". (* [comment removed for export] *)
    #[using="IMG NEEDF NEEDM PZ STKpk NRT HH HAL HA AB CW DS LOS SLO SP16 SPTOP SPR UWO D0"] Lemma from_a9a6c : from 0xaa1b0 (crt_blocks f).
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3v x28 x29 x30 x31 CI. cinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc.
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSc| exact SCS]).
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc0 _) => rename mc0 into m1 end.
      apply rw_cells_CB_of in CELLS; [| cbn; clear; lia]. cbn [cells_size csize Nat.add] in CELLS. change 744%nat with (Z.to_nat 744) in CELLS at 1.
      pose proof PZ as SPZ. unfold platform_zeroize_stmtA, A_PLATFORM_ZEROIZE in SPZ. specialize SPZ with (h := hc). rewrite HTc in SPZ.
      acallxA_sp (bv_unsigned sp + -48)
        (eapply SPZ with (LB := Lc ++ LB) (LF := LF) (A := A) (n := 744) (lo := lo);
         rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by (clear - SPR SLO STKpk0 NRT LOS ALO ACV; lia);
         first [ exact HHc | exact CELLS | exact HA | exact LOS | exact OBJcc | reflexivity
               | lazymatch goal with
                 | |- 0 <= 744 => clear; lia
                 | |- 744 < _ => clear; lia
                 | |- stk _ m1 lo _ => assumption
                 | |- lo <= _ => clear - SLO STKpk0 NRT; lia
                 | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                 | |- _ mod 16 = 0 => clear - SP16; Z.div_mod_to_equations; lia
                 | |- A + 744 <= lo \/ _ => clear - DS; lia
                 | |- mem_inv _ m1 => assumption
                 | |- client_wrange _ _ _ _ A 744 => eapply client_wrange_sp_mono; [| eapply client_wrange_mono; [exact CW| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]]]; clear - LOS; lia
                 end
               | match goal with |- ?g => idtac "PZ-LEFT:" g end ]).
      clear SPZ.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc0 _) => rename mc0 into m2 end.
      (* [comment removed for export] *)
      zstep. if_cases KE; zify_cond KE; [| exfalso; apply KE; reflexivity]. clear KE.
      zstep. zstep.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc0 _) => rename mc0 into m3 end.
      lazymatch goal with FRo : rw_cells _ m3 (bv_unsigned sp + -48) _, STo : stk _ m3 lo (bv_unsigned sp + -48) |- _ => release_frame FRo STo (bv_unsigned sp) end.
      apply aevtA_done. intros mo9 [HK9 MF9]. unfold x509_crt_free_postA2.
      deexists 15. dexists m3, mo9, hc, Lc.
      split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [eapply mo_frame_trans; [exact MFc| exact MF9]|].
      split; [lazymatch goal with H : presW _ _ _ _ _ _ _ _ _ m m3 |- _ => exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ H) end|].
      split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HK9|]. split; [exact HCSc|].
      split; [exact HVc|].
      split; [unfold FFRcf; rewrite ?(Z.max_r 0 (fr_charge d)) by (unfold fr_charge; clear - D0; lia); clear - HFRc; lia|].
      split; [assumption|]. split; [exact SUBLc|]. split; [exact KEEPc|].
      split; [unfold crt_zero, CRT_SIZE; lazymatch goal with H : rw_cells _ m3 A _ |- _ => exact H end|].
      intros HOB b Hb Hin. ddestruct (RELc b Hb Hin) as (_ & RP0 & OB1). destruct HOB as [HOB|HOB]; [exact (RP0 HOB)| exact (OB1 HOB)].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L16476774744.4L26892418956.1L36321365490.200000:00>00FS1A2ns1x1HS2spS2ns3Hns". (* [comment removed for export] *)
    #[using="PK DIMG HH OWN SUB CW LOS ND"] Lemma cinv_chain P ns no NP nodes Rr Lc mc moc hc a :
      cinv P Lc mc moc hc -> crt_blocks f = P ++ map (fun a => (a, ns)) nodes ++ Rr ->
      chain asegs ns no NP m (LBo ++ LB) a nodes -> 0 < ns ->
      chain asegs ns no NP mc (Lc ++ LB) a nodes.
    Proof.
      intros CI E HC Hns. pose proof CI as CI'. ddestruct CI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPX & _).
      eapply (CrtFacts.chain_presx asegs L) with (SP := bv_unsigned sp) (X := [(A, A + 744)]); [exact HC| | | clear - Hns; lia|].
      - intros x Hx. apply in_or_app. left. eapply (cinv_seg_in _ _ _ _ _ _ _ CI E). apply in_map_iff. exists x. auto.
      - eapply CrtFacts.heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h _ LF _ _ _ _ _ HPX))| intros b Hb; apply in_app_iff; left; exact Hb| clear; lia| intros x Hx; exact Hx].
      - intros x Hx. cbn [disjoint_from]. split; [| exact I].
        pose proof (obj_apart x ns (SUB _ ltac:(rewrite E; apply in_app_iff; right; apply in_app_iff; left; apply in_map_iff; exists x; auto)) Hns). clear - H. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Definition SNAME (l : list Z) : list blk := map (fun a => (a, NAME_SIZE)) l.
    Definition SSEQ (l : list Z) : list blk := map (fun a => (a, SEQ_SIZE)) l.
    Definition P1 : list blk := co_pkowned f.
    Definition P2 : list blk := P1 ++ oblk (co_sigopts f) 8.
    Definition P3 : list blk := P2 ++ SNAME (co_issuer f).
    Definition P4 : list blk := P3 ++ SNAME (co_subject f).
    Definition P5 : list blk := P4 ++ SSEQ (co_eku f).
    Definition P6 : list blk := P5 ++ SSEQ (co_san f).
    Definition P7 : list blk := P6 ++ SSEQ (co_pol f).
    Definition P8 : list blk := P7 ++ SSEQ (co_akid f).

    Ltac crt_blocks_eq := unfold P8, P7, P6, P5, P4, P3, P2, P1, SNAME, SSEQ, crt_blocks; repeat rewrite <- app_assoc; cbn [map app]; reflexivity.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L46515235128.77L57506378654.81L594523655.81  L9204387439.81 00000A00O00\01>S1R3LBo2LB2sp1A1fS1R2sp1A1f3BceS2sp1A1f4HLENS1R2sp1A1f2HA3SPR4HLEN4ACP'2B03Bce". (* [comment removed for export] *)
    #[using="HIA PK h LF sp m A j HH OWN HA SPR"] Lemma rawp_range : 0 <= co_rawp f < 2 ^ 64 /\ (co_rawp f <> 0 -> co_rawp f + co_rawlen f <= alloc_ceiling /\ 0 <= co_rawlen f /\ In (co_rawp f, co_rawlen f) (LBo ++ LB)).
    Proof.
      ddestruct OWN as (_ & _ & _ & _ & _ & _ & _ & RAW & _).
      pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (alloc_ceiling_val R) as ACP'.
      destruct RAW as [E|(HIN & HLEN & _)]; [rewrite E; lia|].
      destruct (hm_apart asegs R HIA h _ _ _ HH) as [BR _]. rewrite Forall_forall in BR.
      destruct (BR _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & Bce & _). cbn [fst snd] in B0, Bce.
      split; [lia|]. intros _. split; [lia|]. split; [lia| exact HIN].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00`0@L12281975186.3  L14791142800.11 L14915251665.1  L1605711958.9   L16434433161.6  L28132161751.5  L28813939468.3  L28814039836.131L29500693318.3  L31056727547.132L32195670001.132L34423640368.7  L35653441506.11 L36219419518.1  L40644610849.0  L41784058682.3  L4692408284.9   L49041329788.130L592190672.3    L59308632178.1  L594257362.2    L60098763854.3  L60675383808.4  L60845523811.50 L6183029738.1   L66151427842.16 L67059943649.5  L861591149.2    L9168957625.1   L987010204.137  Q10518214799.132Q10909083777.133Q21865302287.134Q30848934534.131Q37708009648.133Q37708161426.132Q40509833325.134Q45124942924.133Q49303129386.133Q49303289227.134Q4961445812.131 Q52624729581.132Q55318000941.131Q55330458123.132Q58952506035.133Q65067231394.133Q7685922389.132 Q953959757.132  00000700^00a01=01Q01c01l02@02H02\02j03=03]03`03a04104P04d04n05205905C05M08208508P08a08g08j09809C09N09Y09d09o0::0:S0:l0;70;B0;M0;f0<10<<0<G0<R0<]0<hS1A1f1HS1R5STKpk3NRT2sp2lo3LOS3SLO3SPR3ALO3ACVS1AS1R3HIA5PHIpk1h1f3BUD2hc3HVcS1R3HIA1d2hc2h'4HFR'S1R3HIA1h2sp5SPTOPS1A2HA2ABS1R5STKpk2sp1A2HA2ABS1f2KR1eS1R5STKpk2sp1A2HA2ABS1R5STKpk2sp1AS1R5STKpk2sp2lo3SLOS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPS1fSS1f8RAWSMALL3RB2S1R5STKpk3NRT2sp2lo3LOS3SLO3ALOS1R5STKpk2sp1A2HA2ABS1f3RB22L0S2KOS1f3RB2S1R2lo3LOSS1f2KR1b1nS1R3HIA5PHIpk5FFRpk1h3LBo2LB2LF2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m2mo1A1f2lo1d2mc3moc2hc2x52x62x73x133x143x153x163x173s3v3x283x293x303x312KR2R0S1fS2sp2r04SP161q1r1H2H02q02H4S1R3HIA2hc2h'3HV'S1d2D0S1fS1R5STKpk2sp1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk2sp1A3HAL2HA3SPRS1R5STKpk2sp1A3HAL2HA3SPRS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk2sp1A3HAL2HA3SPRS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1A". (* [comment removed for export] *)
    #[using="IMG NEEDF NEEDM PZ ZFREE PK STKpk PHIpk0 DIMG NRT HH OWN HAL HA AB SUB RAWSMALL CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND D0"] Lemma from_a9a1c : from 0xaa160 P8.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3v x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc.
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSc| exact SCS]).
      pose proof rawp_range as (RB0 & RBnz).
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases KR; zify_cond KR.
      { (* [comment removed for export] *)
        goto from_a9a6c. replace (crt_blocks f) with (P8 ++ oblk (co_rawp f) (co_rawlen f)) by crt_blocks_eq.
        apply cinv_skip; [exact CI0| intros b _ Hin; exfalso; revert Hin; unfold oblk; rewrite ?unsigned_lit in KR by (clear - RB0; lia);
                            destruct (Z.eqb_spec (co_rawp f) 0); [intros []| clear - KR n; lia]]. }
      rewrite ?unsigned_lit in KR by (clear - RB0; lia).
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases KO; zify_cond KO.
      { (* [comment removed for export] *)
        goto from_a9a6c. replace (crt_blocks f) with (P8 ++ oblk (co_rawp f) (co_rawlen f)) by crt_blocks_eq.
        apply cinv_skip; [exact CI0|]. intros b _ Hin. unfold oblk in Hin. destruct (Z.eqb_spec (co_rawp f) 0) as [E0|NE0]; [destruct Hin|].
        cbn in Hin. destruct Hin as [Hin|[]]. split; [symmetry; exact Hin|]. split; [exact NE0|].
        intros EOB. rewrite EOB in KO. revert KO. clear. intros KO. exfalso. vm_compute in KO. lia. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      ddestruct (RBnz KR) as (RB1 & RB2 & RIN). clear RBnz.
      assert (E8 : crt_blocks f = P8 ++ map (fun a => (a, co_rawlen f)) [co_rawp f] ++ []).
      { unfold P8, P7, P6, P5, P4, P3, P2, P1, SNAME, SSEQ, crt_blocks. unfold oblk at 2.
        destruct (Z.eqb_spec (co_rawp f) 0); [clear - KR e; lia|]. repeat rewrite <- app_assoc. cbn [map app]. reflexivity. }
      assert (HIN : In (co_rawp f, co_rawlen f) (Lc ++ LB)).
      { apply in_or_app. left. eapply (cinv_seg_in _ _ _ _ _ _ _ CI0 E8). left. reflexivity. }
      assert (LEN8 : Z.of_nat (length (crt_blocks f)) = Z.of_nat (length P8) + 1) by (rewrite E8, !app_length; cbn [length map]; lia).
      ddestruct OWN as (_ & _ & _ & _ & _ & _ & _ & RAW & _).
      destruct RAW as [R0|(_ & _ & RAWC)]; [clear - KR R0; lia|].
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc0 _) => rename mc0 into m1 end.
      assert (RAWC1 : rw_cells asegs m1 (co_rawp f) [CB (Z.to_nat (co_rawlen f)) (cj_raw j)]).
      { destruct (Z.eq_dec (co_rawlen f) 0) as [L0|L0].
        - rewrite L0 in RAWC |- *. change (Z.to_nat 0) with 0%nat in RAWC |- *. eapply rw_cells_CB0. exact RAWC.
        - lazymatch goal with HP : presW _ _ _ _ _ _ _ _ _ m m1 |- _ =>
            eapply presA_rw_cells; [exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ HP)| exact RAWC| |] end.
          + cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RB2; lia). eapply client_range_block; [apply in_app_iff; left; exact HIN| clear; lia| clear; lia].
          + cbn [cells_size csize disjoint_from]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RB2; lia).
            pose proof (obj_apart _ _ (SUB _ ltac:(rewrite E8; apply in_app_iff; right; left; reflexivity)) ltac:(clear - RB2 L0; lia)). clear - H. lia. }
      clear RAWC.
      (* [comment removed for export] *)
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply ZFREE with (h := hc) (LB := Lc ++ LB) (LF := LF) (buf := co_rawp f) (len := co_rawlen f) (lo := lo) (d := d) (junk := cj_raw j);
          rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by (clear - SPR SLO STKpk0 NRT LOS ALO ACV; lia); rewrite ?HTc, ?HSc;
          first [ exact HHc | exact HK1 | exact LOS | exact TP | exact MIc | reflexivity
                | lazymatch goal with
                  | |- _ \/ (In _ _ /\ _) => right; split; [exact HIN| exact RAWC1]
                  | |- 0 <= co_rawlen f < _ => clear - RB2 RAWSMALL; lia
                  | |- stk _ m1 lo _ => assumption
                  | |- lo <= _ => clear - SLO STKpk0 NRT; lia
                  | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                  | |- _ mod 16 = 0 => clear - SP16; Z.div_mod_to_equations; lia
                  | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold AVOL_CALL; unfold PHIcf in HVc, BUD; pose proof (PHIpk0 (Z.of_nat (length (crt_blocks f))) ltac:(clear; lia)); clear - HVc BUD H; lia
                  | |- uwc _ _ _ _ _ _ _ => rewrite (unsigned_lit A) by (clear - HA AB; lia); eapply uw_obj_uwc; [exact UWO| clear; lia]
                  | |- hfr _ _ _ _ + _ <= FR_MAX => unfold FFRcf in BUDF; rewrite ?(Z.max_r 0 (fr_charge d)) in BUDF by (unfold fr_charge; clear - D0; lia); clear - HFRc BUDF LEN8 D0; unfold fr_charge in *; nia
                  end
                | match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end ]. }
      cbv beta. (intros ms' mo'x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & mo' & h'
                      & E & MI' & ST' & MF' & HP' & HT' & HS' & HF' & HK' & HCS' & HV' & HFR' & HH').
      injection E as Ems Emo. subst ms' mo'x.
      replace (ret_pc (Z_to_bv 64 0xaa1b0)) with (Z_to_bv 64 0xaa1b0 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST', HP' by (clear - SPR SLO STKpk0 NRT LOS ALO ACV; lia).
      pose proof (presA_drop_freed (Lc ++ LB) m1 hc (co_rawp f) (co_rawlen f) m' (bv_unsigned sp + -48) _ HHc HIN NDc ltac:(clear - SLO STKpk0 NRT LOS ALO; lia) HP') as HP''.
      pose proof (cinv_after_chain _ (co_rawlen f) [co_rawp f] [] _ _ _ _ _ _ _ (cinv_remodel _ _ _ _ _ _ CI0 HK1 MF1) E8 HH' HK' MF' HT' HS' HF' HCS'
                    ltac:(unfold AVOL_CALL in HV'; clear - HV'; lia) ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HFR'; lia) HP'' MI' ST') as CI1.
      pose proof from_a9a6c as K. unfold from in K. eapply K. replace (crt_blocks f) with (P8 ++ map (fun a => (a, co_rawlen f)) [co_rawp f]) by (rewrite E8, app_nil_r; reflexivity).
      exact CI1.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Ltac list_free_call CALLEE ENTRYDEF CH NDn E NEXT retpc :=
      lazymatch goal with |- _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with HHc : HM _ _ _ ?hc (?Lc ++ LB) LF m1, CI0 : cinv _ ?Lc m1 ?moc ?hc, MIc : mem_inv _ m1, HVc : havol _ _ _ ?hc <= _, HFRc : hfr _ _ _ ?hc <= _ |- _ =>
      lazymatch type of E with crt_blocks f = ?P ++ map _ ?nodes0 ++ ?Rr0 =>
      eapply aevtA_call;
      [ let mo1 := fresh "mo" in let HK1 := fresh "HK" in let MF1 := fresh "MF" in
        intros mo1 [HK1 MF1];
        let SP := fresh "SPEC" in pose proof CALLEE as SP; unfold ENTRYDEF in SP;
        eapply SP with (h := hc) (LB := Lc ++ LB) (LF := LF) (lo := lo); clear SP;
        rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by (let A1 := fresh in let A2 := fresh in pose proof (art_lo asegs R HIA) as A1; pose proof (alloc_ceiling_val R) as A2; unfold STKcf in SLO; clear - SPR SLO STKpk0 NRT LOS A1 A2; lia);
        lazymatch goal with HTc : htop _ _ _ hc = _, HSc : hstkhi _ _ _ hc = _ |- _ => rewrite ?HTc, ?HSc | _ => idtac end;
        first [ exact HHc | exact HK1 | exact CH | exact NDn | exact LOS | exact TP | exact MIc | reflexivity
              | lazymatch goal with
                | |- stk _ m1 lo _ => assumption
                | |- lo <= _ => clear - SLO STKpk0 NRT; lia
                | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                | |- _ mod 16 = 0 => clear - SP16; Z.div_mod_to_equations; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold AVOL_CALL; rewrite Z.mul_0_r, Z.add_0_r; unfold PHIcf in HVc, BUD;
                      let PH := fresh "PH" in pose proof (PHIpk0 (Z.of_nat (length (crt_blocks f))) ltac:(clear; lia)) as PH; clear - HVc BUD PH; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX =>
                      let LEN := fresh "LEN" in
                      assert (LEN : length (crt_blocks f) = (length P + (length nodes0 + length Rr0))%nat)
                        by (rewrite E at 1; rewrite !app_length, map_length; reflexivity);
                      apply (f_equal Z.of_nat) in LEN; rewrite !Nat2Z.inj_add in LEN;
                      unfold FFRcf in BUDF; rewrite ?(Z.max_r 0 (fr_charge d)) in BUDF by (unfold fr_charge; clear - D0; lia); unfold fr_charge in *; clear - HFRc BUDF D0 LEN; nia
                end
              | match goal with |- ?g => idtac "LF-PRE-LEFT:" g end ]
      | cbv beta;
        let ms' := fresh "ms'" in let mox := fresh "mox" in let mo1 := fresh "mo" in let HK1 := fresh "HK" in let MF1 := fresh "MF" in let PO := fresh "PO" in
        intros ms' mox (mo1 & [HK1 MF1] & PO);
        let m' := fresh "m'" in let mo' := fresh "mo'" in let h' := fresh "h'" in
        destruct PO as (?w0 & ?w1 & ?w2 & ?wa0 & ?wa1 & ?wa2 & ?wa3 & ?wa4 & ?wa5 & ?wa6 & ?wa7 & ?w3 & ?w4 & ?w5 & ?w6 & m' & mo' & h'
                        & ?EE & ?MI' & ?ST' & ?MF' & ?HP' & ?HT' & ?HS' & ?HF' & ?HK' & ?HCS' & ?HV' & ?HFR' & ?HH');
        lazymatch goal with EE : mkCfg ms' mox = mkCfg _ _ |- _ => injection EE as ?Ems ?Emo; subst ms' mox end;
        replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]);
        lazymatch goal with ST' : stk _ m' lo _, HP' : presA _ _ _ _ _ _ _ _ m1 m', HT' : htop _ _ _ h' = _, HS' : hstkhi _ _ _ h' = _, HF' : hflag _ _ _ h' = _,
                            HK' : HK _ _ _ h' mo', HCS' : forall x, _ -> hcs _ _ _ h' x, HV' : havol _ _ _ h' <= _, HFR' : hfr _ _ _ h' <= _,
                            HH' : HM _ _ _ h' _ LF m', MI' : mem_inv _ m', MF' : mo_frame mo1 mo' |- _ =>
          rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST', HP' by (let A1 := fresh in let A2 := fresh in pose proof (art_lo asegs R HIA) as A1; pose proof (alloc_ceiling_val R) as A2; unfold STKcf in SLO; clear - SPR SLO STKpk0 NRT LOS A1 A2; lia);
          let CI1 := fresh "CI1" in
          pose proof (cinv_after_chain _ _ _ _ _ _ _ _ _ _ _ (cinv_remodel _ _ _ _ _ _ CI0 HK1 MF1) E HH' HK' MF' HT' HS' HF' HCS'
                        ltac:(unfold AVOL_CALL in HV'; clear - HV'; lia) ltac:(unfold fr_charge in *; clear - HFR' D0; nia) HP' MI' ST') as CI1;
          let K := fresh "K" in pose proof NEXT as K; unfold from in K; eapply K; exact CI1
        end ]
      end end end.

    Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L14793086774.11 L27168730748.136L28132161751.5  L35653441506.11 L38692635477.0  L43712349232.7  L51303916321.0  L58642827747.9  L60098763854.3  L66151427842.16 L67059943649.6  L861591149.2    L9168957625.1   Q1340105615.138 Q1647021835.138 Q1659760685.137 Q18154937581.138Q33081735348.137Q41103801734.13700000T00h01:01Z01[02202302O02Y03403G03M03P03[03f04104J04U04`S1R5STKpk3NRT2sp2lo3LOS3SLO3SPR1H2H0S1R5STKpk2sp1A2HA2ABS1R3HIA1h2sp5SPTOPS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPSS1R5STKpk3NRT2sp2lo3SLOSS1R3HIA5PHIpk1h1f3BUD2hc3HVcS1R2lo3LOSS2sp2r04SP161q1r1H2H02q02H4S1R3HIA1f2hc2h'3HV'S1d2D0S1fS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk2sp1A3HAL2HA3SPRS1R5STKpk1AS1R5STKpk1A". (* [comment removed for export] *)
    #[using="IMG NEEDF NEEDM PZ SEQFREE ZFREE PK STKpk PHIpk0 DIMG NRT HH OWN HAL HA AB SUB RAWSMALL CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND D0"] Lemma from_a9a00 : from 0xaa144 P7.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3v x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      pose proof OWN as OWN'. ddestruct OWN' as (CISS & CSUBJ & CSAN & CAKID & CPOL & CEKU & _).
      assert (E : crt_blocks f = P7 ++ map (fun a => (a, SEQ_SIZE)) (co_akid f) ++ oblk (co_rawp f) (co_rawlen f)) by crt_blocks_eq.
      pose proof (cinv_chain _ _ _ _ _ _ _ _ _ _ _ CI0 E CAKID ltac:(unfold SEQ_SIZE; clear; lia)) as CH.
      pose proof (seg_nodup_nodes _ _ _ _ E) as NDn.
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      list_free_call SEQFREE A_ASN1_SEQUENCE_FREE CH NDn E from_a9a1c 0xaa160.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L14793086774.11 L1564669564.136 L28132161751.5  L35653441506.11 L38692635477.0  L43712349232.7  L55536219297.0  L58642827747.9  L60098763854.3  L66151427842.16 L67059943649.6  L861591149.2    L9168957625.1   Q12929900525.138Q24595204751.138Q37772931083.138Q37777526573.137Q58795103668.137Q59268357254.13700000T00h01:01Z01[02202302O02Y03403G03M03P03i04404?04J04U04`S1R5STKpk3NRT2sp2lo3LOS3SLO3SPR1H2H0S1R5STKpk2sp1A2HA2ABS1R3HIA1h2sp5SPTOPS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPSS1R5STKpk3NRT2sp2lo3SLOSS1R3HIA5PHIpk1h1f3BUD2hc3HVcS1R2lo3LOSS2sp2r04SP161q1r1H2H02q02H4S1R3HIA1f2hc2h'3HV'S1d2D0S1fS1R5STKpk2sp1A3HAL2HA3SPRS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1A". (* [comment removed for export] *)
    #[using="IMG NEEDF NEEDM PZ SEQFREE ZFREE PK STKpk PHIpk0 DIMG NRT HH OWN HAL HA AB SUB RAWSMALL CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND D0"] Lemma from_a99e4 : from 0xaa128 P6.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3v x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      pose proof OWN as OWN'. ddestruct OWN' as (CISS & CSUBJ & CSAN & CAKID & CPOL & CEKU & _).
      assert (E : crt_blocks f = P6 ++ map (fun a => (a, SEQ_SIZE)) (co_pol f) ++ (SSEQ (co_akid f) ++ oblk (co_rawp f) (co_rawlen f))) by crt_blocks_eq.
      pose proof (cinv_chain _ _ _ _ _ _ _ _ _ _ _ CI0 E CPOL ltac:(unfold SEQ_SIZE; clear; lia)) as CH.
      pose proof (seg_nodup_nodes _ _ _ _ E) as NDn.
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      list_free_call SEQFREE A_ASN1_SEQUENCE_FREE CH NDn E from_a9a00 0xaa144.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L14793086774.11 L18966192929.0  L28132161751.5  L35653441506.11 L38692635477.0  L43712349232.7  L58642827747.9  L60098763854.3  L64743327356.136L66151427842.16 L67059943649.6  L861591149.2    L9168957625.1   Q20706545965.137Q20718988811.138Q32570158004.137Q40089520621.138Q47177535110.137Q9492698255.138 00000T00U00g01G01H01_02;02E02Y03403G03M03P03[03f04104J04U04`S1R5STKpk3NRT2sp2lo3LOS3SLO3SPR1H2H0SS1R3HIA1h2sp5SPTOPS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPSS1R5STKpk3NRT2sp2lo3SLOS1R3HIA5PHIpk1h1f3BUD2hc3HVcS1R2lo3LOSS1R5STKpk2sp1A2HA2ABS2sp2r04SP161q1r1H2H02q02H4S1R3HIA1f2hc2h'3HV'S1d2D0S1fS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk2sp1A3HAL2HA3SPRS1R5STKpk1AS1R5STKpk1A". (* [comment removed for export] *)
    #[using="IMG NEEDF NEEDM PZ SEQFREE ZFREE PK STKpk PHIpk0 DIMG NRT HH OWN HAL HA AB SUB RAWSMALL CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND D0"] Lemma from_a99c8 : from 0xaa10c P5.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3v x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      pose proof OWN as OWN'. ddestruct OWN' as (CISS & CSUBJ & CSAN & CAKID & CPOL & CEKU & _).
      assert (E : crt_blocks f = P5 ++ map (fun a => (a, SEQ_SIZE)) (co_san f) ++ (SSEQ (co_pol f) ++ SSEQ (co_akid f) ++ oblk (co_rawp f) (co_rawlen f))) by crt_blocks_eq.
      pose proof (cinv_chain _ _ _ _ _ _ _ _ _ _ _ CI0 E CSAN ltac:(unfold SEQ_SIZE; clear; lia)) as CH.
      pose proof (seg_nodup_nodes _ _ _ _ E) as NDn.
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      list_free_call SEQFREE A_ASN1_SEQUENCE_FREE CH NDn E from_a99e4 0xaa128.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L14793086774.11 L28132161751.5  L35653441506.11 L38692635477.0  L40070721148.136L43712349232.7  L54274957729.0  L58642827747.9  L60098763854.3  L66151427842.16 L67059943649.6  L861591149.2    L9168957625.1   Q26511217901.138Q30208566662.137Q35623039156.137Q42786924299.138Q42791000109.137Q45321472911.13800000T00f01F01G01[02202302O02Y03403G03M03P03i04404?04J04U04`S1R5STKpk3NRT2sp2lo3LOS3SLO3SPR1H2H0S1R3HIA1h2sp5SPTOPS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPSS1R5STKpk2sp1A2HA2ABS1R5STKpk3NRT2sp2lo3SLOSS1R3HIA5PHIpk1h1f3BUD2hc3HVcS1R2lo3LOSS2sp2r04SP161q1r1H2H02q02H4S1R3HIA1f2hc2h'3HV'S1d2D0S1fS1R5STKpk2sp1A3HAL2HA3SPRS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1A". (* [comment removed for export] *)
    #[using="IMG NEEDF NEEDM PZ SEQFREE ZFREE PK STKpk PHIpk0 DIMG NRT HH OWN HAL HA AB SUB RAWSMALL CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND D0"] Lemma from_a99ac : from 0xaa0f0 P4.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3v x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      pose proof OWN as OWN'. ddestruct OWN' as (CISS & CSUBJ & CSAN & CAKID & CPOL & CEKU & _).
      assert (E : crt_blocks f = P4 ++ map (fun a => (a, SEQ_SIZE)) (co_eku f) ++ (SSEQ (co_san f) ++ SSEQ (co_pol f) ++ SSEQ (co_akid f) ++ oblk (co_rawp f) (co_rawlen f))) by crt_blocks_eq.
      pose proof (cinv_chain _ _ _ _ _ _ _ _ _ _ _ CI0 E CEKU ltac:(unfold SEQ_SIZE; clear; lia)) as CH.
      pose proof (seg_nodup_nodes _ _ _ _ E) as NDn.
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      list_free_call SEQFREE A_ASN1_SEQUENCE_FREE CH NDn E from_a99c8 0xaa10c.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L14793086774.11 L28132161751.5  L35653441506.11 L40228640085.0  L43712349232.7  L4384301692.136 L58642827747.9  L60098763854.3  L6106346273.0   L66151427842.16 L67059943649.6  L861591149.2    L9168957625.1   Q23803105389.138Q41821201716.137Q42049574662.137Q62852148619.138Q62855959213.137Q8755820815.138 00000T00f01F01G01^02202N02X02Y03403G03M03P03i04404?04J04U04`S1R5STKpk3NRT2sp2lo3LOS3SLO3SPR1H2H0S1R3HIA1h2sp5SPTOPS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPSS1R5STKpk3NRT2sp2lo3SLOS1R5STKpk2sp1A2HA2ABS1R3HIA5PHIpk1h1f3BUD2hc3HVcS1R2lo3LOSSS2sp2r04SP161q1r1H2H02q02H4S1R3HIA1f2hc2h'3HV'S1d2D0S1fS1R5STKpk2sp1A3HAL2HA3SPRS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1A". (* [comment removed for export] *)
    #[using="IMG NEEDF NEEDM PZ SHALLOW SEQFREE ZFREE PK STKpk PHIpk0 DIMG NRT HH OWN HAL HA AB SUB RAWSMALL CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND D0"] Lemma from_a9990 : from 0xaa0d4 P3.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3v x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      pose proof OWN as OWN'. ddestruct OWN' as (CISS & CSUBJ & CSAN & CAKID & CPOL & CEKU & _).
      assert (E : crt_blocks f = P3 ++ map (fun a => (a, NAME_SIZE)) (co_subject f) ++ (SSEQ (co_eku f) ++ SSEQ (co_san f) ++ SSEQ (co_pol f) ++ SSEQ (co_akid f) ++ oblk (co_rawp f) (co_rawlen f))) by crt_blocks_eq.
      pose proof (cinv_chain _ _ _ _ _ _ _ _ _ _ _ CI0 E CSUBJ ltac:(unfold NAME_SIZE; clear; lia)) as CH.
      pose proof (seg_nodup_nodes _ _ _ _ E) as NDn.
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      list_free_call SHALLOW A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW CH NDn E from_a99ac 0xaa0f0.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L14793086774.11 L28132161751.5  L35653441506.11 L39080257185.0  L40228640085.0  L43712349232.7  L58642827747.9  L58662515324.136L60098763854.3  L66151427842.16 L67059943649.6  L861591149.2    L9168957625.1   Q1145020077.137 Q1157226891.138 Q11725812486.137Q26820086068.137Q44686140525.138Q9032013071.138 00000T00f01F01G01H01_02;02O02Y03403G03M03P03[03f04104<04U04`S1R5STKpk3NRT2sp2lo3LOS3SLO3SPR1H2H0S1R3HIA1h2sp5SPTOPS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPSSS1R5STKpk3NRT2sp2lo3SLOS1R3HIA5PHIpk1h1f3BUD2hc3HVcS1R5STKpk2sp1A2HA2ABS1R2lo3LOSS2sp2r04SP161q1r1H2H02q02H4S1R3HIA1f2hc2h'3HV'S1d2D0S1fS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk2sp1A3HAL2HA3SPRS1R5STKpk1A". (* [comment removed for export] *)
    #[using="IMG NEEDF NEEDM PZ SHALLOW SEQFREE ZFREE PK STKpk PHIpk0 DIMG NRT HH OWN HAL HA AB SUB RAWSMALL CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND D0"] Lemma from_a9974 : from 0xaa0b8 P2.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3v x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      pose proof OWN as OWN'. ddestruct OWN' as (CISS & CSUBJ & CSAN & CAKID & CPOL & CEKU & _).
      assert (E : crt_blocks f = P2 ++ map (fun a => (a, NAME_SIZE)) (co_issuer f) ++ (SNAME (co_subject f) ++ SSEQ (co_eku f) ++ SSEQ (co_san f) ++ SSEQ (co_pol f) ++ SSEQ (co_akid f) ++ oblk (co_rawp f) (co_rawlen f))) by crt_blocks_eq.
      pose proof (cinv_chain _ _ _ _ _ _ _ _ _ _ _ CI0 E CISS ltac:(unfold NAME_SIZE; clear; lia)) as CH.
      pose proof (seg_nodup_nodes _ _ _ _ E) as NDn.
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      list_free_call SHALLOW A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW CH NDn E from_a9990 0xaa0d4.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00S0@D2778437343.158 L1332969832.3   L14791142800.11 L14915251665.1  L15897747528.8  L1607678038.9   L16434433161.6  L28132161751.5  L28813939468.3  L29149025057.0  L32027975233.0  L35653441506.11 L40281191306.3  L40354186202.3  L44349906689.51 L46473788606.7  L49631015752.1  L60098763854.3  L62018535662.1  L66151427842.16 L67059943649.5  L7990453884.129 L861591149.2    L9168957625.1   L9204387439.5   L9741573438.1   Q21517319092.131Q23384234477.132Q29775879338.158Q34247172397.131Q34251480587.132Q43050828943.132Q49628311307.158Q62022307279.158Q67239345798.13100000>00F00m01001K01g02;02M02V02W02X03803A03I06206I06M06W06Z07507F07Z07`07c08308608A08Z09009;09F09Q09]09f0:1S1R5STKpk2sp1AS1f2NZ1eS1R5STKpk3NRT2sp2lo3LOS3SLO3SPR3ALO3ACVS1AS1R5STKpk3NRT2sp2lo3LOS3SLOS1R3HIA5PHIpk1h1f3BUD2hc3HVcS1R3HIA1d2hc2h'4HFR'S1R3HIA1h2sp5SPTOPS1A2HA2ABSSS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPS1R3HIA1hS1f2NZ1eS1R3HIA5PHIpk5FFRpk1h3LBo2LB2LF2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m2mo1A1f2lo1d2m13moc2hc2x52x62x73x123x133x143x153x163x173s3v3x283x293x303x312E02NZS1R5STKpk3NRT2sp2lo3SLOS2spS1R2lo3LOSS1RS2sp2r04SP161q1r1H2H02q02H4S1R3HIA2hc2h'3HV'S1R5STKpk2sp1A2HA2ABS1d2D0S1fS1R1f3ACV2B03BceS1fS1R5STKpk1AS1R5STKpk2sp1A3HAL2HA3SPRS1R3HIA5STKpk1h2hc3HScS1R5STKpk1AS1R5STKpk1AS1R5STKpk1AS1R5STKpk2spS1R5STKpkS1R5STKpk1A". (* [comment removed for export] *)
    #[using="IMG HFREE NEEDF NEEDM PZ SHALLOW SEQFREE ZFREE PK STKpk PHIpk0 DIMG NRT HH OWN HAL HA AB SUB RAWSMALL CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND D0"] Lemma from_a9958 : from 0xaa09c P1.
    Proof.
      intros Lc mc moc hc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3v x28 x29 x30 x31 CI. pose proof CI as CI0. cinv_open CI. facts.
      pose proof (hcs_ok asegs R HIA hc) as CSOKc. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJc) as OBJcc.
      pose proof OWN as OWN'. ddestruct OWN' as (_ & _ & _ & _ & _ & _ & SIG & _).
      pose proof (alloc_ceiling_pos (L := L)) as ACP.
      assert (SB : 0 <= co_sigopts f < 2 ^ 64).
      { destruct SIG as [E|(HIN & POS)]; [rewrite E; clear; lia|].
        destruct (hm_apart asegs R HIA h _ _ _ HH) as [BR _]. rewrite Forall_forall in BR.
        destruct (BR _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & Bce & _). cbn [fst snd] in B0, Bce. clear - B0 Bce ACV; lia. }
      apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
      pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      replace (Z_to_bv 64 431228) with (Z_to_bv 64 (arl_free R)) by (rewrite HFREE; reflexivity).
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc0 _) => rename mc0 into m1 end.
      destruct (Z.eq_dec (co_sigopts f) 0) as [Z0|NZ].
      { (* [comment removed for export] *)
        rewrite Z0.
        eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
        { eapply (heapA_free_null asegs R HIA) with (h := hc) (LB := Lc ++ LB) (LF := LF) (lo := lo);
           rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by (clear - SPR SLO STKpk0 NRT LOS ALO ACV; lia); rewrite ?HTc;
           first [ exact HHc | exact LOS | exact TP | exact MIc | reflexivity
                 | lazymatch goal with
                   | |- stk _ m1 lo _ => assumption
                   | |- lo <= _ => clear - SLO STKpk0 NRT; lia
                   | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                   | |- _ mod 16 = 0 => clear - SP16; Z.div_mod_to_equations; lia
                   end
                 | match goal with |- ?g => idtac "FN-LEFT:" g end ]. }
        cbv beta. intros ms' PO. unfold call_postA in PO.
        ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m2' & E0 & PO). subst ms'.
        rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by (clear - SPR SLO STKpk0 NRT LOS ALO ACV; lia).
        ddestruct PO as (MI2 & ST2 & WM2 & HPf & h1 & E1cs & E1top & E1stk & E1flag & E1vol & E1fr & HKI1 & HH1).
        replace (ret_pc (Z_to_bv 64 0xaa0b8)) with (Z_to_bv 64 0xaa0b8 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
        clear MIc STc.
        (* [comment removed for export] *)
        assert (CI1 : cinv P2 Lc m2' moc h1).
        { unfold P2. rewrite Z0. unfold oblk. rewrite Z.eqb_refl, app_nil_r.
          split; [exact HH1|]. split; [apply (proj2 (HKI1 moc)); exact HKc|]. split; [exact MFc|].
          split; [rewrite E1top; exact HTc|]. split; [rewrite E1stk; exact HSc|]. split; [rewrite E1flag; exact HFc|].
          split; [intros x Hx; rewrite E1cs; exact (HCSc x Hx)|]. split; [rewrite E1vol; exact HVc|]. split; [rewrite E1fr; exact HFRc|].
          split; [exact SUBLc|]. split; [exact NDc|]. split; [exact KEEPc|]. split; [exact RELc|].
          split; [eapply presW_call; [exact HPXc| exact HPf| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| rewrite HSc; clear; lia| intros x _; exact I]|].
          apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2' _ _ HPf) in CELLS;
            [| replace (Z.of_nat (cells_size _)) with 744 by reflexivity; apply obj_client_range; intros b Hb; apply in_app_iff; right; exact Hb| exact I].
          apply (presA_aobj0 asegs R _ _ _ _ _ _ _ m1 m2' A 744 CSOK HPf) in OBJc;
            [| intros x Hx; rewrite HSc; eapply hcs_below_top; exact Hx| right; split; [apply obj_client_range; intros b Hb; apply in_app_iff; right; exact Hb| clear - LOS SLO STKpk0 NRT; lia]].
          clear OBJcc. presA_transport HPf.
          split; [exists jp; assumption|]. split; [exact CELLS|]. split; [exact OBJc|]. split; [assumption| assumption]. }
        clear HPf.
        pose proof from_a9974 as K. unfold from in K. unfold aevtA in K |- *. intros mo9 [HK9 MF9]. eapply K.
        eapply cinv_remodel; [exact CI1| apply (proj2 (HKI1 mo9)); exact HK9| exact MF9]. }
      (* [comment removed for export] *)
      destruct SIG as [E0|(HIN0 & POS)]; [clear - NZ E0; lia|].
      assert (E : crt_blocks f = P1 ++ map (fun a => (a, 8)) [co_sigopts f] ++ (SNAME (co_issuer f) ++ SNAME (co_subject f) ++ SSEQ (co_eku f) ++ SSEQ (co_san f) ++ SSEQ (co_pol f) ++ SSEQ (co_akid f) ++ oblk (co_rawp f) (co_rawlen f))).
      { unfold P1, SNAME, SSEQ, crt_blocks. unfold oblk at 1.
        destruct (Z.eqb_spec (co_sigopts f) 0); [clear - NZ e; lia|]. repeat rewrite <- app_assoc. cbn [map app]. reflexivity. }
      assert (HIN : In (co_sigopts f, 8) (Lc ++ LB)).
      { apply in_or_app. left. eapply (cinv_seg_in _ _ _ _ _ _ _ CI0 E). left. reflexivity. }
      assert (LEN2 : Z.of_nat (length (crt_blocks f)) >= Z.of_nat (length P1) + 1) by (rewrite E, !app_length; cbn [length map]; clear; lia).
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply (heapA_free asegs R HIA) with (h := hc) (LB := Lc ++ LB) (LF := LF) (A := co_sigopts f) (n := 8) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by (clear - SPR SLO STKpk0 NRT LOS ALO ACV; lia); rewrite ?HTc, ?HSc;
          first [ exact HHc | exact HK1 | exact HIN | exact LOS | exact TP | exact MIc | reflexivity
                | lazymatch goal with
                  | |- stk _ m1 lo _ => assumption
                  | |- lo <= _ => clear - SLO STKpk0 NRT; lia
                  | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                  | |- _ mod 16 = 0 => clear - SP16; Z.div_mod_to_equations; lia
                  | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold AVOL_CALL; unfold PHIcf in HVc, BUD; pose proof (PHIpk0 (Z.of_nat (length (crt_blocks f))) ltac:(clear; lia)) as PH; clear - HVc BUD PH; lia
                  | |- uwc _ _ _ _ _ _ _ => rewrite (unsigned_lit A) by (clear - HA AB; lia); eapply uw_obj_uwc; [exact UWO| clear; lia]
                  | |- hfr _ _ _ _ + _ <= FR_MAX => unfold FFRcf in BUDF; rewrite ?(Z.max_r 0 (fr_charge d)) in BUDF by (unfold fr_charge; clear - D0; lia); unfold fr_charge in *; clear - HFRc BUDF LEN2 D0; nia
                  end
                | match goal with |- ?g => idtac "FR-LEFT:" g end ]. }
      cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
      ddestruct PO as (ms2 & mo2 & EE & PO). injection EE as E1 E2. subst ms2 mo2.
      unfold call_postA in PO. ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m' & E0 & PO). subst ms'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by (clear - SPR SLO STKpk0 NRT LOS ALO ACV; lia).
      ddestruct PO as (MI' & ST' & MF' & HP' & h' & HT' & HS' & HF' & HK' & HCS' & HV' & HFR' & HH').
      replace (ret_pc (Z_to_bv 64 0xaa0b8)) with (Z_to_bv 64 0xaa0b8 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof (cinv_after_chain _ 8 [co_sigopts f] _ _ _ _ _ _ _ _ (cinv_remodel _ _ _ _ _ _ CI0 HK1 MF1) E HH' HK' MF' HT' HS' HF' HCS'
                    ltac:(unfold AVOL_CALL in HV'; clear - HV'; lia) ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HFR'; lia) HP' MI' ST') as CI1.
      pose proof from_a9974 as K. unfold from in K. eapply K.
      replace P2 with (P1 ++ map (fun a => (a, 8)) [co_sigopts f]); [exact CI1|].
      unfold P2, oblk. destruct (Z.eqb_spec (co_sigopts f) 0); [clear - NZ e; lia|]. reflexivity.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "01I0@D11189028015.115D11189028015.116D35881667587.115D35881667587.116K54978542206.115K54978542206.116L11741095640.111L11803631744.9  L11807598354.1  L12507622193.3  L13538440439.7  L14791142800.11 L15897747528.8  L19354909044.112L22706556809.3  L24634784385.2  L25382082548.112L26924648792.112L2780121756.1   L28132161751.5  L28814043710.112L31378308326.111L31392867444.112L35392543164.1  L35653441506.11 L36267119288.1  L37414286068.112L39263166881.0  L40281191306.3  L40834179097.115L42908672590.7  L43055530543.109L43442376564.111L43654564952.112L44277782651.1  L46032878640.1  L49631015752.1  L52103889786.13 L54968017161.2  L56763471081.7  L58407489854.1  L59308628179.3  L59499841752.112L60098763854.3  L62018535662.1  L62393202399.4  L66151427842.16 L67162155719.8  L7510805464.112 L861591149.2    Q11801279589.115Q11801279589.116Q15643324129.111Q18235909853.115Q18365925601.112Q18694146040.115Q21798041355.115Q22712450012.115Q22712450012.116Q25157988860.115Q25513505925.114Q25513505925.115Q25604052563.112Q25604052563.113Q25662358575.115Q31228709292.115Q31394594844.115Q32655500769.112Q33918256002.112Q34362328320.115Q34362328320.116Q34820943771.115Q34820943771.116Q35014437530.115Q35717497884.115Q37821600610.114Q37821600610.115Q3830427394.112 Q39939554818.112Q44648843873.112Q49698585326.113Q49698585326.114Q51235796833.112Q53969758199.115Q54057591853.115Q6416456232.115 Q64255486968.115Q66522067074.112Q9843367298.111 00000l02102]03R04@05705E05a05d05l06?06f07A07O07W07]07k08908=08O08c09109?09B09b09e0:30:40:=0:K0:c0;C0;Q0;_0;b0;e0;i0<S0<T0<i0<l0=50=C0=M0=P0=\0>=0>X0>f0>l0?J0@10@@0@A0@P0@]0@^0A<0Ac0B00BQ0C;0CJ0CY0CZ0Ck0D40DC0DZ0D[0D\0ES0FS0F`0Fa0GJ0H<0HS0Hj0I90IR0Ik0J:0JG0JH0JU0JV0Jm0KDS1R5NEEDF5STKpk3NRT2ra2sp1A2lo2HA3LOS3SLO3SPR2HB5Ha_st5Hl_stS1R5NEEDF5STKpk3NRT2sp2s01A2lo2HA3LOS3SLO3SPR2HB5Ha_st5Hl_st2s12s22s3S1R3HIA5STKpk1h2ra2sp1A5SPTOP2HB5Ha_st5Hl_stS1R3HIA5STKpk1h2sp2s01A5SPTOP2HB5Ha_st5Hl_st2s12s22s3S1R5STKpk3NRT2ra2sp1A2lo2DS3SLO2HB5Ha_st5Hl_stS1R5STKpk3NRT2sp2s01A2lo2DS3SLO2HB5Ha_st5Hl_st2s12s22s3S1R5STKpk2sp1AS1R5STKpk3NRT2sp1A2lo2DS3SLOS1AS1A1a2HaS1R5STKpk2sp2lo3SLOS1R5STKpk3NRT2sp2lo3LOS3SLO3SPR3ALO3ACVS1R5STKpk3NRT2sp2lo3LOS3SLOS1R5STKpk2sp1AS1A1x2HxS1A2HAS1R5STKpk2sp1AS1R5STKpk2sp1AS2spS1R3HIA1h2sp5SPTOPS1R5STKpk2sp1A2HA2ABS1R5STKpk2sp1AS1R5STKpk2sp1AS1AS1R3HIA5STKpk1h2sp2lo5SPTOP4HTOPS1AS1R5STKpk2sp1ASS1R3HIA1hS1R5STKpk2sp1AS1R3HIA5PHIpk1h1f3BUD2PMS1R5STKpk3NRT2sp1A2lo2HA3SLO3SPRS1R5STKpk2sp1AS1R5STKpk2sp1AS1AS1AS2spS1R5STKpk3NRT2sp2lo3LOS3SLO3ALO1a1b2Hr3BceFS1R3ACV1a1b2Hr2B03BceS1fS1A2HA2K0S1R5STKpk2sp1AS1R2lo3LOSS1RS2sp1A2lo2DSS1A2r03HAL1q1r1H2H02q02H42sp4SP16S1R3HIA5PHIpk1h1f2h13HV12PMS1R5STKpk2sp1AS1d2D0S1R5STKpk2ra2sp2HB5Ha_st5Hl_stS1R5STKpk2sp2s02HB5Ha_st5Hl_st2s12s22s3S1R5STKpk2sp2loFS1R5STKpk2sp2loS1R5STKpk3EHIFS1R5STKpk2ra2sp2HB5Ha_st5Hl_stS1R5STKpk2sp2s02HB5Ha_st5Hl_st2s12s22s3S1R5STKpk3EHIS1R5STKpk2ra2sp2lo2HB5Ha_st5Hl_stS1R5STKpk2sp2s02lo2HB5Ha_st5Hl_st2s12s22s3S1R5STKpk2sp2HBS1R5STKpk2sp2HBFS1R5STKpk3ELO3EHIS1R5STKpkS1R5STKpk2sp2loS1R5STKpk3NRT2sp2lo3SLOFFS1R5NEEDF5STKpk3NRT2ra2sp2lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS1R5NEEDF5STKpk3NRT2sp2s02lo3LOS3SLO3ALO2HB5Ha_st5Hl_st2s12s22s3S1R5STKpk3EHIFS1R5STKpk3NRT2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R5STKpk3NRT2sp2s02lo3SLO2HB5Ha_st5Hl_st2s12s22s3S1R5STKpk3NRT2sp2lo3SLOS1R5STKpk3NRT2sp2lo3SLOS1R5STKpk2sp2loS1R5STKpk2sp3SPR2HB5Ha_stS1R5STKpk2sp3SPR2HB5Ha_stS1R5STKpk2sp2loS1R5STKpk3EHIFS1R5STKpk3ELOFS1R5STKpk3NRT2sp2lo3SLOS1R5STKpk3NRT2sp2lo3SLO". (* [comment removed for export] *)
    #[using="IMG HFREE NEEDF NEEDM PZ SHALLOW SEQFREE ZFREE PK STKpk PHIpk0 PHIpk_mono FFRpk_mono PKFREE DIMG NRT HH HK0 OWN HAL HA AB SUB NDO RAWSMALL CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND D0"] Lemma entry_walk : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      rw_cells asegs m A (crt_cells f j) -> stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
      aobj asegs AL (hcs asegs R HIA h) m A 744 ->
      aevtS asegs POST
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0xaa050) fc None m (seg_rom asegs)) mo).
    Proof.
      intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 CELLS ST MI OBJ.
      (* [comment removed for export] *)
      pose proof HH as HHw. lazymatch type of HH with ?t => change t with (hidden t) in HH end.
      pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_val R) as ACV.
      pose proof (hm_top asegs R HIA h _ _ _ HHw) as HTOP. pose proof (hcs_stack asegs R HIA h) as SCS0.
      pose proof IMG as IMG'. unfold asan_img_ok in IMG'. ddestruct IMG' as (EGOT & ELO & EHI). unfold STKcf in SLO.
      assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO STKpk0 NRT SPTOP HTOP; lia]).
      pose proof (hm_wlow asegs R HIA h _ _ _ HHw) as WL.
      pose proof (presW_init asegs R HIA h (LBo ++ LB) LF m (bv_unsigned sp) (arl_stklo R) [(A, A + 744)] HHw ltac:(clear; lia)) as PRES.
      pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      pose proof OWN as OWN'. ddestruct OWN' as (_ & _ & _ & _ & _ & _ & _ & _ & PKR & _).
      apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ _ (conj HK0 (mo_frame_refl mo))).
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      unfold crt_cells in CELLS.
      (* [comment removed for export] *)
      zstep. carve_frame 48%nat ST. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0; [rewrite ?unsigned_lit in K0 by (clear - HA AB; lia); exfalso; clear - K0 HA; lia|]. clear K0.
      zstep. zstep.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with HHc : HM _ _ _ h _ LF mc |- _ =>
        pose proof (hm_abase asegs R HIA h _ LF mc HHc) as AB0; pose proof (abase_got _ _ _ AB0) as GOT; pose proof (abase_gsb _ _ _ AB0) as GSB end end.
      rewrite EGOT in GOT.
      zstep. zstep. clear GOT GSB AB0.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m0 end.
      (* [comment removed for export] *)
      assert (PKR0 : pk_rep asegs PK m0 (LBo ++ LB) (A + 360) (co_pkinfo f) (co_pkctx f) (co_pkowned f)).
      { destruct (hm_apart asegs R HIA h _ _ _ HHw) as [BR _]. rewrite Forall_forall in BR.
        eapply (pk_rep_frame asegs PK); [exact PKR| assumption| intros b Hb; exact (pk_rep_blocks asegs PK _ _ _ _ _ _ PKR b Hb)|].
        (intros a dd_H; ddestruct dd_H as (b & Hb & Hr)). pose proof (pk_rep_blocks asegs PK _ _ _ _ _ _ PKR b Hb) as HbL.
        ddestruct (BR b ltac:(apply in_app_iff; left; exact HbL)) as (B0 & _ & Bce & _).
        unfold wa. apply MU. rewrite unsigned_lit by (clear - B0 Bce Hr ACV; lia). cbn [outside]. split; [clear - Bce Hr ALO LOS SLO STKpk0 NRT; lia| exact I]. }
      clear MU WM.
      change (rw_cells asegs m0 A (crt_pre f j ++ [C8 (Z_to_bv 64 (co_pkinfo f)); C8 (Z_to_bv 64 (co_pkctx f))] ++ crt_suf f j)) in CELLS.
      destruct (rw_cells_split3 asegs m0 A _ _ _ CELLS) as (C1 & CPK & C3). clear CELLS.
      rewrite crt_pre_size in CPK, C3. change (Z.of_nat (cells_size [C8 (Z_to_bv 64 (co_pkinfo f)); C8 (Z_to_bv 64 (co_pkctx f))])) with 16 in C3.
      replace (A + 360 + 16) with (A + 376) in C3 by (clear; lia).
      assert (OWNED : forall b, In b (co_pkowned f) -> In b LBo) by (intros b Hb; apply SUB; unfold crt_blocks; apply in_or_app; left; exact Hb).
      assert (LEN1 : Z.of_nat (length (co_pkowned f)) <= Z.of_nat (length (crt_blocks f))) by (unfold crt_blocks; rewrite !app_length; clear; lia).
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply PKFREE with (h := h) (LBo := LBo) (LB := LB) (LF := LF) (PKA := A + 360) (info := co_pkinfo f) (ctx := co_pkctx f) (owned := co_pkowned f) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by (clear - SPR SLO STKpk0 NRT LOS ALO ACV; lia);
          first [ exact HK1 | exact CPK | exact PKR0 | exact OWNED | exact NDO | exact LOS | exact TP | reflexivity
                | lazymatch goal with
                  | |- HM _ _ _ h _ _ m0 => assumption
                  | |- (A + 360) mod 8 = 0 => clear - HAL; Z.div_mod_to_equations; lia
                  | |- 0 < A + 360 => clear - HA; lia
                  | |- aobj _ _ _ m0 (A + 360) 16 => eapply aobj_sub; [eassumption| clear; lia| clear; lia]
                  | |- client_wrange _ _ _ _ (A + 360) 16 => intros a Ha; apply CW; clear - Ha; lia
                  | |- A + 360 + 16 <= lo \/ _ => clear - DS; lia
                  | |- stk _ m0 lo _ => assumption
                  | |- lo <= _ => clear - SLO STKpk0 NRT; lia
                  | |- _ <= htop _ _ _ _ => clear - SPTOP; lia
                  | |- _ mod 16 = 0 => clear - SP16; Z.div_mod_to_equations; lia
                  | |- mem_inv _ m0 => assumption
                  | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold PHIcf in BUD; pose proof (PHIpk_mono _ _ (conj (Nat2Z.is_nonneg _) LEN1)) as PM; clear - BUD PM; lia
                  | |- uw_obj R (A + 360) 16 d => eapply uw_obj_sub; [exact UWO| clear; lia| clear; lia]
                  | |- hfr _ _ _ _ + _ <= FR_MAX => unfold FFRcf in BUDF; rewrite ?(Z.max_r 0 (fr_charge d)) in BUDF by (unfold fr_charge; clear - D0; lia); pose proof (FFRpk_mono _ _ d (conj (Nat2Z.is_nonneg _) LEN1)) as FM; unfold fr_charge in BUDF; clear - BUDF FM D0; nia
                  end
                | match goal with |- ?g => idtac "PK-LEFT:" g end ]. }
      cbv beta. (intros ms' mox dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m1 & mo1' & h1 & LB1
                      & E0 & MI1 & ST1 & MF1' & HP1 & HT1 & HS1 & HF1 & HK1' & HCS1 & HV1 & HFR1 & HH1 & SUB1 & KEEP1 & GONE1 & ND1 & PKZ).
      injection E0 as Ems Emo. subst ms' mox.
      rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST1, HP1 by (clear - SPR SLO STKpk0 NRT LOS ALO ACV; lia).
      replace (A + 360 + 16) with (A + 376) in HP1 by (clear; lia).
      replace (ret_pc (Z_to_bv 64 0xaa09c)) with (Z_to_bv 64 0xaa09c : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      pose proof from_a9958 as K. unfold from in K. eapply K. clear K.
      (* [comment removed for export] *)
      assert (SUBL1 : forall b, In b (LB1 ++ LB) -> In b (LBo ++ LB)) by (apply lb_sub_app; exact SUB1).
      split; [exact HH1|]. split; [exact HK1'|]. split; [eapply mo_frame_trans; [exact MF1| exact MF1']|].
      split; [exact HT1|]. split; [exact HS1|]. split; [exact HF1|]. split; [exact HCS1|].
      split; [unfold PHIcf in *; pose proof (PHIpk_mono _ _ (conj (Nat2Z.is_nonneg _) LEN1)) as PM; clear - HV1 PM; lia|].
      split; [pose proof (FFRpk_mono _ _ d (conj (Nat2Z.is_nonneg _) LEN1)) as FM; unfold P1; unfold fr_charge; clear - HFR1 FM D0; nia|].
      split; [exact SUB1|]. split; [exact ND1|]. split; [exact KEEP1|].
      split; [intros b Hb Hin; exfalso; exact (GONE1 b Hb Hin)|].
      split.
      { eapply presW_call; [eapply (presW_sub_blocks_fn asegs R HIA); [exact PRES| exact SUBL1]| exact HP1| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
        intros x Hx. cbn [outside] in Hx |- *. clear - Hx. lia. }
      lazymatch goal with FRx : rw_cells _ m0 (bv_unsigned sp + -48) _ |- _ =>
        apply (presA_rw_cells asegs R _ _ _ _ _ _ m0 m1 _ _ HP1) in FRx; [| apply client_range_stack; cbn; clear; lia| cbn [disjoint_from cells_size csize Nat.add]; clear - DS SLO STKpk0 NRT; lia] end.
      lazymatch goal with FRx : rw_cells _ m1 (bv_unsigned sp + -48) _ |- _ => cb8_to_c8 FRx (@nil cell); split; [eexists; exact FRx|] end.
      split.
      { rewrite crt_cells_pk0. apply rw_cells_join3; rewrite ?crt_pre_size.
        - eapply presA_rw_cells; [exact HP1| exact C1| rewrite crt_pre_size; intros a Ha; apply (obj_client_range (LB1 ++ LB)); [intros b Hb; apply in_app_iff; right; exact Hb| clear - Ha; lia]| rewrite crt_pre_size; cbn [disjoint_from]; clear; lia].
        - exact PKZ.
        - change (Z.of_nat (cells_size [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])) with 16. replace (A + 360 + 16) with (A + 376) by (clear; lia).
          eapply presA_rw_cells; [exact HP1| exact C3| rewrite crt_suf_size; intros a Ha; apply (obj_client_range (LB1 ++ LB)); [intros b Hb; apply in_app_iff; right; exact Hb| clear - Ha; lia]| rewrite crt_suf_size; cbn [disjoint_from]; clear; lia]. }
      split.
      { lazymatch goal with OB : aobj _ _ _ m0 A 744 |- _ =>
          eapply presA_aobj0; [exact CSOK| exact HP1| exact OB| intros x Hx; eapply hcs_below_top; exact Hx| right; split; [apply obj_client_range; intros b Hb; apply in_app_iff; right; exact Hb| clear - LOS SLO STKpk0 NRT; lia]] end. }
      split; [exact MI1| exact ST1].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    #[using="IMG HFREE NEEDF NEEDM PZ SHALLOW SEQFREE ZFREE PK STKpk PHIpk0 PHIpk_mono FFRpk_mono PKFREE DIMG NRT HH HK0 OWN HAL HA AB SUB NDO RAWSMALL CW DS LOS SLO SP16 SPTOP TP SPR UWO BUD BUDF ND D0"] Theorem crt_free_walk : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      rw_cells asegs m A (crt_cells f j) -> stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
      aobj asegs AL (hcs asegs R HIA h) m A 744 ->
      aevtS asegs POST
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 A_X509_CRT_FREE) fc None m (seg_rom asegs)) mo).
    Proof. exact entry_walk. Qed.
  End Body.

  #[using="IMG HFREE NEEDF NEEDM PZ SHALLOW SEQFREE ZFREE PHIpk0 PHIpk_mono FFRpk_mono PKFREE DIMG NRT"] Theorem A_x509_crt_free_walk2 : x509_crt_free_stmtA2 asegs R HIA PK (PHIcf PHIpk) (FFRcf FFRpk) (STKcf R STKpk) A_X509_CRT_FREE.
  Proof.
    unfold x509_crt_free_stmtA2. intros h LBo LB LF. intros until d. intros HH HK CA SUB HA HAL NDO RAWSMALL OBJ CW DS ST LOS SLO SPTOP SP16 MI TP BUD UWO BUDF ->.
    ddestruct CA as (CELLS & _ & _ & AB & OWN). unfold CRT_SIZE in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    eapply crt_free_walk; eassumption.
  Qed.
End Walk.


