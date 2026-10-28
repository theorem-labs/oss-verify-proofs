(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_crt_parse_stmts A_pkcs7_cinfo A_pkcs7_parse_A A_asn1_get_len A_asn1_free_named_data_list_shallow A_asn1_sequence_free A_x509_get_name_stmt A_x509_parse_san_A A_x509_seq_stmts A_x509_seq_stmtsE.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_A A_x509_san_ext_bud A_x509_san_ext_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2S.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NA1 : 0 <= arl_need_amem R.
  Hypothesis AMS : arl_amemset R = 0x68258.
  Hypothesis AMC : arl_amemcpy R = 0x67dbc.
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  (* [comment removed for export] *)
  Variables (PHIp : Z -> Z) (FFRp : Z -> Z -> Z) (CNTp : Z -> Z) (STKp : Z).
  Hypothesis STKp0 : 0 <= STKp.
  Hypothesis PSAN : x509_parse_san_stmtA asegs R HIA PHIp FFRp CNTp STKp (LFMAX_CRT + 6) A_X509_PARSE_SAN.
  Hypothesis FREEL : asn1_free_named_data_list_shallow_stmtA asegs R HIA A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW.
  Hypothesis SEQFREE : asn1_sequence_free_stmtA asegs R HIA A_ASN1_SEQUENCE_FREE.
  (* [comment removed for export] *)
  Hypothesis PHIp_mono : forall n n', 0 <= n <= n' -> 0 <= PHIp n <= PHIp n'.
  Hypothesis FFRp_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRp n d <= FFRp n' d.
  Hypothesis CNTp_mono : forall n n', 0 <= n <= n' -> 0 <= CNTp n <= CNTp n'.
  Hypothesis PHIp_add : forall a b, 0 <= a -> 0 <= b -> PHIp a + PHIp b <= PHIp (a + b).
  Hypothesis FFRp_add : forall a b d, 0 <= a -> 0 <= b -> FFRp a d + FFRp b d <= FFRp (a + b) d.
  Hypothesis CNTp_add : forall a b, 0 <= a -> 0 <= b -> CNTp a + CNTp b <= CNTp (a + b).
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R /\ arl_need_amem R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.

  (* [comment removed for export] *)
  Local Notation STKx := (A_x509_san_ext_A.STKx R STKp).
  Local Notation CNTx := A_x509_san_ext_bud.CNTx.
  Local Notation PHIx := (A_x509_san_ext_bud.PHIx PHIp CNTp).
  Local Notation FFRx := (A_x509_san_ext_bud.FFRx FFRp CNTp).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP CUR P END BUF lo slo d : Z) (bs : list byte) (ct cpad : word).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 5)%nat.
  Hypothesis HPP : rw_cells asegs m PP [C8 (Z_to_bv 64 P)].
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis HBY : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis B30 : n < 2^30.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis HCUR : rw_cells asegs m CUR (seq_cells ct cpad 0 0 0).
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 32.
  Hypothesis CURLO : CUR + 32 <= lo.
  Hypothesis DCB : CUR + 32 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKx.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis NDL : List.NoDup (map fst LB).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_2S in SM2; unfold A_x509_san_ext_A.STKx in SLO; unfold SEQ_SIZE in *;
    pose proof NRT as (NRTm & NRTf & NRTa);
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation X0 := [(PP, PP + 8); (CUR, CUR + 32)].
  Local Notation NB := (END - P).
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHb := A_x509_san_ext_A.FSHb.
  Local Notation rsl := (A_x509_san_ext_A.rsl CUR).
  Local Notation LF' FB := ((FB, 256) :: LF).
  Local Notation POST := (seq_parser_postE asegs R HIA PHIx FFRx CNTx (fun r => r = 0) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP CUR P END BUF NB lo slo d m mo0).

  (* [comment removed for export] *)
  Definition nLB (nodes : list Z) : list blk := SSEQ (rev nodes) ++ LB.
  (* [comment removed for export] *)
  Definition Wc (cur : Z) : list ivl := [(PP, PP + 8); (cur, cur + 32)].
  (* [comment removed for export] *)
  Definition nodeF (FB x : Z) : Prop :=
    0 < x /\ x mod 16 = 0 /\ x + 32 <= alloc_ceiling /\ (x + 32 <= hl_data_lo L \/ hl_data_hi L <= x)
    /\ (forall B k, In (B, k) (LB ++ fdata LF) -> x + 32 <= B \/ B + k <= x)
    /\ (PP + 8 <= x \/ x + 32 <= PP) /\ (x + 32 <= CUR \/ CUR + 32 <= x) /\ (FB + 256 <= x \/ x + 32 <= FB).
  #[using="Type"] Lemma nodeF_fresh : forall FB x, nodeF FB x -> fresh_apart R LB LF x 32.
  Proof. (intros FB x dd_H; ddestruct dd_H as (N0 & _ & NC & ND & NAP & _)). exact (conj N0 (conj NC (conj ND NAP))). Qed.
  Definition nfreshA (FB : Z) (nodes : list Z) : Prop := forall x, In x nodes -> nodeF FB x.
  (* [comment removed for export] *)
  Definition curFA (nodes : list Z) (cur : Z) : Prop := (nodes = [] /\ cur = CUR) \/ (nodes <> [] /\ cur = last nodes 0).
  (* [comment removed for export] *)
  Definition headrep (mc : mem) (nodes : list Z) : Prop :=
    nodes = [] \/ exists (t pd : word) (l p : Z), rw_cells asegs mc CUR (seq_cells t pd l p (hd 0 nodes)) /\ BUF <= p /\ 0 <= l /\ p + l <= END.

  (* [comment removed for export] *)
  Definition sfr (hc : HST asegs R HIA) (Lh : list blk) (FB sp1 : Z) (w0 w1 w2 tl : word) (b : byte) (k0 k8 k16 k24 k48 : word) (j64 : list byte)
      (tg pd ln pv : word) (jn : list byte) (p cur : Z) (ctc cpc : word) (clc cpp cnx : Z) (mm : mem) : Prop :=
    HM asegs R HIA hc Lh (LF' FB) mm
    /\ htop asegs R HIA hc = htop asegs R HIA h /\ hstkhi asegs R HIA hc = hstkhi asegs R HIA h
    /\ (forall x, CS x -> hcs asegs R HIA hc x)
    /\ (forall b', In b' LB -> In b' Lh)
    /\ bv_unsigned sp - 240 <= sp1 <= bv_unsigned sp - 224 /\ sp1 mod 32 = 0 /\ FB mod 64 = 0 /\ fresh_apart R LB LF FB 256 /\ crange CS FB 256
    /\ presW asegs R HIA hc LB LF (bv_unsigned sp) (bv_unsigned sp) X0 m mm
    /\ rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2]
    /\ rw_cells asegs mm (FB + 32) [C8 tl] /\ rw_cells asegs mm (FB + 64) [CB 80 jn]
    /\ rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL) (FSHb b)
    /\ rw_cells asegs mm (bv_unsigned sp + -104) SAVEL
    /\ rw_cells asegs mm sp1 (rsl FB k0 k8 k16 k24 k48 j64) /\ rw_cells asegs mm (sp1 + 96) [C4 tg; C4 pd; C8 ln; C8 pv]
    /\ stk asegs mm (sp1 + 120) (bv_unsigned sp + -104) /\ stk asegs mm lo sp1
    /\ rw_cells asegs mm PP [C8 (Z_to_bv 64 p)] /\ P <= p <= END
    /\ bytes_at asegs mm BUF bs
    /\ aobj asegs AL (hcs asegs R HIA hc) mm PP 8 /\ aobj asegs AL (hcs asegs R HIA hc) mm BUF n /\ aobj asegs AL (hcs asegs R HIA hc) mm CUR 32
    /\ rw_cells asegs mm cur [C4 ctc; C4 cpc; C8 (Z_to_bv 64 clc); C8 (Z_to_bv 64 cpp); C8 (Z_to_bv 64 cnx)]
    /\ aobj asegs AL (hcs asegs R HIA hc) mm cur 32
    /\ (cur mod 8 = 0 /\ 0 < cur /\ cur + 32 <= lo /\ (PP + 8 <= cur \/ cur + 32 <= PP) /\ (cur + 32 <= BUF \/ BUF + n <= cur) /\ (FB + 256 <= cur \/ cur + 32 <= FB)
        /\ client_wrange L (Lh ++ fdata (LF' FB)) lo (htop asegs R HIA h) cur 32 /\ wcover R LB LF (bv_unsigned sp) X0 cur 32)
    /\ mem_inv asegs mm /\ sshad asegs AL mm slo (bv_unsigned sp).

  Ltac sfr_open D :=
    destruct D as (HHc & HTc & HSc & HCSc & SUBL & SP1 & SP1M & F64 & FRSH & CFB & PRES
                   & FHD & TLc & TSN & FSH & SAVE & RSL & TSB & STb & STlo & PPc & Hpc & BYc & OPP & OBUF & OCUR & CURc & OCc & CURF & MIc & SSc).

  (* [comment removed for export] *)
  Definition svA (Lh : list blk) (FB sp1 : Z) (PHIa FFRa : Z) (w0 w1 w2 tl : word) (b : byte) (k0 k8 k16 k24 k48 : word) (j64 : list byte)
      (tg pd ln pv : word) (jn : list byte) (p : Z) (nodes : list Z) (cur : Z) (ctc cpc : word) (clc cpp cnx : Z)
      (mc : mem) (moc : Model) (hc : HST asegs R HIA) : Prop :=
    sfr hc Lh FB sp1 w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p cur ctc cpc clc cpp cnx mc
    /\ HK asegs R HIA hc moc /\ mo_frame mo0 moc /\ hflag asegs R HIA hc = hflag asegs R HIA h
    /\ havol asegs R HIA hc <= havol asegs R HIA h + PHIa /\ hfr asegs R HIA hc <= hfr asegs R HIA h + FFRa
    /\ (forall x, In x nodes -> In (x, 32) Lh)
    /\ List.NoDup nodes /\ nfreshA FB nodes /\ curFA nodes cur /\ headrep mc nodes
    /\ seq_lseg asegs mc Lh BUF END (removelast nodes) (last nodes 0)
    /\ ((cpp = 0 /\ clc = 0 /\ nodes = []) \/ (BUF <= cpp /\ 0 <= clc /\ cpp + clc <= END)).

  Ltac svA_open D :=
    let S := fresh "SFR" in
    destruct D as (S & HKc & MFc & HFc & HVc & HFRc & SUBN & HND & HFR & HCF & HHD & HLS & CBUF).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma nLB_snoc : forall nodes N, nLB (nodes ++ [N]) = (N, 32) :: nLB nodes.
  Proof. intros. unfold nLB, SSEQ. rewrite rev_app_distr. reflexivity. Qed.
  #[using="Type"] Lemma nLB_sub : forall nodes b', In b' LB -> In b' (nLB nodes).
  Proof. intros. unfold nLB. apply in_or_app. right. assumption. Qed.
  #[using="Type"] Lemma nLB_in : forall nodes x, In x nodes -> In (x, 32) (nLB nodes).
  Proof. intros. unfold nLB, SSEQ. apply in_or_app. left. apply in_map_iff. exists x. split; [reflexivity|]. rewrite <- in_rev. exact H. Qed.
  #[using="Type"] Lemma last_in : forall (nodes : list Z), nodes <> [] -> In (last nodes 0) nodes.
  Proof. intros nodes Hne. rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="HIA h slo BIN ALC CUR0 CWC CURLO DCB D1 SLOS SLOL LOS"] Lemma cur_facts : forall FB nodes cur,
    fresh_apart R LB LF FB 256 -> nfreshA FB nodes -> curFA nodes cur ->
    cur mod 8 = 0 /\ 0 < cur /\ cur + 32 <= lo
    /\ (PP + 8 <= cur \/ cur + 32 <= PP) /\ (cur + 32 <= BUF \/ BUF + n <= cur) /\ (FB + 256 <= cur \/ cur + 32 <= FB)
    /\ (cur = CUR \/ (In cur nodes /\ nodeF FB cur)).
  Proof.
    clear - ALC CUR0 CURLO D1 DCB CWC BIN SLOS SLOL LOS HIA. intros FB nodes cur FRSH HFR HCF.
    pose proof (art_lo asegs R HIA) as ALO.
    destruct HCF as [[-> ->]|[Hne ->]].
    - pose proof (frame_apart_obj R HIA LB LF lo _ CUR 32 FB 256 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC.
      repeat split; try assumption; try lia; try (left; reflexivity).
    - pose proof (last_in nodes Hne) as HIN. pose proof (HFR _ HIN) as NF. dpose NF as (N0 & N16 & NC & ND & NLB & NPP & NCU & NFB).
      split; [clear - N16; Z.div_mod_to_equations; lia|]. split; [exact N0|]. split; [clear - NC ALO LOS; lia|].
      split; [exact NPP|]. split; [apply NLB; apply in_or_app; left; exact BIN|]. split; [exact NFB|]. right. split; [exact HIN| exact NF].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma others_apart : forall FB Lh nodes cur (hc : HST asegs R HIA) LFq mq y,
    HM asegs R HIA hc Lh LFq mq -> (forall x, In x nodes -> In (x, 32) Lh) ->
    List.NoDup nodes -> nfreshA FB nodes -> curFA nodes cur ->
    In y (removelast nodes) ->
    nodeF FB y /\ (y + 32 <= cur \/ cur + 32 <= y).
  Proof.
    clear. intros FB Lh nodes cur hc LFq mq y HH SUBN HND HFR HCF Hy.
    pose proof (in_removelast _ _ Hy) as HyN. split; [exact (HFR y HyN)|].
    destruct HCF as [[-> ->]|[Hne ->]]; [destruct Hy|].
    destruct (hm_apart asegs R HIA hc _ _ _ HH) as [_ HAP].
    assert (NE : y <> last nodes 0).
    { intros E. rewrite <- (removelast_last_app nodes 0) in HND by exact Hne.
      apply (List.NoDup_remove_2 (removelast nodes) [] (last nodes 0)) in HND. rewrite app_nil_r in HND. apply HND. rewrite <- E. exact Hy. }
    eapply (blocks_apart_in2 _ y 32 (last nodes 0) 32); [exact HAP| apply in_or_app; left; apply SUBN; exact HyN| apply in_or_app; left; apply SUBN; apply last_in; exact Hne| exact NE].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma close_nodes : forall FB Lh nodes cur mm (ctc cpc : word) (clc cpp : Z),
    nfreshA FB nodes -> curFA nodes cur -> headrep mm nodes -> (forall x, In x nodes -> In (x, 32) Lh) ->
    seq_lseg asegs mm Lh BUF END (removelast nodes) (last nodes 0) ->
    rw_cells asegs mm cur (seq_cells ctc cpc clc cpp 0) ->
    ((cpp = 0 /\ clc = 0 /\ nodes = []) \/ (BUF <= cpp /\ 0 <= clc /\ cpp + clc <= END)) ->
    (exists (t pd : word) (l p : Z), rw_cells asegs mm CUR (seq_cells t pd l p (hd 0 nodes))
                                     /\ ((p = 0 /\ l = 0 /\ nodes = []) \/ (BUF <= p /\ 0 <= l /\ p + l <= END)))
    /\ seq_lseg asegs mm Lh BUF END nodes 0.
  Proof.
    clear. intros FB Lh nodes cur mm ctc cpc clc cpp HFR HCF HHD SUBN HL HR HB.
    destruct HCF as [[-> ->]|(Hne & ->)].
    - split; [dexists ctc, cpc, clc, cpp; split; [exact HR| exact HB]| exact I].
    - destruct HHD as [E|(t & pd & l & p & HH & H1 & H2 & H3)]; [exfalso; exact (Hne E)|].
      split; [dexists t, pd, l, p; split; [exact HH| right; repeat split; assumption]|].
      destruct HB as [(_ & _ & E)|HB]; [exfalso; exact (Hne E)|].
      pose proof (HFR _ (last_in nodes Hne)) as (N0 & N16 & _).
      rewrite <- (removelast_last_app nodes 0) at 1 by exact Hne. apply seq_lseg_app. split; [exact HL|].
      cbn [seq_lseg hd]. split; [apply SUBN; apply last_in; exact Hne|].
      split; [exact N16|]. split; [exact N0|]. split; [| exact I]. dexists ctc, cpc, clc, cpp. split; [exact HR| exact HB].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma headrep_snoc : forall nodes cur mm (ctc cpc : word) (clc cpp : Z) N,
    curFA nodes cur -> headrep mm nodes -> rw_cells asegs mm cur (seq_cells ctc cpc clc cpp N) ->
    BUF <= cpp -> 0 <= clc -> cpp + clc <= END -> headrep mm (nodes ++ [N]).
  Proof.
    clear. intros nodes cur mm ctc cpc clc cpp N HCF HHD HR H1 H2 H3. right.
    destruct HCF as [[-> ->]|(Hne & _)].
    - dexists ctc, cpc, clc, cpp. split; [exact HR| repeat split; assumption].
    - destruct HHD as [E|(t & pd & l & p & HH & G1 & G2 & G3)]; [exfalso; exact (Hne E)|]. dexists t, pd, l, p. rewrite hd_app_ne by exact Hne.
      split; [exact HH| repeat split; assumption].
  Qed.

  #[using="Type"] Lemma lseg_snoc : forall FB Lh nodes cur mm (ctc cpc : word) (clc cpp : Z) N,
    nfreshA FB nodes -> curFA nodes cur -> (forall x, In x nodes -> In (x, 32) Lh) ->
    seq_lseg asegs mm Lh BUF END (removelast nodes) (last nodes 0) ->
    rw_cells asegs mm cur (seq_cells ctc cpc clc cpp N) -> BUF <= cpp -> 0 <= clc -> cpp + clc <= END ->
    seq_lseg asegs mm Lh BUF END (removelast (nodes ++ [N])) (last (nodes ++ [N]) 0).
  Proof.
    clear. intros FB Lh nodes cur mm ctc cpc clc cpp N HFR HCF SUBN HL HR H1 H2 H3.
    rewrite removelast_last, last_last.
    destruct HCF as [[-> _]|(Hne & ->)]; [exact I|].
    pose proof (HFR _ (last_in nodes Hne)) as (N0 & N16 & _).
    rewrite <- (removelast_last_app nodes 0) at 1 by exact Hne. apply seq_lseg_app. split; [exact HL|].
    cbn [seq_lseg hd]. split; [apply SUBN; apply last_in; exact Hne|].
    split; [exact N16|]. split; [exact N0|]. split; [| exact I]. dexists ctc, cpc, clc, cpp. split; [exact HR| repeat split; assumption].
  Qed.

  (* [comment removed for export] *)
  #[using="h lo slo CWP CWC SLOS SLOL LOS"] Lemma snoc_facts : forall FB Lh nodes cur N (hc : HST asegs R HIA) mq,
    HM asegs R HIA hc ((N, 32) :: Lh) (LF' FB) mq -> (forall b', In b' LB -> In b' Lh) -> (forall x, In x nodes -> In (x, 32) Lh) ->
    List.NoDup nodes -> nfreshA FB nodes -> curFA nodes cur ->
    fresh_apart R Lh (LF' FB) N 32 -> N mod 16 = 0 ->
    List.NoDup (nodes ++ [N]) /\ nfreshA FB (nodes ++ [N]) /\ curFA (nodes ++ [N]) N /\ (N + 32 <= cur \/ cur + 32 <= N)
    /\ (forall x, In x (nodes ++ [N]) -> In (x, 32) ((N, 32) :: Lh)).
  Proof.
    clear - CWP CWC PPLO CURLO SLOS SLOL LOS. intros FB Lh nodes cur N hc mq HH SUBL SUBN HND HFR HCF NFR N16.
    pose proof (art_lo asegs R HIA) as ALO.
    dpose NFR as (N0 & NC & ND & NAP).
    destruct (hm_apart asegs R HIA hc _ _ _ HH) as [_ HAP]. cbn [blocks_apart app] in HAP. destruct HAP as [HAPN _].
    assert (NLB : forall B k, In (B, k) (LB ++ fdata LF) -> N + 32 <= B \/ B + k <= N).
    { intros B k Hb. apply NAP. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBL _ Hb)| right; apply (fdata_cons_sub (B, k) [] FB 256 LF); exact Hb]. }
    assert (NPP : PP + 8 <= N \/ N + 32 <= PP).
    { destruct (fresh_apart_client R Lh (LF' FB) lo PP 8 N 32 NFR) as [X|X]; [| clear; lia| clear; lia| clear - ALO LOS; lia| right; exact X| left; exact X].
      eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWP)|].
      intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBL _ Hb)| right; apply (fdata_cons_sub b' [] FB 256 LF); exact Hb]. }
    assert (NCU : N + 32 <= CUR \/ CUR + 32 <= N).
    { eapply (fresh_apart_client R Lh (LF' FB) lo CUR 32 N 32 NFR); [| clear; lia| clear; lia| clear - ALO LOS; lia].
      eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWC)|].
      intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBL _ Hb)| right; apply (fdata_cons_sub b' [] FB 256 LF); exact Hb]. }
    assert (NFB : FB + 256 <= N \/ N + 32 <= FB).
    { destruct (HAPN FB 256 ltac:(apply in_or_app; right; left; reflexivity)) as [X|X]; [right; exact X| left; exact X]. }
    assert (NF : nodeF FB N).
    { split; [exact N0|]. split; [exact N16|]. split; [exact NC|]. split; [exact ND|]. split; [exact NLB|]. split; [exact NPP|]. split; [exact NCU| exact NFB]. }
    assert (APcur : N + 32 <= cur \/ cur + 32 <= N).
    { destruct HCF as [[_ ->]|(Hne & ->)]; [exact NCU|]. apply HAPN. apply in_or_app. left. apply SUBN. apply last_in. exact Hne. }
    split; [| split; [| split; [| split; [exact APcur|]]]].
    - apply List.NoDup_app; [exact HND| constructor; [intros HIn; destruct HIn| constructor] |].
      intros y Hy [E|[]]. pose proof (HAPN y 32 ltac:(apply in_or_app; left; apply SUBN; exact Hy)). pose proof (HFR y Hy) as (Y0 & _). subst y. lia.
    - intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|[<-|[]]]; [exact (HFR y Hy)| exact NF].
    - right. split; [destruct nodes; discriminate| symmetry; apply last_last].
    - intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|[<-|[]]]; [right; exact (SUBN _ Hx)| left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="NRT h lo CWC CURLO D1"] Lemma nrep_move : forall FB Lh nodes cur (hc : HST asegs R HIA) LFq mq (mm m1 : mem),
    HM asegs R HIA hc Lh LFq mq -> (forall x, In x nodes -> In (x, 32) Lh) -> (forall b', In b' LB -> In b' Lh) ->
    List.NoDup nodes -> nfreshA FB nodes -> curFA nodes cur ->
    presW asegs R HIA hc Lh LF (bv_unsigned sp) (bv_unsigned sp) (Wc cur) mm m1 ->
    headrep mm nodes -> seq_lseg asegs mm Lh BUF END (removelast nodes) (last nodes 0) ->
    headrep m1 nodes /\ seq_lseg asegs m1 Lh BUF END (removelast nodes) (last nodes 0).
  Proof.
    clear - CWC CURLO D1 LOS SLO NS1 NA1 STKp0 NRT. intros FB Lh nodes cur hc LFq mq mm m1 HH SUBN SUBL HND HFR HCF PW HHD HL.
    pose proof (presW_presA asegs R HIA hc Lh LF _ _ _ _ _ PW) as HP.
    dpose NRT as (_ & _ & NRTa). unfold A_x509_san_ext_A.STKx in SLO.
    split.
    - destruct HCF as [[E _]|(Hne & ->)]; [left; exact E|].
      destruct HHD as [E|(t & pd & l & p & HR & H1 & H2 & H3)]; [left; exact E| right].
      pose proof (HFR _ (last_in nodes Hne)) as (_ & _ & _ & _ & _ & _ & NCU & _).
      dexists t, pd, l, p. split; [| repeat split; assumption].
      eapply (presA_rw_cells asegs R); [exact HP| exact HR| | cbn [cells_size csize Nat.add seq_cells disjoint_from Wc]; clear - D1 NCU; lia].
      cbn [cells_size csize Nat.add seq_cells]. eapply client_range_lower; [| first [exact CURLO | cbn; clear - CURLO; lia]].
      eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWC)|].
      intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBL _ Hb)| right; exact Hb].
    - eapply seq_lseg_mem; [exact HL| intros y Hy; eapply seq_lseg_in; [exact HL| exact Hy] |].
      intros y cs Hy HR Hsz. eapply (presA_rw_cells asegs R); [exact HP| exact HR| |]; rewrite Hsz.
      + eapply client_range_block; [apply in_or_app; left; eapply seq_lseg_in; [exact HL| exact Hy] | clear; lia | cbn; clear; lia].
      + ddestruct (others_apart FB Lh nodes cur hc LFq mq y HH SUBN HND HFR HCF Hy) as ((_ & _ & _ & _ & _ & YP & _ & _) & YC).
        cbn [disjoint_from Wc]. clear - YP YC. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG NS1 NA1 STKp STKp0 NRT CWP PPLO BIN ALC CUR0 CWC CURLO DCB D1 SLOS SLOL SLO LOS"] Lemma svA_callG : forall Lh FB sp1 PHIa FFRa w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx mc moc hc
      (Lp Lh' : list blk) (SSPq : Z) (Wq : list ivl) (dV dF : Z) (jn' : list byte) m1 mo1 h1,
    svA Lh FB sp1 PHIa FFRa w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx mc moc hc ->
    presA asegs R Lp (LF' FB) sp1 SSPq (hstkhi asegs R HIA hc) Wq mc m1 ->
    presA asegs R LB LF sp1 SSPq (hstkhi asegs R HIA hc) [] mc m1 ->
    SSPq <= sp1 ->
    (forall A k, A + k <= FB + 64 \/ FB + 144 <= A -> disjoint_from Wq A k) ->
    (forall b', In b' LB -> In b' Lp) -> (forall x, In x nodes -> In (x, 32) Lp) ->
    (forall b', In b' LB -> In b' Lh') -> (forall x, In x nodes -> In (x, 32) Lh') ->
    mem_inv asegs m1 -> stk asegs m1 lo sp1 -> sshad asegs AL m1 slo (bv_unsigned sp) -> mo_frame moc mo1 ->
    rw_cells asegs m1 (FB + 64) [CB 80 jn'] ->
    htop asegs R HIA h1 = htop asegs R HIA hc -> hstkhi asegs R HIA h1 = hstkhi asegs R HIA hc -> hflag asegs R HIA h1 = hflag asegs R HIA hc ->
    HK asegs R HIA h1 mo1 -> (forall y, hcs asegs R HIA hc y -> hcs asegs R HIA h1 y) ->
    havol asegs R HIA h1 <= havol asegs R HIA hc + dV -> hfr asegs R HIA h1 <= hfr asegs R HIA hc + dF ->
    HM asegs R HIA h1 Lh' (LF' FB) m1 ->
    svA Lh' FB sp1 (PHIa + dV) (FFRa + dF) w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn' p nodes cur ctc cpc clc cpp cnx m1 mo1 h1.
  Proof.
    intros until h1. intros D HP1 HPw SSPL DJW SUBLp SUBNp SUBL' SUBN' MI1 ST1 SS1 MF1 TSN1 HT1 HS1 HF1 HK1 HCS1 HV1 HFR1 HH1.
    svA_open D. sfr_open SFR. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    pose proof FRSH as FRSH'. ddestruct FRSH' as (F0 & F1 & F2 & F3).
    ddestruct (cur_facts FB nodes cur FRSH HFR HCF) as (CAL & CPOS & CLO & CPP & CBF & CFBa & CCASE).
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ CUR 32 FB 256 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC.
    assert (FBLO : FB + 256 <= lo) by (clear - F1 ALO LOS; lia).
    assert (SUBq' : forall b', In b' (LB ++ fdata LF) -> In b' (Lp ++ fdata (LF' FB))).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBLp b' Hb)| right; apply (fdata_cons_sub b' [] FB 256 LF); exact Hb]. }
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L (Lp ++ fdata (LF' FB)) sp1 a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBq']. }
    assert (INHq : In (FB, 24) (Lp ++ fdata (LF' FB))) by (apply in_or_app; right; cbn; left; reflexivity).
    assert (INDq : In (FB + 32, 256 - 40) (Lp ++ fdata (LF' FB))) by (apply in_or_app; right; cbn; right; left; reflexivity).
    assert (CSHD : forall c, FB <= c < FB + 256 -> cshd R Lp (LF' FB) SSPq (hstkhi asegs R HIA hc) c).
    { intros c Hc. right; right; left. exists (FB, 256). split; [left; reflexivity| cbn; exact Hc]. }
    assert (CRcur : client_range L (Lp ++ fdata (LF' FB)) sp1 cur 32).
    { destruct CCASE as [->|(HIN & _)]; [apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]|].
      eapply client_range_block; [apply in_or_app; left; exact (SUBNp _ HIN)| clear; lia| clear; lia]. }
    assert (DJS : forall A k, sp1 <= A -> disjoint_from Wq A k) by (intros A k HA; apply DJW; right; clear - HA FBLO SLO SP1 NS1 NA1 NRTa STKp0; lia).
    assert (BINp : In (BUF, n) (Lp ++ fdata (LF' FB))) by (apply in_or_app; left; apply SUBLp; exact BIN).
    assert (APB : n = 0 \/ FB + 256 <= BUF \/ BUF + n <= FB).
    { destruct (Z.eq_dec n 0) as [E0|NE]; [left; exact E0| right]. apply F3. apply in_or_app. left. exact BIN. }
    (* [comment removed for export] *)
    split.
    { split; [exact HH1|]. split; [rewrite HT1; exact HTc|]. split; [rewrite HS1; exact HSc|].
      split; [intros y Hy; exact (HCS1 y (HCSc y Hy))|]. split; [exact SUBL'|].
      split; [exact SP1|]. split; [exact SP1M|]. split; [exact F64|]. split; [exact FRSH|]. split; [exact CFB|].
      split.
      { eapply (presW_hmono R HIA hc h1); [| exact HCS1| exact HS1].
        eapply (presW_call asegs R HIA hc LB LF _ _ X0 m mc m1); [exact PRES| exact HPw| intros b' Hb; exact Hb| intros b' Hb; exact Hb
          | clear - SP1; lia| clear - SSPL SP1; lia| clear; lia| intros y Hy; exact I]. }
      split; [eapply (presA_rw_cells asegs R); [exact HP1| exact FHD| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INHq| clear; lia| clear; lia]| apply DJW; cbn [cells_size csize Nat.add length]; clear; lia]|].
      split; [eapply (presA_rw_cells asegs R); [exact HP1| exact TLc| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INDq| clear; lia| clear; lia]| apply DJW; cbn [cells_size csize Nat.add length]; clear; lia]|].
      split; [exact TSN1|].
      split.
      { eapply (presA_shadow_cells_sh asegs R CS); [exact CSOK| cbn [cells_size csize Nat.add length A_x509_san_ext_A.FSHb]; exact CFB| clear - F64; Z.div_mod_to_equations; lia| clear - F0; lia| exact HP1| exact FSH|].
        cbn [cells_size csize Nat.add length A_x509_san_ext_A.FSHb]. intros c Hc. apply CSHD. clear - Hc. lia. }
      split; [eapply (presA_rw_cells asegs R); [exact HP1| exact SAVE| apply client_range_stack; clear - SP1; lia| apply DJS; clear - SP1; lia]|].
      split; [eapply (presA_rw_cells asegs R); [exact HP1| exact RSL| apply client_range_stack; clear; lia| apply DJS; clear; lia]|].
      split; [eapply (presA_rw_cells asegs R); [exact HP1| exact TSB| apply client_range_stack; clear; lia| apply DJS; clear; lia]|].
      split; [eapply (presA_stk asegs R); [exact HP1| exact STb| clear; lia| apply DJS; clear; lia]|].
      split; [exact ST1|].
      split; [eapply (presA_rw_cells asegs R); [exact HP1| exact PPc| cbn [cells_size csize Nat.add length]; apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| apply DJW; cbn [cells_size csize Nat.add length]; clear - APP; lia]|].
      split; [exact Hpc|].
      split.
      { eapply (presA_bytes_at0 asegs R); [exact HP1| exact BYc|]. destruct (Nat.eq_dec (length bs) 0) as [E|NE]; [left; exact E| right].
        split; [eapply client_range_block; [exact BINp| clear; lia| clear; lia]| apply DJW; clear - APB NE; lia]. }
      split; [eapply aobj_cs_mono; [exact HCS1|]; eapply (presA_aobj0 asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP1| exact OPP| intros y Hy; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| exact SSPL]]|].
      split.
      { eapply aobj_cs_mono; [exact HCS1|]. eapply (presA_aobj0 asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP1| exact OBUF| intros y Hy; eapply hcs_below_top; exact Hy|].
        destruct (Z.eq_dec n 0) as [E0|NE]; [left; rewrite E0; clear; lia| right]. split; [| exact SSPL].
        eapply client_range_block; [exact BINp| clear; lia| clear; lia]. }
      split; [eapply aobj_cs_mono; [exact HCS1|]; eapply (presA_aobj0 asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP1| exact OCUR| intros y Hy; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]| exact SSPL]]|].
      split; [eapply (presA_rw_cells asegs R); [exact HP1| exact CURc| cbn [cells_size csize Nat.add length]; exact CRcur| apply DJW; cbn [cells_size csize Nat.add length]; clear - CFBa; lia]|].
      split; [eapply aobj_cs_mono; [exact HCS1|]; eapply (presA_aobj0 asegs R (hcs asegs R HIA hc)); [exact (hcs_ok asegs R HIA hc)| exact HP1| exact OCc| intros y Hy; eapply hcs_below_top; exact Hy| right; split; [exact CRcur| exact SSPL]]|].
      split.
      { split; [exact CAL|]. split; [exact CPOS|]. split; [exact CLO|]. split; [exact CPP|]. split; [exact CBF|]. split; [exact CFBa|].
        destruct CCASE as [->|(HIN & NFc)].
        - split; [| apply wcover_inside; cbn [inside]; right; left; clear; lia].
          eapply client_wrange_mono; [exact CWC|]. intros b' Hb. apply in_app_iff in Hb. apply in_app_iff.
          destruct Hb as [Hb|Hb]; [left; exact (SUBL' b' Hb)| right; apply (fdata_cons_sub b' [] FB 256 LF); exact Hb].
        - split; [eapply client_wrange_block; [apply in_or_app; left; exact (SUBN' _ HIN)| clear; lia| clear; lia]|].
          eapply (wcover_fresh R); [exact (nodeF_fresh FB cur NFc)| clear; lia| clear; lia| clear - ALO LOS SLO NS1 NA1 NRTa STKp0; lia]. }
      split; [exact MI1| exact SS1]. }
    split; [exact HK1|]. split; [eapply mo_frame_trans; [exact MFc| exact MF1]|]. split; [rewrite HF1; exact HFc|].
    split; [clear - HVc HV1; lia|]. split; [clear - HFRc HFR1; lia|].
    split; [exact SUBN'|]. split; [exact HND|]. split; [exact HFR|]. split; [exact HCF|].
    split.
    { destruct HHD as [E|(t & pd0 & l & p0 & HR & H1 & H2 & H3)]; [left; exact E| right]. dexists t, pd0, l, p0. split; [| repeat split; assumption].
      eapply (presA_rw_cells asegs R); [exact HP1| exact HR| cbn [cells_size csize Nat.add length seq_cells]; apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]
                                       | apply DJW; cbn [cells_size csize Nat.add length seq_cells]; clear - APC; lia]. }
    split; [| exact CBUF].
    eapply seq_lseg_mem; [exact HLS| intros y Hy; apply SUBN'; apply in_removelast; exact Hy |].
    intros y cs Hy HR Hsz. eapply (presA_rw_cells asegs R); [exact HP1| exact HR| |]; rewrite Hsz.
    - eapply client_range_block; [apply in_or_app; left; apply SUBNp; apply in_removelast; exact Hy | clear; lia | cbn; clear; lia].
    - pose proof (HFR y (in_removelast _ _ Hy)) as (_ & _ & _ & _ & _ & _ & _ & YFB). apply DJW. clear - YFB. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="NRT CWC CURLO D1"] Lemma svA_seg : forall Lh FB sp1 PHIa FFRa w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx mc moc hc
      w0' w1' w2' tl' b' k0' k8' k16' k24' k48' j64' tg' pd' ln' pv' jn' p' ctc' cpc' clc' cpp' cnx' m1,
    svA Lh FB sp1 PHIa FFRa w0 w1 w2 tl b k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp cnx mc moc hc ->
    sfr hc Lh FB sp1 w0' w1' w2' tl' b' k0' k8' k16' k24' k48' j64' tg' pd' ln' pv' jn' p' cur ctc' cpc' clc' cpp' cnx' m1 ->
    presW asegs R HIA hc Lh LF (bv_unsigned sp) (bv_unsigned sp) (Wc cur) mc m1 ->
    ((cpp' = 0 /\ clc' = 0 /\ nodes = []) \/ (BUF <= cpp' /\ 0 <= clc' /\ cpp' + clc' <= END)) ->
    svA Lh FB sp1 PHIa FFRa w0' w1' w2' tl' b' k0' k8' k16' k24' k48' j64' tg' pd' ln' pv' jn' p' nodes cur ctc' cpc' clc' cpp' cnx' m1 moc hc.
  Proof.
    intros until m1. intros D S1 PW CB'. svA_open D.
    dpose SFR as (HHc & _ & _ & _ & SUBL & _).
    destruct (nrep_move FB Lh nodes cur hc _ mc mc m1 HHc SUBN SUBL HND HFR HCF PW HHD HLS) as [HHD1 HLS1].
    split; [exact S1|]. do 5 (split; [assumption|]). split; [exact SUBN|]. split; [exact HND|]. split; [exact HFR|]. split; [exact HCF|].
    split; [exact HHD1|]. split; [exact HLS1| exact CB'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG NS1 NA1 STKp STKp0 NRT LFB CWP PPLO CUR0 CWC CURLO SLOS SLOL SLO TOP SPH LOS"] Lemma ret_walk : forall FB sp1 PHIa FFRa w0 w1 w2 tl k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp mc moc hc (r : Z)
      (xra t0 t1 t2 a0 a3 a4 a5 a6 a7 s3v s4v s5v s6v s7v s8v s9v s10v t3 t4 t5 t6 : word),
    svA (nLB nodes) FB sp1 PHIa FFRa w0 w1 w2 tl (Z_to_bv 8 248) k0 k8 k16 k24 k48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp 0 mc moc hc ->
    Z.of_nat (length nodes) <= CNTx NB -> PHIa <= PHIx NB -> FFRa <= FFRx NB d ->
    -0x3000 < r <= 0 -> (r = 0 -> p = END) ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 (Z_to_bv 64 FB) (Z_to_bv 64 FB) a3 a4 a5 a6 a7
                     (Z_to_bv 64 r) s3v s4v s5v s6v s7v s8v s9v s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                 F (Z_to_bv 64 0xae96c) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until t6. intros D CNT PHI FFR Hr HENDr. svA_open D. sfr_open SFR. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    unfold nLB in HHc.
    pose proof (fresh_apart_grow R HIA hc (SSEQ (rev nodes)) LB LF mc FB 256 FRSH HHc) as FRSH3.
    (* [comment removed for export] *)
    unfold A_x509_san_ext_A.rsl in RSL.
    chunk_to_stk RSL. chunk_to_stk TSB.
    lazymatch type of RSL with stk _ _ _ ?hi => replace hi with (sp1 + 96) in RSL by (clear; lia) end.
    lazymatch type of TSB with stk _ _ _ ?hi => replace hi with (sp1 + 120) in TSB by (clear; lia) end.
    pose proof (stk_merge _ _ _ _ _ (stk_merge _ _ _ _ _ RSL TSB ltac:(clear; lia)) STb ltac:(clear - SP1; lia)) as STB2.
    pose proof (presW_init_at R HIA hc _ _ (SSEQ (rev nodes) ++ LB) LF mc (bv_unsigned sp) (bv_unsigned sp) [] h HHc
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 NA1 NRTa STKp0; lia)) as PRES2.
    (* [comment removed for export] *)
    destruct (close_nodes FB (nLB nodes) nodes cur mc ctc cpc clc cpp HFR HCF HHD SUBN HLS CURc CBUF) as [(ht & hpd & hl & hp & HHEAD & HHB) HLF].
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
    { eapply (epi_walk R HIA IMG NS1 NA1 STKp STKp0) with (h := h) (lo := lo) (slo := slo) (h3 := hc) (LBc := SSEQ (rev nodes)) (m2x := mc) (WA := X0) (WB := @nil ivl);
        first [ exact HHc | exact HCSc | exact HTc | exact HSc | exact PRES | exact PRES2 | exact FRSH | exact FRSH3 | exact CFB | exact STB2 | exact SLO
              | eassumption | reflexivity | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    ddestruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    pose proof (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES29) as HP29.
    assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' ((SSEQ (rev nodes) ++ LB) ++ fdata LF)).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L ((SSEQ (rev nodes) ++ LB) ++ fdata LF) (bv_unsigned sp) a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBq]. }
    unfold seq_parser_postE.
    deexists 15. dexists m9, mo9, h4, r, p, ht, hpd, hl, hp, (hd 0 nodes), nodes.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hr|].
    split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [eapply mo_frame_trans; [exact MFc| exact MF9]|].
    split; [pose proof (presW_presA asegs R HIA hc LB LF _ _ _ _ _ PRES9) as HPF; rewrite HSc in HPF; exact HPF|].
    split; [rewrite E4top; exact HTc|]. split; [rewrite E4stk; exact HSc|]. split; [rewrite E4flag; exact HFc|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSc x Hx)|].
    split; [rewrite E4vol; clear - HVc PHI; lia|]. split; [rewrite E4fr; clear - HFRc FFR; lia|].
    split; [exact CNT|].
    split; [eapply (presA_rw_cells asegs R); [exact HP29| exact PPc| cbn [cells_size csize Nat.add length]; apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| exact I]|].
    split; [exact Hpc|].
    split; [eapply (presA_rw_cells asegs R); [exact HP29| exact HHEAD| cbn [cells_size csize Nat.add length seq_cells]; apply CRo; [exact CURLO| exact (client_range_of_w L _ _ _ _ _ CWC)]| exact I]|].
    split; [exact HHB|]. split; [reflexivity|].
    split.
    { apply (seq_lseg_chain asegs _ _ BUF END). eapply seq_lseg_mem; [exact HLF| intros y Hy; exact (SUBN y Hy) |].
      intros y cs Hy HR Hsz. eapply (presA_rw_cells asegs R); [exact HP29| exact HR| | exact I]. rewrite Hsz.
      eapply client_range_block; [apply in_or_app; left; exact (SUBN y Hy) | clear; lia | cbn; clear; lia]. }
    split; [exact HND|].
    split; [intros x Hx B k Hb; dpose (HFR x Hx) as (_ & _ & _ & _ & NLB & _); apply NLB; apply in_or_app; left; exact Hb|].
    split; [exact HH4|]. exact HENDr.
  Qed.
  End Call.
End Walk.
