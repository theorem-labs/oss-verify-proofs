(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree CJ_print_iface CJ_ensure CJ_pstr_B CJ_pv_common CJ_pv_ctx CJ_pv_update CJ_pv_cases CJ_pv_numA NumFacts_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_shgetc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require NumFacts_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fmt_fp_lib F_printf_iface Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_facts3 Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Local Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Local Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gch_numch : forall o, Forall num_gch o -> Forall (fun c => FmtFp_facts3.is_numch c = true) o.
Proof.
  intros o H. eapply Forall_impl; [| exact H]. intros c Hc. unfold num_gch in Hc. unfold FmtFp_facts3.is_numch.
  destruct Hc as [Hc|[->|[->|[->|[->| ->]]]]]; try reflexivity.
  replace (48 <=? c) with true by (symmetry; apply Z.leb_le; lia).
  replace (c <=? 57) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma gch_bytes : forall o, Forall num_gch o -> Forall (fun c => 0 <= c < 256) o.
Proof. intros o H. eapply Forall_impl; [| exact H]. intros c Hc. unfold num_gch in Hc. lia. Qed.

Lemma gch_nox : forall o, Forall num_gch o -> Forall (fun c => c <> 120 /\ c <> 88) o.
Proof. intros o H. eapply Forall_impl; [| exact H]. intros c Hc. unfold num_gch in Hc. lia. Qed.

Lemma Forall_range_unsigned : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof. induction bs as [|b bs IH]; cbn; constructor; [| exact IH]. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia. Qed.

Lemma map_zb_unsigned : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite IH. f_equal. apply (@definitions.Z_to_bv_bv_unsigned 8). Qed.

Lemma zb_map : forall l, OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.zb l = map (Z_to_bv 8) l.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma dfin_of_test : forall vd : word,
  Z.shiftr (bv_unsigned (fabs_d vd)) 52 < 2047 -> ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047.
Proof.
  intros vd H. unfold fabs_d in H. rewrite Z_to_bv_unsigned in H.
  pose proof (bv_unsigned_in_range 64 vd) as R. change (bv_modulus 64) with (2^64) in R.
  rewrite Z.land_ones in H by lia. unfold bv_wrap in H. change (bv_modulus 64) with (2^64) in H.
  rewrite (Z.mod_small (bv_unsigned vd mod 2^63) (2^64)) in H by (pose proof (Z.mod_pos_bound (bv_unsigned vd) (2^63)); lia).
  rewrite Z.shiftr_div_pow2 in H by lia. rewrite (Z.mod_small (bv_unsigned vd) (2^64)) by lia.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma word_int_arg : forall w : word, exists i, bv_unsigned w mod 2^32 = i mod 2^32 /\ -2^31 <= i < 2^31.
Proof.
  intros w. exists ((bv_unsigned w + 2^31) mod 2^32 - 2^31).
  pose proof (bv_unsigned_in_range 64 w) as R. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma FAG18_set : forall F Fc (k : bv 5) v, FAG18 F Fc -> bv_unsigned k < 18 -> FAG18 F (bvmap_set k v Fc).
Proof.
  intros F Fc k v FA Hk r Hr. rewrite freg_get_other; [apply FA; exact Hr|]. unfold bv_eqb. apply Z.eqb_neq. lia.
Qed.

Lemma FAG18_call10 : forall F Fc Ft, FAG18 F Fc -> (forall k : bv 5, bv_unsigned k <> 10 -> reg_get Ft k = reg_get Fc k) -> FAG18 F Ft.
Proof. intros F Fc Ft FA H r Hr. rewrite (H r) by lia. apply FA. exact Hr. Qed.

Lemma FAG18_call3 : forall F Fc Ft, FAG18 F Fc ->
  (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get Ft k = reg_get Fc k) -> FAG18 F Ft.
Proof. intros F Fc Ft FA H r Hr. rewrite (H r) by lia. apply FA. exact Hr. Qed.

Lemma tx_after_len : forall (o : list Z) (tx : list byte),
  (length o < 32)%nat -> length tx = 32%nat -> length (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) tx) = 32%nat.
Proof. intros o tx Ho Ht. rewrite length_app. cbn [length]. rewrite zb_map, length_map, length_skipn. lia. Qed.

Section S.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
            (m : word -> option byte)
            (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z).
  Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PV_STACK n.
  Hypothesis TP : tp = wz PTP.
  Hypothesis SPhi : bv_unsigned sp <= 2^64.
  Hypothesis N1 : (1 <= n)%nat.
  Hypothesis BLR : forall b, In b B -> In b LR.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
  Hypothesis DEP0 : 0 <= dep.
  Hypothesis PNZ : p <> 0.
  Hypothesis CH0 : cj_chain CJ_PRINTABLE m n p B.
  (* [comment removed for export] *)
  Hypothesis SPRD : F_printf_iface.sprintf_d_stmt.
  Hypothesis SPRG : forall prec, F_printf_iface.sprintf_g_stmt prec.
  Hypothesis SSC : Scan_iface.rsscanf_lg_stmt.
  Hypothesis GRET : F_printf_iface.FMT_G_RET.
  Hypothesis GLEN25 : F_printf_iface.FMT_G_LEN25.
  Hypothesis GFACTS : NUM_FMT_G_FACTS.
  Hypothesis GTOT : NUM_FMT_G_TOTAL.
  Hypothesis DTOT : NUM_FMT_D_TOTAL.
  Hypothesis SJUNK : NUM_SSCANF_JUNK.

  Notation POST := (pvalue_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m).
  Notation SPF := (bv_unsigned sp + -128).
  Notation PVFRAME mm loc := (rw_cells usegs mm (bv_unsigned sp + -128)
     [CB 48 loc; C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation ACTX := (actx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR PB fw lo).
  Notation NCTX' := (NCTX HI sp m SPB LR PB fw lo).
  (* [comment removed for export] *)
  Ltac useA L := eapply (L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LR B n p PB dep fw lo PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0).
  Notation PTST' := (PTST sp). Notation PTXT' := (PTXT sp).
  Notation PFH' := (PFH ra sp s0 s1 s2 s3 s4 s5 s6 s7 F).

  Ltac facts :=
    pose proof CEIL as CEIL'; try rewrite alloc_ceiling_eq in CEIL'; pose proof LO as LO'; unfold PV_STACK, PV_BASE in LO';
    (nelimp PL 3%nat; intros PL1 PL2 PL3).

  Lemma canary_of : forall depc mm mo errv LB buf len off bs,
    NCTX' depc mm mo errv LB buf len off bs -> exists canary, OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.ssp_cells mm canary.
  Proof.
    intros until bs. intros CTX. pose proof CTX as (HL & _). (nelim (lh_ssp HI _ _ _ _ HL) 3%nat; intros G canary C).
    exists canary. unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.ssp_cells, OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.got_ssp, OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.ssp_guard. unfold PGOT_SSP, PSSP, wz in G, C. split; [exact G| exact C].
  Qed.

  (* [comment removed for export] *)
  Lemma num_R : forall mm mo t tx Fc fcc errv LB buf len off bs (r : Z)
      x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31,
    NCTX' dep mm mo errv LB buf len off bs -> PTST' mm t -> PTXT' mm tx -> PFH' mm -> frm0 fcc -> FAG18 F Fc ->
    0 <= r <= 25 ->
    SCPS usegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x14930) fcc None mm (seg_rom usegs)) mo.
  Proof.
    intros until x31. intros CTX H1 H2 H3 FRM FA Hr.
    assert (LTX : length tx = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    pose proof (nctx_actx HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 F m SPB LR PB fw lo _ _ _ _ _ _ _ _ _ _ _ _ CTX (pieces_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3) FRM FA) as ACT.
    pose proof CTX as (HL & _).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. apply evt_done. cbv beta.
    useA num_L; [exact ACT| exact LTX| exact Hr].
  Qed.

  (* [comment removed for export] *)
  Lemma num_G17 : forall mm mo t tx Fc fcc errv LB buf len off bs (vd : word)
      x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    NCTX' dep mm mo errv LB buf len off bs -> PTST' mm t -> PTXT' mm tx -> PFH' mm -> frm0 fcc -> FAG18 F Fc ->
    ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 ->
    SCPS usegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 x10 x11 x12 x13 x14 x15 x16 x17 vd (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x1491c) fcc None mm (seg_rom usegs)) mo.
  Proof.
    intros until x31. intros CTX H1 H2 H3 FRM FA DFIN. facts.
    assert (LTX : length tx = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    (nelimp CTX 11%nat; intros HL HP PBS0 ARR LEN PN ST ERR MI CJ PVA).
    destruct (canary_of _ _ _ _ _ _ _ _ _ CTX) as [canary SSP].
    (nelim (GTOT (bv_unsigned vd) 17 DFIN ltac:(right; reflexivity)) 4%nat; intros o EG OG OL).
    assert (O0 : 0 <= zlength o) by (unfold zlength; lia).
    unfold PTXT in H2.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. zstep. step. step.
    eapply evt_cut.
    { unfold F_printf_iface.sprintf_g_stmt in SPRG.
      eapply (SPRG 17) with (n := 32%nat) (junk := tx) (o := o) (r := zlength o) (lo := lo) (canary := canary);
        rewrite ?unsigned_lit by lia;
        first [ exact GRET | exact GLEN25 | exact H2 | exact EG | right; reflexivity | reflexivity
              | exact (GFACTS _ _ _ _ ltac:(right; reflexivity) EG) | exact ST | exact SSP | exact MI | exact FRM
              | unfold F_printf_iface.SPRINTF_DEPTH, F_printf_iface.GLOBALS_TOP in *; unfold zlength in *; lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 26%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc3 m3 -> MUc WMc MI3 FRM3 HFt ST3 TXT3 SSP3).
    rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in TXT3 by lia.
    unfold F_printf_iface.SPRINTF_DEPTH in *.
    unfold PTST in H1. unfold PFH in H3.
    pose proof ERR as ERR0. unfold PERRNO in ERR0.
    transport_after_call usegs mm m3 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x14930)) with (Z_to_bv 64 0x14930) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (CTX3 : NCTX' dep m3 mo errv LB buf len off bs).
    { eapply (nctx_call HI sp m SPB LR n PB fw lo PL CEIL LO); [exact CTX| exact MUc| exact WMc| exact MI3| exact ST3| unfold PERRNO; exact ERR0|].
      intros iv [<-|[<-|[]]]; left; cbn; lia. }
    apply evt_done. cbv beta.
    eapply (num_R m3 mo t); [exact CTX3| exact H1| unfold PTXT; exact TXT3| exact H3| exact FRM3| eapply FAG18_call10; [exact FA| exact HFt]| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma num_C : forall mm mo t tx Fc fcc errv LB buf len off bs (vd : word) (r : Z)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    NCTX' dep mm mo errv LB buf len off bs -> PTST' mm t -> PTXT' mm tx -> PFH' mm -> frm0 fcc -> FAG18 F Fc ->
    ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 -> 0 <= r <= 25 ->
    SCPS usegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16 x17 vd (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x148ec) fcc None mm (seg_rom usegs)) mo.
  Proof.
    intros until x31. intros CTX H1 H2 H3 FRM FA DFIN Hr. facts.
    assert (LTX : length tx = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    (nelimp CTX 11%nat; intros HL HP PBS0 ARR LEN PN ST ERR MI CJ PVA).
    (* [comment removed for export] *)
    assert (TAIL : forall (Fx : bvmap 5 word) (fcx : bv 32) (x10' : word), frm0 fcx -> FAG18 F Fx ->
      evt usegs (fun ms' => SCPS usegs POST ms' mo)
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) x10' x11 x12 x13 x14 x15 x16 x17 vd (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            Fx (Z_to_bv 64 0x14900) fcx None mm (seg_rom usegs))).
    { intros Fx fcx x10' FRMx FAx.
      step. step. step. step. step. step.
      step; rewrite bword_nez; if_cases K; [|].
      - apply evt_done. cbv beta.
        useA num_L; [| exact LTX| exact Hr].
        eapply (nctx_actx HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 F m SPB LR PB fw lo); [exact CTX| exact (pieces_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3)| assumption|].
        repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]). exact FAx.
      - apply evt_done. cbv beta.
        eapply num_G17; [exact CTX| exact H1| exact H2| exact H3| assumption| | exact DFIN].
        repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]). exact FAx. }
    unfold PTST in H1.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. step.
    step; rewrite bword_nez; if_cases K; [|].
    - eapply TAIL; [assumption|]. repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]). exact FA.
    - step. eapply TAIL; [assumption|]. repeat (apply FAG18_set; [| cbv; first [reflexivity| lia]]). exact FA.
  Qed.

  Ltac freg H n :=
    match goal with |- context [reg_get ?Fq ?r] =>
      let e := eval cbv in (bv_unsigned r) in
      lazymatch e with n => rewrite (H r eq_refl) end end.

  (* [comment removed for export] *)
  Lemma num_S : forall mm mo t tx Fc fcc errv LB buf len off bs (vd : word) (o : list Z) (r : Z)
      x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31,
    NCTX' dep mm mo errv LB buf len off bs -> PTST' mm t -> PTXT' mm (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.zb o ++ Z_to_bv 8 0 :: tx) -> PFH' mm -> frm0 fcc -> FAG18 F Fc ->
    ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 -> Forall num_gch o -> r = zlength o -> 0 <= r <= 25 ->
    SCPS usegs POST
      (MS (mkR (Z_to_bv 64 0x148cc) (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 vd (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x148cc) fcc None mm (seg_rom usegs)) mo.
  Proof.
    intros until x31. intros CTX H1 H2 H3 FRM FA DFIN OG Er Hr. facts.
    assert (LTX : length (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.zb o ++ Z_to_bv 8 0 :: tx) = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    pose proof LTX as LREST. rewrite length_app, zb_map, length_map in LREST. cbn [length] in LREST.
    (nelimp CTX 11%nat; intros HL HP PBS0 ARR LEN PN ST ERR MI CJ PVA).
    destruct (canary_of _ _ _ _ _ _ _ _ _ CTX) as [canary SSP].
    pose proof (bv_unsigned_in_range 64 sp) as SPR.
    (* [comment removed for export] *)
    set (txt := o ++ 0 :: map bv_unsigned tx).
    assert (LT : zlength txt = 32) by (subst txt; unfold zlength in *; rewrite length_app; cbn [length]; rewrite length_map; lia).
    destruct (scan_sscanf_lg (o ++ [0])) as [[rr res]|] eqn:ES.
    2:{ exfalso. exact (scan_sscanf_lg_total_gen o (gch_bytes o OG) (gch_nox o OG) ES). }
    assert (ES' : scan_sscanf_lg txt = Some (rr, res)) by (subst txt; rewrite (SJUNK o _ (gch_numch o OG)); exact ES).
    assert (TXTB : bytes_at usegs mm (bv_unsigned sp + -120) (map (Z_to_bv 8) txt)).
    { subst txt. rewrite map_app. cbn [map]. rewrite map_zb_unsigned, <- zb_map.
      destruct H2 as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY. exact BY. }
    assert (AL8 : (bv_unsigned sp + -120 + zlength txt) mod 8 = 0).
    { rewrite LT. pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)) as DM. rewrite SPAL, Z.add_0_r in DM. rewrite DM.
      replace (16 * (bv_unsigned sp / 16) + -120 + 32) with ((2 * (bv_unsigned sp / 16) - 11) * 8) by lia. apply Z.mod_mul. lia. }
    unfold PTST in H1. pose proof ERR as ERR0. unfold PERRNO in ERR0.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. zstep. zstep. zstep. step.
    eapply evt_cut.
    { unfold Scan_iface.rsscanf_lg_stmt in SSC.
      eapply SSC with (T := bv_unsigned sp + -120) (PD := bv_unsigned sp + -128) (txt := txt) (pre := o) (post := map bv_unsigned tx) (r := rr) (res := res) (djunk := t) (lo := lo) (canary := canary) (ev := errv);
        rewrite ?unsigned_lit by lia;
        first [ exact TXTB | exact H1 | exact ES' | exact MI | exact FRM | exact AL8 | exact ST | exact SSP | exact TP
              | subst txt; reflexivity
              | exact (gch_numch o OG)
              | unfold Scan_iface.RERRNO; exact ERR0
              | subst txt; apply Forall_app; split; [exact (gch_bytes o OG)| constructor; [lia| apply Forall_range_unsigned]]
              | reflexivity
              | f_equal; lia
              | unfold Scan_iface.RSSCANF_DEPTH, Scan_iface.RGLOBALS_TOP in *; unfold zlength in *; lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 29%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m3 ev' -> MUc WMc MI3 FRM2 HF2 ST3 TST3 TXB3 SSP3 ERR3).
    rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST3 by lia.
    unfold Scan_iface.RERRNO in MUc, ERR3. unfold Scan_iface.RSSCANF_DEPTH in *.
    unfold PTXT in H2. unfold PFH in H3. clear TXTB.
    transport_after_call usegs mm m3 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x148e4)) with (Z_to_bv 64 0x148e4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (CTX3 : NCTX' dep m3 mo ev' LB buf len off bs).
    { eapply (nctx_call HI sp m SPB LR n PB fw lo PL CEIL LO); [exact CTX| exact MUc| exact WMc| exact MI3| exact ST3| unfold PERRNO; exact ERR3|].
      intros iv [<-|[<-|[<-|[]]]]; [left; cbn; lia| left; cbn; lia| right; reflexivity]. }
    assert (FA2 : FAG18 F F2) by (eapply FAG18_call3; [exact FA| exact HF2]).
    zstep. step. if_cases K; zify_cond K.
    - apply evt_done. cbv beta.
      eapply num_G17; [exact CTX3| unfold PTST; exact TST3| exact H2| exact H3| exact FRM2| exact FA2| exact DFIN].
    - apply evt_done. cbv beta.
      eapply num_C; [exact CTX3| unfold PTST; exact TST3| exact H2| exact H3| exact FRM2| exact FA2| exact DFIN| exact Hr].
  Qed.

  (* [comment removed for export] *)
  Lemma num_G15 : forall mm mo t tx Fc fcc errv LB buf len off bs (vd : word)
      x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31,
    NCTX' dep mm mo errv LB buf len off bs -> PTST' mm t -> PTXT' mm tx -> PFH' mm -> frm0 fcc -> FAG18 F Fc ->
    (forall r : bv 5, bv_unsigned r = 8 -> reg_get Fc r = vd) -> ((bv_unsigned vd mod 2^64) / 2^52) mod 2^11 <> 2047 ->
    SCPS usegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x148b4) fcc None mm (seg_rom usegs)) mo.
  Proof.
    intros until x31. intros CTX H1 H2 H3 FRM FA HF8 DFIN. facts.
    assert (LTX : length tx = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    (nelimp CTX 11%nat; intros HL HP PBS0 ARR LEN PN ST ERR MI CJ PVA).
    destruct (canary_of _ _ _ _ _ _ _ _ _ CTX) as [canary SSP].
    (nelim (GTOT (bv_unsigned vd) 15 DFIN ltac:(left; reflexivity)) 4%nat; intros o EG OG OL).
    assert (O0 : 0 <= zlength o) by (unfold zlength; lia).
    unfold PTXT in H2.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. freg HF8 8. step. zstep. step. step. step.
    eapply evt_cut.
    { unfold F_printf_iface.sprintf_g_stmt in SPRG.
      eapply (SPRG 15) with (n := 32%nat) (junk := tx) (o := o) (r := zlength o) (lo := lo) (canary := canary);
        rewrite ?unsigned_lit by lia;
        first [ exact GRET | exact GLEN25 | exact H2 | exact EG | left; reflexivity | reflexivity
              | exact (GFACTS _ _ _ _ ltac:(left; reflexivity) EG) | exact ST | exact SSP | exact MI | exact FRM
              | unfold F_printf_iface.SPRINTF_DEPTH, F_printf_iface.GLOBALS_TOP in *; unfold zlength in *; lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 26%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc3 m3 -> MUc WMc MI3 FRM3 HFt ST3 TXT3 SSP3).
    rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in TXT3 by lia.
    unfold F_printf_iface.SPRINTF_DEPTH in *.
    unfold PTST in H1. unfold PFH in H3.
    pose proof ERR as ERR0. unfold PERRNO in ERR0.
    transport_after_call usegs mm m3 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x148cc)) with (Z_to_bv 64 0x148cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (CTX3 : NCTX' dep m3 mo errv LB buf len off bs).
    { eapply (nctx_call HI sp m SPB LR n PB fw lo PL CEIL LO); [exact CTX| exact MUc| exact WMc| exact MI3| exact ST3| unfold PERRNO; exact ERR0|].
      intros iv [<-|[<-|[]]]; left; cbn; lia. }
    apply evt_done. cbv beta.
    eapply (num_S m3 mo t); [exact CTX3| exact H1| exact TXT3| exact H3| exact FRM3| eapply FAG18_call10; [exact FA| exact HFt]| exact DFIN| exact OG| reflexivity| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma num_D : forall mm mo t tx Fc fcc errv LB buf len off bs (wi : word)
      x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31,
    NCTX' dep mm mo errv LB buf len off bs -> PTST' mm t -> PTXT' mm tx -> PFH' mm -> frm0 fcc -> FAG18 F Fc ->
    SCPS usegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 x10 x11 wi x13 x14 x15 x16 x17 x18 (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x14868) fcc None mm (seg_rom usegs)) mo.
  Proof.
    intros until x31. intros CTX H1 H2 H3 FRM FA. facts.
    assert (LTX : length tx = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    (nelimp CTX 11%nat; intros HL HP PBS0 ARR LEN PN ST ERR MI CJ PVA).
    destruct (canary_of _ _ _ _ _ _ _ _ _ CTX) as [canary SSP].
    (nelim (word_int_arg wi) 3%nat; intros i Ei Ri).
    (nelim (DTOT i) 5%nat; intros o ED OG _ OL). specialize (OL Ri).
    assert (O0 : 0 <= zlength o) by (unfold zlength; lia).
    unfold PTXT in H2.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. zstep. step. step. step.
    eapply evt_cut.
    { unfold F_printf_iface.sprintf_d_stmt in SPRD.
      eapply SPRD with (n := 32%nat) (junk := tx) (i := i) (o := o) (r := zlength o) (lo := lo) (canary := canary);
        rewrite ?unsigned_lit by lia;
        first [ exact H2 | exact Ei | exact Ri | exact ED | reflexivity
              | exact ST | exact SSP | exact MI | exact FRM
              | unfold F_printf_iface.SPRINTF_DEPTH, F_printf_iface.GLOBALS_TOP in *; unfold zlength in *; lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 26%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc3 m3 -> MUc WMc MI3 FRM3 HFt ST3 TXT3 SSP3).
    rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in TXT3 by lia.
    unfold F_printf_iface.SPRINTF_DEPTH in *.
    unfold PTST in H1. unfold PFH in H3.
    pose proof ERR as ERR0. unfold PERRNO in ERR0.
    transport_after_call usegs mm m3 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x14930)) with (Z_to_bv 64 0x14930) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (CTX3 : NCTX' dep m3 mo errv LB buf len off bs).
    { eapply (nctx_call HI sp m SPB LR n PB fw lo PL CEIL LO); [exact CTX| exact MUc| exact WMc| exact MI3| exact ST3| unfold PERRNO; exact ERR0|].
      intros iv [<-|[<-|[]]]; left; cbn; lia. }
    apply evt_done. cbv beta.
    eapply (num_R m3 mo t);
      [exact CTX3| exact H1| unfold PTXT; exact TXT3| exact H3| exact FRM3| eapply FAG18_call10; [exact FA| exact HFt]| lia].
  Qed.
End S.


End CeilWrap.
