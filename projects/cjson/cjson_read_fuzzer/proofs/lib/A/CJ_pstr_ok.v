(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_traces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_fmt_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fmt_glue.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_ensure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pstr.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_traces OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fmt_glue.ICPT_fmt_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fmt_glue OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_ensure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrN OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrB.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; unfold APSTR_STACK, AFORMAT_STACK, AENSURE_STACK, AMALLOC_STACK, AINTRIN_STACK in *; lia | sclr_tac2 ].
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac dlia := cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | lia].

(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr asegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.

Section S.
  Variables (AI : art_iface) (TI : trs_iface).
  Hypothesis SPRU : asprintf_u04x_stmt_b.
  Hypothesis MEMSET : asan_memset_spec.
  Hypothesis MEMCPY : asan_memcpy_spec.

  Section Call.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
              (m : word -> option byte) (g : lghost)
              (sp0 SPB : Z) (LB LR Bv : list cblock) (LF : list fframe) (TRS : list (list Z)) (np BB : Z)
              (PB buf len off dep s : Z) (fw : word) (bs : list byte) (lo : Z) (errv : word).
    Hypothesis HP : Permutation ((buf, len) :: LR) LB.
    Hypothesis PN : pb_nums len off dep.
    Hypothesis SV : cj_str m s Bv.
    Hypothesis BVLR : forall b, In b Bv -> In b LR.
    Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
    Hypothesis SP16 : bv_unsigned sp + 16 <= PB.
    Hypothesis P80 : PB + 80 <= 2^47.
    Hypothesis SP0 : sp0 <= 2^47.
    Hypothesis TOP : bv_unsigned sp + 16 < ASTACK_TOP sp0.
    Hypothesis BOT : ASTACK_BOTTOM sp0 <= lo.
    Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - APSTR_STACK.
    Hypothesis TP : tp = wz ATP.
    Hypothesis LEN : Z.of_nat (length bs) = len.
    Hypothesis NPR : np + pb_npallow len <= NPMAX TI.
    Hypothesis HB : pb_allow len <= BB.
    Hypothesis R : ablock_range buf len.
    Hypothesis RA1 : 4096 <= bv_unsigned ra.
    Hypothesis RA2 : ~ is_pc0 (bv_unsigned ra).

    Notation POST := (pstr_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np BB PB len dep fw lo m g).
    Notation SPF := (bv_unsigned sp + -112).
    Notation FRAME mm c0 := (rw_cells asegs mm (bv_unsigned sp + -112)
       [c0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    Notation PBS mm b l := (rw_cells asegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 off); C8 (Z_to_bv 64 dep);
                                              C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 AMALLOC); C8 (Z_to_bv 64 AFREE); C8 (Z_to_bv 64 AREALLOC)]).
    Notation SHB := (Z_to_bv 64 0x7fff8000).
    Notation NINV := (ninv AI TI sp m g sp0 SPB LR LF PB lo).

    Lemma SPFeq' : bv_unsigned (Z_to_bv 64 SPF) = SPF.
    Proof. apply unsigned_lit. alia. Qed.
    Lemma SPtop' : bv_unsigned sp + 16 <= sp0 + 4096.
    Proof. clear -TOP. unfold ASTACK_TOP, roundup in TOP. Z.div_mod_to_equations. lia. Qed.

    (* [comment removed for export] *)
    Section Room.
      Variables (m2 : word -> option byte) (mo2 : Model) (g2 : lghost) (LB2 : list cblock) (TRS2 : list (list Z)) (B2 np2 : Z)
                (B len' n : Z) (bs2 : list byte) (errv2 : word) (str tail : list byte) (fc0 : bv 32).
      Notation L := (Z.of_nat (length str)).
      Notation E := (esc_count str).
      Notation OUT := (B + off).
      Notation full := (str ++ wb 0 :: tail).
      Hypothesis HL2 : ART AI sp0 SPB LB2 LF TRS2 B2 m2 mo2 g2.
      Hypothesis TV2 : TINV TI np2 TRS2.
      Hypothesis GM2 : gmono g g2.
      Hypothesis HP2 : Permutation ((B, len') :: LR) LB2.
      Hypothesis LEN2 : Z.of_nat (length bs2) = len'.
      Hypothesis ROOM : L + E + 3 + off + 1 <= len'.
      Hypothesis L31 : len' < 2^31.
      Hypothesis LL : len <= len'.
      Hypothesis HB2 : BB - (pb_pot len' - pb_pot len) <= B2.
      Hypothesis HN2 : np2 <= np + (pb_npot len' - pb_npot len).
      Hypothesis PVA2 : pv_agree sp0 LR LF (bv_unsigned sp) PB m m2.
      Hypothesis SSZ2 : sh_zero m2 alloc_ceiling (2^47).
      Hypothesis SNZ : s <> 0.
      Hypothesis EBv : Bv = [(s, n)].
      Hypothesis NONUL : ~ In (wb 0) str.
      Hypothesis LENS : L + 1 + Z.of_nat (length tail) = n.
      Hypothesis FRM0 : frm0 fc0.

      Notation WE2 := (WE str B off lo sp).

      Lemma blkB : ablock_range B len'.
      Proof. exact (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HP2)). Qed.

      Lemma blkS : In (s, n) LB2 /\ (s + n <= B \/ B + len' <= s) /\ ablock_range s n /\ B <> s.
      Proof.
        assert (IN : In (s, n) LR). { apply BVLR. rewrite EBv. left. reflexivity. }
        destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL2 HP2 s n IN) as [NE D].
        assert (IN2 : In (s, n) LB2) by (eapply Permutation_in; [exact HP2| right; exact IN]).
        split; [exact IN2|]. split; [lia|]. split; [exact (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL2 IN2)| auto].
      Qed.

      Ltac pre :=
        pose proof CEIL as CEIL'; pose proof LO as LO'; unfold APSTR_STACK, AFORMAT_STACK in LO'; try rewrite alloc_ceiling_eq in CEIL';
        (nelimp blkB 4%nat; intros B1 B2' B3 B4); pose proof blkS as (SIN & SD & (S1 & S2' & S3 & S4) & NBS);
        unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in B1, S1; try rewrite alloc_ceiling_eq in B4, S4;
        (nelimp PL 3%nat; intros PL1 PL2 PL3); (nelimp PN 3%nat; intros PN1 PN2 PN3);
        pose proof (esc_count_range str) as ER.

      (* [comment removed for export] *)
      Lemma room_end : forall mx mm c0, FRAME mx c0 -> Cells.csize c0 = 8%nat -> rw_cells asegs mx AERRNO [C4 errv2] -> PBS mx B len' ->
        ART AI sp0 SPB LB2 LF TRS2 B2 mx mo2 g2 -> pv_agree sp0 LR LF (bv_unsigned sp) PB m mx ->
        munch WE2 mx mm -> wmono asegs mx mm ->
        FRAME mm c0 /\ rw_cells asegs mm AERRNO [C4 errv2] /\ PBS mm B len'
        /\ pv_agree sp0 LR LF (bv_unsigned sp) PB m mm /\ ART AI sp0 SPB LB2 LF TRS2 B2 mm mo2 g2.
      Proof.
        intros mx mm c0 FR2 C8 ERR2 PBS2 HLx PVAx MU WM. pre. unfold WE in MU.
        split; [|split; [|split; [|split]]].
        - eapply rw_cells_transport; [exact FR2| exact MU| exact WM|]. cbn [disjoint_from cells_size]. rewrite C8. cbn. lia.
        - eapply rw_cells_transport; [exact ERR2| exact MU| exact WM|]. unfold AERRNO, ATP. dlia.
        - eapply rw_cells_transport; [exact PBS2| exact MU| exact WM|]. dlia.
        - eapply pv_agree_trans; [exact PVAx|]. eapply (pv_agree_of_munchW AI); [exact HLx| exact HP2| exact MU| exact WM| | lia| lia| lia].
          constructor; [right; right; left; cbn; lia|]. constructor; [do 3 right; cbn; lia| constructor].
        - eapply (art_frame AI); [exact HLx| exact MU| exact WM|].
          constructor; [right; left; cbn; lia|]. constructor; [|constructor].
          do 7 right. left. exists B, len'. split; [eapply perm_in_head; exact HP2| cbn; lia].
      Qed.

      (* [comment removed for export] *)
      Lemma pstr_18 : forall mx mm bsc c0 Fc fcc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
        FRAME mx c0 -> Cells.csize c0 = 8%nat -> rw_cells asegs mx AERRNO [C4 errv2] -> PBS mx B len' ->
        ART AI sp0 SPB LB2 LF TRS2 B2 mx mo2 g2 -> pv_agree sp0 LR LF (bv_unsigned sp) PB m mx ->
        u8arr asegs mm B bsc -> Z.of_nat (length bsc) = len' -> munch WE2 mx mm -> wmono asegs mx mm -> mem_inv asegs mm ->
        stk asegs mm lo SPF -> frm0 fcc -> (forall k : bv 5, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k) ->
        LSCPS asegs POST
          (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (OUT + E + L)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              Fc (Z_to_bv 64 0x873ac) fcc None mm (seg_rom asegs)) mo2 g2.
      Proof.
        intros until x31. intros FR2 C8 ERR2 PBS2 HLx PVAx ARR LENc MU WM MI ST FRM FA. pre. unfold WE in MU.
        eapply lscps_step_evt. cbv beta delta [mkR].
        ustore_at B off (OUT + E + L + 2) (L + E + 2) (wb 0) ltac:(reflexivity).
        apply evt_done. cbv beta.
        lazymatch goal with |- LSCPS _ _ (MS _ _ _ _ _ ?mc _) _ _ =>
          (nelim (room_end mx mc c0 FR2 C8 ERR2 PBS2 HLx PVAx ltac:(exact MU) ltac:(exact WM)) 5%nat; intros FR' ERR' PBS' PVA' HL') end.
        eapply (pstr_ret1 AI TI); try eassumption; try reflexivity.
        - intros k Hk. apply FA. destruct Hk as [Hk|[Hk|Hk]]; lia.
        - split; [exact ARR| rewrite upd_length; exact LENc].
        - exists (L + E + 2). split; [lia|]. split; [lia|]. apply nth_error_upd_same. lia.
      Qed.

      (* [comment removed for export] *)
      Lemma pstr_tailq : forall (pc : Z) mx mm bsc c0 Fc fcc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31,
        pc = 0x87320 \/ pc = 0x87374 ->
        FRAME mx c0 -> Cells.csize c0 = 8%nat -> rw_cells asegs mx AERRNO [C4 errv2] -> PBS mx B len' ->
        ART AI sp0 SPB LB2 LF TRS2 B2 mx mo2 g2 -> pv_agree sp0 LR LF (bv_unsigned sp) PB m mx ->
        u8arr asegs mm B bsc -> Z.of_nat (length bsc) = len' -> munch WE2 mx mm -> wmono asegs mx mm -> mem_inv asegs mm ->
        stk asegs mm lo SPF -> frm0 fcc -> (forall k : bv 5, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k) ->
        LSCPS asegs POST
          (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 SHB (Z_to_bv 64 L) (Z_to_bv 64 E) x22 x23 x24 x25 (Z_to_bv 64 OUT) x27 x28 x29 x30 x31)
              Fc (Z_to_bv 64 pc) fcc None mm (seg_rom asegs)) mo2 g2.
      Proof using BVLR CEIL EBv GM2 HB2 HL2 HN2 HP2 L31 LL LO P80 PL PN ROOM SNZ SP0 SP16 TV2 bs bs2 tail. clear SPAL LENS.
        intros until x31. intros Hpc FR2 C8 ERR2 PBS2 HLx PVAx ARR LENc MU WM MI ST FRM FA. pre.
        (* [comment removed for export] *)
        assert (HLM : forall mc, munch WE2 mx mc -> wmono asegs mx mc -> ART AI sp0 SPB LB2 LF TRS2 B2 mc mo2 g2).
        { intros mc MUc WMc. eapply (art_frame AI); [exact HLx| exact MUc| exact WMc|]. unfold WE.
          constructor; [right; left; cbn; lia|]. constructor; [|constructor].
          do 7 right. left. exists B, len'. split; [eapply perm_in_head; exact HP2| cbn; lia]. }
        destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ (HLM mm MU WM) (perm_in_head _ _ _ HP2)) as [_ SOB].
        pose proof (shadow_ok_shchk1 mm B len' (OUT + E + L + 1) SOB ltac:(lia)) as CK1.
        unfold WE in MU, HLM.
        destruct Hpc as [-> | ->].
        - eapply lscps_step_evt. cbv beta delta [mkR].
          zstep. zstep. zstep. zstep. zstep. sepM. asan_chk CK1. zstep. zstep.
          ustore_at B off (OUT + E + L + 1) (L + E + 1) (wb 34) ltac:(reflexivity).
          pose proof (shadow_ok_shchk1 m0 B len' (OUT + E + L + 2) (proj2 (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ (HLM m0 MU WM) (perm_in_head _ _ _ HP2))) ltac:(lia)) as CK2'.
          zstep. zstep. sepM. asan_chk CK2'.
          apply evt_done. cbv beta.
          eapply pstr_18; [exact FR2| exact C8| exact ERR2| exact PBS2| exact HLx| exact PVAx| exact ARR| rewrite upd_length; exact LENc| exact MU| exact WM| exact MI| exact ST| exact FRM| exact FA].
        - eapply lscps_step_evt. cbv beta delta [mkR].
          zstep. zstep. zstep. zstep. zstep. sepM. asan_chk CK1. zstep. zstep.
          ustore_at B off (OUT + E + L + 1) (L + E + 1) (wb 34) ltac:(reflexivity).
          pose proof (shadow_ok_shchk1 m0 B len' (OUT + E + L + 2) (proj2 (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ (HLM m0 MU WM) (perm_in_head _ _ _ HP2))) ltac:(lia)) as CK2'.
          zstep. zstep. sepM. asan_chk CK2'.
          apply evt_done. cbv beta.
          eapply pstr_18; [exact FR2| exact C8| exact ERR2| exact PBS2| exact HLx| exact PVAx| exact ARR| rewrite upd_length; exact LENc| exact MU| exact WM| exact MI| exact ST| exact FRM| exact FA].
      Qed.

      (* [comment removed for export] *)
      Lemma pstr_room : forall j0 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
        FRAME m2 (CB 8 j0) -> rw_cells asegs m2 AERRNO [C4 errv2] -> PBS m2 B len' -> u8arr asegs m2 B bs2 ->
        stk asegs m2 lo SPF -> mem_inv asegs m2 -> bytes_at asegs m2 s full ->
        LSCPS asegs POST
          (MS (mkR (Z_to_bv 64 0x87048) (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 s) s1 (Z_to_bv 64 OUT) x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 (E + L)) SHB (Z_to_bv 64 L) (Z_to_bv 64 E) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x8704c) fc0 None m2 (seg_rom asegs)) mo2 g2.
      Proof.
        intros until x31. intros FR ERR PBSc ARR ST MI STR. pre.
        pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
        destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HP2)) as [_ SOB].
        unfold AERRNO, ATP in ERR.
        (* [comment removed for export] *)
        pose proof (munch_refl [(SPF, SPF + 8); (OUT, OUT + (L + E + 3))] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
        (* [comment removed for export] *)
        assert (REBASE : forall mx, munch [(SPF, SPF + 8); (OUT, OUT + (L + E + 3))] m2 mx -> wmono asegs m2 mx ->
                  ART AI sp0 SPB LB2 LF TRS2 B2 mx mo2 g2 /\ pv_agree sp0 LR LF (bv_unsigned sp) PB m mx
                  /\ sh_zero mx alloc_ceiling (2^47) /\ bytes_at asegs mx s full).
        { intros mx MUx WMx. split; [| split; [| split]].
          - eapply (art_frame AI); [exact HL2| exact MUx| exact WMx|]. constructor; [right; left; cbn; lia|]. constructor; [|constructor].
            do 7 right. left. exists B, len'. split; [eapply perm_in_head; exact HP2| cbn; lia].
          - eapply pv_agree_trans; [exact PVA2|]. eapply (pv_agree_of_munchW AI); [exact HL2| exact HP2| exact MUx| exact WMx| | lia| lia| lia].
            constructor; [right; right; left; cbn; lia|]. constructor; [do 3 right; cbn; lia| constructor].
          - try rewrite <- alloc_ceiling_eq in *. eapply sh_zero_stack_munch; [exact SSZ2| exact MUx|].
            constructor; [cbn [fst snd]; sclr_tac2|]. constructor; [cbn [fst snd]; sclr_tac2| constructor].
          - eapply bytes_at_transport; [exact STR| exact MUx|]. rewrite length_app. cbn [length disjoint_from]. lia. }
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. zstep. zstep.
        pose proof (shadow_ok_shchk1 m2 B len' OUT SOB ltac:(lia)) as CK0. sepM. asan_chk CK0.
        zstep.
        ustore_at B off (B + off) 0 (wb 34) ltac:(reflexivity).
        zstep. if_cases KE; zify_cond KE.
        - (* [comment removed for export] *)
          zstep. zstep. zstep. zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2a end.
          (nelim (REBASE m2a MU WM) 4%nat; intros HLa PVAa SSZa STRa).
          (nelim (u8arr_split3 m2a B _ (Z.to_nat (off + 1)) (length str) ARR ltac:(rewrite upd_length; lia)) 3%nat; intros A1 A2 A3).
          rewrite (Z2Nat.id (off + 1)) in A2, A3 by lia. replace (B + (off + 1)) with (OUT + 1) in A2, A3 by lia.
          pose proof STRa as SRC. apply bytes_at_app in SRC. destruct SRC as [SRC _].
          destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HLa (perm_in_head _ _ _ HP2)) as [_ SOB'].
          destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HLa SIN) as [_ SOS'].
          clear ARR.
          eapply evt_cut.
          { pose proof MEMCPY as MCX. unfold asan_memcpy_spec, memcpy_contract in MCX.
            sepM. eapply MCX with (lo := lo) (d := OUT + 1) (s := s) (n := E + L) (src := str); clear MCX; rewrite ?unsigned_lit by lia;
              first [ lazymatch goal with |- icpt_cells _ => eapply (art_icpt_cells' AI); exact HLa end | exact MI | exact ST | exact SRC
                    | lazymatch goal with |- context [(Z.to_nat (E + L))] => replace (Z.to_nat (E + L)) with (length str) by lia; exact A2 end | reflexivity
                    | lazymatch goal with |- app_range _ _ => app_rng0 end
                    | apply wr_range_ok_high; lia
                    | intros Hn0; eapply shadow_ok_sub; [exact SOS'| lia| lia| lia]
                    | intros Hn0; eapply shadow_ok_sub; [exact SOB'| lia| lia| lia]
                    | alia | lia ]. }
          cbv beta. intros ms' PO.
          (nelim PO 22%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MUc WMc MI' DST SRC' ST').
          rewrite SPFeq' in MUc, ST'. rewrite ?unsigned_lit in DST by lia. unfold AINTRIN_STACK in MUc.
          replace (ret_pc (Z_to_bv 64 0x87374)) with (Z_to_bv 64 0x87374) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          apply (u8arr_transport asegs _ _ m' _ _ A1) in MUc as A1'; [| exact WMc| cbn [disjoint_from]; rewrite firstn_length_le by (rewrite upd_length; lia); split; [lia| split; [lia| exact I]]].
          apply (u8arr_transport asegs _ _ m' _ _ A3) in MUc as A3'; [| exact WMc| cbn [disjoint_from]; rewrite length_skipn, upd_length; split; [lia| split; [lia| exact I]]].
          replace (Z.to_nat (E + L)) with (length str) in DST by lia.
          replace (OUT + 1) with (B + (off + 1)) in DST, A3' by lia.
          destruct (u8arr_join3' m' B _ (off + 1) _ _ _ A1' ltac:(rewrite firstn_length_le by (rewrite upd_length; lia); lia) DST A3') as [ARR _].
          assert (MU2 : munch WE2 m2a m').
          { eapply munch_weaken; [| exact MUc]. unfold WE, sub_fp. cbn. intros a [X [Y _]]. lia. }
          lazymatch type of ARR with u8arr _ _ _ ?l =>
            assert (LENj : Z.of_nat (length l) = len')
              by (rewrite !length_app, firstn_length_le, length_skipn, upd_length by (rewrite ?upd_length; lia); lia) end.
          apply evt_done. cbv beta.
          eapply (pstr_tailq 0x87374); [right; reflexivity| exact FR| reflexivity| exact ERR| exact PBSc| exact HLa| exact PVAa| exact ARR| exact LENj| exact MU2| exact WMc| exact MI'| exact ST'| exact FRM0| intros k Hk; reflexivity].
        - (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2a end.
          (nelim (REBASE m2a MU WM) 4%nat; intros HLa _ _ STRa).
          destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HLa SIN) as [_ SOS'].
          pose proof (shadow_ok_shchk1 m2a s n s SOS' ltac:(lia)) as CKS.
          zstep. zstep. sepM. asan_chk CKS.
          pose proof (ch_read s str tail m2a 0 STRa ltac:(lia)) as RD0. rewrite Z.add_0_r in RD0.
          destruct (ch_range str tail NONUL 0 ltac:(lia)) as [CR0 CZ0].
          zstep. zstep. rewrite (land255 (bv_unsigned (chb str tail 0))) by lia.
          zstep. if_cases KL; zify_cond KL; [exfalso; lia|].
          do 7 zstep.
          (* [comment removed for export] *)
          zstep. fix_lit_store.
          do 3 zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
          clear HLa STRa SOS' RD0.
          (nelim (REBASE m3 MU WM) 4%nat; intros HL3 PVA3 SSZ3 STR3).
          destruct (rw_cells_app_split m3 _ [C8 (Z_to_bv 64 A_FMT_u04x)] _ FR) as [FMT3 _].
          pose proof (emit_loop AI SPRU s str tail NONUL m3 mo2 g2 sp0 SPB LB2 LF TRS2 B2 B off len' n lo sp F gp tp
                        HL3 (perm_in_head _ _ _ HP2) SIN NBS STR3 LENS ltac:(lia) ltac:(lia)
                        ltac:(try rewrite alloc_ceiling_eq; unfold AFORMAT_STACK; lia) ltac:(lia) ltac:(lia) SSZ3 FMT3
                        (Z.to_nat L) 0 ltac:(lia) ltac:(lia)) as HK.
          unfold HEADK in HK. rewrite (pos_0 str), !Z.add_0_r in HK. unfold AEJT in HK.
          eapply evt_cut.
          { eapply HK; [| exact FRM0| intros k Hk; reflexivity].
            split; [exact ARR|]. split; [rewrite upd_length; exact LEN2|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
            split; [exact MI| exact ST]. }
          cbv beta. intros ms' PO.
          (nelim PO 24%nat; intros mm bsc' Fc fcc x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' -> INV FRM' FA')
.
          (nelim INV 6%nat; intros ARR' LENc MU' WM' MI3 ST3).
          apply evt_done. cbv beta.
          eapply (pstr_tailq 0x87320); [left; reflexivity| exact FR| reflexivity| exact ERR| exact PBSc| exact HL3| exact PVA3| exact ARR'| exact LENc| exact MU'| exact WM'| exact MI3| exact ST3| exact FRM'| exact FA'].
      Qed.
    End Room.

    (* [comment removed for export] *)
    Lemma prologue : forall (mo : Model) (fc : bv 32) (t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ART AI sp0 SPB LB LF TRS BB m mo g -> TINV TI np TRS ->
      PBS m buf len -> u8arr asegs m buf bs -> pb_below m PB -> sh_zero m alloc_ceiling (2^47) ->
      stk asegs m lo (bv_unsigned sp) -> rw_cells asegs m AERRNO [C4 errv] -> mem_inv asegs m -> cj_str m s Bv ->
      evt asegs (fun ms' => exists m1 j0,
                   ms' = MS (mkR ra (Z_to_bv 64 SPF) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 PB) (Z_to_bv 64 0xaa278) a3 a4 a5 a6 a7 s2 SHB s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 0x86f88) fc None m1 (seg_rom asegs)
                   /\ NINV m1 mo g LB TRS BB np /\ FRAME m1 (CB 8 j0) /\ PBS m1 buf len /\ u8arr asegs m1 buf bs /\ cj_str m1 s Bv)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 PB) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86f44) fc None m (seg_rom asegs)).
    Proof.
      intros until t6. intros HL TV PBS0 ARR PBW SSZ ST ERR MI SV'.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'.
      pose proof SPtop' as SPT.
      (nelimp R 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). unfold AERRNO, ATP in ERR.
      pose proof (conj ERR I) as ERRbox. clear ERR. pose proof (conj PBS0 I) as PBSbox. clear PBS0.
      destruct ARR as [ABY AWR]. (nelim PBW 4%nat; intros w1 w2 BY16 Hw1).
      pose proof (art_shbase AI _ _ _ _ _ _ _ _ _ HL) as SBC. shbase_split SBC.
      pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      carve_frame 112%nat ST.
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      sepM. do 14 zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      apply evt_done.
      lazymatch goal with |- exists _ _, MS _ _ _ _ _ ?mc _ = _ /\ _ => rename mc into m1 end.
      assert (HL1 : ART AI sp0 SPB LB LF TRS BB m1 mo g) by (eapply (art_frame_store AI); [exact HL| exact MU| exact WM| alia| lia]).
      do 2 eexists. split; [reflexivity|]. split; [| split; [exact FR| split; [| split]]].
      - split; [exact HL1|]. split; [exact ST|]. split; [assumption|]. split.
        { exists errv. eapply errno_high_store; [exact (proj1 ERRbox)| exact MU| exact WM| alia]. }
        split. { eapply (pv_agree_stack AI); [exact HL| intros b Hb; eapply Permutation_in; [exact HP| right; exact Hb]| exact MU| exact WM| alia| lia| lia| lia]. }
        split. { eapply sh_zero_stack_munch; [exact SSZ| exact MU|]. constructor; [cbn [fst snd]; sclr_tac2| constructor]. }
        split. { exists w1, w2. split; [| exact Hw1]. first [exact BY16 | eapply (bytes_at_transport asegs); [exact BY16| exact MU| rewrite length_app, !length_le8; cbn; lia]]. }
        split; [apply gmono_refl| exact TV].
      - eapply (rw_cells_transport asegs); [exact (proj1 PBSbox)| exact MU| exact WM| cbn; lia].
      - split; [| first [exact AWR | eapply wr_at_transport; [exact AWR| exact WM]]]. first [exact ABY | eapply (bytes_at_transport asegs); [exact ABY| exact MU| cbn; lia]].
      - eapply (cj_str_magree _ m m1); [| exact SV'|].
        + eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha Hin. exact Hin.
        + intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr). cbn. split; [| exact I].
          assert (IN : In (A', n') LB). { eapply Permutation_in; [exact HP|]. right. apply BVLR. exact Hin. }
          (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL IN) 4%nat; intros _ _ _ X4). try rewrite alloc_ceiling_eq in X4. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_nonnull : forall (mo : Model) (fc : bv 32) (n : Z) (str tail : list byte) m1 j0
        (t0 t1 t2 a0' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      NINV m1 mo g LB TRS BB np -> FRAME m1 (CB 8 j0) -> PBS m1 buf len -> u8arr asegs m1 buf bs -> frm0 fc ->
      s <> 0 -> Bv = [(s, n)] -> bytes_at asegs m1 s (str ++ wb 0 :: tail) -> ~ In (wb 0) str ->
      Z.of_nat (length str) + 1 + Z.of_nat (length tail) = n ->
      LSCPS asegs POST
        (MS (mkR ra (Z_to_bv 64 SPF) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 PB) (Z_to_bv 64 0xaa278) a3 a4 a5 a6 a7 s2 SHB s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86f88) fc None m1 (seg_rom asegs)) mo g.
    Proof.
      intros until t6. intros NI FR PBS1 ARR FRM SNZ EBv STR NONUL LENS. (nelimp NI 9%nat; intros HL ST1 MI1 [e ERR] PVA SSZ1 PBW1 GM1 TV1).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'.
      pose proof SPFeq' as E1. pose proof SPtop' as SPT.
      (nelimp R 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold AERRNO, ATP in ERR.
      pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
      (* [comment removed for export] *)
      assert (SIN : In (s, n) LB). { eapply Permutation_in; [exact HP|]. right. apply BVLR. rewrite EBv. left. reflexivity. }
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL SIN) 4%nat; intros Q1 Q2 Q3 Q4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Q1. bandM. sepM. try rewrite alloc_ceiling_eq in Q4.
      destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HL SIN) as [_ SOS].
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
      do 8 zstep.
      (* [comment removed for export] *)
      eapply evt_cut; [eapply (count_loop s str tail NONUL m1 n STR SOS LENS ltac:(split; [unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| try rewrite alloc_ceiling_eq; lia]))|].
      cbv beta. intros ms' nelH_; (nelim nelH_ 3%nat; intros c15 c16 ->).
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      apply evt_done. cbv beta.
      pose proof (esc_count_range str) as ER.
      eapply lscps_bind.
      { eapply (ensure_ok AI TI) with (lo := lo) (LR := LR) (bs := bs) (needed := esc_count str + Z.of_nat (length str) + 3); rewrite ?E1;
          first [ exact HL | exact HP | exact PBS1 | split; [exact ARR| exact LEN] | exact PN | exact ST1 | exact ERR | exact MI1 | exact TP | reflexivity
                | exact PBW1 | exact SSZ1 | exact TV1
                | split; [lia| split; [lia| lia]]
                | apply Z.mod_divide; [lia|]; apply Z.mod_divide in SPAL; [| lia]; destruct SPAL as [q Hq]; exists (q - 7); lia
                | pose proof (pb_npallow_ge2 len ltac:(rewrite INT_MAX_eq; lia)); lia
                | unfold AENSURE_STACK, AMALLOC_STACK; lia | alia | lia ]. }
      cbv beta. intros ms2 mo2 g2 PO.
      (nelim PO 30%nat; intros t0' t1' t2' a0'' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 LB2 TRS2 B2 np2 -> MI2 ST2 ERR2 PVE HL2 TV2 GM2 OUT)
.
      rewrite E1 in ST2, PVE. unfold AERRNO in ERR2.
      replace (ret_pc (Z_to_bv 64 0x87048)) with (Z_to_bv 64 0x87048) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (* [comment removed for export] *)
      apply (pv_agree_rw_cells_stack _ _ _ _ _ _ _ _ _ PVE) in FR; [| lia| cbn; lia| cbn; lia].
      assert (STR2 : bytes_at asegs m2 s (str ++ wb 0 :: tail)).
      { eapply (pv_agree_bytes_at_block AI); [exact HL| exact SIN| exact PVE| exact STR| apply BVLR; rewrite EBv; left; reflexivity| lia| rewrite length_app; cbn [length]; lia| alia]. }
      assert (SSZ2 : sh_zero m2 alloc_ceiling (2^47)) by (eapply sh_zero_stack_pv_agree; [exact PVE| alia| exact SSZ1]).
      assert (PVA2 : pv_agree sp0 LR LF (bv_unsigned sp) PB m m2).
      { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_weaken; [exact PVE| lia| intros b Hb; exact Hb]. }
      assert (GM2' : gmono g g2) by (eapply gmono_trans; [exact GM1| exact GM2]).
      clear PVE STR ERR MI1 ST1 HL PVA ARR PBS1.
      eapply lscps_step_evt. cbv beta delta [mkR].
      destruct OUT as [(-> & HPn & PBSn & HBn & HNn) | [(-> & HPn & PBSn & PDn & -> & ->) | (buf' & len' & bs' & -> & HPn & PBSn & PDn & ROOM & L31 & LL & HBn & HNn)]].
      - (* [comment removed for export] *)
        unfold wz. zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
        apply evt_done. cbv beta.
        eapply (pstr_ret0 AI TI); try eassumption; [reflexivity| intros k Hk; reflexivity| left; split; [reflexivity| exact HPn]| |].
        + unfold pb_allow. pose proof (pb_pot_mono len INT_MAX ltac:(rewrite INT_MAX_eq; lia) ltac:(lia)). lia.
        + pose proof (pb_npallow_ge2 len ltac:(rewrite INT_MAX_eq; lia)). lia.
      - (* [comment removed for export] *)
        unfold wz. zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
        apply evt_done. cbv beta.
        eapply (pstr_ret0 AI TI); try eassumption; [reflexivity| intros k Hk; reflexivity| right; split; [lia| exact HPn]| |].
        + pose proof (pb_allow_ge_fail len ltac:(rewrite INT_MAX_eq; lia)). rewrite PB_FAIL_eq in *. lia.
        + pose proof (pb_npallow_ge2 len ltac:(rewrite INT_MAX_eq; lia)). lia.
      - (* [comment removed for export] *)
        (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HPn)) 4%nat; intros Y1 _ _ Y4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Y1. bandM. sepM. try rewrite alloc_ceiling_eq in Y4.
        unfold wz. zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
        apply evt_done. cbv beta. destruct PDn as [ARRn LENn].
        eapply (pstr_room m2 mo2 g2 LB2 TRS2 B2 np2 buf' len' n bs' errv2 str tail fc HL2 TV2 GM2' HPn LENn ltac:(lia) L31 LL HBn HNn PVA2 SSZ2 SNZ EBv NONUL LENS FRM);
          [exact FR| unfold AERRNO; exact ERR2| exact PBSn| exact ARRn| exact ST2| exact MI2| exact STR2].
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_isnull : forall (mo : Model) (fc : bv 32) m1 j0 (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      NINV m1 mo g LB TRS BB np -> FRAME m1 (CB 8 j0) -> PBS m1 buf len -> u8arr asegs m1 buf bs -> frm0 fc ->
      LSCPS asegs POST
        (MS (mkR ra (Z_to_bv 64 SPF) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 PB) (Z_to_bv 64 0xaa278) a3 a4 a5 a6 a7 s2 SHB s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86f88) fc None m1 (seg_rom asegs)) mo g.
    Proof.
      intros until t6. intros NI FR PBS1 ARR FRM.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold APSTR_STACK, AFORMAT_STACK in LO'.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
      apply evt_done. cbv beta.
      eapply (pstr_null AI TI MEMSET MEMCPY); eassumption.
    Qed.
  End Call.

  Theorem pstr_spec : pstr_stmt AI TI.
  Proof.
    unfold pstr_stmt. intros until errv.
    intros HL HP PS PD PN SV BVLR PL PBW SP16 P80 SP0 TOP BOT SPAL ST CEIL LO ERR MI TP FRM SSZ TV NPR RA1 RA2 HB A0 A1.
    unfold APSTR_ENTRY, wz in A0, A1. subst a0 a1. unfold wz, APSTR_ENTRY.
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as R.
    destruct PD as [ARR LEN].
    pose proof PS as PS'. unfold pb_struct, wz in PS'.
    eapply lscps_step_evt.
    eapply evt_cut; [eapply (prologue ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB LR Bv LF TRS np BB PB buf len off dep s fw bs lo errv); eassumption|].
    cbv beta. intros ms1 nelH_; (nelim nelH_ 8%nat; intros m1 j0 -> NI FR PBS1 ARR1 SV1).
    apply evt_done. cbv beta.
    destruct (Z.eq_dec s 0) as [->|SNZ].
    - eapply pstr_isnull; eassumption.
    - (nelim (cj_str_nonzero_inv _ _ _ SV1 SNZ) 7%nat; intros n str tail EBv STR NONUL LENS).
      eapply pstr_nonnull; eassumption.
  Qed.
End S.



End CeilWrap.
(* [comment removed for export] *)
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.
Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; unfold APSTR_STACK, AFORMAT_STACK, AENSURE_STACK, AMALLOC_STACK, AINTRIN_STACK in *; lia | sclr_tac2 ].
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
Ltac dlia := cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr asegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.
End CJ_pstr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_iface CJ_traces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface.
Import CJ_pstr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_sprintf_b.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_sprintf_b ICPT_mem ICPT_mem2.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Theorem pstr_ok : forall AI TI, pstr_stmt AI TI.
Proof. intros AI TI. exact (pstr_spec AI TI ICPT_sprintf_b.asprintf_u04x_ok_b ICPT_mem.asan_memset_ok ICPT_mem2.asan_memcpy_ok). Qed.


End CeilWrap.
