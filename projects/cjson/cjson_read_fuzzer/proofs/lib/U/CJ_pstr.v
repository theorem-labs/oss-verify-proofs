(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree CJ_print_iface CJ_utraps CJ_ensure CJ_pstr_A CJ_pstr_B F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_pad F_printf_iface F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_model.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.




(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
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

Ltac slv := rewrite ?alloc_ceiling_eq in *; unfold RMALLOC_STACK, ENSURE_STACK, PSTR_STACK in *; lia.
(* [comment removed for export] *)
Ltac dlia := cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Ltac killK K := first [exfalso; apply K; reflexivity | exfalso; revert K; lia_cj_nf].
Notation M1 := 18446744073709551615.

(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr usegs ?m B ?buf |- _ =>
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

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma CJST_pv_agree : forall LR SP PB m m',
  CJST m -> pv_agree LR SP PB m m' -> PIMG_HI <= PB -> CJST m'.
Proof.
  intros LR SP PB m m' (HK & (e1 & e2 & GE) & LC) PV HPB.
  split; [|split; [exists e1, e2|]].
  all: eapply rw_cells_magree; [exact PV| eassumption|].
  all: cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; split;
       [right; left; unfold palloc_static; unfold PHOOKS, PGERROR, PLCONV, PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP in *; lia
       | unfold PHOOKS, PGERROR, PLCONV, PIMG_HI in *; lia].
Qed.

Section S.
  Variable HI : cj_heap_iface.
  Hypothesis SPRU : F_printf_iface.sprintf_u04x_stmt.

  Lemma lheap_ssp : forall SPB LB m mo, LHEAP HI SPB LB m mo -> exists canary, OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.ssp_cells m canary.
  Proof.
    intros SPB LB m mo HL. (nelim (lh_ssp HI _ _ _ _ HL) 3%nat; intros G canary C). exists canary.
    unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.ssp_cells, OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.got_ssp, OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.ssp_guard. unfold PGOT_SSP, PSSP, wz in G, C. split; [exact G| exact C].
  Qed.

  Section Call.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
              (m : word -> option byte)
              (SPB : Z) (LB LR Bv : list cblock) (PB buf len off dep s : Z) (fw : word) (bs : list byte) (lo : Z) (errv : word).
    Hypothesis HP : Permutation ((buf, len) :: LR) LB.
    Hypothesis PN : pb_nums len off dep.
    Hypothesis SV : cj_str m s Bv.
    Hypothesis BVLR : forall b, In b Bv -> In b LR.
    Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - PSTR_STACK.
    Hypothesis TP : tp = wz PTP.
    Hypothesis LEN : Z.of_nat (length bs) = len.
    Hypothesis R1 : 0 < buf.
    Hypothesis R4 : buf + len <= alloc_ceiling.
    Hypothesis SPhi : bv_unsigned sp <= 2^64.

    Notation POST := (pstr_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR PB dep fw lo m).
    Notation SPF := (bv_unsigned sp + -128).
    Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    (* [comment removed for export] *)
    Notation FRAME mm fj := (rw_cells usegs mm (bv_unsigned sp + -128) (CB 24 fj :: SAVED)).
    Notation PBS mm b l := (rw_cells usegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 off); C8 (Z_to_bv 64 dep);
                                               C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 91236); C8 (Z_to_bv 64 90916); C8 (Z_to_bv 64 97488)]).

    Lemma SPFeq : bv_unsigned (Z_to_bv 64 SPF) = SPF.
    Proof. apply unsigned_lit. pose proof CEIL as C. try rewrite alloc_ceiling_eq in C. unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. lia. Qed.

    (* [comment removed for export] *)
    Lemma frame24 : forall mm (loc : list cell), rw_cells usegs mm SPF (loc ++ SAVED) -> cells_size loc = 24%nat ->
      FRAME mm (cells_bytes loc).
    Proof.
      intros mm loc H SZ. change (loc ++ SAVED) with ([] ++ loc ++ SAVED) in H. apply rw_cells_merge in H. rewrite SZ in H. exact H.
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_epi : forall (mm : word -> option byte) (mo' : Model) (errv' : word) (fj : list byte) (Fc : bvmap 5 word) (fcc : bv 32)
                       (x1 x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      FRAME mm fj -> stk usegs mm lo SPF -> mem_inv usegs mm -> rw_cells usegs mm PERRNO [C4 errv'] -> CJST mm ->
      frm0 fcc -> (forall k : bv 5, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k) ->
      pv_agree LR (bv_unsigned sp) PB m mm ->
      print_outcome HI SPB LR PB dep fw r mm mo' ->
      SCPS usegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x15904) fcc None mm (seg_rom usegs)) mo'.
    Proof.
      intros until x31. intros FR ST MI ERR CJ FRM FA PVA OUT.
      pose proof CEIL as CEIL'. unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. try rewrite alloc_ceiling_eq in CEIL.
      (nelim OUT 6%nat; intros LB' buf' len' off' HL' OUT).
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL'|].
      do 15 step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. apply scps_done. unfold pstr_post.
      nexists 19%nat. split; [reflexivity|].
      split; [exact MI|]. split; [exact FRM|]. split; [exact FA|]. split; [exact ST|]. split; [exact ERR|]. split; [exact CJ|]. split; [exact PVA|].
      exists LB', buf', len', off'. split; [exact HL'| exact OUT].
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_ok : forall (mm : word -> option byte) (mo' : Model) (errv' : word) (fj : list byte) (Fc : bvmap 5 word) (fcc : bv 32)
                       (LB' : list cblock) (buf' len' : Z) (bs' : list byte)
                       (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      FRAME mm fj -> stk usegs mm lo SPF -> mem_inv usegs mm -> rw_cells usegs mm PERRNO [C4 errv'] -> CJST mm ->
      frm0 fcc -> (forall k : bv 5, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k) ->
      pv_agree LR (bv_unsigned sp) PB m mm ->
      LHEAP HI SPB LB' mm mo' -> Permutation ((buf', len') :: LR) LB' ->
      PBS mm buf' len' -> pb_data mm buf' len' bs' -> len' < 2^31 -> pb_nul bs' len' off ->
      SCPS usegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x15900) fcc None mm (seg_rom usegs)) mo'.
    Proof.
      intros until x31. intros FR ST MI ERR CJ FRM FA PVA HL' HP' PBS' PD' L31 NUL.
      pose proof CEIL as CEIL'. unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. try rewrite alloc_ceiling_eq in CEIL.
      (nelimp PN 3%nat; intros PN1 PN2 PN3).
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL'|].
      step. apply evt_done. cbv beta.
      eapply pstr_epi; [exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA|].
      exists LB', buf', len', off. split; [exact HL'|]. right. split; [reflexivity|].
      exists bs'. split; [exact HP'|]. split; [exact PBS'|]. split; [exact PD'|]. split; [| exact NUL].
      (nelim NUL 4%nat; intros K K0 K1 _). split; [lia| split; [exact L31| exact PN3]].
    Qed.

    (* [comment removed for export] *)
    Section Room.
      Variables (m2 : word -> option byte) (mo2 : Model) (LB2 : list cblock) (B len' n : Z) (bs2 : list byte) (j16 : list byte)
                (errv2 : word) (str tail : list byte) (fc0 : bv 32).
      Notation L := (Z.of_nat (length str)).
      Notation E := (esc_count str).
      Notation OUT := (B + off).
      Notation full := (str ++ wb 0 :: tail).
      Hypothesis HL2 : LHEAP HI SPB LB2 m2 mo2.
      Hypothesis HP2 : Permutation ((B, len') :: LR) LB2.
      Hypothesis LEN2 : Z.of_nat (length bs2) = len'.
      Hypothesis ROOM : L + E + 3 + off + 1 <= len'.
      Hypothesis L31 : len' < 2^31.
      Hypothesis CJ2 : CJST m2.
      Hypothesis PVA2 : pv_agree LR (bv_unsigned sp) PB m m2.
      Hypothesis SNZ : s <> 0.
      Hypothesis EBv : Bv = [(s, n)].
      Hypothesis NONUL : ~ In (wb 0) str.
      Hypothesis LENS : L + 1 + Z.of_nat (length tail) = n.
      Hypothesis FRM0 : frm0 fc0.

      Notation WE2 := (WE str B off lo sp).
      (* [comment removed for export] *)
      Definition WEF : list (Z * Z) := [(lo, SPF); (OUT, OUT + (L + E + 3)); (SPF + 8, SPF + 16)].
      (* [comment removed for export] *)
      Notation FRAME16 mm fj := (rw_cells usegs mm (bv_unsigned sp + -128) (CB 16 fj :: C8 (Z_to_bv 64 (E + (L + 1))) :: SAVED)).

      Lemma blkB : 0 < B /\ B + len' <= alloc_ceiling /\ (B + len' <= 0x10000 \/ 0x56000 <= B).
      Proof.
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HP2)) 5%nat; intros X1 X2 X3 X4 X5).
        unfold PIMG_LO, PIMG_HI in X5. lia.
      Qed.

      Lemma blkS : In (s, n) LR /\ (s + n <= B \/ B + len' <= s) /\ s + n <= alloc_ceiling /\ 0 < s.
      Proof.
        assert (IN : In (s, n) LR). { apply BVLR. rewrite EBv. left. reflexivity. }
        split; [exact IN|].
        destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL2 HP2 s n IN) as [_ D].
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 ltac:(eapply Permutation_in; [exact HP2| right; exact IN])) 5%nat; intros Y1 _ _ Y4 _).
        lia.
      Qed.

      (* [comment removed for export] *)
      Lemma room_end : forall mm, rw_cells usegs m2 PERRNO [C4 errv2] -> PBS m2 B len' -> munch WEF m2 mm -> wmono usegs m2 mm ->
        rw_cells usegs mm PERRNO [C4 errv2] /\ CJST mm /\ PBS mm B len'
        /\ pv_agree LR (bv_unsigned sp) PB m mm /\ LHEAP HI SPB LB2 mm mo2.
      Proof.
        intros mm ERR2 PBS2 MU WM. (nelimp blkB 3%nat; intros B1 B2 B3). pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL', B2.
        unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4). (nelimp PN 3%nat; intros PN1 PN2 PN3).
        pose proof (esc_count_range str) as ER. unfold WEF in MU.
        split; [|split; [|split; [|split]]].
        - eapply rw_cells_transport; [exact ERR2| exact MU| exact WM|]. unfold PERRNO. dlia.
        - eapply CJST_frame; [exact CJ2| exact MU| exact WM|]. unfold PDATA_LO, PIMG_HI. intros lo' hi' [E1|[E1|[E1|[]]]]; inversion E1; subst; lia.
        - eapply rw_cells_transport; [exact PBS2| exact MU| exact WM|]. dlia.
        - eapply pv_agree_trans; [exact PVA2|]. eapply magree_of_munch; [exact MU| exact WM|].
          intros a Ha [Hc Hn]. cbn [outside]. split; [|split; [|split; [|exact I]]].
          + destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
            (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 ltac:(eapply Permutation_in; [exact HP2| right; exact Hin])) 5%nat; intros _ _ _ R _).
            try rewrite alloc_ceiling_eq in R. lia.
          + destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
            destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL2 HP2 A' n' Hin) as [_ D]. lia.
          + destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
            pose proof (lh_block_range HI _ _ _ _ _ _ HL2 ltac:(eapply Permutation_in; [exact HP2| right; exact Hin])) as (_ & _ & _ & R & _).
            try rewrite alloc_ceiling_eq in R. lia.
        - eapply (lh_frame HI); [exact HL2| exact MU| exact WM|].
          constructor; [right; left; cbn; lia|]. constructor; [| constructor; [right; left; cbn; lia| constructor]].
          do 4 right. exists B, len'. split; [eapply perm_in_head; exact HP2| cbn; lia].
      Qed.

      (* [comment removed for export] *)
      Lemma pstr_end : forall mm bsc fj Fc fcc x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x24 x25 x26 x27 x28 x29 x30 x31,
        rw_cells usegs m2 PERRNO [C4 errv2] -> PBS m2 B len' -> FRAME16 mm fj -> u8arr usegs mm B bsc -> Z.of_nat (length bsc) = len' -> munch WEF m2 mm -> wmono usegs m2 mm -> mem_inv usegs mm ->
        stk usegs mm lo SPF -> frm0 fcc -> (forall k : bv 5, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k) ->
        SCPS usegs POST
          (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (M1 - OUT)) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 E) (Z_to_bv 64 (L + 1)) (Z_to_bv 64 OUT) x23 x24 x25 x26 x27 x28 x29 x30 x31)
              Fc (Z_to_bv 64 0x158dc) fcc None mm (seg_rom usegs)) mo2.
      Proof.
        intros until x31. intros ERR2 PBS2 FR ARR LENc MU WM MI ST FRM FA.
        (nelimp blkB 3%nat; intros B1 B2 B3). pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL, B2.
        unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4). (nelimp PN 3%nat; intros PN1 PN2 PN3).
        pose proof (esc_count_range str) as ER. unfold WEF in MU.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. zstep. step. zstep.
        ustore_at B off (OUT + (E + (L + 1))) (L + E + 1) (wb 34) ltac:(reflexivity).
        step. if_cases Kg; zify_cond Kg; [killK Kg | idtac]. clear Kg.
        zstep. zstep.
        ustore_at B off (OUT + (E + (L + 1)) + 1) (L + E + 2) (wb 0) ltac:(reflexivity).
        apply evt_done. cbv beta.
        lazymatch goal with |- SCPS _ _ (MS _ _ _ _ _ ?mc _) _ =>
          (nelim (room_end mc ERR2 PBS2 ltac:(exact MU) ltac:(exact WM)) 5%nat; intros ERR' CJ' PBS' PVA' HL') end.
        eapply pstr_ok; [eapply (frame24 _ [CB 16 fj; C8 (Z_to_bv 64 (E + (L + 1)))]); [exact FR| reflexivity]
                        | exact ST| exact MI| exact ERR'| exact CJ'| exact FRM| exact FA| exact PVA'| exact HL'| exact HP2| exact PBS'| | exact L31|].
        - split; [exact ARR| rewrite !upd_length; exact LENc].
        - exists (L + E + 2). split; [lia|]. split; [lia|]. apply nth_error_upd_same. rewrite !upd_length. lia.
      Qed.

      (* [comment removed for export] *)
      Lemma frame_fmt : forall mm j8 (w : word) rest, rw_cells usegs mm SPF (CB 8 j8 :: C8 w :: rest) -> rw_cells usegs mm (SPF + 8) [C8 w].
      Proof using ACEIL bs bs2 str tail.
        intros mm j8 w rest H. change (CB 8 j8 :: C8 w :: rest) with ([CB 8 j8] ++ [C8 w] ++ rest) in H.
        apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.rw_cells_app in H. destruct H as [_ H]. apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.rw_cells_app in H. destruct H as [H _].
        cbn [cells_size csize Nat.add] in H. replace (SPF + Z.of_nat 8) with (SPF + 8) in H by lia. exact H.
      Qed.

      Lemma frame16_of : forall mm j8 (w : word), rw_cells usegs mm SPF (CB 8 j8 :: C8 w :: C8 (Z_to_bv 64 (E + (L + 1))) :: SAVED) ->
        FRAME16 mm (j8 ++ le8 w).
      Proof.
        intros mm j8 w H. change (CB 8 j8 :: C8 w :: ?r) with ([] ++ [CB 8 j8; C8 w] ++ r) in H. apply rw_cells_merge in H.
        pose proof H as [[W _] _]. cbn in W. destruct W as [W _].
        cbn [cells_size csize cells_bytes cbytes Nat.add app] in H. rewrite app_nil_r in H. exact H.
      Qed.

      (* [comment removed for export] *)
      Lemma pstr_room : forall x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
        FRAME16 m2 j16 -> rw_cells usegs m2 PERRNO [C4 errv2] -> PBS m2 B len' -> u8arr usegs m2 B bs2 ->
        stk usegs m2 lo SPF -> mem_inv usegs m2 -> bytes_at usegs m2 s full ->
        SCPS usegs POST
          (MS (mkR (Z_to_bv 64 0x15780) (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 s) x9 (Z_to_bv 64 OUT) x11 x12 x13 x14 x15 x16 x17
                   s2 s3 (Z_to_bv 64 E) (Z_to_bv 64 (L + 1)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x15784) fc0 None m2 (seg_rom usegs)) mo2.
      Proof using BVLR CEIL CJ2 EBv FRM0 HL2 HP HP2 L31 LEN LEN2 LENS LO NONUL PL PN PVA2 R4 ROOM SNZ SPRU SPhi SV.
        intros until x31. intros FR2 ERR2 PBS2 ARR2 ST2 MI2 STR2.
        (nelimp blkB 3%nat; intros B1 B2 B3). (nelimp blkS 4%nat; intros SIN SD SA SZ). pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL, B2, SA.
        unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4). (nelimp PN 3%nat; intros PN1 PN2 PN3).
        pose proof (esc_count_range str) as ER.
        pose proof (bytes_at_bound _ _ _ _ STR2) as SB. rewrite length_app in SB. cbn [length] in SB.
        destruct (lheap_ssp _ _ _ _ HL2) as [canary SSP].
        pose proof (munch_refl WEF m2) as MU. pose proof (wmono_refl usegs m2) as WM. unfold WEF in MU.
        pose proof ARR2 as ARR. pose proof STR2 as STR. pose proof PBS2 as PBSc. pose proof FR2 as FR. pose proof ST2 as ST. pose proof MI2 as MI.
        pose proof ERR2 as ERR. unfold PERRNO in ERR.
        (* [comment removed for export] *)
        set (m2c := m2) in FR2, ERR2, PBS2.
        unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.ssp_cells, OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.got_ssp, OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.ssp_guard in SSP. destruct SSP as [SSP1 SSP2].
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. step.
        ustore_at B off (B + off) 0 (wb 34) ltac:(reflexivity).
        step. if_cases KE; zify_cond KE.
        - (* [comment removed for export] *)
          step. replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 M1) by (apply Z_to_bv_eqm; reflexivity).
          step. if_cases Kg; zify_cond Kg; [killK Kg | idtac]. clear Kg.
          step. zstep. zstep. step. step. replace (Z_to_bv 64 (E + (L + 1) + -1)) with (Z_to_bv 64 (E + L)) by (f_equal; lia).
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
            (nelim (u8arr_split3 mc B _ (Z.to_nat (off + 1)) (length str) ARR ltac:(rewrite upd_length; lia)) 3%nat; intros A1 A2 A3) end.
          rewrite (Z2Nat.id (off + 1)) in A2, A3 by lia. replace (B + (off + 1)) with (OUT + 1) in A2, A3 by lia.
          pose proof STR as SRC. apply bytes_at_app in SRC. destruct SRC as [SRC _].
          clear ARR.
          eapply evt_cut.
          { eapply memcpy_spec with (src := str); rewrite ?unsigned_lit by lia;
              [ exact SRC | lia | replace (Z.to_nat (E + L)) with (length str) by lia; exact A2 | lia | exact MI ]. }
          cbv beta. intros ms' PO.
          (nelim PO 21%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MUc WMc MI' DST SRC').
          rewrite (unsigned_lit (OUT + 1)), (unsigned_lit (E + L)) in MUc by lia.
          rewrite (unsigned_lit (OUT + 1)), (unsigned_lit (E + L)) in DST by lia.
          replace (ret_pc (Z_to_bv 64 0x158d4)) with (Z_to_bv 64 0x158d4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          apply (u8arr_transport usegs _ _ m' _ _ A1) in MUc as A1'; [| exact WMc| cbn [disjoint_from]; rewrite firstn_length_le by (rewrite upd_length; lia); split; [lia| exact I]].
          apply (u8arr_transport usegs _ _ m' _ _ A3) in MUc as A3'; [| exact WMc| cbn [disjoint_from]; rewrite length_skipn, upd_length; split; [lia| exact I]].
          apply (stk_transport_disjoint usegs _ _ m' _ _ ST) in MUc as ST'; [| exact WMc| dlia].
          apply (rw_cells_transport usegs _ _ m' _ _ FR) in MUc as FR'; [| exact WMc| dlia].
          replace (Z.to_nat (E + L)) with (length str) in DST by lia.
          replace (OUT + 1) with (B + (off + 1)) in DST, A3' by lia.
          destruct (u8arr_join3' m' B _ (off + 1) _ _ _ A1' ltac:(rewrite firstn_length_le by (rewrite upd_length; lia); lia) DST A3') as [ARR _].
          assert (MU2 : munch WEF m2 m').
          { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. unfold WEF, sub_fp. cbn. intros a [X [Y _]]. lia. }
          pose proof (wmono_trans _ _ _ _ WM WMc) as WM2.
          clear MU WM MI ST STR SRC A1 A2 A3 A1' A3' DST MUc WMc FR.
          lazymatch type of ARR with u8arr _ _ _ ?l =>
            assert (LENj : Z.of_nat (length l) = len')
              by (rewrite !length_app, firstn_length_le, length_skipn, upd_length by (rewrite ?upd_length; lia); lia) end.
          zstep. rewrite zb_lxor_ones by lia.
          step. if_cases Kg; zify_cond Kg; [killK Kg | idtac]. clear Kg.
          apply evt_done. cbv beta.
          subst m2c.
          eapply pstr_end; [exact ERR2| exact PBS2| exact FR'| exact ARR| exact LENj| exact MU2| exact WM2| exact MI'| exact ST'| exact FRM0| intros k Hk; reflexivity].
        - (* [comment removed for export] *)
          step. replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 M1) by (apply Z_to_bv_eqm; reflexivity).
          step. if_cases Kg; zify_cond Kg; [killK Kg | idtac]. clear Kg.
          step. step. step. step. step. zstep. step. fix_lit_store. zstep. step. step.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
          pose proof (frame_fmt m3 _ _ _ FR) as FMT3.
          pose proof (emit_loop s str tail NONUL m3 B off len' lo sp canary F gp tp SPRU STR FMT3 ltac:(lia) ltac:(try rewrite alloc_ceiling_eq; lia)
                        ltac:(try rewrite alloc_ceiling_eq; lia) ltac:(lia) ltac:(lia) ltac:(try rewrite alloc_ceiling_eq; lia) ltac:(lia)
                        (Z.to_nat L) 0 ltac:(lia) ltac:(lia)) as HK.
          unfold HEADK in HK. rewrite (pos_0 str), !Z.add_0_r in HK.
          eapply evt_cut.
          { eapply HK; [| exact FRM0| intros k Hk; reflexivity].
            split; [exact ARR|]. split; [rewrite upd_length; exact LEN2|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
            split; [exact MI|]. split; [exact ST|]. split; [exact SSP1| exact SSP2]. }
          cbv beta. intros ms' PO.
          (nelim PO 25%nat; intros mm bsc' Fc fcc x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x19' x28' x29' x30' x31' -> INV FRM' FA')
.
          clear ARR ERR MI ST PBSc STR SSP1 SSP2 HK FMT3.
          (nelim INV 7%nat; intros ARR LENc MU' WM' MI ST SSP). change (bv_unsigned sp - 128) with SPF in *.
          apply (rw_cells_transport usegs _ _ mm _ _ FR) in MU' as FRm; [| exact WM'| unfold WE; dlia].
          assert (MU2 : munch WEF m2 mm).
          { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold WE, WEF, sub_fp. cbn. intros a [X [Y _]]. lia. }
          pose proof (wmono_trans _ _ _ _ WM WM') as WM2. clear MU WM MU' FR.
          zstep. rewrite zb_lxor_ones by lia.
          step. step. if_cases Kg; zify_cond Kg; [idtac | killK Kg]; clear Kg.
          apply evt_done. cbv beta.
          subst m2c.
          eapply pstr_end; [exact ERR2| exact PBS2| eapply frame16_of; exact FRm| exact ARR| exact LENc| exact MU2| exact WM2| exact MI| exact ST| exact FRM'| exact FA'].
      Qed.
    End Room.

    (* [comment removed for export] *)
    Lemma pstr_nonnull : forall (mo : Model) (fc : bv 32) (n : Z) (str tail : list byte)
        (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      LHEAP HI SPB LB m mo -> PBS m buf len -> u8arr usegs m buf bs ->
      CJST m -> stk usegs m lo (bv_unsigned sp) -> rw_cells usegs m PERRNO [C4 errv] -> mem_inv usegs m -> frm0 fc ->
      s <> 0 -> Bv = [(s, n)] -> bytes_at usegs m s (str ++ wb 0 :: tail) -> ~ In (wb 0) str ->
      Z.of_nat (length str) + 1 + Z.of_nat (length tail) = n ->
      SCPS usegs POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 PB) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x156ac) fc None m (seg_rom usegs)) mo.
    Proof.
      intros until t6. intros HL PBS0 ARR CJ ST ERR MI FRM SNZ EBv STR NONUL LENS.
      pose proof CEIL as CEIL'. unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. try rewrite alloc_ceiling_eq in CEIL.
      pose proof R4 as R4'. try rewrite alloc_ceiling_eq in R4'.
      (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PERRNO in ERR.
      pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
      (* [comment removed for export] *)
      assert (SIN : In (s, n) LB). { eapply Permutation_in; [exact HP|]. right. apply BVLR. rewrite EBv. left. reflexivity. }
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL SIN) 5%nat; intros Q1 Q2 Q3 Q4 Q5). try rewrite alloc_ceiling_eq in Q4. unfold PIMG_LO, PIMG_HI in Q5.
      pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      carve_frame 128%nat ST.
      do 15 step.
      step. if_cases K0; zify_cond K0; [killK K0 | idtac]. clear K0.
      do 9 step.
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ ?mc _) => rename mc into m1 end.
      assert (HL1 : LHEAP HI SPB LB m1 mo).
      { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
      assert (PVA1 : pv_agree LR (bv_unsigned sp) PB m m1).
      { eapply (pv_agree_stack HI); [exact HL| | exact MU| exact WM| try rewrite alloc_ceiling_eq; lia| lia].
        intros b Hb. eapply Permutation_in; [exact HP| right; exact Hb]. }
      assert (CJ1 : CJST m1).
      { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E1|[]]. inversion E1; subst. unfold PDATA_LO, PIMG_HI. lia. }
      clear MU WM.
      (* [comment removed for export] *)
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 M1) by (apply Z_to_bv_eqm; reflexivity).
      rewrite <- (Z_to_bv_bv_unsigned a5), <- (Z_to_bv_bv_unsigned a6).
      eapply evt_cut; [eapply (count_loop s str tail NONUL m1); first [exact STR| exact MI| try rewrite alloc_ceiling_eq; lia]|].
      cbv beta. intros ms' nelH_; (nelim nelH_ 4%nat; intros c a5v x17 ->).
      (* [comment removed for export] *)
      pose proof (munch_refl [(SPF + 16, SPF + 24)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
      zstep. step. fix_lit_store. zstep. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ ?mc _) => rename mc into m1' end.
      assert (HL1' : LHEAP HI SPB LB m1' mo).
      { eapply (lh_frame HI); [exact HL1| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
      assert (PVA1' : pv_agree LR (bv_unsigned sp) PB m m1').
      { eapply pv_agree_trans; [exact PVA1|]. eapply (pv_agree_stack HI); [exact HL1| | exact MU| exact WM| rewrite ?alloc_ceiling_eq; lia| lia].
        intros b Hb. eapply Permutation_in; [exact HP| right; exact Hb]. }
      assert (CJ1' : CJST m1').
      { eapply CJST_frame; [exact CJ1| exact MU| exact WM|]. intros lo' hi' [E1|[]]. inversion E1; subst. unfold PDATA_LO, PIMG_HI. lia. }
      clear MU WM HL1 PVA1 CJ1. rename HL1' into HL1. rename PVA1' into PVA1. rename CJ1' into CJ1. clear m1. rename m1' into m1.
      apply evt_done. cbv beta.
      pose proof (esc_count_range str) as ER.
      eapply scps_bind.
      { eapply (ensure_spec HI) with (lo := lo) (LR := LR) (bs := bs) (needed := esc_count str + (Z.of_nat (length str) + 1) + 2); rewrite ?SPFeq;
          first [ exact HL1 | exact HP | exact PBS0 | split; [exact ARR| exact LEN] | exact PN | exact ST | exact ERR | exact MI | exact TP | reflexivity
                | split; [lia| split; [lia| split; [lia| exact PL4]]] | unfold ENSURE_STACK, RMALLOC_STACK; lia | lia | f_equal; lia ]. }
      cbv beta. intros ms2 mo2 PO.
      (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 LB2 -> MI2 ST2 ERR2 PVE HL2 OUT)
.
      rewrite SPFeq in ST2, PVE. unfold PERRNO in ERR2.
      replace (ret_pc (Z_to_bv 64 0x15780)) with (Z_to_bv 64 0x15780) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (* [comment removed for export] *)
      assert (AGR : forall a, 0 <= a < 2^64 -> (SPF <= a /\ (a < PB \/ PB + 64 <= a)) \/ (in_cblock LR a \/ (PDATA_LO <= a < PIMG_HI /\ ~ palloc_static a)) ->
                      m2 (wa a) = m1 (wa a) /\ (wview usegs m1 (wa a) <> None -> wview usegs m2 (wa a) <> None)).
      { intros a Ha Hc. apply PVE; [exact Ha|]. unfold cj_client_addr.
        destruct Hc as [[H1 H2]|[H1|H1]]; [split; [left; lia| lia]| |].
        - split; [right; right; exact H1|]. (nelim H1 4%nat; intros A' n' Hin Hr).
          (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) 5%nat; intros _ _ _ X4 _).
          try rewrite alloc_ceiling_eq in X4. lia.
        - split; [right; left; exact H1|]. unfold PDATA_LO, PIMG_HI in H1. lia. }
      assert (FR2 : rw_cells usegs m2 SPF _) by (eapply (rw_cells_magree _ m1 m2); [exact AGR| exact FR| cbn; intros a Ha; left; lia]).
      assert (STR2 : bytes_at usegs m2 s (str ++ wb 0 :: tail)).
      { eapply bytes_at_magree; [exact AGR| exact STR|]. intros a Ha. right; left. exists s, n. split; [apply BVLR; rewrite EBv; left; reflexivity|].
        rewrite length_app in Ha. cbn [length] in Ha. lia. }
      assert (CJ2 : CJST m2).
      { eapply (CJST_pv_agree LR (bv_unsigned sp + -128) PB); [exact CJ1| exact PVE| unfold PIMG_HI; lia]. }
      assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
      { eapply pv_agree_trans; [exact PVA1|]. eapply pv_agree_weaken; [exact PVE| lia| intros b Hb; exact Hb]. }
      clear AGR PVE STR FR ERR MI ST HL1 PVA1 CJ1 ARR PBS0.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      destruct OUT as [(-> & HPn & PBSn) | [(-> & HPn & PBSn & PDn) | (buf' & len' & bs' & -> & HPn & PBSn & PDn & ROOM & L31)]].
      - (* [comment removed for export] *)
        unfold wz. step. if_cases K; zify_cond K; [idtac | killK K]. clear K.
        apply evt_done. cbv beta.
        eapply pstr_epi; [eapply (frame24 _ [CB 16 _; C8 _]); [exact FR2| reflexivity]| exact ST2| exact MI2| exact ERR2| exact CJ2| exact FRM| intros k Hk; reflexivity| exact PVA2|].
        exists LB2, 0, 0, off. split; [exact HL2|]. left. split; [reflexivity|]. exists dep. split; [exact PBSn| left; split; [reflexivity| exact HPn]].
      - (* [comment removed for export] *)
        unfold wz. step. if_cases K; zify_cond K; [idtac | killK K]. clear K.
        apply evt_done. cbv beta.
        eapply pstr_epi; [eapply (frame24 _ [CB 16 _; C8 _]); [exact FR2| reflexivity]| exact ST2| exact MI2| exact ERR2| exact CJ2| exact FRM| intros k Hk; reflexivity| exact PVA2|].
        exists LB2, buf, len, off. split; [exact HL2|]. left. split; [reflexivity|]. exists dep. split; [exact PBSn| right; split; [lia| exact HPn]].
      - (* [comment removed for export] *)
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HPn)) 5%nat; intros Y1 _ _ Y4 _). try rewrite alloc_ceiling_eq in Y4.
        unfold wz. step. if_cases K; zify_cond K; [killK K | idtac]. clear K.
        apply evt_done. cbv beta. destruct PDn as [ARRn LENn].
        eapply (pstr_room m2 mo2 LB2 buf' len' n bs' _ errv2 str tail fc HL2 HPn LENn ltac:(lia) L31 CJ2 PVA2 SNZ EBv NONUL LENS FRM);
          [exact FR2| unfold PERRNO; exact ERR2| exact PBSn| exact ARRn| exact ST2| exact MI2| exact STR2].
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_quotes : forall (mm : word -> option byte) (mo' : Model) (LB' : list cblock) (B len' : Z) (bs' fj : list byte) (errv' : word) (fcc : bv 32)
        x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
      LHEAP HI SPB LB' mm mo' -> Permutation ((B, len') :: LR) LB' -> PBS mm B len' -> u8arr usegs mm B bs' -> Z.of_nat (length bs') = len' ->
      3 + off + 1 <= len' -> len' < 2^31 ->
      FRAME mm fj -> stk usegs mm lo SPF -> mem_inv usegs mm -> rw_cells usegs mm PERRNO [C4 errv'] -> CJST mm -> frm0 fcc ->
      pv_agree LR (bv_unsigned sp) PB m mm ->
      SCPS usegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (B + off)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x15894) fcc None mm (seg_rom usegs)) mo'.
    Proof.
      intros until x31. intros HL' HP' PBS' ARR LEN' ROOM L31 FR ST MI ERR CJ FRM PVA.
      pose proof CEIL as CEIL'. unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. try rewrite alloc_ceiling_eq in CEIL.
      (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4). (nelimp PN 3%nat; intros PN1 PN2 PN3).
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL' (perm_in_head _ _ _ HP')) 5%nat; intros Y1 Y2 Y3 Y4 Y5). try rewrite alloc_ceiling_eq in Y4. unfold PIMG_LO, PIMG_HI in Y5.
      unfold PERRNO in ERR.
      pose proof (munch_refl [(B + off, B + off + 3)] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL'|].
      step.
      ustore_at B off (B + off) 0 (wb 34) ltac:(reflexivity).
      ustore_at B off (B + off + 1) 1 (wb 34) ltac:(reflexivity).
      ustore_at B off (B + off + 2) 2 (wb 0) ltac:(reflexivity).
      step.
      apply evt_done. cbv beta.
      lazymatch goal with |- SCPS _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m5 end.
      eapply pstr_ok; [exact FR| exact ST| exact MI| exact ERR| | exact FRM| intros k Hk; reflexivity| | | exact HP'| exact PBS'| | exact L31|].
      - eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E1|[]]. inversion E1; subst. unfold PDATA_LO, PIMG_HI. lia.
      - eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
        intros a Ha [Hc Hn]. cbn [outside]. split; [|exact I].
        destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
        destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL' HP' A' n' Hin) as [_ D]. lia.
      - eapply (lh_frame HI); [exact HL'| exact MU| exact WM|]. constructor; [|constructor].
        do 4 right. exists B, len'. split; [eapply perm_in_head; exact HP'| cbn; lia].
      - split; [exact ARR| rewrite !upd_length; exact LEN'].
      - exists 2. split; [lia|]. split; [lia|]. apply nth_error_upd_same. rewrite !upd_length. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_null : forall (m1 : word -> option byte) (mo : Model) (fc : bv 32) (fj : list byte)
        (x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      LHEAP HI SPB LB m1 mo -> PBS m1 buf len -> u8arr usegs m1 buf bs ->
      FRAME m1 fj -> stk usegs m1 lo SPF -> rw_cells usegs m1 PERRNO [C4 errv] -> mem_inv usegs m1 -> CJST m1 -> frm0 fc ->
      pv_agree LR (bv_unsigned sp) PB m m1 ->
      SCPS usegs POST
        (MS (mkR ra (Z_to_bv 64 SPF) gp tp x5 x6 x7 s0 s1 x10 x11 (Z_to_bv 64 PB) x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x15884) fc None m1 (seg_rom usegs)) mo.
    Proof.
      intros until x31. intros HL PBS1 ARR FR ST ERR MI CJ FRM PVA.
      pose proof CEIL as CEIL'. unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. try rewrite alloc_ceiling_eq in CEIL.
      pose proof R4 as R4'. try rewrite alloc_ceiling_eq in R4'.
      (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PERRNO in ERR. pose proof SPFeq as E1.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      step. step. step. apply evt_done. cbv beta.
      eapply scps_bind.
      { eapply (ensure_spec HI) with (lo := lo) (LR := LR) (bs := bs) (needed := 3); rewrite ?E1;
          first [ exact HL | exact HP | exact PBS1 | split; [exact ARR| exact LEN] | split; [exact PN1| split; [exact PN2| exact PN3]] | exact ST | exact ERR | exact MI | exact TP | reflexivity
                | split; [lia| split; [lia| split; [lia| exact PL4]]] | unfold ENSURE_STACK, RMALLOC_STACK; lia | lia ]. }
      cbv beta. intros ms2 mo2 PO.
      destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & LB2
                      & -> & MI2 & ST2 & ERR2 & PVE & HL2 & OUT).
      rewrite E1 in ST2, PVE. unfold PERRNO in ERR2.
      replace (ret_pc (Z_to_bv 64 0x15890)) with (Z_to_bv 64 0x15890) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (AGR : forall a, 0 <= a < 2^64 -> (SPF <= a /\ (a < PB \/ PB + 64 <= a)) \/ (in_cblock LR a \/ (PDATA_LO <= a < PIMG_HI /\ ~ palloc_static a)) ->
                      m2 (wa a) = m1 (wa a) /\ (wview usegs m1 (wa a) <> None -> wview usegs m2 (wa a) <> None)).
      { intros a Ha Hc. apply PVE; [exact Ha|]. unfold cj_client_addr.
        destruct Hc as [[H1 H2]|[H1|H1]]; [split; [left; lia| lia]| |].
        - split; [right; right; exact H1|]. destruct H1 as (A' & n' & Hin & Hr).
          pose proof (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) as (_ & _ & _ & X4 & _).
          try rewrite alloc_ceiling_eq in X4. lia.
        - split; [right; left; exact H1|]. unfold PDATA_LO, PIMG_HI in H1. lia. }
      assert (FR2 : FRAME m2 fj) by (eapply (rw_cells_magree _ m1 m2); [exact AGR| exact FR| cbn; intros a Ha; left; lia]).
      assert (CJ2 : CJST m2).
      { eapply (CJST_pv_agree LR (bv_unsigned sp + -128) PB); [exact CJ| exact PVE| unfold PIMG_HI; lia]. }
      assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
      { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_weaken; [exact PVE| lia| intros b Hb; exact Hb]. }
      clear AGR PVE FR ERR MI ST PVA CJ ARR PBS1.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      destruct OUT as [(-> & HPn & PBSn) | [(-> & HPn & PBSn & PDn) | (buf' & len' & bs' & -> & HPn & PBSn & PDn & ROOM & L31)]].
      - unfold wz. step. if_cases K; zify_cond K; [idtac | killK K]. clear K.
        apply evt_done. cbv beta.
        eapply pstr_epi; [exact FR2| exact ST2| exact MI2| exact ERR2| exact CJ2| exact FRM| intros k Hk; reflexivity| exact PVA2|].
        exists LB2, 0, 0, off. split; [exact HL2|]. left. split; [reflexivity|]. exists dep. split; [exact PBSn| left; split; [reflexivity| exact HPn]].
      - unfold wz. step. if_cases K; zify_cond K; [idtac | killK K]. clear K.
        apply evt_done. cbv beta.
        eapply pstr_epi; [exact FR2| exact ST2| exact MI2| exact ERR2| exact CJ2| exact FRM| intros k Hk; reflexivity| exact PVA2|].
        exists LB2, buf, len, off. split; [exact HL2|]. left. split; [reflexivity|]. exists dep. split; [exact PBSn| right; split; [lia| exact HPn]].
      - pose proof (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HPn)) as (Y1 & _ & _ & Y4 & _). try rewrite alloc_ceiling_eq in Y4.
        unfold wz. step. if_cases K; zify_cond K; [killK K | idtac]. clear K.
        apply evt_done. cbv beta. destruct PDn as [ARRn LENn].
        eapply pstr_quotes; [exact HL2| exact HPn| exact PBSn| exact ARRn| exact LENn| lia| exact L31| exact FR2| exact ST2| exact MI2| exact ERR2| exact CJ2| exact FRM| exact PVA2].
    Qed.

    Lemma pstr_isnull : forall (mo : Model) (fc : bv 32) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      LHEAP HI SPB LB m mo -> PBS m buf len -> u8arr usegs m buf bs ->
      CJST m -> stk usegs m lo (bv_unsigned sp) -> rw_cells usegs m PERRNO [C4 errv] -> mem_inv usegs m -> frm0 fc ->
      SCPS usegs POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 PB) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x156ac) fc None m (seg_rom usegs)) mo.
    Proof.
      intros until t6. intros HL PBS0 ARR CJ ST ERR MI FRM.
      pose proof CEIL as CEIL'. unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. try rewrite alloc_ceiling_eq in CEIL.
      pose proof R4 as R4'. try rewrite alloc_ceiling_eq in R4'.
      (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PERRNO in ERR.
      pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      carve_frame 128%nat ST.
      do 15 step.
      step. if_cases K0; zify_cond K0; [idtac | killK K0]. clear K0.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      assert (HL1 : LHEAP HI SPB LB m1 mo).
      { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
      assert (PVA1 : pv_agree LR (bv_unsigned sp) PB m m1).
      { eapply (pv_agree_stack HI); [exact HL| | exact MU| exact WM| try rewrite alloc_ceiling_eq; lia| lia].
        intros b Hb. eapply Permutation_in; [exact HP| right; exact Hb]. }
      assert (CJ1 : CJST m1).
      { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E1|[]]. inversion E1; subst. unfold PDATA_LO, PIMG_HI. lia. }
      apply evt_done. cbv beta.
      eapply pstr_null; [exact HL1| exact PBS0| exact ARR| exact FR| exact ST| exact ERR| exact MI| exact CJ1| exact FRM| exact PVA1].
    Qed.
  End Call.

  Theorem pstr_spec : pstr_stmt HI.
  Proof.
    unfold pstr_stmt. intros until errv. intros HL HP PS PD PN SV BVLR CJ PL ST CEIL LO ERR MI TP FRM A0 A1.
    unfold PSTR_ENTRY, wz in A0, A1. subst a0 a1. unfold wz, PSTR_ENTRY.
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 _ _ R4 _).
    pose proof ST as STc; (nelim STc 3%nat; intros _ SPhi _).
    destruct PD as [ARR LEN].
    pose proof PS as PS'. unfold pb_struct, wz, PMALLOC, PFREE, PREALLOC in PS'.
    destruct (Z.eq_dec s 0) as [->|SNZ].
    - eapply pstr_isnull; eassumption.
    - (nelim (cj_str_nonzero_inv _ _ _ SV SNZ) 7%nat; intros n str tail EBv STR NONUL LENS).
      eapply (pstr_nonnull ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m SPB LB LR Bv PB buf len off dep s fw bs lo errv
                HP PN SV BVLR PL CEIL LO TP LEN R1 R4 SPhi mo fc n str tail); eassumption.
  Qed.
End S.

(* [comment removed for export] *)


End CeilWrap.
(* [comment removed for export] *)
Ltac slv := rewrite ?alloc_ceiling_eq in *; unfold RMALLOC_STACK, ENSURE_STACK, PSTR_STACK in *; lia.
Ltac dlia := cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Ltac killK K := first [exfalso; apply K; reflexivity | exfalso; revert K; lia_cj_nf].
Notation M1 := 18446744073709551615.
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr usegs ?m B ?buf |- _ =>
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
