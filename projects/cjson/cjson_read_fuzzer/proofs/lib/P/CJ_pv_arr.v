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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pstr_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pv_common.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pstr_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaSplit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pstr.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common.CJ_ensure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.
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

(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr psegs ?m B ?buf |- _ =>
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

  Lemma lheap_ssp : forall SPB LB m mo, LHEAP HI SPB LB m mo -> exists canary, F_pad.ssp_cells m canary.
  Proof.
    intros SPB LB m mo HL. (nelim (lh_ssp HI _ _ _ _ HL) 3%nat; intros G canary C). exists canary.
    unfold F_pad.ssp_cells, F_pad.got_ssp, F_pad.ssp_guard. unfold PGOT_SSP, PSSP, wz in G, C. split; [exact G| exact C].
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
    Notation SPF := (bv_unsigned sp + -112).
    Notation FRAME mm fj := (rw_cells psegs mm (bv_unsigned sp + -112)
       [CB 8 fj; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    Notation PBS mm b l := (rw_cells psegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 off); C8 (Z_to_bv 64 dep);
                                               C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 86816); C8 (Z_to_bv 64 86496); C8 (Z_to_bv 64 93068)]).

    Lemma SPFeq : bv_unsigned (Z_to_bv 64 SPF) = SPF.
    Proof. apply unsigned_lit. pose proof CEIL as C. try rewrite alloc_ceiling_eq in C. unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. lia. Qed.

    (* [comment removed for export] *)
    Lemma pstr_epi : forall (mm : word -> option byte) (mo' : Model) (errv' : word) (fj : list byte) (Fc : bvmap 5 word) (fcc : bv 32)
                       (x1 x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      FRAME mm fj -> stk psegs mm lo SPF -> mem_inv psegs mm -> rw_cells psegs mm PERRNO [C4 errv'] -> CJST mm ->
      frm0 fcc -> (forall k : bv 5, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k) ->
      pv_agree LR (bv_unsigned sp) PB m mm ->
      print_outcome HI SPB LR PB dep fw r mm mo' ->
      SCPS psegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 r x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x14704) fcc None mm (seg_rom psegs)) mo'.
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
      FRAME mm fj -> stk psegs mm lo SPF -> mem_inv psegs mm -> rw_cells psegs mm PERRNO [C4 errv'] -> CJST mm ->
      frm0 fcc -> (forall k : bv 5, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k) ->
      pv_agree LR (bv_unsigned sp) PB m mm ->
      LHEAP HI SPB LB' mm mo' -> Permutation ((buf', len') :: LR) LB' ->
      PBS mm buf' len' -> pb_data mm buf' len' bs' -> len' < 2^31 -> pb_nul bs' len' off ->
      SCPS psegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x14700) fcc None mm (seg_rom psegs)) mo'.
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
      Variables (m2 : word -> option byte) (mo2 : Model) (LB2 : list cblock) (B len' n : Z) (bs2 : list byte) (fj : list byte)
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

      Lemma blkB : 0 < B /\ B + len' <= alloc_ceiling /\ (B + len' <= 0x10000 \/ 0x55000 <= B).
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
      Lemma room_end : forall mm, FRAME m2 fj -> rw_cells psegs m2 PERRNO [C4 errv2] -> PBS m2 B len' ->
        munch WE2 m2 mm -> wmono psegs m2 mm ->
        FRAME mm fj /\ rw_cells psegs mm PERRNO [C4 errv2] /\ CJST mm /\ PBS mm B len'
        /\ pv_agree LR (bv_unsigned sp) PB m mm /\ LHEAP HI SPB LB2 mm mo2.
      Proof.
        intros mm FR2 ERR2 PBS2 MU WM. (nelimp blkB 3%nat; intros B1 B2 B3). pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL', B2.
        unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3).
        pose proof (esc_count_range str) as ER. unfold WE in MU.
        split; [|split; [|split; [|split; [|split]]]].
        - eapply rw_cells_transport; [exact FR2| exact MU| exact WM|]. dlia.
        - eapply rw_cells_transport; [exact ERR2| exact MU| exact WM|]. unfold PERRNO. dlia.
        - eapply CJST_frame; [exact CJ2| exact MU| exact WM|]. unfold PDATA_LO, PIMG_HI. intros lo' hi' [E1|[E1|[]]]; inversion E1; subst; lia.
        - eapply rw_cells_transport; [exact PBS2| exact MU| exact WM|]. dlia.
        - eapply pv_agree_trans; [exact PVA2|]. eapply magree_of_munch; [exact MU| exact WM|].
          intros a Ha [Hc Hn]. cbn [outside]. split; [|split; [|exact I]].
          + destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
            (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 ltac:(eapply Permutation_in; [exact HP2| right; exact Hin])) 5%nat; intros _ _ _ R _).
            try rewrite alloc_ceiling_eq in R. lia.
          + destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
            destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL2 HP2 A' n' Hin) as [_ D]. lia.
        - eapply (lh_frame HI); [exact HL2| exact MU| exact WM|].
          constructor; [right; left; cbn; lia|]. constructor; [|constructor].
          do 4 right. exists B, len'. split; [eapply perm_in_head; exact HP2| cbn; lia].
      Qed.

      (* [comment removed for export] *)
      Lemma pstr_cc : forall mm bsc Fc fcc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
        FRAME m2 fj -> rw_cells psegs m2 PERRNO [C4 errv2] -> PBS m2 B len' ->
        u8arr psegs mm B bsc -> Z.of_nat (length bsc) = len' -> munch WE2 m2 mm -> wmono psegs m2 mm -> mem_inv psegs mm ->
        stk psegs mm lo SPF -> frm0 fcc -> (forall k : bv 5, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k) ->
        SCPS psegs POST
          (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (OUT + (L + E))) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              Fc (Z_to_bv 64 0x146fc) fcc None mm (seg_rom psegs)) mo2.
      Proof.
        intros until x31. intros FR2 ERR2 PBS2 ARR LENc MU WM MI ST FRM FA.
        (nelimp blkB 3%nat; intros B1 B2 B3). pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL, B2.
        unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3).
        pose proof (esc_count_range str) as ER. unfold WE in MU.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        ustore_at B off (OUT + (L + E) + 2) (L + E + 2) (wb 0) ltac:(reflexivity).
        apply evt_done. cbv beta.
        lazymatch goal with |- SCPS _ _ (MS _ _ _ _ _ ?mc _) _ =>
          (nelim (room_end mc FR2 ERR2 PBS2 ltac:(exact MU) ltac:(exact WM)) 6%nat; intros FR' ERR' CJ' PBS' PVA' HL') end.
        eapply pstr_ok; [exact FR'| exact ST| exact MI| exact ERR'| exact CJ'| exact FRM| exact FA| exact PVA'| exact HL'| exact HP2| exact PBS'| | exact L31|].
        - split; [exact ARR| rewrite upd_length; exact LENc].
        - exists (L + E + 2). split; [lia|]. split; [lia|]. apply nth_error_upd_same. lia.
      Qed.

      (* [comment removed for export] *)
      Lemma pstr_room : forall x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
        FRAME m2 fj -> rw_cells psegs m2 PERRNO [C4 errv2] -> PBS m2 B len' -> u8arr psegs m2 B bs2 ->
        stk psegs m2 lo SPF -> mem_inv psegs m2 -> bytes_at psegs m2 s full ->
        SCPS psegs POST
          (MS (mkR (Z_to_bv 64 0x145ac) (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 (Z_to_bv 64 s) (Z_to_bv 64 OUT) x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 (E + L)) (Z_to_bv 64 L) (Z_to_bv 64 E) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x145b0) fc0 None m2 (seg_rom psegs)) mo2.
      Proof.
        intros until x31. intros FR2 ERR2 PBS2 ARR2 ST2 MI2 STR2.
        (nelimp blkB 3%nat; intros B1 B2 B3). (nelimp blkS 4%nat; intros SIN SD SA SZ). pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL, B2, SA.
        unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3).
        pose proof (esc_count_range str) as ER.
        pose proof (bytes_at_bound _ _ _ _ STR2) as SB. rewrite length_app in SB. cbn [length] in SB.
        destruct (lheap_ssp _ _ _ _ HL2) as [canary SSP].
        pose proof (munch_refl WE2 m2) as MU. pose proof (wmono_refl psegs m2) as WM. unfold WE in MU.
        pose proof ARR2 as ARR. pose proof STR2 as STR. pose proof PBS2 as PBSc. pose proof FR2 as FR. pose proof ST2 as ST. pose proof MI2 as MI.
        pose proof ERR2 as ERR. unfold PERRNO in ERR.
        (* [comment removed for export] *)
        set (m2c := m2) in FR2, ERR2, PBS2.
        unfold F_pad.ssp_cells, F_pad.got_ssp, F_pad.ssp_guard in SSP. destruct SSP as [SSP1 SSP2].
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. step.
        ustore_at B off (B + off) 0 (wb 34) ltac:(reflexivity).
        step. if_cases KE; zify_cond KE.
        - (* [comment removed for export] *)
          zstep. zstep. zstep. step.
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
          replace (ret_pc (Z_to_bv 64 0x146f0)) with (Z_to_bv 64 0x146f0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          apply (u8arr_transport psegs _ _ m' _ _ A1) in MUc as A1'; [| exact WMc| cbn [disjoint_from]; rewrite firstn_length_le by (rewrite upd_length; lia); split; [lia| exact I]].
          apply (u8arr_transport psegs _ _ m' _ _ A3) in MUc as A3'; [| exact WMc| cbn [disjoint_from]; rewrite length_skipn, upd_length; split; [lia| exact I]].
          apply (stk_transport_disjoint psegs _ _ m' _ _ ST) in MUc as ST'; [| exact WMc| dlia].
          replace (Z.to_nat (E + L)) with (length str) in DST by lia.
          replace (OUT + 1) with (B + (off + 1)) in DST, A3' by lia.
          destruct (u8arr_join3' m' B _ (off + 1) _ _ _ A1' ltac:(rewrite firstn_length_le by (rewrite upd_length; lia); lia) DST A3') as [ARR _].
          assert (MU2 : munch WE2 m2 m').
          { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. unfold WE, sub_fp. cbn. intros a [X [Y _]]. lia. }
          pose proof (wmono_trans _ _ _ _ WM WMc) as WM2.
          clear MU WM MI ST STR SRC A1 A2 A3 A1' A3' DST MUc WMc.
          unfold WE in MU2.
          lazymatch type of ARR with u8arr _ _ _ ?l =>
            assert (LENj : Z.of_nat (length l) = len')
              by (rewrite !length_app, firstn_length_le, length_skipn, upd_length by (rewrite ?upd_length; lia); lia) end.
          zstep. zstep.
          ustore_at B off (OUT + E + L + 1) (L + E + 1) (wb 34) ltac:(reflexivity).
          apply evt_done. cbv beta.
          replace (OUT + E + L) with (OUT + (L + E)) by lia.
          subst m2c.
          eapply pstr_cc; [exact FR2| exact ERR2| exact PBS2| exact ARR| | exact MU2| exact WM2| exact MI'| exact ST'| exact FRM0| intros k Hk; reflexivity].
          rewrite upd_length. exact LENj.
        - (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (ch_read s str tail mc 0 STR ltac:(lia)) as RD0 end.
          rewrite Z.add_0_r in RD0.
          destruct (ch_range str tail NONUL 0 ltac:(lia)) as [CR0 CZ0].
          zstep. zstep. rewrite (land255 (bv_unsigned (chb str tail 0))) by lia.
          zstep. if_cases KL; zify_cond KL; [exfalso; lia|].
          do 12 zstep.
          pose proof (emit_loop s str tail NONUL _ B off len' lo sp canary F gp tp SPRU STR ltac:(lia) ltac:(try rewrite alloc_ceiling_eq; lia)
                        ltac:(try rewrite alloc_ceiling_eq; lia) ltac:(lia) ltac:(lia) ltac:(try rewrite alloc_ceiling_eq; lia) ltac:(lia)
                        (Z.to_nat L) 0 ltac:(lia) ltac:(lia)) as HK.
          unfold HEADK in HK. rewrite (pos_0 str), !Z.add_0_r in HK.
          eapply evt_cut.
          { eapply HK; [| exact FRM0| intros k Hk; reflexivity].
            split; [exact ARR|]. split; [rewrite upd_length; exact LEN2|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
            split; [exact MI|]. split; [exact ST|]. split; [exact SSP1| exact SSP2]. }
          cbv beta. intros ms' PO.
          (nelim PO 26%nat; intros mm bsc' Fc fcc x1' x5' x6' x7' s0v x10' x11' x12' x13' x14' x15' x16' x17' s2v x28' x29' x30' x31' -> INV FRM' FA')
.
          clear ARR ERR MI ST FR PBSc STR SSP1 SSP2 RD0 HK.
          (nelim INV 7%nat; intros ARR LENc MU' WM' MI ST SSP).
          apply (munch_trans _ _ _ _ MU) in MU'. apply (wmono_trans _ _ _ _ WM) in WM'. clear MU WM. rename MU' into MU. rename WM' into WM.
          unfold WE in MU.
          zstep. zstep. zstep.
          ustore_at B off (OUT + E + L + 1) (L + E + 1) (wb 34) ltac:(reflexivity).
          step. apply evt_done. cbv beta.
          replace (OUT + E + L) with (OUT + (L + E)) by lia.
          subst m2c.
          eapply pstr_cc; [exact FR2| exact ERR2| exact PBS2| exact ARR| rewrite upd_length; exact LENc| exact MU| exact WM| exact MI| exact ST| exact FRM'| exact FA'].
      Qed.
    End Room.

    (* [comment removed for export] *)
    Lemma pstr_nonnull : forall (mo : Model) (fc : bv 32) (n : Z) (str tail : list byte)
        (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      LHEAP HI SPB LB m mo -> PBS m buf len -> u8arr psegs m buf bs ->
      CJST m -> stk psegs m lo (bv_unsigned sp) -> rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m -> frm0 fc ->
      s <> 0 -> Bv = [(s, n)] -> bytes_at psegs m s (str ++ wb 0 :: tail) -> ~ In (wb 0) str ->
      Z.of_nat (length str) + 1 + Z.of_nat (length tail) = n ->
      SCPS psegs POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 PB) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x144dc) fc None m (seg_rom psegs)) mo.
    Proof.
      intros until t6. intros HL PBS0 ARR CJ ST ERR MI FRM SNZ EBv STR NONUL LENS.
      pose proof CEIL as CEIL'. unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. try rewrite alloc_ceiling_eq in CEIL.
      pose proof R4 as R4'. try rewrite alloc_ceiling_eq in R4'.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PERRNO in ERR.
      pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
      (* [comment removed for export] *)
      assert (SIN : In (s, n) LB). { eapply Permutation_in; [exact HP|]. right. apply BVLR. rewrite EBv. left. reflexivity. }
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL SIN) 5%nat; intros Q1 Q2 Q3 Q4 Q5). try rewrite alloc_ceiling_eq in Q4. unfold PIMG_LO, PIMG_HI in Q5.
      pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      carve_frame 112%nat ST.
      do 15 step.
      if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
      do 8 step.
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
      rewrite <- (Z_to_bv_bv_unsigned a4).
      eapply evt_cut; [eapply (count_loop s str tail NONUL m1 STR)|].
      cbv beta. intros ms' nelH_; (nelim nelH_ 3%nat; intros c x15 ->).
      (* [comment removed for export] *)
      zstep. zstep. step. step. step.
      apply evt_done. cbv beta.
      pose proof (esc_count_range str) as ER.
      eapply scps_bind.
      { eapply (ensure_spec HI) with (lo := lo) (LR := LR) (bs := bs) (needed := esc_count str + Z.of_nat (length str) + 3); rewrite ?SPFeq;
          first [ exact HL1 | exact HP | exact PBS0 | split; [exact ARR| exact LEN] | exact PN | exact ST | exact ERR | exact MI | exact TP | reflexivity
                | split; [lia| split; [lia| lia]] | unfold ENSURE_STACK, RMALLOC_STACK; lia | lia ]. }
      cbv beta. intros ms2 mo2 PO.
      (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 LB2 -> MI2 ST2 ERR2 PVE HL2 OUT)
.
      rewrite SPFeq in ST2, PVE. unfold PERRNO in ERR2.
      replace (ret_pc (Z_to_bv 64 0x145ac)) with (Z_to_bv 64 0x145ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (* [comment removed for export] *)
      assert (AGR : forall a, 0 <= a < 2^64 -> (SPF <= a /\ (a < PB \/ PB + 64 <= a)) \/ (in_cblock LR a \/ (PDATA_LO <= a < PIMG_HI /\ ~ palloc_static a)) ->
                      m2 (wa a) = m1 (wa a) /\ (wview psegs m1 (wa a) <> None -> wview psegs m2 (wa a) <> None)).
      { intros a Ha Hc. apply PVE; [exact Ha|]. unfold cj_client_addr.
        destruct Hc as [[H1 H2]|[H1|H1]]; [split; [left; lia| lia]| |].
        - split; [right; right; exact H1|]. (nelim H1 4%nat; intros A' n' Hin Hr).
          (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) 5%nat; intros _ _ _ X4 _).
          try rewrite alloc_ceiling_eq in X4. lia.
        - split; [right; left; exact H1|]. unfold PDATA_LO, PIMG_HI in H1. lia. }
      assert (FR2 : FRAME m2 _) by (eapply (rw_cells_magree _ m1 m2); [exact AGR| exact FR| cbn; intros a Ha; left; lia]).
      assert (STR2 : bytes_at psegs m2 s (str ++ wb 0 :: tail)).
      { eapply bytes_at_magree; [exact AGR| exact STR|]. intros a Ha. right; left. exists s, n. split; [apply BVLR; rewrite EBv; left; reflexivity|].
        rewrite length_app in Ha. cbn [length] in Ha. lia. }
      assert (CJ2 : CJST m2).
      { eapply (CJST_pv_agree LR (bv_unsigned sp + -112) PB); [exact CJ1| exact PVE| unfold PIMG_HI; lia]. }
      assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
      { eapply pv_agree_trans; [exact PVA1|]. eapply pv_agree_weaken; [exact PVE| lia| intros b Hb; exact Hb]. }
      clear AGR PVE STR FR ERR MI ST HL1 PVA1 CJ1 ARR PBS0.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
      destruct OUT as [(-> & HPn & PBSn) | [(-> & HPn & PBSn & PDn) | (buf' & len' & bs' & -> & HPn & PBSn & PDn & ROOM & L31)]].
      - (* [comment removed for export] *)
        unfold wz. step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
        apply evt_done. cbv beta.
        eapply pstr_epi; [exact FR2| exact ST2| exact MI2| exact ERR2| exact CJ2| exact FRM| intros k Hk; reflexivity| exact PVA2|].
        exists LB2, 0, 0, off. split; [exact HL2|]. left. split; [reflexivity|]. exists dep. split; [exact PBSn| left; split; [reflexivity| exact HPn]].
      - (* [comment removed for export] *)
        unfold wz. step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
        apply evt_done. cbv beta.
        eapply pstr_epi; [exact FR2| exact ST2| exact MI2| exact ERR2| exact CJ2| exact FRM| intros k Hk; reflexivity| exact PVA2|].
        exists LB2, buf, len, off. split; [exact HL2|]. left. split; [reflexivity|]. exists dep. split; [exact PBSn| right; split; [lia| exact HPn]].
      - (* [comment removed for export] *)
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HPn)) 5%nat; intros Y1 _ _ Y4 _). try rewrite alloc_ceiling_eq in Y4.
        unfold wz. step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
        apply evt_done. cbv beta. destruct PDn as [ARRn LENn].
        eapply (pstr_room m2 mo2 LB2 buf' len' n bs' _ errv2 str tail fc HL2 HPn LENn ltac:(lia) L31 CJ2 PVA2 SNZ EBv NONUL LENS FRM);
          [exact FR2| unfold PERRNO; exact ERR2| exact PBSn| exact ARRn| exact ST2| exact MI2| exact STR2].
    Qed.

    (* [comment removed for export] *)
    Lemma pstr_quotes : forall (mm : word -> option byte) (mo' : Model) (LB' : list cblock) (B len' : Z) (bs' fj : list byte) (errv' : word) (fcc : bv 32)
        x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
      LHEAP HI SPB LB' mm mo' -> Permutation ((B, len') :: LR) LB' -> PBS mm B len' -> u8arr psegs mm B bs' -> Z.of_nat (length bs') = len' ->
      3 + off + 1 <= len' -> len' < 2^31 ->
      FRAME mm fj -> stk psegs mm lo SPF -> mem_inv psegs mm -> rw_cells psegs mm PERRNO [C4 errv'] -> CJST mm -> frm0 fcc ->
      pv_agree LR (bv_unsigned sp) PB m mm ->
      SCPS psegs POST
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (B + off)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x14744) fcc None mm (seg_rom psegs)) mo'.
    Proof.
      intros until x31. intros HL' HP' PBS' ARR LEN' ROOM L31 FR ST MI ERR CJ FRM PVA.
      pose proof CEIL as CEIL'. unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. try rewrite alloc_ceiling_eq in CEIL.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3).
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL' (perm_in_head _ _ _ HP')) 5%nat; intros Y1 Y2 Y3 Y4 Y5). try rewrite alloc_ceiling_eq in Y4. unfold PIMG_LO, PIMG_HI in Y5.
      unfold PERRNO in ERR.
      pose proof (munch_refl [(B + off, B + off + 3)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
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
        (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      LHEAP HI SPB LB m1 mo -> PBS m1 buf len -> u8arr psegs m1 buf bs ->
      FRAME m1 fj -> stk psegs m1 lo SPF -> rw_cells psegs m1 PERRNO [C4 errv] -> mem_inv psegs m1 -> CJST m1 -> frm0 fc ->
      pv_agree LR (bv_unsigned sp) PB m m1 ->
      SCPS psegs POST
        (MS (mkR ra (Z_to_bv 64 SPF) gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 PB) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1469c) fc None m1 (seg_rom psegs)) mo.
    Proof.
      intros until x31. intros HL PBS1 ARR FR ST ERR MI CJ FRM PVA.
      pose proof CEIL as CEIL'. unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. try rewrite alloc_ceiling_eq in CEIL.
      pose proof R4 as R4'. try rewrite alloc_ceiling_eq in R4'.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PERRNO in ERR. pose proof SPFeq as E1.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      step. step. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
      step. step. zstep. zstep. if_cases Koff; zify_cond Koff.
      { (* [comment removed for export] *)
        step. step. apply evt_done. cbv beta.
        eapply pstr_epi; [exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| intros k Hk; reflexivity| exact PVA|].
        exists LB, buf, len, off. split; [exact HL|]. left. split; [reflexivity|]. exists dep. split; [exact PBS1| right; split; [lia| exact HP]]. }
      zstep. zstep. if_cases Kroom; zify_cond Kroom.
      { (* [comment removed for export] *)
        zstep. apply evt_done. cbv beta.
        eapply pstr_quotes; [exact HL| exact HP| exact PBS1| exact ARR| exact LEN| lia| exact PN2| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact PVA]. }
      step. step. if_cases Kna; zify_cond Kna; [| exfalso; apply Kna; reflexivity]. clear Kna.
      (* [comment removed for export] *)
      assert (GROW : forall ns x12' x14',
        off + 4 <= ns < 2^31 ->
        evt psegs (fun ms' => SCPS psegs POST ms' mo)
          (MS (mkR ra (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 ns) s1 (Z_to_bv 64 buf) (Z_to_bv 64 PB) x12' (Z_to_bv 64 len) x14' x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x14778) fc None m1 (seg_rom psegs))).
      { intros ns x12' x14' NS.
        step. step. if_cases Kd; zify_cond Kd; [exfalso; lia|]. clear Kd.
        step. step. step.
        replace (ret_pc (Z_to_bv 64 93068)) with (wz PREALLOC) by (unfold wz, PREALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply evt_done. cbv beta.
        eapply scps_bind.
        { eapply (lh_realloc HI) with (lo := lo) (A := buf) (k := len) (n := ns) (old := bs); rewrite ?E1;
            first [ exact HL | eapply perm_in_head; exact HP | exact (proj1 ARR) | exact ST | exact ERR | exact MI | exact TP | reflexivity | unfold RMALLOC_STACK; lia ]. }
        cbv beta. intros ms2 mo2 PO.
        (nelim PO 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 -> MI2 ST2 ERR2 RES)
.
        rewrite E1 in ST2. unfold PERRNO in ERR2.
        replace (ret_pc (Z_to_bv 64 0x1478c)) with (Z_to_bv 64 0x1478c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        destruct RES as [(-> & HL2 & PR2) | (B & junk & -> & CR & HB & HL2 & PR2 & BLK)].
        - (* [comment removed for export] *)
          rewrite E1 in PR2. unfold wz.
          apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
          apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PBS1; [| left; lia].
          apply (CJST_pres _ _ _ _ PR2) in CJ.
          assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
          { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_alloc; [exact PR2| lia|].
            intros b Hb. eapply Permutation_in; [exact HP| right; exact Hb]. }
          clear PVA PR2 MI ST ERR HL ARR.
          eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
          step. if_cases K0; zify_cond K0; [exfalso; apply K0; reflexivity|]. clear K0.
          step. step. step. step.
          replace (ret_pc (Z_to_bv 64 86496)) with (wz PFREE) by (unfold wz, PFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
          apply evt_done. cbv beta.
          eapply scps_bind.
          { eapply (lh_free HI) with (lo := lo) (A := buf) (n := len); rewrite ?E1;
              first [ exact HL2 | eapply perm_in_head; exact HP | exact ST2 | exact ERR2 | exact MI2 | exact TP | reflexivity | unfold RMALLOC_STACK; lia ]. }
          cbv beta. intros ms3 mo3 PO.
          (nelim PO 22%nat; intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 -> MI3 ST3 ERR3 PR3 HL3)
.
          rewrite E1 in ST3, PR3. unfold PERRNO in ERR3.
          replace (ret_pc (Z_to_bv 64 0x147ec)) with (Z_to_bv 64 0x147ec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          pose proof (perm_cb_remove _ _ _ _ HP (lh_nodup HI _ _ _ _ HL2)) as HP3.
          apply (cj_pres_rw_cells _ _ _ _ _ _ PR3) in FR; [| left; lia].
          apply (cj_pres_rw_cells _ _ _ _ _ _ PR3) in PBS1; [| left; lia].
          apply (CJST_pres _ _ _ _ PR3) in CJ.
          assert (PVA3 : pv_agree LR (bv_unsigned sp) PB m m3).
          { eapply pv_agree_trans; [exact PVA2|]. eapply pv_agree_alloc; [exact PR3| lia|].
            intros b Hb. eapply Permutation_in; [exact HP3| exact Hb]. }
          clear PVA2 PR3 MI2 ST2 ERR2 HL2.
          pose proof (munch_refl [(PB, PB + 16)] m3) as MU. pose proof (wmono_refl psegs m3) as WM.
          eapply scps_step_evt; [eapply (lh_mok HI); exact HL3|].
          step. step. fix_lit_store. step. fix_lit_store. step.
          apply evt_done. cbv beta.
          eapply pstr_epi; [exact FR| exact ST3| exact MI3| exact ERR3| | exact FRM| intros k Hk; reflexivity| |].
          + eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E2|[]]. inversion E2; subst. unfold PDATA_LO, PIMG_HI. lia.
          + eapply pv_agree_trans; [exact PVA3|]. eapply pv_agree_hole; [exact MU| exact WM| lia| lia].
          + exists (cb_remove buf LB), 0, 0, off. split.
            { eapply (lh_frame HI); [exact HL3| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
            left. split; [reflexivity|]. exists dep. split; [exact PBS1| left; split; [reflexivity| exact HP3]].
        - (* [comment removed for export] *)
          rewrite E1 in PR2. unfold wz.
          (nelim CR 5%nat; intros CR1 CR2 CR3 CR4 CR5). try rewrite alloc_ceiling_eq in CR4. unfold PIMG_LO, PIMG_HI in CR5.
          pose proof (perm_cb_remove _ _ _ _ HP (lh_nodup HI _ _ _ _ HL)) as HPr.
          apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
          apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PBS1; [| left; lia].
          apply (CJST_pres _ _ _ _ PR2) in CJ.
          assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
          { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_alloc; [exact PR2| lia|].
            intros b Hb. eapply Permutation_in; [exact HPr| exact Hb]. }
          clear PVA PR2 MI ST ERR HL ARR.
          rewrite (Z.min_l len ns) in BLK by lia.
          pose proof (munch_refl [(PB, PB + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
          eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
          step. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
          step. step. step. zstep. step.
          apply evt_done. cbv beta.
          (nelim (u8arr_of_two_CB _ _ _ _ _ _ BLK) 3%nat; intros ARR2 La Lb).
          assert (HP2 : Permutation ((B, ns) :: LR) ((B, ns) :: cb_remove buf LB)) by (apply perm_skip; exact HPr).
          eapply pstr_quotes; [ | exact HP2| exact PBS1| exact ARR2| rewrite length_app, La, Lb; lia| lia| lia| exact FR| exact ST2| exact MI2| exact ERR2| | exact FRM|].
          + eapply (lh_frame HI); [exact HL2| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia.
          + eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E2|[]]. inversion E2; subst. unfold PDATA_LO, PIMG_HI. lia.
          + eapply pv_agree_trans; [exact PVA2|]. eapply pv_agree_hole; [exact MU| exact WM| lia| lia]. }
      zstep. zstep. if_cases K30; zify_cond K30.
      - zstep. apply GROW. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 in K30 by lia. lia.
      - zstep. zstep. if_cases K31; zify_cond K31.
        + step. step. apply evt_done. cbv beta.
          eapply pstr_epi; [exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| intros k Hk; reflexivity| exact PVA|].
          exists LB, buf, len, off. split; [exact HL|]. left. split; [reflexivity|]. exists dep. split; [exact PBS1| right; split; [lia| exact HP]].
        + step. step. step. apply GROW. rewrite Z.shiftr_div_pow2 in K31 by lia. lia.
    Qed.

    Lemma pstr_isnull : forall (mo : Model) (fc : bv 32) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      LHEAP HI SPB LB m mo -> PBS m buf len -> u8arr psegs m buf bs ->
      CJST m -> stk psegs m lo (bv_unsigned sp) -> rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m -> frm0 fc ->
      SCPS psegs POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 PB) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x144dc) fc None m (seg_rom psegs)) mo.
    Proof.
      intros until t6. intros HL PBS0 ARR CJ ST ERR MI FRM.
      pose proof CEIL as CEIL'. unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK in LO. try rewrite alloc_ceiling_eq in CEIL.
      pose proof R4 as R4'. try rewrite alloc_ceiling_eq in R4'.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3). unfold PERRNO in ERR.
      pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      carve_frame 112%nat ST.
      do 15 step.
      if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
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


End CeilWrap.
(* [comment removed for export] *)
Ltac slv := rewrite ?alloc_ceiling_eq in *; unfold RMALLOC_STACK, ENSURE_STACK, PSTR_STACK in *; lia.
Ltac dlia := cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr psegs ?m B ?buf |- _ =>
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pv_update.
Module CJ_pv_ctx.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common.CJ_ensure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_update CJ_pstr.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma CJST_magree_hole : forall mm m2 (SPF PB : Z) LR,
  CJST mm ->
  (forall a, 0 <= a < 2^64 -> (SPF <= a /\ (a < PB \/ PB + 64 <= a)) \/ (in_cblock LR a \/ (PDATA_LO <= a < PIMG_HI /\ ~ palloc_static a)) ->
      m2 (wa a) = mm (wa a) /\ (wview psegs mm (wa a) <> None -> wview psegs m2 (wa a) <> None)) ->
  CJST m2.
Proof.
  intros mm m2 SPF PB LR (HK & (e1 & e2 & GE) & LC) AGR.
  split; [|split; [exists e1, e2|]].
  all: eapply rw_cells_magree; [exact AGR| eassumption|].
  all: cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; right; right;
       unfold palloc_static; unfold PHOOKS, PGERROR, PLCONV, PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP in *; lia.
Qed.

Section S.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
            (m : word -> option byte)
            (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z).

  Notation SPF := (bv_unsigned sp + -128).
  Notation PVFRAME mm loc := (rw_cells psegs mm (bv_unsigned sp + -128)
     [CB 48 loc; C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation PBSd mm b l o d := (rw_cells psegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 d);
                                               C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 86816); C8 (Z_to_bv 64 86496); C8 (Z_to_bv 64 93068)]).

  Definition actx (depc : Z) (mm : word -> option byte) (mo : Model) (loc : list byte) (Fc : bvmap 5 word) (fcc : bv 32) (errv : word)
      (LB : list cblock) (buf len off : Z) (bs : list byte) : Prop :=
    LHEAP HI SPB LB mm mo /\ Permutation ((buf, len) :: LR) LB /\ PBSd mm buf len off depc /\ u8arr psegs mm buf bs /\ Z.of_nat (length bs) = len
    /\ pb_nums len off depc /\ PVFRAME mm loc /\ stk psegs mm lo SPF /\ rw_cells psegs mm PERRNO [C4 errv] /\ mem_inv psegs mm /\ CJST mm
    /\ frm0 fcc /\ FAG18 F Fc /\ pv_agree LR (bv_unsigned sp) PB m mm.

  Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PV_STACK n.
  Hypothesis BLR : forall b, In b B -> In b LR.

  (* [comment removed for export] *)
  Lemma actx_magree : forall depc mm mo loc Fc fcc errv LB buf len off bs,
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> magree (in_cblock B) m mm.
  Proof.
    intros until bs. intros nelH_; (nelim nelH_ 14%nat; intros HL HP _ _ _ _ _ _ _ _ _ _ _ PVA).
    pose proof CEIL as C. try rewrite alloc_ceiling_eq in C. unfold PV_STACK, PV_BASE in LO. (nelimp PL 3%nat; intros PL1 PL2 PL3).
    eapply magree_mono; [exact PVA|]. cbv beta. intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr). split; [right; right; exists A', n'; split; [apply BLR; exact Hin| exact Hr]|].
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; apply BLR; exact Hin])) 5%nat; intros _ _ _ R _).
    try rewrite alloc_ceiling_eq in R. lia.
  Qed.

  Lemma actx_chain : forall depc mm mo loc Fc fcc errv LB buf len off bs T d q Bq,
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> cj_chain T m d q Bq -> (forall b, In b Bq -> In b B) -> cj_chain T mm d q Bq.
  Proof.
    intros until Bq. intros CTX CH SUB. eapply cj_chain_magree; [exact CH| eapply actx_magree; exact CTX|].
    intros a Ha. eapply in_cblock_mono; [exact SUB| exact Ha].
  Qed.

  Lemma actx_str : forall depc mm mo loc Fc fcc errv LB buf len off bs s Bs,
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> cj_str m s Bs -> (forall b, In b Bs -> In b B) -> cj_str mm s Bs.
  Proof.
    intros until Bs. intros CTX SV SUB. eapply cj_str_magree; [eapply actx_magree; exact CTX| exact SV|].
    intros a Ha. eapply in_cblock_mono; [exact SUB| exact Ha].
  Qed.

  Lemma actx_node : forall depc mm mo loc Fc fcc errv LB buf len off bs q cells,
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> rw_cells psegs m q cells -> cells_size cells = 64%nat -> In (q, 64) B ->
    rw_cells psegs mm q cells.
  Proof.
    intros until cells. intros CTX ND SZ HIN. eapply rw_cells_magree; [eapply actx_magree; exact CTX| exact ND|].
    rewrite SZ. intros a Ha. exists q, 64. split; [exact HIN| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma actx_tree : forall depc mm mo loc Fc fcc errv LB buf len off bs,
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> cj_chain CJ_PRINTABLE m n p B -> cj_chain CJ_PRINTABLE mm n p B.
  Proof. intros. eapply actx_chain; eauto. Qed.

  Hypothesis TP : tp = wz PTP.
  Hypothesis N1 : (1 <= n)%nat.
  Hypothesis CH0 : cj_chain CJ_PRINTABLE m n p B.

  (* [comment removed for export] *)
  Definition fctx (mm : word -> option byte) (loc : list byte) (Fc : bvmap 5 word) (fcc : bv 32) (errv : word) : Prop :=
    PVFRAME mm loc /\ stk psegs mm lo SPF /\ rw_cells psegs mm PERRNO [C4 errv] /\ mem_inv psegs mm /\ CJST mm
    /\ frm0 fcc /\ FAG18 F Fc /\ pv_agree LR (bv_unsigned sp) PB m mm /\ cj_chain CJ_PRINTABLE mm n p B.

  Definition ens_post (depc : Z) (loc : list byte) (Fc : bvmap 5 word) (fcc : bv 32) (off needed : Z)
      (x1 x8 x9 x18 x19 x20 x21 x22 : word) : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (errv' : word) (LB' : list cblock) (buf' len' : Z),
      ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Fc (ret_pc x1) fcc None m' (seg_rom psegs)
      /\ LHEAP HI SPB LB' m' mo' /\ fctx m' loc Fc fcc errv' /\ PBSd m' buf' len' off depc
      /\ ( (a0 = Z_to_bv 64 0 /\ ((buf' = 0 /\ Permutation LR LB') \/ (buf' <> 0 /\ Permutation ((buf', len') :: LR) LB')))
        \/ (exists bs', a0 = Z_to_bv 64 (buf' + off) /\ actx depc m' mo' loc Fc fcc errv' LB' buf' len' off bs' /\ needed + off + 1 <= len') ).

  (* [comment removed for export] *)
  Lemma actx_ensure : forall depc mm mo loc Fc fcc errv LB buf len off bs needed
      (x1 t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 : word),
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> 0 <= needed < 2^64 ->
    SCPS psegs (ens_post depc loc Fc fcc off needed x1 x8 x9 x18 x19 x20 x21 x22)
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 PB) (Z_to_bv 64 needed) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fc (wz ENSURE_ENTRY) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until t6. intros CTX ND.
    pose proof (actx_tree _ _ _ _ _ _ _ _ _ _ _ _ CTX CH0) as CHn.
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. unfold PV_STACK, PV_BASE in LO.
    (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3).
    assert (E1 : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
    eapply scps_mono.
    { eapply (ensure_spec HI) with (lo := lo) (LR := LR) (bs := bs) (needed := needed); rewrite ?E1;
        first [ exact HL | exact HP | exact PBS0 | split; [exact ARR| exact LEN] | exact PN | exact ST | exact ERR | exact MI | exact TP | reflexivity
              | split; [lia| split; [lia| lia]] | unfold ENSURE_STACK, RMALLOC_STACK; lia | lia ]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 LB2 -> MI2 ST2 ERR2 PVE HL2 OUT)
.
    rewrite E1 in ST2, PVE.
    (* [comment removed for export] *)
    assert (AGR : forall a, 0 <= a < 2^64 -> (SPF <= a /\ (a < PB \/ PB + 64 <= a)) \/ (in_cblock LR a \/ (PDATA_LO <= a < PIMG_HI /\ ~ palloc_static a)) ->
                    m2 (wa a) = mm (wa a) /\ (wview psegs mm (wa a) <> None -> wview psegs m2 (wa a) <> None)).
    { intros a Ha Hc. apply PVE; [exact Ha|]. unfold cj_client_addr.
      destruct Hc as [[H1 H2]|[H1|H1]]; [split; [left; lia| lia]| |].
      - split; [right; right; exact H1|]. (nelim H1 4%nat; intros A' n' Hin Hr).
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) 5%nat; intros _ _ _ X4 _).
        try rewrite alloc_ceiling_eq in X4. lia.
      - split; [right; left; exact H1|]. unfold PDATA_LO, PIMG_HI in H1. lia. }
    assert (FR2 : PVFRAME m2 loc) by (eapply (rw_cells_magree _ mm m2); [exact AGR| exact FR| cbn; intros a Ha; left; lia]).
    assert (CJ2 : CJST m2) by (eapply (CJST_magree_hole mm m2); [exact CJ| exact AGR]).
    assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
    { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_weaken; [exact PVE| lia| intros b Hb; exact Hb]. }
    assert (CH2 : cj_chain CJ_PRINTABLE m2 n p B).
    { eapply cj_chain_magree; [exact CHn| exact AGR|]. intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr). right; left. exists A', n'. split; [apply BLR; exact Hin| exact Hr]. }
    assert (FC2 : fctx m2 loc Fc fcc errv2).
    { split; [exact FR2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact CJ2|]. split; [exact FRM|]. split; [exact FA|]. split; [exact PVA2| exact CH2]. }
    unfold ens_post. unfold wz in OUT.
    destruct OUT as [(-> & HPn & PBSn) | [(-> & HPn & PBSn & PDn) | (buf' & len' & bs' & -> & HPn & PBSn & PDn & ROOM & L31)]].
    - nexists 20%nat. split; [reflexivity|]. split; [exact HL2|]. split; [exact FC2|]. split; [exact PBSn|]. left. split; [reflexivity| left; split; [reflexivity| exact HPn]].
    - nexists 20%nat. split; [reflexivity|]. split; [exact HL2|]. split; [exact FC2|]. split; [exact PBSn|]. left. split; [reflexivity| right; split; [|exact HPn]].
      pose proof (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HPn)) as (Y1 & _). lia.
    - nexists 20%nat. split; [reflexivity|]. split; [exact HL2|]. split; [exact FC2|]. split; [exact PBSn|]. right. exists bs'. split; [reflexivity|]. split; [| exact ROOM].
      destruct PDn as [ARRn LENn].
      split; [exact HL2|]. split; [exact HPn|]. split; [exact PBSn|]. split; [exact ARRn|]. split; [exact LENn|]. split; [split; [lia| split; [exact L31| lia]]|].
      split; [exact FR2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact CJ2|]. split; [exact FRM|]. split; [exact FA| exact PVA2].
  Qed.

  (* [comment removed for export] *)
  Definition rec_post (depc : Z) (loc : list byte) (Fc : bvmap 5 word) (d : nat) (c : Z) (Bc : list cblock)
      (x1 x8 x9 x18 x19 x20 x21 x22 : word) : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Fc' : bvmap 5 word) (fcc' : bv 32) (m' : word -> option byte) (errv' : word)
                          (LB' : list cblock) (buf' len' off' : Z),
      ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Fc' (ret_pc x1) fcc' None m' (seg_rom psegs)
      /\ LHEAP HI SPB LB' m' mo' /\ fctx m' loc Fc' fcc' errv'
      /\ ( (a0 = Z_to_bv 64 0 /\ exists dep', PBSd m' buf' len' off' dep' /\ ((buf' = 0 /\ Permutation LR LB') \/ (buf' <> 0 /\ Permutation ((buf', len') :: LR) LB')))
        \/ (a0 = Z_to_bv 64 1 /\ exists bs', actx depc m' mo' loc Fc' fcc' errv' LB' buf' len' off' bs' /\ pb_nul bs' len' off') ).

  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.

  Lemma actx_rec : forall depc mm mo loc Fc fcc errv LB buf len off bs (d : nat) (c : Z) (Bc : list cblock)
      (x1 t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 : word),
    pvalue_spec_at HI d -> (d < n)%nat ->
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> depc + Z.of_nat d <= 2^40 ->
    cj_chain CJ_PRINTABLE m d c Bc -> c <> 0 -> (forall b, In b Bc -> In b B) ->
    SCPS psegs (rec_post depc loc Fc d c Bc x1 x8 x9 x18 x19 x20 x21 x22)
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 c) (Z_to_bv 64 PB) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fc (wz PVALUE_ENTRY) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until t6. intros RECd Dlt CTX DEP CHc CNZ SUB.
    pose proof (actx_tree _ _ _ _ _ _ _ _ _ _ _ _ CTX CH0) as CHn.
    pose proof (actx_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX CHc SUB) as CHcn.
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. unfold PV_STACK, PV_BASE in LO.
    (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3).
    assert (E1 : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
    eapply scps_mono.
    { eapply RECd with (lo := lo) (LR := LR) (bs := bs) (B := Bc); rewrite ?E1;
        first [ exact HL | exact HP | exact PBS0 | split; [exact ARR| exact LEN] | exact PN | exact DEP | exact CHcn | exact CNZ | exact CJ | exact ST | exact ERR | exact MI | exact TP | exact FRM | reflexivity
              | intros b Hb; apply BLR, SUB, Hb
              | split; [lia| split; [lia| lia]]
              | rewrite <- Zminus_mod_idemp_l, SPAL; reflexivity
              | unfold PV_STACK, PV_BASE; lia | lia ]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 29%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fc' fcc' m2 errv2 -> MI2 FRM2 FA2 ST2 ERR2 CJ2 PVE CHc2 OUT)
.
    rewrite E1 in ST2, PVE.
    assert (AGR : forall a, 0 <= a < 2^64 -> (SPF <= a /\ (a < PB \/ PB + 64 <= a)) \/ (in_cblock LR a \/ (PDATA_LO <= a < PIMG_HI /\ ~ palloc_static a)) ->
                    m2 (wa a) = mm (wa a) /\ (wview psegs mm (wa a) <> None -> wview psegs m2 (wa a) <> None)).
    { intros a Ha Hc. apply PVE; [exact Ha|]. unfold cj_client_addr.
      destruct Hc as [[H1 H2]|[H1|H1]]; [split; [left; lia| lia]| |].
      - split; [right; right; exact H1|]. (nelim H1 4%nat; intros A' n' Hin Hr).
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) 5%nat; intros _ _ _ X4 _).
        try rewrite alloc_ceiling_eq in X4. lia.
      - split; [right; left; exact H1|]. unfold PDATA_LO, PIMG_HI in H1. lia. }
    assert (FR2 : PVFRAME m2 loc) by (eapply (rw_cells_magree _ mm m2); [exact AGR| exact FR| cbn; intros a Ha; left; lia]).
    assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
    { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_weaken; [exact PVE| lia| intros b Hb; exact Hb]. }
    assert (CH2 : cj_chain CJ_PRINTABLE m2 n p B).
    { eapply cj_chain_magree; [exact CHn| exact AGR|]. intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr). right; left. exists A', n'. split; [apply BLR; exact Hin| exact Hr]. }
    assert (FA2' : FAG18 F Fc'). { intros k Hk. rewrite (FA2 k ltac:(unfold fp_callee_saved; lia)). apply FA. exact Hk. }
    assert (FC2 : fctx m2 loc Fc' fcc' errv2).
    { split; [exact FR2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact CJ2|]. split; [exact FRM2|]. split; [exact FA2'|]. split; [exact PVA2| exact CH2]. }
    unfold rec_post. unfold wz in OUT.
    destruct OUT as (LB' & buf' & len' & off' & HL' & [(-> & dep' & PBS' & HB) | (-> & bs' & HP' & PBS' & PD' & PN' & NUL)]).
    - nexists 23%nat. split; [reflexivity|]. split; [exact HL'|]. split; [exact FC2|]. left. split; [reflexivity|]. exists dep'. split; [exact PBS'| exact HB].
    - nexists 23%nat. split; [reflexivity|]. split; [exact HL'|]. split; [exact FC2|]. right. split; [reflexivity|]. exists bs'. split; [| exact NUL].
      destruct PD' as [ARR' LEN'].
      split; [exact HL'|]. split; [exact HP'|]. split; [exact PBS'|]. split; [exact ARR'|]. split; [exact LEN'|]. split; [exact PN'|].
      split; [exact FR2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact CJ2|]. split; [exact FRM2|]. split; [exact FA2'| exact PVA2].
  Qed.

  (* [comment removed for export] *)
  Definition upd_post (depc : Z) (mo : Model) (loc : list byte) (Fc : bvmap 5 word) (fcc : bv 32) (LB : list cblock) (buf len off : Z) (bs : list byte)
      (x1 x8 x9 x18 x19 x20 x21 x22 : word) : machine_state -> Prop :=
    fun ms' => exists (k : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (errv' : word),
      ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Fc (ret_pc x1) fcc None m' (seg_rom psegs)
      /\ actx depc m' mo loc Fc fcc errv' LB buf len off bs /\ 0 <= k /\ off + k < len /\ nth_error bs (Z.to_nat (off + k)) = Some (wb 0).

  Lemma actx_strlen : forall depc mm mo loc Fc fcc errv LB buf len off bs
      (x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 : word),
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> pb_nul bs len off ->
    evt psegs (upd_post depc mo loc Fc fcc LB buf len off bs x1 x8 x9 x18 x19 x20 x21 x22)
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (buf + off)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fc (Z_to_bv 64 0x20ee4) fcc None mm (seg_rom psegs)).
  Proof.
    intros until t6. intros CTX NUL.
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    eapply evt_cut.
    { eapply (strlen_upd HI) with (off := off); [exact HL| eapply perm_in_head; exact HP| exact ARR| exact LEN| lia| exact NUL| exact MI| reflexivity]. }
    cbv beta. intros ms' PO.
    (nelim PO 23%nat; intros k t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MU WM MI' K0 K1 KN).
    apply evt_done. unfold upd_post. exists k. nexists 16%nat. split; [reflexivity|]. split; [| split; [exact K0| split; [exact K1| exact KN]]].
    split. { eapply (lh_frame HI); [exact HL| exact MU| exact WM| constructor]. }
    split; [exact HP|]. split; [eapply rw_cells_transport; [exact PBS0| exact MU| exact WM| exact I]|].
    split; [eapply u8arr_transport; [exact ARR| exact MU| exact WM| exact I]|]. split; [exact LEN|]. split; [exact PN|].
    split; [eapply rw_cells_transport; [exact FR| exact MU| exact WM| exact I]|].
    split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| exact I]|].
    split; [eapply rw_cells_transport; [exact ERR| exact MU| exact WM| exact I]|]. split; [exact MI'|].
    split; [eapply CJST_frame; [exact CJ| exact MU| exact WM| intros lo' hi' []]|]. split; [exact FRM|]. split; [exact FA|].
    eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM| intros; exact I].
  Qed.

  (* [comment removed for export] *)
  Hypothesis SPRU : F_printf_iface.sprintf_u04x_stmt.

  Lemma actx_pstr : forall depc mm mo loc Fc fcc errv LB buf len off bs (ky : Z) (Bk : list cblock)
      (x1 t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 : word),
    actx depc mm mo loc Fc fcc errv LB buf len off bs ->
    cj_str m ky Bk -> (forall b, In b Bk -> In b B) ->
    SCPS psegs (rec_post depc loc Fc 0%nat 0 [] x1 x8 x9 x18 x19 x20 x21 x22)
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 ky) (Z_to_bv 64 PB) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fc (wz PSTR_ENTRY) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until t6. intros CTX SK SUB.
    pose proof (actx_tree _ _ _ _ _ _ _ _ _ _ _ _ CTX CH0) as CHn.
    pose proof (actx_str _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX SK SUB) as SKn.
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. unfold PV_STACK, PV_BASE in LO.
    (nelimp PL 3%nat; intros PL1 PL2 PL3). (nelimp PN 3%nat; intros PN1 PN2 PN3).
    assert (E1 : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
    eapply scps_mono.
    { eapply (pstr_spec HI SPRU) with (lo := lo) (LR := LR) (bs := bs) (Bv := Bk); rewrite ?E1;
        first [ exact HL | exact HP | exact PBS0 | split; [exact ARR| exact LEN] | exact PN | exact SKn | exact CJ | exact ST | exact ERR | exact MI | exact TP | exact FRM | reflexivity
              | intros b Hb; apply BLR, SUB, Hb
              | split; [lia| split; [lia| lia]]
              | unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK; lia | lia ]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 28%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fc' fcc' m2 errv2 -> MI2 FRM2 FA2 ST2 ERR2 CJ2 PVE OUT)
.
    rewrite E1 in ST2, PVE.
    assert (AGR : forall a, 0 <= a < 2^64 -> (SPF <= a /\ (a < PB \/ PB + 64 <= a)) \/ (in_cblock LR a \/ (PDATA_LO <= a < PIMG_HI /\ ~ palloc_static a)) ->
                    m2 (wa a) = mm (wa a) /\ (wview psegs mm (wa a) <> None -> wview psegs m2 (wa a) <> None)).
    { intros a Ha Hc. apply PVE; [exact Ha|]. unfold cj_client_addr.
      destruct Hc as [[H1 H2]|[H1|H1]]; [split; [left; lia| lia]| |].
      - split; [right; right; exact H1|]. (nelim H1 4%nat; intros A' n' Hin Hr).
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) 5%nat; intros _ _ _ X4 _).
        try rewrite alloc_ceiling_eq in X4. lia.
      - split; [right; left; exact H1|]. unfold PDATA_LO, PIMG_HI in H1. lia. }
    assert (FR2 : PVFRAME m2 loc) by (eapply (rw_cells_magree _ mm m2); [exact AGR| exact FR| cbn; intros a Ha; left; lia]).
    assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
    { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_weaken; [exact PVE| lia| intros b Hb; exact Hb]. }
    assert (CH2 : cj_chain CJ_PRINTABLE m2 n p B).
    { eapply cj_chain_magree; [exact CHn| exact AGR|]. intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr). right; left. exists A', n'. split; [apply BLR; exact Hin| exact Hr]. }
    assert (FA2' : FAG18 F Fc'). { intros k Hk. rewrite (FA2 k ltac:(lia)). apply FA. exact Hk. }
    assert (FC2 : fctx m2 loc Fc' fcc' errv2).
    { split; [exact FR2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact CJ2|]. split; [exact FRM2|]. split; [exact FA2'|]. split; [exact PVA2| exact CH2]. }
    unfold rec_post. unfold wz in OUT.
    destruct OUT as (LB' & buf' & len' & off' & HL' & [(-> & dep' & PBS' & HB) | (-> & bs' & HP' & PBS' & PD' & PN' & NUL)]).
    - nexists 23%nat. split; [reflexivity|]. split; [exact HL'|]. split; [exact FC2|]. left. split; [reflexivity|]. exists dep'. split; [exact PBS'| exact HB].
    - nexists 23%nat. split; [reflexivity|]. split; [exact HL'|]. split; [exact FC2|]. right. split; [reflexivity|]. exists bs'. split; [| exact NUL].
      destruct PD' as [ARR' LEN'].
      split; [exact HL'|]. split; [exact HP'|]. split; [exact PBS'|]. split; [exact ARR'|]. split; [exact LEN'|]. split; [exact PN'|].
      split; [exact FR2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact CJ2|]. split; [exact FRM2|]. split; [exact FA2'| exact PVA2].
  Qed.
End S.


End CeilWrap.
End CJ_pv_ctx.

(* [comment removed for export] *)
Module CJ_pv_cases.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common CJ_pv_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition pv_case_at (entry : Z) (HI : cj_heap_iface) (n : nat) : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
         (m : word -> option byte) (SPB : Z) (LR B : list cblock) (p PB dep : Z) (fw : word) (lo : Z),
    pb_place (bv_unsigned sp) PB SPB -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PV_STACK n -> tp = wz PTP ->
    bv_unsigned sp <= 2^64 -> (1 <= n)%nat -> (forall b, In b B -> In b LR) -> bv_unsigned sp mod 16 = 0 ->
    dep + Z.of_nat n <= 2^40 -> 0 <= dep -> p <> 0 -> cj_chain CJ_PRINTABLE m n p B ->
    (forall d, (d < n)%nat -> pvalue_spec_at HI d) ->
    forall mm mo loc Fc fcc errv LB buf len off bs
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 : word),
    actx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR PB fw lo dep mm mo loc Fc fcc errv LB buf len off bs ->
    SCPS psegs (pvalue_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 p) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 entry) fcc None mm (seg_rom psegs)) mo.

Definition PV_ARR_ENTRY : Z := 0x134a0.
Definition PV_OBJ_ENTRY : Z := 0x131e0.
Definition PV_NUM_ENTRY : Z := 0x133d4.


End CeilWrap.
End CJ_pv_cases.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pstr_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pstr_A.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_pv_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_pv_common.CJ_ensure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_pstr_B CJ_pv_common.
Import CJ_pv_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import CJ_pv_update.
Import CJ_pv_cases.
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

Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr psegs ?m B ?buf |- _ =>
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
  Hypothesis DEPN : dep + Z.of_nat n <= 2^40.
  Hypothesis DEP0 : 0 <= dep.
  Hypothesis PNZ : p <> 0.
  Hypothesis CH0 : cj_chain CJ_PRINTABLE m n p B.
  Hypothesis REC : forall d, (d < n)%nat -> pvalue_spec_at HI d.

  Notation POST := (pvalue_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m).
  Notation SPF := (bv_unsigned sp + -128).
  Notation PVFRAME mm loc := (rw_cells psegs mm (bv_unsigned sp + -128)
     [CB 48 loc; C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation PBSd mm b l o d := (rw_cells psegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 d);
                                               C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 86816); C8 (Z_to_bv 64 86496); C8 (Z_to_bv 64 93068)]).
  Notation ACTX := (actx HI ra sp s0 s1 s2 s3 s4 s5 s6 F m SPB LR PB fw lo).

  (* [comment removed for export] *)
  Ltac tree_now CTX CHn := assert (CHn : cj_chain CJ_PRINTABLE _ n p B) by (eapply (actx_tree HI); [exact PL| exact CEIL| exact LO| exact BLR| exact CTX| exact CH0]).

  Ltac open_actx CTX :=
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA);
    pose proof CEIL as CEIL'; unfold PV_STACK, PV_BASE in LO; try rewrite alloc_ceiling_eq in CEIL;
    (nelimp PL 3%nat; intros PL1 PL2 PL3); pose proof PN as PNc; (nelim PN 3%nat; intros PN1 PN2 PN3); unfold PERRNO in ERR;
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5);
    try rewrite alloc_ceiling_eq in R4; unfold PIMG_LO, PIMG_HI in R5.


  (* [comment removed for export] *)
  Lemma arr_fail : forall depc mm mo loc Fc fcc errv LB buf len off bs (buf0 len0 off0 dep0 : Z)
      x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    ACTX depc mm mo loc Fc fcc errv LB buf len off bs ->
    (exists LB' dep', LHEAP HI SPB LB' mm mo /\ PBSd mm buf0 len0 off0 dep'
        /\ ((buf0 = 0 /\ Permutation LR LB') \/ (buf0 <> 0 /\ Permutation ((buf0, len0) :: LR) LB'))) ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13930) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX nelH_; (nelim nelH_ 5%nat; intros LB' dep' HL' PBS' HB).
    assert (CHn : cj_chain CJ_PRINTABLE mm n p B) by (eapply (actx_tree HI); [exact PL| exact CEIL| exact LO| exact BLR| exact CTX| exact CH0]).
    open_actx CTX.
    eapply pv_epi; [exact CEIL'| unfold PV_STACK, PV_BASE; lia| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CHn|].
    exists LB', buf0, len0, off0. split; [exact HL'|]. left. split; [reflexivity|]. exists dep'. split; [exact PBS'| exact HB].
  Qed.

  Ltac open_fctx FC := (nelim FC 9%nat; intros FR ST ERR MI CJ FRM FA PVA CHn); unfold PERRNO in ERR.

  (* [comment removed for export] *)
  Lemma pv_close : forall mm mo loc Fc fcc errv LB buf len off bs (j v : Z)
      x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    ACTX (dep + 1) mm mo loc Fc fcc errv LB buf len off bs -> 0 <= j -> off + j + 2 <= len -> 0 <= v < 256 ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 (Z_to_bv 64 (buf + off + j)) (Z_to_bv 64 v) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13918) fcc None mm (seg_rom psegs)) mo.
  Proof using BLR CEIL CH0 DEP0 LO N1 PL SPAL.
    intros until x31. intros CTX J ROOM V. tree_now CTX CHn. open_actx CTX.
    pose proof (munch_refl [(buf + off, buf + len); (PB, PB + 64)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    ustore_at buf off (buf + off + j) j (wb v) ltac:(symmetry; apply le1_lit8; lia).
    ustore_at buf off (buf + off + j + 1) (j + 1) (wb 0) ltac:(reflexivity).
    step. zstep. replace (dep + 1 + -1) with dep by lia. step. 
    apply evt_done. cbv beta.
    eapply pv_ret1; [exact CEIL'| unfold PV_STACK, PV_BASE; lia| exact N1| exact FR| exact ST| exact MI| exact ERR| | exact FRM| exact FA| | | | exact HP| exact PBS0| | |].
    - eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E1|[E1|[]]]; inversion E1; subst; unfold PDATA_LO, PIMG_HI; lia.
    - eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
      intros a Ha [Hc Hn]. cbn [outside]. split; [|split; [lia| exact I]].
      destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D]. lia.
    - eapply cj_chain_frame; [exact CHn| exact MU| exact WM|].
      intros A' n' Hin. destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' (BLR _ Hin)) as [_ D].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; apply BLR; exact Hin])) 5%nat; intros _ _ _ Q _).
      try rewrite alloc_ceiling_eq in Q. cbn. lia.
    - eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor; [|constructor]].
      + do 4 right. exists buf, len. split; [eapply perm_in_head; exact HP| cbn; lia].
      + right; left. cbn. lia.
    - split; [exact ARR| rewrite !upd_length; exact LEN].
    - split; [lia| split; [exact PN2| exact DEP0]].
    - exists (j + 1). split; [lia|]. split; [lia|]. apply nth_error_upd_same. rewrite ?upd_length. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma arr_end : forall mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    ACTX (dep + 1) mm mo loc Fc fcc errv LB buf len off bs ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13904) fcc None mm (seg_rom psegs)) mo.
  Proof using BLR CEIL CH0 DEP0 LO N1 PL SPAL TP.
    intros until x31. intros CTX. pose proof CTX as (HL & _).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. step. apply evt_done. cbv beta.
    eapply scps_bind. { eapply (actx_ensure HI); [exact PL| exact CEIL| exact LO| exact BLR| exact TP| exact N1| exact CH0| exact CTX| lia]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 LB2 buf2 len2 -> HL2 FC2 PBS2 OUT).
    replace (ret_pc (Z_to_bv 64 0x13910)) with (Z_to_bv 64 0x13910) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
    destruct OUT as [(-> & HB) | (bs2 & -> & CTX2 & ROOM)].
    - step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K. apply evt_done. cbv beta.
      open_fctx FC2.
      eapply pv_epi; [exact CEIL| exact LO| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CHn|].
      exists LB2, buf2, len2, off. split; [exact HL2|]. left. split; [reflexivity|]. exists (dep + 1). split; [exact PBS2| exact HB].
    - (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ (proj1 (proj2 CTX2)))) 5%nat; intros Y1 _ _ Y4 _). try rewrite alloc_ceiling_eq in Y4.
      (nelimp PL 3%nat; intros PL1 PL2 PL3). pose proof CTX2 as (_ & _ & _ & _ & _ & (PN1 & PN2 & PN3) & _).
      step. if_cases K; zify_cond K; [exfalso; lia|]. clear K. step. apply evt_done. cbv beta.
      replace (buf2 + off) with (buf2 + off + 0) by lia.
      eapply pv_close; [exact CTX2| lia| lia| lia].
  Qed.

  Ltac pack_actx HL HP PBS0 ARR LEN FR ST ERR MI CJ FRM FA PVA := split; [exact HL|]; split; [exact HP|]; split; [exact PBS0|]; split; [exact ARR|];
    split; [first [exact LEN | rewrite ?upd_length; exact LEN]|]; split; [split; [lia| split; [lia|lia]]|];
    split; [exact FR|]; split; [exact ST|]; split; [exact ERR|]; split; [exact MI|]; split; [exact CJ|]; split; [exact FRM|]; split; [exact FA| exact PVA].

  (* [comment removed for export] *)
  Lemma arr_iter : forall (kk : nat) (d : nat) (c : Z) (Bc : list cblock) mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31,
    (length Bc <= kk)%nat -> (d < n)%nat -> cj_chain CJ_PRINTABLE m d c Bc -> c <> 0 -> (forall b, In b Bc -> In b B) ->
    ACTX (dep + 1) mm mo loc Fc fcc errv LB buf len off bs ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 c) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 2) (Z_to_bv 64 44) (Z_to_bv 64 32) x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x138a4) fcc None mm (seg_rom psegs)) mo.
  Proof.
    induction kk as [|kk IH]; intros until x31; intros LENB Dlt CHc CNZ SUB CTX.
    { exfalso. pose proof (cj_chain_head_block _ _ _ _ _ CHc CNZ) as HIN. destruct Bc; [destruct HIN| cbn in LENB; lia]. }
    pose proof CTX as (HL0 & _). pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
    (nelim (cj_chain_cons_inv _ _ _ _ _ CHc CNZ) 24%nat; intros d0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bcc Bn Ed ND TY _ SV SK CHC CHN EBc).
    (* [comment removed for export] *)
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL0|].
    step. step. step. apply evt_done. cbv beta.
    eapply scps_bind.
    { eapply (actx_rec HI); [exact PL| exact CEIL| exact LO| exact BLR| exact TP| exact N1| exact CH0| exact SPAL| apply REC; exact Dlt| exact Dlt| exact CTX| lia| exact CHc| exact CNZ| exact SUB]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 27%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fc' fcc' m2 errv2 LB2 buf2 len2 off2 -> HL2 FC2 OUT)
.
    replace (ret_pc (Z_to_bv 64 0x138b0)) with (Z_to_bv 64 0x138b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
    destruct OUT as [(-> & dep' & PBS2 & HB) | (-> & bs2 & CTX2 & NUL2)].
    { step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K. apply evt_done. cbv beta. open_fctx FC2.
      eapply pv_epi; [exact CEIL| exact LO| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CHn|].
      exists LB2, buf2, len2, off2. split; [exact HL2|]. left. split; [reflexivity|]. exists dep'. split; [exact PBS2| exact HB]. }
    step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    (* [comment removed for export] *)
    pose proof CTX2 as (_ & HP2 & PBS2 & _ & _ & (PN1 & PN2 & PN3) & _).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HP2)) 5%nat; intros Y1 _ _ Y4 _). try rewrite alloc_ceiling_eq in Y4.
    (nelimp PL 3%nat; intros PL1 PL2 PL3).
    step. step. if_cases K; zify_cond K; [exfalso; lia|]. clear K. step. zstep. step.
    eapply evt_cut. { eapply (actx_strlen HI); [exact N1| exact CTX2| exact NUL2]. }
    cbv beta. intros ms3 PO. clear PBS2.
    (nelim PO 22%nat; intros k t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 errv3 -> CTX3 K0 K1 KN).
    replace (ret_pc (Z_to_bv 64 0x138c8)) with (Z_to_bv 64 0x138c8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim CTX3 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA). unfold PERRNO in ERR.
    pose proof (munch_refl [(PB, PB + 64)] m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    zstep. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
    pose proof (lh_frame HI _ _ _ m4 _ _ HL MU WM ltac:(constructor; [right; left; cbn; lia| constructor])) as HL4.
    pose proof (CJST_frame _ _ m4 CJ MU WM ltac:(unfold PDATA_LO, PIMG_HI; intros lo' hi' [E1|[]]; inversion E1; subst; lia)) as CJ4.
    assert (PVA4 : pv_agree LR (bv_unsigned sp) PB m m4) by (eapply pv_agree_trans; [exact PVA| eapply pv_agree_hole; [exact MU| exact WM| lia| lia]]).
    clear MU WM HL CJ PVA. rename HL4 into HL. rename CJ4 into CJ. rename PVA4 into PVA.
    assert (CTX4 : ACTX (dep + 1) m4 mo2 loc Fc' fcc' errv3 LB2 buf2 len2 (k + off2) bs2) by (pack_actx HL HP PBS0 ARR LEN FR ST ERR MI CJ FRM FA PVA).
    (* [comment removed for export] *)
    pose proof (actx_node HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PL CEIL LO BLR _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX4 ND (node_cells_size _ _ _ _ _ _ _ _ _ _) ltac:(apply SUB; rewrite EBc; left; reflexivity)) as NDn.
    unfold node_cells in NDn.
    step. unfold wz. step. if_cases Knx; zify_cond Knx.
    { apply evt_done. cbv beta. eapply arr_end. exact CTX4. }
    step. zstep. zstep. step. step.
    (* [comment removed for export] *)
    set (fz := bv_unsigned (sx32 fw) <? 1) in *.
    assert (FZ : Z.lxor (Z.b2z fz) 3 = 3 - Z.b2z fz /\ 0 <= Z.b2z fz <= 1) by (destruct fz; split; reflexivity || (cbn; lia)).
    destruct FZ as [EFZ RFZ]. rewrite EFZ.
    apply evt_done. cbv beta.
    eapply scps_bind. { eapply (actx_ensure HI); [exact PL| exact CEIL| exact LO| exact BLR| exact TP| exact N1| exact CH0| exact CTX4| lia]. }
    cbv beta. intros ms5 mo5 PO. clear HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA NDn CTX4.
    (nelim PO 25%nat; intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x m5 errv5 LB5 buf5 len5 -> HL5 FC5 PBS5 OUT5).
    replace (ret_pc (Z_to_bv 64 0x138ec)) with (Z_to_bv 64 0x138ec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL5|].
    destruct OUT5 as [(-> & HB) | (bs5 & -> & CTX5 & ROOM5)].
    { step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K. apply evt_done. cbv beta. open_fctx FC5.
      eapply pv_epi; [exact CEIL| exact LO| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CHn|].
      exists LB5, buf5, len5, (k + off2). split; [exact HL5|]. left. split; [reflexivity|]. exists (dep + 1). split; [exact PBS5| exact HB]. }
    clear FC5 PBS5.
    pose proof (actx_node HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PL CEIL LO BLR _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX5 ND (node_cells_size _ _ _ _ _ _ _ _ _ _) ltac:(apply SUB; rewrite EBc; left; reflexivity)) as NDn.
    unfold node_cells in NDn.
    (nelim CTX5 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA). unfold PERRNO in ERR.
    (nelim PN 3%nat; intros PN1' PN2' PN3').
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros Z1 _ _ Z4 Z5). try rewrite alloc_ceiling_eq in Z4. unfold PIMG_LO, PIMG_HI in Z5.
    assert (CIN : In (c, 64) B) by (apply SUB; rewrite EBc; left; reflexivity).
    destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP c 64 (BLR _ CIN)) as [_ CD].
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; apply BLR; exact CIN])) 5%nat; intros _ _ _ C4' _). try rewrite alloc_ceiling_eq in C4'.
    step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    pose proof (munch_refl [(buf5 + (k + off2), buf5 + len5); (PB, PB + 64)] m5) as MU. pose proof (wmono_refl psegs m5) as WM.
    ustore_at buf5 (k + off2) (buf5 + (k + off2)) 0 (wb 44) ltac:(reflexivity).
    step.
    (* [comment removed for export] *)
    assert (JN : forall mq (bsq : list byte) x11q,
      u8arr psegs mq buf5 bsq -> Z.of_nat (length bsq) = len5 ->
      munch [(buf5 + (k + off2), buf5 + len5); (PB, PB + 64)] m5 mq -> wmono psegs m5 mq -> mem_inv psegs mq ->
      rw_cells psegs mq PB [C8 (Z_to_bv 64 buf5); C8 (Z_to_bv 64 len5); C8 (Z_to_bv 64 (k + off2)); C8 (Z_to_bv 64 (dep + 1)); C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 86816); C8 (Z_to_bv 64 86496); C8 (Z_to_bv 64 93068)] ->
      PVFRAME mq loc -> stk psegs mq lo SPF -> rw_cells psegs mq 210924 [C4 errv5] ->
      rw_cells psegs mq c [C8 (Z_to_bv 64 nx); C8 pv; C8 (Z_to_bv 64 ch); C4 (Z_to_bv 64 ty); C4 p1; C8 (Z_to_bv 64 vs); C4 vi; C4 p2; C8 vd; C8 (Z_to_bv 64 ky)] ->
      evt psegs (fun ms' => SCPS psegs POST ms' mo5)
        (MS (mkR (Z_to_bv 64 0x138ec) (Z_to_bv 64 SPF) gp tp t0x t1x t2x (Z_to_bv 64 PB) (Z_to_bv 64 c) (Z_to_bv 64 (buf5 + (k + off2))) x11q a2x a3x a4x a5x a6x a7x
                 (Z_to_bv 64 2) (Z_to_bv 64 44) (Z_to_bv 64 32) (Z_to_bv 64 (Z.b2z fz)) x22 s7 s8 s9 s10 s11 t3x t4x t5x t6x)
            Fc' (Z_to_bv 64 0x1388c) fcc' None mq (seg_rom psegs))).
    { intros mq bsq x11q ARRq LENq MUq WMq MIq PBSq FRq STq ERRq NDq.
      step. step. zstep. zstep. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m7 end.
      pose proof (lh_frame HI _ _ _ m7 _ _ HL MUq WMq) as HL7.
      step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
      apply evt_done. cbv beta.
      eapply (IH d nx Bn); [ rewrite EBc in LENB; cbn in LENB; rewrite !length_app in LENB; lia | lia | rewrite <- Ed in CHN; exact CHN | lia
                            | intros b Hb; apply SUB; rewrite EBc; right; rewrite !in_app_iff; right; right; right; exact Hb |].
      split. { apply HL7. constructor; [| constructor; [right; left; cbn; lia| constructor]]. do 4 right. exists buf5, len5. split; [eapply perm_in_head; exact HP| cbn; lia]. }
      split; [exact HP|]. split; [exact PBSq|]. split; [exact ARRq|]. split; [exact LENq|]. split; [split; [lia| split; [lia| lia]]|].
      split; [exact FRq|]. split; [exact STq|]. split; [exact ERRq|]. split; [exact MIq|]. split.
      { eapply CJST_frame; [exact CJ| exact MUq| exact WMq|]. unfold PDATA_LO, PIMG_HI. intros lo' hi' [E1|[E1|[]]]; inversion E1; subst; lia. }
      split; [exact FRM|]. split; [exact FA|].
      eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MUq| exact WMq|].
      intros a Ha [Hc Hn]. cbn [outside]. split; [|split; [lia| exact I]].
      destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D]. lia. }
    step. if_cases Kf; zify_cond Kf.
    - (* [comment removed for export] *)
      assert (Efz : fz = false) by (subst fz; apply Z.ltb_ge; pose proof (bv_unsigned_in_range 64 (sx32 fw)); lia). rewrite Efz in *. cbn [Z.b2z] in *.
      zstep. ustore_at buf5 (k + off2) (buf5 + (k + off2) + 1) 1 (wb 32) ltac:(reflexivity).
      ustore_at buf5 (k + off2) (buf5 + (k + off2) + 2) 2 (wb 0) ltac:(reflexivity).
      eapply JN; [exact ARR| rewrite !upd_length; exact LEN| exact MU| exact WM| exact MI| exact PBS0| exact FR| exact ST| exact ERR| exact NDn].
    - assert (Efz : fz = true) by (subst fz; apply Z.ltb_lt; pose proof (bv_unsigned_in_range 64 (sx32 fw)); lia). rewrite Efz in *. cbn [Z.b2z] in *.
      zstep. step. ustore_at buf5 (k + off2) (buf5 + (k + off2) + 1) 1 (wb 0) ltac:(reflexivity).
      eapply JN; [exact ARR| rewrite !upd_length; exact LEN| exact MU| exact WM| exact MI| exact PBS0| exact FR| exact ST| exact ERR| exact NDn].
  Qed.

  (* [comment removed for export] *)
  Lemma arr_open : forall mm mo loc Fc fcc errv LB buf len off bs (d0 : nat) (ch : Z) (Bcc : list cblock)
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    ACTX dep mm mo loc Fc fcc errv LB buf len off bs -> off + 2 <= len -> n = S d0 -> cj_chain CJ_PRINTABLE m d0 ch Bcc -> (forall b, In b Bcc -> In b B) ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 ch) (Z_to_bv 64 buf) (Z_to_bv 64 off) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x13848) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX ROOM Ed CHC SUBC. open_actx CTX.
    pose proof (munch_refl [(buf + off, buf + len); (PB, PB + 64)] mm) as MU. pose proof (wmono_refl psegs mm) as WM.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. step.
    ustore_at buf off (buf + off) 0 (wb 91) ltac:(reflexivity).
    step. step. zstep. zstep. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
    pose proof (lh_frame HI _ _ _ m4 _ _ HL MU WM) as HL4.
    assert (CTX4 : ACTX (dep + 1) m4 mo loc Fc fcc errv LB buf len (off + 1) (upd bs (Z.to_nat (off + 0)) (wb 91))).
    { split. { apply HL4. constructor; [| constructor; [right; left; cbn; lia| constructor]]. do 4 right. exists buf, len. split; [eapply perm_in_head; exact HP| cbn; lia]. }
      split; [exact HP|]. split; [exact PBS0|]. split; [exact ARR|]. split; [rewrite upd_length; exact LEN|]. split; [split; [lia| split; [lia| lia]]|].
      split; [exact FR|]. split; [exact ST|]. split; [exact ERR|]. split; [exact MI|]. split.
      { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. unfold PDATA_LO, PIMG_HI. intros lo' hi' [E1|[E1|[]]]; inversion E1; subst; lia. }
      split; [exact FRM|]. split; [exact FA|].
      eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
      intros a Ha [Hc Hn]. cbn [outside]. split; [|split; [lia| exact I]].
      destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D]. lia. }
    (nelimp (cj_chain_ptr_range _ _ _ _ _ CHC) 3%nat; intros CR1 _ CR3).
    step. if_cases Kch; zify_cond Kch.
    - apply evt_done. cbv beta. eapply arr_end. exact CTX4.
    - step. step. step. step. apply evt_done. cbv beta.
      eapply (arr_iter (length Bcc) d0 ch Bcc); [lia| lia| exact CHC| exact Kch| exact SUBC| exact CTX4].
  Qed.

  (* [comment removed for export] *)
  Lemma pv_arr : forall mm mo loc Fc fcc errv LB buf len off bs
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    ACTX dep mm mo loc Fc fcc errv LB buf len off bs ->
    SCPS psegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 p) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x134a0) fcc None mm (seg_rom psegs)) mo.
  Proof.
    intros until x31. intros CTX. pose proof CTX as CTX0.
    (nelim (cj_chain_cons_inv _ _ _ _ _ CH0 PNZ) 24%nat; intros d0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bcc Bn Ed ND TY _ SV SK CHC CHN EB).
    pose proof (actx_node HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PL CEIL LO BLR _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ND (node_cells_size _ _ _ _ _ _ _ _ _ _) ltac:(rewrite EB; left; reflexivity)) as NDn.
    unfold node_cells in NDn.
    pose proof (lheap_perm_apart HI _ _ _ _ _ _ _ (proj1 CTX) (proj1 (proj2 CTX)) p 64 (BLR _ ltac:(rewrite EB; left; reflexivity))) as [_ PD].
    (nelimp (lh_block_range HI _ _ _ _ _ _ (proj1 CTX) ltac:(eapply Permutation_in; [exact (proj1 (proj2 CTX))| right; apply BLR; rewrite EB; left; reflexivity])) 5%nat; intros _ _ _ P4 _). try rewrite alloc_ceiling_eq in P4.
    tree_now CTX0 CHt.
    open_actx CTX.
    assert (E1 : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
    assert (LO' : lo <= bv_unsigned sp - PV_STACK n) by (unfold PV_STACK, PV_BASE; lia).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    step. step. zstep. zstep. if_cases Koff; zify_cond Koff.
    { apply evt_done. cbv beta.
      eapply pv_ret0; [exact CEIL'| exact LO'| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CHt| exact HL| exact PBS0| right; split; [lia| exact HP]]. }
    step. unfold wz. zstep. zstep. if_cases Kroom; zify_cond Kroom.
    { apply evt_done. cbv beta. eapply arr_open with (len := len); [exact CTX0| lia| exact Ed| exact CHC| rewrite EB; intros b Hb; right; rewrite !in_app_iff; right; right; left; exact Hb]. }
    step. step. if_cases Kna; zify_cond Kna; [exfalso; apply Kna; reflexivity|]. clear Kna.
    (* [comment removed for export] *)
    assert (GROW : forall ns x11',
      off + 2 <= ns < 2^31 ->
      evt psegs (fun ms' => SCPS psegs POST ms' mo)
        (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 ch) (Z_to_bv 64 buf) x11' (Z_to_bv 64 len) (Z_to_bv 64 (len + -1)) x14 x15 x16 x17 (Z_to_bv 64 ns) x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            Fc (Z_to_bv 64 0x136a8) fcc None mm (seg_rom psegs))).
    { intros ns x11' NS.
      step. step. if_cases Kd; zify_cond Kd; [exfalso; lia|]. clear Kd.
      step. step.
      replace (ret_pc (Z_to_bv 64 93068)) with (wz PREALLOC) by (unfold wz, PREALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply evt_done. cbv beta.
      eapply scps_bind.
      { eapply (lh_realloc HI) with (lo := lo) (A := buf) (k := len) (n := ns) (old := bs); rewrite ?E1;
          first [ exact HL | eapply perm_in_head; exact HP | exact (proj1 ARR) | exact ST | exact ERR | exact MI | exact TP | reflexivity | unfold RMALLOC_STACK; lia ]. }
      cbv beta. intros ms2 mo2 PO.
      (nelim PO 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 -> MI2 ST2 ERR2 RES)
.
      rewrite E1 in ST2. unfold PERRNO in ERR2.
      replace (ret_pc (Z_to_bv 64 0x136b8)) with (Z_to_bv 64 0x136b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct RES as [(-> & HL2 & PR2) | (B' & junk & -> & CR & HB & HL2 & PR2 & BLK)].
      - rewrite E1 in PR2. unfold wz.
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PBS0; [| left; lia].
        apply (CJST_pres _ _ _ _ PR2) in CJ.
        apply (cj_chain_pres _ _ _ _ _ _ _ _ CHt) in PR2 as CHt2. 2:{ intros b Hb. eapply Permutation_in; [exact HP| right; apply BLR; exact Hb]. }
        assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
        { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_alloc; [exact PR2| lia|].
          intros b Hb. eapply Permutation_in; [exact HP| right; exact Hb]. }
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. if_cases K0; zify_cond K0; [exfalso; apply K0; reflexivity|]. clear K0.
        step. apply evt_done. cbv beta.
        eapply pv_fail_free; [split; [exact PL1| split; [exact PL2| exact PL3]]| exact CEIL'| exact LO'| exact TP| exact SPhi| exact N1| exact FR| exact ST2| exact MI2| exact ERR2| exact CJ| exact FRM| exact FA| exact PVA2| exact CHt2| exact BLR| exact HL2| exact HP| exact PBS0].
      - rewrite E1 in PR2. unfold wz.
        (nelim CR 5%nat; intros CR1 CR2 CR3 CR4 CR5). try rewrite alloc_ceiling_eq in CR4. unfold PIMG_LO, PIMG_HI in CR5.
        pose proof (perm_cb_remove _ _ _ _ HP (lh_nodup HI _ _ _ _ HL)) as HPr.
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PBS0; [| left; lia].
        apply (CJST_pres _ _ _ _ PR2) in CJ.
        apply (cj_chain_pres _ _ _ _ _ _ _ _ CHt) in PR2 as CHt2. 2:{ intros b Hb. eapply Permutation_in; [exact HPr| apply BLR; exact Hb]. }
        assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
        { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_alloc; [exact PR2| lia|].
          intros b Hb. eapply Permutation_in; [exact HPr| exact Hb]. }
        clear PVA PR2 MI ST ERR HL ARR CHt.
        rewrite (Z.min_l len ns) in BLK by lia.
        (nelim (u8arr_of_two_CB _ _ _ _ _ _ BLK) 3%nat; intros ARR2 La Lb).
        assert (HP2 : Permutation ((B', ns) :: LR) ((B', ns) :: cb_remove buf LB)) by (apply perm_skip; exact HPr).
        pose proof (munch_refl [(PB, PB + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
        step. step. step.
        apply evt_done. cbv beta.
        eapply arr_open with (buf := B') (len := ns); [| lia| exact Ed| exact CHC| rewrite EB; intros b Hb; right; rewrite !in_app_iff; right; right; left; exact Hb].
        split. { eapply (lh_frame HI); [exact HL2| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
        split; [exact HP2|]. split; [exact PBS0|]. split; [exact ARR2|]. split; [rewrite length_app, La, Lb; lia|]. split; [split; [lia| split; [lia| lia]]|].
        split; [exact FR|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split.
        { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E2|[]]. inversion E2; subst. unfold PDATA_LO, PIMG_HI. lia. }
        split; [exact FRM|]. split; [exact FA|].
        eapply pv_agree_trans; [exact PVA2|]. eapply pv_agree_hole; [exact MU| exact WM| lia| lia]. }
    zstep. zstep. if_cases K30; zify_cond K30.
    - zstep. apply GROW. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 in K30 by lia. lia.
    - zstep. zstep. if_cases K31; zify_cond K31.
      + apply evt_done. cbv beta.
        eapply pv_ret0; [exact CEIL'| exact LO'| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CHt| exact HL| exact PBS0| right; split; [lia| exact HP]].
      + step. step. step. apply GROW. rewrite Z.shiftr_div_pow2 in K31 by lia. lia.
  Qed.

End S.

Theorem pv_arr_case : forall HI n, pv_case_at PV_ARR_ENTRY HI n.
Proof.
  unfold pv_case_at, PV_ARR_ENTRY. intros until lo. intros PL CEIL LO TP SPhi N1 BLR SPAL DEPN DEP0 PNZ CH0 REC. intros.
  eapply pv_arr; eassumption.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr psegs ?m B ?buf |- _ =>
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
