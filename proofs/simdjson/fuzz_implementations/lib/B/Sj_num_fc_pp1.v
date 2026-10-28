(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU SjNumN SjNumSwar.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_pm_kit Sj_num_fc_defs Sj_num_fc_pdefs Sj_num_fc_tail Sj_num_fc_k14.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Local Ltac num_abstract_data ::= num_abstract_data_u.

Lemma fcb_recell : forall segs (m : mem) A cs cs',
  cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' WF' EB [[WF HB] HW].
  split; [split; [exact WF' | rewrite EB; exact HB]|].
  rewrite <- (cells_bytes_length cs' WF'), EB, (cells_bytes_length cs WF). exact HW.
Qed.

Lemma fcb_c8z_split : forall segs (m : mem) A pre,
  rw_cells segs m A (pre ++ [C8 (Z_to_bv 64 0)]) -> rw_cells segs m A (pre ++ [C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
Proof.
  intros segs m A pre H. eapply fcb_recell; [ | | exact H].
  - destruct H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [H1 _]. apply cells_wf_app. split; [exact H1|]. cbn. tauto.
  - rewrite !cells_bytes_app. f_equal.
Qed.

Definition FCEINV (E : fcbenv) (mm : mem) (c0 c8 c16 c24 c32 c40 c48 c56 : word) (pnsc : list cell) : Prop :=
  rw_cells bsegs mm (q_spq E) (fcb_spill E c0 c8 c16 c24 c32 c40 c48 c56) /\
  rw_cells bsegs mm (q_spq E + 72) pnsc /\
  (exists jd, rw_cells bsegs mm (q_spq E + 144) [CB 8 jd]) /\
  (exists h0, rw_cells bsegs mm (q_f E) [CB 8 h0]) /\
  (exists jb, rw_cells bsegs mm (q_f E + 32) [CB 504 jb]) /\
  (exists js, rw_cells bsegs mm (q_f E / 8 + 2147450884) [CB 63 js]) /\
  (exists v, rw_cells bsegs mm (q_OUT E) [C8 v]) /\
  bytes_at bsegs mm (q_A E) (q_txt E) /\
  mem_inv bsegs mm /\ munch (fcb_W E) (q_m0 E) mm /\ wmono bsegs (q_m0 E) mm /\ stk bsegs mm (q_lo E) (q_spq E).
Ltac fce_open H :=
  let jd := fresh "jd" in let h0 := fresh "h0" in let jb := fresh "jb" in let js := fresh "js" in let v := fresh "v" in
  destruct H as (SPILL & PNS & (jd & DGC) & (h0 & HDR) & (jb & BIG) & (js & BSH) & (v & OUTC) & TXT & MI & MU & WM & ST);
  unfold fcb_spill in SPILL; unfold fcb_W in MU;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
Lemma FCEINV_of_P : forall E mm c0 c8 c16 c24 c32 c40 c48 c56, FCPINV E mm c0 c8 c16 c24 c32 c40 c48 c56 -> exists jp, FCEINV E mm c0 c8 c16 c24 c32 c40 c48 c56 [CB 72 jp].
Proof. intros E mm c0 c8 c16 c24 c32 c40 c48 c56 (H1 & (jp & H2) & H3). exists jp. split; [exact H1|]. split; [exact H2| exact H3]. Qed.

Definition fcb_ekind (E : fcbenv) (slot : bool) (xs10 c32 : word) : Prop := if slot then c32 = Z_to_bv 64 (q_OUT E) else xs10 = Z_to_bv 64 (q_OUT E).

Definition FCB_ERR1 : list Z := [0xf6d14; 0xf6f2c; 0xf7304; 0xf7b9c; 0xf791c]%Z.
Definition FCB_ERR2 : list Z := [0xf6d24; 0xf6f3c; 0xf7314; 0xf7bac; 0xf792c]%Z.
Notation Z32 := (repeat (Z_to_bv 8 0) 32).
Notation Z27 := (repeat (Z_to_bv 8 0) 27).

Definition fcb_kerr1 (E : fcbenv) (Q : machine_state -> Prop) : Prop :=
  forall ra1, In ra1 FCB_ERR1 -> forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 xF xfc mm c0 c8 c16 c24 c32 c40 c48 c56,
    FCPINV E mm c0 c8 c16 c24 c32 c40 c48 c56 -> frm0 xfc -> fcb_ekind E (ra1 =? 0xf791c)%Z xs10 c32 ->
    evt bsegs Q (FCS E 0x84bc4 (Z_to_bv 64 (ra1)) xt0 xt1 xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) (Z_to_bv 64 (q_spq E + 104)) (Z_to_bv 64 (0)) (Z_to_bv 64 (32)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).

Definition fcb_kerr2 (E : fcbenv) (Q : machine_state -> Prop) : Prop :=
  forall ra2, In ra2 FCB_ERR2 -> forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 xF xfc mm c0 c8 c16 c24 c32 c40 c48 c56 jp je,
    FCEINV E mm c0 c8 c16 c24 c32 c40 c48 c56 [CB 32 jp; CB 32 Z32; CB 8 je] -> frm0 xfc -> fcb_ekind E (ra2 =? 0xf792c)%Z xs10 c32 ->
    evt bsegs Q (FCS E 0x84bc4 (Z_to_bv 64 (ra2)) xt0 xt1 xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) (Z_to_bv 64 (q_spq E + 72)) (Z_to_bv 64 (0)) (Z_to_bv 64 (27)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).

Section FCBPP1.
  Variable E : fcbenv.
  Hypothesis OK : fcb_ok E.
  Hypothesis PV : fcb_prov E.
  Variable Q : machine_state -> Prop.
  Hypothesis K14 : fcb_kf14 E Q.
  Notation A := (q_A E).
  Notation FIRST := (q_FIRST E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).
  Notation f := (q_f E).

  Lemma fcb_err_mid : fcb_kerr2 E Q -> forall ra1, In ra1 FCB_ERR1 -> forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 xF xfc mm c0 c8 c16 c24 c32 c40 c48 c56 jp je,
    FCEINV E mm c0 c8 c16 c24 c32 c40 c48 c56 [CB 32 jp; CB 32 Z32; CB 8 je] -> frm0 xfc -> fcb_ekind E (ra1 =? 0xf791c)%Z xs10 c32 ->
    evt bsegs Q (FCS E ra1 xra xt0 xt1 xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros K2 ra1 HIN. intros until je. intros INV FRM KIND.
    unfold FCB_ERR1 in HIN. cbn [In] in HIN.
    destruct HIN as [<- | [<- | [<- | [<- | [<- | []]]]]]; zstep; zstep; zstep; zstep;
      (eapply evt_eq; [| eapply K2]; [num_st_eq | unfold FCB_ERR2; cbn [In]; repeat (first [left; reflexivity | right]) | exact INV | exact FRM | exact KIND]).
  Qed.

  Lemma fcb_err_tail : forall ra2, In ra2 FCB_ERR2 -> forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 xF xfc mm c0 c8 c16 c24 c32 c40 c48 c56 j5 je,
    FCEINV E mm c0 c8 c16 c24 c32 c40 c48 c56 [CB 27 Z27; CB 5 j5; CB 32 Z32; CB 8 je] -> frm0 xfc -> length j5 = 5%nat -> length je = 8%nat ->
    fcb_ekind E (ra2 =? 0xf792c)%Z xs10 c32 ->
    evt bsegs Q (FCS E ra2 xra xt0 xt1 xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK K14.
    intros ra2 HIN. intros until je. intros INV FRM L5 L8 KIND. fce_open INV. pose proof OK as OK'. fcb_env OK'.
    pose proof (firstn_skipn 4 je) as EJ.
    assert (LA : length (firstn 4 je) = 4%nat) by (rewrite length_firstn; lia).
    assert (LB : length (skipn 4 je) = 4%nat) by (rewrite length_skipn; lia).
    set (ja := firstn 4 je) in *. set (jb0 := skipn 4 je) in *. clearbody ja jb0. subst je.
    apply (fcb_recell _ _ _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 5 j5;
                               C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 4 ja; CB 4 jb0]) in PNS;
      [ | cbn [cells_wf cell_wf]; rewrite L5, LA, LB; repeat split | cbn [cells_bytes cbytes app]; rewrite <- ?app_assoc; reflexivity ].
    unfold FCB_ERR2 in HIN. cbn [In] in HIN.
    destruct HIN as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [Z.eqb Pos.eqb fcb_ekind] in KIND; subst;
      kwalk ltac:(fun pc => lazymatch pc with
        | 0xf8cc0%Z => u_trap_b pc
        | 0xf807c%Z => first [ num_cur_mem ltac:(fun m1 => lazymatch goal with
                                 | P : rw_cells bsegs m1 (q_spq E + 72)%Z (C8 _ :: C8 _ :: C8 ?lm :: _),
                                   SP : rw_cells bsegs m1 (q_spq E) [C8 ?d0; C8 ?d8; C8 ?d16; C8 ?d24; C8 ?d32; C8 ?d40; C8 ?d48; C8 ?d56; C8 _] |- _ =>
                                 assert (INV1 : FCINV E m1 true js d0 d8 d16 d24 d32 d40 d48 d56 0 (Z_to_bv 64 0) lm 0 0 0 0 0 0) by fc_close end);
                               eapply evt_eq; [| eapply K14]; [num_st_eq | exact INV1 | exact FRM | intros C; exfalso; apply C; reflexivity | lia]
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma fcb_9d8 : forall (q IP IL FPT FL tm : Z) c0 c8 c16 c24 c32 c48 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm,
    FCPINV E mm c0 c8 c16 c24 c32 (Z_to_bv 64 IL) c48 (Z_to_bv 64 FPT) -> frm0 xfc -> (-9223372036854775808 <= q < 9223372036854775808)%Z -> sp_pfacts E IP IL FPT FL -> (FIRST <= IP)%Z -> (0 <= tm <= 1)%Z -> (tm <> 0 -> 1 <= bv_unsigned xa2 <= 18446744073709551614)%Z ->
    evt bsegs Q (FCS E 0xf7b40 xra xt0 xt1 xt2 (q_sp E) (Z_to_bv 64 (q_spq E)) (Z_to_bv 64 (tm)) xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 (FL)) (Z_to_bv 64 (q)) (Z_to_bv 64 (q_f E)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (q_S E)) (Z_to_bv 64 (IP)) (Z_to_bv 64 LAST) xs7 xs8 xs9 (Z_to_bv 64 (OUT)) (Z_to_bv 64 (q_f E)) xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK K14.
    intros until mm. intros INV FRM Hq PF HIP HTM HW. fcp_open INV. pose proof OK as OK'. fcb_env OK'.
    assert (SPN : fcb_spans E IP IL FPT FL).
    { destruct PF as ((P1 & P2 & P3) & _ & [[-> ->] | [(-> & F1 & F2 & _) _]]); unfold fcb_spans; [split; [lia|]; split; [lia|]; split; [lia|]; left; reflexivity|].
      split; [lia|]. split; [lia|]. split; [lia|]. right. lia. }
    apply (rw_cells_split_CB bsegs mm _ [] 72 jp [] [8; 8; 8; 1; 1; 1; 5; 8; 8; 8; 8; 8]%nat) in PNS; [| reflexivity]. cbn [mk_CB_cells app] in PNS.
    repeat match type of PNS with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in PNS; clearbody j end.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0xf8cc0%Z => u_trap_b pc
      | 0xf807c%Z => first [
          lazymatch goal with
          | P : rw_cells bsegs ?m1 (q_spq E + 72)%Z [?a0; ?a1; ?a2; C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.b2z ?b)))); ?a4; C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 tm)));
                                                      ?a6; ?a7; ?a8; ?a9; ?a10; C8 (Z_to_bv 64 0)],
            SP : rw_cells bsegs ?m1 (q_spq E) [C8 ?d0; C8 ?d8; C8 ?d16; C8 ?d24; C8 ?d32; C8 ?d40; C8 ?d48; C8 ?d56; C8 _] |- _ =>
              assert (NBR : (0 <= Z.b2z b <= 1)%Z) by (destruct b; cbn; lia);
              rewrite (unsigned_lit (Z.b2z b)), (unsigned_lit tm) in P by lia;
              apply (fcb_c8z_split bsegs m1 _ [a0; a1; a2; C1 (Z_to_bv 8 (Z.b2z b)); a4; C1 (Z_to_bv 8 tm); a6; a7; a8; a9; a10]) in P; cbn [app] in P;
              assert (INV1 : FCINV E m1 true js d0 d8 d16 d24 d32 d40 d48 d56 q xa2 xs9 (Z.b2z b) tm IP IL FPT FL) by fc_close
          end;
          eapply evt_eq; [| eapply K14]; [num_st_eq | exact INV1 | exact FRM | intros C; split; [exact SPN | exact (HW C)] | lia]
        | fail 100 "cut" pc ]
      end).
  Qed.
End FCBPP1.
