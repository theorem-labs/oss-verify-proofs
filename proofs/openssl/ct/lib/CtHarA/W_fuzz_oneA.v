(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Stdio Prog LibProg ProgG CtSizes CtWire CtTime CtModel ApBase ApState ApErr ApParse ApBridge.
From Stdlib Require Import ZArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs D_libiface I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit ApErrKitA W_get_objectA W_err_set_debugA Fr_ossl_crypto_new_ex_data_ex Fr_CRYPTO_free_ex_data W_ex_dataA W_ex_dataA2 CtFuzzStmtA PzBitsA W_check_tlenA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep W_sk_leaves SctStmt W_o2i_sct_list.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA SctStmtA2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctWire.                (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import PrnStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarA Require Import HarStmtA Fr_FuzzerTestOneInput HarKitA W_bio_nullA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

(* [comment removed for export] *)
Local Notation E_jmp := (E_LLVMFuzzerTestOneInput_1ef060 : uk_tail 0x1f40f0 0x1f4160).
Local Notation E_d2i := (E_FuzzerTestOneInput_1ef1f4 : uk_call 0x1f4160 0x1f4288 0x337020).
Local Notation E_bnew := (E_FuzzerTestOneInput_1ef20c : uk_call 0x1f4160 0x1f42a0 0x237894).
Local Notation E_prn := (E_FuzzerTestOneInput_1ef234 : uk_call 0x1f4160 0x1f42c8 0x338364).
Local Notation E_bfree := (E_FuzzerTestOneInput_1ef23c : uk_call 0x1f4160 0x1f42d0 0x2378bc).
Local Notation E_i2d := (E_FuzzerTestOneInput_1ef24c : uk_call 0x1f4160 0x1f42e0 0x3372c4).
Local Notation E_cfree := (E_FuzzerTestOneInput_1ef260 : uk_call 0x1f4160 0x1f42f4 0x1fd334).
Local Notation E_free := (E_FuzzerTestOneInput_1ef26c : uk_call 0x1f4160 0x1f4300 0x3376b8).
Local Notation E_clr := (E_FuzzerTestOneInput_1ef270 : uk_call 0x1f4160 0x1f4304 0x1fe828).

(* [comment removed for export] *)
Definition HARA_D2I : Z := 0x1f4280.     (* [comment removed for export] *)
Definition HARA_RET1 : Z := 0x1f4288.    (* [comment removed for export] *)
Definition HARA_PRN : Z := 0x1f42a8.     (* [comment removed for export] *)
Definition HARA_BFREE : Z := 0x1f42c8.   (* [comment removed for export] *)
Definition HARA_I2D : Z := 0x1f42d0.     (* [comment removed for export] *)
Definition HARA_CFREE : Z := 0x1f42e0.   (* [comment removed for export] *)
Definition HARA_FREE : Z := 0x1f42f4.    (* [comment removed for export] *)
Definition HARA_CLR : Z := 0x1f4300.     (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma BIO_s_null_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> SEGTOP_A <= lo -> lo <= bv_unsigned sp - 16 ->
  evt ctasegs (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NULL_METHOD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_S_NULL_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST MI SLO LO. unfold BIO_S_NULL_A, NULL_METHOD, SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  carve_frame 16%nat ST. do 4 zstep. zstep. zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
Definition d2i_wire_factsA : Prop :=
  forall (f0 : Z) (r0 p0 g0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : word) (Σ0 : rts RT) (OW0 LB0 : list block) (E0 : ap_env) (lo0 : Z) (m0 : mem) (K0 : list block) (CST0 : Z)
         (adr0 : bptr -> Z) (D0 len0 PIN0 : Z) (ok : option (skr bptr)) (st' : ap_st bptr) (Σ' : rts RT) (ms' : machine_state),
    @d2i_list_postA2 (push AR f0 1) r0 p0 g0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 Σ0 OW0 LB0 E0 lo0 m0 K0 CST0 adr0 D0 len0 PIN0 ok st' Σ' ms' ->
    match ok with Some k => 3 * zlength (sk_items k) + 2 <= MAX_SCT_LIST_SIZE /\ 2 + sk_wire k <= MAX_SCT_LIST_SIZE | None => True end.
Lemma D2I_WIRE : d2i_wire_factsA.
Proof.
  unfold d2i_wire_factsA. intros until ms'. intros PO.
  destruct PO as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & OW2 & bo2 & adr2 & NEW & _ & _ & _ & _ & _ & _ & _ & _ & RES2).
  destruct ok as [k|]; [| exact I]. destruct RES2 as (_ & _ & _ & N3 & WIRE2). split; [exact N3| exact WIRE2].
Qed.

Section Act.
  (* [comment removed for export] *)
  Variables (STK_D2I : Z) (CST_D2I : Z -> Z) (FRM_D2I : Z) (STK_PRN : Z) (CST_PRN : Z -> Z) (FRM_PRN : Z) (STK_I2D : Z) (CST_I2D : Z -> Z) (FRM_I2D : Z) (STK_FREE : Z).
  Hypothesis BUD : har_budgetsA STK_D2I CST_D2I FRM_D2I STK_PRN CST_PRN FRM_PRN STK_I2D CST_I2D FRM_I2D STK_FREE.
  Hypothesis HYPS : @har_hypsA AR UK STK_D2I CST_D2I FRM_D2I STK_PRN CST_PRN FRM_PRN STK_I2D CST_I2D FRM_I2D STK_FREE.
  (* [comment removed for export] *)
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (Σ : rts RT) (ls : ap_ls bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo D : Z) (d : list Z).
  Hypothesis PRE : ap_preA Σ (st_of_ls ls) m OW LB E bo sp lo CT_FUZZ_STACK_A (CT_FUZZ_COST_A (zlength d)) CT_FUZZ_FRAMES_A.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) nil.
  Hypothesis CTX : uk_ctx CT_FUZZ_ENTRY_A [bv_unsigned ra].
  Hypothesis PAY : payload_okA m LB D d.
  (* [comment removed for export] *)
  Variables (Σ1 : rts RT) (m3 : mem) (f spa : Z) (g : nat) (junk gj j0 : list byte).
  Hypothesis HEAP3 : @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m3.
  Hypothesis FRESH : forall b, In b (OW ++ LB) -> off_fr f 1 b.
  Hypothesis GEO : @fr_geo (push AR f 1) f 1.
  Hypothesis CR1 : rt_credit RT Σ1 = rt_credit RT Σ - 1.
  Hypothesis EL1 : rt_live RT Σ1 = rt_live RT Σ.
  Hypothesis ST3 : stk ctasegs m3 lo spa.
  Hypothesis MI3 : mem_inv ctasegs m3.
  Hypothesis AGF : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3.
  Hypothesis SPA32 : spa mod 32 = 0.
  Hypothesis SPAL : bv_unsigned sp - 112 <= spa.
  Hypothesis SPAH : spa <= bv_unsigned sp - 96.
  Hypothesis GSZ : Z.of_nat g = bv_unsigned sp - spa - 32.
  Hypothesis SAVJ : junk = gj ++ cells_bytes [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1].
  (* [comment removed for export] *)
  Variables (qb qd : bptr).
  Hypothesis HEAPX : @BnHeapA.AHEAP (push AR f 1) Σ1 OW (fto_pbs f qb qd ++ LB) m3.
  Hypothesis QBF : ~ In qb (map blk_id (OW ++ LB)).
  Hypothesis QDF : ~ In qd (map blk_id (OW ++ LB)).
  Hypothesis QBD : qb <> qd.

  Let pbs := fto_pbs f qb qd.
  Let st0 := st_of_ls ls.
  (* [comment removed for export] *)
  Let BSTK := CT_FUZZ_STACK_A - 96 - 16.
  Let BCOST := CT_FUZZ_COST_A (zlength d) - 1.
  Let BFRM := CT_FUZZ_FRAMES_A - 1.
  (* [comment removed for export] *)
  Let FQ : Z * ap_st bptr -> rts RT -> machine_state -> Prop := ct_top_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ LB E bo lo m D d.

  (* [comment removed for export] *)
  Definition bst (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s3v s4v s5v x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (mx : mem) (pc : Z) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3v s4v s5v (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 (-8)) s9 s10 s11 x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None mx (seg_rom ctasegs).

  (* [comment removed for export] *)
  Definition hinv (Σk : rts RT) (stX : ap_st bptr) (mk : mem) (OWk : list block) (bok : Z * Z) (NEWk : list block) (spent : Z) : Prop :=
    @ap_preA (push AR f 1) Σk stX mk OWk (NEWk ++ pbs ++ LB) E bok (Z_to_bv 64 spa) lo BSTK (BCOST - spent) BFRM
    /\ agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m mk
    /\ ax_pres LB spa LIBW_A m3 mk
    /\ rt_credit RT Σ1 - spent <= rt_credit RT Σk /\ 0 <= spent
    /\ (forall b, In b NEWk -> ~ In (blk_id b) (map blk_id (OWk ++ pbs ++ LB)))
    /\ Forall (@lbokA (push AR f 1)) NEWk
    /\ rw_cells ctasegs mk spa [CB 8 j0; C8 (Z_to_bv 64 f); CB g junk]
    /\ rw_cells ctasegs mk (bv_unsigned sp + -16) [C8 s0; C8 ra].
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma base_facts :
    0 <= bv_unsigned sp < 2 ^ 64 /\ SEGTOP_A <= ACEIL /\ SHHI <= ACEIL /\ ACEIL + STACK_WIN <= USTACK_TOP /\ ACEIL <= lo /\ 0 <= lo
    /\ lo <= bv_unsigned sp - CT_FUZZ_STACK_A /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0
    /\ 0 < f /\ f mod 64 = 0 /\ f + 128 <= ACEIL /\ SEGTOP_A <= f /\ (f + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= f)
    /\ bv_unsigned (Z_to_bv 64 spa) = spa /\ bv_unsigned (Z_to_bv 64 f) = f /\ CT_FUZZ_COST_A (zlength d) <= rt_credit RT Σ.
  Proof.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
    assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
    pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G4, G5.
    unfold BnHeapA.ACEIL in G3. cbn [ar_SP0 push amb] in G3. change (@ar_SP0 AR - STACK_WIN) with (@BnHeapA.ACEIL AR) in G3.
    assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa).
    { apply unsigned_lit. unfold CT_FUZZ_STACK_A, FUZZ_STACK in LOSP. clear - C1 CEIL LOSP SPAL SPAH SPR LO0. alia. }
    assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 C3; alia).
    split; [exact SPR|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact CEIL|]. split; [exact LO0|]. split; [exact LOSP|].
    split; [exact TOP|]. split; [exact AL16|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
    split; [exact ESPA|]. split; [exact Ef|]. clear - CRED. lia.
  Qed.

  Lemma OFFLB : forall b, In b LB -> off_fr f 1 b.
  Proof. intros b Hb. apply FRESH. apply in_or_app. right. exact Hb. Qed.

  Lemma csb : forall x, client_static x -> x < SEGTOP_A.
  Proof. intros x [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. unfold SEGTOP_A. clear - Hin Hlh. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia. Qed.

  (* [comment removed for export] *)
  Lemma uw_callee : forall mk,
    agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m mk -> rw_cells ctasegs mk (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    uw_chain USTACK_TOP mk spa (bv_unsigned sp) [bv_unsigned ra].
  Proof.
    intros mk AGS FRH. pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & _).
    eapply (uw_call m mk spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) nil);
      [exact UW| exact AGS| reflexivity| clear - SPAH; lia| clear - AL16; Z.div_mod_to_equations; lia| clear - TOP; unfold USTACK_TOP in *; lia
      | apply bv_unsigned_in_range| rewrite !Z_to_bv_bv_unsigned; cbn [app]; exact FRH].
  Qed.

  (* [comment removed for export] *)
  Lemma ctx_callee : forall (R G : Z) (pc : Z), uk_call 0x1f4160 R G -> bv_unsigned (Z_to_bv 64 R) = R -> uk_ctx G (bv_unsigned (Z_to_bv 64 R) :: [bv_unsigned ra]).
  Proof. intros R G pc ED ER. rewrite ER. exact (uk_ctx_call _ _ _ _ ED (uk_ctx_tail _ _ _ E_jmp CTX)). Qed.

  (* [comment removed for export] *)
  Lemma axw : forall a, ax_client LB (bv_unsigned sp) LIBW_A a ->
    aclient_addr (OW ++ LB) (bv_unsigned sp) a
    /\ (forall (L : list block) (X : list (Z * Z)), (forall x, rin_ivs X x -> f <= x < f + 128) -> ax_client (L ++ pbs ++ LB) spa (X ++ LIBW_A) a)
    /\ (forall (L : list block) SP, SP <= bv_unsigned sp -> aclient_addr (L ++ LB) SP a)
    /\ ~ (f <= a < f + 128).
  Proof.
    intros a [HX Hc]. pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0).
    pose proof PRE as (HEAP & _).
    assert (CSB : forall x, client_static x -> x < SEGTOP_A).
    { intros x [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. unfold SEGTOP_A. clear - Hin Hlh. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia. }
    assert (NF : ~ (f <= a < f + 128)).
    { destruct Hc as [H1|[H1|(b & Hb & Hr)]].
      - unfold CT_FUZZ_STACK_A, FUZZ_STACK in LOSP. clear - H1 G3 CEIL LOSP. unfold BnHeapA.ACEIL in *. lia.
      - pose proof (CSB a H1). clear - H G4. lia.
      - pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. clear - Hr O. lia. }
    split; [| split; [| split; [| exact NF]]].
    - destruct Hc as [H1|[H1|(b & Hb & Hr)]]; [left; exact H1| right; left; exact H1| right; right; exists b; split; [apply in_or_app; right; exact Hb| exact Hr]].
    - intros L X HXf. split.
      + intros HR. apply rin_ivs_app in HR. destruct HR as [HR|HR]; [| exact (HX HR)]. exact (NF (HXf a HR)).
      + destruct Hc as [H1|[H1|(b & Hb & Hr)]]; [left; clear - H1 SPAH; lia| right; left; exact H1| right; right; exists b; split; [| exact Hr]].
        apply in_or_app. right. apply in_or_app. right. exact Hb.
    - intros L SP HSP. destruct Hc as [H1|[H1|(b & Hb & Hr)]]; [left; clear - H1 HSP; lia| right; left; exact H1| right; right; exists b; split; [apply in_or_app; right; exact Hb| exact Hr]].
  Qed.

  (* [comment removed for export] *)
  Lemma pay_keep : forall mX, agree_on (ax_client LB (bv_unsigned sp) LIBW_A) m mX -> payload_okA mX LB D d.
  Proof.
    intros mX AG. pose proof PRE as (HEAP & _). pose proof PAY as (BY & FB & D0 & DH & DL & HB).
    split; [| repeat (split; [assumption|]); exact HB].
    destruct HB as [->|(b & Hb & H1 & H2)].
    { cbn [to_bytes map]. apply bytes_at_nil. unfold zlength in DH. cbn in DH. lia. }
    apply (bytes_at_agree _ m mX _ _ AG BY). intros x Hx. unfold to_bytes in Hx. rewrite length_map in Hx. unfold zlength in H2.
    pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; right; exact Hb)) as (R1 & _ & _ & R4 & R5).
    split; [| right; right; exists b; split; [exact Hb| lia]].
    unfold LIBW_A. cbn [rin_ivs fst snd]. clear - Hx H1 H2 R1 R4 R5. alia.
  Qed.

  (* [comment removed for export] *)
  Lemma close_pbs : forall Σk OWk mk, @BnHeapA.AHEAP (push AR f 1) Σk OWk (pbs ++ LB) mk -> @BnHeapA.AHEAP (push AR f 1) Σk OWk LB mk.
  Proof.
    intros Σk OWk mk H. subst pbs. unfold fto_pbs in H. cbn [app] in H.
    apply (@frame_obj_close (push AR f 1) Σk OWk LB mk f 1%nat (qd, f + 64, 8) (or_introl eq_refl)); [| unfold in_fr; change (fs_size 1) with 128; cbn; lia].
    apply (@frame_obj_close (push AR f 1) Σk OWk ((qd, f + 64, 8) :: LB) mk f 1%nat (qb, f + 32, 8) (or_introl eq_refl)); [exact H| unfold in_fr; change (fs_size 1) with 128; cbn; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma har_clr : forall (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s3v s4v s5v x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32) Σk stX mk OWk bok spent,
    hinv Σk stX mk OWk bok [] spent -> ERR_CLEAR_ERROR_COST <= BCOST - spent ->
    implAp (ct_tail stX) Σk FQ (bst x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s3v s4v s5v x28 x29 x30 x31 Fk fck mk HARA_CLR).
  Proof.
    intros until spent. intros (PREk & AGSk & AXk & CRk & SP0k & NFk & LBOKk & FRLk & FRHk) HC.
    pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0).
    pose proof HYPS as (_ & _ & _ & _ & _ & _ & HCLR).
    pose proof PRE as (HEAP & AS & IDS & DC & ST & _ & _ & _ & _ & MI & CRED & FRM).
    unfold bst, HARA_CLR. cbn [ar_PMc push amb].
    pose proof (munch_refl ([] : list (Z * Z)) mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
    pose proof PREk as (HEAPk & _ & _ & _ & STk & _ & _ & _ & _ & MIk & _).
    apply implAp_from_evt. zstep. apply evt_done.
    unfold ct_tail, abind.
    eapply implAp_bind.
    { eapply (HCLR f bok) with (K := []);
        [ eapply ap_preA_weaken; [exact PREk| subst BSTK; unfold ERR_CLEAR_ERROR_STACK, CT_FUZZ_STACK_A, FUZZ_STACK, RT_STACK; clear; lia
                                 | unfold ERR_CLEAR_ERROR_COST in *; clear - HC; lia| subst BFRM; unfold ERR_CLEAR_ERROR_FRAMES, CT_FUZZ_FRAMES_A, FRAMES_MAX; clear; cbn; lia]
        | reflexivity
        | rewrite ESPA; exact (uw_callee mk AGSk FRHk)
        | exact (ctx_callee _ _ 0 E_clr ltac:(apply unsigned_lit; clear; lia))
        | apply cons_ne
        | reflexivity
        | intros b Hb; destruct Hb
        | intros b Hb; destruct Hb ]. }
    intros [u st'] Σ' ms' PO. cbn [fst snd].
    destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & OW2 & bo2 & -> & PRE2 & AXP2 & CRED2 & KEPT2 & [Ebo Est]).
    cbn [fst snd] in Est, PRE2. rewrite (ret_pc_even 0x1f4304) by (clear; lia).
    pose proof PRE2 as (HEAP2 & AS2 & IDS2 & DC2 & ST2 & _ & _ & _ & _ & MI2 & _). rewrite ESPA in ST2. rewrite ?ESPA in AXP2. cbn [app] in HEAP2.
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AXP2) in FRLk;
      [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [intros HR; pose proof (libw_below a HR) as HB; clear - HB Ha C1 CEIL LOSP SPAL; unfold CT_FUZZ_STACK_A, FUZZ_STACK in *; alia| left; clear - Ha GSZ SPAH TOP; unfold USTACK_TOP in *; lia]].
    apply (rw_cells_agree _ _ _ _ _ AXP2) in FRHk;
      [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [intros HR; pose proof (libw_below a HR) as HB; clear - HB Ha C1 CEIL LOSP SPAL; unfold CT_FUZZ_STACK_A, FUZZ_STACK in *; alia| left; clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia]].
    (* [comment removed for export] *)
    intros X Φ Dl SAFE LINK.
    eapply (fto_epi_cps _) with (lo := lo) (OWk := OW2) (LB := LB) (g := g) (gj := gj) (j0 := j0) (hrest := []);
      [ exact (close_pbs _ _ _ HEAP2) | exact OFFLB | exact ST2 | exact CEIL | clear - CEIL LOSP SPAL; unfold CT_FUZZ_STACK_A, FUZZ_STACK in *; lia
      | exact TOP | exact SPAL | exact SPAH | exact GSZ | exact SAVJ | exact MI2 | exact FRLk | cbn [app]; exact FRHk | reflexivity |].
    intros Σ3 m4 HEAP4 CR4 EL4 ST4 MI4 AG4.
    eapply (implAp_elim (ARet (0, st'))); [| exact SAFE | exact LINK | exact EL4].
    apply implAp_ret. subst FQ. unfold ct_top_postA, MallocRep.wz.
    do 16 eexists. exists m4, OW2, bo2. split; [reflexivity|].
    assert (AGL : agree_on (lib_addr OW2) m2 m4) by (eapply aclient_lib; exact AG4).
    split.
    { pose proof AS2 as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD2)).
      unfold ap_preA. split; [exact HEAP4|]. split; [exact (ap_state_agree _ _ _ _ _ _ AS2 AGL)|]. split; [exact IDS2|].
      split; [exact (data_cells_agree _ _ _ _ DC2 AGL OD2)|]. split; [exact ST4|]. split; [exact CEIL|]. split; [clear - LOSP; unfold CT_FUZZ_STACK_A, FUZZ_STACK in *; lia|].
      split; [exact TOP|]. split; [exact AL16|]. split; [exact MI4|].
      split; [pose proof (af_credit_nonneg RT AF Σ3 m4 (AH_art _ _ _ _ HEAP4)) as CNN; clear - CNN; lia|].
      clear - FRM. unfold CT_FUZZ_FRAMES_A in *. lia. }
    split; [exact Est|].
    assert (AGX : agree_on (ax_client LB (bv_unsigned sp) LIBW_A) m m4).
    { eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a Ha; exact (proj1 (axw a Ha))|].
      eapply agree_on_trans; [eapply agree_on_mono; [exact AXk|]; intros a [HX Hc]; split; [exact HX|];
                              destruct (proj1 (proj2 (proj2 (axw a (conj HX Hc)))) [] (bv_unsigned sp) ltac:(clear; lia)) as [H1|[H1|H1]];
                              [left; clear - H1 SPAH; lia| right; left; exact H1| right; right; exact H1]|].
      eapply agree_on_trans; [eapply agree_on_mono; [exact AXP2|]; intros a Ha; rewrite <- (app_nil_l (pbs ++ LB)); apply (proj1 (proj2 (axw a Ha)) [] []); intros x Hx; destruct Hx|].
      eapply agree_on_mono; [exact AG4|]. intros a Ha. exact (proj1 (proj2 (proj2 (axw a Ha))) OW2 spa ltac:(clear - SPAH; lia)). }
    split; [exact AGX|].
    split; [cbn [ar_RT push amb] in CRED2; clear - CR1 CRk CRED2 CR4 HC SP0k CRED0; subst BCOST; unfold ERR_CLEAR_ERROR_COST, CT_FUZZ_COST_A in *; lia|].
    split; [exact (pay_keep m4 AGX)| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma axw_spa : forall a, ax_client LB spa LIBW_A a ->
    (forall (L : list block) (X : list (Z * Z)), (forall x, rin_ivs X x -> f <= x < f + 128) -> ax_client (L ++ pbs ++ LB) spa (X ++ LIBW_A) a)
    /\ (forall (L : list block), aclient_addr (L ++ LB) spa a)
    /\ ~ (f <= a < f + 128).
  Proof.
    intros a [HX Hc]. pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0).
    assert (CSB : forall x, client_static x -> x < SEGTOP_A).
    { intros x [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. unfold SEGTOP_A. clear - Hin Hlh. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia. }
    assert (NF : ~ (f <= a < f + 128)).
    { destruct Hc as [H1|[H1|(b & Hb & Hr)]].
      - unfold CT_FUZZ_STACK_A, FUZZ_STACK in LOSP. clear - H1 G3 CEIL LOSP SPAL. unfold BnHeapA.ACEIL in *. lia.
      - pose proof (CSB a H1). clear - H G4. lia.
      - pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. clear - Hr O. lia. }
    split; [| split; [| exact NF]].
    - intros L X HXf. split.
      + intros HR. apply rin_ivs_app in HR. destruct HR as [HR|HR]; [| exact (HX HR)]. exact (NF (HXf a HR)).
      + destruct Hc as [H1|[H1|(b & Hb & Hr)]]; [left; exact H1| right; left; exact H1| right; right; exists b; split; [| exact Hr]].
        apply in_or_app. right. apply in_or_app. right. exact Hb.
    - intros L. destruct Hc as [H1|[H1|(b & Hb & Hr)]]; [left; exact H1| right; left; exact H1| right; right; exists b; split; [apply in_or_app; right; exact Hb| exact Hr]].
  Qed.

  (* [comment removed for export] *)
  Lemma frl_acl : forall (L : list block) a, spa <= a < spa + Z.of_nat (cells_size [CB 8 j0; C8 (Z_to_bv 64 f); CB g junk]) -> aclient_addr L spa a /\ ~ rin_ivs LIBW_A a.
  Proof.
    intros L a Ha. pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & _). cbn [cells_size csize Nat.add] in Ha.
    split; [left; clear - Ha GSZ SPAH TOP; unfold USTACK_TOP in *; lia|].
    intros HR. pose proof (libw_below a HR) as HB. clear - HB Ha C1 CEIL LOSP SPAL. unfold CT_FUZZ_STACK_A, FUZZ_STACK in *. alia.
  Qed.
  Lemma frh_acl : forall (L : list block) a, bv_unsigned sp + -16 <= a < bv_unsigned sp + -16 + Z.of_nat (cells_size [C8 s0; C8 ra]) -> aclient_addr L spa a /\ ~ rin_ivs LIBW_A a.
  Proof.
    intros L a Ha. pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & _). cbn [cells_size csize Nat.add] in Ha.
    split; [left; clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia|].
    intros HR. pose proof (libw_below a HR) as HB. clear - HB Ha C1 CEIL LOSP SPAL. unfold CT_FUZZ_STACK_A, FUZZ_STACK in *. alia.
  Qed.

  (* [comment removed for export] *)
  Lemma hinv_kit : forall Σk stX mk OWk bok NEWk spent Σ' m' (L1 : list block) NEW' c,
    hinv Σk stX mk OWk bok NEWk spent ->
    @BnHeapA.AHEAP (push AR f 1) Σ' OWk (NEW' ++ pbs ++ LB) m' ->
    agree_on (aclient_addr (L1 ++ pbs ++ LB) spa) mk m' -> (forall b, In b OWk -> In b L1) ->
    mem_inv ctasegs m' -> stk ctasegs m' lo spa ->
    rt_credit RT Σk - c <= rt_credit RT Σ' -> 0 <= c -> 0 <= BCOST - spent - c ->
    (forall b, In b NEW' -> ~ In (blk_id b) (map blk_id (OWk ++ pbs ++ LB))) -> Forall (@lbokA (push AR f 1)) NEW' ->
    hinv Σ' stX m' OWk bok NEW' (spent + c).
  Proof.
    intros until c. intros (PREk & AGSk & AXk & CRk & SP0k & NFk & LBOKk & FRLk & FRHk) HEAP' AG INC MI' ST' CR' C0 CB NF' LBOK'.
    pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0).
    pose proof PREk as (HEAPk & ASk & IDSk & DCk & STk & CEILk & LOSPk & TOPk & AL16k & MIk & CREDk & FRMk).
    assert (AGL : agree_on (lib_addr OWk) mk m').
    { eapply agree_on_mono; [exact AG|]. intros a [Hs|(b & Hb & Hr)].
      - right; left. exact (ar_LIBW_cs a (LIBW_S_A a Hs)).
      - right; right. exists b. split; [apply in_or_app; left; exact (INC b Hb)| exact Hr]. }
    split.
    { pose proof ASk as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & ODk)).
      unfold ap_preA. split; [exact HEAP'|]. split; [exact (ap_state_agree _ _ _ _ _ _ ASk AGL)|]. split; [exact IDSk|].
      split; [exact (data_cells_agree _ _ _ _ DCk AGL ODk)|]. split; [rewrite ESPA; exact ST'|]. split; [exact CEILk|]. split; [exact LOSPk|].
      split; [exact TOPk|]. split; [exact AL16k|]. split; [exact MI'|]. split; [| exact FRMk]. cbn [ar_RT push amb] in CREDk |- *. clear - CREDk CRk CR' C0 CB. lia. }
    split. { eapply agree_on_trans; [exact AGSk|]. eapply agree_on_mono; [exact AG|]. intros a Ha. left. clear - Ha SPAH; lia. }
    split. { eapply agree_on_trans; [exact AXk|]. eapply agree_on_mono; [exact AG|]. intros a Ha. rewrite app_assoc. exact (proj1 (proj2 (axw_spa a Ha)) (L1 ++ pbs)). }
    split; [clear - CRk CR' C0; lia|]. split; [clear - SP0k C0; lia|]. split; [exact NF'|]. split; [exact LBOK'|].
    split; [eapply rw_cells_agree; [exact AG| exact FRLk| intros a Ha; exact (proj1 (frl_acl _ a Ha))]|].
    eapply rw_cells_agree; [exact AG| exact FRHk| intros a Ha; exact (proj1 (frh_acl _ a Ha))].
  Qed.

  (* [comment removed for export] *)
  Lemma hinv_ap : forall Σk stX mk OWk bok NEWk spent Σ' st' m' OW' bo' NEW' (X : list (Z * Z)) c,
    hinv Σk stX mk OWk bok NEWk spent ->
    @ap_preA (push AR f 1) Σ' st' m' OW' (NEW' ++ pbs ++ LB) E bo' (Z_to_bv 64 spa) lo 0 0 0 ->
    ax_pres (NEWk ++ pbs ++ LB) spa (X ++ LIBW_A) mk m' -> (forall x, rin_ivs X x -> f <= x < f + 128) ->
    rt_credit RT Σk - c <= rt_credit RT Σ' -> 0 <= c -> 0 <= BCOST - spent - c ->
    (forall b, In b NEW' -> ~ In (blk_id b) (map blk_id (OW' ++ pbs ++ LB))) -> Forall (@lbokA (push AR f 1)) NEW' ->
    hinv Σ' st' m' OW' bo' NEW' (spent + c).
  Proof.
    intros until c. intros (PREk & AGSk & AXk & CRk & SP0k & NFk & LBOKk & FRLk & FRHk) PRE' AXP HX CR' C0 CB NF' LBOK'.
    pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0).
    pose proof PREk as (_ & _ & _ & _ & _ & _ & LOSPk & _ & _ & _ & CREDk & FRMk).
    pose proof PRE' as (HEAP' & AS' & IDS' & DC' & ST' & CEIL' & _ & TOP' & AL16' & MI' & CRED' & _).
    split.
    { unfold ap_preA. split; [exact HEAP'|]. split; [exact AS'|]. split; [exact IDS'|]. split; [exact DC'|]. split; [exact ST'|]. split; [exact CEIL'|]. split; [exact LOSPk|].
      split; [exact TOP'|]. split; [exact AL16'|]. split; [exact MI'|]. split; [| exact FRMk]. cbn [ar_RT push amb] in CREDk, CRED' |- *. clear - CREDk CRk CR' C0 CB. lia. }
    split. { eapply agree_on_trans; [exact AGSk|]. eapply agree_on_mono; [exact AXP|]. intros a Ha.
             assert (HC : ax_client LB spa LIBW_A a).
             { split; [| left; clear - Ha SPAH; lia]. intros HR. pose proof (libw_below a HR) as HB. clear - HB Ha C1 CEIL LOSP SPAL. unfold CT_FUZZ_STACK_A, FUZZ_STACK in *. alia. }
             exact (proj1 (axw_spa a HC) NEWk X HX). }
    split. { eapply agree_on_trans; [exact AXk|]. eapply agree_on_mono; [exact AXP|]. intros a Ha. exact (proj1 (axw_spa a Ha) NEWk X HX). }
    split; [clear - CRk CR' C0; lia|]. split; [clear - SP0k C0; lia|]. split; [exact NF'|]. split; [exact LBOK'|].
    assert (FRX : forall a, spa <= a < bv_unsigned sp -> ax_client (NEWk ++ pbs ++ LB) spa (X ++ LIBW_A) a).
    { intros a Ha. split; [| left; clear - Ha TOP; unfold USTACK_TOP in *; lia]. intros HR. apply rin_ivs_app in HR. destruct HR as [HR|HR].
      - pose proof (HX a HR). unfold CT_FUZZ_STACK_A, FUZZ_STACK in LOSP. clear - H Ha G3 CEIL LOSP SPAL. unfold BnHeapA.ACEIL in *. lia.
      - pose proof (libw_below a HR) as HB. clear - HB Ha C1 CEIL LOSP SPAL. unfold CT_FUZZ_STACK_A, FUZZ_STACK in *. alia. }
    split; [eapply rw_cells_agree; [exact AXP| exact FRLk| intros a Ha; apply FRX; cbn [cells_size csize Nat.add] in Ha; clear - Ha GSZ SPAH; lia]|].
    eapply rw_cells_agree; [exact AXP| exact FRHk| intros a Ha; apply FRX; cbn [cells_size csize Nat.add] in Ha; clear - Ha SPAH; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition T4 (k : skr bptr) (st : ap_st bptr) : aprog bptr (Z * ap_st bptr) := apbind (sk_free_all k st) (fun p => ct_tail (snd p)).

  Lemma har_free : forall (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32) Σk stX mk OWk bok spent NEWk (adr : bptr -> Z) (k : skr bptr),
    hinv Σk stX mk OWk bok NEWk spent -> Permutation NEWk (sk_blocks adr k) -> sk_repA mk (NEWk ++ pbs ++ LB) adr k -> zlength (sk_items k) < 2 ^ 31 ->
    ERR_CLEAR_ERROR_COST <= BCOST - spent ->
    implAp (T4 k stX) Σk FQ (bst x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 (wz (adr (sk_blk k))) s4v s5v x28 x29 x30 x31 Fk fck mk HARA_FREE).
  Proof.
    intros until k. intros HI PM SK N31 HC. pose proof HI as (PREk & AGSk & AXk & CRk & SP0k & NFk & LBOKk & FRLk & FRHk).
    pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0).
    pose proof HYPS as (_ & _ & _ & HFREE & _ & _ & _). pose proof BUD as (_ & _ & _ & BSTKF & _).
    pose proof PREk as (HEAPk & ASk & _ & _ & STk & _ & _ & _ & _ & MIk & _).
    unfold bst, HARA_FREE, MallocRep.wz. cbn [ar_PMc push amb].
    pose proof (munch_refl ([] : list (Z * Z)) mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
    apply implAp_from_evt. zstep. zstep. apply evt_done.
    (* [comment removed for export] *)
    pose proof (@AH_adopt_list (push AR f 1) Σk NEWk OWk (pbs ++ LB) mk HEAPk LBOKk) as HEAPa.
    assert (SKa : sk_repA mk (NEWk ++ OWk) adr k).
    { eapply sk_repA_relist; [exact SK|]. intros b Hb. apply in_or_app. left. eapply Permutation_in; [symmetry; exact PM| exact Hb]. }
    pose proof (@AH_nodup (push AR f 1) _ _ _ _ HEAPa) as NDa. rewrite map_app in NDa. pose proof (nodup_app_l _ _ NDa) as NDl.
    unfold T4. eapply implAp_bind.
    { eapply (HFREE f) with (lo := lo) (adr := adr);
        [ exact HEAPa | exact STk | exact CEIL | rewrite ESPA; clear - BSTKF LOSP SPAL; unfold CT_FUZZ_STACK_A, FUZZ_STACK, HAR_FRAME_A in *; lia
        | rewrite ESPA; clear - SPAH TOP; unfold USTACK_TOP in *; lia | rewrite ESPA; clear - SPA32; Z.div_mod_to_equations; lia | exact MIk | reflexivity
        | pose proof ASk as (_ & SFk & _); exact (proj1 SFk)
        | rewrite ESPA; exact (uw_callee mk AGSk FRHk)
        | exact (ctx_callee _ _ 0 E_free ltac:(apply unsigned_lit; clear; lia))
        | apply cons_ne | exact SKa | exact N31 | reflexivity ]. }
    intros [u st'] Σ' ms' PO. cbn [fst snd].
    destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & Er & MI2 & ST2 & AG2 & CR2 & HEAP2).
    injection Er as Est. subst st'. rewrite (ret_pc_even 0x1f4300) by (clear; lia). rewrite ?ESPA in AG2, ST2.
    (* [comment removed for export] *)
    pose proof (CtSctP.W_o2i_sct_list.remove_sk_perm adr k [] NEWk OWk PM NDl) as PMR. cbn [app] in PMR. unfold remove_sk in AG2, HEAP2.
    assert (HI2 : hinv Σ' stX m2 OWk bok [] spent).
    { replace spent with (spent + 0) by (clear; lia).
      eapply (hinv_kit Σk stX mk OWk bok NEWk spent Σ' m2 _ [] 0 HI); [| exact AG2| | exact MI2| exact ST2| cbn [ar_RT push amb] in CR2; clear - CR2; lia| clear; lia| clear - HC; unfold ERR_CLEAR_ERROR_COST in *; lia| intros b Hb; destruct Hb| constructor].
      - cbn [app]. eapply (@AHEAP_permOW (push AR f 1)); [exact HEAP2| exact PMR].
      - intros b Hb. eapply Permutation_in; [symmetry; exact PMR| exact Hb]. }
    change (Z_to_bv 64 0x1f4300) with (Z_to_bv 64 HARA_CLR).
    exact (har_clr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ' stX m2 OWk bok spent HI2 HC).
  Qed.

  (* [comment removed for export] *)
  Definition mid_free (adr : bptr -> Z) (k : skr bptr) (r : unit * ap_st bptr) (Σ' : rts RT) (ms' : machine_state) : Prop :=
    exists (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32) mk OWk bok spent NEWk,
      ms' = bst x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 (wz (adr (sk_blk k))) s4v s5v x28 x29 x30 x31 Fk fck mk HARA_FREE
      /\ hinv Σ' (snd r) mk OWk bok NEWk spent /\ Permutation NEWk (sk_blocks adr k) /\ sk_repA mk (NEWk ++ pbs ++ LB) adr k /\ zlength (sk_items k) < 2 ^ 31
      /\ ERR_CLEAR_ERROR_COST <= BCOST - spent.

  Lemma mid_free_elim : forall adr k r Σ' ms', mid_free adr k r Σ' ms' -> implAp (T4 k (snd r)) Σ' FQ ms'.
  Proof.
    intros adr k [u st'] Σ' ms' (x1 & x5 & x6 & x7 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4v & s5v & x28 & x29 & x30 & x31 & Fk & fck & mk & OWk & bok & spent & NEWk & -> & HI & PM & SK & N31 & HC).
    cbn [snd] in HI |- *. exact (har_free x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v x28 x29 x30 x31 Fk fck Σ' st' mk OWk bok spent NEWk adr k HI PM SK N31 HC).
  Qed.

  (* [comment removed for export] *)
  Lemma nf_of_heap : forall Σx OWx (NEW R : list block) mx, @BnHeapA.AHEAP (push AR f 1) Σx OWx (NEW ++ R) mx ->
    forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OWx ++ R)).
  Proof.
    intros Σx OWx NEW R mx H b Hb Hin. pose proof (@AH_nodup (push AR f 1) _ _ _ _ H) as ND.
    assert (ND' : List.NoDup (map blk_id (NEW ++ OWx ++ R))).
    { eapply nodup_ids_perm; [| exact ND]. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
    rewrite map_app in ND'. destruct (CtSctP.W_sct_list_free.NoDup_app_split _ _ ND') as (_ & DISJ & _).
    exact (DISJ (blk_id b) (in_map _ _ _ Hb) Hin).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma har_cfree_none : forall (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s5v x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32) Σk (stX : ap_st bptr) mk OWk bok spent NEWk (adr : bptr -> Z) (k : skr bptr),
    hinv Σk stX mk OWk bok NEWk spent -> Permutation NEWk (sk_blocks adr k) -> sk_repA mk (NEWk ++ pbs ++ LB) adr k -> zlength (sk_items k) < 2 ^ 31 ->
    ERR_CLEAR_ERROR_COST <= BCOST - spent ->
    rw_cells ctasegs mk (f + 64) [C8 (wz 0)] ->
    implAp (aret tt stX) Σk (mid_free adr k) (bst x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 (wz (adr (sk_blk k))) (Z_to_bv 64 (f + 64)) s5v x28 x29 x30 x31 Fk fck mk HARA_CFREE).
  Proof.
    intros until k. intros HI PM SK N31 HC OD. pose proof HI as (PREk & AGSk & AXk & CRk & SP0k & NFk & LBOKk & FRLk & FRHk).
    pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0).
    pose proof PREk as (HEAPk & ASk & _ & _ & STk & _ & _ & _ & _ & MIk & _). rewrite ESPA in STk.
    assert (Ef64 : bv_unsigned (Z_to_bv 64 (f + 64)) = f + 64) by (apply unsigned_lit; clear - G1 G3 C3; alia).
    unfold bst, HARA_CFREE, MallocRep.wz in *. cbn [ar_PMc push amb].
    pose proof (munch_refl ([] : list (Z * Z)) mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
    apply implAp_from_evt. zstep. zstep. zstep. zstep. zstep.
    apply evt_done. eapply implAp_step_same.
    { eapply (@CRYPTO_free_null_cpsA (push AR f 1) UK BE) with (lo := lo) (OW := OWk) (LB := NEWk ++ pbs ++ LB); try reflexivity;
        [ exact HEAPk | rewrite ESPA; exact STk | exact CEIL | rewrite ESPA; unfold CRYPTO_FREE_STACK, RT_STACK; clear - LOSP SPAL; unfold CT_FUZZ_STACK_A, FUZZ_STACK in *; lia
        | rewrite ESPA; clear - SPAH TOP; unfold USTACK_TOP in *; lia | rewrite ESPA; clear - SPA32; Z.div_mod_to_equations; lia | exact MIk
        | pose proof ASk as (_ & SFk & _); exact (proj1 SFk)
        | rewrite ESPA; exact (uw_callee mk AGSk FRHk)
        | exact (ctx_callee _ _ 0 E_cfree ltac:(apply unsigned_lit; clear; lia)) ]. }
    intros ms3 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & m5 & -> & MI5 & ST5 & HEAP5 & AG5).
    rewrite ?ESPA in ST5, AG5. rewrite (ret_pc_even 0x1f42f4) by (clear; lia).
    assert (HI5 : hinv Σk stX m5 OWk bok NEWk spent).
    { replace spent with (spent + 0) by (clear; lia).
      eapply (hinv_kit Σk stX mk OWk bok NEWk spent Σk m5 (OWk ++ NEWk) NEWk 0 HI);
        [exact HEAP5| rewrite <- app_assoc; exact AG5| intros b Hb; apply in_or_app; left; exact Hb| exact MI5| exact ST5| clear; lia| clear; lia
        | clear - HC; unfold ERR_CLEAR_ERROR_COST in *; lia| exact NFk| exact LBOKk]. }
    apply implAp_ret. unfold mid_free, bst, HARA_FREE, MallocRep.wz.
    do 20 eexists. exists m5, OWk, bok, spent, NEWk. split; [reflexivity|].
    split; [exact HI5|]. split; [exact PM|]. split; [| split; [exact N31| exact HC]].
    (* [comment removed for export] *)
    eapply sk_repA_agree; [exact AG5| | exact SK]. intros b a Hb Ha. right; right. exists b. split; [| exact Ha].
    apply in_or_app. right. apply in_or_app. left. eapply Permutation_in; [symmetry; exact PM| exact Hb].
  Qed.

  (* [comment removed for export] *)
  Lemma sk_blocks_adr : forall (adr : bptr -> Z) (k : skr bptr) b, In b (sk_blocks adr k) -> blk_addr b = adr (blk_id b).
  Proof.
    intros adr k b Hb.
    assert (OB : forall o, In b (CtSctP.W_sct_list_free.oblk adr o) -> blk_addr b = adr (blk_id b)).
    { intros [[q n]|] H; cbn in H; [| destruct H]. destruct H as [<-|[]]. reflexivity. }
    unfold CtSctP.SctStmt.sk_blocks in Hb. rewrite !in_app_iff in Hb. destruct Hb as [Hb|[Hb|Hb]].
    - induction (sk_items k) as [|x t IH]; [destruct Hb|]. cbn in Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exact (IH Hb)].
      unfold CtSctP.W_sct_list_free.sct_blocks in Hb. rewrite !in_app_iff in Hb.
      destruct Hb as [Hb|[Hb|[Hb|[Hb|[<-|[]]]]]]; try (exact (OB _ Hb)). reflexivity.
    - destruct (sk_data k) as [[q na]|]; cbn in Hb; [| destruct Hb]. destruct Hb as [<-|[]]. reflexivity.
    - destruct Hb as [<-|[]]. reflexivity.
  Qed.

  Lemma har_cfree_some : forall (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s5v x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32) Σk (stX : ap_st bptr) mk OWk bok spent NEWk (adr : bptr -> Z) (k : skr bptr)
      (dp : bptr) (AD n : Z),
    hinv Σk stX mk OWk bok ((dp, AD, n) :: NEWk) spent -> Permutation NEWk (sk_blocks adr k) -> sk_repA mk (NEWk ++ pbs ++ LB) adr k -> zlength (sk_items k) < 2 ^ 31 ->
    ERR_CLEAR_ERROR_COST <= BCOST - spent -> 0 < n ->
    rw_cells ctasegs mk (f + 64) [C8 (wz AD)] ->
    implAp (afree dp stX) Σk (mid_free adr k) (bst x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 (wz (adr (sk_blk k))) (Z_to_bv 64 (f + 64)) s5v x28 x29 x30 x31 Fk fck mk HARA_CFREE).
  Proof.
    intros until n. intros HI PM SK N31 HC Hn OD. pose proof HI as (PREk & AGSk & AXk & CRk & SP0k & NFk & LBOKk & FRLk & FRHk).
    pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0).
    pose proof PREk as (HEAPk & ASk & _ & _ & STk & _ & _ & _ & _ & MIk & _). rewrite ESPA in STk.
    assert (Ef64 : bv_unsigned (Z_to_bv 64 (f + 64)) = f + 64) by (apply unsigned_lit; clear - G1 G3 C3; alia).
    unfold bst, HARA_CFREE, MallocRep.wz in *. cbn [ar_PMc push amb].
    pose proof (munch_refl ([] : list (Z * Z)) mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
    apply implAp_from_evt. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply Forall_cons_iff in LBOKk as [LBd LBOKk].
    pose proof (@AH_adopt_list (push AR f 1) Σk [(dp, AD, n)] OWk (NEWk ++ pbs ++ LB) mk HEAPk ltac:(constructor; [exact LBd| constructor])) as HEAPa. cbn [app] in HEAPa.
    pose proof (@AH_nodup (push AR f 1) _ _ _ _ HEAPa) as NDa. pose proof (@AH_nodup_l (push AR f 1) _ _ _ _ HEAPa) as NDl.
    apply evt_done. unfold afree.
    eapply (@CRYPTO_free_walkAp (push AR f 1) UK BE) with (lo := lo) (A := AD) (n := n);
      [ exact HEAPa | left; reflexivity | rewrite ESPA; exact STk | exact CEIL | rewrite ESPA; unfold CRYPTO_FREE_STACK, RT_STACK; clear - LOSP SPAL; unfold CT_FUZZ_STACK_A, FUZZ_STACK in *; lia
      | rewrite ESPA; clear - SPAH TOP; unfold USTACK_TOP in *; lia | rewrite ESPA; clear - SPA32; Z.div_mod_to_equations; lia | exact MIk | reflexivity
      | pose proof ASk as (_ & SFk & _); exact (proj1 SFk) | reflexivity
      | rewrite ESPA; exact (uw_callee mk AGSk FRHk)
      | exact (ctx_callee _ _ 0 E_cfree ltac:(apply unsigned_lit; clear; lia)) |].
    intros Σ' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & m5 & -> & MI5 & ST5 & AG5 & CR5 & HEAP5).
    rewrite ?ESPA in ST5, AG5. rewrite (ret_pc_even 0x1f42f4) by (clear; lia).
    rewrite (lb_remove_head (dp, AD, n) OWk NDl) in HEAP5.
    change (((dp, AD, n) :: OWk) ++ NEWk ++ pbs ++ LB) with ((dp, AD, n) :: (OWk ++ NEWk ++ pbs ++ LB)) in AG5.
    rewrite (lb_remove_head (dp, AD, n) (OWk ++ NEWk ++ pbs ++ LB) NDa) in AG5.
    assert (HI5 : hinv Σ' stX m5 OWk bok NEWk spent).
    { replace spent with (spent + 0) by (clear; lia).
      eapply (hinv_kit Σk stX mk OWk bok ((dp, AD, n) :: NEWk) spent Σ' m5 (OWk ++ NEWk) NEWk 0 HI);
        [exact HEAP5| rewrite <- app_assoc; exact AG5| intros b Hb; apply in_or_app; left; exact Hb| exact MI5| exact ST5| cbn [ar_RT push amb] in CR5; clear - CR5; lia| clear; lia
        | clear - HC; unfold ERR_CLEAR_ERROR_COST in *; lia| intros b Hb; apply NFk; right; exact Hb| exact LBOKk]. }
    apply implAp_ret. unfold mid_free, bst, HARA_FREE, MallocRep.wz.
    do 20 eexists. exists m5, OWk, bok, spent, NEWk. split; [reflexivity|].
    split; [exact HI5|]. split; [exact PM|]. split; [| split; [exact N31| exact HC]].
    eapply sk_repA_agree; [exact AG5| | exact SK]. intros b a Hb Ha. right; right. exists b. split; [| exact Ha].
    apply in_or_app. right. apply in_or_app. left. eapply Permutation_in; [symmetry; exact PM| exact Hb].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition T3 (k : skr bptr) (st : ap_st bptr) : aprog bptr (Z * ap_st bptr) := apbind (i2d_sct_list k st) (fun p => T4 k (snd p)).

  Lemma har_i2d : forall (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s5v x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32) Σk (stX : ap_st bptr) mk OWk bok spent NEWk (adr : bptr -> Z) (k : skr bptr),
    hinv Σk stX mk OWk bok NEWk spent -> Permutation NEWk (sk_blocks adr k) -> sk_repA mk (NEWk ++ pbs ++ LB) adr k -> zlength (sk_items k) < 2 ^ 31 ->
    (forall b, In b (pbs ++ LB) -> adr (blk_id b) = blk_addr b) ->
    0 <= CST_I2D (zlength (sk_items k)) -> CST_I2D (zlength (sk_items k)) + ERR_CLEAR_ERROR_COST <= BCOST - spent ->
    rw_cells ctasegs mk (f + 64) [C8 (wz 0)] ->
    implAp (T3 k stX) Σk FQ (bst x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 (wz (adr (sk_blk k))) (Z_to_bv 64 (f + 64)) s5v x28 x29 x30 x31 Fk fck mk HARA_I2D).
  Proof.
    intros until k. intros HI PM SK N31 ADR C0 HC OD. pose proof HI as (PREk & AGSk & AXk & CRk & SP0k & NFk & LBOKk & FRLk & FRHk).
    pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0).
    pose proof HYPS as (_ & _ & HI2D & _). pose proof BUD as (_ & _ & BSTKI & _ & _ & _ & BFRMI & _).
    pose proof PREk as (HEAPk & ASk & _ & _ & STk & _ & _ & _ & _ & MIk & _).
    unfold bst, HARA_I2D, MallocRep.wz in *. cbn [ar_PMc push amb].
    pose proof (munch_refl ([] : list (Z * Z)) mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
    apply implAp_from_evt. zstep. zstep. zstep. apply evt_done.
    unfold T3. eapply implAp_bind.
    { eapply (i2d_sct_list_of_specA _ _ _ (HI2D f)) with (K := []) (LB := NEWk ++ pbs ++ LB) (lo := lo) (adr := adr) (DER := f + 64);
        [ eapply ap_preA_weaken; [exact PREk| unfold BSTK; clear - BSTKI; unfold CT_FUZZ_STACK_A, FUZZ_STACK, HAR_FRAME_A in *; lia| clear - C0 HC; unfold ERR_CLEAR_ERROR_COST in *; lia
                                 | unfold BFRM; clear - BFRMI; lia]
        | reflexivity
        | rewrite ESPA; exact (uw_callee mk AGSk FRHk)
        | exact (ctx_callee _ _ 0 E_i2d ltac:(apply unsigned_lit; clear; lia))
        | apply cons_ne
        | intros b Hb; destruct Hb | intros b Hb; destruct Hb
        | exact SK
        | intros b Hb; apply in_app_iff in Hb; destruct Hb as [Hb|Hb]; [symmetry; apply (sk_blocks_adr adr k); eapply Permutation_in; [exact PM| exact Hb] | exact (ADR b Hb)]
        | exists (qd, f + 64, 8); split; [apply in_or_app; right; apply in_or_app; left; unfold pbs, fto_pbs; right; left; reflexivity| cbn; clear; lia]
        | clear - G2; Z.div_mod_to_equations; lia
        | intros b Hb;
          pose proof (@AH_disjoint_gen (push AR f 1) _ _ _ _ b (qd, f + 64, 8) HEAPk
                        ltac:(apply in_or_app; right; apply in_or_app; left; eapply Permutation_in; [symmetry; exact PM| exact Hb])
                        ltac:(apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; unfold pbs, fto_pbs; right; left; reflexivity)
                        ltac:(intros E0; apply (NFk b ltac:(eapply Permutation_in; [symmetry; exact PM| exact Hb])); rewrite E0, !map_app; apply in_or_app; right; apply in_or_app; left;
                              unfold pbs, fto_pbs; cbn; right; left; reflexivity)) as DJ;
          cbn [blk_addr blk_size fst snd] in DJ; clear - DJ; lia
        | exact OD | reflexivity | reflexivity | | ]. 
      - (* [comment removed for export] *)
        intros st' Σ' ms' PO.
        destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & OW2 & bo2 & NEW2 & -> & PRE2 & AXP2 & CRED2 & KEPT2 & FRESH2 & LBOK2 & SK2 & [ENEW OD2]).
        subst NEW2. cbn [app] in PRE2. cbn [fst snd] in PRE2, SK2, KEPT2 |- *. unfold MallocRep.wz in AXP2, OD2. rewrite ESPA in AXP2. rewrite (ret_pc_even 0x1f42e0) by (clear; lia).
        assert (HI2 : hinv Σ' st' m2 OW2 bo2 NEWk (spent + CST_I2D (zlength (sk_items k)))).
        { eapply (hinv_ap Σk stX mk OWk bok NEWk spent Σ' st' m2 OW2 bo2 NEWk [(f + 64, f + 64 + 8)] _ HI PRE2 AXP2);
            [intros x Hx; cbn [rin_ivs fst snd] in Hx; clear - Hx; lia| cbn [ar_RT push amb] in CRED2; exact CRED2| exact C0| clear - HC C0; unfold ERR_CLEAR_ERROR_COST in *; lia
            | exact (nf_of_heap _ _ _ _ _ (proj1 PRE2)) | exact LBOKk]. }
        eapply (har_cfree_none _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ' st' m2 OW2 bo2 _ NEWk adr k HI2 PM SK2 N31); [clear - HC C0; lia| exact OD2].
      - (* [comment removed for export] *)
        intros dp st' Σ' ms' PO.
        destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & OW2 & bo2 & NEW2 & -> & PRE2 & AXP2 & CRED2 & KEPT2 & FRESH2 & LBOK2 & SK2 & (AD & n & ENEW & Hn & OD2)).
        subst NEW2. cbn [app] in PRE2. cbn [fst snd] in PRE2, SK2, KEPT2 |- *. unfold MallocRep.wz in AXP2, OD2. rewrite ESPA in AXP2. rewrite (ret_pc_even 0x1f42e0) by (clear; lia).
        assert (HI2 : hinv Σ' st' m2 OW2 bo2 ((dp, AD, n) :: NEWk) (spent + CST_I2D (zlength (sk_items k)))).
        { eapply (hinv_ap Σk stX mk OWk bok NEWk spent Σ' st' m2 OW2 bo2 ((dp, AD, n) :: NEWk) [(f + 64, f + 64 + 8)] _ HI PRE2 AXP2);
            [intros x Hx; cbn [rin_ivs fst snd] in Hx; clear - Hx; lia| cbn [ar_RT push amb] in CRED2; exact CRED2| exact C0| clear - HC C0; unfold ERR_CLEAR_ERROR_COST in *; lia
            | exact (nf_of_heap _ _ ((dp, AD, n) :: NEWk) _ _ (proj1 PRE2)) | constructor; [apply Forall_inv in LBOK2; exact LBOK2| exact LBOKk]]. }
        eapply (har_cfree_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ' st' m2 OW2 bo2 _ NEWk adr k dp AD n HI2 PM SK2 N31); [clear - HC C0; lia| exact Hn| exact OD2]. }
    intros [u st'] Σ' ms' PO. cbn [fst snd]. exact (mid_free_elim adr k (u, st') Σ' ms' PO).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition T2 (k : skr bptr) (pb : bptr) (st : ap_st bptr) : aprog bptr (Z * ap_st bptr) := apbind (afree pb st) (fun p => T3 k (snd p)).

  Lemma har_bfree : forall (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32) Σk (stX : ap_st bptr) mk OWk bok spent NEWk (adr : bptr -> Z) (k : skr bptr)
      (pb : bptr) (A nxt prev nw : Z),
    hinv Σk stX mk ((pb, A, BIO_SIZE) :: OWk) bok NEWk spent -> Permutation NEWk (sk_blocks adr k) -> sk_repA mk (NEWk ++ pbs ++ LB) adr k -> zlength (sk_items k) < 2 ^ 31 ->
    (forall b, In b (pbs ++ LB) -> adr (blk_id b) = blk_addr b) ->
    pb <> p_xl E -> ~ In pb (es_ids stX ++ env_ids E) ->
    rw_cells ctasegs mk A (bio_cells NULL_METHOD 1 0 nxt prev nw) ->
    0 <= CST_I2D (zlength (sk_items k)) -> CST_I2D (zlength (sk_items k)) + BIO_FREE_NULL_COST_A + ERR_CLEAR_ERROR_COST <= BCOST - spent ->
    rw_cells ctasegs mk (f + 64) [C8 (wz 0)] ->
    implAp (T2 k pb stX) Σk FQ (bst x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 (wz (adr (sk_blk k))) (Z_to_bv 64 (f + 64)) (wz A) x28 x29 x30 x31 Fk fck mk HARA_BFREE).
  Proof.
    intros until nw. intros HI PM SK N31 ADR NXB NIDS HB C0 HC OD. pose proof HI as (PREk & AGSk & AXk & CRk & SP0k & NFk & LBOKk & FRLk & FRHk).
    pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0).
    pose proof HYPS as (_ & _ & _ & _ & _ & HBF & _).
    pose proof PREk as (HEAPk & ASk & IDSk & DCk & STk & _ & _ & _ & _ & MIk & CREDk & FRMk). rewrite ESPA in STk.
    pose proof ASk as (ENVk & SFk & _ & _ & HXLk & _).
    pose proof (env_in _ _ ENVk) as (_ & _ & _ & _ & HXIN).
    unfold bst, HARA_BFREE, MallocRep.wz in *. cbn [ar_PMc push amb].
    pose proof (munch_refl ([] : list (Z * Z)) mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
    apply implAp_from_evt. zstep. zstep. apply evt_done.
    unfold T2, afree. cbn [apbind fst snd].
    pose proof (@AH_nodup_l (push AR f 1) _ _ _ _ HEAPk) as NDl.
    eapply (HBF f) with (lo := lo) (E := E) (A := A) (nxt := nxt) (prev := prev) (nw := nw);
      [ exact HEAPk | left; reflexivity | exact NXB | rewrite ESPA; exact STk | exact CEIL
      | rewrite ESPA; unfold BIO_FREE_NULL_STACK_A, FREE_EX_DATA_STACK_A, CFED_FRAME, CRYPTO_FREE_STACK, RT_STACK; clear - LOSP SPAL; unfold CT_FUZZ_STACK_A, FUZZ_STACK in *; lia
      | rewrite ESPA; clear - SPAH TOP; unfold USTACK_TOP in *; lia | rewrite ESPA; clear - SPA32; Z.div_mod_to_equations; lia | exact MIk | reflexivity
      | cbn [ar_FR push amb length]; unfold BFRM, CT_FUZZ_FRAMES_A in FRMk; cbn [ar_FR push amb length] in FRMk; clear - FRMk; unfold FRAMES_MAX in *; lia
      | cbn [ar_RT push amb] in CREDk |- *; unfold BIO_FREE_NULL_COST_A, ERR_CLEAR_ERROR_COST in *; clear - CREDk HC C0; lia
      | exact SFk | exact HXLk | exact HXIN | unfold bio_cells, MallocRep.wz in HB |- *; exact HB
      | rewrite ESPA; exact (uw_callee mk AGSk FRHk)
      | exact (ctx_callee _ _ 0 E_bfree ltac:(apply unsigned_lit; clear; lia)) | reflexivity |].
    intros Σ' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & m5 & -> & MI5 & ST5 & AG5 & CR5 & HEAP5 & HXL5).
    rewrite ?ESPA in ST5, AG5. rewrite (ret_pc_even 0x1f42d0) by (clear; lia).
    rewrite (lb_remove_head (pb, A, BIO_SIZE) OWk NDl) in HEAP5, AG5.
    (* [comment removed for export] *)
    assert (ASr : ap_state stX mk OWk E bok).
    { rewrite <- (lb_remove_head (pb, A, BIO_SIZE) OWk NDl). apply ap_state_remove_other; [exact ASk| intros Hin; apply NIDS; apply in_or_app; right; exact Hin| intros Hin; apply NIDS; apply in_or_app; left; exact Hin]. }
    assert (DCr : data_cells mk OWk stX).
    { rewrite <- (lb_remove_head (pb, A, BIO_SIZE) OWk NDl). apply data_cells_remove_other; [exact DCk| intros Hin; apply NIDS; apply in_or_app; left; exact Hin]. }
    assert (AGL : agree_on (lib_addr OWk) mk m5).
    { eapply agree_on_mono; [exact AG5|]. intros a [Hs|(b & Hb & Hr)].
      - right; left. exact (ar_LIBW_cs a (LIBW_S_A a Hs)).
      - right; right. exists b. split; [apply in_or_app; left; exact Hb| exact Hr]. }
    assert (HI5 : hinv Σ' stX m5 OWk bok NEWk (spent + BIO_FREE_NULL_COST_A)).
    { split.
      { pose proof ASr as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & ODr)).
        pose proof PREk as (_ & _ & _ & _ & _ & CEILk & LOSPk & TOPk & AL16k & _ & _ & _).
        unfold ap_preA. split; [exact HEAP5|]. split; [exact (ap_state_agree _ _ _ _ _ _ ASr AGL)|]. split; [exact IDSk|].
        split; [exact (data_cells_agree _ _ _ _ DCr AGL ODr)|]. split; [rewrite ESPA; exact ST5|]. split; [exact CEILk|]. split; [exact LOSPk|].
        split; [exact TOPk|]. split; [exact AL16k|]. split; [exact MI5|]. split; [| exact FRMk].
        cbn [ar_RT push amb] in CREDk, CR5 |- *. unfold BIO_FREE_NULL_COST_A, ERR_CLEAR_ERROR_COST in *. clear - CREDk CRk CR5 HC C0. lia. }
      split. { eapply agree_on_trans; [exact AGSk|]. eapply agree_on_mono; [exact AG5|]. intros a Ha. left. clear - Ha SPAH; lia. }
      split. { eapply agree_on_trans; [exact AXk|]. eapply agree_on_mono; [exact AG5|]. intros a Ha. rewrite !app_assoc. exact (proj1 (proj2 (axw_spa a Ha)) ((OWk ++ NEWk) ++ pbs)). }
      split; [cbn [ar_RT push amb] in CR5; unfold BIO_FREE_NULL_COST_A in *; clear - CRk CR5; lia|]. split; [unfold BIO_FREE_NULL_COST_A in *; clear - SP0k; lia|].
      split; [intros b Hb Hin; apply (NFk b Hb); cbn [map app]; right; exact Hin|]. split; [exact LBOKk|].
      split; [eapply rw_cells_agree; [exact AG5| exact FRLk| intros a Ha; exact (proj1 (frl_acl _ a Ha))]|].
      eapply rw_cells_agree; [exact AG5| exact FRHk| intros a Ha; exact (proj1 (frh_acl _ a Ha))]. }
    apply (rw_cells_agree _ _ _ _ _ AG5) in OD; [| intros a Ha; cbn in Ha; right; right; exists (qd, f + 64, 8); split; [apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; unfold pbs, fto_pbs; right; left; reflexivity| cbn; clear - Ha; lia]].
    change (Z_to_bv 64 0x1f42d0) with (Z_to_bv 64 HARA_I2D).
    eapply (har_i2d _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 Σ' stX m5 OWk bok _ NEWk adr k HI5 PM); [| exact N31| exact ADR| exact C0| unfold BIO_FREE_NULL_COST_A in *; clear - HC; lia| exact OD].
    eapply sk_repA_agree; [exact AG5| | exact SK]. intros b a Hb Ha. right; right. exists b. split; [| exact Ha].
    apply in_or_app. right. apply in_or_app. left. eapply Permutation_in; [symmetry; exact PM| exact Hb].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition T1 (k : skr bptr) (pb : bptr) (st : ap_st bptr) : aprog bptr (Z * ap_st bptr) := apbind (sct_list_print k st) (fun p => T2 k pb (snd p)).

  Lemma har_print : forall (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32) Σk (stX : ap_st bptr) mk OWk bok spent NEWk (adr : bptr -> Z) (k : skr bptr)
      (pb : bptr) (A pv nw : Z),
    hinv Σk stX mk ((pb, A, BIO_SIZE) :: OWk) bok NEWk spent -> Permutation NEWk (sk_blocks adr k) -> sk_repA mk (NEWk ++ pbs ++ LB) adr k -> zlength (sk_items k) < 2 ^ 26 ->
    (forall b, In b (pbs ++ LB) -> adr (blk_id b) = blk_addr b) ->
    pb <> p_xl E -> ~ In pb (es_ids stX ++ env_ids E) ->
    rw_cells ctasegs mk A (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2 ^ 64 ->
    0 <= CST_I2D (zlength (sk_items k)) -> 0 <= CST_PRN (zlength (sk_items k)) ->
    CST_PRN (zlength (sk_items k)) + CST_I2D (zlength (sk_items k)) + BIO_FREE_NULL_COST_A + ERR_CLEAR_ERROR_COST <= BCOST - spent ->
    rw_cells ctasegs mk (f + 64) [C8 (wz 0)] ->
    2 + sk_wire k <= MAX_SCT_LIST_SIZE ->
    implAp (T1 k pb stX) Σk FQ (bst x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 (wz (adr (sk_blk k))) (Z_to_bv 64 (f + 64)) (wz A) x28 x29 x30 x31 Fk fck mk HARA_PRN).
  Proof.
    intros until nw. intros HI PM SK N26 ADR NXB NIDS HB NW C0 C0' HC OD WR2. pose proof HI as (PREk & AGSk & AXk & CRk & SP0k & NFk & LBOKk & FRLk & FRHk).
    pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0).
    pose proof HYPS as (_ & HPRN & _). pose proof BUD as (_ & BSTKP & _ & _ & _ & BFRMP & _).
    pose proof PREk as (HEAPk & ASk & IDSk & DCk & STk & _ & _ & _ & _ & MIk & CREDk & FRMk). rewrite ESPA in STk.
    unfold bst, HARA_PRN, MallocRep.wz in *. cbn [ar_PMc push amb].
    pose proof (munch_refl ([] : list (Z * Z)) mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
    apply implAp_from_evt. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
    unfold T1. eapply implAp_bind.
    { eapply (HPRN f) with (K := []) (LB := NEWk ++ pbs ++ LB) (lo := lo) (adr := adr) (pbio := pb) (out := A) (pv := pv) (nw := nw) (W := MAX_SCT_LIST_SIZE);
        [ eapply ap_preA_weaken; [exact PREk| unfold BSTK; clear - BSTKP; unfold CT_FUZZ_STACK_A, FUZZ_STACK, HAR_FRAME_A in *; lia
                                 | clear - C0 C0' HC; unfold BIO_FREE_NULL_COST_A, ERR_CLEAR_ERROR_COST in *; lia| unfold BFRM; clear - BFRMP; lia]
        | reflexivity
        | rewrite ESPA; exact (uw_callee mk AGSk FRHk)
        | exact (ctx_callee _ _ 0 E_prn ltac:(apply unsigned_lit; clear; lia))
        | apply cons_ne
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | exact SK
        | intros b Hb; apply in_app_iff in Hb; destruct Hb as [Hb|Hb]; [symmetry; apply (sk_blocks_adr adr k); eapply Permutation_in; [exact PM| exact Hb] | exact (ADR b Hb)]
        | left; reflexivity | exact NIDS
        | unfold bio_null_cells, bio_cells, MallocRep.wz in HB |- *; exact HB | exact NW
        | intros b Hb; destruct Hb | intros b Hb; destruct Hb | intros b Hb; destruct Hb
        | exact WR2 | apply Z.le_refl ]. }
    intros [u st'] Σ' ms' PO. cbn [fst snd].
    destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & OW2 & bo2 & -> & PRE2 & AXP2 & CRED2 & KEPT2 & (Er & EOW & nw2 & NW2 & HB2)).
    injection Er as Est. subst st' OW2. cbn [fst snd] in PRE2. unfold MallocRep.wz in AXP2, HB2. rewrite ?ESPA in AXP2. rewrite (ret_pc_even 0x1f42c8) by (clear; lia).
    assert (HI2 : hinv Σ' stX m2 ((pb, A, BIO_SIZE) :: OWk) bo2 NEWk (spent + CST_PRN (zlength (sk_items k)))).
    { eapply (hinv_ap Σk stX mk ((pb, A, BIO_SIZE) :: OWk) bok NEWk spent Σ' stX m2 _ bo2 NEWk [] _ HI PRE2); [cbn [app]; exact AXP2| intros x Hx; destruct Hx
        | cbn [ar_RT push amb] in CRED2; exact CRED2| exact C0'| clear - HC C0 C0'; unfold BIO_FREE_NULL_COST_A, ERR_CLEAR_ERROR_COST in *; lia | exact NFk | exact LBOKk]. }
    apply (rw_cells_agree _ _ _ _ _ AXP2) in OD;
      [| intros a Ha; cbn in Ha; split; [intros HR; pose proof (libw_below a HR) as HLB; clear - HLB Ha G4; unfold SEGTOP_A in *; lia|];
         right; right; exists (qd, f + 64, 8); split; [apply in_or_app; right; apply in_or_app; left; unfold pbs, fto_pbs; right; left; reflexivity| cbn; clear - Ha; lia]].
    change (Z_to_bv 64 0x1f42c8) with (Z_to_bv 64 HARA_BFREE).
    eapply (har_bfree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ' stX m2 OWk bo2 _ NEWk adr k pb A 0 pv nw2 HI2 PM);
      [| clear - N26; lia| exact ADR| exact NXB| exact NIDS| unfold bio_null_cells, bio_cells, MallocRep.wz in HB2 |- *; exact HB2| exact C0| clear - HC C0'; lia| exact OD].
    eapply sk_repA_agree; [exact AXP2| | exact SK]. intros b a Hb Ha.
    assert (HbN : In b NEWk) by (eapply Permutation_in; [symmetry; exact PM| exact Hb]).
    split; [| right; right; exists b; split; [apply in_or_app; left; exact HbN| exact Ha]].
    intros HR. pose proof (libw_below a HR) as HLB.
    pose proof (@AH_range_gen (push AR f 1) _ _ _ _ b HEAPk ltac:(apply in_or_app; right; apply in_or_app; left; exact HbN)) as (R1 & _ & _ & R4 & R5).
    revert HR Ha R1 R4 R5. unfold LIBW_A. cbn [rin_ivs fst snd]. clear. intros; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ct_kk_some_eq : forall (k : skr bptr) (st : ap_st bptr),
    ct_kk (Some k) st = apbind (amalloc SZ_BIO st) (fun p => T1 k (fst p) (snd p)).
  Proof.
    intros k st. unfold ct_kk, ct_after, ct_tail, T1, T2, T3, T4, abind. cbv beta.
    rewrite !apbind_assoc. f_equal. apply functional_extensionality. intros [pb st1]. cbn [fst snd].
    rewrite !apbind_assoc. f_equal. apply functional_extensionality. intros [u st2]. cbn [fst snd].
    rewrite !apbind_assoc. f_equal. apply functional_extensionality. intros [u2 st3]. cbn [fst snd].
    rewrite !apbind_assoc. f_equal.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma har_some : forall (x5 x6 x7 a1 a2 a3 a4 a5 a6 a7 s3v s4v s5v x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32) Σk (stX : ap_st bptr) mk OWk bok spent NEWk (adr : bptr -> Z) (k : skr bptr),
    hinv Σk stX mk OWk bok NEWk spent -> Permutation NEWk (sk_blocks adr k) -> sk_repA mk (NEWk ++ pbs ++ LB) adr k -> zlength (sk_items k) < 2 ^ 26 ->
    (forall b, In b (pbs ++ LB) -> adr (blk_id b) = blk_addr b) ->
    0 <= CST_I2D (zlength (sk_items k)) -> 0 <= CST_PRN (zlength (sk_items k)) ->
    CST_PRN (zlength (sk_items k)) + CST_I2D (zlength (sk_items k)) + BIO_NEW_NULL_COST_A + BIO_FREE_NULL_COST_A + ERR_CLEAR_ERROR_COST <= BCOST - spent ->
    rw_cells ctasegs mk (f + 64) [C8 (wz 0)] ->
    2 + sk_wire k <= MAX_SCT_LIST_SIZE ->
    implAp (ct_kk (Some k) stX) Σk FQ (bst (Z_to_bv 64 HARA_RET1) x5 x6 x7 (wz (adr (sk_blk k))) a1 a2 a3 a4 a5 a6 a7 s3v s4v s5v x28 x29 x30 x31 Fk fck mk HARA_RET1).
  Proof.
    intros until k. intros HI PM SK N26 ADR C0 C0' HC OD WR2. pose proof HI as (PREk & AGSk & AXk & CRk & SP0k & NFk & LBOKk & FRLk & FRHk).
    pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0).
    pose proof HYPS as (_ & _ & _ & _ & HBN & _ & _).
    pose proof PREk as (HEAPk & ASk & IDSk & DCk & STk & CEILk & LOSPk & TOPk & AL16k & MIk & CREDk & FRMk). rewrite ESPA in STk.
    pose proof ASk as (ENVk & SFk & _ & _ & HXLk & _ & (_ & _ & _ & _ & ODk)).
    pose proof (env_in _ _ ENVk) as (_ & _ & _ & _ & HXIN).
    (* [comment removed for export] *)
    assert (SKIN : In (sk_blk k, adr (sk_blk k), STACK_SIZE) NEWk).
    { eapply Permutation_in; [symmetry; exact PM|]. unfold CtSctP.SctStmt.sk_blocks. rewrite !in_app_iff. right; right; left; reflexivity. }
    pose proof (@AH_range_gen (push AR f 1) _ _ _ _ _ HEAPk ltac:(apply in_or_app; right; apply in_or_app; left; exact SKIN)) as (K0 & _ & _ & KC & _). cbn [blk_addr blk_size fst snd] in K0, KC.
    assert (EK : bv_unsigned (Z_to_bv 64 (adr (sk_blk k))) = adr (sk_blk k)) by (apply unsigned_lit; clear - K0 KC C3; unfold BnHeapA.ACEIL, STACK_SIZE in *; cbn [ar_SP0 push amb] in *; alia).
    assert (Ef64 : bv_unsigned (Z_to_bv 64 (f + 64)) = f + 64) by (apply unsigned_lit; clear - G1 G3 C3; alia).
    unfold bst, HARA_RET1, MallocRep.wz in *. cbn [ar_PMc push amb].
    pose proof (munch_refl [(spa - 16, spa)]%Z mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?EK in KZ; clear - KZ K0; lia|]. clear KZ.
    zstep. zstep. zstep.
    eapply evt_cut. { eapply BIO_s_null_specA with (lo := lo); [rewrite ESPA; exact STk| exact MIk| clear - C1 CEIL; lia| rewrite ESPA; clear - LOSP SPAL; unfold CT_FUZZ_STACK_A, FUZZ_STACK in *; lia]. }
    intros ms4 (m4 & -> & MU4 & WM4 & MI4 & ST4). rewrite ?ESPA in MU4, ST4. rewrite (ret_pc_even 0x1f429c) by (clear; lia).
    assert (WOK : Forall (@BnHeapA.aclient_write_ok (push AR f 1) (OWk ++ NEWk ++ pbs ++ LB)) [(spa - 16, spa)]%Z).
    { constructor; [| constructor]. left. cbn [fst snd ar_SP0 push amb]. unfold BnHeapA.ACEIL, CT_FUZZ_STACK_A, FUZZ_STACK in *. cbn [ar_SP0 push amb]. clear - CEIL LOSP SPAL SPAH TOP. lia. }
    pose proof (@AH_frame (push AR f 1) _ _ _ _ m4 _ HEAPk MU4 WM4 WOK) as HEAP4.
    assert (AG4 : agree_on (fun a => spa <= a \/ a < lo) mk m4).
    { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU4)|]. intros a Ha. cbn [outside fst snd]. clear - Ha CEIL LOSP SPAL; unfold CT_FUZZ_STACK_A, FUZZ_STACK in *; lia. }
    assert (AGL4 : agree_on (lib_addr OWk) mk m4).
    { eapply agree_on_mono; [exact AG4|]. intros a [Hs|(b & Hb & Hr)].
      - right. pose proof (LIBW_S_A a Hs) as Hl. pose proof (libw_below a Hl) as Hb. clear - Hb C1 CEIL. lia.
      - right. pose proof (@AH_range_gen (push AR f 1) _ _ _ _ b HEAPk ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & R4 & _).
        unfold BnHeapA.ACEIL in R4, CEIL. cbn [ar_SP0 push amb] in R4. clear - Hr R4 CEIL. lia. }
    pose proof (munch_refl ([] : list (Z * Z)) m4) as MU5. pose proof (wmono_refl ctasegs m4) as WM5.
    zstep.   (* [comment removed for export] *)
    apply evt_done. rewrite ct_kk_some_eq. cbn [apbind amalloc].
    eapply (HBN f) with (lo := lo) (E := E);
      [ exact HEAP4 | rewrite ESPA; exact ST4 | exact CEIL
      | rewrite ESPA; unfold BIO_NEW_NULL_STACK_A, NEW_EX_DATA_STACK_A, CNED_FRAME, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LOSP SPAL; unfold CT_FUZZ_STACK_A, FUZZ_STACK in *; lia
      | rewrite ESPA; clear - SPAH TOP; unfold USTACK_TOP in *; lia | rewrite ESPA; clear - SPA32; Z.div_mod_to_equations; lia | exact MI4 | reflexivity
      | cbn [ar_FR push amb length]; unfold BFRM, CT_FUZZ_FRAMES_A in FRMk; cbn [ar_FR push amb length] in FRMk; clear - FRMk; unfold FRAMES_MAX in *; lia
      | cbn [ar_RT push amb] in CREDk |- *; unfold BIO_NEW_NULL_COST_A, BIO_FREE_NULL_COST_A, ERR_CLEAR_ERROR_COST in *; clear - CREDk HC C0 C0'; lia
      | exact (ap_statics_fixed_agree _ _ _ _ SFk AGL4)
      | unfold exlock_free in HXLk |- *; eapply rw_cells_agree; [exact AG4| exact HXLk|]; intros a Ha; right;
        pose proof (@AH_range_gen (push AR f 1) _ _ _ _ _ HEAPk ltac:(apply in_or_app; left; exact HXIN)) as (_ & _ & _ & R4 & _);
        cbn [blk_addr blk_size fst snd] in R4; unfold BnHeapA.ACEIL, MUTEX_SIZE in R4, CEIL; cbn [ar_SP0 push amb] in R4; cbn in Ha; clear - Ha R4 CEIL; lia
      | exact HXIN
      | rewrite ESPA; apply uw_callee; [eapply agree_on_trans; [exact AGSk| eapply agree_on_mono; [exact AG4|]; intros a Ha; left; clear - Ha SPAH; lia]
                                       | eapply rw_cells_agree; [exact AG4| exact FRHk| intros a Ha; cbn in Ha; left; clear - Ha SPAH; lia]]
      | exact (ctx_callee _ _ 0 E_bnew ltac:(apply unsigned_lit; clear; lia)) | reflexivity |].
    intros pb Σ' ms' Hpb PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F5 & fc5 & m5 & A & -> & MI5 & ST5 & AG5 & CR5 & BR5 & HEAP5 & HB5 & HXL5).
    rewrite ?ESPA in ST5, AG5. rewrite (ret_pc_even 0x1f42a0) by (clear; lia). cbn [apbind fst snd].
    pose proof BR5 as (A0 & A16 & _ & ACE & _). unfold BnHeapA.ACEIL, BIO_SIZE in ACE. cbn [ar_SP0 push amb] in ACE.
    assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; clear - A0 ACE C3; alia).
    assert (NIO : ~ In pb (map blk_id OWk)) by (intros Hin; apply Hpb; rewrite map_app; apply in_or_app; left; exact Hin).
    assert (NIDS : ~ In pb (es_ids stX ++ env_ids E)) by (eapply fresh_not_ids; [exact (ids_in_introA _ _ _ _ _ ASk)| exact Hpb]).
    assert (NXB : pb <> p_xl E) by (intros ->; apply NIO; exact (in_map blk_id _ _ HXIN)).
    assert (AGL5 : agree_on (lib_addr OWk) m4 m5) by (eapply aclient_lib; exact AG5).
    assert (ACL4 : forall a, aclient_addr (OWk ++ NEWk ++ pbs ++ LB) spa a -> spa <= a \/ a < lo).
    { intros a [H1|[H1|(b & Hb & Hr)]]; [left; clear - H1; lia| right; pose proof (csb a H1) as Hb; clear - Hb C1 CEIL; lia| right].
      pose proof (@AH_range_gen (push AR f 1) _ _ _ _ b HEAPk Hb) as (_ & _ & _ & R4 & _). unfold BnHeapA.ACEIL in R4, CEIL. cbn [ar_SP0 push amb] in R4. clear - Hr R4 CEIL. lia. }
    assert (AGB : agree_on (aclient_addr (OWk ++ NEWk ++ pbs ++ LB) spa) mk m5).
    { eapply agree_on_trans; [eapply agree_on_mono; [exact AG4| exact ACL4]| exact AG5]. }
    assert (HI5 : hinv Σ' stX m5 ((pb, A, BIO_SIZE) :: OWk) bok NEWk (spent + BIO_NEW_NULL_COST_A)).
    { split.
      { unfold ap_preA. split; [exact HEAP5|].
        split; [apply ap_state_cons_fresh; [exact (ap_state_agree _ _ _ _ _ _ (ap_state_agree _ _ _ _ _ _ ASk AGL4) AGL5)| exact NIO| exact A0| unfold BIO_SIZE; clear - ACE C3; alia| exact A16]|].
        split; [exact IDSk|].
        split; [apply data_cells_cons_fresh; [exact (data_cells_agree _ _ _ _ (data_cells_agree _ _ _ _ DCk AGL4 ODk) AGL5 ODk)| exact ODk| exact NIO]|].
        split; [rewrite ESPA; exact ST5|]. split; [exact CEILk|]. split; [exact LOSPk|]. split; [exact TOPk|]. split; [exact AL16k|]. split; [exact MI5|]. split; [| exact FRMk].
        cbn [ar_RT push amb] in CREDk, CR5 |- *. unfold BIO_NEW_NULL_COST_A, BIO_FREE_NULL_COST_A, ERR_CLEAR_ERROR_COST in *. clear - CREDk CRk CR5 HC C0 C0'. lia. }
      split. { eapply agree_on_trans; [exact AGSk|]. eapply agree_on_mono; [exact AGB|]. intros a Ha. left. clear - Ha SPAH; lia. }
      split. { eapply agree_on_trans; [exact AXk|]. eapply agree_on_mono; [exact AGB|]. intros a Ha. rewrite !app_assoc. exact (proj1 (proj2 (axw_spa a Ha)) ((OWk ++ NEWk) ++ pbs)). }
      split; [cbn [ar_RT push amb] in CR5; unfold BIO_NEW_NULL_COST_A in *; clear - CRk CR5; lia|]. split; [unfold BIO_NEW_NULL_COST_A in *; clear - SP0k; lia|].
      split. { intros b Hb Hin. cbn [map app] in Hin. destruct Hin as [E0|Hin]; [| exact (NFk b Hb Hin)].
               cbn in E0. apply Hpb. rewrite E0. rewrite !map_app. apply in_or_app. right. apply in_or_app. left. exact (in_map blk_id _ _ Hb). }
      split; [exact LBOKk|].
      split; [eapply rw_cells_agree; [exact AGB| exact FRLk| intros a Ha; exact (proj1 (frl_acl _ a Ha))]|].
      eapply rw_cells_agree; [exact AGB| exact FRHk| intros a Ha; exact (proj1 (frh_acl _ a Ha))]. }
    (* [comment removed for export] *)
    assert (BLO : forall b a, In b (NEWk ++ pbs ++ LB) -> blk_addr b <= a < blk_addr b + blk_size b -> aclient_addr (OWk ++ NEWk ++ pbs ++ LB) spa a).
    { intros b a Hb Hr. right; right. exists b. split; [apply in_or_app; right; exact Hb| exact Hr]. }
    apply (rw_cells_agree _ _ _ _ _ AGB) in OD; [| intros a Ha; cbn in Ha; apply (BLO (qd, f + 64, 8)); [apply in_or_app; right; apply in_or_app; left; unfold pbs, fto_pbs; right; left; reflexivity| cbn; clear - Ha; lia]].
    assert (SK5 : sk_repA m5 (NEWk ++ pbs ++ LB) adr k).
    { eapply sk_repA_agree; [exact AGB| | exact SK]. intros b a Hb Ha. apply (BLO b); [apply in_or_app; left; eapply Permutation_in; [symmetry; exact PM| exact Hb]| exact Ha]. }
    (* [comment removed for export] *)
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU6. pose proof (wmono_refl ctasegs m5) as WM6.
    apply implAp_from_evt. zstep. if_cases KB; zify_cond KB; [exfalso; rewrite ?EA in KB; clear - KB A0; lia|]. clear KB.
    zstep. apply evt_done.
    change (Z_to_bv 64 2048680) with (Z_to_bv 64 HARA_PRN).
    eapply (har_print _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 Σ' stX m5 OWk bok _ NEWk adr k pb A 0 0 HI5 PM SK5 N26 ADR NXB NIDS);
      [unfold bio_null_cells, bio_cells, MallocRep.wz in HB5 |- *; exact HB5| clear; lia| exact C0| exact C0'| unfold BIO_NEW_NULL_COST_A in *; clear - HC; lia| exact OD| exact WR2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma har_none : forall (x5 x6 x7 a1 a2 a3 a4 a5 a6 a7 s3v s4v s5v x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32) Σk (stX : ap_st bptr) mk OWk bok spent,
    hinv Σk stX mk OWk bok [] spent -> ERR_CLEAR_ERROR_COST <= BCOST - spent ->
    implAp (ct_kk None stX) Σk FQ (bst (Z_to_bv 64 HARA_RET1) x5 x6 x7 (wz 0) a1 a2 a3 a4 a5 a6 a7 s3v s4v s5v x28 x29 x30 x31 Fk fck mk HARA_RET1).
  Proof.
    intros until spent. intros HI HC. pose proof HI as (PREk & AGSk & AXk & CRk & SP0k & NFk & LBOKk & FRLk & FRHk).
    unfold ct_kk, ct_after, aret, abind. cbn [apbind fst snd]. fold (ct_tail stX).
    unfold bst, HARA_RET1, MallocRep.wz in *. cbn [ar_PMc push amb].
    pose proof (munch_refl ([] : list (Z * Z)) mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
    apply implAp_from_evt. zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity]. clear KZ.
    apply evt_done. change (Z_to_bv 64 2048768) with (Z_to_bv 64 HARA_CLR).
    exact (har_clr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fk fck Σk stX mk OWk bok spent HI HC).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma har_d2i : forall (x1 x5 x6 x7 a3 a4 a5 a6 a7 s5v x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32) mk (adr : bptr -> Z),
    hinv Σ1 st0 mk OW bo [] 0 ->
    (forall b, In b (pbs ++ LB) -> adr (blk_id b) = blk_addr b) ->
    payload_okA mk (pbs ++ LB) D d ->
    rw_cells ctasegs mk (f + 32) [C8 (wz D)] -> rw_cells ctasegs mk (f + 64) [C8 (wz 0)] ->
    implAp (ct_call d st0) Σ1 FQ (bst x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 (f + 32)) (wz (zlength d)) a3 a4 a5 a6 a7 (wz (zlength d)) (wz D) s5v x28 x29 x30 x31 Fk fck mk FTO_BODY).
  Proof.
    intros until adr. intros HI ADR PAYk OB OD. pose proof HI as (PREk & AGSk & AXk & CRk & SP0k & NFk & LBOKk & FRLk & FRHk).
    pose proof base_facts as (SPR & C1 & C2 & C3 & CEIL & LO0 & LOSP & TOP & AL16 & G1 & G2 & G3 & G4 & G5 & ESPA & Ef & CRED0).
    pose proof HYPS as (HD2I & _). pose proof BUD as (BSTKD & _ & _ & _ & BFRMD & _ & _ & BCD & BCP & BCI).
    pose proof PREk as (HEAPk & ASk & IDSk & DCk & STk & _ & _ & _ & _ & MIk & CREDk & FRMk). rewrite ESPA in STk.
    pose proof PAY as (_ & _ & D0 & D63 & D26 & _).
    pose proof (BCD (zlength d) ltac:(clear - D26; unfold zlength in *; lia)) as [CD0 CD1].
    rewrite ct_call_tree. unfold bst, FTO_BODY, MallocRep.wz in *. cbn [ar_PMc push amb].
    pose proof (munch_refl ([] : list (Z * Z)) mk) as MU. pose proof (wmono_refl ctasegs mk) as WM.
    apply implAp_from_evt. zstep. apply evt_done.
    cbn [app] in HEAPk.
    eapply (HD2I f) with (KK := ct_kk) (K := []) (LB := pbs ++ LB) (lo := lo) (adr := adr) (D := D) (PIN := f + 32);
      [ eapply ap_preA_weaken; [exact PREk| unfold BSTK; clear - BSTKD; unfold CT_FUZZ_STACK_A, FUZZ_STACK, HAR_FRAME_A in *; lia
                                 | unfold BCOST, CT_FUZZ_COST_A, FUZZ_COST; clear - CD0 CD1; lia| unfold BFRM; clear - BFRMD; lia]
      | reflexivity
      | rewrite ESPA; exact (uw_callee mk AGSk FRHk)
      | exact (ctx_callee _ _ 0 E_d2i ltac:(apply unsigned_lit; clear; lia))
      | apply cons_ne
      | intros b Hb; destruct Hb | intros b Hb; destruct Hb
      | exact PAYk | exact ADR
      | exists (qb, f + 32, 8); split; [apply in_or_app; left; unfold pbs, fto_pbs; left; reflexivity| cbn; clear; lia]
      | clear - G2; Z.div_mod_to_equations; lia
      | destruct PAY as (_ & _ & _ & _ & _ & [Hd|(b & Hb & R1 & R2)]); [left; exact Hd| right];
        pose proof (OFFLB b Hb) as O; unfold off_fr in O; change (fs_size 1) with 128 in O; clear - O R1 R2; lia
      | exact OB | reflexivity | reflexivity | reflexivity |].
    intros ok st' Σ' ms' PO. pose proof (D2I_WIRE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PO) as WR.
    destruct PO as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & OW2 & bo2 & adr2 & NEW2 & -> & PRE2 & AXP2 & CRED2 & KEPT2 & ADR2 & FRESH2 & LBOK2 & RES2).
    unfold MallocRep.wz in AXP2, RES2 |- *. rewrite ?ESPA in AXP2. rewrite (ret_pc_even 0x1f4288) by (clear; lia). cbn [fst snd] in PRE2, KEPT2.
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AXP2) in OD;
      [| intros a Ha; cbn in Ha; split; [cbn [rin_ivs fst snd app]; unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha G4; unfold SEGTOP_A in *; lia|];
         right; right; exists (qd, f + 64, 8); split; [apply in_or_app; left; unfold pbs, fto_pbs; right; left; reflexivity| cbn; clear - Ha; lia]].
    destruct ok as [k|]; [destruct WR as [WN3 WR2]| clear WR].
    - destruct RES2 as (PM & SK2 & HPIN & NK).
      assert (N26 : zlength (sk_items k) < 2 ^ 26) by (clear - WN3; unfold MAX_SCT_LIST_SIZE in WN3; lia).
      pose proof (BCP (zlength (sk_items k)) ltac:(clear - N26; unfold zlength in *; lia)) as [CP0 CP1].
      pose proof (BCI (zlength (sk_items k)) ltac:(clear - N26; unfold zlength in *; lia)) as [CI0 CI1].
      assert (HI2 : hinv Σ' st' m2 OW2 bo2 NEW2 (0 + CST_D2I (zlength d))).
      { eapply (hinv_ap Σ1 st0 mk OW bo [] 0 Σ' st' m2 OW2 bo2 NEW2 [(f + 32, f + 32 + 8)] _ HI PRE2); [cbn [app]; exact AXP2| intros x Hx; cbn [rin_ivs fst snd] in Hx; clear - Hx; lia
          | cbn [ar_RT push amb] in CRED2; exact CRED2| exact CD0| unfold BCOST, CT_FUZZ_COST_A, FUZZ_COST; clear - CD1; lia
          | exact FRESH2 | exact LBOK2]. }
      change (Z_to_bv 64 2048648) with (Z_to_bv 64 HARA_RET1).
      eapply (har_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ' st' m2 OW2 bo2 _ NEW2 adr2 k HI2 PM); 
        [| exact N26| intros b Hb; rewrite (ADR2 b Hb); exact (ADR b Hb)| exact CI0| exact CP0
         | unfold BCOST, CT_FUZZ_COST_A, FUZZ_COST, BIO_NEW_NULL_COST_A, BIO_FREE_NULL_COST_A, ERR_CLEAR_ERROR_COST; clear - CD1 CP1 CI1; lia| exact OD| exact WR2].
      eapply sk_repA_relist; [exact SK2|]. intros b Hb. apply in_or_app. left. eapply Permutation_in; [symmetry; exact PM| exact Hb].
    - destruct RES2 as (ENEW & _). subst NEW2.
      assert (HI2 : hinv Σ' st' m2 OW2 bo2 [] (0 + CST_D2I (zlength d))).
      { eapply (hinv_ap Σ1 st0 mk OW bo [] 0 Σ' st' m2 OW2 bo2 [] [(f + 32, f + 32 + 8)] _ HI PRE2); [cbn [app]; exact AXP2| intros x Hx; cbn [rin_ivs fst snd] in Hx; clear - Hx; lia
          | cbn [ar_RT push amb] in CRED2; exact CRED2| exact CD0| unfold BCOST, CT_FUZZ_COST_A, FUZZ_COST; clear - CD1; lia
          | intros b Hb; destruct Hb | constructor]. }
      change (Z_to_bv 64 2048648) with (Z_to_bv 64 HARA_RET1).
      eapply (har_none _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 Σ' st' m2 OW2 bo2 _ HI2).
      unfold BCOST, CT_FUZZ_COST_A, FUZZ_COST, ERR_CLEAR_ERROR_COST. clear - CD1. lia.
  Qed.

End Act.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fuzz_walkA : forall (STK_D2I : Z) (CST_D2I : Z -> Z) (FRM_D2I : Z) (STK_PRN : Z) (CST_PRN : Z -> Z) (FRM_PRN : Z) (STK_I2D : Z) (CST_I2D : Z -> Z) (FRM_I2D : Z) (STK_FREE : Z),
  @har_goalA AR UK STK_D2I CST_D2I FRM_D2I STK_PRN CST_PRN FRM_PRN STK_I2D CST_I2D FRM_I2D STK_FREE.
Proof.
  intros until STK_FREE. intros BUD HYPS. unfold ct_fuzz_stmtA. intros until d. intros PRE TP UW CTX PAY -> ->.
  pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
  unfold CT_FUZZ_ENTRY_A, MallocRep.wz in *. subst tp.
  intros X Φ Dl SAFE LINK.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply cps_from_evt'. step. apply evt_done.
  change (Z_to_bv 64 2048352) with (Z_to_bv 64 FTO_ENTRY).
  eapply (fto_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP | exact ST | exact CEIL | unfold FTO_FRAME, RT_STACK, CT_FUZZ_STACK_A, FUZZ_STACK in *; clear - LOSP; lia | exact TOP | exact AL16 | exact MI | reflexivity
    | unfold CT_FUZZ_FRAMES_A in FRM; clear - FRM; unfold FRAMES_MAX in *; lia | unfold CT_FUZZ_COST_A, FUZZ_COST in CRED; clear - CRED; lia |].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 jf24 jf40 jf72 jst HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold MallocRep.wz in FRL, FRH, FRF.
  pose proof (pro_closeA Σ (st_of_ls ls) m OW LB E bo sp lo _ _ _ f 1%nat Σ1 m3 spa 96 PRE HEAP3 ST3 MI3 AGF CR1 SPA32
                ltac:(clear - SPAL; lia) ltac:(clear - SPAH; lia) ltac:(clear; lia) ltac:(unfold CT_FUZZ_STACK_A, FUZZ_STACK; clear; lia)
                ltac:(unfold CT_FUZZ_COST_A, FUZZ_COST; clear; lia) ltac:(unfold CT_FUZZ_FRAMES_A, FRAMES_MAX; clear; cbn; lia)) as PRE1.
  destruct (fto_open_pbs Σ1 OW LB m3 f jst HEAP3 FRESH GEO FRS) as (qb & qd & HEAPX & QBF & QDF & QBD).
  (* [comment removed for export] *)
  lazymatch type of FRF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: nil) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: nil) with ([c0; c1; c2; c3] ++ [c4] ++ [c5] ++ [c6] ++ [c7]) in FRF end.
  apply rw_cells_app in FRF as [_ FRF]. apply rw_cells_app in FRF as [OB FRF]. apply rw_cells_app in FRF as [_ FRF]. apply rw_cells_app in FRF as [OD _].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in OB, OD.
  replace (f + Z.of_nat 32) with (f + 32) in OB by (clear; lia). replace (f + 32 + 8 + 24) with (f + 64) in OD by (clear; lia).
  (* [comment removed for export] *)
  pose proof PRE1 as (HEAP1 & AS1 & IDS1 & DC1 & ST1 & CEIL1 & LOSP1 & TOP1 & AL161 & MI1 & CRED1 & FRM1).
  assert (HI0 : hinv ra sp s0 m LB E lo d Σ1 m3 f spa g junk j0 qb qd Σ1 (st_of_ls ls) m3 OW bo [] 0).
  { split.
    { unfold ap_preA. cbn [app]. split; [exact HEAPX|]. split; [exact AS1|]. split; [exact IDS1|]. split; [exact DC1|]. split; [exact ST1|]. split; [exact CEIL1|].
      split; [exact LOSP1|]. split; [exact TOP1|]. split; [exact AL161|]. split; [exact MI1|]. split; [clear - CRED1; lia| exact FRM1]. }
    split; [eapply agree_on_mono; [exact AGF|]; intros a Ha; left; exact Ha|].
    split; [apply agree_on_refl|]. split; [clear; lia|]. split; [clear; lia|]. split; [intros b Hb; destruct Hb|]. split; [constructor|]. split; [exact FRL| exact FRH]. }
  assert (ADR0 : forall b, In b (fto_pbs f qb qd ++ LB) -> badr (fto_pbs f qb qd ++ LB) (blk_id b) = blk_addr b).
  { pose proof (@AH_nodup (push AR f 1) _ _ _ _ HEAPX) as ND. rewrite map_app in ND. pose proof (nodup_app_r _ _ ND) as NDL.
    intros [[q A] n] Hb. cbn [blk_id blk_addr fst snd]. exact (badr_in _ _ _ _ NDL Hb). }
  assert (PAY3 : payload_okA m3 (fto_pbs f qb qd ++ LB) D d).
  { eapply payload_okA_monoA; [| intros b Hb; apply in_or_app; right; exact Hb].
    eapply payload_okA_agreeA; [exact PAY|]. eapply agree_on_mono; [exact AGF|]. intros a Ha. right; right. eapply in_block_mono; [| exact Ha]. intros b Hb; apply in_or_app; right; exact Hb. }
  (* [comment removed for export] *)
  eapply (implAp_elim (ct_call d (st_of_ls ls))); [| exact SAFE | exact LINK | exact EL1].
  eapply har_d2i; try eassumption.
Qed.
End WithRT.
