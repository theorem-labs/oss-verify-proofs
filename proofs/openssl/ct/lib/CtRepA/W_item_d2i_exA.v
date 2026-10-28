(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse ApPrim.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA W_check_tlenA
     W_item_d2i_stmtA W_item_d2i_imgA W_c2i_stmtA W_frkitA Fr_asn1_check_tlen Fr_asn1_d2i_ex_primitive.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require W_get_object_walkA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
(* [comment removed for export] *)
Local Ltac shchk s := ab_shload s; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; if_false.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
(* [comment removed for export] *)
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Local Definition hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Local Ltac freeze H := lazymatch type of H with ?T => change T with (frozen T) in H end.

Import CtRepP.W_get_object(land_32_cases, go_ret_cases, go_cls_cases, go_tag_range).
Import CtRepP.W_get_object_walk(signed_small, zxb_lit).
Notation go_ret_prim := CtRepP.W_check_tlen.go_ret_prim.
Notation tlc_in := CtRepP.W_check_tlen.tlc_in.
Notation payload_readA := CtRepA.W_get_object_walkA.payload_readA.

(* [comment removed for export] *)
Definition EX_MEMSET_RA : Z := 0x2419f8.
Definition EX_CT_RA : Z := 0x241b70.        (* [comment removed for export] *)
Definition EX_INT_ARM : Z := 0x241f2c.
Definition EX_OCT_ARM : Z := 0x242078.

(* [comment removed for export] *)
Definition EXPRIM_STACK_A : Z := ADEP_FRAME + CHECK_TLEN_STACK_A.
Definition EXPRIM_COST_A (plen : Z) : Z := 2 + GETOBJ_ERR_COST_A + mcost plen.
Definition EXPRIM_SPENT_A (plen : Z) : Z := 7 + mcost plen.
Definition EXPRIM_FRAMES_A : Z := 1 + CHECK_TLEN_FRAMES_A.

Lemma mcost_nonneg : forall n, 0 <= n -> 0 <= mcost n.
Proof. intros n H. unfold mcost. destruct (Z.leb_spec n 64512); lia. Qed.

Lemma land64_neg_small : forall z, - 2 ^ 64 <= z < 0 -> Z.land z 18446744073709551615 = z + 2 ^ 64.
Proof.
  intros z Hz. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite <- (Z.mod_add z 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma land64_pos_small : forall z, 0 <= z < 2 ^ 64 -> Z.land z 18446744073709551615 = z.
Proof. intros z Hz. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma cb_splitA : forall m a (n1 n2 : nat) j,
  rw_cells ctasegs m a [CB (n1 + n2) j] -> rw_cells ctasegs m a [CB n1 (firstn n1 j); CB n2 (skipn n1 j)].
Proof.
  intros m a n1 n2 j H. pose proof H as [[W _] _]. cbn in W. destruct W as [L _].
  eapply rw_cells_recast; [exact H| cbn; rewrite length_firstn, length_skipn; repeat split; lia| | cbn; lia].
  cbn [cells_bytes cbytes app]. rewrite !app_nil_r. apply firstn_skipn.
Qed.
Lemma cb_byteA : forall m a j, rw_cells ctasegs m a [CB 1 j] -> exists b, rw_cells ctasegs m a [C1 b].
Proof.
  intros m a j H. pose proof H as [[W _] _]. cbn in W. destruct W as [L _].
  destruct j as [|b [|]]; cbn in L; try lia. exists b.
  eapply rw_cells_recast; [exact H| cbn; auto| reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma d2i_prim_octE : forall (d : list Z) (op totlen utype : Z) (st : ap_st bptr),
  go_err (get_object d op totlen) = None -> utype = V_ASN1_OCTET_STRING ->
  d2i_prim d op totlen utype st
  = abind (amalloc SZ_ASN1_STRING) (fun blk =>
      if go_len (get_object d op totlen) =? 0 then aret (Some (mkStr blk None))
      else abind (amalloc (go_len (get_object d op totlen))) (fun dp => aret (Some (mkStr blk (Some (dp, go_len (get_object d op totlen))))))) st.
Proof. intros d op totlen utype st EG ->. unfold d2i_prim. rewrite EG, Z.eqb_refl. reflexivity. Qed.
Lemma d2i_prim_intE : forall (d : list Z) (op totlen utype : Z) (st : ap_st bptr),
  go_err (get_object d op totlen) = None -> (utype =? V_ASN1_OCTET_STRING) = false ->
  d2i_prim d op totlen utype st = c2i_int_fragA d (go_p (get_object d op totlen)) (go_len (get_object d op totlen)) st.
Proof. intros d op totlen utype st EG EU. unfold d2i_prim, c2i_int_fragA. rewrite EG, EU. reflexivity. Qed.

Section MemsetFr.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memset_fr_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (Σ : rts RT) (OW LB : list block) (lo D N : Z) (c : byte) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ wmono ctasegs m m'
    /\ agree_on (fun a => (aclient_addr (OW ++ LB) (bv_unsigned sp) a \/ fr_addr a) /\ ~ (D <= a < D + N)) m m'
    /\ bytes_at ctasegs m' D (repeat c (Z.to_nat N)) /\ wr_at ctasegs m' D N.

Lemma asan_memset_frA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo d n : Z) (c : byte) (bd : block),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  In bd (OW ++ LB) -> blk_addr bd <= d -> d + n <= blk_addr bd + blk_size bd -> 0 <= n < 2^40 ->
  a0 = wz d -> a1 = wz (bv_unsigned c) -> a2 = wz n ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz e_asan_memset) fc None m (seg_rom ctasegs))))
            (ASTA RT Σ PMc (memset_fr_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz d) Σ OW LB lo d n c m)).
Proof.
  intros until bd. intros HEAP ST CEIL LO SPT SP16 MI -> IND D1 D2 HN -> -> ->.
  unfold MallocRep.wz in *.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ bd HEAP IND) as (BD0 & _ & _ & BDC & _).
  pose proof (blk_checked_dst Σ OW LB m sp bd d n HEAP IND D1 D2 ltac:(lia)) as CD.
  eapply cps_conseq; [ eapply (rc_asan_memset RT (@ar_RC AR) Σ PMc) with (d := d) (n := n) (c := c) (lo := lo); try reflexivity | intros c0 Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - unfold BnHeapA.ACEIL in *. lia.
  - lia.
  - exact CD.
  - exact (AH_art _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP | exact ST | exact CEIL | exact LO | unfold USTACK_TOP; lia | exact SP16].
  - intros c0 Hc. eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & BZ).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    unfold memset_fr_post, MallocRep.wz. do 16 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact (AH_same' _ _ _ _ _ _ _ _ bd HEAP ART2 WM2 PRES IND D1 D2)|]. split; [exact WM2|].
    split.
    { pose proof (AH_frames _ _ _ _ HEAP) as HF. intros a Ha [Hc Hd]. apply PRES; unfold wa; rewrite unsigned_lit by lia; [| exact Hd].
      rewrite HF. destruct Hc as [Hc|[Hf|Hf]]; [exact (AH_aclient _ _ _ _ _ _ HEAP Hc)| |]; unfold aclient; clear - Hf; tauto. }
    split; [exact BZ|]. destruct CD as (_ & _ & W). exact (wr_at_transport ctasegs m m2 d _ W WM2).
Qed.

End MemsetFr.
(* [comment removed for export] *)
Local Notation E_ex_ct := (E_asn1_d2i_ex_primitive_244534 : uk_call 0x24187c 0x241b70 0x2426a8).      (* [comment removed for export] *)


Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Body.
  (* [comment removed for export] *)
  Hypothesis STRCPY : strcpy_icontract RT.
  Hypothesis HCT : forall AR' : ARun, strcpy_icontract (@ar_RT AR') -> @check_tlen_specA AR' UK.

  (* [comment removed for export] *)
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (K : list block).
  Variables (D : Z) (d : list Z) (op totlen utype e OPP PV TLC : Z) (j31 : list byte).
  Variables (f spa : Z) (g : nat) (junk gj : list byte) (Σ1 : rts RT) (m3 : mem).
  Let gr := get_object d op totlen.
  Let plen := go_len gr.
  Let cont := go_p gr.

  (* [comment removed for export] *)
  Hypothesis PRE0 : ap_preA Σ st m OW LB E bo sp lo EXPRIM_STACK_A (EXPRIM_COST_A plen) EXPRIM_FRAMES_A.
  Hypothesis ENT : d2i_entryA e utype.
  (* [comment removed for export] *)
  Variable ras : list Z.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx ADEP_ENTRY (bv_unsigned ra :: ras).
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis PAY : payload_okA m LB D d.
  Hypothesis OP0 : 0 <= op.
  Hypothesis TL0 : 0 < totlen.
  Hypothesis OPT : op + totlen <= zlength d.
  Hypothesis EG : go_err gr = None.
  Hypothesis ETAG : go_tag gr = utype.
  Hypothesis ECLS : go_cls gr = 0.
  Hypothesis ERET : Z.land (go_ret gr) 32 = 0.
  Hypothesis COPP : cellA_in LB OPP 8.
  Hypothesis CPV : cellA_in LB PV 8.
  Hypothesis CTLC : cellA_in LB TLC 32.
  Hypothesis ALO : OPP mod 8 = 0.
  Hypothesis ALV : PV mod 8 = 0.
  Hypothesis ALT : TLC mod 8 = 0.
  Hypothesis DOV : OPP + 8 <= PV \/ PV + 8 <= OPP.
  Hypothesis DOT : OPP + 8 <= TLC \/ TLC + 32 <= OPP.
  Hypothesis DVT : PV + 8 <= TLC \/ TLC + 32 <= PV.
  Hypothesis DOD : OPP + 8 <= D \/ D + zlength d <= OPP.
  Hypothesis DVD : PV + 8 <= D \/ D + zlength d <= PV.
  Hypothesis DTD : TLC + 32 <= D \/ D + zlength d <= TLC.
  Hypothesis HOPP : rw_cells ctasegs m OPP [C8 (wz (D + op))].
  Hypothesis HPV : rw_cells ctasegs m PV [C8 (wz 0)].
  Hypothesis HTLC : rw_cells ctasegs m TLC (tlc_in j31).

  (* [comment removed for export] *)
  Hypothesis HEAP3 : @BnHeapA.AHEAP (push AR f 2) Σ1 OW LB m3.
  Hypothesis FRESH : forall b, In b (OW ++ LB) -> off_fr f 2 b.
  Hypothesis GEO : @fr_geo (push AR f 2) f 2.
  Hypothesis CR1 : rt_credit RT Σ1 = rt_credit RT Σ - 1.
  Hypothesis ST3 : stk ctasegs m3 lo spa.
  Hypothesis MI3 : mem_inv ctasegs m3.
  Hypothesis AGF : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3.
  Hypothesis SPA32 : spa mod 32 = 0.
  Hypothesis SPAL : bv_unsigned sp - 272 <= spa.
  Hypothesis SPAH : spa <= bv_unsigned sp - 256.
  Hypothesis GSZ : Z.of_nat g = bv_unsigned sp - spa - 168.

  (* [comment removed for export] *)
  Lemma ex_ctx :
    Forall (fun c => 0 <= c < 256) d /\ 0 < D /\ D + zlength d < 2 ^ 63 /\ zlength d < 2 ^ 26
    /\ 12365824 <= ACEIL /\ 17594333495296 <= ACEIL /\ ACEIL + 8388608 <= 140737488355328
    /\ ACEIL <= lo /\ 0 <= lo /\ lo + 272 + CHECK_TLEN_STACK_A <= bv_unsigned sp /\ 66320 <= CHECK_TLEN_STACK_A
    /\ bv_unsigned sp + 16 <= USTACK_TOP /\ 0 <= bv_unsigned sp < 2 ^ 64
    /\ Z.of_nat (length (to_bytes d)) = zlength d /\ bv_unsigned (Z_to_bv 64 spa) = spa
    /\ 0 < f /\ f mod 64 = 0 /\ f + 256 <= ACEIL /\ 12365824 <= f /\ bv_unsigned (Z_to_bv 64 f) = f /\ (f + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= f)
    /\ (f + 248 <= shad f \/ shad f + 32 <= f) /\ 2147450880 <= shad f /\ shad f + 32 <= 17594333495296
    /\ op + 2 <= cont /\ 0 <= plen /\ cont + plen <= op + totlen /\ 0 <= utype < 31
    /\ (exists bd, In bd LB /\ blk_addr bd <= D /\ D + zlength d <= blk_addr bd + blk_size bd /\ 0 < blk_addr bd /\ blk_addr bd + blk_size bd <= ACEIL
                   /\ (blk_addr bd + blk_size bd <= 0x10000 \/ SEGTOP_A <= blk_addr bd) /\ off_fr f 2 bd)
    /\ (exists bq, In bq LB /\ blk_addr bq <= OPP /\ OPP + 8 <= blk_addr bq + blk_size bq /\ 0 < blk_addr bq /\ blk_addr bq + blk_size bq <= ACEIL
                   /\ (blk_addr bq + blk_size bq <= 0x10000 \/ SEGTOP_A <= blk_addr bq) /\ off_fr f 2 bq)
    /\ (exists bv, In bv LB /\ blk_addr bv <= PV /\ PV + 8 <= blk_addr bv + blk_size bv /\ 0 < blk_addr bv /\ blk_addr bv + blk_size bv <= ACEIL
                   /\ (blk_addr bv + blk_size bv <= 0x10000 \/ SEGTOP_A <= blk_addr bv) /\ off_fr f 2 bv)
    /\ (exists bt, In bt LB /\ blk_addr bt <= TLC /\ TLC + 32 <= blk_addr bt + blk_size bt /\ 0 < blk_addr bt /\ blk_addr bt + blk_size bt <= ACEIL
                   /\ (blk_addr bt + blk_size bt <= 0x10000 \/ SEGTOP_A <= blk_addr bt) /\ off_fr f 2 bt).
  Proof.
    clear HOPP HPV HTLC DOV DOT DVT DOD DVD DTD ALO ALV ALT KOW KIDS AGF HCT.
    destruct PRE0 as (HEAP & _ & _ & _ & ST & CEIL & LOSP & TOP & _ & _ & _ & _).
    destruct PAY as (_ & DF & D0 & D63 & D26 & HB).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, STACK_WIN, SHHI, USTACK_TOP in C1, C2, C3.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold EXPRIM_STACK_A, ADEP_FRAME in LOSP.
    assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
    assert (ESS : 66320 <= CHECK_TLEN_STACK_A) by (unfold CHECK_TLEN_STACK_A, ACTL_FRAME, GETOBJ_STACK_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK; clear; lia).
    pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 2) with 256 in G3, G5. unfold SEGTOP_A in G4. unfold BnHeapA.ACEIL in G3. cbn [ar_SP0 push amb] in G3.
    pose proof (get_object_bounds d op totlen ltac:(eapply Forall_impl; [| exact DF]; cbv beta; intros; lia) TL0) as GB.
    cbv zeta in GB. fold gr in GB. rewrite EG in GB. destruct GB as (GB1 & GB2 & GB3).
    pose proof (utype_casesA _ _ ENT) as UT.
    assert (CELL : forall A n, cellA_in LB A n -> exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b /\ 0 < blk_addr b
                   /\ blk_addr b + blk_size b <= BnHeapA.ACEIL /\ (blk_addr b + blk_size b <= 0x10000 \/ SEGTOP_A <= blk_addr b) /\ off_fr f 2 b).
    { intros A n (b & Hb & H1 & H2). assert (Hb' : In b (OW ++ LB)) by (apply in_or_app; right; exact Hb).
      pose proof (AH_range_gen _ _ _ _ _ HEAP Hb') as (R0 & _ & _ & R3 & R4). exists b. repeat (split; [assumption|]). exact (FRESH b Hb'). }
    split; [exact DF|]. split; [exact D0|]. split; [exact D63|]. split; [exact D26|].
    split; [clear - C1; lia|]. split; [clear - C2; lia|]. split; [clear - C3; lia|].
    split; [exact CEIL|]. split; [exact LO0|]. split; [clear - LOSP; lia|]. split; [exact ESS|]. split; [exact TOP|]. split; [exact SPR|].
    split; [unfold to_bytes, zlength; rewrite length_map; reflexivity|].
    split; [apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - C1 CEIL LO0 LOSP SPAL SPAH SPR ESS; lia|].
    split; [exact G1|]. split; [exact G2|]. split; [unfold BnHeapA.ACEIL; exact G3|]. split; [exact G4|].
    split; [apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - G1 G3 C3; lia|]. split; [exact G5|].
    assert (SHR : 2147450880 <= shad f /\ shad f + 32 <= 17594333495296).
    { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(clear - G1; lia) ltac:(clear; lia)).
      assert (f / 8 + 32 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 32); [apply Z.div_lt_upper_bound; clear - G3 C3; unfold BnHeapA.ACEIL in *; lia | clear - H0; lia]). clear - H H0. lia. }
    split; [clear - G5 SHR; unfold shad, SHB in *; destruct G5 as [G5|G5]; [left | right]; Z.div_mod_to_equations; lia|].
    split; [clear - SHR; lia|]. split; [clear - SHR; lia|].
    split; [unfold cont; clear - GB1; lia|]. split; [unfold plen; clear - GB2; lia|]. split; [unfold cont, plen; clear - GB3; lia|]. split; [clear - UT; lia|].
    split. { destruct HB as [->|(b & Hb & H1 & H2)]; [unfold zlength in OPT; cbn in OPT; clear - OPT OP0 TL0; lia|]. exact (CELL D (zlength d) ltac:(exists b; auto)). }
    split; [exact (CELL OPP 8 COPP)|]. split; [exact (CELL PV 8 CPV)| exact (CELL TLC 32 CTLC)].
  Qed.

  Local Ltac ctx := pose proof ex_ctx as (DF & D0 & D63 & D26 & CL1 & CL2 & CL3 & CEIL & LO0 & LO & ESS & TOP & SPR & DLEN & ESPA & G1 & G2 & G3 & G4 & Ef & G5 & FSH & SHR1 & SHR2 & GB1 & GB2 & GB3 & UTR
                                             & (bd & Hbd & BD1 & BD2 & BD3 & BD4 & BD5 & OD) & (bq & Hbq & BQ1 & BQ2 & BQ3 & BQ4 & BQ5 & OQ)
                                             & (bv & Hbv & BV1 & BV2 & BV3 & BV4 & BV5 & OV) & (bt & Hbt & BT1 & BT2 & BT3 & BT4 & BT5 & OT));
                    unfold off_fr in OD, OQ, OV, OT; change (fs_size 2) with 256 in OD, OQ, OV, OT; cbn [blk_addr blk_size fst snd] in OD, OQ, OV, OT;
                    hide BD5; hide BQ5; hide BV5; hide BT5; hide OD; hide OQ; hide OV; hide OT; hide G5.

  (* [comment removed for export] *)
  Definition ex_lowA (j0 j8 j16 j24 j32 j48 j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; C8 (Z_to_bv 64 PV); CB 8 j48; C8 (Z_to_bv 64 OPP); CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 f);
     CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB g junk].
  Definition ex_frameA (jf24 jf32 jf40 jf64 jf65 jf80 jf112 : list byte) : list cell :=
    [C8 (Z_to_bv 64 ADEP_MAGIC); C8 (Z_to_bv 64 ADEP_DESCR); C8 (Z_to_bv 64 ADEP_ENTRY); CB 8 jf24; CB 8 jf32; CB 24 jf40; CB 1 jf64; CB 15 jf65; CB 32 jf80; CB 136 jf112].

  Local Ltac hide_disj := hide DOV; hide DOT; hide DVT; hide DOD; hide DVD; hide DTD.
  (* [comment removed for export] *)
  Definition ex_frameB (jf24 jf40 jf65 : list byte) : list cell :=
    [C8 (Z_to_bv 64 ADEP_MAGIC); C8 (Z_to_bv 64 ADEP_DESCR); C8 (Z_to_bv 64 ADEP_ENTRY); CB 8 jf24; C8 (Z_to_bv 64 (D + cont)); CB 24 jf40; C1 (Z_to_bv 8 0); CB 15 jf65].
  Definition ex_shadowB (jst : list byte) : list cell :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); CB 12 jst].
  (* [comment removed for export] *)
  Definition ex_lowB (j0 j8 j16 j64 j72 j80 : list byte) : list cell :=
    [CB 8 j0; CB 8 j8; CB 8 j16; C8 (Z_to_bv 64 (f + 64)); C8 (Z_to_bv 64 (Z.shiftr OPP 3 + SHB)); C8 (Z_to_bv 64 PV); C8 (Z_to_bv 64 (f + 80)); C8 (Z_to_bv 64 OPP);
     CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 f)].

  (* [comment removed for export] *)
  Definition ex_pbs (qc qfc : bptr) : list block := [(qc, f + 32, 8); (qfc, f + 64, 1)].
  Definition ex_arm_facts (qc qfc : bptr) (Σ4 : rts RT) (OW4 : list block) (m9 : mem) (jt4 j0 j8 j16 j64 j72 j80 j104 j120 j128 j136 j144 : list byte) : Prop :=
    @BnHeapA.AHEAP (push AR f 2) Σ4 OW4 (ex_pbs qc qfc ++ LB) m9
    /\ @ap_preA (push AR f 2) Σ4 st m9 OW4 (ex_pbs qc qfc ++ LB) E bo (Z_to_bv 64 spa) lo 0 0 0
    /\ GETOBJ_ERR_COST_A + mcost plen <= rt_credit RT Σ4 /\ rt_credit RT Σ - 2 <= rt_credit RT Σ4
    /\ blocks_kept K st OW4 m m9
    /\ ax_pres LB (bv_unsigned sp) ([(OPP, OPP + 8); (PV, PV + 8); (TLC, TLC + 32)] ++ LIBW_A) m m9
    /\ rw_cells ctasegs m9 spa (ex_lowB j0 j8 j16 j64 j72 j80)
    /\ rw_cells ctasegs m9 (spa + 96) [C8 (Z_to_bv 64 (D + cont + plen))] /\ rw_cells ctasegs m9 (spa + 104) [CB 6 (firstn 6 j104)]
    /\ rw_cells ctasegs m9 (spa + 110) [C1 (Z_to_bv 8 0)] /\ rw_cells ctasegs m9 (spa + 111) [C1 (Z_to_bv 8 0)]
    /\ rw_cells ctasegs m9 (spa + 112) [C8 (Z_to_bv 64 plen)] /\ rw_cells ctasegs m9 (spa + 120) [CB 4 (firstn 4 j120); C4 (Z_to_bv 64 utype)]
    /\ rw_cells ctasegs m9 (spa + 128) [CB 8 j128; CB 8 j136; CB 8 j144; CB g junk]
    /\ rw_cells ctasegs m9 (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells ctasegs m9 (f + 32) [C8 (Z_to_bv 64 (D + cont))] /\ rw_cells ctasegs m9 (f + 64) [C1 (Z_to_bv 8 0)]
    /\ rw_cells ctasegs m9 OPP [C8 (Z_to_bv 64 (D + op))] /\ rw_cells ctasegs m9 PV [C8 (Z_to_bv 64 0)] /\ rw_cells ctasegs m9 TLC [CB 32 jt4]
    /\ payload_okA m9 LB D d.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ex_arm_ms (pc : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m9 : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 plen) (Z_to_bv 64 utype) (Z_to_bv 64 (f + 32))
             x28 x29 x30 x31)
       F (Z_to_bv 64 pc) fc None m9 (seg_rom ctasegs).


  (* [comment removed for export] *)
  Lemma exprim_frontA : forall (Q : option (astr bptr) * ap_st bptr -> rts RT -> machine_state -> Prop)
      (ra' t0' t1' t2' a7' t3' t4' t5' t6' : word) (F : bvmap 5 word) (fc : bv 32)
      (j0 j8 j16 j24 j32 j48 j64 j72 j80 j96 j104 j112 j120 j128 j136 j144 jf24 jf32 jf40 jf64 jf65 jf80 jf112 jst : list byte),
    (* [comment removed for export] *)
    (forall qc qfc Σ4 OW4 m9 jt4 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F' fc',
       utype = V_ASN1_INTEGER \/ utype = V_ASN1_ENUMERATED ->
       ex_arm_facts qc qfc Σ4 OW4 m9 jt4 j0 j8 j16 j64 j72 j80 j104 j120 j128 j136 j144 ->
       @implAp (push AR f 2) _ (W_c2i_stmtA.c2i_int_fragA d cont plen st) Σ4 Q (ex_arm_ms EX_INT_ARM x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F' fc' m9)) ->
    (* [comment removed for export] *)
    (forall qc qfc Σ4 OW4 m9 jt4 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F' fc',
       utype = V_ASN1_OCTET_STRING ->
       ex_arm_facts qc qfc Σ4 OW4 m9 jt4 j0 j8 j16 j64 j72 j80 j104 j120 j128 j136 j144 ->
       @implAp (push AR f 2) _ (abind (amalloc SZ_ASN1_STRING) (fun blk =>
                                   if plen =? 0 then aret (Some (mkStr blk None))
                                   else abind (amalloc plen) (fun dp => aret (Some (mkStr blk (Some (dp, plen)))))) st)
              Σ4 Q (ex_arm_ms EX_OCT_ARM x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F' fc' m9)) ->
    rw_cells ctasegs m3 spa (ex_lowA j0 j8 j16 j24 j32 j48 j64 j72 j80 j96 j104 j112 j120 j128 j136 j144) ->
    rw_cells ctasegs m3 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    rw_cells ctasegs m3 f (ex_frameA jf24 jf32 jf40 jf64 jf65 jf80 jf112) ->
    rw_cells ctasegs m3 (shad f) (adep_shadow_pro jst) ->
    @implAp (push AR f 2) _ (d2i_prim d op totlen utype st) Σ1 Q
      (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) (Z_to_bv 64 (f + 80))
               (Z_to_bv 64 1) (Z_to_bv 64 (-13)) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (-15)) (Z_to_bv 64 1102416563) a7'
               (Z_to_bv 64 f) (Z_to_bv 64 f) (wz 0) (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) (wz (item_ofA utype)) (wz TLC) (wz 0) (wz totlen) (wz (-1)) t3' t4' t5' t6')
          F (wz ADEP_BODY) fc None m3 (seg_rom ctasegs)).
  Proof.
    intros until jst. intros KINT KOCT FRL FRH FRF FRS. hide_disj. ctx.
    pose proof PRE0 as (HEAP & AS & IDS & DC & ST & CEIL' & LOSP & TOP' & AL16 & MI & CRED & FRM).
    pose proof PAY as (HB & _).
    unfold ex_lowA in FRL. unfold ex_frameA in FRF. unfold adep_shadow_pro in FRS. unfold CtRepP.W_check_tlen.tlc_in in HTLC. unfold ADEP_BODY, MallocRep.wz in *.
    (* [comment removed for export] *)
    assert (VPOS : 0 <= CHECK_TLEN_STACK_A /\ 0 <= GETOBJ_ERR_COST_A /\ 0 <= CHECK_TLEN_FRAMES_A /\ 0 <= mcost plen)
      by (pose proof (mcost_nonneg plen ltac:(clear - GB2; lia)) as M0;
          unfold CHECK_TLEN_STACK_A, ACTL_FRAME, GETOBJ_STACK_A, GETOBJ_ERR_COST_A, CHECK_TLEN_FRAMES_A, GETOBJ_FRAMES_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK,
                 ERR_NEW_COST, ERR_SET_DEBUG_COST, ERR_SET_ERROR_COST, ERR_VSET_ERROR_COST, ERR_SET_ERROR_FRAMES, ERR_VSET_ERROR_FRAMES, RT_STACK; clear - M0; lia).
    pose proof (pro_closeA Σ st m OW LB E bo sp lo _ _ _ f 2%nat Σ1 m3 spa 256 PRE0 HEAP3 ST3 MI3 AGF CR1 SPA32
                  ltac:(clear - SPAL; lia) ltac:(clear - SPAH; lia) ltac:(clear; lia) ltac:(unfold EXPRIM_STACK_A, ADEP_FRAME; clear - VPOS; lia)
                  ltac:(unfold EXPRIM_COST_A; clear - VPOS; lia) ltac:(unfold EXPRIM_FRAMES_A; clear - VPOS; lia)) as PRE1.
    unfold EXPRIM_STACK_A, EXPRIM_COST_A, EXPRIM_FRAMES_A, ADEP_FRAME in PRE1.
    replace (272 + CHECK_TLEN_STACK_A - 256 - 16) with CHECK_TLEN_STACK_A in PRE1 by (clear; lia).
    replace (2 + GETOBJ_ERR_COST_A + mcost plen - 1) with (1 + GETOBJ_ERR_COST_A + mcost plen) in PRE1 by (clear; lia).
    replace (1 + CHECK_TLEN_FRAMES_A - 1) with CHECK_TLEN_FRAMES_A in PRE1 by (clear; lia).
    pose proof PRE1 as (_ & AS1 & IDS1 & DC1 & ST1 & CEIL1 & LOSP1 & TOP1 & AL161 & MI1 & CRED1 & FRM1).
    rewrite ESPA in ST1, LOSP1, TOP1, AL161. cbn [ar_FR ar_RT ar_SP0 push amb] in CRED1, FRM1, CEIL1.
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AGF) in HOPP; [| intros a Ha; cbn in Ha; right; right; exists bq; split; [apply in_or_app; right; exact Hbq| clear - Ha BQ1 BQ2; lia]].
    apply (rw_cells_agree _ _ _ _ _ AGF) in HPV; [| intros a Ha; cbn in Ha; right; right; exists bv; split; [apply in_or_app; right; exact Hbv| clear - Ha BV1 BV2; lia]].
    apply (rw_cells_agree _ _ _ _ _ AGF) in HTLC; [| intros a Ha; cbn in Ha; right; right; exists bt; split; [apply in_or_app; right; exact Hbt| clear - Ha BT1 BT2; lia]].
    assert (PAY3 : payload_okA m3 LB D d).
    { eapply payload_okA_agreeA; [exact PAY|]. eapply agree_on_mono; [exact AGF|]. intros a Ha. right; right. eapply in_block_mono; [| exact Ha]. intros b Hb; apply in_or_app; right; exact Hb. }
    clear HB. pose proof PAY3 as (HB & _).
    (* [comment removed for export] *)
    pose proof (munch_refl [(spa, spa); (f, f + 248); (shad f, shad f + 32)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
    freeze HOPP. freeze HPV. freeze HTLC. freeze HB. freeze FRL. freeze FRH.
    apply implAp_from_evt. step. step. step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    assert (HEAP4 : @BnHeapA.AHEAP (push AR f 2) Σ1 OW LB m4).
    { eapply (@fr3_heap (push AR f 2) Σ1 OW LB m3 m4 f 2%nat spa spa 248 32 (or_introl eq_refl) HEAP3 MU WM);
        [clear - CEIL1 LOSP1 ESS; plia| clear - TOP1; unfold USTACK_TOP in *; lia| change (fs_size 2) with 256; clear; lia| change (fs_size 2) with 256; clear; lia
        | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb]. }
    assert (OFFLB : forall b, In b LB -> off_fr f 2 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
    destruct (bptr_fresh (map blk_id (OW ++ LB))) as [qb Hqb].
    assert (HEAPb : @BnHeapA.AHEAP (push AR f 2) Σ1 OW ((qb, f + 80, 32) :: LB) m4).
    { apply (@frame_obj_open (push AR f 2) Σ1 OW LB m4 f 2%nat qb (f + 80) 32 (or_introl eq_refl) HEAP4);
        [clear; lia| change (fs_size 2) with 256; clear; lia| clear; lia| | exact Hqb|].
      - eapply (acc_of_shadow_cells m4 (shad f) _ 10 (f + 80) 32 FRS); [clear - G2; Z.div_mod_to_equations; lia| clear - G1; lia| clear; lia
          | unfold shad; clear - G2; Z.div_mod_to_equations; lia| cbn; clear; lia| reflexivity].
      - intros b Hb. pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. unfold blk_apart. cbn [blk_addr blk_size fst snd]. clear - O. lia. }
    clear HEAP4.
    (* [comment removed for export] *)
    pose proof (agree_on_of_munch_nw _ _ _ MU) as AG4. clear MU WM.
    unfold frozen in FRL. apply (rw_cells_agree _ _ _ _ _ AG4) in FRL; [| intros a Ha; cbn [cells_size csize] in Ha; rewrite ?Nat2Z.inj_add in Ha; cbn [outside fst snd]; clear - Ha GSZ SPAL SPAH G3 CEIL LO ESS SHR2 CL2; plia].
    pose proof (munch_refl [(spa, spa + 168)]%Z m4) as MU. pose proof (wmono_refl ctasegs m4) as WM.
    freeze FRF. freeze FRS.
    step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    assert (HEAP5 : @BnHeapA.AHEAP (push AR f 2) Σ1 OW ((qb, f + 80, 32) :: LB) m5).
    { eapply (@AH_frame (push AR f 2)); [exact HEAPb| exact MU| exact WM|]. constructor; [left; cbn [fst snd]; clear - CEIL1 LOSP1 TOP1 SPAH GSZ TOP ESS; plia| constructor]. }
    apply evt_done. eapply implAp_step_same.
    { eapply (@asan_memset_frA (push AR f 2)) with (lo := lo) (d := f + 80) (n := 32) (c := Z_to_bv 8 0) (bd := (qb, f + 80, 32)); rewrite ?ESPA;
        [exact HEAP5| | exact CEIL| clear - LOSP1 ESS; unfold CHECK_TLEN_STACK_A, ACTL_FRAME, GETOBJ_STACK_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK in *; lia
        | exact TOP1| clear - AL161; unfold al16 in *; exact AL161| | reflexivity| apply in_or_app; right; left; reflexivity| cbn; clear; lia| cbn; clear; lia| clear; lia
        | reflexivity| reflexivity| reflexivity].
      all: assumption. }
    intros msM POM. destruct POM as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & FM & fcM & m6 & -> & MI6 & ST6 & HEAP6 & WM6 & AG6 & BZ6 & WR6).
    rewrite ?ESPA in *. unfold EX_MEMSET_RA. rewrite (ret_pc_even 0x2419f8) by (clear; lia).
    (* [comment removed for export] *)
    assert (FRA : forall a, f <= a < f + 248 -> @fr_addr (push AR f 2) a).
    { intros a Ha. left. exists f, 2%nat. split; [left; reflexivity| change (fs_size 2) with 256; clear - Ha; lia]. }
    assert (FSA : forall a, shad f <= a < shad f + 32 -> @fr_addr (push AR f 2) a).
    { intros a Ha. right. apply (@fr_shadow_in (push AR f 2) f 2%nat a (or_introl eq_refl)). change (fs_size 2) with 256. clear - Ha. lia. }
    apply (rw_cells_agree _ _ _ _ _ AG6) in FRL; [| intros a Ha; cbn [cells_size csize] in Ha; rewrite ?Nat2Z.inj_add in Ha; split; [left; left; clear - Ha GSZ SPAH TOP; unfold USTACK_TOP in *; lia| clear - Ha G3 CEIL LO ESS SPAL; plia]].
    unfold frozen in FRH.
    apply (rw_cells_agree _ _ _ _ _ AG4) in FRH; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAL SPAH G3 CEIL LO ESS SHR2 CL2; plia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in FRH; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG6) in FRH; [| intros a Ha; cbn in Ha; split; [left; left; clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia| clear - Ha SPAH G3 CEIL LO ESS; plia]].
    unfold frozen in FRF, FRS.
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in FRF; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAL G3 CEIL LO ESS; plia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in FRS; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAL CEIL LO ESS SHR2 CL2; plia].
    apply (rw_cells_agree _ _ _ _ _ AG6) in FRS; [| intros a Ha; cbn in Ha; split; [right; apply FSA; clear - Ha; lia| clear - Ha FSH; lia]].
    lazymatch type of FRF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: nil) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: nil) with ([c0; c1; c2; c3; c4; c5; c6; c7] ++ [c8] ++ [c9]) in FRF end.
    apply rw_cells_app in FRF as [FRF1 FRF]. apply rw_cells_app in FRF as [_ FRF3].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FRF3. replace (f + 80 + 32) with (f + 112) in FRF3 by (clear; lia).
    apply (rw_cells_agree _ _ _ _ _ AG6) in FRF1; [| intros a Ha; cbn in Ha; split; [right; apply FRA; clear - Ha; lia| clear - Ha; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG6) in FRF3; [| intros a Ha; cbn in Ha; split; [right; apply FRA; clear - Ha; lia| clear - Ha; lia]].
    assert (FRF2 : rw_cells ctasegs m6 (f + 80) [CB 32 (repeat (Z_to_bv 8 0) 32)]).
    { apply rw_cells_of_u8arr with (bs := repeat (Z_to_bv 8 0) 32). split; [exact BZ6| cbn; exact WR6]. }
    assert (OFFQ : forall b a l h, In b LB -> blk_addr b <= l -> h <= blk_addr b + blk_size b -> l <= a < h ->
                   outside [(spa, spa); (f, f + 248); (shad f, shad f + 32)]%Z a /\ outside [(spa, spa + 168)]%Z a /\ ~ (f + 80 <= a < f + 80 + 32)).
    { intros b a l h Hb H1 H2 Ha. pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O.
      pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _).
      pose proof (AH_offsh _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as RO. unfold SHLO, SHHI in RO.
      cbn [outside fst snd]. clear - O R3 RO H1 H2 Ha CEIL LO ESS SPAL SHR1 SHR2. plia. }
    unfold frozen in HOPP, HPV, HTLC, HB.
    Local Ltac tr3 H b l h Hb H1 H2 AG4 MU AG6 OFFQ :=
      apply (rw_cells_agree _ _ _ _ _ AG4) in H; [| intros a Ha; cbn in Ha; exact (proj1 (OFFQ b a l h Hb H1 H2 Ha))];
      apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in H; [| intros a Ha; cbn in Ha; exact (proj1 (proj2 (OFFQ b a l h Hb H1 H2 Ha)))];
      apply (rw_cells_agree _ _ _ _ _ AG6) in H; [| intros a Ha; cbn in Ha; split; [left; right; right; exists b; split; [apply in_or_app; right; right; exact Hb| lia]| exact (proj2 (proj2 (OFFQ b a l h Hb H1 H2 Ha)))]].
    tr3 HOPP bq OPP (OPP + 8) Hbq BQ1 BQ2 AG4 MU AG6 OFFQ.
    tr3 HPV bv PV (PV + 8) Hbv BV1 BV2 AG4 MU AG6 OFFQ.
    tr3 HTLC bt TLC (TLC + 32) Hbt BT1 BT2 AG4 MU AG6 OFFQ.
    rewrite <- DLEN in BD2.
    apply (bytes_at_agree _ _ _ _ _ AG4) in HB; [| intros a Ha; exact (proj1 (OFFQ bd a D (D + Z.of_nat (length (to_bytes d))) Hbd BD1 BD2 Ha))].
    apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in HB; [| intros a Ha; exact (proj1 (proj2 (OFFQ bd a D (D + Z.of_nat (length (to_bytes d))) Hbd BD1 BD2 Ha)))].
    apply (bytes_at_agree _ _ _ _ _ AG6) in HB.
    2:{ intros a Ha. split; [left; right; right; exists bd; split; [apply in_or_app; right; right; exact Hbd| clear - Ha BD1 BD2; lia]| exact (proj2 (proj2 (OFFQ bd a D (D + Z.of_nat (length (to_bytes d))) Hbd BD1 BD2 Ha)))]. }
    rewrite DLEN in BD2.
    assert (HEAP6c : @BnHeapA.AHEAP (push AR f 2) Σ1 OW LB m6).
    { eapply (@frame_obj_close (push AR f 2)); [left; reflexivity| exact HEAP6|]. unfold in_fr. cbn [blk_addr blk_size fst snd]. change (fs_size 2) with 256. clear; lia. }
    (* [comment removed for export] *)
    assert (CSB : forall a, client_static a -> a < 12365824).
    { intros a [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. clear - Hin Hlh. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia. }
    assert (ALLOUT : forall a, lib_addr OW a \/ aclient_addr LB (bv_unsigned sp) a ->
              outside [(spa, spa); (f, f + 248); (shad f, shad f + 32)]%Z a /\ outside [(spa, spa + 168)]%Z a
              /\ (aclient_addr (OW ++ (qb, f + 80, 32) :: LB) spa a /\ ~ (f + 80 <= a < f + 80 + 32))).
    { intros a HL. assert (LO3 : (a < BnHeapA.ACEIL /\ (a < SHLO \/ SHHI <= a) /\ (a < f \/ f + 256 <= a)) \/ (bv_unsigned sp <= a /\ a < USTACK_TOP)).
      { assert (BLK : forall b, In b (OW ++ LB) -> blk_addr b <= a < blk_addr b + blk_size b -> a < BnHeapA.ACEIL /\ (a < SHLO \/ SHHI <= a) /\ (a < f \/ f + 256 <= a)).
        { intros b Hb Hr. pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & R3 & _). pose proof (AH_offsh _ _ _ _ b HEAP Hb) as RO.
          pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. clear - Hr R3 RO O. lia. }
        destruct HL as [[HS|(b & Hb & Hr)]|[H1|[H1|(b & Hb & Hr)]]].
        - left. pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. unfold SHLO. clear - HA CL1 CL2 G4. lia.
        - left. exact (BLK b (in_or_app _ _ _ (or_introl Hb)) Hr).
        - right. exact H1.
        - left. pose proof (CSB a H1) as HA. unfold SHLO. clear - HA CL1 G4. lia.
        - left. exact (BLK b (in_or_app _ _ _ (or_intror Hb)) Hr). }
      unfold SHLO, SHHI in LO3. cbn [outside fst snd]. split; [clear - LO3 CEIL LO ESS SPAL SPAH SHR1 SHR2 CL2 G3; plia|]. split; [clear - LO3 CEIL LO ESS SPAL SPAH G3; plia|].
      split; [| clear - LO3 G3 CEIL LO ESS SPAH; plia].
      destruct HL as [HL|Ha].
      - eapply acl_sub; [| | exact (lib_addr_aclient OW LB spa a HL)]; [intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; exact Hb]| clear; lia].
      - eapply acl_sub; [| | exact Ha]; [intros b Hb; apply in_or_app; right; right; exact Hb| clear - SPAH; lia]. }
    assert (AG36 : agree_on (fun a => lib_addr OW a \/ aclient_addr LB (bv_unsigned sp) a) m3 m6).
    { eapply agree_on_trans; [eapply agree_on_mono; [exact AG4|]; intros a Ha; exact (proj1 (ALLOUT a Ha))|].
      eapply agree_on_trans; [eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|]; intros a Ha; exact (proj1 (proj2 (ALLOUT a Ha)))|].
      eapply agree_on_mono; [exact AG6|]. intros a Ha. pose proof (ALLOUT a Ha) as (_ & _ & X). split; [left; exact (proj1 X)| exact (proj2 X)]. }
    assert (LAG6 : agree_on (lib_addr OW) m3 m6) by (eapply agree_on_mono; [exact AG36|]; intros a Ha; left; exact Ha).
    assert (AXG6 : agree_on (aclient_addr LB (bv_unsigned sp)) m3 m6) by (eapply agree_on_mono; [exact AG36|]; intros a Ha; right; exact Ha).
    clear AG4 MU WM AG6 ALLOUT AG36 OFFQ HEAPb HEAP5 HEAP6 BZ6 WR6 FRA FSA.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of FRL with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: rest)
        with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] ++ [c12] ++ [c13] ++ [c14] ++ [c15] ++ rest) in FRL end.
    apply rw_cells_app in FRL as [FRLA FRL]. apply rw_cells_app in FRL as [F96 FRL]. apply rw_cells_app in FRL as [F104 FRL]. apply rw_cells_app in FRL as [F112 FRL].
    apply rw_cells_app in FRL as [F120 FRLB].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in F96, F104, F112, F120, FRLB.
    replace (spa + Z.of_nat 96) with (spa + 96) in F96 by (clear; lia).
    replace (spa + 96 + 8) with (spa + 104) in F104 by (clear; lia). replace (spa + 96 + 8 + 8) with (spa + 112) in F112 by (clear; lia).
    replace (spa + 96 + 8 + 8 + 8) with (spa + 120) in F120 by (clear; lia). replace (spa + 96 + 8 + 8 + 8 + 8) with (spa + 128) in FRLB by (clear; lia).
    apply (cb_splitA _ _ 6 2) in F104. lazymatch type of F104 with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in F104 end.
    apply rw_cells_app in F104 as [F104 F110]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in F110. replace (spa + 104 + 6) with (spa + 110) in F110 by (clear; lia).
    apply (cb_splitA _ _ 1 1) in F110. lazymatch type of F110 with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in F110 end.
    apply rw_cells_app in F110 as [F110 F111]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in F111. replace (spa + 110 + 1) with (spa + 111) in F111 by (clear; lia).
    destruct (cb_byteA _ _ _ F110) as [bi F110']. clear F110. destruct (cb_byteA _ _ _ F111) as [bc F111']. clear F111.
    apply (cb_splitA _ _ 4 4) in F120.
    (* [comment removed for export] *)
    destruct (@item_cellsA_of (push AR f 2) _ _ _ _ e utype HEAP6c ENT) as (IT0 & IT8 & IT8L & IT16 & IT32 & ACCIT).
    pose proof (item_ofA_range utype) as ITR.
    assert (ACCQ : acc ctasegs m6 OPP 8) by (eapply acc_sub; [exact (proj2 (@AH_acc (push AR f 2) _ _ _ _ _ HEAP6c (in_or_app _ _ _ (or_intror Hbq))))| exact BQ1| exact BQ2]).
    assert (EOPP : bv_unsigned (Z_to_bv 64 OPP) = OPP) by (apply unsigned_lit; clear - BQ1 BQ2 BQ3 BQ4 CL3; unfold BnHeapA.ACEIL in *; lia).
    pose proof (munch_refl [(spa, spa + 168)]%Z m6) as MU. pose proof (wmono_refl ctasegs m6) as WM.
    freeze FRF1. freeze FRF2. freeze FRF3. freeze FRS. freeze HPV. freeze HTLC. freeze FRH.
    assert (ITAL8 : al8 (item_ofA utype)) by (clear; unfold al8, item_ofA, ITEM_OCTET_A, ITEM_INTEGER_A, ITEM_ENUM_A; destruct (utype =? _); [reflexivity|]; destruct (utype =? _); reflexivity).
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. step. step. if_true.
    (* [comment removed for export] *)
    step. rewrite (sx32_small utype) by (clear - UTR; lia). step. step.
    step. if_cases KANY; zc KANY; [| exfalso; clear - KANY UTR; lia].
    (* [comment removed for export] *)
    step. step. step. if_false. step. rewrite (sx32_small utype) by (clear - UTR; lia). step.
    (* [comment removed for export] *)
    step. step. step. step. rewrite ?EOPP.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    match goal with H : munch _ m6 m7 |- _ => rename H into MU7 end. match goal with H : wmono ctasegs m6 m7 |- _ => rename H into WM7 end.
    match goal with H : stk ctasegs m7 lo spa |- _ => rename H into ST7 end. match goal with H : mem_inv ctasegs m7 |- _ => rename H into MI7 end.
    apply evt_done.
    (* [comment removed for export] *)
    unfold frozen in FRS, FRF1. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU7)) in FRS; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAL CEIL LO ESS SHR2 CL2; plia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU7)) in FRF1; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAL G3 CEIL LO ESS; plia].
    assert (HEAP7 : @BnHeapA.AHEAP (push AR f 2) Σ1 OW LB m7).
    { eapply (@AH_frame (push AR f 2)); [exact HEAP6c| exact MU7| exact WM7|]. constructor; [left; cbn [fst snd]; clear - CEIL1 LOSP1 TOP1 SPAH GSZ TOP ESS; plia| constructor]. }
    destruct (bptr_fresh (map blk_id (OW ++ LB))) as [qfc Hqfc].
    assert (HEAP7f : @BnHeapA.AHEAP (push AR f 2) Σ1 OW ((qfc, f + 64, 1) :: LB) m7).
    { apply (@frame_obj_open (push AR f 2) Σ1 OW LB m7 f 2%nat qfc (f + 64) 1 (or_introl eq_refl) HEAP7);
        [clear; lia| change (fs_size 2) with 256; clear; lia| clear; lia| | exact Hqfc|].
      - eapply (acc_of_shadow_cells m7 (shad f) _ 8 (f + 64) 1 FRS); [clear - G2; Z.div_mod_to_equations; lia| clear - G1; lia| clear; lia
          | unfold shad; clear - G2; Z.div_mod_to_equations; lia| cbn; clear; lia| reflexivity].
      - intros b Hb. pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. unfold blk_apart. cbn [blk_addr blk_size fst snd]. clear - O. lia. }
    set (LBf := (qfc, f + 64, 1) :: LB) in HEAP7f.
    assert (INF : forall b, In b LB -> In b LBf) by (intros b Hb; subst LBf; right; exact Hb).
    (* [comment removed for export] *)
    lazymatch type of FRF1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: nil) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: nil) with ([c0; c1; c2; c3; c4; c5] ++ [c6] ++ [c7]) in FRF1 end.
    apply rw_cells_app in FRF1 as [_ FRF1]. apply rw_cells_app in FRF1 as [HFC _].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in HFC. replace (f + Z.of_nat 64) with (f + 64) in HFC by (clear; lia). replace (f + 64 + 0) with (f + 64) in HFC by (clear; lia).
    (* [comment removed for export] *)
    assert (LAG7 : agree_on (lib_addr OW) m3 m7).
    { eapply agree_on_trans; [exact LAG6|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU7)|]. intros a HL. cbn [outside fst snd].
      destruct HL as [HS|(b & Hb & Hr)].
      - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA CL1 CEIL LO ESS SPAL. lia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LO ESS SPAL. lia. }
    assert (AXG7 : agree_on (aclient_addr LB (bv_unsigned sp)) m3 m7).
    { eapply agree_on_trans; [exact AXG6|]. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU7)|]. intros a Ha. cbn [outside fst snd].
      destruct Ha as [H1|[H1|(b & Hb & Hr)]].
      - clear - H1 SPAH. lia.
      - pose proof (CSB a H1) as HA. clear - HA CL1 CEIL LO ESS SPAL. lia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 CEIL LO ESS SPAL. lia. }
    assert (PREc : @ap_preA (push AR f 2) Σ1 st m7 OW LBf E bo (Z_to_bv 64 spa) lo CHECK_TLEN_STACK_A CHECK_TLEN_COST_A CHECK_TLEN_FRAMES_A).
    { eapply (@ap_preA_weaken (push AR f 2)); [eapply (@ap_preA_memA (push AR f 2)); [exact PRE1| exact HEAP7f| exact LAG7| rewrite ESPA; exact ST7| exact MI7]
        | clear; lia| unfold CHECK_TLEN_COST_A; clear - VPOS; lia| clear - VPOS; lia]. }
    assert (PAYc : payload_okA m7 LBf D d).
    { destruct PAY3 as (_ & P2 & P3 & P4 & P5 & P6). split; [exact HB|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
      right. exists bd. split; [apply INF; exact Hbd| split; [exact BD1| exact BD2]]. }
    unfold frozen in HTLC. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU7)) in HTLC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BT1 BT2 BT4 CEIL LO ESS SPAL; plia].
    unfold frozen in HPV. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU7)) in HPV; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha BV1 BV2 BV4 CEIL LO ESS SPAL; plia].
    unfold frozen in FRH. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU7)) in FRH; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha SPAH; lia].
    clear MU7 WM7 HEAP6c HEAP7 FRF2 FRF3 LAG6 AXG6.
    eapply (implAp_seq_ret (tt, st)).
    { pose proof (HCT (push AR f 2) STRCPY) as HCT2. unfold check_tlen_specA in HCT2. (* [comment removed for export] *)
      eapply HCT2 with (K := K) (LB := LBf) (lo := lo) (D := D) (d := d) (op := op) (totlen := totlen) (exptag := utype)
                                      (POLEN := spa + 112) (PINF := spa + 110) (PCST := spa + 111) (PPC := spa + 96) (TLC := TLC); rewrite ?ESPA;
        [exact PREc| reflexivity
        | (* [comment removed for export] *)
          eapply (uw_call m m7 spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
          [ exact UW
          | eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a Ha; left; exact Ha | eapply agree_on_mono; [exact AXG7|]; intros a Ha; left; exact Ha]
          | reflexivity | clear - SPAH; lia | uchk_open; clear - AL16; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia
          | apply bv_unsigned_in_range | rewrite !Z_to_bv_bv_unsigned; cbn [app]; exact FRH ]
        | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_ex_ct CTX)
        | apply cons_ne| exact KOW| exact KIDS| exact PAYc| exact OP0| exact TL0| exact OPT| exact EG| exact ETAG| exact ECLS| exact ERET| clear - UTR; lia
        | clear; lia| clear; lia| clear; lia| clear; lia| clear - SPAH TOP; unfold USTACK_TOP in *; lia
        | clear - SPA32; Z.div_mod_to_equations; lia| clear - SPA32; Z.div_mod_to_equations; lia
        | destruct CTLC as (b0 & Hb0 & X0); exists b0; split; [apply INF; exact Hb0| exact X0]| exact ALT
        | exact F112| exact F110'| exact F111'| exact F96| exact HTLC
        | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros Σ4 ms4 PO4. unfold check_tlen_postA in PO4. cbn [fst snd] in PO4. fold gr in PO4. unfold MallocRep.wz in PO4. rewrite ?ESPA in PO4.
    destruct PO4 as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F4 & fc4 & m8 & OW4 & jt4
                     & -> & PRE4 & AXP4 & CRED4 & KEPT4 & HOLEN4 & HINF4 & HCST4 & HPPC4 & HTLC4).
    rewrite (ret_pc_even 0x241b70) by (clear; lia). fold plen in HOLEN4. fold cont in HPPC4.
    pose proof PRE4 as (HEAP8 & AS4 & IDS4 & DC4 & ST8 & _ & _ & _ & _ & MI8 & _ & _). cbn [ar_FR ar_RT ar_SP0 push amb] in CRED4.
    clear PREc PAYc F112 F110' F111' F96 HTLC ST7 MI7.
    (* [comment removed for export] *)
    assert (STW : forall a, spa <= a -> a < USTACK_TOP -> (spa + 120 <= a \/ a < spa + 96 \/ (spa + 104 <= a /\ a < spa + 110)) ->
              ax_client LBf spa ([(spa + 112, spa + 112 + 8); (spa + 110, spa + 110 + 1); (spa + 111, spa + 111 + 1); (spa + 96, spa + 96 + 8); (TLC, TLC + 32)] ++ LIBW_A) a).
    { intros a Ha Hb Hc. split; [| left; clear - Ha Hb; lia]. unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha Hb Hc CL1 CEIL LO ESS SPAL BT2 BT4. plia. }
    assert (BLW : forall b A n a, In b LB -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> (blk_addr b + blk_size b <= 65536 \/ 12365824 <= blk_addr b) ->
                  (A + n <= TLC \/ TLC + 32 <= A) -> A <= a < A + n ->
                  ax_client LBf spa ([(spa + 112, spa + 112 + 8); (spa + 110, spa + 110 + 1); (spa + 111, spa + 111 + 1); (spa + 96, spa + 96 + 8); (TLC, TLC + 32)] ++ LIBW_A) a).
    { intros b A n a Hb H1 H2 H5 HT Ha. pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _).
      split; [unfold LIBW_A, SEGTOP_A in *; cbn [rin_ivs fst snd app]; clear - H1 H2 H5 HT Ha R3 CEIL LO ESS SPAL; plia| right; right; exists b; split; [apply INF; exact Hb| clear - H1 H2 Ha; lia]]. }
    apply (rw_cells_agree _ _ _ _ _ AXP4) in FRLA; [| intros a Ha; cbn in Ha; apply STW; [clear - Ha; lia| clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia| clear - Ha; lia]].
    apply (rw_cells_agree _ _ _ _ _ AXP4) in F104; [| intros a Ha; cbn in Ha; apply STW; [clear - Ha; lia| clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia| clear - Ha; lia]].
    apply (rw_cells_agree _ _ _ _ _ AXP4) in F120; [| intros a Ha; cbn in Ha; apply STW; [clear - Ha; lia| clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia| clear - Ha; lia]].
    apply (rw_cells_agree _ _ _ _ _ AXP4) in FRLB; [| intros a Ha; cbn [cells_size csize] in Ha; rewrite ?Nat2Z.inj_add in Ha; apply STW; [clear - Ha; lia| clear - Ha GSZ SPAH TOP; unfold USTACK_TOP in *; lia| clear - Ha; lia]].
    apply (rw_cells_agree _ _ _ _ _ AXP4) in FRH; [| intros a Ha; cbn in Ha; apply STW; [clear - Ha SPAH; lia| clear - Ha TOP; unfold USTACK_TOP in *; lia| clear - Ha SPAH; lia]].
    unfold hidden in BQ5, BV5, DOT, DVT.
    apply (rw_cells_agree _ _ _ _ _ AXP4) in HOPP; [| intros a Ha; cbn in Ha; apply (BLW bq OPP 8 a Hbq BQ1 BQ2 BQ5 DOT); clear - Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AXP4) in HPV; [| intros a Ha; cbn in Ha; apply (BLW bv PV 8 a Hbv BV1 BV2 BV5 DVT); clear - Ha; lia].
    hide BQ5. hide BV5. hide DOT. hide DVT.
    apply (rw_cells_agree _ _ _ _ _ AXP4) in HFC.
    2:{ intros a Ha. cbn in Ha. pose proof OT as OT'. unfold hidden in OT'. split; [unfold LIBW_A; cbn [rin_ivs fst snd app]; clear - Ha G3 G4 OT' BT1 BT2 CEIL LO ESS SPAL; plia|].
        right; right. exists (qfc, f + 64, 1). split; [left; reflexivity| cbn; clear - Ha; lia]. }
    (* [comment removed for export] *)
    destruct (@AH_fr_wr (push AR f 2) _ _ _ _ f 2%nat HEAP8 (or_introl eq_refl)) as [WF8 WS8]. change (fs_size 2 - 8) with 248 in WF8. change (fs_size 2 / 8) with 32 in WS8.
    destruct (wr_at_rw_CB m8 f 248 WF8 ltac:(clear; lia)) as [jf8 FRF8]. destruct (wr_at_rw_CB m8 (shad f) 32 WS8 ltac:(clear; lia)) as [js8 FRS8]. clear WF8 WS8.
    change (Z.to_nat 248) with 248%nat in FRF8. change (Z.to_nat 32) with 32%nat in FRS8.
    apply (rw_cells_split_CB ctasegs _ _ [] 248 _ [] [32; 8; 208]%nat) in FRF8; [| reflexivity]. cbn [mk_CB_cells app] in FRF8.
    apply (rw_cells_split_CB ctasegs _ _ [] 32 _ [] [4; 1; 27]%nat) in FRS8; [| reflexivity]. cbn [mk_CB_cells app] in FRS8.
    lazymatch type of FRF8 with rw_cells _ _ _ [?c0; ?c1; ?c2] => change [c0; c1; c2] with ([c0] ++ [c1] ++ [c2]) in FRF8 end.
    apply rw_cells_app in FRF8 as [_ FRF8]. apply rw_cells_app in FRF8 as [HCONT _]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in HCONT.
    replace (f + Z.of_nat 32) with (f + 32) in HCONT by (clear; lia).
    lazymatch type of FRS8 with rw_cells _ _ _ [?c0; ?c1; ?c2] => change [c0; c1; c2] with ([c0] ++ [c1] ++ [c2]) in FRS8 end.
    apply rw_cells_app in FRS8 as [_ FRS8]. apply rw_cells_app in FRS8 as [HSH4 _]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in HSH4.
    replace (shad f + Z.of_nat 4) with (shad f + 4) in HSH4 by (clear; lia).
    (* [comment removed for export] *)
    clear IT0 IT8 IT8L IT16 IT32 ACCIT ACCQ. destruct (@item_cellsA_of (push AR f 2) _ _ _ _ e utype HEAP8 ENT) as (IT0 & IT8 & IT8L & IT16 & IT32 & ACCIT).
    pose proof (munch_refl [(spa, spa + 168); (shad f + 4, shad f + 5); (f + 32, f + 40)]%Z m8) as MU. pose proof (wmono_refl ctasegs m8) as WM.
    unfold frozen in HCONT. freeze HOPP. freeze HPV. freeze HTLC4. freeze HB. freeze HFC.
    apply implAp_from_evt.
    step. step. step. if_false. step. if_true.
    step. rewrite (sx32_small utype) by (clear - UTR; lia). step. step. step.
    pose proof (utype_casesA _ _ ENT) as UT.
    step. if_cases KU; zc KU; [| exfalso; rewrite land64_neg_small in KU by (clear - UT; lia); clear - KU UT; lia]. clear KU.
    (* [comment removed for export] *)
    step. step. if_cases K3; zc K3; [| exfalso; clear - K3 UT; lia]. clear K3. hide UT.
    step. step. if_true.
    (* [comment removed for export] *)
    step. step. step. step. rewrite ?(unsigned_lit (D + cont)) by (clear - D0 D63 GB1 GB2 GB3 OP0 OPT; lia). step. step.
    step. rewrite (sx32_small utype) by (clear - UTR; lia). step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8b end.
    match goal with H : munch _ m8 m8b |- _ => rename H into MU8b end.
    assert (ACCIT' : acc ctasegs m8b (item_ofA utype) 56).
    { eapply acc_agree; [apply (agree_on_of_munch_nw _ _ _ MU8b)| exact ACCIT|]. intros i Hi. cbn [outside fst snd].
      pose proof G5 as G5'. unfold hidden in G5'. unfold shad, SHB. clear - Hi ITR G5' G4 CL2 CEIL LO ESS SPAL. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl [(spa, spa + 168); (f + 32, f + 40)]%Z m8b) as MUb. clear ACCIT.
    assert (OFFW : offshW [(spa, spa + 168); (f + 32, f + 40)]%Z).
    { pose proof G5 as G5'. unfold hidden in G5'. cbn [offshW]. unfold SHLO, SHHI. clear - G5' CL2 CEIL LO ESS SPAL. lia. }
    (* [comment removed for export] *)
    step. step. step. step. if_true.
    (* [comment removed for export] *)
    step. step. step. if_cases KA; zc KA; [| exfalso; rewrite ?land64_neg_small, ?land64_pos_small in KA by (clear - UTR; lia); clear - KA UTR; lia]. clear KA.
    step. step.
    (* [comment removed for export] *)
    unfold hidden in UT.
    step. step. step. if_cases K9; zc K9; [exfalso; rewrite ?land64_neg_small, ?land64_pos_small in K9 by (clear - UT; lia); clear - K9 UT; lia|]. clear K9.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    match goal with H : munch _ m8 m9 |- _ => rename H into MU9 end. match goal with H : wmono ctasegs m8 m9 |- _ => rename H into WM9 end.
    match goal with H : stk ctasegs m9 lo _ |- _ => rename H into ST9 end. rewrite ?ESPA in ST9. match goal with H : mem_inv ctasegs m9 |- _ => rename H into MI9 end.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (OFF9 : forall b a, In b LB -> blk_addr b <= a < blk_addr b + blk_size b -> outside [(spa, spa + 168); (shad f + 4, shad f + 5); (f + 32, f + 40)]%Z a).
    { intros b a Hb Hr. pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _).
      pose proof (AH_offsh _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as RO. pose proof (OFFLB b Hb) as O.
      unfold off_fr in O. change (fs_size 2) with 256 in O. unfold SHLO, SHHI in RO. cbn [outside fst snd]. clear - Hr R3 RO O CEIL LO ESS SPAL SHR1 SHR2. plia. }
    assert (OUT9 : forall a, lib_addr OW4 a \/ aclient_addr LB (bv_unsigned sp) a -> outside [(spa, spa + 168); (shad f + 4, shad f + 5); (f + 32, f + 40)]%Z a).
    { intros a [[HS|(b & Hb & Hr)]|[H1|[H1|(b & Hb & Hr)]]].
      - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. cbn [outside fst snd]. clear - HA CL1 CEIL LO ESS SPAL G4 SHR1. lia.
      - pose proof (@AH_range_gen (push AR f 2) _ _ _ _ b HEAP8 (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R3 & _).
        pose proof (@AH_offsh (push AR f 2) _ _ _ _ b HEAP8 (in_or_app _ _ _ (or_introl Hb))) as RO.
        pose proof (@AH_ow_off_fr (push AR f 2) _ _ _ _ f 2%nat b HEAP8 (or_introl eq_refl) Hb) as O.
        unfold off_fr in O. change (fs_size 2) with 256 in O. unfold SHLO, SHHI in RO. cbn [outside fst snd]. clear - Hr R3 RO O CEIL1 LOSP1 ESS SHR1 SHR2. plia.
      - cbn [outside fst snd]. clear - H1 SPAH SHR2 CL2 G3 CEIL LO ESS. lia.
      - pose proof (CSB a H1) as HA. cbn [outside fst snd]. clear - HA CL1 CEIL LO ESS SPAL SHR1 G4. lia.
      - exact (OFF9 b a Hb Hr). }
    assert (LAG9 : agree_on (lib_addr OW4) m8 m9) by (eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU9)|]; intros a Ha; exact (OUT9 a (or_introl Ha))).
    (* [comment removed for export] *)
    pose proof BD5 as BD5'. unfold hidden in BD5'. assert (DTD' : D + zlength d <= TLC \/ TLC + 32 <= D) by (pose proof DTD as X; unfold hidden in X; clear - X; lia).
    unfold frozen in HOPP, HPV, HTLC4, HB, HFC.
    apply (bytes_at_agree _ _ _ _ _ AXP4) in HB; [| intros a Ha; rewrite DLEN in Ha; exact (BLW bd D (zlength d) a Hbd BD1 BD2 BD5' DTD' Ha)].
    apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU9)) in HB; [| intros a Ha; rewrite DLEN in Ha; apply (OFF9 bd a Hbd); clear - Ha BD1 BD2; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU9)) in HOPP; [| intros a Ha; cbn in Ha; apply (OFF9 bq a Hbq); clear - Ha BQ1 BQ2; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU9)) in HPV; [| intros a Ha; cbn in Ha; apply (OFF9 bv a Hbv); clear - Ha BV1 BV2; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU9)) in HTLC4; [| intros a Ha; cbn in Ha; apply (OFF9 bt a Hbt); clear - Ha BT1 BT2; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU9)) in HFC; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha FSH G3 CEIL LO ESS SPAL; plia].
    assert (PAY9 : payload_okA m9 LB D d).
    { destruct PAY3 as (_ & P2 & P3 & P4 & P5 & P6). split; [exact HB|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5| exact P6]. }
    (* [comment removed for export] *)
    assert (SH8 : shad (f + 64) = shad f + 8 /\ shad (f + 64 + (1 - 1)) = shad f + 8) by (unfold shad; clear - G2; Z.div_mod_to_equations; lia).
    assert (HEAP9f : @BnHeapA.AHEAP (push AR f 2) Σ4 OW4 LBf m9).
    { eapply (@AH_frame_frSA (push AR f 2) Σ4 OW4 LBf m8 m9 _ f 2%nat (or_introl eq_refl) HEAP8 MU9 WM9).
      - constructor; [left; left; cbn [fst snd]; clear - CEIL1 LOSP1 TOP1 SPAH GSZ TOP ESS; plia|].
        constructor; [right; right; cbn [fst snd]; change (fs_size 2 / 8) with 32; clear; lia|].
        constructor; [right; left; cbn [fst snd]; change (fs_size 2) with 256; clear; lia| constructor].
      - intros b Hb. subst LBf. destruct Hb as [<-|Hb]; [right| left; exact (OFFLB b Hb)].
        constructor; [cbn [fst snd blk_addr blk_size]; change (fs_size 2 / 8) with 32; intros [X1 X2]; exfalso; clear - X1 X2 SHR2 CL2 CEIL LO SPAL ESS; lia|].
        constructor; [cbn [fst snd blk_addr blk_size]; intros _; left; clear - SH8; lia|].
        constructor; [cbn [fst snd blk_addr blk_size]; change (fs_size 2 / 8) with 32; intros [X1 X2]; exfalso; clear - X1 X2 FSH; lia| constructor]. }
    destruct (bptr_fresh (map blk_id (OW4 ++ LBf))) as [qc Hqc].
    assert (HEAP9 : @BnHeapA.AHEAP (push AR f 2) Σ4 OW4 (ex_pbs qc qfc ++ LB) m9).
    { cbn [ex_pbs app]. subst LBf.
      apply (@frame_obj_open (push AR f 2) Σ4 OW4 _ m9 f 2%nat qc (f + 32) 8 (or_introl eq_refl) HEAP9f); [clear; lia| change (fs_size 2) with 256; clear; lia| clear; lia| | exact Hqc|].
      - eapply (acc_of_shadow_cells m9 (shad f + 4) _ 0 (f + 32) 8 HSH4); [clear - G2; Z.div_mod_to_equations; lia| clear - G1; lia| clear; lia
          | unfold shad; clear - G2; Z.div_mod_to_equations; lia| cbn; clear; lia| reflexivity].
      - intros b [<-|Hb]; [unfold blk_apart; cbn [blk_addr blk_size fst snd]; clear; lia|].
        pose proof (OFFLB b Hb) as O. unfold off_fr in O. change (fs_size 2) with 256 in O. unfold blk_apart. cbn [blk_addr blk_size fst snd]. clear - O. lia. }
    assert (PRE9 : @ap_preA (push AR f 2) Σ4 st m9 OW4 (ex_pbs qc qfc ++ LB) E bo (Z_to_bv 64 spa) lo 0 0 0).
    { eapply (@ap_preA_memA (push AR f 2)); [exact PRE4| exact HEAP9| exact LAG9| rewrite ?ESPA; exact ST9| exact MI9]. }
    assert (CRA : GETOBJ_ERR_COST_A + mcost plen <= rt_credit RT Σ4) by (unfold CHECK_TLEN_SPENT_A in CRED4; clear - CRED4 CRED1; lia).
    assert (CRB : rt_credit RT Σ - 2 <= rt_credit RT Σ4) by (unfold CHECK_TLEN_SPENT_A in CRED4; clear - CRED4 CR1; lia).
    (* [comment removed for export] *)
    assert (KEPT9 : blocks_kept K st OW4 m m9).
    { eapply (blocks_kept_post K st OW4 LB (bv_unsigned sp) m m8 m9).
      - eapply (blocks_kept_pre K st OW OW4 LB (bv_unsigned sp) m m7 m8); [exact KOW| | exact KEPT4].
        eapply agree_on_trans; [exact AGF|]. intros a Ha0 Ha. destruct Ha as [H1|[H1|(b & Hb & Hr)]]; [apply (AXG7 a Ha0); left; exact H1| apply (AXG7 a Ha0); right; left; exact H1|].
        apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply (LAG7 a Ha0); right; exists b; split; [exact Hb| exact Hr]| apply (AXG7 a Ha0); right; right; exists b; split; [exact Hb| exact Hr]].
      - intros a Ha0 Ha. apply (agree_on_of_munch_nw _ _ _ MU9 a Ha0). apply OUT9.
        destruct Ha as [H1|[H1|(b & Hb & Hr)]]; [right; left; exact H1| right; right; left; exact H1|].
        apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; right; exists b; split; [exact Hb| exact Hr]| right; right; right; exists b; split; [exact Hb| exact Hr]]. }
    assert (AXW : forall a, ax_client LB (bv_unsigned sp) ([(OPP, OPP + 8); (PV, PV + 8); (TLC, TLC + 32)] ++ LIBW_A) a ->
              ax_client LBf spa ([(spa + 112, spa + 112 + 8); (spa + 110, spa + 110 + 1); (spa + 111, spa + 111 + 1); (spa + 96, spa + 96 + 8); (TLC, TLC + 32)] ++ LIBW_A) a).
    { intros a [HX Ha]. unfold LIBW_A in HX. cbn [rin_ivs fst snd app] in HX. split.
      - unfold LIBW_A. cbn [rin_ivs fst snd app]. destruct Ha as [H1|[H1|(b & Hb & Hr)]].
        + clear - H1 HX SPAH. lia.
        + pose proof (CSB a H1) as HA. clear - HA HX CL1 CEIL LO ESS SPAL. lia.
        + pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R3 & _). clear - Hr R3 HX CEIL LO ESS SPAL. lia.
      - eapply acl_sub; [| | exact Ha]; [intros b Hb; apply INF; exact Hb| clear - SPAH; lia]. }
    assert (AXF : ax_pres LB (bv_unsigned sp) ([(OPP, OPP + 8); (PV, PV + 8); (TLC, TLC + 32)] ++ LIBW_A) m m9).
    { unfold ax_pres.
      eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a [_ Ha]; eapply acl_sub; [| | exact Ha]; [intros b Hb; apply in_or_app; right; exact Hb| clear; lia]|].
      eapply agree_on_trans; [eapply agree_on_mono; [exact AXG7|]; intros a [_ Ha]; exact Ha|].
      eapply agree_on_trans; [eapply agree_on_mono; [exact AXP4|]; intros a Ha; exact (AXW a Ha)|].
      eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU9)|]. intros a [_ Ha]. exact (OUT9 a (or_intror Ha)). }
    assert (AF9 : ex_arm_facts qc qfc Σ4 OW4 m9 jt4 j0 j8 j16 j64 j72 j80 j104 j120 j128 j136 j144).
    { unfold ex_arm_facts, ex_lowB. rewrite ?EOPP in FRLA. replace (plen + (D + cont)) with (D + cont + plen) in HPPC4 by (clear; lia). (* [comment removed for export] *)
      split; [exact HEAP9|]. split; [exact PRE9|]. split; [exact CRA|]. split; [exact CRB|]. split; [exact KEPT9|]. split; [exact AXF|].
      split; [exact FRLA|]. split; [exact HPPC4|]. split; [exact F104|]. split; [exact HINF4|]. split; [exact HCST4|]. split; [exact HOLEN4|]. split; [exact F120|].
      split; [exact FRLB|]. split; [exact FRH|]. split; [exact HCONT|]. split; [exact HFC|]. split; [exact HOPP|]. split; [exact HPV|]. split; [exact HTLC4| exact PAY9]. }
    clear OFF9 OUT9 LAG9 HB HOPP HPV HTLC4 HFC PAY9 SH8 HEAP9f HEAP9 PRE9 CRA CRB KEPT9 AXW AXF HEAP8 AS4 DC4 PRE4 AXP4 KEPT4 STW BLW LAG7 AXG7 PAY3.
    (* [comment removed for export] *)
    step. step. step. zstep.
    setreg 10 (Z_to_bv 64 (4 * (utype - 1) + 469524)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; lia).
    pose proof (jt_ex_prim_ofA m9 e utype MI9 ENT) as JT. replace (469524 + 4 * (utype - 1)) with (4 * (utype - 1) + 469524) in JT by (clear; lia).
    step. clear JT.
    destruct UT as [U4|[U2|U10]].
    - (* [comment removed for export] *)
      replace (jt_prim_entryA utype) with 1898084 by (unfold jt_prim_entryA; rewrite U4; reflexivity). rewrite (sx32_small 1898084) by (clear; lia).
      step. setreg 10 (Z_to_bv 64 0x242078) ltac:(reflexivity). step.
      apply evt_done. rewrite ?(ret_pc_even 0x242078) by (clear; lia). rewrite (d2i_prim_octE d op totlen utype st EG U4).
      eapply KOCT; [exact U4| exact AF9].
    - (* [comment removed for export] *)
      replace (jt_prim_entryA utype) with 1897752 by (unfold jt_prim_entryA; rewrite U2; reflexivity). rewrite (sx32_small 1897752) by (clear; lia).
      step. setreg 10 (Z_to_bv 64 0x241f2c) ltac:(reflexivity). step.
      apply evt_done. rewrite ?(ret_pc_even 0x241f2c) by (clear; lia). rewrite (d2i_prim_intE d op totlen utype st EG ltac:(rewrite U2; reflexivity)).
      eapply KINT; [left; exact U2| exact AF9].
    - (* [comment removed for export] *)
      replace (jt_prim_entryA utype) with 1897752 by (unfold jt_prim_entryA; rewrite U10; reflexivity). rewrite (sx32_small 1897752) by (clear; lia).
      step. setreg 10 (Z_to_bv 64 0x241f2c) ltac:(reflexivity). step.
      apply evt_done. rewrite ?(ret_pc_even 0x241f2c) by (clear; lia). rewrite (d2i_prim_intE d op totlen utype st EG ltac:(rewrite U10; reflexivity)).
      eapply KINT; [right; exact U10| exact AF9].
  Qed.
End Body.
End WithRT.
