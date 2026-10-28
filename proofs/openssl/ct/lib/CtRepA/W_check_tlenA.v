(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import I_strcpyA ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA Fr_asn1_check_tlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
(* [comment removed for export] *)
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Import CtRepP.W_get_object(land_32_cases, go_ret_cases, go_cls_cases, go_tag_range).
Import CtRepP.W_get_object_walk(signed_small, zxb_lit).
Notation go_ret_prim := CtRepP.W_check_tlen.go_ret_prim.
Notation tlc_in := CtRepP.W_check_tlen.tlc_in.

Definition CHECK_TLEN_A : Z := 0x2426a8.
Definition CHECK_TLEN_GO_RA : Z := 0x24295c.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CHECK_TLEN_STACK_A : Z := ACTL_FRAME + GETOBJ_STACK_A.
(* [comment removed for export] *)
Definition CHECK_TLEN_COST_A : Z := 1 + GETOBJ_ERR_COST_A.
(* [comment removed for export] *)
Definition CHECK_TLEN_SPENT_A : Z := 1.
Definition CHECK_TLEN_FRAMES_A : Z := 1 + GETOBJ_FRAMES_A.

Section Kit.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma implAp_seq_ret : forall {A B} (a : A) (t : aprog bptr B) Σ (Q1 : A -> rts RT -> machine_state -> Prop) Q ms,
  implAp (ARet a) Σ Q1 ms -> (forall Σ' ms', Q1 a Σ' ms' -> implAp t Σ' Q ms') -> implAp t Σ Q ms.
Proof.
  intros A B a t Σ Q1 Q ms H HK X Φ D S L T c Hc Hk.
  apply (H X (fun a' X' => a' = a /\ X' = X) D ltac:(cbn [asafe]; split; reflexivity) L T c Hc).
  intros c' (a' & X' & Σ' & [-> ->] & L' & Hc').
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HQ1 & Hc'').
  exact (HK Σ' ms' HQ1 X Φ D S L' T c' Hc'' Hk).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma actl_open_one : forall Σ1 OW LB m3 f q A n k,
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m3 -> @fr_geo (push AR f 1) f 1 ->
  rw_cells ctasegs m3 (shad f) actl_shadow_pro ->
  f <= A -> A + n <= f + 120 -> 0 < n -> A mod 8 = 0 -> shad A = shad f + Z.of_nat k -> (k <= 16)%nat ->
  firstn (length (ushadow n)) (skipn k (cells_bytes actl_shadow_pro)) = ushadow n ->
  ~ In q (map blk_id (OW ++ LB)) -> (forall b, In b LB -> blk_apart (q, A, n) b) ->
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((q, A, n) :: LB) m3.
Proof.
  intros Σ1 OW LB m3 f q A n k HEAP GEO FRS A1 A2 Hn A8 Hs Hk Hf Hq AP.
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  apply (@frame_obj_open (push AR f 1) Σ1 OW LB m3 f 1%nat q A n (or_introl eq_refl) HEAP A1); [change (fs_size 1) with 128; clear - A2; lia | exact Hn | | exact Hq | exact AP].
  apply (acc_of_shadow_cells m3 (shad f) actl_shadow_pro k A n FRS A8 ltac:(clear - G1 A1; lia) ltac:(clear - Hn; lia) Hs); [| exact Hf].
  clear - Hk. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition actl_pbs (f : Z) (qp ql qt qc : bptr) : list block := [(qp, f + 96, 8); (ql, f + 64, 8); (qt, f + 32, 4); (qc, f + 48, 4)].

Lemma actl_open_pbs : forall Σ1 OW LB m3 f,
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m3 -> (forall b, In b (OW ++ LB) -> off_fr f 1 b) -> @fr_geo (push AR f 1) f 1 ->
  rw_cells ctasegs m3 (shad f) actl_shadow_pro ->
  exists qp ql qt qc, @BnHeapA.AHEAP (push AR f 1) Σ1 OW (actl_pbs f qp ql qt qc ++ LB) m3.
Proof.
  intros Σ1 OW LB m3 f HEAP3 FRESH GEO FRS.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (SH : forall i, 0 <= i -> shad (f + i) = shad f + i / 8) by (intros i Hi; exact (shad_aligned_add f i F8 Hi)).
  assert (APL : forall q A n b, f + 32 <= A -> A + n <= f + 120 -> In b LB -> blk_apart (q, A, n) b).
  { intros q A n b HA HA2 Hb. pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 1) with 128 in O.
    cbn [blk_addr blk_size fst snd]. clear - O HA HA2. lia. }
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [qc Hqc].
  pose proof (actl_open_one Σ1 OW LB m3 f qc (f + 48) 4 6%nat HEAP3 GEO FRS ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(rewrite SH by (clear; lia); clear; cbn; lia) ltac:(clear; lia) eq_refl Hqc
                ltac:(intros b Hb; apply APL; [clear; lia| clear; lia| exact Hb])) as HEAPc.
  set (LBc := (qc, f + 48, 4) :: LB) in HEAPc.
  destruct (bptr_fresh (map blk_id (OW ++ LBc))) as [qt Hqt].
  pose proof (actl_open_one Σ1 OW LBc m3 f qt (f + 32) 4 4%nat HEAPc GEO FRS ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(rewrite SH by (clear; lia); clear; cbn; lia) ltac:(clear; lia) eq_refl Hqt
                ltac:(intros b [<-|Hb]; [unfold blk_apart; cbn; clear; lia| apply APL; [clear; lia| clear; lia| exact Hb]])) as HEAPt.
  set (LBt := (qt, f + 32, 4) :: LBc) in HEAPt.
  destruct (bptr_fresh (map blk_id (OW ++ LBt))) as [ql Hql].
  pose proof (actl_open_one Σ1 OW LBt m3 f ql (f + 64) 8 8%nat HEAPt GEO FRS ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(rewrite SH by (clear; lia); clear; cbn; lia) ltac:(clear; lia) eq_refl Hql
                ltac:(intros b [<-|[<-|Hb]]; [unfold blk_apart; cbn; clear; lia| unfold blk_apart; cbn; clear; lia| apply APL; [clear; lia| clear; lia| exact Hb]])) as HEAPl.
  set (LBl := (ql, f + 64, 8) :: LBt) in HEAPl.
  destruct (bptr_fresh (map blk_id (OW ++ LBl))) as [qp Hqp].
  pose proof (actl_open_one Σ1 OW LBl m3 f qp (f + 96) 8 12%nat HEAPl GEO FRS ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(rewrite SH by (clear; lia); clear; cbn; lia) ltac:(clear; lia) eq_refl Hqp
                ltac:(intros b [<-|[<-|[<-|Hb]]]; [unfold blk_apart; cbn; clear; lia| unfold blk_apart; cbn; clear; lia| unfold blk_apart; cbn; clear; lia
                      | apply APL; [clear; lia| clear; lia| exact Hb]])) as HEAPp.
  subst LBl LBt LBc. exists qp, ql, qt, qc. exact HEAPp.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma payload_okA_agreeA : forall m m' LB D d,
  payload_okA m LB D d -> agree_on (fun a => in_block LB a) m m' -> payload_okA m' LB D d.
Proof.
  intros m m' LB D d (BY & FB & D0 & DH & DL & HB) AG.
  split; [| repeat (split; [assumption|]); exact HB].
  destruct HB as [->|(b & Hb & H1 & H2)].
  { cbn [to_bytes map]. apply bytes_at_nil. unfold zlength in DH. cbn in DH. lia. }
  apply (bytes_at_agree _ m m' _ _ AG BY). intros x Hx.
  exists b. split; [exact Hb|]. unfold to_bytes in Hx. rewrite length_map in Hx. unfold zlength in H2. lia.
Qed.

Lemma payload_okA_monoA : forall m LB LB' D d,
  payload_okA m LB D d -> (forall b, In b LB -> In b LB') -> payload_okA m LB' D d.
Proof.
  intros m LB LB' D d (BY & FB & D0 & DH & DL & HB) INC. split; [exact BY|]. split; [exact FB|]. split; [exact D0|]. split; [exact DH|]. split; [exact DL|].
  destruct HB as [E|(b & Hb & H1 & H2)]; [left; exact E| right]. exists b. split; [exact (INC b Hb)|]. split; [exact H1| exact H2].
Qed.


Lemma rw_cells_CB_ofA : forall m A cs, rw_cells ctasegs m A cs -> rw_cells ctasegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs [[W B] R]. split; [split|].
  - cbn. split; [| exact I]. apply cells_bytes_length. exact W.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact R.
Qed.

(* [comment removed for export] *)
Lemma ap_preA_memA : forall Σ st m m' OW LB LB' E bo (sp : word) lo S C F,
  ap_preA Σ st m OW LB E bo sp lo S C F -> AHEAP Σ OW LB' m' -> agree_on (lib_addr OW) m m' ->
  stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
  ap_preA Σ st m' OW LB' E bo sp lo S C F.
Proof.
  intros until F. intros (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM) HEAP' AG ST' MI'.
  pose proof AS as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD)).
  unfold ap_preA. split; [exact HEAP'|]. split; [exact (ap_state_agree _ _ _ _ _ _ AS AG)|]. split; [exact IDS|].
  split; [exact (data_cells_agree _ _ _ _ DC AG OD)|]. split; [exact ST'|]. split; [exact CEIL|]. split; [exact LOSP|].
  split; [exact TOP|]. split; [exact AL16|]. split; [exact MI'|]. split; [exact CRED| exact FRM].
Qed.

End Kit.

Local Notation E_go := (E_asn1_check_tlen_2453ec : uk_call 0x2426a8 0x2429a0 0x223b30).   (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition check_tlen_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (m : mem) (K : list block)
    (D POLEN PINF PCST PPC TLC : Z) (g : go_res) (r : unit * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (jt : list byte),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' LB E bo sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(POLEN, POLEN + 8); (PINF, PINF + 1); (PCST, PCST + 1); (PPC, PPC + 8); (TLC, TLC + 32)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - CHECK_TLEN_SPENT_A <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ rw_cells ctasegs m' POLEN [C8 (wz (go_len g))] /\ rw_cells ctasegs m' PINF [C1 (Z_to_bv 8 0)] /\ rw_cells ctasegs m' PCST [C1 (Z_to_bv 8 0)]
    /\ rw_cells ctasegs m' PPC [C8 (wz (D + go_p g))] /\ rw_cells ctasegs m' TLC [CB 32 jt].
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition check_tlen_specA : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (D : Z) (d : list Z) (op totlen exptag POLEN PINF PCST PPC TLC : Z) (jl : list byte) (bi bc : byte) (j31 : list byte),
    ap_preA Σ st m OW LB E bo sp lo CHECK_TLEN_STACK_A CHECK_TLEN_COST_A CHECK_TLEN_FRAMES_A -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CHECK_TLEN_A (bv_unsigned ra :: ras) -> ras <> nil ->   (* [comment removed for export] *)
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_okA m LB D d -> 0 <= op -> 0 < totlen -> op + totlen <= zlength d ->
    go_err (get_object d op totlen) = None -> go_tag (get_object d op totlen) = exptag -> go_cls (get_object d op totlen) = 0 ->
    Z.land (go_ret (get_object d op totlen)) 32 = 0 -> 0 <= exptag < 2^31 ->
    (* [comment removed for export] *)
    bv_unsigned sp <= PPC -> PPC + 8 <= PINF -> PINF + 1 = PCST -> PCST + 1 <= POLEN -> POLEN + 8 <= USTACK_TOP ->
    PPC mod 8 = 0 -> POLEN mod 8 = 0 ->
    (* [comment removed for export] *)
    cellA_in LB TLC 32 -> TLC mod 8 = 0 ->
    rw_cells ctasegs m POLEN [CB 8 jl] -> rw_cells ctasegs m PINF [C1 bi] -> rw_cells ctasegs m PCST [C1 bc] ->
    rw_cells ctasegs m PPC [C8 (wz (D + op))] -> rw_cells ctasegs m TLC (tlc_in j31) ->
    a0 = wz POLEN -> a1 = wz 0 -> a2 = wz 0 -> a3 = wz PINF -> a4 = wz PCST -> a5 = wz PPC -> a6 = wz totlen -> a7 = wz exptag ->
    t3 = wz 0 -> t4 = wz 0 -> t5 = wz TLC ->
    implAp (aret tt st) Σ
           (check_tlen_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K D POLEN PINF PCST PPC TLC (get_object d op totlen))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz CHECK_TLEN_A) fc None m (seg_rom ctasegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Proofs.
  (* [comment removed for export] *)
  Hypothesis STRCPY : strcpy_icontract RT.
  Hypothesis HGO : forall AR' : ARun, strcpy_icontract (@ar_RT AR') -> @ASN1_get_object_specA AR' UK.

  Theorem check_tlen_walkA : check_tlen_specA.
  Proof.
    unfold check_tlen_specA. intros until j31.
    intros PRE TP UW CTX RNE KOW KIDS PAY OP0 TL0 OPT EG ETAG ECLS ERET XT SPP A1 A2 A3 A4 AL1 AL2 CIT ALT HOLEN HINF HCST HPPC HTLC -> -> -> -> -> -> -> -> -> -> ->.
    pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    unfold CHECK_TLEN_STACK_A, CHECK_TLEN_COST_A, CHECK_TLEN_FRAMES_A, ACTL_FRAME in LOSP, CRED, FRM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3).
    pose proof (conj C1 (conj C2 C3)) as CN. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CN.
    assert (VPOS : 0 <= GETOBJ_STACK_A /\ 0 <= GETOBJ_ERR_COST_A /\ 0 <= GETOBJ_FRAMES_A /\ RT_STACK <= GETOBJ_STACK_A)
      by (unfold GETOBJ_STACK_A, GETOBJ_ERR_COST_A, GETOBJ_FRAMES_A, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, ERR_NEW_COST, ERR_SET_DEBUG_COST,
                 ERR_SET_ERROR_COST, ERR_VSET_ERROR_COST, ERR_SET_ERROR_FRAMES, ERR_VSET_ERROR_FRAMES, RT_STACK; clear; lia).
    pose proof PAY as (HB & PF & D0 & D63 & D26 & HBLK).
    destruct HBLK as [->|(bd & HBD & PA1 & PA2)]; [exfalso; unfold zlength in OPT; cbn in OPT; clear - OPT OP0 TL0; lia|].
    assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
    pose proof A4 as A4N. unfold USTACK_TOP in A4N.   (* [comment removed for export] *)
    unfold CtRepP.W_check_tlen.tlc_in in HTLC.
    (* [comment removed for export] *)
    destruct CIT as (bt & HBT & TB1 & TB2).
    assert (HBT' : In bt (OW ++ LB)) by (apply in_or_app; right; exact HBT).
    pose proof (AH_range_gen _ _ _ _ _ HEAP HBT') as (BT0 & _ & _ & BT3 & BT4).
    intros X Φ Dl SAFE LINK.
    change (wz CHECK_TLEN_A) with (wz ACTL_ENTRY).
    eapply (actl_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
      [exact HEAP | exact ST | exact CEIL | unfold ACTL_FRAME; clear - LOSP VPOS; lia | exact TOP | exact AL16
      | unfold MallocRep.wz; rewrite unsigned_lit by (clear - SPP SPR A1 A2 A3 A4N; lia); exact AL1 | exact MI | exact TP
      | clear - FRM VPOS; lia | clear - CRED VPOS; lia |].
    intros Σ1 m3 f spa gg junk gj ra' t0' t1' t2' a5' a7' t3' t4' t5' t6' F' fc' j0 j8 j16 j24 j32 j40 j48 j56 j104 j128 j136 j144
           jf24 jf32 jf36 jf48 jf52 jf64 jf72 jf96 jf104 HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
    unfold MallocRep.wz in FRL, FRH.
    set (g := get_object d op totlen) in *.
    pose proof (go_ret_prim d op totlen EG ERET) as RET0. fold g in RET0.
    pose proof (get_object_bounds d op totlen ltac:(eapply Forall_impl; [| exact PF]; cbv beta; intros; lia) TL0) as GB.
    cbv zeta in GB. fold g in GB. rewrite EG in GB. destruct GB as (GB1 & GB2 & GB3).
    assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CN CEIL LOSP SPAL SPAH SPR TOP VPOS LO0; alia).
    pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5. unfold SEGTOP_A in G4. cbn [ar_SP0 push amb] in G3.
    assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 CN; alia).
    (* [comment removed for export] *)
    pose proof (pro_closeA Σ st m OW LB E bo sp lo _ _ _ f 1%nat Σ1 m3 spa 256 PRE HEAP3 ST3 MI3 AGF CR1 SPA32
                  ltac:(clear - SPAL; lia) ltac:(clear - SPAH; lia) ltac:(clear; lia) ltac:(unfold CHECK_TLEN_STACK_A, ACTL_FRAME; clear - VPOS; lia)
                  ltac:(unfold CHECK_TLEN_COST_A; clear - VPOS; lia) ltac:(unfold CHECK_TLEN_FRAMES_A; clear - VPOS; lia)) as PRE1.
    unfold CHECK_TLEN_STACK_A, CHECK_TLEN_COST_A, CHECK_TLEN_FRAMES_A, ACTL_FRAME in PRE1.
    replace (272 + GETOBJ_STACK_A - 256 - 16) with GETOBJ_STACK_A in PRE1 by (clear; lia).
    replace (1 + GETOBJ_ERR_COST_A - 1) with GETOBJ_ERR_COST_A in PRE1 by (clear; lia).
    replace (1 + GETOBJ_FRAMES_A - 1) with GETOBJ_FRAMES_A in PRE1 by (clear; lia).
    pose proof PRE1 as (_ & AS1 & IDS1 & DC1 & ST1 & CEIL1 & LOSP1 & TOP1 & AL161 & MI1 & CRED1 & FRM1).
    rewrite ESPA in ST1, LOSP1, TOP1, AL161. cbn [ar_FR ar_RT ar_SP0 push amb] in CRED1, FRM1, CEIL1.
    (* [comment removed for export] *)
    destruct (actl_open_pbs Σ1 OW LB m3 f HEAP3 FRESH GEO FRS) as (qp & ql & qt & qc & HEAPX).
    set (pbs := actl_pbs f qp ql qt qc) in HEAPX.
    assert (INX : forall b, In b LB -> In b (pbs ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (OFFOW : forall b, In b OW -> off_fr f 1 b) by (intros b Hb; apply FRESH; apply in_or_app; left; exact Hb).
    assert (OFFLB : forall b, In b LB -> off_fr f 1 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
    pose proof (OFFLB bt HBT) as OT. unfold off_fr in OT. change (fs_size 1) with 128 in OT. cbn [blk_addr blk_size fst snd] in OT.
    pose proof (OFFLB bd HBD) as OD. unfold off_fr in OD. change (fs_size 1) with 128 in OD. cbn [blk_addr blk_size fst snd] in OD.
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AGF) in HOLEN; [| intros a Ha; cbn in Ha; left; clear - Ha SPP A1 A2 A3 A4; unfold USTACK_TOP in *; lia].
    apply (rw_cells_agree _ _ _ _ _ AGF) in HINF; [| intros a Ha; cbn in Ha; left; clear - Ha SPP A1 A2 A3 A4; unfold USTACK_TOP in *; lia].
    apply (rw_cells_agree _ _ _ _ _ AGF) in HCST; [| intros a Ha; cbn in Ha; left; clear - Ha SPP A1 A2 A3 A4; unfold USTACK_TOP in *; lia].
    apply (rw_cells_agree _ _ _ _ _ AGF) in HPPC; [| intros a Ha; cbn in Ha; left; clear - Ha SPP A1 A2 A3 A4; unfold USTACK_TOP in *; lia].
    apply (rw_cells_agree _ _ _ _ _ AGF) in HTLC; [| intros a Ha; cbn in Ha; right; right; exists bt; split; [exact HBT'| clear - Ha TB1 TB2; lia]].
    assert (PAY3 : payload_okA m3 LB D d).
    { eapply payload_okA_agreeA; [exact PAY|]. eapply agree_on_mono; [exact AGF|]. intros a Ha. right; right. eapply in_block_mono; [| exact Ha]. intros b Hb; apply in_or_app; right; exact Hb. }
    clear HB.
    (* [comment removed for export] *)
    lazymatch type of FRF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: nil) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: nil)
        with ([c0; c1; c2; c3] ++ [c4] ++ [c5] ++ [c6] ++ [c7] ++ [c8] ++ [c9] ++ [c10] ++ [c11]) in FRF end.
    apply rw_cells_app in FRF as [_ FRF]. apply rw_cells_app in FRF as [OT3 FRF]. apply rw_cells_app in FRF as [_ FRF].
    apply rw_cells_app in FRF as [OC3 FRF]. apply rw_cells_app in FRF as [_ FRF]. apply rw_cells_app in FRF as [OL3 FRF].
    apply rw_cells_app in FRF as [_ FRF]. apply rw_cells_app in FRF as [OP3 _].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in OT3, OC3, OL3, OP3.
    replace (f + Z.of_nat 32) with (f + 32) in OT3 by (clear; lia).
    replace (f + 32 + 4 + 12) with (f + 48) in OC3 by (clear; lia).
    replace (f + 32 + 4 + 12 + 4 + 12) with (f + 64) in OL3 by (clear; lia).
    replace (f + 32 + 4 + 12 + 4 + 12 + 8 + 24) with (f + 96) in OP3 by (clear; lia).
    clear FRS.
    (* [comment removed for export] *)
    assert (ACCS : acc ctasegs m3 PPC (POLEN + 8 - PPC)).
    { destruct HEAP3 as (HA3 & HS3 & _). apply (af_acc_stack RT AF Σ1 m3 _ _ HA3); [| clear - A4; lia].
      rewrite HS3. cbn [ar_SP0 push amb]. unfold BnHeapA.ACEIL in CEIL. clear - CEIL LOSP SPP VPOS. lia. }
    pose proof (proj2 (@AH_acc (push AR f 1) _ _ _ _ bt HEAPX ltac:(apply in_or_app; right; apply INX; exact HBT))) as ACCT.
    pose proof (@AH_offsh (push AR f 1) _ _ _ _ bt HEAPX ltac:(apply in_or_app; right; apply INX; exact HBT)) as OFFT.
    assert (ETLC : bv_unsigned (Z_to_bv 64 TLC) = TLC) by (apply unsigned_lit; clear - BT0 BT3 TB1 TB2 CN; alia).
    assert (EPPC : bv_unsigned (Z_to_bv 64 PPC) = PPC) by (apply unsigned_lit; clear - SPP SPR A1 A2 A3 A4; unfold USTACK_TOP in *; lia).
    pose proof (munch_refl [(spa, spa + 152); (f + 96, f + 104)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
    assert (OFF3 : offshW [(spa, spa + 152); (f + 96, f + 104)]%Z).
    { cbn [offshW]. clear - CN CEIL LOSP SPAL G5 VPOS. plia. }
    eapply (implAp_elim (aret tt st)); [| exact SAFE | exact LINK | exact EL1].
    unfold ACTL_BODY, MallocRep.wz. apply implAp_from_evt.
    (* [comment removed for export] *)
    pose proof HTLC as HTLC0. pose proof HPPC as HPPC0.
    repeat match goal with H : rw_cells ctasegs m3 ?a _ |- _ =>
      lazymatch H with HOLEN => idtac | HINF => idtac | HCST => idtac | HTLC0 => idtac | HPPC0 => idtac | HTLC => idtac end;
      let T := type of H in change (frozen T) in H end.
    (* [comment removed for export] *)
    ab_shload 8. step. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. rewrite ?zxb_z8, ?sxb_z8. if_false. step. step. step.
    step. if_cases KLEN; zc KLEN; [exfalso; revert KLEN; rewrite ?signed_small by (clear - TL0 OPT D26 OP0; lia); clear - TL0 OPT D26 OP0; lia|].
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    step. if_cases KCTX; zc KCTX; [exfalso; rewrite ?ETLC in KCTX; clear - KCTX BT0 TB1; lia|]. clear KCTX.
    (* [comment removed for export] *)
    step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with MU : munch _ m3 mx |- _ =>
        unfold frozen in HTLC; eapply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in HTLC;
          [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; clear - Ha BT3 TB1 TB2 OT CEIL LOSP SPAL VPOS; plia]
      end end.
    (* [comment removed for export] *)
    step. step.
    step. if_true.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    match goal with H : munch _ m3 mc |- _ => rename H into MUc end. match goal with H : wmono ctasegs m3 mc |- _ => rename H into WMc end.
    match goal with H : stk ctasegs mc lo spa |- _ => rename H into STc end. match goal with H : mem_inv ctasegs mc |- _ => rename H into MIc end.
    apply evt_done.
    (* [comment removed for export] *)
    assert (HEAPc : @BnHeapA.AHEAP (push AR f 1) Σ1 OW (pbs ++ LB) mc).
    { eapply (@AH_frame (push AR f 1)); [exact HEAPX| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; clear - CEIL1 LOSP1 TOP1 SPAL SPAH TOP VPOS; plia|].
      constructor; [right; right; exists (qp, f + 96, 8); split; [apply in_or_app; right; apply in_or_app; left; left; reflexivity| cbn; clear; lia]| constructor]. }
    assert (AGLc : agree_on (lib_addr OW) m3 mc).
    { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUc)|]. intros a HL. cbn [outside fst snd].
      destruct HL as [HS|(b & Hb & Hr)].
      - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. clear - HA G4 CN CEIL LOSP SPAL VPOS. plia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & _ & R4 & _). pose proof (OFFOW b Hb) as O.
        unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[q A] n]; cbn [blk_addr blk_size fst snd] in Hr, R4, O. clear - Hr R4 O CEIL LOSP SPAL VPOS. lia. }
    assert (PREc : @ap_preA (push AR f 1) Σ1 st mc OW (pbs ++ LB) E bo (Z_to_bv 64 spa) lo GETOBJ_STACK_A GETOBJ_ERR_COST_A GETOBJ_FRAMES_A).
    { eapply (@ap_preA_memA (push AR f 1)); [exact PRE1| exact HEAPc| exact AGLc| rewrite ESPA; exact STc| exact MIc]. }
    assert (PAYc : payload_okA mc (pbs ++ LB) D d).
    { eapply payload_okA_monoA; [| exact INX]. eapply payload_okA_agreeA; [exact PAY3|].
      eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUc)|]. intros a (b & Hb & Hr). cbn [outside fst snd].
      pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R4 & _). pose proof (OFFLB b Hb) as O.
      unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[q A] n]; cbn [blk_addr blk_size fst snd] in Hr, R4, O. clear - Hr R4 O CEIL LOSP SPAL VPOS. lia. }
    assert (CIN : forall q A n, In (q, A, n) pbs -> cellA_in (pbs ++ LB) A n).
    { intros q A n Hin. exists (q, A, n). split; [apply in_or_app; left; exact Hin| cbn; clear; lia]. }
    assert (GC : go_cellsA_ok (pbs ++ LB) (f + 96) (f + 64) (f + 32) (f + 48)).
    { split; [apply (CIN qp); subst pbs; cbn; tauto|]. split; [apply (CIN ql); subst pbs; cbn; tauto|]. split; [apply (CIN qt); subst pbs; cbn; tauto|].
      split; [apply (CIN qc); subst pbs; cbn; tauto|]. clear - G2. Z.div_mod_to_equations. lia. }
    assert (GOFF : go_cells_offA D (zlength d) (f + 96) (f + 64) (f + 32) (f + 48)).
    { unfold go_cells_offA. clear - OD PA1 PA2. lia. }
    replace (aret tt st) with (go_eff g st) by (unfold CtRepP.W_get_object.go_eff; rewrite EG; reflexivity).
    eapply implAp_post.
    { eapply (HGO (push AR f 1) STRCPY) with (K := K) (LB := pbs ++ LB) (lo := lo) (D := D) (d := d) (op := op) (omax := totlen)
                                      (PP := f + 96) (PL := f + 64) (PT := f + 32) (PC := f + 48);
        [exact PREc| reflexivity| | | apply cons_ne| exact KOW| exact KIDS| exact PAYc| exact OP0| exact TL0| exact OPT| exact GC| exact GOFF
        | exact OP3| exact OL3| exact OT3| exact OC3| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity].
      - (* [comment removed for export] *)
        assert (FLO0 : f + 128 <= spa) by (clear - G3 CEIL LOSP SPAL VPOS; plia).
        rewrite ESPA.
        eapply (uw_call m mc spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
          [ exact UW
          | eapply agree_on_trans; [ eapply agree_on_mono; [exact AGF|]; intros a Ha; left; exact Ha
                                   | eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUc)|]; intros a Ha; cbn [outside fst snd]; clear - Ha SPAH FLO0; lia ]
          | reflexivity | clear - SPAH; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia
          | apply bv_unsigned_in_range | rewrite !Z_to_bv_bv_unsigned; cbn [app]; exact FRH ].
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_go CTX). }
    clear CIN GC GOFF PAYc.
    intros [[] st'] Σ4 ms4 PO4. cbv beta in PO4. unfold getobj_postA in PO4. cbn [fst snd] in PO4. fold g in PO4. rewrite EG in PO4. unfold MallocRep.wz in PO4. rewrite ?ESPA in PO4.
    destruct PO4 as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m4 & OW4 & jl4 & jt4 & jc4
                     & -> & PRE4 & AXP4 & CRED4 & KEPT4 & HPP4 & -> & HPL4 & HPT4 & HPC4).
    clear HTLC ACCS ACCT STc MIc PREc HEAPc.
    rewrite (ret_pc_even 0x2429a0) by (clear; lia). rewrite RET0.
    pose proof PRE4 as (HEAP4 & AS4 & IDS4 & DC4 & ST4 & CEIL4 & LOSP4 & TOP4 & AL164 & MI4 & _ & FRM4).
    cbn [ar_FR ar_RT ar_SP0 push amb] in CRED4.
    assert (TLCLO : TLC + 32 <= spa) by (clear - BT3 TB2 CEIL LOSP SPAL VPOS; plia).
    assert (FLO : f + 128 <= spa) by (clear - G3 CEIL LOSP SPAL VPOS; plia).
    (* [comment removed for export] *)
    assert (STW : forall a, spa <= a -> a < USTACK_TOP ->
              ax_client (pbs ++ LB) spa ([(f + 96, f + 96 + 8); (f + 64, f + 64 + 8); (f + 32, f + 32 + 4); (f + 48, f + 48 + 4)] ++ LIBW_A) a).
    { intros a Ha Hb. split; [| left; clear - Ha Hb; lia]. unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha FLO CN CEIL LOSP SPAL VPOS. plia. }
    assert (TLW : forall a, TLC <= a < TLC + 32 ->
              ax_client (pbs ++ LB) spa ([(f + 96, f + 96 + 8); (f + 64, f + 64 + 8); (f + 32, f + 32 + 4); (f + 48, f + 48 + 4)] ++ LIBW_A) a).
    { intros a Ha. split.
      - unfold LIBW_A. cbn [rin_ivs fst snd app]. clear - Ha OT TB1 TB2 BT4. lia.
      - right; right. exists bt. split; [apply INX; exact HBT| clear - Ha TB1 TB2; lia]. }
    (* [comment removed for export] *)
    assert (OUT1T : forall a, TLC <= a < TLC + 32 -> outside [(spa, spa + 152); (f + 96, f + 104)]%Z a).
    { intros a Ha. cbn [outside fst snd]. clear - Ha TLCLO OT TB1 TB2. lia. }
    assert (OUT1S : forall a, bv_unsigned sp <= a -> outside [(spa, spa + 152); (f + 96, f + 104)]%Z a).
    { intros a Ha. cbn [outside fst snd]. clear - Ha SPAH FLO. lia. }
    apply (rw_cells_agree _ _ _ _ _ AXP4) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW; clear - Ha GSZ SPAH TOP; unfold USTACK_TOP in *; lia].
    apply (rw_cells_agree _ _ _ _ _ AXP4) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW; clear - Ha SPAH TOP; unfold USTACK_TOP in *; lia].
    unfold frozen in HTLC0. apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in HTLC0; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply OUT1T; clear - Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AXP4) in HTLC0; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply TLW; clear - Ha; lia].
    rename HTLC0 into HTLC.
    (* [comment removed for export] *)
    pose proof (proj2 (@AH_acc (push AR f 1) _ _ _ _ bt HEAP4 ltac:(apply in_or_app; right; apply INX; exact HBT))) as ACCT.
    pose proof (munch_refl [(TLC, TLC + 32)]%Z m4) as MU4. pose proof (wmono_refl ctasegs m4) as WM4.
    assert (OFF4 : offshW [(TLC, TLC + 32)]%Z) by (cbn [offshW]; clear - OFFT TB1 TB2; unfold SHLO, SHHI in *; lia).
    rewrite ECLS in HPC4. rewrite ETAG in HPT4.
    apply implAp_from_evt.
    (* [comment removed for export] *)
    step. step. step.
    (* [comment removed for export] *)
    step. step. step. ab_shload 4. step. step. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). step. step. step.
    step. rewrite ?zxb_z8, ?sxb_z8. if_false. step.
    (* [comment removed for export] *)
    step. step. step. ab_shload 4. step. rewrite (sx32_small exptag) by (clear - XT; lia).
    step. step. rewrite ?zxb_z8, ?sxb_z8. if_false. step.
    (* [comment removed for export] *)
    step. step. step. ab_shload 4. step.
    step. rewrite ?zxb_z8, ?sxb_z8. if_false.
    step. zstep. unfold MallocRep.wz. rewrite ?(unsigned_lit (D + op)) by (clear - D0 OP0 OPT D63 TL0; lia).
    assert (EHL : bv_swrap 32 (D + go_p g - (D + op)) = go_p g - op) by (rewrite bn_swrap32_small by (clear - GB1 GB2 GB3 OPT D26 OP0 TL0; lia); clear; lia).
    rewrite EHL. clear EHL.
    step.
    (* [comment removed for export] *)
    ab_shload 1. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. rewrite ?zxb_z8, ?sxb_z8. if_false.
    step. zstep. step. step.
    step. if_false.
    (* [comment removed for export] *)
    step.
    (* [comment removed for export] *)
    step. if_cases KTL; zc KTL; [try clear KTL| exfalso; revert KTL; rewrite ?signed_small by (clear - GB1 GB2 GB3 OPT D26 OP0 TL0; lia); clear - GB3; lia].
    (* [comment removed for export] *)
    zstep. step. if_false.
    step. step. step.
    step. if_cases KXN; zc KXN; [exfalso; revert KXN; unfold MallocRep.wz; rewrite ?signed_small by (clear - XT; lia); clear - XT; lia|].
    step. rewrite (sx32_small exptag) by (clear - XT; lia). step. if_false.
    step. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). step. step. if_false.
    step. if_cases KC2; zc KC2; [exfalso; rewrite ?ETLC in KC2; clear - KC2 BT0 TB1; lia|].
    (* [comment removed for export] *)
    step. step.
    step. if_true.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into ma end.
    match goal with H : munch _ m4 ma |- _ => rename H into MUa end. match goal with H : wmono ctasegs m4 ma |- _ => rename H into WMa end.
    assert (HEAPa : @BnHeapA.AHEAP (push AR f 1) Σ4 OW4 (pbs ++ LB) ma).
    { eapply (@AH_frame (push AR f 1)); [exact HEAP4| exact MUa| exact WMa|].
      constructor; [right; right; exists bt; split; [apply in_or_app; right; apply INX; exact HBT| cbn [fst snd]; clear - TB1 TB2; lia]| constructor]. }
    assert (ACCS : acc ctasegs ma PPC (POLEN + 8 - PPC)).
    { pose proof HEAPa as (HAa & HSa & _). apply (af_acc_stack RT AF Σ4 ma _ _ HAa); [| clear - A4; lia].
      rewrite HSa. cbn [ar_SP0 push amb]. unfold BnHeapA.ACEIL in CEIL. clear - CEIL LOSP SPP VPOS. lia. }
    assert (EPINF : bv_unsigned (Z_to_bv 64 PINF) = PINF) by (apply unsigned_lit; clear - SPP SPR A1 A2 A3 A4N; lia).
    assert (EPCST : bv_unsigned (Z_to_bv 64 PCST) = PCST) by (apply unsigned_lit; clear - SPP SPR A1 A2 A3 A4N; lia).
    assert (EPOLEN : bv_unsigned (Z_to_bv 64 POLEN) = POLEN) by (apply unsigned_lit; clear - SPP SPR A1 A2 A3 A4N; lia).
    (* [comment removed for export] *)
    unfold frozen in HOLEN, HINF, HCST, HPPC0.
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in HOLEN; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply OUT1S; clear - Ha SPP A1 A2 A3; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in HINF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply OUT1S; clear - Ha SPP A1 A2 A3; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in HCST; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply OUT1S; clear - Ha SPP A1 A2 A3; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUc)) in HPPC0; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply OUT1S; clear - Ha SPP A1 A2 A3; lia].
    apply (rw_cells_agree _ _ _ _ _ AXP4) in HOLEN; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW; clear - Ha SPP A1 A2 A3 A4 SPAH; lia].
    apply (rw_cells_agree _ _ _ _ _ AXP4) in HINF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW; clear - Ha SPP A1 A2 A3 A4 SPAH; lia].
    apply (rw_cells_agree _ _ _ _ _ AXP4) in HCST; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW; clear - Ha SPP A1 A2 A3 A4 SPAH; lia].
    apply (rw_cells_agree _ _ _ _ _ AXP4) in HPPC0; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW; clear - Ha SPP A1 A2 A3 A4 SPAH; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HOLEN; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; clear - Ha TLCLO SPAH SPP A1 A2 A3; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HINF; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; clear - Ha TLCLO SPAH SPP A1 A2 A3; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HCST; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; clear - Ha TLCLO SPAH SPP A1 A2 A3; lia].
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUa)) in HPPC0; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; clear - Ha TLCLO SPAH SPP A1 A2 A3; lia].
    try clear HPPC. rename HPPC0 into HPPC. unfold MallocRep.wz in HPPC.
    pose proof (agree_on_of_munch_nw _ _ _ MUa) as AGa. clear MUa WMa ACCT OFF4.
    pose proof (munch_refl [(PINF, PINF + 1); (PCST, PCST + 1); (POLEN, POLEN + 8); (PPC, PPC + 8)]%Z ma) as MUb. pose proof (wmono_refl ctasegs ma) as WMb.
    assert (OFFb : offshW [(PINF, PINF + 1); (PCST, PCST + 1); (POLEN, POLEN + 8); (PPC, PPC + 8)]%Z).
    { cbn [offshW]. unfold SHLO, SHHI. clear - CN CEIL LOSP SPP A1 A2 A3 A4N VPOS. plia. }
    (* [comment removed for export] *)
    step. step.
    step. if_cases KI; zc KI; [exfalso; rewrite ?EPINF in KI; clear - KI SPP A1 SPR; lia|].
    step.
    (* [comment removed for export] *)
    step. if_cases KS; zc KS; [exfalso; rewrite ?EPCST in KS; clear - KS SPP A1 A2 SPR; lia|].
    zstep. step.
    (* [comment removed for export] *)
    step.
    step. if_cases KO; zc KO; [exfalso; rewrite ?EPOLEN in KO; clear - KO SPP A1 A2 A3 SPR; lia|].
    step. step.
    (* [comment removed for export] *)
    step. if_true. step. if_true.
    step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mk end.
    match goal with H : munch _ ma mk |- _ => rename H into MUk end. match goal with H : wmono ctasegs ma mk |- _ => rename H into WMk end.
    match goal with H : stk _ mk _ _ |- _ => rename H into STk end. match goal with H : mem_inv _ mk |- _ => rename H into MIk end.
    rewrite ESPA in STk.
    apply evt_done.
    (* [comment removed for export] *)
    assert (HEAPk0 : @BnHeapA.AHEAP (push AR f 1) Σ4 OW4 (pbs ++ LB) mk).
    { eapply (@AH_frame (push AR f 1)); [exact HEAPa| exact MUk| exact WMk|].
      assert (SIV : forall l h, bv_unsigned sp <= l -> h <= USTACK_TOP -> @aclient_write_ok (push AR f 1) (OW4 ++ (pbs ++ LB)) (l, h)).
      { intros l h Hl Hh. left. cbn [fst snd]. clear - Hl Hh CEIL LOSP SPP VPOS. plia. }
      constructor; [apply SIV; clear - SPP A1 A2 A3 A4; lia|]. constructor; [apply SIV; clear - SPP A1 A2 A3 A4; lia|].
      constructor; [apply SIV; clear - SPP A1 A2 A3 A4; lia|]. constructor; [apply SIV; clear - SPP A1 A2 A3 A4; lia| constructor]. }
    assert (HEAPk : @BnHeapA.AHEAP (push AR f 1) Σ4 OW4 LB mk).
    { subst pbs. unfold actl_pbs in HEAPk0. cbn [app] in HEAPk0.
      do 4 (eapply (@frame_obj_close (push AR f 1)) in HEAPk0; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia]).
      exact HEAPk0. }
    clear HEAPk0.
    apply (rw_cells_cb_first mk spa _ 18) in FRL. cbn [cb_first csize cbytes] in FRL.
    (* [comment removed for export] *)
    intros X2 Φ2 D2 SAFE2 LINK2.
    eapply (actl_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAPk | exact OFFLB | exact STk | exact CEIL | clear - LOSP1 VPOS; lia | exact TOP | clear - SPAL; lia | clear - SPAH; lia
      | exact GSZ | exact SAVJ | exact MIk | exact FRL | exact FRH | reflexivity |].
    intros Σ' m' x11' HEAP' CR' EL' ST' MI' AG'.
    eapply (implAp_elim (ARet (tt, st'))); [| exact SAFE2 | exact LINK2 | exact EL'].
    apply implAp_ret.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (LIBOUT : forall a, lib_addr OW4 a ->
              outside [(TLC, TLC + 32)]%Z a /\ outside [(PINF, PINF + 1); (PCST, PCST + 1); (POLEN, POLEN + 8); (PPC, PPC + 8)]%Z a).
    { intros a HL. cbn [outside fst snd]. destruct HL as [HS|(b & Hb & Hr)].
      - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA.
        clear - HA BT4 TB1 TB2 CN CEIL LOSP SPP A1 A2 A3 VPOS. plia.
      - assert (Hb' : In b (OW4 ++ pbs ++ LB)) by (apply in_or_app; left; exact Hb).
        pose proof (@AH_range_gen (push AR f 1) _ _ _ _ b HEAP4 Hb') as (_ & _ & _ & R4 & _).
        pose proof (@AH_nodup (push AR f 1) _ _ _ _ HEAP4) as ND. destruct b as [[q A] n].
        pose proof (ids_disj OW4 (pbs ++ LB) q A n ND Hb bt ltac:(apply INX; exact HBT)) as NE.
        pose proof (@AH_disjoint_gen (push AR f 1) _ _ _ _ bt (q, A, n) HEAP4 ltac:(apply in_or_app; right; apply INX; exact HBT) Hb' NE) as DJ.
        cbn [blk_addr blk_size fst snd] in Hr, R4, DJ. clear - Hr R4 DJ TB1 TB2 CEIL LOSP SPP A1 A2 A3 VPOS. plia. }
    assert (AGL : agree_on (lib_addr OW4) m4 m').
    { eapply agree_on_trans; [eapply agree_on_mono; [exact AGa|]; intros a Ha; exact (proj1 (LIBOUT a Ha))|].
      eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUk)|]; intros a Ha; exact (proj2 (LIBOUT a Ha))|].
      eapply agree_on_mono; [exact AG'|]. intros a Ha. exact (lib_addr_aclient OW4 LB spa a Ha). }
    (* [comment removed for export] *)
    assert (CST : forall A cs, rw_cells ctasegs mk A cs -> bv_unsigned sp <= A -> A + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells ctasegs m' A cs).
    { intros A cs HC H1 H2. eapply rw_cells_agree; [exact AG'| exact HC|]. intros a Ha. left. clear - Ha H1 H2 SPAH. lia. }
    apply CST in HOLEN; [| clear - SPP A1 A2 A3; lia| cbn; clear - A4; lia]. apply CST in HINF; [| clear - SPP A1 A2 A3; lia| cbn; clear - A1 A2 A3 A4; lia].
    apply CST in HCST; [| clear - SPP A1 A2 A3; lia| cbn; clear - A2 A3 A4; lia]. apply CST in HPPC; [| clear - SPP; lia| cbn; clear - A1 A2 A3 A4; lia].
    apply rw_cells_CB_ofA in HTLC.
    apply (rw_cells_agree _ _ _ _ _ AG') in HTLC; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; right; right; exists bt; split; [apply in_or_app; right; exact HBT| clear - Ha TB1 TB2; lia]].
    unfold check_tlen_postA. cbn [snd].
    do 14 eexists. exists F2, fc2, m', OW4. eexists.
    split; [reflexivity|].
    split.
    { (* [comment removed for export] *)
      pose proof AS4 as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD4)).
      unfold ap_preA. split; [exact HEAP'|]. split; [exact (ap_state_agree _ _ _ _ _ _ AS4 AGL)|]. split; [exact IDS4|].
      split; [exact (data_cells_agree _ _ _ _ DC4 AGL OD4)|]. split; [exact ST'|]. split; [exact CEIL|]. split; [clear - LOSP VPOS; lia|].
      split; [exact TOP|]. split; [exact AL16|]. split; [exact MI'|].
      split; [pose proof (af_credit_nonneg RT AF Σ' m' (AH_art _ _ _ _ HEAP')) as CNN; clear - CNN; lia|].
      clear - FRM. lia. }
    assert (CSB : forall a, client_static a -> a < 12365824).
    { intros a [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. clear - Hin Hlh. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia. }
    (* [comment removed for export] *)
    assert (AXW : forall a, ax_client LB (bv_unsigned sp) ([(POLEN, POLEN + 8); (PINF, PINF + 1); (PCST, PCST + 1); (PPC, PPC + 8); (TLC, TLC + 32)] ++ LIBW_A) a ->
              outside [(spa, spa + 152); (f + 96, f + 104)]%Z a
              /\ ax_client (pbs ++ LB) spa ([(f + 96, f + 96 + 8); (f + 64, f + 64 + 8); (f + 32, f + 32 + 4); (f + 48, f + 48 + 4)] ++ LIBW_A) a
              /\ outside [(TLC, TLC + 32)]%Z a /\ outside [(PINF, PINF + 1); (PCST, PCST + 1); (POLEN, POLEN + 8); (PPC, PPC + 8)]%Z a
              /\ aclient_addr (OW4 ++ LB) spa a /\ aclient_addr (OW ++ LB) (bv_unsigned sp) a).
    { intros a [HX Hc]. unfold LIBW_A in HX. cbn [rin_ivs fst snd app] in HX.
      assert (LOC : (bv_unsigned sp <= a < USTACK_TOP) \/ a < 12365824 \/ (exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b /\ blk_addr b + blk_size b <= ACEIL /\ off_fr f 1 b)).
      { destruct Hc as [H1|[H1|(b & Hb & Hr)]]; [left; exact H1| right; left; exact (CSB a H1)| right; right].
        exists b. split; [exact Hb|]. split; [exact Hr|]. split; [| exact (OFFLB b Hb)].
        pose proof (AH_range_gen _ _ _ _ b HEAP (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & R4 & _). exact R4. }
      assert (ACL : forall L SP, SP <= bv_unsigned sp -> (forall b, In b LB -> In b L) -> aclient_addr L SP a).
      { intros L SP HS HL. destruct Hc as [H1|[H1|(b & Hb & Hr)]]; [left; clear - H1 HS; lia| right; left; exact H1| right; right; exists b; split; [exact (HL b Hb)| exact Hr]]. }
      split.
      { cbn [outside fst snd]. destruct LOC as [L1|[L1|(b & Hb & Hr & R4 & O)]]; [clear - L1 SPAH FLO; lia| clear - L1 G4 CN CEIL LOSP SPAL VPOS; plia|].
        unfold off_fr in O. change (fs_size 1) with 128 in O. clear - Hr R4 O CEIL LOSP SPAL VPOS; plia. }
      split.
      { split; [| apply ACL; [clear - SPAH; lia| exact INX]]. unfold LIBW_A. cbn [rin_ivs fst snd app]. intros HY.
        destruct LOC as [L1|[L1|(b & Hb & Hr & R4 & O)]]; [clear - L1 HY HX SPAH FLO; lia| clear - L1 HY HX G4; lia|].
        unfold off_fr in O. change (fs_size 1) with 128 in O. clear - Hr HY HX O; lia. }
      split; [cbn [outside fst snd]; clear - HX; lia|]. split; [cbn [outside fst snd]; clear - HX; lia|].
      split; [apply ACL; [clear - SPAH; lia| intros b Hb; apply in_or_app; right; exact Hb]|].
      apply ACL; [clear; lia| intros b Hb; apply in_or_app; right; exact Hb]. }
    split.
    { (* [comment removed for export] *)
      unfold ax_pres.
      eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a Ha; exact (proj2 (proj2 (proj2 (proj2 (proj2 (AXW a Ha))))))|].
      eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUc)|]; intros a Ha; exact (proj1 (AXW a Ha))|].
      eapply agree_on_trans; [eapply agree_on_mono; [exact AXP4|]; intros a Ha; exact (proj1 (proj2 (AXW a Ha)))|].
      eapply agree_on_trans; [eapply agree_on_mono; [exact AGa|]; intros a Ha; exact (proj1 (proj2 (proj2 (AXW a Ha))))|].
      eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUk)|]; intros a Ha; exact (proj1 (proj2 (proj2 (proj2 (AXW a Ha)))))|].
      eapply agree_on_mono; [exact AG'|]. intros a Ha; exact (proj1 (proj2 (proj2 (proj2 (proj2 (AXW a Ha)))))). }
    split.
    { (* [comment removed for export] *)
      unfold go_costA in CRED4. rewrite EG in CRED4. cbn [ar_RT push amb] in CRED4, CR'. unfold CHECK_TLEN_SPENT_A. clear - CR1 CRED4 CR'. lia. }
    split.
    { (* [comment removed for export] *)
      destruct KEPT4 as (K1 & K2 & K3). split; [exact K1|]. split; [exact K2|].
      intros a Ha Hin.
      assert (HL4 : lib_addr OW4 a) by (right; eapply in_block_mono; [exact K1| exact Hin]).
      assert (HL : lib_addr OW a) by (right; eapply in_block_mono; [exact KOW| exact Hin]).
      rewrite (AGL a Ha HL4), (K3 a Ha Hin), (AGLc a Ha HL). exact (AGF a Ha (lib_addr_aclient OW LB (bv_unsigned sp) a HL)). }
    split; [exact HOLEN|]. split; [exact HINF|]. split; [exact HCST|]. split; [exact HPPC| exact HTLC].
  Qed.
End Proofs.
End WithRT.
