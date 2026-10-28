(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel ApBase ApState ApLogic ApInv ApErr ApParse ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA W_cryptoA UnwindA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface W_get_objectA W_check_tlenA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColP Require W_check_tlen_gen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA CtlStmtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).

(* [comment removed for export] *)
Definition ctl_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (m : mem) (K : list block) (cost : Z)
    (PIC PPC : Z) (TLCo : option Z) (rv : Z) (cells_pic : list cell) (pp : Z)
    (st' : ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' bo',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' st' m' OW' LB E bo' sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp)
               ([(PIC, PIC + 10); (PPC, PPC + 8); (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - cost <= rt_credit RT Σ'
    /\ blocks_kept K st' OW' m m'
    /\ rw_cells ctasegs m' PIC cells_pic /\ rw_cells ctasegs m' PPC [C8 (wz pp)]
    /\ match TLCo with Some a => exists vb j, rw_cells ctasegs m' a [C1 vb; CB 31 j] | None => True end.
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition check_tlen_cpsA : Prop :=
  forall (X : Type) (ot : option Z) (KE KW KS : @AM bptr X) (Q : X * ap_st bptr -> rts RT -> machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (K : list block) (ras : list Z)
    (D : Z) (d : list Z) (op len PIC PPC : Z) (TLCo : option Z) (bi bc : bv 8) (jl j31 : list (bv 8)),
  let g := get_object d op len in
  ap_preA Σ st m OW LB E bo sp lo CHECK_TLEN_STACK_A CHECK_TLEN_GEN_COST_A CHECK_TLEN_FRAMES_A -> tp = wz TP_A ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CHECK_TLEN_A (bv_unsigned ra :: ras) -> ras <> nil ->
  (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
  payload_okA m LB D d -> 0 <= op -> 0 < len -> op + len <= zlength d ->
  match ot with Some t => 0 <= t < 2 ^ 31 | None => True end ->
  bv_unsigned sp <= PIC -> PIC + 10 <= USTACK_TOP -> bv_unsigned sp <= PPC -> PPC + 8 <= USTACK_TOP ->
  (PPC + 8 <= PIC \/ PIC + 10 <= PPC) -> (PIC + 2) mod 8 = 0 -> PPC mod 8 = 0 ->
  match TLCo with Some a => cellA_in LB a 32 /\ a mod 8 = 0 /\ rw_cells ctasegs m a (tlc_in j31) | None => True end ->
  rw_cells ctasegs m PIC [C1 bi; C1 bc; CB 8 jl] -> rw_cells ctasegs m PPC [C8 (wz (D + op))] ->
  (forall e st' Σ' ms' bi' bc' jl',
     go_err g = Some e ->
     ctl_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (ctl_costA g ot) PIC PPC TLCo 0 [C1 bi'; C1 bc'; CB 8 jl'] (D + op) st' Σ' ms' ->
     implAp (KE st') Σ' Q ms') ->
  (forall t st' Σ' ms' bi' bc' jl',
     ot = Some t -> go_err g = None -> (go_tag g <> t \/ go_cls g <> 0) ->
     ctl_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (ctl_costA g ot) PIC PPC TLCo 0 [C1 bi'; C1 bc'; CB 8 jl'] (D + op) st' Σ' ms' ->
     implAp (KW st') Σ' Q ms') ->
  (forall st' Σ' ms',
     go_err g = None -> match ot with Some t => go_tag g = t /\ go_cls g = 0 | None => True end ->
     ctl_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (ctl_costA g ot) PIC PPC TLCo 1
               [C1 (Z_to_bv 8 (Z.land (go_ret g) 1)); C1 (Z_to_bv 8 (Z.land (go_ret g) 32)); C8 (wz (tlen_plen g op len))] (D + go_p g) st' Σ' ms' ->
     implAp (KS st') Σ' Q ms') ->
  implAp (tlen_tree g ot KE KW KS st) Σ Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (PIC + 2)) (wz 0) (wz 0) (wz PIC) (wz (PIC + 1)) (wz PPC) (wz len) (wz match ot with Some t => t | None => -1 end)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 0) (wz 0) (wz match TLCo with Some a => a | None => 0 end) t6)
             F (wz CHECK_TLEN_A) fc None m (seg_rom ctasegs)).

(* [comment removed for export] *)
Lemma ctl_costA_range : forall g ot, 1 <= ctl_costA g ot <= CHECK_TLEN_GEN_COST_A.
Proof.
  intros g ot. pose proof col_consts as (_ & _ & KC3 & _ & _ & KC6 & _). unfold ctl_costA, go_costA. rewrite KC6, KC3.
  destruct (go_err g); [clear; lia|]. destruct ot as [t|]; [| clear; lia]. destruct (negb (go_tag g =? t) || negb (go_cls g =? 0)); clear; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem check_tlen_gen_of_cpsA : check_tlen_cpsA -> check_tlen_gen_specA.
Proof.
  intros HALL. unfold check_tlen_gen_specA. intros sp m Σ LB E lo K c D XP OFS STK CST FRM KH D1 D63 D26.
  unfold check_tlen_gen_actA.
  intros X ot KE KW KS Q ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 FX fcX ΣX stX mX OWX boX NEW CX ras op len PIC PPC TLCo bi bc jl j31.
  cbv zeta. intros STKG FRMG OI CXG UW CTX NE OP0 LEN0 OPL OT PIClo PIChi PPClo PPChi DJ AL2 AL8 HTLC HPIC HPPC KE_ KW_ KS_.
  pose proof KH as (DF & CEIL & LO0 & LO & STK0 & OFS0 & TOP & SP16 & OFS16 & XPok & XPD & PBX & D0).
  pose proof (SPR sp LB lo c D XP OFS STK KH) as SPR. pose proof (ESP sp LB lo c D XP OFS STK KH) as ESP.
  pose proof OI as (PREX & AX & KO & KI & KP & HB & CR & LBOK).
  pose proof PREX as (HEAPX & _ & _ & _ & STX & _ & LOSP & TOPX & _ & _ & CRED & FRM').
  rewrite ?ESP in STX, LOSP, TOPX.
  pose proof (ctl_costA_range (get_object c op len) ot) as CRG.
  assert (PAY : payload_okA mX (NEW ++ LB) D c).
  { split; [exact HB|]. split; [exact DF|]. split; [exact D1|]. split; [exact D63|]. split; [exact D26|].
    destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)]; [left; exact E0| right].
    exists (pb, PA, psz). split; [apply in_app_iff; right; exact HPB| cbn [blk_addr blk_size fst snd]; split; [exact PB1| exact PB2]]. }
  assert (HTLC' : match TLCo with Some a => cellA_in (NEW ++ LB) a 32 /\ a mod 8 = 0 /\ rw_cells ctasegs mX a (tlc_in j31) | None => True end).
  { destruct TLCo as [a|]; [| exact I]. destruct HTLC as (XIN & ALa & Ha). split; [| split; [exact ALa| exact Ha]].
    pose proof (proj1 (Forall_forall _ _) XPok _ XIN) as (bt & Hbt & T1 & T2). cbn [fst snd] in T1, T2.
    exists bt. split; [apply in_app_iff; right; exact Hbt| split; [exact T1| exact T2]]. }
  (* [comment removed for export] *)
  assert (HXX : forall a, rin_ivs [(PIC, PIC + 10); (PPC, PPC + 8); (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)] a ->
                (bv_unsigned sp + OFS <= a < bv_unsigned sp) \/ rin_ivs XP a \/ (exists b, In b NEW /\ blk_addr b <= a < blk_addr b + blk_size b)).
  { intros a Ha. cbn [rin_ivs fst snd] in Ha. destruct Ha as [Ha|[Ha|[Ha|[]]]]; [left; clear - Ha PIClo PIChi; lia| left; clear - Ha PPClo PPChi; lia|].
    destruct TLCo as [a0|]; [| exfalso; clear - Ha; lia]. right; left. destruct HTLC as (XIN & _).
    clear - XIN Ha. induction XP as [|iv XP IH]; [destruct XIN|]. cbn [rin_ivs]. destruct XIN as [->|XIN]; [left; cbn [fst snd]; exact Ha| right; exact (IH XIN)]. }
  (* [comment removed for export] *)
  assert (BACK : forall rv cells_pic pp st' Σ' ms',
    ctl_postA ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ΣX OWX (NEW ++ LB) E lo mX K (ctl_costA (get_object c op len) ot) PIC PPC TLCo rv cells_pic pp st' Σ' ms' ->
    tlen_postA sp m Σ LB E lo K c D XP OFS STK CST FRM ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mX NEW PIC PPC TLCo rv cells_pic pp (CX - ctl_costA (get_object c op len) ot) st' Σ' ms').
  { intros rv cells_pic pp st' Σ' ms' PO. unfold ctl_postA in PO.
    destruct PO as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & OW2 & bo2 & -> & PRE2 & AXP2 & CRED2 & KEPT2 & HPIC2 & HPPC2 & HTLC2).
    rewrite ESP in AXP2. unfold tlen_postA.
    exists y0, y1, y2, z1, z2, z3, z4, z5, z6, z7, y3, y4, y5, y6, F2, fc2, m2, OW2, bo2.
    split; [reflexivity|].
    split. { change NEW with ([] ++ NEW). eapply (oinv_after sp m Σ LB E lo K c D XP OFS STK CST FRM KH); [exact OI| cbn [app]; exact PRE2| exact AXP2| exact HXX| exact CRED2| clear - CRG CXG; lia| exact KEPT2| constructor]. }
    split; [exact AXP2|]. split; [exact HPIC2|]. split; [exact HPPC2| exact HTLC2]. }
  unfold check_tlen_cpsA in HALL.
  eapply (HALL X ot KE KW KS Q ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz TP_A) t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 FX fcX
                mX ΣX stX OWX (NEW ++ LB) E boX lo K ras D c op len PIC PPC TLCo bi bc jl j31);
    [ eapply ap_preA_weaken; [exact PREX| exact STKG| clear - CXG CRED; pose proof col_consts as (_ & _ & _ & _ & _ & KC6 & _); lia| clear - FRMG FRM'; pose proof col_consts as (_ & _ & _ & KC4 & _); lia]
    | reflexivity| rewrite ESP; exact UW| exact CTX| exact NE| exact KO| exact KI| exact PAY| exact OP0| exact LEN0| exact OPL| exact OT
    | rewrite ESP; exact PIClo| clear - PIChi TOP; unfold USTACK_TOP in *; lia| rewrite ESP; exact PPClo| clear - PPChi TOP; unfold USTACK_TOP in *; lia
    | exact DJ| exact AL2| exact AL8| exact HTLC'| exact HPIC| exact HPPC| | | ].
  - intros e st' Σ' ms' bi' bc' jl' EG PO. eapply (KE_ e st' Σ' ms' bi' bc' jl' (CX - ctl_costA (get_object c op len) ot)); [exact EG| clear; lia| exact (BACK _ _ _ _ _ _ PO)].
  - intros t st' Σ' ms' bi' bc' jl' ET EG WR PO. eapply (KW_ t st' Σ' ms' bi' bc' jl' (CX - ctl_costA (get_object c op len) ot)); [exact ET| exact EG| exact WR| clear; lia| exact (BACK _ _ _ _ _ _ PO)].
  - intros st' Σ' ms' EG OK PO. eapply (KS_ st' Σ' ms' (CX - ctl_costA (get_object c op len) ot)); [exact EG| exact OK| clear; lia| exact (BACK _ _ _ _ _ _ PO)].
Qed.

End WithRT.
