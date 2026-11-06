(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ALogic16 ARtStmts ARtSscs AMTac AMallocI ARallocI ARallocE ARt22fz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt20wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalmys AMaly5g ASecB1 AFreeB1 AFreeB3 AFreeB5 AFreeT AFreeH AFreeH0 ATransp AIaShell ACor4x6 ACoresk AWrapKit AWrapS AWrapF.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARallocE OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt22fz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx.ARt27j4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIaShell OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AWrapKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AWrapS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AWrapF.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rshell1_W (ia0 : bool) (fp : Z) : list (Z * Z) := [(fp - 2192, fp)] ++ ia_Wk ia0.

Section Shell1R.
Context {Clg : Ceiling}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo p : Z) (ia0 : bool).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 2192.
  Hypothesis CINI : ro_cells rsegs m 0xb5898 [C1 (Z_to_bv 8 1)].
  Hypothesis Cgps : ro_cells rsegs m 0xa8b50 [C8 (wz 0x144660)].
  Hypothesis Cps : ro_cells rsegs m 0x144660 [C8 (wz 4096)].
  Hypothesis IA : ia_pre ia0 m.

  #[warnings="-notation-for-abbreviation"] Local Notation fp := (bv_unsigned sp).

  #[using="IA Cps Cgps CINI LO ST MI Clg"] Lemma realloc_shell1 : forall (Q : machine_state -> Prop),
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk pad1 pad2 : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (fp + -2144) [CB 8 pad2] ->
        rw_cells rsegs m' (fp + -2136) [CB 2064 junk] ->
        rw_cells rsegs m' (fp + -72) [CB 8 pad1] ->
        rw_cells rsegs m' (fp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        ia_post ia0 m' ->
        munch (rshell1_W ia0 fp) m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (fp - 2144) ->
        evt rsegs Q (MS (mkR (wz 0x58ed0) (wz (fp + -2144)) gp tp t0' t1' t2' sp a1 (wz 0xb5dc0) a1' a2' a3' a4' a5' a6' a7'
                            (wz p) ra s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc (wz 0x58ed0)) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x58858) fc None m (seg_rom rsegs)).
  Proof.
    intros Q K.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    amz.
    (* [comment removed for export] *)
    eapply (realloc_pro_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo); [exact MI| exact ST| lia| lia| exact CINI|].
    intros a1' junk pad1 pad2 m1 P2 OBJ P1 SAV MU1 WM1 MI1 ST1.
    rewrite ?unsigned_lit in P2, OBJ, P1, SAV, MU1, ST1 by lia.
    xfer Cgps MU1 WM1. xfer Cps MU1 WM1.
    assert (IA1 : ia_pre ia0 m1).
    { destruct ia0; cbn [ia_pre] in IA |- *.
      - xfer IA MU1 WM1. exact IA.
      - destruct IA as (I1 & I2 & I3 & I4 & I5 & I6). unfold ia_pre0, IAB in *.
        xfer I1 MU1 WM1. xfer I2 MU1 WM1. xferb I3 MU1 WM1. xferb I4 MU1 WM1. xferb I5 MU1 WM1. xferb I6 MU1 WM1.
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }
    clear IA MI ST.
    (* [comment removed for export] *)
    unfold ARallocI.ia_entry.
    destruct ia0; cbn [ia_pre ia_post ia_Wk] in IA1 |- *.
    - eapply evt_cut; [eapply (ia_fast_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo)|];
        [exact MI1| rewrite unsigned_lit by lia; exact ST1| rewrite unsigned_lit by lia; lia| lia| exact IA1| reflexivity|].
      intros ms' PO. destruct_exs PO. (first [ dand5 PO as E MUc WMc MI2 ST2 | destruct PO as (E & MUc & WMc & MI2 & ST2) ]). subst ms'. rewrite ?unsigned_lit in MUc, ST2 by lia.
      xferb P2 MUc WMc. xferb OBJ MUc WMc. xferb P1 MUc WMc. xfer SAV MUc WMc.
      eapply K; [exact P2| exact OBJ| exact P1| exact SAV| exact I| | exact (wmono_trans _ _ _ _ WM1 WMc)| exact MI2| exact ST2].
      unfold rshell1_W. cbn [ia_Wk app]. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUc]];
        unfold sub_fp; cbn [outside]; intros y Hy; lia.
    - (first [ dand6 IA1 as I1 I2 I3 I4 I5 I6 | destruct IA1 as (I1 & I2 & I3 & I4 & I5 & I6) ]). unfold IAB in *.
      eapply evt_cut; [eapply (ia_init_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 0 lo
                                 (Z_to_bv 8 0) (repeat (Z_to_bv 8 0) (Z.to_nat 262144)) (repeat (Z_to_bv 8 0) (Z.to_nat 262728)) (repeat (Z_to_bv 8 0) 40) (repeat (wz 0) 432))|];
        [exact MI1| rewrite unsigned_lit by lia; exact ST1| rewrite unsigned_lit by lia; lia| lia| lia| exact I1| exact Cgps| exact Cps
        | exact I2| exact I3| exact I4| apply repeat_length| exact I5| exact I6| reflexivity|].
      intros ms' PO. destruct_exs PO. (first [ dand11 PO as E MUc WMc MI2 ST2 Q1 Q2 Q3 Q4 Q5 Q6 | destruct PO as (E & MUc & WMc & MI2 & ST2 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6) ]). subst ms'.
      rewrite ?unsigned_lit in MUc, ST2 by lia. unfold IAB in *.
      xferb P2 MUc WMc. xferb OBJ MUc WMc. xferb P1 MUc WMc. xfer SAV MUc WMc.
      eapply K; [exact P2| exact OBJ| exact P1| exact SAV| | | exact (wmono_trans _ _ _ _ WM1 WMc)| exact MI2| exact ST2].
      + cbn [ia_post]. unfold ia_post0, IAB. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; kcell.
      + unfold rshell1_W, ia_W, IAB. cbn [ia_Wk app]. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUc]];
          unfold sub_fp, ia_W, IAB; cbn [outside app]; intros y Hy; lia.
  Qed.
End Shell1R.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Facts.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Let v := aview_of (pa_hull A) m.

  (* [comment removed for export] *)
  #[using="AI md"] Lemma realloc_stats : exists rc rd : word, rw_cells rsegs v (p_thr (a_pl A) + 2856) [C8 rc; C8 rd].
  Proof.
    pose proof (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as C. unfold cache_repr_ in C. cbv zeta in C. (first [ dand5 C as _ _ J2 TM _ | destruct C as (_ & _ & J2 & TM & _) ]).
    unfold off_th_stats in J2. (first [ dex1 J2 as b2; destruct J2 as [L2 B2] | dand3 J2 as b2 L2 B2 | destruct J2 as (b2 & L2 & B2) ]).
    assert (X : bytes_at rsegs v (p_thr (a_pl A) + 2856) (u64s (words8 (firstn 16 (skipn 56 b2)) 2))).
    { rewrite u64s_words8 by (rewrite firstn_length, skipn_length; lia).
      replace (p_thr (a_pl A) + 2856) with (p_thr (a_pl A) + 2800 + Z.of_nat 56) by lia. apply bytes_at_mid; [exact B2| lia]. }
    cbn [words8] in X. eexists _, _. apply ro_rw.
    - split; [exact (conj I (conj I I))|]. cbn [cells_bytes cbytes]. exact X.
    - cbn [cells_size csize Nat.add]. intros i Hi. replace (p_thr (a_pl A) + 2856 + i) with (p_thr (a_pl A) + (2856 + i)) by lia. apply TM. lia.
  Qed.
End Facts.

(* [comment removed for export] *)
Section FrameSeq.
Context {Clg : Ceiling}.
  Variables (O O' O'' VIC NB : Z -> Prop) (hi win : Z) (v v1 v' v2 v'' : mem).
  Let window (a : Z) : Prop := hi - win <= a < hi.
  Let errno (a : Z) : Prop := cl_errno LPA <= a < cl_errno LPA + 4.
  Let notimg (a : Z) : Prop := a + 1 <= 0x10000 \/ 0x60a000 <= a.
  Hypothesis CA : frame_ok LPA O O' hi win nowhere NB v1 v'.
  Hypothesis CD : frame_ok LPA O' O'' hi win VIC nowhere v2 v''.
  (* [comment removed for export] *)
  Hypothesis P1 : forall a, 0 <= a < 2^64 -> ~ window a -> ~ O a -> v1 (wz a) = v (wz a).
  Hypothesis P2 : forall a, notimg a -> 0 <= a < 2^64 -> v (wz a) <> None -> v1 (wz a) <> None.
  (* [comment removed for export] *)
  Hypothesis M1 : forall a, 0 <= a < 2^64 -> ~ NB a -> v2 (wz a) = v' (wz a).
  Hypothesis M2 : forall a, 0 <= a < 2^64 -> v' (wz a) <> None -> v2 (wz a) <> None.
  Hypothesis M3 : forall a, 0 <= a < 2^64 -> v2 (wz a) <> None -> v' (wz a) <> None.
  Hypothesis E3 : mapped v'' (hi - win) win.
  Hypothesis OW : forall a, O a -> ~ window a /\ ~ errno a.

  #[using="OW E3 M2 M1 P2 P1 CD CA notimg errno window v2 v' v1 O'"] Lemma frame_ok_seq : frame_ok LPA O O'' hi win VIC NB v v''.
  Proof.
    destruct CA as (A1 & A2 & A3 & A4 & A5 & A6 & A7). destruct CD as (D1 & D2 & D3 & D4 & D5 & D6 & D7). unfold frame_ok.
    assert (HZN : forall a, heap_zone LPA a -> notimg a).
    { intros a [_ NI]. unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI. unfold notimg. lia. }
    (* [comment removed for export] *)
    assert (MID : forall a, 0 <= a < 2^64 -> O' a -> ~ O a -> ~ O'' a -> v (wz a) = None /\ v'' (wz a) = None).
    { intros a Ha Ho' No No''. destruct (A5 a Ha Ho') as [Ho|[[]|[N HZ]]]; [exfalso; exact (No Ho)|].
      split.
      - destruct (v (wz a)) eqn:E; [|reflexivity]. exfalso. apply (P2 a (HZN a HZ) Ha); [rewrite E; discriminate| exact N].
      - destruct (D6 a Ha Ho' No'') as [[]|X]. exact X. }
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - intros a Ha NO NO'' NW NE NV NN. destruct (classic (O' a)) as [Ho'|No'].
      + destruct (MID a Ha Ho' NO NO'') as [-> ->]. reflexivity.
      + rewrite (D1 a Ha No' NO'' NW NE NV ltac:(intros [])). rewrite (M1 a Ha NN). rewrite (A1 a Ha NO No' NW NE ltac:(intros []) NN). exact (P1 a Ha NW NO).
    - intros a Ha NI Hv. unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI.
      pose proof (P2 a ltac:(unfold notimg; lia) Ha Hv) as Hv1.
      destruct (A2 a Ha ltac:(unfold in_image; cbn [cl_image_lo cl_image_hi LPA]; exact NI) Hv1) as [Ho|[[]|Pv']]; [left; exact Ho|].
      destruct (D2 a Ha ltac:(unfold in_image; cbn [cl_image_lo cl_image_hi LPA]; exact NI) (M2 a Ha Pv')) as [Ho'|[Vv|Pv'']]; [| right; left; exact Vv| right; right; exact Pv''].
      destruct (A5 a Ha Ho') as [Ho|[[]|[N _]]]; [left; exact Ho|]. exfalso. exact (Hv1 N).
    - exact E3.
    - intros a Ha HNB. destruct (A4 a Ha HNB) as [Ho|[[]|[N HZ]]]; [left; exact Ho| right; right].
      split; [|exact HZ]. destruct (v (wz a)) eqn:E; [|reflexivity]. exfalso. apply (P2 a (HZN a HZ) Ha); [rewrite E; discriminate| exact N].
    - intros a Ha Ho''. destruct (D5 a Ha Ho'') as [Ho'|[Vv|[N HZ]]]; [| right; left; exact Vv|].
      + destruct (A5 a Ha Ho') as [Ho|[[]|[N HZ]]]; [left; exact Ho| right; right].
        split; [|exact HZ]. destruct (v (wz a)) eqn:E; [|reflexivity]. exfalso. apply (P2 a (HZN a HZ) Ha); [rewrite E; discriminate| exact N].
      + destruct (classic (O a)) as [Ho|No]; [left; exact Ho| right; right]. split; [|exact HZ].
        destruct (v (wz a)) eqn:E; [|reflexivity]. exfalso.
        pose proof (P2 a (HZN a HZ) Ha ltac:(rewrite E; discriminate)) as Hv1.
        destruct (A2 a Ha (proj2 HZ) Hv1) as [Ho|[[]|Pv']]; [exact (No Ho)|]. exact (M2 a Ha Pv' N).
    - intros a Ha Ho No''. destruct (classic (O' a)) as [Ho'|No'].
      + destruct (D6 a Ha Ho' No'') as [[]|X]. right. exact X.
      + destruct (A6 a Ha Ho No') as [HNB|N]; [left; exact HNB|].
        destruct (classic (NB a)) as [HNB|NNB]; [left; exact HNB| right].
        destruct (classic (VIC a)) as [Vv|Nv].
        * destruct (D7 a Ha Vv) as [Ho''|[[]|X]]; [exfalso; exact (No'' Ho'')| exact X].
        * destruct (OW a Ho) as [NW NE]. rewrite (D1 a Ha No' No'' NW NE Nv ltac:(intros [])). rewrite (M1 a Ha NNB). exact N.
    - intros a Ha Vv. destruct (D7 a Ha Vv) as [Ho''|[[]|X]]; [left; exact Ho''| right; right; exact X].
  Qed.
End FrameSeq.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WrapR.
Context {Clg : Ceiling}.
  Hypothesis UNW : unwind_stmt.
  Hypothesis TSS : thread_stats_stmt.
  (* [comment removed for export] *)
  Hypothesis ACORE : alloc_core_cps1.
  Hypothesis DCORE : dealloc_core_cps.

  #[using="DCORE ACORE TSS UNW"] Theorem pa_realloc16_of_core : @pa_realloc_obligation16 _ DepotRepL.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n old T.
    cbv zeta. intros AI MI Ha0 Ha1 NRQ NCAP PNZ HL LIM NLV TINY SCRED PCRED TPE SPA RA4 SITE S0C CEIL SM KK.   (* [comment removed for export] *)
    cbn [cl_segs cl_realloc_pc LPA] in MI |- *.
    pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0.
    pose proof (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A (aview_of (pa_hull A) m)) as AR.
    pose proof (hit_stk A m sp CEIL SM) as ST. pose proof (hit_sp47 A m md sp AI CEIL SM) as SPH. unfold ASTK in *.
    pose proof alloc_ceiling_val as CE. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
    pose proof (hit_INI A m md AI) as CINI.
    pose proof (hit_PCo A m md AI) as PCo. unfold poison_consts in PCo.
    (first [ dand13 PCo as _ Cflags _ _ _ _ _ _ _ _ _ Cgps Cps | destruct PCo as (_ & Cflags & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cgps & Cps) ]).
    subst a0 a1 tp. unfold REQ_MAX in NRQ.
    assert (LO : alloc_ceiling <= bv_unsigned sp - 8192 /\ bv_unsigned sp - 8192 <= bv_unsigned sp - 2192) by lia.
    pose proof (proj1 (Forall_forall _ _) pa_sites_range _ SITE) as RAr. cbv beta in RAr. assert (RA0 : 4096 <= bv_unsigned ra) by lia.
    assert (RANE : bv_unsigned ra <> 0x58fc8) by (intros E; apply (pa_pcs_not_sites 0x58fc8 ltac:(cbn; clear; tauto)); rewrite <- E; exact SITE).
    assert (VLE : bv_unsigned s0 <= bv_unsigned sp) by lia.
    assert (TPL : bv_unsigned (cl_tp LPA) = 0x5e7bd8) by (cbn [cl_tp LPA]; rewrite unsigned_lit by lia; reflexivity).
    destruct (asI_minv A m md AI) as [HMI HH].
    (* [comment removed for export] *)
    (first [ pose proof ((free_geom A m md p old AI HL)) as dR_7; dand4 dR_7 as PAL PLO PCE PHI | destruct (free_geom A m md p old AI HL) as (PAL & PLO & PCE & PHI) ]). destruct (free_n0 A m md p old AI HL) as [OR _]. unfold REQ_MAX in OR.
    pose proof (aobj_facts _ _ PLO) as PF. pose proof (Z_div_mod_eq_full (old + 7) 8) as NDE. pose proof (Z.mod_pos_bound (old + 7) 8 ltac:(lia)) as ER.
    assert (P0 : 16 <= p) by (clear -PF; lia).
    pose proof (ia_pre_of A _ AR) as IAX.
    set (fp := bv_unsigned sp) in *. set (thr := p_thr (a_pl A)) in *. set (v := aview_of (pa_hull A) m) in *.
    set (top := p_stk_top (a_pl A)) in *. set (bot := p_stk_bot (a_pl A)) in *.
    (* [comment removed for export] *)
    pose (Q1 := fun ms' : machine_state => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk pad1 pad2 : list byte) (m1 : mem),
        ms' = MS (mkR (wz 0x58ed0) (wz (fp + -2144)) gp (cl_tp LPA) t0' t1' t2' sp (wz n) (wz 0xb5dc0) a1' a2' a3' a4' a5' a6' a7'
                     (wz p) ra s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc (wz 0x58ed0)) fc None m1 (seg_rom rsegs)
        /\ rw_cells rsegs m1 (fp + -2144) [CB 8 pad2]
        /\ rw_cells rsegs m1 (fp + -2136) [CB 2064 junk]
        /\ rw_cells rsegs m1 (fp + -72) [CB 8 pad1]
        /\ rw_cells rsegs m1 (fp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ ia_post (a_ia_inited A) m1
        /\ munch (rshell1_W (a_ia_inited A) fp) v m1 /\ wmono rsegs v m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 (fp - 8192) (fp - 2144)).
    eapply (srz_evt_restrict rsegs (pa_hull A) (asI_hull_segs A m md AI) pa_wx _ (pa_eager A) Q1 _ md T HMI HH).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A)) m) with v.
      eapply (realloc_shell1 ra sp gp (cl_tp LPA) t0 t1 t2 s0 s1 (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc v
                (fp - 8192) p (a_ia_inited A) MI ST LO CINI Cgps Cps IAX).
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk pad1 pad2 m1 P2 OBJ P1 SAV IAP1 MU1 WM1 MI1 ST1.
      apply evt_done. unfold Q1. first [ hotw_ex18 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk pad1 pad2 m1 | exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', junk, pad1, pad2, m1 ].
      split; [reflexivity|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }
    intros msr1 md1 HQ1 HI1 SB1 CL1.
    (first [ dex18 HQ1 as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk pad1 pad2 m1; dand10 HQ1 as -> P2 OBJ P1 SAV IAP1 MU1 WM1 MI1 ST1 | dand28 HQ1 as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk pad1 pad2 m1 -> P2 OBJ P1 SAV IAP1 MU1 WM1 MI1 ST1 | destruct HQ1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & pad1 & pad2 & m1 & -> & P2 & OBJ & P1 & SAV & IAP1 & MU1 & WM1 & MI1 & ST1) ]).
    rewrite unrestrict_MS. cbn [ms_mem] in CL1.
    lazymatch goal with |- context [munrestrict ?Hh (ms_mem (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro)) ?v2] => change (ms_mem (MS R FF pc fcx rv mm ro)) with mm end.
    (* [comment removed for export] *)
    assert (AGc : forall a, 0 <= a < 2^64 -> ~ (fp - ASTK <= a < fp) -> a <> thr + 3168 -> ~ ia_blk a -> m1 (wz a) = v (wz a)).
    { intros a Ha NW NT NI. unfold ASTK in NW. apply MU1. rewrite unsigned_lit by lia. unfold rshell1_W, ia_blk in *.
      rewrite outside_app. split.
      - cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; apply NW; clear -X; lia.
      - destruct (a_ia_inited A); cbn [ia_Wk ia_W outside]; [exact I|]. unfold IAB. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; apply NI; clear -X; lia. }
    assert (TUNW1 : rw_cells rsegs m1 (thr + 3168) [C1 (Z_to_bv 8 0)]).
    { pose proof (hit_TUNW A m md AI) as TU. fold v thr in TU. unfold off_th_unwinding in TU.
      pose proof (hit_place A m md AI) as (TH1 & _). pose proof (aobj_facts _ _ TH1) as THF.
      apply (rw_cells_agree v m1 _ _ TU). intros i Hi. cbn in Hi. apply MU1. rewrite unsigned_lit by (clear -THF Hi CE; lia). unfold rshell1_W.
      rewrite outside_app. split.
      - cbn [outside]. clear -THF Hi CE CEIL. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
      - destruct (a_ia_inited A); cbn [ia_Wk ia_W outside]; [exact I|]. unfold IAB. clear -THF Hi. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    assert (AI1 : @pa_ainv _ DepotRepL (set_ia A true) (munrestrict (hidc (pa_hull A)) m m1) md1).
    { destruct (a_ia_inited A) eqn:EIA.
      - rewrite (set_ia_same A true EIA).
        apply (shell_ainv A m md md1 fp m1 nowhere AI CEIL SM); [| intros a []| exact TUNW1| exact WM1| exact CL1| exact HI1| exact SB1].
        intros a Ha NW NT NE _. unfold ASTK in NW. apply MU1. rewrite unsigned_lit by lia. unfold rshell1_W. cbn [ia_Wk app outside].
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; apply NW; clear -X; lia.
      - cbn [ia_post] in IAP1. exact (ia_shell_ainv A m md md1 fp m1 AI CEIL AGc TUNW1 IAP1 WM1 CL1 HI1 SB1). }
    pose proof (shell_view A m m1 CL1) as VIEW1. fold v in VIEW1.
    set (m1r := munrestrict (hidc (pa_hull A)) m m1) in *. set (A1 := set_ia A true) in *.
    assert (HL1 : as_live A1 p = Some old) by exact HL.
    assert (VIEW1' : aview_of (pa_hull A1) m1r = m1) by exact VIEW1.
    (* [comment removed for export] *)
    destruct (asI_minv A1 m1r md1 AI1) as [HMI1 HH1].
    (first [ pose proof ((hit_place A1 m1r md1 AI1)) as dR_9; dand7 dR_9 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A1 m1r md1 AI1) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]). change (p_thr (a_pl A1)) with thr in TH1, TH2, THRA.
    pose proof (aobj_facts _ _ TH1) as THF.
    (first [ pose proof ((hit_sep A1 m1r md1 AI1)) as dR_10; dand4 dR_10 as _ _ SEP_tc _ | pose proof (hit_sep A1 m1r md1 AI1) as (_ & _ & SEP_tc & _) ]). change (p_thr (a_pl A1)) with thr in SEP_tc. unfold AMallocA.apart in SEP_tc.
    pose proof (hit_TC A1 m1r md1 AI1) as TC1. rewrite VIEW1' in TC1. change (p_thr (a_pl A1)) with thr in TC1.
    pose proof (hit_INI A1 m1r md1 AI1) as CINI1. pose proof (hit_CMCS A1 m1r md1 AI1) as CMCS1. pose proof (hit_CFU A1 m1r md1 AI1) as CFU1.
    pose proof (hit_TTB A1 m1r md1 AI1) as TTB1. pose proof (hit_TDT A1 m1r md1 AI1) as TDT1. pose proof (hit_TUNW A1 m1r md1 AI1) as TUNWx.
    pose proof (hit_PCo A1 m1r md1 AI1) as PCo1. unfold poison_consts in PCo1. (first [ dand13 PCo1 as _ Cflags1 _ _ _ _ _ _ _ _ _ Cgps1 Cps1 | destruct PCo1 as (_ & Cflags1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cgps1 & Cps1) ]).
    rewrite VIEW1' in CINI1, CMCS1, CFU1, TTB1, TDT1, TUNWx, Cflags1, Cgps1, Cps1.
    change (p_thr (a_pl A1)) with thr in TTB1, TDT1, TUNWx. change (p_stk_top (a_pl A1)) with top in TTB1. change (p_stk_bot (a_pl A1)) with bot in TTB1.
    pose proof (free_IAM A1 m1r md1 p old AI1 HL1) as IAM1. rewrite VIEW1' in IAM1.
    (first [ pose proof ((realloc_stats A1 m1r md1 AI1)) as dR_12; dex2 dR_12 as rc rd; rename dR_12 into TST1 | pose proof ((realloc_stats A1 m1r md1 AI1)) as dR_12; dand3 dR_12 as rc rd TST1 | destruct (realloc_stats A1 m1r md1 AI1) as (rc & rd & TST1) ]). rewrite VIEW1' in TST1. change (p_thr (a_pl A1)) with thr in TST1.
    assert (TSDL : 0x5e7b28 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000) by (unfold pa_tsd; lia).
    replace (ret_pc (wz 0x58ed0)) with (wz 0x58ed0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose (Q2 := fun ms' : machine_state => exists (t0b t1b t2b a6b a7b t3b t4b t5b t6b rc' rd' : word) (jb1 jrest js0 : list byte) (m2 : mem),
        ms' = MS (mkR (wz 0x37bfc) (wz (fp + -2208)) gp (cl_tp LPA) t0b t1b t2b (wz (fp + -2136)) (wz p)
                     (wz 0xb1558) (wz n) (wz 8) (wz (fp + -2136)) (wz 1) (wz 1) a6b a7b
                     (wz 0xb1558) (wz n) (wz 1) (wz (fp + -2136)) (wz (fp + -89)) s7 s8 s9 s10 s11 t3b t4b t5b t6b)
                 F (wz alloc_entry) fc None m2 (seg_rom rsegs)
        /\ rw_cells rsegs m2 (fp + -2136) [C8 (wz (fp + -2136 + 16))]
        /\ (if unwind_depth2 top bot fp
            then rw_cells rsegs m2 (fp + -2136 + 8) [C4 (wz 2)] /\ rw_cells rsegs m2 (fp + -2136 + 16) [C8 (wz 0x58fc8); C8 ra]
            else rw_cells rsegs m2 (fp + -2136 + 8) [C4 (wz 1)] /\ rw_cells rsegs m2 (fp + -2136 + 16) [C8 (wz 0x58fc8); CB 8 jb1])
        /\ rw_cells rsegs m2 (fp + -2136 + 12) [C4 (wz 0)]
        /\ rw_cells rsegs m2 (fp + -2136 + 32) [CB 2024 jrest]
        /\ rw_cells rsegs m2 (fp + -2136 + 2056) [C8 (wz fp)]
        /\ rw_cells rsegs m2 (fp + -72) [CB 8 pad1]
        /\ rw_cells rsegs m2 (fp + -2144) [CB 8 pad2]
        /\ rw_cells rsegs m2 (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)]
        /\ rw_cells rsegs m2 (thr + 2856) [C8 rc'; C8 rd']
        /\ rw_cells rsegs m2 (fp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells rsegs m2 (fp + -2160) [CB 8 js0; C8 (wz 0x59038)]
        /\ rw_cells rsegs m2 (fp + -2208) [C8 (wz 1); C8 (wz 0x58fc8); C8 (wz p); C8 (wz n); C8 (wz fp); C8 (wz 0x37b80)]
        /\ munch [(fp - 2144 - 224, fp); (thr + off_th_unwinding, thr + off_th_unwinding + 1); (thr + 2856, thr + 2872)] m1 m2
        /\ wmono rsegs m1 m2 /\ mem_inv rsegs m2 /\ stk rsegs m2 (fp - 8192) (fp - 2208)).
    eapply (srz_evt_restrict rsegs (pa_hull A1) (asI_hull_segs A1 m1r md1 AI1) pa_wx _ (pa_eager A1) Q2 _ md1 T HMI1 HH1).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A1)) m1r) with (aview_of (pa_hull A1) m1r). rewrite VIEW1'.
      pose proof (realloc_mid_ok UNW TSS) as MID. unfold realloc_mid_stmt in MID.
      replace sp with (wz fp) by (subst fp; apply Z_to_bv_bv_unsigned).
      eapply (MID _ gp (cl_tp LPA) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m1
                fp p n pa_tsd (p_ctx (a_pl A1)) thr top bot (fp - 8192) ra s0 s6 s5 s4 s3 s2 s1 rc rd junk pad1 pad2); clear MID.
      all: try eassumption. all: try reflexivity. all: try (clear - CE CEIL SPA SPH SPR PF PCE OR NRQ RA0 RANE VLE TOPR BOTR TSDL SEP_tc THF TH2 LO; lia).
      intros t0b t1b t2b a6b a7b t3b t4b t5b t6b rc' rd' jb1 jrest js0 m2 O0 DEP O12 O32 PC1 P1b P2b TUNW2 TST2 SAV2 F16 F48 MU2 WM2 MI2 ST2.
      apply evt_done. unfold Q2. first [ hotw_ex15 t0b t1b t2b a6b a7b t3b t4b t5b t6b rc' rd' jb1 jrest js0 m2 | exists t0b, t1b, t2b, a6b, a7b, t3b, t4b, t5b, t6b, rc', rd', jb1, jrest, js0, m2 ].
      split; [reflexivity|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }
    intros msr2 md2 HQ2 HI2 SB2 CL2.
    (first [ dex15 HQ2 as t0b t1b t2b a6b a7b t3b t4b t5b t6b rc' rd' jb1 jrest js0 m2; dand17 HQ2 as -> O0 DEP O12 O32 PC1 P1b P2b TUNW2 TST2 SAV2 F16 F48 MU2 WM2 MI2 ST2 | dand32 HQ2 as t0b t1b t2b a6b a7b t3b t4b t5b t6b rc' rd' jb1 jrest js0 m2 -> O0 DEP O12 O32 PC1 P1b P2b TUNW2 TST2 SAV2 F16 F48 MU2 WM2 MI2 ST2 | destruct HQ2 as (t0b & t1b & t2b & a6b & a7b & t3b & t4b & t5b & t6b & rc' & rd' & jb1 & jrest & js0 & m2 & -> & O0 & DEP & O12 & O32 & PC1 & P1b & P2b & TUNW2 & TST2 & SAV2 & F16 & F48 & MU2 & WM2 & MI2 & ST2) ]).
    rewrite unrestrict_MS. cbn [ms_mem] in CL2.
    lazymatch goal with |- context [munrestrict ?Hh (ms_mem (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro)) ?v2] => change (ms_mem (MS R FF pc fcx rv mm ro)) with mm end.
    unfold off_th_unwinding in TUNW2, MU2.
    assert (SM1 : mapped (aview_of (pa_hull A1) m1r) (fp - ASTK) ASTK).
    { rewrite VIEW1'. unfold ASTK. eapply (mapped_mono _ m1); [exact SM|].
      intros i Hi Hv. apply (wmono_NN _ _ _ WM1); [clear -Hi CE CEIL; lia| clear -Hi SPR CE CEIL; lia| exact Hv]. }
    assert (AG2 : forall a, 0 <= a < 2^64 -> ~ (fp - ASTK <= a < fp) -> a <> p_thr (a_pl A1) + 3168 -> ~ wexc A1 a -> m2 (wz a) = aview_of (pa_hull A1) m1r (wz a)).
    { change (p_thr (a_pl A1)) with thr. rewrite VIEW1'.
      intros a Ha NW NT NE. unfold ASTK in NW. unfold wexc in NE. change (p_thr (a_pl A1)) with thr in NE. apply MU2. rewrite unsigned_lit by lia. cbn [outside app].
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; first [apply NW; clear -X; lia| apply NT; clear -X; lia| apply NE; clear -X; lia]. }
    assert (WM2' : wmono rsegs (aview_of (pa_hull A1) m1r) m2) by (rewrite VIEW1'; exact WM2).
    pose proof (shell_ainv_stats A1 m1r md1 md2 fp m2 AI1 CEIL AG2 TUNW2 WM2' CL2 HI2 SB2) as AI2.
    pose proof (shell_view A1 m1r m2 CL2) as VIEW2.
    set (m2r := munrestrict (hidc (pa_hull A1)) m1r m2) in *.
    set (KEY := wkey 0x58fc8 top bot fp ra).
    (* [comment removed for export] *)
    pose proof ACORE as AC. unfold alloc_core_cps1 in AC.
    eapply (AC (wz 0x37bfc) (wz (fp + -2208)) gp (cl_tp LPA) t0b t1b t2b (wz (fp + -2136)) (wz p) a6b a7b (wz 0xb1558) (wz n) (wz 1) (wz (fp + -2136)) (wz (fp + -89))
               s7 s8 s9 s10 s11 t3b t4b t5b t6b F fc m2r md2 A1 n 1 (fp + -2136) (fp - 8192) fp KEY T); clear AC.
    - (* [comment removed for export] *)
      unfold alloc_core_pre. rewrite VIEW2. cbn [cl_segs LPA].
      rewrite !unsigned_lit by lia.
      assert (KL : Z.of_nat (length KEY) = (if unwind_depth2 top bot fp then 2 else 1)) by (unfold KEY, wkey; destruct (unwind_depth2 top bot fp); reflexivity).
      split; [exact AI2|]. split; [exact MI2|]. split; [unfold REQ_MAX; lia|]. split; [exact NCAP|]. split; [exact LIM|]. split; [exact NLV|].
      split; [exact TINY|]. split; [exact SCRED|]. split; [exact PCRED|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [clear -SPH; lia|].
      split; [clear -SPA; Z.div_mod_to_equations; lia|]. split; [reflexivity|].
      split; [exact ST2|].
      split. { eapply (mapped_mono _ m2); [eapply (mapped_mono _ m1); [eapply (ALogic2.mapped_sub _ _ _ _ _ SM); lia|]|].
               - intros i Hi Hv. apply (wmono_NN _ _ _ WM1); [clear -Hi CE CEIL; lia| clear -Hi SPR CE CEIL; lia| exact Hv].
               - intros i Hi Hv. apply (wmono_NN _ _ _ WM2); [clear -Hi CE CEIL; lia| clear -Hi SPR CE CEIL; lia| exact Hv]. }
      split; [lia|]. split; [lia|].
      split. { rewrite KL. destruct (unwind_depth2 top bot fp); destruct DEP as [D8 D16].
               all: split; [exact (conj I (conj I I))|]; cbn [cells_bytes cbytes app]; rewrite app_nil_r.
               all: apply bytes_at_app; split; [destruct O0 as [[_ B] _]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B; exact B|].
               all: rewrite length_le8; replace (fp + -2136 + Z.of_nat 8) with (fp + -2136 + 8) by lia.
               1: exact (proj2 (ro_C44_C8 m2 (fp + -2136 + 8) 2 eq_refl D8 ltac:(replace (fp + -2136 + 8 + 4) with (fp + -2136 + 12) by lia; exact O12))).
               exact (proj2 (ro_C44_C8 m2 (fp + -2136 + 8) 1 eq_refl D8 ltac:(replace (fp + -2136 + 8 + 4) with (fp + -2136 + 12) by lia; exact O12))). }
      split. { unfold KEY, wkey. destruct (unwind_depth2 top bot fp); destruct DEP as [D8 D16]; destruct D16 as [[_ B] _]; cbn [cells_bytes cbytes app map u64s] in B |- *.
               - rewrite app_nil_r in B. rewrite Z_to_bv_bv_unsigned. exact B.
               - apply bytes_at_app in B. destruct B as [B _]. rewrite app_nil_r. exact B. }
      split. { unfold KEY, wkey. (first [ pose proof ((place_extra A m md AI)) as dR_14; dand6 dR_14 as _ _ _ _ SK _ | destruct (place_extra A m md AI) as (_ & _ & _ & _ & SK & _) ]).
               destruct (SK 0x58fc8 (bv_unsigned ra) ltac:(cbn; clear; tauto) SITE) as [KY2 KY1].
               change (p_dkeys (a_pl A1)) with (p_dkeys (a_pl A)). destruct (unwind_depth2 top bot fp); [exact KY2| exact KY1]. }
      apply wkey_range. lia.
    - (* [comment removed for export] *)
      unfold alloc_core_K1v. cbv zeta. rewrite VIEW2.
      intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c r A' m' md' AI' MI' AMD HLE FFR PLE IAE VG RNZ LN0 LS1 LQ LB TCR LN LS LP CZ PRIM FRK ERRK CFI STK'.
      cbn [cl_segs cl_errno LPA] in MI', FRK, ERRK, CFI, STK' |- *.
      set (v' := aview_of (pa_hull A') m') in *.
      replace (ret_pc (wz 0x37bfc)) with (wz 0x37bfc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite !unsigned_lit in CFI, STK' by lia. replace (fp - (fp - 8192)) with 8192 in FRK by lia.
      destruct (asI_minv A' m' md' AI') as [HMI' HH'].
      (first [ pose proof ((hit_place A' m' md' AI')) as dR_15; dand3 dR_15 as TH1' TH2' _ | pose proof (hit_place A' m' md' AI') as (TH1' & TH2' & _) ]). pose proof (aobj_facts _ _ TH1') as THF'.
      pose proof (hit_TUNW A' m' md' AI') as TUNW'. fold v' in TUNW'. unfold off_th_unwinding in TUNW'.
      (* [comment removed for export] *)
      assert (CF : forall a cs, rw_cells rsegs m2 a cs -> fp - 2208 <= a -> a + Z.of_nat (cells_size cs) <= fp -> rw_cells rsegs v' a cs).
      { intros a cs H Ha Hb. apply (rw_cells_agree m2 v' a cs H). intros i Hi. apply CFI. lia. }
      pose proof (CF _ _ F48 ltac:(lia) ltac:(cbn; lia)) as F48'. pose proof (CF _ _ F16 ltac:(lia) ltac:(cbn; destruct F16 as [[[? WFj] ?] ?]; cbn in WFj; lia)) as F16'.
      pose proof (CF _ _ O0 ltac:(lia) ltac:(cbn; lia)) as O0'.
      pose proof (CF _ _ O12 ltac:(lia) ltac:(cbn; lia)) as O12'. pose proof (CF _ _ O32 ltac:(lia) ltac:(cbn; lia)) as O32'.
      pose proof (CF _ _ PC1 ltac:(lia) ltac:(cbn; lia)) as PC1'. pose proof (CF _ _ SAV2 ltac:(lia) ltac:(cbn; lia)) as SAV'.
      pose proof (CF _ _ P1b ltac:(lia) ltac:(cbn; destruct P1b as [[[? WFj] ?] ?]; cbn in WFj; lia)) as P1'.
      pose proof (CF _ _ P2b ltac:(lia) ltac:(cbn; destruct P2b as [[[? WFj] ?] ?]; cbn in WFj; lia)) as P2'.
      assert (DEP' : exists w8 cs16, cells_size cs16 = 16%nat /\ rw_cells rsegs v' (fp + -2128) [C4 w8] /\ rw_cells rsegs v' (fp + -2120) cs16).
      { destruct (unwind_depth2 top bot fp); destruct DEP as [D8 D16].
        - exists (wz 2), [C8 (wz 0x58fc8); C8 ra]. split; [reflexivity|]. split.
          + replace (fp + -2128) with (fp + -2136 + 8) by lia. exact (CF _ _ D8 ltac:(lia) ltac:(cbn; lia)).
          + replace (fp + -2120) with (fp + -2136 + 16) by lia. exact (CF _ _ D16 ltac:(lia) ltac:(cbn; lia)).
        - exists (wz 1), [C8 (wz 0x58fc8); CB 8 jb1]. split; [reflexivity|]. split.
          + replace (fp + -2128) with (fp + -2136 + 8) by lia. exact (CF _ _ D8 ltac:(lia) ltac:(cbn; lia)).
          + replace (fp + -2120) with (fp + -2136 + 16) by lia. apply (CF _ _ D16 ltac:(lia)). destruct D16 as [[[_ WFj] _] _]. cbn in WFj |- *. lia. }
      (first [ dex2 DEP' as w8 cs16; dand3 DEP' as S16 D8' D16' | dand5 DEP' as w8 cs16 S16 D8' D16' | destruct DEP' as (w8 & cs16 & S16 & D8' & D16') ]).
      replace (fp + -2136 + 12) with (fp + -2124) in O12' by lia. replace (fp + -2136 + 32) with (fp + -2104) in O32' by lia.
      replace (fp + -2136 + 2056) with (fp + -80) in PC1' by lia.
      (* [comment removed for export] *)
      assert (OWW : forall a, pa_owned A a -> ~ (fp - 8192 <= a < fp) /\ ~ (6191924 <= a < 6191924 + 4)).
      { intros a OW. destruct (asI_owned_where A m md a AI OW) as [ST0|HZ].
        - cbn [cl_static LPA] in ST0. unfold pa_static in ST0. clear -ST0 CE CEIL. lia.
        - unfold heap_zone, in_image in HZ. cbn [cl_image_lo cl_image_hi LPA] in HZ. clear -HZ CEIL. lia. }
      (* [comment removed for export] *)
      assert (PR1 : forall a, 0 <= a < 2^64 -> ~ (fp - 8192 <= a < fp) -> ~ pa_owned A a -> m2 (wz a) = v (wz a)).
      { intros a Ha NW NO.
        assert (NTH : ~ (thr <= a < thr + 4096)).
        { intros X. apply NO. (first [ pose proof ((bm_nth_fixed A)) as dR_17; dand6 dR_17 as _ _ _ _ E4 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & E4 & _) ]).
          apply (owned_rt A a (a_thr A) 4096); [apply rt_fixed_in; left; reflexivity| unfold a_thr; exact X| |].
          - exact (fixed_bm_no_live_user A 4 (a_thr A) 4096 a WF0 ltac:(lia) E4 ltac:(unfold a_thr; exact X)).
          - exact (fixed_bm_no_live_frame A 4 (a_thr A) 4096 a WF0 ltac:(lia) ltac:(lia) E4 ltac:(unfold a_thr; exact X)). }
        assert (NIA : ~ ia_blk a).
        { intros X. apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. unfold ia_blk in X. clear -X. lia. }
        transitivity (m1 (wz a)).
        - apply MU2. rewrite unsigned_lit by lia. cbn [outside app]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; first [apply NW; clear -X; lia| apply NTH; clear -X; lia].
        - apply AGc; [exact Ha| unfold ASTK; exact NW| clear -NTH; lia| exact NIA]. }
      assert (PR2 : forall a, (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> 0 <= a < 2^64 -> v (wz a) <> None -> m2 (wz a) <> None).
      { intros a H1 H2 H3. exact (wmono_NN _ _ a WM2 H1 H2 (wmono_NN _ _ a WM1 H1 H2 H3)). }
      (* [comment removed for export] *)
      (first [ pose proof ((asI_live_ok A m md p old AI HL)) as dR_18; dand8 dR_18 as _ _ _ _ _ _ NOWp _ | pose proof (asI_live_ok A m md p old AI HL) as (_ & _ & _ & _ & _ & _ & NOWp & _) ]).
      assert (NB0 : forall a, ~ newblk 0 n a) by (intros a [[X _]|[X _]]; exact (X eq_refl)).
      + (* [comment removed for export] *)
        assert (PR : p <> r) by (intros E; rewrite E in HL1; rewrite LN0 in HL1; discriminate).
        assert (HLp' : as_live A' p = Some old) by (rewrite (LQ p PR); exact HL1).
        (first [ pose proof ((asI_live_ok A' m' md' p old AI' HLp')) as dR_24; dand8 dR_24 as _ _ _ _ _ MPp NOWp' _ | pose proof (asI_live_ok A' m' md' p old AI' HLp') as (_ & _ & _ & _ & _ & MPp & NOWp' & _) ]). fold v' in MPp.
        (first [ pose proof ((asI_live_ok A' m' md' r n AI' LS1)) as dR_25; dand8 dR_25 as _ _ APR RCE NIr MPr NOWr _ | pose proof (asI_live_ok A' m' md' r n AI' LS1) as (_ & _ & APR & RCE & NIr & MPr & NOWr & _) ]). fold v' in MPr.
        assert (RR : 0 < r < 2^64).
        { unfold app_range, app_lo, app_hi, kLowAppEnd, kHighMemBeg in APR. cbn [cl_image_lo cl_image_hi LPA] in APR. clear -APR RCE RNZ CE. lia. }
        pose proof (conj (ai_wf _ _ _ _ _ _ _ AI') (ai_repr _ _ _ _ _ _ _ AI') : WF A' /\ @arepr _ DepotRepL LPA AL_pboth [] A' v') as AR'.
        (first [ pose proof ((free_li A' p old HLp')) as dR_26; dex1 dR_26 as lip; destruct dR_26 as [LUp LNp] | pose proof ((free_li A' p old HLp')) as dR_26; dand3 dR_26 as lip LUp LNp | destruct (free_li A' p old HLp') as (lip & LUp & LNp) ]). (first [ pose proof ((free_li A' r n LS1)) as dR_27; dex1 dR_27 as lir; destruct dR_27 as [LUr LNr] | pose proof ((free_li A' r n LS1)) as dR_27; dand3 dR_27 as lir LUr LNr | destruct (free_li A' r n LS1) as (lir & LUr & LNr) ]).
        pose proof (GEO A' v' p old lip sp AR' LUp LNp) as Gp. pose proof (GEO A' v' r n lir sp AR' LUr LNr) as Gr.
        (first [ pose proof ((free_geom A' m' md' r n AI' LS1)) as dR_28; dand4 dR_28 as _ RLO _ _ | destruct (free_geom A' m' md' r n AI' LS1) as (_ & RLO & _ & _) ]). pose proof (aobj_facts _ _ RLO) as RF.
        (* [comment removed for export] *)
        assert (HDO : forall a, p + -16 <= a < p -> pa_owned A' a).
        { intros a Ha. apply (carved_owned A' v' AR' (li_chunk lip) a (known_carved A' v' AR' _ _ (KN A' v' p old lip AR' LUp LNp))); [clear -Ha Gp; lia|].
          intros u li' Hl E Hu. destruct (Z.eq_dec u p) as [->|NE].
          - rewrite LUp in Hl. injection Hl as <-. rewrite LNp in Hu. clear -Ha Hu. lia.
          - exact (live_live_chunk A' v' AR' u p li' lip Hl LUp NE E). }
        assert (SEPC : p + old <= r \/ r + n <= p + -16).
        { destruct (asI_live_disjoint A' m' md' p old r n AI' HLp' LS1 PR) as [X|X]; [left; exact X|].
          destruct (Z.le_gt_cases (r + n) (p + -16)) as [Y|Y]; [right; exact Y|]. exfalso.
          apply (NOWr (Z.max r (p + -16) - r)); [clear -X Y NRQ RR; lia|]. replace (r + (Z.max r (p + -16) - r)) with (Z.max r (p + -16)) by lia.
          apply HDO. clear -X Y NRQ RR. lia. }
        (* [comment removed for export] *)
        (first [ pose proof ((free_HDR A' m' md' p old AI' HLp')) as dR_29; dex2 dR_29 as b1 cid; dand6 dR_29 as B1R _ _ _ HDR _ | pose proof ((free_HDR A' m' md' p old AI' HLp')) as dR_29; dand8 dR_29 as b1 cid B1R _ _ _ HDR _ | destruct (free_HDR A' m' md' p old AI' HLp') as (b1 & cid & B1R & _ & _ & _ & HDR & _) ]). fold v' in HDR.
        pose proof (proj1 (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI')) : Forall (fun c => bytes_at rsegs v' (fst c) (snd c)) (cl_consts LPA)) as CF'.
        pose proof (bytes_ro_C8 _ _ _ (consts_cell v' 0xa8b98 (le8 (Z_to_bv 64 0xaaa10)) CF' eq_refl)) as Cg1.
        pose proof (bytes_ro_C8 _ _ _ (consts_cell v' 0xaaa10 (le8 (Z_to_bv 64 0xa1b8c)) CF' eq_refl)) as Cg2.
        clear CF'.
        assert (LBCB : forall q k, as_live A' q = Some k -> exists uj, rw_cells rsegs v' q [CB (Z.to_nat k) uj]).
        { intros q k HLq. (first [ pose proof ((asI_live_ok A' m' md' q k AI' HLq)) as dR_30; dand7 dR_30 as NRq _ APq RCq NIq MPq _ | pose proof (asI_live_ok A' m' md' q k AI' HLq) as (NRq & _ & APq & RCq & NIq & MPq & _) ]).
          assert (R0 : 4096 <= q).
          { unfold app_range, app_lo, app_hi, kLowAppEnd, kHighMemBeg in APq. cbn [cl_image_lo cl_image_hi LPA] in APq. clear -APq. lia. }
          (first [ pose proof ((junk_at_of_mapped rsegs _ q k ltac:(clear -R0; lia) ltac:(clear -NRq; lia) ltac:(clear -RCq CE; lia) MPq)) as dR_31; dex1 dR_31 as bs; destruct dR_31 as [L B] | pose proof ((junk_at_of_mapped rsegs _ q k ltac:(clear -R0; lia) ltac:(clear -NRq; lia) ltac:(clear -RCq CE; lia) MPq)) as dR_31; dand3 dR_31 as bs L B | destruct (junk_at_of_mapped rsegs _ q k ltac:(clear -R0; lia) ltac:(clear -NRq; lia) ltac:(clear -RCq CE; lia) MPq) as (bs & L & B) ]).
          exists bs. apply ro_rw.
          - split; [cbn; split; [clear -L; lia| exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
          - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -NRq; lia). exact MPq. }
        destruct (LBCB p old HLp') as (ujp & UBp). destruct (LBCB r n LS1) as (ujr & UBr).
        assert (MN : 0 <= Z.min n old <= old /\ Z.min n old <= n) by (clear -NRQ OR; lia).
        pose proof UBp as SRC.
        apply (rw_cells_split_CB rsegs v' p [] (Z.to_nat old) ujp [] [Z.to_nat (Z.min n old); (Z.to_nat old - Z.to_nat (Z.min n old))%nat]) in SRC; [| cbn; clear -MN; lia].
        cbn [app mk_CB_cells] in SRC. apply (rw_cells_app_split _ _ [CB _ _] [CB _ _]) in SRC as [SRC _].
        pose proof UBr as DST.
        apply (rw_cells_split_CB rsegs v' r [] (Z.to_nat n) ujr [] [Z.to_nat (Z.min n old); (Z.to_nat n - Z.to_nat (Z.min n old))%nat]) in DST; [| cbn; clear -MN; lia].
        cbn [app mk_CB_cells] in DST. apply (rw_cells_app_split _ _ [CB _ _] [CB _ _]) in DST as [DST _].
        set (src := firstn (Z.to_nat (Z.min n old)) ujp) in *.
        assert (SRCL : length src = Z.to_nat (Z.min n old)) by (destruct SRC as [[[WF1 _] _] _]; cbn in WF1; exact WF1).
        assert (SRCB : bytes_at rsegs v' p src) by (destruct SRC as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B).
        idtac "r1 facts done".
        pose (Q3 := fun ms3 : machine_state => exists (t0d t1d t2d a6d a7d t3d t4d t5d t6d : word) (m3 : mem),
            ms3 = MS (mkR (wz 0x37c90) (wz (fp + -2208)) gp (cl_tp LPA) t0d t1d t2d (wz (fp + -2136)) (wz p)
                         (wz 0xb1558) (wz p) (wz 0) (wz 0) (wz (fp + -2136)) (wz 1) a6d a7d
                         (wz 0xb1558) (wz (Z.min n old)) (wz r) (wz (fp + -2136)) (wz (fp + -89)) s7 s8 s9 s10 s11 t3d t4d t5d t6d)
                     F (wz dealloc_entry) fc None m3 (seg_rom rsegs)
            /\ mem_inv rsegs m3 /\ munch [(r, r + Z.min n old)] v' m3 /\ wmono rsegs v' m3
            /\ rw_cells rsegs m3 r [CB (Z.to_nat (Z.min n old)) src] /\ bytes_at rsegs m3 p src /\ stk rsegs m3 (fp - 8192) (fp - 2208)).
        eapply (srz_evt_restrict rsegs (pa_hull A') (asI_hull_segs A' m' md' AI') pa_wx _ (pa_eager A') Q3 _ md' T HMI' HH').
        { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A')) m') with v'.
          pose proof realloc_mid2_ok as MID2. unfold realloc_mid2_stmt, realloc_mid2_entry in MID2.
          eapply (MID2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc v' fp (fp - 8192) p n old r b1 src _); clear MID2.
          all: try eassumption. all: try reflexivity. all: try (clear - CE CEIL SPH SPR RR NRQ OR; lia). 1: exact (proj1 HDR).
          intros t0d t1d t2d a6d a7d t3d t4d t5d t6d m3 MI3 MU3 WM3 DST3 SRC3 ST3. apply evt_done. unfold Q3.
          first [ hotw_ex10 t0d t1d t2d a6d a7d t3d t4d t5d t6d m3 | exists t0d, t1d, t2d, a6d, a7d, t3d, t4d, t5d, t6d, m3 ].
          split; [reflexivity|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }
        intros msr3 md3 HQ3 HI3 SB3 CL3.
        (first [ dex10 HQ3 as t0d t1d t2d a6d a7d t3d t4d t5d t6d m3; dand7 HQ3 as -> MI3 MU3 WM3 DST3 SRC3 ST3 | dand17 HQ3 as t0d t1d t2d a6d a7d t3d t4d t5d t6d m3 -> MI3 MU3 WM3 DST3 SRC3 ST3 | destruct HQ3 as (t0d & t1d & t2d & a6d & a7d & t3d & t4d & t5d & t6d & m3 & -> & MI3 & MU3 & WM3 & DST3 & SRC3 & ST3) ]).
        rewrite unrestrict_MS. cbn [ms_mem] in CL3.
        lazymatch goal with |- context [munrestrict ?Hh (ms_mem (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro)) ?v2] => change (ms_mem (MS R FF pc fcx rv mm ro)) with mm end.
        idtac "r1 memcpy seg done".
        assert (AG3 : forall a, 0 <= a < 2^64 -> ~ (fp - ASTK <= a < fp) -> a <> p_thr (a_pl A') + 3168 -> ~ (6191924 <= a < 6191924 + 4) ->
                      ~ (r <= a < r + Z.min n old) -> m3 (wz a) = v' (wz a)).
        { intros a Ha NW NT NE NB. apply MU3. rewrite unsigned_lit by lia. cbn [outside app]. split; [exact NB| exact I]. }
        assert (XOK : forall a, r <= a < r + Z.min n old -> ~ pa_owned A' a /\ ~ cl_shared LPA a /\ v' (wz a) <> None).
        { intros a Ha. split; [| split].
          - replace a with (r + (a - r)) by lia. apply NOWr; clear -Ha MN; lia.
          - intros SH; pose proof (asI_shared_where a SH) as W; cbn [cl_rw_lo cl_image_hi LPA] in W; clear -W Gr Ha MN; lia.
          - replace a with (r + (a - r)) by lia. apply MPr; clear -Ha MN; lia. }
        (* [comment removed for export] *)
        assert (RNT : forall a, r <= a < r + n -> ~ (p_thr (a_pl A') <= a < p_thr (a_pl A') + 4096)).
        { intros a Ha Ht. (first [ pose proof ((bm_nth_fixed A')) as dR_33; dand6 dR_33 as _ _ _ _ E4 _ | pose proof (bm_nth_fixed A') as (_ & _ & _ & _ & E4 & _) ]).
          apply (fixed_bm_no_live_user A' 4 (a_thr A') 4096 a (proj1 AR') ltac:(clear; lia) E4 ltac:(unfold a_thr; exact Ht)).
          first [ hotw_ex2 r lir | exists r, lir ]. split; [exact LUr| rewrite LNr; exact Ha]. }
        assert (TUNW3 : rw_cells rsegs m3 (p_thr (a_pl A') + 3168) [C1 (Z_to_bv 8 0)]).
        { apply (rw_cells_agree v' m3 _ _ TUNW'). intros i Hi. cbn in Hi. apply MU3. rewrite unsigned_lit by (clear -THF' Hi CE; lia). cbn [outside app].
          split; [| exact I]. intros X; exact (RNT (p_thr (a_pl A') + 3168 + i) ltac:(clear -X MN; lia) ltac:(clear -Hi; lia)). }
        assert (SM' : mapped v' (fp - ASTK) ASTK) by ((first [ dand4 FRK as _ _ F3 _ | destruct FRK as (_ & _ & F3 & _) ]); unfold ASTK; exact F3).
        pose proof (shell_ainv A' m' md' md3 fp m3 (fun a => r <= a < r + Z.min n old) AI' CEIL SM' AG3 XOK TUNW3 WM3 CL3 HI3 SB3) as AI3.
        pose proof (shell_view A' m' m3 CL3) as VIEW3.
        set (m3r := munrestrict (hidc (pa_hull A')) m' m3) in *.
        destruct (asI_minv A' m3r md3 AI3) as [HMI3 HH3].
        idtac "r1 AI3 done".
        (* [comment removed for export] *)
        assert (CF3 : forall a cs, rw_cells rsegs m2 a cs -> fp - 2208 <= a -> a + Z.of_nat (cells_size cs) <= fp -> rw_cells rsegs m3 a cs).
        { intros a cs H Ha Hb. apply (rw_cells_agree v' m3 a cs (CF a cs H Ha Hb)). intros i Hi. apply MU3.
          rewrite unsigned_lit by (clear -Ha Hb Hi CE CEIL SPR; lia). cbn [outside app]. split; [clear -Ha Hi RCE CEIL MN; lia| exact I]. }
        assert (KL : Z.of_nat (length KEY) = (if unwind_depth2 top bot fp then 2 else 1)) by (unfold KEY, wkey; destruct (unwind_depth2 top bot fp); reflexivity).
        assert (SM3 : mapped m3 (fp + -2208) (fp - (fp + -2208))).
        { eapply (mapped_mono _ m3); [eapply (ALogic2.mapped_sub _ _ _ _ _ SM'); unfold ASTK; clear; lia|].
          intros i Hi Hv. apply (wmono_NN _ _ _ WM3); [clear -Hi CE CEIL; lia| clear -Hi SPR CE CEIL; lia| exact Hv]. }
        (* [comment removed for export] *)
        pose proof DCORE as DC. unfold dealloc_core_cps in DC.
        eapply (DC (wz 0x37c90) (wz (fp + -2208)) gp (cl_tp LPA) t0d t1d t2d (wz (fp + -2136)) (wz p) (wz 0) (wz 0) a6d a7d
                   (wz 0xb1558) (wz (Z.min n old)) (wz r) (wz (fp + -2136)) (wz (fp + -89)) s7 s8 s9 s10 s11 t3d t4d t5d t6d
                   F fc m3r md3 A' p old (fp + -2136) (fp - 8192) fp KEY T); clear DC.
        * (* [comment removed for export] *)
          unfold dealloc_core_pre. rewrite VIEW3. cbn [cl_segs LPA]. rewrite !unsigned_lit by lia.
          split; [exact AI3|]. split; [exact MI3|]. split; [right; exact HLp'|]. split; [rewrite IAE; reflexivity|]. split; [reflexivity|].
          split; [exact CEIL|]. split; [clear -CE CEIL; lia|]. split; [clear -SPR; lia|]. split; [exact SPH|].
          split; [clear -SPA SPR; Z.div_mod_to_equations; lia|]. split; [reflexivity|].
          split; [exact ST3|]. split; [exact SM3|].
          split; [clear; lia|]. split; [clear; lia|].
          split. { rewrite KL. destruct (unwind_depth2 top bot fp); destruct DEP as [D8 D16].
                   all: split; [exact (conj I (conj I I))|]; cbn [cells_bytes cbytes app]; rewrite app_nil_r.
                   all: apply bytes_at_app; split; [destruct (CF3 _ _ O0 ltac:(lia) ltac:(cbn; lia)) as [[_ B] _]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B; exact B|].
                   all: rewrite length_le8; replace (fp + -2136 + Z.of_nat 8) with (fp + -2136 + 8) by lia.
                   1: exact (proj2 (ro_C44_C8 m3 (fp + -2136 + 8) 2 eq_refl (CF3 _ _ D8 ltac:(lia) ltac:(cbn; lia)) ltac:(replace (fp + -2136 + 8 + 4) with (fp + -2136 + 12) by lia; exact (CF3 _ _ O12 ltac:(lia) ltac:(cbn; lia))))).
                   exact (proj2 (ro_C44_C8 m3 (fp + -2136 + 8) 1 eq_refl (CF3 _ _ D8 ltac:(lia) ltac:(cbn; lia)) ltac:(replace (fp + -2136 + 8 + 4) with (fp + -2136 + 12) by lia; exact (CF3 _ _ O12 ltac:(lia) ltac:(cbn; lia))))). }
          split. { unfold KEY, wkey. destruct (unwind_depth2 top bot fp); destruct DEP as [D8 D16];
                     destruct (CF3 _ _ D16 ltac:(lia) ltac:(cbn; try lia; destruct D16 as [[[? WFj] ?] ?]; cbn in WFj |- *; lia)) as [[_ B] _]; cbn [cells_bytes cbytes app map u64s] in B |- *.
                   - rewrite app_nil_r in B. rewrite Z_to_bv_bv_unsigned. exact B.
                   - apply bytes_at_app in B. destruct B as [B _]. rewrite app_nil_r. exact B. }
          split. { unfold KEY, wkey. (first [ pose proof ((place_extra A m md AI)) as dR_35; dand6 dR_35 as _ _ _ _ SK _ | destruct (place_extra A m md AI) as (_ & _ & _ & _ & SK & _) ]).
                   destruct (SK 0x58fc8 (bv_unsigned ra) ltac:(cbn; clear; tauto) SITE) as [KY2 KY1].
                   rewrite PLE. change (p_dkeys (a_pl A1)) with (p_dkeys (a_pl A)). destruct (unwind_depth2 top bot fp); [exact KY2| exact KY1]. }
          apply wkey_range. clear; lia.
        * (* [comment removed for export] *)
          unfold dealloc_core_K. cbv zeta. rewrite VIEW3.
          intros t0e t1e t2e a0e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e A'' m'' md'' AI'' MI'' AMD' FFR' PLE' HL'' HLQ' LB' TCR' SCR' PCR' NLV' VG' ERRK' FRK' CFI' STK''.   (* [comment removed for export] *)
          cbn [cl_segs cl_errno LPA] in MI'', FRK', ERRK', CFI', STK'' |- *.
          set (v'' := aview_of (pa_hull A'') m'') in *.
          replace (ret_pc (wz 0x37c90)) with (wz 0x37c90 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
          rewrite !unsigned_lit in CFI', STK'' by lia. replace (fp - (fp - 8192)) with 8192 in FRK' by lia.
          destruct (asI_minv A'' m'' md'' AI'') as [HMI'' HH''].
          (first [ pose proof ((hit_place A'' m'' md'' AI'')) as dR_36; dand3 dR_36 as TH1'' TH2'' _ | pose proof (hit_place A'' m'' md'' AI'') as (TH1'' & TH2'' & _) ]). pose proof (aobj_facts _ _ TH1'') as THF''.
          pose proof (hit_TUNW A'' m'' md'' AI'') as TUNW''. fold v'' in TUNW''. unfold off_th_unwinding in TUNW''.
          assert (CF4 : forall a cs, rw_cells rsegs m2 a cs -> fp - 2208 <= a -> a + Z.of_nat (cells_size cs) <= fp -> rw_cells rsegs v'' a cs).
          { intros a cs H Ha Hb. apply (rw_cells_agree m3 v'' a cs (CF3 a cs H Ha Hb)). intros i Hi. apply CFI'. lia. }
          pose proof (CF4 _ _ F48 ltac:(lia) ltac:(cbn; lia)) as F48''. pose proof (CF4 _ _ O0 ltac:(lia) ltac:(cbn; lia)) as O0''.
          pose proof (CF4 _ _ O12 ltac:(lia) ltac:(cbn; lia)) as O12''. pose proof (CF4 _ _ O32 ltac:(lia) ltac:(cbn; lia)) as O32''.
          pose proof (CF4 _ _ PC1 ltac:(lia) ltac:(cbn; lia)) as PC1''. pose proof (CF4 _ _ SAV2 ltac:(lia) ltac:(cbn; lia)) as SAV''.
          pose proof (CF4 _ _ F16 ltac:(lia) ltac:(cbn; destruct F16 as [[[? WFj] ?] ?]; cbn in WFj; lia)) as F16''.
          pose proof (CF4 _ _ P1b ltac:(lia) ltac:(cbn; destruct P1b as [[[? WFj] ?] ?]; cbn in WFj; lia)) as P1''.
          pose proof (CF4 _ _ P2b ltac:(lia) ltac:(cbn; destruct P2b as [[[? WFj] ?] ?]; cbn in WFj; lia)) as P2''.
          assert (DEP'' : exists w8' cs16', cells_size cs16' = 16%nat /\ rw_cells rsegs v'' (fp + -2128) [C4 w8'] /\ rw_cells rsegs v'' (fp + -2120) cs16').
          { destruct (unwind_depth2 top bot fp); destruct DEP as [D8 D16].
            - exists (wz 2), [C8 (wz 0x58fc8); C8 ra]. split; [reflexivity|]. split.
              + replace (fp + -2128) with (fp + -2136 + 8) by lia. exact (CF4 _ _ D8 ltac:(lia) ltac:(cbn; lia)).
              + replace (fp + -2120) with (fp + -2136 + 16) by lia. exact (CF4 _ _ D16 ltac:(lia) ltac:(cbn; lia)).
            - exists (wz 1), [C8 (wz 0x58fc8); CB 8 jb1]. split; [reflexivity|]. split.
              + replace (fp + -2128) with (fp + -2136 + 8) by lia. exact (CF4 _ _ D8 ltac:(lia) ltac:(cbn; lia)).
              + replace (fp + -2120) with (fp + -2136 + 16) by lia. apply (CF4 _ _ D16 ltac:(lia)). destruct D16 as [[[_ WFj] _] _]. cbn in WFj |- *. lia. }
          (first [ dex2 DEP'' as w8' cs16'; dand3 DEP'' as S16' D8'' D16'' | dand5 DEP'' as w8' cs16' S16' D8'' D16'' | destruct DEP'' as (w8' & cs16' & S16' & D8'' & D16'') ]).
          replace (fp + -2136 + 12) with (fp + -2124) in O12'' by lia. replace (fp + -2136 + 32) with (fp + -2104) in O32'' by lia.
          replace (fp + -2136 + 2056) with (fp + -80) in PC1'' by lia.
          idtac "K facts done".
          (* [comment removed for export] *)
          pose (Q4 := fun ms4 : machine_state =>
              ms4 = MS (mkR ra (wz fp) gp (cl_tp LPA) t0e t1e t2e s0 s1 (wz r) a1e a2e a3e a4e a5e a6e a7e s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3e t4e t5e t6e)
                       F (ret_pc ra) fc None v'' (seg_rom rsegs)
              /\ stk rsegs v'' (fp - 8192) fp).
          eapply (srz_evt_restrict rsegs (pa_hull A'') (asI_hull_segs A'' m'' md'' AI'') pa_wx _ (pa_eager A'') Q4 _ md'' T HMI'' HH'').
          { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A'')) m'') with v''.
            pose proof realloc_epi_ok as EPI. unfold realloc_epi_stmt, realloc_epi_entry in EPI.
            eapply (EPI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc v'' fp (fp - 8192) r); clear EPI.
            all: try eassumption. all: try reflexivity. all: try (clear - CE CEIL SPH SPR RR; lia).
            intros ST4. apply evt_done. unfold Q4. split; [reflexivity| exact ST4]. }
          intros msr4 md4 HQ4 HI4 SB4 CL4. destruct HQ4 as [-> ST4].
          rewrite unrestrict_MS. cbn [ms_mem] in CL4.
          lazymatch goal with |- context [munrestrict ?Hh (ms_mem (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro)) ?v2] => change (ms_mem (MS R FF pc fcx rv mm ro)) with mm end.
          idtac "seg3 done".
          assert (SM'' : mapped v'' (fp - ASTK) ASTK) by ((first [ dand4 FRK' as _ _ F3 _ | destruct FRK' as (_ & _ & F3 & _) ]); unfold ASTK; exact F3).
          pose proof (shell_ainv A'' m'' md'' md4 fp v'' nowhere AI'' CEIL SM'' ltac:(intros; reflexivity) ltac:(intros a []) TUNW'' (wmono_refl rsegs v'') CL4 HI4 SB4) as AI4.
          pose proof (shell_view A'' m'' v'' CL4) as VIEW4.
          replace (ret_pc ra) with ra by (rewrite <- (Z_to_bv_bv_unsigned ra); symmetry; apply ret_pc_even; [clear -RAR; lia| clear -RA4; Z.div_mod_to_equations; lia]).
          replace (Z_to_bv 64 fp) with sp by (subst fp; symmetry; apply Z_to_bv_bv_unsigned).
          idtac "pre KK".
          (* [comment removed for export] *)
          pose proof (Z_div_mod_eq_full (n + 7) 8) as NDEr. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(clear; lia)) as ERr.
          assert (NSHr : forall a, p <= a < p + old -> ~ (sh r <= a < sh r + (n + 7) / 8)).
          { intros a Ha X. clear -Ha X Gr PF NDE ER. unfold kLowShadowMapBeg, kHighMemBeg in *. lia. }
          assert (NSHp : forall a, r <= a < r + n -> ~ (sh p <= a < sh p + (old + 7) / 8)).
          { intros a Ha X. clear -Ha X Gp RF NDEr ERr. unfold kLowShadowMapBeg, kHighMemBeg in *. lia. }
          assert (HLr'' : as_live A'' r = Some n) by (rewrite (HLQ' r (not_eq_sym PR)); exact LS1).
          (first [ pose proof ((asI_live_ok A'' m'' md'' r n AI'' HLr'')) as dR_39; dand8 dR_39 as _ _ _ _ _ _ NOWr'' _ | pose proof (asI_live_ok A'' m'' md'' r n AI'' HLr'') as (_ & _ & _ & _ & _ & _ & NOWr'' & _) ]).
          assert (U1 : forall i, 0 <= i < old -> v' (wz (p + i)) = v (wz (p + i))).
          { intros i Hi. destruct FRK as (F1 & _). transitivity (m2 (wz (p + i))).
            - apply F1; [clear -Hi PF PCE CE; lia| exact (NOWp i Hi)| exact (NOWp' i Hi)| clear -Hi PCE CEIL; lia| cbn [cl_errno LPA]; clear -Hi PF NDE ER; lia| intros []|].
              intros [[_ X]|[_ X]]; [clear -X Hi SEPC NRQ; lia| exact (NSHr (p + i) ltac:(clear -Hi; lia) X)].
            - apply PR1; [clear -Hi PF PCE CE; lia| clear -Hi PCE CEIL; lia| exact (NOWp i Hi)]. }
          assert (U2 : forall i, 0 <= i < Z.min n old -> m3 (wz (r + i)) = v' (wz (p + i))).
          { intros i Hi. (first [ dand3 SRCB as _ _ SB | destruct SRCB as (_ & _ & SB) ]). destruct DST3 as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. (first [ dand3 DB as _ _ DB | destruct DB as (_ & _ & DB) ]).
            specialize (SB (Z.to_nat i) ltac:(rewrite SRCL; clear -Hi; lia)). specialize (DB (Z.to_nat i) ltac:(rewrite SRCL; clear -Hi; lia)).
            unfold wa in SB, DB. rewrite Z2Nat.id in SB, DB by (clear -Hi; lia). rewrite <- SB in DB.
            assert (Pm3 : m3 (wz (r + i)) <> None) by (apply (wmono_NN _ _ _ WM3); [clear -Hi Gr MN; lia| clear -Hi RCE CE RR MN; lia| apply MPr; clear -Hi MN; lia]).
            assert (Pv' : v' (wz (p + i)) <> None) by (apply MPp; clear -Hi MN; lia).
            unfold mrd in DB. destruct (m3 (wz (r + i))) as [b3|] eqn:E3; [| exfalso; exact (Pm3 eq_refl)].
            destruct (v' (wz (p + i))) as [b4|] eqn:E4; [exact DB| exfalso; exact (Pv' eq_refl)]. }
          assert (U3 : forall i, 0 <= i < n -> v'' (wz (r + i)) = m3 (wz (r + i))).
          { intros i Hi. destruct FRK' as (F1 & _).
            apply F1; [clear -Hi RCE CE RR; lia| exact (NOWr i Hi)| exact (NOWr'' i Hi)| clear -Hi RCE CEIL; lia| cbn [cl_errno LPA]; clear -Hi Gr; lia| | intros []].
            intros [[_ X]|[_ X]]; [clear -X Hi SEPC OR; lia| exact (NSHp (r + i) ltac:(clear -Hi; lia) X)]. }
          idtac "U done".
          eapply (KK t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e r A'' (munrestrict (hidc (pa_hull A'')) m'' v'') md4).
          -- exact AI4.
          -- cbn [cl_segs LPA]. rewrite VIEW4. exact MI''.
          -- eapply (wamd_sbm_l md md1); [exact SB1| exact HH|]. eapply (wamd_sbm_l md1 md2); [exact SB2| exact HH1|].
             eapply amd_frame_trans; [exact AMD|]. eapply (wamd_sbm_l md' md3); [exact SB3| exact HH'|]. eapply wamd_sbm_r; [exact AMD'| exact SB4].
          -- intros ff. rewrite (FFR' ff). exact (FFR ff).
          -- rewrite TCR'. exact TCR.
          -- rewrite NLV', LN, (proj2 (Z.eqb_neq p 0) PNZ). change (as_nlive A1) with (as_nlive A). clear; lia.
          -- rewrite VIEW4. split; [exact RNZ|]. split; [exact (not_eq_sym PR)|]. split; [exact LN0|]. split; [exact HLr''|]. split; [exact HL''|].
             split; [intros q Hqr Hqp; rewrite (HLQ' q Hqp); exact (LQ q Hqr)|].
             split; [rewrite LB', LB; change (as_livebytes A1) with (as_livebytes A); clear; lia|].
             split; [intros i Hi; rewrite (U3 i ltac:(clear -Hi MN; lia)), (U2 i Hi); exact (U1 i ltac:(clear -Hi MN; lia))|].
             split; [| split; [rewrite SCR'; exact LS| rewrite PCR'; exact LP]].   (* [comment removed for export] *)
             cbn [cl_errno LPA] in OWW.
             apply (frame_ok_seq (pa_owned A) (pa_owned A') (pa_owned A'') (newblk p old) (newblk r n) fp 8192 v m2 v' m3 v'' FRK FRK' PR1 PR2).
             ++ intros a Ha NB. apply MU3. rewrite unsigned_lit by exact Ha. cbn [outside app]. split; [| exact I].
                intros X. apply NB. left. split; [exact RNZ| clear -X MN; lia].
             ++ intros a Ha Pa. destruct (classic (r <= a < r + Z.min n old)) as [X|X].
                ** apply (wmono_NN _ _ _ WM3); [clear -X Gr MN; lia| exact Ha| exact Pa].
                ** rewrite (MU3 (wz a)); [exact Pa|]. rewrite unsigned_lit by exact Ha. cbn [outside app]. split; [exact X| exact I].
             ++ eapply stk_mapped_pa; [exact ST4| exact CEIL| lia| lia].
             ++ exact OWW.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End WrapR.
