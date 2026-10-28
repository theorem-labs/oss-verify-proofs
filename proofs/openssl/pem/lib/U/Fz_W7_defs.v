(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Stdio_iface Fz_iface Driver_iface Drv_kit Fz_kit Fz_W1_defs Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_lems Fz_I3_glue. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W7_perm.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).

Definition J_P7 : Z := 0xe1b74.
Definition J_F7 : Z := 0xe1bcc.
Definition J_X7 : Z := 0xe1c48.
Definition J_R7 : Z := 0xe1c54.
Definition W7_FILE : Z := 0x2f8dd.      (* [comment removed for export] *)

Section W7. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma blk_ptr_id : forall b, blk_ptr b = blk_id b.
Proof. intros b. reflexivity. Qed.

(* [comment removed for export] *)
Lemma w7_mbio_rep_off : forall (m : mem) LBall L K BI meth len max off,
  mbio_rep m LBall L K BI meth len max off -> (0 <= off <= len /\ len <= max /\ max < 2 ^ 31 - 1) /\ List.NoDup (mbio_blocks K).
Proof.
  intros m LBall L K BI meth len max off [BM MB].
  destruct MB as (BB & RP & fl & rrw & padw & nr & nw & OWNB & NDK & METH & HEAD & W1C & FLOK & TAIL & INNER).
  destruct INNER as (rmaxw & OWNbb & BBC & OWNbm & OWNrp & OFF & LENM & MAX31 & _). split; [split; [exact OFF| split; [exact LENM| exact MAX31]]| exact NDK].
Qed.

(* [comment removed for export] *)
Lemma cstate_call : forall s CLB LB L m sp tp lo B flags errv,
  RHEAP s (CLB ++ LB) m -> cl_rel CLB L -> lx_statics m -> lx_flags m flags -> rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> tp = wz RATP -> mem_inv usegs m ->
  cstate s (CLB ++ LB) LB L m sp tp lo B.
Proof.
  intros s CLB LB L m sp tp lo B flags errv HP [REL _] LXS FL AV SPB ST LO GLO ERR TP MI.
  split; [exact HP|]. split. { exists CLB. split; [apply Permutation_refl| exact REL]. }
  split. { exists errv. unfold cenv. repeat match goal with |- _ /\ _ => split end; assumption. }
  split; [exact LXS|]. split; [exact FL|]. split; [| exact GLO]. destruct LXS as (_ & _ & _ & _ & _ & _ & CI). exact CI.
Qed.

(* [comment removed for export] *)
Lemma call_exit : forall (T : bptr -> Prop) W s CLB LB L m s' LBall' L' m' sp tp lo B canary,
  cstate s' LBall' LB L' m' sp tp lo B -> cframe T W (bv_unsigned sp) s (CLB ++ LB) L m s' LBall' L' m' ->
  (forall a, rin_ivs W a -> rin_ivs LXW_CLIENT a) -> (forall b, In b LB -> ~ T (blk_id b)) ->
  RHEAP s (CLB ++ LB) m -> stderr_wfile m -> ssp_cells m canary -> B < 2 ^ 63 ->
  (cntA L' + CL_ROOM_A <= CAP_A /\ cntB L' + CL_ROOM_B <= CAP_B /\ bigsum L' + CL_ROOM_BIG <= BIG_ROOM) ->
  exists CLB' errv', Permutation LBall' (CLB' ++ LB) /\ cl_rel CLB' L'
    /\ lx_env m' s' CLB' LB sp tp B lo errv' canary
    /\ lx_pres LB (bv_unsigned sp) (LXW_CLIENT ++ [LXW_STDERR]) m m'
    /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros T W s CLB LB L m s' LBall' L' m' sp tp lo B canary (HP' & (CLB' & PERM & IDS) & (errv' & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO)
         (CFR & KP & SO & FA) HW HT HP SEW SSP HB ROOM.
  exists CLB', errv'. split; [exact PERM|]. split; [split; [exact IDS| exact ROOM]|].
  pose proof (ssp_canary_eq _ _ _ _ HP SSP) as CAN.
  split.
  { split; [exact (RHEAP_perm _ _ _ _ HP' PERM)|]. split; [exact LXS|]. split; [exact LATCH|].
    split. { eapply stderr_wfile_agree; [exact CFR| | exact SEW]. intros a Ha. right; right. unfold stderr_addr in Ha.
             split; [lia|]. split; [unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia|].
             split; [unfold LX_FLAGS; lia|]. intros X. apply HW in X. unfold LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY in X. cbn [rin_ivs fst snd] in X. lia. }
    split; [subst canary; exact (RHEAP_ssp _ _ _ HP')|].
    unfold cenv. repeat match goal with |- _ /\ _ => split end; assumption. }
  split; [| split; assumption].
  eapply cfr_lx_pres; [exact CFR| |].
  - intros b Hb. split; [apply in_or_app; right; exact Hb| exact (HT b Hb)].
  - intros a [X| ->].
    + apply HW in X. clear - X. unfold LXW_CLIENT in *. cbn [rin_ivs app] in X |- *. tauto.
    + unfold LXW_CLIENT, LXW_LIBCRYPTO, LX_FLAGS. cbn [rin_ivs app fst snd]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record w7e : Type := W7E {
  w_ra : word; w_sp : word; w_gp : word; w_tp : word; w_s0 : word; w_s1 : word; w_s2 : word; w_s3 : word; w_s4 : word; w_s5 : word; w_s6 : word; w_s7 : word;
  w_s8 : word; w_s9 : word; w_s10 : word; w_s11 : word; w_F : bvmap 5 word; w_fc : bv 32;
  w_s : PState; w_CLB : list block; w_LB : list block; w_L : @clist bptr; w_m : mem; w_lo : Z; w_B : Z;
  w_D : Z; w_d : list Z; w_pe : bptr; w_E : Z; w_enm : Z; w_LBL : list block }.
Definition w_SP (en : w7e) : Z := bv_unsigned (w_sp en).
Definition w_LBall (en : w7e) : list block := w_CLB en ++ w_LB en.
(* [comment removed for export] *)
Definition w7_saved (en : w7e) : list cell := [C8 (w_s2 en); C8 (w_s1 en); C8 (w_s0 en); C8 (w_ra en)].
(* [comment removed for export] *)
Definition mbk_ents (K : mbk) (max : Z) : @clist bptr :=
  [(k_rp K, 32); (k_bm K, 32); (k_bb K, 16); (k_bi K, 128)] ++ match k_d K with Some d => [(d, max)] | None => [] end.

Section Client.
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.

  (* [comment removed for export] *)
  Definition w7_com (en : w7e) (st : PState) (LBc : list block) (Lc : @clist bptr) (mc : mem) (ADD : @clist bptr) : Prop :=
       cstate st LBc (w_LB en) Lc mc (wz (w_SP en + -64)) (w_tp en) (w_lo en) (w_B en)
    /\ cframe (eq (w_pe en)) [] (w_SP en) (w_s en) (w_LBall en) (w_L en) (w_m en) st LBc Lc mc
    /\ libenv mc (w_LBL en) (w_E en) /\ incl_blocks (w_LBL en) (w_LBall en) /\ incl_blocks (w_LBL en) LBc /\ (forall b, In b (w_LBL en) -> blk_id b <> w_pe en)
    /\ In (w_pe en, w_E en, 904) LBc /\ In (w_pe en, w_enm en) Lc
    /\ Permutation Lc (ADD ++ w_L en)
    /\ rw_cells usegs mc (w_SP en + -32) (w7_saved en)
    /\ w_lo en <= w_SP en - LX_FUZZ_STACK /\ w_SP en <= w_B en /\ w_B en < 2 ^ 63 /\ w_SP en mod 16 = 0
    /\ In (w_pe en) (map blk_id (w_CLB en))
    /\ (cntA (w_L en) + CL_ROOM_A <= CAP_A /\ cntB (w_L en) + CL_ROOM_B <= CAP_B /\ bigsum (w_L en) + CL_ROOM_BIG <= BIG_ROOM)
    /\ payload_ok (w_m en) (w_LB en) (w_D en) (w_d en) /\ 2 <= zlength (w_d en) /\ List.NoDup (map blk_id (w_LBall en))
    /\ map blk_ptr (w_CLB en) = map fst (w_L en).

  Lemma w_pe_in : forall en, In (w_pe en) (map blk_id (w_CLB en)) -> In (w_pe en) (map blk_id (w_LBall en)).
  Proof. intros en H. unfold w_LBall. rewrite map_app. apply in_or_app. left. exact H. Qed.

  (* [comment removed for export] *)
  Lemma com7_callg : forall en st LBc Lc mc ADD (T1 : bptr -> Prop) SP1 st1 LB1 L1 m1 ADD1,
    w7_com en st LBc Lc mc ADD ->
    cstate st1 LB1 (w_LB en) L1 m1 (wz (w_SP en + -64)) (w_tp en) (w_lo en) (w_B en) ->
    cframe T1 [] SP1 st LBc Lc mc st1 LB1 L1 m1 -> SP1 <= w_SP en + -32 ->
    (forall q, In q (map blk_id (w_LBall en)) \/ In q (map fst (w_L en)) -> w_pe en <> q -> ~ T1 q) ->
    (forall b, In b (w_LBL en) -> ~ T1 (blk_id b)) ->
    libenv m1 (w_LBL en) (w_E en) -> In (w_pe en, w_E en, 904) LB1 -> In (w_pe en, w_enm en) L1 -> incl_blocks (w_LBL en) LB1 ->
    Permutation L1 (ADD1 ++ w_L en) ->
    w7_com en st1 LB1 L1 m1 ADD1.
  Proof.
    intros en st LBc Lc mc ADD T1 SP1 st1 LB1 L1 m1 ADD1 (CST & FR0 & LE & INCL0 & INCL & NPL & INE & INL & PERM & SAVED & REST) CST1 FRM1 HSP HT NTL LE1 INE1 INL1 INCL1 PERM1.
    pose proof FRM1 as (CFR1 & _).
    split; [exact CST1|]. split; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| exact HT]|].
    split; [exact LE1|]. split; [exact INCL0|]. split; [exact INCL1|]. split; [exact NPL|]. split; [exact INE1|]. split; [exact INL1|]. split; [exact PERM1|].
    split; [exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 SAVED ltac:(lia))| exact REST].
  Qed.
  (* [comment removed for export] *)
  Lemma com7_call : forall en st LBc Lc mc ADD (T1 : bptr -> Prop) st1 LB1 L1 m1 ADD1,
    w7_com en st LBc Lc mc ADD ->
    cstate st1 LB1 (w_LB en) L1 m1 (wz (w_SP en + -64)) (w_tp en) (w_lo en) (w_B en) ->
    cframe T1 [] (w_SP en + -64) st LBc Lc mc st1 LB1 L1 m1 ->
    (forall q, In q (map blk_id (w_LBall en)) \/ In q (map fst (w_L en)) -> w_pe en <> q -> ~ T1 q) ->
    (forall b, In b (w_LBL en) -> ~ T1 (blk_id b)) ->
    libenv m1 (w_LBL en) (w_E en) -> In (w_pe en, w_E en, 904) LB1 -> In (w_pe en, w_enm en) L1 -> incl_blocks (w_LBL en) LB1 ->
    Permutation L1 (ADD1 ++ w_L en) ->
    w7_com en st1 LB1 L1 m1 ADD1.
  Proof.
    intros en st LBc Lc mc ADD T1 st1 LB1 L1 m1 ADD1 COM CST1 FRM1 HT NTL LE1 INE1 INL1 INCL1 PERM1.
    eapply com7_callg; [exact COM| exact CST1| exact FRM1| lia| exact HT| exact NTL| exact LE1| exact INE1| exact INL1| exact INCL1| exact PERM1].
  Qed.

  (* [comment removed for export] *)
  Lemma com7_seg : forall en st LBc Lc mc ADD W m',
    w7_com en st LBc Lc mc ADD -> munch W mc m' -> wmono usegs mc m' -> mem_inv usegs m' -> stk usegs m' (w_lo en) (w_SP en + -64) ->
    Forall (fun iv => w_lo en <= fst iv /\ snd iv <= w_SP en + -32) W ->
    w7_com en st LBc Lc m' ADD.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros en st LBc Lc mc ADD W m' (CST & FR0 & LE & INCL0 & INCL & NPL & INE & INL & PERM & SAVED & SLO & SPB & B63 & AL16 & REST) MU WM MI' ST' HW.
    pose proof CST as (HP & _ & (errv & AV & _ & ST & LO & ERR & MI & TP) & _ & _ & _ & GLO). unfold LX_FUZZ_STACK in SLO. unfold GLOBALS_TOP in GLO.
    assert (SPR : 0 <= w_SP en < 2 ^ 64) by (pose proof (bv_unsigned_in_range _ (w_sp en)) as X; change (bv_modulus 64) with (2^64) in X; exact X).
    assert (OUT : forall a, (a < w_lo en \/ w_SP en + -32 <= a) -> outside W a).
    { intros a Ha. clear - HW Ha. induction HW as [|[x y] W0 HX HW IH]; cbn; [exact I|]. cbn in HX. split; [lia| exact IH]. }
    split. { eapply (cstate_seg W _ _ _ _ mc m' _ _ _ (w_lo en) (w_B en) (w_SP en + -32)); [exact CST| exact MU| exact WM| exact MI'| | lia| lia| | rewrite unsigned_lit by lia; exact ST'| rewrite unsigned_lit by lia; lia].
      - eapply Forall_impl; [| exact HW]. cbv beta. intros [x y] [H1 H2]. apply cwin_stack; cbn in H1, H2; lia.
      - clear - HW SLO LO GLO. induction HW as [|[x y] W0 HX HW IH]; cbn; [exact I|]. cbn in HX. unfold LX_FLAGS. split; [lia| exact IH]. }
    split. { eapply cframe_seg; [exact FR0| exact MU| exact WM| exact HP| lia|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [x y] [H1 H2]. apply cseg_ok_stack; cbn in H1, H2; lia. }
    split. { eapply libenv_agree; [exact LE|]. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|]. cbv beta. intros a Ha. apply OUT.
             destruct (libenv_fp_where _ _ Ha) as [(R & _)|(b & Hb & Rb)]; [left; lia|]. pose proof (RHEAP_block_range_proof _ _ _ b HP (INCL _ Hb)) as (_ & _ & _ & RC & _). left; lia. }
    split; [exact INCL0|]. split; [exact INCL|]. split; [exact NPL|]. split; [exact INE|]. split; [exact INL|]. split; [exact PERM|].
    split; [eapply rw_cells_transport; [exact SAVED| exact MU| exact WM| ]| split; [exact SLO| split; [exact SPB| split; [exact B63| split; [exact AL16| exact REST]]]]].
    clear - HW. induction HW as [|[x y] W0 HX HW IH]; cbn; [exact I|]. cbn in HX. split; [lia| exact IH].
  Qed.

  (* [comment removed for export] *)
  Definition w7_post (en : w7e) : nat -> @clist bptr -> PState -> machine_state -> Prop :=
    fun _ L' s' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (LBall' : list block),
         ms' = MS (mkR (w_ra en) (w_sp en) (w_gp en) (w_tp en) t0 t1 t2 (w_s0 en) (w_s1 en) (wz 0) a1 a2 a3 a4 a5 a6 a7
                       (w_s2 en) (w_s3 en) (w_s4 en) (w_s5 en) (w_s6 en) (w_s7 en) (w_s8 en) (w_s9 en) (w_s10 en) (w_s11 en) t3 t4 t5 t6)
                  (w_F en) (ret_pc (w_ra en)) (w_fc en) None m' (seg_rom usegs)
      /\ cstate s' LBall' (w_LB en) L' m' (w_sp en) (w_tp en) (w_lo en) (w_B en)
      /\ cframe (eq (w_pe en)) [] (w_SP en) (w_s en) (w_LBall en) (w_L en) (w_m en) s' LBall' L' m'
      /\ Permutation L' (w_L en) /\ libenv m' (w_LBL en) (w_E en) /\ errst_at_rest (w_E en) [] m' /\ In (w_pe en, w_E en, 904) LBall'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition X7_stmt : Prop :=
    forall (en : w7e) st LBc Lc f mc (K : mbk) (BI len max off top bot : Z) (strs : list block)
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1v s2v t3 t4 t5 t6 ol o8 o16 o24 : word),
    w7_com en st LBc Lc mc (mbk_ents K max ++ bents strs) -> (5 + length strs <= f)%nat ->
    mbio_rep mc LBc Lc K BI M_MEM len max off ->
    (forall q, In q (map blk_id (w_LBall en)) \/ In q (map fst (w_L en)) -> ~ mbio_T K q) -> (forall b, In b (w_LBL en) -> ~ mbio_T K (blk_id b)) ->
    (forall b, In b strs -> ~ mbio_T K (blk_id b)) ->
    errst_live (w_E en) top bot strs mc -> (length strs <= 2)%nat ->
    Forall (fun b => In b LBc) strs -> strs_inL Lc strs -> List.NoDup (map blk_id strs) ->
    (forall b, In b strs -> ~ (In (blk_id b) (map blk_id (w_LBall en)) \/ In (blk_id b) (map fst (w_L en)))) ->
    (forall b, In b (w_LBL en) -> ~ In (blk_id b) (map blk_id strs)) ->
    rw_cells usegs mc (w_SP en + -64) [C8 ol; C8 o8; C8 o16; C8 o24] ->
    climpl f Lc st (MS (mkR xra (wz (w_SP en + -64)) (w_gp en) (w_tp en) t0 t1 t2 (wz BI) s1v a0 a1 a2 a3 a4 a5 a6 a7
                       s2v (w_s3 en) (w_s4 en) (w_s5 en) (w_s6 en) (w_s7 en) (w_s8 en) (w_s9 en) (w_s10 en) (w_s11 en) t3 t4 t5 t6)
                 (w_F en) (wz J_X7) (w_fc en) None mc (seg_rom usegs))
      (w7_post en).
End Client.
End W7.
