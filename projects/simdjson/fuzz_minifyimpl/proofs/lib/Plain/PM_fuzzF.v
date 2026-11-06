(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import Stdio_pure DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg PIosImg PIosRegs PIosKitA PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require RMalloc_ifaceP RDriver_facts.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Malloc PState HarnessM ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PAtexit_cells RunDraw PU_iface PM_kit PM_model PM_iface PM_fzkit PM_fz1Cert PM_fz2Cert PM_fuzz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Import AxSymExec3.AX2. Import AxSymExec3Sound.AX2S. Import AxSymRun3.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.

Lemma implM_updk : forall {B} (f : PState -> PState) (k : unit -> Monad.M PState B) s Q ms,
  implM psegs (k tt) (f s) Q ms -> implM psegs (mbind (mupd f) k) s Q ms.
Proof. intros. exact H. Qed.

(* [comment removed for export] *)
Lemma img_none : forall (m : mem), mem_inv psegs m ->
  forall a : word, 0x10000 <= bv_unsigned a < 0xca000 -> m a = None.
Proof.
  intros m MI a Ha. destruct (m a) as [b|] eqn:Em; [|reflexivity]. exfalso.
  pose proof (MI a b Em) as RO. rewrite p_ro_addr in RO.
  destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.ltb_spec0 (bv_unsigned a) 0xca000); cbn in RO; try discriminate; lia.
Qed.

(* [comment removed for export] *)
Definition e1vals (sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) : list word :=
  [Z_to_bv 64 0; Z_to_bv 64 PTRUN_RET; sp; gp; Z_to_bv 64 RATP; t0; t1; t2; s0; s1; a0; a1; a2; a3; a4; a5; a6; a7;
   s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6; Z_to_bv 64 0].

(* [comment removed for export] *)
Lemma rw_cells_C1_of_bytes : forall (m : mem) A (b : byte),
  bytes_at psegs m A [b] -> wr_at psegs m A 1 -> rw_cells psegs m A [C1 b].
Proof.
  intros m A b HB HW. split; [split; [cbn; auto|]| cbn [cells_size csize Nat.add]; exact HW].
  cbn [cells_bytes cbytes app]. exact HB.
Qed.

Section Proof.
  Hypothesis ON : opnew_stmt.
  Hypothesis LAM : lam_stmt.
  Hypothesis OD : opdelete_stmt.

  (* [comment removed for export] *)
  Lemma fz1_know : forall (sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (m : mem) (lo : Z) (s : PState) (LB : list block),
    0x7fff7f804000 <= bv_unsigned sp -> bv_unsigned sp <= 2^64 - 160 -> bv_unsigned sp mod 16 = 0 ->
    stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 4096 ->
    client_img m -> RHEAP s LB m ->
    (forall a : word, 0xe17b0 <= bv_unsigned a < 0xe1890 -> m a = None) -> patexit 2 0 0 m ->
    mem_inv psegs m ->
    know_ok psegs (Env (vals_ev (e1vals sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) (fun _ => [])) m fz1_kn0.
  Proof.
    intros until LB. intros SPL SPH SPA ST LOS CI HP NONE PAT MI.
    set (E := Env _ _).
    assert (ESP : edenot E (EVar 2) = sp) by reflexivity.
    destruct CI as (CI1 & CI2 & CI3 & CI4).
    unfold patexit, patx_table, PCALL_THUNK, PAEF_GUARD in PAT. destruct PAT as (AT1 & AT2 & AT3 & AT4 & AT5).
    pose proof (rw_cells_tl _ _ _ _ _ AT1) as AT1b. cbn [csize Z.of_nat Z.add Pos.add Pos.succ] in AT1b.
    pose proof (rw_cells_tl _ _ _ _ _ AT1b) as AT1c. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat] in AT1c.
    pose proof (rw_cells_tl _ _ _ _ _ AT1c) as AT1d. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat] in AT1d.
    pose proof (rw_cells_tl _ _ _ _ _ AT2) as AT2b. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat] in AT2b.
    pose proof (rw_cells_tl _ _ _ _ _ AT2b) as AT2c. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat] in AT2c.
    pose proof (rw_cells_tl _ _ _ _ _ AT2c) as AT2d. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat] in AT2d.
    pose proof (rw_cells_tl _ _ _ _ _ AT4) as AT4b. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat] in AT4b.
    pose proof (RHEAP_need_locks _ _ _ HP) as NL. unfold RNEED_LOCKS in NL.
    unfold fz1_kn0. repeat apply Forall_cons; [ | | | | | | | | | | | | | | | | | | | | | | | apply Forall_nil].
    - apply kn_range. rewrite ESP. lia.
    - apply kn_align; [lia|]. rewrite ESP. exact SPA.
    - apply (kn_wr psegs E m (EVar 2) (-4096) 4096 (bv_unsigned sp - 4096)); try lia; [rewrite ESP; lia|].
      intros x Hx. apply (stk_wview psegs m lo (bv_unsigned sp) x ST). lia.
    - eapply kn_word_C8; [exact CI1| reflexivity].
    - eapply kn_word_C8; [exact CI2| reflexivity].
    - eapply kn_word_C8; [exact CI3| reflexivity].
    - eapply kn_word_C8; [exact CI4| reflexivity].
    - destruct NL as [[_ B] _]. apply (kn_word psegs E m _ 1 (ELit 0) _ B); [reflexivity | lia | reflexivity].
    - destruct AT1 as [[_ B] _]. cbn [cells_bytes cbytes] in B. apply bytes_at_app in B as [B _].
      apply (kn_word psegs E m _ 1 (ELit 0) _ B); [reflexivity | lia | reflexivity].
    - destruct AT1b as [[_ B] _]. cbn [cells_bytes cbytes] in B. apply bytes_at_app in B as [B _].
      apply (kn_word psegs E m _ 3 (ELit 0) _ B); [reflexivity | lia | reflexivity].
    - eapply kn_word_C4; [exact AT1c| reflexivity].
    - eapply kn_word_C4; [exact AT1d| reflexivity].
    - eapply kn_word_C8; [exact AT2| reflexivity].
    - eapply kn_word_C8; [exact AT2b| reflexivity].
    - eapply kn_word_C8; [exact AT2c| reflexivity].
    - eapply kn_word_C8; [exact AT2d| reflexivity].
    - eapply kn_word_C8; [exact AT3| reflexivity].
    - eapply kn_word_C8; [exact AT4| reflexivity].
    - eapply kn_word_C8; [exact AT4b| reflexivity].
    - eapply kn_word_C8; [exact AT5| reflexivity].
    - apply kn_img; [lia | lia |]. apply img_none. exact MI.
    - apply kn_img; [lia | lia |]. exact NONE.
    - apply (kn_wr psegs E m (ELit 0) 0xca000 0x3b000 0xca000); try lia; [rewrite edenot_lit; reflexivity|].
      intros x Hx. apply p_rw_window. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fz2_know : forall (l1 l2 : list word) (sp : word) (m1 m2 : mem) (lo A : Z) (s2 : PState) (LB : list block) p junk,
      length l1 = 33%nat -> nth 2%nat l1 (Z_to_bv 64 0) = sp -> nth 0%nat l2 (Z_to_bv 64 0) = Z_to_bv 64 A ->
      know_ok psegs (Env (vals_ev l1) (fun _ => [])) m1 (s_know fz1_ssF) ->
      rheap_pres LB (bv_unsigned sp - 336) m1 m2 ->
      stk psegs m1 lo (bv_unsigned sp) -> stk psegs m2 lo (bv_unsigned sp - 336) -> lo <= bv_unsigned sp - 16384 -> ATOP <= lo ->
      rblock_range A 8 -> rw_cells psegs m2 A [CB 8 junk] -> RHEAP s2 ((p, A, 8) :: LB) m2 ->
      mem_inv psegs m2 ->
      know_ok psegs (Env (vals_ev (l1 ++ l2)) (fun _ => [])) m2 fz2_kn0.
  Proof.
    intros l1 l2 sp m1 m2 lo A s2 LB p junk L1 HSP HA KN1 HPR ST1 ST2 LOS LOA BR BLK HP2 MI2.
    set (E1 := Env (vals_ev l1) _) in KN1. set (E2 := Env _ _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
    assert (AG : env_agree 33 E1 E2) by (rewrite <- L1; apply env_agree_app).
    assert (ESP : edenot E2 (EVar 2) = sp).
    { cbn [edenot ev E2]. unfold vals_ev. rewrite app_nth1 by (rewrite L1; lia). exact HSP. }
    assert (EA : edenot E2 (EVar 33) = Z_to_bv 64 A).
    { cbn [edenot ev E2]. unfold vals_ev. rewrite app_nth2 by (rewrite L1; lia). rewrite L1. exact HA. }
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    assert (UA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit64; lia).
    unfold fz2_kn0. apply know_ok_app.
    - (* [comment removed for export] *)
      eapply (know_ok_agree psegs 33 E1 E2); [exact AG| apply kn_vars_lt_keep; exact (scheck_k_vars _ _ _ _ _ _ _ _ _ _ _ fz1_cert)|].
      eapply know_ok_keep; [| exact KN1].
      intros x (wlo & whi & Hin & Hx). unfold fz2_KEEP in Hin. cbn [map fpwin_den] in Hin.
      change (edenot E1 (EVar 2)) with (nth 2%nat l1 (Z_to_bv 64 0)) in Hin. rewrite HSP, edenot_lit in Hin.
      change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hin.
      pose proof (bv_unsigned_in_range 64 x) as RX. unfold bv_modulus in RX. cbn in RX.
      rewrite <- (Z_to_bv_bv_unsigned x). apply (HPR (bv_unsigned x)); [lia|].
      unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP.
      cbn [In] in Hin. decompose [or] Hin; try match goal with H : (_, _) = (_, _) |- _ => injection H as <- <- end; try lia; try contradiction.
    - (* [comment removed for export] *)
      repeat apply Forall_cons; [ | | | | | | | | | apply Forall_nil].
      + apply kn_range. rewrite EA, UA. lia.
      + apply kn_align; [lia|]. rewrite EA, UA. exact BR2.
      + apply (kn_wr psegs E2 m2 (EVar 33) 0 8 A); try lia; [rewrite EA, UA; lia|].
        intros x Hx. destruct BLK as [_ W]. cbn [cells_size csize Nat.add] in W. eapply wview_of_wr_at; [exact W| lia].
      + cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite EA, UA, !edenot_lit, !unsigned_lit64 by lia. lia.
      + cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite EA, UA, ESP, !edenot_lit, !unsigned_lit64 by lia. lia.
      + apply (kn_wr psegs E2 m2 (EVar 2) (-4096) 4096 (bv_unsigned sp - 4096)); try lia; [rewrite ESP; lia|].
        intros x Hx. destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned sp - 336)) as [L|G].
        * apply (stk_wview psegs m2 lo (bv_unsigned sp - 336) x ST2). lia.
        * rewrite <- (Z_to_bv_bv_unsigned x). apply (proj2 (HPR (bv_unsigned x) ltac:(lia) ltac:(left; lia))).
          unfold wa. rewrite (Z_to_bv_bv_unsigned x). apply (stk_wview psegs m1 lo (bv_unsigned sp) x ST1). lia.
      + apply (kn_wr psegs E2 m2 (ELit 0) 0xca000 0x3b000 0xca000); try lia; [rewrite edenot_lit; reflexivity|].
        intros x Hx. apply p_rw_window. lia.
      + pose proof (RHEAP_need_locks _ _ _ HP2) as NL. unfold RNEED_LOCKS in NL. destruct NL as [[_ B] _].
        apply (kn_word psegs E2 m2 _ 1 (ELit 0) _ B); [reflexivity | lia | reflexivity].
      + apply kn_img; [lia | lia |]. apply img_none. exact MI2.
  Qed.

  (* [comment removed for export] *)
  Theorem fuzz_first : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (s : PState) (LB : list block) (D : Z) (payload : list Z) (AB lo : Z) (errv : word),
    ps_fa s = None ->
    RHEAP s LB m ->
    bytes_at psegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
    rclient_range LB (bv_unsigned sp) D (zlength payload) ->
    (forall i, 0 <= i < zlength payload -> outside client_wr (D + i)) ->
    0 < D -> D + zlength payload <= ATOP -> zlength payload < 2^26 ->
    client_static s LB m ->
    rauxv_ok m AB -> bv_unsigned sp <= AB ->
    stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PHARNESS_STACK ->
    rw_cells psegs m (errno_addr tp) [C4 errv] ->
    mem_inv psegs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP -> bv_unsigned sp mod 16 = 0 ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) ->
    ra = Z_to_bv 64 PTRUN_RET ->
    implM psegs (ProgP.fuzz_one payload) s
          (fuzz_oneU_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 PFUZZ_ENTRY) fc None m (seg_rom psegs)).
  Proof.
    intros until errv. intros FA HP DAT PLB DCR DCW D0 DTOP NLT CS AUX SPB ST LOA LOS ERR MI FZ TP SPA A0 A1 RA.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof LOS as LOS'. unfold PHARNESS_STACK in LOS. atop_facts.
    pose proof AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & AB1 & AB2 & AB3 & _).
    destruct CS as [CI CST]. rewrite FA in CST. destruct CST as [NONE PAT].
    pose proof CI as (CI1 & CI2 & CI3 & CI4).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m) as LBR.
    assert (LBB : forall b, In b LB -> 0 < blk_addr b /\ blk_addr b + blk_size b <= ATOP /\ (blk_addr b + blk_size b <= 0x10000 \/ 0x105000 <= blk_addr b)).
    { intros b Hb. destruct (LBR b HP Hb) as (R1 & _ & _ & R4 & R5). auto. }
    clear LBR.
    set (n := zlength payload) in *.
    assert (N0 : 0 <= n) by (unfold n, zlength; lia).
    (* [comment removed for export] *)
    unfold ProgP.fuzz_one, HarnessM.fuzz_one, HarnessM.client_init.
    apply implM_bind_assoc. apply implM_get_l. cbv beta. rewrite FA. apply implM_bind_assoc.
    (* [comment removed for export] *)
    apply implM_from_evt.
    set (l1 := e1vals sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
    set (E1 := Env (vals_ev l1) (fun _ => @nil byte)).
    assert (KN1 : know_ok psegs E1 m fz1_kn0).
    { apply (fz1_know sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m lo s LB);
        first [exact ST | exact CI | exact HP | exact NONE | exact PAT | exact MI | exact SPA | lia]. }
    subst ra tp.
    destruct (scheck_k_sound psegs fz1_IT 4000%nat [fz1_RET] fz1_ss0 fz1_W fz1_RET fz1_srF (s_know fz1_ssF) fz1_exports fz1_wexports fz1_IT_ok fz1_cert
                E1 m (seg_rom psegs) _ F fc (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                (regs_ok_mkR E1 fz1_sr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl) KN1 MI)
      as (R1 & m1 & MST1 & FULL1 & RO1 & MU1 & WM1 & MI1 & STKP1 & _ & _ & KNF1).
    unfold PFUZZ_ENTRY. change (Z_to_bv 64 0x3bed8) with (Z_to_bv 64 (s_pc fz1_ss0)).
    exists (MS R1 F (Z_to_bv 64 fz1_RET) fc None m1 (seg_rom psegs)). split; [exact MST1|].
    rewrite (regs_ok_canon E1 fz1_srF R1 FULL1 RO1).
    lazy [sr_get fz1_srF nth bv_eqb ridx bv_unsigned Z.eqb Z.to_nat Pos.to_nat Pos.iter_op Nat.add edenot ev E1 vals_ev l1 e1vals].   (* [comment removed for export] *)
    unfold fz1_W in MU1. cbn [map fpwin_den edenot ev E1 vals_ev l1 e1vals nth] in MU1.
    rewrite ?edenot_lit in MU1. change (bv_unsigned (Z_to_bv 64 0)) with 0 in MU1.
    rewrite (u_add_lit sp (-336)) by lia. cbn [Z.add] in MU1.
    pose proof (STKP1 _ _ ST) as ST1.
    (* [comment removed for export] *)
    assert (HP1 : RHEAP s LB m1).
    { eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU1| exact WM1|].
      constructor; [left; cbn; lia|]. constructor; [| constructor].
      right; left. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. cbn. lia. }
    assert (AUX1 : rauxv_ok m1 AB).
    { eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. repeat constructor; cbn; lia. }
    assert (ERR1 : rw_cells psegs m1 (errno_addr (Z_to_bv 64 RATP)) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. rewrite errno_lit. unfold RERRNO. cbn. lia. }
    eapply implM_bind.
    { eapply ON with (lo := lo) (B := AB) (n := 8); try reflexivity; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact AUX1 | exact MI1 | (unfold OPNEW_STACK, RMALLOC_STACK; lia) | lia
              | (eapply (proj1 (stk_split psegs m1 lo (bv_unsigned sp + -336) (bv_unsigned sp) ST1 ltac:(lia)))) | exact ERR1
              | match goal with |- ?G => idtac "LEFT:" G end ]. all: fail. }
    cbv beta. intros p sB msB PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR2 & FAE2 & SOE2 & KB).
    destruct KB as (A & junk & -> & BR & HP2 & BLK & _).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia. pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    replace (ret_pc (Z_to_bv 64 249372)) with (Z_to_bv 64 249372) by (symmetry; rpc).
    (* [comment removed for export] *)
    apply implM_updk.
    (* [comment removed for export] *)
    apply implM_from_evt.
    set (l2 := [Z_to_bv 64 A; u0; u1; u2; b1; b2; b3; b4; b5; b6; b7; u3; u4; u5; u6]).
    set (E2 := Env (vals_ev (l1 ++ l2)) (fun _ => @nil byte)).
    assert (ST2full : stk psegs m2 lo (bv_unsigned sp)).
    { eapply stk_merge; [exact ST2| | lia]. eapply rheap_pres_stk; [exact HPR2| | lia].
      exact (proj2 (stk_split psegs m1 lo (bv_unsigned sp + -336) (bv_unsigned sp) ST1 ltac:(lia))). }
    assert (KN2 : know_ok psegs E2 m2 fz2_kn0).
    { eapply (fz2_know l1 l2 sp m1 m2 lo A sB LB p junk); first [reflexivity | exact KNF1 | exact HPR2 | exact ST1 | exact ST2 | exact BR | exact BLK | exact HP2 | exact MI2 | lia]. }
    assert (RO2 : regs_ok E2 fz2_sr0 (mkR (Z_to_bv 64 249372) (Z_to_bv 64 (bv_unsigned sp + -336)) gp (Z_to_bv 64 RATP) u0 u1 u2 (Z_to_bv 64 1) (Z_to_bv 64 923664)
                                        (Z_to_bv 64 A) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 923672) (Z_to_bv 64 0) (Z_to_bv 64 2305843009213693951)
                                        (Z_to_bv 64 9223372036854775800) (Z_to_bv 64 0) s7 s8 s9 s10 s11 u3 u4 u5 u6)).
    { rewrite <- (u_add_lit sp (-336)) by lia. apply regs_ok_mkR. reflexivity. }
    destruct (scheck_sound psegs fz2_IT 4000%nat [fz2_RET] fz2_ss0 fz2_W fz2_RET fz2_srF fz2_exports fz2_wexports fz2_IT_ok fz2_cert
                E2 m2 (seg_rom psegs) _ F fc (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) RO2 KN2 MI2)
      as (R3 & m3 & MST3 & FULL3 & RO3 & MU3 & WM3 & MI3 & STKP3 & _ & WX).
    change (Z_to_bv 64 249372) with (Z_to_bv 64 (s_pc fz2_ss0)) at 2.
    exists (MS R3 F (Z_to_bv 64 fz2_RET) fc None m3 (seg_rom psegs)). split; [exact MST3|].
    rewrite (regs_ok_canon E2 fz2_srF R3 FULL3 RO3).
    lazy [sr_get fz2_srF nth bv_eqb ridx bv_unsigned Z.eqb Z.to_nat Pos.to_nat Pos.iter_op Nat.add edenot ev E2 vals_ev l1 l2 e1vals app].
    rewrite (u_add_lit sp (-208)) by lia.
    unfold fz2_W in MU3. cbn [map fpwin_den edenot ev E2 vals_ev l1 l2 e1vals app nth] in MU3.
    rewrite ?edenot_lit, ?(unsigned_lit64 A) in MU3 by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0 in MU3. cbn [Z.add] in MU3.
    unfold fz2_wexports in WX.
    (* [comment removed for export] *)
    apply Forall_cons_iff in WX as [XF0 WX]. apply Forall_cons_iff in WX as [XF1 WX]. apply Forall_cons_iff in WX as [XF2 WX].
    apply Forall_cons_iff in WX as [XF3 WX]. apply Forall_cons_iff in WX as [XF4 WX]. apply Forall_cons_iff in WX as [XF5 WX].
    apply Forall_cons_iff in WX as [XF6 WX]. apply Forall_cons_iff in WX as [XF7 WX]. apply Forall_cons_iff in WX as [XF8 WX].
    apply Forall_cons_iff in WX as [XF9 WX]. apply Forall_cons_iff in WX as [XP WX].
    apply Forall_cons_iff in WX as [XG0 WX]. apply Forall_cons_iff in WX as [XG1 WX].
    apply Forall_cons_iff in WX as [XV0 WX]. apply Forall_cons_iff in WX as [XV1 WX]. apply Forall_cons_iff in WX as [XV2 WX].
    apply Forall_cons_iff in WX as [XVT WX].
    apply Forall_cons_iff in WX as [XA0 WX]. apply Forall_cons_iff in WX as [XA1 WX]. apply Forall_cons_iff in WX as [XA2 WX].
    apply Forall_cons_iff in WX as [XA3 WX]. apply Forall_cons_iff in WX as [XA4 WX]. apply Forall_cons_iff in WX as [XA5 WX].
    apply Forall_cons_iff in WX as [XA6 WX]. apply Forall_cons_iff in WX as [XA7 WX]. apply Forall_cons_iff in WX as [XA8 WX].
    apply Forall_cons_iff in WX as [XA9 WX]. apply Forall_cons_iff in WX as [XA10 WX]. apply Forall_cons_iff in WX as [XA11 WX]. clear WX.
    cbn [wexp_den edenot ev E2 vals_ev l1 l2 e1vals app nth] in XF0, XF1, XF2, XF3, XF4, XF5, XF6, XF7, XF8, XF9, XP, XG0, XG1, XV0, XV1, XV2, XVT.
    cbn [wexp_den edenot ev E2 vals_ev l1 l2 e1vals app nth] in XA0, XA1, XA2, XA3, XA4, XA5, XA6, XA7, XA8, XA9, XA10, XA11.
    rewrite ?edenot_lit in XF9, XP, XG0, XG1, XV0, XV1, XV2, XVT. rewrite ?edenot_lit in XA0, XA1, XA2, XA3, XA4, XA5, XA6, XA7, XA8, XA9, XA10, XA11.
    change (bv_unsigned (Z_to_bv 64 0)) with 0 in *.
    rewrite (u_add_lit (Z_to_bv 64 A) 8) in XV1 by (rewrite (unsigned_lit64 A); lia). rewrite (unsigned_lit64 A) in XV1 by lia.
    rewrite (u_add_lit (Z_to_bv 64 A) 8) in XV2 by (rewrite (unsigned_lit64 A); lia). rewrite (unsigned_lit64 A) in XV2 by lia.
    rewrite (unsigned_lit64 A) in XP by lia. rewrite Z.add_0_r in XP.
    cbv [Z.add] in XG0, XG1, XV0, XVT, XA0, XA1, XA2, XA3, XA4, XA5, XA6, XA7, XA8, XA9, XA10, XA11.   (* [comment removed for export] *)
    rewrite Z.add_0_l in XV1. rewrite Z.add_0_l in XV2.
    pose proof (STKP3 _ _ ST2full) as ST3.
    (* [comment removed for export] *)
    assert (ADISJ : forall b, In b LB -> A + 8 <= blk_addr b \/ blk_addr b + blk_size b <= A).
    { intros b Hb. exact (new_block_disj _ _ _ _ _ _ b HP2 Hb). }
    (* [comment removed for export] *)
    assert (HPRE : harness_pres LB (bv_unsigned sp) m m3).
    { intros a Ha Hc Hw. unfold client_wr in Hw. cbn [outside] in Hw.
      assert (O1 : outside [(bv_unsigned sp + -4096, bv_unsigned sp + 0); (923568, 923792)] a).
      { clear - Ha Hc Hw LBB LOA LOS ATOPR. cbn. destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia| pose proof (LBB bq Hb); lia]. }
      assert (O3 : outside [(bv_unsigned sp + -4096, bv_unsigned sp + 0); (A + 0, A + 8); (923568, 923570); (923576, 923600); (1063544, 1063548); (1063584, 1063592); (1063840, 1063848)] a).
      { clear - Ha Hc Hw LBB LOA LOS ATOPR ADISJ BR1 BR4 BR5. cbn. destruct Hc as [Hc|[Hc|(bq & Hb & Hr)]]; [lia| unfold ralloc_static in Hc; lia| pose proof (LBB bq Hb); pose proof (ADISJ bq Hb); lia]. }
      assert (E1q : m1 (wa a) = m (wa a)) by (apply MU1; unfold wa; rewrite unsigned_lit by lia; exact O1).
      destruct (HPR2 a Ha ltac:(destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc])) as [E2q W2q].
      assert (E3q : m3 (wa a) = m2 (wa a)) by (apply MU3; unfold wa; rewrite unsigned_lit by lia; exact O3).
      split; [congruence| intros Hv; apply WM3, W2q, WM1, Hv]. }
    assert (AGR : magree psegs (fun a => rclient_addr LB (bv_unsigned sp) a /\ outside client_wr a) m m3).
    { intros a Ha [Hc Hw]. exact (HPRE a Ha Hc Hw). }
    (* [comment removed for export] *)
    assert (WRS : forall X k, 0xca000 <= X -> X + k <= 0x105000 -> wr_at psegs m3 X k).
    { intros X k H1 H2. apply (wr_at_window psegs m3 0xca000 0x105000 X k); try lia. intros x Hx. apply p_rw_window. exact Hx. }
    assert (WRF : forall X k, lo <= X -> X + k <= bv_unsigned sp -> wr_at psegs m3 X k).
    { intros X k H1 H2. exact (wr_at_of_stk psegs m3 lo (bv_unsigned sp) X k ST3 H1 H2). }
    assert (WRB : wr_at psegs m3 A 8).
    { destruct BLK as [_ W]. cbn [cells_size csize Nat.add] in W. destruct W as (W1 & W2 & W3).
      split; [lia|]. split; [lia|]. intros i Hi. apply WM3. apply W3. exact Hi. }
    (* [comment removed for export] *)
    subst a0 a1.
    eapply (fuzz_join LAM OD) with (p := p) (V := A) (s0' := s) (LB0 := LB) (m0 := m) (lo := lo) (AB := AB);
      rewrite ?unsigned_lit by lia;
      first [ exact PLB | exact DCR | exact D0 | exact DTOP | exact NLT | exact MI3 | exact FZ | exact SPA | exact SPB | exact LOA | exact LOS'
            | match goal with |- ?G => idtac "LEFT:" G end ].
    - (* [comment removed for export] *)
      eapply RHEAP_ext; [| reflexivity| reflexivity].
      eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP2| exact MU3| exact WM3|].
      unfold rclient_write_ok, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP.
      constructor; [cbn [fst snd]; left; lia|].
      constructor; [cbn [fst snd]; right; right; exists (p, A, 8); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
      repeat (constructor; [cbn [fst snd]; right; left; lia|]). constructor.
    - left; reflexivity.
    - reflexivity.
    - (* [comment removed for export] *)
      split; [exact HPRE|]. split; [cbn; exact SOE2|]. split; [intros b Hb; right; exact Hb|]. rewrite FA. exists p, A. split; reflexivity.
    - (* [comment removed for export] *)
      eapply bytes_at_magree; [exact AGR| exact DAT|]. intros a Ha. rewrite length_map in Ha. change (Z.of_nat (length payload)) with n in Ha. split.
      + clear - Ha DCR. destruct DCR as [H|[H|(bq & Hb & Hr)]]; [left; lia| right; left; unfold ralloc_static; lia| right; right; exists bq; split; [exact Hb| lia]].
      + replace a with (D + (a - D)) by lia. apply DCW. lia.
    - (* [comment removed for export] *)
      unfold client_img.
      repeat match goal with |- _ /\ _ => split end;
        (eapply rw_cells_magree; [exact AGR| eassumption|]; intros a Ha; cbn in Ha;
         split; [right; left; split; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP; lia]| cbn; lia]).
    - (* [comment removed for export] *)
      apply rw_cells_C8_of_bytes; [exact XP| exact WRB].
    - (* [comment removed for export] *)
      unfold PVEC_GUARD, guard1. change (word_to_le_bytes 1 (Z_to_bv 64 1)) with [Z_to_bv 8 1] in XG0, XG1.
      apply rw_cells_cons; [apply rw_cells_C1_of_bytes; [exact XG0| apply WRS; lia]|]. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat].
      apply rw_cells_C1_of_bytes; [exact XG1| apply WRS; lia].
    - (* [comment removed for export] *)
      unfold PVEC. apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XV0| apply WRS; lia]|]. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat].
      apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XV1| apply WRS; lia]|]. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat].
      apply rw_cells_C8_of_bytes; [exact XV2| apply WRS; lia].
    - (* [comment removed for export] *)
      unfold PFALLBACK, PFALLBACK_VT. apply rw_cells_C8_of_bytes; [exact XVT| apply WRS; lia].
    - (* [comment removed for export] *)
      unfold patexit, patx_table, PCALL_THUNK, PAEF_GUARD, PDTOR_THUNK, PVEC.
      change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in XA0.
      change (word_to_le_bytes 3 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 3) in XA1.
      split.
      { apply rw_cells_cons; [apply rw_cells_C1_of_bytes; [exact XA0| apply WRS; lia]|]. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat].
        apply rw_cells_cons; [apply (rw_cells_CB_of_bytes psegs m3 1063537 (repeat (Z_to_bv 8 0) 3)); [exact XA1| apply WRS; cbn; lia]|]. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat].
        apply rw_cells_cons; [apply rw_cells_C4_of_bytes; [exact XA2| apply WRS; lia]|]. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat].
        apply rw_cells_C4_of_bytes; [exact XA3| apply WRS; lia]. }
      split.
      { apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XA4| apply WRS; lia]|]. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat].
        apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XA5| apply WRS; lia]|]. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat].
        apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XA6| apply WRS; lia]|]. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat].
        apply rw_cells_C8_of_bytes; [exact XA7| apply WRS; lia]. }
      split; [apply rw_cells_C8_of_bytes; [exact XA8| apply WRS; lia]|].
      split.
      { apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XA9| apply WRS; lia]|]. cbn [csize Z.of_nat Z.add Pos.add Pos.succ Pos.of_succ_nat].
        apply rw_cells_C8_of_bytes; [exact XA10| apply WRS; lia]. }
      apply rw_cells_C8_of_bytes; [exact XA11| apply WRS; lia].
    - (* [comment removed for export] *)
      eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL.
      repeat (constructor; [cbn [fst snd]; lia|]). constructor.
    - (* [comment removed for export] *)
      exact (proj1 (stk_split psegs m3 lo (bv_unsigned sp + -80) (bv_unsigned sp) ST3 ltac:(lia))).
    - (* [comment removed for export] *)
      apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XF0| apply WRF; lia]|]. cbn [csize Z.of_nat]. replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) by lia.
      apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XF1| apply WRF; lia]|]. cbn [csize Z.of_nat]. replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) by lia.
      apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XF2| apply WRF; lia]|]. cbn [csize Z.of_nat]. replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) by lia.
      apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XF3| apply WRF; lia]|]. cbn [csize Z.of_nat]. replace (bv_unsigned sp + -56 + 8) with (bv_unsigned sp + -48) by lia.
      apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XF4| apply WRF; lia]|]. cbn [csize Z.of_nat]. replace (bv_unsigned sp + -48 + 8) with (bv_unsigned sp + -40) by lia.
      apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XF5| apply WRF; lia]|]. cbn [csize Z.of_nat]. replace (bv_unsigned sp + -40 + 8) with (bv_unsigned sp + -32) by lia.
      apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XF6| apply WRF; lia]|]. cbn [csize Z.of_nat]. replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) by lia.
      apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XF7| apply WRF; lia]|]. cbn [csize Z.of_nat]. replace (bv_unsigned sp + -24 + 8) with (bv_unsigned sp + -16) by lia.
      apply rw_cells_cons; [apply rw_cells_C8_of_bytes; [exact XF8| apply WRF; lia]|]. cbn [csize Z.of_nat]. replace (bv_unsigned sp + -16 + 8) with (bv_unsigned sp + -8) by lia.
      unfold PTRUN_RET. apply rw_cells_C8_of_bytes; [exact XF9| apply WRF; lia].
    - (* [comment removed for export] *)
      eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]. rewrite errno_lit. unfold RERRNO. cbn. lia.
    - reflexivity.
  Qed.
End Proof.
End CANSEC1.
