(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface I_asan_memset AU_rt AH_memcpy0.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import ShadowTac APC_kit APC_kit2 APC_kit3 APC_kit4 APC_docalloc APC_setcap APC_setdepth APC_active APC_create APC_dtor APC_memcmp APC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import A2Lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import APC_pid0.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Section CANSEC1. Context {rc : runConstT}.
Lemma rw_cells_C2_C1 : forall m A, rw_cells bsegs m A [C2 (Z_to_bv 64 0)] -> rw_cells bsegs m A [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.
(* [comment removed for export] *)
Lemma aimpl_split : forall m AIM p1 p2 pad ASI cap AOC AIA, rw_cells bsegs m AIM (aimpl_cells p1 p2 pad ASI cap AOC AIA) ->
  rw_cells bsegs m AIM [C8 (Z_to_bv 64 AVTAB_DOM)] /\ rw_cells bsegs m (AIM + 8) [C4 (Z_to_bv 64 0)] /\ rw_cells bsegs m (AIM + 12) [CB 4 p1]
  /\ rw_cells bsegs m (AIM + 16) [C8 (Z_to_bv 64 ASI)] /\ rw_cells bsegs m (AIM + 24) [C4 (Z_to_bv 64 0)] /\ rw_cells bsegs m (AIM + 28) [CB 4 p2]
  /\ rw_cells bsegs m (AIM + 32) [C8 (Z_to_bv 64 cap)] /\ rw_cells bsegs m (AIM + 40) [C8 (Z_to_bv 64 MAX_DEPTH)]
  /\ rw_cells bsegs m (AIM + 48) [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m (AIM + 49) [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m (AIM + 50) [CB 6 pad]
  /\ rw_cells bsegs m (AIM + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m AIM p1 p2 pad ASI cap AOC AIA H. unfold aimpl_cells in H.
  Local Ltac cut1 H A B := destruct (rw_cells_cut bsegs _ _ _ 1 H) as [A B];
    cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in A, B; clear H.
  cut1 H H0 H1. cut1 H1 H8 H2. cut1 H2 H12 H3. cut1 H3 H16 H4. cut1 H4 H24 H5. cut1 H5 H28 H6. cut1 H6 H32 H7. cut1 H7 H40 H9.
  cut1 H9 H48 H10. cut1 H10 H50 H56. apply rw_cells_C2_C1 in H48.
  destruct (rw_cells_cut bsegs _ _ _ 1 H48) as [H48a H49]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H48a, H49.
  Local Ltac scell := match goal with |- rw_cells _ _ ?A ?cs =>
    first [ assumption | match goal with H : rw_cells _ _ ?B cs |- _ => replace A with B by lia; exact H end ] end.
  do 11 (split; [scell|]). scell.
Qed.
Lemma u8_lit : forall q, 0 <= q < 256 -> bv_unsigned (Z_to_bv 8 q) = q.
Proof. intros q H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Lemma memcmp_res_bound : forall l1 l2, -255 <= memcmp_res l1 l2 <= 255.
Proof.
  induction l1 as [|x r1 IH]; intros [|y r2]; cbn [memcmp_res]; try lia.
  pose proof (bv_unsigned_in_range 8 x) as Rx. pose proof (bv_unsigned_in_range 8 y) as Ry. unfold bv_modulus in Rx, Ry. cbn in Rx, Ry.
  destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)); [apply IH| lia].
Qed.
(* [comment removed for export] *)
Lemma bom_res : forall q0 q1 q2, 0 <= q0 < 256 -> 0 <= q1 < 256 -> 0 <= q2 < 256 ->
  (memcmp_res [Z_to_bv 8 q0; Z_to_bv 8 q1; Z_to_bv 8 q2] [Z_to_bv 8 239; Z_to_bv 8 187; Z_to_bv 8 191] = 0 <-> (q0 = 239 /\ q1 = 187 /\ q2 = 191)).
Proof.
  intros q0 q1 q2 H0 H1 H2. cbn [memcmp_res]. rewrite !u8_lit by lia.
  destruct (Z.eqb_spec q0 239); [destruct (Z.eqb_spec q1 187); [destruct (Z.eqb_spec q2 191)|]|]; lia.
Qed.
(* [comment removed for export] *)
Lemma res_nonzero_reg : forall r, -255 <= r <= 255 -> r <> 0 -> bv_unsigned (Z_to_bv 64 r) <> 0.
Proof.
  intros r H N. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn.
  destruct (Z_le_gt_dec 0 r); [rewrite Z.mod_small by lia; lia|].
  rewrite Z.mod_eq by lia. intro E. assert (Q : r / 18446744073709551616 = -1) by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma pid_sizesA : forall len, 0 <= len <= 2^20 - 64 ->
  4 * len + 36 <= SIDX_BYTES len /\ TAPE_BYTES len mod 8 = 0 /\ 8 * (len + 3) <= TAPE_BYTES len <= 2^27
  /\ 5 * len + 182 <= 3 * SB_BYTES len /\ len + 60 <= SB_BYTES len <= 2^24.
Proof.
  intros len H. assert (C : 32 <= CAP len <= 2^20) by (unfold CAP; lia).
  pose proof (ROUNDUP64_bounds (CAP len) ltac:(lia)) as R1. pose proof (ROUNDUP64_bounds (CAP len + 3) ltac:(lia)) as R2.
  pose proof (Z.div_mod (CAP len) 3 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (CAP len) 3 ltac:(lia)) as M3.
  pose proof (ROUNDUP64_bounds (5 * (CAP len / 3) + 64) ltac:(lia)) as R3.
  unfold SIDX_BYTES, TAPE_BYTES, SB_BYTES. split; [unfold CAP in *; lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
  split; [unfold CAP in *; lia|]. split; [unfold CAP in *; lia| unfold CAP in *; lia].
Qed.

(* [comment removed for export] *)
Lemma sidx_40 : forall len, 0 <= len -> 40 <= SIDX_BYTES len.
Proof. intros len H. pose proof (ROUNDUP64_bounds (CAP len) ltac:(unfold CAP; lia)) as R1. unfold SIDX_BYTES, CAP in *. lia. Qed.

Lemma nodup_app_disjA : forall (T : Type) (l1 l2 : list T) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros T l1 l2 x N H1 H2. induction l1 as [|y l1 IH]; [destruct H1|]. cbn in N. apply NoDup_cons_iff in N as [Ny N].
  destruct H1 as [<-|H1]; [apply Ny; apply in_or_app; right; exact H2| exact (IH N H1)].
Qed.

(* [comment removed for export] *)
Lemma parse_win_out : forall a THIS ASI len' TPA ntp SBA nsb AOC AIA nsi,
  4 * len' + 36 <= nsi ->
  (~ (THIS <= a < THIS + 96) \/ (THIS <= a < THIS + 8) \/ (THIS + 12 <= a < THIS + 24) \/ (THIS + 28 <= a < THIS + 72)) ->
  ~ (ASI <= a < ASI + nsi) -> ~ (TPA <= a < TPA + ntp) -> ~ (SBA <= a < SBA + nsb) -> ~ (AOC <= a < AOC + 8192) -> ~ (AIA <= a < AIA + 1024) ->
  outside (parse_winA THIS ASI len' TPA ntp SBA nsb AOC AIA) a.
Proof. intros. unfold parse_winA. cbn [outside]. lia. Qed.

(* [comment removed for export] *)
Lemma uchain_keepR : forall m m' top pc prev R k tr jr,
  uchain m top pc prev R k tr ->
  (forall a, R - 16 <= a < top -> a < R \/ R + 24 <= a -> m' (wa a) = m (wa a)) ->
  rw_cells bsegs m R [CB 24 jr] -> rw_cells bsegs m' R [CB 24 jr] -> 0x671000 <= R -> R + 24 <= 2^64 ->
  uchain m' top pc prev R k tr.
Proof.
  intros m m' top pc prev R k tr jr H HE C C' H0 H1. eapply uchain_frame; [exact H|]. intros a Ha.
  destruct (Z_lt_ge_dec a R) as [Hl|Hl]; [apply HE; lia|]. destruct (Z_lt_ge_dec a (R + 24)) as [Hh|Hh]; [|apply HE; lia].
  pose proof (rw_cells_bytes_at _ _ _ _ C) as (_ & _ & B). pose proof (rw_cells_bytes_at _ _ _ _ C') as (_ & _ & B').
  cbn [cells_bytes cbytes] in B, B'. rewrite app_nil_r in B, B'.
  assert (LJ : length jr = 24%nat) by (destruct C as [[Hw _] _]; cbn in Hw; tauto).
  assert (Hi : (Z.to_nat (a - R) < length jr)%nat) by (rewrite LJ; lia).
  specialize (B (Z.to_nat (a - R)) Hi). specialize (B' (Z.to_nat (a - R)) Hi). rewrite Z2Nat.id in B, B' by lia.
  replace (R + (a - R)) with a in B, B' by lia.
  rewrite ref_mrd_overlay in B by (unfold wa; rewrite unsigned_lit by lia; lia).
  rewrite ref_mrd_overlay in B' by (unfold wa; rewrite unsigned_lit by lia; lia).
  rewrite B, B'. reflexivity.
Qed.

Section Mid.
  Variable AI : AMallocIface.
  (* [comment removed for export] *)
  Lemma mid_blk_not_client : forall L RNG st l1 LB m p A n SP a, AHEAP AI L RNG st (l1 ++ LB) m -> In (HB p A n) l1 -> ATOP <= SP ->
    aclient_addr (aci AI) LB SP a -> ~ (A <= a < A + n).
  Proof.
    intros L RNG st l1 LB m p A n SP a AH HIN HS Hc.
    eapply (removed_not_client AI L RNG st (l1 ++ LB) m p A n LB SP a AH (in_or_app _ _ _ (or_introl HIN))); [| exact HS| exact Hc].
    intros b Hb. split; [apply in_or_app; right; exact Hb|]. intros ->.
    pose proof (AI_hb_ids AI _ _ _ _ _ AH) as ND. rewrite hb_ids_app in ND.
    exact (nodup_app_disjA _ _ _ p ND (hb_ids_in _ _ _ _ HIN) (hb_ids_in _ _ _ _ Hb)).
  Qed.
End Mid.

Section St1.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  Local Ltac pick_in := (left; reflexivity) + (right; pick_in).
  Local Ltac in_cr := apply IMG_CI; unfold client_ranges; pick_in.
  Lemma client_static1_W : forall LB SP W mx my, aheap_pres_W CI LB SP W mx my ->
    Forall (fun iv => snd iv <= 0x64dd80 \/ 0x64de82 <= fst iv) W -> client_static1 mx -> client_static1 my.
  Proof.
    intros LB SP W mx my PW FW CS. unfold client_static1, AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, fallback_cells, guard1 in *.
    destruct CS as (C1' & C2 & C3 & C4').
    assert (OW : forall a, 0x64dd80 <= a < 0x64de82 -> outside W a).
    { intros a Ha. clear - FW Ha. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|].
      inversion FW as [|? ? F1 FW']; subst. cbn [fst snd] in F1. split; [lia| exact (IH FW')]. }
    (split; [| split; [| split]]); (eapply aheap_pres_W_rw_cells; [exact PW| eassumption| |
      intros a Ha; apply OW; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; lia]);
      left; right; left; eexists; (split; [in_cr| cbn; lia]).
  Qed.
End St1.

End CANSEC1.


(* [comment removed for export] *)
Ltac trWC PW INF IMGCI PRN :=
  lazymatch type of PW with aheap_pres_W _ ?L ?SP ?W ?mo ?mn =>
  repeat match goal with
  | H : rw_cells bsegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells bsegs mn A cs)
                by (eapply aheap_pres_W_rw_cells; [exact PW| exact H| acrC INF IMGCI PRN|
                    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
                    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; unfold parse_winA; cbn [outside]; revert Ha; PRN (); lia]);
              clear H; rename H' into H
            | lazymatch type of H with ?T => change (skippedB T) in H end ]
  end end; repeat match goal with H : skippedB _ |- _ => unfold skippedB in H end.
(* [comment removed for export] *)
Ltac prnB := ltac2:(Control.enter (fun () => keep_only [@LOA; @LOS; @LEN0; @DL; @CAPR; @FK2; @FKB3; @FKB2; @FK1; @FKH; @RP; @RSPR; @R47; @PR0; @R8; @P8; @RSP; @STOP; @LY3; @bFr; @bFhi; @bFlo;
  @SB; @SB0; @SB1; @SB2; @SB3; @SB4; @SB5; @SB6; @SB7; @SB8; @SB9;
  @BRM1; @BRM2; @BRM3; @BRM4; @BRI1; @BRI2; @BRI3; @BRI4; @BRO1; @BRO2; @BRO3; @BRO4; @BRA1; @BRA2; @BRA3; @BRA4;
  @BRS1; @BRS2; @BRS3; @BRS4; @BRT1; @BRT2; @BRT3; @BRT4; @BRC1; @BRC2; @BRC3; @BRC4; @bCr; @bChi; @bClo; @DJM; @DJF; @DJP; @DJMF;
  @bMr; @bMhi; @bMlo; @KC; @SBM0; @SBM48])).


(* [comment removed for export] *)
Ltac prnC := ltac2:(Control.enter (fun () => keep_only [@LOA; @LOS; @LEN0; @DL; @CAPR; @FK2; @FKB3; @FKB2; @FK1; @FKH; @RP; @RSPR; @R47; @PR0; @R8; @P8; @RSP; @STOP; @LY3; @bFr; @bFhi; @bFlo;
  @SB; @SB0; @SB1; @SB2; @SB3; @SB4; @SB5; @SB6; @SB7; @SB8; @SB9;
  @BRM1; @BRM2; @BRM3; @BRM4; @BRI1; @BRI2; @BRI3; @BRI4; @BRO1; @BRO2; @BRO3; @BRO4; @BRA1; @BRA2; @BRA3; @BRA4;
  @BRS1; @BRS2; @BRS3; @BRS4; @BRT1; @BRT2; @BRT3; @BRT4; @BRC1; @BRC2; @BRC3; @BRC4; @bCr; @bChi; @bClo; @DJM; @DJF; @DJP; @DJMF;
  @bMr; @bMhi; @bMlo; @KC; @SBM0; @SBM48;
  @bIr; @bIhi; @bIlo; @bTr; @bThi; @bTlo; @bSr; @bShi; @bSlo; @bOr; @bOhi; @bOlo; @bAr; @bAhi; @bAlo;
  @DJIF; @DJTF; @DJSF; @DJOF; @DJAF; @DJIM; @DJTM; @DJSM; @DJOM; @DJAM; @SZ1; @SZ2; @SZ3; @SZ4; @SZ5; @ZD])).

(* [comment removed for export] *)
Definition hidR (P : Prop) : Prop := P.
From Ltac2 Require Import Ltac2.
Ltac2 is_rng (t : constr) : bool := lazy_match! t with | rng _ _ _ => true | _ => false end.
Ltac2 only_rng (keep : ident list) : unit :=
  List.iter (fun h => let (id, body, ty) := h in
    match body with
    | Some _ => ()
    | None =>
        if List.exist (fun k => Ident.equal k id) keep then ()
        else if is_rng ty then ltac1:(h t |- change (hidR t) in h) (Ltac1.of_ident id) (Ltac1.of_constr ty) else ()
    end) (Control.hyps ()).
Ltac unhide_rng := repeat match goal with H : hidR _ |- _ => unfold hidR in H end.
#[global] Set Default Proof Mode "Classic".
