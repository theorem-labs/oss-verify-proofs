(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude DecodeC Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import F_strlen Cs_pad
     Fz_M_malloc Fz_M_free Fz_M_secure Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_growc Fz_W1_writec Fz_W1_read Fz_W3_iface Fz_W2_rep Fz_W2_puts Fz_W2_writeg Fz_W3_defs Fz_W3_lems. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W7_perm. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W7_defs Fz_W7_f Fz_W7_w.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

(* [comment removed for export] *)
Lemma first_nul : forall bs : list byte, In (Z_to_bv 8 0) bs -> exists str rest, bs = str ++ Z_to_bv 8 0 :: rest /\ ~ In (Z_to_bv 8 0) str.
Proof.
  induction bs as [|c bs IH]; intros H; [destruct H|].
  destruct (base.decide (c = Z_to_bv 8 0)) as [->|NE].
  - exists [], bs. split; [reflexivity| intros []].
  - destruct H as [E|H]; [exfalso; exact (NE E)|]. destruct (IH H) as (str & rest & -> & NI). exists (c :: str), rest. split; [reflexivity|].
    intros [E|X]; [exact (NE E)| exact (NI X)].
Qed.

(* [comment removed for export] *)
Lemma sextw_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 0) = z.
Proof.
  intros z Hz. rewrite unsigned_lit by lia. rewrite Z.add_0_r.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Definition J_PW3 : Z := 0xe1b9c.
Definition J_PW4 : Z := 0xe1bbc.

Section W7. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.
  Variable errst_fp : Z -> list block -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).
  Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
  Local Notation f7_invI := (f7_inv libenv errst_live).

  (* [comment removed for export] *)
  Definition pw_inv (en : w7e) (st : PState) (LBc : list block) (Lc : @clist bptr) (mc : mem)
      (K : mbk) (BI len max off top bot blen bof : Z) (strs : list block) (qd qh qn : bptr) (DT dlen HD nh NM nn : Z) (bd bh bn : list byte) : Prop :=
       f7_invI en st LBc Lc mc K BI len max off top bot strs [(qd, DT, dlen); (qh, HD, nh); (qn, NM, nn)]
    /\ rw_cells usegs mc (w_SP en + -64) [C8 (wz dlen); C8 (wz DT); C8 (wz HD); C8 (wz NM)]
    /\ 1 <= nn <= 255 /\ 1 <= nh < 2 ^ 31 /\ 1 <= dlen < 2 ^ 31
    /\ length bn = Z.to_nat nn /\ rw_cells usegs mc NM [CB (Z.to_nat nn) bn] /\ In (Z_to_bv 8 0) bn
    /\ length bh = Z.to_nat nh /\ rw_cells usegs mc HD [CB (Z.to_nat nh) bh] /\ nth_error bh (Z.to_nat (nh - 1)) = Some (Z_to_bv 8 0)
    /\ length bd = Z.to_nat dlen /\ rw_cells usegs mc DT [CB (Z.to_nat dlen) bd]
    /\ Forall (fun b => blk_size b <= 64) strs
    /\ blen = zlength (w_d en) - 1 /\ 0 <= bof <= blen /\ nn + nh + dlen <= 2 * bof + 256.

  (* [comment removed for export] *)
  Lemma pw_news : forall en st LBc Lc mc K BI len max off top bot strs qd qh qn DT dlen HD nh NM nn,
    f7_invI en st LBc Lc mc K BI len max off top bot strs [(qd, DT, dlen); (qh, HD, nh); (qn, NM, nn)] ->
    (In (qd, DT, dlen) LBc /\ ~ mbio_T K qd) /\ (In (qh, HD, nh) LBc /\ ~ mbio_T K qh) /\ (In (qn, NM, nn) LBc /\ ~ mbio_T K qn)
    /\ In (qd, dlen) Lc /\ In (qh, nh) Lc /\ In (qn, nn) Lc.
  Proof.
    intros en st LBc Lc mc K BI len max off top bot strs qd qh qn DT dlen HD nh NM nn (_ & _ & _ & _ & _ & _ & NWS & _ & _ & KS & _).
    pose proof (proj1 (Forall_forall _ _) NWS) as NW. cbn [In] in NW.
    assert (KS' : forall b, In b [(qd, DT, dlen); (qh, HD, nh); (qn, NM, nn)] -> ~ mbio_T K (blk_id b)) by (intros b Hb; apply KS; apply in_or_app; right; exact Hb). cbn [In] in KS'.
    split; [split; [apply NW; tauto| apply (KS' (qd, DT, dlen)); tauto]|]. split; [split; [apply NW; tauto| apply (KS' (qh, HD, nh)); tauto]|].
    split; [split; [apply NW; tauto| apply (KS' (qn, NM, nn)); tauto]|].
    split; [apply (NW (qd, DT, dlen)); tauto|]. split; [apply (NW (qh, HD, nh)); tauto| apply (NW (qn, NM, nn)); tauto].
  Qed.

  (* [comment removed for export] *)
  Lemma pw_keep : forall en st LBc Lc mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn st1 m1,
    pw_inv en st LBc Lc mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn ->
    cstate st1 LBc (w_LB en) Lc m1 (wz (w_SP en + -64)) (w_tp en) (w_lo en) (w_B en) ->
    cframe (fun _ => False) [] (w_SP en + -64) st LBc Lc mc st1 LBc Lc m1 ->
    pw_inv en st1 LBc Lc m1 K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn.
  Proof.
    intros en st LBc Lc mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn st1 m1
           (INV & LOC & NN & NH & DLEN & LBN & NMC & NUL & LBH & HDC & NULH & LBD & DTC & SSZ & EBLEN & BOF & NSZ) CST1 FRM1.
    pose proof (pw_news _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as ([INd _] & [INh _] & [INn _] & _).
    pose proof FRM1 as (CFR1 & _).
    assert (FRM1' : cframe (oT None) [] (w_SP en + -64) st LBc Lc mc st1 LBc Lc m1) by (eapply cframe_weakT; [exact FRM1| intros q []]).
    pose proof (f7_step libenv libenv_fp libenv_agree libenv_fp_where errst_live errst_fp errst_live_agree errst_fp_where
                  _ _ _ _ _ _ _ _ _ _ _ _ _ [(qd, DT, dlen); (qh, HD, nh); (qn, NM, nn)] [] None _ _ _ _ ltac:(cbn [olist app]; exact INV) CST1 FRM1' ltac:(split; reflexivity)) as INV1.
    rewrite app_nil_r in INV1.
    split; [exact INV1|]. split; [exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia))|]. split; [exact NN|]. split; [exact NH|]. split; [exact DLEN|].
    split; [exact LBN|]. split; [eapply cfr_cells_block; [exact CFR1| exact NMC| exact INn| intros []| cbn [blk_addr fst snd]; clear; lia| cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; clear - NN; lia]|]. split; [exact NUL|].
    split; [exact LBH|]. split; [eapply cfr_cells_block; [exact CFR1| exact HDC| exact INh| intros []| cbn [blk_addr fst snd]; clear; lia| cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; clear - NH; lia]|]. split; [exact NULH|].
    split; [exact LBD|]. split; [eapply cfr_cells_block; [exact CFR1| exact DTC| exact INd| intros []| cbn [blk_addr fst snd]; clear; lia| cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; clear - DLEN; lia]|].
    split; [exact SSZ|]. split; [exact EBLEN|]. split; [exact BOF| exact NSZ].
  Qed.

  (* [comment removed for export] *)
  Lemma pw_write_step : forall en st LBc Lc mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn st1 LB1 L1 m1 n v,
    pw_inv en st LBc Lc mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn ->
    cstate st1 LB1 (w_LB en) L1 m1 (wz (w_SP en + -64)) (w_tp en) (w_lo en) (w_B en) ->
    cframe (mbio_T K) [] (w_SP en + -64) st LBc Lc mc st1 LB1 L1 m1 ->
    bio_puts_res K BI M_MEM (len - off) max n LBc Lc v LB1 L1 m1 ->
    exists pd' max', (max' = max \/ max' = grow_n (len - off + n)) /\ len - off + n <= max'
      /\ pw_inv en st1 LB1 L1 m1 (mbk_data K pd') BI (len - off + n) max' 0 top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn.
  Proof.
    intros en st LBc Lc mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn st1 LB1 L1 m1 n v
           (INV & LOC & NN & NH & DLEN & LBN & NMC & NUL & LBH & HDC & NULH & LBD & DTC & SSZ & EBLEN & BOF & NSZ) CST1 FRM1 R1.
    pose proof (pw_news _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as ([INd NKd] & [INh NKh] & [INn NKn] & _).
    pose proof FRM1 as (CFR1 & _).
    destruct (w7_write_step libenv libenv_fp libenv_agree libenv_fp_where errst_live errst_fp errst_live_agree errst_fp_where
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV CST1 FRM1 R1) as (pd' & max' & HMAX & HFIT & INV1).
    exists pd', max'. split; [exact HMAX|]. split; [exact HFIT|].
    split; [exact INV1|]. split; [exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia))|]. split; [exact NN|]. split; [exact NH|]. split; [exact DLEN|].
    split; [exact LBN|]. split; [eapply cfr_cells_block; [exact CFR1| exact NMC| exact INn| exact NKn| cbn [blk_addr fst snd]; clear; lia| cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; clear - NN; lia]|]. split; [exact NUL|].
    split; [exact LBH|]. split; [eapply cfr_cells_block; [exact CFR1| exact HDC| exact INh| exact NKh| cbn [blk_addr fst snd]; clear; lia| cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; clear - NH; lia]|]. split; [exact NULH|].
    split; [exact LBD|]. split; [eapply cfr_cells_block; [exact CFR1| exact DTC| exact INd| exact NKd| cbn [blk_addr fst snd]; clear; lia| cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; clear - DLEN; lia]|].
    split; [exact SSZ|]. split; [exact EBLEN|]. split; [exact BOF| exact NSZ].
  Qed.

  (* [comment removed for export] *)
  Lemma f7_seg0 : forall en st LBc Lc mc K BI len max off top bot strs nws m',
    f7_invI en st LBc Lc mc K BI len max off top bot strs nws -> munch [] mc m' -> wmono usegs mc m' -> mem_inv usegs m' -> stk usegs m' (w_lo en) (w_SP en + -64) ->
    f7_invI en st LBc Lc m' K BI len max off top bot strs nws.
  Proof.
    intros en st LBc Lc mc K BI len max off top bot strs nws m' (COM & MB & LIVE & REST) MU WM MI' ST'.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    split; [eapply (com7_seg libenv libenv_fp libenv_agree libenv_fp_where); [exact COM| exact MU| exact WM| exact MI'| exact ST'| constructor]|].
    split; [eapply mbio_rep_agree; [exact MB| eapply agree_on_mono; [exact AG| intros a _; exact I]]|].
    split; [eapply errst_live_agree; [exact LIVE| eapply agree_on_mono; [exact AG| intros a _; exact I]]| exact REST].
  Qed.
  Lemma pw_seg0 : forall en st LBc Lc mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn m',
    pw_inv en st LBc Lc mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn ->
    munch [] mc m' -> wmono usegs mc m' -> mem_inv usegs m' -> stk usegs m' (w_lo en) (w_SP en + -64) ->
    pw_inv en st LBc Lc m' K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn.
  Proof.
    intros en st LBc Lc mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn m'
           (INV & LOC & NN & NH & DLEN & LBN & NMC & NUL & LBH & HDC & NULH & LBD & DTC & REST) MU WM MI' ST'.
    split; [exact (f7_seg0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV MU WM MI' ST')|].
    split; [eapply rw_cells_transport; [exact LOC| exact MU| exact WM| cbn; exact I]|]. split; [exact NN|]. split; [exact NH|]. split; [exact DLEN|].
    split; [exact LBN|]. split; [eapply rw_cells_transport; [exact NMC| exact MU| exact WM| cbn; exact I]|]. split; [exact NUL|].
    split; [exact LBH|]. split; [eapply rw_cells_transport; [exact HDC| exact MU| exact WM| cbn; exact I]|]. split; [exact NULH|].
    split; [exact LBD|]. split; [eapply rw_cells_transport; [exact DTC| exact MU| exact WM| cbn; exact I]| exact REST].
  Qed.

  (* [comment removed for export] *)
  Definition PW4_stmt : Prop :=
    forall (en : w7e) st LBc Lc f mc (K : mbk) (BI len max off top bot blen bof : Z) (strs : list block) (qd qh qn : bptr) (DT dlen HD nh NM nn : Z) (bd bh bn : list byte)
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    pw_inv en st LBc Lc mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn -> (10 + length strs <= f)%nat ->
    len - off <= blen - bof + nn + nh -> 3 * max <= 4 * (blen + bof + 256) + 12 ->
    climpl f Lc st (MS (mkR xra (wz (w_SP en + -64)) (w_gp en) (w_tp en) t0 t1 t2 (wz BI) (wz (w_D en)) a0 a1 a2 a3 a4 a5 a6 a7
                       (wz HD) (w_s3 en) (w_s4 en) (w_s5 en) (w_s6 en) (w_s7 en) (w_s8 en) (w_s9 en) (w_s10 en) (w_s11 en) t3 t4 t5 t6)
                 (w_F en) (wz J_PW4) (w_fc en) None mc (seg_rom usegs))
      (w7_post libenv errst_at_rest en).

  Theorem PW4_proof : bio_writeg_stmt -> F7_stmt libenv errst_at_rest errst_live -> PW4_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros BWG F7P en st LBc Lc f mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
           PW FU LENB MAXB.
    unfold bio_writeg_stmt in BWG. unfold F7_stmt in F7P. unfold J_PW4.
    pose proof PW as (INV & LOC & NN & NH & DLEN & LBN & NMC & NUL & LBH & HDC & NULH & LBD & DTC & SSZ & EBLEN & BOF & NSZ).
    pose proof INV as (COM & MB & LIVE & LEN2 & SIN & SL & NWS & KFR & KL & KS & NDSN & SFR & SLBL).
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NPL & INE & INL & PERM & SAVED & SLO & SPB & B63 & AL16 & EPE & ROOM & PAY & DLN & NDE & REL).
    pose proof CST as (HP & CO & (errv & AV & SPB' & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold LX_FUZZ_STACK, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range _ (w_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold w_SP in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia).
    pose proof (w7_mbio_rep_off _ _ _ _ _ _ _ _ _ MB) as [(OFF0 & LENM & MAX31) NDK].
    assert (D26 : zlength (w_d en) < 2 ^ 26) by (destruct PAY as (_ & _ & _ & _ & X & _); exact X).
    (* [comment removed for export] *)
    pose proof (cnt_of_perm _ _ _ PERM) as (CA & CB & CBIG).
    rewrite (cntA_app (mbk_ents K max)), (cntA_app (bents strs)) in CA. rewrite (cntB_app (mbk_ents K max)), (cntB_app (bents strs)) in CB.
    rewrite (bigsum_app (mbk_ents K max)), (bigsum_app (bents strs)) in CBIG.
    pose proof (cnt_mbk_ents K max ltac:(clear - OFF0 LENM; lia)) as (MA & MBB & MBIG & MA0 & MB0 & MBIG0).
    pose proof (bents_small strs SSZ) as [SB SBIG]. pose proof (cnt_bents strs) as (SA & SA0 & SB0 & _).
    pose proof (cnt_bents [(qd, DT, dlen); (qh, HD, nh); (qn, NM, nn)]) as (NA & NA0 & NB0 & NBIG). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in NA.
    specialize (NBIG ltac:(repeat constructor; cbn; clear - NN NH DLEN; lia)). unfold news_sz in NBIG. cbn [fold_right blk_size snd length Z.of_nat Pos.of_succ_nat Pos.succ] in NBIG.
    pose proof (grow_n_le43 (len - off + dlen) ltac:(clear - OFF0 DLEN; lia)) as [G0 G43].
    pose proof (w_bounds (grow_n (len - off + dlen)) G0) as (WA & WB & _ & WBIG).
    assert (ROOMW : croom Lc (wA (grow_n (len - off + dlen))) (wB (grow_n (len - off + dlen))) (wBig (grow_n (len - off + dlen)))).
    { unfold croom. unfold CL_ROOM_A, CL_ROOM_B, CL_ROOM_BIG, CAP_A, CAP_B, BIG_ROOM in ROOM |- *.
      clear - ROOM CA CB CBIG MA MBB MBIG MA0 MB0 MBIG0 SB SBIG SA SA0 SB0 NA NA0 NB0 NBIG G43 G0 WA WB WBIG LEN2 LENB MAXB EBLEN BOF NSZ D26 NN NH DLEN OFF0. lia. }
    (* [comment removed for export] *)
    pose proof LOC as LOC4. change ([C8 (wz dlen); C8 (wz DT); C8 (wz HD); C8 (wz NM)]) with ([C8 (wz dlen)] ++ [C8 (wz DT); C8 (wz HD); C8 (wz NM)]) in LOC4.
    apply (proj1 (rw_cells_app usegs mc _ _ _)) in LOC4. destruct LOC4 as [OLC LOC3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LOC3.
    replace dlen with (dlen + 2 ^ 32 * 0) in OLC by (clear; lia). apply (proj2 (t_cells_halves usegs mc _ dlen 0 ltac:(clear - DLEN; lia) ltac:(clear; lia))) in OLC.
    assert (LOCs : rw_cells usegs mc (bv_unsigned (w_sp en) + -64) ([C4 (wz dlen); C4 (wz 0)] ++ [C8 (wz DT); C8 (wz HD); C8 (wz NM)])).
    { apply (proj2 (rw_cells_app usegs mc _ _ _)). split; [exact OLC| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; exact LOC3]. }
    cbn [app] in LOCs. clear LOC OLC LOC3.
    pose proof (rw_cells_bytes_at _ _ _ _ DTC) as DTB. cbn [cells_bytes cbytes] in DTB. rewrite app_nil_r in DTB.
    pose proof (munch_refl ([] : list (Z * Z)) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    cprefix. ths. ths. rewrite (t_sx32_small dlen) by (clear - DLEN; lia). ths. ths. chere.
    eapply climpl_seq.
    { eapply BWG with (K := K) (BI := BI) (meth := M_MEM) (len := len) (max := max) (off := off) (IN := DT) (n := dlen) (lo := w_lo en) (B := w_B en) (src := bd);
        [clear - FU; lia| exact ROOMW| exact CST| rewrite unsigned_lit by lia; unfold BWRITE_STACK, WRITE_STACK, GROW_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear - SLO; lia
        | exact MB| clear - LENB BOF NSZ NN NH DLEN D26 EBLEN; lia| clear - DLEN; lia| exact DTB| exact LBD
        | right; exists qd, DT, dlen; split; [exact (proj1 (proj1 (Forall_forall _ _) NWS (qd, DT, dlen) ltac:(left; reflexivity)))| split; [exact (KS (qd, DT, dlen) ltac:(apply in_or_app; right; left; reflexivity))| clear; lia]]
        | rewrite unsigned_lit by lia; clear - AL16; Z.div_mod_to_equations; lia
        | reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & R1).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    destruct (w7_write_step libenv libenv_fp libenv_agree libenv_fp_where errst_live errst_fp errst_live_agree errst_fp_where
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV CST1 FRM1 R1) as (pd' & max' & HMAX & HFIT & INV1).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ (proj1 FRM1) LOCs ltac:(clear; lia)) as LOC1.
    change ([C4 (wz dlen); C4 (wz 0); C8 (wz DT); C8 (wz HD); C8 (wz NM)]) with ([C4 (wz dlen); C4 (wz 0)] ++ [C8 (wz DT); C8 (wz HD); C8 (wz NM)]) in LOC1.
    apply (proj1 (rw_cells_app usegs m1 _ _ _)) in LOC1. destruct LOC1 as [OLC1 LOC1]. apply (proj1 (t_cells_halves usegs m1 _ dlen 0 ltac:(clear - DLEN; lia) ltac:(clear; lia))) in OLC1.
    assert (LOC1' : rw_cells usegs m1 (bv_unsigned (w_sp en) + -64) [C8 (wz (dlen + 2 ^ 32 * 0)); C8 (wz DT); C8 (wz HD); C8 (wz NM)]).
    { change ([C8 (wz (dlen + 2 ^ 32 * 0)); C8 (wz DT); C8 (wz HD); C8 (wz NM)]) with ([C8 (wz (dlen + 2 ^ 32 * 0))] ++ [C8 (wz DT); C8 (wz HD); C8 (wz NM)]).
      apply (proj2 (rw_cells_app usegs m1 _ _ _)). split; [exact OLC1| exact LOC1]. }
    (* [comment removed for export] *)
    eapply (F7P en st1 LB1 L1 f1 m1 (mbk_data K pd') BI (len - off + dlen) max' 0 top bot strs (Some (qd, DT, dlen)) (Some (qh, HD, nh)) (Some (qn, NM, nn))).
    split; [cbn [olist app]; exact INV1| split; [clear - FU FU1; lia| cbn [oval blk_addr fst snd]; exact LOC1']].
  Qed.

  (* [comment removed for export] *)
  Definition PW3_stmt : Prop :=
    forall (en : w7e) st LBc Lc f mc (K : mbk) (BI len max off top bot blen bof : Z) (strs : list block) (qd qh qn : bptr) (DT dlen HD nh NM nn : Z) (bd bh bn : list byte)
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    pw_inv en st LBc Lc mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn -> (12 + length strs <= f)%nat ->
    len - off <= blen - bof + nn -> 3 * max <= 4 * (blen + bof + 256) + 12 ->
    climpl f Lc st (MS (mkR xra (wz (w_SP en + -64)) (w_gp en) (w_tp en) t0 t1 t2 (wz BI) (wz (w_D en)) a0 a1 a2 a3 a4 a5 a6 a7
                       (wz NM) (w_s3 en) (w_s4 en) (w_s5 en) (w_s6 en) (w_s7 en) (w_s8 en) (w_s9 en) (w_s10 en) (w_s11 en) t3 t4 t5 t6)
                 (w_F en) (wz J_PW3) (w_fc en) None mc (seg_rom usegs))
      (w7_post libenv errst_at_rest en).

  Theorem PW3_proof : bio_write0_stmt -> bio_writeg_stmt -> PW4_stmt -> PW3_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros BW0 BWG PW4P en st LBc Lc f mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
           PW FU LENB MAXB.
    unfold bio_write0_stmt in BW0. unfold bio_writeg_stmt in BWG. unfold PW4_stmt, J_PW4 in PW4P. unfold J_PW3.
    pose proof PW as (INV & LOC & NN & NH & DLEN & LBN & NMC & NUL & LBH & HDC & NULH & LBD & DTC & SSZ & EBLEN & BOF & NSZ).
    pose proof INV as (COM & MB & LIVE & LEN2 & SIN & SL & NWS & KFR & KL & KS & NDSN & SFR & SLBL).
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NPL & INE & INL & PERM & SAVED & SLO & SPB & B63 & AL16 & EPE & ROOM & PAY & DLN & NDE & REL).
    pose proof CST as (HP & CO & (errv & AV & SPB' & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold LX_FUZZ_STACK, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range _ (w_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold w_SP in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia).
    pose proof (w7_mbio_rep_off _ _ _ _ _ _ _ _ _ MB) as [(OFF0 & LENM & MAX31) NDK].
    assert (D26 : zlength (w_d en) < 2 ^ 26) by (destruct PAY as (_ & _ & _ & _ & X & _); exact X).
    pose proof (pw_news _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as ([INd NKd] & [INh NKh] & [INn NKn] & INLd & INLh & INLn).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INh) as (RH1 & _ & _ & RH2 & _).
    (* [comment removed for export] *)
    destruct (first_nul bh (nth_error_In _ _ NULH)) as (str & rest & EBH & NONUL).
    set (n := Z.of_nat (length str)) in *.
    assert (LSTR : n + 1 + Z.of_nat (length rest) = nh) by (subst n; rewrite EBH, length_app in LBH; cbn [length] in LBH; clear - LBH NH; lia).
    destruct (cstate_blk_pad _ _ _ _ _ _ _ _ _ _ _ _ CST INh) as (pad & PADB & PADL).
    assert (HDB : bytes_at usegs mc HD (str ++ Z_to_bv 8 0 :: (rest ++ pad))).
    { pose proof (rw_cells_bytes_at _ _ _ _ HDC) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r, EBH in X.
      rewrite app_comm_cons, app_assoc. apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact X|]. rewrite <- EBH, LBH, Z2Nat.id by (clear - NH; lia). exact PADB. }
    assert (PAD8 : (- (HD + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length (rest ++ pad))).
    { rewrite length_app, Nat2Z.inj_add, PADL. subst n. clear - LSTR NH. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl ([] : list (Z * Z)) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths.
    tcall (strlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str (rest ++ pad)).
    all: try first [eassumption | clear - RH1 RH2 LO SLO SPR; lia].
    cbv beta delta [mkR]. fold n.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    lazymatch goal with H : stk usegs m0 _ _ |- _ => rename H into ST0 end. lazymatch goal with H : mem_inv usegs m0 |- _ => rename H into MI0' end.
    lazymatch goal with H : bytes_at usegs m0 HD _ |- _ => rename H into HDB0 end.
    pose proof (pw_seg0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PW MU WM MI0' ST0) as PW0.
    pose proof (proj1 (proj1 (proj1 PW0))) as CST0.
    assert (NRANGE : 0 <= n <= nh - 1) by (subst n; clear - LSTR; lia).
    ths. rewrite (sextw_small n) by (clear - NRANGE NH; lia). ths. ths. ths. chere.
    pose proof PW0 as (INV0 & LOC0 & _ & _ & _ & _ & NMC0 & _ & _ & HDC0 & _ & _ & DTC0 & _). pose proof INV0 as (COM0 & MB0 & _).
    clear MU WM HP LATCH LXS CIMG.
    destruct (Z.eq_dec n 0) as [N0|N1].
    - (* [comment removed for export] *)
      rewrite N0. eapply climpl_seq.
      { eapply BW0 with (n := 0) (lo := w_lo en) (B := w_B en); [exact CST0| rewrite unsigned_lit by lia; clear - SLO; lia| reflexivity| clear; lia]. }
      cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (-> & -> & ->)).
      destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
      pose proof (pw_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PW0 CST1 FRM1) as PW1.
      eapply (PW4P en st1 LBc Lc f1 m1 K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn); [exact PW1| clear - FU FU1; lia| clear - LENB NH; lia| exact MAXB].
    - (* [comment removed for export] *)
      pose proof (cnt_of_perm _ _ _ PERM) as (CA & CB & CBIG).
      rewrite (cntA_app (mbk_ents K max)), (cntA_app (bents strs)) in CA. rewrite (cntB_app (mbk_ents K max)), (cntB_app (bents strs)) in CB.
      rewrite (bigsum_app (mbk_ents K max)), (bigsum_app (bents strs)) in CBIG.
      pose proof (cnt_mbk_ents K max ltac:(clear - OFF0 LENM; lia)) as (MA & MBB & MBIG & MA0 & MB0' & MBIG0).
      pose proof (bents_small strs SSZ) as [SB SBIG]. pose proof (cnt_bents strs) as (SA & SA0 & SB0 & _).
      pose proof (cnt_bents [(qd, DT, dlen); (qh, HD, nh); (qn, NM, nn)]) as (NA & NA0 & NB0 & NBIG). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in NA.
      specialize (NBIG ltac:(repeat constructor; cbn; clear - NN NH DLEN; lia)). unfold news_sz in NBIG. cbn [fold_right blk_size snd length Z.of_nat Pos.of_succ_nat Pos.succ] in NBIG.
      pose proof (grow_n_le43 (len - off + n) ltac:(clear - OFF0 NRANGE; lia)) as [G0 G43].
      pose proof (w_bounds (grow_n (len - off + n)) G0) as (WA & WB & _ & WBIG).
      assert (ROOMW : croom Lc (wA (grow_n (len - off + n))) (wB (grow_n (len - off + n))) (wBig (grow_n (len - off + n)))).
      { unfold croom. unfold CL_ROOM_A, CL_ROOM_B, CL_ROOM_BIG, CAP_A, CAP_B, BIG_ROOM in ROOM |- *.
        clear - ROOM CA CB CBIG MA MBB MBIG MA0 MB0' MBIG0 SB SBIG SA SA0 SB0 NA NA0 NB0 NBIG G43 G0 WA WB WBIG LEN2 LENB MAXB EBLEN BOF NSZ D26 NN NH DLEN OFF0 NRANGE. lia. }
      assert (HDS : bytes_at usegs m0 HD str) by (apply (proj1 (bytes_at_app _ _ _ _ _)) in HDB0; exact (proj1 HDB0)).
      eapply climpl_seq.
      { eapply BWG with (K := K) (BI := BI) (meth := M_MEM) (len := len) (max := max) (off := off) (IN := HD) (n := n) (lo := w_lo en) (B := w_B en) (src := str);
          [clear - FU; lia| exact ROOMW| exact CST0| rewrite unsigned_lit by lia; unfold BWRITE_STACK, WRITE_STACK, GROW_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear - SLO; lia
          | exact MB0| clear - LENB BOF NSZ NN NH DLEN D26 EBLEN NRANGE OFF0; lia| clear - NRANGE NH N1; lia| exact HDS| subst n; rewrite Nat2Z.id; reflexivity
          | right; exists qh, HD, nh; split; [exact INh| split; [exact NKh| clear - NRANGE; lia]]
          | rewrite unsigned_lit by lia; clear - AL16; Z.div_mod_to_equations; lia
          | reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & R1).
      destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
      destruct (pw_write_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PW0 CST1 FRM1 R1) as (pd' & max' & HMAX & HFIT & PW1).
      eapply (PW4P en st1 LB1 L1 f1 m1 (mbk_data K pd') BI (len - off + n) max' 0 top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn);
        [exact PW1| clear - FU FU1; lia| clear - LENB NH NRANGE; lia|].
      destruct HMAX as [->| ->]; [exact MAXB| clear - G43 LENB NRANGE NSZ DLEN BOF OFF0; lia].
  Qed.

  (* [comment removed for export] *)
  Definition PW2_stmt : Prop :=
    forall (en : w7e) st LBc Lc f mc (K : mbk) (BI len max off top bot blen bof : Z) (strs : list block) (qd qh qn : bptr) (DT dlen HD nh NM nn : Z) (bd bh bn : list byte)
           (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 : word),
    pw_inv en st LBc Lc mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn -> (14 + length strs <= f)%nat ->
    len - off <= blen - bof -> 3 * max <= 4 * (blen + bof + 256) + 12 ->
    climpl f Lc st (MS (mkR xra (wz (w_SP en + -64)) (w_gp en) (w_tp en) t0 t1 t2 (wz BI) (wz (w_D en)) (wz 1) a1 a2 a3 a4 a5 a6 a7
                       s2v (w_s3 en) (w_s4 en) (w_s5 en) (w_s6 en) (w_s7 en) (w_s8 en) (w_s9 en) (w_s10 en) (w_s11 en) t3 t4 t5 t6)
                 (w_F en) (wz J_P7) (w_fc en) None mc (seg_rom usegs))
      (w7_post libenv errst_at_rest en).

  Theorem PW2_proof : bio_write0_stmt -> bio_writeg_stmt -> PW3_stmt -> PW2_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros BW0 BWG PW3P en st LBc Lc f mc K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6
           PW FU LENB MAXB.
    unfold bio_write0_stmt in BW0. unfold bio_writeg_stmt in BWG. unfold PW3_stmt, J_PW3 in PW3P. unfold J_P7.
    pose proof PW as (INV & LOC & NN & NH & DLEN & LBN & NMC & NUL & LBH & HDC & NULH & LBD & DTC & SSZ & EBLEN & BOF & NSZ).
    pose proof INV as (COM & MB & LIVE & LEN2 & SIN & SL & NWS & KFR & KL & KS & NDSN & SFR & SLBL).
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NPL & INE & INL & PERM & SAVED & SLO & SPB & B63 & AL16 & EPE & ROOM & PAY & DLN & NDE & REL).
    pose proof CST as (HP & CO & (errv & AV & SPB' & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold LX_FUZZ_STACK, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range _ (w_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold w_SP in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia).
    pose proof (w7_mbio_rep_off _ _ _ _ _ _ _ _ _ MB) as [(OFF0 & LENM & MAX31) NDK].
    assert (D26 : zlength (w_d en) < 2 ^ 26) by (destruct PAY as (_ & _ & _ & _ & X & _); exact X).
    pose proof (pw_news _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as ([INd NKd] & [INh NKh] & [INn NKn] & INLd & INLh & INLn).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INn) as (RN1 & _ & _ & RN2 & _).
    (* [comment removed for export] *)
    destruct (first_nul bn NUL) as (str & rest & EBN & NONUL).
    set (n := Z.of_nat (length str)) in *.
    assert (LSTR : n + 1 + Z.of_nat (length rest) = nn) by (subst n; rewrite EBN, length_app in LBN; cbn [length] in LBN; clear - LBN NN; lia).
    destruct (cstate_blk_pad _ _ _ _ _ _ _ _ _ _ _ _ CST INn) as (pad & PADB & PADL).
    assert (NMB : bytes_at usegs mc NM (str ++ Z_to_bv 8 0 :: (rest ++ pad))).
    { pose proof (rw_cells_bytes_at _ _ _ _ NMC) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r, EBN in X.
      rewrite app_comm_cons, app_assoc. apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact X|]. rewrite <- EBN, LBN, Z2Nat.id by (clear - NN; lia). exact PADB. }
    assert (PAD8 : (- (NM + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length (rest ++ pad))).
    { rewrite length_app, Nat2Z.inj_add, PADL. subst n. clear - LSTR NN. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl ([] : list (Z * Z)) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. if_cases K1; zify_cond K1; [exfalso; clear - K1; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    ths. ths. ths.
    tcall (strlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str (rest ++ pad)).
    all: try first [eassumption | clear - RN1 RN2 LO SLO SPR; lia].
    cbv beta delta [mkR]. fold n.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    lazymatch goal with H : stk usegs m0 _ _ |- _ => rename H into ST0 end. lazymatch goal with H : mem_inv usegs m0 |- _ => rename H into MI0' end.
    lazymatch goal with H : bytes_at usegs m0 NM _ |- _ => rename H into NMB0 end.
    pose proof (pw_seg0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PW MU WM MI0' ST0) as PW0.
    pose proof (proj1 (proj1 (proj1 PW0))) as CST0.
    assert (NRANGE : 0 <= n <= nn - 1) by (subst n; clear - LSTR; lia).
    ths. rewrite (sextw_small n) by (clear - NRANGE NN; lia). ths. ths. ths. chere.
    pose proof PW0 as (INV0 & LOC0 & _ & _ & _ & _ & NMC0 & _ & _ & HDC0 & _ & _ & DTC0 & _). pose proof INV0 as (COM0 & MB0 & _).
    clear MU WM HP LATCH LXS CIMG.
    destruct (Z.eq_dec n 0) as [N0|N1].
    - (* [comment removed for export] *)
      rewrite N0. eapply climpl_seq.
      { eapply BW0 with (n := 0) (lo := w_lo en) (B := w_B en); [exact CST0| rewrite unsigned_lit by lia; clear - SLO; lia| reflexivity| clear; lia]. }
      cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (-> & -> & ->)).
      destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
      pose proof (pw_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PW0 CST1 FRM1) as PW1.
      eapply (PW3P en st1 LBc Lc f1 m1 K BI len max off top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn); [exact PW1| clear - FU FU1; lia| clear - LENB NN; lia| exact MAXB].
    - (* [comment removed for export] *)
      pose proof (cnt_of_perm _ _ _ PERM) as (CA & CB & CBIG).
      rewrite (cntA_app (mbk_ents K max)), (cntA_app (bents strs)) in CA. rewrite (cntB_app (mbk_ents K max)), (cntB_app (bents strs)) in CB.
      rewrite (bigsum_app (mbk_ents K max)), (bigsum_app (bents strs)) in CBIG.
      pose proof (cnt_mbk_ents K max ltac:(clear - OFF0 LENM; lia)) as (MA & MBB & MBIG & MA0 & MB0' & MBIG0).
      pose proof (bents_small strs SSZ) as [SB SBIG]. pose proof (cnt_bents strs) as (SA & SA0 & SB0 & _).
      pose proof (cnt_bents [(qd, DT, dlen); (qh, HD, nh); (qn, NM, nn)]) as (NA & NA0 & NB0 & NBIG). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in NA.
      specialize (NBIG ltac:(repeat constructor; cbn; clear - NN NH DLEN; lia)). unfold news_sz in NBIG. cbn [fold_right blk_size snd length Z.of_nat Pos.of_succ_nat Pos.succ] in NBIG.
      pose proof (grow_n_le43 (len - off + n) ltac:(clear - OFF0 NRANGE; lia)) as [G0 G43].
      pose proof (w_bounds (grow_n (len - off + n)) G0) as (WA & WB & _ & WBIG).
      assert (ROOMW : croom Lc (wA (grow_n (len - off + n))) (wB (grow_n (len - off + n))) (wBig (grow_n (len - off + n)))).
      { unfold croom. unfold CL_ROOM_A, CL_ROOM_B, CL_ROOM_BIG, CAP_A, CAP_B, BIG_ROOM in ROOM |- *.
        clear - ROOM CA CB CBIG MA MBB MBIG MA0 MB0' MBIG0 SB SBIG SA SA0 SB0 NA NA0 NB0 NBIG G43 G0 WA WB WBIG LEN2 LENB MAXB EBLEN BOF NSZ D26 NN NH DLEN OFF0 NRANGE. lia. }
      assert (NMS : bytes_at usegs m0 NM str) by (apply (proj1 (bytes_at_app _ _ _ _ _)) in NMB0; exact (proj1 NMB0)).
      eapply climpl_seq.
      { eapply BWG with (K := K) (BI := BI) (meth := M_MEM) (len := len) (max := max) (off := off) (IN := NM) (n := n) (lo := w_lo en) (B := w_B en) (src := str);
          [clear - FU; lia| exact ROOMW| exact CST0| rewrite unsigned_lit by lia; unfold BWRITE_STACK, WRITE_STACK, GROW_STACK, CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear - SLO; lia
          | exact MB0| clear - LENB BOF NSZ NN NH DLEN D26 EBLEN NRANGE OFF0; lia| clear - NRANGE NN N1; lia| exact NMS| subst n; rewrite Nat2Z.id; reflexivity
          | right; exists qn, NM, nn; split; [exact INn| split; [exact NKn| clear - NRANGE; lia]]
          | rewrite unsigned_lit by lia; clear - AL16; Z.div_mod_to_equations; lia
          | reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & R1).
      destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
      destruct (pw_write_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PW0 CST1 FRM1 R1) as (pd' & max' & HMAX & HFIT & PW1).
      eapply (PW3P en st1 LB1 L1 f1 m1 (mbk_data K pd') BI (len - off + n) max' 0 top bot blen bof strs qd qh qn DT dlen HD nh NM nn bd bh bn);
        [exact PW1| clear - FU FU1; lia| clear - LENB NN NRANGE; lia|].
      destruct HMAX as [->| ->]; [exact MAXB| clear - G43 LENB NRANGE NSZ DLEN NH BOF OFF0; lia].
  Qed.

  (* [comment removed for export] *)
  Definition PZ7_stmt : Prop :=
    forall (en : w7e) st LBc Lc f mc (K : mbk) (BI len max off top bot : Z) (strs : list block)
           (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 ol : word),
    f7_invI en st LBc Lc mc K BI len max off top bot strs [] -> (8 + length strs <= f)%nat ->
    rw_cells usegs mc (w_SP en + -64) [C8 ol; C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc st (MS (mkR xra (wz (w_SP en + -64)) (w_gp en) (w_tp en) t0 t1 t2 (wz BI) (wz (w_D en)) (wz 0) a1 a2 a3 a4 a5 a6 a7
                       s2v (w_s3 en) (w_s4 en) (w_s5 en) (w_s6 en) (w_s7 en) (w_s8 en) (w_s9 en) (w_s10 en) (w_s11 en) t3 t4 t5 t6)
                 (w_F en) (wz J_P7) (w_fc en) None mc (seg_rom usegs))
      (w7_post libenv errst_at_rest en).

  Theorem PZ7_proof : F7_stmt libenv errst_at_rest errst_live -> PZ7_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros F7P en st LBc Lc f mc K BI len max off top bot strs xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 ol INV FU LOC.
    unfold F7_stmt, J_F7 in F7P. unfold J_P7.
    pose proof INV as (COM & MB & _).
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NPL & INE & INL & PERM & SAVED & SLO & SPB & B63 & AL16 & EPE & ROOM & PAY & DLN & NDE & REL).
    pose proof CST as (HP & CO & (errv & AV & SPB' & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold LX_FUZZ_STACK, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range _ (w_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold w_SP in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia).
    pose proof (munch_refl ([] : list (Z * Z)) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    cprefix. ths. ths. if_cases K1; zify_cond K1; [| exfalso; clear - K1; rewrite ?unsigned_lit in K1 by lia; lia]. clear K1.
    chere. eapply (F7P en st LBc Lc f mc K BI len max off top bot strs None None None). split; [cbn [olist app]; exact INV| split; [exact FU| cbn [oval]; exact LOC]].
  Qed.
End W7.
