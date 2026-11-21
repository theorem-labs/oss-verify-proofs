(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_defl_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_defl_kit Z_defl_path Z_defl_arms Zg_adler32_iface Zg_defl_iface Zg_defl_path Zg_defl_entry Zg_defl_pend Zg_defl_hdr Zg_defl_blocks Zg_defl_fin Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate SendModel FillWinModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSlow6 RefDeflSafeS. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section ASMG.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HSTO : deflate_stored_stmt.
Hypothesis HSLOW : deflate_slow_stmtg.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HFL : flush = 0 \/ flush = 4 \/ flush = 5.

(* [comment removed for export] *)
Lemma defl_dispg : forall (Q : machine_state -> Prop) (X : deflate_state),
  (ds_status X = 42 \/ ds_status X = 113 \/ ds_status X = 666) -> 0 <= cs_avail_in (ds_strm X) < 2^31 ->
  (ds_status X = 42 -> DKS L flush rest0 lo r F fc me Q 0x173b0 X) ->
  (ds_status X = 113 -> DK L flush rest0 lo r F fc me Q 0x18068 X) ->
  (ds_status X = 666 -> cs_avail_in (ds_strm X) = 0 -> DKS L flush rest0 lo r F fc me Q 0x18078 X) ->
  (ds_status X = 666 -> cs_avail_in (ds_strm X) <> 0 -> DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return X Z_BUF_ERROR))) ->
  DKB L flush rest0 lo r F fc me Q X.
Proof.
  intros Q X HST RAI KH K90 K98 KERR. unfold DKB. intros until m'. intros DI.
  unfold deflR, Z_DEFL_DISP.
  destruct HST as [E|[E|E]].
  - specialize (KH E). clear K90 K98 KERR. rewrite E. zs. zstep. closed_br.
    unfold DKS, deflR in KH. eapply KH. exact DI.
  - specialize (K90 E). clear KH K98 KERR. rewrite E. zs. zstep. closed_br.
    zs. zstep. closed_br.
    (* [comment removed for export] *)
    zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zstep.
    unfold DK, deflR in K90. eapply K90. exact DI.
  - specialize (K98 E). specialize (KERR E). clear KH K90. rewrite E. zs. zstep. closed_br.
    zs. zstep. closed_br.
    pose proof DI as DI0. destruct DI as (DR & _). destruct DR as [ZS _]. open_zs ZS.
    zs. zstep. if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by lia.
    + unfold DKS, deflR in K98. eapply (K98 ltac:(lia)). exact DI0.
    + eapply (defl_buferr L inp rest0 lo r F fc me CTX Q X 0x173a4); [right; left; reflexivity| exact DI0| apply KERR; lia].
Qed.

Variables (R : deflate_state * Z) (Q : machine_state -> Prop).
Hypothesis EXIT : forall X rc, R = (X, rc) -> DKE L rest0 lo r F fc me Q (wz rc) X.
Hypothesis ROOMR : (length (cs_out_rev (ds_strm (fst R))) <= length rest0)%nat.

Lemma room_of_oleg : forall X, ole R X -> Box (length (cs_out_rev (ds_strm X)) <= length rest0)%nat.
Proof. intros X [OL _]. apply box. lia. Qed.

Lemma asmg_lf : forall X, R = (set_last_flush X (-1), 0) -> DKL L flush rest0 lo r F fc me Q X.
Proof. intros X ER. apply (defl_lf L inp rest0 lo r F fc me CTX flush). exact (EXIT _ _ ER). Qed.

Lemma asmg_fin : forall X, fin_path flush R X -> DKS L flush rest0 lo r F fc me Q 0x18228 X.
Proof.
  intros X (OL & RW & W2 & E0 & E1 & TR).
  apply (defl_fing L flush inp rest0 lo r F fc me CTX HTFB Q X HFL RW W2).
  - intros F4 WP. destruct (TR F4 WP) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & _).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
    split; [exact A7|]. split; [exact A8|]. exact (room_of_oleg _ A9).
  - intros F4. exact (EXIT _ _ (E0 F4)).
  - intros F4 WN. exact (EXIT _ _ (E1 F4 WN)).
  - intros F4 WP P0. destruct (TR F4 WP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & T1 & _). exact (EXIT _ _ (T1 P0)).
  - intros F4 WP PN. destruct (TR F4 WP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T0). exact (EXIT _ _ (T0 PN)).
Qed.

Lemma asmg_run : forall X, blocks_pathg inp flush R X -> blk_cond X flush = true -> DKS L flush rest0 lo r F fc me Q 0x18080 X.
Proof.
  intros X (OL & RAI & RLA & RST & PT & _) HC.
  destruct (PT HC) as (LV & SG & TIE & WS & HS & LBS & W2 & W0 & WRG & RAO & SE & SAFE & OL1 & RAO2 & ENM0 & ENM1 & EFS0 & EFS1 & KF & KBD).
  apply (defl_rung L flush inp rest0 lo r F fc me CTX HTFB HSTO HSLOW Q X HFL LV SG TIE WS HS LBS W2 W0 WRG (proj2 RAI) RAO SE SAFE (room_of_oleg _ OL1) RAO2).
  - intros Hb A0. exact (asmg_lf _ (ENM0 Hb A0)).
  - intros Hb AN. exact (EXIT _ _ (ENM1 Hb AN)).
  - intros Hb A0. exact (asmg_lf _ (EFS0 Hb A0)).
  - intros Hb AN. exact (EXIT _ _ (EFS1 Hb AN)).
  - intros Hb. exact (asmg_fin _ (KF Hb)).
  - intros Hb. destruct (KBD Hb) as (F5 & FP & LB1 & OLF & RAOF & E0 & E1).
    split; [exact F5|]. split; [exact FP|]. split; [exact LB1|]. split; [exact (room_of_oleg _ OLF)|]. split; [exact RAOF|].
    split; [intros A0; exact (EXIT _ _ (E0 A0))| intros AN; exact (asmg_fin _ (E1 AN))].
Qed.

Lemma asmg_blk98 : forall X, blocks_pathg inp flush R X -> cs_avail_in (ds_strm X) = 0 -> DKS L flush rest0 lo r F fc me Q 0x18078 X.
Proof.
  intros X BP A0. pose proof BP as (OL & RAI & RLA & RST & PT & PF).
  assert (EC : blk_cond X flush = negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE)))
    by (unfold blk_cond; rewrite A0; reflexivity).
  apply (defl_blk98g L flush rest0 lo r F fc me Q X HFL A0 RLA RST).
  - intros C. apply (asmg_run X BP). rewrite EC. exact C.
  - intros C F0. destruct (PF ltac:(rewrite EC; exact C)) as (_ & _ & _ & E0 & _). exact (EXIT _ _ (E0 ltac:(lia))).
  - intros C FN. apply asmg_fin. apply PF. rewrite EC. exact C.
Qed.

Lemma asmg_blk90 : forall X, blocks_pathg inp flush R X -> DK L flush rest0 lo r F fc me Q 0x18068 X.
Proof.
  intros X BP. pose proof BP as (OL & RAI & _).
  apply (defl_blk90g L flush rest0 lo r F fc me Q X RAI).
  - intros AN. apply (asmg_run X BP). unfold blk_cond.
    replace (cs_avail_in (ds_strm X) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AN). reflexivity.
  - intros A0. exact (asmg_blk98 X BP A0).
Qed.

Lemma asmg_body : forall X, body_pathg inp flush R X -> DKB L flush rest0 lo r F fc me Q X.
Proof.
  intros X (OL & HST & RAI & EERR & B98 & B90 & HDR).
  apply (defl_dispg Q X HST RAI).
  - intros E42. pose proof (HDR E42) as HH. cbv zeta in HH.
    destruct HH as (W1 & WB & LV & SG & RSS & RP0 & RP6 & LBS & RAD & RAO & FPOK & ST5 & RP5 & OL5 & E5 & B5).
    apply (defl_hdrg L flush inp rest0 lo r F fc me CTX HTFB Q X W1 WB LV SG RSS RP0 RP6 LBS RAD RAO FPOK ST5 RP5 (room_of_oleg _ OL5)).
    + intros PN. exact (asmg_lf _ (E5 PN)).
    + intros P0. exact (asmg_blk90 _ (B5 P0)).
  - intros E113. exact (asmg_blk90 _ (B90 E113)).
  - intros E666 A0. exact (asmg_blk98 _ (B98 E666 A0) A0).
  - intros E666 AN. exact (EXIT _ _ (EERR E666 AN)).
Qed.

Lemma asmg_top : forall (d : deflate_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  defl_pathg inp flush R d -> DREP me L d -> dout me L rest0 (ds_strm d) -> stk usegs me lo (bv_unsigned (r_sp r)) -> mem_inv usegs me ->
  evt usegs Q (MS (mkR (r_ra r) (r_sp r) (r_gp r) (r_tp r) t0 t1 t2 (r_s0 r) (r_s1 r) (wz (dl_S L)) (wz flush) a2 a3 a4 a5 a6 a7
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) t3 t4 t5 t6)
                  F (wz Z_DEFLATE_PC) fc None me (seg_rom usegs)).
Proof.
  intros until t6. intros PATH DR DOUT STK MI. cbv zeta in PATH. destruct PATH as (OL & HST & RAI & RNI & PERR & POK).
  apply (defl_entryg L inp rest0 lo r F fc me CTX Q d flush t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 DR DOUT (room_of_oleg _ OL) STK MI HST ltac:(lia) RAI RNI).
  - intros C. exact (EXIT _ _ (PERR C)).
  - intros NE. destruct (POK NE) as (RAO & RLF & RP & LBS & EBUF & PGO).
    assert (RST : 0 <= ds_status d < 1000) by lia.
    intros y1 y5 y6 y7 y12 y15 y16 y17 y28 y29 y30 y31 m' DI.
    apply (defl_pendg L flush inp rest0 lo r F fc me CTX HTFB Q d y1 y5 y6 y7 y12 y15 y16 y17 y28 y29 y30 y31 m' DI HFL RAO RAI RLF RP LBS RST).
    + intros AN PN. exact (proj1 (proj1 (PGO AN) PN)).
    + intros AN PN. exact (proj1 (proj2 (proj1 (PGO AN) PN))).
    + intros AN PN. exact (room_of_oleg _ (proj1 (proj2 (proj2 (proj1 (PGO AN) PN))))).
    + intros A0. exact (EXIT _ _ (EBUF A0)).
    + intros AN PN A2. exact (asmg_lf _ (proj1 (proj2 (proj2 (proj2 (proj1 (PGO AN) PN)))) A2)).
    + intros AN PN A2. exact (asmg_body _ (proj2 (proj2 (proj2 (proj2 (proj1 (PGO AN) PN)))) A2)).
    + intros AN P0 RK. exact (EXIT _ _ (proj1 (proj2 (PGO AN) P0) RK)).
    + intros AN P0 NRK. exact (asmg_body _ (proj2 (proj2 (PGO AN) P0) NRK)).
Qed.
End ASMG.

Section DEFLG.
Hypothesis HSTO : deflate_stored_stmt.
Hypothesis HSLOW : deflate_slow_stmtg.
Hypothesis HTFB : tr_flush_bits_stmt.

Theorem deflate_in_specg : deflate_in_stmtg.
Proof.
  unfold deflate_in_stmtg. intros until m. intros DR DIN DOUT MI RL STK LO SP16 BEL IO HFL PATH ROOM -> ->.
  set (r := mkSR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  assert (CTX : defl_ctx L inp rest0 lo r m).
  { constructor; [exact LO| exact SP16| exact (st_lay _ _ _ _ (proj2 DR))| exact BEL| exact IO| exact RL| exact DIN]. }
  revert PATH ROOM. generalize (deflate_core d flush). intros R PATH ROOM.
  assert (EXIT : forall X rc, R = (X, rc) ->
            DKE L rest0 lo r F fc m (deflate_in_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (fst R) (snd R) inp rest0 lo m) (wz rc) X).
  { intros X rc ER. subst R. cbn [fst snd]. unfold DKE.
    intros y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 m' DI.
    eapply evt_mono; [exact (defl_epi L inp rest0 lo r F fc m CTX X (wz rc) y1 y5 y6 y7 y8 y9 y10 y11 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 m' DI)|].
    intros ms' P. unfold deflate_in_post. rewrite Z_to_bv_mod64. exact P. }
  unfold Z_NO_FLUSH, Z_FINISH, Z_BLOCK in HFL.
  exact (asmg_top L flush inp rest0 lo r F fc m CTX HSTO HSLOW HTFB HFL R _ EXIT ROOM d t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 PATH DR DOUT STK MI).
Qed.
End DEFLG.
