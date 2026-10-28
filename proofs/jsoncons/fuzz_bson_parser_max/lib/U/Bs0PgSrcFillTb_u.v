(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnParSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParKit
     PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSrcSFillP_u Bs0_code_r369d8_369dc_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PGSFBT.
Import PMS.

Ltac tr64 M0 AG := lazymatch goal with |- L5.u64_at ?sg ?M2 ?a ?v =>
  let X := fresh "X" in assert (X : L5.u64_at sg M0 a v) by PMK.gmem;
  apply (L5C.u64_at_agree sg M0 M2 a v); [apply AG; lia | lia | lia | exact X] end.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Theorem fill_buffer_tb_okG : PMPSS.xsgetn_spec L HI -> PGS.fill_buffer_tb_specG RSEGS AD L HI.
Proof.
  intros XS. unfold PGS.fill_buffer_tb_specG, PGS.src_specG.
  intros O OK fx R M model K OB LBX cr sp r src str sm Wextra HH MOK K0 ENT SPLO A10 ARGS WX PA IA BASE INCS KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
  pose proof (PGS.oo_lay _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & AL36 & AL37 & LY6 & LYD).
  pose proof (PGS.oo_src _ _ _ _ _ OK M src OB PA) as (PSRC & PNI & SDEFo).
  set (os := PGS.ow_os O) in *. set (ois := PGS.ow_ois O) in *. set (lo := PGS.ow_lo O) in *. set (hi := PGS.ow_hi O) in *.
  assert (F1 : sp <= os /\ sp <= ois /\ os + 296 <= hl_sptop L /\ ois + 272 <= hl_sptop L /\ (os + 296 <= ois \/ ois + 272 <= os)) by (clear - SPLO LY1 LY2 LY3 LY4 LY5 LYD; lia).
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  destruct ARGS as (p & A11 & A12 & WINp). destruct WX as (p' & A11' & Hp' & ->).
  pose proof (PGS.oo_win _ _ _ _ _ OK M src OB p PM.CHUNK PA WINp) as (_ & DEFp & [(q0 & c0 & OIN & Dq1 & Dq2)|WFR]); [|unfold PM.CHUNK in WFR; lia].
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11, A11'. rewrite L5K.rl12 in A12.
  change (PMSP.pm_scr 3) with 18432 in *. unfold PM.CHUNK in *.
  assert (SC0 : 0 <= 18432) by lia.
  set (LB := PM.src_own src ++ OB ++ LBX) in *.
  assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
  pose proof (L5C.stk_writable RSEGS _ M sp 18432 STK) as WR.
  pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG.
  destruct src as [qc de rem]. destruct sm as [g eg st].
  cbn [PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
  assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.src_own; cbn; left; reflexivity).
  assert (TIN : In (q0, c0) LB) by (unfold LB, PM.src_own; cbn [PM.sr_qc app]; right; apply in_or_app; left; exact OIN).
  assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; intros x Hx; apply in_or_app; right; apply in_or_app; right; exact (INCS x Hx)).
  destruct PSRC as (S240 & S248 & S256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & QM16 & DCH & _).
  cbn [PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
  pose proof IA as (I0 & IDEF & _ & I16 & _ & _ & I40 & _ & _ & _ & _ & _ & IIOS & _ & IE2).
  destruct IIOS as (_ & J32 & J36 & J40 & _ & _ & _ & _ & ST).
  cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf AD PnLayoutS_u.ADDR_S] in *.
  assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
  destruct (BR q0 c0 TIN) as (T0 & T1' & T4'). unfold hl_ceil in T4'.
  assert (Ep : p' = p).
  { rewrite A11 in A11'. apply (f_equal bv_unsigned) in A11'. rewrite !L5.unsigned_lit in A11' by (clear - Hp' T0 T4' Dq1 Dq2 STOP; lia). exact (eq_sym A11'). }
  subst p'. clear A11'.
  set (WS := (PGS.W_srcfG os ois ++ [(qc, 16384)]) ++ [(p, 16384)]).
  assert (WSE : PGS.W_srcG os ois (PM.SRC qc de rem) ++ [(p, 16384)] = WS) by reflexivity. rewrite WSE in KONT. clear WSE.
  (* [comment removed for export] *)
  assert (OWA : Forall (fun b => fst b + snd b <= lo \/ hi <= fst b) (PM.src_own (PM.SRC qc de rem) ++ OB)).
  { apply Forall_forall. intros [B m] Hin. left. cbn [fst snd].
    assert (HB : In (B, m) LB) by (unfold LB; rewrite app_assoc; apply in_or_app; left; exact Hin).
    destruct (BR _ _ HB) as (_ & _ & Z4). unfold hl_ceil in Z4. clear - Z4 SLO SPLO. lia. }
  assert (OWB : forall b, In b OB -> fst b + snd b <= PM.sr_qc (PM.SRC qc de rem) \/ PM.sr_qc (PM.SRC qc de rem) + PM.CHUNK <= fst b).
  { intros [B m] Hin. cbn [fst snd PM.sr_qc]. unfold PM.CHUNK.
    assert (HB : In (B, m) LB) by (unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact Hin).
    assert (NE : B <> qc).
    { intros E. subst B. apply (PMPK.fst_neq_app [(qc, 16384)] (OB ++ LBX) qc 16384 qc m); [exact (PMPK.heap_nodup L HI HIok LB cr M _ HH)| left; reflexivity| apply in_or_app; left; exact Hin| reflexivity]. }
    destruct (PMPK.blocks_apart_heap L HI HIok LB cr M _ B m qc 16384 HH HB QIN NE) as [X|X]; clear - X; lia. }
  (* [comment removed for export] *)
  assert (OWK : forall M3, L5C.hpres L LB sp 18432 WS M M3 -> L5C.agree_on M M3 (os + 240) 56 -> PMPK.dkr M M3 qc 16384 ->
      PGS.ow_at O M3 (PM.SRC qc de rem) OB).
  { intros M3 HP3 AG3 DK3.
    apply (PGS.oo_upd _ _ _ _ _ OK LBX sp 18432 [(p, 16384)] M M3 (PM.SRC qc de rem) (PM.SRC qc de rem) OB cr (m_vmmaps model) SPLO PA HH OWA OWB);
      [constructor; [right; cbn [fst snd]; exact WINp| constructor]| unfold WS in HP3; unfold PGS.W_srcG, PM.src_own; cbn [PM.sr_qc]; exact HP3| |reflexivity].
    unfold PM.src_fields_at. cbn [PM.sr_qc PM.sr_de PM.sr_rem]. unfold PM.CHUNK.
    split; [apply (L5C.u64_at_agree RSEGS M M3); [eapply L5C.agree_on_sub; [exact AG3|lia|lia]|lia|lia| exact S240]|].
    split; [apply (L5C.u64_at_agree RSEGS M M3); [eapply L5C.agree_on_sub; [exact AG3|lia|lia]|lia|lia| exact S248]|].
    split; [apply (L5C.defined_agree M M3); [eapply L5C.agree_on_sub; [exact AG3|lia|lia]| exact S256]|].
    split; [apply (L5C.u64_at_agree RSEGS M M3); [eapply L5C.agree_on_sub; [exact AG3|lia|lia]|lia|lia| exact S264]|].
    split; [apply (L5C.u64_at_agree RSEGS M M3); [eapply L5C.agree_on_sub; [exact AG3|lia|lia]|lia|lia| exact S272]|].
    split; [apply (L5C.u64_at_agree RSEGS M M3); [eapply L5C.agree_on_sub; [exact AG3|lia|lia]|lia|lia| exact S280]|].
    split; [apply (L5C.u64_at_agree RSEGS M M3); [eapply L5C.agree_on_sub; [exact AG3|lia|lia]|lia|lia| exact S288]|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact QM16|].
    split; [apply (PMPK.defined_dkr M M3 qc 16384 DK3 DCH)|]. split; exact I. }
  unfold PMSP.cfg. cbn [pa_fill_buffer AD PnLayoutS_u.ADDR_S].
  destruct ST as [ST0|ST2].
  2:{ (* [comment removed for export] *)
    subst st.
    LeanFeed.pfeed P (PMSFBP.fbE_conc fx R M (fun j => match j with 2%nat => sp | 36%nat => os | 37%nat => ois | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSFBP.aligned; first [exact A16 | exact AL36 | exact AL37]]).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & X10 & _)); PMK.pvz_clrT.
    set (P := fun a => sp - 32 <= a < sp - 32 + 32).
    assert (PF : forall a, P a -> sp - 18432 <= a < sp) by (intros a X; unfold P in X; lia).
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x382d4 R1 0x383dc M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
    { intros a Pa. apply (PMK.cwr_stack L LB M sp 18432 a STK). apply PF in Pa. lia. }
    { intros a. apply PMK.rng_dec. }
    intros HH1.
    assert (EK1 : PMK.ek L LB sp 18432 [] M M1) by (apply (PMFR.ek_of_piece RSEGS L KL LB sp 18432 M M1 P FRZ STK (PMFR.brange_hi L LB BR) PF)).
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
    { apply (PMK.ret_to RSEGS fx1 R1 M1 0x383dc W_373ac r F_373ac eq_refl D_373ac); [rewrite (KS 1%nat) by PMK.inl; exact Rra| lia| exact Hr2]. }
    apply (KONT fx1 R1 M1 (PM.SRC qc de rem) (PM.STRM g eg 2)).
    + apply PMK.preserved_by_index. intros k Hk. apply KS. revert k Hk. apply (PMPK.cs_in PMSFBP.KS_fbE). vm_compute. reflexivity.
    + apply OWK.
      * apply (PMK.hpres_of L LB sp 18432 _ M M1).
        -- apply (PMK.ek_weaken L LB LB sp 18432 sp 18432 _ [] M M1 EK1); [apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil.
        -- apply (L5.defined_grows M M1 _ _ MG). exact SDEF.
        -- apply (PMK.dk_grows L LB sp 18432 M M1 MG).
      * intros i Hi. apply FRZ; unfold P; lia.
      * apply PMPK.dkr_grows. exact MG.
    + apply (PMFR.iss_keep RSEGS AD L KL LB sp 18432 [] M M1 EK1 STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact SINC| exact IA].
    + unfold PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros E; exact E| lia].
    + split.
      { unfold PMPS.fill_res, PM.CHUNK. split; [reflexivity|]. exists 0. cbn [PM.sm_g PM.sm_st]. rewrite L5K.rl10.
        split; [exact X10|]. split; [lia|]. split; [lia|]. split; [intros E; discriminate E| intros _; split; reflexivity]. }
      exists p, 0. rewrite L5K.rl11, L5K.rl10. split; [exact A11|]. split; [exact X10|]. intros i Hi. lia.
    + apply (PMK.hpres_of L LB sp 18432 _ M M1).
      * apply (PMK.ek_weaken L LB LB sp 18432 sp 18432 _ [] M M1 EK1); [apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil.
      * apply (L5.defined_grows M M1 _ _ MG). exact SDEF.
      * apply (PMK.dk_grows L LB sp 18432 M M1 MG).
    + exact HH1. }
  (* [comment removed for export] *)
  subst st.
  assert (TOP47 : hl_sptop L <= 2 ^ 47) by lia.
  destruct (BR qc 16384 QIN) as (Q0 & Q1 & Q4). unfold hl_ceil in Q4. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1.
  set (Wx := [(ois + 40, 8); (p, 16384)] : list L5.range).
  assert (WCx : forall a, PMK.inW Wx a -> (ois + 40 <= a < ois + 48) \/ (p <= a < p + 16384)).
  { intros a (r0 & Hin & Hr). unfold Wx in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
  assert (WCs : forall a, PMK.inW WS a -> (os + 256 <= a < os + 296) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (qc <= a < qc + 16384)
                                        \/ (p <= a < p + 16384)).
  { intros a (r0 & Hin & Hr). unfold WS, PGS.W_srcfG in Hin. cbn [app] in Hin.
    unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; lia. }
  LeanFeed.pfeed P (PMSFBP.fbA_conc fx R M (fun j => match j with 2%nat => sp | 36%nat => os | 37%nat => ois | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSFBP.aligned; first [exact A16 | exact AL36 | exact AL37]]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG1 & FR1 & FRZ1 & MS1 & KS1 & X1 & X2 & X8 & X9 & X10 & X13 & C32 & C24 & C16 & C8)); PMK.pvz_clrT.
  set (P1 := fun a => sp - 32 <= a < sp - 32 + 32).
  assert (PF1 : forall a, P1 a -> sp - 18432 <= a < sp) by (intros a X; unfold P1 in X; lia).
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x382d4 R1 0x5d574 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1).
  { intros a Pa. apply (PMK.cwr_stack L LB M sp 18432 a STK). apply PF1 in Pa. lia. }
  { intros a. apply PMK.rng_dec. }
  intros HH1.
  assert (STK1 : L5C.stk (hl_sptop L) M1 sp 18432) by (apply (PMK.stk_grows L M M1 sp 18432 MG1 STK)).
  assert (EK1 : PMK.ek L LB sp 18432 [] M M1) by (apply (PMFR.ek_of_piece RSEGS L KL LB sp 18432 M M1 P1 FRZ1 STK (PMFR.brange_hi L LB BR) PF1)).
  assert (IA1 : PM.iss_at RSEGS AD PMSP.T3 M1 (ois) str (PM.STRM g eg 0)).
  { apply (PMFR.iss_keep RSEGS AD L KL LB sp 18432 [] M M1 EK1 STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact SINC| exact IA]. }
  assert (BASE1 : PMST.base_ok RSEGS AD M1).
  { apply (PMKP.base_ok_keep RSEGS AD L KL SF LB sp 18432 [] M M1 EK1); first [exact BASE | intros a _; apply L5C.outside_nil]. }
  assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 32) 16384).
  { apply (PMK.stk_call L M1 sp 18432 (sp - 32) 16384 STK1); [lia|lia|lia|]. replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  (* [comment removed for export] *)
  assert (APART : p + 16384 <= g \/ eg <= p).
  { pose proof (PMPK.iss_unread_where RSEGS AD M (ois) str _ IA) as [(Y1 & Y2)|(c1 & n1 & p1 & -> & Y1 & Y2)]; cbn [PM.sm_g PM.sm_eg] in *; [left; lia|].
    assert (PIN : In (p1, c1) LBX) by (apply INCS; left; reflexivity).
    assert (NEQ : q0 <> p1).
    { apply (PMPK.fst_neq_app ((qc, 16384) :: OB) LBX q0 c0 p1 c1); [|right; exact OIN| exact PIN].
      exact (PMPK.heap_nodup L HI HIok LB cr M _ HH). }
    destruct (PMPK.blocks_apart_heap L HI HIok LB cr M _ q0 c0 p1 c1 HH TIN (SINC _ (or_introl eq_refl)) NEQ) as [Z1|Z1]; lia. }
  unfold PMPSS.xsgetn_spec, PMPS.xsgetn_spec in XS. cbn [pa_xsgetn AD PnLayoutS_u.ADDR_S] in XS.
  apply (XS fx1 R1 M1 model K LB cr (sp - 32) 230204 (ois) p str (PM.STRM g eg 0) HH1 MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [split; [lia| reflexivity]|]. split; [exact X2|].
    split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
  { rewrite L5K.rl10. exact X10. }
  { rewrite L5K.rl11. rewrite (KS1 11%nat) by PMK.inl. exact A11. }
  { rewrite L5K.rl12. rewrite (KS1 12%nat) by PMK.inl. exact A12. }
  { lia. } { lia. } { exact AL37. } { exact IA1. } { exact BASE1. } { exact SINC. }
  { exists q0, c0. split; [exact TIN| unfold PM.CHUNK; lia]. }
  { unfold PM.CHUNK. cbn [PM.sm_g PM.sm_eg]. exact APART. }
  cbn [PM.sm_g PM.sm_eg PM.sm_st]. unfold PM.CHUNK. fold Wx.
  intros fx2 R2 M2 c RP2 Y10 CEQ IA2 DD2 HP2 HH2.
  rewrite L5K.rl10 in Y10.
  pose proof (PMPK.iss_size_lt RSEGS AD M (ois) str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ.
  assert (CR : 0 <= c <= 16384) by (clear - CEQ SZ; Lia.lia).
  assert (EKc : PMK.ek L LB (sp - 32) 16384 Wx M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
  assert (SCc : 0 <= 16384) by lia.
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp 18432) by (apply (PMK.stk_after RSEGS L KL LB M1 M2 sp 18432 (sp - 32) 16384 Wx STK1 HP2); lia).
  pose proof (L5C.stk_writable RSEGS _ M2 sp 18432 STK2) as WR2.
  assert (HI2 : forall a n, sp - 32 <= a -> a + n <= 2 ^ 64 -> (a + n <= ois + 40 \/ ois + 48 <= a) -> L5C.agree_on M1 M2 a n).
  { intros a n H1 H2 H3. apply (PMPK.ag_hi RSEGS L KL LB (sp - 32) 16384 Wx M1 M2 EKc STKc SCc a n H1 H2). intros i Hi I. apply WCx in I. destruct I as [I|I]; lia. }
  assert (HI1 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M1 a n).
  { intros a n H1 H2 i Hi. apply FRZ1; unfold P1; lia. }
  assert (HI02 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (a + n <= ois + 40 \/ ois + 48 <= a) -> L5C.agree_on M M2 a n).
  { intros a n H1 H2 H3. apply (L5C.agree_on_trans M M1 M2); [apply HI1; lia| apply HI2; lia]. }
  assert (BASE2 : PMST.base_ok RSEGS AD M2).
  { rewrite (ly_img_lo L LY), (ly_img_hi L LY) in T1'.
    apply (PMKP.base_ok_keep RSEGS AD L KL SF LB (sp - 32) 16384 Wx M1 M2 EKc); first [exact BASE1 | intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply WCx in I; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock AD PnLayoutS_u.ADDR_S] in Ha; destruct I as [I|I]; lia]. }
  pose proof BASE2 as (IMG2 & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG2.
  pose proof IA2 as (K0' & KDEF & _ & K16 & _ & _ & K40 & _ & _ & _ & _ & _ & KIOS & _ & KE2).
  destruct KIOS as (_ & L32 & L36 & L40 & _ & _ & LD & _ & _).
  cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf AD PnLayoutS_u.ADDR_S] in *.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as B18.
  change (bv_modulus 64) with (2 ^ 64) in *.
  assert (R2_2 : getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl; exact X2).
  assert (R2_8 : getr R2 (PMK.reg 8) = Z_to_bv 64 (os)) by (rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl; exact X8).
  assert (R2_9 : getr R2 (PMK.reg 9) = Z_to_bv 64 16384) by (rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl; rewrite X9; exact A12).
  set (st' := if Z.ltb c 16384 then 2 else 0).
  assert (TAIL : exists fx3 R3 M3, msteps RSEGS (@mkst fx2 R2 (Z_to_bv 64 0x3833c) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x383dc) M3 (seg_rom RSEGS))
            /\ mem_grows M2 M3
            /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (sp - 32 <= i < sp - 32 + 32) -> ~ (ois + 152 <= i < ois + 152 + 4) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i))
            /\ (forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (PMK.reg x) = getr R2 (PMK.reg x))
            /\ getr R3 (PMK.reg 1) = getr R (PMK.reg 1) /\ getr R3 (PMK.reg 2) = Z_to_bv 64 sp
            /\ getr R3 (PMK.reg 8) = getr R (PMK.reg 8) /\ getr R3 (PMK.reg 9) = getr R (PMK.reg 9) /\ getr R3 (PMK.reg 18) = getr R (PMK.reg 18)
            /\ getr R3 (PMK.reg 10) = Z_to_bv 64 c /\ L5.u32_at RSEGS M3 (ois + 152) st').
  { destruct (Z.eq_dec c 16384) as [E16|N16].
    - assert (st' = 0) as -> by (unfold st'; rewrite E16; reflexivity).
      rewrite E16 in Y10.
      LeanFeed.pfeed P (PMSFBP.fbB1_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 36%nat => os | 37%nat => ois
                   | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
                   | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSFBP.aligned; first [exact A16 | exact AL36 | exact AL37] | tr64 M HI02 | tr64 M1 HI2]).
      PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & T1 & T2 & T8 & T9 & T18 & _)); PMK.pvz_clrT.
      rewrite PMPK.word_id in T1, T8, T9, T18.
      exists fx3, R3, M3. split; [exact MS|]. split; [exact MG|]. split; [intros i Hi N1 _; apply FRZ; assumption|].
      split. { intros x Hx. apply KS. revert x Hx. apply (PMPK.sub_in PMSFBP.KS_fbB1). vm_compute. reflexivity. }
      split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|].
      split. { rewrite (KS 10%nat) by PMK.inl. rewrite E16. exact Y10. }
      apply (PMF.u32_at_agree RSEGS M2 M3); [|lia|lia|replace (ois + 152) with (ois + 120 + 32) by lia; exact L32]. intros i Hi. apply FRZ; lia.
    - assert (st' = 2) as -> by (unfold st'; destruct (Z.ltb_spec c 16384); [reflexivity| lia]).
      LeanFeed.pfeed P (PMSFBP.fbB2_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 35%nat => c | 36%nat => os | 37%nat => ois
                   | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
                   | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSFBP.aligned; first [exact A16 | exact AL36 | exact AL37] | tr64 M HI02 | tr64 M1 HI2
                             | apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 (ois + 120) 152); [exact LD|lia|lia]|lia|lia] ]).
      PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & T1 & T2 & T8 & T9 & T11 & T12 & T13 & T18 & CST & _)); PMK.pvz_clrT.
      rewrite PMPK.word_id in T1, T8, T9, T18.
      exists fx3, R3, M3. split; [exact MS|]. split; [exact MG|]. split; [exact FRZ|].
      split. { intros x Hx. apply KS. revert x Hx. apply (PMPK.sub_in PMSFBP.KS_fbB2). vm_compute. reflexivity. }
      split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T18|].
      split. { rewrite (KS 10%nat) by PMK.inl. exact Y10. }
      exact CST. }
  destruct TAIL as (fx3 & R3 & M3 & MS3 & MG3 & FRZ3 & KS3 & T1 & T2 & T8 & T9 & T18 & T10 & CST).
  set (P3 := fun a => (sp - 32 <= a < sp - 32 + 32) \/ (ois + 152 <= a < ois + 152 + 4)).
  assert (FRZ3' : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha N. apply FRZ3; [exact Ha| |]; intros X; apply N; [left|right]; exact X. }
  apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model fx2 fx3 R2 0x3833c R3 0x383dc M3 P3 K HH2 Mh Ml ltac:(lia) MS3 MG3 FRZ3').
  { intros a Pa. apply (PMK.cwr_stack L LB M sp 18432 a STK). unfold P3 in Pa. lia. }
  { intros a. apply PMK.or_dec; apply PMK.rng_dec. }
  intros HH3.
  eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
  { apply (PMK.ret_to RSEGS fx3 R3 M3 0x383dc W_373ac r F_373ac eq_refl D_373ac); [rewrite T1; exact Rra| lia| exact Hr2]. }
  (* [comment removed for export] *)
  assert (EK1w : PMK.ek L LB sp 18432 WS M M1).
  { apply (PMK.ek_weaken L LB LB sp 18432 sp 18432 WS [] M M1 EK1); [apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil. }
  assert (EK2w : PMK.ek L LB sp 18432 WS M1 M2).
  { apply (PMK.ek_callee_in' RSEGS L KL LB LB sp 18432 (sp - 32) 16384 WS Wx M1 M2 HP2 (incl_refl _)); [lia|lia|unfold hl_ceil; lia|lia| exact (PMFR.brange_hi L LB BR)|].
    intros a I. right. apply WCx in I. unfold WS, PGS.W_srcfG. cbn [app].
    destruct I as [I|I]; [apply PMK.inW_next; apply PMK.inW_here; lia| do 4 apply PMK.inW_next; apply PMK.inW_here; lia]. }
  assert (EK3w : PMK.ek L LB sp 18432 WS M2 M3).
  { apply (PMK.ek_piece_in RSEGS L KL LB sp 18432 WS M2 M3 P3 FRZ3' STK2 (PMFR.brange_hi L LB BR)). intros a [Pa|Pa]; [left; lia|]. right.
    unfold WS, PMSP.W_srcf, PMSP.o_src, PMSP.o_p, PMSP.o_is. cbn [pa_off_p pa_off_is AD PnLayoutS_u.ADDR_S app]. do 2 apply PMK.inW_next. apply PMK.inW_here. lia. }
  assert (AGP : L5C.agree_on M M3 (os + 240) 56).
  { apply (L5C.agree_on_trans M M2 M3); [apply HI02; lia|]. intros i Hi. apply FRZ3; lia. }
  assert (HI23 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (a + n <= ois + 152 \/ ois + 156 <= a) -> L5C.agree_on M2 M3 a n).
  { intros a n H1 H2 H3 i Hi. apply FRZ3; lia. }
  (* [comment removed for export] *)
  assert (OTH : forall B m, In (B, m) LB -> B <> q0 -> L5C.agree_on M M3 B m).
  { intros B m Hin NEB. destruct (BR B m Hin) as (Z0 & Z1 & Z4). unfold hl_ceil in Z4.
    destruct (PMPK.blocks_apart_heap L HI HIok LB cr M _ B m q0 c0 HH Hin TIN NEB) as [AP|AP].
    all: apply (L5C.agree_on_trans M M1 M3); [intros i Hi; apply FRZ1; unfold P1; lia|].
    all: apply (L5C.agree_on_trans M1 M2 M3); [|intros i Hi; apply FRZ3; lia].
    all: apply (PMPK.ag_blk RSEGS L KL LB (sp - 32) 16384 Wx M1 M2 EKc STKc BR B m Hin); intros i Hi I; apply WCx in I; lia. }
  assert (NDL : NoDup (map fst LB)) by exact (PMPK.heap_nodup L HI HIok LB cr M _ HH).
  assert (DKQ : PMPK.dkr M M3 qc 16384).
  { apply PMPK.dkr_agree. apply (OTH _ _ QIN). intros E.
    apply (PMPK.fst_neq_app [(qc, 16384)] (OB ++ LBX) qc 16384 q0 c0); [exact NDL| left; reflexivity| apply in_or_app; left; exact OIN| exact E]. }
  assert (HPF : L5C.hpres L LB sp 18432 WS M M3).
  { apply (PMK.hpres_of L LB sp 18432 _ M M3).
  * apply (PMK.ek_trans L LB sp 18432 WS M M1 M3 EK1w). apply (PMK.ek_trans L LB sp 18432 WS M1 M2 M3 EK2w EK3w).
  * destruct STK2 as (_ & _ & _ & _ & D2). apply (L5.defined_grows M2 M3 _ _ MG3). exact D2.
  * apply (PMK.dk_trans L LB sp 18432 M M1 M3); [apply (PMK.dk_grows L LB sp 18432 M M1 MG1)|].
    apply (PMK.dk_trans L LB sp 18432 M1 M2 M3); [|apply (PMK.dk_grows L LB sp 18432 M2 M3 MG3)].
    apply (PMK.dk_callee L LB LB sp 18432 (sp - 32) 16384 Wx M1 M2 HP2 (incl_refl _)); lia.
}
  apply (KONT fx3 R3 M3 (PM.SRC qc de rem) (PM.STRM (g + c) eg st')).
  + apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
    repeat (destruct Hk as [<-|Hk]; [first [ rewrite T2; symmetry; exact Rsp | assumption
              | (rewrite (KS3 _) by PMK.inl; rewrite (PMK.cs_of_preserved R1 R2 _ RP2) by PMK.inl; apply KS1; PMK.inl) ] |]). destruct Hk.
  + exact (OWK M3 HPF AGP DKQ).
  + apply (PMPK.iss_upd RSEGS AD M2 M3 (ois) str (PM.STRM (g + c) eg 0) (g + c) st' IA2); cbn [PM.sm_g PM.sm_eg PM.sm_st].
    * lia.
    * lia.
    * apply HI23; lia.
    * apply HI23; lia.
    * apply HI23; lia.
    * apply PMPK.dkr_grows. exact MG3.
    * apply PMPK.dkr_grows. exact MG3.
    * intros c2 n2 p2 _. apply PMPK.dkr_grows. exact MG3.
    * apply (L5C.u64_at_agree RSEGS M2 M3); [apply HI23; lia|lia|lia| exact K40].
    * exact CST.
    * exact KE2.
    * unfold st'. destruct (Z.ltb c 16384); [right|left]; reflexivity.
  + unfold PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    split; [intros E; discriminate E| lia].
  + split.
    { unfold PMPS.fill_res, PM.CHUNK. split; [reflexivity|]. exists c. cbn [PM.sm_g PM.sm_eg PM.sm_st]. rewrite L5K.rl10.
      split; [exact T10|]. split; [exact CR|]. split; [reflexivity|]. split; [intros _; split; [exact CEQ| reflexivity]| intros E; discriminate E]. }
    exists p, c. rewrite L5K.rl11, L5K.rl10. split; [exact A11|]. split; [exact T10|]. apply (L5.defined_grows M2 M3 _ _ MG3). exact DD2.
  + exact HPF.
  + exact HH3.
Qed.

End WithHeap.
End PGSFBT.
